-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2257
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:09:47.163778+00:00
-- url     : https://prove2.me/submissions/28ffc8c9-a98f-4cb0-be82-6873d64d3863

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 405755395 ≤ n < 405935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 405756645 1250 405755395 405755407
    0x309032904030c240207050f0d1b03140f1213320a0501060e070c0f2019082b081e0f041208070804020f030c04060806060906010f14 58
    0xe220303203070480f0300c4c0030740f00380903210700d06a072190700290462403054602c1c0c071a01c88186103d46001c64103aa40c2807855486000e403030480c00b00d500350103810311022010482e046ca86440710000110191104a00702c1035030070354803a040782184454680c003410b40c180c444000c02540000648040180340824000c0c10303c201125104003031014440380001d51525640030b001d80382401c00038194030030b10641e0904940008a611a4002100d5000b00000020a4400000c0100c00865420300c2c081110307680d14022815400d810714040340d550ba08155040608030b43c02403040c00b00ca082448016907016200501e08001190301556109140c100c038110f609214005002c20508054201c50080d00c1d80c0c2e05900180c58189890042040c80c02194141c1d2420078240b8090400746c03244030414005c81055079a01c64a46981d003c000006002141d20303a07152003980806500c0e91128020f07640284006030203400d01c0c4c9005024003455003001020175040100d9807101442c5203801c89040d144040036940f01580b248 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 405757895 1250 405756645 405756653
    0xb06010c1a0a140a0c2003040e0c03040311030c0322080d09030605150a050d17031005010818060f0a0b03070305010524011706060d1a0406080106050604090b040213030309032904030c 80
    0x449250400401c0c24009420803880c0142400114051842033b580c06000070323102860070b912400750600c5041107400030804ca10b80f501800703520742d02a51291540780300b000e59404e60113180418072103411000c41e081c6c0c0810024010107200f26907001c1041c190003030500c0400000110b072110030340510fa220340400000c0e101403001890030605180c1e01d0182c1c031992810f2116840b40302c10814401d644c00540c20b02c1c0000c400200554240900d51402c1c002008540c0311200c400c1a1060010b20411000b0364440000070300d6070b0f003040000000e40c0200300000c0c50382400c0c66503000d0705564410400c44101904a50302450764048882c00c2c2d0400c01b20036400158642d01c000078094828044603030301150030032180c0d0381c80c0c9280000309400c01d0011941040b12995440c2a0b900b138410034861a54020340603c001c00c0350f07451542121042d1400140010314000d0203042010701d10700c44d6001600000c08600c002c2c0100a82c414040c1d0740c50449201800188035046030015181000500003001c0106602c4020300300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 405759145 1250 405757895 405757897
    0x1120204020d2c0105070c031707020c09070509041d0721021f030b0108060f06071502030718060c080405120f120901020d0c0b06010c1a0a140a0c2003 66
    0xc03624400703c4401a0305252140b0a018192021000207502c0c041c0890405400346030303298076441d40350300d9a0f020403400940341c60480a00070040e50960045000960107507899040080c840d980300e4641d540c84020b00c02c20300c03040760304220b0000504826074034041d10081001030040116a400700390200401c8403a41041c004111a08000f9000759083c141e180c0c11749169102011815819034080006802e100011030380c08005650446d00401c115040040c3c90030910000e01c8d03641e014860030092400c40581ca00101d0b4402c0340c0c00e030002070902c00894002d41c950030061000342594544100319012036101c180740c0d4420b80c810740c0d00c100070440006071003000a10846d0301603001c22095484583c100d21004020b1790100c804203005014240340007001900038007540540c250003004d414455541c0d400191900480684161444150342c1e81400070440700708007492155480410202e418070340c80c11070510042d17024019042250038150340220542d03001c00c0785607140c20004d048140b2a00c03c00129411 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 405760395 1250 405759145 405759161
    0x51b03030d020412021c0b04150e0a05010e060c040315020a030b1305040b0a14060f06041203050a020111040602210904020f03100f030510020a200f0c01020601120204020d 75
    0x5207500225001440203d40c83c140000381c1c1c000d6882c0c00003c1c030110042c250001e03103800b00400c050043c20107d0b02003070b4140e04101d03c06601c0c110001e5000300301c00ba0b00340707000fa94080c102e586039181c1c04c0d0031041400c248803054008090140c0d00781054115070315440d40500181c9084041c641c04280700511901c2a08240240c28000e40f10b1010050200d5058000c0e04049600769414011000480d1561860740324060020080c889429080d4645108002075400e1101c441580500e05000204c0c04024107a2842c40f00e42c4a82c640c55511a13681c00d01030b080d04d95050702c1c9805910207000402040760042414500710040e02040d402c0d0800200d40e032100750040003a0150031074400703d4049103c511180041d40100f031007000d80344980781e48102c00c1d0b50703c08041c04020001d0b00070308640f0941d611645c0281120341c090341803241e184d1440300e07100e4a0740160b400e0110380642c82005540c48030702d804e10004551300c0d401c2c07010303004960400081d07501100403200300038012940011a060140d100ba400241 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 405761645 1250 405760395 405760417
    0x417100b040c1e02032116020d05070303021e0f030912031509040c08120a0201061208040501110304080a080a030f2007110d03020106080d0f08010902030a0b0d0602130b0304051b0303 80
    0x100501006c0d6240c0c001e10011102c1001884010307609005aa0001500c4c030354414643d82d480e8a8003542e40c0d02200a504211900e52480364410104e04100b40032030040d00314100c00d400070320b4882c0303486400c4920b001826000c042d88008204107101040360880303150094180183c426030415107c600c0d04440010315540300b000b41307008509200d450900e1220040410010b5a0b000307120140d251142d4503040300702c1c0c3d840206140020002003049501489a1000d600888030a0380c3c00d02da42c0d5170300b150425440110890b0000700005a40f2130320f942600c1f07100f442000400e801c2041954003166004400070980d801c0750741e940301040100030884403004465411401504580300b00d825440c019004e40100d003d818414014040944206c1c1e03c03c00726110303080701999071000c070380c1d10f4200320900035840502610481501d5a101c3c003402e865030300044010a20440005a40e8200700c003012030960140d07001203840b00f2040080c0070100d080025020881a42010168640100d41e00028514416036401740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 405762895 1250 405761645 405761677
    0x316140301060e28141206010501030e0a080d0b09150a0314010213030503091f051c06082407030b01020a080d1803081e0103150509030417100b040c1e0203 68
    0x1101d00d0301d10030454400d200000380c00400c5d83e040056607000008068407a51120004018540c466080001c21b43c8044007a1035020711541c0300c1070038683c060144400305076108d900661450520551351980052510203141d4081010800103c408401e84006002c011004003103003110300080d030403a81241c01c0c1c90100c56460f0343e02d01c1c0c1725459412640c5514030078000c2c0000c40101e01242c900312030f82142d20395a15807401c90744a503d034209050503020138031002d079108008180d00c0e0040212414184804103018402040d80440c9451140c00500100825080042c031a1b69640c00050103001a81c1c400c80042d111084140c1c13020050400001958103010190443e20034150440c0029010710340107400b1070402c800100410340c4482c0c0c203200081c052a00074008a80a00e400e03400240c0020084003568075003640c6801d0400200702031100a0103035088220110100c200381d101d05004003030140c8040c007800fa0140d80c0a01005030a81c2891110b143d01042c401d40f1a10a104850b4001d9501e0202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 405764145 1250 405762895 405762949
    0xc0203030a241410030b0d0b100e130c150e010509030c04060b0a1107060507080a12110904051b07080f07050d0e090609010302100e06040b0403080316140301060e 71
    0x43c0a0341240020715500500300402e80d0995103121340603c1c449810060890b00c40020780b0341c1c9410100d04000c000c002005400c15001c2012403600c10707040d0217004500c240c140d00d50740f141003a060050066000ca4002042070f0040030007650082c01381c1002c4903090801944903c0c1e6080441c1c1071691424249503c01d18141000c1404009803001d84039a40300c03039071400c1046900300d525668402c0c0c0c030700491000c43e505006200c0016132000082034080f64030718100741e110611489140c10b40b24444000481640d000c00c009805003001e2190660004461751011f4a41c5802d1384608a18400c503034002e02143c0c40010303100b0000220000b02c40000394400104e41304a1030481d001001a0b83d2229607900c103640300004104c0500e0000c441d0f0703042c0c03900141009030300d0402e1a801e442c40d001d00020242c2140003030100080e40f811f4140504021400303060074564915001c03e0211178800000100c0c000d002a401d40038070060013103425a415030345207003007900c6800315a600180c0c9038001c554a00c0c900319010400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 405765395 1250 405764145 405764159
    0x140f0705150717090613080c0a23070b03011403070f090f05071e030507020f06040b07090509160e0a03140d031d0a20060a0306050109090c0203030a24 66
    0x41c588151000e40e07035400e0b00c43e440e800d25110000290b0705000700d03600c914003094000182c040d954105a110381d620b240340c10a00408207007011188081502c2039801c082d039100d0802098a290001a00034001030700140781840c2c0c3d1078103140018080e02104220860103110a80c4040003d20003400c00c4034469100c1b55921004030000c4c140d070b150110070907400c2001207030043c3c1c01110103081e00d0030242000001e240c6009000c07401840d0003400e1008500c1910304503c000c001c10701c18a80550b010f14003410940c034040c0004ac2142205501082c0180040c2c0b04200d000d0310f200030280004092440d0000c1700881c000001101c60715907810160071407114840101c8440b8000aa900b43c80240e40c4091141d95085081d03689501c401920281c0c42d90081499880090381c403a41030448407400f452f03044a0fa40350100856116080711340042c0201341d850f0400c1c17240e0360300041107d000b026026014060010100402516030102230159444192505100308071518254250303222900d07072003a1040352582d1814 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 405766645 1250 405765395 405765433
    0x121a0a061401030608030711061b0a0209060a0608160e10050c01050c031905090f1203010608010807030c060f0e120d09090612080a14071112010903140f0705 69
    0x12030075600c688032202080055009002e030301c0072503142002860030846503440d0095800280e034161544000d041000040c1c0c60b2901c0e030400b0b0044c1000e002082509600d10610210600151583e032050501d07030000c00500394458605030b8440034141660341c01d03109120301520903116461070290301c459094868114240e120000e09040342c0d94000911003038548441d150118032040d01c600080144c441400ca240079029001f080d000442001100e005056920303d01c0d04100c0c900788511410b60000004014583d48026000d0160504070090007009140d40d681a81101a034800c040500c1070704206140ca50b8020301024103102005000d06514108180c40c1c951101d0b00034500c000855250840032491024900c14103055a03003190480c0c202c443da54039101c0c840c1c1c2080e0001c20030406500354942c104020300c4003800c0e80512440380794070301c41c02c00c0c0d00708171014511920520680e85046202400300b5400128880341c1603144440310303601c4d54104108000c5202e9008003411902c5000541c0b00d000c00d140c0c0e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 405767895 1250 405766645 405766649
    0x303041209030b150414070e0d030504030b070806240a0806030f0a0501050a060b031e1923060301140106110f011103070801080a0b01031b0806040b010302100f09121a0a06 75
    0x2182001b198515242c02003900f403040e43d44800080c0e030f0304592491420200d04503e034480c000e083c05401d20303599540344002754000300c85140000d00d0081c14010079081c62102c480c68040c41c2501d418140a60b6401404a8014551218100412600454000c0e01c081c0400c403140f10301e5006a60241c0c0403801d01c58040c00b0245c520304581d07460140006006407070f034415240202a45035024034101461412081c04000182c0340030307403800001c040795403001201d02c5001d0801c2c44510b110781142c011078000c600c0b1528010401400307641007250300903079180d40c1c121b6030381504d40600f89034804002801c0f00501d000a00901c83c482d542c42c101071008043c0d83c0030041d606c1082076617120f0b00203a032268031031500c408004c1d00c028046e83e4a40010300008258005145141e20141c5d1101c4280380e40d030212914000c0250b0702a2500714440f401441507042c84e039103015060b08281041034640104200081903a00544200103030806040d5a400030041100d83c441260302c0c41c020078507030608090b103a04004000300c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 405769145 1250 405767895 405767899
    0x90c090212070e0102070501080a050a0e0613030f1b06091104150509070e030a08090f041e0606050c070e15270106020604080306062101080102070c0801020405030303041209030b15 79
    0x10f195580c0e0a90f100190540596006a44282c1c55032102c40301305010300782c003500b0060607d4854103000548242048103030720410b15885030034801d016506003c1d007000c80d06442d0b00f0402414031401100c0480d001d4040c251658028400106e400290418040c169410103460f070748036007007100f180042e118045608054910446404000e501c0700d07001603074140c3c0e20500440d015040141400045400300b0080c2c444020040c18000d442d56408000600700c40e103a14102c518503e601e6502580c1d20300920072074000c0d000904045182c840121036080c1c0c0c41882d489003039014400302001070101002d20381026814000074164000002d0307005a0009001d00200d4600605002c0d80e00020300035100107107450143c0d4115080600e1600c451042c00410340c041a5009120380001c0f00c0e105143d005030140d503009010f074030300050300c80b8081d252603500940310f80d0004425a00501041c4031954020080381e400c03a9101c48901d200d1850031205454002d001e13400904280c5621080103092501c3c118086400001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 405770395 1250 405769145 405769157
    0x100e030a081f151107060e03100603031715060a120c030e0c06091504030f020306070f05040e06010c020a060306081608070b0703090f0609062604020f0a0f090c0f090602030904090c09021207 83
    0x1d8811009d00703c950070311010b0000b840d00c41d400e208151401c2d01d01a0001d80708091000089140c80205100b13a00204102002a403d2403481c82c21030850320800030811800d2809015000da2102070b03a5642014940c4544100e01c00641148240e40b400c005501122664480070349503983c0f41040601c600784010140e00900414002542a034440c1350440380c500744580b2158185410110101d84815000305494140980280f008026917611003040008088990700401c205091405460400000101107491a9111302d0240a4401c01044c2101518014402951207001608044901c04410780c45107000c80703800c0b0340c0815034a45c044800c0095840c142c0700c0c0c82e00e03c3c00800c0f0070181c40c03200354032203000c0e201840080b0b0014540021002d0307600a0041c0048207803034807403440202180d45030b444001100c0d641c1d0720703410b1010741158440b10052180e08100308204e190510103512442852003c0d03109950705c0d407071081040030b07031030880e00601094441191203141c9001e1050250b8801c2d03d942000c0380c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 405771645 1250 405770395 405770413
    0x3022110060905180103080a0e210d111011070c0e01090c091d15101d010503041e030507080c010504061a1809100e030a081f151107060e03 61
    0x1050400c00c400300c828100313022043c0c2c0c61030700c50001c950001403410f8100004500c01840d1691008190600d42880d010706003c10200303020030a00c0c000f00410440240944801c501703100c41404240e01c00a1808154081015150420721000c05e101e040d60041c504816228042148042001000c1c169054210100880240070005448a50f41441600b02880d06d032018a4445070584929940100c64142421018100000040c3e2116a42500704bc0060300c01d200354145060402401810a013082c2000d510354109a264000300003500015044401040912134081511880171180d8040d04401e0b61a00c0d04402d0b406540605000d031070581d00b01d800c050480300c1c54030160f131003c15240c40080503456415910708100311880c500078200000da008000c104120500207020300010000110080c2d80e07a0308510323401809002c0043e24800c0304903d41e9140d25101e010341c0f402c6005071800f0403146000381d01c0b0044220b0b20820103406062060084110005105400c114107005070141141547d01c294 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 405772895 1250 405771645 405771649
    0x1011090f04090c1d091209040c09180b0a050603102108030c1206010201060501020c040908221e030b060d0f0c0605031005010c1a04020604031e141c03022110060905 72
    0x24501d03510403841e91b5010043c0c4000b40c546035001a24000e12400d09540040d5151402c02034600029604226681c50342c1d9502054900454200301a0070302b110903070f065003040c0201340c41c0090540920120001405404610754501c88121016164040203c80e41c910f011042d19805800a00c0800007448850317001c2031603503006001d1041038030010707030041406001c04001c00c40940080d400c26200c43d902000805058040c0410001600410480c031000207807504110b010007140e08030145944010b28001800000c05a001c12508640102d9001d0b100c1c00b1281070003114001141c1d0020500c80c07003801c000070320070303080005903100b01e500c50030092140381c1e40c4006507864000d80c9401000d84c01642040300c046050380800756005030001d01005c0c28240ca960302c00e420001ca80c000810042e6414480108012052126540410600000d0701d000c50381d4203d0aa40600c1e00b802003414550081013039009200d2480d40c902d01c880e9a03c2d08205c603400c068040e2181c40a06c0d0141000007500500701203154 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 405774145 1250 405772895 405772903
    0x10905030303090a03081f0312080705160b1b030a050105030708030715020a02120301030506060901092703030f140105150a020304120c0f171011090f04090c1d09 71
    0x9144640240004c010259801c40b02410010700707051121701204001c840100c9420207903405503106042c8031008004490000e4080d010007410102000000c000380d12038406015400764502d6480008640642c44410805120030050318207100300c000003008000c0401e801350010350488005406036414035481c1d0107185e88070f210707400020b0300220300302c0340c204005034940c1d0080c01c032034000d841584c9a0924449900c40310b580300381d000341c90070b60122003070207007510f403000d030960041c04a10410401c2d81c000070801003444200125400704103003030200381424036001e40c100a02c1d00355441e604002090300d40d81c40c0c40030350100b8050f00c0e0064890742c44c0c250041040c101200c1d03518445800850500b0b2400742c3c5014a00b8090078120b4041504e500c0026006141c8a005400303814101c0c2e003940c02c1c06003420f402c0d141224280303502b6800b508001ca269030002c3d90b5000c50f4001b0006a031111607005110f400f090280c0711108005003c041800c1c00025901d8203044006505480c9401c51000d5071120b0759200d0351 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 405775395 1250 405774145 405774151
    0x919061e021303020f0d0605010f0603150e0118061503140c09210111030a0e0d020606010918060b07050c1f0807030504031e02030c0f0303040803160909021305010905030303 76
    0x400111420030310141c917054041c0303041400010070012001d9466500e41d0243d4601380d01101003403042100a211031038041c054a004400c0e000f0003222180c3c50714184840442040c400d002091040e03410303140b01101141c10450207008201d413004041c24403400000d004283d42c0c150b51001c0b11211000c40d5001d680e20b011030707600600003829162200305416107404d240c40c181c64100d000750342c0d5a21111010030044c0c040c601c00d20410340c0c0007803080005c8a0b942d0501103611a0300d41150084010003189a070400c02510a44943c80744004064407441c2410006041a0b0024000071001240d50010840d001803101808001a05c94001c3d60824980c2c211000300008242008900524000b51007648030368071140d40103004c0e10b401e050008403c0c41c80e28181a04c00301c00c0d001070700002181c10007402d040001c42c07504594000218078616040c7c8540086000140090103400d040c200a280b0542c49140c281c0050302640004550b50f000080042081008a1091501242001100040303501d03005c415248 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 405776645 1250 405775395 405775417
    0x308060a060e0904111f030c08090105100e070c0209190b030a0302031603200a0b0c09031207110306240d02010e01121e09050c0411070b0919061e02 65
    0x80380c60320f656041e0301c003007130180440d0080709203440c000e006c00c0515480e00100841c0e84000031032040c1c0320002000498018055030a036811b10f000e110507008680740c1d11045400a000101b41511000c0c801c440c0064000e0b03029601680002c14031184481c010120b031442c02d0700050030020800d015040c140c458000680140150304144001004840c50710074030002c02c1d1103441c05080310301c2700b030760300500c103003104203038038480390700128407002003000c40200584c0080d1007810ba641464440310000781c0e0b810029040741000d06012504c0c42c00c2090400400401000041c2610028a0700941c406030241d105c50035200080c0000722140182d00740300049800c550340696031103014940c0100151120b07800c181241f41c1d066507c2d4040c0440c00703103000c541151201204008540c0790010f042c2503140c840030700300d014411031805032503c1c644038409007143c2c4030a501c0710b610f02c103d40d0b903580004d003000d180784803c12010f8910b011500800500d6170000301d00080c4002652070703903001d04140c1c0e0100c0c024082429 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 405777895 1250 405776645 405776659
    0x2070c08250902070c050d061e050115110312090a05101a06070f06050106030b0a080106120311010f09080912120f0c19050a0209131502090607050a0308060a060e 71
    0x10140710030076001400c1d00d1740550700045066507688040381d000383e050f0006540300da5441d00c0d0184204203032810080410f803190014000b80d410007a0047d0300e614044a940f05101c40c016400351740000034402d4a00d00d080088000c0c420b403071f0103600c1301c1e164200a070301281d00303011792100a840400b0501c25407070441e01c601855414980780b6401c0c070185520248054031840d42c810b900d00c00088040c014103020b80440e0303901042e102601c9090105000040d0400401a41829424046030700242030b00314491b601403070661600c4442d80113242c018502580c140800605082d41103052005200c01006a04826a003a803100225012141d841b00f03088060450340070790420002c5044200b10000d0504e40d200401078422200c046040d12460008009040350107402210120301903150036021070781e0200c6950211010805a42d41c0c00d0700c51141040515441c0b580841c000a00c0d49900050365613041d4000d040b41c140d50120b0034041c00c0810101c54041c805c200040c800311781c440c4110007240c5c01c00341c01341c0300d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 405779145 1250 405777895 405777899
    0x150f0e04050403021015061d090412051603051306110706030e010e150121051002070609050d0c05070504020405180603250f0b090907200102070c0825 66
    0x301400707020b003098086100348140c0001d03807200307485010314000c1502550b0f814940317020000341c8484140300c80559060344502d8504081d8881005050748580e003c4000140c0c01b00c050b009660324007407802e20341e03000d0f443d41e80d0060030150030800a004121007080d81c043d8140d0b850324121130010220801c0d83c0d00c1d070482030003041100c0c000c0e000404d60ba9204800030030903102c02440c180c07820100c1f50f00c0c03900d040640401040440e05407000c500301d18900d4040f0078108070a94407002e5079000c1403520b2805d00c1c1c2c0e0010301d1034180122580042490b552010a89003076070140000100a43c20303411054410b400707403e100280502c1c0c40d100726011900040d004c6500340341202003058503800014002d0f5054041e8000464400c100b60491131040043d9101c000200d5040c0300400255040365085000c650404000b208500d41d9011541035206040e89800313415500d03070300590505103400c18140a0250b00101c4c0210810200b10440c50035611010112800001070228030100c08582c800e41c0c86105900f0307031301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 405780395 1250 405779145 405779149
    0x709081b21010e0d030506120102030708040b0a060f09090209090106050f0d080d1b0906230705010605040213091103011203050309160e01230f01112401150f0e 70
    0xd050880078803034000040640d062010181041007107410303100020b655804110703440c0750209500b50300c802c01500071400d61419810161590f107024002030501440303900002d10720f08007500b121001c2c1034a030200c3c041d03c80d60381d103d85002d0806030104a1040c002c801c002516450b05128250031984001d206c041d66100541c284021080e403c1400c0c0d410700020851055200711074050b15001003c101d02e49048140c00220040400126130003003c10400c3c3c203641494007542e100041c512200314800b0707050b940d8031240350590050009602454019001080c507140c01194110b6001c00c0b0307449510184510f58900400d04a223100c24003600804c04400142d07d0007192154018542c052201c000722048645401c0c05d9242e02629640148009540a40140509920050000f4000500406042c00440c96000080c4801011020981001900641e07a015036004100350a103030140300d00030f240050403008003003200007024014040520701c8007407141000d6108140f200c803000460ba0381c400901e110081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 405781645 1250 405780395 405780439
    0x618141b0702041d070f0b030601050708090409050109110a0603020712110703150603121805060903010204031e020418030f032c06010501020c011b020d060608060709081b 75
    0x1d002d0381c201e079072814a901c1848031015014007030901000184100d5207020b201d1080207026800440c1e24880910a015072a41c029054817805580190195228225940480c004000c0392801402540c2003143e01400c1c081c41039910b00c68550180c17601c0c1b007030548822042d000c0c0d03c56450000c0551030b03094400e9808501c2294411070054040c0256158a0703a65281e80d5000900151111a290780e9820b0400030000384620481040b0042e0500c0e42d90000300500c5a00741d81a1840b8050041c8400900f5902d296000c0d81118041d581c402c0c1580821180c030301081002c1d0a049004a01840c58858103000e5248040c01c1019050f0b41580d56440322243c17100110060003c0c00800c880700c03026070481c41c0e104070344022403451894007503005041540c5400c0009190410203090750b41440358500503c080c00d4215880d08259036015209a0001421460100c005101c2c80c1d2000c880b07405801c09100c41e0035800300745007080315042004c840480a0000070b00c0392800764086003a6001490b00070b001c8506500361 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 405782895 1250 405781645 405781657
    0x5040209040b0603190f06080a03180506160203060606090d0807020109120809010e0901060203071e080712090914060f01030b0303191101090503040b03090708010618141b 75
    0x50804582800c2e6030003c079009030025910b6201d80f06070301c41d00d2601c449051140b606100304940045c4941c52402244a0721181051005000c11940c00049030900d030319900c0c500300400000d0700b0300d980c1d5403400c09000725290070f01000320b210b400b440000c29401e203040c1e000c0d0b40d030140380103180340a0785401d6a0f80300c4103a840f40404070306001c0c50b114000780301205040508032560003003100030703035405046000414000114000c0c511440f8904011300440c0d50000c2942d00880e0310590b2042d0304440c0c001d007052004074105000f0150310000681d1020090403070703002081300580707488104906880e0449082a07450350002c01c24070001c0d500c001a801d00c2d08034070001072020107040004200e0144070100b400c5600c06d02d0741504000c44e210220009950140340490000c41000080049441c1c1795903083e01e078401ea101e9010342d01400b0010a5101703205001c050000e121000007000b100e6a1200105414418444180c0f1400d2034600c0495894500d6041f40344220042c60500c0305881401400b2074083e0800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 405784145 1250 405782895 405782899
    0x39170c03160c240b120d031d030d021309050603030a050306040b041103100501051315050d05040303062d0506161406010305010b03031602012016060e0105120105040209 74
    0x40407180080780c210340040740c029243c0c01c0c2d61955a101c00c10b003801038a00007040940a800c60420300001c2403000b10b82e84841303090910b404582d02842c0f05240e41d59840e001c2c48240340c0d000c001018400c214807035005107001c0d040d4030244030205603964041740807200700f220440e03010f03001000402200c51080008550040d03009200040035040301000c501101e2800130740f50b40781130000050040d04608e100340500105400d10b003851410341e003800800c03407488240c4124440e146401c440100845e010714140c4119146a0404105a10303150070000c014050350721a103500b108410481080800140c031401001580d100e024011441c500b0b824442c580d80a041640034120740f4807160342c005811756545480302c1041c003004000550450404500710744092031714a200b580100910800d1200b5201060006030302400d061134400302000c40e40c4201d191000d50015a0300801e540c10b041da41c2d1101d1608190784a660b6500c201001090041d20301b0f124207450240000c901400402c03c51509030020900c000d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 405785395 1250 405784145 405784157
    0x61e070306080f01140903070c0902250501141006081b0417010f05010f0f06030209010512010905090c0a081002030901110301030c060e030c0906010339170c0316 71
    0x81c2e02040d50416610029441a80e519030048408444500780b0303140e0004580d4000e540740060a80c3c80000798903640c8940c641642c1c0114220008480c0d9060f2500c000b01001554181c0c1c80c09890320b18020030019a03e180540060004944207054510b0000e06503405901c0380c03882c5803030721403010b541c2da414140d40c0c000304481080b000ca0f10b20781402141d00241211000428540402d403003070415100140c1124074034000c8203408000242004031407104035000c0f4100140e03640e0308100100d5017842003c1120240d2240c85000103002c0300c07568021845a0703019002d48854260754010030a00c000184101a070390b40c070810010756040c0d5594010350700314440c02c0000903450b280d00c06000c00c0e500260300075030355031a19080c00c0080c42d421080c1d007111030b0000c5015211030300890380042c50790000606078904040c1d5540c2060300b4201c11517a019031405070500000310003074541140b182c0388807071030040ca000102c49210784900d40041003c4a03001c1d54411343c54a05650780d80240c5d0ba03030030300014604010451 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 405786645 1250 405785395 405785399
    0x40803130212010c1407051c0306030b2706071e092303060106031503060903030e07090e0c0a1508040203160f17030c060402220f0507020105060102061e070306 70
    0x240d401601a20301c01403400210b54203503c51009841700000a01041e6001010032a460004202054900c00d510500620703262254400104400914044e0402010303c1c8403981801044400387d050320079480304903400500c80240c40c0c02d08a4803070300195036480c0803500b020460700401d5001824202c1088451900e5905039035902410040803407840351794400ca0500788812030702410180003480c050812400c042c06070200790b25240241013024071002c1c01c1142c2d944409000c05210f0382000c481d001c1d1148c215a603861312541844002c0101d840c901c8050301c5080103400e030030304159003844101c60180c55038031160291300c04141c1c4c4490004000303d80c14019105004244240d20072042e002d04008901d201540c0c1c280301080c000d582c10a00c0811040d881070103c00880d0380c0014100d0fa219506951814840301403240c038401074601c01200550301ca081491380343c200c03000c41e07004505c61002070303000340801d0f11070200591f2160700640b6024040c010346218020900001084550081641d1500159803a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 405787895 1250 405786645 405786649
    0x906040e061302090115050d050a022116030e031204060e0304030302070806100b0a12061d060405180601151b030f18062a0501020406050304170f030408031302 70
    0x140045800d09103400c0042c04880560400589560140040500072490000390030f002608601403185c04101d066292400565514010340582e02216001e070102e02c00388282107410240d440040f20701c41055401c45012030100e51090040d411110724050155160025250044043d144e001304151801034440c40380b01c1c0d130341100708001d10055002c1d502404203603003440322203421b114000d00203814580405205101c1d01101c0400c4501e4000141084200c4070f901d03c6211010b048103a1103400c40011040481106003500002244101d104840c10019540c441201d03c06d01c0000b4a001541a070200b001132108a000c0d011150031030505040c0b28240c852110041d2a070082c400104800151424525202039a0001100301c51042d40003c1d01803800c1c28004010242d0908150804030f1490250192500340280e500a070b04198002c80203540e100d0300d4000c0900140e00030b5400301c43d110010a1503a02d104280019150311078101242a461503d40381c0f94103550350070141c0703900d184c0030614005100507 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 405789145 1250 405787895 405787903
    0x506130308190801080309100305040549090302131b090806100e06060912030f0c150108061b0d0603050c01030f06050d020d17030c1209011a0906040e 66
    0xa08032001520780d0b40c0802030b0000c089803810307403040d03011b58070a2040408950f5241248072404405190029155a484c1441d07071a203010418501040040c0d080384604001e44207600c0c03241d05602200b0a40c1e01002542004854006c4182000c002900120203100500e00845a001c4c000c20400e4007068000000c4403410780342284080e220003080440c5001c02c10b003002403040c0c0b6444030040d0713049504e1510384452142c0120005008130300c1001c00080107911a900c1c50040b82e120f03138404048175180c0840e03807044d04055200200000007485040c1d1491808940c140d2200d041c0c40f4004c020b010607445442001c020f41041d00410b403e0547d040c494215a1f00da2403060030011405032000340840e00d0035000140489001400003030f8081d0906800303001079298003407003200e02541926180245003550901c05900c200f10860001a0301001060002000641001c0c140c01e6031400c0401c0c1c041c4d15980300a90172181c8000180c1c02403850401f001c0520700d0b03c41d4283d46c1c011406400800c80750381c091615418 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 405790395 1250 405789145 405789157
    0xb07031d0f0c090721020a03090c090501060e0a032f18012c15030a14070906090b030d0f03111b010b01030209010c0b040c15020d11030f040506130308 66
    0x11942c0820380103080c5140a401c601d4010b0200e0500381501000c10612003070300e0000f41042da9450b6000241c1000680c8213510500c005500125015030068071800768602502003841441d0010b221088402843c1c030b00641404200c90f0f00603000071b2107440b01099100502c00b0488200c1250a1900e00c2c4c1582d07841d04d4501101d04191489000c0d0590704119a8141908615060300b8204080c000890540140d042010b9000326001d03108551501c0d01c040082d24081541c40700900015650031900d0100384005039213016a15220303001e104441d04c41e21040d003181d01d031240302070303155000c00c805254007400b0361074002c400400b602c2c01040d0a41c0180301e2000c1c07607201150a940804048510400c128000c4c41402915442441c0940c0f400c1d81440000304a84140180a00060b030b07150b0104042142800c84070005041481840341c0381a800382c0f0194844400484041c04a1030507195004e44040c040b0880c0c80035404c8021050a181c203113014440690410804003000326852400800401c1c4028040d2072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 405791645 1250 405790395 405790423
    0xc1e2a0d050606010201060801020a0212030a020d090506012102100f02100c0c061d030901120b03070608180a0507270e010b0112110316030b13150f030b07031d 70
    0x11a04003200021b00b1940c2640c800c00b4140d1061040010103540464007441003a0202419900c1c1e03158038202c82c00070f108400ca104105171602000383d0400c10081081d80c129011203999040080c10503404a0101c3ca07010802548009100d0b130000c00c15005000c01c00300700c0c04910494607059040c0c074092040b18100e100070008030328020307410704c10011140a00c40544401643d400d103180d00c5001a56078901407040b10605203e0404031a47c0070840560058040e0040101150307581c0365603801c00340544105603100508400754212040c0070180018040c1807d51380440140303a80391821f0810740354a59a04091030090f02c00350b80004c8100618051003070150306403000068152542400501128107101d0031440c81c0341022044440300500d5000d4992024040362080707180c00c40071000714011300f2519900c5070700400802c0e0004040c01150300c9a100303410f0700401c0c01c0702c2d192104040c141c40e800307521000300f0005e0f602e4005103015110f41c0110040b10484030b20400c03072040c844012801e101b5030903031501c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 405792895 1250 405791645 405791653
    0xb0f070b090c270c071401180b0c03100302010809010b0301060b0901081806070e0105070204050f0a0501120f0219050a080a1505150d02061309020c1e2a0d05 69
    0x80c000e898800d0560003090900a0281c100810020b90f805010f07034010f00c902a51580410040709200c00b40c0b0204440c2e294101c000c1084404485405401c5013400409582d10080f03800041c14079812201101d0003142012201b11642c0c0c40e540c0115140d0b04001d0024489541320030300e1301560b49090040c0c4000e4070080c0034040d01c0d805100e000411012000b490488048514030600301241004101103401000524000c800c44e0302200040c1c406209269000390401c1c42d000070001180900c0c5900340c002d000303402c424005030340c0c0e0781c0e002c8a0003904960054541c02c0510010801031406030300740620507902d00030080b4002c0c0e60f240080c016000660048406070000d051540400034141225062841d402c90b08012a0a2010b612180c1411001d0390318058851001d04605642d18602034500005a0001142c2440c0d10380c50404040c1d0000c2130845442c1c850403e40c2c1415400010050414210701001441e1000503d51040500d2803101d021090540380e5810f04851515910355125001d8010070044c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 405794145 1250 405792895 405792913
    0x6080303060f09040201090b03040f0b0123010807020d0318022205090a0308010501210507020d030b04090206091e03011a090916090b0303040b0409090203160f0b0f070b09 75
    0x201070702c04903064015104031440c408100060ba0080d6a1400b9030309210300701600c9940c2d40c0b0300503403040c0c4d07071802c050404501880006a1460b94202111807004912051204401c40c80019606000181d41c1800960004415800880e10030350201030014010088040d0800064020a0410f4201500400c40e034403841c44a1100c900301e805080d401545840040c88101c0150310b00070011b603018010613040051580400444410a0598020112850404000c203050210300070b1356031062070031040c01083c1080c1e21405240b8052181c411002e070068141490980c0402c10001d00400c080d00030041c80f400d0305181840c58509201e900100144891b154800a001504001400b10014a143d489070b100440000f000345c140810b40c011103814503000b00e82c075140440042d0071402981c204110415001c03400046050985e00486680c500980c25504c179411030f80400354050016014800b0079040b0741c0700410180041e040101030242182e000c8a04112841e5640300003007400380c411158650088000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 405795395 1250 405794145 405794149
    0x1c120c050a140a1406011202060d02090414070f030b06031b0f0f360f031f0f060e010602030703050a0c08120f07051312021816030609230406020903010608030306 71
    0x1041d1a429000700025813501047c00e1002174885e500a0140c0c0010030f0440c9c010085070162481107100500a01145002c000d00840e500f804540f907000080c0000301040310f041c0a40b107980b15040303000d0146840d65640301d10480198414581040c074100c0f040080184049114000d0a100c910b0b05061076276807101300e0740d01e150343e0b8095050144200b005d4a83c410040400c50a08489850103860340f0f00b412043d400000c1c11300c60250020241060361501204002203954800352000171036140802010f51100c0c202190320000b40210800b5038801c22840021a0162015152402c09440d15001800302603a95000d641c00036400301c0ea00000700b40a001c0481e20201486074004176620381a418000280b808004517500c41c4a040c80c181980303030198055403a80048880c02c4150f610180c0402d05244d420075001014800410b00002c1c07404070046104061401003d00c000c84000c4901007200c5203140c004a400030240c001c8070180e9003005840c5d01c0c0d46003801800c004015000182d602e83c0b6003002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 405796645 1250 405795395 405795413
    0x406030606140a050a0309020f1c0605010e04080a080c1c020706140601120518060702060f0c040e04060b1f050406020705150f0307020a0c09050103021c120c050a140a 73
    0x20b41007401d014140b00603080303603501030f094a400340321a140115515201d030001c154000980103145402c01813a400860552041c1800b0303000083c410101044241c0ea140d400720030342c88081c2c4004000d031504105486146100d0001540c1101d038406105281501c1c88100c0c0158590a980b0491120b03000329854041c0000c5206030300301181c61403000f01c450310304500000d010303011040241049590394000314a131030076000c0c00a40e00c204104210749403404e1040d00655a0102110075010385003d2000040240f01208241d400b140c4d008940c0710000c1e02e40e80d5a42c405840300350342550f00f0142c4c40700d90500d404a01c1d0512003003115541c480980c1d85007086802410408240c204500912003180c0b07030951018603000b2919582c00c000040c51b280c2d140d44004070705180a11901405a502105011800305002e80c0018102c030f108560042030074400d20010100b07180052009040c850781000e03021400c9010341081e4288500c90002d840303121401d80d4074440c200304c1d00000c502c0a42e00041e884010042c2c510 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 405797895 1250 405796645 405796667
    0x5030a1a070305010810020711131d0a020609040c030b030a0804060306050603040f0605070c0b0c031e04050706180305030d05090705030304030506130204090506070c1b050a03120507080406030606 86
    0xb14040c8041c2d81085c0815654201401840300320680c0000c0f0001403100c00c80222180400041000004030307180540e00001d011000b81000060002d03001c0400304080010b401d00e441513000d40040d05109a0500300310041005186140038192540705480c01c035901403141c0d482c000c0c4101a020744070350030030200501b2607400d604481c2c010309041040c840401d00d9644114940c030742c4903d000c5116910b8000480702c404042000501548501c000d000140000703030041c0d4411048144000410304500024141440c0182c0b8080c10b5600504001d02290744038513078940e0186401200400c26980e266103039865a40212800e042d01039030750042c0103d10406100800080804500443c14a810f60300c0d8951908000303880e1110380c6814801c3e44046440b0744e0085100705801400f90b03049440c000401806040400408a600301244030b032801c281c02a007005881524009407281d62400e0442d607802d450740403030800300360502c00b007030106000080c9042c009101410880c2d074081217051501002070300b414492 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 405799145 1250 405797895 405797897
    0xa06090b0702190f1103070305070305060705030618040c151206060512180a1a071808101d03031008060a05041a100807091410030c03080a030605030a1a07 68
    0x4202003810303280d086043c0015005902101215124901404265003c204168041c00352110000612502080150450340604152005036407000c000f104c1030310044910540c030079080701158468012103420f45074828860440d40038840d2326502804150450381d84d000002410107000c0344200860341c0281e40045ca11414114180b09600403010750301b0300000c01c06440e84040c411a601015000c0045401554101c2c220004140c100c0c040ea00f24100b041302d0010210703141c00401c4103609154031000f0f08444240026010b5841e00392401005441004864000b902482068428009040c03004500a01505540c3c030b450511340031040c2d04080000780707440c14452502081001244000740954030010101030100015600c205582a000320340d5045040180328004001c1042c58241e4040342d20b80f01824025509540d8000518400101902004001d038559807410000503003d0409040c0b19042810042107141d101c00200303180c540c0803903094030007220714101c007421401c040c18a43d40008803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 405800395 1250 405799145 405799153
    0xd090c260f060c090d1a010b0a0305102601020f0301090506010f03090c0302040b01020f07060e040608010603020d0633091803090b091201020c061e070e01120b030a06090b0702 77
    0x21400384a40b90007070111312401a08402044000c2040700701d000d01a001d59890701b02c2c46561140f841c507072207400a1100c1c0340400c1c505030226400c0c10f1083d14401c04c440100c420751402150149903a071411002d42d05042d110b41d02402038240c854241030245029019000e0006090710742a40010200c0022101c4a424545880c007900d0200d2038250f100d800307803038044e140461040041d10040346400418500d943c990f005021010510360382c0b0687e04c0d40000c104583c180400340e150181d8600b00c64541c40000d5001100c0154071000074482d412034400c0b070081c110000305851414801e140c04807005249041d465514107414010030300d041c86448e00c02002990600c1104084d9540603051301080e01440e0440038010601c00341c42c0d564101c400a074100c0d520001d40d100c0d09895170140d554079054400400303001c3c085500307150000b03610070601d1041d18140d90360115460000015a2002c0d10102250754954a50000701c1c50b80d01c0410003039043c41d104880000c3c511000d81400482c1d404050180c60031500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 405801645 1250 405800395 405800401
    0x3031f120b13020a0b03090c040507141c021608030403020d1409090a02131403070603090305030a050a0204230901050303090a06030b03160b030108070e06060d090c260f06 75
    0x1030700611a42c8208120502d82c00c2c501a800014200750440d48481c590034400401c2001c1050040f4003c0c5945106440c10301090b2240c16041d50700b6a80c0d1840ba52122400380048022050302261020129802c40e8006190051035164810003030720b030307007030a40b84814004207210030581e04000c40c65206459151420421382c003041a050107118400c000340c880c0340454080f030644006641103d13550308000c1003800d0010707a99500043e10442071241213110340030303d81d00082e00f14068080d00000719815a122499035551804a90041c0070150904914540c24000441d1812500643c445152451400707000003c403e00c00f0801d0a130780581119019801c00d104480085e200d4541c40f005507a551b00b8041f030b140e0105008645000700300704003500b1440c2e0a01c000a603403070803040210305075841a4103403900c05484150b0820ba8660681d0b4094102808000207034091202d64001c100e076510480c07035010444e40d20100c0d1040d03980d000301e02400d1011103091201040008001c001301c001c00402c05420b881c6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 405802895 1250 405801645 405801653
    0x11d0408040303230c010605030c03010513020108090a05101e1b0e0d1a01050112090b01030b06031606111e0a020105070f08030c0711040b090109110c03031f12 70
    0x20045101c0241840301306102003903242d403140c222900c081403d82c40e40c0c1d22181034461a0b4060246881158044d0140029182c040d041c1801068410340681002c021f01e44a59801102c04560003040b000b4140681240341c000268148a080410501030502184d00001d48850079950011005440c10b40c80c43e0190403c0484078402c9119010450b904091052041c904082400c802192070002e00020b0031080380041000707520201c5059075000c3e41c94540101b07203c0784160031115124000751148140f48010030008040e4040281e100c42d015056070340c0900285e542242100709900b02401240158524407417243d0100010a0500c958451184140c0c4a190040b41c6400b0203007000703810450001442c0041c8160402c40c0700b006940b10101c0d82d600d03d4125141d80e001d4120381d0b003c68200303110303600100c9940f40a000b1007540388402040f25082c0d91a03c02103000501484403c1d40568009000c1e007100c1190034400f6511850b03e000c1e41b040714424245141a008482f42c010000582031041484041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 405804145 1250 405802895 405802897
    0x50d05042c0414030405030a0803091207050606060f281e05031306020f16230c0904050f0111040e010b0a050d020c070e07031a030304122603010e011d0408 68
    0x3060304907100d82c201040030f1001074110f11980d04200c1d0588101200b50781004520b8008501c0780c0c00940c252184a40f0f030142c1801d007441242c2c006031a40d0700c0280030912a24011004000383d05880c20001c2c500f4150380610f070b48403080d2107110200001001455112a50004e407a90150b1099100321983c003074a00300058040e0001614035010007410452400402034940d04039800710307001e10311403511800c04c2018800002c001d28003c0b0b950302c1ca404000190803842c0f810700382031900840003802c0003416030020b000207108010001d4409204001902c00f0303218081c0724500002800300c4086030760b070307041070b2111802c1c01e0b06920290b0b22080c05c00180c190036a0010a9440d680d00c01c0a0240c0c2c3d8605520040b454440b0300c0d0082c00a40621f14240882c83e038155200c5007411004040b0004403441610070142c4034001e80c443c04c410941c2d130846420016100703000708400030031142e14510ba10325110350307251503d410981151426042000044c09800526030b0002d1802c02d291048030710398a030580d141186 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 405805395 1250 405804145 405804151
    0x910060309020a1a03090f0106060c0b0406060906080a0209060607170307170a02031501080708010612020c06090c011101060501050a031a120318010203040f050d030c050d05042c 78
    0x3050381d0340919500310b540d961084802407515544441c407010b80300344d40346055401a20191b175075100c0c84004640300c141c18080c023070444c0c11940342c2c0c0e00e884165440302e0100c2c44001b0320803503419a4829011410744291700c41e06010300025001424600018810f226a43c040a00b6040c410704043c806c0340000707604d5012000036103072805c03043d649940740e008064529200110012802140c98410000003400903400385216000d14018050846030b00c5005445601c026610751001614034801442800c4c043c50035140c0e8180010b900500d000c0302008082c3c00d203442074418035101c0c0c011031039424956074085c2c40001e00c0c5180784000c1080510302400070300940f18012840c0e091503100d00b0138101180e0342407200241032502400f4010728030004c0b094a610b0303074880e80381c07122441404401c2030074a500c0013081c0c4050340e440f008a0100142003030104140690f000310201c4c02c2054000c0c1e108000340041c060170b1920141910b800d07880701d0174000b5889040c00040d914551148000c00d100280b2121a982160 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 405806645 1250 405805395 405805397
    0xa060503060f0f011e021501151220070503071407080a1101120903020d0206090c0d02060c1204060e130c020d1815261605131d15091006 60
    0x58420742c0380c001603a555503499a03209200350140a0045e420341c0103d5942d025105aa8141941e81c0e259840c1080b940310014840c03000079802c1d03c504075400b500c5c0c0d00103c104603402032031220703074803d80c40c1c10180ea81c001030084038030360000300d082c0302004080424608200842005848140e0800d511143e40d14255400035098624900c24151240d000c3c1c1a14004500081014030903d021824060354900e60804c20400512403080012611000850044002d0301d0013000c3c40a40d1895408010300d98002d500700385481d00072500340c201c1884091004100501c0951182d0301605008020022000c040c00c0058410f181458540c3c0041540828000c00912980c106801c0307108601c0c03100350b1108469040b00b040040f008415004868008100d001d01110400d20540701044140a000d484401030700e140340080c81e4503c0c1280c009005502600750410162440c220180da1490034034100c0c212941c01c003100170028400c0c0140d414502204004031b150541e281903040c1440d41034040ba41d49140b0901d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 405807895 1250 405806645 405806659
    0x140d0b1506040321021e0a1b150207080f07030c1e090c02010f060503010e030703080702030c07030f1e170c011b2a02031203250504050a060503060f 65
    0x8a460703a20070080d54003454114040d5203050f4540382c909940c1c0c2210184210261107941015251070b00d0313401400c1c0d1007030010300151049030119912020089940c00c6001d0300d01010325800300758800ca0b02002d506540480e40105031082c640031040c1e00305242d0309070070581504582030510200f001a4003600449400d0404041002e0307003900107451801c0341c0e4003d42140d41c00c14040d82c0c0c03025815080380003020941d40081110355954070805003210401d000d0a009078005205420109008403105548040f042c010703213281c40c4603030b00580e050402d10b410466030034040102c400c041c019800b1800070181d4002d060040304a1139078890000c1c2d41c4156006408100340000d805c1c407828020b41028aa9104008c3c0c070004042c4178800140040100081c921402011600c541003c1c00c4000001c550103a0041c0c0544650540100340c0c00310340d0b20003040c214603044154580e11103130f4040558035400105030344e903640d1120304060420444012561091040001c24020702c14540d44100786125000d500f00c40303034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 405809145 1250 405807895 405807931
    0x9021011030306060a0509091f050a0503060a09030c060e0d030f0b15090d17070215041206020d060806090d030b0307060203270d080a0e010302030c09150f0f04140d0b 73
    0x446c1d140c802e440c0065000032801c001d01c80784005406031801a0005131441a1019444034140064000e440c0708555065004a01140d4200051f60007407004034080c1c0381c1154a01240e880315820348143c001c0c400001e07030080c4980b211040c1c1c0340c4a008030200409609100351350740e42002071500d103500250008914000100030480760b507103c1c1e104c0b24142d848064050788082114151029070010b0505a00400c00c82107240382d2801c1440894069039141c0c8090304054078a0b4a8981c000c2d080ba04001d064507507600c034041030200c01001503030f100d07528010003072040b1410b102c40101035800c89036845000c3c0e48038400c2800300b590040151400e1118402450710040d1001d0032103520032a121000b40c0d040f910801364807003806034903001005040400c5e15001804d00792080110304910084442000c0035505022984c481c0c502180300e00341181c1d16412150410303c900010001c0c540c440008940c420b600040c04010505d548124400320303280440701c50310020210740b20800b00b144010b141c40e2107180c2a10720 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 405810395 1250 405809145 405809147
    0x402011d0a1a04150906090e0408130902030601020114070f030e0309060a05040611060103230f011505040e0c400c030b0d0503090f060d020d09021011030306060a 71
    0x52402000303100b03080c84080101d03005214859200b03000b110040d01c21400b500140301d000c1c0c5640d4084440c40e50b1003509141c9061a148140070307018000f2180c01c0d10400c1421117204000008c40040d080010700169a400e085001a00716642446a000c90511b00d10400802a03000201000d1082c01c5080c00b03e02d01051a59050030f52046071030040d40300101043c51015550700a0142058401c103840e008501c002c4e1b40b84103030340c440f42440001e00201d601c6c8020114400300146050039006d08000303e03080810540074050030b6a9040c1c1c420894615070440802c03640c070f080c4c02000030010066001c1d0010f80980f1001c41d08a640d080001d042401340698400e61080c02c14161340348502c840d4070051090a006000c50f8007500d1079010320301c002400c0c1203540400b1f02c2c004580d8507034568010011850620b0010a101c2010904101654001c41c240220502503c1c40c4c0010701c05000e618200241804140c0304000340e680c1d100701c8130810081001034800d2152800002c43c0d130021011200b0035128401c0c0c42d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 405811645 1250 405810395 405810409
    0xc1203180a240b0409050d08070203031308091207090f060608040f0b061206040302100c031e051e10030303063c050303070501050108100b1309020a080a030903050c090402011d 77
    0x1c80f141c02501d040162400e0120204201c2082e90382a541d0215549800004903030f00d0006580041806078001143d0001410703002c02410030540280c190b14006060300741003070601c505640001d050549410000806101510608020300a10700301441142810345941e8a6008000f00081400c09032802088540d5240d10041c00c920750800700302c0e0414030f03181c90029101c2801580850009007014040c007100750090150082011a80c020840d2460502e08076074060103000c0c000068401c2e161b172045000700100310060b4440c003062540341042918600d0010100d50056004040b201c26891680c002400c01c588090b032601d00d12464009039010301506d50043c1242c43d40042c0d8117100000308071080040c1034026a040340c8604080d03e0702e401014a0070070a9482c00050701d0381c400e0f007880c450800f040040e406180454000741407000d010386c548002c24540b5070f0040c02900420321114040041044c2040200d01c030400a071640100d50406600107040e500d0369911700030307150720180c0c445001d60315400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 405812895 1250 405811645 405811661
    0x906060a05040626150703020c06070e090a051009061d0a060b030c07080412032705030304030b090a020429220203040f021306061205010e0105060d020c1203180a24 72
    0x134017800150501680140003944101090b0300c0c0c2c5d0040300d0006502e11f004050f03900341480064114030003541ca0045490041a00600420f4600712461000c94010010312480003d4020a0802d58002403803400508007517000500380b400260826000740007041240040d641c01143c42d0502988801540c540f40165003c2c5410000e92103041498030b9050607802040c01820b5105031a42080c01590f400d008400d00140c0d00030140c1603030040000300002540c1040703513a801584081515244055680000c040e1403091110781c5a405c000404010031171801b68007100035801c00c9554240d003030320f0b03102e0359041801503c0715a02d07c581d01000280c18882c502444000c07160340244010284070a040c44080103001c2c42c0a0030b000180469901c40281d006889810306032015201251403076883d10303081107032551154008070841c45c0c090015200350b4130100f007100056030481e5002626441c20b110b030040c400380200e0050419a0101007a500401c2102c94842405940c4512041d00c541c1c207401d81201800c000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 405814145 1250 405812895 405812923
    0x70f0c0518180703030e010c060b190602072903061c060f1a06030402240f0d050c07030804120c02030a08070201140a091e0902030906060a05040626 65
    0x2204420039540752490010b845002c91004840c400801541810f640e0359050000a002c501507412280c019802400c0355064070f1f103e0940400c0414200d0040b0380743c1200100c40050004140405100303140e0140f180e140903006048a540c0c662122102006a08000b0402d118101800101065068070740d05880e40d9441d42104011500041c0361500d00010f24409010911591410f030101044c103800c141c401000400c0200b04130300f15115070302080032a05000114042086a00314400c1c0005030300806440032031200301d800c5481d051144040825524020054000024200f18950010350004629900240c00105c26003410b407603448107955000d034001010754184107480c000c004202d28140140501c43c401e0b600c0b101402002c00c40c000341402018000780204901c54024040e0010305d1040e403140c0d80262000c40c81444d0b544d00c041080741d00545041480d80c0203102000398908141d12903000804040e18200042e07441c02c2c803901000365801072824101e0910302410301483d002000700c0301040042d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 405815395 1250 405814145 405814159
    0xc0309080f0a02040e072301020102280e060403120e0f060c16060504050a060f0e0d060504050706111213051512010e0c0307083c150105070f0c05 64
    0xd015034142d650820000480c484c81c148400780c000c8240c0800c1410480b00300c0e20019100a001c021200e00b1540117030002da046641c24040f4100410845a0103401100140381055004061030001020307400e680c000140141d001b00710420009039a00f07210300c24401c051030841002c42070b04000511105414a05544c80480400c00420fa20b50100e082d612103032030010f842c281e044c0d03516001d0360940100d00c1b0f05a0301c40c901203020031045004807e4020034220b145042048521104001201002043d006658043d912030400080000400c4030201904407410090512000d00b03136100e039210b5454215001002e0085203007020622001ca148018240081c0a80d100d1740d02d8200c10b02c0550402021586051b60407400090305410003140c02c1d0192000166851540c0d5503100144e07107241014001c4070107028510820156400c9202c40c0f4210420060850905001d01e454940074400f0080c101c8105081c41c0c06e1540700507a0803204a40380203a0000003541d00d240f09080c0014648443c2d800b01d43c10047d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 405816645 1250 405815395 405815413
    0x1802060c010213090605012001020409050a06050f0409120309030c08121b070201081303202a030a021c0606060806040e0f06060f040915020a030e060c0a0c030908 71
    0x901900581420315001c07800f28102566100c110003507802a22070316000c11240403000b00181201a0502c0111901c0000035151030b90b42d504120840744201d54082e252030380c1e1002800140b51a505c40e0446160031030f8140465000d5850b807060303a80025001d002459602e226600030540039810060b42c06070012205030706c03201d24001c074510600781107a49840e1100c0040d031814010a01506131200c040c0c042c3c3d503180ca99540c14282d2680c06206440a606201c400030149120f0200e0401c0e00c80e0380080321002d0700050b03412890100854240c076890703407990100c0b28400d400c3d580300050310640442d01280c040c6454400c0034290840c100880001030f1030b06040403008502d40b41c001c10b07980e014082c1a101041602d00903a0810f484982c103c2c03540e030490f0006000304001e403500c805507121459004000003504119943c40081c0001030741c800d01d1480e81c010a034461660b40511504042401590241c14030303103003100d10030b05641f140780b09a170180a400362281d000e141c441c00e024400362440104071400b000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 405817895 1250 405816645 405816667
    0x20123060f060711120d0822081801081305030712050c03030103030804050613050607120f0606090e010f03080a0305040602070222110f0f0f1201171005010e0604180206 74
    0x30059004190007841042d8541da00d60000040d06c0c0a11102a036408100361a002401101c0c1d002d007071405518040c11503c4038000c00c1c819401030020040c0d1081080c0c2c0e0240501c005848100300402403036010400b800c1980c0071030b2010048488880c1d008683d040d041d500650107491038007030070410728694400800080708040d0480c08503402240200c003110042e03650300c160610a50035070980201960400ea021940460059a4014000381e114001003202c040c2101c00c0c00c01c5443c1e5901c02e000007084d1201c10031000c0c0c44006030302d02401c40e000d514600300f41581c450700c00504c030715000c1100305503460f000101071000c1036050b6515a5802421105022022880e042220842e0918074444c00d01c2c08044c101d125401e40201c5240c14511282c190402500385225800354101414840c0d02200400010052214218540d40070f007070300e07072181241000b00001d103910307000c140a1070200c8c0b80d03d028014400c41c2d80c1842080c0e4049011a0003040181e54007034030829060400c0d0b002500a1404a0719a80754 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 405819145 1250 405817895 405817913
    0xa05060405090c04030804080a030201110307120c02071a0406031d0a120c080d0b040b01020105060306060d051c0503041b05010210050406020c0a0803090c0904150e03040b180907020123060f0607 85
    0x103404be85c0240281c5800d69401d0340a072200703880c4a40400c4242d007203503640720402d40040e8441c941500541c0c4c81161344003018840c203207000402640c1104005400e00410b038061140050030313038030716a24140c0780080b9000683e40303030710401000d800f040c829282041c486100e080550250b90340304070340c55201c662250f00c6d400940040b511a83c82141000c15928055105100f000e03c82e0030700900400300c130344414060041d240c51591098540b40220072042010780240f404c5c0e9600d10b134180d41c2d0242e59143c503003440480c624008a100b00d52045100c030400c06681d00065a901c11014030100189644451400c0c00080c4185a41e00b42140120002d02c0c0900c108200650300c00c82c607000540d60000c140d001084000142242c0050904803203040000004005900180081207104100d034075140d240c50001c1090b41221501c0412160b000c030388c025807410078182e03480d00051540000c0c81810501508401102d960541c0050a01500c000140c01d9036034840c802c1410038005080310b03650f0715803800c02a100c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 405820395 1250 405819145 405819163
    0x9050103050c0c060403030f0207081303350310120c030b100b03150a03020a0803041d0121150207110406150c0b04020301090c06110601050a05060405090c0403080408 73
    0x20034a03041c00a25281c40c010100c0d590341007104050100e07079840381d50039002040384000364149035a00b88817060004040038020110381c12100e181c0e0640b103103180f40807580c0440c2e503102d00500781c45404842c071310803407418900c05100b04011202038881e0341b02c00200c11104000d61121000c001480c011009100d501c4010078140ca02440f049078540d80c1c0e121240d40740d58050b02c03e4000d140c0081000452106014180c04e241ca80010004e1100701d50b82d40019001070fa41e504100380303030740000408000f520b02c0c001e0421104001c9405540256141c240305042c04081c28500740481042d0820410800c00103c5201c40c03501d07141d180441d2544a42d0810800004981402d58003031031602801003282003582600c920b1034010f0f565090410012583c3d1800c074100701a01c01c84c5c05640b254070120020703a00c8218074024022554890041c03810002c1c0c010728004042c2e01c5103004104188042c080e513291401124151402525030b0365041d1200100d0000904c11036001a000c0c070004680070034209000320344824 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 405821645 1250 405820395 405820397
    0x60403080c0c0a06120902041508150601020d0f180b0a050403030917121b060a020702100c05210c07030807051506090610030f0c020c12030304050d030209030708070303090501 77
    0x40100042c05201180b0054000c40021a40d4021192a03414007500800d041e144040d001044405d485258080102c1694114440301d4000941c1ca01d1042c40c80c4503410b074030007002d00c0207040051042c58064944d000007806001000b990740c1002000790300021800d0002d00c000e940d9155100078989000b40a0340290004400103446020001007640c03190602c002912440b0000e05581d0a0301c0d64482c00c141d0042d1203440c07120100c0b170707000810b045040c0300301c601c508054540940c2c2d401140c8100044041100400d0052141d0001c2c8034020800010300c42c2d583d1814200e1081d03031480248500280c5000e03080d50301d2064452990080201b001c103001030807580307100d030044610710700201710409800007080305c25603008420ac00001e0483e240c4080500750f40303541030070001803c100d0138440d0019240d0101c82c0d08003580c0158881350203070030b01d401100700303828040c4081e41c00c604140e80c58a858a0f24001c240301007603008500340364555020f01044006020310000c40e15035503500d1030040e080c64051303c2018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 405822895 1250 405821645 405821653
    0x2030d02010c110f030d020304020a09020a020303040c0504020a080604051806090a03260601050d11070f0c091a0609042a0206060a12060f02090d061409032502030c060403080c 77
    0x10f4000b03000909510740100200079500b00500e06905000941004009036403041c4641e2002902050390700c010710101049a02075543da183c5800d1401c00c0d00341582c00305026a20411180e000c03140c1c02480540c02c03079401c44020980c0d44a549103e40d09032039166480c1d03024000e0b44180218070700002494001244692100f0141007940c0c4007a0602c60074200700f9094446031040010184d44c46900100041c101041c0e0014150704c01301041451703a0401c42089540e4280e440b10340c002c0c0300c9507042150042070610000c0c0080d0b020540031403554007402c801d0328012136000c2182d01c0581c0e00c40c0c11050304040d480742d11074080410500e001b40d92080003600800980241d2021030b0060422040d500d0039907810b00300d030100e114031664407400280103021b00715969560900c107035405a640c2d1030000b00d1003402400c01203406c20000f2a0405608000351010b21755901c100b240b41c403012410355040007500ca1541c620314883c002c03400841d0610032100c0189500a00000b0003008004c0c2180103070040b00e0108c1d080f1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 405824145 1250 405822895 405822917
    0x109110103090c0e0405032502030c03010209030c0f03030724061a09060d060e1509010816030b0a0e0105040b04060506010c03051b010b0a03050f0d030b1509030a02030d02010c 77
    0x56003214502c1c1c801030f000a8150800340850555007855980151292044030310740090038003040d1021880745c00c0000b91040c89481300b81545001c001051101904a008615080c910390029584007030901910f0f00460030700e00460425a0305105460089420046405d5000d030040300001c000c0c00c000f420351078505e10b0b180e40030070a000d00c0311641c54400c4980d001e0380d140000300300400255801c48000403000d292108000314004190604560060844100d03e001c0099990300b0004183d405030060302d0654000c0070b0341c89507514200d0030002101c1d08820b009620380c42e4034101c90050000c080c00f015641d801c200502080112140489101b00e0013920200f0690b2100c00046400840c401400360004e1001e020740c800141101c2180c070503948881c0000a50a40906c010a1040e0402d81c416030301c6801601030042641e01c18007c40c01805124901001907540120001d4441a81103030742050202000c0354a4072291020020500d409800404039180000e80c21002030181001c504240005001c0d00d0701 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 405825395 1250 405824145 405824147
    0x10f02070b070908210d0f15170609060408090312040f170114150103090b0f0f060102060c1204060f39020a021c20010914010e0405062101091101 64
    0x101c3c01d0340101c40001ca0301e040109003100845da001765511160301c1e0340d9002419541d40140c80703160740c1d10040e40c500c81c0065113803500542c5505160700480c0348942101040100300b0310003041465015600010b40b1742c43c1c81c0c504000c2440c0c01c081c40f0580301080400100842d590107840c260303138200d481e1003002c030b0030001c080c000c124242c0360220303981010303105206d01254074038485002c440c2e103a00040c5030000d00850340c0d44500c00d43c10402c1d150810344203800000d11100000440c042075118100f80010300b1107080c4624820740c1440ba06e0070408000001e10003183c03c001007a00600d1107103200304814003c1718100742c0c541059484210b80001540f09480a480c1c00c0c01481c00c8202c00006107401601c004680c1e6020311a0a000486c01003d100c0c01c1c158100000504000c0700da20f200d27481030000000850034100141400070107410005032207005004085003603034018a006005041510049000d494442c00300308085032807050b660a00b0b40c5807540920301601540019482405025254020420303000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 405826645 1250 405825395 405825403
    0x3050910020106080607110a0b3d0906152d050d0c08010501120522080a0329090a020403020301091203060f051509040b041112060405010f1511030307080f09150a090302010f02070b070908 82
    0x2c125525605002c00c1503510500582c414ee09000d03070056110326225100240c03000000c811a01200483e40106d440f140640451103030500109035800d1260881d4180b10000c1c20021146803030a98aa807030300d000036806640e035941024100c80802c800300300c0c4082d51a01e43d20307036084003c039840064904203185e2900352202e0118009035140891034400f142c1400b085c400e03840c90080c96140304540030040000140c50901c039421503d40031b4610b40980e1102e20350000c0984460764803441b4610b6290390140015070f42d10702c100180e1070280300507642e40c0d0119070101d8058190888503540c0203240c1003401541408440007440021031000c424030640e92500c0c100021a1028000c113604000c00a009010054a03010842104880c50801c02400c14210702c0c42451644102c44440000f40c0031401d1010010880780306c1c9030005104809050015003d14083c2e021910041a55445c1070b2606095400d05000394030500d0304144440d0155590107150034540b80c100b81c203480100c0003801c800c200040c8148082 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 405827895 1250 405826645 405826649
    0x108160f0b0c0a021305011706010e0f07020c15041815060c022d0a05060c0a020f01050f0304120206070f0906080403050910020106080607110a0b3d0906 67
    0x428100e46801d01d455600903401c854120000c91080c1c0c210040542ea50340c403d8210401070b00d2003c10190b0400320b010700c4200108029a210313030321080c010f0100c4100c085405621078903040d034400042d074402d00105e10b072202984806070031044450f021a62200c05200600541d1145580e540b0a0031040c400f00045544c65050700011140d01034061007000d1103010303440311250000b400410300810201c011584400440c03110560000c40081c01c0e1020b050803141c074001000226603441c1003a0100c43c3c065100c80d01e07104024411603d408601d815030b07004205648502c03010210b003035101e141905d400c0a001c441c0d01e060b42c01602c5680c000943d2a0b2048004420341c4225583c0c0c031601d1454582c054881d000c000c0c1044060210502c5441c001d03485c2c000305840840c01c19400421010301d05107002d403c1c400090141d201308403010070f4000c2c50081c0010424010390340849030360120f585203003000d42c0c9040e03aa08048800342c40b540010b03007000401c418031581d00b10300c25200e0a5040e60f8441100403103000b8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 405829145 1250 405827895 405827909
    0x42619020a1502250906060e06190504080a050a110603270106030f051506090c1b0f0304120308010b0304030e090601021c020d08010510080402090a0e0a0308010816 72
    0x56201805020415259102110b030240101d588885000c00792803400100028000141911040b0410100e0007501400e0f00900d4030b401e1000910303a001d4041031251141082c403a081d000d440703107016800c43c460001c4400900c040d50541d84060160701d48280c03901340c28030f02130301c5184102d84482c11030320b407130070490340650149040d002004041100102e140940c9020104065507101c0c40000466961910042500c4c441d42c050102c0301c003111018a25064060075140c040c0d074801c810001d0002040e0101e503116481c030404000001c9441901b285050101d0900d84820301020400003801a00d40003a14101c91003511110320741c0e0780b0b4440c24801404126800341c000380341503101c01d4040c10703e40113182e0000010701c19642100600c0c101ca100885400040d1070050b80200003082c52103510402c2280544002c0311003000130030300038000508161018101030b1140d100440844e40090a69000043c104040c8090f1121072034141000342000501740301e62003c502034503d0035440e00d4203c0913414192818 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 405830395 1250 405829145 405829159
    0x60a050f01080703110301061e02010b1c0c03061406090106051206090c0c0a030504170a0c1a16050d08060612160201060b0f030406110a1409040204261902 68
    0x80e900111020603024010381c0c14075684824510802c07103103030020341c040c0100da01c1d040d69441d0104490030703240d607005488000710791400071a03050365a40d65510400da11003000340c00e183d040c0700e03080c50000c0c42c145500081200d031811101d44842100030a10320700c1080110b030f0b0f4007030b5a03980701e400b035031310f0300ca8000d02c0100a40803a0005070186025400e040c0c200c1c420b0214142030480c00f803416440c00e0a581820f801184000c141004071080c074080040107003c00a0292044199554232110501e200c4c3c020b185800341c01071401c00000014806a0f5401090300c0e8942c21419800c3c02c0660b21008030310f282400203021400003038243e050801c111405803688204442090f1f803420320504480d400c001d151411952112000200d880008010b400e000d502c09480a680382031030321b0550112030010390342c29440f10062100c0e840032900074000490100c980b89409030343e83e1031800020000d1145400040c1c5010760000080303a903103182c0b0490180c0150310801c4900001d000c540071681c07080f46020095224803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 405831645 1250 405830395 405830419
    0x907150c0b0c0a1b03020a05011503030815030a0507240504081c02031606050f1b030c0904021207020a0327030201050f070c15020d0306140f0d0605130b060a05 70
    0x14081d001030000c0fa00c0c900d8000c0400480850548840e005020150010381c001c0a101013071000070710500c50204084102c6100b01482c1d5a07001d0054503004294120320300e440c05070700320700d601c00344007101d0440c1d84802910f030080d84490b0000d0a010300c0205014210b0000f0089103c198002c90843d821f4030b803130000401c0b081c19003003c0f03c1d08900b2031102050440c0400d002c1c601154040300d500020300391080001041a14204070500300c0c10400400c0403a0b03264481140c0d58014400104582c0c2000c031203000c0a540b1100711000c10042e02c0b0f041d031808003003800001000040b0360f01248001d9401d220703640e40f166410841141403012161060b16a50907444200d0030401580540c00034480c0d405420079030303410622140c5407012000210fa201700d0820307e982c4007a40c4503a40c18481071900b0360f500c0c10200407190508440c80c50701c50394130704041d01882c880e4801d09155139a101c401411141c0c00300b0b0900c00751408424000c840c0c1e40752101290004000c1d40421f03a14901112840269103001d0821520f0003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 405832895 1250 405831645 405831661
    0xf17031e0a0306050405090d02010b0402030708010e0c3603070305101e02070521031e07210c1407020306041704030c061d01030e0a1401060e0907150c0b 67
    0x2078819a585024180d80c2e90000800783c0740c81c0522445440c00c039002d00300d003a802000c00703800d458201107480d02c40c0e88100100440e03150441145415100300203281e82413a50f0308204074100d4854080210386c4c50381c09031030ba010300d81c0c6030000c0440315070325440549400f59010800e141c0c1d903d49a0100a10315080841d20174826400f6610144400e4200e040780b20070001a01c11910880e44240c2058031075801c180c50080061500f40300c00102404040c0c0d25604d9481c0100c01c5441c00c1a1800080c00f1410b03068011400903442108208441014611411a500c0113440410000d280c808009404030328890001002c0464a03401d503074800380c0250180903940d490390740351000c80e448214010881d000c01e02003c00411504540d5101600c4140c031072440303110701010301005600940740194100b5003040c020421902000c07590301d20a40e8407030900700c3d1184a03500414090700c0c0795041040e09040f00c1042041d00c003c00588941182d411504c00784516107204811200903601142c003600a4068a0201e02c0ca0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 405834145 1250 405832895 405832897
    0x60a0509030d2a1106060d02040902030102120106081303090e060118081b06072622090e0d050a050706090818040c020303060f010521010f17031e 64
    0x110003036005691806000d448180100c5110042c03141c90781030300821041c0c54500e43c0c450300040201505041ca40d80d4050401c2965490000340814003842c2031840d0441152240c3d00400507980d0f000380203544504007049601e10b580000d00c10b0303000041081000c18010301d944030f00d01920036010350b59a06480d040c140100012070001d0001410415500c6c0e500208000c40440e00c400790410b180a86040400c010204590340d254900640c81111b04010802c009032140350041d00341101c18145100d200c202c6190300c2002d004502119a8050001c500c2e68980c0c1201c806410699a080200b0000c89440351001c960b220300b468250070125400f00940398500c0c0c064005443d025101e10750102e11008244d80d40401904042508200403110954541161a05000e030380c2d95071259200650840c43c0800000c0d002d1120403e005051080002c1c0034081c00300040394800341c20baa01c0b11301e1809543e44d8000050850783d00d00c01d6440b50007641c0c00b5007030b200d00c0100440e8a04c1122001066010204504140341 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 405835395 1250 405834145 405834151
    0x70201080606090a0b0c070f3507090f0e060609070507060207060c0801032a1a090a080a0201110607050912010b22060f12060c11010905060402120f060a05 68
    0x201490600c212a0b03103a8450700c00a0140c628480851b071039501d90b60b2450b2804034103400400c92080d0f900c1042c070404100e60071464032040c40244020740c02c8184000c003250f00c0b400241c0d40805025415001c100d8064a070848402e2030f813a18000c1002e5110020707000c3d00d41c50181c2da455030043d14440450b0109210b02c011b00080c9004510051501e091684e40004445144107801c004c103241d10b0040080c4456030180032a0764600c06104200b811041c49001c59000c402e0007200d41c0074481c801c903074520344c1c2e41100b0385011500c0600014032980e00e42d02980c0e640d04140108a00040c106030904201490120300907010b590b030b070348401d0700307044000e020030920b140b80403142c5160359664201c010742e42c0d035410741015a0241410b01d4411f01c5071000c08140544071180c12a42c8448a034030000c10251145d03000700d04080c0d41104000550340407941045404017110b0050565960034031f04410144034002c16a24010703442201c203240c54031540311a058813045041e51000e07290b00704100041613804c0c0354220703a82c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 405836645 1250 405835395 405835399
    0x11060304020102032106010908060702070504020d06170106031e12031d0a031205010f082523040507111009050708100905280305070f170901020c0907050702010806 72
    0x4108210303041c00c0d02c54075507410440f1780c1d691149414007096503000300102c1c0103082c183e00500300c035151006010750baa90842c810540039076070000d550400c0540316882403024140d0b24840508985c11401c281d40a00050b0000361118004404088002c202010034007a1295206120f40d902c1071880c02c051f40101260480718070074805c00c0d00700030002e82d4241328082040b4400d480707102c1a0081401240f08650058200402555242d1400d000785600040d00940801c130011115020105001c041c03600c030354440d0300c078100c41c0c0c2840001c40b1b6229204070380711000c2d0000766410032880d0344c3d071131048404116498540d01580c010221090342103146810040c01d2a024000b21600507640e1b000080c40e041c00b895042251558424054003041024000481c01e00c518852068240408104541062113554402024000e00244140401203945011450240c000d060080b0449829109500580c4010031f89401401610f4a103011480d00300c003500e0140b1610795a40f81440140c0e03005550100c40030702119 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 405837895 1250 405836645 405836647
    0x70305070b1606090303050f16020703081c05090604151e09141e010f051e07090510120c02010c0806060901030e030c210405060a0f0e100503090c0d1106030402010203 73
    0x42c0800c280d0b001d0f80320f9261080c1d40020f0f0b5468030708040e1401500281845200e908031803000e1011940c005000e400792508601959aa0107030003042d0000d0300002ca0040381110301f1304040102c405400700d0304511440c024100c1a10082c101c00400d001c8a03c004892051a120010f20301c2032a040c42e4442e0005503c10812350b001d01c03258002e40c83c030341100d00910011514020074007100030b9801b07002e11001c0d01010001030203030382020300051000c0000c041d600000c0f00070175400075601d580b1a41c0c041008040180200010050005004002c014417120301803e450420450005007441423060340c2c4032951565490100f40ca4050400c00107602c403a0b02181015201c401d411054072041c0010040ca102c007100401d0715005c044117007403842180c0e005400380000284810490790700c0311011140e40010910b4040302d112034032001a00c4445041c2c14150704200c04250310ba81c02a0000000e500070356007a0200d402d1200323500204000c072584c6100040c2159044a003054160500401443d0810f205005a03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 405839145 1250 405837895 405837937
    0x11100f14010e071d030d03021c05010f091d100f0902091009141b090d1a011e0b1206010203070b10090c05180d0816031e02070305070b 59
    0x30394052042070b0404420450804148141140c100c3c6003007203d40c180148801032550480002515186445208818103400141c82c865003002c042c801e601e5080920020001035071501090010504030b8054030f2441840c0440c0410b144640c603803100d8060001400600f0212250607400c40500300d034100300c403003154030342480d02c006a030380c2c1501c907101d181d0054900303c0c254508146c59042c0c0e0021034580303134100c90400900990359000100007004010b82000a60f075002c940d03000c42c01d89045450701070300003040401004000042d000c00e00d4100c4003c580000d14900c1c080d10808021b00346403048135aa42d1080042140c071203000d4000b05d5101c80140107130303801c0429680f0303200c60041c1b01310340ca05201c4016103000c6c0810326061007410300508085c03800508004802542c241d03004a60303d8142d200e444100c00030406c01402d581102c0d00e07680b5041c0c002ca4a2081c2e40741c0a015040f0302003080c64490300075014034120741c0c4000340d0b00003180d41220040a00924081400400780e1040c45111a4614040d1030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 405840395 1250 405839145 405839171
    0x60f45011b0509040b010903020306070c230309090603010e07030204091b0602030717030f0112060605120102040906081c050a090b0a0e0937090b04051c11100f 70
    0x10540c4003081c5840382d6076500c10a8007084200d075200b0303009605010310785909001589002410581c0001a81803182c050030450604145400100c59100c14883c020360a0100038403000c400742c1b0a100044d580014582c8520040509031800c603015111250b2011b107081001d85800c0e00f14016450145080c00c42940a04000c80510b2025030084000740e40000b0314a001c12030030040750301103086441e02d410f0841c14481c2c0c0300e410036401882030342881109544501c090001d41d034000001000d00034081d10b5054140c1c0c000c0e6010790083c0c0700303548071145401c00c0016001e60108505000104007c0c064814000b0664140c586820206c40002080700041303000c2540f00848000b0114070700c00361a00059005900208440315000910416180032521000310b4088240521424401c0b80803560a40382000307003100400400410402810701940042404144a03020900c443c2c50210f106c20950007185030642515060198244002142d10440750741020b4011603210310348914240b18040344094410714 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 405841645 1250 405840395 405840431
    0x30204050702060103030810060e1002010e0d11070509040213051003121701120f030809011401170708030a0203160201090302040906051005040c080a021803060f4501 73
    0xd50720000d80c0c0b008006006064008540d01e0388010303401d41d00801c541c11f00000030210459004101d0041c2c03600d8040d5000d4030300039000030003900c80080c2200c80c26800c404000b061310200210f40c601c01d00030385001003154104a0440b91003250050880c1d4040c480041c02d4030010900242201c400c48a5001e003c0300143e4480e561460720f030f000b955030b000e030088042c0c142c0c08100e1042e480382d0384003039440c8070302400140c0c040202403406405041c250655581c08103524090002c0400b8445040a004004142003142d12454650720500d501165030998a03203400d56902c2c8182e04802c0d025a1040c0104100001500c8401d41303480d01c1031401c201902c0d50781c1d01140640f601c910007101d001d0f40301e40030400030104244100c80203040807a0240300039828680060042080504404090303500000c892040e00e0b01c030500a110410007404980d4075140c010038643d04071200303440b00303d054000031f2080e05418008091000740d0100c0c1c0758001c102c070403040303040e040c1c2003080300070403910365481305444010041942 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 405842895 1250 405841645 405841651
    0x9040b0a180605070e010c05100c0e0301020a030912020613060b010306270506010519140f04150806090f130312020409150504090b010b071b030f02011206030203121303020405 77
    0x30b004259414203190240c01c2140000340a4100207054022101256002510403501c0380b569034000f5000303441d02c40465440d15440252a015800080d641c1c108e264550301415105008103007024a40500300812600c4000070341b000400b5030305601003080410116881700030f04420504000841564a800a0310001c1c64460600204195840d101ea02c0030380c3e50143c694040402d02e03195244c0441009001c10b2558901c0c1081c00f00010406080030350102c95080316000842c00d0403240e1503a503500d0402c1c0311898291139600006c1c41d284040340c0d1a04007040034a00564080c944468181c1d03a01003514024100c005050b42003140c400c5103055134040600c01080942520580890260307c009488540004241e11043c0a01d25000114011a91010303407103055905554060341c0d207504600b01002c48900743c0c0e40304409541c15503c004100b05000204d10f8585100b80c03078501400d40031031008812901c4511000e13406030800e540d800e2a01303441d040100070641ca5440d000b05a1a241e40101c0d080350001c0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 405844145 1250 405842895 405842903
    0x1080a241104050f0103060e0703020c0f0303010e04030906020f1009020d1709040c111015030b070503070806030d1e0c06020f03090f0f07031104111303031d09040b0a18 74
    0x82d09100c2c90820020b0402018400c0c241030006900d4400f001c0118403004080c84205a030200d800761400f1414000f4080800103a01241c1d01d80d61918818941040b0030340d41103000c95038650740025164004101c000116480402412101408000c40006403c1e2108101d034803205485010002441c0350800440c0107112055190f215003012003400b0032101402c510700f0500c02401400c001c0700c0780c0081c0015444501510201d810a14501e40c8080e07030310160002400c401c000420003d40319032180c080c601c24481960b0303035501a103404040c541c032031307000006420005c0c0105504001c22041c00c44034071004a42c0c0d24158074050696120a0100e80090011440e2000000b040c840103000c1005800c100c080481c02420044100c0c00e0240d990310788a06c4000e22710076050020f5296682d45500c031024404902241c6685c600200440ca0b0300741c034540c00210082965065108014103400040c0740300741c8805800c611080d12075446080c58040014601c8400c0e0b9118190103e06a44030054194450300c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 405845395 1250 405844145 405844147
    0x30218102001090b150a030f0605090118030522120605040209060406050a0e0403030b10020f101b141b070611010504080909090a0210170a020301080a2411 68
    0x2000d040412950700900800c080d80c100010309000c25044030300150000d15001c0020a1000c1520203e1100c40c025480508034202094079070b0f040c00199041103110f40c1c0c008008004034522110f030b4025081c1c4d60702c00603002400c18010400c0454139030703001315034244070015606045ea80d85c120b00d401d880b41481e0125201929881404214100305521a401c0182141c0c03c0c000e050402c400f10703070700a105105003250309001d040402e060500a0b03020004003000504088001142240e000c1d40c2d07034110403c039003080e2107000000724112149104029500710100340d10048030280607012070300200c80040c15860018100041c05101c1964010040050a802c2c0a880060b1030300a02400d601c1070700a41c100b60340d05200c10807002604003822103107543c5003140c01c40b40c1501c2d80320400b450003103551b43c02500803182040003980c06070014801b00150070b0b41031084205660300c980800c182c1c0000c0c401c0c040141e106c05923a800003801200b02d20089100d003400101d849107994024425645031961560075100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 405846645 1250 405845395 405845417
    0x3040507080322090203070c0305070309051306051311160c08030a0f0801081908030a1b020303011e080d0f050705060f100503030307081506091f03060f0609030303021810 75
    0x903543c0314440081910b282c0031402e61a0607480036010742e0845500404101c40041c2c004101400784112502a00000d4508103101031040020030041005025052003000b100c0680102180302d8000c0d120030318200c0340c0e2613041a144030507040d0034040c00b80c02190008250030000c6200d90040018103008002c9a4540701d0303150603001c0141c00201e040e004140c0c142c110f447ca115031a00c001c2000a0310075880200f0070354075980c801c1407800500841070400e50031101d103d040d00880794000003450590344000d501480242c01441d07410119001d9204107043c03074009456440c015800745041c0000d048032030500f9803600580e0341eaa0741c24010121155480c03d1180d205010307402031075a804401401c004d82c010361550401d41c0c4c000e000c484006004204824000b441c4c1c040c1a00c46405480700110301610b140c0c4140d988506520079914681058800286008400201d40780b8143c0c60104450746603c2d02d00b0741a0458404401943c010207030081c0b0110350101201c4075480d0840d90181544003a40c1d40941d4075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 405847895 1250 405846645 405846697
    0x3021201090b04150b0307030b01150e12060610090503060f0403181205060a052502010e0102071a06090118020a090e07020f010507050a0e040f1410140a0b0a05030405070803 76
    0x400c685c40540c002d0388803580600014071424400360540c0c1c0d60300c03170001d0350311000381c4112000084e42007500c1d00200020380e826011940012018002c0078106c452100e01203c0010450317840b4454410540d041d8060303400300d03844c0042a10032941140c0030349090b54030320b005d09803212002070300303a88400101d040d001c6e0789006200061121310b8001c1901402445541085580300485801034032040a1080071548a240014001d5016540c1d922001000f0341d1521070a08160011001d10041d5402407102480050302c0341c50040c503034505903244044442140070118895200a400401103c4184204040302184100005040f14881d41042d4014102a0002c412a03402e58001030000010f01c00280211004180c010041c8503034140142da002130008002780760940604095842c14000c100c2003014004403200850440d0241c818041d8402c100c4410310b41800800e03c4c0601c1001507858040c000c00c0202446640159041030117032045401c0c894964500f58111760005a02c01d0080c103c1c41810700c140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 405849145 1250 405847895 405847901
    0x81005030d0e090a2c0f030a05180a0801060f06030b06040302060a14070204090b091c1d0303040b0c07210206030406020904020c0601140a0e041104050702160807061e0903021201090b0415 82
    0x60010100038600f00521100068a28011404401c40c1c8451800b0601c12607122f50990f00c008050b640c0003446940d540e240e20001504250180c400000d0400745c0482c0342d400d01104840451b0360103000d15140031002e060032100c100c90610001303180c0030704010080145e50740d802102d00990248525942c01c0c1420102645800c2c090702030901122a0000701600a68005044508a01c0c00c440c00c0c04007500d203c4006030440c0319a0f00040b00c005008103800c6a0220001030701829201d5100b0320413105641c1c0705405051040802000f07500c0354041002800180c0031b42c01030110074501030400b41c202000072014508005007600700c41c1825141120000c154a41240580300400c0000b1108000b03080c2500e613401089042184640219264408100d07a10300c01c100101d11101c8040414203101e8450040684900c0584160000600d041c150b41c03e0101d0141c80f001540b041c151600c036180d40c9140e0074000041c103065000c8031a0b56035036102c8408101036003610783c8510f22a0010310b00c020304550b105011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 405850395 1250 405849145 405849163
    0x14010b010905010806030a020112090b1e010501090803041a0403050a120306090b030c0405040206160305031b0405062b0606090305060c16060e1c081005030d0e090a2c 73
    0x400004d40c1c14041c0f251004076a10106940a1820310000e140c400241e202a0404400c01090140c5080800442c030b83c0c5440d03842c140a000304c190000503681c8600440b2007907141d0044e240603402c104000c10034220340342c1c89120207410b100015410503541e41c483c1401c1c0f03055070400b80c1e00903c11062200b495a4503100340e2015010043e010490340242c1c80200e030b5110b4803160143d001d40da4071004142556547c4080e1501c1412481044880d031280b841c000b41290410f1714030084100840b000e1040110015095505450029148905000181060b4902d4540300b13012260b140c0d100c1003204020070030601481e40540305d661208006985149040d5240c4400248a0100201c007031205440b030315038644480050340e0700071030049102881d920545013408001851040100c00441005002940150469120ba02c18990f0100c00d650356005158031100803680711400161500308100b9580350500d0320319000f0b40e4103200021003440c601c020030b07544d0701402010150181e1100ea0482071060401000003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 405851645 1250 405850395 405850397
    0x180e100801060803180d0209161b0f021306150201060518010b120a0f061511010501150f12060f0e100e041401020919080d0504050a06031814010b01090501 68
    0x840b41e0301e00240b2580301d01802d01070250f580385016091000399605444615055001800d504543c109803907034583c0e8210303000002012440900c481100c4414003c0010340c1e09070081c884c031072040c04c25801c0202c2412001c1800311202e507580e9002c5000c400c06000c0350040c100c0c81d00000f640d85d0410f800c01804e22219200c03c0c8003100e1920041c4401d11580b01a40c03001030742808401e28545403044214080e00c0e842071941d0500c4d180c0280001c0d4080e4109903822000d00307948548402c440c4084440e03099880034001c51244006900c4070402047c81580d41070010003282c640141540500081d1000343d40b0503510002c58100c2d60718081c401d0b8400b000d035168000c591004c0081d00c061412000f0500d036000184082d15040309480120724004080d01126002c081c01007000c9001003000500540002060040880502c10100e0400300c0342d00407422071301922002000482d203d46091811009031540e0100162000304c01c0d040c0000280c2c44421b500fa440f10000c001007145001703840010840c4101d0380c403040c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 405852895 1250 405851645 405851651
    0x607030f142a13090902120f010c140315121e030c06091c0c0206071b080c01021b10110a080a0f0905012001111b0601091416180e100801 60
    0x3020000580c3e562508a030040080440d20000600004841445aa00307044644c09070300d034111005801075001f0200741c8503540301e410ba46403194034078100e540405c82e0b203c4002480c113035464109182001c80314140d800c980003115032102441441d4980e407549420101d0880e0b00104003807a01c205d0911030303e41e1001006c4d00400945901d24588607d2200b0350910005012140350f50400355110101201d20389908902850306141c0807003007400100342d10b4400c62040f402079445070b800c5076102080c0d400720340e02242011602440c5000801070510022000d0b5824800398100c4804044070521000600901404605403600c560003400340c034000c0418031003410031152000c1880203a0704084400718034004003003600c038009805000d1b58010f00004100d481200300101d20100c402e81030000907119041b68105451640e680d9401190075142c41a80401020140c4030002d15070018201d1000d5424040740b4003048040084003c00c00d0500d4242c00c0204d0860440c020043c552001c0340f40b003401091010020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 405854145 1250 405852895 405852907
    0x1f09020f040e0604090c03140a060e03030a0b22020906040503010507110c0a0609121406011203120c0903080c0c0904080304020102010c140f130b0c0106030c06110607030f142a 77
    0x1b0018040c102d0000070028101080402e8400004004000e6250790103281000402032a1646940e40d0b00101c61214199080020400c6182410604904818036022400e001d03c0100600c2c64007940010b140507401178000c0c0000249580c090141c01e0082c01962500030b8550500d8403094101090240e403107008065251041020540c00100e034001c5954004040403560440d1504440d600f1100d00003038080e1050500101e021140a41c9001d01d0718881d8481e030340c0c41c5004442c008241c40c050080d403800715000000400110b0300210042c41104c0d032200513145d42d003020b0400140142c00646003540d898402004000455809124445060381182044841c40da42d172003021045102c1c80810680460000c03441d0108800341184c84c0c4e0184c42d454102c140c441c800e5a4213207000700540e00c01510003401c070110001e0140c1c014800c50000b0340356800580b4481d03071810700c16005000c81c501d4844105968031000442d0f40b4440d40030310f00410141c100200409004143c182d804603801c04841c050000030424 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 405855395 1250 405854145 405854153
    0x7050715020403051c0302070b09060a0c090f140315040609020909060402030a06020a09030b04060f060611030d020a050f120703060b12060d02220203010f1d1f09020f040e060409 78
    0x1107069669103a17446250b8a1400c4029024010004010120386001e00c0700d848030100da03552090414120420501000f408110341c005003500c9070b45124412400d091142000000b203654441a0280440b2400f41020040345500301046400b580c00f5030741c4405200c1185031186030160060440d0000300283c0c10a0b400003038564041c07a0b00205001d0307001800701307640303801807084000942d00001d0100c8079140c20704154001d00700344c1d5510f2026601c1c1081c00b00e881401a454041c009188000440c103200c91503007803a000350b1280300104240f0030288030403100c105c8400002c00300c0a201885840b010f041403400542921015002418108000d0240c84040d03a151808207170321140844508030800f4090010501105013003911848200000c1c1003020046030b80c0d001103040342c00c0340304000c41c00b9560b403569180304038803400542107071000c13003000c5442502e01303828060000002c00300d404089582c1d040345400f00e038070075180900178280100341000080c1c200300106601001c01d450074089026960340d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 405856645 1250 405855395 405855403
    0x3051f140409110a030605040b090a120809030912010e0708030f0706090f060504031707020a08030118150801090203010609020c06040210140a0c0b090d02030d0915050705071502040305 81
    0x40d809140d40c1e00d0800d050101905040c0302d001006400465000e4890501c00c000d46002c031400d4a0100191001c2955203000040142c0c40580202c5100c400e0791311020b08071040c42c4050440001d03484180300705803da42c0c400e800c0d200300c405650300001b0214000281c1e42e0500c02a540032900d00d070001d100003075100480c0e900311040e42d680540c000400303444070315003400c1461030200040c0105280200f003000b00742d0400010703600fa0380741610283e01075494007001c0340d403031100c000c0042c192081400100a00e807042ca4120323070b51444090011941103c1503405500c6000d55611410543e034444e1042e0055040c20700c00c03807010b8010043d0a624001102021940d0ba42c0d020300001c2c01760718088855030566100b420400400c0002c1a0901d0b925008020000e18500b200401958141003010214110301f000083c09002d0900e0b07a00070f1801c1844199050004004045090b5110401d445298886041910032144902015264541c4070304050804009100c444140741d46081e10410080c13020400000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 405857895 1250 405856645 405856679
    0x5042301060509030102071a01031a0402060a0c240614040e03220f03060605010f0305100e1003020a090c2601140105120a05010504050703021e09060c0d03051f 70
    0x410000c2c3ea891107107010900a2003030150282421198110f00c640325808558554122030007039001c0000c16282103414460b24800b61002544010b003041451090707405030018804e5103004884418440f8541d000074040c90070801d80c00c0102690340d038018021350318441440451060244c6080040100d080300c0107559114030321003800a04202d04058009402c4c0810801c06020305840c01c16025999180074400b80071a4001e02d40032410034100c8140c0c044c840e21500c1d120720070791014000781500d0000c01803000d10b00076160048003141e0400100141c1c59030461070004065880001030344454030f01004082e40c0e080c11109042c0c00d80e60030000c0d4550100000c1a0640e844140010f10040ca2600142c03058410752a1481d8a0620303102041000b2081d9403209040b02c0d410307035003800950740307040d0200c0492003070024a0060f203c0c80003c00400c001004041c10010401270052880d0501c5011080d2501003c0c41c220030010351111700300a0031040b0440070413114101340f43c100d8081070070402c111884c01019 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 405859145 1250 405857895 405857897
    0x1020a0329180c0408032106010503060105180a09090c090e0609060f25020102310b03060411072105040308030c1c180606080708031603020703020a0f0504230106 71
    0xc2d0104120081d0b400480d802061104100c9650303c42d1802c00800102e40404003d1814041000294865005004603442038070140d452034584402605026001d0081c10616500104401c00200d175012041c460052011700444445200b14a48981130055840e403580041d055000b00c0c040c000407a2000500d1900401140d032218040e07501c1c400c2c080071490340620b07800e1030b00c640d04e6a0300070350a80650040c00340035103d8034a11b40c0c1c01d4500303d410303403a2246400b40c3c5030000c0d4418410002091100061500302000501c040b5100c07160a0b4201400c5e08184401e440414040503110219210204401d100c0903c50600c00e040a01e50f8946007550f0000401d86000108009001000d010346043e0318015a02824000c0160b101ea0804c0300307129007041c074001c03525585050004a01c01000080b504215803882000b9440c24101d4500350080e0400001d080b03066208850380440180d896000300b5029060b012002c0204034079100420003600e80c12601642c640d151103004000300d50031030f80b06038103627411 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 405860395 1250 405859145 405859189
    0xc1706100302152104030f030506030c0a061d12010b180403080103020d2a0801060b040e01061b05070905040605160c020928020a11030c0307032001020a0329 69
    0x40303600e9090b006240c1c44e14103001c164120402040503000030040990450f43c1d0360400860b5100010301d60350780070802c113a50780f2040f4031504100c80d41c40b44400480d54203101c03060700e0010500c040070803c01c041c030700b00b05003159468580400442c200490242540c00e0740c4481c00c500f178101510041c1040350107000285c012000800e000d41880104108084050b030768076486078100700340d400bc1c442a44030354000c2c00501d500b00000001d1a1030350400362401c1d6503002803c10790304d03444c140080d6038042c0fa0490410003513002d0340d44a40444c0c0140a0b0000601c00840082894505841d00d0402c88100a11030042045203c8003005601d41c009090203c0e5070341039543e0542501c0352003421152100c0e40381191004071000020744203842468014050b114000e850706c109042928001c04d48a005a40d400724441e8810702604012a204162004241d913168070807000c0640010002403d80c2d00180001001c42e8580420444400c0c143e89900700b80c981080c1d00601c002035002c000342000340c074400c2198803507039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 405861645 1250 405860395 405860407
    0x3050304080f04050303030a151409010b0d15080a1101031a010e04020c010c031b030e150606090a140f0a080d0c0218010815070807050301210c170610030215 69
    0x10042c084402400c001002c503512803902890040140c030680c00614141c80e194100040c00313040c0d0035206420014000c000d292181c1c00c6c005105c040d0b0704407010014500303484a0340c441c51004013030302d4903020304040300103000c0100103400e0030001100c0d10707030f0740038105031800703401d011170b22124079001c2040c4500740381018503070071000c000901902078844c10f02107552a19922542031601603002e0000c07040200440c4445d90901101501142c500c1420113406401242110b800c1c3c402d5541ca0a50106004080703900301260440803900003041500580400800c440446860b450140003102101c0c408403043c0015609003280a0f0311880015800000d1002155280045648520b484110982e803020b00034000e603980c070a60380e07480d2400702500640c0d4000101154403544244055881100152111071450340b0b40700103550034191110084d01204590105000052a5050180c0085c40c605400002d100607001040e410004081c00811900240c03610400058981685e0b003900c440d00098515150704c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 405862895 1250 405861645 405861667
    0x30c0a18060905091b09090c010c150911031c0203090f0f04110901080f15101206140102070504050402030601091508030415030608010b0a15031107080c0d09030305030408 75
    0x84120b0708180301c65418002009180c0d00001081040e01c40d88486020840380b125050100c071140a0350981c8461b0010814038100c1d50240300c0008016101c0c4100c05030070920590414200e980c000c600300c1750381d14402c88040552400b003028064a0111210b5840403102c0700f14041c1d034030300c40c6119890107461072403c10b0641d80e5600700705c40000400900144502d80004200404a50244100c58042101303040030803066880480c800d442020301000503c081c0e00c00b001001140108910340b0810488121403000d8101a68000c24000341070810010003ca0843e00000e1f0414090340c00041c003d42c502010400542d6000551504541c0920800101c20082420125400d101a0400360041c40700080000300e403a00311505800f01c244917681080600c0d11802f90034283c0700b003a0801a402001080c3c1400581d07416a504c4c100081c407800c00051040311800940305036000200240c821712404201d5a52042c0113103e001241c9003680b80001d01c0c02d00390f9038068403030300000e80081c242503000f240e409151 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 405864145 1250 405862895 405862901
    0x8010503160e06030f10021908010f0605280e09010503030c0c120a0206040f030c09050402061b0c0a080c0907021c0c0201090306050a0209040b03010e15060f0612090606030c0a18 78
    0xd07404005450740b42d0021401d04020794402d00031103141030120803142303040d28801d8001c4c5050b00c0100c10101c0100c1d181280407180364004410000440351501c001d500c450804210890100c00a0b8482001c034020800402c0342040d4142c1c00075000b80c2003000780da810880c008c1380030300c16500119014000e140700d001034986007402c210780003504894002800b00344403544404c0003080303910610743d0b401800d031248a190300b5141c0903240203401c04001d1020030a14007541000c03941c44521001119961610700c8009525001150b0200721560000d01e11039845003004000d5030351117144d41c00180302515185038481c8440000c042d42c03004000f00c0c10658401c5a00c03500d405801135411400500a50911000e444000d51000e95420301c2540340402c005423505041c0502040c1010f0400079003c40d1a0080d00c540d98144010070442c0e0140041850040f0b03070783d81001510310301c44d500d94100d07030700c0c501510701c5803500310040c04551080c1d0001c450f080c41995115070160954060400711007800c0ca60399198005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 405865395 1250 405864145 405864163
    0x40f0c090b2419090f050f1333030b0a090c1503020705010609050115020705030303011418070507050d030b0603041709040e030901180f03080306030a05031908010503160e0603 77
    0x840d101c5144100d10319504c140510281c2d40d0b0210000c062540e22000c001403146d411090700d800c8401c1e20b00c2c8191010070340e8400da0340800484190500721002000c0549078480c1250030103094412404144240091030009951200c0c1c00c40c02003014040c01c1c0c58507204880745101e210210301241c038900315501c1c4282c069039141a408402070000c0c07511a084c640c00f0344024003540c10840420306195900030720029091048940140255103141d081000d0b200d1300841540019401815840780d44d4201d40200101a10400d01a56401d0310340009160560411400341d4a0000b01410100718083c250b58200c200c2e41c1040d44410b146c100904010950161801600c4030560312a142888882c020300c0e0100041443c003800340e840c81104a050014441304201c1c41c040c0030281c00a6400905c00990050011600700c0b00050403169124866940c81d45150702c42101c20b00c42c014002c000745060781c1c01800080c0981022006014100383c1c0520009103800c4501c04e280320402c07420b0101c2d075552002d10507116 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 405866645 1250 405865395 405865417
    0x140f03091606031d01020a090902030a0e0a11010e1e0f01030906050f0604060f06120b06040527070503060d03080a0b060a0c0b0903070503071217040f0c090b24 70
    0x60390750710340024001303000310388501140f0050328510089100040c400c42d20110000c1c0c80341c0c94280d040550301c00003034100402c50b13030239950303078986843310b040c01003100d40c0196125814504508040e0341c00103042240010340540106010110316180b00c0604000340c030501015590b040000030100700407000750808080140c00300303140009000c805601500b0706485600d050b00c0c24052070f90303200000032a09519209030000030b051403082103103608071500a0002c0610003002c00c0e060548400004a0b00010a004a501c4108017080b03a10031004010300c0300e80c004000d0a0607411880c00c680030070307040c1d200c07140c0080070003d0440014010003070b60344c001c0702c92001c003070300060300e42c0705d03615020300010150f10050f1042541240001e41814001084401c402d600801440c203100160703641946e094000030761407041c055800903152103080d8201e003682c4038602030b0302000090507581c2400855035180341c00a092803824203031280c07101c1d2200003001c0b56400c03e43c1c416505a103550480403000c0c0c02615400741d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 405867895 1250 405866645 405866683
    0x30c04030b07120b010516020114040b1303030e04060506090609040f0f02070b0f090d0503070e090c180405070936050601081e010b0c030702030d020303070e01140f0309 74
    0x710300342c1d520070041001031a824030100000590040159800c0c012031700004040b28042110b9001544111140c000d42500c0c6400d05d410a070300c5401d07030b4116400c088404d40e0703107a4048008105040e48200010003200d800e440c10041c260400c2c01046440c80351681c081d01992001a0361030b0030743c0300e56020301c00d030001012081004000c0c00446001943c04070f030068500e0f81c0c0c0040482d0811504505160103030080700001c05030203207401015100c64000600e0002448030340300150f9040e881341d40506201c0d444d514a01c2d9540d00e0404403440d00c10039850310048c061841c1c8030801c00701f59080040d1034166214120885803004807000007030001c0c0180000201442504c008400446405410060150500340c0310084142e0b200f400343c0c240e0b001860841d8402c5c0c3c03840e400411003440f140e40100642d807100800d0724507040494010a00e0600411400c074010382c800003c00c0021a4001e1002400303178401d28140700706280d50f03141805240a2403900442904001002c0340c0c403100100400070301140c00000c48 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 405869145 1250 405867895 405867901
    0xa1112010902040501091e060810090e03090406060e031018060906090605010501050a0503040206090414070908070504060f03140106030209090c0a05041811124c02030c04030b 77
    0xb81d0050301c030b038038045502824081003840c401c1113072000304ca4004100c2c4806520308101112105070240c20204014011003021a02c21224052240d00601490055603541035510034081110300c01d82c000c104010079403504044c5540c000c2041036104400410108a1024800c5640120590004009d2070f43c3d01c1c15a0400400c10320303410100440d8019101007140e60f907614015195449503041c0280090310401c0044d0040c034049000d8820500064000103a00c900c0450080300d1f948190382000101d030008000b0000450200040d0024142c20f46007413152603c1e243d450001401d09000040c2859203171002804030a0007540144000c0d90020401117503410001d8001d0348800062408501402c0c0d9140d020031030341013602451350b1007000d00802500581c5e09454280d05420260b180952207007032100c2610000b40200000a4228800174990390814010001e40c035000382d540005480b8104454203c40c4500320f01c2041d540180d407061000740e525030b036054442501c0d200e40d4100910320f034051018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 405870395 1250 405869145 405869159
    0xe0a23030f0f100c0c02010203042706030b060f011103040e0c0f0f0418051e06040e010c090816030c150c0c030305220506090d060f050403020a03080c0708030a111201 73
    0xb00140b418000d10041100e070f1300d6204211031034460004045d0261f80200420454184080075166501504403070320b042142c2c118146406585840d40b040e50201e15400030311041d40f828420758040365409080150301c804501d1400b5849016610510407151445000280c1801102c421204103540c100300c155035a1004008103405504140200b00740c01e8000b80c3d032080c05081c07a109850040c0020130140c0010711316900c1070855080d000300116001500c545450120310024012000c04c40c4a5880f0f5801c05070078035040318a0401d034001403018500d1045410804100d440a00c081a039140310101009583d10032402d44170103001100080202060380000402d141e80003000d80520f403a4500500702668440001d00b007684d0a500038180d000b801004942c0b00b910f031510a44075014400d81001c140c0800c000f9002c1c080710b100305e034154050380105100e40304140e4441200c55210303811540c6242007040c44e0b2101203260100030480d0045c6940c2e0703001c000e00c0c2511203054030032002000c1c02ca070340e1039a12629 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 405871645 1250 405870395 405870403
    0x50906060325030209090f0d03060503031603020a0c06080109110f0702010e010c0b0f010f060e0a0504020d0b120d0f02030c0703020906010509101106060d030c0b0c040320010e0a23030f0f 82
    0x187c51007880c000c40c12045001882030103100100e4400900a6003090440c0d04145840c801001c81202940b00d40039200001640785500302000b032015495038200341d031404000310203469040040751025402000705001c1c03020142c0c20364040750f4081c0303001c00c680c4d159100160b515030080d0401400d00c80a12007040a018501c00205e8140c5001100c013200d00c0760b03142c000341c1d6000c0c0001e40003580304e15504018001814954003030000301c00030700004101d0308040300100392176182010310000250080b0384040402504036a0500700142d40d40700461030310309031585194850180780002441682454003140c03a0740c0c071540a0742c40c0240c0040281214891180010b8800c82e60317000364400ea4010003000542d42c1c54000c2c1c008650507016102d03503801c0c18291390741a0144030000c14941c44800c0a00c00400401e0282d11102901c2c6c9503a1040307580060b51500251058030704054451260400d01018000d00a03011103520890040d0000d020b007032300180001904126561075070020502c1079003404018144002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 405872895 1250 405871645 405871663
    0x307030306090c0509090c1603020c04060515030a0c03060308031302010905030303070210150305120406030f1b030b010210020a0207030b06060301240519050d05090606032503020909 80
    0x51020070050369500d42000c151002c1100910114009204040d12414903075036141d40100e1040080d40380420340300340c0001e5461710540c2500160f1040b00c5404071030600d842414040d103000c884102c0603400c6072401e250b50344401495001c08980314100e00c48803038080d80141c1c000c1c6602401154591802044094020400c0c00050303002401c0400001094200401180c0c01207695078058060b1100e500b8502010b02404d036100302205804000000108409104454845443c4100c0135a51380c60450003d0070340301c1000750100200d180541d610242014164201c0c2c00c48008e0074007142c1c0c40071000041c1c4c200111440401c0340d0500000380c00c40c0c4030781e01003443c500b81c0303106030400242ca0300c07000c00f8402036000901035800c2c142c010103601d100e01b07640b81c804070400c441189003072850000f10000c02c415401c910f18666004c5100403507040c941c4402401401e51180d2010010801442c065000981d1883d00080c500f00e00240b207a21890009d0f210340c2c41e0340145401034000b140e6400c00003101d07540c6407040c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 405874145 1250 405872895 405872897
    0x90f030b042f041a0d032d0e040b031603061b0203090604090506030f15010f08010e06190b1905180403020a02060d1b080106110a0b0103110d0503030405030703 70
    0x103185901403110320b81c0e116181a00141401c442d00307442200030312000300141d0750480002181224440c03010790358450b807981c14a1182d07440c142d11a1848007400c000080c0c1c60107920315100c079032001d0388886900103100ca8040d0000c07503000c98078051000c0446d0a2034031501c070700b0b00c48a9080c070000c418841a504041da1001d9100c0c0c104844c8100418101c0c5c681c0204c1c1d10040d4040030810041040c400d131a0030042d00080014146c6501c042c107401800e00c1e244140d0403500c040c03000d06004000c100890f10000c0014480203000340206200e108006841e142e000f0000300c2c4610995404c00084850b40e840540f203140050401c0d6503c0000001e0004280c0907441018072904c0c0000e40309040035140d600c40780c091507041c2c00a02d10314501d503081001c2a0401c842c48502130341d03101e8080050342c42c2d80b646100303800075540f90401c480d41030681c010216004188641d2b03155201500d0040040c1c0110151030459400460400020018100007840390106640c0584a07120103c00d20082c000080010600c1d1486 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 405875395 1250 405874145 405874163
    0x3020703020f0315011202030102040e09010e0106060e060a111e0105090120160201020a0606150206060102070b040b031504020415090e010e01030212210a120513030f090f030b04 78
    0x105040560320401100507001d0a0103444c01006828002c07072020904034801000513060030703102c040c0740814a40132903011080d0780d129210202405400e218600240240d4070b0b010310a50b10a10109150f40b00d90f0200f94100501d4001d13090300c01d101071180c4001464441e00041b0084041d003c603a001c0d000994242d106e0394a00b00b98a08070f8840d8258080c00d100b40301100d9070070a211110401fa064903450000d9055000d41c20108000410f107114803c00391840000603c000018140002e15000c0001d001c60b056600c544018865880d003001550111000f503810165640d031226108d482c0c000c81285d0094000380049004605803600d50740f002140141a914a0f540a550341c0a009250400707205200726042c0307807c0140090b0511145290080c42c1180031148425060460a4014086420740000c2442c0c046000200140e2283d6504041d400745441482642403490814140c06154400101403110b804040b0076802d02440c0400d005015590714102e1030f82d81c0b42880070888904030750445600c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 405876645 1250 405875395 405875419
    0x1e020c0310021e0a09060c061512110d02011b0c030204020c0c150403030509100c0c140f0607020906060309150901020403141c03021308070902070303051006020a0f03030204120302070302 82
    0x1024101341c444a02e0150307a00104249480f1081c1c07280000107205440381904c42c002202c9040c01d16020a0090002001783c050011b00b030b081c140341003171110744180c1c8aa40c1c00c022210140c1c0c1d000e480b24400e81100303c8403503511811480c0c03450090300982e00084d0040e0000c2601030301c29501250301d030024001501c1c9920041076540c0843c100703224500008020400078000903a403070800c2d4880084464003030800300b0002000c1d48039450100d0b6158041680d10380b100314000f03400d0038207031610440103409513040c605000d11640017030b003010801450796003e5000840050030400040040605e0b034404031076602d000d41000030450b0302039403081c0010f5841d008001c0c040381d1070302c02c0010074030352103034070110101043d800d5100120041e520039002d10302041d618030804550f619041c4454001421041d600580d82c5440d441e014081e5040100b0003402c110008804110607900891a03109071903002000720710882c05440c05034000e020301d0304003e4841c1c803e8540042010380001e6141d056a00850705194044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 405877895 1250 405876645 405876697
    0x903010e060a111c0218040216020a17060a0203060d0b16080f0405030a0309020f04140118020702010503010603020306010302160506190c02030f071401050f0109150302011e020c031002 81
    0x12055107048440b0001c00118400701d0084c0c0d030b003d011410004800c40100c4184407000a09a0f0003484032460b08030b04a5442c54118584501000d0040c44c0503111035001e491002c6c080390326020000d240400d07482d0000002009552a00200c7c00b5595001e410041942045000c2e4030b032a105481803400440e000002040d8029140f0100034032882c1d101004502d00b1000031002c84c042c00d5801e404a800000e415846c425030741e12401402091016030303e82076029858800d1101402c4d0180080b4120313240304009100150b42c0c40000c076030546249080150744c0f40c6034800101d00a00c0f032594111071200b0b8000c210810020b02240d8507000d000540701010b00d400d8040d203c2c20841380d60b20349002c050780c810000b042749242080049c00400c3e024540032500244944d030302d075081d90400c5034a80c0a5020071b40051000d02850301c60b02d40c0c60031814640c001c48908580c000f0b010092200748003103050041098031440544200074583d410700b0003030162040c0303100c2c0480c44000380d0420101409010389911011503a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 405879145 1250 405877895 405877897
    0x109050106030908180d12020d26061c0804090f15051c0501020705030c060613020a020604030e0d0512030702010606180501030504080c0a050703020405010b07020f12030903010e060a11 81
    0x45400c0342800f454600720f4944408a40000f400032a04400001c540a0211f040e2030028412080c00790050910741904840003084043c1c3c040300e500f12070020803401c40300000010302c0d565002c6d06c182d0354810b203207800c00300c1103131990705080700208081c90025000c00c80c01d00e00d400028400340340c034109101d09145000c001110600600585801610b507070411044062040c40c000e01030750084000614041d1241c0326603086500070329400e4041e0740500d09004d02410000c401c0e901059140e0011402e18851503c000d440f41d03009800907081004203502c000c2e641e81c0b90581d14104030707401011242e104000c400d14024a1b0002c0f500302015510307124001a0440c02078124011207900e0081a050f46410980151300508025109a41c040742c2408030580341039041203288031f41405540140b95491540c810041690016080520f444200f40b081b90f0040c1c035180b00e4800d0059007151200300031400e04501314954014414029032540c00c2080d020a0410041500b13401964128001d0190805110034401c003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 405880395 1250 405879145 405879161
    0x1c0207150e0d1202090901140a06050708040e04140318090105030a020d080a0507020d0309030c06110316140706080105040b01030c0507080304020d02120d080f070516050114090303010905010603 85
    0x8036080040d86402c41c0384141040000e03600b03981c00050400b004100420f02c0343e0b800341c0241d040e540c0003142d617094600e42105031600912941c6045460814583d894515078020383c8140c1c4e101425060100b0204004d581051200f040c0e550102ca4941c0310004c0e854201c1540041480e000b0754910f000442d46050202c0c10300320190700944000321034205a5911181913100340014001c0003803d2083c0340040e03550544a05400d4003a41ea00703098a801c5003441001c40e01d0540c004000c0c05000301f8024030907013000c42502d00105840454075004040e0342082208a40203007881a01401a40000301e8525000182613042c1c0380141c0c0c041040a031207800540868400d84030804c04aa000d1107441d00156a400c01158000d2005d4240400120f440c2e02145851703802c0c070841c03145500100c1c007024856511000e8150b0103102484600b0590420180c00342c4180308000ca00261681001e40131000e2200c250070003e010400409070001c1c0b4900b080c0e00646a800070700560403001d003010000240e003441381c010204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 405881645 1250 405880395 405880421
    0xd05150103060b041d06061201180f0506100c050f030409020a0201061e0e1003020405070c140607211122060903030e27040506181c05030702031c020715 67
    0x1820316841703000a0094600203203120ba200808000745480f2550b03c16205000f044918214900c40709100c101c40195181c6c18101302c0c48502d4030003003180e544c2c1c681ca003003040d0707a0381424914400d00b001d0622504008040082d50038500c0700013400100079111340e00401941c00654020003405072210340c96441e155180e00710401c14030002d842800a06901e9a0454200d42074030440d46080e0b580e0b501090980780c003250000302140c0c0c030444500900a008022609254105c4041c00451400d1440500359061210f0f1841d0404030030107540b080c80c9000e9102d00020440b80380640d8454081602100035115030440003000c203d00c0520004426008030101804d41c0c0d45600e61102c103008031014070007040a108011070010168075030119101d4170311000b171400f1380e0082002c3c080e04e1504226244200c40d0158407844039501401c1e03a0403c8001d00490340303c0c0c0030440d1030b00b166241c640f0803040789035004032411900100340c40000c4102c03a4a0550082c0115441421400340420070f012802c0d0480b6011f001901c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 405882895 1250 405881645 405881669
    0x6010324021315020703120f1d0102070608060d02090f01050114030f010506070c09020706090b07210b190608040b071d0d020103021309150b0304031b05030d05150103060b04 76
    0x404510307110103984400c110580304480c5c8041c0e40352035554a042d00c0c0c01c0030801043c00b481c0a80640c643c000c0c1990b90703000e85828524070860006000035030342d40e040e204010070448ac6d403000c2482d55581e0300c5014103082c0c004041c1901820f008601000100c2d080c404d4501088103065500000148481a2032080e2217100510500c1da103460700b44805075011610450360384240d10b5010410f0101440a800c000740a000002981103103460010b040c440060948000c0c410100218250001e5400307000d2419000c040003c02c81c2d904c1e820204401c0150b54504083c20102c0810108085070b1007001c161003140110010112625001c00940718000804500c4001d4044d00d90b007050b140c14408a030480d0184103150051134410094541500500240c0007103c40545880443c520000802070316030240800d401c1107491408c10380d6001e05600c503900c4e9000a886800c2000d401800001e000b80d03100030b42d400d001484680341080e80d2a00321800240000d0209241c10408207501e074502c07080e5801e4644100303a50f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 405884145 1250 405882895 405882899
    0x50910030507140303120f04060c03060b07030302160203150f0106030b09060108100801021606050912030402091003020d030f1806051b0106050d0c0305060c07020d0204020904020c060103240213 85
    0x154030091001140f09401d44400c005e02c042e10034030004240d1058046100647d141c4c1018508201901d1001029004050510000b0302c244807541c000c0301c0750f590741401c0c0147d070f8045000150040303086a010295250041451030391121883d07030304841c402d5106000f0b0000d580e8031600c0c10343c21501c40c94480358001001400140440d40100410345c2c000c107021010420555072220b007c0d007680c1c008402000a81074503148501040040d004d02a000601880945410514200c1e0f0724014000100301902c03034102034020508000c5904205006941c010304201d0003a00a4200603045e0490340ea0218006080800ca40e0440030003c1115401d8074000d0b41d48a1034a44021408104596460242e42c05556100800500f50f5118058114411300c11441003542515600342542065002009404000c80c2040800016601c600c910515164125801600d84140b4030125001b4010b9401c2001c09105080021050004001d0100d8a601103510035404071000c096401c030603400b5100c1c1c8400049142902 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 405885395 1250 405884145 405884159
    0xc022b0c05102c010504030e10200f1516030b191e08060f0a0b0406080f070e0610020c10050706050a090605132d150b0901140d1104020c0109050304050910030507 71
    0x812944000c40c540400581174020b61540130030b02c1d0f6080701c1800d41c2f10418041420170107020030081d0981c104c896052502d0031071140107010815000c0a000c05603a15940b410641d10f0702209101f069040720f006040b9030702d40e01170264420700c02810340214001c211002a040c139001030920b00c0b440b402d105100064031800700d0300b800342045440695000d502c4060210303402100300800c0001102d8040103003c2c00e845c0213810201120060101d0340942c1074001c0100c10242c00107207052a4090580b09484001c001c40703c121058000c0a4000300013904082c2880384035403c0340c012880ba00c0c058501081580c8410300c5032480480182d4000304518a00c9809108210304815044801115400302007555a990b175604000001d105680752051a51180140d0b014148a040e1074090440045649000034000c4d0020343e0420b1030b4000109821130100c4610030544864060300c0c488441c9000a0041c8407072440c01c1d60301da1304240600341c0154280000501803d140e280c8041c21660000c000d02030709401c00c1c0c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 405886645 1250 405885395 405885409
    0x31b0c0a0620070503070c0503070501140a030605060307170604020a0e0909030f0a020304030c0501020303010f0320220b090105091602030c0307060c022b0c05102c010504030e 77
    0x10040140b0202000c0d00c550100e940d00100720349071261028568a854a2900c1010305c0d4068120341c1c000da111003804c1c00583d80251200d0802081e003025580c94880a0740100c0240850340c10107504841d000c0144880d1b1600002d0103024013851000d00c1e642c669400e0144000c80c0210a4640000342007030519107030f64201038844a401c48500001c2d42e1400300d00c000d044030158881103040d801a40005030400a0114007102c1002602092001d9859035240c040481e10294003400041c000342941e1002c9072005003184101014030a02800301ca1720b000b81c0c00301114001c400c00085515680c00e0890a480619018003200d050b14001082b898040e21110b0301c0000300c000300f4180e04150300c01000400d103110303800c0014142d1548511008511405840c2c0000d00381501d042442114140741480b4800c074000c4082c24003104045480e080680380c1a6081443c60000212141c80300d03071b0300d07008074803207410003129070801c080700d000100b0141150784207103142c02c03140300711005130004020484058491034402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 405887895 1250 405886645 405886661
    0xb0a0b03031b190309031406040b060f120d0216050a0b0a0302070804030b0406050109060806090616020a0204050405010f0b010207081f0b0402030901051b09150706150605031b0c0a06 80
    0x40803503108003d100c0240303032818500b003010380c08560054810001c000f0b0340c0c0c42c100b0441401708050200350421f5604c8002c040c001030400c2d480b504050005103295240d01602c20204e40001040382c04a000110000e5200d806825550840c10020071001c580740c145001c0c00400c840e0400032b440e1070041c1d03481c0c084009411140b0201c4003038400b0000000480d8003a00c003540240e009840001e1030f94944050442266403580c0645400d41140007000401000807c02c07a030b00c0030000115280059020004038184050484001d510520700030506c0103020341540101ca0030304001c85c08020b10a078020042e6600d290600ca00c00c810341c4405134140b844c070040b0201400354039107580f022034800300d05400982a60021284918035030b560b441044139401c52810304105020040d440703907241c10310040118a00c08840e40400706a000d0004040c42007040d60750104c0b00c42c41c00e55000c110042d4480c1d03001000c83c1e1058442c801c480d0006041c40c40a0310b2424111850b44040c80c1c0245640300d5250354640140801c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 405889145 1250 405887895 405887947
    0x3040f03030b0904080c06310c1d0412050418180210081506030613021602032d06011508100306110a030f05060d02090a0b0a0b04030b0a0b0303 63
    0x1401040c55191100300303c4034052482a44025101c0755940c5806142120041404904030600419440b00300e00000c0074500189155492000705c19440c140f109461405030300010640e20015038815010303050407091406280309500d8600e031800b5685084555000b240900b445507003d11210380048031441d800302e90300b008012400c0308032038840d40009540c02c1e0000141d03400b02d403410040090900e10010080230110040315000c3c114200200440d10082c0d5102001d141280e00107080e004004007003810816541d401030484c2c2c2ca9049003070020b0803000701707000142c07038989800f607100005240105046050390100c01541000d403c170407a040395221000f6120242900c00c90b400030001c80c0203800307003458540e12041c1d0180d442c440d841c0018100e070205241c041400d49000f007400322590320201e8a6413407030f404846d010601d0f1150803c0b40000e100e000901c0b548408041c5000070400040e1010b8400c4070f001e8855800385544212415058480c01142181d05400c104500d42c1d11803101c41018004003c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 405890395 1250 405889145 405889151
    0xc070507080d080a0b01030504080904020901120908040e090f031e07150507120204080a030804032604061107020306011a0705030d021b15011202060f0d1b0e0603040f0303 75
    0x3a03031040e6400c00c0300310700c01c2e9000515a80208000c0c03c226000c0c60307200c0c1101f80790070003141c50705481d446140e0040c443e0b042c1c031664000030b100c50390340e109041c41d482c2c03001881010469543c080c5010307002507000307100d40c20380d081e8000e000451101001c03803060142e00412020750f203420440071021403503568031064403040810510a07000030a00302d481c0c80e2031806030b0540029035030030510340142c13408400400268005004001c2880100f1000c00c4c090f0720603a240c00d10132607649a42c82d0130748002d01103130603a118181d105010340703494000c1aa5040e003c2ea00810081244100f18401c040d0240f0070a00e01030b42540c04200100b140c18603196100007004103980c22903003410455920300341076030f100380c060501c3c254010500004402100c441080040c08d01401406407001e00d069103890b007201445048001b021301780d8a40150745a103411151486901081c003940d592521400e03c005040c1c03081e2948940000ba503640e82c185004a22608207030b80000c00030b5085a58030781d1030351000b0b01003480442c20035403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 405891645 1250 405890395 405890399
    0x1b070c091a040518122d03190e06060d05010209030a030206150904122a03021005150604181401170f160504020703090f0b090a08030903060c070507 65
    0x99038841d1a404000c24079042440910003070402081e5600504841503007480020040d80c2030340300042c1080e4079150081e00c652980001000003d4070014809208500d19021400e0102c0b00d880000035032280200005c4406c08071042007850b0121804011203c140e41e1281022610034900718101800a612820002d4a420007200110b806d0849003501140982d2241c4180000700807803001c0c030101200c2c182c0303002900307240c035485181070392041c041382d5414405a4984e44410720001484001d00da20014190041400a031500035a90076801d44444002c1e4617000100780070080d14038080466800c010413060609080001000f942c4110140b9543d101d5502c8034041c1003c02618003103402014880d0210103402d03242207100c0d00f030005524804803603420210780403619010a9a4030029a0419207005171945000c0c507090341d4540b0903410641c0c081001d00c80c005a1041c3c0c00000788844c000903a03255644a50740c21000b603403070040b910950743c07607086038002404000c020780241c4403650140b000c45d8005a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 405892895 1250 405891645 405891659
    0x90102161e1b14030a0c050d1104060303171006050405040b0402130303030b0907180e0a0e060c0c070e04020a0905061507060f0605010f0e06130807230303031b070c 72
    0x82400c503684107002d00c0310104000311140000d605805180980152440e02141c1e500d03400e4034180c6010321403050000c50020018026040140e80519401030020400130341c4906002c2d0a9118260603041e08000007000203418a000402d010204c608603110381d804c040c20001044098620040b03810b40055007401000100400003004030005e50080c0c4002072031900c041c00703200b210040100100140500f0200d24141800c0c21344180e012540b040c0105a61074441d202c1c0c0da0301401c1c444001c0c0a4600c20301c0280b255015000c0010640c415650b402c030748a850361801002010301040340c001e0350080c40d07003404101140e07a41d0030583d406a00101920b12081c803d41880200d50042d51041e640f181d030341c0114021100b03480c800d1074003401007400e00c40700415503420000c000304c0d41e5100c580e000d5000410b034140320b070001d940c0c084042c08090b802d0f101c40544940b01a070714492a1251060271801a01c00d15070581800300850340101e0700d040b600b030100d00701c0d203c44c529150b0000c03808484180350100c001a42d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 405894145 1250 405892895 405892913
    0x705011802041518090f050114070207060c0312050406060305100f05010b040b0a1d040606020f1507050712020304091103100608060f010e0a0806040c0e090102161e 72
    0x100d5520020146850314500601c01210404550780c01090f01c4500244410080404a0b156082842c000455030711a9407821040301c000c0141c005040b9030a107088010a00f80f86007076180b10310156802c44440765030b6008115a03801c0c0111380074002c140d200e042418406e807184c10207940720b801200003040c1d003541ea9640614180800d00c040c200070340d40348000303a030584450150310300402c0409240c40c100390030300ca864056445450020000d0020441d10703240300301084e0410380a000d0004001b00002e50ba90003002e900d849510345004540e0242c58004060b45800c0c0300e0315030080310160b030b59a0a00c1040c2e0349100181540306c0390113040d07110900000810440034003519000b44400d2802545a0070703c0f5004c03840e103000781c1e0020000d0041550070800540c82c5c44c610512201d409203852041c030302118020449a40c50ba404c0034440e4080e0504001c10311107034880c01c400721440354030015515031b00c142d095801c0340200520140d80380f00040795900422001c8032800d540541005503001186820380e40c42c460b03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 405895395 1250 405894145 405894161
    0x40e0312071d091f0815101a03060a050402040b0403111f111612030e0a03020102031606111209060f04030f03020d020c071701241509090203191109010c060c05070501 73
    0x30ba008454034103400c1c461814481d04429081d003101c5c00c160070000600c0d101e100c9072100d100522030110010f0620381d035040bc440d00400c40a8000c545c3d40361540343c9113034a50310901059900d400d0140100416007401c9890750040700c681c480004a403e040003048070030a04060080b80644211850700f00080340079404400208102140e0a0020426107000303000b00204d84411842070042040400c0981d8000c01160105603c1c40c01c0752445000c2c2d0315001c1e009092a0b40010305021001c140703440440140054280546048021a00640c0e00c0124640014a0450b401070000c0c1d05031607501c070a81d000e500074040d640903464001d8241181001428a8160654885030a420360150b40d400000c0e401c0c41246103000000603004015206228850711000750303403003092101001100711880c0184104418806428600020f543e24203140c00d403030400c6501c01000c05d85003072402040b810f04031407034022211181e0042c0c4480c2400d10a58452100520807400413205000f0100003010001e0000e100d1203603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 405896645 1250 405895395 405895409
    0x50d050f0106140f1f030209060f07260a050d09083901020901021c0215010b04050f01110c1216030b01090e0304030206040909050c040e0312071d091f 66
    0x7101c0d211040070003070804554501640103800a100341419003082c01c1c101780c0c403181c0c9400c0150b9221203c401007940d43c4502302d10318505860102d03145d0204043e9000020480c800108110405240b6425099080c0700314501600410020003003003c00c01e2242c0c01045a00b1300503288941000c0894520049407a42040108000d0450f100444100d50500c0294140d900f4880f00840c18010884000303035461441c1036403c4c2c211060106070f44600c0c0c0c420420140e43d1a4115090603080d40d5440c6001c0840d0400e025aa00c02c910100341041254400d107052507060f141c0341c0060003620703d60014481c01d8491480300100310300944a09550090040900303038002c5100d2045804507601d0104000c08540e880302556a05800400003000036a49032001d5400380c60f584100014164014076003d40740c8483c050f60700d60098280340c05044060000300184c106d44403180e10000481d075440358220b5100c9004020440b5448180c50010f0450909502480d801070b4031065603501001c45100b4038207400c0c100d5100380 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 405897895 1250 405896645 405896669
    0x110a0b040303051b0c0a12151e0b0103020712050304050a0507170f0706050a270b04051e01052205090f0711060f160e0d060501050102120f04050d050f0106 68
    0x10f004d001c00c901103c03844084400074250100b0b000380007602821042c45005001e6201040401c10b01c861803482d03401000c9512000c1100c0c861100d400e0f2044495901c01c0c02d080c81c41c0c6103820402e54064002c807000c140c2d000c3c11860020001340e03810303500d540000c3c000392905c1c803407070712054009901041440017400c20121142204e5401f450600e10305030205041c403816800900e010403029400206540181019042c500c1402c80500c0640c1d14070403140d4401800800c0a00e000a91303015400c000f8800d46078151005d01c49400840d1491501b810308404003170001d68100b0403400d00b20302c1035000d40e41c0b03070040314030b00d0480315501d40018064010684501c0c1000c11141c00b170200316904154015054810b26003e05207600c0d011590400e01c071401054a22361642c03014141d04400c0c4035680130009200c0c0104030741c100c02c000e420800000c120034003901c0d0152048103000e014810001090b6040d031b402c4034a0311854103042c01d044c00b405c400c0c01403045413103200340307181c0080060080c0194009001204501c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 405899145 1250 405897895 405897907
    0x10c0311160512010204031a06180f0618090703020111030f071416060507030e0427051b060f0a0e090906040b0601030902010e010c0203070807140405070504080a110a0b04030305 78
    0x40401d5500303c82039050ba104000400c001182c00b08444422440c1c10365045c1280c3d00d00d000f00d86213034960031a00790000c8a20301088900e00305110100c1c0100300035502809400120021180381c40e6041d1b44c0009198410a0200019846050660241038105003901e040004844188005812881d000c494020240c44180c0400138100103000041c440c5007842c10000b49400310240040c400d01b0406410481180c8140a03144c4560b04105001c4015100d20b0507880c07101c9410000c0500d000c1c2041356140100034014011944508444802400043c401844c0565005442c01c1c19440089040d0a02c804003c4004a559035183e9440c802c56130000a84a1403406107483c00141c0d10090602c0c1c141882c0214a8001d43d0740a6141a110002030070450000300107800080d103051415404400b0920502c14082440c1210800c52001c0351800c0d2424002a202c807502900d550146024071030b0380d540210540b401040d041224020001c5002e4011039503a6280c18038020107074040c0d04180c020500020b80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 405900395 1250 405899145 405899149
    0x303060b0a053007050d140103050a05010e07051c0615062307030c06020d090b0703140c3a020a0509030c0a150e03010b04020c070518070e010c03111605 67
    0x20714401100c215074054800100c62800343c1101c40c01920b44c6003040004070b100320800d10594001700c04580640782c8070410f5a900c1c542690b503136a0200c030894065007086016040468000b0323452056403030042c0068503060351030514195800a1b40c8055442944a2119000a820400400000c0e10044d43d0700c007021840c1240310007041c00000c0740300500c0002003000302c021a52090840410f580c0c0f01c2c5015949044955a900143c400340401401409000f0103004500d60540d008a0192580400c1548a942c0b04015400c9502804240c601600b91609018101e00000c4c5256143c5403086c00c000000b0488030001e510407600000716840c0030400019403c482844c04200c100180c8104854100a103820700361011410041c2c4103100d014041400900801c0c2d9500303420420001601400c110345400010203003a41d601c0603441118040e041c140b00c006000550081521f104011603100d100300703a0f081200441d0124040d40041e41000086442402c140c4010b0011100795034402144002d03403410201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 405901645 1250 405900395 405900427
    0x150106180605030f04140c0301050a1e020306030a12090825050303070c0501050313060212060405090a0f110f060c010b010e010c0b36010207120305011d040303060b0a05 74
    0xa000091080000c1ca444d446499a4817950210b081303090100803015007803401d07500c085070560550a042c03c1204d0102141c0c0043e8105201c0840c031250643c1140411307080b8407060710f2080e0160084808207010031060481c9070f10070806460889440d50fa60034006003002e001c10706910714040354040300f100464100b1051009010102c010318a04203c507654000d018440307210701810301c100440000d0803c101c03101d071b0b201aa03400100640d65846424001c013203901040b03a1141c0f080b4038090104088090000d0032701c1d0a5603010440401c0f00900d5226980c5207030b04011000c4c0e21801c2c003181c821075602c3d602c1c09402d40c00014000800c4d80b07141c000015103900c1c6000c01c281c0c1080324202016020861030502c060308507030300f500511010001604081c0100c80300500304601400c07244030a80c00c9050540c0244403981c02110794049012030950f0440584400784112190704580562003484402d00108042c0c001b842401c5c00076050343d031307001000c82c180c100c0c3c0d14001c0800c0002c0340724441902c9882d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 405902895 1250 405901645 405901649
    0x30c0909070f030b18180709061d07180306152102280b0d09080c03040906050f09040305030604090605070f02060f0702120310270b090f07030b010215010618 69
    0x5e40324201d03a01041d5100248105c010415003000c5105504140c51300000e02c40400640030a51040c08026160629000220503041592046880d040b0005a00a10942640a0740000e0345900c0c103074180365880e00c41c0039001d03029018170040c082e210005502da49000c3c20302464030600103070401d002460700400c50398003280c0450000b15200072042c44102d45145952006a5611141480d21205000c8001c8020400c440000b8000c01c0d001070324005054000000c2c00031980e190b04240f0a1686038401d11040a20002a143d0812000008030300081c0c0544081d5a1201000e84006088102906c803807081e141d0036113030700c4042401080c07040040ba905016441c6d20a035465035400c03103800c10240080d91089002407071070711411701002040070303050000c0040000741000e03404c8000080141c4050f28502d000103410f41c0d4114944070400b01c0c80d0038085041881413210034500d002c655210141136010f4100c24600310704501541302d13841c10264100da002400f9241c15075034902000202a0415016850f0ba = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 405904145 1250 405902895 405902899
    0x20d06091506022d030a0203040f0b04080d1101091b09200d0507020304080f07090e191b0302060316030b061305010e130f0522021302030c0909070f030b 67
    0x3041d014855150001180189006502c0c00c080807664070402181e121380b403484d0800464040040c40200c2264000007910a81d1004480040d0040d52803440b10f015104e1441460031540040281e03107461801005090107804042001044112440d42d5030a0b019018000400c60704e0421801444010914801c0d81d9550603082d00050403a1444c0301c48810f18010079410884058844001411941c4280140c400410510048905a0350700f00e04054541d9014003a0030041c0f071402e03000c5140e19000042d0780b80303183c2c01048000c14049494441c041c4990701c0250810000010407400401a02c0c0c1c040194480c0c403c40180552002401c90001d0907124080f0000b449801d00b4001c0346800310349038841d00101d0b202420401803180d40d490104049003072280c1d0501c03400c3c0c0b0340f020045c8803500c9600302612410642810703010140c085080701d0003480e10980060b40085641e000c49410b0315281d801990003244010344c9034180ba01d40c20000c3c803200f0040301c211000480c0789410083d800d0700340c0120301c1c4400302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 405905395 1250 405904145 405904181
    0xf0409050405010e0c0a031113110d0f05160816090f0801090605011d0109051b040305010e0f0f070501050d090506071805100c0204090204150f030b01080c3001020d0609 74
    0x285480d42c5054014841d4454440c1140088a4100341c202b90701121012505a186c3c684030108001802e004081c5198040c448030304145c005055000040300c003e2402d110307a00e488009441e8840b11000d1845d00358a0a02440f44048009c2031215018548000030b01300c10001080c089000d2421400743e400692000c08925140324068080540c100c4145040d280900c100241d02c0c2d44010f000e003803012031164140f40b003101c002004401e01c030040d04070b183c001c0300c2a800c0717031109003030b4801d481da4034110000d000382c041c0c103d100180b1041d8401d030020003000c402c80d400440c2128044c1c84142c1850410f440b103070042038410210212040e9008602402014100e84910610b210420007404025450100038422036651841d402103644941c002800700e140e0101c00b001076900d54050b8416401e0a010540714038042500000c1d001d400060b02c00c00000010384141c3e8400400f02858110321405415401a20800031060b548140c0920142102c0d003508900407031000c1c540542c401c11542c820320b2110420b60 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 405906645 1250 405905395 405905399
    0x6020714101505060a020705120a06022a0c0906040b01120e0d1e021519050103031d030c03070b070f1209090605030a050604030e03070b03160e0d03080a020f0409050405010e0c0a 78
    0x20f0086041d4023112801e0341e44030b01d010740504046043c614041c0e00200740c0c9201183d10081404811200c60708400e10021596210540c0a00d0a54500c915400789a1003514400040c2003410150003600c284181070601d650320014480d1048143d5206444038141648500d000324041ea0703004050302d001c2402c20b070801c0d44003821410000e40b96800041511036081c1c95001060b01c5065007400348002005005c4100000d5850345002006054070320303d01300600302c2604000100d0b1074003003000b90f401d4800800800b205071030f0040c1c0410a800640041d11500c0400302a00003142d00c0702c2c1c4000320b440a070b5564030415400c00031a41c017185e0071508400e02960000306050000384001802c3d9030047d4060620364401070782840000d184c0f030300503080003e50751400f205101410f01201d61403810341d40c481e00c03030b20070a40c014410b1000004035080041d000981c0880070401c2c14a040d40100820031013068520300d07240c0c849000e00140e034401c1d02c00b15600c4c0c1d0350708500e510f519024818040d885104680c80f40c4176034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 405907895 1250 405906645 405906647
    0x516080708010e01031b17060912040506030412031121070c120e0303040b040807030c080114070e0609100c02030d030506030705040b030c030d0c1103071206020714101505060a 77
    0x45070500000742202c01e01c0c10980d008030801010030008090a07d64050900c910110312a11486c0c2640e10b01024410a10200b4401200c501510150317240548220304503a101e840e02045038507018040401d0640d59018208540d000c0e0004110b0101003c2e807a103c050950351410980400003441c031001c214002429500145a0804086d844131507882c08181401c0c01c480007a0851007103038807620581d000000c000a45180100e0520202c078002c0460014040c0d40b605990700381c6102445800f00d03c1340d14400644000c0c05801044c0c030481e0013400b1a0300b005200c90208610307541c5140d40e00003055032440e0180840c5020006080369568520b4244490309080c00417a540d10f6250041c0d034402d03134940c604c2000580f4208181c560a00d0010103c4d8440c0010260281003245914016034402c1d05c1115030640c00d080c001050740440d0101c040c0b4030031511403521841c00940000008032800d8101c1e400c04a48c0b80010082481e1002c10880d0020748075440304444040134500b540400d020300d105200c040301075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 405909145 1250 405907895 405907919
    0x20a0201080a1505130b0a12020d200405040809041b020c06070627050d0305010b030a0f0b030a061a04051605030c0c06010f05040b0906130f020706051608070801 71
    0x1110b0392001254401005900103002c0c03a09800c80c94200034401d031022040c100070740103034007211400e5402c440340c0c6807901310007403d4071468440030303400c8000300c11004005014410181c11032030180b001c004a1020302e20014003034900545040d201c06ca400314110803186002d21805101c960b411025812000c189000a500e0b04cc5400c1038901c14100411402d05122803a0071519052400100800d03030000c6080203e0643c4400322401c4ea454464640d204c03c00c01d0085c03007054140c0768900e00443c2541e9607041c00c480642080b0f1208500552070b0015482181c808204044040b0710440021541c01e4000352012140c1403441c0c0070302e10031070404083c0310031010245218202c80e00d4625181d030f80d0ba5200c09810685110343c0652000b01d10035100001000c1105100c03032000d55200712014070146001c2c4003081a48081a44c6075588940760b11806030700406140c0c455980211000d4015007801240d481e00d01c100e0344202c40300d02000307521880127044541c0c465401c5900021505026415504114100f110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 405910395 1250 405909145 405909151
    0x1030c0e100e030c03030d06080d080106081909050a0c05041505060414010912050c0315071e020f01060306020408010507030c02120c0a0b09150603030a0c0204150905040c15020a020108 81
    0x5110b9009403a01c4151002e100300c0701300385405421255036401c1e11791084010312640c0300c0d8500f103006518040442d940700318121412a11140e54030380603515548030180d06c45285105421070340fa6030f000c07582d00086061080740b0305103020700d035040a001c3c64001800141e4040da0940c001c0340340030384020302013592894256002d990720311100c00e10000b4501c1c01615020074035002103041c140007420366820080b0000c0c403009000010f0b01615006850006008180c010646040300401c0f10107040001c4a0814465003c110751184115070f190074408500c1e500711081500203594041d00040d040c041e40360b003406400d40020840c41c0410100b440c1240084d15180c0f911180c01d0002c074001440b104ea410100201030840340c00c4045504e09041002140382d072001c50f41401c0441803050400501c03240f0380030094402044160300c4950a0041c1d541c20400281014a520507240000a1000c260103455105a5100382d10803000c00c84007506011840301001c002d81002004c6511a0b501c0c900182d03401440207030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 405911645 1250 405910395 405910397
    0x305090715051b030333010c03050903070b031305070b03040c060c0f08030c0306030f060417211e09010b130b0105190315080a02030a081b010609090201030c0e10 71
    0x62111400c0c410b680c846240c0c00b0440103e8032011040c040b6030786903d400c0b80b081000d07440c20120100c5002003900c500d40180204035010a05100854002c01d004600038400c0709030080c1650f840d283c4507980d08140c2d40040e101101c0c080d005082a0301007210412501c00a4500d42d00124114602a070307400003140305074041c04040240d007111807010005c50110080811b80d11031b000e1512483c20b55501d000f80d400803140107100e4403c4d0b054684500b01d000c10f005014a0b082803800d6030790244502d219070640d100080c1500002055049a0309404001412070b0140c2132060344c02c88030216040d826400c0b10409000c010090b490000180c4c565540d1031007411030003002c500007007a90300c0c5420040e9202c1c0503d450220b4410a030840002003507034164080c1c40c0212094183c0300340e56460b4040c0955039801d03074030000e405a111410201c085880103000e0802418103151200000003030040d03990a41c0c0307481d0b00c0084025103d5131400e007150707010300403901d4890b0b5a00d44410120500800149011201c0c05c21380 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 405912895 1250 405911645 405911647
    0xb040b090102030708210a14070503060307230907080f010306090602070b070e030f0a05030304020d260a03050f13060911041103011d04030203040e070507020d0b07030509071505 78
    0x100ca074024003c0d00c00340e6030020002629464100761940101c0140c0c00d40344400c042c0b440c00185030141c0ca1180082912107001c0a0706141d44107201610700340e00c00b0708416454824845c0006001240411141c0c88000e4807216200000c1100705102c1e00d01800381c40328040c81803610400c84508036012103e41101c0c1c21050102e4001041e0a004009200340c45010381014103600c00c1140d40c680110040c503c10b013064007183c0824620120540e10b038502008010120340040004c1800751a06c8462182c0b91402080c00c80450b80303880c512074101c14505440c150504101141c000c20705601072040c1a44100d07101c441d98002d02c0c080d201c40240c1d901e500b00c002d00716a582e80110f424400c46814030700d0310080251040151544440048160340c109100340390064503140d86950361440240701040c029a899001141400c0c18000200c0301c041c00104018102300c014410340c4056500c2d0000c00005501981e840303281800c1c07041c0010107460000304090010390044404001550350200f180d201225945452 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 405914145 1250 405912895 405912907
    0x5011409190c0e010b0306030d030203070c0b040c080307140606030d1407050c130212010f06050301120312020a08180d020318030c04060b030105090f150f04150801050106020f03040b040b 82
    0x40c0c080c11030302d80c1001500c615a04004906071659400950052070220101c0d00e01c6a4506001c60691100310f80740c3e8002202614554001104154515003081c45800e140490548481d01c842c90360300281d2050f00c00525152009800340c2c014444203030060000c2c0d01401d220001d0240107031200c1084150303107064800018124003402070078031082e0b41c00700c0c0090a0000e001808603428010790020403041c044109908000181c100b030300b1280c941219500d031a841c0c116880c3c80318044e1a8100c1400035014840840030003041240320b440103080100349500d071281942000f505e24840c02a0070f441895087c1e200401c40201590000281c0d00e0326a4a60f8000c0844280b04010a042c00441c0b48103a40160034031201103680c0c0c9030080698161442510300c0c0a99a450380c54040c5403e405441c0c0840181001200540505040303143d80b00e031200c007030404104404100c040c0440d65406500082d02a556040144542a07050215864610040c1c0042d800c25040c540d4218081c402d610440558680000351 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 405915395 1250 405914145 405914153
    0x8062d01050c030d0e0304090608011a061b0102070602030114063907090e011103040c0509070314040c03051b060909060102070305060108030406030c030c0c0308070306080a0303090501140919 84
    0x701e0304c4002c0032040c203005298816070646c1d03507a08070340101300c611424003c000c0f27040b150511420240d11002062411510f00c1803050244c20741c854550000580000e03444921f221381c0034001002514407071390006940390314094110354255030884900d40b1400040040841c420700b5812102c001000320b02c09414480340305042c42080c0c81c3c03100f000840a00030401c0000320802203900602034000035000900002c0c024166101c003502c01102c005081080a400a10850030a220300c207500007498100003940c500600c1800c6200381084030101d803000101d0030240100901402125441308400083c02140d20f005000200c1c41e010f5141614011015000002e400768820001940110303041815900503586540303105440c1d1b4030030b0140c00042420903080c0600c89110b441803040c02c17016661a00228107595604a030810405080c0f40708054441c0170204441f10140504503500d03101c0c0d00d00140c0415542703000c50944020b101d040485800070002c00505140201e05010011550240d4010030491850 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 405916645 1250 405915395 405915397
    0xd0f0518040e03041206020d051b030a051009020301030609030207052b050717030d1b120509250603050a0e030a0503071407062310051302041508062d01050c03 70
    0x1204043c05e034811202c08040c025140c0c014003006008640c24030450f40d42c101c0d940b000c20b01170075190955038030410001c2e40c001c4c0198002a044001211552001c83d606c04214003640c0080e0015141e45a84481c00d9007019010060744005003400c1c0e40306442009041980103150041c120110000c0c00c00e01d0701c200c1001002e010000c094126000f90718100110b1529080e5290020051b1104841c03030301d4941da089409241440d42c0301c902d50303900c00070b600d01da001031840074100141c8a9080c511130028912001c1c50702c0c2e0751800741110391010003640c46207010f100509680d4041c1809044c580380400303550900078040102c40092240e0b00300656a40c403541e00c1162944515028100416000b041610400190790042c40100d42480c80020a403c240d0092107000201a01d0030000340303121400c10861800d0010b012a00b180b5560401400d00d643c4a0030351032400c402070311020009103004204400b9203424611814208180074540341c94903500c094640e00c1c4010700c21124180600852a2103003040100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 405917895 1250 405916645 405916649
    0xb01020a0227010b0c061302120a03031a010e0d17040b03270f0c0123030118050108030f0703030515030d09210c05061303050f0d0f0518040e0304 64
    0x30300044284110003400b072050350000d000550988144000005600c0e5030201070742c00e140c5251025000c96114500810703031040413a401281c00592401008008400900c01508101c2c007030b48011928450381c190140582c18142c0142d814845201c0a07850b003901d0f0041000503031036020080000c241150710a00302c80d802141d024004040000042004089800e4840f030b12000c22032510a110501c080c040913252900440780382595400040040403d6128442003035560940748685441e00001509128807070f407090b004030142c0c035604407050b20a901070780b04150041403200007030360800c8044070f00c204142c882c1840150405813600089100142101303403024090000800315507800ba0f030744e5406098403000348030f03500e46141102c01d402c6042c0e00312428841d40c55800140860134600341010024946c210a190044201d0001008400181304200482b0442d6001005000300020f07624002c1810500c1c11110040280500581c2c4441c0906c41320205c8400d0300721070201700c100c01420550300c2d600a517 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 405919145 1250 405917895 405917899
    0x3060f0303020f160302131509020c0a022704060b010513080604030807050f04030f080903010606020a050c01090b1812010c030c080a050903030402150d0c092603030a0b01020a02 78
    0x4084000105500000c0c0d040300d0031030310b1094074102d120301048420301803401e00c0083e400c2501148070122014244c1d212035a00b42c680304460607465240c0c9070f014101d1704800d11002843d03028103050400d500e0300c80260014000b00c1489000211884245600e0010f0094001032035662201c0400146a0048050310344402030f40e18100410359607141007a0b41e4410036607081e00810300560204e0103080c0b2810464520003000c1c0d2a09150501c0c55458400d0307005045001d94494506000104039a81c0038042d20000707000d42d82c0145005212414518208034908502d50305101e10000100241c81103007040d56034183e11a880640101042d0011420500384408441415447c021201a034280c25074400005041c141d500d40c4140c3d594030038844c1c111780c4103032880c030360a920500000d001450318803034038001484181d001c5824100c14003880003e0359040001e11000c2031180000b031100200001d2030f40420f01020b02c820420f484144561b58a13840040c10480c01c131034441c100c0114503402080380320946540 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 405920395 1250 405919145 405919169
    0xf0503070c0b040f031d01050f09061b0304080d0f0c060b06070f05070f061b0204021303050601030f02280b0306180c04060207080604080906071104091a06040e0604120306 75
    0x1151401e00c2050040c0c81c0c1c1100030904c0126441c100301c5800040e0044840180c603580c1c41e011039054a049c0c00e412a000d43e591040041000041d514440001d5081000d103074030041d0344540c100705681b42411800d40011080024032944140540d0307128405400007900803400280054008001c11314a00c9882c3d0003810800a1070006420031400240031412546664000c4807002c1e100c020440c3c50358280d003585030a98000302030341400361605074001c0c010444035140880501e5aa56196820800264000c3d01c2c0c25011003460410750a090140c0b5240c050510440030032040408240718007200c2d0317405407400b428400b000007029610340911414000d44072422204080c03406142444c00741c1d106005410040c06488070000340168006003140c015984615507504104015040c810aa0040101900d060301c00c01407041c0907440d03612900406c2e9000b4540c1c01d60a00100d0780f0840b01c90000741045016902c0c010030a00b841401090054100c1c0d44241406007000b05c07020100d01070b000c40d411141d51258 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 405921645 1250 405920395 405920401
    0x21b0d11190e010f060212091207080105150612071d0415030c05060703050d020a0302041505030a0515010e04020c0c030f06040303060b1c0207020415060c0c0503030403030f0503070c0b 81
    0x100350610030120b031202401c24401d40c0e2100c0c248882070402d48200700240c3e02080b017000c8074241d00809082520800380512100c41f450001036482d105c61a440382d58581d42d01d1052140c034804a8030b60140d200800c1d40d0145c5090360044040411100003071480080141c1d0491668104104108450351413000520074041c403c0303e0103803800201203a21080f40c03c2000d20200043d641030090580b0b6807140c054035010304007591001100003075800341c1d682100b0190300304004660b4049000c28045d180c82c1580d68152a40b8080c0d00071012190080c01014291440c40c04499490b030b44074110601012042c1d802689071004010618a00908400380507410300540400703a40b00302001402c1c502c550300a50382403001542d01c5210342410704c5090705940020907810500007003658a41c0082c011107101400006030968209042030300818a90030a01c0058441c420840902c524100d01101401c0c0c202c024603d09491541c01402c02807451200400344940403000810303080c0210340058400350000f501401500e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 405922895 1250 405921645 405921679
    0x9060c011e0c0e040c0801030f0f0204020a1d031f02070312020f0a02331e091f0b0a0302040b0a080f0a03030f09050a0212010e01091a010501021b0d11 66
    0x8108200305000041c00c8000400380c07441c16001708005034800ba140c86010380d0a40d210079603150401c0206807a0140740c4130a507401621144002c262118565581050400741c4a489580e079030b44880c1d1701446580704000e18810640d0f030743c6030420090b901c4400160b941c0030300e25044c5c0d2170f000c2400c900c1e00032520208808000ba44810010079841c24141d0a58a00080010540b400d283d02c2002d052284c0103814050200c001341304aa282d00010040400314412a01c03003585405500100c9241002d03401c40b20301241003107148500303c100461078500510440a0002c08642d1706540c9100c064401ca4a514807200030b910354102203409000e901064407609160141d1242d9514101c3d98210002860a0150007140c3c0c4107200b02034013140c4c080050005070225408108401007400070344000c9550351282c1c0c4004402c00d00c184080c0c2d034400c80c910340b12078140041d40c0c011003105902c594155000104110007600d6102c0d1080c441d0841190301000224240c203001c00e107400c8540925030045034041c420640b0f0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 405924145 1250 405922895 405922901
    0xd0618091109040c12030c470a151707051903020f04240f050a06030c080403050c030d0f0f0f02040b091c0206070c0f0609030809060c011e 61
    0x180e8020840030903015100020301a46803821100a0204100198140b11000d246408141d01602925042039500f403562104180030301c5184130304203c0804140c000895000100500a61a0006000e081300d0000c0c481030031360651005100b07000d00740d961101c42c1c0c0c040c032804180d0b0703000e440c14410202c420045607180e503a0f50035080c00360a00c40c0380d030103d03a220003a80e5046102c05482d800381c41c110315207000707001b4803003d002011000b0a140a0701000a01020032000d140c070001c218071a183c0005924190511160320900d030840c07000c150420440b14100798000e4500e035085941840d00640c0d94640707183c41400c5005c0c00400c1400310741050842c03082d40040360440c0e40580700c5880108a4104156186030807449240724595120340140321b1404180f40180c1010303038000d01240880403661060780003590340e40c0001411611000d40e8181400f50302c2401030020050506800c00701740e00c03815615400380d070780203410a1603c10100010002e01e8040c080d003000d5155441440012508105810201c0207 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 405925395 1250 405924145 405924161
    0x1704090c081f120f02040f020c010204050f030f0a081b03041403300f0705060115020d020c13090302030c0a12020c06070b13030203071a06010e09040b010b0d0618 71
    0x1910402002c19072441ea200035440c0440700c0c041181002c50180d640e8424040b0b403100003e0b6409661154410908241d0340000c00e03401407102e0005a42d98144810800c000c10b50305444ca00940c003034040c0c0d0440c0c0200192041c040c03a0007803011078480009005216010900030700c0c1d0032840c0404280010300b11404174030a82c01100840588000d028144455110310b0810428460078898801d41205020305200c02403e091114400c25880d0100380e44580c0c0c80c0200a130300101407140426103050005905000d17800c03a502c21840a820103801120018050b00507542107c07501694544138002014020001c466803100320800380c4d181002d503414256050000c4501e418050701910202914070301c1e00c0401c40b030310168440e8041030903071110501c030044100d44440440552100b01710010100303880310035004041111080c040f005180141c0010001c4020810040c0103a525405010008041c15802810b540203a1100303903c0b00c5827191808060303c1154028100030f006510310642c59041508288a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 405926645 1250 405925395 405925411
    0x1003060e03161a07260601030b03070e0a060812090906010e1804170a021011070c0e010302032a091b3105030a030c0606091b02010507030203060d1704090c08 69
    0xb42e0764030804c05a0700717107402d00219150501c902c48920144500300c0c2c0440d40102c018136001401c1035080d00420310748240c0d038010910807400d9500700302103980c40340103040281011078081c1000c0c0f200c5000c000098024020490301c103142c142e00007901e90b482405020205a0024a01e00b00c074140c1e03101d0395588980694040d80c18039030220843c00e0380316a460441b032040405600821840e001d8110750b1000f41070070f00c101c0310f01200070071114010900c1d082026000d0813402112080320352440c03040600e01020122100c00342d03a405140032285811884a41059a2044e035040b84a95a031b18550409007840001c0b2640024021980d9540000c9220b91141c2c1c0d42c090702a900a4a809010344050480c160300c20a07a056001c0f50140000920410325414443d11460f80810181d40b903500701000d40700307008041210324100345a091001682400749540120640c10f0031072071410700e800030402c1d030500198040d140104e008009601c040c0e1410448000304400d00042219541d408801090600b0940b4506 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 405927895 1250 405926645 405926693
    0x30403030e0c150d090c06081f0e0f063c0a0b270901060e0102190c15090b0c060103020306070801150e010c0c06080613051003060e0316 60
    0x7041c441000288150614001030110b50303401c50640068000e40e0000d0b9041c804580c50f0401d440001d42e1240700d900150000b500d40700020325000400051001008000b0201c19011030b20400404d01c0c042d1049030004c405600040d52070341c2c0d542c0131500c40d410200008280144600011941c2c4000310f4107401e001600c8100c10710078102c014100940110a0b0140059607070382005454072801460181e11070360b1000103404100803620400203902e40000b40d10400200340c0c0d210140e526507a0612071130500c1010162149501006900d503240f000d40e190080380c01c0c180c50301c641105030a0103460201f00a0440b140c00d95607502800900ca51686c0081c8812400713849080d000c60010343c00795080fa41650002140c0b03240390f20000900712280e4091001070703410706c04d891181030042a0442c004c0400b50281e512035850f00d003404e9043c8103e01a24500002d802071505040c041105490044c00c401c41c0d42001c07020a0185218000300c0c114444d02000321002c01483c0031100800035862150120880022001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 405929145 1250 405927895 405927911
    0x3023a0e010203040818010c06050f070f02010e070618090204031110050f0a0f0e1c05070b0a0c06050406060b070b07020c0609100309110a140907020f3403030503040303 74
    0x100c1c282e010a680007043e01c1e805200444844940c2d40c0c1c03644d03544105241655a000b031545403241103650981701500301c1d2100008001802c0d412844050410406d403000b0000e0380540100741e51207106c2da014603000c03c078584100200e140d010034480d101400c00710204540c1c0366924604800403200114115000d40000c091405106000e00f0603911200b50030840d0b10315000e1544000c8825921540010f002e000e80740045101980751030071644184817023200d400b0840007080c2055132030103107103500190750042e08100404015a02c0044005a664000c4c00410503465610741040a820300c0d82201d2a0450089858018884040000e41c0100c8640e000d60340081c410005001091041180458120110401000f0340b644a070f80144440d03800742e98411b46444c14100000c940c024181d1208039031000f51130503803c0398074015a4264004506c0d0001342042c88251410944984201405916480c0e0001541c1503c0d2080189201e50a11010a801440c1d4913860046c0140d0800d031760039000a441c040e82 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 405930395 1250 405929145 405929171
    0x70506030610080a180305030a1a010903030c0501110a0f03110906030c03070c020301020a020f0f0c0306180a0204090c030605130203030f0a0c081809240103023a 71
    0x11203018001c0540909001440c09030700341e65140014207146921a5122210703420601521500c40700307148203940b09981c1c1e040201050003a210845060190030810700d0009441d680c0104c941e0045a40c142404c12682e800d60a0041c01400c03440352440040200107500c1044a500c00030910000c1190b4404020140c90b110428000d400b40311406900300d101040815854065440656802500d51030000301c0300e1407580c0442e013641c02400d030000c0564070400c988009601c0c140f21185d250f90071035000f05444100b0f500003a544950241c0480e0f041c4100c3c13519090305100502210303400300c0c0c0141040c000c04606142207410302440e032005448040c5000045481999418800040150005d0045040480c0c50501d00c45a50100d02d040d001d0000d400020b070001440000508201d201007402a40010354410900440780d40060940d8054010040086414035036203042c043d03000028a0b0050301e441c20301a00845015500707000401e0642c080554500c1450444185580001c1c40351060001c5200703908 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 405931645 1250 405930395 405930397
    0xe0f070608010e090a020105161505060a0e06100810120309060f050c070506090307030c03050703060b09130b060d210e0109030b040602030a1e140609011d06010306090c11070506 78
    0x340720703215508040b00745805503218202030500b240700c0150326103600c0c5855540d10403509a18490403082ca442f541004442d00e04010800f0003080c032140a0070843c50300d04000317486504e1540540e03041c8908100851800c18894110b0070103404650740b00c3c11200880d01b00582991110700c1100009100442e10359245032169050300c80d1451440000c011050810082262030341040c4401c42d010b209200300040810410901c00e001140030b44003902a0358214108917060300c030a0000b20b8060710710081402082d0f041c40180c8401140c21980640749620f03841d000620b0b02d400407002908260a0200e01c0d03404550f80b03107c01c001d03c0c4003900c4d4410f100d0159401034031030011602c000b070029800d1340c002078040751040d001150f200660b480c000480e881d03614644546101501c0b1180c1a09646e0340d468148541004c0351b05401c1401240c04880d150301d00b035600d0401c400c003041c80b21000d284150216040f40d0098102c0e1014041c0b204c0c1c284415406208028814402c98810000610031014009441c3c20020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 405932895 1250 405931645 405931651
    0x1707020a12120c050309012106181109130b010201140c03090c0319080c0307061d060c0909070e04150611060610090611030c030d0b1806030705130e0f070608010e 71
    0xc8045c605203400700005650304e680c005281681014851000c80d0075003514840c640151003001c5010799803114509498044660034a0000b9840310100b00024096441910422003d4100031010818041050040303015283c0700d0892400c040c030700402c1c822000c9903000918402c035000d6044070102c100c5c80d420541c1c0ca00d01038202200068074020400080740c0c0b0000181203c2c0e90a01c00c0300c1c5040015170f070b0b10045880301195004c0c42e5044180d201c0c10780206014882d000b0b0303000740c006400c08031074000080342d95801520030014400e000040107415207858001c51891103090201104680d0340303120191158003019030324441e83c02a40001071061a1480e0039440c9810599a420b80d05820100182c43e14501b101d00d8001ca0b1005200c807444281007000200102001c810f00444c0e0724105006000451144000d03500b1a0300803c82007200c0c5840014442c02100d10881d110b407003103080c2d030110300000c1600104d2606a07024414140b0840c01000813170798121943e640c0d60f01c01c6a82da4041c2d00070b41101c16 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 405934145 1250 405932895 405932903
    0xf040311010804031b021c0807120c080d0507020a0212060a060e100302011b12030f050108011e0209120303010f0302010e03031e0a05042103030b01110a1707020a12120c 74
    0x45c2800902010704015021301480604446900ca01f00d00400000c94040352084401c5400003802104004000050f500c122102b070500c0030f03060005a45101c2c0d5405000c20034a03a10b82c0d50400a0a114400c10028100f25000307000e01640380c1101a0154a81001b200c2d150030860400c4000144c40140342c1115104401c0040040c0304641507500446202d100d0035140c0341c00c2040742110201065202c4290b80400e401510b00185402042c480720741a078005a00c001c200d640b40181c2c003401c0d217840c00c651000c0690b903c00e0040e07450006d40002020b00c0b00110741c45a0901c000300003c0381074003d040c002d2090300e000b601c2e42000c4110040c02c06603a4802e00804034800301a01c01c20f02e140321309401c080c00c8400384500717000d800d003034a822003070746042d40d980c4412140341c0c0408541c07070502d9054410030042e2107003880c0018400c0200324a2036503401a08030014065114126060380d100c002c0000d03503031360079801806801c01c2d44e582c264044008150420036500c0e03c3c03240490100d00c90081990800032640 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 405935251 1106 405934145 405934157
    0x1021908030915130201170f1501111002120c090a060509011b0303050402010e24210f01090b030303100504090c030b401e06020f04031101080403 64
    0x14104040702001c0c2c4e1007050250865640c50f0305a030008c515502290588402d60048481110012400c2f4250141e510070086980d0705400501e400c0150014004803520351307e56460a82c40b405a2346a070250602c142005628000d4020b05a940414140924011140082c1c3d030b842c0181075000b200086c2d07440c000c01c011036070070200ca41510f5809440c01d03400d0030f0849a03040b084489484800d000b007200890140300181041501e424640d41100d98060300382041c040c3d9800100c02800741c482c000b400d040004115060010a0783c0c840c0518442c00c41e22207107403c0600c402130100c81d405980e809508200407000c14603491145006501040041c110603996412401a0400c60f01284c00000b07420500c03c44141001d000d80f42426400c04111720205043c0d92580403400f9501300001c0003540003041010051001034042c00450303010351030002803050300038011687d0740c02c00c8a0003008144 = true := by decide +kernel

theorem cover : BRFrame.Cov 405755395 405935251 := by
  have h0 := BRFrame.cov_init 405755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 405755395 ≤ n) (h2 : n < 405935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
