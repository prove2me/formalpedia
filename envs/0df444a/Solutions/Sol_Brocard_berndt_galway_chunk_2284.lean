-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2284
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:14:21.236484+00:00
-- url     : https://prove2.me/submissions/690e188f-d81c-4e6b-8c2d-2186f30f2bed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 410611510 ≤ n < 410791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 410612760 1250 410611510 410611529
    0x4051905011e060e010311040b04020a0509190f1814010828080403020418060507050a080a060b1603020c0d0305090306100509010909020d02031606023003060105130f050307 76
    0xb0300e4018132a81000042c08040c0c490b40354100c2c0803003d9121500850141d00010f44115550000620020034542000704414071606001c58280d6620504070b0400d4259650654120b40b117510380101480c2d544509052180c11589a00b50110074150f640140e500810307103a00540980e0b01d44000706111400c480342c20321001c0c2c0402c801100825040c80585080c1e940c144ca002035044c0c1c00071001d09103001d8000004201c5070421041100c2203502101500c0b00044d0b544640c1001d03101c014284080d0340407400b40c80b032401400c0c40040160990840b00c0c8420900030f0041d10b8a2a0110010540d041c0203000154007003400082d40b03200c5070a01b0022907a1000750150b00006441c02c0000081c41c41c101071113035181940d03d5540c000306550340c01c2c41210286ea80181110342e01501c0003c580400c40040c85800c0142c01859808000c54440f042d0520a0400c00300c94801409170781400061242c001420300780c10020140700541d40d0444100041010341a50300446010914002c01c0601d01001500444403a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 410614010 1250 410612760 410612771
    0x9010c060e01050615120c03070e0a09020901030b030f03030c0906160f17090907050d2306040e03190f0c020306100e0108010209130216020910060923040504051905011e 74
    0x3c00400840c6c2c54004000c41c81b1255a52104070048880c00700705044580e010615207000243c84243d54001c0007100020780b014841020020101510756940d00768410498004000080075500017000900e840880101000c0c03c06108508030b0104101c484002c0300c1402030103c04c04280069030907070003204001c11040e1490400440041601428040c1070f40d414080c010810110210381500002450a0f1520f0103070401e180c14044d40644078400d956030350003185880311850b03030544088200c5284440f040a00440c22948100440300b40c0001c0c040c1c80200001440c040700166401e0046070f005070840703650504c9040c10851081507002e0180c2c0420b986a00c100b004101c2c035110740180e0388103141c0c1d42d80700588031620720142c10b030345060481c0e009600c4048075041210f184030007103440e0151211f660700c649510751202242612441030726a04c2e655840c3c20643c8408514058000b664483d110310196128403641d14502c80300300c54654411241c99443c0d403e1802200c01d01d6102520541d0740000a021 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 410615260 1250 410614010 410614027
    0x303091b10110f0f07150206010f0b0f130e07030b03070f031b050406030309030510020a05030a0e0715030b010e0d170a03020f0a080f060d080f09010c060e01050615 72
    0x803110300d01c03400c00d0180b08401c409907140d00414001c120010604005032002e18185000382911030055002d1380100e015050f200d000c3d81880000d04c10705a0b1030086500d00518200880d01c4803075001150844e0b2162000c01c0344040944240110000510b80e07082000d03014100380300c01406540d885442640250b000355270420003298503084000440e5004102d000801c103803082e400e819050300d5004280c219042c6240001050351060007641164060015a1714401c4011400c0c2c1c141c0c8a00c42e030060000b001070000c5103407c0016804588046610400c40308925074030075000340cc10705160b1608000c6036a80842040ba5604201c054008900403104c120000d16144e840386020440c1c161400348140000c00c510080c140264119070000200503480c1d40c9442c00c1e0180104100d03000c84107182d031401403401044e05800c210001003070b07040d4003410f42030810492804500d41c4d50404512581000103056400c804554544038180824840f4400881c0d01c2c5041c10500140050540c2c00d0540b07150200300019 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 410616510 1250 410615260 410615269
    0x7111605010e04060302030a0c050924120a0606030c0f05040209060304030503090708060901060603060e0405070312031e0b011e0c1205040b03310c0e0403030216050303091b 76
    0x1000ea9a0900300301a9000301080800c000705540e80000307400d84181e2002c1e40500a01404090072a04100c514804643d2440c0c0c01c40100903807a0440b0079a5084403100003014984046204c013010013030b00851390488115200c440694820398002e40d0050007507201070214200345034520014117403c0e6001d61500000b14003140d050321000704040e0400a002c408124429414080b640082c00304208a501500b000d010241c000c04152085902003480c050340000d070591044800c6102d07681202c050100d1320b145403101c507440e181c28405d20041655945d2003aa085000d01400900304a02d9400064011a1080050a5025842c400c0d8001002811102c402e10354081d407528041640b1804c001c203451000ca82c241c83c240030305c0d0400c08844c080802040042d1034403130810009503403864039698812844e41160540032111540c00b030011307015083e00340091078100d803d59030018070900e4014544900c0064408290741002c1d0211119040001408040c4070200300004101c05600c1c1042e4141680300c0014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 410617760 1250 410616510 410616553
    0x507240c0e0a0918050304030302060a1b0203160c0807030f11010507020618010c0b0703090203150907060305090304031a0a05010603021804050603010b04050108011512080a050d0204050a0e0711 85
    0xf0b0701a5103641a1009002440700445400ca82c01012651925224a4080e44030700040391003d036035a2400c070a028032044501566a040350300350700950310f08076285020108070b007203090050312107003141000003403001010010304004500030040b031503207454149009080c0113100c502060401c0801d008110241c2d541104894015242c51400c1c078a01d500c040c0103030f0704040c0f80c02c1e0161050480004110b0019019004607416038421000d4410030708049a080c0f036159000d071440300d00ca501000f0288200c90103070f440642c011420008480c1402da80e1350390b042c03840010301c00400085110764188442c4200c1d6000c0d40d8050b0110313080541c200712003950350b405c2d013480c01440d061059448a02240c1c607070300c0a5200b42d84403103001c3c00c24880c642c0c4506a044c06005c108aa1513031419802c2c0001a0600359201c2c0c0b104c04590040142c0e01c0c049418034102d60306d40101050300b1f24a542088005200c0c1e0350242004004c24003140c908026141c01c071170241c80b0000400e505022900240c1c210180c000385840c24 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 410619010 1250 410617760 410617769
    0x280e041a011b03120f06030614011a0d0605060a02030a020706030501121e021509030d051309150e090c0a06020114040b0a09080d0203010806130b01060804030507240c0e0a 75
    0x4403065220142011071382070f4081100d40b4081460032031035004584043d0003981c140d80c090703c82030064081000d410840700000344140000c500018194180c80c0034540c0040070040c90b2a4004242d417a100c0c030024000f43c0c030510710304001da03100054003080580c0500490340208040e0030100925803510500a21502c8c20300001001100c848481c003d03014a0103032282005074024212105d407a2103007069120503070044500c40e1080c4a100c0d04120018801c3d02120a03401031a9025001c46180002c410f000d0924034040500c045025000424042c3c41d40c07003c0381c86100000014002405460148202198560031407011039040c03480c1c5d1a0500d10701040e02d0f0700039034000c050711481ea0707402d1500d40041c8107010004052460015204030321906940156040e515281e0688409449250017584486100c01008004214410041203164043e041c6181d00030300130f007851494201035990f5145c03910031740000503000c802d846840503020700303040c0f0a035000c1c9032560428000d850f01d03040c00901940c11034031a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 410620260 1250 410619010 410619047
    0x40305030a0906020d0e0a030306120809040f020f0a0e090c03010b1b0705030111130509010510051e072306071b0f061e0b0901030201090605280e041a01 67
    0x2829401c0280130740c101c82e800b01c05040200000808400929103540b4001c0c8140c00190074500e011818146034240c1c04084c650082c20207145c08680303002e01024010315600300300309590910540100c0618800109030418150761880d4841c005e400c100144a4005440c02180f64001d000501060a0f25000c40f8410009801d1000440540c01c2d0580c3c80d0038aa40c0000b600355003448901140f128448000e0420f20304032000030b440d00c9071142d05022012200740320326980840810340b171001c024084c0c00105800582c1d0b6003103c0004407920713114601c40e44140012188400040c030094412040b0406180255400c98050803e9040021009003098102d0b032250300c030490840c4400381007000c030100303149041c0c1d4400700611060481580540402403242d03041c0340c216040c026181c90625042070041c0c1a607505840314800503007048801c65641d0440b07003d0700318120301010081032522044a00c45044034460b9540340d9012000300520054522914940c0c24400002c9085900d980c4c00045540d4503080341350 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 410621510 1250 410620260 410620271
    0xe0916150e0a052d0603040c060804060605090f07030e0105060a05120c030f010507021605060409050403030f11180105030609070809070e132904061104080609030918040305030a 78
    0x140d58903801e81e028542c0311035410030f08040007445056005076078542c2000110200c80c200c007481500d2100b07d0f801003a001080744184911400750280a030064064040022107030780b140c001c00c502403001e4480c02c6458032084200b0203480d5040c022070f0318400450009100500b0300300702154504c0502c0c02500e102e02d4210580d84e0703006104200102c0c110100604503030f00441d801040701c5c02418151107000060055910312030902c90000204002c0f6403020b00070600d400c2c40e0201020050001034401c600701a261400455a20081e0007159403c81d42851581d546119a080310b04014240600103414082c00f03104201131a90b030802003591111070350034a800c0c41d6a03010280390509075507030408807951402c0b0701400641c47d5018803d103290f91043c60f103000c917014543c846450074980c044040c0701d070034805400a400225540c01c06004081000c100314101038640000030309001c811a01d560b910b510110307071510586006d00c04a4003842d2800c560040c0d60a01e91801400c1d480020b000380b02140c2c485 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 410622760 1250 410621510 410621537
    0x12051c0e010b0402180f0303190f140c0106090621080a200f07060c1e03020705040606021b0d0b07050f16030c020907030b01050a0320040e091615 64
    0x20b40003018082c200800466039445600b41001e0031044101046000d411442c00c0c006041c00d001049850a940b040c60350241540000022a8166440700350202003280c80030342220845500d00103890f00c861a50004a012418000c02c0412195203070710441c0388984401070404030a01c88084910802d400c00003c540e0781d664280d042da8115035803d1720022141d940b25200b000f0450200c0d0400036050050261840755030707151b0044840d1601d8240240070383c8002c0d29178503120701421455610413407003030050b180c5e501e94501c0040d049400d298080390241e00030504100e00303045480f81040c0700c04800c888032407443d400354440c0e84030320b08001d1088042c00400103c0e000d91220607002d4a1000c10921030030518140c241c030f1300501c50304d82644200c1c059640000404c456600901030a241403006035652810b02450701402c078060705200318003190407502c007030a91488280a0004002600039030100144a040058000d864407150040601341150715450500c102488100c4115501c10340e89008201e00004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 410624010 1250 410622760 410622763
    0xe0105250803040f031101112a030f040806090106060c0b1306090c06080a05041106070215030703060314060105060703050f120a0b1201180305071e060912051c0e 71
    0x126a02501c201008400c02042180b5030000038100342c480d07940c0c400010071100e8842c0c08d81c0c2e082c203000d20010f43d091180c0000c0215103038003508111207404c1e190034140c1110420382c1c1554004a420118070b04001030600c0fa241c0108801d503080762405008002031072410740001d00d0011440070003400000f102000c1980c0c50f0031801c000060507003240c020003000103241781005121b2201d12525011880720750018100200d1031055500c507036017041400c511140e070a81044a1a800000c04980c440342c0c80d080b034102420740310003444c410589134400066842c290301f089042d03090701c625074002e29401100140b003140c030786005883d031f025403504156441d800782034001d181381e00070003030a0f0030b082c00b4680400c10b07400302c207030030440700110103454484020b881601000e003079626400e0840046201c20700c07100002481080144103130342c002e00b4552120004a1440030800003101f509039012a02c480602060210b250b03851010806181800351404034083c014400d8881307941300c0c1a045a03601d40302850741040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 410625260 1250 410624010 410624077
    0x5071703060a0815072604080d180f02090132040605040e010f0e0111070b040606080a0b0402010f05040509060f12030403140d050a02062d07050304120e0105 69
    0x140c02041d03e04c90346402c484541104001c5500b000010201c4014081041c0481060b41000540c007940d05000d41e00e984860040da4032925185032201d0391840b40840d00c1400e0440c0010f1144155041c090740725082c01002940710303040e00800700720401180458062900701030400c1d00e0a040016441031160f0480000d002492a507112581040c2003490540d40d43c14194068000c03074400510404c80a0360301100c003070888a8a0070701d00e4044904001c16004980c441c401c0b2940315114030300100325191100b000c01e050146404080b6040748041050004560f04a41a54040c582070f01e080c509044c904400a20700b050090310150159110720b102000350303103841e51404454500001220382c0e40f41c2c0e924042107280d404a1644040e4019918040140d07442401225014166580200111384482c40a40301a00821202000c101d4101c403250a40306000c0c54141e2089255484443d20f0385043d04100c0801004e201aa80411000d00100c45d100d03a003140a030b5440c0c0c03201050000804100360050402c444 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 410626510 1250 410625260 410625269
    0x603070e04030503061003020a0905010e060d0c020f1506011d130e0c0f09060114030a090c03030507030206061203030714090d0524010605043c080d05071703060a 71
    0x200840200802d0541100042d40130305c070b05403030b074007071300301040000b00c04a0040000c000300040d04c4d40c404214a6125400a83c410b107401043e2528200403c5e5480d0200c511118010001d83c1102016422480040c4400d54058241004201041c900003000070021040c040d82c00e000030380703d12080c48a9855410f5040f550810340c0b042082059529410107680d500070600d0188504c8003440380c05040e0415880d5503000700c0c01a16409006034210710212841e4000a004000980d620300410000c9481141d185004600980f14155903104509000b07090000051042f4000c45040d031010ba40502d0010489611155519020b28908900e03814810140f01d96000141d000001040403070604c48041018540c039540ca009600003c801d00d400b00f14085000d204450109201b40b100700100c0e000d404036518500442c080d17040186140700662030303020b003041c0810031459504010512449208204054841c0034904145040518075a60301000011340c0302122005100880461203e8035206085000381 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 410627760 1250 410626510 410626529
    0x30c0903061f050409080901031e061401090503010c090b181909050f01060f030b0f060327070e040f02030a051c08010608060d0f02010e0a2408060603070305060307 72
    0x30b042c9a001c0404100c2c040401c416400c5003a400082c15181600c80c52020301d80c0031403001c0c05c00b0302e094015401400d0040035002c0118810803141c05080d41c900c01c40020b003130143c000901c8100c034940010000520354100d18000d82c90070712002c1c1601d400040c010100d0341100c3e421a0740e59100400d07034801240e54030a04e604200300400103c1c40b58400540c000a0f120700820810132503840300702c903c00740320080c03040c107010541d40c0500d01040c511a4100c0304900401514100168014002040341d0781d20031582c01048190045540c43d1480c0032107012a41c402201004100e081e043c00700350f082c84107002d071005180c032511210b80811500e0606c01c40d161f4035004000d032104503181c4041d403035490080c0d82c82980014081c0002182e003c0c0030383c02c1640605006001450950410b655015020210010503030500000d1300e01125150740307a04468024211032218105041c00000705101c08580c07851030081071240071010041251940410303254030854601e4046aa0b03122440404c0c24000f1035040900907 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 410629010 1250 410627760 410627773
    0x150f1306050a030b041103010209011d01051207021e0c0f0111010b040501061e03060303080612070f0f06171e07030f0c1e020a08031b0c16060f09030503090402030c0903 74
    0xe11513401d0b281841a8040e21041c880c2d28160400c142c01c034030407141c149000c104d94541103412142510100400d02a042c10020314141001007620310f10001120040c0041c0d114102c0b640c0d81c0003100003280002d000340c10040981c0303161440001c4c41564514280e904001c1d0507855200344080035000f0307040540000d0000c0059585442e00100380030751803074002d804d01c01c480c0409151a0300c07030b02c11354040301d030940c1da040081c0d00c0e52410404d00d106e251091200a20400e03d0100d10140303809080002055000303031a100540c94500050311008071859804410b1003400c0412100c0a0861100400b80341d030700800c40f5255a44000550040a03055000f0250500e8016210505a00400000085810b0302011100709014840403641d035403046500406003d0141301080c60269818111a1442d4034912102c3c208101e4400c40b070303e04180c00381c040302c44225103c0204150380d00200301251100c01c606d0070408050964556275900d100386541c8500903980000003904185100b02590318800300141039900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 410630260 1250 410629010 410629013
    0x110301060e09011409040b130515010f0b03060a05060a02030c01020d0207020a0b03091506030c06070605010e060a0f0302010c080f070b010e13051507050408100203010e150f1306050a03 81
    0x520007000a1680a44511000450703140c00d402070a0310100001001d25025540d207507140810f6441c042d015204030303030710858010001801172024015498030780031440c110b5854902400804030440d40f18540ca084100144040d9031550002c00c000c1d1103041e00d95694030a6140001c81c95845145004071103548013164240201703420f80c000f00310359030007280d8106503182c41d44880c211501c0180c603106016405901c0c0140b4a41311000030540c01040141507407a00310114000c11402d03031003810700f220780603920300060241c41c3c0510601c94004000382e498115039070400c01800402071140c080039040c081c0c800440810030034040100c95123140c0e5850000d407100d1061801e041d4241003805508000308409000a00c1c410081703280070311f1310390000001d0050111041d00e844e907201002e0840001c001c810000400c41032804c201d401c9407922054001a81ca40c0342091800019201411400c10744428160b140c00701e65030074600450302001110791603000320b0600380303120090880750302c120303003101f02c0040000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 410631510 1250 410630260 410630267
    0x210c180218090c1b0309030109030507050d020c031509030405040e100e1603080f04030813080706090e0703051317040519052214160e04110a0309050111030106 70
    0x2010301e040051480c96a04070000c021200703504950080d0402c07030501c45804c2da08060708004100941c1c900560b460702443c0d501003030a5400b000002c2d004203000081100410030304108042501c4405c4c0702608250b143c290000e6180c801c18882148102011130200351303080c0c0f06004440041c600280100f007a00f0740c1041c01516801070300c000b5260f4030314142e200143c404010a00c00702c50361198102988907411f680c0c48401c02c2c0c00c01002540001414400480000c9600d3700511400d0882c00080d40018a400205490201180c00200400040c40002c1080540505003d40c1150a90038040b80b55980c25030305880b440701c2c1346805061002c034180390001e1142440e006105942040d209801c030500700041c6a8141141440b446810031500804109045c040c04105910a00f0840d000f05e4a2921440c0e60351030090142c034600b40e00d454017002074000d50b0300314210650901084c0e5080c82880c906c1810002c0c0750086240e4002807680320b401c440100306080d44004005a680350880c1c0e2603584a40005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 410632760 1250 410631510 410631517
    0x60c070c150e04051506030a0f09080f04080d030c122f0406020d0207080d0e0d080f090913030801030210022508160b0919150c020108060a210c1802 65
    0x550103103181c103020883c0d40c02c903110413201203074010b086d051a40d161192400011f0455400c0c00324201c0d0f03250f101d100000d1004009011b240c80703c4220589560420b00f619080402040a84082c140780041045455400c00c0c02e0703d0300240c004100184a400c264540691650400242c20b0301802240105404040d064041c0040d621140d08444000c4408801070703070b60361450701403422180e02540780d456840e0300c9040e00f46424a40507040e000d5209981d035600b0040c1d040f074a41c075064030f0b40c04252200d042c1803035081c0030792020214810415080385910f02611140041c0400390081c114140480d0040e402000000300854a691889170402c2d40c482daa5000e020481c00f070401d15002d00704222348582000480e4200303071010102e4640c90300400904102075503494175900c014030981e0300400924050189611102e241d910303100c0303500da20660310004012550080000d403165000540c14410705401d072803540b11451412010706500103440c01c0201c440340c40c540c000d2496000c0319003c1105602d00350043d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 410634010 1250 410632760 410632787
    0xf09080c160f050319080f0a0c020306160c0b10120309030512030402010504061107090608060f181b040e06040c030311071a090d150c20060c070c15 65
    0x100d281c1035158040c11000c03403418824103a055000001e07906403141d00020702444944036403030041c1750040c4000c0303590a640008a4000c0481c05503034011084d82800d0280302e9024080d00107051442004d410041d1850f64418070190041c83c0c100e001803005004080c00b4809842c0483c2868203690580c5401405001540401c6a0034080d030290042800070305401e0300e0040760305856180c1010700f400401c5030360b10005901c10815204802000034810b445109184c040c22203070b0007810301d51070503c84284c0c3c0c180c00a01150303691281035004055241c40072503100030b40960340362032003141c841d81070002b8060200303c80400f4035030240c88144010004202c0e4410304483c46502c40d9581c80e0f504402113a00c1c0c43d0f0302c0c8a2100c0f081240c0c003018010110b070078010415071000a0841100c130300300f038a81403080e100a58022140760b5845075842002600107003c50b01e2124a100d102d4101c2c41c01c44010303500d984002c2c0c050b058214020074400d0402c2102131400300034089000c4103c030070101410b030042030785810210 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 410635260 1250 410634010 410634043
    0xc09021e040501140d15060305070e03160909050a021206550e03030a111309090f080307050a08060609010804020f01090317030103030e0618040f09080c 67
    0x2034a1194015003081d00e0807524140c54150501c00c80480c401c855500c0b1103560340d81035507200040300000c17020344c902e103010f81125a4005040e01d450346001d40248104c0134071501c668080000f50b550004910a40c000769081c11001180300c490a00e0540d203440100c00000707600c612080c019014444000600d40c0c420301c568002005070b2000441e28074029802c0c0c02e0741c1c014081000304612111400c8c55100962902c2d489000c514940c0d402008c0c0c03085890b80009002030b41c000009210303080c4690702814403940c0f0304030301007443c04e00031500e9400307030b44580d12480318540d40b80c0c4000002c5c4001c861400d82480c0d00071076080d0f620b242444006050340d200d20800004038074000e000c00c95a0501009450345a041a1200c01c0141c80700e40800c85c541c200302c58454104600f0302d03800300000724101890010f0702ca4443da025107950440c034024003602c4400000c02d015082c01d0044420341c50400c01c80912404c01035070001140d008041080d000307031101700006807082100213159440c0240c0021400350710f244180 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 410636510 1250 410635260 410635297
    0xc010f02211f050d020d0210020d0807020309031005150d0f0213020408061824062e0c0c0b040e150a05010e130207020904050708010e010c0c1b030c0902 67
    0x440c41402942c900b403420b881c0700c024140c14441c42c103111860180322070008111140f0a015030b40003a12a8581d1010310006070000c4156010454001140a4012100340061402d05803c0740c040703a501c6002c0101181d81980300c0002c030300000303894540c00d0610b110141500c1c5000c24541807014032a0048d0714200e0007810002e00403001c1000300e00c00e40f01581c5a9002415458560758001d03082e052203000c441405002e901e8104008005142007045040d002c0e8040782c502c0d1408804000c0740098486040150102e80380301604460321002c41c040c0000d2090600305400d50381400c0c05075000103603421252084100040115401f040c2d0040301740f11383d9150308281503844444061104021040c4141800b140300038120903090301c2c016084285c0001015001810000c10703800082c07004c1c00c16a1b0594580e0403485091140f40d2081c02181e151851182c001e1010f04202c040042c40c4000d4404040c0862000d1041020010b460310401001150441000d0302c900d0b0b200c026000080d44000c0000c00c0035003809 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 410637760 1250 410636510 410636521
    0xd2303130602060a0504150504030e120c03120c06040f2f1c1101030f0f2d05040c031103011d01060501020d090f06030207140a030e0103050f0f01050103020c010f0221 73
    0x103024586c807440c0d002c40c000020011510132100604000340c402c809000101c1c45074007240e101c920400c00094501c20040c14402c0071082810300f00070170009081d4401104005490210324002076064006074040c000d108005280e0401045020101c2c18030807084804041d004509144c0001d0b42c840400200e44c601c0c2c1021000782860219800309030000d10482030b14500c408a90300a03030101209980040f40490b00e00740720011f43c0200c0f0300c02c1d40600a140001e407034403038040d030300c240c0d82841c101604c4104006a00341515a501901202c0c0700003000321580050103803203914290811000244c0d14200918031201e0000300318040e005034010301e8010701c50710421a000c0341c440d02c000422070f00d40e607803145602824114100c0c0079501c400380c2541d500103603041c6a1190042008003240c014040c1d41c4813a2801140b500050581b280030700100190b40303e02c0e0a01c8100030038800f10350304480c02401d0050f0355040450880303001d40311300d20014050503c04a0301d0040c840040006018804400344102000d640c2c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 410639010 1250 410637760 410637781
    0x80f0d09230a02031209030c0409050a03090509010e0c09010e030f010b03100212010b03090c06130f050405010b09130e0a0c18060b19020115060518010801050d230313060206 76
    0xb0640a0340c158007000560400c01805c030014801c1c054082c054600d8404040c001c01c0c10398490000032a10755100b90045014164041c030b01e0310151004541d100030551410300c000640c1240644100c181207030000704008182e00884180d042404007400755482e900c87d102c8082e0003002400c1840c1d0281c003440340242e003481da452084460200f0a15040c000d01d07400c00201400c107804c0201200c0c454445c0c10041d600a640d03070b001410074802d088031011110382c10400c000080501c0e40d4072090081e401d260040c40b04844080c15a800800181c0754140000d20940b40d42c1c016100c010001020341c02540301d02e500344410010000c054030700c0049a4098006044114030480d1200d100d100d141040a0012034408115400c50321814440c0b0320005c41c40d1503a55912104400e40e0741d00110104100180b5011140100c20040300c2c15402405c00180c00d614103408076580703406600006050b040b42c080200381030801086040e41001020003103d0b111840c40304860800354042c06011702501c030342070004540c07500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 410640260 1250 410639010 410639023
    0x120311060c0d05060607051c12091e0f1401021209070e0f0a0207061b02100b0f01030b03010f111b010e070e18100209040b0a030807080f0d0923 63
    0x9040c0c01180c90722140b15400790080c24003409940e4040010003140e00841d00800101540840f80d86441e1003035032217100d02400e024440350b4034000290920b00000c2c0032076040b02848041c00a10703004007a052480c0e181c40540c00100800003004c05958050b019042e500c154040c00e003800900012030084d80b1218501130f61681d0b03c0c405c00705581182e400144e8405818450650420004d400150806003207503542010755141d4980c04208070766444110030115410047c028003801425010171006445030301240b0700030768580303c07141410b03143d43c80c00b9140d40302540701000c20070300100d081103240940a01680c46501400300500d000001c030221501410042c40782c4803101807100c009045c80752501030642a0800010800411040c80d032403083e1603440140301c0406180740003840141e540b005001004101c0356160841402080c2441c011301c0001e00650465190342d800094141e101e8115200d1200c040c8030310704c0440d00c00d03070809089000f04128030103138540d0310201020b80e04c103840ca00000d00d99a0394 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 410641510 1250 410640260 410640271
    0x203060601110f0f01050415140c13090e0a0308090f0304120303140f06040e030c0c1c020307090525170603160308070c0e09100506040207060612031106 67
    0x200144082003440d8041e40803150420520070941c1d614520149815040c41030329800640c2c0c5945410400041080499100c080e41c14403400c01c10468180103041040200300802d451031034a03000031043e6543c0c20861020f030081120400074400b074202201015250845150110041044480414024800031510002c030b000e0b41d01c021402c2a1903c030300b00900c0c11001c0f030180c0078113566a031741003051524a04800d1003030b039000b00280c1990604106010071210300f0080d001c0950000e0144840101010400c2d0450034801c807001c0710042c801902124140d080304c0d00003903040c03088500c000303040c00c00c43e08401c1c0319202d16007019016101c440449982c07032000c001d150303000072800c14068178131001c001503450b04900003a044072201208000d54000d14580382c1c00c10342d00c0500114090b000c110210508034080e1038101e280c150300341400340002e0b641d200c0007420340e070802d61140b0001c1c1040d20340360b0540740007a402c0503007800810350741d6400c1820180f40d410f059000030640009419004e0000036283c0c041c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 410642760 1250 410641510 410641513
    0x10f0b0616030806010c0b07030c02121303080304231014060f0405130602040b09130c021903050d110d050907050f06070c03020306040812130f080901050c0706020601210203 76
    0x2010140c2c2c0455030590010106814811603600000101c0c10540d101845424152000102c03218807510192800c2c001d0000c4031115001003006020300c0d44103030360460840394003140042d200d44407841d0880c2c0440401860304140c40e4440d8202103040c0000407900d1904d42e286e4400c114002907001200341040b000c0311a26003150510083c5411824254040c81d40040c400c441e1040c100c05540c0c41c0030990307000d41e100c86115440400d20315118502a10305d0039102c4000749040042c01450b500294641c1d8800c2503000c84840e00043d00000d150151003118041000311008000c400000466808c080e0030421840054900d000001041c142c1d00085003810f44600034044810303010b60130b0401003603900c185011203018052420000048c2c03410003410340210b06c910082920391a441218041008008000f2001d003003071a01e40b500444c0d00f040760075034001d4001c121103039240034488c0180c03060f2050b8480f001c260300c135142c0b00040440d030108105060314136580000c0341c80c030175982d05000c40100d50800a0740c0b6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 410644010 1250 410642760 410642797
    0x702030309060f040813030309140a0e0c070c03120206010603050a1a040c0504050d0606080d020d05070305032502010603050106050609031b15030a060810140f150a030302010f0b06 79
    0x8039034561406500070321807070303202d0b103495540b00204a103010640e10071230200f00c990350306120f02ca044103401100e044042e40c0742e882e20343c9000e020096404000e00003944445000400106101c0c040101c4c4001c0c0d504180380c1c0e078868840b0000290307504400d200c4d81000901c2c00c004908031240394040d0a04241415000c407640340381d0042003000620100c4940b070107120301000002015200d0018158010780140d0000512a01d006d00c083d05214490100208540241010881854000064583d1290103190607a100d540f03124146460460b00703080c2d84007003000d580d460411164150020020780c2d202c4e400034082196140288445401104105030741a006403070300803d142c140302c03080c0011030b100034020800001603540000681d0300698140007155169001440100c6042015100c1c141410f0002c0002100d1215600c09144003e0840f0b075109051002042c581920403951400320100207103c040c1090350b030b14002e802481c20700c9607038400504090340c2d0801c0e4541035099840c01c85000590644 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 410645260 1250 410644010 410644021
    0x60b0d29130210120c02240601091413090506070201061703040605030406060509070c050c0108010605040e0a0e031602010815010927090804180b0a1802120f060108070203030906 78
    0x40c2c1d400151a01030030001c2d940132549800c0424001c81030920000c0e0090450389508052a1000200c02d0521a1150f20b105060010326640003443c507040b2004080255880300424000500307200680c003140d28014109001c41081c414045011801240150000c120702a5070b84040f00e04000d80c4400b2041642051104000250096000715441445110005a41900d40d00003941c20001511a18001450f060901041210422009601908c2420926003a40c034100c0018081e00c241d0081c1c4a080740c0c00d41c081000803035980c000c1c0c000c2c240c1d0070040ea51226a100245544558000e1042c0d00080803100800c0131440311500b030308101401a074924030420b08000d0841c18020030990030f03017002c0c103175980c40400704903451103480002840380d0801561940b0700040417a00e0305800b1001240103181190710a40380e51031091510441d11014004d109544c0c031000f54900a0150710341c03072030f8183c030b4402c10042a180804440d901c151800d0701c032402280c45815040341e50303000442d94001e590340008003140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 410646510 1250 410645260 410645269
    0x506040603270308042003030301030213090b2a0304050318030a050f010c09080c010e040c0302040b16020a1d0703091719090b0a1407060b0d291302 65
    0x490702c984425044002000101448044842c400d050303000961074420300080101c62121080800c120b074856a01c480014400240c49102c188002441f6860103100303500e4100e09500f0686e05260010788030300e43c40c41c04002e00e80085201c406d010041b401680d01e20349421046100b80c0c0c2c00303680c00c40020b5040c040c002c001c10040c40e040825007075051081c41c481d040094020448000c1f220841c200203c0c00c02e032000c07009001000e042d002030704141c105004180442e40e1082074440c05034000c07a4040f580d289060310681c028450780d00645d81d01c001c0069549023952889850081e158420f41751414066520040d944402c444e2901040700c44040601080c070440c425000720302030720301540400b28009160f441b44d442c168030110301e070070000d0348111102c01c03070700d8000c4005030051802d04440340c981302c41c6020041901d009240e00011004003c69904180002c1b81d024841140000d8051260b00c806820b001034151051080c42a080890010b0f6420144041c100c02d0301685990018040c0c8481315401c10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 410647760 1250 410646510 410646521
    0x81e120c070b19020610120213200909060a0f03140319020a020a06050f041703040503151506070809041808030a0608060c040303080106121808090f0a0506040603 71
    0x2a4054400c1c007001003032440d50800201449507a19140503000850800080d050000081000e006021900020014114141b8900080a40c110390302410b554820f030f608001003010841050540c3c600900c02c0c032040c801c060085c03403071400c00c03100904c86a80703a40c200200340b8600e0140d0400303203049900410014407001404c100f80b103100d00c1520f0504458009125044010008020043c4d001900c0e49080d030600301c0015000c2c203402c0c0340030740c500440b4040030751803489144140c00c20303490700c0490911031420500c10348000d484010142c5085003100c0900008000040e9003000481465400b01072151511800b2542525404540c003401e0003001d00400008000d403031078175003a90503680087d01c00076801c40d0046205140303402c000600c803411310040503c0e00c0001000820300200170070040c400b084d08114524111074091070000c11201500c1c1d07100000e00305054560340b01b21441c2242c3c2d41005628400717805030200548100b5007240581c810008402000c1c45681d401c80e40800c0140b203c0c42c82500403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 410649010 1250 410647760 410647777
    0x60a0c050a061104092003070c050705090a150b160f060b0916020d020c0a03140a0c15030b010216030b0621010603140d080c0307031e06081e12 63
    0x2900e407140d003152103074000e07500c520509180c6958005414800329000348200c5100717181710f20b1881c668460314404018148405444003091004040c2c5c801e041080c1003080300c0140c01c001d07001d0406400c040c220071000e00f00390a0400066403c0706401710700944141c054619120425032550009007542d1140c100c0ca8032480c1c02920b500da16254000015201d50200d140540d4220030000103a151038240242800b440d510024119040100c41540c266604010001520b400814820703040c111691030910b000c00c80d0b4001005070b9800040001c0040c003510320384511805a8409110340c0380756200482e110b8044114500ac0b81c00203070010b01c00302d0170f2100125480fa00113007000708210008200102c8a89031000f01da1080d82d140c0c0400c0c000c00a6a600341d080030248240249011001d4480181143d20014034400c201c070400b200080507070b44070750050601034140c03101000d8401020512480509502d0047c00110700c11600c0c1e03031584c0d54031240c00e94141d81c5010007030000c190b52030074121601d6010f0010b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 410650260 1250 410649010 410649013
    0x40b0c04090c020a020f010f08040605101701020310050901061d0609150405132003150607110a0e150d060b04020c0709060902030705030609070c0c060905011805060a0c05 75
    0x480c011185115046010b202ea40080c0741004480c8100711030800181c4600703041140048085e0400b83d0000c0300e0a8005030702c200d0120700e6a849080030580c541e030a51192261400c105410100c103070381980258001d503154a20384640a85a90900c1807108080c0304600c0018081c503003007191407103021420f4100c0e120050820345401c1c000400646658840010b000000d90300003400c01c803a10304141030304d4500c04101424400006c0f450100d5050210741d4200080c04600040080c68260102354490743d42c12008201a0300d0b12014101400c100c2007003881540190403281d0046003e18424904d50b100d444d8050060b0908540e20050103c00e682840c000c40b000e41d1241103076641a42e0728000703030024480c0ca0b0010030b2064500340c12402540d807030b6400941810b10400c00e1100d1581d0000072290b1100701943c94080030b03241d43c102200c070810301d080080c0040c0c5000101181c0c8617403080c8000304a80090381c07140f08041310b45568a880d040d20380320b4070b0b0303110104100d01112a40100c3d902d00c64280103c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 410651510 1250 410650260 410650267
    0x301504080904150e0a020a0201051b0403031101021e040801050f04020a1403190302010506031204050109260708240f0103020111030c06010e070f1112160f050a0209160206040b0c 78
    0x21214013a1075820350f400c00384250003094500c1c40540c24440d03541d00030043c03c0d0b0007a001c0c110304405004e40c03046000107003c0203100201201900000d40407a0400d8829007810042184c2c0180c4c4107585820901580c1c101e5424580412055001d4402c0c10340241c1c3c004044112540c40c1032102194601403808240d018004c13041c1d0000922100c1e0b071110b2106000760001f0440d498003008141c00c1540145441001c04418042400144d07807042094080d1400c56903030341e851900720b12285040001c505107540f25449441000b0584a0f80403800740904035240300e140000698580034441c804d50200c609105080380e40c001000558803900b02d0305010042075050342c1c900711000c0480f504000098110840e05105841440142c0ea03000701b010754000b0081c5842410402d0f5001c1c11511030b800c1c4103413800700042c0451000182510b94003801040caa00c0345903081c0d8110303e0701e040fa84a00d080d02e011382c4103c10303201c0050300380c01c5c03e0005540d03121000c0d0b010b00b0842c0c5c1c036580c80d10080c99000d0074007a4a4101070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 410652760 1250 410651510 410651519
    0x10e1c17070302070e0c0a0e0d06240605090f0402160804090911101d010e0415140303030108030406030e0a020a08030712050f0706090230150408090415 67
    0x44051a000304031004180c0c0c0c0c40c40da0801920780313181c80c0e00400c180c640703590030450301c03a503101d003a030f4651045803030075800d0395482038001200400500005480180f414028940340480b1a4102c482940154801d0f000c031552000c00782e0303040c0110016950001d143d030000c4445450b00c2d500800100751003000c0090302c0d10340394603040c0461300160400315102d0780e070b880d28000344a20b09240c6103103014120384901260350110002059001d00d6903400c1022100b1012008441e8003901e954428064098810031080700003c1e8124035a410510485518004652580c103031400c3c048200d905803060381c0c004524151400104400410300310304490924013400d900500140e135004201001010004029519403425040079095104403250302001c3c0074042240c145d1042122060b41c82054210100052503410350011550740721005580c4d07a62156944c810001220320003240c0c402680c2d410044070a074240a1680b2101c1c4281943d014007a84010700c4407603150710b00b0360044039070450742101407000c01d581d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 410654010 1250 410652760 410652773
    0xe0a0204050a061208040602010509030a0c030e0d061a010912030c030503041406010b0d1a0f01050c100606020601060f080f0112020d020d050607020d03090f08070816080702010e01020c010e1c 84
    0xba50445d5041070000d01005000e50900800340c000881c44040c600d1700f12081000380c40050360b607400409009000c1203402d01592444206009541c0210b4207100440c101d0007003c44098407202c2d26404a00c0d0084007041408401080003401989a2541703030691095071000e0b50f0f146c100500032103d402d1002022a02d150b418440c0703d000340b06540302581c507204031200319030a891140790319194000c81c00c007e40c503155940c110303801e4900708282440c6030390700500d01c400f80c14100c01d1920760000354281070000944560010315141201c0301ca03030782c024000308201e02c21590184151141c1180c200c0d000c00600982194003940030429100510b2200d00056a9000c5103e110455034199070079001001003103e101d406100c3c0c09043e00d00c5203020004882640d660004005880b0005811810b001c80d410081003900d000311032a03080340b030640c14803210403864591a5603010000490025070390310003608844d400001c1b03802403444141c40f0001000e0b0381c8414403a2001010b050303150211101002c21021521 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 410655260 1250 410654010 410654039
    0x103030810030c08010615081312030f06030f02030d050a0e060d0605030f0a031b05060c0c0c18040201180e060111120a031a0105120a0c170c03090c03010e0a0204050a06 74
    0x813080004100c5914200c01210352181b00b0442206001450302045078540d00440c0140d0000d512503a110382d0001c40c014220000c015800d81c442c121450100040180803607aa21034071118400c400702c440604880300c0c2140c0a02505581c800885e00d41801d040007490304074040c0004510840c000a1100d81c0c8600092400b00b014810b19426008050031500703040e40410307140c0c0c112104e4540021501e059a492540d0345000900380e1482c00b0011500440401c42170048030715109004041d0010790380350b42005503c0d154140c42c124040703010182011a04c001c0340d01090200c9a0507200d224140e50b88500644803420b0001c0501100e0007200200004414000068802c10178a590001104403507401001510031861034103906200c0e09110062070301510302001c5520030039902e0081030071400600b0661301e003410348040701d05181d80364080141d40540c20016610450600302250001d642c00c100345030898030300d00942c4599800c40d07a605005804c1039042260880645000054415030b01c81d2400c10444 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 410656510 1250 410655260 410655269
    0x3130f0807060c091a040504050408090a06050c0d030c0e010f17100611060f190b030d0f1205090c010f050c1015080c0616060b190501170f0103030810030c 68
    0x2030369401c403540f030140e0081021000d8110480d0710541030f6048070125005004d140304403445075440b140094200001070042d10032005000d004542d03001d480d020f014003d600120000303c0d661254000c000038891290041c05000b41260b10f841001c01091001154030000c04c1203500300b0b0147d8002c81c0320002c503a40c0c002e54031641c030280b140440b640c140600200080c0e40d00c070015415a20480520002546900c00c898100382d0300840d103104004241031000150815806242d4180110340300c620040e5004100c3c00d44c90481640e1f80c841542d20404e400b821180240c1d00045294442000c0c0c1800354001c030b440040e00c05250400c01e0a04031028815440c01c400710b0540f00740c02c1d44070b05503540c0f03941180300b14030701030710181c4e010388020004c860115141c0e01440d000c21000c0c1d45460048010b00403158000d40c12044080c10303940c40c69042c801c1196603244248034040c0001c1d554184107a030748402e013807a180955849040000c1c90303481c640341100e180d2405846003c10610800c1c0000c001000b0b41400c600a2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 410657760 1250 410656510 410656523
    0x120e0d020901171005010e0c0c100504030c030324030303110d060b0a021e0604032105100f060f080a02130e1e071e08042603040c08030a0503130f0807 66
    0x50145961141448140e0306256030850502005001f048428001d0603884070400b4101c64940031a440070501e4121500b0002c4030a92510b0b0034802815801901c0c2c140300ca00a0b10f00340010610100c5041e03071640c2420f40540840c0c5407c20500000e8804d070080c0f00c011203141c1c0710608014031118604116002a80490303448180000c5001202d03405118941c40c45240c0d48840c02201b00002c501c580307611740200010104413040f48901860300007480c2420b90303a0a03c0780c080005140c41610108c640d0300c0e50150042c2100b26540000b4804d208a504042143c29a541d60602d40c944000e0300029400003500308601203c450804510010340b13100c03007403292903068a62022080000c2c01c800c58090054a620700b00004161144540303131030a103500008403885c4c030f0a540c540e5204d042400301d1404480041c02101c03045c03101725250ba071090f40078500650044a4401701c580d501c605e917641d00d20070b5a0070741303010a0083c03001072800d0316410f101100c60b5002c0d003900810b500c41d664540d0308940c0854000c80e80b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 410659010 1250 410657760 410657789
    0x915050301050610090b090d080c060403020c19030201030b03190f1103010b0d03051803011b021b0f060d1103040b070e091017120d020a1209120e0d020901 68
    0x185401d004083e0403010075614540d8800b80004002c02842542c021104c0000c40000c00d1520f60f00c45a9003500301503000381030b8036100c80d007600045803904400da400b5030040c45030034501080c9140c01e00f80714010340380ca40d0344480390030f103507034015000382c0001d0781c1d219814007800580c65401c00c03a06001d060681c3c800c044071502041039140100c40d5140c144038441c0030703071b00d002644012500c0d1f420040c4400c6805080154440041aa21100f4019032082d1241c041d424031800c2e00788046090a4145001c000307800307035184643c41200c1c1c0c041031502c010388a94042c00211161401d42801d0000300000550440d021402003250010802140e00036201160200009020040803a50101002d81805c4c001c07603148009080000c005814500d82c0d020364000482c1d481400e40044808000c0b41650540c0c070b9407078640b01c41541c140300000790800860880403615410445011040320f01c1004140c0c0da00c02c2da03001c209403010398203d4034134134a02103494000d1560360601c0c001d40d0382d01805a008025400d008403c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 410660260 1250 410659010 410659019
    0xd020309120f150402130606200303060622030b0f0618160e040e070e100501020607121e0f0903121a0f0319030305010510050c0a02010e01090915 64
    0x40c0318040d44986070540c00820720070058001c00308400500081650780000d294a40e80001406984101c0c0050000c1e803038080700080e050f400c5100e84111000301200c03010008218110719449201c1259603943c014030400c9031112800d1180f91811040e904000501015a00c2e5a2072103a0020190707141400d600c5898104409403818100b01107481080b004010150b060086104001c1d4419002076810b00a0020703500ca92170b161035014802c520110806c49050960720303503000c1030060080d981c401c511541c066021440d5400003603041d01546890703540007102c00030040c0300d90007010011407181000000d20f100240340718841c01001e0b40808814000212255249030150948030b2210071848001d0818005505c074040080d180c0c4e40c00c08040c1c039095100c185540000c6c1c00e000b10740107a150481c903504c10500030300d82d1652225050b030b001a94010300c098100101590380d806501c0c1c1d040e64941c445030450005500c03031010003040c0d40043c1000ca82d0680c80340f038031106503441d0900098a000020b0b20801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 410661510 1250 410660260 410660269
    0xc080c0307050a06020303181908091e09190f05010305010209040e1f0203090a05060906042a060e0307050406090905060609010506070311120706230702061909050d020309 75
    0x40105401c0360b07825011444c0100107500c03400002d10801c28005220313807090602009000607440048400081d081c5400145000d11a03504414410740c001c0e0f5071100d1120754080001c4410009400044c14800760b50740300c201028100a000e0b0030003040d240c850030034100b03001d043e000f000c1c00b07184100009603c501d00c8200748801c4640c0035000086035807000b800340c00034100700b681c0340000141622001d41c1c0c0e0754800303410914284141000602c1840b4610800c80035940204243d80500c0c0300725042c40e0041c901200307949521242c0c1030101e620b90420ba90402426002d60301d40c005901c0e0103003d0341c2c841a1f50304001000c58240b44c1c00707146821f031542e01c0001008010b0010303d900103030449520030f180d41803002050050241c1c03440202481455840c8003a500d400b0031207000c41090100103681c0e00d007035038030b40500079160400c440b6079503400b41100e0084407491100c0031480f80c1956030003401a0780c0d651071051402c00c41481c0b00301105a03110255130110b00705001d9082c1200180c2c0007140c0d659501018032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 410662760 1250 410661510 410661523
    0x2190503090d140a030f02090603130212210d090203060f0118051302010804020612011202040b0d03021518100605120a0c0b07080d2c03040302011413030c080c03 71
    0x81c0030020207001c1580c00f6070912042e90741001841c03a0018803216200c002600a2180e4511140e0101000c4200464002c0c410f003001c05071352081d102111032a08007010641c1d28010301d800380e22031000813500d940c60108040c0c05032a00d060042000b01d0780741c032950003207400e207a8265940030900969400602581c1c98500b00d80c00c0d81494440100220f01e00111100c4410082000003810880b0000c00318055540d4481038500e034240108880d0010f59543e0f078500700800362844204c0c0507c0c14140540c40c01d00d040c030a00e070603141c1c050700600b01114066498010080004102c1c07101c41d000032958070b80f1144100301080005038421400564142800100096508a5043c042c45079002200b00b00006841780614030071203132260a09511030550f0319001c01980144401c9940d01441c1900341304200348810800c521000031062503281880050b0faa02e81c49102d0703408041d01207540c9201070301840484100030104000810300b07410100d0b40700e82d035025507042c03e0351000c9096030151a940380c2c60324060089 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 410664010 1250 410662760 410662783
    0x4051e0904120815060405060d0b060313120806090a050402130e0f010b031c0f050f120f06120d05030a0b0a2d03030e0f0310230a0c0e10030219050309 66
    0x44d10018001c000c0003030094440ea01031b03030340691004281c0101041580d042900000c50040000d510703894600c9010081c500b0b011816038041e036a03191305030252405000340c1c034041d01d0050f1000b0310981d181e2000c80d001d401c0c09881260403565074140007090300e1451240602c80180350000e0406150460038090a40c3d01c0040c15030b01c81d811032108103600342201059070f2486241401c003000400744110301030f83c8034055007100040048000580250700c407000e10340c0a100d000148000f400e6034540c40103006c103160421001051550100c504201c016014801540c0e00c40f4410b0000300e00241035001054209400da4060750030382c181c00f2030105e030141c0d00340000d40e8180100c00007a01c20034a5924010480c503030015203980216507a090305940307610244650040c500c1001c00a20007039520b1645010070300d60310300f213104600b40000c0c0842c0c4250000c0c0100c0c030f4410a140c2e40c105404d11442c040169101035140c64005145e0708020010080000c07140882891030710b0b40740c0b03070b4481c60540003103402e0140d800e07007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 410665260 1250 410664010 410664031
    0x50409140609071206150f080708013c0e0405120f09041e0e030307030605010203040302061905040f030b01060e040c0807080c250203010b1504051e09041208 69
    0x100409516100301c00c5501003d00e00d8581a8019150700090081c07569402150002426901d101000c6801484804e00803a481e80c95482c2c1d40d40b61082102c0700c840a01a200c60072001e0f0707071101002050959420780e10303902a00c0d0f800300a410001c804458030b140da408082a44001c2d01000300344030f001d101d0700394801c450401052402101c940301c602c00d0b10030361005601c250343e1034030341c1041e01000144410000c0b01a030340400c892010408015502c3c2c108858210001381040400f01c0c05507c040180c0c0e00306c950182c84a8240a80c048043c00e0900d20000b840c1d08010b4184000141d804010214000460040303454400650501030001e024010701182a800340b030424607180b030180e5200704916405a00c40c03070309484a0715040100012485100c03104901002030a203c1802c01010304a00e140b418402c80c000c015240820043c8285031203880d40200380804244010811400c00c107840804a451640740c00d20030381204800140e00300010b65054a000c15a44a4501416040032206411809844 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 410666510 1250 410665260 410665301
    0x60a0905010e0d05161403130503010c14040306050703021611010f1b0b06030f030703030b0307060c0308151f08040c091b0c080408060f0a1a090a0209011e050409 71
    0x7240a800c174800e541001ca10080011514000c1c0080003810821814400f001d40390b581d00001b280303400c0c0d00c90b207009092080d46444034003201d9502441581c52600301c6a1281410310340b540d103600c801810020007010605400708140c0703944132801d46000c46130b00d10486014001011403800105803e0721a02c408052114200003e2a1205000c1e0340741c0306280e100c80c00d480c165484002090800074207119502321880041981c004146c0c140c1c0003c09013070750035022201c1d955a200c1084805510032000540842e2102000c00c0e232202d060b01041c800940c0107417030384000c0380600680c084c08403960020b03030f000100114248410440c0000c840c00080100c1f1000344070384a54001717841d48483c4480302c100c00744061000c04004015040055400501502d001c1c2e41c0316150400740a824001e0865803441d04900d4108842d80145403001160740130f10024005954540e00c0705807120003036208903c180e0501c1100450741d074900c480e80c0380c0a4520092562a25200c620308406c0806071a0400c01c4009e1558000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 410667760 1250 410666510 410666533
    0x9060a1401050f1c0206040807050102061303171b03040303050601120e06060607030c0f0503040314160e1905070f031503020303070303020f04080f2a0a09150503060a0905010e 77
    0x800c00c000a403004854410340720039030004d1188140b00542e4000e4203d2400b14000808900210301c600c1110000e030251010307076651006001c0250007941c80100071900300144ac507501d000c00c5200d26803240301070354840840c8003040040111a0011102200000d4403142006082d503480241d00944d0746403004140004501c80c10100d0319204000c185900030031001c0303590340034184101c21841500760080003103410044c01d401c10701e88962241c0416128400c640381ca00c1081200000d0762400101001060009181014014a000e0030082c01d07542c5a050140c2c1d0003041c0c100c8600c94940594200d840c0c00c40c07500041c9402405540101e03505d654a400034000030405a1400310486400f142d05180060f501c40d15040c00300024055a0412112486881e40307800602c0800210784e03558000303420094101c01c140510025040c2d07095071100341c0045851904201105071508104010201c134400f0086654503180880d1400ba011907000400c42d0302d41c00c180052080c02e202d02c0040b0900903000e0000d12011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 410669010 1250 410667760 410667769
    0x1621020d080a020d090804080c0f0d0b010506030402120d0201091202010c08010b03040f0f0506040308060d0f1b050d03120e0708060103030f021501091506020c010c08071a09060a140105 81
    0x42c11030314580e40000d064500401c00c3c0c0d002107043c0f580110482c0d2600d485845050b80da02440c2c0c0784174000c0090b9800c0000c203140200010044980c04507404469a0070b003000d200441d04041c2c02240c0052000c096246489418003070942041c1095000245c00c1e0005d040c541044c2c40f00300741b62015645003030100e52006500c01040e9041d1605100c0041d40c0fa1241c3c030742603090700e0f4011000340c050b02c01d001080d000c101010070520300030723030080c0d03203d40c1541c542d101003040e400c225100c02031200b84000d112030300143d64145005031180e21b040810606580d80c60105004015440b42240010105540501d844005204066200101d07500070140785040c410a1742e03503144180009000c0c00704e00700d50b00018070710070031254000e01d150010400165035113008401c00340400f02a1200b2052440002040091000034041a400e50580d51444030110a403582d49807540040000d640070a901400c140c1081c407148000381c0220191001484646816807108003194049080f0038122190b031f00040101c0e46e00e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 410670260 1250 410669010 410669027
    0x308220201030905160e1602010204060801051011030c100f050609040308040c230414060a060311090612040212010c092c01091a010e0619051621020d 66
    0x40c2800c00248010f00750070000c0c0b4010484064000380d000c903440110342c40d82c000403010f029458150303818401804001c020703030a078010760082c00000349820300108458039040f4507449801c081403c0031b048189000c1e4001341035034058070394900303590310402480c07050461610802e01041e144010410050030144001002d480014102400300014900031a05002807501d44500815140401e40e01d07068034210642c3c40ba14081c00901c1c4124503250f0a06400005e1004440c4603001c000c0244403040e042103020b6005081c241d600e20f059450034803022a0503140d6400800721925981224007241c075140c410024a074252a404404a03418001d51a11460304249403000352a4406014406100403201d03080300030500008070140035814900000e80060503910245203040e00c40ca101c52132905420040d01d081d03001480c91a00640d0400441594400617842921601107130f00c0c003180780500d102401000e260300044281d998500c011080e20032200311071103104681d00d050000d8011012500c401030305165 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 410671510 1250 410670260 410670263
    0xd110c0d17070f021009030221120106050c07030204020304150608030403050714040b040515271314030406030203090106060c0506062107060504090c030209030318030c0d0609030822 80
    0x303400c0d0b03c0040c90091100381c0000e6503040b41080440c1032400c0007543c80d1036080a4a6024140784401c0c07400d0104c040454850b041501100203840e4a40402100d1b0b95104520302d0140e40607103640400182c0d281d000450082d40180c424018000c49403000c201120301c0303940482c09641c0200001c200003440414104211070342d22a640e1010204500071402030080c0c0c031001e43d4030601d0441000381650310340c0c10003180036209071104031044d8804100c00d045074100c43c0722480810070910020310340d1840d5015621110307208104011555900200051540d0400c0c0c100c0001720341c01004100303480800348036060082005140810745081a0745400e900d418000c1c040500881140e84810300f01c2e10068142e03c020300602045a428035603985000700160801d001c0c3d1080242011090080507200e4001d44000150060103136107007040c2c000350212000c00a100454240c041c00e40300c00340941d80d5180b84022940100804a2155400c0c90004d041c140018022050303603d00400d015001440043e0840381036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 410672760 1250 410671510 410671517
    0x2010f03050402240309120a17090a0501020307020d02100b0913061b020c01020c0a03050c0d140a03030207140607050f0d02091e1507050d05030604020d110c0d1707 72
    0x40d162400854144c030f000d510100094442914080d0b148410320008500c2000d01c0c0e8280d030031011500d400310840d4070411801d040011501038200340d2a17030242c8156500b0246020881d0054000c035543c20707003a41c000300e81030700241e081140c4000c0480c0e010301803110320f542040302c00c200d00c420000008240100c0078080c10102d1900c5c2d480c0c4000c001013548a00085008081b50640c454203885000359206100200c00f8014056a40782807450309001c01004156540b1030060010b400340b8200b480407083e18080d050350304428002d12080118800d00080480794000d039000b6940d06042c2c206020307245100c0b055281c0c1c0d81e1180c01040403160f40b142c06d40742c5911a0780c002540da203481140c2e8001902902aa4541c445108446205e18082d8045811004442583d540003620046103210317090740201070300600650407000d1048219031003003005680c0240c0050005051803021103817981100c4018086c540e08400006d204034180704204811850074920b4540a104503035424030f060341d40c040140c03000003803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 410674010 1250 410672760 410672771
    0x1502010903051c021b03090f0607020310110d0c09170c09010614040302041802090c04180c0306180c030f020901020712060914160b0c03070201080402010e0a2d0302010f03 75
    0x401c1c8561301202c1c994030005180c603c041e420755a06607101e5211102e418032942040300c1c1c881003070810740c1c00d80f040c03113800401910b55034041e4242c20317019100c890300310700401d9010170150f00c0c4401c80744a03c0b0460007580d9244d0040038204128162030341041c10b0720800591020308201c589944807110181551500d01e4104204c1d0068081c0c0c00050140c4d820003503115051110a5511003a6a285294500e0080320307422030a4803003082884d0305200b54040d01d591800000d40071280d505003034100c03008802c070074580064541d41e82d03400095085140350904000c0343d22105c2400e40e0603418090080364901c0640c04500c2c2014010020359542d600c0e00c5080015400c110442c400d00c40160b01682544e42c002642540f401010076995072038490f48800a1000c100c2400c0c041904568907040d5403a11800718001e6281ca09250010344542c50000d10480c100040d030b59003483e140d00d034030401000605100700105035004040481c2c100d18803c60011032400c030000501000541c0c1d020115000201c0641070009a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 410675260 1250 410674010 410674057
    0x1201060801060816050a0b0a030e030403020604080a050c31020c0303010b04060f050406081f180c090e06150a0e03190302010f0905072606010f150201090305 69
    0x14114960100d8200e528118002408603c040340702d0305000e110002c00c807140ca031244104604402c46e40105401c010060003e0f18904e4003e074420310b042c0405604903410720307540750300080c0c1541c0981c00180060300508034190402004020f1742c2d4080e03030202d81740d900c041118001d005c1d9804200083d640a101c1c119200c4201e041154112401c410711001540d90b25030f1031f400b030100f40340c0c803610403d80018403140304050210302c19815074094401d107965042280e21840c4d120090f0900104825804a8950500113a038040442c015180108000d102068251441c2e101074030380712a6a0207280e044010304100115071307403000b0000001c0c0741d21000c020f03100d039030402c0120f55552030316503143e4042c03165003103480d003d420950211a00f94402d9009020a5041c0b00581c81a590354000041c0349600510b0148070003400f20702e0702059087c0c1d00c104240d80c000d030b80d2801480c050081e48070b0788400c985000700b84801840700310100100e5800d0f0000b031201c0380683d50001c00340d02c41c03c540b019001004005010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 410676510 1250 410675260 410675263
    0xe0a0807060810060504420e0f03060f0f09190503040905090d2309180f010503060405060708060a03060f0f050907080604020607020d020d060507030506010504120212 73
    0x24141680440e0300258071000041c0600c0010303034007045001c40e071410000315548550201d50076642c043c0f1910143e4440d48491101c1460000107850b14804034090040024503543d000040b141c00c00c0d540ca0203139a454030180702d4195841c0c507955005e07030821410807141240c508803954201540150480344c80d543c00e10f0301410507500d2840000c02e07111410b510b800703204001000d4000c0d106400700800c00f9442c0d0480b015034503c81c482e00c0354081240c40441c50b4110340207000383c00e07920544031110361601c5000301c00903c5641d60742954082c2e000c079a209100ca08001e101801d07000d82001e0f0f00922550038651140355450400810b03500c1040b2520b000107005841c0d40d144038006550155003804105012045d46028000c030000c03003140c2900d89000a414104c00081010031a0720143c050070558945409000040e03005843c2640c01c00b606039a00d074010707240d480d900c0c00100d0041d040021141451407000382511000b811440c10400148010700078100840d108403100d40e8125884ca100000000095 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 410677760 1250 410676510 410676529
    0x180102040803070809010905040504260c0307050318040504260d0f0911010f0f14091503220b070c0302010f0203130506061021061203030b180609070e 66
    0x740c0042c0000f084590070000604003030001050241c0780e800c410b640f14005d00003125404c96000d0038656801820074069034080e001701d1b40d840c40d000121032030701101c490300602e964080c040494490f800050064400801c0034194244842d0403541407203642000d48a8003e103041d080940c14001a09055015001187c20221025040b600c541440f400c214024000020541c03018240c4820400d03c101e210958406c5034890700491564a441172203a060a000300c90740c8004c000c4d08011010200600303101566408400340840c2445241c05070b9900e00a0f0821041144020902015130301101e0b484000076211400150f0210a62074080510442801c0c103d0151032010014403109200009000385400c80030042d003007050241048402d03a4603807400784644140c0c94030b4104000703010804400c021140c007240401e0380d002801000b092154550300c0016080b01d1101049011981e035411400032400c000600d14000c0341c041c4500440c5191441c00714a000720002e050703404000c0030180c0c122140d6200142d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 410679010 1250 410677760 410677769
    0x11040614160309030209090715050c0a08040f08160302010518011803080c150c0702091b0309010b15090d020f0d0b04050307021903241d0c0415080618010204 69
    0x41070800d14031400c010741844540c0c013060b07028210388800039103805000240081180c52910041d0038000f0303204011629500a44030340c1a030382c01181360a03c00314400d200900081c10f04e1000301140b99107005001807519091441c034002e1345000d0729040001d41e800074141c03145207030104540100c1c10030090040714855400e000c43e407880d03004200e02105101e40c40018040e4143c40004442d030760030061024000c500800c90f000c14500740200400001070a04401151f0400300350b0454002740c00c510036100c01190000c40d44405641c1d5280014030781450025111f818201324019440d2900c40c140c0c0c08100400481c00d0702901034401e102080d102e90b2100c1e410001d50035046840c410107820685001612544090350503841118480545245d0404002a02d0112039221941d070381e0440c80c00769441d518041403150069200e6403404601d4400c41985c0f110980d03013001c2d03001b4180020340c84c4100b208079003000c2000707504026400d0007480200700009007140c0020008c00a213040090f4001d08901a01c44c5801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 410680260 1250 410679010 410679037
    0x8060f010603053c0a0b0901120303090f030804020a1401120510050307062327030a12110723060c0a0204060b0703030b03060c070b0402010c02042d11040614 69
    0xc548454594040f003444400c961401009100c1c0c5941e1001016603403190b4005510507140f42c0100074014286027100f618501c40d0501140d1400b650b1078440b013507644c4120950115407407104100c00c529010409501804125164441000110780020061038011082e14541565040030071070103c04550000c0c010a802000c64054640301d00d40101141c1c051419900048006600d98100080a0f41610105500400b942c03074121003282110b130190032042c48140d01409030000900105400181c0401b004029490706a00100c210603801e1030b00c01203600441d0000340c0d015441d004000640450000f002003110442d4aa0118552040c107001003840c0c000d40c060b10303207003000a14041400281c51300700d020383c074100a00c0d44028207242c0c0700c80d0102c8a4010f124410800f110010b642110760135045401850401003008695001c541110052082010601824554121036401c504102580403060f000140b040b0940890a04200d001d030303005140a21510840042d02d5242c02001d4407000c51400a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 410681510 1250 410680260 410680321
    0x4030c0605071e0207080c030a2f0402070c1701050702030901031a120106050901060201060509070507141204090c0323040f0b07030b13090b15040f0501030809030708060f01060305 79
    0x4001a517121158403c000c028000e1202c00007640ca000310348540059000044289420011800252146001c6203440741c54803c4802980f140c0d01c0303510140005512401c00c0007946401c000e100e1180d44540d43c1c5005080e0b05000c100000c403070303010058031034050080c200403030b00e85061001034854900300d10b45a0303007040c03e014200e000103005420040407108161074401e01d50740c0780d850072801d980d5540602500110107402003601a03200c0d0000707050b0035001d021006030103150082c48500344060440241c1c1d104201180611840740c407481043c2d20108141000c001d01c00d11912100d501300300b842035203145014070b400000e00b030210003ca1001401e41c89108070341545841030700a4000c1c5010892140181c0300d41904441803003840c450440780c4d40e00700716140460340c0c17501d0380103030680c4400701e0343c513003007600c415009122403e20f0080c00e0186110b64010b90701c51292006051a2040a500906071076001205002486021070791203130650b40c00c0e190104665480f0701104040815000c284460200100b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 410682760 1250 410681510 410681567
    0x90e030a0e0f01050d14070e0604270204120b040c0603021303230303041b0f0e1f080115051f091208130b131509050d0203100c12050a020304030c060507 67
    0x8840d003504c5071f111500c40140200c2031505000d524043d0780100c1c3c6e070400800e585a840251010300415408541d03401c054030b810740745c6110f248400c02c6054104c0e5698001028030003000007841d46240504020b203021802c0c03241c4240d480190303445502c800f0380255036100101c520f00005010070f105182900701142d50700e00b02480c01400400000325410014510f040000c034602c1c2420340350b0002c46080820100d8640c81c2c1000000340b02c420320004620350741c3c64160000e03515a0a00941080c6058114031210042c42c210600489000000c0600e10340140c0000c415003050300b00c0e528000f582e440040c912030200c82c501d002c1040d0302c241391280780480000c03070000503002c2400f001400c200c1e914280540b43c40b5a140041400c0154142e011000700701a800244000c0c10958600c0c061759000074115080000c581611900b112501400d00c0000b40000e1403929070305440b4000c40c0e4000711000d000310302c2d601d081c1d140148800080e80e0010500b80c2c0f148041049188140749501c2c03111000c200b054151881c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 410684010 1250 410682760 410682791
    0x6150304080d0c1803060e0f07081b0f0306130c090510080118021c081c092307060813020411130f0f0b0c1204080106090e030a0e0f01050d 61
    0x5840c1c4030b9001420308151650480c454000d00306801140012a08074500795952180546a421941c1e2002c1c03040c4060041145000c102460003004279501419041d44601d46c4d6205110301044254040c01d000300c030031242d58400140c02544410104c185040014041c6400401c000550340301d084000d05010a121000550780e40d01c400b229a410001c001620000c40014400b0101c004081c1d842010300d4460340c801166010b0540c009485481c2551405002044004048002001c00348a0302d540d801000d04101d0b0a0420b0303100c4018229201c040c040c41071008036a11201c0d07002d003400300a071f4200030401811201c001c090700d03154010700602c240020550030740303200d800501070351046440310003000554164030039155003591098240070308454140b00105042d0745c00b105148020f445003000359000324980c0310240000d0006d100000c502c007450400c103041510b00304110300500b074104000700c02c240ea4010b0303c44001c900741074490551502c60440141d4440c0240900346624a0912040850b441207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 410685260 1250 410684010 410684017
    0xc0904030e0a08031c0612150209010507050307050708070b0f031605250c05040c050910090f0803071b050105090f13020a030501150809030d0e07030f2001030509030d050615030408 79
    0x1454003040240941d00c44a01a940b003047c2c0e0080c0c04070310620b4038450301b80d501d50005c2c80d1803181814500d150080503910030385103501000082d1b4a94000d0300050081c15030601404004000c0c00074a00d042c842c5c0000e180e0f06a04c0b0280401d00069089800d0103c000d018100740c8441300f001e81450161201e000b0030307c1c00500302c0c02c04212082400700d8400b10b00e81c5490306c02c962044051382d0f290b904007124041884000305c102c084190070b200c0c0172040060f09141500c1c02d079011705200d20107151202d20b41e240000c0402e0310300b95110f0a200d00e608062169982c00000e40e102503e040710f48400500c82c200c04240305840724a400c500341c0c1c2c000603041c003480f90142c000904980801c4065903d800001d18100c90784203040e0f50b8140325800410582412910310341000e10135580070f10070386000b80d0343c0f99500c02480f2180101100c0c5007180c501100d05003004030b5090803034802c0c02e003014400c5240c80103803151288505d000e00a0340399903078000f1030500d44549528a1515483c50700241d034a040c82c4c1007102c569003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 410686510 1250 410685260 410685307
    0x30d0b032a0a1a0309010b0a0b0406050310030209090f060604020403110d02040f020a0c140304050607170d02041502150714070303060515070507090204050a030f1401050a050a0e0c0904030e0a0803 86
    0x11f08007484070805051801f21602180c01d070745070580c180fa050180403509944045c1ca907801100750410040050387d40e034042603010300034880c0100a020359250301c8508040c0d00409491103144140402c01c00b041520b900706140110031201c03c200d440483c40020010407040400c446c145101045180640390450000056035000b00a255081c000c14240c10f42c3c1e030710890084941001041c00307203000040c1401940032001406c0e50741c145c2040c8094405504a8226030302200c03150595003904035219405102000c1003055040c5c06003a40e2400c0c9001a02648041e0600f1459800000c1d4090031705200794801c40c003800005105030070500000c5501c01070b580002506807254000c400c070004600c00b1602c01c88084a102825100046186480310122501404420b64114854841d1000a0300c2c00384551803013280740b103100052905040c00b94004441002e02064029407007078001030f1050780e07019080c03540290b051400c10425810180822038851495001c10200d200201d549141d400599824103800c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 410687760 1250 410686510 410686513
    0x5070219050f1207050d0305181c0908150403050306030c211c0c0f1406070315060c0f080a031803020109110603150f061308030d0b032a0a1a0309 64
    0x22001440d03010f003640b141460040c40c2d80d2080c95040704080c025082954411116251221400004140c076410600f106040139808100d054040310940c1c2c0040100000d1b1040c20001d1022464000c41c605000750090000350510102000103034841d075003005014031035803000e0310110b05006600d82c0900c0340e1907000d074036210301e00400c800400d507502200c0c04000c0c1c1da02292b84142d10400592105c001c0207151001c1644c0c01d44145a04c0480030f481044031a01075036103690f00107038070414400c1d07a151031040e42c0c1100c003c1041451014002c1141c13256040610b90304030310681d940341d4117450181c00800580d80b03040d110411144231403042c0340c2c0660105012600403003240c0c3d14034924000b0400343e484100c03480c51020000c6116030b01c00e03083c0701c5607407105540c001d000c0030b240070b016140083d40151141e001070b2140d0b10020b29444c0030021130281c0c00081d0f500741c00800f000c880390f2084807a018400300c1241c808050821043c2c1e2a55540d55440005201c041c0c0502805c68403510120340960046070030f00c0f0903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 410689010 1250 410687760 410687773
    0x315090c080a0c020d020a0b060d060204080a120f0e13090606080f011802090f04030e0307080a030905150f03090327040c0807020607030f20031b070c0905070219050f 73
    0x5590011685c90b202c0740300c030340c081d00350201141d80d82201241c010388140d0b00481100f411100194170f03840104060a0304600070451400c640c41d00aa040c440868030341c08004640020034120307500b0524500e034600041b1035100752800380e071003007200801041c41c01070001420014006111003020526042124002c00227020000b5204296500c1e410f0640000b5040f8003008001510601c400e906150000d201f031500704210091500041c0ca49400f50f0020821600501038038020103030031004800041c001503074000045c1a10308031082d018085c0d0442c020000304004002070503440b0900440e043c0c1000c100d024110702400311002012001780340007642c02a49490402c800b903601610110f0f00c00d12195000700080e9031341001c110040c1ca50baa400b461855256508c410000d40d41c62006070f007003d941c0e031080361680350950622034040090750400031803690030400e42c0c0c0420000605141070300c03040040814240c489102c100e00d07103000c007030000c0c13003620994042c1420800046400b078410358044044801 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 410690260 1250 410689010 410689031
    0x40f020d050402090115090b09031603080406030e010e0601410f03010203040b0a0216020a090504050c060f0f0a140c070e01080c0d061a0904032a02030d0315090c080a 73
    0x1046d440c40800d4000720b1504107003004558004402058241c00103410381b650174031980c3d00804101c01e2600100c83d400c0700442d0074080e440c0e140c1b00b0140b03800f500000070b20481d080d001696032200e00600039158100302801d00d02911f1540150a28151101d40001460a040603000d02181d000c08000c01c178490340303408100b61310b14a014000e9030302032604041c40b20200e0f15002c000070002e52060150070203642041300c00d00090780d190b40340385005244070390010890f8070305031804504107094062820702c00c0c0e0007842001c0d070184000b41611a151038201520390b81c0e112229042c1ca040c21100c003064072610001510004202010805204881840c0c440302d02990300c400807180c481b01000561078200001c089071401041c0650406200c5545006244025501c4440480d9082100b2034040c0e003c20071f5142071100c02d410b0440520401075810345d0700340c0c0071829580020b8948a000b50b0010416460f002c1d5440505200341c2d00c44001c00108000b00403201d40d000c00a40309074422100b0030300c0d0600c1e0022000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 410691510 1250 410690260 410690279
    0x604060b0406060203030f06040f0e0c03011515081504020a2003090105070803060d0b0708040b06060306090a0e01061e0905010b0306222304110a06140702040f020d0504020901 77
    0x3e68500d1340140d0f003941e403100340d01d810010b0014090f60b445030300d81c1071640c0c241d8101e1103409040a10080944501c1041c002410b081d107951600c4050301c0314100d1410817101c10a017001158403a400d160012081d01c5070a264960b051003900d005078400d200007036481c0e0090f00143d80d852503242001e0784010384c000f0200c045440b030090540c4140802e4040208400180d6a0b038002d681c411002400032039070070820313100c1c038400c19011503002c008500c0d80c4003032000340102440c015034403207000c86071a8590324010b0040351041c0d6024084074841178540601c000700481c29001700001d0550032040e410708141411104410103180e02c00c00750058907050020404000c0321040380c1c130544014201d82c07112079141d1044071001d0040c0d8044c0c0c6595990b0051a050103c0c456012a210841036058405d10708050501d031010b0700a005080c2d104424490b020000240c00940440583c3e442c03003019521000c050005c5005030816040407890700e0702c0000d99a081c800355500c15070286000742c0383c0903950703170704c0e0200ca2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 410692760 1250 410691510 410691521
    0xf0309050613061d03040b0d090506011409010e010b0a08090a12051b0304030206070b19020c0c0406080610150c06060e010f12081903180c1401031a12011b020604060b04 74
    0x1c070f03c85d0000c210500c0a440d0000041c0700c1c1910148000401035a540c48942c20514280c0000c2c00b480b43d4102480b0b2949041e13900b40340034098102c400c0c0455494500719600d588984400321081c40341c0e81c0000780d400700080c000f03050096041203042c109408a400c00030030640c001c40b202c074039043c104801c000169400000340c1d070a890303000d80070600c0c285540e1200e4903230a000400750140d07442c40000b5a003c20801c3d0001e05090000007000f441202400350411050f80d0311600200c0c90355022100304040c40d9241442e050803604c0d0900d5010303024601344412180c00c0350205010f8060380c14000005031015a0b5030000e07040f0740c1f040b44100781544c0c580400c200140100c6e0000b5003045010b00855940c810a041c1c20380c022030003814002000d200c000034903e248000e18500f42d40c62410540308102c00321460f08a6204400c00b460100f116441c0d0443c8804818050039070300d801010b0203031004152000940c03143c0200008088001824000610001c0d520790084074122a094106039500040b0b0500380181e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 410694010 1250 410692760 410692811
    0xb18150405071401081b0c0706020f060a020702010e13060b12090705011112030c09101110020c120d110c0604050c01031e020d1104090b01090f03120f030905061306 72
    0x4000c103d45502c406440880003000d017046d0400310402c003074000c002c0100040380c002e00668000c3c1165442c00d85025082040082190321003d00402074540140c0e8071242c030000003001122076080e07400141c1580300041c0015003020075040b80005890b00c1d0101c0b5003140e540314803403400c01c80d41401e4032040119110215000c800b1b60507400f0018101004680e41d0181d503002040015042c20b1070a408001905040e4003000207000c6a5644200c03042d07c40c080c408149481c03005c1005600d0250060b0a06035541c40704068005401c002145a40700345020340c105000c8070303650003101a00c80c20b0040b540394490a007900c04940610800d04c281400d54000e001e91032148a00d0501c1580780903c00346100c010350310440310b121410391344a0238154007805050141014018910001841440c072400140c10505146c03c0a40c1d010010b42d030810020700c0700703044446a8081880c0100c81c81c0c201d900145e018200b40800242603018401c104142d0800b410141400c0500400083c0f05803060b00040f540d410161140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 410695260 1250 410694010 410694017
    0x90c1207111c030f0c030506010917070e04062f0306100203130f091a0d030e011b2f1809070803030c040518070c0b18150405071401 58
    0xa400c0e9018a040c020203903038040c01d4038040001002c41580c0400041c4150000c00d03960014682429458030802d00c0d03c031a6401c04220a040c400c002801c100300502c1120005849441c041000784c5060044c24024000203d01d5811400c0c02e282c041e000d040c8003500c82081d082c00c0158420081c0060540a8031883c0b28400d407850b50300c60308180440f20080da6080c0341503200411191417529140c10090004282e1035002c0c082e80b40c00c002e20101a1298181030130000703103c504075001d07282d40e00c8400003051a81810241169980d80006880c25119420b441074400b40000f2981d0a0082e1410300600030700e0804601815048000303852803034031007241c0c8025044003420300e4a41e038480c2d405d42455040038078101124945035884048910b9580304840399a079000d0003003801c01190070581c80302d4241290303000c03503002c0925007803e00034030003c0c0d4600040c00a4a8a601240c11885001c240b801d05040c1d007030a6034851511046071201070041543d0445082c0b0a4400c0015000c05084200701d00902c140d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 410696510 1250 410695260 410695297
    0x910140702130902030318090711120d0603050d020309010807051206090a15140f0409081903180308040c09020c0c040e0705040606170f15010f02010b1e090c 69
    0x20240407551031110380080c10259a03c0440015035410805007d2107040c4070504440d4080e00c405011409201030b15070030501095076074203400756101060030818160440503c1d6102c0004460940140c00c003544042d00501501081d050803a6004c0000c05d1008800c0c0c132078003640c0e111020304449034400c3c05c1c0020f540100040100f1106c3c540003503c10b4100b04403640200b4580304444001403045000d6105804001c400110b2441c5c0c5d00341402e00b8000e10340211000c00c10bd80791520b48944a124501c0c60f01c00080d864400100e0f61802540040311510000c80684103070400e81c500507000c0034042d039059540101c0c00000013001d6129000300d034a083e07101005400100080d009001c041c0643d0100340080d402003d202040c1900d59205150040a00d45c3e00c4051407803071080e40c00600000035240000c0722a428080000703002c040c8503c0841501c0c20b2800c1a503540e20752108034010704c1c500740219403201442c910910301c40f4184001d001092411140b0b62415240c2035003920a502c139030040c043d0303a145030b003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 410697760 1250 410696510 410696513
    0x30f060a05100807031e0603030e10092d0306020a020c041b030b06160c0501170907030b060112050c0903010c030603051203040503040905040b10170c10020115090209101407 76
    0x28800d0540008041c01e010440082c0f0003070f8511003401c0542a00802987c0c0c2c0300c104140750740901c40201003e0240d603007000c41090000000e201950501400900380111058522158003802c49e00030b80403400e0246420054a906c0c1c02c1c0d020758010f00f2950014441c66610380c0302450b041c41502c2c1180e0101100352030700844881c0540140c208500c0c0d01da4444020f0104003007451603140d0100109102e80100e588142c00c1100150003010401c40208020840e4410080d00a40c0090802c2c290b035084914400305994010040f285001c0007816207001604280a104001d844078014140c3ca5800301c00910078882400b00403802c90751144009019580255001d24081d54000c00450b042030040040e01d1400d40c480d0341e00e0042c2c600c02d9a089600150100801021200c500d4040c8060601c00041d0b40b0214100d0300e4003603030707070100c5107420388105010980701c00100d0007503011707a8200c80c00c1c85000c00c07141c1e0388003003a070000c0d001a40060702400070807224002082c411616030000f1178440c94081e017040e0b030300e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 410699010 1250 410697760 410697767
    0x1a0d05090a021206090a140f0f0a061d030406050d0f020a020a2108150d0b040b07031a0f01030506120a03020c0307060302040602190804030b0f06030708190206031f0b030f060a0510 79
    0x2940d40c0304005001f12381c0000e0140106120b241c40400c0040014180c20841e0f1401b8000c4501c20303114044e43e6038041c6852007103044040102d404070b48091501c2c90312041e01d012454000c1072580505005944009800c2742082d8010a0099085000e03000c40b4100070300030410003402c0904900c00380000340144000401e10415440324800444001c1c041c80d00102d036030358540490540541e0151034401c9400708100400c5c4c0d040c05aa5071050302e286545841a00701c030045082c40e41140d00e0f4505140c0c4420010705181c4640250201104108080300d00b00c81c61400c020b511038402e0481140640a00c500c0461a18028000c80d03007100e5041e4018444040348001c022340c2402c0f649002c84203030104000000c003040b480c04900b070103600d034080c07800d8142c103158003003514206036548845202e030040d50202002e01e10760303041116415010740c7d800d65244e81e003000c2c911400c00d4401d500210300d81d07024070215984100c00c1c0503612480c2c1034901c0d10f00f80c2d00c2d54010002030340d0341403050303c0c1d001d000710460f40e41c41c0d0722 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 410700260 1250 410699010 410699033
    0xb0d0212031603050c0706030b09040209061f12050604090302250b131d01050906060c0c1005032a0304060207030e0a0602010b012303011a0d05090a021206090a 70
    0x4028040d20b0600782c0124020070200c01c0414140c00203480400c00074105401400200300400090400f042182008408140c1c1e0080040c00a0304c0f50306804001051361b00d501c003801d19107002103130300b0700f0420003101d201400d0001580c406003802c61134000015500e04003071103031055040d019002048004021a4200b008901c00c080000c080042101d0008102c1c5520700504440c01105d10121849820183c9440c01c0f554545a81d22421503448010055a107a0f21801d540104040e42c01e1642c0b5041403401d646020603204103d0f4100c89030405114045502c840594015841c000050040d100580010100048052030314013546c80200301080004103140c0c002c0400ca0720074244109070784230401c006250065141d03c41009030351240701540156a04c0301450f5504c1d07116101c1085013550038070705803a284c00305014101c486e401c4000340c030070110703415000d0307610310391250310288071701e11313140301c8194031035403078a400301d000710701c00c840c0c203c0c010b8000f140051240005100819040700e0540f180c0301e1a0303d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 410701510 1250 410700260 410700289
    0x90b090f060622031a1603020a05041205070603391b0302060108160e0a020c16031a0a110316200f060609060d0602092209150b0d02 58
    0x110030012003003a2005015a000c128010300f440020070703455401c01c00780e10ba5808030413440701003035941003000701e11104036202803031246880d0050300c0d1054550140c0741031003160881103845120500b034404200700001c010090f51003d983c20700c0f0500c1e030540e12004a0b0303c00c8081c18604d80c000403c4c00048040345e65000180300340d500c0c0c01650b83d00303066200d04c10058600403c0c1c5c01a0020801030205030410410140354060402180e0030191400728110806040074006140c0c29400046480e0008000c01c060030504190307080303203080184e4034908000700030b80328104912400c0007240060a4552140700d003d07100c0d0a05100503140d9a500903200500404926102044c031003509210340084c0c038044440a0f0824240c801030100160301d0030790500e02640100114440d0303070000100262501c81d00404d1200c0d9600680258490104a00040f00341c01c0314003489095000c84400b041e840d10117604000780b042c0c0103141040c4d0507007005080c00150760040381084d0704005181604001030400710307584007411 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 410702760 1250 410701510 410701519
    0xb0d15050709092904020f04061d0409050d0e0102031e0d060e0f0a0f0b0a050105090a080f030a030b0901050a052106040f060b191a0c0a0c0f0e060d200325090b090f06 73
    0x20040140010b00312950f880c030034dd50990045c08101c089d19045007140381e8090090000714144000d608881c2021a1400340d01c409001c00800c60820460240d001031028001400040e085843e10380645042d150040394400703c0681018959402624148a002840d0001501500780c0302d08040065440768810b02055811201030304000940da0b2050100301d001d5078402000d0341da59850a18002d098882d000a0580718452400c01000641d9401a49000700d40c3d080c1c540118448070f44000f03005500c1000800e082034001d041c00c200420030540d61448007103104040c02c20090780300c1404d00050b80000300200300400c0030f009081c400854403a10300501481940161071074860035100303040c10154005012a402e800e00750080c40340c60860500e0401a05110b10b4901080c5030260003d07250f024920f201404e42000201c0c00c00500e004140c14855071800175086172002030401103520103204103001044c5030f40500721000b0031500710324000d510003140010601c40c00c07511140c40c84140c13280080c0000d50300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 410704010 1250 410702760 410702807
    0xb0a06060e010e18010b0901030b1804021207030b04050a140616050c010609021b010605010c38040b090d110318010e0904150b0d15050709092904020f0406 68
    0x13038480c8100501d01810500d0b280c00e0725183c49000242c242c803108a203440c411102d61034660b0f106910b074420320380d1151f0102c40140301d4100c0c1c0b10070079040031800c1d0409010b014809041200784000000c8201c2c69500c141250900034041198041e1507240581e0704041d200e084000d070034070140c854005040b1408031400001401da548400010490744090700780542a07000c0c0030000c40f00d04080c424103000303200078200f010500001d80da408030308400c141e8203030306070344488080740a03122034810a482010241200303002c041d0816007031110489000f102c2c206034502c00c050800010600c181e0030708400c0c40f000002981007024015074040c8251800e0034190400030410381883d02c1c1c1ea02c00c0803041c05240924910100f50f1101c503030240030780700d01e911014042c2030314040300400100b91200035413401c06208000181a00d07410700c02c030340c00c4102e548000107079401c0c01c2d0305080102c000005401262103030003441d44400c401b2000e11050340640340094905403000c1c00200030f01d500403541e6000301d00c3d201e44980384 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 410705260 1250 410704010 410704039
    0x1501060c032f010e01060509040201050a0c0f021003050901200d0f0e120a02240a0e010f1b030e37150203041a040b0a0e030d05090a0b0a06060e010e 65
    0x110b514072000440583d1160a5036841c00c1c02032060030091308090700c0700c4c441c07860140c00203801480345242070350402c100300580d0b106000c09820303503422413640104548006180d2500c0140500800d40d00c80c0c1c9194a03100d40000254103510685201c03a090030344042c00c103009025408020000030041c0c41f0620340302c1c000c480088505000742141406140b40680d00c1b4a0300c540000d2400d160008a003229400c200d40e4030030b10b018000800c0798407003081c80e404a444010f00405034050482046038aa0160901a030807942c82200581e4911204455804100380a103074040e841da02c4011005007070184c040b84a01d031030840d0071158102c03c010282008280001030750741d98865181c5c00d6604041d0348644c040305020810425080c0d988245403056030780486800c02d900c801152080107801801c0c02c40e90ad10382203c11200c24010340710303645c00c030740ea0412840c9040e8803c3c40d228035002c507040b42e0b070000d0b00700000c001a10034030601054528a50310410308000450041d07560400402403036900040b00d150740344 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 410706510 1250 410705260 410705327
    0x1f020d020d09120f050a080c0a020c040908031905010506070305160c030c0311010c02031b010306050415090c080403020c010c0305040e0717010602070b030a0b0a0803040603060303021501060c03 85
    0x2441c0f44960100030100c983d071a001411540810720040401c0340800c680c01c4106d6000340c0540d0032002000209a81d407003039040c103a2800302107042c0c1c69005070600c0014018400030300b010314401d0b02c90030341d2010035050412020342200d4090041d00da002c042030003180040381c401e1028100c0001d944070b10700001c8a07280c82c0c010881026030300031110a03842900a008011a40c0e14803000120700f030038884401180380c0e000907103614030407041056a4600c40380c80c1710540e210b074001c07400501c40139008010440d1145c1c0e01940039005c60141c031171080e040c100100015485448858410b6405070f000e06851000000110340a95014400354108201408042828059000402d0090500d0f840303600e191034104103101c200366416403106003590810941040210500c2040f603034400c026010001e21084c1c004000f4001414540110810b48004540442d0075901648110705503400381c0c00b101c0c21609160800140e11009004010009070143e0100000900030071107c900d41c164603910b4400440d42c8003001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 410707760 1250 410706510 410706521
    0x1005181906150e160e010306141e06040f080d1b0b07120c1e020708030a050d0207051e070f030f080a02120a0f0809061006110c04050103030f0806031f020d020d 70
    0x38030f0301a5118540c003d4450300705e26080c6800c0803c0c01c00380f0106140200c400c50060036142c03000d000e041d401e001c044008011b40b9149018600050a09448580700c00d040c985403450b50041c07030038520428246c144018002c4110480c08481c00021508031000f0f03030f4610900410190500c1d003070000071050902d0141e070501070180701407602d17541c0c4a0654100301101ca20b03035407030300c60b0300e030642d0003c00081c40202404811034400d80234508125a55180d001d08050081c450142c0143c058040c40b9144000c4540402070740482ca20140100da1500b6212000701618000354440109182e440c030b03003d00f0000da6948080d15240b642401a152072139988029071491764070086194001500003c0c808c034019400082c4543c2148003507004154514200d1102c0c80031001074050181030040318035108010b0b030010030880c120584003500501441d40e592402401c0103111620360800304036100300144e1581000502e100e58501e0620900a55210304100e6000a60140c10440302082c0c00700290003039031405c1e0184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 410709010 1250 410707760 410707771
    0xe011a190803161b0e0a021e03090708060901110d09050c1503090f1c08180d020303010e090c01090323010e031210351005181906150e 59
    0x20100f000186040c06007042511440302da00c1002e502c083c000b1480150710300da07001d843c2500059485d2100151800d0441c00403441d0811058004100329a5a00c08a44501200c41e5942126031381d40b202409075003a00e0840600c070003804001d002800d040c10541c4c01c01355606010740251546101c2403404151800000c0000a1800303f0000038000034400820640780d0100000018221407d401c040c110f5030030001036071007020010078801103000080b4010000000004401c2200c203106040400692641c109106a01390740c2d50380000140440030104804203090816564410716500799610b4015030043da101c1d40d14080700150030309541d403070b09100d40b0306192102c400458442e2a514841c0c0090080101481603410f210703402004400702d0b0b50300381c00541b03074003d02000c26485000f20030b02e214103020310310803550301c03445402801c60503031a840780c1d0040000143c2d0a8050304181d85540c0e581da241c408042100300c8082c9440c2c04201e407940013800029014481a0100341d5031a160021602c00b50746 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 410710260 1250 410709010 410709037
    0x131d012f1c051e101409060103060b03040c03030e31020f0703050309010501090b0d1e0b01140109050a08120f0c160608060d0f0f1401050c070302010e011a190803 71
    0x80c103941e07151003460b144d80c02110720a084240c142403801c000c01d036050101d4510f00900e00c90001c1000c0f60300981050b4003400d4000c80140c0c90340307400e05000103498050704c02030300030030342c84049180305042ca0814000010620740c1181280351140030000c601181c0000704001c2c0560a01181900e480c0a00003003071124003940e1016100d00303105210740d08651041c0c0c0300d03001e814a008600c40150f00e84480c241c1c49207800c03101c0b8484a01d80b4031400c10b80c09000d035400400405d64440003281640314001600c640207020b0707885d5100151900306200b52101680a04612603016010708d10740c0e400b10704020403114078000c1010341858540d81c606468890103981c4089051341d034480034800b440e80f0041541d400081100c0510082d1942c0c0c40301022801000b00182800d08028006000d010001824400200c0008020080c52426100c5140b850300712000480c010f50800b5a40002804140035454030715400d040c0498018440344208404c1c00e981a16010082c0ba542e01d00054510b001d00150041c92071351324 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 410711510 1250 410710260 410710291
    0x1303201006030b010f0312210609020703031d190f0c06020601230d1104091a060111070f06050307090306050a05010f150f0e131d012f1c05 61
    0x5800c83c01003005030000e0486003024078081000c00c581c0001d0a001c103042d030800c00f018441d112560840ea403004c010110707126003046d00c0003442100550040c85001d000f03640400c000d42d075501d0b64960344849c0701d810344001da204000300320f411000b80d4a480400351040407500c041c0d403000c0e0740726007121441d540b005001d07800182c01000360f407002480c240b0300890841c20345041e00d1220f0300020b0302c01d1116a0040c09a00c080d80110aa07511207501c11540b45411111244551401ea10000140c0c0c1c1c0c01c4032082e00195000b011070380d0000000412000f03039003008208122017420118125803d80000380203400300b140c1c81c00d00101140440c0301f418040c840020021a45606219900d811003030076900003000400d14807603240c40d032640800840040181444c001941c1b071650000100000c07468481c680410f8502001e460048500210b01c9248840782c5e0024070144031901c1c01c804550303806054900c10480640c03d03041c55a11703035500500281030701c3c0e030441c1e6000326000800c80442e1011901e420f002c82004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 410712760 1250 410711510 410711513
    0x20409060213080703170f0d0f0b0411092d1309051e03030a090203030903100f0501080606130b0102011d06040201091401020d03200f071a130320100603 67
    0x582d00302003d01020310003001160314541d00c00d2920360741c1c1d2003000d02002022442500d110380745030442d00c0c00080800d0920071603980034240d4004100280c0c490740324500d01401d469411010b081950842c3d10002e006002120040844002c6080910701d620911902908608403a83d60281000d0300602c82d1140082d0030112880c10a290400020213155601d034070b488140d91110707002040729030000e00a10302207600e070054404070386580101c0301c400390300d13010b0050703000c504c02140d50140c09090b203101002e0003140d031385801c0705861312405e40c0c910f0340000944281960a48190708086a60f68040c4000250f00c40b504d00880f42c411304205068003079401c04000d00c02503681c03000040000e46103200021300a603581c40d002030754400920810300c00341626180310248041c6944051400100ba05d070a20f41d55110b01c400702140ca9004400481f0014554002e00c0288d0102d0031201d807050366065001c0000c54460303103054031140c603188452a02c0310141204e4200100c0103020340643e48001190108500d800c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 410714010 1250 410712760 410712787
    0x216080c0304210f020f0f061b070915030f0f050106030c0501030c0f0f14070c17070801060305120c0c040908030a0b040b10030c11070f09060b120f0601020a0204090602 74
    0x10503c02c0c040c420f1034001200085a005039041c80013070f9044401c00103140b0100d02040c0080b00340400282d101c50040f07100380d040300f88012120280c074200019105981d03100e041703000843e0440142c04600070380c0c1440502c005002d0211002c002e9024000c00c1c0d40ea1445655518290b44407600201c5540340f415404100c5941c1500690003190b00b1410b026448460580e801000e003204600c1807002c005101b80b000842501c6c010460758100c0c1c2191030740340e21a886a481d12611007000d104121507100b8101d00061004061041c00d06803a8850701415000340070012119854100d101700c1d4006000d4035100c15026640e84c4030b1105c1039481566800d80324034045140c10116885e41c14120b0080d0309180c20850280d132076001885800910b4240080c01000c2ca4100b00d540252007031000195114004010403070a0743d401849048421501d801d00800e51110305401890051254058590b4166804226100001c0f00015441700c4184111440e00c1003540009060300d0101c4025500340d0750005403d04110351 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 410715260 1250 410714010 410714039
    0x150f2304050906040228140c061b0316051b0d0206041103030403020102100e0106031202030d051005030a23032803050601020a0303020c0a02060a11010f0608030a030216080c0304 78
    0x2003c1341c2c11410128074210028080950769458406e481a0060307501c8000d015030070f0040503104144580781c88407026068241d540c0403e407a100340d0b024a03150710300c81000018040ba846001c06c900e5007a456610308009070b038160400c2ca0503003000c1108444013102c40800700030030010a400e60b4018223490425003889103c3d031410f0143c0c18060f410420040c030250341c0000e030302003000450100c0018410080c03107801d401068103400003004d19040d071024401440c1d000025120390014030b68200295200e50f503100320548024418650076411041d00c1001040040103051901482d81094164034000c144070241140d2240c4141c000c1c0d405845036903d51180c81d000d0310200d140b42418108018141500041d6a8559464004042503000500000d00307032002e2150f514101d5001d003416403142a08000600b04030301d080449003a070362802e0812840584c40d801054103c41030000514138020820104501039402001010707041d8200307040b42130003d8035890050400d0312a01c0d000c2d40c3c8030f0782400040c1400c0c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 410716510 1250 410715260 410715271
    0x150d0b03011a0123070506040318050a0b0702030a0b07180b0f300a0c0f0201051911040f0308070b0106020a081803010e010c08100f150f23040509 64
    0x389800111030840902c4095280c03401c4007401d121200c1000c4c45411911400c0040c00b15202100c0030510a04015001403024003d5200c0d480303c00d10080f18a0210300318601c24072515a1011450108000d0030942c48010700c180b80c005002e0706d07034501a41d164408994030a4500c0400076100288240060303100c041e03902c2c05010204119031900364040810f007010700841843c490000800480401d4400c1d520100006000c030400d6902c86a140900c1442e0041900242013008600c1123022402561f1062085c18400c80c4a0001040000d2000e184040240403640745a00318220402012034142416041500118810300b04166101d58910300140034802c10380c42001550701c0800401e00180e094002c0d168041c0248000381c02040c2101c0003e80508481c114403400c46d4645840700c0302881c0d0043e0042c0c418000c0c3c00e0320a0946a4520000001c055203201c0d8020314107103070110303103152231085803240c0e045003e524041c49034500603044524484421110b2144454000a080049040c0808002e80c080d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 410717760 1250 410716510 410716513
    0x10903020f070f14060a09030b1905010b0c0a030e0102101802031e060a1a090a050103050c01140306060304110901060203040f2106090303021c050a06142d150d0b03 72
    0x1d20380707840d60610100a1003620701c140c00100d90520a548604107c0000310f80015512060307042103d1001541c1034008176514140e811b20001080420114080300c1e066101500140625201074070304079400b80e440002139046004220b1030300c000a40a000d180b05030408551040c1c03c0000c18410140703880030a0400c84070400c062501503d0300900428815406654513901060100e41e07044060700c9038006114644c1c0c4042e004090002c12a01a801a4142d034030036022100e407818624019525001d41400b18111040c0c1040010340c40e0a0100c0659040340c410785040068600550000380d85160903040100180c0c4041010080070081601640044c44000c110030302011301da03641c0c5442041d48e03420140080382c990030b02004051299044500380d424160b2000810030135000703058050a0291422004141060400b04d45c110704102a4030003800c001303151001480c03448501c030390603c02107280c03070100207400f0180d144d142d100e0405c5141d09850904249d56034801814a02c0704541c143c01406010f03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 410719010 1250 410717760 410717789
    0x801050f0105030a030806040207120f0e0603010b09010c0510091b121101050307020f01060f18020307171b0708070201021b09270d0f022e09080c010903020f07 70
    0x650f107000c11014052034061804a100b50307503080208020307100f48030f4000c1030040010054410203502c40002030240340d066a42d030082c0c0352894108441c5001c04c0c05001216901013000c1c207840d41c06803100e6400ca5201e07a0644182c045030316a408121510a201034840582181d1610b00240d11030070150054020600711005021154039186019500381b210103041c0030000000c644024000c200081c010003240c4000c0c00000c1d11080e40b40505007080c840d0040e040400a11948602018001d4a1152000c0ea461041c081d48000b0500b08408003c4c00941010740039200c0118180703603c0000b0020a400749242c60b0b40c527251031000914150b8900083e41111151911000311581c5408449400082441d46282c91003512220a0348039029505044800e2049049490f13600744c0119448020001507000c0e280f020003820389400d40305040542094840310084d0f00039070f203180385a2109845034024010203007054408042103007121030440c01a0050b0303000480603850924200131250280c0a481c040408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 410720260 1250 410719010 410719019
    0x6080c03041502160203011e0c0318020d21030212060d170310051f0e150403080a0306030206120406050105180a110906030a020301140d1a0703060801150801050f01 72
    0x26458551070848002d941c0001e401000559031040340078103950001c0c000c004c03004803003040c03003a010041c14040b04400d00b08600d82030894000e1161581d0801d502d0354244880d5082e9007005915040042c085481c0305030007107800003c03011b11103019015400d07902c0c0181d8822a40104190b038060041501d03110340410804003000605044106d20f025001c0c00300152261181000d40030300d24010f810258101c00c036a8294065654440c0c003241c0f440a05440701c0000403089c405000e0052180d036090300c0d4441003040100001a403110050040c0c01c0940703000100c0c140c496000a14076440f680a0081d401904800d10040c08000e100e01c03801044100c90b071490b00e154842e03091024220081509802c60790b13940c0c200341c0300204030b0101c500905005028079a80d10340ba4004500a400a001d01c910f03600450703c10130018246000810f41450700a1540404c041d2910b0101c17007803040c000e020804050700d41000048500302405003401103140460304140003814010b0050864400412128500d01d0a200411 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 410721510 1250 410720260 410720273
    0x50601050d0b0310090809190b0316021509010209010305161710030614070f02030405060415110f07080c0a03020f060703020309180402090f010308090d020f0d060606080c0304 77
    0x142034014255001c02c08014090000703081c481901c41d1421000d040085441c00c02c4030650080c00040e800320b64000444000c032005603a500e0940c0550102c0a404001040c1014046881c0b01c001c036025104451003160054109490b43c1001d4400d018580c1d0041024502c0d580c00d4045d50391b00180c4541d56038036125081c900100f44500383c406241d140f00783d0f400816a030055810440014641050f410701c080c065a03d00c0b00b0884d0ba0845141000801108501c0401840402280c08840740100450b007001c0c00d2030017640340484c3c42c01502c010312221011045070500103106481d45156114044c007005403800d001c2c24205585031404c1403281030000d005000607940d02c0780c0e0b240140000c0ea032103510703001076143c2a4903500c600ea4003c3e03484a40c0004010426401d80d405900c640e10079a90311006440744641ea0400c040203003c024141002030000440b01c0c1083c180d49010540010b0040c0240106000815403c11041c9015510181c942005009898010b40c0d0035400403800d00500785103280548806 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 410722760 1250 410721510 410721517
    0x150a06172401111011130e0f0c0a02010b030703150b03011b05030702100e060105131a0438120a030207090504080d020a020c040509030406020a021306180b0a0905060105 74
    0x460521200c0520f240d85150108000b15807a84003075010080401d00c0c0c20201c40d1341d000352100c10000700701400049910081c0b0369550b4020311100242c0412901c43d0700d40b03194503420400b840700440d0350f103602060260750f040180600441c019041340c3c401c6030111a005003900ea443c180d00d802a8100510b94404440446100064518603d00b05481c0d0703d0340101203042c00800c0042206090910340402c0544030041001d9040b240c00310f6001d90070b0200548a2020384800802011007220414100c40e864106908140c41201c030356855446404030b01d9030301d021034040d04241d080fa13285081305d6910b040c0c00c000b8607a8041030700754002000e0010280d80e0095072401c6900071a0300d41c0e0b88a102003801c00055206403071203500e045034251740720801300c50025541e41010482c5803107981841d02051003e0800310403a03060781d402c0e07400351015090640030300c0701e40d0501151303900245640383c80010315010009040100761000f40000300d0114032031400c20603003c12542200501c24644828400c040c0c0c0c1241c00c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 410724010 1250 410722760 410722831
    0x90c0913060e03370503040210050f0f07050d020a021f02010902040c02030702040f180201050c0c040507021c170f1806151807090608150a0617 63
    0x100354410362440e100c00500722000040d286032001040003281e10000b480e0b03a5001c07000383c4162a5903003c00d08403003141c968016041c0340100700100080782c09410524440024242c0c0c504045180c5002c440200d1a07590005030070254440020608800304502807001003842000c620050154107000d80000d640212109a0301104e00880d10b40d0700b01d068000e40040c05181e40003003081104185801004e5202c0d0f006120403482680707041200c03428603401c0d00c5010340c0b004010a000d050f00719035a0065903651301503c101d1a10f80314400d4000d903903541d00e014031380c0f1485442c1c4c0604082c00d481044050341e8600c88094909100c00042c1c10055040c00140c003561192410f91008101d440d0105101401138446880744080c0c05403908202d0740e13a460400b01c00d51640c0c292004800d101d1901e0107583c04200548102e400521000c100700440d510821100fa0001c1e8203503140418420740724000303036101e01e0070352050007c0782c44500354085861041580d82c0e480210120f86c11201c2d07045a40045094050410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 410725260 1250 410724010 410724031
    0x30307050a020127030f080702030a230f04180c050d0911190510020102040311010c1a010e0a18020d0221030409020903190305030601050d090f1109090c09 68
    0x10703038000041c07003500456800d078015201c0300c502c4c025004044000804180c019404254154541041584112212481092180d001d503081c40b00050085600224485401c01d000b6058480c4003200c0d02008003c041341c9100300f25841e80d8a242c02d080d08e801c1c402c000e201c9451f0390306e81101007071000c0e0031401300c0301070032100b0400040f10f04c000e282640307858084151850300541a600800c440c41c00900c0c0d0802a15000c41d51503028042c801c00413402d134030940c00300815000680744070044950143c503030010154884c80c0e2081898444000b101941c0d502640000600341c500e0044c41000314061003031000480328126401130920494010070b0000d811a64001e008034900c810108031106240d816104143d8428250f135540c9685a02c081c1c060740104055512034001c40c921920b0301c14054402c426410342c0340e1140c80c216520319006440580000d0404541c0d262540807407000601601103a403800d0380b081141d040c1040520040c031040d8180100801e42c00c0d031080340500c0c041d559844c034196122a9001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 410726510 1250 410725260 410725267
    0xa02071e1a07080919030506040c17030408100b040b0303120103060c05091e01111b0f04061802070c030206040612050105190e0603070503120318030301050901140f0a060e041503020303030705 84
    0x20302c00c020b00c1041d46d002510b680648401c7c0705c100b040d104580c1d070480d4452000d110000001c030002c01c1c2c40b4465031044c0700e207a52080720f4214484003181c10091032040c000b80000740080911004c281075a2182803030088006080005104000f000e04c210304102c031862904901741f2044c24042400b401400b8001810a08100c88180c203e0703104901c1c070407401d0030090580d030343d2a074584840300c0320604500c8454829283c038108007101d81000d215120840d40e00c104034a61541940d04200f00030f51101d441941c0c600b960240120160321180f000b031004001d940d03181061243d080458404498040c1c024502c1529074a07000802800310004940070f030340100740140856190314002901d048200d034003954060180300841c0d0026400040030b544a6440c100c06024158616040c050712403009015043d40003104000501c0483c4003d82c62044002000e818090110419000514088a281d01810000704010000c1580741810b010300400001c5414008060a0a581c002926804024141c0c0100407021 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 410727760 1250 410726510 410726539
    0x20070311012708150903030609040b18061005040506030a080d0b0d142d0a030f02010e010f0501230d030503060307090c17090c03060c0a02071e1a070809 67
    0x1280400e402c124542c1c5214507980c1d6415005460b00b220850146126405034002007840802204481c4543c2c0000c0c44054140d0359a6241e17003c00d5005000003800854000c084920340c4410840580501c0400d400c03445800d203050b040200b42c0d0130040c591400781d00580071800020b0301d59015030307600e983d6108010941050550102c1e4004e15440006024810a042100c11000c4082215202d0000c0c550340d45074180c2040241c0c9060043c1c4240720240b6a02495004000c02d10440306840e035080c03c0e200100c0da034404026010309440101e0000c2c0342c0310f5a030708010454030b50518050301401c038100188400344925030000500003800c3c2613000c1e01340100040080d04541c2d007070043c00080c01125604000201c440328000b40150b007110960002055040c01040f806800007902500c801c0c0001c00401141e9500b92404880d90040351380c84080d44101c2d0008a00c40c0404080c40101d844021f43d10b034481ca00d4142c1e00800c5408114055545040070081c440114120f5400c9680942060381c004c0720700c1250 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 410729010 1250 410727760 410727797
    0x11070b1302010c030e060f070c08010c110607030f0905060405010501050118290403050a03021605040203220206090a06081009020c030403140a0605040f06050105030304050607061d060103032007031101 88
    0x9030000c00b41f8040000400a08124540f80380400b07032180d610003009020b41548058961680744052000c20303510400000d000584207800c5107810802031800801c1030700c01903903010f1030290b0039201250903035102c000500003541d1003844220003203220340c100850130303240168142e042c0100032036422001c18100c051406d2070b02150100c4009640c040202e941612850400035141d04074201448165032140c071000803207241034002d5a018045c50104460b0b0321b101103c001081e846002ea0482e08204240071440d41e030350f56011144001c02c45510f401485281c03090f0b410305c4006130ba80104545d2441807002c03e04442c80001900c054a500c0950618001d0032102c4d09890221140c60080001d07040400f000101702c46a84c1e4a1076440c46000c050000b41d07200c070101a00e0340240c1c05880d4010320305000f10804a0f001d9002030100381914100d01400840a00000341481e000341c1064010480d1201c0607495803e4041d8800320a400b0103024011003810f60b6180690711000c211840e041000301405002565034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 410730260 1250 410729010 410729017
    0x21201092d1b120507210c0e04030306030605070e04050a060f1203140f0a02010c110c010e0f100530040308090f01060f060201230112080d11070b1302010c030e06 71
    0x1c450100c0c92001d82450019031740e40041c0034840c0001d0290340c070f0554054581407180381a99029500c883c00f1410012840002080200181c0415440c0c00d8000089011782c415240200c4484d80c0305a00812140c0911040d52005481d000075903140803410820002480138250588002c1f05da5224450440d081c2100c24080c12251410824400140c4001802c5000000c0c030541025400030302442d242000191a19125017080130703082d40046e202c542c5258400e041164018800605000800703c40c86c01255170b8003c8103010f1008140009540024920640140d20046241c0c405401280ca00d1106101280304040d10060030f0200f000f0205009070740501041e409580305800801c070080c0d5802c440a240d2185104400141d403902d0f4010082202c10180a00e45020080354100203900e00407980518404003802a200064180854184444280920031403019442d04507621501c00c1d0410745001c9801520915884d07030030451200050741c001074103541d07040d010b05000751400c0000001c5141440f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 410731510 1250 410730260 410730269
    0x5030910050c060f07090509040b07050a030204090603080403020103060b0403030e0d03090815010e01090c05041502010603020a0e1b03010303020d0e150a050c121608030c07021201092d1b 82
    0x7415040004c500c07110400140f02d001c482d641c0360380c2a42d0750303003e1145607001030300e001d070010311040e000804503402a401040d10b103116140c010310382540ca207901c200302c611035041110031801c0003808100359170b4140500c6000e00600401103240c07500e90b039400b0b4200c140380440d0130b00824211410342e0a040c0280780e51001014400280c4401042d41442c003901e6440c24000c0b2030000a001c000402c4560b050710580b45901c10030740f01c10b440e25042082d0170025180d04104d21013150f4803601c0c00310046e12090300d0303c030060200340c000e90300c1c41c02c6c0b440a2040048031106803c800b01c00030f000420109500042d4000911214108140d0241855012641052100d10040c560304000180140340550110003480031007090815034056030321003aa800c0072881003081907654040e4150b401c2c0007180e0040c0c001d40c0c02010440103580b4044155000c83d41041d0a40c0e6000071036552140400b090080311203060155a0076a00c08411103181c070406541c10709103031003004d0b0424025990fa040e600b2502d004d00802760 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 410732760 1250 410731510 410731513
    0x8150d0c0801020702090903130e0910110307030b0103020f0a0302130305120c06060906090402060d0b0901031a100609140303070b09070f150507032a03020105070e09010305030910050c 81
    0x16031038081c454040d6009a204a004200090005040c00000300c140c864142c103c0c60314040803440c0405140c10f100d8040e10070250390068400b40a01401c051103220410240000c101d521392400000c0a8110b4800d01d00903818540104000d2a07050704c405e0494031070000130b040060301da80c0c048451102c0d00b4840d410046c0b02d4825904100208000c04015102c010500400c40c3e1a03a52503400340b00366508182c9074250001d50280c041401440d0640160014042424001a510407900c0005807690000c1e80161801a0114000c030b04200050681c0c1e03501c8105d01c400148100d18046000740042c2c01c0e4070a0312501485210701c08510399050080703c01440e0803039400d1405090420300a515019948a000d03444629443d001a607601100b5440721120340b20784aa83c00d0800a4805440355140f00804845c2a1084441500d007003c4103038030307114618000d0f80001072500d0010340207002c5801e002c8440d0b10600c03076180100b0000d0000400c42e024a98151109101d010514a090369240140840d070b0305036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 410734010 1250 410732760 410732783
    0x30405060c010e0d2f15370606020f0a060c050f0d02031e0912030403090e0a05010603051008071715010311030c0603061c08041815090c08150d 63
    0x741d0b02c22092504080c1007040d50400b40781249460200017445c28102c04546c000b0b07040b542c501810002ca9543c814a000814986c0e50781011012004400d0303000300710310f5030b1144100091210b0562145030f015100c240024091500d840c1005071381c800103d04001c0607252a100c40c051014403540c00c5c2c51305004240002510340203020500f07c069003080700d009542c400d1028001e5a0103075a03186590040c809075016240540351aa440021980b0042c015418000d02150003d200b8403201030b864032411491200207150350410f0070060a640303000c2d04514280c000d6200610003034002050020844042030760005660340a00c130382a0401403440c0c42d20703142800d403c00001c24070030b400300c101c2c40301c3c0320840036524119203060400c500b50200ba20000d0700074440c60b25501204901c1c2c0c2c4051101400386811600f0b00760f07030b21152000c11a54540c20424940c60b4050b15606000500f00d0038080c040c0f500d0240a062000301006104070401080603001c8030004100b074004d0b8076802c101d02d11094018122020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 410735260 1250 410734010 410734033
    0x4060b041202030f01021e0d06030c09381909020a0c14061e06030a080c07091812050a051c0c020c190510020c041a031905030405060c010e 61
    0x64803901a00183d00a0007010340718140e15406108903880034107001c140d038561045481e40c072103080d0882e149240c0c41c13654600012012500c2054440000d200840000c1003108000e070035480414040080c1000382c4082c48106c0c0306001307119a007184662801d4407103400d05031650740d580590f4041c1c0da0084040c00d1000460941a6a0044401344036601503c181d40303603d04d001860503698401140d20030204010a0545400c070001e002595030041e01c0181101c6002005803540c00a135408520802e5203030303201c54000c0012160030300445040030b00c1a84030b254103076190746a540407008540061420000005140e03003982d03000704140d030242c3d1a841840c1e076408020310aa2002000262440b01c00340c802d198141040c0c0ca88911160030a10110a003144010301d44000d101c2e034541c2914603d429070046200d038415540f19031040f02c0b1010000c40c1c0c03202c00e87c0d04070b20901d814282c0990180c0c034080304d040484800304000000321402c990080d40e056584400c46042035004008051340e400c024000d800e0701c00c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 410736510 1250 410735260 410735279
    0x14161b03050304030906050406080103020d0f12030b0f010207030b0a09051e0109060b10020d11010f050a09120c080a081e04050c0f0a030c0e070918020a080a0515090604060b04 77
    0x600c036510a071a00805c50b03455002c29241c0d40150f10403900041e1000006100508100841146052240c8020444031050382d40b4503282082410040000aa680030140110302e001148900522401e00140c000c5600750744900008000007849503601a0300c0e03460b00405c10408028a4941c20034640e19580c940e02c0010395640078100e002410348030a41032110060b40303441c10a8441c640e44d151500181003028003042e00313840800c84d00000c1c1102d5541c1e21034050b0040010f000c1c9512a810005001614011914107141200d035002203181c00c201d404d400f04400150090112150240f60f802d10300560395444014220361000d0054a25060144100348402c00a0000340071303982c2001240e20f40c3c4946800018005c82d1845440041c2c401d102ca0302d41013048481042e140350304040c0d42e02c0e1184100c2d40b10501c81d84484810b9507030400c1580e0000b500d0107140da112100c5900082242400e00c000c0c01d082c01c00100c0b80b88003583c5584038501c40800f06d0001d6989a1048004103801c40701d49440f19510041403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 410737760 1250 410736510 410736517
    0x3040302030f151e2701020406030905011505060d0203060f060a0201050a0605060c03071104020405040c05030403090519030206090f04060f0f08030c0618010b0a0f06110114161b0305 80
    0xa490554229011440b6080c580401182514821840e00601d0b9110340b4041c0605c0b5040403180c500c00048548400e035104203000500250065450200d0450810718040d421075416501040c402190f984040c099a9542c9040b0f81e02032000b2180980c40340c980e0000101c0511030009040d40c0000006610b0700d01d1601908083e100e0700c0c46075000c00030705687c1e50030700c0805e11450382c150107039400c10022000007980f00903820481800142006052540304e001080440d00c02e48242c01c0030400101c104000c00d07903c42209005414181c0c1c83c1c10801d40108a00343e401505804001c2c440c40000c2500344c015180c1e4034007100c405000070814025142c2e1640c030250300313000743d0150b00d144801404002c1200c2c040042182c412000000c01868103a07a4003c00301541c01e0f214541001c1e5549a040d644860741e101d0140c08044d0490394003155075a450007001515050f021089046a0f904210f01c80700f0740301340140c0259114406079050901041c1001e4102c0392103080195410861400d000ca00043c50340c840041c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 410739010 1250 410737760 410737783
    0x503011d06070201091212060308030405011b0302070804141306290f0d050403120603080a0f030b010c1223030615030f010515040b0a0c031d0102030409090503040302030f 75
    0xe5601d141c903080d10490130788038210000b0344150348540004c406548614400c104000001000055650312503543c400245c0c807c0e1802c1d07505030b441300815003680c4001c1460001c1c40c080c43c14210314021056603200d00c58001c03403003910b22030801a0b510f0303401520360104410100c0a190020000d40e42c41c0e2400c044a0100180070310751202810015030383d6810382c60110f034000d124011403181009580b6103000c0182000a0013101044980d00054200c25003600031200991312880c40182c42c2d894101c0c0060003e0f852100500c10141030001181260b6005404056507641180d40c0e016541d030403800948008044020165941c0e04801c5101c0c03c01c10f040c006103018410440d500344102411400c05045c5000a0ba035803003c8080b00d100402062800c05070981012107140411400c1540c0c0e00075004030354203d601c003000440d20050701801096800003a40da10724440009540b620059500000e50381e010b940240c1080075540c100348014840b04206680056a0040489001040e04081c003502d64105141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 410740260 1250 410739010 410739013
    0x30604050a171204020f030703080c0c010825110c0d0c0e0a050408120417040e040201080c2a0f030307050a120b0f0607151104030213151206060503011d 67
    0x800604501d0079a044403041080840c664440307031035a030200800e6005600c6e00035410301c240440000041d54a4010b0b015a07424500500b210922050014280f040e00500c01d402c09052002518070754a58950030704042081403070304003094150300300098a007694601c07041d83d0000d18600c0c010108414070132040140d500c6009012640d84034040d00c681524400d5038000c0416a0500c030004c0131801ca00d1210b07034050b014019101c542d0241350340e0070f40181d0141e0040112060420308200139541c00c0084140c002c00c01403880307807a20211061100100982000300d511a03440501c91850000040040704011408130050f030f6502d04104101500a51148420002194400741301c41d4200301c1d188500400035102a2034841455005020040c01d1340c040401140c01d6039000d0860038007010648038014030744803e4241903a440d81540108018803c2d1005002c5240d4200140e1030030b4040d0360034044080b078800b454000410758492510710003805075504095015840e01b040c0a2f68440600b050700301d040d42c1c690 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 410741510 1250 410740260 410740283
    0x2160909060e0105060307031b0306020f030103050f06220206090303030c19030209030d05210f06040e0307110609031f050403090b07032010050114010e010207030c05041a030604050a 80
    0x1100b50903104c003103c00a0b4190065081000814540415003066045500c110841039480c0c0e5268800c0340c10204810425030000310050040190402c04001c06480f04401064a490043c00b00000701c00940301c03084102c0325901c02d003002c5440c1c0606880d00e0407030003000d403600c03860070070490001908416007866a0b24807040e03038019034074002c0c03084945246025002e02101000c4d0f0600740d54641c406100245841c1c4e81c00d060f218244003281c2e0490003403480c404104264101041004282c079018100140503030400c02c003910001d020421580d4460100743c030040c0e01c41d525040040d00f40494101d040000b807502c084141c40310300e519030280781306074400d840b1490100e40340e0820b10000e000b2004001d01150b1030500411416851400110b2102c45002c115542e40507003203002c1098460a9016015401d03c003034a40c00c640d030300246070344881103080c801860341034a1a1914a1112203c1c440e144c010b507602c0017450691003c2580d2007040d82d0015040752440c0c106803410550b500d8070075109588086140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 410742760 1250 410741510 410741531
    0x8060f0604051806042d060608010c05160b13050a0501051b0a05160c05150d14040c0b0f1201082a0f120102090411040f080606010c120216090906 64
    0x984203c1280c202e20401400395a503996141ca6441c00c0810700c01207208811441d5107588014490b8510045108483c042040b510b400c1076103003512010302821040c0700c0103000d2400900c1c0d103400207022307103500407113281440e880e05c80791050f2140602030050f00b94040d80340c088040c001705400a502a0f000400c207044120b0032108813110a014440381140021010080d28522200c0c41d402d40784920300901500e00041d5445e0002030800310701115001001d2000b0500f070150306607501c00d240c89540f07581c0a00300946041e556002e032552540c0911a4010b0b40803540150715030040090303410303803100d4130f85100c070950b16003a055545036203031803140c9440e00d042c0404605002c0340d101c81c82040c820140c1300c04840e02c40307101041030751204944ca00100c7d6609102000706607650703005560a469110380d0701580d9500307000d11101c070340c591504007482c0e950046092200b10b91b40070544904068001c0d4050182c1c68607130808900f41016100c0d076840d031700d40c0340101140d000065484000e40c14420072007000020100e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 410744010 1250 410742760 410742781
    0x9100b04080706262409070906090b07030509011b1509022e0c03020f10020c0f010501050f010c061b030203070224010501050c15010b120106031a1908060f060405 71
    0x90403849403020400e00400c5d00f085c1c0304240030b501103003d4901582c10480c09000f261592004880c03010000343c02c98010080c0940001d444005007100d009210700e08245614090414403516442504010f05907400750511071241103030500030f5900c0b40c1c03211030070894070405a01902c0781180a9214192420a906020300c804803402014245a08540c020500210702a140078003042819015030180048403081c0302c2090000c1150030014080050302d075404003030460325048080b901c1032078030303850800140240c1d5100b84001c0041342c03091a0808012402d03181103800f4214000d80c05c09150700b1400301d030103580c1c0c241c3c01031803240c00760f030b800c07104100c1c84606044002e1415004400e03c00d28258014003040d4405d50041ca0365401100071500128200c040700424000264010720341a540401e01604280c2d10641940c010b107440c2c9000e02660703945400d9108070301c1c9044d0506215140302c1720b58035003481c00e0302e0188000301501c2d8180d58143c50240c00219913010111100c80c480c510f40070002d8a030304034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 410745260 1250 410744010 410744057
    0x72405060f0d0201030f150e04210e0d0c050d0c05011112040905040602040812090a091b0c02040b1e090106031103040305090301090c0306140105100e09100b04080706 73
    0x100505000b03a60030981c0054006042d25281d900070551900400900800d0510f00c1400a02d010103410700c1c1c1d4a02402e007240124444d0041900c0000308040712500c607540070004e241c0300700702100e41d483c1c000c21502d40445400d9640c0d101d03540100d0b60152480503c1034200c4003904442003a01c1d0150424214481140c80c0c12046c1c05050004030300744014454450b15a00599110380300b542e00500d010b0b11108001d1038194214500d039401b001c001115a8070717050032040d40004107414642402003908150f1200b41443c8415814800c00560f01c00c0041555503c0c3c010301510308000d441074490003c0001d0704048121452940750043c04d0103000015010b20a224807010554a074030440e0941e03c680d03504465542c4900c6940e0391541d207a50780f050204001802000046200d18400035400c244006005403051050b0700c020304c2481d040c0e141c0310055030010f9402058400490712240142d40c1c0c83e400081c41c2070241c103d02010240800c010a02d0389001401c0c0e82920030503120803803507104903102e02d4007510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 410746510 1250 410745260 410745289
    0x60c02010c0e030c0d0f060207050304081b060406080f10170d03180206030c0d09080a0507020405160206011509091a03070b0703120c050c06070905010e090c0f0a0507240506 76
    0x144169030400890041911140002e2240101620740140c62b00c07018a160001d402c494a1904400004020289444400c0040c4c8405423207031401d09107402c42c0502490b03030080c481540d41594800081002d0041c55401028106480c042c02c034200c0c03c1c9068a0340e035509243d082010924181040080d070b00d4051407140707e5a80104241c0c95996505d001d49110782205030500030b0282c07100403020005131b00c40c0c0588403120305650350039206c4c88a80104416140c01a05400722603000d100003441840e404980241920136401e1042138042c485601203501c03c0306076104500c168502580d0200c11141032010411a040031000c681104d80c485242c141c440c89010b20080106018860341004607210307800c000e10610107810f04a0a1481100660307003800c804691a1000803071504040c00250307040400400c895909940c0044039140413244401544130303005081150641c00314004440c248a00d0840d00059440a44649118605007900d20a8182500040191410000041d8090520411000602 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 410747760 1250 410746510 410746519
    0xa05010302041514040e0103060f0513120311070c0b0309010624120209040c0315081b0d021c08041d0601050a08101706150f0901030b13060c02010c0e030c 68
    0x240d490f03441c01c1e24201c0a02d40411100c5405100000d61400503a5160b8001d500954000c40c281212501500860fa4000c00440c07880781203000c080080748101d01014072811403810001003001c4100c8042625010b5900d0081c4880c99599001c220050b6031000b0358060070802c0000e001141e01d801940d681c030102841e00c6403440c024185e8000d149441510701c144103800004005181c181000007040645aa01c2d960a0209444003014407650300c0325101403006060b20f178081c00d00b06100c1111110350340c049120040c40b0300c160b420381100759550b0044112108400002a0441c81501c0c40d180d809900301c5c1c8100082881c654160700140c07a0922400741c42150140d503014500f40030b000d01680c0108000d0401c0580100d0f107040440d40403134241d1040340c5c01d09208001e2480313140000113500185c0540d021300d030140d10403291281598039802c0440b41920782c03181381070103d50b0303401c40081c103600d8042002030700c15400c009810701802d070117500640c0100000e0307945000450304c031001e156460001c0c1c1c180c140c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 410749010 1250 410747760 410747789
    0x231003020f0708070b091c0503040204020f03090a0c23060f04051c060b01021c1110110904240b0f071b05120f1e010e070801060e07080f0601080a150609050a0501030204 74
    0x2031f41e1142c4025035100b48014801800c1140c2c0f40c2c2014180d800c01c0b03c0750401a03001c1c010001c11300c05a403004000030409615085000c8030800d24142e0b84030001b0001a000d070300c0c0861200e01c0750f45544260b5029100140102c003840307803180c0a410b02c00b02d185030143d0314280307032078402e882652000c0b0345103000f03652074900d60103407100503907044540d40e00d5807000d011f0600070b00c0ca0627041612380380108810807a0740380800b82c40e12101c1003004115070342d0b64050165a0200600880303460000760050045804100c001600c841203000b000c1034038400d4401c02415070714200e800841c0a0032050100003518429103000b8a055041c0903680d070340d04071081c840d4501d0381c04120340300d1910a214003800d44007040c040000ca156800640c0c068500300c11a006000540d445240c00d20481000c1e50700254040400d24049070541000609050310401c0a80410704100e61000003e4404c10300c3d40045511450002d00d40040c544d4030780004242114a010305031240240d09000100e66105c0d0080c4d4003a101041c1010b601d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 410750260 1250 410749010 410749063
    0xa02060306040e0a050631060902060d060b0301030c050418120309020a030501061e060c030806010905270a0c023a0f0207231003020f0708070b09 64
    0x8640c200030002944030f901c079034034015a42c100740844a9820720840050515003841d01944055081641212420720052a00b007280c41d01c01c2c0c0101854150001c2000070059014004a01c40c0d00c102c8111482d201c2c00c01400080e030107408401903040340e000718044031007075441e0010003060303625030b038540440c8141c000254008202d01800503600309a0604000400001340d6001c00d1112407254401e50703403a50340361000c01c03144800c3c400884600c5c85c0c0e601d03940d81d2542000d6001d043d11402c034002a0402403048000b07078080e4003421414004c0c21004020002c20340088820348400b0400c1c1c02910612205080400c0c15001d041c0100f100024151700541400f80c401c40c1070011002d805072400310074103100720882c6140c20724240d441030b800e00140c2d02c5002850000c0d1019240440300e0340000c0c8601e408460710100803a40366a0f4100f00c0004685a400100310f8280881c0640154074076140244000207140341044959001800100d1003003044800c10354410341c1460f00d03040f0600c1c484900400a229658 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 410751510 1250 410750260 410750269
    0x936160329010e062712010606050d02030a1503050a02040b030610210219030c0b0403081803100219080f040b0c0f0c10090308090f030405120106090c03020714010b01020a02 76
    0x20f00028010b40000d062080141d07190306100619801094410082c901844c0c0605000d088001500d070800000d000c114071301140200a442074680c00401c01c0d501002083e91400795400c541184146801d15070141e903200d01b0700544818050804034400d51911104914a040c00310b43c0c9881a030f0500ca0f450100c034030b010000c40c044c2d070b10485000144108000040c00580d511200114080848610420500e0075031800d602d21207080c1c7c0004a501102344000c00c0001c2d4088100d418031521100d10b0300b140d5204402107480d2904030440c00c6c000c1e90000c80e040741140031b040702c6100705840c1952003100585030035032480c0102c94103441c042d004880d1080001c0443c07007840020712021182c02d50f45460156014442d90030140030701140f107001a00d4140d0202030603401000107400c606030314058685d651414020b140d613841948506409403070750b40e02c4d90100f0b40003940300300c00130014a03009000c81286424003c00030741c45600101c0355660000700802c403a0405200d610324008041c0c009100c02e900079002c11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 410752760 1250 410751510 410751527
    0x12050d05070e013c0905150304020a0f03020f040e0114010312030c0309020a031202030403060e0d0905010e10031104030803250c0503040e18030726093616032901 71
    0xa0140922405c001807503031942a040e420101900e0411500d03401c20b481080088091540010302c8420400824800f60340c48043c1786884660032580003580200280c141d5015140c09101c900342032001400010501031036400c00c40e000380d0320303540c104803245100c102601110210000a5040307904000e0520014a4014145a1076511401281d040070303920782e2843c056881c018881e000c2a00802514005540c111041380c010304000d0900000001c10040811031a41d800392101c020983c85c0d5110368541c10495045601a5400540d401d50f20719014142c805031604071140304a0102d40500808840b034807400848920952082c0603504c0d1903e0f0655070b84807190b003d400203151540320b210015600a08100600c0076a1258201c00a440f69001d4907040000c00044070200010f41080404000c0d0340300c890b8515071130660b0f102e100f1000c84000000e00c143c0d41c1d501003d41c80440410510142001c0760f00c0e440307040c001e01d58080c030680010000084ea0030300c00202c000740040300da0741c0f49c07800c644c068241e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 410754010 1250 410752760 410752877
    0x1116030c1701022203060b0a030f02040c0909090501021b0c09010e10121115090604060c080c0d02071e0b16030e03010c1d15030412050d05070e01 64
    0x150400411400205076914400503103151582c003400d0800070080180a951f00010046807450200317455134542c4049080080002403050b5a50301000e90407900513030704540501a8001d0421807032403d80380c164002d40c05070320100b8241400c001070b80e01c0d070314000943e0386403041c01a013280342d40d91030402005000c11001d094106800d08a042c04601d200c8c0307501280c0000f5005903940054268034034140962816040c06201407404100100441600d4540440741101c015240c040d0025101d814012a54015888400384078083c5e05080d507032907680000d100c0d09903043c0c803440014810a100322510094850b00c103406542e2400d111880f040c0000d0309040840e940281054000003080d54006801c6440e000704c0303200411600000007030500740c071540c0040400ba01359146c42c000020351036001001d000041c8018400d0401c0c41e10182c20700d101c1c40c00d0303c0741440d0803070050259050030600034012000803156580011400107080b01520b013070343c0e40c0d01d01d03007c5c000c0c8010045400c5454580440c83c0da00c1034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 410755260 1250 410754010 410754013
    0x180b0703060506160b07020f030906090301020d050c04030b010806040507172b020c010905130c1103030103060515101d010315140a05010513061b02040c1116030c17 72
    0x1c000035a5202d407001404030041407914101400007070310b440480c1000152a80086521481801000c0c0f00008101e03204c4144c1100c0301071703e40940c400007a0181c490700c444c070008135003084d043c000e20040307030f03c0030700241c078801c40406070183e807201a03071559010210340150465009503400c11080413082070400e82c581044065801c098007105c1900d030034442d088100502c840d501b00a0200d11a4180a90000000c2c02d180020b24903182c880060542040c16420052443d0384092000003240540d8402c50044000c0096070340301e40c4c0d07030b0406000074201240da40804200d0661062024900300303c0860f401c0c072550b2600b60080000400c02d82e1510304d03442c00780e0706040e66001c00100d14504003281400420241030355a4240c6107450921103101240d5001034103120003031010803104d8484956580555485240c01029646008540c1018090380d00000c0c5d0400d2a040300c0b260126440740e409031442d40554103d03410405c1030394680942051030b12008d840f00c4031448c014021700703504c81d450800c00080b040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 410756510 1250 410755260 410755271
    0x902040e25050f0a0b0f13080c09060108090d03050402032814120301090e0102120a050f0906010605070605090102091206040b07020610180e07090b0f04180b0703 71
    0x200c0151420700c885600203006081015500c81c00703800350940c0400303040203035840c070340c0701c030301d500201e42c254130240100c0d040c41c5404140c81c408060b440054036509503445060303e6503a0341d038041c44c41e00d40c902d2100050040011600144455004c0c079011070103401070000504d42200c4a4804038000c00014201301d03850b010340700c44074400000130342c2030b9003110b81070710941c154488a0b45408103c4800040c200c6681d0f0b000000c0483d050441c4200b0f4030704641c1c031300c0c4020130741a14400c83c090084c498061100c2982164006000b048156580b140d0b21034420350a1544043d140c100c035466490109114440c00940f01700945c01c009602900550f82200c180e40025080c0070003000010b0206440c4680c07032030180e00240401081c0601a60013a0300b24095002a15150602582c600c1c115000f60044145134030302d4140c44079100d105944480341284041003501c40041e02e903003c08024000800b1040d100e12600d41c0c1d04182441c0c144a20440d40c8500c4406070ba0b00d4510b69600b460b00303440181000241a40c81 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 410757760 1250 410756510 410756531
    0x204020306030717010c0e031902091009060f1502070b0f090112020a051c0c081303020312071e080c0406230415031406010e01110705030118020420040504090204 71
    0x13400880d00d5034201d90000c61200307041d0000030440049003600390710035404010380c0c902804054240500181e0140c0c0c449180c1c0c0c0d039000d6201441041e55100c501d0061602000080042150301303608152180c104850301c205800030422a0355111a00411826040030000f40c0480054034000b40b10030340040c10120218028003c04000300d0300440341410100f007000402c40000c242d03580c147c03840c414419000b00f286031a01c000c001c00361107004288255880e0355040c464181802081074500075000022005400d2030034241c020900c0d2045001d08074944007404003120124082c655141c4121020034040e0300380340c070304081103510380c440d801e2004408006480c91401c406114008202600e040240e40d0422241040020120b07800c00154204038541041031100c640e07031000646e4000182481e0000700c11a01c42e01060800c180c1e0740c0480e03407641c80d00c2107001c0d0005039030861014880c001c44041008515500c0d005100a80381000c1103103c482c1080140114600350b0310407002035001500018849404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 410759010 1250 410757760 410757779
    0x1703090127060c08310b0a0b010f050c030306150702060a08151f120b040608160f080619090b070309110f1804020d1b170706090302040203060307 64
    0x10089950329440759085240180905800b940710012460314204045207052006035002d85041c0381022440403000011603007100401910300043ea402078000300c0b4900f04220210010039121220710702245610115209a6010310203403025840d08001842c03840e03985004010703401484400300108650103011442c09611170401a1012504584950ba80e81c144403e00c000141010030095209001d110302409035408801121110100103051808447c419044500086e0200c240c150307400c546000d100080c0c8400008180c0c0d502d80380b0501d090007160300c8038041840844140641e0800358440c13004644c840321040000c125000e140c3d00009a01d140650b9114558401680d42d1070011380c90b000d4440034071014480050034282d040399901603004010010030170751a61010b0002d540c1c6c2040000038150349580700d42440c1507620580e6020300e84806031020b0a041c115000b686606c00342d80c00803603000100040e0403810b46031940c0f0303110310881c599400c01010b9407000744141d4050064001c0060705140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 410760260 1250 410759010 410759051
    0xc0f05090f030703170a0824211902040f050103020f1003020c0118031d01080601180f0902030f0f010f0b0a03020d050106020708151326030f01150c17030901 69
    0x1c2c12400703039546d03424420001d007000406840d0b1500d0401c50b0950310800c000c0e00740c104c3c2c402c103025107041208102813024011f20054000542c041802400419035000340300003c0d02d00e03440d02c01c0340d00b003110f00c4048070490301311182400b000790407a81c0c400315921180740240600341c0014003480c0c054501240325096500303481d20b1500d00d0340100000c1c10712004250304040910309400100410301e100464420000340000005003042d03050050f0304c4225040d50702415001009031201c0c00c2c054560300ea0f903950780d40080d0710443c0c440b81300301618000310f0040900000c01c01d04031000304000c40746241c2482203401302907004c45003030030505074200075098400390309004650003800150040c02105142403800c07070900100603002c2d4100311444080000082c1102d03070b40c00c82d094005411030944220302c07008040c008445c02d0a803203840801700c10411205c0c10015040d0583c0d41084407840c14130f0740c01c1810340b00c21190030750081c0151260400c0307544c1001d802c4055a4401c064030b0010a5818001240440741d15 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 410761510 1250 410760260 410760293
    0xa0302040b220b01080105030115060302030c0c0a052401080c011817060103050609010e03030c0a090816240e01080a0b0a0f1a0f0d09020118080c03010c0f05090f030703 74
    0x680f10a2054580e40c0c121510710b0041c50309030002d1060134024058001e55520328019032080c5580400410f00c100c405070300f900d00302488001194550700f52400c002c2d03500c041d001e80c500404080703084003002c18005010b4280c12a5507000c000c100c0944000019100c144010401017155141c01d0800030701207a4898042d8151961071001e42081e50560a106007001001840c000842c5e05104441d00301c03000005c216640a1403040c0c401e610741180450171034108025501c1100140b1503210800d8115542c031600c84212507070012000f825888103101c080b0f25161503028980818114044031015500941e401d80c2e01c44104100007038109503202c0080c403101e0f5140c0000d4504007030f6100600064020351038000c045041c02050a080000c411030074009c0c0e01c00c2c284c110800641761000c0fa03003164014070b81640c42803843e1214140c2c01d40c071003c00310341d1610b005c900c851207503080032014003e9601030003203440440f190390343e920716207640b59050140c0700c50301e807402640610030300c00d00101148030082c071340d100030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 410762760 1250 410761510 410761579
    0x5130b0d120e01020d020c2b0b0c041401020718020c07030209070c06060515031303030e010504060e0c041109150c01050903030709060f08160e100206010918020a0302040b 75
    0x1e00b40c0c4000249882d5200f803899055622030b960f03600c0b655848000410703805a0005800c80b882250000d85141a102c40307200074100d40198040c0461805090040c000382c0e10300108840141c4442001261344400034828414420040e0030200400350942d0000c081c2c800700d0900301e541596582e4085210740104407083c0c4005011565618100300141c004d0b800100000c6504550100307072440e00c8c20a510020706496008909a428001014020781245c42a64401e400801c2186001d05143c4040d03c3c800903802c01d81d0041c0182951540340070300c039120711401b5400d02c460804011006000104072031010002d1400000c1c0b11400024400f4083c19210340c101a000d952a4201014040d100040c1750b049036007889949081804072550281080340c0c010542280b06d850003207016402d4420078103007280d13103804c6035000c25140000c58001071414102d4584642c100031a00084034807406049130418001d41c80726081d00100050301d450b422140440c0d600600c6007464040030640359110103060000341c40349 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 410764010 1250 410762760 410762777
    0x90b0301260607030c03140c030f091e0309090c13052b0c171b1903050303090f0d030b01020c12070b0c01050106080601110d1409060a0201051504020405130b0d12 71
    0x8246d2601400c4490410800006442d0410601c60840b600000345035440d086958400140420010040c0980c18032103601c055420150065101d078a030b50102c5003060242e520795010808190680c400c0750043c40b203010950314103d0400342040241500103030341700120500c00303542006c2d0300035055046c0f090501ca040c515071180c1c581421814800e0310b10907031103d03a41006c1d9041c07040c04c008105983d50711108941d01c1d0084400d500942d240c07000541c00c0903001d4440030040184010000694820900300c0c01d084814007440c4001c01c8007a250100f40c003030300681000c0040101401e0070700c8141005014481540c070981c1d104d040c00011a0840c455421440e034442d00108070170340d040504d1740e41080c800e1901811403803a2541c1603a0380e05c14007100d801084500141d55500301044816070710074030401072200303aa4001e0303000000c0c042c06080e110880003030401d8441484510b0a80b084030700310380c0e010744000f100c0b100c103c1c1810000c0403068491b94005030440740880006840ca202c04001c509162140c00700c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 410765260 1250 410764010 410764031
    0xe011e08010807120209070c1e0b0402040b0312090919110d0c020102070c0e040f2a0b040302030601170703051219031a100203070f03031b090b030126060703 69
    0x2c0c200340e41c0c0c410300c80c61255038500030140c3c80795208940d000c0d1f801e09001d00411040d1030080c0c4503440f500042c0207482d103c070158070100f2402e0314445000d03a000301c0e0f05000140107c410141c80c0d002030609600090700400000d01c00e41003003061141c0c4040b072620f182845440000304101034440e004450101c140002401881c1030744284105141c19119200031400d046c803550b10304120403128000c201c030740d591400c001410840144000d103c01c651100d640c00707400038011758038000d1011010349404607843d081000f240c6101c088055904498005008150692800d20403c1041c9100d04010b0b0a5020300007010000c181c0400500e555251a0181d0640d2800c060b0145220381803521001e004041c1486132070392001c50030b0510303014000c07021942c0320b40303c0b028031000f60310314483c070500245058210340e980d8040c980c05601c2040640c145100c1c1900410381040d0895216040340259100e10a051006103c00c0301c602d100c4600d0007204554443c094045503025500d0004112007040c0000e40315a10401d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 410766510 1250 410765260 410765263
    0x90606020601031415040212030702031e0c0301110304030804021f050a030c050c070306020a03060e09150c133b0105040b06040305100504020616060204080d1e0e011e080108 76
    0x52415150025002c042c17007000d4503100700380b07010713002a200d100c0141d44101d08003824001c841c140c541c000c08a58030600704075a0145094040011860f05004412a40a403810306005440d010450034210030701d1030390b90b0365042e1605a00640240c0e00803501400000159120403180c01c2c1100344c035245c036502d420500c600201610701c800420741c1040f03401e1040010b130040c0080e40409507030303104002503117a041c0d030041100103003130b241c0c001c0c01c5000440c0705103d58070001294031440c5850025020710180d450900c1c190442c031407400c44c0905c01007110010080c8414800b00f00c0c0c0010318181d003442542800901030044c0c1c06600310041c088907115030040140d468140304404c84520141ca4103820285540c840e15202c20351603c0207103a058a450001e0110756070700040790414042d00d41440c548030840d050440094015014040c41c0e031040700f0011459a0142c0c80640b00384480f41c041e0842c0003140350080300e40e0880e807118141840341c581d001e032000c8481d55441e0b1108041c0369980848030740c945120607 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 410767760 1250 410766510 410766533
    0x1f060806090a0c020a030807110d03150609030b130c0b030c0a02010c02060606070624060206100f0308041205011104060c05062a130308040909060515091603020409060602060103 78
    0x412030366181543c486440c0b5000326941d50510340504040403036a80e0050155041e460310055502d02e8094052410307910382d00f60384801400c00c45000000105c0f41c8504040d2150501d6020190041d01c10900081498040392015541d00d407049a001508030b643d42c1c18490660000d8072004d8840101090703c08010380d092141d1103101009200508c2c0f18203001c400300d0a1440b80c4080508650f4a6049010746889452407000141c001d00075520b0480d039549000946904003039980c148140501c0c000065082503142ca08403c1d80d0300090080c1c5000c0c60a0164066026000d9003250107548030a00c0c504412100d0707010b0401064181c84500180406142590404400402812081615400b09442d42039000180c40c04080c0844080c3c0da01c0e600351100380d90b9105a03a0004091540000f0701240441c103a800008569215079018441a01d07640301c4481d03c14008902160010a42e4000403c40a000d6050004020071801d00500e00f40c1c403a130210007651400d80006002d81d00110040013003152803a400d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 410769010 1250 410767760 410767771
    0x130b0913050607020d0e061e1303050732040b0a0801020306040606020313170f1c0806062b020409020408011b02030a09030213110a020c01110c0310051f06080609 71
    0x180c94017055444024000480c00c41c1d4240c024400480c802c0b4040d011400855200880c00d144030303031038a01c0c00c00c0c1c001040710207020465580c05400c000141003481581b1b80c1d03a111086403440d0b401e17151202004850b107001c00003450b510030344455100c68240c481c802c440000c0e110940003d82e807440c0000a101c2a903080380c1c04a000c543c0200502c0101e503030540c1d060300a031817403910210100da104050340d52510246200c8035103140951807640c0f43c0c07212030000d4028901e001e600c900c022952035108009503405900641c4040ae9900144840f8103203070703105402d0a502c49500010304050310791810404a03005604450a161b640d03405503004d200d4804500da2210701c1610080d450020301100081408803a840028014240048200441401500403202c10148444a980c07100d040000082d80d07188604c8034503000c64042d030322074100002c4c007040828001c84050003d0006a8100003401c000b410010002c28041d504000f100808126040c00760009014035034504140c0d0500c6401c019190502801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 410770260 1250 410769010 410769013
    0x1005040c0e09010306150e07050c06100303020318150703180b0903150702010f09061a1906080603150f01031509020a0311030705100f1101050601020a02130b091305060702 75
    0x24440790755807039a000724150303588950301103402940f117081640d207600560042c50b01106400100800340f13a009020b04420042441100c207a600e80381d9460644950300d000142c0103030010444c2810101c040c907138011703410304050304010b03c2c981d00b4542c01c001c5811200c000c03000a018045861030f4034141c494000e001d00320810080340740000000000c1c0e0790f202400c8141040e40e0340b600010300240d0003036221420555090405110689091074883d000f0518503244202c1d000d19450721082c03a0420308032180c8850719004804c0e44550401d00140d0f03550b1402420282d1603c1f40742c03803162141400d140c501e030107407240441030102941107151083c0c48030141d0194211151a0090007009070740c94015a80c1143c2e00000034000300801140400e007088159013002d9000510100d01c0c03018540e220010340b01c2907202d9a1010402c100d6406040e0070307180156680b5005910400b081c1c80585802080708541d040c14410004103050104082a41c80b4422603600305840204140c50090080030711040b07900c100c81c2d10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 410771510 1250 410770260 410770277
    0x241b080c0f101a090901020d02120405100e030a032a0806120a05060c0702180c030a0c180b031806070f030b010c0c0b0c030408150709080703080319020d051005040c 72
    0x1140c0f4000d141041014034440c02c005000f10750003040070b50464003801e01260707055650b092019400080b8400545040343e00d4411000c46003030224091142003081c0b140000a1480c1c9808184100d0151000100303509410b90040300c4a40c101a4141c40400d10003065115494149010001c201c10580e02c080140c4130b03604404100000904080b4038194442080d810198440101d0f001190410b020a1030007402c240542051104d8103e801c80954400c2c214020144038000b24007c0c00c070b64402011040e0b0180c10b00d941030900c90304400001640c1c1c04079400004003180c0d88441580e40c03900000b43d8120313002c101251800c0280980c14010500c900000f03080181204449540e4518510007070f105041c19817001148608a1a500f03201f22001405518212041d940d21002c0440c0f6442d0140e8100340402c1c0b44070000640c81d00c0102e0344008490700484114116a64088404100140d40313800d81c1840ba800c001c00c1d28a05002e10036540210302d504136440502d405c000601c0308407000054801c0c24402681e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 410772760 1250 410771510 410771531
    0x30e01150303020114040f1704080a0c05031204080601050609011125050a06080609090115030515010f030b0f041a010612050a0e0a1707060c120501241b080c0f10 71
    0xb101f9003c1d02907000c00a444180c9101c007052045001e00e42143c411801034107140c1c014459000040d0040d0b070303411000c0d00c941101b8800e103d00c543c4554400c07108160428001041580342540180580d10303410b0500208211072684490b05010f00130821400c82140d8005012090109181003005071034183c881c02c100d241468030240c440354008024511803441140052a400820341121a1401c22500126205601d0b45002910340e140c2c228171640b00f0b0812000020300b5290700101c40c1c1180e401c9020603015448041e1480a0b5450090064900c032001c040c5904540d00710281d240d0080500da82e49100684007008d4050a5460142090f003459080200800054001045111030395a00ca140450003107007152200c00a4010203401904d0380303140c05418046103401a040191213030640104000030380e00c414a0000361780f14110500c0c0000b205050b0001c1c0e41e801011001d0401c05505c1004031802d4095550b28440d5102401d007605540281015100b4400708104210115403ca9000d010038041c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 410774010 1250 410772760 410772773
    0x509070e0f0103060621020904030c080f0a0810050622050a06210b2101090602130302010f0201021c02030c19020d0201060e010b0d021b0d0c0309050d021e01030e0115030302011404 79
    0x102a80a8840d008d1500880d0400d070040c0a8052800c0d13002005c6a110000c0080e020410b401c040e40c0c03070020270b40f280002a006410503c0d07400035036100411140c20510502c0c0090400703028000010004035500c0c10200303560383d42428410003044a030781d80000c10159060342103c2c0b80b00c50203080c000c060a1942e409000c2c2d58400c691800300022010920790042c0b840000303030140036038280145c4003d20000307082603007039002c95105090b24000c1e2501c10011045d140100d080b03220741d580c207003080c466510590380b01d800c40350011a003100b802626070b030415590201c0d400001303040c046c4a00150b030246440324600d580a0080100900003614201195032401c02c00c070482e40b180c3c0b42c103190665030000b00c1e481c08030300c1403001c000f0a04c00d036011211004020f16001e0007025081c1000d0b40401c0a50340006154640007545400036940901340074404103600f4400031500d40220405814076880740c0501f512418248102103642c20712082c0360021510354200030342118040691920782802c41010080803644 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 410775260 1250 410774010 410774069
    0x11404090f0b092b0801080a08030126030d06051c0c0311190e0702060a021611040e01020f070b0c0705190606030206120405070b0c100509070e0f01030606 68
    0x1c011109808641e12003090724180600d140303100412041d03d0254100084401c11030380700400c035949039001c5c543d0300e911081d551202c000380000e04a000400060140d5404080c00070740030450000381040140b5102c444c1ca040d0b400002c0208005070382ca50003084140307403803c120200c03505030030010810324a10740c880c1e00d08103d482c0800381000c3c42c01c04030940b26884424140883d203005c100703568030554a50161074407444042e0381c90f00c010700c20740010070106d1004c0e01c200c81141d0042d0840816480d081d9031048040c08143c4040703540b007503a030002c0e40c241683c20b00003420b50001101d4525171b604158035210b1410300001d080140320310014440d00e000201d000802030460f041907150b010001a042c035010000c0d28050300000d400607000702d130f41c10108500a400c0c50180e4481c0c0190754281d500c9158100960003103070344940c180e0380101000c019459241d80120380001211050701d0f070392600c034079600420f21003d482182c100d03401d000040051000318400c1c040a001803488650a21500c8982c9951220 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 410776510 1250 410775260 410775263
    0xe07090207080d0504030804060b0108060127081b150408060c03040f080415020f0606060316020c0a06020a03080906041a15031002040815061e060f0d05011404090f 72
    0x140d0009404007804400c005890011103030310300070b1142e880c01e80b50041132030400341c0d0101c50700340c02c004480c440742d130280f24850710400040c0d6030202c012403031020806c00c281285040500b090505040850781c40f10034400301e021545080e03c1c180c3c000401d8001d003d015062501d9441b50a0003d1006101e080310205251390413001daa034980e5200e494500300710b1758480310403000a00040000070300150168481d40759404c0c071070807602038400c001e0102520b0750321140e045800e02d07400101040090800c03100310803000000e8280d0320495404a02c2100401e402c018283c05c0500541e116510103400c06a0111083c0d901c40903000107040c143c1400e551340d1150412141c2403c1c02c2c6040140004c0041c07040780100a10060000e0071102c1c402683c070b44620003984140580b105501071500800d000001c28440d05005100103005105c200c28090801c0541010388922154002c0040000710790712820000a000c464542a4000407a5458289500c69a14894030040d0269080c102c4c0784e808641414030b01c0b440326 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 410777760 1250 410776510 410776529
    0x61d070b0c100c021009031d120d08191401050a0602070e040305160b0f0f091203060d02030c06120a06120206070b0a1d03190206100303110a0f060c0806040e07 70
    0x2007510043c00c4c0c1c1080245104403014911782030500040c9a4490300340440c0e40901c0c0c4044507c1d1500100780200b102d8001c4d40440180d101c490003902d0035209000499100030041c80b074003000c00b4a4040d800c20364090b0f4000c01ca01005601c0144110b190940e29a801410940004c062882c9490320300003c1507030042018090100204048841841e039214009641d507005007201c0d0280b130042601e0300600d43c00d55103034510022102c00589010000560501c200150403501c40c107580d110130070070040c0210180c0c2280c06001d5101d03600041c2e262280540314444100d11000c10b40c4c0b40c041c140074129100f6078080154080041080c60250b1148800c9030841500310690b1145075445440c01030242c030185230040e0b481c11040102802801c404009008900913800030180001161a001ca0b0b480d0f1094442c10000c82201c0000c000013402148000200c01d50748040d20500764040d2030321802940c0503282a00c46a4840d0003201a05911043c415440041100c08000c01c02c00c0078041e9507600e80070301406c0c000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 410779010 1250 410777760 410777771
    0xe0a0f030501091b06090b030a0f050c0c0d0e010e040e01020c01141609120b04060608070b070506060d02151602130606030c11030f1c090614070309022b061d070b0c10 73
    0x227030307080d00300b035414100c801001c2c081420304541008059000303140c221441c1c060449016002d9100e401c0d000c00d4400c05075150783c5000300320300803c00204805500d210840d03500b00126400880d0030301581900519100c54100145800b4900d44a818030301c0f5011000c101c180042030281d0207030800d580700401e4020b5524905990780d490494010070b00750b045044244115503001408210b80030040148510070800e5a902d5151601445900009068001d40c09002ca80031002102d80d81c0c005003220301103910310380c1b2100c280303600810610401c6610081c405d94a445052003202d4060054403c8660245070030011000245607003902d0380130700c101c0c00342c0030400002d40c0305000b24074072000c4107a146101c03001c02955940345030600040600384c036449030003243c007000100c0c2203029200b28002e140d0050480a0000303c034444034403540703242c0d04551100107250b94040001c035041d480b0302c0d041c04401d21809100c0d103001c070004074600081030340164406842084050342460010821190243e03010801194 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 410780260 1250 410779010 410779021
    0x40605060f09010e07020d02030c0a060209030a0c140f03030702210c060c070614040f050603071715090a0213050d301b080a0e0a0f030501091b06090b03 67
    0x3a800c071240001d80c400b80c8100007080390140641600d00500341070b001c84003c880001010f07a224000c3c110080c0291304014100c03400b00ba5a6001460625401025034959100a50b01c42c40856211381080c5260030410301d5030000750400800e4010341c00b00840003036060040603400140490840c6405104500130381000b00c040ea01c04001080f078905004000945810758151289c2d42c0b070a03d41f09650014203030b13610075041c4402c410111400c0d1020702e00020300302c0d42414140174443c0c2c0080c0c800300810402d400d560b200d88100c100740301c0c0511901c040a80c6213140207410000a40d0010702003e10706441041660011000c1c5800c003000c0b94820303119048610343d203007812001c41c61000f00025181c0c00702c1c1240d40682500340300e6441c1c0c1e42c07040c1e01c501d40e20b4510301034420400c030001003006203458130403c5000301e21b9000c1d51060400000051800480c503440e4428007038213003402d03401142c4980d10f6035035100c100309160b18120010810091000046440d00500400804840c801d40070842c0e40080400e2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 410781510 1250 410780260 410780269
    0x2d07060e0a09271b0923010501080f0c120c13050a05130902040e011b110309011202160203030d0c03180203060105012316050d0c0b19060504050c070312060e04060506 73
    0x580d04c0360082e1043c0c040d903440c20441d0207070640b03000210401705040361840042c044846014180c50041e07403603260307070781d940302c1c86440090015103035411b0024148111210b020b03600d050b8074031807401a00d1050302d580d04e44c0d80d400d44c910b049400541c410101c000c1c042c40309490b00c03038440c003035070740c0e8204041201186400410018a40403070782c01d1481d400d001542420708020380402081354066030324684a045000039035900e07030203121421070029083c00f00d07192001501e0f0700586000c2610740441e403503000c81640040c0c07860f4041000b10100c170f500d0343e0341020b00035003611a019a042c4d14900c1c0300b007400a5580001d0701d402d01401750340e041c0700000000300c2c1501c0a144c0e00c0b894110258651071b41d10b54864688403810840b03244121850300c154114040802d00c501c1c01440c2180e40b0204400280e16440008188924822100381200360340382c01c005459941d5000e07031806204551810741c0e442280c1c0c04c1c024400c0321640727a44030b040e609010b820000c1031030301c210503030340503821a00014490300d4040c00107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 410782760 1250 410781510 410781533
    0x60f0e011e0c050f010e0c090603010b100201051b130e1308070602030412110a2613080c0a0b07020120060f0a0c030b01022d07060e0a0927 61
    0x40c00070003089030a81201ca401c940b903014000f100c220003a40750081e400d840160700c0c80d2041e500328511741070090521054168100038000d00110f80044564003041c07403c0785403801c2800507074440c024080340c108014810464100a10161468501c0c0050344140414980c80b403081040350642c0014900322107850b408800c81d0b4000299039490006041c200080d4206940540f00e400080310202c0b40d6a00448001e01d140040328050a0160116140e9644404000d0801c11200480313007880c01c03400007050000c0c000381c0d020b01240e001c40303410324045031b00c1e04580c810300c0ea006101c1c40302c06001c40044502560703001542481c0062505081440111196030051035641d098030821061045c0c0e0484074200c00c5c418031502c43c0411617480e005804906031050000c040d4056084081d80107008a00c0111082a118100c074029140c8103075501a41e10f0000c480d840f000014850344100822340c075015030880028803c4142c180440741c08200710000018031069060b00040802018004021501c81d50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 410784010 1250 410782760 410782787
    0x1f050a08061308041203030213050f090f0702031c150506030609010e0a060510050901030c0503060a0909020301021201061d090106080c180a06020a0c1a0307080702030919080f010501060f0e01 84
    0x1205e1060028940900a0b401182c14168100c10710310012915082c00e5800d1180e10500518401d03543d21148001c40305280090004811400f0070810301e841c45501c0034428155071442940011042000c80b40f8914011541d00624811502001030018a0742e40034075190540301080c5600742d450301c544051000500c3e40794002a00715941480200f0b9054001018010380c140c280c03428000c1d11001c176400c551500c0200d03000c923880711510100f03001000180d8003000040d440034000615060000846042e1800c00340d000e14005075403407158042500700c1c10600580c0c400c05440481c9107504106011b400b00307000230481c11900d10b000c1000c940b0006403408160308002d0140103191000c2c0c89240003902c0c0c0e1080b0720b003540c0b80e030a01d03030001424030508074645040f43c150140171425074661081c100c03110840909030a0441c8400d00c0020000c0c2e990302e8840044032100b0021020706460096a541085003889110003944d03d080c00404c01d00b90000c0744a084402c41c0d1505807031040940f03005036600d8404450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 410785260 1250 410784010 410784029
    0x1410080f07030201020d18050a2d0501140915040e01060224072d0503060411070f0201030903090902030a05070f0e2b1e1406010b0706231f050a0806130804 68
    0x1000103074003c54980d80ad02a002d14911503051041c50203200540c9070089c400e1a0001308a10380c100c2c00040c4202c045d00c2c400c9001841042103420351801008641c010790440032b8041d60b00310040000c240c04000304030500c0c00514500203100c885403085445084014030071750070b20407885903143c641414030901c40a00c049000a19459402400d001007094101700c0d40d1900a920300b002480481d040030703090361881075100800c00c5060003164011001790444400c1102441000407010442c662240003030f43c8202d11200c1e00007550f1600d070300010000da0100000d0030a010a5501790251900c1c0d06400e21914407031102000c0c5280790140c2000d03068400041e000d00040402c60010300882400102100044e01541c0c00000c00d07007140000c0340d00c0f04428860310102d101c2c1000340000040c51a045488483c2d54100000c1040010026840c0c1c0000200c61000e40e50341e10410302d00700c003010071000f48064a410340f401c0e00580d042107121552190050013585107500300d942c4920800c209002100c010704003142 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 410786510 1250 410785260 410785279
    0x40f020d111c0506060a0f0308090111121e03010810092102061501030e0618030d0203010e040b0a0c091703070c0803041a0a1209061410080f07030201020d1805 70
    0x180b068a03684800c00111458010390011404604d0070010040940341c540e00105d111529660390203685901480f807480c180894407440c1c90702207009004803400c24150040c2c696072030008040c600d0341401c017041440201c000c148014007610400103101c03d06a00c2011000400e400c403400d005500d040d10307550420b000e115440804c0b070200e501090480c0240185030312001003001c04c40054003512200c0d004036840b07a100100080264034211074130030155911200352443c0915441c4848140e03442600700000c14003410b8188030401076203041a0b80d0160f50224100043c0e4040b14000f0b1141ea8140b0070300440c40c4c40e5040080854500340211101d030341c0d0121a00c6c5195036241c030042d80381d8106102d08008018000000c2070b1080340c0c401150410000c1d44e807904003a03031601c40d51000800c10074905440041c3e80e004640c141c054101c40560207202e6940321aa051440c3c20889440c0080d802c901d801c450b0000441000140d030000382c4500e0360340e0305060200f8156100410501411042d901c599800100070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 410787760 1250 410786510 410786539
    0x11409010903030b09061f0c320f0303150406080f06070f0f0e10051c050108070801020f0403170c010603030804020907020a051c030f05160215040f020d11 68
    0x15404400010b00c82d031010311000c03125804100710354108807142074200d506442e0201051929242d0360707600000e1070070300008079921512810030544070f01007814000c41c2e6148101d02103041c00c0002030380480c1000010038440c0c40494016840340000b600c9040000b00c098030700040742c0d580350400c030f001e422500200c600c8120101342059545409540010200d2010491002e10911a040c0e0f46910342d45600d03090000417409040c0705000b03003000300000801006000d0300c1c0000d00709a461884500340e034240413480d541000416402c02d04c0f65403224226a1042124000413000b903415141140d40046040c0a0100b040c041c40c040781c491400f42c801c0c507500c2c00300c0100c01c164000707081d14080c41c000d950b061215070301c082d800c9c0d070b4400c00404080c0c46544405900050780480b0428141d030103c00d0318010405003866840402a160151100c07142400020307480d400d070703d43c100b040002284144e0048002420180c0712403441c11800180030303000c2c1c01d210070840d003848104020311000700800740c0314626001d0903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 410789010 1250 410787760 410787763
    0xb0d0e030708030601090e0c03010b0d09060c080907060c0507050402030a060302030f0a0309050a0501120e0705030d1101051e040f0620070c060201270f050303010f061803030509090603011409 84
    0x304c2e0b10602140d0480c4003c514151014565071244030345d1040c0600d9a4203005d044009504400070300c1c0545612082d840300051014000c440031000951241c4032142030165840d410415160000300c00c10074101d04140102d0000502c6c4c001703c5400f0f680c01a41d0340c0b20b50b5800800380c5003079040070f074142c420041c441000407000221040c10501a98a4440c07981d191400c20001d484039204490009100c0101d50900e44410f501c210010941d84040310005691440440e04100103000000040740c00110a041c4030f407402c0c05400e03070082c02502140540408921a108103020140000e0018401c1507520307410407010740d010010051020008241000d5070a2100600e588000012511030260040001d8414014050481748000311444184007548003603809107100d9900800b6140d80e42c0c85509100814001c0c8011406483c4207040c1608150a01c02d0107000f03002c0e805485400c084074814100042a40103080c3c40064404407112611070300c50341e00190140c660401d041d00040a06130a01188500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 410790260 1250 410789010 410789017
    0x206121609050406060503150f0310020d140103030801030b04050a0b0f0106020d0801050105040b0c0c040e06060307060207050109032307140109050a120f020102070e070302030103110f0a0b0d0e030708 88
    0x82540c5001109480b10144010b0321038501c110b0740400d0003800410b1a16581a60301452080c0c060017a010f680e150000183c5046078100e80052103070f0f80010620300d1100c0c40d004001c21206000700710314840d45995001865108140710103844007000e00081001c11a0600c202d00b00c081c4c0159100596080c0101d91f0340a2a40c207208a00140c07260b4045140040d0003504034504a450503114582000d2800c0041481070f4880603141c0c066009100320704100e950341d0321815805018541c020412450164181460200250082003d56000f50000c0290742e0340840ba10003a654410201c40c064814070360246196041a02400018090038801290842010b0301c80f0345a01c600366925004141c0c2c035001d1140e151014025101c80070000c80c81d4101003039035201d500540a1040c07048400d556036030ba4980c620f800040d00c00c000000e80020041041c403c1030180000c0845045602c075180b01000700014000b000644581e800750740380810302c404400210b0780441031060000003617070356036101031602211381c0c0d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 410791366 1106 410790260 410790301
    0x2062a0408030d05060405011208090409020d120c060606171605070f0f0b18030d050612100906050702071503090221030d060803030709060804020612 66
    0x841c00c1000301040120b0900004250038103000b007109850042e0300603800c80340c20440c140c0c049030011040701c0c1021011a80014404500d03c0807440355a81054080c042c08201c2c4501540381c3d030030406140c14144200010003249840d0081a120135101c0c0c50400d404039070000029010345444844561001c100341451410004160355542001c03c99a00c100d03580c000804660040010039001603030070150f10310065605440d050003403542c0f40510600e101c8030039162004202d2540b502d41e074400b0445508400d8034552200c00d41c02d43c01904000380105c07840e074500310009070002d20201c0c1c1c60b815961610003040c0c182c134202c1000c90103008001410b9070300c21b401541e044000480d401c102d00082d1302800103507458040c00504041250590350121646402c10401c000c0c03200d43c000400000c0e00c1d0107040114203502d4138004500c0074000c41c090061400000c5090220042c3d0500c20240c948 = true := by decide +kernel

theorem cover : BRFrame.Cov 410611510 410791366 := by
  have h0 := BRFrame.cov_init 410611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 410611510 ≤ n) (h2 : n < 410791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
