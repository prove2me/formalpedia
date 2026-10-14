-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0511
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:11:09.875989+00:00
-- url     : https://prove2.me/submissions/db29dc52-923f-45cb-b2d1-a2a390445dd9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 91726619 ≤ n < 91906475 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 91727869 1250 91726619 91726627
    0x20f060c0a0605040302060403020d0f050a1b02030109060e160e04020103051f03030f110d140c07050a0e0402030601051909050711030307021006090c021908070b070806010f08011415 80
    0x2c50300100c400aa0301070700182c1003142000145a01000f0700d10140d1010b2030840568440480010100d02420084004008040c01e10020211201281c00402500200200a03061103450078000030955491846000d002d00301046803e001000d410350f080382e801483d0744000e40c0e902d07030045000b0500140381c0c8000281034040e80040e04140128440518403035200d52140072414603000d400c0741040c0201c290141d0107880c0035a680c6a12062003143c140781c811196403262222091182000003035044107070070502229000400c0312104180c3c0380914002d4081d11001c0e42c0700c0007845004100e0071000b9400003c001000c10450900d0350005da800495032074102882030819080e5411130b80203488945c0181c0c4054000d141c0b000003407044900800051108000042042d04041c2d02c40404801441440035120310600602080c0070486061540c02140303007140385040e03030002e4a5050195403050000b00701c0074075600300038040d20515040c0c03181c410f03071010401c0990041020001070000c03800e41600c0280 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 91729119 1250 91727869 91727873
    0x203030c100b09010e06030a171c0b1e0a17030d090302030a02010e21131a130608010e0c0a020c0909010605010e040606050a1103070f03051b0109020f060c0a 69
    0x2124007004074511000120741d00000e0402c011816106030000700010000d0424014160390000f410554903038850001e480b0060046d04010640c083c00d40c00d0080d10018501640c009810360340003200114044402c0c820003411107000d40c1d540c041000c0b001d40c005202400034440f940440307040700d402807003a40c1100d00c0d00300140081c000703031411020205c003d03074008100180282e8080c0a0314080700b86440081881e080d001d00e15140f003402001d900b090700303000018a080c00481c4007038440050301c108410000e0300c100900f4807420581c84a410325940004a0b00c011890034070a05c2c15034120340f1203c401812540356100c44000c29071010200f60203520074214203184603101e52460304d110f0380a0030000a40103181ca000903140c000440a110b10591500074284440d40c1c0050540303200054030314001d034103080d00010441c0b030b62040711009099250020000f1003099809001040516800c0d0001701c22006088040e6081c2c0d180300000030b42c080c05d18000001e00c0e0401c40060040307199850202c9014144036 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 91730369 1250 91729119 91729123
    0x10e0d05041e0b0a0806090603010b100c030201090c0f06140301050102030a030f0b280e06130e0708030705011b1d060a051201150807020303010608010b0f0c2e090b060d0203030c 78
    0x92213544040388501041201c6803a08500d95540304a003074000b484106030840000d001c4020186110081c04a4841c4060602d8400d40c4543d04070380e4032940d540c851540361280c4403603000207841910009030342000d1114100080d1001d0340c0c100c0d20113070002e605026001000390b02078070740c0b0b5030b001e4100399581214110642d43e01466000c1443c2740d4805030b050300d2401843d06c800071420741150880d0f40d007a50600c1aa40c50f140300b13940b206101150000358003070000c07000a092442540c421103040c1700100307064040c024107610800c50090644c81148001d407141000b81c0e510480d0500c003583c0d041d450050304403182012001040b1080d4a0719105280405a81c201d400d040e80c20b800100d45070381010195110b25407c81c5409402c40450300040d41150302d460030062141c10140034030b4040b400041030f64003d901078503058404c424500e030705803494520110384094102201000360059070740408000d800b201e84c18402e405140341c02089190f17003642c403c0c0c01d01500c031300240822a0148401c1208500202d81 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 91731619 1250 91730369 91730377
    0xf0209150904141626210a09050f03060f1f0602010207061103010302090a020904020d0606020c0a0f062703020901030b0f01050303030c1603030b03011805010e0d05041e0b 75
    0x1c18002c84000112590072249841c1c0c1d03090080c290071309505005c0c00458401910f02c030580c038040d03407014500f802007500c042c1031402003c2c3e03c42000e007141c0c850094400b031600107030410281070360b40d41e90103680d101308101500a01030b400e42e8054200001181c0d0a100b0008020b42c07008111022005070101c0880e002000a00c075406080103035404648003040241c1400341002c590010001d980c110350650300081e81c881c00c058600b50b80140e00041c03200701900e17140c05171036140804000800c90307541c2e10540070391950903812096118040c0da83c0302088180e01e042a940076201d1a650301c0028017440a103220b10b00b500c864111000c5a40b042c00000140e80d0030900078065031003102141c0441c2021039440e442e081042c0c000c01e00c070307400c01c1c000c100103550305800b03503000604958040c149010381d0b4201a00100140c00c0015055400c0c00d944008813030407051100c40f0b42e807060f0000c10000301030b407100e1921544554101000107000b04001c104031400b9035040101680959600401580d8030305440b0f459500c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 91732869 1250 91731619 91731623
    0x5040f05061006020c0f0303041710051003030f031a040903090803070c061409010e060d0902030a0b01050f0328020102030d0f05040204060605072a030606170d0c0f0209150904 77
    0x181414091002690601c42ca00805c00d0948a5110b8800040d0000f130b1240154081e80242c1c00c044040f46048007020480840c840c0c0100204005506003c82144041d03070507404141c01240301e000203008014800c1c420019440c021004034203007844603001f088058444410309800700b01e88140b001c134035030005000419040d40b05940003903004c0d15000015040d0400c2d52100c100c8800d01b84004100c0d6600038010b44a5220101ca009599982c2b66500701c0050140840c06500340c0309904114013042005030304141668821141e56520240751f02c20599614803001c04401390110000d035031140d5414460003401d0701841401980c0c20070b000031041c1c004840c044c00007600040d4450050009508192183c0400f40c4800d00d809460a1800e49502d4000d41e040503030144041015500c5a03200301c0c03100c145038055984920140706890382d80b060040c144140102000f1280688040500e40c030b40a0014101c2950b400b124500806001e602000f4220b5001440c0c500b00003140c218036070865035803103840c9100d18 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 91734119 1250 91732869 91732891
    0x102030103060b01080c04180608030a020708010b040b060f0304020d080c0c0f060c0d110f031611030601060207030609031e11010f1e110d02040609032603070305040f0506 75
    0x2601d1070400e10281e80c003008115052280c650207010521100c101102e050301c50a0b0980d61082110703088000007071146130720018080c000450311541e15a40400e000e0b080303071041d100a1000311101d03400c00044401c007114090f8040000c003c00074019410801441d84140018500c806180c182d40341c03004243c1c0804201b0f011a004034800720707814540b214100200c1c800554140d410303e010b81c11200d42c0d030030304026a0420703c0304010284a00150400080b002501b0740001e881c2c561030101482c500750480c0c1c09c03045805000b064100a6181000604c6034100c6050f80c0c020405203107503441e800000c0485207000d4013000a1025103442e441e410749000d180585040e510024440b1890f0401c2d421205042c4900a00038141511224801e5036201c80c491400e034401d80c0003420704400746201c1c1c16841851603460318140007180009815420074500b0048030701504000b21040407641011074031100041c14030803400e1051001c162100c0c400e81c400d80c1d202c0d04c2400c0d078042107161a15038501c0c0c034100b20b032000848 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 91735369 1250 91734119 91734121
    0xb0a1704050c150a120b010c02122a01030617070308031905010e011403060603061f1701051006030501061b050a05120306040c020703020a030b070207090f0b010e0319171b010203 78
    0x4d54000180c0480b03150024041100300f40d007000080000c01c00701c0d400392052200641c030149000c03040c0014000c1907900388203403001104504148030540c41100c9100e001c03e24000001543c45007500341c102800c0e110102804d01582150788407001c940015100181117420382e030105108101074800d45001e05141760030200b25600d0210450711100c1d412111a009402c4242031000e59180040c03d241c1120704601441c00510700000c0b50280d848003640642d20100c0c220001525142043d44014043c1c00300c0100c6003209a1136446c191f059490030300c100307000107401c56008000984803c82c15107005114600f600e629407480c1d11030f14582080c00d410404120300c0001400000d1615119410101800d070000e0300140b0f245030005070402880340300140194200d480064111341c0300707000c0c0c4005060307002d20400907075001030084002404c040f15403a001c1040308880d480c07249000901100701e050341800403650405036907100c544004043d5840300315a5000d015104109440900b8240001c01ca01e00068913 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 91736619 1250 91735369 91735387
    0x1b180207150b1305150d0606030308070206041e02011202120106110a1104090203010e06040308161d0d0303020d09060218090c03130c15030c090b0a1704050c15 70
    0xa004072091000c0e880500d002d44007152a01c2c2c1c0e25508a600800f000c0004141c0d0360800711000c0700c0205104982e2050100fa00c01c030800100e50701880c16280603694a645560701c4160036607480714150340103003041524030003a0a0400c480c81c607119000c1d206241034406100418000801da820881101c1d90041e5054014000c0643c400c00c80390124801c08000c1040d80d031641c9442440182107260701d0301846d22100701400f952401d42000c0c00400c200821240c903845c0500300104a00030594812903003444d0544240c141a128001e07516424074104580c4010626a00801c10303600c03142901142810780038080c1106200340740c400d11001074020803025a03500c200c3e01100d403144034207075021480313010702005028a42c275421040c1c0758404400d0410103044210350811b191845107a9210200c12421a8050140550b15401c2080b4103c0961600c407001600c440c100e5205009020850000036124100b5040305040904004d1300240120240c6010007044c2000c00c02015920307001529039480090b81c005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 91737869 1250 91736619 91736633
    0x3040c031e0b0f090d0f0905090a0e0d050a35070215010b04090b06160816050715030f050702190c09060b0a080c0405060301090b01020f0a060501081504020d1b180207 73
    0x440d01c0c450b140c1004895800790300541500464020703235001c3c07841c0000081812000360700031490f08818400715404a2a0030302c00826691040c00382d03e0020380e6800803000090482d00d0f1103441015a03100075903a43d41380da00d0161503120004c001c4001c41c4180c91341d4407503804c880ba054038080c02d810034a0796070340c4d81850034050a89810420260140c0e0013003109859209415040704056540403401c0c0e5600d9410110344c3d05403107442e0801528034000e0140014456114403440503018003540c90a02c921403c010b10b14040700c0f001c450000140c0c0140000d044014103150104010714403640e41541d909031524444011a1016002a1420140042d66400c0660022061a401000c00c04610701e0941070002180ca140010b10410780088d0f203511100300b05038002d00c12075045032031410450307041c00001c7c1014006450203104039a000d010b02003110310740480340d0348607520842d006000850002001c0d41c0d030501c0701524150355a00d1281802020901040333000c201001541e0752000544ca550721824268 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 91739119 1250 91737869 91737883
    0x1a03221103070e100605070507090e030403020909061b0d021e0304020102070f0602030f091503040615060311180a26010f0504021f0201060b0f12070503040c031e0b0f09 74
    0x9480c20100701003100c0f68200c03800c0075068030f49a00d46142c8410441ca2301d00e241c45200d42082c00d54501700168181501000070140044a0085032250510b85944070032948514054542c80b824015011255030980005c3c002040c9001500e907005180110010041042c000d060407c4600f5103000010b22081d0b680c10400200546001c601c801041c528140019560303106282c03d0040d0340d1004206e034121a40c07042503041d01c2450614181d90340307240038a040c1000300341c06940c502e0071500340100458404d1280c400c017400070310040300942c9490740100341c4910f4007440100d2998461001c034000b04640303264039042000c801d4036120f40c0d50140c401004250a69a0204040c0d034131515043c20400544d580b1110254401c6450780250301c0c0300e201031001c03405441141c10203403403c1000108084207482101c0184000d409110562480b91180784e01110684000e0f207003d000c5421410702400400c2040505031000750003605510300390401075443c500c160000b110b13070f5101704154030200140310500344201 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 91740369 1250 91739119 91739129
    0x200a0303060e1e0714070b01080a030f02011104211415070c080a03021305030111090a080d05040b0f04080111040303020f06010620030705031201030213061a0322110307 74
    0x5181c0340d42000300c04070f800203802003042c3d04100b26101070b660b80d000e0b07050131200900c1c0c03ca0340c0300c44290303165008140d0765041003400306d0004045140d104034451041c40703054040380243e64440d04d0207283c240203602021090301150341d142c1d82515503c0000303003006d21078481c2103407107030140501c06400b94001c44070342001007114042c010a091510002085002140e0460103141801a181c01720307100688407264403a0809901980380961100fa07090110300603003980070f0112002141c3c2c039100e40000b030311500c101013103030041101400140014903040003d0003520400c6c0508038107099903005440d00391000800c1000000c03500040c14820b0681c1440019440c1d44842c00820b41c0d5458040d0051841c44a241040402c000306a00c4905000d01401114144c982040840c0c3e16030091324941a2040402e1200b00d120702e154000c001c1106850b40503402c1120944c03030034001c0401e00d103900b0a80580c0003c2c20464a000b1720b070710b500c01c0381801c2500e1034000c1b8094220311168402c4c1d401803518103091030b040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 91741619 1250 91740369 91740391
    0x705131e0b060708030405010e1b0a0b0c03160311101a0303030f0a0203100e0103080d051003031b02010507080c06010f0512100b0102030c030c0607030b01030c08040201200a0303060e 80
    0x1201c0da0740c880070215403442c2c1d031010109649640c6c0381000ea004141000000b00d5a0040010401c41c0070803041d0b030052003440403030714507e0b56661203403031281c0c5100c0c11454182e0790700107000c3c003400c1b40000305050b00840d009051980b8406501c5030700d503082c00800403131200d40c40d5545024030100c4200c42c440507540c0034140d0003503246041645080560207002040310f40200d070000000781000304c00f0060714004282440408030556104d143c11012500849071030103240c3c3c030708000900c84007a405514000c40f0f4042d00d850030b60780904041c0300100076000805030706021080080e040090038a80007050094600300c05050f080d4103000d01c0040c609001c2d4401480b65004003800d0000140c041000f00051646100014105050301c005074213502031f10240d01094000851103072124200810800d101d2104c950b010050784105100560444194081c00380000c1d0351000042c0055001d410001c180c14400c0c1d0092040d00300b11444149815544141100000d440d03801c10091618044981a000036019030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 91742869 1250 91741619 91741631
    0x21f11070e011214010f1e05090a0f0308090c09090c040f020a17060f120a06050601090e010303050d110a030c021504020607120507020301151410020d110705131e 71
    0x1080180d00300c1410003138001e4400f01203414854000b58810f40940c038404506100f00b844194055081403941140d4144a904107800100507410109072804210351242d4803c0c030310b04031500c085034000d40041c040d0380c1610841d480d802541e503401c1c07240c07445010224000c00c100900002030005440c1e131590780c0c0b07542c50300620048440341c0d00038410f10114092940803030480c1e0780f2000024804e072254040e990300170b8403078511850040d10100d61414054007501d818089030300c4101c0115a031015501c82c40100200c04001032001920400041980040300c29000c0f445a00403010440c05500015000740803031780d20000303008001e0b018002c500d0509122a0a40070610b82500420654481c074030000301151180f0b0380300f8898901403825110f0403600078008100080303e0904e003000c184441d00460766000d81c0c1102485141c80c0c49144803050401e554060075403031400b10810350301c01c2d5000109400a0160359404a015101d10081107404a5600408200048031a5080305141d005180308425141004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 91744119 1250 91742869 91742879
    0xc020c0906040e0c090a1b02061306051807060207060e04060506120c04210b130203071a0d02070c06030506060412020907050f030406050402030105060315010e04021f11070e01 77
    0x44126840312054401143c54441c400c2c00d1070900004a401c541d22504110902034560703840d911000f941241c0c4020035044542248003660780742c0084540c155440c2d002000040054182d4200e0350f049586015a00d00400815036030b60300302452500301000507400781d242000055400101361464a6040d20100041c40c24400450020f00c1000700d200c1181040c20b0204450101c1102110010000c0da100d1400000300031407001c0507030102c180142c4a013000c00c00800c0304d00703905034652031100386d00a00406120f440c01d6040c25030205240807082c8940024800c000500724980010400e4074400e038544105181004000303011a100549264058030301400140305003ca20310640383c1040d0106d501c80360b180e50300d007022142440365481c2002140004424003080001503000180111b208070000c1c04240d4491041c0350ba01c03450350546222000c010f40041200302901c0010359086030010340004041c10310340c0c4540c4048500210401c0c0003903a00f525102d04042c041c050000946028000b1107805d5140c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 91745369 1250 91744119 91744129
    0x7030b01090b07081905090405150913050f03070b0603060f010609091503020a0605270303090114090a0e040308070206041109060d0204061409130b0c0c03070c12060c020c 75
    0x280076014a2a100040f07000c1400003d000f9a449205070f04a81d02102032055401841a044000443d00480c01c080205200510001d00a000458082c102c61007030340d5900241e06003061011b0b0196540e0145003e2600d8007482800242035960042c40e0459940c00c205050600e0120018241410031400c2c0006106041c1d101480c081182c0300c03000081114030003d02d0781142615250310007548010710250028003541c221020b0001400142e980300380d60b1807044544200031150000945d4990404c00004e0b241d9030094410040c0d40d10303800300c95030401020101003080c00c2559040208082414002c00082560050200d640101184007902d1282003640d0380c88001003042c50b1880c443d8011100040a9448001c03110b080190010010b10000d641c8000f50019031411194a074052004040043c11a21800b413204025942c4004203010070f560301402e18500c0d403c02c0c9607064440c001089450040b4070700f806480040c1c410a54240d60046203460a003041340e54140741c181c1590001c000e207090a0f42c3d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 91746619 1250 91745369 91745387
    0x5070b0304120f021f05091603020604060f020709020d05011719141606080108010e030f09091911030601030c0f020c01080709091401031109090a020609060d090f02040507030b01 78
    0x1242000f40882c1e42200b010780c14603800712030f01411302865688800003240a500400e00480b5020701faa085581e6a10302c9407135142e01d50001a410072010042000b071540b040040c0020416184180c4083d16100c0d40004140d9005260104095488000501480d03400303802252150350103c00408121b6102d40d0280380c050083c00024100b0710001d00d141d645100144a00c0c607820810f8216440959101c443c0500000020300450346250702c0d0090801d03000301d0000482e4842c115000780581840c10000c2003201181005018005510036032902610a0b4100d015515003218014512502d034504080010304032447e5000540c00c1107200341c1daa600590300803d0511581c0e07000c2c0b92541503a1b0b6042d001362982d8076a03510542d01c40b480c20101c00c0c10802d81d565074906032441440d4121b0500d003010b0070008040c105030b5012107079412003007100d801494007000901e00d010010b00500d007010010001c0368110b035080c1006541c280405280882145001d109107503000d00c660408100d003046850000b020030340 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 91747869 1250 91746619 91746653
    0x111130e010f151709011b1412060d0f03050c0d0305040218040201031503050c0a0602030c061306151202010e030f10020306040905120408060f060d030c02180703060305070b0304 78
    0x2204007060b603ca9104a642c2014401c2e2455501036a0501d030050303e00828280c070b61046441703140c10750718601c1d40c840e142c0d10554000c401000c86c20700074425030000711904041c10080d0f01441c015580000603401d01708001c40c2c28025164951190140394185041107109020202010f191008100c01692a5013146500b100791112040c80340d074492005900030f01c0f00756254280a841d50800000308000080d520940c028181c41901803a50781d05010b0f0303a41e00074004003040541140b00020f01001011001c011003602a10012503107014441203021241d00a0300080c2c12031600c180032009558010045d42c000400550041c80300c3c2c0964100c0503240c2150803003004550b600000885e4080d0b5498110221480e0002d00f9281388880d801c500581e030390f00c1403241c0c240c6405040001006030b02c060010b0f41c403a1401030035082c21003040c1e542c00c0391960804802240e014490121001240302c01203c000d219180340d40b000142c06085003001890407541d5800700c0c600c10310400804c400241c0111a0100e814 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 91749119 1250 91747869 91747889
    0x106050112180b01090902130207030f0804050307020d060c08090a0c0b090a0504060b070311030909040b0a1b030c031802300a0b0f01380405030111130e010f 69
    0x12240141c0c04194070050800500b1102c0d10400101d05c4003455402820018400c4030000d61b40410201f240060340101c050143c0411180312000d0310280c021080142d10901c51001d5034074102c1c6650019036032443ca02c8003034071590754525050812642041045410021481c02042c1c440310076910000e2400440c090f01d00c802102088032010340c1c890304c4003080605002041031089640307556610480744c01000e07040d000941900ca02404030000070048074001d910107072501d040d90384e4944500c031201002804280c084e0780c2d40c207601102e0005069840e0602500346c0d07004150300144000040c1507d140052550062648188050059652600790080c2c409101901c032880740f20040110040703031440d90206154054041c449082000d01203078684206a100100c60a42c0d81790707411180100c0f04c00c2ca00760a08160309c0640c680007500503080c00d441c00c0100000501d49615240400c0c2035851400001a0440c00818200310b02100c150101d00a80701b02c1888038169850001d2200740c100c0144030322811302c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 91750369 1250 91749119 91749131
    0x5040b061c0f0209120c180906010303030911130903110714040504030e060a020d1403070c0615051c050105070503060108010611010204030f0318061b1128060806030106050112 77
    0x6400160166100010010140a03040546424254035840c01e0341342d05101e02100051f000740c1c5083c00818501070382e0750b103004203260780c290f85d0b00b82d00a140c0e2040c2506c241d040c111143c070a60b640c5402e440d141e04281100450320821a04d00a41041c04581402c1e841c2d400011050118080011820300c1110007102d0100c1c15403110308050303805c4054102a03030780004000890025058001940780e50a0340159682d000c10214550b03105860700040d2100c40008240804c201c0115440f80c0160b0700c809411400740484e559550b0009000c00803042a80340b00945200014091003021321586a12941d00e00b4814135505e1310760002000401c0c1402020180007459609210104003503041e10051541300351040c5a60795282000380a0400c2e504810080100d0400003103a0b1520038028100b40785100410440c600c2e40d603503034118108111605690b004110202d04600344624003080e0315824980a84c401c00c003a08101c0f00411904005059901076070500f64200500d0340e10800242105502140c00911 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 91751619 1250 91750369 91750391
    0xa0609080d020403081801030b060d2013031b08060714040308031003060b0103091203020c010e01050703021306170a05090c0d030e1002150c16061505040b061c 70
    0xd50040440e207052562001c01d02000700058400104000e000d00c4a0b40103101c081304004405541000c440d0541008051250501c3d130001c50700166545118005850000291001210304e160040740c2c0d01032464070008002c00520540c401e580005070031450362040c00e24140442a99078040107440001002a00121070b034502e4a560141c034080c40d07104c001940e41e400c0c80d180015140c4c4042c0000c1e5400f5180090304240c07036010f0302ca0700c480c041d031046901031011940c00c02a402904000228841c41d500c5030500a01c466080c40740c1351040070345890058607100d0642240340d4003801c41d0403a034280006078000a03502d078681c4045951112914602182c29602c034401682403892a015103030700700094010f0300c010190091000200c514094072025642038070440704a0351080c603981e44c0312018101d0401b003100013003800c0007030207a0a1081c180c0351010a03540d490300300302c0e030001e07917001c110301c211600920891402d4001d02c0640b0702c046030b107182449820b4038180d459052901c21145200c0d641c0302c1c11a5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 91752869 1250 91751619 91751633
    0x50901050c010c0825081609080a05100518030306090406020d050708060312040b1b010905030d02070606171902010e030d0c110103110406050a0c06020c030711060306030a0609 77
    0x601082101c000f88102280080090f250801c240e848204400d010a030399201604124112414403486544000f01d9440d59030125098100121468081061070000400d40c0704041040064052080b0700a04030b41c50b21300c4849044500c098840110380c5000c0b06180f83c1c580001003600d4100301d0071600e201c900d403201e00c7d0032070091003001c450ba41468105020440400d402c050843e11030740f402d0701074840940a0840042c110310550291405614050011180c0e0f1116803042d00a180740c410000a84230680380c882c80d1550700040c0c3d00c0301030360340c00044400c10020316005002c020551103494285214520503402d07201e041085c5810b003001d4424071000190b81c49819480340181001e402e40d1001c0300449401440c2056240c01598600b0011040351120352091203000c0b17042d1001481c2e14100381c10901c086815078481848002082640302007040490340ca40f0003404004c0c444d03c01141c3d540a030745000320180c0080b00000384602c805204102c210340300483c2d100d100720741c05040003c07106200c0c50700007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 91754119 1250 91752869 91752877
    0x180a0b0102030f041a12240a080a03050309010e15071412040b090a06020a02030702040b090c0405131b0903030e0a18090c12080309151b0c010b18011806030503070305090105 76
    0x16850050400134410320700700500500400170004514400284080c20500500e501544150031350380d48502b220401091042000d1038101c21601d00110300120031199152515420500c2940030b030401d507003400444d903080050384500c101820781c40ca00f8010302155422800030020005481d602d1914001140c06005000c09107401d81e201001b19101c11489100968a0300f02c1c5004902403454102010070520f4100b03032043c0300d200b9120900385090704100038880030320941890074110a4a506c142d0414440405005040c040d2076641c1c040c1e15480c6040013058001038002c61800380c01d024206002da483c010140c140f49622281d408601080a8036108401d03660992100132740a8621200104008451004500030100c2904031040c00f511401000981c2c0e4040c0d0300103142c01c06000310205080d50a50203401f582c0032100000a02c860b01b03101050081d480ba4041c1085500c21400500c504c0d0f140800382114080000002c001da181144e6a85540e8459100040c040c4078000c20361b546180c0c854803c0ba = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 91755369 1250 91754119 91754137
    0x10905010e03030711030906090d0302031303080a080c03060f010f090807090e010507080112020f011704060e06070c0c051e0a0f03020307050105090d20180a0b0102030f041a 76
    0x200038020001c2000390722030f04180e0308500003070711411000710301a0001050b44c0c040000100360a10f415421010065040c640520403801c2d4002841500c0b420a00325208800841c000d030400340e524048241d0003008810010072440341e00c10309009008407510741410381c1003000c8082c00d00e8181d00000c1181666207a500c0d9010f0010340c8075164000c1030040d5690440c84420802c00000d100036203813058140d81b540003d004503010f040d140c021180c0585419001501b91101c1810038400c5100c50350101e0145500c120b800303903441c0d45c8459a541c6858403c01c612940f028003441c00714000342240e61000b05c2034105204403440b0b01c880138245007850130500ea000c0d86500c0700a26240381d542c2ea9904038581a6040d200991007030054442c006076650281c412a042041c00801883c1281e000e0b68403084000d1701c100101010303600c4295862038035201e2140801c1e48102a20202e41c80d840c14403031807811340d00c1c94508581150028805a10402282c03002e40703064a00b03050b180c102040d1a00609507690080f901c030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 91756619 1250 91755369 91755371
    0x110102041e0512030a02060a110412050618010c05040329040515060103020a080a0903090302101106011d0106050d0f02040603020703080604090507050f040209030a060606090807180e01090501 84
    0x24180800020020381e085034401c2e2070f00400c0c0da100000309038032402901081005600044001402802150300c00610b218401a9950506d034485560050606c0d00942c1203480364009800d0102c079030f0004458004c0030607817000a002c0340003c004020701d2030140b4070000f8848120000d50f41c50121200020020f4400c040d480080280340904107140e580002c008428140180f600c0801c5039548203000316800381c1c0160f182c03442d181c1c80d1140c408004140302c170f9040e000c102c80218003100607070354042b039005480d02607592110a4600d00e40700341e01786030b01079100c29005c0440700400100240d50200803411200a401c01d00d80b40d44210601102170420800c4545c54a40b00083c0480c0040d0140c5c05803404a01990f40c03030200340c0d1600240021100e03200e10240c51680045020402480d01441404829001400140c10b048070040824504105e115007180c3d52030302c0b017105005d10365000010500a004520092144503d0162030841d809003a0400a400646500c40c139551107034250460b92542e40c0c0680 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 91757869 1250 91756619 91756649
    0x350d0b010519020d12050c0405010c0f020310020306030118050a023006010e09030a02070306050901021308010608010e06070c0627030306061b0503121302030d080105131a0111010204 80
    0x300081d01d40d11900204c0c804036206201207034150303e8070b2040611444001603001d28240c1424015500c0340e900906c100c5082800035692801610103029031051002e46010150701c1c0d0030100300301401e6401c011025200004815505404a1400243c00703640c146c0680d180c00100b11a0215026075110840b81c8101c410385110b03580851000005100381241e08085040049032901401781d512403040d0380c1d4440059118403810300c045207080e030025800c0a9401c000515109141020b699443c0b29580102c285035556203007001401000c0c007804030740210800290403640f41041000e004440c0800004d40b10729611000c1d2144601e5925031860070b000c4065408040d00d12a103030080140400d40101c2000070380c81c03454101207906860000d1402580b00d40a141000c020000b23280150000034641d01c0c6190b110307840031000d0b880c14044010707004100d540d513400540c140418490212214031008142d10700d012101100501d9444c40900d0b501e40902c1c003010307201d282c51040c0740079002e80c0d0400844000e000c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 91759119 1250 91757869 91757917
    0x3030403020f010f060e061306090c120f050408030c0705070e04110f120a11040204270605010507080702040507020a02030609010c2006060904031407350d0b0105 71
    0x9603601d58220207400a001d0707658401d4141066030100c0c8100d800d040440804035440e440c01c2c032000d0236400320010000860540c8d5410b00c200b9202035140704070100708d0101c149040c6150a00480030149001d01061140c0d051581da1100745200082081948810100d0b44d4002c104051020b0f0000f040c10384041132090405003000c401070114150002e10926920301c4000b114107043c2100c0ea04d040c01d4030068500406140ca91a100032207028186a000742e00300300125100c00c03018070051100d40740700102c03110040701d21403010031038041e0b400850501c94180f02010004e00d080e02210038490f41a6000705050b00d8601c01a45011b00b00c501c0258507004220810258040560000d69040c88550b2800444040c4e61001210600d03d2072000c1d070582c22000018481b820325140d42da400a100303142c0442d1610301295510700c1c5800441048981100b8200c0400041ca02c80700c0062100721082c2036030301703426200001c83c0140e110f1201030304211911801441580c2c2e01440aa50748a800e0072800e0f0142d9800ca = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 91760369 1250 91759119 91759123
    0x2102601051e010f03020d0b09010306140c040b0901050d0f0f020901121401030204090f06020d02040e0606160b0a1409010e0105070f0801060c060e0f0a030e0f030303011e080303040302 81
    0x90144034054003203422036810a80d070b000505808500c0c180c66000480d03c1e4100f045010754003d840e10012551111035110440d00c4583c00e85000314005c14000640720108080c819034410080e191041228050005002d00881c00c0e00300c903075010302420010380d9114101600c901501c9030300390f50403085280c41c0e4075486800fa56001804d81d20000d84e03490035070034a0f8070722040440305d002e4825030302c0544210042c001403c3c06d47c016031456000d00d0130545d400d0150781c0c91806981c448071015400580104c0c040000c0a40d0000140e041002221014101105503d401c1c0c1d0b0399807650000b514280e13000000c07451041d41d0382c0c00026607880c0301d524104030746810301c840c0e4068010005c55600395840c02d0005003032948100c521180800c0d07030755a00301c81a441e203002210164408001511180d9994a01c480621410407881d04100f46010140c0102c02c054280074000281d5940842c0c010891101192002d98010048070305440c90104411500626009014114009504050414400081880145900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 91761619 1250 91760369 91760371
    0x90203040f03030c090b070609020406272315010509031209130501030f0b04030302090405011706010b03010f0e090f0f0709050604060e01030228060e030105090d020604021026 77
    0x40c0e00e00b8401d90940304e6045803600018401c1030800d02c401e10219000580940245800d603000810104056803030343d100743c00640700c002507181d00d036080c901e00c030000704030703034092045c9042094075190211003c21300d0b501c204aa00900980341070310200301c40312107a030152003030b81c4d1440006801c0703604a28501320005440d070b001011080c071501d5007150281c080790309405175605803588000c4840b80780000c1e581e00503050130098411028180c081c44140e2080d11b0700d110722802015100364154900880350440d40c10008181c112600d05602040107011000100114204442018094404907900d40000d103041440c14415900240034180d08824120400550402503c0307003104100f0094a860f01080b00711902c40c400e070303800c103460701004001628043c01c0f001c40a1309a01040401000034072a0740703a8200140e040000812580c011442a030b050034480d10380d00942000040100c404140c40182da100b4008000034421941c090219280c2e91003640c1d0b1101210700a00d41700d110380c00d074080d09840504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 91762869 1250 91761619 91761623
    0x3020d05010909050c0d0f061802040b010c0b0115050c03030c19030c0c11060702030709061802160212150108070630050a09080c0303070f08010b22090203040f 70
    0x30030100081840c10061003162612076200c0d000b49100903940e424049000103845050315403480c942250008510113001382c1c650203041d00c0e104541071143c0d204100846544507809410806010041e000150f00b090700d40f41540c1400d020085554110841101c20340f054400c0018140808002d00c950000d002d005401c556245000d401151140c41030202c1c200c401c0e18403040006840111600085450725004c80c01055002c1c3c4014034120080d000302c2d1801049a11603030300e0541e0b07090208007058094055401124213034070b040d4500066080ad41215000300c0d41c01a00c507411848151a03600420040380c0c0304252001003206140d030355072981c03640f160403e109240215031011442c450b0000700c1842e51004148007410034121142449207100200402802007502d140c0d9503804038085141c03003010f070081c05020001540e581ca42800020003203901c0c9a108002d02c210314006110003050041680e8000200380c02c2500c580c048110f000c0c020000550000114520000920042c84030740d48a4640440c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 91764119 1250 91762869 91762871
    0x5040302120a0512070e0d030e01030b01030902060f090d0b0106030b030d141218030c0703020f03010e06040f0302010f0608150c030603032208030f0c010e061b0703020703080a03020d 80
    0x720000c110070050300c07803020b0a10020344100510200220405407464100074145440400b14205101080380b105c12502c09030f01050206410445e190f83c1400350110b2a4020303e000d0080041d03580c04641a40921141c81050b501b0100c1c0301c415544035000b07110f035903d070003e1942c845542d5441000e070040082100a40c002d014000c404210140203800e05005a051848280d00d08800e1410484c5400000740641d01d800c51101c01d024890320040015221042c6902c3c007524007140341d48104280c0c0403e100c2d006000e40d04007905440c5101000c01c40980c49070300900740828000407494103c0c010900030b180003007107614201000c00c0010000596130040c03810051640c41d82d4660000110b4035000469403154140e00c100030900105040c0240b040c0080c003030383ca00300341294466014600f507800c40d08007848001408035145134072480900800b04004440c001418642c1450312054900c0f510b41c81d480409078200049001c1050f00c00c00c0228000c580001e103160311000100c400401039030000d1000f406503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 91765369 1250 91764119 91764133
    0x4120f0f081c02030f1f0302030f0c130b0108070c06091e02030f010e2805030a0323010602120903030d1d0d08090c0d1b1203120507080103150b060d05040302 69
    0x82001d032081340c1c010014502008166507403000806000f00b13251640d0390069a40d42e0000005803020051403881480794009010b28400074010702116151600251000e00d0030310496180690300814400d81188081c9017101c008550f41c104400946640c0800403c5426210202095a8564001164401d20840540310204e05920205082c0c5001c1c0a040d101c0740c01c080c101550b80500c40042c01004000e0800d40021028107403030305821030700308214250220791160444580c121104101d8454041c020000603c0c0d94100b500003940c03007000c00c00341000d4200000e40f08082d660304105460600c5400841444280307112030200451001e11008100103208148e111501035006910851195008900512800031450100110072601240569200c40040071500005a000c400301002d440c041c01c15a020040c2c80c6002020030b580f00f0100401c85281a040c445020b90008a00741100e81010910301040c0809041400070000000e10552010380040c144448590b1504024802c500a800343c07010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 91766619 1250 91765369 91765417
    0x92e030b0105270f0702010f05010806040212030705250e0406091704060e270903030103030206070915033303020f09070f03020711100c110a080304120f0f08 69
    0x40f0304000a161640400d0b900000c20820b209412264003070524400800d054a4010007641182d200703030003c10301e40c0c00c240201300640c03c0110400e004040070100840c41d20034951601c03600d4030f51300403038040c0144180035204100d0850100441c05415101c181080a00b070500d81280102406417045440c020002144507000c070800c01614111222515145038103008102001b07031210311544815140c000c1c0c1c0ea18451030141d00260075218046a0000310727906d506504019140080060004040005012043c0064101c40c1050314143e0180c1c2004a014401030f00c2d06c94141c158070903003034481e0002422021031120000b45400440e030003941c000350381c5a01c280901401c80004c80750070300400d030083c192881c010b1082d40244a51800350b540004200704140001e40c4400a6035011070004e0591440b220074062111078044520b0022503400e41668503050446889014510660140d40d20860115090210841801040c4c50380a1100e050803110780c0307004441e0360058805407440070401060160 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 91767869 1250 91766619 91766659
    0x80a060803041503020d061520010207110108040203100c03020d0e0606180a0207020a0608150a030b0a0c1103070503250c140120070510080402092e030b0105 69
    0x209544000c0380e0b5019881c3c8540064020390702c480241e1107001d03030b40d40e000600301007020b0b1104c142241c60b642ea400045c0421424400040c45520b1501a50348100701200000b403000b101211458001c0c2062038a40d526400081c2c10b016441140d01619400c1c0700080ba4030640c1a401440c4076105150304010700c0038070f0426140d8900c8129500b980090024020030b0a600709183d5640d402280118091300d482c2c541d5001c11070038101c5900c00800b2075244010301441407005504810480780c10b0f03603035101c4245503440d82d1000030301c050040f48815a507400e1810000c1d1042d115010b001c007074101104d540b04032515102c5c1c1e0301c0e80300c2191082e01142c4090003642264600d000190308542080d0000003541c01c0420000c0c0d08042000d12134144487c01c07a4042c55011035030001048002c41130058986e551a000610110300b141c15042e5040148803800c01005030340d00c038245604118a010030b001ca1060b00c0000c410034a0300b10309c00c0350030000f080400004000d800135410303060303c006a80c1400c1d0b02c085007061003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 91769119 1250 91767869 91767877
    0x80d0219050705010e03030f070c03031101020304021008130b04110901080d050414040e0d08040b1506030c0a0314010b04030c0603061508090106050406140f010c03120b010e04050106080a060803 85
    0x74119040484100480c0d032192403041c0f04504014280d92810318a03070351003003480e403144408854400c42510100f0134590895000a56151b840d4025880e61500c5c0d40007a1118040d480310030140050312011820300b14111039001242d59200a00c14003074202820160700c075000000402c1d220700c0f015000480c40f0540403031403401120302610780c0e86c02c1c20f091001d42044c0e00041d07001d441e0090750310203c250400208002119504140782c03103208807804d160500c14072a45000b0710301800078000a00805490310340008483d8070000320000742d84c50b1000398100714042c0c1404080c40790300c24a030600108942c01190028400c81e4442d19005042698608065050b5981c601c5290144d180f8109280b180a01031015a5400b0f48070000000303801d501c034400a01145d41541243c0070a210003030942c1c038035081c92994074689c1002405d00903204210769900400a0a0100b01e5144040d01d99520178030590085180c2e0004403c0240144107642c0c5440c401041c40e802260611911411b201000403013807000f004907 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 91770369 1250 91769119 91769123
    0x303090d090f17030706140601030c1d1207091103100501020a020a0b0721120605030105060a0506130b07030509090708010501050a050901020304030501060f06080a1e0e03070507080d0219 82
    0x704143c0741111810012641d491610f079280020004440021628410351a6400801d101c600090508100050480b499501d1a4041c0725448100003080b4a010f0b05120140000320f454040e10107200c0d01140c10009180d015003981c0d820041c418031380503000c0700514440c03511035610644040d42c4000482c2c2d5410f180001941284480c0c0c8180400c000d00801411000d01a082050700400d138440c4d1580c2d455600c0340c81c0b0001070000c060008041ca240d0181400500044000740070b00d080c03500004012601c1d0348101403103104001141c118500d902030394000145070100b0201d8032001a414090324030f0b0301130302182e84030702c1210002508490203118050b040c0c0700d0603980d03036041c410489010303102c03540045a0541540300178080000013130400d00070720000c0d00c0403244056605103494009032074448050a91800309003885604c45803070b140703441c00d5a0300f0f1408040120b408460301e0344860441c800c000019229024000010800c41e40c001064008800f140e4200d9068644500609020071282800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 91771619 1250 91770369 91770389
    0x2120706080a0902120d020706090b271c06020405040507030c0e04020307090e0405011d031606050a0f021b100b06030612031209010c0f0c260903010207050303090d09 73
    0x71500c4182d166010440c0e031880a0114404c003d20074800900e81240c1c841480d005a01c00e01c0d0034014268441207200080054843c1c1134180281e51801c0900c83c01041580c101210711003515102650754800b0281541000010300310301030a0320b0414102039030007802007501640c1480042005184a4414902000480e03070300d54003803807002010403010b5800038100c039081000c00310001c41d20598486202d402030380325034000030f0100d200104031a4180800c480c1050140c000b4400042d00601c0c02c0081c0b000c0c503034082000a03c507520348403050020a804241000d1161010401c5511821001401081c1c14000d030202d4a00c1483d00d40d690b820b45459011198000c4003e0020078001d0404038484001c84e00fa0740c3c1964142403017603480384c040c801d0072503a07001142e4540c00010040ea03080300ba42c01c40b400c42490020700c0400785031200b11602c0c6500c02c40340c0d075100d40c5003071405c0106070190a41c2c0181000074000d640c4c0d0603143c20a15902d41042d120b00789240103240103003203624001c2c40000c0442d858050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 91772869 1250 91771619 91771621
    0x50603040807061505060a0305090f010506010507032d030c031116110607050d0512160f0807090512010b01022a01050f09041d0c090408090609030106090f02070212070608 75
    0xd2003c1c043e00e080c104100c1c9074400d02d00041060350b01c05015025000407aa0006132501d4050085860b003600f81042500e40c1e49000144601668000112540d1603054200f1042d10100400c000d02c0c40065410003038039a1034001d06100c04d260303144d08070402241240d5000d000c0f902601031701c4095841446070f90068802c0f10300d82400003c6036004000111000100f0903403d04c03c4a032501c030f0800e10b40030b40c3c5000144001540026040b04080042d8110184440d00303082e8419006020f0405441500710806002c8444005080188100302c00327005007a010b003440d0282006004882e01802030080094058001d002143e03c0280e6601000d016100c032110034680b02984200055850340d01011b610034207a44200000e002903100c0d4020640810a24484c85031031b041c00e45203081c1400301d510941807242101400317020202d1222826030f00d04100c00c40d00c582d51611744000003401400b80f40d0000c0c0d000b6003000108201c0c84032075400381c80782c035009440042d5102640140c2075100c42d0300e809801d010510340b034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 91774119 1250 91772869 91772873
    0x106080f07110304050f040609050708090d0906050f090415060306060906031a09060310020309061909030903120908071e080a08190504121103010e151305030f0f03010f050603040807 80
    0x7a0340e182c2206c400703400050016100c0c03008800341c2d2400c40e218800300c0c44072014050780581c1041400c04041e40c078a0048086420034034001c1242c81440d002c1c221141012405914640d0342c0d40c8842811448160140d9100d550342e98090080c040b24825000820300f000c0002994500a00800119212069030341080401040070442c070404043c20060f054031940c1c07499800790a10703200a5001c0c000c41401081d00b13192102940d2031500c440c50502c15007500f000b01c420f0000303401c080004140ca51040070845000b86455048888429903440100544103c000c00200b003c48114115a401c025a00b10022281c6441c00c00d550f914042800500700c1c1c400f0440a409004d6050038100c481e00d0754640149481e907a500e0b28550000001c000341c03541c000d601c0c8a040b240c6400d01c60090345e00d1611020344039065507504a40c04801c80201234a40407074681c0c60b0801041414011120103560506d000c54982c558518000c080ea0030900034142e446072030044c00304448c54501305a900c40c0c5d80c00000245007a12503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 91775369 1250 91774119 91774129
    0xd0c05070e150d0318061b15020f0d0510120c0608151012050106031b0c020d0b0112110915011803150911120a030807020709050106080f0711030405 65
    0x2081c941110000b10200000c070f56565400d031030301c540217954500300070f0801950f103595240154801c10a1100c500030780038048105010042e6107a8210114080d40c940c029070840c040c2c85622603034141444001802d41204003160701031402002111080c4407801d031110f1525140e580868400307803400d03504000802c1028400c984c00c683c0310070726105c1707180d00ca90000007203a01103d0600d482d901080003400324644004d8a48a0180108584c6c41c2c00d10000c0c6100c0550b40185243d089090200300c44464110155120740ea00450119440400d4100541c1e45a950303110721269004101d402c4c01c182c80700052070340b400111030f078041c0c02d000d10196241d02200f4015a101c0a640c40780c4460030205400000100c0d003258a025000c0010b034202103a1510140b400ca4550107080c3c019910920303458480c11407202c40007460042d83c1d50f16052220180e01c85200581c5001d18950101d40000d00b000008076059501495841c056100701c441d036a1503444110058071860410309100b01c0d10380c0280020003643c544 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 91776619 1250 91775369 91775371
    0xa0611060c041406071b09231504020a05040506120f090129011209050303070e0a0806011202060403060516080a051b0310080303100611030309030306150c0a11030d0c05070e 76
    0x4980c100c01000700b13900c0851908000d050380003444003561604055054010f15011100c1c5495490030040c00d8901840229496480c8c94061400ad59012601c03482581c01042100d010304001000d06860750b08001c001220440100c03060704814444001081c108881406000400c50040c030800d41215000b070b6152000844201d400750400c8030071840844e000302107102d01d241c800e01540242d0795a10300028040c1503030401aa04d14040d031010302013084886070214016041d141c0c0c0f80c0b03080740043c0b11400040c980b8092030b0806403e1501d080e083c0310042404c0c603d145904850340e205c0c08990358481060f0412201304a8207006214080c051700b85004c91a0001140d1148084e80e403640d11913287c071001c03403842d00110b0303035001d14006140d4140001d036045280d45205d82090401189140b40c8500842c3c0c40f4000900364902900d181912928150300e581e0945510310759071400c450800c2900d040042c100c144143d1800e000f07004001c03002c140135116280c2c401500760001c004000711480d0804100e14590 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 91777869 1250 91776619 91776623
    0x10302040c0c0f03020606030f0c01090b0a0309050d180504020306100c0204181b090c0203040e040302011e020310090501051806040219080115020114010b1303020a0611060c04140607 80
    0x2c80360140c00010104282601e00d54002d5004009528050702031604d42514204040120b0780404806900c9030b03441030100d815208151829612142007140a8003e031280c00002030680c0561010b20046585c09106201c90600420400000e03669030800d101c1244003c1d0f4909400503103240d172544055001d03081a55900384003900c001144100d400784481e0341d8201510450301d0800c104c044046075404800a1409040600c0c0100880300209001035940e110300d1044848141030f100000c1d003814001c4d0f100d5083d648030b84e15003054403170a0110800007507008071104102002040340100307210305070307100c1c050699001628404c0200d200d2140c2c080c00c3e06008100c1940300e41c0030001d441008881c609946880003168444001039414124841c142d40a0300000e5000c581c9080c800c013410b0000c00400c82d04440003030705481d035207800c441c501803603090440d00b000e900321188001c002107050303100e15000c5942d000c56050314000d403a00041d09005210324413070300041c00313403c03a120005842e0120091515074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 91779119 1250 91777869 91777877
    0xb1021030807170115120506060a110708030a030c08130203100207021c06091e030e0904020d05010e060105040606030501080703080c070e0106020c09070e01090306020309100f09110d0b010302040c 86
    0x7200884203d0000d49098100c0202012140619205160481c880d0407413030034140810710a80c030705040421800e0061003102d00c10001421580c0c0c540a0702400700d90090a071400c02e40b9526603e040c17028001e850940b5001002034110f400045c100d00c82d4010104465034010090801005e6100c0c508000e0342240f0020390b030140c07104a151160301c0342e42e500a84d0b218421780d07011450200c00c1c01d040d901d4007e90841e03604900a2b48880d0780011750304c810301e85441041203800403416222400410042850610014210740c640700348600880e01c00507005040741c0c02110188121600c6485c00c4054440a00c101e18447e4000b60003440010301c1c0b0005020709050354000c4030400d550381d006200580c1000c1c1d101e0340144e00400c161014905110314080e6202095041c80c83c210402e29000a0984005200180107185d000c030201d945828148815040c8502481050006108205d0310400a00101c00200c1d030300f803142c0c130035100241054107940307004d51380041010303139240c0c0303540c0911015000c03951800c4100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 91780369 1250 91779119 91779137
    0x60703020715030e0a0c050405070c110103020a050715050f0a0903021e010209100320040302060d0504080c0a1a01140901170304050a0308070c080c0d06091e0b1021030807 75
    0x1081040034110303170f5004201890040d072500d02444100c0700058058010028103915000204000c05840040c5040a10b001695840400d60445240c01100381c000c0404a594101d041041220b0b00f00340d0086a907003100415a4030380c2c080071801c84000d101d00a01582180a0704420085592072144140c03086100261034070300000300080c0f00d05420074401000c40c0e51003000c40010191017124403e11480103148600c1d041c00c54000410303500545030684241911080098101f09601e000e848840002e1401c43d029410549414049500500380001c0e14481207000014a230310359800c034111400016040708001d03424038580c400001d220140c2c681c2d091100300400201c40d26001b10304001140100c0c00c50361218000d01d041024080580d00121090f4000d41c40500d0540e01c448400703620300c1e0f020380700140864480c40c1100b184502c00e81607460380c040d6404290188000584468460510380050441480d00e40c0c1d40310782542c00d42c1030b0280610150684450000f40201100e98200100341000110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 91781619 1250 91780369 91780391
    0xc1c030c1703090f0c010509130c03060e010803120f010f05060304030302040f0f090c0c03080705070c0509071115010e07210603110328060c090b0c030301031106070302071503 77
    0x2a68025918000c0f103610000e60000583c03010300040003464001d2070039a10308440f02000511180002c8107013003010755600c0902e41400d0103640b00304024005020b040d201582c0d47e2408039200c3e0420040c8001400c86680010300da801c998042c18160703050480c2d142101d42c2000c1c1484900c1d08010821428182c0c2000041500c41100c11036400034418165511000c50800340500c0540c2d00c030001c940180440c0d07a411000080d080a4040c0d40120a494a50385072078250521103080c4030030354002e581041c18030084c0f060850740700c1c04014103084080201c60060303204018a00303014800b4400e0009440155001c2000b03244185010304088038002c1507080d2000902d21100d04882e003d40c01103401180300d80b01d2807282e06061281904604c0580c0000c0f034026007888651044007240400107001c01e6031403081d01e000714040c60300c94028010721401d4649074102c0400440e41c903802030006841001440344004102e1400c182150350513a45540900a107034640381c10580302d0a000031818061580760094a49 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 91782869 1250 91781619 91781663
    0x803090109110301140703020307230406030506091006050913050906060907050c120c01090b01030620030c070209090c060f0301170a051209061303060209030c1c030c 73
    0x402064610000076090304035180500070782442002060190741032034002c0f182c0c080092011035010350b2509015980303660f411001c54103a01312143d481d81c4690318101d501200030790389014009075051501e0030050f90304c44404010f2000011101443c541400368024000c082c4500042c020b0303e440a4007101c8800000b80304c0005941d4220342e100c0980e4404001c101c402d24043c558039421440b1403d18914151a0480c0b013502d5010b400ca4016291400090400584a095000c83d56540d00000480b81c1541c41f4035240d03001c1e15010362001d13625005240c034040e0030301c010700c110782c01102031800a0346450310319824800300480080c40300c6207602910300082c5082d107841000b060040041c072070850f900e6040440205002901515003045944029500c0700011070000e81c4c1060010155a80e1340c032070311080c00103000751282d0341407986500d0b01801c0c00002c009080e00034000b2810200e0940d941040c0c003502b40201030340f030400b03072400030555401e443d0042405418041ca40f07600904025034411a0514410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 91784119 1250 91782869 91782871
    0x109021c1e05010902040c0906170c04030b25050405010c03080a060305100c110f0a031409040606030e0105070e0f040c0c060903050301051c020306010b030c13080c010311040b0403031b0803 83
    0x40c0ba6a512203003841d04516241c4101114013150b82002800c4e0380c14400d0040145c00c00365020768151814130301213085034000000b0b80b0000d40d80120500854600307140f90000289d2207512140c0603140711110040e40e40d008101355004c0d1038042c1c3d604519810b0644040741c000b4400343c040c003426591140c0102c0070803414051100040308511010402c043c1312a002400404113024588071074101500c480b4001e500481c8040000350185007802c00200700031841c4c803507403040001d0b8990080c5407440004400b03400d074014168265016000700416a20028240c0b459207550252a070301c10821417441c04145050b900ca001900d00c94601440501034039900c0380100e58083d24160085200400104440e00d0803446428026000341150860081d140d400b0070340d680c2c0c06020701941d40c6400720000c1c0d281503590064510310ba60120b1010803055071b8001d01e580302c850589442c0d001a0a055010284024240440302241e003001941460030745103483c111004240018001c9450000309002404584010007071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 91785369 1250 91784119 91784123
    0x803060d080d0e1f06050609150d0c0806152b06030f060203060a12050325020910080c060403170702031608070503011413020121060e0a0c020109021c1e 67
    0xa003503940181407540360300034031394481c0c84200381449000d2140e07840e08001e4a00380141542c03080c981e00000022071109000e82c1c003058066919040407181da40390701a40850183c81c00b03645803040b910542c0c1950b240761003030003001c5000745e154103e0541e46100192800f114440c20700c2d000990251a40da51441101c04c611090300d05c241c0100c14800032f4030f0050702c444002d0550322070b0f5500004050b52810f07100e01074025a1155500c90411001e02465814200381205034014000380300c0b403030071642070354648645026610f0341d4420582c6002ca641445001c450a0380c0d000310401c44051001040006203501185080b60940296814603030421000b42d40180a8180c580c0078145490074a410b06007100d005204000000d1100d0003030181c81d901305076629040c19028030f00a001b107903000805100301640b05040d00c60092806400290601d42041142e00825010b901403006031b03003180049098a851070701c080c0d0301040d0b0380000c200030190728546c0c09034540f0400000020302440402120340ea01c05d2042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 91786619 1250 91785369 91785373
    0x21160b090f030f060c0d111204110f0d021504080303070c03020d050307050f09030f0d05040e060a0509160201091205030403022b03091110090816030803060d080d0e 72
    0x10115480c580389048601d520400e900510001005a43c8555138003c003501c034000c0e0010015166400f00340b25040021541090348000365110a040621401c01c03d048400f6100210f00420520a030328100d9801000e4182c0146076020881c016001c0280104074002c0f4003e90b0700080100150300f1406002462154040741c90f41c44403940c0604029050196240800c800c2140c10030810042a030860251489518184100380c6c81f09100c00110b441c010314007030000340e00d1085200340c0c60860340c4a0028400d8600031081c000682d2a1074042c84020861405550f070702c281040000340c85a800600701301c4601e151440081101107540d11000180780c6c0001020340062000000c0009058040000003d14002c01e04400303400e941925504510303030b902507492000c041c0c032070804009001020352001c18050008017030240315204400d0180002007148515045409801c03c00444a421030440c4412a90850310321482c2d55909002c02003400031700d00c01160a20303024040031014000794071689000845580c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 91787869 1250 91786619 91786627
    0x60c0503041202010203010b07060b040b0a03060614010206010b0a0c2126090a020405090c09010b070201080603030304050709110f0d060906051518040e031809070c0221160b 76
    0x820160141100d01c402c001d680c01000100485090601100c8600d03800c00800503030400b944001601800c8010328251f4031101e030301c42c08810310130180d0200f030884084000c004900076005005a0720388a0902c01c803200020140034000c3e04a024110010315075102c2d10780d14146030443c1444040425003807003000c0010f060301030000c080c00b4003d03413800340b12074007400e01c09003a10740a40416550503401400074061a2a0342c0440c6c241041000269000c000050900700e040d03131038000b8501940c1042000b603000464041c04980070341000320844e80210341102c040c3c40414200242800603101d40803819034450810020400450308050140128403160440031a00d5441d0080910581e4030a8002500c500302c0303924841c9055040e03204540704502d8100d03950f8100c48000340000c000b03000400054220b40000247c2e07001c04816044010b6182804550700d408a440b0f4841c120340d840d018640007508141516a900400300b00d160180300311400103030896541548400281c0403a410561141d114204045 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 91789119 1250 91787869 91787873
    0xf0105150405460f0c050906120924070306080c01021011040b07081c0b0a0302210106060309151406010f0903080f091306060503060609030109060c050304 68
    0x40300440d1440c8048400b800b042c103003c04001e000c030300d100c900c10510034900c0b015000360880203040e203043c0440507003914405030320b18400080038240008800c0b031841c2c0b17081d91076179501c0d00844c1a18005000a02040d042c9a44044502203000300544910300b507202d10204100d03040c6809401e03642c68003d01003640f0450400103005401c4e214030b07400034481904114440005071f43c3c0050400e10129024002203014650442600c1e12441707543c104000d14100043c52005010710710006004144107140190f002080c480c48503030444000100e01540000161001c00140c540110710350085441410104500003422851a0071180c032a80700502003034440012000348012048090102100c2010034440681241e0540c04c41e0071700180303d54103124203400c6405c20140324016690127503034011642942da0f8103a100d00c01c03003504000300140c4660400c550080b00c25030301d405441c040b03420640741c1e40d00f151036200c00c014541e0003584e4555050b41d6150006000728003140241c03040c2624a0319080c0c2e03207040034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 91790369 1250 91789119 91789141
    0x90501021b0d0306150e0d0c171506150903010b0a090606030c05030603060109110403050303040b010504240308180310060510090e01120f14060601090f1a0f04080f0105 74
    0x1d0040c2c2c10700d45481820000a110303241e019407820114078107903a811144100080a1041054003d8604104040d01080304034138a24031f10811042c401c01c5405039285500b00100d414011201d080e00180d90058074010400f58102900c0c56000080007c00c040e20540f01107460240c01d07074450413403d911044100b20040e09441007558100c1c0d00d02d00a4034501e13084001c241c2c0d5a4062248088080e5144458500b2064400948000d1035202d4103495032414a4108022040802c0c050144220314024801d800b41d04280d000b03007500c0059045180c1c00e20700e540c41d605000d8101c1c50450070709030811032072f100465034107200d4401060700302d01001428604190600040445402c0c401061186401090100705450a0b01d141180e40314203003200c1000e080d2800c60a4070300400001000c465949144030040075010640da4400c000030303698480c08641d070380f00032800701c60541301d1083d020b424940c01000350b041050041401c1140e8965062420303559101440c6000014801d50f03119955903001d21000c0312032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 91791619 1250 91790369 91790383
    0xa0c080106020307080f0904060302030a0812160816030b040903020303100509040b0a0c0201020f07120f02012309160b07030305010e0f150102070e0711060907080d12090501021b 78
    0x7600c0150b0501000742d5446202d48a080b0803000504c00224640105039103e40250300a941e0140076584116003514010718540c111203d004040c51000b8002090317102e40d841140c01240702c503600c0044d15265805051240d032810042881010b0305e07212041d5950b101d0b4014000c100d80300e6030045030350745000504507141480e141c20552041c06800c00f800080741038442e074a50003d00b194000660030780711000c00e90081c0f04000540c400c091000c40c40d6814051605103140000e032558a54549000030401c0c01c1742247d0040ca403019000c410011117000b0b00320b807860b14a0380300b60500103d5210128980d10700100704040d901c1100b44000003d0504101035140c0207180c018811500d5150003410110145080c1c9040200b04011400350308198001c1e1380c0c8200850740c010b08a4104442d040d050120300184910030783c0e900c0c0202d900c20540030401c617480c000707107800440311010f01030291030450082c2150b480300948541d412040c2c03030b150312f00082402880100b00d00055005411400c00350031000a0078409 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 91792869 1250 91791619 91791629
    0x3040f0f0b070807031409130204030201030b09070906030b01050408010608030309100b03030f03190603080301061b020a030210090905010b070c140306062101050c07060b0d120305100902030a0c0801 87
    0x501c980400151a48150344c4201d92508058810b035548000d000300300e014100c45a80d01290f0448043c00c03010265000f0000d49000380d0701801001000000d11907000d0b0141c95010000f4680c030402c2251030701c240c0c400c191245051405518155035140c10609440464224058a410002c14000451410002001c0100104009110300c48124000030f440b40a030441c1100c290314000001410702004c03089020303178000740402c104500da44a041c1301d002034009000e40c4000c42e0707014004500c3c128120800314207481e401880d000005003503900b40181c46510607918010701c400d181c0080f0b90843c081c0180d034060500f211180780c48581c0e600344800e070b410082d480a1000c2c148000c05c0d418a40340481c0c03071a408101038940101d041d5902142d034942c0c116001d81420207511f4103060001f940f17001c00081c04c1032400741d68248100c42604040000c0710445080c024100d00300c241c05104e0942c0203400265201c5540aa40c548859958586c40241c2e40203e0f0310700c40ca90703642c00b1000304444d046002540500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 91794119 1250 91792869 91792889
    0x101a010216030b06011124150303030103020d02030f0604062a021e1c020a02040f0e0a0b100e040b0628030609110307030c08060114010e060a020f03040f0f 68
    0x952040102499101e80030260038603540c400007030380300c1e40a40f0750a1200f02008007103e031042c900003440181c101200c1030310f5504910000104034412000ca0900300d82c42402030295145034615400c104203012400000c0341c040c002c003080300350006c005000c503500c100d010f010301250713241880360b440138043c41494140444060780a500200d40e503001800c1902030640a210300a044c40031b001c82841d1102201d52031b110110307a0b0318070781c0c102c0780d000c10482e80144c0b0a80d0140700030b40500c0d08070740550f955000480030a03805250244049122038401c00e130402c200340c104d0b60030740c0e4450451902e00da2040740c0649000e070b1440c0a01c07550741400c0c2c4a100180301d10303d00c1d4000720380d000344002d02154960303c0301802d880d49a0b0445428002c245500005007a4010700300c0349244da0b24502444403c09500c00c4901c41e000350000001c0e0144a4034143d6480e05050b5200803e0041c18410040a50000170a510440c030954040c41450a0f081000704050005121503401c0d051601c59215000c1c2800c0e00040125 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 91795369 1250 91794119 91794133
    0x714010503100e090f03130e011505070f1b03030c020112141f0905010602010c09060e0f060708090907050903010b03071409180a060f063c030203101a0102 68
    0x242c0c0c08414031500b501c1c0c503580c00d400151140c003007140c03034140010300b0301035580000144080c080034401c88000c103d03200b01c004040c41303030790b0f0b548013030412100e00c2d075801c01041c0c00300070490000b041440f0b81c40410340714800306000100030204011a40c400390700110046001460312805568102501e000300602040003400301c0801e4200c04003e11030701928042c020550f0040e030346d0240c021200900083c01c21001c0800080da0b694400902a06d580c5070f0700c40216030340c074402040301c03840b80c06508410440a00b008144040c51002d0003080c3c0c0c085541a506428240003800303c90791940700c4203000390060b40e0f60940750148002054211181144410301c00d52040d002045507803111f69924031280402c80702862a0341d1011002c04540d40c59000200710390007030078014010409654894020120f0114007001501d4496524203007070644000801c0004043c003105480c0320041400c0240143e042e1548205000c2e507a86c0428500038010b1f0041084a0f03c03054010352001e9803010700c00440800744020545 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 91796619 1250 91795369 91795381
    0x12090b0a05040e240f06270a05090f071b0501020c0c010305010b070308060613051f0f0906120b0406090c031e0c1709011e0203070f030c020d0e031203090714010503 72
    0xa018041c40c54140604580106540b1582e41c01084d1240c11606800220341c1f01041c05951641080b58920503204040982e03002c5000e00741000640d20030314200c0703000704040d114140c0c2921208601c940010f0000d5505084d000040e400b80040c10310300c50341d80010141d450000700050103598050308040c0d8044018851900420792160f0300710b400c060103980c0070303a0b01c240d200006502c003042a00000d0300300f0b4003101008610030358102000e800754601c0d82c0e144090b115081c01141c1481031880f4010000b60004101002d0199030b80c89081072030f20013000020b400740c2d9002118140d03464400180c020958800900402002e028854034030150100713401c02280864100c040d0040081501d58404100d02100043c441301c025800035070b94100114031800d100c0e0301241154082d5000300c0c4c4403c0081c08000c8040710250085c024000c0b4040c0c0d5070040c0200780c012210443e215103614030302a5052080d4110407605e501c0200c0214050703001c4801804056042c000c1550000d0350085000d81048410020454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 91797869 1250 91796619 91796671
    0x602120c09010e0d02040902090c180405010501080105120a05100b04110705031b1009080703020f0718090303061211090c070209040605191103060102010606020708070312090b0a05040e 81
    0x42c41c543c1200d548082c44914000304000306440200250481100000c0c400b212000001070100c00340040f19081400441c0000d11080e103c0a201e02c0d40031a0050303005105514000000c0c0f005c0b101200e0072107407000e41a880e080d1900420403401c60754256154010380d03003402d01380500c1c948120000e80c841c0c640100ca5803407556a110f540804a130b42071403a80b802c10340c40d00074040150b1788000c4000c00c2c003201300541480d6910b42d000402c100c0141c031805055100040c00410090100e403e60019140b500c0000c0d04418094040144120101660b41030040b4078044010310303640d0450701510700300f880d145c1090184441c100d005031040710468814401c06d00140d90b45480c90394000c1d03001c440425552201084451907041a940d400c140900f050013040081861001861003900309034000d002c00ca40e585420b980f100340502440e0800e400c0400c0500100d00c81041500e0b00140c1ca18010881665540180c1b0700351f042108040001032000508000703c011409aa42e003000c00003c01d00f44054901c0790240f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 91799119 1250 91797869 91797887
    0x20106080d05030408071a0f150f01030b030106091103070906110c010c0c0509070c020901090216020f010c02030316050d030507050d0507180e090618060a05090309040204030602120c0901 82
    0x1008102c40040000c0c03c0103180c0c0241c0d8501c5900a03103084e8010010034070702c080740b00100c464541000c1444001201d01d18850301c4400b029501511039505501030740d0044000d132801402054040d03480b600005091450382c414101054032540d4041d80340c1c20402d100030410710a652006080009170001c00916040100b60451111409d08000780030303156500d00040040125803020b07074800b40c00010401c485400403000c00c42d01d803007243e02d01110303a2200c0900b0201c1c055407002032061143c02015800504100c8098640400b0506013042c0e074800c0c0c0c3c0d0010340313580d10000c00c0d60100100350052008028003000742c07054480340f81c101400b10340f03090703400100300340682c0d60355150305510f40d4042001d20707006401e2000c3c841c51680e20075440946829001042240a4070440072074030545c00050303c0900b52444001020401601031314450321100c58200c05850050300f0901c050004021904440d560380c0700400086110745805030310b90503090381c20102c03034800402e030350400d54040015454aaa10007038034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 91800369 1250 91799119 91799143
    0xc0301051608061807030207170a09030204050a0906180b060a05133602010809010908160809030105100312020705010207170703081810051204060b04090b0103060c0f02010608 77
    0x30b15034a9840030006100c40011040c8101451044010700580c83ea064008124040c084c40800c00143c115411550702ca100700b00c08040020760031002800180740c03035004290805031100000c82e8804560300c0711802c54545140c0d9185111852050031708015112040c03691000003210080c0c0e189240001151a86901035100c1400301c0d580d400001c7c800c00483d035401c10040710980310381d10418511f8031501400c0c4a11506030b02046607032001a11030340c41402408449980b0038440c0b0700744420070500041000754080100c034010380900104800d52024440c1c03500c01d80360001c21200451070b509085c008980604080003c40d0061007050096076000140d03041105c0c03840c1150301d01c0c64400a00c0d80c0c1008140d4000428080c0b000560320100b500782046042c04c80011250390108040310081031313515104061903030f40c46400040000b03010444139880500880782c0940040340001e00c59643c00440c0d0301c243c0048460380d079100c46010760780e580300001003050340450000304101030501c451a81e45425000403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 91801619 1250 91800369 91800377
    0xb090108060418050c280501030213030503031023030606100c08070501020c0706020601030c21150609050912041203090b0414030105060d0210030c1b03050702030c03010516 76
    0x11603a103480750342c030124015808000743c0c00c03040207078903040d0744603485403660314854507080503650322600107811443c0c44042d500007690300310b40c07030700300158041d4000344810321020f083c95000102154003031004510a54804101046183c100700040705c03900f010150b107030f107140d1045c13844400c5600d00180458010200704c50402ca0580851030848603580c903a54024107203100401e00c0410020705401501d8000111401e0f58800c940f5180d0481c0c2d0b480007480301601021000311b081011001c9042030064410030b440050900b0510340e20303103180384000c0011081da56030ba945c10820200d071082c41840d802081103400380c45c6801402d1200c80d058095801880d940d1985c0c80544030400d802859480010620040c00985031969402c81d1108105800c00a60203075003001c0000b0050b1614803006a15075600400303001e220f11419008031700411100140748180101041240320005e110110310700018440e940b00d5036610428418141855000e0b2805402a170401084c0810088420402c0341c1d5110039141c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 91802869 1250 91801619 91801621
    0x40308030f060a17010509071208030a050a02120717061e090a090b09160803040b0712030e0f0a170315060f120709060e1210020c070503010501150908010203010b090108 74
    0x2000882c9011161311408102603d58408400c1c0d031010f411051203011008166000d5698a018100c2c410030f21a200078204e0008000180c0000425072200d5000b4580143c0141420140d01c3c0880104006a4804000c924010b04003006041401e0b00941c0c00744007561005050b00d08060003203192404280050f1150a2180024249403620392043c140c1540260300c0b200c0c0e038184100140e48802c2d44030840000303060000300c003240c1c4400010446040740d0b840c1510340c0ca0b082841e140e55820b083d500180300101612070044200e012003c2044245403030148002c1c044036501454925681c0b110001c1844201c031007442040129420203403c0c24204030281d502d0703030342c07646c9141c14220309215a41038000c013481030320203108945a0088049040e940c3d60340380e468801e00410f003042030350620145c42c2291503001a0207003080c1426038025196403900401252058ad8a07040041c0c02d50b4000d03000901130f800e100c1c007020081a440480e0740c004181c020f00031495035041c1600445140300d035a02180c18401d4600c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 91804119 1250 91802869 91802881
    0x120c150d0e01050a02042102030d0f03180318140f09070c060906061d1603110c01020c0312071404061d04141603060501171b0d090512040308030f 64
    0x1401400482401c00001c014500e4262034400c000d421034002e406a0750001d03800d28102c40c4841406003140b41e0001d005052840c000c240c02c403492040703100c03084105034560140d2a04e003607260140c0c3e0b421520a48482d4560444065810804a95548105c0d10602003856010298a400803001e440c500103980300d207101d9a41c1e95090700d150f9146000245682d252203040010701a2581c403410584070000208820000d2010800c10944410b607840c0d46512074200f4032000743c60103648942c41c81c05030110601c0c02c000001d00c3c0c041c2280c12504901c185070b0000100d070805241401941d90f480000350030300440342c640c010200300c01400382d80210024090501c00001070ba40a010f00303000c41d440c00810038031005c4852358544004810669614804022400180c1d102d01d00901510b0281c13101a5203e51000b42c1c0c080d080d080130f04000d01500804004003c6040d21036030220001e000e803810000c0003041181c4581381483c60003941d44032a44400400740014000156000100e81c2c20001d0003a000e03072151516 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 91805369 1250 91804119 91804121
    0xa05011b081306020309030c0409081b010e0a0602030a060617150a031205120601050306030a030c11040e06011e0e0703020d0b06040801090c05040c020303010303140405030d0e120c150d 81
    0x10030b02c0c42d101e50745516000200250300000401002c0d01c1a819a0162014103042c4400d98419003c014601c7c8401d02080f0b4140d55014008244c5070405400400e0200520418a041003030004064030301365000402c03c403c10000c2d004400080c0a10314200c07220b100d44107400943c80d1409488104c01d80422000c8820790703603c1d240020301458106086100c40e4400e03c00c043d02a5201e003000b01107003240003001030b115600035000c0d030344181c00150240ca40200256800c499481160000f1501d5a500b6402111a520395100f89105a9038602c001e00d015418010300043c45a11801000ba184418901c00c0c420b40d0f0401e56032075002842c500b0003603181c0120044420180c00e480150a070806404100000c5c42001500662803c1e40125040c035074042c1c8407410b01050f1030141e8849800350b4410801000002d01c5400b13a00c00000690084c00d0038592140000b03410b00c10610a10400101e518182c11424078000d14490000108078005040100e80e00000c50011000c20344415442c00011880c0e84040b85d003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 91806619 1250 91805369 91805377
    0x30909090a020603010608040b0601030c020d051c020301090605090919140f01090309140411120402060d02030103050d03140403020c060a020106030b0a09050c010f020304180603150c0e0a05011b08 86
    0x4020f050a40b60341e1035540c000c02000c03040b078050720328680313800204181f075002e4829501c0200c2c0a40c081c007075682c1c1c2200180c40f06d85c40540c080301919809014404d240c800341c405140070341442040814054a0142002070100c406032095016402c4417048610604001c840d00d02d22541c0b0020468112a0f40b845072411f085601100984a50804010a0401da4412080310540e001245440150700800050104130b44480d00d1514111700c2c10048040581e030b1800704642c0c803500c000c1a203890140c1107205802641c10aa1040340c170f581c8441c00240d225501340c081c4030400c190580d902502498652802556403102d12060344c02103c001401c021034501c00e4000c903016580003400781d07040d403c02c140c801c00180386a941c29512030140d8084c096046d0b01c285284460110a0350080d4101410017040041c03d102c00340450312081c2d81d56400000060700a5540120282900000145003005d4407002d001112000003652161380c40e040c042c4030030703030b080240f0b09069000c1411082e44155a454801c0071441 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 91807869 1250 91806619 91806623
    0xe03130e04030c0212060a06080c0a090b0a120807050c0607050c1e0a030302071401080115080703090f030503100b030105060406030207060905070f030c0605030c0301150210060924030302030909090a 87
    0x5151100544411350009100c7d01410103500308200305035951081e1901e0b0103441c071406030300000b003920400c08101d203904126032088000700707000318495440445503a0503003043c1d01210b0101010030701005101c2c0c148500816a5401e50304603241216640e1110b0720390700d030084450b10820f008d5150340036040205040350700010020304401100d42e101e0802035a01e40c07492042e0023551880c11280811540f04404a904071585035444030002c61000c00d0640d20080010009401c056507040d410f030104140030800390403207000c0d850301ca0392400d085241e4202c1d0032654201090b01c20703040004000680302c0d041140e0031503201d4600181c4442d01c0d4a0082c2c080d00041c88094418400d182e00407902e024000e0b070443c2140d111b80e00c591516a80c030b400a4500780400c441c800311030481440108200c07075072140c3c83d0032400c21500c150341000b1b0600005004903102e58002c40481a9a5100b904141e6440b1050241c41410004824803032407035a81d0017035480c03140650f00b9018500319030200d174000300c00b0010300128903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 91809119 1250 91807869 91807879
    0x30e060a0c061505150a021c020a050304141002010606050a1407060e0309120115170f060108070602010e03070b0714041d0601300c18090209040e03130e04030c02 71
    0x28560000180416078000d07280b141000c90fa030901c80c014a40200c506d072a110750090201458240c42449400c4600e95440d01940140c82c60b410018100340003c001500710415403098040e14001400341c15916075441c1b0056a250074000d0110076040000c1d00c10725815443e2145100d003150300324918a002e918801450030707081019502e800d02020000e419520740607941f468401c480004c505003a00c0c801100e0481070341e1401028400408415a000110b00120046a1080b0a084002403a00500341d101d0a81034102040030f110059081c0a00700465080c18010b60610845445844400d50301a060805008a116529500c0117040c001d60300182400300c40307280e00a0000448420500b0104d828a0009040c8055900c01080285080300404442c20001d0391020b200344000008020a11042c010700c980381d0710445206071121100f00141c0f00700c4001503150948102030000303460001403080403e40040c07024442d0303413440c0d5055000700c1e01c54600142d43da8581307040507144400c61450182d084 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 91810369 1250 91809119 91809131
    0xe040f06050301050606030c0702040203061c0f050f0a0308011548120c0203010204080106080a02130b1e0f0402030717070e010c030e1512041e030e060a0c06 69
    0x59051a8050401c540056000f480715640711410401380f8402240d2610074054180440030160509501942e44001c0c0601102c400303450507001851281080e0070219001d40c04400c800042000520455841181d0800241175520302d503a009001c110050040f07100d0480c0f160710004e400340c42004100c0c0d0442c400705c0240302c0d201c031006080ba1050100b5907250701c0c0207110340ba843c090000900041c0d103195000b141041942a548601300c43c10241d40400ba46c0c50b640038080490240000e00c80c00b002007490400529088040c0e1050103901440382c00c070640e0291805890700d8060300c541031000502c00402071940900da85100000700400101d41116410920120402134480c0e0003800c1841d4110034050281820b0b612100101c80c030070707801c68500740054440703902d000000e80103051045801d10010b1942c940301000c81040c00c2c2a4005140f1382c980d0344890170501c004e010340c00c0740daa40100485404807101c800341d0381f800b60a01500081c030b64055003000070074001746481240b01104081d400035050081c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 91811619 1250 91810369 91810391
    0xa081b010c170c1b03070e01090209040908030910050603030901080118110a0305041e03090b0d110a0503220f020d03030e16050f1e06030402060412050703060c020d02120a0e04 77
    0x2440b01402c400030300503c244c0b4035404452a00140311000c46a0090003212180e0804d89041c02079081030080e81d800c540c5074404140018158406944509610703030007440c0e512078440c40b45050b141c0c040c0260380660810806c0000300d0368800d6006040d40d4201a40320800c2d0000c0780008000c01000301601e94602c404120007400d164180c110f14029801098110918008120720850a806e201c2d4000c0100e48458800c101840d90303200a05103619190782c0c0040d852440740d90000300c40d03103d0002140041c3c00002003041074a008584042009450691840021851381d48c01e1030704090b811001c0d1040d680c11412004051003500701130202c038034000c1507801d80803601c0f000c0c880122582c01a28410181c2c522051010b003031000302200350300101c0f20329000942e1620188060f036480500284d03000242000b0200d01b0304100a01c00344d109201d12f00402c0c40c44e00c2d5003000e13821224444280011904481030741c81c510f07030340000c221901403c0070014036550906070742d051322824060303407800d60464104114144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 91812869 1250 91811619 91811623
    0x220510080424091202010c080f0612250f030510090c081518031810051303110a090606020303061026010806060f0105041203031413020a081b010c170c 66
    0x503d081c030540c03074441c0d0416051800e81c01e0740ca1342c05117940007540f4031000070091189900410b8103c07001a00c94410340d0302080005081045100c03101f8010b0119107440c80e912007203110254014101c0d00e541c031520904555505032198200f0785540100c5813115151024010214000e0008100e1442101c0000c0fa00030f101d041001c008480540c1c0c100c0040c180c10075009000b0044501544083d602c08404622020030840c145d2951460282001014800c0c00460788070174500d84050f41c041c0c90308000d01047d0130100f01c0d10692a400011055040c060200302c541d03000410380c3d41082045500c5403802d00b540d40215160245c560000510f00c108807140600e102d601c487c0700e416140040d0a0310507a0341d030281440f0361025052002400958100410092065110a1464410300c00d10300410480307602c14a80c034445200380d81c150540c003090107954085103000307a104401407009501400d404032020319141e4004003601e05550500107440024802c00c1903002d040072450811041d00d58403a001011556 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 91814119 1250 91812869 91812881
    0x6020d020f16060f060f0620010c0503091204050607030e130c05070302010b0312030105090a06180e10050103020f10170702030909150d12030207050111220510080424 73
    0x525204d10f4a113418400d10a41d000300000c1c1c95040340702060591500a0485415403108041c0c0300c3e4001d40344081c81c0044082c02007000c0700340c80782d40d61512400c201c0c100c1e41c200410001605c2d0079080400c0200610303100c2c01c00392180280c05081c402c0c000032a00c4081000c1c5d0901d440c1c146e503950b02d410b1078801c956030080003404a55010f5402042502c0c2c0321000d01d41e40b10140128441c00d480107100401407454030804440d40032000b04008280d40d8bd03100b241c04981da0354240906405a101c800c0c403800e8040c104103071520307004c02d200c0500a951458000c54400c8021a66040c051340e051103e9a5050340515107011406a070f0344412901441c0054009440b07800860480384912403040200b4046215008899400e540003084400d0710646a80c843e410808402016014103800f03005c1c64001c10420f00c5421142d1003005c084503661096104401c1030410011000600c04401007010f103c1d90b00c4a40c41a0404442d505069200d5240d41c100010040d01120400d541c0048100c071446100401d038000c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 91815369 1250 91814119 91814123
    0x50a2a170c070209130606030507151701030305130e040c0806010e15040c032403030201050105010201090305090411090909030409050717240301060608151c06020d020f16 75
    0x5104100c00045a401401425503603150001c03018007000000d07250048034a5088034210f4402e44080003596074000946495a00035261500410030401521003148051803007a82c56280c44540e02c45040070061024078103010180420801040001207000e41c1381d0000054480c0c010801c5a034030305440e081545102e00d000d48800c500510000242c02c2d4126200c1034010b00c5529007006880ca10803040c0700041a086012000300741c2c40c1c0044418050f840c1d08941c0070030312803010b13190380d9909604000e829140b06034429411a80761881c4480469400410b695410034110303400315001e00f1200c0041a2030166400d501e07071190841d8140459554008000d000315a5455802d20065959400a580324156500c22816038070407100000e00c2c0095006c54081c1451102c080510043d0008000c20b084a106412050100b00c100307041c0040315046d0101928540c034222000e0254640c0d240b20541c08400c0c003e8010318881d00450011a0f4216a4050320309070760080c0300e05516452081c0790355610344203030001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 91816619 1250 91815369 91815377
    0xd0f020d0e150f040f080c01090b0918090309030f0c0609150408010c02100f0605060d0e10021305010801050a0302060a11030418020702180f012303061006090e0f010603050a2a 77
    0xc000790221001c15281c1030107c0503118144002d10300940414654031080003981c0c03061407030111555100c0413403030b014051200c0380c2c0190380b40e03001c034000c4c18a0124040d10341c600d66030000382545802d545005c200d0f41c0400382601c0c8124161070704400c42009005c0c030382110016509040c00d1044e45980003a0400c42414030060500041d010106c1c1481103480e90701480d6000041048000c4050101da00321044008000e011203102c1400e01501c3c0c4100c0e040b2044400242d801040100310300c0da80490310324090241159910708292450340028000e22498000c4d4003030080128440040590501c240c800900d003103400040312a00d084d001c0700007907000d2041203110300001418a0f0804091002c0b640c4500c4148c0c24640803642030910684000710200307680d20b50f90b0a442c100210b2903c080c802d00340140070540341411882e0030018040d011924507000170040c0d0580804021004140080d81c9044810300d05001807640c482c845000084c0590b855210300a40c0f60b081110135140060000d0f0f03102003003030b0f51 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 91817869 1250 91816619 91816649
    0x4090305070302060f010b0d0c18030305040f0501020f0d030b0d050f07090c08060109051216031a01080f07030618050313080d020a05100507170403110d0f020d0e150f04 74
    0x40c40c6014903d003805071f000950301c24002052041103503803100c080260b650401d001404e461101040d43d25295400480000c0d1780810100b00980200c2490005404240090218403030225407203030356070300652030312010140c6542e00c03101162142a00008020340001c1a20100c1003600e62607903a5444e54821900d0851401050600b90b40c490000c1300c2c01500305940c1d120f00c40d4039010810044207201038800c031070781c02408803555414a04c0385404005520541c0840307100341e040c0c09000540c000590000d0855008290320054180c000b08410060720b9010900207400d0420329000d1500c540642c000510512000814000d02e07101004074004542c05841280e005800d864070480c0c0380d0080031001003280e4844400b02002d40001e4001c00e501424514020203542d488014007165503c1c269030640c081124524000b860303c0062240801c1901142001c006a130030400d0002d644482c0708d4100c0080120904513140c26540380170030f81404d0540664120b40300c03059003680030400e501c6442016040e10785a6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 91819119 1250 91817869 91817881
    0x1e0c0605120a06030201051207140c0a05070909150c03110d02180f0d080c03070c031202071e030803040f06150e0108010e0d0f09090204062c032107020409030507030206 74
    0x40643c0080d81d40c182d48550902d0030013003590f0403058000c1d01078400c1c00305030b11074601860340320b001800355040000c0043c194850641011414004150415050f607400c10300940049001c040b00d104000845800003d24003c11900860040c2007210000c02c01d0100014032121492040c1c0240810703000601104003003103a90810803412407028906245c01000a22106020032843c03005010110114010389161103416552030740c01d040c0316042103c003c0b50240f1408000c1da0b0402410300903000b42c400c2e072a00c0500302001441b80840b6440000c01c0ca0200000080402505805409039150f0200050107032011407040d2000c14a03060041072107003030100c000011030309014051104411030b100041c189d04002044106d941c012010728078005c0c41030499000641103140d00c02031009004940d40d014110183c2c41e01c0402400780c621216501d5417444003501d02a941c0840c1d105050114135002805a2503903003502c1103207010710031000e03500c81c1c549041c0100b0f054101005200d154804d90a881880c1c0e124 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 91820369 1250 91819119 91819121
    0xb0a0f0b090c1b03030408041e03020d120315090f0f15090c09030b07020610050d0b0601050a0903020429060316080406110d06092003041e0c0605120a 66
    0x150609950026000020070141804100109442d082c5007400f42c8101c11454103c500e154000d0b5002c80c1c4541001804000740090802d101e625104003a9042103101e15540005044039060301000d004010020b1a440640780a503212540d202d40243d00070000c90307520741c611001401d55034841d190306401c251a0392420702061041100b5600c401c296851000c0c00c00402e0300007410a04604414800100c80220225110f01c052a1141e941a4001c0400d4079150300d551114001d2076028600030956011554009079900c20031079806807080c0b07080c1d611016110070456490481d40d2019410524103201c21035400400c100420f2042e0100f00400c0c110341c0690280702c000d200841d4000420b510460040c16064481d6100d04d8002d40203000100c0c81d03c9100000c0e048550095070700a00c160760760b0004008080080c0aa51014800d0b482c10615180300c14988102d0f52000900041c0500901d00703a410138030548409450101d500290b0303202c2c00c2d1340c039210060010350200320f91800e56841800022208006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 91821619 1250 91820369 91820381
    0x90311030405090c0304050c190f1203051207020709060b03060307050d0507030f020d0c06170a05070905010806030a0614012102013e0304050112050c0415020102040f030b0a0f 77
    0x2000d8021040c5130b842c40e000100c60340000e80221250b01850072106210341d82c92800e0001c94032100b0800340301ca0b00d401e013032403030404042c1c5c405402c807004000c2050100b508002a20418034001201c0304030303035540c90b404a040c1550382e008410754514209000c05d80000140141d44a03a0081c0d08599005848004000a02c25010f000410ba03910040e01030001415414500d418544040c10086110031540d40300740f5844c00d2a00404000fa1051a00c26884003640c500c580d040000340c84200040c2c10110300085c410606801041d060044010200741ca0391410842902c03d81c1c0c2081c020000c40c0000301c444602d8950030320908144c140143e10780d003c1c00c180c24001c025010b505845000f90070aa00c100c243da5405040034141140c1c00c1d01c6c0c41c00b03452454040d500c5030b85100e24000b03103076110300f0040090310420001c002565070604e000d0400c1000091541114251010712581140b65800050124064840c0b900088a1100008000420002d00980383c50103406455000e1007100038006400d421940c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 91822869 1250 91821619 91821629
    0xc05150403030c06020d140a0c0815100509040f0b03070801021830030c0f03034c030311010506010c0206030a020702040501120c06020f0c0103020307030204120302010903110304 78
    0x98100300801c0040e00078810283c009114800c05402d200d903401c11071045880c0c6a0409084609482c10080803c107588240d01e025945418004503d017050a0794021040c0d220100303d00505a074440b005049005d01d00b99503a006000b8000e201144401401d0303401b0b4072003400d81d18040d200348000818010010b000350f44407091300b040a03001b0303001401c04201c9a1a000c5103c8006000c00c40505081c14100841c21298000c41c540110303030f11a00e44691a00d002c00f0386800c0f182c107420600074804054020100d92014043c4001081c21030b40a00200e0251050398007014400d00b82c43c5050318812288010100302224001e444480e10b24401d1441c15007643d80072904240007580355468440185843c00c0510f0704006080c2c001800d0007800d070301040c21140280c10165121448100c0304040180030038008018001c244040c14503c500c550b00161b80c0c40e0707208900e506054002c8000f4140750702c6903050b500140300310038105980d09120709002c1e0080282c0c220543c00555101c90b1850711540010454007250 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 91824119 1250 91822869 91822909
    0x702010f02060c18210109020f0406030203060112050102131d0f070e0d1403040602010b090a020903030d02090607120f02010e0303391c0501050414042603010b070c05 73
    0x101d00880c2142e914816004c035640c8000220200e12280840e104408229410540002403c0081c0d00400c0701107920b132107169214504241c024801600c01250041c11140b0202d5920074084a6145c040d029004886020350003008940b40041d186540308070f80c1c1e40d40d00a16803a00469100c1504179848100d0846146020403c804004010381c104407807200c1c0200c0c0105c4560000c00c2c10f40c10180e086038031507400307180141e4560b01c16181c54a010408203030000c50040c0118603240c1103d0100b9260f00030a0a000942e0358085169005d030f490b1f04040700c441c0e5500c85107561156243d8840a007250f14444001401580381200f602d4401d0b0000084900819062045000348440b0995204040b0f60148585a40d9030712151600c0c1003e952401078000540755031f8541070401c00d55140001203610503400310f442907090984420820300603000c4190019000180c48004202201132051642c0404c0265074040c1000400001c0511400003d041054410700b41d100d041951442005819107487d00301200300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 91825369 1250 91824119 91824127
    0xc0319180f05070803030709050307081504021309020301060b031801060609120501090602040e010302131103040b250e031504020a121e12080115080126120702010f02060c 75
    0x101d01e840e0400710320680301d4021181a16201c401060541c3c205456003070110b0544481030241d460f081c4a0700010300140d1f402800e00c1c2e004984a41c20102c03014202901503015038032040a9800280c0109413102c2d0054000c1c006541e884140344071561049560709055200308190240e0124180144012956070342d0b00c0c42d0525080501c6803000070f6a04004455540d170310080000080c246001400003000c141c00070020561446c0103110100202604103512140703441c81c00030031285024103484e04a43c000c0e84040d82135641042a60b407104841c802094114090203541d2030312540803221413200c503815425030300a207003842c04202b404007080d28020340c000b0030294248010344403801c2c01811680941d082c3c6100ca181c0103901c861080c180013003a550410100110406580c010098a0051044503100b40b654219160020020141800790020044050310340c42c4101000d9014185c03c5402d12090b1b81000003100c03580900e950003c01c1c12400b282041b800000c05900116140c0e1241c2131500081c2d1074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 91826619 1250 91825369 91825373
    0x6040809040b1c0b1608070507081b100f0c05040905100e1603050c04150f030204090f09050d141b12040806041a070c080c01060302090c031918 63
    0x1103410106031260800d54980800c07805658007400d031030405012914903003812455040600d4502002040c0e10360509030740181030365142d440b061990f80860240391036070f1104d05514100682d88070310b0740d052019403a840b02d00c0035041000701d41d0420800041b0400c2104e030741c520001809032454000403002042d810310081110010315040640c3c80200e07001843c910684401406483c1c6c82c064410f451841d80001114500d540c061195030b800c000c0039202ea50506103045030030300d50a429011100c0c1004940c4603000b902074082d030140c80152505840c24489001440c000100420b82084180e48902c20030039a07404240c00b980d144802041501400782ca4030314012140d07040300c4031112103500c0130311a00d02c04900c00d80d24507010300040d080c403102a04280c1040d0400280a40032400320004811545003402101074004a0b046045580442c400f0384854010f2100c42c01404103600107504071449000b0428240900401184241e03034265203640040d0030186c00004403036401c1a00c1d01404625004880 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 91827869 1250 91826619 91826633
    0x30e0706140d02040e01030807050f0a0c0501050a0c081602130b01080606070507050a030602090102010e0c0307180b0d060b0a060201050103080d3b0706080405030409020c03300609090604 82
    0xb00740c4041a0001d0714041c2d44a5801904503000d0b4802d85020070003140c0e00d0104003052202c0c1c1d640000400c01000526002c0d04c0c0c4111186082c0703c0d05060007000207d401d105400b90980c42c40083e0002c01f0b04d42c682160108071111440300d464200d101d810b4846440d00016803510440c5c200d150b060b134810f1020f589000a2003003540c0000d405403403600c00d02e100018580e07600e40c0c5110207148035440c003603124841d0000190035510b415410a5842d040800c5034000c648000940313000f2154100024034041c84441c2d02c007002007104030340706a0401c404210345014030043d500600c91010054420700351880d6958000c03401c960003800700400310700c400c0007034100071740c0c0c0e681050300e01400c4820a9803001801c042c5180e1a00b145440100614070708400c003061000d400e0000b01d0040ca500c0c02c100300c00f8941642c034140c40b441180113540c80103034080341d0084c9115041080e949841d00a45004080050708107102c492031480070b100250100e0003500060035810704290319801581c0b200c006100544076a03503aa1303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 91829119 1250 91827869 91827877
    0xc060903030720090c0313020906040e06011205160f03080a1101020310030c0504022b060b0408010608060606070510111c0605100f082d010e07030e070614 68
    0x1581071005000800202d64203000b40d011862088041c012518983c000344203403050000c0901060140900c01c01122074a08006040200da04131a0000341d9512080002c0041c0321054041c00d09104100020132003680340b03030345440c0d50343c0035000312034202a48005031070b60720507140100d202c07010340600d013000006c403080060321450300a420881b074106980d8545a003240c10844210400d80349604080040c091206441005007130300340c406501e05110840507142c1c0c180e469404190002440400c0b0038034180ba03030f02000c0070b0051690007070356503036607031000034064109405151a0f50160b48040703829858040102e0703035481d078060041c041d140b200414000040280c2e04403d803103110200220039041c0301e4040d00300310010340588009851410b210a000b05011720382c90313140a20500444402e00283c00c5060140d1001c040c80c85201c0070503049006907100f0144c201e0f40d0340300c0c1e01103900201c3c0c50224901918403d50141e54100000c0308000902940c0f1886445410f0204240060140003094880024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 91830369 1250 91829119 91829137
    0x801020c160f0e1e09100b041a060c01061205280b0a151802040e150609150403050313080c19060e010903120c030f052505010905070609081005090c06 66
    0xc03e151401244e0040b0582c4411109507400f0381003d000c1c201c00320b0462140c0344540070280c400b00035907455120140c0c034194001180341e100c2e840100c0c00f002c801c1c0342508454060003d0380c100e9008107009142c8940e07104910300000e0801c1c1804e840c0102d580c0117800d03189106c541c228156809585952110500a102c240450f05c03241d509400c0c08160105041c40c2c1c030100105000f00184d40344d1402009000718030000c0c00022644c0c8000340d20204aa9500381528500542103a0101c152662030110403491311950380001d003280804a000d80920402c000103008a508000c1074401c651088020060444403e180021031a04e11850601c40e9a00c5007140004000040c100080b48644a03107030703005030b03c0e461f425420018003030307500d148101580203035044e880360039504111b42041307205121004900c00007210900307114544102e24041c010309400000b900c642007000d40d800f444c1c4034100240304c003225001d0641d0511510a03c0f0803501102c0c032844c1d00c1624841c0181030303902c10820401a556203c2c0401d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 91831619 1250 91830369 91830391
    0x712020306090106110c0a0b041e0b09040e07030605070c0c080d0c030806010314130c05150405010c111315080a020d020907181403010513050a0f17040801020c160f0e 73
    0x300f4000c1c0c1e25000c000308050903c0104149d01d40b0300c0c000c08817860081d014036004401c120210f040100c0e60f100410748240800c12180820b487c9050708540345484103d900c00b900b05420300d004e001da00c40c1c00030000e80303886000315003034040140c5500e003981da01c00301c100790305002880c2c00c41d4410100b480b54541a0b044034052601059071842c0b00c40701804814162401504803035401010001c00a40c1d07900f082c0200002c0d075440c0e1a0f1b00705158488014000c1b4801c2328103124031640c41c802000124030048688140051070070250207001c034a400300906030b0b00400b010540b0024404a070700302d00090f212850950052004805802e65400d10002503800381c4044180075282d40105110340442581030047c0202515501058124008240c05d60300e0144c515006180174075107000120384081807200d80b0700d81221102e04500714600d8108518000d00214148804002c900419600c4064006045001f203100854012f14007007040c00704042c8031880b8103504000c1d0420204a00c1445a603807551209018034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 91832869 1250 91831619 91831633
    0xf0302160609080c1e010509010903120203070203120106030b09060f0d260a02060907050f100e0f03120a081b03010e280c12060317070206090a030506071202030609010611 75
    0x40080e2500b58400340d40032190442c00317400c600d40c2000f403003559400040c140080c0400300c01c40d140601f0000101358800c00c815000000aa0543d00810468516000440c0031211669443d40020000c20180000e00c2c4141d1800000c00c407107181c0316043c00030008000b0f25808442480b640d6024900901c05950301c200d4416070085501400701c0c402516070b00c10203801801d80381c80c0c241000760400103950000ea00c04c2003188810081a240e00b210007826803040d00b41000004082d00c0040d000b498040c8030503a0521628902100c07189296010740402012512429940d032240505c4041c01000b1890380d1a03510b0003440100442a403401003030b80c0002c840c40c801444c05814807241408140207602031001c050300c540d12050010741c040c03002039a0400e101002c220381b908641d103084441c031041c804a042c4010102e180401d55139200111795400400030054050340d607881c0f0341141c03039940c22220140460410f5509144d0f1450728022a8030408000300325000076030808000340c03004c8207280100c1f04d080c42504 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 91834119 1250 91832869 91832887
    0x4090b010e060d0b120609060c03090c0a03150b030c030c040b0112060806010302010e03010c08070e01021014070801050604030803040b0a0207050d0804020f030316120507051006060f030216060908 86
    0x1003031071a030f40040c0030865400c42014001c01071100703440440c8540c44134003040700d0581c0214920390000b8242c54000d40d43c3c3c075140e00b03091400054a0540d6170111900030000108156060018014512210b0900020151800705512400344101c1103405401c544001c00c0103103016030010819803014109812803120580040080340c02a400150342d940c0280300600666822401402105400b10000c0c4011003625030011300c40a000b404c44028000310000002c02030b0300a20421104160002041201951589124190100599240d03003c100c2074000452203040480440301500e0b0840015491130700c42e0b650302807000304c00910080c1505e90a000b81000039805004c161200907403961084000d003043e0041040c07944042c107203507109a00c100700640940519071082520560007007030a84101905003000d41e114403d80301c0c020841e0003400300c0d104000085600507002d07070740300342d442144241203464180d04a02c20313140c0701c51100c514150a0743c00203519800ca425035610464009051446207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 91835369 1250 91834119 91834129
    0x5030d2705070303080c030105220b04090b16050c030a080901180b040308010608150103020d0902060c070e061e040e1c05120c031003030f032009030d030501060504090b010e 76
    0x403201114035800c04441041819488180c580d0000c0d0003004013032565150500054842107403480e607090b103107135118007560144210b034092460080041c2050107021100d00e0b06030108402100ca106510280c03580c100c10941c440d00030b84503c5015500118504070360000d080d1002c41000382101c031a90749030305440c907402c85003452300c4c0c00030761140f00e04100e90f09013413030301030680e940580015081207440703400c00c9401d28400c2d04000d02d100d400e00340103940311184008032000e4550454040c0d00020000f8030001000000900242240d05040b1080c159480c0c1e00c0c10029038464884072050001d0603004103400610b030541c030030300c00400181c088414100355004035480b400a00c0c02a00c1c0030420120b0140710700d0100d02c00642d40001344500d11443c40c60314010103030741403840b80005401c0103001c041002e6240c2c000d82c0038005c900d10154032088103079084078000c5800d51014803614000e0190440d682c0e440c0b0300901800c0c3c1651904e03280c4a0609081103000001803d100b60440d0411000f18001d641daa1a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 91836619 1250 91835369 91835441
    0xf0f0f030504060806150a030b061201080a0209161d0d05010504061b021c0309170c030702040b0d020306181e030703020705190603020f0c0d0806010f020a05030d 71
    0x21a88070940c030303a4908800982804001880503029482003004c64000940301000c6036098280342c200010a0030079031003c42c40c14010b02c07050a1491885c00000310701008002807a000d01482101c0c16081555144641d46a02006c400311034081040720082c007410045505442d86001f40c05003c080489501d034440b2801d48806032025500700d0f5583c000f034081814840b808282e8a41180010060a40d0359032504500318001d105250805541d01c500404100d0030100c41c440c0c500d418000103480e0032131640c0a9850741c1c800001288a036260a140030280e0901820714801c681c0c0003000303054560b40d101c0b140c614860709012040514003d800d20102c0031aa004045000492014000c50f1030311540c1c80c02074940442038110610413004101c1e840c9147c005081113000b580e5042c6805038a9a01d0200c10306014050b80c6c00f503031018041e02ccc8040780c01d25880204184690401da0b2110700c003880558040c0d03103d80143c01b0240ca69041040041d141c0d007416044540c102c601d0051010070800d120301a07212002d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 91837869 1250 91836619 91836623
    0xf010c0807030f0801050a0305030414010903080403030806040605041e0c030b040207420e01140916051c0f080403060c0203040f0f0f060f0e040c1107080c0303070f0f0f 74
    0x344264558002c030341d101395902d000d4403054840317000c22421600c40350b640703000d107215020201e40c100380c1840240e485148260000d66000448a07119902ea180107003003003134101c4100e0f008034505840011245058042c48041d58202d01d00b158803e9a80342e0448082d00c103c1a1a2040c19228000e0040f5a2518401001d909026800e44a000f130090a0001d030031411007013010102001c030810600d040c03004619456144810a8000141030b10503801e000d0160400c24403045041d04e80c00c1c1001350344100130a0140f48003c049121900e4242c44204028400c1c01c1e94800c071420003442050540081d0700f800054400724014104e0904281e5a41d5400b0251245404c01800582010404004503000120808090503240000228150504060341070182c860310540c410440c114035684803a6004c0c0c4100443d101002d0414481c0c6115018080c1031001d50405111a6208206002078940c1300403032000032a00c00180550300d0700e4440d440b5010300c110b500030261440e001440d4030078000b481078503441c001c00b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 91839119 1250 91837869 91837877
    0x20c060c030405090604020304050601061b020a03081b01110a0507020612150108070e1e01030207060507030506030705090919021201020a02061e160f0e0910170d09050f010c080703 79
    0x2e410711051042214001d03104a00407070040c014440014004600181914801d141001c0c00c441d000440c2180b040340728201a40100c40c600300030040c81038400050400304441d0260030500840c0149890032100c0305101250402c0e024002b01000c070f84140c008001480c0014060b500f01102c0c6024844407107000d540c0c1c90800442c0004040003540c00c0b8686c030303500c000c1e9400d011750f10202c1a408a02c8031804241d03201e44184d480500410700303038040e0703069860180c0c01c004204107600d461038001e070080c002640d17260310a21440f2070000d5a881c204908a01c10088400505a8030310600514040d400081702c040340c0c011264801641055001d03c060003500000398010b14007402d1128441c400106c00c42e0351800410b91080030031005006414103008011401c1c5032098a101d06501c08644500b03030000020b5000d01407800307011401c0503400848054412010110783c00003800002c0320364404205d00080d0115105090810152400c561481c4203004181171100b028007290b41d840c100e55010840c124041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 91840369 1250 91839119 91839127
    0x30402010f180914010609120f0305030a02070503070c05090a060b1207091205210909070e040209030a0b10080606010c0f050114010b03100509091e0a0506272b020c060c03 75
    0x50380041028010000d9a10080d12423000b5140e204900c423200074050300b800300010100c0c80d03c080640c1110b40721398100e41500d45a03102c91070001c60000c030620445115142d280003088180c030161080204807501540164a800070700c54449502c40390042149080c0040f1103000503848039400b0410300c40d180320b1000345c01300c82c0d0409801c800084240700041d031041c40c00d0003010040d480e280000c2d50407140e0b904021841c0720030600041c001cad100d03101c50150180a02481c110400003070724032031801800d00311030140c10b15071101c0704145d40b014101d41701800916420741c1071001c514811404032000e4041c400100d020444035084105142d400c4e440310301d01e6440001002440b4101e414418060481225006010304001044942d541340342942508605080000542c000008011507450107500c8410f4500e180340030700030118010451000060302204122817003044003004180e242c568042c1d0155500403084141440001a041100318000d61080c00000c40c01999101c1c040c0c2203031421540250b0f92 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 91841619 1250 91840369 91840379
    0x904020d020a0b04180209010813020a0503240a150308030c0403080a0f0314151c0f03080f0106020706020a03120b0d150b0402030c031503030f03070203030714030402010f18091401 79
    0x150303500d00e02017000c91510611041a075070380e0001050b608024010303c0001d580049000060f65100e040d03100c0c079030500c107192403503500e8150304071000a43d9400140d40401a41c6400446054a49141515800e5140094240300046420b40995000303a48102c800d0305042c2c59953301c4040358812141480070a841d4501030b2405c65150203240c05081e080302c0071a15505001d070780c070036546201228a174070032400da1800c1c5821481020101c034010780c2080500c505001c082c140542072074820340c0c0340391003601b042001246840c00044d40030110380107a80100405419920112031400c3d4180342c1d00f10068440d42c02c0300c16990384144e00c0c81a9401150a651f80e02c241039220412590045681d5005070b0051040000740b81094056035840094128000303201c0c007400001a0442c802c841d0a12030326000807043c0000181d002019503c5922292541c2030741c40000a500003c034041110020300080314a0121201d0b08d20070842056071f21400e0401d450100c3e21000d0080585010410002c0045448401040703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 91842869 1250 91841619 91841639
    0x3050705160302280e0703020c190b0f07020604020402070f0204090c050108070f0c110406030804030317070e100e150720100504030816060e0f060c090f0904020d020a0b04 75
    0x943c0c402c20568141003407503816030213401c041288980341c0d441407007200003241580690111641e00c0c109006494109160300e095095031000c1c1101650b40780d54481c0000c0c02c0112901242c0d004007002d0b00244541e030780302d030f007040b0185d80f09403400c6992132288a80f07030006844500038062024411420008618200b07c00188113110080c06102001000c130011003417260041c60301c085c480d400191803510b41d80035002040c05007a0070392000300325000c002000401e25038030181d10804401c211300440080c1d100e400c01116403100007480c103a0b004603145142540a4050307404080c10880144c6000d03404035087c0642c0e0910f0304102c1c410703920340c40c031803610203400011031944a81041c41116039900094401400601e540200d000c0280611400a281060300f03040c910445055a0301140134884000407520441d1100364100c0c2c40890ba210306400f0522840750001900d910140103814050098901402c0046000000d03005076080303c10110a20050703150f080404010b040078904050395985000d41c0d0003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 91844119 1250 91842869 91842889
    0x8070f062a05042102030102040314070602010605060f09010c0204060f06030b0f04050f0c0c01020909040309030302100c0e130204030b0c09010219020303041818030e0a060507050d030903050705160302 88
    0xb0440100003d02c80480141c0200c1500385005881c103211000c2c91010a00902c40d43d0000b4018100b40d2451141c1517078002481c20070b462842d8024004107503a00140811030103074170140e8102c40014030414000d5403117079042e000010b00043c000b0507030968034030342c4490b0303903041e0303080f03400002d4a6003101c50840c1444604500c411400f59030420071481d11000c1c81c4c60f40000504001c0c180074001030326000d52002501503480c480340040041d002410540b4003c0c03d0480c0c1840200c0c098010f11800041da00d1140c4540000860141c0300c84081c2c030890810410782403c0399212070703d04c990a21011002c6401c10b0f00303541c4240c03800000c055880c4c03400000a4940000000100552804071101000588000c004d8a08030b42e1400b942101072003040e81d00d03c003c1c0540d400c500c64514a0081d0710810b1503480072101c442400240c03503c221407a15481c00311020322881102601c240e0120b80c82180c194869440a0b901d18040d02c0c1042c1402c01940d00c0c4d5003442c500c00821003040c22500824030542c42c18008071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 91845369 1250 91844119 91844201
    0x14030c091f120803060105030403050717040609170a0212121c0b030d02100b010921060e030a090e1b03010b03011a0705210405041401150c0b0408070f06 67
    0x508100b21a65201c0b441440000d28081c10040080045001c15010700300b82c606040e8884030303141e60301d201c00c800a05e480e04688a0480000c05060780007030f01e8810380942e92608055100540100085502444942410f800c2d003251030f88290b210100d0300e658541d010700220038a40d040c0f0070200f100c3e42d46e10707410341e604086114400c0d040b0321095a05160002070342141c07000c0700c0e14040342c0241c171880143c0d10180598006004c0040c1e104d046001b00300044500c00703189100340020420314014400c102c1d500e01800c09024040f420700388040c030080d9401550300381e02c103100c145840756103148403900048a81003030340149013194010006101d166071041d42c9102e01061000c800e03051440540742c40e0380c0d48030901d800b039464402c002c4404e80380e04003140441b00074002c043c0007400101c00c5900d40710b090003001d1140951074142c40b0020000544183c008004207a041990f0b810030341c44688900d070355540300c000100c0361280480e0328100054180e005a0141d4403000c04040d00c013450501c44400f840181036070f030b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 91846619 1250 91845369 91845389
    0x6080603061b1e0a02060f10050105030a150f0e01060c030507080a200a02040506060301030c06051c060b0315011103030a0209040e030409050115090f14030c091f 71
    0x1009040d8a0000e0841e60101032020001006142d42030003074000c1c801c01000c40a10048005801030540003a0000d045604295089a003180da404200083c100000da50701c034040ca915a104003c151301ca07002440e003198061f080058150b0118103805410038290703000081201e0042010080798203c8042c10f4010710242c00d003182c100c90680e9008045100c0c0880051161102040ca41c0310a4843d61140000396072030075841680c007642403585581c40c01d014000b00d10440c105000a0500e08000c015a4101d9034080c00101d03c1508004042d84c180d0800f1402400c806001200c0440c4a401030081070b0084c030600c80c0d11a40c0b400c0ca000c030400100610704250381408180b10310686441c41c0002120b500c484401001038131004c400c0300007000b802d40032600c2d8142e4400402c0210302c0c00c5a9502c018105c401a83d04c15002c2c000c4514161201141072003074000c0308080410820101001c1800b0100d980c0f0014140c40e41c424001c0001419040241c424010551008113000a81c048519802c4050072031102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 91847869 1250 91846619 91846621
    0x905150112060b031303020c03070603020d0b0409080307030b010c15050f06010302070c0b1c0203100504230703180203030307080a0f020c0718020f0f09010815181807080c0a0608 78
    0x106000510014204681705c00041c076406050510900c02100c8881004055414031b659512008010350010000c0030f10716031034031111080e91f107403e00c94445138030350040341a821070380c0b00c1809800401d4400300b140c0c14401003000007400682400103614605d02514000540303420a0408440c1d0640020902418140304200306000f0850030210001101d4040c288103980316036007070303080100020300700342c15500900110500c810401c10741e0200054400c1a5000c00500c810036444843d00001e001d1a040d00e41c0d040008684aa0310136000004060811203a01c252003c2c180e02203840c642c41210558006182c103000d0149458003400340301200070783e1410039820302d0039108025407a01079920840004000000300c0c0420b603031468040c0c0c0d480e60016009542c84001c07003240400030354800c0001d140001d00000014072404012038841c01c00f0390014140b1100d1404070328803100b0f410030240201243da28403c10090000e041041a80c0140c178119003c0c040680da00c0041c00310441c1550402824404580 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 91849119 1250 91847869 91847879
    0xa0b0a0506010e04110910050d0506040506090a051012060b09010b0c0d050c1603080a02101a04020901030f050106020a0201020717030f0f0c1203010611010504021003020c07090515011206 82
    0x34400b80800f00e08032030020700c01d8029614520140314024081c0d8010100d4802d090f90540c00101074809811080d2003071103950344400c01c12040710000c58555038841446004201001d109074801c0b58041e540340c13003003a80c46480c0c050b01000d1828a140840d4499103030307510040346040400455004101d5401c00318140515806200c0e19020103540c500d0400c00040b8855060340e10401030214200b80e031425440c0d48585905101210360b108a0095001d0310815416900d00341ea244942d41142003030700c0c04901c8501103c2c0401000c1e5004182c4a81015252401d405484046200e081d000303101c01d40080184203845c0c8000f80c1040410b40c048645241c3c2d0502041c559a804000c0b9078170540c644020b41e694a0f0811406241341c000c21507800b0071031082c0d03011640c04900200055042c0c602e151540f04000c008032140b5820385000311002904a507078030f09031084136801307a00a401c0310b01d006025030780902c3d1100d0800d0100d441c2110b180d641440e00102c1c80d0760b256001441e00c0c00c50481c03d80207204440c200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 91850369 1250 91849119 91849127
    0xc0405041106071106030a06170d09180b09100503150402090402091012030f03051f2114100b0603070e0607061103090c0a050103060302011403091e0a0b0a050601 71
    0x10203140a5000026084100405030a80c003c110341300030441c3d500ca080405030b00c0000c0c011805500c0c1d541e580024880a101d0000800351200c5c036455840400d40c41c185000c20032034100984003a4482074464200741103584e240040c03544180b011146d0302100301c2c6804101817800b031400d0070030b84080e140d4030305010140e03c03142e41c0c030707a80240c054891351500d45680080c80340d01103140d031104980707040030b805960415911129860132107950f40d406000c90386540c09440000c40082e008064560000d081c108004040c030800460fa01150103108007001c038181e152007800c0201c400d5041e0440e0046aa10104409075200c0c0200902040d9030990440ca4040c1d405041704084200245c03082e40c01052550820585406c807103a4030644001c125200d041888a06c0d55900440111520034050080d0104081d44248200006c480e0169a2000010400504220f00d58000b610310411030003440314025241c804100d00f220320b28001001011a00da0790305190244031000b43c14562418104002d2184030ba0344 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 91851619 1250 91850369 91850393
    0x10022b0e0405070c020603040804050f0105030112060b03010605030d11010606030e0607081b0a02010b012304060302071109070507110603010b030a020a03060f18140702030f0c0102120406020301080c040504 90
    0x8155000161501d030f0300010307501003500410007940900d002007084100100b0710064011a88103a80c0407182110351001502c0502090143c81c068441c620078140203d0525000b01d0014030b0003400000e0751075119800b09090400141100000ca400c0600b005c0d80d40d4001d10503600107181c145420417107001c0c0c4207117494a034a0041c2c020410803221401044500003450080c800018000001940c3d5401d1070380080e019203d00c0c889580842c00b181c2c00d56400c450b03424002e05844083c809960700e03141c10101c0c254002c1d08006001da890030310078003401ea0503861350b42c600e034003460250702d50390f840e084145000603542c800301003401d00500d0203100402028141b2400e50750803030040c4a001d602c6034600740040700142400d42c0401d400982c0d80e41c00264140344800f0b00a080006084240211060060885400c0a05442520059004001d00400c000d4500c018001c00c150110002d1b1604220310f02c140c0c411b41c0c0903502694040d5001004000031803081205484094042d1410700c818034094841042d00e0039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 91852869 1250 91851619 91851647
    0x1701020903150c0f04150f0c0b0109090320070515040506091302090d0803090f0109020904080901120c03050a0c180317040302041b110718021810022b 66
    0x2050b1008151000b00001c29101c4035000b02e60b466448076034840700700c010140712588400108041c142412403a40c03040300240211070704140c0d204d5080e442d0078580b6000303182880c03050301007050441c5000d008a10111500c00c001e8540ca0007011510700f050304001c0c2114481d00451500c0804202c100041d844501c1511840c11048511703140600d2281c5001010744105aaa2980001d040801000300f011540186018070002411128000740000f5814203c0300c8020000c0d501600700d46c00140011000c0300142240340301803400040c00481c030b0102c0e609540ca1201a0000719488200b00f1074162968480d2403403814080c6001031440700d080b403160058032418040a03003903842041c500400341c16141c00f00e0f40115800307041080115007c0018218a00100c119240054001c3d005082c68030400250002070751010b0740c00320403104104002500170340c4807010010300300300e0401c8000e139559122048014491100d4001e45000c503251064400304141d0718801c403521503405041c0e06a0240d2040007003803209 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 91854119 1250 91852869 91852903
    0x20d03020906040503030a1d01091a070813030b040302060c0307120b03031909090605180c0c10090f02010f05190e0a09060f03060e0109022b15061701020903 69
    0x40107120204070740744982d410458051100194054000e0b602140c00c0c1048440368180700c03000c50f00d1070011103500070140310300f400705d035038602c0c0100f503020308170b4014100c451040e00d11610b090600403210b000d1041a50003544e40b2621a8100010705405010441d402015580700030f24624280402501a005602049580d19644e04003001592401c0088465411a00e1100c00402014101c0100503001034083c43e8503a03402c1000004613400e0041002e0040b885c4a60076040c44c2d600d00d4a1007401d43c201f02403031121031040f25480c0303101d08100d201d4020010f0150100041d40c008130700000d072030300040e00010000c100e01049800010308281961880b03001d01d5250825183e91b800c0e002400124072604140b0b082841d0450004404020001040489202e00018850070501e12000d60803141c2d40d580c081d40100500c00560401d52801042c600e01d00300400e46c01414214036210300e070340e00da004207140c0c100e00d99400043c00000286180b610218007010001e524105000c1c2c04291940d02d40d40c901a208 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 91855369 1250 91854119 91854127
    0xd0f03111c031d070807050a09181e0611121006021c02010204080d030903090602010608030304020f0607060e031b0c030d05030c12090a02042f0307050c030d05040209090d020d0302 79
    0x2c66800c40c03c4205640f80031089803d5036440c0c50005d6180e5503a481b5031740c441e10036410005141241402440c4424640343d0301341001e68000d03150076001c03044c02500300050074505c1e1510f4000400754400d80000503440241d250300c4071201c6000c0507405074081d2107001060b4001408210703441c0d00182103851070943e0300c02000c000c0c0707411600381c0c0640665080604103005004440e20440e40c035a0014581078000da0711581019515081613003210078078004d07032070f051f0410000039000d41400355410b4a080805005a494040355403508800c5a1042c81d8030701458100156101030392800d02140d65100c90050060544041d110001030748d00c40300741d840d00301404000310000340d009084009076803403d004e200407060036241c007151142e00e0b0f0154000880c802d5207003222010050f51001c0c4426040303400080205141c852500c1205a5508010800703000c200781005080101d00040c0083e05502c82e0342c1c8008682420144108000d00100501141581e4800e5030040364103580026003164000d400c0c01d0050303803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 91856619 1250 91855369 91855391
    0x3050903030706050a050709050a0303050910110d0207050a090b0604141206090a06050a020c03090d02040f02130e0106020f0d26040b1801020405010507020f0604050d0f03111c03 78
    0x65020311100507000c18a00300400419845c1c60300040e1191000e1395900c0d03030b1a5150703400c1000c6010b150001800140b401e102150035414107904102c0d600101d82800030b003a1035225161880c0010032003000340141c2049008200f1401e2074200c2e4005403545580520480c126180415502e00640c800c05c04003120f0041074020036151b0140c0300502c0403400007590701038909002101e035520f04407401100c0072454200091074914881c800d813a945d15070302000c1c51814103000c0800100710381d014400d0b40d2040e650f41000c124003600d1310080166030100240e50800c2440c200580c246090141e0040b819500401c85140c11094042005144076945050501410300c1451400c0c0303103002600c51901403d0105401d000a1010084680c2c2c130803001107041302080c06020180f07501340c0c0100c4c030030940071580c148189401032408040c4041c07045005040c10b414540c1c2c84000030a685240c0c00240d0340450818904418140d01c0306000d204034410303000601d0511440200d01c02d007424603480303007010940c1d03030400322074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 91857869 1250 91856619 91856623
    0xa05010c0605151f0206090312060105030405100606031d0d050a08042402180d0b01050409032c12010204060804060e031b0c03070518041209120305030105090a090b0403050903 77
    0x2600341c006004040511813804900f5030072140d030150400035100c0c4800180c1289000801c03900040c0c01c1c03000d00c07071a079103e40707005440c2c54101502c02c503028014428004400900c0b8420035000f00b80030b030780100e4481107a04401011881e2070502c1c1c3c40c55002005011041c0e80c106c003c07100c2058132850804039a644506040d681c403841905400710101c1201891038007014a034000c2d102c000a000d01d107a640700084c40c1008642421341c0402072460104400402691519601141d507441c000e040c205038008a8480032001c4000354415608200e03503c20380780860703003070400462034070400f900c0085103054100302001c1e104941c000e0004054544613000000e4114040c0241c8070b562201c0115820b8400d40064210303214030520309403034064400c0410008940c41c02c24000500d801081c0b001d040303241c50310348a48071440c40e901d0101c3c05003e41490b0000e61810801c4060003254000c0c1d50f010386135410841007203100c0b9809090314543c1410080518003248803001c140b0380080e41410076595888591001ca4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 91859119 1250 91857869 91857901
    0x801030506151305010306050106110f10020a0c0b010803030403020d050c0303060d0f0b0a05180c01080411040902060309101b200c040e010204080705090c070b06010903060c02100b0a05010c0605 85
    0x501c2e03c504000000080000541003035059801a80b1002400c600b4081403daa4204c00d40c0500c185a110848e4090409510303401040402031502c1c198001e4501611010340c450020307032120b6095403000042005160707051001100300191803401c603142000341d40f40c00390b0368000500361611a418a100310b00c1004920950030750071a6007c0c4030400740e0302e004480d0b40000c040884d01c480e2015801c41021a4003480814040c5107035505850f5024580c4494580e10f426a80c01c000c2c00ba0015507070410040542d07144c1c00950701c03030709060008010117000d80e1300001c2074540211005602064005a002215800400b86200da5a0f20001c0c1c0aa400c3c0303101e1050314040010141c941c0242c42c1c13841c011081c0070190018070079aa1007008403003103142d07070710140b004401c4101c03005107035950700344608400038080c4c3d6000d58100d0414036140620701d4680d142c16086400d400c2404025a0009000915045c0c0ea07000b10300e500c2e84111a2003040c3c0d481c200c00079026485240f8014241c556441c00a604100790304090 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 91860369 1250 91859119 91859149
    0xe09151f0e01080327060d051b030405030a0323010512010618060503210910020a150905061320040e01020a051e03010b0a05031302030d180501080103050615 69
    0x481da5944500403900c0b030b8070013022000c03c074400200090842e02c4d00100d0041c2000007800c064605205981020000e0002800b42c0d407486254490380c0398443c1c0e0f00740195000d41d00440140d503484108031006000c40300c1043e0155200100b10003c582400c3c0840e10140c11210150340c0100c1a40015490a00608094202c4120b40d8070b9000c4203084416180e2124040d100e081c1e0846200f80440882d095400342401070f50ba4030824100844020380c10410b51400e08444240100c61220240303513500300d40e00d01501c1d1120412640c0d200c61a003401340c1007102d9504200c1000c0b00d6044d400c0c85842d00080e1050702c040300c1129210f6501c14039500c1e210f581c8170b01c00820106000315103480116000400e40d52014400301d40b00614515410b19404031082164100e81489001c00d10340018114247d5803504010003c0c0c15001c02900c010026031002c3c082c14a00c00d0700c5940f90001f0448411201d000040ba58000d0b6041009131320040c00081d600240054220580440080d0301035a2540040c41a00b460144 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 91861619 1250 91860369 91860389
    0x1e050105073002010f020405060301030326041109130314090d05030f04090b0102030c0a06050402061c05070807170a0504050c0307090e06060607080d050612070303090e09151f 77
    0x380000440e0100921240310ba550080c0b00c08140e0340d4040c42039018a002e890b5201604000410000e8081c0b403166988070301c4484c4e015050000c0c0c3c4140d11001c3c80031501541e2041d498184294140b924910040c0c1c08620342040701c9030b200050302c0081000c0c140b0403c5003403d640c000750109490b9112021108025400421039503140680c01054070250030a2040001841c104010601550f00200c2981e201e0201800141003900681c1c44050180c00d0161099800c410300304141030950350b8607400354190340705101020450341420312004001407401800306040019010300b6400015a901e0450f4103c2e40a2801186035119401c2c41340c1850500d0490f00d90510036041c00080080c016004084919440703810780c0d090703a50329414004c8078403a4410040801004004c0009100b40342e92100f90000c1e00548000c842032240c09a4900d0428a50020f801281240c01c082002440204c20745034071409080180600d20005401118041d40140c020040300b217810081804020140c05030500401016007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 91862869 1250 91861619 91861673
    0xf0602300f0d0605040b18040c0b03090c0a060f05091203040b0c0d020118030f0516061503150b0d0215070218040b060117011203020f1002131e05010507 67
    0x10700545540007110010300641000400540303072425104011400b200a4010340c440c2142e003824aa4110000b001101c0794403d95002103103141c1040040c501c6021214018154110390800300100c0c00c5080d403155040140c20420307a00b20a41c000b081d1440804c05980e500b1101204400d901c0c203500454010f4800340a000c83c8202c0400c3c0001800030759490030f50000c110303109025912982c0e030203c4240c05000b14150000300c040c00d6105000414130100d00d0004443c07100101d0361407000380d40030311090400800300382c84280144840200b00703d004c3e103078802c0104500c0243c200410f44e10742210b14007130300c00e00c4086c0b494440b01c501541100c9501e640142001250f40b1031501d280301c0044c05070390560b402c2000c040052015405149604884d5400c003e42003016880d01d01c180300ea0314844c1c04110114066080580700c0400200440d490445041d8005602d4044500801441c90b8866020000c12500d0b80351014600c0d0029000c4ca044da4420701e0055903803071207030521080514441c07a8006d6441181c030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 91864119 1250 91862869 91862887
    0x15061905160f0c0e010b16051906060816030c091509050c131203080115020312161e0804200303030907030203010f06031e02180106080601090f060230 66
    0xb00e14603072050310034140b041d2800c1d02c9011034220014240a0010088030401c0001c4a0110380f0407118a2244108215006600305030000381d6031408542003160100d440d040180581032003170000c003454071000b002c940400f43c0f95132524120400e0510071035a415130780301082c0800f00c042c00748603c0600340480707044c0040e051000d043c02c000e501404074444655070014002c14900c0b503901c1d40203441505513903107400c0c590030300098402e049410752101c41548010410640150616900b4603c80d006032a400f05003d040c480c0701a140c0c0c090540c208031051203020342500400d820441c000e4126800c05e644011225040c00d85440c146035003504250b00d8440801000056640040d65000342d070703c02d0b0001e0001d010b0340302a0200f42d07480c070701000340a900355190707407000120345203000840e050004180100c05d0340c804010000081c02031308002c000500f00010455956088040d0900410a84445001241c58a80025110100644078903201c810504209030360403250070b20020440c0c1a2682c49984040c25 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 91865369 1250 91864119 91864133
    0xe01060b1c050703090803060405090f120405040501080c010203070803070201020424020c190509040809060310290a0309030207210201170403020c2107030305040e1506190516 77
    0x12200001c0a414080068155440380c0140e18002c0e5100d2000e90860f2209420080500701c01059500b0300e126840c1d40c80c4006074200522843e104a000300c15949a00700350070700c01560816000001c5584c00030141c4003290740d0010849440c41d4202c4401d50303c85c0c40b8035800b280603103d1a030240a02191b00f8240d0241c1c01359980301800c02c40d840c0d4003154921803d110034009915107000c1c21713a4a0b03960941d0204907508005da0903552061103000a41d1622202200082080d04140c40600703280994840c140721030b40d550b070b0142d00e0f1008050224005511a81039680d082c0c8070b40100c40081586940280040500811200c2d01504140c04501d0521140c841d0400f0f840c1d04514060b800a090740b1400300701c0000310784807603021b690150b000e0711a0b841941c0078408a000d00c40c80100c00e07506a8989841100003e100b01c00146209a407411b554900d011400b4190f150b01034050842c44d9403000a40007541d8812045868840ca50213017180d44034220381c0d0581c4d440c040c2080f0344540b024103c008404001c95 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 91866619 1250 91865369 91865407
    0xb060307110d0903031d0103060e040501090308010909050703020f0609031002031609140103020a11010203010e040303050601030b030a030f1404180e0d08070302070609060e1b220e01060b 82
    0x8100b00c44000b60911801ca03604045480013a01091102c4248101030728a0051268903020604001c1003840d070740c0d0310300f140500044030309480c3c695444005004140d0b02c41710050040000c98070900c40204141c5803039840d00110b220080c881e5942c3d408114141d15040d05072007074000000c00350395250a5503610440a0b40c42200d1180024842203075480c40c05000d0001e10098034845510a8813079002c8200550007540168020001d00400300040e03110766500340011070107444543c0d040b0006062910340034041c1e400141105051608011520441e030320b001810010752601481d00e0083d80c4417011080d070303410346c4800900f034414000080105a42030701c03240301220340c0c440388070820004074005200c03511212a05560307400110100b010500305803094015040c90350042c43c00241c0180306903126800c031101c0240c100d9a81d00000040c00c0a41d964894000321150140e4001d0a42841000084041540401076408040c0d44048103080c1000c00d51001d80078000e040206944c580f1075006000524007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 91867869 1250 91866619 91866647
    0x7110102010509150c030c070212030a0e04020f03040204050403180602011b0215010b0309101e051f0e0a0f0c021509010c0905040e011e1a06030615030403030b060307 73
    0x200309004038000d854002002d22000e2221980783c699521784075681d005a5001820400e1204410b002c4540944c0d282c14822403c2281d100040da03603030081440107000040e04040c800e00c150b10502010101c80000320440347e00070b84c129000105551189810385881c01c2101035010001480f032004146650154000e01d8000c80070035107483c500c06982e0301283e607007840300c81c845d446241c4100100240ca040d980516004005202903500c0c8040c14048201201c40368944006c851a00c152085070700d1a251040070b41080c06040f41d1000075030780340d4100b44801142e1048610710020b60000402040e01a403100b03000c03411000381800990711540d0020b40d9090b0f0700c81c62041418103000841d048800505c210300c0e16082546071401d881c1c1c030380b104020080c103002800e0803a80d522984120008040900180d210010204002440241078181c119190354000c80e110b000304420014400d42c3d90712801c0c16208054540c401540d2a40d492808802800034510003d40181e000f20510010315000807481c401c1e40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 91869119 1250 91867869 91867871
    0x30b0c070c0803070c0e0705040b0a0e01030513020a060507060e01060303111e0d1407051606170402030303010522050403030f0f090c06080a0b060c010b010206090303100e070309080711010201 84
    0x60b210040d00d078032481940c04c014002003505a00b003180183c401b0340e40d503000f4850f052050405036602ca80c40000d81c40305080e00e00150501425160301d68262041540001d440746140c10ba40081d41d01050a82c01c0074081c120a010002c42c0300410091a90414900c86820000a100c110b41d80d03d000341072420968100601c0d80680c1010a0b0861441611015000032941c000c0115000c0c610b41610364944400b5125143d050401016000c42d004001d01c8034000e0715408510070441c40c10500800148a4094000d003092000c0180409a80c001066a05540c4211140c0c006007011030861411020360a203941d0000382054104802d00d40c15138801c185003e001070040c4081c00303030311080c28122100c0180c000e0582003584028007202e441200125840030001c0c01c00290f80210741c00107112a00b0800171800169142c0c20b042d07520356814416560087e0940f0020741c118109003240c112070328002d0040501c02c0c006040002c0c0310b148680c000400080e00604080d503a14401e0900340802d161a180690240d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 91870369 1250 91869119 91869143
    0x5030405030c06070807020f210c10031a1009170d141204061509061205010e030a0207060311070209070c05120a050711030a0506100303030501090203040201050a0513030b0c07 77
    0x342c28140129041c1c0341c0c2c030907040c85c0381940036801c1020050188600030b400488850101c0c1e0b029410827040401c0121070300040c2030544a4008010703001c0701c04041c42e0201820f05011240c11140f003886020105000c0360890b1480c1d06000007142c06440340d51146030300c00c06003020340b07801c1080400d0000e42c03040d0a82e5454a214400002c0150030303c0f86040155a80c0c105400080114410b0341c804040c825105489298003661102c2c0c0d102998100c0c2c00402d50000390350000c0e82007260074810744180d1718040b0007440c200100403801944540c0c0b5403107101c06142e280c030000031815140c2d0040b40c109650041120f0f07568204820300900c0591070340c104451912500000802202c2c40300c00b5501b10820599076940317450300e0b50740c444017000c11030241d942c3c051003031401000002e507040c00340301c1c401e9554a0701644071501c1c0d0f003002419030328180e0101d0a401d104100b4880542d03444000c4607040c00c02424015030316604403100b24800185a0310140c840398050044c04a426003c0d8000c00070980105410803103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 91871619 1250 91870369 91870393
    0x12c0c280f030b07050a180801020408060a06030b040b180102040609031e05060612030706050702031c06030b0420090108010c020d05131a0714010c091512020c1002070503040503 78
    0x101c140c580c00007030030141c0002e0015034040c0c410001000c0504003460301503501141e15680040508840e00504500d0350013080034050068100f00351544149803141c1442410300d1a2580d421809014101400c552160b0700007560a41724227a9003040850340800841d40e030b43c0d0b9040b0040c00c0448a01084405003d50440d9841c1104403403c1904180c0d00407016003a03585510080100900b8030704554000f90006105500205409200d418407400190300603565500d60201607000024810380b15100661624406001060011086517405030380421800c100b80b004403541c0d410b51a0460030107a1120080c00042080341c4103402a20080300b01c1d408440106911101c140d07100c0c09222014080710540503410050b0a01200604901120100483e86040d2054031845411440c5074030a49881c0c2d1194602c0aa296100150f000240001400320100c070710803403c010242807000c0b4a6011132900401c100901c05024008180311441043e07085507a1012443c10350748940041c030032584240110203410034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 91872869 1250 91871619 91871639
    0x9050708091b1309080f070311070e13020a0302090415050a0e0604020d0614040c030c050907050a0c1e0605010e09060702030f1615050603010e012c0c28 67
    0x2848a070800040404000d0764414031181c4104948080f0016883c2da0640340404c150300020140c0503080070b01207603181054100070b452503031100b4051080d86c0c4001010086843c2d0100300c10b0300144010b0090039a0722250000179070303006039604041e40c0407000c80140010040800c2200651461803001882160b440703080c0c80e01200c01640162590b0303040344002071300501d4140440711400c2c2c455040011003000c44d1880000c0035501700c80c212150200c4200503c107010505025100030541115515440e00d0b2414000b000c50040d80301d400140311941065000b04400c40c41e07841124440078040000c41202170070000d01402c1c0a101b81c1d0700317144500010441c04400800c00e140310382055001145060207100001003254071041803000122040c000307090009046803c1c04000f04404403011809003082c400305800c44910000d0340c450380c0c0c0340090809401c124005080e01890342509d45003c240c80280b0341c0d50600003a601c880d0342c004800c010740b10030060760031210012002c1c601d0284034801e0715445010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 91874119 1250 91872869 91872883
    0x41d121e03070804200d02150408030412060b09160302070f02060c032206020309011809050106120e0c0901051e060f210103080f0a0c0f05060108010b011b020402031f0905070809 78
    0x154210070341b0707881000541000c2d003003442556816100e42d85810ba80e08030382400c1d904560840700c084400300a401041c86402c0c018014200d00440d444110b40c02c001c202801c0108c112000c082c245900410440244901000590340360f5802901099440c1d50183e0150f8407980080610386002c0e003c128010381c1c4915010510040c2c4003150000c43c0345c001c000c40150b9140b01d404c0c0c40c140900420a0b00030039180c840e03028041c000d0070a0340781c3c2c038240e00c040d84204064030110000c510030f960180c403014001c1c9d51842e02e4907044580c21b40e420741981c1c2c42078140300d8003004081c100d140c0010000820f10845400040100141d0740c5a420004404104041c444400c0ba004c0c8009030000c403051041e111038141c21f80c0140320305031081c00c02c9680a1595980c075022410940f0044c1d407681c010500421055500703002c0c1c5042a0000d20b0b003440301c6121070306c0e42007003000c24480c0640610b502000040401300300b40724900442807142e0308483d01c80c0d40c94651002829080320a80002250480424844200050381d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 91875369 1250 91874119 91874183
    0x220803040621090302100c0e0d020f0f040501030812010806130308100302030d0201050f0603010204031505151c03020c0409050a0201030509120406030506041d121e03070804 76
    0x95450149403041c102c44041640c01c4451600c10740103410001c0302020302c100b02c030040c07190f0064412003464044400440341148801d5003403100340d100c80c1150359940c0048194055044403c1d0400000c031501041507544040207454026240c80008000c1c00345c0e100141900c10200001d0030715036038035410031382d40760101034681010b109614031400b0300203402455460f6000701c038060200c80d40b981d0381d00020719000c07503d940c905c00f50f55a038040c0104001c000341d250398060401d0b0000d5103000c0c5035549800414440f41400c405841e607900c049a18402d186800400340007004000d510861003130040c002c1840c0505078200e02520aa44080840703040c5401422001038114029100003900c0d0303001500540001801d105040c01005148510815110003820140c0385540d40013465141c50010f01003150400c002c14240d9500882d0194803103d000118422070010540c0c00d69111f82600801c4610f07142c003503d0552051201008200035141e015050303030311484c0503030441c9000f040f18030820244100303c0b51391 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 91876619 1250 91875369 91875373
    0xa0b040302031e030f0711040b0405060a061206051f0305060118090506040902031903090f0305030403080a0c0215070605102102031606020f1015060c06180303022208 73
    0x102d1021602c0301d036000002400742c00b0b4901e070580400c000d6030705c0e80c02070030225074101c2030009002a40c18580328603200040103032000c120b07500340440040c09002140c1302c0c1d0800c02007038008040a1503030b2038100380c00500c0080c1a02c1e151100c40555485e112174141d001c50002131801000a6032503101c0c0040141c02060b0184618035642049007640203000024230031038006480311040c01c0140c4003000b0118100b4040740c1c01100107101450000d00920311540302e4211145021021300200384048112011a54441043c0380d0f00e4009c10b80503100ea024450010754403a00c00700a03500b42c144498014645548035801c204000c2d542c3e00500b89181c08680100209400854117940d04020480031741c064441c002000c640c1e901d5252201d10700081465005500103070000402c000d011102000089035916081c0e40a1003859402d400300c040340b10305485000d0400c041d024070081485101c1e849018407506400604c0c002c0040b5040c041d0203944042010000c0c1d10300801d8503680e0580715803090003500e0780840 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 91877869 1250 91876619 91876633
    0x312010603020c1501030c080c0a030503030c070c0305030f0d06060503090a020111070504050c0909070f020c0d14060f06010e06090a050409110a14100e09071121030103020a0b04030203 81
    0x1011402500301a004a44520034400c41013003820003121a140254403c5040d000035038180f828041c00c001000700040d0160100107003e10003d000402981e90103140140c9958940869040c50040302c2c505500240140c0400105000c600c242c1000516006038000014040d580d07884c84c0440f010311045824035502c2c0c0002107100010340c45140c41c802e2000200c5c003282c0394192940001400c40d01d00351070030321524000159001d41800e01c851050b034400e01074107107502d62002c40c04d8065241d404998815100741e090b032008400700420340801b9540c02c030401c022602076181c4040a00e420000644009021401480f00c80106240407001c40d00c6419000c0c2645030194505030500c0003038001d65100b11044038038000700c40f109031900d1041070002d103812858403a49450300e400313004401c0d86a103080030402200007031070341c072035202c43d00d00c190000414034050380b8840319994240d0600350030b45000039006c040684916020b1540001860585e03000722406414142c0c1c50400301104d11a40c44000c0d0180c203d21 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 91879119 1250 91877869 91877879
    0x10e0603030306011116060c1509020a030807080f160c0e10030303020904021b0d09050901030f240e0d14121b07060507120509010e100b040212130212031201 69
    0x220005c8500c4400500311820400c081c8454928168203404c50701c0090504403145090104264142c6080d0b86004410010f4405d641c0210b0303d4114140006442e074070b0009416802c004400d000c071840304000d911000c2e101c1a031507110014005d07040d0020307111450348a41c04510019003801c10f0380100382c410910440c15145580c1030f40690440c01c10594440c1d4240401245040042e40340f0070340e4504034015101c40e0704400c02c058800d42a64200e82c2c0035060030310050002030303564980006850340041240009514801380140c2100e443d0385e43c40d40090503c862100501e100081148031118151140c02190781c001d101d41c03038103004510010194441400202d40e4030200703000c00342050084030f55201c2c580f0301e00741c0b50308041d50f40a0b910b94000031102d82464212200601ca280d411103070410003071045400142035a41c0c0c0b410110711030f01da080d6a41846480c02e50769503044405400240c940e450140c503221000c01240d6069850070f030301075403e142d5083c884c00004000c9480018007000b17a084681d00301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 91880369 1250 91879119 91879127
    0x3030e0429100212120403020f0f0c1318050309130b03030a180b0c03030a0c2d0302070209040b040201020114040b0f0705071b06120e07090b06040f0603090308010e060303030601 78
    0x140300c0642c158000c03004403c6444080000811440d211222041010b0400e4035009141503040404162550803180c2500346c9104003107007440400c0300458010721070307000c0d0f80e4028004000815a00999080c1210580100407002c00503001c0003104a03400e104140c400140e0713206448441150950503003003041890b4201c0e00800d4808003d0700c41850181d01c1d551038949400b901d6000d05407444940d4408070821044203954001c03420580c10b01d01c2c08041548100c60015081c0b40c0c50285501036080e40100400250b1190341500e0f85550013f180382c5150809052501c0b82d5201950140d005508190400b94189a01030380d850103a139001e135a0461300d540e442c1e10998504009011501000f01c100030a1000c15151640749101040520b80841d0052400038040c202c2c0e441224a98225414485003424200006c1410821610302c0700f4046110014140014500d10540e00800030480007184c000c1201c80d07040e804151001e101e601c80c0503040c0d880d10041c1e0003114049030240d501d60300030030000e00e0301e51203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 91881619 1250 91880369 91880389
    0x6060f060f030a021912111606050603010f09030302040f0e040206070321090b150a1d0606040306020a0207170c0904080702030c0312070201091505030c0a110703030e0429 75
    0xc42040181041001c171a030642e060700104a1000041c03001c042226042054801d0803400c01d0524149450180046107103248059044030142c00c06903070f2000500e07561001e41100103200954082000a8013403031030050002e42080c0203414a6039284800801c0c0500041460b90007185c00400f00c40c104880341d0f80c1151f102440007159000d80307144000315900e140d0b1501418032032a1054812856501e0710319086c0442c40000368000e440b6090070174040001802003a640205094440c150381d005688040c0400c00302d2085501c000d00d000c0c4002003409000341d010410030255000c0322003204490084114159031510b0600302e41341d0140420020400003640c240041620314405002c3e02e20700182d080c002801d100c3c070f11800c854541c0d80054108211769001c1c18032400307401d0244008003103003010a4014610300008100c1500c1403800070744007071581d00800c14500481e0005080b1041d00c0d8a03890000d110212080000340a00d04000c0080380c3c0d00c140a00fa09840c81c113030605596070b610303040104620500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 91882869 1250 91881619 91881631
    0x160e0303043f06050402040c1d12030903070609050901140319030e100302030603010b2409010212040f050f060304030f120209030a060b09070815060a0908010510030506060f060f03 79
    0xc986214080b8a016007664500c0c6015800c0010189044e0060105503403c080b170748403c00000706100d01c216800340311007038890b60003961170503150410710b40901c1c51481013640c89981072050000c0052400e9010480100fa260280d6584071543d030b07104286801000300d40401685a008040c0040c90404800714100c1450b000c2e14180d41600d003500040744003c03008190f4503000030303000001c02c80282800d0003141543c50064400c2c010950007072841c40e0041805e0b00c0ea1060440000030ac3c0904c0e40e2081282000d42d0300c40d6810a5074071070740c0c2c0c4a031011907040703441541e028000c1100c0d800d041c1d280c03507030659108a070903458595081100c414100c2ea0701c2116442d00000c80d03030130701c007201550b142040015545481000c000580000481c20010b9541006261030108641e00080250340701c0d0010154100450903140035495195181e42580c500b115900b20300308640c40c020810004021212000d800c90b40514142c94003074031941c090000a803010040c9031741225040000202e0007041000440c1c3c408 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 91884119 1250 91882869 91882949
    0x807020307150216050a020411040503060a050c0f03010806010303020d111b01051303050618071a0906040509070c03120204080d0e15070c090501060806130902040b09160e030304 78
    0x307880b07007880030604c080c2d41d05844d076500180e07840003141458032804040460031a0340505040c0b811001a03a1100c00918121049840700013049401c40b6407002d0301c1c40d8140e01d41c4904d841e9a1501380040d0350340e100b407000703034010302c10341240801403030182c011a40035400c1740d00546034280041010642113080041e01c03d0400c4401c20513024200b40d82401c103006103128a0241056082000007801c44c5840f10309500e0954101d90310030005410ba038064484c074103801c840c0440e00d65070320000050041c0501d502858000000200b0444010351010400124511070744071030001c40c498045101c102c0c010f42c0100d400da070f400003585111040c054204140c0250000b40120001d180c510b4050300150002402100d6400340198180412011801600e014240c0c40c034100318203207013081c001000c426441c9800450030755550524025922036401c40c54540c0b00c05072060726107040a0200e3b540ea2007094184030002840e003403d1080600e4040300710350440d50380042d00b00c0c1d074101004007003000300d40384400e01c4804 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 91885369 1250 91884119 91884127
    0x3010510090e1515040f0e190c120f06060905060f041502010c091d150d0c0e10090501030203070608100906060302040f08030717130504090b04020f0108070203071502 73
    0x5150b5018007607104404001c2205954090041401020760300320750404003494081c8420710245c2202c031081411640d2402542029841c6c0030980c5100000d0300c01c880200700c0c1000089030704141c1204042c1542c0004074030070001c181e08640840100c9034203001d034500044e1030030b500700305a00c4c007000604441600078098601d070030b07134a0f003480c01812202c50303034603002d40d46030f41005180701c1d0080d0074140100300a04802e4400c198004108808031402003032604c42415070b108184031512402401d580a5501411000760507482c0c620825940c0c6e8210b5081d19a0705c005a000708401c0d0303030341c06414100c0e50b018000708a8a414240c05803031a001c0104a4440a14070007400118124280103000c000c0540d41c9005940798140b0000002c500c6c00d64001920b5540108400d80c00039441c0312440103240c0d94100c1298641d000e48900e501080b65540c07025902509142e091810b20482031000c0380614401c0302e50743c0700003d10100640b40d509048030300c1c8000d42c00c02d02584c1c0210b07000c90020205509019001464 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 91886619 1250 91885369 91885379
    0x50a02150c011a0a0503071514092d0303070f2003070b030105090a02030115030e030c0706110c011b0303090f0213020706060803090a060c051204031412030c0301051009 74
    0x2140c42c250b00140071403c001046100d40c0c28130004c0341000e40411b8002c0c10809040c1041055190404403031041009400d1030701c060312078005400e80c0c0d8840d5009200f2503800f60510452000b00c0302c4110700d6850072400c2c1035a0701080ca000403c8492850344030201e503000c1c180c545c03660700281840f2042c1020003a031811155219a03424070050300502042110243c03a54100010300061000c010b205d060290320420041c00400c02c60101c0003046000303880c010604140501802e81117000d0403861a08034072070800046002a0450f00a106141c18442214402c10b02c1500441c0e2240201c1400d00e0201f80d81d07040d1801007882904584040e6010b400c0c1d9021048841c0d021039445100d65400c1c1040e294007003290340400c00300780502001010b24000660a010000000a0300c815441c4510014400050307810000c0140620034643c45001d02c0317560b1515960b40c0d051080702000d00340901030860090700f10407945400c47c01c06a900402d1008002c40c216804e1409116500b000140f1729018403034401c00c0045c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 91887869 1250 91886619 91886621
    0x90503040e040605060103020405011e030e06090a060b03060103021014070203060114030d080103030203031f08010e01141006080a0b01050c101506020601030209070f0c080703020303150904050a02150c01 89
    0x100404607901c10070031a15060900e41c044442c040d000f1810940100420002682c4c08183c40901e41181e100000d552030304d0720340a40c01051045040420750051004101a10300046068901d5038000e030400e01038120401d007050f448001c00d00000b5401048401d07058102441106200d62141d110590369203891200e40000789004400d038000301a0000b07a1015043d03a040034000e180703002d481c0b42810401c03941580c0e03010f91603001c014404442c511208480910000940042c2c01c001d10a070300c0200026502ca4030258081c02960a4210a4290a5020400c0b07201d403a818401210619030701c590594464890356000ba01c140b1603000d040010922000780e0808041c401c81000440c08a400190440c0c0075040348900c983c00d0b4062402d54018200400141e03e401542c642c0c01213852404a0036a0100e100a9402d51000c403409031105402145160030541c00000840c005d44001c941c604099140f04100050325404580080003604600d40310001401d0100e09200800d190185450600c404280e10034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 91889119 1250 91887869 91887877
    0x190b011413060e1005100801051e1e03060c0a09060e0a05061b010b03030a050708031b04090507021603021011010f140411060a091505040302090403021f020c0c090604090503 76
    0x240f10044103002e12190210000080000b418240ca400c00d041d001028064100d040500c5402e00400d0001d03402e910815400c000c031805410010140200320001d01c480c402d440c40c1e040403041c080d04c1010041441240c2c20000c0d294040c036075a80b54040c4a041c00c0b412910000035140c1c058122464a0f800f14141e0359400181000d1242c81c0c16105551009089a07400d41d650314050b18044e4004110342001103078004201c51440b40c02500c1182c1e0303500c0d03d10ba1560700c100da4800741a80900b01050102d040341b040d4104901130149907003202c1070043d44090442542c422803100a503c00c0000c20103040407070240e050703840300c880408000502008a01c080e04141c030300350582800c44441d0441040304201c0801c40484d5854402c0e96064184001002c014148101900070302d23100440c0c80703d03102015840362003103502840c3c1c050616001e6003030034600607649a441c01c100f840082032522068414400328400c2c1e55a48200400500c0706988401c20f1100c3c001018100035003081e140c2d00d000700421341c200003c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 91890369 1250 91889119 91889129
    0x528110a0e0a21030c0213091a0114010c2603150108150d0f05010b04020f03040506090a0201050f0f16050604020a0b030105030c040c030b0414010503190b01141306 72
    0x3071007511600004000610403680c018800c4000c20003102c00c00c0c085404414484030360301d400c2c07501940d826400001e1085c0580124200c419017420050710802403205040c0740301e04c041c008004850390700c034a03030a500c80c50401c00e010300154182c040c00001c180c0c1e000e80d030303101c0304107129a03102c01c10200391400401e9401201c20f0030443c4443c0140321032035640f02c1b880303a5010248031500c002d016040740004504400018003d01461000c25112003802404c0d4130807800c41f00014000c43d61241d46100d0308034503800c11202500d860080d04000f407801c0c85c0218816140c55816550180b622819010201c10b68102c440d003400542c400340f241d14100c1000c02000460540a803000b40b40628003032042240d13040d04c54010240602d820b02c010000d03520001000d0381c255030100c41c040396801500b10308900408003000c02c075a1042c2084481c989210f20b05d17459034140c1e1801e900392448000907191403149000c2d16080240000080c0004020040881d020340a00b401c008042c4030911080700000c074244d03070b00ca8102c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 91891619 1250 91890369 91890377
    0xf070c05060708180c0a030809031203040609021003022b061701240b1204030302090402120105040c0f0804021009050d06020406120e030304020118090606120b040528110a 75
    0x50020b4100911340540040e6074200c020b08450000c000803400c10394582c4401030000f04082540d10090386d090282e103000c0c2119070411a2245000e06000001d04007014040e40110710124015141d68800e00031200c0c100d45404600008a0003454136041200c11701102a0070b003079882c2808140003e140c9400d040d80720410001007904a4104c04041a004000700c15601804003000d040000005c110207986401c4c00100043d1301d42c2d5600c0c00d064003e40f040c0d012603940705100051215400c08a81d2001d41600e005490811011013a968182d441f00070207100c1c2c0003c181902d000a0041c07400b0705000007001700502c2c01a91442d6140046424541a0f500c02c40b811500410140003142d4003c4084000e6803a0b20b1040c04402c5000ea0b4407912844050006810044a150703080390907071000c5004001000210030070421a992040c0080107003000504038100c0714140342c0c0c030444500c4c050040f54042c5c5005c15071421552001580b001522036050041c0b42e81710384800c503000c2c0d80454400600f006200d2911 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 91892869 1250 91891619 91891621
    0x41410021b0c030a02091306020f04061205070216140307051005030403081f03151b0201090b0112020303191803060c0f0c0c1a0d050109060f0f030503030f070c05060708 74
    0x8103160428407400c0c4054000c1d0320608004c0e0140e55418695a00890210078060125080c2c2c00d004001e8896500d000c0302c40800000c0c002000c40d8003007144850b080080c00100116116410120b1b00c5a203800359940c600341e6030800500503507080710300005080304010103c0d0841503440d4041410700342595806004a100442080107160704441640d0b40701c4202895200300b07036108910221280420f000280242c07240e804d400880d00e4095100d1904006101e8003040080480c50740207028101070001142c00c032002900012300b00c1701c01400c001c019a0300401450070711001580d44050071040042150800c98524031080300e41400d42d1284e000780d8003d44c0c0105191448032005407815400070044801c1103070100030703031300880c2d004811501500d2000403601582c070070005034860580038020318000214035102c00001c00340110360080040300d01c40c40000e000180e0300d5420484810b000c2c40060904d803c01c00000f000700d21568003266100c41c06007804005082c180c0c0750356240c4502290010b010805d080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 91894119 1250 91892869 91892917
    0x30a02101107060305042001170f1e010812070201020a06020d020d0c020d02100e0307050f0705030c060a0203030f07030e03070c0303081501091401140f0307180e04141002 75
    0x40020400f81909080603c49810550b8590390309500c0426803d80c4101650720038400c5a100340110700e0400f180c1d00244c400e40c240000c5d01c8130740d4601650612800d10b064010400308800581050741218208800742000e01124100b010300d540c4240002c0b411070041c00b42c1500010501d1003c0d00710600d00000058803010702065881c2262101300c0c0b42000d5502c60b100aa448541c00250715610066111001c11240c01c00054145503000e0440010590b000304043c00844c100000340700b0302200c030218122120030b0103000c20f10100703204401000006030020000141015008003207143c1240c1103140020300a805040c442d405c5401241007150407003029013041090583c81801c068100c101e45c0d034184200366248001130502d2456200760306200c2c15583c600703c1d183e0f02440c404220000719000c6c00765500900c06d00400740386c0c02110f070040860780342e044074001c01100c40c02c80030a0360014541d000742a1103a86407110003105000c1c13120300302d1107110342079160841c00e400a0000392422416652b804420030f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 91895369 1250 91894119 91894123
    0xf030a180327030809041a1e03070605130e090a020402040306150605090a29040e0915010b040501050d0e010c091701110a0c0f020405010315051605090f030a021011 72
    0x500ea142c002c0b440d0368801e0000c01d0080080710350007002180e00003113244500341c190105003041320050781d1011007000700449440d60f0100c801c08a80f021070513520750769110a1300b610140981080030808484030344060105407050140241c00501c031320103c4400000359800241a03a21581013241d946403150038083c440c2d800e0b0100b84024051909109080c1114400400c00c0c5007004c0c42003500d08200600d2070207624040c01d420b511a40305400f0000c0d519902c0360741154507800d003621b50041c070b8880d0f4085c2101007201220158141c803569440c06190614100044071150450410481c8640ea691820004150240300320000100305445090010740b42c00085649814032841000d00c40c0d052012440340000e1030400c4802001080c289004031911a080544101302c3d4404020f400030300d441c00100610440910010400035010410300540d910252100900c240341a040c102007003091008000c3c901c0c1a0340e0700d840800025044403002d40098000070008620800050701141a20304100182002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 91896619 1250 91895369 91895417
    0x1703100815010510030908070c0324020a0509010c05100c03060f0504092a03061a1e030c090915010e040c0b27060c0a05010e07090c050f030a1803 64
    0x2051125441d5850140403500030078080034820201650f60012504200710002551152a001545440f6060722440c0901141c4002205a003c54000d0104148001214022100380502c540c1c1d60764100040d030340c01910144280d078070451f00307805612950b44142c41c49105a00140d5580c8c0e8012501d1071402e5600391a0340a07603003090b401107003031003107030320100752110302c40340d125149102814000b680c01030550610403032640000308810300700503140b030300c02e000c100208405800440c0c04200240000040c141078034016064107415402c80650f0192a142405005074004203c805640000801410706508010240c008251811620042c0418480c0601100018020300c1000c2031514040008040d0b4420541094403400b0440b10780300b00003134031079200790344460282070211610b2014618080703010702100c1090b80c01501c2900c0c000110025031303000308400c820441d01c400d45440310320044860b80c2d50006008070300c40e540312060900845107101c7c0c40c0010600130381d00d64060f00d40c0c3ca1502c6240c0e0f40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 91897869 1250 91896619 91896643
    0x30a0b1803040f1401110d09060201050705040e0f0c1c060f05010203040f090b0f040906230105060729010303021c0806011b06090c09020d05090102160f17031008 71
    0xc000c0c4400e0202103a032035020f01c19115080e071500e030101c0403c40100e906e004154400e4410b8025803035081c0c0031350b0b0070403000400c0c5e541a4000380820b41c0c07401002c40d0f080c007a038401c030500d4900f120b01192300026850541a04100318024991902d03078040c043e20321110320020358102156541c101080180c1080031210040c00c3c091010314500345ca0b200741c01444490070f024451110b5a03171364108405517a8612914015600940241f081071100e0504100901400c2c649112000d54401d403d41d29041510780581642c0d4010210341c00d14981c0c0e180c9421110307940c04800c8a416005480c00303c0c94906030041402503100b58002c0c541099095040b0040c10010100107080c0014981801056a000b02c54020101d091031501d500d44043c5d410a440a4134a1503000303010441902c070007141c80c0e22203400070030203101500d0003845a515414221802c0f4402c40490102c038824181700c0100003402000a180501d000c0d2000c0302c100220040980480e41c021742d5126a4130420079800c202c81141409600700c542 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 91899119 1250 91897869 91897873
    0x30c090a05040e07051507050a08030a0b010c0503190e18010501140301080c060705100e010f06080a08030a02030c0706050114010e01020a2a0801060308070605091b0618030a0b18 78
    0x3802c0d401507581d03601341c240a6035101d21040d0641910404460054803e056000340c11200390340c1803130411202036403040d525410200d04104400c00103500030440443c074954802c0c011446c144c4c0c00d048020f4030040d0034016404100c440e42c80008503941e4600a841e0b10502c0c2c01c01d0700311a51501001511414604400c00448541840100410240804c2c00310030003d0581d0714035a00c605510305603007084070b09040c05c60001d241038131544110805500c00716a0500e8444101300803034031440300c66900c01075030310001c0c0860001c000141d5410055005560820014401d040c1081c140d40c3c0d9030000d4403804d800c210385016117a040d420896a20107070142144401b03002400c0941c00b036848844001020170a0142082d5061404d03540328200a46c907400241503c00c002c0021170746078680700c2019402060706941203818100862940301c404222401013903100d561a2010b6983c21051100b150441401d000f85060301340700c0841c02d5213051002040e514400c1d5030f022418588118014540d040d8032540c40d482d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 91900369 1250 91899119 91899131
    0x60501090e0108120f09030a0614070203070b0c0a030e0f0c1509060304060905101104030b1f060c0309030204060b0c010509030f090d06090804030b0106020c060715050615030c090a0504 81
    0x183c000400d00a540412640710143c1e18004204206994442c1c800856054841d40b01140300340802070713000c1c0e17000c20560100b0500700e403202070040360340b8000c200d0003800703071072000d030200d0a400c0d0300000030004200c0a003408580700c2d503544180d90800303200000c03651207070f081a5844e25051501c881c5004e1030140980600d8181400d400218896010041004201d95507036031655090040c1008844070720000054103000801c084a0408955001444221402680e900108003036220890081000407040342c10907158520701082154207040440c800d8003842000040840561954005e003405000c80c0c100c2c00c0d07036480d000c4084500b158030080400c00c60350030070311415150300544000c5907021182100c913410000480e04180000300340540000f00b11540009000003000807081d5524103c8569400781e42c07144810000348400b601c0380d50401413400d0606c0c480a0f504014a51219420000140030100c80c1f00c42c2d031075028855030080e200031240c04c0003c28070302c0301c52401400c1c1c2000303040246d50510034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 91901619 1250 91900369 91900379
    0x4031206050d030f050a09050909100e030c0a12030f020a08150108190b040608010e0604020306010807050904020d060e010c020c040c0e0d080307050c031c140601020d05130b0d060501090e01 83
    0x40c04c00090502020050001200c030581441120b000001d00001000000541802100c0030f035510050314803030707040c2400d085007140c1034000401038a64840e5000090300c040169a51303412154401004070300d0900d035444000c0e00701c4401900c0a000319000380e480381e01540c104100001401140341804504109420040220903500014406054070001d04041901050140081c0c00742403242c003d81615881e00c94007a80c031707980006107140100e000b6401c0d02c120745d0725a82d0300d540355080d07400fa0700c5d00441c2c2c00e404940182801d004480c880c40c0510000034a413107128804500303403030f102d21a010050f400003415084030b1809100e03152616000d8144402c00c5241800842c82c0000c1408014244480202c0021041c2d03000304100c629078038144060f29a2041d80c00000e0300030341014903908200504d00711558000005003d030f03403802800141c0040564030502241151240d01c1122029010060b20340300241d2515510084c051100002d240410000e04040005101d207c00350300000c010b50b002401004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 91902869 1250 91901619 91901627
    0x3091509050402030a06031b061106040c0501050d0f140402040516080c0903031903020c06010603090b040b060f0a0314010b01050901050f0906090a080105160509010509120705030604031206050d03 86
    0x49030310603200913849aa418100d400281b10aa0000c0c00b102da0f0f0000d0169040b0040040c1c0c001d9400342e032550003a00f02c8031032802d0364030a0103c60040c20709450820504c8150f0090307019014108a210300070031514621803580c4140d548100c1d0260030301c8611001e000c1149418000d01d40d0000070418403444604040200030144c420242540342c002100282058139620300340120380c03c9041c0c42071602c0c0b15402d0254010300070741c400b0012085d20f004440012403118420b018502c03049030016003901e00c40e1101d44800403207008c05000c03035034081000704c6a0700854441c001500010743c011405028104d0200301c4241c02e50755140885410003074104400190f81c0c1c0c00c04140d85248603044030742500c6100340400328003244200d46829502200010000412081c1504514803c20001d0940070481d4001c240658440c007908540c6404580306100d2002981080c407841c4484005417001c4400203652107002c241010300940d0700303070b0016888034050800d4540c24000d88004003420b40304a03091402d9074800030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 91904119 1250 91902869 91902887
    0x60c110a0e0405060a0c0f120207050d0f0212030c09190e01140102160509010e0c0d0504060f0f060605160510090308010602060f09070b030603030d0606050919080309121c03050103030915 82
    0x7030910100b81100307861543c0d160306448082d584072f022110040d800110291011501c0c0200c480184504a4822081d02500065074002c00d202c10b040c5c2c2c1003117000e2041002e20440c84807a1562215064000181c1403840c4454034002c02c07440c400c0314120004040021700381103048442c522030f442400301c104540d0301c1f04410281124074980031004541c54404c03103810507102c1c1000140c9120300b01b405000c28032000e548824500c03841180300f04120f0b0b400c0071001003669010b205580203e1406d22050003480d1a400708c140c407891041060364207110302d6002d00b03411a0b01c1190250300084541005008030f5070108005500001c2d006400d40392460512022035541d00306d801142d94a00020000c540c2d10384040040e0762040d0f00400c024050240c9905000b0103a410180b0303414850700c0c04443c9a80b64605003a080404c1d6400702c8050f51a1056030130038032443c5c014078111421180f0400001c50b04400b54880318100c1c0e0442523070082910b51440c01c0091441c003035a0003860700115405c1403a899190003100798 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 91905369 1250 91904119 91904147
    0x705060a18030b04050c0a0e09060c130308031311030303090604020409031e0305100b0705071202180a0e01050f0603060708040809030d0e1201020a09060c110a0e0405060a0c 76
    0x444880c0c00e90685110304a06281d200030302c28890300c4103000421001180002d41c106c1c007038401460680c0d54040381c03210f456080c2ea8003900c6070030050100d1000d03210301004040101503060307002c43c51030381ca59070302c540c941c0100c69801c1030101800d0742c0000c1010000408030511803c81c029410340c101840000d032100c0c00500001c0c03040f642c5407061000c0600440300080388202c512105040c004031100054080d040460700112113194640002c51f11a10300c03000e84500a0b00040100b0003503051440c41402003082d02030990380300c0c00c0c1c001c2c1e070b110f0200c295400a1040340da0032404100300c0c244041190030f440c806412081991001d504029050b200014a5544200c180c07078504916101c3d41411005031140d9920140c060040100390052140c0050312040c1000003074a507082c02900182e07a580c01c0380986c40981000500c006010081148a5046418501d00408142000c000300c04c0006201e88140c0d0f01040d0712a606404101c2030110911207254070000c034071020300c034200800380e00401c11942e807520 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 91906475 1106 91905369 91905377
    0x70e0a15120f0f020406021c0c0f0b0406060b03092104030c0b0d0b030106031103011401080606012604060504050d05070b22051204090b030705060a 65
    0x414035414295903900c56041c4200c1d10604041c258560082100c40e4484000750888403c41c4020401030025800514888540002407041024512100b90038410243c180001050f0a0b41d41402c6e42a0f100211894030b0f0f1b036a181050040c109500000b90444e4080200b018010b000140d02500200b0400c0c0750202c451a25003202c868483c030f000050074105105400c00c160303041d0201420b90f5201052004c02c05400c0300c4082821204241d101b51a80300030b01d0810300d01d038103007803040100d11070b28031171491000d60514030700d00c0c0d5820001d40014100309403460380141000702c503420150380f072400b034004030780ba030800d030811002130701c0140e606a03464002d2079204540e45010750111042243d10040c80041a0b030f80002d500e10070243c9501109600c19032203034050010300d0500080c0d1141040422103500c2d5070501585200f15070a02c1c0f1503c0c000d0780049002d00c52a59441c095448044031450 = true := by decide +kernel

theorem cover : BRFrame.Cov 91726619 91906475 := by
  have h0 := BRFrame.cov_init 91726619
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91726619 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 91726619 ≤ n) (h2 : n < 91906475) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
