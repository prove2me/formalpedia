-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0206
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:27:24.889739+00:00
-- url     : https://prove2.me/submissions/4f964e41-edb0-430d-b102-0b0c39963bc8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 36870508 ≤ n < 37050364 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 36871758 1250 36870508 36870517
    0x1080f1003030f0525050c01141c020403120c0201090b1809092103160807020c010f02030408011514060a0c0b15180f150109030b0a090f080a0207050303 67
    0x21011041110140000b0340100605061040c0e141030550038036460b10345002c1105000742c482c1ca19440071000c528108001006a0b500c0b20809007424685a62100c40001003401a002c1c1822440d41c040c3c40300c1d002c4002681103a000e1a00201e080305101401c98000d00514101300c4101e0000d4010700c0005604d10001013581c0060251584010051404204200c44807201800068480c000c082c0e2046000105c2358143d03c51681c0780c5162516894014070381c5030701c031048940c0003041c00524000c0103040307580032408075141c0750b090070507900149403a101203140d8001da07082500e4662034020a14405034041e0000c00485182804800d075400781c2005000160081050801c04500d03103044680c0019825800300e640303e049004001c015848450006154251a001003002030545600b44000354005580150b840b40b140364006c030030304880e00c0000b0030707a04031440094240c1561201045e5005019045903c0c420703000a0500b09a811904001c022079000f840c0c200c016111715180090141804415275 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 36873008 1250 36871758 36871771
    0x1a060a050d020108060f090420090601080408070507211403070203030702091503061302010314010b0a0f0201060b04030302010212070801140f010e030a03080618010b0a1103040909050105040201080f 87
    0x3071001e00e000e82e0041d182c41002614a580c0000175808080c400e03140c45011340e100724020500c1030188400301460385124581040d003030f4003c1411303074100a590f0740c000380088d070031581c007401c0319541c2c0c8281d0600c0781c100203683d04540c1c800520140420300703046090001441c900c0c081c20740103030f004500300000d50b500c1c8104c48000f9016001030001d0005460200f401d2075015582c0465424103c555000113814120f0840700c402080302003a241c00250359051040348100516036408089075414120b10713043da40901813011003003112190b00300c03103501e10070b40282c0700410309100c10503140da4403490040d010b50046480c8912140609000540552040e4030203070486010028803031302d501c100c6052240f04402d54126a051203e029408000c0742c500708004104a80a550b560100b03081c030b40100410f60341c19240700c4042d54141d00052000d0704980d01142c202003414203050001c83d00c000c0c0c6180c11341c0580d60104019514203156070b010b03c0410b400c800c3c4034610036600c4805580d125000080c1d0948281c40300d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 36874258 1250 36873008 36873019
    0xc0a1e2312030123120105010801050411060a0c020405061309050609250612090203151008010605011202070501060302030a05060f01050603071d0303040b13030b01080109051009020a121a060a05 85
    0x8882c4005080c403076071303e0760b0701529080300d04104000d4030b42521000c1e401000160340d01c0d400c00c4144003081040c071a0031481180d0091404001c00c000821a03040703d00068800d543c4c030f0000c10000c2d03850703001d0071051420514060085907001e00f0b140d0381744e070401c4518000700c0c084d0740005216010780000722102a4041d01c0881c05041c20004100d800181e003031030300220070f50b41d9940007015030760822810141c0c1d40d04100f0392882c2c0c641441505000c0c0301640c01100c0681c1842c8040c400360ba040280594142c40000005072a07000b06d0824034050240e90307201a4050180000200500c500400d00a10030001c00000121a90740c40c41841124401180c00100040c800e08a481004144001074030140c0c0008003201d0400c0d403210240712240e4803480d00e075544031031812010010842c042005d1401041140c00030400c3c2038054817400d0700d4402a040801c03070705994042c50803c540e10072030300f0700142c04400c440318a104000c5c54000c22900d400c41880141051441c0022000c0c42c002c18124203464001d0704 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 36875508 1250 36874258 36874289
    0x1909092406080601020a2112110409021606050c03340302071502030c07061503030503040b0721050f0609101401050708070804050a0b0c0a1e23120301 66
    0x18200c48208002e0f203000e04500490100c80d001c00c40040140ca11100100b113281480c3e10305034400782807503600110900c0d0480c10326402500b00f050101c1540e04079541e441001d079540c0e081c100b004110300e00c00c08006000600e41001d110405040001641c071491401226185034940c211100c0c40340c0400d0715035102030368a803210a5441611a401800740302d4420060380b0200c034240c150800a9802c211481c155540c0f0105104090220343c0c002e400902e038400c00010030460540c0c4000307019200081001c0d040c1c03900312011849040c82400c00540d4040c861581b03030010062814400064035003074540707802d0401e10f0300c00700c1d140345001c0c03a445003d180c0b00308481d80410300c0c0510b0b030007032485050455814050140507000c0494000801031020b50722038800c0559032030620081040c0485960000e150003502448000e00c504030000380c61810381c2d003201c4000ca10065051001555a448a00041c420344900039035034552124803000c041c2d4240300c0c60a45840044000802d0540d0000348900280c6901c000c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 36876758 1250 36875508 36875519
    0x2030304050d030e09041407060305090601030204020c0304080d09030606091b1206050607060c03061e060e0f0402070b010e010504020903031b03090d150b0a0303020c04050c19090924 80
    0x21801c08083d00c2810700c0d211000400e0300184840204580c00d88000580e181041d2040344c06006076805010720781030130031107030500e03142c810b54071081400003c3c042e5a00040c1c180e4051b801300f0036078000b070144004548000c0701404004144e040f1511080320050f01384000460022007500891000d0010000e41c91900c41044000322002940b9204001400b0340e500b03008180f03034951600130b14050340a0200440c01804062000381103030902d600c0310248462100d2440c3d1214034865100003218a0f610b0528100c41400c400608403840c01c0b0b04050b4040d1000540e8420003031241c1005040fa280e0900100c1180e07a00e0080c081648101c03120550300d90004c00000141c0300700d0100249a2401500440341007104a001054181c0c0e0071405c03d44d00c209103046003c007541601c0c0a00d1425400699421410b50718603034001c1d595581c01c031b042e03d00c103949560025101201103816180240c0034007a05261006001d000036004192078041c3d111031506201da04000030030101120b900141c030314541890002c0c03421 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 36878008 1250 36876758 36876769
    0x10e0d0e0907030b040b060c0309030f0d020601030f0303110309010b01080601030c05040e0406090203010c021c09030201080705030a0b10050a1403090606120109020a09140702010903050306040908090301020f03220203030405 98
    0x4d66a03645c0c0180d8a901d501400c6e1212005005e107103036240019a91150b400c401c043c03809442201d822803943c000034152407060750210b15141100c1d400445a000700b8054501940601082040d20031044004002c0040c5440b05410000c2844000c0c0c890301e00c2c0d6202d14004405944001000502182e8204410840600e4044c1407da00030700030b2000050700c0c542640080e00355a102e130781820059000442c00310158051881100d400007090800542d501d14550010f010808000c0450040c1710001c40065819240e40e005198103080040003039458000091300134059030050140400000e04030120180c3d01ca1450f030450313001d4590b01d4000c10441d6206010009891142e01d00300b0300315501c510000006032034402d0400040c00c084440400c1c40401410344100b04080100391b5000c6a0400309039101091308001104d170080f1003550003041d20042030420b54110b114400f4069010340c40040c0c152202d1005401550040324929080308094a6506102001d0b0f60000000307941600100000c210300c4c07500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 36879258 1250 36878008 36878021
    0x10080f15010c02040207081e071e1b06020d0f05031302040207080d060801050a0b030114012c040c0602010b0a08030a0305060a0803030a060501110a030903260309010e0d0e090703 78
    0x145006640180382d039001c6030980c0c00c00c5e4422110a0008155850003051840206891500c441001803c0001c030303490700000d14820214810f105c0c1100c1c1500d005006d072016080d5164140c03103840015041e5038031002907540149031b0385280000e28a0102140c002e10800403640038410b038000c000c42140964081000940c400c440803200c5400800a915480b1102c0c02100001c0c001c0c0000043e0910b00a07020500f17551900280b18400e9140614101d40a806942c405042d10030120340c68940240015401e8841c142e14203034103d1250100080004201e4862800015130354158000c0c0000e00c0010148004548540a0080903130024003075100b0640c401d078002a4802e6000784802e10480c0e0b0b030030721a400c50380260303540d02416032241024825960400701c2244810305c0c1200811075a860b94500400f5030031136002c018940074aa12050801005440191700c2401c003120410742d4900f407034a0618001d00056550400d203010790801039043d14054a2509841000030f0030034031207a6500a0110300400c0b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 36880508 1250 36879258 36879301
    0x3030b0a030f140304150309030f26060103110c0102040305010b0108040c060509031f0e01050711030a120b09010e0103150c080112060905010213061b05120d0b0306070503010510080f 80
    0xc05d01c03000803650752403030b0411000f0802da01d00060320704c0c41d42401000102403242d200184400718510082490101c0704044030141c20352030030412512803400490140c10b80f500004100240031400d94001c190640c001c0c0b04a9204034000c110002c520001903035004812140580030150641040003168010402080364400013000e6031640341d40246800d140d6041000100003080d03813100c0e07440400109200e69500942c07541011804400a454010307070301e1040c103403054100002d00b4006000c08419400c450306100340105640050b40c2c40e010000c48004091009031056101c205003000e00c1006481005400780d80e59880542580c20030140d005c3c8205016400c41c2c1c12a916000100854400c0c4043c3c03007480607082c0c1400240745003407401040c44800b801e14126101c18105c840c1c0009800041c80514102e608490a0b2103c0c1440701c02d80003001e02c0c595080e01030203034108120030305034040d009605a45003103450b0700c0113109004027200d07051741c12a10144d040403003d020880a0010b4150030b00300d500b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 36881758 1250 36880508 36880513
    0xe011511010905031209010f0605101209020d050303070207091104050d0302100f1b02010605060706090f0f050a060e0f1e160e06010e0102120d02070c0506031303030b0a030f14 77
    0x50036661081d01d1a441100d440c950405c1450511200d03400038050030320071805d4031400f40040d07420302c00005d10440240c0445c01c18441e074810040710604958014407961500205565141c10813414240d403281c1c011500080140600d040104650085101c0e004402c45d24034501800d00c1c2c00c00d41030003003a06850703100350194406c00c4450850300d0300c90b01032484a01035038030000c00d482086500ca04200001e41c00c54000b91f904101c02031100340c6038082982c80c826040100483d401d601820154000764840ca005800700000c01140001c1c8403002640d031700000c4c0f05010820800d260700b09081c0d1510103450160000ea003103500a4142c12680d080343c440f400000005840c2c610900b00300c10603425105074092884c2000000800800c4c3d0703040329100c500907c2c207001404107415100c181e0902442070002c05107000e40d0102c3c209081c840c0840403078019080c040d0240d0ba40b03041c2460300300029940902d00300d0020342000c50600e100d007000d150207001c40c0d50004c06400307130007655074501c00c0a42c0c0c010034844062 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 36883008 1250 36881758 36881771
    0x40203100905090a0302010c05070308220206070303060e0a1e050601051603090f06080c0a030203150a030f02040b061e0913110d0507031104060f110102180a0e01151101 74
    0x2840d842803d00882086000748035a1009180c080d003074030243c0f103006060010a12a94010a8000340b4580d4440b8031000c4a204100243c024407006411411002e1740000340464480105034150b4080f034150b64840ca0008010764420703c22070709865032111441840c50030340701500c00200154100c0d903045101410024281503c03505c070389034480100e04040c0c3c0019072040301081207001074840007000d8111440c01d50001d2806180b00d840d07030f10410b1121030806034000001503261510b80000035811100400d0b0b14101e40d0380342000c4c1802d5a40000507880b40e4903203048a126458150211070444210750350b002d00c580c0540401704183e402c9444581d4000c80031102640e1401002c0c4103102d190b0b40c0c440d03411038489440c813403d0811034000a20700c4050515083d1400b20601003003085d030741120042d1600041800c1402d80854000a1040003441c0b60360003c1500102994a5010300c500c0e44800d0b20710f001c615a5030702c3c404580240c28442c0d1203002c4c902480c14012a80f14203c9280540c2043c2c001090b107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 36884258 1250 36883008 36883019
    0x2030703080313020109050301050c070f0507051801080f01060302011d04060504090308011d0103020d02210f2112010323030403110406060f02070905090106051921030c0204020310 79
    0x90340e10440b01c03446030780c0c1c060f0b0180c0e04540e040100b0300d02501c800d5000704024549401903105a00c10114080c10501c4007242c0c54080020400081001d00006000c01840c0001880d0164200c42e007070160b0800c43c0152441c41c00f050314144100c0d01101d070142e40382209080d000c5901ea107502160f900294004e0303100d40d000719a9032602e00805845a02c41d944081e000d6141c00140d1203100300e0441010640700346100108050703034801c08a0442190111480d40c00b0452510042c000c0751000200000c0307034081c5100c100031405020400e6014920100f800c1d0100384020f01d2450310b6071240044942c0c500c03042800510110700f50101c8031924440c0442c2ca40401440424840c0c9103801a9100b00c07820441e45180519500f07160040340014605410008050b0f0350b0302d500691184014007a145003135a440000403421070342500118000c4c01c0203086c1c6940741149250203d04c954450041c1b0016511800082616440c410000f040154143d230300c0c009580b0b101d500304406940090300f85c001c9036002d45e0340481d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 36885508 1250 36884258 36884273
    0xe0703020c011409060f10050f040e010c1805060406080f04060204032001090e0103050312151507060509030306011e031b0e040e03030105031002030a1104060f18120b0402030703 78
    0x1e01080c0003600000d51030f00071100b0303203003041c020000c500412003003007480298040f21320311909856085403803c40278181e900204004102d481c420350025800d01c1005e201e01604101e1104070707813180643c000f020540741c034288510b6104034400c0c0400907000d60b002a520b10310340485540c0240c80307000c0240c5815507030384460410b03080c1031341407440400d0100c6040d9080e68002c1a400002c200144e41d5142075031541d11042d80364002c1c2280f0f400125400400910404414207250440301e20041c9072841c80801d00c1c54030407050b08800c008450b40351500e004500400c0c0000f003035a00c1244141c1d6041992006503042e0b40f81d040100c400c26041c9600c1d1252040d40100800f0484940c9080340e40303e02d4081b210a082105580c1211400401c6410800041c422603d0100300c1c614580d010482c00341c0e40c0d031500c820600061862100c42e00c107040c000300d400324110380d0000301c81015000940d510302150081603500d80302240c0358416000e004000045140c001f481044500d030b481030006064030802a03803070f1583d04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 36886758 1250 36885508 36885521
    0x2104050c0d140c031906090311010c05040509060901080d0c0510060902030703180804050f0604080f01150603271103060702100c0203070818060d090f060b030d08010e0703020c01 78
    0x361810564407182e66880382c1089080312064044000302071300150030b02403c61154028001800792515408600c0925004014414410400f070380200240c4000c054000c02981040c041c2900ca05003400100c0c80754941403c1444c141e0f500310b405000d908160040170345d078202000004441c4c40c05519a1446600480e1041c2001428540805030380e900c0d00c03031001421610501c50406e260303560343d0010320128801d0420349c0c040e40d00a803454003501120000040c1580103691107030003148110483e8000303500064103c1260407668880c03140e41e05840e900c00f030707095842000c14003100b0300310b07200c00303035a8a07110455104a80380102034a9100901140109042060803190000942d10413000481d05014074070031b50400340d1852001e103083c00071030f960b4441c9901c600c0307070207500381070510070410031590f0342200311940344003100801c0091440c2d902d08101f500c1c911181c107884081c5050000c00f03c1d41008621211100200d42d03a4084030307800c1040150726400302601100803d5801d10440102000920401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 36888008 1250 36886758 36886763
    0x5121c021c0915030911060906070602040f060e090103030c0f060212070c1b050f040e07050603040c0503010c090503150421020a170c12030714040e07090501052104050c0d 75
    0xe1182ca820300241070302d0050703003440e20002c1524000da0b80000c03561038500281c1c040001c48126070b40c1c44500f400540345004807000604090301c001000104035082e400800e080300c0c11915814803425002c07040101c0030400344005400300c2d1064603600d000031298000c80c403000d40310342c0300142000f00803c010300d00c800c404c8a031040401e01010805040c8881011f8026941d0138080c2030004c200d0170031021403034500b8010103550003542c50303060100c1031510030300c2904050030780500100e4480c5040d090030110480e103885400d01035441d00900450070391048440c00143da40242c002e0044403580c05094803400707001802614160b1000000a6015080d00c004000450303403a4000c0c00002c101c2e00b05048040c0c00550341898030542041400c03001c10b000300d02e52080c65214508181c40f5a100d00d03003070310341102a850800541c840003601040714200480e9450244015503240c1d40015100d10066846108076404c62100c2d941c07040c00e1542075036024452030b40c424490010b40f9070303084015011400640e14107608 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 36889258 1250 36888008 36888017
    0x203100905070c050610060e13020408030309031c05010b03010501080a0f0f0f0b09090c0603090102090d14010c172802032e05060d050c1c050702010605121c021c 71
    0x150410703c1130070014075400098900c03040c030080d840c01c0c00280602c440201d140707009003084804c0600c0d182c07075541504e00800e45003095075501c2c03420300b03400b41d00e0781c0c8601483e10801500b400c51109820251080c02e0507250b811100e94650703407c060055070f4000005220700c405940760f81d181c50190015001c0c0142c3c07106034020224a010304540c01c0c80c02ea42c0c003240a18014000141041107030f0500161000001009460255590b120504420701a201e640030b681d40041c0d00d107240c0c00c1007061150b0307800314802540e0002c12500540203c1220702801e850282c1c4400d008030b1010940d141308030010061082c01100c8400d0f4554083c1c2c00c5481070b0380040300c0c0200c4e1000030004016070001c80e5203602910f4011540d10b08581404c00001a4090059178030501c0c400d0358510010780d21354040011034407180c0e41842c002c40542c0e4500030400140000700d030048019400e01d18006000d0400c22600c01010402c44040c4c28007081c0241914000c14101c4242421403141d154114032030242401a03600c010110743d203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 36890508 1250 36889258 36889277
    0x90307090510050409020607140a050a0803011802090109060e120a0b0a1107030c0821091609020f09040515060c030403050c0d120810150203030603120403080409020310090507 77
    0x40d614194002c1c1d40701500490600400b480140c1e24141150f03226540075030a0b001c40c004100c0381c00e20703050200c1c200508910451460394280007a02e0042c2d4102d0310422244020718040000144c240d003c0d01c04624041202c0e12014004240100056224920b015109500a400140800b450940c0440041d5401d0401c0b40601100141c58003a560b0416250380805140200039500144243e0a109010b44030000c04281e14007031210302801030040d01031415103c070b40350821540c0c0a4840703001000000c02c0108441c0e0000300705c6054001d403462811440d0104d401d1a81c1c0030144801b41c10b0003400c2c4400220947d010300315654529000c0e00c00c203021000150785603801e5240c821314154008800c0392041681300060070001d91981643d01c043c800c1c61610061341d072643c07441c1441c2c0440a8210220285960032141038203035000000c1c2d481101d080741241c460b4020f404d9000c4072071065000244c20010204410301c4100c28980045802c0406104405000360b911841c0074221030040d100030000424046 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 36891758 1250 36890508 36890521
    0x1201020a0905120d090b03040807061112010e0903160503040503010920010201020913020d0f05090f060c03010503032203060216200307090c0c0c0807060f0201141b0903070905 77
    0xf50aa0308080e00340c0c000308605080b00002414422080c4134400da0340000100140c200081402651150b540c0702c1010b00c00d0325424103021000341c000a59008102c81003c000280030060702c03d403280a0300c0601c0155103040b0b1030501a115410402e01e0984448c0301c10440018551000d00c120b1411034001e540010749040800c904c4a14100c1c2054000c2c1103a005021400d519035604041c2107540010410050340c440402085401500c84103e98220380c0e0f1401e41044a02c420108040e54901d441d0710640307001d030b5144d4541000328007083c00340c43e40540c414001c2e03400001005002b250000d0804052414840da00c1d92030b030090380e000e0319109250900d000041020050b12650380701d0380310784014010000d803c108002c2550350a0310300c078104400780c0316054404098000c12240b508031b034100d400302c0052070704e40912aa40795030300c0c4030310800582e045088860092040c41080400440d041013812644c41e4080c0d40440300c9801d51603049858401c22100d00c860b5400c2005400400d00808086060724141 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 36893008 1250 36891758 36891769
    0x3050f0708150601050306010c020f04060902031501170f1308131508160e01180b07210512042102010b0405071106010513060b0313110109051e1201020a0905 69
    0x440d100b040740001d20b080c8101c40c0c0e008400e4980c829002e2038003400030b141e1070001869030350310305100c0ca070007520341007010030f0601054005502c242d201d40075000102e1000401103c001030341c07a249078960b20120010988a900b40340007150420b0001600d404001c0b807031344445460303900480c0c40420859060b5420001d1000b01d60039200302440a080c000700030f2402000710400b50380c03215000c40c100464074229180d1a0b004110804101c4004136807000b050f23440700504070f25588a49070a454200c12000c8070461031004440300c1ca000102d5985950601c64010240c520030003000c0c0003101c08100c11186100008104615603a5100c6540e0010448a03004014002110030107010700c000c10800e001800c5a00303200041050444005880844883c0c6985110100805040e00003818100300041400004009002c90b601c60728003848105083c215180010340b004c200c5445000d40095000208901c07101211480c0080028080e01420312402c2c3c403003141d401c80e8002001c144c04a000c030345051046082a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 36894258 1250 36893008 36893023
    0xb04050105041b0f021e010b331e03072003041a0310050d0503070302010612020901061110051608010803030f061201060302030102270a0608011e03050f0708 69
    0x1d5504200f04004050440d000006001e01181400f6030310140b212002d100700301c00d00f04c0f0506c0300100c18000d000c140f050f0b400303803003038a00013481164100c500d404040e4080b542e4400401c080120031402d911418070310325040d0411045065a00040303d10200000041c800a5104800b80e5603228440d0350040203030f601c040000010450b1562080c07009001c3c00f03002d40e542a00c0700c0c0c3c0e840107d03070312656030010814500c05a50401900200c038451003a0400c83d0000107840e006200390005d002c01034480814019400c3c20305806548107025000401c10301c3c1c020905582180703484000c0d1b42e0304140c110603a1043e100c040d2000705034075604044005600b54002201405040800095461401c01a131401c60f9548003500052040d298252840841d59007540600010b43d4050b00a40d00c1e2894000580502c00d442071000d603980502424000591a100715400d00b541e115403540107444c0d00342002c03d101d4214005000031188580d02010000c1842001064090003105008100c0c44e401e18241e541007001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 36895508 1250 36894258 36894269
    0x1404090f151406090d08070f170c030409090f200a12020306160c050601150801050418060c050903010e030301090c051603081905070908010612230715030b040501 71
    0x107680824028020301d90409001031004030b602d0707501c0e108003e000803c120090800145076080005044042084003040241e000340a00510702c200f100400038681103109080c000300329500104130510488401394049001c0f24080d203000040128981c2d2080400e00e10410b81c440c51400d0110760b0780d8a483c0c940100e4015209200340702900001607404213584aa01030b00280c1c8250460210383c440720304c85c0c0b02500145421204548081d60360b40d001009002903541c031600010040c40000c0f600f41014000c20000c0c0301c044a402400e07803166191000109900391000301001401c01c0b1071803075541c1c01d0042c20742c448011000f840c0d0702d51400e00c00d0402c40742000c1402c2c050060030710564001d0384041c105800d48035050f0622486695035800e14180ba0148202019010b0789000140041d1b41c0c3d10a899000f074400c594000c000c041e40b02c540c01541240300300802000e0000348a0900c4400d001c070358180b9200c2c00100111a8515224040281c81c0402c2040700d100080da50501c00070f89190030b0140c00e00501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 36896758 1250 36895508 36895541
    0x2030a080c0304051f0b03010c09150809010209041112010f0e0a020c03070b01030501090b01060801080c0105090402040f0608040b0c091305090705030d110f010b03030412031404090f 80
    0x19014802611100000340400005031002c000101804020b010f644051841c105d1810004c1d5002c0030070400814070580f4090196107030403600072406000e0003500007510019031135032805002050040314032040003809095555028428074051b91038074010014a12024242c045d280c0b10340781c10301e03099008143d00001c808060050100004154060170a4001100700750150780d502c000c10449244d031142078001413900407084000000d0140c194000c0400c02e100748281e1a40e66a50301c0b0072075801c1000c0c0154034054110781500f841c81d6000b00000c0046441c0a4009400c1c203945145132168600240c1c0420081118901003104010100d1541940721302100c098508211305100402d07334481c008a90101802d6986020401309001000300c040200030040480d200310303a0b00031000f40740d00d00d14800c5007254403030038078100ea180d98107014066a401014000314109480e00441da13080281801c0c1c29024172100c1c0f41d42803522000903004101500c1c00810120300e06960724050300495a207003030301c0c12101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 36898008 1250 36896758 36896767
    0x3040e090a0206041802040e0408040603050f0c0406030902010c080705010605030706030e1c1e030b030f061b090a0902030f070e0d05070303080c12090a060605030a0803160e030d030f0b010203 84
    0x1039039040306940c00c1c0c90603140504d00000d141703040c442c002d104580000100341c0c1010108810440e803c4018001e58060395800c0c00f1329101c42003924015241130710304000c0c003003007072105004881c0f10f94007800c80d4500501d41121004071035207445002d0f52042c801502d4507511a0382c14440c0d414104100d6000700210f25003085409007526200341c40341605400b000c01d4003000d40c064582c0760f2180341c940c258140c000b05980114a82680080c0040000c4090b113030207800f4200c6516401c02c4003281151040c112803184402009500111140c01da100240140e48009421004503140440740b010710310034441e099184c00a4200004060000091b180005200d5039140421800040d408510a01140d45c1420a0070310768441c480495158001c05490b00c9040c04a07004011802900203030003011140624810800139440d40c0a05459813034044015283c50300420110b1241c8140025906149450346404446418140b000900b043d20501421000035203e0b1261801c0c50020b2003854640c590900065140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 36899258 1250 36898008 36898013
    0xa0608071215060503030a0c021903020306010308031305030417070b03040305090d060f0c0e0a05030118080a05042304050c0a09120507080114010305010f0b01050702040903030b1203040e090a 84
    0x505801d88801440c4100203081040680e1450b0800406040000d06403600d800c1a150002c004c04048001a442641050240c610703840482c8500016a030f00039000e49001d0303003180c481d2401a0701c00b421410032040d00784490780214800b0b001420107418000c4106800c0b0070800380c2c151821034542c00039001500e003042403000103908841150b2444009564a590001c032904280c00280034080b000c0d41518108840140690340c40b86208005400846400b001e031915003041c14221342403650701200d0100c0c2d8803c0304000c110700c5d90140609140524040c3d1500361500c82242e50b800c0221440320554080004400d654941030142a6101c0d000c00340729802c0081001d03004001028a02c038100400252112007000d00206204003005003003004001c2c440e00e151108581c4107007409200a4480394680f5203072074010120f0340181120002d05035030342c5050680507000c100040042440c102c6c1410340e0313440c0c1c80c001d503210034241e8498100b40c40701031070301c4500d007029680d14440024001d80c040c0c0c000c85101c500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 36900508 1250 36899258 36899279
    0xc06090806060907030507120f02120907120b1009110405030f060709050d0510020c0703140a020102031b010f05090c031e030301031212050901090c050603040f080903010b0607050102030a060807 85
    0x3840502445d0100e4640c88007071040d507045100310401c10005007032500d920404034080c1c00a020740e01001031620016903903291100e4484036203000340d4000f003040245400100e4050500b6a80181e07188000d00c0209a03035407909022a1003003950744140242c08102040245410b11002d110365514401400880c034000030003c00200c16805403901c10300307504040c41c0c02d00c4010070210b154603004000c2190368a101400c269510307021440112803a580303404034044402d002240034008550706800941c1082c64050a8040320b030395002d6140065907880c20307420181c00c950301401d1702641444002d07020045d121418141002000c801d501d10090f00c603032941500324400000c6904482d042214800c1c00c0c000b858080380d01c00c00715486501c00034180424403c0300c2006502c94403a0380d200782820f001c06545c2d10280004c0d400308403030103840c03079141d6481400418039207001806905030040000801c04844000902c2c0c1d80c100340c2e03003540c25a50100401c102600e9900c03440c400b420040009242c2c0516007801c03c00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 36901758 1250 36900508 36900511
    0x11d060108150d0c05100203071709060706051302040b100903060b04020c060906100e0609040f1b06110607030203060631080d1e020d08150901030c060908060609 71
    0x6040050880001e52207031802075220341094801400b03c0085880c0782031564013604c450182522802041d0b054500c0e046c000804c440100782e0165070600e6080c420380100140b90000340c1031a0f00310008200c0e4400081152140f00d1061410030006d48a050450051008441d400300149004918000c004060541c1102c074180c1144d5000c200880c10094103000324000c2c0c01005036242d040c2c4151001d00ca01404080341d294458244c50746000e100d079a460303019440c2084140c6003642c101e031720080802e012031481030701c2022041c00707403034030000c0703150741110041c0c9043c1c0c180d10801c0060821241a204071000b80003858000c002840d06504500b4018001050380c45211f4448041100c00c2d80564240700700c0352055000140b69600c150501c60340c80141585900c60390224000068548544d40401c080c1c007400741c0b005c66142d0b401460b040f084800142d40d0030308007a102d2204104a400c501d170710780e503d0082c00c034065407141c8007406100c1e06e0003102810480e040e400404040c1c0002d0300f004042e880300708400b07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 36903008 1250 36901758 36901771
    0xb06040f180905030316080705090114072f0307120201020606130b030604030e01110106060917030c06011e0801050118020901030e160f05010e030703030f09081c08011d 74
    0x80500d980c04030141c0d004041002005100340408010000740c003c0102ca03642a030181d07522100032540d80d034401103409100320903090740822480c4841c5001c0003105c00c0500301c81c038880c5207841006000e844519207401041600c0d070003405a0b01e600e203145418284030307110003081840d40d078002580c405e80c00070b500c46000a1001e80180300941044034030180315048500020000f4003629100c0c05e0030705004002070080c41c00580804d0358440c010b1025201442080204c0d14140d8a80710054204111a03100304850603590b1981e10043c400c5c000d2416040c030015008000044030a03e201001d00d9000c0d0781043c02c1c0c0d10803041da03454800100060008501140349045640c100107940c4d54103000142e00501c0b000b5030071101e501c03414401991100c00c2d00d4048056a00319181c01030384c15615030044071121844200f0b95003503000a9801c10002e1b0041039004401401801c194a0481d280c1480d43d280c24148511840e40070306101c030464055410014103409812240c42c80a034074001c00c00000c03040003016004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 36904258 1250 36903008 36903029
    0x503060103051e2e0b180414010906060f080d020303010605180a0e1302090a0c021b0418260702030c010e012703050c010f021e0c04050702100b06040f 66
    0xd50000e1205201e2501d007214640c0c10007130310141050b0780c1c9049503e400c43c408032852504c00d008034107141c0803268428001d10702c0d0810303441d40d0f01da0b60380500b00203040080751281e40d00c038541440062442c1c01a03c001c0c001e002c1d01702c0881450a01000e00e403010038016201990403c00040c81a01c3c0c0c080d040340e42091008426401c03c08020000c40c4d0000703126882505082983c00c1804104244500401c007014002c540034084d58403a2040e91007120908090f06001d40c2c01444c0d21401d8400b184641c2c1840ca1008000040d1010720319008509040c050404039030516410031000c405200352100c821a000c04510800d00340310140e07000c40d40d00d80340700101905101c805004507000342c0c89100c0d411080b0f400c0e0001c1014041c0e09020380500c09400f80002c40e16405032202c592b809510441c003594403c5003e40c01041030041d401b001e01510310300400f80c1c0b15a40100201c07100c4a4450b405102d01078403e6500504041e400740082504885103034003ca403185004100802000c042c0030001c0055a04c030760744 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 36905508 1250 36904258 36904303
    0x9060409051b0d0c060305040311011b030f06030204050c1c140106050c0c060a0e01080603063903150f01080708010603020d150b070b0c04050a06030b03150108010b0a050306010305 79
    0x70003185180780018440c04c3c4626003c01e8165041d003125020394420307120b6044d40b000c0006407501365064540d40e1004944002840345000d0320982040c15030070001c10001070050b44907008038080d100201c1e190441807c00044155110400c1ca4079018070042c0300f842006240a1700404518409040c0704040400c040812860105401400308034104500200095a111610134015000d919480f010f9804a010b01f80050110b00380410f0b00c81c40740d02500346030b64a84069040821500c5581040412101c0210600301c45080b07000d801140a03032030110920040880550800c07000714250b40700b541c10400032005002110350000e070000e065462500307000d622010402d8120b8028880000b011880c10000d141c001081480e00b0700400e4070f14000c0c40c580500c0e85d9000c0940c8258840c621441390000e40c29102042101d21990011307540382c1c0014140c2c2c0c00d0b022004a90b0072070100070f800c80320969558826000310b62904200a000501003034010b44180e43c910b8071100e440b40580c40c00300f0f015080485 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 36906758 1250 36905508 36905563
    0xa02101101060f09060e160c05100f02090a080c1509030a2f030a030c06020a050d020d0c120b0a0e041e0b0106080a0e030702041a040f02090906040905 66
    0x2022052100303040003006850703a5081108007041c080c1c41041c2c01c4900c0c20701d0108600450217121881211040f010100144114004582d0003a0480d01540d0324002ca84038011940e1480c0141c04a283c2d600b00b02603103a04c0c00b00d04020003110a130380008a00c1e408035a2035405503c640c0c0e90786800741450008292105104008242000a0050010003404c0c80c406880083d65155900c1100703000a1044407074a5018001071688e90700810794080e01003000d40b60034900054041e0018103c0d0165403030034905001103440e14030140d0b00074050304801140c4030a0401c10450f8807040c2c04404404a50781840010360503400f04400e0031041c049c1440c05094040013800f808691030300700c50544d00d0b000301c2541501c4c1606000307080313130000c1c043c09001599000101c2c1c020083d90107403018800803007020b149031130055400c0000828500f810904040c10403c4030382000e607114485c00b122041c903d840541d90f80042c00400c030110034010002d5108600c1c00b6003010200d40000340c01c016040e0b0082e01e15521003600d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 36908008 1250 36906758 36906767
    0x906060d020c1614150d0b041a0f191707080f06040614010b0307050307020f070602030702010e09010b07030c06090813032306060f010c060504030206040201090f06020a0210 76
    0x20419150002800410204000a840094188403504542c0c12504c4881014022198181c3c80b584403000c10011643c1518480050a941c04886c0f40000c8050141002c0b0b019182040d21111724800c8404008849007170a9219003607801049442c0d507502100c0c5010444e0b51260340c02004441c841440c07a02c4209441000b5001c082d2100404075620360102807001c81c0e1b070340003c41d01120b0045c2021140313681102c1031030001e41684c0658003440d045680d00c3e10122815000106080b0071886005106928100d091111320083d040c260f020350750340c80c801c1c0009003201403801d00f1940215a05001000302604440a0b1601554540f41c4445101c40d02d003030102c040d100c4000e000e4203018000400d100b03490345002c01107007168414004140b4043e03480c908a40102c21030018008103820002c0080d4040c40d000e81080440c2c003050620742115482a00d5410032110b0031070f011400340e030120003448250b41e0070101c0b68004182d1800242c1d082424500300035215410b60b07030024000c1c0398a000c3e158499005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 36909258 1250 36908008 36908017
    0xa0c020303040506070b180c2215090606090b07020d020909150907030b07020606031507090f08031b03040b0d020a090e0f0f070f02060f040201050415050702040b120a02090606 77
    0x1044140c4401c482d040646200d41d0544810b150301c2042500100440c0c80803d002312640401807000017400104c480340021002100400000c40c0d81e41c18911000005441114002d05491100003400c20b0501201605054590700a5031003004107208500050751a14402c2c14080c4d0f05451202c0c0a89501c00c807a446c080c0c2c0001180d070b03141207041c10003440710360006603007040741d009020711801600c2e1140280e0b2111717010350f01990560800041050365407030b005078464001d2200e15024500f165502c04511142d1181d4104086a800000c0c0454900a01c1c400c4580002e428802075441d0a10b4404407a241c0d01c2500c88156610344c0215055144c5405040228001c0c00075410602d03045c40c084203e0351444808503480c4844609000110394541c1c03003aa03010070385800940041155456900c248611850020400c0781000340c1000040f030788900007440c1d158241d00e039440e000d48850003441040700303562112004c0d50041d03208050744004840000741041500390182c5000c1003903140e000c0440c285208 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 36910508 1250 36909258 36909269
    0x30a02061b0d030c02071d15060405100302040302041a1012060f0e07080a110405131805061b07030e040207031202030114040b1f0f0c0506011502011407050a0c02030304 74
    0x40b100e107021026095004024042c00700c3e403c1d1404ea0307841d00020340102640a0311401d01d070f05010b000403040c0042616410790f0300c10051299040076611000510001042650702000070b80100b020401c60509000b44101c01e450040c4001e00c11400c60086028904440310440400c84c0c10009000410819071000b0054202d002d0154100d41e203c01c403c446c40030003901c4060001c1c03991400030700a0005842504134121000110618042c40c0c02c0410040c0002400c01c039010f41e5a803880d09410b6440500d41c0b85016108001601041c900400c120403494181c000340b40c0c285108000c2c02000030750004030540401800c42d801626250603003000c9841540300a91503010504c0007002180d408054980c1514450702114140007840041052040c01e50062041802c1e894440d1194410b0314015103541e02030203041d1030030850304c01668680d5403a124007039000c0c0c07124158403140900040d40c2802024000c4002d080162001d041542c03004205208030050402013001c40b1020408550302882203500400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 36911758 1250 36910508 36910513
    0x30a0f0c0b040309080c0108091c0905060417070803090a03030c0302030c01050403110106080c060307030c1202070b0103171201030215130e07020c0a060e040207060b040e0f0c030c030a02061b 84
    0x70b040d14015012800c0c0d8003c1d550184500c0640049940c407074000c2900c6200300300060081c821080d516031210006200105083c0143d0728404139440c1c4808000d0f1000300b42c1c000c08405111850000780f8241502c40d00701882ca50820010041e580d00c40c500848102c1e0303850b00d85046100500e00b000c030b042d401020107491165081505000505510003001c03100c0c01c0d180d400030441c055503049816a291035103022141c2001003440044c0820b802a485408800c2d11410b00154001000300440100d0707100c000100c541d000c0b540c0060041c480e5128156407145842620a4a090480e00c1362081e02901440024404c0100c21003080e600c0b070402040d18021026804c07203001c00740e00d8541d44003030350301c04070783c110014400d0281d00348580c0b070001045001c13510107482e00c02c2c003c2413a0080c04040d504c41c0d4009c0e1010b40c1c03180c034402c000c0d40362440303040d0300a9000d03405401091050005907007064614a13102d4403075400300e200e20720203550100b12200003e0341180c0300d940e40c085203400700002841052a003441e07030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 36913008 1250 36911758 36911761
    0x41e080d2c07031505180f060703110328021c140c040b0d1a1302090f0a1503091a09150f10140406210203010605040e030a0f0c0b 57
    0x124072000c401d441c0c45184044111149507407030741d50340301c040c0e20025080d10306030b40f03075000829110340c0300680081d04100c010b480308000410341340c504450146246403d038004010440815498032603150190800d003006403850400e00e01159000c60281491010700000364a203002e000309550403928684464811340ca10214001000701c020a00080030b94140000900015945c907101001c40d015219540b4080341800c922040f031a00405001d241501d040c1428450681140d4031312940c02c0400c00c1804016a84002032414007003418101c03441c26000c1d8101000501901540703103540d60500c1010705d400030f040b0821382003542c0141d02203c0141d02ca04940745c03c2c008000804142c08031307504100182c101d29511010540c00e00307101c08688002e00100c1c0403400b802405140003844165910050010030225110503494000c1c00315841c8601110402c03605810450400b07002d00c00c01080111020003c2c0d51080307540310b03207a20410b068542048405d0321201c4102d4080c44001c4105a08003c47d155107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 36914258 1250 36913008 36913031
    0x3020c0c130e010b030d08040320030409020301210b0601031802060c01060e0f010608010303080408070c0801021e0705030901050318060f0a0e0105060a090c030f0203040501020a090e041e080d 84
    0x30042542c0201c441e500b04002015a401e0000c0c0044480405907a0b04003075a882d6141200d100118144001500514110503039412504002800207400d004400607581d5242c103200c3d8000800020900c8181e2620107038000100d800c404907a40d00103403c0c00e011844090a0745003104080c00ea040c025803082000c2454034000a05501a40640384035103a40f21f425100d034031103503110740700034403407140054100340040c00024410340001360424803880004d030030300c102560303080c50030400d642007020242c4d03011a180350b21042c003064140311800b207041ea9610f0711255803102e0f902d0340f1420000702e0521400001045807908503c02c00708a45184000340c0c0c005061011111902e04801d90340c0c1c0001380d040012565001c0018881d050090340024201c6580750314089000d030141c0400d452802c01c1c13542d9101c00d18103240c80380c002148102d1140b4001a91400301c00c0c0060031004503908076030950500b81c41003000040e0300318991a015141c032405203024040c50300d04000300d4450381111007111030804182070300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 36915508 1250 36914258 36914261
    0x1020030405061c200412020105070602220b0a090e060a08030c06071706090a050a021608070204050c09130902060d1103090705010518040203060f0306040b0405060f010b070303020c0c13 81
    0x350a954184184a210140f240c0d8060391410000390304c01c041030800c804c00803100c3c01c0364080e204a00c10f05100d410500142c840c00200c4c0c2011900036008000d00201c0d480e01c24031004400b0181540044440c200280d02c500104201c403036000d01a080d008400101c2e480d039480760311400040010303100311b0341d45000100889840300b809550fa0b6000c90030700329508925400a058961142c10043c11042e0380f40d42d40c03070f01c5002a010180c1302c0680f040e402c00c0102500b030000301c0e19004050240d0700182c1d98140d81e2042c00211400109a0040740c03406101c80510ba03552040d03100400c1c1210308010807100c0041c000200e6601c202030f106c017206881d00c110140410141c2000d140f00e00d03405015504840c0e55540190b540d807207403071280501c0b040c100d540c2890600d820303406107400000203019014640312007804245481000d84054500c017440204003c00c0141c1004030b00d5010301c480c8106c8070365500d030518060060281190003014581c0110329101c10307420412140c0c40d0322400411944084440344004030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 36916758 1250 36915508 36915547
    0x51029151c0e0109030e100c020303041203110715201507120b06030711010f050108060f07020a05031603030f050a0e010b06030606070809060403050307060b0906102003040506 77
    0x2070460707042001d80ea100c1c24061080100c02605612008a02c02c0301d042045140030001e06600305200c82c02c030f030704401b58a0800203003015200c400c6020748400424100035105841d0700218000a80c00714805006000c4e030706c260070341414098100f07442400e42900b1301c046440720340c00c50141c80744660108206030a000c0c0745001d0080d074050722281c1c034070050807004405440d0f505001d0b80e0007400c00c00c0400d090383d1180814058080540b000090081c112800d0002610801c0c9d006203526441402808400d086e6080d059070031900d00e00050541c18155569035480303024a100c40012800004003110515019410540300c000e9001420040c1d440c150400c075000f801180716240c055840c20201d06114100101224041c000003000035042003402d0b40c455074594040201c50340c0180060000000040c4100003400003140315820201e545205201400030f90348004280c10320030011402c80314001a0440d580402d603c1e28a298200c0f80a540b401c15071a612550b1b000300d405c10310008100a00040c240c5090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 36918008 1250 36916758 36916807
    0x6050103030e060705070501140d05040b04020901080d020607030b0a030605090d02070801060807050d03030b0306010b03040b06010c02100c11100503010e0a050103020105040e061305090a05102915 86
    0x40b100020b180c06001003401440801403180d844118144455802a12010440f2950450942c0b03401103600040003541c1080d5070449413800c1c0c00c02400214a84004e900340940059401400703030501e1300340003d540f0b1b08003800030400d040c0c0d60302541ca220f864050222000d1500440c0a00070390510081c02503841746050a8800180038841022a6100041c0525011180c0000042c8545030404c001c02c9017216103980704a0078150340340310080d00f03030b1000d000049c02031001c82c83c0683c0300d2400f41001804800300628283c10010115004070044c0d03a50804c81a080e021860040c40c48082c0b0b00d0305c02d40103041c204a140c0d1002d2030700300310343c0b8143d8010000d42c180c51801080501c1c0d521807161400c20303148203010017404103c05200502c800c0c40c44068459001c04009c19456a079070303161010308220340e01038410713141c50b4100300141d001303011042220b0401c4821200d0100704002c101510305205e80e000c500c030418520406505200d103907487c0641c01d0881e2303107120390181d906da2404401c1c4000050305101d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 36919258 1250 36918008 36918017
    0x70c0c17010b030610031b03050d0f030b010c02060a03020702040e01020f07050106120c0b0705010b06040303050406020c0d02010e10031e020301060207080a0308040b1f0f0518040c031106160605010303 88
    0x440300c0b07506004c034419001c1c002484003041c2c0e09040d543c4800049159100d43c00c0e91856280000001c2101049045a2141c0680700d245802c4260040201134402180f18903052051500e006401601c81c0c4003220710f10a40c80c5001a218009071000401034040440201e0f49580042150b420503c03120004103c850304c038400070803206a03529407840d04c04680a0b070190045540241c20803100d007075a0010300c000ca00c179100000c1c004405400144058100c0c0d00b041e0000384002c501805116010821001c800c04202c600000c07010850707000804880c8502c4105000d0555212500c902500a4201c4030302c1c0c65042d440308041c00b5442d80030300001d410900c48c1c1c100600ca210000070f0140b8004c20312142058150ba40e02e1082c0d0390b01d49503000c0d0707014041e010b014403641d0071005601c05034204c903400014000026500420501d0802040b0515440e146440c0445144005000002c0c04515606007142d0340031340ca59940d0841e030000100e030360084256084540d4100352420040150035401241602e00c644c48 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 36920508 1250 36919258 36919271
    0x60b031c12110315190602030901120506090a1107020604140301060f0605070b060a030b040b0a0605010513171501080703150c0215040c090c0305090c0303070f0308070c0c1701 77
    0x46490640320300780c1e2040384040c000c00100344020114072076548134000142010003000300c00140c900e041c80d50341c1d01810041c0c0022a005480750b9010910740c0a0040248080c00181450360010b0300c0010041c03c5202e45503a1444101c030361b03031103403001d50340c00035001000076032a00e95071030040a1288400c0d01c494840e511f04040402d014007200f0110085c0c445560b14a0705003030850b50340b00c200c0240500030b40d0348850569800000209452030f0988211300c40c0010b4011400c04d80c0442040c0c031003540046041c424103012280042240c0000380c001c0f0380312882d800d460000301c40d000318200440b60001040c01c1d0001c40000c0f442140c001540011240704d5081182444d40da0320440007100c2c582e07000300b401a08a008494080c5403007a4040b07400078016202d036242d00b0359510011003114039044801c00420f468500b04a06100d00307004c2002c0601042d4091880c24595a82c2d041e001c06003800020b090003001004074243c548a01003e040c0c031903000340031888154071802c094414500c140501d5009608004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 36921758 1250 36920508 36920537
    0x2060a06060206011802030405030d0e0a0303050601091401080408090901060f1e0e0f03011d0c03061003030203070b0c0f04030f0b06011e0f02010f02030708010608070309031b060b031c 81
    0x1c4035412201d100e01c0076500007900a101704040c0d440540103442e1480706100c02c0c5d040c142e0900c185000400454010411440305107000703002c0d00c82c0141101e0620210300c004128841c8c2c82d60781d5410202091800810665407440c10b183c0318055203601540214400002007105070f00141014502c0c52a9100e004045003d6500b00d201e445601c0886000a0b6403100058501e0030080040d0144881c02000031894000c8032002ca0551540c1070104240c80d0f00484c981601400c00b802000d03000f89010148801903030a50310302a543e482103000050040c840d541c006000d100232001a40c003142c0040342c803296126540d0410102e4a901400192114401000400c1240d070140c0c0d0255191174844080c1c42464100c458140d41e08a020000c2034203554880c21200745903200c0d403000318895000350b20b54008550501d00010125030b0000c00c103405240c40c142c00c04000c030786c100300740302040d442007022050f82d00c0c481d28002002c0c0804e222026018812600400ca480d00d07038116000d015820b940d07540d00721135040c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 36923008 1250 36921758 36921763
    0xf0109020306151c090c090b2409030a080d06090507031a04020a0306030b0f01030c0e04030215040c050d030207060318170a03020903070303020609010506040b011d040f060602060a060602 82
    0x19601c01c0d9000792901c1044120f400320002410002e402c070401404035024091141d02501d20b401c1d801c4a4815114909001d290741c648100b000c243c0054401010100d03840b00404085100482d40850030140030441d43c0044c1c2d002c00510030203d501000d1035413144c90701c00295000d400b0030b02581040038105400145030600c01d2041c103c5581102496441d20080202440021761080100c80c1c03c150300d480001c004140b0001130140035910000346044a50f14606001d000f69100e034101c0c1074050980780c1803001182d400100e070444ca40400080340d40b11303100ca1800c4180a00d00da400103401243c5010b0303050615402203140800c4440315242407240342d801100b616280300d90010014900030380701400d0720362012010080c0a03510745500700149080c011400182c81c0194070760044005074040001c116056800780107643e00070b20140c40c2803251a00080000e80011505050b0400010030000c0012290790340342c101460040340104100100d540381c200003515030300c040360070348143e1381050030010784103200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 36924258 1250 36923008 36923011
    0x1804020303030f07031d0c090a140415020702040906021812100f09081204030210020f030c030a0b0402130608010806010803031303020f06010906090e0d080105120106080a03080f01090203 82
    0x20081c40c90b6070b45450003001c1c20480508000100b6a40d80748048102044180ca90116100c3e940203001040071041080780702c0308002c2910b801070b414109140c0200d0b03034017020305811684c001c1c080718545164110a43c001c2c002e00c42d0103903015007498021001c0c4200c44e0300030640800c1341490424194003801c00c1c03000c44120309a0300800c40c1e01c61a11b0030070020180e40211180c01c01c03c100402c0c102c0103502c4400789a00500003000d0042444d1080c4820107030100181c070a8411a441c05500f850080c00104503a800001e03d120360480740007000490406056110400d002c000030000c54a9125401420040c1c0f600350040c1408070710700b0000411a1440003d030070f8101d4421000035407540d924929003142b1070751541e208030290300c01c804013018000814041e490107094000b0000074141d28140242e829645620007901e105e0700700c40d90144105900c00b01d0b0905540c815110f099021504401031801414564084855409461608410540c0c030050042c042c00c60803401400c2e07642c849404000301c2c0300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 36925508 1250 36924258 36924263
    0x50415030818040e0a05011b02010501060e01030b0303160b0105010e060702030d0c0807121d04020903100506060c0a0501140601170415020c15010510110303010302060f0c0d020c1804 80
    0x10284a000d81000c12041e5044102d0000f03800880c0e00c841c0f50040d0340c074000b0b600310202c030240d44031810504100b003001000082d444251000780a1545480b5000d400920100c50300703030401da2540d03003090058404100311031080b0900c60765440c0d0420036007030034041c20b0b000307000711070010f030000035046043c2c50510103603440160002c01500741028110001c0e03890700341200c41203c041c00305100b13480104900e52417500c0101358684500c0e45540c2c12600c000481c0700c040300ca19114520600c0107521903100000e007108981c0201342c3c000361079140e120004226015040740d801180c8101100041085010340002d1074044505540d02c00640320307100103440e02c81103082c2e40400701d803001c40094080b44000001200c00c00100900506e85160f8040c22824600040181011100e401004020504080784105034200181c81c20160007143c180d44c05440b0312042c40084d22502022030b1101550414104592010912200f2100320058151029440d152201282882808030b50000d11801001448080c030680d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 36926758 1250 36925508 36925523
    0x80d1e0e06030a0b01110f0f01110403050a14010612060b09011413050606070c06170a0e031605070b1908010b090105090105071b06020f0f0d0207060c081c0605041503 73
    0x2a2007890202c018040144005e04000070752946684d012001c0c4000d0902811820190030303104a1180600d094841243c9210100c110820040000c50f034042120440306602002c0d0320030203015210700301d014080381e0308041d8241061400c010300300708007944118240d480a580c0307000319a03682d20440c440001010340e201d4001c4145481003182c40400e43c0101d40c4900024111400d100c0503440b21900188541c1040c07006c207003020191406032011010b403c2e0710054801041c0815030084500684031300850b2140d0b41c0003040f82500da81040020b03c84000a044902e05140d260000500030300c4010a480c24540c0202e41c5080c00800e1007002c150407152100c4042e10b0306032074003014500454940c2d002e150250740a25225885e80070540401051200810303030390b8000c05016407800c10190520b210328490b1b000303581c00190100e04c41500441e41108035403503030410840c50001400c0c0000c140c4598030312990524001d219400302c019082c0d2041d801d690381580e00300702070b40459204601c54083c0e408040c1445 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 36928008 1250 36926758 36926761
    0x105060f09010f02010906050109060e1f0510260f0a020708030105060711120607020d02070305070608090a0b07020303150108090615030a051c080f04030903030315080d1e0e0603 78
    0xd50140c05103d44214152000140764074071174407000200c55003030300106589510b81104022581d00c2400d255000495200c01d9400100d684440321804507051007100d0003040ca00c8041841b05024091040000000c09214260482d0900c2503852621003150341440c4400d520001c03075a0312000d8800da691682d40907c2982c6941d0910b0b0411070141c00c040b00c1110604120032580300182c4070600d80620b0804514010a001c1c1410b00c00641000300307011a810465009900400120703100007012012200203040520254507500041800e0000c5184090500c03015107041c86012a400801184144070742e0702c8200d0071a05501c01110158001c2e244984603034043c0d404a2240713001841081c4061800400300c0f001664030740d0f542070400c41400c0440c000c010144101a1403075030085241a80704221040d1440e480c9061303540a03203040e2a034007015040507a14010481e1812070b8034000406860480212802c1d401902340040c01c900b940c21449520002c009101c88001380941650b408c23541c4000c041c070382107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 36929258 1250 36928008 36928027
    0x60909030a090b16080c010c0207091116110a080c0f060304120807050903120d0f0903020703030809210306120708030702040b0307030c06080907050904030f03020703090e0c0706050105060f 83
    0x44c1c1102e20441070f140d2603054004c00241080c0010700c1305520344400850040c00b4400080c1c10055640d010040c0c490901c200220b0120f00030048074029004000c0703206031f0808505040036440300b0007840c0d90300704a20790408110b032000010984040740046400b410002640b0040c800e1500060300c0017803298540300209402c06000d0511700c0c1d8030000a01d4080c0c00d0800c00c0c00024540401070b00c05d600c4c1d40c00001402001281c40e4091030801002d51401444800302d69a4001c0d40e401c550700c03000c0d080003a89400306d003d03201c0900060444c0428403100c040c01c50812040c0491315402a43c0d00b61103012400141ca07600031000c50290111221003024600b0510b00d9024003016140c6841081e0b49030240c25004030001d100c802194028061642d82c50310103103480c401c1e05282200c1038000d1440b5001400c10000020790001c1d0811798040b09103005a1590003510781510280081d0300024040d4404004003d50342c00701d80301410f01c5601032501803001e40d03070340c106002e501d104a40000303030790700300c1041a07901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 36930508 1250 36929258 36929279
    0xc0302010c02010c0213060f05030109020303070f0809040915142a040b0307050403030f02150103080d0b0d11010914060904020c100603060902010807020129010908011103060909030a09 81
    0x1c0950040c104107001074a541e00148401e501c1500a86140d50380f040140007001d6107800d40c81c06400107070002c0044400580009a4901404000511030400489003004010501080d203030005800f43c400d00c28094107242015913129018102c06000745030070102c0d5204108480c04a002e5181c0b01c00f41907428080129000c024030140c4a52100507504100008107144508021485114582e4407142c42c1c5045141c0200341c8a0540c04160840d8002c01d0b05500f05041c00d02c1d00e904699104500555031550950100003610040441950240c8114a040f090244a0000400c0c628003642c601c04100c0d200c0704c21841c0c002c405400c040d0008024000854141825402400c204560400321130b09660944051025940580c208a4010392034031510070455030810107142c3c004201e40020b0004038000403145005604210010600184e94034485040c3d0340030707248100c00350030130400901c00c01107009051442a881614900e006580380800900c4c80c101c04030980f0180b4000707030b5400900360b03e0850142c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 36931758 1250 36930508 36930527
    0x9170d02070813081c0206010b070f060e0106061107030f020d0507080d0f03060b0906090d1401020d020903100605030303070c030201062601050606030105062d070b01090c020102070c030201 83
    0x41696400c00c0400c0c0420b0b6074001074103112403040c640b0055103080440daa420160013240c918007410760700c200c0c50605900071411f01d054910310880c0070384070132940c100034501505680d0050440c0d80782c80c450b0000742d00f0640148054640755190b510340701103a0034819544030b96910002d0071a40f451181c400062500300e0604d10f03514003a07021222510f450301c00c240d0a005c461401030303000c21183e1440c03110054141c040e0350010504540314034184410300021a80f24820707074110610542200400008120a0081d84200114140c001715110b2454001c03640096100303010300c1e4424810183d02d011452041e0051101340e40d4050003850440d03c0d8030740300362040061104103c0941d501c07000d01041040d10940c2540005000d100e0210384d06648060701030031aa0701904040c024a170800042c015500c84000b2070705a1450741c0b5090350700800e0a1080400143d001100680c0351000051000521149000d03040c161034164808100600907518242e00300d01c00c000006054911440e41040076600070000c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 36933008 1250 36931758 36931777
    0x102070f050f090a0b0301050c07030f050a0e0f03010905031303060e01060312050717120609060301090507060c030e030106090212101a0c0a0f05030d0b06120103120908010c0503060907030917 84
    0x12840010540006c0d00355202121f002c18a5403000c03900405060380310440703c00030302c40d60030407520303040f140f240040428183c1240140181c031a0001c42c3c415440035408034600580100999071903482122419803d00541c1c8000c0d117040b41031000408042c4010701c100c20485c0c0d8000d10300c7c4445c00c0c5112080d40da17030700701c4034013510404034419400c0d4038140001d000f026a4008049144110f00c0e001080008104c0c0c0a40114000c0c0c1c90400c00030000b6000141c100280c49250402451a840502c1e044400e20700321030354560954244040000d402c8503035009060014400100da80141d40c0301c49510000c0045442824510005c4d02401040340201200506005d103030340303081c1e400244c09600d174903504c0e0f16038a8048819a00000d140306a100c8244902c941e11a01212524074001c00f2580c400001981800080c24001d49411180030050007a00004001d101d10002400a900703900000342c05504103d40742070003140c911000a88440c46440344821091f40a901140c02501d058014480c40c0c1040c245d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 36934258 1250 36933008 36933011
    0x70503031926010305030a0305010e0403020606040b03010b04060b030f0115020601031203022502030106120215090102011508030406091410030b030c0d0b090f0a0b041205070b010902090102070f050f090a 89
    0x180030b01082c241c20101c1c080d44c040c0d00103680d1030109540040032220143e103c100e4046828091200082c0d004c0344980d04508222070104030701c0841e200080c010070003044110fa015107841c00005000079400041c40c032400040461008580e41c920051141c49443c140c0b0a00513000b000c010b00c0040c0c07607040c3c815009100e5150050420201c5c980b00030070194412200c204407448220744408520b424003610b00a02405a800700700e00c2c0303060740440c0301c1c3c20200e800e07462301da080441c0c18841a4400d52040c0c510811070b00040d05000d54540203e40c81303034840d014130400a80705401c0800c0c1e020760301c030000f1828000680041c0c0e4a0100d03240440043c840c0195850317040c02913801420182d41c501c40b002c171401e030041d07080d40c003681441900e103850201c019000c0b030a03036084802c80034042140020065881608080c050100046050045640d440354403801020f20415000101d268295680a40810402070b005c8072211521307883d0f050404140c078031800d80c0c00342d6000210344407420151242600709400040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 36935508 1250 36934258 36934307
    0x30c170903070c12051606050904020d0917030405010b040c0f030e070b0d0f1a31020a05030402010305130503030c091507061e0e0c01080c0c0105070801080705030319 73
    0x650080c031401c84d078020004012141072520500c074092064200c03801d025845021000e1a100000d0120b015800c9039512550f07002c501c43c07481c08100d8004c00d81259111500101d0503002035515803942d0029a01601d281d860300c103081c2894101032090034002c80294484210030b0074400422800b078000c008580143d402141c10010b640201a405821651941c0c0c4010407180c3e001002d10040710001e09014500e60b03956288680b2688038240201180c03645003403030b400100024010940c003c440c0d801e10500c0a13100041024240342d008000c1c42c0114801d81c2c0601464a81a541800082003444080d0094208002059003440800020010700c0406030035401d207203480e511103184a0304142c1c0103a032125100d6048504004c85200b444808441e030080c10000b51843c0a000c40c0d50b4842503080c54140400b0401050a180c2c090081c0c91280250b88028003a82c6400f2130000e021040070b101c0c0d8842440b5280c800315240c41e02209940e41004c81c9030b4a07400c50740a0003021150303c00c01c11300340d0501103038084 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 36936758 1250 36935508 36935513
    0x9030f030e0415090e0303190c090e0118140609060f030a080f0d0e070b160c091803020708010c02030304021c0507080f100605010e13060b0a08060907030c17090307 72
    0x3d00007007107a10310b01c050038040c075114415090304e40b268003142c4507401c1001008126825140d15080d180c130007000000d16454003210649120046070004e00c03094004000001d41e041043c5202200c1c0c2400d0142840100e6029148030683e0000b070310786980c40394a040001c0c3c02802c01000400c00710b2801012103100600b20b03114292503500004490420f000000740c05801340f441742c003c041c84802411300409034607180407020740c458010801080c80e09646107403a101031240244c0c0da0000b0303102c031090070000c45c50080101200c101c2451400c2303000d0f004140c8001444501803003520401d2206801075407440c0d503141d0170408404400110b4040b40c4c04104d02250100d03004200304c0025160880c01040c5000181c00080c0c5007844402440c2c014034148170007030005903031202485040b400c0a455503114140c28034201c0b0050000c0e40c002445550700400c0f10122203034080c0c0300f41e010700016a001d01040e200d0b410304400fa00d2565a0100100303505c03c41018690041141700c80d40600c03614142e9007014504d5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 36938008 1250 36936758 36936761
    0x102041203080a061a190311040b0706050f0615070503070501051e060a150e01030608100b0411030105090708040305070204020313050c030106060906031107020303040602070e0a090309030f030e04 86
    0x26801d4000440c1c040803c540c2581510414000c1c00c0e0f11144100c110003041001c07401403103401c0f0150000042c42d1070440541c1e000340c01880442c81c0c02c0480585887c0c580c000c86103a9000180d00350703502803e18021801c01c0703c2d0814002c0c091240900086040568003200c082c1d03603840710508407554442001003001184080c0b0a0601a0500540d200c01001c00b524008448480241c07000d40b00740c1203108100550b05070b121100d00d61340b0f81e0f820006141041840182d0003446e882c4d00c4420a4010174040c9211848180e215480341c0c039080f50200940e840441d6044400d010900641d5044072440380843d0840740134090f0143e22a100c0d2418a1901c00954003141c141d81040d50a241059040406541041b80c2401800600d0030150001c01c0982d19010004180624030301c5940b00345a903904105c561101341004441c48950054100d0f03590380d80e100d2000b551240e8a01c5408003440031a40850042e0040340a110080b5070103039201d80300765055032580040451400e44c11002e106400100f40341c82d0321603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 36939258 1250 36938008 36938039
    0x51e040b0a05040515040501020a060e0109150e070906050609040e12070b0103020405010e040203070302101209050d021204060801030b060a050d0b04050c06040807031b0314030a090f0e18010204 85
    0xc1d6030b02510f8501e40300c00d101d483d0102c00100a4071034020b120901881c1d9000580c2c8082903085040030440c80e01d007142c158010216074101030038217100c2e00b11056052120b508030a03140310200046503003007607461295900722002c0d4004c02c0d90240c400c01030090185040d030402d05081074000181c2d8041c00f502c0c6151241640041e00840311180c0c101300420544ca00351094070700410301d5464180306482c02d035002903252038250200a229800a03040e1060040c454450005800394603038040140350000d040150b41ca010300d1982e480107102d440003906c40402c20744203071001c503003168442c200300d40d0031a603984584440c01001e15801035901d40002455980d90400c04040b64041d401c0d00255081a06045003022550008180208030800c0300300940c40c07000903000c040740e4110398100441a141920030003042c0c0e01d640701400603c514000e142045034080024048902107441d1600c1c01951980c0038411101e07071384151851322411800140f145090148040c4c9824814000145095241c01032141c51b58038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 36940508 1250 36939258 36939277
    0xa110c010903030605040911090a06050316030c06020d0c0602090402090d06020306010f18030b090c030303090601080715201c02100e0a0b04080a020309030105071e080601051e040b 79
    0x1120701418007032540511425016010a03079003807002805a840b02c9600015008042d40109014000106288000c0d803105018202c0182500e00c225122882280311548902064480b0500d0500005a042c000646800371b074005480d502d060440300d884090082d08540540c1d0740140e000c02c1100da06503180b00c8800790b02440340000580740c0c1801c0c0001456440c000d030007801482003600c00f100380043c040007080f0480b540110042c0c903950360503402c0c43c10040a0040140c16110100a01042d01d001040c02c5060341c0083c0100d42c10117560780f41a4840b040004004008140242e07036a40d1400740381a20905041713010011201e082d0900d09030030415030110241100160480300020034504080d000f40442c4090001c011b00f43e40016448490740404060001000b4140014078085214000c2c0160766403014010020049031910b002c0207003220107015401140224029800c0d59510701842ca00c46c0a0001a55040c1c00c1003402c0c00307000320b031f06042d00344480410710034040041c08522190003040f0401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 36941758 1250 36940508 36940511
    0xc080f04030903020a0b0d0c0201050108120a12020313200603060d08070f0b1602011401050418080c0303010614070c051302070b0a0c0e031b0d060e19020109050315040b0a110c01 78
    0x2030800c0c881f000c40c1d0040300c4600459040100410098000141000000b950703007541c0c913030b150b820340c1e4281c0e1111174442c200c007480c81c00402040344440700c0e9086011880e001d54090500074607030b08000d1480450100d07859500440c1480401d01c5402c00500d101e00303592003203112510341784d8140c903607500d0030011071000c5689600d401c0400202907084c040c40081c01070240028030802e104000c2ea280700c1c2e1014002e00d40200d6039106001900da4041d642c0794502e0b50403402d9681d44009588116860382d2003401128040f0b49850808039084000008407040160880d0200407000e00704420002e032025015681c44140b03030240440808124000603070350081c00b503c4000100040710a00103441a80d070104224849c1d0040007610144c60202045d920806004450764a1201542d240c5400100240700900380140b1034008232131081e0400c0c030440818903000340c8525610b5581c1d08101940d4603201c442c1020408402c002160014241840d166007244030b1031070103d8450b4842c0c05501c096080b00750044042ea = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 36943008 1250 36941758 36941767
    0x310090e0624030303040b0603030f070302030711011106150103020d0c110729030c0f040303030209130203090d0c050a0b0702060f100506040501050c070503010f1409010c080f04030903020a0b 84
    0x1806441144440120002c0084240e03400d080003a844c0d01000b030000d00380103141070001d00c03540c1e02401250061104040229141c01d040c3c100250740350410013080f508a603402038100d0b80356010381d0047e8100f4403400014901903550070002c5e01c0e01005403d515040c160240b01a01da0007013a40290b2036400e080c0e075102d271403480c200c85181d407500809501a510010a161059840130340c00b0980d248415520b026142e52901c0e480c1400300d11340b103040b4400341c0860003c00c0210030954540c0040004031070441d20b01d540030300c0d1840c0140072840203407440041a808000c40440c0140142c0506880c540104241da50600441c1c4801d45281021510312005130440740070050031001042401b900a83c4070418280b01c03e080001080a89c801c9e4003074941400710120300d03040d40e0002000040007801028000340721821803031070080081d06440420780c1e5002510b030002050385505200c0e604089003d603a8500154407090b1046100b004c0c003410035010010340900101c0544c0b11820440000d01c41501125502e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 36944258 1250 36943008 36943021
    0x20118120501050f090a03080c0403022101051b09010e040f02030106080105030d02031303020112020c010c1d090f040308041a01120606050d0f171b0703060b0a0b040306020310090e06 80
    0x21190018131a0000001c8202404898000015100d0200da4541030044464440d01d100c0052405141d000a60040416400310390440c2808806040c40000703000a1005444a079040004c3c202d070301c0344801c02000103014240b0380d50302c07483e00c02d907040c42d02030000120600c00f14118400c1c1c0e8426008500032403994001082642400c21000540c0c00304e40c4061800d1600c0310407003c0f8540341038403001e810404a0340482000440f180d044a41d400007001c002c02c032079940f0840140c0048140c008002d2a103101a80e403040c2e90030084c10a40c42440040c0707100549590755039003500d10150240080d200c0c03003100b02d000107200d2a0181114084c205e80001c003503401c020341c6030110541d078054001c1e43c043c03811825048001502d290041c00015400751050081f18400403200c44140590720003015000d0038140040300c03440c0301090040a0782d006450600c62030b020340c0d0900c00406298030800301c0d070803070420080022070415405541c100c003c401c03600c19a66602c07000c01060766501d103030f240d403681c1000090010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 36945508 1250 36944258 36944261
    0xe0a030503070209010b1806090112090f050d0212030105040c030b030307050601030c0909030804030c140a080909090102040e0106120209040227040b0f010c11060703020a05010507030522020118120501 88
    0x1130081c14203040ca41036151130000240c540c0c0101fa18000c40c0080ba1141c92603025540f407410541c5030392000c102a241504049810514409040d6814015142e29814003880442c810b0720380b44d82c000030b0318070f5a403038002404014010f0000d140105543e9411241082d60240000c001241c0280006c02565044d804d0a040c0454554000b4110515092060000a03000801d4661060700342c100740a40038920705008141802d4041c401c11580200c40c038600411081d10042c01c012502600c12015070f44d03403100d44d00e00300c1c82940a40c02c40e41003840010401c02c0c1c4190381100100d1311842026090041c082c011a0913030b001061a24070751a050f1441420100d82220080c1181108940900041d44098040f40081c42501d50540c104114412031001b401744854641c40100c0c4050509540c0d4003250078029190a42c40b6000c031195400d103808034080e6880390254500510140007540704450000e5010b80780602e252a00300d061044500b24003080c05148540d000c02418154440460f54102e45032950 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 36946758 1250 36945508 36945511
    0xf0d0503071101060e130c0503070801020c06060d031403100e070305010302040c020d080a1104030b0406020a0207090b0108070f17090304140105120c0304080c0303090d03060e04030804120e0a030503070209 90
    0x196032421100308102c001c05c5085030b80007001000c2e600a9144a0b080c00d080099190700402e030140318121001030702140550041621021090949440791580420840c0050400070302500003030f001d40b4a10280c42120b4001c64104022225002005940303000c0c69081040c111600008030340c0d101700400c00d5041c42d000e0240590f00da032001c0c080042034064041c2842e480a401c07401015a9011907801c4030a614044402440d000141451203140504e05240a07600450402006004a1500081c850354074000e200020300c05868014244d5103241c400c076211105102508100052028405443c5545810950140a501c4040e43d0344900b0050740c0e134039400000413000d0400c0f5080020200100d6040e116a4005da071081c80955a9256820000034074001c1031018070b4240000001e102041c080010300c922804c0f180e0701c0c00c0c031031681e5030030317031200340c103608503806404202401c00142c000384001d043d1044088007030400d103410560500c00f003640c50001e500304449035400081c1040a5241c841c2400c0e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 36948008 1250 36946758 36946787
    0x305070e0117180c03010f020d0b03030301060207090c0c0209040b16170604020705150709090501050609030a02040b010306080a0804140604060f08070c020d0503030708060429030f0d050307 83
    0x4403440e4440c04615824828028070440791410303400f400e2611590140400c503148034008000b4403110030300510540003580460107200440d850004140a28100402642d040301d0058000c1c2440301c0c500b00111003d1700ba86d0a800d03080080d019800300060f0f0302d18840e0b90040e030080003091180c0c0382000800c00100c80d0b460082c401d12140c0c1c0440d50520074011103581d808002950b0140c1c03500c04a240003464410003020215441500d00200702d121680420441d0071101d1401040c0b100381d0381c0e007041c040703c0c2c410108034541680040c540d00e40035040580207039007a140c1c10f00d40040c400b540c40f220142800d01a007806c072100e081c001020000c0200303095400c035409a00701c5d511450f0624010303001e4503c405506262702404800c0002601c50b41c000c408140c801a00908101c0c11034a40c2c0c50015145d501c115034040214039600003240f039900707003480380c90460310080e0149a4400c407498490055400b240d0601c90b85841507041484843e10248005045401107844603620fa0400d810060b040c015000003030f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 36949258 1250 36948008 36948017
    0x1512060209270c040f0b22230109030b01030f1518051c081603021603210b090c0d060b0f0406080c0f03010323070608010f0e090c0405061f0305070e01 66
    0x605c000801360305407001311043c0100440d40ca00c07189010030100204840303001c6100060400004209003400021107061700f03400000c40c0c0c0840070a0064828001034000a040243e0760001440081c0180c41c61711b026078018040c3d004064220342e044030680e4040c0d40c1400006074144603000401c1000c10407401d5840ca210136065410728a0a070041800c403004120851440904d207001c40c08a00a80c110b038103146104030717004180003132400c0c05401c1003018100e11400d40c4c0783c406101c1144615205440204000500b18410703500c88440041c4290080e0b411162040c0d5500c0700010b08641c3d4600600040b40c04c0c074400d9031510b2030201e000e001024000d21000d01050108468001d0040800460381901d81c407110b010841e40d242003503069861450701400700c141c13180c44070110380c0a400c982100e048500b00b81e402080c075600d0b0b0b481558401c0c001d40c0c20940783d0f0300c004000c10311850250440360380b040010b000344284015a1510f00c4d80483c03008030100109a944040c061459881490034050060a080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 36950508 1250 36949258 36949267
    0x603030e0a0b180105070201230301030209010e09060a0b062205041401030503030601031a190801050a0e031804020f040b0a0f0f0f03050603030405030703050709050a1512060209270c 80
    0x540f048210844095410040000b48240c1168022502e900c00c0c0002ca050b003160790318038502c111189500038003040c1e100d000301000009844496042442c030030034414020307044a8403549038010180030100f81c4598401400d12503028401d141c03654210004900403c105c801c6480c02041c84215144491040c071040c10900051002c42c400108681d04403030b080c80c0c000703114061414400107401403109a26072000007241c0c0803c003203003000b4040054401c0c003070080000b911000740b80000c945002c184400740e43c00c01d10131500718410310103952122076009400545807061607003aa2010b50b0107500080301e2207a0205040460961203050554210b6a07070910440c200e0340240c001c0d01d50f03400c2805900c2019184c9002602c1030300c090054038010600a02100c51864072842c2c015101e00c0c00d402003491030792a150004e803408045000f1a81c000c07265003200c000c42400c20b610114401a11441900c00340e4003080f04481c280c1340d80e4900031802c910ba000001602c010b0094811954601030a401c10612041c071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 36951758 1250 36950508 36950527
    0x1c0216050a060507110a050402120403020609010515041a0306070c03020105010b0a09120212030307030b03150601090b0a0c0503070c0e150a1205011404030e0306010e1b030a0e010603030e0a0b 84
    0x1046500d4517802007011000c0b0300a8600040e1b806049403c0580c009001207402130050b148110818003c1d440380d001e5404a586582d030742400c0358030848151440000745409100e55043c241c0c46a01da07007800d0502c0022102e041c0004c20301e04542941c20f02c0010b4040c0000344181582032090720301510310b03001490b240010340800103180ba00c89000c1c1902014400d88030400710345c2e0307030714003071411940f18800c1d01d0f102d00e0201d030054014586891894000e020300d20000c00c00304941b116561103a0380584402c4070580c203001c0e1000058021000010a02c00c02424000120b0000c02c041c001c02446405420240750412000f80b06491016002c82c113002000201005079641d01c881384400d50300301039540c0c107400782681040b0740941100307441c407041c4120f12402d010a25901c41c0620030001000d8085580c26640c40e612440d07819800c503100c00702c002100c2500c0903c000c0390310045820045080d004150a402c60150b01e0844180358811004200a002040d0030303070410903240002410b220f00207604150418 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 36953008 1250 36951758 36951767
    0x3150c09011103070c03081306080408030403110f032701020604150507031d0a0201030b01021b040c05070803090705130b0112050408070c0305030403031803031d031c0216050a06 78
    0x1200d40c0c1803181214510040c401c00b001079410f615000b20302c0c82405943c070304001c000c60384a200f080424440d6040081181400f0307903c59405141c0c00711b090351650340d590301c04680d03090598000030468050003880c025502e0f42040030380b000144403d90203a91210743c00f50a00c4416255407818195044502000040345001610300002522070002140680d00c3e188100d008100005090110040d000c00420100030001611042c030b80c03003030300d04100b01c10a00b0016641d507241003180d113604c03c0c4500010680f50a164110005041c00303400d00fa810101146d1711040181c10444440d12503a201c62420450340ca040c040122904040c03460401c060b100d6880001d059000140f10100b40e0798544004c1801c00003518100c3e082c143c0c0082c043c3c4445912841c0160b2690301a100c00e40001e801100086c9040030b001c0c04810859074903803030306005030941555014080103010b4299501d03001c1c0f42440c4c240601c1010044a03403100c264050b001480210007400141841500f0a5000f08240700040c404581c11 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 36954258 1250 36953008 36953017
    0x30415171909050c030d0c060b03070f09020702011b08071a0907060503190603080403030822060906090b0916080106060206010e0c0706060e040b150a090207020a081b03150c 76
    0x901c0008910300c1540d0900c82e2500e07141036000c1d81c01d80700c1d441c5554030f00c90788203140b000b12074030502040c40240035a50405a41c1c80c8280110810760350f08107000c200c050500d034000e140141c03041c100070702c0358644c0d901d6091020490b10016200402c00040f03401c10003060040c02e40c0c94807004846040d113400c00035800ca0b910466806040140a0000301003190441d4414240cbd0041020f4a42840362540700d2411039400e8000b40302c200c0100d001d00b40032a441c848141c50701450242c01c0032045120040c3c5490708400740070360340303030903103407035a0310001d4002103440310142510035070900f002030813540d00403009051a52056407200340144d15210003030002c02e6001c01d405c0d04403240b0312450107058440940e000241e10a900e0b008200d00c0c68a80c000840440b2005600e110303d0150402503400d9803070740543d50038074280310b03031088d408042d1403001c0c0400f0206a018154440c00508880e01040d140c400241c030302109020000c0881500c50300701d000c945070811008848080441d480015801c0c4800c0481c1c55009 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 36955508 1250 36954258 36954301
    0x30b06041b080703020a03090c0f06140f12070e041b02120f0406030c1407060b010f03020a020a060f060f080708010e0a0c0e0703020708130501020705220f020c03041517 74
    0x1700015502c003a544030f45c001640d002d80000d00c4165042c0d48400c09500300300c85105420202d10b40da03849011021450082d1500205100fa0340b61808404580d50704018000500803000e12101c0d60004015854510605015602c483c081100d4004841d0001c2c1c0f03820640812800709140401200000e00480b40c16901240d40074103001c191000e12200682c1c004168245040b604580802c014044c40010b41010444807001c2c1c0b0340c0c44280d01c000101314160704c6005000005a4440200840000e000d03900826084050060000e000d50b1030b5402c1826150079607100710302e658000542401044002c1c800c42488550703140007007070042406d80d11901e003044640b0400701d03c01080f000082001e40250101e90842c0c2c0d01c21819551050150114840340c2c0d90340c099180103218906000c1002c1c100710024501c400314040303080510b45903c030b034050041d008002010500f5a000c0c000078124032010000f4001400f40032010080d000c1003204c00420210a01e00980940f014501c00d10198241c001c034141c2c0a0320 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 36956758 1250 36955508 36955511
    0x6130f0618020d0b06090f040503030403080a1803020616050310150e040c031a0a0810020306060405180406110403030e10030b03060c07060f06151d0901030b06041b080703 75
    0x7019651100c4400d81076201c00b94100020340c82c940200110081141d11400048600e0041c5484021000480107406c82e002415039104001180103e4060010b455104c1d1604601050485008180080e081c2c0200c108401580c018800d11100354080c80f1240704040d20362070f082d070a41ca42080c1e071600001c101e102d4124100c000200c0c2c0c503038961080b1054000044d010f0414071120980d0300000b0008c081c250150321341c10800700e1410300c1c6403400107401012280e05100506c502907920450400030b42c005000180c2c03140c3e0400c00082c02d83ca400740704185282d68000b8505040c07501d41400815521003a070380c1c00c8606010041400040d030003249080c0f0059058641c914030451441080e030051034035a4011740d02d0300ca00020040d140480500405c02981b08200a1120308015885142514824000c100940b200141c80514583c0718480082e04611501402080382c0c030380c039003c03a00c1c8000a80003036410f0001030301001000d050500550f0300003551901c1441c0032400300f4030010503510000d4010300416 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 36958008 1250 36956758 36956771
    0x60903031b0304050402070f03080906090c040b06130305010203010608010909030816050c01290109031a0915070203091804020901030318051305090d0f0203030a02031008010c020106050306130f06 86
    0x10002c0003a10003405001e07208540e59031311420081c4501c903060740100e0002d086880021401074002c240907024000c002d000348800040e143c10040a0282840c1140c0c01a0083c414502e031002c51008079002107000b903000503525410914000c14828050704030f040f00c04d0509160600081c0d0003040c10b6400f035880c0c03103010803d100b241002c4810307100d4002440199800c000754200b21090b024200f0101540410900101305101001036841c00e1381440302038202009860700745040c0424800081e8050200001c0d1130422507208114080703148142c42200041c3d10104602ca442d040150140342050610150010545082c1d80020102d8a05010040820901800e400d20b44141080c507e005490014a01507224503000e206500528003111345800b04c0c404d03003020800150185000f19400550380c1d024600d10390b600752040c000395001034400c044240c0f881000040101c1c1c20321074582c10300c101d6400450410f1421003010b2900001520783c01136405041e0261700007170488120790320400d5100c480403075103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 36959258 1250 36958008 36958057
    0x209010509060c0d031d06061309140105100506040806060409140a0803060f0904020616020d120203120106030c0c060902030f0303011e0b0712050c0a02150403050c06090303 76
    0x6a0080d048115000240800c000c42c00c032002007211134459100c0c0da01040051032070a0740300304038181b07080c182e40b40750400c41c0415640d082c681c240f4070310341c010090081000165541e68402483c102c01d1100100d0b5503d0f422312040c07010300c214081c010700040303c486040500b0a080c4948922000d0b1641d481550360b00c041c02c04010070000710103050310000c070540b040c414503820001030340d40c002c0310308600c00c02401b44480d0161030080c86040c000d0341c001d0301c0c0c3e0341000c41c1611952403000e0314044c16a07210340b03418581c200203424a43c1007510300301141c0c09113807550001a1001541b02041c0c22010616081140f054207055002808050a0b82c000c000414052414004607040686146000c0700c2c038040000007103014141505926425041e803500c401030710382d0301c958009e06170085040c002e01c1010080d0b864241184a0005807000d07801500130744900801540c00a082d01941060b15403a2480200301081840320034049600000b1060303c076985483c2c00307400066160b100c0c0004010460078000700c200c49 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 36960508 1250 36959258 36959267
    0x11041502070f090b0109120b0103080f07020406090207061b0e13110c06090706050301030314071103060f06030705030106050307090c090b0307030f0b040209010816050c060c03011d0103050a06020901 87
    0x8022502e908007102c0e0701d50b4580800b070807001c80e150b80410640980000d60125030740a61120710f0b001102d200d4241d0941d941c640443d8441708501040c81010320071000565218412000281104140141d80c2d0b0224a4549c060b0f51744480b640c1180366105031800c03050b903000070031f841c046c41d404c5890b01c090001000d400e20003440300700c80034241c1c203102007000700c1d4414002580714021034107a4200d07047c003075503040106ca0610007400004c00058030560b68907003500c0c54a0103000c00750700c038050301c12011030304401003403030118112030042880c8031003410f0004500b42030051401415059000380066070400d404681d071501c161140e0403010350f6070b02c112018544a460500c0c080c00c13036031003100da482c2020400217000e490101d10740040c0030b15001c446d40030b030f1519108407281c21006849802c4d4a03070f51060b41c51034140c20400182d05000080081d40c40d6100d003482614468202c00c402e250f2039504200e024980c070200c4840c801640b09020005201041e00040c0c05104590312450140c0e803901a1001202c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 36961758 1250 36960508 36960523
    0x90c160605040b01060801150f03050403050906070b07030501171e01153b060d02040204090906060810090503030a05060d14010903110606013203090312090111041502 73
    0x5004a182070184002c0009401109040700c040c0d9803a2141c5980356444c0701780719190202d040000c00d20560b140038029000f600140d42c414024240107080c0013003100824410707446024110791500343e00041088203509849414098296104060b0b802c41401d803c060707031640d20040e00c80c100c21150005480c0b24109410134000d0f020601c1406403c1c507a100c1c9030010284c2100c05001481c1040d0840d03042c20440021600e8100410090f02c0206880b55020b000007941c11300007c3c2e80080d001c000c041124174450007140300541c441e0701e000842c2e5140c1464036040c441c0b40554290502d0070404d449001c83c0d0000152501b08031480d20020b25600c0700e00014241c0750036820010704c0756640b91050f001955040d4401c1c040701c1e020b80c803000e0502145140c4a07031111011680342d070115000203a8250020307580400180c0100d401320710640c03500700191003002c00d6042228140120380c400920b41c6000150618616040350b4445c00900000007200c1d00d2440c68000d5000e03080100c00358144500300d8600c01c01040c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 36963008 1250 36961758 36961763
    0x213050d210f0305070305070c11031006080a021507030936050f070801051c0305090319021314010909021305150102010608030306061806190207051e090c16 69
    0x640781c01c01041014042c0ca0800d0a0500428540742c0010307800e9009004030343c890302041e80c0d400480001c035502c40f00c104104101068140c0b0031503503c43c5142c411841050080d00e044001441c2c01003480c4100304185002c041614003980090010000194002444405507200002202c24050312400c42400c425001500501c10108080c800c00d074400c5c441d0302c207602a0500c1200e00604d96602601079440c01401e21481d40c01c4040d036021100718103404054003084034828500710b0314042520001906d03040c050914401141245074043c400c51900210345000071480c0d000502c44852151110492480c0c14411045415240d0460b101150303503442e030707000000041003004c12450400180f21030a00d02612107003805507180c060046071031000041503c3c440c0341c000f03042c0c0c0d00e0200c1c0c980140c02c8030b07500c1e0200f803600000140710201350f00c801240fa968100c0071681c010485180751100f0089900c001082401d2240e59120000085031554940c0a9101c407280d21800c1e40e416030f168820b884d4050340b6001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 36964258 1250 36963008 36963053
    0x50312010f030303050a0902010215060316080d02060108070b04060509040605060a030608010c1103090613050310140f04020d030f0207170102071716061107020405011e090213050d 79
    0x4a000034a801c0c400c0e003520301991302003007140d40d9503401c1c40490340700030307406030250780080c420480f61010032481e180e000380060199031150a244c0e41ca41d20703a14954206e0170300c40e0086403c2c0781c0d00f03580c10040a4010503007031008102241c5041d0f1000242d2051340149803c1000002e5401c2d0940c466410400082a001d45071964961481100500910b590300943e043c1c0c1d42044006010f9512591683c01301c90404000303145000300c00c0003004096442401c130100c000000760390000306682e09016042024100c008081607048040b00e10721050b040c02000c11031555901c00a00000d0b031258001200c1c0c2940c0342c240200049403182050346032051592161a0942040011054041040d000f4062141c440c450f81218000032881e41e2905015080030151900e081001e14004104c0d40e4104045141640030014500030071070b004141030341c800b40c0040034050410004040e002411102a0000b0707d18603400714103000350381034080300000041c8507041c410080003406505202050399100d0040742e0000704d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 36965508 1250 36964258 36964261
    0x27120b0606041d2505040501030504050708010606080403020f070b040b0307030b0a0f06080903070f150f020d060302190302010906110309030d030b130905060103020d080c0a0b0114010228050312 85
    0x36502440c041201c0920f0052a0910010b1054240300085004c040b01c40d111346007090309000044004080090080e40c00c0e2041000c0014082d10a1281c00c0280c88030341d503000040d02d01410043c1c54080c0c1e032400d200450b400f50b14104640d4644409a4080c1c0710489a110f507283c039a10402c402070410035511550107a00940002142d40e10304000c441103480030344409850b581c403c0d001549a02030709001401e0202c54006403000210510840307c40101054800156600102d000c04100c0e0800d4030074000c91760340c4180070b000350f14200722169803480c04100200245421540003c000359940e03c544000d00600440c000d0380c0c0d060920a480071002c01900320f42ca40d80b45a90020050031102070b10038010301490040d444284482d004117035241c2d41240c0108016480c607400c0c40440b0a402038103580b0340b01c0c28020a140354200f40440c02a0700d02512007011603505081e41c2d091185c240000090540d80700361310f080c080c1c03c007171201c0951110150584183ea43340d2400d00300d08610508430840341d007044150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 36966758 1250 36965508 36965549
    0x6021905090a08010b030606060a020f030403030e0405060f030a03030507020708060a020703030b010519050f040504020d060806010b070209040f0311060a050106022a0d170a27120b060604 82
    0x3028041d00e01c03080b40c11040c0e00d9561401e00f8200e0b07a81c1001981c0540002c00014917606051005100154440c81101c60154400008c11b0441d00207810480004101c002001101c1c5060300030075402c035074101c2d014038007145040b0000c1c0d40c90703004007030040c141034071180000e07144e038001e00140c0c2c02005103e0996440346001d1486500940c00890110042450007050020380d51081042d42c503408009044060303010a0745206955580000c0200d80ca0440108008105510f40e400500410104001301107580c40c2861400e078213140050b00000b8101c0c4052000402682c0c402c01d40701c2e0000d4000e003083d8000025400d085039200c0d00c0032144400c500c00c1006001a03541c042d401103040350321945c05d50380740b01c1c100c0b01c1c060120048d405a281c0003254171284a83c282ca07002c400c0d040c03103911900f9640780309406451821061f401c02e0f501c420204002c00c4601046495110b04081d50000710190300032214100301000d0120400035002038600c0482c440000c040d038446000300e9010f44144146202400e0204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 36968008 1250 36966758 36966767
    0xe04020d11130e280f1113090b0601020c0d080d0603120c03081302090a0507090302030d02010212010b030c030106050309030f070b0106020f0f03090d020d1208060a1202010e0d060219 80
    0x3c829408251141d044801d110246202d6036071030f600f14072082c02003955000c0e140c040007454245019504003103080900031b40340e558008a400722440005d030100e2401450701f40698860780003401d50f415504041003100440d1b0318824000000303603001038a00d4565000080d400c0081600707030002000404003041c1403007100d810031a4511558400e585150480e51410074050b020206110000d403c40c802c4400324414065030f81010b540b0850341c1c07401c092203583d00d4000130300d0030045881c0ea40150754000383d40810b6069040c405405001e0800030103145013092400c4070000e10051080004222001c00801d450110510803602500802a00d49843e44042e0501441480c001e20601015100c4c110452034000408506100103090300405141080c40240502c00180035850040b80e000c00348420140002d11100300c01c2c540901c1903a1860580d1901206200102c1540c0d0811500b40c1010302c40d82c0c0050780d002e10041103a590070366074900032907001c1ca0504040e00440804d0303442103504500d1000c159601 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 36969258 1250 36968008 36968021
    0xc0c0902071b0501050304080a110604060e07080609030904050910020d060f06020f0a02120f01050103060c080105180a020f1603020c040f090b06060306011808010501060f03060e04020d1113 83
    0x82a54802c210007604401c241c0c0304640c421180800d42c2440000c02094426014012403202030916681c03024480500d1420b2072004c580858440c0d03514141000c618800700424405031928400610590819010255a03400362020b02c6114544400001d10181018444030f04a04e01c4001c056496086101a020207028240509402c00c03035286000034440b440016040e074810102c0e00035010114894080c00300d5100c001d190345d80a171040e10138016148200f440b500b4001d5005000004418442080c01080700c030040e40480d00c0340008603801d01c01d00f03002e010600c3d008400c2c8000140d454614828017403290284580e4903c0545083c0ca00c9c10600d9004a45c040b0165000c840c2080300c80d900181d080d081b41d00001c006424807104400003101e5003800001941c02c800b05051205003441c5805800c040c14900e5040802d2a0f51039200410009400c11400000310083c0e06051040c14240800c0344030700c1d100200040d10500f0786201d10300c1800680c50000c4080c1c00064081e444082d41090a50b018112 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 36970508 1250 36969258 36969263
    0x5120a030e0d0503010302012c060a11010b010507020a060f0903020a030305030907090e030702010e040f02070c0f0503010908030703150302030708070e090d02031204030e0306100302011d060f07030c0c090207 91
    0x4290940b034070302e445001100c1c140d075816100c071510a007080c0100319403110300c41400c02d10803025880201559541c04003404030780b002d940c2c0d49596200350440c0c1c5d900b0f5801c40188181408030900c4a0720040e80c4401e0b850302522401c0c80c10040d1000c4019044440490642c0301940203010500701100345507100000358894184001242c0c0b60690360000d0fa400c840c0b000500d42c100d50002d0000d88010340c4130324404c00c0e40090003000450f40c607003003443c54022644195403c8565826800c020031441200080301c02c01000106c000300041066501d5411252200a1041b0205640c403030000b03401c8903000391504003464001d41110480f507116540d856460b8914060141d812800c0e800040106134001043c980328040c584c069410f001c40044000300d180c601810890a00504108884c0151020485240f15008030b502010301c0c28550300024004140308143c0c002c40c00640c00120086858010840e80340a9113090140d81c1c910480c00d0445118459141c000d182e5503450708009100103654014041260 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 36971758 1250 36970508 36970513
    0x3020414030601180213030c08010c0f0201020702030a02010e0d0611130f0b0406030b0a170a110108090c091b160501060e0403020601060c140a050607020601090905061305120a030e 79
    0x2001141096611a802d101e0302090300ea400a888038003a140313802130280e21131110171042c0c8447e169520014050f28903000000305070b55840a6406041c0d10180c0911184101c0c0001c42c680b06171a00484e8032094001c4010b4141300706450500d6540c0c442031403000c040c81d046502082074070403801d0303036410560040714190043c02c100c02011451a014106800c212510101403c0ca09858400c054029114021500398090f003d10740c00565401070441c41703401410746e02c0c058101e85c066440d005042203210105941009529420030004040001d08010109801c43e515141079640b007017464003802c0700301c4405104003008900240011041c0c4940385045105200134405607407616810700c440d1304211030103030041c7e100340700420405010b07040070002c0c14007810481c0884010010090301c1c4c08130b02081210b40740c4c411800c2100b0281d041c0400d07805880d603044144807451040d1200c994070040030b001040d0008542c0724440806c0b104001e4000300d1031600c00313201c1d1101c28030080900245803031401c020150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 36973008 1250 36971758 36971789
    0x7050a0512040e18030f0f09010f08010506070b040618050a15020f030a050702070b03010b120a060807050405100825080607080705071b12060f0c08040b0702010615030204 75
    0x94200c0300a0341c050b2901d240d0b104250313580d44210500707410001c600e035004a01042064880c000008030090140201118482c5d0380c412443d4001007000d20200616410001d50ba00180041e079a94400c4614054200754242030039100c9042140040c80800c00060984800b081d4400400c10045410b000d181d004504410000c40c019800105a12075803190b08840d81003000000c2010019034803a0b600110ba0703104807a6216110415400150300a8120b078560840114100c10b00030100d41159a110545410500041c0d02d40001169141000d0142910882e26100010b4076078200000d104001c18101d03048600d600000001410b0320860521080c03a640e2038180003046501001030401c2c003c0660b40d80d241181c1e40d4110040316540c102c13510450351610f150900301000100d022000000c2c09100d0003404020000f8900041100c0070364480151140c1000d4150724200d0b00442050343c4590003030301092880e42d540000303e00600c0c69411400000e2440c0368a0030995034941d001c2c0042c1d5180741815000c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 36974258 1250 36973008 36973033
    0x20a0b1b12090d030c0f06060311040b03010902011b02040f050106030b01021509070501080403170f101202060307080402190311010801140a06030f020c0105090d090608150405040c0503010207050a05 87
    0x2d100752480ca50708641400202d40001c1d120303c0b5200456070040c240024500320725030b03401c1d01380c55181d44251518080d024100c041c0c0c0c5010f11070246100303821002004111440e50011301200e1040601489403c0c2401408040d5240d1750810400c480b1083e100b00400d40c4c49140c003400511090290500511601c130300311580151145480340540141e000802c2400d140400440e9034210042013201001248142d4a01042d031904809025904400131f40c1c801c1e240002012100491507445007042c1980c1030f9040c405a1036050450b40c000c1050716048140341d440c0d0000c507106400c442c4440c17021249800380002884500701c84071012000982c3c44500c0c1ea640c42041c810000218181e00d6448907500310200a1140254400001c04256440140c10800007010b81030844404580d10001e40d0030018103000c030f055025012001400081c1044075083c2400c82000bd03100150200050159a40b01c000c5030520110140e4070008140040007555115000e1074403540b2140c5c00c0008640070301c80c00214414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 36975508 1250 36974258 36974293
    0xc010e12040b0403060b0418060903180e0112080405030f0607030b0907020c010806030712050601030209070908060a0c03112208070506070f26030910061a0304020a0b1b 74
    0x1c4a100c2d24036a0300b0503086031034550042c28001744103540540d8901460350803c90401e07103900748038000c90b40040d001c030316403c02401c482c00ca2026202030060319031041c0030082d42c032511030741518400180000100040d00e8801e84600c216080f5070360500c02e6030007500321360b1070028a9910400c402d903018481c90340c084040c015104000d039203010142c1c0124500c88c04951107070707518a9203e00d000f0126443c3c1a03070b868101400d8192188152001c0e00013000600640c00e2140e4119000030403885e005428603c3d00c00c100d52680c8002c2e090034855500c490015050718841d0308521000c25006801d5039540b000103400c1848480917076452035401024080008106c50040b680f98201c07140a001c41c0d10341103480d52881b899401950701207811610021030405120100da801618004107621216500c0c10261602403400a40e1003410300200c6c1480000d100f8050004800303410317840b6601c01580c407507c503840001c0c070141c42c40d004910368080120701c0c0603c5206a24003a0324074030840043e1407016958407004032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 36976758 1250 36975508 36975517
    0x3120a030b040b0105180d12020a03170105030703080a03060b0310090f0b0306010b0d0207050d021e0604080702090903090405070e13022706120f0103020901080d020703030e0d0501020c010e12 84
    0x60100310144844143c0d56080195140510001000800c3e107c04070b56800e480710000c410309030016030204074031604050f00481d91309100780d000d100c0c41609600d040700095071041c140c00010208040420150f016074020f42242e405010b50102003603c0c0c0c5030400051800801500c10350b000c040c01c0420000d0240eca0f8484c00303080d128050080c0005038280590038107240e01c40f25041e06103681c00c02080020030380078003001e20111804e501401c10800340028a01d81c9816403034441c2c0c0f46400035001d200c002140070f0b0031201034903410745d0080742c640c0d01c0320403107402c2d4003a122038260081e0425081210081c0e00640c240044081102d61400c210f0741012400c080b401840609440c41c1086903a0f10321f0340504490409104800400d071924200c2100701c030751030030003003601c0b091500140030005200f10b14015040c2d5015140301c9005060f02c2080d200020343c2c07855940b0020741480700030f81c41c010b0b0075124011444605500200295501c01007021004d0081070a0001b80340c050080c00b5a801040c40f6404c12078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 36978008 1250 36976758 36976781
    0xd0203070e090a0e0c060c12040b03010501090b0f040311040e010c08040312020906071b08030409050108010b180a050a0b1005070b01050109120314091203090f0102010519090c0503120a030b04 84
    0x300070b0500b00005020740703a4001842c03101c03540f12303826054042e060200c0c0103001804001615548a514190000d4032544180c1c010014040d802d0040c00200031b4807034180d8089903007109090840203c1c0d5008640240458900e802195003040c80c400350304c41d080032490b40518800d5442c036044020900d41d1404074010303600400c1d4080d03820000c400c08100030002020b500600081c086080e26076030040903155500c80e50040510383d8850300100030640f404e10540c8010700302903407071079262946d0440060080200500a01c011581d80d008640711040c0e1340e010707d1054101030408401076180800203465074001440440311040d004002141c1944200841011501c80c22002d5022050540e03090758400c181e00174150700c5d1039043c44041550758417010b090340b1410310040070b15644d050120902000000814846040d0381c1040280316800844491682c1c04481e901c0c000174044082e40380880c1c043c0c1a40d804241c0c1885540b10b103100030070700c24000f06400c62040d1400c2001d0b00081042c04103a03190115070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 36979258 1250 36978008 36978013
    0x20f0601150e060d140108011103010b0702060c0c060c010b031603050c0607051908040915060e190302040207050303060a21031b0c0b09130b0607030e0102030d0203070e090a0e 77
    0x40600150007050b090640000042c805420206500e07401d034104c480e032002280000c00250010040c4a00a00c0b035003d511802c0e540f014074543c103211503941644103100b8000d000b0600010401c40441040c006081c010400419685d0398851440f801400381c414140b04a1080c0241e125102d201e0030313200628070889501102500c560030b8894100020b03500301c4101a56540543c10140f94240e1070014442070b0316201d40c00c0552140d0820042c00c0454107074100f01e070070540d005101800926000030f91081d0130001140c000704d10160031ba48401d01140b8036800250018000f00c2c0d010200030002c00030398840c090913500c5060fa5a51075580c10310466000c1c007603134122102c0d400322001003441400e41240ca03001c5807140000c0141141c2d01d0b010224540e40c0080e01080011540401514002e10101c3c2c002007082418000c00080c0400500301d0721403c81d004090000a0a40113601d90090082c0d0b0104a03d00d8000c646a1404c640080c2403140c840c10b020340310b010f036080050350341e201c07a00c62030305a085130000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 36980508 1250 36979258 36979289
    0x1802070f02060a051201060c060507030e1e03070203060a0608010b151611100f08100605120a18050c04060902070302100b0604051011010b0d03020a110f060a03020703020f0601 77
    0xb4824180e02c118900c6007009410485c02a0000c01403005074000c010303994840202c450582443c1c4d017140d402624500805007050b1141044210008075006c58040001e020360308401131616a41ca1072245d0345000350140294410400c0540040d40000203c0d07600e0402403040b4001c1100b081031032100c41000c1c5480740820320110b079901e4404d0300f171440c100d84948030400b6441841000144e0450400340200002003240e82e07108106a0700000c4190003070886001d20200138208100130f065070017520b444400c40740101001550012560700040400d1242c84c03503400302d21801d0300304a501c0c0c94150300054001c90900d00c1c00078000000d0b200301d4890b25015405452000c1c007071804c00014044082450307500880c00d00000c40c8581c0e03022003c3d070614510b925100510044070311202d00b550140540184100401820728000c281c001c01c1e01280e1680c0000c50003003906809001481081c0c0ca00705807504050086400780b0031980550040003024042d80071202c2401c000d030a40c0380d44090902900840003030150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 36981758 1250 36980508 36980513
    0x302030403030c0c0504020408010912140d0905030409020f040e070c02280801052e030c15050c010906051e0114130908070302070e090a03021c020a0204050903041802070f 75
    0x2d040f01142449040351aa40c0765444c00010f040e60019041090180d5413040b500c4100318807030008030400c107140d05164082c02282c001c043c04038010000746906198691244a0800c4006d0003141d001d000040310840d1a03091400406240350042e0250805500720305011481c01c2d400f6039207520300707036030700070000008400400301032110007030040c81842e40203403c180e002c1480d41d400c1c0201071040004140f07000c5000c2914940420001e800680d9240703a04000105102103148110319400360341c85416030350744c0410041c804580c07038454450b04022951808000504014480e000300b40030303000705400c2c44900024003001c15101d8200b8840c1070300f9a1100c0304040da180c10400321824881030706210004c0d03a05056110810541c1c800c510840068000701c005205603420004d00980160801005040e12140d5903806035560442500b915450600d240490455031310070081480820350140050140d42041d003c0b40f540d9802034003d10040c640c0d8403180030f900402034402d60f007c10750070808a05447050a078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 36983008 1250 36981758 36981767
    0x20c0a14010201140a05060406052202090114071a010503010c120b0d0204060305160b0a020a0201031107020301090332040b0f12010b0403030210020702010816030f06061e0c030203040303 82
    0x149500d0540d503c816039864000c1c4e038010b82a219101c003107400308161526030200802c442c9203800c058882c6034640c040445012450040760000d0821480060b640d100600042e100840501e918060011340003910768100940f540040b0b440b060700c805034001d1640c071802054240d078540c900000000d0300840100201007502d0300300d15544003010382071207007203829034001c03606413480f0740c1007030399184d00050b1180d001c10110340c8510010030481c0317012400c002800720001e44034555620080d0415455180d0070050482050440700c003d80d005008009840f105e280141001ca001800d03201c150003855400144800580103000a98034103a400d02d2030141019900d80107a000381440c4080003030144803000d4981541c0a000340a0100080d0340758803980b9500c3d00a250000d810301c03011086005000c03a80c0140d801c03041711900600030006014855599030030032401015001c5e501c3c90200d00384900050f065812001024441d4075050543c01c4a0100c078405565516000d00000c005900400080001c02d114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 36984258 1250 36983008 36983039
    0x9010c080c011a0901060201050112060b0312030a090b0108070602151003050f06040b060402040f0302060d151401020c030d05160303060b07060f0b09060603010603090f02030a0f03020d020c0a 84
    0x8001003424920034840c440c0c00c4035000c0780a0400080380f059000075610301214514018101840240400d41c10301d45200700060015000400312502c07072442009581e000c0c8060006026400f00d40c0380c481c5050b41000025000ca00000d840ca0402da400101e0141d4000c034440b0161041034000b8900d2000302400a10140e074020450700703042418120210000b41c06108188010407000c0080c4828103060500c0510170f40c025200754803980c4104070400006100076003e0048980441c3e80c07540303540b20307035038020054081c1c1c0d54042c5420290034408520441181c412141c02031003a4215100203140c20181940d5000d04a03211010030014045040341545419100d00c5541c403e02d00070038643e50300c1d02003500607000000300f10303110340d121001c24400482d184a21050888100c807540201d00382400800d04d03074401030044104158072600707500306006142d060610320b154050700f142c030a00c5032400d02c00b4102402e40d00c02c800501402c801c442846200042544041e04c0090160000c01c2c40c00784101004c149 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 36985508 1250 36984258 36984263
    0x50a0b011d0a08060901050907060903020109050402070201020102090d05011e02030c03062205070806011103090f061b100f11120609040201140d0b10050a02030409020304110607110301060e01050609010c 89
    0x11070030b000f140400d014000c1a004449480010980d0309180d01890300703240f195048002006032600b010070250b81c0c40031094040354800e0f40c1c010303542c0d4610300040380a4071039000720f0303a0800284a648001c10005511a40300000078204014041a00910040c160b2100360b0761003503540030501c0031440c40e1504165503402601041d100b0980d20381e4500b098000d0744e004075885004a200c81d01000010b50f08803401403821215207000c5c5192501e941e00040503284050452400b4070000706400600c841d02c100700780c00c4213044801310f070b02401030031000784081d00d040480f60b20340c0e07030403c4c0d8081c1000d4030f010305032140008140c1505965a66a03003d002c82d1540c0100260b040164401301281c061150030000e0814840145c004a81a102c00d802c1c00303d08000a076020007048002c210602000d6800300582d070550f40d003804051307a40c2d200d41c01e06003a188e6454140d2a070040000400c0005c0204030b104491088409800034403c2030754030007130210455400d00c106500100c0c1001146003a62003030383d03000c0b0700b9403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 36986758 1250 36985508 36985519
    0x609100306030f0b090d050c1c02010e0709020c07050901031e021903060c0801050a150305040f1a071202040e0c0901090f060203070b0a020307020307080f0f0706050604050a0b011d 79
    0x107640c3e495405040d0080c9000381c90b1105100144840c1840500c40305140900c21301b0400d05d080b1402408603512490240100c41e000b1102401c3c800d040e1003900301d46123001d2008221494103880d901858020360003c0040c00310791181203000074141c14170016080c100d035000048401e02000034000300d4142084c0c1c9200301da0200103410b904401152103113446002c1c5014000002e0200a815406014410180c0015200b541c500303004000d66007a900d650707082c5070001c2c0303000310f80c03500c4a18043d03004040341d8500030070b01000e0017481300303207101090912071250140342c0d1401c202c1111224801c00b2445240100448101c5107000149081c1680b0b00034a5603a02c18034000003515603481c07418142042582114005801c000348283c00d1010f40c99509802c0404900c045140d03092888000e90b40740300c1d965000f84101d001048800600c4120070507078040160306a036541e40c404140c5800c0004002c2285c0b6584240c1c68540450f124a455129010342004107840341d24044030401c1040081005140c09542d114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 36988008 1250 36986758 36986771
    0x5150d05070b0708030105041d1902030709060806190c0f1d0306091f020405030604030e0a0b0a08011d06090103020603060301090f05010e240705030a141003060b0d0206091003 77
    0x140141d0b0010488a8001c060450316541400c0410090303c00504081c0f1000b14030490440159501164498041102c0d4140310310344103ca1000c0303401c0680030b13404511003602e05880060795802c0820210b00c01c240500c20380350070341c0c80003203000211415026640b0000751030b54004180301c0c1c040c5031880d11440c8035071100a11030f000c0300c0003c0c0c50444111a070b00000c2c0c01000384e0003000103401c01510800c1c580c0002c00d604244c20140420307034034200104081c0420001c80c500e0034003078849000300405001d0740c0102c9680c5a4403400d025042100130301c54589103c0040004814850041ca28207004500042030400a64030315020004c142d0406050390307505540e41d000c100001164840844030f07042c819800819410190f9100718148804109040d505052440d0340d58641100031421035484281c0d824901e49a03168650702c0340081c00c000b00500c02c40034141c001e01030155070f000c041d034049912400080c080b00c000170042c001d40c01150000290421424071812003070b803410f0180c0b07040426080c540041d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 36989258 1250 36988008 36988019
    0x90a0302040c0e010801120819050c07140907030911010c02040f020a020a060f020310030303230108031201062a05010b0303030106120501060203120c0a03060f0602010c02070905150d0507 82
    0x11190900d03000808a0941c0207503403c6035070072850290040c0102c0c00380d00310910b010307194150b841c0304001c141036180e140c91045806150041054628020924007101c2d00a03407211180d10024504c00324080c4035059960000d40b44030f119000e0744080503801008500000290780040d2860050480101d901a4680c1c00003490800703944040c2c040d003031007540101304112141c103048084601d149040d05040d8010000c010792001c00d4030004040743d60510300000c0c0c60f22483c84003215a0301e140c0c103001c1c102200f2400040c10b4074002001d00650f08030301c0000407407031340c0c1c070307103044e900107070400c40d1040541c0711103544e07480c2032615400c400c405034041c0c00040b44000340e420000303040d54000d8005001107400220f8103009031885101d01303809891180025031034802140702e2581d040304010302400d823002c2e0010350012654401c0d04a02c0080080000c00c0e20700c0c603203841010b4080d00070742d103030030005102c1e80000040054941c00b50502131038544140c070801007020814042d000f5807400d4203a0392446100800541c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 36990508 1250 36989258 36989261
    0x10020a0c0f0c2c061206010302010c080c01020d0c02010b0a0305120c0304080708030301080f0c0a14061201060e030f0a17030403091505090109060201091a070c05060a0b040c050408030a05090a030204 87
    0x2d0780000c5600811580c040803004120f6404041c22103405440d04030130380740c0340880004d1401c0c103483e02424086a1016145460011485542d04c40e070200c1d40049960803125006800045a00384135400a0040481c0e003410320440b05a07034071003d0b05640c0b0030740c0803d4150316541c000740400300101c03055900c0d040c2c503241c1003032420901c2d61200311583c0c400001003210003002e0010203a6500300102419a0200820010b020703982603000d01d00c1005034900705100f0fa0742e103c0b401c840074298040b10440c65982d41d60005080210050105400380c0035040f005041020003065050039185d01044295048540802a040c02e0700028011418400400c8001c00c0040700031035220194185035488aa4030740284000500c000940d500440c29603050410600000301e04000e410a1820351118091940e541c071001211201c0c0502805003131801600140310b42120396030424103c95005840a1004c80480b14085500d8416841240c0e5242c105100340160700d44036500805410900615008010b91203800040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 36991758 1250 36990508 36990539
    0xe040b01031101030b0a0828030f030507050403050607080a0e03090d060b0301090c030b01091407020c0f0301150609030c0f1203080901091202011e0501050f010c050106030803090f10020a0c0f0c 85
    0x4820b5840000d4a8494020b0402000304248d914000c04040b10007030368005d89800d08041c1c06809060710307607000403070b850310178000da034000c50700003040301e19900701218042d003110416601010342c1420310580b8040144000200c0d071700b00e0009400d40c0f903480c03500d846000080c106150060345c55521a003140c2c0106800481d0a00518003c10a03a1070035490f0101e68403c60304511903a000740708102081003800c0f5008120591501c01c1610821105442c1c440024010120008400604412035001041b001d51061030301c400c0e2481144d0071300700300e501c811036039a00307026510803841900041030f0a180024400e01406070415940c00010a0110080e41c0702e81c8068402e0451400603035446861400000082551201c0ea1003038174010030280d4140008101c80c0c031000c54030581480414441e8108110096000000031600f103410b803616420140d40c140d454000000d0301c8103c0303200b0b91302102070000051084445000e41c0d902c42c074005070708654600708483d600e8902a100147c1e40940007414002088800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 36993008 1250 36991758 36991769
    0x7020f090f01080d0f0e010806030a060608030c0c0406030c1a0c0102040603050f060915010c03140408030403020a09021201031e0501050a051806061018090c0804020a0e040b01031101030b0a 83
    0x101e1141d8188415a8a0301c01800710390340400c152014030b1003243d0342060151b8481c1c44d082c80e0040c01d03a81d0b203602082c42c00d003078038800503e414500100003840c80e0340071025151510000081d6001285004200000d0796131034000a010b001030b2904c10003203980545030b0b00111540601c82075003000039020086089070820340c4904080303501d840030804804c103041703030165008400311014800c500304a07030100005040d002001d0305010110101105041c02503060440300000c1144042e951520750714010f0312a001480224003500a056000c501104540262240100108904243caa2841e00d6100c0741002000c000300c11012341441800109a0038040c0c14802c9030003100224142c1012a04010000544141d1004a4100380e017442010b070344400502d09540d5080c60103e4110014150303a00c0302101560000b0401d5240140d00d160190700905194402d41c02110600303013942d5a03d801080d51142100c0040c0000c0840c0b0042c00080d1303007081c22034040c5906250016110204101090313980040d500407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 36994258 1250 36993008 36993031
    0xc05090405010503030c2802090108070608011d0402040b0105160c08100207110904030306050604171c0f12020f0705030301080606060f031503240a0e1903030207020f09 74
    0x4004542880e000d06030042c101613000318074228980e289283c68892400885c58002800d684144c4013601a0300c01619164000304031050a580d01c2c0b02c203640c0e1b0f918902c0307070801040300b8100004041200c141d0422034007815469006060741c80380e08000c01810140030050501101b80034000a9803961400501210b1042e4030800400303080c814424940b100440b00c4448003401007008000040c04010140030318481990b807a80310340c60700d28041c1c019259641009422030f90104000400d122418400c1400790700350016654000220030b200c0c3c0032840248106400300302c11000d0108020b109060040c0310500009005040100c10480c0400360b5108030400c0d075250b403000c00140110107060000c250050350894000b40703440704c13100001d0346601004003500c0341c140c030940641e481910300f03100f07001080c801003041c04010650100c84240c2c002041c1e0728600340341d1030310688100d4010000369802800c54195034000641c00241e5048020b540a08000c0360040c0001030040d18075184e008100f4001e1451900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 36995508 1250 36994258 36994267
    0x60d080301180f050702070306050402120a120306050a060e0108150604060504170c0d140106030203150f070f08150a1706010e070302040b04050f0303071a011508090d030e0a05010c05 80
    0x48060542e41d01e1090f80c55168030302404d00c049540c000032240100c1e40c1c091008550ba5446000060222030780429106880c0105001c0000304035100d006145100110384003081036940f0b4070f0a22440307640600845022440b14105402d4a601482c00903034065006514440400d6205000c00c049400c1644501c021443c04581070011001c1e01d4040702c2c040b00818014580501e000c8001582c80c0072100019040790450300c4400880038082d00490007641e00074040320302803a0a0380c0340f86c4020702d04030f40241d07004600401051220b8868100100c2c0c2418aa40e0305d041741d210315421600c004a003a82c0d407680688902e03400101040760f071401801508c2e110f00680702c258540444c0120940009000e10f08252040205010040c4901c0940b401e4640c248da10540031140303d4007103452b6100b1200c000d84104404211041010f698400d1541039a40050180303214000041d802e8030307011030030364540b0340580008145000c554403070b5118410310300c5800101d80e051034407030300c404c0d0844227403880c0b07003000540024 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 36996758 1250 36995508 36995549
    0x30f0e011a01020d140301120510050f040b07030e100203090c130c0201051b040b03060a032001020c100c0b040503120106090e250c020103020d02040f0509090109020a0e060d080301 79
    0x4110604c1908a00300035101c0f080c8461010042c0c48140103020668285e0541c48051190030408060644014441040942080034914a0380c1000700c1c1c0440c1d0603a01d2100062039203119005524044003960010281410813103402000f9400042c41130f159441003500a090f5991400c031089412000ca80c400240030f80030030300003401d591004101320300c00c05500c41d9296104201c0c508a078110342d10181041d441751524400a000c41c410b030b03440940100100790100384503050004603030461500907000c80c2e070004039076024000c0300282d2050700e00100f49102e4000d4041543c0c05402030f4042d104005403450724120112401341180281c01c04000180d10107418130116988030311040d08244d680c0c4a04003115003003c80d944003031441e0f0010508000c01803041c00c0c110390086c0c0640d41e9900c0805010764849803110101c086500c1c66205a41c170982004020403950f20b0103204000c0e0b00c5401900712010f4505250010041c10405061603411681d00503070000810078a40c00340d8040c01405801484101121 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 36998008 1250 36996758 36996763
    0x703170108060606220f0602010b04050f19020d061e0f0e1003060b0f040f0b01020106090908091017040f1b0e0105040903020c04020f04030201140703050a030f0e011a0102 75
    0x160060725603548240c0a0102c40c3e91008251201038481da09400c003010580f03551800708808960192591042e0040c0114080ea0190095403141006071810446a40c0720286651480b0043da403000984610075465a2030522a8000b419418a43c14005c01c2239030ba12864404988050690f0b40c2500010400600000b00400902c400a10801d140710185040c01c80013294440f0035440020000740d50f410203080240c82d003103102400000000c1c410040c55407455800406004410034060042d444d02d0b6000c100c0703400d03034800d130003800d50001c01c2e850030501030780140155072400c1c4006000f40401004040c028800002c00d86204510480a002c100c0c240d07464076094203034404407989025814200c081c0300c031231443c5542e117045590441e40802c401040b82000c0c3c0c1018495080340d6000783c00082c0e03010007402d403140284110783c404c0c2e0300c010140c4203800701c901142c051440d005001400801015002510907005504040b8144d84006144503402034500d08640c3c00e407907844140039445c42035000355a0103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 36999258 1250 36998008 36998011
    0x3060e0702060106050f03041b03032708070b1c050a020d0b0108091005180102180108060a0b03060d380702010902030a17190518040c1b1106070317 65
    0x900080040f035040c040e0151140c028004c0c0140c0f8010003200203014400354880d681c0810148168080701641c0f241030041051060200c019440030000c40204204400078074028200d81c40c070300160041303508003a14002d256000300401c0300600000c4c0d03942c60f00410103104550003250a5480180d42c0d546040c0d045054502c8101e10740c0c103021040d002c0100903907004c076030000000650500003400381c0c3c07840b1304c041003542c0134010704201c2e40c4045400d104d8804403401c43c1500d07207802d880d5141641e42d280200120a1440c0c01641d84221080c00490081e04110a403140c8503403107035101e0701d18841509180d00f003800d0101040006004a100c5194142150340151608421a44000d2111900c40d8000c07035581c1d045044000e0591400b415521004015841901c2020b0505140041c40304150a0000c22541103c0f0031540c1c1d40c0070038070f455540d80c07420748920856034034203840d0200c1101a002d18076117041007405c0280d541804910710411140c0d40d02009010240c46030310703100b003d55007030304c000e4540140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 37000508 1250 36999258 36999271
    0x1e040e010b03010b0304170f0a051803030301150806030703060c0201050402040c09050f150909010e09070b19080901090602030a150e0402030a020907030209091302030d0e090601030905190303060e 86
    0x500b08010b00581a600080301d60168102c1ca800d294107101641148452180b0600c81000c007401082c2d03405001d80c400001c1058131070b01000c000c0c0103140d850805449100c2885026500c40c00c0c41104415140502441d039401503006094580d1540da0743c40700d0080e03421b11344210006035516030400c81103103480e20800d00b03911141e25000e0084d0341041c1c082080d10700c4907042c8a1240d110505a40300c0c05803021304441c002d141c090b0001c3d0a559540c0d50240d9020307400c0d281a2180d001d480b5001c41c0307040e8a90b044d2000126482c40d502100e07000c00700c003a0b440301c0019041e84680d54a494086011603002d0001307501416241c8000601d6005496640d44d000344160400040140d4445c00e110140e600007038404806038040387c4440b131a07160004264000e00ca18804660440002410405030103041050848424000c1d0300b80c59260340981c0c8122407208000e1000e40d8003c04480100d05513510075406100b646102e40300310307000c03083e514403600028444560300f280020703200c10042c4160410108195000784 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 37001758 1250 37000508 37000529
    0x1005041d04030e04110405060c06070807030b0a0509060f0a03080405010e0105041d2211010809030703080c0a03090503040b0403021002030a020c040506130507020f1b0307030b07051e040e01 83
    0x910755402003a034000d0f280c070b09109546554058090100140880b0000d000c01024a0707918401c1140b201d4444208480d50004520b80b00c002070b412601034010a40001750080481002034140030422800354000351065411407000030b0810415112040300d10301450188071071940b10351514000502c500c0754a50f445e0304110041c4020885605d040d403068060711030309442c803401603a80f01d00045220030b4984014507080c1040402070140988001691502c10082e41d4001d840c0e9030382044a0f40c0c0380704510001340043c0c0020000350001070b00201414000d41507103808205252540c5410f443c540098008090f100e10000f010011403070080c8404800f85003900156003846401480030b074646e600700107828000c81d00c4500050095a401000d0070001e403007804e0030402410460f82c002d664062618103041d90b0b105807021050030140d445604840581c000300104155802c1d030f900c50300320384806020b90003845014400d0100790000034815144041465040c0f5031aa40740a130961007544040e4404400e10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 37003008 1250 37001758 37001761
    0xf0b010f0609050a0b1b0a03051201140f0d140f0c090609070801140105040b27040218060706020705011103040302010501060503161b02151e04050102030a11010b1005041d 75
    0x113480740f500038800c99821910080c3c603904d100e1005015040d810898283c10302035400110101a00800a020308101c0c910180c0c1c4207070380703602414076203244010155038081070a414012042c40c0a406000000d4420824010071404580c0000c2c6400c1e03505c10025a1034100040281c242c1c101401019400401225403916a003080c1401422a21044c0510001d00d4100c04040c10944d001c3d0048800800000403003503a80e07881c550030510640e0101d1400d03200b01801100382501442e290094070b460012090b82814030120030303010072400e544806400c40312107400b0b000c0351012920a120307040c1070a03142034445030351789001d180007400c56905800c1403042c00010320030b010301c0c05c11101c0b0b00c03810407030141000086080617031481d5800b0b20307121400a5001070314212014010019001401c042814000b0424103814082a100c0c9140103034090540141d0041c40000f10040c4500e02c80e808801e40340e40000b40d0b04445e0800b0404000c26451410080340f000101080181600d00000489034416119010b05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 37004258 1250 37003008 37003019
    0x212030f0f070e0907030204050306100501080a0b040605060403080307080c0307020601060e030a06110d0b0405010302030a06020306130608060415090b0403050f1204060c09050108040c120303090f0b010f0609 91
    0x840c0588038500715450200041c240d58020903824010b071000800201c1d00d854a02401030181d8041d0144a00034022407000c00c2d01104c5440e00642079482c1611007030490364603000e4000051544a00441c0d0080c0c82d0f032b80024244e1a00c0e0002c0001d180107440d181c0d80d074585594060982d60000d40251340c802820020840d81e1503010030700d581500c0c1e641c40c00c0301c2a450010300291a194038004083d05c20346c0703003000300c6001010b080c1c010042004052000c1c81582201005c1208035002480042d402d42c00640f00400003901d00e42c000d560151340200010540400c9110580807510b071900190507c4e4170400610052150101c0e20320000155044240410509552003541d152800750008090006c04a00030a6006042090b6160400720040e04902481c2038101900a070090028020101d050800c010443d54071450b0241d101c0c540044906401070318003144401c0e0306580010503030030140d1b00d0b144040010448076281c140e603401151542c409506104d950881159983d00c800d06104c0c040408010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 37005508 1250 37004258 37004281
    0x8040b010315020c011b090501050703120c021504080901030b0d020f09040305090d1b060801080303071101150618060201050610080402040b030303160807090f03080a091701020703021203 82
    0x107407540045505580e84000742002c020b4040c50035441060350a004100d402c400b1921944c3c12062040d50f1070414159840006450078465994003400161107820800d45011041c6c0089950700c6940c411200c151011400100000900f90303800c48090b10001955440b0350390600480306003440c02c88011401030b259034009880c0c01440b0809030301810a110014007810701440a030703102d03040040d0480405103454541051402c0c9000c1181c88060388004000c20b015200340d50045c11303244800011840c5131540f4100b62612111a14030550b02d640724a880c0d4034400e1000840030051406484811700642e84001d00900380c00d240c1c126a04681c940030400401e41d8a100c0440039900c528244644035446d00e0000c100a4640d40d02016054031000060180010720031460b1914080580d640b4001c0740c85840c6c00f00d80b03041071440b400b000c1170003250050021800e108020b01b0001060300309101510340d54988001d085001c107040382d4413650b0200d0740005040c0c05000c140380d07101040e04041c0c91850304030242030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 37006758 1250 37005508 37005511
    0x607030c0e04091b0f0801110408120c0a170d0c0807020d0e040902060301060507031805030304092307090501020c03060606031303051b1e0a12080621010504060c08040b 74
    0x1807007182c46011074010b001c04600040800b84c0803540d41c00e501c2d5119803a240c5590820310409215618141c201d40726080007201340d50655540c83c000d007200d000800d03d0100250000c003c5200140207540c00c3c00300240250700ca102030303160a08a01a140d0a010f03d0020450302030f80300841c1402074580030080d8890b0701080c0c07107a08448504000e00b2100c0a01e011800a2110a50082d00318030008008101660800090460148640c0d103141082c08a80d47e01c203902065032042c2505030f4070601061000074155000701c4245400303030003018600a944e21a10301450000d42d0725002103030459109110550b03040c080200140c206600801407410048045200d0f4440281071034820030a6a610b80c01301803040c0101d4104000c071035206903000e01c01c072043c103032038072100071030350300c840d006542111140712000c00d8402000d9000f06802440a1260740280c9001d40c0040c1314507400540f210600401e40e0400900e02480c030f049000000d02c0e40307080c0c030703081c8101c0b401901d000003800381e8501080300180c102d500c00d9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 37008008 1250 37006758 37006787
    0x20111060921160b0103020a050d0c1802091009030204060803040f051905060a110c0108011805060a181a03030702100507050a02040e030304030909021317190302030301080607030c 79
    0x103103224103401c40c44042800391083e00104141000f80e40c20034810344000c5581aa8001c88400c01d480f0b81d924100103c06c250b4902c000c02c07000c50b0140c10424094100340410400617044005407038101d079440080c80e080c1c0d0085c1c3c4100407940711502070096051a21447c4023600503280218509030070302001c141c0049076403007400c0c031841222041074403015500c0c051078010000904129220903031036101501410307000080f52118810902da1010642c494000e180c129049074290200d47c1040701d2078000a480010182034100d540303010f0006d00c0e4240c8608408880d10511000120400f59041c0030102200f44c00302603101307520900041000d660380d4100c00d2410403407810b00c19501c0c04c2c03034940b10707003041e80d4001d0295000d8500342490507214000300045201c0c920a541d880a150740f5040c1c3d01e0101e0050b5030455400d200394820a01440900c95103541c1c49100780b408490039400400c240004140c040202240140c00100040007440e03810010710390000001d003820700074001c20840040c455246040007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 37009258 1250 37008008 37008043
    0x230103022104050106030b010b031909020d080d330807060e0d141b042004090e0a0501090606031205030702030f030a0207050703030201051608060a0e19060905040201110609 76
    0x2c5420000250b000303030011503002d111500d10750794552520607180c004480155040c401c018800703686038014401c01c030000fa4020800c203461600c64507298100d400c00f410300101550f58800711503079000c2e500400c000d442d4003418080c503a00b200910200c071342c41d001e07842014280c0c404c00342400b40540000a9040403030341504c144000c2d2401e4101400700c40003040414a16001d880d041c0840324058002c3d54a039504140e8050140700c0b43c0006407110203009036587c40307400c14103000511170031049820005130012000201c5038400c0540c0c80f0182107d4850f80d007180d0940d92900c0401c20402c001c040321b110000c1c903040c11401c44c94904406512440b4030030710340313804e200c1c0040010720710704e01541502c40c85608401210441a2a0f1502900811040c1c1d02c11145c1d0f441c00f003504280c10701c150059882442c01810328007641c4e10301400b40f98203000180100f4511b094825031000500b14134485c0900900e100d882c0419142810b0001410031100c0c8080d09085030800020868646400240d02021b40b26070010b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 37010508 1250 37009258 37009261
    0x8031308070f03080c16080d090e06010c0201030b010c1703100e01030b07030902010908030c0105180d0507080717030405010b27040b1009060602010f1109010206010e040305040e012301030221 84
    0x281703581031085140b1419440c3c1052030020644143c00035100000e11400e441c0c07000da107620740031260345c01042119400c1c005400c1511000041d4441d41040c9105c070018100880c0050255a402c419035500c8203e98400b10008001c100c8400c103a80403040c020022a09100d403254199180c05d241d00300300414150606031103210703d204692240110310f00600c0c000040d603840e22a02008a07000c2c02096480d08a004500c44843e0000080800c03129411b030056241d0a150986c40d9803209004e4018003c180c03240c0c10355962185000481c48011403040c1d00c03d0000040152041042025a1030074805c1d1100f140c84210b58440c49031408001e09401640004035100259146e5055401d200b040340c11140b280342c140701c4c00140c040d805411040380405222000d001c10000021114014000e4610186c010b03440715004008003104519940e8010340285059443e05440d1681029056400c0c2d000da5140504807601094101808141122042c02442c00354984141094941c41035290022181c4081c2000740 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 37011758 1250 37010508 37010527
    0x41703041506170d030b0a0303080c0405030307030c05011a0a050909120a030c02010612020907120209030a0305070210110304050f030c040f050601080c1905071a0108031308070f0308 80
    0x4280ea030000240144009515143c40041101c29080a0ba00c2d40c880d284000203464041c3c05080549103010b000c64848501c2c1d03032401c603002500940120b400340002c000c003061584051004140081c00380d101c3c11010308051a01d9030071034000c500d031110582c514040041056032040307620011a88100c07003800756520b07014100c60030440a00c2c06207090030300000d4030420003074060f0422000420190000c020b8580d50748002a1002c01200000b0762008400000503040e134040d042c105400d007070b91000103040403003010200349400031140040c0d0200d2804200a011842c1004108040c1003040c07600c0b100d004021040666240107501400b4402c03002403940301c9480e1002c00440307081200041060000307241d08850400182810385180d03000800c3d40c0c001910031031610040340c030300100e000030003403030300e0810f400840d142d81204804480040040c0100c4110918a20304a40a80342c02c2c1c000d1695511440b828600e0640c0aa101115a0b04024030070021600b074160f00404507504500e003507560b1720303110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 37013008 1250 37011758 37011773
    0x80112050f0706090f0b03010e060d0c0305191106070203100f0b04111209060705030402012a03020705030105180312100806070507030e0108060916210504060c0804170304 75
    0x3044080301d540300722040080c000c1d07804924001101d01303840000304025140e0541d80c0c00c81c403090003074110341800c40020641d02d040c141c204d1038030a4010400c44001644a0340c40608180c5c0d8281358100c1d160000200c03209120260129403c4a141250580d00d80341040d0301080c1c80d4042c0c882850503460343c907050600c01d0320542d004150582001403081040e00309000d00107405030800210074100103030a400080e030105002a000d40602c9064940c0350950352a07900440d4801c21f419640004034045200c02d950800e03030303280d20303007202403083d0050484103040c003041c1800c42c0d1009001c040f00380744100e10460510310110449246540200e154080b50b603c030420110050100e030710400c4584038607001c0041a642c02009030115034841c0c6d40d0b103400b501140c0c0045507002e5050361500c0d488070b0148080380000191004602c000345c20340c108805100710030341c058002a10000d141c801102e46400030001084140d00c40c142212010b42001c03003a0381080c0d140c010180620001400700550008007090130301442 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 37014258 1250 37013008 37013023
    0xf0f11011107150f0606050d0b060f1206030c0f06070303020d0b030d0203040f09020304080f030a0b0618030f010203040b06060c0c0a090207060b03010905120f040e040b060a0803090108011205 84
    0x304940c1607610002d80c0340000040e5072603024242400c0c03904a0a04101000e401800308507051580ea05040c403032131900c140e0051214201c401e0b80258108101e046800000c0b01a2400c204c000440741001c4c079002081c541000591a0210f2086036030070108043d5544079000c0d07071511901844c0050f1629101d0b41d565004241d03d1507030b44c0d454403c500328004104ea0000003070081c1c4240c5580c1c41000c59a80c2090400d900003075400070a0342d0350500000c1d600c8030f05a00555030000507804081000102030340420b04c41c0d03010200c041e0009600300c2040300c2d07a041c00c201c150350300d0042c10300031442c0d45810340302e048051801400310f51081c0380009410424040820905050403401001d407020581ea40c4143c6000754807120b0101d507282c0c11702012041078601031007501180394002c009401c0c405007800e0341030101d502c0300c02400121903080c04003203040b100a10009110382d12440c0b501c4150b0030464100241d81c0d0940e88001c4466104001c02c040c80d0341d04c9810141100c600c141c06149100e80352410a081005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 37015508 1250 37014258 37014281
    0x507140903011401030609150203040c03020603040f0209160e0d050c091e0a0c09080309030d03020306010c06020304050d0201050619030b0c0d140103060c02070602071202031c020c0108070f0f1101 86
    0x5203d0000c824030542d98441424280310b032008401440d12000d143c2c0607400126809002030003940420000360800341c00455000b41f150304001840740155000074084270044e20061003210b0b445c000001c1e91074004403034040800b000c23034180c441f2014550700c0179a1014031541460041c41108080790260a04051440c4051544042084c19207810b0404400512a1445507000a18a03804c002207100c070200441d5002c3e8405005854041500f0100764080d40c0060300890400601d4800305020429a2001d07500441c49080a044003100b02c0c0c400074251800649070500c03442e03021324803845268400f1641c100300c95000e0300e107890564401c40c00080300c1c0101d60102028a080c4070014550b03440d00e9a404d41038900c01c600802856918050490b520040c900803c000f59002c040700b445136800c100d110380c0781244010200c484207200300c0707080703d600c180d8042c958025a10032007040c440d5603004042c0c1540b200319031401d850342c40c00c1c00308000c0c10a044100401c05104502116080421003900802075044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 37016758 1250 37015508 37015541
    0xf180d03020f070e010b0a0f120c0203030103060f0204080613060216060504020109090e1e0f030f18030c01050a080603010914032a030f0a0509040504030e13050714090301 75
    0x8810305020751181c00060303945449026543e00820692140000203043e038400405803800c3c1019104140c4c1c448480007081401d000c040b24444032201c946000381c6120b41c4840d8080c503240e52452030000282c1d06140031607602d81c1e006000034043c1c0c031800078450707500c5401d2601100b440003d60410600078424600410301c100c0d29100fa03c005d002550700180c2c041c138401e07a00c8040b5142d403148050211806074030b2040d07846d00030f2000c507645840403520b241e628440b120305030380f08000d0002c06546075920000350074201502c046400c100d90544001640c540c040140c003e810300c094141c000800d0383c071480c20380034244050f1001003046900c3c01d40c4022451580a58841020f54043c200302e0350b25008035000c512003403807000312038001c21448040c42c5181d0412100950504017030755040b80b00e50b0400d00f030b044c0800c030381845072000700e0391117015060140b800b9880d4000001108801e1003a10240c06071409003031130920f81441103069101d804045002000300c4c01603242d40c403041c002405030184002810b80c91307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 37018008 1250 37016758 37016779
    0x109020403331103070206090109020f01030e030904060306060807080f030d050c220510030e0c01080601210b0f060901090501030e01020403060504080c0d020a03080601121b0c0209060d02060f18 85
    0x30f260800550244100d80c00315140f035616580d0150982d602040700070f410004041980d40554000d4115059072410030050f64208040705001c20f048950b00d03402a00e140341c68403c100400502031180c1c030080c1060710302410441c00400342190f624880e00342d04070b40881d034500005121040010643d174020300c1c00810300c0780c0036a01d61460207801009024541c0320744000c00e1b10880c203a01a100c4d001c0c0700d01002000d401d8402d804030041d1517410004104605012031610520462820140e6001e0348aa8480000510700305510030b00481d8984c0c0090540110f07002c221301c03405aa00015035004540091801162144a14002502a000d680d000401460801040c4010005814040d00c0030100a2044440c00780c1280340c200e079600b04541026002c20240000300e54036510407103c4004011601c54041180c0790301e403440355281120000510009180719200c0d00861078615420360300020121a1007803038010030b40001d41c0901c100c0f00c500c03410b0100010030004000000d02002a41e000060580c00c61 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 37019258 1250 37018008 37018031
    0x2030d03090507050f090a0902060903030310060f36050d0602120f0417030702011b0e0108090303060310020c010b060a050310050402031e0603010e0709060806010902040333 76
    0x41e0480d05400c81e03590064580100d03850034036030528a803481e402002c086141e140da082c500010002a40c05980101d020419400e04d5101000118000d00345410380c1c10f480d51030210000c00c00c0c41c081175101c0030440210201c0d20005643d418030381092000c0d0491207290380f100c504d08120322840703a1001380c01c4103a10802c1010b01c6401d0713003c1c01d81c06078030004a8000e6a0b400c041d0780d0160801326402000e070380c40c0765003601c00303034a824014640c00010b41c00001110f0400444021100d1419a21040002c10105124119503804007016401c0384807040103504604203000000e4884861800c0640a95030100b0707001c10b11f0700250040240b80b04050a4140d030b0700d03584000101158022207440301c2451402c1c0000500b81000e108491180c0d00c2104690340a940f8102c0030284a00003400540e85503490342682e10403e40103000c4031000380600c840000b849890280700b181402c030142c3c49070a1042c0305200410100321154000c0154030f5422056041e2080070b1809200c2e040c645060841c405883c2c2401b030b101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 37020508 1250 37019258 37019261
    0x1f0203120c040e0118060803030f010503011d1e07090203090a050d09050d08031512030a0906030501030506010b1b030f0d0b03160510030612050d030c0503040804150c02030d03 77
    0x940298106810304a41c0c1d4400703564000d108621851280b5034034072004015400c64040e04900e5544108000305001d07a9402d00b09285800a41d00081113060080040125103004d03c140c0480c0343d0080d10301a11036501442d110f869000e100503480000465040b003205855050100c8800b03480b042c20215100e0a003442d0840c0d031180308050896140c8644941c5500c0c103400713116510200c071001080200d12440603903c1c2000e5030005400081c03500850364517060f0a0740c03946041070012011000854946c180c2d03000007000400140d00c2101898506070048c00480c40c08914141034400c0c20f0351295441018515055a00400301c010500c507000120f029000e4500700001814011125202800f5101c1d80000f0103403200401c610441c00b041c00d101041215090080d21100380c110a0704000401e59a00d440c5084a0b12083c0000c1b11b65400001c0c0e5040001d41500c40c516007501e552038001c0c11440c0c035903100001c9101354056004100c0103d802c0a0310a07101e0115030380d00d2a4051701751551801594400340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 37021758 1250 37020508 37020517
    0x30b03070807170303040b15180708040201080a0603020d061112160201050a020c0c12030c07120c08010605130216080706051501050a020a020f030705041d060c0f04050f1f0203 77
    0x1d00e03041010b8100c00d0f800200109a900840d009020b11040e070300c54030395484031103922901c200c0e0800641d40d45401c105043e501d001c2d10815640c3c944441c1c51825100040510ba4000d041e000d010340b030b04405002507115a0440d20f0031075801000080d160300c2400360050070b8014800c5402d048407070301c420004201c811042e103d1000070507400a000c25115a0000c4059000c0c20707030f441d812075121103030f0403400740340000e81805800c3c69042a2442c10700b14081d51414040035420a40c142c940c0b6458107410480c050207414014082030008004840c104800103007856611840492400c0c1c0105a0481341303034030403600281203584880819500e42c160328143c0b01500049944040c03001c8641080d182950240c0103d40c24032102c0e6025108880c995420002c2c070b803c0c03100c0070341d80500c07400314040345948940c4204c5619800f000079803a41c0c4580084603626040000b0401c90041e40140040719140d1080c8080d603003030720350488151501c519a500070818400000503600e8412600c85440a5101c0c1c0120050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 37023008 1250 37021758 37021769
    0xb100c050d02060114060d110307090501120203130803250c030305060405040201080604021b03042909130f0b04090309090b0105130306050910020705010501141e040c030b03070807 79
    0x160120340c555102640c4400092042c0b44107500c2c00c01030441781b4540000200b0000c1c621031400034003170402d90030710724898100f100c0000100c1d41c182400d00c155030704640034883c89081a0300941c038500d401e03074a2680c14406c0350700007021880d0202c00302d00c0018560504a00e00840c10350401d051220004008004038137440042d0040b13860040401e6440c1494000d091042e501a140d011054403201c080c40029400030380728510b030b0704240d40810303180c0314180010700050202151140c002c04040d00451181c00c4420b400d45a03001c8100014841d03070310b8903544411440180d20b0009204105100d200000e498150031941d03009280c070b40048100b54010103100e0035075a40c1001040380c6201500103603014070803034500c4401a8480c96040000510513044503501050482c1910040c80a980e82802640c10025044070181d440b103005203c03100740080320401c2190110703807203030034210030454210f84480a041110301036a120240c80c85420300070703080701664060140c01c6844507943c0750340c04e9495414034000d2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 37024258 1250 37023008 37023013
    0x90b130f0b071709030c03011404020307061706040902040b10030519090302030313031b0b04110405041505070e1e040b01050f041202030c18090106060915030506040b100c05 76
    0x45040d01ca84030566906651001c84040b030b80a0712910104103400c0402480c2e89842000e800982e90f4501380100c11100408003031220480c10140304060511840303401910801c6030303180c0d418184000760b11035103403c00f1094500007950749031400132801400000400f2a00000ea14a00007601545a800030348603817103d09441c0c514451840c0040180d0b00c03401d00c00350060340280302003050080e034580518049407090425000300200c825441a44002880c070943d0b000340318004020500200306141341d4012812030b8100100e282641d1440803d130b50740004286420f68903000546024013036050103044c0d15004100050b48503155605440010f44c041d01e450149003403010503042e550044096407041d9112000300b50426044c901d0300c0032507008140060f6450700c00c0c4068003816442e024810382c59141c40304012102480c100080da800d6900303951043e81044044042040190f115400d120b0300e200d1785c2d103004074041d180c0000240c00713040c0455121b40d001803902c10a0030f0f603640066904500a204505 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 37025508 1250 37024258 37024289
    0x12090b0f0618060f040e0a020d080706050106170112030909110901140702010503010302060d0908030a0e0c030f060a020c011b0903031b0f060c020313080105060a0504060f1203090b13 80
    0x20300d4040d41809841d05500705100c91107100e07651401c1d4000540032400c0400f2601c24101075000640590803d0b00e090b101c40ad40000c684045c00054050a405051035082074503004600c1e08950380e5142052084180e07101209092038205403140d0601001014181011b20620440380301035210b503401121040e011402c4007000c0c600c80d4203520f040d81d007140c0d0140c5417507085a180d90240b210f95401401d0400302181e0b687c40800002e61008051030252003200301c002101d040c0910030901c1c12043c11811440ba42c4898a2040d851000045080c3e202c024201c01584528161010a014100e410a890640c2a06c008418407107170748045148100c078080e03541d2103002c096801d00d0004142101101500c45808100040042030451b0400031100b0594030440c2c5ca080030003521900d10f00481d4100480b5070751214144061483c01c04085c0020b0301c3c0c11142040142e00d083c090352811021481224240389a0392036150078180034000f800001c0c040c148d070b140d54925607240495001c1c0628051b0b80e148024410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 37026758 1250 37025508 37025539
    0xa02041407020123060d05070905040c0317120c0a020a020607060e15070c29040b0105010801080c031b0303090303030c0d0f0c0f0e040209030a08030f09060609010612090b0f06 77
    0xc151078221344400c01e908449442d494103202e0190300201040c2c03614403991800144c0040c0300d12800340f041e4040c55041041d2811450401500c0a903c01e060400b04000c1c04000303440040c42003601d802140c1c5000795507580c1180f8806a00b808450301010b940200c0c00b1480e401800543d82015040d08034131420b490f81f0f5482954119640903003507500f0720011b41c008411500181c44202101485444107506074076410310000c20090400e422103048504040c008010001540c00c2030080340075201c0034000e8030040c114000800e0703440e8890003840d4203804e17810340b0711441d584050003128a606409404e8a680b45071801d51b0034002c4c0d1000341080c00c00e03480e215040300289141c1c411040720030000d584051034690110000c03079080810051655100c3d1342040360504c06c2d542000000103951041d0180c0391207242c04007400c05281e400406588654100d101004040d80d41e2040440c10750f070b41414140b50042810003680010074441030020050303118201031104080e01c01c81d42610422044600300700300c20045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 37028008 1250 37026758 37026791
    0xa030209040624050703030b04020408010c08010e13020f0409060908120f0c0d05070e1207180b060f03040611030103031e0f05160203030f0d020304031416020607050a020414070201 79
    0xc3c06080b401801c070050030042621070401800031501901e0041210b0f083c0e2400030341207a0003a48108d500d60340d00c0c07070b004103081e0700444000d00509883c16034613103c2c41d1241c40c8840034015100000d20030428642c0d4108680c0d1554002c0112039000241040b03018170f50f2600900746d41c0701403d04410707602c0140004074100341080740f25108070301b001a064100700310015148040c00c8054600c0081c06080c0510040c01e440e00341c02844780e80303060002040f00300d00d004485507406150840c020107450074194034901036210032084801361800c44480d140c0c1c07507540342800d100400d1069404821b4410000001081c16448450030b04a1a00c03484c8201408600000a50346200c3c07406660b001310307000b400042c01c031aa8101e800c280050000c0c081d245030140e10021904151720100c00040b28903404010320080c5944008181141c28010051a2078500030f00c0e0210b02e200a1584000c0c070400c1d00041c0c0b14200304007845094440b0341d0140c003d00c4801620115003c0c000f170101c46031401586000454042d0384450b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 37029258 1250 37028008 37028039
    0x110f07141e0c060714060a0507030605061306050306030a0804030c0f050108070906080903040e041505061e0d060f09030804060e0703020d080a03020c060114010207240809010e01020a0302090406 85
    0x40740000d02c02c0035030380c0702440381d030b50413003030307040d10f0169013182c0000c0300081c00d000c100c1c0f0034241d490000450b86003420000d0201c481d9600950302644042c410719490f14003011080e8150391b15030030080d4a0341d84e60000a460a0040100200200004600082004000d901c08019164405048040b240c1c032100110341c01001120b401001604000382085094020035600790071000c00d4050b24a016200c1401d12201482961700321072605403003020741d6544070648a0b540c3c11100441e009200381c00542403072010080e240c1c0102c1d1181c40060000410403225612400c0b0340200d0401c00e004107005420090b1041e0070441c1d06580d10f80c02d0446c2e03003020800101d00481945e90013803c600c100d6005071510500c2e90048030351501816030030824581c40e1602008a10b008002c03013004004100b411034002070130322542d68845c4000310300806200d8541c11200c07001c2d002603000b80ca401508c070b5440704940780c0035140c002141106944006401803031544c4c107400400b1006020b0b0303024002c0c40c0e40d400012008481 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 37030508 1250 37029258 37029313
    0xf040e010b03061c080c030a02070e010b0901170a180b060109060504050607080304021201090c0311041103070c05010605100216050906030606010f090f0e010312080910110f0714 78
    0x204101002404003200152224003851006040506c1e11035018a1a40b14000d0503000d07034081003040010403400c0d0481405400b5001040742484852400601a04840001c0c4142e4009403800030390307807200c907500080140d10804500d83d541d112900b8104401c01040d6410b03030000c0d06c0320300045001c5010394126412214040d1900c1d140c000f40e80c481e42c03c01d4201802c00ca80c400e41e18080000501c80901407401e92601612008a03190300c3c51802410340c0c00c494088600031030901c5981c1f5009241e5000740e942c0110581460110040245407840c01001a50800c80d800f01c030b5000da49100a0340012034090514849415903221600c440810103001021120603a15a011100003840c9511610401403c21103909040030340e0f41c0c50ba25046174005817a04110b01001c00c0b0070040013032111020500c00714005e6400e04031854204018404c1c4c907946d499809504003607c1e07404100020342c11000700d80c2c01d00b075801d0116460368034034580184502010414030b401e51180117010081e800050781008981827 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 37031758 1250 37030508 37030519
    0x702030415020309090408031006030903020a02040b010c0b070806040e0c1507030c0b0405030a0e0906090c130801060b0406170906010618090216020a090e0a060f110f040e010b0306 79
    0x1e1034101414100154900c60400318041440b10b81060703212200360900441c402c0200c10f480b850207040c0140f070801154002030401d410700b404100842e80100e85800740d00e80540303020036141b10080c0140c902e120341c04002840c43c01e900341005072403a03010f864680500812501070100107103811060b5550b44001c030003030394000a181d40502048078544000d1110512038200300c0d1340344070303607441d03007000b0b034100700d0f005c5e43d0070b80000030003000c141d1b400850360190726003c881455440c20b000300130a242d03e100502c4d200765414009140440c042c0c05440c2c15009000c4e1000a2020700d84079003011130260040d1081ca00450480710480b0f00b002050044140308125000003481d40da0b180c40c50882c0e09080c105800d02580710520b102252440032030000300741002030003640c624080824414040d020b0b269078420b14826140c80c1600c40910f102013500040c00d40c00240202d0b501d1300d02d40200c0c005008040c25020390100004018030702c51400c00150045a0381e408402409a0b65590041c5240c8412550070750f014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 37033008 1250 37031758 37031767
    0xe07061403100b07110102060f01081b190306090b0108070e0703050c07020a06030203071101020c030a030203090f150103050f01050105090604020d090b01090207110f03060601050c1903080103050c0405070203 91
    0x10014101071580209580c0c00d0203051a83c0b014490040c3e444540700342c46204211408043c01e503010081550030081c42e00400d13615600d04a40561504044589440301090125840c205a91461101c0224083c1c0c1a4060803056480c5007400c01002000c6040764000d803043c000290101d00403822800b1212000703120030565130b88503400c4005040c01884443c40450512481c40580c90f00c0106401400d9075450040e41c0e0700300100301500380c2845d4454604140e00402c81e0350103000f0040141c5140000c076040c0982c880d2103903c0c41c1070074025510032094861142c03003401000340500d58005070480c0c1c00790066650052030903240b5420b0f074400f4010250050302c9480820407500785079000704074524162000040000c0c3c0c982e02c820890344d00b27030702030154150041114802c0c031660a80780e090300c0c4421140c01040b80b4600c0007281d00c030b0700d005140d60305000700800e0f0100f58450600c600c4200c000000302070b1024003520b29015108903800c0c041910340e80705405a044444c241031040f40c4c0111620780007181030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 37034258 1250 37033008 37033037
    0x1e0604050a120207091406011128030504050301020d1e0203010e161e03050105040e010504020f01142b050702010e0a06020c0c060705010b040b100503010510050903060a0e010e0706 79
    0x90b040c1942020003184210300d40000c1c0003145d40b2400904900305150003c8a040500004040d541c0243d02900f8940052500c4240080d00609c46410b2040c00305994417407110074201501e4900a90b401280c00d540000759100300f00110b40d1140352501b40c403040d19265410100800001c9000074000e072424400d00c1c00100380300105142030010b0340641407034031030402158107010303106a01545c0c601c440070980350342c010b0205180c103004a03100f0391203e030020883d9241c40d40000300e0110100441d58180007980586902041c40c81c02119201d040440c0c510452203181c0c075140401d2060300c10b070401210b01e0600405c100b14418001c40b004510403e0003448814074a890b400300075413041041050500c5686500c28103500d49c4005041000e010740000242003051009020a4071000440315201318011a040c4c2e1055812406a906507130f0143c41d0080722440c10030059801d0320440180b96490300c00d0004001a0580c0703500003982021040000b402110410365005950322560300031a404a01d210b90384101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 37035508 1250 37034258 37034273
    0x5030702040f0e0102070c030b0601020f07090213030503030106090f0f030305090f120a080d14060a03030c060b1e04060506040b09040504020a0f081006050d1a090109020604081e0604050a 82
    0x40b00120311200048074601d41e036032542281d000140481d220b0529902c100144841182c4455009a0078009850140000c00402d910340e1614012011080c8e4040307050341e009084449680059603010041360307070b00d5840e0017020b403c10b003844c400c645031508015000b00b0280d50021240d02202d505848842c28803409000300552442c441411980105188419030b21940c4108248000d41c0d020300c101a1b036038103081075034070256403035400d2001803004001c090007040d40300c2c23034440c070102c039090302d0b0a036800c1d00a481c0c00000b41c41140d00055010040c289002042a4003089206c4010b40441d4204810380d41c81c0c080c010540034038030072160414001e202951840c14107800081d80b0510060002e0240f40d03e9250110003585c564019503410707442039059070a0158544130348000381000702d6003009003d400d40d40300485c2c5020002101038144803900841c2c42401e00b504000d81807a030040410340c50b030b80c841e004240c0d280707602c0d00302040300c00400098a803000c80c00b00300f4030b0040390094040d14945c82592207460 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 37036758 1250 37035508 37035521
    0x5090a1a04080601030515220213091502091e0307050904031107090501140d0b0c1602030a0501020714070e040204110910120b0108010e06310501060305070503070207030b060a031407030615030503070204 89
    0x592442e240c0500c000001d40f6610b030a0030121700081c0044e2143c107540140b0074180c29100c91014fe489202c034007110a030f0f90000348542107810480c0c2140c401d80e294501102d80d040c0c0140c030101140300313120004c01d000c429504244d0503640040a0500d20a110710200306a50400c0c0300003800050804c0003048048079688e0003484868120405014083c00325800300346070184880c01502c2030b950100e001401c201c40c540c180c05c0407903503070001410f605040c401c070b83c0c00c00caa0180000b2f114641d250b02003c603030800d04040d140d504500518421544121a60150001500f0100700c4a0305180c2178001ea0a580900340c00c5060f2001158800103690702c01081c80103c5580500d481d011104061384070141e00341003100d01140085440000c51194034103600a41500d4004c4c0280c018080c0030700400c400f466000030303402c08036500000ca500c002d86a040104000800d550005049080780d01d4000c90044030015000b01101c0c07250b0002c0000c40304440c6148030980850000504c00d030810031007600545402c0e004034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 37038008 1250 37036758 37036789
    0x1020a1403180303090a0c0b0301061d0f04090b040605010602030a0c1101050403020a0603060f060c020f040f0b15190c02150904020d2a05090a1a040806010305152202 73
    0x1501c800315250703000b51443d001100d40309666440b20842d00204018841d840d00145800741c0d01d18203550404002508810b40800154001420112007400316513590130003501725680a081002007107607a080071504c102003160103841190030800000b40140c800800c4030707441000d50f920010022021350340c0040b84141c0356080c50404c01e0900000c00982c0c0e5410b0741d0801007010b510b000403000c3c074146049110300f84a42c031010900c102880c5000150f25107000e080707940b40c0e00f19800200070303030780503034002c014000710380e185402c28007038812003805001200c01010401c5d06410008001281568100c90049503000000d40145e507038420042ca00e0000009070140314001440503083c040c40003444002c6610110a40803054514004c40200080c00f92040a50382100e1030620724007410f10780841c190a006110b62a03800d007240c01c0c000d00e110b610381700340c80250101d03a0544c0d100e560742c0e041159403001f0301040700040d8483c02c00860182159541c0c040c110b14106030004c60001400e8080196a8842407183c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 37039258 1250 37038008 37038031
    0x2010e040f020c0703031112030604020313051c020f06010605040b030901180309090f0501050915010c050a03080708100303020a0b1302150a18050a03080307050c06160f0201020a1403 80
    0x18840491900d001505404403c0c400500d0032034911b0400030801850f02168018a401842d41044065000e20480c0e81c820025600541d594a074865010f1a80041e010040c0140c003510a600b81d00710b05d081071168040f810b81e0300300d07010040360001482d01e4a000b0721078140424010001000405141d20207140c0c002160800094512305e05c14522840d921401c10803000074006030000d01c01c0c55043e224480070949507201c204199030610001c2070003c1c0000e000b04503043c15a81a610060703224030700c8120603681c02803d0760950041c518020380820026241c5201103903002000404020745242d42c1411a40c06038002c201d05020350301d42c04010000900410507a2101440013400350705e03042d500c0d2010013a400290769030b0715844003001740340716150200c40d04902a0840e0800055890005000950740c00c00200c66503611518400c0e103c9200340040c440a074040c1d482040365803858103c0741c07030300703400603444010703101c050100c00b20b080740b0a02d407850000c82e00f0b1043c05401c00c18a0070255900c841041207 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 37040508 1250 37039258 37039271
    0x703060c020312040302060601080c13091104051915050c030a0c2a0618140603070203161b0e040f0b07090b04030b0901060501031506030203060105090a12060b010e0d02010e04 77
    0xa83c0c40c00414200d4064015900c840144a40c55900c0101d155000c44000052070a044900410400c003251038401e801016441c0c10084000c583d0400458005110041545222600341240d0b0380c6c1c00e00040c4995496071180d02d07035103050580580100d034029000d4001452508100100039201854004000e450b9000c585c0c150380c040096942c1041d20480c0741d100004403c41c6000d0004207803800b9900b48081e0040308040420458240c100444141002154415103a5460020403841c0d4050b071041900380d8052000410140300d19001c08001141c85000344541c2c3d00d446120410b10380e101510010008840398040e640812a040a5242c12141030300c2c1000407e070f6a01a804280e8029410a03104211681c0900c01000300910403074000309005e080c2441100c2040b03a06060306011446000181600040051410780c4100e04447d0419801000016034a85902c500884002142c0c01181d17074a19200d0b50038010b6008040030102000001c0142c0050880d607801119aa202d800d00c04d0341041c0c9540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 37041758 1250 37040508 37040527
    0x8010308071b030803090c0312040902030c0f04060504170601030803040b040204110c100e0a020108281b020c0f0f01030c0c020301090b0601020613080a1d0307060207170606030703060c0203 83
    0x10351520085008840d220344905205081e175091540c0087c81500c6a0b00c001011010780c0441c40a440c1258020480140c4a54441d908a070991049448107500088000360201d1555000400340042c0c6403100442030301995002080d603641c001c20701000e42180d01c107000003030010f100080415401880a0b001041d1039803000b01c114000d030807a10034450f40e40c002e1142d0422045480c894403015052a50041c0b039402450340000e4582039003e06010381c1144904c481003c2518414106940e140b1200010400c050705a00090200616204800014000c45204c580316160141610401c1d2000401e2503481001d4040150000c040317010580c01030003080f00598002d40e5080c0705a001460103505d008601d031800303c000a0a00b14020500d40c0a5480b80c038511001c180c0f240f05071100030702a810038240c4260840103201040d0041e210031640f40c840c1150102c0c0c440d40c0030907041d040710010384000351150340404019803100d400300d44581d0594802e000c2080490841e402642101c25a401130301d18152603403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 37043008 1250 37041758 37041803
    0x102150106030506030c150a11120705100b011e1218080304050606010c030e1909020c33040809040e10050105030d031b0c051606021608010504030801030807 69
    0x9a010708003082da10740401030142014170a50b500c8010071200f800098500011001550191581d580c04224200040c00041c4000300182404282c1c0307002120745a801754980700d5130782c01a03040088000707402c1169040311035010755021120401225001c2e803540d50884005c5072141019400394107001c2e2030b1030505062003a070f41d092080080c082d08030035a903454142059442c0c036030050280c50412101a440030042544615061408142112401c04000301906800c48040098115400342840094194161480001d0031003408024501c40801060700c1c002c00308440300c0d00510158444110030018001514040003030003080401000011000f513540030051810145034913280b00f56079903100502080c9010800100c0b50089443d003885a10a4860340341c001340340c3d048040051118428503402040414070a240f80c68115170380c081016941c0750402503a502119241710b80183d0300d008013040008060040900c40c6030180c8410f034081c0d11f1951514000d600070740e81596140c4c00080507030307403d8090303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 37044258 1250 37043008 37043011
    0x20d0b0405070b04060302041a0906031b07140a0501050601020c060d0506060d11030a0605090c0a0c02010e10090e060907020c060a11010203040f060f050609060d030903020a06090f08030406050403020609010215 92
    0x51b40e005860ba41010086070000400b909200c42c104030034031002da0a50348040c101c0740d10115102c0038800260100541c00d101d401007140050140342a9100d2180e54100050a4289640100d0080c00581c803003400690300d941c0a901419000b5408200d801c00944280d000160010030180003103160565070580d00d03044071403801c00101c840c00b00005100d02141140103082c00342900701c030740306281c0c1844040c110040c4030b0003c1c080103000ca0004145d0540e80201a51344444030040c090701c0d1203014200c0f006100350f50b22b0241c103401c600044007003075080c100740d5203c0b4840d100b0354008200036205541001a1a00080140010032108090041c20140280050342c080c40c0320341a206412445454001c040d5041942074408962a190810216a48044069802c83d43c15070b10082c01e644641400c403484585900041e4208030442c40004145074002d441c08219545981c101012503102d19815842e413007103110300d50018800344824070161038408014850000140100d0707502c4e5060824045e0740020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 37045508 1250 37044258 37044269
    0x50d0302070b091204230901090c0219050304170304080114060405090a03080a020306010306030606030b04030806060c0a11040e0105091b040605030703060e1f0f1404020d0b0405070b04 81
    0x1004100c05081054502c90303076030003001c86006000e01d030320105041c0301d40e03028511440380340d182d50002140c041500800c01729030154000c0c0188007a9070b107a1042501800c15074584100520a1340085c2c204880c0c0107400109651344280550b103000d180070b40c812040311001511407640d0004020029402c4000d11403480f00c507110782c0e84458207282000401c0100e500040513031007146c10402045001079408800f80c2d0707002c82c41c803000503103d0316000012002051240c00042c22140341c0792001c018400d2010140b40b1891080d603841c90243c3e240fa0901031180103142c201019644445882c200007203040d00501c1d1246005800000c02100c64610107003502c1d070640312407a1076085071406102d04400c0e04d0b24040584001d907410f002443c50540802c0e41c440981c40043d02c5079a60f40354115040390140024442c0d0a0101000c6034010300c09070403540100080d06000d500c0703a24040d00d0a07a0202405880c5101d9500100611822000b54884040889008000301c2c0c00780034400c2c0c04205450600c014101401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 37046758 1250 37045508 37045511
    0x50a110703020f0111030702030717040f14030d030905031209100903030c1e0f05030a090f0b010e06090103021c020d0b0702030706060902120105120f150a2f09010c050d03 75
    0x30b0a00340641d0840708400ca05c14000c00c0c0410800c1604d40e0004115202c55078001104042040d403280082003501682c3c001451045510703c0c0002c1546049580d400302d0301048042d2a000055801c2c268115910403074014002e4100780900350040e0308107640540e01125200580d4030790324130304100c0c104036a00c1c0d8104801181d40c0d0325502d0003141d40680d100e101030b03007851000002003980210103003000000400e80ca0070000f00000144203207200fa004520301c3c0d0380c0f0414444100c80c1c039281401402030240078044401800c1c40000312141b034a040701c54101c1350041e081c419064101c015045500e918400700b40d0b00100031f001030700001402c0464280c0704201079405140c440740e0a203401e6007956403550240c5052401407120801d9200c4000342241121000c480800c8070700345042c2000e0a021404086130558051142c80c56074540361205001d11403602c07002c00b04001c81884c2007021550701c000e111182c0f6024221801b000100703007280102640321b03050400d13440a02282d0390b0175161482c0c0600910009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 37048008 1250 37046758 37046773
    0x3030906020f0c060f040206031f030212030c1606080403080c0712020106320f03160909021003020a0c0803061c0f030f0f08040204050a0e0105070201090213020406050d050a11070302 80
    0x700f09104d81900844102003152043c2401d40003e002d40c00060034401c00041a040200c0f19001ca45403003100550340a40910b003040c8101d10095200d03040440c915103907021714012072400441c58050307041503070040e844100181c0c45a407800c44245000070300609440c0c0d41080344401203146900c0100c1060442d070f0001c0b44940c01c02c200e50403010208500c44d40b40611076140f105e0072252900032031842c54130944a00203030701450030000f8608105842e403c070f00716840b5200400e0040c0903402841c4c085001b504d5900c107442301c02100310101c3c17180c40320000020b44032030f03031100014075001c0c000c6810410040000250203407a814004c03540e20059001c640e280c0c6000449010540c00204590720f00301a810502d04800c44003801400c80f8000601c000d20440d625800a0810041640700b10100560b80d03008120b14a40610023038001c1c85003002c140c1c41415400302c4812801042c0c000c41d0255030b21a52003d081c100140703c1c2201070007000d0300001903c4d4995000050002c030150243c11110300960040184 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 37049258 1250 37048008 37048027
    0x306150314160f0f0b0a0318061505090c0915040906140f040204060819020d06080309030f010203060d0f0f0501020721030506010507150b090106050a0206090102030103051903030906020f 82
    0x6242079071015402c10808041000702c00100f44a04d42111030f40380305290ba41600c844114000c004808102008000482c900024000540d00542410150300708240c881902c0d48204206c03a241118040e00001c001c0205202c241001c642043c024940c03180c0c11404c0c00c0d29890a01d00342c912541140900000320100000300789404d601070300318064240c408629203800c00c00020f100036401443d0080d40481018050045000d40c0e0403074920510f082010008a519082c00e543c0f40d81c000d1490f01c4c402c0c42001d44400403c50f061080f64000c260041102c41811a1540c40074420603c0a1095411700f03048190703000403c3d070030b0000b4009241b0a100924281002d030320140c1789022074a400e501018949001c2041d280d0b045411249080d8011502440318241010320502070090405001d801405010001078038941101c050000f400d40c540070744485542d4001054201d020900c4040d045a0150410b0010b0341c42d00b080000209000707182c08130704002e40e5202c1c501a0b90051100241d03003540011840700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 37050364 1106 37049258 37049293
    0x10e130804030b0106120c0e010c08070507060c1401020906030a02160c080607091703041505040e0c07020108060906010c06020a0306080604050c090c03010f0306150314 74
    0x54564891408020f4100284542008607203101c9943c60005039902030030850108035510080423400030001104c0e180103507042501c1c0242c0411403075010450904c10b640c003400590300c0d240c0a40304c403890302048a41c1c001c8030305980340c0d1041c00309422030b031f03202401c4035003000c07182c00050b8442c1c0d2000020b60700e00100084c0100091201600010100000305100f0307c01c540742e031251182256600c41801d200340d1680f031021000c1d00200400d00003008070003106024400286482030500d925440c15041c502d80a40d02c200881b080800d00e00119a84240d04030f0b400b01e4240d844c2c0c025030070b0500c00609007101e00040281034540114051072010300c070780d101c540200010380c101c8109003010f0800a40300d220040b415402989070307000013075900320000110b90494414020440c0e4040c0f450b11080000d00581801c039107070080d0780030b001000c91254030050f22071140880140c0b0308004000d04125 = true := by decide +kernel

theorem cover : BRFrame.Cov 36870508 37050364 := by
  have h0 := BRFrame.cov_init 36870508
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36870508 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 36870508 ≤ n) (h2 : n < 37050364) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
