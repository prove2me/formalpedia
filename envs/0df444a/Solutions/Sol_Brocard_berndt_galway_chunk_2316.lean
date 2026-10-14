-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2316
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:20:24.480706+00:00
-- url     : https://prove2.me/submissions/f5d46fce-ad41-4395-8f5a-5e288f16f219

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 416366906 ≤ n < 416546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 416368156 1250 416366906 416366911
    0x609040b0a0e06092505030705010c0c1d071d0d02310c0305070c0f0210030905010203040303090302010515030a0803100b0301060f021009050a1b080703030309020906010c021503 78
    0x10241d440c0c642c00a0002c00600c859071040c036401c0002c01d51008100400040724040103924041018003a005100765200829041c0541e0720030300b030007541d4116031719080f40a4070055104104844038600d01581045004a080e8002c81c034540d40da00810040e8450b1150800c00820002d6000c0e40e90300f00d01005040041004140f025100b004e0030205490851400101204140800c5195a03560180e51166058410b554201d9064503001c081c6c1d180f00c0e07984001d42200c031040a807096442e20308840d0740a05c13036045440800c1c2c2c004002c0d52030741420318014024000911040740554200303000583e50500d40c0c440304031901002030041808015a4588030b04981c0083c0082031101069040070030703091040c500560090100e81e42d01017072203048080c000d003480c42c40f00d6001003103820b0050356008100c0018014010a40001003001d550032120361030166a40e03264017080131405004800003d05415902400100d8000c1c0c40350000381d600c1c1001160700b0200482c009621913056003000d6958989c1002450f03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 416369406 1250 416368156 416368171
    0x20f0301020f0c0105180604080a030f0f0e0109120305090307080304020f0325120804052205012601090215031503060c0d0e1c0c0303090605041110080609040b 70
    0x40c070b0204803001c0400294020443c2007800ea45801c140710764204078010950551030050054001070800f540d07004204d00c134007162441015141c0e10950500b80c41540840541d0038a10f4040080b03801203803005019146a44041c1c466681a6a5102107036020340141846100d0110180d4130b419407550700c0d03464503080a4010f0360040801040700e096a2005c1004c503c05c01d03d04813642a107100d610000021034403407a000300c2180c0b8441c24a81300041c00349026903055400454428940c036160071180703004140300001105085051000000e118460020000e5a641c0b025054140703d60300c10181074260743c1540340c0250441402d10103000c081c0c0207103000e55000441c1b1902c0d0851034409500003894000c09496241c04040c002401d1300310811144209180044800c008c0c09210407143c12540c3c40d030000d00300341010f129505888c1c10030107100c3d50000942031b03070181c8100205d05080c1840c2d804803407450495402103c200000c4a0801d0081c907600e03104080042c010701d215a581d070b4520868842c00350604 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 416370656 1250 416369406 416369411
    0x601031a160e0d0602090913120201020c0d080711060c0a0207060504181d0703050c011706010f11030c12040306060602160311060705340506160c0e07030b0301050105011704020f0301 80
    0x280c01984d03440414078003a01c041301d4440740c423a03800e0a04142c0c1e07040c104000029a8410000013901e0040860007514940003400c0405241d070313401f8000d54600880c2822140c284c042c440801c509a62101c014107540702c256400c68140940358807007a94688900e02a10007802000031410b65508520703040b501141d00c4e140000104101c4541c1d40174500b450b80d8108803031341d400502c11101d240d45c0c09884100401c0840c0038501050400721f00192981c6c000e90144010459072010038107090344200221144001100c044902d0300c40c950250300b01d0354005000c211013031410410002005440042c82800d05240c2400080e1964556507800704a401d040000c980c1000c002d01c02c42e00850300510007180d80444c1c0b4200c04000d2020500c0240e140c8030540c0007810381c0314205c1c02c01d1009464081c152500700407588031580511207030341400c04403095580d020541821a0300304000328654160409458020182c0083c010750f622140151044050381c0700740302500c1c0f445070001d40540360000141c0045200039000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 416371906 1250 416370656 416370667
    0x1006031808030f0a110403050a020102100209060306040c021e06010e060d0309090b04060332030a09120c091e0f110f0d060915080708060c030403080709080601031a160e0d0602 77
    0x1605c8158005a100351041e40081003450f06558060200c0751100c141d220301103140902d814001182d038000500528041c641d20845103003860300030445641c40858030b000454950100c1c480150380c40000b400307100c840e240c10b400030840030709180e0b50b14506580c1c0360301d83c125400d062141c61001081d030040a180c2c4242c07210000004140118a103094445001080c640d100d90038840c102103400350004291050760080243c02c4081c0d51024200c000d0b10b40c84212001e01d483d1314188500d01007541e411210a0341e02c1d0411900c404c1820035076400c440c503481a000e004900140d0802e4084680b00740445188030000c000c40c1c5a803282240041103c80002600012429100c5060381c003220820840212910110311052090480820945008000c110300038a510710301320404600c0c13030201038002400c0c01142c1c00418240c41c050342c61302010f8103900c0c0840c0d20f19a920b04210003500f58020900e002102840c0200301465100c2003030030546160350310f85e61501303000402032042010202c02e0944407154207116 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 416373156 1250 416371906 416371931
    0x21e0606151c0b0f191e0f06080105030f010509120a0314090609010f021c110c01050c030f0f1303180b040b0a111912030902091006031808030f0a 64
    0x10200600e20390350000183c0e249824041c802500e941005043c4611350401011105094540840c0141c404a00c2a80581001d00981c100290b1054010420549000501080311507110302c21038103e030002c50031682c074841e400c02c0303090803107030203030741c28159074010342d88220040440000a000140302480c000421024208602803a003a042d6110103403504031400b40b0540080901a400340704266080c210300d040c00012120b0048030034070142c03800d8a5103a0907170307020380680e500640d0b5038040440000e0043c2d01d084900c4080991003200c0700901c0403001c40c00f15a0039100051428800c0d000e02d0740e001244021500e007a6500903c90a0b01c0c412010790f81404a225505d8601500051190000090303c0342c2450001800c0c00407050500d41055000305150310b0810503004c0065182074100103164000141560100d003d02a03161029410410309070030300804481100e040c8040700c2c0d0b280c0c0c5c10806244001c100302480300c1580c0000d80010000c5c40428030064074149000e8020700105c2002030740c2c0b449000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 416374406 1250 416373156 416373187
    0x7030908070b2814240303070308011806061b020609040c11120a1b031806050310081c05130305120c01060e010b12070905090115021e060615 62
    0x42e5035051000c0601c00e035200030311000d0729040002e00d081c402413001c10145201003103e4880102800341c00f030303c10405c01c941c3c03c022812002e05202d000e01070740c0d903820380360501400c01b14080c0700b040030224803070030b1000348098284200000d948095580300d0041942c0c1e52100e00140c64200281d0740030104003c24002c681e903900c40e502d0028030340c1c0c9130401400c1c40c2c80401400c2c002d0307032105140c90f210104402c0511325401210306054603141045110380320b640e804c0441d045220700d0341d88120b8816080010803400d400c400a0340c8540070311124642c0668440b0900c940b034084da4030007040a041c1c22801d00d00386502030301c05015050031f10401001074035540d80b0317200d18080c00c1c0704580c126003e000031402e80202081c02510082e010006145046500d445450b117030512588181030303c10404800840c802507c83c04030007000707200041c0441c1d02940c5820207041c0c0c1d529420101030140c4101429a8000030140101612140c500000b80c8426500c1a09000c00341038201c0c604180c0031010004984008944d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 416375656 1250 416374406 416374411
    0xf120a060609031101030608070807091409120d0603061a0f01031b0e0607050601090c08090a0510020f0c060c0c07270b06070b0703021e1201030303020d0908040b0c01050105150307030908070b 84
    0xad4010403e20386840206000c0325603904101410301c41d8503080210121001604038080e010701c90569948911183d2300c080240030641000f042a03051141d649030401c418005d81c0e003002011141112a02030140041d022a101070308081028004070041c05110b03405249401e5901c0806042c40d490503d9613905e140c18140c00760840700030256141590345240d50700c20680c0342c0c4821680d0041659000540300c1c5c40c0c0c0c6443d84030002400c26000a1840100341c000740c01c2d250b90955140441c1c0640c104081345854507088844004028444c030f03000003034081820320b14040c40802441c49091031407000504a00a0a817000e00290054020801c080004200307640701c0e031207205190b5005031210001045a07402c1004680d442c011400c1c01c0c061462060140403400d03044a40c1418010380d1104e40a2b4664041d24550300050310100c000b01d070008000d40410000c10f84288014020801c5a07245c204104512580c040048528001480040c4009010754001484103001e01d401508111507a5a500b4104504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 416376906 1250 416375656 416375669
    0x306040804091b020a060b0a1d060102061609090b0406080312100f0b0a0e03010b0312070501060e090307030e01030f050405030a02010522030c0f080f120a06060903110103060807 78
    0xa8200328110040c800c141c2501e0900c0303481c101400b40510f0080d611018260090841136442c50050f206581d2102c50750010a94000c8100684400000301ea01c980400c031070580c0940a0400051142000341c0d01400a400035504c90b100481d040401030b4000f04825050039070010f079103407000318008904202605110040b10440740c0c091400c082d5012203045c09610600442480050501504441e94240c2e059242e03a0300d0b060100703100c060006800f603d00300003055010b015502d04a80058514401064164015030003840034665603916901307040000c44025400ea08140300c40f0000a01c0f41c0000d04841805140110340d240742c60004400b15482a101100c03540d1000602c00c0c221078083c0181d07a88440120b0350013950400c8070b04480c401c190504401410010b00e4840c060812000b01c1c291040d09030001005a00c1d034040040d120070711b5008210003998100d11000141c0c2c1c0030150701402d8141d801036500c9411852440c1e462006000201801505154955034081180c6000b000701e007008255 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 416378156 1250 416376906 416376923
    0xf020411161109010b03010306090609150b012006270304180e1209060a03060b03070203030108121303060203090a021e0f0405060603070807210501060905011d060306030a02030604 79
    0x41034030b412901c10452000650040ca00040100a031000d0002500d04494103c080030540035903502d040320003000d13203903001810302c800000d000000d0311556201d0300344038200fa02c03003401c080345c08410354003190180085182603603c0040016050b4203c5000c0302820550282c02807001c0d14080459800c58206801c11040e107604d0301440309001c08540940c01030f00400801503e40c0f40c1d0980002d1103144280a1018052100060b4401840e07100794050710040c040407071079507102d0400b180000c0d201d9000f845404818403030721140c400306109200c2101c681c21200847c04d106140b8641ea0140650001828010140a05401c80002da00c0d050042d41401c44c00c600e0f100c0c21509a0020000740c40c5a14441a00480c982820010151a03502c200ea03080082410141442e649140044500b4201a08203a0180c0701440c84603803281140c2c0c01083c10303182161540700c403450301d030030044456040724400d1000500c800e85c2004410706001d0002c4d900488060103581d01c1184076004039180c81010b65046588dc0d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 416379406 1250 416378156 416378197
    0x180f012a0204111c021308030d09020a050312031311060a0c05010c02030f09190b04030c060f050313063c05070203040f0e060609120606011206050d0f020411 69
    0x103081e110300002a03a07500c4402d802c14400c4180c0c54443c910310300e0140035050b40000c1440385600c0c0d2403d00c0d8024007c8500301c1e5514120900d240001c0c00401104034000d030400c150104c0c0740c2c03a0105003854410241100c16085075117211250080d0070701c1c0c010a881054003a5203003051500d90303030014000700c1603589034600c551905180c5203003102c03a900c801c4001c541080c031110140510b0601142c403107100442c1c000a00002d20b01200e40c00c41c1041c1d006400d00c82001400004120694000408503906600c0710380410700700b460103413583d01c4200c1c3d0440d0188208104032001804d50f500c80341c00446000f00313106024050400e0b0001043d882581007a0f41a00826980200d240d580100340d800710007840910300706440c03d0080d83e8004003900600c00c400d0800d4000070a191110025241502402021074110008c1c522810761541e50642d8401c0c00509e12450024107407409008001c00c840028020b2800000161905000c4c007000180813a4491741720440c450113000101d020744200ca20076591f014501c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 416380656 1250 416379406 416379409
    0x908071103060f0c040618080105240609010503060409050106090524150a050322060b0913020604050f031518060f090304050616020a030c051203180f012a02 69
    0x75401050040d0742949001084044e0355040700352030458085e0709080c0100347c041c03103003500000e4a0780c0003100c4a40c0b92100704910450380400303131030740c1e1001415109081c1e060038040c40303a1486012003203804504200041101403e1680c0040c2095002e2030000600b6611707000800d060352020f64080c2d6030b181d42c00c44502000c0740741400b02014040c9c1142d8107800d03109d11180102c0140103110300c41d018440e010000910b40481c401e0054224a90f41101511280071490140003c01c08401160b000f6a00c500000d03001d5119121070101c6250002e125a06080c5040200701450244000703854043c06840114400501ca101150380250307880e28054148511040103136150000090080440760080700c14002081d0001c41282c040d80c0c4156900303507845800c415145170807038032400000e4106610000000034440307041004c800341c880c102c03840c026148000701c0c425a03d00603800700113429450140503204601c1c111b25000c1c0b0b01c00043c10048242e0079603820300d00d18090341034158400d8805180d03004e13045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 416381906 1250 416380656 416380663
    0x903050c12030114010f180312030b0108070207030b130c0906210f0204050411031c02100c02030d0b010315090207021923010203130803041701020a050708030a0908071103 75
    0x70460301c900c00c900310f614000c14070700c048044080d8141404194000032030402c4c4900c0c050000610505c985085407a41ea1801c1107c14499a5285000a00c2c0440c221190340c400c00d00640a48099802060810f00f16210883d607440301802842114040d01c0055000411041c40c03000244102500020040d2a204024440320140081c103000c0f41040c1c0d031100b0002d4007200100b072459406031000680c3d076136545441c0407041050901240e240c86101e0001d1f420030f00c5842c2c4241026070070760030b0301d26518191940394242c5c1c000c0c030828001350304144440e841d0310040e607201b000c0c1c1032414540801c40d100010300d101d04422142c1c00c02d1007016000503000b025801d04040d100000ca0b003003807904050a291000e074460820700c80c00206034402104100042d45c0e0300c00c00070b48440342144113901e800aa6601e0320706a0701d42c070034441c2020a03289810004178008041c402d803a400449521003910b04261603035403201c01d81c80100008605540d030035141004c01e40e0303400034040f20340c4034203800794000e080c0c00c04040c80e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 416383156 1250 416381906 416381923
    0x180f01061e09060501090b0c0c0429013906140405070608040b0a0e010e0601120c0b0403080307050c030715050f09060c16060e01050717010605030720010b03010903050c 74
    0xb00c10741055000c200c1e42e40c1c000890b2044400949040d52a8800d802981e400c1071803481c1015403060401c940c602440c18101190b400b004003020035006058070540c010340d0551100c240701440c052110a10100781c0c42c101c3c00d102804501002c200e60702480d00da0f25142110781c01d20249040c04203600c01c0104020040010780c01401550801e41c01503d050380d540b024100c00101750b503620344e40307500c0f00703010340182500590b000540c07030400d0b00e15a607140d40240e81a40020502510100d0040c24009180c405400032101074030b4108189519565030708909032040d5011950001852004100480100f14551280505201180740208480c20412290981000042c2606a15802c26428414141205c42c100c80d14000200345030040640326041c640002c21341854480015401d0100700300da10743d07001d864688601866100c070030890362555000c842c0b234041141c040e40405c10f81d6419074a110401007a07030407101079940001c07032200300c101c011078299215224101c1c0403035008203040c0a41c074014042d111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 416384406 1250 416383156 416383169
    0x40609080f0c0d0f02031f0b0f040216020103050402032b030b01030b0a090f0f0504080a080c0c0703020f06071b0512010902030606060306060708041202210303180f01061e 75
    0x50180c0e050b8000a803000c28050005029180700d11422003151010b00041c03011582e12280c55485202c40024000a4103079940224402c2d14901c819008074030b064400d480c0240076140004a24903890350048d0020100503009903414402c4c40210344a038800322691400c1e500b52815411840b4104140180941ea0110091810f0500740380600045880b203000d5041215019940031907043c03075103e4101b00070701103160300003a11801c0404020038004001d0050500c42d5160b0354040c51540d071400c0300f4440e8054101c6012164201e510304002514010100254440b0010484c074540040c0d56070f0840c07411880d48890b1031041515008018515144055042c0990358400a0042d61015800a0340340e18004103801e00c60800440842d1643d22100155060107900a110030340e80c076102c0200f83d40300610442c0c02ca00c1210032441001e0b24001d03103113080045158090085055441724140001c941c001c4a80d040d0b04d42c45409142120510240100401851150700c44224a6031441000000d10125080030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 416385656 1250 416384406 416384413
    0x6100e010e01030b070f050c030a05031603090206120a1b030b01082508090a081c0b0402120c09040f0c09030215130302060d0e03070b011403060603191106040609080f 73
    0x1040844c1005500703036031289040c81c3c200340d0200d82074070507616401000c0d81043e0b14440401c200321510340240065014082c281081100c07100c652004800341e40320480020b410000901029044074200b80d03400c0d4100a042401041940851080905040e001004c11002a49a5281b0320785d03941c010132055005a1240008000b8074501e4104036a654440c840f400e0800040400154803841d092200000003984406080e5030750301c8104008000d032003c0e4500c0c0c40c90f54949540044a45028822124215624514010075644110140e50b20741c010400d402d80064480e581441800401d120780030508155455030751140c1d081d030040c81034201d21400800e4207114100142049028007a0b00300b01125030484086598540d000d03e000c028010300c20784000148004250542005503107825541078452a800000800e907890301003650300d4105179441d50f015000001d000711450328a41544445c0c6000f11320500c00400d401c1d01191017a0701070740c06840050400001448280420720904001d81c040308000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 416386906 1250 416385656 416385659
    0x22091a0319150606021e160b0306041d010c0e0402131e0312030209041406100513030209040f03080603150c1c1b031503080409110c06100e010e01 64
    0xc81d98030144410014021096000c400041140e5004107030303846110b0310340601003503582d0b9001030341e44c6030403400309402142c03500c0c20850190030020b0400591150700310341c1221245003072101000c03640040c04554026440301c00b0410486c440d9004100350210000000501101da0719004003110601703015039110714010040d00030405102d9881405940300c889040941e080c6442402e00342d00302740d520007400701c3b0b240385044005a07090340c0600b00341001a6800c0c0819960b01c0101d202c00c2d43d04035043ca0b03005102c803805180c082d2246020313149920804420340942c1e516500000c0420004a0b403c6030b0030b160411946003095400522950403080680003031000104800d14000b10345001081c0341ca20686c0403403010100344078211407030110441400204088103d054404424112541421020a050040184028111200b01c10860380c01c002d40340c0c140750602401030301070021001c8468552900344030314500f0040500c049409549800c2d4103ca465181501c80e500d401c0d816840840540103a500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 416388156 1250 416386906 416386909
    0x30b220b06270c0a0c150603030e2e02071703030105180903030f1009060602150f100603020d060b0a1106060102070501120b030a1203020a110106080706120222091a 72
    0xb800b94202c240903114907181c3c02c000c0011a00910060809803056000c11443c142000e49544014240d0f0f0181d501c1c22403808954050040360399044804030040c1008140d860f2010082c6414941b500c1c5840c416100700300e5a8003094a080198450501c1715904000b00401c8903250821500580740600082d0010310b103030600f8419100c2c00020081100c80e5250000101d03003400a004075406410204000c2088640b41e5078002d503940700b016905900f1260382c0b00411460350940300481d100d03292030ba9079040440c6c00d00100314040d401512041500944600011a0600c40e510250100c01010307030710405d21452882946103072503009052103040d900b113402c0034001640e0108807000021b030550404508102c20401291501d4a40000a0a04070740a00e000501c1c1d40e01d5002401050350702c1e65440204048818824200c0da80c0b4424006664404c000403c0901d0145601c0c200b864011f100c014103020b000200010b00d548050324400c51780c801641d00340024103003071192001c031a9100080c462008070800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 416389406 1250 416388156 416388229
    0x30f07180b03030418020409050a060819110f041e090c0e0903091c050106141009050a06390308130b0a05181002040303080916030b220b06 61
    0x1700c11318007480b411005068601901180d005102100040050785010404031300146100d0003110742ea170090520120400701140c405030708894010000c40a0b12025500700401c14500700b01280d001521400300c000404a500c404024038504034402082a280920303048500310f6030760704600c60b841c4c0e01c04180000b14500006480001a054804088403400c901c0e03051000c2e6a0071b4001002507080c10700204410300e800c4107050720130005541003c10310b201c030041500c8050703540c0070711500440210130400845116810356070b41c20811480d00c0011200d0604129112502d400c0050800d8800380c42e407804143d44143c1d4036522032100207120001f43ca69940e088100d0b107015041500142d1600d001c141039041c0c19002c05041d041f05000c07540968000003501029410900c4146c0c04605140005078000d0f8010481c040342c0d5261800984226086030344030020f1038400f81080c0754410001940e04a16070b0740d164101e4a07240141303681603191a001c410042c000c11401e68265079021f8668612000141d0315 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 416390656 1250 416389406 416389409
    0x30c09050406020405040213181a04050720150109020906071b08070303030515030a1703041b030609060f0b0a050112091a0412020c011b0302070302030f07180b030304 73
    0x2280100e89500c890510780082e0056410041c3d0041c070004288410000e0a11044111400d022030034401040f84004002118041e1408011000b45900d12260b10b00d07050f03000030345c4295a410050b150000810303e841f9940d01c80e8204001551114034607801d20b501510303415004000c82c00302940740112500225007d4007030b03884018030076400d203900032519840e039900b0b55000d085a041162141d5a0f24203004014200581c1c5610045581200c4130b506801e0125110b2251a0007862201c124600640d01201e40d0340002c0c8290b0b55900c04c842220818000e180d1070100950203000085402106400d203e0200d401528040b11405c0c0b80890403885901c6d078003496001ca90307007400d01001521804020f00701414010100510520f001061030301e65403291409240114010302c08040040c1e0446c00c240d030366508106000b8003082d51a01602d65405081424aa01620a1040e0382c071080d130700d0f40407a1070041c00c04e85007036840c2c12150090200c07070396000d40c410000e0560801400200c03180c0c000700703849120303d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 416391906 1250 416390656 416390669
    0x3071404031a070215090705150403020f1c020d030503240109180209030a0309210b010306020702030f060a052d0a1113090510060e0f092205011410030c 67
    0x20b1030004000c03074024401c0d5804c18104011201e154500280030301d40b03c5515009080c482c08004403860040e00954058405a90b405002c4680c2c10701b8010800224071103900e0301001c802681e1003007000581702d00d150300703c1540c443d40383c05403641807194103413480401002c2c2440c2c074080d1394180b120650b83d12031000012034002411401e010409484031401030f02c42e4109194151080070002e0b002c1590000c440700c00c40d280320840c0190030419040710400c403a10510041c1c00645044014400b04aa030350080c01e5140c03004044031000101c1e04180c1c1d060400484100700000d69410400004d04541c600014555184041c10354140f81090b602100c10540a00703401000c0d6a00d82032644201a000d0488512610b07895075002c0543e600d080c180003410040b14240b48000c03070280c0000344503010340040700ba500d100400c0700741818024010b0082d00c10005200c201d00c0b120810384400303240f440500481c1d099026000101d141c4540300d8401540b210080c1c000c22081e1140c21080003c5400c440d40d05d41521034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 416393156 1250 416391906 416391953
    0xb04090b07180512030307030606050301081c051207030501090e0309220902220b120309010804030909020d02040f0b030606070b0601050f030702100b04180b101a0307140403 76
    0xc8101d5000400c1c2003540040d5000401013a41c03100b01c6000001451003801d80f46d4081c8911500c0b000c0489281c0402e00c40c4144551140407901c5904540c110441041461440c0843c00c150100e402c07190302d00000d450300400b20f5a10320040c08000501e0040c0d124580d0180000c614045010020030484600000ca01c10303465407000d020030a4500d00c0e000103001c00d4000303003400724910080d16569a05414820000c10541c60f101560055050001851420082e0b00018600304200c1e1001907944400041c401c50421000c0100405e47d02d965101902410410080040e11142060b00d851401101c1d40c210810314002441000040e9503114116001d4030b5105d84402003c0c2c5803400141c030700e400380c80d00710403410001204000c0b4040c1d00064031403628081403010702145943d2000d0000302da41a494030f10960030b04000d44400300e9450b45a1503000314520100680d5607030740d040c1055010011010401032254000300b403103c03142d480180c14000c8109925070364070741459566410700c2121902d03003071202c40781d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 416394406 1250 416393156 416393177
    0x103020c030409050f10080105060607140c040606181202060405061309020703030b09160f0f0e040204060507120302030f1605120708010503070e0405210f040b07060b04090b07 77
    0x440034810b031001080549010f020b14140000c8200d2140d008031192890441003101c0000c0c00c0178140102c0f40241805400789140c5915621007858011440304810b01502c0ba00c0420340c1c880d1514400c1500408950390340700140d00249c0c808a000c0c541d2541b120002c060800b5040015940d100129000c44004070b0351144d0790120b602c020000d00105601005140d44089a29414150150040e6040840486101500d030b551580042c07818101034514400186141011503c0c050207000105243c040c0c500300300c60148420000201070760b10035045040000e002268400400c0b440c12022801c64000381015130451521303c0d60200d907800c0040c030405451308071700d64003449140070b00203c40d60301c0d403041d050004510380054040c156180a21440d0300920500c00001001c644e8400700c107014035481400382c0080c0a4480d403202c00542c5558110564140410692070300401c540d0041c0001e15048080ba0f84a83c511304019044502c1da01d0101d018030306041ca0300c00000c0800003010b80c400306030300f061031608 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 416395656 1250 416394406 416394427
    0x10909050a1704090501060f0c0318080703211b03030b010c02130e0f0a080d0b1507060f051b0703030c090f06080916060c0b09160e0603010e0d0e010302 67
    0x1210200107401c40031010b0a00015000840050040d0b5403038440a024a0360b0300e1200b03c450002d05603208001885030101d620000e0311171400c0880c00305003903181e03a800948590702141072501550045802c54240247e80401c4070000c1c0c00b209030503069040803600d8010311a0354408120380100e00800b09650b444021160ba0f0240300a8010742e5005081140000c100303505040c01052040489605440303071a40b007148450001403107280c4640e102040c18280f040420028000e061020211644a908400340340c60018201026004590040a0100308448d0800f41e1004462010306210006d410140145956210078000c642e00c06605142c00074055200c40070844440da00d0340c00c5103944105c1c50f540028035603400356119005054074419210705d0800e046014110702c03082d10514012507a07072503608003c1011180e003154460304240c182d4420591880f18003010815980004c0e0324091b1410500504c1d007400d10070305c1e8404500f8801071130300480280000e0017540003495024101500040d450307044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 416396906 1250 416395656 416395663
    0x170c2e050708040b07080d0b03060106050f09030304030b190e0601050a1401210c0806120a0b0a09080304060504050c2b03090513230c0304080702031617010e1501090905 74
    0x100a018946505e98403a442e003200e40790b201e0032050000b94280160700ca054a130200301141251100d44030186880c2056207141b4403900700025a0364940400d110000102d034040c1c003180c2c4030b2510401c030f500241e82c00800010440307081c00001c4c445907018000612060b04c6104261043d2000d040d828210390649800484202480b980000410500034001c4101418030340c00401041640d525000f01c20b50710203062003030f8040d250a5440e001e52201801c60040740000189a1b00285c0c1220f0205d06078106440e0140f140e44240c80848080e983c501c1004280613043c8191405402c00715001118055251041c244544a114101020070004907411f0308060003000d520340209005000c420001048040e050001e201c4080c0909110440b10604d42c400c5860301c0780349102d002940d282e10704540359034840c2c000700e0300031041c100d070503114400c130b00c103500101c1706081c000901c200f4161500c0e0161001c0700b5425505080c42c180c1d401e03803040c101440c02a40114469055610006001840c2103207400c0803480c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 416398156 1250 416396906 416396909
    0x2030702061602041b0207080d02010209030a060e15010b04030b1f270501241106070f03020c0a0606090c0c02150a1e050901020d080105090f040c170c2e05070804 71
    0x24174903140c40c60700f43d40c58022480804451800c001e40b000c21582945c10307800d03480b81564541e07268119030f000b080091441c0d401000c80d40c084100b221841000c140d00800e909a007031300b0a42c10000049030400c10000c424121030b034003a00001120800f560302c48011495006d0a00880e101c542151581d1080da610b1018a81180248240309110f5960345005280c9040074040032100c0402e40001030103c0c0c9401950b984807406400c800901103603441c4103045800c840070300000c108068080026003400d0504200c164101c600800700000e54604d40741d0071004465504201105014510f03d9200240c1c0c3e0f01c805940413102c10a807141e9994680d00c10459403000718a0300341d80c00400124a00301150b174000f024280c0198283c0807a60b030282541d10642d010b0320240f00301c3c3d03440071a000000e0f0b02c0e000c20740d10542d0400c2c41580c001c1c510b00d40703440d401501802d00b0051800d041c0c1c80440080c20718039000b0700c030644a44a5403080070084803071185d02c2c550000c5201d11203041c4080040d12000304013407481200c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 416399406 1250 416398156 416398181
    0x60605250311030a0c050c06092d0a06121409070504020f0f04030b01062706030f0f0e0c1305010510080403050405030a080901020d090807120503040306060e04120203070206160204 79
    0x36918142803101404c5401c5d029410f844034881e43c5100c00103410040200d900d0200001c100b218040b1500c48188a0203056804680c0c82ca1114500750155886002031100940002e403503011501100801c150b00300c0704640d200f114a40080e8061000c41c4c80c010404000b40c400075070700907a503085945450000c41c813500c124000c0f0824000741c0001400090040365051b01c80c40d40da040ea9040c03d100f2120800c103d42c0a16008803030244008010990207503005150307072503600740041813240e0280c004800f110854130140381185c21096107a0070390320384401008103082901c50104955410310002c034007113a0420f00b20a003840710410108041c10300500c10368004180c020115000b40031360385001d0300107402114002e405441440941c0d884d05002d400c800c400d80301020014010940341020306280402990010350725400b03300404400329009001d00006000d01c03c541c1c0c4207a05061070101902c2002c040400210340082c0402001030391404e04039103228401410440c0c14100500016006100d036042c000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 416400656 1250 416399406 416399413
    0x90b0105040f030501060303021b01120c270611120712090801020d020403030e0303121909050f01020307021905070302010c06020c030a020609010b0d0b19020f0a12060605250311 78
    0x4c01c40150002002d4a100c2da0988080c1450740703e03081e2640d40f070000704c0ca0201d04c606000482c0081181c3c092401007e051500801c9041c4030b900041c0e0480840e4103540d441e00c00c1d90014032110350800700e80c101040c0000002c01180f0030812024000e4050b0041c01001840601d454080c0706202e500c2d0340014006640085540d02510042c0000943c03180c40218089103481c2000221445d0100640d0b480d40000303040b942d05a550b004080703403207000780700012070030580e60b0201d034011402c00c102020841c1d055900040c1d503401d00d1a07001c3c7c81e01c455030715080c8480994402c0f40c070000c2e10201c0d6490480c0d0307083c00d15403894070036850100064015000345981034031012402ca500a9070000d003d0b0300450240c2c0c002c2042103014800c0c000c1c0c5002e2082d01401059202020a10340389901c440070210840210005003405040d60385500154803000c0500d0028410840c985000c1da0503125040081443e400c0c680d2600018001d03007081c1c407000c12018400c0012641c840801d160050704824a00010542503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 416401906 1250 416400656 416400659
    0x7110307080f28080601030603020906090604021b07050901050a24021203040605070e04050c090603060a090e060108010623010e010e0a171006030305120a0902031212160504090b0105040f 82
    0x68180f4014a503242000050400c00401c030303e035000c2d200d03c10076690040e082c00708583d02d00c01400f441c000046c00d01e03604264204a00000b860b141c0b0007203444101c03c072001e4500c3c945071000308507070000182c11251203220204401c008031580b0f0203065924101449003850460010002a4104600c0e40a5a2211480042048204201c5030310841c8070303c02c41c3c1c40d0401c50116050500c0b04030380003244d050302703108400c0015035151300c1d01c60042c41e0b00c24002840c080b4056110310314201903030b5003d03032104400e500210040c4045a003c3c00381c50083c1c00200c82203070340c07021502c84040f583c01c4a810b06c3c2e410302011040c2e81c0e0040c3d100d80d0348082c2e2110080d00c5100c1d655035481c4404c25141301c019460b07405010b244604a80015280078a00460340c1540e205800c0c040d000110b80f28082c13000e8880c00e8002c2e07545e6068001a201405400c1c00b6400c00d030503072134941e01044c0c1010712401c401031000e034816410140c5c004101c0d8000c0151030684054000000d0401a08801601e0b40d121303d400085189000c1c140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 416403156 1250 416401906 416401957
    0xe1e0403090806100602071a160302011d03070507140103021905190e0a1406160807060b0d021005180409080a0e03030f030105060706020d0906050105010807110307080f 74
    0x30310000302c03215902110455512000e10501d01840d45c0140001038209940030411030300d44561078001c60b0080400d681c50070000d001c801110a00b0001c040300543d45071042190402c0003080380d1070107040c05002840c0380450540ea00360300d4100c24004c0e41c803c1215044401c1103a44a68140ca41024821041e40c0020040c4840038005811400701001400520042581000d204031040440c403000500700404c0071b070402004041070290164090b42111091003001c405024040c1e490b1040c40c0222201596040e250600505941581d003881c0d0041510f00448801600d49080c0352701c20401d40d1906030349480540701c6c2101c00d083c03c00311155225041c2200c000a00030a000246408106921441013a46c0c03480245070300c03030160840b00051b82c00305100411040c2844002440f52504c100743c0103203800c811402c04411a1401803090322003a9031000188902d5030850010740d0040010b00300114621041d00150750b59200d0036000a00c2141d020404d040881141c10956100e40009103e001d0844050003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 416404406 1250 416403156 416403167
    0x31e050303041a070518090a0209151c1a0103050907050d05150f0105090c070309030f0b0a2702040b03012003070207090501060c120903080f0406020105010803030903040e1e0403 78
    0x19a0111038040b540108415600907000c07100c1b200300c14814076020007120000c001c50101d00620301019560200b00300d14a503903410100f641420514014a91510548188030f2140000801c00070000d61402e41c10010060380c0301c08c00d0300c01345804d03c2c001c10145c0e180c8407424101101644803980001c0210030360800c0090100d9619403405801d540c2101541e0390350303150024050f0030301c600c6030400310050115010300001c1004000300c1e0300a040043c0c4050b0341e030b911f00918050020054030011448030602041c2e050364020507400710100e289201158840403600b1034000e0304000000e20640ea10309041045880070b41107490b5805500045081c0304840c8080c0346441d07842100c0940040c0103c1c2c401040301c0305903201381816581540d6840300722407070994620030f05550781843c071800c0c01a84440000011600002032159148034141da584a0345014006800e6a8041c5c0040445403c00c0c41040548240041603408845858040805039104c0d800c031125880d03012680c0038107000d092002c1005054015 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 416405656 1250 416404406 416404433
    0x30f040e06030d09050108071106010b09030c0103090c060521270a080f0d1418071a190903080c0102180d03091a16050601080d090f031e05030304 64
    0x6554003581507807090308150300c503040c01140102143c03240c01305002035440f5603903159000303e85003480700700c03001c1c14030782140707482000d900c028001e502c0028500010b080601210848010038201400060101c0c0c0c2c6c1d403081980b9034014001040301c082140c00503051107100003d000312904060f502c03176082c00e02c6160090104803045400300701d001a0030b1005604002a5140417540160a49040c4803144001d0701c081e602c0b200d504801c56840d8002d005403c1c8005a14600628011024425259807900e401c0d00300a0700780d1010300c1b20b00c0d00007007291603105080116a40c55010542e104503081071004192182e03841c1c0d4002400050002c640b0034a2400154014040498150780d050780d00ba801200304605800b0542d4000d0019a01e4038003006550000011101440920003c50703003410243d401c0c00790300c1711240400380d41e00d51011004001804043c02600100021490f01c5403c26091411709030502c0d419100003003e0305d8100301c0413559180e04152500c1c455034850f003607980e070782840d0030b00082c1e01445 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 416406906 1250 416405656 416405669
    0xd030f02040b032a070c030206070609050105090a03080a020c07090c0504120f02090a0c050d0f060819140607210f050a09050d110705120a0203010510090b06250f0203030f04 76
    0x103403212413000019150654a401c0da006058019107410341d03007402116000300b00121a031b40e889250b9040010028001c0d548141104c0c0000c00840c081c6040003885900040c0c4110482c902c10001c0426140380810300304180c81c1e0a41010884e01890f00c8115414462580000907941e2031142c104108030a0030001c102540c0221204512502d41c06051011183e07a0462000440e008209610203042c09401c4124003401e0714500090080c0c1d5440180e081901c00c401c2d85071170300e0a4040c0700003003007096042c0075600d54101004116034030f002027000c0c1c510007111422a501404004032510048100e8104240303001da00c220520090504000c020050140f00314121201d010f0100e11000c40303031017241c402103900405001090b00758501001c0c0700042d994202c03d1803442c007500c1c241e01c0151b102400303501c1c003550745c255083c0c12503850081d41c1c208031071852580310f2107804c04000c480e0b480003442c5254503660588208050302e0f4034003413800d042000ca00c150000c2d01808046074503520324810b800500308442e00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 416408156 1250 416406906 416406961
    0x70608010911160f050a20010201180308040f140102040f050103290415090e0303091203090607080a24060f0503064009030908010507020d030f02040b03 67
    0x300504240c2c4030b40100442482c0d444030458404000c10b802c5031401d014180518256041e10f006915034040e10700e2090019100340c08240d0303a00201c1d5034244a450700004a0146a170341018060303800808002c2c01a002403c000c01071070300c000a0054100e036210040c0908c0f402199215a031b5428049000d9440c8105800302e46055428109140b00c41188110b04030080401d1861341039030700030880203065020044000340c1071030314040f966a54501c5000c2d80990030b00001c4d80c580c507120440d50310300480714200784c2007100700f80180407803040002400ca0300020780b410920301542ea864114401401d003050089120007150040004d00011000e482c1e080e19030716983d8141c0c0400c180c1041d200c1d80700035a891034011145071900145218042c5100521315056048400c030340b440c0a14070f608407192003a05115250350ba01203142055040b560180040c03500c0c1c4024801403408850281d21350008403022030a140e12410441c50780c021503411a00903140c000c0708280c40c0c0c20044002c1e071480103002c006205400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 416409406 1250 416408156 416408171
    0x1b1501060801080328090308040f1e0605030a090227042f06030a09020a0e060406051c12020f0a0c0e0702070305071a0d0e010207050d0e150306060c0706080109 70
    0x1001c0103c8145003003503c00100f03001d42c1c0c03410090311052109140c01c1003140404000c4001023a140041004203804460384003d18102804e941c03480b102c20140201d82c01c0031400820410743c1250540e0340c0b09107071000004505070b140c00481c0e15140080140c0b41e00ca400e908000500350a07503450640194000e0041454148a00b0182c6400800c1b1804070320010031015100e4625107007075401998000a08880450540034075030208600c000750380c01100c0484810400c004260500c0e01c01d0b0401000100c81c46c0c00c81d0207070341f0300e1b0300c070700000c40ca002a1056190b1149105914020000d594000010204843c41c81005040c000c0315424a80103400190317100c0360101d42110310000c0c214041e80d4200016010b554986001a2400342500d5160145511309200300c444503959880380d41d042041c0d540025a48040c01e182c0141481c281e1900c031001d0080085804c0e0741c903200c1400e01030000c3c2880c15110b651b915004001a058001d5040e071100521070414040f60490b0700564550494013004014000c19 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 416410656 1250 416409406 416409419
    0xf080d42180f0212090d020d0c021507050715020309091e1602160303030c17091e0c031c080106020708100507030e0f01051f1a1b1501060801 62
    0x80040744501d4a040039154030403040018964022024900c00d203000510348040700c2e4100c26a4082102c2c400c125030006c0c071440c840c031a010312070050244001c1c03170201d4100708140c1c002103048401e80101080260003044040030884d0421980002e460201d0801044d9109060001d659074003030040b00d8003804041000c2141c0100c000c2c07100c5440642c214441a4540e201c05000c0c16807420300302c595007144030b4500c2c0d0039130342000c0c0b07107254025500aa40c081803080d1003010107480b00000034402011005c25001700710a07080045110384104030070407031500d03216401d070301c9441c0790805030811a64180960f01c1d8484030344c802c055070201d1300030aa449411190b0327600c1106988a5500c0d103d00901038020380d80303400d50316029920041e4001e88504000030608040b90000e8901040803103a400241c1d554028010b450540b42014440c0c0c00c00c036442244000c0c10025001d00d65010700d603190080c0c03e404924a0352210325440c42e8100300c17003490b04480d1210a1480c06040c0c0440030700c2100c0100b0036103400403801 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 416411906 1250 416410656 416410781
    0x5041104030803040807050703080c100612020a050609010c140f010e0d0206041e05010f06080c0604061b0809060307020c19050d0321020c0102040f120f080d 69
    0x1140e4102d500e290840c2d9554072800003d0340311500071505030040d46004000101c580c0d015000c5240800c000b44448000ba5065004a0710680c201d244a00702110703d02005949000910080c1d030b40c140c41c2c442d107402c4404010b80d150300c0c2c4c84500911400800c448103112940004004000000d03480013480701060b10103400d07458202c0712801c0030068100b0000600441c0103d001c1c0341c10070242c03d144500750f8600d42c58003403c5400d84100c844c4d20369280c200030050703240100a030b11202c24049503607034545494110040e01941071001404861419011220140a20001942c0c045113016100230759900c3c010310002e4481d109402d4403481600e03408801000c000e0319202d56003e070344024020303021605050310296807081818043c1e40d02c4500000c3c8110882c9954006424982800d03400961254101800000514082e8001c9400c143c1c1c00da030600007045410503901d02240d00700c04615604c004020051000d040805684020501c03040c3e20490000c203495910b011440ca9030303080c20350107400c80888031039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 416413156 1250 416411906 416411909
    0x270605010e0103150e0a1401230c04031401020405060c060405010c0302030c0409020c100c02010902131407180b04060f110a050c0f1906050c1c020a0f02040e01050406020405041104 79
    0x4020f04d0b018868030300c542070b52119444603015800c80310283c0c96583d900080000c00040d07140d16944460410400b0f0717a1210756541c5003440c2d821804140d24003402d090140f40500d00c40a0002d0303019025080c40001c00794102c40280601a0410f96121144510b85941c0c0e00141c030201c0309503190208104d9214824402c0d203029010001800340303041e1400c5a41d202a40100d5216040c0b40504200c94403101d05511035900f0050203a000410020345600410690000c1c00300c2da032241506108070b800442400302c40c4103038402c101d070030101d042072000c05d000c80b8200d50581003102201c400040101e03055403c11128180113a180d07450501d60704070070000356250030003240b000700217030701244c0c200f941442c000400002c440c10240c03000140d0001c00c5800c5821070381070360244011900c0056038160f1600c0030f12805901c2c0080348000303100001100ca009603a8050303084c001d0080c1c84052918411950349400c681c1e110f03c1c040c8020f20142c1040e00b400c030001d40c8144507081c0714a140107080c4d20066509400d460 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 416414406 1250 416413156 416413163
    0x1090c09120503130e07020c0301050f0403140d0c23180103020d0b041b170702061b22060e04180204180804060804030f030b0303091003270605010e0103 67
    0x168041c58034180e65040424108102d40d1070100784002600e07400c07190b40c035000030008000d5213100750400740390180c00c0400d0342071940c0c0640d0410003007103400c09084402e6034200b580341c60120154080c503081e10341e0a000c1d0b4103555000e1070600020200c000d0b4081503003402e0701820801d004200c04105082e6070603100d12040061001c8603411680da8540c081d90280038107002c2c3e0304020841d40748940010f4219000c0f000344490902400a66105150b4004a1007081c510050820080f505181202940c1c45c90000c0c424420141107521000300d00301940c080e50038036a94580341400981540042001c400000e0064400040001e5a49503807480c1a001c0d101002181c41c107000b880e01459024000079003c41d070b08444407100032503000d1001803c12001480241210b544510355402d06150043c507100000310744004150401d580841950307004000c5401c0300350704458020040c82c00e84001c0d00607115410f0100d100f60036520032000c07504940d220320600244901020403540c1e8841d451764409000038040074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 416415656 1250 416414406 416414417
    0x501090e040302100c050405031020091c0302010f140618010f0e1003020d030c0b09070501140a17070e01021e030a0f09052e02060106080a150305030f04030b01090c 72
    0x4922015595101751680d144c185080d510f015150f82c08285003108491780c0342101350784d03002038914a103810704503404290860344481e45404040c100203407a41800b06442c80c103001c0c150b6190800c15000b544a01072445004006000f0790140b0551035034415000c413102409018403015481d01c54203e804080c0c10389014100d540c0c011400c220156024983c001c089080c041200b20010001da60703481803044620348a5a244480100f03c3d00c2e103030f90b5521002d090344810303078400b05082c0400e81e0028040030400b00740003075058540740720010440707803203d0380403a20031442c55030400c2c8000540e10511180944000b80c00b2512074155100614407028a50003a00c045600b0502c84008401d10410b0441c041c00c0240c50203000305500c1d03000190b111170485051145119a40f00c0044044c2c0c01e450385400d402141c3d0010744800e6241060191030b105008140d030a00c0e40e0386070083d090a64141e06818059a00117013200d8860425808201c1c19901c50300066520600e01c07000020405100e0150140c1c4100030340c2d40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 416416906 1250 416415656 416415673
    0xf05060f040e2e0f020301080f1f0f021204051e06010f0611030d15031e0507090e03070b01152c0108041104050403030902040507090303050403080c0106080a0308010501090e040302 79
    0x95030b900c3d40ca000d24148400040721048103850144d005111030402149001642e9500d09059a840d00c00c1207917900c44140c20180c2d5035031811105130510100c1c4012480c020542049410b05a0700920030302039035296104107401840309001e000241d04034200000052610140e0801c5042641c9900c24403400e1411203084000f440020302c03581002e08464451030840742050024425a020748030584c2a0074550142c081301002408514403c103452308040c2c0440f424449825106d00791503201c3e40c0a800c03d566150058441c80c40e1081085900d05c0b03800c42081c524558541c100d0035145078003c50200f00050180f180c0b041c000b18096840118070311a84076005407a85c640c001982d004200178405e039031710360824243d260261118000e55210341d129660009107008141704010840d200501035904000c40400d0500001c0c1d04407003107900340c0e034014a0064944160456082c054889608003c429005130a5a5070805402000306410b81e00300742c072500c49054035406841d000800c00c440250041c0d11404a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 416418156 1250 416416906 416416933
    0x712091515030f061a03071d0a1a0d1b080114010906050a090f1b180608100504020c0a020a0b0720060711010309050304081b0f2209060f05060f040e 65
    0x41e020803030409417182c25a42c0071000030b4140041e0358003041e410a40042e10621102d00c400120350700c0b40c0c145c0b034108001c2131034075a00601c08035011903850044c02088503540a000786c22900d0034018400b54484100181c03103c002c00d0103060350a02030000f150102c4008944140e06002d100260f6002500c05c0411510705120b90026041c1030130001c0039166a2201c44081d0344400341d054900300d07a60b45544004802c4201c070b00c20211820390101d820824034005100b003201031218186c0c12204d04440c09a180c0040c6213000e800c2c0400902c000790f00207414000020844134102c00f4110340e41c0a2481103a00d0180c0b030108651000300b440102d98052010130040700090034100102c98501010b160025880c0583e60f20b2a1039030303000fa00300201d2136100b100e032145034003848840100100e0b07040d1445040311849101141c120842c0300820510140c4640c07447c071030b0700081d038050b2440c690000750a11613058068001001003d0a0300d03c0c81c020802d0312000705060600c1e00070b0b1015403105c00300800c0c840c1c0c01c4a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 416419406 1250 416418156 416418161
    0xf1b09040201050d0f0c09080d2f030d02030a090519030504060c05010b030105010b030a180206030c0a11030a030209090106081306020d020403020402070b090d0903080a080712091515030f06 83
    0x80c280d046036171343c01482c03038017001910501003940c2440d00e41c5990981000e404c685044038820a05040100a6104103559000d00e4180f4152403e0544000c102141c450945c03401c6009002d40703540c15078030100800c100b10400e50000342c58580a601034803486031841d03980a0401c610b000003c0c000c14010030040140300d1140114401035401400000f810f2a841c100003800e6400a0f40f240d00003600100601040c10036510540303010f4201c6081d003503032881103903010400c103000051800540c298045440e50040b4000d1090720b202180711001c0ea80d8601421402030000c1d00403442060052a0302c0700080703110340c0503040403030041c00c0d04080000c411201c0e03542c1c04041c2d80b000c00250070b01e40e024800003005032554005082e160f4822500524a0b02e060701042d0f04d001111509103080000b649810004100940b00300c4080007480d00c2c00d800310340e80300842944d0500400c01c2611010746401c500c60140404008001910450154140032541108800d0b800c0940e150102900030a400d00001001680381d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 416420656 1250 416419406 416419417
    0x8060915060a080d0905040b0409050c0f120d08010603110c0606211603170316110c06070308041101050a020d0305060a12080309010f050f0103060b0a0510020f1b0904020105 76
    0x20002e05807203803510011420040d103802c0702d1000c148801070501851070940168044c9040c240c8017000002d9440c1c50f055540c80c90140d0060040c021551100d0542e100e06c0001c5a0800c126011101011007070303100201000390134840c5100013490300041700c00c0c110314541191903400e0110004e0009464078010800c01d400c81250500045034004441562150240009100e0f00003070522452980d140d030405d085d002d102520802600842082005044205110407080008044c0741609194841c458040d2800d000d081d5950b501030b1300411200d00b0150301c20321044c8641d204480040580741c96500645407805103220380c6015811210303006a07800d20a501c5a039001000504189145aa424240004028001c0c1c01d40e5916030010401848203800d004619080d084a80100820300c0c00b00f00008015006010050480e9140c01c2e4650451b610b000200c8083d0034024a00145003230400e0703001c2c1d90b030880c0c41d82401103805801e14201429a490703901503002c3c800a007104985030b90b589c0c01101c50380c1c041c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 416421906 1250 416420656 416420659
    0x20c2a0913050712110a0e07051c1b0315060206040b04050f0a121e090b0a2102210c160305070203060a02030a15031a0705040f0b070b0f1608060612040506100806091506 74
    0x2b54a140000c000790360003066900111040300c00700109000d44000d0548d4150307001490000c000540c00c100165000405503409074002c820b18089490f0391030003e081c032100b41261060b620070f8181e01e07800c2c00f50b8072088500701000341d164002d025140e8500c2400e04038040601e00003041103a4401c1101c0c1e81d01100030040786500d072518403103240540181e82c40300c20501399902d18190340881c07031051000300c10700d902d042404100c03003086442c81e00c010302000300e12842009a400d1070707090b0028000c143c003a03070564041035030040030b4844903e80250014000c5d00111344034204281000710b0f41428440d0107030008184c0b0781080d03c08801d2042140d007100ca048002e00b07141c0802101b0000090000f00540b100005406000b6045a0755140c03030034150103c0801030110b001c0c8003450000e110201c4028803034110342c1902c90400000c103548000000d81035014040940201d00d015000300410030101080851084945800b100303940e41d101c0300c519036902d03000c4030b1001841d8030241400200f0307052007200300ea000d0070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 416423156 1250 416421906 416421937
    0xc0b0606071403120c040f06031d0307201210020a1713170a020a030c0203070b12161106011707090e01020c2a0913050712110a0e0705 59
    0x6550340c0316020442c1e10014050103420203c0d12803e110140c0c581e268000c000100d846007041d0a1843c0548491950b102d0766041c10b684a10320421408149802611f1400c05000c0e2a260440b85c00d012000280d82418001c81304100b090a00c81843d003483e03001807010840e00104000da035204d250300c000307602c216040c0d0144018000780319000941410070910030f21101402a40ca0754082c0703010040e203211035184001d008401d100d40c040d5182c0c001000b612582c0c1510b4118031000c8503001083c00e2040b10342002c4a44040015204080080468620301038080d0f00405505000d00803001c4414034600005241282c10a40040041c02c800b24103641c8261440016214500e035a4840b0408407500c4e0000040140d4010072026900c0d002844800c106c503080c0d5801c15400c86405101c1e0107090341c1000b00078414003001020400342c245452410f041907034810b0071a5034150b140e00001411202c038003030445640405c130030036010074281110064212440000141015290420240e90540001007404032440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 416424406 1250 416423156 416423167
    0x2210c031803010b0303030106021b1e040c030f02031503151b13090f06081b010909110d4b05060607120f09050105071502032526070c0b0606 62
    0x11780910045000b00b01070b07001455008281c00c042076101c548802064803c02d1880038690800070074481000c40190100c600090203010340754140c001301490365000400902c00300400c0712003030858242e2201844100d04690400341d8051201912041c200c0e108000394401280c08880340480401038032007549200650b9a410f41c480b04854119079202c9280c0c3c2ca610f0301c03120104040700c010300900320901a43d0240131850484500043d211b0180c40c8103080c0700320b0350b500104044501100545114000d1440d041c01800240824000072642140d030034117000e5030528900441b103840d80f00d0401d05070007801c205440c9000f4180d00000500c0010301442e040107040100c4000184040300480400c0c041f51540011b4808460005090541c2d17500701c0c50501c0020000c031400302d40c18500305441e000e8100c5c3c0c09640c0c0c3c0d0f282c401e002ea600032111045008a101845c2403200250041c0921020301a01240c1e90300390074401d64181c41002c001e0300c0400c041411900a0300105541258650348031801814840c50507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 416425656 1250 416424406 416424409
    0x319031214241302030c03011a183006010311010503090a0210030605040203091b15031b070212071514030708100b07030302030115020f070e0601031b02210c031803010b 74
    0xc0c0c0c003c0390444581b140000c01070081d02d22027a00103c0401004120509220700b00d0181849120074030345440c0b280300d500c8120780c40704480301404581c079070300f07142c0318150031070407035070310341e0f5880e000c1c00100da20308859801f01019510034410fa034440d070f1102005104480f626000d00100c0c03208e95003c1d00406442d014040780c0d54030303140015070180c0150300040c011084455000800c000d020003003984102c403225050304050800c0000c1d43e4019190842d0100c0d50b01c624441140c0520031060020f41241c01081a4641041d02085144c2154491a40708804019030750f8200d071300660508080c400b03103505001051201d88111415a1b00015034164658a01d4659142c0a0f09400051003240080d130000018042d54a005c1c8030f42503458030600040040030000c18200d46c540c030340740c041d5462851460000500503882a0007049000c40000b080501100c06044000d440e1844a038031a030440911014a00003105d0817030407609012080070265081200b9000300a01c0c070769074a52441d905640310000303040c85 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 416426906 1250 416425656 416425661
    0x903020a0f050c3001020a0c15060909050d030e12030a0c140408010b0f0409020609270403031b0c1e0201031b08010513020a090e0603190312142413 65
    0x80766401030300e460410f101303801a8959452400826222a40180f102d05011030b0044444c07060b080d4003410000080490695480c01004140d006e0001103081400d4941030110129240031291000d660601c42c444844413000d50b070f048104c2000d5a03103102080000c03d034802c036500c03440d0782070b01500c0d00c60504000d0300d02108403500150043d4840d039542d410b030903e403841d120300900c0786004169001d00030310b00c40d078002480b1405946d1206000741816500c4a070f0f500e6001c290040b081c001c003d40708a5900341400c004009005c1c5000c2c541420400300543c260050044418904007680404c286e46400783c244c030325208500240b0001c0741456100c02d07001c0700d600001c4816030380048070780d43c2c1c51690350314000c20130003880c03650025503084910400c41414060b504c4144001540c0380e44032480210344070031021924012540081582d201d4051003c039007007650008800c9401e0b000341c1d900b840640840f007491100484140c904000003071141d01d4410004d07805146a04800d03000808a448900403030860805 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 416428156 1250 416426906 416426929
    0x1a0703110706051306020723270402040b0d0c050f01050706021b0606010908120912030720030304140d030c0b0114041404020d1709060c1b040903020a0f050c 69
    0x70450100341e40c0f126000f120030501c000e104510013087d00518000d031404600c4103040140d034890400744103d40359602c1d041d5041003403c0603600800124414000644001503007690200c0c0300343e00b01800c100c1e0a00d01401e41e043d01c00e40016400400b1440c01d401c0180014410400c241806010f03c100d00c040303606840030740700180c4e941c0c42050f014120154864101035004200318140b0012480501c420799000174412608072213182d29079662510807001500c10620011111000d100000d40d040400007070042240d440c2900c5520042c0b15032a000805480303014502641a251403c01e0064850785040701d494400c1d94040c1c10320300140142500d580c02025400d8200b82000c1400da030004285051070710905004043c2c880385a249428541d000034200003502c02c0250174030202c48680d84c1c600148408032a0a514000c0c61341d6944c0c140307200b60070b13120b20f07aa55019025000c2000342c21640c3c203241c091910f03800c0e41a8050320201010b41d031030040720850300c04151050700c00d042d40d105190b10380c0c045541 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 416429406 1250 416428156 416428169
    0x3a0602070501060b0c1002030a1b050d0b010e0f1c2a081c08040330060e070e10020c09010f030b1005030c011b020d080c0d08011a07031107 61
    0x603038621850401e03500f92022980610421202009210394451010650001100700350502583d039440b01d0a06030040e04a420140650b00d24480440012541110052001c8002c01406000d05d40c01e140040d10325003420201d180c0c0081020052040c0c0703143c40c255519034450b2140c900b002c00f04e102e460300440c030700b00340303038001d001d4110100049208100000020000c0c403880000348100c5203114000a0303a40881c0c1e002506205084001c101018000c01c0000b411070071201090300c0b0b40c490304128121003405615000d02e0145050b0f001f1501000d9101082d2083c1016200e51100d8810102032140d20006006a50214019904086070303980e14000c03070368001e20300000900e4059045040500050030054000f1030014001e10040007562800308580c0858542400d040f040070401003491141c1c43c81b098002944178030148070190401c8030040c00307801410100d00407212a010080e00c1900c5000080c0a04c034078800803041a425a807030910018101144245040400c441d00400061f06d01083e982000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 416430656 1250 416429406 416429411
    0x207030324030b0108060907051e0409060506041107020a1e12030509090903120103230f070807120804090b0f040c030f0b0d020f100e030d0201060501030c0903023a06 73
    0x2c2041c49012080b050142c1010001b0340641c1c280305684075960010752152074094203e201104000e03802041c6111202e05010b402480698154503105004100803201d6500c0f40c2c0c0303400342080320150b5600985902944c007400f911901414541101c500e500701110100d2800411400851550490351041c50130078480e031a801d455039030b0001002404c00000f8103180240e44280304412111240300521411a03800650000022f40d1340300f902d18041c5511419150203108501c00942c09581c001409011200c00409441c1f901da00c0b980410f88140d0091006050b04100b80001d115280e1181e020600f5a00018607104600c0190310102d02503440c056142310120b03540b48040002c682d002e0190f540001c00c01c45044240d0000b503800a0760013800205050f00901110249480c940d0044000791258100242150b00029603100002d01802403800751900103410102203050090154000c8000ea0750300078548007070400c1c02a0946014404180014031004286140700c40c03110405006140182c00744001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 416431906 1250 416430656 416430659
    0x30909060e060f1210060807050307050303120a0513020a030302010b010806040209030d0c0501090b010e0421054504050f01051c03030e060117010e060402130207030324 74
    0x2124540d074031011002642204100c503581d00c604241000c8070085400c0d6800660442402c0e01e02408031800301e030028a400004142624001070500840701c084007201c46058071007090507102e00074110005024840c100115000340c0c8a034004550010820f040031180d501d240d000180174a043e50300c25400b503551035803091400c0d6031094542c1e41c020010381b410752030582c0002c00310359106900c8a400c4108405034004104002c402c1d0880002c080d000701014104d940c45406143d240d01b000da40840e030048030215402e0404100c1c031000304200a0a032251806c120660003d40c4264186800c0111401014464205500c1b24551824030701403801e10a5400856654140402c8400c0074103060b2030211108010800365852060382c105a41c5401e01050a40704145425000341c200d060101615025100c0080b0b144c6841d48e61040e07442410074000d202c0e501d4024009600e81205482c041d400615550391400d40725980d40044c03002c0380c8a49000106908101406500114005607507030001941100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 416433156 1250 416431906 416431919
    0x312070e0612061e010e010c0c0b03040809270c03040212010501090204140103060510140c011a0f090910020f09040203090102070c0605030f01090906020d051006020d0908150a09050a0309 82
    0x80c14649040c41c01035040420002400180004010301b81c00c2c0d0401014403015030410910b25054402408500346194403420640741402c1c29030003100b4050700a4000c40151034401c100011015039012030584040340c10b444180d10a80581d0000f007043e6044025415a0021800241300d06c500808100304010b80302c504206101412903400200c1d1030405041c40410300880c3da1300190800030f80b5282c20403030f610801d00840c0c000c9a00a1208100c0254600301440d03689090702c1c40314000309401221005ca10b00781e41d60404c00c0c2c00341d094640ba000c40d8840800c071061107069500610462210540c4203062851850000e8103913441151350011a03500880c08904200504803820041d100a017403240c110302d04400d4940e8220014032030040400c5d03c680e8540c0600c4003d504071180e04050790030910113803804034214840503041d4400c050051291000031111140306404140a590300b54000c8c00744a0740c50f03e00110342c000e0250100c000117039551700b8800042c20801c201040705100303480d6101203514016 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 416434406 1250 416433156 416433169
    0x6032d090c060a05041202120f03130f12030c030e03010c020708100506090406021303080a032412060518030a0801170c06070602130e01090902150c0312070e061206 72
    0x40071600a40e0705101600aa98001007a038007542c4002c541400d202c00640000f5120034844101111540510252005001c0010008110000c03540342c3d52600c44c0c2e940c1d030010b031202ca01d501c00c0d0990500300600e00000203200d419524150360091610041c2c4108003400a800c40f602803e0710000362f4042c0c0410000301c142400b8a00101c00c0850040007a4508040442d01c8024024002232165600003540110000001c210101958200034500c3d103d4100742c0c4054024108143d000914400411a0b051961020210b0b44203035040176003182c0908002d696044040d240107820070740c540922030802119840100040d1203020b446980f045541d5252a441682e0944000000004c540060200d011540c40314803c640240c0c3d400040141d9485000e0342c40e031014030b440e8002c013240080e8000000ba84011a800c240000f50003220089081040c007624610b00e803103821300316040c80d08140540c650103c01040440d611100900703200000c6d4070303420700140c00390b808003900c03428404a10003845110709280 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 416435656 1250 416434406 416434423
    0xc0c060507062012060a12020d0611180f040b0a0611070801050c130f08030415050c100c1202090a0b0705100c0f0306050f0a1a090d0f0201020114040b040206032d09 72
    0x540300ca486c2981041c180d130554a0008601030f0141160000030b8003004440c1e445012054200f00074681c0341c2c010a0a03d0303245014110712030384203254400c043e0606240030310a10b082c06800804880342d01e843d03c1d606a1b240200c0b04503001c954050000d0000b0301c908207000d00f0f03200b8410381c130440e540c80c25401c005c0e03140b51029422040d00400b03800c400b444840f400004541c00d81d500e00f003940089001030703c011642442003100c0740d2520700824404800e880d03101e800907a1786081607211000c05154000c0413500324010410480d900c0a0a46010000d008034000281101400307007003646c015603420801c0c14103548101c241100095000340d0400041a0301d803140340c000d041c0454604040c2607151000a007140c055000e145814102a865182c0c0345403c441101c07003030b0300042d2045504181c1414078120324801000140d01550174503031141282d40001131510b05c01c65014081c0301e0141c0351038080c001d00360001894110859035004860410100825048035000401192502c1c2803400c10003080c00c01c00785 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 416436906 1250 416435656 416435659
    0xe01080c0a0f030b0f060409020d03080a0f021305060904111b0c06090f0906281505040303020304060f020304030209150307090209010f0c171c0501060c0c06050706201206 75
    0x1200040c0002501340fa219500308000303200700d000980702d00000034020050582c0080d80001b61815480400d5008400e6a101e155030301401c118a00010307a00c1010707807007060016100050050014880e074a02a40500504840900b0000e6000d101c540484203941c010a0141c1c0c41c00d0001001d501d0b0700404200c01c2ca079080080c0d80503400d041e956408105d124001600b414444c401d50400a8029128070000500030f40c901c03400203912101000c0c103070303079040e88a0040c1114030504c580c401103928000c1c8121401c8aa15030f000310301d850320740b000c1111042e0a040801c000c5000070800000540c1d200c0e00ca039030140e1520764000010500321002c041c42e0002030303800080100c2c0180107111041c0e0f0000c5680b4440c18040c00e10280f80c602501e00820003204c0c03030741b0328249810300cc184c1c0c4050440b031a1000300d01d103440c03030310403c11640c035181c0903140c540a40300024100b0651406c1030140030300c500701510308148146400310b48508400d5100690140ea40032083d01c000010075104903207041684c5650f0402030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 416438156 1250 416436906 416436929
    0xf1e04150f180219021c170103030e040b0901060302070c080705010806090c041e081603030516210503070f050c10240b0307091e030209090322180507170903040e01080c0a 75
    0x7c001036540142c00051002030103000d90003620110070b449035008000700c05801400802d003580c588101030002e401c4520143c4500068440210702041c00003054411340d1016140c8003c2075a0306400c010510500420100141c182803000040100c2003d40740000100f055a000500310b00300440c50345002e00702180703c06100303a404001c1002c030781c00c8003c4074035610100d02c51100e592258204400c41c800441c841e2803100012100c0400e1295016000c2d50003181c9070740d140c16005165500c02c0701e00340110b0401ea5115000ac05081060403c80c0e84000c9000079008491248450b00d9880707504044420b41c0f1280103424008100701a15034001c44520103041e0102c0001045e00d90081c554203001a07600000780a8100312012800300301e02001981c582c2801c00d2200300d1241480d0103600007100c1c40d8810396100a59a03c83c0c00741c62a071500529110f10100c2c2c0d104843c2c045011014205800080c01d011030501040101003141c0c019004c00d1406403000e08001e081c1c0c2001e000900c500700307200d40c0c0641e0200f00f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 416439406 1250 416438156 416438177
    0x606031a0901150b09040905070e0a0b01391212060b07050307060b061204050a0201020105010504020307020607030908040b0a170a090b0112020f1e04150f180219021c 73
    0x200d110403a01034418001884c1d840340213400c0420001c0c424001c02406070b101d0140006440092914803a200e400044414003100d102c00340107407441580a00031301010145e5841203030400b020b5041c90480310422441c3c45810351030b5904c0341200f000040215400048402d595803601110600400c0014070421004a00e821803617112a0340f2802402001403030652280503116503a99080141c6078004210301d0600030314102071510ba40d490070050002c03030241d404c2c040002030b186468800d4034441c0e6900e401030281c950350300004500622120400311200c0c00148404207142072504081c103c03a02c03d40d1030303403255800c2d520410500c8000050812070007900340b96410380006d96981d0000e044640401641c0755248032131001843c262040c0c0e00b556001400c040c031015000a000f201001c0052098404204031411200054040c5c0030304d024107012080030b07081c10041102001807980f90101420700050420a00f4189100c0100c9401c455500503031200241c10096103402d0341c441050411030804c400c421 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 416440656 1250 416439406 416439431
    0x100e06070b0c120108150a050c19090b1903152402010605060d020307030c090515090f0306040b091006080705090c07051204060908070e060906010c0606031a0901 71
    0x611405000030480c00081022030b9007002000c1c140c0f00709007241c03100c606182d80c550f55000c0c2e031042c0500c40c102c26000d81c8000f1075221900e40c8140c034040d0724411030103032401040b4140120300400c414002001c001c2030560002d01103141380c0141901c00b92501340318030480d810312070080c107031400c10180203802c648110082080c03200e1a0701b0342041400c5600450480421014240e004009940c012a0000070006240b0010142540114407400d0940ca04001d104d101a00c1252840d0f41401030700d0304900b030400c075080c80b0185040581242080145001000713480003000c079080400c1990215030f98900641400000381c020300c0f20090607805440200251860280c00e907540c1e00340d601c519802405054045526400920f040f40c00c082e4005040700c140480203e02e02c007031507200d032040d0000542c00020120780d140d00811007e0454481030310030540f070307110304042040c1d2100141c00340b030604c1018400c20001a145020701030041d40030703840d03003c0070001d002d40c0054150030040900045926048803003c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 416441906 1250 416440656 416440669
    0x60e0d0201030b180124050a0e040b0f0d080d110f0a0309030903020612070e0303070c2102030d082d0f040203012304051608070e0a1b030506100e 64
    0x56580900c0e010070a0030b00c40c4040b440300e802200402c030500e04540c00100e01241d403451502c000700007020100c0002940707030804480d540640161080028241c072410084d51510307402010054400805243da0351081c8000142c0f0380154040071200c040b408680003038a8040703403040b400150211081c0c2450950103414141403480745100c010180744e0340d640c40f01c09051140c801c0d04003a56028110980c0c526444001c070181a104845900c00036400c114862038a06022041d103421a503c040b00b1000d031400c14407000306001c1444041c44010034203c44100150b90304020f071400e180101c4d00c0e0292581404280749030341d070f003c88805141021000000581000f6204070056000c0c0403281d181840303480d20300c00070340545100f2001400710507041c03480c001184500e00d81c503030041c0d200d40c0488102441c04083c02102d0182c07031249104c5504400402c0141000c134802159101c2c00c85840004c1024032000c1007000d607116402d2200029555004000041c145010041407507101d5003020703002a00301c080041d20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 416443156 1250 416441906 416441929
    0x6070c0302130612060903211a0f01020706030b1f080a0b010e0904021e030607030e0610030b010b0a03060e0c090f180a15030b07020c0a090b1005090d1502090a060e 72
    0x11003940e8001c2c079001d0500c2366000141c2810500e0158501900e0700e5842c5019041303507a459042c1104515181c0e5051526030070900c402d089c182c001c0d00c825450701d0710680040c01501c44c590b0b003002c030074036141d42646402c0240510840158803040e401d0304240c82c1c82c00c101ca504000c03040c14400344186210055688094030341c2e019a04803041f6079070203602002a41c100d038400620030b40510803281441803040d0590003210440e00080101e503096074441e074810404211a00c006003082c21350364010b1004500304801801c0d0300381e0600300410403541c1c8014145c80101e00b00c1e1036640500c00801e680c0081e24100b10300b80015a811103400a068000341442d090001004c2d0503400516680d820742c038034a80c6662400001140c10010000d890f00c3c0c0200043d48940d9403218451207040718007404521900c0c6071049400580004e8460782c600c00c4065000d590075841011220b6002c920040318030009070007841c400751200c041840258135240c0150900c6484946c40e045141072041101c1014000d8907070700000390 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 416444406 1250 416443156 416443163
    0x20a060507020109062918010e0601110304081f020a3531050c010c0f05010203090c01030c020c06031f0807030302011506090e0a090302010b06070c0302130612 70
    0x526525004002c0e4010701c04284020400d6081411065100014810200040080d0865044110b0045040280c0101d01040022030300103151b00600c0801c20041c20f1a501c46010304044d600100c0303038403116180d600103038481b000ca54080e00b0050408200f296107500150010300041d8242034403000d010b080d8840318503004045d14030441c28141c502402c40469440888050650070b1203082000144001920f00061403171110b444101c034846444014408824054100002e010100307856801100c0500580d0320542c0d684000c04030407004640280300070b40c0030341075041c0100722940c030100015003078489505c200380540d04031003090401c0b80c03111411654070038143c04019203002c150103028000c05560350441341c654420f0000100405d901580000364001d00042c0c68001240da4403c2260080d140340140f030000d0781c04401003007011030240c012003402d40c0310340000f241c10954803001c62020b800c0741c1c00c00d40d20000d00d25410429420004100f0502400000c1c0c240314003818030304402140d04200320001e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 416445656 1250 416444406 416444411
    0x10f02030a030c020118060506041406030a0f030e181e01080d1115010b04031b03020d0308090109021c02010305011a030610020a060f060905060102011b12090f030206070807050a020a06 81
    0x26164404c0d1b108141c11248102c1c1c2065105150401c0c0d80103103c103c030818002d92400007035880b03810715206c280348901401070050400410310350f210340c01d00090300000c60034000c50902c9004290782d9810029070074065240422494076041001c21800e42c07100c85801c00800e11a401800781c4031000c200d900d0045500e0400002503104580820311b0038441d8100003001d0443c4400109050000d000140103c0703001d0303104840040030740000e00d200308559210080d4080300300e51041c00000c0c029140d1a40c44090034000045a00064000c500c0149409900e0300403010101f865508642e014844c0501406401e0100b0240301468080c0358610311026142510512491490a40061003041407000d590303480701061000c0409850000d0107014a405203910543c01c003800a03010b944144680c0c0006a001219401941002d10055400314118880d403600240c03503980c25004502e0710402404814402d5008101c18074060b00001c01408002e480c420410208001600b0903da001850b181e4294009200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 416446906 1250 416445656 416445671
    0x3011512091e080d02030403090e0a0b0d0b19090804150e0f010e06070c0e040606090e0601050f1804050a0506060d080f1c051807090b01080117010608060a0e0c010f02030a03 76
    0x104030b18003a004c0d130b03280e00310f000004002c109940308a08608482c1d50042c0c03ca06900c905028400703540080071a16001103003131034041c0225690b2400c41f0303004034051841c5405188060400c0050300c00c00034003603030700800025081080000c0110002a881e409280282040070f800001440c02921022103c2c10042c08003412640c07a602c2d0030440d0350f00e661051406040030f0303079100c801404001c2141d054070390340e1a103000042c84403680e004800b18481000050301141c1c1c2000c01700803200c1e200144403a0440941d0081480c124051400356018500910051041720400d00e801e615100300100368600500c0c0350700714940058400c4060b5080f0380c1d1000c16250b115100841c610322001600b00c20210035a0812003800b0f50807024202190407d20703a441038900c840d840d548500d00340c1c2d210780714450028460350700401c00841400c0d40c401050f103601001041d100d640f280c0c0c4038600395095900c6030460b5a03501440c80d241c8410818040c180c8800e09240e00c00002c9100044d44038081d2401d01c07010315456600 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 416448156 1250 416446906 416446913
    0x21518030d0b300c1203340b240102060a020a030f090807060f0605030a080c07050402040b0c06070c0f080703020c030d0f1d061e090603011512091e 65
    0x400881c90031000d20b41e964101040e0180020f10041800700a0b10b80160040243c031424015416444031602100035458a4005e0440c00600c5440ca00300c803c425000d03a02a15494080b010b0f045d54060180010400034104a00e92144919100b1606081741c8401000902a6600810540e40c0b04050708070040e2620346a000c00d80241c84141c400640f014a0180d1400c1042114009060140e009000411407004010302e05002c07558180905941544200301c04000642c800e001084069480425204140c0d80c94000c14266001074000140042c40825030744160704081218992000c038600d46504465103603264032012000c5100040d010600000e200c50178980201b2050000b85805402c44681c2c41c4034080c01403c0c031296500c40c0000030002e00c0c2140200c00c0c0300d100c6112480004220350b1074841c10703006a81031400c84002c5900303451070a105043c00e86c3c2d180005140244101c01c904110400270303e000916190180a500425034039100c05070010072448000b10720b09040d40010b440c0c2c8040c040c02c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 416449406 1250 416448156 416448169
    0x1201140420061201030308070c21051905040816030f0803090115081623061e0c103c020702040e070305060c0403030512070915021518030d0b 62
    0x110403a402c0350001401c100070360b2000f403846040b2402940c3e40d10076511071800403125902020740152444214241c0310501a92481020442c4941400c00a01d807128008000e0f42e0300b41c83d842c40c28049400801d003000300710418810410b5105000011100302410750303494088400558070050715003840400020040d900c254002c100300d12007518070480b521fa13503e070300642d42d906065001c1d0007604a1100024013940c1c4c5445140d1078031181b8510f000c2d03484200c00f44112500410b81741c406c888244204035503a0311a0200030003142d50204003420700a2194030031907007528038100700c0700c1e5054526688041e40000904d0316001c0301d810500381c59044101000a82c001c1e00030074001a62181c5012012448442d0001c0d8a00480340f151098a0703ea07920503500200c40d004903c4040d010860410000c485c48000282c0c89500c002c250500420780e44d00d810300e5a203580c2c582158400985e00000000750000c40700088a540320041d003e240c0360104542c94007a45a0051000c680d03000c0380c842c0c0504000707a4540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 416450656 1250 416449406 416449463
    0x20a1d01120206070206120103150911042304050f0d2c0609041e140705030a021e0412051e03220509040c06080601031514030c030f01060512011404 65
    0x104490b8440450400c7c61042120a10044640410304400175031a00020b0203141c9000d500480500c0070355050034103220140c00500034441d00e0060100c0051042c0351a070300341031301550103880102103129051414500e00a8502d454406110b4800440c2c7d1080d00248141d06581d903554502e501c01c00c10030302c082070281c0902e04802d5801424540244035005401e89182d003105500d00b400d019a200c02481010890816201c05001502c1040001e01c41c0c0f00c203400070444114010310034890034880703040390110b94100f0f400581c0c000c0e180c10642418001e0400c41d5510820381d0303480007015500c2c8141407565902c02c8550f40303440040030748010b4241444030100b0340000c00000d810f50a03149010302d480d0441d41528010000802c04490229105511a1003100c26a0190f078a1000c00d441c2002c00520828500780c038215418440c0402d0b02815440900c115026a001d00002043d1700f030070300082020180008110304840d03032411001411041c294003038190071640007444072160000c0030616443c0350022 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 416451906 1250 416450656 416450659
    0xf0a0905070f020c06130605160b040803041b0f1e08010e010e160501090b0d091209090b061306030209031603050606010314091c020f0f0a020a1d011202060702 70
    0x4100c104924107030001d0791604848250350940c1d01e640c6921082107224001c2e520200012494242c0600c03a441c0518010081c546d6220001c0840c0c0341c00b56980c0f00041d400f2181203030b50300400700a20040181c1150f52100c6130302070100e1000840c1c18255101d5150302c441c031540301d95142007100c81d5100000c0d048c20070050900c035002489111038011019001c0c141132254408a84184805584601344086c02601507590595405008901d481001e0885821881c0c0708007a8035601c03111070780054042070840705104055281d4408a0b4503085500301211181113565001c1d8808001c04041c14815030004015240c075410010b0f210b46811000c2482c00d8005514101d2456105c1408014064005083c42c480d40c001d07a0140300584c10007140800b540c0040d60342902c43c5c1c1c00400403001e404148861032501810a104558510010741d5101d854041116450300e025004401c0c80c1c0d0950500d11000c102800d484030244038459a07003070a0003d60cc6c070500c924031390414040605403c650f80c0400b11144644c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 416453156 1250 416451906 416451911
    0xa080d06031e02011107060c031d06030a0605040b0114030f10031a0a06050402091003051909060b09061813050a0b09030c07050a0506070609020a2103140301140f0a09 73
    0x8603031000c02c500c904190400d074003240300310049000001c800903403d0f0581d40301d80d8070001a804c40b07036000d450501008a840e610200752000d001025280c0c2406184244040d0601044130307031802c014802103a0f044203402d8100040422407807090003c400449070050035620740c40c0300d0750b42c4a50320907124001c11381001b4061030700c14142d200025111461640140b4004000b0440941e6a004000c12486a0343c0c019410650303440010f400203004c0c0d801350717511103015000d16000050103008003007100e1981108840301c1c1d80d1164005241d040c901103203680640299051541483c5001201c040040c2c002d040c0e001060050700d0000410105120f540a500e5022403114000e013031014807a602c035007112502240a1081070000940ca2501c0940001100d0000d400d46281c002c0c19102e10000c3d00740c48100f44d802100e00103000a408621000a050b112040001c2c0001345220303103001002d1844a00d410380507001c0510041c085401c868010444000f4102c408000f4501031350301203001e580b03060f40840009031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 416454406 1250 416453156 416453183
    0x12d0503190309060f0e040f0e0607020a030909090c0b0a02010e0a11100e01080c16050f0d1b0819020f0f0105160201050c040e0c0f03040501020a0e03010504050a080d0603 75
    0x48410190501c14071a4035000c0195031a641e0031544113003000740000010f4180c15690195080507409484451000e9501044a02c00080c94070300e00b19080d10010016444180d6020605502c1082c110140c501214184400da4245c0c403284238205041c0103211140100040480419000754802d0f000c5d808200c05440e4a0342480c100701400a1388800c016004641400804071890f110780350704010124140c6402c4002e8540d810440110b4105004104540e42e40700c10380030101c1d10811140b40ca484c610b03002828142010032004200255012021000c0c0c000101f805002807410b0040d10003000e40720403200010b0900001c224989080c41c13009101a01031480410802001034000718403540d00014a99030700c002c00701c4101d003216011120100054030500c002c1c02070190038440340b9000360026040c4c0d410081204801d1131294002c2d06c040f281698001902c00da1b26420aa418a008004070001c01c02c514060715800d4583c020800010103160001500f4202c100e1240c0c0660083e6800012031728004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 416455656 1250 416454406 416454433
    0xa02031302191836051b100825020f071517070c03181e080105010605130e090319110c0f010806040b150f03040204110304021503060117190c08012d0503 67
    0x7411a007178087c0c0111080d80c4010071190040060b0390003211206100071030101c2d6040c20800010042d20410114085e88641f0302882c2c0041200601411703005504105042c0d20207005461109120070580408401004210fa0107401c019404412501814051081c00565001d200e80384001d03002240c52200c0c151100038061a20240c450170f0368000d800030032040e6204d1000390707140e0044c83c0798640010302c1d9880a00000c008202890b03008050b010440342000c01c00102181c0c0c001480e1008000600240e48a59808808103c0c00c10010015240c00b0f881d0b1458034002840888010403c0780a07030784541d1010125100d0350703072080d0018400302e000d68076206007034140900341d442070301c09910031800c4c1030031000c4408072407040b00e0040c3e50040025003401300700c6c007400c0c1c6582c20013400342e8188580c426107070030000703200c0c6119407091540d0741c504001c01100c0b80301c0c0000c0742c1c240e002c820708102d0000014028903207141d69020020303410702c20500381c440158420304070809107a0446d0760540902c0700c03808000e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 416456906 1250 416455656 416455693
    0x4050709090f0c0e13110409050105040f0501052d1005060c0a0303050c0c190302030903030406200703030e01030f020903010204060305041a0f0a0203130219183605 72
    0x11910a00310f1074401a56010340c01c04804042d100652526910b090a0001640c020108018034401510118000b07d550700c0d5a0b0842d00200c509490040040035a1401c0000a03c40d0301e07400b40070098110080000380e02e0303180218400040349401a102c0310f0101d8070b01c40c69140301c2001810300a1800c2c1d03480c2260011701d612080c044204070003113810200803e447c1d01d283c100307503150002450018003141d00d055610004980101c24290f0075800100400d200c681c03420300040020780381a8649a84010000305081569151030b8103c4030381d600000c00c28000680c4c03111403451180424030300411003052000c1c004009118101c0c049030701d988000b600062090301908014400c40c018904030f4408031074001c030320039103500c21600491580c031881c000078071002c020750185070080395a5414a80c1a06250701180303248020b408038030300091182808000000c502a074606104d0f10201090080d484004a030782c09826985c1e50010300c0c615850341004400000340b400780c00d000c0c2c11004894040010f0340e8003049 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 416458156 1250 416456906 416456933
    0x304050c0d081903061202060a12091211031206190806010f1a070c21050105070915020106080c0d1412040f0b09060706150b040b120f0f0a050405070909 67
    0x100340030030700001000f10b00a1260000b1542c40005003501020182d007000003170b40c004148a014040b8440c1561024000c601c0341036885480341101d642c00030346281d0082c12030206803008814543c410000306c81e821404021030b81c0c101c0c10a4842d5000c14400c451622a440600e400075555489074074000103200c120410a03501719010300c1668191545810741084040c880c142000c1c102468a0300104000c01000319018040d544111842104140c940e6440d03007991000e03105c050025064090601c108600119020a0045107000801240d03117031074080c5d911004070801c0c40344142e9101ca5040d0901400b400400c400c1010300d010340301140301c1d460510100ea00b25005002c0c0d2009040c00225030104400c040380c440d01390003002ca50610a0582c0c88401030410740c03502640e0380410140000f084011240030f48040d00c103e01c0071035142d16100e068100007020051400c1e2204120105001c03e0034103186507590000c1c4000004600e981da90b007404da10300521540116807051a104401d024421540181c08 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 416459406 1250 416458156 416458177
    0xb031209043902030910030b04062408040503070218010e0a0218190f0602010603030e060a080423120712020c0a05010309020f06041202090109060605030a020304050c0d08 75
    0x2c641000b02d002003a0580c5040420101c07400c0880b0300c400800b0034010022141007491044902d808215130104841e503034007100d104007203615074407002e4461500b13001e094098501d41c100c0034003080b00c0c00c16407150094420340060510484101150611805204a400d400d4000c0e00c039091251803c8501c8252080902c0307907103481500540460800307241781c007c840c0b840803081441074030710300084108200c3d51100703e90036103282e140c0040081d80c005000d01c400020603464000041d143e00d1401c000e840441c0b403000562092104000c031322400f0b5001130751190040c1e04078125031048009040c0c010301c221203d1208680911a0340300c80d1078910119402441c00c140702d141458619020104c0c00d0741d803811a142d00c3d540c01040030b641032209500c80d51103030700003a000034000d24141c86202c1c08101f960340035400441c07200d168224541c0550030300e100034600400140e001003006500d0071000500c2c5000142035000ca00350008041400d202c0304109078840c4140051940c081d80c10940342a10841e1300100d442c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 416460656 1250 416459406 416459411
    0x60f07020a110405181b120f0604030507080d050108101103060901140301021b010e010c0212121009050f041e0305040e0403090f060216051020010b03120904 69
    0x400a510125255415541c400701807400b0442d004200005008001c0202c2d40441c85035000b6210f401d8100302c1c00c042103c2144461100300d012400340200c45100c910b90302d841d0b51282503541c8c2180c41c00903007d98400d4140c54003a407601c5883c03401044911400b20030508240c01c24001080303040000c0303000000c110700d01400b00318902100313000c009980404c49105a01030b17030060040000942010b011400d104004000500c1c00e0400440d46d8a84420038041ca00d1580d560045001918804d05c210f104040050009003d0702d601c11100b42d019104201447c0d000e0b0301400080b8103c44450030001d805031120000903c040d1418451b88054450110740c1a03c801c4203490326060f0070304440111920160301544e50340e203880e061060003180c204010703000700c0c104000610700182c2005011800c001502c04da60140014201010000214010b10340006100d441017a880c03414903900a202c200b00018210703070131a032484c09884020b0060001204458240c01a2555108104540801011003e204030b608 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 416461906 1250 416460656 416460661
    0x180c15041806080a060b061605070e0705040f180914010504061508030706020315151b030325090801231b09010c050106031704060807110d050a0302070b09060f 70
    0x1010140c078034501c20b035400f541092a0040110f135542c0c2020b60040d2001d003003e46001c1441008558041c090710094500d81c02400c018441d001d410440d154026000e450000c2c246810f00c40742d40104011486074844600c4424084d055402558000d038001640001d420201050324040da1030281400310341c02c82e885403424030a0100f03044400784950035140c08038000c504100d0b890fa00d000080d80040c0440d0100700b8540382100c2140d13035240c16140800c0d100c428264460600300041104219a100302999503003042c001c2015000c2d190b8020982c000c120104000a5128034805446800c115004145e9650070b00100503556462494014441c1400800d00309050b51403180c04814581e00154406403c4001c000e440515803160544d80e10140c016030001030f41d10350365503901d0184030b0020017595903103501140800050342c00000c0700b980441c0a090110f086a90055015105c0224030904814440040b8880008038869419500442d42c0b1098101403800d01400d2179035102c204507860000c40440000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 416463156 1250 416461906 416461949
    0x303080a0e0a05060a0c1418011403040f0f080c011406012c2806020a0303050f090706030e120c0717070e0a050c0c06040303050702071d180c1504 64
    0x41c4036000b160040040d02143d01c0f025001d401074001680b4100c100051401d07c0100b20b94144024848524420f502031400a0401c0004d010700c2908100240c1c444014020070022032440380c4e01c007140903803160b80d0040808035442c0a004901800085004941c601070b44034400c140d2003e40d050017001d00341c8490509008502e410302c0c0c40c0101031003403458200b0b00c004801881c20f10804c1581c400b0b00e4684500c02590f8070388100051449a82d020900580c800c036000010b0540510031641c02c01068200d07401207252400c401980d0351000e2260300205617407280410310801081c0101c01c01004c20f40c420b19554510060310742d40e00c4100d80200c100707080000840d50450780340000c1300d60451750099050b100d43e42e82e0074202801001c00400f018103412080005500c0b80001b40300052045200751000580340c18031420007031504810750000c1c16120114402d01d007150036901c0b00103502410300e030286255030601708400c1c2d0038901069803030b40c0c000080301d00d080305100d503110180098500100c9001c540f2009200d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 416464406 1250 416463156 416463163
    0x909070305100209010c0b190b090c1801030f110c0d020c03100915230f07120f0e060f010306182001140418050a0e070611160303080a0e 60
    0x48010019030212140a08000b01c41c0c01030a00020141080084122181c40f0f000080e0011224071490070f82003600c0e45410310507840340e03450880d41901c2560480c80c001c400020386102d50f42110441c80d950085202150384030f86c100c40d910f41c200d03100502c03410322022600c0001e80c00c00081c211090107110440b01d01d09200040000100e88000d0003440c01403482c0c0b070203800600340c00a064070980140c85d245040d2015600441c1c404144c0c5081c4840004074402583c000040060048032031074980b8018020a290b1009841c0b4203043c1c030a50000c0c0c80d81c0000e0f03c050042170709081642c018040d00e01080048800100901c5c12030303000341414000e007440d900d009842d68441c080010034205026881c1d0410300e04110790b8074200c50042c1010445031840c04900039281d04a070740082c492901a284100d1016400d0081c103800c907501d00800e004400c4507403201502c501c0907018110411049120140b00d24004003c8100c13110f490359054203005449090041c01da01d001c64461803103501701964140e2411000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 416465656 1250 416464406 416464409
    0x270a0b0c03042c041217070903020f0a03080901110f0a061508060c07030c05012c0f013c0c0507140a2a08070b03040203210702010f0309140c090907 65
    0x42e0b5044015611030340c1e05124100ca04d00c0035010401001b40e10507400c01d20112640c05500540c8950307501c1480c501c1082441c00d10b03410102d0084031400380c1007000520307110641d4441c60003420b2055171903800186040c0350183d4104007212500c64a0b10f2042405003952040f00070741a004c201900442c0c41d03581455a40800b81e4500780d5965081000402003481081d40901c800d10402c0045814200641c804041241c1c0780a0001d1100381d0481034900d81504106070700c0c003015048000d02c00a000e842500c82c401030740d03600d680300b8401914030712240d1901001002c022601c81c02030410402c01030400040007504002011140b00c4007804c02030340103100014190b85e045500c11160140d50f1002c4480e00d0300b0b210040411403402ca403c0501040b220b005018490141c0502d2034a41d07200d1500d40101031034480280b170600d6400d20050005011442800b00311142285c082c205204a034100e02c408170b00400020001914082680200c080142404a010450641e04580400b000c0c0c4418017102d40b03400d6503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 416466906 1250 416465656 416465729
    0x41d090f0a03120e1b0907230a030902030607080402030105010f032f150d0c030903090b0a170112020f09060d03140405100203040812270a0b0c0304 65
    0x4107160001c0d101c1e07841030710481520040400c0206100c0712080c64003120080d04065620b02e09440841c40c100513a0b00c03648028285007240958141025040201c0d80d100d50303004a000740011385101d540c1c06034011019199018003200d00c40c0c908a030009106072000d9408034801c0d400c1a0000514003440e4204a0076242c01508292401d06901c0090781e0f0005038800541074003010fa05034801603591090300503418450030010b5030780c40e91111000d200b100c0c034404048040c18030384000d40d00804d80c04401001540c0050b414540e6510301c009084e0b401043d00000002401400c00011400d100880000f100d0540b0075200216584100c0d410004007031011500e06030040c280b00303800000b1074400d280c492038020365030b210285001c0c1c803071b004035441c1c1c0071882c04080581d00010f030400600c03c04000e0071038081d040b580341c0c0b424210320103d030000b40504095807000010805e10342941542d211101c060041810151041d55041d461407281e480b9003081c840c0318801541402103e4404100140c202c624494 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 416468156 1250 416466906 416466913
    0x10c08041518020a1203090f0b09010f02071e06021902090a0908250b0106020a021807050d1b0314012402250302090604020703020d050a1202041d090f 66
    0x819034210300c01441070152501944981c54960300c05a15040084e13809400c020011a140e00d0701402c028150844a5010800b000c22000c42007142d40000c10648140410901e8504042c141c0c0032402c034a0018240c00c40b04100409072601512400350950840882d80305400783c48050700c0848494080320301000020750404000c4001410900d003541c08140308070710079500e250408681c2001400b060514081010504003100040000d10980b203041038010f140901c0100591406079020030314500e24100610008403420b008900c641e4000e00070b0f034541e41050803040080e0900b05654290081d001885d09022030710b00110b40b00c00c4848041e0391410780d072103170151041c11410502014114403003485d02c031003180906040382129110760b003012503a200710f21640c140c04909500400c448400e01510f030502c1944104000b00001e500401c40c0c4210300c105007003032911000c4c045401c3c2d9005959070350150545100041c0460907031006840b100000380c6148549101380c1c0c0307a401d810742c2d40d015440640c10960 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 416469406 1250 416468156 416468183
    0x110c0306011a07080301030f020a0e0c0f090a080d030603150b0d0809010201020f040906080d0302070317100801060e0a05011a040312030b120f0d0206060a0b0f040806010e010602010c0804 82
    0x107801c0d289044900788001005180c50b9198403045a681c00070303003048450382e01c038141d44001c1d8a02b958a007c09080314086401c10390400100b00e00091160040c03400c00c1c01d002080075213813a41c2d001c2150000340101d0041e91072034910140c0090081125000c1110034031021403c0b00d00c458001d00c40c039140d07120003520100e41c1c8050754a0b401c01030b40144e802a4110364081103412000c03e61b06014000a0800315800f003209824406081d0525500160003410184148140300110341d128140790011411080340340741c1510745000d20784208070036800141c1e0940c24030034000741c521181c0d0300070791042218001c100450303604c5011b03014046c444001320204c0c4010a00c01070021610356480c00250800504000645029000204241410b0070790300100d1500f084001e0590a0020300a6517600d000b240301401c420b203050350001e0710281090254850a1402041c00301605001c4007c540c00f0740007900840e5059030b0765040d02c1003060401d010b0302c40194203010301300c1c5607a4003c10809001e81d45c0b0000d01c94008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 416470656 1250 416469406 416469419
    0x90e0304030201081f12050607050307090b0714030f1e070c150c060c080603011a133b100c02070e061f0234060e0315010e040201110c030601 62
    0x10a014000305095003030404103600740031000001500504e80c8500440d10030302542086818208d0003007440041c44801c000300000345501c600f1000c2503404045000e9140c40d039034100454500d200400d0516640300014402104101003000b41070001c01e6440f43c50381c2500070400da801d80d8011084000c1240c00500da041c001d040380344000050b4010945000b00b8441c00300d440d010195414900150302080c00541400180d0800f0b010345040d00c600c01e06400e10002500c00850500418560322615480d540d42c600341d10003146030b1052405070300511003004e40c044c1a03414114a8690041c0c001d00c0ba1183c01d031642c50042181c01003143d624069000303400320300c1c540010400c2144000f0200e0394403811441c44c0350b4500c074040d2041010507a86600a000541341c070388005210f1544080d170403c1e40503080e140708546d000c0b5180f04100781c800764a45407078501242c0001c40d142034006121701c019200c6000002c2602500d9110316403241d4000d91760469440d42100415895051494180350035400900041c03200c0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 416471906 1250 416470656 416470667
    0xb1204050a05031903050a020702100327050d030c08040506041101050409020a02100b1206060d020409020904030509130506091602030d020f090a0801060b03041106090901140901090e0304030201 85
    0x100303024900792030070006940d0b9040e08580c080401c00704100341c410704e0319451a9040c41401c1d07100c40c400b40e0031850f042c950b0700006c150052420442e81055190007000d0f0702e5400042d501b031210341c0355114600c49040c561078641d840b180141070107400645802d801410b028070544519000b40c1c1c07c500504071546607a19440321103605102054180107081000061824441c80103180184c5c081d409040a1041050000b080c0d4240c1c203403542c812071140c28034031820800030070840c2d00140c04a4600042241c1880403502038100010042d60001c109000c010a064000005107a858000c580d0306019205409042040f654282c8455401103040e9000803d844184512012210714500482c2c3c1800034008840c03080e60b0010709a00321208000c21194030f6420080b0000010700060700c02480304030305200800e11a400700034409010343c0d000440d0503105071100c0c011500c0e000005003442c00107603151400108000c3e07443c0c40d06401040580d00028003c2a10300c0303031010740c0318008003071440e103440e58004544 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 416473156 1250 416471906 416471911
    0x40308030406090f150507030c2303090a0c08030c0c1509010507050c09010f030515250516031709010b01050405100e090403080f1005030601030807030302070f0620040b12 75
    0x3400711032000d0900111703420318002207502e0320001010415160070400141a207221a003030030305005041e02c10322031a00c10703a4001c0c0f020072200302404da00d0799901c1d8011850110303800380141071a5480300003c251002c011004161801400044605d94001c1200340103080d140f8030700300700049c041404080800e610440c020b023025801902280d58440070400083c511071401c5e8408002103480300c804204011007840b91440c43e681e1904400c0943c0f03082c000c54000000540d01d0010458203031034ae000041c07400f5000307a659922000d00113140c050300500d000b416089204199150303d9801e503000aa2010050103158403504041e5a42414107240c1400d100203600100350040030301202e8802e40c200c689410030860b100710300907034600c0343c90300f00030510070034801b00640440c0000c1070040e0148401e071000103541d4110303a0310000d4143da80e0040c2c181200240a1218000c12900101ca000e1040c040560084844242c03440824540e0003034a07003070000039114501c50807883d80d60600464000402464400c2e5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 416474406 1250 416473156 416473163
    0x1a2106061b0f0c030a050d0c05030c0a060f05090a0f02010e0f090a020301060806060a0c0803040f240e0a0308130602090604231008040b040503190203040512010204030803040609 78
    0x2800d001080c1e541104a010804400c01d0036030100744903980c007a4040100140510054010304900030302902d0b05e03030701c83c110f2242c2e407410712101213000d5003004010400c447ca030380050015280141c0c0240780c440064010480b411900754103120210700c49482c041034203000d45600900349542a41298015125500110395059100308581d0322285581c45100c07041c1d2050355510801a5a981864009000c803030f0060142c50184000f030000348051900001c944000c6500300d494bc640725582c5251440c01e003d40c0130b038010300085204100035040c0041203c9527110450171070303040c46400c00c01c51485a07640803401000d4000791000002c0707260040040b0070106202d008007c098503001ca11004600030768001e5001045021100f90b0729101310080c0520b860040004403090f500010000740000e0501901910180c02004900041fa00300b100030030072a141c556507410501e02902002202035100e0f04a84600e42c090900c4214800421506100b258240c0768032820040c1075445c3d9881e084000c100c03908088 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 416475656 1250 416474406 416474419
    0x1a0607120339050408070e090a080c0c010824010806040f09081e0906030403110c1507060f0b0a03150b0910321e0603040c1a2106 57
    0x1100d0100b0100309820216084003003103003a6009890011912190210b042042401d00c02404904804a001400c4500d051a5a070642d1283c9220609103082408002c181010000f402204058080346141130224240c80302c0080d41d0b504d040300b00400b0803030500d01da80072030000e84e01c100542c080d928042e000903000c0c100052621583e00c8220448a41e0b0006858040001c81c001654652a11800c0e0400300c81c030711170b9401c085640f0080365030f6001c050001001d01c0280d1441e0904d001041210740c60946008060b1404034050280d007023001d44c880c070310035180300d400c00c400c282d103204c21806110b640002c0a0a2050b1b0245140c591190380e03c00f0b4068201c50940fa028a0749040d501c61621a0050884c0020702c0e420a1820000d152101c0c00340d00300040416030b00880040088400580c00e20f410f0b41940c50001601c01d000c265036100100c0c44c0200d40c014004010321050001030030301d110603a1000d03282041000038901c2482c0080c098855011b400701000405100c0c01903441c50ba00e5048035000e01312 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 416476906 1250 416475656 416475671
    0x20a050d03150f1d070c030503010e04082101080f0106051807090e0a0c11010b13020f0f07050a050c120a020415081c120b0109050603060109050d12031a06071203 71
    0x200c00820010b51148081840c0511104400c4c0500b9103000c0e040122818400c01c0c4800070307940581540814031910a00c80c400d40c4c006400d2100e26001c840d030101c501c420f0100008241400c01281c010280219402d511a00f000c035a4004030501c00c0d05c050303c0380181304000300c0c0070315090301c201c1d0304006080c001005103561000800074085101107000348480b0320081503000c10b0000c010045c02c070240d00d081c51a130604e548100e5613161101c585290201d04a030140e42e614a40145a490384113200740d60410b0b6600092030301c1841404608210001e00c03440548020002541c100704d81303040b1130501000305070840034841c0300500c0e040d4000c43c0c400e018001e400078030301d036200142410106415141301d031440c01500300011455110300d40a03680805900200314407950540020104c18007801642d01a500000108002e43e000f1000359008282c020f01064000d01a407400b506211205180040401c0c10450500392506c9150501140000098140c034281801519030601d212500321411091658840d032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 416478156 1250 416476906 416476919
    0x105130e0a200411120402010908150609010801050f130f060504082206050714030f0307120e0a030c020d060b0901121106072402040b040e1501020a050d0315 69
    0x84803404900070500707440104507401e4502c03016582d542d4840d02c643d1030310315103682c40208682510304d18124240d07005c1c8140e45501c016a28101950040301c0c040c46039280e89072480900703480143c03040f0019102c040059030317105c2c2482d00f0384009450039010300d0050300000d040c0c40004d001440c01c450082c0000794082119031a010115030301074070123880d4034000042c00003103481c0c90180b105503500c1410381829090724044000b4000e014070b0600505c2c0c00c02840503840c468008005a5400e851640101c41e5070f414410000b401e414018400c0300c180e01e050003850007c0100200d00c0020168060310b5040a10003580e0800c20388591600040340c0c0282c0c0c801040200b501e0721040140608103040442ca030400c1113040680e001c0380ca50300903500c1501c2c2003041000040f50002094154403d07403030303072840410700c200da104003034040e54010b03e0320b4000c0400c001508000c03c0c40900d01441000450050b0400c018004981b82d08001b40d0262041e481210802c819a129612a030307603585550440c1001d66803640d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 416479406 1250 416478156 416478163
    0x130504091109091b0d0f0501020301120201020d05030106020316080c0a080919140103090c21061803080610140c150705270d1b03060f140105130e 64
    0xe05940340c05a030001c0a0460804021994000394850b004042c3d9440340181c0440d55000f02c1c81071070080c042d40f01640b00308415050003c0410358864000d54403503031511021840f41c11091026401131041680250f002030048007184d050701c641707034061440c002010302000741c0002e03042c200304d4883c1c1c020032003041050000e00801c8540d07403207011207a665440710410060614100c12003403000d0f290003081046808001402d1441d40c14081c24080741c1e8030a9410401d4086929500c030f000000048041169044190030340d0b4903440e03118800030130941081601c40c0700581554030000f40800c0506010407141d1500568001008a491415480d02c40d0b4154404c07e06402c040e14204003039121b1300c0600c903001380d4051056404542c41c90300d0360500f111070103c0403207046501211401c0c1c40301114144e0264a03524440380040350040b04010072400d2455503400d481c201c600c03003910310340d1412404100000032402985c17007400d001d216003510769007031008000b00d41c142440c0d6596a1917490754210242070051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 416480656 1250 416479406 416479421
    0x50409090b180f10180c030c06140901020a060f0b0d080301031e0203150601020120070c05010206070f1107030623010e0606030a0b031203010821040e0606130504 71
    0x141d1410000d800c0c00005020395400005449040f500940500f03401d88200041108078880070001c08184801d6a800c5244003410018000e44524500617020040c0002e00c11410111042030303030340c41072083c85c0340e0b0720340c48502603001e00e039005811000101d0007045090b0482440760400060005180d06580c0000783d003240206001c850703064003c80100b060040c610701000458484180c64415012641d00198689048841440307160035400040341e0981d200350311182d070714511810380303504001c0c2010740c034040c0f504000f000301c652207041c10001c59154404035255010311501c0e101c040e4000030648094405a0288803081a07030b10408000001045c110701900060203882c2c20380003d2280030241c2c1100034081600321441e6560000140601621642c044030352108101c08001243c1404c03500090600d42450b02070b0300740ea0340100c00861808004140d0140d1500000c248072159080740007003100300c0c011445280280441d203c0051201e061000040c17100f0302455100180c182d8603000060201c41c544d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 416481906 1250 416480656 416480663
    0xa0504020a06081b0d1a030115120c05091e07092105010209131401080c0604050409081c0b03010b01020c030a0327080d09211202010b092a03041106070305040909 71
    0x1901590200d0039000015461b8101d015002408425030f503492124202c0c619204003002c0891515011041c8201c03003041e0400751070010001d070340360309100001e4003008842902d800360403840003000c07403036690080180204580f182a89240a45202000075a514802200a480e81e5400308103101550b503480c1c4441500141030040003540c0c0681909850718441c05070084140343c2c0c4040000d07055507448000f6034080b110220b4000c500449103282ca00c000c0e0041261110074030500d8510700c11a0329164106004080081d4000c008130055200126542da5150408a0705600500701620100e40300300c204140300c00c12100a0302d04070b6280012550251b40d10f0b40709007a5a0080c00c54500324030360083c600350043c04045205c0310358a5450200d51000110f81c04002c010319419440c1920141c001e4000e1104a40b0007050100036203050b015214091190f003d03400c02d11102e2040603152803500400b030b030b4080c64002c98240c0405002130b00b404026484081c0603000c3c00300511000074802141c0c05494402d070320 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 416483156 1250 416481906 416481911
    0x4020a031b032102070806072a0b0403080411040204031e02010315030b040302192a0906031401050109180605091e0c12071809020604090c020d080a0504020a06081b0d 73
    0x3c090300080c181001508000c0b83e41c0c0100c414008411b07403001c0c1a0403041c0f0500d40d0103d10103044082142d541c1a030704801403029000c9802c00c07040c550031812a0703120f24082e000f043e40c4100c00c0340820080341f10b0741c000200b61942d442c656030a00504071900a07002803040c140040c594402d40b40303880345121154401c460350f180500c02c0008141d414030a4400140001c2c0315402c1c00d01003680d41d10101c03010411221000000c1c0903150903000ca01700d04030307402440d600400b007280c5900d0707041c621000e82240c12280844e60030500001502e443c10f00c9110002c200f5401402d0f80000075503181c6010b082c015181c0400c612920f414104801005187c11210501c810010101882100244080c14112150200c5a0b422441c0c04220300c0f145d0070790013240088800000030380c0703003c1c9100155050003240c00c8405010b1a0801c491011500000d40004d159480d0b20783c81030550703d0310441400e540007240c00942205881e101080658011b000310394024089003030742c1c40348003090300d12685c0e00d40050300e90000c4941c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 416484406 1250 416483156 416483213
    0x51303030b1008010e0a1b020a050c0907080103080309031e0c0c120322090f1e021809090a1b061704170309030d060308120a0504020a031b03 62
    0x19058894a15002000d80c2c555031041481030300a40382540501c01c81a0040c00c4000180386481581c0c014241140c40031044040c2c020a00002552051480e100b10b455100741000300c46103250000000f4811440d6a943c40c800c1e07800c0d0342d0740300401d4201400d6010988028070080200301c0c80c11540d200c168951000c400e4488104045882c50a8100200140103c0000b02074000c0850040220f031a55005881044414894102c24403035042071540941c3c4190720344030a0a04500c0c0541003224200005980f00342c62a007462040c40c100d100340c40a0100ca120308103075010580c00d100110984c0124103078280c5458030391036214a101e4000040e19210404a070344414041c030340c0c0100628040003049800112546000d1783d03040c109500c81d00c01424110404070000e80149000c00807a046003264210600165a9070300e020107513a0800c9032001040c0c141c41c0000746a11a02d0f02c1080c4c072541d002002c1460041c0345445480342450302585e002c1a5007101d03900800441c0b1030850740e000000c0501d1084030700c5d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 416485656 1250 416484406 416484413
    0x50f06120718050609030604032f01020a08060114070b070c1407050337050c061821100c14041202090a0623030327030d0504050d0308190513 62
    0x94203420213803140c1c0c01805012440d4070002442a8460b03070506000b011005910121388121441c00410702c0600103c15803107004403410340140060020540303131807605484c0da1005554450206850711420380b000c0c071041010581200e580d44c4c2050060801360f0208289440746840c41c0800e2100d00b18581c06900d01f00528141002003080300e480c1120924283d4240e00750f082014080302900144008000ba0a80117101043c4200980c686000701780a541702950f05803402d2946140c221280703e0307411022184241d03002d03041342011807140407019160070020804041c1c0140301c441000410445a008000c03400d00321140240050200d140c11304c1ca0064003441080031040005226001c0e4078142482008458000000c03005039400003075405004021202c08070346107000e0302c0180d441280c0c5240c1901c1446869100f052005102601039132000e01c42804140d4041c411845200c0c2c00204070824500484d00ca036a00e0394024a02c0d60010302c090b2081c061090940c0c3c01039401c01e04281d6011004d4042 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 416486906 1250 416485656 416485697
    0x50c0f0a18050f010c060908040909210203030f0712090c08010b040513020303030c030a090c0906080f1203222a120809090601050d050934050f061207 66
    0x1000103c0308000c0122601c00002c040ca000c82000400d49900d0303100038801c02001009450107088094001c10101d201030078032442c11440d026642c004803000c0c0403040740307680c401310440384100c200181030b40040c1c44400007180c40c03011030500c241e44d680e40c2c1c002d10f40003e40789019584c01011050004211804c03c00c0401c8222800600180c25030083c040d900030040e18040160703a40291201441d680740c2e49d407807000b08c0140506a20040c981c2d041118049984113050340004d0640e003174041143c01c0c0084000307116658480111301542104400d200041f9410001001d0420140b42d0100700c121140403075484441d6000c1440e900c42d480080c00d552580104080f83c009001000811445c2c09140254bc4813070b0340c05e105061042d40110000000141107900610807101c1c00080d446d0100040e1801504090303e80d0390160003140c020300380d0043e4082480f0700142a81d400c1210a441070000fa00c3c20041280700c0c60201e0308250810f00a002100c84800c0d2041900d210b4a443d48a059101c075442824050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 416488156 1250 416486906 416486909
    0x60b18040b0d03030f0c1d0108190e0102040f050f090103023303061f080103020405130b0f16090501080606031b0c01060609060f081b0d020721030618050c0f0a18 71
    0x2001181c1c148202000c7c00303a04802d864040078242070b0b80c5605c640144c50b079140414000000d5003403c051510312034000540c0144100d401e03440750390440c0c607103450400c4005003603003e400341c0c0300301a14014009482e00b14061943c14007004080011464000d416021003004071081c0700e11380d81c021007046081c3c181080303c90f00000400f407008500d00b844040203801804180400b07406547d0b140c000400d103034248411403040c1038003d4000b02c00c40c0b40150101d0300c4004201c89a590303400103440132481346070060140406561050710703115965942d001c00d00c40140c000614905e00040328105100404019500a000c00061b600003c00c2041c1410f0015100c0e1503261300c407078200800040306000095010185540250161820244003511440140d030309005e40c0300004a918030010302d100403c44c0c0344460600f228011211080326191019055080301d18500c074101c1681100140c04001c02e000b90300145e80040c044403c541003102c0e01824180c11f8105540f4100401c1d04d048042d50303110955141c2c0030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 416489406 1250 416488156 416488181
    0x4050106020c0d060f090218090c01050c070306110d02030f1008070308120406060b040b0904060b130b071a010e09061807140d05032803060b18040b0d03030f 69
    0x242c002c10020104804545592028010613951000b80e442d86104d03403c20300880c0c1d002041c3e40ca00b5202c030b40b083d4441b803201303803840744070f40c481c0512140055001da0240e03008001e2910103007000c0c42c9140c80e100054100e2960203a82800200302d031050840c0d00e8805140200c0c3c0b9844082d4041c0350004402802d0704040d04032424a9000c028200000361003103003114400c00f4074141550280e1154607144025180603000400c031040d0200d1b01043d070081c68000b40c114035a04885c203201841c0d89403040a43c9209400d281030228070a84010700100140800030840300348254544690303200c01b051000700300102a006200f5040e030800510030001c20030000d042d00944001c2e0a00a40049525080d9440c1c9291050a603000b0381060204402c0e0341d0003200503607094000f82603a96a12940b240315412904844100820006901c0c00d0700c1d4070740c031178420201a100c1900400345001080c14154102da01c98000c041e03401512400c3d01440c0e0780f521071365280c801c1d1203a1000315072051034000300c8080e0765150a160 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 416490656 1250 416489406 416489413
    0x90106030506032806090615060309020a030f0f05070f0504110c3309011d19150e030a031d0a02010207050d1b0f031a01050603060f01051c0204050405010602 69
    0x10080e80c02140e20103070448244508180c0102140b01d104d0f00e441604e81c06041c03d450480c08106120060300070240400c102c2c54943d5034280c0700d8109900f01c0d5101400079403c01070000c41440080c250520321138000380103070f5082c9404501d95448620308481a04124400500554104418141801000180640b078400b4900b40703442c181c0704030b070754041d00b4088010070a20311000040032207107138501030405440c0c0c80301e10b0f060786440301005000c2c0c22610100f400880321440f0810320725101041141d443d5450b404000b80f014099154105403034090b0303c00501b02640c0b02500308120000700014441c02446890101e0001c0303075070400002c85c40b05544101160f8002070450340050b0f1b4042944016075204451347da50700641d42c1007000180200700002c8810501910000c20044040306000c0c044a10a0a07159005c075100d03003040882c080c3c280305084e0804000c0c408507259103071414007030b182d00d0810300d41079007425100c4140c4445207041420600d407981d4001070a000c282024062140034000d580001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 416491906 1250 416490656 416490661
    0x403060f0e0a02130f0e0f06060603040b0705070302100903170108060c0d05040f0c0605130602031e0a020a120302070510020a050703081015110f0a080414190b07020901060305 77
    0x1002c0c1c440080c084003c0c451100f840181000c81d000742e0011070300102c410b1042180403901200c1c00d0307940b851000301481c0780c480d150025190385000b40880b40302e150b02c025002c18948409030143c8054000c501c1c21400d60007076040c0000034482510a00101078003a5481020150600020270503a27101a00905400c0e0010010402d4885030a411540c0201d0304110020741903a03642064210140c4904009108000d8614005023595012018203480c561002c441240c00b41e580da402d81e070301d1054000c42e503580001e40a46200c0300044001500c440907450040c2c0b0303000000b9546507003008c030a22400f01c0100e68040380140c140903040142d010b07805009082185000407c80b400340990040da80000e00300302440b0f000a54802c24034040600412741d64820040024424001801c0e000c07811180020b00e1180c0200109910000281600d0158015a2540c90301d800d0005102020b40842c800703030b40103c44c60f000313514222100000c101c0107000c0e12a4294070343d8041d00c100000c410303060303104408040c181030a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 416493156 1250 416491906 416491931
    0x40c030e0c0f04060f0803030402091e390a0e0402040b0301030b19020f030604050a0911102c03010506010801180f0603120206010f052706011b080403060f 68
    0x11072564214007210882461004100000c01500729500701000340360400000203078410300080030310b000764030032076107500190741d00151011011000b01010307484e05100c0010904032003111603812140c6407000c1204910700001d0342e00c41e6a80c0407071240d89605440001e400d02c64254040340e62802074608403415450146071030f00c032514601040c0005044801c07840e011030b080c000c0c45c4410500c6855543c3c1c095484445d40325070f5180c95001180c8040c003030b60078540019040d101d5441280c1402d54422208800d03440c0400030302400390001040310091148181c8490b85040d1040e681c130300441540b40c054031981703130020245425100c01070031550500004c07100612000c1960001d040034118580c2d0002a104000300c45840a40210390026108002c3c03646108040c6d0390100c0c50a044e102042005400e0b1036031402400100140c00b40208840010700041000c00c0d00040072007500702c7c10500d010200e28101204d81d00e02d546040c1401c03502d40c4030021f020010802a80101004400301c0320003040100310001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 416494406 1250 416493156 416493163
    0x18070f2301020102040f090203042001170c04050a08060603070f050108010303030903090b0406050909070203030106210b061b0705010201090804050f011403330a1203050c0607050306040c030e 84
    0x6414004a03980c0103445440764400d5041d42e004103460b01d001018a0740d20701c1c0703040081d4010741c2d041e102c994001204e10900b964100e5121990324043c1e451403d4001105655101c4040c0980f4400440108100005060f030f42d071100300c2c01800303006003d0061801d240c2c00705460400030380e000101261102004200381c0e070308154503d0440750142404125829249011109a215600050403091020070040342c250f40c41009051495400d80b0068495150400c1c1a0b0313490009220708400166400701926200400b11102c00045200343c0d80800e01313000500c0002c01940011109200d4100080700e65035500c80d0401112004110a0008101d208007039118984144218042c1500031001d80410381e515911400c990301d82c08250302e003025282d0414410088042d01c9010392140791407410701da40e481c4c407243c404842451400041007240564948071800408030382100055003446001d11610309540702c2841814070030651569100c0d942e1400c80104411500c2041c91401010310f4801d04114590000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 416495656 1250 416494406 416494439
    0x106050f09060312130f0608070314010305210d0615080f01050f0111030d1b020c060f18010c050102070b0106031d060c1822180807060216080318070f 66
    0x20039415a5460006584217989580d50b0004043c580c0410002411581c410b11103070140a4a0b507040c002005c10240b881008482800040c0a0703030000d58120318030008113542c003001013030f500503000d0501407568236400803202c9581c00707a10075000c00c400000c1c101d81c2c019459580400c3c0c2820380c000d82e50411010511a14141c103100341804a81d2928244854080041c3d654809400c2c0080c402250030019880111751641c40f804058421505061628503124060703c0d403a107800801c003820450102c0f00134280704000001c50703050282e4900d180000c03c100f80020065140200c890f002c0039454500024229500c0c640c05900418134a2008900301070080b80d132540011a43d01d040d504c66000c1401d540704a001284c5083e800803034800c005141000d407400480f0640c040b075904003c5008500c1078003090000c80c0000a01c006800c108250010703150b980600b90219440625400c601841ea079100c6040e0300a40300320b0402481d203100040c4100c0200b0225019085444404c0b440524009802c40380030441d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 416496906 1250 416495656 416495683
    0x4140405030d1a0904110301050106020f0c10092d06030603030c02131e050a050a05160c1a0f1005061602040b030c0d0c08010b030c010c080a0309140106050f090603 72
    0x40b55803482451100402540300c02c1070050076000c4038280383c5802c1803281b00403404240a5401d200000032414004900141040c003204013502c0e904003c0000c0000380c400e54500c00051218109020a00303c650300400b9400c0e06256514a200d044001011440903403250704c20b000301030800005100290b41712803c001d0341c0d0341c1618240055684031010002070188130030503105c3c042000d001d48840000c56000745010316071824040081c2c0d00d5403803c07403041d00c2d0304461034407070b000301c41d034801031002c0c8115101c144050040e1045616408001c411050491003070300d041da480c3d1b19090034860314038110840c100c000e210488510349000d00d01014180c512424280181c895541c840d008e200c10741381402980b00d5a900186070048111203403402540103150b50184031940e40c64458010038500340054001e04c030400584074419010000e94501c203199000107004020076458281010003d001c0d2003806603040040400450028241001e002d4008801440e40e80304e0340395201400820340700030480500d81c861 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 416498156 1250 416496906 416496911
    0x702100c120b130f0b0901081203010513150b0403050606010807120905070305030c0f06010e011d0a0f0c020c04111201061b0f06140109020c07050f0406050910030204140405030d 78
    0x802c400012820000124103550150030883c1a415400455120001c158401c81d4035001d0340c1d881d4140169180d091007045100414200300510982c41c140c15401d1450317403d41008922120420300c2c0d00381044141c0d004100400b00440c0604c03c0100134014075074407120030720b40132102d440c0ca610300502c10280d03150540e050940d00d00401d0305106060003420301558100303048075aa040c90030805076807071954a11601c003901a010000c240742c3c6054460707a04a031200c4c104030720101120a2825030846c0080c001240d42035450720300d00049929030084400c443c0141e009001098006000d000c1922145203c2c0c509440c820410040c4c41e44e0700c3d410440c156849450000c0c159180341e40c0503600c40c0311101002d0082d40900401a00300000c5401c2540e810340811090b491590b030b160b000005078016070a03584507540250f9028401e50510020703250411200030000316490756500003103044010f00360ba01c00e900c000b5006007030066041c1406070041c8184899400001460a916070383d450740980f4a02c010541c4c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 416499406 1250 416498156 416498171
    0x309060a02130f0e0108060108150403030b0424080d090506041703040e0103050721020f1002031603051e2104060906060b120a02030106020c0d0804030b0f0702100c12 73
    0x610b480c940406409a4020101100e07220504032101c078009201d0410740f40309050022820010101d010503848140d6101c904480e100c5a5054000d81704100324a9003041d541c520400708080060241c6d215603003a5404080100c0c142800503041c000c1d00030f882c409110a4180400403516200d003203c00701c071080f2881c00b010382d140c41002403c6104503407216000b1901400003006008010450008444400404c40b4100c2c0307074080141d038800c2059102a40c4240c100070302903164240b0780d10b440d402100603c10740f0300e0316a1100307210541c02085001600040c07004140d11113805030140f1801103821002c04041c0c2044440c0008054400114199517608202c00300428100411034108980065020f401801310030349071400030540350024403240c81d08104800111342404050301c220f078103858181d4042d08681c00000140594840061800c880500007000b0000118050320500c0c4e00580806039181400d04003070300028503102000c240703d80c1c2c80c0e141540b00a81160014400405105492004a14039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 416500656 1250 416499406 416499427
    0x90a1815020c0105040c180c1403070e030f0a05060606030405120f070c0b0d1805190201050f0301091d03040803040e06030c09040b0a180210030504140706170c0309060a02 75
    0xa02440b02010495030814090108002c18441e036001074507170382d500fa032110f011120300000c19904080b0001c00821141610402003e14100007558407400c54100901c1c005c51a901081c42e21108501700082604810004000c0181c02d219094100c0c0040342c101d03003141001d0b101ea40d1600105211625094000500d00c4071851007030082e00d03095500701e14a803000c5543c0b00481c04e642e034002c00d1400c810616180100d2280003800c140b030011607030040d00603c81207840304c074003070304e444194841039061100130710840c00003860b0800254040c0121a4021440d48105403003001204180082400c0c0c54206000a008480300001600c080310200c4003801410346680000c2424901d4200c442c607048404801000b080c4201402440d0141944450070404213a0040f0384d03004400104100961140c10725904016643c841c0e00900e401600906000141c2400c546082c0d24094a82d8030600c00704081d145000ca50452000343c140d840041481c00610f1454a4503841da110000101101c410550214450460 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 416501906 1250 416500656 416500661
    0xd1806020a170a1b0303050412020d0e01050310030804090e010b0312090925020c01120603021c080f04090b09060a05090f04080d020d0605030106080703020303182409090a1815 77
    0xe5205080c142c4c1d0604035050080140c281101d05680c8110f605601001680c400200202c1c001d1a03569508031813103860340111980d03032001d040034000c01d070070501c040003190070640180010600311070001181c5200d00000e50941e1242881d60b8482e810599410300d15030200811100b41c400101c0c2c0898465840590001c2102c100e401c001c810400c43d9030980b0100740c6c0000c0e0b60034116409072209034200002d00001030a58042c1d000007034100c10341c02552404200058411503180f4411040c4030b062865000c0e9180094025074409200c1c6a20356611203c1ca00300650b136590060170555130f400030706041501045e251580900710850701c2001c1400113060260a9064a004203170315442955105428010070018100c1401258030a5103445000902c0040c009030442c100c0390b000c2d0195080c1804440c103290010b9100b40469045580c4052038480d18040c000342440c6031024100c0ca588481c0d10384240010800024114081d85181240f403154294201a220a086502c184101942595152050007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 416503156 1250 416501906 416501927
    0x30203100b03040c090203150405061009031e050d0207030b1e01050609040b03190201090503030c0c01210504030305011d0103020307091e0e0601180b06091309050d1806020a170a 78
    0x1445c910201c180148000b09034004010700c4411101130120340c9030101003180248d00e5003403841c040340340c071101080003420304035625184a80110420b410780134292151820180e50021400044c0c100d840d080c030070051110203270b81d00b01c1100c1072100c980c143c00e245010000501800f13202d22807440400d0aa485540b07a0304131a40d070b07020141c240c51584500705075400078494454001ca0206d0241c0202041900700007058401424641008000c80d150340801510018a181500c180c0006108024850f0550303a005240c0201d2195400142561511b0066010b5004121561180066134401003015a400142c80b03400d844000c1000070b441e09500203800c0c44005020004416a400d14001740760701d142c00f0400b04d040741c2001c056162400141403803c0308550b44101e413203a00c9401480140824100078100103585152450000741c8a58a5201e903440c25010341406c0d400a0011054a008045c0f01c14540d1300610f158002000a04056500c81056114079100168481c401081450207144505031091 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 416504406 1250 416503156 416503169
    0x90115030506060f060702060712090e090d141206280f05010f11060408030a09080d200703021e01090c1508011710111b030d0c030203100b03040c 64
    0x100559036850310a8599404071241445056000ca0304a11170402e8403ca8207034640c010102894004140c2d203424880c85052404010400c01c80300c0400c1110031000503e000b0081c071401001c0c02c0880c00c500a025503104d544100074007105014030f0195814034a07103070350030100456080710740c481c240409080410107146680303c0420607400001d40c903890040207000f60345c001c3c0d907208000c0c00e810300180ea40d00c4050864074150b510030000900450100009950422020200482c020b0056200d800305504046214003030300b81d5601c1c6801c41e02d24081c4c10b00000004e42d1030b03014140a0710352006501c1c2c51399551440c0c401c0b083c01628071940704081d40b200d200300d40d000c12032072401500c50b03c408100800141c0702030f000c41c001c0c0001188403031201da40091700d160460014020191901d18413030260200c512110003c840a1129500c0b403500c500e0740c01541807203107000716141c018500c1c0c0c00050325140da51600074548100244a24000d81400820503200ea4101da103961303440c1c0e49801c0811541c00d91001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 416505656 1250 416504406 416504441
    0x32a0824030d05071109041203230106030c0e030616050c0102040b0406120b0a050603060f0a150c032a080a0519080103060b090106081909150e060108060108070e0901 73
    0x780b0069801c4809003100f503016840700d101c00c031944010b00140803016200680005102d2910141651180e0440001c061000c503414212107441c40980300a0301003a007144005c00c0d154060540b034164441031900020004800808130790400400c0489007810340790190080110010785140f0800342501103c0c02000004003c80d17445540c1c1d00002d01c0d04d036420040300030b41d6051913103049881c50505800301c103540008110500d0b44e1280e408000c0c0b010420b92141d03810092458001802038800340d25100c101c1c4840d2180b9941035075a181c020014081502c8030040045414041c0341160b04104a11700d1941c1d0040f1150b0392050f524034203031317028040c10412a030032464016000044944c01540385049034419801404551440d00800074a04e00c24090132000400160015086990703802c0403202500004200040d40e591a44a00c041c500030401a01c1209407696803411400900b00141401400c100300a0015541048511503d807038941c46600c403c004240c0106002550a40c00014260402400e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 416506906 1250 416505656 416505673
    0x3030310050a080c0a050f0103140702010e120c0622050303130204110a0221070605010902070c1505120a0219030c0306050105120c0318030a032a082403 67
    0x900200c000c6004180c0100942c41c00010340c2080050100c80194008001c12011424002441800b92815860074105500c4031400e21300b540c40c0c3e1181c04d010312620350011900042c1600010300d4480441d6440500750f0040003e040710000204034580c0050600d1403221414a600c051400c03000003924018141d4003001080c40180c46650040b00701d601d100b96000e219210640d00400390f68050300c0000c0c3d0158101a005c080328080c41140248a19240e1001500780040c2d6207440040700e809800c89040f595000070800140441c8520303950080081105000e02003240400040084c040d2100540c024940440807804400725134060361510303840c0d400c241d6800741841078010003410340c06080902003407402802040951023a0101c5e000022545040c0c10181c0302c901c004051a0300c003c100102000541022100c203420078001000c003620140c3d80881c4050805108158042c036070b40c910344000407113200c03441a8a0300006031990008a03d0541c1803040047c00701c900c414040c940c506685805200403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 416508156 1250 416506906 416506921
    0xc2701090506182508160f11030a02010f0e010231030f0305031006050903030a0c0501020c06190c0c0f0807061104081005060a050a1a070b0c0c0c22150302030303 71
    0x2030b150021068040c8442c480003c08000c1d82c2080d170960300b80c810000805003100b101c500500c10072100751103030710702207030307035415164089007580c01001c0e00ca80142d46030f60f030320201c032159030040a52419596000b18604420f0014806003000400b20b904080000b80000030107644c440714250340119006941c6a80b400c2c05440c00030610350040310181d8902400030404a00c5038817904c03d85009800190007140b901c041d0300c60503500e070840b01c14110381c0341d0b4081200d0040400d05120313040c0901c843c04444140c408a00345900b050360b050a02003410001b915851101041541ca41c0204168100400c640d81c0d1100e4205a406030649484805461b10001000504401d00068003040c08041150800c001c2e200c00c02009401340c0c1501c10594014402035042c014a0222a078101101c3d000c7c0c001c81d803816500e40e682e645507500c00c0340c0f18a0749610200d22403804040c10f00540030b0a050807500700c3d0705141c0b40c8036102e002101002c7d5495955581e4000f1072081ba40a40c843e40c00340d50001c08503501c0e440c00701c1c1d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 416509406 1250 416508156 416508181
    0x204050109051206070c0f0f0b0f162f070b0a1209050a0209060303090927061314161202010806011b2306131b061409010e120c270109050618 62
    0x86610144103600c2002409440c01070170900302c01002c8cc8e40340d03200581341d01d900000b020740d41c800741d003200c40380780704035500303a0f20208000001000d101e1a503a403540d08401d005010581c00c009100794003420255540b00240c00840c0f26245640d0455040c02c0703d841d0403010078614013910640c19005042082800001034200101501c070010780c100c0c8141c1001c51b9030890f85c0311001522451141480329224000191038448901c08050b4280300701c071400e02d0801507500c00c45a0030f40c440d00084514004e808150b5a010b08091740c41030017824150601003800c44140025a000b00c40034106c0c64800c3e51040c04808000314949502290354201c9410742030441c0030b00d05448821104550454804059540c1140d410389201c0466081d44c0b540c148603440716428101c02d5200c1d981040c104a84610480e00c150b4a954103441d12480600060110031001c506200a40441841301038031004000000d0f190242440102c81c191003486a011440707803580c102044640380b8215951080702c804100300282e902c4040d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 416510656 1250 416509406 416509411
    0xf0c080903030a080a060918060b010512040b01051005040e06130608011a13060e0c2a010e0609120d0e01020409061205060105040c1d150a030204050109051206070c0f0f0b 75
    0x2004010701540d0b9041442180d42c070348402e403901104900700703e000c40d03c1984400cad80040103051140c40c0c80c0d86403204481410046404403000410100188101c1c1003014a246405e07805050103841c05003444089280290014000ca00c20700c10001d07180184082500260010701880009000c0440c901025072a881d58000156000741c0f9a6200e20b0000c88003801500c0c100c8001a1221956464840242c1c07207a41c09465080e04421200000032107003444001c0c47c440080d02c5500004504000c8030a55040000141000c0c0096201c03d202c1e4003000100002c03144d080e4001c420029a00c40480340e010f0180c007661f845005204c0c80c003940091095440040c00e1945442402980d1090fa200e10410041310f440e40203038400035104031481500001f800c1c50341c070740181004240e0500e2035411040c921503680010103610002e50086400c205950f000851032001e00300498410075400e4050190f141e4031180200301804001d2140290000e000c0500c6d400311446821841800100006042494101106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 416511906 1250 416510656 416510671
    0x60201060801150b040501050318030f0c0d03090203191703091c030c0c02040209010c02030a0c050a0f1802221211040e1b010e122b0f0c080903030a08 66
    0x803da42180220960b6028500f62010360001c0c0c1d084c103061800440d0a500020011010b251140c0e4813040c10785070403c0500b0910082842d0613a82e4124410410b0a000300584180c060608080b511001a038020800841d95100010f02c00700341106400d041040d541ca00e0034482401c0000000e000c40c1182c0030580e4140c0403813201e200000da03600814110102c032200969080000e0540c50b03210700500e450380040c181d01e07a0500d40030000c00d02e143c00180c2003074143e031001c95030750303200107400c0000c3d08140380301da401852440183c18005203800c404107803100d5110035090303401c3d60000350b241141c4008445110390a1110054030a25600c0e000c0c01a600809100c05035032813444052032007004d140038045e0908445040c00500800c207051071001715501142560541070000b84003d0b407035161985501005a081c030030000700011020030780140c15880100075400025040841a80020394201444454410302490244610b481c1c5007401401409002e05041c2e0600000800088003540071307000e2400740c440e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 416513156 1250 416511906 416511911
    0x5090405070603150806010605180301050f010e01050d11060c160602010603060b06030c070b0c0405040905010920060a18091a12011e180c0f0e070e0d02091b0301060201060801 77
    0x10444c0d1031032540c0c0700c3d03845801060f40c003560051068034420005030102081000519900c454000000380c29103034202c9003030004000110041100b00100b0780c0c101e00404095503900c4400007151500c02c880c0142c0e00c0c0603070203018009100d4280d003070200f2140c12412a00120000825210000203003e06124402036070001d040c5151802c041c41d010003224000c013894020185000d507283e41e800c4d04114000e0010f80404418403002a1075122030003804d81c928401e6000062030700961400303c21306032291030782840303040950341d034400d490302c0c2c1c0000c80300b15545905115071901702001d407048075008203030055402e2908041e180700b0305552140c0c1907041c041044515034110002a10941d0880c1c0e01c01012010441c040c0f1300c25071185119901880459180e0a03400403101401c0d11803150281d07071070b40644640180c2c1c41080102d40302034104140c011840740350480b0846040e80c001880034100c0c04020344103907030180110791681c500701d040005107030310503070259160360b03594001030300904092088461950 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 416514406 1250 416513156 416513171
    0x90e030a031b080412031d010e071203051c06030f11030d0c020a06110a0f1115040f0303050c19050c0a090e030a03052a0d2405060a0201020405090405070603 69
    0x70042c210300c440528650350341603916a1940c46807612540e19400c2a414542c0d69412040101c80b106002e4445806440000c100f0424441180746012804e274010800360515061300701c0043d40c03040c02c8454110414440d2855a00c5204070000140b40e1030b400140207126550701d01f410441780c1441086480d1044098401131081d8000c19030701340410b800c0096002c007004009110aa0150000ca40c2d5083c0c840704076918072809a4540070209013078041034800400800c43e004080c90508080c80301d0005c880e11190a02e89460400343c0a10507a000c01030501c407020803039078003c100800c4880c40c050084045144447c9650030f0161f166160034042c540603034a11603000ca41e1040c24000c0800324110200114980b45240008400422002e4200688446510400e4405055031014401d41c0030580500daa6a1185034440d01d0884102030307010306042c1e00144052080321b81c1c44070301e00112041036400c2c1d66902c641c88012802845942c100c0303a4891441c005110a0110010b400c0081c0d6105031010400031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 416515656 1250 416514406 416514431
    0xa030e0907170a1508030403080d0506061303020402070602071b060f0f09031e020a03141b0105030a0515030d03050a0b0301051612110307020d0917100b0a090e030a03 73
    0x30060102a50100b0002004100070003420303840221141c045418812480303803522406410742c0d2080c0d000f07a41c01d240200d01119180150310406400500451b0041d2a2004248014403000603921010b4411940450f135081401510f4049a409a610900088042d541041c07240343c030554031301400c000108404041e0300014000d13a220784806000b900c1c0d08600603d95038940d1019100c071007000705815420403040c0016240c0410240255100c0c2d0700c680901c011143c3c82070329003141c112100d401505280346088490342c1013400c41f13800210517007010500f50f941d60b0301c0034100880400072582505c12030007890105641030b40f1003400307441002818810030120000b01420380340c055906080070022200d50000c010301440c403c800350401000046180030481c034000c40070782c10444500b0b0141e001104c0591203a076208210002411001119503d80c035221140c1c3c036582d1a0141e112410039980341d440d8080759440c05003070401400d22100911181000088680e100d0300440d10040109045c0b08000020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 416516906 1250 416515656 416515667
    0x10b0301050705070204020319110a080609010f14030a02031006030215071112010902061602030f01050405030301090c0e10050a081302010822060603030806120c090a020a110a030e0907 81
    0x2c401c103036035007801e10f2040e4081200952020301409000c04054006000010700b03070040609a520841c10b440c0c46000c10003000d00440402000d25100d08507110040c844020880f03020780540b1030320118040c020f18050086860324a180602a5051103012a0700710b11454542265064034400d171441c140c220911040341c401406104c800400300c05000015520a05000081e42907518030356001151560040d00820b0b11984040051080406201d000c041907050400008003410b581500800807864243c40c1d01c1c4c2c03240410300601044a44860500c4aa82d02c42c0d408550501002458900c072007440d07080142c110741c0007421080125500038009405810641c030b032004100d0301070315585000ea94445203818105250300160080c901d086081c100480d01500c21040238521030348036100c20781088001c0090340300845451802d0360348814510903082d1030302c050080e00b0144440025031241910340c416035a40e42c02901c00201c0d441030049402c14994030402400c18030700d094806121544403410225207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 416518156 1250 416516906 416516911
    0x3060c0d0b040b0f0103022212060b0102060f06150c01020f0a08090f0d0e18070c050c031b0906032a040b010f0c030c0c05030d020f0c011b03050a14030106030e010b030105 75
    0x280902d180c00c1065081d40031f500288501801650458200c88068054203450015908411215103100c2107502c10840307644201d5a0300c910900003001075240045c2100b101482c000c00040c0248600e02c810150001240c0565507085220300095495004001e00c07025a508800710100c001010500482c07100310000c1070b08401d003401d48c40a49540b030013809065528401c001c20301500440c0440440d0034017030302107074440d0151029940c0d04001c00c0c0a820454900405e00300718601c01c0d04094280707903080c810390000341c44901050701c081603d699800b0000e4200400c0b41d0003c1c5a10003850800704180c403420000b103128500c11902040281782040044501c1080c64020802041c11580e1503004a1f01440e110300c0740f01d10608540d01051389620100c6d04003a900c40b8420f01692103805030344464003060044c5a104002807801c05c02d0031024450b904030a00d4440c20140902800184050b02607108126000e5240490000e1554030b51350745a000300180140d400140c0c06510b4050410410f28041c0100c90 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 416519406 1250 416518156 416518159
    0x50901090312021603050c10031a0409080d240f0308030c0306030a05010f0c110d02190507090911010f020111190c060606030b0307090504031e0e03060c0d0b040b 71
    0x141141590340e800c40c0452121002d60551052200107a844021200d035540076602c10030240c007171140507030144075402003103498000074541026426091404000305030650710900310703400714590320030703081a201520607908400c0d5014103006150810310a941c00c1420003080443d403416407a40d40301400031000b0a2800010012001003002c03684404040c00910f400c4580141075800d0751360b095454500711103080030241c0d030451b00ca201d2145507030b07000940e0441d12022517001d0914003a642400075211150202880b10204420b4110310501c001007001c000038042c020410030503031440f030070880000300d0740a910714001803266411260851040c0110400221201c00c1d1034104848003401c80d0120324042101010040c0d15000c1d20702148040c050301c3c00902c1c3c591070024030030103900113050400000d500840200741c10072052000203540480e00406a40813164080d0701c0503030510741240e4060109407200d6252040d0400e000940c42ea0100501444000030020884200244140015100180d6005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 416520656 1250 416519406 416519417
    0x904020f031614130e0c1c06080c04020f070318170106031211060105010509220e12070308010308070609120f03150b03010b071a0a061409010e04060e01020412030804050c01050901 79
    0x5c001107622008940d400082c2c081d82e19040c90b00c0c4621040000b84040c001102442d100c5034100840d6200b4002205043c005a41c25440c3c9080181e11108034400d0707040c01420805c0e141c0c4144560400603c180d00a0078901c40e031900400305c160f40907400b030641c6000a40e014100e188540244038010a14021035180d50400780c00740ba0b19100065801d60800481035030494240c07002020f403280c22140011150f08000400121240e41030203080c07401303e400c500210131000400c070310404030f900040c1a44c11a0340c0b0409955440f4001e1a0203006071040400040201c2140c00a650080750403403440810f80d462a5010005c0700940802151440641e12911000140800041c08441030b40c60050103030724010041358001c03c0c090044022008030031181d103123219680344002c1c44485568500c054404200322a100d031194108460101401c00203000103201b80d50300c1409054011081d01910002c110082140c0d03c850110b05026118120031213048986000d031070a6622070f0b40c055026101d5258069489 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 416521906 1250 416520656 416520659
    0xa0f0b0f10030f2901081b0903070b07260406090513090b01081f022b24030c09060e040201050a0903150603030f02011b03020904020f03161413 63
    0x5014480640003101d208064907000058407903056405000d0f02802d00f03020000b0407240700150b101070b00002c0c0c500c29040085000c188001c00404004031074a440701c580c3c0050340d0301c0745000000e00e0850503174000d14011002154200912013240681c061044803c0a40c06202c84c40a00507140b82c46140981c40124007202810300c00c40c20a0000c04203504110540011521415103a400404209900446a55020240588800a6034241d84c6800c0c07052030401d50400c1141003040d02c4c00c4c5035405032501c9014142c2d402103034001c2d0b59041400070049041420740d11a1003500303c60700c5260140410750b094411b40c04001000c502c54494030f0101c5141583c80082a00c49600444141d4450250902080101503000c0080307580e40124501458a1090000b0050b00d1494054180c810b0012044156454001200190300c0c146106400c3d111407842c0045c0e44000d4a00028020700410424164400000c0204031007050070140ca8900c03881203460310300c90181d01e240c401c2d206200e4075240c40210740c2001c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 416523156 1250 416521906 416521909
    0xc0201090614070c151202090907080916080d0e03060408221d06130b090403030f06080f07090501080304030c0e071205040b10050303070309140a0f030503030a0f0b0f 73
    0xda4510302c1c021842c03a90700d407590640340c0340400c054a4100d84029941c01c461042c4258000f080c82c036050302c10074010360a01c84114002403451400510300c00c02e1120350000030340207000502928280c5100440e444014948030001c0395a81e00d01c4400e91070101d100d141e04a0300b2441c001841c148113941c4545098075204d5441c4410304000d401c24110045409a680045041d2011103024940701024600c8141c50b40751481c104041030b40d484107400da580340703800e580e0019070300d62816403503103d609418046514405800c8020091101e5442003404d0300940300c41849080c00070490300100da101c0c0c40c090040d80d80f2840d10b0f640341d00c83c03403000038281e03104000f04100380102a10318a601204505010420041d107960503002d4800444007200e806810000b08130020100f0300340040500415801581800801e6401030514880d034006d55171814009181d04805540b20b0330030501505862190242e52070760717440c0859a83d0820355445007503609161007178507210110320445040f014020240420079335800e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 416524406 1250 416523156 416523167
    0x1e030c15040b0c0708060f0601080c070506070e1311130e01050102100e010f02030c0310060503060d0f020f030a0b040c240c031808030418020c0c090c0403150e010c0c02010906 77
    0x2840303c511400f80c2600011018020310119105804002c51213480d85041000100f40040040130403400c96010310074540403d0000070100c0d448540c0c0c3c18800601d602120004142c0c4044140240d03071507081000001d80c103032004018007140d90104a08091b000c0e218480610780c80c80900409005038801203101060203c59007200e4030b1911007038000100301040507485400c0c0d0b4412034807011690000000d00081400b50001400102024506a03041d4102007000502c440244000074010409981e1040d0540d600c1c000c00c3c5040d610014102c62542406241c9011650000c0700e090b0385010043e000020701807a840004a010303945a2540c10140042c0d10080e90012030002d001c1c0d0420200c12144003442d043c1d8030b1a64040d2410303400654443c0d10303000814952407100341070351f00d040d0f0052104000c1e1400c0040c10038181c1100302c5021845a0310602d2100c824001c039400500700d102d0700020404040800e60000c507224451070b00a020a100c1b10006070790315850148020b0009541e02420021648201e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 416525656 1250 416524406 416524417
    0x20d1407050604080f0f0f07120c021c1103030313020a08010b03060a020a1107090b0a06020a0c1403031e0706060e190506210102030106020d08090309100e1e030c15040b 74
    0x2102c0341d03400c0a01c0b403d107400c05030700640000000950006201414005415510274240e01c041c0707001d81e045001036001c6a0840144035001c441c0d20070440300e1a04008112035004403100c40501241d8403450400341034426040340e0201070b0700605440c036000c078a200b81801004032041020340141400d882d0a044440298060a0380c8000c100405403035603100e80d002c0c00300ca00146081c036008190384172554204081125194071090640d400b4030846000140c0420404040701e0a11031622445020000440d045125502a40c201031130411a00c111140586005d00180d80c007840f020465903441700c17482c00103203005640e04418070720101401c04600c032564208a60015020f0150303000030300300101d5070140300c5c915800c403050799402000500000e43d0400450703420303480718541706000b17061600c1182d40741c0c8104000320780165a806900c1426900841100603034400143c0b0310301102c1440110307c0300000d052102d00e0b12030301034540160000c0c500708482d100580301e000603080c0f4052400c030075074205d60f106 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 416526906 1250 416525656 416525677
    0x201050403120e090a02040e040609080405090106120513021305060a08030a020703140d0f0c02060405130e0d11070501180911031006090b03040b100f06020d140705060408 75
    0x1000084009181c0b0310603240036003040c0d201e01400150240410101034402003091910034414402001800030700020250415085000054510740300c1c20404030b80c0c412034218a030460a403d00000e0729591101388410002c20b012410440e54a5400401074030702c14401003c1d500074156203440111300c0c1180c0c09075030040c000410907010b1940c0c40d9041420750304014200d8002d40c01c021800c0090101124082701c5542a40d8090120041c00c850058003020401d0440e204000b6410b0000e021074503074104a502a182c01401891105106940100680070305520392586010b150708020200d405103000d00345030082540648011402c0500450700307070b10741041420604800c1c10740002e06c00a00d1044100401070265880d0340ca15004840c4980099a540050100b05100c64208a0401c850781644e400035070100c1c200310b031b031707201e0b42c1138003000310440c0d08900c1100c00f240400044a94000a641104030074903181c900d00003050300e4400d032207405440d90182003904450006000500d0140052900210 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 416528156 1250 416526906 416526917
    0x2100509040939060c1b08032703120306190e0708010312080408041401110106080607020d05030615090d050f0d0806030105040309060f12090f0314130b03040201 71
    0x8040d00c0342c074103012005007092a540d5080d003c85030440d03800c2030b452407982c12001d00c100001385081c07001003103160100030181c8105c40c04004a46c055512403105c5c001440a9001c4903120600c441581040458580d00440740011064120103582804188a5036030000c8001007802c5170b0b105010301107800901c01101092846c0703014081b03029400f4072681070044800d6507601c40d0700e42c1075203420602c8828201001c0d007482036a20030040010441c40440303003643d03021140e4000c00c0c4a00001a070b2071040c041441411035007008008140c1407000102144030701025800c555036605451825220342c4019034480e03130003010005402c80400c040000034006207001070183da0001c003154841604190201d0207064858002111045206a1004000f500554220000c200f9428160340107000c040e806d228420500000004110f03100e4003481d185440a40844807e022030092407925081c2c2c810000c2045000c0340f80902801d2030f41c08481c0a5500b03898421448023a420f090020407103c50704000c3c0124100131 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 416529406 1250 416528156 416528171
    0xb0a060f2102120c1204061d0f010e0d11250b0c0303010e0a0c0512061306031a070201060e070e0402090a0801090515072f0f06010303110105040210050904 68
    0x20441c0004685220345410050300da0941e001d144400f0074029004624540080c0304850511044540e020740156000e840081c0c0104000040030038000c240f92080c00394011741c00c40001c07082c03043d00000c00d141d11000c20f072140070b0352a840c103807000100e0341c101c405070343d01100382026001854115245080095900d8034022641c0c0e0644100b0b13030b40080c4040c20107800200c010001000d03030380310827038224403403910601c66242d100d11300401034000c206900c840200d21b880403500d942c54034001c82d02c25084220060207103684908045072040c6c3c0c40c00f00c1204411140c1c0c00144124418401d080c29aa038903203090000b615001004c0302c08010141c15140c1c8594200480e1200ba6294165000204000000860000900d00f011070411180341405c08041c00306104125005520003c5507200c202001e8401c035110094080311212f11905140c00280c0c5d02c2024042003006c1400100c860482c1d1080d500c51401000b00d0b40c5d03050030385005030790003900004400000784d8424050005844c6500c0085c3c800141c81 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 416530656 1250 416529406 416529437
    0x10c0c0228150e100509040902010c120e010816023019080601030e030a050a1101060303020604050609120912030c15010f0b04051014040915090f0b0a060f 68
    0x400c80da8440b1060403041e8140807040e41d0040900980034004903803191054030003031009402803140b0301c4514443e6940f00702c070508680c09403411400d0550002111034180c0c1c00c105010704a03140d070788000c9020503403140018403031100700f40c01c1000103031003075007d400e003a070510390750011220b003808183c03005040b9840007280896800707000c0e21000c0000400011621150381340904400310141072603040506112004100d0355002080781c81c098918a01981e071200c0541c03048514000b1f100c0804150b500304900001490380c005841c9024900610036124941c0703c60a940e03a461640c8251700d1011303102030203410680d2800180d52215181100d00303803031801c0d078680840d505002a040d42c055080140e200140005a8420070145c09800011149442c060a0400040c4007515400c005005c00200700d03201440307200901e0079038008141da1201403094843c0c1414080582182d40900541c2030326080900d102e0748050f00880d554000050400c00c0e08505101c0201c0b0020381e251202e800b0b020840030f006561 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 416531906 1250 416530656 416530729
    0x504030215090d1706030a140a0803190b060a0c060b06120906090d020f0309060708040b070803160503010521012003060307080304080706050304051005040305030702010b03010c0c02 80
    0x2900702e0005461070300c0c5082d0000d00031000c804c1107965003c01807004c000070380d00d0010390800040d0300070104201208020b0066031802074240c0d402410301d4000310600007846000040c40544040c40001440001c068405126080c0617102500e40024501e009900215013141c3c4a4944140090310041c9030000c502c10340002e2800a4540c901598440000c0006102c018800c40608400300d101406070aa8651032450762030103407508051007030000042010802500100300e0b80104075180119403296501d0510500a400460b1016800075801d00c101400c14818001c4034142c440040c4942030601c917100d2540d0b0554040000c01489660b02e0640c03914240035808000c1060002c089055564500310b0140744c1860121340c032a907482c1d8424041804000c0020400f00b00ba0703031740c51820680703070303562403c4c150300c0c109226042c442c00d40e15003028441855440001584507030350fa80c0013402081c0a91301854201e074584801c460024003018011801490805d002c0c480d01d640c10010028030245a0040018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 416533156 1250 416531906 416531911
    0x9070518070201051f0b030a0e1905011802181e09071403150c07110904030507021e061b0f0114040201120b0d1205070b01090e0106050901050609040504030215 70
    0x2080c0c841040145281e0309005140d40700c0201118048100b8000b48812013218950160002950010000031000c040a0740030003074000035003044406004610300071a0204001c840240d5040d401c0c182c5e62141c4100c41c200d000c21880c1d0181c02840f200c1d00f104491140090040c00e14451f071540b465200b948055036808446c0a040404041c0c03417411301d130419003041400480d0409010390084940c8002a400f120a01c65024280c600103582d03e00c06442c0641c1c1d0101030b86c0420340d100000c80c003808181948400903085483c400c0d14003810b085000c3e45100010448101c620b41d008a040100c1000c0304030928510524803203c0003142d41d07080c840710301942500d1400c030b05401000b0f0188100801d42d03a1000064046075140642000a610b151000c10308440d12041c01030441561044e100e00b08900c2082181e44150b0000760a038207a5031103c82c003d0162601160701c0c20385600740b803008143c03450306142a0b4104c6400030b01052511807050180000740c82e00601c19001d60189150804110048400300d03803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 416534406 1250 416533156 416533189
    0x40f050c0a2a02010c0201120207050c01030506031501060e0a081b01020c010c0308130c230a05011b0212030403051b030d0305040203030913020922050f071205090705 73
    0x140c54184509008101624501c102c6a100140410000051160264500c20300340c080c640b48a00c0c0b0f8490005075400d822620300b480c5800e00c00100c0d103040c01808164668280803d03a4203104039110783e804c0580e81c3d40103a18900702d9440380b100410040307000754140000050003400003046103944200042c20000030010452858243c0c4007610901e40c2c2c18400c04a8280c02420243d241202e65200106070f45001403175080c03401e2980c2c0802c8140301c004042080148a180d00030442035214451903c01b686507019414000c1a00317090224056014070784c041c0d0561342c105c104681c41c40954003081800a0203031030025040c042040040089503040c8185500190707180380c011641c40f400f1080c50324003052915100b00701483c290038000140d9000c000c4882c3e0500840704d01120403000380e1070302d00900c00c41c0c407070702d500440300008100b0182280310402c000d000861010401640d441070170104000d411100360b40014403d040100c14031307489500c0700e90403103c890101c1d00d0b40c07030321640424140c0036042c00b4503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 416535656 1250 416534406 416534431
    0xa1d010801050c04030b0406050705071218061d0603061c030f12021207031d1b0a0b0906041a09130204170714040c1103130e160210020306040f05 64
    0x52005040900403160440f581c8400035203041d00d5919403661118000e080242055240c1002c507040364400c405a900c0d00b47c000b81040c000396240c0744040c01811000c010014121140800019440c0c0030b00c604000010380c2460700f25280c0d80f0324040050940c00103260507407046050b040f030f11800e80320140380e650840c4640c43d0759852482080c070141000424124000950740108901612050a460202d4100301c40c0e060100d102da0040d01c4906041c241c0d544100c26512800d008030402005800c0207001080c0c1c240d603c031001c90b4813003138a040e49105210340181c204008000800c0403030400e000c8030303890200048503242050b10074400144c0c0004910351116441d03402040c1030088404c080d8014400440210042003418508010000410b0400e050300348a0390392402c0d4840481d0142040c0032180c000c40b0107895407940701074021040945913000d0030703082d00c21100025481c159811021281280941c00400c81e420162216002942c0020246600706884041400d81400d00c0c0c02041e001e80391a800c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 416536906 1250 416535656 416535659
    0xa0e1606030b031605010509010507080d050408041806211703070804020a120c030624170c1503010b030a0e0a050a060b1c121724012c0a1d01 62
    0x3c0503d080d00d04001c0c02092502c070001004142e820030121590000f0030700f8600d80303c140ca0705010000b0700411340c1d80f80c6c095040c0010082004482802041550103522081c100004840c4907441103401600400c8101003a02010480d41d00c208800220b80f60310030071103c440e100c0800c504500a4101b9107104011403c0401400218a0203203c4003002d0042c040c4000c00040068442c06a42c2c1028840a07140300c3d990b1240d05070500214604175420a600440201a50b5031101d49101000b40040c0c4000e06000f0034851030f0444c074101404048090707403500b45c10308507400d010185619600140010504555452010f040d010b414824000960b004501528503811a0700b406070030b03188a00740f80d030b210300e000310034540140e10030005108081742c001025003a40d40d000034060300d13101224101d100c2e40600900c10406042c00104520702c103139000b030040380804581c400c0103680300491001c90341058035840d414460384540b0480d102180110042c02c6403089903031504c01c8903c40c0340d00c200210000215000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 416538156 1250 416536906 416536909
    0x901180f030e0105121605090a0605090f0f090403120f0c050a0f1e0513091107060e010c05090d02030a0b010f0e060a0305070e07170a1406090f0a0e1606030b 69
    0x1610a4140b03020308140b40b6103034108090b681c020f80d00403c04501121119012150b980c45101074034682c2d01c0140446007500c0d2104800b404541214454a214410100c07510b8010b041c510302c0440481c101800d90b00042d1116a425103c41584001028030250380b000c410345400d0b540e02600341030301d07141e0704c440390303038549401c40141036503c000751402c05c2c004c81048458091428428402c01c0310311500d8401d03151860340c0300a601c3c020503a03104559036030400c812455410700e18801048224070401d010402c202940c5030290907100180b0404022034400e0040200c20b040c865241c80080303100400f51856603880d0b98450b0708206007a0002840700b01e803548240000d0025901032508810103d494840c0b940c5180c0e20f20b82c0d2880c850041000710325101001c5a1018040d01c203150f0b006000904503495443c06c04e100c5e0000f131030488400741c50b40004c41c0100711603085c2641b54501031580d82c46100000c0c1d55400c0c40700064030150f0301c07101082c4074100740841e1001c1c0c0380301c091015008660300898030400e50707030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 416539406 1250 416538156 416538167
    0x120513060c0201050405120a0302041d1006020115030201030b0409051e0f07080604060e03040e0408121f09020f12090a0c08032b240504060b040503030708030901180f03 74
    0x400120940e813501d0300b440301050340092580c0060b444030004603070390100c0880c110007030301880c0e10444201258800c01400c1112808940340308840c007080450249548110490907642d842400c04511044040140055403080c1c000d8150880044e20102d40c40c1c03000c2e41c07003601e072044004680355502d0100b98010225a014070409014200485c001e102190031700c3c05c0e45881d0740d03015100074019a503464034001c02c1c00e003d00c140d50081a0a00e40c07240c05241034185203c0caa80036035050780148152000040d00400b101c1c110079520500c94030a20515403d1106020096000740d880420f92075040c0311040305219140e411501c20060f800c0a04403001661030004900d11441d006584590001d100e048130b00300002e899415552802e0190701001312140c040c0c1d400505202500040800066101c034a80c11898541030f01220400d0f6002c100040d69251018068040e074003132258141c02c20884070300407450380c0c8080c44e002803440b00001044908007030f8092035007070841402c0350742500089002040c10b4000c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 416540656 1250 416539406 416539421
    0xe1e0108010c02070b030711070605030108010c05031312110709230615070c05090c0a11031c021809040f050f01051005010f020a02150408070504060501020c010c0312051306 76
    0x200240440e811042c0d0183d154103450190b509528000b10001b50718a02c60000c0c1ea03500408081641d611946580005000ba4000d01074400e00d582414000282103125001301c910a8442031500c4a441d0304594900b6400e41c01540c1c60000c1040391049010351042c2800010001c04084000013008070f90552201440b19481071414442107a660401005854080224445410110840c0d9861101d490718400e110900e400090700126110100488081240d0040c030020807103403a0b02d24200131210f8000e681c2d105902a030403400d070072035007200d00350307403035030300030f000c2e0303681d8490300004100c0b02400410042d0a044078103540709100b1410903818010188601503a81c00040024000361a100598829070030080c80390b01c0c1009011250b4008040c8244008414180c2c002d140c921a031912a4040104e07400038015a0002d0180c03c0000900d031506100f500125003060b0040d04202d0302500042d500c0b040104825014071070904030095405000e0301c11030342304214400e1610141c0388142000c508a030041e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 416541906 1250 416540656 416540669
    0x8070c02121902040608061302010503040606410a12080d0e0a0b0a050705070b0c0706090302030a030b011b120917010c03050a02070f060e1002030a0c080603070b0a0e0a0e1e01 77
    0x40908ca0124110740105a880c8e4081c03c1c419030301e88a40c41d140300142101d501031100740384083d812520003081e40c0c2207580303002c0d812061040351a959007031a0b803591104400b9903a01c40718004082000001d15400602c2440c02072041d40d0030b10340c2800e01c89050f5646250034542c01d42002c1c080d403007088400140c03141c100c0580d2500300300c02c0c5004800544180304104001e00111907600008883c01c5688046441c02030703000c2c0c400d010304030703891501958a03001824a0404030741032248031040c0703510640b00d099450640c4042c1500721141074032404507050300e0440c000d041100e5a400490030580004c0b00c610401c02c042e00015102c985c1c60001000c4480282031030360011300410202c000b2685103030b8a5640c2d07941000c1c001604003c1c05004514000e50403030011100c0c2e0001c420425202d030a9404105034000c83c0e00d500445035641800c050f11141107000e031080e0294140701000e47d0600c20708140403150406400400001d84a032203d03861040110789a1440400070300320355411150242410740107065 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 416543156 1250 416541906 416541913
    0x51b190e0712060b120a0e0109171605030a020615120a020f010207050d0807020f090c0301140d0204110d060b0f040605090f09100303030c020d08070c02121902040608 73
    0x60008514036804007400000c104410007001e1556034802d54003c4000706031426902d40e071844407206100c0e50060403108080d10520b820050304026006004d158001e0703500000c2c11040500c01d15001c10140c201007680c00741b810301144c2810024800b01300401304541d03030760010b19013440c1c010000160044107641c2c0b9801002080000e400400000513104840c0ba81169a150600c035000c0040b0b1409245921156100e540c0300340444c1400750307500c010032805000350b441c0f013100c00c000d01c00c1c08500f410980b101c0e26246020030040100303241142410411030700c018000b44180c106500000c0c252604003840c00441880080d1100c0e0b107031401c0c46908002c0c400d0b8002d19080248d01c01102a03940214810384041c08000108142603903a8103808184000004010720917a0610f50a00040c0c0d080c103000450102c3e10380071901c5059800020f000d810104240c1d180181580d6840e02103c0c41421400101d0b0060b2405843c80b0324540c003400f03032800f01c24881410300540b560500420060b10f0041c2e104255680 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 416544406 1250 416543156 416543159
    0x91a0715061e0906060906050a0315091d06010509130618030809010b0f10050f07050706030507090f08060403050d0902041a0114040311061b011503020a0e060901090e0a051b19 77
    0x51b00509001c08039800350615903200c0b01e070008190f0180101d6004102c98942032031000c204c0320584e40c49104980c4114040c1d282c0c101c6015001a0785203028083c46502103a00400100b59100f0516402d102c548132380c01c04038501e018550003c0ca101327081c032022404501101e0820030104000d206000307441c074046a0121102da0048089010629460148003c110000860300c010140140859001e580c0c800102c4400766900d490080080c00d05071084400030b550740a0010307205043c4818041503448071380107891691181da4050b6490790080242612840d190209d5001503620b0707100d5205560b51045845524a000500040c8002d8128a003410300b003406010a2020803480b11001d401c0c0c0038280c030800c1d503440700401003600078858001c00481a60801a000d0860181d10724a0822644207451070052140c4644000c10180802c40c5d2940d00800d20340010081e034501608038408a06660f0f0590b59203500030703140c070703420500c260820201c10f0445440c48000ca0600c05e10720018180c50100440406 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 416545656 1250 416544406 416544419
    0x303250c0f0209130507090f0e030f120403121404030f0c05071a07021e040f0204030f0b0402010e0301060906051305010e04030e031e0d02010c091a0715061e0906 71
    0x162400e04083c2c0030721030b5800001c9901210307a1aa040c0c09030001d048900d980e81d5030f00100068002c00f03003443c20550074030050728100b600000659a010140c583da0604200031000703517400c10040140241c1c00c00c8020300210f480e0031210700c40c1000100c4616910030b40c52600e414054004109007014004111100240c0d90200380003044000079600382070401c581040705a102100c99028441c1301a40c0283c3c441002407005040c0d00d002c5440313020a80c1c0c14080c000c04603243c01c080b800b50340300103031943c4281c5150708009140c070281281d000740305040000d400d0a80b100071a08503031064026044c4d0341c1c0d6038503091201c0d10746500146511050a00144503540c1060081c2e5500d5070040c100609014043c4800c55040e80c1c180110302140000d4120311340307800c030b114001d0f070780c1e6031002c61b0107a0165190880032240c482c4614814000d4421020240031610701e00e01c040c1c209a0b0129006540d0b81086a6080500707030b045010704030040148000c6c4042d10880e00c1e05144613154103600c200102c910b03284040105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 416546762 1106 416545656 416545673
    0x1103090105130b0a020a02070f1203030f05060607150b100f17010806071805040e070302010917070603020903150403120629070f050303250c 62
    0x1d6840700b20300205415030b81007000c2c203100041000034107600c00580080455601500c11524203076035422030500040500e4003d0030740308020034030500625905001d000180750301104d0400c814101000016010704c54140b0081040c040750200600b1030364964010b02110001804441c0d241603540001840702d080d030081140803071340898001844a4083c0300d50740c1a41c40c403800a0a840e1100401a00c195401ca05610440e141034440410180c94074002c1e640c100340303084014803190f401c0d480050030008050300000500b55003030421b140b103840300048d004115521802d006a035416000042410070b660005003100400c0020180301c02c26a1040c640300e0070080400c0c0800c641500d49841c04029a4051503424900f0045000480c006480d4802014264403130740e1482240312055466270f0950300105c1302c188514a43c14174001c0020461910318081d84a9442e0a80c240b107001e5541180 = true := by decide +kernel

theorem cover : BRFrame.Cov 416366906 416546762 := by
  have h0 := BRFrame.cov_init 416366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 416366906 ≤ n) (h2 : n < 416546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
