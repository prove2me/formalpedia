-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4855
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:57:06.29826+00:00
-- url     : https://prove2.me/submissions/08f5eb9c-9278-4d5e-b788-8d0cf618742d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 873021582 ≤ n < 873201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 873022832 1250 873021582 873021593
    0x90204061718010614031504020a03030c15020307050a1b020f090a060b07210c050303131403160b01050a0605030a090c05090901150b040617250c1b080703 68
    0x120392210000000b036940908034500e150840d11180c2158007005100d05800b80d0301d080410441c2401d1080c6038014140e81040d400180d41e049061000608120080b001b100400005203402c0d140e01091142c10b548a0801d0a07018003c0e40004c8400070025080c50180031462081e030384080000d07a0058600d0001e40740b0307a000e110300004001d041c51072132030b10f0349030026649100a00400c0468042c140c0c802c1d040c0c4e803e14880c3c01840313200042008105c1f0b1650040e000c540080112a000100c0180004100c0c90900c0c2c14a0420400c2d070100109000214202442c20381c0400e409100301c2c89005843e100340c1c1c07140200280c02c0028041c4c003000503002d01c0000c40e4a031459102c0344d00c45000f100700b100c140780d9444c00100b01c1c101c221112041a51512074040058a0a602c10b030f010f448919a01e5083c641040c0008065420440040b80c0c240d0341c04020030505d5503440b00c1c8030b4480e021180095091681d8800107445145138903802c42c1e018030740003010444a584040710700195a0000003420030f06103191200d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 873024082 1250 873022832 873022877
    0x501142a01060503031c050f070207150e0a03050f010606110c040b0a08032113020d021915020d020f03040819030539150a1d0a0c05090109020406 64
    0x340025980c8a801180980d400c0024208540914040c0f0114003644440c07101a0f03600503041400300c62150003403003409a00401c003807080e034181d007203204c0ea500005402184c4005034200c500ea0004428180031040c0300e40811082c100445000007408015910002120501c40204010b0b0840d0040300c4515921328242c0c001c030756501d40c014251180151620455070a65011560f00c0381c40c123081d101c0c051210400134800581c02004000c2a10540400c1c1d000300e95100c04000009204003140f038502c015800001d002000602400310310b40d100c6101c1c2c000080d644842a00100b4090700c61180d94842e040030000c00c070707002ea4450034090b03c00e02401140c21401c002400c0421800d11100380003071289110b00300600b0460040050150b83c034000b81c1032000c100903c0c0724001d09036a420081480b20100c4400b48207e801c4081c034030000640f00044c0090502418802401100c90f0145640300c00910050406440030340310215404407099907213011001c100d2089210701400306442d0411103111004032101e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 873025332 1250 873024082 873024157
    0xc0f010201090507060507140303010e1b13060509011701051f02031e0403030806241305090408070606050d03140f07050d0201060905060607080405040e011103090106050114 76
    0x4100300b006995440d00300301003a0072490005001040c5401804142d400c90820446020059031455040400c9241144402032042c486101c1ca00d00300d0040d411007008586c05042c3d0781d00f48500403611018014401d82c4070b82119400944440e40b40c000041e4900151412070b40000c00d41e450101081003007011a0200030b4141c408e500043c440c0c4034103103001841e00787c0255806040d040e502d500f50320b00a001a03001805641c003519682c28486400b1780e00444864030700c81481c03a82c513259500c1600b407004054442e00441d0b0009220810f200030010300e40041c0100074885d00d0203103d50380d2941c2c10b0190500c034840c0c000d00001c101604094050036680014a1040038001c0107500e0021141c0300c031850300790300c49580c00c0140c1d503528041107e100188201030300000125529468104943c0707808405002d030340030750740c40349541d090b421a966a00350f004911144401010035201d280c0303409010b0080280d4032840d03003c030f1448841940504584e0044901e400d6075a0001c038401c9101c9509003081000511 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 873026582 1250 873025332 873025337
    0x40b061c0e1c0c02030d0503151909060b091302030903030a0213050a0803180a180509030d110c0c030a0209150315010f0807050d0b04020d0c0b0403060b03011d0c0f01 73
    0x20000c900c150803010b007039401e00056485042031000c06205042c6800450a41d6504000d414814400fa82d43c880149101034902251401810013040024900012169200d0741c0e0082c500030000802c00207160180c0f00c1013030121018080e00c1e40d42c12280d0160b21048036191780c26041040001d142aa0f0303507000c0d06040b00c2d0700c02d2001d0486c0c0c451001c0b46c8080300c55000301d0300310391000c03418040d140002e41d00c0c042c1d240401e499003103559250448907034460151b81c0d00707080550388a400281c46503a080050301d13a4068a0702e003c0c071014482e4910740c01e42d54041e02902401d406004d01c01d8101d4100064452a0980d000d07000542c1950784507405501d40c50740000b000e52500840c44100012075030f00c2c41d420b010744650038003804500d10f080c0400e80381c408207610490088520468000c0480d100b045020751054065410981000d117515142003106041d420031081d00401040100900c42c10b50f002c5100d54400b9002048400d206095034001204c0002c031003103d640c4184a50309050400c490100c100c0c02060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 873027832 1250 873026582 873026593
    0xb0a090501050c0912010b0307060c1a040c03020102070b0a120902010c12090501020c151213060606090501080105040219050903030f12090607051e090f1e040b061c0e 73
    0x90303891a007034480c01d490006500b100440c3d0003031186017505003003006034502e500030003280b075011000ca5106c2d0702600c0340005120b1082ca00c2800d2240c2e0380c8500c24950704800312881a0314080c1740c00949d00c0d42d82e0006a005115070407000c83d1200410040300c000c000540c0f02c1811b0813030f940b201c1c03c02502804070106d04101090340d218001504200500741c1d5007000352190000f860600b0002441c103106425810700c106080701d1741c08038080b000800c03541c480b8000040446a43c0c0c2d0f9400c0821440080807000b80080e140140006d04242d101001509540c0242d071543c82c00d07680c94040205038040c41d0200340f8000c5907202c0c007191482c02200200810131001e400e486c10041b107808003002a400100902c20946e00490070480390420038840075600c80c03400c2c2040f03410201d404a00b020b001e1b4180995505400d000500d41c0281c0e9903008000c000c5c400010f040401c0c484244d500c031000030384002c039240c0c0140e0421085100c245000e2040e03074403d001400085001c4101d0210300130240144080156550051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 873029082 1250 873027832 873027851
    0x60219081204030e10050405211e0a0302010606091d0a0b041e0c02010905031e070f0510050a0e030703120b0d0f030e0a06081305070b0307030609140708040b0a 70
    0x200c0072071403045009495940074244400148a00090403003d00c604120080009100070340d2454403d89d03000714000d00c00d00c0114885c8500034502803003905400c1c40c0030b25845008912410005400c610140700b41e00070300000e80c0c1c54070b0560f8020042c1c020070011115011100d02010000c005a617800047d06202140e00912107012400b2510140322688074942e80d8108c2d03850496a0303010746500c0210b548000c00c006403c81d1203080d1030b805850340440c00e655000b906440c080307207003209072580c454014034001d005940c030740f0384141c1d5a4100b40e050041642030400003000c400140c8940000d041600300514501800c990f0f0446000c0123011640c0d65607544c80302d090500380c45400794401031900c50181c405400805003009072004845040b024402c03030310120300f804140e0740400b41e40e401940146c40e62940e00300c60300d0014103108807a044801aa0303008801c00500f00e84c50f0704801c0031501204000c02820422040101e142e6504884980101d40c40e5408580002c400585d419405400144005000e582 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 873030332 1250 873029082 873029107
    0xc03041a0709030507080604020f0d080403080d09020f10081506251502090d030e21070f0b040b03011a04030605130317060310050601030f06080a0c0e0106021908 71
    0x9681d00380c00916091018020003c0412012024100144c02042a85490fa0000b00e441d8410401540910f0240398030364100a60031303007624055030b4810201c5032500c0b1803110740ca00510803000180c2c400d5128985007441800c0c418140840c02c03a813507039065400c1d912001110560040301c07500c00d4002c80f00308445d4158443d841082040f040040b6401580c00d0b00c241403101390203002024031401c0742d104000611482e5503c04201c684203606040c0040b0603d00c0e1000207043c0c09600c48500e0b89c04148210b41c004806010414509881c22541c1e0043c07560303240c100001003800346005154810f40b00300b00500101d0807901d1100301c0002004083c074909520b075600da4080d072700c003070b07405a51300300d00499400201a00304088584215126110a48078600702000a50720035a44400340c5840f5aa00c1c00f01d05164825040000c1098070303118280481a81e61017015550311340e10f00c0959041c0d00b100d0001c01e01c00200054281200c64540c020300301d40354514880143d469850400312400441003000140621 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 873031582 1250 873030332 873030383
    0x52d030705060d05090c09010b040e06040908030f040311011401030609021203130504050c09010f0e0103060b13030b070c02101818020901140c0d1d0402071506060e090c0304 76
    0x103620701000c13826041c910001480c001d00c80000301c1c4207044d900300511510031010305440c100c580e08041180c20f9100c2c4400701d001000c46241c06002e50b880002000780440304030510034000c034402d603117228944000301046402c035604e60b1009021311141c1d00041003c5a900d0b0030108526000510146a41d00807060941c07840d400410402000b440340d0302d040001d441c151050350342c88842805818900b00c54400002d0503d055448020184011043c82c0e0003181d1096114002501c142505503645008040c003c204070607862008440e1121180c001820081c8905e24500300c8940c050010b4028403010b410640f10403405103c140781e0902c10702000200048102d803898280140c01400507520f40d40e000c0010307c0ca0600e01a20074040408101160b01c054000841142100d001d2824070880c3c0b010006114084074204030042d402800403c0d040f00b403140e00d050b541103c03180c662041181e25078401040d0752000b074003042d5540c041006000a114949090003c5500c0780c40351041b51020034004000c4e0000c032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 873032832 1250 873031582 873031597
    0x30f08040b030f04110a03080307050d0b04020d060521030307050322110f1905040c0908032a011506080a0f0e0f07081513020a0e01090510052d03070506 67
    0x4461000921050005d915040360b1110019a01030214601b5921501094400502140d041240c00607251003004501c4d80701c085c00100080c42550f50700f03004940c03071018011901856124922026283c0109503014042000c1c0100f001e01450031a40d40540c260b4890704001e0000c0c142a02d5051146440801c00e160341d03007290322440186250001030f0f0288507150109401079402206c0369184000a035400700c0032403007103d608840216038141525401c07111542e06500c0f42e01d280c400030510230000301e204140d0070310340c07500703080710f524504104e0707088034223941140440f850181d41d13840e01400164420000c180c0c0c0b0001415002c110004201e950a08035000260426465048246e402c40440c2c0c003802000010240c0900602d4483c9022643c8041c1a03400307080610000c6140e06007000f10748030501220010441620302400075a5a42c0006016240440300d506500555581c0860b40b4904498621a2824050791180d9191445510003040c8500140c1540c0d261003007000000315551030600400d40c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 873034082 1250 873032832 873032851
    0x512010801051005060c0709050603150123030715030b01030219020a05121206060c0f0607030204090f0e06060103090615090b041d060403050307031d0d08060118030f08040b03 77
    0xd0b00d8520f81c00b50103500250481e0388102070410030f07117020700c0c4001010402e0705d6201c0000201600d4482c0042d141c54050030014101c42d40501c00000c0071484031140c0e84403c1316100724141c0101c0f0500815480c1c18590049912103032001440081d203e210342c2c40000c1506042c1001850702148041454417030a4030030795680141c1c0b0442c11003040140611820b00c156607405551818500c1d0101d2200b1202401405a40120780c0843c45204c0e011040044110302a81442030f18020b05050704010041e5101380100c0301c03114241078a014040c0760340c0c800c02c500311080401822403512404011009010b9a000c165400c0d51079403480f003c005503d401d984000d2021801c0010385405040034042035880280c2a141203c20f851b01100780d125004c1269503010b0760502e4117540d00d0b5241d8005400512000d442c025000000003403105501500007a54103901070380b0348503401e8030b0f52244e00445280c0c04a1341207000b15807012000b00b00044114220309001407044130302904017a2507071518011a0011030f0031141 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 873035332 1250 873034082 873034091
    0xb0714160b07021003050126030706060f1d0121020a05280821071e1a090115090b060c030a031512020f2b0b090f06060307030807030512010801 63
    0x440c645144500301544c801d040034000b0758540f440e00490694030762440d10703a980c80c02e45000d50f80304090007100c14081e4000020046140c07500d2403441900181c0c003c503104800c40c41c6413076950003691b00300a8103d82000a104525510b442c120751201501c0d00343c100d0704425000000304090307680058161017544d981c0d000c0b4007102507a40c1400710317070215644102e5940d0041828403451106d0000b249074491140f0715035503a9002e080c50012804030202c21800d615040020000042100c5560314031140d00003010600d10903142d00010038226a4035040040b0000340304034040240b0440c5800004c0c6110008094900780b1044a0f2a43d0440d88115890800a940d600d040401103505003400400b070500c4600c4c1c11154400344d404a1103941d2905c20440c0b1501d00080305c075034001c49004514a491080c18100d00b00c000c03140c41e1003030b26140300741c90011050042c0e0b02420301203240015050f12888000f8000c1101c02d00c0c40e11000819800004180c040050811008402402c3c41c00c1d51030007005403000014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 873036582 1250 873035332 873035347
    0xb18090309030d0c08040510050706020a0509130c0c020f01030f020310170a03020706081005031504030818030405091f03030203040f09052719150c0503010b0714160b 73
    0x60500d03d525600b2001e21031101e01160104114005550545a01303490b860fa94110122003a80d15000302c0c0401400c0a00010301114815481030141c038410400340c3d0700880c584d0380e040e142402d07142d1818100d03000842c1010b103040549030030301044020900c18100010090901070601090340d10803034a84001c018022000c00c40d0000d400c3c4060030f403c00d440068140585146d074000d44440303103845210100314082c0c02203600d8000d03881e01d120081100500719800020782c450410880c00045605501044100c40060381034141c19101400480b06076014525240c01c00e0200300a809001d00030004c4480d00003104140f091103010803101a5000b50000d40c1c64600d0546036086100050304034002e140d0401c0305020501051003402c015400403900000303210300490701c480740340821041c0c5400c0c1c0716042c070505a04bc49503102003001d03a5a04000203001b0312a0f04401600c0c80c0c4802c1c420451030060801084c400b060810100075440c4c10060240c03013405100c403070954070b5074403076070003414a034000050300b0b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 873037832 1250 873036582 873036589
    0x309021003050103080f180a14180142170c09060417010f060621181e0b010303090612060506040b0702060708030c041503110901030b18090309 63
    0x1080c0c440003072605215641c1559600c040d503002c0c212401e04032010120780c05d030203002045100c45c800140901902142e541e0344c22100419234903484070500803d0200b05010010b50f040401c503041c5c0307181101c070540758003d01e40344d03980d0311030100440d580d4561158a151115003e0300003010404009036503000350018511403c1c084030320050113050071070000f00202011070321080140d03022170f104d0000018056010440c001e024008051540c25807034a00400411501d400c8448020024640d100301444502c200e2518022a03080c107103204644070214680380c0000e40380010380d0080c502000440c0b00040d601e956001c29071142a007007140801c1d40b40e0f50501c180d50344a0000c00400b03d191500348643ca10b4400403a055228502401503951000507901c02035483c0c6c042147d2a0703da00140039a80c2e07203004202000203410038003400d0803204031920320240e207a120380200c80a40e4070305c540c103034940f5403001c0054009124070340015810012150180da950031200f5401485140c011000c4c540e16203001081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 873039082 1250 873037832 873037849
    0xc1a090f01060e19090b0f011502060c0304060207051509060717161202091302070203070506030415020304031215090c110703080903070b07050a11060702030607081510030902 77
    0xc828050b03240c11410040c400c52503c07140c0c0c102ca07240d403a514404100c040301038084c100d04030b4007611442c050014045001015030445040721940d000642900900344012600c80e403050b40ca0401c80d480c2070011034081030700b079802844502e10400c01c5501980c4102c96000714003004030345190164106004000c0e01d0703500402c4410014404034a001440d19000d0625188001c0000c03403481001074403443c60903252040c1c1d045480c81e9000501c00c031803038044520ba80c8080d6102e800120701a014400c030004003410100c094038020346e0700600d01901c815210064000030f410040c01681081308030300c4c0f80819107120784541d0305000300300d41c0018501c03405d00325081d0a0380c2030f02a15008101301551080c540d14004a9400146d03503001100070760b07801c0300c040003d11340390041e003041e207003a080028100708020700007406c0b0105c0340c031407a000c4500d000300208020540c0a0040c010b0341581040e400643c186101c2d60545a1010344105404d40c2c01008801080415500a440c480801c1e6220361070340035450305020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 873040332 1250 873039082 873039103
    0x3080301210f0b0907080a0b1608010e010b070501150b0d0b060c030706050a1407050406031514010c05070e0a1a0d1115040b030408031f03031e0c1a09 66
    0x385642034002030742c9030310004030040c0c1c003c0c1600030b10a01103000003e05114000080207044200e89644055007007042100c1c800f96400d5260f01712040d0218103960003181424104e07040500e907503540b0307882c100c1806031640c05817074129119542e80340745040352508004040c0141592a0280e80c0b100c1c18a442070007107030758892016200750300c1401251904580041188c11840d4045004942030b283c0c2c1c100300d0003424000d503200c5c24203103d0204001030241e114016004480d0706603030070b0042c00c038500c2e481a0559458000c0a40e86412030703900c0d42c140c0d40140e031280c416510407021101904e1f40c0301d1108440d0403069650752822601e46100d001540c031144420441e0000071500e25039903055950f51440303c4801520310b40d008100c0c841d00e9105a1910318180c800130680000c1c4240e491400349041c035110b40c0101c0b0968242840084048182240d9030602010b03260b05440b801500200440121030101c40d03110340c00c04001d01900c1d0b080008951202c0c80c100245010000f9041d402d10f04211400e0100b09203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 873041582 1250 873040332 873040379
    0xc060e011704150f0b0301050429010810052e230d022b080915031b18030709020706060e150103050c091e0108070203041412070f03080301 61
    0x2010b110100300c0450140c009104030000010301e2600c00510311002e4001c0d800b02c1c6625510701009c04c070901c82c03041c40860325400040060b070700003c0858030040d40c40d00700303000e641002d603c0041400214809544002e801c40c4e1105030005c0c66910482c02d02ca41201000c031081d12400c10b0100800c04040d00c412001140300081800d000301d54001c00126200305800034003e80300c1c141b00034001c840a9150300d15686100c02101b140506110300c0d090554103503011049176409890139002c104c00703105041d01500c3c01101942c4003034080003042030264009401030101e02583d072070041c00c0100d03107580400c0440c00030303d41c00d407001d81c41c2c610701d080c0b10086a545910860000041504111170710a044030425074000c000d0074000350644036a600b9528601640030741c2d84d0420f103030708180fa040c9002d88049007440802641c0e03050aa40d19040101c0e102d010794440c802103107035848621181c0d490302c0100e1080c1212070301c017110516691111001c01100840c0c1c4182d610b0600003005100c8000b080c41c52038507008081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 873042832 1250 873041582 873041627
    0x20d030c0c061125030816110f030607030b0a0b0c060f0c030405101104051305040c090c0c020f06090d0804140103020f03010618080d030e1c08010e070c0c060e01 71
    0x181555500d0341c40c01401c409049540300007002d40e074030f004e48203480610341000055448280d480224014001040e00649109044410310403062815000203244540e0140103403000d0703201c20a0983c003401c4e031481855880485164081200300340c80c1c01401d0f0010003c00102401c2c05d0100c00d0351540280030300700d00080f072003c000700004600700107001c10852a00890004035a44c090468413480e000b182c1000354400030a02500807c000940c204900032400351003182d08103503440166004851070030002c00081421400070b00301520f407030b40342c00d00e480c000a0b2000b450914503800181c52001240300444018001242c103100350301c0d083c4401410170b4401c0c2021071800c42142160348050005104101c10080c44241d4480c41751402958600103000000449409121520014010b0082820100424030403400c40d60042c0000d100c8054a981d492389440c1d80710390803e5041c05aa040c004c01000074003442c0c00c400320004009084a0000302072a079a4209071151040006000c528405003d00300600070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 873044082 1250 873042832 873042857
    0x161e0203030105011d0d06020a0e10120b0310050703050106112a1f1e0314060f0607050f0d1101020703140a030f1113083007020d030c0c06 61
    0x3003101e041d20004d080094070340070b807444614102070f020380b01140c010070300101c00010822613801400d407820035a00e50000f441120001c2c0081321489298450003d28884001d422102040c0c0c88104103260140955440c124101100006e80b14207541c002c00203540c2e10010032a1650044802c0801e50035000074200b0b04010100507800e010217800b0300002001e5120108031580c0e500342e4040810f40c502c0c81c1d080780b2403400b014054107400c051104103820900c401001d4421511a20540c5480d01441c0e0526103a9180d150902c02600d04041d99142c00001c10002d80020841c01c114034285044240000d02d00c8003480c0c00020701100c140c40b54004103a0044c0410000290410480b00c1c6403003003a01c449460343e625041c00c4018000c803c144584062800d0003500b40c800c90100206001009044880300c25950f4290407959580c140c1a4285108045c8007010031109858080c02c1c000000f01c195641072181c03135000940c1c4481450800c601144c040a46e4104101108004030010003107401c2400300c5200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 873045332 1250 873044082 873044087
    0x20a08151501110d09060e01030b01050d0c09050d06150b16020d021302040e0f100510120b04020a02010914010204120212070b0a11070801150b03090c09161e 69
    0x14081c04034000355007041030341c0300c4a9125407019509840820100c07424000440320113070690b00940210800101c000002106550085c041c0d0021480103958191034110000301c0d16009014040c1b1005c00c03c400000c000078250360307000c624041d850092100145540440200e5094240e4981c0844d01c00c0c2400c4c002d010307801e03d0b03402c014003400d90103071030031141c0c403100b80300044071000c0c000c07044050b20b07101243c0802c0c405140343c1264480d80f40f0700302d08203103521203140707440200d20a4800c40d584040c40c8103072100c0092140ca02d0325003200b295140030841d80305010019080c0c4e001a01103000617952502d420703045c085010480c0e40e0b0000c940c0000c602d05802e144680858400000700a4002d90321148003ca012208018880090040d040496102e4503461030040c80c210001505482030321518601041d80081071140d8000305011104514800d850402903850b1070700001d280212900907040c103980c440d00c9003c2c589100c0c078002e610310301700310440500203400103038459500100703046c1091800420a8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 873046582 1250 873045332 873045373
    0xf040b010b130503010e010e07140a06050f0405150304120903080f092d010906030e06180a020907021e01180b0429010312020c0d031b05011107020a08 66
    0x8140c03101c030716955050a0070400a82403581c0c0700c640c0540ca0842038080d1218198489a0462a44800e41d51001d0350741040003024100014000e0b88401035640170880e1a0162005000388152501d1650501d5950000180f0f40d401850031124090000401c00041100d00403242c54209841e050001400342951215400e9004a06000e060a0b5001600020541e907554042c071706800f001c040c0d90400060140c50700c1e00c03074170b0010255012843d080e9021403840c2c0640102c0d03446007041c034014500303580e4500b64061264501458009140180503092001d80c0300c0d10742e860710800c9150010158032880d03c8840e90702c0140c40300b400b4040c3e4036020544284500c03403203668030040c0e0004070118480c0c466042c00500c0007049000c0781074a525403940458038410062403141204c0c003920f044031351301c2c040710400c1c0d0311031120300b590030345c8480e45000030b20001c2e0184000c0c1d141c0749080141d40c200704450350b641500712084441c2400c0e8824001c1191400c519121201760040c0a00750094602c140c11480b2559110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 873047832 1250 873046582 873046589
    0x30c0c3005121305042a14091c02090709050306060114030406050c130f030302060f28150b0301050a2106090812040b06030f0c10081009230f040b01 65
    0x2403800100f000c9400742c0f844940000d003000600400204c0e408040c41c0c0c000003036901e20088403101000c1d1030400b2901070449050a203416140c11031415909408100f0415981c6020800e0144006407610241c7c85401e281ca07c11115a2542c1c0f1038039041000b0940303407280c0140620b040207040c099000d407510f01d0000762500103500040100d000e4450780e41e10b460034002c00445090745083d2040c00103014a00c040e40c2000c585c000d0302512100e4650001e00d504200c800c45140c20219807102c0d40c500022001a900c040da0f102040b400280010850754108908a40340c0c003402d80900040014003035481d000002c0e000910700c05000131201204001020941440158050140c5513180c2030001800440c1c0c04482d03041a402014503a1450700d40741208059405440740390180c45000300350200100005001404200300400c0c60030384d1001c00104455800c001041c01c001c515a4000008840ca0107000c0c0b00406103560b255004d6090403001481401d0000400b13145d05210a1818080401d40d080202c0c3d055 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 873049082 1250 873047832 873047863
    0x30203090a050a0f0306021312210315140415170c091605031f06090905090a0503090f0613080624150f120709090b0a0e070804030c0c3005 61
    0xe801d12014075814041e07030760b4022004401c03102c0721903017041100c0c103240c10f46900c4007100d08d0074407034ad04004500720340c030051030204955040c80c4140404130546d4001c801c201c200034808201d0300e008082c21505800c0d6548024221100140480a12070091103202122101611412100e20f040c41c288003601209100d100d0078801d0000200d81108601e00c10540e17880380c44510380150f06e0b80d95100030406a1103129100c240e40c07a10380496210340c4007040c2c00386c0158104000310706040d0400c0810842480074410740c0d0344a1410480c110202208100c03000080c40c200f4094841c0303107804851141500d129490806070840031078424119a554102105814058070324801e44900b04948401d0003403040300454610080440104070390070742c0c40200c440680e4032014050056110b0041404413090b82e5001e010403000d1000001100140724003c0306600034043c0c0f81c101401c0c5440d858a5144200c2a00300503400000705074060304100006080080c030452080354582c0400741c0f0b07200c06881d05e2040d13628061 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 873050332 1250 873049082 873049087
    0x7053d06080f03090f09100e0103050d0f03150b090f09010305060402041112010b07030c061404020406080a020906090a1404050d0806012f01020409060801090b220605060418030203090a050a0f030602 87
    0x10f942c41e007c03074002c01601d074071051410a540c42e4109250b45807684462800083c0c140210031024601c01d01601500110403908440f402d4141111031003607403c6840900e400c40190b68148030313245c1d510091140294000c20142500e414140180826034601c500b25a650400420900300754084444000381144d02420f201511440c062034101e40d01c043d160405002030342003040ca5031050080f01e09250045108950810480303545404190311249802c00c060341c4201700200080c0c46090080140c0c0c0e001e4418100060300a0120312400c451703240c1a90281e400d68011044080919000407000d50442402d080030704214504140c41c08980d00034904201c941d449070102c1401003a0250103603000381c0300c180c1062080030340340c1004900030003120381c050b81c00075609400320b680c10f03554003488841310f019100f845011b20000e0701c2e03800c007a05029001e16009a641e0850201880b04005201030040c0300b517000e1030ba610101030801502e008150402c6114010b82c10782046807900400e022000c0304d90101e000758 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 873051582 1250 873050332 873050341
    0x1814010608060f0d0308100f0602030f03191e0f0506060301090905101a1906020703080c03070605010e011404060605030718030f050f07090207053d06080f03090f09 72
    0xe0f480c0e00354202898211264880f5a0101904440c55910800091880c0d0441c255103522200000405118020140e0002c00200600381b003800700559200f024000c0307656141010786402c0d81140c101203002e000e0404100d50a00140c840e901035804411030303050060041d07042840000305c0b075100610901c40c030942e07604118030800105000b0303443c1d89208010200483c20703049154100804800541c98800c64501d0160244a030705008541c05440c483d034014500c0070304640d100c0f0040c0d440501e209505110501a00340010654024680640461204450349500d000843c520380b80c0c0440620344194201441404400c0c0c0c0701e42900d501010780c2c940092580e15040c40303400181c90640002e000550f190002d00244600000d1401e001201c1c1c40482e12800d941d00580001c034054903400800c140c000400504010700001101e170341040b441210040c5840c44482c10001c1001011a060301c2da54991200304864841440107400c14541c5101070f500e030180b02800561103228400c1060301c02c1c8060f20114 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 873052832 1250 873051582 873051589
    0x2c010804060b130b100206130305070302070e0a0b040b18070e220b0f03120d0c0519030b03010b01090605041203030e03072d02011e051c06181401060806 67
    0x30b950490000d80700c05400c0c0c014004100141c15840721150182440109908a241c03000840500c00c00301d002c0c480c4449050340d5000c86a66106820590452050b504007141c680451120307940101d04441c000200c690340130060105035282350420520409009800d5080315441d508000d5000300949090f1380381e500d02000280d144544040c1c20000303000c1ba142400c000000561124907040c108403182e11000c400320303003010f94a406d07a40c0340302454503081c081a8a65415604200d400401600b0301d40d040240e5822200540340ba040d11000010f61940440080c50500f8420407840703103800e2a06080942c10413502600600c114032841c0700703510780c031481102850b20962204128200b070a0030399a0b60385460828a0044021000700400d0b502046044c3d40f4a0102c281000300465042e1513804040351070401c1040401014034210007401000c0107564541c00c030140310000540c00c110000035816042410100d8540202e042e15401d052810b035506110038650a0a5070448540d03240ca815903948030703000b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 873054082 1250 873052832 873052841
    0x309050102043c03080a080a090212030a110105010605070f020d051615051218120408030a0e03010c170405010b13021b0105070917070b03162c01080406 67
    0x302c000b2241d5242403029002521004502001c142c0d03c994075020400340f01110030965612008200e0542003042881681c006d50200e03501603c1c2c0c0400040070303449070300407840400c1103080302044c5800025045806641010740ea2043e0351150008000c1581025001b428510405e40d01500b00c0520092400441d550f20f40700c0c150160b441003c0d54214041000c00091041e0703180100600060101c21910309984540241c804d2815125890b2803141c030380380128440c0c945640d000070183d01510010320320b4030844c0001400140a400700455440011460082c500c01452600310b2199040a000094250b402012020046010801c4e1802900c03140340031f1f4014500b4410050304110710307040b10700002c002c81c0e02412000390300740c804400540044234550f00303c1b402103c580c0c1c082040440d00348080f208481c00008500710f480121040917880e040c6036149604102e40040078001c00311050a01603a20038458200c0002d0210b0b040c02004454200001d04907a02c3c1d203540c10416070500180c28402035411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 873055332 1250 873054082 873054089
    0x30d0c06110c0303061c0816020301021303121716141201030305090103050a0209090a0b0303091c020a1502100c031b0f020d0e030c0d030c080c0703120309050d030905010204 76
    0x2407561900b40e0300e0b800391641c00880d83c8902c1100c2040780030052015500c105840c1c69882841b2618000d00c001681c0100490030505980542d400c2c40403802084102c004c203000b40d07000c1c2c00b4420101034009001013204011810440d050b81707401d0f06101c103003c000000014030050700e0070b104140c07014642201c00140a0082140101d0100c000000241500040104a019400c2c1d030f060143c0c1e600c2d080740105070302c0703104a61908603174440c0016030031003070300c0d070101f0091403008050303920b0005018009000c01e01d010b8101c2522040d280104c5003180303044880c20000300450710400c0e03000c85400b40701a4803030100d80e0a502d011603d59001c151064480d03800400c201806202d00d40f4401c10791400201044401e514002c00b512030300d205127040d903029001041036000300030010310369a210790040c02160700544070300714103103c02002046e00040101c400340440e03004100c0149221071031030034060302241c820102d40080c9840d1940c804042076003c90441200b20041c10302050301340c2d061800034024441c550 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 873056582 1250 873055332 873055361
    0x60c01021e0c060106080c0910050c03071401050a0603050d030b030715021c110d0c08040f1701050c160210090801060609051306060e0d060f090c05031605030d0c06 72
    0xa01d00c2400c004488003078280d48440740110761041e0780b80d5070203464080c07040d1012241144244085220362500c403402c105103c61311300e8140d082422810b03c40345590010342c7d08595038070203c1002200410248101039120f201c6010500c03015140d9110346403a100d80707046042c00c158840440f4141230b01c0400150300140314020150100281c0d803000292201c07600c134510500b60002c4190010303003500c2420000c1e407002081c000340c40d40d5142d01c4001da821160501003190400014000021340e240703c25004402000f021001108051484044908481c0020400d020021043c0a039011401030251030024041c0c0c1920010007030081e100b000d40f0303450300d650f20014040d130038508041400c40c0d11400140484505030b134000c00034584d01340000e041d2100c5005100000744a00195410740c98490400f02032300e40034a90020b140c15540a04100f9030b4070030ba2040d00c144824400c10482428200184100e20b01c108440c611000e05010000e0b0301e5260708501d0380d08026541000c07200b44802d0b64003165001c82c040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 873057832 1250 873056582 873056617
    0xf090615071a0609060f0a050103022101060201060f0e010317030a0f050403110705010e062a010c090312080412050a480b1311130504060b040908030402060c0102 71
    0x42d01d9031003412408a031110b011301c2c1c40801003085420300c0c50307081a0500005001d4504142000c004500039000100146801b0225602004520b0780d0001e05134040d011035400807591505200b6444407605030366100c000809140c400410108060a9540c8040084030b040d0aa0329280c1508075405018020b9003040c09070300e01010301c4200760b00400141a844060b0043e07450180e03840303005503511201c100d1070036001803080000c0c0e012611028036040000f00301030361403102c1d01c64000a660840d0240301044001c180001c8040c82031210700c1d2400002013083d442e01c0407061920340c2c7c500d0201d040024003001072010104014402c03e018401075210414600002400900140c002c480c05211621032800c041302d001e210320196000d40300044d455543c00011083c20340d1140846100c1601254600352100d04248050002ca6541e2003801d00c601d909140010032181030a09120046807001914644980d00e840c8161b8005040641070740c0e441a0111189a1961a10b2184c24064031543c03a6416202041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 873059082 1250 873057832 873057863
    0x8030403021e13050604060605091c030c150212011505160203100e060103020a1d071d090403050c010c030c09050d11060a020607080a18021027060e0f09061507 70
    0x1130b803010b8410802100d086c0b100c030303542d010706490501c1003401c0c0b59044009055099145403906007441c0f1241e10a2070442442038003034540014101030b45a60030a0540c0000d68030b200e8a1440d10098090310303120500c41d181c4507900602030900c0c49000039070301035000010a18019903500303100900e0700d00c1041f0414132181141011203900c0307440074007049100345065000810f40704807611603c1e003140001c0341d102103952515002505c01c1e110f41c04810144101c072600c100841e032240040540181c3c41381d01c595132210090049a070079541380900c80c0007094a0940040e940d26805003221084680507201c41094050311306091220303805003111613070032060010b03604641c3c07540007a43e103203c3c551702d50310a030840e201d540c03440c0b05036a0a074500014500a18468001519000b134101503c280c0d2b07820081084865403d628484924040c814282407480c40e8041000c6034001801c04450300c4111412070039540741000040601c10064480742c090400d24912038804802802161065504402c400041504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 873060332 1250 873059082 873059119
    0x42001020712140c0a0f1806030305220b130611062e050301020a080907330c0c0303030e0d080f0f131406150d020a0605090303070c120204060b030108030403021e 71
    0x30b501c190b2035014100c41c0007104c594003611030303230047d2513040d07564503d03041588d480e52100d8030758a040400304071003800000034540e50b01c100421990111340c00c0240f0f21490071a0150645280c80d0200c0840d8018000b08550504c0c0d041d140c00b4031012680078114000d039080c1071101c0c0d41841d504116015803000441c00060754005800f180f00780b650320122501c2903220b00d0020103d412001445814518150305101002510106030110101510f0007404180480e2908003444541d68016408079a49501160100301c0c28091a21071001500b402000c0f81007281c034401c02008020844101c00c80600c0100300c40d8141001c0d45d42c1000d030012a11f44e1107800d500740948e1250790584407050038000003411080113003041d00103820303c0d0707070002c120100c0344d45840403d84459003c0c0a4290340b6020030004c00b000610300c0300c0301801508000c0d00c0701107800d0080c41840121a490303000308001c0c0c5d4080c03004100d101d0000007103a040e01d40c140c3d2080b11030106408040d001030b2340c0d42c0460740e00071481c0496070000c08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 873061582 1250 873060332 873060359
    0x2010302210a02120702070b04030312090b041a070f05120601021606030219140a1d0d030c060b03010504020a15031104090207051c050d0905100203042001020712140c0a 74
    0x2001048200e13000d0300c401101340d036203e0451050b01d406940038082000842e00640711400d180e85811404a20345006513a0400ae54104490850360700b102a43d01441c001a10060503a100103a8205101440804203010709180141d200f000c105013203500028410382d01c00c0c010b600d594000c4010000390b0b284c8451020f4040c1d003121200d10303158202e25003400700d818404d120903c07600e01170142051400780c2c0401c0c1115050130340c4000748041e00d00356101078500d498540701c0c40b61050090713172103400041a614000c010340703c141031100e10a81c100b209110140e0fa550a080d0704036106503007868046141a0010780c0a0081701a904007040d4010400240e5080c83d5001001458880c0003551080744100c030612841101c081c48600c0020400c1c08480d07030704100ba0f0b020280060041007190071100541e1004030503079004480481d0000078611000403090040c80448205e01d40c01d0000d00092410b00700da104034128040f2002d00404036801980040ea041840740d0203501201401301d08006855520074400b81 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 873062832 1250 873061582 873061597
    0x90408030702010506030606150a270603050105091006050741010c080613180501021315080a02091201050408030117011109121c2d0c02010302210a02 66
    0x19404e200c00245140350104801d4820007006099458240c8106840e6a064010603540700a00c180003c20300e05a44822880944a5100440c15580282072a100409035441a404a80182003060034800040f8500f038048094030079600c1c020352600e500d07040154242c0c01908003096104003048101100c0c0400c03c031800103100e00d140c140c1c40b40c1e144002c00c240c201c0301c8d004e0819000409020220712103190102070745000c0385c0e0006001c248a40c030034628003045850b60904039440c0e90b00040d01d030f14070002c202c0e10400802c0c048611000503e0300c40000307084100024a20b454085c1d0009407030503190758000c414054040301400800c1940f034545015003d60b48203001d13841c00741c400e00d540402000014012208101304a011007810400b06c3c009000d032114411045180fa03005a804d90b0960015450f15403056504c1980c4104001407031080c13008001c5d0708024070440f1000101e030114a01a000040c40403003942c2880e0040c1d45042034600041c400311050142641004c800d82400201d00d5140c0240050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 873064082 1250 873062832 873062837
    0x4180f12080f0415050c0706060902190203070302060a0c0903080a09060e0f01020a1209150302030a0b090105103228020a060e030405061902010605010503071b05010b0904080307 78
    0x90b440340b010b8000d072160700b01c400801341c3d1445101c04188082c1900943d805c4034001090300c2c14200e441e41d6441c142d80300e6800041c005a40840c40c840c455001d0b03640c5115040188c0003840c44c0c401281c0b0002d495540041c1080c4070b058554411072807142c49084050019030b0404482c0307032501003400740104040002d10480d0005540f41000969505c0d10212a00009005070000e2520745081d9441e1103a680700d480d501c20030b100c1d58001c005504041079103000099091076800683da45005c1911408546003058440e00413548440103014a8541c488000d81c101603909210562107004051400001003486d01c82e58039998443d504480c07400d1020203131860398041d0aa01c00d900440180c140a9240e41c0e0710740d100144d00203100100070030100d51000590246c400c0a90340350681301c1021801d140d000e2001040c04c410003c030350410741c1d58203200c0e10020b00000d1034064030b94108000b000389403800e1168070300240c240c2006000300300402540b110070031500103400000b81d0301c1c080c02c1085040d0070845d80c1c2c002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 873065332 1250 873064082 873064097
    0x21e0d14070b0f0c06010f1d0a1506020703120801180e0a02030d1706091b16020a180e07060503060f0109030609030c020a0801090503030c0306010e2806020105060f04180f12 76
    0x200800303a01c7c081c40603110507521400f140ea102e07406812014030043e000b40c3d1071030361303075980058240d001d4030184001e4515034000300059859840d051680150780180d40d0b04001c0c0440c01448908005005031880f09051000407500c001c119440f80e0408038403080095051041000c02c0320f0894000400c14402c1040e101b80c40000d540300b030140301c82d40c803007101d608002d00c013100840c140c003000302ca0241c16140a401880b00041c105a17020413002d0f20b06412000d11100c5504520122180d41c0c043d0015080071030303000d01a00c51a001c00034209001c085d0519108200c00369000c1203507440b80d5040d000554001e41c080c406948035060107840070b08644000d9001304840040840c1850050207a0610719074007500451565883c4407240300c5641000c0c004034100103041100a0103540c580d003542c461b18600c04503914403000580014001e0300c84e982d000c00309690400003004015a00c140d441003000320250b8000c00d952000d0f2008e503c9140c20444000c060072104a410802c3c40441e1095242054803a1100075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 873066582 1250 873065332 873065339
    0x50c011103091003020f040e0708150d12080c12010e180a240209041407030b0a030213020f0c070b07030206011a03060d021f03020304021e0d14070b0f0c0601 69
    0x1d44074496299055085882d078100041c40074803c1d4002d10340d552450362500d092a46802a401a41030195280710005070368105002854034007070a19043c0c1941185c15880a4115950b0348411418495040c414020f0340c02c00200500784540c00c03500f0070040c4260000c2c4668607050000450707881036844200f110360700e08645500701400905800c0140d04201e94241c20204243d180e07540444105820040c0343c1c01344022403040c1c0303440c01084030305081d02e2841c0e5a14501071400078112400404040e00c40d801c40031081026803141c0b41444801c035019400960380c2c1c1000c424a4681d0701c03680020004601c92000000303000040f0720080c0842034803940c00d4075010703640c640d00ca88109000d001c03174a041d0201000401c8003460310b0402803880c548090400c0d00f074400d04086001070b1400d07400315000400c2e0000100b1046140c02010014032200e244080c00d500c00d00e501c0410303940f4041100080ca42030180518101c45174041012800400c0381c846203030b03569a60200f00e103510740c00085040700544540350011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 873067832 1250 873066582 873066617
    0x30f170c19050106030204091115040b12060a051807090e010e01050f150a091806030305031909080d0e010b0102060103021003021602041104080601081c030e030c0a050c01 75
    0x32060582450010314020350042010301010000030000c80d1159642c00c0e0000c0141c84a02441c154140159103071400c103660f120501000160745654407100300e2080005100d4041140d05440c21040904e051800c140d60303003004100d001c1c4050f04469440b402c0750300c145c80140a01c800807442202581e440030701d02c641c0d0f4504640d10013401c0c02950320301032030034006000c0ea00b80f00303001c0c40c01014001d104d0765150361070840401140e8084030031074000800044061110400d50324521881c0135504104004151960310028418000507043c8480f1010001b00c55010982541110002940000c5e696544e100540c40900003010115881c881550030b1407045012580017081190489402400c0104d00c0710072200110001d41c0501d414400010658035074401689030f6101e0b070410001011151a61141844035151030321310140d104180c80d50001100d0001c0703800c100d00b0020882c803107080c0030400d41c50032218542107004820351000c0520134415014107003d00054408010803085e00c030807131149031000c0074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 873069082 1250 873067832 873067837
    0xa050a02100c0b060d240b030d090311060c030409180c0e06030a030f1416061107031d0d050a0516140a0b0a1103040909051209091915030f17 62
    0xd4907083d9100300046603420004201c0c041144114240008541000c501403040000480d4aa007802c1da13078201c2581608040011601c0c400013800d1075061103203107656030010910f00d010002d00444020a21800c1548104240c130040e1000c81820b00490403110410711115100d0001500d519108d9078001607454003c98030b0a001d010007030040e0003000d0710b82e1400c1c0d80c3c00765050101410049880121803442080901400720103000e01400003001340207051003426100c0d12450403004440400c0400006a0000f40d2894160031014141040a4083d0300250051400190213403680c041c82c1d000300100400400c00e0002e101d050f1000058654803000340c01d0703030214421000c0383c0150541009020801e0004007500d1480081e141c90810311029044c480d05580040d03125580742038481044000b0018107014090034940040c20080c140f031680400122180030291100c200d00c40e1b0300c928401c4551081e0000b0310144003400035480e02907940d00c0d0241035418090802d13142e60812540003421000000c08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 873070332 1250 873069082 873069107
    0x1c0903080c0a05030a0b1207120203060705090a14030106050d0b040c081c0509040605030712030e06070f03050d2009130b0901030209100909140f010e030a0c0f02030a050a0210 77
    0x3da5074110b0b076403075072194018020690365039408a2080049900f002c820000140a088555200c102450300340c41418602000546080d0603c041800b000000da25030080940c1212203080c40482129000c4c40440e004240540026030066402d100d040203202d1040600e40c000e521410b2820181c594400c1141c3e203c0c0e4100740310400b40000350303a44129407813040007d0125540001c02c0000d44582e2940003d2800703a2079480300d10211000540c0c80d05054205800b0214010259426454520303281d80b030710345001c0400c03401420b021000c118401e5400ca03540c0100d50024071704407250140c4540b0b200c000050b40101030801c0c4a5180318251058000f0240140c40f100c000203400360641341d08650030000c01d10300c02400c00d2079400c0302070000a5a08042e02507228280c0c0070300e0b9036071085c4201d00c41e044e0500f0400480f8000c2d41e81403020b14011404004116268110146040d80307520402c1e2603c15500d9214000295051003110801418084085206201b1500c22920610101d82c15202a150a02540f1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 873071582 1250 873070332 873070337
    0x20d0305061e040b03030c060702070603091a0c0c010e030405040605011b1101020f10020414120a06021b01020f0309060106180303030b01170f1009022506021c0903080c0a 75
    0x944038103291456201c810702c80384000704040740412403000406d1650304040d400c00e40076400728081c8900c903030301030050308060701c95481d0a002c011080c0c4c40c1d444080c46001c03111022005844001051025018196484101500000d20040d940c0041f226561342050140300d10031440d040b00040c0640c0119003404d5950400714803528118500d0300d81340c24a2600056182c190f0249007016010018148501c481800c2d04034001a1118201681510300814060040380100f943c0316111010180c0007a0700f001e241c2c0e01c8a0056541d01903070218407401c0304d0b06011070304550300200b03184000d44103100141d445242d000c0212003c980e80d49200322010202c144a5074807160b1800e50900110703101c0d070405107460b003060403d510b09090081204802c0135040700d81d1001ca01220041c082c0c03803070100400741c6c01040c1e50481941000b07030b81403583d406010385e80b000c02182e1071a0f48441d0104100c1e0f8054a1171034114043c000d11007541c502c0100301a0540003412000a010100041d000840c44010b076004014150f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 873072832 1250 873071582 873071599
    0x150f071b0507090f0236090f04061406011b021507031d0616030503060315041a150604060e1306030309210b190608100c03140405150703141303020d030506 68
    0x8020119081b02500c0846e0820704100018800d92500ca2815001d10340c01030f49200c2d00d00d01402c03c1070842d00304905a01d42d101000c0140521a80c0c40f0013640041e40c524a490315414000b880060f40c40460f03803044c0c084078500421102c041c1a003150015020281e40e018a1007541c1c00c000410405100b40c003c00880340340343c00d0350070340401c2c0710b400503503071040303002d0222000e40181c1401c1103145201218203c0b455415007042024100780800085e07004000328450242201980c2c2c0000c0080c0145c0c0103000412418101d05205965860001c5070f076003400302d008201154a07824010b044030094082d80c603c2c0000341040c146000356842d03000301e50603048020720314503132035284a56480403011184025001d848082c04101c0260512001c485034004200009030002070b603001070195200c040180014244601c104000310b4000b180094100001d0406066265102d4505074014400800c2c41e50111104a040003c25000040c0c500c0c400ca01a0b021552140c0300c030301048050300e400b00c89054100504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 873074082 1250 873072832 873072877
    0x272409092d21110a0c0b0c010e0703060b030d183506070807140f0a05071208070210050108070e041a04060902120604030e150c0a0506010f08150f071b0507090f02 71
    0x2141c000d407c1c01110b11002050310b0f061200b4451500b0601d07001900d0056446c82d010b00c05140400000c92500d0035410710100740020b1214a40107001c192180d8181064800303042045807559002600e4440c0f1700148119182c0c128203025617450404175802004200440d0105403060f0050100e40d02c15454a4036107450801040f500b082e040c0c02590744e203014040e040c030070000000d10507003081d40c5c00d19955a88103020710340640c000b4500540e01c49100c0da62440d15005000c211400b2420405039215000030f18100c0d00c55181003070866084501242404441000703210800c08140c101c407032410300071900c4030480700500598503100d0005640c000d022400713003022403a0b64140f91007008a0388403a144500e003810881d40b1000e00b4010501c0301144c0d00d400200052101d24400020f85003e422080001c0500b00c2e0030382c0d042c1d05200000340c45885058822800501045d10a0048004591109140300044001d52410741c0d80c4d04401d0251601e880d04002c1d00c02620812442650b14480d819104d240b0382c40e10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 873075332 1250 873074082 873074099
    0x61e121211061306110403020303161112060901140f06041d150a05160c062d0506040b030313272409092d21110a0c 51
    0x84000100d01444060307851005581c00074460b15100300c0c06010f00c0a60107240f03182040c1102c0c140c03d03a440aa150030301052000d07803000425075031038012000c00c40c001c1050b02c0c140107d602d880c45030704940c49514059000c02507100428081d0080220000a00050203036031280d800545048440300d880740c881100040003803829800c4060844500058041c143c40200ca41c50300301000c0800b00300000007440c0510800b2606442130a902418412a90568142441d4010407003080d01b0805082d481e289c507104010200c18411100b01401d810300c450fa00001c071030291601611080303582911503441c01410160509020040780c41040b018481401e000f400c00101c0c00d00c001c000d20852120700011f40f07003103d680142c4d01c64603604a0902016061825400500140362015904801929410145440000b8418504a030162090105901c100255040c0000d603012038880d4041d015020f80b101c4202c040c41000c1114202c5c4d4000c2c0e9800c1d00900c0c0340709a50b6030715020740e000140001c40003c820442d407807 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 873076582 1250 873075332 873075353
    0x25080c04060b03131104020a0e03150c0403080c030c16030615080d141c0e06070f020c010509061303030302031e06030304120203071203051c0e1b03070b0706061e12 72
    0xc0c403c0c0c1c008603c117106100030030103d0704400d03a400d0110b07500074100304562504215400076454420883c8455180040c1242060302071b61100900c101c00c0400c030303807001450030710541d64410702800403034900880d0400040342c801200d10058a005141404082515004409803402d5815041c010300303481a250b0400c48100307a03604014501940e05001ea0709021102c141d00011001400d0008562081c95194040c2005805000401803010f020450080c40e40c0209100010341c1090821607124036800300486c1092081a0507620f080c0341c0260084101501507014500920204458254102d081345540c030760140309030707842c41c1d15034820300c010466149911249108684094142c0300701903920400c14128000021040b40415000b00303140c20a040c00311800540000e0105c0180100c4103007080380d81e1a8000d0038083c1800f200c0840c1102d45a0b181041103a0090044280f43e9a4507141d42c200040141451300481820003086901c81100d2300c40da4000406941c841c548448041c50180d484a0110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 873077832 1250 873076582 873076621
    0x60609020a2a0b0a140708151009051f0909021c110f07050d120203070f2012090a050603070207180b100c0210021603020105070525080c04060b03 64
    0x15058800b00000400078400c0900448940f100403661600c43c12001003140c50081c202c10401034404c0c10485d0030051140319116070384058481d5400350040c803a0464101c13982c0c0d0040394124600300e1004000722004034001401a015544561803240c80e1a4100140d1007906401c0780e40c4400b0318149070410800d5030004c00710041c54400c00e85808000605d000f615049507400785e070795070007281e01032668a0300240f03410342006488208529502d00a00e000c2d012040c50344980f400c10040201c00360b800d680aa50b08803030303140c030b4804491a8103400c1202001c0b90b8400a1054014100094001034509010003540d010310541c1d0050300c070407402c18218403100e1420211158051f9200c906400ca607803914242e4002c83c0445580302d182c40e440900500c00d41c0c9030324030b00006c115408201d0201034001c6a030441d500b0b0340d80c2480c28580d40d1a950400d1441c1c5840c030903001030350810106084204491418860007140c4e45401034401c2c00040341c0c20401101c80ca842400320090007000051012100c014602d40320313 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 873079082 1250 873077832 873077897
    0x501090e09030405040c020313090506091302030c0303030a1a101b1b062f03040612020d060b0c06010e06010e01050a1835030706090f05060f04060609020a 68
    0x24030f42c0d5080045d060b1120078010030003680001480345045000410b000021f001a80003d000505000001c5054000000c080c0c1240c0c2c045441c6420843d94244a082c02c12140101100d4803401c1510300c1c50000c190460008481c0c40c00c1c400c07a00c0c00385c20314412002000f422910f070101c6191605402c854404000070086844c41c84049080c40b4001540091030301810483d902c1c01416840da040e010b08104400414401e08000b02c0b41c0e80d02403090003c21202a1400c0c1c0c60010700300f00200c40302c04082d01684031340210007810080003190202d040300203890a40002c03821940b070f81c0d80c0d8ac0c4000144a2058820310300250182035240d6165010380000e051506c1a440d007024500d5904840e081a414503030400c0c100e5111180030a4105600818200d4071802090008200028500c0060740e4900c03603101c0052095480305064000d00c80c0480c41d006007140c03c8415102c00d460680e10403581054101c50860344245000008500c51803a0720a0b215400e1050f1900030400381c038a068081d084024140000d40f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 873080332 1250 873079082 873079087
    0xf0115020a0611090f0f0f10030207061a10050c0c012f250b0d0506031608030705010c090501201e150a0b01080a0905010612030c0c0b03010501090e0903 67
    0x1c1c0e92440f401e2440e803150040c00f52079005a00800c250050042400361048622041e01c0031103031307910340c0c1c81203507050200c1d40101e4884001c803055002c1d000c0d5000c0584682d00c0c1c28102da0410415105100d0078402c200c0c0d02c01c0540410702d02c19035507070207039141130601a4001c00c0c80039441c0d40201012160407005c840503542c07140581400c0500c10103c4d040543c080c4d049506500495001c0e903407401180141c0c0038054007000d0816400170402c5c001e80311080061038032100412440d032800e00c84d094003c0d030181a025443c54980b02c40f10342d41e0380b03c86021660366103031101c02403080f4803032020b91043e1031050f55451141c0002d003a4042c40e81c1290994900e03580070f1442c1c000610b0301895200b510203c0020013070300c0e03007410300540c071600c1c22001000340c185c0a00b0100051820307039211401c2648840c00c0e582c00150100d8502f005070040025401c081c0d40b1440031034850381499000110284418810003242000688079500f440e0540400c1c0f04a41c00b0480c01d5900b40402e502500312031f035200703804900b10f03170 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 873081582 1250 873080332 873080353
    0x405012313240f083310030309120809100e09090a02091008070308130302090106080603010c230a030e100203100f060c02010f2c0a0e0f011502 63
    0xc00c58803040c402ca01680c080064515a804052078070000801481e044610b003d403405007265103600b01002000402002c600f60340c1302d07011000041d4207001e060ba0b00780340d2003031070141084000b0080070301054010926400300082c0d441000044869001d0303001d900741c0c4c1000e0b80c01040c813811a42c0302012405004a003818031406071203c400c024441c0301d220005204204250051020389032000d440e0b140700c28000304042c0640c40c80065404c00b2a40e2040000365514102c64842d4040d140303070740000754000d030b8520001900a44c01321041e03020b07170400c030000c00c2031a900d00c4056500403006140c0d810307540385500d0b21408000c4044050000c0002c1400c000c031b014101d00c0413171428001c1c44200002203503030100038003407404040400301014122085d91200007604080014241c0d5120030002410888001d6503072a40d184607040030068215003240c0d04611304c080c00d00391403400d00301088860082054410000da00e48440694078000c0300d4401000d600b0340d0804104042c5100300f075038072405606c260035210 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 873082832 1250 873081582 873081619
    0x312050c0d0509040c030608060f091002040602011e020703080411130e010f06081501032d0c031202010b010e040507031103040503090a0f0b0315191e0504050123 71
    0x5140c00710440c0d81c0d06544003043c50070802103804585101080501e046001c0c010b81a00080359508190320441908055072030192903442e2500a0710380401250000c5030004086405400c0030381c62007090b18114034002c10a081e00012030051a501900040c00100400e010036050719a10885500180a0701680306108200c2d00070383d0542000303510300340c2d0b60f020307860f05800c1d035481908040c01911028101020032000007000c1008180000390502e5903021004490b00281240c0c801200e410000f41c8802c44124286140001e180d8401610342c4126807c00182d45031040c4107802d040c4070140c4a440b080d07086d10081c0802800000c021006156031050120041800308004d0740c8a503124000440d9104240d006100b45d03c94994011104207070303090014404041c9980c1030f260700c200c1444074452291a000c000400308810b180c0b00078a0203050030000728000d0101c0154103404064050b130740b10515561020f1104036402480b516003020034041d0920721001b001d1110590340c1c0380080c5960444264404d24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 873084082 1250 873082832 873082843
    0x90115170a0b100905040e030a02100e0313120308090613080906040503030f030a140f0406020901090e0a0c1701140d060609060e0610020a020306180a14010c08100f0312050c 76
    0x1000103e130312098104514075090007401010141c5001860903e2044000a942d522100d4080d00059032900c2441010326020003c0c1c540000b00c504001844503503404600043c80500e070001c2c1c00161303403400003c1040f8800103405000b000c06202c1d6000c14016515000349a070411404140c1c001030070000010b0654080000e800100c2c1c105002d5582c90400403104000c4a0b00c402410000c00710100400c100500d040c00c00030b0380181c12100141c1e40e80c0c400001224009602d411602c2c00c00946014402000c01603404801c070b074402511010340001c40050041e00f20442482181041e54084002401d242030901041d10007501c02d03080403403000d80354107495007911103542101003005640c204100c06803403c070900003080f54050003d00141001d60f00400d495510080c02400b5604c4652000c1180e032404200c19484150000c00c074003064000d900300039005c1c140c00503c2070300040489012039010314050400d541112034800c40e501e05203207140c0d07030340004c82d0500c4443e40078401d0620100a005c80d06026 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 873085332 1250 873084082 873084109
    0x3040905100f0609080c130b030f06071d1f17091005060d0f0b09030c010218011707050307030c0306031a01061b0f08090303071203060302090115170a0b 67
    0x40a0000034102042d0b40e10300250b65000b4401c10800f0203081100c00c00c007040a0311030b184107442c40c1d80c0c548840e24902c4081c2c441e02c1e0055070144144202102c11100110b1018021140c6a40307086e001e040403880700b04c5444030346940d16882000148502c121806041e011141000c82e030401500b05070820001c0700e03614030b04540d080c0c1c95411090180d0000c9019114042e40190201c520001c1c003481911036046001e02040000e0580b4101008110011010410f071003c030b0703188800a5590703010350b1007145154644815605d0100d0305a501680707000a040034001c0c40b034042c50ba82c00d415655580811000790840204603028190b503010040b000c100090070355041c685984031490459490890024003d007a0001c001e030b80401c603013070040c001885807060040310030381000c1c03541d48031050003000a00398420f505000f04480d80c0340c0000c0341c5182c2c0580000c1c0441e4021941480c00b42c0c0e071032a00f80c400c030312495004c10020300340d402213140300c0440080c03054000300b401000080300940c10005c034000c002e0248 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 873086582 1250 873085332 873085351
    0x1030503040602060a0c0c02040e0c04060f0f060302070305030c0702220e0708010605030a200402030108060702010e0102091804110a080f071a04060f0302090d0f0317150f0303040905 80
    0x1d401c2c082c00b0b40400c0410b8200f1010702080040f07503076800700101950003004c0003d200300d884100d41d040c210010041c504081200410030003415503a0010b00724600198415500361440072100000d82c24020b20960b00c1613030305070712860715568849204400700d43c003102d002c0340e000c4515000c542c000d80d070f040303807140d00000250b40010f22420840400b9240100d43c2d8080140b0381e05000c014807540d24041080040c6503441207440034008040403892035906980f503146508a8404000013030a03600000e18a80610070356002080039a400c00c000600342d2180741e19264100c0d0340b0b000c210307054400c44c0268a41c464000d2014800c40c005150000f045030380c036540114a15481020440c581c01018800f14004094006210560002050180f5464010707403203004244440d05038038500c01d50107501221602d0b10014024170044031185070800702001050381c02d8000a803401e02c0101e40c880310146090141e0350141a81e442100344004014204100046581d0140014000001d01104600440b8018030100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 873087832 1250 873086582 873086587
    0x110703060f0e1b010504121401020c07030c080c0d02130b12061e0609040b0601020a08070b071202070b06041107060608061b032208401d060a030b01030503 68
    0xb41035003441c02c07800340c0d40c80a102c0d0040b88158581c2c0e0b08001210101c41e11445002c44d4030301c6078108450507a24140c00f21000754000100d0201c42d00001c45c1d880e055070f200700b08031444291209480c981d14000e407009682c0108208140b900540b03021480100c21000154010400402c0d0401060048581d00d440101a502200c1070010104003c101c41c2021b9502991115103480c100f0001518001e001e88082d240b100b0031b50109840740d10134007042030041e400281071036a03241c00b0f2400c0c0d003e201c011600b5500041c81c0c540002c50315085402103a4206400000001c2261120307010003008003200c0d8102c4845013000c1140a0000790503000707200007480c918018106a141080700510401c9030070b0000c01040e203042082107001d522401c1c400b10807101031011f52075850071904c1c03c11090320410901c501052a0180725580f0311441080403d812804540c400840c0300149581949503001d0307000302c070343c41080c624805884c04084001c103640b0640003480c0c01d01407980c9480d0540c0d004c81c20b03001519282c100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 873089082 1250 873087832 873087851
    0xc060f091b0b0901080606160209010b120a2a020309190306140402060d0905121b0705030708030702060d0609050103050a0b0709120308060a080f0d0e090403020d110703060f 76
    0x11101008002c01e50b8070556442c01c00b201e8002130410400401e07542c4039039000300b450384000040440380d00c4882c0d80900f5141595848100b081c9050300100741401c0d01480c00e400040f23130707051640258a05c0d074001c0744607902079400182c0981824a00c686410f000c500c428400e404250740d800c2102c1d840c06034071024440b0900e040d8103003401503030425506400c02c1d94145d0180300041c2c480004035100d000888800040b100e001d860618184050f010200c14200f50214941440007644c1e450001035442031b00403074440d00e907510207064682c000c0740306000254005120240141c1002c130b0013011320080114000904907200d01c80b40c011a8000c1e003003991240d224004103c104401c207203103103400044609001d04820714010407103220454141d070003010403900d480070400c1034844d0305100c1e01428082c0c1c10780e1480f01546c020350741c0d1001d03040414000299000d14448480c05c100d2222400355400d075000d05991129000152507848d0b0b81c3c28250348910409a000010800030f104031414811504404602c0c1c405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 873090332 1250 873089082 873089123
    0x1006120212010c0507300306061e1d13060305010204230609040c0309140105091203010b0412020a1212140901080103061508010e0703030f08090d0c060f09 68
    0x1403000c0038441e41e078900307010710f21081d4103d810744519a074000031800d42040c1c44002c054904000d10010000c00311072070751405030300750560050b5007a5403c50390340c000726484070314110003a4084d0341c55401c0030400b0304a240e00c4a0603074440d01840b00001500e4944a01d0010001c0c00071540b090b40309980a0b507022900b4440600d801d55501c140f007680000650f030768450b103400900203104642e041d911881d40c540f030000e00c0c18001d411081c162904154001c020b4100101014060001119134020a0065500f007541d03550805080d6816500010310706400c060802043c1c004a1600e101d0030390340b282c0c2d5840006042c0b0115025440da0724442d4605000030040b010001e8503050240e0b18000d0301c1ea01c184050341e210390f40011201e044039001030003c2010a8480c200452a803501d40201085500b0002d000742c1d15a000035020088038440d5640060701402c0c0d540c01c9a4a0000761820125074000340800b809070743c0300c2c04012101034059000002d07101244044202201c1419908844040c4000c3e069070b43d803070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 873091582 1250 873090332 873090349
    0x305220f14030309030a03050a060302130c090909080d110c031c0b0607051c050c010f061e0608040b100b0a0e04060e0106051605100c051b070605070204020c10061202 73
    0x1c0228000b1810350501c014540d450b0300420300b1070810541d03107800290307950180e50803010040d034014118060104034003803203030080c4c910303180e0410104200c200001401c0c180d40c42941c40c001c5d084100c42e4242124250141c018101203405c803c0c50640601400c9450b040510051416003160f001e2924546504082d4406455000c80700c24418941403100c0008900e010920105201000c044001c160075400005d03030710350040400040c03040d0320303100300c2e010914800e61022090710b00210075080711303004d600800800d507048c83c0150800601d807900407900050764461050340000522a0081d03989407510050301068000030413400c0003900c2c2c0c4000781c10303d003414850603028061401401074158108200903043d0f120303140c2915030003c4400e51860a002040c440b807a0300e50201d80b410300422400740c100a005030048182e001f01c51076031030b03c481a512800540081244d80d00c1e100e407802c080d156001c0100941040f10540c2c140e00465410081c0a03889106050241c09090412451030007640103100f42039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 873092832 1250 873091582 873091613
    0x111e03090f0c090115030608070f05091312081b030a05040b10030512070305071b2607060e04090f030f12020f09040915020f040e0609160305220f 64
    0x940100d031424001d40c507030210044c191a44a462200c44030b241318003c40003800c403a4403500841c007074984042103038017003c80301c0c001300c8504460903002038560740307021260500445402811003101e03070401d03040700b402400c1c030b40c3d0f02c007070303581c1081018020351041b9540586c000c0300c1d28809256a4401c00042200100425401c98230342040b070040c0c64115510999520409114162400c4c5c0100d100c204062141c0308680b40c1c3c90b07021070070307a18000c04031100c0c0c00c3c0042640207814211048665241c18010181881110a41d6403030007400e81c41c0c41c2c2541920031210304002e140d041030f25100d01c04c0101c0c20906400c104e461080c0d5503441c040c00098801451803020261000c1002d00401800c02c0c464950401e49a10036004c039000036081c4001c0c0780400038550208048480c4a0000c100ca04220a201c0b0140c4201e8407415000f05080c2ea4200800040328400c03204580003030102c515003908070380f080c0c0c0859804460f501e200c07240120040701020200c404400100d81c0b416050320181e080040b03001d4501d610 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 873094082 1250 873092832 873092863
    0xc03050a0209090a05061513020f0901080108151b28320906071a0610090509071d04020f09030f01090b04141002030a020912070b040504111e0309 64
    0x422115944954596070041c00c01004403140c202c2a125541d08c0c0c07001d04150318001ea00071592404004168055900402c068a021461800002400c0900030070592203034846080031001b143d07a00d2900110b018007070740760000801c03c18400850100c12904211255908010b5666031084070b4400003040309904160880310503c00104c14010301c80600160f42c5243c2d0f510701daa54130707050786001041d513500030342e174001c1c003185c0f28180c41840c03403144000c0c814051002611150403041a080059410019611681c0d0700301d4038401c00664100e12039140c44003914201600000744824084c0080d0580e08424554003010000182440041c40c00300104134403030f000d4000901c1452259101c600c1d00050041014005a1144101200001043c03080c0110801d803c8000c5403a410070000c0744c00250455464503001d121035404071260400c00181c1841104c91000c030781e40c40e107810502444050b02911003540700e940024060040c0500c8100e000284a10382d0140f0b240d22842c04180c070070b1130b00d4a0043e49564 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 873095332 1250 873094082 873094093
    0x712020106151e050c0a030c1a2401020d0512060f0a09020405090603011a0603100e0c030603161a0a110601060c0b1e0406270305031603020f0904090f0c03050a020909 73
    0x3041017002c9032101d401501400e100c02202c19504005007004202d4030407855804213a8200003810381540b0390407412060788600001c8280c400030040e65542c0743c1d00d881e040840c8051050061580c0c025400c3ca030710110240c18001c0031078141c004250340100c6c0780c1044040c9034002c2402d1045080010446070f009104034003c2c00b03a0a105024048400c0d403542c1014080c88002000a02c5071300040031400051441503140c49070751414115441c9140c0041d50001e1080c0203094114409000c18030b180829240481400c1c150005c0d1500b465500b98080c80002c42031110350140400c1780700303041c02024000d140e16164803004030810f140180c1b15407001071510f581e03020030b0002c50000f800860505075000e075100c0c1c00041d0394640032026003108100140050300c000c01d00c150b02410181d1140c0a1402610b4107046001100c0410300103a00360b004481409244d483c2c107000c01006403500740c01000e0100e0247c9100d840381801074450102074074503a001942d66601c080800400c506040d8582039202507180098807 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 873096582 1250 873095332 873095347
    0x910090206070219030b0c030114010c050c09090a050102040b03090d05030705180f130b1e010509040c03060f080f12030420040e01091103210712020106151e05 70
    0xd00c24091850040d01902c40005070800c107103010b201003405107800448800b4030307240c0704a202c7c12541c000d00400e1910502e007142001c1d40d5005001c1010340c950b000020300303a09c0c00304109009801000900030f23942403140c0142d400100e5002c0c8028009480e0302c0042d1079036480c148403020720705550714900c641004020800c01103a250b100050380c0c0a1645800280e100402c81000903101e070f0b600808480c0c4c0300f12036540310420b9402e15800400302074000ea40740c0a0300d522010000d00010001482d86020540410031002c03030380342652000d25008968140050203540302c0c0d09101c81c4003003075088043d0560060401280d0503070304000c8104d9180980304d03050f107540ba0542d180707a01c194903031700e0700d4180001c0d807846402141d4072504920040c811080003000155054127046100c180f406c0c0c442800307070048a00300d204444840603226440c8604840d0780b8035141c038aa0780c00402041040c102001c55581e2075020030713401d07080c9040158030010b65448101c0c0c050302d1910b64850700c1000740344000f03104c010000368 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 873097832 1250 873096582 873096589
    0xb010f03031704050a02150306040515281a12011a04090b0a1505070b01080c0609130e03040e04061b0e0105160f0506070801060302281e02030309100902 67
    0x42c10510281004090303840e1868603a01d00280d101e030081d40440442e042540d48400d01c0043d601c500f1084a00f880a601d500106c4900c0e018103c004a8008114200c0d400700d9199201182848894074034459034600c3c0d540e880c01c4130040c2485103490000030005104511601003024070f0b030140041929030000381018401071565403046201d0440041d484511a04160391402d400e0002058100c00b081d2104d80d01c007200400541c000641180c40d04c3c0c02100100d0904800900031445035000b40540c2d203000d001c1c80c100300701d4407600171042d48110345601c05000c1c1c4250070303c09800103000011004803682003a140410544000ca401d044500104504803230805600c003123116001d4000313081c0251340c2c101c1c3d604540d5500c031941e07401522071408410074030200700d80042da00384186050760b14450301340d032210000c41c10f0b442203564200490845041c24030a0b049100d041010010460900707200702120b400801e01c2c0225401c5082d001741e0400f10030825024800c0c081c84800042c1140f08000c0d407040ca9000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 873099082 1250 873097832 873097847
    0x40812030603060621010c120c0e210316030e010f0206040c090e070806101d0c090f01050c100501170f0601090b19090204051813030f051606090b010f0303 68
    0x806124414081c0300746000c0302d0380040203001c4417282c070087c40940d0a075403002d404015039851111025282c03151207030103035204244c0800d204500030450781a50b8038849440d8403042d03616a00810301c0c00104900001c00160400d15400030340310745c4038001600d2100c800904030064504200c4255080705c420400040c0d442d107800300c00c0e41d44031040042c01388885980a49050100c9c0c12900051142c4024011241058501e0000320f50341c044e075401440c120210fa100070010195506024000140601e50940ca080d0948000100041c50050700704661107040501d08a5140d10000c0c10f50f95400c010310520071200c80141c1440b04417401004130342001c01942d0b41e90201445000c2e030f965950662204196100784590100003410750070084542e841e254444001d61151080e107200c0c03050910040011001d00d1101ea2103180102c5030200d882a154800f41c07444902d680050f010031000300020075810b10136100d07450f6080e0003508002401e014034035100750a1001a00580d44d0039003480703800c20010303900203034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 873100332 1250 873099082 873099091
    0x190608070305180319030e2d070b040902090103140a0b040b040204050310151a041706071e180830030402271e070914042007030504081203060306 64
    0xd8081d10303131484141100109426100c82c203d601a81c50841c8008c5501c1920903091680380740205450101d07050030300d589060610070090302080600c020008030070541e0182c1000081070402080001c115030101c2002c40b001c42e03403014000c1d965040f0625074103051107031009201046d6011484c2600b4500003980d160303002108410300548529850b4a648a41c0c840341004154101d0456002c64550340807091079042402000c15908210900070b108100c0024032038050010340c0c492524400690114902c0c135800300c0d0406081c00001441c1d65074410703070a00d80500920000001e403202c844407000246c4060040010449100754601700c010406000e002200e401503411283c005850b04003668450054200c105c0980b074031140e900c2081081207000c0b02044003850022500e52441d541c0780016501c4001502548001c8070012206c0b640341e0616a1141d5000d021113a0564054500440e0003549980030910407000146d002c24204440201002440111404054000d04514189010a9640c0001007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 873101582 1250 873100332 873100357
    0x504020f04090e0303040b07090308030c071a01060504090b010801051e0d120504030c0506121611160509061c1211011503020906040908181906080703051803 69
    0x98140a00c2040c90489008205864007400618207920b401034a03500200c800ba5600355000001443d082d1107841e80200352903111001c1c0781507480d661042d405642010700115000f00c89105031032002c45180d40c065000f03080c980c2e0307040e66541c00c240c107441c10341e00c0304441141400303c1000184415650146600c0500005c648000154030420001480c40c41e05400040d200708029101d550740541c0c09801803042d41d00404182e5113081d654000d0000612030200aa512101060040395441d94044002e114003050751414040910f44042103a0800c55801200d005450500c00f007000182402e03003940e0ba001c03900726610543e1034200b0703040500d44580300b9802020605a41600d000490148802000d600a1000200721110211002106040c1540016031046522a0010380b0924050007a007041300c0d88a04d0341d6040413070052032803241c00c801440b070b241c1c0000b001c00310015107041c981c030b41d01c014060756460786e507581040c02c030240866801a119401280480038024618003000046407145d21608 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 873102832 1250 873101582 873101587
    0x2211b1305041802100c0b130525051c2114070c0b0c0a0203070504111806090301020a08070813080403030513170a1407030c121506060f1106060901050402 68
    0x1501c0d83d40d103607002402c02940010400000d40001e0391010042031007511030f102d440003d84410154046030402100008c100303501000501c0c04e2005544a01001801d019078801411600c80000a2030480c00385d0031540340c0c5000c041088148030420f41901e03034420580d060f5103072140d032414004100c0d1881c0c0d02ca50030070315000207031a030400101c1c204210080245001207a10360b1a0000403075101c100f41d440070380c0305c1e2095510124041c5464400c1d50440c0c0d0044103054a4a03100c1c0206c5100100383c28441c070303400744080c0a40c0350561020300081540c003c80303544800c11885d081d80f003e00000c5003d04010620b80032012807400140c884030440d4241c07500350422503180d03c04a010000d4409823604210020f00e051007915603002000030310310105520505e11a89007010f0407003802d542d0940c510014140041c0300f80704100c011b500001084d2214020070a05410040a9828400361005075015500040e08140315200c020350202c10814020403041c05041c0c1810040002105007006010f5540b095030300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 873104082 1250 873102832 873102851
    0x100507080a050408010204240206270c090f1008060105180604021903060801060e1905040515040c1d090d0f05040f080a031b050604120302211b130504 66
    0x14105940044c01004004d569840d00c03220b021003180c442c0601040c9450308a840141790320f0003c103265204008240d05580c100944811072441d030030380024003500c20b01503ca10f186041c0c88810802d481051000c40c09022800e100c01424106203039544580c86a8202000501c650358410602000c0303c200c40c03001d440030f901d580000800030301c07070038000b020002e0a110f0040707070303903038054110300304880c0c405008100e2560788a20090700c500381100c02c02c240071008000c2c00c81a204036841980c01c2401113084814a0390f85071074542c02e000c1c017607400761502c0303031890000c00c0180d08501003292010164160459182003101c501640c80180080c1d0b90180100085103140300d51290058500a10340804022a420382d03c0d0000c1c1e80300c59482802703800144031201d1010701816190b4030072031500d50110050403039076280e8484544502c0a15045020103030200400560071400f10311800310a03003845200c04e4981040d43c0222800104040304500000c0c05000000d19124901001d004880c01981c010032002c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 873105332 1250 873104082 873104087
    0x50d031a03060a060305060a0207030918090f0f230c1021050615090d080924090108090d0e06130308031f0905010b070807060f020406020a02040506100507080a 70
    0x80100805401d072040404012010645400ca81c0861340078801342c0c1c00c01e444402c1c900c410b901c034a05014005c00d107000020807081e1000c6107000e0280f01d502c2c400241603d01991072618204100105996021240150000307104100b0346803025181400d82060b110300400350840e440b40504204588030705001141400380c84d00842c0e54404281002111000d04523115035004000c000594145025082580d91855410210400c589410500070f182c411250125038603814144d000b04d0703000d034100306500c14030301c1d6642061075000f030415000280382e80c480307400302c000402d1158020903410f080c0e4091200782c90f009402c46504001d088040d41ca080d500c90b80d1842aa4040c20560302c0109044000020417403042031a0542106a580c9010590392503a550110038047d91002c1c000d034501078200b00038540000d0fa0300402494103520500300400c4100c0c0000790035007240c01c56803090380560062000306045203000d100740d81c0e209a04a5092100e2000d81200815030f00070342e9002005120000b600309005c90 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 873106582 1250 873105332 873105371
    0x60f060e043b0f011a0d08190e19030b1f061211031e07080106050406050a2705040e0a08031602030c1b010807030c0c1721091603050d03 60
    0x210300c1c01225512154540fa0038000c2003161050384c44094240d050003d14030b8180003080308940c20000443c100b00c0c640ca14040b081011540d0301c1d0604c04200300390403054860702d2038100c544100c1d1555644040ca50b00701450711600080000611002d09504100040d60907030060f010780e6218944070310a2200d04580301c0050074200c034a0301103142c01100700842c0c040c1d85195680030828520070708407551290721341a50a00030a01400c00030440510080c0200d9116001500390a4a14503188014402c009118408004500b031035840b688011402400f0908190248008034039906000f4254176241c0e80305e00c0d0329800090001011081038a41c00d0b4400d9108200340d407e00240502582c1c0c0c80c0c441c1c81c000c01c030160541f03201d80c0d01094a000c0064000c40c001e120300d0f07144090706d0f00d8550344400c80e5034403811541203202c0840151101440f04c080360010740c0320a0700561540002c80e0003d814082011443e00d003005028803000c048a4200344000340c0c0109580703040020600340803441c03134141c8102407a0389 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 873107832 1250 873106582 873106691
    0x50f0721050c0d110c0d1809051003060c020d1409010804020d021f020f0c060c15040303150e011404050712050a020720130b0d0f060e01060f060e04 65
    0x42d8240700c8000000c4c80044001c2c015802d80404482c20501c8511003a43d00d00281e21007800c03070760100c000070848050309030002c3d13501505040381c2800700d54690f40c50030104d605450711280160b00184084512a070824800a0b13005103017076810341416440d8000034403c0a0043c402806040350303010302001c5441740c0c55003602d1030340c4901030b208030602c141c20b0083d650703403688010300b503140704080000c04203040c240c044035040e00d5004060803407a541e00340304004070f4501500490070180c0d11a0b0186503240c54441d00e802901180c48816060752401c5a59210070380c68200c0c03907100d1480d110510011642008110940d0380c141032010034980d031152210030081c052100081c01d200e0b0000c1d00049002000030003000202400c0b00d009a05031400300c042d104a80c585801e60390090010508000403450990710803c80610076500460a000b11440d1030f42920303080c2d408500095441c00051190f41c0d0812100c100307041e000e07502003190003248075401314540b80c6440c041002c40420054801240940400c45824 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 873109082 1250 873107832 873107857
    0x306130b030c0612070e01081501231303050f1605130f0f02040504180b07110a0c060504080607050313140c0d0305093105100305070801050f0721050c 66
    0x1a04d01c81c0c6100107045000b00c41c0080010b422044068096000303030b100e9405120b41d00d0741c44064519402c01900c10b04540200d07000700d000312402c91850000d80d48002e000214103041118811455464120316200081d01011503540100702608420380c906003022040f10000c0b900c1e030380500d010b642c0000c0204441210818002d0514808900001c9690000c104503a0144e50030812941050f4032030b0050029810024a03c0040f07801050249200d1009a881c1c624054107030f601c2081d15940c0c01180c3c0045034000380210b000840c0c100000841480069032085c0903040192035031500d4940305401060207100182004074601420b8102481000034085000000d010042c2c42c0510703050180c29500410411445400c5c004080b0050b50719001c01d01450b02001464645100959007016005e800c0007000341981c025822800408508100104c00041455200000300e504050809581e0740d41c00910580c140a5001080e0340c0d00300007c181540325118810300044c0390b403104460003042e4070035811112a03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 873110332 1250 873109082 873109087
    0x9180c180105040806041a071b021003060b1201031b0608070c030c0803100504060503011521170a031b080a0c02010b10031d060f2a0304030e030c0102030306130b030c06 74
    0x2001200c0120a10140d040c0529418959034088c0450380c60b0030010f40d04002c0010180748100505052650000000050a01184050300c450285c00c20703400c640b84c00b00c0440e43c5a401041480300710141603000c101d000d1248a809030030004040c01c056009020300c410002e80c01c0400c0300341031144110b6620541d0203000d25513a030a00982591407451180030f45e80c4584c0c81c0010000f02c5240c14465424007144880b0050b0000d440c06608000c851428001800c803035462608030b00021703070300400c1d1f103180c428092500c0362150710f0038600404480f4000e01503000000c4820781080000c0d0071400712507200d400d03101c010400a0441c14200e024014049000d0b03003002c0c000c08041c0100d40c160300009000c0c070700401b404a42c0d4505c80820742d551841500e20001c888000e4020070750190303c96440300003501001c0d00803211460710f90321855440d403045400f40d0028030000c1020000e407238280081035414100348001c45c1541001030025a80744000903503c500c06581d0100781d5207036181400040c1c03a0303440c0280a2074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 873111582 1250 873110332 873110341
    0x6030115080f07051f1d270c04060c060b04060305011d010f0b060306120c27060103201605030a0c03020d08010815070c0b010b09180c180105040806 65
    0x1a9104810000b8004a004a00300820b0304c1c1404400d5480090b540c2042e1011202039220035503807084042d0141c051301001181075011902c50321701d000c04c01e100d4041c8051200c400e1018a00d40380030050b0865030001c10410080111961040f41c070f8080170f802c130a000820088050015000303003502e0348000c0c055403c1103123103400d854040d500400c1b11003048000340310940e2a4005070040f10040040c241e407068003400401c5d02800c00480140440066000f140c0125050100207800065000c100c9a43c4220020141007400350748051180c01810030b08091000c46888a071260382324040b00b43c0c1c41c2c400c00011681c1700b82c2c8000c101d1044c421a070800c0a69503110702202d00108083d401c600c00b40e02520901414010661241e20554100d884400140c448014001151312044a0181980007009a0741001c90082043c0d070030194000c06048030025030301e944c0e00c003d215030140940000140d00088501300b090b10904a02200c46c2200903480582c06403041c00e0060390130740501c1e00110719a215590822 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 873112832 1250 873111582 873111599
    0xf07020a0603020406021902100f2003091c03081b13030b0a0b0a0f0332010f06060203071703070c0f0c050f060a0c030e1302071a01060e1806030115 65
    0x1130080d151107500303803001c0660b40780800c3c04c0c400300340740000d400c06031954546481c2803054101e10343c0c3c005a071410084504202041c210002c0a550740fa03c01c03600006071002d190b140818003d0405002082c40b0a003010150300d01402400d0010810040780340e8400180703003020420710494400e40c1d400d2501019607038881c10240320b10801150041e010030726150020035a07140500310141150170490140c1c61403401d681d2280c40140e030b0240d516242d0790b030100c1c40d241c0d200b0152410714080c010000001500c00c0c00b8029502c16589541c2c00306041d504100b05820100c0d48006c1802c420f600761094460341e94580000c115440c03501841c020f440c5845420004c010403004034045011608111814498081c600d010080c0f030744240314241012a2030070050800203400f07061041d162840c0141070541c410a51600442070381d00c1141c003140c030242c40f508144510009105401d001d0821403408100044490340410040302018451078106241c840c0040c56968094010040c282441545d801c8100d50300c9500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 873114082 1250 873112832 873112837
    0x804050402180405090a02061603020309090f070f030b03030d0e10140f01080303061315030203190b01080613020607060902060d0906050702010c051602060c0f0c0111010207050a080f07020a060302 86
    0x3031442141084c011421801c0b000611091084d001400e062814034844407241d113505041c58101d0960005000106442d5140513001d80300c0d55100c0c003440740300e182200e0000e042c800700c14040c8080c103250a003030000356240002034840520000760001602d443c90031180b440c2403103181c6a00440d80c00c00d544d41d2100554100744a0240c3c1c1324a14110407030341c0b990682a100d000480d1815002441d010386c2420800494110a9154001103407a07e460b80e00c9402090505060211002d825110b0200c9401000030241007203005050000187c00281030035444414168209180a031240b140804d403c014801154001901b80741c3c0103109035038402441d0f916801810300e101c001e84403075140c14000788000d070060081e0f18000c0f4186e901c0f1480c018a4100f0818021060402683c101e5000d10104404980400003811042c0705070000b800d440d0036120004044540442084500f03074010b12600d00050070004800d02c1144e440004a9203542c025100c0f6800e43c0294080130754804854031000806a405500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 873115332 1250 873114082 873114127
    0x90111010e1e281b0303022112010602061f212a140103021201030b07030e16050306090f031215061606060506040311130e06040b090d0c1104090804050402 68
    0x13402002e09403012019130510000703110140141e0001200300340d122916100d290100b10700c4050060030b21f80000202c100070b4509800000c0503900582c1846208201d05180140070140340810311555402c22100f5001c84100c4505004c40c0501900e01000b040700008200007108024000c080320140d08902010900c001845507031040c034840c03407421000354403078001c441c01d0480501102e800d0707034610f586440c48c003072000300514209a0b6a02000406c1d18043c81000304240488480f501c115080508050521201a0529040d0303402910144030141e004410b40e000d04981121440f1903954626041000c4000041000c0d804900000c91a0f80c40340c07800030301401d041c080d6004106483e251420300190384603d00020b0107120000724120140c3c54103401c04000c00c480c4003000310b1107802011401b482c1c040295400c48080a08200f004410343e030402074902d0b195010b15088065a0490b10f4050961101c00c00050045496541c14010301142c00c040360000c04018004640e50380401d02c480708005000b54 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 873116582 1250 873115332 873115343
    0xb22050423071d0702030304030c0204060506070b01080606010801060f0c05010b09090f0c09150906030c0a32010905040504020f0324010807031101050a170c090111010e1e28 76
    0x60f5010840307441c40f100d1031080005800451940d241d80d14155215190004126032081d111400803840d5101c1f580034081943c0324000144030b550400060600300003000348003904003c1d000c3c0c0108101c0d0381c090712000290100d414114221001307410807501501544445a8016a4210900c41c1a0700001035800c0d000803070030180c0c0d5220032000308000e2070400a83c0c4030400c088000d8042955858502007a540025008080b1042d1a140d0004110310103515401188605401c6003910320080c41c8218106000215440b00c1103642041800a0021450b60040b1405a40e490b00000d00f151250340700d41d2441030004080b101c10084e01800e110756000c8440d08a804860000f0002070340001c001011000e07643c1c404c0c410b10079940410011a82a0070156481040116040c0c0d4031510a00000d8114010b02c40c04140603607501c0d4001c0090f0803220154880e040e05c0e8500043c03051117100106183c3d055050301c800e64085800805180707840c05a00029101c2000d0844007410b12100490401c510035920a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 873117832 1250 873116582 873116609
    0x50703110f0a080c060a12051302090703021c0203040f02030109080a0e06070b0705160804060507170903070e060301021209011d06010b03060402030c040305030a030603060b2205042307 81
    0x300280102c03418148101810340d840140c8105a41c41c140b8050819910546083c40484824040347c10540b407041c0d8042c21018084111003080d42001e1035815802601c5040644c544480c6510074600d213202e110b105800c0c20303400b00101e0300b0410450a411031131794001b8000d0083c07580c0740c10700e071445900030303100c0b00301013044055050700070304002050b0b4441e25041444240569146207055440e6400603140f81c1c450707510418035100080c00840544080d00d05603462641300d41992030181000d210b0481104421241848004819a00051100140c4171140701a4400d80c44074408240640180f4042040c030f02c00400420400c01030546c0100050b007402070b00e040341030741d145900c07a8543d0001c0c003d0081000b41040083d40504141d0029604030388901507207850f065603030b2a16400d541240c8401c20009807605002c02c14441503006400d12010304803048010f80c5503200301070300058180c01fa0031780165120000501801b54044035240b110388000081074600c04c5c85030031079840d680030303010b655a2080d19 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 873119082 1250 873117832 873117859
    0x2010e0a030b10080c010e09040b1b0712030c030920030118060b1c1505190501091509020406210219090e0a09020a0e060d05010e100f0b060301030209040f05070311 72
    0x46071704d11002d1001921030230280d292500c425030012401000320302546c2e41312940703c60410401d4000c00390f050060084074646c00004100400351003000c410041050700340302d50000400c07544c82000c206503000342c1d0703405200303448000803901618124204076540002c040b8080705000140d00441d01c03034001281c40301307900c40070074103145000c42c581030025200252401103500400354991007a90001d018840311800401c100700340740d054034000d03082a00960f4035014181600c90143c00700001034030021009605060401c1c4c0001d16071001101c0318042000f8401040041c52620750403914018110380300b440856a00741400f41041000b031003243d180310359100001305410403910560448590050025400c00d01d0107015044104e8013420f0035502c0b0205880e1880051400d208044801c0c1003000500680045010700c54100e40403140d1400b006800c0c901c11070800d07520081280c0c1035039411503221049841d030b4140304800e900c5490000b4218030a40001005000000001c480240011110588240f06 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 873120332 1250 873119082 873119087
    0x5070b0f0121030203070839120904020c01020d0902030610030c0b09030c030d18050d0507090915050f01170c0906040209010e0d0f1b0602070302010e0a030b10080c01 73
    0x500b4881e51410034080c11503280200300640d41005800d000f403040ba81040319039181e210841d44000312084100501040354002c03c485809080001001000e040898400003031000d0b0301c1d150040084a002d5a002500e000960f5490341555501c01100c00210349540f056038824005204d0303050161711900c51100002c460700c40d54860001a03e512000c2c0038500d510f003201d0025a03402440181e94140140700e08410aa141000843c26a00701c0d81c0c0d41505e0151304402600740513280c0e40005008480390703401c0b44081840020030301e04a804d1070344005140e000e9418000044510119200b0780c0354248800e0045847d200300300103060f03921868800c43c1d0b80590341d031120f9680b0074440351302d90084a51000900700b884d041c3e0107400001ca042c10300018500c0d4160008403545080e007004c44031205040d90300350500104a0b02d02110809400035008a0760807d1006580c1c0c400a1000038100840801c880159468401d040c0c0c008582c00b50403c1d100e400c08508102c80403246000320b205501c110b120a03d001e40c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 873121582 1250 873120332 873120361
    0xd0201061e05130f02070b01050a140a12081e0903010b0103090b06010c03300e030309071e030b010e0a0c0311070609020f03030f0d0e1b010f1202040605070b 69
    0x181109040901610b481e05001a000034600c0307045046684d000610840c4009000030482144120065820b640c140420000107803a182c001141c0e442c040304811419031a01d044800c19515001c0c95160703503664501c3d06ca4807d1080b00403c0685800340503410102c0f03a00d1034003a02172004114028080100c01600440807100c0da90005420002050082052540140d2411007401e01a00d07146000c40031b1039a04a0110f850303200124485640381402084000b2603204040c0c0c3c034a2400c000d1459400d0074102a030382c8440744c1c0941c0f110507038011014808a80c0c0070170103c0c0155400078403480c456a5604032509521003c41d804104070307040c2800700c22035a200e8415034a42c40b80880055003040314075101c80000741030b105000c03608059116032100003a0780403c080c02d6409130b0b03403e40e1917070743c0142408034041c1c586620711a500d983c0601c5540d01d6440c002030b0800d012070800c7c80e0003541a85102404c07143d050744001d13100a181d10001d03002c5200c55108008043c040e000e50020b100ea03841d83e0303040e0907040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 873122832 1250 873121582 873121619
    0x6070b010602070b0a0c110a080d260603070303080c12010303080414122a07120c09050919031b031e081003240228020f0c1207080f0d020106 62
    0x1070b000c1d146c480300007a00e104500c10181da014048040d01603d4882d0b1b0380c6814141031960012400d00c4038084050314081c003d00e020406810f00c3e00d21982010000700b41e848405000003010300098400144140c00c880b400d568040054002a4031656502e040140c4a050241c4e010b407401c005200d018642c0c03d03800202c404029544e851424940310281640e00d190348040c3c17110000d9032101e1440b100004108010003006010300702616094200c080c600712171202042d9025441c0141414208000004081a841c0e0ba20850b006203114171005441c08562034001c10712604404008003603d8000e2540c040c6850308840c401401801c1c06036409141580d008404a480300c0341d5044910b002c0c00010310301520300c0c42034621650003517814004103101000380d0300912071065200fa007241095680d104084110001403441d40068034a00403458003180d110860110001c0c0181109031841c01c0c2650100040360050031114141c80422026091044d180d002e2107000d100150b0074a840401c921b404a884401c41d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 873124082 1250 873122832 873122837
    0xf02070c062f120403050114070f05030c0d0908030a0c020c2e050403200f040b0117090705060c010e0105150120010f0c120f0204050607060b03030906070b010602070b0a 74
    0x241c001d100b01a00d600c6400140b00c40c458000d1003011620780c0c44490150001d54450750022988900d0741c684c7c819031610080100c420004a1041c0490a40e001412070347c208142d84c202e156140d044107680c1c000341088440003441041c1c0001082a456031541c0200d141144070750039240a007802c1010001c101001c02981e14002074218810b0310780c89600c00d011020346400d400c1c00c2d0708050740d0f900c1b00c3d640580300c070400e5030320308554440408183c034080740c0c0b000b40b680b4120380400c050062440024006001c0406d160b407480542d0000c00e000080400c00318000708402041d450b0b4502e000b003000c81c06010680d200350499800d00c40403031072a80030130607060f98000f0180d64190f120380d04011503c034510b4555030400c84035585d0709201d2000080500a548080129849502c99041140c00a604a4008104d400281c41c414481488290754020407103482e80c1e00204046000302c0c10400080c00d500c1040c00c210751055000480c0001c0100144080e8102c1c0c42c2c07502900c80540ea00c010003600c510405102c2c400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 873125332 1250 873124082 873124127
    0x3090601060504081e0f0316110d110904170a09030201030f020403020f0d0305090d1101020d092d21140c031009051f05010f0501050708041401020307060f02070c06 72
    0x10030411117503042000c000040840305603094070302059045500c22013140d80c002c2c0a00d0500001d00081804015940b08262070b40100d200c1d0646510505043e002100c0b0302c28a248230100d0f042c0507250b580d5a6444101c40801035480006440182c40000d40e8481203000c6410449190356204161003500c1c00c494015004e00501c4100382c04000000700700f10012002c0c080c05200c40500f9455802090850700d2144900f070010000310800a80b51802e0b9007808030030070010380c0c1c06010070040d0710924011042c088001c4040c04030424034444500f00d40d03400070488184466100d0803850f0b00d0071300c0005000d000340000100c082d100300c18940c648070020f100e1900b541c010003800d040c0c80300340d0388049800342c019415201451081c90020501041200d0491105a01c03400103200741c100030b40c00100202001d0130464079005103036032600012301079841740d102003400e01070380041964000c0c030481384140d034041c0080001c25440103103c2c000303400410050795028014079000c20058064403240b45816508042e42e0f8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 873126582 1250 873125332 873125353
    0xc0c0301020732010608010231031113050a320403140d1d0105010f0501140a030e2410050117040302010e0f01050912070201050d02030c041a0309060106050408 70
    0x10000f070240650034140a001d2022140640f00a00c69540a082100000340e40d645800407090a8032900305600e107411070b1011402091761000d6070481d81142c0d803190988503c80c0305000014256010f00b00300503081030910b8100071906d034550744452106180119460005000c1822444280004036182602c8000207004500840e00858480c40c5c50100000c180d403800306040406e50645258110040444910f000c107a400500e0070b001d064050030034855030300d41403454503000901d500300c07400c0703508050800010081642442504440d0010490f101100c6500300449001400074910f004031003080345021010600180081d40b40b04201c0700140e540d000300c0c8400e880c681080410142c03040301590342e6050510074001083c0301011030b800f142d400001d0145001442d95040c48802d28051101c90810880e540050303801c00e041e9a00714102240042e1255078101895064cc4070360307005440100680254240351605403002503110314500c10684000386da80e41c100395594042c81c054103017240c12450121 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 873127832 1250 873126582 873126623
    0xf080d02010c0206011e030f0312110c0d05220308130905071215210606090e03070305030403180b0301060f0201090507052b08090913020d03110a0b0a020c0c03010207 73
    0x1041c1c01b515500c2e04401c050352583d805c100401c60440480201e04030700e0124900f65158403490b003d070110680c0e0185060071000200d80c0b5058120030300b90900401154900b00c0910582c1006010303448018020102900ca051021654011101000c4841580000441c080c495409002d0180c6c2440d260461144a20100c00d8081c1100c520320200e506480c1400054000580c0c68102c10141d1403651903041859609201003920615001217a2850400a00c0c03011900000212003030b0a130546850380c0c03641c071140780484031841210a40c600c205007a03440407855103444001141260a83e448501d00e91308144010781c241d6401e42009002500500400c1104d803d00e0704000f511001c80d80c948881c10590310801c81c0459191030f00580301060081081c6115003000c01d18150417000052484c0c64034606680001c1c01c2c1d525058000b810401c4004c001c10f8a00010000d0304192a0b200b401c80015150600e80074000750400c02d583c1c206031191490421407400c044c42103601d91074000a4100031560002c459 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 873129082 1250 873127832 873127859
    0x7033206090405031e13060201090f021c0b0406020d0c1107031502090303030a1d300d0203070c23061b07020a0801050103020f091303270f080d02010c020601 69
    0x1980d441c003080100119101040017000b0808800c0c140080d00c402d956003580c4d401701e00702d4005206582c50325218902041445400240255048958001c4111070101b20004081d000800404000c40c07001130204010441c0c0203058403400c896070801014041c0c110440d40c1002d42840f072552a003010000348046101c03144034040602c2c00d036070301514000b210300c0070a207180c1c011540018840d689101809100c5032076102410710788511002000a0094034034450380044001c800680050013041902284c0040c030400d4906900c0c180c0e6046449151002c0d02805081440d0300c100c407a004440349901c43e160044640b04000480702d001001c160381c2c0c07500301c1d945000c9181e032a100c24100500006006a85030080440a0f141c5100042129451441440311541070308807500d01c01c101c00d0040004010a04407001c2c1e10f9901817500404461010300303940d80400e2280340000c5c3c0350052120104212064440170341c22220381c01c040f1845800c40c0f45040b822900041d5070030740181c2185004211009001d00d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 873130332 1250 873129082 873129091
    0x20d0806061632060103020a08120f07060b0402120a060e011a07020d02150a1d06091c0c0b07020a08010b0120150117060a0c090911040e0703320609 65
    0x200051940c100150f4916115051002e5115950040d4014400c60410796142c0e03004188140080c100c11001420540c40c0f4080c07400070409450000c500b101c14080a604036043c4200c02410443d9500c00c030b5509804001002c58810003038900b4004006083d0300c0700c680e014100e400da505034054440c1c0d003900c194002c0c0e0046078180c0c1d110110400740c0c00541d50302800c940e18a201407419686d1400c040308003609480440402d0440700071400300c555800d485400c202c2d560075000700c4410b10f81501844041c4d040e07488141c8043d110548260703003c03413800c40351001807900900845040c10407039940c1e02071500743d44120038007600050300103c88044584280700d0b10b0740c241400c04282c6000d10098030590450035800da1002900c66203001d600740000c0c109110881d00320800c0c00090003000441c4c0e10180401c90a889150001a60340f0400300305001c1800558002d08107013507858800d424a900c0c01005010000c410742c0a21640e9401d01c1940d0031040541503452850340818161603950754100504c4000051 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 873131582 1250 873130332 873130373
    0x702040603060e031b0706080f042105090a0b0702060f07080f07080d0509150c0a020f0a06060501081f0b030a02071a01170706120e120307020d08060616 67
    0x30004070001e8000d016100041101d000210345811207446580790300000c60361841c0c6a900401c2c018001c0960086180351f002ea03540c415420b503502e83d880e0080f5807803080c00c55401c3d01c0604029084110354840002c03d890402140c2d10610b950700d5030150812480344180c020352000080000301d10301101c500180062500a000d0581080c242190105c1240c0c030a8204642c104000a8540b04c01f100714459240c00c400c45000070a09001c8087c501282d02002615041a20b10041030b60760311703d4820081e800c0c0201101d801d41d50300401c0d038606170000e070029006441c007240e00713040007c1c112120500c1560009a50754003500140e40740c0880c075240343c0d001909800d01c568003088001e01103100103420000340c0140040901403985088800190581e09a0030500141c22400782009402d034840c20540680000100000e445000a1341552418240740c01d4005c16050120400514030380100d400040103a068590210710364464040051a210ba855590b400c03500c2604000d000c1007204840343d50303030350861 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 873132832 1250 873131582 873131591
    0x9010e0303040f170a27030203060406050a06260f0109031b06060b04030807030809011829070206150f010909020d06030c08100f06050d020603130b010f17070614070204 74
    0x30103d020030758850028040410030005c120ba0101c03001340f9492411500c6c00c1600880a4150b0b80000c0e03e9440261015080740c0d154800300d4590b1810b60300110040007003400040c6041c0960300f81141c04014041501c00e18060280d00502598060154a80079070303156039915401840102507000b40003402c482503039500c1e91004081584145034004001460042c0e21040e221011403070024440c41000f840d02840c7d9041010f4141c40d4038104180c07200180d070100d8a41c1c5001d2022003c03030f1f0701054040468800018003800e01c010907401049441c0103c0483d80010341c2c0d04000400e02203000700b940c101a001440303691040290500e03e501800354100340e4034010480a42d6a2034040f01407200789c0000741d0b0380e00150300c080d8135030740b2511900c9a1840310050500216190500181500f010400c4c0a4058040000000d0a44c0443c0000540c22a8030175006207495840301c40c5c102d188a410701490f0300309240c0d0a1500c140e01c00028403c0300311151a51760408100310420f49072a6034104a0003240c002e0703101e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 873134082 1250 873132832 873132863
    0xa26040e040303060e071d10020f0a06050405070b09090a1a041103090d03060311150c0706080105012c040b1507060c0e1207050103050c0d090b0f09010e0303040f 71
    0x1000c410300d029074002c0da8041040c9090400011851202170020000e01114001c10721400c01542e0f20f124050400b02c3d8004580074050400f070f42440d1720501c8202c054005d40c2220810071400b58401402140160200e940c4e0980700c4440c0e41c107610500e25074580c441981400501d000c03a5541049004806100451b1960751194000c2010344070060080d4030703c42004010028120020440301c0501c045510b42404050f14686030080c0d03412005002c0e5010300c820204a043c070312441422180d0708035a20082f62a510782c0d801005000c5902801414002100c0e42032480e0061103042004600103d690100c3e410713041c000007040300400c2c800341d03216040402140011a0000d00d00d0107042c40600503a0301141154039034400800114042c81e02c5403260100b04048600c00f180042d52006036030007820005030940743c234031140015002c0d208d1030190300c1d03062868010400c82400161401040750801004490b00c5407100d0600760f544074012a880c80c3c0c801c0c000140401e1000a510034100d00030001030946405 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 873135332 1250 873134082 873134099
    0xa020d060305062404090809060903030708190207050d05190203190b09010608030c0d0305040f06050a0c171e0408070506130507080d0e040b030c0a0618080a2604 71
    0x104603020b81110f00b0b00c0c0d104c07800d14921400c0e84111280300701d03010400590a55694440c034000d01e061640200c0b40850000781c00e450800c1240c040580200d0f01030703110000c000e10840d03035181c9a1205001070080040014003402c00b1000700c02d400c0c4e481400307092803481e07986680340e00c2403e4003070599240c0316580e8080c5100010b44d0000101500640783d8030894030f003010b00942903c0c529441207085034003c10400700542070104464803991151f203000304d02511a030408425003500c040d0090002460b1200344003d400340303907006c00c0400340c003034940705400d0b0340074166110003450468a0001d03000e03085a19038030014170100090b50051060920b5401c1100c0ea0311807501d00201152078540d94101c1c900c0307210a216041103500002e1407214010941c508403040018401000361020707502494580c02846116a01408080341d0000003400545116503034440c000c0c98400034050f41c0030b0408045402040300a404541c205220381c002c40c1c01c0845c5a0300c18403035018401101d00030048804d050001054881 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 873136582 1250 873135332 873135343
    0x10f020a030213080c1503071e260f070c140303040b01050a0b030103080a1101090b1603241203050c0f06010f1401020706030c0302040302300d05030a020d060305 71
    0x120035640140c0301c5030140400003c188194200c940b0300d500808050f4040c0d5501e81d040c00389841d007a84015203984a0309420b981c03d950516806a20942000206541a40c011070001c0200d0310315000c0d84070310001d00107041d41c1e1130042e1003035885a818a0000ad01c4d060180c80c84030f4403d4401c0c0c60f0a110303480382048160540e00305460440b0780d5005007004001c00d02c0c0c001040000345c0b80c820f0301c10b0b10710351441ea02d07248948141040001800700c807030080d0114540a6026002c3c644e000641001075241c000391014030740e02601d90b20404030b4039040303d0240071f065164403030b00503c203001c10140352141001c4464808010162040301040400c10852454200c2800710849452035040208080d5040c904000c07005480c0d6003020800b80f24890300c9a41503a030002e0100202e038050b003030010700d100aa002c218082e01c03468001940040030a206050132010940c0303400881e00e00008d44a80101a03043e80541300c05030051400001103082c40881c00d002d502c2d1307004200ca045a1940020b446940307580f03540c10f22 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 873137832 1250 873136582 873136597
    0x907180501060807140a0804020a090f051803070b040807022209020108130b060d1b060e040b030d0c0311150703020a0e0a050a290c070812070206040e060102010f02 72
    0x6039100e1004020081d089220542c0120b0941840204012150498092801b811058804100040d4003040654407050300600c00f40030040d8043c04950040441c0d034003c1c2c20151990780c50444841150303003580c90b000c4141e450242d448500e00915440325110203000e50080d040c2a81d000b01c00703042403003041020b40030a000300d64826a010078601c0a83c0000350002100915429000100341b900b480014800c1d070b00198004412284144400c07072504202040b02c0312800c02080000c21400003080640e040303040d201d011441200c01b0b002c0069924241500e4042d01c1000d4004141641d6101000038003544111500d100404101c0e540c072024410010f85012007a076070313117020a6002898080c0958000300200c24a10103035401c0c1d00c02842d050100d02c0c40d400c64401d4020698550400a0710900d45001c6006041c1c0c09a80c0940c0300c518010215031140c002c1d2042c030809114a010000400010006840080c2c1e00203220500340351511502040c00840189602c0c115540c4d680c803e203031108140f0182082 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 873139082 1250 873137832 873137879
    0x40b13030c0b03060f09071814120106030308061c0510051e04080a180e0f1e06030703030e040213090605041d100923010c0305010605090d06050907 65
    0x403440c5050180c00555142c100060342c440810400c540d1740c840c404514000141550090b11541d11190102c0b0f845100c520700c8986452807e90010714807104007000003c1c0b007411038100614503a1103402908036201840002d010641c0380e40007400fa86041c2c0c4128008462607103040708807120550b0b0b0b46040248404051000680d0b41040c44840c1a5058406580c0c00c2c00107501240da050540f9004258090410403004022000d2201c4081d1140010b141c8001c0c5a1600c0407181402c0007070000800700f900310b071010441407660102e6001d003036511481034001d900c003601508555003161822904004000a03203908103800304000401c1c0b050120f000c0004200c0301500103030041c00c140801c42621400d5001e1110190940e02103031400e000402c4c90300d41004c0b401d10010300d24503507240060840d280b94541c00841c2c4d07419075010440071010341010441c00c8965030300700700f5031780c89860584460007400002a00000c0c00c00340d0500043d4103500450308400c4000c12101c0b215aa05292810740e0284003d0616 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 873140332 1250 873139082 873139117
    0x2205040c0f030507380904062309091b01080a090b07030f0f0903020c0d0203121209010c081e07031107030c02180105011209021c05030a140f0d0f02040b 67
    0x7121031040d00c030100d40096000c8003184191412440002040f02e0554a251400c0c00581e000e12943e1b2076000748c0050038255624074601407981d4081082e01e0a070741101e402900d0324000078404210120b10025500c00050748150041292401100c40003030007010680394640d1501158040b84c0311400d018415082076070f000c9074610101c0c8090b020b0f6030700f1001020341541021004000244c000c140705029210503640000180c0b840d0000a1416000c0a50302e0b401c00800100c60743c00240f440713105482003000e0b5000b4800524003006c102d5a80c9011a9242c2045160a400c1011746030aa450300380c01c582c180c940802c0c805426200300c1000d60010314100c012481c40c0a043d0114202100d00c1c2c00c41d50041c1d0440304c1d25615110004e0108902c2240007a911699400544119070b950b000041e1600c40106003605102540d02d012540d036880582d440780403603940040345c02d1170b12111045078000995262980c0c2009540409180a05907001e00c03840b8541c0c0034407000c0b0304100322401600f42034201500c000b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 873141582 1250 873140332 873140339
    0x318050609101104060503042105180d03050a051b011e050c09090423120d29121c05071401020f04051215090309030c2205040c0f030507 60
    0x615095210211841d42c2c1d04203003d25000c1030001013620121512402c2050340ca40d5145002c0c0800a0880401400800c0300d88060111640c0709000d0440700c00c07403e051045a90240e000c0040000c601c0b100100040e00801484140034800e0300541112003610301151820100308183c43d0a441c011528001d40c200140030740141c4203030383e00517503403c04410004075140070341c0b1901240724020002c0028011204414020a0f401260003800030719041280540e070810552106a001d41e9100b80f00030003d1604240402003840550000d80d00151429103140300c0186020051200c940170100040c2c959000b484641601a204245000c3c503011056980940d01c0030706103851102030800f203245d20800ea00c140700304410301d00c11400710340c2600c200721040d8442c144126030884c9010f03108407521010f41409814070000ea0b0002018050303104084040c1c3d40300d8a500d505005c488030f50f41c1c001c4210101d03000304034100d201c0d05500268200d4081e185603202c2d41e41707030003240c1084007456004440300d5103c10f4040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 873142832 1250 873141582 873141601
    0x1150308073314040c2d06200c24281106070e0402070c05100309050c1005040509060406051002070e100305152a040f091104060e0103180506 62
    0x504940c2008a90208900b065103e150300041540074400d808091120f04c6c4c03080d02c0342401005070b0810810500d5420070b485072030042007407983c58a288131400d40000d8410502c0c1c0003240d041c11085000e49032407542404000e400c1c5c00d4900b102d40b105a2440d0420070708051242c6a009070003085022098000440018000103220200e01403000c2d045802c64401c3c050040d50000d140c4648000c1100c02684803e00ba0400a0756400c041d400300741c1c080003070340f00700c0301c0715801d40c200003502070050b015140c000090000348114446200c407444002481008148800d01d000499203400100c0500000b400b0798403000420048500070f00b400d4050b0344000300802070300768600051548880009072112b445481c1d80e441e01e0b60b50703030f6032088280c510407104001503185020b5020b01c041980c1620040c03883c0381c09100c01900c103500c1800341c8003940c1d0030b5890114448295010300f10030b61400030301c071910785881c1c004111508001440200d040507210b141403075903607a0798004081402c4c001d4001d00401e00f402c0d03112 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 873144082 1250 873142832 873142841
    0x1503010e06041b030c0905250f140a120f09061103010305061308090d06090203060c0c07170c0603070e150a0f0804020a060c02030a0c1e0602011503080733 68
    0x403c80c00d4400400d0038000504000794003070031107559041c085a141c880601e145070703031014201807200482c00c940755000030355400203086103d140580c444610020f92000158114402e00502e900458105025070300308003034503405010140300e05d54001522804950740c4009481c0e419803040380032240800103100f0300c1014070125070040b0303032101c03d070113104140e5951050b580100c0340c05c40c0c42201c18002035001c0c007400d5007248403510360080942d0724502e0402c0f4120600d800c4610031841903c81c044011898030108400004039900040c014803004031107204000d6240c1c0010b01101c1003001c074007038103000c0303807034012103242e412414503843c940703510809034028140400502c0314000c0081c00d00a100140c0c40700340813902a560645000d00903c001c80c000300e031804085000080001580100001c4c03514809528a42800d49a1200795140c540d2980101d00780d80040b003981000148503c420400a44140000d03c103080c45090142d51542076203042a542600301c0040d4092804844a04440c1003007601c034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 873145332 1250 873144082 873144113
    0x210715050c151014032b111207170d02040f091b0c020909030c060408040518010f060f0c140c03060a090f1203021309061802040312081503010e0604 65
    0x40d02c02e2186000d41c0380e20032081d414455001200b507003000600040e20700b0b000c81d01010182941004d500d9030a2541d010203101c800c000200012401c070f2110a15a0b808030b45c0e0406010078840f0541041c1c507607160320b40324444020f2a0f2500c00810080004414514001340004155108900b0116403134944c5440a88800d0841000440c00b03140400c1d00d9035802c200c44260598060391056030036603920310070b14518450601c0004062080c4000c000801100c20000c10564100741c1b20301115056070400505410740a000301c44803505a140300740061441065000405151031401c85040c0c4000c0d00d40041c07804013043c000c070303d6400001c01480513040403c82d140d04034130484002c00c05441c2c00c4d191082d00d55071a020082070b9040205541c047c0f14401d4042e01c0c5140011b1504030b001c01d0f0340d009407000030a40381c402c5c642500c1c1c000e0340714400d048051003510b00b10b9401c246036030741191507524211074103c0c0040c426481541010043c00c03003500c00344611170107040d04e44010f04c101c0c1801d0900362845040ca41 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 873146582 1250 873145332 873145363
    0xa0f061e030501081009030912150605030606130911060403080a11060601050a05030a0b12160b0307080432100506060a0219031106070c0b06010e210715050c 69
    0x50040140c6480000c40b030030503441d080b00c00148044c4c4d47c074084030210950303806202002d154400200030311480d0b07450711480c4801c40078200130071992201416200c0d030085681c581d000c1c0304c4002c448801d40c4550841981e043c420160082c80140301400601250000d400c1600c02d02c01c0421880203941d0080548081030200000411280c0b41110000b0814072903880c60200b0444044041000348003e80c20005520400620312546d29030341714030407035a030401305101c980c04c0c1c4a17800c00000e42a20100c00c590043ca003546d640b409903500d40d12842440803d081200c8481e6104000c01002d801c1166044420400d151000e0844521403480303d10607030740081c1032103220f101d0030801710390590b03000a16071044c1c0180e903840308030481c42828140c03590074141207880040e028000c2004501c0381e0107107101d60303d80d1080c6415840c03511204d0044680c5007003400c3c110b40180104040e0b2429400d00d030340c03003094540350204444000d80c503481c0b005025002c20341c0c1c40004c9240850b04002416081c41510182409030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 873147832 1250 873146582 873146591
    0x30c0312040209250507080415020d230304080c15040803061215011512150501170f0f0901182111100b040e01020a08011a16110a0f061e03 61
    0xb50404184d032044c0f55600014054001407810410202c00150f80c01480070076a005052510741002a445144821400740000d038001e000c0509500d2191f808144030303d02100340c40c215580c982c0c1300e40095001c1025149984600d240009100c1400d00340b1620170362140034a55200c1c06c00c0c805004c400c0c1c052820075100b6030032041807682040032003800c10703045518000d031035002a80080000e8950071000395550300e00f6801c2850061071500940385a500b184c100781d07100c03031800c2c00360403140040d42415960b581000c0e44040116200c0000d038008540c115407000c0000480d640d40000c4070b100c80c0544035046a401514040d0032514500b0710700d0060a0009a0502c2d10041e03002c040c03103a480c2c1040405071600c00c0c0d5100034449403500c40b075004081080b0682c00071540c805c182080944801024411404208a007950310110400003000741e0704034228a440060f9540c2c0300c0d548203c00d0300d4400c40034640241c03d1440c0002c41c2c01c01110880f00610407030b00d9603d50f00c0031049080d401108a91032140030705040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 873149082 1250 873147832 873147871
    0xd061505180f180607090f05040b010219060213080f120c0703031d09180d03180609061103040b010602010c0503040b01031410020c1b0306010b0f0c030c0312040209 72
    0x84404041d030002c003075180d090250752459074007114000a1036000e03001d40b01d40c0c800c000c0f0b0680c2005c220002d44d030000d41565059a50b5204010170341d40c80e85c41250058101f1061180010304149000c000144690005402d1241904042500410f554000c0b50306501102811460010600c071001c0448410322406180c80703c07a102d040d55035542840010200240c0d0005000c080d002c441d0300583e412070040a010541c00c00c500418020190008072000382e000d05002c5200c507900a21404403051600a11525401d01684076100245030345002913803506d449040d446c141e00c2d01e03c2c1c01544501c7c41005180c80b1075040c090002d08540960007440248041001407001041002070054112a4800128500c0051551020341011080b602c003071403003400410301500704803003c1111100781c0c51070070520740d003184907400f01039440c0001e100315083c0c1a000c02072000302412440040401007070b0501105c1c40c21283c84581403866200518400c1c440c3e01c50300c140000c524100840b00d411500da00381e141480840c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 873150332 1250 873149082 873149119
    0x915011106371a03010507020d1e030b04090b04170903100203090c0306280207080d02070219080105390a0e03011d0601060206010f0915050d061505 65
    0x180342d00c1d80000303040b00e4401150b01e80304000440d0380741020600912a901d02005850401c0010000040c865420034000450452000136000402c20199035516200c20400900d00044201044c3c06410191a260401c9860301c0f00d000d86055144980706000e60b92070113003410b007031550440300400310030282001940c0700b42d036001909208001440200584e04d4845403000c031301e03000610389074035058024503082256140c0300e09240720f5220b1401e4050200429200c170f1074001c0b1310231b0800081c900030307007800f01508044841d80504000c40c0b010b0070f06501001418a03186188075150311440c8030ba9100c0042150354464103141e240701510740d80000c00494003011a026441c02c100d00e500d4035400b00461a20041c84c410100c051401d10054000c010701030b03003402e40380c4450400100300c03034151160740000035110b44009202c034103c8180540c2410841d0038a10a90042c01040e54141c01882110101042981d0b030348200000d030714400c900008110601c0c5140e15208143d50344100e101d9209842a60210302 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 873151582 1250 873150332 873150361
    0x15180b0a060e010f03020714010e0c15030109270c06020c0d050c1302040902040305060a0b060901021c0909061e0503210c2806060e130605070e0915011106 68
    0x260b09080c00c000d2980c0d01c40045000380a8000050f22000103031403c0e907507514040d80520082e000e407100303441c0100301103030901900a001503c60000c00301c08000401c1500300c039500c00140c0340c0100c000041100400303840e14040441c9898152813001d500710040003010f40401514015480942d1200181e84841d10703416214202c2400d2140111074400c0204101d01c0190704a401801c22514115251910ba05009030345c0e0004a031705004071403900400d2251032422000340c41545405a00412481c1112440340055044190106c014841c0051007c1030041c00b42c010710000e44412030080021600c54041c21500500390b60120340250428400c921000341c1213100c903038151803250805680c5e0b40304890602e140082e00c45841030550f40d061815100c4e03004908001880b0340c01b400c020700c001034996003070300255441074401c204440507401c9002c0002d106c54001c03d40c020300905140106940100100c0c040e02d004076640c01e5001e80303540c1560300a6802101c00c43ca00c1c0080c2d0000e04181c03412a21414110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 873152832 1250 873151582 873151607
    0x270303051b0a08130810090b18030702360108060a020f070b0103030e15030c090f030a020405010f080111091011030d020406231207050d15180b0a06 65
    0x1501400c1c5440d4144100700815454158014082595412441107841c108407040c06000c40c24060701d44101200f00550080043d0030350440021030301e5884420781c40c9041c4144a035040030700d020a0002402503500d403074035610120708030508a000c011402d14080001c2c4460881000ac12061400500c0b08803000504076612801c50307600140c0e0341d50186551020b80c00b859100400003000e04001000305540203101c40d00e9050251017110120b014420314a580303020031039114210321814442d1440e82d180581112144a03070140c10356081800640104050300d400b6080030016640f1a13100704007044007413050310365203204040180c0c20f04104000148900085e00420010040c0c003020401c6400002d2044846030350000400b15075903036981c00f02500840040c0e641510711480503048107900080581280e40e903078120b101400a40e42c452500361810340010304d0014a5076694240e0911074038007010048003400c0d4052091509080f03540005041d01c0100c04842e000b0640305000f0410b8580000c80041e06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 873154082 1250 873152832 873152857
    0x210a060f0e0d18090515040c02070e040f060609230601030b0306011a0c191104060302060d0e03040902040605180a08122d070309060807120b030a021027030305 70
    0x380f1a524503034070819000302025500c2e100038000e41c02201d400c400c0501000351001d124000c4091001d0742c40d5511441030580c040182000107000504141c0ca512016100e008006245c1c0e450b42000803c17240001c480c1846480c20000c00031005000790800e17903021000740b0301403104400d5075001c240c43e100306104502130014914108041024240c042e15040e41010301102d1900450340464204160000010344000c7c00d508044009414a40981c1080d203801400e031601c0c1520f0074400314018440f6660020a5010621011841140600007400100741640e1165160030180b003034004800d0309a4034480c840c26071441c040020b810b02007982890405d1244989440d003c1d49a070b00810414031308002d1040c2c2c100e48510030441c4d150380001c0d0078803900a50700c414226850b01800e503185441911200c000c150706d40850300c41c0c0b00e9541c12034034402384058240d0301d40e604a41d0228800300000364640c0003280c543c10104a04400704007210410546015001c00311600e941c5014040c2d118441407500b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 873155332 1250 873154082 873154097
    0xa0203130e090703020d0212161a1806030a09080406021608030705060115020c03150a150503100b062205100c0305070803071b0506070e0904120c02210a060f0e0d 71
    0x80d5038230340080501800450045d076074030006906070061030701d11a000d42943e03021144010f8284003545000d6801c071070ba0302c1d0110034110080d0810400356403c002c00c0c0c1200702d501c4d4005903002a9600001c4c00041c8042c0e0001c0a82a8855000e01c1000d4000c0e000389056600c1407107118049000005c1850445d408005485614241c0c024202e04045000e04045d80600c24040180700c1152190103861080300000e00c01c111010480e030002c96a095507118095160303002c001d484120030758a601031000c03494020305061130001d0003400c0182008000050303002402c81c007003040190b41408942c10710044141d01e81081d81e42c000d0303a000b8049010301c08000d003042c1004000541c143d806840310019169940c2203061512a031881e015964100450b240000101020302d24082c03410300c288406d0040303511061007083c0d22584c4d0011200d1188504c0240d0740304001140000e004982074480d40d400b40030074000380018108034180031003968010400448a5450300c801c1c01c50101300811059400b8a03103190120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 873156582 1250 873155332 873155359
    0x610030b0a0621022107020d0f12061d0402010e0312040b16050604150c0e130c0504050901063207020f01020705130203180a02060a030e01110a0203130e09070302 71
    0x207588401168084090a2000405d00f2203032050720000e25402500b0b202c941002c2e6a0f40307000303d844440881041011030706440c031a03000c041c00750039440c45100f039102001911565a88a440c0304161200703e80012000c510140001d65901a10040310040305a0040a4040f281214072800780301d03e1240d4018081c020549a4200c0c444081741a82641c000c0125402404e050a01c507071141d0996091160191918bd040040580a103440d1586004010720000c200400c0011120283c00030a0b4400f04000c400c00010426540307034210280078100d00d80d2800e41c1490000d4141441150080d110103481e105030806800740121001201d8210758141d80021180c800400142d14201054001c2c60b070200c8401119016502c01d580554400c400c4110f4040440e03c25600aa85881e40c5490280d000003042291a1140d8060740101110401c081c0001034a130300c4e0058070301040e800c2074a0450041e000000d00002d1010756005200241c40d501c3d00041c40d50a000c2003d0740d4440031448001c1c001e411154411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 873157832 1250 873156582 873156617
    0x12d1d070909021801080d050d14010b1218070902070602090a06050a0801141513030b012705010b0909040f0206030a090312050108100e01090204020301030807020a06020d0e010813020a0e0610030b0a06 88
    0x1252480308114800e049075840701013360785508424070003526041c3d144000b5024241c41e5018005030a15400a0040b250800403040080d51190368181e8003d502040181810384034a101c0c54000c0040f039072040e0300d4000000f40104680010391020a621208505d000f2080d541c1c284080c00050902489a9582501030100c5100c06407580c4007904030f003030310000003a4602d003469011081303200342d00754461410510011f41040b18004c2c024290401e100b03200400f00307824100d090540041c0a51812400c244840e80010704d154030031690001c81035201c0342c541f0105034103e40e0068901c1d03540c0f94144401e40c10700c403449560304603071602c2d21502070b101c10b503c0355501c000f075100000060700644299513070b40c1c59050400c020750207483e08178002c508a50300040c41600c00304944003010016555000104140c1c401183c03140f0303015180f00b4440050000401c0103a41e8208100c0044c003000485500740d180c420200004c5440b0020300c802850300700b400001035640c40100220030344035079082c0020a00b0004140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 873159082 1250 873157832 873157841
    0x501080603010f050906010602121e031803070510050f04020112050703060b13033806060c2a03120d15180509012d1d070909021801080d050d 62
    0x1400c904e2074142844001040410400c0c1a140d440d022503004010084030440c103813240c00700e00070080c000f01e60001e42c010360080c01075030448505604072541070006082181154006041282c95074001c54286180885074050f01d60301c5018003180803003a1502d5000a004582c5074040c060042d5030b1400001c10090107a4862005801c0031480d01ea29240d1200c501242c0d0610b600068a00308021031642641030466000300309500039104c00000012424803c0c0c0b401d01d1b00c06000254003280c02d0101103461a0208642350b148062082901c0d1141c1c0c4140825144409440c41c19000e030f08014111440c2014103022101d19103905040011000100880440c8240d016004007482042514100c035214806e5005140101c0210008000a030300c5502d80d407540b43c00c0c21860032280c180900e0111246c10403a40305104554060751400280c0324844a01420941d80e9000307410010b60703503104e580c15410200c2c0402040d91091640091550400d05603d681d0311441d00200208100042c800082140c107070031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 873160332 1250 873159082 873159101
    0x30a080903041707090501091104061b06020a1e05161104110307080405010b030c0f190509012c060306040f030507080301090b01030c02011e0b01030e10091506050109050108060301 79
    0x129401e54001c9a9241d503184c1c00c43e0700c1000c034407501b0070f00040b4041c207c510480200584a8280528107443c10f0f000b503541e407051503e0a2590702415070540041441030000784802c40e03043d0b0302c049a00c12601d440f016840320500c081003c0000c2403044802d00d4800031400c0e541d0740d4100400b5680304e010440001c1c040c00c1800c6500e41c21007404824800c400350488001d90240e48100024011030300300400b81076840c141c080006030300140c0d500041e1842c2c10029402c084c0c4c1c005900000303071020344800105460317401c207034080000c80b0040c80c600071441215513405807928184c10040300c1241480c500003981c902000e070020303084102d000d000008040c0640c045035581c6922800c5542c40e5a5030744a035070f0040907680b1350103012034180000d00300802d1040c4a90209611042c0d00780d502d0951040e000002800c56911060515685130207020b0302500812020784499a000d1002c1400070189c900b403281207281001d021300d03550030140140410703078003c100326042d02e0080c40c00f00d14a030f076010002405850074a2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 873161582 1250 873160332 873160349
    0x117010905070902160c03030e030601210308180717120306090c0f1606061703121503010e0106031506050a1208070825120c050601260f0c04060f0503030a08090304 72
    0x31b000040542041c110580344000b101030301d980d0b0ba0780f80d00e0b424800d148000c8021101c6584203400002038000c10b00c0700d0b040707a58140c44501c03118002d030800d0318201160b0007050245260743c010184200303040220f0f1443d628070890460450a04d1400708503016009051005891008906e8484074800303a000d688110000c15920031020b56241014030090030280907030200e420062185038103610300041183c0c1c040315180c0202c0c1259480040191004011502e650342c10354030f414100a04410900952000d14000ca50118641001e41c0146080f03525560005000c0c00d41030208100d4480800003805803260051181c83da21095490280356078468a0340052003681818200032030440507010b0705030300303a1040200e418402d90109080c0e600303080b005001003840d80000014003540e0000d0032104c1c15281d02c0e003103a84035003d050380014282000396182c0303540c0381d104002c050402d01d0301d4001c1c200101013a035402c0100b2824500800e4492203040322103070a000601f00851004441001294020880710 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 873162832 1250 873161582 873161603
    0x330a03021002010e1605030106120519030e0604090e060f01120602030c130803030603100b0d2006190e01050a0e01031e0c030603020405090114040b130614011701090507090216 77
    0x1c0da210340e1010800d011b1180a5845d0800c04696241580489480150400006d02e0707144032003c00c8000c0c0b0b48400c03900b2404c202c010021844c1d191200000740c8040d029800e8040f43c404d01d0320790128601b00d40100304014044030417004001000b5440000d000d403a80210000d41d59550f401a1b030281c80c8583c0102ea07040803105100001e040c0404030203140240011000d8415054490341a00c041d51507407421a540100b10f080c100740000c1b1801e045e590b08818002c1440030700890a0000b0b902038001c201c0c140c060f800303114000700829900000502d640b030b0003400c0c41801c0c1500402c0080034991a001c106042c0342d5154042c80300d55100d001c11701c3e014800c9000510a40e20b405600401508861008a00490500012801c064010b02402e00c044061f4451200d16558540321107050365005400142c00820b00d4034001c022403048d005150002506c40b039400142c0d40340820798404281d10300300300c7e4241e0f494049950000350001c0340e81c2c1d08a412802002d0784031000c070a800805125040310080040508 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 873164082 1250 873162832 873162853
    0x2106050306010311130c14090a03020315060114030f0c0a110708010606180302030a0b07140313030f0816050a030b0418020108010e0735330a03021002010e 68
    0xa521031310a00481903410942028581d850003007510b02030100007010400b076103e01c8139000100c00c003070b00c2c00300c20003004030100c160b0300e40202c2e08100c20054040c0b051102d980c108099541c200809410505054501a00c0c51070315545144914034041c0407921007000000c0c8d007504040c480c034451400c56840c002a280030a0343c840c01a40200340c075110714408504000c2060602c1841e520790302c021646c0107809441d03490040d40c1e488030b40d414024420024070202c50ba030f200c20084e585010b9440703440d805540311a040700504000d4542040d660300d04040003d0cc0041002a01540d140c03030800403514201148c44500c155000d40c083e1043c8411680c010740380441c00d5600c2c010100180034464001c1c0c850748601e03601ca95408026240c212010400309040344c42c0d0041c900c2446608100442c560008003402c04001951000f010000b80c81c192031408820035400000c0500341604d03840210319515440410620f80e0220b403007905648000b91181245038132042545000390071401e11400340741d0507150401c01e0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 873165332 1250 873164082 873164093
    0x31803030f0f25020106060e03071d0903040f0305070305150c0a0e15070606090b010c0b010e041b030b0613020c0c12010f020c0d02100c080f04020406050603072a0321060503060103 79
    0x1c07446101c0015410b00e500310701505000c1a0281a140010642c20192812f003a8210182c18080c150854a100c20400014456082507001c0041d601c5407020b0000b113841c508102d450080000074080140c00110244a11003200808440720407003a030608041c40030603400090b0100d1032004101c441c030940080c080007009250b074011402d4440300101009036405510046420081c0c00100801e481d10140050140641401c00d0711343c02031003020480c0f0380700c1001d03e41900d551419402164091051400c3c0030a9240684550081d41d00b651411030030110007641881d5186401c021490017112102c42000c00711500307400440c01e800300c2010546d038488000404a65590100c004072006001d042c411340c810650602a0000d0016240e84602854aa09850428000c005070040707034031550f1440c0004051311254007841c4642002d845440358043c41c2c001070420f00c1c480764501c5a240700080c00440c002500314180e4404024500110024040003058160040045800030b80d814030680000004012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 873166582 1250 873165332 873165341
    0x31c0f0605130c03050c030402061b0709021305030c090408041203120203072d02070e0705120403120609060b07060902060d0e06070306080d0e0118050406030602031803030f0f250201 80
    0x1503564080120b503868000560706c030f02054500a602070300c10000d03948000b80860b001c440c41d251a400351000c241e0741d0f40001c8103d82c03081140740c05c00c0182d010300304610701c1d061010300708504003513500500610307195886a1180c40342e80220800180704096200c1498803c904501d4144036404046503641410040a844004a440c1d40c0174102c3c10215466002e020610300002d2104950f00104040f40c01c0001c2e070301850340003d003000d0030000d007070001c54041d45000600c0d900890281d140c3d0751880200c1302c0400203546060300035001460908108115441d048402c481031242c1080c3d000802080301d02c00501e062142074804501d031403e1010701c0000310004241180502d01d00c3d2010020203645e445020340b181041680d14010074400c0750160300b46d5018019007400f2001080d00c550301f00340c0303400009040f25082e0308161100703030307000c03082010403017011b0018080075820400440c03c40c17901c102c5040707114000902c0e0070003038100c1d040440e1981001d420f42040c01e400405c52040c9107011500000e0003003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 873167832 1250 873166582 873166601
    0x1709211305041a150a0504090908090907200c01020307020f06041d060f0a060c110a1703130b1303030c05070b0307080604140c1e0904020a1808031c0f060513 69
    0x103c80d402260b00350030864a04545d021001c0c0d85920f070502e4900040e00c1c0091800810540f5842010084030440361f0368000c0c40307031198072180c54108281402d076241d4001d1302c580c21565903107540030380000640d40c5e070004103403000f490b030465081c1070303034401000031540b180200d07400700b80045440311fa000414488552840e12407202590108031102e401410806c010302c051150388082a00c40702d010004c00c50305101c1410303c0002070308103040c1c980c0c1c440c1700307010594010200031000d800c00310f4007800072041c8000787c03401008000c0042e07081c85001010003000341418840241848241c8501d102044818450103004000729210301e9124946040f018040000172511984220710b48406101281d00507600140a0340207802441d007016a051050701d64500c1804840203a050141704803000e1340e40324002001030030301c5c0350303580011070820748072810300d5101d1a0840032140c2c00601039540c5804c6034a036620400d0440520100b40400070025110080605030032158128084c1c03000c0d000844199040702404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 873169082 1250 873167832 873167839
    0x1605040e09030705301c0b031e160807031a1803040320040608060a020702010509040c0e3307030c06050103031119050c0f0316061709211305041a 64
    0xc0d6060f818020095201d0704520941b03001d1010369551000156030b111802401e030140407100107088910b81c0f0034454104456042e03075940403900910f041111510302d80000c08182d00289003150071aa030708080000808411411034900302c1c0010441c0d50640320042c41c40035100107696a898484c10140343e0030b280307099505200200c1d10386001e01c4d400c20348180001c4a504902405c119118524084044d41c8540c2c401d82c1004014400344c0d04d1a40e0380e1203203854203411074072600581801c84040c400d12075a41e5400441e829081c030403c50b0b05020958420001b40d0385c03065081d80d1031f201e03441c041e0703450509000302922091030100084105600810000102440c440c2115402c05a50305041e0b500d07180c0020081036604031100c1140d00b8242a0007182074804001c0c00d58001c0c1c1c0c00c6103c5c0c0c0034089032075800003001450018802000711075044150340c2080c1c40e500540f025500c00b0705201490826600380b8102c1280c000340c2c03030034280c0e02c4201e080d0140c00000c1c0280900c28904d00b01c40d41c40650301d8080b510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 873170332 1250 873169082 873169153
    0xc0922060f020414120601090c26090c0316061b060c08060103270602092710140337030509120d0813020f04020d0e061605040e09030705 60
    0x101494030304080d0314102c900ca4002c0103141c1c00e023000003010740795075502c0c1000c0c042281d0004030304084105e004000c0001d1882008528984190308515044500c0107490207a0414401c3e03134100d00e101240e403801c0e41c0380c0e402e040d0350b000d0034003d040449000c10701c005440300b460421103203103843d44410040d0181c542668140302501000f4203e40303014150b0780d00c1d00c465020340004040024900d40180c00c130f0110003011a4502d40240500c2500d8500034440c0405905100d000c22030b8010780c015000000d0098411100007400000380400c1e9a02301ca01503481480c40d5107228003060070306d48403c10801c02905a00440c0c01403240c84c014206800c1000410b1103042e048c0c400031a44e110000d03400700b0780702e400c0c0d881c2a8a501c840100c0203042207403039010790300280355085003080703502c590005140e500d500034000503500307000c00f04a0341400d1024180f02500401d5994110701958402c007580c00b40c4200d1007003144691104480700c1d15500c54507600074450b0044000300d07003000404000f8000701c2d8480054804 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 873171582 1250 873170332 873170369
    0xf0c0b0406090509310303110405060405060c0c1210050a020306030a02011224090e060c0f0c1e010203010608010b031003060f0902040f02030105120c0922060f0204 72
    0x164038026401001e00285000e80704220b1071070310000c40d81e0485400a42c0200c24000c1410040c40c2000742c003503c80060031012020400c140c0d0610401100c0c501c400003450400c0c1c03d10380018054401c0e4864548940004980e030108c200041c4444641180001c0103a4076a0140d0075010740c5440041d00c15046107458500040c80140310750007141e02c2000d0080107051480140d90044d20302c00d103484010301c0b003a0341d9030719813091200c010110354220305601c514804000e840c0c1041c8900b6501c18220366421600310b00c090203140300c25501902c0c03c079289609400d842d5801c0728100c40c60709081081c1e000b814200c0c07440400b00c8050660003581a510300d6625a41c03540e8842184100620091b616242088480320040002c50b036198004015244e0904020131000b0aa800040540e04000c4c03482d103085900100407c09454104040c001004150029040c1034212100140b0040380041240c2c0c0c0985480204012a182100200c1c544a50042040100100c0136800704000e40250150059900360f040700700 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 873172832 1250 873171582 873171599
    0x501090e03030103120c0c030b010f030204230622020d0b0103050601300f050403110c1005091e090c0705070f08100b030709140a05070c0804140d0804030f0c 69
    0xc0b07042e42c0c3c00c0b10703080850705c9106104407108020214203031001107149202100141c0c401210600901d403150f0300c0040782e41035004201c1191186015050a0000d403c6681c0c02451640d01c03050780310380115005100718071844079440d04c99180c00c0d11070f2500c42c8001030480120001d54402544c0c02802c0c3e8041000c1c0d55000010344101083c01d041d61030081610f921968400c070501c0b8440549001002c01040c07034030000034034800395501558114003040403562a0b40c4200308c100f040d86000c41c0215078070640311f582c840018140380720f0240201d0254040341e40211f5441100200c0d26144880a07049180504d4184460030300d83d000544100d6090150b00f500040b82c2d911201c0c0c0c5020780f50000040d0081816080d80540107120182140383c160003005000100c00d082c038400c0d14144200c0da8520055840c01d56400001c03198000c200000340040000c0303910101da813000c1528180e44003400b0900440d0003001c0000c01211302d4041c01458001c000401001f00001413031501c3d070745e03445000c1c242002c98840241 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 873174082 1250 873172832 873172837
    0x52d030115140a0e070c050609070b0f1b07031a061e0609040e0d0f031103040c030b100506030a0212090c0112090f02030303090d121505010f031805010501090e03 71
    0x8075480440722201844009403100d50051200b000a10b040e0f40e6a9650340e11401d4590300f250f0707050104031140b044000f8804180310441c0d21104400203494a40d080240608107402400502d07180303220007048609064610722940d4403424002e500f00d072710607603482c81c202000315140300200190400c04000308183d030a08200114400a5a40d85400005e95590500031a5001030000550094440020200303220f014050300007540020f1350340c1004d02c40300a0003d001e80e0101038508208010410801c4040f4010804c01421361350300101010071500c4480c89a10420080e80010f5445040041404900000355006060100f04d801c0301407800d946100c0200d466465680015010880051103856581d00c1c0d079010840c5c2c20301c20220149154001d8010906e541c008840100f05a4081043e081c4500d410000b03501e03045646480612052210550000c0321444d40c2c81401e06220000484041b524040d4002034040710314065800301003642d07424100d000e00020300c02c10410603d000341800c1c00100202c01c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 873175332 1250 873174082 873174101
    0x9010614071a280605030c01120f0c0201020c151308031008070807050a0803090f04110c0f06010602010e1f0209060f2701030e03041211061914071e020307052d0301 72
    0x2030447c1400d1070700150365000044003051120ba540d00360707900e60b42000380f040c241400c890f9800107896070b11400c8018541890500b00c40030f2060003804004111206999100303006a00c041940d41702c2e00d420806001300145030b00440c0c05405410008580c4042c001000c2003110300c11944641100e90780e032a500d480b0700c100100c094000d005061030070400d04090700002d0703d00504030b283d186041c00f00508141030110704601940ca40e00700000400c14030350309015003610103444101a0291603030700000b080011080102c0c60403102d8000c070702c0004c0b0340c1d1210f007a110f401824115044c1d6402110740780c1002c0708404403413000680c60550f1070302d600754800c0c442c4100c501e070300100440c41d203410145000319401841804031104401b0f00c82c0c0c003e0380e0300c4010243c01d0210884503840000b20300c2c40c202070080003920340c072204814014012400400d10100d8803031500444503d4003401d4080070300209040c0b0944c1e801060f04401c0715880c80000c02010710001c1c4c90150400000e41842c5400800c140c240c44c1e0020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 873176582 1250 873175332 873175339
    0x12010b0a06080f1510140d0f09060c080f130302150103080304062405010804020402090a0b03090d0f05040303210e0d0e0406030b070503180a0f060b09010614071a280605 74
    0x4071644401e4042e45100d1043d001600d46c880c10000c0e5199450140ca09010250700390a03107417807045042007003600452a840085082c01480f80c54502c1e0840080e510003080310030b00540182d210f0003414020b100c41010080301020b000071640c0c490410107200c1d48251002c5605a00e0b006841d4000d80d0030003102201490322408001d401440c00004458201010300141c0c0d100d642000740345070307a40c5c0c1c41517900000c1c140492002d40301d10305001d82604014030b1a510350240403494000554541d440070850b41544d42c075081054080900c2d540340c01d68900b00d1103610200320700d0301400c080344540008d86030340f88140341e80d503521000c500d041c2400b050f14124800205000d02d2500410100c030700400185501064a1600040001c105107c06180074074145080c0c1c0c40d43c280501041c24000d150040301514401aaa0542035501d09500240121500104c160408901003592420001c4030f0f0f0085100600c4660300c4203d908104480e40003142d030030f100303041038299507d0b0880e4620083d805840304462008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 873177832 1250 873176582 873176599
    0x100c1a01030507051e040504060b1003090b061003020705011a030c06040506040603021605150411011803081b0307110108071805210f060a0b03160512010b0a06080f15 73
    0x4402c1c00700c071541c00c20b810705c40601d96403661251500c07544602445503010721008500f4410701d8007403184100501051004041c1400101000b04504d03003581900304070156500c004054901008600900810320002c3c119420a14207000e00c55011341c00307071141340f000c5094400202c03056007008641c2c402d503c645d03a00540305120422400303002e07a002d0955803154043c40131408005685460904880c031500d110304002103030600080c0511482c51070340442003824042c1c0840384461540e180600540b000400c00c2c44002078400390740e810b003000c041c81c0c147e03c10700f00c030f40300e810600c0d011080c400814600790024143c175001590103403003100640914102d14411212803800c050a000c42c011003103d032083c1010401618070014101048020802403a10010384810305006003030381c042d9011921000c0c0300c3c0d40514620032940002c0c20380c0d401190340459416071500710010920b03006d00040c2d0312a83c0c3c022951070000984607001012a4400c0314020313110300280e500c2043c2e0318540d621100c180d0f50882c020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 873179082 1250 873177832 873177839
    0x30603033504080a030f0e0a11031905010e0c010806012304050a0b030a240e040c030b090303150402070b070c02120601091a040b01022a100c1a01030507 67
    0x40c0d604451000c0e14201050761841400a031101058165403c44000100180d1110360319414031501906101c0200c09014154640711100d540b9002900e01501e00304960b03045581c196070401c07841c0c2c0301c20000318015284015604049000380606c250a650a01505400304031561140301d40c07611856050b1100d00f0300c54010340002425402140782c420a0240400c40814940d413274428510042c86940c000d15603a251000b1b07088103450065050071449005101c0094a0750b203a03251038800c0e200c01e40402318440e510360074a900038104591000d0000303a40c900034048801c2c0003100441c0b00341e100d034624440241c00c0e182440124480c0d000b01030000ca015030701041d441442030792403c1000d0700040c68000071020b40c0e41e0307060500c071082e400100030581c0c441c3d01041106840414500340c0d02c0841e400c0041104010010703440b80030464081c0f425504111b0030b40b20381d1a900100d40504403014092040c44045550050b1980d0300b05842a90700c010007881c0300e88200803410545068903401409014203518 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 873180332 1250 873179082 873179117
    0x10e07200a060203190b0a150e03071a03010815090307080c0f06090c0f0315150307120804030b180c01050901050417031315020607050d0e062503060303 67
    0xd0200142180c040e4804000c0411514009140500c030000301080300d0400a00f084001c503404034601501446102c64200f01c0c03085a902602c1c04004541000810303042d100002030304106841d04420b1012892a000c184e031a4500000355050310052000c0f2003110500c0c251840c151300d0102c0d442e0407d40d10801241d0000b0385100050058014580d040390480480f520501c0d05180c411140710a06511441c0d40ca02c4d41e00d401c0242e01074251080d0050440c4a00003180303d00000802410038040c2900040c0140d070507101000f0310002400c0070240301e1a81b20880c03400e0300c1180e100c0d11003a1035810150010400080c4000316540d840044440202810b0f00e10314010f40705600030001c0035042c4003040c800003421a603203203030f1100500417001c051a80d0b0000f60142c0e11601031340b60480e040da030480c04440d41c1c0e006d0f000525250000300300e080c6a07132901c80c8609480302510301d40e044030f10a03004623420b00200555440350302e0226091043d250034810a411b00c128100c82541c44060005100303111400c48420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 873181582 1250 873180332 873180377
    0x30f14090d020a090e0a1217010509090f060a06140a050d0f0809040218030d08130b06150d090201030c110c04390207050a030804030605071211040806010e07 69
    0x51001c3c0c4034900480da00d8a40b081110100000070403035411142001c01080b240307424501400c001070402000312032030940c0e2140035810500506002e0a000b074007042045008105d140030700707410601114584d00c0c11400c40400f900091146849002c0b4449001d4a14600a140501501c901514084141e0502d454004200203000340036540e603030081004001680300c4c0e0000301400f8209400c00c11081c809031051614020300d0754010300030840c1c0031007402005045010b60010031a0032005000c05900c4e0300c4000790040d103c051868bd0043c100042c4041c0c4a05140c20a07501207000762400c00954541c1c24050750a500c501610f104103800810042640d1715060b48040c516248103000e510782c0710000fa01d00b03d520b003259010760800c0d20b481880b4905103941000800c010b000709071035490070b0a255503281340460055020060040d51207000245c002c611a11a90414041040c2e0071301181651500d800203952041c014280280641000416000303121200103016444543d1050100d012180107101d010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 873182832 1250 873181582 873181609
    0xe070c0c1202130518100b03190c0e09010b0907030506030d0201141f08031206090c1c11130b130603050f01050d0f0515010e1303020a020f01032007030f1409 69
    0x15003a2a000c481317103108125071905880803210000310800b030441094900102c0b01e800e0824170f00340d400d690000500410343d4000303e5040041c030203c60b8958100550260080d80240350f00b0841e00002c00030075030750540149004010036420369081400d9075100302e003604c05103d41d2140c1e00b13103004041841d41461813032a202da650241144026661190106411039100415460504c03d030302052040d41c4c03401c0c080c1ca0b13810050400e4914641f01403c4040b0b0307489412403004641a0b9611440c50174038032164000c0350b80301c0700040c407103050050302c424146106800880100c80300080c07030040417a078540288107150180460b034203810110b07885d24040000700300a107441151500170154814000070010000e003183d020807000762006960601c80304001c1c40d2001088800d245210b900c1e200046500402c04e5034035260147d07408506186040010780207848254014090703101d40da044a2400c02c4204003900b655032180e1b03158020030b800f44a08036200450b0704695078102c802000f02c00b246140062091010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 873184082 1250 873182832 873182851
    0xd08070812273913020c0f0f10180f0b0103110a03020108040206090303070c0f03122a020a0513022106060d091707080703020c041518060e070c0c12021305 68
    0x6a03903480d008200e00701030800c0d84140340c1c0e0300070030700c4d0144d1b20050100091414100303001b025110340c419030007a954217440300b00008143d42c1703020000c0090100285c140c4d10a821100c0d40d001c541c540d00e0000c0410f00b091009503000c80d40041c0d01d8031685000315060040f290143c0d0384810360b855640070482141d00101c60998148420440c001c0090400d1440d8001082c003281006421403450405c400e00340050b001c00f00800c07100c6914485111010910401101c21070986440c807008544085019801d49030407195022030441a61542e0500b0f17a0005e00c125a00003141940c05104c0750741500d034504003914440d90050040c040061034010303d5001a0015008854a030b4903040704180640c015403002070203540c00403001a505051540410014490110a44040103215610955903c0a12143c0520031080d0480580d28201034076135007150303003d00f0001100c41c842d401c140f40054640c40074800f0444001c03810174800500c0348403404074990801e401510f41c5414a0726090b05500a08004191910 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 873185332 1250 873184082 873184183
    0xd0e0c04090c0f08030307052a0102030901061d0403021e1504030c06140f06060c1614090108070b0703050c160e15040b0d0807081227 59
    0x520356500d00505800034000c0c500540c0e52801d1140781c02c0c0c0060745812402203a8400c0080c0203490750b009040303600070280c4900070510b00d2024107d400206c448081c0b412115030021090000c07412040d80a44101c03555400d014a04080745024240040341c216400350158105200c8046100c0709409040c00040302401901d540b940c009610b10480c1209031415400144001c5101d4200803082c40b030382201c2118031000c03a050f13181100c0840d1218200900302c9005120105190032102d4041202a01c007640003950300007003544031118511030510780907155100300100800007601040c0030a804003035444161015250100f00e03102651030b0782c080c0b041c04032540302e5500e0411001c0c80d0000c40f54060800c03005042c501e030926140710205c02c092481e41c248039601d846a201441c0e0344030464800255405441c05440d04d60604020b01d10f40200a8107241c1c2c00c0f1240c0070007600600341500021110031229450b030304c0c2e03000103c41d01d507100c0ca5440140ca03020041040720310741c00a000b081f0b6030807410354101540c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 873186582 1250 873185332 873185353
    0x507090501110c1c0803160e010c020a1401050f1605070e040b0604150504020315090a0b031c030e0601031b060e0117060f1503010503210307140d0c0c0204140105060d0e 74
    0x45d00d130750003180e04078115900d00c0351044000c0e50051400b070164200340b9000515001e04d8002402c00f20f0301d07100307074500e108036500c1e10b80c6964080c40c2540c06140b90b03070b10741c103880e80312042c075601010300503440444a602800a0224841030f0030b403c0e00380a6500003103130403118cc0d00c51003440010404000c8100040c000010001090f40d940d00080d4030032041d6440101c80301400c981070203c21480039103121030300d604004914803161000245a00300c1c00c081c3d204507204041c0f145c02a030051841c68402412030280000103c20b02411000b0801c99682a900c5880c60030340c0c6641c22900074234406c1525001810b21480d4070342100e43c0058903a0040402061032100008900c00144481a869000b81e90144040010401032900b40f21108420020f03012030f4803040700010030704a443c44010509818041125521100004984262160500d40303000c1001455440c040180827508100b004900c29400c2c162602178108048004a0403158003401c050302700704011a00101614a01001041c548111281d92 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 873187832 1250 873186582 873186593
    0x406050f0f03151504140103021c090f0c140d060e0c09010f1a031513060519180c0f030c170c040312050a050304060522060507090501110c1c 62
    0x218040c1c0c00d51200120aa00b445040c0920141c241300800c80c44001488108a0180302c26940020302c40b092900503941d820814500b13003007d116200c410201c1303245c80b60200400c1050311800c0b40080c01841c52907019580c601c0140f00c2003d807044140d802076840004400002ca807500100a84004082514034401c0c01d58041b90040c4426448420480203124041164064101da0030380400ea450480910707502d000c10201e1a110a03150b5040e004020030004031070140c58079031181e0f01030f01000349007100b460305100c40745850a002c0e00030500c19500300e01e244003c039031480c85548522245503e410640802c40c0c40140c004150300c40410b4280050001485003441140355100d1040914030130301031301d903800d5003020070201c150707940325105000c01004600d40c540c0e005426207611171b42c4094081200e6903500700c517181c00e07100e5054046416440710140001c10000f43c21544c4a0b050654500c80803907503c10044801061101c44079141d6080804444501c1c2000290030700004040d040480000341300d0743d0383c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 873189082 1250 873187832 873187837
    0x100c060e120a030c050708092101020f030709080f060106110111040b04031a0c09190302030607020a03022e05060a0321020106054213080609030c030406050f0f 70
    0x1078281400001654802d880d81601c07a918205510703107040b50800406585544c42c0d48070700b2000394420285049400005000108183c81200d91003009540766000300c481051f82e80c0040e04da01b00402d0203448046003900c0002001c8040346043c04c024000c51b440c1c1001529168030070300142299540350035080001000c0c003001040104081d07160b0707644d518590f04090070080604800001ca5000810030300440b01080002da403200f0380d0880740d0b030b054200a1541d2005001030740e88000d4060092804011103244c000c80c04034003d038060b80a03a24a5052016440001006014140346281030b08108240c00500ca0740702540c41302000d0600c04550391240c5602d06035030701140b499107605200984000e1184e50a00640004210540c0c0070b03031084600306005850820701c0304002c20a810300d4012140d03d001070744051802d001c0090303110750344c034518a840500d480f009401189420301c15400482c3c41580000116401c4150a4001d1804c0504100040f0b8059011105070300044000703024481d24509003800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 873190332 1250 873189082 873189103
    0x30c080910020a0b010819140304120305180f01050a03090c0b120a0c0306182c0f060c0c0c310e0105070906050906090604080a030207180605100c060e 66
    0x70072883d1191300d07001c06081c105030030010b09600080d1780081040b61004001c05101e40c1f20288503070900c00c020040386903000300c0e4016100c0c4043e0b664800f041c15044002090400da0700c4000d0bc3c04c910101c0240803400e0250040180040d204001410480d88a548407205051240080340303001ea60381c100000d19500704035131580c0b1404c508421b2124540a40c403940103403000d1400c1c1442140d1402e107082c203680105c5c0c280100019114000d1090a020350400c144510b43e41c0e030740c103007110700e8030038046551207000c620048441e00c526004139002ca0814020b48000103800001020484114014030949011542580c001503803941c0b03041c200f00c1110041054980c0e540c0c000080c0c01840010110f095440141035902480040c0c002400401d510a08482d01c0c038030b0a0302c901790788030b0f0200d022407480d1040303502c580d015009815500d010503034045440d0003100c52542d404064003d462820804590383c512603203601c190480070503000300d80505030868456000e110b000404d40c00c4c25075458202425000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 873191582 1250 873190332 873190337
    0xb090f13050f090a02011e020c030d201209060714010504060f06050d0201090b0f0d060f0501020127260a090e0106020106030b010e090c130203041a04030804030c080910 74
    0x1020020400b800841480c0e2048030b510050101c00780c26000030308000d035105580008000a01d04420015008100070808514054100e0f01030b00d440341001000840c4030240096820402c012aa51021000803030b0300c02400701c000c4161070030350700c00c0410140c3c0d88405002c0312801c2c1c1c1e4001c04005078400b8401c1c0307842a4084e26010aa000800e505d0300102c409640100788601948007040001d42d0340072130548140c0e404501501c3d55809803002d803075280d000342920b0700c48250400d1804941d24aa12000c04200c4400780c0003400106501e094604e030004402c080481130a0076a01943e011800403d035889511015500000c00035142d046204d80302d0b841425803102090300c141081103807a45a034100750040500d80b0080083c40c0c156a60300b07a201c103043c41440351425024001c00c9101c00c00784000021520b0040181000c1c0040414020194104036402c0c0c070704441210109212000c0304500c0d5220303940c181c0d5010400c4e615594292403181850b802501ca06505120018540c0c40d024102c208054594 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 873192832 1250 873191582 873191591
    0x30403060603020a05040e03030a09030e0a060207090c0e031902010903141c0201052406040509090706080a060b0702091302060307090503010e0106120816050615030d09060206010b090f13 82
    0x1401132001941480e40010b00803464940c45440d50b142c04001c1d00d80102141e4004241c035807882c20f089400c0410407800e640d01040c5240c0003d842e6800256080132611200d40500602c4c0010000351540c0d00401038141c2c00da003242642d40c0d40101195600c00700309205060400c0b009460344c5030711108000c1d06510052550102004140b070409280c404d041c20002031001340040c0c6000c0020054400746020401940280103076851b202e07540743d82c16503016000c043d0046c90f0524011080d60342d15142031094401080207003003c110251000d003d03142c10380b41101d080601e0b00c46103074240944482c000b010308881c03200c01c018400041c0e03101401540166420b41d11202e442d400d0004060071541146d07a661161382c9054ac080240b4011078100805a50308001400e803503100c1d0003585140d2a5812600420f540118402c008940211070329101c24a003090701164100240c140c002e65002c0090300404025a006a00400c58010030030b00502c09040c1c040d194070300d0405c40e480410b1140300400303860040161034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 873194082 1250 873192832 873192839
    0x312010b070b0a15050613030f030e0a0b0a0206150102010f0e07050102071d06121c21020304031d0a0e0901020a3207022b0b0109021c0f0e0304030606 66
    0x408030b01c90b4100c00104410080e08640d8105005038040780e104c1c2c02e00443e00815550390845040c58400700031500800100344c208e4061400822562040301d04610030314a0310404903076030001109a400211843d0010405511040c40c0044502208140c440c110b40d00d0b00800c2ea4007200502540b030400c03441c54000c02d040d5040c00c0c0060705000554100142c1c800841d1540810703940c1d05481c00d50445030503266178052006000c0103c0c2000d4003254581c08e01003650f81c419184550280c5552050080d910b00100d1020b54240514180d00c8140d0300a000185403030418518003070b144035211442d20005000e6580a5610130381084503c00480c1d00c00d13020b17540498080310740d94004c0c000401c0408a0482e10f00c211000c5001c2e100c20103003a132a90800c10f1004a01d401c01c42d12101100d01801e559050610200c0103407460840096100610440d0188a1440006005d0070f00e03000380e88542d003043c84080781281c1c13070300c04610050000d01c0a5440403610380030500c403840700510040010398040c1c2c20128804c1e04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 873195332 1250 873194082 873194093
    0xa030905010e03070b07020a0e0f010513020a081512070b0301050301050601020c130c18091a060a0e010c0206070c170c0603060a0608040c2111100c02120312010b07 72
    0x48a40c406418008880c2e0311031420741d00459003a0555902c0120b550b2561000c2c000310340384e07590903002100710020440501011005c0c00544504a40040365404c885840041c6864140e0044002d210702180a40c404202001c2d00c0121101302404090b1000801c4400324075000d203031251507030081c2075003003002005100b10304081c040c0540c0300c8028001000e03c0081100030a140c54040d001840c3c8031551614041d0b4072038403440d001d00c4100350a1000c102065142c0300181e004120415808a001102c00311004680c1000d01c00c1d80d41c5d845440d2255452000810700541742c4000300701c82203a000c4800c120200c0040c00480445010f40246480b0392031058500c3c903038610f0821000b1495104d443c00f40200019599800b003040d041e84c12603e0f01181036112460400056480b5401141c04c403649144440311401140d04401411802140c0c0007900042420511048600c0c42000d100003c0c0d40c60900c0016003001210205003014182c100c82c40c00342852488880201c00382c018034004100090071505102 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 873196582 1250 873195332 873195347
    0x151124010512030304080a0c020604060f030c030603171e0c0d09060207080d0f020c0a2309060f060c030c072c06010f18031a0a110403050d0c02150c0a03 67
    0x1c1c0c80b88807400384032114403035680c04000d03c01055000006400044036104103900b08049031301070b100b180c865407200c034050320030104100942d0010703140000b040841c41c0f00780109000c40341c0100d607035512100c02000d4040598454000d06101c00106010f0300454102d08008106040d4880080c0500d50302c6410020f0001c00705501c10401c640c072000c01400101401f04140034840d00c9410710140d125050b800690500c21061a00f5500400408001410720b42504c003240d48010000a51000c54842c00100003010206940d070a0300041c0d6403100e21400d0500d500103202240400c02113a041034080941e4904c1d00d052600300b0780290102003144801d04120040a00c1803042c3c0a0400d8400d2403c01c4c0002c1c1003110507207505007002034100e035940902083c0313004003011b103402c0205c0790000d0340b10a412045119081d6103c0c49541d10f000f200c6840400b010041e90152030303024010301008052a00101c460418801b020b980c002948601d0b003591800050013851007c000307030054810752106050161a00c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 873197832 1250 873196582 873196589
    0x40303080c0a02030a0f0903020301050414120c0721020a0b0d0c03020a0e090601050f1210050a0506040314070f0810050f06030309012a030216140a15112401 69
    0x190810b00031401d00d150080245c44910320145408840d40060040131a8101516807019406500c0c020612041c080d800c5004c0740c030f2182c0d040c200d90642c4000c01610000c1d1181021074106074100b03d50501034110ba03a10b4002c0b506011440c074030500c2c5116000a1070b00f40e21544441c44510380050025006105c1e40201c00031446c00303046c00c60411048400141100280c000524450008080028607503800350081d20540002100c0041c0c560300412a1804101800ea640741d48039801c0000007d41c5141010100781601c10151400c1e0510b884c0d0344e00c0100b02110b50340e00c40581c3c0194207011980e0359441c01c504004180f200020301c580c3c07410608040841d9000340c10101000407540407c0401e44000048a018250a2030302c040c1c4d4155107006140c24040b4407892902d000e442c10320b03480c20305074000b442000d107003601000c00e20042e41e20b000000c181c0c10075034007298220200941c10410240c0f101e4482c105940c0604040c05440d030551542810310919a1022031580140d1340200c5141c0c64020313015024 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 873199082 1250 873197832 873197851
    0x5030d12050703180204090f0c080a0c08061b0d090219140d11010c0204150b040305100501120602210f01080115051f023f0a0c02092a04030308 63
    0x2100c3c101314500480b00440c0001902880e240c020705c5040062145070a0a0150005000f40e01c450701c44007001c1d01c03000e0018090345c42d2011f464000c10340034000f04059000e50013003a035030304503100401019240c5d07800c8134200545007a600c1c0810400b40e201c252006503581950301000c401e82d410075a03c80c008a40c29040340b130044d03c9100c171800010708001041c125940090905404080f103d10020f005840340c0d100340004804c041c000024400b4018000e0000d60f8842d400b0f0314010481225a1003c0752024414501c1e140c1c105002e00e00450740035401440c0200e5424174141c4961501c8000b0f00036143c00f0781d007182600004000401260341d0a2151804051a003040c41c81d010345000001042d82034800350066123520003085001e1814020010340c004010301c58002403684e80e0085051290620320503407400b03004071080030b019205003a030303080301d8501034030740c27100d4030076281c20f8080c0450070600808012944240f4401c480c6550a00001c0c000d0580c074044c0b8041d41c0e01c0c214a40108865070241490380c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 873200332 1250 873199082 873199091
    0x30b0402191d18300f030f0606120c1309020a02070302150c0309301f060803121503070909170403031409030c06190201060e090a03030b040605030d12050703 69
    0x32000001c20b60105004040500d14074030700130603c82d4540b0800d11280d1031440000000d031604440c441c1400385120b4001c102c4100c240c3c3c1c2d2000b05011151054144c156001140680010715081640001d00103a8000102d81c0b0200f50b03d03141000d0484e80501075000141c1c0c0400001c000b103180101030195001c80286585090207840c2c4250307940c03401003c0003684140c0180380501e24400c0104151230000441e20074402c40b03800f00c0c3d200103072a0010046010380c019051012070110706010b01030301d022990108000d501c0c040181100b880c42ca00040c1030180074400500000810f80c1e010041c10014100c900741c0040c0c2c0d04150b01d82040c20100d11000e621031010188010800f007504a0003d1200e07401c2000810f035103c1e050b40c0000d0038101000074a42d031200c0c003c5410034072801c065242c00c20030003e81c3c0003004035680300c40309001c0b010703800c60310714205511841142001a03c03030740016550840150000c80c0250b1100c0c0000d003010741c1c0480040c00120743c2001400d00034440e0203002d4006c00141000c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 873201438 1106 873200332 873200371
    0x20f0307150e04091205030612060c1c0e19060612060b03010b010905030c010e15041e0905070504150c02181501030b030601030b0402191d 61
    0x400640c80c0d03006401c2c14105841034184407a0042c440c200110307000403049400d580000c010703581003114418650000002000b40300c2c02162121041521201e984203801c40094012a542c0c1180b800c0403076803400f40902041900c89010b07400c1856410f807210781000406000c160748110701e4004088a074000348907d83d0701054401e0801c83c0240484851040116a64482405402e0781a00039202c10071807580500e1050f540300101505012200e11120701c0e880303d90f00650b00c1014000010710250520141d03024982000d4039000c03c08201c50308002900521501545c021810b1390f48007040009040b40c01940411012503000300448031030110800c2d0319441c608291381307102e061011081030110540c003070b000e181400d1001900034079050b0305c1d54940380b00c00340b806007040e80c01000c8100b42000d418a911040000f81001c100c9980c0352118020210710341c5040200060040e110151060 = true := by decide +kernel

theorem cover : BRFrame.Cov 873021582 873201438 := by
  have h0 := BRFrame.cov_init 873021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 873021582 ≤ n) (h2 : n < 873201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
