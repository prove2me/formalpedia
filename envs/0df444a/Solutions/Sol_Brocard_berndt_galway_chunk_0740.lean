-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0740
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:31:17.502567+00:00
-- url     : https://prove2.me/submissions/1684a46e-83cf-40cd-9f5f-9b90e6a25ad7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 132913669 ≤ n < 133093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 132914919 1250 132913669 132913679
    0xc0b010305070609061e0e03101104090b01080f010312092c010f0317030415020a02061603020c07050f0a0f0806090c060702030d11030409020f03041103070b0706020a050d0204 77
    0x924141a1022138607070050f400e1325a40c003910300707605101d0110b044403241c2601440c4103200f0300c1c0c1c80b480c00c036025044403403482c0f0125404040e40c10015008a0b082004681045010154012104500c0d02030030440303164100b004040c0d03d01141400050b0944280000404e40d02d846140d0200c001d1081061115950003101c481c603030540320001801ea45084070400216007000c0b400c6200c02202c1c5e100041daa404a403004414083c4d0300010419241c101820340d0800d40340c10240010060120154080c1000d4600000e0318020700f03810120600401d4414000b04016280004030700040d1001201e0380300000c4cc00d07000040305005d80e0b0b0044070040c1000703500003842c5040029658016207000b0705840240001505020140c003403400060350640c043d00c13020035070074001c00e0091404441c000a8038078054481500c0026a07200c0c5103564031103840002088103000440c90b8980e00c0c42c90840c09000071a01d45404144075004107280500425400074807401000e000300100c0386c1207121034000355100c85e910 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 132916169 1250 132914919 132914923
    0x270d030603020f09160305070203090d120206010b0c070603020d0f060f0f0905070e10031b050406140c2a0409030806040e010606121104050d06090203120f0a08070c0b010305 76
    0x3a12049000c0d0b880c0c1c20011000d0302d44100d100d0310541200c81c1000c800107658030228040e080240880d010750100700700305180c2ea00c607803500300106401110301c01c003401c01402c4001c0c074050f0140c0c40140740510a0020004078800440c580007160194a809a01c4992842a10004108120100180307a103050740004019584c2107600c01114140c0046003807950307035205000159902140d0303e800003421540e801d0800d01d80103c250921080618002a07007681661080310404c41201700d20000c10341c04a03080000070380c403c0c0c460580c4e6145d40c803c241496180205540c0d2107840c01c554560802543c4400312415120202d48181c1160080050048151508000e4454030081d91003500560030440c0000841c0c405010312012035040755501003008090444103c010300c4e201c1e60405d401c20041000003041e50b296044c07500140e001c0c101c0021040140d1041510306001c00070a03022100c420b10407580e0140026058528002c801e00780f00c41c5654403040100c40d0260061001000f04161200110900c280 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 132917419 1250 132916169 132916181
    0x904050a03120203060f010309080d0608100606021504030c14030f040303030c020d0801060806010207031a10120812060d0f030c0516210816050a02040b010f08270d03 73
    0x1c0d140c68444140c2e079080081070f4482200d0f52608894402002c070740c294032aa1252451601924855080880c3d0b00c4524040c5c4d640c540c00207229510850840161880c903104540003040c41d4001013000c80810300c10308800880080001d018046030300c1005050061004c003059220700d0080c00c0d6503031844101103882d08e40d001804294002071a00242d803008a000080100e070002c42501d800c2016840c0120803203110f80014072aa046003c1c803140000080c40e6200e01e0083d07024400c020301020b00c1c0030425682e01e1000c0f40d025915000a540754080410524011a070045907140109001d517601d000c041000b42100800080070610744100b10380c14103501001c043e40c030f00e2044c001c2c4d50313540301d080403d10b4455003103025000c12048958010a440304182d0010758501d8032404902d03003000c000d049004c502ca141500c040d81c8642014400c0c80840c0b4003480740000c98182400c0c80400c6e000000402800400000d10b06110060000c00300204031002121340d650b45041c0508491a400c07070544010040d01c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 132918669 1250 132917419 132917423
    0x16120206040606170c0f011e0207080d031b05090102010216080304020a050f0a050607050f0a03091706010f05010e03070506160b060604120b04140601030c060215060303040510020c0904050a 83
    0x481d20f034010400e00078010401d400e0101507002056843c0700b030300400003120010182c1b28140122000501c50b401d24500300700d82010b00c0c41d00604070700703032518648500300f402c03d00c0e05000705403402d0078441461103242a560f03024106460300030380358484000140c0c028850b040400b45d10f2030760204074000b08822407005510030b40c03081d26403484450303942e801e110400c07103141c0410340d100050200c180110300786880070b020030a000d202182d5000d007400d810641030040c1910140d001a881c41c1041c007142d440302007800c030300c2190a001040150714003090240006c603507008140c10031102440502466804000ba41d0140a0052189030740b03039010baa20b948066102c1c0400c9541c0940900050658030f003940c1501c08580d145681c403484108155a15505606d000b00100c2d0803000903007400021a20030010381d4041d61244004580288c10302801030b20b003031100c05c41640a0100c810070010749440100030b90741217820640340c10095445850b0142d04005c49122500c0c0c026003400c04200030b2020022303c00b49894 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 132919919 1250 132918669 132918671
    0xb1503150a2009041e020a0503040b0f070f0503060112050703050106020f03031014060c101a03060709060305280f0c17040f080714070e07020a17161202060406 70
    0x5111841c0c80c11038226169104040004140801e00f07031030805420152407109040700910b1942030344400c007412600300382c501c400020008810001000098560300390000d2030031030a042140380108006204992005030181084008000b250b0140d01030ba0100e000000c130b0140910540c80c141000034014070303003485043c00510a00d0000c0c84021004001c40380203201e60f2023540e4071642450b2110074400e60350700a26400160822100403100c0f818091000c40c20481d4101181c0407650210301c007801c51481a109100f6040725090000300e94015140e0f1048601a090110f880d554801680b20300014802083c12001420346c00540c00d641c06a004102d0400101c804000300d0306404811540000c0481c181000c0d44592004540841c680c89000000d003442207030828a0140c00c2d0f80e0b26100d0320a070310829a06036002a80a000040c81150410350240842c401030580306c400c3d4542c0c003841034120414946503a000125002c0307001210110706902d5401005d016207031484004001d5585400322408c1d5003803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 132921169 1250 132919919 132919931
    0xb0a0e030105070e011b0c1509030218010608010b2a01060f08030318010203060607080d110406181502030912010b030307051e01180b0603010f05010801090c0503010c08040b1503150a 80
    0x140010854052186d83c111000f1110030381031483d400e519520300400001032048012000005076189880301102e009065001e800c254548034028100c00011303001000100030500401c102c0f12040403055404024181e190595035403010300d040c0c018102e58000f40340d541668800801c00e030400000540c00759441c44080c2202e4140308400380d08034042030f584a60300810400240c001f1513501e002400200d00034074800549075007449051f02c46030380140e200b27401182c0c4003d03203071640c0303921400054020305001c035005481d10744025000f03490313200344103415124204220711460109000d6005c486280c070b001d401c403035542d821824841d40e20302601d0011100c50304026000380301c0d41418000c9440f16074180000040c2d5005d1075441c250480d60080c103c9805641e40c004540000503240151402000c2c000300025030034500303042425404403a03820a078020380c103240b4184600d9601403002540700d03400480100703040d15540c00801411701040f10701c0c0d515100300c6101c0030004008071541d40c02068019010050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 132922419 1250 132921169 132921197
    0x10c1415060d0c060804170412120e01020709110d0c0327050a02040c030b0411090310060e0a0b0607060219080112051f0b03010204090b0103140903040b0a0e030105070e01 75
    0x100002c03004010150600300070100a000c0c05500758036003092058806c91004c0817600d4451905400035403041080c00410901c400501981034000103080242d840d00041081700346c00043d503a40024401e80504599a900c0d000710b0001c0b56041c1c0300780e001143c20074041803200c084010060718220f81c201104080c0034403182d0720640300802006180e58464080c004800041d000c00006001e081c0c01c490926407640d044006a6803507103d003440100c0c81c10b5655072500400414103180c80b076000c0b4000b0400b03103003840c140007510014001c0c0307038408605540441c40050b0000816039034020303040010011400498503207002034495240c5d00d5064001d41d1003c02503039039814101c00e490051000600a40c114000c110501030f41026032411103d100c1c0c2e0302180240c481c202081c02ca900680c0000303e42d0b592424169225a4175000d0f11103a6003800000c0d40f403030304100d248a501c0344118454040d032400000380d64801980107041000d41060020020400d6240580010f41041c90441e1180e0000d1814203038445 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 132923669 1250 132922419 132922429
    0x80c090603390d12141602120c130902130c0c060b0102120c0f010e07060210020703120e01020307020c100504050108100803040f080c0a06050a030b010c141506 70
    0x1c0049041030155409a0705000d516141d054604403580b50000555051011a100d41c1c0740940607604c02e45125204162141008218080c006010100880200703c4c580c04041c00040450100d40c04807078000703078400741c0c0b60710b6841d080041c000c0c3d940200781180c000b181e9003c158001071040d402a2202c40c00a09804400400ca405034262640403810174a2104081403255000f03c03440b18040c0100d0710500e1549094409580118000300e045e50301062042a03000800c1c094104070503607600c0240341007410320358080c1d100c41d2070041c48014241c4c0401c414003814410720035100b019504540411070900d002485034040c0d401100d0060161041c0f2010b080182400d1045c81c8015540e03a540038107003820710004442201c000b4000459500038110003051006060004200800c00405d00c00c3c2018981080c140c10001c2030b0076600e2090700a420b04020054000003100c1e5080081d1500140c103041c803200682e032038003c0300c802529140091110b4204081c001032055038a5102c6030480555a41d448100b00d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 132924919 1250 132923669 132923683
    0x106090509060411010e060d05060a0f090e150f0c0c010b0a030c03030806030601140d0213020f040e10060819091502041e05030c1203070f060912030e0d0f0203070804080c090603 78
    0x107410100400c0000f030f0230401a40583d40081c0000c004450301d44e911b4080c0c414907050b54200c000e182c1d80c2d458170403900c04000c00440305100040c00c0850007600d88441946040c420003031103003682110020307154401d40e40a50001d0120800148040d030540c4d20b07401c2070034490595001c02c401003003005001c0345080c60000703150750480c4c0340c4640f04060080264148402a00c02884c12030708100c24102e51910840680064a90000311402160f1150328169508004040141c40321011a0701e0342400e10465621914155118589102e000c840d156030030000d400400c200380c0080c013900c49058502110390440c2d0010300448056214100c10769103080f61072280c0c241e1503c100d6505038440b6200d008542030000c41d00c6403107902c00f0305881c10310449451356a407558070a00100c03242c1c2c1d0755092110411581c0e618104e401d400c580b408212100700b10980e69a00c10a820f0400c0c00e0180e41e042c0c4d098803070310070401c40d0031695121480c6a151aa02e03c2503681d07507420701810510a1400b01c002620505000884c1d07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 132926169 1250 132924919 132924947
    0x8030f1f05120708370b0c0304020a180f0c0207050607060c0504030803090601062a02150903100506090105010309020a031712090d18080d11010609050906041101 71
    0x6660440d207080c1c10807920040e60580400e007409503500c0090680820701446200e04e40c0c0c80040711082d544400202c0604481c1540c402102d01452484004030343e912101c10790040c0103401040d0742e40c0b01c03400054049245039114000c440443da032880002c400580014114140104050142600006040c0e803202054002c0c0c6400070b00030f209540c00300c0d0054218190381290350a09a19154032901c860140d60f1084581e8000b90f0300c0280104052948103812104c00e08a008215800d40c50b1050340603040d0720b06c600043d1190005610020111000104a880038180201190520a82c3c800c0e8100075203401c507089441a100c82c0000078a03940039026070284580e000f0091380b003d6081d0b66a8180d120019011811200c100340000c14a4180e00b03280c01d40908a8540180020850b003c070003032107a80b0040d11030360b010300c0340941000752050000703240369080c40d0350501071413403070440703a00c00c0c010800c5621070001503003007030240a90103a000c204640141d0203484e008a100d10f40341c0040d54400c076400c101c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 132927419 1250 132926169 132926221
    0x1207110c0d080408030a180b03100b03060406210201032003040b09030403060c0324030c05061b0105040b07111c030b040f0e030d06090902090103080f1608030f 70
    0xd5a4800d00e042150006000d20400880c1d003050346469001e459070708511510000304041803641515014001e040500402480c800d01c0d00e1450308888052590005200e100440c3c9804804581d9a9445030040b20151140025a180d43d0310105140d0044030760b16401a8007003850701003280400c00c40900744400b8111a41340040c6940c81f03c0d540d1003004040103003105103900040c4400300c00204c1078020105804601e940100d14606400e40480c4008003604840341078681d940010000102e08050b01c9040381c108841c0180c4031080c7c0c0000c03004095600400030055441c12080104000111444500643c502e07541c00c0d013080c0301518865585d08544212018a02000d100300b050b0310700c41e40141d010108013500102d49040e00070b01c202c2c01d8800d8980c00d464180c202040550340c8240354400c0d40300916010310240016074254000c01c440030303410b01010300000310006120103031440600485842c0d503801d00041487c20304d1814000341c290020750350301c400e040304040403800340e5800160441051000500c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 132928669 1250 132927419 132927433
    0x121902011b0f051e010218090a021b070312050307081b0d0207030207060e011407021c05060103080415051206241c180b1302030a08030c120711 63
    0x199508501c14822404081c2101c050900196192201c0c20540744150014102e4a2482d221082e10100714540000f943e071051019000101c030342d0742e80d02d007004804e48d07603d0a01d80700c080a08000e8400c090b80e101214202c00314402551100249807821030340100c65038640701c2142c1104440a2006807080d10021700c3c1503011070390940d2008144131a44084c0600c4071f185c0a0303e01881416a0800541940035030400881049807507041007580c14010000d18201136542c2440c990450700c0c0c0252003002e8040e0a80c0c2c0380300742070100a0401d01030b4080e00082190010340e580d2030f11091640c414011822240503330051003010701d002c1d10a54039584481001300300c6541c3c540382407015809a07104c1e03c0b0044140108101c003c2d4802034010f040700001a990380200d0f10111580c04140c03901c41d150310400c01c4e04a800710300450027111031141c10042c4c1e011120f00c04500d0303000003407811507401c5001c0c3c0301400000600c065203418100900075498403040c204015521283d06543c0341d6103100d10003c103600290 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 132929919 1250 132928669 132928673
    0x5030609031c020a020a170c06061c030e030c030a050304180216060905102f0a0e101404090b0111070e060105090102010207060e030301030b010b04060f0c05010b0411091219 76
    0x10f0090b01102d155441201d2055081e91100414030a010185000f84030000031562035000043c0f103060351210f4150740036441c0d000880c0c00760700d04403001c0074040c007040244442c2019550703080c80a5075500100a040b1481c003c02400c0c86912544144244007030400c0d82d445d00040b03006540243c4140b0451000c00001c3d100003a11588094011100300300c405001d02200389140b000203114030a44c190599082442c5031215031000805070104441448010030280715041009901610703480c01c544043c3c2e810241e20301c40900c1590540000c1c0c3c1180079000021501003841070359540700002c001c00c26a183c0301540844540b06031200300e14000c201c0c1080100300000c4440d4003450042c91802410b1000500e0281142c0340e00301102d2170b0210303907589074000000400900001c0440305003d021a1410710345068075141c03010341540d081c03031030410501c118208000240b02003948041d849410150050280c8995070091000319484040c209108260248505144400000c0e80b5011050501c0070194044941c0e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 132931169 1250 132929919 132929921
    0x607020304061209140d021e030d0c09080307120e1f030b0609091006030b120616031b0809010f0905030f091f1e08070c060518031305030609031c 64
    0x44403c00840b038460000300f00040f00311031800c0c041c3c111035000d04029080310400909140c8070003400e00c0700c40c7d00d15000c10400341000c400c417145c60710341070000900401410003e641c00d07107440c0d10420b450700001c074042c01800b07038141108104d6100380d641c1090310109802000301c00c02e11008071894000f08850ba100101c1d02075804480d06010081100d0300304001c0500088803c0011615221180c040c0349040040c00c0d058009d8900c0c0c07602c00c4410100e03c640b05464281d4544008100c0a81034900c2c114007007050780241d00c01c0310b402c460081a0600c80180000180c280740703064030494002e6203000230a481e4507000744900d00016500c9000b6616000e20200b031a802504080d504a503c00907450381140300144402a29030600309545400d00e0186602c0075081903a9540101c0304140196103040103640da80c485c80800c0380c03e034010340014aa4462088050000680c140b440705203100004940c04c2c0d101c1c514003c04101e4030120110f5003191790b5406000c2c2c40340a61003004140c0b6a414048461880c03503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 132932419 1250 132931169 132931187
    0x1e03080a0b0a080a03050903060f012417070807080a0203010b1c0204120c0609080c0603010626092b2001020d02040b092106070c05070b0408071502060702030406 71
    0x2000301902c0d100c54031010064100702950b18100c0c0810f5001840d100a42801c1c4001c5902c68910050189079600d8800481da03144010600e140c910303280101d60940711070040001c40c080c00c0c200c1c4210100d40c81e003200c02402096080d14040b01040510f400103d4015090080300e040c1d034000d426480c2800404490b00f0b000c0c3e9407000c10340c80c0607602884040742180007400b14044103401001c030200324601d0050003a0102c40b031034100b62606c1e00400002c06184d00e4100449044805600c1d054046010401ca840d0682c550f49008a50716000303d81440030b81c2e00300040880a108040c54481040103a21091144030050b45170040c011400408034106010420085007800e049003000161401c050401d800040303038811b42007907510010100d610142c500702000d06680412401c1d0b6290305644d030100e0b29590340d000040c141820000007040701f6003001020303c0440000e15030341b44026180c030b4680142a48442041c00327003041c84030820440070105440050004e0050b010390b00518a000d0a2410480ea040f030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 132933669 1250 132932419 132932441
    0x81902010f1b02030114010f150f0e0103180308150d1106090d05060a090614070c15020f0c03070b090a1110201501080109021c060605060a020a1e03080a 67
    0x351101900000d03131028002c0320504070511070842c91a60401c050568408041c0d08081e43c42801c044000703007882d4008007429601440303030034000c0310f003e0380c440124040c0c801c0040d0900c003042d0011301101015003000ea07030b41c0079070700e80f5a0700d00441c11808244111482610780103802d1080344003a004c15420003000812795018080c00007050b500258507182d00c0d02c4400d85200114595030405001445050710842281c0b58900400101506001c100200208910b42000c1d00b030f1015401440c002031600c0d030440b0031100e00310522644840c04041465143c0d0080d000a903010206500000c124a0000c100c00341441d902c4248482540d8002c07081c40150b0361030313101500a00026032003900c03810220107904150700e6540c00050242d5040c42100282801041e40600000e030305203002440140c0d500030ba13040d0041003000072040f5440c00c80c14000c01400c0d29610058100000069070301c0410b80c0450b038050f19600401c10035805409542c0d20700f05c0202d04003006070008048001040c148502604403207030b081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 132934919 1250 132933669 132933707
    0x20703030b1908061b2a010c0302030a14091b01020c04110a0906080702031804140717070c0201050304061802190f08070609031203140c0301081902010f 67
    0x405000128040090440344002c100b2540202007103155010040d1561100b240c21042d002543e1003255a2101e00a00003041600511030028042c0d107000030360b03031302210403505000380b00c16200c0b000f0103402035000ba600400d0207420710812400455000400c540900501001842d901c0002d0320146159050301000904501036040350802d0340e5202d0262441d00d121000b5500e68480c1c80d20f2001d0000425a40501e040c40b030f10504000c107698002c4180c440d001c95240801c00209034a00c0014024500c40d01c80b01c07051001c1d00300340132896074042030310480c0c62629a4489826154a2030943c3c000d5480000240068006c000040018000350004c08030460383c1030699240440170b0b0700040fa026160307104410054120b01d0104019588200705400604940019050342420480020030000a9000142001c4480808103d013548241d216403040218040d21881c01e0400c01546886c581c000e1141e482c007031059520758035011a80d40246000d40750305071528080003030484d00a41d44521076041c0c1c40105 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 132936169 1250 132934919 132934931
    0x20f0a09092a051309020d3b030708030a1b08010b07030e030f06010b130509041a07170108030703090603050f010510030b03010e0601030b1003120509040207051507030c05071502070303 81
    0x61603200b00e0002810500c50050380742c2e44c09031b42007011070781800c00c03414000a42584003044c07210f908c1c043c0d000300e0b88103483c1c0311841c2c800c44000301d1451290b04001004c4810010800c0b008201c142e000301014030700000081d44011540000710f8001ea000e0083c16003814040010800081c018049540051406003c1d901e03103c3c070000b10345041490036400801001000100c400240146000100c050070381100c01c88024280398650340b003010aa0402c0c100401c901401142c8114020240118503040e0901c004410f5038540d6206130300d9030400304080700860070070800882d5081c041d01036588101821501035555a2030242009206040d203540340007030664038403590256132000c8c041c0d60b45400d081001403070300f540343d858031881f13000d001000d003100110126030a00000e840000d15283c5d80c0341c10300d48940c450a105c00020001d1281145c02400c5100c4d0008202004400904003403207860303a41c808218200080c9001e42c1c080c032540e28002e00c3c096495032000f50180c02d607409070000f90300907d000505 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 132937419 1250 132936169 132936187
    0x1107030c1e050d03030b0f0319020402160209040c0504060e1501030906020d0216021002150711070e13060b01080115080910050103051c030b010503060f0d0501020f0a09092a05 77
    0x20403e0100c001c0c0c000070b4a5000039200d5042c14418040082d1041c3c0c01415483c44e40081070010388072502c4002d10880d00020404041800e424480304501c2e0010000c216900306480d01c000c110030107102d032074003490800c4000600031303100200c841e10461a0104014420340c41c1401100107140814040b100c9a034203000c03c00d1585400e101501c03d44c00b001301c01d0104e40525004100c800050b6441500c1150f11403081c42c051000c840000c141c010505040c462040d01d40200030500300491504045a409442c20400410318060b000c21344001c2c0c0200000c10509015000441d10b1074030901815028104042c0e25004e1756114540c082d0b8001d145030b0035614044542c18406040c1c070380031f80c01503556501040c040c01e10403030921842744030840d2508040083c1c40203140060031500004041510400c100c104003021a2030b80300805680d540d00ca4001c56a0708500009400941c028241d14000600c1013000800c50004070b1041e5170701c10140f0300c103801e040b21118031200e042c82d0104110104100d0103100c4205 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 132938669 1250 132937419 132937429
    0x40e040f0302073602090a031401060e1303030b040507091a04080a08040f0b040509040809220e010b01020f0601031103070305070e0610210b030a150504031107030c1e05 74
    0x62400d10241d5143c400d075070803014a5120760844099506020710406c450501d90b611080000110380e8004001070f40c850030b110304240103100700d87c0301540000204040108030300c0d03050301c2d04082078800c0d01c0400c00402000d050000704c6804591103804100021400d00c440d801d2207800c3d40030384008400c0c0a00d000d49501032141401120b0303000711001d41d0080b4062104180c00000700d80680040214141401c3c9400300081100e100038001618131840003074070a2007030b103d06020044041c0c910300040a4284150b00324070061100b0741012205500c0c0a4510602e5171010031030440b009007070002042d5030703402e43e01c410045840745120241c1c18820b040e0008000f0b84e003400703070380020300312900e100649150040501c1182c02d280c0a181c0c2c1082649440c80000d480c0000ca00c44580324002d03000182150240040b0b454441a10009441c440d00803400240c0d2075080d410807031066100f582d9400600f04241c46031a07607040280030050440d400d404040c0540154001b85451801c1d0014001080d65600c41c00301d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 132939919 1250 132938669 132938699
    0x10810170d02061f06030902060c03030708090607210b0a1206020301081005010602150403120603060504020a080102160b06180f06030d05090a0501030513020a060203120705040e040f030207 83
    0x98481d0807007200340c9001901440702a038006101d040a00040744148100f1280c0502c600444085c540d650511000303640312541501c030880d0704c0c0000c6079030307900740300101420382c610848079445144181c500162103240308181205004015070031107070700a10b1507804a0060994a1811038010211a00000e0864044196440c0a078010200185c1d25410300703055600300b42d170303142243e1003031428500100405d65002550f441520742c126000580c40c0c485240859000c80080046048241028008030a001265002502403803003111011041552400900d00b0303809030f45c00e603480d001001c11400300482c4142d10400d41c8800b00900060712000c00d4256140c8034075060700c1d08408030f00c1c9c0c0000c01955003030800c0120708000c071a003407250403c0031020000e48990001e0264a0405d42c03a14045000e00602d03206900e50395074010080c02c000c54450800a51b08d4114000e001418061900482c0c034041c003030310480c1e084e5140300303003030008076521364403445481611010110114400c001d80082d0b0300c15032804070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 132941169 1250 132939919 132939959
    0x204060b1909030c03020603040c051e011b031403040f02030a030c0618120e03010209060a1106010906030503030601050702060c1b1002030c070608041505090a0606080102070c05010810 81
    0x54548603640c158a84010307001d4840c0d014014440010700100300c001515104030ba030b048903125642d65451401408107000e56005a80041c0070400100001001e5400750810a81c04ea036414000c0001c002c040203040801400a008100c01c880c102c881618504003c541c4076000b100320840440c230603400b1900c0c2070030950060b0000380d0401c447c4400c00c003c50040c0400b40020b00010b0640b04079546409200040900c240800d001040d28601c203240c0702034040d1114402d0003030006c7d803500d030b0000003d485403c1e00a411311103801408000301c4c4c260310307070303c030b02019030b074006000b94116650000150790540c03060409981c080018490020000030801207141403030070b92031944040e60441c4d014000c2240d4280d00300801e41d001402402c14000000401c0011a190703071608200c50b407590f003828880c00500d807401c1c0307590302c1c100402c00a421400298a14101d803040404004050303070340b07801d18201d0144000042135500300c3c070001c004541c0304240f250780001c91001d510500d683e441c100d41006031011060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 132942419 1250 132941169 132941189
    0x1110a0b07050310090c020606060310080a0503030a0b060c0a0809151908090102091c03090e07090503060c090d0f080f0705010605040e010212040f0516080604110103020a050708070f020406 83
    0x410050070204e0b15024001d020a080602c07440e46a800080e466050090005004c0e0b0b03004000140c0011034127480c20002c000e80020382d614180f5600784582c03681e004480d070014541c1056419266818124100d500200d010405801081910750702d102c4298000c8a070b407503101c1810794250200d032030360b42d0080111800e0081c004410b4500e0307130005030440600801c142c081c3d0b4814000340c40503840302250300001c4048030080601d0145107240588107944e09070410080c080703034582000519a0800e07888030603141e0403000c031040e41c0d84049418840744116121203411914505105000659807202003040f10702c0340d4272840c1040c05189402e981c1e908410002c0d101c40e07444107400c00c010f003040e110b03041210703801000075403801200f24a2103001103800303080142041c5018114805200c1c040c030010101000c400c0c2004032440d07030b68a41c0d594801d42510103030380452941d1114081c0d0340c007074400c8038001817883c3c803250b040420740d4540554a4104980a80c1ca10411800c003500507522441a44090040031807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 132943669 1250 132942419 132942421
    0xc031506091a0f010e180603030412200306010b0703051b010c03060911030412140906041508070804120e12010207030203070308100e010b0a050909070206010501030f05011401110a0b070503 83
    0x1c03c0245040d04104014184041c180401c411900c030701001711a40b45044813441d036140c5074030300804c0c0b551069030301180d00200b00c170703c0603c1048041d410003142e0b070641e8030f028556560480201038640000707100d503e0545008000400c002402080074025424145810323005200c0101034003802c0d128030725a4074000941d40c450074070007501a4800d00240340c3e20306684c0d17801d6141603510b41c007084a200c0000414420b00311403103843d049600049441c0c0e050094011074807580d54034000410314111400d2940032503100400950754a105168592003a40c01071b00e1503c140c008128103075100d2000342e81c041d4100e8034800e40107401800900040420504c41c2e070045a481c034042c20020241d19000e44608106142c40c9800c1103001e040d0c2501505403091030a0160361031420110941d11445030b003c40540010b480380401c6030340d68020030402e049400c2030300c0074072150030914406001c607202401085241482d172300202d0b201e0352045142d603041303108110440300401560303160b5580e00c5408880366000280000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 132944919 1250 132943669 132943721
    0xf0209010f090f110f03040c032f011d040b0609040207120e03070812030c0c010f0c030b0f1f02031b01020706060f0e0a09050c0a031a070207030c03150609 68
    0x21044400c14424110208403040d002c80d002d4484e485142000000401d001c400318003440310f82e402413001103920125202e0102c100c0007403104107001440c04200f99050801928650f5401751035520304d299540040e10648075141001c10005050f03044003190001c0040c45803d000f13842d1480103000c02405103549041e03119500c9001045412035404050183d04483e00c2009040e00002d00f9050f42216196055240d580b2190010128000c892044809609040900c100c518090f4010080c0c0f076034907507003401002c20442c1031226200c100ba615580058010007021011010041c1401c4040d10a2054a152080c3d0b40103940c00d04a00134800d0310265400034603182004407520940006108071414092403915013140042288401001040c409865146440c20400140b10524001300c0c020100b0003216120700b400e08a40000c40d04030f135000c00d4240045030206000142c05801c0303a5100300050942030940c4c0d0360051661010032081d241035101c2c2c0c00031503c41c0c018010154024012034541c2c0c0084515 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 132946169 1250 132944919 132944921
    0x203010b06040e0a021c1406010206010b0c0a0b0405010905151006090303080109020912010c0906110712120504091d010f050c03060d08070f06061d060603040f0f0209010f09 76
    0x429024412042004100000341007070924a40c0211441344c01070301d800284d0802d070b040300c000c02501e109003813500291080c030403c1d0882481c02100c00380d003141c40a03a201c008000aa110700c0041c400d45920041c0c140c00040c15595050381c0c4140b0910011482d080d040c1c0d100752500480c01e8002240310011070400074028030b94200326008044514054007054a5524050310540040c0038181e0702c90b03000190a001c1d07490303160440d000360903d000200009001201d008002120a026500000b40c1c0856000000c070070005950007943e2030f00c80ca0301030b040c0e82a51081550540b4607600e00500030240000100031796203124410f034121558001d01810085910b005003154105208140b2852400341804512503103c810349600000685981c1101c40e40ea061030a607a000d003507002060769051103031000c01c1001a400107411154802c02c06414903507484101a42e00204541c026004002840010b000c249005581c0e0821402030078050b42d801100c0c0c01146159100340c024000c14040c100c1c04008203156 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 132947419 1250 132946169 132946181
    0x1a040509160e280305010204090c11030909070c05030301060801030b071718012d0606050f03060405040c03051c110f060402100e06030411011206050f10030e19020301 73
    0x241000c8128829215101402d4480b00d0591903009035003c48100d0b4001900154080407520840e40d44207506560b490124040e42c05400340504a60603c5000200580541c122004c181c2a80002d5810320100000748172160400520352020001030350800f0b00403981c1400218081d03d01603032001169810341c00c020300210400350041080201544056422000c40b14500da0040507407a00c9401016040d842e0318003600081b0154a000c05039a40030b1022000d490701522510552200c05000b40c90391040c0c151080d0182d503c1922040c0401c01c0001c070b45c0d14040d88402d030300602ca22102e428150b16601c407546001c0c0000000c03407010048101040b98982c12440c4614005285401803a801002e2004217803500000b410003801031043d00304000b54103006495842c004003026250300d0700c92519041140510701d10488031800b140f40c0300354501840707505006000556401400147d00095036406202c41c10708440c5541301050341d2200002c3d011031060041201000d03840c0d0760048481c2c1a40101821208 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 132948669 1250 132947419 132947431
    0x120090a0b12070c0303020912010e07091104060302030a060308030109090c0e0106020d0c0503160308040b010b030f131119080708011a120106030c0906030b0a05070212131a040509 79
    0x1090140140480c0c810b0402503010520345060030700c9080a00d42640030780200350b4030591040340c07001503c003038540542c094090040800e044450566a8032015012100c1c2c8040781140342c001080140310860281d0020340c2c10030f041c0d0708000f80b510390302e45030302c4806c0e0030a8210800b40c5440d098200d044c01070756244440a001c41c1d0b00c103030246500d42440650b6034040c4103410700500003004100800d000c02881034410184a9020b950ba003c01d00d0715004202603022502212030b2003044001254020042d000d81c0c1c818404c40903c2080b03901d844600000c03001542d0012a080407405800d141203841e640100c40910032070f08030740344c00541007800850401c01d13543c104d1326243c0e01d8455420aa0f00e9100c1d200c4134800002d90303c00800c82008010302e405000a03070405071103880c01e103a001403906800e41c05901204e0154200c41c59030340f81c0303902801c00c0c1c400580d00400140d1040400740da1728506900241a4082038030b040221950f920303d80607080443c514030448002c080802c0401041c186010800c2c3d00c04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 132949919 1250 132948669 132948689
    0x19020c031b040906060f09021b0a050d0804080c1b0406080c060304020103020c070906080a14060f011e05091f0b27060405090f0103060e03130b03090120090a 69
    0x30146038180c80003025501d61240383c4403600842440029488540a014550403c06142d40c84c2e10501d006035026880440c005040704504031071114010841c03201280d400400b800b040034105030300316601000030300103907a0700c1810880e03a10310300f100304520500e181108114011464400701007000311156980400c0d002d402c001c241c41c1955551070100c90384981d090070010303215901d6150880c50402030740c000424881c94070001240c4600001241c0604d5445540c0741801c6000f85141613480c2c10007a6080f1004035034400c0140f10701d40010340709801e1022240800c00c0c90f00c0d0340e00001641400c00707a480d90102548500c1101d19201f1603401c21015100241030549001d40c51009450095880c1644006600401680c2c0140e81c2d00e240c121801804010301110b0329080407868610b54260070301c012243c0500c2c10781c01c42c605a1011094500141c080403040c03482e1485e005c085243c2e43d100404e081101d540c1e414450701780030b031100c1240c022411008245030321034000b401803008070140c40e002030300c902d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 132951169 1250 132949919 132949933
    0x50603070b041a0c030903100f0b0d1a0a0f06030b10080d05041401090308030403081602060108030d20130305010501050a050604052206140a090509030301031209090219020c03 77
    0x41c0081c4036000fa11400c03440045035540f001280103904602403030004c0c0341d040c0200715010346480101c0c3c124452825094404001903a500402c0014401200348024000341500c143c1d24003095a502d0b6190784500307414404900b151303041c8030350011104241c000301c0304c5c90001000c2c8411610180076080c040e014000003415100b5500c0350261041c0114401c880c0c0c0b4400c0c2050000103a449002400015a03200310041c1c0c407403d261401400c90031084800c0585032000d042c0980006100180e068100eaa0100c0038520300b2421030341c8075025040700400600d450f49000e03c1d9980f401c62000c02000701002642c0000e02071420744c5041c500303540041e4041840350854200c02e001e01d5a0f42000c44084a2003220f200b0801c2003010340d00c0603100540c00b480c8840b5032510400050b108509010309040e02001c917041400e00e07440301c6c007010403290f0545036944a50720a000500c0022491800f080c11000c09040242c0901d075208000320681c3d11089200751030070701c0e00d504041e81680410107070720210f40131809050380d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 132952419 1250 132951169 132951179
    0x9010e0f01140c0f040305160501030c030528020f030906060108090a050316050f0a0602091306030f0b0601111c09060c0f0b07031d0109050c1c020609010e1003050603070b04 76
    0x7a89409070010f140703580c00080d8511042c524208030340085034010b0603101e2042c450700745480c940c030035480350b01d001c282000070141c255482442441d01c0740ba994607076005640d503250b40c2d00e00040c6c400039607909101e0307080180c0012070718031802462161030100700600b11440c00c0e200040c10600050a003685941c0000d003030100284000c02540c440300307400b8004298100007420001e10700300c607404480c0d0450050411903800e115203a0000c02d10108165081240c441021207214200d440b513102c09406802e01c0d4880e000015903d040050704180149020b526903410717200c1882c106107280d40b841c0c1c039001c070f90103881c10829001003143c8000d00c002c0c1460030001c40d81d074982815054048100070700c090070880000f613007140070b07500c018403c500000051804000b1400300b18000c0c90070500641c2c03644070702003241207070b480c0c030b080c945912030514032040d07840d118150f090041582041110364144200480404901d8a0b41080d9105281c03c0ea900410316040c9101030605102d8560030104110408000501c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 132953669 1250 132952419 132952451
    0x4050111060f040308190911150405030604020d140d030911010807020319090b16061a0105160804031703060a0b0f090d020619120501050d0230030309010e0f01 70
    0x81d1050b014201448155183c3d01b00c40000f4541c4002440c0682c80c0c81c812900f03100364110103a0b81c81406881e80210091031a4000c01240102e115940d8554031903030000c0e006003880741112611301d00c517511011214076a6542d080c10300d4655040c050000b0b80e120b5030102805810044010b40120a0901090900300400025100c0c803d1600e40d208161290901c41d0707075144141d003040700030a20608c0703603038503142000800904001030800964001d41040101c07100040e000b8542016000140c40f018613040c100c40302410306209a01d420b4882e00c0d403d100010100f03a0a6603280340c15002401d4840d541c2c43c012080110408660b0042500c580d0144911070780aa001401c440343d0200880724a0340030101840001e00380d115003003c070004188e10680003031003560411074841c080f0201080c18010760380c0310000c0c85860094403001039408000e9003160001b2100b500c071064445807048509441d81c02c0e0034140b00d80303554001d49800721103a640300c2e0111103110042c1301010309010130710b0090001000d070b04a025 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 132954919 1250 132953669 132953671
    0x220602060417070b07030b0d05030c0a0605010f0e040311100518160f05040f0b0d0f02090106110607030203060d060908040f060801030f020f030f010f060e0f070f110f06010b04050111060f 82
    0x5c02d240d551201c1c03103d250f480840004505030300c402200d540d05950100c2ca52102d00c000d0040701c0e00c0e070401c0008100036602c00711100580c2c03208002e003000c5640e00c2d141158070050340e030714203c210b010700c102a00c010400c034098503108038000d5403115000303240503408910301300c081101607552155a18041c442c0807120144031003103807021980865804071040b052801805582c035a01d5000449280d01401c218840110085c80b5000300c2c0e6404e0f69a0342e88c00c042e2508110505001d040744c002c0310019011a0080c0e0103190802d401030030502e000c0310107544203004c81e1608442038400000100c3c0030002014a41961070140841d840c101c0000d500d1541d42d100200c03905140244a45140b40804400d031702c04002c080d00040c400c0000340560440d40b0041e6005043e20701602701e243d2046070019164040b0980094002c845075500c0074142051000704172203a940d2402a078505019620403ca1b0300e201c10410b40b4060004a074a8a5031549440000b60076001b01e1001c40001d40c019008110b46210185001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 132956169 1250 132954919 132954931
    0x16060503090a0311030c03030406060911030c0a081510020708010c02010b1f03150f0504290f03030d0606030f0c030e030f030402060906040602010b15130506220602060417070b 77
    0x1c400702e4904184c1d1411409400510341442c4400710810042c459a41c01c084c08070740d00003800b00200400e4525400440c88110340c0d520345a80c0810001c4040341c401e02c0c40c2c561080c10810701032844900d440004c0ca005142d11902c0c00143e20111052007042420b216040f5443c00c280004c0018149a0b0042000c9800d0b10030000380002c88030245480160081d00100103000c9072070390911a0716292644c90b102c42403280030b840e010398a8088204a890030300c0a02c042c401d0300d030303c11824040c0c690200300300b03040c146a8045030b018003081c0084081c125240c000c40c0040c1043e91030200700c42200016140840d8242c019000070103083c5048105500e0b40407003151000814122201e82e0f079611800400d8072417203211113481c0c000f0303c0010006001a419485408008011510045000300040450f01e450080718030100740c4d5200900c3c00c010a01d07005d80144600c0001d2110100b0505685e2880c8400ca404c0e9400b19025030416000c00041066070600b0318000c1384c08102e0740f03040c03003010b450700d5907200002494 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 132957419 1250 132956169 132956177
    0x4060f050f150d050403021c030b0a120303060b0c101103010b041505070f0b090c0a05060316030f0c0e01110303150607020f0405150a05030a050303060f0a0306060816060503090a03 79
    0x3050b030000d0300d0101e9949050a03a0213010509040c60029521401094684180181541c8180d401c52190203488420000200200211418440c40d441c80b10109034044081c5a603031000010a0412400582012004507004c0c080032403699940d1000c3d04c18550045a41c89000c00060121340d40c00020359060314001c103581c40c400340707150364156120310900c500500f80d00786000d5242c0420901c44142d600c1606500280e40c60034441c0380510012401e40d0040c0395010100340000b611520b1a400c1d4030320a0f046a180105204013980202011281c00c1006040001c1e00b20748101519600080c505050416070402546546068880d070401c90348401204c0c3d1255000044510556845c54821240458014401c024a04040013207074181003540c11028001c60210800180903e008542c1680140e0000080e500d10b507144e40070021114582680a41e0000c40a04040b000ca0414440c0202800e1004001d00c070161110801d00204001980a0420002d042040151403000411002046681420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 132958669 1250 132957419 132957439
    0xf0303050402210d0e040b01090905072102071106070c0311061209100e0703020108040f06150b0309010b0604051e010302190503160206090d0c080904020403030e04060f050f 76
    0x3000803a07450081c002580c03081514080c510040001003111000001144c490b107105c14144014442a100da2105481c041781c803070801000360030140d8000681c402c1c0307285400202800710f0100c00318490050360b00500d01c1d9501095a8003001409040d0b655901c01c1214000c1c11f001c41b542d50440900e4860200a0203c642c4441169085d15220180c0c0c0c030310310a0f40c4200b400752a100c1c032110ba882c511a0020460542802810440c0c0400466107005890b0103a480c4e1071242c3d11a25a0700062060b0743d4111401907580b03a180002441601070036014100f05c0541a40d01d0600f5241142558400010a44607110800c402c2000f070391540002c6918820054010000036400e10058000740503007030400d50201003105c00d111000c2c0d808002144540720550b103034015400300a404a07a2100200c80303a1825030b202c1020710b2117503400351280e0314107941304041c00c0c0d141555400108099030803035401103011442e1440f21080a02d442c0c02808068a0035004c458803040c03130700001602d68480120964010b4200c55 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 132959919 1250 132958669 132958673
    0xb09070c0c290f19090803070b0c04080d0c051501120b0a1b03060806100b0a051e04060905040e12180301060e01060806090a051302041e0f0f0c09030f03030504 70
    0xc50114a03001071009850b207501018241031544d52000f20014130a0041484641c9481c0c01012090151000d50380190b0505082c3d5440301c5000c0c5019007401e00500083c400000e80700010001a00e0800b00c1ea40c42c9000d144007881e00500c0c000f0540d0040304030b82e0104c0c00500c101c6401404000c540d0740c20603910701c1d01e13846896140c0024619101d10341c1c1444621002104966055000f41007103c2080007195202d0b03840c660040600003480c0661300025408000c1d000460348240d01900d46040c2c542820310300006403044421003640994421404600040020400340c5054403451410070140c60203400d6400800c05040c0180c40f03840c440f42c42400c100d140710202070b1025403001d0058a10003040003090750312110081c04414084903c640b08005142c0068030244d200e00407a80681034a200c000e0102445a003004082d269010790049c0d0f00342540340342448440d40d030140c2da540030305104001980640d0001c19005460742015460140403460307070100006071002c403c1b41c07003407a050704c0c0000e2151914 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 132961169 1250 132959919 132959969
    0x6020d021204050115060e0a120305130311010311070c0506030a0b03010e010e0c1009180219080105030d03020a020c0402070c03020603150414070203090904080904020c010b09070c0c 80
    0x2001d5501d54107100201008200001503010781c2e42c003102100b00d003880356031725034040300c0800320107001a4111403001810800703da50b566540300084d100e800d00c981000e485200002d80c200c03050f4415901c0d00c50b1100460440c0d46c2600c6901c140041d10151710780380c50225241c1800703607081c911501d4020030000000a08002081d84441803111000b80240a42d10003c0601c40c0602100c20034440c140c006c850842e8500c0c90716140402c250310711030312a200c81074900015080c41c060f200042c0301c07017281c007084800c042258801c142028400e5a031520543d9506082c1490310341808581c1d004141071040012b0341e070072031f000140e03100c60000442d8056510444e5150400d6071000e0f940c0000c0d04142c020080c840543c2c811480c0c1c52000f00c1c1510700b044010700081061020810a41c0c43c800542c10800039048142002e07189641d005003e0207004d031908058202290480c0e02c104440c4110380d41d250300d20f450310300c1d00c0030449421511610741461640040e071a60440c082c3d8070300c0381e0700d960914003511200170140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 132962419 1250 132961169 132961177
    0x4110a0518060a12030201091101080f0109050a2c0f1b060c070504090302060109150f0504020c0a05070b12090607140c0a0611070b0a0e030307031d030304120807030b030a06020d02 79
    0x10b90002400e0131041c41c0c0a4041d0500410488001005820800c0c80354800d54800d0710402d04031040c01500d07440c1c40517000c01000c014011002841d100e041410a0380460420303070081070000c480d08281c20805070203a904001443d480e203540d030b400c00e00c101c1500e40b41c0d03001c2c0311900c2c1c082207070015960640c90102a10f000b2182d404680c01c5410300c4001c0044c540c0210381141291141117080c040e40417400d5103008003400e6801405400e44004000b40001c0c00c007139000c0d10b211144c0908a921180c1242c5590345071860940c060741040d03a00185080f500b484841201c3d82188048000b00f000b806c182c10054201400c00940741903407407010445001c011410045070002c19000002004850304103615440c503035225003000d070b40044141c00821684449440340c2103140ca03940b000b450a40c0c81c1c80c00e044024254588200726003070090280e041c0c0c100c10505c010b42c05513200f1a401d6030000c100c00b1002d032031002d00400c21804c0c9450060b014006d0b80b4040340102c40103a00c1100180c3c3c81c0f140d116041c0007405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 132963669 1250 132962419 132962429
    0xb01020f010e16090e1b010c0c15030e0303010806070c05030403120201061a0306031f0608100b0108100f030b0417130906120314090609090f04110a0518060a 69
    0x20030301e0315200d8151000b14140c100c10301074078010600d80c0d48644801098170400f40030601c40f503000280c0c0c01b0514407485000300300101e05251021a8416540b16071a0707112181c1c2008000c07089106000908581521601c2c1b01c1c03e82c401d016505541c54508076507240c0300018200340a00c02d030300c04030404000707050003120302950b84294400b0800151082c001d000707010a02520b001c90b203115004030100444181640c0c440c00009004140000301d502d400c06030440a0701004046548548000c1105a02070040d6800f5000030100018403a0181c0c000420113440640514645641e010044c400010b00100d1038058070341003410400961280c0c42c2a12844051401e0b0400440d00811365805d10501c40700000100c42030280e0034403040380c542ca100104088030190080c0494401c0f00d899038401050005401c0343d0000030700207030800d8803010103d103035080c048816940c0400800200402c016034625640c102c54030545142c1621400c0030017080340e28010014142c010307200b5000040701e9903161010503000d04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 132964919 1250 132963669 132963671
    0x905100c21020a14070302010221030a2a020102210118180204090503120c03070509010e040905060403210207031b0f0210050a091e050d032718051501030b01020f01 72
    0xb0390004403164450b045c1d40000c1f40180152002000d005442c0c0c24480400442e00c40003501d907403200b00d52030006110b40c440c0b04a0000c0c03040c00c24105000600b900300c240082540025a03102d458491406003c000d069002100c802c9841c0140024a56044422008400070200040c0c0c00d40341d204840c21481108002540b013802c11001c1820070902002800060399490085001c60302e074015454039a010856180b40054014020b16225601c03030100581908030280c00041c0350f0100345c84260070158100d400b940401d184d1555210248141013014580700346a040c11424a2000e540051040e68172024500d0100c0003452580d0501007540002d60b801e075070080001641041740e180280c01030b0400c5000d40085010045c0014580e40342100c070840518600d00c0403102c2c6820241001456a41da2400f81c0800074801c0031804600344258101261144100b10000b61520b407215a0001e00c11403080c3c8804181400e0500c00711490b0245008603410702400d01003410608440100d04d000c540c450100340ca9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 132966169 1250 132964919 132964943
    0xc0f0804081c0f08071b03120e0303240307050405040203011514030c031f0c180f170d0c20270618010b030c07060c0905100c21020a 58
    0xc808015100c40b0b0210b401c1d12100d1200714201c1c8281c0343c60030200c4035000450411003040701c0200e00343c5000b540d540e1181c00e204c50410100d11511040307a07041c141d1100300342c3c80082800100c00c0c64424003089282842031481d10400310750040303900c8a400784100303402141c544012138110f42c5e0a4100c6107402002000d040307a107a6840c0b240392020001510f20700e0190051044540c410300b808901000c100a500d05500c0070306207060804801448095442d004000e408080c1c1800000b20020500043c20516140f120b40c90400d107220504000b041c804031219030050044c080440d070400311500031185c025640c2100d00c04c4030f1000c600b682c0d00e1a000f881d4441d00d1003010b14040c164510b800030302441420700c0e0303071401d03a01c0500f400005120f9210800d0545c000308010080042c20070010365021b4482c403565420410103654183c01c0d115519040f40200740c4c041d400388114100a9054000d000992030300700c2c00340b944c68450301c0f003514002c068206807500220200281c24000c202088803140d00c040c040c190 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 132967419 1250 132966169 132966193
    0x110f030403020c01030b0301020a020a11030109020306010e01091512020f03070b040f0e0601140d05090c060d020712020c0f010809120f1c0b0603070305070c1202070f05040c0c0f080408 81
    0x740d100f01c1c070b20703d400710746401d81d4120a42014420f580d0060540d40040a2042c05612141328803d200382901d0f605640f1480d0440043c0c0381480143e0003001101213071800795041015003819a8504a0102c401540007241001a800b90507900c081440d010b40d903607010005501c02103410b00720741c0c1c1c204194207000007800045402c0c01d000202c046480707800c40d241c03490301c502c4011905e1100980e054640b10b04240305840f08004254805608000e001d001c0301c8803a803505021480542094110b20405a03000c02c01c80140309055032460a14103240c03021700004501100011644850044114104035580e400102210f00805c031401d0b0841c08400882d031070382d01c030742034801c410791240301101d00780c41d40a030042d03201e00440d0280d40e02c0c0d844010001c50a41c0d80d4031100320010000100030004106540d10090042211034500302c90b0299268058003040b410704903604a446170503400a4019480c0950059032640c0c017528034400c1d250708c9030040d80a2000b90030440860301603034000705040d0281c3d40d54004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 132968669 1250 132967419 132967423
    0xf06072d0201021c200102210712110d1109030303040804031707030c06110904090b010611070503030f0a0c05030408100507030203060d0206090d05010f151208090103110f03040302 79
    0x800920036802c81d070205100c0200b00742c804a13680c1041c800304000c203030056200ea401041151a81c020600010f0030010300500c0f825071035400c01c9008218006400503c45241c1e407000300710442120302c0005210260182d00540c21601c12b4006d9155000e6640380319030780b010403440031201a208001c0c1120b0f2241072030308121001c0c1d4418401194440c2d030340002001ca842c030705402c0d158059007640701c803001100192903904c080c008001120405c103000301714a6031a40d03a540311304500d460140441c0d141d01c1d03041c404094000d5500c040b020303065038001d04080191b907130000200c405480c441915151200000401603401500010b401002e034007000c940841d02c104001600080c5c003075011030600c401d4480407020380c00c9120607101c80360805480c5550001505124009103030072039003d8010703a501d85050701c0e110308440000300c03040c03e42078551000301134940c0f07001c240ba005008044198511001c49546944852180440250625132036503002c410034130b00701003034441c807864032204a81e1303034502072034000c2d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 132969919 1250 132968669 132968753
    0x702031506010306080d0206010b0a03020909040609060605040e1902010212030a0e011415040917040801050114030c090f070c0c15090b130303140c07031a060f0f0607 73
    0x1d4002031130004002685040054911640603003070300501026402c1c00b0140740a544100c0030700d01131680810198226403154441107100380d01034a030004901c180c900d04081500c405a001d00d12031420322034407400d0240d0100b034951003001110580c61030501a4030042c2d08003c3d50140c0200041408000c0101a1003160003a02501071803000800410001c1d441032848101d007943c1d142122007500d6007051050410380d0010b040e050040413858134801c01c22440c00f030240d1094028a6459440c1c40040044581d02e50a00300c08890441c0130b81010b26086011482041c0002c0110f00c08030681800f00b80d4041c007070301c41e00d03800035009039800c0d0300c6030348800d80d90100d1080104120001041100d00081151410040d5452802c000c0746415100c1d2450b00c08513006401114550b00d20501005460b113644420042c3c100210701c100c50001440c548100180094003004000c03501072207521049450985d00c600000d580f0319401c0f00c5158841d0601e041420b4801040e100f02503904a0b00e480910303900d00490402d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 132971169 1250 132969919 132969931
    0x3030703050c0c0a03240e011503020915090c0304060b130603120905090c090604050a08070305070b040b0a03051e040302070816030b0a051e16083907020315 69
    0x1100c0c400c82c3c4800348107020b1007074400a0940241c050701082d440319402c0080c1403503c5040c0002c9040000760701c40f1401c4400741ea00720f15451805690410840c107002034480d501040300320030011042548008154035040c020b24580428900000041c100700303040e4000315015601404060710210844a603030002c10b0640000d88100d10b4800008041a115000e61340a0303c002030401c1525031a8040c400100d81c12220340e0070381c011010301000c43e071901c0c2c030b0105d80020f040207002055440c2ca181400c5003813843d41d802c5452911002c0000340b190f00f6204003203038084032180c40c0008040c2c1d1542040c031030758015510700303140424440003840245a400284c00041e5a40e4506441d2090441c40c1600c07400b185900c80203000564040010700003103802e42c04568424000c1d1050059846013020706c0e16901c4084400098400e0208818503c05900030308031a884038034604900400031240300320043c005800c0c8130b04aa51075a29060420040d9488251001640d025040325100c0316413118210340401c01f2522 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 132972419 1250 132971169 132971173
    0x1918050411030c2119210c0804050f01030207080d0617010c0903200303072105090303030f040318180509060105010c0809030715200601062c03030703050c 68
    0x1c40d05551070b011034a0030203c01c00508080d03840034540100354802c20041043c404078021741420604480a5240c2030003513a00c900a0030208500b8100b03810054009107000c3c500308801c1131110000512400d045a00740e40040710110140039004004130068498150010014003010500c81500f20041e00b1220503a1004010320102c1c0c1c0107540158202c0c2c0c08020550009131030504104085806282110030381803410107546040d1008001184c9580e1105030101d40980e076080c2c0b000b1300b502100b8590040400185411850074652b140000c0c0c0d00d00028020707166444503040858200f5000c2c2d0960b0001501100d0040302c0c0c16924001c07449101d4400c10031080460801000032807501001c5225810788005842c0c940710b0300300d00e4859030b1081e0850b10704550144102c06011403011242d880c44e103c18401a980c0b052020302d01044400400502e6982c0200795105100600c80fa41c0c1052202c0e500502034030903007101d101900320801c42e410700580407d4050100042e03110505074040002c022103103214003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 132973669 1250 132972419 132972443
    0x90f05010c0509011d0609090907060e090c0403030f030609060f03030815030d05030a11040e071b030e040207020d06020c15100b0301090203180f0c01020d1d19180504 73
    0x14041c1c0b050b2140400e0f8500003044001c0c0031114102d4030310450007040028040314105035100020400351541691443c5066211070810800c0c5a440000010a0041a68446031070304100740905158061408028144507030403066685087c8254800001044145070900c011a510141f00302180b20500064001864500008002c039800d810303031602584000d0001c02c3c820303c0c0141d0031159508040c00d510310030b50b19200c400c2404080b000152000d000140c0c0e06d00b5490400103030190002001910300702162440414410200360803082c1c0315100c400c1078401581d101ca0f81e00c000354941d080240000c00f401c3c4082840d1140780c0e00011050088480c0140c0c124460f1101d00c021241401c40b8402c00e0740c448030801c01400403081c250081d54215003030056080300e46480c050780c1801d100d40c8500c106119032204580103040e42c3e0411019400a5030b41c10304039031f8241c4002d44480d070b8418640e5440e0240480c401302c1e002299680f0075640c010002c00441284000c003035541c603400780200359425038a0030607050f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 132974919 1250 132973669 132973691
    0xc09040b16090b0d0c09030606031506080610090e1002220602030c030f090d020414040b060a050a030807050f03030f190519050636070804050601030303051009090f0501 74
    0x940b10105480c10707442800d041c41c000d05039840260038480039100c00c100c4000e00000016115010f030f0341c013840c420f1013090204201200c240d012a41c4541c050701180d8090420300050007a440324110681d55880000301f0700c003404402c5203103003980070121268464400290000d4010fa1200e9058012550b04014081c081c0d030742d60b04030303580e000359032403015550803c21114007401c42400080029403400313800d80000700036940000e0f00301c2c0c030404010820300841c40308100410000e5150b1030b40c004070031544280d40c03034103201c0841c6140040e80402841400c0000c0d00800380401089080031200c002d20440751340c0d01c1d00340314101c0907440c00d0790382d40300c521040c039244109845e00b0301403144225000c42e04880b15804081c2010301511001e44110381141203220140c1c43c0d2203000d4042810103080d640f8a0000d1003d2004001803440b0040c0807108120300c4505001c002603010a00504503509841d01281c903840303004841c6d020340f643d80d0040c401e0703628044004017000184160001414007078030007003044a060f9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 132976169 1250 132974919 132974927
    0x60105030609060703181406060118080706110a0b07090f05010311030c090415060203070b0a05010506030f07090905131a01060806060a0e1e0a0801020703020a0803090c09040b16 78
    0x155402c0d0103d070031141c000340a90744a0352100312180c0380d068240304600a0f588402c0200300b2902c1510340650080000c205965801134248188899904000c1403458909002d180c0c5480e80d500a941c02c2140014140042d120104094401c0c150080c40c1c0200900700b2200160010245115410f0700380b541810000300ca6020f4420003502c484070241561071036894070450b40740355011202c0c03d80e0096450841000380154010b440d0040d124680083d507403541503003400c0351b14080003008921038504103001400943c42d644217403900140c0402e01c0c00a680c40c1c890b41550b00c00010f40200071280c0c0303400704201c0f0380c0301c8204200080500881d5851181c060082d10080d89081c01d00590002c290305d100072440f10304044004003100c802910300140000003107400244c10104d024001c0e82123112034589080d007132520121040c01888600001c615103480da40d000303503e40d03500d9a0007802406004c80080c411040c180054007240c0c0000700595583e05e094902451100016034400000c80140c10b061039100c2c0c0a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 132977419 1250 132976169 132976171
    0x1020304140303040809010c02061e180301150e0408041502060f09010c090608070c1b0618081009080c0109030305090c030c09010329040c03021503060117090f100e0601050306 77
    0x178102c0c0e0700e4043c04030010346a9184424080740c100104101d2102c0b00c804602c1000310bc00540818035584500b40110450180c1e10b041310075210740d00d007404140c204580c0d10350781001c6540300849041c003903885081000007070065030b01c0b41c94400400d2440303420f4503902081c8140f1611103a042d24403076481d040c10503800c9946540f02400400ca266005200043c0a40105540a070181c030f8407140000c0c03250741320811511040c80011030301090820601017560404000000c841601024200e141d2400200d280e82d50200518401d800b940c8401d0340c0244581c0204440c00c02c40400000e000742c80341440c000b00100b008954511035400350300307603112092901045000b04410001c02c07514280e402c1d62280e00e010f40c5800202c2d0012402400c13034520303203001007040c41c6c07203180507012080d4a0b61950040c00303c0000c0702000c4660164040003001041d0782c02900300d6504003c4147d204000d82c0d9000c2440f0b2405100c103842c00d00c0341c07140a481041c4400e0036006510000c681c60281c0358682d03038603421f1681e6544 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 132978669 1250 132977419 132977423
    0x616090302220f0e0f07152a02151309110904021b010501031b06031427010f0617060402090402120a12110d020601062c040e0102030414030304 63
    0xa91802407000b40715082d50700034180c10001c00201048080307000001c03a0b0b205a20010240c00122404003a46424480c14004003055286003200030030a04004200d07441c0c103c2c0741801010120841c1c01c85104502d40304110a5024261074003020681c43c80480710b4004801a0100010f218000704c0c03c3d50721402141d02d500366600d05241011008400c03c000380d0004a00c81d0981c503041103a444941000f4094140210b000d0180040d0a0030342005201403c611500180181414203c841420142040c60a540b001401946090f2030380d1102c6404407800415422411940c20800412450076055201d0001c46440c82e1851104000c00c1043c3c0ea211002150040d5024050400207400f42c2064440101075140700030030340e2001100c1d69514010740c0e00450502c00000d1148041c001284c004002e803070040b04a90005200303540c07400b00c00524401d10000381140e111a01c1e00401d102c1044540300c00d41814004006101840c0c041c0318450007500100d80950f03a100000c641152040c50100859020701c0e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 132979919 1250 132978669 132978679
    0xf050f180405060d11060708070503040311030f0102030906010501081806090106090c020f030a030905160e150d050601180f05090c09010e010b0405220203070201060816050604150507020d03020616090302 89
    0x8050410490250017147c000c2d20083e10402c45000010701c00d1000b4000fa61240b0010107140500780d00b403500d03100022402e58001c0e8810800c2c040700110001d0501c0c1102d409203071640c003c0e540c5c15007003180e00c1c0380ca2901c15130794400e041c10b02141d001c040d008002510700300001000040c00860049039120b204e07043c1042d590b0030401c03159000a2223030300902c0d581ca02541c2100d60912050008014a075200c0d070101c0360234170100052100c40c1e15a007503030ac0036104c1d0440314107041c42c9654440d561034202c10b100b1000340c25000b4500d1402441641c101c800f40070307a001c20821140c640f640c41c803601c40c1c0504620612607031103d4008961131550582003070590300300620007030501c0d04003800d0144246000d0300744100c140030340c04105103440715400114071400301c03a030010500501d8003500c43c3c0f40001040426000f00364000c0103110032385808007a102220400e0700045554080101e0943c0c0074403da140103900020880070000074913400103081030041c0c1d41050040181140b843c000c8943e0f8280e800025408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 132981169 1250 132979919 132979943
    0xc061311061206091506030903090901090218040b121b0a061422030f0614010504021608090a0815040311060c07110301060e16020105010e040507060f050f180405060d 73
    0x141807220940341e1249080e0601081c505c203840000705943c00856017042c007940002100780407803c0c0031441d0b9005018940080d81042402241c0340514054406003602035940d4281c9411240d5517101c6001c1ca040c1c1d044107480c2d00c1c0e861907081e580c4400c3c2c4c00c4d078094001d00c6040c4000815074404c0300d042908084002d1041d0500c0b1041e081e100707400c000c401203207a010107503a1002c00480e10341281c55861500c540c90000b0040b0000c6000031024105030f120a10462060000707240b41d100c00d02b00240c2c01640102c00ca984d4a40d0140040c400080542042805102c0ca440303100360b22250a5070240154000d44403000d01d401e01c2c60310965141411989a200e458045c0705500000c7c000c00ca040c1c1d5201c00040c0081001078580441c0000f5040071242c40f00140c0031617103044072454081c860380740548056001106103203855200c0b280c1c2d8010303034440e00c420084007115802071103100f8000d54203444d09000394255111041100043d40803200c80d15140b15500c0c01000c181c1c0d503d4580408090958450800140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 132982419 1250 132981169 132981181
    0x20102070615064d010f050402030d11071203020c0111060105060d0203180a03030b0406141c050a0f0305040302270a0203100b070b0a060e0f01090f020c0613110612 72
    0x50300500004c083c00440c0503101c0b400c09081c01e0000300e80d004a25114820900f080d501c8080e00f907955103c0e0341511540f83c0420300000d81c5004c030b0b20300040f001d1070900021018904d21442c0c64241c4d07e5100c1965442002034640815a001c00c034404604000d0380e0700b8401c007400310380c0140c652100b03100780d90b0b000c08100090014000d0340e8011f9540100c5403490450880c10000340b0500300b0441810480001e544d800e100c0d081e501d0a403042c1000340c010b29030401c0250641b900480c032202208203400d103046000b00070750360401804000d02800151301000b24101018031f031030068810740060104910804020054251100018441d0010a07161046c3d107007594450a495000139800501551200d00c0c82c07140c041058a50b000042002134469110945a842d02100b071008450b042c0d00b15000c0c100400051044d4201100c1c0f03460706503404480005005da1442400c0c5009100300a050f1034903014120400202e002003a5000c10b441c2e010f210814910030008040001a2090780300b80300300802d41c1404115 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 132983669 1250 132982419 132982457
    0xe0402090601170916150806060702040204030206041403060703020316080403111204031b08100b0402120103140c010203090d1e05060408030702070f03080d0504020d1202010207061506 81
    0x5040310043c10221074400805a5003441e4800072a60313495180d201a03000f444c08110310074140018000d03554200322003001802c000300740010140c0518031607080490744a0a65032280e040f50700940e8014150b40e03071142d4500f9196030b00c106080ea00d40c880d0007414000b0f40f05900034000c4a10034001000100007010304e0f56001c6d502c44101500c25020003c0c0ca00300b24042d13050410140c1c015500303001080b526a403031468580700d40030f4503141184030412200c504024030103000519032001c0c202c010000c1011401840450001d005451258070b445a03c9000001440410804541c82c080c404081d111144119801641c2d00d10a00440c43d03000592000038001040200281d450a038007415011400361885840703841c5010010344060b56588400014404086e80401c40c480092145400700f107020340c995104c81030b050092148100400c0d40b6000005c046586880c0a00401b990003001c01c41000205c0500034000d403c204811200706141100c90442c5812202c030703c1c070483c1c840740c0d02c41a40d40c04080e5140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 132984919 1250 132983669 132983671
    0x10506030c1602090a0f05060d05060601080405010e0d031b020a020609040902030f030d02040512071d09031c0b10030203090d030c1404031a010506130b13050604030809090108070e040209 82
    0xa90403102c14550300700141c0c0e8059045010f0040058081810080300e100d4904459001c0c21403845501c011003950700240000c10142d81c06102401d01540d250313102d08105025000b1207110a201d0b00a0100440255805910162040d1117040050740c150128400980c3da941014401070b5105805118040d03a80c41c058000030501d600c044c05680324540d40000741d528640004411592030b80d004102030200e414a22a410503420600340200980342c60710a0b815800b05620034100801046c68000850b00581082250f0304410f24891003c803200510301200001c18040303020b18402d1550b0110660414480c1c0240c0b03010b03400141c05001000a190000d5006060f92480f8409200c0e01e4048a240212120050401140101d000c1c5002e4140c100100400240582042c1d114207028860034011082e0a4980d400380c03021102c00c00e03074034400084e020440392055400720f40d1000c03000401004104200c03014145001081e10142c0003a603c2e81038003926032003140210034560340312200040c00341c94004101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 132986169 1250 132984919 132984937
    0x170a0b07030c09050f18010326030c090d32010608010b01021b0f0604030b0a050a0e0a1230060b09030d14090603070c05100e0a170c0106180f05010506030c 68
    0x44586006c038030f20b45010b855403d034003c2e00c01800420441d440114102070f145030344021a400240383d4540f191540c0c905009002c4103d000c1e0400c0b0020004002c010707505000046501003105000030000f0388001410000207542084035401c00c0b0300020300b280c050244003060041600603000d08180580c0c5050203040c1507011507032211a13401d0f030480035150300300204040c5015103600109131a21460384006d0b0748000c2c0003a00d0051610110801480010840c80881d0380d102004800003800d00000315095580464007020304202e00030403007810303941e180c000b804800038a00180306807541c580762001d0381d02501000b079070990401c4450844040c850b1a1100b42103c061540d14140703c010700125106800c02c44044001c50303210220442401740811400103251603074907052003643c1c9944801e40e1141d181c100000d01242402c100c4400426014054640c802c400400800816a0301e0074071102040181ca8440c0300d5520b485104203000e0024010a8140c0c2c002800c0c0514607115542e441461b50301103071300b03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 132987419 1250 132986169 132986179
    0xc01030504060b0d080705070506070f140a120507060e06041a1b0d0c18030c0b0c150a0903080705031006050d0b100807180f0605090109170a0b07030c09050f 69
    0x300381039654130b411070b25500d00403180b994445080d49031207445d01010b0b405c4948100c80c00d00c041d0000542041541c0c0d54280e006000107000c0038400714075071401203001801840c010041d480c5904c811343c407101510105004420a21900500000c003e0b16024140d8001d88400d01c02c44401d143c4074001200190022003030b141006840400616000d4940c01440d880c00c415521398104000007079001201305802c3d2001c07081e140c4410700e503079100b82000e2024464400900c202240c007031802d1405003d101002510810700001c8e0f454048002c40040c24088012000314030240c02184440b889031080e00d203d110401507403886203040c0b0105465680002c4c0303804600984035010f00c1c1c1d590f100c001e44c0c46074011031510b039198030b402d000f14060480c4c22252038440402c0c413200410440d0300c00c10b031402011034040c0e0400e29a40c1401fa03004a400409540140551801907203082c04200700000e105840d050140001003441d407100b5000714140c2c1e00410703c1320001340205070148420f00d02500c0021181c0c5000b45 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 132988669 1250 132987419 132987431
    0x16030e0d03021b06280203060a1505040e010801050f0f070e1c060f0b04060506160609020f0a060905090c0c06041515080604050f030c0a0b13020a1e060806030c0103050406 75
    0x181c0f0344e1401c0e40c116218080e007107805000303980c286901118071817000c2442d0b009508500e010004104540f81a100b10050f03200201c0d01518100d001e0000c88004d440000c01c0c6040568441304890b020340016203218002c024902d00040c40300c9000102907005003161340da0840a0640b11702041201c04038843c42c10314540d0300c140c13940009102807042c502240c1c944007000ca0981d0b1064200011140d55a1005008603410040c016031144c800301c005440342d074000c00c001a03209803400841d640c0e80d400303002c2c1600022004c002141480c1c0080c8040203d80c01280d0b48842580d50b0075410310f281c0100004150136900c540007040015108107010002c0d613254501c000b40b080418004070300c2d40c9010340e000f419582c1020040c4024440b06003c21002c400e00a001589414000e8007626591144000c015140b80c80040100d105003081c1411b01440300d4000340f000c3c2986071158490241c040d10008482000c0448120008040e401988a280314400c010080ccc0080c0300000c0c015000340070024411601141d80744 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 132989919 1250 132988669 132988717
    0x601050d0207050114100531090305070512130605071a0a060e0f070827070603050708060904111302070c06021c0e0603070507062316030e0d0302 64
    0x1202030b00c00c1d00e00601c0041903c1c50f81804015003000c000d0907600c00590f40700c509101e1a1200f50500b10f6040c4540c0115148810802405011840400500c407c0c103013800c2c2d05106040e404005054854061410741c0e00104a07000390030418400c3c5d003200090502d0525041040c0303400f480140180902070582803840d0400164200e402d4841115501c01c0580daa110034051480200c0080754054980c401c40b8800f4200300b48003404c0108020b00d01d452216090341c04110403130342a0142c0c04031854150403120566218240507006d40021200400000c00075000030f616031a1000b2224010703a000401068041090024000001e2900ca076031000d0725020000800026800416440144900c0e8003502040890742080e1000340030007106142000001442c802d01e964619040301d13000b6a10741015030380c8181c149442d43c040d082e29402e19a440e801050307040000240b1404d0740d81f00b40710700041c40d44031100081003a400c603141240c60060503807014841c0d0403202d0080d4020801410030241900d00510b42c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 132991169 1250 132989919 132989921
    0x36040309300809030a1a0108010606031e05100816150507111e0306010f0611070e0105090a060b0c07030314040b040e04020a0302031023091f060b070c03050609010903090902030601050d 81
    0x4246c5000d4801d0201004002e110305c2071140c400941818038040c48068400501848031803103182d04078101640d0b400105071100940d1140c20000d04c80d010580d091801480f01c00c02ca03d900d940300d81594000d07200d00a0b41c120380b24500302c91a0b203a111039002e1350140301c0380c00e0140007180c680c0c0c80c0c481d80c45044c840e40031540e02084400e00074100d441e1340d650413030706022004201462200d21401c495101c400c0502418007891840303819500180c41254a540e2000e462201074509540300000c0c843c00001c04440c44100401c85400b52400382d100d101c40702500e900c00320801e204a200b07680c4402c400784803d00c1000d11111500741c1050005004008031520394001904120b0078042c01001d05a23a4a6203502d405007109441030010212200c0c4203c0e40340ca0600c00c0d440ba50013081c0e0303c1d5040640f400c9600c07640e40c540d200101030600101c3c001d071114200c0c0f40c00c1190314a0b40c0000d603490711503000051206481400b8030042c0c1d40d8141e4440b03001d82d00d0f02c0d0815010750405401681400030901c01002c810000b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 132992419 1250 132991169 132991193
    0xf2209060806100e063a0f02010e01020304080c010c0807060608060714040609060309052a010306170304031401020903010f09021201060536040309300809030a 70
    0xc0d01015102d076041450202c0e50b082410b80c031000e2031501c1c0b181008620f0307894010158480300303207500c0106180f0189404412404c04550034440d40202e1141c0c080c24454541c50305400f291007a200c030216102e07040016a0f036030046201d14261782d400140b441215510170422130701300c0341c0305841150030a840ba07581e000035030b25644c00002582e030000042140d0f643d404020341c00e48080908110740740908024000341100c909006580605459916000801900b00109030110116024494043c4141010b648061210701070890000f828094040707110074039141d980c181580a02c0046242501d180d8480c030494841c06100780b00f65500b484090b00341d45082c0190700d0080b6131344800060036886441004140c9035403150007240b0381e142c0981409a42c9452400c0c904c007401c0c140c692841c2c1401c120501c40340145000d11090900c8450b014401010740244042c0c0544080c445083c1e981d140c40240d00b000c000e2022000b015030f82c036080400d00440d40d824000e00c60200064140c2d9030503241616400d4020503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 132993669 1250 132992419 132992429
    0x6060103270311070b0a02060103030806220e16080607110f0f03070c0605120103170c030d0203070f02121c0e0a050f010e0123070309051c030b060f220906 68
    0x44580442e083e04105000510240640010240c1450800035000b5600c200c14000201449401004070b03085540382148207050200d070f850b41c105404000d80043c0054810340d0f40d0111503100ba00f12191040c2c4c00349110b81e040da0345001c01040e05954000040321070b106001c002e030741e080c09040e180850800c01406056140c503007200c0150398030020b0340340503031822050741d1000301000400c0c001d01b200c882110741100e044a41000160232441c0c40d8540e80d0f525845640558901c070300c000200440c81e009150041c5100745501e8030758640e080c0326560166124204070000155440e0308100e0120811050740c0d65200001d202d04000600c034120340c0d401d92400f0750921050b200ca901a45180d003221000b4050b59591020581c024000000c2c003884904101e803203505182d02e04040031000600c1c3d140700790f0028a90540001c01c0703410482c114414103600d5555510060f00003400c2c03007500017042c107190b41102c83c1086aa51800d1a00324661020504070b0070b0b0700d442c030301e480c2c0b00c0c03440000d01c0681600074503010341 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 132994919 1250 132993669 132993677
    0x30501060807030c02030a0c022b23100903051603020606040e0d1407020f151c05060f010305090106031218082103040c050a140301050603010905060601032703 70
    0x15040c40310203440440c00600d010101800c00684150480e404000e45d094040c10381001019606240300152000c0c100d00c00310414051004003100c0410b91070b411075801140030b508038804a0009800e15241d01411185102c2c19074010403104040900030740c8003000e031501a1400c1824000200e0f0513041e221841041a4010390006081c040d1078a050f100c1c0b084441e0555000b8500360840c45e0000e000d41c4d0020010080c16000420040d0554482c080e0001c03c151009004d0180500052050303070303254001c3c90040110440403030099041c465140b081c207015103c010840410030341c0980044010b40340c0144194055501c61000100290102c0380a05805c0c0303040c0c50700007846050844007041242107601284559103c8205c5101e001d000e0710100100e801c004140d1580c130382d994203240c070700803040d54886900541da00500142c94101c1c460141541d40c0114000c1c859500c0d4178040509990207003a000c0c1c420303000350012801a60082d0b01c001310320108000d11a8100201c2085000d080701d40762016400320f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 132996169 1250 132994919 132994921
    0x7030309080114090d0c210f180302010509130e0f0c10020a0b04080c0f06011e05012c010201060b0f0a02070b0f0403080f0f0c07140402040b07080a17070305 69
    0x70010030f00511604540c0700c10398640d14500401d4043d601d60406480340309000320b07105414240310003140d840c034051700350382000100c2101c17140c4024981400440d00c000010394090640d000c06130394814520480790140d490b0f9080c060300e00200210700f100190001c0c0840d80d100f81602c1916000d00c109100c00310f07040701402004254500b8440300c00c00d1350b000b400454019115070000504904022a0003580061210b41c55071558580f039403501d21003010819840c4111000050240110b40700861000c812103000aa215034450054502180026110034181c40a0b004010389151041403000204014030020a607181c0d2034201601542c440d550031170050000084000d803040d01088040020310408202501e0601c070071119115500503800003d2052000007a00f1400d03083c00d009607841c03200101607096441c1d44440ea01a40c40203644680f1042c0c1c0320595807450246007030b00c240c8080314204442641b410380c0940d912030300d660000429034248a12a064001002603c0142c90f104101585000500b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 132997419 1250 132996169 132996179
    0xa0507030201030f090c0314071d010f06030c0f032004030602070203150c03071206050a0b030a0507051312081204081b0109020f0f01110f010209120106050102030306150c07030309 79
    0x19113103100c18121000c2d04240194000039840780c3c481007140d40280c29001850f034031480c4a4105582c5a005410164002c0c2c1c0c105800c90969040c103040320300c03401c0d000d0041079440c0d4040c1c0c190380104440201103041c045180030080d000707070421000401c80c1c984100d401052050940d8040d0025003090b940e043d4040340f510210708041205c0385105244902d003a00501e040300f459a8a07100007000c41c8104030000c1d403850044129600000040c0030000c1c80381c81880d032650026812900304a40062004e030a11000c210794074040e80444405412142e10b140f003550418441c1c0840440c41441190f404904104e622100214000014010f51240c100e05035201030040a00041c00920445407151717900d006047e1005039280309501c000204241d8002001c0000d080c01030310710036002d20b044d098a014020f44103c90303c40650040180f0041103500d04603003800c0c211203500302d803400d00500740503a0007080402d0151038118840c00b0200d0000140500c2c05813802000c60810341c0b10385c4110082911141c0c1401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 132998669 1250 132997419 132997421
    0xd0e06010b18031207140f06010e0601021506030c0d050c13140c03070509040f141005040c02070f140d060603030302031b12061e0406030c0303020c0105040303090e070c02030a050703020103 83
    0x4042c40c811001411014840c0310140070034841d0300e00083c8004824210600b03081d10601c4646450b001450035107030f881d0b07929a5000e56506044844500500419084030313092405040510f0240201400a018071010f14042c00100351000d8029144ad02c10f005c00301d0203503550020030035500c003007801c404290110100c0c401303410000040c102e080030144c18001c0104082c0c1c00815100c0383d030002c8801040898400507850002d05940302034400c0101e015040102c0041081e484c00c04561003034408100c0740d91598001c03038076101c9034014007072402000e90041000c24188080406030385070080031041959016600d040845030564821000320381c010041066003207550a0405580400c0803140380307071030000c0e520f102105000401c000c3c0b04441140c07501024845816400c040040c000d4000c0004945070304002d45c00e41c200b484118010b101c1c0125000195104405030b0f01120307490741f6440d40d1503040c00000040248002c00380410400311030100340150751304000d05601203004401811a007030030340c00010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 132999919 1250 132998669 132998707
    0xc040e1c021203040609060902180910020403020306160e030312240d0b04030203090a0f090c050f03011403030904050a140a020a1d060f0c0708010c02060f0403050d0e06010b 76
    0x41550015a100840369040b030b422070307511a0707120400203106c41e50b0749044c000801074100082d40200c03021458040c029503450a05001d802000100d0b6600714200003a17805901c01e50200a400d6001079002c00c09401000140d140c0080b40c03810040b0385c440c129404241795410503003208041c082c0c0c031028040b0003035081c0b05081441c00e01090754062000c040d00030444030703450007100a0282036140001800c0c58803d0081c1e5071881c2c0001e00ca52106562044000124107003409036584480c64001c020002030702030022030300791258502440741035a01c0d06444945a0461201d0150903001c10480700d0056030311842034612644840340c0000350070051104800c0c0111000745004a03030780c81007100e0190941c001c10301391071300e0038403181003050110045c01240a0303008480c43c4007007541001c0f868101c0c82101007030100907142d88400800020b402020200d0b9640070555005005a1072000801e0200740700750000c02072000f002c080851000d5040940c98944082680000340050000c0742d0140400041c140c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 133001169 1250 132999919 132999973
    0x601140f040e0d020d2a0b040309050901060e03100605010806090c04030b1303110d020303150303070c082404020a0603020a020f0a0b100e010b03070e0a0905040c060909020a08010e090c040e 83
    0x421a08006541e0603081c2c82c280d13110140207c050000064101481002800c010b000c002d03000120f556523a0074040c041c49904020248240141a040006c2e1100c5101300e0084a10580d101090b036211350040c0304801d04c0281c509010040704000103c003241c1c0703160501d07004032082c0084441c4007400c0e0a0041c194040ea07101901141c01c85614044110b9002059030340003516252250f01102c44040064038604c03c00f030f402004412401d500158820000c0b822140405112900400e412086140824100e208880080d0b0011070b05c001446540d00c0795010f00b480650900442d5081590343c201c852070302040c0c001c02c0320f000320007100304105040004201401811010102c01c1107504125003074049000c01041c0f082080311b08070b441c549995030801268020071640d0380802070750520342426840e200c402d00408010804006c0c00140510080c822190f160105545080d0701e6400d0044800c15200084c003040704c0b40c440c1514110f03443c3e50341e11450900d840240010480b2030006507804481c1c0c0d40744040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 133002419 1250 133001169 133001207
    0x10f0b0306030d05030601030e1606140310030305130308070b070306170c0d0512040905070306050109051c060608030406080f0603150f06180114030f0601140f040e0d020d 75
    0x601c841034900040301070006205050290b1030f44c0d1030000485c0142503281c0400c286129260822609500506c0c1d64000c3ea842d07a580d01855001039181c1005512007a50000134034105041c040012910078805070003a4a034141280301082c0e80c0f034980b06003136000000300b80d8004000744184103c640d054403514004040800b2465078103088603a00e0754071040b10b0861340d4014001160400200b003414021441240c001c0c00d213064a990b00c424240c4c0040c2000c861010100786401d002050340c0d130150880c1822078800a00c82c6c14228401120510b05100500d021506c0d682c84500c042960a0300b400908003401a917035800b1058079102612848040f00581401e00a400c01306044440b204581807050f4825501454403419403900000b00702016006039050340d980f100080081030115407400303403181402084040b11895064940302c191208021b1160b06407003d40e0552110141c20201262100468001e00015550000302a01c03428003940304501740058020720080c9080039040741c15006441d0320020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 133003669 1250 133002419 133002421
    0xc020105010626271c0804150b1504080102070303060f030b0c0a050d090308060f03011109100e03010603060b090c03150d060e010e07061103090d0201030e03070602030c03010f0b03 79
    0xe003610019020f0700d81e12400610f0800181c05030018941804400e1030414980c0440d5441c0780d01c142c1c4500c10464107805100000004407851841148101c0c061900701c0c2d8500d07242021210307040c00030105680001d80041020080886545489010300000c280320300001d6500c90315072500808441d000e820910303400071003100c14000f01d180541c82c540d02901d500c0c000c0e55250452034054070240120150007901c0350820100d04c0815034448103850040a0540c0c0741c0e40c40001d8241014243c0302da1580d00b98041009100800b100e01e800070300405170b200f040c00c0004241d00d0340c201003400e4452030f030010348241c2e031030364110b81c85400c1c40241554802000b110789415401d002406003103a81c1002110703803250252101590a2004543c006105625560020096203411002150303c84d0300c0ca201c0c0700e0119500d40c0181c0d80c0c040780807040390784c4940300802c1b80e00c0503182980198010143c54403241d41c00c0c482032100e500098814070003980186640000c1c9522585445c4400c4010200340d044400d120400b80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 133004919 1250 133003669 133003697
    0x102131a040e04050a06090c060e0d03120b01090e0108030a08100b030a09110d03020d0807020f061b0f0d1505040603081b0c060409050402090a0e030706020a03060e09010c0201050106 80
    0xc000d880580301d01940b0403409840d01d05200e07103418a042c5000c0c01c440d107884c0c000c004120074000c018084030400e4848007445000c420130052048112500078011900c126800203154080ea401020119414184410705030349074840080c070380302d0980120006034000a0038540e6a03401000c2d055000343e101c02d2000c00380b814541d040045003c060320f00315100b0384500e40c240400c84280320b008442c5070040d1108840c0c01017410300135940c255404c02030000c9903528004c03a002620101c1c1c000030046060008001c81d0311011075200c5108900e40c0200311600080c0700003c1e039407403241c0041c12801d0481601041c5103000014942c2c000f481a40700c1d611891900c038081001901100c181c903100d40c00280c03109842c080c1d03803403074a04133144084616403000c0009000320341e8001c0c942c80346005a00980700e8003040d84e2044110000c903003130210164001e600a00214002411035001030241850603d0007090040d80da40946000640c140c1d00c901e100d9460307070200b41035540d0901c605030041146240c8158494484 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 133006169 1250 133004919 133004969
    0xd090c15020a1401020f0f070308010b090f060c0c0a031202070602210904090206030a0c030f09030206010e041e0b0105032505010e01050f030f0612030a0e09060d0b0405010213 77
    0x2100c0040121600e4040002e400f2020b5060b10320345c0f90002c020035a900860065000300758481d51046000c01d800703100100300c80107081d0607500e43e480050181400c6045080410043e908401440c000c01c0c03084c6107841c0350640380c4280003801584034200d446008075070600003a08110f980d4201c07500315401000540404c0c1c00001c981011910402503987e0741e04072540102d0094030400001a40060001052008e44812940a614000c0325035a04114161420031004c0580708100d40280040c0c0c0f00e007005002c641c075002070454000340700700c00c8410000c0d210103403104003880e88a02610560541c01c01040716003000e000c0a1500d000100d482c851414114034500e003041268003c59042202d040c0b00c81009900072022180307005404450300d40c40f880c0801d2a0041d465084031018003821840100c4205035000006a41c5084850303105c0c918000c810384c00b44000d00034014a440c1c0c0c006401c031013120104c0d00c910241405030380100001340c1e480c0010300420160481c503501c032038200501c900d0301982c80ca050f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 133007419 1250 133006169 133006183
    0x61509040204050408070c1503060f0806010b0306180403020303060f03190b07030905011b02010e12030c13050409050d030c09080c0402030403030b060d02040311010504060c110a09020d090c1502 85
    0x104942c00100303034a9a00304045140580d030b00c000c00410f44034001091040000c0e14031202c54101d5501801500d40f0740c0030100f5000424402d168860307210700010f0102112400242d6070010000c1e1070608035042c44405c0084100c4183c0301070380540c20010603c415400c200b802024001c4059008003082d141c941d0800140101d0348034050700e41032110022601e603a100780c0041e040c171074010000340b000c502400000300007041298141c5e405907103042540f0711041004240c0301d80960121407041d0656440c401c1034001b1f980003080303404000c03604000c003040640d114410004824058001002800e10005015045031703c01415041440714544c020031a08000055a41540605643c05178582e207032407800b58054040c2000f0b19500000100e44200c020045038060021280590440303071190010390015203042c400c038090342000955641d40c603408155140d4880e050200050a1038070324a646682c0c035801c0382c00c920740c9a000d198880400200b0300134000091005840c41c1c000b1500d102d901140040d6072612 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 133008669 1250 133007419 133007423
    0xc0b0708090f010905160801050f1504020d0e010209120303010f0603090f050703080a020d09050603041e0c1e1403060402091b030103080705210a030f0603020a0e040506150904 77
    0x80c1000000c59589050250700180034030356000348004580ca107081502c1d560604020301c04c400c1502000240c03071b8414011135000d071610398591503a948a55560591b0058141d100710b0700305070204541596104648142400c0c0d401030f900058481941c0c1040080d40e0305a50201d4281e60310600041c028980d06c403056200700c03400d50400060319029481d210700d1200c3c0d042000781050103815000414010014000d20b04075480350300b62002481d0030700b800c0d180c0386141d02845802c01410310005000981c401011001160214690155004180d8400c484c0c07002c1a00440e1500e109514012104444080101c0103041840100c08074100c220f00841c1d40c9040003800648101400404104841284025400e05c216041c41c0c4940e0f035a100e0405000030b85c0400c50480b11841000922518081902d461040e0010074800c0185000c0c038000c0110041c00c003003094404519074581000005030f45110314103008108030b0784143d00c1172429081060914130300130005400004020a0035900d59240359290381e110b6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 133009919 1250 133008669 133008677
    0xf0102010908041e08030a050307020607110c010804031205100501090906030b0c0319050106050703080109200c12041205010b010c0b060402130503010c030603050f07030804090c032306010e010c0b07 87
    0x104154004c80c00303c41c0c0343c0c0601800d0000080051285a005000350710032140c40d0200c8070030381c4170250100c444000e00000000d081c2c0ac80001d10000c0e62003503040ca500705000e881c1c4240703407001078a0004d04036001510b100034014500c010070401560085041c8004250380c80342009400e2454407009840403004040c040040c20000c00541001d00a0f6014031079840080750070048ea6071110700141007940582030903030204051000000d0b40c000103000c0e030000b10700c00503040c0800d45504461140b0303640142c68440c805008114400045241c40300207040207140d803031604013141d83c2e942016403c6648202c01c081c108041e0400100100348803030400da400c403200341ea0059503140b0107460200303803080d9900f0095240d400e00311559542c40c2c0c15040b04007038034081c1040d16900c900800f002c07903482005200c0109110418482004610341550184410384028140450700c11841c12412083c4401e0b460b032202940103190034405203581c000354064250300d0a0030900d040c40140c0d1680740741c440004190360100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 133011169 1250 133009919 133009949
    0xf08060a06050301150c0507030303050a050114010c021207080d0e0405070807050a0e03010908030103150608072312070e01140603010609050d060f02030c0a1202091c08040b03040b01050f010201090804 88
    0x39072284c000104110f403c0806d23202c0c01d41d200d1400801601003500c10007041170900c400800c7c40080d0303083c07a2000f2041611040031008540c0d0038001d940301c917207103219800d01511100041c03684003404080d90700440c0e980c0780e040144400c0104000c0751009400e450400801c20b08101c0a55007120441305e40c024182001e9004a01120010b40502213518000703020100c04030000080007810040290000f44c0207105101c000d0301c400080b0340e00d031041d128000c03401c88181040c075071000340b5400440322001c0103070062108020107841c0a140081a6100542d604c141c0001040b8100d200e07903002a60100c1128081c0c915407411400074010b545500901e8400c1d80110040820000903030b10022298001d05400c0d51a481c2a030b1240c503017600014074a202041c0040241e0300a94541d2007141c0300d1040003886902d007644d600c205c1210103a44020211f901350340812004c640005020f001d0352040344943706d00c0c8465030400382882000391742c4155440c156030401640f4400184404265425200720107040542 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 133012419 1250 133011169 133011209
    0x41a0a120602190f020c100906050705010209120a140606060403060c031b030b0f010311032205060408030a180c06030e01020714060901050709120b070507120f08060a06050301 77
    0xb40f0a84000303078445160910200c03c90f42c0c1000d0b803000c00c180d00c0c0e029281d50b8240c100500c00c01d94944901c0710005002c020043c010140150f001e020340f40e00600005050241070380120741410210300050480764000b80c0c00c0c0080150300407600540b82c484201600050902e4004500103001f14000100340381d441c0da2950041c107100303034829481405041e1510045600c03058000d0001c220b070b115418000c865102d42c03c0b801d5400b0380100780804034027588286c034541d210100b103e108a2240d0369900b0000c80b00300840b011460800400780503074003400c0d5640d6242010b070514003c0761000805a1b0142c0840542c51300420000c00d46401180c1c03107414003040c0d2090169284e0700911440800404011150001001d003140000e1800e01c503209040c0208a9501c03104016540d02205200b03154a000c0001090400294013410580e044400742c10300e5418001950b0340c040d90034803c448004c0000300100408500190b01140740c0303030000780584510a007141805402841c500c014000c00c55034118000710703e51 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 133013669 1250 133012419 133012421
    0x712020603062d090109060605030a021612090e010504141609120302030301090f0209100c0201030b0a0306140c340506010806010e01091b0f0903150b041a0a1206 71
    0x1124440e010714040c0b185004800040c100703140c2c00c91a40204c0d046400441d40348114400c600079120f10b034983e903085580c0c10070107101940c40f00c01d02021144800c0c0c5920002109041c000c0080e07250350b20750986690500190600c042c20581c82103201d5824a2190544d07043d0081c50650000090310030490309010643c4261907a180e950312543c5400c1065a903141130550100c0514141c4444280c02e1000c20b254444038070580c01a00243d07548800c102e0f10b8802c8841c090309107504524418100800c1d0000c0850020300a055180d2042d40c000b6214210172a4030f032002820181d00103003003405241802610354800c2086100c0079110300c003501c460500c2c810f22103207581c00001a6a400303000c58940391307100c20049844490a200350725200083c0030000c5400405401214801805800d80c244034698425045034101100562030062101124001c8042100780e000c8503440c49079400b020440c5030100b014081205c40b00d150700c0b2240140301e0301e640d08036600e0510820446400c00ba0410365845e490030030034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 133014919 1250 133013669 133013689
    0x20a170a09051009031107150c1a183f0d020304050102090a08060c03070e010e0d0803190908090f0111060405070302010906020f150903070602071a09071202060306 72
    0x1030b1003445895441403d00b402508003400d407074420303901e1002c55440c44941d00d586490760300580941c2c0600302540404a13125444801010f13000f030348171504211598840c4d0b0b50402e0207a031401b1402c0b440d00030701610341004100c5210000e0b0308a00d03d60b1029124614920003d2207071411050990714444403904650000007501c1046009003403c559070300742450054000c1d480025854050100340c01c0025071004080b920720b1240026481e00fa1031503541007802c44810b00020303510b0f0f06010184125075421b880d104200c03420a881003401075a40e0400c01e0b00805a15040007a40d10400d00b4071080e140003401000c181d488034042515001e13800743e54040180c030303002104509020340e441340c8000c100c2405000650401102c2c002c0e01c07002d0b20307162103000407611003501d4100c0c1c426680c003140419805032207040c1c1d9030790b2010b2060242c03410310b8080e54402e0103907401400181c0e1900204000310340f0302c0c140003040a030407020810041094908e880c20417000e044403058064450b02002c80000e0bd45e440700e261344 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 133016169 1250 133014919 133014923
    0x1b0303090e100b0c150a02040305060105100f0f110d09091d07150c0222060b0909040b0606090315160c05060403030209010c060c020d1206140603060406030c060c0510020a170a09 78
    0xd17803803c1c501802c3d03500083d00148000d44151140000000d180d00384102b8410035511155144524981c00032000d03191b000b0005070040c01c00c5002071181111040a03c460950070390140da403141020324000e10304069038441c00c000c2140d00c2d0280002c10b000da90000d600c3c4102c03440d03580b03640c1112060300c0041d00c0c40c80200324083d4000b07208140707500400c0000c451045118160b0141045840d4540d03541c0e82c7c0d9406001041034100c2a0a0041004102c803017601c541d10200082c034682c94188560080307070a1241c1403c13032084003000c6400f80b0016102c0e0031416001c1424a1422032120388540d00c48641e1200c0113000a410705038001042c100b9039111f880715140080d04032405002c020b122103802540c40107000c40600c0009c03146402c103440c80c02180980e1040704ca61001c14000419554208085030340042c0c41c10b07521641d102800400600d00c21400c00c010440c540f690f504a00941c03c0c61828041e80f0041007501d14410415500d40ea600305900314002404200001c0b040c0d034900e10600c00810f1070b0600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 133017419 1250 133016169 133016203
    0x907080102030c04170127050f2a1801061202041508010305060a0504152d0c021e1002070503070c03080d060b13140a031b0303090e100b0c 61
    0x10003400c07803d060010800c90b0101c0900030118a05040414201c034551141118800304c00a02142c40300035500071490014000c1c41504c0200c00d030800ca4a1400544450000344481981d03100245c50060f40169020342c0e0b002c0e075808550705240d110010003407005015400c140f20621581e050b496091742c0c10758014002466070b0b40e920070500200641030305000d00c42103619200b000001500034556005040c001d580c86004540d01c10755070303100742000c2c20321402101426110030301800c50341c100451900d5408464450300081c41c1400322002802c1c011a100d107113001031000315486095900010384001509a08072006858005520f00306080d0721800320090150591240701205000b100c90003840f4000000c001000b40030350303c0700c1a82c1d680c0181c01d5a0070701901035503010024881141d23154604030600414234800591a5580d102164502184010b000704e0501401e004140d00240074001621142c22009594544400005210031075401081405080424042100f201c1040300340c0c140909441 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 133018669 1250 133017419 133017421
    0x20402070c0b0307090f0501020a0c0302091306060f031119230402070b010806010609030804050d06020f030f0106030f02091e030f0106240309020102060f0606091e010909060f0905090708010203 85
    0x14000784400524007400346244451480010300d50f00015408a000b903010bc041c26440c0d103590204031048078004d003003404110001031042c00050700c61140310050100c090070740c1d0001d4103606110821400d00c810103070282100e41101e41400c61118413100407503018000c200030511080045540d8007581c201c000790018008a0500200620f064200e810f841c2440704035001a80c1c0c50340c0440d410a6a4031001c9c20086c1e00300014000307824140558880c1d1405000c001d0b00e4600010351404c400d0b070017102c0d1648840c411700018880f850f810f0265081c800c422040560a0444100004400c007515000d80e00355103001001c800b06a4500344400c5940c0e81441008205e420359602c042041d54160904460f8440f040700b0b1680d202c58081e1144440c215010781c01010981e880c0255441d40b840301a1000303600a0017400790740060b46c1c915481c0460741d04201c007840c103050310200c0003400300c00468105040e018203000782400903054024080040b00c01c0c4040205180d240c030b224031410424250024400c03940004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 133019919 1250 133018669 133018681
    0x61204020f060c0a060b03060c1e07051c08010e010b0d020903010e01050106110c030601080c010503130c0b0405090a05010b09010c0201030f0c05040f0e01080307060e030c01150828020402070c0b03 86
    0x407a40c1c80e2a2801903601b4002c5061020403d5181c40703045410003401c280c10702542c4030b022004070751145807800152102d0303e232650790b03150140340103107064600f4003600f40414000c0b099984080702500400c0684502c451079410a402e420050156082d034004442d8089800c0d03429980175009900c610110070001c008950310390400801c01c2c800764008156a02c500d80050040c0d0900060b1281220b010320b0252840740c0b02d0b03000444a41d070029100c17016804180c021000884d03000b41c3c141c3d0041202e000c03899602c0340340c10207004c0281c200a01021015142c240100445044181151400351007481e01e019480c01b140300680080c400841641c5105144c04640d10b03405401034000c005440110980d49581c1c0e40e02c0fa01c44020250034002e0009941091003132900040c0e5581045001100c1d600580b07062031325841803182120f591300c4049035000c00c0c4460810142e01c05101c1c0f815103c0103042d141c1c0100100e0310080340c41c404401002030183d07900099420901c1010404480a0602500ca03030ba6282022 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 133021169 1250 133019919 133019923
    0x50a02030105031b060406080c0708030c04150c0b0606030a09060203010306022511011202040e09061501020d1d0406030f03030507020705120606012d091a09061204020f060c 76
    0x2d00880d4040d10800d003480c61681c15050300780c40060741c01030519140071b050101c1140d40b000b010703054240c004000e008400000b020440914403405d004c002003500c55241c110305c42c0c501228540701c0350038800d0982211011031700c24121982d01c0b22054907601c3e900d84544216500030038240b48042c00c031074800310001c000c000b00d60300102408105081400889901c0c0008032103000090500145105222000d000d01940204082c1c000016449001400c09680f00b0b03c01d0310311403080303410a01c241c000104000f030803030500041d880030308004c1c030051000b0030041e2070190001010860303034441e84420554596043c2e8444d00800003071a8072030800c05440400345006009000c0c15107c0e0000340c011680e001c929404d00340c0381d001c211a40c0d07100a01d410703243c0400640b00d543d0000040b03143c0c0300e861245c0144840d4011304c07a803c1102d203a41c520004501d070410701110704500d5400030306041000c011084460780e6503004c0d240341c55066095540c660300c40f4400034000b800724a44690308483c2c0071031070f0b80403d040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 133022419 1250 133021169 133021171
    0x602060a1d0d08041a0609151302030711100e030406030b060408191406040b0a1a030d050c01060f050901150903060f02030a050f070816090503030c03071a190209060d050a0203 77
    0x4219082030983e1031709a0503000610040702d159401466a10025052102c003043c020820b810161149401050300e89411003a40d1040b1a0303c80455080180510114401c10060000e0300c050b080c00c0180005944c4550703264401c610071132040684a00740300e0302030b030b5400040360001c00c07200701152040d16803410784140640301c11409840342c0c4c400140700c000b2040c01040c201c0c800c3d984013403401203650340c1032041c00003000380050302400c21100301c0d80750107551410802c1d007003145820345a454650b4010540c09080d42c00642001d1112400d000d41040140c07100341038141511100580d0700c0b0005403000c8119a04051580080c203e5420590480070400d210b40c0118000e1524071001c0c0102d540e10943c4005810094400d0070010b0800700002c0d01c61203480c19a102101c02c0d526040381c0f4541d5031800203103103420450224440382c2000404508100c80031181120095108082d09820701c2c21802030380b0011040360301c0c00310703154001038105603039600d00003107410070704251401304890b0400720541002508 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 133023669 1250 133022419 133022423
    0x30a140c030a021c030b0a0e2e1517180a1703060a090510030206030901060f17010c0813030807050c0313030b0a33120303020a03060b040602060a1d0d0804 68
    0x1350060340850310714401c2c040c41084030006808914528645907205407040d200030404290220b00ca600c4040160704040b4143c0500b010340248542c0300d0900340e000b680341420018210910590321044007a03041d55000096014862060501d840b403454243c440c10f242a5450007003619407084814100d018015001e0b60048100f510701140658650311400e0850b94180c0340c90f4040c4000f09400c00062500d03030002c5600030320326400401d00035501c40c01d5a84c200000e800c41d000d20300c8a1178621095a200344101e0010500d245009035160410303400c12000841a20405801c0000101c0007500035400340c001c03202c0400340d900c1140d44e0b07001e650404503292825400110741c040c15040118204507854014005d07007201c0b92200980f0940c1e0060002180410101415600004200c0020702c02c00007980041300b01d8003039140940d5900c5000380080c01c48526402290078840c2c2403005015855002840c84d81c0502c10000004e50003029656410b408041002c140c0c0a610038460954180b40e4440800790040f4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 133024919 1250 133023669 133023703
    0xd0803072303070e0d0303230a0b03010b0a090504030318050c04050f16050702151303140601030b07051621030e030a020309100e0405040609020108090a0203030a140c030a02 76
    0x60380080c10310760745120654007040041e00035200000b031803411240050550303200717040c00100130029000c1c851b81501040351401080d0003c00400524403894007410041a000714000c1000814000004003041c03401d000d8048580e5030745001504142c06a4080f02c0c50b045c0300c885480302e0100c0b91270039695442c0d510004902031402c0c1703000704641405c0003100c24000c0328020140580341d801250704a0b00c540040340240e0b80240b01c4444469500d00b82d200411024000d19429440c090550802c400c1c82c8128982445032076124070010000309003070805181e080700851a0140d03442240d52407241ba14100c816010307102c20904a140031503500010910071784440e00ba181880002208101c55899020720321241c00580c000700180025440c0501c450944100c1609090302401c1240c030124088070011602160426030700c10000d0f0966800c0418540c1c09a043c10041270918829030100303440e4001c40201d0024006000b64220302d010012041c2d4031388040c4002202c0e100c40101c8002596071500050703840e600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 133026169 1250 133024919 133024967
    0x60506070821040c050d0302150c0403050d0f0203040504050402060d0c050a020705120616050d06030318150c11060405090420090403050307050f09030a06062315090d080307 76
    0x20b604030019980c07065800007010040d03e0f14100511561960305182142107004036010400280100a1654003940c0701d04522510f80e800c5142443c41c12496400d21018810380c0c05030381e41400d03800002c540540d48280c2c0c0c049443d460340d02c045000c0d40200b0341c0d0000e01a0074289081086039004002c1c0007e48c1c0d9507822075100716a56024000b149110404c091001e82100c0b0000f010144031074000310582181c5c4c40d296141c180000101c2045034400e400c00c8000a9085640c0351040e299030886402410505603034601c540c44400700584080820f000c0104115a09440e41d1496a02d010a80d40140000f520103050b81ca0580b81c041c0505091100c03040305030070302e86100082810301010f250300c00e43d4151541c80c910f0f00c80c2c8c0d030b0a440035001200403200000b0308010707400c2c9a0710240700c12503005200e28804161181041d09480c1c01c1c400049c04901c0f007a12030700d25007142e0364440300b211105513000400c4c40d40e81c01c89100400c60144801c140900307030000001c01e105c48194030031503252045002070009000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 133027419 1250 133026169 133026217
    0x10c08010f0e0f0915070504030c0b0c0a0f020a15090807150f081021150e070b090f0409080a020d180e06120124091103190605060708 59
    0x2080031076000d2100d00da20540c00041849281512841c3c020803100100d850042d10740012500c2c0402c125803141c00240041001c00030000000b1000025187c034846c00c0341005421201d013507891000b00d10117003200ba0710341d10160540d1654007a8601510b48900101035541c1106005090142d051080207420b102700440028014081051a01d007282d041d42c510400e200d0701c0310100d6030024090103012103460340f43d00015000103034000c480301007449510109041c01141c14020b00001c004403550012500b403001074419181c0228940040e603600c6a0310503214614000426030241024507042d40007450603e03007000f03000ba0030019042902c0fa80d03086a22000d0386840c00c90706254050103d441400c0170040501001c140d0f40d4580743e001d140585190300c07910300084501d081d9a09a959810360103120600052004240ca24150240c4400c0501f40120701075070380d0451042c84010400b1040900c1c072111480c495040d90442001400c00074080342d122906410404041d5006007030146502200720074103c6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 133028669 1250 133027419 133027439
    0x1020a12110405090a0f0603110f030c01051c0e01062601020901080a09061811040b01020309030a060b1914090a09020a06050a0c0b011d01060503010b04090b0604030b09010c0801 78
    0x7046030100180282060b1406003400324404003e41070b10025503d40c1210512502903204030f030f00445c010008019050503000501c8201e070203410502c0c0c040c0c1c004d1003050501e640c021003194000c240060b543d442d002d2081007907200820040200e00a154249440000c0c202c0400100d180014108000c50001801c81080f5600300d200754040b480c00305a082d40040d9901000d0f80c8000d00319406154007107028130404a00d810b0301640a1412034012034109000c7c0c006080c18070a03001005001e0000710b2a05500c4400680c1e90340c0c040700c0061085403260900c82c03141d20342e1414121880c2100a00c1600c082e00c4280b06440d201905946038052507514000031011880d6000e03564040d40c000d0091001c090821004807420750106c0703414000d2103441044a000aa5071511942c000d151403e0600391702c80c428040100c00c000c060b40003000f040703010300051060a600718201c4049440007140000c01d41d40340400b140745409039a0026011751541d004002c00d003101034014204d480c109545071300c403983c4c0310270f4020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 133029919 1250 133028669 133028681
    0x705071401022a0f01030b04020a033606021b12030403020c0604060c0b06060412050f120c07062109030509101d090c09040903091805011a03040c0803030901020a12 72
    0x50b030f0711105005000d08508120b80300b03080c100810302d404902040030310007050517031f030000b21900d002a5440705580984010071000c80c2e08510118040407030642d03d04840302200525001c0501119800160001d2000c65641d91222403698003003565681007251900001e507410480b003c1d4054050501214401e1030304800311421380b4010703100c00044041940718005540001801c48d6000384040001080c03c903e560190f000c5c0521660007401120044020203003001c02d101d056141035002841004042600031500300c0c1a01c5a0b032811512007416a86000424440c00078001c080c503180c481004241a849402000007201c1990481001c071783c424001c882c40719590302c2c1110134914000c014403092030000c07451500a60b15104c41810911a2000202107540c001c004902007040030718104032514002200d5036885600341e00810031585071442526102d00c0303e00b000300c000c400010010b030810240440039405843c00c0c0381102c0d22440c0c505d400718000e51006114802003024004068170001d4980901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 133031169 1250 133029919 133029973
    0x31209061012060609020309012f070209070507020402130501030c0801180e070302100801030506010b0f0301030b0601020114010e011811040b03040507080d020c0103050f070903031103070507140102 87
    0x105001803500d10070b520401041c5004980090301c451000426030035600285000301c10020002a000c030100070041020804030b40e2456540b00c0008518044004100a503081d0f13540584501a82d60b50310001101c15116401c00203601034030200d04220064035003045102500c1082c0c178108590016442e0a071881c82c03091042c2440541c04bc1800351098503d49c12081c4030101d44030455504070340302d40c0024140311262040c0e100107032140300100140041081140d0041c82408040e92901c2e0701d407110300e4070310711050001400f0004401d0105600364802d600c00140c9800d03230340c0c034044156145c2000d81903192081c480c181802109880d0041504014410200037445020b401890140780c102070484a8200030400d48450056407000106154148440c0d0400507250b80544503100e1200b0024080b01c5024121510000009007007211081e003252503030061780d4140c144100c045208107c4a45103210741c0700c00030a98002c620001460344201101c0820000d0b003602030b50200355003a0140000c217840c107000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 133032419 1250 133031169 133031191
    0x10509040b06010e0411070812010b0a14180904050109170a0207050d030e15090112020a0e150c03070f02040b010314070c0602040314100b15270a060203120906 70
    0x41076070b0358080c0c103400c00d41c0f101c080d1002c5200aa5001d91549507000068183c03042c0400052010602c654503079582c1c050302800ba1500d040402001e001007500034440d8425104407400600d2040700041d071245150380000c01030000d08a0700d01403400368082c0100700d030b0450741c4085010410181c2d02d8000c040c1c42c00c0e48a00d41c002e02156207804100704070b050200c4416010b000f00c500da450f22940b69611555561502d4000903503a5017000000100055150340382c400f291403041c0b04a403001e030340c4485803400360130044940701d04103502010b240b80107209125001c165488001095010000c00590525826000702c400304000c054035401541584e280c1103800c280001d04800041401e030140c0406203c0c0c2d4017802d4018101034580e555040d20850403010720805070b20407041141038010f24001c13115054000d50f43e21041c0380840009140c14041e9482c407802c0110802800e006216403c0c510100d00710703008201c400083c4e44c030b40000e504c0781d120403c00240e03001070400207103651400054003070042241d042 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 133033669 1250 133032419 133032421
    0x1811160204050c0f1b1501060512060316090f060b040311010f020c042a0c080307030f0f050a060609080c0607060209030f0f07060906031a0409020a0f031a010509040b 73
    0x400c00009000c02050f141075641c0030701c542074030131041d800078182008080368000c15003641c8050107460002403142c020b0160003200010b10125520a00b9030700194226407005009440b2180003074140020601e440c1c0d01a4144440060082442d4002d25418401000c00308015a00d460300d800c158407483c00090900c140350b030942d6070654820030000c00c0702c101d40c3c81070b0703407000b07480100140503660131082c81700140149484d920859100c280340e44040150602300b130a60286941d403440d019010044c1102c1c02e055840d050540540b01c19040750114000c5c860703041051389005c4110340c00a2819002c0d010000e0800c9201081e504400034001c04209070042c485410810166200300c0a0360041d1102d54050240d1001d2805010041051042d02072050025003c11401d0510080c001040d41d0b12020425041140d505032018040021001c40345003514040b41d140010700100d25100c00f1640802d240c00a618400000c0c000d005924501032403100c00031b00314a0b41c3e9a42000050034080c0c8001c0d0803030307050320 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 133034919 1250 133033669 133033673
    0x506070305090a17010f0c05130302040509032b0c02150112020103090b0711120a08270607030b0a09020702013006030f0b06010306180507030213181116 67
    0x409050b4003400100342598454950b000359994201c0079003084410ba4403400684020f55450080d160340b40040d00c1c0042c1420404c100280c14015184000b030701039507844d008507819503002d104940341200d420b03030011482c10303a00260580102440005210851601020280c054404514040b003c03001c401344400700d03401e02d0700c2108181c41c5100200e060503900c44c0c3d600002664014400d200b00700a40f101042c00450342c42e080d080074403800024010207000c200998209801c14486038002101c030300029164040b1060f102d0586441900210b5030b44079810800413141c2d0305800c01c02074410182d502c2da080580c0c4455100c16802807020090216440c04a26401540701c945504040400410b105400380c402c044000111201c40e0420f54501c6400400c1d2002d00000c0944603030040c030300386000c11216182600c0c4503022550420096641602c990114407198400c0c0c0540e82c445142c400f000404640e141941202020083d000200e218280551340e6500356400b015540c0d41c014246000c441d11050b0703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 133036169 1250 133034919 133034927
    0x303050a050309030d0e030702130b10080402030a050610150305011508040c031707200a0e04030c120503070314010605030a020f190804050f010908070b0405011404061d060105060703 80
    0xf00280342c144010301c0001d50300a0745029041381600b17440301843e43d4114500501000402a4903001300711800c0160419958480b07141020f2542c134149000103060300c031403001901700701741c040c0007602c140f003000144543c02c50003050060450b0450300f1004580c070000101038098030000d2049041d5440c0050011004c41e008043d4158802d100383c64403050144c80342c1e1560390320140c05a484d960008049600801c00102158000c0015105c10141c0c0c0e03044030000c0044e80c1005240521440c034a040350104040500992014120a6000e01c840c0300b80000790b0001041c60300200d804000003414407810121a60b1840d850354140d4125035259451591940f031001c3c041e43c0710740d5460150390b1081003821100310040401046292440c0d031090001e0803d41841451b00d4100608608903074500319040c0d0015000508480c81320340d00410500ea255640e00b003e5004150080c034000c0095003140030841000b180b680003c00c0d00d0b0100c00c7d1240b070201440501640c4207070900800b81c005000300800c4c07001c2805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 133037419 1250 133036169 133036171
    0xf02160828120b060c0a0303050907050303090a0306231e0a0903080f0606040308190314010e0403031d0f0a03020d021b0603090c0a06030209010e0103090209040605090f010908090907090303050a0503 87
    0x40a0080d81c5131981000720b01e807406c0850001a80041c1c1e482e014815481400d001c0790b002428100c00440c101000717040001c00c0300911784001801c8039079410924040c41001400a07100010800e40c5049518100c0320700c000c0307554103c04628104a408001544e008078610034031074602d40696600c5e145648030000701c05034110142000754442002d01001000505d464000c3c807c20340002156001007400f008045c040c0d030240200390604a01c104014004003404500095000342c240c5070108000b2a11254004495a9046180710500034110540b200400c0001e403800c02e584242e007262442c41b4210000c90310b034461640a89441c00081d4108005403901c0805180c0004a1806071120030031050002041d0700301540c03010300800c2d00428a41110f41e005501001c0c0c1c10400c0c02d0074041910300794000b074840b03140200010031940ea1080420001c2c0c8041040318590040343c0b00800555540341460324041e040000d0591041000100003810188140510811640d240e220541000001d080c1a926030300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 133038669 1250 133037419 133037441
    0x30307030c0510140f0c09060c071703030106140703030912030221061305040507090915060603180f050a050d0903020f0609030303191113140f01120f0216082812 71
    0x14003006034250703150350049c0a441a42c40080040c2454030055401150000c820201c49400c1400100032031600640d0f41003030100042041796403401a8601a0024200d089020348407221509681295580560080080d80c03071011460f245801003051044035088112900c030340107900b03506a500000566040250058030a0301a00d207104d865081d0348003110450002a80c5130310040b070079108030591610900c8060005031500384581c83c0203030759078001c41d05558002030166810061080c10701006101d04209540e1080a40300d10440320301004050a441f40020b901c6060070089800c01d0745401d00440d40d600101030044c5086907901081c5860b0a80a08100020b268960400d418441c0d141001030100708801021505070a0a2240348450031515200407409408000c005aa1503a0007514180300346c7c44862001c103210100b000070311302a0180e6501001c3c41042600c1d00802c01c0b0043c40903086600100044a0660400c00e011001d004002804040440c11980c84503450401a40003808004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 133039919 1250 133038669 133038691
    0x606050901030c270315150303050a020a0b09060105030c120604110d05010f14090a032c0409050a050f030a0e0f040612060b240f0d0b030307030c0510140f 68
    0x400480d001a44c0c0440525100f084581c0340040c01003000d828094140d120b00e0080c00c100c2014018805100254140400390178000d0106034540e90f24030811008040c107610283d01070b254108086810383e030340000c0c09420704c640211400d160031030a04a41d59542c82c41c00d03070014030b015111a00c984600794201203085030803886500f140d20216809024100804030200ca0000b80000001d04000e0345200160400480f50081c103002008260321882c0d50101d032001c1031a1100c2e5080d02d000001642d002c00e50529086800d110960013404004148141070031301507810385031840802c41907903131288103e009480128681c4440502da80c2020000300c010145c1c041c100041d642e40307480790b680c0180c101c42c074204c41c2c42d900da4446900c1e0b401c016030506940a41140f801022140c0303030590364140c0c002c0083c03483c0c4480012660510110341a004240310582c05410389a43d003065090043c040103516000b501c4038890003c1900c946030341403003070f40ca0802140d4600105a115840341030000d25001d40082114 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 133041169 1250 133039919 133039937
    0x18030d0b030c0607030509010806040b0303120601030627050c1e0c030d05010b0c10020405130b0d0c1701180c031212060f1a071101260103150f0606050901030c 70
    0x341c48140041040b45d000c1e031101341d01c0e00000400102500340007407010b8011030429101c2c0406403000021382d4006481404004242d942c0c40004030300070541d980c01032031401c0140540020041d20021041c00312080b05905002d69601c8039407030422449401c042c48200c071100b80100f100c9615402c0a4808100c051080d0707450030088090300c10644c0d10a07002400030041c0020400007003281080361030401d08040c60294281481d02001071032008280d9000c00c401e6894821007030305952660083c2a80d19803026068101d182c1701d00c407200c00e5043e01b1440b08110345ca032109480304090036019841e60a94010586882d5904566030100603080c40340001c0180505020b9801072600c6a01580c00076005107070904092074640280503d03101d1400303800412150007040070788041100b0f4201c072040d255003820072226506070965038201001746141060300f001c042100100401c40a055401c22101214034280501181d6500c08000c46800d13104210114a0404c40c0c11155400fa412140607480941001c09034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 133042419 1250 133041169 133041193
    0x10821070b0f07030b030120180405090a0b01060c08030103080c030c0d2a0206120613020712030b01020f1c090306060b04031226060f0d030c02030618030d0b03 70
    0x21021041d50348500c000100c0d010840d0066151240b00c0721007804a0003070001c9a48c100d941001130428050740c03201d5050000c3c001d5180c0d142c49400c82c00196004c2d004214500c1c000c030220382c0f5580e12507000c0341c4a00e2040000951a4400c42036080419082421640340d43d1035603944482c0b0382c0c0030a8000304140070074040781c0c074140e00500c07a82c0c0074101e581d00c400521404213030306600c0c240680249800680c0724100544c000d621401c00703440251111510703880154031840d001500c1740241c41244080b00780001034106c208900c40d00e090340e6a514945050005c2c120000c01680c507091003800881e1158044104404402e940b0130f04581244102c0c10001032864503509d0315400c0e500136400c509224070b4002400c104200c003480c600a401d0909203010000014010040958044a4020f010003014240c01040340c0b680e84400400085070700034010400f0002d64980600450559030080c2d02c00d016001c001000380020222681821160303c0c0554503001501342508004c040c20610250148181640451 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 133043669 1250 133042419 133042433
    0x30305040b180913020108010b040b07020f06040e0112151e0b010e27060d0c030b0705090d11030d031127220f09030507080d0906050c071103030301082107 68
    0x30084d0071100007841240c5090002500e600c0c2c06a0051902e03003000c02c000c1000f10031a10a9420f099412140d10aa4500a400140140c00b458111240b5031022800005816810038a401c00a900c50b0540000d0030007a4200c0200712a20502c170158030200410326015070340e59070346c0b0440f2800f0050401200c007000c500c000c00c49400360198070480c8050000301c0c2958411121a91550040c0b04a4244680b69070716510390760340031468800101401c070007070007185985000300c1c01d403099104050510480b0500030706040c140ca11040540d64082d000d0b40c0180b8450501c207001395040742d1101c1c203100e494092801524a086540001c0c1a91040c001540c101c6481da120f04255180e07032481801d22188080a01c510001c49801892416040b880e25015100003a081401e503100540c000b060b403074840140508a40190003c1d0000500c01460441000307665040b1002a03c80c03e4060070088049003410b6061617903d1101703004a52641e070180840400c1e203089070b0080a04443e6212490f07041c901380e683c40d00d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 133044919 1250 133043669 133043671
    0x403151b02010b0306090c060913020906130303080907050609061b06040501051602030a0c03050a050903070b03100b030103151e06090606080f070e040b0f0d060b011404030305040b1809 81
    0x300041c1d44400c082e50061808000c466001710852014001c02e10704400050040d20a11074903900907803030004a0801c0d1802541a60b07200000602040c0d507480410f0001419060b1307901044000c9807084011a44840c800100c98056038800303043c82745420a510200401500621410b1355130710242d2845540c0700005000c140d00035849440042068285048810807a00701203076014110360007409203080c20343d8041e4107040d40c1034050400c29600c20481c001151903200319404643c15214004001801c0814140218464500804940220303502d8074080d04541c4001e100103072141e8400041222400b04540c400303007420503018080740040c64420150b10984819038000c2d1007680c5e407841d08100b61900000c2e403030741c40380301d0310304071806032078190b6000c0c0c85c0c0110101454090f9030f454040e01410b881c0c030f40140700080c1d40207000303410524072480c000780501441c0701410f00251390702180001000b014400c2e10240c1e6416152241894249406c1003c91b401a0200c02600cc0c441c0901e40641d854070141e503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 133046169 1250 133044919 133044971
    0x6070c021e060f071e050d030f1404030206070207050303070302100f090212010605090a05070c030309020a08010f02130603090c030314190206041a13020f1206180d0203030705040315 80
    0x20f6868040301c0c1001c141c2282c41400b8180030510001e070007000a1404615607400c81498100085c803c401c820f040402480d1100e4200c40000344401488181500003e4091143c01035900302c030b090b00d4855040c19202e0140010080c00360380010034001c20b0010641080500c5060000002010030a5400040021407035a00807442039541c0c4000b8001818074041042c2c0c1308007241418070090409a800400000d1803c41c0501055610b650402c215651030882d8001800e150000740940d5490081920080d4003940021101c030351841c00002e03042d8040c0c0a0400700c55009444410344514585003510317100480c00c1c0980e2992740410070007604008030000c030402c48027260300030000307442c1510341130000d8001540240031232444801042038040f5148220790301c02c0d5050701c6580c2200d0050010030b6800d0025290b4900380d015802c2040011060385026100540c5c0c0c130021070300b0034503070100c0503030300ca100540c1e5550005004200034004502c01c609290795030781a07844009002202d0345000040c41a050a00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 133047419 1250 133046169 133046197
    0x40207050f1c020c0306070c060207060f0213090509070e0705160c0306061404150603020c0a02030105011410050307140705030c0a12090b03090c0d02010c0606080a1406070c021e06 79
    0x480c180198104044c0102110a030020078050900b10000740482080e40001008a9000100c5408220309900a45800c80c000c000540d1201900c1040002c039030280c1c040d0240c40c03450a0b000030544e41c0001181d4044600f12046200d039074031032401c1126164003000e001e4016052429140c80051100418070740214001c8100041423401c061500c05040400c000040c81a0304014240d200c00030084405021504141001a40c405400c041641421000140654194070304400014a205004144600c8000c220342195145845240a540902007903034000c00041210380140505c200480040c42e0103400750781160b0410202080c4a440c04042500c1207500e98006c00c1050f8000b50800042d030b014000d4001c1c054294503000380070713540e034804621a0510800c0c44008207815a4003c0d103003404996007001c3c043c4130050b01c40e0003566031120659000c8444101c0b100c030510000c0320224440d40640106c0c0e82d504001d60098007001101c0b90010340c14030113130f2000c5802d102c2a030b4032034004048813110280 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 133048669 1250 133047419 133047463
    0x1c050109060506010e0a06030c020703140c01020601080313050103110408010207030f08010512030d05041103070909020102150103020d03270608150604052101180602070b07030614040207050f 84
    0x141c2482665406000d560501c50810038500582d95641268000d5a22a1500180b1614040c1c0100e18102d4103507c081c00088070030030903071030499001c281c00c0c040c4030b82038088508030b0342e03a0f201490b92403003541c14425800d000c00d903081c002988690010414080441d41440c2810b484054450032a03102000032404212540c5a0445c110b07001b0294500600c2d00312002010004500c040c1900c910031050f50100c210760390070000303040007440d680300d02d00c004000d0116500d0541f101880001012512001e902610440102c0d0400d07800354180c5906999020300240c4545c1d5640d035007642c051804200c0822100e5810481203c142c00d03014032070000340601c1e0b6550340107042c0f031720402c40d07001c940301d000600a1600308010b1042e03031203e290700c00492110614100c04160001005401000488180304030107001d20301d103030700740600707500640403903801194080300700d446400e029402c1360300d284078251181a08094007810ba2900785c1c05001d02074055019510059140c02da201c2c140071301c0c1c209100049440032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 133049919 1250 133048669 133048673
    0x1090b0705070b010e19151e08010b04150b07060b100c0317040b1b040e0c0307120c0f03020705012714060906060d0f1208010503011a100507021c050109 67
    0xc41d50f0360050640300e00f0101380f820084003c150410088085040381c0780c943c3c441030403d4059032500b20040c0078003480f1288104401100c0a01180244541e03140d56007840342040e0380c0e1620b445207503512041500c40f640ca080ca8101c14142d1394000e05402d544407940c0c3c080d10585911981071280f00308003e40d0300e003040a901813401414400038400001140800c00b0100700016107103181881c0c00c481c4121540c44088042244581c5503c50342c4c11040000c801e800c148140d2201d2480554002c030030380e0711990300440b850701c15a01184c04040352480011004c04843c024107000b03a0062120602400000c00c43c5018a40000301c41c116103072151500c00e4011407854140072002000b440c07402c0c8044060003003424035614282d91040043c1c07080340704215011305142000b901c969a00e14250b88984152144c070b443d40c0d409040207409102e454040c4d42040d207000c1640c640d41020059840e4010038030780b405540081c0071156030308060003c0340c000e0003598000c2c03d0200203030400b0180920540000c1a842d8484c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 133051169 1250 133049919 133049933
    0x604021309021b060906060108060a0807080303010e180a020603060613080c0301050c04030b04021306030501050a0e07050109030f0f050a08030c03091c0509011206051005090a0b0703170901090b070507 88
    0x1000c0f0301c8220740101c000d1142802000c100190810800d10300340441307449482c0000c0f1780901c0c40d80441c05c103204190001440e50750100107541250085a00711255548038150024114080411903855421682182d4014038004c0c0c061500140c02501c41810144042c103001d040502075084424540d0206190b50000c1c034090003000d5011f01c0811004c0c0c18989141d0303e4211901c00035200030300c20394025241c0d0304100e60390b9010000854210340248514246900f020000f070042d05151541e40c00790301000304d83c55002e0001001200c1c1c1c051040c000343c500c651100c207403003003200c0f40c00c4501d400341001c840c0200b900d403005140103e0300e4485d8540e032030a02040d03e600e400054864505201d0184a03103a0445410005513421003c0a00300131a00c8400c16400030010011500700661214113138800c035540c917600070b000e80680101611646102c80d140e02c200500b038000c80300020002003404041c01f0050340507020704c0390440350340c41c00403c5980d4250780b1000410000ca501000141011618105101c1c007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 133052419 1250 133051169 133051207
    0x1d01150f050a0612020f070f0203070b1e03090304050a1e08010c05030f06120105010f030201030510050312070309080d030b030c090919050a02030304091d0c011205060402130902 78
    0x8580c0006000c0d070715090128045030b640b4859032051040000461110b242c454048640c101d0480030301d607035602c0c0f06203002c40100c00c4030281640a071282c020040b541405060440d0010070107000c0201c0004210480d1038140d0303000514040441c0001d00001800c0c0e10341e85201005484c0f60346180340d8003038807071000c0c040003c80c65005106680c189540500743d540c02c08201ca421540400c0d01581555a40001c60340c1c0741700c06540c421b040d6203864000034200242c60101c0382075034800d98040c030054459400c00e0b41a12000c0c041c2c1c6a05402149610352008107034001080040e20034100340e10b4440d5180c1d00b980c1000c08a03140c10011075100c00000d12240703014448001c003500c086441010b2410064070315652014042440d056004994400c0c3c000d010003000b100800c194000d013140e80e140d07110056080601840c0c05e40c10040d00c2c10001c100c6085e4400b25010241c600180d40c0c182460080341e0300c0380043e040250007030303820070350811124486034a80d180c0b980203441c0b108000350f82d8441c003401200701410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 133053669 1250 133052419 133052429
    0x10c050a021c0801030803041110200c0a0b03130602030702330c1b070810050702150402010804060b030a1112070303080105040207030e121c140a030f1d0115 69
    0x91002c0300c0396140d03040301229040d41d40000340c554980e134642c0341410b218151000310340c1d4082020f144802d1031303952040d607810b40c800107000c0f000500000d24207030544e00d94041c1d1011341e001c3c4004030240107485808024507480410903e1380c00a0340c046499407012a441512000e0050f000203150350011a14804000200e01c4004001c400c800444032600402240c05000e0203242003002680044000c043c072000300440c14145c058861060741c849401da510541880c0b40203201e0f05000c00070710341900206800c103604203200e5000a0b02d642d550b004452030500104121034007595002c5151690b2804c118041801d4440c400c6406090001c40411404100c000002c9019921070340042c800a54002203c0c0d04507203064034003680b615258503042e140640c3d4556001d40001d0a407260030b400030300000d9150380230180040b02840d8924100d0044070800190307404040d44a0040201c046007030b10960000140740d2180c480080c000c0803041e90900410407502201e80b10343e4440c804260170552004000000308 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 133054919 1250 133053669 133053703
    0x10929010b03011401110111210f0121030903290c0a02031b01180b100801140f13080a0302180a0f030f0f06021605060a0905060a0b0d05010c050a02 65
    0x1d031424181d156010b91303007804d2604000700c010402001074000d412603192000606281d5407100044101c19001002c0e99403c00c141c8211040885e100c07024410300281600c4194001180002110342440c0540d404210704908100c01c01c04000046600e0302062145000404c202d51022461503454a885a0b03001e410140c0601c030400c100103546800001f120100d00c03d420725040703621083c0c6011030040510103060b9181c3c20741c68194a08000c11035615a10421600031000c0c07446807560421400c85000000c03400c4101041c17004685070f4403500708034550003000c4039180c084c4080d255031242419000804017a001c02c0e00891440c0001c0788684141c2e00b600001d441c030002140c50111903c4080c1d14a00c0041d204c0c1541e100b5410070300103a040c948040a0300008107540d01c2015a200d55010413001c641070301c5500a520200d0043c1c0c0b007600400c11a1900b03e13004180719262225804020807800180d10303032251103030140c080000c1086c002d076840e00040ea224651030740381081c006800e01d0040c0230207000322 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 133056169 1250 133054919 133054921
    0xb0a05150f0109170109050f010c170405070501030e0c0301090302010c09050103050603120703090803130603051f0b0c21030105030105070c20060919060e060c1c02010929010b03 78
    0x140e60f01158103801c40e60180540c009213241001210b00500340c02001a050740182101107a07205815045400c001c98590755840d0500b0006501c004810706c1940d0042aa030800307802000550710035008640500c081d5426502403485c0400040e007101c0e188101100542d4491042002840d00300752507100a14003800c2c05e024524000c40000d4450446d100099002400403070440e043c58030030703521640940b110b079003101d40d102c02c5813060002070a03091042600090501001480100242942002440d2840118500746041c180030f03c3d21608a007d80b8281c1d8420080603101c9469081d4280541c009150781859895040205140c03d50301c0040000c800d005001c00904006007100103015019076510700c4015a11001e000081c10301d200e1580b00e00c1d0300c00502e1420310a8001d107003c0020888425440d000107207655107007440198002c001c843c0107250402034001e0160038035903401e4404180288000100d0380e0701a510343d034a012220004551800c40e068001103034090303100a50b40501841c0384280c2c00c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 133057419 1250 133056169 133056199
    0x1121a0a09090308160e0d0c0812040b16020f040207062319020d0b0a030503130f08031b1006030b070305070c0b0619080609030d0501150e01050a0c0b0a0515 69
    0x200c8140680305c058000f02c0c0c2d0302c600b20628030407a0f0704201014010120305200d5806c4c140120b80c40014083d181290240c4070200110100708012101200c280301030351400c0800b206000290858006010ba0b00000c400011000c241d03a14030040170030301d00c690000200040510b0b141c0d5084084900c8442d20f56040c2001c0c0003018603100d80e280341590545502690707c0c90380c124000c01400703580103444d8000000c240044100480440600003400800e1a8000c400e540c94000386000348052181c04000c0e001005010341d11495052080b2180fa1400101c941c0c030031020f10554100c49030799005940c542540e1007440799850745401002c0e002480d9107044001c0003142e44440c01d6155014004510520360b083c000c020b8801044c0445005016207410790b005443d011001c0c545070b038840e280309642c5624080011650000c8507482c0c44402e0099503424410041c0e0500641c9c0e19030145038210103000116100300c00050800d11214411102010085100e042001e0380b10007500380003a05a100b4040c82c44280e00b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 133058669 1250 133057419 133057427
    0x207090b0603060d15110304080703020c030a12180b04120512120c091216060e0901030f060519091110030e0c040506060f04030b06120a03090603090201121a0a090903 73
    0x1138142d0040362010540514a100c200244112046044000404810030050000100c080d001c0305000c0d030290741404560204064603a01041402820340d0240e86400c04031034801e61120074104000e948000781e00b61180c00c10311342030f00300c1e41c0109085c1c46208688400c1020a12007219408200081d560604440010a01d20085c004094001c601030100e404a016030710684d0f18103020400c0e000b6039000c406c000e99449105941c034090100400e0502010f5051821300c00c151604a0350800d040901c0241e01d543c1c3e407000f0381400340240344400d9040020a5801000f4403800741054454850802d10b41d00a4040c8000c098407410440103140c500034180342c55040220719000d405000310b90009a40d0340300c200056070f43c00b0300c000c03654054402203004400c000e00c070400d00d4020403045030ba00058204030b401450341d42c4002400180024a01c440030404c40e400f0b42c100070320701c0788141008801241080c00910460742e120701001c40d4407071100c98514071030804000703c4010703000c3d030002070141400c2c0b910082c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 133059919 1250 133058669 133058689
    0xc1e0a0906110c040b1f030515010e010e100e090c070620120c0d020c07030204060e090a060902060912060609010602030a0c020f120102040b07050115030c06180b0a0207090b060306 79
    0x2602450700c415a40e05a07958110a401c00c6c00c1d405a4030809681120350b000f80240000c5952501c0180c0c88858410258060b6240300c14103103050395100003992446d403d00881d10000040c0b00c0130b02c07000e9055040c0b1987c401903d035100c0c0200d4602c00391a980070342040001d41c0e8250750034904c010701d0282e0056444c007a0104540b0320b00380e900303644642c603290301980400038451032a00000c03692000c1403d0882e044042046c104881c02202c0502101d502c0303025110002100f610b011a00b907002e58005000200a5007000c02501d0000300350604014004002c03504080d41c1c2c0c0d0f5407138250f0300035408004061628606041c09407000b80700440c10000300c1394025140c0c100d1400c1c0603210302c40459821109548200340340504c11100302c029911340703a4a00840805400060080307501c7c0d400c0c080b011b114841d00c0000d04003142c2d0016507040400d440c003d0140d0b1248480304800200700403030039011508480c1392009040205855004001107458003020344100c8000107005840791000708144074196649800c62 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 133061169 1250 133059919 133059943
    0x40309091505060c1f090b0c090108040f030504030b16080f06030619060801090605040302121804090602070209010e100602030f030a0203131a010608011d0a050c1e0a090611 76
    0x1d0f40e80c0c0c0324407914951800c405841c05042c2c40f4030401401c16980596040010013070700c20003c0c480e01c1e843d044050201d90081c0040700740020006c030002008101400c044254040c0a4100a454107449480d01ba41508003103448401000c0c003c0c0117020540e0b800610164407200c07001e0086580d040c5100000d40313030480940403d004045840400400c0e12103a0b0002000f032a99500030402e80c815803604d01c0290100f100c082e0058000c1d0306501c41c80d808a00c0844a003000403280d0700c00c0c03818510041000510072060142e41a560070300c04c800050301e0701d600306406080516001c80c040d00d400c2119014580701504107108540040c4030315150362003400c00b92070b00140180e00240c1c0f40d03a80c08010b031204141a40000c0c100345090901c02030000c10400c41c0314140e0714070340c0d68510240e0f2501c280884100661940544801880300000d05180b1140d1005400c40b6800c41d52503e0203010494200340845541024800c100300000c3d800030444d000b00c0c0410090546041c0301d084548010b02039074840f0200d0409c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 133062419 1250 133061169 133061179
    0x426061501080603010608060a0c02070f1503090609060203040c05031b0105090409020118060806011202040e0f0c16050c1905031b0301090c090f060501020c21030f03040308040309091505 82
    0x1151481e41c00b9081b201c050001c40d01144e07a1351070a52108c10142100c17009031030240c0209400460840060444041901c1c416503142c582041c80354401c4000f0300c40504265505944d6002010024825000844c01180140310500c0e146041104242c00c0200e01040c155890001d040c0c00784040e40c10409845000c001103500249981c042c0c0016603480740c4c014020314840901c5000841c034550800c2c1c90350301814082ea201e4151040c052040412882036009030551100074000042c20318a0841300c035680180c03495880340c2880b55046414204c4190101c04031a0360300000010040e5041c190200181c81c0f4a43c4600c0240d94036042c086034031040c00c4a603c2000088107000582540c030250019404141e001d00d2001841c4d41d031380c4052000701080039003450707a0750130078400007007a40c80050356203a000c0004246c4c0c0c0d004101d9240c0d200348079001d01b160550a0100b031040015900181d00558810780c02600c4010b014074161400401d14000c40d001150850729101120381400c09449440342510b10030340b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 133063669 1250 133062419 133062421
    0x201030524130b09040b010f0608010513021b1903081e0f07020c0603070306081504110607140109030201021c0213090c030905070807150509090402010f1103042606150108 75
    0x400000f40c0f511161040c2c114046209200030408480c501078100d031060460510099154141141e10301002c0c818154843d030001c0e810b55540350168018038000342c0350390450b21708403e207181c00b60620b800440381d4001248040b102d074003030680100c889507101019004011910061100e88008840080c18440f02810003400090303e0b28000c2041e422513501c0181030984a25040f04014040c0c202402561481c0c040c000d007010541c05891829406550700401e01301d1517000b603500303008154110740300130f0b114580c68800800c003994081c0702d00322155011f1f60000d6619950700c0003298007018403444200c0464130421100d40c1008180d8181400d60380c0c01ca401081501e07644200714094110104003415070300401e0700008800720300280040c1141c0c200c100071001410340a0007039845009146115400403142000100191300c11801140c409c045420100c03000100680600c1c9184c2054001e00c800818000803a914001e00510901084440d4401044180303031550088408180c050300f042e040c00f06d150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 133064919 1250 133063669 133063699
    0x20d02010e030f0a050906041a07120c02090402150405040905010e0d110c010507020619020d02100c0801050d020d17030411040e030d0b1309030302090a051f120f050705070201030524 80
    0x303042350024803048107010410340f000803284206078400d620407034568149400d8501580d02882522252035002011094550360759028085101110400800d2402003040003140c0c503035503445465840e038094800014079242c0380481516100d1a001410240301c0f0540482d1002c2a000940000c0c8074001e02c0d00cbc0d40c031000241701181b400d00030382d000100d0302011010110081540000c5c1d249801082d6421103002191030003c41d021542490745c01800200070030014092030601d0001c408003035101030700b00f66204250351900c0140b600b195001c20a03d2200005004c1801280020300c0c2d84202c08642c00c01025148180d05071752032041108407606a516080c0c2440681e45840d42002d82381050001441410642d10b070040c000d5000101c094403c20b035154010440e420048054110b40c9061078010100c0d060240096030a0f040f16180500a581c541010024808290240c03034003420050b1652520b8140c21300c00501603c078000d0094504136007040c00803066503058000c400c9036540603201c66142c04618 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 133066169 1250 133064919 133064929
    0xa060623090f040903050304170310030b1e0106090608090303010f050913060606020102090111060709030b09210301081507020709090804030506041a0a0c0503060103022206020d02010e030f0a0509 86
    0x1103202564843c3c031341045a014140c02c07000641c4160322860f031f07004410060816400e0030740019141113114105040c400c0c03001845a0094982180b00c02013201e0680070901c041079a103140c26004070000070184803081101980000c1540c0e000244007000d5402c2d58188514444250a0352043c3d600c64a03484011411405150000c00c1c0155040b040c10b000c0c0c0350f201c21000c2e000c2d5001004041c00600c007442c0d114035101002c01d61a004d01c060340d03030300080c1c3d41c950f841324585000d01400e070034410701911111002d4000210a43c91000c02c0034805c40f81c40358034115445003006122009648187d405404100d9010f50104200c0241d80b0740d814009152069070074240160700482d00000c1041c2700351018041481b204110340056440820b801c0350a0782d584019140607641c19442c120301081c0e052000c20710660007600a00722200400d4110070640503101203091720814954000009030300b1440380f0204c0c00f6828014200540020801940382101e41082c0344914801d0302e180340208400851403030f08958030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 133067419 1250 133066169 133066189
    0x12030708040f06051501020705030a080703030c120504110f01030c08070f0306030b0108030304060c3209031005070305090a02060403140304051002030d05070e010c0f060e0d080a06062309 82
    0x200220320707184c0c0d04035805c08260001207001d84202c85002030740340703400a81400c21651000c126800c002e41554142d000d042441543c405212504194080720912880741a11450144101110388119401400155101a40818109820200c5083c205034010082c2030304500704c2d01d00601036440a0b6011802800c00781c01c000c0803606058000140110008003460080b07004e1001001080340707441c000d465a4810a00c85248540100700c01030794048440d841c0d02000c8850182a440c1c0300c0e1040c00030341031600c01510707116250340d00e805005013242e152141030341c011003c200a020389020342e00042d4281c00742d480700801c0504600341422280700240300703480052101078090701d44140d01ca403000e0340701d40100301540f824529043c00035864600c201e442d80490780c01a1620b4401011588440064030501d26081c0e900c0780c1c50b455101200e14080003c1481ca040c01d9856050a0426886100c21b80c1c00030380c42030b020400402d15014489581110072040c880240121a980304018000301c0c5090070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 133068669 1250 133067419 133067423
    0x309150a1d0105060f030706120c0302040e090d110c01200309031603050d09060e0f040923071502062e061d0d05030d020708091509030d0212030708040f 67
    0x80c0c150010700a002054200a001c0c00c0d08880c480340720709520341810f0781d070066440b5801c002100d88401d000e0395009076200d1b042c1c01041e86400341c6415101c454019080009803070154695005a42d034003200c541c0100048040442d050241000031100e9000812104420344641b181210f220601480040c4c00c00898404410250030b5400e0350f48102a22200d501d0a0b110685050240601144180e48240b1646090341c0301611011a40350645042c0725440910400c80750b0010b0b40e4101f00310104401042c0c991441301180d010414075841c440c012818414a90710034000482103103c001c2090b0b8020840e107a10451008000991900901c000516101c90402d480032010850b003001c1100ea44c40044c3c1c0c80f1112000030814494413103c8180000d2602110b0080d00e19001406a50040c02440d0010f00d0740318000d5000e2030903d100c01d00001c200301d1a80086555100e40003606001601b0107001e2105ca058460001c0c0c03251851594a1406610000300108200700d40103000504000a20203042ca003c0c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 133069919 1250 133068669 133068701
    0x20a17010f050102250e09012004080d050414090c131e0806040203120a181203170103200a08010207051516050d020306010915030507080c0309150a 65
    0x15079915000007440c00540a21030060140d4010200c0500c1c00711800a0030b0f0050788010120240340115002d41101c0142c89001a95228114000d80d41c00040509558082d6000055529407400003158900460b801098042c400f0520041000850041420f00404010381c1c042c512b50f61040c12203807080c481c04003a106446205040451407003104241001d82e0703c17002200d44081030311203043d5541d500c004c445c02580341d07001c0038418480c10301e41d40142130b9038409400c011000b0b120b68200800400b00035040b840c0040b41050245062540c0240c5115100d005c0b405031104950440c0c554105c8051742c6c18021010010b42142c0810ba0b03102d115800c402003074501d00854941207030f4605143c440140d148120154051070000c50703d08405102c10001c11b2080c1d0311014540900308404501031b4000825240c1031048408001401668000004072070014a5800180500e000700300074210307100240424100d404144200550b01c40c000442c000780e291042d614600d20b0740d42d0900034024000d40d5800480603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 133071169 1250 133069919 133069921
    0x402041502030301030611030103080a0c03050405030a030c02030106090506010f03230a05040b06010816030905011d03030103060c0c02010509010c060b061308011109090402100c02040219030b0a080d03020a17 91
    0x8241d0120185042e284686020300801c8144d1074040020300080c08040e0850800b0040d14103464014200c5c1c0140354800d00f415410166a803000030f06100c5003260550220726141000070031803a081c0b15a001518095608210324184103000a0415150f41e1a490a26945805208080360440380c903980030841c4e6036141c0c046103062000b40c4080d00059504a42000704c0c280803402643c040c01400744500c2000d00205908039000100b100a004a10f006a5141d50703696102e41800700c0c1e0956120a000c000c000075035032545146010001c0700c41c10500032081141304600040141e17480806c40340368450910b0560b071886843e003042402403070004582544040001009090203d00300d164000f1100170360000c110b03a03a184003440c8070a1040c140e4095120b45600300180041c81c0c5001600364100d0030385440300c40311a00e580030034126488051046165070b6040501100558980652401400151015041c16140c0002541e6540316050004249500442c40c0141248912100440c43d00c0b0808540d490b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 133072419 1250 133071169 133071209
    0x809160909020102010e011a06070206070209070c030908010903020705130e06070e03070501090b07020409081b0105060f010f02070b0322110301060f1a070f05030d0b010e180c09040204 81
    0x140401c200032409542040e03c044030310b0300d0601c0f544608007407500141d2001010a4100003456010344003c0b83d00c00d0040c04040c015882d0f203902d16100e88420380b200d0042d50303250304002e010321246a0001d24039a040401c81c90000794041150412210203440901071000140d03030b60406400603d2011074984103040030003500c6075200005a1002074142e055441141e1600011112101e541c041c0d041c20b64000c0001074018106603202d113080380d000e03089150809207141c12804d0500c111f03140f5a00f03582c3d11b88042c0000e44c40c0465001c080d920017401e050300c6141c00714001030744a8001d4402c0602900012000402e68020b00d507420300e8001141030058038000c158076101d00281340060059020790702e8010003048040000c12940e0965048a401040200402244d10301e80e5020000c00c9a00100c11444000021001c00c0a0030a068080c00b010a0b0480c070f000004141501c03001c285846040780d10217038003d240d00841c0d0590042c2c00064210390325200c150101d00a44100d50003209503101013450552 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 133073669 1250 133072419 133072421
    0x7020a03052508030406020a0f03020c09070804060c080402180417040e0a0e03131202060d02040311100e0f010c110303030108030a1103071e03030b060c0d0e060a0f08091609 76
    0x215854140b4a403401041c1c8903800240d507030040c0d01412016a0288800e0404142800d6160540a04c02c1c41128115540c1e21302240782c0700c3c0107403444804610350500b8402001300c5401910315007032891610200920713040e0006600c4d02015000c0e08402454140402c0c20301c4902e0110140c48210100301583c1c2da0303078078424520318007411240c0403a11858800c000302d20000200480d24040300c0c50681c1030480d404e1000040d90254031007801c9038071020070403041141c080b4500241c80198060312003004080d980c0005d0289126035842c1580420500c10140d40403951980c10f4a4403c47c801c0c0b034070706c804172018a0b00c100a0111050301503072502c8040000102804004010101807006942e61a02d00000c544e4131960b034000e540e00103280051010100512000349145508070754043c2c6004500703002e41e40045142507000c4245020150000807074aa207440d04110039031140007041d10106d242042c2d03000300522030101c100420302040710580c08954100700030003244c00c1001d0301c01b100070b400c1035a03401039070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 133074919 1250 133073669 133073713
    0x9060312041806080601030f1704050904030c02120a1e03020f15090f0304030b07080a380f1003020a0c060c180b07032708010509210f04090207020a0305 67
    0x42d0620b0400c0d4020a04507008501079040f030390700c070340c23002c1d9805182ea44640daa420344144115a0b02000d000000d5145d4810740b110b402607000762243c840d0700c42c0500620140609491117141e80d548002c0d890f10001c2d100800040181412810410075039419290807400e103a206d01800120303218000c0300c041c52007440f084d2240500c180f141220081014401059120300917448090400200040000e51141c021000380d41d0119000b400020090402c24001c402610301c0c00c91030400b140f00011001209070114807100c0b940900f250101448640b140000720100c0401360303541d04158001c01c05540003405020b54000582c0e00c030342d00788010b98114500034103502200e100300c0080741c00300c500007481032540b10468500d503415545950000c480703902880c6680103114145000c04e80700420000740940c0a100325402025860086d15101103040c1c0c403d03aa0076031325003100e4061340d010408402490b040c01c04480449860103405a11280c56000003840301038036500c06071040c0903a5001043c0b110b088202e003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 133076169 1250 133074919 133074959
    0x402070c0815040305030609060a1707150c0507050f030309120a0b06010f050d051807080c030d030618050709091109040507091203080903070614090106061404050906031204 76
    0x2102c044402608500001400782c4029010941c1000802c0d06800c11034105680200e000d411080e101c0e82c3c9070b540444640b6500e045600d19042050103000d0702900c0721307420050700303800d00c2c011920301001d4441c261038009603c200d0344600481d518681e20b070f03107040c41914140f24005284cc1c491207801d140207903c507400181e04079208412040002c2c1558080d841d000d0516041d41d91342810020614202001080090300e86481040014408060301c081001880050a80c9502030550301c03030310303005041c81e204a00440006050500c681030140822880043e41900440f44012605803601401030351841e06039046150320314148400c403906413100b03100624a22106440420641c0e4400c00c040f619005240268400707108a1040140828030a04425070048000c1003564074220803076a51004640202c407031002000c40344030421050100a120341c100074800d03420211424001d0005501e824442e0780622481010644003003225914108212802d008032081c40507561070f2603180100952250b0008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 133077419 1250 133076169 133076173
    0x111070f03140f0d09050a050f070501030b03030f190302040807060305040213111e0d050f01170601060905010f03020904240b041409060d0b010e0403030e150412020307020402070c08 80
    0x26250020b6200315148111011040e6081040300e03507131100680b40242e41a5401d21601108030045001400b510785428041401071000d1482c080014050324100d41d2032621a420500031415190307404003c4038174003451500800c10403644040107078000d0041d03800840c02071140d0540810b86e103406038015800303079008481440c0c40c80042d0300303081c0a5440204078065104001e101c0504111802d542194103018440d04440c100b69543e0410411a0000c581a01590000c0b100421048919031250074140c1d0b809806810150305100000d00705000cec81c400c09041290404409096030b10a42c1a10b14040c0b0040c0188aa80545642000c4840b014081071600700d4203c200014981e148104035802c0343c8103589801446a0007404000400d44000d18150300034124403a440c000031000c1003094082c08102c18240d00c00d08107414001c0444410b80ca140c0c000341e200300c010301d030b200940c3c980003540503070f028022440001c26078100705d00358042c00000a401500114030a4200801c01c1c1d056002e998200d02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 133078669 1250 133077419 133077437
    0xb03031b120705012009030a0201051e0d0504120503040c030210050d0207060e0d030e0601090f060e10080c10020a0224040b030a1104030c12060b0a081515010912050111070f03 77
    0x101010311481b03540301c0258141e011107240342c0103500690117000340003003e180e11100d01580394484000c6503c8000c0030505255035004000421545241101e030110581c50090f0551905965240040c41d95001c040d03c6040c03000f0401c403105100300d0450710031b44903004095448090a160540c043d005404482c981801140800e5204034401c0c420740112120303850003409a41d280200100041503525001e04071f141d00d4441c0801d441002c0308240340100d856048002c60b42d8600b0702c2541c10840701d51401c603c2100800071000c14543e001802c58251601141c105241c03c22078826410f51448044400c0c50070240440c0010b04960314002851290103440c50a018034012a41940320070312031800300130f1035421100020f00228240140702d0313120038810000080c1c01c243c42000a2180030143e800704485500410b107070b4040754000c81c1c00540180c0c484410403000300315200080c041540d42e019101d45150b61241c0c0c4410320000b50003501500c50845103280d903a034818280b8408040c4565019408501c00718 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 133079919 1250 133078669 133078721
    0x504170f0a090e10060e06070c030c06091d060418120f020f01110f160204021602040e0109030503060609030703060c0c0309061b0201211a0406090b03031b12070501 72
    0x360007a4858003200c1041000141004000e403a2206c1c4008440d82004081c0b0807080000c446402c0d62000d140180582d2a0031442c0140003460508240c0106082c142c49010070180698100352040e040002102c0c046030051003210030f41201c6104240140590120908440701203820035140c4015000513400c2d602d682c10800322080c01e03103400f01040da1038141c04000e9803400152100181c8000c0c07181d81d42e0003039410840d0300018140e0b0441c29198110300c684020580440c50b161098506d0031400301c009003c0c020050b14080c0032804001c000d1801413000192210300341e5004d00002000e150f20800030080302989003030007494003040031000c401040801030081207803400303074206804410301c3c00070a800000450780116210f1407040d05020910004890035840c140e0385000b070980c0002d10020701003d14400e20204020344440d070b807113182c607146850040d1405450100031140440122544c0014a44184081e04e00e0542609110f0041c110003003581c400b004070640007041d05040c603444c0250040c8a83d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 133081169 1250 133079919 133079939
    0x1e0309010f0e0703020d030908030a030b09071d0402030a020c0102040902070b0906090703030c03030e060a0f061a09090402180c0d0b012a03022805060c030601120504170f0a09 77
    0x56408a69804000104010320740303281d102d46c9841c8240b400500d11951042540d01e503403c4040100c0220752603441404003800d29802c81d5034089014038040f2910742c91020008502c80f0301d929071500035a000000501c00c2000c94044521400a0b10b008560f13495079a5800c40081d00700391001c03540c2020440105120350300000c0c400b030191041f90094844985140c0e030581b80160611400c030141a100c1c0c0070174002d0041440300500c5070941d42400b00380010340b03020000c1210513603081a40401d070103107c0884100e00010903500300074070944143d803664a55000141e00144149506003002c01c02c042000710841a49010f0f03c900050620284421b0b29684015640300c3c02c0c4030200da01400b422a42e1a0103106400007410003203000f40142c03180f084c2c0d00d000040d580104200b8034240400080c4a0300b081220030419540c1c0031b002200418118244400000d0500f070203141032004c0f407512a8040340902460300c6c0500381141c18403590b25601e184060564819811187d0090080b41100100260722001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 133082419 1250 133081169 133081181
    0x41d0709080319121410060801080d0809011107030c0b060907050306041503060e0c1305151e0301091a0a05010503060601050d060e0a060e0c0403020a09020705031e0309010f 76
    0x400c0018500f0f0840250b44a921481e50340e4141e42000018540ca840001591144d0302020103202c1100b40c403441c1072054240c0d4401c941d44141d04005022004201c6d0380c0b070201e212012418649050721068940c51400d501601203207154041e1150b002800e0410160024a40407903d0321500300700a083c0d03945010820498001c40b1480c01003501080001c05c6407030a40e0000a150601710407002c5000e44079250740f411140b0355a0308406e00c1d0302114112000389048201504c0b100740101007803081703261620303c2401c01540c5000540c05110310007440f0104005907443c0c40307400b45011340200140c024500b0a54070704041c03034010200600369100031400e10350041c0542e40c140c0d28050f00074403454607404011201540400c1095007419500c00c40070410044900d4018000c40c9002c0012032164117005c0e07004009900074014514540f01000204016216175032803c048600b813182c01601c40c6d845060041c154801c0c14000804c2040e00039401041800210107507006203182d40080110b520740300308403012224 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 133083669 1250 133082419 133082429
    0x108090a0b040b040f0b09010b0414040c061b1b060f0305040b0f15130f0c1b15140a0906050703180b060402070519030206070c0305030a0e030c03041d0709 68
    0x2801e040000c0c0420225000300b50001e10aa054100685440c0c4617000300c8041a0f0340c10019035160b1103208400e2500b030140340084141c4c41c01a030a5401c0564802c10b02d80090b100d980180b0010034040c40001c2d00000f04445d5050700718060080c3c0b90100040310035042058050280811030790b1400324200c41c424030405200301d50102c062641c0d5202c107094490a02001048880c0c0310059460101982e10f40d001d103075020040400001c64544010076401056441002211b0100200d91050901515412280080c0b03a40c22001c0c044105200081c10005010541d031601c0385c502100d010b0245080041d800f00c0303002c40c0590010003060b1640038080741038a01d20001d4124070a544803840010590300c8c45c59541180740207100520380402551820b040000391100d040c404080b51054105043e014090240c1c400100d1a004056588a0350701421500014000f10115075882000105803001041250b10642598048948855031450801420224280200d25201e0800081007402c5c0c040c54550301591 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 133084919 1250 133083669 133083683
    0x103030915020c150f0a020a170f0301030b04020604091e050106020708070603020c0703060c170105010302160b070c0b10032006091302040308040b09101d210d08060108090a 76
    0xa0b0180c2c007085a20600014046142d001c10449401224101710061040e0b46680d00034043e0469242002841128402a5052420802c2081c582900e0240d821a410360384d01045940c0c1e40d0b115400800c120b8011a040903200310700d8500304a140e0520802c3c0d1400c1c4040186040c011a80c0301e0303000f2621a5454421595180d000035020300c50b0324021b4000c2c1024104400c102d030101c2d0390700c1d2070340e1090b83d04030754a00c408185d2019003c5000010580300c94094002821300f5890560036503140c10411001410160040c100035010802c0d0a01c111211045150002c400002314248841d04000c28051448211140b000c0900c030681c1d10b0815900300c03008100020002428640800e0620480c0c042c3e60103c80c404543c00c203c0480001c07210b1f006400601694120162504001e9040c0801080b001001400f842104138240c0251020303091744011641041d10030100c034140a118040c00c1805481000c60680120103040c00e110303900400d81840f810099880750702030b899800089445030000340c0098451 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 133086169 1250 133084919 133084933
    0x1050316050a14010c080f04051c0314030a0e01110a170c090d14030703021b06090d110a030213050915090706141605070303020615090a0903031104030605010303091502 74
    0x1103d090b0491059950041c101080300305900e40d1012070603444a02288101400850b051180c0d0500f10404180042d084030502e100040c643c4026100c0d00541d2000401518000001002c12910f5004030302204c403c58000c0c400e102208911201c190032041800000442200300e002130301c5030410380a800b91100d90750480c5070000c504140030104141450543d6103040c0b0040041017030f042000140040d500a502030030305d040304144994065500303000c03264802c8030207210000e240e5556044156040b6071010300803943c1c40300d40c00400d92030041c0360302c06076100c3c1b080f545c1d4126101c042e80120b80b00e04642c40a59049031218200031800040580c2c6090165000302010b020160090071011600768086d80c1080c2041c2d1500420b03902d141303200c81c0481d2241c0003000104100740e01000f041c5d400024070400c0c2d511500180000ca007403541c00900303881403039807560200e000741802548602d19010350108115074543d1242000b501404c0300707200890014460303071400201d80141015178aa402070f20340c00b90100d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 133087419 1250 133086169 133086179
    0x3040f200a0e10080f03030a0624030e100603060f1523041b02030c010509010204060c020f0604260d080c07030e0f09010603060906050f010801030b07050c0a0b01050316050a 76
    0x303050300144400f00b465005000441c038071400300510703078204e40f068004543d03038a00a15480c00345d8655500c152503003a013818105249500307804c150030504400c6d01c9c00080400399240031038944014074605822407468514044284a41c6400080d80c40d00140c800340483c881d06038918212010354880c0c618108014040380d40c0600103481040d4100d08000e0003c6020a110800715540c0910f02001070b0160703000140c0d41c1c7c1d51170b5083c083c099100d81d0303410003181814a0710b44041c0c0b105c41e005100a20801547c0000403055540304c1c2501c028040502e0701c4001c90b004a40380d10076031070441006400340e04c41c4803494210f8034403c00c12940700790580c5001c1410080f6030758050380c942c51380d242c205030b00080c004100c1c0700649418004900800c004d540c04154545044071070f00458038607801580c01303070303642004481d56640c01c50300300c5045a50000c810501030741d4042c0704070f03504d00078000000e2041c00f40851603400d00051500d018141c581c01c8060f2074041d13400c04140000d5103400c0c45003a4000500c07140c1040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 133088669 1250 133087419 133087439
    0x61203080c0c010b0312070308151003020a03021207020d0801091e0906090203011b0e01090506120603030c120403020108010603050f011406070209100303110a0b0f04060b0603040f200a 81
    0x2c04150314000441e03940e1041d0b000a01b000c1100c0030403c9041004a003040602d603010310801e41000362401109446941c150104562a0900610000f0f140e00010040d25881c4245d04540c11803004d0b6002a205060000e8001e480d0b401c2d4407841d0700055810400030a2080c45c0307114400fa603050050740c2e401c66003c910f4916019080740a010f41c1e600c1d5a0b0003214016032401e0091141c07c5000582030f81b00045200c001414410810b24441d0402851280501160311030302d08a40014041000c00382440e5034840001707103144076102e180a914019000d94411a032030030300c0504141c81c402d885d2003569a8032004218100c039801c50f00e0a07056480c00303004003c030780d000140c41e00c4241c0000c0c04092403c1500d0f000b00b17544c040241d422148032182114200185a031001c417000d00003512001414902400c0e40301d00c0d105010241110138029042c00114041000d1580868403801c030180c0010348070310301030402c994800f039003081c02c2d10191480c4101c803003c10210f40c00c0c1004040014250809a402d01c4003c007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 133089919 1250 133088669 133088677
    0x61f03020418120e0901080d08040b0a0b0607051b060702030d030519061e0608060109170a0b07020102090307080c0607110604050405190f050411010c0c03061a0301061203080c 77
    0x34549031440d20b10480424000d0705102c80c00d05990301c403042c07001151010b0290601d0140d00840060304070203550b4007400d602a0141d50465040380703c01d900c2d0340703541208000800410340c00307d40c00700700050001c04000012450b00f14115100406113407031a440303402d0003528410782c00001e41c960014002190514020f9101e540c00070000f1400e50042c00110b2200c1003220501e403c200807070580194030319041c000d180700c0307000941628034100c0c1070b50402e03400103030088040340105403107020720501c0016411800c2003405109030300300040400504151401034000d50105c02468040d0107411400b0400d0b090000300101003030303c0545010b00c4d00c00c3d00d44622440080c041e0718a94032010400c800141c3d96190b00445001e00700003040040c0701241c5689000403a00d0184240b0400c504040400002c41d0102146510554007802e03c544d25549600d0161003d12650f00000c109510389040d107100c05a90603070340c00d1202010740080081507241d100ca0340345040c203001c004000904c900d00160720200d03404090 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 133091169 1250 133089919 133089941
    0x604030e01030b0609100311040b090a0503010606091205030904091505070e0a1809080706060503100504080a080402060c0d11070509040c151101091101030b0907020a02040b03071d040203061f030204 87
    0x1d51008c40880ba008544c050f41c0b25100c0101301080880140c508828010b0007044114000c00c0308500d89107002d000c1404501c52640c00512500c800c0b01440000d00c00c0380c201d510000c00412065070745140119101c01d45402d40d0400c140341c180040d07066401a6052058481c0007008144003d1030300000d440b00c20000700d11034404c3e6445440040018001d800034001c418407904002c10070900344411f15282c001d8940e640d0304202d091a041c400400c490b00110b0f50580458175040c0340c01d58443c00443c0e05842448802e51440c41103001c0d0b03034101ca50010211807541c4010003079450305955030081000b15802030b0780c082d000c181a12400c2000c0344102a1421240c8007a04007948100c640c00d100d0340c01c58040303080c20303980788807401c0008200d50380c1071180f54641c04c02211101a28100124001c1d5100e022401c024007a40d502d00200f03200750b404019400040c04904281c0038044250304030703082c040c902076600b00d00900c03c0e0340101e110812660320a020700c80100704c00646403031440d0200806040e00c001d003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 133092419 1250 133091169 133091171
    0x1020d080f0a1508100b100507030503060109120b01060908010e0601090e070503030309030a0909060311041e0906020403021e0d0b07182603160f02030102040509090604030e01030b06091003 83
    0x6030f005400d82c0300740c0110040503654042e00403840f281807000c0503160182c0145115030445c41482c0001600f00c004d079094160140b8019440383d48a00060b03a210705660091545109421f0a0504000040d059681a40c0e000c0e0f68004080e6600d250050980c2ca865005034066001a001806107281d154410124038051a04407007800343c0d034101107400cad5841556141196000040c2464031a60041c1c400c2004040e0440c1c100303c03d501c2d6460741d054501802c49094812501c46401c0d0b10402c040701c411050b0801114010030048120f4a8580c001b544684070403400b4801b10360341e04c45180400300765034034600c0b0040c0c0080340c14026039550480070600200031f0b4091041034401c1a1111400210305800340901808102903541e80200c0c441d5105000501080240c0c020450440300400e07240c00a410f0319440380300b00c03410541510000c3d001e070059030409034000c00300104005c44884002075280c0500d00a8480040341c081050044040d28412802c0d01d400100c00c1142003a5800c106a00342182415858 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 133093525 1106 133092419 133092431
    0x70c030b091011180901030804060c14010903030b033a0509040c050418020310030b0402010c05070b0c070b09090a0924060f0501020d080f0a 62
    0x4040039250004900700710810800c0401c0c0501c18441800006681100c07000385801c4200c0301410000302c07401d444994100500628180e030b4002c5d181c5803034107091240940340c6aa440c802190000f28081c445004040c007031040c0c2d85040d10a5030080f03401098541014075244840b56002c4070b2100302d50000341d5088084400c040c0c06400c00c56110700306084c0d0201a0f03420700440110681160030543d1703203a60b0035802001441034600c12103100824200d1075040100301c4c04201c5000c460746525640520200303440351800c42d4800d20504d880032601b6096601e00341004e801c0e40c00340d489204080703242d40880c9020701c038910203000c800c25150706061605000420401001d0030024455569a1502050156040302d07048000d03440b42100c06911481d012a00c0141401e10491703015060300340300031400e58800b15421182038015644c0040329260316903000003600c13024100000181e900c0c2d0b = true := by decide +kernel

theorem cover : BRFrame.Cov 132913669 133093525 := by
  have h0 := BRFrame.cov_init 132913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 132913669 ≤ n) (h2 : n < 133093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
