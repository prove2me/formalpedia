-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0358
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:23:56.105788+00:00
-- url     : https://prove2.me/submissions/4749bb81-094c-4c31-bb2a-f3c9dea604a0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 64208635 ≤ n < 64388492 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 64209885 1250 64208635 64208647
    0xb0307030e0c030f070e010b040b030c18040903020a0b0a020a0e0d02061b030301060f02070513090501090219030c080a081b21120a0516050702010917061902030c03010302040b06 78
    0x800300135040342e84d040b21002d01195800c0151101d0321400603030080e450140144814040304084204884e0004600700301c0303641e58800c3c0c0280742c048524009440c2d0380103150400b0402459004203100241e903100358131491407035036401e40400c2207005a00d010000220341d4003102c50142844680071002c58001083c0e070381413000090014080f40b158514024054001000400031315400400484480710f45001078a08d040c1440003081c0d08000c00b040310b40e106511900b202c8140706003940080b510b40d40181c10485031400d807001c2c58908050a1004841041d07940700005007035030307001c04d0340541c0c10f50011040c1c7c985480e07104d08500500d0302100c100c1c65401a203036456a010400907801303081c50201d05140d616448080001160488014002542181400100b102200c0004401469000141045925034105000494244606400900319210b1135800c07000200c0e00000e500e407003681807910500101c01c4000c484800d901091b43c92090036101800140014034013908601803c01014200c181055 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 64211135 1250 64209885 64209889
    0x70204060303020d140403031407082116110a08070213050a0504110f010206040b2a0c01050903041d0c0708070b06030c030a0f1101020102040b070606050a0603060b0307030e0c 77
    0x100e00c0d50003100540e00c6005000307500b60300440c1440c0f01030380c620305083c1060702c3c41d03d010b400e512030081e412028060000704001004212400d403040c440001c2800c10942080011700090640c040d1550500000a010b2020b160b9106070208081d402440000d00200e41940d91500055000b00d00102e0703000c10841c2080030304000da0f1003403070310600010700040b5050070030b401c00484024031150454094075140d001e0201c2d0742d80000303941e40c0142d4401050b400c546d483c0e5004132511001a10540b50205801c00844072000d0340b80d02425424514000800594840220303595992013184200c4014584006d0900c24200c01812440e0340180456107092518100d0344d2081180d902032401218400002c00910210381800c012940c2c0200044c2c00410032004a511241000302280c20010b0908640e00c40d50700c01e59100390103031401000c0408000751261500d1a04c00d02400d41c0c0d0207a00c0c0503014041000403820310a0080c01c00f140d1500103980d2a64480700b400310003401d08100f240c061445110031441c895 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 64212385 1250 64211135 64211141
    0xa0809041d120301090b0a08031204140a0309030b07030b030a03140904060b19020c0d080c070b0a1d060a0905010809070506040906090506120723040f0b1018050402070602070204 78
    0xc8074090450b556039070500102034102c948407813566009909080301030001c508000100d50022010307455012440d0345524004008000d1401150380c180940c0c2d00c0c101c10075410103e40c0f230a03030303104202c000416a101d1004a04440c4403400143d4940d20400001010030300074010307040b0140040c050b0b2031600340d001000c5800d550403a4410b100d00748001507400300b2100c440c42c00c526009418800381007041d809400051032000c46d4100604810800151581e56074420070a400c020700107464804d4071030b6903140015041712103040c9508400171855190041a26148049400c02c425940700c00d540c0a080034011943e0050090058215110307020010810380c0d610405000181031102010540c1400c1c42285025100d02030306803030042041301d12007a8021030100b240025600d0540c149110441c640c080e62800035810040290030900c5d168481401038a50b8000003c079440c2650300b002a0000c43d107046848401115080710601d03810758051241d80740ca90005c1400d54007400e00076041042940010f011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 64213635 1250 64212385 64212403
    0xc080c1c11010b04050417090406050405010617010f030f0f05010e0609011a030c060301150c0f1203060b0712110c030f030a080c070b0703020313200901080a0809041d 73
    0x881d01919400c403140c8024000c20b5010032060760140541e00b819521030104022501e100005240045145445911150701c002c005100c003c001f40001d5a5521025080c6170000c1092050180700c3c00000c1070011104060200700c0344e00070782042c2034020075203820610404c0c0300c404030b403555200c104d524140d80c02040958015258003000091000071070007002c26aa1620038018040e4200032107054256440c2015681101d40d01d050301215080c1400040302d03002e1000100818060304540795005016010110841c0c0700d034203072001c20007151242090103182c06500d0380102501ca80301c1c00d004503213214490070310703248412100f201c03101045080040d0421413222404485603202007070000d030181e445088960810f00c1c0c45074084c0b400040740c1314484081c030024001e42c107050300000071030440328100a216110a40025000407072507000c0c880c205030307482409201da108600d61000411f0b0f8030720200f8103109a80d8041c010358503058400d01404098802000ca030688120501c001121071b020600003210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 64214885 1250 64213635 64213637
    0x50408010509060a1505010903060b0409021005071703040803180712030203030906100807031101090317030603060a0219080c0d05040308090f01060b0301031112010e0a02030c03010c0c080c1c 84
    0xd4113140003a0348500f00d6807a00c0b2041150186500c0c100500d90700602c000381643d42001001c110405400d01182c003824405500941040c5402c9070b080500b90300c05c01030702e4010303c5424800e100d100158125040c0e400103803030140020808102050810317508144040c9484560b1040d00d9580e59503598814045501101c2a00541c00000c10081c1d8841d0034080654044141070300d120030389040c034040c142e881e95a80002070030404230fa1040d00b0180c1c050342c0c4150085034803040510034a0183d54410040b0340043d2110b901a104100c04074041c08682d0003076544009440b007116150b071114640498860002400c4407010394420410090f01d0760040c05050300c1103000b0303102c41810741071000406180141ca80503108469140c050284141c01a0504507070450340c0116410140c001c14600050041d0320154000890390f180440a10b80c007030b00031403824503442c0210282c414180c070035014036003641e0f103000e1003d00061511034000d00041048001e00520203900c0112207001072002c1c1e100503d0030065003118 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 64216135 1250 64214885 64214893
    0x90718051c0c080a080f0a0201020f030c04031202070605030610090905040507061b0c0303050d0216150c0806131d0601030f0b06010c03020d080903090310022203120f050408010509 79
    0x10705200b05550b1103401420640010300700b1464644403150540100910001e0144000400c1910b1502c01d40565160b44450711201b0341e03d05244002c1d500f16030040c80100c48a08200200284d818004a0b04000b01c2c1d49588801e40b440e910841080181c0b4050b06048062111040c004115035807a44669071141e4460f8004041081c01c051026203034100310716410342080550801c3d01e00040d0301a802074112507150402c640c5501c0c40111141c068010040350000c3c101c0744860200c10300c49010f906010800c0112400c00000c0c00309141210320740c4049a08540011010b02400c60540c0c1680c000b0032a603122410007600c00c104c004185050440c00e9105803500b001c032102080502c0007075407045400a400b42001c03c40d00900c2d6070003a40312020050000240010380c00000c403011024030844607224402410340c2c45000440c3c00c0c150003500400009103840c50b0003060101080d41601646042d42d8004040c214a00a1441c04039150b20101800c20308000e0240700000c2c4039142406200c0c010f84054003d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 64217385 1250 64216135 64216189
    0x309080d0506030f060c18040617060f010902070218060103060f0e0a0501060503040b06010c020a0513021201050102120414040b04020a020a050f011a010c0f080c160503070509071805 80
    0x10301c0e003404040a4141a000002070101c01c40c1904c0c22510f510350740048602040d92140300041c0102703000c0e03000d5254020004100b06002c10b02158940c07155030f5039540680300e40d890340b002c10104e0140f14030094100c00d108041c1100314000020680c0d000c8014540494142c6d101d004e0b242100c8003c2c1c0c070a54000020f10f0602148269034040c007405400c0515000303045150503111402001d001400a1341404507800c0d2100070f5460319a05000603000c05800c04507100c0c0500b802200039441031203585003103130206001103119840132807810a02c1700841c110b1414181840d080c42009021000c100341d000b80c0d030325404081619240040e102c008040d4018108000c0b07e0b0400301d060080030300c000c01e0340c0e03403400c1100320000514401c01c40340e0352401c1c6469800302c0e0f114036110164545014000d0005080421010150f000005030101840351040e80007064030b0703070394050595030300c054040c140c0c1c000e02400026204501c510b95813008103400e0b89c3c040081c1999600400c6005054420642c554041c450070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 64218635 1250 64217385 64217389
    0xa020d170f190509180402150307020f01110a0903140c030a08091e0a0b1c0204030b0103030f02070b0f030915040804050f0a030804060c0c17030d1a0a14010309080d0506 74
    0x20300280d40d030583c1012460701150303800040c0100d050454503108082c05102040a41d02c0da420040d0085011002155980c00d001c40e001e0b41e680e804255200480d801c00540301d44600040041e5510340360952a640041401c564400041c0100703d00824001c1c4907589030803006640030000c1d8403040d4040d6001030707070b200c520100b44481c46440c01c18600309140440c4281e030035500c03181c9916046400a800d050f0720340c4140072036480390f8600c5400405040e030009c1004402e1204012500b41224802e07250211100540401662500e4141c0b1900c0403021080c040044c07800060402158400d1003001954001c0c02258082140c41e101510182c480040100781804035043c01003c011440d10111501400549180e650301c01c80c0c0f095005c2c520800002407100d104004464059001030000482c0c8408168001d102c140e030380b904591103146d441070a20720300c0700000a194245000142000d02502c50f02d45c14072000200c41c0f40746000d030320704246d95101c511000c5050040a400d0048100300007140131700300801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 64219885 1250 64218635 64218667
    0x8060f130b0c0301150804051507050906032401020a0c05010c020a0518010906092d18060507020105070c020d020904020a09291909091a0103050c0109060f020a020d170f 74
    0x4045040c44100c0382400041140001e40c0c00d65251b000041d209c0b15610030740110303028026080c003550080d1001c03080c0544410030040b5012584900c1c1d25855003190098012a82c0d011035150261048004460074005941304119004040d4000b50440c4d5801c0d41c0d41003c10b00d0340b40c041c2d00640c0c4107440400180a80f06940c09010f00920f504031091084658071089200104000214400105000094196284040d03001003002c2001460f15160042d00c0d42042c00c0585005c6800070015441c107800030328203901403d410b200603500038101c9540032400798240140d440014000344c0e0702450032140004d100402e030044204c0910703500d80304407081c070070b9404405c50013080d480d0700e030310422418142040d100e6060101d4011140c1184002c1402c002c03604244403100341c100420003070f6800c108008410300c140020382608105083e82c60003900d595a0104071454086407400340010f810181c00f510144c036041d250b05031024000d0040300c2111500c0c1c820345c11a41d03c58014081c02d1000401e81041040300c844e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 64221135 1250 64219885 64219919
    0xc01050c030a0305060a08121305010c0b060d050a23060a05010e0c0711090114091003020105030105010f0315060f080c040f1206090210030203060a060201020408060f130b0c0301 78
    0x2090690030918020412501c03400784912550400d130356100041c034141d4548054800a103007050680350955601c80c0d41002d581e2101e0b46209031844010000100c0b544581c25003250341d40c0014200000d5140c020400080217000c90b030507511481500203850100300c0503010204a4000d5002d0034100110410002d404d003d8010051242545054010041c04512010180e4003408220045a850420703103440034040382c6801c5580c0e04038058400116501e42c410400c070354807400c100d480c0c504555620600c0d000c0c020950100a0000714140010040e650058124102e42c020500700803c40411103081d54040b02d100ea031090001030096810342c40c51315007000c10641c03c0142203400c2c51810381045c2d002c0210848a206440ca000c0f401c26030700003440040c3d4045c40540b540181034803102e00050030b008001c2e410584003103114031900c074400101c06005208440458000b2000f800103a500c1e1800c0201001e401482c08104814080e460000118450880c41c0300b00c0003210416100d5041900344a4094101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 64222385 1250 64221135 64221137
    0x140307060302091810030f080405010908160b0a050c16030201030507050705060c070201210606020705060a0c02121903030c02151e1801060f0e0916090506030c060c010207050c01 78
    0x403c03010740a503c800c2c48003c038020b082641c2201c0d68940304054a061102c5520140c08408004c4007482000036141c018400c4650990321719469544171400c2640b9440000380103154142c01030400c1102031000030182c080c0c2010340c10410301346107003001c8060801c0c0714040380c814507901e00101841150f82620406800200c1403a1150034860070f80e035846e60781d003c09070510301114404030710481107a00c18543e01e8010b90031041903501003000c0e030100c10081c00146c090352016010315000440c49040900542c0c0c14a0501c3c0e90f529030201b11a02401100640c11000c41890f024110241d03800c2c0700d0000b0401e503040e00c41d507400108102c040c1030007800c040d4100c180c40802030b000070600c10702ca80700760b07e82c2d19000d641041d180c00b1a25030020705256107003109687e40f160f508001000812903006035089045800c5904242e1059907aaa08a5142d51090750b8031110000008030510a0701038a90005038084e00c090704507040e0255207030029032650000fc40c5021103a400250440400400b440b5201c0e41801c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 64223635 1250 64222385 64222387
    0x1309150e040804180b121b03060705180a0803070f140a03080103080a1101110c12090603071206080102130305100605090a020904060e161409030d0e0102031201140307060302 76
    0x380e68505103446548540580c0b603000130308849641d526640b2149000000802010085004050054450140c000401a442030740d02000d101810040b038101c0c03169600d9600e880c03401e50b0792404042440001071407990000158034000c0b590a100300020155180105251158803155103000701d401d681c40006c00203580c10100f00c120002c3d40150780b4a054a80c01181940c803074540b4081106c0801d1400d0101070f2540c01d00300000d00101d424001490341c40c0f8601d054820070060490194035510584000f07580004007000020203091085110002d000702c64000030404a035103030b1a280c00d90700a400454060942501d00308104a0300b0402410b0208140b9001d001d03282c502400180221002015072101c26000151908a960f580e407150029103452102ea01c0d60b41400440c40c1d90841c50500034101107480164002c03010394003102030751840c2100170024030300b0905031a4116204010005e00d5415031109104c1c00800c00c1d00f642d241c0d4060818605907a481824640801d450300c4000d038842400d01d44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 64224885 1250 64223635 64223641
    0x10020307080a030203041a0a0501080f03041d06030708010203010b0a0f020c030a02040e0f061e130804090c090e0405010b030709150b0a0e03190606050f0105070b0c1309150e 76
    0x4001c4099902c0d40150381001a01c0341d949040c500d00c0880c00c1d00401681d050650b0400200403256030140e81030b40c8001d82111050000810700a0382d80c850790103140d440c841d034210b00050844210340125400903001d0300b80da801035a205521805c0ea08280c22085404d01c0c08100c4052840e400f2001c400f01c84a1480103020340c13120390000c213469124040380039000e10745803403c2c07101ca518200702c0130829010405c105d421038640205801c0740c0036240b8400300c150703000200c042141c0d040d40b550a42405500808010300e0180740044c1d0500030541070111905024142000250403103101c18424030542c040c03030010800e080000101400e10a06030017010035640350018042d010f5040b40035aa0645004051856071210302c80804e50b02411302c9103105078140302e0444030883e0066050180c4024511840d07041c0300b842e171240c04003c0b880f0300c284a100d000503418400300010464500d513094001c402407080d24a048070400c041f8035010011380205038100d4036241502211915407050701c0c024070f031050b0b034036031182 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 64226135 1250 64224885 64224893
    0xa020607123e010612060f06080303040201020303010e0910330807141807091406090f01050a0e06030a0207140a0c0b0c0c060412050606040e0c120a050f0c10020307 72
    0x4030320300c0c0c4240d0b4041c103207000850040c403d500403406441c03210b641902e081145d16003480942010011341d9003450a21000051218000041d43c0c06540e058029504503801c000c19103009220003171940704070344550319040300010105d100d240c035107840c003c00e11440850340e483c041e284030b0b01584203c420408041020440c00c0c4010031302c541a6035048401c4100b10140380300007a511401c0c814a4403080e40501c083c0710900d80c0002c241c10803681c0d00d100f41d984400c105000c101071070240040d20380c0c0100124100d00c80940c40b41c40200f4042c106402c002e050450301a0120b51250421038440e904030381d00080c08001e00c2507407050840a5480356005004c00300e10b95554040190140c81406810342d000b00c0c08450291040c000d120f059900a40120b8031541d5841d00d01c00d01c3c012034441942c00d405040c010481c2070500b0300540128200c070500814403901c01c001400401e2101c4602040ca0f8041d01c1c1043c00018400c1c003803614950744d110010268600c0000400c40e014104131b4400e025507200f00700900001d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 64227385 1250 64226135 64226207
    0x3051f03030207151206080a15020301030b07080a0e01140a06050901080a121106040606060f03020306010903020609040902041b08010f030f0b060a0314061009060806040f050a02060712 81
    0x4d20310302550729140065160301a034130040d60301c8000c40c0c0e45042c503a000c0b54641d80081c6004056000381c64402910b843c1c00c01d01c108070711003804084c29280031040020407440c000d21460b0b421050038013001404030304044800742110189920700f0307103c0c40d4140c1070000904041c050300024003c1100c07007503580d501d0212034035a030b50440f020041146940b407124800080c000c6290901d07051a607015202a4a41498540014009402010082144940398001d0300c0e1091081e07920507941a1103106405046070200036072900829503c0743e1040d190600031005072902c2c0200d400c582d844ca9409458110011030260640d00140c2000700103003001e04c800c20200c0c101c9048050038035001276145685844010208202c00000d800103440c0c00961800e1011000f070005945124080c17180c241e08081d40c50340342410540b0014450f40070341e5800000800c0c007140840c0700c45503060384120121100180154040b400c2a00240c0701507504060000c280301c086500040c42e05040c6551040d40241c1145428603280b403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 64228635 1250 64227385 64227389
    0x4020a05031305030919030203010c030605010503060f13060b0403024603140d092111042003091504081209070b040803250c0302010c0c030f0303051f03030207 70
    0x959902d4904a0040c0101407045408508014248488007402890300080749182448100e0080d86082110501288a40b00c1d074815168142d451500d50b0700c400d020010520786600385943c3c071800c1c070320310505121440d00c5030310000c003039044c5250b480318514010466001d00ca07650b0341d400d01d0440248000314810f86041900b05116415144012600c084030a031a011a0790308020548002c0390107841c441c08000510182c05030365982c810700443d45420641d203490580810314a070b50b070a10f1108400248080c81d07003402013a002b400c00101c0f0030504196621260a040810811040000600c40d6602c400d12240100068001505d6100d01381a9680d000d035214489406040031960000700350041400c0c0420002001070318a0360f9101c9849800594480c1c0c4811b4001144e003000900361001d06080e203e194121036045030310010700500d15001542c03520b040301021a82214802d40c0840003550040c6103030380060003554005180d14100000b642c078103023094450030704003a044504000090b070009803282 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 64229885 1250 64228635 64228651
    0x127020a0b070b0f090a05120c0606040b0102070b0708090d060b120d05031b090d0602030601030606091d060109080304080703021c150209010513170c0901060f0e0f0d0b040b0604020a0503 82
    0x11551109070280c24180306c40401030182c0224454100d940c0b4140000d810180c47d4941514282e03100c01040104403850300e980ea0b0f000d600020700030403e1410712030160400d680201c030b286241102100016901c1c18802004803000c40c0d50b10b0088219088c01c4066200780c3c40c0603401030244410740071000d400c03400700910390020304213110ba07480c103080c9010b003e46000b03440142c006098000319107030060180d0411240c65002070328150f4001a0907102e0003c0f4030031030310316180300c03e05920b141051000c01c4500078a01814000c00620015858a0400c0100028801c4001605101d402e510400c03850f01111210010350210030300103100402c000c40d981485242c1100342c0160b40d8072280c070041c2c90900404184281c1c40b099140000b07030002c00b18056140700c041810940c3c901c2001182000100d0b4002e0003039500241000304c0b0420581d001e52260042c00ca4001c2410015601610005150301d1012004480255520703041c0030800c600540115001a41107805604000070340100030f09602006081032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 64231135 1250 64229885 64229911
    0x21010e0f06060f0d0b0a20040b0d3201030309050f01121e09050c0301060506030915040302030f0324030304080307020402070206070501150e0601020c0a060c050127020a0b070b 77
    0x2034203550760b1600740c084e0b1961255205c070452410b88034200080c0441c030450170201241100440303019034404201e40664106078907a900380f8818042c000018048582e280401903003618205890001c00720707904120100e0810392041d00d41c1140340051002a4075071209004940c080c006e03200326a0020304082e0125490000081e011f901181825202e095a4080b600054600380c0007800b8000d004c9901002050160001d220842d40e64040c0315444c40212030b00103198002d82060000b00c404014290b4015009104690500e0b000d1300280c0015070042d15510b014006200c0c0905525041810441402404030f0196080628000c1c03455100e118a981c0240f19950008071642155548420341e014980c2003c001c0000554254107034140403024043da191142c400400514a5032002642c3c04000c0300140c4001c240720318000040d242940b101e001250b1554032901640d8040702c0110380314510031400b62100480c1e112500521803c2440c507003014052403810021100424200300b040c54000207004584 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 64232385 1250 64231135 64231159
    0x50406060c03080403140a030605041104030f0f032d0e150d0f270516150503060105070b040308010f080601081903050c0102030a02070b01090b130b01020c21010e0f0606 74
    0x1181c0c2061b4400307030003801c002c0c007160f07410719994164040c100391f03041520f007040700d1941c22a06643c0c5004031311000780500321200090000401d1031001500b164401d04200c8414083c0540038142d11f80c074036001c000c1d55000c13580200710f110f45c40302d05420039a00542d0030300400c07805250880d03100d118801c00d090302942c44008143c502c0c00558407240c0751340e29052101b41d0780d5080380ca4100c01c55030030380d100b03a505200392011900c0110340b1865000440300c40403038007042d000d00f216040d15540c00080680341441004c2c0005d001040c444420180700f241300f41e582502960510110f0b100821841c5c001a406501c032400500541c1c00010340209000d0800b60b084190707100c1441d01300e0f03882c0b00b034005166207940084280485400150060002284035980012503030382c0f1910b181c011104803008803980405400c54002c00c2c2c0351642d0003034214110601c1500c6202000001107170070300c48a0b028446c541c05158020b07010811080c41190300030242e582c00750000f040500652039030342c40042c003024030400c40c032488 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 64233635 1250 64232385 64232387
    0x2418061a2d1206040507061107050f04091e06060b130306110906130602010c05090f0108070e030106060c0b0901051b0306010915020604031403090a0b0402040f0204031209050406060c03080403 84
    0xc0c070300820704000d04981401030480d07800742e29114103036802c90703c40c8100403000c2141806015100e1401c2d20000040c20510726000c20400d00f40390300e034652038200c2e544014005c00725000c01048407030703102e6008900c502e1081c2c0c0d00d054022105103510003040d803e018409400007500c0c420b010000c0742d400170008904080051409000ca105500c401c3d548040001406c94005c40e0180030401150340d950000c01a2141ea840c3c1510b6030301c84c02c10f500e0b5106408c000c5505066000b0f04da629000506480c0032218042203001190840d440780e000180801c400b14401d60401c160440324070381c81640e2000902c96800c0403c209007042c840003070000326184001c1b000030b4190340b0443c0090020544114441a40c088840003c0e444500c1034400341c00144c440319485508022480c100c138020b51250009003640840d940301c0410114001e00301f00d03400381e00c8008030412003446d4006440618007601810701e070400b03048c0010f481011154440c60181d41420020800c0d990015020900250941450540355455140c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 64234885 1250 64233635 64233709
    0x40509031207320f03090a24060b0c03040e041b03030e0f0102070e0604020a0504030c081501090b010c020d02040e06040c05010f020304122418061a 65
    0x908008403400700010071444940c0240c03142ca0a8014038454038110445a0101d103d91040b003412043c80101080204003400400c0c0c015544084480c00341e9143c15011f54034140f840c0001c031554090a03183c0c0c002000d110000d481004002d0030707006c1d003141c0b8251040d0f40848e00e03070086200d90114003003104001814410255000740d600c901c0310300c0e002d2095890740340180c1841541803504c0c3c0146122046d4407100c2d4000103040c401d4544925401d0110354840d002c00000e98404214102040405d00c4008000f41c0c0c50040e00024101c001c0c0078000401411602134812481640300044441c02d01c504501e240c1d802c0442c8000d8242c0550368030340c4a14050010a0103450095219142486030328200410701c44011644416606c09907a09507141d038400000b240c0e81d00683c000d0041038001044c40c2c00c0000e44039224065020100000c5000402e0403a54440c00c5a41c03d5003071120840c284400b510821605108041040718024400349181030b850300461881e805000c032007005100700d006242d401e400080c5e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 64236135 1250 64234885 64234897
    0x1807080c060c12030412141204140a0501020d06171c05070309031202010506130903090506070501060b040905011a0a0e09061c031d01030e0d0c0809040906090c0e1504050903 76
    0xb000184d072800c0502c0c20380b84c521240340441c03000401414003100440c0f074042c11191400c4405105080d2620303281c40d104c1c0a03002844501c40544070b08020300300020800e001400030f000080c5000036441e452702c2d40603c402443c0000d06107998010b1045082d440307003005424244144140303042b580f2800c1e545004c2c1c590390160340025010703c024000310800654150042c920071402030750b141d10134192218809054605148000b008120900810700c01030428101600c900740c0500008030b441079440b54401d00030f030b0040d0400e00c00c0c5500c0d08010300c100303265070903902c0f07110354095400c52a1507000ba2005080040617040548259105408942c190f0b5a01c40a0107004011300705070b5141031100e250180c02c0c00c5040c050301c101a04158148500d0350300030f100704082e003030298028000801c2500710803038080800c00c8086504807400e2290ba040c0da19548100d07446c1a10901000070110380c6814010711201580d4001c0213080381c0c030b4007007144c0842080a8103075111b00541c0c3c04034094031751038440c6003980100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 64237385 1250 64236135 64236163
    0x1213050607030f020f0f0a020d1404050405090102160f03111204090902030a0c150e0a050114031008330606162105070209070c030e2b0602031807080c060c 68
    0xc43c5d21210801d0304d60007452150702c103400712069109c541005807103110700c2d0101002e40036400d010030041800c2ca074200543c04000d0700001813501d801540381051911100ba01601c0360a101d59201013099005036400c20581000b100070400c50001080c40030707691186010703d494180c2c0780c003092001c41d107003080401c000341c0d401110b5601190312048640d10201c141c261900001c3c070252201c281e03508002202c001606c1c41a900c84059070407000c083c19042d440a8402ca1206c2c1d10f0440c0001c00003c240444550301038040045002d41c0766101c045c180d540d01034150200910301100130f00c6400d644071021600b400059800480c208c0d06a400e02c034080140080d110a130111074003099805c1d856100e8010040d452080711101d20300d03103440c40c040742c499079400701c0100450306655481c140e51400c0000d4420302c014804442403c15400700c141180040b0f0400125030454021040c400b03d00b07180800303159144006001048540e14140e00c241e0340f10140111540210800034040b40f00a00078082d460f051208 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 64238635 1250 64237385 64237387
    0x60a0c1a0a05150409120309030909020708190e0d02190305030d0c090e04030c060f020f070f02100c0503161a0709050102010501050901141219081213050607030f020f 73
    0x1000a201001c0c14040ba181e0400e05411800e03d201440c0038464031540e6600408158440390700090183c00801c1e128074240c1c184002c4070000940807225000905040c0d21403200741c0c0d2200d04102d43c0d89480142540c985003405040c0e419043c403921070347d40707150071750341c045600d1402844102180c1c010b180e0342e0780010700309010020f0003c2d02c420307190b00125113040a5a45000136103a03900000421817405031001400182070105c4c00c0081792003500b00c204452803000005141842c614180801035000c2c220849890210f28503050542c6001c88403005903454604000d003280140f41e071102c2e12442101e2604074120082d40c804802c4c000e040b0030f0555403110ba20510b2030709040605010300302d9807091055900540c2480000308140c1031004a00d8121800641c02800c14054502003041160303412814040c0344c07040010041d03021000401c94000c40b40034031042e0b951101c1b034201c140b0808000808840c1107151001c020300c00035a00282d81a40400a480d00280039005002a50045d101c0d003160b506c00054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 64239885 1250 64238635 64238641
    0x8120604020912160501080108151f080109060501050a06090b030c04030501060303091503021303080936060301020708030f091c090603051302030d030e031303050303010303020f0606060a0c1a 84
    0x71000507180300c0105142d00c2418001e985800440340c05009020f112a80e41140d04a110008400e032b442d242c0200001c1d0700401c1880c0328074403104405860b54415040d5a460302c0c1c0e0311092200c1445001e01400301950480d040728180305000d0001c0c1010322980c2100c13a40000003408945101c01950042d691240080c8042e40d40c0c1d040044c142c10072801030340c1c030b0701c10120641c0c0c0c002402403007290703140e0107508081c0c2c0c0c405256031100102070704210b1302d00307400c0010341e60001e6840c60f881c2d1000100d01c66a0b800c155001d1404401c5c140400c1c0010030880c004c0e0720402104010408000507650700035610035400c040c3e580ca402025090183c07045806402d0459000d80501c11600254404d050329400d540400141d600c42c8000c0780700502c0188081e425030015540700401c01c1c806c0d045520300090702400c0740e2030030000f0303150100b030007a103a4001d42d00c0e904048014410554140110301340d281981d00106203600302b41c0d001440500c00c20540d40207100c0c60800000c00c2011820100080050f80780103a641c9107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 64241135 1250 64239885 64239919
    0x8030304050a03080c120106050c100c02030a030c08010b030609091005040501090218062107050a0807080705090c03192d0c0c051c0504050a060504060201050106030504081206040209 80
    0x5003002d00c003140401c041400041c480100d034020740d40e59481e005010315159203000d0058825900c102c03091100f0380201d0720300c100051424043c641c410701195005540e9402e00e0b40008048a162011b0320040002000040042c86101c80070359402110848100329280c807100c812a140c03545030000a0b0703c0c9806c0c0003c00c4240074040d4016440303d8004c4d101d01c9002c0440075907120f0240c8007190b46580c8152140400088024243c0300d6a5828440d40f0445103156161030000c0e04500d016844002c05900414050004a0081c01100c0082800307440d01e40e034034205081c00c250340e40001001040311002c584050380d500c1d50305412900c2e03118281d08c0c8162241c101c600c4041d0214041d5000c6454850a01844914980c450307451020603c0e00075003e404041014012a0040d40407400f842c807c2107420710011540d0741d26040e003c0c008125640712141d8603860220042e0a450059000303006061800c2c0400000c80c01c3c0504a88010782c00b07208104e030540c0e030740e03001500a0094002c07940c1c00200e08518031445c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 64242385 1250 64241135 64241143
    0x8070501081006020a06050601020106050316051306050102120708090405070302120702072d0e010b07030e0f0109120c0b0d0204092a1d090c03061c0506060f0a0803030405 75
    0x2440007079075448a00e548070000969407801d984140001070340000340c0b0340042111984001e4110b0f134140300200700c841d0b0354030020345048504a41120100003c02e010003041c601140e40b003d10036041041405401c0c44c2c200040d449803490006682c00380320000724a01006154001c9904588000740304001030306020200a000307412010440489041c00740110b0107460000401900301c1d0300740300540b09204d4040d0455000394a004a2102c0400056400442c84070340c0440800d001c0d00b030340e10900d0b03141d0b855810010b000c0111003072050700484071224100d50300c1e64003905440030f90b014410b2540d003a4816160006404010b648200017040d40880e18106120083d00117100712400240144501040740d403455141201c07500300d50102080e1006605895030040c842038043c4d642e4429400a916a050b0225102590450320326924180001c100541e0f03250504800c45034a01e41c1c5030030b800d1000143c1d00c03141d0300c401c040c090502c140394040c1c0c01845a40c9060752840581a8441565200e040c18a845075507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 64243635 1250 64242385 64242389
    0x203010305010b010c051b0310020c01051f080c28080106060e0402040e130503071a0f130c0e0c04030c030b040614090304140d020603070804031b050309040b030102070c0807 76
    0x741d420700000100c10740c8100c2004ca08583c124000d0300e5045c0c045d0744002c0c082d507140c40c40f480e01402040303011a1156482c1c405002c0341030981001141c145404400d61764400c5911060181070003410b03500f401541000102850000410b590702e2100400c00460f10601c210344403550700301c00c540010041014141074018500f100d80c5901c610800702818000c0100780c1c0500c1c0210302c04024180b002030400407004008004103400b80041e20f281c0043d9840d920881c4518418001900c00365800740070003072180080469100d200383c811201006402d41e50341c10030b82c42d90300c0f481c00c00456610204030300c0c19942003102e00842d800312000d5801680ca24181c0c56000301203070b041e14440d00d4100c0c01d070f0000503c80f030724a01c41c040038400b4604c2c060a1103011a10052403e1103c0d03000a440d26552005072103040040d40202d04548608241c2d2403d441c00402c3c914404180300f0000260030020300010341c0006c03e44602441c100c2e0081614807013500401d009000380c1700081c0c400300a14000042640e40032801e001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 64244885 1250 64243635 64243643
    0x1c03090602010606080a0f020c0303010b03010302091312031a10020f0613020d03080a231006021230180c030309060a0c0201031e06140306040b0c07030306030605070302030103 77
    0x504958403039003603089a049224440c0802c640e90f0014050404a600411216045d00c1e0010708081d048452246190400d800211003054000010b10551410582e003950214100e04210345040c4199a130419400811100d079040c50386031803a25824040e0100c48000b48500904101041c0d0b4060400075a50021040d0b000e0f02800b4a502150170700d400501a400566005040304518501c0c0d680c00300c401410003051004400c1d611139032a10403031400c6070303001286840d0b065400c2d02c030704050181c44003115041c2e00820655000030f0070500200da0450035600703403d0019451103481500202d61700111507840503100340c5004680d08101040c20204c3c0780022012600003241c00701800d2206040d620320620b5651a030001091000c8091548110200212030f8411302d4081041009091300c00c120740440401e0140040e1515018080280010f000010f0348604800404403414140c54039001100058030051403080000b031580c1c01c0c10f000340c000c0070046511110402c07c5180c6040024000d400a0201319 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 64246135 1250 64244885 64244897
    0x9010305100e011a040801060603020c160501090b0c0a050303131a0702030f0c010209130e010c080c0a0e1f030c120507080105060306010c0c0f090b0a140402070f021c03 74
    0x302407001400640c1c0c250b85000a08404a90034038140c5482100010300c43c507403030f520030440403541c42ea082c01030200400a0b920003686800b85045640c4c01c04805850025150356040010062a030b0300c540e40350115004401c519550b0038003480c404c0c2c1090500c1c0805402440300209016015240e0410b140c1018013500e510072414890010308068240242d800c500142d000380107a003840c5040301c00401040151800041c1f6004901d0049809038001444106050741d40340516081c2000a00135022032036043e15140b03400346008516100180140d2201c1000c00042c0010720505448899091204600c07041458424030f035840001406000070a035000d0010b00c0b400c9420a2000b007500885e8010709450721049d065a080809100e0250402402241005021140769003c2590204500060820b20340442683e40c04c1a03c1d0702c040c0d800074403800c1d010f84001e00080101c641030781000b50244808a03005a582c040d2030800695603004071001a40c4608490780c130500003804407062043d01481394481c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 64247385 1250 64246135 64246141
    0x31902041407020a03050a0309241d030d0b03160806040501110a0206040b09100903020618030a0912020103061505070302151006080402060409110304061a0a0302040509120c0309010305 81
    0x4144544181e50b2040903038050b941160020340502c0c00f515442c8014a000505000301d921045c140e40020004450f2021910f50040788140c21030040c07000e00218459a0000d1522075000a03030780f840b84841c210111540c84510b0352040d0350a00440740100c205a00300329000e0348800030907858803000d6070200e44661130000040080b00c103047c01ea903d60800e0350007074000c0303640d6030f01c949011a4004040e41c009010310b8461003c003170000d119241019000c0d9000f80560310b003840c400e21903500e6404800380d40c4e42c03040c0100a000c5034841c0d02a401d5a14400310201719400340e2005071b0250a0301d0300846007030040004010b2a040e0b110001e401c8a6020340d0803a04040d82400e071140c0300900660b580360b0120400c0c07400f8400d440c0500c0409801900c0500000d2030103a5800c00750081b110043e100144001300002800140030b080e0142c180c0341d0442110840e01d002101002400580d11440024003454403900003441c01c0400f4084144c02220392107400d41c3d0b5410381c0d0001a1203601003078010380424904008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 64248635 1250 64247385 64247411
    0x3190c090815040305090d05010b04180b060a080a12020a050a32060106110319080423100b01170903030105040e01090807020d0c0306090804090c17010b13030203190204 74
    0x1000f405180c058585500e0521500e040c840d15a1605c07030151050b44d22406450510b889500c16441910302400d0400090240c501d4000f180c400d000d048a882008070860078400d95002144840b0301030392111040e00f9031030034884207a040803840e95000d44180200081c81c0300340010742a03a8002c140d1145603101c4a0f428003d50007400c004200400b10752544880018000b16014903051000401080102ca0503c03040034609480d04861504000000c3c0c0441e00344400c003c989000000302d1108403101043c0c815000c00219640c0c400c00d800854040d07241d61a060269000c2c0140c3c41381c9880140d200f00d05807801102d229641d40c020311550703008914100095105240605c07038900c1107507101c00014580b10880d000c011810144450582c2e21014001c0000002440d0348103400000340b0501f9440d48481c80c2000e550111034884942030203000d825000d40010704c070b8404c981030568611003180f60700c0320481e65800d02c1c607011541009405114070320204240d8090791651480c1e49100f00c4080c041a2031600c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 64249885 1250 64248635 64248673
    0x50601020616030e1612060e030a021b060c010222080c06090405040c0503060f041a041112070902041403070602010608062d0f0403030608061b03190c0908 68
    0xd1011070000d840d404070b400c110301ca03800c2a0021100c40301154050882c01158240c0824142d02c1080801480c0e20b250702007100e41d000e92402c0d81310342409581030600919010303489165404440d01c1e15928868200b41c0c581d0b0b003400380c0d144010714500031511803c0e103049046400044860311002c0d0001a0f00c002500040080d455000e80070203040603003411424414080544000b400488141c15800300102e880e4504120461103804601c0080d89103050500700f104c1104400c440d98450120300701c04120100c0c403108a681c0c11240c040d2001e41045040f183c5090901c41c1c640c10800704907000207000210f40c180001d00501048040b000e5400c0e082da0346505034202c80e060f10030b00c00b80f41c00040008618011021000d00100b80c00b520000c00441c80140d0b500c00c07604100c82e8489041e8181d01844141070341842008050000c2c1c500400a41c10040300c883e402c03101d0140719488820380000044c0325026a0311301001503030038000c0d051100d4150603001924500050081c480f007031140441246003625212 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 64251135 1250 64249885 64249891
    0x3040323040501020a06020d3e070809010509040f020316020f28031407030305012105060c070303020c060f070212040b030412110d08062d010c05070e0a020a030506010206 75
    0x44c00909071003580d40d407554041d4105c41d0900600396918042c5182400600d0100d54600000e080201c203614100c62502d44d02d0003404025207010481404070f40001141790049030b040640c242080b0391101c0020001130081d05a5080c0900d181d40040103010b25007894000c42e0480101da0b400b07899030124640005641c86408000f40311120340114480508890403c2d20043c1c1c06002c0e181179100c40e42c9805400702c4603030100f14110000780c0d442004000004000b0301c030540d13120708908003440e23804190b1241d0703540384806041448207010010700e54040500030b504940800030903030103445485c5408103c0ca408010111640005405404c0d946401d012404d02260141c401c1c81e1002ca0540d26152100040350304c3c0310000000703001e208409045c82c11020071000e503104003240d9458001d49403981c18840b81020000c0380d144100401c520f0182c0841c000351001c0c5200f182880c05400811103414540d00e0305981c1c1e40301c0e2044408d03000c14040e51080540040018000585080c001600e4603001241d65280803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 64252385 1250 64251135 64251137
    0x6080a02090105040518011506030b010e030601050103180c170606010908120d0905010e0109140f06041e14010e1908030708070504080f010204150509060d05060103090803040323040501 81
    0x10301d006003c0740c44e01d41e22481e0010010b55a0103002d41420070280c3c21150032076141c10703280d1800e031010880f45a240c0520300e003014083c40c2c5880061070320b5001c030396076000c103004550505803646120840e14040c09284404160003424070001c03560b5900408015003201c45260b40e00d8000c00002a90035405440b000c5c0407204102e0041c080140526241e4210381c2194000b44a42e5413107038402e2012800900171410004028000001d80760700d545041e0800c400110400b5000b900141e41702101120081031b01d0341c1c0142c01c405410a10310804058152912082c08024403620400d0704251301004154420728600d1134010464000841c018a00090001042d0008186940400001e00803501c6104a83d81040751820304906250302c1d506013600340480d00c0e42481150f940880c0c20482203001e044000302c03001c01400c0c4a4604418140812000d03c11000000100c0e0b40f80d07004244542d12943c41813030b200e80c0044c1c0d40e9440f405c0615000703016a522601c880740074003001c1d0401c0700e11807011003242d04603801 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 64253635 1250 64252385 64252399
    0x6040f08060105180a02090102030d063512030a1104030305030a050c04030803010510030e061323030a0f02030706060e040605070327140d020d020706022103061309080a0306080a02 79
    0xa184c1002021f0360103244124114041804031600d03c0d501130294070702030901c1d201d000c80c4184440e01c101d5030704101071340401e441c0b4240283c58404c410000c503800b104210f103114920b603281d99600040ac0900440d2113410000c100025002090540c010301550141c003c4200078840c6c0e4a900c0204010741c011400042c2114008000420203071818040d02000d44409007004102c0a81c0484c4a90504404880c11001c80c40d00070740d04000c00542440d51079508454010f1500404010030b40c250f07881c0036001c01c81003030112104004080034020002d88800c03c0d8481c03800d00c07030a51202c11401c103000701078401b03d03081410900859103450080c00382e841c2200982109101c4604030000411900c1e817506402d4a05000c1d030505c00052200030300c042c007100c0050307800804c1c03c0c04054074000d1501120740e2002d41150440f445e00302c40f080b104158005004983c01405d83c0300e48074500018508a0704185a14400e4502446c00c4100116080900000f042ca0345080010035982c5900c20b0f101c1580890003988414 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 64254885 1250 64253635 64253641
    0x41701050108072309040f050109030e01120510030f02010908160302210c010806040e071409100f0302040f0b0303130602060601230304080910030f0605180403030e0c06040f0806010518 81
    0x2400c0f01740c51341c4140201030b580c908a405403a000e08407810f200040c1c000608100c0c442c01d040d604021255145051352804000342c1c03a00361403034020a199404014101207c0b2490b07081560710500d02c6c0d2000c0c00921003a42c03031581281a50310300c00200e500c4124001c11426000c4110406038030800144801030102420031040c0300c00044681072402808258402e07034400c08810010010456440a040080d10a040c0e003d40c4000f0400746480082450207407800114050140504256004c01120f5054502141c200c41c1c1e00da980d000380030311821a81e018400800c0071100311804c05403840840319036400740d4403262581c0f40110303400243da00001c85600c3d1014403910f52030220100079075025010700382150030a48501700140c0d120040c81a8040000d8560314050124986849184001c0508840c0b185040e0b01c00002c076007a05a004101406240d9039800c46da110300c506000300300d40500003c1c6032a035515124100b4885080050180941c07034480c0307800100e0641000c010780703a64148030301c040d4500f9079 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 64256135 1250 64254885 64254889
    0x12150901090c1b0302011b03090b0112020a03080304030c0210020307030906020c1c0501060308120a060501020304150503060a0b0c15010e0705071e0206030115020f010b06090d03050417010501080723 87
    0x443d4400c2c04904565a80840c554060070048501c400005255004940c00080d8100440d407503e041c2c000201c0300a030000e0b44e40040c0c0d6130390908001c03240e10039031030380d201ea03207034101a9044901940082d401c8803440c0f4070031800940c00300040000620a07100c0c1030b0800e441c1d20080b0396401004c442c440d0000c507035030a41d01c158801c0005500032903205c4e100218070582c481d43c9064150700080340740c0722649212010f10081076018090640502800e00c021810245000750401495003140403407028400c00201007002503c40b03000c500302510060180d140d4807141c0134480c581e12070107241021180d5000800100340c0c40d0031854114055040c41c0d40302c50a02e022501c1d44159403070fa01540d42c1c3c140d0140c0c00c40c10010303210180518020086401030b010b082c1c4072568040d0626a4145001c007040e4540fa00352603503603030303064140ca041c2641518255103892036031400ba00c65120b50b40004001d14050111140c002c0782c150030850590b880304090b111540d40d81c18581c00103030031410314060342d046800505404d41c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 64257385 1250 64256135 64256177
    0x405091b06071506140307090905060c07020303070c0b0d0e0c0306010501032301030f031b0312050702030d0e010203100e01060203040915030609030c020a1d0a0c02010212150901090c 80
    0x4103000b01c07803a1404400c3e1501900403603466074003102c0041c4011a117607685281c1440050300800c894036046c8000303c2c517642c40c1601c4403401002c09626000c00304201056480070000d5880181c0c2c4109600401030316881c1400640c1c00c032510040c4028140312261603542c501150b0200c41e02400340080640385d00307210040d4080c0540741000070443c17240c24a0707100030001c0700303403010300840c041e440140b4148843e0800800010f400c2072207010310034000c0381260010303070703c0301c2d043c001c900b1010130016a03610b88a40490079486a01031104580e0700f00015409103e00660085000b5254400315a01c038559915618400041c00d12680300580c1050004110044881c0c10044602c1010003040c070160b80c4940ea224101c4920802c143c00044402d4004021810080890f001620510206180000214049150012004140310042921100181030590007501519450301c06000401c500e0314019401c141c5940351044d07014880c00d85600002040000c511a9012480e00c0303035220810300150181c9840c403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 64258635 1250 64257385 64257397
    0x10c0e09060f0d110102100e0a02010c06020c010204060e040b090105030a0b040201091502100f051003030507050a020406120b0c030601050d05040327050a0518070f050d0203010605030103020405091b06 88
    0x8194004004180703543c0f2580c503042c040e44200403202c819041c0c040024a40408900e180d8580c0307103890240c20300c02c0400074002035050303030901c1c012820000a16105010307005025905410f5800800e01041e115080102d00c07083c4c00041d103041107403601000c200b060341c540a218072509904004048404213542040b100d50090040c1000d03e206a5100150801e18402d400c9070001a00b2400ca00d03e03c448980c09440341d11680480305100390300780070014040c1140c09110050900000003090020031030180818020290008d000700a01c5546008050a025602004651102c0c5140c0002d80205150087e04e008980682d240307818000d40401c110300501001c4c0041c0e003030140428424212046944001d4445442600d4050400d403034002802503d98840d0040b51180140d40c0a04008904081c22a07610117118600005040b808030b0f8191100d10403150000722944c0000300114426802000940c101c82c0b080d40c0801003a80c1d808003450701c0c2c9540600341e18000c511000d2a02d0a0316054002d00700c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 64259885 1250 64258635 64258639
    0x40210120608060c03090d02060f071d04020c030c0607050421060902031006080c03070803120c13081f090203060402060d0f0e01051e04050304090911040f060f08010c0e0906 76
    0xa505500d0b0744078070703251440486000c055200c0000c20450070000034060380420524134001010307241000302d0100154803005204a0400c00090340d00a9074114003000141c440310050000c545d14000b60030911744a500c4440303c60440c1c42914041460303184114100c4046400d007448080d136981e0188030440b1a009400c0c000c0e50801d4540d00da03040980e40620600070310003c191000121035103401c001505000401c19441d120b9000410704210341440401103c452525031698201039584900001107107000314198400c144210300d0f808101180c002542c0100318a2103030b000700d0150405654402a80d8041400940582202021900508042c0d02406090100071001b0038106e0b04564548103c4141ea45ca1007a141c6d140c0e000d00466040b441219510640c48030180d1070f092901340c5a00759030b80300d9882558002e544d00e0b5001030500c07410079940c0103090b8004000340610544040b80c030000c0c02040c001c8850315136131220b00140000b4144036044090101f515481c04a41250080081030b801c000c114503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 64261135 1250 64259885 64259891
    0x3070e04110f1204060b03010209180604062111150a03090249020604060806030a1709130e0703150e010509070e0601030507080c07031112041404020304021012 70
    0x1c101e5060002c0c1c800e0f081002c540301003d01d0070b030400109441050301e6450190f4030400940c0c1c41d540b42c041a404100d120507070203030b48942342c02c008900209040da0084000f0341e010341460440c4020742000d810000c0c001d50b4030b1400240700e40c04011240000c1105505844000c220b0f90745282c1c029001102414002850340744203080c64418444a6160007001002d6681c20a903845104400c1c401c1018044060042d24880d40c1da440d40402e801e07200e94002e010038045007800041d600d6804104040c00d1075400303031000c00b440000156200480d0800181d50384501c0c00168010490a01442903911103260300c4002d0110ba0300e1521204520f40944c01c8900c0c1d40c9071100020300c90b82409000d45c90107440000c1c0180090f0b0b1800001e429101405000c50b41050706000600191540c8444015000005014102e1b0b031400d4601e42070728485440c200307000b40c5004862584d070f640d01c2d450000e442200c0900f0801c1c1038210b20301042008070300c82103c000358400300c20a0300f65591446a04403c0042409203400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 64262385 1250 64261135 64261147
    0x601050d090c0f060c06050f04030804020d050304150f0e1807140d0c0c0507060509030706050a021509010b030f1c0c02010210050109050114040203070905010f12140906070503070e0411 81
    0x90055040f0f8012501041c2259420070400100f841034a1f03000503500e00740c4408e03040a03500100520741c0548003a120746503012580080c00742c00d2007160700a00032180d442150b001c40b2007000d4418010504007102042012000d4440b5081c108041810302110080802c0184c0d41c000d42607d1146400700940162441440315000b04100c500c500e0055242d01e0b01e03a61145800d070b2510303034901a07468010600f0801c0600030244242c4001901006450090030403607200c07909800e0882c0b4200c00070132524503000c0c0000622052a00641c400ba0004c0340503400e90348216103480c0660794904c0450001150703162144054a01c03940701c1c250f22001d1510501c103990080c00680d22010503144281c1105098a40c0c0b200100070000e440300e080410030809507825400d500d02521301601800c2684501810b2040f03144000741c0140c815028048002284d240410619002c2c204243d0b06c000121402c104138400c20001c246842c0c05078050b070740318180994401d02d100580c002404049c05041005202d054010304c90 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 64263635 1250 64262385 64262399
    0x120c02071806030b010b1303020906010309080325050705070509060117010303020d08060411030604050601030608030d05090f0303040203070b0a05040b0f09030709060513020310031e030906080601050d090c 90
    0x5010301c11590540460314604506042d0000c100690215021180c200600810092040480403c5a0b01142e00c2c40d210764032080168040c0446040c0108081800010008489101010001d621490301c1905124025103c2c041e034440c8200e010141c02580604401c000c14a45401c22681c0554103240c04600c58400140f050603002c0300f0b0704101c015030042c0542111080c0e000d40516403140301164180300542c208505010300e0f200241801b4051600c80d0b00140099000790407800040203c0c004590380ea0000c0341300c40d8003c010a03100c0d04540d02403240303403071141324000082d00e01458000300908039283c5400c0709034816030300070a81101444414880000c64104400c0030300540700031008440d0752124842e0401d17040050719080035484610300346080c4095101e80082c1d0300c40c42e07a464030050352034690340901d10200f41c0c50380c4010f0840d0b80003244116203011241c10860482e110307850352210180ca5090030f0b610100300722081400500240100e4840c0f50090b00320350308050240c01c92140060311400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 64264885 1250 64263635 64263659
    0x1b0e0604060e04111e190507030903030809010914030903250e360c010c080301090e0f07030f0b0c0412060f091703011e05130b060c03030106082203120c0207 69
    0x41040f030414000c280c64046002034007071168109007c0c54020300c0e2081035600a811031a0707601019041100c1e0a001419850095110f20046c030340100511009401181c04a03a61368000d8281c94064012b2044c40c40720300b40c0c0b40720760380b03510400d2021450b0110b00b00565111403010041107044420750214050700f806d8a1015050000940c049401d2006d160110b081480d00c1c0140c00040e040040d8945041c000c515803c007501c0c10b4886e07402010800e1010983c076145810000c0c5040b000601a103200001040403460024020621560080b18250340d6810200e0540c0201e101d5040c008070101c1000001030910b030b1220400307000440b8001085202038941c5200300c21310046060380b8240c0040180007550000c6460240c418140c00910852814a40442d540c076516007440c0c40c0702c0351901a02201c550700c900542e2120064481140c1c0c0700e60751550300514040054403121b800106490903144d100d41d007540032000041d05600c45054482c0190340217401440c0d4008600211b020307441001c039600807034103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 64266135 1250 64264885 64264927
    0x4080d0806130915060312081501020a110609090c0a0e0616030f0512090d08060f0d020f060417100c08090303042d05011401060c03080a02030a020d1b0e0604060e0411 73
    0x7c401800b04032000802411100c00a007141e0128a46c641d040c440740c0e81c0c00103a034602c85501694043e4801c04010220b00d80e80030350300d0000d03403018070681040b00003031180f0050050706010342c2d5044420744020051003490306c03a508507605580282825100400d01490104013140c141d403503c10301d04181c0d6120740d076a10000340c0d0356440c5a00b010350700c0e1007001c0e0f11890f81c64000c00201c0791424007081e5003000034078010705100002c0c040c040b001c010500d0390b5510303810386009180148034030007100c0e80305210359203c100b094035103001940350050200401b44150f50061141704171704010751950b01c83c0d48a1202e17044441e012512030850a0301c4030411000c0704140c20200c0780c440d40011411001d005d0b4250301c0d03058160840d03010001010511804280c0c0900d4043d0021445800166251586900c90010348034101500003018103002c0199910480c41c401031030300c02056900c0d4800202d400041181900c2144a2500002e42c00c1100400350310742940a6000b200b80080158500301c032554031002c0c421140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 64267385 1250 64266135 64266143
    0x70f090b07081c050c04051203070b01030b0910020406080f0405010605130c0314090a02060705010615120c0206060102070504020a1110020717090303161b0b04080d08061309150603 79
    0x208001c481a100f2206240040c503521001344190300d801c3c000010140a01d10a052042034500d0504003048001e00c215445c04e90000805d00642da1203041c00b1420340400c2e102107a2030f05c640c0605060300c2015100b91401c0d0784460780c810b4030ba40c4800300640c1d510b03000a071055601c1e56942c140010705948600620b51102403001021800354a81d04001c1c044440072558040300d00005402c00079042d41c0072404560555044884544a6078035040c11401400c1c16081600c5000c0b41c4582d0507a110342100040260300701101c0c0a006180c20000c04076150a0300381d500b640547c0c040300c414031013481c180e000740056010500d084007a410080e20f02620345120591031441c81c5500048400501003840c00f08284001c05880840c82c120725800800e03606e2049841d000d59000189058000700800403550500020340098002d5a044c1c6400345580258070502c10202c0c54440d01a0180055000785522481540000d22801d00c502c18170700320700e02800c0c203000c2c122444042c81c52031a290307203003a00c1404069801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 64268635 1250 64267385 64267387
    0x30f010c0e01090f05060f0f130f030b0618040212011e0f1404080307120b060c06071101061a070302070513140a060506090f0f060c0604050d090806070f090b0708 71
    0x1c800160401102c0d4101502800d80c0090502603501d40800702c1c0c6491b40e075170462650320104101445000e000c2c000340c171807980d00450000501402e0038601001504d0090040d890191648030400049140310410f5203440c101040015025152810855198010480000c036811038400000c402c0550303c4600300c042290b44585c0011011058401d180c0d04045d00080079045040a0b110803645010040c4800e04000791280903602050341034000e040c0d0305002402840c0c940d441c2090694640e01c040700d52a0008800e010030101c81a014021401200d19010005203141c04013403846a0365444818260154401c000d0009110341701c1c1d5402d214090744500c400510103042140c600c52055018240b01d8003541400c009000315940d1104540ba40e0104544c140070000c0b10300c0220f0074040010f104254000c0011869a134110004a80d249c880d5100783c0c19a869114040000d50b040e200b68064042c06a02c080e0000c0c0800d0b010703410040d4120380d64100b10301403070354402188a0b40d50000704205c882d0301c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 64269885 1250 64268635 64268657
    0x30e0604030c030c0509040302060a02070203101a120c0a03020111011b051908100501030906060801051e090102040b0a120e03030a0204030501050a110d0c0504050d0b0708011202010507020f030f010c 87
    0x1110380f44e2813024200440e0403400c1406d1548000350340360303006003005130030650000b0030a00715034040251008105010070148070500540005c13140807164520164080d0700e4036007140210000128594840d00401001c00e000700b41540c0046580800c1c22030614201d6584090701c414031020301400031070940302a51410b60b9080030300b80e00b10b603461818051005201c034942c240306d800500c55029100b911028600021140041c1c100080501013543c000001c6510b00014400e21000300c004102185404ea0180c07625a111402c02c5401c1b44610f201d5507690040c1840202081031142a0500c0300c0500ca20340480d1000303640011504591055a01038606607000804000b084401c1c00792641c8140000300c00c00c1809404401c0000f148180f01d1041880f596910b40c0c411014020400e680c0030b803501900c074115917401d034900940c04820030785210002c80c0d40c0b600005410b0b150b805042600b030341d069441c1800c1280e0b48e420f005c00a801500c0c0d040d4140030381500c90a21060900ca03d4425241550361114211 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 64271135 1250 64269885 64269893
    0x219080f0a0b010e070315080d09060815040207020612010905060a170705061c0203040501020909010b0703091e030614041101050708030f0601030605030d0801060e0108090d0c030e0604030c03 84
    0x52100421525a0000c1c82a003011a048404841c1141c07080030501040e0395a01108078010407a11001c0c0c0381d4109180c10100741d0040004075900040d070583c9450200310b0700d5032000e54409508031000c003022034907030694405600701500541001d07480a00501d05042003298000311100c0241c1140c503805135158104100c600d040c1001e54000d100c03150640f442c02c0385001c00300b43c40341102c3c020a0301078500020030319444040700642c0410701c400e0403000c6440b801c1a1070018041d50004409070710800d032040000c5500c5a04000b194890b43d0301d13496258203185420f2148000c49041c03e003452420101c0030002010980c1c171701519006050300600601a45000d25080c400340381111145410014140b00031000101d200040366001410401c03210315a5441c039004030040d1034940c004035018015606200301880d04180c400d41a80c07145d8843c1030520b0080001119042802c9901c001140d001440c00c0d500c090240310344552503030007483c041150324a00008506540e1250b40304454100d403500c0100240 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 64272385 1250 64271135 64271143
    0x108010b010909050403050d2708030109060602010b060703180b040b1e0313060902030a1b030b010e06060d050604091b030b01050301020a051b030403050a2003010905210403021908 79
    0x3d0704500000300114240742e10010100e004403444558040d40d00e01640c1c0c80e0b00742d0004072520070100c00103503181d4004c2d28034095200350401e21810181e54100708010907040d0040c06a07180125000e0801d81c1091000c0d2811500003400302d580c80340c070b0101040003142100d00c5c5001000034001c4600c02c640c0e04c0c501c044481300072140540c030151405100340148203661001603d01d0450340e400010205040c0007074000242440c802d00c40c01403543d0345050320006019210340b100030441c0d01030045402540e80e501194030011004840c4194056001c000c0440917401c82d81c001c1381c00202c0034000055034503080e66000d886210003900c5140240c01070780100100030800010902403c0d081c1c0c001e505000700d628002d0054000d1203684041c851646112040000c010001d4600450b080012201200803e003010042d601d051101103001040c1d0b1650480c85040501a003812154043d009080034000d03e007840d10300d13100b42440c2c5141c090701000300202503680e16544803242c1940d441c51414151404100610f4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 64273635 1250 64272385 64272389
    0x706020a0801050112141807080601030f020306090c1f03151e060509060304020609010c051504030305180d20010e011506080114040207020d120e01120213210503030108010b0109 78
    0x9201e04101c1451104441681020f0b00940070403842100385810941288c1010f6880d08103202c240b26807000001480551184481c0e5140240e041d00e0058480101e15500c42d0690034905800c18030500c0d06210041c020f11820b409010245000a428091282e658030704600c00d0744403100c4400c0084240441d140b0b5406218010070903404c0c00b5140041d10300c0030800b14080100301070700c240d40204552841d84d020b2010803c070f441c3e00600f520012322110221480d442002d450582c0000d2412000504d0400c0441c0d5a58070106194000c252020000e841114a1070700041c000510300501130400300286424002e484441080c1000402d40449444031019402520b5004404018403100100070201d04c120355040140000c1d1005070383c50b0703441e0000c5506198100c8009002d4500c2403882109140d2050032543c1c000ea090743c4056000e4146035402c01a03004840d800700c0c4c4000c01e07680404c11099250044c5040e00803441c07021016450300e82b69141983c2090780314101c140d4403191030505943e805080880 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 64274885 1250 64273635 64273667
    0x40c060810061209060b060304080310050a06020309240721030b01050f030402040917030402090604050c0417070314150c0403030905060a110d050903060a09030206040f080706020a08010501 83
    0xc1103031500c040289080007000c0f41d084099542c4000d0301c140b05440d0800100004043c7c5019a41c0c1010b20340085254012942c0502c40b01a11501007a0f82c90b2041c8914101c4006a0085050010003020404032034035005081880c0c104400c050082d02c15a03202500c0814003039500c40054001790011900050605034003041014a001e00c8140302da80c00505807540f51191013603641d20390740c41e4800310380100030024004c0c0050201e40080c042080c3c2500c000c501c15071090310204000c0d00c9802c03e202c280c40c02680c0d82d0706095402e00080c040070625821400076042d1020490b04080d64035110b0040c04c2c4614050720480f40c000006001d5404648250150080c100f050054035051031518001c02c1041c107802441d20138100040c0c0c619440b4807130804a15410403000645402056808003d02180c3c811210a4024007030000042c86512580c851418569055000350900303036501d944034100d9622442c021514140d091220002042252010b08148130380e54031031050550400c00050711486504c51041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 64276135 1250 64274885 64274911
    0x210a2a050a080303040b040c05031f180825060c0302070309060e010f030c030f0606030605010e010c0b010302010503090f0f01050411100f03020a05070212010605010e0a1208071a040c0608 82
    0x440070b000007180e5200b604002201c200340c446160412400155a11440d030610440c81104e000d9107841074240e00e200041c4400b0070407044bc050561004400000340a01090020701c00c65040b85052001122103892111001130640b4540c0c0d5108222a07064209000103a804038159080540000d8881e0140c082c40c10109542e10190000034400700c00ba2940e04101500c0b1807402c4080e80c06500494070003503800310705120a98a801e03008006080610440b400600c40d0301c0314103c01c0d4050624124080d070820a03400c0c5d5a030030340d001912180c0c00649000200d01c10300d9404068860305005008106400400204140c01c150414074089006000c240f0702c80c50b88441c02080c203039000305030700d180c0787d81e41e00f0090307103801c2814800d949601038028042d42040e02e10700c8c00340b51203c040d440007007983d07000d032982500900c08406110f090201405062602d41c080c181402c00704542c14043c015680c07290303504000c881440d8001100c1038100b030314100c43c0d90303402d001e0600540783c00800142c0c1c0550454004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 64277385 1250 64276135 64276139
    0x90c0b03090a020f01110a03030e070906050307230603011203020706050a1d01021e0c040609090c0605090a05040606020d0e010509030a110402040801150906060e210a2a050a 76
    0xd50748690501e18024450041c1c40780c010344c1a4000c66403250320030b1614050703450444280c00c000d405004206001d41076406040340101e0b221000307101e104141c0d500940140403160500001600150f030081c083c0c007802c100010205a81e85c5d68000840c080c240d00e0003c1880c0700824900640b518810713401c04800c1c00409d0141100196005000301e01ea9501e00d2200000d0a1544005031304010b040522074440941e8a02142d1051a0000d801846800c0998042080a6540201004986844900a1080c20003100801200c0c0c41080604a100c00c010540da0250b6504c000250403107085070311070b40c0982c2110040782c80e803640103262420740e0f510030300323190703103032140310000285c5841940c0c41c010710311301e00c20000350710580f195030694000d800d07200002c011000e58106501c4002000703101c0e46100c07a052150219070148602041003c062002c5c0c41c41d001688007410380840d22000710703480e8100d40b007001c5502000c102010b12080c4a07030303008007003004940c2c05800d02014854454004900590080d942 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 64278635 1250 64277385 64277401
    0x706110d08040803060a0905130302061008030f1c02040e011503090b01091107120201060e090d120b03100c09050414060d03030504020613030b07080f0f061003061206090c0b03 77
    0x1158081e82c00744010380d070b80c5e99a100242c011911500514025407611040140c52380085501c0c0c41154040e070216969aa50120f04c07054162617401550b01c503410600c0303641c444c0c0040740c026007118526088041c99071003940c94a60300f00d030419803140c032180b800d000040010602c104601208003010345401e001c3e01030143c560003030020040c0f06a00240c0d680b04a151003141c0c0085c15502090b5010200900069000b40000e02814040c00b0b021840400703000451095080060f52018035200364540802026090461400519003804202c1d01070007036820b0a00402c030603101e00e2625a80e06e0b1185154035050200713000484040c603038246004810002808190340e06c0600034110980e0600d4081032039901c610103c3d549024003203154021003001600842004243c0c010144904010381d9802c6a503a00d03d19403450041e429079001d511a010140402c4050410701d91000000e240d60401150050303582811400900300424140d50072540c4480e0390f0104050322030070300000c1440e002d001d400e604150107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 64279885 1250 64278635 64278647
    0x7050706081302040f09050f2415130501090606050f0f0a0c0506040803090d08070c0308101e0305011b0f0e030c04020a030507020106050927030f0c0706110d 69
    0x80d4414001c85200060494148126a44800d030740604248905514107001c00301414003020300716420b0050f048031954880d0002450000511110f500306072444051000b040071503406003034525210940d80c55542d03262a07401d140b10540c2600540001d066240171844c1d4202e0380c05402c44030410000b0000c0b50400c80e0b41600703079100500707410580c81c1c0e1344048041c00da40e5025000300003030990054504200902046401541c400d040c00d00684104580204003200c61640482e002000301d0609000c1d080400d1051008990082c0b43d0205015155240c1411600c690211034507a2038001c00344a0910400c4028051040c8500d443c020480c0150407124001c1c150480b0364100d8001c00000b80010000d50340c0420038442da01c0005003007190b542e1040030008028000c12203410003d58201200051a814400d00c4548545c800303c130a10f500a00c8491800c25025001845400a12042c0b03c0400184e00c1e603001800c0440b411030060100d0340c82e1280160400c0b40410501c502a04010148001d00d50016 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 64281135 1250 64279885 64279889
    0x3182b05031017030c160302090a1d1009020a0504020403030503160e061204030e0306060303180f090c070b0a050c030402040f020c01050106030204091409030921030c010203100803070507 82
    0x41840360316960b078201c900c00318440a0340b180002045002800c1414840400200340c1580c0803810740386070501c24003075100740b01400c1c800203404c040c14400003900d281040c2d02000800309003e0380c010b05800f5412585242803518109a4221641c40942804500e031444458005000958055003440e04d144c0780a081404028030b401f0400502d02c0308070070042d1080e00822400100103009540741c22040d0094819068211421404991724030015040d5150010310a44900c20080041d4948030300c031252a802c2a00000b5140c0e0046410401e00c1c003107554151002d41b05c0d03e15030b0809511042c041c240514040d50282056108902c0d07d0140540e030b1985000b104c1d401501603d0100b000d181c0d0a860000921815200c030358694603190000c00c0140d8550014401c69400c82020302c454000780794103003a0300400b80c42d01981e039401000344260a0400304882c8058060042e40c01d03089900444681d8110f41c0300607a041e006941c00401c10021200e040e000c1005460908010341c00c20240765901640c0740014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 64282385 1250 64281135 64281137
    0x4090209010501030c0c05030a020d030506031522151a010801060905060702062205040e0d05030103140a080a0203130e070e0112060503011104030c0504020f12040c0b03182b 76
    0x164502c800c2c1a00580034102821342c07120480ea80c409d400d00e4005e450300e002907020300029051001054143c5800511510300c0c0c1110203221340b040d00c0d04500a038008140310b00502c001c05500c000c44000c659140c0e40e0b6074800c00c0428011411045c4080039440300d040c1c010341941070003000c03001400826480031400b0141c9a05681e00f0759503544c00e00024800d4000c50100410b1800c540058900d01ea0000440404840041c3e80602403c003410300d2198481300000c50780400140b0910041000c80c0c216420b20212a40400c15280d0215103500e6550865110f403c4030400341e403001890601a554422000c0020000c8842d032001900b80b2000c0103000e41000382200703040000d0390307081514501c0d00707a126030001c050082c001c00111003218002c181a400910056440d996150f100065078103003802200d16102a02a589160501640300c20080c0b000280c0165106d680c804404514003c2c41c03070046000780f0355000555111000b20240b00c7c030700881202c01c4001405007400000c00c0c035030310048a826041107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 64283635 1250 64282385 64282391
    0xb04030809010b06071b06020102041a0702040f0203130c0503010b0612070306081920060702011407020301050a020d05070e01020d0e0102010b090103080a0f050c0a030503040302010914030306030c0409020901050103 94
    0xc0d820155014101c500d030b4180d804000050340200b04103500410b106d48400c4881c0c4024920b0b62040107900700e00542c0f080c9600c007001c483e12095440301c0000103203420352006000142030045503007090300f241c00c12203d006134034107950303145003e2200c118908001014114000d000315080003000c100580208000d505180c4401004124401c0c0079070040300141a812044a0b604010f580807a13a5464038180259000320605080c01d0114031203007041d08151070060070781880c22080340d0045403503a02c940a00f8640080c00d010f0343c1d005a80a0050300c0c002c1d00000009038680760010f10074004c1720400780030304061080089048141c1c1e600481c2c4601100c1003820036612400103071300140e025003811080b0b01c0e40b140350880084100315418005e003900c08244e41ea02680000e2446c0156080c0c80b42c06946c001c030307510003425000028462070042da03116200b0310011a1044407940d62000b517105060502c2c640ba08044100680b41c2030400c006400c0501c115424007061410b500454030760074041c00303540c0c10503403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 64284885 1250 64283635 64283641
    0x72c06010309050609031e0306091f03060501120201110604020906040506040902040e0a060b01020607021f0b03061905060604060c020d0503041205030703142a0111040b0d060e040b040308 82
    0x20103980b2401c0d11a070003806440c0341d403034140b060a0301c84c7c0c0020315505212450812440201c0c0e009001c2e24480c00e0040d0440c02942c0710766080740707a24000994800303080c074103550001c070025030f540c0502d50007401a07840a641805d030510014005e0428423072050640d511140400c00135a903055003007500701c00161030000d02ca40b219004580501701c480000780d0000d0901107200d21900000070f100c0c88860280c201044192400d40049844003001e40d048001a882440880c0d40c0007240381403110304240551000822609050100e8280311048031401060003141081c2001c80b0001e0041ea44d0005003101c84034905410844081c00e40181100080c2c09201c1c00740491007000003c004503030280a030b07041c140390121a40d10b0090f41da50312440044000584081b900c040c041c45801c150380c04001c0c8007150340100903110082c0c0e0381401d43c2c00c00382e401641d20f0712074518a030103000e0021300103400400b584c25500c2c450700407840e00350340326984041c44c005040313420000400d04460b4081c5d0481c1d45440c2500310342c0c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 64286135 1250 64284885 64284887
    0x90c0d05030c0706050d0506040b130209010201062102090a0c050406050906070b040b150d02010804060f1103090a061a0307050105031905010e01050112090c060e010c080d020c072c0601 81
    0x10241842c5003110f80b0410f10041030380354014000d03000300403944c00240007654605080c0810385030342c4412140c00040c0607100034401d00c201d40241550b07000610001900070b03551808100b0400c0c02a40440d003040311810b003d015420708040c0301d9484800441d003030150409000b402004d5110b5407045d807040085c0854a07103c1a0b4403030003101c44842e00000c0b2104a03081c58103200ca40000d003030301e031445000030448a0550904060210385007042c1c058450f00c07e507030b589440f50000781521000c42e03081b40c0c0d65011004c10b102c2c2408041c50017202404001c10384210545060411507441409550500161940300441503600003a00340c1500d000707283c0343d9280d858115002510700c46111030105402e0800001203841104400d800381218401d0741e444003400004807600701114030044018060000c0c400c000d10000d80070703d00381c1c141c00d4018500070000c40d4864031201c1c0b10f5040404480f41c855000541d1900c3c0040410100001d403400c46980c4285d8620300c00e84110005001013400640500780c1c0000c1ca1603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 64287385 1250 64286135 64286137
    0xa0f051011030408010203010f0e0705071e0f03120b03060108060703090302030c01110a0e0105030f01090506060405030f07031101080c0301030b0a06030210121d03070f140a050a020315090c0d0503 86
    0x80000c1d44100c9031200c3d00d54460b103010303410900450b40d008032a80c1c4000780c2c0c003040c0602d60f03003c0c0d51103446080c41c01d002911000508448440e4131044090320003001000162600e1803440303201c1c040c0c1e40e804540754003804604140e03540280050321075441040140f2401c000800c50940040c00d81c140058190003511b010790440c001c8038011080d55103490301c04802c00010304000d140e07280b503643e40c14000302000c0006403031500080e40c824200c3c412210060000c04650303400305800c541c00421990420f9a00c00c0041e01d0303d100740c078a1084c0758200c2a07082003003140981c0300007180002401c214a01c0d03c5c0110b0450000d000521018005111001c0894804800703907108101035500600210042009200301070110b4100084549401e8904400c0716036103800c4e01a08500840301502942c60f050850715007042c0325080103816601003403006001404030108004d0401604e208001034040303100b25004050905c2419440441c600c40740000b0000c10950101d10341091440840700c509441840d410001c1c91 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 64288635 1250 64287385 64287407
    0x30c0b0304020307050d03090e0106080f0a090203070503010603151404030503041e020d03020102072303090d061103090a060608011406040e0a02040c09050a090b01020d0f050d090605040b060a0f0510 87
    0x100c0509403e4106041c0d000d001d41c809daa142202c04005a41d0754001103940c00411605c070081c1032301040200e822440c841d000382800c140001c0444070304a8a840011707084441d91790080310001c9100c40320281e007100d50300440d540b20315003001090740c82c80e207501c020f031071440000e000902d04501d240c8050040700c40100701a1419070054605044901103150182c000c1d44080c1e01585c040c400305000c000c0960484c44070741d103801c50420265003408203a00c148007070491111b4003190529224185401d00d0110b580285216403003480003003400d180942007410444070b641e008000645d040c03500ba807070b40a0700b030301c1e40b107070005010307180051074062802c5054100507800d6002588141848060300c00507500918400a40c0c2d81207460540c450754540e44242180d0981610324050381104003600543e03402215403200b4008181001c41ca4070742d400d00b0200c111a80d240342110610b540b0360500041c001d4135100240d00600079990140c01c0c500b07040d00002d41d00744c10320030f252080e504600c40781070103881201c8842c6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 64289885 1250 64288635 64288639
    0x503100f0303080f091606050f19020a03120513020d03030e01090305250f0b0606070c060801230d060b0301090803040501050412090e0a050709080d020105040b010807030c0b030402030705 82
    0x62510382c074005141c2041a0f68009000340c1c507001042c040900840c1d40707000040620310a8080c940f8112007503690341c01c540c40032a01082c1c180070703c000303810b082c04c1000a0411079502918040d150703032801900a01d40711041001c4240f811041041d918406604030007902e804640d20411090986022805802e884030032414a5003480d034010100364214020305032003607990f0070180081716031485d5903000107030b401c4000e0300301411000064085a403100030b80b5040200501114074004813070310342c00c902c62180d40c0310800140840307004211100300400c10b11520f06c2280b84688a907901b1000040300c08080e00400341c0340665070b5003450702c7c1d40d0302544841451a0f202111703640701c6c40d05042090081008036000d4075103811030205805038030f10a0340007000342e070681c960030401901c8111041c4000c100080418050254215012400329810408045200010383c004101e601d80707032034804819841039100080381d0340040014400918480c002506450004500301c2d141c2d41c0c0e0303000191405c2001c0c0d01c059 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 64291135 1250 64289885 64289909
    0x2070810020d0e010f0902091501020a020d02030703080406021b0a140906061c0b03010b06090616031202030405030901021216080d06031b06030506060306010917070f060e0307090e0d050310 83
    0xc000554603085006c0701c3d402181d4141d5a81e844901e200c0301400944d10490058024405400040c6807104071138019a00180846596a03241c1e40c480645510a800100241c1d01060700000c2c20000110008261102600e041c0000c610700410759501e82c010794042d83c071500e0303040c000a0558031601e054a14204540381d000311060842071000000f01340c000f0031607020b03500300104002c480c10010103c1c0c83c0385801410b8036140160315a148100c400d00841d044040088480c9142e1000c0031500146019900401c06103a86903c014006031404103a8020802c14410621212140350200c856081c00c55400c0000315950f03a104034648802004107410007001821031000c50f20050642e140400c003500c00300c0d1400c02540e00d0b000e00304000c2d0b0004803060b42c00280c2d41e5909000381d0050310300803c8810b40030801c440c420383d1109072190708480c241e0042c40026a051441603d140b504020300350080980e41420800f010700b2001e400c0d12a0082c200d0b000920500101080507002061414401091160080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 64292385 1250 64291135 64291151
    0x5131103010b041e03030e1005070204020a05090f1203192705030706050c0d0e121b011814061303060501060c020424170703021203070b0702070810020d0e01 69
    0x4521940141c040c1280d0204e2154200c8a0300c402611034505594141e210944400c440c8420400030500e00410f000410106100340c20040c0c48074009801c8041c0d20362642174a45441006015114071444107052007040d010f600d00400e400c011044032401308100c032070f00d8000042c014041e18040769140d841c84100c04400e00c10b03440604800c82441c01d49504030281c403e0540c0d15141114180036109d1000d07030580240c803882c043d41e4040d048403401200050403246400016011480c184594480d40d0181010100c0e0a14090f42c0c6c0b28510341040700d2000380c1c1c1209a42040c55054404828191035409840001036803482c4420407280c0340011a409082030100c1c0d030310703090028602041030604a00590a04407070240c0441e2110303800c00c480312041c6c500c07001b032480d0400815459001c0458000c1c54081e142012016860700b10402c840725480900543da6030000c0c2c50818401c42000b000d010454018200520000d0404030300d0130300a0040e05409a02d584030409258001c0495810b0300840d03601e07283d42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 64293635 1250 64292385 64292399
    0x40e0a030f030c02150f090c09220c18090311030a0210050c070206030108160b0403030c11010e0d0602030414032d040e09010e010b010212070201080901150308031005010c0c0513110301 81
    0x18030987c000000c0c0ca8104c4414000d10032040016540c001000c440e150095018100e914841400315004074024200c09a403840e610b1384503a41803850030030031900c4403025000d06420041000c250032107280198901444500000e41b94181d04017154001c5032181c0215a680008001350380e210b80e0000c00c01035495a4a43c10303140e6030841401c2d0700a4100c0c01c1c07200041d031001003000f610111b82e0503899150001141b5681d1443d04001030840e035040c0300c50307102c2d24078042d00c51010503507640d0b20030540141d0b170707061908001072507a0780c1d0003441c100790344104003c15040c0c056011140c600504209140074203181070808039817070b0080f0341040320205003540410040b0201500b00c4010003048000030480c1c82225001207850310700481102d0100d84040000d01c005500c2003008541c80600035000041c0001c043d500c14142160542c400e86a450001c41441800300400c00220024407003401d0001c172801056451480d40d18881c41107505c0340021091045400003290820540409003040d80d9940390703141c0c09 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 64294885 1250 64293635 64293661
    0x405090903040609080705061206040f020412030314060607030c060e0303160e0a060e010f0504080615091e040807030e040c1e020102030108061303210b040e0a030f030c0215 76
    0x3080f0000684001000140818081401c805035040508400c2c81d080c0400d0307500d404028044d02440d042a07403140c82080c2d226051025001800e001285840da0501c2c500f0700901383c0d40d100c62565003003580130f4103100c1c856580108555051340c1c1400c2c105088151410080020030440c060b0780b1241c00b00000704031000044503081c103414170250f04c03400c510310340e03010900042c07094500800d800310304100107040340c0f0341c066030407180c030000c02d441e045240981300e09049050100c1910b141c600008084503002e03041c9003005140d6444026036034020210b04001c0311107c0c4070f00c0090000350040400154190034184070703440c80004914040c000380003038040e00e0303402020f14501c20501c1000030180c400669401e0300c1802124100c4d59603000810450700c91494010000c1848070040342888101c90301c0d560700384140d040c1d2049042d0004000074000440006210680e42ca0000900f42904000c06640000360090b41c0251003220b940b6000a14064001041c3e20345004280c1c12400301c000b0204100c02845004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 64296135 1250 64294885 64294889
    0x60e040c060c02030709050c070f0b0702061b031906030b07020f010f0b0102060408030702071521020307020607210e0a0c080703030c0818042a0e060906030c040509090304 75
    0x30012156881108840c05624403000030f61580242d80e040160380020b030401c90300115801c10b040c0c41d048560391101c48095505004a94952200c000c000b403954060018035445060030036030340e24072060340e0602003141c400286101901601064000107542c100c0e44000065548520f4210481c18000030180d44c0302d0301704030740783c106609211042502955500aa10045906800624150b2502e80c1c4241e12500010300d03500c110712406000103884150000410301c44ca02648403043e078107032100d003407140e11912040881e02c1a8010018848201c1d030000724668000742c1c501c0c1402078994200155540d4040401010b1429400c0440b070000703054022034114001e0740319020503060175581c0d20131039458032614440500412050b2131018003240b480401005603000707000181d0560306100700043c2c1113490201c030311680170180394550343e116100740d9203d8003c9240c50910040c125100c0b0001500c4ac40380b801d03a18001c1c4404008141035261300e5080e40d0140c0802040403000b0724055090315900d4104d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 64297385 1250 64296135 64296143
    0xb0604080a05121303060203040807050d08011d010303140c0c090a15050d030806060c010207020a030b07030f06050a0b0f0c0d182403020702030a0b010810110301141c06060e04 77
    0x740007031000d00260f4040310035040100195400e00f03451500d5030070080d00000d0003552400010043c110005905110311102c401203511200d0603075041250403180f85690648031031821a0307610041c40402d030021541271076900740c03c0107070f641c1c0c02c00c0c0c00c001c6043c00c80706d6107400e4002c6014000c0c0004400302d0b800040ba203080408403800180e64900810224002105019011a0613200840c079641011401000b11121000c000362802441c0d138041504a54168810b44070f40d070824083c4449180e141c051503c8005849405010543c01c1900040c0c802d42e052080200c51000000ca2a11030001c0c00e040c0c981080e4480141d455801c001a0040e003c5520030940c1c48031a803400c0c00c04510400349080300c42c0f01c802003200b012241810742800350003c4d4840c000c141c1e07051045c200000c0016121901039806004240080c0101c80450800f10003600c0000c00940c5401100344014003210244103a5180050760449a04401211401c038040d0741e420b8420024141ca802d040d404101e543c0c0c2c01d00c503c1e0045100b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 64298635 1250 64297385 64297393
    0x50606010e06040e06010305041730042003011515030c050406050304150905010f14010602010c080609150603070306060e0402040e04121b06060806060303030105060d0c02010b0604080a05 82
    0x1c402004100c1c401c6002d800e0100114002043c46544070703511140d03102d1b1068080a44080c03850320115825008810a4000300140d00c66175008100d205070300f400d000040f00a24119810941d540756414215078044d104142c282040311034050340c00f50009038001a1501940703007440c0d1600b24103941401c1c90307220040424141400700010a00c07c4045900712415550340c981103896a5464034a01c42c418034030803050a03101c49400010600031720442241c0c00e050400055140c3c10b540c20702503401c105038002801d6900d007100035007640340c00c04407550388000c0455500640d5950300401c500e80b00303012522035400480110400c80034a03015407000c0283d64058581941011910040105902c0780f8003e092601e010100854000f603e4206440c0c1809120304003c81c8022500424605040c06150251503003038a480c008c0022013030511100344c2050065020718995070521010944900c1104113454a045d6114900404e8510030340c44250030550086c6102e540719038501600d5500c0130032a10070344050203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 64299885 1250 64298635 64298657
    0x3030914120301060507020406030614060405060f0631030308040b01080706090605070c0801050717010504020309150a0b030a060e010c020a0c05240c01091703060604050f010e0d05060601 82
    0x4000610841074403000c01400745181e00703010084856800a9030126000f5450302030110014519010700321020500303083c210040c1c0303400001c0005651010b0081030281c1c1e0003810346078580c1c444c04112082840101666108040024007142c15800104182c2510241c140408410540d0040c1114020303400740744072014030390b2101600e40e1640d03458800e40c0f000c80c5c8502e00420400b400340001e0308003580600d020405a60380c46a803a801d5541c103c1c0d9120000308071041d189451002e844405001d00340c1950111300f98034003151800c0d690320280034200071070b0aa079000100202d20a401105400c400075040c0c90402c14140740c80e2014008044042945508210391a640c9500c0041ca02c0c499640040303c1c800c0c1c00b407500d0b09126500703030683d800200c00c0c0000d180e0546140b141c0f100402c8506120742c00082e80341018240314052138808141d544180e0010000e021950b520b1600f0780701034681c00c0790741002034001400142e60b00220b41c040d182c0c100551502d1841803000c0820074522400d030a8030f42c001003003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 64301135 1250 64299885 64299923
    0x207120305070c0b04030302120a0507031109030d030510090c0f1706010c06051f03050d1103040e040809040b0306040302100b0616060b01031d070311150a03050c090d030309 76
    0x41c1c0d04440050000d44160a1200032504002c8100c0d0000d01030b04005281812500703c00100440444030f2515244e00d420601120300d62521030b4241500341d40b02c015041160101c0040e455000c20b0281c1c60416480d003000c2150111154946401040821001c224413045200c0160500c403040b002080030442020110003000280c6150034070845059603084240380081c3e940800500d0083c010344416000d02940815801d8100b05a502440c051b000400080c540040001e2208801c59911807083d001030104101d202c8580c400c07940c200b40d1002c0100d807a118000b011030001c103840c0c03004640c503200d080306200c28140c003c1041014542502c01c1440384078100800d020a5100d6070240401080c2e6860780c442c041040340d030000c1081c0d841454003181c90700b1031250722003003e080300da40401d41d900080c10801c1044640c04040d21401c8058a01c080180d07840c00030301e502c074080c084680c41810307212000102181c450008840c601c1d10014109586c201131800c1c002d00070b0076116012a071043c0c000701041010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 64302385 1250 64301135 64301141
    0xc0b01120b040b04150c0905130c0917010207020a0b030f0106021c080a09051c0807030506060a11100e0a0b0606030c1608040803070303051504090c0b07020604080a0602071203 77
    0x1a58100d075000016480b20768401c006414020815220070024501603020713505039001d6a04440c80a6075058541405c050070003031424180030f04030750540c1c42c0286103248035402680e80c80032502c100d2101003805000c18040d03406441440c4000b5403000e031901001c2000607106001c2c2d4042ca4001c2c1108056a803210416030b603661060707485150505031122215030040c8105200e0340d1000d040038001c10381e01f8581d80d030300c1c0c038218075141c401c402e031380c02d6081c03000e40c1aa01807034855011601d46014002c81c20444081500d9114120710b03e42080800101c0c02543d02003049440b80000500404101c0d09840c1030b5580d45400d0004411251415441c0200f800d40c03418105490003800030140c80d03890280e903c0317103101c50414007880440710740906200015030030000f803014101b5039009860100307803860300300301084400302c042199a128034a4554660041200007900d181650240a01c90380d45042c0782c00000c3c15030159922105040c841c3c8020324040102c41e0f000760607140d114124184010702c1e40001074050f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 64303635 1250 64302385 64302419
    0x2101110307031d2a042309120f031509010305030408010c03060302130b03070b030a0501030b070c030c140109050102040306020706050c030103110f010c050105040b090d140f0a020f0d0c0b01 83
    0x13580101c0a42d549000e00d40314011000d4018440ea40d00040d00c071000c1429241c0841c03c500740f465124100c018449090090107a101c83d8100c041d1110580c00a03d501e424085c0c10740c00c80140d1000300000f80c4450707560291812240c0300400c0c550042da501d01d41240e59a1060198010650070802ca0f0140da0f8000d01800d4280e907401401c41000103044000500280340c61032034070783c0c14410418001600e84010000313500800c2c840f0f10204041d815804c02d181c1010014088008100d04440c0303080101394020580500290f0011500c1480e01800c10428050194000007030302a510002d4004100112a4001d0807210710400d010310940d80e0b00e0018000900091101422040c1201d09410300c500e009041140800030506101020010030340744c0c1421500111012110001e0080c184015210200103c00c018516445c2189032048074042d041018000c201d43c0312095080800e00c0c07400d0500a20625101701c00007802c49504d600300032001804100b5048096401d407020341c0c0045203640c0510901e4078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 64304885 1250 64303635 64303691
    0x31606090902090319030c020d140601060e06030415060512150f09120d0f11090916050403030c08090d03091509140915060a030b040e071202210111030703 68
    0x20703800c520003e1001c050300070710201b00c04101d003081480d0010b070741d100214401140161004a80e0710f002103146441d04038182c00c40403d1000502c3c0040d030f56921581281c0d0b006500080b4410710000e0095180301501a541081c1d0348202d403100e150102da000010030f8000c3e80d2010344401e009459410149520070f405482100321a00035000c11085e0301440c000030440d8491440c0001a421106201a01101c2c0900e03990b40d044840000c02c0101440c04010441e008840412503460440d240c0c5405046c61185210007001d000740f8801c4e100a0004a10641b130201e94054a0082e001c6402e10380140b08402e14050300044070341b40d0703a800b400b103882840c040e4180c030b00c0e1304030305541c0c0d0342c0314010084010700080c10b801e08080900c030061a580c4400c00900124a407903280814a2002c0c0002c07c0f0603140d0310400440e0503070040c142007017044050114400200e8043d2051100360700300c9050301d02d104d1815890248c2640c240000b101c20200010300561191803035940820000b83e46003024000940c4803180f02c1c07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 64306135 1250 64304885 64304893
    0x21507080408070311010911090f01270608010f060302100503060303030c031302040c020d020c04020c030a030209031207050606090606120712090b130614040309060e06090316060909020903 83
    0x180020102c070001c029081c06070420228500c1444159425180b90034421070f81c2c40c2c010142510142400854182c00c1081c92020700d03402d40c1008000c3c1449407100340391038601203221128001314203c65100b44054017940009010f101245c82d0803c000d13103100c0c0b0040303004604401400070510f10800a4900440740140603500d10f0b2a00c240c0100f81c0c1d040a003030081d0007007800290f41d005944034401c107541c5120580252079030711010507020381000c10841c0400d01950040101c104000400f10450f00501103604005846000c900e01007440e104080b55100e042200000d4082c0a0150000c0c513144550000c0740c24600d00e41d2064107008040c080c51510404033540c0c1d00c0441d141ca8040c110700d041e142c40300385000800208544600d60a51800e40300e940c0d4041105c0c1c105001d10601d80210903203141030002100303d600f400d99004221807958403031082003199038245c1c10306541d07801c0229460904010112440c2082d08035060304440b95501c10b4a01085509400081c0d0610310b0003519000c1d0f00040285c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 64307385 1250 64306135 64306141
    0xf050c0604061b140a05070915030c03060e030909090615060f16050c060f042c010b0a140c0c0f011805060318061003062304020d0606170d02150708 65
    0x202c101c04401a5085548444c04601801c91500030044a841640680c0040043c18680f510750011035401441d071140c82c520300f490a00103d0501c42c002011a94094400a4400244079885045000f401ca90715807000106050020a0000040103405480d08500241c03840211b90704001481c49404010480d100703081c0400046142040c1c000c0030700c0d9010300700340e46480003840002607140c2e008207525440c4030008902442080c000c0c1c80503001c581840044c002c545400f03828103410305001440b035080071210004907044110b02c1054080c42c034006615a554031222501c40564880401050382070107501c3e0f40c0d50048039984549544842d80c0b42c03800120004d60301304001d10a03079a10007062000c0160951401100101c02040b10a106400803803900003080e04500d401c1d8203135000102403480704c00c2e40841c40504412501085a0490740c12035070000a2505407400c00080d0003541d1060155905680c1c4200070b180340455114a040d415500356403000c01030820701c1503c40005d40702031001400d0a000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 64308635 1250 64307385 64307417
    0x2060402090103120e04020d090c0503030723070306180b0703110313060e03040303440915010e01050a0e04080d0903090e090c010f0806031f09060204030f050c060406 73
    0xb200b04800214a8a140e107002d8081c00f01b4140d03070090900d0b0544070740d20110041404601e901240180100320003a628244040d1580000e800385004030701e81e1218101c0c941d0180c40c5041212000a41d8014030a1007403014010040003100305000060f51810510700025460911a1040c100c500081c581800c1c2991506104464098840c180480e00166101008982600204081c000552103640c5244100031600f603c2c0e0880282080315880030009800f2895600120092501100c003003081c0250080c3c0d11040414504585070115844000301d03000085000381003244160b060340e0040e5551541c2c80d0796601154417071641100e018001072810b00441d10800d1f09070304402000c5000b0b00d8411390084d03d40c2c4640c20456000d980355509a403002040b40481d58000e55002d040750301c1d4ac144a0240e00d03240002c2901c0c0c1417010b010381481ca8080b04142c1c042000ea0f4020030b003594204c881103481d942c591614110039401d41500391420b10880780802d9040c41c00c0811901074a000303940d41000020187d032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 64309885 1250 64308635 64308653
    0x50105030601120c230a020d0215040308060d1a071407020607080904020906030c09031b18042603100e09100203190504060903030507020706020c010c0c0509090a050106050102060402090103 83
    0x4400b004005c88002401032a0241882d40004240204d074001d0355a0686c21020b842c015008042809540080c000e140c1c940c3c105401c11588150941003010322a40c6202c0011880110071a0080c04d504803c00140c40c508041084c4910900054880c4d80a00200c0340c8101d10070b004941d002980281c04010310000504008082d24881d24007500c0542020310060000c0d102e03801c100c81c403410350003001c181c3c50200e1404110041440c000c08100071001080200410820b0030b045811a411044202c08242006407000c4c08640041c4440d55401c1503252620320110740798002e44400c0318285070140d0100c0c00400754a440e07409419484002c14003a1189407200000e07400040016a16900d14140e00c0304251550154a21551103200001b03003940c6940f402a00b01ca0300940a402190b01c052003e10110341c0008014411103c2400c200318082650f1806480e80030580e00042e0f0004442d0303052003c80480002c4201042c1d1249000307011107600c40e00126540c40e8100d9000c1c2d4014006401000403804040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 64311135 1250 64309885 64309901
    0xb06030f060330160203150f0a020405090c0c1002040603061d010e010e0403050c010615171005010c0c09140720030301031203150f080f011404020405090a1a0109050105010503060112 80
    0xb18407036500140f03600000d083c4003000400703a4101c41c2d0581004101c82e0888d000d2540704141d10011414581407101045c22500d00400350b034030718240010002c629400401140c00100c00d40741c0199983d0751200c070028080c1c580d44c442e04142010082c00102d68084844c94a4140c41c203440301c1c6001d41e03203440865621038001501c2501804020000d40503240002e00039640580603106101c1802d2001e442d0090890b44400c803460081d120300400d010341c80d4484420007088034403d00c1e0815207a20141041800c00c0215880104100d04d41a1810301203e02042414070030300286c0c8606a9220348031424000f010021071058005400030030041c00084c0e400003030514050305500e00040e034169541c14254220209420015a4141000c010001280c0c100b1a540c8400144402840b242801e0301e814100c1c4140640002d100e2901d84000810b580001c104132403400740c10030980c074059180c3c074842004540e000e0060b20f902c1414100003150b15406882107900504040e5107820380103400004d40d1000307007101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 64312385 1250 64311135 64311157
    0xc0506040620210619150302090306090d080903070b070507080408060702070504060501050f030c030c070515040c270e120a0905040e01090804030b07030b06030f060330 74
    0x403078003003110b00724040302600c405001e03034920101a4180f0950141c02c3e0b40700800c61482010700c05201e441d14002c50807201c085520302100700c2c200c1d00041a054010380030303003045207030540300d00710400030801c400040c11650602280ca83c680141c440942c0305859100d04680505030366540808103c403107115100402410313000d00001030038691510002420407009451020050748141c106000500d01441001c0040c0b8003400c1091070425810f0700c01b0581e0200821a200d4a50084000ba01d00c2d01884112119942e000701070301d20704801c14071502d011440c19601680c84100c003081c0842c4001940108222042003925030882d04141000201e0240500c0582001140a4800c06500d80290074000d00f1174062152034441889007400c042c48101e1f801180309250744e82c1420402c4001c41e141d01c00b140c0a03640c100d0b0b18055036950340f90056014120201c84941c010000004002603c500c1506031400f0350005c41c03c0d184500c005c5603600b160000d1401c1c0b40c1c400402d290303041c00d8508624000070311070787c400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 64313635 1250 64312385 64312421
    0x506180a0606140316060906120b060301030c0603050f06090c071110051b03130513020f07060204050f040c1202070f0507031a011a090105090102030702041505100c05060406 76
    0x14594468058400b00e03800007a02103079031504010745282c01c0c03003961042c10400041803411854030314010841d000500c596002d210400d141c2c02501c5580d40c0004040c4034010344190b580e56960324110360046410b203c0c08000920b0300010031006840030103028060036000b0409007503600c4d01090241207601180741210310203111201039446849103154086c003250325884045d101d8048003104112180c00d142e88040036001001091317070b608072054203074099039001d4880000ca4111410140024802c0420360801003001041001c10003025400178401c0c0c42094550090001c90602400252003084003a54042a9024074121068145601825015000705240c2e14040c1d841d4031018207100107074000f9034840340c2c409200214900020380c10340c0100021019045107110000031410700307014414141d4100900007864241c240c2c801c01c295000240c004204201d0803c1075051900d41c1e10740e910030a4002c1050941820440c0e004405d11450550484040c05a9030740da031b41c40000510022220180c0281 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 64314885 1250 64313635 64313653
    0x1a031b010f0509030c092e090e1606050c030c030c01050117030915130902070f0204050f0103032f0d02071503061802090a031202010c08060f10030e01061a180a03050618 74
    0x4005e031418064140740000b00d80640c0d00300a0b41c9001c0c0c4403458440380d044c0e03000290100c00a42c51031184400c0b1007080c5001b93700d8250208110781148141c01243d40b103480701140c0007101d02d07019031211f4100c610003210701100030b40420f500c5841b80111030350300d6801100e08490030700c0e013401800200480a8691490320803103440748e440e00c013280c2044005480014030300440f0011070902e4814950002c00740a103040d00782d031555400404545912407007400400103d40118001b481e62261401011030500c15104100e2210034001d564002d640710703502e241b5290034a05e0350014041d00c142429140c0001180256600c010444170103948040c041c140c000c480c400001000c1000000d003211f40182c598004280300b843c100000342040c40c00b40035244104504d804503203260ba0f8503c080d0f010100c943c14042445000e00c01c90b640180b030307243d01c0321031420000324010409c85100c0004061840640b10321a4180c441030f0144104942180801005076202d0340c08207100c40c15206811084200300c404881000c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 64316135 1250 64314885 64314931
    0x30e09060904031b1b091a0307080601090903020703170c0714060904110405100801030501050702011b030b01090509010906060305090d0c08030c070f0b010302090a0506060d1a031b010f0509030c09 86
    0x9510b46c000c2420340e0341d0341c000c20484c0c0e10081828030304130070482c01000010b09000000c4e03181d10b030601c51150015500d40b03079403081600074081500215000403400c00c0380a10780c010900207911048030400300d4010b45501088840c0b8800d0a101c80002c0507103010f0810413450b0621000b41005070070000d201e40c06010001d03859440c025000b05503501030385c1340d640d10b502d0b61502e6425644c002d0400070641e41011821400d2317510620303c0000d0ba028916001c00d05000c0d050041c5c494000c1d81d003095030002c0000002142d695182d8018604562240e079040256613244d501298448410342d100340300090410100a003c1940400a950850a4160502c0c60f01100350b5600035400c50071101141cbc040b4a12004100b580780035030049038000301d000c20603c040d20780300300001c8c1a0304c101400c01c004942e540020304007200d80305c001030781d1446000c1c084504004110003403220302c14001400074000381c60031051016140c461400d84040d0710002d8024400c1004250401081140090841c0400c1d68031200b590014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 64317385 1250 64316135 64316183
    0x1908010507030207020a06030c0509040b040e0604050f160b0405010c051615030507180b0c0f06180c030a03051207051c0905070506070503040b2104030e09060904031b 73
    0x266010342c9005075180c41d944103101d100700c520351000f4241440c0041c420400380e0414110381d40c0e65000ca4001400c08000c07800980280701039040111540308030b40400042140004100b84003860050440d03494030040125030b0300521290150b071a03504418842081070354000d032940580300d48200c065980c1407600c94501d0381c83c000903602020026819400048481d0340611904e40c124206c1d02d400e03003003480c0c0ba1410040071003080c400e0343d8442000180000700b294083c803011443e0502d950a541c4141401c00c0100442c00ca01075203400c060040c041118501d103000201012159496207034103042a5160706403800c00c100041c800414080100225030b1411000b9145081e00b80b010200024001594100503103400b031039422207070041104014160200328000300399800c980d40d91001c19610010f50304401c007510481c003e000b5848094000b80030816420000188812a0503203801450ba83d03488104010050203407005004200000c107031081c0443e01103590503195014090040c14844014001103103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 64318635 1250 64317385 64317391
    0x504020315040f0c0b0f16020102120d0b0a050904030c030c17040315050c0a09031b05040e0715020d090905040f12031d01090803010608151005030106110a030e19080105 74
    0x510b00e001080501000300b0300d13040002a0100081e904d0034a4103046582c1d40c1e510480c804660034591142e40c5008581c42042001e15001c041050b40c1d0702c4da00c40c0b03c400c00c0908800296248551424200802c00d1f080c514500c41c0b00b01c0d0142c0e100c0541491710f1320180e40358025100243c541503030408100c0c0840d1480801800191712a072204403030300c074085000340e085460142890284500420000c100550f005200d881a00d0b0016070380b0700103180c80341d0741c4e00c000407144c0d0001e80c00908107240c1040101c00407a50340700b22003064642001c40100c800302283c507580c5100000c80402d43e6444d05015450040e03105641c0700d8442c4400042440030394179204404040c0e0702e004000641c56000481004e280d22950201c0b45079690700030b001101c0b469959007901d020501403030302082001400100e00d412911140342c2c0801e806842c4400c0c5410107030000300b081d4024000d460211740e003410112103080d400203160f065941c05070b6401c910135160394100541030765038100c5000200d003001004038103042c00380b0403140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 64319885 1250 64318635 64318643
    0x20c0303070521070807030b01090b0306121e070f060f050d020a120f02130803030103050615060d020a050301091d0d05030a0e070f03110306161b080a120b030d02030409050402031504 80
    0x103031510b0782e401008e0720325480d8800d041000210741002144840c0f002e8035005441102e402e42112201170004d0b15141c000c1561030b25140c0c4450303c05034460320119001003611040300d9075000803512400300b81c581c448401d0001000900410000d050350159034041d15054490380b4120310200000403500c001d582d800c03600343c01c401e640002e1600c0340c021120513440050401c0000b0318159851611400c0c0c44040080540300c140e58100030010241da9a04c0444009402d44a4115129030043e000140990800d0040b0703680c1500d048814032001080c101e2a0060214150042842d0704150324215002d400162910204541740c486c2e6001169060054030090017000810848551450825082c07182da07051042d170086d0411814400051000c0c0761400c021020340c2400c60b40c4540703240407050050a80d00010309000c00100d00039000325481395206002d400101c1050007408d00000805444031515002c03030000da8401c0004221600c0c1a4100300c1d400b40c0001c007914440c492449141c41d0f1040101c030116 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 64321135 1250 64319885 64319897
    0x1303060207061b081f1404150305030f1801140a03270807060f02070b0a0908070c060503100f0501050a0c0c0b0307020d02011404020a0302091308180112020c030307052107 75
    0x862610740c2c1172200d410910024000d400d4451800b200071504031001c502c3c0500482d228801103500c6001030000030011544902140d513104280d2081c03030481d410041e0862048442e003101510700c1d40c8612002560603840b6074015207004540321055004203015501e600b425a42c6245c0b030100e8002c02202030b9190360241c0e0300e5540d1440c9038608001100c00945100f061a8410300030580400c00c451240e50780301c6a0030800044000b8103080c280210b01881e80e0091920810010125403541c2c0300010f1f50065090511142d03440741c07104e501e02c5a010032809950300054003407003a02c0959200d05076001c1480e01500d070980c0210f481d003184200310341c0211000c00c0540c2c4032402e4100381550920541b41c154100ca58a0f40d06402c10390b0000e0342e805440e10000c1c0c8505031a602040041d401a03c1d00200c1c00e512001c4c142e600d00b40701a0303a0380c10344030034a0700501256003100c003500351a405000b02ca2914000f0b1001d94a196030b105000d80b65030b080301e140490040c00c07001d0014510448014a2406502c5e03d8540b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 64322385 1250 64321135 64321141
    0x311031602060f070e060a020708030f071407030203030d0c230309070b0306090103060207020102030910030606020f061618030c0902090901081902120c090c070b07051303060207061b08 81
    0xa40b80c100050014194001820b00300074040e9484150710410000440d00c1c02e0355070b40086400c920300402c07900618a0382c040001d541001ca6105002004118031610048810b410a5910191070700306074803001c0d406400800c100581d080b490b901040a4110700d00701250080c030070f0302003905940140b603480d84503c4030000520254801c1008440018502c0c03a404a00c1c1d854035801260140006100c010103603500070840034116802441903030550b510107070110110000c951001000340040d485604058000e03101d484007074040224106200e05800c02d04142e0580030300800700d6130160751070201040101c2500380440000c0c0b444441c6d80040002420140c0c55000000c1001131240041e8002b403001d502c4042c0480100b000d01c07441846080e01107031008400403811000c41e0803d80d2650a555020f0400b10420011584600107080014000c1d4460a0b0503590007005840911810304440088a080c100410008030030b90010a11030348140310201d0144000a1030410003201e0180c228045040c0b00c1c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 64323635 1250 64322385 64322387
    0x3120106031407020c1509061c0b03150609070e0d0b01050a0506070321111303120c02090f041a0a0507030c02190b040501020c030403050307060b041b0305040303110316 74
    0x2100d01c00c02803001410b5040c20640390203503680d01214807013070280b5540041a41010503100035129041b40c050540e95071f030300b20b040070b910f08010a071805200c2e251409140c920b01707040001e140400d6007101d80c020301d000d4652030200460032600500c7e107020401011245e00190305d88074a500026441880c60480a50408040180c1080c01c2d41203540150740600c940c070046a88000340f48541c0070120645075605012032000c202910031010001248040001c05008042c1d526008030b00f00c84c000e040e0b01d205400807071001c071030107142d810011b0360205a03040441c0080c1921500d4540080c8501d404209030b58203016220105641210b00b0301040707603181c081100541d0580102d044100d5240301904c528002140709451b002c4002d40b0203009014010000380400500b581141c5040b800c0e1801c40c1d44590b1b0302d142956803544040700c01caa0300c5080c086507541504240c0118056150b0485020395181c082d06811801800010010f5040540300c400d18031044006400440c09450107000284c4038880c0d00d90 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 64324885 1250 64323635 64323641
    0x140103060c020c0105040b0310260610030c0509190f090b130804120204110309010207170c0a06050601030902090708010501090b0c0705060a110304060e120303040f081b0312010603 79
    0x30070410354006a0100480d0303a404021903094070315061406480c0e031a11616000040b0142c2c0008010842c02255a416100c0402c891480503030007104994403030741e500499100e00300342840018400c027110390703044c0411310701419503d82c4400003068030440005103a1600c400e032107001140180c005e41d81e03c182418000303000c0c0c010740d1080304515018842c0907a965140405e1045200d00030380241ea5901d40310443d5555080710701c05030240d00e000790f1242050200c16000f5806081d0844011450b040450308030002441555080540c150181c02500f0182d111100a00f10080030213040550342d8800c1801655242e41c0c00d8000c651030740c2c03003410302c0d0704110014101107841e8010242d55803051280460041c400155401911300aa135404c0c0ca80362824000d175a2445119031880880c00049008205207a002355124002c101c122080801022100c949644922080c0c40203405040b2481042012683d00001803a011150a5003000201e281114240c00e40c2c00c5408102880803c00004005065040c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 64326135 1250 64324885 64324901
    0x204060509090a0b091e06010503010c0f090303140702030a030905030d0504050a1e08070b0705070e01060813080c011e051b071b0b0705010c02010501090c1209050703050114010306 79
    0x99158081401c110803540c0d5a1403c689005004901550014800c11802e01c5000844810034145002900c0d62080360358a54009026850084d840c0c010030101e4248035610b0040c1402680d1150b18105082d901d084560060071219051503c504014240060304c00304806c0c1e0a040c060b41c0c2c2d0b241000c0c20301c02014208140c61464408004062006000b156695074184046402510740403016100301d09902030210810791107100e01d40070381c1c44001425501c0c034004000d424072a10541c0d0380661901103411190b0000e009400002c0c1f42c250016420042161404c42114000c007001803c0c003450840c410300f903c2114040900b80070715040f0608480d461401610381019901c4001e0700101d0421703a20180601800d07034058080d01c12589c7c22841440c00c2d04001e0301034600001c03013503a02c00c1036043c514040d1844c0e89000d00158a40800060813401ca84a000d107143c0840d5101c010b450320906e148000351001c48c00c01d44150040202c00000a00244248a030000442840003019890360611204803800708e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 64327385 1250 64326135 64326139
    0xc060f0305060a1d0a090b010f1401050711041a030106060c031205072309090c210601020606120111040f0305160501050d09030c02031e0c0402130b0a140f0702040605 73
    0x500041c401038a803013041100803002640403528030b95503200c2c002d001c0c10b45c0d800041c102404000c00800c608220603414006c0c1c440e070214440000c440c1da801105c59214101c0041c1c440d44c082195a0142c5c900398215000c1044841c180c2c4100144400010b0308550b0b079940240301150b0340780c256008041d00f0480120b06050341081c00c21107032070400c10143c0003011540209078116083c101303420190a0400503200c059501502084451400c5503405080b944440e1802010f540f5114220f50600500000107100b5103042e4007078200740d2106403d0048805e080000281d040d501ca00d2528841e4501c407020304000c010003108107580c43c0c50f506220741031001088050058100151042c0b0990341c200c01292182480035900054405d200e06045402c00d000800080d8540100705036480d42d04498500b420034030a14101381d80e6015908020030049200303029030400e040125210402078580d5070b4016000058132820070002502062100c20580d40c00742250f1014404041501001e40c105403242001400017 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 64328635 1250 64327385 64327399
    0x40c0503090c031c08040f0c0306050105090606030403020a080c0307060f0b190608011a1603210e0705090703020903030c1015180f020c0d020309120604020904031107030c060f030506 80
    0x30344e0040b007801d400c801c481101480003280100c2d080010072107603440a01d810501c580c6110340c992422901a10003841103500c82e0140034040382d005d140a5003120f0180364160001c5c0002c01d82580c80c41070503009401c900481c0c0c0814086c0c0c002050041c010059003040029000503840c50000800c18810642040c2c070007000c0f0f04100501015800044081c1950004440145003a80f1811014224171602901c04d10181b80318003c07800b0076401582c180d040e00c0314840510380b103a0102e001e180807a050003114100ba0780c050781c4108900d0400004054109449241c00342c64030700020b02081c40c1d98001008200c031a441200a1814a0003d10a940449030060071000f0180c0c0307800c4031f61450100440c450540e0554810200c0402e0140f0740c1200e604e40d103108240c0c1d5080546400c060344a8110704204c03030044007040d80c107000d2070b0030110f003003031203603900801c4002280c450f9201101c0f203481380007016100348100c0d900800810212902800140358a070798040c4510160a0000c00740d6002602081c0174582c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 64329885 1250 64328635 64328653
    0xa0203040b0a020d060506071b1403030409051005120601090e060c0403081305220501080102030403211404061d0f1915110a0206090a1a06030309040c0503090c03 71
    0x80c05280c1c1d03801000c00c04000da1180107001e55000100f0903648480e50090300003d200d000c0008828030700303812450540c102d11115540b40d244902d14159201c5c0781c2e0b17040d00104024002e0409642c0035a81004003440c0c6500100d454101003001d08805005004040d44010300400103000c007401041000498400030340010304090b80d40d244107010310300000f0550b030b1020941005801d03000543c1c000402c00103100b91140100f06440304540304054000c418070354141400407410074014001c0303034040c5515690302d48445414000e4042004059905034421580301e40321000f80c1c5c840c0d2825036026600030341001a00151a8951200a85182550010340e4102d0346030006007000115a411074006141541c1c0e04015552828503107411140c2c022580c2145001c10001c281d00e50980580b1a00c902c640882d07510745c4681d520140c0d44e541d41100100304500e01500500072100d42c2c11300716000b81006d402c032800c0002c0c140008050f20000e0160301c00084001c420402042001c205180705d1a01c1600036040d0b980c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 64331135 1250 64329885 64329893
    0xa0603030906080910060e060102010b03030301030203120708120a020d060509090c01050c0708070b07020a1a0304061a030a060b040b01090b0415021c02060403030b01030b0306040f03110f060105090a020304 90
    0x8030500c902c5050140704800074505500900503202d03c50003003201040070b1601d40141c042c034400e060b1043c90040d031170324100844c1d40c200002140c4c142e9400500030030003502182004030181d03000340d01c02c50303524006210310341d01c002c08105054060000c6060150721404109298400c60310307690b210701c0c03081181d80c0038800c101c000801c4014000d1420b1a2007a91014110b50710ba2500c1001d51240c8601d1180c0c840010703868041401501c060f500c211442d4070b12650b2900140c044012020f00e401c10000c003000410001041640300b0030035003150042140181031103800203403c10591031400c1c1c0d000c41d01e0720707030820503454248200c1c18030030002d00f0b140e8a5a814a02080c8460045000d00e14517031404000c80d04502e4000c000c050b0301d11442c141084054080060300135101c2c2000d4504602281c00c1c41c2c4120034640c0203011b42f01c1100005002000d15644d16156140c644490f0203081d018807014603018110f034034043c03192400c241900801060341d03503d007405204180354010320704101e41c0d205005100c001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 64332385 1250 64331135 64331147
    0x6070b0402040b04060816150801060206150d0609030302030a05090d0c0308090a020a061805010201090f02090a090803100501020f061e040c260c010c03080c070602090a06020c090a060303 82
    0x2601520001103c4218001250003405550003014107403003a42555110000301500e41d41c15201442c0e10000000541d60041c0c5a01c40b0031701070100035801c40000500460100e21612248010082908603119241c3e10358000315559410141e0002e9000401c001c0c03110340c4c03801400c0d001740e0214002d0156040d56007000303018401030783c001010000800c01145813030008120381c002080c0c0041040660303a50391400640441340d0b0f000d040708080031039100001c25600610589010642000c100680240c0310350803c4603600c0014217000600b942c0322220f00124000034042c5101c1d40c1d0100b42c4600442c10300b80060310f0139200309040c0255900001c1000a0b41c03c40b42d801d4200401904549d900d183c949141c03682c410b80c80341d0008a403013112683c0519603e2400c0c82d8002e8034840c0407081e00c01e8480514011075601d6600103000c0c01054000000c03c2805010400504c260303809a40018107108201c00007600c09032069202c0307001644021920700c2140743c14a089600044d0400c001c0100502d1030790f0150107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 64333635 1250 64332385 64332391
    0x11b050a02012d0b030a02060f07020112051303030905010e0601090204061d0612220302060414190312060504091104061707050f0111060906091606120c050c070b0703080606070b 78
    0x542a1528113038100d40d1002c0050809035680141180c1d2500180003081040c3e80040e44140c0c002041d2142c41c150b0318000d0700c2a503004450690141a100e984c9072001d44c0540440881121300e5942c600f0300603444c03801070221601a28a902c40560b541c1e10b003000c000e0100c50342e030365201e0702c5108001024120b0741c0d529085540e100254000f4400581c9e540140c140810300c3d50703415a9143d48d0f1150410200355020038054400d0f032154241c015072412000640355210030500c01100a1129400e0b15008213000c0d041d001c10258440d88041b0b8101e4465000c14184d600741c1c0c001b07c41070041545410500d180c0b40c020040a00740f80801081032501741000c40360f65070014810700b80160180111103000740d2140841c1110180b000d000c481c1c0700c0c1070454116640312800c8609030000c0c01461420901099075107042400c0380d0b681c1d82d905180c0311b4180040002880081c0e05801030180800048200c4107003404582d00402c0c290300714070b46900c242c0c1806040c1c50f1000748442d00c140d90800600c00080c2e61084043d030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 64334885 1250 64333635 64333721
    0x1a090d0f0f0c09050f070c02010c02090402030106080f16140102070b0a0903021e100e03070905090709051807050a06120c1101061518080705060c011b050a0201 70
    0x2500011608207050054a501c4014000114800c408200542581c0091340503000f00110621641e0312038400302d035030740c036000700c001d00080b0260700600140c0703801e81c4150740160004000240c42c9a841c088289042c0c0200c2e01c0d8140c40d00030782e040f80d41e20483c40008100600000440391602d5200c540001d4907851240038103464200045110401a03110b91031800c0a1036000c2e0620104101e910f41c03031404807002e040c243e84aa8200c520b15410b040c0300d010050040000500180000e03400e00b800320000e407030020a20f0140344190240010014040c1c0201400703415580740c000700300c440346d608450078181380303400c828025165801c0811041e6440245d0501c0c0d0341c844c120014010b84c0f2444100d40e00e1100b0211156213600308103020030007202074089888a0001c5856901102c9540c0031801c500310028400d005098101600c1044241400c0c1c00602954281c0c0000046030010803582c2d1110356100c406900c005000802c4020b02d80b13409104840e40507803c0f0420305114a002c00f8804141320001d04490 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 64336135 1250 64334885 64334903
    0x711011506020a0323040b04210201050301170a05030d06050108070801030507140f10031a0f030c090606070602120601080105030318010f03090609060207110a030f03030c09050d0b011a090d 83
    0x10119004c0550b5000419840c86074061b0f80c3e9a40b0500d0300b4803504907020302c0542c0c81d940301d4040441540702c0c0013000400d5040c1c4030b441c02c1d40e2030102000c1015003810340e49802401030181040c0061002d20051580004503440019180c0c00c0c40001003000e03800a1841052118680050010690014210f0300316050781c032800b60720600101c003041000c50003c4855030410090003108155640507081003c1d1000d001c90300c003190116080400003140c01c10a0215056041140c0075030075400c1c01003625600c0702c00a0245880c0200d5a0b03120803c030b0f80515660b111224102d0148003a035070303102c841c06004060440007036051a11400d1041010b040c8101d6183c1444466200490344a0107600620202c42d0800410070580c103090501c000a580034010842c1c40720300c900391001039032403d04542e0081c1c035041103480c00686180e6a0540007000003400b690248140001d0004141d0350b611000c2c141503104402140055140442e0100c800c030b52026820030241042c0030341c8090b0740310114413003c699000601c0c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 64337385 1250 64336135 64336157
    0x601031e06110a11010e01020a05090f0d0206030c0a1706130c0e0301060b12060a08030f07020103060f080c120303070f0c14120c0f0604020112050a140711011506020a03 74
    0x81c00200008807403990b481c0404250100e00d16040203080700c0400d10340d8003d0041c01590030346c140c02c0780700350007410f40892002e000d0070440d030a00440c0d45006410150408010b070700960006680c0b40c004a441c807000010008500d90031641c4400d00341000e441c901d004103140d003080c10000710000e40800d83c1c001030301d90352400e4502040c49884d140008080c00780081041301d48882c448102d0380e000008440c0c403a8498404243c4074103160f03991001b02c51001001d5070801c07100745d4099085510000044c0e040513120200490f44a41c1c0b0f41c0721400800000004000d400c0215040c4070fa089103003900340841d0342062081111058000c80c91a4400e4030501c1c0440d07008440b4034100e0b94025011848860500c074680e00540400c1c0e0000c006d15010f1241310440306200c1d249000d00f951005c00310340007130000b89128a2502c000b00340f03420a9421602d0640c000c00d20030703401c0c46400600d40d0120303140c400140c8400e45031000006e080c4601c02c006190003070011107050038500c001e50b0b62991010001c040060000b00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 64338635 1250 64337385 64337393
    0xe0103020f030c060f0409060e09030703050c01060302040c09091802150d090507060e090a02031515070f0803011a0301030b0c0f0c01060f030204050c0a020a1106040f030602040e090601031e 83
    0x240840f0301001842c0d41d8458000046054143d009070040b0030209141000c089152060070340f903241b09494203802140760204c3c943e021143d54010b24592811992030765800710040c3e445020724440310080d0b039242d0404038070b813082c1e560070760780e00d03403114490020700224090158a41100d010054000095842c1e42c441c048030400b030040800d4113014081d8042c43c0d40200c0c016900c11f100001c10031040716030341038944450719810100c0c44243c1e41c1030700c5007080880c10700c81401e1040d001200d444114039241d04082e005d40720405c440d00540030450709074600100503c07003944002d041c010114030020341541150304650b01c2d40025035010b0901d940186000c2060b150b950414030442d039071092414002c2c070038103550b08002800d105060000724880e5060000003201c03102038500741e07035002446500510050a064490324100305075440b10301d802c04402c1201040d002032010000c801144240401030303441c1c1c64441c12000700c0d4005050911160003040040011402c4046403860a402048428811400d1490 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 64339885 1250 64338635 64338643
    0xa0c0e09130818120102040806061e0913020603071709010902012723030d03022703030d0c0207080111030405030a180f0305010903020c0406060f051b0717070f0e0103020f03 76
    0x95642d0b10004c040020714602e841034014004440380402102c07501c4c2c881c14200301444241c03d04201e44400c038a00504098903040c00788a410450101848050540d2030b004585258411a10314021481c998104425500c03000d0b404c0f0382c464420002081680b505038002004818481c040700c010740e80c060000c0c10024482c40c00303c0000e06a84000c3c44040707045d6040c550f20b600074190040c3c8203008280030090400cac004c0c001c49007020045030280c001005007040114042c40000e004640600c018040c0fa9445802e0b8840c4182c085940d8004120280c0342017502800c2d03500f007410f20142000e0034800d00c170004800009884016105080c1500040c4000d0501004010290b0240d406401c00c0c0d00008284181076203c050428020b03401e4171076191011044c40f0071f07038409201d1400011075200e00400203078071840281800ba0390500002c480603840c00385072441d140b0306030081c0041142942e80d80c1200c07003007044803070024814081e9800c06107103071441c2a070700c2c80e00500c80603015200c00d444c481c91940d800c0c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 64341135 1250 64339885 64339927
    0x90307061505120d0305011a0301060c050a060203090a150e03040608070c021c03030e060115050c160605090907080609010902090d0b0a0608010b0909060a0b01020a0b0a0c0e091308 79
    0x10b4880c0c611590810b100315501d402a0071300301c0209107080d002041044112042c0c0c8103680c0321408a500c0e40c0d00e0681d088a030011503a209070323002c0c050160b10740002040c40c0002e5001d1800c000050880030680c0c2800c0f0300829003c07404400315072400c14110b0f20490f0100a8a040300d8181c100560385035100d600603100f20b4860400290f2095201080d0f6a00b9400b0b9100d041c80c582c000d039404c010600300e681820360368140a0240810b0040045c1d50074004030710840040c40440c410400340d91102c5910151000c0c00000f40d0000008907a010803640d04505040c2c0a01381d103c03213640b03050300306400e002000c1004501d0600840000a800051003881070706c9501c061b1003140d0f84480070365030500c1e1110710b20000f170546008001555007880a01020ba14000015034082c040d2400507100c603444401d502c5004016110a003810740c060002c01901050b01d64480c1d41c40b030401c040c40400c00107891200140301d41e0a0908251161103460140980140044001706520b0b5010104076038070a810801192800070203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 64342385 1250 64341135 64341139
    0x903050609060f061c0602090109030507030f0605062d0d150501060306060302040f0b09030c060a0c060b0901080a0b10090204060905030c0306060108130c05090c09090906090307061505 81
    0x1001808220000042c0440c0301d0010b0141040041e1100da0802c281507030001218000d20ba00100340c032003ca03d041c1d0060200143c141410440d05590307035201403e002082d40280c03458148d001900041c016035001e4680d00c0b0303000302c44480c1401038280700c07840c03d2541c4c0c04d40e000c60380400008065041c0c9410180c490810342051366050740c50145083c2801420003401030200080c101180010400e019000340c405403000210140b03506410920664016000710710a0382c0e051061441004140e00c64500402015585a6030307480c181c00d0303900305101540c403650f0f005402001408010001d1400c0072808910030365001c180104a0b881d902050a0303108410f4100c1c40031303d84002070002c1c81d43e401c80c403044c080f00c100b941682c00314101c000030181c541404403822400300e00368000094600301c81100d108003052083c40d82c2e86030151240007244610b4011075181081c50000100c011591404280f820ba010056030003c208503e00002029241c1c0141c190042c8910b880d2741600300b5070101c541916000d0800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 64343635 1250 64342385 64342393
    0xc050f030109091202010e100203060f0a060207061103041a03060409050105070207170303010510050c070305030a170a1a040209030a0b070306150207050f09130204110901030606032a090305 83
    0x50761040390040c05820000ca44c030851980960010b64018014855000c414201a0900c02c440e500800d0182d070000f00285e0703001e1002c40b40449035544802c194005094103034001c00b903050034120050201c1c000165017207007983c4244030070001d02e6401c0c1c4200b810ba41c07039259083d40382c2d1210804640a020818001406942040200f1540c10340c00108134007210340b0380c0d081c01d000c0c1c02c54410840d220710086c011150800d1f40403801542150140c002003c100241e842140e941660304c0d1925410741e04417024610005042440c030a4102c80d001c0144c0740c00083c140c07000c11001192001d1003c5140103140e00030300654020401000968051040110540d00b000c040b00303107803a00c0c103c018020031050042d4110080301516031001284002046401d0f60009003000c228008070310108030590000070004076810040125010040e141e41c043c1030300c5005c0f034031011a100c41c1c40c900054161a0f0a4012104240c68500308200c4644a0070800501d183e42815800081e40300400850f1000c4264001510b1481 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 64344885 1250 64343635 64343639
    0x12151107060905031801050c0c06070f06111908071d03011401170f060f0a0906024e010302040902010e090c070201080f070c030f0302090d050a020a1d0a0c050f0301 72
    0x102c048005e0030307035194005005107100300244c0191554041c0c1041a816503000362095000360500100405501c0d00442004060810319542c91082c1c0e10304910301c00c142d0202081400c031418020079150030540160402400501d08024001c0c481c01803800494082d03582c1d41000410343d1030a5010382c41c4094078000c015465a100e2100743c01650280290310114031030300310541c0c201325000c030f540d5008140c01c055200c0c05441d9000d403c00a401303980e0060750600c1d0308018441c0c40c0505206c1c95003101000100328030303030040807a482440a801c0c950704d003c40d0600b681400c229100340503a4140c15640e04590010703601e5042d0004a0700000100f01c0d058006100b181803040910f41c450242402902c03da03501d503002e03030318461102003140c01a80c2882c046501c45142c2c0e00082e001d4204625846021f24005041c004071a0008140e450402c03010780b92a044081050290305000c01e0000141004840d034040c0701c42207417404108120024440380d40c0e80e51310641405568403440c22200e140701c00e100510b407296 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 64346135 1250 64344885 64344893
    0x903050403021e06042d030308090601080106060e060c0f030703121a011b110303030709090f1505190e0c030a05060108070e0d020a0302030102071b121511070609 71
    0xc0e100780400d07441980c424026110701c40324510090048140074150b40e0920380791aa039060011040e40e600501c8915a003080101849200007501c001c2d8020755450019040c07016840f81003110613080360f0840d034140002400f440c0c0d000000071b0101c00007582c0c02940c500141e88070394200350752650807820501002462105260344000603c0c1c280003011070802991000003182001c0b149000b1100d07001c83c6400450800e50700c1000b840280550113041a1503014050400080c01c5a00449580c8042110341e0010702000301c0611842021050103070041000808001c0401e45440e00c0b03100b240d05c04c151464404800030b8a40e0803c1c4010a030450080415040c984100300d001d8000300c600003481031a00c4001403556214a040e140a00015103502c5074404615040c45510000c900040c2e1b0020540080000103071005d20040c103109005608090362464804044219000a6030000c4001d0741c40d00e041c000842d0075a0b4260a43c2454244006103801c401140034245000740030b40540001d1401d0b040c4401c8c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 64347385 1250 64346135 64346137
    0xa0f0608061201090b01120f0c0603150806060d060c0908010e011407020c010e0402030705070f1214041503020a11010207030c030e04060e0606070515040c0302010210020a050a080415090305 83
    0x401d011a8040701900b03030900c03898202c40150310003a0904002e00300401c5090040c2c0b24600c1124011941200d50300e04546800d140800c40381e02002c0040e0307682420745645414517804e00083d041c0e004c050719032400e065000585050130309401030049a41ca6040c100101e008000d01d20040c0901c034000d00c880c40c19600c10a000700855400f0200d0303d4081c20010b000c507072012a0080480c281610b0b10310f00c1100850a001c005c0d04018080428024100002004181c0203041440018421360075110038840313070800142203489a960ba00e0080304107101c248624402010240718480c4603142c0146c541a40640440d4141840d21403103a06520000d5007005150340819205c1c9a20b0082c1c1b10450140c640c01c05200450300544101c004034402c030008100c1343d2034284010f2850701d005004440c1030942081281106120940382156400d90002003041156010b104200076000301010850804c030001101901e00d100e80441601081762000002d0b0800507000d40c10000740759220010459201145009001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 64348635 1250 64347385 64347391
    0x20a0302010f110a0c03110a0807021c02060a03020d0908030a151403070303140f031006030c0206040f0f2105090a0f03050304060f1715090f0121020a0f0608 69
    0x55003040e50070301000b001802140c00744038142021910b4a02c0c060011100700c0e000e505d0860400900d07401c41d1801c400d081188170001c0e409100c1e190f60364001c85c4100070382003520061103a02120104851805681d074101500d80701912800c1c05a5100ba0444c4940c00400380608010880d01c0e02100340301782c1c140f03603510400e0680300a0000442c0d158660b2000144124440b0b0890341c1680460402d00001e44210750191007074108201946c100001c103500781c561a0011108034108003500d800400ca000d5050195103200340d141c2c0060f095a04154689802d2150440b1010b064542e40c0d070904810800b11191003264008a1040d0164050080d20001e1032035210404045c820010b0f103201040d8000004203540861364094029440d00389402c106503081c8191080fa1414440c41c1301e400001701c0d194070044c034030400d650440c05140540040401130a850301806e024502440d03d03005000c10b82d1014400d018a01d94900301c3c05039110345100080070418242c028400c5c04c10318050000b201c94020107000c2c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 64349885 1250 64348635 64348637
    0x31c111011070206180a14090901050609010b07050c040903031506090b030a0b03030d090308011d1303031d0304060e1e030a03080c07060609050108060c0a0816030b09090606010908010c1202090d0b0403020a03 91
    0x132381e191400300c54240da0040d2040c65010000d1001007210b40000002010081d103d0030954017221030240004048070b1180c503094000c607840c2c0380310901d001c2c881d9030120702800450a100d0743c2c250404603802c0140c00010000718000b561603458010542d800c100344e86080c5003100041c0701c1c0fa9480d140080400c070080c8071b60b07134100b5540900301c2d032140d1011070341c540300c0c0c2680d807404003c5250742e80b02207018100e8822071200d0740c550904d0b1020601000e200a2024196503255007503903c0006041c08002910310f0740100485c008011044a5954007044d400071468152501c00200c0e00c030300c02c40340618410070100500d03151414400089120b25034016034100d031820f205541c0f555840e4041420640710b45003280001442c4000001d9008081e1070040c0c1802c40c0034607000403a2441c080102c1e45e06001a15541d00c950300c0300b07042010941c4c1c400c00080c050b25817071000f130210444412000d441d081007116011081364010030b051209484154010408030b800c00d2802c11641440c1c240030f900e907251402c042c3c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 64351135 1250 64349885 64349899
    0x50705011d01050a1808030a0603080c06010312030207021012020405061c0b060a0507120915030e0705010e180402040f02120103050615010903020f031c111011070206180a14 76
    0x1c00131303c3c59100b28103402e200c586103030343c10800654800b101e40c1e03c0207040d1301201c0e58401c804408511450098032445601000802c03855056080001c0e41e8114041083d08145c0100988001a1601e00880803100240e0522102c0d080d041801040070b80107542006806c80c3c004140385001500a407041c1a404101303090400c072041c80c14041c032002d4440c04000c940030883c2041039a0001e000d084901d86440c6c030503e0414407407a290b50203c0703110007124071403a00198943c8002c8851100a0001030014642424039000d00f01c4800082900958041211540c52030400b0014081d900c664200d11a0051611011550b602c103036150001e2496081c0400c0e1400e110303100c000388602044a90700c034034046058543ca0140791030750f800c212a0049000340709030180105011100c0b886041c90f44100c2c0309469441e031030f000304100f184051409054259500107242040d4034a00081d503000211122a60142d640d156682c0d00299502001c00d014484550400600c110000d01e003103000003107155502007200c02c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 64352385 1250 64351135 64351141
    0xc0a090806010f03080d0905101b0206010510140c0a1a07031e020c03070c0905070f0306030b07050c070b0c031201080d02061602070314030702010f171303050705011d0105 75
    0x1a54540c070074025100d408a01c0c076800d00201c0c0700200505003020b140003021400101136995182440c1002001c08181ea4895078410705680c6690502c040322441c600c0103120a615110020f00790340c1860300300300144400404c00c4620044c28008640700c8c403961390201d8401426500c2e20096000c0300881a032046a814030204100c18864000c44c0020002c2000c08070055540d09013000003540442c110043d50300c410889030000074000c078155002480c002c58001010318128002030860780c02d51008070205841c6c800180001500440e00941200940c82d015454940202c40d46190681b00d4001714610300000c1038a81081100100805241890001c3c2107000d990740c90103d42d40d440c070500d2090250700840c00003a0f5040d5180005c8081c1c402501c1201c10403946d980700c201036803044204000c880c1e000040c4100c15960824251040101a40303041c1180300344046082d840c846000d00031150508a0b400e161052611650544881c0d5411800030400d084c0d40300c0204022101400709489113500304000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 64353635 1250 64352385 64352399
    0x1e08070503070f060513050d05100f0b090a0e032106040b010c0308040201080a021308010b030d020705150a02100e0109061506020d0309020604120803071106011a07030909050c0a09 79
    0x70b00842d003010300b098002d2400d00c001907a1581109000d01601d048140d00000c0715a10240306542260060300034041b0031407080c26040640b100310303145019150034101c3ca01120703220000d540341d000803180d200103528a00c0040a82c19403148840c494260201891048036140c0c0050791035005d00d504a40410010b551800151500c0c3e41c582805808184010001005035000b2200c0a0340b002d18920018a0007000821015658075103801c006140da55036281d407111414100001d640001c80e170700081c1070b000e2030700001880a0214a90741e140040d40480c514900314001c014060542c92902d00c240080c20442c001e00e8000c1401400076903000d4100000a542003800c01a40c0c0c2c142c0321036601814101c002d507001035016000c2d900040343c015000304400144030200e40c3c0303034030700f141c1c865103c0c16600d042059008201c1084510b0900c115007011004122a100547c20307450714a0358400c1150b114549070902303441c1e440c1568041a0074034145003c01411400a0001300340018058503400e650944a0304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 64354885 1250 64353635 64353643
    0x60318010b0a03120e0d050706030905060c03010b041518060c051e0304050d020d06090605010303091401090e060301020c0f0f07060509030601120212030d0b0a0902070308150a1e08070503 82
    0x1101424a050181041c984030b48140e42180c210000504024400c010701d0303031f90514140499000c10700080d503030404142049000e00404e90030600c0704400b20b055506001d200c07211841948954140fa11111001c450064055031820901300758485c14a251359685170b0000e4284000f10108981358020001170b401c8401041c2c0c00b25102d1003601d8010341c02c043c1800284a02c403d68075000b641d12420807412600003804600a03070f814148038003008121381d4914640500200d4503500001c281c0600c0c40f820f03800590b40004048100c8040241e4005c1c81c0e100c000109009100d9504240980d00808100701e80f044030002c3c2c00d908080c0100110744c021a5942d82c12180f5000364030354190b154100b107004010907507001412407003180c0014106131915482c150301a10b5540915420904e0b00d07120740032211245040d10150008068900040d0720300000d9940090624a008252030044401c3c880e01018540325030001e81d01500c00000a0403006000300f00c00e60180fa014401c0e000c06201d0104081040c0c00e005c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 64356135 1250 64354885 64354889
    0x9090f3f0801050907021006081e030703021507051b010501051207050a0b0706062301030c0c02010e1306050607081216020a1205091005070b0a15090e070302060318010b0a 75
    0x180d200103040c1d00f007508101c11198050103010441c030400c841c2e060450041e1003500c0080c008480106a00d0f1440e03210501025681a11103040c4d030000d0048101003900880c4040c65001030850b40e0340c0c81e40e07032861706544a0050100e100d4850390074612031001c0140c158041c606070342c0115108a45040d61078100b40c6e907030b0b049002d116005044002c0400030125440080c0189a00c0b4900206580d52555051003940100308028210750159107010310165130148940180c0407106e241401c4040a6600041c244900407104e0901600403400c2c055144996a44900050040100059a10142d500385802c5581004038039207a098428004102c2e800e030982001401401c7c5074001e2311080d03280c1c1c1c952403030340c20314003044100740704042000800c03a9440d80c0f01064003212540f200c0f41c450040c0d003004034145600400120005150920920504070010103050032100b420a0100e0100d074103003046800d15100d944003e401540200070720112018003250f072315000380c3d51402008421f0840040002c084464 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 64357385 1250 64356135 64356137
    0x1608030331030c170a0c0b0601020307031d0a0905090c010816020d050c010212040f03030e01060f05120f011103060316180906140124030605030709090f3f 68
    0x20090540010b40118100950280034452400c43d82c0c14200501d252640415054000035803034003090306c00c03c028000c5094000c107080c402103081c0b1007a9500a032034034011100c0d080404403803044001c00f6588000c0d00c00e01802c01c000c82030100342050074035256200310001c6402c0c0031498800020721214018074204603141070560080005494911064850381d01280c0ca0350240d5408000002040030704411241c0518401d01c1c00300c28588240c200102102c00d480b40d080e10b10303410320504210302d00c14028100185c607411500786a0f0b82c0301c08a81c4515003100096113101550900240540100e10340003c5c9d84245019000d890b2070048240c00d240c45520076014128424881c0100480e101781254041c1000510400b000a80700d1100800741043d04000d81c01808900f809203d6681380030102002c001d80c0c039145040521080b810200000d031500d41500030b8050041c0e44101c14030920403500b26604001390004c10742072102d00c07803000038040300a4103120741c2d03843c60068035145034000319801051181840c0f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 64358635 1250 64357385 64357471
    0x10203070c030204090c0e0403020c01030e191401092f01141206060f030f090f010c080a0e030f040b0a03060e07120b03030408030d0204030507050910150216080303 72
    0x2d5a08000c0100010141502c909800c00c601294003190a6440e50145000750000c00e10706e01401c0006040e1003154011800d2600404045c4c10358642da00506481c499101c10440340d4450844201e80c01000c003020080c0c442004002c42c5401c3c80d00160102500c5803207102000c060360013030b400541e058142d041901100314010000309555081c1102c03c25004100100702030b01c0c001080034a085541c00039110b61001c41d2118082c81400c4c0c1040200707510024140b0024020b011050b80080c101400c000c00740388419854008580190200348200d451150003000c42584580d181e905114140c2c21600c45000800d10f0000c0c0403c85448441c00c851207010599905141c1e0403100c80440098800409103e0305403005002c04180a40240081c1100511900c00141c481c2e1450404902e0004241c1c4083c1c011408041885506109034066800b40d881c40c2c0008220050402012071400e480c2c0303a204055a80d10703240115024501200841c003d101000800e550000d0450704400b821504107507111074070030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 64359885 1250 64358635 64358639
    0xa0b0115080108060118060e0103030806121c05161a0405060709050f0402070c0317090f040504050c060703020a1a04050d02010c1d012001061503050601021e03070203121305010203070c 81
    0x1b00c12640700c0011010214081541566081903003100e5a0a070401c5011403501e000700704090801110f480e0b07070300b0350301001050019003200102c10380102005540080000005014014404400d03440d1a0300390b0042e110840506e0b00801d2100300750050b102280c5d5030140e0707008076010324815580001070301e1009151b41c180f540e03284100802076100850441d00d420b40040d0001c007190b60242d410b5039040381c1508003682c44540000b000401508080c501e4411480c1000380801311344001761101c2c0700902a03038901d030340300f1751400c0507450000d40440051402104010034003404284e80d01690103540f151044981c0701c5d403011030603401d0300c40c19028000010b91585e06520800107a508101300882c06040c00100312001103181e0382811101c90ba041c0d2244c1d10f0754001c1010405109881e064039120b8602002203044c1400001d4035a900c588180b103d051000414072614141802290702691340201201d2a01d04495500c869030341180d0450007041c10005000107155002104982d4000d034007000305040f00e8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 64361135 1250 64359885 64359899
    0x503100e07120c050306032e180507080102070b0603010903080a051e0c070209090604030516060f0f0504031107050a09051008070f05190b03160e030a0b01150801080601 74
    0x440d00400100802c9601c000d108104041c5120b9200301c1c00703455844690703914140050500e070a00214410f03d004000c034441c003160301c0f05607840c910008044031012031310300c142c00580ca00344072062074094098052800300040c0f4040560040c0582446114a80c0c01952500c003010300300c840c2c4030809004100c00d04005000203055074810f035800302c2c100a0014070701a4084c90102e42030411900c030342c008400041c2c2c100a614110220603030004541c00100380918181e580289a801351400506190680040410800159410106c000e07500d0500130001300340000c45c0c503000741105580035004901e5001400408800c0400c0d90025180301900c1e1003101442c2001e180014800200b0191200d160044007003403103070003400745000034081e10700c400880605110400440c010484a851f0345081e040c40104262221001034070340c4464400003910055908c9a415280e1140302c001c10b95050080c030903030b0420042040242816280c09070009081503802c3d40096070200001e000b1000c0320f504c41c00c0100a42 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 64362385 1250 64361135 64361159
    0x604090f0b0a05011e02101d1501060f030c021002070b0402040e0c0f060903070b07030f09090605010c1b03020604150210021201030b15030601030c17210a051605010219050310 77
    0x1501003881240d25001c0366098441c108c07140e01da000c2a2800e4201120801e0640411082000d0211501603001035450308802401d485035251720201890344030101c041d1818001d0121540c896501001507648a0b5140303072034942081c0807141248205c2c5418030070040e010001a40c0d5a031050060005a441442d0f001000320726040448031640c0344c4200b14001c03500c42c0d0114041d00203c0d12946400301000801100504120039136000703041050300d00503003044140e034410349814006410a01810340503e940c6442110b01308141c2000c0d4004000280000e1000e0004050000030a503070b6081e03031170340100d002552041e0302c101030203088200301c07120040c004141c0401d881904610b15014419100220030086810108240d00a86040600c500200401090581c0207113042110401404803080042081030700840601b110a8154201242160303640d40a20212440e107003586a003001c0b44261032500c4d5000c0d502c4052441c0500131203605a40030180100152030040c070040075035840305814110b40c1211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 64363635 1250 64362385 64362437
    0x6070e0a0312170106030506010c081c0603030e0315010e010b13030605191805070312050702041e0c05030408040b1e130806010803040b0d0b0102010b0604090f0b0a0501 74
    0x1200d205140000005621a1102090054280c880000070b90310103a500c40c840d84160b20400034182450204000d50380d11100300049194401c543d01c0e00e914000d01c903010144407140900d101c4501c0c021000c414103030040b2095907010030840c1200c50806640364030000102d001e200c1c1800542080740144841c420040c00742020720542030030707235500c0da90b6926081e094400580b0715240c3e55410700410807000c1c2d0350303009143d0382c0c0412840303100c608005692056501d41c00382c84082e00082800207040c252910a808460200d60000c0090140d140c2c004803000041c1c840003401c808180c68554030f000c0302401101540d10071a0420000743c2401d00e0240c400b0b0303055102c84a5000c00b00780d204100e60040103404090b10440036803c80c020b6170075080c0a00e1500d04181031f0070403080d1f58400c2c0400c101130840c07030040300c0c1d10201c01080490ba40c41100010703070141c0039080a0b290b00200c04074000c11065966484500d507401c82a60601c003201c3c0300b000388141042140205070000702042081c1c101c0003429030703280304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 64364885 1250 64363635 64363639
    0x10608030720061809010b0703080f0a0e0a03031401050301060b1204050109020a080319020105090304060c050a050109151503021309170f0904050603010e0a021306080706080105130b0306070e 84
    0x80342c8010301c002401c41e07800010815840113080008405500b420000c0350301401300400824500125074401030311a150080c45085c04070442d1001410035010780d08500f0500d08803c08945c81070042340b402402811000460459076035001000042524050240100304c13480700b01c0d210325204030b03c00c1751211164001d10070345896484100400068561200c03010082a48801854441003048500000316080180040c11681480d0901c01c108a0210444007151583e051050b00300744a45006030408010040241503075107020b150806000030550b10075460b10486500700000c030710002010359a44860f000207074118100000c049400c001590000340c0c19402030800c0103500c0890a030080030390740b10149145c84584042201c0b22103003020b0082541002040f4000d0007810340900c00130b607940302d0602001c0e2055081c00b000d032079604c0342d80d401040900900e07025a03907500d803a250050103074102032041c60b00422076000f1440001d4650702c90007900d5000100a88241e40320b80604986224694008079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 64366135 1250 64364885 64364933
    0xb0c0c070b0f1b0105010b1b0a120908070807080618010b0d11010207060c08030f070c0609060903141e130e1303030b0d0b0109020f090306041a07020106080307 70
    0x400c2104156028007082c40024480325580c0c80c10240c280c0e10a540c1c200201d220741c0c1044018011030f50858165420311010650b410032420242c13640c2440c0010203100544080c05c403508023040544e10960390310590301900d0807580900d0744c520714107079034040750f101d9444180c1082001ca04000c1000358900e005c1c4051030000324600f410903000400342d1145203021a4038001e814141445543c0600511005010a040143e06034000303480d0b4072800c1c4001404001a050441c000602c0c1c0d6005000140813960050000c229094403858044010302410b0404d40203c3d82400008801c1082e482c200c5200404211a0400c2c0b40890f80c4101c06980120b1783c0b0b4018202c84210100e80006c56620a904c01c00c0d107441c080b00001454207002d0100c0b0807040030503004d810100358550100302c219080d141100c8050200603610381c218440d0b21038074010108204d500d40940800d11085c0310b10115061180d0304010501205600d401c2ea0036802c80b0070601c11941c40d07400c1400100c001c40c421054500c45e940e2454401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 64367385 1250 64366135 64366139
    0x3050303040809220905160605041505070c0801090515040201050d050603100e070e070201020403020904080a0e0a03030f0206071d0f060c030c0a0309050a0509010e10030605070e040b0405040b0c0c07 87
    0x3044091300c44d80b010020309940c1e036039030100f406000c0189000d214481600c0c10030190810000030040d11031402440c03103140d400856400f0040c0709004490346590040144009551148982030192603070110985861107480e0210426464180c070503400745a0503110b8a150002801e6600f0103000d0003440190f06009800b0b14019008207400f4501c16207030200003600c081c505080d00020346c54406001b840441e0710502c03090005854400c075494124be009605261035549041c2d04481d070015840a99170003c5c0e000304000f04064015150189520541d0242c4045a80e4100f048542d000e107000144900c6080ca002c54005040580d440b450380000609141e01e44444045040d15540c07184101008540c01860042e0906070b100c280304002d1320007240c0e05c049443c6000006090150180034042075100800c000c65980000c206107400190303840b0805001a00c0d141c10b000c1e1500b0359400d111401385080454048241c81e15101e094031807680304004801c0340c2c0f00d20100444ca9000306210026034030410f100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 64368635 1250 64367385 64367419
    0x12050403020a0b0a020909010b04290903120306090618070c050c120708060a020a0e130b0a0e22080a0c030c050703050d0f03140a020d060b0d090506060a03050303040809 74
    0x2c64400c0c51240304c090783e101042401d00442500c1640914030310007080c8030500030806e5044003180c082c8040310341c80c0c07070443c5003003c1140a8442c0c292000d5261240b0700300351120200490256124a90440c0c0a1006542c0c0006004a99107a1b01c0503024500500c4002000c850140c2410f8015a002e041103901c0e58900901140f0071840d105a680030755400500c04102d5100100021031384078220a00c02c0d400c024100b000680900c0141c4440dd20030582c00c051300426030401c0d070100f003240d0f0b4020406584141c1d145101c202d00c407410b540b1035440d00c540002210b04134a250340481c10407607110a01500e003018619003240c0c00c0030401c0089007000740b032051450210b0800c02406001c0c42c0603102509681c0b450a6020b04481d0b01e2240041c145814450b56084a12040240d07650000e184200507036030755008801ca40c020811900444514180400c0c903241c0781001d580450500351140d011103216458400802c00c5806040c03200400319881000010700003a0742c2e0014000c0e0031805000b02007074403500700f5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 64369885 1250 64368635 64368653
    0x90a05091f030c0f05030a0506070f0e0301050421050708031f0b03010806071b0b150a0b0a0c150908030403180f080102070312060602070603150503070f0f0501050a12050403020a 78
    0xc01074a00160300031007482003480740c0721035600405c021002030502803038a569035034031000020844000e112001400c009024001d0b5242c444c2c03103600138020807003403810f4940745d500040100305880001a004128888140c0038800303c403403041e04820223a09680d645a520596407010002e500030b0148114070004548500346c02440c06001c0300c81c0171f05910728040748c0007005240d040045c0000c0c0104204460040b485100600703400c1302c04840c209003440a5030000c269070304200d6002e0010f6410000b61008810340c0055540301843c0319080c201103441200000d4000c0e00d80010010304081c2042001c5000680940b4416810700703103803142646406e80d2141005850603041d40690660b94000a1110803d6030002651380750001d005001c000c11410284000c2d40c0d035404e03015a03814944d5804c0214641054900000f004290080846544c00d80310009800400014480c0d4003004a40310b0303011400398014015600303030154540e03074500c8101d40d215428002d4807014100740d0a40c080e1500030408900451 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 64371135 1250 64369885 64369889
    0x20a1704090c120c0e0d020f12070f030b13080306060705070306020313060516020c0f0402120106110d020316021309020409141006050603060405060111030304050a031202090a05091f 80
    0x1854000c000410403d062094a51a01000042001e04000c11502c0e90b1444060200290181d804200b2400b1a0004c10402e800c01a4001171520402030005200c11140c0d080741c0c180d038070880c0301035405c3d00d94002c00105c1c140040c8000f80010f03010720001d00350742800805492007074043c20032681c0c500d13941c0c1c0321075080341d000b61b035450407160101c03580e642030003443d001d0160003040340d145c10240018480300c025116546c140300d2510404200b212410700c4c0e80c880c1c0543c1c00189114203d280d155942e81c50107003481904200c1031501c1c3c01480296100a400801517944280c55080e4100c1e402c49039a080018408060301f08a0031a07540c0d0003050007580b5140704406640e4032803480f1485003e4031070000d0b850b11150242010743c20381840414459a1a080282d0741c210b05c00b0380d00841e00c4d403610001a611000c038004c0c0c5002d10310002c010001401000200c981c10766001c0c0e210b91481036590300c440c40580c82007081d299042094800300f041103082c5204150381c44030204c0140a2141c200c405d86101d45c5940d6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 64372385 1250 64371135 64371137
    0x1504030305010e060d0203070306050a140c0c120304030e0f01031103160315080a020d0611030c090108010905010302100809030904020d02070c06091d1e09030c011506020a1704090c 79
    0x150018042c14a00d02103141d0002821603021007090b00317660009580308e4440c000104013a40760000719400051980002c4003490032000c038010035180480041c01650007100d06842580304180009880000300c9040340d0241e5015074030342489481c100e00340999841d000d200c003410181c2e502c15507081102140051030049040e0f1a42c0c80c200b07480d1030801819565510b2000346041c040d03a0080082400004104460a9059480c4440402030b0700300301004100840105c0200500001000f03110074146000f00000300090b281d40007180d2f01d40d091001254000d010003034121420f2584103003c0c2c2d0140d0038003580650f000089910303108201d00805e0598008440c032155054000c60040100400d82c10098050500e030704d4125100f910b00942c4441d422200d5a004410050b0b10380403031f030000741144408171034040d85559040c4034141803c030136a8030303132080300058a0340d46400f65240302a00403c180c481207681036801409259065282c07502407032101c5600c80b81290042000003a40031207805a09000041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 64373635 1250 64372385 64372391
    0x11060a1a1e01090806101a09040e060f1003080a050c012901030e010213050d0f05070b0d05070206010303050a0e01110f070807060207081009030c020904050c0102011116030c0515040303 81
    0x52030024200c4403070740d00200d036217400c400b0130004c0303400711448414121103112074100540c208903d07145a080c4148010180c1043c140300d10752070310380d00008240740111180e9074100f007690740311944080000064080204a00800c1041c81d00b414820030142ca007600b4031074000a030741c0401810b402c8180311141200e0164000d4001009650368140c40b42440740e103042c400952519007541900301c03039609103000740e521640c10902c0000c203102e9250000000d59911608641d0300544800c4061641c0d08028404c01203a401d190001d03440a1011500070704a81c0e0640b1490b04010080d00e051703408c62000824641044040540800d400c1c000b04145031090344180090001c2e10300304881181003201a0f000002598400a0104812180003400c50b0164084400c0003602150516040310f0880a407035010398403803000c0b02400f041c0003010444444030f5009800030008142207640c0309a03a800303074003881a003100c543d0410354040382c001d4848005991044c0c0581d0481c10105040ca480c44c02c06a8007940082c0d0303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 64374885 1250 64373635 64373689
    0x50106030e01060302090c0c0a080301060507060c0e030c15070c1203111b04090c080f0f1b06071704081507030507051614010e011109040c11060a1a 65
    0x501481585984804080280003c07415500401e800210140c13881d0342c08840050a00c00080b41801741074201c9500224665603541d5420000b4003a400c405000c0e20054074080210985a01400c0d101c10801400f4010341035001e900f804204200110300d400310025582040240b0026003080064005026001d20001c9040b9080c203006001d42000e4403a22803a90082802800000c00329003c403000a804603800300b0414241d1030001c020002d641d001504903c0b0784032200f2403d28000c5041c040c811342450440b00780780f6032480350782e881d001d0085880360171000802041e00803072a03982d840c0b016000031003245442c10b0307560a091840c001c002c03013156200740e41c00d00c240122075506004054121800d445c1c120b0034a61141c1807400300809c03072240144000f28084c42c0c6141400c080d0855046035641070020440c07807081c600c858255902c00c105451040b03282208100420340101103000f8404641d000500c11035a40340201d0004082c8803c0c003003004a4030691100ca60355070154010000c41d01d00d09140340fa06 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 64376135 1250 64374885 64374887
    0xd03030603061409030301030609020303130806040201030f1a010309080c0304030b09060901050606160302070803040902040602010b1c030f020c0603010f06021005070e010c0305040308040914090d020a0204020306120d03050106 99
    0xc0c03005480f41105510031050101a100010a0301d054a401900015a440361840040c0c80c511030703117856098407500545e002030091000302e001c4c0d2255000307803400d00c1902c84000b140307004ca86040d05142090b090441004d00107512a501034090320b0f1050722024a0120b082c15058690340140e4401c0b5030058004080200780c0c00180f1003140c01c25900d500900150502000242d486c1c054101c010210900e49103240041c03510030050031005180344825265181d844a2507440039622602030000076600702400c142003414542c114021000380b104250741d4440480c1d80c103d070214002c0c00d000c0114411000c0811050351580005c500070b05001d40d40450780c80c030b0080d000e800c051451941102c8140f42801304010729400150141e2a0103007441e140c060a0303142c0c03a09a07514040c80d00007074000c10700800c02190300e0015500c0b420a1030380042800c02141c2e656051550f075400c10341013400050300911000303401070505801554002900601c00300da80310240b220b09207000e01407003441c00081d403a680100916 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 64377385 1250 64376135 64376141
    0x709150902070c03080d0212010801020a022104050114040806010f0e01080102121902040305010e031201080d1d0a05040c030c0f03111c1407080403021912030e03090d0303060306 78
    0x402804905600300890b540301c00710300344498807024110725000102c880700c1d520340c1d504440030400f451101038220f58580d141203000f90809040c45000d0710401400c004011588120301d540d404400700c00a25090400d00119050696000c0b2913416001c18040030800c0075040c01010b006e003e002d0300d07842c06203244c0840c0c0c1d05805030607441054264030400500302c010f0341074a00184e00c2305070701ca0b00100c02c03035a041080d0300920565201825a52820380303e240607036030100080892089042c3d8a0641c0c2c4d0b2200f0803141c0b02c914505c0c500000c142703805201e60aa08103000c0d0314a90034001400c0d625441e40e90808501521040e00240c400070b6aa25610b502c0d0581005114501d00c605d49810002c030f941404a0009500c2070035400804070320802c444c0c0c02d22602c250090f4041007010b03a0355140a04180a0150240d041a641200580610440801054904200c113581960010402c4120a08001d029001031003202c28100080c08204050040f5031100048160002c0c8603130f40000700345d0701d075082003412 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 64378635 1250 64377385 64377389
    0x1a13030503130e27071214010c2c0a030f032f03040303030209131517010c090e060f0613050307050604050f100309020415050301050a05060108150d05070915 69
    0x4158400f014401e100c4072540042401d9110203948240d48200303040d1252510405d94080710404072603400359410800e010320a101c000b200c06009210a4031180700a503501621060561080380e8078207080030300203a442d28001c0c0d60083c081c040c403c0003500d90301c030301000443c1c10006901040305038109903408000091490103c969014001c10003003000c0c801543c0344d1159200203010560007161211441e03484c15141d00240d1001d071002c02c1442c403207020a0204000a100d064110300300400103400302d94040c02003889d2181d0694500b44014204240c1c100e2032030019000ca40c1010291140c82c50a440302030060034401741c1910000321284c98a02058a0711250b03802660042c441400100999160940301000f000000c6072104504e841d20032080340101941c01001c0e60182c1031015000c030700040c110b03804003a034200768028812a40d804500800f078900a0310301c0380c0015601400115031030080d1180f0b1020709070090004142e4402c0c3c3d11901c3c0740c00d0242c0c00490a05580c5e2002c0d0390484850744074440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 64379885 1250 64378635 64378649
    0x20a0c11150301060c0302160314070e0c0708031509071805010c0807081606110d0c030515060d0f05041407050111101107020d030801090f020f041a1303050313 70
    0x41c0c41c05800d05504202d000c181306440170301411511300307001c1600034480106000c2c11602028903c682d241407030b05044e14100c1651045c0d0060200218025888000581c0b0803500d08a01d2490841c85d070391400510b0744010440050034429816100f0300342d42d0761182a0207001c084d03840550100410f1040c00020394158041c80c180141861070342e0019040c003003901d5034903411100c4c00703440d044400048601c005090000500d018074000303010018490306030140c020b58440000c10040340c40c501000360304948040e079150b580c00c007001070442110716050000f40fa600b44043e00c0801d0000b07102101030306940058404840300720b030515015100301000c0223268010002441d100303280c0c0702016000e41c2c40c0e0300d9091500300110340300c03101c0a80e680310b0081200c02e8554041d00590030009503040042c8201030a01035405420b013489201410000d49000341c58610140011241c9000c0c507198880d424084100b54080014200348140507041e0f94449030403005501550143d5504d402d855001180d006260704903103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 64381135 1250 64379885 64379899
    0x403080a0e0d1d010e0303030906041a0c0d0c18080105010317090603010e041a0f101a1c0e0106030c150201020304030f05090301110a050a02120405010c1e06020a0c11 73
    0x15641c03d501012410410032107008000302003801d100103c605a91403020070341c15103c000188403403c640061040c1c4154001d0741e2000b0541c683c011101c0711b4a5061340e400064803018170281070f051009034800c45406d20581030820804c0607003125402c00e245140d05c0260303940d41d100010028005100c4070b42ea03180020070b4070b5529109000f80018050302040c014020107020900000f010800c0c40e401c5c0c103240d4824024424010f19180300180c070603074800c45440400e55212400000e02e4100d00c001030001c0b10003111024100118000c00960006d04e003003454040544903a012001c2c84400e103c1c0a001d180100d0b0181c402a052200c00c11088000c0d00b4002c2c216841001000080791313000d040055042003500e4113070391f22005040041c0c007500c002402245040d01c00607410a0a9030000024041d11425800781c4d0140c020300d5072645102d005074030030740313010030421003c1100050301102e502011a168400b110b41d050200d888080c101e800c100e044101040d00400c5900c140026400c0c05a10720b801217510b2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 64382385 1250 64381135 64381153
    0x504150609032d06050105041508100b130603050c011403040206040506071515050f010c110103020f040f0b0405011b0203150c0405030610030b10080601030305090402040803030403080a0e 82
    0x20640011480054002c014005500d030501000024610580c0c2c6039850608000c1c0f100d042a0000345028891030b03108034a03020070004940301b220f403140700b21850900909080550070740d01501078001c1440c0141d00550f08194403c13000c00501c80d1f6000355020344010309941d07900400160040c005000981243d0798140200030041c0d4440301102e041d280140c48070b981f100c0c0c8038605a0030641c0c4d4140d20440f1582045180034080e120310074044100d680890f0311015850b00c1d080196900000d03410050a140040f01e40c000007540650010256803042c00c00341441d095a03506c108810b40900c1d08a0400c5002c0040c0801c0a0341c3e00071801170502c2161000344110030801e0340001d955030fa4800c088100d1410000001e00390740c107050309031402404042c040d101145450004240d13018041d0000f11081c4000c0c0010030028055001c0050954513004001d00c0d0b140d0954900b07907029041461001da001c4d03006c01000c12100024005035010f5480394550708002d080203c205001d44401103074411441c0d00848103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 64383635 1250 64382385 64382387
    0x30309030405040908040b0c01050a0501050d050a02270903090310110a0c03110a0317090102091806150a0c150203090304090b03010b040603030807110706090306021b011505041506 79
    0x2124112842103e00080011403461708024500451b400003000350b0b00415280c00e44070040d044140704e81c0c2d05420070404c43e80c851040119000c0100409031440d40402019001418212b40a480d16060350746162100320b05904462240041255110f4041d00301203042081341c10300300708084c04140b4014052104c8480d0290140306401520110400c111090207403405150140c1142c0c2c080c0d1030303010140d40040041e421301a08944100c140d01030712189c81400505500d10610a880d002400140240340880c1c61461060481c00c0207020158040c010300341c884079400e00203004104c100a580c44045001d43e9504118048a200c240c58a290a0040041103600c03140402250107a4401110000d4030300f22200c00b1a0050144184454000749070076000300c14941c020b81003a2040d80740d0381d00d40d850344e0580e0080b20340300e031810701c070b4000410160f13007041c000268190068a000c2515003504a02101140000d81c00c2d00c2242c0b04031030340f5900d000c005010500b003138050040340d0b0406076101e500c02c03890008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 64384885 1250 64383635 64383637
    0x110403050712031d040b130606080a0603050d08090c0306040b06010e0d030819021902160b0a0509090408070203060106090512030412020f15070c0e07030515100c02091602010e03030903 81
    0x1c1800400d0035014440d008a58995200c00c12802d0f024241021f080b00b101800001400b8034000daa0208106000140307035108203000d40d200340c1c0c2c0d004001d003040a00e03505051303515490251001c4814080d0382d00180254804100c124410340c0a401c900f11603080503000900ad040b840c402650041c5d14111030080030036000300f06250469000d1040b405003841c1490003038001e00a1259151050000d001028070180d0300155004104150b04000e0a00c66a105030980440c41001920408a0303400d01211445103800040141e21a000b9880e2504c0d000c4c0701e500003814000240c02581c04103c1c45d00050205041c00c81400c8940d0b5603000c02585001d0500d043e0124082c42ca4000904c1611406442c400d140ca540e16940d10241d01d80c454591181c205140001e003c03136542c01000400f45c100c00009207898030a00a050107040e25080000d0302c00c40c100d00340070070301e070340303c1c10560500c0072100420006841da4a042031081c005489541c070705004210000742500c51a40030109168811b10030b21001d074074040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 64386135 1250 64384885 64384907
    0x60f09040f140307081b070503070e0c0702010306030f03020607020c012a02010512010605190503010e1803090a060206040501050114220f020a02010902090609071202031302030111040305071203 85
    0xa070300b0304a10150795101c0c0303156200704040104405000320700c2c60509040b150200c0c510304400801d5030b909036141c1d010706942e42050310400080710601408644404092001001514018500030446940300d45070320640d8049108114010381c8800100701d2210350501c00310007085c90034640440c90021015100031407580240000e4000c585040488003168040e0046409805071100c818045d984d40341030140658000036500032500b11100d07030403880d15110740300b11781c1a2507130882c820b01e0580700d100305d1001d1107400b500c403402c0a200822030b0115640e5860501401041c807036004010916191520394251401a80650486040102401030a0355800d502c552503580b10001c0918803c030609000c00544040d03010a0100c510000300d513040140d042d0882c1c0780c1c1500a4078220304907107510b000d1140b070520840e920800100c1c04488c08a04840e250021a004000034800d51100d5595400081c21500c1074500420542400203003002003100038080c2d0b100814070042100071041064802130070a416403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 64387385 1250 64386135 64386143
    0x1b030f0b1e040f0c020d090506071a09010f02030a06051825021005011202010f090609060e0303040305100e0d0206040206090108040212100f0e060c0a03050402010207091103060f09040f 81
    0x54851240d0603282ca5100544100c041c64003800144041c031406502c401021012800043c0f1144020680c2d0524604503070065510a11800c2c1c1c0708416601c552190301e01170541c0322107549801040480145c613001950250040701d50014505142c4810000f1010581341c07107840301043c0e4001c0021070500341e440e007421030f411a5040100307110450000c9040900303804007400360a24010002c0b5a0145500501070380e1b610030703240d220300f1146000059500071214070407440060b6001401b80301c068461410918201000b808403401d0503107070380d00c2d0b85c189000c01c00d148041c1580d03040800c2c9484001c0104454030802400078001c10700746a000308000348515107066040c0030f0bd41000c40c0031511402040302c0b4151140003a901001b0340244004090044611a0b05000d81020780d6464102030115070f140c090103003a02114905142400c0075000303446c000304181e0550107080c00019204409004080301501440c5015540746011010440c59080c002ca07994011800c1008110001c0c8104d58200882a04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 64388492 1107 64387385 64387429
    0x90f05060f0d110d170316080c0a051305040e0c100207080303010e04080906040303020307020103060b030402130e01060b1201170309090c03060102101b030f0b 70
    0x20548540d100000902c1c000004501c1c81a02e480180041c116440c800701c2900c1e004181990481c41244402d800000c12500c1d89a580d00c0d00903140c0d05081c1070342107003006c850a100798007940314000c092040010307039134000030b81c801079420040074028814020100d40000e01d940f102009542217001e00d416240b401f030f505002194410550340388500660842e031070483c0c01000600c01520075110b03141c00b00103c00c1c0c562540401800990700a0700110359582042c80010100d50059120141c06003040c01800010b940303056001040340042080070075248032141c0401c2c01010b180d032040f2000400007654041c45101e034170f4524100e41e00101074000c1c52400c8903041c0c1c0c40b80b0505640681c850914400640341050700f10103190010307410b20441e4580b00f40404440e089030300d080220800d04020410760b81e60307603034180580508404181c0040c4200c18014011507000610b8a17851420500 = true := by decide +kernel

theorem cover : BRFrame.Cov 64208635 64388492 := by
  have h0 := BRFrame.cov_init 64208635
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64208635 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 64208635 ≤ n) (h2 : n < 64388492) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
