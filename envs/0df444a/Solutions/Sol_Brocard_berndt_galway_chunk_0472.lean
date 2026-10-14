-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0472
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:59:14.048645+00:00
-- url     : https://prove2.me/submissions/74082d58-cd42-44be-be6c-0ac75547d035

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 84712231 ≤ n < 84892087 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 84713481 1250 84712231 84712261
    0x9230703020a0810061707110f030301050907180b030618070509011101290609040e1501090b060304080c0f0313061d09060d050330070f02030a180b0408240c03 70
    0x1101088400d0302d080081d11410409c0c00d0002d144035001d503031a903040100784454210000c212908000c0540c1c643c2c000343c0d2076881500c041d079109000c22903490351001c004c01e0301141e4501c07500104585150030019900d500c00007400004509a070f4400c149d401001e45036090380c907064036510f9104010381601650b555039034141c418004001c2d081c141092080c43c00101150300040c00c581da9a0003900320584104070300f410303030b80c00340014400800160140d400424500c0c0002007004000c005c000032610244042007001103039541c401012a5640c41c546955004a10900d12441c0f010407541c24520381c988420307100450494501a180381d00a6072175030b0030007946ca071a0080640c0c0c0d50108005a03500f80440310b081c0c1c0210601e801c1107038103600c5441085260700701c0c024000d804101d4020a0704010a0780842280e2641030280341480350540b100d00ca00000c2e01e2168805003104e9400600000d40c903001003402903507406495104031007103aa500030f64101070341c00c0b41c1e4426039100410001e140382d0425005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 84714731 1250 84713481 84713491
    0x30c0203100615090f263c030a03051801060807050307090b060a03020912030d09020a0b07030c1101090b030f0906070504030804090f06091d0c031609230703020a08100617 75
    0xc1c100301c501340902e218103100d103503040c0301087c030305180c1034114030640520480030702001e0040d50f90207d440c00a03a82d841e4045c0518110416454070f0106240c8055000fa9540120340d160080003e19600c8042e01e42d109120300c145406401880c4000030b5030500c80c41000542c0c1b401400c19490a915642d084000b0340c42648801e601c96602c1d0300405800b0f40030005040f40c8199030340005132015890041080030b0000764803130819100204818400241e102c00326400d5580e00c0080b00f181441054010785030b0010b141c0010940403004410019a6240078001a0051601d003007913134480c1c0c9034610103c6080c400c90002611040082104025215403a40328034818040c01c540011840d0700c030712403002950011090ed400c810085e031070305464844188007906201004800501c2c0085902031501140405482101941c035a100908100c0641c4c02003140c07000068605c00d180140341410010300250445035100c1c1c0003d1041d4002001e59020b00e20b07540aa4000d9180d900c3c49030200d035070602040c00c00800c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 84715981 1250 84714731 84714779
    0x2090a060b1201061707050a0c020f03030703020a060e0604030504150905040c03090507080303071704110405090d030b09190518120703080c040b0301030f030c0203100615090f 77
    0x103000a0307032072090009049510505030011115526019005043da00316a0500c9590040c038402d110301744d508402150000b128078200324070341c1e030b00c140000f504210f41c40410581601000403040201a0301041c8050704a04c260400c00c6210460304d551552201c007114001d0100f00b08000500400807482044a13500d02c0514200c40030b1900c480c00300d426140022910004203403030b02501c03c20040309100042c054520b0500a60441c03401d040010800ea001e1020750340c030990010041000d11110b020992134002c1301500500c00c0341008112240c1d07595688180138002481c3c6a0030a1581ca850b503202da000cac1803002c2800000384103070f1042c800240070140040b4030402c070a10311024400e03000e00000e1301c020500242113840c1c100d503080203004094010300c00c0848600800c0107201000d020340580381960340000900c03030440395034901542c081d04d0b007000c06035061151040c2d1505140382504101c1c1601e040c1644044001c0c041041590b8540c0107000e200501d908504003404141881400c170320070340c030100d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 84717231 1250 84715981 84715991
    0x5010804080c0102070c060c0317071d040b1903150501060c03050c16060801091503050a240e0304091d0d030c02070306020403060e06092e0914060603010f0204060c02090a 75
    0x1b80d01c4121005036548428089110310301c6840606411120900c0c0b404504042850a17180c6504002c040c550030f40003481200c0c6807189000c07000e80381c940c800d00120740c014111845001d0841c543c000d44100e544400c4624526183d40e44444146d20701995040b40d146844104641c00142c0e41503d041e0882c001c018454031030341c03075510b0034070490143c0d100003092203454400d45541400004420f42d500884031201d00c804031101040000c20005100c011242c110032001003800d45140341181c00c00d0101038010500e41015034111910700f01000130001c94841d604c041085c10886010910350510850f1407074540d4004604555106009030009004005c40c0c0c07059410107512030380e5520480e0400d80094504030f50350020303100003803010459941c00c0200e14004210300e03404002d0102d02e0300c442c42020f40010f90200301d800c103248407a403c50700a44e540300c062103000c82d042030b402d540c1d1044c2c1102d82d140310790f003031404640d10340b03c081c8200c2e010355070742d40d503054800700058003840002a409014401804d07509d17 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 84718481 1250 84717231 84717233
    0x103030c0206211906080a02040c1b05030d060905040816140109081e0f0a050d021c0504020307170c012703140c030105010b090d0203010e06070e090f0105010804080c010207 76
    0x801030728841e04640090308981000c044035840c4c4441403080d040e465103058006d00c43c28a002402585443c0d044074080380c0203d04040845103800e213070080340c188140103040c0c40200400480900003c4051000030800c00d5070314507460f801d4800c01d45028248550801001e52003a85400120300707200c4c00341040300e4002c6d000c0c49205085850794041503c20650100300c86249100c41d1010080340000328500030300b8030304010800308030381c4211400da00a2003000a85142100c040380c069a600010103d03180b09110b8514014001a01e02240c04902c240290800815001000303820420100742240040072090200801920101035035441c221419090310100383c02584041e10103005503100e80c81b0120301c90480c00807280b8240b220300241c0d1190341030a00500c810322040d419900d400700c040f124000442954004240140485521103031203000d000d0400614a8000c420383c80c1d5031005035070b0752a80369155080110301142c28040d03107002481400100740403644c02c8001d84640c5849800046c9090b0103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 84719731 1250 84718481 84718507
    0x20f03030718140105030c031005130c27050f010e040f0e10020702030303040f020105070501060806090706020309030c040510080a0506060f01030903020c0105030a110d0b12070e0103030c0206 84
    0x110303075540c00200e11024000302070051207a1540144400b010072250312100c031002134090700004001d420800c2c4003000080f028840c40e4400300060101400c440c210440511400f006807014101d0358000c5055080e0094070302000c1d010070950040311004516505080000308000030300b5138240c25041000700c0314240010754581c85401e0111034111000203942c801c902c111405c1a0907605100c085038410301010b00944c0f0040120796000354010282e2150549920043c0e44501451501503d20340c60400c2c08180b0000000d40b02d070080d443c00048503100c3d659203904980e20320500c2810b64240d04800e006503941d050079004aa041007030865801141c5444100103450400d9000c0141c03400d501000038811203003401c0d0580b4042c00000c0ca810702c02000c10751006990b40e20319010031030402c503001000071514201584213a00200303d07480c4540d070f20020819403201400c00050424880c810300e0840500c4d049000071081c0440e07060074405002d90786151800d8840424010302a03800a03020030182e820004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 84720981 1250 84719731 84719737
    0x303110f030408010209040608160302060a0516030e040b060720060903120306010e1e090402010e04180b0609040c0b0903030904020703021608160b0906070605011706070306050d02040903020f03 85
    0x161880016106e60007401000b0a0380c5681d4058101c54110080221100802c0d8000905890b01500c50590718a0201c008a0f40361180701c11410040010940310805c05d507011984150300c2d00300312814000c440400d01000030510030030303100400c24a511280e003161300d8516495040480700082143e410b061134400440d00300320410341070b000d2002c400803c216096030040700a40004070f0030b0302c4c000d0986500c0491a135103404c2031b00e0150702c0786001c0c20000d81168490568040041000781051001a0b4404143c42240e526000704813a142003001c0040c2242c1004182e4a1081d90002076040c0c00c0c6150902605641c5d000350162505030104002600d41d40d01c1b20b0009025240c40703070b4000c00b0149101c1c2135001000005400079105d0f40c210803007028000e40040c0e200e1050350300f44404e4a1792941e418000071401d114160340100064101000001d4200718840e8a18900c14254180e503c03ea540c58004c800b1513101e4011550300c02a40c2110382d0260510780e1003044103621a00403107940e24152032185245030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 84722231 1250 84720981 84720989
    0x50303040c06020d0909090f06150906120506010302010c050f01050c03092b120b040c020309010f030b0d0b06040228110316030e150403030309020a060807090303110f0304 75
    0x151001091200304201501a034004000c41d00c054100098009401001560244104840b4546a904001c240244501a403d5056000c8410003165190290104280f41244114200f01f0701d0010300080e0704038603813180c0700c000e82d21001401040e0b0950b401520350001d40003007555140302d420740e62040e14209115480c0911101c11442e0b0703c9282040c1114501400e44201e40003501403280184c80d0106039240c2011030504500701302e5001046520080018400980007680c441d052207090b20b44250040010500d032802030707070780790f485420782d100c2035060b0743c002c901c015000310060083d00c02107070403444119004600280054501080810260300c04c501e060901420b00219000364a0019006002c80d8404a800006141014450380c04a41d410340c3d80741c4003505104480b40c6c1da030b04d25902c3e101c0c090000c1144586d860b807100d4582c00c0c02001040843d9007240541764121020413400e0040300c0c039500c2144940e40e408511070840e50704036800102c04090340483d120311000d084603440c0500c0680058 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 84723481 1250 84722231 84722233
    0x140304080403110f0117071211040305011514040c110d08091033050d03030c080a0621020a21020406090209090a110f0708030f0c18010c060e03030405 66
    0x28505600b00030504195000f0000c2c424914101480c026903084203a520245508032a50005981c03600000d0f1242910140c402d10424079120344070311000c0c10100078006890140e4003c004a4000c003401014030039145c0191840e0703070080030a8510500d001d4100b24071049191030800303184c401d50b18204c0c1ca4116004206008922440100300100a081050380c03030303661140702c0a1200d82003940005001401205203d54000303414000003100d242c884010310014900a005500c00030f4250400130010540880380308002000751001c9190b0b107000340601010340710008014912402404c50306032219103004412600b25442d0350002481c0c1074044003060781c02c0c411280c5250481141e00c1040112003481d006107110341d10500002b507082d103503c0207c0d54090100b40c000201c1000300130560045020f5032000c000c240c1030000e040020007020740b0195000704021800031003545c850001c400d400d0b00a0a00c3c0c0c0c0041281d21250010a6110702c20758010741c1d004040c001161010070b1401825948212800e4401e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 84724731 1250 84723481 84723487
    0x2030a110403060e0c01021b0f150c030d0b0a0e060103020a120c030f05061e060a090f090b03010b0a06050d110714060403120902180405030d0c03150501020a021f14030408 75
    0x30911040c014005d255009201800052814118822005011100c1180140001c041141c6a80c41d004a201c0702500c10800198861051008540c0c1d00d80c0010010340c042420284005400d0522080d43c0e0141c0355031141e040c0c05a914480118002d40181c40c2c0c1004101c00540d000d02205054803074000321141503900850f104045407445010394070043d200c207009242440c00012580a004403500440c3c00446203141c1c1c4400f4840215512100e5802a41c40001c55040007d40045180d03c40c41507020150024000040204100402e144c01c501c00c0c5404102c007040038007507000f565404016a21448074010381003100c1038844819884030b070422a0810f80c0504113000601d6040220070584150320901401442400ea0201d22032101601205010481d598007103000c00c80140291694540b0b8058200407082c00d540000b00580128000c0c1d411280c200700c00801d0551002c00c42d08109a00070b80010312100c3c000404080080c008011502004040b90011081808100007580a030b802200711540f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 84725981 1250 84724731 84724751
    0x51c02070c171b03120f0c10060302010e030102070b0105040209040905150a110403081218011a0a0b040506160501060305030403060b03011103090d0e040b030d18080a08070602030a11040306 83
    0x12505400504a8a80f100c40064594a40d80c002981184107030580c00e80e5901c078015032000680c03a016003010b101103401400141044009254031a0003124001d9a071000704030740d40c00926080b4460300310090101c01c16100140068281070b001040c0e55000130700005140981600c0f6103007001440301020f00b181c80514144403074469070380503ca42c90307584903100c1480e2620f55a41c0b1842403107440c11403110344d90030200083c84914038281000e148070022009200862203000742500c44242230050f2880b50325007040210344425980d040d203096600c050072051503c8008501c0c0115030190560446085d9229030000c00050f10601c06800210710448021500c00390ba8010142545c0c010641caa00c444410700402c1400500058013040307001c1c441c00e24800301e00c1c1081c007207006008401c2c07001d9010312410301d0500b803042d400300e10441641c00c80c00d150403891b03444455454a0f1a80c610001e8582c00c0706104140205949900943e0008036414000420306142908404c040d041075105403600c4e69070b150307005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 84727231 1250 84725981 84725983
    0xa090c030b0f01050a0801031104180f1208060d0b061f050c0d0e1c0203210a030501090603030f08071701030303020a020f061009090c0b070501090c15051c02070c17 72
    0x8440090804d6810901100001030243d00144406444500c40c644070001d05e4549a0010348401003400341c040780c0700b6071810140003116615104a540000e80700780e041141d4421480e5900441e0014102e81042d02d00c0d0720b07070112106c000b0b400203070700050040c0400d03c01900d83c0e01e480d00742129030300d0b00e503110708900048c030341000c80001000b0705200800380201200d07500c210188980c043c0b0b200c007a105d100018004a07103009a04040c500e1101282e50428901000300009851520b030071350740c1030140f6030303d9000407825120a44001004a0549034214414500595040d0b900091524046662042c00304241604860a901c26000300b54005a4131008642c144045101054241d000f40030a0500504140e116882c078030a8001c4aa920703a1200100204c00501800500b001240b69031038511506101e40202041d54040b039040801e4440007842c2c8070a031502098840c1180c903407505194640401141803031a0314008400d82c2c1d0b08005482c0000c3e20900241e025190140a446c082036021443c0d07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 84728481 1250 84727231 84727249
    0x30919030b0901050c0906070501021201060e0a050a080a02060702180403121406030a03050901050705070314060f01181d0a140106051c1205090d0503031501080603030909060a090c030b 81
    0xb10540c0d03414942081590b0200c42c04860039110300303840050790b03801d450502030700a0151040c1d9003440003484000244039a0700c00b001e03a10420003101d002124558030010803801d200f0501c141009074001d862500d0141c6000c5c4060071314540041c1401e200c1006666407002600b408440c2140880c0d91a0450301e00c82e50140b0491842c41e00010313846a05051450004c1d988003480b040090801c0f60008176010180d200d07000340c4d02d5246d800b400310b038441034480c0303059101720030545a0440544174a0b8000b41d0340400c000c151a040791120503803010700620444410001c1c1560524554000c040319042d180c01c000c2c10060350401c070340a9540c0e882007805004401d400d40b1503940c04288580c100305d5156030040980c001c60028142e005890072149002c02c0001d940e54004c07040820b81c450b00404443e800e00c90007000445c4507960822031404030740d4045005441c403034800e88500c1d4240c1c5c0207104856207030401aa0301c0340c00030401081d44032426540d4280070140c50210700c0c50800261100b45c45401381c1429005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 84729731 1250 84728481 84728491
    0x7030c080f03011806140d030306080106061d010203030601080a05090c060708030403080a0501080c0d150507020a14010507120903020a0b070512010503030301080303220c0f0302010e0121020903030919030b 90
    0xd105c42440c0c01c40d242482d80316104410301c1916441112030804d0300030f500a00091101d40024400d8a5445001822170010711031600c030a0062161465403542c070210440303118040507140c6809640b03aa214820003000700030100440341c407882c0e801104540e20080078024141c8110b08882d41d03032900345001080c101001e04081030342c0342468014007080e80c000c82c40e0b8110f00700c16500c070707a181031490416008024002c1200c8011502d09018809041d50100389a03502c03c3c003480f440a4040e003d1003895003210701c11650900007030384101201440b011140c02c01c012050180c4110b90025509031601c0c852074030706440e0040031034000540d0040c8900c03408030503030042104070080d60a6614003c840c035183c5c4401000602503407021300d000c08039a00718801418050350050703902c120341600ca03080f40c0311442280c081a030110700d104405010341d40c40751002c800c842a0f00d4001040d003146a103810740103504403000c0385900d80004e00c1405202d07100d40300f50a481c1444458240c0046185090124540b400502 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 84730981 1250 84729731 84729779
    0x504031b180510210614251e0210050a1d06040503030c0703090e0a140a0207030e0f0301020d1103061002030f04140d12020609010c0c021507030c080f0301 68
    0x1c00c0210b401c0c100c40f01281201e003580d144401c0100c001c4419070000d058840010010b80c5419a40400202d1101c5224840c0100145104169400ba696020002e5030500403c00203400b0b1206502c0203041c1c880c2c113002c101c22900482c0e11082d00072070102e00340c0b041204c4400c046a5070300c00304504041c0b42030000c24514680b07405040b10b0f0030705454003a201d2100515541454200041c040200740c403038100000107169880541485d070506010b80800b50610080010b408020040802c0340c104c1c1354401c0b10340c0140c1c07588942c105255010207105c135503034850034400d5065500b8002c6e684404200d019080c00300c5c0b01301d40c01c541d40386040800c0010034039000804500315401032110903e50080c0108440c155281e4171403c654418151000a06100750450300402c1e00c42e4013807990f036625800240090044003620024009281038500403a00303200440e9000c0c0d8001c05030650200041c2e0010002e05180e4080d00d000b4030b082c0d0321500d0300141a8004c5d41d0401c203c13000000100031485c4400490b00321301400c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 84732231 1250 84730981 84730991
    0x7150e100e03040b0702030304030212010b100f050d0c03020c010f0605030105090106050d0605090c150304051b01020709020d021e0703090b04050607060203070e120d02070b0f03010b0a0504031b18 86
    0x78407182d4900481c00342c0703940c0210004185065607001c00659005560051002d181249100c060f54040e01d4844800c0303000d0300103501c840040354080c1803c140f140c1480d5031524142440d0151143c05003004c1c0c803080b801d15600300f080c0c203071403002801024204042940d0105451707282000f8107086501c01000300d1056498140306101955030b928aa400c40764011501142a4842c2c042d95420113101003031030340e4403014418864484420807005148264003410545851011040d528000040d00800d41c1d07005821440c018000d041e26036000d00f00301002c4003401400c2c140d030440e00c0b01410b0001f0611071030a03000403c641d800c155008a40b030025203e254141030405240202080090080610041142d50040001074046106500364002e545000300661b5514841040d1035459a043e4981a40107008040010903804002c0c400c07201d00a18003000340d8070710b80c60004451107641008002e4020050200400030200c2c80028255203440d2210300c494075090718001c0240520540350610f221202e040c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 84733481 1250 84732231 84732251
    0x7080606090415020c012c010b010e0111011d15090f0c040b011803060c0906030b03060a1d0f0102190c020901061214090c04050f090a080702040207150e10 68
    0x21682660002ea03c48115029039407501c19400107405a403807408407035860b02c1d00480344284421010280000c3c420380358080e20603060012403d0f00e0703101c2d140d0741c04140c1d040d001c0c085ca9445411014441c40c640800024504040c080302403003aa9420701c100160390185080c5140c070321003040d559410091020060500710300c005000e0342c40d142c03180d0030144075680da20341d0100140d01032618070410100e07400c0050038840c2c50745000801090101c0b494000a0300304074010030300a0107445510144100200207110f86d40e11281848003030a100810500c0713942e640b00f030607142a1005c000c1191502410000583c507180c191001c3c66a00424078240c50421403c288601d016071200c1303c4040c1034034a1440c04034041c03410203400d0b101900782d4040160325440e0501c1044885000070411011078101220240002d4503400084074180303030159048001c6410501405000944041c0141182d900c094000750529209880b481071a69a040d80301c4402a29040c613252407210521860004402003002044040700c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 84734731 1250 84733481 84733489
    0x5060d050709090c080a0c0303020c0117041b050d08030f0c04060c120513030807050d11060106030203190f051603020406090b130f0b04091104030b06010804020103090210020d0207080606 82
    0x98800c640020f9503d0803030b80c0030b02100b4000b8001800a040890300062001e103842260034003548000c2d80140203940c11001c9940c41200072600071028951011020384560305c40380340804a40d441c02c40c0210f10319000040c0ca03201d00f1200043c0c640070b01c08050300e03440c1000d800d05142d0f40090074540a61000c010500035250440010100d07190002c1400c0111400c050b0140c4e1944202e1501c1080300040740000810000d10a0040c450203100350305070f81c0748901c68401605c0030f034800e24010b01103811401c01400f4492099018560180000003814911468220440708aa0b058100340c41c0441c1c8032000c015500c040d544c0c03008150300b444c0c602146070514101e401000d1010500034003c0000c000203803442206a020078102c09004100700441c10f0a90350f4844840a234418403036482032504092000c48400705003c02d940c2100d401100d000d40301eaa84000460341e100c4003d0040f41416624484200542c8413800e5035205466250001d29070951108401380c40e09445234800b400700d61200e41003140c1601d0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 84735981 1250 84734731 84734743
    0x2040c090305011401030f230601091d010b030a0b1b0310030b0f15040e030d140106020f0712032609010b0418020a06050901020a1403070c0504090309030215130b0d05060d05 76
    0x107001003070001c4840e190248e0401070306d200a8070300c490384188000400c00740350b15403181207240c00f9031001c56000c05140c07039543d090b04e0604a045906410580131103010500307907a041039002245146441445030500300602680c0c1050310010804d0107a02c2c0240700b00070740100d907150454007208840c0c13654941111910700044540030000e0246450700750f123207400d450800517110300c100a1041809480810006850380e40b03003d200d40c000602c80c010f006100d11002040308420755a00110700b0031541081c0e2016100b804a0441a510400012510030380030703403801075640d01441e091000410240d05106c1080240c8503c85600401c188650880b200107aa030f14054000b1900d890906544540000006034241040400041d00b00802c413a0f1001c0d51040c044000c00082d44101d0a0000094803803051004603050504001c01141701841c050015252164001e0002a0645022482e084010021882010b0b071580502a084804210b0801c641d1207405200e9206906079040c41d9820103e4540c00e98400b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 84737231 1250 84735981 84735983
    0x80f0f010506090d0b04050d1701032607050d020c012c1201021908060306010603020301030b07110f070f0306050604140703090320100c181e0302040c090305011401030f 74
    0xc4000507504400c0d00c3d0080c00b5004150006149141743c03605040c2035071910946507a800c0011441c4044601312050300d600d1034143c941182005150340c00d00b02402002040340c4604c440518400e00415000a43c200818600c3c02d500380c0c040e140d03019107880054a0840201ca40c400401144011451100071000f84110317501011100d59400c002c00c0d41406009210320308103c04914006032081c1480780e00b100015011310415001c40d015607a072220118200c0c0000e00009003c00c0b0301c000400c0c0102c3c441c4404281c000d030648240d401e04800d541040d40f40c81040d0348000047c0c4180d910400500401780b2405502c081c09075800c0c0030040d0322a0a0841407940202501c0074140d441c0e07000c20900d80310342602150403168804131185d07022000c03401c59480701c0380e400b1461254203200804480d544100005040809402528401e960620764202081000c1105400030180351310400801340e030b941e0082841540340b5850708119103045040c200c0c00d595424080c1d20604d40045d00410018502540700701d011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 84738481 1250 84737231 84737239
    0x10605071b031704030c08120d090201110709140c09010f050304060209040c0507060c020a030f140c0124061403070c110301060303030f060509010b041203021f060501080f0f0105 78
    0x1051140041422040c002c0d00050008244980000200468000104107490040080b50ba4030781d80d400100707544600011a0341d011400c18030454180c90341c10b401003c80c0d10b20504108072640d514106652424040d98881000f07107890318040c101480c101500140c00000702030600d880d2411602c0080d01c80042580b080f0f0401000000007000e1198543c140c0d0312040004101f8400d034400400300510ba500000000d4038824604020200003900004002d04215030540b50b2b10805564a401540d84501502d042e20856a04018217950004207200e515911400b00c14156602c41d10340d0415a0441d00c9900542c040c40b4040031605020720101c2c080d00c2c3c0c03241151802450040031031610401843c2c10400702034040d820a800442010b41507040b070492901024000c1000c660385d4010000009400e1040c40d8184ca410070007401500c40c0c4001000006020340101c2e0b031403500c0c1c004895405024030310116060360391141c0070320103584d000c040c11340c1050304102c0054103810401c05201001c0818400d407449 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 84739731 1250 84738481 84738503
    0x30a0210080912070302160e0f06010e0411030901200307081f08030d050103020103050a1109100207080601030309060201060e061c060b10050c0f06070f110c0603010303050c0106080601060507 84
    0x200008101400c8035a003d00540d58a8000c1882c01079a41e00c00007012000340c1c0048000171600804018030030b44550001940540305403610f80043d034621002446460f00a620350401110000044004500a0f8640c6d000040c1c0c0c4d4505030f902c0600c1d11460b002c8041000f81c20011f004481e54000006900582180d4601c00007481c10b59245034540041e90041e036041c000460b8404407240c155111034100c0b03000384c0b8240626646d5580305000c1328801007002e07a462030140140d480b241080c0f41c001000b5a481d00460b00556207030782c1d4103441c103a026403044000a40350f01050005035428003c0100901042c04501041c1c1000800242c0441c0c0b803005400070404400410030074805590080600800054010940303450690700081c9503a100420020061203080c0600891a10004882e072240a0958541001074510031b8125a03810410000c01050304c101c00c1c25060ac4da5078030005600862098039040ea498141603452403d640c15688100c00c00d403c12001008120b421008036440554884141c2d10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 84740981 1250 84739731 84739741
    0x212011d0a17120f1302040e0c0a1401020706050304060905030309030a0f02150613090602030109020a0207050901032409060c051206010c12200f03040f09050105010507110d0629030a021008 83
    0x5a142e0b803000c07006e5130040c103203101c1e045001c0e40450502040c80060ba4008481903d4280081c80042c070542c0850059111190800c40c2500c99409035401c02d21840c00810600040d880d024a940c0055503040b11a401c00100400c40c5030b001981440745a0702c50020b00010441402100c0848800901c1c0c580140c10161000211801d0340d0701002c02d143e80408119141e507103c40c0c005000750458100c90026128104c408586450f100b0340050480f548011412500d5044481e9402890f4011903070b800c0d81a103900540002417164001d650717400e06030360f90f003544414414503000c0400002508907410b00c4864117000010440155546200103000e0924801581645400448481c004074440706980103102c0b00035544800032004100304d50700c104090aa0036100c11003801114428031416001c55010011080056910703401d83c003180e0801001160001c4241d2a51000d07181c3c420344010381c01c2400c42e045d00ba18010030711410305821080d4010003c4420550204803542980045042880151070010b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 84742231 1250 84740981 84741001
    0x3021804060303090f050d1e0305131517072007090e0a0b09070e01050d020604030b071716050708030907081002030702100e0a0212011d0a17120f 64
    0x146145806002045a56a03e050042c04010b071401030764155864170900084510389501038a0241e40c00801150f0508041d00d280360086914450071028040c05005000000d290208200d0040007001303540f182840706180002c101003010031202d82ca1200400600c180307168400d0800c80b024080300d00203941d4040030342d4060300d00306159001c0040702e400c10901c40401840828081603080c89144004103540b20b04ca60591a61810700404580b0765841d001080709107448201100000c0c0050160740c50940c89031100020244201c2e40d80d000308215007036040c1c0c03012103019420743c81400700307521b85130031000421300410070300c11404041d200c603d000c0701260500f0000e121440040c0041030441c1c011449092404020b07420842e10000035024504034103210707180500079802c0f042d0110003c0e04050b0000c2d820040290301003100231070b45669030035000c2c600c030340d00100c15140c0440702c42c020019102103190a80c3c01414000c1c010303600384818012030644c40504070086400c403124401601966450300142 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 84743481 1250 84742231 84742267
    0x5180f0a081b06040e0708100314010c0e040203090a0303050a020d020412050709060617150a0914011202090c07060209060307050307021902010f140f0a1710150302 72
    0x250344418414000181a01d00041c000660a0404a02410461600d040140a01031881440310028085e000201118840d125199100d1440a55400c2482d01c03070700e4500032a02c0170012070056039500e04038032400366000b0b05501941d1000702c800790301e50b281009800c2c0e04c482c54010003c0a0580705e802243c2ca14001740c0594a556054610071502c0300ea4900380201a040c100c40c0580d001d01a0b442c0124120100e405603800b51200c2d6280c0031020b092080c488010028010100302d80c040c0480c000700c032140d4441c2c1d1404000c0880d000c01199002100c0d280e151240303410b0380400c1410a00f0060040103840710040c0660180020407d43e4803443c9a040c01c8002c5d118020b9a80c0e400600002048507068206010303501494840c1e00b100c101c801e654a800d500000c0c01080603000c075083c0c501c3c01e5034440c803810303020821142c5900c07060b0810b6140b46120b00150488000307a07000c2a12049851251007070b00c140c10350711604000d1180c02c05860101d46a92010348035040d0740401d90006040f2000e14100b51704 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 84744731 1250 84743481 84743509
    0x3030b03030c060f010b030103051b03010e01050702030d15260a080409091112060c0a0309050f070306151406030a2405030606010c020f0409030e0d0b010603050105100518 75
    0xc0e29501d00ca0b1040031502c50104551107810410345000100740d0035200802e581c16603500034000c0003031080a030340b801258030350a402150b0542d2074090500646101380600c900640254004503101d10504030702800b541d400030191084080c1d0f00304100400c1e8034100000d40030184001c082e610800200121a0400c02900d42c05070048000141c002a0700c2a1035210344200ca00640ca800740c0000780d04200300482c144d40341e03840c07003e80c0410041520840c4c000000d201c003000500300029285030f19503400e0304000751407003c0445a00100010024401c26000b000142d019981d20b000281c0e003810020002c1110407101035000d21008400a50342880c48d5010642030075141085046450003508102c2c462032003801840d010f4024013011510f294050f1203914101ca600501c032011150030141480b00038200c010b000c0d4204002019415026258841005116805200c5c001140d605008002e4195481a03100c5805800260403160403607078400f0544081c8070198109250010f951800604800c51303040c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 84745981 1250 84744731 84744733
    0x506031f0e0108150f0609180a060518010c090603090c09180507050105041809020d060e030304030809030406320c070501080a020f04031202030c070f06080a060f06030903030b03 78
    0x100c081009101a034426040f907141d441110001c416072141c510740d4403c1540c03030070358076070a44020449500d0300c0034905d58002d03e000900c0070202c0301c030000b103446c0820f005000d80b85036950704103101c4051480c480d44107001c41c0280c024000c0020142005010091a00c02c14080590715090303030303040100046901d0001c081c0e043e014404050000348403245000d80d24401c80c0c8601c1001c1c80095654014010b503030440300f02d0007100b13010384d03131004502d405413201c0007040317a00521a0300840300203503280c4111411005041c1c000d6480e8509450040c0c0b07154809440d4031036590043c403003001884ea208003125100d1a40c401174100a2880f0840060845044551041c891001007002d50b01d01c0800200c0c07070210f031002d82e108142ea440301c41d2400d04031301c100c001000200d941001b041c00030a04094004054541c05c0c4100d0f49424400e40c0c07118146603d40d00424500020b0080c10800c1d40d6004a00642000e16034500300f102d2803921103c001114010310681041c151621545410b2500035400b0074201c44000d8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 84747231 1250 84745981 84746041
    0xc030405210405011d010203030703090203070b030705030f090c06180120061509100b07020a030b010b04090e011506140c030c0601050922080d0b060a0c03020c04090c050603 76
    0x74032a041c030740240c060140010019040c0b040e0f2074504c0008000400810307009540340d5241d1a44c2180a80001d0384142d0f054419074800046408030000114880c03010395507030315181e003000149a07007081c07409443c04401350301501d003541c569138540040f6203107038079103609144042c0291070045e02c041c0c0300f85019245448401d0000c100050010510501c04c0e90f00f40130702a070080c51401000201c90042e6110382500b0051310090184c04101801410b101e400240a0031495a0340d949541c1e94541c260411140e0754808901002012000e0048144906000009100c4248407241c0700f989103c2611034039080000d4a8040c0004816450840310140030400589030340301c0851402e6960740c0d0080c82030f1400742084100050007280c10744401c20843c1410425402806055142c945298200514004603641d0b21000b000700c1d43c4d5504010510742401c0d4070341400039030f203604000e41070140070044d8600603402c080c0c0c1400050000300003881a50402c881d09612070700c031780890401284040c1d035000b51300f100c40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 84748481 1250 84747231 84747283
    0x9130603080a2a170705070e0405031905030708040f03051908061509030318010210020406030b040b040e03070f060e0307030c110105041401080403020c041506110c090c030405 77
    0x20010440d0407111100001d4005030f03180c031540100d40e10840000d80808443c0741054907005a41004110340c40c010703003c49499603144d00100140c44000d03181140d850b44001444131490030380e204c8610a000f4a0f0808904500d8240340c050004980100300400418401b50f000007098015800d98001c01c0141d01a140b509a0a00c00641641002e85080384600200c0c0105501c42002508403958824042c01440c14882c0700319a480388019110112415809005800000640f151020f07100600c1e03d9a0b010500c001e5a00510007141c0185400c47c2c05a400c3c10a070000b805000007c68800561200f00d080142d17603607052400041c0b00741e0b07800b90030341d000009481e000d05502c56a03e000c43c5000d0b200070020821504015151441345102710365601c401c0c40c00d40d02240d8085e038806680306000e07005440d0711350807001c005800c031210030f0003040004442110034440107034840e0a16440c20304220040003458425400034503100001410036940f123034000005410401d0030310100d0b25030340c103002180304c80c2c1c424 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 84749731 1250 84748481 84748487
    0x1050726040503010f09170d0e0a03081501081605071a0406060303021c09060e060d0e010608010c050408060411011206030c03020111010203150105130e0a0207020a0506040b09130603080a 82
    0x142c890b0034403960030300e280d404001c40107100d03166040d5401009584034082c0c443e00100c15070800d0044d01c02699950010000c00c40050080d000541c1c840d50300c1803064a00307030004e09182e40a0752442d40c1040414410042440b10000102c00840c2c010b00308140c03214003501d00f00340d801c120403141035000c41c244001d0200f001000c0c0c2210302940c1c417039000e5880000016103070f12941c0d07404200c0540083c40404d0104031a034010010700a4410010340602d282c44001003514040c0c0307170704c00c0174160660f5440300c042000820038418518240107074a403040c5030034a0b104a190380c40c400030300090700f40008590390051583c05082a45c0001d40104018009a42c2e00d050506143c2303418801030340882d02d0388810507075035038040c42240e11550040400030542500b0000454164100c5002002c5420b512840802c0b09811081800e1080c0306012026a449405105001040406130302441c0030b0700c0103000030700c003607498441560f03065101600c03950481000340c45460050500f03503002425072040040c000e0702c4158 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 84750981 1250 84749731 84749737
    0x408010207051612150207060902040e0d0801080d021011040f06080118060b180325052806030b011701080a060516050403030309060b0a080a120f09030201050726 71
    0x80101e5145442c0c0d80c100744004c451503000c00911010303003040f200c0b084080e00e5015110705401a1000a0b0000455010404072044d4001c3d0030b919601c4507011842ca0351b80311742524050f25610340640105c042c172003006035a540804a04041d0a500d5a8000200c2d0149200b55802000940301035500640e8901d00602011420300031091000c440542c2610900403d000340d508590303108a565181140300b820340c014500450117030035450300800a41014a0844423143c01c0490000d40c155240107140a08000301800300c030300e000c071000c0007a0940c282e281c1050301001003110803e04002c00c0010425004941e00528103040144408a034400428510070014000c46201d116000400903a2240381b12074605002c0b40074640e0001e070040105000281c4281c021b0901c1030700c2141c011400300040d00c0050a01c3ca800c0d048101a64400340ca5042480252142d01d48101550308103134001240989000b81764004501000c3d05000700017840d002080041d0348480604100c4c00c440b0460103495000440340d07a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 84752231 1250 84750981 84751003
    0x301030305030f06040c050909090106030602031f080a111207030609030801081614040b0109030506070f0f08010608010b03090f0105010e090708030c0307290903091c0b010b0c0102040801020705 85
    0x20340c03c0c000f0304103040c03910914030f000c00180c49190914480d030f401c214881800415504007952a8640040003a4150001d03502402515041c09208007507041d66000e815205d50110003680e0084144101042130f02080c000700d52015610b00a500c00a84109860282c241d0b00041950340b400302e10000341980300c114141270720b0790002981e00708210310000d100b418405000e420412642c101d0394000c42c0c58a64804804560b045c1410716109680b80c55542c240b180840b00c0703c0c0490014a043c62103541d0003000c4429a10560a20034000e505203080100402c030705004080c1c10400000200380036080030000c1189a4000000030b00031582c54002e80c92011000b80caa04815214038900031594113000320a55440d9046403008500b0315103140c0f0b0729406001e42d040e0b44003000405105c01c130081d2002d1001a489400403600841d03039801040107001000f0b501841c80e56451040340c42c0ea8001685000205045803404030311603881c1d0420000d154020703c103561007102da662000030100c0800901048103800a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 84753481 1250 84752231 84752251
    0x13090225120e090610050901020f03040924031a06040b0603090a03080c04180f110a09051c02010e0d030509030a0f021008090703120c0204050708060306101802031506030103030503 79
    0x800150b0080c4803040205030796a980c8213183c800302d0a09203100320042d01002d007051048880070386920b038080e8150352164000804054130350107006a059008842d43d203003840c18801c8a1036240c65034482003821074403000e40591044101c404240c05603986c1e0403003030741c04a0080005941e400c0c0904442da65000440088002c6550303100003403600d409c1e0600340c6d4110b41d50505240e15822004500d10000c1c14180c1008600b15622101c021100c10f10340098400106130b034964076603d07802c100c20440d86032042604648460340740704407000183d9000c10405d1040318140d03007504104603941790a036030502504112541520903258a40280300b90441500641402a030740c0400300c00c06290100c94984044400e086940e018050400005201010060803201c2c6403420011014080d40080c082c1c40090300c561300041c0703400051142d54a800d01140783c100003100f880c02402481c040d4410240b212181d0703914201c0307501100242113126106411200c1403801000541c0d40d44c0c60349006000360b08240c40c01362030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 84754731 1250 84753481 84753497
    0xe01020a0f030506030c220c050307030605030a030c080a0e030609070306050f0108070308070c080303010902030103030f0e0915060d0c0507120305010e01030215090a0314010e031309022512 83
    0x3040c028829540610b03401303030181400c00802020300507540c1c0c80300742c0da0201841030240c1c0065031152380304101c4a102075a80742c0741d072070500e110000c00390703034998001501c40d0b080b07503490b000000d8002c0440003a142c2d2100009440b44c08510040e900862041d881c3c03a0107006150400400c40404034840342900c0c4640c908002a1700e480f91042d00100090144a0312648402c0d42400441c00b40000782c002c6510600100c0840f40e142c132595070941e0400e038020100d142d004001802050340199000c0c5c90f6041c40d281c0304c2c4a6460120000d0800500901880490f030146c0c0c8406420b82c071104c0840b04014403420052008510b0104010708540c0005008d0344e841d1702c4915003490307182c46401180c0c12100e6102d08100141d00703540030040c14608031029260b0b004030410885009447d0110403100650240301e81d181c1c10b95a0320121400e4650b6000bc0c4040ca030070412403494401c11105024003510f0b044000140c403060b4030b61048400b100002907100361009480c2c081803c114101004180200c060741e25134075 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 84755981 1250 84754731 84754757
    0x3010c111501050607080f070c1221020601060e04062d0807030f080a0309050a140d180b0a090b03041113020414010c06110c0604050d0509030a060f0b040e01020a 71
    0xa0303501c000e01403aa48035030200708180100d0140c3c0c025184103e480503065140c1600c2c1d580d16031103044d40d54000d00031039807103014a1041c0544151812201c502c2100090b4600074012002905c07854140644010300c0440348114406484075800322000d882041402803064550805803542d40705c81e0601c1c85042c9030001d201007071344640464080100d946c040b0020012000030b036210491034002c1a00c04003050750b90640c40c008241c080108031105406000c01c1d4a903008070b03050305400e10140c10421401d108180c4ca01c480340007640410f2500b00c94501d8007a644440819000300c174034000a07803107070010900c0031041c00244aa50005213000307420031641c1c0070b440020540e181050b80643d110303040c10f00490490a0406500a487e0424541c0c440c44000403c18015030b150002600035024402c0ca95211000300400c200f401c100e408440ca04505001c0d003044145000a0740c0c4103811440108820740f82c0210080385041600000f241d400001e02c01d0000322011183c550007908024550300000d03012500ca50 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 84757231 1250 84755981 84756013
    0x10603110a0501050c0709021e0a030c030b1e0112090b07080a0b0d03050702040f0b1c050105011d06100e0907030c0806040c05090607150c0e0108090d051209030903010c11 75
    0x17680c21180c80d00a40707441850b116880c0c000350803000403504540b00300e0402d180d0300c0b4042c02c0100050301c0c141e240010a1044c401008089414485445000f02c00e0703c000d8038103000c4c4414161030a2102440d1007543c06005460100107028254402803005509409014009400c204000d00c10026001c0c200043c14940c0f0401c01b07141d4108102074040f9408105d02c40c054100798015040c2c0c81079060001c03030760080140207c0d2640c5523401c440c2c03031122001580281002028004d641c01017000300c41e021031031507030020b0402004801134012403054862800700c1007106d00134442000c0c0c0750710041a404180c940824040e001e050840340e00c00001e02401c0c001030840c9024460350841c3c0b0340c1c0740d13541c41c100b406e00014058140d010301d00a0310040326007145503907105c210303007e800c2602001742e50322039101003110005425084041c0042803150090358041e03055952040c292203c0e10326045880010341c60f01c514250031403003501500d981550030a112521803035000100006070300c0b06141201c5a0400d002110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 84758481 1250 84757231 84757237
    0xc06031303140708120c07050a05070617040206090622060206060a0608070206070f05070506040c030c150807030f061701090309050303042303071d0402090109090b07081008010603110a050105 84
    0x2c011a80c240304c41c2c41d0007664842050b03400721181024514080341c5880d181d2130f18004402c02c03651588180c0b41446330b298822004056800246000300c0c82c0d080590000d111030251140c1c05004080c0890b00d82ca0303070200d03031034003107510449a05010f4580741c990750020b4072000701316086402000072000000319140b10707900c00c0c1c2c450f00c52640503040540b10498200c0d041040c03030401c582000828000480400c01c24041e1074000e5108441c20304c1e00914518100d04410750f03913841101d941c1050029036a4080d00880d40e10b03030006041c0344c001054809101c05000400c0c09400a052102200303215107210081580030943c0f1a00945644415031380e10001c050740c038030903030113502410701d64801ca103450683c012040400305400142030f00c1901c0e48440152208541c0780c03120030880e1041c40144007e60601e42d102c3e80c090b1115603c28000c4100c42d49802807010400740a0004200b00100000c21a041c0f00141c140a404282c0092001aa41e410591a00314841500038400d1000243c0065158010021 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 84759731 1250 84758481 84758483
    0x5060109060c020108270604050d020d02100506030304030807050313080c030304030311011107200405070e12010617160b090901150210020a0306090507032901020c060313031407 78
    0x4141000c550781c0c2c011a00717200c0150042e607003800c5c40c90241e54075400d917110400489031840002c150a01d001c3c10714a103040c0e100d41401081d500301520507540c484e4086409400e41400c1c1c5008541520b515020a2075449144e001501038407012550408005d00030005140c2000c00c1c0c036520400503103030310f0b010361621446100ba56043d03104000410009004052103c0d00900c1e03400001fa010044020740c0c1100e522810040701c035440200202064654100116003036100291010001840e00f130001070103400600c0b1046201d482e08501d84d2010410940106001e0700c0d9154017984000200100d255481c00012140d030b00c0c0d003101300c00100362208000c0c00d0b20340049006006072031503441c00300b0b1400f840c0301801c201800c5025100300701c000c1805a000501040804e0350700001d41320710300000941141c27009002c081c01c060034141c5a10110200c102c1c2c44280550100030311005545030030050303290900345000f01d034000501004010503010700180032840140031b903e803603540810409002c1164814410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 84760981 1250 84759731 84759737
    0xe07120b0a0b04180b040903050403020111030f03011802070213050a061406070b04141207060c080601020c040515150901080105180f04030c0510060f0503031c1104030c06020109060506010906 84
    0x200400400603400c0f5a041daa8030404c50010365940b1810105d4184c0d241d0074816030100318001020406c5581c020368030354854040c40051400d05115600d100c01c4c1d44018442c2e40264032041c800b1400c900c6181d0b04940c000f41d401492110000040c00b4888003610701100c42000741881d0581c001492151a50b42c1c007140c280c01400d0600c0c0413816030782ca51b032030035025009644003d0708107080f000c07050040059100c0e4200242c1400e458564030710b0300d41d041d00c41e00c601070000c010307608050001d0360340c00007140200144204c60119681c0d48034468064210b0071b42014507808815101c00490b00300208004203800c007801e03603c07640717560b89950520295558a59200d01544100c50016a441030800ca07242e400c24420300d0040d0441741103032161f900d8000d01c00c080054440da50703441085034060740e0000034000c28041c2c0103035042c11003460418425412070300b200c414492b111000745800182d210111030281d43d100000071034143d29807800030700074026030030100d900b10701d800042911903000d0281340003140c039141c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 84762231 1250 84760981 84760987
    0x608030403080c0f0d0201050a0f0e061b0d060b220501050f1305040e0c0901140310020c0a06110310050609090103020402181234050d0503040e07120b0a0b 68
    0x342c2c401e1010341c06a0321004850080d08401c0046501c01d0240d40100041d0364008901810107561030401c44440e00208243ca629084000e000c008000c14803a0f40b00715152a2100d2189907088400e8503849000aaa608585490404604820154042e1130700500100328060098032084040d0715951081c0a142c0c040340701409400d0603404c0200c02010403500c0b8041c0c0c0c01c4696980c030040b0701910380200d2590b46640142c2d0b9041c609013840c88000d40100f140e000242405d41140020a03203030039800300e901c15200e40000b15100141000c204224015500290030050f002d84c088451a868005990560304054420310014151510a066440750803008044400c1640b0710350030000258001461401d0300080745d11060010340e64000807c0311822894080c180b0b0b182c01c8900c88000a2040c6032192614040214400071440b003010080e05460042c1e17042028031140307081807071640c003c55024100300012401007007249a84441885041d2000e4881404410f2000f002c01403148424050708114860038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 84763481 1250 84762231 84762233
    0xa181103010f031214070605011d010e0c09010c050a050105040b070315050402090d0b0f09010b033d02040605040f09090f03030203060d05101a06120f0c1209010617010608030403 78
    0x8060ba415040181000000e0300c04582c032014aa40146c0e9040d25485d98402c010408030031205007910020803141c0c0d5034103a56050a0403850b101c8005400600c80d0403001c00d028a2590081100ea09003a8000f0101d4000744070514116001c0c0101702c404980d9240c130000800d0005029018801c4142ca4880c2e40a10050402003030000079000103040591110708200c00e80041001c5186081c000d4180ea0a424050303d014210142552400000c480c000d50100101b5255803801d00880c1d0300400d5250640c102800068540d40042e046102d15004094800a40020701941000040045449941001c40c00c2079076248190211410454040c213000b21030749428002034829070013540e20640041156014040315255549800340340e65200680d13030b54440c02c0714440700c00c42c00c4c00c00210008640d0185460699080e1003030310580078109003074146449010400d0040c1c55425240104032000c021109443c18440c01d601a01941c0305820038880c16030018900741006000e4101a6641c04004502d03003451 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 84764731 1250 84763481 84763493
    0x6041b0315050c091e010305070507170d06030519030f0908030307080c0f0a0305040215031e06150304031707020d0509190b070309060806030a03121a0a181103010f03 73
    0x41c10481c000301d08000c0c0c15240d58072407007451000c44e10741080707400d0801e0705c0c00090b00300c0d14003070540000d000c428080400000e401a1030b6501d50308010181d1a2150342520002020b00708a400090a9000341c4036007003100110400540e691502030781e0f600d2000b21030f04038203586500090184c90155001000000e05160003070b240c140d048400c00b8501441c207400421140c00c20341000f4071140001c6d403944184030541c649459005811003160300800d10710304100719284000e200200d61480c1d800010740024031140d84694208210390702032440c035a1360303181c030f0300c0d00070203580350200403082100c10780300411002c520000e40f840a0030301c5604c0c1c1d0b502d403140c2001084028000303034220a100340d003901c2000c5001c204042c0074020b41d52080c2c42d1101071307900b4160080c1410000038013050080e8041c1448402007030384004240181c901511000421101010a40072800060104950017409003000003070304514403902002405c00100082040c0000078880414500c0288140399080e80010030600c08100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 84765981 1250 84764731 84764741
    0x5060a0c0e310c0810060e010804030c0c09020304020102011a1e06090a1509060201150918020306070e010e030105040b0c0c03120a06090f05040201121d070806041b0315 74
    0x2c02074048458034006801904a100c510700d140842644404500c0c0b441500401020382161035072648544040c18100002c10f03425441034100d04200300d204c0420245406140402039803500f0480441e1000e03103c80000020303500a0314200d00545ca001c0c00d411200483e00c1074140c88c4403005000281c4511101c00011a28255080d51030f4800d00c00c1001c0324413030780c0700e040010080110b070302040300c018400c0360094180d0070303540d10810079641020003000581f00c07201601c40988010b8180040e0054030303688200c805040d1800c000707405110700424811441c0e00580c0b122441102640e4854418648400380740c281ca0381a18010112082000421a52110b51014010030040042140e0502a146800b082e0b900c02c00d4820003c00c540d100d9081c88084010300030a1110074030b0900511141c24554002065140c180350f00c0400c0b0781d5501604061700c48040d02c040c2090185404541c000307912080001c0d1a4181036800b00c41d24100072101c0b00303030807010240c820210f0b40c02c041d07044000c03032011300c658028103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 84767231 1250 84765981 84766009
    0x9030e01090e102304050415141b03070527130e0a0f020303190e0906012a020303090a031a010f08070311061204030c020909121e0c010c080405060a0c0e 67
    0x100791100344e800e40e40c84501c40c5600c1240a100ba841d00c1074200c41c000d00445211107140103003480004108180179903840d140480c4074139101e041e16625601d1000880d501e00a504007503614159107004070f4035418811007603036035070a42202c1010841c1c003003100520844404680301c1255410a01001c004251001a11200076002906503032502c0ac40c0c8003541d5034005c049040e94082440300e80d4403041d03818005400c1780c0c090000e003026200080c0c0307140301455a2420303400a00305500803509290071518280300f0303644014400303081d08142a40700d24064040a020024402c04152118000985124050b101000722080440645002070131620303003250400403620754540140c3c0400105038015007c401c0300344214020b0380c0d000f03d01035140c0304000c01c052025200300b62a070321080480c0d041d650f612044070306186030380740c1c1c6080710451150100b4190080e203800c66984d510340400700c030300327075801090091045219a0582e00c00b95a05683c407804c0300c01c2c2210f900005141c41590700030710304207403140301031030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 84768481 1250 84767231 84767279
    0x30b04020904020c0a0309150c060504030e040c05040e0901090b0f070306050d030309110901080d050c0a0506071e08150f0d0f06020a110a051207080c0109030e01090e10 74
    0x80e1800110b81682e01070480300403581d000c8001c0505144e485040b890281003417009003168412a40002001110f91a0000d044d0a0740c0d8004102014000c9035480d01210000d48103205078a03040001070120f0300a0f204059118045000041e105181131054485450348007602c800c4d1511000042c0200940042001082c90340d1914041504e98a00240c0300c10580320340e40125004025181081c4a014041c04d12030050080000500c60000041620759030703500c0c40d281064444880e46039030b43c0380213200358010f001802440d003400750841c4e00c004c903480655131030008500d0080b030606d401c88040038121180d113802c4083c04640400340c940b84030854003107103008203000204c00caa1303150801c03000d0715590304907191540043e0389410300703400c0242d000d0041070709405054210126100d03292640b042d40c44207806054006070300c1c0204403083c0240e0380c0c0e050269008014060007480c003e48110442e40900d0b011074880341001801d014864204d0b80b0801515203c080343e00c1c80d02d00a50f8400c0840704951a003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 84769731 1250 84768481 84768487
    0x130203060d050f07093c0b09040506060108010e04170304020109080d080f060d021e041503050a0614150409030212070309050a0501020106030b0403080912031f08030c0d030b0402 78
    0x40b0324100080036425204070080c00320203140400403130840c0c170700304003030144800107030488110002c81e010300e140f04101d140c5800c80a04418020f1800502803185220391004800e0148414050002551032047e0820b8aa66440c2c1e40c88404040c6d4602003220001c181e400c81081e10b450303010010002e5600701e032040c100071450780e4540d000c60b0b003000d40d54490038001500075820082005101c00f51542c03c000e0541e1074400900c010b0300402c10688a110021742800a020ba200000351200d9000a042c65040c05410300070715241e24100f5242c81c00e43c1d1040e11024180324488604662140406010300d00b0341c2043c0010108940c00e00029000d0300c1815415809a0705500c640c13100084000d00249200756140604941040c04105007004a03400c440c0c11689480018000100f90760441604550036082000c541d5507a200c03180e103049450340f0760502c908408400d028007c04001180308400c48402da114260903140e5044960b60b0094070300610350f550006100004560003548218001c070800340c4003501d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 84770981 1250 84769731 84769733
    0xb0901090e10110f040311030705060901020a0204020714030703080a0b042702010c06060b070c090e030a110309040911040f0e060a0f060b040f150e0603041205160c05031b130203060d 80
    0x30344c0790407a81c4240d800d64031061601649140a100c182e010748403c850442c1064a43d0380001e58501300100c00a00407940064004c042c1701101c109881d464140340c0c101c82d0f4a602c0ca1400030031030402a280c0301c0c0454103200c13507a10f043c130701805840e50b2040066030640c0080e4080b54441b29603500000141d0500c101d00c02d05c800401c2160142c3c001410040209950782d507510700d0030000c140e165038400c6000310300c0c0c8081d15919403c0441150700b108a285056a0b203810b44041c00c0381503108400d146035000345448400c004101501329092000081103a0400580b040303a0a038005450283c2d40340070591304a0030028010711001c1d0f0024201c034842140010b441500c0301c00300c010b1035019400c0751041d14405c44041064140b4034200c01e210311041e01d0040c101645030b02c00710324107000c0500001d01c1c26901c086009170640c80342e81525024010f428003001400a0740c149070445919500a4a00078042d040761760340c1020f60a20481c0606d00040c0c41b62525050202003007000790800741041e54005002c0348040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 84772231 1250 84770981 84771007
    0x20d0504050105070905060f030c0f0c010507090905090303040327031407051002070f06050703050f03070914030d02100203061c151a01050d0c09050d060b0901090e1011 74
    0x5118512801c0001441c2c10410800b4211500c01e900c5544521410400b4101e0141101c3c1507913001081d0f102156165821030210444a01071802c40004562a0400300030840341d01543d40c100702d480050f02000150cc42d2913078142c0741c3c8811600500800e5201100b2304100c00c0d40d82102a200c51040d26400d407441c0c9079a00c07040340c045005501003c50b880070f201800f0b60b1409500028448000c0d000070800d040c034103442d0341c5088000e84074900c00d202e13020a050003854000c00459150f0a61b590107680e8900e4101c00140c48880a4081c902120302d48c4402c681240c00c0006400000d0326094000f4580c8a0301651b070580070307510042c0141c2e0003a000c40b2070102a540740d07145200e22540305451401c6212201c40c82c640c2152a0302ca0a9040350411030522034080e60030030225040011a030602041c0e41da81d000c3c00b902c030210785510071500703c85808064410f0160603800305454000840305032440c2e903038881c080700030f86146084451507504108050304e444a104c1c0d10110b0f41c418500e008500304642e038408a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 84773481 1250 84772231 84772241
    0x3061003180609050f01090b011404020415030207110105031005090c1204030f08130308040b18061e010b0a05041217070c031406040b0106030e0f0d0504030b0f0402030c0f04020d 78
    0x850b078050320303204680300b04074007406010030424400340200140102030700c0d81c00d15100180300340044050894200d880a0f102c030b40480e0b01030310306004007402400282b540200254022003054840283c0b24480410a6108030700700c1c0d01900b084400b52520904010800000340f030050810004c0d171504011200d681043e448419204d14040d8880b200b042804450140031071400414001420448904203030000c8d0300107007195003007034221a14903200e039529035180425a814424281503031140004100451100702c0b085000e0600c60480640b040e669030003c0c1045008500c88040815030501c000d004001405280210080c000d008240d440100c0000d40141c540c0002d800b5280108020024000d1000d458900040400b024005068600d05600c44400c4c845042c01103408042d00d811040c084a802007002a01c060030340c2c41a2010803800001c0030f0000c2c1e002d8401110308040d1100091300e2815541c000c98840c5130007502a00c1712150003c20401e0113441c4851440d482a40bc0c4100c081600e80c0380f0507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 84774731 1250 84773481 84773483
    0x2030d0f14030618090114010308040f060e030d05090316060306140612040809010e06130602060615040e220507090e0a030203070209040f02060f0301090b040b060306100318 76
    0x102010144a200000c0c40ca10070301c0c25600d165642042808426101c0f03180e1105001e40440032510305499401c0b1550240c40340b16100c040d20000500040248110f040041040302c03e5140140412603071514240c800300600c112699054110410b0008054010310007000c5050b40141601ca0318098510054075507040ba400c41d00009540e51b00034000c0200060081c4030200040303480f6800c000d0701a104500042c0b0051004101c80d1000c100b034400c50740a003c04080107103008101c251607251044480c00525070a00c141001441440040f42550034402d10342c4601a40e281d060511781802d0080507000746102502d400c0e254420205014460103040081500c01c0f8441e0010f864a50719214180056039910031030f00069420055040000030303000821a40d2903641615140b81075510780c20100703030400070310b00d02039000000050030190269001000f94181c800102040154000c40c01c00e22084070310728200aa0030860800128401d841c06104414442845180100344820240d98035403061200d280 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 84775981 1250 84774731 84774737
    0x9090f0d080613090807151d010f0c03050603070605070314160c05011d0d05070902070311150105090403050c21090312090d0803070311041409061806060a05040302030d 74
    0x7040c0003040c0360242490712081c0c1001c40070f1056000300c0e11541400c2c41001341c0180f407002d0f0040440b2103900301d600320f03041e20380001d0f41403018448603000ca41d003e40210038064200b545000e19140085009200c3d031070061300050010003860f81040420f8074558400c1c3c0d815002d01401c00e10020101840b00f004101c0c0f03131100c641d10b042d007550300c0c0b07000c18040c06190003043c1070086c00b00f038210000400c0c511100380c1150440300381459001501304681444095004a89494000108070060541001c8070310140c640c040102c071f51802c4209003500500b24207010303040e4440008004178002c240f040004d01f04c4c0ca924030098461907541c2d07c10744940c40e802079000c0101640701203555411131800340048421550700400445c540004280020055160000c0c0101041004070104861900c00c0e4070158080c122032242c29030301c0c1c1e29190b0164040042840d1540b1469072140000c0550818a10f1100d0004601380c6c9200192900d804200309600041c012008103c0c09100005c050783c2c080042500c0c090150b2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 84777231 1250 84775981 84775997
    0x2e0506040507200328020607020c09060f0612180601080109110409050f0a0c090c0801030c09020f070c08010204170307051c11071d1b07020405040c091409010e07080c09090f0d 77
    0x17002c06400e00740010840810b40d0010502d80c0820348a8240c2030354081d6045602500c20144100000e500c1d000300383c000d00010700300108220342540d02c82c1d5800003003440001190345984e41c41e04001c1c2a14992540103150102c6900c0a080d07604140e0030260041d4442d1081d6107c0301c4005100914041e5090710584501404560800200006108040a06842c1d1401003a99815500c07002922079091050390703207242d800101805d00c00c00d031030280e80300d96602040c420591580e8400d2035000c0e421030300812528038213003080c6440110000046500043c1d0200240a40300f40240e0882d0444582e130082c0014000400944100650180400e43c00b900c500707850a5640440c400d0100c680360300051103071340d05007613000c0e480e611000d40c2810740f020706038100c80110b1199100d251000c3c5030050f55200c596581d04180346c40d071145510103910b0303204426280017081501c0d00d021030300d59200310f2403282400c1d9070014200c4811a04000680300d520031410380490302c1860702040c2040c501020351184c4c1c00015101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 84778481 1250 84777231 84777307
    0x513050402040e010c020a080a1707030b01090b03060d120201020c031204061407140901030207140109051006050f04020c1204080706140703090603020c2e05060405072003 75
    0x2e4840c40303503a075100b00c0c0204000c9114541c003a50705c0da4040f80180003000c0114031020598400e03803881e10300c0260624084864280681d0203800380a682e8142070102d0408400420384100c0041542d1054000070542d2901c82e034551910b03c514007500c101141155001c0003040c0b4110010002003110b079500c030344034000616203400c005045031a4040008100ca000a003441161940080c0582030074426803029541c0b400c01c000141c00078482c001005000146002d18101d4210065008180c2c0501030b0050343c0718108403101d03080498806009540c3d2104090001e01e1131760400340d001e44110310450044400d036480c0701c02500076907080713680070740d109500c1100144000c650140d60b282d200207420301941d00f407000da541e014101104501454003050b034007141caa054803404000000d08500e43d4141800040056032010740014000301c18000d02034144000f0520a04240c45020321036a2142e03100c4048a0880181d07805040052a10304190300c030500040000040d440310001100c00e040d03075440c504d9005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 84779731 1250 84778481 84778489
    0xb03030a120f020a02061602010b030d1d030604030219020607060203040803040c0902090306010302010c1a0921040f0501080408070501021611040b0a1401031e020a030e030a170c040513050402 84
    0x244075248034140340144113849859400164254000d00117107009040c001c02d02004a00602180350340c50740c503226116084d01c0f4650031207002818400500c00505082c500d03102403665400c800e0741c0041c0142e0100124441c0032401e060800c0d06244000c6c01d03e0324000700e985482d0280c0c0c01c151001d4525420000a04c000c000621411b10020701c3c004105600f040c0307a540001c5c2d1601014031001c0c1c18840403200d8801081801031121454804003127000384907050071884039540c0c1910320b40c3d000c09864101480c8280407055001c1c1da04442d81e880c0e10342c1c0d00c0c508003401100c10520181084688820074072000000400a0019101c00d80301e10251002501d4241001c0007000003c8503002e0080345440030103460346d150f090a40003500c042c44c0c59014800c0500d00124010000201100421803c44c030b1006105101c580040010711300c1682d003880200ca00707424903500c0f48140401030009c03032910346001d05801c20720030b01c1c95031002c58800383d07070305081e40d98021852182c0e000d400011481daa41c0c2c2000114070b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 84780981 1250 84779731 84779741
    0x5031f0509030d15080d0c0809090a1b0804030801050a050306011502010e030c030a08070306180b1f02010b03070509090d0305040c0306020706050720070b0705070f08030d0c0f0915030b03030a12 85
    0x20390b071a202c407209001c8e4a8058540c8140d90f11035000d0000d180c00640c402d0a59004027010025000c041910f9a950b410010640038084d0b5080340000c40d0000001a00d00d001030642c81a075000401400e40d0b6480d03d01451001c2480c07044075002c1d0354a0b243c803c0d10010060016040c041da503030014550394414250700806110b80102094203040c9400d005004901c8840f0040b09a10351005000880c9144000010808200089010200c01103107243c5140c0300e5064000c00c6020b40140c0c00c64406035296010414070311001c40c3d0911280d40484840c05070715110b600115001801200306c010003a07240d4644e803099a200350b10950f070050b120f10a210025a214032a6090446017080540386491411030a94440f4002e1242c100128000701d1a00309101040c03001034001c0210700c03111b0718040d95440e00c50340c0300d420440d5001100e603d040400000d45028621150700e4031020392f180107031641003184040004040f250711004040c1d40321040840390314100010012409580c94045070808242c035101c0a5130 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 84782231 1250 84780981 84781003
    0x5150702151f060e040b0901080a17090f09100305030711010f020d050406050d060b0705060106110a050d080c0c0f01050a1505060301050f030a0c0306020304020a05031f0509030d1508 80
    0x820b16a0b11821041114218081550740610301500d007021004001005080d55101e401d5010701003000010342c80c0400190001c11a105010043c0b1100008150304014011105440d41204500b0190b42c450314000f040d00f0342c4542445220107d060301c94841c0c0380f454011590894034008518201c2d9015a04028940314410051001301400051148000d0040c041c80c4101d0f014848041102109002c4c41e41200f0007a000c881441910786043d420300c41e0f55500d0a21454021940c2211802180500030035266401070b00107009121400b901002203030780e820001c0501c504c00740c0c1440700c003080c101d007400002c0040c550580082240e08144a0300006c0706d40d07907003c42e01030070f1780184204680d8540e5016241160412100c4da0092034074171000c207040c462a000000c0240105402c08010402d0075400f56018034000c2c4c6503020860b40b901d0605907a1502506680c4030711070b2004000300103040d66080f007540926944144c0341014881c05d00581502c9020040d4151404450000d00c4840310800c2095014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 84783481 1250 84782231 84782251
    0xa090507050d0b031f0c050c010e030904060605030c03070f1218170c1504060207050a0c03030e0a0803030a0b0a050a061101111201060e010306150804020306010b19030203040515070215 81
    0x940d076034401c0c91108018605d04940075214070503411090b008105035007400210800074488c0c4e414039042c15440b60301036140c661060f480e110002c1130300ca200d20280d038840e40300106150703d19129440103a69554440f20010200100c42180328205070b402c0c0180c3d000208035164200c03401d280c0e1300d480c201030140c103003850a070b1441c02d101103550080001380e00c80504545190101b21610707107041c1400a403142c000c0c0603001d4070070000c0d42401c0000d0404c0040450b4040c1d640d25103407865040c00c2200c40d0b141c40c80340040e590302c14400b15007a15071950100d80600d00c000d2aa26182e0b40da200800e03800c2c05658400070200d0805490894000000e004141910011800c0145071544544081a0350801070013947c04020a61131401082d9010741d018030050300c00d0005e011504559148010000d400c102c40480c000d00980c400081d03070309036072020f507031040c95962641203540384046000c9000303400041040e0349520075074148404c880c01d1001100d000d4502a8080c3c803441c2010800c45e401c3d400054404121 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 84784731 1250 84783481 84783493
    0x80a02030c070326011706060301110706021c060803090102010e010b01020607050d020409020409021909030c2c01090221010513051f0f05010f020105060d08090a090507050d0b03 78
    0xc5008400110b4035841d5044c1000400007900e07840c4000d0f040f10a808455840009400100d00c03201688031401805800074111203895a50000781400e0b511800101d030550b030400e1009100050b090f401901c0606074950a041406002ca45004151101039201c0b0500340c00c0021011485d503428003400303890075203a030001e20181032038000017035483e00010700d06800c01c1004071f10100074aa180c0c049400500020106548458558503500700070f600041e448041074401c40c9188003080d010310710341c0007103a0b000459030100e9490f01c515240d100140d030700c0c81c19002807500b10542d8110824800c45000e08040900141c9a40c9038140100c448911450704c0341098124400411043e03a80e4040c0308420310003840017080e01c1c0c0341c2940e5a409200d20128451008000742e0001c10707800d00700280728003103d1003644e8449640c001184264200c0380c0642d690754000051280394000301e0403120050840f035001404510045aa512904084030b0b010380f0020001a00010f019581c0140e0b4000d450040c2d01c22005008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 84785981 1250 84784731 84784741
    0x4060b09090403080402010c050f011d011b0e010504170705040617030412060f0c0c0b0a11070221030703030605030c0901120b2206020c1908040e060d02040e010903080a0203 76
    0xc0c840708014002410000c1800000b411644911a40c80020b83c1c08400c0b40c0b02142d0343c0007014080d0000c1103844a202910008400000d0310500411f45c41d2000920780031410540b90f4821504152510030f0181401001c000004803000d08035241c0a0300544c05014100391403d240c01c00044d6641035004c02c1c3c83c0f4020700540c0030786840c00b00c01c50b001c507a8407061051008803c1c2c0ba0036000360180324a800300c160300c0d02d40008a529003055800da200383c1b00d1101c03141c4075510600e5800460b6100c404224480740d0910002d0f00606000c02e03030303c3c160800542c4601e102d1802124182c5036030301500f42100080c0d00c45e141000141801c02c242403141e84200d841c0b60032981843c0900e0307108031800030064008502200411110b4040d036116005501c1c1c461009800e10200d801c0c001e01a62240d0103400d5140714046601c11031005520048203030550002100386481d02c2d001000f46841009003d0942c1711b40c0d1b404070714005988078803402c41a256414004291840c050602400c0d4002c0241907403030447c01001040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 84787231 1250 84785981 84785989
    0x506120c0109060c0606030206030c031f060e0d080d05010f06020f0a080d021803030406020d02060610080402130605090103060c030e06010f1a07051603200306190f150504060b09 78
    0x120554003e031400702da0241031402d141d00030300403d80c00a034005000005100903100000011480703428501b42c0c4006026000e400780d07d030004d007072240d0350001301903e290340c19625003040100b224070700a845072420040c0501d41d0000f00c030001e90151010081410042010f00d03018000b0f100595041d03800307009444540c5d1242402c6100b10f10240468039800941b00c94010600c40522050101c017a0880751a03e0715494080c0d600c101301e0003444003503c10240007403640c1c54540a2060446520390341c0e0461a1141e074203000e450704441441001c05500c8110200c0c041d01c8042c1084d00840c081c107800b0900c1c0c102d2a402074110755603559591823a402000c0140401e210414401d01100d800000e20000320207a40c00d4900c1c14080c8841c020f1403230142481412401000880d042c0982e402200441e544551180c06100d1035050a0b61050b016084040043c88200d002107240c2c951020300c2c030001c50000700c3c1b10f0400d41280e404c0b03a03001b9000b805010041c801401c192044002038504404460724040c8200001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 84788481 1250 84787231 84787247
    0x22a1801030b0708060102030d0c020115170d0c02030a12050702130c0c031103040e0406020301090606091203050a03140f070206060a05030309060d020412081206060708030402010806030c0a090506120c01 89
    0x60148469130001c141107034800c0088030340000100300e04008040300c0c1400280600201a07442554080101000c42c440200d0510103c000390a0270050000302c05d0070a055882a00c8054242e0340b501880f144107001c508444e00741c0c050f544031659101e07034852491041041c0f4914001400c3d00342480c100d034411100d90811030901c9481c0c0c050614a0040440d40080c0349141301d00c0c0c11101c092021302c400d01c0100642da40295042c3c4000c0d61003448800d0b240c085c202c03501d541c140300794058020201200e10110703016200400c681e20007440c02081c00c0d46000400c40756260191201c140c800703c00010003400030760520042d60480c0f41129203008180c50080001d60304e000e201c401e42e108400000701044000728aa0484008110003880c4d207441811901b41000a9002003e20105005c100e40c00902180b07040412140401d6100c0310060554455400444003100f0044c0300b6505441111201900f41d42d80c0720400000b000a101d01103003a141201c24442c1c1020f000031207003032035440303860300101c04e03a003012507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 84789731 1250 84788481 84788491
    0xf0c03010608130221030403060b0118061202090a12060b010206360a0516050105030f01090203040c0b03181209010903240f050703150f06030c022a1801030b 69
    0x104208505000140c0c10b0145900c0400d12039045c00a00c20240f10040b01402c100d03401040b003009400c03456401540c2c1050541e260170b238901354123003040c0501405024050019403a40b0001403c101d4500702140203629190000f400c25620341e01d5600410130703140154400044284003a00c07440c2840c480c1004e8030320b074180100c03680144039030316107585552211189040701c10b42400ca40030b0030300b18285161208410b060010f0301c000c0080340451f1550291080303d015954803501c0f151103a1070411105c1c02504094002c0f0340c0c0c6200300ca800a848d00d00070b0040c47c0642c083d0780c03202400042c0034800d1450710b120002e5803582c5040500806140340e800160f800200ca0b0001903110515650380084003408003004504480c0300d00e0000c038048104480d40c440c92260f12292020004103660229030b81c0c10765030b941300303400040816000a014080c4260000344025040d40121084074120310108000d50403114592140390060843e0300d640e0b40b0300303000c4041c550002002c2130001d55046840c5c0010030000108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 84790981 1250 84789731 84789751
    0xb0306011703070611040602120909011502190605060a050f0306160903170a030b0f0a0b0c030f03010308070203060609040f02040902010e030303091029100c050d0203030f0c03010608 80
    0x62414116002441103c1889601001c10804640032054510440e041801980300612640e9600e14458228008890710030000800303010b01a860014600041150910030504500510b40424150481e48242c0ca4080c5c1c41120003203401d2408500b0f01c1482d484650010b880f41300c14100c0c00c00c564a01080c005d030490413105000c6100c85c42c40809541c680015030004001442440c98003d50f80020800303052001f14668083c171640d1294400c0103c219258480707650b00006403941006000700781401010900340001c296410880344481d10748154009900030344001000240c09404c503c0c081c01241c3d0320240031640c1401908150b160f5110000b440c1e48004e0040b681d0b1410075040d68028844c0707004904008040301d90300d00d0035040180d12103408203040a4541d04100a014100a00340c0d200304205500d103a85511a506803820014020070300240c5c0002d00c000c03084050040781c4284501048240e8940045d6581c3c101001c214070942001040b05a44000600c014801e0ba0f40c00303601140c02c01145a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 84792231 1250 84790981 84791009
    0xe0c0112050a02090a0b030601090e04031b03120c02010b040b030a0f060b060d05070c03080709080a03140d060f0602064803070f122007030201090f1a0a0b030601 71
    0x100380b02d00240f0801884550202c2c00c814005003002e036071001540708220a0380e03450f400b81d0360740c121035000405c1580c0090110f41b81801709061504408a5680407a001349400d040c8400205030b0201250042c071100c00042c0d4441d1144506414240100d00c40d94109034018410070b49551104110100d0068008218a032501c1c01e800c0a40c0d10101503420001704404104828240010050001c2003400e1048000c60100400501007a0060a541c011101e016000c0c026080059504940f9110303c19060f0084100500200c491101284624000341402000b0441c0040c02e04502900c0c16000409a071189149104101c40748601d00b40c030b011f942955190001c509951400c01e50312040405800048403840100804c540c42d43d000c115403c00c0815916107851030b202c18412032080d5020b4000124417410400186a40c902c030080050031b03050301a2000150343d10903071365503a80b060030300c040603101801010165504074500c4141d02c1d40021002c5010004000b010303002c41d4540d40c05100d0481004d44030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 84793481 1250 84792231 84792241
    0xf0703020705040507030e0f06220c03050609010e150103080703050705010b090901020912010e0a030e01180306060e0903070f02190503070e0f060307031e230a05010e0c011205 77
    0x801c40407020748401042130003c0c0c40c1c0850020020556020035081c40d1150140d4188040c1000c24864001c003011103440c0640250181c26200c810080001151700380d00c66000000421011700c40366018412500010a0094121065900e0311100c1c03409002c00b400c1003801000001c100c4411120302c00d41c1420007a8898900d030074260300600321729030740c0e41e0041a2034080101890301940140103c00c0201ca071400c000401c080c0c224221010245002c2095101650302c1020a0207043c0c0140700600501d003d000401414000311002034a0b6842100c070b090320b5081c01e002254000c80d0710303680600389100640c1841060384a0241c4c142607940040c0c000c01d001e11400c610881e80d55401c40191130003508480106075141d40007004650101c420081107200000810002c1c0b40c003044600c11a078020710040b1b5040c80c0d03050200c01d412014201142d046010b440100003044560b6a100488003000d0050300d07040c106824014203490010364420a141c000c0d0902c0122603801c400b8034000c0e0b0303e42a1000803a581c075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 84794731 1250 84793481 84793483
    0x61b09040507050d09032a0f08030a0219090e010b0306091611010c0c050601140a0306020d02090406080105160302031905040606080105010b1b0705010507020d06091b0905010f08030f070302 83
    0x3810070107001c19080c4030051040c160041401101e91f044031405c0140058161400c48024640403402000900d101c1e855901003201c079806581c0008086070010b2900c400c20507090712541d82c0c000d04201045082d102045104011034000e03004041801505241d0b01c2c092001962003030000b401c1c101c0c11200d1145458601d48035604903114050a080200480e004150001e0000010322100716507500c1803000100344c100881802c1008040c0240c0482c413214210782d100c070040d40040a01c5a00c10f90b0901c07814400781c0d298010b09005004d0a4000103241c14910440c81504001c41d80072000d16004101b8000715081001c101c10002e210301d800000c440e12907243c03078005810594400d406075824400041242c25583e4020007482c15081014000e01414107a84c40d00c1d00c420703100702c5011400c180003600150400e5500060594421040018104a83da0310000e07070144140411400c03d14120042c84150010701c182800350a05618440d0014038102810780ea0f0311a1000c03020180da00411402c04140c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 84795981 1250 84794731 84794737
    0xc080f0307090509240a0807050108130f0b04020319020906010c020102030705030c060708090a0302030a140d060609060e04020301080d1107090e061605090904060506060403050109050d02061b0904050705 89
    0x10002d0514811713003841120f0640c68050300c10080c03c540342c000d070f080c1d20511b4a61542422a1290f40241007481d10341001550b880400422001d52084007031091000500ba000c03c8803000e0b441840c5541d8507041500516241041680d814003a00c541e0000000260340d5848206502075007d103413881745080d031840100d0840c010030b40c1c000d2407031002003501c90a56001040d1f542c4561a9591650401c2c1d59040c22582d0300c07141c0b0745002d009138004214809401c3d20505200d0100184458000e14002400d444001211555488840001d1084c5c1d400d110181c1d0191203089203407000c030380a40c00c65043c034030718a0300c03988005000d600f40003a800c48800d41842c140720f80c03c010070342d03031074100174065148882c07640301c0c2e90071a4000015541c40d113180c403001d4061026200d042d40050a20310f050350380d030754031030300103000140c42254003020611001001490074050103694910410152030111149040a890300602405c3c090b0340000c0c80450124041aa40c00e55418400031500410b140d205c100064500388 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 84797231 1250 84795981 84795989
    0x9030a06020c011a0a060507150209120109030e012c120d0c0c050a0e180f0304090f0b03150408070309030b0f0f070206062103040506120f06010c080f030709 69
    0x181c000308102000c80700c10740c070654600101440c28076141c16190b0400004144a00035980032480500500c2e010540350b01c0c050076a00b90040d40140f801c84000e0028201d8001e11441f00d12580d1108500c1e010181d0049808500402c01c1c02c14040209400c110401c0506110300324440743e130600f8004081303d0780c0701d003e0306815218920942d402007140540040c40444442016544a842c036140000c0030305020840c0d83c100d070121030440c0c8440c1c41c0c44000c100440d01140b03501c40c641c850f00c0c03026424120107000401c018a00490001a5207d07400c4903401910501c949540c8240c0080d41c4440d814154002501da10a90107003c981e510308aa1a013a80c115215800281103401c50008200a01e104520810700400003024121015a01c4140c101c1c1d403002c0403505240c001e00c2100d2200f403006080203202518030500b5041d0b904081e1a000800c3c16a080f00b560801529400014000240e4400c0c02d940e821034000e00c0c1014030b42c1256143c400462140840f0070940810000020781103d10030b4070518040c1c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 84798481 1250 84797231 84797243
    0x81b0a030f0804030c0e0705041214060106050405032b120f02070b0711060907052428030204081504020f18090c1206130311010c020d0f0305061509030a 67
    0x49801e0b800c1075600380d046800110382d20002c0c3c281c04940b030301d500e2118605c200c246603280342c589400e040c40b42e085506061400c540d518012a0540c01600701401058060700c06582c5094880785001d0030149000c0a501100340c040440001840b00030400d000500070030112402d14280c10f40ba0181481e008050421145043c5480402c010040210300701840e40166500d07550707007c14003007510240343c99460a8030006010341c059841000b403400c0c16800002050225190340d143d000d00c0b043c4c440c056038020b05d98000724003850402c10440e40e00042e6406046401480d0841c10141805a4641c2c3e900340b2480801c0740584210000d0704658403102c1c16410900054076451003541c8030211031107800000c4c0c629944038041d00c2251b404a040c81e002c410244005000201010303111644080502646010b0907401c00c000e0503010150041c0034000e07554542c29a60052103a1061100700801040303110402508250424050090743d58403c42d113480c9610150070f0b15a51a681c00c000030b454441e003042c0046c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 84799731 1250 84798481 84798503
    0x60f0a060b07120302090d0606032105130314010e0303011d0c030f01090b040b040c020c0a23060315030d050304030f08090d2118060f020405010c06091b2d081b0a03 72
    0x1044803c0210b600c0780b03880380100100c0d030980084180c4450003000c0d03740c000c01a8804040000c5061960b40b202001501d60002441600d1705188904683c400d8005c0205140f581000300300d5901d00c5181e40c0da2003110550024158282500307949071200040c8a10fa600b55120f11b151307280d950700c0340d1151061150051041010300e0002901a403a44070194255200c2e410b007080018404c0118070750703600000901c41d110115001441c040040f1900040c01c0c8410403000050032100c00e403000c108042a0400780d441d01c6440e45014130707008210303220080e603d80c100000b99003401401030000071000b03102200743c01c05541c03c1085001c12510304803d22204c580c010305001c8101c11142e40c841c1c43e040002c2c003070f034414811603490084400c164030846c4aa02d00151507012240040b03a0590701c2007000714410403030b0115038600c044181c4006082c2c0d82203a030302d440e0b0403000c880c018072140e1011704900264020180400345445103094440281c203010100f00c1451fa2309070011035803012403000c06140c0c405034501c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 84800981 1250 84799731 84799733
    0x10e090f040503120414060a0209030307021c050604200a030f082b021c0b0307030201180305011109030c01090e0601050c01021e190302030c0f0c010b03060f0a060b07120302090d060603 81
    0x1441480030a21b03102134092030001c65840c441c103000300e900440c0007a000f5480c04d00d9a80c00e019003980302d00d0603980c03009409910700000030030900443c0c0c00399000307400d265612080d600324407800c80085803003603110b05400401000080c80c01c0c808001143d400180054496000200c101b140130003420111402920103803282907900001d034040c00d451b1205900d803900041c032464801c8215200c201303030660305900801007040150f2140d01c800d600c00d082c07205c08510995507955240d00f560b481200070107407000d02144205581c1030800c80b50350001024640380508a140882c5106400400380010341084400501581c070f03183c094044130303000402c0400c2a01400103400702c00d2003030340020544184032503105d41e00c15411442802078034060003813001d1440c94a0300a030324040722940b000341d021049540302c5060400307940d81882071520501503143d50000b2443c084031003034101c40050304070740440c2606200810100f5000c000c00f05440d541410300580d1009580c0c0003038500486640020515418103074080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 84802231 1250 84800981 84800993
    0x90807061b0c03030818210f040e0109020a08090109030905090606070b0f01030501110c0d1d0603040c0f08010c0e06072607120309020d06050a0b04020f07020f010e090f0405031204 79
    0x30300c030b06c0c284662044032204401856031076500f00400e12690400340e04040344610b803210001c0c12146002101203282c2a603d0700030940c2d8100990008104503400b0504d48881500140c1c0c0da030707100340f020000704030030002c0c0d0760094030542081c0151401654464002030a40e1120401ca50420fa0003054119591610000402040009000484484d400d05032045d200740145810f4030303808901040980803101084c4001c44000b02402e0310340c681c0075090300b96022a61222001140a0360094541007081801d0090008070720340644d00526840e072601000b2070f2103d0b03000112200c2480211055a80c52181d0300b0b01410328511001040951904a01e00041c05101a401489590f00c40e6004005440300d181c0d0540847d6035211019401000c14146034002603419070205610281c48000014003c40c55000b050403600114518030554000003030781000d501c0c0000b034000d401c0900b440c0407031501036494041051448060420b084048214001c101001820301c2a03c1d400b200d10a04840d1602d002d003410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 84803481 1250 84802231 84802247
    0xb070606150809061902070b1f140a05010c050123040506060d0c0303033909050303070206040b0a12020d1b11120a020304050414090d090807061b0c0303 67
    0x80288100041e03032404a41d0180480c00e20491100c03015115a0303035583d10103100b801080304a40138403070f07080081400241ba024080d5005106020012250306a01401188003692542010b6048020500401c52546c1d643e900141560403c2c49c10010a00c503500c4d11a0150154111030080e014401d5440c1c1181c0c131200c0d008074403443c010001ca403120b0720340400f401101c9503122405852001001d40903c00709000c0d800c50f100040404210b05141c0c00300c03182e842581406586800145140c0b44d500d09030182e41725200c0000740c44220080e500d00340c45540007602034841c61040030700041001c191007c000d8020882110307991103288082d503035000b0519181009001409a203c1e813000071040014641d8420118040380852480c000c2100e024546803a4081e5081005030404502c000c02c4045016102c901030345c00002c0b800c6010030b150381020306400e0f0400c001c85450004202d24040b007001030700c1002400b402241e4060071b000d0343c0c2c0d40c4800d40f641c1d4060070380e440c0a842034030b100000200b016400251 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 84804731 1250 84803481 84803489
    0x705100b150901050409020f0c0a0b070908011e0b0607320105040302100237031404111012020c061803131401020a0c030302070503011104080312040c0b070606 70
    0x1258465110680740071403180650450303640001c1c02408103200d1159540c5c001c104801004407044d0400400d8680340d0300c0c140141030704407041c09544d0700b84a41c15402c004075070042c0104500034815201c940c10700a040c40384e82410404aa07440d20201a0380d512404100c400003500311910701030300801110404034001c8000c1403850450200084403207081c0040c030403c1d0046900d54090920b242845010700044d402030003181c81c0c2101150104003907407103042c80311054180c200c00b481055208003040a41103076114441c0001d5004410104000202854110018450308803400c010049050008031020b24508030500c110b07901c0061f503907800c514001340300c40c4100241d07940c0b10011141100036548901806904088403880c0e980709200c80c1500e12482d041c010010b1046440980003500d60310382c140d4543d4400e50258110301028055800c3c280070f510901c0022101e494949450541d003166280f042515180c01e2032082c0c0c00ac10200308800007020000e1010701300e159120800c2d03040080007021a485 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 84805981 1250 84804731 84804739
    0x12060e2d100312050711090c040506070f060c030903080406020c0115030f050d0207180908120c030906010b04030c03080d06050301020406051c05010806060913050307060b09070207140d03050705100b 87
    0x802d40d24030890440c0e03181640501b424104083ca00c0506c080010050007180c1c004006000c00702e043c0e03d400c0083c0540754024810240d0768400340c2401c40841d40390686000402d401c0038110302c0840d401a102c141c00c9544000300503a200c12000345640102241c580d0648981d4000310000148441103001d4006540503406031922120300500036a52071029108a00200b10034080702c134250f0740d50303611040003140142c01d01c130303c0d00903040d54914800c0300440310b0801c50500841885510700342046054054100080490b00d014250b841d6521521814800101508000190380d003003803a240d004000203020180c029911240c4881e400340258000302c14a84154206540c40880614117008242c100c90001e0081c0005403100700c00e1000030103005181c409207080c01c3e54080f0006500300700600c05917004103400540f03100003008019881d94042d190a085510004042c411072141115800d403012040f581c0311a04020792500340c550707028620001c1d02d54021600c0003020010701d81c1242000c0c4004a07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 84807231 1250 84805981 84806003
    0x715090602160e070c02180403110706080601120c0c1a09120715090203210405090906070207050123030f060108090d05030c03060d0609050c0112060e2d1003 69
    0x303400026141c2e00c92041c400c140d00d100012410150041d45e01036549030000e010011820480b40c00704001c0b1805070340480000d401000081000308052000d04094552031400320b545003410302c0003c001440c000c0075511040e5171418030b410341d5402800322018056022032012025400d010380700501c402d00f207540301400e000b041c04400050740031504450b2550b0344002a600c095100c400450002c0030042e03400c81c1c140c461400c466465040351103e1400d000341d076144103075841d4142010301801706400780107030406500500038810754680100b02031080d9078080c68000107005c032800b10750a0302070074450a5280c000000052041048009181034880c1e6800e885000203034640c4d90a56550f039561443c4840054000c1c000304845400540043d03400600080600c110002142c40d03a60407270383d42ca40c1c21107869002019510761541c00414010b0814407070002009000c2c0350520b0030740300d007000030056407110140001e107440d42200f01c203004480723203001010342d006c030301d0072660307400c000081400b0656403204c0c60 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 84808481 1250 84807231 84807253
    0x231903030f0908041503110c03040510030c051b121804060602030f03040308060d0606080604020901060315061101020c0304060801080c03030a0f030f06030b070203041d090712050715090602 83
    0x18082c0c00314160f84001020319003843c00d0a50002c896140d0910010076842d00ca0103515071003150040c00c40011408051541e5511300810001201900b51100d024141082a84500140c00c601034610340b442403c60315407034000c095122800c0030f800c1039803000341e5000030900080140b894007043d0f1586a09607010030005032992016642c90150310b00981240c00b0070000100020310450f550794205801422407143e00005030384443c03c1d03540c0341d040760002c3d512881c1084154541001d51500409040c10300300060b0403054008564002c660240d00b090101c90b2040030b40310242541140c03250015042500c1d12251a9080200424800e1003a6000c0b0f10800400301e040e480c003c421256118402e859400300c3d400820b07420b4003d071059a021610180d0f0700d080000c04164001e940c01c1c840c000560145944a0604507918400a400c082140c000c1c402c1b0400c11514500000d1b408003960101da01841084202e454580d00d00f1109800c09412040607468100701c3d01e81148140e03007580c82c00c0e02910465424 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 84809731 1250 84808481 84808511
    0x20a0902030f04030f020c030618010c0e030304300f0308090d120c051c020a0f030b06090402030c0f04060e040b060702010c0b0a150b03010f0e09060423190303 70
    0x20a40c0c2c001c0d0081c02480210340020b0250701c3c01500203204d80161079100400707000007818001c04451085146004007080c13070815800b8800c01c1c10541144c14800c1140d0701840100c0c0d03903070180780194180c01480e00601c2403013025891503c1d010036181044611031030454035203568031411101e4101d000c0740242003c6911400003290540b89854240e607500416400003207840b001d0042d50f40142d05002d001c00060408000300c21150001284011380541e0707440a50800409800c010003c2808040c6080c010840c03a0f9038200480b002c05100f20303000b507203984410610300d5182c41503031410f0003201400540060781d2070700056182c035145800c48040250000003814408a407181250003800034040c0d4503801c00041050021030b40104143d07500080001104403080c103e04d1a50700300807103042011004100c54200500e429008e040c000c00140075608110b00010303030302d60f00a003008122103042d5501c58403619801e4480d1880c50401c400711418030f030348180d01611002d0040c40503000207045c144c0742054290 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 84810981 1250 84809731 84809737
    0x7030204111204080307120903020a030f09050105030a24080c0a0e0f0403080c0c01020a080f0702070b0d020703020c040507030c110f07051e0d0c170111040506090f0604060903020a0902 81
    0x907100b030b0b801005584a941e41e04540c4d0008005000b8854400030315800103036503125401100b8031036002041014410305000d05240c0c1e00521702001c0010004040c026030340c5c0708040e07a0300314250140c007040720880c400a0704407a42e82040072401914400c480011071100001e03038801c2550b0195034409106464080d810003e0200f01d607070100004811300480c2c00244610000b56001041d40c81131401c10780452030190076640080c011100242c0c040c41809026003108040d503130090220300040108900d42513000129019102c8080c203415800301c0c1c0d4809041c0240010300c4126002441040203250a04014000340010a402000a85c0b201d01c42182c240e0000303000160023514200805105180c0300420480040c2c580c61459004030302c40141c2420f848141408041c24071400c5154107135030400d0710540b60b00145111000160b0305041401d00302000000c11a030540390156a920359542c0303410007180710744c03c9070003601d504000005000100b4aa220b080703c41503a108039409801103a940340410140c0c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 84812231 1250 84810981 84810997
    0x180803130905151503040501150b0d05090105040b040b0c07050a0b09100c020c100e03010507080103050607020a0b0613240f081209040902211c031503062007050703020411 75
    0x10b200306a0045136444000165501610440021800240380344020030300898a6005400704100441c104c0c004d10941d015850740700740010003c00035441c01e0b40355112081b90240000d094440c0003030100303508a116200300c030111500401256038240040c03404004e025422540c0d800e80d8047c0c10714450b80501a0f018030f5000c820290f0082c01c4040345042001003058549503168184a08018503c015490a00401c2c0c441c1030561542402585141090390900b140203003100115044004c4040000e80c0c3c0780d540b03039084001038685400c0d0f903041d450315a008089440075400030b403040c1e4070380c1c84c04010000c0100082d20000704850091560b0b40b48a603645958138001d250213603506000140340c508040e40141c541da800100a008030020903251082c0000c401c0f07000c4409038220046000720841800d00e0203010720104d290400a94100c0c0100c0e110218481c000140503503280c0c0001c106248034000d8850311102c4640e0429941c82e00c0b8940180d8900345488100d00440c01c0c840588486544082501c01031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 84813481 1250 84812231 84812239
    0x1802010816080c03060d05010603120206060a0b040902071505091b01030905030306060f12040503131203051e0d0c02070e0a1b0c03031104120b0c041518080313090515 73
    0x103030b10f500045001c81d070001009641c00c49401c84604e80440d42c00d000302c1005500034483e110402c0e644000003802d05200030142c074003580340301e0403c008a034200802c880803612041401a19000145807000c090f50203803030603140e12402d050500511580c0481c0b040000d1221241c98414120844010350a03551248000f6000c1c0d0400e10020b280d500309100140056003040040300d00d84801180c540384c0c0c4a00984050f2095400030502e00300541c89a07242a010b000085000e40500e0b2855034001c1040c41091031705a10201c160500d40b00b54403880c410390b08000e51200c0103008050050b00d000f0359810f814031072403281d07001c2c8101203901c1c0341d110721a144200e0100c0480140c0715010040c01d8440401c41c040c11010551b8881d4003418100c0e40c54007400241ca402d02c0c1680000a8030b040c1541014000362055100d00b000b0041080142003051101500e0308450501e44203110014540400751003071548042c11030302000410095a16400c03828030195030594038100030a88541d040005c40e040310801007a00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 84814731 1250 84813481 84813497
    0x10b0f01051602060409140a0b0102031e091201061805160c29160e030c13090c0509040305070209090d051611040c030e0127140307061802010816 64
    0xb82031910240da65810b00140807989429a03c02182c0b0407a90202000f03e101c800d01c0007445400d003460b014501ca2404244029820a81e65480342a10802c001c0341d0456018000600d540f80d5807103101c50182c110210030000c10045a48032404c098441080c1c4031703c45541d142030005134524100f030780704004140303180e614001c050030203a45401310f8802c21401c402c10b8038a10041101414681d500c803921400d1041c1100c0000f0210b018003802a212809400d40300740c104d08100032642d200c903c4440b44841d90590007150002990070b11980d03101c070581006401000e0380b01003009054102c0002e096207442600c0c049525955140001d032117699924284002030000c00145035030a020180c01d51283d80121020302d010900e80c0b0008046441c00084c14012070346601100c011102d00b031182050300702204901284050305040780890b0303100e49140080c1903005800820204500420946907d40c0d40940108441e592400b000c58441c0001074040b0f000489640004203280440103104519540e1511440d01e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 84815981 1250 84814731 84814747
    0x305030a080402060f0a0201140112170a0c0506040b0f06060310301202012019031b0903060b010f020303070f020c060d0f0609050103020d1103010f0203090f010b0f0105 74
    0x41c0524001d40107a0303010809010210840301040004c100c40802900005080020030030360f810346400c16484020380c09440305428010a641406600f003000d0344000b031507a54040e0510941e400102018080c1c01c5224030010001000600c26074035009000d040e200d4556550342c10208034891108840e9014200c1901c002000100c0c00342c4600c135650403c2e5011811103003203c0c2500082c00f0745680d03050b21801107540c025480590203100f40286e8862820b80f402c881c102071f80540700346e8403a0905c203150403540c4c800071242c15882076201001d001d011246072007400303070304550041081c0290300046c0e07000303403514640d2001980918164440000740340c01540c156601c021040d20240c081400c0d440941c019140269201d656041c01440622031050000030507450f0003002000316101030308003040792440e040c014405641c60b084903500860740001110400e40451001c00d001d06410103081c0d00e0b0342e00210603c4811500414000d02064800000b08a00d0b00100304106596208088903030104d0800c010140d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 84817231 1250 84815981 84815987
    0x1902011508070f0927031d060a0918090507080714040c1b020d050d200606010203030c071703010b0c160311060c010207120504060f0801050102121c1a0f04060305030a 73
    0xc0c58211034101c44680c0c0c9409680a0b030f038010200608070000b48045c60342c0702ca0107c0100b22200c1091041d902203040c0103c403440175105280601034003008240801c1203480c0c592994200c41c098541c0701041ea50f116986004040c0da40041c1e000f000001c08410006203441e041c1032051007090061640e440c0e6440c0c154040031503084540070410b981101440c503079200490f4003005260403841d140d55034250094220068802d410b015000c2d400169003050090040a81c0d0000680b5000320510350320996a602d1131601d20b5007420000c0000254031400b00001981c002980c5c0501903021143c4140c400303012004502c040a24a2030100802c051041d850601c1e913414100050010182c44000061400c40d090315a2041d110390403545400240d00090240005a8003102d804200651400e1044540d41458000f0303480d80c1610f42081000d51010503000f000103810b83c0400340c0e00314030220401519683c5803094500c0301c0c42c5042c00707028000c0540700281c01d040c24822030301120380007000307507090460b94034040b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 84818481 1250 84817231 84817241
    0x10203070e01030b030a0501110310080a020904032f03070b01081606030c0306090204034209020418030809060c0a1e05040b030c04030605010b2109031902011508070f09 74
    0x20705e80510684042200040b400d100d04442c180762007202c03035100e20f450ba03a2a84580d005401c400c032560000890b010058948602c080d03041589402c0006a602512103030307807044261030001d9400c9410b11480c01d25102c9010004001507402004151040e070b0321103e041e075460140407041c0c010403209003003c221162095000d1500c1c00f10501d8086051566000924241d820903081615890f08500405071016612002c501c41078040c40d90802c21840030561010b40480c1d07441811418a4031002c8040c219a66030307001b0389040700140c2d0005156201c40c01d00400c000b10403201d1035464407500001c500100c2c088026203080180d965544540791050b840940080b41110214105010090101060440264000d035104041318860b0686461031070508909851041e4000302200c1010490700d524200c02e24980c1188402407204950591100c0726000c2ca944603c590b900c117002d0400100303038a1607606410294061420101c6140c42940328070318692510030078462a1082c0d50500001c129100c010b4103c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 84819731 1250 84818481 84818501
    0x50a1202030408010e010509010b0a0810020304080d09080a03050f100303050705010b09240405010e010509071110090302010b0a06050a11030d1104050102150c0d09050115030605061002010203070e0103 88
    0x580e4141652201a04d0948480c1c591516499440da800c00a0310a824824000c00d10001c8407203500303451920403601d44448020512803480c540010000c1c05008224084403000d03180c100e1300300101492810201542e80000c03c01100217400e0101084180250300401ca025450428107240000d24680e001c3d00c503580b080c0320480c1c10355259031421840e65107481d08076204082100c01039038807000c1d0100158009040c951003e21462910006000b0240c2980384107040d1042601d204041c0d1301c4000040e190900094249030551040480502a405064104042241c4640c009100f982810010002100041d0103410f0014909000f45509144282510161028148113482c80c25685591110030364106241d00e0724840c000140800255904000141410401c1c2803002030b103062204904900344200815a0030064a0307410300b0050160a500405d08421150a01c000c605d03030703d00d0502c01034034044542034420601d001c5c65524860060007181d125560316540d84501da888200198020002512 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 84820981 1250 84819731 84819733
    0x90415090c091b0207060207061e030e010f0b040b0402030c09060307091d0414010e2a090114210c091b0d0506030f010207050705091b0a05040e0f04050a1202 69
    0x1000111684540318241071420741d4215060f50003821000039142c045668002021540108001c1000030341c003400341d0040341c9403104000c1c80d140d01c9481c11000752617110800b184075440c03c00f610017002207590080741c901070242e03024001000c06108000c124001181c00100142e41000710440d2460268011070380304103103040803010f981d16120141c041d00141c245034000381c0d0300e00c42800709002247c459010000c0c0708100a0144005500d011038403040c0b9990009035201400505e8102c96401c80d100305070080c0041c1c4241030035a0364240c060000d003a9119181d02480404440e0603000380a02a6841641032100040c86400403a80034000340003002404121034104182a042000c0d1401004107600320f180c04002c82c160610504050801040c5004400c03c2c4c2c0c03040001800060003c201941111002c55000480350365451804043c88001c2817020704034a1300140141203143c02801400945001105458688da50000082c1e1010f0040c2c6000d0900e03880300b01c0c00000140b0a82400c2c1c03204100344 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 84822231 1250 84820981 84821003
    0x22106060408100f050f040816060204090c1e020303060a030b0705040e090109020909030910030f0b06160b0105012102090f03100b0f100f050705150112030e09041509 73
    0x3941410001a8086080a95200e40c144d50a552050103007540010800040c5805803d06036200d4201c1d218248000041501001d8084140522541038a001300540141840400c0980030001c1030415680c16124800d07030300c3e09109581a02c0001034901c80d14018104004560030b540b1029000e1100804040412004100118a0b005009030440c01400864004201c1003214410030560400c010f1504640342d00c140b01c0b1040c0c955544d12602c01020442c20300103842002408000082e2400000c407075008100000d001403e403c405c80514551030040a64804603621603004490b60480300c140d071016a25111040901036450794000c1400402c01081094480c030040040790900303044440d09411030ba80d400c41d00310903003440001c0d9180082d04840000d0082c46c5214050f1401010241101c03c1020101d407500400004100d02028020108010300d00c075a034400600e131082203ca1822000a6408009460141044a80349002e035030300c40030a410b0b01e22000c603000020011030710245d80d10034401d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 84823481 1250 84822231 84822239
    0x100606210e0106090501031101080603031b0c0d0302070807060f0f03020a020114090106150309081918080309040f14040803060103020706060f080c010c0b06100306030803070f02010b03010221060604 87
    0x2d03c0303618014001810301080c1d5602d94144400c1440510440ca814050003104100c0c0030303540030007158201407080000750006101e95414a107000e40c100d0481c2d41003040c04081c903060540000b000011034040b0412904980e40f0380c1c0f0b00f2a5075941c0754800c1000702d041020030080c624043d070090302c5514120f01c00026200600d14100b100e0364015180e00c00203035902d0b1070034000101c0003010f6206070021400c0500810301c20f5900c3c240c01e407044800291590b1452030b03000802911031a00c81c0305800755813807540c940341d844294642d240c2d031220701c40b64480e516102c4081c03140700c0c1e40c0c043c04600c0040c010000d01c01da500e903200c13200c0c0c80d4402004141019800c1000600141e41c0703114001c0584400c90741104035a013003000c1c00c0c1c84c040354454201d0600c40d003214401c2c00075a80642c01c41d07000c801a02c078441d4040100506402400c042c0d08000c1144001008005a4a6000030002c2480c40fa581c02849020350400501d0308030701c502c00000701c1811000700480302802d400c050a42e00208013030030251915950b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 84824731 1250 84823481 84823483
    0xd020d080a0f05070e12010204050d0b0403030204080307060501090c0e030a060e0c030708030309010609060312140d0207120807140909090709050c0d050c0a0f03050907030210020f100606210e 84
    0x201310786110100d240300400505030b05000c0c248052084459008620340fa040c900007440020000900500c1440c0030400182018030a40640c3c00801101040745d4031071503289004005000c00740030310080c0c02d26101c44410424450009410081d00c05800f50200740410307207450028103501c0c0c481440a200d1240310312080e0301c0420402d40104040d034090364483c14003070b100600356030345588144182420000d0034404a212600c1d0480088210309280c00c829188540c50b5200d03004603401c00510610104800d402e100c1541c03401044101182d1310281703e070380d0384081903549024011307ca0350060002e1040003118108041001d410400351404c403030505030303100116800c4c0c503000c0f01e0000c403203140860881c42440a50240c140c020300c4004041d81031008825000340440741d800100000c06882e0004540d1144040c0841c170060354001c2d07e034041c1015984030280d901c0e030358685d110009214803100c9200f005d0803445100b043d5501640e03140c404801001c0c55885030700c0c00a41c03003c0b5072541d034800c1d9640b03100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 84825981 1250 84824731 84824741
    0x105010312120e1c0806120d05070c09060f03020108070c23161d0a020703050a030c030209150a0e0d0b04020108091c030603020a08010509060705030901060b070f05010b030d020d080a0f 81
    0xc0030801008840c810001405c1340b5014001502a241d106060b1074a41c0012850303580c0c0d00400d10b825508c1e0341e06800c2030070300303003803a81d01403800d1500c2d128011884001500ca407d080d28000e884510302511000c000319000083d6010203060105089124a01c8020385900b810307100c03041d50704440b81d031822107840201800441c0e0211001107c0000301912420130b540315903030700103c0c2c65021428003410351000340c104d12540e81804200343c5d41c1e9042200042c002c2d41601d1812401905014425a00301e000030308642c03150704074038041140b1511619082c0f0309915030194941e0300a096407104d4449600549020b08060700013420f901a880d0b207003554840808101105542c03503980031480346c3c5180180003100b0755540152680703034188020440c410400013200f6420681610304250b0303a5640541483c01061303117030442000c03644000340c2c2c88240a05401c044c41294010802006842984007c150303442c0f15140d000c1c8003581003404c0c401d2004d03028001444d88030071321000100307001c031001007010100c40e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 84827231 1250 84825981 84826003
    0x8040206031e0f06031c02060c0d09050f010b012003040b0703021e07030b06090103110d020a0906031b080c010212070c150f0801080601050a09022d04170105010312120e 74
    0xe6050320800c1811700d020400440ca200302c0d0b11b8001c48244e000c00c002520307142e0050008546180000c6e003403550b055290700c003184158114041d50740a10480702c00c07502a00111400b00d0004110300c101481010001d0034951840d0101d20085180c14030305080c50f902d5170170011080c4c0640c045c0702412241400000714480341c001411000d040700f241185444014014090300003401201140014030000e9000038a0524030340c0c048401e1001c0002520004080c0c1209400003051079060140000070401781c5146d017200c1e4500d47d58000303080c980b200070041d130360700c03142040078010381c002d044003018034142000814925014000c803003604d41c1c40702c40e6580324010022450002030074150408550307075071040f0383d42e015100800c050034403545080d0004480c10594050035150030340c00100a214034001100c64041900c03852442d4150700c1c08086c02c0c5025411600c00c3c2c0812204403c0030311642203040c411141682d6200c004a001c030409180c04a4500344c244424800c03040d82c4c0d100c2c0c4404407504111901040c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 84828481 1250 84827231 84827251
    0x18060513021c0c060215010608040c05030d03151502030910030f140405011409071518060309020a0f0b07060e0a0203010e0c01020c01090e0402010804050709050403030c0e0f0108040206031e 83
    0x42d008a02d46404845070990100c0c045402c091111082c800b41268681d046640516002d80c0b142c0300d03410030800000c4180c0c02160f1502c1b604100300d08094040e008000d00154002a81d480c3c1d6a940180840d0b8546004900e00140c000304060b00b1540740c090120a0109001d140000e01588031005c001c08903031041844865149405042000f00402401158130715020b0341ca00302c40d282006188036556080350b00034450b58600c6103001403030151042e04c200c00a00840e620543e00701d652904007030024200c5107011b90280c0c0b0b00300d00111b0b003402d401030503008a8549403400741c54010691540c0000f8102c001462001e401a000030074051381e000d02a9030319103108a00903003801d112000001e0301d4030310040c0c07241d41800b080080401020401c8100130b9402a028284a400d60760395150980c100b119641101e50403925060510041c5035141c0d1001c1d000c02403541703032400c0800c10101080034207103004880600141160b0002070050500101464109850744032010042c00c4c8400c503c001500201c48540315 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 84829731 1250 84828481 84828529
    0x20106090f020c060601080702150f09070b0408030a05090402071416080a02010801090209030307170309120f0a120e010f0212060a030b150316060f11011806051302 72
    0x208100d68422004800d02503201145040c06001496440d144018121414480c42c1c80004540034000e00650345200350910606d082444c00c000c08000700071701503c1002462044080205007800390308101c0d0140c0d41d000006505040064070100c8413607202482d0150416005d004c0c2c50001030701c048800400418a5010b032403141d920007520300d2000c0040c2c1c015909584042c41007001350742c11101150646800c60383c050307a60102c40c00802d181d4403941000524200c0c0b810810403640300000003450282003100b0584121007140100122140074a103080c81114a0070021a5440c1c0c3c040d188101c5200200340012450740c802200181c211011007008410050b000218184521a80b1800036442801126114403050441d10381c0310000318004c01401003420034010052055800300035000350030840d010340306155526147c004103900903c01d2181c02044600084441c2c610060103101d44d18083e0b5829104c1d11a815140c0034094000a08228540c1c0080c80428001d0780312400741202c01d15010304d11706a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 84830981 1250 84829731 84829739
    0x80a02010507030213210b0103080301080c010e0109050f0307171e06011202061b01091a181207080d09050d020712030c08070201121a040c0203090a3003020106 70
    0x20075120028440700405204218000b94102d8160101d8142e520404c941d2981e8901c10300108102e0341c20000c0905200364500c000020010088019416648a80700b030724208901d020040d10488011110305002c924101700500076801c00d8940958426001011070703107403079654055140360b204001c1e04044160032a000c07461304023440140001035101c9000041001d90300d410b001c0d2080c111002c400034420440001c0e81d1180c60361410680040035401c500030000c180c02d52a01c1102800342c0003a20741c43c05004000100c1308500c0740e1001e104103920b00d026210000d0750780d85c1052181d0147c4012140c0071002d00c115800c2d29600d2040c24041846000240443e2200c000080e00e80003450340001c110403198500b000001e81c1c801c119500c85030340940d006403611098401a42c01020012070007281ca4500081c41c40107040b00c4503030181d196002c1e1402c00c01507241017001c81c2c41c0d01c201c1205503080141e00c141044140c10307080502003180a00c80200310550341d440c100480008140106400607919110240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 84832231 1250 84830981 84830983
    0x7060b1906090f081507020a0812040c08010e062805130501051f03060b010e0303030f0105040506010509030a020d02030f03070803091203040210030b040b04060e15010f1209030e040504080a02 84
    0x2e80540048100f0300d0102d480d04c3c0355035598010011116100620090108654038001c200765440103a2003400591209d000c03000008040d041102d050f24950344a1500152019041c4100302c01074201c00b0140003240d40c0d44021506400d0300484120802040140895840d0120f115071405403a402050026540d1541001030075104041c114000c00913000060108203100140c0300000c032940400080f90040300d03a40162081480c0c03444017a01400300204020000710100e80182c1600c1c0201d0703041003035403100b00045400c0d00400d82e880b40c1680c0542c00c0d00f030241c906070305242400c903c002e00b10307207500040400d0541982c00004084620344070100521031320101c00c4c000b40c101c9207200ca2215003145000c2d000100c0d00c40404190200789a5104501e0516440d81d80003050b0080c00a841070020694071400025594022941510740044407181c180c1740f9882071041c080c064503142d1b942000c100e0451076100080c002d120b0202d050101e80780c22000b442e02c40e4000c10703206074000c84a02e034072650000c03406 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 84833481 1250 84832231 84832247
    0x11180303040e1b130b0703020f0303060a0b0c0a08040602030705071410050d0b1f140306010c1707060516031404021f030204080f0106030c06090806040201030207060b1906 75
    0x16109820a00080c0960040a0b00b40d540c000c20100002d4001d400b10540f0401501c00c0701c0c02079202d4000f43c00041005400c40000b0180c0e54443c0d821108010103410a03ea140d0005544455000c10040c404000b55400c0301c000d8540d00440201303440e5650030b88e07074654010b035001e0f6025101503040481da81c0c040c8a818002140241842d0015221207802c500c0000c08014044080a0900c440461011002038150b4003100300444098000c0e0400818106c840a00035807040506000403640c0b8803880d182c10910096901070f06041c1c5401002c540303260748100c1604407480c084040d0303080c02d0104001080041c01094025091b2610340c0460520790007001b41a6032050341d450090f070f020700e0709010061f10343c0c41c1040a40701140303c04980f0342d040700d20200d019128cc1c0c2e01640350703072149100075008607006603c1803003140c2c403800c1c1e0b50501599448042c0c4650440b4030410b2101e400c10000500594007a40090065a00c1004001200d0341d510001844031105843c1a0100c210341000c28015503400940c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 84834731 1250 84833481 84833527
    0xb0c071212090e07090509091c020c10020f0a0303020702030a06050f01030b070309120513120b010f1a07020105180904050105060405180a0609111003151202010e010c0c0911 76
    0xc40c01e01841e111382c0180488000b481494010704102000955804042c005017400c0700f0284010b00845003001030007942c440070402154410600c501a10003160700010b4046400000d01001d85445006a00c050300203402850046c0d80501070100d0040014146110b0346206101800512240f9410760910348542c03500105801c0c00e052a203d040400b10f581215040b80925003840c1080c0d543c0b20a40214450385d4499100001c48500c20300030340308210103291014140c0c0d0780c441e11a40e0300c65458040e0000c5000c03000d04040c007604100031041c0954403900c0103110800327400c11000e0170311107000b0110b00e40d140f0460f015140ca0355030300b003404400e14142c0900c98100709801c0070411001c0005101e01d40b5034802c40c90007090155a801e807035003004295070107440015030090a1a035800c208520143c080c0910500c00c5040d41c00b0f542c00454480c220300840807440c0c0d0182e5424180584800064441e812441000d07202e003544d0190000e49814540074a034004c0040141c03140d10b980c0c0010b80c00c0741e80809041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 84835981 1250 84834731 84834749
    0x1e020408010c09030506060909010b1c02100924021e0a020907021f20030709030302010c18090506010e101821020d060f091202190308010b0c07121209 66
    0x24080000c05c0c00082c40d941c000104544980361f64642010352401442c11302042c90b00407030079a0151340b41d04004622014001d00940f41c002028050303403c1211041300b40d010320b08140c03400324503100004a511600031040545070040383d451082e43e002c0d5184041c03030102090425801118034000b1401e01c0712072150024001c0c0001d14064859118400844030106242c4030312a59400620302d56080c201594248000c44229181e641c0c11f008000030b0002620b80015009582050001401c1071b20402810200c0d41002030b1f00d411090070305555802900014000c181007020013820341080b5500c02964108002c001e842d0071518036a4000361002140d800e0f806800900018103950604000940140d6145075044801044507401450200700422803440342400481c60310228404001c0340f500d8030350002d580c54084901514019000e0b00d009080954024001001300c001085880050700c041d00400c02424240d03130005403103012000b001d4003043c034161603c00c1c1015610011542044142028000d086 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 84837231 1250 84835981 84835997
    0xb0a030e12031906050411090a0f050105070f11093904270e0a020a0b0304050a03030e0304052d010504080706050a030204031a01090c0306030b06131e020408010c 71
    0x5105100c60000801c52801c6540f040c0c41003400091681c0900040c0c00e0044c000c1100e212920000403503034000f401000e0040c5440f0300c012400614001c60041164416500e10780750400f15901e1044442990108480b00c002000c01c50783c2039990029502e200d03000e51500200500468000480078410510f81252070b848550713660341e911003651040700c5c20355000d05500384c0ca042a0041034903080c0c4c0f0a0f018018940c0c80c1c0350072080c840b58080b41d20501907008481103502d580c1c031015210014882034400400079889490741c40d0000b4004d802411402030b160f000c0e68149660b4002140b041c02e1260582c90f24581b1028408141c1c07181403910700f141201c20300c0c2090400c1d0070401c81d169682028040e0106100010405c500c040c6c0c801c0d0125405564005c20b5500c520101c680c010b0001c04081c0901e07030225082080944800748688998000c407074000380e002d28961100c4052240c05071503c01503000952300d400700ea01d00d041d12600a046169140b500050743d951038080c600382110a82d0006030b003001440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 84838481 1250 84837231 84837253
    0x12030c1015032307050a0b090301051e0a0b0a120308040b0c070b0114150c06090c010302160602090402250b0a06030305030117100501090204140a030804150c06060b0a030e 75
    0x10043c60034000740e24401060320340410604562078007116502c0158032200c0180c01240c0340318910701600301e00034250001c0c803154840d12403da4441d503800702900c416551500004014050079080881484000b40c020340c102e90715203400c0c1001400f200419000b2580c580d040c402008010782242e40d2000031000e590341412070507642c28203003203c10b200c2d80480060001e0301070013980c0da155541e480100b021800c241e5506141d5815900e0b1202126031005a0048030384901142d40240211941080d108010201103c0507985410080d040071403019006a0309000e0120b0200a40c200408005181510350b550b10086241140100c400204034072101c03401c1c9881040000d1700401560705541200d030144104001140ca02481c000391034980c81c42c00c60500000180d0f4800c1c550092080d100c543e03440da800128a1014020b44100e2444000c0003900d040104000d116011002c0350100e055a1600941400060701d0340801c0c2c4e03045410207203100000050001170103801d813084210316800f882c05031070445d200e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 84839731 1250 84838481 84838493
    0x1b01020c030720060a0f0e01020703080910090315020712050a090311010c1a0601030606031407030221040b071b1101050c07080609030712090f030f0212030c101503 72
    0xc064000b0400341c0c00001000143d00c414108001c4074101410f11921034031945401020b0780b082a03c1c0b00041610050700d00d00d02e5102042c0e900540342c01141142c80d000300c52041c01100e149005410042028018001c4005a04056203403080020b4000141e1134801b43d090110044000c0b000a90500c40100003645015410011000c1113940140060604148090042c2c8120041e0300c00102803107540204a9419801383e028940601c100b80c0c0c2c02c21404e5102c0c242601210705208034450801c004400241480b44240c0042403088040c01c142c0c039020b01c1074a00043c24010580c0c0031210b00700c149041041d05a4406d5135030000ea00c0c0c40e00c2ea00c5942481c1d0320703444102285600e81504001c1d0000359100c0c5c00d482001030701c0042010004135080c030b00c0c01c0e00340d041c1c036a001814112171283c3d0300300e41c1d454460f206020724030945946800030841c45185a5807051161801c04040342c000088118042d90003c040c00904081d80707004010301110045900003c0c11100811170fa1511914120000e1000c039078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 84840981 1250 84839731 84839737
    0x120c0a080103081602040507030609110703021c030e031602040b01090506030a05180a060603050c03071a030403020a060507080a0605120a1e020406081606051602190b0d021b01020c03 80
    0x180040445913501da2030390180f0340c90f92460034083c0d086802e02c8184807005901d0744c005411141075040c10020400c02142110407803292090150041e072001031000c0301a210610401100951401c0008011030810f00483c11900290300440b922205c59101d0741c04c0d401c0c14010810022400d00e4603014950805001032032600002d0658606a542c41000070803000043e0500010400000304441c0c0b604010b140900161281d400115458004c490b480112424000303018030982d800c07084604421802110350005541004006500310b128110030100030032228800c2d5401200540d0340e070311581c50100411000e80d00705906c00c9018160108000081d0000480d0012000d90b1010050900c108032241d0a0340e80309800c4000ba50051a010740003c2c14903001038242e0040c1203603001c3d0140c89940f40000e0740c05000d08480c98403c0041004036034014a004e4528a600c4060010706081031a00c0348480c15a540044400c10701050f0300054030031010700641c2105160314100ea000398030f450303040b00c140d0307880380 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 84842231 1250 84840981 84840983
    0xa02100e030a06060b130803070c1710020a050c0606030f0709020a090305060106171503070302060c0109060614030c030c130b06070605070c0308070f0f080a0e0102040803120c0a080103 81
    0x4400104400c80d181c1e030a00c145014660400c1091000c0c0751520201469540098000c00b0203c84140c80007580481c084180c0d0420340d049010301c071115107020848505049040141a0356005d2540003000d42405440070304900b204031341e5141c4d141c41c01c0360003151078504050100d41c444d40c0080f9802e601206c0001c0d1036400d6a500000140e00d4a0110406a44140d681d41000340030340156000481c550707074000544190810f44641111050325903114403551401c082003c0c0b9050342140005002508001c0c3c01825100b0848000040417211501d625003103988a402c6803c1c0071905044008a83c84c1c01c00003880500c4d001c50142c40c0c9058504005907034036800080c4042c480703494030000f004694458083c0c0c0c5406410181c28000c3c1c1c61300600007402d80b80340352421408907642a0100719141e22070341c00310840c184941c56040c1c05144100c0c0c1960f50f210010883d101640c0c9a20840c58000d100380003400003405000021034954003541d258020021004003010131740403052060852180e4060085811a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 84843481 1250 84842231 84842237
    0x5060c0a0306050a0b1305120318060705030705010e07050a140405060307030203030a09180519090c0f0f050307080303060a030602070501060b040b18030102090f011d032a01020a0210 80
    0x3a000441055000e00800e60180b0750108490300c00094020100c0f00801d2500381c00d0f1401400d0030784810400c81e0284050380001c890380d10901c44001321160b0070301220014000101050b040200d55900c107855640104011500d6944803e22040c05040420052006e0481121854401404c00e040140e401002e0240c0e81c2c1b00780d460701c000c16071a4406102d008059038000e0152030b81d90720b410801801040180c0301d219400c5c980190014110046442030900845c940600001080c00c42002c24018000d200f005584401002ea00001d20805050700d50340145942c403403180c030340d030302c0c100c20541402d09503071128074070790420000c010b6942d482a840c01c4c16294014030050b12403890381080e50040415130491940c0c400c0000d40498a1801d030340c064101a181c0d00000424207103036a0905090380074010b1065040071410803500c0a942c05509c0d640c90b180b645640e01e05408045000107460085606480344030ba050301400c00c0402240e407400b030b03981c282c0280005c01c007000641d8042007519096000c60820 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 84844731 1250 84843481 84843487
    0x10206060f010305180a030918090b010302240c0c031504020312031e0f043309060b0a0e040c080604050d050a0512070e0a0504050c0f03100324050f0405060c 69
    0x1460300031710380c0000301c908848103c2e0000c00c014540604000e00b1802520741546c0030500d0165a0031060240d2104142e00040040325a46580d0034400140708813082001e9480301c4250380300d0301042c20005048200c00103801081d0114a1005050404a20300920400e130350301d01c0100310150707c002480011842007840100d9403075446001001c100200d0081e07000a074881d41c010701c580c5c1c15040900360300030350040c000010502031450703030751003803a2083ca0503600740c5107803509103034503180e4a03401500230764000c1102090007800c4000180c0b21803c04c0e0001d61540c0d10403414482442030050510010300100b03001008a800c141e22080c2d5243d03840300f000000c2150006810401601c02c8040e80d0200d01c480c24940d869060600001d0720407540824554015060b1840010701880e0601401d1301504d4010303049454415102a41e042e030b40d0000b01042c0c00c40b2444c0c3c10003c0050f95144018901c2110302110302e06003500041e100701924005070810800040fa50188000f25902040954100545101d85a6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 84845981 1250 84844731 84844741
    0xf04030f03180e04020a0501020f0d050a030e060c1b031e030c04080115080f030406080615160b09010507030c050a080901060f030303062105070b09040207080705010b0f010206060f010305 82
    0x784015000050b048002d03102c60002405000740e60781e00c1e024030300c200d4030706000a45032030049a440c40390200d490420340c802048104482d000301c0c018450301501b45004508d02c03110503002843d045040d54034100380b540006e450401505c10304924010406680702131841e240b444041400300d01401c0200b141092400008200071404c400b0485001746400d100a101e4044040c0300050b283d982886000120301071202400d01801e4040708440c00d40751261282411510781c001809200460501100b1540c0f1080014000030f6181c003100c603070900d100d655903410516014152900b5110044c143c07005050034140d421202c2a0070105803814a07080c3c3c43d080005a885510850140400740c0c486981c3e0141240e000c8141a0f16401810546541404420018007140d503032040904c00c50401400c1350300020340a011080c0c15a004101c1108004c00141c100001602c80400d1580004070454031070f99614956041420221840c2c20b0324642400a444180742820205020945080d00036040503540c100040f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 84847231 1250 84845981 84845987
    0x30e040f09060b12190f140f060114090103020603042603090307061401050f090403090f06030c020f070e011502010915050103020108010b09030319021f0b01090b0f04030f03 76
    0x1403490140c0001d1209410500304100180401600b040c014860204940d18440c00080c89403806802100c550036070360313025112180316090360002250300d45030840c096400c10104000030011425040301510040d4580500c00d00154210010a8028080b0400400160307460b181980c0e4455041481d94222004120306085200f80700301400c01c090101105002c074468000003c0c00000e44142c0041000003000030903120007550911400342d00c0301c0b031050150ba10342040c500382a001440390500d5004241c40d0b49150400a05c150020400283d9415150503855030420010310500718032340c040c1c1140360509504038007039141409006a82d42c140c00c00413181c03c0c400d510040c07640d0340040c101c40c00d02070301f030620002601c020300c2b05138002458031001140c42c460701002c5404c440c10080081d4581540e6506100d0080201401e880c15806441800e084104080b110301100d0b0280d008000303100d1202c140003608919194000002d100014850802e09000000c101e03410380c0e41218241d0b400c070160340b90403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 84848481 1250 84847231 84847241
    0x7030905070303030b0a091406040b0109030501050f0a06140d1101020c040204030602041511030307121d0604063e090d060902150a05090d03050d1103090607090e04030e04 75
    0xd0a5104446002051507816802032003100380c02c98503100141c2d030390600e080645107050b6176940301c20700304808201c0d6890b240d4082d095400040c1407114000f42d5944829003100c0c1c0807222041c03040114010007540340a0b520a682c00f41c859003680740304c0d00c4900c6004ca801c406031808010030f410b441010074525a0700800c00d07091041d800030b00540d640ea07181c1c60004040d4205100d2001d035000d1a8080c2e084c280d001306084440210ba1900031419503035800340441e01c075854034801250b15a036900000d540361005404807034900d0300340d100425031790500d1316250007251000801d141182020b9078402c590621041e0030341040715400610a01c07410f40703c0d9a0503119100380001942e10950207040d940402000d60000c450b258000c403004401a20060f410f1405407080e464103200007401000041c000e440c00c014010a550b0003841c1c082d0070400c104c80c00000301c400080f02828507620210400c81480000c0224551142c080d01d86840b00724a07021650b56245e40c0940b0007402c1c094051100020f43d241c1c0e0b880303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 84849731 1250 84848481 84848483
    0x2130609020d1b1412061504031103061005130f0e0105092401030804030f170f0417030708030408220b0703080a05060a05010e0f04060303020105070f02010c17070309 73
    0x30071503484012030002c0c0020a40c0105109040740c0482404450074055040c1900e50401118600d2400c0b0303401e04d4038410400e00524160f480b9400c01c0e95050403611440142c80910301c181310269102040704205498944000c2901644000394003041c4250b8492120b2200c10400d100000f00754030401040882c080d2000342801c2144d50320705410403841010000d80e43d00d50a2004842c00360000b81d003590205a07090900015111000400007000002c2c030312200880311902592105803c0c20400b0f903c08510f44c841c80401c1404a0049010702a400e07003104a6211070303101c0c01c0194074145007580c07660810300000b080038041c1c043c081404402080c81e02d0355103001403a0050029111034a84031030281d03a81041505500084601e40051040b5841303205450081000601421813149028011101e8204114001d90090074840c8005031648480c00f5140c091480303500041024900060000e011085145101085a041401030180b15402c1640720480d200080700c1c8400c2ca07650315506078003074180e41300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 84850981 1250 84849731 84849749
    0x40506071e03050301031b0803090d06180b06100503060d020d05070f06020102120105010206090c040b04021c0903030e060c04090b06040513060905010f05130207030905060301030b062b021306 84
    0x64001d08155120b40150b050342c3c498000b0500d1128044081103e1813400d001e900381030b034010014041e580c5000040c0b51b002170311660000c142441840304021903410348940458403644001c05208903460a100c91019680040c6412406e5281103000125014190003000c0c3c00b403a1085580401c0c0301040c08050b0281220740c60f8207200b84e60301c0d04024001d5100c1404544030100c000700200b055803010407100d0054040c9402031454680e14002c00c00140942800305d54025820001206a4421184138000907240b5000004190003107050180544d40d10040c20a40e0f07030003c5040240c49030340e14003590195000d41c0400191481d92002144492107a0b07003205a000c5240300c015452141c09030000000e580c0c1140d803c0c0542d0366034120000065006000d0540c2c041210b0f0145800466260701510065020707184c04540341d0303030b1100031802543c02030304240d0f044c8100c00700700155810101284030f42c440c207803000c15090701034020400082107a0203c0003032043ca001d400c41010261250041c1011b020920 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 84852231 1250 84850981 84851033
    0x90d0503040510020a030201060603060302060703030507030609090318050406060818010b09090102030417030105010f05090a03021009090507051201050f01140a180e1506070606031e031d0604050607 87
    0x3d201035a20002d1071001c6006608080010544510074020342045980c007a01c0d42c1d080c80016a030540181c08020005810590b4505c00080c00804500034001300340d0182d00d928803580018071074480d103c00b2541065010300d0402c1d01c100445580302d2081503214029070030700b0300040404104a4058040d40141d00c1c0c2c07280b101710070b0112068042d4001c5000301c1c42107014140c10b80c0782154010460009100c2c8901040d0750400c040e00c031074002d4000b030555540080465440c15240da000440041104481000040048406009034101071240a404c0035a80c14200e091085110003449035140500456001d008030244d8000517074094403045d1905820320802ea5292040c0500040c81c00c0d1079440300d8641070300450b00020f40c2d4944000704601502400d0842101405210309001c42580701da10200c130891b036540c0001020520800c1c1040d2100910261008101a1410000c00440398404e45101c42800c4101c43c0d40c26950f84021031f004c644003590001c0d114400e42c00c01c1a140750703032102c400321468022 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 84853481 1250 84852231 84852259
    0xd060b040b0414190b13050916030807110102031308060601090605090904020409050f0a0302011a18070e0103090807060c1103040e0705072a03030e0f06090d05030405 73
    0x154208100246080e54100558165a000c0009446126400d0b00481c407410001c959200b1043d0b40034240800a06404184034101001081d02d1620a41801d048a9502c4050000c000400c0c041c002920b004000a2003e4070309546a0012070b20498500505c0034181c0000414140d000307206417070303c8144503c003401405da510310080da00c540c01258054001134841001040450107a4155569410080c0c0315060076a1180d00380401400c8600c4180c4062046100300800107c1c10400e035035015202c0e030f0001c0b0f607403803112646c03091080f04841c05903c03c11480203140c41619481400300c2d8050042c1c41e007845050807080060b0020603c01401074545040000c00c0c2c42400384d260084000e8014669603012142001c0c0350194590190b80108880300a00d00c0104034001d101d8806082c00c240a4500300301c122081d654900c00412906040d8284c136106036008105154025090001c042000d690780f100d100721420020719648070311207200d8811034866419074203019082094501520010388100c15102c05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 84854731 1250 84853481 84853493
    0xa140307090303030606020102070b24031605010810060f1206050315010e0606120a090317071107080f070504090501020405060f03041104110d0207020f0a1e0b0a0522050d 75
    0x460100f58003290820100140d01ca01c1442200e5150350000708920f115180c480840b4900310f54070481c0e9a00c3c0856100485095400780405040ca050108001148071b18040014245200c014a426001600d50700308000082c1c10510a002e140110710b402201021100f10f40e41c001c280b00c3d00041e03098401c4000205003080440b81060680b810f070748401c0a0703a550074040229621940210074500c020141c041414540030386c01c6140d0300c80c07080c01c08800d036410908600a181e80d08841c002d00091441800189003d01400201d0140c0443d102400b14070004650700e80e40c484c01ca1085a01660307681029405110080d4107450141500400c01030340c412042503203c42c0d0741c02c207542c02da9075540310486c1030581d40703014814040400014240c450820345603119110003034000d000140c3c0c20019280b034028180d82d03154001d50103042c03801e601303030400b10a81142e83c1d00c008640c5c12500206100300043c0c0105900b140a48081064104240640c0c0084103401a28403c141c0d02c400c1e0040d01c50340230b61040201c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 84855981 1250 84854731 84854747
    0x1902090d17180a06020d08090102040b07082511010f140403060c200a08030606070507090e0d050c061302030f070f061e080106050c0c030604060b090112050c04020a140307 75
    0xe811010200750090b041000e94a014030403000035074004860308440078080c2900a5018403001c00060500c3e0f07954284415660045200321030240300040c0700402d41400c0211614189007011807910b100d0225614620b080070310341c401505001c680e42c0680b001600c00d100c40240c000240c0c5480e80c0b101d550b450103c020304000c4803070802141b240f001000c0c000e643d003c00b200c1422036010040c0b0702c1410a40300c95059600160207987c129004001c01004032b5000c00c0140c0041c44a281d00203886288002d0031030502e1401d4800400b001000c0028003659803000440b1a040101b80d284030481140e1480000c1c542400d02404104c0c0d800348d19000501c0d4220880400201c8090b5111000e001e88105200e0141841e0004444007040c03021005000e028803500142c03030b60751404401ca5910b401d05000007407404400b11400c075001521000e844101d030400000146c01894180414542c6020b00c0e6151a183c1000304007481c0a11f50114008c034819204140c28103520105950203617890030980310080000c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 84857231 1250 84855981 84855997
    0x21201090b04200903060906070f0e040209100c030207060c080912010912090e07030203090d0e0f030a05010603200108011208130b030403090806220602040324050f1902090d17 77
    0x4003906001031f240100103d881440f4020964855004000c1d1500070390340e015600d13408a80066091280707241c030b81c4031800c10840080554640405403c400d140091504a054010400f0085413103401d07000603901c40d064075414901240c520406201200e400b900603d42c1384405000b00d403c25003003440e950f400048000035104e01c10b00036400c550300c1c004250260310007614078584e0303540146075920425200b104e14011000e001410000c2c100d030311200117460701c07800241c107941595540d40100700f0841000b2007a2000c3c13200c074841110f41d0403480c002920705801440784e0155010001031020401403001d00700d60172400360005011100317403144c180c079200d03030001c44048012840075040031070780703403c00a4202d01c40c060868000f082015810029000303541c11410880c0c00b29024080440001c03500700052407420f000054985000300e00720f040d801550030240c241c002e0001000c089c4080d50842c20902001706242c2d0701c02603901c016020108500800707203207000c3c1c90100c60b0880800d00c130b40e041d80102041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 84858481 1250 84857231 84857233
    0x9010c0203030f0604051b04090608100b06120c072306090c21010f050a0209010906050a050703050906070510020a0914060304060c12020304080405040f021201090b04200903 76
    0x141da880c44207450900076180b1101c0000c08a01d002e410050b409000d2000340c180f00c02a00c0d040717180541080c0c001e60840c6840d1041804071800c100700c5510b9445040f0818001020300c440480c02c24480d0a06084402c00e1500000e0b54407548102104d00081e4440c0042692820354201c801a04107112051081400b40002181d401d05001400b800e4150000b80810070040d0f0000d00316101002000b2200120354070b5540012244405214603441484a608050380d2400a03100040c410410741e00311b0006d212052015052190b48401543c8007254181011590f039480e60b800a50756000d900700090003072240c2800c0300142c240d540c014058070840c9440300800c050700c0740039a40320070759100e00e0142c004400384005804500c282d00410050703911410301100c01c0c00c9000c8200c080c2da1080b10299902480001d040206e410720348240c0140c2503040c80c2c1141000110021028840810b00ca0000d4136034440c030000341c0c250b03196484074200782c0d02c0d8a601f051800c1d8600d800d03481030300301d480800e1007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 84859731 1250 84858481 84858491
    0xc0503070f120507051218030a0b16090803040501050d020702040207030215090c03150a18030810090e1e120a08010f1205031605070b1c060b0406051b0c0a0e0901 71
    0x940343c010001c2d2071540360322102800107003440c5107680d51150001c0c0c009810241d124a4940b42903202030061700020740c020210078207140340c41c66089100341001045503003004445002005210004401c2d038060315403d1074085d940c1e52000308400083d018400000e944284001000c0040540020b044080e40c8603159080700a42c1e07032070140c1a1200b011803540e036059045007500f8080b181c80040c80741d40c03080350f48200256202128041011901c40c1070340c2200800e040200b071004400160180b1300003000004401e010403450610303840d49580548911481c1c1000e07030840140406014001c0c0c00035003014001180e200c1c515960010840002881703100d05a244000000c21081c2e0503900d03030b40f40c940d00f220003135180c0404040c10300560007024006842500031602c01041c900c21a000612902c040c008805800780e408261520484946a00600c1c90480c1040100945a00401510b04025400301c1c16401482010300180c104a081e007240740e44581001d40c0801c07211a140f42c440c1c0a4000b000003001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 84860981 1250 84859731 84859763
    0x206040c06031107150203240d060506040f0504030903150203131101020f1903030b0609010507020603040c0308030115032a030207050f0706091508130602090303190201060512190803070c0503070f 86
    0x1540e074044ca2351308101103004080c00714121f03800c4690018009400040d500b00c0f0a0030041c00c41c6c1d8155811030000c2d0404c5000c0080c407100360f80944e65921003003030462840c10507042c0c00d80ca04891010040c15826240a884521ba0080c48001d00040b8400252844071241c40d87c0d203215501c130150200c01003864012680c00c1c078100b4100740d541c1c411040e100c451414a0359000c008042d0001401126030001110001c0000380808015600a0132038800d1104001940e54019055840d59203943c101c41e490f01003003031a65060032050540c0500ca0707007030040c0c3e83c0515040403420301c0d87c44c40c11707040d80388500f0200007038942c1e20030380300d00454858100c0901c100c0242c40d03088a4000741030300c00e40326007003038209003002065842d401881140c10013000c8030326140c5404107440341c41e91021079070030141c1d54900c000c011508081c500040248010000380c001800c903121a2250701d03000c0c0358080d02d010320100010f03071520b00031000076031069048001c0f60f4840d8510300d400100f02202440031500c100902800d00307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 84862231 1250 84860981 84861031
    0x6030b06030d03091211070b070b060405060d0b0c090a080604080307020f030310050411070516030b0a060803030f13080301030b1b040303020d180f1e060206040c06031107150203 78
    0x2000b2a40c40174607102807103001081200d89041c0710000d003ca0303004502e0001415a2400c00900343d0740d10682c805071840c94880d080204540f03005018a003e0100280305800041c0080d0559a0241805008645402c24040810b00d500c415401007030403882200103110500102201452203048103508a84142440b00c4900307440380400d56900c000008000004d00079440c0036040404401c44000c201070400d0100d48440b4036184c88180d60f0304070605004424828013001c40d0355154451160b4006108842c0b0308011141e40340b100500362610ba691010101c7d228a0180704003005403600300340740c29183d507141e042207502130302c040d07580c0455034150741c103a1001c4110b094140c0d130031280c050300035041640e10740005035030b01c0b6481900000e05004d1604082030740c1d0a000c1941d0041c1107140008080640861011004002180c10400641d401501000f0000d40d801d00e0740c0055644a14002c02c0b1007110001e84d4685009502005108069000b10b04141c4150b44d40a1803288a100070070b4945c01001c44998 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 84863481 1250 84862231 84862241
    0x30b060f0604060f080402030a1205070302010e070b04170a0501050c0319140402041a0616020f0a0e061c05060403270305060109020f19080105031506100c020303090406030b06030d03 80
    0x3200128110484c421880c0f40501410380e80240007601f81c8880b2485070303640d10100380c0c05031a00b07400300300e0100e104001d0503824820310300c0900d40d0400502d01541080000419801648100341640b908281070090f0884140050b0380c03070b150701c0310080c0200d003486a04008550030445400410440c041da56620400b00e6004490380d20f900070710000c04548998082c000038020521b0303441300001004101011503140c00c0000d0551000030302610600d55500e204100d002113400032043d20408004205002c0c00031218441600301740110b80032804820400003001070081110340250a90141e44108414981c0141c468060512841c0c0c0352011002c0610700c0300c080b04070714003001d02207070f0214006110010741a80100054812500e0700c0e4182700e00681500c528a11801c0342c40005030316040100107904007084a585002150000035155241c10310200380e400d114401c01d44104a40c20f41e00c102551014001c48500c684007600901c61a0748904110070440c1e800d40e0854001c4c0319140d03130360240503c28801d07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 84864731 1250 84863481 84863489
    0x8130308010608040f14060a150b0d09030908120d0b030316030815060408010c0206011215050a021210080606031603020d02060f04170601050a05030a2604030b060f0604 74
    0x1220341507400c0c02411652001c2c014412101144030140b01404107807040503031040400c00c00003c11a500c1c1c501d404100f40c41410100c0802082c00c400280640d2600c00213580e80400c1000d4000380108042c141100c6480c4d56031300c59100c81c01084600c071403400c1e4242c010114101400800c3c4558246407080c90307507174401d6061055004d44040007000c0001d205000882e0801510a0f00c90130042c031610000340329900c580e019043c240e40d03981e10255003503014003c0f0703801041c0340e0080da401c895480d100c0d11405000ca43c442c030f24a1f980c540000e2488603403139050352100581c50301ca42116203050414201d161009006110076486210001490361800007501c020044400c000300508510310b50030302885403961502283e02ca503003840764107124141d1130003802c01090044101e03107541903000130582c02c084041e0003050080c95880001d1009840000d0314209140d07110300381c0002c1c810140780003100d0320940d0700700860b40b03000002c000041c00920803146000715011500b81284036200401c025842c4150300c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 84865981 1250 84864731 84864737
    0x110906010e0d050309060a030f0e0f0a08070c0e040f05060115050f180405090601061404422102090904260304120e03060103110609030307020301050106030c081303 72
    0x101c0300c64035050030158001c0e42c912807422241030940e40740003d1070176081070740c0c001c00080c1c2d04c141014022400d80144500004400040c1c01f544201c00c07074050b04d44419040251200030006010020001900e080c0401007855440080301400d180c544010b0840c24010207844900c00c040000c42c0c0d059000901d02c040c16000e40343c0914000316550b0396005a0000c0c41b2400701480c10380b03586502a1030300e0180c01d1155403c1c030042d0844c0d606201018200c0b4403494541c0b0320351181403009112156814400d07c40c4544801d0306e1684c06000b0360403660b44a80d514140d800d80409041c00e0740c3c221b40c3c025410f21421b112030940044280d1194000a04900a0348251a80030b8403200104001c246000440441c2414071a00300c0040c02506c46010115030080d80c089408005000149c107240e9070190100003a502c081f4003911035949903484103416011111f20607031042000182c03092196604004072446d1640c00703402070206695030040500201404003901000c43e00d06000200720340d45442556032402d038952 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 84867231 1250 84865981 84865997
    0x709030302370303020d060905190203010506030402010e1f08100506030c070609080409091a060d0201080f19060f050a050d0b010603110403060f0501152309010212130311090601 78
    0x8450050725802202c058041c1a403c00886e0044402801240043c00c0704107c042184c0c14506841d07034045545502040d11944140014012a134850f4226900540c09180c4614100b0100f4005031242c1440c4000f90000c00f14040070024040e0410450b61003100d500080c0e508c140c2c0d440c0e05001051004880152103c0b034100a003000060b00365000e154028010b030b0800e4107160316500e020046441c500c20503a4000c100c00b5080c805030782520032407680100c0990f0100c00b81000c3d580007910600001e8002c0c00304800c0a070000c0c03051640fa0300c41d64940c01000c44188107031542c0c1c2008400d0b00c134941c010580603107900311020860341031401000c042e00d41e1003014400182e1810300210000c140c6120300f0117084504101c0040490310a00400c00c4681c0107507800a4107525183d03400d03400008a01000d0184400003034041e8641c1014400d400c000c0c003044050513621740030400100e040c40d0714842030920030714010035082d8440148800354415203110b17a42000c8880450000c20200d40801c0740c0c1e40d40001e2100c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 84868481 1250 84867231 84867313
    0x1514120f070e1002120a02030405090108030409050a14060405040501110a05091903050d03050601022e0c03200f0c06240102060c0a110a0206160605100b09090408040503060709030302 80
    0x21070081c9a2a1b5441c41640c0c1041d4444000074040754007a8480c5026a10204091000d00010b03c14990858441c1404015102c26180f2440c00031100612591242d82c1c0e070340000d002e00c502900072a01621100079521395461007402d0240140c3c0203a01c0080c0500307211f20300e0003c49a44a105a801d503900940200400400301b00c040b409807200400c120b046004008401018a115182400110140003e000c00d040d903080721040486030540320140c00c250400300540d40c580b445411030448642c0051550303a4401c114a0384030703907510417420201000e11901080010f070f0041d17180206050200e40c482400d1415240d401265103140c1602c2603901e100080006100443c041c221080d540040042519010340198000070655000300b030142d03050a261030012801c20000c1d2082d22341c8070140c0004940500d050604464582c0a0303140451b0040c0241f030040b600380030543c01a200180801012144580707403130480141b060507203100440140c0309840c540c21600c916001040d0f500c800310790441d0360380b10603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 84869731 1250 84868481 84868513
    0x71205061603090503040303110d03060b090f010e15030105120a020604061d0405160e0102070b0702040c18030302011e02030403020d081f140a060203041514120f070e1002 75
    0x8100c1d568145a80c8980e03c5002035014800350004500a071604101004011215410520300560744010580713854814060410820107990030200142c40c50745010380340c100184d80240d17808080e81c1c0c4c130145145200041d02c03285001035040c0e6605030f801c0c80807211151046035540010b0100254018010b110610066118200311400811452050840d10882c40b011404840c016200e814411018400e13512926402c248204402d038420310003800890f260900010300b41c0076107071000303118036141c10246c2c055621641c9004810400d541c1400031060f603916000c4d00034a42c24000c00c0b00c500da1009141c1d02c40301540700f601c2c4201c0d010780141c519031468800c01c0301c80d11401004242c1c1410760700a18600001c5502c0c041c0054410050340b82d0820481e5000c211325a801a44401c0c00c42d401044103103e16a0318070004c0c0050641c4c0c4c28928a817031409480e00b580b9000764010800d1401503802042140e00350340c0d0030301d070240c1d0b40f03915841000a1090f0500111400024440c00540d112184a62070528 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 84870981 1250 84869731 84869761
    0x20102071e0905060a0e04030306030507060f08041106071e02130603020d1203020f0c07050f0d0302070905061c0b06010809030a05041a0d05040305031b0406090603021e0d020c07120506 81
    0x94002e255185d40c1d52590420301050100f55001c1d40043c0e5148818401c1007420004038001d01900c0c1070003014000103640c004c0403000c0c010300082104420002e8041c080d1501c07020303564000c0d417000d83c032101d4030b008100a40c40c01510a2081c0e128615041204c1e40c8510039200d0782050b0780c2c001e043d4480d6000c0685a41054035244114807081550811150700c03c0c50100d0080d240d07044016001c1c03c0030074907150400c881d504007211081e114130713005954040000c0d00040d41800f01c0e40411004501c0ba0f1352040011004021500c040403035615554088040040d00384001d4440c0a003606c41402039160a20095583d02403403080300f010910800043c46030800c100d0b00c00f0142045a41c04500d007410b07101c481001c3c1e42007a01c0c124041180403061001c04029000030603140f81c08062000c0c146454002c0040904146109010500d81d0000e00001245d560464000f0610001c900c2c4540d540b4041c903520b4000d60000380c0300304003030141f00c1e00413031003240c4120072031103058105d401002da070b403100a2440352080d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 84872231 1250 84870981 84870991
    0x8030a180f080c1f150504050c03070c0f0804180e01060308030105010c02041b0e100e030703020907112e0204080304140612011e060c0506240402070f020102071e0905 73
    0x101c107251804a80c4c452409001d58504e9001c2000303c0d5242d000045111250000e4101902c15400e00082100c4041380c6010380e6800782c0b4071b1030040e00381c030381d2410600001e800601c0d010b0800c9a0000340030a031103c0000110b012420820800c01001e007076000141e080380c085000040840104000401ca0741d8070912010f00100e000034000190b1301540c1000781284503600310001e0220b030b9195000308091510704544030600001e400d00f8071030455440002621001d69000091040480001049100d40f280f1240381d1400340541c2181d140c048014002d951801088160707640e000035a01780f60a91041c58001d075401c44280c00b00650409060003800c6588002c100041608110705215aa0b2600c801721401030007005604000c000c41c01400821207042c41258200106001e81034507a1400a41c000842c680c0c13104007140400300c00d0f40078144155000b400d4040c80e55106001080341402e00520401440c6014400d0b004c4581d0166502c3c001f0a8180c501e030040a004607845c4010004140d4503044180d200b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 84873481 1250 84872231 84872233
    0x1f020a12030e0f071e030b070302070320010b09070f0516110303030f0618091905010b0a0b0c010615080a0c03110708031501050301050f0409050a0c0308030a180f080c 73
    0x4202240c0c9018a4400304403e030200e180d00c10b001c2007215000d180f0901212507542d030001c40070035055480e503410039080603202100b010303400901d40040c035124044589060080c541c0d8000a6180420254045c10300e10000318807440c00300c40803c0301c03e405182c4040154040340ca8079070a00760a00c00e00e08134404032103015511458440744d20280c0380d4080c401180b18003e805850551402d00500340300344000c42e440000f460700310080611030607010001d058414207a10100e111755081c50352800074050050810b641c1e42140106a01189003002c28020b8081c503400079000300403003603480f028188040e040107114000b298541c00410900f200d590007580418049040c04140521b92100c01e01d0350b130b0b2000005682c0341d072011050200e91001100c8204c1c4150382483c0803403c6504242c0042c02c0c502520180d18804ca42d1800040c04111003840511060b0744c00c80b1016074001e03030b40d0030408260344c0304503560454a854100f0440401750710130b161050007a00701c1030040214010b5915041d0720383c0800100811 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 84874731 1250 84873481 84873491
    0x70e010c02030f0d0801080106060c0809060702040f0e0309040b0a03120c06090803012c010e13020307050301021b2e0e0c0409050106080c01081b070206040b0304050102091f020a1203 80
    0x30424003000703135140a0300942c4d0b03001003039890190f542c2d08440a42e0804000c100b004105540480d4814007038651080341101d04594820251000600500000143e00c0310300341000045080948084080c00d0401d1f0142c40c140012180001080810b0b451030200610f080c07011040d9414981c8907407146451288202000070f01003032951600003141e04242c3c40a1000c26011220001c0c0300d514009940348070980c25556019941803860182e40543d00404c110101888258048150342d010000800184000390085543c3c5846090002c03098514205201507441500000e12410a80303400e1350081c108070710308103160340c204070841d50050701400341501c135035200b4203101c0000c80d030391403145000603440b85000182d002d1424a1a5051000148100f81440302190400c180c0403c41302480c4000003060344031a50381e00c203d1000442070300075034000221900000c410441040703015070003001c070714104071025801c2d0018460712441d41c10211002c0d0005800c01c001540000d0034800320440880391908002c03134 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 84875981 1250 84874731 84874753
    0xd1112160b040f020a0506034b011d07050702130209031603060c030b0a14010c0803240f030309040e1e010207060b01030b0604170718090515070e010c0203 68
    0x5200c1c0040d034050300c1e1102545605421480c0030190200140300a035034050071407815008550040e8061402070b40c10061800f0030000400c0c0e40b2142d14040c0035012650a8070708400e00c5c1d820004042401a008030900d401d02c00c4454204417500240301c0c0483d41e40b0036140c403103070b03600b84804419032190070302c00241c0074006698555018400c1c88054203072400401d80031465414144240d50301140360b0002d0502d044645141d50f243d50704001c0a44400d0f001c0c943c903400c41c105c01212800080d44000d44503190204c1804141201c10315418440eaa507000d51425800740c0d1010400c814100a2a05502d607100b004220340606064004401e88100002580c9a000042044610424203200c0140c2c040c0d5000030707210104030030343c031503a502181d0138030301005074844050100305640705500902841e03508514034000d003c501000910013800200018203c0c0c0d07507032810148007a1420246c111998011001d1358080742d00c142550714858402d941c3e5010000524030010b503803407811200705981501039059904 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 84877231 1250 84875981 84875993
    0x60601050c06070e061902030702131802091003060608060103050d030c080712090204050112061a100c060b0402040b0d0f0b0f13090b04030c0302070b0702030307200a0b09030d111216 80
    0x800d146c0354000d540e482c443c620400801c40b21041e211054a8a892229070b010002413401041d51903068414440c00c0d01c4150701d441104c60030b94001843c144c140f070004100143c0124a05048905c101d088403104814045c099007500c03000303800c200000710b2140018514922400030f0f8080060300140000b451000b131740126056600c00d8015010613400c2d06054810002070b44a81c18854000b001c141d4402d40700000000e0801102c0b154030700030403150000300380521000794025400120010411940c451340c601c07200708243c000400c0200f415241024104503030109014846051000074941c05c80042d1309410400e0940e01050f0403454199503002c80e800080880a405015034042c0d191084807005510300286003500b03d80003080f400205216032801618004242c40c08258000014100c60034030401c0b803100b080f2a99042940600203032000590114104001c1016000c164145d844002140d80180c60350680110440c1803640408015500080030502400341d14049110f030012614a9440302 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 84878481 1250 84877231 84877267
    0x30a0b03151005030a050703060b010522030201140a0f030c02030c010f0204031b0e04200931020a180b120102031e070f030506060d1d060601050c06070e06 68
    0x1e010444074140502000742401d110103030003054124028524000c05a0f101500c2e0840d170700c0014a12512407460900031382c0540d040d00c0344840064410031802c0c0740d05c80c00d07210040c02071000340c5c0441d0164409040040003841140c860410304e444000110003e0b8000310000d050404400e001c50005024080c1500802e0081c07101c030710700b82103000da11581942003818000015050801d40c60b1a542e0f810055a8490000700c0c2e801078024110150f001c5840c1010400d03000c40c000500d0740050f107242045005042440e04014000003003042400641413901d900b9001d004045010f50721400f5a0420841f104000c5c03641420745103501da02143c0c2521010108511041c1425614200e940100070481d40301d0340e91000c01540103050300f4002481c2000740e0302070514200300c2106010981c48500113189034403031100300c3d5407096076407104125854890181015511816644062900801011a04640c4108191142600058040d04a40d00c2d1320406844d11054248183c0e0040c1e41840300e040c900040b5100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 84879731 1250 84878481 84878503
    0x4120909111801020c0a0e1306020307020607020d030501050d080705030c0610060f050324010905060c0a0309050306010b03070807030f090b0105031006080303012c1602150108060a02030a0b03 84
    0xa40c94039118140102880418030b040410f0455200a6260709941e40e0a00d02c6000c80c3d400d4005400186c85041e060b0a80c0d200014020f800e450000060040d032542c00030700c00303215000e16803c2c1c0f4400300c2085002c8041d1002031264a510100c0c80070300402042c1030380001c00c1c40c42d20510850b80f400c0500c0a085003003c10485800e08181d2003c041008010b8220740e2000845005140661030340c904824031001141c0640744c00100c0505410201f062079020f84032010140c03000910707071a00c47c011400e01c107603600b08003a0200c001410601c00014036007000a0983c3c140d4031106091030640d552a0011203040ba0700400583c10161035110291000440b803261104c0e2138003440e9548499810141850f103003e4100d00200501860224100041c00d00802a00d055031080c2100e802a80381c0310b8400300e40700a14003802f45001d40480c0c144440024580300c5104100c1c655020355800100c039207580c00c0c214800348100080307900000c0c0080e00300e14030340d030040d81d118000003800104d21140320082840c103e0300841c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 84880981 1250 84879731 84879761
    0x311160803090d02030901050a050d02090d06020d0f0b030c040e12070b16020d020705040f02120108060105090123010813080a17101202060a03060308181c0b04120909 73
    0x7032190b4a54144100c0105801d1030008500d01504140000d02c14440c550503181040000300b101d070b0500340c15804035000c541c0018180381518510b4200380713000358400346c01e80c0e0240f45425240e032783d03410b580d0013408000c0600401821007010810148800b038452801c09480c40e000b0158142c02610240d0043c256241c010a10120245816080d8164070626403186070151341c080101c0380c00c5142d0004a900a58005030f030045410803010b11458041d00903840e2284000e0041d10000c0346840d800607130941250012200c20209984c0d42402003080c0c01d0460b204003110403100035003451035001d43c202940080e44840d01090500f540c0d01d40b145503801024888000a45000401c8540030608624580010082e100104a10700e490004444144a10f400034002c00d000309000304001e000703500c0f2000031074000c0c010b1562038201e1207091150040748540c3c1842600d070200ba1603c801860b5448410342d80d40a1015251a199034985071804003012b0185820401580c034041604000350280c0d068500581c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 84882231 1250 84880981 84880987
    0x3030b01020714091f050303070609020405060d150207170318060106020d0906080c04090204030503031f1508090c03030c07030506131110110a081c061503111608 71
    0x400242415210380c440c0598000c041c450a80340c1d80d03040721305500f00c4402d4010850408040c3c1d40c1e050030700200e0303000c268507010100c0c0310018400c158100d5480b4034400c941c204855a00e12301045458502c422010b400224512413201c14400994000c100c19401400c4004a4481012920005500407903116245a8200030f00c0a55044e003000401c0c090304950004d440040700b07001c40201001018403c000c2003141c2440490002c141312002c5034050300030440250764458030390501c550399500950351180300c0303240d180340c07103c00b81c0c600e0000b00155040d4603090356280d40d4091049680820261503182c15000d900d60b04040b07a034042009258003c080c0e0060000c032480c6040141c101180140491480a02e150300003000428a03102c0d520074500484030301c0100f0b0b50250003150008143d82c8004460f220340418041448943c0c4054140c20807211f0f245003c9800039a2088241d4400b807040c1801e1511440e07040c84c040740071750060450300680e952340c0c0381012240301d500000390854210546c0c14001c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 84883481 1250 84882231 84882251
    0x41511010c121a060f130b0703050c15010f05040f0b040603050d031d0d0c0f060f06050f01031e110f030f070f170411010903140d030b010306030b040b0901021201030303 74
    0x903000c1c00c43c0480344060301201401d040c9010480610801c1081001220300040310401000c1a05181c0080d099000c80503480303420707a16001e4050b501c0408498000e1080c41601945400140f540c24140c801c405400c0002a2030a41480090501900d10010071912445203080c0f030f440344d00c100340082d4003520060500d07003000c00c00541183c040141680d0001004058610b21890020300700c011001145810301030442c460611407400c20441c100100105d0a0990f0080d856403250414001d030780049603041203907001400107404413034444002103101001c842080e41d5100d00b03680a80c0d0a0a0064000c40c9014804c0f1008080e51740211001d01c2d9a090300ca041c1700034540d001811103400c000e01d003880c1c94611200fa1004485000c000d200416195059402202e9644a50681e20041d9030108258a0084110320b3341d80d1103252100c0d448001a24000e101c50b01c5601c2400b0312030842e80c0140404040d40c84603141c41c5140c2c1d00003400c6480941d02002484820082400030b42d000794003e80e40083e1196807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 84884731 1250 84883481 84883517
    0x15120f02040c02030708031302010509090406021207050a0c0b0903091302030f06270702120315090708070f0c0602071209030b0f04030e060901030e160e0c0f041511010c 74
    0xb1003030191085504c14000000050b00c180c0c00c0320740000c0810401ca029486920049919105503901c2542000075282880100b00d0150003600540e014103660408507079a954048505002d40e140002c00100140c2d25140424400d07000d0b190009009415a882c08000c90041603d8505035030704900d03079681c00000c00032285040707600217402200803070300c100351507103c11454201c0d500c44c60f110f08e500d41c3d01c40c0f000c1144103008100c1c0050740310b03076408182d40341c0c40c00103001c0411088840506014080150001301500e20500d4458880c2e051030710b03015a41790461100710b800c080c83e0401115015401c0100c0c001252201008042141850365000030080c00c40c0f03080c2c11121001380208400500d4001800700003904070b2a6000090000e48111381c50303040d90070048010f001260b4400c0d80a02078001100004540711401505a480008022400303849804045013184540110320000d1041030006101002d4001688035045000340307820120301c20b1123201ca508603451100000c002ca1a9803081c4100070300713 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 84885981 1250 84884731 84884741
    0xf03030c0a020c0301061a0a02190f110306060618060c0604050c1513030201080402011b12021b180603071505091c02010c0201030b0d080d0504030206010f03030903020415120f0204 79
    0x290003c0c00703c01c0c504180e01f40e030741c1103001c8031b419882c50100d0b10001d03585c401c01c018101c0c0c002e00f00a0b04904060350038032003c1c040c40750106450304210030100301c9582c06c0000303005026010107400346182c00c00521661031a900050303011035102004012940d81d144040118078000c5000341e018001c02c03141d080030044c1c0700c1d564000500c0b40d00b1090062080314201d8400c0d080480760217007800d07601503442c0e20048501e05054140e1003000105903c6500c180901d484c2c0c0102092090340131910300c1d000c00080c8c1ca00c0520081700a0f60700c501e80d00e05240014401c090710300d8100d90040e044541550b15025800c070840c4031282508005940820089411719100188400a107a280f021808081950b00024850006d0b6480a030615845141c04103040e220718503403d01080e002640c441e142c0c10001ca403903000c0d080940d015001071189070f0003c100d41e076102c03203580101d036450b4136180f14007865a070911000d00100d03107841060456244d00040e900d4005c4203051400c0380300c0c00c64a06081028410081290 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 84887231 1250 84885981 84886003
    0xd1a010e010f0b0a0e0f0607030804050706390209090c130515010f050d0c0e0f060301230a03022701060f0219060b040606050408060604140a0b01020f03030c0a02 71
    0x9051207804101c50140d10085450318044c17884d000d0180411400070606001840c0381041d000600051444213041d4001d0003540901c0c400d506594000381d40701400c441c14142204040c81c207044130301351001105200e08681d40804002d4107a140302164079000500e41407811904404a43c000002240051400408181410402103000c100c1c1d8200413000809039440c9546140c14801c00061030201c00d40560705a58440b0b82e911400e0102c002c0b4501c0040000a5180d6150f000b910782419954a6141c91070503a8140c51440044000c1c1ca072008443e083c00f4203006c20f451760840c02d00782001c005615150800c00a004006480420003448814070302c505420503030150003081000d01040e55015404901c588808002d640f8804451146013042c1008100e081d81007907005240150000b0103c2d00130020b0005c035025602512981e80d2180140015180141c00c03158601c0c2c0d40780d000075212141c3d640400c3c01382c58184101c40e5120440c0c411b040c9185d00c1074a542c0b119000110350f80341d25542c104060034481c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 84888481 1250 84887231 84887249
    0xd0305130c030f14030a09080f03120402090411090c0301051201060303080c07021908010501030201020d02030a0906050d0e010603060e0c03070810020c0f01021602040b0409021302090d1a010e01 85
    0x1010381d00c818800882a01009008003e1100c90000740841540400c96014824082d41d40c3c3d0321050303a001c0e1510f54140708158240c05501080c3c50054804000d840c41c00c016804a01055030760366080212003c0300410454120801d000300352070544070022080d10952410b81c0c415070342e504000401c001e07500d00b1000706989a041c030380c0234400203038807102c032513000340a81070031544070020340c40010840594102c1c40c0301003900d40000018160015081f60b81224000e8080d100d2980550004036264070560103220041000350b4010014180704034004c054040b0104030005d14400c6c02d90b20035003580c030703540d05c240c6005454403902d207a8420140590800148220001c2c22218030707204c61661900e00441403074410a50201d102d000c000070078025551000c0000000b1507841c980885480c50f0703800741d2074060303008600e004840e20003420184502046543c0080103034490740d606035000c00c00382d802480301c20740080c800000c540000740c0603000c1c144905005c6540e80c0003076050001e5a101080164011114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 84889731 1250 84888481 84888511
    0x60909050907090c050d1a0108070507050c210109060903031b120b040209120d0f080f1f1a03150402250615080109140f0d08040609140d0305 62
    0xa03030071000030040111a052900850041d200200a031a140103102e44054114108072150803441c00d5503c0c01c030318805090302e030802261a4a04115102e000b00c2c80c00800c154010040c89160380360907440f41c0b802d608151443c0651032203268800d070950300706600c115070042d00e0721640070802d5010b008100d4442106030203a1714031000c91400418900c041c0c50075503a240c3d50b80c6083e000d00e17299a0119001400d01800700b84041d0f0400640d2966441c800004074001510013619030101e9100ea40c3c8140518030307009400410703480307014100c202012105002091001913801c00030301980509289000400c3c52000e6a03161710380000302100410341c642c80c2511451040102c1c0b074890040d0707100c0349020407426040b03207681a05480c121008040001005071081d038643e1001809910541000c5035081c07161100d100030a00d141c000d9541c400380e14010b0030b26130304079140829010307124180050b032040c01900085251132440d101d80412202d0030000c0c0031140c10403808812130740d406004143c0c20100031807046031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 84890981 1250 84889731 84889741
    0xb0103020c1203040f0503030403020607031a0117190612060b04090308011829011b0506010501050a0201020d021801230706020702060c0f071e1206020f1b0706090905 73
    0x20700d4001c80598080c2c1140040040303024407140c81d50310303019942d02004803680c074103150401941d11302040320711a0009082c071401c41c0e54400f81480145501b81c040c0c46081001d00b180c1d610f074000c508005c0100e4003102962041c0710345000b81d401000b00905141548001a0b8043d040c0b600580c1d844080850117542041c9a4100095000240c1ca0444581201000c0c8000c8880c0c00c0f280900700b030aa01440c206103d80e81964030100c0d8841e00c11911300240c85140002007444c5c001542c241a004c0701400c0340d000302004002c954011002040c0010042c80014505010706003040201d0b00042c1c4e0000364021074100f510115600080502d80a2000e00c203200480c5802030051542403103000c070010813a03a00842c00d18119101c0c0c1055800c81c0401005680e0030b20a03a41c103641c2d031005680b00e00003c0c4210300940503070406280c80b021080c1c40c07500c0b480e041504666280c25001e0340c0080d5007140300e09401c00c030600b000004e04030841520b207107240207451f0b8203241c40da00034104102a04420000d520b4101802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 84892087 1106 84890981 84890983
    0x30108060f090c01080a050c070f080c161203211a2b06020328200a0509040b150706060e090f06040308100f14040b0103020c 55
    0x14207030b03440c4545641e036070b40c1403141c03a404507a0300c03404208250368642104d46c2c4100c100c5a8140f03050455592808034548030319041e54115000325040401500c103000c000344c3d05031078000020341c040c140728404d5001308e80703010001e0070b009848a11402c01058031fa51101d800c8a102c0c401c008c01207040c500d6202a0742080b032172034407800c83d40d0301c10310500c15036041c0b590454510000ba5012940c2c0c41d59100000d5002504012007040c214039100d07421281c54103500200420000040f9044e410506060042e01030302d61503003d0100b061060504060b48402a07400c007460840d40461090612070214150344294800d058101c0000030b408000e000240d040242290f41d240c403840903d03501c4ca81415140d2403580c1180410f60410b60101d40824420240d460300000041384048156540300030011295039030340d0094100e05c0700c443c50403c007403403c0e102e0395840304401e080035890043c22100311 = true := by decide +kernel

theorem cover : BRFrame.Cov 84712231 84892087 := by
  have h0 := BRFrame.cov_init 84712231
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84712231 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 84712231 ≤ n) (h2 : n < 84892087) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
