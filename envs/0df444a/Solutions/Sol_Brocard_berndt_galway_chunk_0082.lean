-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0082
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:44:19.797986+00:00
-- url     : https://prove2.me/submissions/8bb3579b-983a-4543-ae0e-c82fd8147653

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 14568352 ≤ n < 14748208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 14569602 1250 14568352 14568373
    0x30c04020313020901140907080a06030c090e0d02010c09060e010c08040803040f1d06040b1909020903011811010c030c050703030e010e010203281701090207050708030c030406140c01020c 82
    0x8104c0d10f024014101e80200012050400300d07243c2c81d0043c16040034015030400081200b0704681022020f55440400c0122030740d9035914050150902c0c2d503142c0c881d0700442010b0310140780305101341c0ca0014956629a454940b4080041d43c08a140714041810004031164204c00308000c1e070000c10003040300030000c59440389030644107100c9130801d070456030340e800c014401082c28a924402c400d800000484001070790365071070000114941e801c00110700c0c040549060010300051941d02a191210043e4020f2009100300b0402010215680a00030540c500541c0b10100755441084441010791090500c19072901e102d8441320b01e001d0055004070000307a500959602d141d40e110648241d601c00a000641c1021001400170000000007010b1108180441040142c2e0314401c1202d90308903d88018501c0c034a58540303481034041e41c8102c0095030f2601c1500d40000d0041c0c7c3c00402c5940c00400070015504042c01d00c90101c41030080255401c04c1d41100b0b01c000200c101c3d0030320050100f200d0542c02802210b03035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 14570852 1250 14569602 14569609
    0x7052209200d020307030605100f020705010504051807020708030d0603110d0b04060c02100f050609010803030c031602010605100305070e03030a090302040b0a120c06030f0506060405010e030c0402031302 89
    0x21115524444240315044907809070510301c156100b401d460400540c07a13550300311303044000780101e0b4016a84841c041701c042c500a500070241c0030009040e070342a02c42464484005494921551140580280c401c1c202040300f5403034141e0f0389400501c41d10580d0701c101d80e41c0070960324540203100d901406a6551108000b00003c1006d2400407040640e20008a00040e84882070f20840040005d400140c0b204c0640e01c80501c2403000c17244103c60614108422500030703d240c0c00406084890380e01903440030f0000b085e4100c00000360b81c802c0c01b1005081e0300d580c2d01c406455076500400842482990348890b000b0420b540c1e10b13200c041010755281c1e0005050310745208014a8901c61060f414001c4e00100603131906142d2001100058a0f015540850340c140a180440d40d050250381c02a0300d8482c10059860400181402c88401c5540070340e000d2120700f11801400702215403d644403a0f0150041008000f0b650240a104901c914006d00b52010700c000d82c0042410790340211244464000c03440c0003a8118603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 14572102 1250 14570852 14570861
    0x5030a030f050705040b070c03060501080307050106050609210a08030f06040f110d02070206040803030f040b070e030601050904020d06050f16110607030207050f0d020a0308161707052209 82
    0x1519070400340114180781801422a20443c001c42c1c5030444000740507414088608988401903a00c078604110640c0d5031554283c40380c102d95002c403500e5081c20b00002c3c140c0340074815602e0b100b00041400e403103500c141b15008403002002c0e400d040740d4043d0111800c046812a0042e40c40b810b00f240c1952550b00c0c044041000702d400300c2d075041d4111b40c50718521040648540c01544c81440f00c1c50b03801a621545400011141d006551107260705100c000f0400251321016014180110322460a0694507140e40e00142c848a4410b40342d00e8050b48030200411451505c00341498019001416500000b51280c5441e0160b40c8210350060340c0c2c0003c40280643e450782883c00415080103450903180207240000840d484442c060920410150080340c2c0302c0c1442801e00078019005241d008a900140c4815406503c07001c2444065000c5014400096180c4c040b07405c06800c0c840450392040d0383c0105000c21503880d05800703491001000300030721042015101c0707000d0020303003000000c2c0b40705030721031070305082a09a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 14573352 1250 14572102 14572121
    0x3050304060b030a0f060509010609090615060908120f07050102030403090e060a030507090c03020c06040303090606050906060910030b031b120c0d030e0102010f110d050a05010602030d05060a050d05030a03 90
    0x7070b0b10481504c8045180c08090180c000c0d4085804959511444031040c050084d58000555003407a06c0d001104020f2a41d01084502c0d1001d0490110036076034070001e90b102c6690340320b0301055822405035603622080b18402806107a940c400c416040110a498142c226001103608034082540c40c40140f14000200201c26801141141c1111100d070440d6039140e1a484c4d54030400c03122645071868036000038080c1e01520002240f0170112030b22403816042c01009000403050544110345040f80116040c10f0020302103201e10703000703000c0e039142440301c00c207101d170025013019000101170381e5524401d1190f80a1080a10044003a05d541c502000640104130001118800000c3d842c0d0090382040040d80300c0802080e09603400d400c00410200e1b40c800142c0c0036006072046110300030324061016900b65000c0c4090107106650507410441640d805c0109000c1b201c3c2802600e001da4020b1207038403d0b0219903004a6403040c400303030400044907900c03004518400c0c0291411103041d0004640e10760312035418491100403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 14574602 1250 14573352 14573359
    0x10e0303070914060403081207030605010e061207111c020f0703170a02030d0c0903050c0108040506150f0607030201020309060f010302090a02030a0b13020409060801060f050f010c050a03050304060b 87
    0x2141080c080140c4002c90a00c180042c5041c1605804600ea8034202954015030304410601c1e605c2c04403014441031241e00f1144400072a1138041c0204036035225070380013050607134007400081c41c10801e252005030304000103146004001d084541003d01c04000e0200e00ca040d181000d507480700b5082410040d044c00500440d0240550040c00c1c2000460300300d5120707180701702454404030b5417001c080a08a0441c82039200d01c40241d0309011101842e00da00100c0c40b000c50b070056065403803008a1400456400c4010746003d0419485107000c1102145603e140000da403100814861810000b60702003583c0d0781100c542940981d50102c20003c2000e8144441688a18121889221507045500240c1c0086000d020303203d4165011001908480d2030f070380306203120000101070341e1040c03140265410117035005006000d125400c2000c0010030210501500c002d44141110789025141000306101c3e5114005115a0422402015941c08100d061068802060281d40c40320343d00d281906003402034440d40d0060902 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 14575852 1250 14574602 14574607
    0x21c05070203070306051b030106091a031501030e0708070e0a2a0e01030b0306090a060e070f091a060307110c0603040210111c0503010f060206060604031209030807050f010e03 77
    0x10b80d80800c030034003581d03030102e00010541c45030580e0000500b091102a81c44039000000480d40b07640001c0b1400449240c4100e07a00507807020343d41d104043c042911495514207118031058003d41c081d030015840319089008480c5035581d90f0b0502450000981d00000543e03041109101d0503500b0f80c0225844180401d0200110301e10340000500c1250b8006410010041041080300007688030341c103c00c54805008044410318140048519240c44c91a007040781c0303551425404094041d0081843c82c00c840c03500814190b8030745002c4400300540310250100a40341c07426114000c050780d0300303030207940520b9076940c03001880d0324082c03c02c500e07054040300c4240c45004207008010069542a001d050f0754419460000c00010140510b14600101c03004850210402c609840580c11740c000007440c101c0d00b100ca00c1d83c4101b035940000b40c0c5c0b208801d0702c901b50031075010002440416411400b5580c0550940fa00e103064030341d130b03444980440e001044121880d8000403a1007465050034001e1913203260045000c2d52 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 14577102 1250 14575852 14575867
    0x20f2b200301020a0207230409080904050a0e0d0e060712020303010603060b0f0301051908060108010b18010f06110f01110405090a05070516030201060509070201020909010803040b03150301090f03021c05 89
    0x255240451f00ca1004152500b51040686080c01240341c4030003800070b0402e0008420030315041d05c880c0c00c0061002d009034604800110340314018040d103100340c000640589104480c06801b01d581d00181c1c440070b41c100004120150001740451b014801c03180b4103602850310f950410900400780d8142c0c0c0d009000320300e030a1203d000307199110b1044070b046400480307100140f42e902486041c002c00c03855000340054090100000b4001c601900304240c40401200c02405500ca10001c0740c02c107480a000340302051920b090184184d46c040d140306c6103d8101d410484400400382c0c00000e0a4503541307000d04600840c003180030051414221942c54000a09404c00e00581c40c2449008125001c6c1c84408062050703605400000c0c58001e521032405003a01501d0480c0600d00520302074042c2d80300710f40140c055041d0500001722001302109a4081d91352801c262480c50b258560701040100c1903011280c0d16541c0d40e034082c00011003901d030a9444611903005441c456602045410642241c100705409026007000490b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 14578352 1250 14577102 14577107
    0x10030c06020105010305030a08041103060a06050a0503030f0d020903030c0601030c0302090702012a050d09061b02060403050901050a1103030a0608071502150702010b09010803071707020f2b200301020a 88
    0x9445480c2d00d40360004040d952b03070400d03086220880701a90303011b0044d81d0a02a42d0b8000340c0101e41503520035942442d120307540d2028580d80f0320815076024a503080902c4000700403407040e0010600706030002c00b1a82841c0c810240b25042c08401c0c3d104031442501c0c641d04008500309030105a0f813002ca180002c10084c2c01c500101000060200300700703030f1081144005408002e0184091340d100c13140b4443c040041d12520300e0500020b101c14a099801c2c0312000018004243c03000640602c19540360343c03040d092100f03110054800c0d810101090043c401120800c444e0b12034104042c40c400c2500001c0810075903e07244955052240c00e8000d2810144c8001280d40c0c243d80000e40902b03508030071512110182d8528100f20300504400c800c6c1c44d400550440001290800003010301903850140100c3d1100b01a1100005817510414400a4116040c80c000c000385280c03a5140000148512003031100d11960315486e01542c090ba0081101e959648255601054815070402e5248420590085150004e0302c50007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 14579602 1250 14578352 14578357
    0x8010c05190806010201150b07110a030201120207020406030213050a0c02161214010518010605060301060806090703060905130b0606121603020405030106060305090c0a03020a140f030610030c0602010501030503 92
    0x2180c180042d000100d16103920035030241d0b5a203a400292480002c2d151260b44100b03a00406c02035a1102c10072400085d82d10704030100004407a816140d80c2c41c00e5200c10300070b401940142106030b80c065590800080980c5640c42240450000c1c1c500c001414640510840110b803105100c4504550100e10024081d04e0f040f40d008082e0b80700e4020300741c03604500d0b140c46864002840408410b035400d100c18020740020681d4001d650300d41041c003d00c8095190340600c810343c00244900000603222a02003005d03402d100c9004d82d006102840d002ca0381503154401c140035608261030045c41003c011601405224010709c2482d044802210715a01d49004002840981d000141c030072104091048240c1c40c180d80070b54100c80003080c0c054024407500355130b200041c00a0400700c3c0c03561a180159960000c0f1032030002d80c42c1c1d0540c0c1e40100200b4480d803c0c10341004405164013803094001c00101c01c42c4e001ca560400c40c0d14030075007050403402002410b40c074100000400582c04481968100b800501c0000c1d0003005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 14580852 1250 14579602 14579647
    0x30b04050a060f0909020f0a060e09010b0f0304060c23030105040c050c1510031401020a0e030a0f060e01060b030109090c060206090606010c02010512040506090c06070203070902030c04180608010c05 87
    0xc0404c45805d240002241d90203907202003544441d41620000d00c954100b80208a008030460b54103e260780e07120060b200c10b2090070705d070381540e8200700000340c0000c5480c0c0c410f2001d204a8501111a040c031030320728620400c07000b03003c11041c0b00301000420135850540100808060541b070300d5401e207079104159542c0ea01c20020001768403506440015984e09104a84800540d04001001d5004030500c05060003580040c1e01940010640340c00703404507040018441501e01d034040e8450900150310344440c801412045140382e0295200d203400901c01031358a01650280441c1c4000040702011440d1184405645d81e000034103540001c1d08000030988003040300b41c1d00034020300304400c4040c0c051004994a02c81c0962041c400c21859091106118000850750f1080440001301e407039200140d01001030724064840001d60562000e4014807010109401458200d90f070000060b0a0076100c600054005c0d444035210760300250340301d4082280304000d0184515003215401d0003403500d03c0400304403807020618030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 14582102 1250 14580852 14580869
    0xa03030e0d170f0c0d080c030a09060e012307090608010e0604090b0405060a06050105190e03030c150a0506010c0206070b07020f0313030201020f060708010509040501020d0c030b04050a060f 83
    0x7601c09024442140402800051466035036074000740b00110030769004024107400074424111030001081c001c5604500492040b440103003190380b0b600c04030b07015114010044034034640381e003458040c2c50403d000c0c24000c00d540302c10701c50b42c8101c0e030710003940001c100404034400c000320035208100043c7c019425505588c1400c18a030141d0f40d80300041805000f0b0381000601004047c810001804004510716001d03040d655000d00c41541c1d0390004541c035000b08071600e45405024030f5201d02041c0a0126803407444400307410742c0e08110070120f01d107091443d02035040e00100400d50800c50080200d206aa5000c002428035010050f49900892124001d10000829500f41d0002003510240204103100c1c401100788100ea68500440e80c0c0c000b141080740c8003c0b0b0140c40b503030103505c074042c03008540d0f0f6115500b40d80c1c960109078a0b180030494030702c0028205032515542000b154144040c0ca0103060071640d07040c4c17030100740c0200c1a07003031108840c00144140703030b580c0c604a402c2c000c0d850080303031420449041c0e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 14583352 1250 14582102 14582119
    0x71b050d030c0501020f0f04150206071d040e030309030304030810060c0206071a041202070b0f0909040312090503120c0702010c020f010504090207060b04050708041e03050f0310030606050a03030e 86
    0x1441c0c0f1a0081c031918542c0420f00c0d4002c6203c5c0910100c81000348180c07801c0790040c0030b144403c6030043e40d54200640b004000301e601c0600500815004468a000c40c683c024004140840541c0100303086500030348032560789400020401003415040403e0540004400a90180c2c5610300394008081c04180c80e0001d21600c0000390400074090851400220350064110b1141c007400c0a19040c484a2080107000c1e0241c000c42d240002d10220070810707210246491010f141c80d00710003404000600c48028400c0f018012040000d40c038402451299240040c450300080d80c7d1041c00106540040f00d00502008403a1810800500182d1340400704607000355051b241c3c0454400000c00580e114040d642040c0400c1d81f001c600c1c40244204c0780c01841d80f030303003095902b0040ca4503240c1c0c085584c0b0004460203403d520b0400a044c444840701c0f1000110a4003e26002d0b05005c100301d900c001a610641d0040c1c0540d000d44028001d000043c40307104010310003124683c60151440d64041d01e05c18808502c2c0e4400c0024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 14584602 1250 14583352 14583377
    0x601061205041119060207050301060308030c030402030106080f010f060e09030a031119020102070b0c030115050309030906040608060906100e0f0303130e041a0403080105040504020102010608060705071b050d03 92
    0x4660354580000c600611354540c54490a080030051507852240b440140305412002441d41410b1080c041070f640c00111540c0f46650744003030007010b40d00c013070301c01c0360150b6881500056009040c4802816074030120004110018203903030103400d503480381d0410301001c1000014403490311400000c03503008025508001c00c41d0940c00c0b40a1a480c002c2880300030b40600150600c2914560642c010216a031040311b030030400d0f481d80200801c0c0c0740024000c00c40f55140d04c082071000c4500400103140d000c40b440341100c3c5030008a00224005402c140c2c03250000c035030300c1c1c0b06001c141d10b071201c080c2da8490000d45003c2c5000000040c0140b140015223440c9000c2c1100306041013140d2005e00444070305282c848035039004c090f40c0341442d0412010485080d516052043c9516007441c0f08907180c64003950701641c900d00c159007042d00708070060030700ed882241135640c0c03080700080740b1105000207440388070583c4456441d46560f00748003001c0040f801c1003550b0443c45a005101566500300441d01040c0c1610341030051191 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 14585852 1250 14584602 14584613
    0x60501080c090418080415120504020d020d0c05040f05150d05070501110709110c070812030403050a05091e1e0a0b160602040b07060c110d030f1503050a0212060106120504 75
    0x102e0100151084400080c0828410081f003040f00c0700b02c0c495643d0304c13801c85848990342c049560603a0001d510124128a42003d4a000303011103103081d000d171801000d8203981390001411140805904a55142c03200d00704080004114100f030b010000588000070320180ca07594a030340360805401450b040c091401140c90b0402c000b000210081d00e0030550402220401c4140c00344240c02c02410340c1c0240c4501900851001400f0400e203121210b00988182543c1341ca59064815030407401b040d8081000510800107103541e0b4147d41501508005198503012595009218000d071031295403890010120150101549a90b202441225995001640c0310718059190301d18610a10002424150011070041400c038048002050490301c039583c100407240000300251544404c8504d001201d421450380c2580e5140030703402502012024941c0050800c2a1208100b18019517070400d54140e481b41c0c2001013103040411400d406103211030b00500456141c41c4008040c000c01d094580021034445c03010404122 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 14587102 1250 14585852 14585891
    0x120305151210090b012408010303030203130503071410090c03080d091a060108010603090302061b09030a06050a11130b070f0b010303020c01020106091109010c020604050405040b010306060501080c0904 88
    0x1030482100f88481c940300c1c100b0b0f40b0200c01c280500c4185401c4411898441049441113112002c4141c8070303001244e1075510141c0081d0401000e031554031a0a121036000210700303000038a0001c0c4140448030b0311102c1c54462600e00030281c07510110040c6880c1288001c01d0409241c0d80440303174880801a50750058407001c3c030241c81c482c44004c0000030740c480c2d02c400071700d07000844c40d100c2c51003a0f0b5100c0803607131303540c034103d064444407180907002d038009202003050340d110403150311344c0c00901a40c41481c0030035000c086803400000c200c0079500c00fa030f10720a000300016240900f4042140510495050800000c0c1d0050401414802c0826103500046c6607400c02c2030040d032504041c0c2d00426108040d40c1d4034140a521120564820341c019481d0980102e000c007105c0c802d12141140c1d043e40d0900f0131300c0e00e0005641c4100e034044280da01c07400a120000c0c859a980c02000c0c4180c5c840d0340e402c00d05500d580303801400c1d101a9004a414000401d040200040c010700645004d03580442e004107055a4402c00c404085 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 14588352 1250 14587102 14587123
    0x10030602031005150307020c01020a030e010804050c0a060504080106081204051e030106180c0903030905060c0304090c0c02100f02030f0d09060e01150f03020906090c0c0105131203051512 82
    0x2132041d605410301001020714421000ea40a5035540c2c4054030049880e181070040050207e42002241034a079480703421746a9000d8461404c0318001c0c0d4000b00000c141d400716520690000310700050500c4030135420301517440208200001071014003007800c00344006000394010306006006070b00211001d1980701d403050312504000b030000c00074140c842c406107103c1004540c248410500304400b8030161b91140550307400b00c9400d941c6031480d5508000400985900c4101070300003510062101142d020050700c2035044e61015034407422094445441400038001010700c850b0705000b001000482e000780c02104440c6901600041540c1c0c41c01c81034a800b008185907100545600d241c8220700880c03000541c041201c28420000005038665140341e02e910310b03e4070b03000082d0850070b414080b8000d4104000e20707580005446c1029410a0201100c2c036084035022075a400000c00000ca002050004103010012481030500d0140300902e0103a03008411450203641841c001c18400600b407618950600404c03425 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 14589602 1250 14588352 14588359
    0x602090102070902180f0111121602090129120f070302040806090c120304080a0605090102040806041101120506030307030c03030b130911010305130f050a0b0406020c010c020610030602031005 84
    0x5918022407003c03980301203d22030310302400c030300d00c046c040c150701400c1c0c8101c0351152a4001d1680300622544020302d600b003140e6440c1507106004240700180e9071490441d010703000c0210040e08986031000c65211440d4800c0110240303001c10804190040395122070103500011805d514450354503540380803002445168004e00340c82c09140305000003600e0120702c0302e102d98001c0351214002c44c0302d120016100d20641c0b0400400360b200740094400107001c1e1f00b25940c080d06907400142000c0da01c00180d814000201c80466044403140c24540e020340c0c0251650311212500d50b41046070345042d60100780d40388034104001e030620044501d22000c141c8250000700001c2006030005032140d04405110780a040d500004071104e54a0140c3c810180d4445d03c12244961202802d03042951031320f8903060030078215140e040d0359a000703003800c90010850701040d041c00785108440059440304602d00e81401c407845904500704542010086c00710b06507001c400c200a8a80007840140c0c0c0b070f140c0f502507400782ca066601c003541 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 14590852 1250 14589602 14589607
    0x70c03050607020d0207060c0609080c1e012307050306030a050d05090112020903030a050711090c0c0c030106030203030409021305100302070c06030207081c09021207080d080402030a0602090102070902 88
    0x800501040c464042e480540071502c00003040b910076a143c0c0440c0c000c4d038000800307203141140443c1542c0c00c481541d60280740303020b19020380c50310740e035003007009041100c0b034404c5141c44010f1011009110f100700c00c8201295145031480c00540301400420081c0202c0304108001c0003080c0a581d0600c0307811700e0190f100049035200110385001803caa003200c540b031804135940c1c0b541c1704880742e080d000f10381c000007000b006075180c41c03040340003502e00346c2028100f510340c0c03091440324845c00c1d02c561a489009185403000036441c0d441d280c034014a0503c1000d06a4000d9042200c10001620b0001c02d45003038680000016880b03210652581d4070504140e030005500042e0b0242407400c5542650040103098055920311008589400b41501a4030991000400b000010440240101c610490290112900700c20100704104c6c950000b840c44000844104640e030071889041080c1c80d001c0003000440d42407400d124403103180a0300069210070f04294090311598000031810201d038030901040000c0d24040c0c50854 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 14592102 1250 14590852 14590859
    0x906010f17070906270e0702031303060203040204180f060f0905010614010809070e060103180204020d0e010c0207030f08090a030c0303050403120305190b0a09020c010b0306060414040303050705070c 87
    0x3c3c01990140b00340c0f40032803c55100806000103454010588160884000316024500108581c3c41071000700024118001448880e4025a0721030303000c40118040e240140e04d9041030b00401080700c80e42c03d2240311206074503240000003030080604940c4290814000030741030a00d03448190140010f000300400c15480c0010116408040c4511140d00f01e40a0b40e807100c3c0d580c1c4100b0100c3c0d403849940103000c15030084500182c2c20350707c6504060441c15110b000398440c2002903010034140d03004040c2504000707840c1e031607044088109100341401c900051004114051854490f0640042c810101600c040d000040c80b4182e80c503060441c800944c1d000d8039400805a03030b424000d0003600075000440c3c90b40802c50300303003403c14403034000e541c05074100002015100c040d0030001c00c010044081d0280d0000100c0c540000e8101d1544054800700c40c0140001c03c00344801c02c10541040001425188128078004c40f0700e41d01c0c1c50f8181e403d50b12560604001a19031240b200036900c0e406800f40080c4000030007030010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 14593352 1250 14592102 14592107
    0x2307031508150901050601081303121425050406030b0f10020d0215060109060309051203090c1201090c0509070504150504050102010b03070509071b05030a03050108100b0906010f1707 80
    0x4110b0428040c241d580e003a210540f0281c261002075410900084011021980003410300783c02e00c401602c2414a551070040010b01c6009403000304c40b0380882100b11000f046840c0798941d0040e40c41200307985c03000785407980d0300902502c42e0240c3d010385010590754a61103501503d4a500290f005c2d00002c001400741c09202c60700035520324070b010750b80f8014060380c5076044240310307a5102d203401344405071035003046c00c0c1c2088400c41c01082114410b4900d8403481d01c1c41c1001d1204000118001e8502c400546102220002848600e015007403102c082a0701d007541e12008148215500026100c1c03c81340040940c60b828400c40d0381e401503403c228014503842c0214442150840001c0048034420b0700203100008081041544908030b501c01c058000854030b000602451140f20750390b018041030003a0401001050301c8585c9140c004071036600200c1d58400041c03020000030041071030840a81c060901c07075108040f000c03900004c005840d003418490760b096000a040e004d000d03204140180b6400e1a031280ca03085200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 14594602 1250 14593352 14593363
    0xb0a0e190606051908070302060a171501020706020613080a050d020a030b09010b070f08130806010b0310080a0507030b0a0b1305040b09030708030103020f01050403020a0902030610032307031508 85
    0x90511030340721464031a5113000c401d0f0f04030b0708071071084001d8141c00c0c0c80c603024028039071310403091682003081c0207840842e82c01100c0103150048101e00c00f540c24511000001a01c0e05006030800340540d400f171020011042500d0001c120340650011030340d503d0b080c10b4442551103015002d15881c02c94004160381300480d6160340080c0085000326010111660791b80c01c80c42c4684640c1d003026016040410a0901140d5500c00030f10341048105896103c15a4800c00390341415820b070000f0a48101c008180015030203d15035901c080c3c10406c008e06004402551082d40c3d0f549540300080103d44548001280e44e03815a02c80769000358054480231065a00745402c00082904a13001c4030a503800401081c40c00b44000b040c0c07030410b03500c0960145903034255001c00c22203207821059541041800c00c004401621000c101c140100942400941c03079082c480d0812804242c1507404008140c0b5010049810808004c0040036003001090441d6151f1a290402c40281403d162080054031004400003084c0800044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 14595852 1250 14594602 14594609
    0x1020403050304060e210c0f06040803040612150503030a1103090d050d1403060a0504020903010207020303070506041a0c071b08030a090504050105060f030106350103020f0d0b0a0e190606 82
    0x3c203440e08204a4080600107030642401e19201c1d1f000703c6081c2032504040c5442101d03400001c000e43c0c00c0c169619009031035030b481500300000060000500e04e0310701c0024001c04495411142034031881a04202c0400d0b40c9004081e04407003008003094401800d05001e000b15030a41c20b002e00410b00074812824800e50b669503000c0d4050000da40429801518442541034138003900c0300030b0016003218a0072003000040c2d040748440d6070b410f5508100520050303800b04001c0841b148280e01502a500d85420452219442130b29000d0b810880c1e80104400e00075507608039000702d03520171a5090840e1074868a01007910306504407030b4141c84001400b610803030700551b6400442d1001c039402d000985e03c50307080c89014040d6025121200305e040c80148103940c01000b5080c0070441d4042400509518002c14484010800c000c034000916008014419818010507038006000d06440e1007101e02081c1e61050070010006040000b69a958503440c00d045800b401a02403051084440100d280c03d6424448005c240620 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 14597102 1250 14595852 14595859
    0x6010b07050d080906010603020705010e0303100e0a020403030f032408071403010e0307030302070302150a05040b010501020a0c05150702031b04050106020a0503030a05060109090906060602060603010e19020301020403050304060e 100
    0x4042d044850312605035284180f0810000d0900d81c0d02c1c0550540103508980c070103c86035529032030b030b00c1441e40080010303500c501101c5a5100516141060300074075074801402584201d80100300501c0803e800c40100e001c070000c985800204c5503001d100d0311484480c81542d240c800c03c6110320004682c403000032010242d40042e821903103003240800400d400c94002c001881804d8000344204804a4000e5029045041c0240141e4048400b1070500924010080b103e007180300343d0f50020301007400301c8427030344501506003800181001c0046448461a1205c58401c1074858100910396440c0d0300203203025a01d080e035000d030846014000300d0350750751401d401501c202030245113454000500b0501c0091200002a0000042d40c03564a1348134101c40507010007403545060125140c0f00241102d020f10800a5003400307054001581410604e00a00742000906a980709030304100d00e404400360081400400c401c22181022070101ca5813021074003a003d25030000d0040d01020600162050304144c0800c0c580c0c030210b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 14598352 1250 14597102 14597113
    0xc0804030e01090501080f1e0a020c12090d02040f020d0f06030212120703080c04050607050a02090703020f090103091403040f0608010f060e01050a0207030b0c090109090207020105030417070506010b0705 89
    0x507004540c090403a1207210f0001c0c4101c1d011844034812101d800380c00c188000740c0c0c0304540c5e40b200300000560400b9140306004039800103220803200c80500598403005210060340e841c0c2107030440080c0180c6000c40010b0310480e914074185841101c554100c0301140c0820703034144041004005100e0040c4814441070f4045e1040390441c4803410350108101102851015125080c0a11a10201d03180c20b40142041c0000f00e003000081030a68582c1f020303104e4644201d009041c14100f80c418005c000501030302140506d030050000301621409041560002c2e0350a10b400a0070440c00d003460380e00841d074000d0304049400002004107031140d0001a45090350242e0301d99484503640c0c0d440c540605020740c89401e0006a01090010b4158859401171145140500c1160101c540f02c0e10380c4009a101603803018010207002500d941c0d80e5800c414814002c204041046040c810290006012880700405c0184108446210082e40c00c9c0d404082d191043d0b088412209190784407003014103d41c2c41403d0540b82403240 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 14599602 1250 14598352 14598377
    0x1503010e03030105030a0f05010e0a29060f0118030609060603020a0812090d03110d050c01110c06010b0906070b09031b06101403030c10020301050f0901060f080612010c080403 77
    0x2c4078102c0d18064014000c0301150745417a0b05c0004000741c102c4065485803100d00b000c507030070001031100c507019114009003410742e0241a03585c4125121814000f40c01c240800803280d40d940c00d00162600282040460304140455400184103681c000820b85407030310b10040244103641d809502660302c02e80784c500c100d40c3c41c0c000c0c40b503846148800941004070200620034560030100c840c404014030134108100c0c07c00e0001c0d00507003013441042086000950201d800701e02000b007401940080d90b54800e00c140341c03110748003400780c03680d00500480310414800030b000b10941c2c03142c204944455401032007000160070128051522a4013040700912100c1141e0101c04072000d0102d62507000320101d0890001043c503185000e8142900000714940c1400309214583e501f040030300008100d400300850050744d03903062804200d400e5035074201c003038000d1400000500c18207802070403074150000d1900301803005556040009007030a110444d000b4a65007482038001281e070700400b25a024a02c40c2c2c4542c3d980224 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 14600852 1250 14599602 14599631
    0x307080d0e0612190207050a05010b0a0b040509010b0c120a090608060a0e060405040201030f0e0a020a080d020322050402040602030d110a020c12010b090403020616030614011803020405150301 84
    0x41c9004a50400d8080d00070404842c07404003405500d940b6160098104100d070b40700d1f9414010390010544440c0d44a10400c68180360100405004c2c212008020307040c42d08190101ba4812014018801c0400b40042c5c01003a18004100150b4401c0e9821005962003818000003041c0e0642da00c140404900c0300408514549802c400400a55030030340040092551140204400741c2000351042e418141c0c1c3d8038502c2810440c6000301300040c01480000c0250244520602200c040540d01040c116080001030028082d800303c1200d00040580903d014640700400000c5200c1c940f9902890307001e03100103030001e081038010003d040500100182001a0302c43c3c0c0101158920071403032031400503040200b45107950714014070005400707501070000203001b0903200701040034000203440540c051f034020b508100d11030b070400003400030a80340e41ca01440590f2030100300c00c01d01d00c81c52105038140f0840303034402c840c0d01c03040d0240d240045800900034451800c00d1100500b540c3c00312107803980130703500704408020f6001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 14602102 1250 14600852 14600857
    0xe0904031b0309050a1203020c060c070519051e010f11031c0603050a060204080f0a0c06050a0314010e060a090b0d0f080c06010806070807080411120c0307080d0e06 72
    0x58158682102080549103460035104441d902202802480e59000c1066112100580003400801c001502c1e00c0c00346040103494105440d644da40310344800c1040d078070381950108258048403020394610f40209030524405080c000c240c1c0200d500320820708030b4030030400042003d41003d04020b032a241040d14440d041200c1035035000c46491113541c03040000325111110601c0751841003000103070000c2d0868499982a080580c3c24030306035075042e0081824010240180210310f290102540242002c1c0140ea40350b503c3c401c014810f210070300c003010800c1842580260410302e4100c00203040200c0315038660700c5d560032440003560880c0c0101d6440342c000c01c2100180c480c115409000400f4414880880d94501e440311444034011181d0031001d00c42203400076010014240648115005001d26140401b00144021303802407200c010880b0703035011700000c150181c06154060030306549002d1900e45040220b403502c0c0e40030300d01503018882d00500049540c004107005001203003560b42d0405d2041c80d402008140d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 14603352 1250 14602102 14602111
    0x306050108061b0306040612061505010503160509010c05030c070311060c0705060d020f0a050702011205040f02040b030c030f0601050910080d030b03010902060d020304060501090507050f0304050a020d0f030e09 92
    0x41c0b91840f100300c00c1c1c40d0810145a102000501c0810010344619501c105100e0b800f504031030f1a610790400c0041205040d203a80060002861701034298a004c200c1c0c05c000829812204080c00713070000d451072243c1d1050348940c1d001a000710449036106181081e981d602d040500c0150fa6840011001c1c0d0400c0c5040000c5803801c032403c10007403000c181020704000f055409101924040b030303402c22450a81140c042c01401e1110220b8407855100e1005000240508425000001c2c01f58070f00410000024101000801115010fa80000f410141240460320300b0928000b996818840c00c00c2541b14484e001455034140d44003558007443c9620f860062130024201c070700815009410070410703201550320a6100d403011181c004c00200328170820f03802041c0c0790792005403281441c5030004204828409203004050040481e1001004107160102004216004880b02c00e8501c403400404a000d200041200d0b19126400400e06118803405251010724100c0306142100803980c1c4440c8e140c01840c007100f915215 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 14604602 1250 14603352 14603371
    0x9190c03050702033106080912040b07150b0901080106050102010f14070c0c0905010f0503011b140f04050901140a0801090f03050c031209011d061003020f0105160606030605010806 79
    0x2402901002e40850004403006405094481e5000314018031740c0d0340005006162a403102030b83ca040407020303d0306282c00c00c1403d140300c12040104002c0c0d00384210880d0307980d64010002400c10741c04441ca070005481c0032040c5e076901c41e1401d400440c0048040d48400c0480310260003c0180c12104282e00041d1001030300d01000d0040c04100050640e80524030006613603100307500040006031a48100403c840d42178120314030021200c40140540c0c2001d218020400c1101d403407860030700b4490040180300c8030b4610b060064220300445d503402e040300071100791b4000d400000c00d50141d83d030311051042c1c0ca485078000302ca486060080da00080740d80d818482e807113581ba040711042e500210385840030f44880d408180d880d0301c00e2000b04032032560502c4450b0f1840c0100c3c0e04d800007044558103a0a424503000f00198503040702d070070030300c2070200540306100310008407503065031650800070071303180143c0e190301819070309040001c280c51014041000960200043c1ca108901c10000c03642c03904480f998412048941000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 14605852 1250 14604602 14604607
    0x305042d0603090201051309050105010f02010e070611030c010e15060a03030e090402181312031505040c03020c0a08030402030613050604060504060605030a03120b040209130f0b09190c0305070203 86
    0x15580b02e03401c01529a401814002d14050509a518220006680c0300503400d9035034200502c010741e4060500d1a404013544024032003101c1c182c40c016100c03981c0c1e02c1444180544683c08000000c01402950000c185940c0200f28007108044626243c402d454103d0009000e024009580b92030001290700c1969003555495910706004402d110f0042c0d0040c100380d9222001044424030070f00000b100501c070300002e00c1444a5514a0f103402240302010704401000e141c100710003200904541000c040807540200d40c00301d0303280d000d84002c0e0300034424030500501d9809a90769050030f201c10000114019882030301241c081781d0300c0500011011010f200020826045180401c0201b042c607044540c00c01d0041500080b15035441c03000038600400d1400c1100450b040020f40190480c2d14802c07070615031400d85040d860100310302c0c005611440544070030740d4103640c0c2c3e10132a290f2005591200c2c00c1e0020180021b606030400c80d221174840c00c2c160100202050421070401000d600c20300940d406150a60001c1d030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 14607102 1250 14605852 14605859
    0x30412060b0411070501020a2a080708040b1912050106120504020316060f1704020102070303080a11040303050c16050a121412030609130c090b0613030305042d 70
    0x8041c00c0c082400e150700c0741e02c0360030944541c0007900080c00310600c20350005035a854030003005094050300d6400c047c8240408000b09002941200504a046510200c2559220100c0c50301d0700c44d0b402039400c1001c1e20000402c404204442900c0d009201c003045469441c4880155081c00b02650340034040c0b4000101c2188000740b000c04640c12250b00148000c017503d01d42510202c50311806045507100030001540840e800e009a6000803c850820f1500c00441c2070b44d192680000c1d69440c56440b0080030810f111000442da000507030300c40c20342c0700031042e03130207544076920704000b01140c02c040400e41440c001d01d01450034031030f6120040c5049072000340c808094140340c88180c420580d00002c003910880d01500c0500988081403000348280e45014203402c1e00da0408205000000400500c00445020700300004000702e83c5804006d400c0314058a00032401e10b0361100450b5480c041e11110f50414001c02c10048105a000302c050402c1c0d800c1e100120002d10901c00e03600400c050050150303c41b078452000c0a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 14608352 1250 14607102 14607113
    0xd0302030405030702130c0314090607051c090305030604050c0c0a170906070c0305011104030809091008060906070f020304050105180103090b01030501050f0105010e03060a15050604090501090c02030412 89
    0x2140d000d4042c000303581c200211900810740d4401c4400164110030794520b2090080f98242c0704414804401400782c001ca482c04c0c1d0895030780d07010090606824048049000c44604000e8040a8410201c400043c000011a0320b0041e0403604180c038018419810440051141501c0d00151103034005404010011803030151180a0700480c0c503151282444020041d81c10355882e02d800404c0700d18070500030070f42c82d0361640c203105003194080e03185401214070420007007000c6001c4c0c10940d54130f13080844180d50703642c65501010542402c0f5900103210b5000c2c2200f045101e507030204080b84107604a446604150903142c504903268822402001e000c51400d114240c2c441481d0400190f426006040016840ca8692601c0e010520300741e204407101c1e911001040f00c980c0094402d617005240a00b490040d8295060001e52201300c001e080940440d07440c0411021100c18288a20007480007a0183e90703103603103c1e49000f0282500340501090181414100c1c60040c0c800401c860855682c50100e680e1450982c0c2d48 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 14609602 1250 14608352 14608357
    0x3050408150f0711121305040b0d0201051b010207061802010809070b0708070c0819030e040c0e04051e0702010c020106050d0206030f131b15030506090c070f050706030e060a0203090d0302 82
    0x1904ca644103808200d008100500c000700201c0306ca0b900c1044055141c001080140d48102144900451488a0580040c1d8004041c0c0d0b000c0d44001d00110030441030501411f00a00610700054800c07403d0948070440c030180c1c00820f40708107001781e0398494141e4403000c0b031030b584a01c2803090140a020401c202e00c04134900c500505001880355001900556403007840500d4404000c09981c0d60302c843c2c035000010190001c01210381c03018142d8080c4003144a85001400040c1d610140c00c0c095604e59001075003240c07107544402c1c0361595011080c0c129003403e8100034000d021301c818207009036290480c041803c0c034017800c81492041d40104a649196203e1284070302c01c20300907000c9010f07102c0811b00040000e500020704003903c40689010300e200c1b40340040315850145209441000d1524000c107001190300c2c1c42d034525a0055860703050f9561921180f401a088800c0b00c00c0107850350080440c00300b0126416007001804241410803502c10351a1512010201c5c4402c1d141c114160344144210144940079801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 14610852 1250 14609602 14609627
    0x117010e18010603060507020d1106060619020c03010c030501091401030b1807150309060b040b03280219060206090d080106030b0604050618030609010b01020c190506040303050408150f07 82
    0x403d001d6901d55401050311402e03150000584c1003490400c400a500008940c2240b900b400100300508000c1c020900f2881007244000540c1b661107034040080c1e00170012044046030280c001c0103119084000180140340a010f086001c07414607803020721032202000c105044c3c076001340c00c40429403a51040120b114444a03410f101a02070800001000c0105c000e0404d006e42d070a8602180a42e40c9181403001c41c0d040302c41c9548560300c2d1048031352154500140d2035035107a2070f50504481c20250003e00440317280002c200254803074141d50340e00d01c1d2001c2d03481d140f204850003a003c9401c1e03512035a40280d01c502a00300f0940001c0c045100412202c2c0c465000a20340c00b9020749220300d4180c651020600951000000180f5400c14030121092800c04229041d0f10889c494002c00c003100c0c402000030f449800850200e8841d4400c806100b2080440d80214001840010061950356a9a28018100c0d42051050302c0c054007891f40807860402034102c40a20404003050104400d40d0740316803e032240c152880c0e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 14612102 1250 14610852 14610901
    0xc04020d09020a03030c0203010c0801060e0108040503130602011401140612060d0803070309120509030307060b0f0a03050f07050d020907030207030e031915140f04050f03030f01050117010e 83
    0x1000343c2c843c2d020580185000365034520501805006040c251804c408402c000c11a820b070040081c154040c54450000800b40382c00c1000d81c5640c18400c0c5180111440221b003000c09a60025200e030701588201c0401900301202c140a031382c4c03985a013103a45c0d070b104155500540c1c01c008090741034802100c07055220000800c6500ca020b0143c890290320342080b5520800b20f55281130300030901c94511501882c183c41c81c9003051505200c08040b03900c0c1c0c09012001030015460300c00902c155500c070030781005485006884815079a035241091513582d8403c001665850152401c00f0405042000104603495009002c00d50309850701801100251b012030340c00d0341003060000d898545990f0a00c5030141039020052030008010031410310700d554074070487c0400601032078602007017600f1990b04403583e808000a5000c21480e5242d0404a080048200107d280d90000008104070031000101d030f14140c54080e40c0e03901700109036110b8603070101002e0144400358541e03c000198202c800d142c007241c1100d4480e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 14613352 1250 14612102 14612111
    0x424020102160b09010b0d12031a060d0518030a170408090d0c090e0307050c010305040812041a0703020703020a021e0613080c0105190806040e15040c050a0302030c04020d 75
    0x32440402e40803610441252055a0f2005003ea40c007000d0181c120705080864903001e0078005562002e0100e0a014116003d05481e10b0385052082c4055000c141c3d07081014085507070f1034000384c81c2c40005200071255045214661a868982c080002040c0c50039800e2a445035003440011030304154208a000304225600202001224070756201d40c0d48608000b031207450441d4a03681004501000d9450100c1c20999a82c000c2c070068010810000c5c2001d5801420b0070009170301d0700c80d81841c0c00c482c4106c004049542c1c40041c20b00c410408481c1014010460705000240f441d201c1c1c0030114180e214008000d03005030f2201610314054903061b038650381d00310003100070410750810f1000415842d0300241014145030901035000c0145006c1489480404017091800354500360060b40030400d4500210941801c0090760000544251111341c8080030120404003101c61080f0080911201c1c42001c40b412a030b01e03111010000ba0608200fa5103000742c0350700a010b4055221400c0c144002504940c45200b0819240c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 14614602 1250 14613352 14613367
    0xa020d02160c1a09090109200f030405010b09060d11060d0c080105091003050d050703052703100219050906070c0602060103060509031606020c0c03010501120303050c0424020102 78
    0x303500c01c18801c0c4902c0504440c58903080600c410a00031403440a51910208a04085a44c9120032a03043d50528840003030502c884919038964146540e0107030400700800103004500401c054080d504c10b5100c0c1c0c0c000e100560300501485185041555002c0d00540c1c80140d507800229502068080d0034006801541020b42400c0b02c5029a035005441001041c0c0c04001404507050940e034041e0b10064040d02c00007500e1640d40c1c0d179a81c40c0f00c44001e801c100800400c0e0f080405124408640050a1134019003131482d07514207019076807003406003401e44280302d441041040c18aa900035a001d620031108000000111201309803420380c86608020342c090410810b40000070207107052000940410b50003045290b05516065040361000f4044151562080c02121200c0340e44108210740c8580c003401c0581c507940e074240c0e080e180c0810201c120b46d140d42810008204d0101000910a00034061ba80900103515603420340f0055104600a03802c2c1d101102d100c80d1000441203d001c041c40303103240300051a1104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 14615852 1250 14614602 14614627
    0x260304022e0504030b0108060601050f0a020c1809010f0c050405040e07030b01030b09070b13050d02010c020406090507171b03040213050702030a030c0f02060a050a150806070f09030503030a020d02 86
    0x2001c5480801e07804241482800080c0c400c1c1d501512100006011034140540040c1c0580101341004604000000300000003910070b0118001707001000c0c0115515821419221b51180f0b000c45603c44558644000064100014054402c0142c0305031900c41c030f01400c0000340009080b5482c032990a602c1080000030000d5000c5481d20300860250034102094180440c0302030038a01c055100c2c00402105100408125030b040c021b12003150790444140003000054401a21400056040603601a24180002075086503d40200d44101c4660b40c40c2c00fa105d0012840004611007030700c0817880c041106480300c403840410002075400c203000500105241e1a5000340106a40b02210203800681010a1781e0400c41c0c0c26001e6001e6801682c20040503042110000941e1004000d000c2d85403940c95a01007520303191680d104800810011510302007031a11041019680c01c0180c40c0751000a21903091100010700c0381c603003c8160707130340304000e940f554441c2e200c0d0802940001c6e1508520541c200540100c259 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 14617102 1250 14615852 14615929
    0x102070503030d060501020607080106050a0302130504021b0c01110c1302090306090d1206211e0606050a08060c0403080a020c0a08060414010605030a021e0405010308030426030402 79
    0x1040e0f0840424030905100c002428014040c240740d0600040c400140405600401950780d02411480c1c0142ca8154504240306030480c0c40c0c0c40150481c2c8002040b00c02d0410700c14030400c480c9102801c49510031fa02000440f4004125480d12000d500002c0c034944484c074140d202024800003041000d42015000d100007410464141c41c44485980020112181c15030070045030640409a600200040e0385044201e6401e550300c414044102000400d910341040a40300d6441c09c007001c22822500113921900d17101001300000e004d40d5200e204d1156000550311030008055110700000c030381d000e090602d55a203c0727986800c01452001503000390100844c46441d040c141c030006100050081c0300f24106810030540c184408050310500c1c1c1d045c5041841981c03000508242c04c60341c199401d05082ca030200381c8107104003001401c40d0344141898000001d12041c81c0145d40a640030701066115880010030380f20214590210300e0211200c1030000801602e025000f0304040040d0070324890f42c0035010a0364004a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 14618352 1250 14617102 14617117
    0x30c07050d05012007060c05030408030f07090305030d0609110a020309011d150a0816020d0f120c020307020a060306080601090902040e060109020c0c0a0506030a050705040806070c0b060904030804060209010207050303 95
    0xd280c00300380c21046c84824003503000b003640309080c8281355040540350702e400d87c07100030b01315490030340c40c000031030041403048000b0002036400106503900c540f20700341000041c00891290700101800c02440c02c9060a91200300d80c000400f075002186810004801074441b15441480114036841061400910351100703500000141082781d9055500c4d803041902600d9000007922110102d0100d1030701c00d99650300085d003403c01b20202e040a03502290101c004a59801c1c9202541740114102003c003c480c3c0d0b00080a010781c40c2c402c039840442240c03500c00884c116401c51140007200d0340001c00400c680440303544042c81c920700140000c55032280180303009150082c280d00c40000a40c1c001000304840c017041c044c8103d6000b044580720b03181071400c0300003505400060720002e00195141d0216066900800485008009600a8036006c2c50415000b61650b680c0800c00d0703580c1441e81000030210b1424000c030034491a407540700c5a0564517507446080003034101108240c1980319101e40400e10b90f41c02c00281050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 14619602 1250 14618352 14618411
    0x9060303030f1802030c130f1b020c0d0c0504050406060305010e070515120a02161403040602060a020405010807200a08090a050a0308030a050601030605060d0c030c02030c07050d0501 80
    0xb550a0700445030400c0e80d8844090103003000c8401a034002c41d50003000c1d04211080d883d000c00c00d80403d401000c0d2390b2144a00140b41425031540c11044c180d04207000010f50302994070600c1301b001030003000455140000c100017500d01c002d1141c0d161176031299402c80e01032600000c0b500c0e2255202401c450002c1500c92031030f0b200241c10889441e0417000e0902c0b0920810f603c0d801c0092020840014101c09844058015008201c02d02c07a05e503102c2d40c0c102820741050f09440c2c0c40e105d0001030742c1c881c1e101d40514401402071100080c0080d0740e600803282100d906944440c5180c0e100041104c007418082203910680c6d0301401e8902a04504006d07400c41c96010350304082d613500792182000064107055200303038060082ca40007003021880c2038059075403150030b40202041c20365514004800401e140d4100581c0130001041c0c04c50040300ca5800b61520884a4070204039030360005506a03643c2c0910294210b850307001040074070641c02c2440031042c0542c491000814041031030f003c00c418040139205007915 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 14620852 1250 14619602 14619611
    0xd180306090c17100605040e0705090c0706020301060801090c0504030215030a15080309010e0306090a1e080d0b03010f050415020a030204170a0209012c0408070506040b0a0c0503091005100906030303 87
    0x34213202481544003c1204803800c224804040c58201d882d05014415107104010400006003283d020a040340c070102e40c080c3c000c45d941c0d0f031584009070a40c1001c0c01042e8502d40b42c1f125200405014004480690b9001004500c902031a00052140b03940001d00c49000d840d01d450b042584403e15252040143c15074002640c1c07116004000107045105c07611550741700794030500500510710000311340c9991117034000e800149a042d1007041c075100d919500c03400a01a59002480b888500c9881d80000c0b0120000c9000707008140400064000b6500d09450103003241c0907503040c0315806907483e0700501280c44182030150405d40d0700c0513485401c551662048043d9003010050108500d0207400441c09810700007220f190485a02c0701070540d0755004d004003890280220041018800d1007020340302013a40c013408035802e0749024906658a4031341910556046030400f000c001e1a02e005800b82e0b417042d40b0710402400c10f40c83c0702820030050300c4080e002e032000036140100800d41441501400d009140a0b490100c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 14622102 1250 14620852 14620873
    0x110d03031a0a15180e0c0a0e0f0102060c090a0302031501062304030f02040e0613050706050a050d0b0109051203030708060409150b04020f040f080d180306090c17 71
    0x8030065420a141845040312003010b00c0351040807450b0940001d5a850848100348200c194104d403006280c0006007828941020009004400c80082482044941e51b0038880614407003801103508451104a0258005400003100d080d55103000d0302803074800409000c07105070340340c01003800c241c42c1202200d0000e0000300188400f03904107807418a078000400c1d0500804180b040044e007a8056404010010071030405800e0079592650070410301e8010910503101142003c0c5410345241602d00401c0740e081c0030702e03e8000b51083c025800d0391181c3c146510307210320309031400600e8001001c10081e10f5043c40419400407505450741403c1c00304500390700004540e039061a040c050078031140140090300c19410120041c000509510b14000310010f41c0c100856110400400103000e405001c407582c1c00c40c1008035000a045510552000031164400d00395041d0780320400c0e045419443c00391030402e046250080030400142c0c564800b881131409410105212502c03030403104201140c0c42080d0744960300001904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 14623352 1250 14622102 14622131
    0x90507090b0307050907080a09080301090b030c0102010b010207030308060310021204050c09070504030f150e0a170f09091005151908040c0b0a02010608030d0c08100305070e04110d0303 81
    0x4050307000003100105066407603c4001010328000501c4c040070070008601042400d0560703006012110342c0041260b032690b8444260134010041d94041d10f100788940520184a940107100342c00555a040e800b901d60a825900d00350340c007c1c40508081d0b094864400c0002e212070580c07029051050303030150a000c0c1e901b058100245480c02500c3ea082c4900e00080900641d60340210441e42243e503c40422510002d00d030501d0320101101c0c400386000319080155007101c55001081c01d030911881900514100c0109100c00c10b4540990407006100741020410403065240402d8644d1b84100f08000c41d5001035212004254804203011860300c0380e820200d071506030342940f5241d0999283c02464144454605500e0f24a00800d59100711040e01340c2c005540c0400e1f40c400c0d0032400240020000f200d507604955a8030034010218010000d000034412000300307480881c02c071000800c82c0d40050050070900c0c10f01141041c8054040c104889030210100360580ca43c6032441510358460094500045186d4000c004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 14624602 1250 14623352 14623361
    0x8070b0f010e0106030905150103050c0414060d03051303051515030f0c040c0e09010f0602060106020604050d0e06120a0902040f0c0507120207030c1502010f09050a020907050d09050709 81
    0x60340e188103104001845444510078169044801d285070116507044c107824980d082000d08910b01224940800000c402d21400250310b6031240415201080f0442d012484001c10481c1914a1603000d5041900c0c500400e1185024013035245012101104a660b40d503a01464004640b605030003a4801c00c00308800714146640030182d125055028000c2c400a00c40a281c80f9401b1844175803040c5d6490f041c0c21080c038070a0300c000602c0d60000e80640d641d96110100803074016240d2085000510030380b070022400c14400315486000307a030701400030040710790420b001342d402610381d00c0c036150403102c240f020700349500d6144402030041180d2403000501925600611099550400011001d64105a240703102e0a038007404640000b42c1050400801c0400391074124200800c50b48003400c218480700011842a2040404425260081e0001c0029a107820904c1094602c981c201a08940000c00c4210140c2001e100c8039500c09024034000f450043c02c1690340c01101d80e01eaa054075150311034482880152184c0c8503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 14625852 1250 14624602 14624611
    0x2160504020702090a05100b07150c0306060f030c0e060f0702010905010504050f0d14010e06070906020705011e020c150a12050c0912010b0418050c010314060f190308070b 75
    0x5041d40740c807250380c02154008a0142c1140e01041d6584001070740c0001c6050b079000902101180d0542e41e00042c10f0040e5810281000380c2109490f0904040c03540d406841500110b03000c903140d82c11128181c81c0300360000c1030980f000806005035000301400c140e6403600100045181103032041d8071020035000040c0302c00700c1f0360869414410200b2090000d55250000d071102c48008440d400c0c415000761800011400000d244d1011a40c02e01c50107140700342c4046001d81c0318110130754440072040c0e501c071030407a07072036885220b042c3c0420207a00070080c00e01134141d0321503640e02d001e0048030811883c0d640400c007440d0903040310802116010400c100000d5100300e480310203c1200c48203101d18107003400c0103031940c41046156441a03031808040f00c02d244d020f410141540c24000d100b0030451140001010354440540000c80b00b500a09202c04000d60081c8220f207091405641445031950310b10302071249580b01c400c0c43c0c41d80583c250241111900b81481041c0165128031812034984402d440c4c60300c0300540240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 14627102 1250 14625852 14625859
    0x30c03050c16050a020d0305040315020414121c0207080f070302030312060d062306040507020601061805031e190506040b071b0b06030613030c020f0a080607021605 72
    0x302071200c4505508160340b40702d000800d280d00030001c0d07071030850700d1310840a82c025001101c1032102030034035800c500680100d0307025600d03100003440ea001c03540049104a0048604c40b80c1044001c2d452414a0041082c00c40e501d04121080c540e0307101801410a20703502d0320400140c0c44510240a881414092804420414030050000b2421540065202e0098141c200e290f54141c4001403100d40e140042e4070700c10358106000b005221100d8203618402d00005003009041182000403c2041c10284038981c41064940d000c1c000b183d00300001242e100c5111400010200c2180704041403540d003c0c80120b080821807209204160b102d404683d0604149c440641010b28100100b03801107100826031990040c2d100d00c403100c01d0380d2031540540e010300c03041100714000d4245500f42e000300701c029801540610022404c86480d44e40e40402043c0c262031035034000380086c1900d40e0101c018140041c1900d00f0f2a0010034408a6036218602145460300454440006a000000320410b0401c60f0204201412056 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 14628352 1250 14627102 14627111
    0x50a030207050d1109070302040b0c0a03030c0906080f040501020f0d060302040e0a0f03050310030804061205060405090c040209060c01090507030b2505090d06020408070614090109150201090f03050307030c03 91
    0x340c131581608034620410034081c960034000102050b201c1c0c1d04880c0540804815152034118042d03da65035920803102c1107012926082501502c580a0041c0d00103c5406954000c441e0740c503002461490007024000b1a42036400b031102c4080c01081c00041d0510b014000d0000501901e5030041200b0307150400700c60390700c41d002104460040340f401d13030300e103070703c150300340c2081c95480c0c4a040091900500c1070380058035040001c9030100e4441e9000c40304800954140368140116105c10042200325481075610320b8481d408210040501d0803d0b402a0848131001010503091804c1180f05a094511862044603287c02501c07060041061000b001504201e00c400c0f010304540a5100a12541014012050078031401061100507607503000110361030305130b100c1c405544031644c40010343d50314451030040202050000a51640036111035081c1c804841c0160741e41c00039030740381103a4003281c0d1809001150455480d1125000403d500d420010525841796480c20350302c1ca05208010201c0f8010741e901c00406060 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 14629602 1250 14628352 14628379
    0x90606050703051305030601090212100605180607020a030b07021c0f031a040e030301050f0f030303040305090604080303090705090603010c020604030e190e04030e01090e010303081503030304050a03020705 90
    0x80507121101d6260030001e80e42c1d01e02446911290840c0d610040e41482404000b08546450741c0180c1000300da00c04a020301340e03c494065141202031401060005034092281d048011040c0b80c42410104014107006e1030014a81c0200c2c0340a10315801c107850701d80c40c1905010a480d4100032611030504c04201d4007110200d0b080000f130a40b562003560008144d11018031310507015030801c14605462004104000c603040b090141e41d140d400910802d403140c1c0454100e0011400c0880e9030b560b81050080c081d52441e81d6039a425103040c0c0120908640200c020b0102080c148820002140504c2c404070080c85443d240804001c0b400c03000402d074a000764188071243c030140340c0010740c107900140c1c1824018180d009400100340c0341e280402c4c400e400090700c800300080c0c40c43d000500c5802103000350b86a60803007891100549650803584500c010700c80010780100003183c171800303801e0b030402c140510900c411030030140028030719041a0341c2030716035401800b0f0034000c05d80c0400c100e00060000b41c03441c2060868 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 14630852 1250 14629602 14629607
    0x90b0307081b21090607020703030207031b03021207050f06071a040203010f090b06030c010906050f0a14030a1e060503070902070503120c0c071a070303020a0c02030d0e0a090606 78
    0x140940600e1588001040301005100030b00d007038502501a51440480585000b00403a20103407080c1d4a15045006800c04611040d00c00705488041c0d07a056001040442d10315a40e102281441d010243c035412460000800169202d461118529062800400416003403008000d01c4c1c01d00d082036a44070340000c004000004699440a0824100d40c0b580c1e9a19996580080303805402c082020000c61031500002004003d642607146000e018103404031400c00b0032a00c015104d00d40f050141d100800c6051003601c0a400101c40180004c0c41140340c4408006640e02201c2201d401c16581045500c1d11880340f0700c0d0402c580c0c110301d8402440c030007003030000c24901804240c840680303006441230306400092071014007800300111501452200c02840035494040c82d40507982e04058904520f90140701d1000030030a40e84108144c0140c0e41d4864a4a0009641d4069000394441c0081e04188a80a0b80185c00350ba4140030603080b0307840c0350700d0b0f0810172200b041c1000800c3d01c85400c0001603070302d8000180552039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 14632102 1250 14630852 14630867
    0x8060709180b010903080c070608010806090c1002070506040306020423011d04020702060301030c05031b03150403022103010807050604030c06050f0d050a0b040e0625030f090f0201090b0307 83
    0x4801c4080000c80b4606140101c503600107640014205031000a44903c1c440c000055807001c03078112350356040c100d903210104641c035604284c0b9070503d141d0140c0071600d01c1d0f01c0c110700400e108903041d00481304015906c001003000c58005a0040d103020b580494104a19020078411103070f00d049425000000842100000e0014200e8800c4102264001c0d44031044036103c90b4100e80105070024030698176980d481c074019046140d82e000b41806030042141e40000c120301205481d41d01800180a048071540c030a01d060040c0c40c004000340d045210b1002007098070403d02d003260403484040c0c1d400076901e42c1000002840c0c10384039800350340a402c04000420104061254420681e0f05a1800d15a01c134000850080300b40a01203810781018a00418030180c6203071680400e01514060710140540d0b0548560152103441c112826103142588801c0c07020a99500110603d6031801400d000030700c614502d045004698600c00c1c00c42c1ca01580040f20019513030004c48503070040ca64074a40a1030751030807407801024234 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 14633352 1250 14632102 14632139
    0x111070b030c07050f010203090706090f030803040201030b120a0b01060203040e0a2a030b0a050a0302030c0103050405030d0c050306120303060312070c0b0304061401090501080a140c1203030108060709 88
    0x41001c40803400c101000c50458110980004c00c0717540c0c0f0251407681074000d50041c1c503071820034420454005001030060b080b09040310904401e02030010316584600318035078002030040b070405680d01d02e10615a590808a024651040e50050003413010300e28002d41000810781044084d9402448200001c500ca80180c0398030400601000c21500480d00440013107010900758061003403014005402c42c140c3c180d01c0300280d56021160005510307951802d109004010340400794041e00122850241c0e54026000240c1044c8944200ca00e0034440d01d402c0d108440e2541c0d034560002d034000045c40709030b1504111003406a40c10740c01035451400e0900010b0b5640e1002c0308401c0f0710140104a401c00c1c007124400003401440340071001540e07882c0c113242036002400c1c88014002c05440290001c00c0e18007441c0704581c113840456001707044081068550b034a81501280a000140c45603040c070300c1c03280d106d81000c8210b100712070005548950400801a08080c4002c01c8002000b224290802456585a5004419 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 14634602 1250 14633352 14633369
    0x16060e0606210a0203010c170a0902090a020313020a060f1202040602061b0706050114041a0a12260a08010911191107060203090109060201060f03080c0a1709040506011107 75
    0x80440300d01000741016503010300a175155103000030b001905a0490041c21054203070aa1404903603403000b5903402100c500d5140a500f049589000503243c035420740c0116003203c2409201d1540c1d0b10300f64001902a10079801ca0000550410300c9800c0064110021040701c299a0200b9400c2908100000b03658000c002d255215071814420340700c3c80030440b1000c1301c2e41107802c48400c0c010f56071210f8030380b00d071003019000c06806540303800305c495500d81d9454840c81c100d0900508102c1c2c22031401c8900d1005128a83c0d003660700760705030321130b185400d403a040c1e542031406000c5044c103443d0030700c1400c050300d203642c1684651481c508100e01e9001c03544038481203580c1d005034a00715044072164000100c4039558940820502c900c100d04011500c40d4000004d45014242607030b580700b50a40381e140c02c9003a00c220f40703c1e00d01503030607443c1d0600000d080c00010740651500002184e040421130b0300d8840c242d03040d00c40011900c3c1c40006c0d00b021941450f00031507a00910a0074001d4410619045860703580200c3d1181098 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 14635852 1250 14634602 14634649
    0xf04020408062d0f040b01080a050d030c030e01050406050402040b030601030804030f080702031e0115080a060c02011b030902040c0f020604020103050414150901050604090302030f070302030f16060e0606 89
    0x107a002c8098100403883d00042060025031400040d6580307010780070307282540e1071207a01c03000240240d80010100049507000002c0c08e002108060142d02501c0c4014407003040c16140c01000300040ca00b4400c0500c514084c01010841c0e08050050100720b541504d2007a00907048a8018400304104900b203c0c102c0c1e902499002502649041c151018041d100000f540740c0104c40081e803401c10082445142c1c6030100000b0801e081c400070140c0070903942c501c01e47c05c041c6c000490b001c2c0400c1550b800059404058000810000100c54090520110781c000d404082961032030003e0641c1000d10403403800742200d0511907225032020401030360f1800e0040000b8109074039440010b0410890483e00045021100211014102141c0d140050040c080300c10203125072034080041e10700d161078001c85a1007501a00590b01d072294018038052154480c0030158190b1200b0850035001c012b0f180003d2030a40c0c000c9000d0f02c132400d03680c601038003582c20f0422400300d00d6000c0c2c1c0c00c0c4181541c8424900703220380c442840c00070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 14637102 1250 14635852 14635891
    0x1203080402040b0604170606010503010f03150603060204270c05030121021c031d010504030b040c050a0f050f0306190207030309061407020f1203070318021203090f0402040806 77
    0xb0050b00488400355040340011800240303803003400e030303440b810618030301c040d684e01da034901004486600003441410602d202d404020004100c0000341c40d5100301c00c5000c042240c1e038498607080d060740e01652002100750940115920000000d080312401404000310510a044c0f602400618900040c003c041c50031400c070507a800360210324024170040a902902d80e00211003003081c95840900c2ca00c1c402d8000c10508001008184c0e1030001c10000007105840b03281c02c16086889a6501450092044a0485090901181668484041000034580450410072280c00c140c01d01200c03030400031142d400399000e2410b1040001c0c60105100800b03520860040c7c43c0c80f424201100505408940907291a1500385603100c56140c20499a20036804c0b5000c032054601c884814540e200d2034000e02189a402c2400480c1d0b01f0b0344260800400c14811940d680142c0150341c00140b54043d40f8440382486500008001c085410305605202440d0300c2198214101842d00403020f44562004041b01d0040c541505043c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 14638352 1250 14637102 14637109
    0xc0501050306030c09010605040501090b070506040303020306010224011a120a020d060f0905010314060906040201050313021003050106021605030705090a0204030b0405010207020a230405221b0602071203080402 92
    0x14142c004002d201d905c49582d03034070015001b68400e0103800e00054001394080340e010003100880fa450b66010380180015070386da44040300207400240100d4114028503d01600003a20102541c1b1000c6440c050000c403035150400c41140d80300301c050340c0c086d024001c0c0f00d0320b140182300c0960b1035840750102201690382d80d60200d0080082907a031b00800415040c06d2400f1401003216401036060300d03c51060a8595024008210394424017181e54a40d070380c1c0104005070041d48240050760f00700c0078500c1145407240c0503500007240103040c800d503000041d50364070040100982c104540c010b100c0c81030381391003015810b00c801700c0d4035031006002d03282c064040c110100303242c1903540e4100e030004e540103070444009013004c0c03030b015003c2c0d4442242a403062408600c049107410380c9260040341c2c4c40442805c0c0c1e041a8540c000d21002e0800101641480d402e0070880e0003820a2403034450440c144614a42110b074442651803110720800e85c2c11903021588542000e0111401888105018540504080d1060b54462000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 14639602 1250 14638352 14638363
    0xf0c12030609020c060103020f01050705070b0f1b010f15051c0804050d0c0303030b03060c040509060a03080c010f0515010801060503090f1902130e100902010c05150601020d0306030c050105030603 86
    0x101c00b01610010340304841904c04a02581a24030131500300390018001c4004423103074046d000c00a407580e0000542040902608001401480e1440e04100e0528003e6511101060620001801c2caa51038a0001700300c1040d600c901c0460012550702d2484140c14800815002d0311013203c9001400350218039803060000b524107070340c01024020a070318406d400910345500c0c010030314881140401c1c1403000e0120203250100d855440381814000140c01c00340303410704224500c48098400b50b0070180d0040301201140c981d400400d00142241c00100300b0510003a0020120b41005001c3c000f0300f0306070707111400c00341ea1000019046480a242031926501c640c84645d09094200500000f0b522038012180300c0410346007440a03210b40201c170107030324081c049104002a508030817043e84e1140c000c0c0c07012080c0000254402e03c0024010305d44200829010b40e15507260400605104010300ca55004010b41903904120f5450034402034601803040780e19594980d0b8964400d8080c0d00d06202000c00040c405840c04c110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 14640852 1250 14639602 14639609
    0x1a18011701020409051501080a05010b190c0b0c03150901050d020439080903071110030b120102030f09120d0908071a09010b0301020c060c030711030304050c09070f0c120306 76
    0x1801c0080381007070781034503082014640d101b078040341041000854400503807003000d04846a10000070b1030040350400546c1e0fa000c2d500c109105101030300a070346004c101100d103001c1c4030300902d2120316500c2c142500500765511200d58558803d0740320034018000c94892440100c81240d056070040b61007525900e084020100d022019601e4074100c00c114200c0e181b18000c40381252041e0740395210b2a441d01d01c951900d80c400d0b98005031441c001c0b202c610b900d0b030410f07204ca62600a81c41c903001944000050008045074410800f2400584d0003000348000b005819080d19000103c070001804013500200e6500c4a9000d981156a44241e49a040e8028070003904200d50300b20381d00c0710b000c090310010060071120440090719416441d40c80c002c03041c580303424140300b2a498100040300401c0c09985211f8a001c240d40000e0501c1c04100c035100e0b800310300d80310400c081e40c003d6103d207000c1c106a103482e60a01030315800003800c003010464076240341d013140c94210f0125010b50341c200805e8410069036110540203441e01d5031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 14642102 1250 14640852 14640869
    0x307020d081806160309050a06200102040503010903020309090601020a02090c07020402090904060507090e011d0603030702030f07060201050601170f04230c030c03010203070504060c0f02090103061a180117010204 93
    0x107012103135403002c1c1403080c00d11842a103074020460380310020300079030700058068200400e001c0c0320b6080c000140c9007020361034a00c81c2d0001601d0b00e5104c41c04207003907a50940d070031805a1b20120740740300580303040801c0c3c2d0362040081c402466240b038039400040c44401c0107885c10181c601c1c0083c0510540d150741d0111010b0b2413000e0503004007420945040001407504aa21400081504001041c941e04c015071607412505c0c2c500c500307481446206c0030500000005403902d13a041c441002480016101840403010007108580a0703e4003500d444006400d4900051015040100c01c260004040c0078040da916000609010100100d0350b861038480d9400146814601e1008103d11066801540005120010030320a0f01511002c001c0003043c582031b400251000000700f10184418409984540208601c05000b2440c001d01100e0740d80200d04000d50a03082a1242c50b150144029035102c004107820b8015010b030352000d03482c0c00c103400c01103004006018850521142404000054401b5010f0f5405090840c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 14643352 1250 14642102 14642107
    0x50f03090105041e0909080403050d0f0806040b01020f07090c0f02010608030409020c0c180a0b06090907081009090803060a05011b0204050601050405040204180b0a1512022110080307020d081806 85
    0x7d060001ca40e0300540720454041c0b140302c0f01e80314203e105441000d08040f1a880726031580d00d8020411002c2c150f041c0706a8118030641d0003d16882c442003245000800c0800c1c1c0008101d03076500c40040c802c03003a410188065a05010080040010000858084485401780141c4900e81c482c007950501011000056100e02e261818982003100c4034042070140c80c581c64100302c0301d1442030921405008420045a00c1400c81e40001ca4a50107000c80a5202d00040c80e548800d0f0344800c0e0b181f00311035a18a0681d1080008000c01415080216960001d44024201401c0c06001000001680112060000c1c003558031100810706e641d008030141c1300600700c010425522030780c46800343d00080c000054001c035140d0400d00c041c521814113404440985814105403041c40001004c04d483c062621b02c1c0e00d899082c1c1c20440c404c25648904e008895100c0d41c12001c01c5142461951070400940d5600090021b1300100800750040e030f28012840104c80d4052955510b03540c19108801c0440b41d5407041c43e8000000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 14644602 1250 14643352 14643371
    0x3050405040f022704050a0b01080109050c0c060405030a0801060903050303150604050a0e040b0609010509040605060d0b090d020d03020301060f08040c03060c021e01021303061a0a0f03050f03090105041e09 90
    0x2e00340b001c4c54102950100b02e6513440c1500c4101341d44c1d400700d09501281e03445005210045c815000180d00c640d1000c001071810117000b0f40c482c034040c0120b170282ca403a0000b2624118440c0c0c00208640100880c2c5040f01c0c0c1ca50545e1581505ca01c40070700050603000c102040c0c40d5540d215001600c004110091100c0d41691ba250440700032200200c408a61005080300010380d02d00d4a07041c101e041c0c1d9070103040c504495940d9901d0000030540540410b44c0004400344400000751241d0041e44203041c0e0710090400500d01d45400381c94201c070304080005160045c001804566441400c400084440340340c2800c071900c07541804240c114a5070009042d1600b080000c0780c00b940c001a1038144150308000b801c5881e650300300724500307c0c0291940a00c61481c142000c2010070000d402600700384244900784041401500c00280314000c40380c2c4284c44032901000300f00309001090000e44040c5010801851509403002d0000301944a5409004030b540c1d524520303c01d1100303100d0181c0c005014040c20030000c0d01c0c82c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 14645852 1250 14644602 14644657
    0x2e0e01031b05042d1d0d0210020c070302061303080f0703032910050409090501141003170a05090307090506120105060a03260d020304020a090c09051203070c03150b01020a03050405040f02 82
    0x1a001706d040151081080340000b48209100b22085000040081d101c418115401c0005680c40081980c4a9200b0315001101050300c0c400200741031042450384030b41c2d0b0781c0b081c680a015035800300c009032448050404140d050190003083c4140302c0710f046840d84080540f1440a99840c015600100e00640c500100d400c20070405501c00c090000c00c4036000700855a600050341ca004d01e0a01000b4040d00904041800d2502c210000e004054440c1c2484d40c1000c02c0c80c00401d2404495074000d60501c2e03243c0e0203025403402d120b0f030201092000c400007480345240000100380c501c510344c40020310011700281241240c030842c5440e0040803202c15403c0d0b541c1c220311040e00703002e5041036906a200e4000240000323642d030281e1050389480c1c9000d8580201c03592034507007003080c80300f041502d500c643e000402a1000048400700c8690107148140c4040c0b140003280e80c2030300c0840e9030520380303181590700c18810140032035040401c0d182143d9007100d011800c1d245901413203000e402807441c110040b88801103403002c0c0c4074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 14647102 1250 14645852 14645863
    0x20906040e0f010317030115081302040c02070501080a0603050303160203070c030c0303090e04112809150b0c100506010905040c05030a0c05032e0e01031b05042d1d 72
    0x174058941c4592410010303246070424031083c40743c1007407400c1410200f0001e600440d901c41d8041045c6c0c40710392503011141c001c40d0541d901001c401c40140c11178002800030b5a00208026009000c5031403c104050455440941d6848090004115200c4020111106610800c00c0b02c0e00964010041e07101036990b0315141c0840201400101d000c5400400080784242c00020b80522560b00003c401c0243c10240090004101d9208505c60380704c10802580b1001c02442803a420042502480c00100e00d01101d8040380b03a607100750007048202404210101d041140060300402c0c1c0050101c00154649079500142d03810b81c02070b8011034005081aa814040d0350304100654070810340044144000305a004c002c071214030048400b81e94022040f1440c882c0d4010602405011150900b140d09885468403001c0614040076441200c040e06103031030600a6040c608618001040e0986050002c1c0080e000444007051034281152002d00c0d500c040380a40080b15048000000e4036211001d00c04602d80114680700c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 14648352 1250 14647102 14647109
    0x91115030108060705120103020f030c150a030b0a03170d022107020c040903080c0a050d02030a0b031908070b06030a0b070e041802060301061110020d091403030712020906040e0f01 79
    0xf80285000101c0241c0902c00f00c44074154036491034902a1700b99804c00880134112090550140b140b82c0c600143d58031012500440c150380101e0154403800c60304030007000d6070031140d207903802a41c4104080000641454036105000b005403280c944441c00c81807020000d004640c158000c0700350001411081d15812006180a01c0c0d8030350a440981001c00f0510007958512100180040c1c1986d000030f110704501c4d0013911690601e85405031034900700742101030a90300142d032207620080e505e00501105150400201560f10322030b4182801011051f10340c0e401c18010100c0150121030b48400007000b0396014031001211a50000b1858100d0501c0c1c03500400300349000d50000c3c060761900704440d103800f49251000c1140c55006259a145038203080040b0303070500000440c00d0f241d1183c03070b464440454840c0054801c49001d040c0c000380c2c20b25581400c0607000320012080541c0d030801c10502c80c038594440000400e500f810b10000da5146c54090100302c07584142d5100149070782d0040248101450038409040c103e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 14649602 1250 14648352 14648369
    0x50a0305070b0a1803050c0a05031b07060c0308060105030408040e0a1e06050f0f0a080a030806090f07020c01110c04020d060302090114010c030804110a0806180712060911150301 78
    0x2540c464141d40202d40304c0f45900081841020b8030038000a02c260001d1010607010026103415060580e01c180c51904070483c8459442c07125203200724040020012100200040d19040e10090926200649902d0019040c14100400007000800b403155840881d00107260042e03c007d02031070810030403001800d4030708800306000400d10300101210540d0049601f690300051102c0e80d0704202c2010401d5400700040702582224211000280c425001d100341d010f2140a900c409102e444c00c03c08208481c003000301a2030840c502a02480f03c6c4540c00201e0000300c149c00c1c00d01d5400340b1700300e40d005440d003600c06c140c1179030160002072004040c0240c2d402000c100c91003925101d00a176203944010b49141042e00507140060002c0c82a540424482c1841c6500680100094920302e030035400804c2c2405025080002154041c20500034807840c52843d00b44907a80c00c00260130302034208070302c00d4540007060384041d00c42a150080d650074403229100103001440000c01c101182403400714001007542007403246015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 14650852 1250 14649602 14649623
    0x140102030a0506040b031002070213020a080103030201141b0d060305071503061202010c0305030c04080601030819020a08041e0503010e0d020f060f160201021903020310060507021813050a030507 85
    0xc3d80c2003600030000380c5200140a03101c07141010301560020340280e03030140d9002d044004901c00300945440201030051103a41e0721a010760550502a0958295a4000d88860000020071407400003002c0400d042d0424030707403c0765803205070b004c444c0040c04080d040601307140204000001c0d0103602c1d1101c10300300f140035201402041e075030741e2510302925441320010380850081042100000d00c10340c011580041c03452001414035840d02142d9281c00c07801d170403c8a400d100050440c40c85464420102c11000541c401054a04819582d024460150f4422400c140303003c6140c1e4107074102860341c070001625000c0d00810119008030850b039521402c00b204031001d406048550141c40d100840c03614400d802c10840c02d40d15442e11007101120100310808101103550074004000401600103031f0131900d000390780d005600d0b400c0c051150700203082d00c0d50160f02844020400613005072070392698004034490300c8400c0031140d61303803c02d02151a0100c4000500900038404a0000c068010000c6c20b0554001c452544 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 14652102 1250 14650852 14650861
    0x601020f070f080f0114130804180501050112150501081003060e0601030b090304060c1104020c03030a0b03060703060503060f040201110604030302030406060f05010c060b060f04030c090f0212070c02010c140102030a05 95
    0xc0c03c84020115038165034486e2000620501c800c1110018002c0c89043d010303160075500d4140441c1200d88030311001d55140c0310b0004200540c0c0c880c00c000d03080760014104100d9a00910640025064a441040c2c1842691800954454040c440038401550840d4040c040f840000c0c810a4031888240422114484942c0108048100002c196419180c2a8540c030301e52002c00e442d04601508541c4c030a9038459020007140005410610103940112080c03031340030440c0700152040608005000b02031500b00341c5812001c201c2c03035400041440d04501d281c0715608840c6c50303d0004a0b095148455402041c0c8210401d0208042d0306600542c0309038041ea80c00c200054072100120b180e0303c940c0c0300d4640002c4002d0400c0010840316800f044100c030004003010b15010511b01e404405070016070081c0e5800710200c4040151204901620b5036620914901318600018200300c0c20071480054401020011495600c9046900803002100e0f401c3c0c0207101116941c00c21810395010754400c440300d0320440e00f03090116 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 14653352 1250 14652102 14652133
    0xf011104050306011202040603140c010905040c0c080d110301030f03110a02060406030e07050405070c14010203010308041502010f02030c0a0f0207050112110906041502060c03010506030408030601020f070f08 91
    0x32000d8070001805000b2607464007106003008400c805041c4e0303010307940e12400000600458041c12102c1907480190080c00800310015003044150791007140070328106518410b040342d0050f9495205076010740e01a07280c001d210240e0005106c000c4c1d60b090140340010000c0180002e0000c1014a81d00c40d0785d50641c4c080440c1c01c401d0301c64003c107800030740000d0148402d10030107000ba0048141c00c80c884085a54459032030000400703070740c000d8900764041904403080405121200550003c81c8616100940c659450b542e543c004610940c0f044503000c01e0118101c8600c035200790803503048401050010764403428640101c6041e588890b200300c0104000032200402035001094160854205841c0c0410315403400c0340c020060140320840e1180c4400400140a6640c1c0e0b074000741c0040c10f89610b545001d058580d5020380f929101801c102e8a185e03007880100441d0303641d0000c6a41c0540d200c0141501d03500c42c00e0041c0d2906a032281412158000d40c5008106454002d041c881103841440032128245441c4490 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 14654602 1250 14653352 14653357
    0x1020703180902040e06060702030a02030111090a0902030906011215060303091401021c0521040f17030c27060313020109090209031c0908060c03101401121a030307050f0111 76
    0x80c1c0c17442c0031071400060040c0c50303d403014107000d070700180980d00d541c0d04960000b030071603038420460460781001084c01105410900c0c40d800c081e00d000d5004516500300341c0f200301d503070b2041442030384c101e550302c5c01c15001080400c8146001c408400003082c441c90342c030f030300c0c000e0446142070141c900c0c4001402c08100080d0b20006a14002c603038500008503c03180c2d2078a0481e900d0748036000d0f0081d04403030302101101903440c200701507101e0b0f03010744003402c8117282611b42040b091074480040340040c002481803022203004002110041c203c0107940e41c580c01c00843c0070f1704414040d041c0440d44144040100009058002394070030001e03200741c0c1e92010044c0c039502a0822806203a1034682c25900c12203035030309468a5007114402010503410304480003039035542594682001254800c41226010086c030803040141e40319000a00400100e4200c020341810008018a2070140000d031415107030340304120204090404204800405401c1d0b0341c0d0340d10b80341801a65048a0850994150703e07000310b515034604050103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 14655852 1250 14654602 14654609
    0x2100203040f15020408030d02070506010522150f08010b01080907060c0807050106090510060206010b07020d060b0d05030a020c01020705120c011124090d0801060801050103020a020f0102070318090204 88
    0x41e90580e102e0a468140c107503491440010f02c0300b50308020201d12990f08002603c200b230200000541c2c0d07003415241803801c3c2941a840280285128550b0200c03d40003455095040c03074401000042d00d400b003142e9181680580d500c08001c804800c000415188019040035101280030f0302c440c10740b926040301482e0740b48150700c505400106929810000100e0750401040c3c1035000c0c20002ca20a030710380c000c0504480c015107002c1035001803580104401a014404240105503155040d42044103035000b0907050f00807031b907004203800d40d07801e0855010354460301041d03c01600102280d441399000074029503145045000107000d84100d0100003480d2900d410004110300d8110041e02c145040140103444451040b004241c040c020303240701c2c010303181c00c1c1c45001e50300c00e40070b503044400ca007007110060f420101a161094104014600188012a040700581e41110400c1c640140d13140100103080741040081c80c12813265500003c0c0e69014140e102c6068105141c903450000d030072640d00d9030441d0492090b4030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 14657102 1250 14655852 14655863
    0x3060c0c03030c1e0309060b1903020312090d030e0d050f030a0e0916030507050f1207030605010305130b07051c0203070206010602031306030b0f06031003060c02070302010806060a050f0307030605010210020304 92
    0x81034128070f4425008a00d01c148a0f15010074030003030400024425103540d0314101c10f09d001d0300104100758a0100700814003120b0400e0101d1901c211b41c1c002c20780395510110040c0602080c1d0041c0391844e202c420102d01c410b41c200f0103a4580024109030140c4a43c05000c0d064006039202050068030b01c1c0c58201c0c180940880c01c11000a480106c505070086c0c14020201c200740030091100d5840700c038611004090500e2a103020300c1c25460300185c05800c841c00c941007a8105840c02081165000174112441d05250300300c00d00140e0340d920741608669510400d0320b078101000048010068200150300a18041c94103038003642c100d80e8030f1b0841203a482c007540340006041c081d804000c0060501070341c1700104c406006400c0c41c8e088000711000c0360030381d80151400d10036180e9101c420800e0060314454003031207000758030103410306a00d1038000800502c00503050900c18800080d4030100e9902400c200c4682502c44001303180c41e40303001c4d00081c004140760320541c1d000d401380111b451345c4404140b084902c92076200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 14658352 1250 14657102 14657147
    0x901050f0a030b070504050622090c0c0f14031c0506091306020906190804121d090a09020a1707080a080d020c12030907030303060803091012020403060c0c03030c 71
    0x103403100d40c2281e802030084e5060020812012406894910041000300700a80e004182c43c882c1c0b652400c40343d07405902c114029444d0440c1c41c106641d00c0f540100300d0381c0d00300e0000e500081050500c42481c01000c42c6402c542c0c4400145003d0b031452041c0c420300340c0c01c2c0d9035108204698036482840402141101c84401c0c0b048a546a80000fa08680c0078bc800d07021b015040760b0411085034009151307540b010070107201140c488020001008040050701d4030b54003261400a05502c0210925042100100ba41c94400c07803240b00051903400d4a1fa1160000c190000c009420850751421702c4022a0340034050401940241140410328050024070160b8241e44816000c0c80c06004071070580007900315415210180c040e0b016000b08039900315002c1c40c069040c020103403001c42c3c45d40c90060110307a096880501d070750b04140400700c42d03a5a1400d48459902c0c0c98102040404001301032a8024440c2e40c00c014081071404244225690348150380d07200492098804121908400400f40c0c1c9081240c4030190020440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 14659602 1250 14658352 14658359
    0x10303020a0210020c09040c03060f060b040603020a0c1a0f090307050a0b130609060b1002070f030b04170a020105010504050a02120408090a09180516031a0408090303180901050f0a 79
    0x1241c40c124507070f01c1c03407051391800030000b00043c18811040d0b8041d260408850018414040c007841409103956800300d042002c607260078440d07205400b4a00c5140b0515501142c1108028002c40f11030511980c000d900d03c1091040c08001c907240c0308140d0b0b0690040031144009000120000101c1c2c09498000000b081d503098142c0d0344100b800ca00901a4400b1180d0100410010b0140c1c041c07440710500c140c50110315144c8142c02e00075a410380c0c081080455000300410411409580c295100392600000030364015039880c2044421128040c0040d0403030100000d05c100196419030100e41610b900710f90070701c03090700e6910102059020387d2580005e000d000f000400c6c002440c0f9401082a540702411005036190307606a034004664000307604c40742c1c0040c104401c40c01c0103030511841a00400030341d1201e13101829610340f009500710080030058101d501c0d40214050121050964803101801803c17203030b070340001d000007103403109425000c1030062410a0000c1064507203420310503041c14018040950b910315 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 14660852 1250 14659602 14659609
    0x9010b04050f040e060a060806070203070c090506010203091002011401050411030a0504050c0d140706140a0503060402071509110f060a0503041b0303050c0609072d050a06030b0a0e010303020a02 85
    0x2000102c40c0d10a42d0742c3d5071100b0200c02030101c5803150000e581d0004456150826550a040b801004082190420043d08000800510500c400d0740d12103800018144d2321400143e203103102e040340ca9903001d1a9101c4100b00301c2e505412a10402086020710709040c1d0781d0b03d040c082551405951503110b1082070000801c00300302d40d848a13134004e0103030303003100e440304031400209101301000d02d02541d11002000d4042e000c410b007000220014038192501000703410320010707031000c640102e4044108001000010800a50740da0701130b150195001841003403140440000d0f54002d041280d01240c10f0300b90411800c90310308d052042d2000c2e03241c1c0945054600f002c600c4080307034954001001242c0c504540c0482200d40c400c0c0c01709c2003001d11700ca03807520781d0b0b80c45580c44080d28142c1c004101a80030b5000c0442400b03240c2007048024500362014510390b200441040f468500300c0705507046960803503d0071000003000c40e8950800b4190308416180d101c2c0790364a0780c004217680c0c142400007030050380c84681408018107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 14662102 1250 14660852 14660869
    0x190501052110060f050301060b0f160c15050a0206070c080a0e0406030507090506011103030601020a0809011106090102030601090501030b09010b0c10060803071e03080703050a0608010501090903090509010b0405 92
    0x40c450070079168400e034060303001c0c030840301d40c2d40200d150851001014411401c00b4810003010309424004181048001640c02c0181d101d03004a4401110b10b04000804000050309402c010780024488041d0055100c0c40007000d41d04402d80000052041d0310114005600500d0303401a502d80006416103010900740c000d9510895601d000b542056a414001001c501d00b84050009481320000c082410b0a10800040403045500c0d40c0b40d020f0f0b0410800e00c100c90f030700000c2000c0410382c488401a100ca40034401641c2c251010311142400c0d020b600100410f00c5810b40c01584651000d807242a0b6142c1c82d54011000c03111000002508503103801c00501c41805400090212405860112080c9084c3e52083e4400d845990740705039619800803801e00204030004510445111098103035401c100c81e140c500074074003400500302c0c10a240cbc0d9079000c65407a400359080b20f8050505d02000b1300ca2075954040d4000102200d607010f800082c444071002c2600c1c030300000002d040340c100d46d0103503003010706003000c0004a2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 14663352 1250 14662102 14662159
    0xb030c0d060308070506070503100905040201031e060612110301120203010b030f030a080c03070e0108060120030405030d080603071802090d081b0c01020d030b0301060305070e19050105 81
    0x158051240311010000340c00344a028510410304161038000300e180c040c0c41d00030080d03c90801e11005008000b500b1582c0c3e2441400c50f4a084008112034031203000580c01022100905001652401c520015134803c64200008845042d034074408001f5403200701401301d039001d100f00c9410980420040050402594541210038002000010080c50742e0000a250000070003d14036541c10100e404514640c2141c08107501c628290f0001e072661608130001054080240da10505200e010404601c007648070740740c031195550612008206018400010301ea503900035100300c610078031030b18401002c01c52286070554000c0c05c01400403c0c1090900c40c62003030701e6180c0b02101c80981c1d400d0017440341d0f507501c100040030510f006450455491290f00d40c9030946a01042d91800309038030013803045250b40d170b001843d420303c00100d00d0009220045440042d002d4413403644064000d1140710380c0412140c0d48124114042c00442c0701c200c80a18118800b10199071091141c140d00046010707040070044401030703000440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 14664602 1250 14663352 14663371
    0x21203090603010e0106030b060a0801120c05030709020d050901020903060402100203190806010e040b090a091a07200106080a03141611040b010806060d0b0d050a11010305060909070b03 81
    0x108408030380400c0541d00700364020112030000c2c400410070103402d4410040303400c0040e90001d282c40002c20000e0035001b170600c81d4803207000c5260340700c030244400c10720b43c4005882e0040590341d40c19926020032000c1e402080b0810a91803602d000310b03460350814421905058009405010070f681e96408200d1400c0d5454030080650100300309204000e6400b00b294002c01005495501c898280a000100148185000c4900440c9490b903080070740da4a84811075030020b640c900109520b002440d017442d10010b03254000d00344107580420300400b50707000b0290031000c403003009101404148031808207081c0c4546100308105500440d4000d00480d00c68000080c00c00480801c041c6800360b40340d802030300881e601005940d00444100481e6141c40d1a00582499200c01d1901c84042d0410b41d00180880c03003404902d86034150348501c51207450700d03a0b400c8040926040400d80d01c801880382000b0300c401d03c0c2d40d42d2a6000914000000d01d0519085a0040c0201a240010300c2c0081c2000011800b41e400a40417029 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 14665852 1250 14664602 14664607
    0x602090312040801060609080a05062205010905010501031a0705040302010507020d050a0506010501080c0a0203040b0a18090b040c0c11091005060703021b0f030d030203040606030c0311030606010318021203 90
    0x241001918024401083c51500004d1000e1900c003008000c00034641003410b880d000707041c100740425400a101c036044155000112808003411007205c0038403006500007800c65003480c0380c10051040640c080340c1228080d400000c01d0050312000750420030000c54038800401c00900c4240095441040135008091018007101007146070360326250b2401003c1602110bc95100c0f01c01407049503440b00c10542c028010152103810610481400303900c80c0200d01601e01e40700408a41100347c5881007110500008580394110700c2c403510360841002034103001440758025420841114100340c0f03d000300340000e50b08010019480340280c0100850404054116030541040a4010035565100d4008198652194004191612450404800d07007035030301030001d00c00c00c4080c0e26800346d1b40300400c0040c0358400c14580180d8030303541d615020300100066000904040c00f03042d008400c0000004a0011f890b1044007110f82c2540c030700f40110b00342c1d000c03941044440c01e00c1080210050400400c0d40b07540e9602d000c1544e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 14667102 1250 14665852 14665873
    0x6030406020702040f110901020d080603070302060c070b0f0309070f0609050108060d080c030c010b0a03030504051011010c050a030b04090c05100509100f080c040303050a0e0d0606030b010801060b0702030a06020903 94
    0x41600c0d9046c0e12882403074000030fa82d114035030301044408495992030510180b43d1601c080042e848210500c006402510001541c04070b40109120082c0540118520307942c5074205610040c2c0e1642046810b0844e51140c9400031401c03c92044002045400580d68203520f24103000045907100805491160440c881400715000208004081c00c0c00e00340712002141c4074101c42e00d00301e01307440e00e81310f0031402402c882d802440070030f034800d0450342030700c4041e00d12104904049000b00c40b682ca820354040025442c10f0394411011b03a001d0020300e03000000d6641404903480d50400c00c8102c910141008020a54200b002c0019050064452011420342c0c00c1050074801481c1c0454208401804c1c0c000c002032104022100c0e490704000201d40204a00d004c1030b09117030660340d000d0014441e08021105100c91001c00390b9180e0340c0e8118603100181d01c1501880318035528a0103105410080c05401e40e01d508049000c0b4401c0221001d440c40c031030b0000c004101c04541a26490001d500000140d6058007480d40718a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 14668352 1250 14667102 14667131
    0x16020c090103081806030105090601030c0c14150106111c02010b060d090512390f06040c0611070302040b060906180405070e0102030304110109120b010819020603040602070204 77
    0x360082d40540707402a070b518502c01c2c5020030070240182c401d114110a000501c0b00d5114901c802c0e5008100b800c0002d02851111400c2d030340f010001000408045900b9010070740c01d480411121643c503140b02100c03005980382c03042510350700042c884041c02e690140809c150207104540400c212020035000010708201c0140200784a03621a00c1c0c5c40d00100d4071006250100441085030903a0b10036400d0301c160400c0150f032000403000c80b1000400c080c40c0900c5c1c032200b031100525000e00e1345124080007140c10300518580c00b2074aa450444050354108042e00b00001d00500528030104c060007070300003400d0306a055500304001070035101da213940c0180d000d00c813084a5440d9040140b06080004502000541e550000c100a41d0703001400142007100c80d120741c245698002080e650032550003100c0b0404540084012101003016a03c40c106081c80c0070209814003009901e2181602c504a081c0c50000c003035000d2a00d5a42200c0100942040c0d04000107404030340650b01038600b0f1440240003080000003907501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 14669602 1250 14668352 14668369
    0x402040b0d1d070e010603020c01020d05090c100e1302030c0c0a05030d06050d1509050a0213060816030203150a0f0204031103010506010e030721050102030429010e16020c 75
    0x1002406030b580e40715a100c803107615845100d0b80089401810481d04001101e4154981846040c041c5900800c481c0307518032080d019038500032200d007030800591904100d25507840c1442800540215541c0017060a020302c911089884104041c2440062000707043d5004003d6200500311070034038a0501c440c0c07c421030f060190040345030140c070085440700740d440d01500441e0051742c441e5105046004440c000039424103d0008002c483c2d100c001080025824020f00f00540410003d601c1301c0e500070401e003108210f610840943d1145000c40d00403c4281c490169200290300000e51f042d40500f000b0400d000c1d0007003016501080140c40803450070750701480302d0140d030440e0304116500c46268400e009903040074400d01e03600010928000c0a556000808a6111300e1907004120f800303091704103600803011210080e5205c1ea1350141c021556441d2904001c950120889490761444441d0102e03100c1d9242110f10300b9041e80c0b20780c0c1c003207501a1907101c81c00c085598030207424401e5005022043c126956007408 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 14670852 1250 14669602 14669617
    0x30209040b0601080a0b0f040b041b08010810020708090d170d1d0c0d02040203060103020f040e0103050123070e01120905010c0810030305040504090305040e090c040f0506030a020904020402040b 85
    0x50101e890400e03a0015140d20070040c80301030081c1c0f8001d007005c01d503035a40411742d85107003041d2130019030b400c10701c80820054101c80031000040a07041c071089028950000042e81215580e80c281c9142c0e041c2055010300341e00c6540c1c4041d06418003408101701500e0000301e01050544620751540031380078100c3ca920b5494003d1544080c0700355075400e560141c911001308118403c240c1602901510440788009070002c030b403081c40a8003c5a0200000342141d0082e0704480c0c05000c26900d0342d880e259142c0d428900305070240812211542014010030496100071465400810182e820302415035890f0300899034102030316240b5040000782a40c02000c4841d038403c50641500034400444e840c00598005049a030300034143c126030ac007031058100040382c4d0010944042c1c40d421078000c6480380c0c4030b040449403030080d60041e12034181c4003014400c07040c0300000c00d55501a400d40c3c083c0804580b080000040b20403c80d03130030341c040d0022b20401c8010716002112035802031006000506150b15824404829086910f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 14672102 1250 14670852 14670863
    0xa09050f010506010306050a050102100e0106050604141002010603031707021e03031602030c030a0e1f0f08070804350c07060206060a08030a050c010603050d0c0201031a0102120a0903020904 83
    0x90603c821540e042c0507050161000741c0700c01040ca450400000e6841038070182c40440700340e6411003801704a10a4001e10001d0400400140e151511441d21310710100c1c6240c601c602c0f80d81c111007264017460041c0554011030f82c06031124000c460741d104118880140040502d0704500a16070302152000030341c10008003543d8080021038032440c1c000000000300d500c5c01c0f032101c00d42d8418440344483e23950000864036a5404d910b0011501c400d51000b15449800750305804450620304044100788560050301c0d100400301560382c2900b0f0340c849420581e1440d8042c2c4001d407e224400d10454401000842e09109036100340c44100e615070f00802d0445041d030030140303070f08141e600103030002c0000c40e60410420350024011100101d1852400100aa480c8038409030501800b101090b044d001a4082d4003510080d03401c901078401140c10800c0042100500e45000c0380030030320301180e082c14140d0684240c40b2410701070f0002d00c9040c80e44020110150020040d6004010b80350b0000310040e1500c0f0215400340f80b090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 14673352 1250 14672102 14672111
    0xc030203090d0b0906060d051207021804060e07060905010905010516060501030503040f06020f0a020d080705030408010b0a090207050d080c0f07081b0d020c0603100806070206060a090e0c090a09050f01 88
    0xd184503030400e17801905092048004000309400716801180c032018956040042c29501e9400f4400300e09003030b41007542c45880448206c01c20090180f075070000c01804084000b9201a59120341098400c02c2250003101c2c001423161030144910350084c8024020b4801c5810354004050315652501c056900c00d8204407480d400206041001d080f180308504090481c50000c3c11189290081056850064030380c06807081e90403610360740a0003110000c9440458108c3d003902d40d25521005520f01a003071030441c803405403242c10b000141c45c020f14402d0340c0046520a028200350003003e00111202d9401416044010340104030013000c051040000300740c00d030f10404c4c40075168244160040c58071490200113001d83d4210301c4110035032990200c0e9200307840404640c50b50703c9488040c585032180f03400b40c101c56550311a081c14460755940000b001071044004130380300d19000b929907641609440e05140419040e612940d503400852502511720f030390000c00013000041f51501601c0c0d00d80341501c6520001c0380769656 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 14674602 1250 14673352 14673361
    0x513050601050406060507080f0f190206070f08041101030608070603050a140408120411040e010e25050607050c0402040e01030b0a051308090a050a0605040602010e0f0703030c030203090d0b 83
    0x1030095500601e0202d41c1001654500072000c1c21911500c03000500201000510004c04100402030700d5102c0340d403518245d00c03180c0d44008083e08071070700403414002d44528000600c42030711a21080c2e040090603940e01c0125103130b41d83c132811041400c100b050305054450002280840b02008144010400d65a003c1034a0900c01050402c460540c074040340c52080342070410020440c140d00319003028038618041c01d00c990303950820149102d0005d040507840744c1845540d081c2030405402041e14100602d0a0b54050032040754141b02c0d18480310346007280100c940703004000d1031400c0f00c0500017840c000e80684682031740325400141240d006420a41030406608014018442141540340d03120103c00e004004a04110f00440d4120390361490040c0001e1002a42003855124455104000e01c000ba001c1186952a200042c103607400034003400c40190703c0d10b071044601c003c0006007001c0e030b03204820180c566542540c40031280882401c0c0300b9820f40c80100710072500350301c4144c203150880c0d0103604065080d090 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 14675852 1250 14674602 14674613
    0x30910060e040c030b130c0306021b06070906180801021207021b0102031606140c03011409060d0215040f06050a090504020903100b0d0204090f0203060601090803070807150513 77
    0x1560007100c0407040c10000c01c8000707540a800d00081d85d0f04003101c0c406075543c841c400440748010240c014201c820a100010401c0200c1d00038014107014100701c000b010010071507a5544038030803920b140010b0f18180c41000f603103020709880300b880f07007001c802c0c441e8940d100c100d041c0c2660300c0300045a000190380420044415030610108400700c420140d080914080d40c40001d40e21b00420400515044591410f0303002c004550340702080e0286411000c0c0c0152a0170001030a140d0801d108000d414990984020341e107203002501e8602c00d940040a442005031a6001c0c043c03407500901c85c203000030b08204404203e110080000b44024940355035400e5035254402001040c1c821a070780501c0c000c0d40140082c801580d00030400301c244004181001130990040000102114403202010f9085450035203c0c0341030001c070405180b00d15000740c003250035503110600111002c10310b520554016400c140f00c0307540000d014000400255009410010302d05000204c92400c655094803041282442641d90340308214 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 14677102 1250 14675852 14675861
    0x90f030e01020607080a0c090302040f050403020d030207050a06020904020f070f0507061d040c021906050103110904020306010b0a09030b010605070204050a05010503120912010501060818010b100f030908030910 92
    0xc2c800b929583c101410054089a0044c040a04507500c82d01d00c120b41c58440c4c107420b4003d40c1c0040050100301c0b062031281c001014107a07015001801000c125010380c500034001c95212039802001000d0070700490f200d4400035042502e400f82c1c0309408000301c040b101c1d01c10000d0400203000c2c004040c07001c2450710f84a031800d2203a40c45603061222028000d01c00c1304440d1683c90524509803004030700b038400c1c980c049040000c1c01d000c55115002405458090004951000d030590b80308140f900c00d001078034020402040d1045074001d606520480050040540c1c903006040c0e025a1420001503980c1c0344d98a01000070001d800020024901044103015441c3c1801256080031449500b0810340d414600466116241140000312102001a0220041c2c440954105029000c50002c00807541c403000001c02d015010f80e00305120210410001020000610480c03240c020001c3c944142e03034400c60404d44040c5c501c800a10309040d0368401100101c1c44400c001d62190009101410114075007003840070444 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 14678352 1250 14677102 14677127
    0x31407060e010c0b01050f0a09020a0306090e010b0303040b0a0905060415080a090c1505040902030a090c08010203060a0302010e060909090d030608060108150405101b08060d0b160306030501090f03 86
    0x20104100f090301181800248a0643d0780c15100a040c80d5042e101092113030490b98402c0030164030010340980c07560352581c4818181c612541040c803107075428500f8582610101036055a058004100c100810341c02a0010003d2202c10300b004403429035104006407564000391701c03621284900d200c10802c0d080d80050715540c440c03068402003001820030b840da0031140e1014000c00d00c05171041c0c0050801ca40c050001c1d5801454601029541c030315000348030401400e40304404032001c840d00840845d441c0d034103000341da2040d40046d080780c00342c43c42c6400440d00c40040011300c942000c02000085108c0e01c2e04500540310b84640c000904440745001320090817244e1a90020245800030001880250004100c0502c64040620584440d48490030010b003056000b003c19100c4a18000700420505c0b001c1004011035174994845502035654a82032040324410050000d0011031407000044401600c01620700602d580343ca0009480c07503c9543d01070031602003010560b00c049595070308004060b8071401c0d03000132 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 14679602 1250 14678352 14678357
    0x3020306150313020f01030908160512040b030a090f050a1b05030a02010923030f060603100203010b031603060503150604050106090501050708090102120307180503070b1602030106031407060e01 85
    0x31450401c0c40420f1544546000074414850384e02601c041c0ea100341c001544e1650002c10a65441c440c0c980110400c0700300200c00c40e01070299410102c06102440c061314101c032907001c40705181d40d560b0b0235050001c141c1d110342110a500d2600c1a0004140b0401109006d6031040d2406041c1c40d1007030489110200081e44903500c0b9512625034000183da218608504540300c0304020f80300240780700103c001c80c084803010244c240c481d820241d0551000019400c1c01000c040d025a252034032086c000b54260300c001d00540c00d40600410104400000002e0801c4c03035000c1c03514000030f8240c3c44d032002a0400e101c428070b2600905002041c0440351405d0711680703004002c0c504159800502d007c002900b14051804058620903001c01c0ca00840c0c1d0082c03010601d690541c0030030580d00c0c64011000f0707104442c4140102c0c410030104001282074100021101c054036143d900807400c02c4070580300d030030100b400c41c0350480c3c142d520b400f0000000380c02e842d4801501001000038025141c03c0480c0248a080e550001504 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 14680852 1250 14679602 14679607
    0x70506041d0a0e010c050403030807030203040f02120a0b0702010605041407020c12010204030c06050a0f0309020906120102040806011203020d14180f0d080c1203010f0b03090f030a0302030615 84
    0x104486480852001c05000019026995009007800c01010120000c1c032055080090040303645034400f00800aa82c030036110001d858481e10b4049003240800c07031700104500c00c540000400340c0781900b80040600e460004480508503641d0307403054030f21320030740b248070140c0c0d15240140028903007401030035118a6000d070103440710302d4110740003075540c800900224001d4880030402040c00e00290104c0d0b003d50b810989040c4101d585030310050a580c8041000000240d06544140045100f8091504c043d50000d0104230582c0f500c500304000b039540c031822041c00b990b0030440080c03804402c0c80014002c00744000170100960342800c001e070608490307003003110801000720800302068403160b080d10100d14240d801070190310490000b140c50f0104401c103440d40401d481f803502c0c003004503e2004003000402e41e4291010603031030f404030400c00e01013802030402030708145d0028048100c40e1030146a100000380d04a9117010070440002d82154418110100001d40000400980781082c13a407a102d0a0a204c40341071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 14682102 1250 14680852 14680859
    0x120809100509190302030d0c020607030608010e0c0f01050912030a030c080f0705070807021801030c080a05100e0c150403170712030b0102010f0e01050901060503060412030b180408090307050604 85
    0xa8481e90f01c104240f80503c081e00d50fa10603d4800c2041d50103502c0c1c4201c00b0040e0a00c010070103035544100310358680009044c80d4010030319103018010b4a160380b4200c4000d00d47d207011a81001040318150380000c0c100501440a07804580c2d6005c0314001d13a01d090781c0a155510450440181980c034403840b071100344504001806140212088c246503c0415464480c3c0c85103240d203024001c03803154110195004a400001b440050b090300080e034120781c400c40000c0c52090303a582005455070802440607000d9084910040062111078100001c0c0504587c11790703400c0440c40340081d13440410000070014103840400e0074001c022022019020720a00d4448050504107160344841c0b0032642000e8180c10580ca4000319a03980e4000d400a078040c00e030448040c4003000c001d00310b880c020130701241c6c0d10041e50b0900c2c1c03001500d0b043c0452450b005942003200741b041038003030b684140c001c0c00b402c07800550010f01300151365103c0001c4aa400380a036200d070311899074a4004004152504030140c000500c986000c02c0b040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 14683352 1250 14682102 14682121
    0xb09010503070e0406090803010905090106060f0c0f020406050406080607020c010212040306090c051c060b06030c03010b16060212040203060601020c011e0201020412060203060a060e0a03030302090d1208091005 92
    0xc045449400c41448255540e1038900302406e2a0030700100b00d50030100006c21102119004540301e144103a00030040a075441d101181d496103440321034004030300d0f00034008010602c400c5000c0c000b9030014101040319990fa00102d01184c00540c0300030f541e90014401d00101950500524160b80024402003409207400a2126090b216510000f42444e035603090342010032105242410040600418050000c0200b40e038030441000140d00c201c0d5a02d25140444585140c043e0949000701d03608011142960308081c40740f5020f61040e41c031400f400c601c0d00d0340d8100040c1240010f2078058251422a02141024814540780003130243c40039065400504502e00d040e60f102408200c0340460a140700181501103200382d00a03c0365800400d407610001e42800c0901130b0540065004040c16a400740c0241e03a10b5004540000c040b0080650003003000c102080071074800c0d000341c2007400380105a0a00d1078099a144140403008400c528041060401004001901480456421040528180440d10300600390 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 14684602 1250 14683352 14683363
    0x131d0f0f070210050405070504140112020420040b0d05010909051507090512010c08060a03030c0204090206040902070609060b030109080924030103030201060509010501030605030d08070e0a060804060b09010503 92
    0x403211648098000500101d208002040b504510820108050b080c14141b290f107410b1507000340c034051810003903d0141e00112104590407100e00e02c41d0320950b008d42e0b60030807000e403c40c0c0c0800304a5240760580d07002c014071008000c00c020460014a0303586e4014503001c180550b10168401c2603810701c1d00c082c400100d40041031a10100c11407144240041d82c0d2000701756280b11180d00100e8101c0d00204600c2002d030015400369800501e40d4680c0b26043d0303184001c01400002c0d034000240080c48612412005007040d0304005001480109964102501c481c0701d1000c0360491101a5030b50381c5c072842c424090288901c11400da45909030000e00c0340009940319a400b0b80700d1890340d14058400102030320001e10070724403001e02c11400c410720309680b540e4a0500a000e030140e40102485420344100001e110748c06807103542c00707c81c0040d01400f40090100402d0320103400080501d000c7c81103c00380c0310810b0f9103110445010b010b42e52109011810182041802c9404000000d4002c002d0000140300c2e584d0000780 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 14685852 1250 14684602 14684611
    0x20903030d0f0e030c0f060a050702210d0e010f140c2a0105040c080f150a0e0c030708150c03040b01150203070503040f06110106030314071403131d0f 66
    0x300440d08401050056004124841c3c00c0b8006004c0070036119080000411500d869419510854903592101001c000481d00c06403611405a4003c2c403000903550020814480c00400e0a030740e29044c0a50b400080b81558040140a415079550760241a02c106052090324200c005030003c1c00e190b40781c0a58460740074856103500020018034a05403070f1228850400b031710f10042c60000240031900701494103200d1080203001c0c02c0c09078000c00c2440d8000c140000b440d18020710fa01608080303a40c450300e071603500030039103d150003d06003d66455106203071020000fa000a00d0001c0c01024024911089403940080103441d4200543e81042400701196000090314151420701c4034a01501c1c00320744040c1d203180f06010000b0300ea80404900003c00004e0350394158112286038550002104030281d80030b08a0b02c05000040200b05c0e05041c10180c50f020001034600e0911510310521123043c1445190b1454001c0c01d206a0315900e40744050001300c4441502450b080100b0031001040d05000e605950716880052 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 14687102 1250 14685852 14685877
    0x718090501060302031203010810020a0804030f030b030f071a0301050f060c070306050405030901090e0402010c0b1003050f010c03110703081b0409050f041709010c080a050403080f0307030f02090303 87
    0x840002400300a41c0031000565001703044a41900c2803211100d100d400901c01e00c1c0c10343c048c01d84c02e510340c10300303170300031500d21410307a68440c040350359180c1c3d09a694007000701c002d10070160384489103181605d0030804030412040c0c9034024810310717240c5014000c0040b03130200007511105051004110f142c036811910915644100caa95840b81030804420f403802c9071540c00900400d00745130602062000210050038818800e17a128001e047d181c8000340c1c0c3c1074800750b13002400512616490700114000040b505d030044080740080d004640d0701c0e1900c51828134071078004591650350384c603003d0920390144200350751103201c1100681081c1c0d03103450103030094400030316a12020382503410a0750089031001c101c0303010b00103940041200307040041c2078180105048900701d5074643c00301405030441c030790402551310b540e805031744564200c0d26075a00c544003900408450014443c05220200018424802810300b03c80d0ba00946a1a40f400d820002d096624020804906078410414081241c402004448002c00c0c0301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 14688352 1250 14687102 14687111
    0xa0605060420120c0906030a020702032a040b041d070807050f010f03021305060a0302071a011505090d050a03022107030f030b0307050910090e0d0503040210030212010308030103050607020718 84
    0x3914000b1003842642549680900c00000f0002e0700d100d2399001e451654000c1d400c85000c002c640048651204008a54141c0c007002200107812600c1e0640114084403030250011903d0005481001842c40e03c0e101010b065400c00c140134030000400304039000c0100011a11001c030b04a8003000a004909914400010150001240002ea4100d0b100c15001410007801c00c07690390303d070450b00034002d4004010494400003102ca600b0040e08802554505031104005100403250203206d099800d5400b040b00aa00714803c1032404002c65000c1c0688200e050281d0050034020f51400000c41151803500306140000c81e05001c031801081c2e11a803048030269007401c0c002154102a000a46800d020b80e000b99072000d00e00f400c1114000c540f2075940100d414441051007603015854003182c035054040c1c102c0e00090000c1c0300043c094038003c0c0e0684400340b0681401868541c0703941900f82286400d802c1a00ca0041c00401001001010054507500c03403260b00c050081da40c180480410f03181d000351103000999484 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 14689602 1250 14688352 14688361
    0x81b090915071d090103080406030e07050609040e0c1507030210020705070501030b06070204050a0b01020c06070210050306060403060203040f030806040212040308102301020f0a0803010e13050a060506042012 91
    0x181041243c550000030b0043e645503a407440d00c42e016a020b0300842c070000e03041c10b4852086c1d80b030005210094440041030b4509121011302440b0080000310350700c55030780c440c1c070240070751584480c0c0d1034205030390042017091350310f100070b090207841c00b410220184507041c0304004e4000416004200801650340919012038001108c40004290b40100388004c0d41c0540380078180582c8495903400403051000a0b0251140e200108041000f0743c040c03840040e4010b60009800d512440c8103078002c5070300100041c525070416441ea10744000720b0300202c0341141d0600800601c101455002101c590340414116000d510305802681c003c01171b51806003004044c80010303004201640c00d49446c1901a0190781c00340e1000c6500243c3c2c0c0c03c109018001a1400750050321141c2480890204d000a0301039000100310345940d28000301c402c00c5000c01050030ad00c5440700100700001074014403108030a60701405020800741482c070208400c6404090500309040c100d44c80d107640d0304007600166008020300c1e0006103442d548 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 14690852 1250 14689602 14689637
    0x40f050105280309081303110a0303021209030a0c060c06060e01030f0213020c010c0819020403030801060e040f0204090b0906090603070e040816030c1401140a090c081b09091507 78
    0x61095008041300d42c003046c1c0030310000c0071024180c2240d01030420150780b07110120a01000b2003031408041c0041c1c011107100f034010014580180340c40794015044070107801c0030b51144001c0851942042c00010f525a80090520240340503c030301030000c50421000b99451962105001d00102c803009004030514642010040c005506071490805900000e0143d030b0400e440090a12a08840420030060040d1180c004900d95200f0788090782d506454980b07850742001070603034400c4c000300e8106038043c1d203859403142003411a0020b40024203138000c003c03030100b400c030f810403811580040042d0f018a11540400046030b03400185101156501008000070b87c03210304000303110380305560b0030020190705000e6003410181e03c00d000b001b0140c064071070041d80c00228480b07103081e6200620911340c500a040c0c0421040d03815540a2030382588680c01e000030030b640d5200d0f43c0307091060300c2001440800d1052071145032070410035903840e4001b20207000f80c140104205150f0b9102000601480c0404c048201da80d415200c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 14692102 1250 14690852 14690861
    0xa1503030c020d060219090e04020105090108190204030303050105040507020a0b010b0a120606090302120a120503090a0606080106081203090d0c0206070c180c02060403020a080c10060b040f0501052803 88
    0x240c0207001035580360f51000b040355104507206d14030000603110703c00c00a030288070b0102842c0280d030f050f500d152600340000c004540080b0050501d4400b00510014002984102d200a100451003518049021362400b4100811280d00800354815034200e41855000a2180a54281907440403881c05482d81c80c1e03400304403801c1c200016030380861403520101044070f0740c200c40030b001160b10803580f2020004407111a6a180c0d0b0b103c00f00141801d590310820b0081501800c0039551101c00c0303500311103103030200361982c40c26200c7c507030720601450b59114400e100c241024010380340041e000c51200303455410100342d402d5030382203100a100b00b040102110842156925802c44d82d1854010700c4a9260070303105c403080c0d440109034800c05030702c15241581054a42c0c0c0046a281d2040e900354018100264030744e227540c00c10368015803505000e070054108d182c800307035402e00ca000080c1000ba4000d07501c690800c03004085c5240c0c540c103c0c17814400d0510003000c0101010052481758540203889200c424440b150560160 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 14693352 1250 14692102 14692129
    0x611010207060608030904060b0c0d0305060f0d110f10050d02090604051002070608010509091510120312050114030303040f030c02100507110402040602150405070b12040b0a1503030c02 81
    0x641050310004e4180000405880c0c0340c241245c0400400790340b1130540590303124036800e0468a401000e00b12461074002d6003c0c5030301c05000303403032442c200c044c410003d80c1a40d840d501c202c80c00b02c1d10243e50075080c1131100007119014410744002d02c00c0044550003810a005484207844044c0c1c0028140200c0d48a000548004003130180141c4000d070581c0c031020752205440c3c064080029034960001415160410340300d40694120400b40690341c04c100010102c0b1a0000c09060b90114619000601c11110f600b11141a60084d6140e0003684580121141070300c00603401041005642c080d01007895801004a9403c580d0004488840041614041d03641420310f20001c2d50006100380c07180f541581110040c801c5a00c01c000017858101004100002c81c0540e011f14401648480342e4850549080725105030094000c100b1a8141561580c140c00d040d4800d410300d01d40100c2a0090201300300c2d128407441e4000382c1020007882040030022801c0e00d4458039100241c03c00005241c0282952542183c81c1c005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 14694602 1250 14693352 14693363
    0x70314030403080705060f0a020906091903080f09030c0a0f05010503041401060e09010b1906030207080408030c0c0117060609060711120c010e0103020f030c03040221010c03060b090306010611010207 87
    0x204e02050800a8840e10200d465001c0038102d2000039000100e517100f05e8040c0e000c010199410060360501b07001b014014800c40f41c0d8128000f04001c00410038030000303449070311700240415a40b0f003004002d040c141411044014000c501ca45801d0020340b044649150a442081c42c040342c480c2d413642002020681c03503e4110313080d0f5280c0340d030118001012150080c40358448900030b101407281c107030903c020050184801400d0350810300044c4280d80c42078000780440c074001c0c0c00f0b0504003034443c15010305681c841210a00c40c1c0e440b4844801c0326513040074590124800d4559444814603103070001c100c0361301c03c0c0450f90780301e000b0014000c0104a60f00101c8080e00c840501a8980034a240d014203640d4402042803a001c5064903014101e035612a0080b1740d008902000010706540724012402129080513100300da21118100032601d0394101d03000c030b00b00025590340011a4401d400348000e001c445a94114140f0100c1c1040405080d0300c0000d11141155450328049040354001c02405009002e4072400400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 14695852 1250 14694602 14694607
    0x30603160801090b0610080705090609060f03181603150f090c060305160c02040902010e0303030403030906051506180a050a060305040c080303070c0303020307170c0307020105070e010207031403040308 88
    0x54074101544101e2903075100d0380450089855032002c1143d03081d800640e02d00000d0a040010328240d1003031000d40401540070b007060b410001d2840c00940300340c0010b0850016001e020040003083e180030408e00c592081c806024041160200010419040c400d00000c1c00c04000c1d200340403101d100343c1e400300b807411300d41100400040f209413514108440c420300c241070002c1e0034074000c02d04840380300d54044941c0d20540c03100c40c01b450003035080c0030142c910036601760b0611100d50740041d5291001d00c01180f050b8406e5400040a41c014a441000c0368000342000c142c1c0c4a1556040d10940c49910480700c0030b0700c412002c4d1040c00c1c1c908001500c0c0d06260f401954002c0483d41002540d160181c00250195100c1c4007001000390b00c13408141d90b640003c44151001859031204040442c1c0240d0040d07400003502d242c0451002101083c2d001400303000c0d900d1094943c0c0000411074180e5080c803445130002c00d18607040740c40a1203d40000e41d5000140400740c000ba19141d1040e500d081c04000300c900456201e8051038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 14697102 1250 14695852 14695859
    0x90e070e09070804050f0610060804060f05070c030207300203070801060801140105030f21130f0608060a030213150e040303020a08090303040507060509010e130b13060506070803060316 81
    0x41c0000401d44045075544034050748086d85400100302584a281c51421008049140c054119500c5a025000b9100d01c0c0da40c0303c01c0e005d03450f0903002e014890b41e41500d0710031001060340381c001e10308507055200c1c440720760414186044a001c103d159504082d0b65200c80c41d0001c80a00000c1d082060075070101005603c5c040000503040c0b8103412211b10040e1000010300e4681ea18800d042d2684106280d480941e084201020700b4001d03080c2422203000c6d00860740382d0601150032062000085130360098940000d22400401c1030303a6101c8030303541d0710074020f4607040c07032503032840d400720b11070704e00c80c0c04009015a190f20388401c0003500b0201c0c407030082c40c540109880c1c50900e8140900207512202c00600010000c00001c4c12100e0008100c0c0c1c007580d070010083c1121031030a4004c580769005446040e04100040701c4841281c2c1c0d0f52844561034240a030000039008003503100300802c0340810b0714020f00030350070000c0400032a42c480e400e80c0c25a5803c0f5840c6992596803800007070420741c02c03032030030295100c4028011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 14698352 1250 14697102 14697107
    0x9150203211e01031703040f0614060406060f0807030c02190c2108070305090a08030a0207080606040b0607020d0f0f110301050c1218070515030610050a090e070e0907 73
    0x141c098030040100d51908642d03512001c80c0050240405040789180c20950f1862000410055034014000d603042a820546540c5d03a409480c52024880e442d62240428800309191511883c0c0003414541410034a029684002420700740c401042c20043c0740d56048030540c01c0c0d000303002d42039503c1103000f03401101180524001d102c0580e070780142c10007445c00200e04813100600f01d054040d03640c1c1040280d8241666a134080780c4613481418407940014005d580000c00300810000303007010900e41d0300986041c41c1000e81185c544100280501e109070300f00b030a009450784528044402d89034054402c1e81c407224141c2000b41300650b4a00380180b00382e03841e04984050003840e514034210468110028080c50300c078a0040c40040c01a03010103180c103521680030400720b800c000d41101201c441842911540d6540301e002030b000102c0040c50030f08070baa0000411440b803034140c1d80004103040c58182a4148043c41e18020711812040c00383c21520f058003400300fa4501d00a808000000d00003c182c900d0501d80742200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 14699602 1250 14698352 14698417
    0x5040801020409020d0b040b010c140a0b0103150b0108100b1e03010f0e0105010507020a090c0e0301020307090906080706090620120c01140105100c0305070804060906090e0709150203 80
    0x5c6041c01d43c80d01e800c0001e0342c40c0c1405030010380041603541e40032205268031030740d0b0300f04545601c0c880680310390084440001d10340c0e4681070086024000c00710f04850581e95440c26649801d8041c0c0c1000302c41003c12690840c0100d040b0162081400d4041e110305c0c0f54a889586146040f90300d000148010000044c0514226840000e40c0c260400c0b4407450b0341d888005558600031048000d6202c885c0400c24850313500a0b03130201260500a14203c0740302074038800446d0880e0b000341c0d0507100044000300c2c00d120b4446a4041c660049c005803000302151450314000912030390603030160008001c240c0c201d006c12103812411080803036804006840340e0b1030300282c00c1c070341c13640c000a2031003415400c080c1348900e44285802c0d40c90403075002030a07840050005c540d08560500c4641c10850900a0500100d00410440c0c1c0c0504045c1c12541c403903502c00d03400c100003e400d10341c19038032039180d108002d41000314036a8000c40300070845000b030404580a8904110603403c3d806210030386500710110707101e12001d10445c1e900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 14700852 1250 14699602 14699617
    0x7030f0b0402010909060e04060207021309030e03070b04050306060d03021c02030706050a05151306271d070519050910090c0e010503060f040603080a02030304020102010b09091c0504080102040902 86
    0x1c0b558007050703035100031005590141c450b4000384891f150014003c82c415070000c20803188020014030802040d90340306c408a8510b140e0541c0000d400003441005400c040201e00d000c0c1121001d03d80c00d0500e484000fa644400090541d8000d610304c80000c0f0406000700920b0009100c0040074145990000340b000390349410070310080e5850f5081c213010070540040740c07044502806800c0280c24a6101d91000d0040c200c030b1702c0c00305a00c1c0640d51400050914003210520b402000718030b14035003040203501d0440b8181c9203d82c1d41a0059841c01d4010843e4010000d020421200e00b5a2801b4001e9030000d1358003178010040d80100c0e0020b190100b000350040c09441d02c0c10641d411240100584241c42c0303001c903100001201c5a40c04140c3c1000410b00501e000c014404030200024401b180e00c944175500c401d0300390401c2c003003400503038800b0080c403003150f03020701131244e19040c2500d1205e0b240c45d00500c490b965482c00c01301404550652004194480d00c5081110003900e0080000e5551b2b694810003940254403142 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 14702102 1250 14700852 14700857
    0x18050402030c0405040305160302100606020c0f04020405061b0316030804021023031f06020303070f030b15030402041104080c090c0406093003200715050702010207030f0b040201 78
    0xc0b0152101e03e81803007a5070046806030307140e90400300c1c90544602d0070030440006500f944180c00e0b040c051070145006100203000181d000d0083e541c41d40090141d000c40c3c89502a2060f0700501051129880340b4054800d183c0e0421070781c031001803070010014150300c18000b195603c503112030391200c00c0c950803106050189100340d503040c1c420b0405a0301282d0f0520400e11121240c0d081c1462941710300c0303400000d582c00c85501c1d124a50794200f10741c0300c5c891001c078940c043c0d00135800200402c00c44903001203100661500034101800301d601c446d00061592210304010014692000c00410299219640201024080f507455140eaa5072500940c41d41c0702c003162003440c82901118005401d0380c43c440269412502c4540b05d0b100f99904120f41c1c00c11411800310304220040100c00f85c7d4080b403400500d910740c03c9000b5107640c00d50075511074003540f00c5400c9001c400101c0d03220f11420031403800000c3c2c658001071080c0c5032032612b0391a9480101c2c00c01c0120b50002d0320414460408006100140100a020341e00c00d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 14703352 1250 14702102 14702113
    0x3050d020111031302030f070609060f0509030d11031614010608010b10080402180a02030601090b070c0501030c110109080306040506090405072105030d05100803160206070503041805040203 83
    0x854040742030321298603800c900b010701400414880c0001d030069461507440201078800302001c00e81094179020b590b0b4410000100c20410801013075800c007282c0340311030603a45482441c0c82030400200340d44000708800c80041110002070134011901c14000e4440052003000198403464a90420f03000c02440e0020004081d4605440001c01c150144076a49280c1400b920889101e11008810f960841c0010070603070b0000c28001ca00c0700e1001c0503045462150005520040e101d0070081c00040840540360070041c1041800c0107080041140d02440908403207003440d001c0307142c2c040d0820450b210710b01030310080025070031f04101d1390030000700b40c002c2d512419083d101040a07603111403c21140742d0043c0c50240145c1c00060003403041c01c413149428243e186040300c00400c040074958405185a00c10005040240c2d80d4000380108150040e1b03c000080150348000c5003403569800428119819056009119050004400c02007080610a41e03008100e0501072840c2c129a0b00409409403c00b1503040f44240100d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 14704602 1250 14703352 14703373
    0xc0501110109020a03020d050a12020a0b0c1617160f05010f0605060301060309080f180102150702030901080a0609020c0d080c0301030f020607030306050a06050403050106080f0c012a0b010305 84
    0x502c94042401c0d001040380d4402480c540920400c15102c0170b017503d45005004510000c2440310300c0000c03d880840d4000d00d200509402c2c03126107a10040d0440c140c8460030895000d0641c1d8411620403425080f40c0c00c8072540808401254403842129a00c40105801581d81320901c15003d10002805001d500280b0505210311900f03c01c580c43e9000b0950b002400b800144002d911950000360824414580e0a01e00250200d01c40e02036004401380007846007039040f00c405c080d641032200c0c400340803080b010001a41401c880181d100d000d5850003604010442c80058801c50482c0c100c03100030140d9590465031201c500e80302585032a0f038084440c0125292101040304403c00c3c1c4110703030489400602400e03240c481030742002000d500460b020340425032204e00c0450542c0c2c441c0d42010081249481d2255102c2c1745142c00c3c2d09645459000e4a940c0d00103003107900081c540820307482d070b0205091070020003a40005100c0a181d241c8803c405c0c22640000503070b070013003101d40760640e41668020022909003086 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 14705852 1250 14704602 14704637
    0xf2101050f010303051e1317010b0405040503030105010e0105071205040501021b0108010315090605010f14010c11010509010507060e03070c230603060303070803040f0b01060c050a0209040804050306040c0501 91
    0x242840020001102040307901c45400f40d5420814681c804032900304d01e45101147c980400e43d503503030000700a464a105c07013071004000c03d10540d03a4202d82035034148403d1a10791a82601ca020502c1928180240c2c611403070805da2040045501c05980700a640d03d80c1c030b0700508004c081c1c0c1c00c0350251501521419800300080da20800c0c10b499603100581d6814202d03030071a52683c1c40c0d00c105d0a001c44110ba201e030b00da0340c0086c0c00c030301559019240c00c480002c0f07254507010341c03414581170031030486060002e8404030002084041014a0b8241020700f021540c40c1049170040300c0318428490042d00c400c1c54140b404040b100d0100003450700780d01680b030490f8001c1d1900554801c1403131700e8000301194000714250b0001c60600001030348e0f112400605403810035801e40c54a40c1243c4c4100c6040301c801803401812000c11404651f100c0c05844d2900d080d040036412660f58541d9403c8200020744200440c1001804010890381100c01070007001d410341d41c0a041c40e00e030592800e40b10307000750b501150210000049000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 14707102 1250 14705852 14705881
    0x309010501030c080303010f23060d0902040b060c0a02090720070302030606010807050a080402030f0727020901051206131a01020d020c150c1207030504030605010501210203060f210105 81
    0x451039042e9108007850034802701c442c444c80c0d0300202c003010080c0f0340f4003c069aa04019105034145d0500c01718100d502c52040004650360714500d140700d50010700c1250940100087d508075940e0f81038a00c4001620b0768141130b50040c00e0602d0b00c0c001c211030381e15080307829840400c40c1c0f822a4820350864400741c6a4000641c0c3d100b00c104c2c1c094002407410300c050b822441c03042003d59045800070381914040c000440d05c203130030445190040100503034045100c00c004c034400c140c1c182200d0040241141452841e02c0001c1161040b060704056a440c010007088483d40da480051200e907214103020000160b081c007100280950b9a095140940500807a985025001145043c52040e005003004034104500c0c410044d250460b0114031f1540c412118207800202c0014010004280281c0f82c0ba51583c3c0b8514140b42074a1050b04800d04010800d041c00702a11399142852420018940c3c3c09070b180d90f500e85c042402e154803121100d40c008040c800c8211800900b698440321003510310001d210350703598504101600c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 14708352 1250 14707102 14707109
    0xb0a08040b0414030c07051201060302030c090403140a0c020f030106030b0c070309090203010806010503070906080309150c06010303050d06050405090d030c02070902030405010c12140a0e07050301020309010501030c08030301 98
    0x1a4a9900080001d0000240381e82e0092007461100c103a03110560345940745821020300501103510030b40043c82207140414040300740b210104002d00c615421540402d031500c1c0342c801381902418551020038209402a001a80c200000c8030104d40c54840b462402030040f030740200c040e4000c8004c851010202d05060048405482d0048101901511901d0403007072940d100d800207404020810b0004904851030b4001940200219401006154140010141041e116078448200546800c2d020170055202100f9646c0d031440072240aaa0701d50700041d404010f20840c04004290700504001204054000014011440f01201c04200e40782c1c540c014001210000c0c0d40c3c00032190321401d5500340c918401c0d00300c1c00800c41e0030f03c1070340d64070303039071003a926042e608140c0d0100c601c0d9465201c03078a20280d2047d856500e513045182c1c24094002c42100030201c07070301d01074020182c098466004500700c100412882d0018140038000319079925002030490300038642804200d03040c090502c0005400c0000100b07581c140c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 14709602 1250 14708352 14708357
    0x70806030c010503060114070506090609160e0a061e031704030809040507021c0e03011103070c02040e01060f1410020a0b220b2d0106050706200f130b0a 67
    0x1407014020054525400c02403a82c1d0400c41540b41c1c803c0043d5004e406400420710800003050301b420502031290410200800c03a034003551203a80250250a80403030b0b008115170a540a01605844c0d010446000e49025080400140d8a0084e4103400e240609042d40c04c99000384041100010f9403121203640d4401e52001902c1101c00344000c03192407616078425a04018640115512886112418440504024510301c0071032804001400303942000c1c0149a0b5055040380710714514031381032102400170054880f000c1d01560b0354a05821211030254810f501914100040d01412a030329030004400912409043c1d0090300481d410407546800010b01c0c401165201c03428090940d1103141d500d90004405503501a07014141c9080c1c4003152100d110140551f100500f800300f00c000a007010880c40ba601d0010102ca403107600d004100d1240c0c0001681c022503400300780490240d15040c00720507928440042d481c0c0f00c4074001542d0420251ba6402007031050084c0d0344160441da40c58200060740e0241d204c05a01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 14710852 1250 14709602 14709613
    0x501030b060f040b010e1905031606020d0f0c030c03020a050322050d020603010b0705010b04110d0515030d0c05010b0306010f05090106020a0c0b07031209110114040503070303030c21050f07080603 86
    0x41c0f914003107447c510084800c0c0c5061038000e68072000a85003d04400c41440d5061540605110095061040d8590008282080300c410500008020b00b0050024006400c10807001441d0040500c24040c9601d041e070428104c5e074503001c00a094043d4206000700100e41d0540080002605050400c4200700740d40e001800c07541140e20b0400710440307541c4541c004981c03c0d540c62641140c1c070313a0b440c03048942482c402c00c0c1d2151200031070110b01049030b1020700340c029403101511601c5074681c0c00280b81205090145016021982c551038030078003502044107030740e901d400791a00209240d40c008030f810044440486001c4e030180d0381c559060b42c0740c00c44910302801001d124070081c800c040141000381003841c480c1c03403c807014882c0c4285031401c480c0e5102c001c8519a07100d8104100c2503a20074204080101c20041992800c0c1c5403200007980d44001c0d120080c18036480ba10031104c0103000c0e02101203c048206000e207030a03000b071510000100b000701c80300010341040d100030801d904c0c42051424840e0001030001c02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 14712102 1250 14710852 14710877
    0x1403060103090206040308030906040c05040509061b04030b09060a140903191b030c05060105100c02100306050604080f010c050a0e0409060204050d050601031a04050604110102030405040501030b060f040b01 90
    0x180a030082d980141e80000c0200000000942c03400021403192801d00050442c6041a1034042d0b110316856008920842c10700080c842c96080100d02207030081141c03900221004e00c0410440220301a42e44054405122842048130300c00001c22800d105000140d020080c116258807146400c400954044105070302c02d106502d4a40700840000203031078a94240400b5900020740316154107070124034103c6c001744012100c14100314042211a0241c801115007482e84040d554009001c21a40d00002c1e20415200d254559418000c1d8001c0001e0107015203016519510b52004c141c4d585c18900700c1d800c40350710744a0101c2c84d2603c034100307456280002d1781c0d4400d9140140780c10400030f80a40340068816640c00c00002905946500c0881c43c10b0f40b00c0c8001e000c1a40c50750811080c1c500309181c0e0504000d051310104800650041b5030264060307403108603004484050750040f455030049401454010b072034200003100348040c039001c1c5403007000c08640a8080542d04018881038841040c1d080340820800000031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 14713352 1250 14712102 14712107
    0x160308030702120c010c090b0a02101d15040317010501050f0c01110d14060604061710030501110414010e030d030b1309030302040e01060c020310020f0c06040303061514030601 77
    0x941e00200544125080e00b040b003d0318107020b50100c05209480d81d03451201011968200ca190740013400b400d000c00c1e0034644441070280d110141d00d41141c030b100d60350304810500c915030f541006404c043c914080701c40380304480301e91010845080c1e8060b0041000303c08440800711801c2c4070f01c1d042c0c40c5d060392014141004404a0480d980149150716015503c40310480c0d0700d85a00c0300a0302c2d409051503004100c2d00301c90400c1c14280900501824094541080144181500500d40c941501217804568600380e60700c004980d071101031600020425401d04507000c40c000000c01c0503006540a03114100344103103402c130041d10f408810307015040d0550046407601c1040f50003a0f22801c1c806d030004d0580e5191011203418003040780c00e40c1d00200c010907400700e420302004e10f03c158114094101818a42042c14407a00020b1761550760004004034681c00045070a01c50302c0716002d90312106294022102141424503015002d00028003401d000c4007262207649000c50b11031840c03055115a041c80461a40d203400004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 14714602 1250 14713352 14713357
    0x30703030203060d050105100504110f0f07020303040305010c030501090606020606030d0305070306031a0702010b03030f040e07090504021305030c0f280503070801050f01060c02011209060f0c030518160308 90
    0x40f03588a050411030002240007806494815100e412500000506000c108030454070740c0c02c048070007900b0501580204a02d00c0c4115441c1030081032109456098030310010f8a584225000280315500302480603032116016000603044e110100000c0c0900d64540f5000c80ea19801240d90a5269020310300c0c4200841c02540301e55080140351802044994484c0c9500041180039035003410128120000c0010050742840b440e140440f044028604d04038080070066824000c40c0116050010080d000c116201d002d05041d030010f1034003030004c3d504d03808800300c43c2017100c074076119280c02030080c0c8903d5a651318001e031741c039208580020209040da842002c11001c000500d190700070841c00410b00c0210705941e04110140c024050103002040a241c02c001010712000103900080900604404a500603038004055a902c2e00c030f503000002d1000c1d001e0511402426100105814003032510648841156243d00807621541d003444444c540061100b034296035950301001d4020b05001c1e85042400060000d000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 14715852 1250 14714602 14714611
    0x17030306040b1f1e02150f07020c0d0503120a02040f0306050c04170d030c020a02010804120c0c060201020c1908030c030c0903060a0603050f060c03010b0714030c0d091205030703030203 81
    0x21400c520412804035083c520019500725020400301c0340c460300322800d94140303422090082c5c40503110016807003410701120f440140004002801c00c400003a2854420002440600e000400781604102142807854583d0300c8842007c40076040702e00020248045070013150110303841991300e070803414035541303922004050141007146409001c110010f0386006d207200c80b40710841d61102900c2c1c020075114000c1c0c2100c400160354425500506660b00142c0c0c4c00500c03040d03000382c101486030002c40d4440802c4601c003141c41c10060403ca8001c002042060341540500030071000340c402c586840c0c003544000e1110b00088003005190590810015404042c4030001d1900850342160443c00d248801000a06000c0c080744d1300d6010559070402002407002c00c03c4035183c001c45403000f400300c50a1491140a0070310050180f41540707000010a001084140e40201e04942e2154003940e46800705000c0382501c950ba2020042c00080c0c504601040d840712a036800b00d2000c1d4020001d42c54844299000c0d00650801070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 14717102 1250 14715852 14715859
    0x3060504060608060907020a080904020a18090c140403050c0d0512040308071109040b0103030e0607080c0607030c14070303110c060405010507030c020a0b0c070c03080d05010f17030306040b 83
    0x400a040d884900039180540b000e074846001c10701d800c10600480600041c000000c41d0301008180c8041270704a021201040c0041d1400744e5500182982641c4540803428140c00c0c03420711210008400c1d4981c0e0000c2c0c02da039181d5440721041e000b900d41100803405103020240140d00455206d07440d503d002c60f96581154032400c240d880c0c0e0750300d4014100b05504240c7c01960100340019025040140d03001940f44d0140044650480d02d04007511080d001030014040182800380c1000e40c00c1481d40c6140c25500074503409010315a8440700b414413541c0f6480c003a030b0083c010900b04070b0032654640c01041000402d011028075541403c03502d07102100078022503484400c90000c10040482482018062076203d2809240085150305000100800b110000f40c00350b000c54110001490008100000a603000525030b10314548521aa0400c0b008103078407a40000c0c80b1a07400240e100e89030340190015030403a0044e0041100090b0380b00400049810f074400c00b00b207940c00070000603416150643c48910001c02c0507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 14718352 1250 14717102 14717111
    0xb030a050601051e120c010807030203070c0f0519110909060702030f130306140405070902160f0614040b0708010b12010509070c0606080c0405010b040501080414010b1c12020f030301050f0103 84
    0x4e5010940f02c00304603030f000140742c1006c00c0182003540c01000369a04101d0234941146546402c02008008100f40e00c0300501004003159801c0c1401010000a0400d95080c03880d40031031800e500d080070b180340480703491500a81da44400140c100c040460700500c90310280d00a10b1030121540c240c43d0b5142d10140321201405a0300f000800420f80603c2800900745d0341c240980d0070760400341005482d0200990011204034010024503a10840800e000d031240e84d408549104c606000346401ca01800c00034049002c49a02c240400c0706000300311803e24041c2e9140d494140321030762100044a02c520070003c0c20641000c603000100b02a040048031564030450a142022607520603507200303c180c0e400f55000b140c1e564400403a00f1454901481013500419140c000c0760300c0e1504d0b10b030018103c1180204050080b13151000300d00c0d50341100790000f04544400500300440c0c007070f00900052411584010966580d028110950201800018540c1034055004001c41c2541e181c80c04000541e1201041c0138101903d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 14719602 1250 14718352 14718409
    0x810030803040311100605060f1606020309060610030b010906140702040501090204090605010e0a05090c040305060703020301150201050f0402090603010608030c0f0c0a030f020402210702060403030b030a05060105 93
    0x303005580510b1003a62003002480700b2040e0645031180082c1c04214031407a09404208035070303032002151600e44110024907203c807032000c1242c661105254002d0729030360000081244041010400b42d01c200c60071a0b40c002d0a0340c400c0c2c412011070f0140c41540b404074041c0c0c807080c060540207482d07520882c05100300356445d0000070340c0441c0c2610300c20303440f5a0351103401150038003c01c05030380600d40c040c00003840c1100405102030005120b41c54a0304c540c0c1d009031020030220350005680c00c00c0b280a1604041103c000f07040c10513009000350f0003486452130030b2460340321660710140b0601810703004071381c8130f12044582c2d1501d40810640d904080c200d030b541596510340c00144800b060010304a44a1b095000e0443c4004204201c0d00348548605101e1003010607202c1400001e2540054020064055800503110981d00f114904000095000d00166060003020001c81560000768644110b00c40c0c0d40500607107550909042d52041c02010040007a04090010702142c00c0016180c42d0b103400307200984813941d45 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 14720852 1250 14719602 14719613
    0x3020d050105011703120a1a0303040f06020c06030402030309010e03031908010302152109010908040305010903140310050f030a02040c0c05060f011401030207050705040c03020702030105090105090d081003 90
    0x1480008940070703511180100440c0c1c4811003a08400c9424001441c9090a2003000805814006003c500e00c08c1d51455401c81d400740d1000e081c0d024610240c100c81d0740d5602d61180401d1034001d80f1600c0c00600c100c280c090501d050070400d60340129030140055007084003400c010b6803041c2d4107903c595010701c418002880da4071094041c20120f02c00b261601520f550450043c44507412000c3c0f02d80668910400c49008a840301d0402d0314480d0041440b641075a032103400e5041d015010441d4058544000498088180801036000d9a84a4481e4888480081960420f140e41b400125000c503a2004c01c080d0070022400d044520b401c3c421001810344101761842e44c0000c0881d2180503001c00003415a02d00d2a080003c10001d49070007451231100a0420741c580404002d203072404c2584641055004030761802042020011540a400d004006004040402e14004c00031741260800364425800e05011070380d864018414580182b41c03c80c007818100380c81c2d02c400e032840c04000c0c02010ba103041a41c40040803c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 14722102 1250 14720852 14720869
    0x803040204090c0b0405040f020304020306010e1509010b09120a12031d070e19020310181506020f120301030803070c021309080702040c301d01020c0f060f0415060302 73
    0xc150f003484c2c0d151420641404100c40076013030500030440c810010720025980c0014018110780d14000d80310290380c1c13060080c515402d0700c420f041e0f0700300711070800100b140003074000540000c2e002500d04d00c0f1003907043c01c1c10702e80e070350000340c80a020041c0e01c6000304e13410b0717110b90803400d0445840075446000058220006142142c5940003040f0f4400600c00d00040f807150740703e4a03090032a012015803c5040044400c40e1940032481410112007408060744100c1550783c0020b0130001502c004102c10310f035280d50107500c400c0c00b00303071141c0b150080103060108203038920181e030305a1790402d42141c25550f48a20a9801c42410b002c2030380d20201c80d800f1600c0243c91402880b00351803113030b8540340d2a07403032a00c1800240d6841c2c40e0084240210b444901d603c2001c0d1400c3d807111440c030351b6100400182e80001c090028501180008051124000d40d8100404150001d12540050301e045904c01c1c1040350076161510000d50b4101c40130302d0ba0070003240225600148680010340c0c080c07000900c180c1d42c1c5d0300141429 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 14723352 1250 14722102 14722109
    0xa031e3b1309030201050f010b030a0209040b060304140706090305060c0306011b050307020a140102060406091401090c080607030c050a030902010212070b0a15140603090c031f1503030c0803040204090c 88
    0x607190142c0104059080c0100c68006100e0901c0880c2541800112001030000800021040d5070200383c1107825130f102d4000580c050301c09002a5500d04080c10b0403071034030f0008000c44810303200b146030010f00b0078450011182101d0700718010b04641d441d800c42412507680007818081c104000c540f1f00b050f07190504d02441c801c02e403007000150703600c02c03076481400b4102205078020103c16160191091041c4d80205030380c0da00960100000440d01d159141092204d80c001039054107540ca00203c1104011418075910140e4218100700d035001c1d951070604400381c40d5503081050000d04140080b400c80f40c003903000114000e1050040e40c44007903940f4401580c640043c9000e90f25850440d091143e2502184204408061380025488a980c20002145c1080450110242c001c00b4000005452164140080040440e0050550b0352401c80c900c034645022414031100d540c1a49000c0c4c1100c5000b410509280c1200d42c16142c40c180c9030400e4840c000380c0d800040050340c005868a58100000d41c82d1003101018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 14724602 1250 14723352 14723389
    0x2030f0304080d090f0605030a05060d050601080a021201050403090b03040f0b0f180c060a050904060e0f040c06020a150c0e0a08100e03070b060f030703050a031e3b 72
    0x706003d400040c04099039038071482011100c00d406100046e489070440b940305104040c003044c1500d0b00404101e29185041d00a405030007000008288020040340304240240200c0f240c43c02e040b041804a4200ca4040d603004000c03641603841008130841c1c010156901c81c0c051550300d12038252a480c1c004e03080300c04480c0c020074078600d00c00700706120b01031058001000d43c0142c001c015032410307030b40441c81134400c0fa0080002c2c45008111100c143d55a5000036020f025810b483c00d04504190500c40b26001c01914100d030f604a120302d010a860344000f4074000240e401074460b082c1250b042e40190300400e13816040b40d003000a010651038150f126810207a0060980100402020200e51114000c6038944c501d1019140c00400c05000272400405c50103030080c9084038035071501d0699400113407401c02c4542c07005001d40100b084800c14140c00c00c148040302c4164207948940400e213444121070308108d6032241d4041b03503110001c140700f030ba61926220420034086500a0044d00e010300008246060140001c0c51 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 14725852 1250 14724602 14724613
    0x212502010b0a08010e0601180f0e0a03030b100e0402030a060302040c020601030501150e0a0b030a0f0b0105040f02040303021f06081504050705040b0d060c0201110705010515010806030a020d02030f030408 89
    0x540e801d0500300b0200810140e0020030400c507159078071a031142018407d954880301b40f004494000000f9034000349038401c403010104809030310310b00d003143c03541d0f119001078010a02e42440f44184e41410301520044404590302d040308c01d04d0260800009400c0070b008441801d94444020005031120b1165254140254004083c00e6240d40384c101d0035141600080002c00c030b92107008024150701e100400342c111202800c0401c2174982da0f0080f82c0b40c88904000031f13000089514036003040c40340c0002201d051b100c01303540078004280c0080b0302c58141e103d14840100140d1001c44180070400300c2d1080c2140f00c0c0031490000c5a0b440d51480214a880c5043c4519244203051a00784000c104080201034000d00b01918148404c400283c0043d0040080301005410b5079280c56440c05494400e45c031003403020340040d92141c2c44180504155000f807030b08a82a6031411030055144696601a1440d00e00c1640f00400800c0760401941c240110a4000f42089030907120305800c0d000400300c1840900050003a041c010b10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 14727102 1250 14725852 14725871
    0x9060611060c13030305070206190c05160b0301140a0b0a0302120105120307021009091104060e01090e0a020c0309060a0e030d08090601031106072001030c030221250201 74
    0x3401c054020b810000101c4040000400001c859003800c01103e030503080c10742d2281514000305006110b909094550780540f22030640d00640c0042074129801d0003141164040c0800f8080180c1190050040081705a1305000400080c0100d150441524402034400d4600070760341c065000b01c0380c124000190201c0e07004510180319170701c038494080c0180021680188012100703029a5141d2040107006800f4000080c1090030042c0a1a01ca100030100000c3c10840b11804410141c0c43c0e421030701a820024003182e80011196200301850340c1559503e6050700d05030b4958107880743c001d62041000081e580000d0103148404d0b5911030241c01c1d0002c040e00c1d41510610520300b0103040800d0895504140710540044c808404000a1070a040d40d5000000d4945100c1210000d945401186030040584100b80e5110004a0320348814240306102a2414070148241520a4040c3c1c05070600090012201c603003102508500004515004010280424583c0c00707038842c0b4968600c400c04d0355001607034448440c0c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 14728352 1250 14727102 14727137
    0x70201020306040b0306040206030a090302030c1209010f030e1b0301110412020306090a0803060103020304031403040309090b0307031e02010311030901020322050c15090a03030e030c041803050a030204090606 91
    0x24013210500301c0250901d0300d030541c00282a0701000d0144a07103a030b039030105034040600800484402d1030a1100b04c891070b51107070100341541c0c4e00400f030703070b50010b132240c5000c02c00c1c90700901a440f106036150010b4401502e00a4001d4141211031017803980c5507403100d020107500260303031000304080c1028001501032a690350040c54070b0705401605051143d44400d40781d402280c01138083d04d4101740300340303000340e40c07512682130449402c4e41c0391080034a00369000051104040d007004001302142d030031403818040041041c1c1003588402c0d0b0b034031002d032080030b40803025200741d0b5000d09020301d044e105041c002070489900d613129065400489101200da0340c00804d0000c0c11096000c0b030140c1030000840c0502e42c41d50b075a2015183c441c40000503000742c907444c401144080410082d11a82000036186262080c0e0740d081c000d05045c00c9500c8a802801030030000c00c882d05003400b640e40c0302d000c4502c03090301c03810503650111000c0d8800007040301055400d000200e0030507550300407c0000c08807942d81d01c51207405405c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 14729602 1250 14728352 14728361
    0x1f1104060207080114040203060103150b090906040b01060306050a0504050c0d02030c0a020c04020702010e0d0302010b100203070b010509040f0b0903130b0304121e050c0c0a08010e06010b2503030e0607020102030604 94
    0x16880081742e11405c110041e81e0004486054079404503007442c0b4812100014006004904032099004024504110340c1060001d00d0b948510302820a00540703982c1d40405130708582c1c050042541090b006042400581040d402541c1c0210030380120740d1408001a0300d880881c1c10542e034240c0c55100014600d240a64108840807207440101c070111304c0c1c034269500290140411010f0b0b14041d0003495114001d0500030751051528010150207010020349001c802900c83e40400001c980501c0610004a400e0030003200e030610a640c0516401e0310109284c40d141109100240004003e01c410001c10f84c00001c01d8104000400200380d41c240c0302c1c1010311305890144400c10038a010003d080040e881c408100302d01880c820700d030500340140d403200d07080f9943d810034000c04103030741d0003892480c4c0c00500718105502c984001301010040d20101d0740c80d2420020a8405e641e116181c402c02001c10440c01100f00034400f015900c2800c00080d2610301100781c0341450301c1118240c0150b540841002160b0906009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 14730852 1250 14729602 14729621
    0x10611010c0504090b03010e0111040f060306031a060a030507181103040309091a060705060901110a0e0f01050409090308010503060a0903020307171c020301030203100501081f11040602070801 84
    0x248150310102030010120300440c03080c1d0007016182c095805179a102913002902441d1008024012200403c0c01c1c2e50307140d84a07100b21485080b90007000100d0a10a11400081d00c2e40017007010b07402203480c02641c00074200900400c2e40035a44620002c00901e0800c0041c004001c401c42c0480c00300e60b401036441c1101c1d60130a1220320800e003041004002680580404165104140005082200b0541c01c2c94034004038540103800841c0000d04006002d00017510303034030404607800240401c03018489a480d56000b000c8921001c42c2c034140900a0310700d840c903d18000b812041c94940c2c102662108418151082180c054020820700c00040c012802c00384085070303112105400a02154845644c000d55078420800054503425510740071035006207080c012a98844d1001c2007c090940482e600310000394828071040740f0900c9210100201c070350041c05018100c940a43c040c1915502c482880f0400b1341a02c0e000c0806160b485d14850701d40100c01028202400c0194024038015003425012802c6451102 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 14732102 1250 14730852 14730887
    0xa0302011d06040609080c010e0709050a27050102070f110f030304060c1106040302030307150506150a0f1806030605120604110d0314030103060903031505030d03020a0e0a0803030106 80
    0x903a41c11081c000800680080c2c3c41800040c0440c00c5050603516405068071a180c1035080814540c04000000380c00b06c16107182d2041003003c0e4407030751000400ca803421209402200001040c4500d1401e034003000200141c05580058940140c5590b604001002100101c61781d000d00b4024014501700b50514041190b0250001c2d8a8241401d602402e5404d080300024228200300c60404c426132a82c1040d10000c55001d8101c2e51140c0d01c03403070111500c07196281c080484503d442c00003601071a01c4400c0301500d124004610385012914607007240c403000d400382040c09000d01102d924a0070a42d0a42c0c110040107680c2e0000740040c1080f00304950201c0f08155000d465014038144000700d0f01044043c8aa0304c002c607046500c3c0350b85480c0640e030104d44000540c0403050003000010a000040d04406070f028030a580410030380601074520721840c011800741c1074041d88030b20a4982c07460b002c0d60080010b02014201616441d080e80c000560b0b00d100c3d900546210b070808401001042d030855086840201040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 14733352 1250 14732102 14732141
    0x1104050a1b0f050306060703020c03120c0609031305060703030b1509010905190915080d0203030601090602010c080f0c040306050c0d1404050a0b0403030905010e07140d0201081b090901080a030201 86
    0x3010300411038003005c0c10041c800c404c001100340416008000e100166000982170300c404003980240340751550480c00c2002e500f40030708400120f90308800b004840709890341da080c2d01c03001030401e4103200307030380d040f03d4021403e0544c0c85d12003002550b611000141d2802228858030342c3d5507000000100540a280d000c1070140c3e007090362a00701e185000ca001d07000d8803240000010110718402d0b08080154190b40102038030f029000005103501c3d4040000d41c0b0410080e00e1303546d80790380e50314012800c07140140c00d404000b440b1040860915400c0000070743d00103056404070340c01c25440e9211502103410a6a8007580c000c000030b0918503068050007005009080403c0c484840c4c94142c0302d43d61124905400100031711417460018042601070307401061035581110082281400742d208417951041c0c03901840c403003000182840b5025103040108101c01c0340e41a50f40c54034544070344100185421528102c03696000c024000001d507510786102950081032404002e0442c0c03074a50070064211500100e1302c08490115 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 14734602 1250 14733352 14733377
    0x10f06030215091302030405030f070b04061404080d0b0f04020a090f29031e040609171c090c0b0705031804021201030809031507020a020108010e0601080402010c1104050a1b 76
    0x13a54640c9078907440345007000d42c0ea5525450300c24114403c0171b00126135800d01269000070702a040320b82a02c143d1040e0b804100c3d4000109651500c0031080350001c01c0b6440800440300006c41c2a0404065440301503c03c132810703038107200080c1c00e036000b05201d0000120703148010840520544842d8000380448003d155046140380c0080c1c000c1498101007070b550400c000082034003001d03000c9407104010621803150f042428a49048005090080003c1c0c1c1c0b0006c0c0c03425401c20800624007120600e0312088007010b00d030f020381001b007005045041410741d100d003040712000400000d04801464918800c0c0c01847d91414503888440a1445c0f240d1020b010f070b40f05205400724071005486c2d2074156600004d419407202a2000001d14000e02d40814440d06030994007400039082d000103800031114400d0302c07540701030307038030344105da407201d00c1c201d4800e0300160000012602550242201080d2039009401c03114038083c0345000b00301598003d071048519070f40d64900b803100c850080d0145c1d5401e41d081d4609030520040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 14735852 1250 14734602 14734609
    0xb03030f1201090b1c050a060203100303030f050c04050d02030a0807050105090f0102070809060d0f060303030c020d050c0d0c030512070c060e030a0c030e03030c070b09010f0f050406030203070908010f0603021509 93
    0x100080b1440c64991344402890900208100c034a640c7c560000d025542e91420181400c6000114071040700030034200940307441d4042a50041701e100e1401c0c40d543d1420f00340b030401003006503008040305980602594040c0030110350314900500c901802a00003207071604000e582a89403401d444620101e40c2d03c103101060001c2c6011086a150f64030850b44c0d1380e2101c00c12604034000f0312485091200307140c68a4000810140c058111500c20b140540075190440300700d0348181d40c28480c0c0b0b00c2c0e01040307800c94191400214040c0c03800c4001030780285480e40c24250311011100400405440103c08106801c07030140410880e801041d0800c041017000d1400c0c0100c801c0e01030314080f50303610b0007018400b0103d00c0c610303075031004c20588049501c8082103440301541c171700f146c0b9a0359100d45020350000e560402609003840c0100ca400c1d020407900c0e5101441c00f403030a00e086000350009442c81e000c0003504400058280300c24001c0a000c0a003549000807054035600c100920b001c07081070704a115490a2095518964 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 14737102 1250 14735852 14735869
    0x70b04060509040608010c0c060b0103020f0702040203040503070203030a02060105030613083103030e090603030901080118092a090c020304060c060608032205030c0d060e010b03030f1201090b 84
    0x868034102140c450100c02c0c00180603004a4000141a45c80e00e5004540558010310040b0894020a4104280901080114282e200e00912076050074009c00c044001820180e008640c440d0040041c0c0e82044d4031580000d04503442003a84100603404207005000a2900f400180d03080300201c050200014006e40c1d070301070540a03040f50003c02c2e0803916420342c00080c00005070f0819155a60044600b1a10b0f4507000d04001d020f2148540580110800201d8a050020440e1140341058482c4501c603885d00c1c680c4c1101c0714140c3c0010400507202c42180300042c0d101c040603000d00341c0d003400011440c80048640ca00ca81126400001c03410300300144000c42d13580100c02c48007a03031501d01d4846102031003810700c0e0380500b00c6603003c00e440d4400000c1d40c0410140d1400111001c03108440ca016031141d482c41016510400800c84c183d010110030000d000054103540640c3d4129100400480ca00e07194400103130540c0c02481c610010745e04009000303480a0b0a0071130301030145c4422102048082e00c490081050700c07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 14738352 1250 14737102 14737109
    0x20a09030b040201120e01140606070c1203030207020604030b06120109120c0201021f0903021615030e1903020606130e0303040611040b041e08010c080a050604020d02130509010503070b04 82
    0xc505140114041d07910550305e800880c008070506125180404030300300c0c02000b0000b4410300c090161008103d441ca0f0030402c4440e81500301898032491130500b5401120f500051074128180740d420410400161034010240000b940591803040c0c007480c1800602c50207090140c1d6403901645009403120001303c8a8241d070045008501c0d00503880082c0340b0060340b0b45030269044180e1850b1700703590b600e51403d403031b040041d503075101c2c1d82650714088980020541201c418000d8038021040d1800b52417085200c1c0d4800814000018204c035408042c0d0002d9260000e409101680140c0213101008180d0805840c40101110081400c215040c030000d8200d4a07804003030f000a0841d500c0380c0300c007102c01c050344003a07a002d8070302d40750800e41d03460344c92407425000010204c03401040380f0380e21000142500181b180c42818622900c3e20000d650360b2416050007041c1c0244a00e5203da4284a40c2d0040344880c4042c1454041d1041c404854905260400c851b80c88142d00241c82a03002907410b0015a80c8007040c0c0c0c084 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 14739602 1250 14738352 14738363
    0x605180d0e0609040906060f050105030403020d120209090a050a0b100e04050a020405090c0304030201110c03031602030f04030c0512030f0d0209010201060509071d040b0d110303040b03040b07030f020a0903 90
    0x244002880001d8181c4501c05025501a041c42285c03018490f181d440f680441e03e00d440800e40144d40d8078015a43c03400220f40142c00f68000c0e181c18188107004003401420508540d070014607090700e000006117180815a0616031990b80c2d4401c01c20b542c40035100e0809402e4040340c5d101008203041c60001c00c0b8510410034240141c3c1ca41002c9204081181c040e030b00030704801480c1c09805d00d0080202081c5401c1102c06a00540c205400c80c80c4440b1604111101009288091443e42c1c2e120540200c000d444840d01c2402c40c84208041402c4000300000351001e5072150000c070a100c0d10700420000d01c0c0301540e201c080b4a4008000d2707402d1101d0148100c0344040258500036803181600e60050380102120b50019401c070030345078100020113910041e5044584410412507000c09200014401208c441081c95604205445c65444c0840c9512181da038040d20300504581c80c0c6a22903400c0c6215400a6030300321172000c2c0c0701c814040195010b001d80c10080005000841c01c110282400a045400720f2001418 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 14740852 1250 14739602 14739617
    0xc060405011b0506090d080a090308010302010804170307030209031605010c1e120806040f05010e0c0d0b1201090b13020f04020a0507060e0304140904170a09170a0605180d 75
    0x1050001a0b0704010290070206a40c0140b03000c5070740c41d03203c80000546c0070001c1c1920b4000307464030131188105840181c142d0b42e144003a80c2598019a444103014005449800007110b06402600403040114811200340d03030b0140e15200781030141441d2082d01010705485a00c500408d0010b40d80c0610076240c1d942d0803405c2400807141c000000414408441806003255080a49041c5e2054100100d00e01400f02502c003000f00301c014a1480040f29028003031422017101800201d4601748003c000b030006c1e0750007409d0000d070000c1c0c400d000910311030f034400380106580d448429040c01e001e48110401c2c0d2041c038203909100040314550005590f40c501162203449140c2c0400c00c815110321900640e00c52650104003049254404400075550341c02900c00c0d0004202824259030302802d1a0041c507025652041c01040d252205a1700b4460036000002c542c070401c201c0c89000210b038080f0720020500f1300320b00c01c0070b840442d0396030610b00240c440c0101000404050250a1f0004000004400e02004540e103000300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 14742102 1250 14740852 14740877
    0xb070507080d0c0305011d0610030b030312040f03021203090604032d0c0506060d020105070605070c08070f0b0106030203010b190e1203030603101103070305190606050a0f020c06040501 81
    0x500340d0103040403902d107103494480100c04143d055440103050750f0340c02d4074081503190250f00044425004549903500101400c2c41c1c0240c8902075000303041c2c0e41c600102030301d023090749103070740040c0010003160240c4e22100950254014190140642801403d04000c15447c601d808041107985180217000202001860303400303000d001c012107485003001080c141c0c08018265204500130041641c560301038031503001c3d2001140044c585005201200b942c103031581403c02001d13464403001040c0c010308042c288102031502e140010012401044110b100f02500c1408501c24100315503140c6050300001d05151040006020006040040d2000340100701c0d0118003000405034111031030480702038055088100138603217005045001c000b841c41000f00ba0102c1c0c0450500451910070b81d002e68544004d00c6008101107146940310350007035035100c42d0300ca83c00e80101c6049071903c400c42e9455408000000c8000c56840600b07548403c2c480810b5441b840186140d01140c800202140f0171841100e041c4640b020a07007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 14743352 1250 14742102 14742113
    0x1a0d020706020a120e03040513020f040515030f0601080105150a02010b0406080a0311060105010504030209180d080115090e0703020903070902070309050120060a0504050c10031a03010203040b070507 87
    0x340c100da903211074103540703a00c40f804014000c0c000d0380000454460901d850001d155000209540c1200d1008104441c0090a8007130f04000354401040041c1c0380c4810440880c0350340700c0d038243c0342c0c0c500450f0010550700c0c6007040c0841050b80002d040241044014001004641e035081d1000d5075424207900b00c15626025114164010300391200e20b1703038025040a800140461000c6081d081c070340c1c02a02c400c0034a080d8030311015250402409024007140c4148814005403c011311100d41c01100d8545180507180302c1558a45044912001840080e890b44014002d0303074050030f003440c0d624140b4108000030609007401c00b880c20030000c040404050b0b001c100b200407640c003007100e40000c190404c01190768043e24140207080d00e110f4012070740402e549000320340d070b10505d08403c60030010b40e0300007070320702502c42206100c0600000380c015911031140312003043d00c980c1c40c7c1441e540c032032040d43c80000c1c1d0000d00070841c841210060003018440e920500402002c070b04c41a90f1113911058500e0141e54648191a16 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 14744602 1250 14743352 14743357
    0x60b0d02090702070f0918030e030a062405030604020d12030b09040b0108010510030c030605060a0b030915160503040f050a0b01090c0e0409050a0f11061303120503011a0d02 76
    0x281d0321004003014030652503004a8404150341004010944040e2030f00080010788143c81c4098150341e000c0b14104001ca8491350844889900007010369403410000d803a20015904048980c82501441c420401c03250b503c00341c00b0340c0c010001940035101c0d514080c1c0000c4c001c0c51071410040c150780445100440301c984243d01850a8034001810b211031030401d810400f2070a0024003890209601e8500070a80d401c00840300c1d0001c0701d0b07209001c0fa0b0110704560781c8030048c0001900303031a00100b25400c045081a40c80d03010b5071081c19003100918043c8442c2800703501090b401b0b401070ba076448a52610200b082d50040460b680300741c20004c4940400060b203440e0703180082e00340d0051310040c0c85034008900c1030703800c1d0080484032003650f0750700004c145100100001c59a082e0360083c6907038030010400000170619101d040c41680906400c011501d40c0c2008585542d00c170390440b4604c000300b51001e1042203030b01540c00320000000e103040340c115030601c00303441c50029042e002c1207d00c1c0d801041101d0401f030907404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 14745852 1250 14744602 14744629
    0x8040809031b04140c0a1101020d020304031d0613030b040c0509040302030403050105010b090109180e120406120209061606020702030109120e090f0606070c03060e0a140c0904060b 79
    0x841e519041802d2000368815940d904852003541032000440d64289034144081c0140c0000101034074022801038140d9140052980c0041c155400348145c6c14035034203500c0554400d50081e19005003480ca0150503500c2c4c1c51551040d00d05c07a0070140700460741c1020b8441220180d990107000304005403200d003032440c01d10300a0f0740465400700180d0100b104159002c4041c0045034802d10091200c0c0e41c84914460a50190545550004840304000c100c2c150700724400c146000521000051490102c1002900b00201c0c45600c4490142c00203003008000e42c40507200302206030f405411820100d0480001c2e80728481c1a00d041c00080b00240c7e00c401380011641101c180761750040082140307800d1803074004544034200c0c0180000c58600343c0409040e08000c011140b0401140c1c0d00c844080c4e50381010803199401020060380c954210000c00701c0010410b00c21202030300014001004039110615011803209450030403d11550040c04401c001919020702c150b4209604c80d001044103100d10002c0740e0754942048 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 14747102 1250 14745852 14745859
    0x905040b04020403080a05041d0705030601050d0e070308220506070204020304020307090f0506090c1603030c0c0602040f08070f080a02040b010e0301090c0602010c050405030703231b030c01080f0708040809 90
    0x52811a05400c50300910841d4201d0b0203c11030480741270f030500c080c600c04440740d030007161080000600704c0d0302c03801c000d005000c1c4510000132007c0d0400a40391800000380c00407102410000350f002c1300c4003c4109802c0010600202d000506400e2101050940c005c03042d0090149030007001040440d82e05001c054090041500b04001414100d24148090030301545c1c0e03a070080c80e400c03021501d0780f00031000300d4400c0d11607001400c2c000c40f5140d40c05c41c001c00e0801c164504011003c0100b60006000e0300040000340f1a0b80034818100c1e00700554035003070a0003940030850700341072800c1c20415240301191000c51f01d80c0455000580c11f03c0782d401030fa4090040b016007685546000d000808200308040c0b032034140ca20781d9008010304c042010080d55079204600030164540c1c0001d0003000020b481540072070300003c0021001164420443c612450404950403003a0800c1802c003421030740342010403161085080c01d10b0414100d017050382184400b180702130704550820100800040601c082c420440b000c280025 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 14748208 1106 14747102 14747107
    0x20405090c090f0d05190507081e0d0809010f0c0c030206010504110708090301020f0408060f0703020703080711010b090702010b090a0606050f0c15160206090601060905040b0402040308 81
    0x2008200c0d0144240031400004503ca1000240514403410023045c82c1400c1c9031085080190704c011560b0740c45815904812001c2d400075140d0310b542050305210005032501d11115014210300c403803032144207052441c0750000c4c03a888840441804e00a60a4503250390301d84e02000284d400c481035401070384109111030310120300804000d10031550700400051406411018503041b81c0c20030740c45020030390403d80402400e001500c405603489003051400f140703065041d64018101500190208041020301c0701c2d54000300600f54007020400e0402000c9003601c1c640784030003e0103080100f45440c01212000c000c030ba40700045016400554400780c88081c10500707992000302c416040f011110700c1e5486842070380c2d4401c4030803001941c00381098501017012840103035406031030714002400c4460349901a100401140d5071158201043e5082220041000c2c40f161000802a0085400161106400 = true := by decide +kernel

theorem cover : BRFrame.Cov 14568352 14748208 := by
  have h0 := BRFrame.cov_init 14568352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14568352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 14568352 ≤ n) (h2 : n < 14748208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
