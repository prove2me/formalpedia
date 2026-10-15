-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4669
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:21:17.153213+00:00
-- url     : https://prove2.me/submissions/265ef563-fe04-43f4-9baf-2916d31a5446

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 839568345 ≤ n < 839748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 839569595 1250 839568345 839568349
    0x30e0a110121050916090c05040605030c13080f0f0f07050904150c0e1e0a0513180b0a230601031d1c020c041e052512060b07120806 58
    0x151071282220350b04000c14940402000d4503071500405040d41d000c8510b5010038000340350701c205003034595180c1d80d65003003c0c24008155070366480541403018170075051110880c00c4010400c080003820801d0302a00a0390004480c15142034810b4640d503005030001c022034580352800007411011108119004142c589840c01c1074001170114803000c4898600f8681d40d5043c0a40104c00000d60b4034003034400781d1050f074019400eaa44c401002d05026401801240c042045251681c0d0b110080794001c1c0000825a80681e48402401c6051004807030342c0701e04908001c0215405d1166038000c91440c8800a00c6260340c120320f468182008001c4c4d4107041c0d81f1108207074001c94000c2001c0011500c501103450240754807070300e80840000d42406400601c9031480c0300c0564200382c0034100102e507481031078a51080440c4841c6001c0c01c80200311006188841d021800310003600d50f88000c03070356100d46031240055081904030b4180d861581008150003810420300c00003900d07040403007103d0700452078210011348031100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 839570845 1250 839569595 839569637
    0x3051b03060a063209070305060102060105040c080f060f060a021e070620030d090b04060c0311310308041a07020607080702012d080115051b071a030403030e0a1101 72
    0x11920b030401704000402c61019095031026008070001d03000c84001d80c0c0d0b104200800e8421201c4840c00040d80d601c041401100900704041c2c1028008014408451803a0045081c0c0e801c020591030059001001150a83c5c3c544101d50304000901806400000e080c504098a04441c42a00ca01841144e07032450746124130034010780d10381e12030101d024030a030001401e00349260f00c0300f5601034072214034001002203903501a1003140c006401803c0101d0400301146026481020000c0050b01c10b182d0f810281400700b410100c0c02d0002d5489a0341090326a0f05040b02c0003940c1c02d0449802800c902e0402580c4050b907900300c10746484591051000d642c814251004881440d02c200a54030380310003000300c01c03507055814808400601030303c0d510b1203c984c0e40c5500c4102494508006100803c10800020200d81142940c3c24031000c851001c5864050b55001c0500151880740001d0303203210710201c00e1008244d4503004440f0308584000041428000e01d45070480c40551601146052101007803a103550b0880d00300b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 839572095 1250 839570845 839570939
    0x19150c054e0f071b03030e030a2112050a0603140d08060d050a02040912030b0f1807140309030a1d01080613060b030c07050d090308040b030a0603051b03060a06 70
    0x145a540c202202013001d0710751150940070031008590303101c095400030300700000c0142e030f1160000d500400c60070000150b90030152000c85003204000c3c145514080000a50040c036000701094100060501c0c030703500300701d40c2464041e80c500b0000e0b0054010101c0c855407041c440f5401000480b0041080021468818900390392013400a4015091007029014800c002e050660000c459840078030031900c02d071080040300740044845961140110300d003500744200d0401503507408561030a014005001e030041241680d0402c55140b402c1e81e00000d06242c1041d8070121fa120350141d480b44039036152451400191900c4001005c0310300900c50780d290150b41c481141c103c4c600034082d00800035070300e0030034000304580d645c40398105031543d00c076581030310320036901c01c0300700204032038024284904107030618401030385c581c0c009089140500d0f02d6032404070103e00d06000c0c0141d0541710104074105106058107145c04d0801c0140390885080c0b418608020032a6a0403099070560381c64005540e00d08025104140303034030952 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 839573345 1250 839572095 839572103
    0x1080a050d12020d09060c120e03070b1302030703080405100f020303040f3f0e0d03050304031e0503070810060c0303050901060e040c0801050619150c054e0f07 70
    0x101c808062060700e500041d200803c03030703840300081c0c1142c48070340007a10850319140c27100360310400c4124086130113030070010380005211624140c42d040c10b800192403d442030300140d40d80480010108414603012140100107141d80c14041240c1d58480800394480c000103001600d1a812400e0400c1003004401407841800f05181c0210942007201415210070300340b04603411070142d00404d440022030b00a282c481aa1000103240c1e4a10039000c1d9401c85050300060320842c240400c0e00491103100030040c005e2b81c0d200105a13030f019104d18002d407000f4090f20015201300e1144803002c00c04e0000981c04004002501d40500340404e2644070300c10071758010b002d20303441041034103035a100b03100401507250091001c80b03e15000a0200d500c0c1c1c00300f0414200da0364880343d07111064500c0c04111240c202010b60780e0b44180740c10010382d042d401da1911400c0c00c0007141d60b030304032030308020084043e4198507182152440c03581a0003000341c2446180b0f0066180b0151240c26601c0d000f01340c1000702c91a190843e10080d0788 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 839574595 1250 839573345 839573351
    0xb130f08040f060311040b2218020a0e1002030f0f0c030c01061e05420306040e210313140a17070c03080a020a021804030801080a050d12020d 62
    0x941d082040180c8101e0081c0303c00a410700c000c80d581c1c9222003060303c0030740c0c480d5511a8904107040380010201d00d02c0030307000c10070518080c900203407207a580d00015085000d40704016940d2030030100004c00c0b0b0240f002844e88542211035407400103d034004141d8266210b0004c4071565125402c02c0b10351940241a030000c000c0c03000003050303080c960040d04064100d030442444000c84c2410808042080d1801c1d00580d0b802c104819902030b9800c40c40700300c0490720030b51800c0c1801c144c04200340c8d05040c003514601d42d40060b80c0000610803d41024414110864481c001610700d083c2c1140c100050401c500400c50907130b04011011403181445500b0070f11541d075002003511254181d1281543d00c454102c4e074103484244018083d0314120521104407400707941d0006000e20098159500c0711f05c2500f003070300004110301c12082108016190072403114842007028184002c9880c281c94000d00f5410140c101200136000b01149000050340021101c5180c616400d12604c19800852491300a004081900c0400c80c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 839575845 1250 839574595 839574599
    0x1031128030605011d040602090604080d0905030705010327020a1503050f0a02070203150901021e0903071502060a0b031609020c2a01051c0504150f06030b130f0804 72
    0xa5414a03a4049a00c550300900c540c1c0e990b1400009040d0310100070a602e40003007400540060596030061064040c02014070341050780700c8942034a0005040d10f0358020902d040e03030a203e41d16080210f100181024a81803140c420050300c04491011100c82c41d00f07005120341c02c0e40c02159511110724010304503900140b8000071040c0b00041c00b030142a24030600c502c4e150300c04140c0d481e00a008a4031025006030050950020343d01006950710300040c10084955401c7c4500184a00440394031080c11004a258944070507020080500b480d490f540440e00050b822999142e40f1a0085140b40e808110400b0000d400b40c004800f0070308107901406c01d0520004a4800803030703082800d9000c0c2981c200100111901d0890741c0e48a00340364418030380300b8401c030380a07103104181a600c41c41c020040000d40f1207000d4600a00d6412440642d882910100c90303042c2d0005010482401d281b203004241400890240800e0b443c603180c04034040e1014041a13941109038940a0030312901d458110001507205800995550b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 839577095 1250 839575845 839575909
    0x417030f120403030e060103030c02090a06050319050105151c1401181110081f12111005031501050d0e0a0308060a051504050f03071502060601081e010311 68
    0x81c904840440c0420b01d040d411201480c2d0000d0207034141c1e989a2598040c01909408000c0c1100b40284050a596110817000c034090301c06000185001d8801c20819400318200e107006425a00020728440000ca0580950308103903442030202004076035200840d07001000c2a040000e4050074002c5000c034958204a4000c0c8200c1c403c2c0c030b227401054082c01c61a0003003900e005c10080c880032400506400540d05901144011006003030900d1a1025000604852640c0d00a0243d110000100c10f0f5091401c03c1010105c0f41410f4010641912252070610b280d403401c18403075090320382d00e6101981081808200d440e00d200e85907101b00080c00c49601140d20341022898001c1c4680d80c115a0b02c0d015083c0d402d80092541040503060304061070a4075440d05240c100018008070261040000340d25118441000900c1d81d0525140c3c0241c4202e540906540d10301140003400e1440d010b80302001c80c0088003080e4403130150805416054983c8207101003654000c0400081d1103841c09995548075036600312080d5884 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 839578345 1250 839577095 839577127
    0xc031215011b0602090f090a0e0d180b090d150c110d092d15020c010f0813080c010204060207051306060f0e03030d1e0b12030417030f 59
    0x50806040318420150309a00446000000c2e00069208001480b06140014481d801070401e509028000d1940302e444400060346000e410303103240816944d20118140681c2d018040c4083d0040d040c141452581441c2a01031400c07a524465816038010204e840520380d03445a4003075040c1c5804c21810868100510400d00040c01c0364038445021500c5103c1846010f5030100e101615000eaa8030b43c0c82c1480c1c641180c146030b880e00350008030b02110202c1002030300b0005044950000d00301101c0319681c2000c800d00040d1406181c0003219040c411000084200d041d404010036920000d4101d0a08001c0358a15011195009003102011154004100401c4a41d4005908022501d040715040381c9800d44040610449046008400000790904003201540f801003110010022000d000c480c0303403a602542e04000c03180b070b0520306600c1c4440d80f1084020410640100201c4050444070341200d030b141400596500e200e50301c102142c800d00300a0240c212a001d10555110b40301c0064125668080168820a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 839579595 1250 839578345 839578351
    0x60f09030f020d020d0c061a040203040c08070e040b04110d0831210f050a030306050f1905130207021e15040b041a130b270904060b01050c0312 63
    0x10f110302640074025500c0001c1140d00180641c445003602d020383c0d16518098090184281241c1c030310501030b5419616144000c6201c0c600810080001c1403e0482030750800300c080e0300401c000200401400003207501c4501803600664002d56030001c070305e054008603c2110701c034031000c2c080c1500800c0260a00c20703500304140000d000a1402e01030320300914240603d800941c0503204254015500318005650441c4800c0c0445000341540030465043c0d64480e4944581c1d00710890000340c6503441000742e070a110825201c400c00407107030344502c3c860b10000e40c8241885440303401c0c0b04803000c402c1c0d00107004441d4110394846401030218183c0e10901d0030b82c0070804007044012402600780d030007400424100c1505072030564207000c0b1224034151410b450141c0b440703242c1c0c0e00b0b071544080c10041703075a201c451030540100400700050819111030141500b40001d15503203103050510034003085103224a42c1d465007002c0c0e000750b2000c0c0c00a06095400c004031650301414003144034034440002d60504180074240c110344 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 839580845 1250 839579595 839579597
    0x6091e1006091205121606050a0c030506030606092d09070510051204020d06020d020c10111e0327070503010f0905030702040e010f0603150518030409020304060f09030f 74
    0x86a41c2c0d1842c400d40190343e5100058070981210181c84034440300c0350010301c03641c10b1244a1303207501c0754903442e980215842550301c890b00d01e6640700c0d081400c175014085c55611040440150085281440c0410300444c03004108048078925450b0701c4000c0c0d1580890ba41c0b4940b407800c44105a03151105044e0354800c01401343d00c0c4603014503062034942d140310704225031001d08000103000058445a007803050040a14000319201a0248080c0101054a10140a04818a1006001015182e1f98590441c2c080332000041c6502c200451400c1140810043c1c40406450104d15070781e81c0d54005080c8100142c0020070403842c0c800020440b4104005550415204220000c00102e09141500c00448107402c0004049030020b10112001d882c141d4450302c4105103150002c030f81c02001c0c0c0850021607070550400c071603c404640c00c1001c281118441d8662043d44201c03820b0592202140407685c0e40140e01c1100300d44c40d00080060100106900094024a80c2020500c40c8240500d00649002d5501071610 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 839582095 1250 839580845 839580857
    0x703022506020304031226041101180501050d0b0a1d0106030504030905090406090503040b0a170103020604051507061104051306060e0411071b0e010e0403050306091e1006 75
    0x214080c40004008000c450140c2c004528051550341c40300c00340880c6084003014001200600fa40f0864103c150031004d40180300e00500b1171905180600c03c15010302daa81c0e0410503000c00c2001d44100b60380000003a038400742000c0342c40314501707440403010380010070307449402c104009000200e40341c04040451050360303404400c4059a89480013282100d408550140c0040c0c9003c1c0c042055041010080350441e0103854003150340a40d545441d071541c0d00c5584010054007001820f818041c5d40610603801003205c1c1420307003025500d59000940c550041b402803503c54100704a240180e45038440071112540e0744044188800440d4143d0303460f290304203103d414090710106d0769141711302c06e42c0c0c441c10054900b95292905540054810700005043c48990300c00204400c001c0c02c1e000ca804040060705480d90300c0004e0396483d080101e681250070040c0d210b001d031646081c05000019800000f9a0f500090907500c40e451070b03460042c48880441b4495101da811031901003404410b544580000042c2c401c03c2e00c43d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 839583345 1250 839582095 839582143
    0x150522050118120f05190809030c010c0f0e0319020f06130b0307080c0a17060103060308270328020d1a061903032001060b03070903170708030f060a0803070302 70
    0x381d840d4402c499441140c0c6c3c40c0c131070b01c600d290b0b0300a484c01c0341c010401c40112810840c1d05c0c88a18215520100340c4804500041250b20107a6400b59504144400503405041c400c42d000387c1758210300803503200007849521052007654441d1144825501c0c0c400b00c00015405c25559000000010350044c1c0b00600010a41c1c0c4c0001d02250000c4200e40009030f0540e01c071000c1c40d003240c01490350304c0c4014180604160b01c640000020130b13046c1014158005801d144001c0502d09115444041c200701c030303070440c083d401c500c0c40b0b07400c0b0801c02c05890000300040c0d0005100100c1074400560140c0800000410503001d800711104040600124917105103029904d055105103c41071210900388117120040026243c0c0c0c1c242101e1480120b01203413060940f4001248540e1a113508004540085541c00001800100d081050180000c1d0691804514100c03180c9007007600d1325001d51600c40140a0321400309000d01140c201e03114030340000014004c03002625101c5510703150003500e540c08000c407000642030031420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 839584595 1250 839583345 839583347
    0x21f1b0209040f03020c0a09050f0105030d0203031317030a05040605010504020f04061d040903081e06100309030903050601061808071215060e040b0103150522050118120f 75
    0x8112119001001c0561640d100e903640d820800800e1070440441c00351103d0f0141e40d442d5500f514015050030742000c1800e15000304000312803001688994413951141e0100c0d0103982e00402202d8215242a000c01881d960a040507191130322050b9113035146400010401c00e6031070300e991000340601d02c41c82d0240050790b60381040000b640a6000540b64400003004104002806225602c4101042610f603200680c1c09100086c121a00c0c130900740c01007281c1404100452070129003c00c510000130101d012541001d402040c20b01c070100f41d100e01030542e9405000c05050266509034015984032040b10003030341e1a903800400002d118001c5620385072541401041c010300c0455010180d4440504800f011ba45075107a60f4006400100010941c0b90785600c04200c40c180ca20095118600802190b20345505d5031402084500c103100c0c0c60a0045d28003c14000702c001da102c80c90f51181e206c1c82c0d08249918071030400500400c0314070720320880203820303a12090802010400781044201103482da241d041c034203070710 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 839585845 1250 839584595 839584637
    0x60709030305090103020d0e102703090510021c020f070906031220010501091d0d1709150108011b140f0304030306030812011a0915030a0207021f 64
    0x307011500a02c006815540302e0f90241000c5e410000c004103000082e111840d0a00c111426690a102e840f14030452003801032800c000d1002d86480c60300c0c18011517a407802040c0c1040341c091030b40318030b1580b038a94118500c00c010005500945030102c0280030946070307020750b89481d40d0107403a08030302880e03400041d115a144101012aa00190880b65031261740200711000400031016145902c1c1c80354080d10007120910a45001c0c1190030b000080601e000044e9034030082841580c00d04586c041d44c405104240c1c403000041c0c40c02031030324000c0b81e16114150801d0402105050001055418100002d4000415008040c031029420164090001074000807208a000030541030075110f0104811700405500310021a4070034007a1800088290f01c1e0355449016038480b1001c0d1912466950060014040d1311201c0c0103c1c0134075003c058a00b150420100c0d0740d03403015100c0200f1640000c000100c7d5031141d03030110340c543c1e5801001c00b40e0001509030384505c00d07000c140204d0001146542c1c2c018030b60181003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 839587095 1250 839585845 839585849
    0x7140d020f01112203051609050c030103150f0204080a03180807050114070503090d060e070b180d050c060a0807120c3e1f0506060307080903040f140102060709 70
    0x943e01d245031200b0320580c00340c100d00443c42e04400f00d400d5540000481c100f840b8001601c0b8070080e0168595192030840c409490020300641124102080108005000703144001810044c90345d002c58881900e40f803200003801a82e01c04409401418071f0742c020968403120038046030a08880d00290b01d034542c1c0001d40c3e105900e005e61808103211076000c4481c001e4080107850f507a84503004607803034002c000d804221048040041101c1d004d444000d6244048000e00a44024003904a0040d0a1402c07052440043c0070b4440c2c0b50a003c3c4001000344030074414240b100c0c051043c009000c0a81d503800800e002031081c03008542c020f0010710080032030f4840c409180a042800d00c201e030b80300c0090300300b100480814404104021483d54081c104030864071034210b41500404140340020b0560030848026110002d418000c001e0440e52034503040000d43d40d01c91060725008201841c080d45165a8151040d10f503226903000441100b1007100009030042c104580107072200000e9080c1c0e21207494089090700e10061038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 839588345 1250 839587095 839587121
    0xc0509191103072a05071410020109020102030a05090a09020c0a1406010b09060d0e010f02130f0b1824070309050303030f04120201110c070e01050603010b0409020d0207140d020f01 79
    0x1c22400301c28140011050802d810301c00fa4107003250455980d80a10701400c550102110121204c000c00742454100d0b230355100b20b1464002800449015070000703403039105140c1110207110b00410880ea0301c0d12856201c0c000340222120840d80d0b086041c0000355103264402003200c1d41506492a0301e81040082909030482d02c6000000c0e0400102508105450f001100c01500c1d05a03a840c0040c1c402c0f03c03d010700d02200e0381c0c030b50340146d9465003854078198249075600042c1c04102066000c100007035650342152840e2840304800da0070b0140c03210004041c800542d0010918801058442c0c21548408000b048610b11989034104d080f6580c0061688a0000701d40901800325000005004a603401d000503000c0b07038061000096810301012020502d40140e002c20445501c91070040c0140707080f149105024000456100303066600d045507120040c0f16074001e4941e031a40118038500c207564160140d4100340c0d8003d9041c44551040b02c0b031184c4e40d01002c48410014460940b41c044446018442d4403101a25 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 839589595 1250 839588345 839588357
    0x1080c041b08130812070903120e01080103021c05030a050414040b01020d030b010e060a321b0309090115020d03020f04050108040c0b04181505090f040c050919110307 73
    0x1d80d8640404101d420034144e03040c100400c0040b1000303113200030a030300c07440c0162541e03100982981484101d803d00c26403160140003030007085204503a0001a031b10f04681d411100020240c02d200b9610b6000ca10010000388540710100c1c004901c00d8204028005a0b9881852110085900000c0000b910304030841e1307078050303040b420b1146045032007a00407030103943c03043c140f81d02e40045440111b0f0241d8450500140000c070700f240c81821b41800b11680c154800c9541c940e08000142c268030a503120710800c8050004048824600c8000d2542441070f5044406d00510500b41513035607124145520014481c0d140040c022134070555400e900906c203840c030000142807043d050600306001035400840280fc150f075100200d07100040e10072803907001480074042d0b1900c17601ca18041c2c9143d520650f10341c0d02c11b0440206200c40c0070302540d21070450722540295070381c101c20026110f5050005207200b054200d180c012074502c00700201514040030082d207080c081d03901040240286100c3d0116800140c40640001c0c4e8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 839590845 1250 839589595 839589601
    0x10b03061009090204060302270618131a0a020d05090610050d050f01110405030d111002031906060801061202120c09120106080106031101030c02070905070507020901080c041b08 78
    0x9440c0c1c3c04011200e101500000e581c6481c0d0300011018150b4503249103001d104001c20b86600c203900c4d1503c6401038002c1d80c03403507590f0302c00036580c64850b00d0003030528126249184660050091101400550101c00f1140c0c410a003442d0451001a40c000d641100940c0d05010100d2800700d40003036118850505a0083c0341c10605101c10400006e00610003601d4510500c510b50007041428455071038000130b4240303030546d075502d40f10a140c10100440d8801c030500c0100000c0b10b50f001d90200705a00c10f010103a80059881e40e54103035608080c0900059006001c8c035041000c90007070b8202409505907405515801a1020900082d2042e0720581c1d03400322004560b0030125042c500008050000410000c00740008080303101559821254641d028402c903a4603031408100b404500030035056104028642408402a03c1c000a9036070b24991107400c3c0a103644000040c140c80c445c500303442204c0d5005040b84000e507503401c842a0b0303400014144034030681c80c0c0040000100c0c541808410448960f8865813042d039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 839592095 1250 839590845 839590859
    0x23106062d1119021002030c06070507033b0f130203060a030b09030a030614091501090803120114010c0c090b240c010506040b0a050f121e010b030610 66
    0x124112449414040114804070740180c05001c09000210070603c0041800b01500410664004500144040d500104a8a888141c0105116500903590f0800729691501032a085a82ca2500c1c00d01540da000610f0070900e010001c1000300c0c4440d071022a044822690b1a41041280711a9514007a8000e4415007a003018010030340155520080040031800d1045c1e40340c0711201c2d2400c0c111355400050300300007000c0b00c50301e800d0b01c40c40010341540340c209208414004d0104106840c041e0901c040710501101d03080a0b40c1c8941c20007000703444410282c0343c640d2226078000340640002e0041da180e082e882044010135510840a000e0026004030071510310501d803051140040c28564034145d00705000c03004c1d201030308844605c0f0079aa1014000302a0340ca08501300c46c03e0842c0c8020b06058869400c4c080d51094598420303d0074004da41040300c81044c029005400140c4c0068518000c2c0541d0145072846007544080341c100290503c20640240300101940040681b00c0c041202c1ca4403004c002940180b02130 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 839593345 1250 839592095 839592167
    0x22b05040e091005040c090e06010e0420130c0e030c03030712030207120e091b0a0e010c0b072a0b0c1602130b0a0902040e060d02310606 60
    0x1140c2081e21404916280303c007041d41c4088600344ca0000c0b44030010000d00c5143d1045420300040381004c0d0400d541002d42d40b42c489440604041d041106c0355640403903402c1030041c04c18030108000e281c1d00c1e0230320841042c60041e05840503107502007400d00754180c8807400c0214010425102c0280039515041195071814030f07030070b20700c9442410145c0c28800392000074075520700004604a240c86902d4241e4582c42008200c4000600c0f0705070581001c105092095207480654020004509128039102c5890004880803410450050304400040007440640303034110314804101d00c070000003100d031640020b001c2d03e030b180061071008140f0020381000035081410140035001e02c03155001c0d002441030140e00003641143d080b8000ca003005640d044c1d50300c142d1400840490040030380000035428280b4182e68444402c1e001841d050241c40002c0f051001c5607150381041e050f594017000d503912103150140240000e11a80d000026400e8907062001c28194040c5031502080810f94111802c01a400381c611105 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 839594595 1250 839593345 839593351
    0xa080f0c0f030708040306060b0901021f15090506030105090607020a03030903110d180f03031e110304080304030b06010c120c03021c0809010b0906061b0a0f03022b05040e 75
    0x41800780c454940c56201d401e00c02416810f000b415445e842d58118107052086130059446203000c001d0800c00500180d03004030320380c010207240b09052142820402038500113003c8081034000b030b100341d00e44003041044955011034001c14003500200a996134000c0506d075149401d41d88800075900c000510000070b07220ba0040c0b8001c074483d160114602c0d01c4402144d181c0951102902c010545401c2d0350b403810503c221150004014054606070220f2a40e1405010310b410300b40c0303142003640824006000c060160907140d18034540e001c01c8a5886039201c220b1a2280c02c103000c2120341e0714420001ca4ac2d01c0d88240704c18a101a00003801d02c0d00c3c0070b00100305031a45001c010044043d80a2641420308040700e91814a01000560320f03000307620300e44850000e0856101d829070920030321070700307040c0710b45a00c0340019609040c0c041c075080e103142c1c03080c101014034142503040018035011400032100d04152740840c43d00c03040c0004c0b480c0007070003814100b2480c400751452400400010414082080812450099690 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 839595845 1250 839594595 839594617
    0x4050703060e060f0c0301050a0b18060f0403050c15041502100510030516030b1902040e130303050609240d05120c1b1c2406090c020a080f 61
    0x4156039269105410740d414100124900d401580c100002c0300350b14442607901c00307220010180b41d58100000141203100034003d803102244080b601b1081c502ca0b01e008042064001011161a0441c4d003421903220783c007078001215a8069103c2c034080d14145005c084070481050700e052070410b814092414401c540e071850007001c522580b01a0308902130700c0d01c20103008103500e8182c8501f10b415070a00b40d00e0200003640908440482c00000c00114640c41c40c40768000035004195001c0b003a40010040180c0034030f40000b508403004506210500c0d0240c2d0b8100e158611903142030085580718002c0002e840e008a858034040b02043c2e42c044a4a10302c0640395609140013004c3c8036140040b502e90302d1030b0642c55140031b180900c002604a8522004100c556842c4c8550031740b85218904070780108240194100170010812410056a400c01c10700c0f040b00d5550700c180811001460940e03d810102405440c441c121165180c000e100300494400f040c80d161282d0000380e0107150540040014005511103002c0c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 839597095 1250 839595845 839595853
    0x1e0310030b04062405040c050f070b1015020705100c2a0e01081e0d300f0504030e100203160c05030a050609011a0d03121d25030314030405 61
    0x18001d12009902d030102042e590134445845400e003410b0000321401156042d00307000c0144020f130f0b6200842c2d000c880c0794540c01101060151901a80b0106500d840d411400c1c89030406003400d000b10758009100b070120f40c0c0885d004408103c4102083d10010f20380307000a89810320030303804a0708041b80500010098042c01e404100c0f06541c0d40c81c0001740b41001e805c1380c85160030105100340301c85140301c00c8410050900c800390001302180800034140300007005a909000c801d18038944c0b10a02d1621181031100c804a07018800003444003c104000d002c1241c0880218400040c5810241020a0000641300303a54004504d0604c0c42c8050300b81050340d20b202201c1903001000042010f413014000320203020300c200001c01c441c5c141010b04a00b50355440d42c8030b2002c03002024108400ea9074a802031410035401d8105004088400b8407900e01a00d00e81c690048000c801c12040384030304000107620b20b1000d45c100b100021300020300e611000f0b030720304d54803001d80041d090620610442281600a6070400e115000311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 839598345 1250 839597095 839597111
    0x60a1701050f030d0f140d05010f0504050906010627080f150c04061d030a0b0a1109010f0c150c0e130203250e030615030d020606011b060e03030c1e0310030b0406 71
    0x4410a903100646c40c06030a238403540104002100c0b0889440a000c04407001e100b10f140820000c0d9072400140f20300300c01c20072081e030348044201c10b4050320289182c401142e49010317911040c00c1c55456049881703883d0b071441010854034541e40c03035040090240d0300d004c0c03500d0b00e400e152074011a040e410480700100c21080303040d102d5075150b604011300a0b20364400e003480d9070240f03000450a0700312444210180f0783ca820410813159160b90000c0c0c507080d45115800d10030b440c0d490b40e0034400e2081580d03851400545180241444902e0703000114183c0601c0120340410320b511001c21504285d01080c1e605240c1c82c104400250340d004040420352040403110b11740040d846582d00002450440282c0e1580b0800400c40307007041c0d142c1428025825070031603500090a1b14189100000d11400804203c0c141140c1004203c004001850f00078190302a400012a41c81b030070b085400100c0c076407101d0740c04040144000703119001610321005a030310542068001c2416580703162200003480390028400c46000d036607a0b0700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 839599595 1250 839598345 839598377
    0x15110c100b0a090e0c0d0311010903020309030c0105040e060d031106010e07030b030105040b0a050c0403050a1407050d0b0a020a1103070f0c080102041809080702060a1701050f030d0f 80
    0x99044005160311000c2105041d950030310084010303a8004250081c206000e0070980003002451011100303040d1011548010542005c0b28001e04500d018801ca5081140c80014154000050a9405011019160790440a41c010748262056114055020000b500041e1651800303d00080c82a80a814603209a84a001100c4e003007400036080b2044d000d41d4207003400400c40d03040c410f4a86201c0c06038002c00c458101912811000796006001d02c2d440c07501e800c0040d0480c041c040517600103544c08021203228242614069502500c600c180c080b0038401c030680000c15241c01140844540c1c1c21080805c160f46034079444001070762186540e60107002c0201c016440c0d2010401c001c0040c40d00840c10201d90000303d140110703846040354840c1c80785070700610050180c103036800e84501d0082003100001890358094504003956016000001e540b150340811000c1e42990040d400044248016000884581e2110100403000303100c02804d5816a00c240000e46d4583d00070360109200c0e68180c00c00010b03a1064141d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 839600845 1250 839599595 839599603
    0x1315020114010f1805190c11031305040b040501032006042714090705010c1a010b0304121407140708060901240812031e010e2215110c 59
    0x4070607645900351100421001c080918040113403c9481000e001340e003450218101040325045034105000e41c0e0f60b400b41a25030007034000c04200d60000081daa140d229414010040303486900c2a50b02031414400111041e14181c401e550680c2d40c000240c5611410005c00f034609035624240f025005041000042680c2c0d180d64100e030a41d844014078082221000202e680a684811041d0024440340009003c2d02c40350100d007001c140c40c428a081620031006042c8041d801d4a00d4150a541c562080e0010425240755001544a1400340b9241c68120600c00c10494003000000075020040c10144a400d0000d102c02c00150507080111044641c11603c511840d820580156080c0d50f46a55420300740f06004009064122190f2040c0981c0000c545484105900c03810703200b0301d412241200000040e505049482803c0d4402804140404a90f03116000c02802d40c8007030b68848420f10301c0c03500113251004203400403481264065150201039501d4510344000d0111400d429002080a01140c55000c00803c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 839602095 1250 839600845 839600849
    0x180c0a050409110c1c0e1212031005330f0d110a0e04060e0f0c0f040f05010801050906210a170703030c020604120f050904180b0705131502011401 64
    0x250070301e40c1d850304c000926140002c840e44804007000d424158414003600001c03071501190b41521441d000c140b8000d5000e04040d442a2010000c41c408014040e04140103188030054500959030a9100aa20001c60310044204400c0301c10707a010b1001100100a941800ba0090141c007042060420070035a0340f90099400c110b40303e0003504404105600c100340d03c0464149413802c00d650030070250341401100140407800910f105030011120001c18003081d0001c0485140a400074450368403039840310226461400c1d94820103002446100020403985000070555003c1d81e0010859241e40f5244858000c40540c6650250094020081481d0100713aaa0318004110402007800595882c024680a411125405184c1003154040001c20000541c1c40c2a0500c10a4007030404a80e02090804103c1d220b00c14110b082ea001810681c05214003458206406405c41c440c414040300c5a07183e480464447c0944a040e0400c504400700421402400101240e2662114400401d205a90400c120660402a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 839603345 1250 839602095 839602121
    0x171015091203030911040b0d08090a080a03080601021b0325121a01090c08040b04110a09020a0e09160305091006030503070312020711120c04050c0406030b180c0a050409 74
    0x1d091480420004513040c5c501141c0896003040001100e0f00855407282081400409551001410400540e01c8a2550004200241c00c44000c3d00646c43c0007801000c040d81c08901510030349440c4564001070a074203198050000e0000c080c200c40c40304503490042ca00e8071145869600c40d000203d640d0542e0352140e010030307010f26819040b0401d03400c0e1030030710071130305a0242c0f001e50704d4a000f8008107540250011b41094014800702019140d50400c101c207000c0344c00c4903680c030500d500000240070707181c3d4029250241450725278040240c40c00e024000394190880d080c8810108102000c80c805009a000740c0d081748600040b1445c080d006c40e080c1d03003124401c1d0000d03038245d807000c0750f02810140c0c000003400c115004d280f4298145106944c07100300e0300200d0340c203040c89140800c415003200e1000700100484424000c0007400740e810f050891003c107a005000c1c4200085c1051074810380d600340f503c9018241400801000c0b121354501b1031061480d08811000400c101c010000007030142c42e540115100c45001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 839604595 1250 839603345 839603351
    0x12100c020f070522020d090605060111061005060d02130b070b01090903050f09011b030e010e03030418050907090219091d0c1c15030317101509120303 66
    0x8400a440d0600c0314651901036844010140f09a4850340208120007054040541c10340080600090213070007003442011000f49051524000d010060304030b140180c0080e00c13903221201080654a840d00404c50700140000d004403400c209d2b030b0405100611b030001d50310800600b840603408031007800b010a41d100d4100c3c12000324410f0180b00d4034084050040004110070485d1504580d0082c215018003518039580c040301050550441e4016689000c080c1030011290031050840d01d4060a4003486129080c0061a41e0155011600b00001120207452692050711a0264084d0b4010003402d001450680b9500555a00284040d402d0000d003407051071218a10310f0061007400024076043c05036200500b0701861a000309200c41031159060780000030302086a0f1b5400d50788503200159100d203100100b5451500d80c84190000d80441c50383c0030307603110b5900d101d8800440c2c006072411000c19100300f4110000710340100305079144a00c2210b0700403484d0070004181982c400315803c481046c01010340100391 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 839605845 1250 839604595 839604611
    0x316060f0908060a0b060d360f02090406180c1a030c1608040b040308090301110c1005040201170a1a060a0c031d101d041a010e1210 58
    0x50000d03408031000003540341c0900d01074600202e540d039403040a800122900c2d030741c007100c515a4403194125104800820400d0002d00b440d01044801c03074510ba06126040c444900442e40204590741d203080c04103402256100f1168050307001c2045002011740b0480b28103640380c80c200050591100c48515030380c040d013502c483d4036141140c0c40043c281d01d1015802c18000c10010444840d1140c01a661b6804a0080540071002e140c87c01c0c2060344920b40260b007502c00082030010030070103400020044103101741e000703004010000c18104960f004014202c0d0858001d09003400886800d0b9210380c3e4400c0c01450840340032002500305201c09001580e0341e01c00d580c7c98040070f039560540042170000048095454a02d04080c10300000c00c086003500b001020040c4094101000c40a100c88019500c40c004143c0902803900c0d40d00641400c1110f42803d0715002c00030307280809458940300e00c0003a20741e034200100071010404011910f0b0101c0900042d800740b112020068034050402c0400b1035100c481c000022000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 839607095 1250 839605845 839605847
    0x9030318130e1c0207050603240301060b3f04050309040c0905100c02150a0e1809060a020301051e040f09050c0114072105040b070302060a06090c080c03070e031606 72
    0xb080c0303940c0e0300056601c1781c0d80c01c0280c1d4464004903541700b0440c2c082110090000d21101c41915a018042c42d4190708014010940151100c001d00c3c0c40310349201c1203e80700e80a0003030400d1007d03181c3d04041850300c40d1581030f04021290100b00754020b01c110285d13843c040003500010b0440d00c808114800288003660184030605241102015030311207802d00103074605241c1e00044c007140802255201289010032900c101034000d078011824080024800d220380c02242c204841c03c40c90490b29641148a140007058000d0a94801c07641641d00c043c18006510311111502601071103003401071030700103540d0314000300360031094070803000c1d040c0c4110003401c007402031140014003074040e4003115940380c2c2003048904001898880e201a07030f902c000c5040180c003280d0f40000d46040c05181d1000f41c082d4400219401090b50100740c46110f8500d85d001040110303200c140f0704040fa00364141c2c54012504da8800b00301165900c602941d40303c1078600d0300e00f003003224000201e414000c1a5014102580544005006003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 839608345 1250 839607095 839607133
    0xb061909050f030307170c0705061c151202060901050904050f0901050c12010e130c03030207080717030d051f0609081005060d031121031b09030318130e 67
    0x1451040f002103050400d25200d1000700120082c001c0358103140007500380c1c3c0b800c1c0c081c0a40801800010545512101e0341c80044070b111140102c281200c51504144000c01048212948242c40040f012800c84000703644c03e01095600a09282d81482014880c1001c01e903164050385100e4180c480d602c0c0464113081a600303081d60409400100c01840500081c0e41c1c0d0320b08550220f046a200001841c036540341c000c0e006045001a0300d010340320903460032001c014981c001611304200c81c020400c41d0043d640c1e908284a030280c3d900350b0148680c1081104171004941e42c2c010740d030803d2010112070400340c071a100c224900d8a441d406100481d40c200c401300322a0700c05001101c0d448005010901852400b00c0028191110805005080c07007140c03e040324481c242080383c116031070001114245a2608204248050b40040740c0d41203252140582006025105c60140c03202d151024000b10700f4084064010f02400c6c05018055811640c1c2100e0411111032900509080c0c41110002d401296442c40200ca48 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 839609595 1250 839608345 839608369
    0x90501080106050d020d06080613140c060d02090a150f0210050c122517060a031101111501120b0a05060d140f0607080a1409100b06190905 61
    0x1481600c000411070140c000c0100c03a41c00300010310040c0e40382a520007180c003c03e1250081d010034859641003003600b04010b943c4018650103005c82c03071001d00e1a42e440d541c1c0e400001070342c143c115100703005540501039150081c0900303e000610403541551165041291268100840b4001a075401d031b0200115806220946030202040c000b4030103890315050808040c81150802c02c094007003540012100b8090044030f01030503101c1402e403020b084251740002d1822078148844c0d078111510b80045041c034070b0502c460740110395103c03088554480495005541c0942d5000c07080c1a0380c06074038844054050900c10041c0a400c0d01c6280e40106105410700c80416040100001c981501d0002408410f42d90444202c40745a480a4201059170142035010b0030f04603000407050607442404184400d060700403448600c035440c01c007010845220400d8035038045140c10b56044845801810041401003403036001142c0c00b02d00a4003640c03030604041c40320145002c501d8100740000740d0044090002d40351040303013240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 839610845 1250 839609595 839609597
    0x27280605130302121005011e08010b011d0f0402030103151d0a0807080903030d060e090a02091303170705070203070609030816020a23040c020a050706030203070909050412090501 78
    0x1c2494015440c51203800414000648500308680f1440124601006282010407031002c06100a507580c1e90840c01a284460001050703c6909001042c61001446440f0f0b5404059661001c6a006048a415801d4801c54040d421400c0c011004205440f180003e50083d0310601c43d002401054221807003c40703c0030f0543c68036056a41216260001c00003032140035050300309920325a50070991429180c14820700383c1d819014003022031282c030302c4584c540c0442c00300c603450300d407941d05590307a5005103071130b003040240c001d6200030303041c020813007002113900c50340d008130311a00f88403042251142d51030031a80001c40e20600058800161502182824002c240c0102442d04001c000103045540d80c000c240916001c3d14068032021041c03000390343d0b90303021060081c206100d500400400d070740203000282d02d0400d01103005600b0060740801c22440018030040c401d4001001d85081810301c0c10440c042c0d4005031120b420040400808150140f007481264051840b4480e007060740080c41a019203c0ca2040e4040c82c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 839612095 1250 839610845 839610847
    0x6010e0f040c09020d02042303011116150b06040f0f050d380907050a140d0201120b1c02030114070801090903051603080108120f27280605 61
    0x40000c8002c986034082d2880d440015803140358104820000703004540c00000c240c1c218040c1402017034040c1141803150041607000b030005000c80319405030305101b25a0010007242c1c12155643c04030310540c00c44602c8030038040780420107544601c00142d5039041900861002c0055540c10000b1081c024100340003014140c5031001015401c1d107860b43c40c3c0801d10400d1800c40d150dd4842c8688031000135828a42245050038420203090414000d81d40e4180341c004c11f809940c500c0000710750804100b103140664800140a000011001e9004403414410540000d0040751500c05296180d0b803110404c5101d60b5000b110506001542d00405080d81c1d45400811202102d0b04240502158805502810344242c4080403810392501d190131030710341c403030412028002e0b041e00c0040410168480640c4e4121904030084130445411603174031400780d109500340010405010000244010152003858405029001c54035205942c4200032409462414000c0501e018900c070805860007000045080030b00340320706d095 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 839613345 1250 839612095 839612101
    0x308040f080109020f010815030703140705041a0f06070b04080702040c030504032007080312073902121504021003231b130302040b090c1803011d06010e0f 68
    0x42408085e07541146810004a40000b030021040300205061442004d01181c402a94034140602506415694004203005075280001c19107481e0203510a081c0024401c004210141c5041085000462182d9600f0074818829200807c0f4880a180c0c0305a0161003e00d540303649a204110454552901030001c1c94130b030406010120b540006121b140d0303884040c0840712001c00100103481d0004542c025503980c03000103190301d8011108090580141d045440d0724441210a1003100520380c000c1c022860243e0245606090cc0a540a15080034500240c5449c0e00219280ca1070b5080ca68652440d0807280f6205c400c0c8811402c0410b955411001c3e249401c00501c1c0c0b10300c00520124501c0c400f50040c3c0c0302c001d0085070000300564441110346c0d00054606da900d056004070001a070f0114402030384030700d00d80b40c0d43c08294101071540900c1020b966069501c0d056040d05280005801f0f5418182c0543d42c13007026110700801140500f082c107912000130002989841a01e01c4480750042900700000c0f01d80d018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 839614595 1250 839613345 839613349
    0x190f03082d060312070507032916031104091a0415090b12010507110d0503010b03190609020f04080712020907080a1b0809010c030b0f0d1b0308040f08010902 69
    0x6410031001e1200303100e04032901c40e00c000914119200040b00b110000000e0702c10304200000070b409080f64441d95a007403007081c2071f0464803182e680902100c0c0e0341588000008400075801c0c81103aa5104070703401d000400101c10700014060740c00580102c17012030f645156002c0c548201d95440000c040b003c40301445840c440e0310020322102582c0c0326441c0c3d040e803070700c1209480b0707a94913117100da20740031101c0200034030b24240400604003850402e090001d4041c1d038030126400c920940440341a1802c1a44451954075140c0007e04262590b03110504216681c1c8404110502c0700c0c00100b217501780380d0060b940c0f110308180d0898180b01140c1e08c040e00d48a800462000182c07500000d4541c0091103040020050b80c0300d443e88006440d40545102c140b0821003072802c500b5402c8850107005012080080088640e070751000d070308488800428036800700200800007984c1c0340c2403209400d61442003811001c821500d00052960b00942c0e08103c0b48100c020030180548101c0400943c014072400000788181001e50300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 839615845 1250 839614595 839614651
    0x905060a05060f1806030f07081617040204140c0c0c011803020f0a120b041a13060c11010509070303020606100806100509061201050a08030723190f0308 67
    0x96810f4041c00801e51105940329501480042000500600e07501c0c40c0075010300f1071502041300c250001c5105240810900c0d19010050440422282c4402038610f01d450b080e1b103035820000340104d81c0142c8454400c004440d4210860317001d60a4061415141d6401c00402424110308a14081c1000f00050503a082c00a0100d01001102d805031044e543c0b02c1a000c0100d000d0b256550401142c103403c0b400d00908204501c00c2140c4180c1c06015201300d5042031103280001700707206852400300240301070030100200758542d10001d075600c242d0030300004451505507410b095a0044074442c1c1281c01c040e10070428181c051200030350005044925003200c604503c0064050800900741c02e00a20031032503181a8180a6011035802c07034070080c0041d0b10340c4080442005500c00c24061180221054440015654000015610a5644040000c0841c0100004035030b8045c00390300582428840e00c421310390300e12004808035950324041c8200c1e8003000002c0c140035081c030001401107442c0551a00440ca42d11800340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 839617095 1250 839615845 839615857
    0xf03021e011415150708180a0b0a03110c0f0c090f0903190c0618020a09050112030302071703010609061b0804030308040303090b0c0c071a1b160303090905060a0506 72
    0x100319070304401104004100c1020500d040d0501c01d4400043c1c8109201b07882c4040c11048009040381c4070448400302c1804074443c0340780304111300c5650500c40d86008a000c2c0d00300030700035180c103412203041c00a20015940f0b4410342c1000051240c207d4007680250f4200420044d0340003864a40b8090b1504114500720317502e00ca0303c18440c04150030042d000c1071080c85241d50303c241681110f0284071200d61015020071842c1c1045089102e00100b2500255030f00d000e026150494580b048002c10304100d90b1801c0d4041d5100890807207100e0300c803100c18848403100300d0180d4060605556200c9101e410058040c01c1c43c0219000c20402e0780042510400041d0080c003107c0c2920341c545051075164803149070603806000500c1008000d502d858081011340900d010241a03000740e008221142155110070100700301251107210040c00e0010884002041c01c020762610355035411204880801c002e910f0300503a5461646c1045000400f1541c0030800910342e4001c440d0403c90403182c0d611001d03d80000580148204 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 839618345 1250 839617095 839617111
    0x9020f1801060f090e01090519050403270302042412150e030c0604081c230403050c0a0302060f010b21061909050709170a0803130f03021e0114 63
    0x580080042c548584d48040040000742c400840550312070b046400640801c4030300d19007a00c2d906201d000908001d00a20f40100c0d0592150080f80140a90320441060b04000480c0f5250b04034400100580f900e2081c030b4030000c40300103090310252000c003074050005501d42c808101039511058590125085800f074050a820001c00000d00600004410303080d0f002d4042003400600507081084144600a40108081c01e5915154601c0210355503120b021650b11155043c060400786401810701015250599002400790900d50300b0032684121141ca04110030a08900580001381488900d44680d07500798003401c154901282040c00c0510341c48140e80411008800038800c0101041aa840c0d0401c0c008968403a80b080c10503240c1c4804800300074140a031a0100003544120f000101d100d4003086082c00c0700002800342094628030b40710404550006040b010a444041c2a000005643d00f8043d056540c803d4016100c2500e04445082001e41c8900070146075034102100c44a80c6a2601103095000000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 839619595 1250 839618345 839618357
    0x18080d050a14040c060f140d0c020715090e0610080402191e03050d05090d060c1206080f120c0a030c080c03040b12010b070803070c030e1309020f180106 67
    0x1516581d4002c1c00368a140350100d0000e11060105004c0308070b0701c0f41c00340c41031604d03500018001814202d65080b803803000d2036003c11081c01580340a40c416001450901228411109c8013603d800181c111a10203c49642c0420000d400400092000e4000c0d00c0c0c3c490401c50300352090050b09240640440da00400082c45510a8000304e280319801d20050005404d188042607102c10418442c0902d481f50b03800103aa95128585d070380d08109103d20102e4000d01070141410300161419980d083c05484070302c96240c02e000d00700c3c070040c03c000d4180c80f4580042501000030302d0480b460803c7c1ea410040c100c1c540c4001910100851044ca010000300108515413506c1c150500c04001d081900142c01a0425440b0074040010001001c00e812005001081d686414010161740d0b2690218130034442e401000702004030500c0000d0559024410b242d0280380070307080004040d040c1900142d0740b007080c00746241c02955a416a1350950074014215049c100003a0380980d0140124082421100c505201e10003c00c40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 839620845 1250 839619595 839619601
    0x603090106081014010e0603071802040b0a05180d03050318010917070209070801030b070509040209030f550c0e1501081006080a02070206030a0f18080d05 68
    0x4800d500003001018001e056070407a00e0402c07102c401610301400c001c0c0f20032900e0b40010405002d00c480303141c09102e004006040f01d52425150041c1c2050f0607501d201c04030760034400003a201d41d0207001440503d075155212642c5904814101d181010600795140c021072200d02c174140001c1c0c000c070407a50090041092020803010f0128501d01400c105e070030081c0f801d00740c03003461101c4d403410700082d0008900c221131294079540e510100310741c4c0540074840a41000540b40200301ca1038000d130004c142608001e0005440d258400001c64980952907002e00c1d407540c0f110020710800031888440b00040c1c2d0b5209040c40020a580000c102c0701c07010410b110110484014200002270307522a240300e1407641c80030ba0703c0d07803032580c1d0543c5081c41a012221f01e034507820324010341e081ca503101c2e0429174840d040300610500c2182c2801000c44403414020318141485500300104005603072840042c41c030400110700003160701c000000c4200705580c60101030500101c01104290005081c5030250385031a02c072454000ba60b55 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 839622095 1250 839620845 839620861
    0x13240e0409150203040b070804080702040218030a12030b06090604051306120b0a050705210702030f04081b010903030f0804020406050604030501090b06010914010c080c0d02061e04030c020603 84
    0x302944a0090641c0c40310044814808801d40144d40b046004040c1490305584100b0241c1c1d090804840082c4070490800c100d400500d400c0d1302811a98141802181030800c002010918000d101c4809440000400c041002c1c0554540252840c00205450050418020101040c1c16000f64010032f80b082032140000040c405040e84080000d10500300007038040445820518151802034869207011403e01c1e00098001e4000d0041b9541d074442d074081c03a1551f6a441030402c210600c050600070440c0401c000c070505000450000c1c1c400b802048018020039a540302e400c0d174100402c489c0042c14800c41500c00c0010075000442c844010740c850900c03019503030b41c610016004011366000903a01040c081000f04c03e1250561256400c54850303000138101d9147d04005403002c40d030502c1490f004150f6072000e00b445500c50041254064861103e0070f05000414a0700c4d82032083c9080001d0040e4401d400b048113820009400c1c02083c800102c00d4201c034202510002d002c0b034880d207000b038014480003011034510303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 839623345 1250 839622095 839622101
    0x1050a1d04021b010b06090a0e071101051f0e060603040b150d06060602060708061e0f040207030e01020712050d0c0813260622080c060103050313240e04 67
    0x2440c018011582c03004141c011181000340201c3d686140d600c0c1004d9807000d41840002c5440401e40244142d20140c0b5220301000e1303800d0000c2c4442c08020b0b81c82030941082a0900905000c0c0c5103020b10082c10444014000b644041c09a00c215044180b2500b40003a81d101c0e442100e03001a0054084002c40d9141240043d18007644007000741c10080305480041401443e034401000d45aaa50035074001c3d4076070207011207040e4001d41d62545c2c4120b034400485801d103124a0400309054020b403021840003e80000141260411042640800c0d130707000728041d80e982e040c000c11018002a28440014412640f209540c0359410745006060285103044da0050060b04025030311601c0a03500c1a01c1c0c03194490580b8203401d291031301510241d9441d15a044500c0d940031030041d10070b100341811506c03402030102c401401c0d406142c40030350328038070200411920004113120041c003940c00340e0019035a845440d0b00c3c2c14a000b5040d1f01900200d0700d50103659180501c4080d51071f008140c541b41000700c441e1818000303801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 839624595 1250 839623345 839623397
    0x1050d0305070f050f061033200a0b0606070503041505040905070908010e03090f04050a020c030324010f0206061210060e180a020a1208040306110309010e0c01050a 72
    0x42e80c0300704094021a0b01d400960540b060ba00001a508241d0361382c100540d4801c000c244030980342410088c0070b80c1c002040d0111404854440c03030f007009a10380340300d00700b401c00d007000c1082c0200350841040001444440600d40350489810359050b0300c1c29091351030302512400340d40101042e04198203003021540e0711560540300039108006042000d8201100003400d54401c42c03140e03401c10350130306c0500300c5030380008010f0300e401c1701d80034010003524a4548100402040d00410894140c2e0f402e0040c155920340810285104d038100d40b1442000c001218581e600c050700910f0303a58100b2143c030064456456003c11901d4105038161222200301c0e426800c2c0a090401c40303001050701601d03009001801c1e650034a109070003148a00150300ca528070708210980c0700c40b2403120294004c95001d00400c45002000f007401029400b8901c01c9081581b81c1d074500069130325a0b081ea4454070008401e011141100303200b0000a286110010690400801c0010307045008440d0840d09000115544d8400a0312565a07128 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 839625845 1250 839624595 839624603
    0x1501030b070c080c0303040201110d0f030509100c080a0605061c0c2705191a160803101e0e0105040e030c0601150801060f021e0c03070b2101050d0305070f 68
    0x10311811804240c036517030b030000c40c0c0c1a40014a0340611403043e94010540c3c50790304600303541d80f40c4c1c410b0012000390b0280001400f662902d200300002c0d46d0603000d15100700d002214282d07540c900c550802e0305001040e90166080144180d034100001c01e8810041c0714400c0e04020407030360111b115106002c0a0b11543d0721000401d04a001401041c1d00d9a0000520442500c00444009032020180d92141541c05e80381d01031000c40c9803070819000f00031a0b0010151890055400815100b18503e0f680c410180c1c000b9520410699030f900c009210500d65084280c058540380c90170841414504080640340110610a45028031f0359150f16003040d04040c021600c0310071002c41214520f50351540103d52070781d0300c43c00d00c4000840d220008900c051141c410703024404074541c001c00e074050303003814084002084800e10740a00e01c11803c140301c580e14180040710040012403d0603856803050045140e4580000105521444085005000c84d0385da240c0b07014100d907010b01e4200e03141e91007450207140707403214148058 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 839627095 1250 839625845 839625847
    0x6090f01020a0b091c03020702091803160602090f06070203100f020409060f08241501111506040b0319110402310611030d0c12090318081501030b070c08 67
    0x404850700165082c64140441c01078001203c00c000d01b00d080f80030b5044000c1d0b20408a034003180a1400d40002d00c540d07444050242c1e8900609580403254410f5000d070210707502e0340c001c01d80324218500100074048150b8240c82880c80c2c00300e0351340004c1d00c03081e5000c2448501540c6080e41d00740161658140c03001380004c1d0380700b0001180c403000c0702d44034405c82e4410b40c0098400c5041c00e001d21083d4030700c40080040c1076011340126440e03098080f0980f0702c1401e502d504200082c01c2121058200300420003050f4603241d044405401c02c1c109100540355131002c03039802640158140308008043c140c4100340c15810081c000510624080020080e07c0340040d1468040c031000c1040c89031060890b91100350355050512591685c0c1e40341c0d003e4070440c03044040385420740c00070b205114680c84183c119400350007003490101001d51107000c642003150180c6100360001039406010401403031703840c4114405400c0710f000412030b652540b80c00103505041408000d060906c1400801d28541c000c480080500317500038142 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 839628345 1250 839627095 839627101
    0x121d04020d02030a1508031603051207170708100b0c0c090f0a1b0905040f06090509030409150b16080403391406161401151406090f01020a0b 62
    0x60000380d04151522400c15240110f602c002c0050088170358112400040518208521301d07500d4821400c01840c10b03810f00c43c04011001441101e100c1040c130544090301d64a40444240714500c40300c010041c0704105010800c0d0602801d1040d029810b0704482d90300c419a40d469480700c08c1182030942c2c0e404070f140c0003e20340c0c0901c0b41d100d08101c240c03407040341c410008100c4001d1080010090950820020002c00c1000006203d2030816030800f407505240a1004184d9565900c0c5101c1240c608445000d01e64002040a000307400c007901400542c1c00d500c241f10502039003009041c00040c45480d05050f05503542c2240c02003008071240c2138600646d0000079441420804441586450641100c131a0b55645c190b65a00c11032144200c1d001c041d80e4541c11194000c0440030240b0a01d540a03a15080d2090340218000001034441c0c419802c07000c200000216040c100d10403885d00f031071080d80010b010080000b00d90103031902c504047d00c2044104441c5111303c5224000140c0c104808028040c0000d4018020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 839629595 1250 839628345 839628367
    0x1206010603050609130b012d090e0f010911060c0f0316030e1818031b0114160c3002010e06011d011503021207081e04121d0402 56
    0x1c1d9100d0f24040c0c2d00c1c90690340d20810244000d0014540c01011130b01d400c8014418204104400f07134000d00007855801d04c01070340c0e0f445410760010503441007000c2d58440c5a04040103909101d9032000300b0842009211020541e5204011040c0510300302c0d001d40c1e400b10b1807410111013005000c2030f2480980560b596030050942c4d1030381035031003407409401003246c05040050908200b904014810a0001d40701c0040d25185402c804142d040001004c0303e00c82817002222081d443ca1521052050703c1000150380341a0242e080200100104001c48488042141802c1c80360843c05a00212f80c3c005d90428201280c806112411030503030301c40c4000c1200c0c00d03540401c0c0036015406486070401b090210703007079603030f032030030707018110004101a103100e80c01070401040700d50b40ca01c0e0a01d6000360181005400c0501d84210441d07101011900c0da0001480c2400307215490038400808114102160103104040c41c2c01e4884800e070b45c051144450821100c0c40c4003441d4000750003002200c2c900010010340d40c40000c1c00c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 839630845 1250 839629595 839629601
    0x3110d05010e070518040e0c040f091704050303070b09100c0c06240306020702060d050c072d030516020a06023a050d09020a0e0403020c010c03050d09021206010603 72
    0x24800311408204003140c0307444d0040e003c2d039915100d1310130000680c2c000902400060100c060200d15103105541c0381c1419a0f65900848021610140c2e001a00c1081c500f45404c12042c020305412030490204010301071510007100f115181600078011906e540c2342d1442c55480c00ca010904424012f25140c0107401940c0c0c41004481410b00845003400044d0f20310089a06850718110a8406028a1441040020150340150039079a000406c00ca0071b0950004024081c0c0d02d04407038000325500c1c005080810489510200036207c1c0c8074410101d003821440040801401a018003d8144a40401ca04440c200b441403002c440c20760143c081c280895503141701a585c0c1902c040042c400500710b0403a010300b20018120301d074101c8091480981900304084c0c4c01d03501c55001503008054075440e6450740c40036840e4944404020720000200103860f1071f240c10b0089c24400c03030301c8040d070410a1007010b10010079070040544a8905401c0c0c00026039100342e20000d00b40c2030895401900c28003610000090090701a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 839632095 1250 839630845 839630849
    0x100c0c0f0806060a050a14010909020a0c1a0405030307080c0d0f05070906020a052d0a080a09050301020a080604051302030f03030402280e0712021201031203090807021003110d0501 79
    0x7003260829140c000811034080308038018160412096042048115101c3c40c2c2100e45010605118070100e80b18140c020990340030441c1da00101d040130b95a2070410205402412400031303a24203036009810541d54141d16444040c182c00d042001c00300200d03007005c01c038004903101d08102d520108801c0011f4003000c1b0282004465500205407032000001c1c103140081103070b04039241d0003400360424021020074a4101c20600c01c08221020101c2d2584c24034103401c020110200b8010004c2036160300d10010b00424801e21030700a14041d9005002000074181c0101c0d000b500048201c03804185075807500307240c03200305141c050080c2d0b051140102c0018584400309c02103010300d000343c61040402a80c0020310b4454501e804142c14101c410440403c40d51086000e401e4101c5014a0b0503050406041000000d90704941000c1c12140c0c03001004200f041041c101015801580741400d101201c0e044d01c4540305030140a402034010815620414074161195116019401d40029595140e082d6540d28500400c424 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 839633345 1250 839632095 839632109
    0x1c0f09080a110f0301090201020a0215120705130b0c0d0c060f06060801090b030703020612071e12050109150b0c03070611120906040b0604180204021c0b040204030f02100c0c0f 77
    0x140000e83d81604040c0260980a81c040c1c004100d211419400c0c400c003c1d0f000010305220f10000e1010102d0508840003450007000266070706621100c80d4019502251125403000d07050f00010400c4400e40100822100c2080711903080008410401c0e0804001824241700301c100340f42d14100021079030a811585d814183c1d205c0c034404000c3c1109120a065681940c0d02001c0c0d0300c060280800460070394113110b8954441c0b00ea240008451400b0f9030707801103402e1507048401c0411076040304200e4a003401c0c49090700400c445c0e00140110000c1000084185260b40290402d00c040050030b1018007a08000700e9101070341c061010005602c1240000702e0f96000440960f00c40601030300400c10342c1c540000d48038046c503040110070703a481e2600000c0100a10b0440760b007200102600ca0083d001d80d460f840941a401402c84107801c3c10351000000c44c0c101c84000c0c0f180c1d8071a0344148801d0010840004100350307940d60583d02200240e940c55001e0300c40c01c20350480180204080440440d0903542044050112804 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 839634595 1250 839633345 839633359
    0x60a18140709061211221d19060b0301120507170f12211503060a0605010215010b030103060b030708030d1506030e0d05030703140405060411031c0f09080a11 69
    0x1440b540081581c02040349100c070317407030140301c0040c5286040c60164841510300d409070020030b540c1c62405010070b0242040d000104018070801114015054203030300c4141c0164000c00c20f10742854900c0346140018018408190f140100700d10402500300900f401410051418604a00c1c000d04004e5070317007a458101c51290f0080340d042403107501c00e84003581c41c02c00c41111500c88048102c4a243c090200040c0400410400c040043c40c1c0f544041c00454011040d00c000420203505100001e07160079981c0c00c1c0c003802c040d4800010030120854400356070540ba407005021901c1c005890000e490000701d90070206c4140000940d01c00300394150303480000c004288038022180c91f5039500e4160300309e48451503089096044004600350b040d11400045a11002d01d080c00540c8180c481504805003808a40c12203040d846142844240000c40080c4030b080d01c4102d004143c01c2d0050303c4901c181640e1804600d0510035004c0c0540009402107000c140a00f9560f001c495036092181484d548100035082040e0242070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 839635845 1250 839634595 839634617
    0x8030c120f250503040210030612031d120a150b0612010906140f19120602090a09092a030b070e090615070f0f061b020c030303060a1814070906 63
    0x208a904a040380c1c402034582c0d50542c1c0e920707006e108240004412107c2019a03600b0081800c02d444c000450340c95000f581c0e48203000c503805642403002e140c100303102885400d22a0340342400c1c020009080c0070062b4071803440e00194109152200150008150103075018601146054540028003030050407505540c1d000c1c86510740e200441c8900702c2c200b800300b6400c002109049a05030074040c000440c106001e040701c0d684e0503034640c0740000302105440215501c50b00050039080d03900e000c901c0380d805044517020800501900369904a01b11030343c1d0b8200248120b500700c1c00507501e00c0e8010b9000c021a000160058a8900400020070722000c50210038424841c282c049011810840c80c0a484100c10100042c549034141d1520007401007440d0085440031089980640002d01e14000c840e24080c003504106041c0d2503030f00d400381c100600c1326480c50090784141308101240d80c56200c19004c0350032411101c9601d0002a4110016041c208251811090120144542c2c207038441c0180c1300f00e43c5144c4e15421001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 839637095 1250 839635845 839635891
    0x3070509010305161a03040b040312020a03060302150f16030908100902030d021c030209130c03140f15060304020409060614120f120f0d0e0109062708030c120f 70
    0x9003840d6040f8140d0001800002e00188c40e000100c0d41060090811071800030301c2500300000d9a01403c084800241c13030b80c40800031800c0a0b071081ea103012031003203600d06150324400002c10703601a0307a41d4001c00390222000201414050198000642061811303a15413850744040140545003400080b07020740301d880250b95400c0d10100314000349400040d04440f00034000c50701280a5001000c51a074080c04403002114405500c0c810003030742c69260380f004114403200c040300317403100c410040800c817492160004118640d4003009511050711801c03a80709031280c0b05e41c00440c00030100440010801c9240007030105001307141d480c0b56541c181080303500403084d46403440c40d1030711900ca0700c4441c03405078020241092003049041c09420903040151080c3c0c100012040702c4010b4449101034154265981c12050301406524090301485c414a08102404a07603900b10b042c071a1081d215001e880c00d0008804942c00d181d056049410004407203403000550f00304002018000f00d000d07204594101014242003c0d07207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 839638345 1250 839637095 839637119
    0x812071e0803061f120e0c0604030c060e01020303040f1b18060f08030c03032e0b04080c040b03190204020910030203090609071203080c13090e1006230307050901030516 74
    0x10450b9458204a40100417248094074070007190802c0350240c412040050303118000500011802070130b010712000d01e0400c01410b4041030304081811034200300704210101d212400001da607030303070f00111031001c0c42c691450404001c030290708031ba4241e50107480e031540300e0280762708030b01c0c00d4170803565803070101682da2200140c0e2403045100042e000e40040c0000768030f00c50101007102a6207500019010020242c00b400440c04109400104012074040b506008050003041400034814040c1c07801c1140040342c100203907a46103010603003c440590944400c0864941c1c0d01502c140f001c2c00307852001d5504201202801a4008480e0481c81e8440d2500243c0d60300e00014500c0f044807054084100100c1407510200d9034001d0040121000d0380c010881c11040c840600c444000820151100041c0000032402c0541001541c50340810818140074092000c446445147c01619610701c3c3d500b84039901001c082410600c2d04d40c0265448007078800004184280405d14840940ca0824003850f00d075203450000c624 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 839639595 1250 839638345 839638399
    0x11a090a061707090501230d0203070203041e05011409032a090f010510080a020f0a21050106090b0703020109170927010506090112050114010201060f0812071e080306 73
    0x1550022107e24050007081d0384102070134188407192810340300c1141c101c1a81e1080c1c0d986001603000050821502407802004048161a20541801c803803030039000030032981c0d200a01c034184260001703803040300b80c4c0c040010142034540300c0c0900b08130303c0d41c1c06e0000212204101045001d60340a070002441c840210280c5030503607030000c1440744000c901c5d48003181c0001d00107150003101e80e4200803d07182070000074050480311045030b40d02e5400d1107a4510302c08400740346030460801942414018000c3c550022001d400750340c1c100100946031207242c10100c1c003511003000040c2c860802030081c410200c85090043c00740c82001d40b152121401c8105403809450342030780c50019200c240c54014001c503e00b50004042c2c0c0381051500c050f04c143c41000380400c8800c00c2e48080d801480006410400d9602802003030001e12040c41e160785038a113800c1c0703150740710701c220405100d031800000745100030070291504892031900512031740c82111080f441e01c24001d0780281c9003203201c2c0500c0707940400080c0840c0e281043c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 839640845 1250 839639595 839639597
    0xd0c020115090905120c0109020109050f090f060105070b161b0302100c0e061c0e161712030f01090b04020304030c060b060d020c01091217011a090a061707090501 71
    0x2500924059000c00200205981103680d4040d4203000e001d80d05c072540242c004104c030100009a0710200e88000740c2000c1b61507000501848010f40c180c0c2c20340e9200110030380d1100f50030b1030030601c03980e0718001240c00e4490030710300420b800c00400500c04000e200202032481c0c01c419440700e490801d81c424803815444103007640100180e10681440b8a1320001b42c005034a0b405403800d20840032075810001642c950800c40e805200300d16844564110000e1718000c2e508410005005018440f0405205162850450213055043e4201d030b2004070010104000c50507220b505000003640364142280400ea480d0000c3c071412a00c242008150409490980700712030189516444c0e031003c2c08078035691200a01807a24803954800014426103084884500050081d840c03c2000080d00082c00d2a1001a0428003800b2200f003190581411608122050403507040d58233102d50108690325150020f00726120340c14005400641141001a015130082211104405642240780540e03840341d034212800a054440e1074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 839642095 1250 839640845 839640881
    0x3050c0708150a020f090a120302120f09010c0f050303131401020406080f060a0306050a1d1513060902040c080412020616031d0a0c05121504021314040501020d0c0201 73
    0x1a00d1501554000c00e16903170210501c5003001d10010000d120a02d00d9813101031440d0301c030b03d41c0d80304050703061100b242c1d80180c02d01458105410a50004038500800e00468140082403112800740a06203180900071580242100e0796450712500c0803040400414003100e80343c000d42c41c00d8800501c180282d90540b8416981c801d900d40d19a5003500c0031510140c01580c1059000101001244180c0251441044002c030042903040c103035180c0b0780201a20b51310651498200c64442d100c00d103811103259030002400d420705806c84005050100090001180096005140c42040002c1540013080d45110f00c0c0660540e4a81c024084402c0c1d86401c000c031000449843d0442007440414001c2e0b00212408403c0c2c04903070361251940303804518241c0419002d8030f03510a240300410142c0341441d0500e880d40b601c803001d05291065000c201c022210041c2c0024418054682083e001c0155540108102494014014a503042a04001e4000e50006481d500054201413600b803005005002d40c8003c4e13a100350940c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 839643345 1250 839642095 839642101
    0xb030f0d0f030c1211190309050c010305040827090604090f08133201020f070603050604140703090b10060c080a02160602070503060a050402010509130e01020703050c070815 76
    0x882c02420b030001403d09000d41005480c036903042900c1000303812800b50118070f42d030b110a542000800c0d41240e10303000c101400c240e05d071000240b010894196040003030074081b41c0c2e515140350617003c0e40175200001c114060040380c00540c68030722081902c0d02c000180d50a0005484440901c82500d13a20701000c0e010480240c42d81c00051b140000600804007a4031411a01c181c076840b007846043d00c0500711a2800880c2d4080011203400814545480700c42400102440c43d100d007001620f80d5054842d0400b4950f0310300015070300340c50320f0300035602c01c1e41400e011201e03c1c40c11001c0034008060104c4240e400000f40400108403d044003c0c8900382c035401d80303501100b084550740b03002c0303690702540129045000340710124000d103c00303204420152810760040c2c980e140c1800281840c194004202c0c1030594104414040543d8000d0f0440341d41745400d6403c1c03e0b8407846221000c010f0904903020501c00e40c400603d0b1000e040d0300001820782840514180c0311920360303030481e07241d071682640000003902c1a845c001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 839644595 1250 839643345 839643347
    0x70506060904050f070f0302030d03061a03090307120807030b030d140f0c15091002090d140f0d0905040e060f190e0304030803070806090c0a050a1b060b030f0d0f 71
    0x10ba403003445941181d0b02e00d0001d0504504000450303100040c2d450b403001007802189002e021500d10b0180c00e02c0e003008124a4411086010344400c070707142d04508000400300300e040070140215500c150304480d40102c52010705400400303055080310c00750700081c940511f1901d1445d0209880e1108250b550301e15404446640708003441c0e502c40b0448102c00b500c00c20400405030805d0010804a00307200c013181405140c90b01d00c40b81450b210a402400c0d0074810001d017951640c4400aa014154000c034a0000903820130600c5450448800300d0b029051041d04060550280e1200d02c0e803050f86e2090303400384001400e4840c0d00d0b90301ca6056030000c850403102c0000401041031040184400701220f2804034140b4892459141150b2017078100751008000082005849034104982039000001501d851f4854a405125400c03030303020340d070620b404005000420406803417281c035901230550780055100000c0b5505240ca8001403019100060184c0548441d5994800d0040b41124454000d1b8460b600e0005000d08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 839645845 1250 839644595 839644609
    0x40e0705031c17010306050711010207022b06051504290405040c1508040b0f070c06020d0e06130c050108010609050409020d050d090303080c0705031b03040b070305130b07050606 78
    0x140c4007082003600404000c00f0710024014029801854001501c2c20700d00301c001c10b032406121135211540c1c0100058401030300c03403c0b03080102c030340010703030f451101703580c02030072026041480501600150074103040c030103041100311001c02300020884d02082000807010340c10009030743c1c030f4030080721a2143c8101c00d5503d0a0a410440e0301030f204100041c1c40d161140315607001d60140c6100c2c0e00000c1c5180040100300603c1208140d003140c0c4c002d4040c00ba034030303140740c005080b40301c0044001c207e69004900c01e100d10046401c1440000c90b140180d44441ca00300b010094094508030701a44e03d018140400903c55001c1c1101c0e50694000780d86410320702d420001800058021014103d810100809800300031900502603071003a241c03950b4070030701454a541402420403901030309902c880c54040010300300040c00001210010115801091515036010141c82e003180656400b01070136500004121040591180c000c20000307400104092410792214000758041c0184000200158000008074005241c040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 839647095 1250 839645845 839645893
    0x608010b0702010c0f050303010504050604020c030306220e0f121c02090a050901030f0203060108010c2007080d050304050729070c0f0f140603040503030f040314040b0306040e070503 80
    0x81071405130031081c1d82d20104160a40e0405036140d0700b0100042c020307032406004141c2c2020007110305500b08082035610989920010701403911910200506a207a101c00a0660600410204e0101304641030003010b07a0f168142c40c0035031019801846052080400001d003076604081c0240601400d00f0782041520009600c00903006a00c03542d02000042c09585050300c2034042d5110b9100b003c0c02e2840e500c18903141c5401038101d442c10781d040ca90140d03205030f40721182e502d0b0100310003841d038608140c000c1ca0b03500b03000c000d0b00b0200550064103d0382201d1600f02d00110b0049209000320745c0141c1d581d40100c0701d9a500842007905542503403880e030340346107410800380180e40d0048400914007035484109052400c5568401809680700030000c100034a0840380414030810140c95061542c68183e07110b9490384001000d482080560b500850306051183c001d82c00440303a42d4194550710b507101e2018040580045848034462400c098450700014408240c01c3c0c115980030b170043c11300019445090101101c50 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 839648345 1250 839647095 839647097
    0x40c020d0f0c150207111503060613050d1b0602010516050a1707030b010215040c1a0d150f080c03070e1503030f04060906110a060b040b31060608010b070201 69
    0x20310011030210701c5071030f020540300a40d4400141e41e210280781c0740f00c80b03500f12a0031900c00c0141c000c40c0b9002030b491800f1030fa0b200d40100d41243d60396150b9500c8945c03000194120329040240070040c24100b00c0c1e618160030000e6050301040d03104230394a001c00c0b800d984049500402c1c010320300c440600b4490280300542209181818640f4080c0c1d070056130498050070031a14100080e4448000c24040d58062055241d401560050b001c442c0c54140c88003001c0c40403d1140350f815140048580400c860391505072071071b0510045090191203400c2c2e030200c00c500e080313001d5117600720401d16001812440c0050301040206e4007402610b021490000c84074a01480100840003140941807071101c0d1380d83c144000e1403004100e5545c6a1618107044008180e030035950000b0041c0320f00c11451a02611b03000426036812b0b50700c500b011455468000120b0040c140b0b00595035001207020040c688100c981158a0403516a450540c00c160885454058140c600f144200004903410b2030040c05128900d000a10000d401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 839649595 1250 839648345 839648357
    0x1080a02090414060103060b0f0412020301140a0b0f040501120b06040e030703021c0302040501050d2003090c120606060702040908040f03080418060b0a0e011202040b0711040c020d0f 80
    0x30201c0402d00365110302c20004800001103041140d99138051043e03002a014980400e070810402c06076034945449180207a03031004a00c0d0381081c04640d401d4102d425000c1c90f5442c00d021a082a0901002601d02d84a00c5841010410b0201c0356034141446814100e030f103030803040e00e004203668a602100400180c07015030003036150100c20104220800c000d010580c481e80c003c00220851040901c0380111980d032070303c10540104004c003c05c1e030303110080c3c804810307100e400081c107407491b0f580e906d445035591200d900d8855004810082465008a036500e20024103644030003a02016003405601c403081100c0041c0e00c1402032098001505080d800150441d114040e80c1c4d2906495005015840299038801c4440c2035001038280420b600d032232075402040f52003510500a440c2030060103040c13400707020054404c0152a4402c251070ba845028090007003410404115610341c3c65280780c001f01d600c8244160707031080c403481d102400c9050501c50341440c1c041c20340c0640782d1111303415411528405015449820455 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 839650845 1250 839649595 839649607
    0x28121b0f0f050f1006050f010801030201050a0201062309070c17070245010503120904022a0129040b0607080406170f04050c0103110705070b040302091b0901080a02 72
    0xb0820403a55100b9a00c0e006001040810701c00000f500c0480e0442d0b405001e900c2c400d1044c90b608042034505495090a26684408031110128010030050340103400d440c5140c0c00700c00d5441d56288402030f1130074080c0c4000c050355442d80c100303032100a500315005041c3d042088011440081030005050110320050804460215098200120445d9400c4d12000003061a0307851680141240504000030314a0a0100700c540c500000252148441441d800c800040000c0254031507440740d0440d00c85500c0040130461044504208801c0b485800003400015841e00503040d5170100e100e140d0109413042c006400c1001c2082406000c00317010041440703034000d1014401c3c540001e4480d805440030b0f202d2961081a0700f000c0350001610b8040103051064650140d1040c4804a10040307000c50400f8401c0c00d000c03405054500f00ba032a640301c2c0c548060054003c0c82c101160b0f00920500501c01c6038000c41d01001c090b1030b1380c840b1440e6000380305040c42d9174140800c00d014480d405620156403008888000604102d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 839652095 1250 839650845 839650853
    0xa090b12042940110a0b0c1c0903020d0f03050417010e150c340c1403030f0a08130204110c060c0309070b0c28121b0f0f 53
    0x9605803543c0c010703a0960010302140d4003660a4049409181d040d0000c1c412000d42c0d00c002140700300c0c42c4007034450714480f49003000b80d4885031020303c0100302c40200c00d991241c2c0c100516484040404c0d070019001c042c06403081c1400c1c0700d05181415203400a000403801070741c07940c2d041e195184440080301032010600c00040e211490050300880440302da00040f65505880030b08506007a100f001c1c5442c405209814002d82d11030000030b0705ca6818400c242141e10402a04a04003280044820480f0702492010081c04000a016418088810140300c00214a1f05401010b0312800307045c00c0104603200c140142010340348203e03615504078a80300c01c41d0380c0c40b0b01d1980106041e034108181015005000180c2504050b5003000720b1607102901d4040f0340d066081030f4144d951241158070601d00c0c030040228484000d0320b0b0a106880030301c0704008102c83d44000200444042040115040d0743d8140036680f10740754180618040346080f0034240c2110030402c002d55400d100605141c500341d41d02d4107084a004001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 839653345 1250 839652095 839652173
    0x22e02030411030321061801030b04050709050c0d060b3c04030b1501030e191704080d021002341406150a05030c0103090f0f080a090b1204 61
    0x20440e036444c03000044412401d40445d811020701814091158808078403284125101401c2c1900d43c0550841081e48807070038480d10b01603558000d00d0f281e81c500b800b880b01500701c03500184400d0305050028008517603225145020b81c01041808008156007040302d00724140c0b900900c4410041c103500030351004c14540c07001d117a07030b0704160400c40300c900e1142c0a000343c1c408950328032011404e0034038042c85a05a902c40c0305851b008503076051050340310380c412035000700085108807a02408240480319101d5640e0342d0030300e03640e01061040710007501034108031013444441da0086420040d0500100540c84180700144410301100f11000c00020b090920b00900180b81c100ea211a075680c030038010300c072a00344403140455041d0845242849000b0203103003000540c0300030072000c2851701d0900303000800401904001c0c120181e041c2004069225a15814040190310740281a01c9041540c0c2c2888040e2200c80940c5503100780341710070000322506400140012000b035100500d5079140c002d0603400e0f0210740400404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 839654595 1250 839653345 839653357
    0x10203011212140a260415230405100501120803010303181203030b0108130309050915030a0303050702060a020309190804090e0c030d0e06030c030a06031a0403022e020304110303 78
    0x2e060344002030500c000011440c4441c60705540d18604a04042e074502e100468034000b40c0007c5515403210030b282c1d600400c02d4a5854030441e07101e82d01ca203046c3c070700540c0f140801b8110f09011840d1500200e03000700100e005c9001203611804403031440e400d548007542c0480c600b0110003011203074503001245250b42d40c0d80b0f0f003c00510944011030700304606000580310040041c00ca001c1c000780c02000c1004664403041604c210380c2c044e205151a6100c0803403200801301249101609440b81c03500744810141c0c5588168442c2c4043c0c0e00741c440030344400c10b150081c0c0c8000d50302e61141360301008121802c000050f01d82c044d030a00c94400d031071425940b07209400982d08000886600c40d00103049440c05814203108404604c00d0500d00300154000240008440c4d000c050212a02c0715004000104010403a41c00034001d140c1004031300b000caa1540411001c04081103d0450041c01900300e8000e400444d03e2701c605480034038900070301124009030441e2009420042c0282c88140d02c100c0388005a44080c4000c0103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 839655845 1250 839654595 839654597
    0x60303040902160201080c030c0406030f150e07090f2301111902180c0a0f110307060c12050105090a0b01091e0e010b03070c0206070204020d0c0908010e010203011212140a 75
    0x310f50035000151140e00b0003440481c03d10801c2007040390301d80d2020100c0342900c442d41400542020511029002880d0b541c2605c00d04041c40003011508a5403011690300c00c02c01940c0f1401d035240c403041d1005071142103108012102c00c07002c4080512401052102d51801c1d810701d0030f2040c2180c0e904003c2e14141c540c008081580308035003103074810740c101022442c00414040341c4076100e038200560b40503121310640e01d201c81000700b15a20924600c0c42980b6208140b80d0a1003140d8a138841d41c00c0040040140a91080108540c1c0e07443d07c0d010300c0a0b02415040320b00c002c1080340160340c0c140e900c0f00905210000075040005080c000f14103001828600c1503403403038603260b21000300d05240c03480400c02c006130030524081005000700301125a00c000501245a030650381c1c03c3e26034101d40b000c180640140d20540283c6800c010b06074140e41c0c3d008403041c0861f400c0c1c0c0c00030300a9026589006080784400e010740706007106a0060880496042007101603a081140f5000b60724001c2603c05540c6500f0454201d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 839657095 1250 839655845 839655877
    0x4081b04092a0503010908030429010306140105221d15010911280c05151609030302030f09190b0901030605121e010e07120219030201050d05060303040902 68
    0x81c48081802d0945000d0700c01030340208003551864a036101300703000040005249140c1e592010b20440c880514990144022781c1007428196103d190490141024000140f5242404400010310b4a49004004109480549031031801016082201c001d89044e0301900d0114900c4205000001400c0140010290040c051541a9418500140e09444d045099003021400c14400090280c00d40100c04110ba42c1303085050000c40e030742c44415100c02d04c040c040a00a03015403040700d20303a80502c0300301502c00c401c0ca942103000c91744881010345111406010260050b8070038010b0803804c205a030b004040300c200040c01d02c0c070304c0d201c20603c9a152001a812003d02c2081c08240c024465805000f0140540781c01c6400c8411070f002c04102d03941d079145102e2200904e0f107805000c261085400c1d84510452016003055503003e546071001c09510031812081280920502d40129955503100403c14060302e605030f440c1840e0400301d034800805000302401d0700784d05020420001606600510092546e000398520076 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 839658345 1250 839657095 839657153
    0x506040b1201050a030221190f0b090f0705010503060f041803030e0a0f020d060f0614030708010c09171501030b04110a060e13060506030f180304081b0409 68
    0x107440360069110a01070710441400748016601c030b420302e0841d4181c00801d003041d0180442c940d440c1c40d040c440c0740306d0114904540c107801d2101114030754000c90301a040c00074094407290840d541c0c034000c001d0428010b0300000c01c240200c2d0b1184e40116004200100704402202540700010110f45861000d0305103580c0d02d4015804160701070150105980340d41003c0c1c804004c50307444400c08003d41e440d000703200e0744119242c01c0800c4429400b00c08058221030040086603143c02c0c00589480031000c03410300c64420700c040040d91840c14020000e40c0446682c0c1d03440d040e4640b40340304007a8043c00303964070b0060180c02030344c1e00f514074070304443c078000d6000307042040c098105810900c60140003800040d0040c1041441030001940041d2051f040c0705042d6942d84010019810030002004190807940c2d00080000600540d1034552154a0142501c0a035164031079845112055691203903104203142d64000c002989020366850030302c1a2000005000810440ca540e91541100503081d00d03031f4440302d000714100d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 839659595 1250 839658345 839658367
    0x1404030828020d08070f110a060f0e06060a030f2108011409100e0a1d061e01030c090c11100c0f03020a0804081b06040c030521220506040b 61
    0x140360501c1140060800145140d00c0145002c80040844040c03145d0010180303401c901c02c4055400000c268815102d484d8520710300b10003c2c200902c144400c141c20403202c00c807507100201e0990300401004280208240c51030b41d030100205d001c002c056440b045d009901a03050800300c403032641a1082d0b503452048940c1008400001040480d1216008400d0b900810820311000c0324020143d50402c1314041b4140ea4a040080c0a0802400d842d038001183d1004502d065600107481801002210408024980c500c8520401345000340b00140000e9441c080801039010b241e03004c1100c400640c541103165000c1040003034a000030a45800800641e107100d04060103520141805031440a46402e52a101c07009100504141010784050800c140018041c0030000517001d101138400b6040c030558001d0300e0542404d04100b4558401620580540000c440b09605440c0040700800404000c01c0e040199084007644030055201d41c201c5a0074101002107202d5807104050b0000b00a070781b04165440203950302d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 839660845 1250 839659595 839659657
    0x91b03010f0315020f0a140f0f030618040209010b210c12160f050c0309191508011212090b030109021b01060503071a070c170f0d080714040308 63
    0x4411030501c1800300203210003541c2c01b00c925000c024508a08285000e15468082e849405440700395a4800280102d0200c0d001d4095842105c0c1121883c024803182000840032100450740290311100700b000501861404101524807030280d600d03094005e41074256100d402d10740075508510840da020a0000091500c000c101d039000c40041c0c51040a2a01c0d440050060f40700d0103500700a0103400728402004800400544445100003071000c0c40c1d6002c248a0100c00102c20700134211030024600a80c000f090084141038105c40f400d40c030707101c4580c0301d0b52900480013411a1000007002400f900020700c400b0248040c41c040c10f107030200185d0340d04043d114042c003007120311045042d517414010308200c0742d0b03004a42d5408546141071400105d081154a02c2210701c645040104261280c0c40c002c20307a5102c502e0300914005801085503141d508221507542d482a00c4205200080c01c860005030b844c0b4400c004458110749403c421a0070729440c0d9941e400e0a40000015052000c0344040a0b007040040007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 839662095 1250 839660845 839660873
    0x20d1206080604080d0b03061918020a050d17030a020301061d0105090f130504050309031603020906040507180909060501050306131202010605040f0b010912050a240906060503210306091b03010f03 86
    0xa588040c2c20ac0daa90701203140c80b50244103503485804c11003201c40900c030303241d8503044600c003542d60001e41c2c0f4588038100b50000c0d00b0a00525000a2905c3c003160003000c080c034410403010405850382401c104200701000403400103130498a07046001c0c10b0726a18041514016103004a20a4015540351020740080c0341c46e198419041c074061000c10316080001da243c0d40a62600004141d801103140e43d00c410042e2400b007410b0703150714010011080001070301c541c56071141e01c40c10b1107043c013444540d030307a0020183d5906054800e043c2d4900300b92001c0c800500044180c1c82000718500001c62002d5032400010212400c0c21440c09019807102840c0c5041d40c1c0c4071000402801d80c0048134030000205489440d03544040c01d200620352414580941000002c80380c0c180240900c1500600501d002c0e0f10b49035019180274441c6501070b2080002a05a105159403261040c50060100c0c034110b80c0e80720208550108041c0801c211281080940c0c0e40b107001101c000c0d030103464580400c0312a949546000d1040c25142 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 839663345 1250 839662095 839662121
    0xf0601031506090b0c010612050703030f170a0b15071b06050307080420120f06071b02091902070b0414030f030106081005060307020d1206080604080d0b030619 70
    0x44407041c01095040852072081c3c0d0036030a60982c0302c006203a1034a0050032103400142142814000700000c0000000f1004190303071003941d841418401c1f890040d6140ca17980101b4022104110002400d403510030b40c4840c1c10381d40700a00050101c1c02c141e0744a65141d0042c8e2050f2060001000815401070308604400000c0140d8603001c0d1441c900547d004085400c0600002c00c0f0007002c05040b08001da0100d00c0d074082180040c0a10501c55409106c140d5680642c01000305070b003c1c00d000280010301500c410b007503500d90244c13156000030069007004248030b402401404c1d40d03150200e68940d070003a05d00c09490100d100d008040040d0615080c800c00210b0840409410740d03000b041101040002d42040e60f0445000781000c40c4a6140c20b20014001461500f0454103e0b5000c810418110380c0000c0700c2801482603196100d0711104105404107031030040c041d00325168000c101140008103484028000300ea80d0050001381207004000080c10100103440c100008a4814a0f8004155071362190505103056 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 839664595 1250 839663345 839663381
    0x705280e010e0609090402060c032a010c0c050309060a0212040303020c01091a040b0d0207021201020d20070b07020a0813090c0e100e0d0203190b0106211a0303030f060103 75
    0x151340e0005548440c0180f0090040c42c000c55100745038603003001615800c0215100b95a502c010a40380002003407210103800220f0343c20004e4404003107014146480707295070000080d514003040a01840b0850b444544d96004610603102821840305405010300061803207503026101c0090100001031401119410030055803402c0c1a407004000b503444115011218a6100e00c0c0d02c0318407556120b0001c0c0516140a9000a00c100714140400c1c0198018071000800140c108810100041c00000044d03c2c426403030040030703041000354007044c1d1310091160f111a6510494200090b0760383e82070314a070000040b990703481c8a000c45c1800244424000c40c849291240307441c00403d0500c90000c1d043e04001c4000c0c1043c0024980110302c5503d4030f0305034060464024080f103032a40d4113841402c03082260b01900b40ca0b618480c20010031040d109005080050384511581541d102140c51060020481c2c088441c99001c00c000e164102d546007480a0b40c403480808200b20350a10b060000074040d1039a8056040d002c81d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 839665845 1250 839664595 839664607
    0x2030a020601060e0411030f010302030f01090503160507121b0e1501141b03030105180f07031107060c020f10151406070c0b07110a030b0705280e010e06 67
    0x5800107066045450f1441c1002843c881ca42c0490020300032400e06200c041000010002605644d8180904036407007134003280e030300410a01d095400c07190708001c014802e400070007501d4802c2001c1050740489030700503019208010703038400303681c07a80c50200c1c581110031403440c2c0e00440358903103a064120700516049404c00d9543c6003500e0f1001107400c0c0c0c5540f1b5814419904550040b2000719010349601d2100c01202c812085945403549503650002d10800d8860798895901702e800c106c5ca104000e003d0074200304480e886844c0e400e07081d80545920307114244914010700880011840f240501ca2082e4100d40290600d0100c2880741804d0020004014140508010700d07004040c2c031a60040c42141c0400c507072048145020b1000400c90300c28054094802003410001048410000000f000030300d2244800f02c026a55036410f0000d03501a40c840504400b00702400240c10724080c0c00105520000c2d41d82412075810780c0001c000703c2201d5049000e0024007282691401541c01820741c03080034a086070310b142021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 839667095 1250 839665845 839665847
    0x120a021c0903030c060507181214070605030105060d09170405041505031f020d0218090f010f0306180210020106080705030111180111010e010b0a0b03040c0b2a071502030a 75
    0x49130010082c40c003641ca030006041c00d842440b003480c0012400c04103004841e41c83c1013003070844008490540300c0c600075104a40100100141038011583c00781c88450460313107840c00700a0160031642c00034104607203481d2210000b44401b4040308411070010103c640b56030a003030a0008541c044130404200e000c01d180305114582e030005101c900c8180032480012005c00000031400030740610305024200a0002c17464161720245040f40300b500842c00d40fa0740340c0a1f600e500385504500c0c03003881660034040c03e0100500c08542180c006403441d140403c0c15004112259000c581204106c502da030300142d658030820700c480c60007807203103030010041200240003041180450003000d00c038030003644501508007800181c159024007113a441000c0d1060082040780344880c00345010303000c0301d80c0440c45000d1040020070855041c41c00d80e4099900038400045003410401403c01030760000501010240920200c1d45481794106245201401504080d1420500d803242644010000f03401c0d06066406c01e2081c58462 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 839668345 1250 839667095 839667107
    0x305041415180a0f05031e0703050a0e0418050625050d0e19060621050a02010309060209060a030e060c1207050304020a03060e030c07080f0a020d05120a021c090303 72
    0x400b038000d88481d080760074200c81618016003403034000c0500410002c00800d000340880078081540081c020040c0e05a42c2c3c1c016144070380700e9000000c01141d02400b100b001d81d840f48010706a603a5004c0c100280084886000084411014101b11400e0340030600300031130103172b0300c0e50f04443ca02d0303151901e40d0094890303000c003074114002d807039001c4059680c404001c404400c0403c01560a54940c45070401403048605014002d03008602450003449210780c0741d41c0c40540d52107006a03200303400c203024048158095004401400d01e20405581c420303000c0c07100781e529550746c500800080d1110f0310009003007800e030f0094900706240142003408226051008103500001c045860740d002e01c0c149806c5640356078600c0014030441e1150405070095243c80319020400b01c00000500100c45548115503007940e441c86c00d15a200090340c02c0142d207811540400c001820600103544c100b510801c242c0c2c0d070700040041c08031015000a1003d40042c3e00c64401112650b10310715010340c54145c58034050048901f1a2406080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 839669595 1250 839668345 839668351
    0x1a13050a1a03060d06110a0806010503060a061101090c0f14060c0d110f010501031101110105090705010f0512100608010f0f060c0305090901030302030a17060f28060305041415 77
    0x26207180000015042d40e9408480c800c1d02d036000200300809160303038079000140d4100c3c3c00000049072520300403c0c140d60007501560b101e40b42c020700f019060360414804a405401c1c100c00c2d030540d03640b00c1c460310002600d8914200045c1480c10340950000b80b6020118501080916215014200c02c00400c034101c0c3c00801e046280c68504c1c10030350900c0b005141c2c00b5141208070501400343c1d510300000030040100c40703401c20b0246034099848042e0b5001a07496142203c800350f07114200c40d8402c01c0101302d103500170203207010441c5c3d0034206182080400d0044501604040743d048a14040e441e60500c03115403c524807901400040041c409030905101015492500c40e01800d0309114203400b401040600c02c4013140d09210001c1c02c401c8003565680350103556034000b42d0160340800c0302d80b0390072070b800d04a0b80c01c07191060100030301040c80420030b4001c4c4440464440c19242c040d007080b184c8448006041102c603c01400c140e40c0001c1d4034505802c2c101080c045229940446401a030315085020b404a505d03030350 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 839670845 1250 839669595 839669639
    0x303020f01110906041202131109040c03051003060548040b030c1b0d11060a020a21020417030901140711040b0604050406120506010e0613151a13050a 66
    0x580e400147c000140050303d40c018885069003080d246595108024015218a200540301070010345444402070301520070884c1c02d00b9010030b44820410200d80590080c82d080710300750080741c41c41110070b01c01c030046403001c0404078140c01f03200c40d0b2940a10034001c8810302c441240c0c00c41c1402c1a01b4246a80b070f20f480302820300d40d05003a000c110400a201040801c05500040d10100d440403901c12502500811000e4281d640c60b005040c005044040035000702c5100c40401c0e0b80e00c07007821003884550282c9030020710301d400399284d01b40400715040c1e44150003c17078004242c4000315124080760000402050740d00c10783c4401a14180460000262140154290400b0440740420300c0c0c074040b4042030320b601459020b941d0041c00c1020000f001d885250120000900501c1076541680e01c1d400700c04400c4009407500d40d0405c460358400c481030385056104000e240000c03111146580d42d184070705e81da0300b00c0c40e1000d80d0805800003140072403c1804010040142425940008403914040c44000140514a0640 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 839672095 1250 839670845 839670869
    0x3091a03070c1401020f0a11060c040f0302040216020d030206190c0f03020903011104060309030305130804150203041a1902070b0d09150213030c0e0105150a030e070303020f0111090604 81
    0x2004400080d01a02c0004d041091400d46510f2800e87c01802e00000c260040031a01800c4040340f030300c500744421182070b101c0010040da0032615543c00d020003580b10400030091100510160310040e0388a00101480368000d5004281c14100b5032080303000343d00b904443da01100c1c500080041040e030004500070b88240107080060306c0390b81d440c0220340988400718800c19401c800080c01b00b070640d0103a004210840c040c3d94100416501d030414907112004500020382494028003017041004e042c81a000701e204d180d0710580f0308240d075527807260789030780054020b41c0c2c285100400c420b129000c154046c1900001036100030201c03586025000c4001e0b1141180c0021034a88400298041c000d1180f036400407004610021583c4083c140c0d402c48114142c0d00080700d461403117034000145403100812031360594000402e80b0117200c21221310031000740c0c420b4269100b4140c9801c00588121000d1003e403006600a8000d00f1101140d10701d440c3c00c59030035901c4010407400910640800d510780c0801d03a8142c41c0300000c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 839673345 1250 839672095 839672123
    0xf010509090f010c08100b120114060c0102031005040b1804110301110d0912021605041a030d030b030613050c0607031806020a06050130031b03091a03070c 68
    0x45081c0b10351510400055824503035103800035a13000d0142e40c8100c101c480e91840c11901c3e5521a0254842ca044c141900f2040c440184980c11100403112445a8000c2c0b00d5407134003095509035800c3e0b800499070044c205224610401007414580203120b80020111240040208104c003503000d22180500082e00c6403c0e02007030084180c03402d600003040521000c0d8003d480e0150f54844c0e101401c1021070841b030f90071000000c14860b600009103510004105002800000c0c106010b01c8000c100300b00c100c142000e85107000060a440620120940b2526541c0c0401c02c08204000c1c989401001350002483ca00080382d07c00200300e000c101c2d885510360864481d940c0d40182c2c20100d4114109a441c2c90082441000002d084e68000408414076803180c43d080c0026a40c230f40107400d202158289000349804441ca1071190386820b01402200d00e4030904005140090682d003015060030010821001308083c56000d20800a1449514081d4102d454034a840e5150201e001003d1440c450002451031000d1964 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 839674595 1250 839673345 839673361
    0x203060f090c03100506030f07060503070c022b020909030a021f140106050703110c1521010b09030609010c02032224120603080906180a091d01050f010509 68
    0x202c1c250704900908807440fa40e04081a80000c0c2000c0e10268030034171906929002d21000400c81e8801c8a00c603846039030655441d0a025502050514412680010304512807114006044422283d181d40208000c811040510510604440c00391240c005940244146400139600062140740e0500c00b140441a01c650410300038050940070030041e0700ea070214400481c3c41640180640120350080d07840c401c0300c10300501b116848070001c0340a81d410200010100f49080c26020062030005079021440001402c17004544007249001c2e00140040000014840c10510b0108042c03500440300300000c0100800e5000007035502e20a0f181010b4002000c1052524428000c01c0ca05c401403103808000d0b07000c94500d00100c05442500718400703004c1030821003000071001042c420442078980c008c0a9910f032900d030b0300030405160480ca8003581c88103d0700102d840c280d22000725400082c40e01d8603010030030404c4091601410560a5501d1950360300d49020441014041d9004030f04640e010740702c540d2b0340d03120880 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 839675845 1250 839674595 839674603
    0x90f0506090d020a0e0f0c0405010c081c060b1e190c15060621050727050d080414060a080402040507050408010c0905010f0c20060412030809010f05040203060f09 71
    0x240180d4052002c903c0050310007404170500e44541d00c514402c6c0c179151740700b01d40010301d8065030040300d00003150084030000246004004006900f4184c0007004001d450200300f8042e140f06401c03195071810007207500c11002c0d0b00c503503520f191410000c0e0036a061003d001010b8111140c03825080082000d85d542c801d060010b0611462108403001d2414486240c4404010304540005022aa0060700f04909400f40c60307400d2282c02d0145840f070303980600c0c000b02c5200a030066032440001c1c200080042c840014159900c46000740014800c0300c0b43c6841d82c0c61301200074001c0c080f03a101c813406424200945c010aa0340006856885a412200001c081c2c40ba82c400310340500841d08040019807a00d8840c01c012500014000c084031000d81c0c0c3d0411911104400320f42c03200c40b02c0d50017800e07811a018800c102240e0044061401c0c80003030051401e2540d40c4c6174179030b100303514240305401003500b00307003030000c03190b401c0c003600c1e203e10841b1794107101504103540880d80c2c802c1d00800e1103141c5812000818500c140c140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 839677095 1250 839675845 839675869
    0x80f121b060c1201050d1e0503090d0f0b0a02190f0513060e0406050301060b0706020c01111621051605011e020c0c0d081e12070305060907090f050609 66
    0xa0125585071074000101c52183d448007070304148088180c2d0000480d0310b403500701007804503030140303c03600034800c02e0348000d4410300c1d8180c003100c29000900c4501c045465009406002d540a07178010f940140803810034050300c00026002000c15401040310001640ba0307500c50f00c160190074502507405031080b03c01210940501c0242c0c03050605804030000b40d143d8450000301080300704031820001c15a582041601700ca08a200f0a021003206021007408505254041e082c424003075000410b10008181ca412240da0000c40501c031010307203828140e000d00c000d044240f4050740c0d0f010b802c1841e0808518002d00743d0300602103200035a02d010303110141006800e421a18426102042c1d101081c0c010302d00d40c2019400c00004120f41e840743c0c0c98403181914203e08280501e540000d42e20b490300440d503076010f0f5010085100c509c02c8801c10003299180303c005000039449100a5640000c0c1800c20b00304001c02c0390000f9003a2000c014045009201c4141c1030300105048503021142c0d0303a40c492040010440800300c1e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 839678345 1250 839677095 839677147
    0xd03140a0e1c21020408011a13020c0c03060726090a080d0e0d050a1215050609062b0b0111060106110703170a030506090c070201030f0f150f080f12 65
    0x110380000030f50043e90003038000d550100d0300a212001c0c41c1556103980700c5c0360082c0680d01409500c030710f007981d4007d58001c02d055405281907421640410010900d41003050300d40a0000e0038000e42e02d56102c46445513450f00f800c020f1680714041c14103900080d52042c030120064100031000804044a0702181e001c82d0102ca0420140d030007640008202030003503084240b1005c045018048043e140e400e85126400c0da4a200e6924071401300c0c1082c05020182d00211040d40c1c002e20100100c2991010f21001092680b20103c40c0001085215a0070030986000d400000d041c031040c40d403030034001800440e01d02d054414500d0004805840140c0c0e0526150031507001030585d82d80e404141f0034806038000200540201502e0a00164542c50140103100404450452003030f0380521a2000540c400e07045110041e4040c0c4011402c0007100340481c003200d6580b010a0f608a41d4081e0030440070352203000c40401020030802030550842c540700c502d511003001c400300c500240030000d0301050141211258590050312 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 839679595 1250 839678345 839678387
    0x83304181202010c0905010801031e05060c040807050609010c02010f02120a1205131e080d1a0f01110714150712030e0307020d030810080d03140a0e1c 66
    0x4107050200448000070500c50040d400c0114983c0120300440700c0c1411a241a56020f005078030b1a16002c2004551007055a10b079540101c440003c28010020350740103200440e207840da564609105245442e101c1d90005014001c10b000f018500da800451100c83c40e0b8080c2092509514100402c034204008503002100013400440d5945d80642e01c41d051215191500000700140d0f15000040751034503203014401440164440340c0302200c4080380c280c115010f84a095038505026026003907400365082c0385200c1c210845104101c050500d03215040440640007030820781c4c2c2000460700c1d070a417034003094052450303080140c02110f1400d840c0d4a01101d11640400074107600c8000d1861700c01d511a205d44c808000203410f04802a41843d0f0100840740042d2703004041d50800c98699a054502240040c00c1944410780794800003410710303003030100c050740800704e65002a80203040c804200c06000090810428603143c070201a0aa20b000501c11446044130318030000d80706902c403c01c0f9049490f100c01c6501da040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 839680845 1250 839679595 839679641
    0x7062309240d020a08060406050d080f0405130e0c09010e150111060a29060714030904090303060f0e0f070804050f03070b010314031c0b041515083304 66
    0x3002e82e0240c98020007940d03070b161043d101e060030030055a04a000d8903903c544803085020014074000300400c0c02991401206041540e124002a040c81030810310311002a2a10b401d82da10341412b01c1000889403003221501c80729410200070000e0110018a6501e0380400007503409107981c050940c2aa14030305007012100c0354a03103800560054108080c00100c8070400810400c2c964440c000032518200340540424140314071030304e40003030102400c0110700442c00100501d030b486443d00d000c1c19006c54004c0d140420080e24081c016201c008180d0f100304003040d01d107000d10403032420104003250805001c0c49c20005989036402c1c800c0c1804046841131265110014600c0200083c0001d100e048a002c1d900316500340441c05007164591151203006960340311008411010b90320168490310008070060300000710b40186041c00c2040c00b01c01d400480f04e1410350781d04c00c0c0c80c41382e00c6a6265401100c2c55404401c1e20541d103815140b510140d4800c600303820004040b6809a110b43e4001800840040c081d000021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 839682095 1250 839680845 839680867
    0x2090103020c100902090601020d02150703060302090a0510120c0b07020f06280338030708010b0306091504060f230402030c061e0d0615020706230924 66
    0x40b0b8244c0303040303001d4410340d8001409513001241d2580c510071260040c00616044001418a0210080806083c5a950b1300c0202c0507031101a5907034030a070800000002c490030074544464140325641c1c084600c51038a06e4036540003030b4035a00b80500b1a4421840c86440311464400220200800045150400700100e00f2030128480081c0320400440e1305460408010f80c42c89007201503c2e0030320860041c0e41c42d6006071010b420710410201502802c1c1000500e584e44038400002d081516681c01000c140e9190300010b4080e1a00340b10480c0c100a5140040c0305a42c641c2c408820018170050010309201c0e0b9514840007148190740069a84407000541c1c8040c540b561000302c1404801524164080d1084115003002410140304407101c90341940e054010020b03150140d0925988640c0040604503251500050000041c6620302d6003420f06402415050b420100000d04600e1008506a51654041d515207a4403850b0002ca44103039500b41c0300c120728000302c945610794405c2c250030441c400b01c00004d0000140307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 839683345 1250 839682095 839682101
    0x61113030c0501031512050106051e0405060a06020d050c030d06030305040806060f09010b07023f0102071e080c0607030204090b090105030d050702131401030b0c0a0f0302090103020c10 81
    0x35a12409251585549a400440889003000760b03c414008142c9000d002c80a441000710344071501c100004224542c42e00c0c0410080c3c01c4c03070f0490002d8180d080001070824a0035000b9194403c8003a074031105190324140009540e2440c4c01a0603050240015a1204801e030900840c2c2c02c045810b8002d01266559240080103a4010722800000303007e40404a101840d10402c005900d140040142c6010303424a0300c1c00302c00743e01044e000c80c3c2c00f4070082c070040000590143c0008050000c00d200410560000403281001c680c54150703c13072680d02c10000c079000544401c054007071441311540c10320b060f090300e4904600c083c0316080c51042280300f1441080341903035041c0c0041c0207449103074101f03010000c94070b828018a80030a0040701d6150304170280d440603103403086000d804603900090100c411302461010401c2158142c54040303000c40b484400500c24000c9003542e035a0490b5010307111518016500340d005200524405a505c1095000202ca1220760b120380c0540c0c00c43d04039402502d104082c150040002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 839684595 1250 839683345 839683349
    0x60f070306060e13020906070b0916120b0406110702220b0303120f0403090512010603050d0e100f140d0b0f04060608010e04050106031a330904061113 66
    0xd0818101207041842000c1048030f4900c05000b0b00d402041c1d2401080103908016005900300400744600da000c41c4c20080054000d40c20107001e0400d4916401c9088048802d03134000b18001ca0305540c00e540002d400900ea2544140c000230001b0303c110000d01d9a40180c802c40320080c1d840502d441e050400c00340e14980c0c401c1a110011000c000380000f52081c16100d014100d840c0d4240d42e90000021007007940b0840895000c0d101345848400c8c9910f51000581443c5504032002450795124030600400c881001141030019403420143d5900d4003a0340020b8500007009034020821408642119071213001e842d10100401c5147c007556110103603820320400a1100100c032511a204682c0340c0041824107203c1d08050320074555914002d60f0030540f180503818805030044800790b60b1540e00101041d00c80d81c0070004035054500045c1c542c01d0074003019202c0b0280080162440c07010b43d110011842421036400b01d090300648a108140c0d507075003000001000c90340d07402c0d1420701c800640741b61828001802202 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 839685845 1250 839684595 839684597
    0x50405030a09080c0109141201021605073222140115050f0304030908010204062f0303130c2102011404050102212715070203062205060f07 61
    0xe0b000c1c3c1c0d03141081c1c0d84040c4001000c2c0400c9001c0e009015101d10a443c40300081e03000703059405810420b106c41d5007203074070000440e81c1c0c1802061035101000303424055640100040039808800080f01301011241030840903c40000e1880c401d05c000c00d94440b000800304500c0403900309414942081c0341540940f60180c0e2601442e03104600110701004044100d9030320340341940d911410320034444010440c50f40094015800c1c06800300c000030b40c40909000a00180c501c07641d51594040402103140d40c10038980e482e510025a542c09220508807001045e26481310590034040b54a400c1800c151002c4003013500980400709032070b20140950b00d0f003040d040420354400e13602c0340e5010940c40c0da10b100364019030103001d0040e00038078580003100d1410014401c02c04195843d0720303d4042065040311184840304080001402034a002802074a0080c451210030343c681d4014038981100e550009848200082010803201d40d40940142c4943c06030910300d8880d60300008541103814504c1c4c614901c2d0030101c030b03558 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 839687095 1250 839685845 839685857
    0x717120a021536030301061107030b04030909050c07350c0102041d01080a0320100504020102071e0306090807050a0506060a0f060c02120c15040801050f0408040902090a0504050405030a 81
    0x408400a43d00e401a20b446030a00914156401c002e4100e80409000c101121079208022003c00420403031a0224041d900c283c4071602494541a0340724191100103060301c3c8440b000f40b00074000f0031204048410f00b00701410f4402d0010703403a100c1240000108019088d1030031f42c041034140c1c88180543c014000d45000b08104c4078400c100d4019020303500030900400c0302e581c002110010002e4040d41a1401007410008040c1c840c1c2d503c0300d046443e10444000c2d4403481900d60040c0015540c040c05a20094020082c005180752007070249003078450794900c001454190b885004038207110b5000c054034200d591003020b446180d4841e08100d0b60710241550414856010210005498032494100104465054541c050744140c10f4080025201041c80c64105c40d0054450300584e540d0742c0c1c00b02c0042d90011400c1141c60341d040842090842d000148040c00074403144081c4401b00d0703001025902260020640580d40d9a007600101d0404082603009980281c00c1409000070020044040c05106d0000c1d40d900c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 839688345 1250 839687095 839687161
    0xf060602010b0f0901051804080d0e0d0e01030c230f04030503130503060103020d021c0b070221030105091303020f0a03091514160204110703110717120a0215 69
    0x44030b2904e00b8400c2540c8071418601916070884007821503035000b805800c0140c1007425140d4031f00182c9034103100844454020790030b00107000d60030070300006030b100302032800700700781c81d1551005401e8000d9552410800c0244001c1d02d4012002d00c011600201c0414003015210395517460002c2d900d800008550b45820390b50140440c890400003180c80c1201e40041c90b82c40c07110030039024852010070301320310b8120061003a0112008648041e1950740569801c0c0c0c004c01039a0303415103c0c85896503092406000d190410401001566111712086402c000843c420601e845c5140c0b40c141d00d0039440c8100d95206009941c465001d0641090890003120f110002407030441407000412070b102340036200c207420b45060034031003076202401020083e4803041c0302600002c0c400d4182e0b1a21421030b000a401200000c410030003164a0300d109000c11002401e082e80401c1251440301205a210260040d85a0740e0840100f07000b0b41c1e0b10f1081140b0711b1894401d10851000e4180300b00000214241061036032017070311040c509 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 839689595 1250 839688345 839688349
    0x60711010b0603010924080c01030c02071d1306060803031909020a0608060613030f0204150806071416030e010810030c0b0304030c050d020d08070503010b19030f060602010b0f 77
    0x107450020600182414030356030a20301c1000c000c00c2441c03004042d0b443c0041d0001c0f900c003c16034001010304030300801000c1c140d020500060585600104802c00c540004030100100b40c421040b41e25500c2080044134020754642d001802861505000070348254103100b00042e01c001c002c4000c40c0151803810040b00b0140190b44030308282c0b258030700003d403c440c002400b000b80a1042c0341c0c0c1c070b03003000700142a589015122060b940f166405604240c483c0d030101300c8400114602072066440400c0104050f44846260441013621228000d100307000780500103800c5034540060340100c50001702c840c20075624800042c28001d0605030903c4850303000c20000c40100c0c40340b20111541c00708881d4450030041c00309061000c02c003850b82000e0002c800380302d002c15081c0e00003136090080031555a091360081042071200c00b001003001101030540030a010081005004501d05001190324020000110001c0e5a10304003046004020407030700c070100c5a00d005404500d80e541900000521b0104850700301440182c0303c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 839690845 1250 839689595 839689601
    0xb03070b160f020d0b070c1101080f19181a0a0b0a0603020304020109090c0f030e010e0a0602130b07080c240601030e1e0706031b050a0f09030c0f0810090c17190506071101 75
    0xf42f420540c140410014412054120800070a28440f004c08110500c0141e422031a41025660884801c0c3d150f03101b4440000c3e000c101c4e90f0740003903030401c18044002000045a84c50100d0b005150801d50004002029a402280340da0000c05c02e0f0780741048000c51482d030040c42100d050091400281c00d1210018210b4014001c0e82d0740d0801307140c00392030680401c1c2d403840f000350301c0700c445038272403001d40d4100050640d180000342001034003520200d90b84008943c0e0050a00108004014a489000420101040c0500f4075660f000c1400c0c00d0010310700700340d40c5a0619100d4000040301070610040d8440c50501c1e40442c8100c2203800e1500c0a01403220064401c840310581c000c034040002d08207010010f0701c03612078402c2c07182d01e80650811000c1192651030310801e025554001070100d0300e0b00801000349500802069018543c140c604110010480e030f11004030071000c3c0f1070780b56901c80c80a044001c1e40c1c0141b110406846d146801c4e04070f030341000e181180d03d8460444400c0003040c4a0b807015032074014180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 839692095 1250 839690845 839690851
    0xb161a090606060a030f050c032205030913020702031b01020c0d120305040317040804030309080d09151119050d0503070206010e0a0609020d0b03070b160f020d0b070c110108 76
    0x140150000390b4800341844200e0700724031214001c060300c4e046001000c40d428424640110715055580c1e17540d1401111103110f8042a5180c0b40c0c0b1081601001030120300c001c0305969003ea42260715800d03800a00040c0006809400c20195142c001c0d0300c4641445003805458440c106403e80a5400861070003040103100c00341981c000c2d05000d201c0b512a503078103100fa408694418403a0801002621180c012001904400c54040721180c2000800388141340d00b20441078001e14220000380420304e49010010804c141e248103104141250300e40c0107008600030008400e85404000450704410003640348030001070783e4a4010764080c0581d01a180b02030788941c0490744240c020303400500d5980d04c2c1403114058050001c00c0c144485558503004209901e15000902c926800c59802240d0800c0040c00c150030f0807c0e5500c4480316140400002072010485101c2003112a0080100c64000e078640c00403d600c410a1340340104110741e00002c10815540090340e9111007030081c4d0342c15540780540001920307420b40603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 839693345 1250 839692095 839692111
    0x201090311160b1b0f071e0605091201020d0f090b0601020102160312090b010b0a090f080a0209040c0323010506090c0904051005060a09170c06070210090b161a 70
    0xb0060501031010b00e10b000745031000304420104480c6801c6120b850401c0340150b5501c80030b8001c0c01c0c0070001c424404210411403031290385518841840d0a101402c10300c58a00c0250195400c0101200104d8003981a0303180410144424005811b1205400c00103140b0200201c2d40d05000b40c000c955194814070070340e20801181440a2030494141e01c00751942a07000c90150304158444841c0b0000542d0020040e00825108048549900c1036400140c02c44080c1d8001c01840d1959450410606200103a480000f81e01501c1c3c240054507181448007100070141c00c050011403000248001c030300d8a10583c0726054104100800440d00c5030020400c502500b51041402010140302104e114502544101e400402e1510080105a65200880c840c1d8100003640c4c8041030580800b001543e200111083c0c0a00404c0701410901a014002400301d010700740010303002c1c0030b51090a0380c040b40100207600c041c00346200c41c991608001690282000c09030700341140c90040303808a220401c400300302440d00403404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 839694595 1250 839693345 839693383
    0xf010b1813170d020d0c0e01080702071509050d03020c01121404110402090d0606060905030c0a0e06061b0109020103110903100b03031210030b16050406030c0e040c0201090311 77
    0x2180d200c502c0054000c64040b042c50408111080305103180d84024043d407489000049101039903400d002d080100124600e9061240a4080050042e804950f50064504000e540f5400c1000c810048440801030f07041640c0100d4081c000e070092580000b1002512242680d03030040303a042c900905004d035040c2004040803101c1070743c04140014a4090720340d00706880500014113003002d0000040c00400704c4001a80e40c80d60341c100900083d42d0000740e590107003105070000d10000300b514000c12400740c4244a0310318032061440c00700e40706581d40c4044a0b140c07081a0311b0740344480c00b0003010500030300c90200c040740071a103044103505960b0441002c0d2030a10b50010301508040102281d1300f4068288002016030500041203c2d242d012114011030b8020852060450100c03070a40c5406400a40040d2500700300c51102844040b299510004460544e003051030017140c005240f81c0b09546400c0c0494000754030070f080c41e02030708185034154001c0b01030714000c3e130b602d165506c2268040c43e1a002d80130030f46881c2c060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 839695845 1250 839694595 839694631
    0x91404080d02090301090b1b043006020703031a01110c13090f080c0106050901081e03040f140307080c09040f0507030b040525050f01030b13050f04030e0a06081f080f010b18 76
    0x9071095101103aa00d218001100502b041d5507a50100d0b03100010480100341e80c1c400900d10048070542c403440902c400c1c00d061800c00c01d010311a5a54200c0086094440d90120303035400080b4005820095442c1d500c101c0d000103c210500d040086c54120100c1ca80e515031800d03000191607e0301c02201ca040f219603102800c803403400915040900300c04800c004101e44420440020074900c1541c100004140c0315440ca03001d00300800801d801c1219662011410358004005d0540c0795031116290380c0c002c2d92111690340074101900d401c5041c4622980301800544604041000707201020030143c950403041c50408e0850042c0408224000016006070740c0c00003c00000e10710154044c0c1e0100c503800c5d100910404035001e0100c90f00c01592011034001552403002c10500c001c15401006c0d0501520f8200c48132407009041c580000c1200030020304200300b00d9625002074005a03c0e11007508007400f8010140c48082c240700d061123010301607151205001e120401c1d00d28441c1350480e00568000c4124880c01d1102034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 839697095 1250 839695845 839695889
    0xf0609010e010303080a15080d020c06040b09100c0204090c06031b05220b070501090b150d060b0d0b0702071701140a0225051006091404080d02090301090b1b04 70
    0x710014410325000d6a1f90b0711220054008031010001049008000c0000040c00c0a0003424582c1d001d02c071900a030010300082c008210307400140d41c0c1404068034024010340d032280007112400c2d0403c00c0a5042444c1c03840f000c043c4200c03408c2d08000d0703403240c0d107082c40064866900c1d854401c0c1710300e4090b8005103051002c1010000300040c2031030a00000090b0206c900c0c1c55424845640c5d00000080700d03507a660b48940c104000312540d403154400340c907020342003120329400b0104040c0c032103008004265a07510481c912640d5254960307000707050b070070a40c0d00015150094010f99520014000c0124200d040075401101403814001c516500ea0340c1d201840158650f030070050003075045406001a100191850041100e40821021b45038602131801450003c1d000d580c0081100e1664004800107410a542800030840b0200815042640100e046075100c1c40080c819000b070081c00c51b460761550909401e1018410b4555200b805100609008041a40ba200189050b4825441500344039280020700e030b4514 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 839698345 1250 839697095 839697107
    0x20a020d060b0a05060f03010305010e0708070501030f020f0c0114090c010c0b181506011b0506070f110a0b041403040518040503120109023424020408060f0609010e010303 75
    0x104401a02540443d0385510014420350007264100e40d01500c0800100240b040074020000d107401c844000d030158905042c01c507910703034000b030091905140c4c50b08261480b1480b0341e412a000364501c1054a51200d43e03440380c980c00390400b0f244400045102d8000701da603820f001b14180191080507110b40e01203909a035540d5207a050001c0840c400d072001650310000b8100c080c4107400f42c0131850503d04501d85420000035000c0c0318444000740d503004030340890800003000011130070b42143c80c6082c1906248e40e68003088900c0d0003050b0804100e03008010301c20b0100452100b66078092845a0f0900749a034403c88006581c0e4055031042030b5210681600903c944508181e4058215001c0e0090320b1030081d19204100c228a002e17070048030541d50006003c60100310310360404d070505e00040a445d840440101c000400f41c49003410103004160040300c584101d1045000c20001495080c80039925103980704107094491004645080c3d000f482032000036050b2805d11000d9050b2164584d00310100c1e401c5840403921 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 839699595 1250 839698345 839698361
    0x80a0f050405060304140d0e06071b0806070203040602010c0807091701060503010e10110306030c0618181512030301090c020106030b09030a090801020a05030a020306060d09050309010f17130c03060609150501020a020d06 96
    0x14164000008030f0cc0070824040f0900c100500c1d0000d581d01c17850428001d08654800120b441041903880038040e800743d000390148200d0b151a0220100081c00c0b03960580108480e500c803175450340c40e10f03c164118000126500340c0302e050600040068100210202c4140e2004071107999143d04451008070031850a41e015206000d042078030304045140c081301007608030003401c0801e00c01d840b60f0004c0010080c1d080402c0b10100c0815222030040381280c0b94040d58230f01043c000c050046444840813001039100358080d41c000c50708594140443c0c140500225284d40c010380c4441c001410f0b001021580d0001402240c1004003540c0d580c1d8075603511840b540c0c0007504040c0006502c0b02e010461099000400d016141030742e07000f240074580c3c4546503400580348840b031207408014040c4a00031036609654603070056034011491103801c90345c10030320726101c503d4807169000204082d03e0500c0208e4206880c1c1e016101500c0c00c441a140c1032600d40e40107981e02c02e01044005c2d8003031080d02d81c45000869135005000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 839700845 1250 839699595 839699633
    0xe04050a1e0c0e1506090904020907022d21070b040212060a0f1b02060f04020301060f09061404020f0a1206080d0e09070c080a0f050405060304140d0e0607 68
    0x2886101a5910b5582000c80e80c80b19940d02e400310240005808104402c00d01a00e08842072442c1c0307240c040100341d210000030401b900c501d24003c0020086170003032040c5000401646000030208040d20a0500300840e8040d100c907080c405c800d0068030f0300c1008181c40400c00e201c4031803241010b000733654400d02964014002c0344c01c140c9501c0f9050141c0702c1044801d003d42051100400d1035034101a900f01180c40a80d0541d841d401c034800d8080c1003d40110384250481c0018501d01640e039513600119015103096485501d41841c41203000034a00d080b580404244d8852260010f0031000140c1000182d014425401410030020000410768500940d0b002080c0301e2040707804036805a4501300d02d410310b120b01c0080000309181c00300c50030241c40c14108066000b4640d0802c01841c0d0883e8032601120701500030b42d0750600103140507004846016a09031002810028032160743d81c6443e1400307400701c160039464040688104592580054014034807644041c0025004034100892611028012204003500715 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 839702095 1250 839700845 839700893
    0x807031401022b0b01050f12060f281d0609070903020303031302040b04020f0a20062514030a09030c020303030a1401080a020d02010e370e04050a 64
    0x30121072180f0081070081081c425001007164943d0000d0029150205400350420008101083da5021060b090ba190010450050507203a07940c000401c0c5103500d07081e000c41d07000750b0142507444000e95004202d8aa0080d50091454295a441002070f00d1114001441d461240200000301681401340310300c0d500560b64a412000241d80f0740120381550b00c02e4800c0d0391080310300301d110070560901d03019024001c1026901186000b0200701414094060800440c00300100980d00300c040006000f01d800960b01c0d071505a0704a42414002c2d070700341e041901640141460303011095515035000b500c210962014182c0040c1c03a40e90354405072001005820380880c280000000c2010150724100090b501c0341c80e405000144107498090021001c0805910401b6107034440b002000040c0c40b0880d81804299080c241502064080030000d403c0071090a40104681f07400d146d0b100c88021603a80345041c3d009190000c000042d2501400030b03c0c0741084401601689c0035035091000102062010214411058012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 839703345 1250 839702095 839702107
    0x317060612090c030c0f0901052205090705100f1d0a08060112020414090c220e010c030e0d090b030414030703090608060109292b0e07080703140102 65
    0x1460181000d039240c07516a488600c4104490404005c4c891000e00d0407101010512510b600080e003035101402598064211102e012481c00440707403248084801d20b103014452454981440c965915207446a24071038801c002c0d0b149282c40c0942d034640203400380341d581d22100000a840c8040d44240c807042180e08000315550014910509000c0c06000c1d00c030010510f0740f480b88500410007510f4109a070304490760805410300c0038100001410040c01d40c0c8c160744282440b03500d00c0100500c0b0140303130300324940300342003500030f1440710419800b80c10701c004c058508000341082954401d80e40e0f43c4041a22002c242517403170500150300504003841d031007449003c00700c0d541e10a0304982415500410302c02c80214810400500606400503407165201c50286400160070385040344000c000b0428258884401a5a000080101044100f100c146a0240e031107000c030100d208160302c0f085501a00848129440d00304020310f01c05000c648542154407900007008420300390b4032180c501c20301074210310100d5907080021b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 839704595 1250 839703345 839703367
    0x915050c0f07061a011e030b010e040608010209010305150607060f1b05070309060315050d0510060f0302120705060f031f060c0501051003030909020f1606060312020a03170606 77
    0x4041c024414400401e00000010440c1410940d1104d0f03241842072807610103280341c2c201e40000803030307500d14600802c121158800685d580c1480000c031940203400d011011403094015002050392400030303a41008a681d9202c40c0041e4412019a484d610038002c01a020118555800c0101c5041c0101c1d000100800c400031020141018005901c01180300410f0900525402411150080c405400c2c03c0c800ba9020f090501d00c3c9100c603010fa07903c03841071080240140801008250410415000104a0036031654000714159a40344400c07846412800b082c1d48a9020102d040c0c0c0440750301412003420070700c26003000d0680360401010010b164032030120440c01003010900000090100761110341450005c1d08260307013074900017001d048001b118003504000081d031161802e812281c21030740c0161201202d0200c00c80a20600c0003003102907804000520500c142c1e45e0004048a105a91a01d40031007911402e03601c800401c0b0001c2c002c564a61565003505882041d005e50001000b00082c0c40c1103c4440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 839705845 1250 839704595 839704597
    0xb030312040b0c071e14101506020115050409050316080703030b0f0a0e07020304050402041e1508040605060a030f03031b0c02061e0f040e0f07030915050c0f 69
    0x40e804101880890078007090040c28a14550401c0d10310641a10f000342e6901d810303618104400445c031664198203035103410303c5801c1c0c044003030f6085401c0c16180112502102c540142c003d0709017182100d42081d400003022401485000c4d404100a500e0311815403401003000010300c3c1010083d59a800200000e0958031100002802420321984000d51a554981002000c8a0101280c64040c4403620f801440c0c0790f898616020071103180d8068862907503500202241180100d900c0f490b082400403401144030705a00364005c0075842c10008182e510380d607800d00c1036008429201c10307402003120040443c003c61460f81002c1d5000c800605480c0c2240d95960b10420f10030f0740300c04c040c1c6c00a030f80d07804c6801c10b10061a0141c0410b42d042d02d800d100d1112160009a52485000c0d010030011107017180c0704680b6404202500c24410341c00c0d528540b541d035104020fa0800708100c0f14440f12010500004804500070301c04c8084564000e1802003405944600c600b006250152040f44002018003d44551500c214 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 839707095 1250 839705845 839705857
    0x210601140d0504030e2e09090e0a05011a011202070201021c080f0a06080d0507060605091303023703090509131a39040e06120109080901030b040b0303 66
    0x3400110b91500e030800400c1e042c02110300c0741c404c0c0c0b1400d6682c68070244da940350110f01814040b4500040c900c11600382c81c415a036621464031a42020703890400b0100114500f14001d00510080c0019142c0d0140b4000f4000002c00340c0d4046000468100d04d400000c1e409803902500c103004840f600e045028412100e440e450b4a0400083c141c2009c00c103840f2800890f098002442c9201440003a0400140c42d441c0d03800340d0a901c040002c046000c1c0103200058000e4401850007405e081c07118140b25001c0203501500c203009602600c69160a400d43c2000d030b44484902e51049020750140010f00c801d81c13941090b107050141c003080040ea80202d4250f071400349840c065044407810801400c5645032420001c4400d041002c84000c40d5410031001c034102e4000c2e000594a100c61f038106070a05006034000c1c0c1c65942c0280004180c0104020441c001009004ca0084008950810600044c0a001c07820f03547c1c0c0d01e10081c20150b045c40000e455500030340100f40d24610003800454020076600200e4510b80140c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 839708345 1250 839707095 839707117
    0x81008010f0506030c030714062b0e0d020601080d21110d060506030402060d0c050c0d030f110304120806010903050114040303050709030503040e0a0f0e0106051521060114 75
    0x3610600c43c6a240c01c001e1711220724829000f0f0050300786410070011003101380c1801580202c030005600300460300410000b200c81442040300d010420018500c1034020085403090300840d01c04c4400f000e58250002a0316812684404018880025480000c6800003001040002c0c100c8d013400c0000d0303281c5298094642d660106480580e103580380004004199656544a240101030800030f01001d81c0301c810860700c401008900c08142d040000d0702c11125031241c1c0040396001d0141e0034031844010790580048185400312401880102001031030108988000d0b0b800070000c0300e4141c815200c01c7c3c0252480d40d80910141402c3d800da51380c03920b80e6425240880118404601c40038108002c164040c0320703d82c0c1049045c9842c102941c11a6a400c3d92071040380142444950b01c90001107101d20703150820410040440700511400e4881203c0700c4c003800183c0156882140d0601068074042c54040591f40300c110500e0303040e402a2a0a540c2d546040000303021300303041201211030641001c00d501d004000c1e041785 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 839709595 1250 839708345 839708351
    0x30309191a091f0c0203030a0c020a0b0f04060506221d0f03070c150909050a1d150c1c1802030102031f0504141f0e0142081008010f 58
    0x61a20802d03c10074150344464400c3d00d0804440740007a8008150317075000040c050009000c1044c0036042e40f80c201110030041c0340d00041010000899140d8030302c0c0c1d0180c4d1040030180050b032100741c00c00041080706404a46a1044040c000d0a501c00ca40c200c55040c1c00130544c2d020100c0c1040c000381e4144a0052541b00040d48002420800c001c095406280108601403c0d40ba603d03d565000409403542e920a0004c0151600041b030b00e0603174030b507020b034001c24221400310303ca21400c91f030010b0711582580c0c8550403400c040400110000c160800300c07000a0007001034241203843d0161800000c0400c40102c000d400702c1070103040c0050b1001d100550045c1524514003081a500e18104c4081d48072680205003d00d0501d0108042c1810348045650004194001900204242e40500540f803240740e2140c00102c0700c1b2400002e40c903041c070941c031818000300c0384540d108400740b440d506c015068015a401481a0205656020030300c280314551b000100c2d11541e4081c1a6180345940c2941c4005440c81c04d02c682e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 839710845 1250 839709595 839709613
    0x702040929090a0506040b0a15090615210f0b03030d062301050301060f02030c0d090f0b03010b0315011b05240415020a0c08030408090111030309191a09 67
    0xc02089401d50050302c0d0402007820300c040341e454a480d2000604018510081d08010424595454010300b101c000da01100000b40c40d0313607801d5180644114400c2640c008400004044800d110300c903200c003004854050042c0044841450400608034141222001c540d07611b80040c1e95036040c00100110019083d022400781d08011103000c50082c004a007502583c03072000a01901d0342c2100a07207045070300b6802d0010072803140b8041a800c51040303200c031401c0c5005d003d00c00080c07550010303845c81c103a5038003541103900280c983d0403c2441d48820301414045280920010b00000445e8188002451044c5012204000d0350340401c107159075050000c90342034100c40d440009075641d40c40e043c2e552000d480304e03c1c14135083c141c96009866146c98540d03001e080c0c00144900b40340780102c482040031030703211006075501d2502c0e08050200f0341010100d01d0000b5500c001c08200203c00100b50f83c00340c86003001820000e1040c043c04640e018850004840104000d403543d4494041144414071034401d08028095040d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 839712095 1250 839710845 839710913
    0xb01170a050d0e010306030f0f14010b010c021e0909070515031501030b0303210a1a010504060509010905040e031b0102031e090a060c0f030b01030506010e040207020409 74
    0x64200680202584500c19020105000080b50080c031161030a081206440b0100128081c1000750000343c58502c1707403c1c0e4281000b94003200c40504a00411000c3c01000021507100e00b0b80d2400c03208135002a00b0b100481c8050300d0600c3c4450004403c0700500c0740e0b06a036500c08500b02c0b8000f00c0312029240c01414040000381440c01424103483e554034542c0d4503600d030020009020500c654002410107a991f800c0140a4404204903541090030041150f5a0106049074203071010f0f080b80d02c1c0740003c0c01d1011550400c02000500c0c0c0001d20142c442a081904008046403e60020105141001250b0b40c000030b00c0d4580344182c643d000c080b40c018590f2540030300c801d2100c0c01242d101200280c1c0c4100104840d40101c030090040034540368041c101d158442c2a80c192038040c0007040030307194600d8204c0c148a4541c104002d58800d14441d00d0900285449900544c00c48000b1600c150205020409900d245c0c54107500501c4940e100410019210131940c80310458001c0742c0f00384403040c00f9003003440b551035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 839713345 1250 839712095 839712119
    0x21608130e071e091a07050f0303060306181603060c0807170105040902010e0301020a0f12061508040302011409010b0f0a140105030907030b102402210403020604030b01 74
    0x2401c40080d01c0481800e011900034031100c241c0300072003602c600e00b884080342c840c81406010010040003048008130302d15002c031071610f644561000c5420b80306900d0403403c0c2400100a60748a610001c0140003a5600c1e0a01600310b02c81010502140c0e000e80390b143c0185800c1001070384061801940300044448130b4070005800503101070a030405008050b161501c082c1c2030b8000003410f40e003054801240441c45840140c0b02e00c10a03452483c0d15500119840290350751040704425080b8150b42c5007488035200224801c2128200d000e40c980300e43c0860f00d0a4481402005102d410611920000815820044031006006001d03940240c1c0340c0d4461911800600d0f1011090604260031903400d02d50618002c05070201140d201c0c252030501c20084001805c0900500200000319086003240446280004101500c50b5150040da50004014002954212002400d010413504950010050080c075107220b404140c4001801100101c410000440180c5813040500300452003440e100c1215410300d00e924441c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 839714595 1250 839713345 839713349
    0x51f02120c070f030e030a080f0306040b01170103060b120105090d2a0f0c0e0108030904050f040222020d0608010f0c0201051b161a1008070602030f0d02160813 70
    0xc0d0700c40070701500c0003042007060104100350f4982090070180d20143d005c05c1c20b00c0c01a40b0040c0c0001408148400ba54800354003d5104440807a001c00807100000c005580c0541441010440760b0203a500520000c0d006502500100c1d400a1503c0e08050401c1d00150a4030030172150721996801460041c52042d403ca44550355032032807840d00720516049403405540c11014000d0203041e00c24001c4410046c000c0e6540e00c603002d000002003c0c1020768580d01280d0b40c13688110480c0340158070300800141451207031100c490107543c0c003c0500c188a410f85000840b4a40300d51005460f42d5801c000d490780048d0144110301c010710f544000801c02c0e00e08451050211500514400e00b964104070030400c5004e05689440300c58607203403800341d4551404118a010810510000600d11014030410303281c40d41803a51194415200412a1810030b03440d0080c5645820740da10540d00907078170070f020036071503800ca0b0700c00b1700801060395030014200000780943c1004000c09010549103498002000380d40050400c080c400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 839715845 1250 839714595 839714611
    0xb091305070e01080d08181603052a010e0f04180311240403020c0a030327080705060c0f011d070b1309180f03082d040b04051f0212 58
    0x8943d6141c007000782c2d145c0500b00c94050801c40074800040c003007844100c140040c1030390201204e44107282d800301d01071660380070301054510344540003418001b8000d0b030703280701d54803100d030741c11056420723014401944d20080da0058030303900c02400084001c803600c4a21503043c21641c400070140c44a000d5013005899030b04001d888032130355000300c00c0500c0c43d04131a0760045003a01c0c01d013400f01b400d039a45003401ca0030006204140b0758011070710100001416030000740078241d50203028603045450000c009031000700d905031044207071980085104005920300800500100c0c0300050a54555203032000015084514005001c0c500907030b01c86013818049030801140001e407001b095800c0c904a24850041130212541c8194031889481d0b899680d0030b112200d054480c8a039201d045050341d02240d140182840c94119048020884002c5020b15800303840485500104d003a134440c00255146d0380c4503051001c4009005580314854040c402c540030410420701e4102c1c103d00140180c450b50986418849040041c08103a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 839717095 1250 839715845 839715869
    0x1020307090603090f170708040f050f04021c0c112d03120f0703060b0c07090f02090904080d150806090d0e3f030706060e27010b09130507 61
    0x1000040c0680c0082030000d806c00d0620203c04565943c1e01401e10507490000d107500401704e4005030701d5603180301003010ba500c12128982131268100030700041b401240000350014181a200030180560781d80300308205007480c40c122001c084280b00b0030785044012040d41c0f002d51301c40c120107a110762079002040c401c0004030b0055440c1c0b00d44045180c04816002d840c80384e00440c80d070040303010750b0300a5100c14000c5c180c0d0300003a80c6400c131141440751102010b200c0ca0406a08082d240d10303820010303100315200040b004050140c41d840340d464001158020300c00d00c2c00c02680d1001a4001a200040d8100042458034000c021034030344942d6503401d02100223045000c1c004404021141c0d551081ca001c0c800c0724109543c00300d0248144e10f07045042001e03840021b05024400f00d00c1d10580800f0008243c294042d190501000b56144212480a0780c01c41d00b07102d0307803511510213544550000c40403400c140d4619001044060714580044c0340311b41d040d1903800024510807280f02c01c01206010810003441c142c0c4c4c02c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 839718345 1250 839717095 839717111
    0x711180f010603020313020a0608091510060c02060d02070b040606090b010806040b010314070e2b020114090603190c0c030f030903020a050d030507021501060903030e2101020307090603 81
    0x164003a00107005203024140c0100c0016440b600c200f15003560550002c1c011010f041d9280fa000d01a15001e5554174407900400c00f9401e40f8031f00000c1c1d89801540c580841c21603181c58a074044030a00b107020b20482c1e06c0300c800c100b02c800e4101180080c2c00070a0160305450718509240c500341044a1186e44528880741c10141c150940742c2c0c0100050713512140548012450704a4000128018030000032502508440402400b0368544c0c8288190085001520300007117240c1141000b910b4003056450030b01050345401c0844006520903d00e0010714005403540702e0030103007000005480b50308200d4600c0d450051040103a51600450f00480c10314240b9030a00c0345070b1503850784005020041402152080c19207820160301050710800103019400e80003c282c40e00001c038000028040c00302a250700c0010312032071507010341480b8a440c05e58101c89003610740603042c901d940d40684a4019a82d206607004c1d01802d40c03c0d00312411302d20825041e402c0800016680d141100d8080e00007580c1e5040001090b15060752 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 839719595 1250 839718345 839718361
    0x150e0f010e03070f140601090e010c050301050d080f3c12040803100b0f0a090f1508040c081b03010c0f1704020f030f0102030a180308040311070803071118 68
    0x845580c2900201003d00c2c01d4105c1c2803580c59055034505030030b4248624800020240300b00e80c40b000c0082440e4000740004104004203c580340000e02482d617000058041620001e4289401441c6111416484034204044c0c9100c40c0107140c00749615a07000410b8a0040202c2c00003642e1200c164445451524202585005406c00f080001400180065000004258000522600000180020640c0d195166a1601001da0315045020f02030b0100f00801000300c0e41030100d2440009440d40301c580e41aa0ba61440c0741118601d002a0081c0d0345150101e4011503010f506000040307042c4002143d9801000c034a40074942101c40781d0456808009170074001d64000c56100001800c0c02507503800788800354941d400011014511000c0b46a4940324002c118007003103406401551140c640c03440c08002c4072003001e00012916098150041c0054085400140000d00400c4400c8150080e10300b162641a29101d00d40d1030741e0f0100c10181d84018424040144510700744807044030001c0401d070380c3e42c2c50f801e00d119 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 839720845 1250 839719595 839719597
    0x6030c01090e0c09360f1e07030e07140f0405010303050708070c0e0403080702160b0d0f060b12150301091212060506030a0609051b0405062b2307200703150e0f010e03 73
    0xe0102641d40000101e40c2c8d81c3d1007600480381103a5880207480b01696905007065141c0c100b000c0740ca0194040d00c0a40380c0610701445040d048980503150145401060360780c0c81d019500100d000c03244843d00110100d0341804c45060720744110322903101c0c0d10440c10894006440d14a46205c420061450b00744140300231300e180002c1c0d505503481100041191806a03001130003500080c1c021001c106000b0585160300803001c42501e0051202d4081e40030b04403918001d02d420f0b241ca200f0301402158180c48180d60980c403504544040e80c14091001403425219030016001b40d0040c1c40b243e6007603461304024031110000e4854682c1120a11603440d98800080c2d50440c040d0207984100c610514010540207901e803401242e401c205481b0701c580005403107403d603a000061038108541c0d412600b80c18805c001034503480286038001c20307064981130013510811a0481c16868064016000ca008246001002442c200f0181e03001c080010f4020132a0340c98021820700e003901c00048903603aa03041501080d000c400100c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 839722095 1250 839720845 839720881
    0xe0409170c01060b0c03030714070803151906020f0115030f02010809030f0313030306050105090f0f01020f121b0604170a030912030506030c01090e0c09360f 69
    0x104949440e4041c15501e6801000c01e64040c4900d000300283c4040714000100c02548281321949918001401001e02c500d443d014203200108204000c0000c9600360400c400007036541100205034400124000c1c0d404030704c4010944c01003001d607120b041c1a916404080c02510401c06e090311410f0009851900c4568550f00400c20280c103100300740e400704030405018030850b040100380d141071300e50301e040c5085040003a8040107403c1e400a860a0070104146d0312410132035048100050140e001043d95400f08081140d02070b080605500c9401d03081b940c5000705020944107103120a11b1035868002c600c005d190349000c039000c6964642c1220082000143c608814a540c1e451507000032505c1e0403000b0000d40040103500d40141ca0b40b50104544108039134960045841050300f50180d41c4864420700041d56034808030b000d02221084a80001360316000362401a00e8806002064031129200c281541584000c500c2c0c0128a29920704091400c049410303000c10740c01c65200c4e00c0b80003262a1009035000030030400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 839723345 1250 839722095 839722133
    0xf1103090906100504050910030c060e100e01021906090515010e0a0b010309140d0905090c0d020c01020706091b080307111002070e0703021206060a0c230a060501060e0409 75
    0x304800c0c20f8000e2143c01a50098000609007009034141200e000c00445000c0c48111594000040c001c20341c80c0c8140c00840c004070b400b4204240d8198081e009480f4140e9074107000d4110310400c1915802240014034151805025420005600000d41411403c003140000c441065240d13843c010021504810001640302d1001580003801d40003010041f0302801c028a005010b030714407400341714146c3c680803855208000b000c3d11a140640d03a91310500040803400c449130301442d20f080c4120074220203590014544d090418000510b0038500d951628112604418241c0b81d1040280b6842c00031b641c040e0340b10000d807950900a41c03d022031a40c41a10380b02c50960301da4040d00d01c8403441000c5600070030842028026140c02090700d0b1802c0c0800800940042c91026041130341040495200d05100341205c5210300250f40f012804842038840744101c440c0d0407031040c0040106601c0700402c0300240aa00c0680b8031880000c02c0310751610100406800d80b0b144081d21031844c050302c20b0009404141008268001c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 839724595 1250 839723345 839723359
    0x40302010c080c070311040e070311190e0c0705150f0a0b0d0b0f10060c05030f0a02190309050a0501110c0f040f02071a0f07020705061303080a0f1103090906 69
    0x59031a1660315070082443c00d0b4910312a84c80c01000b08a804c5035280205802581d00f0400c4044030103106550f8600d41c0b1005d030002c0111680014181055401003946c1e000000440c01d1484d520380e064507601034100d58208600710041460801c1210034400b00300c80c9403101d1459078103400e01d100825a01ca9010303200701e0486175200308500306600c03071f00710881c60140c104400001e1403410250407000300408545034040032040381c101040c90b90080c007004082d290050010b600345154444090310651050741100107600c42c2d0500403001405801d410403841e8032980c0c0e9000341c42d15003000e1110200560b0000e50501c0365601e100d11041d200051031034000c00d01114001c3c00c2c0d400f45070115008080c0310509030780e0540006030320810f07c0980100d10101a6180340c06098070764850b5101461014150f45020060700020b800f04282d14040c1e000d001501d0210a40004c4140e4070340e074034a02a0f010318410000305801303541e841d0401e5005a10220008000d0340a14501400c081c009015200014500340c4907800d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 839725845 1250 839724595 839724617
    0x10050a0341070f03022b15080109030e061e0d02041503091e0206090d06090b0a0203060a0e0912040602010b03070602010209010f03050a0608010606020319020c0117070315060507020f04060303020304030201 90
    0x102c6d1406030b03401131440e4410710081040310700c00c0d40041d103100e40514005d200c10007800030b1110014031840c00901d030103680c0e0002a000a4003004126880080d40d90700502c01d00c400d4820729001c0c2c0004007940e521103c0010b030307910700c0c0c4210000c09412036002070043c18a0400c440001c00c101c0c04c10036040e10b00d104038688940280b84000f80117030241090142e0807060004404040041990081a5150250909840d641d8486909170709a00c8200d81c03c9400c40000101000001e01c2c100100d03800001c0d910640b02c07072a005500049040d0410340c40840140e44070780b0a01b15904050180318043c100501c020b42c5401e0a02001034000160503040408150b61240000e501c140c040e803118018109250080c40115035651009540e504120205144a143c42660b140b00d5030000401c00710000c8103840340154158104c00c070100070702008008105140e00c5040240304e4081034288840a00000c0c1c81f01c54461225005112000c0c04200a043c080c40c0f82240500201c0d03000001d41c0c0c1200e50900e002d0321484 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 839727095 1250 839725845 839725867
    0x6140d06091a07020a031d061b0102070b0f0a0b010207050312090a120303060503150910020702190e010611061b090a0f09020a08060f10050a0341070f0302 68
    0xd081c8012a0b000003030007509100d44203a01150034501280a95680086d040701040810851540303001e125600c10f004000d42500100da0340e040c1c11218181c074000508041c008d0722100f00250003210140c1d0791121032804c110b40d40500d0701c00c03054514800e10040c41d0183c203180100b69214118061907480348008104114135035541c07210745000d416030f4804032214049520700076001d40024020540700703014a8040e41c1e151420b41d4181880b850940300100485502a11750324000d40c410740f416a000810044825040310484445100a0200c0b0101810942c074045d4000d043c1441220309401c140c0200c028440c4070311a20540500e19180303982c200b0f13940d03111000001e0700c80304c00d0f5100302d00d2403824200c0001c442a071940a03081e002507035100c02003580c2e540d404020080ca05c004801d5440b10303d448184400c1803085010304280d0301ca40c00d002400c440c0360b40d121140c4001100703040945011251004418181080c017100f50001d0169503a02380d800c0003900504500b440280c2c03001010b601103001004c00d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 839728345 1250 839727095 839727113
    0x80a020906060d110c06150d1a07030b0d0b06011e020703110d291006051207120204090504021c0b0112030c060c23031902070f1a040606140d0609 64
    0x4041014900d5071441c031100c81729191302d0104c1e9640204801c242d511641824581d1114100b0b0380e110384541240303007510000c80c1140d00042c240100301030f641c1104400c1a144d10395100e00c1c0c580102039004152a1410005200d6441c11141c0031481c42030003070068006400007070050a1326070002c1400c1c11601708101092030400c12403400740c41c50540e0301184046200203402180b00c501c0c045603ca06640e00d1418030f030020718880c03082c0e01c0010303020083c1c601f8010500f901550008484c2c6040c8240d0300300c0307181800c281c1c0c10940000b801c069a130f0050008520304075035042005400c0c6180d0741403105030341e203680429a41c144a80048107840010003000c052040489080059003c01e041000d40e440007001820201485900c000c00e16150b00404080303100041a2449111100c1e50009920340807900f4801035086808100c89401c0445c140c58001241c40b015400d0044e0311928004d40c1c2e01d0941085429a04141e009007a1011420403890042d100c82940301c0d9201d03000702010075050401d1503c0804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 839729595 1250 839728345 839728361
    0x150b0f030603030c030f0a03050c070c1401031508100501050f180c07020315070e010206090601050d23030a1206140f0d060e06270a02240d06050a080a020906060d 71
    0x5d01001440004101518000e03001c0c00c0351031345d0200031680d5000d600032058818000e015040646000d001c00440c0782200009a0b40030040c0350102e0250303900140403160390400c0d0010078107900184944455020b0900c03c040c011301d0100c0d2807002061f6898089280456007101354a841d200c10000211881d800744100d07030742d02c0ea002d0219000c007204011411120399080c0c9500000400403c201021581300082c1d80c0d006003030398000340180c3d07460003080086240040d041119481c030702c05d03d802c1595807511030901d00c0b4103220020b5030f51480185001002c40c1116240005058640f100505c10310315003c01c04400910b05031441e0a131100d0344070015004041403040285014285051400d1440c00803c0d0075005120303250b2111000d112241c82e0b10038004001d001c1e03130615402500d055025181c1018143d4241228640019203051621580039403070781300d00055420561518020040b0b03007071040c40400104407100141008083c568005082c210001e0f10180c420713240440c0c00d40200d40c8541c0120a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 839730845 1250 839729595 839729617
    0xa0207032723151317160e04050c04200408060708060d1a22030e03123c030a061d06010507230d0201090204230a1e02071401150b0f03060303 62
    0xa005805c5500680d52045a101c03003181a030840800029009100601d4500481d482070103041f03000300d008140300007880c0c1c50001e0303d003841c85404080d080442800c000c0c4060804c5101030000d5161186001c0c00c400b201400b014040c101210260700400c130815042405207041d511b03c07840e55207a100d510002070440c040c080c0440001c840c0544205504403490f088080c1c3e080c1d0554454034101305c0c1d0800f4a002e1820301b081e03d807130507012003403803601c680018580302500c0d14400150b0341c11154501c130003504200c441d42d5000c0d070740b4081400101001070301c100b588650b1803100c0121345019000200700e402100001018410300840e00e4001c2940701c04440c40c0405201e044524011803400000c1c06007540c880103900071807814410b01a401c000540c517030600c40c000100d1810581303980b244c0400414400740c405d1000c6204800218403004503000070888a4064120081c000d100da501c402d085070114490182c1c0013184000c10041302030704800b0341d10601500d101c415140d03522640417a0851140070402c0e5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 839732095 1250 839730845 839730869
    0x3040f060203071208010f05091e01080a0c050402040605040e090f0f011d060c030429190e060708010902161502070c0801050606030a02070327231513 66
    0x40340040d40000a00741d5203000303041c1228100080030302528030707040078007481c1e4101d060b80c0c20500140c100189150f41001540342820110a050344036010011800e8016041d280c10074407414041c04150b441e0030002c0d08040307800710300c1d151070104017500b0740c892481a500702e1006030b000039420702d40c00e0080042e0613003103a040c1c0e400610600175040c000c0074814498070b02c2c0302c013044640c0010480010a18881c0e0508000280707151569124800207501546811103455200301d50070500e1800c01d049180190110441c1c6500d0a10208029080d11040288184903610007c1003010596111403c90b0468880410040c0e40b0780e9004180c0c0400383e042c0d20041c143c1c01c010503051890750f82e00c0d0b00070302c8903501416500b03124903107440b0114203030703541550241e600240030b00111718188542d5008202c1c0b0b81c0300341800008400401003000c4200d581c007452405912103031008104a582c0580b903055010003181442c11806580c0380042c0c0010084540024001e00104802500e0001d540b0941701801c000b840f0300d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 839733345 1250 839732095 839732099
    0xf0907081f030f030305041412041706060108040b09012d11070825210e100206010b030405190c090f0629091e041a030a06020a0203040f 60
    0xa4000201925031550040d40164000d00a40050a80070140d03035003c04104030220040d00c0841c040c00c07028200f40c07400c030241c0c68a80584003081094419654070921499100e82ca030102d405451041c444452050b60001010096160780c4260f909500591007042e1402c0345d10344031919401002c0380003504c09101c409100c2c1c00440b106544061401111220f0b09100c40402031f1a4841c00c0e026440c00141040401c4c88481701c01c1809444403003115542c40700594440781151a004404072940482900940d040302112111952022044c01194815219118160010038009641d46014401c0c0070840344040003040c200941403050000c3e440c014940e020480b1002e0500701150780d1079202e445529807400550300207010b03080c05a6001c482d2100074440b80081072495807a020340e4602e039400054031041103040c601c1c2e030f980303e10449100b010160049041110b002400221500745050a00e08192422911481d41c0e0004038000616401040940c8550030850160301d140510f401c5031000e00200800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 839734595 1250 839733345 839733347
    0x3020c0304030b100621050901022104020f03060601121a0405010611010621060903120c11061b030718080d0f0f0f0f0302090118030501152c04020f0907 67
    0x1040d0081e0344a11120800c0350740c0d5117040d240800c0e9241340314106545000e0703a81d00e1480070b81c440b91307220132a04000340c50712481c55514031602d12680303030403441c1810b110705100a41c02c1050010a020200b03400904ca2820300741e0029081815001c0d10000c89a29a9810b200488842c03a2109181c05c01900a019a5840c2c900c0900036694042c0040025840c12100003080c40c901034800c6c82e610795001645180c4a942d03200c810250800b0310054003440349020140c070612098ac854007414501981e01d40c8102c4510051150034900040c2c4940c40e40404011899881410070b030032207070421903904288402c502003500c01100d1220651194505000740d0055590103a0482d000c10300301681d6a50b0400f00c41c009040503101c441c0120411400a9180705c01416000d01035401800105014188661400b03082a851a88809960021500c03651501c158142009501232030b60050600c0e00005814a0407202c080007008101c02c08415844903034001140540d144c92405540e0010080c0c01c4110a00d00003c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 839735845 1250 839734595 839734613
    0x6090d0b072a0c0303121416180302150306030a0c06050706050f0f061003020c0304140a0b04060c0219050d031112040501120203180304080a12080103080d050703020c030403 76
    0x420048a1520030300104080b003082c0d03121100281d400014881070504544003103600103441e00c03030003c220369107030341c0a5008142c04a14901c02c8280c04c90502560b1a041710007071038500700d0480a030441c40604d0081c80166a1411020303610000040442c3e200c1d40c907107002a14000038040b01400062642c00c002c284d0310b511200510105001c0c2030180312a40726403200c0702091504550410345404100042009031070300a41c0581504140e107000f6007001c40c1c1c1415607041da4001d9103e80c10081c20840185180d0a01c00d520708020403c41e807060741003d2620001406039414000000c0c80713038203100040d070135002000e86600090400030340768000303056403460f0241c210303d1600b807402d01511422140b1546034569400f00d030300380c82041e034400708000c02003e0170601941000d06501e102552404040a200c10f0410142c40201000d01c0202040841828900d159040c00301c00744040020190041c004190654201c0d141d241800d0320000790b503500c5010860003801601c0d4280d009020024001082c44800d035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 839737095 1250 839735845 839735867
    0x3011e0b041503120e150a080901020c1e010f0b0d060b041803080402040e0705031002163206060a06050705070b1902010615020a3504080d0207030308010506090d0b07 73
    0x5245d6109203060841003104851160041c1d00080344104450b04000e846040d04a4001402c180054104620034070b8080c2008580841c0d48250352a142d9003101c1c0e42e4090190003605800d001341000300d000300c000032400c084d51801020b40110345659800ca266100d0b54400b200c1c03040c15004d501441b01292034014031401040e1000e92045041c41c80c201030045002c90130300b044800040c014440c900391702444e50080d42106100080c0c1070a4110610003245ca50315200800e030308200d41c8490218418580e580360640480f041c01156405070003002010389680a00d9420b8035001d0518a80302c184e40e00d0224508481900703e50881040071660400c0354405000038864018190001e020b0140c4401000245600001d10a00140d00c00d10440d000f00d0b55000d1025080700203071a100b0303103103070b400c5c41c44443d01076101d0034000d54000c0015041100174824032125003c10954405030042d24910344004004501c1801810701c503200010f54038010340d45000356403c84075405026141c0518110f100507040480c3e1f1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 839738345 1250 839737095 839737097
    0x3312080d18110906060a0c05070f06050304030809011b050c0f0f10060506090a1203050c0609030d1b09060806030f0a060e07050111031801050c0f0a1103011e0b04150312 74
    0x84040340b00da524003031090a01c24a4040c04090030200e003030001726284003240741d003135405000e08000411b06941c0b07205280042c03c1a07441e081c2d528100762400500c4034030005c0840c0a2640340030000c800d9441c51000101d04e50429160064071a42002c2c10710303007050300e41105010345108010308500c5154002c20b18501e00301909a00708a8195a6000c1c0100307403013080c29036944045059806c0c42129a940d0854011500a14043d414801665001d03860300c281910507070300070317400482e00c2c040e000c0860040c4410f198514a80049003421520050710008060150200307000c45000011115141009050344a010541c100c070030784440e0341403c01c014880206800c50a000d000c0c0e0101d1365500681144592080000c01580761824010100382d89040b081980b41c10807008104170340c1c1c8620b041102c890b00034202e07005041c582e02c0902c0c00000d940d815400d01402641025641100c50120310140311500001d09008a1103c0401c80000c0080074117503110307143e200001c20302109003c01c844d024040c4840c2d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 839739595 1250 839738345 839738363
    0x90a03020d020c13020705031210081b011d01140a1d150d020901030f02030a0f1b020c120a0501090c0602011a0d08070213020408013312080d18 63
    0x1c20030040303881d0002e07040840c0d048481800325251204d40f039030042010304c0c01101903904091254020118818059902500c04034005605004002c02444825515010721501000d1520010000303020740c0d101190100707182e0528000f4213060b900416a011959051105c03060b540d48034060064002181d1040780526a83d00c0c44980341d4900781648160040724142c3c2109050024000030780010354821018a4101521100098054803160000c1c5016690794103000c10702d552080c421500b00c1c0c940c2c0e00389035250009444084034403900410b001e540c11105454000f180e21400b43c0c03c524240050200520350b40c41c105076101440f44001260080d103581794028005148003a0400c03c4040d010700c0700701d82c0b1001e1000041c00084d0210000d140d280d2002c2e2100a000e51602c83c40070403a080350b8040720340e503515580358181c04045507141504260400e01d44000c014241081c0d62040a401e004a00c44610080f400000b03002101050f1030701d07009885000d012115828410b150641c14210040ba81000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 839740845 1250 839739595 839739613
    0x501030b0d0b13060515010203040e150604030f0b130b011208190804020a0e010f060e040f1b030b42030405011401240e010c060608071403060c0d0b011205090a0302 72
    0x4031109022806106c140d004500705420070300c10081218001e81001c44102c071400c40422a91140703805031001f14016800610410458100203000d60b20060201c0c441e0b5856810700390024003442d0041c5e041d203042d001505210707101890030703a1840c810340300c031510560010342d00044801d50043c405845180b094540c540382c556502c4484c101040207001d41116041d040c0c20501401e40325078a0947e0703d8500409c0860151181c0b18034404445003c0003401d8424002c00100100f10f4241c00b50350f40303040055030320000c0d1045504624107100320010169036500003914501001c640240c3d00072104d0100c072500c0542d20b00700fa1800e54000c5c03109024850041000300d000060031910702c504042c1c01454244981c400207a103c2040395041c1c1070030040390511511005100101e14144244000380010030000d00f4500e041540b991014a40c241d0210f110754040c00030040c42c030280c001034404041481e28080764030180080183c4070409409401c201d400d190504103c5481000941c07103c501d8025000c0d01c400310 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 839742095 1250 839740845 839740861
    0x20f0306030115060824091f06110c24030f041203110304020f0105040807030605060906030f030a0507020f15071101030204050f010c0203010221010314160501030b0d0b130605 77
    0x40c40610401001c68010b00c0051520a50b8010f80d00802441d006040350455281000841c000030aa589080c600440c440e402c3c5140202c1014a01802090401808208109180d01c0e030310402f4441a5000300c0c1c000b00c4600b106064411609900e0310302d01007041d228a03043d4044204c62004440030344030500020b40c504007880c001e100b240c80c2c403140c504c0002c1c17030341c1e440c2d400340b2000158411080741008010000040c1c1d488003400114003840c4036130b81c00f0079142014000c22000080207000c0c00d100e41c0180c0744c1a40070703003800001c8850001643c2841512a449400001d0800301c0c800380c0741c1e401c00c12010030440d080c180c0300001c028485c0300300030b603403170002648004400300c1c040e601900c0d80150703805101202940c007420850002500c000e00145c54407114030b08034004119034540c018040c80580c0011f00030031903101040e031903600c6030000030300350040804c801d5106055984075241c14503030b441c040205562615501000f40a8010284031081d0410410a160340c000880c01640e0f0580b600c40821242 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 839743345 1250 839742095 839742131
    0x13080a03020c090f15030a0210050a14090604031b0b0f0405011d0901060e06071a0f0a05071422030822030506150604090507090513020313140a06020f03060301 70
    0x44601c1c83c68040d6940c0c514051400d0300c0c1c0c0701d40c0d949500d80b18411030303240140d0b1a0290b80c0c9913426143c2c0e2b05922200054009020700790841b1a00001c2e4030244a41c1d151a00d8000503202180d800003030380c1c1c64041003030103200c110341e54940040c024245d00081100080d2040b40082c81103030b1081c0d85015a020140660000000c22600c04991081a80d001003011074440c0c0e0781e5460a0f40018805841c00c076840d40c0344500f130448905c00c84007107050501040302520f1202c0d10240d000da20030350180714030701d81301344002c009001071080000040d60100b44101d45100200130541c2c2803141c850300200107070b100c2c01d0902058201c0041003030700c2e00c40800400c6211598010f2030046a42c050001c0029480352080c03111076814406815070000005d0000080c8a94075019082c0114580d49a0706200703802e02082c00002e01c21142940700003030041043c84100c041d059090754071640c01010f08058401d042e500c040c20030f800302601030009030000c9242c0b0340c000b900720001c3d401032508a000300002c00f56880700b4104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 839744595 1250 839743345 839743351
    0x81006030b030c060c072d0501020f0d0c08040810150501021b040908070b040b0619080d0825110c09010501020a0b0615070b1807050a030609060213080a03020c09 71
    0x50f401c48041040300d810503002900071070641e28240d07043e15072582d03902400c44044122440d80c1810306007810b450080140b84080c0038203001c0c40034024584240c00090368a0061b00100c0702080411a00c1c84240003028080e200540400019a082c40b002c141b4014041e10340d203124545401a048030004403903000088c3ca050000d0300031940d4500c08000703c10000208001e007400d40d4000d00400c680303000900c194410502c1588a0542491070381441f100340880d4100d02e00426154014030501440304882c0019804203045881c0342c4514290b8511100030390309114658001c1d00705039644055540107410840000c42021008100e40076034034100200b00103400c0a200f030302c1c05030b0071110781c00c0081402035103c2ca620640c042c3c015862159452209811a80010800e5841080036800e0102094810100d01000e15800008140060402c00056104022440004c5c0002d584003d0601080f1598059884120362140319000039076480f4081da45a0404880480c014007400c84070003042c0c9800111b082c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 839745845 1250 839744595 839744599
    0xb07020a0e0a2c1506210d0906090e01052812110604060503010b07210c0b06040c0813050f161d0709090905010b13020c0c0604030b270a03081006030b 66
    0x42c0d050a251140d0703560760017410349904002100740c4840400e0380c0c41110341480081d00d00401601da81c1040040034890160000020064034000c00c10440204090741070541c0c03400c49000885540c0d24407203901c510031a040d00c0780420541a80002c0042050388a00c2283d4000c0890a040c0c510301c00c2009424800e034010b440114100744010b1261100c00000341c040c4512030805009220600b41413000031591042c1c2040004004000380c0c420041103125083c0c001406690901c40c03089035a0001c0c1c81e2800092000074501102d5a6000502000304030040d10f021115058500c408914000a90300b18024090003e04010244920710a00381d01e616561185041e6650b04103024105958980a4444120b041d2815921010130300e140b942c40740700010094140181c01030380c401c05099103038184459050401e00c14201031101b0001314803080201135003c400d01403034403801c000c5010040144030002031050014415881c0b080b04068020b0b001c01d00400d0b8202110268960301e1004a00780d8000c40790301c1f0303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 839747095 1250 839745845 839745853
    0x306020c07210b0403110f0c010f110a030f052101030311031e0f0d0227010306050312090a03051921020d0c0309050d030504050f04020a090b07020a0e0a2c 68
    0x1010803c1c9000e0316410511a240900085582c100080d107800d1058a4207011a0000020045552380020491800300c0090404038010111401020b071071340018040642070115600b515421705200d00115035403d560006800c040e242d0840340c19405c00c0090000302d0208190724001e010041001060301d403006444001200c02c5c2d420082404040c6c3c0000e405410308500c184890a41c0c64402d0006d04503225122611100000748011030210700150848058149481d0203070a0086440215241c0a00c011106445035115104000700303240701c07025400a00103010b0042000b4002c403d800440c202d00b80100025043c0c10080030121002c40003080c1000e015030702402c41203143c240070b03050341c030344090080c1418005280e0307600c01305a00024290341100040e20000d0140198070340700c50200c0c1000303030035138045040c41c0000e0b0000d4440c1020780035009880c040415a01d0031580d40b0321030300340540242030110602e130600965800291100d41d52502000003254039610b1240144007004524440e00c030020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 839748201 1106 839747095 839747159
    0x9130510050a1809050307020904050d08010f0b121003050d0c05150c0403150b041d0c0906011b0201030e0d05120f06030a020f0315010306020c07 64
    0xa5106420034a400d104414002c1c83c0c0050290043c000081d00b04000c2c2419880e500a182d00250310103485402c01003004000305091003c030481d5280c2c401c459885007060b22420f43e060290030312102c0240700c0d440100d01c65005103a0054620b07a4211509600c0791100e906004c0b0b030701600c9005c1020b110803041005020041d1140c826080090841142480240e0030014419440041c184400344001075140c004158401c0042d80c00c000c0c0104500180d04075038410010448245102d24094004c7c0141d49003030500c403c5d44644816554007078817a0b1010908444c159240c0d605038105544c46200550f526402c10002c001c074101c640380d4030307100c00100400900e07040b001002e00a41e400340740103000103520005100042154100c501440040d40d200101e40f40c84901c6209950200c0382400000c20310885038018400c8a254600313a400198079181410007200346001010f2804040900d6 = true := by decide +kernel

theorem cover : BRFrame.Cov 839568345 839748201 := by
  have h0 := BRFrame.cov_init 839568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 839568345 ≤ n) (h2 : n < 839748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
