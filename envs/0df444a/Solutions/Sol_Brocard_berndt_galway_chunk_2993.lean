-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2993
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:21:00.367889+00:00
-- url     : https://prove2.me/submissions/f7f5ced2-38ce-47fb-ac10-84826bf9f76b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 538129496 ≤ n < 538309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 538130746 1250 538129496 538129499
    0xf010612110301060c021306031e020d1a09070501030e0c0d030203040e16030b0108270307050307060917040f2916060b010e0f0d110904050c011209080d0e07 69
    0x1100007503442079001c0c00108250741d2640c41103081072a43c4d41142d00e404a030030400e1034038648a0048480c4a08400a9014022030700038045590b007100300c006080c6c00c20005031880d1540c2a14417280780d02685c0c60b025901c1202c90000e8158030074040c440b09012000302a2004071201814000b1107904441c0c2142580014800810f005c03e100a059101d00c05402c3c0000801646502c09002c460614500340e0411505070700700800381d07044405032580396150050121403a166002d000d800c40c0202c010082c214000081c041c1c00340586608140e580c9401041d80c90342e003424456942810340f02d54071505810185902080000c2c1a20024000055840c10940c1c0c0740074203210a40300c02c3d5403010b0300100c0c1078011038401200b80b00041c420503c841000b802d052003461070001c001480445440e2010340f2070a8a10300380d000b080340701c0701d4000498102810018041c10240b81c00d944460150041e180010741c182c0c0280704c010168040c00c240e603900b1155161600c01100d5100000c1c04504014800038810704a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 538131996 1250 538130746 538130771
    0x60d0b0f01030311120d2a08040303230403181505040905071125030b070c05010c23090d060501031a06180601180b0307090f0b09030319030906050f01060807080f010612 74
    0x42c81100c5c21190747c8d8003110313071a2625002e0200c0740d0104244c000426884d480311801041e0906598105400d4141010010401e800300005200c00b80c10a04904850201c0c691426401c24003070425244c0300c140074803903581c915000700c03103205000d405c00d1016804200a00903000c440940007a01010003251071950b075840740c0394072900036019a044000150b034949450103100d42031007224120718540c03400e450b8901d0402c11180300d4a1400d14143d28a500002c0c0d502c46503034a06404084150340b2943c240080e680d07034104640d1280c0c1d10080502c0c0041280d00117045850111400c50b00c0540d040303d5400145c03508030044071040ca2087e1044e94144040001040c1e140030800a18420b400c190740300406181861441030714001c1350307030180c0c0300d0200c2800b04002c03554011043d203c80e5900602d08400e9048034200840280c50810b5024000034030300f070b090006c0d0f0514001040d040e510907441e50300e56901e1b045812a6124405c4802101400300c1400501069124521950305141c100c1c40200d2a20144a0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 538133246 1250 538131996 538132061
    0xf120309030a1406090a0b01230406060201020c0607051c02091c2d05070611100606120506010e03100c35010b0705070608060d0b0f01030311120d 64
    0x181c064403044840c0202c100070441c1040680d5005c0400710103002c0086050b9074142181720103025040c64400ca0081c0001d07903500160701101c40340e000078000e00001c0d80d40c0401900035400031241c55124013030a000250214054030445820600b048480d60504001c1e1285100a42103085550313813203160304060101c07501c5080d4a583c2c026001e6010340c0e00454109406110041540011200c1d18620380c41c4240401c04c0440c40c10219402824623801080e94183d1b19401d1000315403064104a02e00b40020035415031040910048203401081049185c0b2910015a00f2642c0c803200b0591550168803450009a00380d0801565000b203070901d40c0801c1542040040c400d4010708042c8070261103140f0b4442c505001d5240140100f01030381c102441d144144c0c580c0b50315000c46000d00814804c6000c04253305848d0040909190780d0081000d000c0782c05c007040141c03038120080c40b044d07001612a200490107035001203880700b40c84290240e07a920300002004c10788017410240d09403011141000250b1050030170000b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 538134496 1250 538133246 538133263
    0x30406020f09030339060c0c012a0e01050438040335030112080409091407080118030e04020903150a0f150605090406091805010b0607020f12030903 65
    0x41d000c0341030740d171100c40c040c80d964240002c16a00c5010f81a210018201040341a0002d080345c1d5101c0e5140740d8a11001d01400301101c5010890081a036000000c420700b04040b00503d9040e03403015180001c190044aa50055000b40c40700d1210050345610a5041030388004148641a40c0044603980001b881105a401c10ba2068400c1c496034104000412440840c40e019580c004980d54000813500258a400303020501910b00e18140c0090b07000203000007101079030001c10400e0000d0155107039624000ca000030f00590300f10443d11410340045000241801030041041d00d1244880f441c10542c1c130220f07442c0d0125080e003900540d08019815079500e00b44001801c1400d0760320384002d207040c851072050481310502c140700c103010316003032419800c14240c44100c41150304510b02185c44a44800002e401449198402d074001480c08903030f0802c0f9416260903041c4280030710300800090b5856418081d0a214403000258000700b050710801503031420b05402c0d0a175001d080304590500384950003080c03401061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 538135746 1250 538134496 538134517
    0x5010801020c01050105030d140307140a1d090103031d06091002071d010302060a032d05011811040504230a091e02011205091005011d1b030406020f090303 68
    0x10b001c03080140900a03140104803e40040c09804816000140703001c0742200045191035000000c10b201038030801d00c06420304049041da81d034400071001d02401c0d001050070f1506a000d0510300d800c40780d280149403103048035010b0700d6025101302403050114030748104440080d03100d41b09000e0b1154503225020100f01c620226001840d0a90400003412070380140300c14600010601c0000500058507030b501034800101d00e07030030701290180e5510f00c41016004c0300100700114401200c8161003600b260b070400b6040328515054004c2e0080d074140c601c01515200000c3c01c0d04050100b0041002d4109903009029844580003441c900040d1b44144542c07428003500e103900010b44511081c13084c0108042402142041c0c01a080360a00150780060410300300c00307600c442156640c0b4002103454400384031113010152403110401c035543e181d2102005201180c03171442111141d00700041e500c036804c080c501c0e059104062074582150741d1a61404043d500000c0d561040c14018401d110035600c0070400341400340e12 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 538136996 1250 538135746 538135751
    0x40210030e102a090e22050d03060602030c0312040f02090108030904050105040204290903030d06090f02030906040f020d061e0b010e010f0507210f030c1e081905010801 74
    0x10420005a500c8640007008a58580f89509a21198004055204544e4644c0c20a4115501c5034140984600d041010364800441071215604100c40070030403040b02d8150f80c9003040700d5521100f041341e40b401007044003c0b25900070004101845401190550301c01e204240c16504c00d1500c3d03000c074080c040c083c0e0011b1007d82c00030803402121320345070003100d001d410180c40441c202460043c031a0351903d001c8150380b506040d044281025201c140c01101e40b082805000c0b290744100081618009000a1141c0c00d2001e150400300c42d03444410f8000c1700c1c001c02d8148010104d41d10395441300c0c0b865403100d15080740d102c00c0280380d000c00039000b40641402d50581010a410341c5404d10010b10949081080c1281000318920103010b05a8001c54042241c403c44e14000d5201e00c400c1c03601002200044060105ea140e90350420134000d60b0014902c811400c07540d60500c0250010407098a901a40c0d5220381c4001c07260405c246030a9104020090340030042a840200e6070b4682040b0100300c940a0b0001e810594 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 538138246 1250 538136996 538137011
    0x3060c050403060c0f1706010c020301020f0d0612052e05010608180d02030f0d0902090408090a0b0c0606060304031b0b16020c060318070e250512040210030e10 70
    0x2043d48201c965242c014144010b00da130300c80f10000d041c05058103001c84080b502c1030201e101e6921a401a40083d076001e0000c541d28466402a461a0780121a01142107410a1b0b008200d09903030940306d0642e181e0280c010b207507201c00b03441c04028460407940a040c1e880c42d0f1480c0301c10b018402c0d000d907900904058840c038a003810105554150200b074800f2944041d81301716048a1300e994004100c4903190b82422115895880400064010300752081000e580301400b64180b00a10018030000d0819413021216030230341c956541c4a888181c05001c0c0ca056280c2c000d00d000400c0c40c18402c1c011035102d84646072140400e080702400c80034007562003400f907409480038010071031588007a00c959080240c0500090051014103000540e1612004280030010400c50480307001d82d400401c5941c0c094074041c1015044e40c940b0b0307510742000c20100440c00124180c0300440d80c0c00603000b5400c0301c0c090000d05100840d1541c0319000d00c01501c40106210301059074071030702c4902015013801540318152495002281781c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 538139496 1250 538138246 538138253
    0x302030309101403250e030d081b0409052d060105090406090c0201050402031204120219030b0702010e0c180f0402030304090c05131406070b2212020d021902150403060c050403 77
    0x6019145c02c00c050000740c600c0c4010383d6030006440c2906924900d85010903990720000b011503004294160f0b1522803020801294807071180d00518800d1108402e40034080700d5043d40010f070103042d640503c518600c07100209809501c6600101300316003001d80003041c516038814404003120043c440070001030350349a040c0300840c03405000c2c80d010814650b000238206030401186504081c1c074090000c1c810402030301110790944101c0d0f041030046400c4402c4414502e00703004068042c003a4891b51115070f004400c40d0003003914015461140314031001800c0900355036031652825440c1c402502c140d90500c0300b4030001920070401c0c044d101e00ca401c035541e481c0d2038000b903d2020b0300c1e0920315001034501d0b5103070704120302242c0c560704e09a8070390340d40215004109807500c03a03148420302d40d01c2030709010010b8003801d04024841c88054000d81c2040360f44c221070420300310100880e00c0300039400030503108181890085025207418a460000c0d011565206458555a40d940b14111a0001d0034a400b14001260404c00d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 538140746 1250 538139496 538139551
    0x1203050c07170717030c091c300804080a0f0201090503030a020406031d030723190201020f010c081308040b030f0103020a060311030403081f0b1b03040302030309101403 74
    0x80090f0030241405e40c05c2070241c04a884c0540c0d4085030040c120440041c041207010001d40c2030281d08448031071800c00714041c001d03a10b0350401d100c4c2050718000202000313880b1304c01c030b900714131554000d00b1007410030b0300010f01200c4136040030b0840000c543d00c40b00c00c0404144103000544c00391046180050703031075290041c0030f0240c6940301c0301814400e111340700208210034080122241947d01440c1d51381d5403134a030740116000d03d9800401050358860355030b1a0b1454141840994031060007602160b900c0faa51a801609841b1100021000680307a5000300310700f0541c00400e50403185c800d81c0c05504085e00c0310004004c1e6001122843c0c801d032600c4004000f5802d1184d10140649402d140c2800a102609030130200f0f484041c1c002010480310300700143c0300206980203036040e840c50131031140505503130314000314903030700100705818103a0f0410030140304144000045500301c07640500a5810030b0784880404c65100d14030b10484082c000c0c010442c41e528074000c0000c5204a0384001c0c0e403510b44210380d000410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 538141996 1250 538140746 538140773
    0x70b19050f19291c0b042102151b0d050601180305070b0d09051c0815150f090d030c03091409160905120601030506131203050c071707 59
    0x1c1441c5400168200300c2c40350074400c4030468540c3c00710780420864101044507100d80d6213900e56400f00501c5011300f0800203d0042c0d00440c06580400d402e0b605500d20509070390011107007071001d42e000300314801c1a06403160300c0e03592105910316400c1c80e0b54010703070071507038540c0c464039158520075580e00401800b50b1301700d0408204859a10140c41225003150b90342a0f42d4071746800344400c41c00b0003083c00400a1020703001082c0303440d801000e84020100b01d59070001d01021092402e0049040e110000b1294112500402d05040d002000c2d00b1405508900c4445140d00c02c0d5100d484100b420003c0c0b400360349401c803480250358460b41d201d42c2c1b038050b00d080007490620300da003250f14103008180d02002c05581d41c401e0150400c0d0764030075690220b0125001035600c032200782e0100d0742140441d40d140b071031a0302c0407030010f04a03805002a118280d03900780504005603140c0704010245050400e83c0102d0900c01d502c80d690186d3701d1400149041010b4881d0084007640c00d0703500482e56800103007681040040e200248 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 538143246 1250 538141996 538142041
    0xc080f04060801080d08010315110d0c0203070317071b1401140f010b0f030411042403061103040305070b0403020c13051906050112091712060a1703070b19050f 70
    0x41e000c7d411659801d1100807101e00d120045522014046e00384401305049500f0b116005008028064044d50007a46942080c403003503001c945607903d021004c40307a030500a449030404d6500c9401d50066964003041c40c8440040a4503280c03401c413a0700301c03e901d092103628140d0b030107101220b62901e01001072502c00e100c141c0010b010110244000998241d0b00019a90420303800108a8200805000803800909160345402450b1541c3d403440400c00d4140c110000c10b5078051241030041c0454890104410300c02624000c0004104100c4200864401c14140f50403e100e4070540b100100c644001400c549100c1c15071310340032543c0b401401a511322230100c040390318845c3c1030140003051401001074001007499442d8442c46480d044040100070043e20740583d03501d4444450b68407403040c05181640c50100301d80007405a07209580200d10000203880101d94900c1290096213042410355070a401c2d40409402c0c021a504070760740c106107052a50250300d200b1079501100f001e86107459545c414902e520403e058 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 538144496 1250 538143246 538143257
    0x403021507170a020102071b090e03040f050418080307030507030b0d0b1929030c010203040b07121101020c0a020301270602161217060906060a0c080f04060801080d 72
    0x280c000503a1024142840c244031204561204100311080e8007a00c1f40c102d000707003892091108121240060b0b03291005495581204116482c01e00301d200b55603100d0760240400706a0404000c000030f24058200b4503501c500249501028401a80c40b0036140e041035a1007404030751900300300810240d15118002c003c140489003607110b2502600d460481820242042c03486006410307c01070340c20034940000f41c200315401c501d202c140848590751190400c4038045030340701c3c4c0210070848091f584000151020384054202c101d14082283d03403180c400f200406038100500801070f45d0707140020001e102401d04491064040c00000f13140788100b40c00c41d007000b06040c0400340d1402000612900c1e208520b50030960041c0010380c1d49a1191016444845141c40103040c2c403190824440c00a0b40414101200c40910050b40300300c0d01c4200c100320120004a900d160405024060140010310813003a0b014034902070014146070100d5950b00324041c6e0310903004500401d462000400c0689001c00c0f11100440c101d2808 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 538145746 1250 538144496 538144507
    0x1e090b0c090f150c0a1406011706190b18090c0a060e04020d090b010b0a020d0f170630060a02030708010e100e01090606030b0a060813081e04030215 65
    0x4803884002000b0034016290343c9902418186000d040b102100003200840f40c60b01480d1070300c2030881c85a00d8460f0043d00904000203035038a031074074980e607001440c40c000d49041d0799803090300c0d1100000c03c1039034480a610756912418984607182003480000700c48541c8101d81c60301001807031a000701a00494003551813a90708200d8564042c48a40d29504100d0780980d80d918210326440260a00b2079018145540c45400090211140c900030981c103030590302560131140c07140c02d0a542480d054070032040440c01c4042c0d15500c882c148a0016400f038030042140141e1303c06220080980310048c0e0b5402050884115000301c080030401405a015012080644ca94503041030000d03c2c012043c0b09400302c5403040c81c0406c18820129801c1800345c0100c030f403800d039550795034580007014110520401d000300c0c0c07170803002e00c1c0642049500d45040d078003243c659404070344401c1110401514508825500000180001c0c040d1050004000c45c20041d402c03d0580ca8078190700400038440f031004119003406808004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 538146996 1250 538145746 538145749
    0x918050105100e0102100e070302030111070b07080105100c050f060c04060318020d0803091207030909180201140901050c160302030c09040519080c011b1101060f05131e090b0c09 78
    0x44100e410510404003165110300d00301808e103042e4458000a41c59402c010841004a2549001e031454a0083c40690026203510105803608002801101c0c0c021140c1000c00c1c0707206000e1107000e0000b0b4421012521034400c1103403c00d04120080d58542c401400015040040780d43c9802a0b0803089104030440c112040f440e80010342084031070900030403139540800050107143c428095105000d603c182c030540e441030186802055495030b0300600101c0351030006003080d01100d03035206a12042e81a102e5003284046465484102c0c0c01003a003030b604100713040101c45100842130007032207100c00f01c02c9402c045060a41c030401d404c114550818078002d08482d010880407500001e4010109482c0c660b400d0015140790606590074401c4e000d070003096601701402024810f81580c03428941460580d12004c42032820242513003038031118403c0c840312000c011401d000524080d18000010402c41c040080c0c83c100b081c0803121121201446001201d0780d5000c04402c1c4a43c41502540c010001142c1ca85030007203400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 538148246 1250 538146996 538147003
    0x71101020424050705121c060302010c02120c061c05090604170904060b030108030d0608010506030a062703021e07031a04021201110c0c0609010f0507030918050105100e0102 76
    0x20030b85052503414848095800d405002155803994000f801e803030103003000c12180802c81d030210f6098891164000b00f901014003043c8100805e40e54169507009800000e6004c00c0f034118040400e440c024044c0841c80301c942d03a541c030001d05881d0590226006500380d050741c0d03e02203507002041512a034026000300000288081ca8060300c04968964250f00c0740c5601d0040340c014003d5030003100800200000100301c00304000042e1010342004071043c0005501c68054a00b0388070195040c54040d880101c906002941d41d81154525196050b0920a2044007030f220120f00c0d54000d03025005a0406a4078074003500d04c060056080301e03040710003812000d2650352604500c24820209a07042d41403000420211b40d034061201021900020003400303102800010703606c15500200304030000e8032503040c0040705824500e060302d50810058484401c0b00380951000d03103455108080c02c404018041c1000310310003451000c0301081040710040010258101402d101c4524012002c1030107010300e084003100e2036070740003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 538149496 1250 538148246 538148279
    0xb1c02010206060d051513050d090315020c030d1107030221070303050601021c051804110703050c1002072303030f01050f0d020d0b1005120a06050408040e09060711010204 75
    0x40d10181551125803d0590502c01c05807000483c1c241c06c4000d21840702c1c0700720742003440300303000344141c0702070512040c4251402c0c00356200c01414060104909101e0200316405864402000000e803490320031011001c504940609640394100c50020800206040c0c1c1006040a4869248040b10201020b200080a180108a0000c0806850f240002c410b0791082c02100240110100e034071810140501003d0525040103c00614189912980640da4036045c01041e1100000c014103502d00754254600b180c071941b081085500c54880c90310021111039140c80200621402400c2c1090035403c12501a0b0590358403242d804201c3d03105000707210f0407039010800541151011120f000c03071081641e000ca458040010b00180d400004090b00e941130005148070588240d1403400d44000f065114402c002e806070310920701b2012030b4040140c844c00503280c2e80c803494115001d02c0070a401d040d507542071340b030052408942100e13958012009004003035400c0320404002515000095090030b0411444416010f1078 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 538150746 1250 538149496 538149499
    0x9060c070204090f050a0b0c070c0b0d090c0905060108070c02031b150a030e0105060a060906030b0f060f090102010b09011a1c0c02160503060c0304081b0708010b1c0201020606 77
    0x258000c11542d03180d00c4000244c1c1d10002d483c0006185080490310380413214415194071726041d00044a000c1600e045404003644461895501400d02d48800c2e0036400c0302c10075101d816510528403000ca00203540400c01003100c5075010031340740707000c1000401c0e0141c0600f00c60700784280d00450000594000c9400c03412040c2d816440d008070801c28002030a40c0480c241c9241c0d140d500026404541035243d0030000c00006d803803009000e242c4030746051020441c0117105040c0014400c01040c04101c0c801d801c81c803c0210700410020680c541e69000400e0381d032100060f41200e82d030004000005503028001c41100f810121000b0f11550b00d040c80c02400c904d1405040364107140c0015105490034210807c7c4d54030201c42e110b08002704d403400d080c00303551121b10341000540c18000b84070000d0146400129a482040d0b1200400e0841d1226650704680d45c0050760020141503142c1084080707030408100300310040c201e40b400804c0130b22209040c860384d0801c0600074502c0d441c021a8031405030f40c001a046402400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 538151996 1250 538150746 538150771
    0x92a120f0c03210a0c0b0c0703030e070b040b1806120a1802060a03020f0d060305070e090601181a030d02030d1a0a05010807020f01050c090a08010216120309170c12030906 75
    0x590000446101c0c03945c00008244403510014491101000c101400580307129440030440003504019442c1e44040d90300c50039080c2501004140010300900010b452503000b64043e94a0018a00000030100c0d04084441c0a210b41c0b12010413850310300b640181d2401090f021441906060141c0110b03401d4814640c508042c0b5400050004ea0402c0520171140c2a00240000300003060b00c0740703081c0d625034007a4031880b00c0d038813000c0011941781407000ca010340c126941d1000040d20041d9142459020b4040c03d6420147d4590350f00c0c0c14007041d04c080c002c5100c406100c5c3d016503038806820744200d044980010085103040d010cc070902160b5103035090020241d071024245900a582d4141080b80340a881d000c640c610f81d400e1500b03111413103d403000604540c0e08210b460001e002d071150003071400c0303000d0b000c1c0d442d030603400c2c0511a8000c16040801f04200d100b02d40380102e06000182c64180c010048021035010880317000590014800e001c0c01040e5082150302e803014a14100003407040d0741c441d03010b028011100c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 538153246 1250 538151996 538152007
    0x3200613061b15050a050609070c02090c221e030209040b0a060b0c010e10050717250c062f0c0c090c0c15092a120f0c0321 54
    0x2003000044014040d40854070000c00403443c1c01c420060300c0181e8220004074285000708505d458552000c510848095507142c0391924135030200f1402c10005001048032190400400c00741200807100c0e2541d1015000070080b1803490310008a203140110341c03069039030810f001c005000581c0d420f51940e400503004044c50601741c503034030207000c000e224561203a09404000602c0343c4a240064002810300114801920100c13404035840209880b4100c50240000f14035000002280c0384002e295600b0040c01c6d80040003984150808600c480c0030800c1d0342c1d001c6020304003601c041080c54042c0300700c91900b41072444003c109004080c3c203007040c40640304404000c0424800b1600c4010044c040700e4010080c54181242403040b2125107543c0118900e400c03d0017203c0c410420001415800e902a440e040e000302003210001e00100c15100700110300c41c3d181000349020101a684101805d07154282c40d2000c0d1401d6100603903140d20b4072115800d050b000c1d4200001541d0000702400c49210368541c3c4400859854 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 538154496 1250 538153246 538153277
    0x230604090c12051e010308071103030409060e090d02070b030c0f0a0306051305091c03020c0d17070f080103110f09040320030304020f010302160503040320061306 71
    0x140115040362480c640740100c1440541d07840382c6103003644502410100001d4440343d20b803c8004140c20050160340035000300402c00641c451005010762405020199209011540007904650050348440e40b8261688810b03c42c040b28004501d8001c00400d0007001000f441030700103904c0d02c03d04d00ca030002e149401f0001410000503a0211303140c040e01511460381e81c40710041c0180081c1600d010b80c0b0b01940d0390540141c12401c2c0792007058017a0b480e0000520403264480805100c81d41c44504da1810981c0900076000025010002032101c103045440e01154600f031500340c55042203005042344100603414480014a40d004458541500d400071040306044508a0101e400e045d200c1d10a180c208000e00100300a1590088050385c0401000068013008600c60301d1081d543d0009072006544600c545080402941c040d60041c21142c844811244071891036480711030654110764010748400c0d03400641024820030020f20101183c408941441c14885c070f18481103402c81311802040103200c1d4100b00001d04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 538155746 1250 538154496 538154509
    0x6101710020c100501090902010e060306040605040504050703021203210414030c0a05010c0e03030f091903052506020309011110020c01140c0304081204020d0b041a06010203030123 79
    0x80540d40c609566600221000540c0d0ba1034840c01072000a1801e800402d200a0601500c900d4540503940c2e601004414001c000c0c03d64406460941e0055854100040c1500d480c040d9910450180000c3d10266140d40180702101400d40c60000385508100304629030114241140d081c80f03912070f52040c0740703581c8624245050500480d03c43c12148008142442031240000e203003000d02b80b14038001d010b03c074030503441902d02da0f130440d0303003142e064200788420340355030179194094266040300600d016603414004c82504c0c07200c1601d410036940780d0441200003030211003a5a41da01b0605030f40e4000d207101443c107030000f074503401186e039107070b041100302240c0015980c0708008052619600702d40031076603034081c40e005500a15170028641c10a1401400140d0042444d038103581c412600205414a0520707451600000c10800a0040342e1042902c3c1031100840d8860204520980c41900c0ca01810380c2c16442501c1171403401000c1a0440d0303c20801480040105005000e9004000314100c21a64007140010701 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 538156996 1250 538155746 538155763
    0x303191104152a05101109040b0f04050412082203030902031e030a111506010f170103030504081027020d0213051f030807031209020d11030d02061017 66
    0xe200f00510340310702403144403861100d550720a07401c90b03182640e03402c4050290b4807514940001a141800300f080c01e8107080e0040800e11300010905190f8801500c00202220360549040c0d90810040c0d102d16001508401040c2d00520105514103032581c0c509103858121354507880c014101078540510f6030031928100141070900740400b40110054004e402c0b0182d41380c1120404000041c83d10310000c69030301c408114000100c50a006030b14850f81d40000665a0609002d40d0304104080c1680c5a6040e5650310b401134007862003a540c00d0354940c5008020f03441c000c210b42440d099070340341c4241441c001800030303e8244641e19220320408c40d02001c0c0005208440001030280d0850b01007100c000701c20304603600940c480c1c5180400c03031510b54011178010480b514a03010040c001c00080142401090144883e140070401c0c815010901c000503902055052205907411a818854001c1d81da05510f0280100244207500b4030052249240540003110341c512a4070920f0f204e80741101d00c03442d0010702032050b2403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 538158246 1250 538156996 538157027
    0x121104020903060a0c120501030b010b07030507060e010605120c0907110f03040e061c05070302090411060703030f061a120601020106050607050604020102071d0f0c0d0e030319110415 80
    0x10604c2c9004040b10000c3d00b07546032503400282188242c04c2c010301c0d00b4810141681c0d0002e000b00201d03800c0403c940c501e42e00c074920660520005000460006601e8002c0398440d28062001140c42c5281000b440540300d410390303804c1c01c6a0801c491803106a00d0726040f940e4000224a0040320303090200710400c2c1072920050010380c05010005000c500036110114081c0079540c1503401c189101e21108065840440301078000305660030080c0100301514002d03042681090142c002c41c0c03150300c040d10004056611494088011a0b164000401140c849100d220b00800030700c1034420036100709441c4545544101d81c112256078500d0380c0270503000e034403d40c46280a8040907140c959114000d0421690340d520840c0e04a0042c49005d42c0440e110108041c441c40030300c0800d440c14081e4403450400703036250100605451074844140b080340300c2240036000d844142030842d0041c0d07540b42045910141610740c0e200100389000d0034000031048081c04403007110203e890b10308482c82103c51070441110240a046087d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 538159496 1250 538158246 538158253
    0x10f1e0905180117030c06010315181209060504050a050d0606030501050403120b1509010f0c121706060403050c10050d2a020c060d0915020a020f06010906121104020903 74
    0xc9592040c000000342c10794040e143c1803102d0070500c41300d1039a20b00c2021860311aa4018a0041000900000e607820081c0b1070031502007800c16801d003076000e8400710900c0c02c1e581410791403a0f84115a4002c400c040c090100b51038500d1400e0300703000129054101910515000e270842c030591409200c604c3d0701940c05160f004000740b10b1800c1a040017068100c5442c0d018441c0e034a0070a1001f910b150000c0399054030100715404a08200c503000040d6910507191115409100c502c8004100250503400c03d03400404041e1603201c1003d031010204540400010201030081c0410001440440c10005000c2c030b47d280d04031100b080d645c00701141203809020b1001945080d504121070301d440ba0441d07101002c01c0d549151010b04d442c1c3d0070000100e03580c1076024102ea40264081010000214140e008107032054045c0c81c00c2400c000314810114100c0e4000d140703101c010303007002e001c1d40341000060040b580100b41c0703044280309050424000c40c1c185085500014140d150314007111040740c5907a0199014120001c055 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 538160746 1250 538159496 538159519
    0x60907172a031006120b0109030b0a0207050a05060703061d132409121d1203041703092e081314070e1b0306060f12040f0b06010f1e0905 60
    0x124803d07a0581d01820010903110b0840c01140501889000c142440c160741d4582c00c21300c0c40c0c4404016a20150081c0c0c5819020000c100201324104120760015102c0d00092045280ca58001012151550007029480381c1c5014000408000001155001902e05e4446c68445556140a08501002c4016140011650036071003000303600503032180075401e000b050080c1070b4000305541101c048d2610002c0c07040804069544000c20f0826031f003980d0700d600744030084910b0036844502d1000e00e140c4a41e20455980e0001031031840500780091030220071413205084100710641c02c080701032440986c0b002c8404008022000901000000145464042d040708401407903100f16072041e500c03038143d40100d00c10411984081191000002e840b80d503000710ba810403e0450b100e010410a0640c0030b4040602014001e008240c204c044508055005900c188080050b001441c94205500d000040200d8140240380039405082c0381c001c0000c0291400542c112072034100103074001e40d06071900c0c1d0070090700108400030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 538161996 1250 538160746 538160761
    0x531032304080d0908121c0e030c03071b0602151614040305030a0801141008040c0e010f06080912040e0702100615020c06040302010c230114060907172a03 68
    0x960070513030b00d00030155002602d00c46507584841c1f180c403c0c0480c82d60452442d803800080c1c950b10924020001300250ba240c21808d90003645076811035041514104540e440c11540383c115407501c0d00090195001915803602d11181002d10110010140c0286035807181c00c1f850342d94814012118102c01d039460850312240c0341d003400741d503039041207081c00c003c541030030f0020540e8806101110021800108001030841aa101c104c82610000c0e00c1240c0881d0340b8030011900d080c42464240c040c00e204c2418041e40340c50b02100400130103001d8002c1c503c1d40c00c6914010510107540d4121400c0d91824204490705840e031303540803890040e0038461942200c2c0303821400705201a81c030b810050031001d19402c40700454004010064248102d120090104900141c50000111284501c90761400700442c1651000440312030617003501c60f11401c50103422094400c114283c079000348143e4010200e45016203480011523011000c014000d44135596800703031409020010000b06510710060080041d5042d1a401c050a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 538163246 1250 538161996 538162007
    0xc0c0503030f03041e0c061202190e03070603060608060603060102340e0f0406110d0608161706061e190602060c1e070f02040531032304080d 62
    0x4c50885084075100c41011001c00d40310f45a0310b00e55040201c03c04410726200d0103031542c88c074071107003900101c0d001d018040074121103003052184003585031207450030011080201418404141c00c4a81070500d440003d0202a90011110354440000d545040d900d80356180182c0c54090074100000700f010001d0b14540c02e040000040349008102d028207200600d40f1011240c0480d5812218940040890b500103030104070560014102e04084003840c62801a9007940c40c81600c501e608409410750080c420f1256010704515048020881450785003000304002000d00d0f10b80301c018003481d104072030000d40c90b580040d04607881046004014402c0c039280e8820808807015060300d00c50030015000340310004a1340002c2c1821034000d4007040d15010500d80070f490240f00c40760010901590707018110416000161035a1042900540110004400489400d400010360680c13100007004081510b08185c00060340120226241e00100d040c9403d4802c50300d0200f034100c2c00b5550060a162240c811740340000c58201d07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 538164496 1250 538163246 538163251
    0x70b01061b060b220b0f0109060c121107080a0c091b12020913050105040c08040812280e0f07060203160809060403240c0c1104140709080f060f01060c0c0503030f03 72
    0x46d140c10399045040c10054804010314410840031030305803501e5000090611950038844542824464026000c1c508403601e0000140c010039040d902040b1448280005000740c40020b1076188001d2144000654500b6034286981d0203c1d414491400420000d050168050300d468030b402401310950941c070400c0e0744001c2c007002e11802c3c1c016403030200724a4002c0d1081742e440348640d401c959580d2620714034610614440a00a080203a00c01e2002c0c03034001c640680b02109030141c4103501c00400c0241e14502c00d1800c210316002c0c01c1041e68004030042101e540c01009856550712036001502c040075490402d00184e01c0f41040e0160700490020b000300030820403c403a03610b07001040c081002c225103018641000c640305031040c3e6000c15038030380d00807001411300344014001c0303000a800440c0c1411001c2d031a040006056076100c0c0400d00c5010103005008040107022130300902c010080130070f4107140d1162203103614107004007010403c2e0070020806002c0c4618a4100070b02004c0c08070790341c2d801020042040c40c2c00c01d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 538165746 1250 538164496 538164499
    0x1817130504020c0c1203031510090315020301060807020a201210020a0f0c020f060c010902090106023f0a020708031204031116140f0a0b070b01061b060b220b 69
    0x58000640301179000001d5a11078107000c00311100e1620007104119800441002400422071117403030200020350385c0c030490f07003002c18240c3c000360312941445800340c41e8400043c0603108540c006501440400c1e40800d00723410a1503d20001c4a50012000c04615000426803c0311040e100f40140c204000341d6650061680c40011b903500000d000130b07010b00b21194548401c000c1d6000a6010341815640380a074000c04100300700a0000039001c0c010f0340450120710b0241c0c401c501580110301d0040301d400742d1000e08103118406072411548036141c1c42541c9503540d00c03490f071140b1140740428019015402001403c001e040d28004903611040c505802c50410314085804a001034144003120001c5040041c07104503003d0307440d42c1d60010a0804c0d84100740850311050441e8000000c03404401d5540300c0800c404040c00000303172900d9441003a030800300c0983c0010f0784000e04024030b071103036110b500b24039211040010b940000045940e041c0d0000281078200354103200312514000d9540205100b50079813014100850 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 538166996 1250 538165746 538165759
    0x61212020f06010b0406082e0509070c02010909050606040305070b0405031204050108043e030c09090a120c0c0603050915160c05160b030a1817130504020c0c 69
    0x1c21400c040d0b202c19007031041c000c10800902c024000c05000b46a5070354050300908440c40808950f00d05503c042e14044d0b0039440c0071076080720520030b07410142c1c0c04640c00002801c04900448050307000074a042e1091003071041507903443c8085001c0b0b6503001b00f1103004541160448443c15242c0d80101800d60040c812144a8070690741881c408140000070380f41200c0d4140c4038080c0aa0780e503140d00340d000170507480800816260100d04804080310103030032000441400380c40c004001412090501d0903401000b0948601441c13010003080d4040000c480b1441e07544404060a0710303100c85404e0700c07103d1a902c0d0007010710910940c007152055041d4072480c422803458040b030f01011424800d40c08182820f0b5006100400e069010403545409000e541100a1159003110b80070445074903a0700070228181c2101e41d660038000240a441c800328010280a100b00082d03498030440681e581c100000c10070342c41000399084c08140b0340c43c070745081d000480042c01c0240c01035503626004020a901e480500895030322800303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 538168246 1250 538166996 538167013
    0xf0f0d050105030a0f060b010306170a02010216080c010c0305190c05061f1a090a03050705090901180308130210020606040c080c030a02130b1c051305100f06121202 72
    0x240004d042c24143d50040e840d2008290742ea11248041c010f840080c6044c1610785800044281400020001d8120f4a001908a040300d51000a007059501e40c3d005149507441c40c400c2c0701c40c0c4008684428029002d00301610300f084503140560b00e50041030b03400b201c9021400c0030510f45980081410001910600c213561003903407221101030f0701525000341c8003008110311005211102c0c00c11104070904030a40065814600c24100041094220f500201c504c1d4228a00400042c206451031070b8200810070024072150000d02c24071b191407410a94040d0403c4035600200303050040c0003000512898000d8160000c000000c030000c3c0d6641021380c6d03110f00480c500740c00000c1840c0b05941090190480a000c0e901d55195022501e010390014402e60b0301c2882d02a90000309042d4943c010400d600c00400c0030201c0f90360794850301d0203e6000030074001c1000f480030b000d6400503a0120303425500c1e207801c54000400b0306141031b801e8024490b54100d103120b080c0c0c2c44c001905029550100c4000a0720756421101c424 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 538169496 1250 538168246 538168249
    0x615160b10030303052214160b040e06031c1407022d04090b0f07110d021606030e0a0308150a03320307060f1404031d031204030609080f0f0d050105 65
    0xb40100803a03041c0e602c13031b900c5614002664010549200721111001c403095010750102184841e40b25030b200ca030780004000307801c20551800c008005ea00c55411005072410104019210425134640400901004031104c6c400207910188000e4600341030f000741204c660024100294556050414522480500c07202c95209007441d1602592a00769404000032440f03844410f444800e1030720281c010820700034103564100503400c0410840450351f8850340100008154200d00b0740311714185400200c00c050a180d1a811f940b10001407640740d865051620b544203a942800c0300500020a11718107601404014001040c80750240c0d401c0c0000903181c00144108140c0c0e0f0003a00e080c04503401c0302d80f09400500c45c080108080340e11100c902c202440c8042a540b942c0440400c3c8140229030444c00300d840061000d0007000d0707024444290040640003004121502c0721152010f0040c0e1100030315844e2209107000070080b5038001d40386081e07802c048103926610b041100c0d00f41c41d0044000351507500d20302070000a40303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 538170746 1250 538169496 538169521
    0x3080708030a0605041a060f0c0102030405061005092203020a060606021b0612010522060f0603051b0f0a0215072705060d1a030706030f060b030615160b1003030305 72
    0xc8414030303003000006c0035548090248981106a805001900c1031090007265402070000b50700c510b102d000a440c1501d040d0707046c034071035101c140c10850140d0148010085400003803404840c21310b0901145045124a03490228035194192000801d80d40c01d007074001a02036000242d4800116640030307100600c02c102800d00186000c1d01105507500440ea01c0104103034142445020000e40040340150401c80791442882c054421540c484605821106020002954548109904509440c020303500740e4001c4c1801c4d851500801c000400300090014114164500800c00d41c041c00b1440740300d03203119142a40000c2c0913a95001c002001e411210101110717401c03100300351030007a0381c1d0052099007081000307030083d030051010186807458a0b54108402200d65003c0203840000c1055507004103c2ca8000c2119105841d150f034020710010301c0910030301031103548441d0030052080e12420380a4031411301c0c203809880d041a40002a11075420314007405481c4948176440420b41c0c0c0030380c90903c255220403078074035407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 538171996 1250 538170746 538170761
    0xf0d030501090e013e0a050a1b0c150918090c0b031306112118190b04051e0307052e0b0307091d0c0105120403030203060a03080708030a060504 63
    0x1000150840445c0d560504054190150124040e407a5601080c0c10740d0070005500000101d00030804c00710303c211038164003007064050f00c0d60b0680e490754540e0b031035600e2030345529041c01a00001c1808010700181107100e0785004e801801031910195011012445420040801c88025280c0c00e0540c0c1021820406050869004140700c2000102c070840c55140c0c5402015108120544544104001e441409604135200c0c1d000b020a82d644003181045100800268103940f1000a150800d00002149400c082c0d81e1012154100014520075071365458224180028107443d07154904111110354140c0d01c00002512a40e0320401c202c4070119041414005055407000460b5100640c9214003172072808182c00441c007211003e42202e414a0303c41c100c0c02c042d0b03060681d0504c002c0341c5e01c88041e56445001c100034400c414003800c1242c5403120605600720f0100300104041c05140e00003011580c19283c3c1d00761000219008081b461700c940a82c60102643d50043d24086044c600705080403401e440c15200b046d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 538173246 1250 538171996 538172021
    0x120f04060507060212090c0405012103140403050601030813140a0504200d1e020c0c010c0f02100c0b1803190c0f060c08070e030316050f0d030501090e01 67
    0x905151030300908507a01d034001c960884015401344601076000c080400d1480c0035403183c401810040c800c8600703001c21540140e10071303c0700b540c100d44044003442540180340e000c40d4051614100c0101e10481d400d50301d2080ba0b10003480d500c2468000001d1014000250030103004410a050040d40c2d13400e15060343d01c40c440240c83d8024085002004103203481d034080000d40f05040c0400e00356a40b0b560990f0b840340c021315590803115441d0718114400f1041d5201d00328250f0840c09045041c08104190a50340320b480c0300ca400c0c12b001500310000180084030b40307200d07032065000702000c0318403119a00c010310b40190000202c5401000302c0c08982d0b0382e18001f50408810607103000075420050510b40002514846524500c1840b0806c4c12000c00b140b108110100154007428020450080c600c0000b450040020901010051046a00119641c01004403900441680511440d10f60107003021030070706c40c01d841041030510410501410b00c0d50035400c513604868101204204020510701241e00766006400c106 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 538174496 1250 538173246 538173277
    0xa03050604030e1507022110060f14190b0f190c110409020916051b01060f0f06230f071b060c0515070e1e0301050a0605030a1221090512 60
    0x1f104002800c40000800c100c0340c0b0106c1c2c01c0900c80f10440811a06680c0204c101d00524007414088850110b020785106241681c0d41d19205110004c43c10094849000340e0054030310019070313000c01561100684000c0c01745800720301c0c0465050342d4003800703248580324105c0c1d01c01000c1d5000b030400d04d881c0c40f0b207101d00c580290100002e641ca041e10315600c28032901ca1030081c03190a104aa440030303040c01414203040c0c3c1100001540c00e080a0440880000c141d01800e0303000705a00341130045039408120007080c4020b003c041e440f2000802d20742235150003074000321544024045099420300031b180b003803949580c00c540420b5858a888403001c540001817410094141c5e8002c0d41e00c42c422141d8621491340c80710705403a00c5500b82d905480051030181c061304414030b141200307400d0f955a0b45000e200e1190040c4e03030110100300c89071400380841e840d01000034001d00032800c081c0903000500d00840342104034103c5010340254070100c22400600601254509441038420b010980501104c00b904841d0550780d01c0502 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 538175746 1250 538174496 538174519
    0x20a08040b090f0a110307240e01020c090f25020318040608060c0703020105090a020a0909020103091b2904050d0309120818100e0d020a03050604030e150702 69
    0x1c84149000240c54640305109501049008810522000c0c40c030a00c1400b1140310404442c08040c41c1944d1604071030a81c41c40510107026403880172200c000598454140840d8107078900380140c1c10945403206080e0006081c404201b10340e801d003204e040c0300380c01c0742d4805e0030508000031041b1500d05c4454114000360344100b00291071083c1440e080c088104000f8400f0134196207581c5847d090000680713400b50f0416004c141d60003010380a0003801ea005004400802542c0156000605a130459100300640603640700815400e41e4400d401600d500c5401456001510018409001d00302080d0b107d005141001101c0e85851002400d000c094500004800e4030708190400c0c0c00c010361250391200c201e050081e000d100258060620100010301c60286103880e4807800c0702090b00302c0e607205445040344642c1c00303603064802054104154802c3d00c142911031542c0ba809610124000640b103402c003030040c1c0304100c100310400d640100c18000020050320110341c503044000e045c1c03007e4054280c0013988100c50008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 538176996 1250 538175746 538175753
    0x809040209060c1005180606030d080c1303110414040b04320304030c0501080609041b03050f03030405070b0c19060f02030901090506060102150a09051f060315020a0804 74
    0x24020440d40144201d1034001035499842c44c1140700c10b000c1c1c400540f00c0e02000b00c100c80d0861611601c0c1c1155000d0001c5182400000c2e4994490f143c81000b0f2001720030200c0e480e900b00c6401d803907441024045400c00e40d501c9007003409005c01e004d069944901c2c2880d843c181502c8041d0005c0d40200e074400c1c492901502c07181c0e146002e4a41e4000845082048521480010403146440340040211040959592800d5081c00003280d8980d4010505104090f81801041d444080d0a41d6001d078004007000443c001802000c2c003941080d81c8090200d01c1441c001703240041020000398004d0b0302c20760440e00c41d16503071410b0030307081e00581d00c51590a03004840780500304101c028141d00c14a100b480001240350114507024105d80050b10b0380c8816179500e558180c100302040051076001103003400180780500101c0b040d05a005402402960019200d003100301c10840308010307000071994019044282d01c00742d85c16802c0102003d03c8241e440101150742c6e034080c0c0000d0710886103242c0199a54100a650f6a107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 538178246 1250 538176996 538177001
    0x7060c020d080c070e01051305160c051c021501050a030c1401021608371707050a0308100605090117064b220608060106120c0804080904 60
    0x840a4030240e40800c21540c0d208418458071005d01608030754000c481d4103101c24000310240c00748002c1101c603c1c040c2407261000c104075407104000c03143d00d4020501d2050f490064140040200ca0900710000501e600134407540108208640003080907420b4066039a4804000d64041584406481a00c01039000c5c4001d00004030000f94011060048464408002038500d5221001d40d200e030860f5008001070006003111401c95541840c01c003403650811140001041e0000c5485103030007440584a0341c0d0038034a40c20058190780407603810000b0b490110b100c60602600054040b182091900000c0d900850320302d000350261000e94a041c1c0d9180c0003882d0f066410003494201501c070076800040c09110a210b003d84600401d202a2580e2a4a07107040d40c075506013004d285014445030100c00042154003032921030100300206c4007015030440140004001442d4010b0000360086060303030044900124500f600682507260740b2004c0c8030b040007804941c420448600c5415100208084004c001034a040c1c6041d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 538179496 1250 538178246 538178269
    0x4150e07020f0601170c03070f090216020303030412020d020a05060a1a15180109080307061e05071706061206060a12020c060a0e07030c05060a2c0a0807060c02 70
    0x60040300c03000708503000c1c2c051901500340d100b00324004455491010080d4240155452007000358000d00c0c405041c05400203401c0b2050044e036019507404071317030180c00c405010180302519801506607039490400742007003c0340800c01403a15000d44038840d0a980308610001d610740d0f0a0740c01c2409096035840f10391069001c1d28062039110442a000c46901c0e04580e00e184c118141c12985502c401e82d0340c9418800628001c01d03041e000c506101e4007003000c0180150100803114a44d600a01c0080d07000503040c0404c00e158030214508800c03d1a0500b00288035410074500311754109000031228840c3e840000704215440792075080746d100860b4002080080c1000c102504850140341000f0780d4010401200500300c6e0000307103020340254044014488640103d00c034496013403000401800e042030840d2070302e500c1c40c8514441c950245c1000902840c0e094070810b401c02c2444007642c1080031007900e0300654100700c99441ca26511601889000180419000800000301e80c1191103c0c14102c846808100c8000d144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 538180746 1250 538179496 538179511
    0xf0a0305071403160302101515050f030f1b0702031504080f07030207050a05040608060f0604020d0203011202010807030e0a0327060918090804051c060c02011a04150e 73
    0x303960088502802d00151061111020503604d0901e80c0f41802407034002c081200360741139032900c030b0400400a0030907980c80a03602da0708001c16410f404440200c50074481e00c811441c51710000300c00e00c40e0090070f100f00035004601c9060020702c400c40d9115021a1441040c9009600d03621503200b0101c10411100215803042c01125550708200c40c8050144056001c2601280160001c0030207200c1845d0032000300003c2c04d8261410024181445195170b603c4030003904081213100d0003c000f441030780ea40d4044030220501c40005640369603503200307030414058103804128045007200c00002c01c11f80c42885031843c1008204010301012010f40c42c2078900181d160010340468504c1d000d0700c180d2a0316500213000800c1642d8500740040c0ca4a00300b030410503c000e00000442d81000d4803440070420007016107003500c000300d405190060300c1526010742014025030051555091803003040110b5019031080c011200200080d19074081e20b9020031041303c0303c0245600c2814440034081c08088903503c20b29600c001d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 538181996 1250 538180746 538180763
    0x301121101020a120302040303200304170708010606031415030309010c1a0907030219060e06031305010509010b0f040e070e04020d060e0307023f030904090c0e01080f0a030507 77
    0x43c0c0e01c9507200c4500c201400d0b0042500000c08000301a031140c00fa01d040c0d030704c81018080908080c8091a120301c07851140c0ca03406401c02121121500007400440c00412480001308007003955042e000d405400b070004c01e0301e40e50b00c50100280580855900e2000215002005103150110360350040d5846410454150f8070b070070f69102c400c0780403504036586a01500243e401001c59a00d1441085550707a00c011102c41d480d40c400000300b00080e080f03031b180e40420b68101d60a070341b82d41c1d880d81540c41000c110030010700550700700001d010004406500104c082c00050b1241d10204618605100540b01c40031003040340d40d440b8800c10040c0c94420a42990803d2004103003452030082034980f41c0076990410755500841e08009460011868841c2c0301e000d1700344044030010882c600718a84400110608810003004040345441c18491860501c12a00f00c0e0b0b800900802648803241444134070491107000d001002684000003041110000039011800b80c039010040001c0071301690b003101d4581052004803180030303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 538183246 1250 538181996 538182013
    0x111061914091005091203040602040e090a0c03060b060f0307030605120c030627060f0703050604090f02101101020a050c10061a0c010b041a0109060827031204080717030112110102 79
    0x1b0342c84000d60045004030009038660b8208040080c9946c4050501c04407075018507150390020f00840020300071a0340081d00020742080503404541c0c42d1183c40141202401e000003000600c0d074141c2d00800a03104255100074809449102083c0d4850f44902d52030380c1a0720500004000300e00d55039158038103941c10b00c0c0808035240381c0c0421618040090701c54002d0049400201b040259245c400d582c0d1204088409204c0a0585e848005071404c075000040d028060b04112100d88601690221000c005068021562010000c0303006111750810061805c3e10301402203205680643e030f001d020b05a0b400680100300340c03000d290128455a01c565541e07031055407030b00c448134940c0e81d0354441d0b40d42c080c20300e00984507200c1d260400103050606503000307842404034030402d100302c0300b40341c0c941e85211640c02003a1441c00c5130500c0059185005240191820701340403010002003080701c001034003c0600c952400c0c803012551560700c9000780024020055004595000c00d03011900e20f600d0403032140c0c0706005444004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 538184496 1250 538183246 538183273
    0xc060a17180a0b070f0c080403020d06151202090f04170d09080d050106030f090b0601031a040e03091f0e060a03020d090c05120601081b011106191409100509 69
    0x1c40704800986900724900f04000d006608403280906403442403174664040001c965403914240514040070380a580300b44e840b50200820b59000317490035202c0e183d03568005036544501080d10f0010386812800b41c00c0070707800b00d8003400740c80508a005942c00100076403080e4884007101e0140d0800c0c0070400e00d06031605505404201c0d10307801045144130711039011070300c0d605128010301170b0382e031000404120610348480f96010660940403180c00c8082445c000c11284d0a641042c041410a440c649501618020700072402900010040c2502d01c1c042c0c03064030060000e01451102e01c3e490f51480c9011490724881180302d40380c03000090500349143e0500604104410340301104803803024004494548641c0402c3c802894050f02201d11036070b841c0001d0100c2e6042860094850340c040c4821a0420451031483c802603008807030000f15640c09d54115000d929100b2285a001c50000d122444450301e4924040c50001a40d410300e0b200d405501d00130b0285d02d41910ba110700403c1c0091013207000b40900ca1020440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 538185746 1250 538184496 538184503
    0x6040f0201320d230106030c05040305150a180b070c02280501030b03030a020c040207050a020d030c0308130812070311070305120603060709030809030a02090405010207050c060a1718 80
    0x8071503850001d241c40c0c101089903c011900a0342d1000c0f50f00c5003900e400c0c0c0740d1001301103d45041d9411444e0206081406a80a403814021074000400c6401003000380b40240561103061403007040481e1b402c5c400240d0352002c0900000f04120060030210080001501407801501010452032002d400e03910312003c0031206103145803c2242e00c4c0c4106804803410807141d84e240c05039505200d01200958a001d007585070296079100d50541d01e9000c2c40e000b1641074103010041c803c41d210030b5005044241d0449903494020480034000c602200840c001a0108590309400300c0c1480c0740c56071002d10980361508141c44910b400e800101160201070f249c54024034144008005812240d104e80c171240e44a111420741740c1c1e81c3c1c0d54010308035030082d8000c0041021507a8010003603030449400a004540e03482d80440402c0c108000690042e40110900c018402080300c15030003170003400e0042054130085850002003228501c11043c0740e00c001100341c0c0c202c1243d507141115198101d030788000324018501c1a040075509 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 538186996 1250 538185746 538185827
    0x31116060c15020408030409090c050612040c0905010506070b040c1509050306010e06010c12030e030703110c0d0b1f08060117060a021914120a0501051206040f0201 72
    0x1032140480c2074200200c007245800041000202942014204407007250b480c010b501c940545c941d02e8401c1a42840b04009441010300000381c240359503580b0246000c11810020703038080314090702199000461041c0351103902d050b214000c201b1450002c1d140c44004908502070000d448031802d60780001030703d1500181d400b400c6000b03611800c0410740b41c04201820404140d00440d20310100700708004807aa0f0185500c1417141e40b152806030041f0024608600621703003060000118440080da5400380b680084191204809440c01c490703d18050005025500f012480018202c8100340082100c881c0c0404120070001d0342e10101c007900c95980d400052824000303070311410756a2110407040b00e02850900c170b025803040303d0303c0e4103501c1c105000c62500c81d0785410244141c104001c0314151000d10460008072014640b032101c401800303041c852070340d01c001d0400780314240c802e01805101c01c00000c07000c5010b40c8541e4202c2240701030a140c540041d0b525004640503e200c65032031a134032070079080d00c42c01e1809 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 538188246 1250 538186996 538187009
    0x304030803150901080705130b0d0206030c0d0f0f06060201090b071211040e0402040606080106020723040e0f010b04091110030b060a08060306060f0d030f030b0a031a011202030703031116 82
    0x142e110707e0301d410f2020340d610907071992480c071b03060050949140d2201030a985429506582c0320fa5130356901006200c0354000c1d5004090a90b00b40302071000380c420641c00ca1908041001003c03c40c4030f0340c80005074201c035030320304008064100030f1000624450168650b144540340360320005c2604441c0d950028001d91113070308039039000c4151005000030b6003418420800601980d0078515030301d5042180295486619103e4941c500b0200b44d0302d4541081d9501044c0c08402e006071060101032103240f003094640e43e807045c16030455885c02c0c00711000b03031405025020b4002e400c1a890783c85119800240309000e405101c0241c02c3c540c40e44800c04841e1240310041c04503d009076070344000e5044c001b04041c1030a41c0546130710312580c50580d03824010303034485400554132641070904001503040d451003903010341f8882c5140c560003100c0c01800001c0c0b01d12281003125111040d050786519030380701ca900382a0080b0750280650154003505050001901444000b401610107008494584030780c0103110401c09803580041c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 538189496 1250 538188246 538188253
    0x11040b0a0f0f1a03010501020703080a0c0b090d0210020415050f090d0b0f07020d0e040209031501090903080f010f0303081003022e030b0603071b080c01051017030403080315090108 79
    0x100400a09084100e000c1d40d0207405203444c6500d4200000d6448049002c050034441c400905014118010341c4001d80065201c01c0000941c5410a40c2546030100c480140c0b001d40240e004405007c00c0e54821142035070326805850403a0000b03904d0444064120312410880c40340c042084464503913070701d080805500d105031180000d510340205240308120000e000c0e4015507000700420068550060305080c7d0343c103c1075070f00603160148030700001e00d46051b14140304890b2003010008075403007070941c11000a05010381c59a84040e01c0f8540548428402403040c1c1c840400703a20740c1071002a10454940350441e0a00007003290a07626030700051008a1807143c0d6019424240384450301d00c8046002400d9140350a0408211003480c54000c04c0b01480014124007c005400c01ea04840601500c84500a203401664003a1900030000d1228020401556003c0700041aa680000d500d80840c50340c0c000d4001000c044c60030030b899640d0f80c1c40d0036000a040c0100048070003da40710261aa003184c41c0c02420058000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 538190746 1250 538189496 538189499
    0x20304150504020625060e1e07030c171f060501110604020d02060c010608031902010b03030a021213121a0604020c030403020d05150a06030201120911040b0a0f0f 71
    0x280032610000380c41035032410882003101503910403042e516454055000410350b2400300d82803140358001e0740002002c40d072030610300070040e1000081d441107404541900c101d503a03410840c1c03a03603546c00505c401440d0700300180c0103100064251809010358030b01c10f02180c02d035407000442d1010f140715420380103803000c0d0795041c200106d40e07004040d880c0705485100076141c00d09282d0045001d010848034041c2c0150400101c1c5500100e096215000800680c01035988512030021030b402c0040c840c4448000540c24204a00e100d40340100440d10b001901d600100b40c841000b0024654617040410900102c4a00c4240012802d10004807160003521030140742c464000e010b40c40c0c40c0c3c40100506004d001d42c0c41403018a0303010368000222030980e0740440c1d070303030484410034503049140070070116a200c02c0300c551034140404061160043c1d81a68801d8880b4540c0c407848180b40011a141d41c0805480c0b8402010154030b1810107034409104070700c01810038485c040c0c0301c0c0140707103029409620080c103a07100700300d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 538191996 1250 538190746 538190753
    0x7120507030f0e060331080d0605060f16020f10021e03040807060503060d0c03210215011211190801110405010e1003200304050c013e0f01020304 64
    0xd4140544010f801d286941c40722400215480d400024150304050031100d01124002041041c0304408100c00701d10011200340a260000e41ca40100c100c001c441421f040340070600c1d10f880c00a48481b0100c42806a0400003c0e0032811401c3e0004082a60450f40481e100da80c0ea032165103040020000b80d030010400f010140708140818030702050403401c160000d00c01440350340000724014045404500d842030b200e0b02c41074002440b600e13058400408912411000000300043d2a9007480383c03504082170807194690042080c2c0c2c0320030f880205031640c1503038040140b2060400110044240d030250004a440142c5a00800c0079948440f11003022001002d40410205d6000d001d6500c02848051080382400d21301030020b02020f01c0445862b10071140386c1c90b400001c40c800e600c040d01020700d0710103002500c040c80038500e04d1070340180c900b581c140c0100f490504455020b0561045110001d441c4c00c546024008454600020345c41136150103000c00281c44200041c0030800040c03501244000141d0303034249131a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 538193246 1250 538191996 538192007
    0x80d090b06030703030906050a030216030309050601080a030c02040f0b03010c27150e19090219081501030c0c05010e01061502070605160c0506030702060403030b0607050c0f03030712050703 83
    0x1040640700343d000c5041800069444150304080b107003542000e035210848240141c019001c1e42103e080c1c2c07020f00c0d140312024580e0640122070014011019100c617641c994032510740313440075000c0c054041115034100710014103045e0320111092401c00310006a800001d40042e09481c10700703071903900042d001f002240c0202c0d425103140d240381c0300d09000c000f00a4608000c01810806d40c0e80c0340030500000c010400c40c2501c1d03120f00c40c505000d0f40148250b84513151042c1b40c00139080a06a980b00781241c00c1015003582c003565041d030003076035000c441c010a9071080c40110701401102d140903003001130300c9007070b030300041d0342405503100083d41c01002040090620000e91002c8411072142070440d4003140c0d0400040350070104882071500507555481181d6202d003010601103125a00081d080480002000702c0280e0100389503020754401e81c0c05215a80711401006524050600058400c0d001a4124521881c182001c0c14407400080c0c00c1e01c3c01c2c02c1c07054031011a02d41c1401524408100002998403c145e03101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 538194496 1250 538193246 538193251
    0x602071e021e0d0b0603071707150e010e2427010302070b130507030b0405030c0f0318010e150a09090f0c090b0325020705130c2109080d090b 62
    0x40000042c880305101c0020b446000e030390400f408101400c0003048007500d0a001200152030304550311703150000b0021860f6541c5030180701e030080c10162440803c04082c031565541a00000580d20b800c06015840f0800035208001d2070751100c0550031440c0400c444184002170310103c4054030302da0007100c0f010482c0280368200d481030903040500c1000304070300190b100f911040c0c00800e5a034000300c14200601d45a842c0054607040a4080d4820b241000b0130000000001c1070680d808409441840bd03e60a5040e9603006c0c41d00ca0129184003000c05a0740713548607001c03155510074001c0c6000f803500000004100203611002d02140054031000007403100b01c0d42030095840b082e08400040090440054000b0400e620a0049914180c0c002000c11130000780300708610449246601d849500208068000c0e5592800c0d2040f00c2c068500c085c440440b80d10b0b5031082010502250300e8000750820ba40846600c0c4102c400d4179800030b50f68034401640822100409840703507a43c00b80002400400d141080060000e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 538195746 1250 538194496 538194529
    0x4050a09060b04150b0a0207080a080702100807020706051c0f050417040b041403010207120801290a081306060312090506160b060109051905010f17130602071e02 71
    0x241360012900d0039809044a0494005040464440103103640407403c0030325039031114809200741c0100700d017403110810003000e44c07510840c0c40450340c52402a056408030b00c115420360250b01700e080c041000700d020380003c1200d000e41c00c2e526014000103154440840303064211041000303640d0030402082003580360005440000004030542414a4520b031501e040c81140920000d0001c01800c081043d1000d4050704c95507039008a000424456601004000c600248100c000c0c3c61122140713600b00521590f00345240b1030502400b0f03890241d042c00c0c151440d0300c01801e580301c42c40c11604070802145481c410040550700c144c2c0701003007515195400418080607500458400c100400608149100000c2d1007440c0a5000004106940d50440181c44e40c103400e40c01243c120390f00b0b84100c00e050140405143c10f83d2340c00d80f914003005503803020484142c1606480c04000590140109814a001c40c1111a4041c07040340d01503e0001c6542e6490030b4602825422540401c000010000b1403506054242e0140c20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 538196996 1250 538195746 538195751
    0x1060614090d110418200307030b0c0c030a1e11060601030506011b050303010314060f0f10030c090c020705090c04210c06020303090d0e01080414010b04050a09060b04 73
    0x8100ca52034403144107418155100b03580c0e080101d020031103104000e0300c005000800070068004c00000d001541c1480010072269084900b882e56041204005002d06e528006070042041c107080d545d0390009680007500c0e0100441c030600c50b0480104003080100700044180d690200808036142c201003100d80c0015200040c000c030102d500054220004c0d907a0340c020001d290100380f980728400140d0310349040c1e0980d10008000215440140080000214104c9109400c00310007195035051a5031582c01c00d5034206c030300a2404e400b00380500074004040da08288034103007071020142e072655900442110786d0f0042c030105403643c0b00c0780101a010700ca008000e000540e420741140ca050342d030030034251042e4054088507504994800100c60300114020340440d5201d000c8041140c3c850300c0203075498104032540c880754481d102c6800c1e5440d201e4100174844220603140e42441e80c45070b5451000c007080ca01103c051030342d40d8110400300c039a40c5005031402810003d0001601030304138108071080d0385400ca0401d000d90f0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 538198246 1250 538196996 538197017
    0x90105090c03130c0f1a0403050a3801060e0a030305161a01060201021201090c05030a0f020d110a030e01050606070807020607050106090204050f03010b130c2f010606 73
    0x48801110300c1d40206031000d0746039a503680041441c4000c42950b0301905840a446010130300b00c80e008080e200b40c0d03140070794030480050002880e0010344201c0c0001092500f2910891001a41c02140c241c0516800b210b2a010251a400703070702001a01c040311409450b40741c0004000710391b0024064220030400b9034481421900b180c50140c600c3c401e502e00c1200e030700d8070320390400709020566690b001c0300080c1481211040d40d607460028040e4104408501200c00040000900c1d165988a0402c400c40d07151945821036030703510071004c02055611b030507015143c2c00b0031a0450020040c4580ea40020010401d03541b6515107800090889030010002d46540c4e16050030311115a503680c00380c82d8680c0e030022030240d9440d0188003003412401841002020741d8200b48010982d58400d0300a401613500503078103048188020002c0600f0385000b6078445820000c01c1400f9022000749400c444044106401c2500807217012640034040b242481c0a0000714a41c00140341c440903070b081c003c8400501c0640b40c08420300c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 538199496 1250 538198246 538198249
    0x9070c20040e0d0207210c03140607020f0a020112090b0a0614010c0c0e18030c010902031002040b030f06042c060a0e250e0405031803070b04030204020d0902041b0905090105 76
    0x2680317907000346c0c5480d4080200c58104140d070b050065802c1540840800807113962454440d18510388020080d0b07090042d10001400035100280c00084000d031030b8000d00100c00142c0040d00d40d0301d845880360605075182c40c3c41001003a400c40d111409002013010014040d0301d4038100031020304000750110304002d10102c0e6a001b140c1a07082d07104c1920f003440070034412a200d50840700081b1030b074043c58400f10302010405103011181940034190344c900940549054003200c100c0b2408900c01c600030700e004504248017295407030148a400aa014a0160000035800000e401c1d04140e20300354885680c0c1120103482d03424095405201030790b0856014030082c05480c48885030355851780800d0f0110410200c003480c2c0440c66400d01c1800034002e00141c508001c1c282084c0c01c2840e12540800386610314416962a640964200000d4007800c0368416040c250809045600300b0011750b104150030303203d0680300c0103450096501e501c190b00040804880620701c80001945c05007004801d0792000d88a084c1000040005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 538200746 1250 538199496 538199503
    0x6070302031603050604020c07030c0303080903120f07021501150318050a120e0d0c05041a13021c050718080a030e091f03030810050405041109070c20040e0d02 70
    0x800a0030f000caa15550800420000c2c015032158800d94800c0d1140041442000605001a01e01079580c0d2556a41c40d0305204d075591003094251080140101d0010303d01d0f034072030605150807482500c10780c1c00c120113107050b44000e41020303007040e103100440e91424404c8642500c1104c01d104242c0c1380b03a644204054842035141c50000802a000600340940c0890b07051140c6034003600110003d203049141c01f030034142090104064003070280640e24114500340900d40a101c11401420010301c0509094144a4150040c0d0440c955114000503c04586545220035010710b038410001c039a0384201c28501a0b8bc02c050700d0b8199880034415801030501440401d038003030788200c2040d8065071901003039120a9542d07208155035480e2408142c482c00804800c01d9400744805004206102e001e620803519441080120348050781c0c002c1c4840c1b40194142145e06040313a00581c003180341d04160a5100c000e49514401a03015501e041811008004d40d03078061070b02c3e00c40c007000042490024a280c4c0c00510020f0b5a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 538201996 1250 538200746 538200781
    0x5030114040807031103070302060612030c060720010e06090d0804030f0e0a0e161d010819060e01180c03021206120c0301090803040209010b0721021207080c0607030203 74
    0x40e140b0010711003051500801145c0d0510300d026049030303520032130760900a449007c1540d00340c0c4100920200784052100010560740f51915980240c403141e143d90f40b007500e88003001c0c851402c0c01e008a0700d040441034020701c00c50100162280147c036046c6840b80055007000907076460201448000c20911000c00e6000707a1320408084142407600250b06840002121000261301801a007000380c000c10035800140078840c0d0075440d2545903410211015098002c880050101040c002540640000c0c180c00c1c42c050013407042e00360b15070000b0b54941c9070540030340894004d81004c84412905030f00f828508507140b09800e10694146421400c1000c21448825844405040d040c420454003004600380d2000740319490401400030000c000301d40c1e4a02c0e282402390001c840980c07091018400000f005050f0310304480712203a1000400d03800d032107161006000300c0c211124100442c41040600c00c03c04e11407500410000380160002c039281c194006501d440c2520052068041500500921040381d068020050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 538203246 1250 538201996 538202003
    0xf0b090a050f1305100e1e07050d061e3306090501110f030d091a06031921080411040c200a06020409020c0601080313140d02041b090503011404 63
    0x105200710324242246405140c88075001d0003842d103071408503507880c00a000c0a02d0487c240d1401800c140d480c0410f515445644039054000c95400007440c00959541e21244640204a5580e60b420709100d01c000c080301c04089420148640443d0034413208168980040504034628104e106840c3c01c1c01e4006015100d240324040c1401000400398107403030001e0252060802c9a2002c5075180e102c140c0c2c13410060f1070b4040e01900d0b020510902c0e0201f074404901c0c41031103038201030020400b4004050310704201d59641c07441a80e010140f2001d081120041038040e90440f0407942d103c0c40c903824a070800000080f00311000030300c101d00d0007028071005034100c00b1b80610701c080e00c00c2d0f100703000e5010020141802d401200003013180d8800100883e03c440c181e03015104140b20709007192144c0c5c0e00c40b00001d60b0383c8079504400b010308402d840200555103800e820010918005000108014103230390101d0187d407010208200c1c0101e400407201c0d2079551010441c1e0040200320000e101446601202d1401c030306025001a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 538204496 1250 538203246 538203271
    0x80c1f15050d02061c06061403010f1e0f0806071101050f0a05071206090207050c01090605070204050402061911060c130e07030b030f01020c0c0d1a18010f0b090a050f 73
    0x10b00c10744d5649025101509011520100c080443c4541140203084e07034080e500215807001e0300c1c031200036051000c0d681600c1c1d100003680081c0e070400e9180d60f00d00000c12650b40c240f5808071400310342150501c10400c001d02e0a84020f20701070400d001c3c040e05c0c2031541450304280c0e0f071400e41000b0613140104107003900181c002c075000400ea280d00104882c030b151080788408900d402d0600001e00d802d941c0d4014030090307014070180c4085071902c4004490b0700a5500c60300c000250300b48906130240c03030250b202c5138006100400e01071410340b400d18513045c2c1084480c201c1011a409000c41240f0007410f210807684000449245071030140d46601002c8440b2003401a569502e00c11400500c1d6140298000d40c54144000c1c1194007030180030109502035804002524541c7c00354101600351410100d50607900c10398842241d4098074203550401045003002020680c813102d99003554006204284295144030031700950100d14094600103000c0c4411001d0542641d440c0340030701300440c1700d9013494899001100c034800d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 538205746 1250 538204496 538204519
    0x414160f02010b040c12060603020909010b0f2a1c02031b070e180c03030a1209240c140a0f0c08070507062012090f0a03080c1f1505 58
    0x100e0043c01c04503421600302d407424201d208071a4010380304091200e50310704103210240e10307400c0807400e900450720201d4201500300e0040c400e120410300640022100c8005050500c2d050300c002200080064011510301040c420141c0d01e04c7c4014807580104480d039a809010003029000700035541e00c00c407884405c6021214640742c4d42100c0034401400144101c01c0c444d100350401e0b03940500481a04401080700d440740c11040003a50801005661884215031038440481000309240c101a050745001141c10440c101c482c0070940d61082c02c040300b000b01010001a041c90400343c041d21418200c0050b18031000144000c004c0d441e07000d0424078a0307410503e041e98604001c0d00d0600a103004030300005229010b8484045242944075940d4250b211101020030300010701c2c00001c54507140c0a0726507420f4031400f00600c80139030901c6110101950000f0b040411455625154440a90000409d42c400d9030012001e05100300401151040c03142000f840030450f5612001415200d0141407050368000d0509400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 538206996 1250 538205746 538205777
    0x9040b03070801020a05034312050c0a02010c030902060403080c1e0d1d0a0306020306030304170102131d0a090f060f271515030c060905041416 63
    0x20107000b0001d54562003c900b010b0304c1c42d0011107407142d55064480c41e40c41000484050f40d1180b0a40c0000c5109040f000307880c2c600030705d001c200b0100a10289245403400900c05119551082c405140c000f5101c5003100002400d45411180b00c8003003506081340355016a5400084400b240d03400402c0d169144001403000e030405c42007094200c3c0350f40e09110341c0b28420901040945003104d1507540d00d09072414812803031081010040c0440e4010041d86028030004825900030f503004400101120b0810b5580e80101040020808011001e80d4000c40d62841c03981e041c0c0d05513406490200c0d01001c00c25a00c46c4405c4041e01c0c01840c6200d21510350907a2800e101880317501c00c40503600038100f480040d0440310000090400f4140440d00c012550f400f40c0ca0200c90200c007488069400300c1d8061050209500c0c90001c1c00005488da030b10032040c0e0100000003042d41c3c0c4904002c1000352206803800f4504030411040318400c6c402440c15400d10340401100f03143e0301c00e01000c114440d0803c6d0490000186 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 538208246 1250 538206996 538207003
    0xa1509090501140f0406060e090d200d02010e0f01050115140f030103051b0103050c04030f14060106090801050a0b0a050121061403160503060403080406111603030e07030809040b03 79
    0x142c2490780c030b801010910900d285a13505039885540900414015241c1d0754101064408044500d0742041d044540391013512031244e16040e0740d8201196610750102440c40d000c0b414200c01c0f001a0015130354408520101b204280850f08801c4144402000650b15080e1044400d1906008075410000a0705410050f14a24001c0d5444090403601442d100e60316803070141d56a4080c0c001c00101c0c2480400040790562203401101e100710200c040c0301e81050b1035a5504103040031825005c0302d08540340c40b001c4803901010000e5a00811041e0f0354003074614a0729090508660f809041c1c00c1368281000e04407510307038a071040802c08445080c44c0030340822220306d580c040342d440c0040c48541c0355800e1030400100f011407041400e6009000700d003543c00e00c030f05102c280c44d410b0480d40726a03074041d0400b02c00180824001c0e15810740c024010100401d1502702100b010300161300c049504007028020607444010300d6410300c901a19562075400400304542141c55241650082e2151584560344a050702c07516030b1012f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 538209496 1250 538208246 538208261
    0x2060f0c030a0306230604150c170a09080d0512070507120e0f010801031505041502070309030308090a050c1509060d021b16090b06090910030b0a1509090501 69
    0x1502c0d1111028140100548100d01c64400c40c2d01000d01000c08400448645c5010604001c0a4510300b902c1c1c55407010b40d400020000314140f12412008801040700010401c0850f00c0310408541e0712a12444081e24203400c40d04511000d82c012030302034504c40c0e04001182d00e2030009003001c0745265190761040b2214811780600511400311040c03040d00030b5030017805101d02d41100b1a02e45003443c2c000030044400e29000d100c05480180c049407101820001c640c00300350400c0c041d210304038031030005210900a91384140421000290525010006d01d43c1c0800c11580100a000281a4504443d00c4d0165100d01c1b99a10030b1141c1c80100311880d00f00ca11504540505074050413150703c80080030b041c50001e40000703044074000310011800d0004214003050a400300b002906118040c241001c50361402880075004064003c101080401040d950748103100340303e04c0841040c0d00d0860f0a518000b03c507100040e088400c9241006544c03c12004406c00c1c817001d075440d1020000300c5590f542001405000c05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 538210746 1250 538209496 538209517
    0x8070c02040e0a060c021b0109030206030603120417010c030504053406050316031b0c06090b0a0c030c030b011d03030417030c1603020108040821010801022d0702060f 73
    0x81000c01c1d020813010b60026400848545c094464040d088100041c11030000b801050004043c00e0341800103141c03100203943c10640280403500440c2c42101e00e035041c0c0d03001d40c20034694121002c02c800d10901c003d0142240042451030b050000d81050783d00c01c0e546149110118105c5a440400d501c2c040d0710754101920f003403c0054800c0042c03070380d03054007903c5a4410740c0c0301e000c110440030249150784d020703001c1e4070103060300640040c0e441c4540d640700315806014000201c895a8641801c031000c00d5400052030f000301443d1000040d201d03481c0e940a0126001c2c10100000d15061003207695081ea0842c0240c802019403801d000b44d0502070030700013825807107240c00071482c0a003210686000c60308000050860600c001c1c1c100d926460346450080c042c24450310000380043c44040024000440e41030107000144010b00034141022040071812041c042c00b41c001580c144c0d0b000c6241903001c0d484801c080700f0050080510601c1e030b0550802c080b4103120790178020303000d144002681c101441c2070b80200d82482c400c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 538211996 1250 538210746 538210753
    0x80706020703361a122e05030d081b0c01110a030b120106081b040b0a030b0a1a09010519030b0c040f0803032a0f0d0e010c02060708070c02040e 63
    0x103075803035000a541d404210391800074210103001c103046101c0c0c005880b14403006581c0f40c4c00c0041c0164411804040100301808500c2907a0050001600307161101d200e00c0346c204101002c50781400141441c10310000060b07400c00060409000208034804004000100342000640e40c80751821003050240c086403101d280d03550030004a8401c081d501d9030100c0c0307401d40c00b01c0d02c200c01110040101800d0312154091a0078030707000102210201c0145a14604495a01800c0410070400c4200011244101540b003902d188142100b007100c11041881100b42061031240210194081c036404039604400500541d40610030188080c0c1c1c101e174600e20f2200c001c0d5400840e0f011207142c45c0100007000e402c688540e40101102c204041180d44001c000e8a1042d12000c00042000c0307803142c4c3c60305007c8000000581f00c50010022000d40d01400380040981401064020841d00319940e003040c21141d6482003082190001d009100c45181e1100115400c2100c518084003084d02038000140103203016140e0000b10b10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 538213246 1250 538211996 538212047
    0x70c020603090601030b06120705270a240b0f0a140c1f050106020a170c0708070317070b0708220b04020907080601020a0b04060605060708040e010b07080706020703 72
    0x40001403c0d41641e12400d05c00640c3e031161414082c0030140b03a005c01c3d150303402c07401042c450780c1442c40d401409510364410815a1108d2500241c04484c0185d608200c00e82e03c07125118103018a805480107040304021554010794a44012403000340140d01c0300b5501d80c107000850400243c4190190781c40242c0c940c0e641f6179500c403043d01143e038803000d400d0a01369606142010b42d104200b90310070b131b604131612900030306803070030850b0707500001c0002003030220310301a00a0040d01c007511000c07c42c640c05050100010031000b03045007032984002541d041c0001601030204403210000750030390080c80e0004003e042800d05a00ca04078200c03801c01c54280d06000e215103002680c8140701441106500442c004c1e5403590054032400001c41c0c60060440310940503901032840c0700300003407520b01c081d54001d000d800d001600e113482c0c80000c0e500c1c6d405040107441000d40030030280007540ca070104190041824210703161521415503a13408041c01903100240100e030740801c1039420705028404600d10801820344011056 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 538214496 1250 538213246 538213261
    0xf03080c01151517011d04030c0c0f0509090604030f050f040518040201271203020f390d023303091e0309042003010b040e07020109120305070c020603 66
    0xc0c0450310f44900003070701d01e0096540d42255069228181c4036444020602d51040342d681200c8000d014008404111001d203607040810040d01c0540c0180401c2140c001c20725181c01e00b007000c0700d03d0180c00c110446c0c0000b428403001a0f00903180c80c1040f01c150400903100c00070002c0c01c1030340c4c4c001e80c1d1140d9045440c070000b400c180902c074007260b407081d8400d89900d046a58011020891040c44c4040419000d22141090000030101901151101d100303104450070460001450b50800003035444001d005040c900700d9101c00c0400900f140c841901c00311003580a40580400601c90f0504c04070080c1c051240140d5030200075080701081400e0316002c40f01c0754040b03030b0700b0000710100358003c59409119002d03c841001c074501940801e0b407921046840254204032481c0200801810a01d00115180f80c04a034a10340600d140307001741d03000b0a441e00e00c00303803900c3c03610b1018503070b8602c01044942164500200761001981c201140c9081c41418034001440783e0710301c0d400b03070381145d80728074003a500c0407000c4104140f4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 538215746 1250 538214496 538214519
    0x2040e0f0c0f0f0d030203070f050d1407050622080d02030f090d020a02191d01140a0f1403010915020706151206090809130605040b01140d090614040b061005040f03080c0115 76
    0x200bc81658072102d4a85000c40d071840b00380205e0302c00030b025821080101d58080c11800c5c000111030040d45425110344002c0e0307120962a403020303240115154010082100c800b591070100340d0b02c10340480191130455801000207440e5480d40000030300c1901c3c0814101340305d1813a1014100980f46802041c00424003d0b0050410300000740305900c03070b0030141d60712120720781041200d120403210603203220a41c0f18103000c01c140c030000c2d20480d101e03095981d0382042c00c0442c08104185401e600c0e41740700140d45813502e04041d4250b51610b1f80415003031980c04410414410740150244a03181c01080000d45401245810b8009110b81001076038800340c082000c0030151000d522010403100c04880421407403071904015600001d110a0540b8844030521170030000e040e950b0003c1e441542308860010701001c21425000c203a04041c0c8003507642000f5041040483d041c801c40590310140d60741032041c01d103464908203442c4403001d40002002d0440c081303840802c012094200f0b0030b0641508c4840c40703841d070301d40703031040385 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 538216996 1250 538215746 538215763
    0x20712020606240a0c06140c0310090204060807051b0601170708070b03130f02040603060506130b0f13110403030c030f08042d02040e0f0c0f0f0d030203070f05 70
    0xc5a95103c0c9195203032503034405050400f0200e0301c520750074501124001c2d201c8900a50b0203440890f100c0e4007141c1003250048a03e440380c01000181921790600721102005011207800400d1a82e10400040c03082d550043c1e0310300d41c000960720f800c0703030342d042c03040b1034600ca940c1784e02954520342c4128800800c1c0e2024501603005110340d51401c580d00e10b40d45180c034685d40c180c14031031040c01c1081000400c07508a02c000c8000c120f1402004024080c00340c0740e02150842d001ca51080c0d40403582c1e8000e000c41d501c0c003a0740020040301c0841045c00b0b48001c060009940940803040e0b50301c1740386149007210326040540c102c409848028689075448581e00d05014100b40e002580840004c3c49e20321020301010f01803d42e05025070307080307480200700701007118000541400b055013261020040340c0c0d8440041c1e546015212910040b480503100c002503a5007210300d0604403001503441a60079031001c0c034807a201d0001c45081102c084904100640349410f0513070a521400c100a841016403810718405d00c18002512036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 538218246 1250 538216996 538216999
    0x9050a030305180a020a1415031003120c1a13060204080c011106070807031109030a0311071d0c0708091c1719081f0f08010b04020c030f0d020712020606 67
    0x2020403e038102e08a0b2290400702c402503201c001034509100890705640e00c441d00342d401520340d80c0340d140307922800c04e41900200c3c1c42c60707007000304410103000700300c80c0544805041c9028200700419110030360750204007143d94400d80c0c2d81d503400b1600080040e070071006401740c9150088011552030303403185021503c0710000000c0030b01003030315035200c04943e6000083c8544a400a642c8800ba01d45030f107001200640703c2400e4203800c032401807041e181310350307018849079079004e22940340c04075010180c101280c00d01e8501c0c0c0c0720350f41c8025490301101d2050384241031968088113100d40a42e450f0406c1c9030003521030064116481d0804101c0c600740300f60301e540c1800740d05281c1c0160a507210b5000412240d001a10a040220b0100c110f007802482040c3d0058444540108940c0c1c100d407903d1100d2254403101c900103500c9125900380c448002c000302c00081c81142c00e829002d4400b94a0305072107201c01e61740c91140c03007a5242e2403640003581c205424695810349046a0340040d01044910b21000000d554603800c0d00d105 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 538219496 1250 538218246 538218271
    0x2607110102221a0306060d0c030902040501080607030c0201020f0406030b0d060c0801081b100f0306080f0a15020f04030803040c09021c1b0801090c1808061b07050a0807020409050a030305 82
    0x41014603203d4080d0303031050754014000d9140400c05c04444000e02100d445807414152280403070300060f5942e0041601800728480101820b2078400c0c40101a212048088803e5900c1004090b01600e005000c86040e00c1c41d60070042013940c2004003088007082003820191a55182c90207854500d81d000792003604079012942240d8918507041040a03c941b8042d130800e074809a0b2008000d1558000c40340790141101c5400e00256442da100381041c01e0240c041e032043c0090700048002d00801c9104d8065201e48d400c4d001d421802c140d40d88118010b02d102da400040c1a5600100014040bc038210b40404040d1801e40d206544900c81c2e503900811070b19035142e804160301d081c0103100d143d503200c0000d550342c2d4401d16a02d14455902c0c02d03400030300410030503994100704851005c014900c4001d8508020040c400c0800a207914602100d817250705080f0700040c8003215208102000c0482c03030000d41c00541c5c03604000c00c1c0d41d40300d00b40c1c80010000c108500c0001c100b170080f041060207040d050390210b0301c15003440d41c44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 538220746 1250 538219496 538219529
    0x30c290d02190f02060402130905070b0912010504050607210903031b03020a0806150405030604050f06010b030112110f040c0c0203010c0309020d060b0d020d05060403260711010222 79
    0x351080b0310281c04601c0140e021750009005881c100f048490905079106000640003040d03225181000d225402c840d044010000c1d0902c8141458402d000038444041c1c000c205c2801c0660703e2a443d00e04c040d001008219128003840d030320203500d010204564454020812800e0741a02d00500640b1030b00300d2103c83c040e1025076a030500c0e402402140c1d42d130340003981c0315003003a070b01c9400b007204100b0b0014200895400c140300108140d2010003005000f07a0003103004000300c5083e20181c40c601541600581e46682c010302c01041419100352031041d40a034443c5040d009000c038480030400c502d130001416030707000f81400c90800c251a0400d00c420f2406009900074400e440281805506071040f501b4002c0d0059004400c981c042400d96110b02100040245040c100903000c0d0009042c4030125081964560011000d010030117030070800c80102c20341c00024500040c04003005500040c0c000424602c18445d05410f240046042035040b00c01c0030540e03030120b568a003421050b5103011849401a8071450055401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 538221996 1250 538220746 538220797
    0x1b030c12031b030c0e13020d050912072006030a0509121824030f07091a040302120a051618020403050d05130e0a090b0709030c290d02 59
    0x3500820300044800040485100070128014803009000c1c0c41004445c220104680c2e03a041e49150318100c0100001d606c40704545003040445601800085041d0710101074400304441440588503001d401052252010101a42100d08420388441e40c642c420310000401100140590145006070304010840d9001801501a944144541ca014000644042d0381400f5549451241042200381c0c004400300c0c454403218040405400c20707a04c1c19101801c5000304003800368821034080042012404181845d00c4141a4144600c02c03400003900607440d601030b41013115010001d000006a020b411070b14203801034a440810324140b405000c0159034440b55000110740c1c41d00a075010340380c02c2030240c040300005540c10388280e0b1004030340d5180c20044003000a95407031031032200c5101c0c040d0103802203a004001e142c400480c0100a107a10180080c0980c04d00100f0307426034144059800c404282420070755890b04003000040e081c0000b180c00c40c000508000843d06a40140a19100c01d0240503403001002d007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 538223246 1250 538221996 538222001
    0x1819030503042c0106050f0a0201020405060a1116030b15010c02090a0501090b19090e0f1903030f09230a1b080c061c090809030102070515091501090504031b030c1203 73
    0x101d820005141444440c408047d4600100141d072884d0000503d4942d803400840c2c1560010b4221002180c1c1040844110b10400d01604054031a005060700c1000e0441e501ca040c5070a010b4a500490100b02c3d10100040e4003442101c1e81c003540003000c4030028540b84207414040c0809004189919080c400043c4030740c00e002010f26090b040d0302041c600d0740e038100380200c4000d103050031061003180700d000300c10000c02c81c2c240b103000594001a05003495280c2d2504010b802d1380c00f0b840090b030781145482590400305288103024010106548081a800310400c030160389001e41c80387c00500b0b12568103044550f1040521900c074103c4034000250b8a860f04014100001c0b4000d87d42c0203101140500a80004400d29520001a01348200042c4e810902c58001003402c98200c0e00045600b5401040000c0031100440318180d40088010018650121903400041130001c1c1807103049143c0b5114800b2904240c020341c50a40c0e641041d8a80e0f00350004607040041090b81c18800c2a2464100300f00030500040c441d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 538224496 1250 538223246 538223249
    0x201060806060d0512070305040e070c050c0103052d041203090b040308041b180518030f03060f04110a080a0614010e0d12030f060503031819030503042c01 68
    0x108080c05907642c0350010311001080840048441d8082c0c252a000f10044010261008078020354845071250b0070941500401107010380940e003444240e000b0000040c20001d100484c468080c80c001c0b0b49511083c440d0040300d58600c02c107424407016007110340c80d0403400c14032062145020f001e21200210444900b5811108076a0025015000e80d100160219001d0680c1d540c1062180040080c989140e0f031412007003032450340168549281142d5041e0451041d40602e9400034420450300b1083c81e0525241642c9201d0803120461146020000a000396136030200c4003030304c25019005100c00d808a44400390580d00c0101580c0210f07000340c011031441c2029100d0038040d0740c00a40c1e4040511307880700041d1000c03803c1116659015210880d02c600040c40c0c41022a2071f4041e5481c08101d07000100f0342e94068070790f940c0089000b6442804030f102c0d00007240500305800f00c0c060b2050090303400d10380b0303400c961104e2a8002402d1840700090015000031414112860b0320700304040690314a03040d100700740030302000703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 538225746 1250 538224496 538224509
    0x2012003010b041e2301020c01080903180607020402160b0a050114010806060c1b150711041107060603110a120b0604110c0f0706080f011a07020607051605030d020106 73
    0x60100340b004641d9410301000800c406000f21300102c5e642c418036040080980c0d41c200c071581c010380d808086941c04000b01d500140702424070384c0341482c012280c2a0340c1d0051118030018540502a4011540c030744100f200d81040d0054401d5503141c12040c40403558110b001d01c110350782c040140c005240c045043c81020f0603070f003043d41280c5101e00e101c001100c4030140602040e501520800c110302c0064800c0014003841ca04640700600c516542404009441d40c0d190244051500c081000364001030541e42c1c2c441005100f2540094084c0b100ba150190500550000401c0b05281100110900c1103102d46200035010440b924100345880702c035a166200d06410f0020702c001c0c80e900200e00c40e45031503041381481c0546802058200b1100c401c10a1502d9100c4001400c241c0103100b051000a601c000d015038001c03d43d01d0426440d52402c190101d0105e0844c003804071582010030036608555449003120740300341d0014110398503403000072030322054241540700b91440f074820380b40c2e004049030060040c8821904c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 538226996 1250 538225746 538225769
    0x180c0a08012909040212040b18150a1a0d0506010503100c05030604050c1e03010504050a0b0120010f0204061101060801060503071a1e0d050a05010f120507150201200301 74
    0x1e1680510324541007211090b134044e8081c444d0340351446851045902c2240502200305a5003440020054601041c42810400d40c10600780c524418000110294100c5440c09000a001c0520f41e09101e403120481d04080e071044030402d072401408000103900341a9901102550380c54403140c2c84805c122607128410101040081c4005486442c2584c001c2c1d0744218400100380c0380400650046100314080c908511804a012006010a09141c81142d52295042c2010030400110300000382c0860144e000346c030000102000d8001c00300d1000c0d040303075039054140c08055488540714030300a044014844404c0d6040d40c81c00c0d00000310003c050041408603680034000e00701a60401c54601210415803245604101e404c000340c0103030500e65034a201100320a05860751719610a4007401d4295035024000e031640504100c01400082010813140c002c89070202800310118950b131401508040595200c8411000320340c421903581501908140d2800301d04421510031640541a940305901003030050384a102c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 538228246 1250 538226996 538227059
    0x3050112121d13020a03050c04050303070212030904060f06230d0b4510051309140709060b0c1020040603061706090a020f180c0a0801 59
    0x240100300d007400c115510244200c010b46401c002c100c0c0d0b400d010043c09807480e800901c841c1c5213641441180d40050090120524040c40d001c00265030380a02480a1b10a081801c3e00c420f079a0406c004403045800090000d000150f505d0303004140c590214030895021a80c200384125400001032000c03126580100c500500305140d0701020300080020000240d004001308490144c00c1000c059a0398804004000080c54450041440d0400752498140604110451001c1c00a544550b00424040d24021f454040140100b40e0341c0002400c100710000d821404024540c81c6c610901040c90016614420303002d2004070307030351002410f0702d110351400b5081942000c003810707541c11031580215085c900a0b9115103da03000c003044141d081d40c031603030040c4042a0b40f0303001040041c001c540a5040c040002002d003003140f5107c607426854185d0403900900c00c07102e000c0b082c200c958a000001128030754168103640d00d0b103015080e9003c542c1c02018001d02007001c440c00003d400300346001000c40805c540d40d0924108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 538229496 1250 538228246 538228283
    0x9050105070f171215011e0503011806050904060b040b010e010212070606031a0603010f0b060a110102190e0316080a0b04050312040602070b0606131809060207050d03050112 76
    0x6000d0540d08210408104000326201c40d0992402e40116000040784480030844800548042c411f032008117000d6004500081d20940c001c42642d04503500314006d402c0021000041038020300b00e40e00159840350010301408141324203030313102c0180c0c030300107030390801140003002c0c015103110821085a44c0182d00003405003080040c900b016040651003072601080d100e490399145690001d401000c82041040f1130100030b1645800d00032180c540840c14402c000c1b211420020410703034402c1d0071502060007001c01030384021110950482d05804c800204000000780302040060280b183c40f43c40611a10035503014108100507101e9000485061400400034080b6550301c841120700b008006841d1070005201403040d0366010311130b6910551040100580d1000249000030b086a0080d00c80c0f805200c0c02e102d103006030148070400d5015aa00280941f4400800d00300c80f10240c8000280200924004103202040100026850040e56007584090049070703202d1192a41000f03001001803c4a0f07428044403501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 538230746 1250 538229496 538229513
    0x301050a050105180d030f0e01050f09060331020a0510022104030f03200615041a04141902070201020a1211250e09030a030c09090f0501030309050105070f 68
    0x41281c40503101401240500004004416a51096011400301d1900c0300582350300c0b000008180000b405e149042c035064105080740f82c0a0000102d0207040700001280d01c00300030a8a0f0a50040007022011004512540b414294840403c0c100d00401c2e06a201141c80e00e0011800f2401c0c0d1030030f5004080c85400d2070030040141000300c0c401e01d4072000400000c0007041015a6440c031180c001c2d114401c1c9007100112404108107599010b21071600001c00f07016241c03000c4158800f52030402c07140800c4013402204802c852661102000c0e40c03040c40c1404550080110b03468a501c0381c221aa078260b01182d1103403065081e88079415000f80107030000c451150018009020a5802070424030340003000a0500c5c80b00c92a251500d10805080d600410301001c010324000c0860019007140c020301c1c031203820a42e0310b45603a4041d41c0750320780a040d240c02034190010301c204880d5004180c1c490050007515155400c00004040030f00099000940102c0c021409501480407640819406134070020a403a090325034000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 538231996 1250 538230746 538230757
    0x307050c01020f04170114041101021501180b01021c050304110603041a01050109030f02040c02160f030b10030b060904020102211207090506120702030d1a01090b0301050a050105 78
    0x244502032000121400091001c0c060607030035040202d41d5242881c00f4000783c003400804514a6a040c03001464400b24110400b40d0071903849900c00e0904402040144c0c20510f012281e0300088480c5400000d0155080381c5104001001d01c0c001c008e070045d0031300120303103078601503036550154400d80d14503900841c4164011544a0702070082440c0c0b401103000041c07a15402a102a200c1801000700c80c940e001303c410145004003424200302000302d184d0303910109038204c1d40c00c000c5e200302d07a2050720035402c074020b10640305450a101c10003130742641c50709040814402903000c00d031154108000040d107012000f00c6004180d940041d010415a80c0d6902044420400103101300d046018140c180c0c260040d088d011b00c102014850b4005849024043c2d612b40b4000340240b0b0b010400c81081d100300065118801161640e5100e0840304040c1d0761421026882c5102c1d000c0344905651802040d000ca00601c0c2803020550031099a501000350741d40c55568045010a01445603c1071018004004541c0a50000c1c80b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 538233246 1250 538231996 538232011
    0x515070c020402030408090f0a051003050a0e06040f12050a0903080c01090210091805060907050c010e030a03020a030f05062220210f01031709030708070906050f0904020603 76
    0x880641681c04101070340c1040c0c40450300981c01080ca4601c91500c10b05182c203440040d038180d141d940c44c0000040d048905122100145a640c1c0041207440700c2c0c0382c0181c00d50344603002c1107920780d04140c5003400224000407402d03a45a011040c450384000d2240781110b035200e0460340c0e0b4000c5141551684030741c0f41c1c04020804c2c0c030356613208103400c0183c4940044100030b841944035040b000d850069201020f229000e00700d0040740c071704020044c1d250350300b14104c1d40101a62030003e45960498550300c0c0144210106050f0b1803001003040c42c84254150028520081c07a0b641c18130604101c031020724165201076409542c010f88004005d041044003003507113070440c20300e0310010400d03184440c0641d40c840d03501001c04050460019880810340c203c0718014070210703042e600b04031151400c030103950070400c01800001c02105140e0b80c0034000c15885130594a41c00303002019180d405071303288646a0f032000644181c1f0401030614400040030b2410400d8800c1c0c401e000303014031a0956440e03080000c1580003d1012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 538234496 1250 538233246 538233257
    0xa06110312010b0408010609050103081218030d05100603230c0906160201020d0207031509030905040510050102071d0a0b01032904060506030c0d0f020d0e151003051507 74
    0x700c4000301c403111424028002c400702981c1d180c0c01e01403400c1c2034603032540007001e6081c200001000022100400c54440c17060081d040c081d036448030b40d444441d505401c56000030b07900c0b0124051a04000550006002d50920460a2645a030f0343d1000d400707644400400c9180c42d40029156001d541e0301c291100c1e0301900c418000c921b01040e01f4009a5a074001c0030070000c400c0c0341c500d00541103580400a5980b0880140001e024844c916681c403c114411039150314803050f1240704010415006191100c090715004000b800145850a00c2d2a1328403000c0c800c440c01845911000641070080305811418a00c40500e0641c1540c0c8201c80b80c00a411204111b9040595070070b03105151480440429085210106e00c00030201014010041a01e07455000948125000c0003400390200451080304d1103004485400300c0d8203441070207108005d01404043e0080c090909003001c81194000c180c04142602c5010481c15545401814540308845c0d800000d21962151094010380c11400707540780c1d44000c1c0c03407411 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 538235746 1250 538234496 538234507
    0x804060b0a120c0902032503020f04090905010f181b0e0702100f05060105071509080d0204030c210b190606030b2d06091804080403150603020a061103 66
    0xc1160400e050b030114070040445103100c0d007040381000d400002001480402d50a50a000c03080c5070b2903540050001242103860318000070346500980580e07034a0b45030007201ca61038507a1800302e4000303410106004c03181e5501c4e0131a00b994401030351049046a00c05501d44181500302e669a034168440210002a502c4601c80b90004900da240d48805214824035070180884c070f00450090015510700c82041c3c00c100d400e100400059076032000a980e5041e8100031142c03071810314040c06100800c0040409030100a000401840b419050b40041003200c2c4200c0c40e82c01019aa0f9134184148240800c01c0a60f2040b0144400040f81c06001e0740364111003001c10b03507800f144c0c1102c05001212050703844000070036107950034000ca42ca0843c209110b100300d80c50501d1456032404402002d640b00d02c903c0d941c842c40010444040300e840d0f04c5100780030280e0700b0310426070031f00b080d00701203103a5000740c88100c0c1c0e1700d4502c19034242090224040e0004803a806010b8000003420440291400c3c001500c015035a484140300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 538236996 1250 538235746 538235749
    0x406031104210308070804030e0d03030b032a0103050103111210020c0a0209010605030601020d030c020c1206061c08030a110913090302060a020f04090b03120c0321010509070804060b 80
    0x2e0b004801e060403041080589140b802510001c0000c02c0300080c48007010030040480c2d0040c0c0c000d143e68208039510b408020035494158010808041c0c06500f510071004452140d2401010304030014039600d0140c42000407010044082d90030074000203140e03900e44404403001e0b04061039a50300450220007916031482d0048020012600984041d01c280e6000038004015420220006800741810b468902c3ca54500040080c0d65084c001c1083c00405950325013460f02d1394400e000b1140700100080140b8610720070300845554501c41500d0040c417038600b01c1051840c0802e2030031941d003010b5002d409181940d98111095000f00f400990060310701104110100a030b641d000c07200c41c0000580d82d4001030100c1103040003413401c04001c0041a0040c81042808c10024a290607142200c40c1500701084c4c030690140861b040105105601d031407040d010500c04401c120200c0648250200c80c00040c544040c000900700701800c0c28402c90307800115030004200c0540c0b051241b158003a00640010810000160 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 538238246 1250 538236996 538237019
    0x106141504031205090a15080f090708030d020d0f2003061908060405010b0306060d0f14060405031b0c090a23090d020f430e01091d030406031104 64
    0x40c140e00195000482098078031b400d41c0440d000d03080d891644541c240040c003001e44030020103271841c0c0411071010009090241c0800c05c44010702942400e0b01e480300008d04004002c0e411004000c401d4504001e030902d0b0302d1a0b54030035034044012009404d1008145000201d41d13030b03400a00342da90850100100e9009241224402200500050b401031130b85240a00b001360844a049400310f01c290001ea080c8031903070381c1d406000c0300041c0d00040c900b00103803904d14001c3c1c4c0d000b2220210309240d002d10010002032190200240900c404078240c60280c20900c80320068481c0e52074145980d00503112404120344241c0c990028284c20b00514036007120603084002d000580d035048404c00a1075004d0051070490395410f100031481d80c2c00b001c0043c11002c0d40810005120255242c1d200086000e00400705201e5240b039100307200060444520141d15612800100503542e02400fa002d1b5660800e000c2d44109040010443c2d80c40103080044c0d820941000001c4000c0c101080c4000b4440c42e0900c408181d10303d900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 538239496 1250 538238246 538238273
    0x703030c0813170d0903150e1c03060618060815010c0f060203010f12051002031e010e0103210206010513061e05150a0c061512140f010614150403 64
    0x11801c3c41d80e1003030407403615144200311010b040091400301000050550f0001d044054420800442d0a080c2851001e103071140100c20000c11203400701d2800c4240350154400030580d04030350396440308440d54070007000e511020340c410700b000102e1000c0024100e2512601c58104014140751140242141d504c440840c540080c20a0302d00d5503002004108850280d41985e0060080c0c800e514891002900c0d4181c40384454120954016000400104110106d407994111801000300e610082e584415068900d44000d0104032903001c60191175004070701c480c02d5136015898981d4000c1042d13030700306018030000c0002460b851841c16144ca8020458031941880500d140101d200300b980d99a1505040210840102085007001c94040000401c61380e40301010031825500840080b6146c0c2c5140000649201164442d584a24580e00d40c1010030201c500c2e000e2107506101e003203810004c10000343c1800c0784e20b18071481c802010910711260007402c3c40c9038140326481e1204010390820740c0c3c071b441700c81c10490038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 538240746 1250 538239496 538239509
    0x90904020a0b0304061a460803041802070203030a0c021201091b140901030b0705070c0810050903090d1704080d0c051902010e0409020a0b27040c020703030c0813 71
    0x2105041d407043c40300c2422013107070700408446200311048020000311f070007003625840c100d40c040b000200d0503212900400b84001d000300c0c20307455466603580740043c03a22070b00940a02c0b11803405641c52071000f2105070081c1c514860300140518580200c0700001e075045051103004903044889203001958080080c8184403129000301800e5001000c0300042107400001600300301322607000d04810000c540c64240c05941902d0388200c100e049034071405000da8280c020b04c5001080da80000f03001082c10300020501441807030324460300788643d845a08075181c40307004408485402940150a62010449000c621110001c050103820725181c1c03940714060400008220301d43c00304011a210390100302c030402c07815000391040c1404440b0018554002003240c2c1c400ca0b50b1074407864641014070150754801e480c59000301440d41c00300365190300ba00e02c0d155606e0003d80a40c030090700d0f51001c10426042501904e40a201540c1c00781c1041ea00b91f03602a50540300c190343c251800c0b0340a101000400f82c7c0105803d014110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 538241996 1250 538240746 538240751
    0x21e0a121b08251116031a06042022060e0a0801020304031715090403031d1222172a100f030b04051e0f0705090904020a0b030406 57
    0x84404041e0420001070484140f40343c44005401c01d2101c15410481d07820014079195082c41c040d040c0407441c0c140c011400c000c2401c062900001044183ca8550881041e00c14a0300d109aa840341040110b840340412085a51203034440c0074400c1074884010500004660b502e01e1174507000e2100d071050181142c110401040120708594124075108003120700400c8000025441c5140641d0000c01143d14220245280441240401c80d041d04040d45a0000000580700c030f000c5107058100280505030b8504220103d6100c0c0000301c1100b00003181c0e107094010542c280524000d241d140c0390180070351085801010741241a0046400384400080451025051009140422800c5250381d5030000c2c9100c000c065013552040e4800c683c03581c0f0300091410196085c6840410f16041c006d801400d0708c540400e034440e10b840c0c200f080b44c104100300e4070780c4030001caa05a011660307408124002c0910a0720300b0310101d24140b046601902d40b15075815803192000e040b081441c0d0b0341d41e0381c0c03c0d00d5800541d81200d65a4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 538243246 1250 538241996 538242041
    0x70e041202060c0a0203090f060906071a07020a211110050718060c150e0d030516081b0903030403060903110c0301150302040e0102040f0f0810021e0a12 67
    0x81d8100709141d0400403840ca114070f80031400c44069038900c00e94102034041c00c25a081701703016903640404d41e52400c8014002c1d682d40c405c5882c2984040140100c2d15060f9031580000c00c244a10009009014580c842d220b00c040d0f0010402c0c2032801c00102c0e42c08001c00400c001005100c0c041400a44d01e4410030703410203e654180301401810004c5204c07020b0708901c4200f42c0c1000f0265000500c80300360f917007141e00202c00d0b06415a921016000c0050b10b6119489890761000200c1d92640c0a80d114a42000000c01d00c20480c01e41142c2c01e6030142c07404d00300e40d0030859401e540c0700e10803001004103040040c1120b140c07558950b505019070306c5002c801d03404904469048400070380180704184000404900800c101f07800407611000c0340f6400d0101a01a66a0f2120700200707100946c12100074041380303203148403465601d1400e0309020000340142c14041c054804000340c1c1d00000c1c001d40b0303c0c0c900d030301550202d200d1500c80c00614540000300c0310420400050045482460148182500384d940040d1104226 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 538244496 1250 538243246 538243283
    0x4090f0b190f050f18070c02030609150a090b070f0512070f0e0a0e011a040503150103051e0616020a02090106090f0e091c211d19110102070e04 63
    0x35440340d111038000d245850004c2c681c2d64441c3d186004010040d00515640c0d1100042100c51142035a030003034043c4168018071000e8000018111510006800795002c80d6903540c0710711042c0ca05030310700203002419502c041113030240207002006081c01e040c134096003400c031000078582042030145c5210b00031501409903814016400201005400f1050340e9802c04245400840050080140f2070411003031142c40c0950f07a01c21254046a00914009049034150a0441980c114614081c48201c40d14411081109030358140c40c50800c15102c040e8014140700e0741c2e40400d10400450300c803c400c0460281d60402c10050782c6402e000c80c044d1007682d0703484103154106490b07000404860382101d440c5642850401091030000600095020301c010f22141084441400aa400c504440100392200c00ba504a034086200c407030303100e00c504514400c113076039030702c0490035286480782030202e0310812407100c40002d0000b2501000c00e51800a074180b0448410540d84c050910003c1e038192003c8500c1c2c4503003101c80c0b086 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 538245746 1250 538244496 538244519
    0x804050f301504230d090603020a03060b1315180e07260103121103030a020c03090306090c040501090c021e0f0a0602190503070813032309030f06060604090f0b19 71
    0x803154410002d01c0034174000138019150040c580b082800701a000116200000d102e9081407000340300c42c20449881d0351194140c0901d4450601450030031081c10a60220014401d40114008028050709140d81506210304800d61010040440b130900c151a02c0700c80b5800700700c0c00c5100032020050000300a6504504d044201c4801020001041128651011003c0d01001c01141d40041800c50b0059452050388000c9085000b0b002c00c080c1d06002d032000308a10b0300d0000c80c8890f441d441c12075040040b03a80310040d400c21541c2d0b000349007006a1024842520155a130070440318030317101c1c5000312500302107095030705071a003140710004680c1d9503000f04034a0b50003880420b03c80840c018604100781075141200d40103040c401d004020130788031707415a10307600149801552005070f0030882e0613170180000204010304049a01400c101c2c1d0092160720080c048060020400343c0c040c0100270145850280f420000c40050004050749216040c2d4551400d0855541d40800043c0348030a410040082450003012040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 538246996 1250 538245746 538245803
    0x114090d020d050c010902040c4107051509070603050114010e060d0216030806031603020631030c0806010f080703020405090a06090804050f301504 65
    0x82a61240310095030264001c00c6040c14600d09140c0540c0b583c540d80c042602500d41c8038070194129250107613210380d040d40802c41803011202803040f0020b017901140740109503107001c1d40042c448429491104c550512100082802501400440e40301c008206d82201011400340c032103003400c0e1700c9440300f0021103030507014140c010082c4980305030450000500281045069003c600c2c400c440000344001d49a150342c0c1035505550b540503008100b40a1454082e0222000740c410078840e20401c4c900e60300100c0c19040c0d0300107481c0d014000743e08103c941040b150070241d02c2c2440300d29841000b100c92103012540081440154003a4501c600090700d0440070b28100401a00012000c2400800521203404000360600c1103d1381a5000609039403554882d0703041c551880f000500380c2e82450701384002d02ca810400303802031380c178112403804001e16800308210110300c0c40c0c140a6030b440c4281048a06415030420068441c203a520162146010040c010300603080b4110f070300300c840c1b122002c0d14001a8554a50021 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 538248246 1250 538246996 538247011
    0xd02030d0305011707300803010b071109090d031d060a0906050603120313030e10090f0506070308040f0204020910091a0f1c0608010c030e2518110301080114 69
    0x4016081241d038507664402202c00706e1041c0141e07211220000f29020100403211f8001e240241c99517111303c02c8035843c0e8805102916002003c46c0346603020f2800b040c9050013903941000504a141034180183d0140800b0700403101d00c004003600d009060102407144503c50f04201100040c6030410b49450411a20080c040324001d610512203680408800011241c00c0308048903072419600e100c1c0740071200d01c5100940d041c4c00a1400c841d54507500d8004c1c0c0341c082921980c806448203140c0307400a10807030b4002c3c3c080103000502000c012a020400c00302028980c03034000f900141ca0010048046800e0302d2402c5141c80000b581100200003040e0380d10b41e4103001d940a0018903251541c0c1c104c03014040c1c01008514821140c4206e84e00c00170180303551000f401014024000d001006a416003c0c0080001440c106824040c0c41858000c03020312803081860001030520480800c1e0600c124a4054128420300440241c2d40b0f82d000f100034009440503600034000360001040640100c00c40c0d100c075140140011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 538249496 1250 538248246 538248253
    0x102030d0908071a0402010c03030510050a150305070509010906050903030d09080301030c0603090b061216170606040b06040303050d09020a03111f08072706031407020d05180d02030d03050117 84
    0x10307030740124070b050860b409d0720f0085440d841d407801c81c24024115510181e0312034820080010b074130410410b4805402c016840811080e540c1d031005030394510a0b0980e150000b42002c00a019250040010741070003d002340c122801c18005000e0403085508082c0183c9448601000410400980b0702f81c68000c0d04491030184521503180c0c0e10705241c4140501054031410400c4002d034402e4070200104014018140b2035119100d030780340b13610321312482e10144442050007210000348450415014000d8044009458186094519101112150000700080c0512625540c8403005aa07401104201442c0940030181040c0101c0d8100468100c44144008001c02c11010b203401c295003084c2199840b4400741415014070000c280c01c602040340d050f01240c41120b00c0d110204d2450382c140d00201d020780a406251000e611307590300a9a540d10070a18100c00200e080000b100d00100150010006101c003a0400000300d85982c0024100440c0c44001c45c0080c0c2e43e60b0040003104002000d441d40030f41c045003d0f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 538250746 1250 538249496 538249501
    0x2040e1003022e050c0a021e040606030b0f090711010912170709150306080a05010606030e0601080703061e14070e0d080313080919080606040515010c020102030d0908071a 75
    0xc04119070b0400181804e2010124481200800520507100c2880d03005104030341201090700100d8400c500d1540040c01107103080c10100302d884c080c1c0704000d481400200400b45802410b010000b00c88402001034041158814403185260b00134001c001c8020300c212640281c41d004418002c0034410f08059841c5d03241e2001060080d42500210007506440100c040c500c07000494600c00d0700a4402903110030382610900c1410002c3c48030660042d4180c400560b4280405071080c0d442668a860030700a8034480e4000c10070030400110907901c9180903650001000a414080401c01c1040f9801c0280c8031185142d640c04000c00d041d4403d00c02c5004400840e17400142400584032010b00d8000102641074480c408004030b4207100d07015041d1071000c1c0b0001c0c10002e40070220380d514000e007a0244a1140d1511600d0003040c04c61a00d40181d5224220580da081203c038040c1d80110f465103030129041e81136000402505800181c14026060054010f041a0b035980745c20b850980000c051603891498030441c81d105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 538251996 1250 538250746 538250809
    0x31e070807121103060d02011e0507061d0d03020c0a0c060c05011401060c08130506131508040305091c0b1e1503070303231902010e0622030302040e100302 68
    0xda80d04807105a82d906c4030b8a51500c01a241c113004d100001d002c0304516019920f015a1000c010b204045c031981040c1b00300240c1003000080041ca0000c284030f150051f07910308421902c01d5000c1c25000c0e007074404603a000b041c0d42d00d58001c404103540040c0700240444a1080510000340980b4862140c80d0000410300d40c508940108030301071982c401003000700d0006240d0a44890050b4450150100500c1c07981d8510021038802604000c1c2d02c40d8103034000d116540c0e000454050700a451182da00b50310791929000385441044101c0d08860303640200c01c02c078208041c2c0483c480801140c0f06030540402d061107241e00b00303e00c0e055403100911101058080c41c16600aa4402141071011240d060410424803d049000e0f42c1ca041d603030040d0300040b0740300130641c0d00c01e21411200c02e40e01424a40c000b007100005a100c02d503120f2508607200c1c0c000302c441d001d80c44050042d50180d01c0405000385070041c101b0741c8a01c84020b1401c0c0c01d4440c3c4061000c032200034170640c03814000400d500d03940800411003c000f80710 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 538253246 1250 538251996 538252031
    0x130b030f0604121404081b09090a110f0315040503030a060f1203180815070801060c0b0613020702060408011a1210090f05030a02010c031b0212031e07080712 69
    0x2e80442006004413451003401610020b48024240e12806e42e80039454036101d4412081c802404580308943d40030120f0030810700031601d40c1429401015402c0740c0d105d0f038021302131485d02554104c5d40500c036480e510720785040311203500740c05188600d010710b40d80d05040d0014810340307401da008913994510a24040001c1e410b81c2c141108107582c1420410013a00039001441c1000105900840c003174020280c1c0161440481c07800c00780f1901e0076072500415070342c03140c0f4122526901d0386401040c00031103901054552520313101071401024206000751030485035034080b40090304240c0c882804c0d6134541c000509000e0202c400301c07100c0002540d40c0d2010951f690307022940c402146064000003542c44807000305100302c0b290b044015941000440359258100400203000b440750b0154140007c0c034000385903901d118035003400c03000071020341c0c000c008803040311003000071aa0029084400ca0001000c25050b04010840030030b1007449603480c0e042e0280b400341400751041c080048050032061801d800e0090403030b4590f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 538254496 1250 538253246 538253273
    0x30b15160c05041116020d080307020d0f0e03301b0c0402030403021b031c0809010516051e09030109081e03040b270303010b1b06040201080c18130b030f0604 69
    0x8980305e10401da0940042940301c1d41c4210042c244010010401c00195000220702c40455100d94420140741110a4116160589106050761680104180d00e4568200c1050300040c811a440c038010014224884107002d41e001940000b0000c458005e0310146074030900c0f07503051030394040d2000e40c51450079580c02500d40141040340c6116038903801c03810640c1d480c2040305070801c0e40706118808440404140190421108a49098203582403070700048045084080040b2480200d0b19024200b1030500f50700c0c050ba00c0d41c91181507150009200d003130f405541c00d000f20129103014803103079992100080842000e021022314074401050b41041800002104a08000d0340b284507407519598003260b8444078a40503480f580c0103100340c803021001040d00e00f01240104500044103055010743c41000d0084d03619000212406404a17484000044071403a817a8000e080305030494060759440c1142900142000102011150405544001a50507070408100745220000f07404001c103150324256407400c03c00050b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 538255746 1250 538254496 538254517
    0x1051204030909050414061003080415120204090510140a0e070513030c08100908222c0919081821120406080601030b15160c050411 58
    0x14100040c0030315219400c0d031000341415010602c80b6013403130708018030402001129080c00d402440c0c003040d400c107604210178003280e60005016003018035180c40102d0380402c40204405020003ea001031018600e0b10040025000e10440010319041a003504980011190040455042100203070202941d5480032003044407100802181203984041040780c0d40e002d012480300300030410080210810046049103c180d60540044030300c5110102c1820b800e590380b09074058082841040020214000444406148800c01c458295040da0f14100d03a080d940e403a00e00003400c101600700354042c40024032034040e0000740860041c4158203401c16100303c04d23800c014004054100000d110680c0c12500c0c00a50700c1070704014602c11000a100511910011070501940c815001d03820410700460022410703a01078800b60703075900b802031340c6080c015030040500c2c6032400d6110f0003451140d04960307500402040d40c03104000b2020340c5000c42c4e03e40740c1403443c1150841c51046040490110b1020a02816264078100d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 538256996 1250 538255746 538255777
    0xd15020306040603060f05040204050c0a050405040e0c090708090c06041d0a15140f1f2105130c090c02150a020403050d1d0405060d060e01060906060f031a0105 70
    0x200c1c000010b0041003a980300810381c50821599200c552030740e6014512a5000366002d000039910740d03c2001a900c100072255022a0080c0400d11607030401d039001d46103c680b03250441e440e8240031000107140304030485180c00000c614804010300c010703090111481411040e145d042c00c0c5418100e944a01d800710011b40e81e0800740b96000103645512503008146041c0d102c044100070183c8030b032000004c0340c080205450060008001803a03070307406d010003500300e0655119401c101c21098014100d40c03540440300c248440c1079040d4000c1c4004009841082e014a4a0b850010040b520b40e05e000c09018110360302000c0402d141c800e04400c51794022611410300c0e0101418112640c0d1040d41100081c0180d81015101f8414260308206150708040c20061401c2180020221101410104800d440f812030703a0302e030403a0082e000300c0001101c0d508070440c082c1c920b1001190050701c50700d054044a0a070b034020300c0051805da0380940d07016054400c00d020a6500d401603c4107260303900c00a0154466402d00214015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 538258246 1250 538256996 538257001
    0x3010f060206010b0d0507360b0403050606090a09060c0c11220e07030c08060106080f0c0403140c04050c030106170c04030201051b15011706090a060509010b190807050d150203 77
    0x144281d000b5a41054003a200d03060084c44120502140c234511034203550780200507000803454010f000203036000c41303911800910040d510401884a5040e015160551b00d94990289038000345031030080303050816203556580d00710b6041342800d5072980c1c51240060b01800c40c624114001790206940c880ea201510000881c1d540c1075005d01c203141010548c405081075996440100c1c0c4c4010115950341201e00503900c40f0200e8803041c04454080c1015241101d504404000803c00110400800b000d000c1c02c0e042030340d019117515004203041d134004a0f03c4000c04240040107201254018400000f41004240b80300342515020070101980d215600001c2e052040c0898841c4030300c2841e1038541d5811441d0010748101006150072030035200400e000390718000403151194046070178000b500c14411105a4020050b402c0251500c400904020b000b0a025540b00c8440d540c4a0300d032055191085400c2000d030002c01031410b240c003424100305402c254030805410f07080c9004039031016000f1501410845c001a500c0c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 538259496 1250 538258246 538258261
    0x13021002070305012f0c0304031b0815041203060806011806180f0b09060f22090302030304120305060105070305030703180615060f0507150609020f03010f060206010b0d05 75
    0x2101c41d0b80010901c0d03080004541528002c04082c05100c88400303c94841c0c078403600b401008034040c100740e103c40c0e5801400700300040751074110989000745410441a410795111714030b207818801c070400c2002920540c941880b041041ca03149656060300d00d8602000900c0c02e00309020303101d03081807250300f0b045400400080c0b1410008c1e4041801080072080f10010700d0381410b50715002e8000401400f101a2914054507031504101d2662842090002c0c04040c0c002e18200c00c010a45203e20b100e14400407a8048846886003103104108466010741c0055440b4a440e1401510110300303841882c0c205402c03c0107200059070000f040c0d0320400d0381414141e4403541d40070302c00c034000c1c22501020110040410514030a20581d540414110740281003207074070340c83d211801590b43d04040b003149000100e0411001d40440c0c00d0395000c0c00c900c0603840d4040350059507500510240d800072500c2c4a00031000000400c140500c44081c00f004043c2030004e40803071340c0b6120b0000e50358018224050207490b00c54001a405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 538260746 1250 538259496 538259503
    0x21507231806090a0b07080d0507020a050c0301060e180111040801020403110406030b070c050a02030a03120507030b030c120c0a0603050108160503060402060d0e0609010c0e0f150a051b06160813021002 88
    0x70448c4000f010049454140340096841040c5442650306016040c5080340504040c0115015141c0c1c180700d00f41903444e060503c07a185030514109420315507944181c4c00324029200c00410040140c20000351300c49043d030502801e00c1c0d01e1000d600d0b01c034034070b4030070100005000d0040399a400302d01418400040e15172410040d0600c004408025414040c2c18492003c260b04600c5e004e1100101003c1085035907180070b000d50889100107103169240d8010010812a4030345528072807040310041087d100108002401b040c8080803980110020a4a03000180a000020060141224100040381c080b4500e000d011940315400130744041e0103107800113401c40940000790080150304250038111905403401048040c000d00c4080d603c44000348109401d18510b1808005042006c90010560404810002822805035110403400c5060000a02c40010008241c03401034107074919440c0900301c02e2418486c41d2021017001c480d02001d01118000b881402c0c0701e40650110f00321f605881440f40801500000da18 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 538261996 1250 538260746 538260757
    0x40603120e06040f0603020a031b0206013b01061814010507020a0e04110123030f040c080f010e060a05250306091107020f010c03021507231806090a0b0708 68
    0x10300e1884c41000040e51035265005283c0411a0345e020071840d080000000501c0c50403c080c0c80043c0d01210060004903100c0e11291000010302d4034041c002c80c1c0d40448c1640c1c010341c400000c1c10030701a000040028507002001d03003032081c02c030b25030031b05a65041c40b05200c00c01012207180b50401c20301289480071900d0b480b0000020b4148480d02100b40e182c01e290061020343c404030b0035070010b6181046030b015440f4100e521061080030b00552810f540d195900218030000003042503072811104100021030050900036071032885500400030501040134031215281800190400014a06c1c0c0030810a000031504012040280e424100407543d07104076908501905103600841c40d0903160104801e0f4008443d0000c082c4580300361081e1000a20b905c0065928229442e005000360b00031b602d90f504210308800d003041e8481e03d64105104d84811540c4407131815503001c28421450440000c0f4048115103000700d1259044040300c2c01864103060b0f001052000e0390a10904c418400c000c01c4400400501c80b05a0301c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 538263246 1250 538261996 538262009
    0x1b04060506030415290103020903100c050d05160914010306030204051f051c020d060e060f1e0c1608040b031e071403180a050a060501090b040603120e0604 68
    0x141c503418203007001c010344221121074021007460004c14141c14008941551749141d900204002c402c0b507500c0065002e0341c44108495494002c03c01c28180c3e038062441140c007403041644d550743d1165601c512140850780040e02c424050150a030744404000d900480d103609642c1013101c8000c0c00ca80040060317000c4d001c13a8200a500070308100401c0f10400401842168400c1503a40c40b41c066583e400c140404400012100210840380801000c09801c0620800011a2060f400040d01c2c1414841c92414103009441e0007032541d00309010300021255080c2c2c0200c450502c00c6000764a403e02900c1c043c2103100319407200c00c4030840c4049900030b1102c1c00c400d840040401d007c10903520302d050109200039032202e04041450300740f60008280c20a20501e55130301a0780c00145650301c0c5403551400c0c003095600900c6402418460001241c0019106001c00c8142c988268001314295041909041c00d0314140103001c1e00440c503228003000443e4040a080f0400704071400e000c1c10040c401c1020400310b100300e41026 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 538264496 1250 538263246 538263259
    0x612020d0608030c0c06040305060411030f030403080307031a09010519170d02370c081603020f12150c21010303020d0306030b040308060103020c0a23010507021b040605 74
    0x841440100c004c2201e40c1990090303070700402001c3c0c00c000c0d003030055000141403688040c1c000340c0010b00c480a060406139005085491041c4901c02c0303070307180d617200e500200e0b2444404030500c1120782d010700607210002c0910846003030240f00c03c0b01040c52400140b20300c500c02d9540300201220528090611400780c0f245040000038070344c542200c1655407861040d01c0d8010305c2000c18200c0c40d0fa01203104640349100451020300580d90360312050311155100c1e041992600c00400c0d000aa100b0100f280c10441002c1800c034080341b61a50040010781c445055a4601031003080015908180c400708809031070f5800183c0307440c01e58648440424460180361040d0f4600282403400500c08080d0a02040c12203110744d084501c1b8070201c0c0021003c0d5251484001e2181107142d0118000a004100300381d40b1403018540142008d6a500da803900e4042184020b41d04400c1c4030b01d101080c1032010820315011418003000340640d080c461802542c0740c00e809105d540c080e03242d00041000e0f07919504034a00420300207108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 538265746 1250 538264496 538264499
    0x304030c080d152301080403030c03020d02120a0606050a1205041403030f010f080319110a0206031303030e0102250309030b04060f050624070201050c071d0c0408070612020d06 77
    0x604032100703540030b10b50080b40300c0035051190a01011604240c44e806030b41d40c1d0b89644a0307540c19005403070301c994610141a000d101c406034287c81440600042d0301da0301c1426801d4100f419000b400c90b4142c1c1c00200400030100000400c041d0042d013542401c110450780000d4954030f5045c9041d140f01e40703030501d000d940400810b00048030901b00707045040e540380c56841e25210b42c0d1088081e680c1e1145040740076904d01c504880e01a964018940c4484540e81c110548080d007a55030300003081c607401240c5141801c003c6609903014035500d0700c035140b0140c03401e000851801f112110900010410301700c07040a200441200c4c030302011700c18502c0074011680204241598102031800b01e001c2e00340c00041ea2030051401001910300c0c03403e2882c42c108041c1503a00c1e0725000102100840056000b20410b1f81070290400c80c403103085800304405402000388a0034060003d0a5644043c0d04000c05014942414400d0100b80310b42e61010621030229011070401c0403003075540600d4840130307016a0f5203180780c40340740290 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 538266996 1250 538265746 538265771
    0x612030201020c1606090b07060b0d051f02031003020910081b0907230306011b05030d05010524070609150501080c010302120112030c080406090504150b0304030c080d 73
    0xc2d007128180b41c0281c40022407a0110301425180d1840380304006958910308004049031f410050090b50302a107000309855040c14007003103045031005812101a440303001141d81e0484202404107030010012415451400c051041e68840e45160101074450304500300490403504003012242c0c0104a9a0295500ca5100c01400030302000600c44441c0107840d036070001807032244101c0c52007d8048500945c01550324004104080310340005143da41401081c07801500700c514801c00e0080014400c0f80103507a503a1150345600180c1e0010b034406030098a200d03d010307109441201700b800060200341c00705900e9400e20b046c500c01801c00c0e41d6010381440110f201c4050070713010316042039041c1c428182c111445401004011412072103101d07501100d60b00c3c1200103010f000c03604000c2d8601c0342d01034075000c40140c0564a48030000e500a520040100c0c540c0c01c3c1c01c01040c18103002c2c1c4901e5019525100303207480e26010030340c400f80c40000c10040401254540690402005d203040d00c459038000c00081202c0d85541c070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 538268246 1250 538266996 538267001
    0x3010e0a06090615030f060917040b03181615021002030f06030c150912030904060f060807092102130e15090109050706050d0219090302011206270612030201 69
    0xa5440d03a00f40304e040030811140c09a450b040340d600036110b11018807180ca50038010301059808035802c0400175900750980d40004064406003003119171280e0b4078107002140c0e12404c68443e540e421250080c4425a0b40350b5038003a056000c0b51900380c2ca040764810140c60481c20104260a052003a41c40482840b204040034901540320750790503401c0302c83c05a898400c00c131046d4440140358050600c104106100d43c200058600d240b00018412203081c100c80c100028241c483c80e07080790361030884282041210941c816082a000521801c080c0a401d0426490b0034217050704401c40034413640d880c000702c01152035200c81b00901c0501004d00700984d0144600b015240d00107004083c5107441044003050080344180300c0c50301c0269100008115042c0380040550303207604180031048102d0390a00c00149014a02c1c805030b01100b4031540c4140e0203500318800941a25000b0803206411490184140441c0e0900460421844618140310000d56190780c103200c054100c40d0008205402449a50800c068054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 538269496 1250 538268246 538268261
    0x3060103110907021b150c010f0c081b0324040609051501110607031119030c09061e03110403020a0b090108060919110405120f0105072c03010e0a06 65
    0x45481d24031a40f01d4150482c1d0301c5900c0182c903200c00d02001c00c0350803a45403820a0f03803811040d144c400c600303000d6914031840c211030102c40109040c43d1160200103d9540c403804880d848502c006881954180c101e644c09190700004100c82c2544841a04171400c11284d10044034144800900501003142c44030500700203008141c50900c007610004541c817086c9d6003c1c0144040c0031404100410700d03981c41110440c0507100320f0913400380b1a4810803003c00a040e40d070706c41100d00000c548010550003941b140c02440031341540d021000b0032400c0e0140ca844140b5442c07408a0003640e5107808200b007400346000f01c4142c0301d9580025031080d6011800a01046003002400012000b40c0342c0142550301c032010710034050300469011440382c2e01c100a02d6008034165000c01d420000c21208a07003460b8451010480b2003007900188a0540c1c0000710220f00c40d8000d006450b8009094a80200c0c00c0940b6110001804841c40c18409000c041241c20b10458400f54005c04190038450101c841c40180c0341090001030105 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 538270746 1250 538269496 538269499
    0x5100f0b062a030903370602071a0405030a0305040503130f09051621060b070b0612010608070608130816110603010f0b03060d0503191b02060306011107050306010311 73
    0x140d0100c2c503894000441a40e80244024004d800440480d01d40c581d103d251110804800c04400510840c41d094000103002503244036920045c1c0c0c91401d130511203d2080500070502da85910b000801c03000a2011003946c914000504020446031103034a84113007540989180e040444803405e400203031000107070b00344400704c80205008121503211990030201050321070348207102048641600b0b4402080d087c0014040f6404040d00040e00c42d11004850b038030f40d010100030358040d020981070085510703040c0c00f207014803540200204045841d1030b403074030780783c100910031107003442800800030301c640e81c50302402340845500002099440030303503088070303c0301c05400f51058901c03c41d500100c41d0300b42030200459050750340034151020040c1c600980c01641d075200a0100350015844202800010800c0000c3c24502f460f005410104914016004105404401c42c00b0558a00e400107600903841b0601141d82006e02807801050310b240800b150341c6010a0380c2c6c041c58241c45540000803e0002c1400b0f40c0008040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 538271996 1250 538270746 538270807
    0xb060d0c11061501091a0712110321060d020f040b01050909070206010f08030717030405010207050601030c1a031003110325090c021c030c020c191a0705100f0b06 71
    0x1110441040c01303034000d40940510f52806c100042c0850780c2340410011030703203c82c41c0c42c0d103a02d004030803000d056400200040410b115180c0c14413003001c883c05170066001030182c5110b420707001141c0006105905031a40c060146940781c10f1003405034030400c00c85001b0790015140b9070080c00d04080007035036500309202d0b21042d1280c0d04004602a9004421201c01e56001044403500101802205009500180080307030784e50350810154000032020711005000310b0041d00342c2e2300390a00c3d05901100300d1070000b030b00324038180c000c00c20040700302d40751b081d488c051780c0e04036045c11514101c440100c0e1a1101144060805020304440900746481448035181038901ca107105200c244d00942c4280d0f518031071500e0f02c0769039100109008140c14800e50000c00344c0c2030703988100c03004d5020f080d000c190380024010407412080380b085024002c0c540b00081410300c030100403890b80c2c50401141c03141500d03960000e4034451201d444030642c40811040342c02034421410018005030751201c001c000003d400008a14003440503d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 538273246 1250 538271996 538271999
    0x3050c01031b02060105210616020f0a080d0513020d060b040b011d010e0103110d06080c03120a0c050a0b0702030c0106060305060f150c0f0d120b060d0c1106150109 72
    0x2040c2c50008803090503e800411450342000c1c108284100203980c82d0442e07001c24811120300080811895000f20b240c1c034043c9841055107000242003101c403015011280d4400c05078a80003031584001c07220044140d000001c5c02e40c0f2034a2480e00c520b001c401c1d006e54029982c003071440901520b54070201c020601298104040c030030007001510307107114020b0100b0060035841b1050856500594548801c1001490005000c4620f10000b4009401c18079242002a5903404140a500d00801252190a004070300400e040020880e14002500c5001038143c00c000d403914055080040801c031307020021b64809003402c8607107400e140007540c0760459080c501d402d600345030300014803600a03c5280e01418000d483d0718070754001001484400104100ca101c075000d0104038503454900140020555003140201410303612800c07504c0100700064852480c2c000c10318041c1100520382da040104c0d10b03206194040071070440700c0028260b4100302d100d0041180c5000d200204004d520545040d0310013020241c03280b141c000e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 538274496 1250 538273246 538273271
    0x216050a0c092304062004061d1e061c020d02030f0f01030201021c0e0301060e090d0503060a030f050a05100510080f06070507210f110d0207030204020904020f0403050c0103 76
    0x7518410207100f5407035548000c0307030110b502070f08030a0004016050203c00804400115107a59000b03a1195000607a400a0032004107403680358140e036007a0441e69859612100021f000f40d48049074084c5100e040002660000e102e110007100200060000e000c540320302500c000b04000e94400c641405100042c40d000501004c0000c0c0d040e0b0580341c040e4000c10b00c41107540c80c500b0003080032718942014440803101040c0705680034042c00d0081d102c0107100c0605402c2c1811203d141c019046807000501000703004100301511001986c00440380c10800c48501482c2e41c0c01c007142424140320000d002c1d801551030b40e4500c1c900a4000c41d0080c050041c4070410a5605c1d84981d40394500026200c50750380002001c281ea44e4891000307450000e00070240106130304980405500c51103103003006540881d90000c1d01c01c240b02e400031000b904031280000641074075407503050000e484042c81d0000034030496000c100b0620f1a1904d0703050341c10301004c0440742c80ea92a1641001541c41c0d40061082e400a41048070715800b2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 538275746 1250 538274496 538274531
    0x120a0f0f0c0b060415090f0c02030c0d14120a091401090305220b07030309110f01080604270807060b0307050d1401020d090b070215190216050a0c09 65
    0x10502030703a07600e40200d89a940d44034120b12000c1c1c041a8016160320908003c070ba60a1403810040000c85000951401e0003105007041d210405800c03829500180071070310344a103000c20000000700b06490010030804045210000c00d01909240c1c8050080d00307400c0046120269021038443b9000321a0180040c42d014556070903a011107800030002030003130003044801c90000f85c41c50682c0c00c1442c00e094885803142c410003016008508240d0010b0344410044040c0416400c20b071075809000c0e180300400703110b41e5001070480348020b4549400b4540e240000300940c40c130038800315048010340e0701c4c40203080c00c00d0402d0500340d003100d00309a400c1c1d440c103a40c2101c0c0e4a00000c1120441c4c0300940070114001560300d400c1e5160180e80242d6886e95020010b24040c20785911405480b14810189410503050140d80246004030000e2040c1c02c41070020240701420b540d08800244120014030096528203002601d2482c0a04a46004203980f20703a0405600700200410744000780e4920394801c009400f440d1b42d90080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 538276996 1250 538275746 538275767
    0xf030102130e06040902120d1101091707051501060c0b0108011a01140408191202060103110f030f16030b0f1501030c0c151a0102061512070305120a0f 66
    0x140c0708140c0070840001c0e2031400503884000204002494070007500466004840250071444a81010380318200d4030f034200380941e101503103e2000708072444141e966000d140c110300500d10700384c1c0700104e601d408000702088140301e0140d0802c2c212445595a0301d01030014160041e0480c0c040c1e1240e8000f090703103c014414441c281034030000040218504400640301c0c1071040c080010030100400020a8000082002d07180011b583da441c640c1d624064108a050001850840411504440010004100c07550140744003180110b903a0660700000500203031a00c8100b000f034040318000d10000480102c0b20a4005c1c007205e01135044603003a90744055a20020074405c49810118a041060100f400d504c0b80c0d104040900302414140312025240e15860580ca40c0030b07040121b1036454542202950001d2680184290807c0c0014011070510110015075503004190b010f0180c180360344070040300c5070100300400003180c00c42c003501c0e002d030042a284a6194000d0000c030010a15404a4901d210300c903122700792 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 538278246 1250 538276996 538277017
    0x90d06060f080c04290a0807080601170105060109030803152805030a0c09051012050a140a031e0e06070302060a05070c050a120e04020c01020913140127050f060f030102 74
    0x5c105880f1244098062501c000006400c6003465001198417001000250040c11135000203100562510251748107801c000d469940860b410f02040c400980d030480240d000f0369501c42c0711540c4903174030b080b210b03401d4424410649134400d50305000f50798100c910903201d000010440d1000c10300c00780c4410515603200c01c4018024007000e60400c04218050040c1d01240d0819250040e101206070f45108030394101382126801c0c0c5050700007135020010082c0c11800003106048100c05803c207001240c074054240c00616880e00145010340134964070480c0320340a03c2021410040c8000c0d1500e58a04000350394034001c84010303040303c0c40c0c4004104000d00030000340c5055a030200083c500c1e0591b55071586549000701130000188401c0b101c480c0c0403592180081c10002181c03000050701c5840e15400c02250410034000800282e2516040c1641d014440030500e06403a128200b0008510000000e100400304a103c04d500051801041c440310b03100303c42c4540c0c069901100c84a54010506041500b02e01c104600103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 538279496 1250 538278246 538278281
    0x40503040303050c100606110708010b130b1c0b0f1b031f0e011706010e04030c0b040c0f0f0914060a060309050a0203010c0e01020709020a0f0302090d06060f080c04 72
    0x1000003a1103030f00240703c2e2550b07000544120040c40c038925070940380ca54100b940841c02c100d16000d0102d0007080098000c1902200034041c8001100120308500d009041781c4091a0b2103460740d40d01500d074290403028010030200405d007503600504042d550540700341c920b50b00c40310008000c11800741600000320856901c8001c4a803031925503040484488400d810b104809410070180069000051a50180200480030907144c0c0b00000d1052503080c440140c10049088080c030b004d10000c40e51000c03285400c990310000d003134141c0d03c1d5400c5c00500701d40d465018400030294000c010a51203d444e083c0e10440c0d0311007109000c1e503000101d0301003203060101c070215002000118100031480c4641c102c140c460740124140d400c88446600400e094810510794080440d1180d440d80f021560304005120040140e6a421801c0105441000382213011503241001010b0700451340c00380507500c03884811100c55005030108602070b0389003861054030800340304906407401035a05c800707010300307040c002d038000700100c1c0d42d10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 538280746 1250 538279496 538279499
    0x912030c120a090f1b06080405032b050103030f112b030b12070e01060f0c03030c1416020907031104030609112701060f0e0f042d0b060304050304 64
    0x20710707071459004181100080d101c400303800204940700c2440c02214003d194101c035102000311039035041c0f00245c0c0306104101e00f110820010078004001d440d107410008100314030900c6120801c03c5110122000142c0c16403605000004054200b0001d0a8840450300c4050040c400000700707039110f12480c600f40d0f9080c800302c130b6180d0002000c03850a203007204039410300040e04490480031604e030200e0782c1c00a11880d03124800501905000d034030440e00501107840c20000c0d407490240001d180004401c0024141a111940031303006501880d00c040070340c100f201610340c5540c600a8400106c2c0001e50b41a030280030b101011506440c8640186017500510005451500380f0350350f0707a0070040510701c1080d20481c0402034040151365130080c200341d898218503100d202180c20420018064141a8040418480d00007803072011280c121607041c2c04108102e814001c4803225002007805490b001e24003203a05440301c00030100d5101003c1004146c4000008200701c42d00c00d01050001e076100584003c0c2566000303010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 538281996 1250 538280746 538280767
    0x140108151c020102010219030f0506090c0d0e071203020604060b040b060f0f04050414090601080a0308060405070c0804060315090902060708130504150801051f05060a09150203030912030c 82
    0x8040002481131000520f09450080000c1d50744441034820300c0043e40341c3c0311065071140c20740a100e4005100b00d075051924141201d28880510843c014445180e458482d1402c0c0e50b002484500020b00420082c0110f110052400a4943c0340c11034040320140c3c0f50103c4080c00d41040d00c1114044c80002e00054a070054082400c4040d400882e01800c18200801c0042036503125800b079140206001c000702c00490800204080c03e0081c16008110305510082c2001d01080d17004030000d03080842640d000880e62540c01c0c0845400c002c800015002c10400180061030710380c9603001004004e450040d024001c0d4840384100261b800e01c40c4060340c009401c2c025103002c81e20040062007445110100107403000e540f180032030180c0b21026000750182d40d01c184d0801c01c2c0350080c00fa1540c00f107003c40c8110042017007401c4800d000d510a0203014003411003c220065000e004408200141c0445000060020b11107880255071341e2084a0b2031805004200c400503058048000f0f4a0083c3c281c0e51800d41080002c46 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 538283246 1250 538281996 538282039
    0xb040302190518090615130e0f0a030c030807030b0a050405040819050d0b0613060f0203160b0a11280e0301020d050907060f050d0c051909050901050307060206060603070c0c14010815 80
    0x4201c40801d008040340c5414050b010002c2b2401a44291110103c4500b5820082c11a00e401020301c002c0c0360414501882c283d0350741e0958420b80d041141c002882d52a0f900f81100c441c0140950118240a80050303618080c0d00500900b1840751010801e20110040343e0a0100c0d50240700115000702c1003030340c400d011290081000a103804254070480f8240500007803180030603c0880c80130b032068400d04081c030015085600402c9280c01700d104440e46030504001c219032489041c2450f960001c240350380480c01e101d106a50020801c00700038001e41d00c900044140e04001c3c242034800d0a0b040c031515100090b414054000c0d40d01e6010306454071030818003805007000103403000036039020400c44c1c00c003c0e205898100c1402508001d00964580700c2160170001880348149040c0c03c01031199102c02401c01c10540e0000b003081c0d01450030341e00c5545070b4803840d000b92584904140c0c010041c140c150408902009601c03101c80c010007090341c41d2035181e202c40f69500c0c0030802d95024141c1042d04840d0141854480c803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 538284496 1250 538283246 538283261
    0x60504050f060703150f030206072a03051506040908042102100201020309010f060b0409020d0b04050910150608060d1a09070314070b04030219051809061513 69
    0xa1003652018841d854441d400e1000880c2c01c403010a50b00c2c00029030741190844240c001d801c50140c0c506041e4255000500103004800c0700400103925501d84a07000509030001449800085040010490b2686400c584542c41e6215555041502c040050542c3c83c280c000d503962283c01081e12032400b41040503150a03241d4101e0b09440007049810120016210700d10b969143c01c140354001031716070404144503030035546c1c1041007070245400c0c00f40520030108007204880403944c00c9003005a80708001003006c400b40690303222040c0d000d45001c00b00202d611010540005041d40ea030300801180301c60724802182d070b000740e025050024803000005680d5003401d039040781c005401030b500c00d50102401c1c1c0341400a4082110020303d25005010100204030a0f580709800c541228805044028107100c2a035109001d5807001900c64202402c415000000300f00d40180035080180c02043c0c140c10301d44190400d41c038240e4440c046032140c10300040b145a80989a1802100010080c06203005030500d4040900080d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 538285746 1250 538284496 538284503
    0x321305030f07060903020f06040b15012304030b07050c030702510414090408070803010306021216170a2309240403140c06070309170403020904060504 66
    0x1000141003800380c03480582010341c403c0402207420512894000c0c05e0132040c43d845503455011005000014030005a102e5000c0c1ca28180442d2a800c0300c0012203c48503030300c8410a0003a40046144125100030b4010019a800303040c548485481d5000d04903558130401c0b0b4521302c0c94100b40202e40040ca0200a00744d0902568404810a03112000810400751001190341e00308151014a110f014030380714602001c003901e481d1805007403a151000c0103184580461889201d00f9810001804000301a01a22819504149925101c0d80c480ca8400029485200405254030424000400c0b00c401c1c050350804400403507546503074905036000040c00c4c44101400042c3c0281d00e8041e40341482d0240209420390355002502290a401c048030300d5402c01140b02c1c66100c010b80104440c903500d40101d071a20342c04ca60b2500e00101d03402c4150b2a80303402400347d01d6005031a03004090600048a0f0305400558495000d00310001c4c91600031f02c1e40e8640c0c1c2c0b01c0c5100c001e400c2040c2200003004106103a0100c2d074042d01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 538286996 1250 538285746 538285753
    0x605180d090b0d14180c060901080121051c090f0b070b150411040e06010f0c110316060c02010207150219050319180501080114040203090c03060109321305 68
    0x41d008190644c0c000100d5000500d0313441c641d032495030900c04008925a041044d540d16140a80c1c8800003060321005014003100c03c5031031507807292135080206100d5007964100003517038500001021106403950420406a000500224003c0341c00a070782c0d80301c4012240d041e64003900d80b0001c3d60301ca80c80020001d04004151000c400c6085898903035001d0b10100300060481c1581c2c4600b0310303d03207a02210700641420304202c03030f84035020011500150219441600030354806061080d4100091500c1d80141d5000310891414000044041d0400c81c4c151805200341c0039204240e440e400684250811b26101d400140c5c000070044404181c2e00188015250280e016030b481c040403120900e40302d440c0780914500081503da10400100e046041d21400780c0001d00c2c02100651600c6d0032aa0000d10310200f175480fa43d40080855540d401c100644c2c451140b01409407041381da9141000c2c00180000e880d02882c5154107402e5800765011401c941d0030100034141540401d8032080c0000c0011034040c08103c03501e10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 538288246 1250 538286996 538287011
    0x20d0c031209021224161116031212090b1503160e04150506030c0906040f05090f0706020708120a0504080601141507020d080a03060308070605180d090b0d 68
    0x80303c5078513000a40d0a9400140080021181074804a403211043e2100d00c5402c1c40500c200481241c1410124400c54580050100b405a005d0b90070a071103014012404e001000001003002198030380395028605545841072075540c0c44421800391400c9140c01440c1c0d204810014412a00507883c404100001030200e80f04841c415204141c08103464009803031052040b030812007005124450f1240134503450409000d94102400803175552001658040d104036022800114161504c1e840680b0894085c0801e1045081a101d160b03296030030103c000c08a8000d4810109090317000051031021034a4480040000c03881035642030000f0342080041c00d00304041007000040c0030f0020444940079040611080c1f4440755104100315a0403420445007845d82014410100580d0751211503a04180c0c1105030242e032004840c40440051a207600010080040828020140880e640c050380c460b8035129003075600e0728815800326030785410182d102070010700c03450800d2002654060103442018482d0701d000c5080d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 538289496 1250 538288246 538288249
    0x40b03090304080106050d1e140114010303020105091506060307030e03190912030f030b0a090911040b09100317040506032410050403170c160602060106020d0c03120902 74
    0x154000d84100c0d1041d4804181071107090400e2107404000d1200722420005100e0a070f450b0187c0c3c210754810700da0901a00d46410f028860350311000103080032039000030441c424115100325500c16003030005030700562900000450300e84001922000030714000b5a552055a82c041c1041040d51004164104043c0c0780d0035843c158400400180c41e03084800759540b400900e40c2c0d0340042554555034804007038607a0114201e400300c1d0708143c50145850b018074000c12101091000b081104446600c5500540d10300100b02c820b0084407800e040a14000311020300c40e2074104e004011081005440d140000703420348034100001514030600d001c08001e00f807103036801c241d941c1c0d00040440c0c2080718500384d60003002e0000d4021140c021421010789004503401070380c2ca01c1e00d240041140c05940001090700071200c030403500860004003030711100c041e4802140c40304500b0a10800c00e8240e14401e1902610900d40003050781c030700200b226080c0700c0325a643c1031810402e0340c82c01c07101c0a008541108100c1d07500c03044140903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 538290746 1250 538289496 538289519
    0x603040602160f1101050f160203070302030d020a0b0a0b030d080a0609320118020d02161103060a0204061d0d05060703150522091704030b0a0b04020702100f0504 71
    0x242c6000703c484240314541c500700300500104142c81141040b9080003418098a203060a58452900c007a82c00442e2050502c0441c1c581481a040a03525108401c5290011540003d401d91291706c1500d00c0d5405c1d0b100c50440b070003a600000941c1c1d525400042c002c00141d4804c0504a602902c8810302044085d61a801c1c1e070f0032035103854107500104010842207005c4031111600041e421622885040e925071402101c4000c0c0c00c1429459041e880e000691903088819540640d0381220171400c007080440d0316860038810034401071011a01074045d8400083d41e418a502c20754080b600c840c0c0740d840c408040d20285034070043d030f490455070703005050000c1074010584c100311461240e01691000540c106000c0c80140c90301800d54403c61162440214103080b038034100005c40900071400802103040003903071070302c1000c01078a5001101030001c041800000d00180000702d90148502050400c9004160001d000c264490340d440030b0b4000d10190030808409124030b1110300032944d00d2801b00d0515440b07240c05d110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 538291996 1250 538290746 538290787
    0x206030c071a16020606090105060f0f030c031006080106050313080f1809010f0b07081e030703020706060509070c0209070e060c1c050c060109020d020409110a17090a020603040602 79
    0xb4202e64100900507802181121041c41180010401031504000142540c10140142c501806011614404002d1000255101300d4240c6010747e480c2c0c17401c4a080c26150704201d814501091002c1030004040d401104402c2c1a04d00542c1c07024070315a900a220b109120720103100f2a40084108400a0b005100201030540180610790f14a10407100d00c040100010703060b003001526920003030701040603161090895803c164450003041c1c0720041200040c0c0b02410100c0407150f541c20000030003004a9055000745902d911495041001035111024800444805c0301c850000c0f0342c041010710f000d071405c0c0011983c064200d181039003401c00c1140205003542c0141d010054680e01c50840c9103480c0010350200c501d030319400c0c07030443d04184181654580d5150180f150300c10160740014000c094101c5074040f0381c0680303000c000500800821030303400c0040781e010030032000005941a081e400b0140c0c0c2440c80791301402039800142000070341502000307a0f0781c0c809041107400c80d90030804002c02640c600c1d0000c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 538293246 1250 538291996 538292033
    0xe090715090302131e05010807060c0624080d0f09181b051806090d0312060f06050309100c050a260103080a02100213060804050313030b061207030f0206030c07 70
    0x140d108480c03070305c002030426490310b0b181c05604102c01405078400000322982225a24508103103095440e0902100a14907011130700c0d030034900283d5604010b210100d2000c210341044c0300311069031030543c4040f00d24801075450740c0000f407100e9100b044022440c0a44000c1407498a50000c0c04890710400c02c40c0b40c06101842c103002ca44045800c01d0740385d020f00041000c140003075030010b1030104003d00284a6140d10140102440415010762405042d1a88110064040303c290403545549030310010700030350001c9502d000c83e0b202e0b1480c40c04141000c1c2c01008032645075a00c40f182003030b06048090715405d43d4004064010804804280d03849289080310500943c0207110a5030b88208140000341800d424007462044a4010002407a61b8060000c4c6001118114034041c10140c03600d140007811441785d00d4420703050b180d229201001f40603034030401c1d5000b00c0d0120b440003405152580d2203911143c0c64030002e0064002d0704140c60250401d480114dd02070001403009240245951380c02c3d42c10325103003d500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 538294496 1250 538293246 538293251
    0xf080105211e06060310050f0a1805010513060c0e010c14010e071701050106080709140a0308030709060917031806040317040e151f21090506010e09071509030213 71
    0x1000b142418000c0d03448441c03160605010f40e1408d220300702d41c0c902018021044045d55000c0c550b4045816107040d2031240d0344100203202c54200680030000c1c0c500b18001c00d0318a9481c0100c0321101c6800b4a07a02049180d06850b8140c40f501c0703d807562003900c26800c131511400e54035100c1c4200c580e24240461405400c6d809440340c10a405240150700f1610141c0190003885188024086850341140d4040101c2c3c0600c0048188440300c0030100b800d6210990004122050120600214580080840042d1120b80e641c01120b04e6030340030700640d5800c46204030302554008015010002d900004282001034010f040d240c6050354a51700c41c1c80c0038031200c0f00072103480c201041c1400031200d00444180c01148046003900c41d21800030010f01070a420801c000303588040000e255480e103008410528141070b000481c4d40c0c07084100d0812102500d42913008640d6401124004520700614108240c09078402c607000b021841d0406440040208800744941d0034408154070000069480b40e030603010000351400c02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 538295746 1250 538294496 538294501
    0x204022a01050703060506030412020307060501060806030c1c020112200403060b06030c0906180909010b0103050a0207080306120a02031e0c01090305060a0908070b040804060f080105211e06 83
    0x40340d0031510040e082c1d40806040440400182da40c50003aa908540c02140b02c100e0715071100c4d0b045c1d01d07511491030000d2885081c9000011103d030000e0f2400d06c0389200398140e944142c003a1040083c0c80394424106090038030740c2c80c03102c0d016521a0560a10401d02000c000981228803c207841200c5c80c91036401c5440c0741c0000703040c420030081d801900200c1000740d131407070308506102194518a01492641c18081c110210344c003e8040d0740440440741060010340368904504000003061f018100420005002c00d00308808501108942e10807608030703030740198a203821078680710204a010b11144040b48000d1285290385c07030240e903081c070800d042081d041c21703c1e0400240007101141810200020745060000e264010404540301003000f03940100b840d50001131100c0e0741e11b0326280c0350190503c081c1a20b180340d000c0104201c03044000380705966041d02c84a0148030703240300440310310800f4040c954204540c41000100b02c04c60101c6024141d8540058680507002c0b003480f0700d022240310340706401c107900540c103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 538296996 1250 538295746 538295827
    0x120708190516300b0a0c030f061401020c090408040b03190e21130902160512121f03030804110409120807020a0c05091e04050709141909020402 63
    0x30050740f0710480c4100d12201c40050310b0700c00705041d00801e401c81c51070300c58011089842c445d0707000c50700720142e2504c100040c0c1d4a84e032001d1300511180000b00d004d407050a07103c90071880d001c0740440c811070b44640d01c039150a08002601c1400d4001501001c00761500c44140c0899124502494008244040003004228408055080b8814440061084038081008160824080301c4010415a0310f16000960b035004020748554615901610141040c011010800d103102c04000040c80701c1c0940103000983c81d11802d052013103c1d404419070724200c550602c402c000003400382401e194064010030120010260690104082d6a102038081f20504952075624808a0304800d07801c3d04400c20384020300c00d0055541c3c03461051080b50040910551a40c0d0001d02d01020913203460f1400b00c0c81750800100d0741003d1500503503441c514020404643d00308800110b00c2c0d200014580c0c03040d0605813446203010284103200c401000c000b0800d0782c2098003000410f400e0000801c0030052819a0f00c1505c4501c02244c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 538298246 1250 538296996 538297049
    0xd0c061b210608280f24020f190905030a14060f060102101121100b0a0c060b0307030c0602070e010803070c03060b010908030a020307060506090f0621011802120708190516 75
    0x74894002501c1442004d00c203040840c1540d02022403127009010a004101c1c0a942c00c000c541d011a41c1840352080001c20002c41c0e450354000c00e40000b040b25040d840301105421035640440301140168004035040640e03070300d43d4010002005440c20013520301118102030032a10070a41b07441400343e6007400c05005007441941c0c41200145416094a030a180b03080d08008c0010b811075201030a620f85548842c42265002e018500003564800d0325038101e180c0d00c0d24040d4940c11036215282c0c59015403400011207440100880c0c1c000d40c0e026114800c500d0455654100900e50b000030641000400400070030142e05c00c000500c05041550000c503140c0103585040c005550009020358016150001481700082c140030301d06401690449101a90384036200010301c0200760a039000c1e00c01e40c00c2c1800015003441111691840398020f88042d40040400c4682541d903c00d140300319504d950164001d9801c8a00f20700f03a4640140c421000d41e40704104c40d103000303201216540c102c44e2104244108124020f511070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 538299496 1250 538298246 538298303
    0x30212070305070801050f13140f0c07020102370b1f0f0303210501030303200c070b09030703020a09050105210d0c061b210608280f 58
    0xa1070107000030724011000410b00c100601c42d00c0d00418003a10500c000c1d40d0340641401c212400910208007651040d40d458621710400c2d0342c10301d040d600c641c001c1032a0541760340c12107404c690103800410b071081d074880441a030010a40304c415010469030500c0d109001d45220200c50150040003140c1050410410000200f00b10000c40e06040304031800400100c441d000d210300807241c02d8103000c0303050003240e6520300011581c2c020140701d1502e80800441056016808404241071100803e140c400003803000c0300e1a44a100d460200303a03800100b04000e0380c007103000241002900502501e0003d50350b80d01041465001323412080c48680c075680144841c4c200368022400c0801d21411440c458003070401da0a4841c0c0d03501c40c506042180e05585e2009020580e0400710207070940c120101e40b003070700c1c2c0800200218824160f100b060415a401031010074402c3c0541400d0720740120140c541e8990450307000d020707104030b203141030800d400044404020414040c61464020701900d003482c0c02d40f01d0340c415440e0f041d48a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 538300746 1250 538299496 538299511
    0xa0b07051324320306010203041d07020601140102030304230703141204030312090809060c150709050a0b0d27260702120106080d02010b040b03070311091510030212 72
    0x940880840003000c900c419500f0144641641c2c2d45131040101d08622035900305040e03007940710032142d0a11520b4042c0710b1040c480356082d02d90598950800042c000303d03060806006034020700101e00482e0440e80e003840d0050314050b81c0480301d424010a242402103662064961b184401682c0543c2c0c1e5041c441401e50a012600702803a00c1d0440e43c01400d140412010000e510341d85100350700c10001d41e50704403220558002c026030340340c1030100a220354810300c078154a98107020050100700c51500405600003507900c0100403244050519400c090039812a82203018661344a046031005688060520380300b505000070342d04005983d6040c0000a8000000540403046c62109001200300c0c40809a815852b0f04440e4003016030701490400380548516000a40940100e10220f03002d50740541c444040340006840501114445030105074840400f440041c1050201c059610003a15201c507005500034000403200003210381c06000f1907240440e0b030b107040000c2540017a82c2026502400c1043e98002e40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 538301996 1250 538300746 538300787
    0x30601020a080d02070618020f011e050c0c04020a02160e041101050711040510260d050a1106090a14031801030b030f060a060302120a0b07051324 64
    0x140100000c1d0348044070309019040000200b000c050302107590301242c1c845900141d05000840d2844018840380f002c0a80492082110500042142d4054201d0307440151964110441501031180c00380d0342940084941d800c40e006200c0e05000d1035603244081c0c4440350042d40100307080c24564000d01c1c041c10481d0045003900c8034013010080024000300780c64518003402c1ca0071540b110b10a1502c43c00180405801d55031160030b040411448802c043c01c400101c860454500264460a00f40c8c41c0210f000401c0c651030503000b2079100b440d00d6000360010aa469076500c0c0521611014204160500f0410b4030103880035003000504000f130205192044c4002c800c40400345142140d40703e90758060383d846070801418591141e01220565034140f02c501400b0314803106a40080c503040045400804080c00100e22441d0180c00d202d00702d020000b024005c0650280800f0540d85840d0400d03140d6030001c100c4c003860900406404070703180100315a00040b503400c03420400c8c070700c00c07503040058101040d0000100d01c020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 538303246 1250 538301996 538302001
    0xb131403060c090415080105091b0a0501050706111b0a061104050f091f090902100314221202060411040b0a060c1505010312080c04050f060d0902100f020c030303 71
    0x403502800c0700c2c400d480454001503540000324401700139804c268008101ca500e00410400410004201c614082060f25801c0c40c00d0810354040150b0f46a103802210700141040c00440006041c0b544104442490000d419050180c0c3c00441b0f03a0301800382041c200f240d000b030012402000182d0003081c00c810140c8000134149420400811015450400040e100309003050100b030510403411520213000c041e024600c44000d4803213443d400540a9400128001d81c0300105814160748640f240800081000d6204405926400b82083d06000091503100c5241403150303071800014200c440030100d006064001c0c003036610702401d020850220301400030340240d0504e50b11a1666403401c0c213040a0703981c0e03410f00b0090241d4038140800000b81c941c01107a486031401002100b0b2105070340f4203040322000c07561141426074890032501c5850095200f03081e00441c581050b1101d80c50024003030150b030900014009030072048e90b00001c0813000504d0000380442c104000700101c15a050104e007212240641c001c51450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 538304496 1250 538303246 538303261
    0xd080402062502060d0914060c120c0c0610030218191d06010b04030b0702030c0c010f030e01060609050f010206091903140c1e06040c060e0a0b13140306 67
    0xa1107281c4107a40215400b505040c03480c060324401144050300070348000c0d21404e036503080000078001008156000b0b4102c4c5920355003020001029881200d0018030242891600810000b038954081c05050884c00d0502030300d90310080c00c00101d4817903184810f44181040c5103005002d10b9485d00f05080110056850820000c0d4000801c03210ba040b41c03100c800907103e0b20202914076400c102211542c1940584000000c0792103414001d4801d40780941180c0f440c42c1ca500c0e074240c1e80ea00c52071060000c030381c01c03c0b01803014540c001e1001392082421410042010f030045250903084a0190b0004c0011a5095009011a0a1150000c03c10520030300007403c1505011103010765451444868280100c828090b00c41050b10403c40110351407862406d036a25510f1542d0103e440b100d0100340d10159158078448a4142400007803a039001c0c0c3e400040c19020207040402c210740c184220702000317822910b00d1400051407040709000305640305401d1600404241041e014003110079030304a0062181d8086410b02001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 538305746 1250 538304496 538304509
    0x310180219051803030304050a05060f1003020d020a080105130c0602030702030c0402030a150803031e0403120903110304030c170106030314210c030f0108030f0d050a06030807050f0d080402 83
    0x1c0606609015488445001c040a41042950324480d05070101206110401c000003d6250642d48075100b80c81641d96140408906031204070b440580078001035000b000503081c1170004c00302e0702e8005402d8081c1c950f00c900d042c50075924141c5030600171444e80010a814440307072140300d1000d4046480554900815500006e03a1080a1344506115070ba0000108922980b140e0008078501034074142c00d180e0b1642c8090030b80d2079070000c4540540c124503002a62071480c407040d503072521a07941034890704011440715103200020704d0550412000e00081980b9a50b400800300007801c01507204041c0343d00820704242c0d10360f00a00c45061480d21903814100b0500c0000d4100900c50880496690041e40780c200102d803e0f54098002d9103c1036884015105020030b4040380d0009511403421101500c0203a644c8a002c00c1e034071b00c2145000846c4105c181f00310040884541c00c45900200040004a4455201d8488051a900c4640c044605502603048050403450030711150120f01030905000c0e40502c1e254010862 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 538306996 1250 538305746 538305787
    0x3040f090e070f030305040e0108060403050706050709031b06110d020a02062b051f030210050c011b050a08070905030c09042a050a0b130e06130203101802 68
    0x3810752560480410308804000078401805036880c24002e607581c0c2c1c01c02030081e6001d80500c1c1c03108c03c8000b0000c1400180001d18601a543c50354400e031034503075507407110401000003605c1700040cc411005c1c004041207907400103c1e0382086920010302c1042c0b170500083c11100785a511045503400c03c0044030b95083c1c0101d0300550294042e03070410742d1a0701d8a481d030140712414400102c414110030480c220b501c415640240e10a00c940780e20040001c0e042c0c032051a0500b410b100085d17222003248503045078a03105030f001d8000c5d20207d90020460f500d66081c01b045407403880201c50002003000c01d20110301c591250080b0342264090a129040c00c0c10303d80480d403103840a50b4518002c50321100030404000074582e60350030800a135038450740c00d500850980440c4502c0c5218442c8600088100454545081c03411031b05444a04e0800b0780e006071070119090382041004001c60750001e111401800701011038002144148029500c403007003c5e041144070001d90300191004030042d841030092030084031401000d05c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 538308246 1250 538306996 538307009
    0xf03070501080417030f060f01081504110f03150907090f0605030c12160206011d060d03090b0304060509070e011223030d0e0c12100b0102010f0513021203040f 70
    0x1030140e5140d040c00c60440c00020713005a05288000100a500844e90030300901401c411205a2072010250004403207884041c1c5400c0034903100000c00301c0403440c05510040c0070800920a4078200480c00103801d10301d8000321000070441210b0b581e4880703145000c3c507510341c1c0228107041140c0034a0404059080071082d60081c80103104d000004280804281c005844584a8801801c100f9182c284c0b0b4662210003601d1100015120302000807034102d1500c1c00c0f04502c0b200c50150051180d82c1c41c0e040182c0b0000100c0240c090291005001c6490b180900007140f0441c022400030809080c0b0740d100300d2501000b94401c00e0140d90280040c40814150229180f4494100308004020a804c00d9600c1000e100d18411a80d68400060980d5203480ea6070001c40429100360182c0d500340c4100d0702401115080d15001020940012191440300b01450388001c005007010710000440c41c541d004100e084400c103654280c1031000240103a004c620300410400c205000300f402a60602e86002900d10403103d0314001c1c070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 538309352 1106 538308246 538308257
    0x150c090405010819080904060902040b1308010207030e0f0118170c0a0807050907020114132906100c0501052a160303020d09050f03180f03070501 64
    0x106403000030b040c00c0756041c800981c1c0301d40ba1580400d1403598010f9a40c03401127400c0380d0a20180c80580550240c1d103a07a0907800c2c56103801466240d02011a51380100802d60000c0d40c0701d01d0000092409031808200c01e0300038001a10390744000384184003030307500400f0000358241d402c043d06403803031080100307851340d24000c0c00c2448036030042c5000d00d031200d5024120401007420b0bc1014254000c045200000c2c08954402401030020f00564000c05410300ca1048032046c03041300440101400302d000d00030059003101003e1610040d0307004001d40d114108100d01e158549000718060003002e940040200501c0c0750a0b1751401c8501501403078004d10706c1c0c01c81c10812102c15800110340101010506200ca00401603404802a61160f600d00c218551108078504c009401040340050b50b50311071020715254110001d0000510020444243c0b048151011818058401040280c01d80782e00b031804 = true := by decide +kernel

theorem cover : BRFrame.Cov 538129496 538309352 := by
  have h0 := BRFrame.cov_init 538129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 538129496 ≤ n) (h2 : n < 538309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
