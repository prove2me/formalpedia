-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5294
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:23:40.633194+00:00
-- url     : https://prove2.me/submissions/95f6731b-b795-444b-ae3b-7eb4d09f746c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 951978417 ≤ n < 952158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 951979667 1250 951978417 951978431
    0x5030316080f042a1806060207050607030c14010203010e2a0d020a210c1803020f240f030610020723030a06141006030603080702061602040e061608010b0d 68
    0x10360002e608901403a010000010840054404225032003840f2404001740305110b0950b0360b8105985483c1e0034403425802c0501084402d00203403044040e003445601c600d501140490340c60804608a03042604212284000320341417080010411102508503540c203020300803d019017600f8010a401002c14816041c0e40201d14825114014104444900f1500a4101c400da10030030642010300315113110342c008186030351301141003200107243d4841925009000d45040240703460901c51400f12100c050f0808a5480081d014880030382e0700204038064ac54006a03841e4140141001914804204400250343c0100020040c00f408010340900b8558407940c1200c05806020129080141026006040d5858011a00100109a2a03ca000e0200450342c100015162503040e8116200c501000e049090144041001458000010405031200402009020506601142c1034900040039568284c1000b400c10000c5060034500040320fa95924100c2940d503d4407150300d40038400d441646882e2915801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 951980917 1250 951979667 951979703
    0x31003080c0f0a0809041a0901060f021204061e1106041217010e0106030c18090b0f1306060305150915030304121b140f01030b0a0f0305030316080f04 66
    0x2034006030b407910360103850500342c4a1400c481c0079401651440d01c0303680384c86d860804c005004a02c10140d101301403c0c8640c182d0074200b0a8580c50300d541c03403090841c031840540300501040140540003c210035203e00c0c001d684003289040041c0a5480d0f8a000c014075058075407a42e250000d011130300217400107e0290a0b40403c00125400304c2400d07500302800d0300e51400002c0301d00420003254100d85403540d0400c20a465a03808860070110122041b01c82d40b003210007407003c4c079006d1f4000d07550b0410040c4040b29145141010409410100419403001c0d40d40341000c101143c7c242c01100d902255107807000c804a41c0580000e511510098040041000f403011021070030b8508000f00c4000c0c01007406001140b244615007448206511403019410114800700001c528580ca80c83c0c02186200918450841245500460051004118103540b003d651900090803046011004014501031800341da42c0e4036100c6011030400341c1d01e4001c3d9007001259810418240a8103000981081d409061040600400b007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 951982167 1250 951980917 951980923
    0x71b140108060904113006160801092c0a031710030803090c041d0c0a060f03020901020a0c0f060e060903060606031803040e060f040501030c05190b070c1a031003080c 73
    0x1411a00d02e044103041140c6840508003d00400301c01070741b0072244207030707260f90b810394035a110145d130400031809400042c0120112608003e0b00310880c01481c0b120842c60b10b05480380d40006205220441d004814032809051780300c20b448440c0c1d16a42e05154280c20b0182508901e00319601c00904808000b20100362514030501250b095001d0081c8240051100c56240078411300300c401003440188030724141070403a0706054002a080740c45a803204142800c21005c19800782d0300050220b41140a500f4000300060b06410841c009055410b060700c42e03040c14104041c0c4024991940c5900c14481802002407981c0e000a58503400300003926010340726140d5500050743c80c40c0851070207205000104000c54940007003081c0c284511300881d45120215a5a014401141c10a0001406400240906010314140181c10f001c16810014142c10310a9851101d00c206401280c002c59540c0c800d01010003030000b080da41c41c00d041c1c0c0602019890b506241c0d0b41b0b080a00090300c001440b241000c6002c0a9243d424 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 951983417 1250 951982167 951982189
    0x302010e01091109150607020105070f12030c0210200705240a0501061706040506010c02061c060f0602060613020c0a05070503010c0201020a021e03071b14010806090411 74
    0x91040000a240c8445150451000d144c0110103c1c000100001c4050014076202034000c0c01e11450904142c004686a9110800030b5903c1c50003c0400070000710382c10641042e10a50703039030029015100400007410304a8035096045100c0c00d102e00411901740d425a0144040c503c040f04036660a82c92610a090200c3c03a011411031009a80c40c1d150b0010051a0041c410705c00700c4403c10460781c0350081510007407010111070004c400c104d0001101401c2690025410007030504001c041c3c007035254006415507004c5803014903001c40300c8000d0174270500c5502070b8001401d800c2000c1c7c1c2015041c10384c001e55584000300b2251041101c46100c07103100c0300d60350480d6103d0b11541e059910f01841800d01c6582c400c3e1610849003c2d42c0781807070421400e84184240ea134810425809440520850542d215072100700000803c0c46020401003200002e40d0804400389148510010281c102d1800980d5640c039070410907082c0c1849014010803a00e03135201c0503a1640310303610040424540c007100011450203d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 951984667 1250 951983417 951983441
    0xc050d05011116020a0608040b041101030f110c1c050717070f0602070201020c06040803090f1f1d03030a05030712090213060f090e0303010b030c0c0607050702131104060c030201 78
    0x903500e0070b50f24039202200c545030098030001d05690352004101d9081100700c2d009440c2c0440603011a0003e0000c0d03407280c0d07012070140350101708100c103206070300c04a840170f22241c00c4120000400e10f2010806100401c6011402c0344801d10303102c802c4ac00038207507100f1040300401404951030b4120789004080141c8101a4201e00008900e90726131415200a5221801c1680944074100810210745401d00885040d580b1150107941012241d00c180106c0ca14042d50302ea902c9800510ba1441000100d068a450f46103241e83e9520040314480100c50715074528041180250010481829400d1308181180e411242500d401030030081020740c400010040c0c020000c1d4020b000c10b051511850160300900180c80c0d082c294800c5c40c96485046800311901000f10202a40050004000d00801030340655403000d804102c05250030751042000341024821201d001c0841c4000c02d0010030f41c00c041806007601e000c50081001891b4a502542505009501c139a608000d0b00e40d1180c0205440ae40048041e111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 951985917 1250 951984667 951984701
    0x609010c020d260a390c0902030c070b0109050c040e0712050702030a020c0a03052d010c030f0f050f180114010906092d090c050907080406050a06030c050d0501 70
    0x2200d046a40201c1c41200003402011580100b50f05c46406000340700c40c03074200c007200031807a038422005940c04148207880b2800500d2000034442020300042d032041d100c0c0282c0c103a0340c800d50310344500405411380016200318589000c000240b1400c2040310f007920b800c890b00c00c48980d20504201c0700461041400c2c44500e0803d0140061a6000409414201d103250255052480401c050100107c2c0500c0058078540c04045403019a81d00705180034004400030f13011004000c02041a02e007907501090b00c1000081e642c2001c00e4550f0715500c80c841c6503500600c824011410320131000c43d49100b010300106a000c0201103020b048a001350b20561b040144612090120340e951003000c00100401e1151030141400d2038809031401c0480c114100403400c001000071215082c6c129078100030320a500781140c0c140f0881c4000319583d0740341c1e51310710310a1000e0f6960500c10701c0e040c5840030580e80701500c2120300f141012014800101c150402006560007580c1000580c071884c1003607809026a0368000c82840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 951987167 1250 951985917 951985973
    0xb0105060f07080c0c0f12120a020705031b0405010e0f06011103090a08060108060703060b031504150b0706150b04030b0a02092214011a0c01150617060609010c020d 72
    0x32002045c80030203444200c0b154803e0842c51000e20140182054100074642c00090382c1400c0807030400060440030358075104450382641c0361720101c0c0c034000c030284120500c04201541c1d4242031505018035400f41402e119500254200141902c0c04140040c140c581032090941032614255001c00c203aa2507070400030102c2800c1035072401400c0c1c4860302030240c18210b004040004a440d800f038000d44080b218258502c5185658007407400e03c80d031030101001c981c02503c0e4940d20b0304139031005002c440503000100000c1d54070006850004c00700c5814194039a1140120401001814202400d5408890708183d5404a0346d5840d40007400a228010540380d104c80700d4484480c108150003c800814000c101080140c004403d030740c4480d144e030900c06d070006c070f641010b14a0b0111a040c0c0140c050a440c1c0e07000803840c0e44610751a0070a44840743c10100000d001484103a03c0020300345041074000c003045d00d40501d040c00880000307110020345400a401440d200c18003000700710741801b1071440b00d150385d4600e82d022 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 951988417 1250 951987167 951987187
    0x18010e0a09021e0c0a0b0712020301090605040b030c010e0d0f020d03020102070314090d020f0301020d1b0f03060806070c0c0810020703030c0f17090322030c0b04030b0105060f0708 79
    0x7500015640c0c41200c0d040c2072055020300c02181101c81c8401413000810034281103640c0c5000ca0704c0000c0c5103904220840145124880e40c174000755000c0c048000340032821605202c107000031201ca0031099840303a40000448034441e604401041100703a4169141d80712412541003a4501d402c1620000f5006129030031220306044e81903000d040c019100f917662502500700e9120b07401c1ca43c00303485450b5600040c50003804005140c07031078210406c010081c1c0058140035420501c0402c580340003031544001030b1442821b0417016030028001c0c12802450a0810240382048511036445034010b1900080c80b201e4103414080c85910100c0034006c002c80030444024094215408001c0e4100c6041103020a040602c0503803228041c103030320068440b60741c1d2442c44114400c04d50945040300982401c00c0303804100002020107101c9558011050013503100341e18a9071035441d0281001c03200d9440510000000c1c030060002402d0281080d044450898240341c071032400e2182c00c1c00720310503078500030403564002034600a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 951989667 1250 951988417 951988421
    0x2041a030f36060103020f0a1505071a0f15030a03021b0415150306090e0d120609090807260f0711040501060309021f210608030403050f0f0c0618010e0a09 68
    0x617244241c51454201c00041c0a21180c140c0c01d0140a60201c2c0c00301c80c0e043c3d140d1050010303201890003681340241c3c191b200c0000c0d0049a506503400c10b040e800c0402004006070420009400d07030b10041c0e004002c0c40301a618000d4940011031110700401400000b00c0601340c0d2140c0109001048010603600344941d078281504074411700c0d40148010900f4190300090b507083c14400e02d0051107140c0b0240c5884080c0b00c030111100c0c03c10007000d44030b840d9280c1010810030f121344900f890251142d0301c001c4e0384903498204040c83e0790b114007500e04040d00004950502e800240e082d038142c82682c0041584501240c5000700031000540501da400c240ba003c00001c3c681c0d07042d00304008030340c000c2c0c401c0100d4281815401034605c0401041c3d00c040350604a01e44034542e150382030b40100311507040300010a00e4403984840c1c1198050382c81603070729610001c0e000044007010311202c240318140c2030060081c0704814020a01d00c3c000c08a00911309101d209100305240d00a0014440400d0003c280c92000c503220700c0c030040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 951990917 1250 951989667 951989669
    0x30204050c0d060f030b0408092b02010e0a141522031e030905060d020d0903020f16151d031c030614090a0b0d050607020102041a030f360601 62
    0x340a8241100054142e18814940f415260800d01b0002160303101e8490070103e501100065422507084203240401246281900364001c40c16120004102442d0000624899141e070b4082c0c400c0b420345e01d080059a1070007030200300801090b00c840300342d420381c41d01c03101741402884a542c0d403003091050b00c02d80b030311621030000c41620700c10042200300442c1d10700d420f0100c40d2400c00003808034102d44410b11462400340c014201c4620745040151030030400c1020b00055400400e011000f60340030995070f00074102c080c480c218252201031600940203141c05801c4120528010701003082c0b085041d0341c070300882c114031b02e02c0d85000d4000c5c0c104e07031081d111003003103894032101d1002c1000060310b80301022034010040c0e441480540c1008100e15419141da114280c020400007080d40d034040026071820340002c50a02c80d11b88280307200d8000588482c540303990038400600c200034925a443c0100104850280b101c800070350803c03062480c207482d248250417840c400301620b540d134450a50010b4282000040000340e00c3d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 951992167 1250 951990917 951990937
    0xb04050f0616110312072111250c0501030c260108070b0423120714130606080703090611040801050a0e030301031e1b0305010902240406030e07030204050c 68
    0x5100c1c2d070030344a0340c11303102c0c0106801d1000c201411400b142c2d08611410030140a1211050003203104224440c00c50100c80382c03003c00308204140460380300f101c0b01c0680c1021410403407203101c600503034000e60303580d00322408103009036414140d40759000304c1c10910039102e020024890031140748000e030801490b00301c594804d1040309181c1c400e0315804501c64409609440031180c92500c034a040a080d10b16440c0c000780402101d03a0030030340b1041c01402600007040040f00420030015503d456900c0c10090240d15600000d0204915041a800300b0140d50b00c25400d55001304070b460001380703d4101c0e1074001e0240501113000034a100022802062050040d44454014460343d0000c0044000d082a1aa1640400d120241c02031405c06800712807103c816100b103503200e204003c441c00d00002040ca1545d48821900243d9150399a80303c11011801c0c1080f101082a03448000c9110140c124400c000051245000f120101616115480f0030343c5402c1200c18091507009005115528290f181a00c00360030111940f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 951993417 1250 951992167 951992177
    0x60f130602040803030a1d0c060f07081c0b0102010b1011070504050109140f040209040807141c03140103150f0b0d0303051e060306160509031006051801050d0b04050f0616 75
    0x884038410440d51507c000044000150421007104400c0240a0f0040d017070600034407804003d0140015100c2d4014641c00c0c1200050280340d40c0544415400c88400010085c1136a2400030b8510302d41d0b070380440002e902e00d42450400102c84814980c50705203440c40d88a2a0850305002c0081940486a08180c0300080601d0300c40d02036603900b0580300c1d07600c042614080e4018454101007404601c03e074004010003030154500c1d2140400c0890854504104802d0030074011044500c0c0020b0981d040c025040aa0710f40c4281080d19411502c9407064481d0380021503182c60ba80b02005062400a0f810040801c0c00052400f040c111107403d0103006080103d817024410400000401545140079101c0c2d405004d016004100329515500d0740055481d000741c4003000d20906101e0150180e0307003006007074400410002c000c110607150005000c1c483c680060040c040380030640040c005500e584062048071078007c4071540c210b0f281c504205082031100d8041008070300540040040c00301400d60b005040c40300e42da0711 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 951994667 1250 951993417 951993431
    0x10501090b04060f0e0603031e071416090b0102010f0212062b030513030506100305010b010509180c09060d06080d08150f010e101d0409020102060f130602040803030a 73
    0x204421510140240801402404001e010840950411640c0564081c049a14007002c034000d0051079000c0070380c40303804046d000ac0e882c0108030700141643c562803802001401900c02c03409803080741034060b016440416a54034030f44a41c0d80e1003500032a0140300903160455866051803142411600100c8d110b03409101e0900c00000d04c50035119503c2c1c00241c41602c1c08200421075503040385c5ea5400740c000741031060f24860010004c11814800640241e00000d1050b074103034558605242950b445803041070521005001c428030644942640040005403090400c2481c0e51301d0008401500540101d9500084041180c444580c101d900550a035a00c0c2d004885c0740d0081001e0440f1000d4049880081c0e506111390000032604240c400c40415020506001e00000c1c0500c02260181c000c04401800003a40b9030340c3d400040c1ea0600c0b80241300340381035078148801d08654001035590000501010b08cc249101c0c0000ca0300c0740d403140e0741c9821b0382d4040419561907940300c1c03040f580d981040e16400700c03461078104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 951995917 1250 951994667 951994669
    0x2010e0705030316030c0c0302060a0e13180f05030415170f0103020d02310204031e0f08030901090503040605120f150d1112151008060c0a1b05010501090b 68
    0x4192000003018085050302c00c4116541101c00c41b010f10317412510010603c0c40400186c0e1480b028000e044440c0d07071503001010300a0100101c043d05150500e0916180100d8140c009402e04907407440d484d04002000c1e2281c50a19000e881c2d441150b20800c2480002040003030041e601242c407803003a0900c45117115054488200c428090300c0d0a02c0000d601035643c5005100508000100b140400b03018003219441c6400444e668907121504078407102501c6d40003809104000411450428242d034840c1e001c0d0070030100f6034900e18004460758014120300e00100c00168a540c09420100101d40d0000c00d42e92260303a1800c01a249801440080c0340704100740000410080001c0c1003e8410080080b0010318140c0380003c1c44400e03c01045e05644500320303c0e00c400b56a0312682a412240c4000b80001c0111502580052180303da000c1c1000c420000441c07410441503d0000301f0940207003140c1c40e1151390f103401c0d0b20b00740c480014074695550380080c0c03810100305205d819400141214134501d010722107002500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 951997167 1250 951995917 951995923
    0x170a060c05031015090909030e0405180f070b030f041b062604050c010f051201151b030e010f0908160608130218040212030c0a0302010f060302031c05041502010e070503 74
    0x8182d000008041d17035410000071110b81c00000d0301c00d02a0038102c40700c4030f0000105090755003c0741e400206101050b80c0482c0b10780100300c80646020804040d08070703103080c003580160910000d1308840142c00b0080200d402d00c101581114150144131929000741c079541c900140072200320300503d401080788508145ca544201d503800ca886158010050300b061500e01c001540c0d6004180004420080184900c0c20358116108a10f4041c0010444003e000c103022080144102c0b0000840c1a208998140060010380c11209035050f040c000d0130f1007520344144440071034a048255125080305c1c03094038100302402c41310341000307019aa1180c1d00d201d401d68450004c001c4008920758000c1d080085512036a20174848002c8080c1c02505c000c2c1101c094141035845245980c000302c0c2181081d80000001d0030070503409205502042c4070060050110501e13580000340c544c191224410706510301c00d500326916510500465015200b40c0d0180c8804800c6504024005c00c01003c2621aa115501c00407585145c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 951998417 1250 951997167 951997199
    0x1e100c1208010b0901030c050c0f011b0c240b1314011a0d150b041517060609060c0c1905180126072301080f04020a170a060c050310 58
    0x1c2d02000d132400904500450007081040880c104108041c0000c5014000c18004000e607008208008580c680091000c441050004d50085080c062400010400035000041301440c03003011b80c2c0004801c00c000704802001c0c00664060036441000483e540c1500c0c2c241d42d00c5040000c0341400d10f02c100743c1e26491031100c90505400c030184901000d012154000703640b6080a00c0c1d056a086410580c04c0d40c8080e002c5554006420400c0c406400b4103182c803803603500c40c0840c20800c044503440c405600b045c10214585101b1140714901039100083d100b55a02c20410110001e4003000d0304500c1c0004955600400c00251805400d2181003010598000303a14501d0100c1d060300d45514007a00540c180c5c000c7c505d101341d1102e12204107130150301c000280c10300046009240024083d18900c001905041c0014070101c00100300040d045c503100e040c000540c884141c6901030350784000400d41690322141c8514039200300302c800141000d003003d40581000350300102a600a00700c80c240c1d54034040d21104034150020301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 951999667 1250 951998417 951998429
    0x6250306081009110f2b020907030c08100b190c140601050a05060315040e24070e01021c0e04020d020412060b09041707030c061410050d0803061e100c120801 69
    0x440800910819440e14040d0340d40045940a8182d00c06d107a010449100c030495500c030101e603407062096260354002c044154422611501d516105007060908001030040e8038200d80c4084104042e10421b81c011040c091907076030400c08885029941c40d00c103039607a034024050280691ba00b5280007030b250034000c081c2c0340601207215071110f1006214060000a25140e5070700174052140c0c0c400c00f1031421a8031340d4400349080d020b0105059140c01c42c1b029001c142c0c4400e0306070445d800724030350101030841c9006074400400f0030f10b000b82d52500c07200001000f80c0a07003004110028400500028400c24104080c441117224400521030b030300503041084842c4c6012a4058082c4c18494950b500c440304510043c01d00901c0ba050001e09280f060300c0340c004560141c01000000b4040310305101c00040d01c203090030014002107405940d00c50b20390743e40c8201c900026080c1070260f040ca6044100e002100e142103c078140018200e02e50380c0c4030481004161007800d0906540080d50148034018032889403010a0581d10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 952000917 1250 951999667 951999679
    0xd14010c030606090e150627090402062b0212060307060302030405070e1e0108060f1006210204050306040b010e10062109021c030201050906250306081009110f 70
    0x1183c010010301c6174800a0441c2d40c81070001030038182c603903100c0000d0074078811440d02800c806031105000e02c80c0500900d100510400c2c00004200c01640e9601c00c80d50760074100f000d1000005060420281d102000342c1c1c040300c1117800407455540d4100f410000310310071401201258803007503461000f90101d20013900e025240303400c00c80d000d0240b5012101c0564100350340011003444c881c41c9410250503034500382c000c88041c0c7c21090502c280c3d555200899600322130400d5044e01301e070f4030380703e005032141181030000442403500d030058401c4000c4a0341900e000741406000c1c0c0b80649024a000080060300f40a0703047e07050070100104002c101588030200954940e51951000c40844d10320b40c1860381c0d06056034849560b1079021100060b00d6114185800c02041c1c603c1c80410b0700320b46070190a484008168051a500800070801d6509a000d42c400120035081094a10b6006188044002c2c0c5000c0e00441018418150307182c40c071f00300e82e0780038803040c2e401111030007199203017901000071700e5845007000c50b4804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 952002167 1250 952000917 952000919
    0x5060a060c030c0c090f0506100504060c03171005130e0318040912030c030c0e0d1b0e070206070e0117010504110403140f0106050a1518050d14010c03060609 69
    0x10303028074007001425000b82081140c00000d0740d42c10100100c01d03000f00c000543c07034002803405509580a0940c002108807412035007150980b40c0109240558480c000811584191040900d40505990803104150f174120484c0b600d0010340b410742503022441880d02819590010301c003808082d100d00294a081e08029610300b8040c9003161030b00c07503407850301c2c154059940e40401c2c00240d414081d1401c020001c0d00c02040000742d41c0301c06022600d460441200740191000d2407080d41d41c90080321380165034040c003040404000c2c05550650104650448506c51404806000b8282d0300000c2940c071650442d503c0c08140c01d40d8070011501c4260700079680c3e04440c400b000501081c40d02da08814a0752500e030708103a04082c2d0b6034681004115860900f00c0050304070640d0140030708402c0c000c100c00780030240d41c0c48828914000407420170143c09106042085150b00c0b4884040c8200207001c80103150040500c0746280c0c0f141054040c90f068003a0320380300c80d86011980c0070701074040e0041101301c0300d960325104281 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 952003417 1250 952002167 952002179
    0xf0c0303050a2301051903020d140102070b0403020106030c3203010e1b041b0c060b0112050718150f0e030316080408010b1e3d02010f05060a 62
    0x160001804008946450b0802c2c035209010ba004034081003403030f10008000c1549800203001c0b01c070300c2c0326102811880800ba014401350710389440c01091103521000101510804841c06ca0090203410801403104c0240001d00c02403590540000c0282d0307000348855051a942d03801100180401c44010840c0b040702115449130016240c0c7c0f081407100b00203000030030340218050b40e89040c0000c608003081071503078055110400382024814201100007940c01d0248900141c007000d004402444402004540c03107419026031644a034540c0200c4080c004014030407800c028101400c03e040303800c0b80070b191a0018000044c0407603411540a4a11110303107501001c8950366174221000c100c1034400030303010b110800c0301d40c00c6900d52480b9619070600074015982c031542862422820b49409031051480b88500e5980b0062450304608100c0718900c003120a0800c2c541c41d24820300c0d1070840042042900d0030018019030070042d0050640401c50f0b0158000c100c1a46031510344001c4400589070141c01003c2c0907014001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 952004667 1250 952003417 952003421
    0x2070b18070e0a1401140d021e09070302031e040224271905060405010c140a0b0907061b060c140d0902010e030c010e04020d020421050705010f0c0303 66
    0x100d9803148007034569664a4880108090009690000d019940c41c00340c08229100c3c01240e50140002c958060590030010300080e07500716807014080c4c0f140d0402220315014440c40d1030003028a0201900c44c400300e01d02100c1c00380c001e410864040300d1040000240360004c155034080c01e4480c50b4001c0106003950981c1c0c05a032001840480101c1080b403041005a2100110300026820031507010300500b8440c07014410b0254a10790100c901e492191288070a200701c2d503c00c0150b400b41c48080c6485003541285051410300c1c00d500d6544101c0034058a200a41440000a480f522840481040341e20240d52a40100d074030341002c9450051240d40402094005a8241c018110b40c1c40c0514005400c0f020030baa00900590100740d13501303007981c1d0f584000000c550b0451a103400c002c0080300070f8010404a540044c000300300740704206104985c0000c1c0c1118084243d8156009422565a403110444400628910307070710b0000419200d034030541a000446620903110040511580d944103030a954080d641500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 952005917 1250 952004667 952004701
    0x6030b03030c07030c050109050303030115030b0d120305070917030f0f07120f03050a02030603061803160c08060a0c14030907030821010509070f05090316230402070b 73
    0x2900d400100320102c98064200a90005103003d2400c6620440c60309001524003022580000d0107a00140010042081030791026004da40542c00c0200f14002107000240201c900c03c0c900a00d01444024503d204945c540c1c840c0740b00382030365100d924000f03403690305a0703030b010070010044141580f08015041545042ca0050040e4402d800c8815017041c07615a01c1040d40301325240d281002405090208281c0ea61500980350007800301d401c01c40c91401c0400c08640c5480000b401510200701c0805407002410003041107800321000080d000c640c66110349840001600d0710321502c0e1192144502294840b101071041c0e00b589010ba4442038100d020540320510305810051106541d4014090000049802c0800400c52080044019100506541503854180d101030f0041405070071420104130050750451724100004c4c03250308099848111000004c0e2400400e41c03003c2d0386c040340c1d086000610003c0540d014002458440c05407825a1407581480224050300c80041c000c80343d1400400c012442da102c54170 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 952007167 1250 952005917 952005919
    0x1050706060e0112050610050a260f070311270903070b13021f020717030c0a0f02030706022a120d0915140a2001320603060106030b 58
    0x109800380c1d41c82c07807204140000d038802101266030b2054402040307414060113a1101c1c800c1c541d002c6960030b1101040810340d0718000c8010300341c00c45459065181000a54010340072252040303400180c42c02c21040e0311740c2ca052004803600942d8400e247c00e14900319200ca501c0b13040700301c040c4ad140b11600008405503031018110340b016020030007070040820b500040d1148645102400c0350304404091051000d000303481d184040400b08041c5c000000c103540851124110303140c444a500806100300b481e282144644424001d00e40b081d000f0401c20080c60300000140d85008074242c3c0c00f856039440e0140d8540c120684002c0d0003540101c41c00030041c0380707030011406100000e060411500090350356030740b406180c241140c0c0400c60040b41002000507140c000d10b0300020358030346a002e000c4401601c015a004110300c0318240195507001005852504204100440400000340081010000300b40d5809003a28001c6500004480408113040210280b841c0614000740c001c2045a01e050070850007009140ca1312 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 952008417 1250 952007167 952007171
    0x1d0105150108190e01050402090a02120a050705040503060103150507050c070b070317070c120f080606030a0b031c0f03050925090603050c090a0b0d0609170d021806090d0201050706 79
    0x20203d5900c3e511448800c4502040005464205401040320360740d401480f095081d80100411018802d1a1001c03941080c0094008030310398a030108261007502980d040141c26216120000090140b602440c49400b064084100111307101c10004982c140300d8032408040039400b0000410140201c4002810560300078500241c0c400c8900d00d203114610700a03180b0100080741202c105083c82809040440c1c13100d51424200c42c0142207120281407004001c0075603100c1d90b400720004040a03150b801070041c10307800905403041c25407071020003031007089506140c100042c0109d401e681c5090092060a004030020300c002c207072481c00220707001880c80101c10100038540200300c0019200303801380602c10280d44208003408610b0401b005000c40c04c1c60050907150242c0c1001e5090341161542e565a109090b0401400704650005003400c8081100c189440160303043d001450801041142e07003e8141ca09a4040180020030060100580f900407190595803020741230354014019030040c2c0007042028410301d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 952009667 1250 952008417 952008451
    0x315060a09020d050702070501050406022e0501150314060108181e0106090e061e0903040312080103050618061513020708121f05042a02011d0105150108 67
    0x40c042c0c0e00068890074500780c6440501c95460b40621600303001e0482031031b09506103464a00d0003507482e90002d00441242c030710300034000c5940e0f01d04a8003110a21003035105002a50350b500c1b10820811040e2501d0b40001c3c030700325401c020038028249050040030142e581d1100d64807060300c40d078103090b1b82078074a440600c641d40c1c0f030788600c100604510078a105200000140399190041c0d003420b4882042100680f82c001c0350400072405446406070b00c0d0f001c002c4040c0ca000381d0314400c03100d282d4856608040c00850510601c2604a540f01c1071042c140c80c4035406880054448080310b941c07860001c240c0b50300715003100b0002092034a208804201c1d0201c01020082d103910350540e10400caa02c416015280b808002030390ba107070510714210041e04258540c1510322803810101012a4070000741c0140c0c0e2042d501c0d0000c0011400c0300c101707550f009001c2c1c410041c0e00119290b20103802001100004141090b1038102140d400c074040c07042c0c0c0d10411104010245040399000111592100180b0700c40b081480e2040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 952010917 1250 952009667 952009679
    0x15060f090303120906010609081f020f04030605010b1b0a030e090a06031e05010612050703110f040516021b130c020313030b01081c0e0409080910030f11090315060a 72
    0x5140c061300040001d0242d65051807401054010650002c1403198000030340041c02d450001d61042e05201c2c0c5030390040c3c0b01c0c1025000440ca504c01c5034000342125060500128030180140c3c0149041310710014001d10704c0b956180e20a44030140c3d02005070100301034810322481e030700b007000100740c0c0320413407800000d841034603640c0724003108050a074803040d408500012902007040034070400707026010014000440c0310786962050754510590100401045002040c100941c031003402c4913031484c0004005005c070b46040314400c0118455110950014454a000007400d2aa050408148241c001d4101550b030210303c00108003a01118080f0011448104941e2507660741088041015500c15a03000c155549800c1445180c103640c074200030004141303000700c400d40315080071190005402c01c0d01e000c1072195490078030400c00c0c003800784181e800030120380078095556810f074040341c58056540c1040210b1510110659a24083d00121541588c02040c0d080000c45090391110740c8a03400501c5c4401c1d503600c0316 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 952012167 1250 952010917 952010947
    0x3061306083d140601180b07030306051002010b0a0906050a0b0c0a0506070801061e08182a0901140d02130e1b010e04090b0c07030207080303040f0b15060f090303 71
    0x16400c8000e181d03909040c401d0010000e00154010b42e00b413030040320b40d5010100d1090703404914403403941f14420001e0403404050080d006070004090050804500c50050342029001e400d078220402d01c41c54090901140384441c0e84503150070343d040609024040c0f42404181d54030f660000d101c0340454031071040540700203001003001600ca00841d40c3c032040319516146020304522034910042c1180041e00c010f04100e50360200d1500ea2146003002940811045440343c503040106500d49610441511004840382c400c00007581a0820001e07a12440305aa840840d00442c2800c801343c15880281c51010b0b0015103001c0c0040018002c445c0000149107200d800c100e46060148410303000d2500c6816a100182e60b00700b0701c0b20034903a00c181c1e0188442c6c0d18036541d0080340e0344020503c0860070f401151500505100b000b0034805001840c088039030320b042509002e48151441d58048800c0001100028070340c0300c032042c80c1d0030001c0c0003418290a10481070320040c0e050700055107041c0c051000340000c408604860b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 952013417 1250 952012167 952012273
    0xc020106030507270b0315042105030709050a03020a050d0510020301030b0a06050303070c06110f01140a150803030103020d02180403030b041b0e0d02190b0306130608 73
    0x480c2c1001d43c18081c04484d102a203403600c0260491901d410b0b140039898030040303401880c40b000310441c0d00c115507803881c02587e620380e6070303041941d890400c5c0c18545144d50810010760040d403c0c0d0b1610400030396660f04202400c010303400025080810560200814281a1489804548140103403450340641840c0784080343c0090348261100701600041c8400414584a5800541001e601541c580403d079120020710200303505c111402c00c4860305100303038041c0301481412400c05105000f4000d100360f0001101c54003400f9a4141d0250b0b280c0381da18540010144521007c6612020195095a19580801c88110140d101c01c3c1e0708113100d540754001640e000101203218511949000641e80003a0342030004440000f007260345031518054181002e160886113441203607a0844400c02001c040c0d02c041110b400d081c03031392014004560712011400b5a0348001035889003030251454907100244000700340503100141b0031002250000054440d0704140019640701c02000c6a030360104405190303505007640305c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 952014667 1250 952013417 952013429
    0x1e1a060f09090705250b0f15030f060a14131103070302101d040b0a0e040519030807020d0507080301060e010e0303191101050702060f04052802240d0c020106030507 72
    0x41c400b4100b48440c89101c00340c100b0a6543d940e015407981c0c03003406100014145400754447ca00018025965140c0410350320303170000d0150755406071030301325417590f5000540da40c0085174100f45600c04002c1840f01c1e00c5100ea03801200f107000041e00c9032501c0b02c3c00100900450380500403030340040056180d404021291000b19526941503900c032581c5051002c00755160644500d00b4903e0940860341c62004500c03d49228050388031160721140fa119240c0b20859654030b179000141c039044410700d900500c1c90743c851030b03440c1c081c1d80d01e50390a07420803111340c03040c3c4000524a60003880144a2107100365070048180e401030401c81c4411f80a9400280740d40c00c04503c0d402c1954241010305105503002200107064448017000344003500f40003030041e484000c020905941444005c0024007445800c1082c00d240400f9100113180030000850204105035010340280c0c00b036102203124452075072035031103140c5801004900085c14412248900c10190002e8015001150b49a94000c408220148116001059 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 952015917 1250 952014667 952014677
    0x3021e0c0d0807141b0f010c060e010203071d1003050402030f010f0f0c0507150504021914040c0c0b010e0703110c0d03061a09040209060712031e1a060f090907 70
    0x3043c1c0c90510004014246003025603000800c25001c9400d1a40074000030310000c070b0304030403205c0000d00100c8a1020000700500141d007040c885041c003140650003103002d09000d9403401851002000d50520128001c2c0f88075401044000540c070441c2d101b5032015402920090607640004400b00d501c50039a090910114062a55205104003000651080c0300c00c40d400c0b41001402d00c032032038954003511050300d00f5005c1140d4032503000900f15560603606500e140d003504100048552280b03800000000340125250045150950b61120140500703d50343c1d401d680030900c05807681c00c0004200c4030410103071924052640703456017501d40e00e00081c0541051030b9140d000f000310100507035000b000c1d56041c1d44002d120000300700030744c80c544c0000d4007103d909034402d84025903500200804107200c0d02c5a034001410302044641401c00c0103602d80c201881e03001c4079488849041d45034204000885040b800c5100444081c0540c5035500d0400f9000717058140c5e41d0008540c00d02400344042503d525044401000140e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 952017167 1250 952015917 952015927
    0xb010c140606010905101e020708070603050103030201050601080103050307030e01051b160b0c06070507021f020610080d0c060906020c0f0303010824040305130f1701051303021e0c0d08 81
    0x1503072113408040201003c440c00070140600300000b816010307280e0344c034036683d03072030144e04490030303402004085d0086c030300c8808407a1103a0780d6000040042c87c0c20b0204034015402c010201340258484e403641816240c110016516288495900342c60900c6d1f40030582d0f050060a0050810b82064080c00c2c00c00b4061000142440d503901500c064240c411681107000c020790103102e0480300000000b206603114410382042036844805000040c255010702c00702080060301d10340c20305141680458204d001700c40c0004c1502d400c0351609a11920703800307540840000110b061260b400480c8264214010507805544014074000c95080b1007420681510816081c560000004004603c8100302e1030740d910308032040951201c41800802c4171000030191025040007400304030040f80e03001e074440980040c4010f20800c00e0b01035882c1c0c00e2040003a034076080000030394038246c00107800740c0e40c0700480c0184a506601a05117407492500001c240c086800080e600c61103896404c800300c0c2c0f146299140c40ca40100441a10b07a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 952018417 1250 952017167 952017169
    0x9010603020315100608130204020414030d030c0509010f090b040902190c0b15030313170708010209060d05311101110703030f1205010b2206120b010c140606 69
    0x104540d4a083c0011801c1c401c210442d12a04030030401c3d50298548200c040c0c45804e01507805540141010b544584009400500c0890002110942c00b2050707041c3c5038124100310301901220855100d41020442c100031701c3d80c856210b05101080f4150504140c0000e680310f070340c1c508050f04140c011600c8540d0008500c592a50040740801d081c250501e414041c0409550b560407540c00c2c00350008910000c0d01c0c0340b801441e0703003e1096683c0c81c420601d44201d21aa1030100d645610300c608003ca0310b900800c0b030b000c1403002c01030084955070301d009001949000c104081c000c005001c01000d0034408041e0704c10b20b403007036000205503803d0103c0b0030003541085543c07814081440303581c000502d814440c404402400803580404c046080320307010b0030603c942103980f903815218041494038103542c0303615181c0040b64100d1880e000e031001c0c03040c0c1681c03840f10f210b141071740014501c00c5001c0c03035011a01040c168910400c160300b02990340030040c50315810301d0409686401e000c4801c20001e000e907801a200300542 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 952019667 1250 952018417 952018423
    0x170a08060613030b040f1401090b06010504033801091401050a05030c040905010b0a0308040812090a0b07050319080a0e0d050708071707080a020d0807050f070317090106030203 77
    0x1040d41260001e1600885a014100000443c0b0000f40381010420015061020300256210b03a030f50044d060181c0070388040c1c40340d8000c0503405000ca40341801c0001149655220f00140d4080e2944051a503841d40c0c0206912481304100c0f010f140c0e0754243d100c080414950417400300350300a00d00010046622404541d42d21031640058101a0040c1011706007000542e8001482c03e4908805079000141e00e94141011400340c640d0311035054002070320101c00001c000400b4001e004454000c41030f14210301403400d020215200700343c4119840080300c00d051000f0f100000003400304921075821a8540001d1030601c1106540150130f2101042601e0100240418140074920300c844d00d00c005044a03401c0204090b14a0003000f401034100e01c13001c10060100040c1054100840b0070f440d41954451106e443c007550b003a40105860801401040060102a4040c1420728007400032074403002c1c18504079982250958100242c1501003100760f490109040d00d4904c00540107480f040c0003c110302c0c0c114018189 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 952020917 1250 952019667 952019671
    0x3050a0305010803190507030c02030f0a02010806030606010c02150418060612050702030d1d070806060a0f050a03060c0201020d051821040e0402060421300e0d170a08 73
    0x100f2900100a8945140d222070b0007104019070b1400c0064655000f81411510505041002909807040ca160f020002100090350f80501c0e200b43d8841e01c0c1a5295001e0548810046d140076000c1407403080c0d55401440c100c080780c1115a80003414504003681d41012204000100d80408030950b0307104000e001c1c42d07a020408030620760070340506018500740f040d0000d581c1e21401544400c11981d4440c410b41d040e5030400c010347e42c141404d044030240760325000244c1d110103090343d400b1311640003c80000380c00204422004200c40005109200240c510303120800604084080d4404556003041402003008551058500030840e00c12020081c0c4014554980382c07101c114101c3c1a80d03007411007440071000480381283c051700d20b20300c0310030761941340d0348042011406590805e9204807190040d00c00c01411001445240713501a261a03110720303e00c05440c841c18030305004c0010f00c0003190b80417041118040d082c648040240031f0410094411284c854031144404151161211900043c0d103086003540b00f0b51150b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 952022167 1250 952020917 952020929
    0x1021219081609090c03060b031f081501051c14070302010f1727060c0918090d200f030408070f0b040314010617010b090702030306030a0f08090d03050a030501 70
    0x40100030300c03500040c00036000f40c131400c500c0d96151100801c1c4075100760070910052991602e0b0f81d460341000d616854001c264043e040c600b030340d054080040c030740000091105032140c00840302c0c8556400c2605101c0988a010301264500134000a40c1001500003582c40d14400701d00c0c0c02030540130b821031000400b5146003014601c204000c041107118801c1c1c008201130341049114900c5a0416113450510340304511307054810050703029000c2040a401e08000040800f92400c0320006080e00b800151449654000d60b8044040c1e0300046c0f009071058041d001e51468044d2980e008210400010580e900d0078002192400d440d800c0801e00308450b9608105007000380104803200c02030141010030240e454001c61001600d44034281301580f0380d9090070351007040500010398025500200d02070a49028214040c122400b520700d90000a400078804410742c0d000704001000b0b421041130b591101d0050250080065504010420800c0c3c1559282e0f130000d41c08034440d460385920f844100b10042c0407200168045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 952023417 1250 952022167 952022191
    0x909050d0203391204140d08030402130b12030c07050319081c0213030b1b09060c03093f032517040f09020915090102121908 55
    0x7103040c05140054500d40c2100c04019096a00d842c010065041003d182c0d07060401d0182e04a0911845200e00090041c1c6685444840050780c1079001d1060001c1c0071040070380224400d00c0420018507040800031003016145c0804a0b88028030701c00900c203210038030300541081e8000940e08440400a016180051004a0103032a85c0c0814000701a12141c1d51000240b40110010704003018440e40032502244000000e004c54699440b4a910f0507000c4050000381c0711200440009046e40404001c5440d044550b60155400c10000c08280080e58210301000d0b04103000600010003562034500b20b0304550310704400b0b400d0044240141d84c81a04a840460100c2402d0f224007507021814000b080358000204554001e80c0c2110000c3d07a44072902c0441e40040031030703052081d02000146400090001da1314821030800c0034a07a61041d1078124454858819006034121038144942440705000d0501c10006006417004200c1d1603081c1a1590700c944241403104045054030074495901c141c100c0e174403503c05880 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 952024667 1250 952023417 952023427
    0xb03070b030406110c0d050405041b020d0e0117130212150708280501030c0503070501140f120c030411060909060d020f0d0606050909011103130c030c0909050d0203 72
    0x40012621000b40040d004588403540814003070002c6007140c000440741c41c10303a000206180c5000b46030f980188a0b6505c01d83c104030743c00d0103a0301c0700c000344804441701d9001000142240d80c1c060341d0341403020401d41d0622004003c8005103038190b0815030301c945000018442201c0305c03481082034252600b288541a603100d6100e1040d0420301c468401c0e086071081c1000d046554603c4583d045003e8030b0f4001c20f5000000342c000c0c1a01e0700880d041306050701d1241e034010a00c0d0b030716041030503512070140c4103c60000b1030355001401e0031011a40101010302803906810b140064851180c0f580a01c2560000c1c2054400820031042c440c60b001001403854003111088c3c58041c40600140f28a103010300200e00c660301040c56142156030b10b80c6400805076015080441c9001c290034800000c00d420702c6510300485070343c0b002070f1a82c4c0041c418258085810038030705056440d551540c0d2040000d20400316604445040080007003040c01040c03a000744034010001c210f412181c5441414180140358070800e40d401480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 952025917 1250 952024667 952024679
    0x6040807170d0f08070509040609020d091a0c0f0715050c07050c06040302010801170a05010c0509040509240903070609060f0b040504020901091a04061221020312040201050c010509030d0b0307 84
    0x981145c0101e154030b0304a403604019030000d40203192a0b0f0210941c648000742c1d0003550810354200400c02400f0300c6420340f070310507e480c1003030101030304544480c000c50080150440c4942c90303034041c261841c02480140300381e0280207080c0b4100c64064a00116905010031142c003000400c010801c0607100988503182002c1c65940060400d010601400c40d080000c03c0c4004a1350404000c1d801d15540c005009104242e4007045c00f911300d500c180300241c003641c203290010b403403000e000680135140241c001d0120703000e0000c21640013004001800e25102e600042054074041441d50284108840c010000000c0c05082c3c0c01000007180e80c2c4c49a110301030b42c105020040036940d83c03036003281143c2000101080440385c1008031095a015441300c0b540c070500e00900441c48440c0400200c0c4081d100b00075070098140114051580001e6030120140184d104110444c8851207170340d00c003030300144103040003800c01c0240c50816094440c101c3c0d144040340c1c0082411010111180508012108158040c1c40410704081d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 952027167 1250 952025917 952025927
    0x40506040909060b100e03010e0601080606060310030506090105010905090105150105030a0b12030403061116120923030c010918110c10090210030b010f0c0206040807170d0f 76
    0x4400c00141a0342d800710103051102640181003448402044140203415407034015041d4148603803518000e40c0381c1450500f40c0326001400c641600c4c02c1b00014040e5681c2c0c034080102692009040840701b6120701e0380000090803c00255010716283d0340042819070401c202d56048820060103418070342c0c14403041c00a03611650a541016810a10f46581e8965a1961060240903014066900422a180403024020303012018005580c801c0f03100340003190465107507100e180564401d204e241000c00410700300184005800784101642030800c1d40086680e01900703074600411104200a044501c106400e00d0b1a0600444081030b000342013501060f401c1c580100b640e2040b1a08846d207103035a403444807100e50f200c1c0096641900d00c103030441d04c09000003500d09028010740007003240640f044a0001204600038003640e0342c2c0d40c80c10303950160500c4401400b2035070a4805801030740c000404100200c0c2c600f90030b1140740090000805e401d680c0d1544136510a1601a60b04128802c0003e03481800c0210380d07004c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 952028417 1250 952027167 952027169
    0x2040f0815071d01081005030a0804030510021c0e010f09060c020f070602070605091f1806050f03070503060103151217031b0309100216110307030b0105100e0a0602150a0204050604 79
    0x28a0518060b969046c00100690380d1500156071510030311000d6010019010000c2c01501d1107507080e6401c0e000700c0280202a070191003910038010f10f01400c0109a00c1059024480c82d41110001203a4010404c401808543d040341080d10900d48404590402c10340401c500c10b00a50144014a03c96250010094441c00705000b070300c0800c080041d486030325a40b440340f03502e2000480d00c4003900d5125081405405589008102d598500058200049450154041d40c03034600b48014000e14650381c4c0c0c1c104403140e1380001c180c2c0c0d050556440440000c603542c0d0f04a10042c00300c40310305003200e2036982400501e81102c0f003000507e0103420020080175800140c400d041c1d00704205007503134880e00c035034200c2d9052a01a0700705000705c074408510311600602d002210b080f01801504080c070000036207428542c984002d03000260101e030424004109504224682060054841c6024045c0740c1850303002400608503030748468016840000208003900c080c408954025401c25004c510341031030140072908601076 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 952029667 1250 952028417 952028419
    0x3040803092b05130b0c34030b0402040f110901022a21030a021b010c032111030c0c060f1605160803090d0306080102090d060e0102040f0815071d 64
    0x1300300761103c0c2e044401e040d00500148045261100d010241b419a035225010800703501916581c1a500c4000d09104554451038004010b003290030305540302c50000c6038020700200c0c5c2003a614041600c1d4a0503504c5030b103180d0007400410966a407801c0000a00d4104074400f11050b1100e00142a404009103280b401507242d02502c0b8101000c2420700d04028000045c50001c43c0d80c0800214000c400e58082103000620011440c000c00c3c1030b205200440c0c81080019000b40482d045030b102c4403420101921084000c0c24540010038414003a2500a031a504190740303c140501d408182094201c0c0d05000c215440142c1c20120120340c600000f5035001104020241d80c284000094500c100030148180070401c0c2e9000240e003a507a040090500b0703640c40640e02d0000000b40b078420007080760036060003201e80000d00100800303109030301500c0300402482c084904510340d646c00c001c000fa003003440084010080807041d0140250050400b0001d00701803009054000f000f04500c1c40c40540300003c070701e002c03410704 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 952030917 1250 952029667 952029677
    0x3040c06113705060c0705151614091c060c08250c0606031a06100e0f18091e120403150e01110a17060108130c030803040803092b 57
    0x107140c540308480c419604029203d07014801c100160345854070f00070000380344101d0071141011031100741c420743d1110903505041003001c80814082c00c0c0e441030b00da400720b0a0742504d42d00c1c5894904000240e50625403015940d100341142c01400510044e881172084807081810101c55925001c0181041c000c200e8108262001d040701c411408648107461320050b49512080810081e0744a0505a40c4140c0900d40c0381c0c0500441000608079003070074821310340d00c400e0036110780180320380506c1003240314a901400e03190080c0c002d19010416540443c802e6004140603c09040b441136100007401840d13904154400099001032207124840703540f5030844089075000f200660b03000e02409440d1005c0d101d00e07514049a0b43c281700801c030188003844028400482141c554409071107003c0f2032100d5182d01265414049001c01000640010043d440542c1c000e110780074003552192240e031341980e241c2007502c080c2e80038100802040110001005404c4648030402075451070f1540c101203043c0e14403045000102001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 952032167 1250 952030917 952030993
    0x70603180807030507170d0f0b1005030112030c02040f020319020708030604050705120c300408070507030506090d0e03150a0f09020d0b0604060f030f02010c1703040c0611 75
    0xc201620440340071251030043d50b02d003a001c01a0000c1c1a06c240500d114a127000010901c1d403a1070b400c140d05d40265170300c4860560380380240c1c0741c0c0c5407802c440c800c0e424821141d103201c0040c0e070365106400710311005140060b20781c00c190b1020380c4010b418440d80e1b5141c510401c420317004907807000c2c00c0d241d004d5400c94022940390f0f10031000f1503890060000d1120211203040611006000100280024800490075220002040928900c0c90044c3e80c04001e002544075003c1404181002d0080468601440071a10410340d03c0e41c816182c84c000315003c0f006900030300002c0c906a54010322040c2c541341c044000300722940c01c5541e40c6000c8000070307104003c0e00c0d81d07444010202c0c0c540c82d008104220f07001414005211100d00f807140740c0d007030200d80c40c0d48031310710701500801c0c040c85087c2d0f080103a0341c0240d0030140c894140e038019150322006000688030541305070030030340b41104680d000350300c243e108141b040e074024034241c03001c1c00101c032190510420760062500c103c1129980f0300c0d4113080c0511241106010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 952033417 1250 952032167 952032173
    0x30103112413151101050601030b130513020a0305010b0913051b030106080a0614010b070506220f1202071535071806210b0a080609070603180807030507 67
    0x103102a5402900e0310b540c2d5242c1541c803d9084038803011103074481070003448917035141300c01141201c1801c190264801561000703403030400800d5000f030303034040c11454480b06142401c0d000502501110340c400c4072130f0703910b07441c024540341800d5040c607420030407401000f00f1140103691002e40340c07442640c24850310f404d18505050303159025004a0000d01100060310a4100107041100c003612041e54a040e04c0c010b0301000090b881801422560b4403a004030180c01961a110b4074000b84020048011010442e002c0c840004500c02c0840b582141d031140b100c0d0ba80300c2412140c06400e01030940c0c000d00701034011291380284e885d044044000342c080c0c41c030110380004114507003070901c1030010381c0e441d022018500c040041c441d80080a0860050031484054007142d59071908607050003000b00c030403034840d60b00b80310300c2c01110040e0805074880300700a001c0101c040d200c1045c0d5140880840b081c60301c80e441800c0410850350140304141421440c032680c20000155516615424070400b00c0c010304020000510b82c080c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 952034667 1250 952033417 952033447
    0x30115091a070609110907020c0109050d170703050d050109050103152009010302041e03140f0a08160f03031d060103050309191509091b090e18030f0301031124 70
    0x805c50007006258942440c02c4000e42d03504400340300f280810907440020500e03203040e05549501e1507010f6410b01c8200b401039080d20081c2c012240460038800f0921a41029410031b0140c0c60180c172103040d000070198034505103d10031900c110802e814803858800c0b0911503000714407000404c0c841c0104102c0d034500c03150004800a02c100e5021100050601510198290f820780d081c6c0c08890145c03071684910080d04504030b440d152400e00848082c1e020100702c100040028000d4507085512620308182c05049803544a42040304d01c40c11400650340f0b009804585207050742030844140d404000301120341c1580e460701d03500d20a80d03409520543d11103055415210080d6455800740c8004500021010388440c0068a098107a000c0c420409040c50400c94102c2c0e07850060404605050b078508007114034207850072030703100c00281c00511003501424035020030b031008000800b04413504000859507507155040a600030824240b44510a0070860050810000c0c400c42d560f0140c134583c04903a40e0b485640000300a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 952035917 1250 952034667 952034693
    0x40b070b0c0c2a0307150801061404052e03061e0806010311061b0c031e03091201110a05070c08060903071514010801050412050f070b0402040f02030115091a070609 72
    0x1504d0303c00c04601080d80002c55140d4a4504031136100c0c801203980301c50017a80c0060071000500202e20341032104205524014003046002048802c3d0311981481f40807010209050b42e0342c150740801e803201001c214510300184114011121811004c00d0607040c080a5622004d041c40003030700f112a07285c0020190790714401100c1c282d81e11752544e042c0d841c1541c07a40d542c0762440f200055101c3d00510840c0752090704031070840401c90b10074502440c580281c0d0b10412800c030304950801c901943d80d982040030034101282c001c200c1c4101da42c889a07201d45840c903200c640c81d0040e03000408540c02000c02d200844400009682c030349940841c004182c0d01d03004400400410085c00600f80c042e040e1400060703100300640c06540901c1c05040c0103841c845d0340210070b48062213011b070300900c1210208029030100f5000b044494005200a10104410100c0403462003603070000e8001d407581d81d0270310101c00c99054000d0f030100c0060000ca048020020007841e120042c9004041c006000c0540313030110f030020030040c545c02c14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 952037167 1250 952035917 952035919
    0x80c040b0a15110d090608040b0a0e01060b04030204060f0803040611033a0c02030a0c170c03091002011104090c210f06081609150803040b070b0c0c2a 66
    0x3202c001c909a10040503a02e0000744000c1074000e20300c0c02e4050798400d0f80032500355205501c4011a94031030340d950101503074000344003861050341d8051540700188280075610080140450303154449046004000441e00198800100c41c43c00d00810002d8034400b10584013101c03500d04014620f400301041480c01c610400000821003c00c070035055041072000345080c41524035503146980c0f00011509000b01701c914007c02400507030700038000071004610031140000c1c80d61040e07500c0b6005000707460b0302d01c031207030014105140310342c01c0814895628100001807102107282c0d4402070000e00c514240c03407a0b462103180603003140789403582e515980e00350240f00201880005442441e0010055041c49001000722240c00030001e8141f41000626000001c0c80740100551351695031043e6182040351002031601203c02c800c4112902400905140140060300050444103005591030000b0302c4e1141c100c0b4001000c0c40400503060000190a5070001550409920020035032890410001d09600b0204403001c002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 952038417 1250 952037167 952037189
    0x510020f060f010918030c02040b0118080a02150307081302010c120c050c0d02091303020708102301140d03120f020d051501050a211b02100204080c040b0a 68
    0x11001c81c0c03029402d01d904840415500700682000c8070701e1000760200350100500015400c10f415405131600e5840340c2480c4c070050501d80c1c41c2c40c854160342c1400080551003280b5640014082c4400d6043c0852142c456880300920b43c0c2c91842d19410241800c00040c29100410031060742401c00c59002c0d0882816a41c0c00500d91110a958500c1c0141900b814079400c8810780952001c58101d802c1808081480c240d0013088880196591042d2010007600c8020030b03170452041c940005003a050500071040205003800000c50314415141c5c1982070340010020354420b2003c180e0040200e01e131181203031490b0340d804403500540b2002d1030030708894807c1da41070248811440e1203107030b0302c070b0004680c02040e242c0d60201d010712040c1c7e0380000c1c0400c882e0030401c0c01804554100000c031070441c803400040c048000b8000346100d00305004c802d0041120032103100c074905603115110a2054640400090402da61000f106603d8a0b04000713495880d5413558040314040e60301d0308401030f503a943c2d02c45140c002c4c000d90440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 952039667 1250 952038417 952038421
    0x7020a1403070510051308090301090c30030c03030f150b0d050a02042706030f0f03030e0c03030d020d0e240a0b1c02040b0d030e10020312010510020f06 67
    0x1080d180d0b805240101c80034441d41180025880103402454400e52500c2456405803c080d02c828801d070344004500d82d85950b0310490440081e15943c0c07994040d08218181264050f82000c581c2c0404060285204009880c001c03c1c00000c2e90044240b20388a0381850041034840c0d08042c1c001c06014500780d22456001d035600c02144020003403010348200e03190355105002c0c0740c0b15544c08404a12642c00b43c1c00024404804445110300760002107000100c40032000104d00b80e59841d0b01404c14260346048071800f6020100200340755050056180d00300038500901003c4801c0c00000740c0e02d104031140c1a0407141c000c40c01310350720111940301c40ba040494405403000b910800d48000d0041c0c0941d11000c50703108030400890040806842500400c010141000c02c03200d07405606c0610440001703104903032090715400d1841280d100c0d20140c0085600c00c1c2c444c0103d80e60a002000300d106848042e6000b10f500034460b0300d445442409806045070000d5440328a00e9112210807800c1001540d1504030034072030401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 952040917 1250 952039667 952039703
    0x40f03030f091208100911180303040e040308040209280b01090b0c01060306110f04030204110d1a012a020904031b0b06031b0619031506020f0c030705100807020a 71
    0x11425200c1c8031720380e00d4580150744510a00c0101c5a0f0704840c1c07031012030140a2050041c04154141030120401411281001d039903000750360350102c04540881c009075882c400d01c011030501e42030740764002010780080f0745c5203008880e400107140245eaa0340c450198444441e504070340d001d0300024020f007030100c3c034140c1c0d190401c2030f140b4043e00c4070740b104998240c80c041a5029901c0c943c0700340da4100449140c118070301860f507000c0002070a2542031140130325200b0400e0404c100c1051003444003001c000c0007103802d140030000c005406588002c00c440c04000004010241000d08007440c1040643d040f00ca402441d00c0300d0804907412800007c1080800100d203c0507018441d820300101c0c49131b10201d00325409400a01a1a84d032030019400c0640c02c0801446002108a8a840e001843c120076281c0090090030041803060704003102d600030b6000d40c2250003100036041041c0110b000002c01500180f20141c0340c14007060020019244041c00c00c007800e404201098800c1c048a400180c000d54030310460046d40c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 952042167 1250 952040917 952040927
    0x408210313030e0a17060f2a07050102042103020106050306100b0f0d0504030504090c0e0d0308060312160c0f0312051605030a2001110405120717061e040f03030f0912 73
    0x3481103120881d29400140d0040c55001001c0c0f1070305641c5203941e10b0a40c42304e40100e000c0d0010601103606540901001c038290850003495403900d01b4400341c410a40d141e82c1000f9084500e19000a80a504854100074403101469201d8040b00c10021156030b44400c0421800154011a0300ca9140c881c2410140824507911401400640b24050810032024080c07550030389500d0000024550082c210120079401711340101e1f02182c2c041d0018098030440110038000f411942c1c00308041d6107070000980380c1141413048828249010304a0f52035924501411078480320740b00185040d00d40c2c208540040e8201210765401c8141002651000480f605e880075084090035403890440c0307620f0380b400249015901c0d841d05005061701401180c00740c41c03a0038206804c0c0040f94440c6040d41d56544140d442c00520306441d103600b0111404039801624a90500410010040701500041c02c06540c002042c0004100f000520741c0741182d25040000b0325008440454000c2c003042280a80300144032050000e0207a006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 952043417 1250 952042167 952042171
    0x2070506070c0f0b1b030703080f040f0c0f1e03020303250c09020301090b04021c0e1f020a08091f1505060d0e0d03140f0c040b0408210313030e0a1706 66
    0x5200c41c5c0380c0041c402502c2a0350b80142c2c04041c1c00a900c241c041520360b00c0614450b60003600583c40000300900d10b40300c4003501da950ba80701a8207040c3d0702ea81044404130301822400801038806000c014945140c0001e5035034041c04a0340c0441e8a0308055482800d002c0058404045034030041480c1407a54403203050000750000d100d030301202818a1041096803410b8800c40c0c00742c101d85881e440c090b86d60310170940e004003140031203143c1604c95400501987d50b804000396a41400d42d03580541d0700c1c44015001800c407007001d0000d404c65405420a1400740142641c0700704500401d407400150201c40300313a0810f480c09540e001e1078100c440010b0b58002d11100b504a40f0034044841c040720440c004501084045545600e0340d00469001040420062a902011207401401852500b41816107500c90807583e54040d5001a10a0b80194840206c04001c400300342c030980c54507000f01f411450148908400540740c0766005042180c603410540c41036880301c081c44054600e404101d4030840c3c122070010b59910003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 952044667 1250 952043417 952043437
    0x7050a23060307081b0405150c1e1209060f0705160e060a05010509060d0e25140d05011e020a090e0c1c0608011a19050102070506070c0f0b 61
    0x103410114180e03810604200c03800b484040e600c58000e039880c0904042ea00040c08001c80846208010001e00d99440c12040c43c0008200c500035640c1d504107100840c41d0100a085805201440340c803200021000842d034074620700407001c2d000e6501c00040f0000f40c1544a60000700c2c402d15804107083d030a108002130402c0f0340c1a140d1024080340c944454200106040031034480340d000400d80c00034062940b060000d1300c0d8004002e8001030402480924681c1600c4298018103100e3744070b01b1034826001003d000740b503842080c80018580041c1044208100c804480201034020a00c0b5500041044401d5104005064681c0340c50410180440040320103540309400d410b001440340c1c400884c58154201003c4e016400c40384d0320303034541202c451034800c041c2c001081090141e0750b0340c400010141c1d02801907140080b18004521100d12004041100c4507030310b980800100c611212040c04075076000113001040c1c41d02114400e844180b68038000c1680c9845801c481c01c198214135001409941000280c00ca00c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 952045917 1250 952044667 952044719
    0x30307050c011a031902040204030c08060603120a020c090411100503071215060c080c030a0c231b031f0c0212070f030503060f040c180807030c0b0c07050a 68
    0x19010b40c55500f0011034000d650305400c4580310560000b401d02881040174809072004d03090581d03e8440188030007040c2d2044181d0b400ca01d04102d03417840c0c2885000c00c52507440c2034841c140400010025aa181082d07102805002e04002240a0080340f0208000c0c142c002800c44000c03819100c0000d2142d0030540314540402c6440400350302403141406600c0c05088014214a0750b50324024003100c20340c0c41020282c500c0d1504025444124105000600015040f9226a0014a120316044103408903944215441d11311200021520301c00211b0a001c05241d54105a07018412050009050800400407182d180481c46c5010121401c19005660300104580a43d007003045101c00000c041e10640400030030184540f41517500080c000c201841d00100c01034041d204c800e4142011400b1940d180880300007007013070500b0807115441d12080362750150001c0f1028200300c40c5569644031a1034207a015240b00070b0408904070082c10030410118009101c000c008203c015030307651005540c50300b8400c02c856146 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 952047167 1250 952045917 952045931
    0x190228050901140a031b02010b0a0e010803031b0d0c021b0102121b030702301614040e011509060b0310150207032f031c110f030307050c01 61
    0xa40600140c1d0402181a100c4622a4007849403961440c0c0c03005408800745a581e4001809a80340c10001544043c400d40002031022609010007904944036448500c001c4000001444803080100130703240c001d00b031405c01d130501c90b00207480f50206004901000503054680034034180010750001e0300030b00b80c001480090307102c090984012601d400ca10304500d224071800304948010140b0401001900070903030740c10f807810070240f80d0000e44003800d03400ba0300c00e240100c1444011118415200501054607400082c44006a41e420140c1c0d9418248100410b29412020160403522283c11241c210388060303000300710503a00c1030b03c000540320742401101c0c4a40c0c68040c0204050300c000040f43c0c0600f4400c48841c1074103192070740b40c014076125601842d085029a5400100044081311000c00824002c0c000b40800c080d0a1304810300b00305850b00c602c1c8254410400040500c5058640000c06a0140f41111000340300c11703900e81c075140002d140a41c0c148000030400041690003409400c000340d019000340004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 952048417 1250 952047167 952047247
    0xf0109180f0f020c031e0c06070504080d020d2a15050108060c0702010806060d09050d050a11010510090506060c0a03050702181017010b0603040c1d041a1902 69
    0x3e004d81141c0910310350040000030a81c6000c1503a00c0d940c15071504920740fa000c60151010308040c8141c5180004c118081414040803806100111004c0200d200400451111100041c1071014181d19031140301009943c0e100f100d0240b8440782e07a82a00649504016080301c0300b003900512003407055080d035000340c2c800314400b514104210341405070165144403868580c90b00700403043d8040c01141e0741c1c1507a0342c0304a81c002103044c04445020b1f683c43d1a02502c66515508c06410078180304d4112100b64541010440c83c4000b03003074020142c0f10f134010001001d82e100d81c00b0803882d204602d1032040134403da024900401d0317403000007010704501c00c1d503a01c0b5480c0c0c4084240007000d03100344c1d07800c1070a05845806010b24844d030240d5042e80c002102c00480c12241c001c0220710a81d001755400e650aa00300c01051181090000c0700040c25110b490405034035240c00e0312800b001c0048030342d81c1c0703000340700d40400704004c0c407201e851100045220603002c41d42d44440d500d10001608182c0e0001e0214003414080c0d18072 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 952049667 1250 952048417 952048421
    0x130216111503040803070c050a0c0f06051c0209120a1b0e0606030a0e010609110306040c020d0c331a0108071d1804030504090501050306060f0f0109180f0f 68
    0x481c00092008a0a5440f1540c13803410580000340700c0c00030407060305501800f040c410810b4501590040d4855100103041031142170f400062600400d06021080040d081e01e036580c10205c51007044000ba0040c0c840d180c060004a02c5070340c1c000c0c07543d011321429680c03106125019014031101c02d41c2c000c0261202d44d54020308506040202c9807035078041030900006114841e10341160709401a80000002c0b055169003090f400c0307a0201c9080301500d500401081442d0038030380b061403031001450004203c40384400784010100d031610718000b851116420030046000b5603420380720b40a5016130a4589081240002000081c00d00c9491401c001030101040001940940301d21801401c440c0c1c2e5000e54481e004540d003081040c000d006540019401d08000c0300d0740742151105010701c0c801e07540d50b6600d074a4070003500d041e1541078201511071741140d4180000d075680d0200701c940b616415144090003107010801a5000d0005070b000c201c14100194048001200750740c0494240b44542d2404c103d85014a61800c0c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 952050917 1250 952049667 952049689
    0xc031a0117070f0608040c030501060b120f15060a121a03010b09090c0d05161e06030515011116030c090e030909280c0504090b0d02100e13021611 64
    0x1140b0f0341041024800c85208080056105000383c2c40268025501d45c3d501e0300b1188035a1001240042c0410704040354200310020f5500600d06d05040f1020b0b08200c1c100e006008401c00d40144102d0000440364400360080b1011b0805009200d409c000c944c1c1c403070001410350710500b18098030030351030020700800904e040f12149014080c03982c02880c0c124201f400384451480386010580b00783c800d10824807c05507981010760054003012544003240308002d441e40540c611380f504000d0906041104215084d082d0300200c0d0701044c001d10b44240c079401d041503c07600b08a4000c0043d041c90900d01c20101c24410341c0a03c500485860301e400b0420030081e00e0315980c40c0d0048503186540940c40a004c00c0006100000001c1c8500f982c660310340c1070800d8440408111040d6401080126101050403c00e02850344544014034005552200703801ea02580025030000f900d50300b44003409840e100841403903d408401a44480f2040411942c07010540500c4490301e2000d48116a911505400b461107405c01c2c040d240c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 952052167 1250 952050917 952050929
    0x50a0b0a092001021f09030806060705060a02090d05010504231b04020711060301060e0a060906020307030342081f05060409021309020a1707050103090c031a011707 72
    0x140070307030300c2810700b5107010000d842d14581144260107078103070080c8507262040070b56036070030600142c46900e62070007a09078000100b4141c42048203110304000300c0d1021485039404003041c00010f80c0c5d020003500041181070810b8025059602c0c080c104003c011440ca10b02c0154403131441c41c0d444c1d014041c0401503135148410080d5001070b04d041032040650801380c01410302148141e4281c45064803210100d40d0980090f401040020806881c520b46800c00c0506400680468a4a000701e03a040200103503483c8a0041c00804040e0707a40c035034801c1c5482c407032002c0401d903440200244050104006d000e10745400e880200100c40820700002031242c4001403250851202c00b0310b09010030282e480c0c00c5004041c000c3c601038200341c407009860010b0383c1b005550028411007401c005038070f00306401071055642c50744e045101001503454030340b55070100004444044950918010607001404d241c203032010402507000900e0b60202c29541c042c00358000c22400d0580d21501040c2c9184c8805061543e0b54501c24841e02d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 952053417 1250 952052167 952052183
    0xa0b01021b0a0305060f1506090616060e03040603020d0f060806190213030309150311030a0914010513021203030402010f050d020c070e09120c07050d02011b050a0b0a09 74
    0x1140749840340c008900d8201000511014016589803242070408004076030303841111440c0710420200c0c52842c0700d41620b502c000d5681d0390a02c0d00a00c04100107100d8a501000c1c01c981580ca020300f000307416040300100003500300590741c82e00d41d1018058040e40141a0460301c05040141d0034440ea03015206640c200c49001c001809280c446d1842000c416503801d880c00d84694007001403519401314015203e000318400d0f950b50000c0c40c40d003600303001021a16058501011300b840201d414060109003a2508002d1506e4000f40d0f14505141c601042e542d0014001320030350903c810001980c0300a0440140140256542043d02c01070402c030580380e120440e80203011407030010401102d41d204038040c00c280d401a03030740145400303000b2480d545040b0080d4040c03200700081d03908008104009000205603080a000c00030f05007500c51503d00c0d00d58045008550007905804d03558002d40e072203152481c520b01415070464884a0050401603128045c0d600107840e002591004208041494420070707000c00d07005441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 952054667 1250 952053417 952053433
    0x70906230904020d0c170601260a02190306090b09010b030a03120c0c020306042103111b1203040803010f0b0702130507180e0a1d0304150c0602030a0f050a0b0102 71
    0x208561070790002c50991700e621440d41c0c041442c140705128004045001c00041100c0c1d0301d000b03183c511008600b50090710a44824a96040c21070300020341365005941128000c00000c44c800a003030403802030f94401380280d400d14041009111500403180d00510041000b4003160b50b812043c5592010010401030001e003d205549084010b20340c4180d003922814034103807078400496000a0310f010030559096900300c0020f550500120302d13034a10300c1004a0385080c14426900c550455a645008020403000c0c031a810880c01c0c004004240a6013082da05461a141d85901381400c100d90310350404d000c0c403ca041c066841c02700d6001002000c0d00d044907070003020031071500e01c80030385030b000340c04041c0000040c051107101e40b08008110050007409094852540c1c00c032490020340500588640080065008034400080540c81c09d000c400c6600391060f4111030070003c0c5003604120b40100c0e284901621440c400301c00d01000641700e80042800360369101d03042c40341d600d032141c90208860141203050301503482418 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 952055917 1250 952054667 952054669
    0xf020f1009060b01050c2e0e010c022b08150301090f0b010506030c030604021b10090303111327021204022e110109050303160807080c0904020c0f07090623090402 71
    0x10f11308501031f0b0300e8008410381c403100c0e1200c0825200310141030070207a5101d0302170101c041d5042112091601400085462095211001c2a41442c522400408100d58040020011a9100c075071506401e070280003041030390b540781000348000040d20b1040b2100003089000150794501482a41d02850441010074a5600c5041c1000700030342c071902e21400e031206113402d00c402003613017400a911031034100070010540d038070b451038010200c0724118440850100c2c01d200f01c000e03081451508a09941c2030340c9002d605220708600d500c808003180d01103003038060300010b54181680c0a8641c2e2f60f001d98030175148144000b5205804481d00c0c0e001a0004003142c2041c2c200381c205610520300d02a48020800000a07512440e0b01e0705421340e401150000300724100c0088058101d607101c030440b41e001c052840c000030a03042c1003000c2c907031512590440c40c2c4626008589480702803020700805000c0e0010008031001140c1c0c40c0040e8024105920450288190004ca001c118403000020002c0e450001060304056913110340c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 952057167 1250 952055917 952055953
    0x1080c131202010c021801080709090f06051e040813060503090a0308130204020304060606090506030709090b121506030f0c010e0d080906030103030804300f020f1009060b01050c 78
    0x80c4050741003103e107411480c003507101e00488034481080c031181c0320002c7d81482c071700343d284c10a203500c5000c0a92a00c07411101260303500c4c0c258a83d1992004001c1035944503061410701814155022b45081e1413000e040c030042080380e600030030040c4044000a443d01e503681000b80d816000c1110000f07510f0308030344401d5000074490860554005550440d04030420115004076003241c00446007210440d03640d4406101840d0050003400080100321285880d618020100502961440c815600c4103038031000841c810340c1d920541c58030014103100807503180d182c00e0b100000e0400c60603511103000b80a41c0707021058114000c20742e00e04c01201a141d45d211100408140800070f403204000b5902440140704944030341d990400214021402560b070541107061034107244040000b0400340c001545054081e11566050b011070320304401e00c5504203410084070b150010b0303050214070b9205105a0152410101c0700742003992141e030001d40280c2040068185400041d00d561055409881c6e65034000000c1c21001841d40d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 952058417 1250 952057167 952057199
    0x60f0809100c020f10051e220b060907020303010f031b09361104050402011103030a09031107060822051903171b070f0b0f010501080c13 60
    0x181101c009040c081444412900c5001c1240016081800440c0000d84200b080041c140d80d012402c12103030610b00c2c050400c004004800da102d01ca854000140d48546e00014004c6801c1c20001c24035581130646030041000b102152070504c1a0022008960498030000959042c0c80c0d1042480c08124156140c204400b040031040b1080b03d07034a210041603900303a80c002d2501507940303034110300b035148404400551b0220a801814000d0260701c24804003140340b00740d041d000c01c1b4099500040c0c0340c5031b0380012101c03154039815041701c0344000001e10014801603402000301c04d000e541d03026100c3c0b81003044903440702164031580e4005034142002c6500c0482c00c800023241c5440d1901c42c0406841250f0710740b8200b418000e0a01400d2510300c80903014075400c66080e1000c0404552009030600e8401499103a800842c80000800940807034a00104520b1005c40150180c0108503011280380484902135404001d000f443d000036001ca010481c0700c04010140c448900000310507042032814030148480d0300180c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 952059667 1250 952058417 952058431
    0xc010e0a05060103050d0e010905060c1e0f0705030307152415030b03030a08010918021f0f05030f01060c020a1e05011d01024206030c0901060f08 64
    0x1888002012400041180508440c40307940940007030741c034606003d803c0120381603e030300a02040d03034142e003507513039001510a043d204110b41944d110f40043c1002c41c5407080d008440d04c0401c03446000e99800e0640041c4000801c00a007007155420b41d281c07810b05442c1e0095102c024008088008580a00d52040d0855a488450310000d081c3e6070241013040f030f04100f00c1ea84240b8034001b07200f02c89520a6494025144400300c298020b41c54480b03014001425403a051041c040e0140d9580004010709104807140d10146800a00d04000b203e41060710031007084280d040710020440b500c2072004070900960a40384030305190b0300c2d10202d60380303003003025036405100c504220f034030403a440c0c00416180c03ca02840800106d40c0c510725290b0a061a0001d04011001301ca0704080702100340100e45580e03400541d001e181c1725000200305040c050142074a18103051610749561510885200e40c50340d00c040a003461003458210101c41a00030340409125070403000b800b448000034a40c040300b40140340184189500154 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 952060917 1250 952059667 952059671
    0x11b020607060b03030708070209160804060b0f120102041e08100f1407110601061d1504090204120303110306011b020307030209161d1f050403020d1401200a03020c01 73
    0x1400001d0942c0c0c04040c2c00c40380c035503020800340305602b0030740c14040d4091a0132503104864000014080c1900400900007050651120760300300881e103c041c05121903003405000d48440816403503000e8043e411a00031000105520458010b00801e104640d0080303441481c040c0c0502030900340d41b00c014104611820304040e40300e050352a048500315040718420440d50766484810720070621070a0904106034060420840d80081c2c0b10b012506e4551084d400c46800c46011b50000c400d421200c420303004907402020350b1031000c54001170710307105d4020542c000d520a503010000c941c0c0b010307001c4009010070740d101c0340050f0b1035008001003540b600c581c54002c00d000034201e91010765294002403010908880e200c01484000d0500240c050300082031501340101da0740c01e203001d01461004660b0f889a40f21101d06211000182d03540347c0b034040c800316000b5607000b414581d08003800742801d146010341481900f00d43d40c47d0540a182d6801410540444dc08260450a103412240c1d1000c8002c0d401c010b0207022a55 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 952062167 1250 952060917 952060931
    0x20f0f2409070f0f03021c030f0c1a0702011410080604150b030106060f18080c0d030909021801090e09070e1f03050c24040b13081e010b011b02060706 66
    0x400840b0f001c0010402c41000150903410b51051001004081040000400c88142e4400000f40c101a80306031003201c92408041410450429003c0195068000500300d2070708410f11040c07580c103402500045821228022698440c0580d10072841c030144501480b0341c00981c00300d00012680740745002d41d400c45c000041525000700c800a800c542003a0320a10105002e1174003200c4080c5c00480010740742804403801040c851070b004020340c172016209412441030800c0da41440c1094000d00d1004007400f500002113445000300c176072006424412050080c0881c9c50a8400500a052601250301c00c1c4846005400101c2c43c1c046101507401001c0c008180011142040410b0f403107201c144000114002c800503d908044001446200d510b020130003200c510341708600b0760b140e115000440d0101c0b070788201e040341c1d00e007407010700f07013400311146d41020100d0b000e046410050518410a0150020b40e42c900822804180600540b01031151507203881d130140030401400090300d042c402816455000320404110301c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 952063417 1250 952062167 952062179
    0xf090c0a0e040f290d05031602040213155007150b040b061207360f080a0204090f020414090d0203070f08070f12020f0f240907 56
    0x90b50707107000c40700514001108850140c11102c5180d500084060b1000c9611500c580c0300c01d522441520766940d0008c1e8040c054030215255039040359010041040b10f16941a10343c9042170110444607140f0000854046009403081c03c480507120611003030040c881840b8410030807919100d100d119000d80382507840300300c1e0700b920855480200b0071a4426526048241c0101030300c04202d40347d0080990080e4504290741c09641c0300c85003221410441c82d0000403132603444440856501c1c010b80094484120408400c1d507404401802c1c0c100b0b514010500341e0440c90300c7e244d40485004481c0700d01c81081e1b0080346c804015080030b60103003000340c0c00791a0b00300c00e1034450f40101c1c060340c510b00c1e80d90100c8401241000505502031068205a1086202862610380c0603111401c0c890034408001d44064000544502000f00d006c803c2246e81e6070281e6030099500860601035107070301801d4110341150048030300c0201d5030000071516451440115051070203622981c4003a44034210f00400c440d0071751051401c00300386c3c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 952064667 1250 952063417 952063421
    0xf02070504060b0c0111040e07140c0a060f05060d0b01060509041427030c030a0e030f0f0c040b01090b0a0503090708060a090614060109090c020a0206180f090c0a0e040f 74
    0xd48400c03c040b030380c0e03200e2421140d406c64010800b0305022810a01c02401061020300050340c2101c240c2c54084d6060b641041c08007030a110b0781e4040c2c020b52207031040d07000400c500c0d500803404900d101502000155204018082c4100460000409415070240107022050007040680700c4140c000c7c4c070000740c0d0f580408031201415016207400083c20802c4690103089072490711030700c030b981040c00043c5003400c0d04a01959035901a0300307690418030280903d600e170360751010090807049100d11001c0700c1c2c0d5442507482540d101c00321a20742d1401039003440001e00142d4040c030042c6c1c00302c4080030103051401c0115001201e1a800c05450f8003e107018503140014408000c028182c020040804005000d041d00c1c03800d401198080e030f000254060000d17007003208603a0800302200407540810b002013081500aa0100d040010300e8074000e600c00350202c0da500c1100b40d8900e00d00070898058801002e0f0f000d05800700701d1503440480b06419a4a420064a0221442400311803840c2034084d001007403180c0341d0710f05401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 952065917 1250 952064667 952064669
    0x40f02160602160c1e15050306150c0114010303111212151207090f0e0604060903050c01110d113112030f021501050f1909060b030a0c08060603070f0207050406 70
    0x1d1250001105c2c8012200085080c5d00280740e0005010b511014500010300700303000043c030782889014094003461145500300e00701e0313905820305802005039005400313502400320000c3c0800c0e0001620b4006104e003100000603503007101c10201c00d50740d0401c2c0350f00359540ea81c05c000410a414080019150044645520340130303403c954004030141c0012400c10040c0340445140041c0141014141840e541d440c8070b000c00c580343c0040d004040030582518508042c0d0b4640700b0b681c20000d40c2e41c40d0500e040d107a0b10644014000381c0c00204410701c481f00d22030031500191b006400700c0c0c070002c048060001c0280000360021b2410020b003044c407822616990b100c02d901c13104a642040e80880c60f0039105032066903041c0803501c4a49100f8064000950600000c80c1e1703020b014100040c000d00c102408424114100321840000f01074004051021644030002c9410b030750015604181c42c181400941889640100c2605104000140540f821580d5400003205c000c2401c511a2044d4000c0100c0401c00752694060700f4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 952067167 1250 952065917 952065929
    0x905040809060a080711010b0a0e130804151b05030405191802220602061914010621060b030606030c0d0e1b03030f37020c040f02160602160c 62
    0x50042e1a0170140900480300c08a050030315a49450390882d50303503954109210030703500e0703603503440102c0d17507429004618042e0242d8001e0300f040c0012500041128820301c030300760580b05070b540310702000600341000d08020300119401006a0000e000a10071800c000c1404088601d000e00014940c035a9802c420100b80e100e218502d2400350000313403c03848114540d40f05030140a500c10703c032103000d00e000c074025110940503000358408005420714544070041d0303030040840030002400c8041c5030b50303540c0805401441c3c41c4494111042107203081000c018801d1003590304031854104d8035481c5a9030705042200c1c0d40d2009200c00c014200a0003d5101030310b50f4840c091406c100500100680d01c01d240104482d48244014140321754410800e08a03051074980c2540c20700400329601d5074504c0300c08002d840350b08181014412007200303891040188503070300246103585031390159400c006401241c104d090582c03003a921854085083d511807140001c10340e0303006054070707030340048510001c80760b07075a03148600a082c1c2d002c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 952068417 1250 952067167 952067177
    0x6090604150201150506071a07030212090f070803030906060d0602040819020406090c0e040b030c13020307080708040f021002030412141b092206020403050d0f050903070905040809060a 81
    0x136800e6081c0c01c081c0207440d0480e14141840180d03a204040da40240280340d254194510101d01014001c0d010b4a202c1010051034032890320301400e800350741d000035800084040c400c1600001341a135020003141e025040043c00703800e00369070312000d00c1046002d007003003200d400f0350030800094003c0003030010080101607026801364100080c01000305881c565000303440e8036450059905030542d081100c0c490303181400c2c0c80111318041c54100080c241403001440e6070704102644000120b810096005521905076900c440310907444088085803403010807030300100303014100090280075141c1640d0740301d4a80120f00c1124030b001c0d150b1030781d4003061400c000b0803180c5504920303600b40541c200348060080f0301a0600d04039010320700000061010381002d071022003090741540c80081120b10b00441c03030502641252055554583d240f030702c80d40d148000006000010a2141448221441001103411080d0010020860941400500c10040c0009001168120300404c003940c6130351122400ba1a45c80d10340d44074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 952069667 1250 952068417 952068431
    0x3030d0c120e03040f03060e0a14030d06090b06070602031009060b13080c180a0609150504051e16210b010216050306040f050f010603060b0109050d1106090604150201 73
    0x881d805503442d4a8005005400134842884150f080105240031203400c100c0124000100c040801c0c1068500b103c081c1c00e0310301401c044007180308004001e21640a170207000300b004542d6903010303404407580100000d078400000c200040c041085600699000000c182200c08201c2d03540b81c4440441d046a031002c52880b101154006207009141c004200030100c0d035015001c100c06000000f41d507007038800d0f000c4020b4000ca1001c22452411031b4007803000361901440c20003040c03000782001002c0400511420b0320490400740021071f02d008076481441c16550b00c002a4030f171910b42e4141c208005519541120412200c10745010214210000300c5141440900d4000b5011071041c00090400402820040c83c4e247d601ca000c101503140000d01d581c0c019000122081e0801f01850160304150108110062940c2001c501200740142980501800e850980b10502203e5480d001d014002402c100c000e001d9002c604180313070340b508064005100780300000740341d40d1a003500c0311500441d12242164010050790f55041c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 952070917 1250 952069667 952069697
    0x17042f1e030d110a03050a0203040b031510110d0f032003090105010b0c0d05070c120c0e01051009031e1b080c1c02010309020f130e0d080906130203030d0c 68
    0x510281e0110b1840c00a0006003406101a51949044002030400c400040c100c2c280a1003441607402604110140e641d0302d04100c0c0e08440203103241c9140500c0340303d015984c90300c3c2a002d0302580051419a40c00380407540042d003015161848820b00d25018503844503032418140808000d0303100406141c83d02ca07510ba05010902c1c50840d48140c01c0880212010000288074903000035480303041c0c0421385000c60351401a49001c022000b09940705e2010b181c00e4144110070000c1e40d6141c0ca05072181c404501e0380d02d0b0303695001c02844042d40300c04603000c581d0504050001c41c1390380b4040d41d0300014000034000b28075034550b0340700b2441450384024100310807580d03014400c2060a1204c502ca14104440e45440400d040440c0c001900f181c100080c140356071101580119191100c9002828100614162801c1ca1410b2034402411030074180e08040d000e00c40d44000c40f05c0c06040e40c1c40c090706c21000200344958031001c0708019141c542d035059926100038812040c8450440c0108119451259580382500349264 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 952072167 1250 952070917 952070923
    0x1060314060906040f0b0c1b0c011e09120c030b040305120106020705060307080a09080c03041418280501090915050405061302042a17042f1e03 63
    0x2d01800342c00c1e04624284804100719007103810440d03801011012050701c07580103007180741c82011407049580021081c08190802c001c505100841400c0e01d1380711001c2c02040d810081481c1c1c1440c00d80c046142104107001c03009600030340c0c848541c0b25010111203203480762184290800c040314102c001610002d014600380800c400c82a0040000740000e0011a00303010008000340801007040e8200190303a80000c0041581d90003a02e4140c1d0802c504035a40e04d070b92142c0940b66449400390b5061450ba0140b0700c155402d00c1102000c003903070b0303200b10910310351035408c41084208000284c000660041d0b0018020301410f81c0704d4240201070144000440202c40d02d48401c80020000e00c0030920b03890300041101040002c030b40141c0c4600e003150001c04026035880003030000d1a07441150700c0e030400151200801940034646801104006840d25801c000d4000714030a42c3d5403049600811922180c2854518910540c00b0190141c040b0100030307880c094884081741c038040c1618410f00d0718800c00080d0038246d04040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 952073417 1250 952072167 952072171
    0x14071202090319080301030c150f0f020a0c0b04060f02071a0f0f04091d150103120207080a1a160c0303050421020c1306031113290307121e0c080106031406 68
    0xc071610001c0b42110150107015000d50a2003d01801140bc2954074910f10031311401103801d03400800c20720081d4a440000c491500113021301c2e40030401ca400c42411590001460000311043c2c090b490062034144600404107400c008001400c00b40d041c01081c1c1c4003080c1c0300291010709014200000d0150aa809400188258540c7e0b5142034000c8d520030320034200342410660540740c01c00c4050746054001001245000c2c095841102c00b4040e40c0e086508010340803c4800d030201d0014465030340c0b510340c502e5a84940e0000702d190004100c6110410380080e001e60402d030f1340325000d41000300c0030302e000c14114510425583e0760400103030041d54900b40c0924095420800303d4030700d05c6040040e5411030313452440301c15010008921a04c6110681d0060168507040002d141c0225008080c00d010f02070000d2108000a1013030510a004400d00420707092400308603603848179000b00e0202035110190050400000041805442141c0e116074003048110090150300001c601c5204c025a1143e10403035420300306000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 952074667 1250 952073417 952073429
    0xe12010c0e0f09060d03050418020403020f010206090303040b07030902101101050a0203060f04110c0106061d031c2003191b0b01171005070c020414071202090319080301030c 76
    0x200c490010382d546a403461568409026a01c2c8121050582410348060155901c402c01000f06816000240100d07a0041c2c01120710079192441c0f050075a000590700d4000413140740560358000d0000a0125111401054104455007000154110703181c0224460819251055000c1481c46d01d48451429092040c00c0e440507200e881181035082c00000221303440503010b507051050382c58a0358144c041d14000101c980040a0100070441d40e0b40c1c031203002e80fa68507040828030180d407140f0303540103481c00c000c11554445038894690024640c1c400c001520304c0d5030400168041c43c1e118400103801c0c40d9041004040c480240300007100120b203202c0000f085551070440021201d01130351628000035180c8091941036494070381c1012043c1001162980c6411800d4041021280c20601445407140d0400c0c0c0f520040390080d074050048103400604502814410340e54000001c401000b80f041e000a9075000c0c02e48200e00a00741c81c0d0b480c0c500f0780304d07a50000c10802d003030b2a41da500100410800440701141070052107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 952075917 1250 952074667 952074679
    0x1150809010c090b0c011509091202010203060a03230a050304050a17030406030228090303140324040f050c0a1b0f060221180c2b030e12010c0e 63
    0x2031100b0010200b00741c80c403450306100390100340012840402e401818880e04d44003001c2966a9a81c01090054503001c082038480722240c41c203403a5464818000c4038840d0102603c55210b503461980d6210161445e041d65042c15142c00b00340080a120901c000144103000b900103584860502041105031019a2f2110910490000a14039650404015581202c0080c2001030315040c01480001c01c0d4846c0034000904041c9800f40309050307507040203402c01074138060707900c4100c0030b2606141d8010910040c2d43d04050940369917180780c00e03001d5116842d21074040281c00030456600204140c0d00ba52415a40748030300034008981e202c2000d07070044030001d4820001e6400c01d04803019890300b182e642404003000c9c00d42c84c0c00242c0c40011f81d100e0486942044114400c2808a01d48582203440e045101098840c5501498144001a24040161501c030103010401520880c42a0062101074031061508600340071a109003426a540c03100c00210012500ca4004126202c07150300090000034a160307947d118003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 952077167 1250 952075917 952075931
    0x3080906060a0e0109050c0912030a3902060c15010510030504170708040b0a05130f1503021b151008150613060503071d0c0c0a080a1103030115080901 66
    0x10001103d5411100c100400060b65122081c0a40280c829481d040790881000100340c000d040c0000000c0403510500d90b12540011080130b5410391a05681c0040303184940c1c681c6a914600d02408203104161741700400e428500b284600105003041490300c003030200c1d624103900400980c1080380d98051054031900d03041215240907943c0c1c0b201103190303030100203a100011448500300180241210041e1102058198403003c0c09440140154440048c0c01d501c04000f1800041d00c007280d04d42035058a1140c5036090301e0451a04089003303401c000d614880e900303c0c401001004241c03c3c4815a081e8802000005661810580c04844600254414480b03540030061205001034894005134100c0c030100c40d04580018200d000070060029600010344c1130080314000580d001c4c80d001c001d420000d5800d8121140c0d03440c0070800d401c44c0182d1a00d55000d40140e00c1e11000250a400101003003180c6051200c440f96181c2c90040c41c5802c00d801840004003840c3d61f0009151708031844541c07059042000780144 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 952078417 1250 952077167 952077179
    0xf090f0609020703200f0102030c0405040c020c10030b0d0b01120218010e0c07050f100e0c03030c070e13050106090f061517180a050a0204060b03010e040b0a0e010903080906060a 78
    0x51605c040c0441e0b11314070300280c00e10324840b080c000308a100c11404000d40d03c0f41410043e58030b403644940b14862003289803810800b41030740046148821070500800701c4428454200c02680a0031804803842c3e800505189450001070b00b084001e0f0180945400c4901c0200151040c8a124100c0220b44030a4405100c010407490600c0c1000c1940411600091501c5075410301d4500e103800a0500742000901400c428120004030b251f2128114010010031502c0305994102416164842d800840c0040d400c410b60900c0400a10381d00190054007440350040103003055203420342110b06540024031010303103c2d000010b035414140071310000b900381d100d84100720103021403014002c82d540c41910b00a90380401d0000d1710013285019079800580001042d9070000b034042c03428580300c0c082420120302c5a89070035004100b0507010029241038880c0940a8481d544442c0c49080b43d8850050138680c0594507039004002884082c041d1400740c030f2081d02c811000e820940e200ca030030900000e0003207028401d202406c01c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 952079667 1250 952078417 952078427
    0x1008040804031104090501020c010c18260c0904062306010e041121041b0e070309050705060f12070311090d0c03080c032206050a03020903070f090f0609020703 70
    0x440ea4050184001d0f2050500803e002e884200343c00342155202064061554106400490250b00d40d9510000b09006158081c80440100e026032480d440d5501c0d82c1890080210700028020082101203d5254030a0000166086000c440c03c40748a6150b5041c0c4801c0d104082482c1071044480300268110315006000030503070280e84689a2065442d9119402c004404408481e0b4038280801001c4840d411001480c610100c20384049510100d054680940c002c400707802c450030340d4204121300d6025110144120701500c40b04100703546e1400750403c00111baa41e1400106481040000d00b961601d42c01480c60a035050001e01a200303241c1071080301015042050304991100c041141c201c2204001818044800d000c0c90b000100410000a2450480d80300000a03190024410501e240c54503095980b599004900d03208040102d80d080c403111452034044e03000741601d01005800c498505544e001c0070700610b0000d900203086d40d95218003070715a07681c540c014400070704030720182503251031500d03030300101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 952080917 1250 952079667 952079669
    0x40b120d18050d021309030e03011b17040f080f040b04090603021c171b01050112140109080409110d0507050c120414060a11030f030612150c0a210b1008040804 70
    0x3d015a9504c6c1c0d00c400301405014600441c00c0060020042c840c2c03000c0c1210030061641075058045100200908030943c409502e0070700c15079011100c640400595500d9402a40120a00708180d082c140b1011910804800141009085204001c1030607840c2d4014000c810f068010300e00c6100748051004400b1901c22681320490103040e810540d0303614902259401103005a840070289542482c0000807801a0100021000350040b01d100200001480002e4200c0d0401e59004240d2582070108000002140d481503001703604110881d441c21043d0281c00d000c40b034040318000041000800c05410794201000030f100400f8440110514003810211a5260b100507680514402c1c0e1000540d500418441d031031084151586400701e03074075820300c1c030001040c41c0c00450b040c41c09500b1003a154840594002000106260503003690140d0f0b0300c5100d40f024140c3d00515485041c00200340b40c44195030307004c002d00320b58180c01120004243e926030342088159060f0101600400032010b090002003004101110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 952082167 1250 952080917 952080949
    0x4020a060c050706112b032405011b050a141e03040302060724020405040b010f05030403081008030d09060f0b0a060c0312050c0307080106030c020309040b120d18050d02 74
    0x210151020941170340c43c01002c580340482182400c40343e0503d800c040329260551400c00c2e10180202c00e00000c03c594802e50118581800d240c016108128550003504010307181c0c0c0c015030310022104916183c46140c980d0108089440c2880c4860401c51900144002003a4146100790f26011040040f0740c240d490190b400041d1052741e000a01c00100800701c81d45106100010a0100115107600f420f6402900305100d5103025a0803d100c02c8615231144100d8507140b003403034a41e607003552620b88046500c0c0c68010710040030041150008914050104003034002081400c80c0440d00030704c9454001c0980d11480c9100d0b50490a1900e42d18140e541c20244000707075074282c0b03400d00034484e0ba414200c910850702e400d038500a915020611250002c814002c7d8410a101d84442e405071341d07101821030850b20640407000c010b820500804085203003541107240035000061681148940001031241403002501588000c14002c1c0420003d03013858200e45001050102c82c0710041540c15008500019410743c411 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 952083417 1250 952082167 952082177
    0x30f070f0315170a0507060513060f170910020c030904140402060715111602030d090b0306041109040f0c11070503030a030525050a0212180d03020a0f0b04020a060c050706 75
    0x6402e0020041251110b0150417000700d41020b562000b0123442d5900881ea43c0c3e80c0c900100c2408140705000d441d514008910581e600c1e590410850140e000c0480b010744059018051b100705501640c0950010b0070390f8800c058090f507a41c00c40501040100c806005c41c035160360020108110141e030b20103055884054000c0d50710030103c000e01c1403000041c001c18a49225200011410000f440150a1301581c504c3c803c0d8201d5421041c004ad090354280e000788a50ba941d43d04c1040040d01c203041981144001d440790720b501c5420560799500040540340180407910a0a175142c9201d403019501032488070651003044007a2840301d09081c0401d0700ca21411090506141d190004038803001c0b0518101c3c89035500d10303400c0580c9055000c6000305594000c50b0980014400c111000207100107840860303220080f03404107030016550303e6041c0140580349c10000e4082d030103500001004907520041945040b03100301404a620303c1c10b44100700085090340c000101700810000b0385e5002130400624101513070043d00340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 952084667 1250 952083417 952083449
    0x140a1e1118010210050103080306090123060c0c030304031401060b030f0420030a0309030c0f0f0519050a0306050106080703020a02030a270b030a050601020d081603020f030f070f0315 80
    0x50303107801c55144c6034940c101d01e84400001030221500c042d6000b10411560760741700ea66100300480048904103813001e4580c81180701d48186252110062083c2030500059074982c0050344000303420f54005910a84801e0410b0798400b980250030311481000c0d001c42402c541c118142906141c95540d801040200b04040014440800e46e82c484565203001c00b0050440e44602d100d171400406002042c403045034001c101c800c0100cbd40b00e01c011103000903102802800c4905034076040400c072484040c0b140a0b12501ea00800c082800d496603101c08000c1d501510000c14030b54500403004024210041000b000c140c818001c04a00c07583c040300700d1b80452a0b03494481440b041480700301000454000002074459100340c8006112903017803000d9807041c3d403489810041aa112001680c440e040d61031141d0016030042d000038041e1030b611080324030302c1303149140050030441650141c0d0050b903c25031380400341602034002c020b402036002c52104143e00c154902480b141240c41003628181c015805103090b50045021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 952085917 1250 952084667 952084669
    0x80a0c05030129070b041a010503120f0d0204151e02060106050304021e1906170c040e090106030503040b04030b060103140112020319210c05061504140a1e1118 70
    0x9582240d034010401c90f07006e05251421072055458074458440c008103640001443d80750204140b88104040c00001e41707044046201d40c0d41c3c6a003c0c0f0ba844440325424040414254611603210003442055241ca41c44400b40c006412078000403140080115403009005201190340310054a42041d41035455019151101000c070b08808896848103401601d001c40f2405240c101c41002c00443c1c0c0c8503181c841800b581d003000061103801c12556515a079400704000c02c1950b0140c0c0700a03900514440000480c0e50f1280e590310300390f1f88280e00c0a00610808602402401400d0b11019009802400e0410241083c12500da40d4140705202d0a000d01402811000075502c0522500954241c80c844401c1d07451440c0c0340094000d0040c066100c4481421003c0e41d64850040e14070412072508000200542e98820207031030340031031400d078038686c00c50f03146c00c50b03142c000498803400741c0120034040d004334042c0c1d0180d2401c802c6e0079003189031544082c20007080c0b0411041c4001119020189420507070780d12a8098 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 952087167 1250 952085917 952085999
    0x240b01091517040c0f0503061e100b0a0921050d0807030b040e06221a13080c01140604060b071e020603010608060301150303023406080a0c050301 64
    0x180800802c070085600f04020441c10714a80d005440801030364401e05034580040c9940c40340e04544020756a603090052030303060200c0650b00307640708041601c11100b80b07454040002c2d503034100c3c81c0c0120100314030b041d0074407500307010062442846030340401181071500c3e20303281c10b59100ca0907030005c8140b0002d200481d105500c03e8100212010f0050800e00a2401e02c403025a51444100d40401640715800c0b1079460090f001e03107003500e101d5003121140c3c40c28070404090083c4540b010b040e0a80640070000c1c444005441c0001400d030000910000154010004040001c0410005c012900c111315040301800880e00103c280d8500d00d800ca034141c0440a42144000000100c2050207540944080700004607607071700c4403a061250708141c0003070100061101c0d1200480089000c000c1c096000500210302107141d0140020b81d100c000181e002c00021300001d59a0044055008030002441035810008201220f00580d225890341d45802e0b071541d0725160408a034020b120280780101245582c0142901d0404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 952088417 1250 952087167 952087187
    0x30913110a0c140a03091a120702060702070609081f0b060c0a060b0f0f0913060c0c020f06070308130f020a060f120506030316020303070609240b010915 67
    0x540c640681c1d0300710510019090306115078040701e83e1070300c2c8445403082010200d00c01241c684d25440740601181011000d580714140820f40003949181440310040710802d102010780540500e030050403075070400c10300c02402c1c41e000d6000038050046a8030100a8030400144080307146601d8041d1310500504081d001c0c01070b00712070121503800701c40420b2002c0740c243c002c2034580400344a007900300174101d6481c0612103c03280314009107502110011310b00d2a94100b40314080e41c402040002c0c103001d484155140c4088541d085816000155485c20f69011400c10820551281d8400c03110181048126500141040002000ca00041140d103244030100043c800c0d804440c9580108088091600d424000b0190508030881c0000034124402804011130f440c42807a00560019015601c0c000711641301840d80c41a11508980605c01048071030003003a03580c4200c0580034410b403121411246000c00c0c0c1c44113000203261110600349003250000007a80c205a02c0c80c21200c024201292114a042090b141e58001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 952089667 1250 952088417 952088441
    0x60a0e030f030c070e0c0706051302090f10053703060204081609020c0a02150d1506110714010f03020d0c0903030f0f14160807060903021b03030913 65
    0x386410302000048040041c0a064005404a40d159613650b901d654030417909680711070040d001001200c003c100300d0b4200304d074000b140039008a203200850340854258001203540c102001a070302e051000504042c14090000d041c200c9a8880e0001904d00b008090042c8011020b503140500440860300d80c408000100115081070045407600d07900d401c4503499662034000c0e414010884078000c84c1080441c0b00f5070f142065850010052907203035a0a000d090484645004a250000e20503441a0384950180c02031204440e08610a0a0726089014003841c090290f09203182d003011009015058000490141c485000d02c0c1c5400410130108007a0000c0c400d00e03100486442c10900900992a00550450700301c074801e688038010380010141c00c565024406c10302c940099005290321001200100103894002c46440896005401940d5103030110b5025000448249444016a0040c1901400340c400000c41c13801d80d0501001680000135101d01ca07419040707104110800244010039055440603401c141c3d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 952090917 1250 952089667 952089673
    0x406060b0304080a0219051e070812070b060d05061b07060606020c0f060c1504020a0b0304032307020609060a020106080f1e0111071e0813031208010311060a0e03 71
    0x1d281c03c1c00d8410398000148400580308800649500c003640c40002c09006400c00003070044d8000c20081c0080b0541400d4414002d8810000c001c80d2501040c4030340390711040030b4000030395601001c1c0b6006080034001407002e0300c03d203800c03032481002c00d0011590941c8071300240d03090740405100450504150044601c00b03420b007480c041c0c01203200d903000950308295140c21190401d81141074800c001c1a88031380030312030151ba0805219802d80214a000407a0007034801080c0000c040d03100d02c90030509402c120340c168001898455000001040c0b20039811110004c00489803502140da000301d15180f00328030669015900010f800c4408501c01c0d801040540440c0090b6000ba04082e10142d1361541031030a1907604a0070034022502100051090400380d031003c620017420000580c40d00002414503000541d04059160074100014101c40700a24003220020001d12040303007141071068040d8031104940e4140000040140041100b40403001c540351030844019a0300d540c007001c00c403500b04400083c80c2e0148 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 952092167 1250 952090917 952090921
    0xc212506180609031d1f02121207081f0b030a0f1406040c0228050a171c0504030e09090304080f0312090d0807140909040f0b0c0a090e0406060b03 64
    0x4030b42504581e0000b4080e070b903001118200141c840003843d14200216070f100c00c40141c540c145108020040b80340340d4250040d28140d90f103200e441b400c5907100185880310880341c0810800d200d9081110300d07802011190008411041c0c54581c54158481350003002d031a80301c003000040c0c2c41c12941d004200e0000f1041003c4c4804010381d00c140d060000242d8a46100b1800d10806842035031000441c5015001e5100079000c1d02d8010014a404001d4901e409803018080c3c11104004120100c200496080142c1d40e4190b0b00c2c0ca541c850710b04041f10745440744030158244424400821f502205045601404998007001911020b030740c07510394440e56000c001a8001e012031103002800c0480a0002085001c401c490b51b540c4002c00580c039034103090000004148031030017190784c8030f01c54800c042c58002600040d51802c4036140001c0c980c404101c80c211901c840019600080108000e042038002c550312503902d0070186501c2000e00301c0902801110402d951240000f01804a0341e00100c0060000c400001e40e28 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 952093417 1250 952092167 952092173
    0x30807050c01020705060708030a0f0e031303030f0305040809090a0e070f0e0f13030e0a0515070c0e060d17040302061303140304030809120c03030c21250618 69
    0x91501d030300a14050300030300300700040f281807040803200d000b036200700494510340c3c071860700400404c015951494116590041c8081d111020030080090b10f64a01c181d0141d03e20f90f1400034440141c3d4031402003010704040c14800080c510101740c4000c1e040444203c805a034070b4100352030080c108961280c0c40c9103d103500014100511130608001da41080000c0c56a07603681000100403800140c84401814202420b10783c0400d03c40c6040c6440202d00811010390a5540e000080c017208810710740088150002440904000c0030701c101100404c0030400d10b46061916000041c054030035130304082c010039100c0182081031244070302100d0145a008240c00c6c1c4170302d503075800c0d41004d50003030200325007000501503801d0303541c0c00000568003103076800940c05150500d444140720200250034a4904103101d00740d00f09540b940c0c02d201401410074140c00404d40a1701a548400200d0344c003130710340058440300b00304036840070100ba190a16208080a00900130f40081d141c0b82c03008041d5031070303420040e03100030010000f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 952094667 1250 952093417 952093423
    0x40c030b0108100b09011b020d0c05040b120d0e150a051c0b0a09020c01020705011a130b061b10050903040e0c130311040e0f160b040614031003080705 66
    0x40040c0a03a1000c90558600b880802c0070543e50144001071501400722420325032007000040d803507604c15440126000901d9012401c590311055046820440e0400140520b0a083c411f01c61100000c030b51081401c6505d1011b141c07100003200142c410003a40505010090b1070741944194a000003c8800f80e4800308040010880d8004020110703020b110040c0161910207140280240f9140040c03106603154078010880f80203500c910101e0030035540078450300000c14420303c20303101044111a458051f007105441003200003401c8400d0008070750310f080000001030702e0f90340a40d01082c8480f40000b281e140051a010b24120b90000141222800c0c03408008003004007102038800c9640c03803003403103069840da40f8108545000b5421041441c526182c020400300e101805404103501c00608002140c020b01c1d1909400c0c0001d0350203003425940705480c200c00c000592001040217200d038603401400c15085c10401001030100e22464030003805c0c0030020034180220151420015a40140c1c0280d5a00b403174a0005c0d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 952095917 1250 952094667 952094681
    0xa36020a0311121516200a02040b0414040f0809030a0c240c02130b04060906081216030807021f091407060f230724091109070e040c03 59
    0x8010110389040202c40d20740050240d86564211070100e600d543c4002c40c00117060310703200e80d04e82004030b14072228800c50340c2550401031181c007540150240044a0040c041601c403140d0b500703806140341074100c16209000d51010b035005030744480b0b608070001150400f0760150081e03400c1143d2501801e41d0010810540d50541d808852030614404554260340301000c0d0035120880020002c03520300c00c841401464040c0f200c2044416074080000c140042c04013003011140503401c030384e0b0442ea5600041c8403807041000001d00509401c61036520303040809a545400500b1100001c040c4036010001c1242c090090207009104011900803014014843c0708031030150034070202c01d0703d4252046035100110000400c000060700d2690302c9400880c84030035400c845c40401790424000c2c4120803070304240340407016002040ca45008078911094211081030596040031a054240d070700038902020b00002444294282c030341d6610444190070b4603a1804002d0700d09005103c2001e604c6454501041d6981d41c040c0d2003e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 952097167 1250 952095917 952095919
    0x303080a060e0c0316080402011d0d1b090f0e210405040c08070305070e0102061303180821041a0a050d0e061501211808070b0f0a36020a0311 62
    0x17280e02c2c450072001e48a0031819640070b4005180380810b801410700305010881c04120140400c211481d00d07456a0605440c42d0201c012000007501041100c807065000c2c44811144810040180003015000980d443c000009184440d861042d044500e5014201c03d603402400054403d2041d07105810707004003503010848220340480d14113004142c8480c480c1001550310541030300204542c4e1101014040268690841102000700302020768030a00341c4820840b0050400c100281020241c010b0035008180c01f164040070446424801001200d41c00030300d41d907103a0340c00721943e6a41c600310381d0201c0c0d41d0b100d02c2245032041410982d0700b0a03003440c0000e049201d0f40105501c0480d1005080044403d01c031000f10140319151040010014032205901c001440b0300c0d140a1094135041e1031f90b4003255504503c10503140298610200150551442c0400d50301108000c03040013014120100800b01890140c59000342070a4040e0504220781446401c0048680080c95044030b107940f132a06801e05103524900c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 952098417 1250 952097167 952097191
    0x80313080a05060420151923091c0b06100c110909070e01060929070f020103021b060a0b0609180402130207060c02250303080a060e0c03 60
    0x14580c00081440700801e984400079208035110313074581c17682828208100c201450844155100c640d43c1c0d04900e54856004140641d4a80c004800013418110b440c41144081c00384103a007001c8003400585141c00307407007820002c1a840c0e07601c1c14082a424807195800c0080b0151380600c0c40c0a21184421140c440c5408035428000040344010480b61041080760040c5510020402c0c11410f1404400440d80f280c1030804840400307645a03100b400e01c0d502a440440440c0003000d0910081c80950403a00041492074000ca00003403194070900d165218501c8041e103000208018102168400e8045170302120140310100304240d02c6e00c50031034440750141e80101030326280c9100c01510307040030001c1d168040e5009118414501e181e400f00c1ca1310080c000c0080343d0201d0302c0800e09244080d14030191104501510001540c4920b414020b4600090800072240710160400391011180c2d803181c40c3c10903240d1510701404162203c5600c48003801c0e45810800c04100b520b4200114002a503010314490007043c0d402c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 952099667 1250 952098417 952098419
    0x70605130215040f03060216022e03060e07052a0f07150c021e0607060c08090a0203030f2a16060e09040201081312110f1209011116080313 61
    0xc1a45070320403407050080c500003594003080454201e5002c6d195008d0442c29203444840181d002034000a156841f5805c20314116040e011461486d07843d0380c1c20801c050604001150500c1600c1d02400d80090200c002c2046c001071403803208041404041e2806400d5a4820303c650707280000d17949845a01e030074501c031407044400001d50980b9046004400385000c3c0c643c5100e09902e9000d12500400701c04d40d000030071030f0001034804691581300003000724034029500020588404503008000420141c03150b62198490021000540c1d0080229054500c1407903001d503581e454108501c2401d03142c0c400d5000000c502083c4145803420201e030300303510030302480c9a540410b919a481a0b450310000c1018640105200c400100154083c00d000d0b40c01005880e0790800c54400c0340d0310440b074041070024001c0001c202240200090904104240c0e0b040c030200c019010342e00640f0349090007800b500c41c120341000600000f414038040180402c089025080000da00348580310300600d80e49034406e04144441c9030789410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 952100917 1250 952099667 952099699
    0x609020301060e0615090f120a0c090f05070509130b0a03020603090709110307051611040e070608090f06220803010f0e0a060302030607180503011404050d0c05070e0703020706051302 80
    0x70490390644001819007047c404104240300c003403400724000950030311459030b00001055610b00c0d810f00619030403c003c1078410b01d103c8600e0540d1000b610910a00c4414000f00b44599100d080f1500050304640740054900050070000b8203140841e880a900480c000007071101c40070010581c2070030794811500500050601000c4101c04d8401160030300c002500500001400d00c1c181c0c1b106d00740c00d50041c2070040756920402e00081c2103030740b90990106940d206071020461540c0000c0119403080805001d40300c0a100b0543e11078495a0040043d00c2e0b10b4060311145640d041e01a912310703170554008940c1c945039a10703034580b026400264001c045042c40104001030b01c28125010b00030541358040c000d0070b4540ca40c900f0607035000c10000c0010794030340011400495141c5003403040b64084082003104550600f0b00b410140c1c1805041001a0108003154071a02d01141000a0150459180220740c00e041d6030b840c541200207004004004140c1400c0c081400a02c4115011200c1454000c440d17030100728607801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 952102167 1250 952100917 952100959
    0x17092e18240b180f151003021c0e010b0f0303160b2509030512031021060e0723090726040c051801180c0302041d040c0e01140d0609020301060e06 64
    0x14207210746c80f035001e1031b84040d02407003600a0115242c841c41d16a41d00c01c040000720090760445e03511080180c1d92610140346030f10746881c4105880d40c0641c00b451600500c030802078034580100001070700902807000400c4850454405100420285000c00c0522100503c5c004100c1111440296214400c0c1c03680180c0341c403494421a030207046954207100714a890100a00307041c0958a000c45000342001051300d02042880c007442c150000b1000c0034000a504145c6080d140e40820000030000d2041c0c0c05401c00141c4400c2407113900414182046001001c000300c1603480144c3c05091005103070200c50501c004c00400c101c2c00c105503001192411060702c10040e0500301580d09101d542c449032408003031500702070419400000040f40034030707001d440c0c03544800441000c600705095019980c0804c0c000c11040c4107000e0781090150540c528021032139450000a0307070b45e000704191014801c0c0701030645007081020a41c4911180c0303601400030f20110b6a01c140000849904440300780c0611031320542030380700004903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 952103417 1250 952102167 952102201
    0x602060106020303060d02120d02030a0306091b030e03070c14090105040b030d03110702031b040509120406030b0105040306050a09020f0109030317092e18240b180f 72
    0xa0b5004600390750703550701001550f032510607041c2d0308100602d800e1710715008107002c00d00c40030185800865842c94207043c020100e61950744011400c170724041c029a607880617900640025a10361801142e440c1e1591901c0b0304600c00c05000525169081c00006803041c40340911400030041160500d0300c42c1e07603c1e414082078400c1641c03480c0d41a002a2201c180650003039011042080e4640f0b440d80c10040310f0703400300703252440a0103401c14040c11040700c94402e00d054020a6808146640a00390389050b8440c9481107024070301881d000d0640705c50356543c035070744140c0c242d030000c50300b04000740403505050300746000420001209030301410404200c55072a5014000320000c40f58195103040400560406040c0d0001c4007610b154468091188030301c20110340500980c80c2d1100f2144090301c000301e10030642d4100e6401040141300c0801122440001c1403080b060425901c8450019803000840440d04030001c01070341d403015511109000340080b4040300c090f2000d00c10a900c0c4045038050701d074144d51404800310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 952104667 1250 952103417 952103429
    0xf0810140a09050304050607050c1c020901060f140a0807031d0307020609120a21031a130e030c03040f0b090f100e030703120807080705040b16050d0c0b0106020601 72
    0x10400441c5880d9890703802100014001c0054034100380d00c0e0700c0000c03c01d40c80034405481603440030310302041074940180d146070300040c4000c0c1d800f0b04800d250b010400b180300500c20300c0140081d004a104095010b4107541405c0101c01032802d41e91040c00750060243d04040d00c0510000340b070f00701042e1a40004d4900c6205241d00b0300b0055040100f240c0c00c000003940041d40481d040a2003091101841c00104000d401451140aa40040d182405038075041000012204803c1608005004a0480c15107204442044090f120100c98140d0042520090b14546005034014030000511900c0400040040c1040c1d54245040c503c413103507204d2165049010b9005060340c02052074204804603c0c0169005900090504180d010f61a8000000c2c0c00e0102961081c2c820700f04142841325081c0d40002c0541d4800c415050001c01c50422200061040c000d5020350194210005003c0700300c9083d9071600d01c081684003040740c21443c200c180c0284010203800d0300300c44004072600042441d0f800881d1907816191 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 952105917 1250 952104667 952104701
    0x30b0f091b041a04060b030708150d060507110d1d040e10090f060c03091110090b030a02070602130311240906161a010611100f060509010f0810 63
    0x541c2004010040a0030ba01e1040a0710103529440d0580d21580550402400702e00051a201c0c40d0100c00600f801c08000e0240b0440d807400b15280300c1c01d9a401c0c3c0c0392200180c10050024680e910f030303101511070080003040481207108201c40c090829a0160300030307903601024020080059a0b01041c001590403070720400107207400c8040d44082d0f5889943c0f01003a01d501620700c00460000c03548800003141e95210010002a84035012a000d000604074813090383c1200f0740f009106001016001004c42550340203400d481d400010103d00114000d4040d80c2d030303041d0404811540d0b007045070340091070849507100c200c90101c8103030304c514458a0705041c2001c034030b440804861400b0f44042040c1080d40e0202c3c0c5070503400318050003803040d1002c2000d41d803030405c0c0c40b032034007005031018007401320703811910503440107003000380c2d0044a2556440c08a0380400c1c100e400c6601040500300d800c00000a01080e8004540002c3d801c400060106000b1078400b0403100000159545145160427100c180d445059240d002c0a1f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 952107167 1250 952105917 952105963
    0x3100303180b071707170a08060904050a0609060b060a08041b080304090209010c0b010815010911070609020a0e16031b05090d02221a06090d081b0601030b0f09 70
    0x1411081200c0c0c0f1100c0092131a4507040c0c0a0303564080e0154400c541c80740c01c22001c154921001d030014811034205400b11180261490641d841030743d1034000700030003080140c6852042d010050300e07802c5007009040080c0030540b29100c0241c0180030032811101074502420160500624000142e02d10003503802202c0a5031500e81004103c0c000b0350300c000000c504100f4083e082c880801c3c05840c14a018050a00c040c00d01400034601101c1c0b80001a048550140c2ca01452216030201500031030b03004a82c0400007040e9503074035000040c401d0340f2030360216000088020400600e0b845503201410341121039142002030760300190035030341d0704c00e203410400000c07501c10041611185404c080c00c0701200c1c4001c00d100d80310040c03142112131044e410141c441d011501c0e4001c1c030100c901000c00420f0b0080017074503d181042c852a000608040000401800100380041d40840003c2c401514403500680801101d03d5035a5a2030050141035040ba1071003044031010001c10309134080851030842070308212010751169 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 952108417 1250 952107167 952107173
    0x50613050d0c0c05060d05012d050103150e010b030601182102041d030307030e01151208310504051b030c041a0c06070c1a06130203100303180b07 64
    0x140900982c1074070800100d00700040c5aa4982000301024504220042010751404000e0303c108954540081d1080c0d00030004809140300310345c040021602c0920b80440e140c0c042039048642e1007203079001300020f500c0310400031482186820041d40600303000c0c1d03500e400945405048000140d00c1e401070001b04040141403205440f68148032065846c0002c0001601040b5405002e9208045800c2145550404001c1002c5160144148203031400400002d1040381e1000c500c0c0520140d9034050064881c490b40356820074010301c541521700c4124984110b003c2d90000102030b01768103d80703020410b020090200301266904003070180070f002c4c1602c41010985c010042c00085026000208101d04282007400b000039542e21300740c80c4910740230070400b00540d208942c0e0001400c0c00c80c010228424010400c80400c005000005504460030341403444a4807134480c00002212103095201410a030f0340048144040f04200c1110b4030700b140d200c0c2e20b80030113145100c600d0200c4003800344105000c25200b8060304002c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 952109667 1250 952108417 952108427
    0x40c0809120306190e3304020a2001090c060f090b071a0903040e0a02040303050a030b03160e060907020105010e1803090409061a10020c061e0301060f11010b130c02100e0a050613050d 80
    0x41241402c1c0e03070407900001c9032900c0d40c6840781c01040c01e0791181c040ccc405210b8801401e1000c0c0005241440020980610142c181c10403403040300107242d80003510b0310606c00141c4902031200018940601582022091190742e600b00307000d03000d401d02041c03010880522280c800c07541203035850b44a03d400e00100d104294020109032601c613415001c0c203410103d030a110174a141c0045d00c803038180f401140c01c1c5203041c4a03038414020b000034290fa1602e0f00600c01c14103281000f960202c01103010b200c198042d003c58600710b01071042c103035402ca03003440007031010440c2c5030300280c0c114041c0d940a07001c08140e00b82003040c4584400c8001000d07801c48181d070002401c1000003400101102000b0a450300700d030700300e01010ba9200740d004900183e8030b0b900d42d4080d168048000c3c60400300d010020b00140401c88000f030b80701c3c8100c0d00380548040d510300c0403a00140c000d1011403d44910014204440324542c2d81440c0c0b10b150f600022203450140000003080791201d498040078607500300008003800710724500c0c180c0f8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 952110917 1250 952109667 952109677
    0x40201120b06161103030408190609050303010b0705010b031f0e0c1002030310060201230702101514091905130b090a02040c0809120306190e330402 65
    0x42155120785000085884540092054182c50442601080d6507401c20980c03606641c190329109030000c02003040036182c00104001c00d08030312500c0c480e001da11490403000a00e00f20000a051380030200000070703003d0300b080141000500900090003800e00d03880426440307040c0c00d0580701103001c41980505021000b40d0044140d030500e030040b00e4480d5000000100c000011940640060b07000108102c101042001150300030070f0907000910210000140984050903150003160700030701890000784c1140e100700803040c55008046d601b04254904104851528080d40c058100001c130302d0444e460703040c00c002641741e11039000d0102c1c0d1102d14003030281544c003801c809010310618400006820b008146c0c0040d01c54080c0148030010065043d161040c003003034030364001c500b400340924241003004449000c00d4400783c8924140600c1c1d40d030340da14000030f07443c00c3c60180801e03100800120042500d842f4060a1405220740042c96544000841016a66070105511884040c2821000d9145900b0186c0143c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 952112167 1250 952110917 952110947
    0x37080a17030c1b010207021c0308040821090f16050108130302030c1014070302040e060f0a12140f011806050a0902041a1e0f0108090a0c0806150a030b040201 69
    0x40c0c50315091040b083c803806000c10b4043c078242d50028607642140f8140200007001d2a0246078907030301010702d0300c001c3e000e9100284090110100000d2441007100900c400c1c04c080f448030700100840d0700b171007001140e8480c2248401c14840c483c40240c0d104440300002480116101650740107550360720340656218007260386d6402c4003948410f00c00d41040b48020b001d4502441c640f00302c006804408114000d68140c0064650350906104100a01124410400c1c840d80b0040969000d1106001f04000c0b6900000c60b5201c0a034400d040d018080c02c00024003662090403035043d084481c0e400480050500300c1d4803030782120020120a030f0307003030700041c4458011036440004290b000075040d0554000c6070544143e90307000c882d0f07445d8241140003a03103802c030b40780440b440c401622090b480b8a40340111b2040da40505903281880801c0000900d1480c0400001c00155488000c00800c02d55031801e5554500c400d580a5035442c41d1500e4107501810002451011240c02044058003601c498006540d44101d40541c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 952113417 1250 952112167 952112191
    0x301090c02120c0d12061d15010504050a090203060a09021803061602072607151d0918030c030d0501240903060c0c2f040e031837080a1703 61
    0x1f487c0070b42080e40010f22450202e0040191406094903000c564070740c2c95060511000740710612198542ca002c11003601c50f240c0700181d490b25040001650500c0700d600482c02c142c00015482c040c448040301c0d511011100750103c4056407504a1003484040602c142d41c00180c0c0032000c100015000100c442c915411200c0000415030f201a1409080c42c0302600315200c00034407070340383c2e07002c040d8840e035480e070880c010003901c62000f40044001842c0410160490703e249414140c540f5140f1414030854090020720b004480d0390300d82414550300070300401d10070f8034400e0b4074458107060341c0110401c0302803a035465a900d100707541341941d032181c004245101e1404104461102110000760041d034402661681512074400d81c0b900d00c1c13040c03251180410718440d010314205050100419000801d070703900307107111106c5c01e6414030310390f0f004c030318503404000d43c04540080d02006c0c0c102602403240b490080b880e101c110740d81019211840d1903551846904002c03c05483d5120b49245402e245002e1600940013a0742 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 952114667 1250 952113417 952113419
    0x20a0909051e0f07020c040e0304120c0f0501021b011227050c0a08030711060f030f010510030207020303070f0503040503010606091509060801030605040c0b0301090c02120c0d1206 79
    0x3001203810482e10100e241c0010b031065281040d0440c00507600071860500c00071030b440c2440c802900c1d082d0040c100b0b4001d0f503c80c4100c0d00825400e0044d60064240914020000c407000d003044a12403843d03104890992040140100d6103502c003107207500142001c3c0c1c04089a28096400440b90403000300d8204107000da0301d00d0800284606c0140d0316503020f0390120401d036029500e00300300d81484d4540140e40e02c41c8109078810002c40901100303681c00543c10079990400100000702040141c416084441700e8880700104100080c401c501215042e11005d80758040c111110f20003c3d401c0384a900c4020350301da0300500000c00001c2c0c4050182980d68810400e0720f003082d641720b000c2820b58041d41c22810104070450001d2000c0c1c04200340000d01040305290003030485150260280003400c041c00040c0c111911800081e05000c2c4004130b00c001030800a5045a0b25a942e803d010020700580c8040170050158041c5820f2041c140d0007514030900c01d180c050a045001e00f641aa101520305580b05803064903404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 952115917 1250 952114667 952114679
    0x90203010e060f01021b01440604050f040f1a0703061d040f0b090109020a1d18031b0c040c0f120e0c0d030e130c0e0f0310020a09 57
    0x166008200030309410410b81400360030082e42442c1c00541c039046511600d5003003500b00d40e030626100314000a080c1950452074510725202c002c860f58034901d4070081002403403441d07041d170400702002c07490380c4c591440070382d4480d81d0800099440650301c400d00950150041004510210803610006104404220315455031080c03c02c1020012140d40020a582c0c000802000da074102c01c520801c00103800070b100d00c5c0341aa0758880780200c8200301070300030b12005000a00d215402d5101844042e0001c01c08100c26a555100c503901034464110850a2440800404ea124290810916034140c2641c061800c00600307148203c522004001c1002192049034008041030301c6a110340356400c0301b03c0e507440c0c134038420041009d44070010513500030703102c2898040b20352440385000c80c0351800514212420800ca20450408585040b0007440840e4414180015070b450048a58024119008240c03100e80300c081080b01080140f40000d03450070b030503401054018200f094a94001c0c48a840300c1e0800d186015200c43c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 952117167 1250 952115917 952115921
    0x62f130317130e01090e060405100c0908120a0306050603040c050108190207080c0d020313060804080d14060f0f0a05060702010513060e030c06071a04030917100e0d05030c030c0409 79
    0x261140780b0f0301e440320005002d001c1581c06022074400110004140b03d00b443c0e5500c1ea0f6448090044041e8030f6030783c81c902c0f4101c030310625102c0d00600c42c400c2250744400c50401083d01d20340c084d140d2000800d1501d0741c001450f08290302924842c5400c012001c0d03001e480d18005503024600241261683e2921443d03d070300702c21551010b00440c9000d114280d45400400411a00e400e00c464103400c159401800805c4102844102c8101134400750303c2c1598036501c0382c0c5003021642c0110303542e0b55032880c1000402480c41c480b48170360074810a42100e041d01d480d00c5c2e400034081607624103180c0710382001c0c0c98142482942420300c01008010b00c10714201d4681000044080c3c28030343e840d0040c40014249d85604942e43c601000341c00600d140840e0242d14089940d551043c810440c90528038030101c072140000e06040c0511a80002451101c54409050126200d90342e03c44103c80d030300102c0a46007036100288204001040d410080003510f840e860341e112580c5880240c1c200500c0d500c8003140030000814149c2d024 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 952118417 1250 952117167 952117169
    0x40504061503050a020406060c0b13060617101a012309061201090b060319090302010b03030310170d02070501121b0305061201050f01050607030c062f13031713 70
    0x185004d820390fa1110320401003031f1141940076008103c0d807410380801090316000c400b6042002c00c1070404c146031043ca0054050321040c0d02401c804051a030060001c58404a8008184103201000304006e001d0b2140c03620031220302198045c00a42d8001e54601c0e80c40214072440f03401180c142c0224102400000000d060341e020b1105d00300c40860301d200410404001e4003541e42008400c0b034601d421480c00b8010703400c620a451012071105a00c400e205001e042c001e5008030b00c107240160582c0d0b56858801d4004c0744448851040000c0e060011000c0000041d0204191410241690182080c1c40c980b10044840c143c0700520b480240741c0e5210180c0e401e400903000c11070011a1610042050314041040103120a810042202280d0401c02000521080c00c1c0c90107055460403251a40c50704c036141000c0b10001c40c48040100020301c0d080701303041c8920501850310440600d11070340b607101d01341c01400703100f150003038160318105880d44003000d000117a40780d2005007000c8100c1c4c0150b07041c4018070090360100d0b082 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 952119667 1250 952118417 952118423
    0xd0207330c17090a120302040303140f09090103050303090d0c0b011a040f080c12010b030d030c031103090105060f0a03030905060307111e010c090308121807081b0a0302010e040504061503 82
    0x2c00c4a55900708040c517500403540030034034181182003038035546004c1e08601707840403203001c3c20300009074011001c582401070b40c5411a02601d58007441d0786901d011076076940269464074403445540070001c0070b1441801e40303611890307019420b1001ca902e41100162190710a548413142440240804518004446080d50041c040c504c0200440c400c0304052008031500850303108501e03410108c450a80380c5000901c180650b0551400050103041400111300070580d01c5500080d40c0c0c40081840a400c81c1504a0740c06546c04403441c0810b00d400e8400c0010010107440020045180355504100600d030040c0507580c82521810008010003920400034201083c0c1405642c0010300084103005000b42481a401030080ca820006d01c01825521800110700850303440821002225000403c5817641e5040500b100c0c2080040390300540d00c403209640c80314690101031103031810704212109140b03072015110044079010707150504211820400d00c40a03000050056030800d4440300d10140c1554862000402140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 952120917 1250 952119667 952119673
    0x6070512071115040510180f0f030b0a02120103081c02071a0105060c032718340e010e19030b1e01061b080d0207330c1709 54
    0x4034020400003100340c114451412a6000c1c442800300e40c0f101b131054414494681007000320000caa064116900030142c05c8041c8220520300300151107164071070500d00b030780c0c8962034010381c40c1e0740c81908404a0040b104202a005080c600410104800000030300e8006141030745009102600c1540f1010b80e4040b6604498840108400c1e0f0440320a01e10000c0c007410085820300c3c6480348094a00356030340a6108a0066801a90203114001c100c0b1044140000300190220200c010b194204c04480d090455010103040703008441940920035084921001000101e4803c1c0241e1070301108840100b2400c3e901814080c1104200071a961030f0b0003007500b03010862541d0b01282d030441c0307413007200107002901c1c9040c41496501c0149a5080e0300c0c2c2c295054614030300d0500100a0000c541143d070a903040d8028202a0000600f00c0001d180d0780c0007042028082c0c190881a880c0d2000349200810364407a45408003520452505039040e120b820224210003e171610600b10341c800071410401910075503a6814940c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 952122167 1250 952120917 952120943
    0x907091a0306091501021c0e030a031e0507151107020a0b030108010c170414030708030a0603020a1401080105010e041d0d170709060807120515090108011104050607051207 75
    0x80b03800250140c3c004c450301c445144512071800080e542c0c8010003600411710a140800d68441c42c820705900741114030041c02c840130131240d030030f02a18640e1038481e40c0d0442040c8080f1311076018000c030221a06150b0000300702048001309070585009054190400800b40c100b0400d4101581d10003035400050881551a5a039952410421508440c000c207006000e100c01c0c1180800e451880c001403030f61181c0c1046140d4090825030130541d0651207080c40040071841c01106101d031611746a884142600d00c00d84000001d144c4510700b6800802c001514140000e0316000103210f1544102c14600132110040c0001c902d01090031075074141e4100c010340d11412a8000382401101541c030640c650a07107041c41e180c00045082c003982c01000c86206009410a0140380800b04144d00e2046075204400008004100503600300924031080c2030040140c46841442c1c0000007007441c02041c800e600710141d0540400c1e14003454602803085540140c1401d444501074011214079004030321700280000382c17094030321071030503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 952123417 1250 952122167 952122169
    0x20706090906030b060d02220603110603160c0503130e06041a0a060302030c1306020313060201060f2603040e090d0c0f06150f0605040801061a090907091a0306 70
    0xa005500500c100c1c1e0405004201050546026039001201510f00b0703410180540040391800401703071800321151444002d80c5a02d608103600c100103032803180420b500b0f4140704000300916408182c60494a84045403007243c0034500410340344520a00c5071041e0303800d041000300f004000006e135522103400109202d00700101c9107018405c1d40d44c0c90510301442000084100042840d03038009020f101d00f4543c0c00000300e000061080300342d070380380e020351200201156119a0001d4503500034401112401c0d001a00114116006015004c19125840413480070703d0f24181c00050604e40d040c41000c41c0c04803a07164044841c0041c0300400240c509002044594184020010700d025401c5894108001d00c9600960008649468082d4450f401040110742400c0d0840d80c4d42c10820760f50302c400501d422191740041e00c240c000c0c2c0584129096a0b0003081110354030502000d180010800342851600f04012042251510100950300104c45d440c01010460b1200d00c2c0d4a00400ca451691800300b101104010351 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 952124667 1250 952123417 952123427
    0xc050d0b0301021315050f04030303230610050f3702030306060a0c022d0a0807030515040302030d020706020d0e0c1f170a0b03010b0904080f1602040c020706 69
    0x69a00c103030000c5180c00e0200140401101a0f809045101d4005180700071410f846541a291060704c0c0c00c4925075625034a10b4082e004003011444168600c03c10000384142d014868101e900c12040a489074100700707801203044405038440c0800c5c40c4031000074007a1040da5074540c00c035104c200040f10640041000c02a001b5410b8145990011003103520420070060070b6201c4005135040803804e4100040c500540f44000344c8102c60600034502440b103446600a0a494001005450480b0540d00500c0c402d845001c1140c98035007501014210b80c2c4443d0142401081460072282e1281c042d20640381406000c520303007002d07039014210030f1b00e5403600410812a015041c0c0b04610703483c40001c0003440c9540d411030100f403050f2030021542801c01a0000005911030240c0c0e2580c140c2110102000803034902210304500820001107005e002307602e0503044141c81e08080c000c0e54000c0b40c1000115080c04100000c4d18080d501164000307551181c102440780050b1600e0140318040d08807a000340c0341d4a4104180102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 952125917 1250 952124667 952124681
    0x2040f05090f07050a0e1239030a0b0a0e12030601030f0506030606041e1409070b0a08040b0702011413060b0901060c14030f0c150901050f010918060c050d 68
    0x2c1c001100418400030541040c1140d002428605140c5030450344040095110300c44c00a030f0705100e0242c1301001e03180840c0990a403040041c02c02c082d1002c44c80c105c1502400c0682e01010907090344c0410034440c08904810111503008182440204213000100031850509240c140c440610840100a21001d90381600402d040140300550400991400400190b070b58007024202d940903c1d65240068514040d901c0e9406c3c070302d01d8180d02400820542d800032500c8130302c21101062a802000808200445460212800321302c2a5035031140c02e44551310707151080701003e1f200710155036031401098000709051039058402d00c02810b86242e100002e0402c2c800703840c0b14801140c4561149070040c4003c0b500411540031980d042000c030800035140202d10f80ca90320640c4003070061141e01082d60140d4850006050381808680d4188448903110045000e0a03210191100182e00828800502145403240c2c82180e0055004810b1f000071003403521001c0031181130100d0301001038400031b1110095500b90140d25 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 952127167 1250 952125917 952125931
    0x50a0210020a09211e03120501030308060603090a020901230f0a0b210907060f0c081801050d0f02030106020706090b0f030c0403060c030204211a06011202040f0509 72
    0xd464000c61000c001c3c50031981d80503a00c90400c540410325207a0080100e03402005900001c468058582c001d001c005128280200f140040c0d04131407407010240c800c1c0a00c5040b641e158640c0b10a94030f4940802c001504002c0900c90b13684608821032025a8540d00c4080c02001e103540800c800310004908002c122403003990351400707150070a03040c0899482e4040c10004840622814503118554400040040d00320195484e10214549081c007031031800100c0c484046030025102d891503080400011395100c803c11001a20201e410710241c6040482e01040100248051402c54900700e8200000011602c190362440c01c940d41c0130006100341501004510003030a000e08090442500c0e01011102d00c0c4100095410320000110100c2d0749424070074155030203140c3c0120288000101c48500400035086842140e821407040000e19040489400380f03c1001900600040400110040c02061048000d0849030400c250b603107104010007598030280c000342c11000c40510401d890b040c2002181c0f00b0191400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 952128417 1250 952127167 952127171
    0x50a020f120307090e06240d090503090a0e0903030c0702010c0501020706140901021c0b1c05060411010c02060d090c1d180d051b07170303071e12050a0f0c050a0210 72
    0x8031042d940c03078425000d420b0704111810746003800c0002d101d012a000f14008008c0c1a03051184000401030003001a181150f0b054a00c00d001c41e0741c0e000c0070440548240c40c60b01e803642003000405c5841610100034101203006040200070742060356501c50072a4004081a03403016560550087c04240c080b4040d50405c00310402903050000301a40481c3c1d00c20410246260381c2d681d0b6070f0034078094442185800c00c03202403003250125440c0324100180c48030011203003190544000c540c145015130290041c8004507070040d15407410080d02d40c02d10b02c010080c0c0807054445100426000036200c100a681804001711300c0f9001c0d03114200101400b2403070841c032007074484c650802240303ca88164020213450603e200d440720f01492001c1c0c07891190400403960841d4102e0f00c1c0720300342043c64200020045000b011140d450010a020700301d56072a0000302004443c0010700d6400303920380a0043d0b50050b03a004901400002160140c0741c05030000c4034603000003180031034030116880c1940e40d0184003020880f0076034001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 952129667 1250 952128417 952128421
    0xa23120f040b07060b0d050d0f0f140c01060504050a0b0414040f0f2603073e030405030f06060901091a01030203070e04060f1401030615050a020f120307090e 69
    0x140c034001d004901400c0300300840480c0c030505000c10342d0044202c8031400b81004140e107029081454031410320260010102d024107604c40781c8035210345d010111310403c0360b5030309803009141001c02e0959446002c0d0710600f50748848010902d079941c0e104a9009040010300001c01c0b01e03c1c030040c401610360403500c154512015904001c04510a10304030941c1e15030084680c0d40c005011300c0c00c0000c0d1000d0001f415150002c1940305642c1011290095019140a2700d440347c00001c1c00409460785e070007082c0004000750380001c52440b61180d050505c4400848841a00d08254603907011928061030140c00000552200303090125504200301c0207405402c01c00b03c242b02e1b020440020ba1140401c000b4080d041542c0040000ea0862095001d440404401031044c0b2029540d0080d010862445004091541c1074505c40381d036096002e03200d12800c84030110000405955064030560741508600e0302c42c015809084801081c1201c240600300005188a02e20354aa0602c5403000700f50640c0358001c1841c000c00081 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 952130917 1250 952129667 952129687
    0x302091018170601050409170f072d0602031503160f050904030c120e0409050c1003020a08010e0c040b040801060807051002030d150b0c010614030c210a2312 69
    0x2c1d11a06503070702914082418032031f030700c3c20a141d17842c841d9002802040100fa800b801c4100200105001402411490f40c8503480f5400c4003200000c080a0569480c41c040700c410000d4000c2c0c0207075a0080a2644240304400054041380c2417149287c2c1c140105803445005005074a4140030f120003030001900c0618080c6003560f0060444c0c00c1520000d0031070b803c601103140c605403042c0c180c0b0a540b4001351050062207524030f41281d8070101d86c0d41003441854004e80c07100e900740c4284256407000d60325558054803a40703002d0100600c404d01800841001c0c20800000ca1000d00281c01440144104400041c0103442c0c44c501c5402d09480d500003a00c20311240603070314200d030750000960b944002c40b004006400c001c0242c80e0680c0800c264001e003164100865207020244040d4080d02c100c40100d02c2e0f10751400340100816032520294424981d0100c14070810120346002042c0604003105000100d6403a03139010340320300c0b251070085000f81c200b802c112516401c04541c10b11039144441c2d1700744a0700741004c4c0307070407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 952132167 1250 952130917 952130923
    0xa0911090a212004020412030207080303130618050102070503040905150a260709020a08060402040e0708070e06070606050117041211121305010809030a0905090601030209101817 78
    0x20364060315210f4622403240c9140100080e0040c03000005104656031507071845506c07000061494180c01601403180002000d920210880340700320520b05201e40009006c0c1d49a500401c0c800e01c1c80c40d05c80700700c07441030000141c09200030500c00d800340005517251450075600c841a00d10007091400c03104c0d07296540d00c1c21516469402020348034450b00c42a0064503034003000d12160f07a08540302c443d1744a1004009a8400030341d0050100018130b648201c4643c0c0c900050100703a100d140304000e0800381007030024040701c0c407420f48260082400c0c506500803d003250001400c680102800f80c0c1d195940d40c508000542c0c011686c001400640000003000d07140949400d86e03c10000f03060340d0700740038080140d900104010f11030403002c214014229a100d008052507180804014000c80e804248000d001c80ca8010000040d80c1e000720320780d40c403145224241810301c0804240078006a050540034404011990340d001c3c80d180e6002d10583e1648074603c1132004024000700380764071002825403103040e20b0500400c08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 952133417 1250 952132167 952132229
    0x3060f1d1603140c03160309022b080304080d051303020616090515090405010519090f140a0911012d0c050d080a0f0b01020a030e0a0911090a 62
    0x120701d210802000141d003a0064420300d80c1090103001108200080509500d010714001c102c1c2c26900c080c00c0c6070030a42a01214020314002c1d500c800c0f2000c4120079824441007401e4204c0594004d203c8140e0281e4801a403070300241c400f10b81c91100800e00101a51181c03050503888007514000005032003550300d019455038000b41401d05050114000282c00c14040c6000b030b401440007400c00441c00803e0050f0f09143d81240600b60310440c1410b00000d424901740300440200c51110307851b40c031281e180c0a18a0010018110380302c5041e03032118074030600300c10201c0740c0c01e02c5914410404074107840e4a01c0c01c00001d803281402d180c140030021841c0b180b009107918001c00002c104818194080b6183c000c150341c144442c1d0002001885214001c152050744a94034501070a400402405140500700c441d600751010314808500503440240c1c90404688100c0d444a1500c0000e84512201030300d6010580c1614050b0a40c0310007070f000041e00701040d003000003c81006003091139610350b0501d40d80618000c50508 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 952134667 1250 952133417 952133431
    0x405011410090b0d0614030a170a02242a0403141006030f05060708010308091011010e0c09090606030a140309090f0f09070e07030f06030b0703060f1d 66
    0x1c1e007168001c40c2c1c0103a208601610740c003075446860b084100d0040e800b4003000d015402e45940c1c080c0c5100880d050000d0540074603a03101c41c14059800c0e0f9070b04c41d80940c0c1c014004d200308501c21202a03241c03164252042c002c2040103560f9400d010b150490002d00700814002c1940c0080c1c40b0b00205800b511200300566055030350099041a0050f03004c01864986446200d8991400d1700d8084000100400d954141001030310401c01d0321100d0341c45040c107a070b5081c800d1102030724524040000c940d9914000c1050a00750030340f803d110a0b208006006c981c00c4950342c903070845480d07001956000240c42d281400d664456800c1780100660f2a002020a0710340440440042c04a401c0040300c4400640038810f643c0002c1c0045c10400d258079003507126022120741981c52804078414000850400140442c00c64142c031490a0040a2500e450348210010704944400075035140ea501e10210024442d0040c40c0d0207504d032540d0121b8198207001046180700555405000352040d02d41803c091b00c2521180c0350b603c520 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 952135917 1250 952134667 952134679
    0x110f120d0902121f0b0105041401020a05250f0b04030b041a0705030414060609040206030c0d060801020a020c1c060b0f0907030f06090b060304020915100c0204050604050114 76
    0x19001040d080a0320600000940c41800d08420303600462001510b0781d0706003030070070901c00c0343d04440800d401181c05890300180010300c100402d02122417844502c9108140c10710440700070200d0303030b01c4150800f41e007140b50316062400761900d014151b50b1101500b015103c03034400300352030500e803001200e041e02c00d42c40300400c9c21100c03000080901c840341c4031580b071403085980c001d507151800b95002000b5910841c2c0494415018181e039070121280060302d40d01c20140a0316a8000b41c5664003001001e4100425001c400b1404110b01803680a03a405030100801d850800540c40310b504030000380c2046620355030140100880303030701a08408000260020070f9034100000048044054003c01c2181c0100310000b85c00105503014000c80680c1039006100a001c444c80411815803a074101c1001d44504005041d8440000e0020070023500d17010300b21070b422105a0002205034403050021501c0c034034151950f40045211009400154107140c02060b9100c60211400c20a0f0340c144880c2c080c10581100c8000d000341 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 952137167 1250 952135917 952135927
    0xc0f0b0903060f0c0c071d28050411040c08060a0501050a08131e03171501020706050306180106080a2403060f15170c06090102030f030403180b0406110f12 68
    0x2168450031555034200300815100802d440b11004200804003807040c080d20350147d000070304003828281c3c4006103004085007c50384114a40045001380c1030207441610b00d00e6480c4003152541d92117120310115900d10b0740b123200d034501d03109081010740e2301c580d80013605121040010518103580b05200c20303441315183c0d0a03c8a003248506103201228000060188d4604400c50100241a004401750148140b14030a400007592074034131101d1440d0750f10b1066405640140f50611036103000e40007943d4880f2000c1c1007600074011001450fc004042030b07100c0804202840207001506c0d0440c000c08100001c0c1741c041c802524000c440e12090342c1401e10020f802d042d6501d007003040404041c0c0008810760040006600348588803079048200300c55581412145201d1000c0041c89401c00100703440341003d058000d541007404c5034819861551009004900700a148440880e000740704001100207000b80e0000907889030b0409a020740000c82c0c01d20504420b030301413400d52083c80300c0000e14012030f00d21422899182c0e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 952138417 1250 952137167 952137181
    0x1c0c0801092a0b1201080105070216050d1104050c1902160303110f1b190e04080f0f0403080a0e030f10020a020705122401060c1b120c0f0b0903060f 65
    0x200b40c280c0040e2518100042d0740c082e810180d081c214140c0340140d008101075104c644050303a4402501d1706448180c1440d503020841c5180580e0204080b90051301c480c00045000c400007401c64900b03c2c1d20010000011441e40b40c9018049404042c00c0500e0008002c6240a090861500e00103440010100540304070071400340c0c50144440c03108002044105e41d0854134112104c0800f0117a0740806008802a28108c294029408000360894414000b440c0c4940c40d0303600c0e040e50329031002c0c0400310540c02c03c0050211884c90fa000900040d409a65256206e07090f01070020200800c2d1504188203910012114a808002290b00d410306064240010303601d09880c50203904110700e507030101c8d922445240404580001c0420300718550b40350320b0100c40480b652400081c0c8542c10a028000c00182d503204841d00058540071128035a109103400c0d521035641d80c849060a5000161085601d107422603400c000c3c0e141c0a00407007000d45a07a030191030500d4040740100750b40d503000600881d0342691180104042d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 952139667 1250 952138417 952138493
    0x3110114030c1b0d0c022d04050a090203030c060714030712090c0812040806070203040e1306181505010603051302090a2c16050604090203060f1c0c080109 68
    0x8020810040d541010000e10001d040c4030100a001d034060f03180741e08103518004085680c02e2447c0580540c034001c000b0b501c41408014140140300107840350340c540f12000941e0b1b00304054840d80325200010324003880c0c11100103002d03900c0c1c150003004441d000d10500100e95000000e910f05001d0310b000c005814029410b00e0080c3c01d060703078010580c50181c0f49843c0c40c0101050003e0080c1c511010444181781c9861001b207a40c0c0c0714038030940880c000303203a001c25288900320303e4001002d800390001140c020f8103070380c60341700d0072200c8001150082820444840c4281c0a4001d65006220f6420200078516000013400c1c06040410300081c820740d12500001d008801a41c020400c030a0030341d15103190f00c210200002803c00480020303c0f8903100d4450703104090782e150400e66050f41e10241c1100d041c1842c0c0701d00b03400a0340010302401c0e4082c004000c0182291544e204074070b0071484d2508042c020740342600301401910f01c3d42d08528042d034100030041c8041140c04280381c0c00c100304101026440f100d048190b9a03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 952140917 1250 952139667 952139707
    0x6210603061a0108060d03080f09070f090203010302120a0b01210602030708060a0905060f01030908190306090f0203040f0f021f0201020703030c0c03080423031303110114030c 77
    0x4a403502d003002c031000904210350601d040d00300a8840042c0340e10b400d420000c0342544d607800103000a501e50001109041d403403c3c81c3d03401c0280b0000729450291902401290048290425202181d01000420640ca880750441594503101e0024180d518507548602d80802d10500413220220ba490344600310048490000d00300d2181c000d4021512400c101c1d20080c0440070959005204680907603011841c1c24040c03040a01030000101404003414001e030055010340343c92201662850340500c0a061040940380030541c80303401c1c0d0341d40000c03030302e04040c90704044501c2142410611481402080f00243d40010840801c075000f209001e0440210310028500402ca040340082003002604902a507940540261104074403a44050140100c072080c22510f01066520107070010300700c0804940070451503411032500b80700300d0340746150656100740c20034603590200e00303080503407410303180108140071400340d5a05642000346041c1d540f0040c500074058a074000030f07001c05289040041c111100943e8800880 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 952142167 1250 952140917 952140923
    0x10e040e12210906060f15190c0506040b0106030c030b06041703040815090601141f140c0a060b091303030f06051305060f01140403031103040e01031202100606210603 73
    0x140c80d890042d083c07135110340042d0f03400c034010385c00394600740254030b03214040c460040c036021036850400e0500010384403030114111003901444074000d55240464020b01c01300b886140580c0c0142c183d075140c944028103c139044210a0101450b14400b004260b4640c011942201c0c0da40c0d41c09449154014076807402e40c456980041031602c50039400040101d01482100e204420384425140d2980c0d8800560f8030011810086a078010040d1388501c211454000a44c0c241c50304d40d103040525215401160401075000b05850061644030828840170404c007030084c6030b10410300b51154181703420002090a01241c80f580000d0526071a00112107035030380664410350086c0001450b003c018040394008200522069034200e005290810280030954040c0e0000c003411085a401c0346d00d02491070324111a12070b640000c4102074001080005400c0015098144c0a076016001c00030100d000901d02920340919020003005050808008020f2a508029002c0520307141092040300d00070384142c5031300108180c0d0001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 952143417 1250 952142167 952142227
    0xa0b030a110309070303020705010f08060607170c15090109050607210204090606030c02010b060d090f02060307180f050d030e01020c120d090905011a36010e040e12 72
    0x48111100000c4c0361048074069005d0322180c50310368004450f41b4040035002008200030001107052400c0480051800074058803240030158140d02d540c1e11590700010546000ba4042d47c010703807582d1203161030395401155801c000c00000030b01c0c4d80d450f5240d11000b00000107004407000c00480281e400d40785c0f4200b11018000440da100e444401034001010103018a4001a250520b480110750052203903004007403004100c01d040c107400460240144c000050101e03180d50051a04000507151034000c1c6015001d44d855404580c03c81c00005201e605d95513016a000c0384800004101686481c02c078520702e59010300d8104401c00e00b110050707140112481c034580c0c001c0b200c0e2103040c908000105407034858540999854a07841d6880b00030304280d4000b030054000e050b80240c605036501015900800e200c480c45885000212400e80c1e840000d100f8230b4800c0401480d100c0809442d5680c007806105404004880070025481c10070102ea942c2d6040c05010003109000280d2617000700040080160260b40c04148 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 952144667 1250 952143417 952143421
    0xe0310200331210f08091e03040506040f1a0403031e090b0a080f070c0201050f0a03090c030b2d0402010c08040801020409021c090209070e0f1008070f020c0a0b030a1103 74
    0x150703d10000002e0b4200000588a0089180c0c491080450074007845042000b02000c0841c41c2d00d50a080c54200f0300c2003200e00c01001b0008044e198180944020310112804050440c034280c02da01d0409078000440d505044101b0040c0000781e0480e801500300e03e45506100d00044200c2030a984060352070708610301101000c20036003000c607480142d50741300d20301070301c0100440d40312a04207072a8200c2c03403440280428020320920010341c042d18042e141e00c054915010407500c1c01ca071541e9100c40010741040e6001c1c80c00c9403c01c401c40c40701070104005c1c01d9160b04d40010150780301c42c0401039a14017600c0241040080c111000038012180c00350781c0039100d084021541c071507491404200030740c411241030070040030605801260802034400c4404c6c05401403c50141907607070010854505e20395540403540560703500003600740ca0b21204100c202500c40380d00d4003059800c141d000501021464841441154000d4840001a444004c014412219a54003d58503070706e9603880f40e800762011444401d060000402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 952145917 1250 952144667 952144703
    0xe040914010b010e01090602151e1905090a081207030e06101a0a0f110712030c060b2d031e0a0c090212010e070e0310200331 55
    0x71260004007401d03204c0c1d1550240703c07001502d903c007280c81403401507082402c0c0d6010045100c1a01507101c11202070051301d86550740364500603a4019100203090560314540504054440d2040039003000d079490060018900340c1e60740c0c507103620921001383c0c8007000c1e00c0040f440303d50003a04010030412124003a070b0103914000403240c1083c141449080c00d04145503082d140108034078070403509230070b990360f0702d40100f000c40c61340642c2c00e46100e00141c0002e00c24031400050340d42d2200300d1402c410b40320b0340d200080c607031542c141002074454250207a445120180711407a4024018031821030b0b000340d124001010701c02203030700207810541e20030b043c02c03602207024040c43c9040f072000c11a1811039101d0425500007a40381e419820881c061961450341c00701400740148003541c11407000b81e6000881c3d00d032100d955a008808a418210380c4060652441e45444044440c1e0082d20b200c200c0d1f8a0f0104002401c41c90198540e12000c1074001c160841198a0140e00744481c01d0001d0003160b040e0415074004070500ea0074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 952147167 1250 952145917 952145921
    0x10f050a021305120a0f0f1401090c090b13050705090d080912030322020a08031804061406030c0d02121003060b0d0f020f061c0b030c0108160e04091401 67
    0x1902250002c40c800c0e80414540703090320721403d542c8181e500410514082d541c1c0c01c814905210300503252416100400c0002a0f161030f800e02500381508000b00d102090b070701e044100500581c00502c92a810300c0200c04003a03e500c814290300704000000865140c0300d100c03064507039200e03144202d504a02620040410700c40c2e4980202401e50060b5130340100d5210145180e0b45900068440c0c4502182d0344074010040303c41510b0342c003102d5000800760040745644000452a50740072499804110020a45480280c80c2910640e0700030900c1405152580c040000080c440744401840115488000300b8807555450166041d2102c0b003070344280c0b00140c0d0410588611800e42c1314030085030102e0a0251140d25401d1074a1240c0c00c01c0c0d81701c2121840440e140d42003015480c03090f04c425801c400c090000c0382c004501c460700310348480030950000419112140a15003014410a03459050020b2401885900620402280b001206a151069004d000e280005014000ca084d0180c110711082c28081907403403040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 952148417 1250 952147167 952147177
    0xf030c050f160c080d0c17120414011a031002160f14010c0507170c0a080d090b01150504120f0c06030f18150207030c0f1407080f0a080c010f050a02 65
    0x24440e030f00500355940d4501a91280c040144e5000115003124580000300308411000f0515444604203003000d50700f80058502080454090b03034002035028118420860a1050311182232100040d000d0303c4c900503001c01da0300c001500d10b041da4142d00003200ca040c039100e019642044c82e840b6040424065460405900d128a0340d00c648116511300b071043ea55903030042d421525800e82c0804020781c0071406803c1034a054002800c85205d0b406102d46140000c0d030300100800f4044608000060108410300340114a188160822024501c5c1c40d60416021a00715040e40c00b140c28088990780c030f0070024685008070381ca0075030000303103581240d442c04a06a6010b80000c8890f255a440030020420002c140300304070341400c140a081024a0062149401090380003401224060b0819a115001c190f5078081c60441092050f0344602c05403a892030002002d000540c001c00100c2c0040c0a440d01d042c2c01c05869500102c001070139002c00250001e1036150a4001540030b00c40608100500e1501050b8a4069400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 952149667 1250 952148417 952148423
    0x60706050f07020303040210032d022106030303011509081506040507051c1805070b0703270b07021201020a1107060c030206010b030604021c0b03010b0a05010f030c050f16 75
    0x24107000a80418400400e882c8a5500100502d0702c880c02d035a0b0540041500070058009074503901c44000880074078404440d0700b504aa07000507502d43c1c6c840200c500820420072034480388080c0c003003440030f030360303000002d0b0f9040d83d020382c0b461110011560b2098543d0309840e480a10680513800300d505c017001d144032180380310702001e840500c090f90b074520f0304a81c3d034420072803000c401307043e862140e190f00460b03a806080460042181c003c14170016407174541c98030754150300c12010b8000001d481002c05901004c0c105880320000803040038040c0364a050700d5032520601455550070340c00b0035500155074602d0b001d0703070020807100000c640e61010b112009080b8045c11400c0406485048000030f40284203914041c09982c00d81e0182520381d003030148944569002402180e4041d4081c82a581c4003030301e0500c079550306100c2041c00150081010300741800c0d03503580390400b449010440c0e01041180d8010b003585406074502d103400101041a85015102401744030401c500c16100414802d8000080c0d0449520541c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 952150917 1250 952149667 952149691
    0x1032327162411010623040c030b090a050402060d020a08090708070602280602040b1201050901121434080106080d0513091e05090a1e03020a0206070605 67
    0x51108010400882000d0ba60010b04549a05500046205020120b88640c41c0b80020a00300d680d010b0955814609841c8071110b9820a080e11650346064800c41da131149060400340040d41b0813000041d10410000c000115040d1103400140840d5203403000c1341c0d4200045171003151a00800680100203480444403d003a40c850362201242c010400141d100c11540207078000c000000c02c060307000c1c1d400001e092118500204d1150071000040d81ca00180020f056141301c40c50f03c8036545444003490340d0060303000e0350050b1019801480000b44050f05482690342244a030707481405002c104500e000b021a03122001c11807003e031110b003900d40c2c0350800018580096500c180c1c164442104608996252042c0d410f1a8003522a20410a0165014040340300400701003410042d078410303003202074500500010705845040381368090328038018810f59410291502c020314640301075584981407032107000d071140c2882c6503001c505d01c1010301c200408940f007a806442d0a0b21140e051030000c01520003610140d480721 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 952152167 1250 952150917 952150919
    0x301091d060c03060132220303020601120807050a060605151809040203240415021206010e2e021e190602040503031c0b0103232716 58
    0x4000020400e0042c1200c820040c5151180c00041d164049120541c9600e0a10500244c65200084848005220b000c140861340c03005150000b00c10841c1120024001c0c10064100b880840e50004049054805006820040390400e00b00061135006060004119126408442003000031070380105c8101c40d8252640740484038100d1064100380160902d68038603056007800005589405c100e078540090000d0143e9050070310740842e41c0d201c4110060140400341121091104001c81c1d1a5140072090380000d0031814516801c490300d107403603006002541044442d454130340340b9940c0c03510411107484150983c25181c01c1c1203401a803138014050200e10160042000301e42c00c24520421200140d0b1166001c0c00503a59101d1040915000e840420340380c05078248400700725518100700800040002800780b006a0742e03009482e40c20744044a98407810076003403041c01410300403107408421460340036001900950b950081d050b01101d0b1500d0391100500381c2c1c0003440c0903c1034042030b20040500c10300b055103011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 952153417 1250 952152167 952152221
    0x80f190615020a061505030c100e060c010e0601050d05030a080901020c010e07030606090501050306041b03020d2f151e13080d08060616020f03030307050a1e0c030c06020f030109 78
    0x800544030741b42e095081410a40e0b03141c80d0140444148010504100060350b1007400814400d0304042d09580117a9917545030b0310003503401000b4880c0105011078084107802a207170344040d1a0301400c5a22018000031401140f584842901510540ca1700100204900c00c1004500d0b5a01c1100d440250740b03041c40c00750041603100c081c1c000c0f14103070307a4003a000300519200c55884100112420b003441213205043d500c04070040c0c0e10040c0c0780600d58060808201c8030f241c40004800380b2004800401c541120344419000142c6401d4041e440c448001038109817140c00b0306084102d0700381c0c80800a8117240380018a4150780004003022800d0300c90002c00c0b10b0207419051130540d01c0041c00d64040da84034034244104d5101a280c181924105440941481c543c00d01d02c802107031031500b01b5030300040400d0300440c102c11203e600c282e0344140324941e1304e09401e41e14071400300036044181012029040215900b00202400601c2c0c040750200d2145107002541c03980c4d90101000140300303c2e01c681c0402003807440b2101c41 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 952154667 1250 952153417 952153451
    0x100c020909012f0405010f09091b1b1e171b1023040809030109080919030c0504020c160f03031202030420040b18010e07080f190615020a06 61
    0x400601c1c0103031444e150810380103640b0880c07240316500030403c2c89500030a004103540a181006100d0040c040b040d10481240a890001403010700c403090510b84402c00d001c1100140211428420b11940740140021420410b4120071045008000340d80c001843d01c1d0065124240400344080c400107648c6d10030321100c030481c103450704141500c000043c41c02240360340d411200c00450304544285049032814000801080c00e60b80b040c80d09454248001c9000b480606149500c0544005440c0315036007400d0542d036422003150101d009a40c01190b003c00d185102000401144c00d13541061605942a1560740514141b0f0001900044002866400409070070306007a000b5203000d42d0341706001120154a25051505c000c542514041e481074440d4000120b50716041e40f925032081c4066403103d81903040014203a60400041d0024040005907020041403c1d007400701e05800035a0002c058618a0801c444200503050540041000c817030a946519941c1d50002800d50382c4c2c611031a020310440e41c042400ea84 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 952155917 1250 952154667 952154741
    0x16050618070e060112020903010f0b011107030305030f07030e0715090b19030e030d0606030207020f01080c070b0405340501050405030d03050a14040c0f05090402010c02100c02090901 80
    0x25460340b41801040d41c66000d08100031503400720000060401e42c8041c000303801d4400b80c5e20058040c6a40e13081c0c0d00303159644400e40102c02c100c07039801400154907641d401015440b00910302c80129a55901245050b880f039004088182c1c124001c4402481c5c598070442525403401140d200442d20745100042d040743c1e500103403a100a20015031000c541c985a50640142c41c80c04480c28081c0010040c06400041d24030460000d40f000380c2d00140c80355424814400755083c0111454144078007407040040039503001c1c00703d805040c0e100c03440b60001d0301d507031800516000d44810b00602103da10007081030032041d00446060540901582c0f4421141d0701c40054a03540709078000d040d0986c00c031411107184c00780240c0101b60041c50490000802ca503d2032565040240c0659003115134047e21001007110f54100c032101c00103800121155502d0741415400602130524044c00240030f0310108880d0720b00c441c0a510002101a00503044130301526202c450a0300805000c01035802419007180302500f01c000c0020030300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 952157167 1250 952155917 952155929
    0x1401080112030f03060305010203091006051206011e08030f0316080402091b0c0601030809090c030712110c0604050d0912082d0708130603020304150b061605061807 72
    0x90031041d510300f141d070b014103004928145510740c24000001740c024030065110b21003240c00303003035000982c2090505960090340840c0c4074481625844001140101d01d00341192816034101042c0c400c403450340b18002685034408141740c0400f00f0548150b42c403c500440c0329420b407805c050001000360405a440d40c81c10768000e90804200f40014007200d542c07411081d140e03c07a03458802d0409160001d203e2500000340c10456260b0000314840b103031410b181c404560800717410f000300390940c40c040d0030041469414038079404099894100800c4840c0d210301c110b0b01002c5800d0155000f40c078090600a5603928842420740c002031790107a002a0f02030a40b0b100ca0080c80d031000798246000803114101d1404c001d078030680200100100b0b0842c070404000701c02828103910521017940c0b5107219024080300545503501a200b0326004004100001e8030034081207002c0750b0315183c002503110102021840c2c43c01255810000401300e01220814404005441171203000302c00039400c2d04140065041d5203840452082c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 952158273 1106 952157167 952157189
    0x80a02031b4e0d0606140f09060909150910050d11030106050a030501051b0721180e100803091c111806010e0105090d0209060d050a0c14010801 63
    0x302c40104100d091051100501140c1c0054507c606040c0d0019024006611811607641409494440402802c00c1d8441c0c82c281318003c010700c40b100d040d58420982e1400007540c0c0c8041c201402d00b51940a80b40c0c10b4200b030656103003065004d46058641e4507548540c40495207071500c9540300004c5024000120f99800e005449031002036240c203c6860700e020405c040b40116100301030744299410200c1c000800070b007442c0411135031029815904440c520002a0006900700190001c50080311506000080183e581c102036540f0300c034007054145c000300d8102c030b04009501804403545440380141c1070322020141400000d002a40440e0a41c03a0b8440081c0a020744ea5900017000c030004078080c00e069250000b02c400080004112040003482070303c84000140b11741d15081c99002119610604a0701051040d140100f25a540750140c10320f00c1303521606140496105070300c7d4904941a01070302d = true := by decide +kernel

theorem cover : BRFrame.Cov 951978417 952158273 := by
  have h0 := BRFrame.cov_init 951978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 951978417 ≤ n) (h2 : n < 952158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
