-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5544
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:13:04.764494+00:00
-- url     : https://prove2.me/submissions/2e4e4466-7a35-4eb1-b320-d8f46b790060

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 996942446 ≤ n < 997122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 996943696 1250 996942446 996942497
    0x40b130b0411180d171b0f0109032a0209090309040f020a0806010f0e04110c06070e01020c060f0c070b04031406040b01050f0d12051b1c08040c0b0703 66
    0x62540529000400480290881031040e600e8080ca0500c4503c13401c03c00c450300510380f6154224036842c6c480d203d00c03c0c040b81c80c407400708062100c0d102da01c01c2000110018803505481c55419113882c0d4224051640c0007012a0400526000c03210f540c80140c00581c0300c0b049a079100f038240c04040c543d2b841500d010001200d444000070b00b8400d00c1480480400b68000010f140c00000900380704034008514081129001c540e81281d075001810000d5200c01006880080c280300c007400c40698030f2554410104035103401c00480c060340107900c040509003442c203000004200c0441c00c11042460440111ba040d4174141440e030042102c1600042c1c20014081d90a00301c070381550807034024046030704080d211400d007000103004892103940281c100405650781c2d5000c54201551105084400340a000000741c01500085c084218000000000340500100410103494000b00c925421350320b11003440c0c00701e454040050003101c820b4990100800c13600264005080c07502d1282c2c0e1400310144003146161601c1012 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 996944946 1250 996943696 996943721
    0x90c090403030b011b021503060307030f32070b16060614280b090d0f030f02060a09081e0c0715180501020607030c05090a0b131a0a030b040b130b04 65
    0x2042d0801c00581c0c603511414051001f8440d440c1e166160000003030704001d01030748000c1c00440489244010440030311540b008010441035025000104e1401c09040d02031030080720085500301d0142401407290202c0500480701902e00c4101c0503c0d150b076110401c07070340d01d0307003280440a04001207003060303180c12007081105000c0420010a680c0c0c4a94061903920101d0080d8220b4200110b002e84007070311244cbc101c4000710b4008000d440b1034403460074003030035034410340051000602030903000810510035805418410740c1d1202007540380c200794194070704800a1b140031001048604105080f950402048240302800080c1c0621019001c040303400b6142501020059158420385a41040b86a0b000310741c0c16401512410049000c80110b00201c03240d109980c3c00310780c010680ca81c0030600c0f64007400076180c1000c00805a8020b151520046c01c1e14842050218195040811800c6162071098010550584018002040300c49940001843d104001007500e04415034031108513216240c1400b48a164086 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 996946196 1250 996944946 996944987
    0x7031d07230312160321020c010f0e1504052d1605101b0803011805060d020a17030f041205010b190b180301180c0816050108090c090403030b01 63
    0x1401c1d4184075a03003e07160814146104c444070304001d15002c1e03c0c0b0b090000942c0300024009508480d444c000039000661080384541c0ba002d490114a000c0d40f140501603041d150080c1070319611001c004880082c0144111000e0245c80008181c4006a0000100703403607181d9035121010038681400c0741707030040c0c40c40c5144084114a804120b0b0380c6440ca18003007008c0d95807900000101c4414865801c50201a000521981c0000000190016100015000e1191fa22000e0040d5161101044200707001640003a51000203200308100040e068240c4000c8201c02da0103407800c004802c0d03000e0b10b0940050b0b20081d81ca201114540c000c00100780308014405104842600d035034411a1078030503031040c0602800c020800005170521800e190350703001f241c1d1041d000b8001c0c0428882c12110010002940c0d6088500c081580da01003206100410b224402900c0820001e804615140c01151600760242c034000c0b10b40511203401c92103450300340b0b5052090b070003510089101c218200004200c5000120845113850 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 996947446 1250 996946196 996946213
    0x717072d060302030703020712080a0f111204020111030d1409210904090c0305010204290922180209071416030e060706050a0f02040e07031d072303 65
    0xd4202103180d00356809840d0040c1c0f00d80d01c80409600071b214445024051580b1580c40160f11940190450710030035001406020b140860380c81c42d8140e400100000c0004031003071010780a019040390246500c28014580340c88031b0301d034210505041d0f51003081c0d0b80100584503044201031070040d0342e0282d04484483d0003031400541c1242d80242012030b005407000c94010000d18525555910b401010301f107600441103207183c0366649403160007035010340b24481c0700d60824003000d4090500c0344106c0043d03400b02c00c2410700d051000810441e4007400030400130841ca052428100d250030ba00c0c442c2c2c031000c46c0741d5a07210b04910254010015000001081071080200030450700c0024050b4000303850307402c0d01080041d09844071614003640c10711200c0d00e0362504180045100000e000c0d25030020340c010000030350200603090f0000b2189044c1e120703901800f00b50041200c0400c940c3c500c2544141140c040181540e035151005803045400c02c21990311000014100408084803e10740c070007044030032502200100f2441 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 996948696 1250 996947446 996947519
    0x40b0f0301050a060f02060a0b030c0a0801060906122604150f0e0603070f080603031e07032d0e03070902030901020d0516020a150608011104030308070815060903071707 74
    0x411008002c08c0381c0c203454410000179610104070100800341e000742405100f98462000318000d0500344100900e481c1404c00000e11901150954801c7c1900115128210741d001c0850722000c0c0080c030440d120303030041044005120034842020101011040d9540340d207000743c554005090700b09210105109090410501005030740041410744c0d48061420010019511080001d00b10f001d1035400740a9001319410940c12001c50070020042c1510070703140c0c211f9580c2c860065201c072034444400e00105a207100220100a0301813001e101d007810000f411121038503281c55080e810390b08151400d04840e90040342c81c10703541c2e00c01e0240c254040c49440880d43e200403000303c001d54800c802c05010381010403002082000500c00d80103540a0b10595000348002504101c201006034014401540058081c5000c1a0300a00c2001c3ca14052038903541e00107401480300c0c04000e00d69000403a815030601c20b11000190100044952024040c002000340030014075080c0f0032006000500c211d100540640c2d0343d8130301c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 996949946 1250 996948696 996948703
    0x15030105010c020f042c0d05090f04091a1503120d0930090b0306010915090509010f030515091207020406030b04060507030b0d0f02060906040b0f0301050a060f02 71
    0x1180e10929040e803031a10240081155901403802d000d41250421942d0340c0c448800da95000b625400c41040801745918900c0e11a840380294000d000000f1001c00040f0041e00d0301000b44502c81c6002000060000780b1640c82d210500c8030380c420290340803010b6042001a4951f8075209154000650281c881c080300c131a0000c00f54803a80c403216a039140d03207043c02d509000c041000c40001100060810903204102110100b000320818035490000c1d60100c80031071044020825a07004800c182c42d0080000d0a041a0746060f03444500d070700c2c0800c1207007a000942075841003407550003170400904004c50103045041c00c6050181c3c103180c074039180602e54203020220000291002d03000100e03c602a072544514400a00504100da2001d41001c9448007804280241c83c0e00550050440c1d46040007100040340a0002c0640c40140141c0b10b05141480704015007480002000c8404000344410714240e00e0b00c41c2c4000340e401458900010500120040c4001c1c04d020000b50701a040d00d081c18849591811002540c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 996951196 1250 996949946 996949949
    0xa060c50071215050a060510110d050403020f01080415060611010c050405092d090c04050a0c020307081305030d050705010e01051b16051f14040f0b0c040b07080702010806150301 78
    0x12941c0d80c0d88001175012030541c0c0224040c020040c030118590702d003d0401401c48507100e03400300341c0d03003d00140c3d099064061000c60302140e60241c03003c0305911900c401503404500041c02950510b10b49130340761842c008a8071503500600556110300031541e10580d1803908590040c1c0c030510520008120070f0045540b642c4c5155405819070401c0e20307142d0258085882c400b0711030303640349000c0300d10101031000d40705000c0b445840c40702c420755040000340c3c0c41908030415503003405c040002581080003406d0200d44128010908021062041c0303504550b98000310346024050ba000340c00207400860b40004100727080c06500c0c61103601c0d078000d1207141442c840d03000c0c520314103c0e21096207031b5000034180c804400d11070665500b20703042015a240703020042c5a401000d008000c85c406039916010020f81000b160480c6030b402035402241c80070a07601c141d0b54600c1c100d80d001d0100c1c20010350601c00001c0020441c0014503159201c1c14006880d1202e40c40003400c800750142c001c41c441c950f806400c07002c2070b1404081e2030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 996952446 1250 996951196 996951233
    0x261503101a03012f09090403050405190e0703020a2a031701050604090c110703110a0806150904020d120f030509010209100311091804020a060c500712 66
    0x161107020855050313610410010542140d02001007005054000005d00b049500c15180d61411120200020101078814002d5100c0c1c508072101140078103100358080c001102c41c50a0546899500d002c6a151424045290300c0200c0d00c51100e090415078000e44070034210040080410007075051400056a5019601510414039541e0700c424014900c1140720000d009076040c1034410868607801c04902070340030441041c0c01440c8003900000c1c95200043c02501c50b402d10039000b4070850101c41003003180640034005170b90041608054801142030307408030000a03445900d8201054110b68805003d0750350050545910b07074414081c9411584800c0d5400c000034009280c009800c0d900020702d964180501c851440c0c20100d0406081285d1495407209030042e802160004241596803000300e51201e640800200052124842010008a00311001c10403a41490040b10940200003180e84158a560390554035001c070460120504001444058084c0c039644e9510f009102446e1039040309001c0c03080302e06 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 996953696 1250 996952446 996952511
    0xc0c0919021314060a0c0212031b06040506100303230d020c01090203070b0405150304020d020402070305092b030e04150e040b0106261503101a0301 65
    0xc00c0502000030314100341141800840d110307144030310141c1ca5020075000d5265161890582021240340c80c42c1039030f80b40080d030303500c02c814000e0315800d100c0348011104044500f03100500c034094140c0e0030300144810700d90910004003240d1a0508220349070910140c45000a00c0d44202d05002080d4440050608004020701801132485039801e03d0815104261131003841504c0072070b0346128020103401c9601202e000b00c0403502d800c0e8651000840318807a510a903640f10070303d82ca2076032024003140d02540d030081c00144803550800c400e4000c24183d03441035504400140700080d200c1558a000f44c00320300f002d0030304004082d0301e070000c483d541c07801107420101406100603c3c4107404541d41d0740c0c0200e0382590b00c4200b14080c041c1d9070000303003094000030354045031208c0c0300c6c070000704450340304180310b0702803881250300c2c45450000d10381c84400714000607003616184008504030641c0c40d241082021003100b00001c0006000b80303200a20125900d41800c15031082e414080d00e60860502c0c403c24001c01070748401078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 996954946 1250 996953696 996953701
    0x1030204021b06090309031c021f0f110715060501210e0703060c080f040c030803091e0309010f0804020310050709090509061803070308010b130302040603050616050c0c09 75
    0xa00c03100421550125030b1600c10700080020380c61010010388841c100079011540810540300184a548000d030411400503440395503440003a01604008032081613124400050751142e490040064a840e0b410faa400b9101c005254410402c4000c410b10300b1130710107a0100315040c103080000b00240300848030741502c0b8900c100c01203c049a182e00c00040010b240c03046a210f280e80385040405810004020710104140c00000342e8115500c1c510301d4071035680600c124600d06d05550700c40da119000030302034a19512511801c0441c0b003090300e00a02880754600c0041d034950180400051111000c1c4110380104585002400016180025408480d14001c84086481e540c2c0e0441290a589998081940f07d810541408400c100c0854200d009030f40091820111000c0202d0140e564400d2000080009035488010803480d804e0802401e04003030f01103440c03010b60765241c00080c10b880c40c642055455401c0041070001503203160303607696508580b50425074140000c1030b14860300d40c4c050702d07c030502444c0b51400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 996956196 1250 996954946 996954967
    0xe090412180b04090b04140114040906110a020c0a120308130206070b0705070203070b19030f0e01090b10090e0d0f0215070804151a0111150412080a060605030103020402 74
    0xc040d40030b000712001158885540e507021101411a2190b002e020358500402d84842c13003071014626050703a480440c4002c1c0c000d00c84003400300400d03c070b4006858060b42d889828032240b98450062005094030350060500d005860100060784025a100001402d04221542e002a0700110b100c0c0d8421200d200400005035076002250052080000c000c1100481c5810040035640000141c00e9050096040380c05170358070780c5423a03500c0d07100b080e01e000b442040c0038090901851181c1c005040281414101240c0c00060703002050a40302a4a000c41e03025070320703008202c1860607415200f0000d01107048107000242e962800075880307050012950040124070001c0c5100b650081141d41115a140c0051880b180380101c002044800c0649080341ca14014085d520340300d000c540140c83c4140114016024503100754401500c88031000c9000d80520301919071000003400e090104a40b080c1d001d202c20700300721981142c006040c84070083c5014902841c1120507c1582d500c10203803810740c0d0781902d0042e51240c10b443c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 996957446 1250 996956196 996956237
    0x1508070515070209070c110105040e0a0b01030b0a0b18090c04120321090605150616150e0609121204060b010c02030a03030605041a031c0507050303160e090412 70
    0x142c0070b5040003c1c035042c045080c0e800900703004010b00030811036408038101d0b001100c1303070710036881101c4000010a000c5030710340c1c3d01503020302180e400c141400a000300080001c554a048240d10480f4440b034085a102da0542c01804c9000344031004840c1981c09140154040c0d82038003c601074045103110b014680c00405000300036100d501079038082210000c0e4069038000c005401d0b41c020803503c50b828100031032074035003070b01d21030340c002c400c000b07204d24109200c0d440e055200452408080d20620202c1d03000101404042c0700d10322810455401400c2c4915041595514000b101d541080069108011122240d01035008640d00030794421000702e025440903004071100d00d0985000703541030003050328032020140c251f400034007164003d4405102910482d07050b5429403002c0806c40f03401d900481442c403096400150391640181050410700d05250041c0c584600d141c00444c0d80889180c0c0e46150700e40c40c50b070800b00c0c0c1c2401401c226505801071800380c3d0307001062610b6045200503c50f400881d00009076411 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 996958696 1250 996957446 996957457
    0x2010b0906060d2c010b0114120109180803040c060801080a2402040503010e0609010605010c0f02040e0312041b23012a0501020304151107080a0e040617011508070515 73
    0xa2801c600c5084c00c020414020f005011810740800d06014403200d11941800640d590010410450901a0720703205829000e032006018440d080c0300d11052402c00151600041c2d4002c50140c0f4801c0906401e209000d80300c403e060b0020022507000304804030008031008041d620440340d6921450703001141400501c040c0c012500019455403c28401c80050480029071138030807a0130100900020303940f040150750a4004210103070031039101050000250400750400140e08500c1004c903854442e070100c940c00c02e59000c0e05c04881079185a4892022012203100d0100507100f860401c0388280c0307520140261090b4015038890511400c0d00340f10a004242c140c1c080b2079101c0740b95681000031b0007443c0c954000d5000b06c80494400c5c242c0c4030400c600308010301c626000079070042c20341380c58884a03885030036480c0c005100c0c090400201c0d6480130b0050b2254064280109a1030082c0141581c121280509541c6100b45027503e0040085080105460004e07200741140d4098a03808100084480190f000c1e200300c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 996959946 1250 996958696 996958751
    0x51b18010e060412050606090c04050121020f0c010c050f0d200418062309042d02011e090512011b050c0f060103030c06021c050a02090102010b0906060d 67
    0x20800240138841042c000041a2040c02034850b65600c4500300110001d0980780d00c041d030b0380140418030503540142d6912100740b04660030040c44480d041c01400036030380310f0415600c2413440451003c885071001d00840302890700da03042072410140b075003041440b14007800d02d00b0307031041d40c40f107074100450601100741c0d844011004000c41c0c0d0f02c1d0b880b580842024420007840e00300342c900d40074001035040d48564428602d43d400040e1051419400801c008552001a000b941e14038110300868411028200c0040c4c440802c00c148609090b00c4c0303000142c4821451070000000c40102a029115141d000c15000140d07081210035404003803810009030300403ca000003241c112520164030700311054000c0702030110022140101c6040c10000c85c901609c4040071321005001c1781c494102440045c503103801409400311454240000c040fa0401c081e01515001d0312216a000e9000456100343c0d6428041c85002d01401e45094005007000c4020540314811074240d2800c6903a02c0449031101400b141c1480c204004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 996961196 1250 996959946 996959959
    0x60f0f020a020d020f07290c0a06060b0c1c03020d06082503080d0c0309080a0917190f0305040503060c030601180b18060405040f0b0301051b18010e 65
    0x6100a14002540880d64a01c0503118042500f0340482c40043c00d02000d0942c600a00402d900c0e00d01021008421202d03105036603940340350703144c9001580c88041c081030104200189808012810483c040b01c029401c0ba4011207400c20140814040c00140c03200025003080d22402605400b2400b10000c0c0160f00ca0390302c0050a0802c00204114001080382601d2194070b040781030892200303800d183c50011880000c100d01000d100114810400e682712125030980c80c03c0108400400b9515040e5944c026500c9d4000310364140030a1145400c4402c290903031041210081662440d00f01a241b14900da0820080050358071241d020f08152144064070010203000c2c080711240d003010308580d5000d400c2162240c0c005601c103980401000a903c115000711025602124504001c0003180c0345502c102842c0c0d5504a402000b00040302c0d103482c41100c610035200c074000500224808109030039900d01070010780c1742c40b50440c9080448144081102c0350300d4070340c803003000d5004101c05c0169841c0e46141e150319800030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 996962446 1250 996961196 996961211
    0x516030216080a02031005040218042405150102122b060b0c0c01022b030615020304261f060f090c030507080103030813140a0f03092907060f 62
    0x10002030003071501d413003103055401486075003408404599040320060340c080b03a0714080c4100c00e0031844005401030302503840311b059080f89190b00c1d01034031188695624800d981c1e03030030802d264041c80d1015869000910241c150364251040d600f0340c5004407804800d102101031410b40302c8200d01c114404040d2040c1d0028840c159849083d100300e90402c02080c00720f40a0000c1d0f140b0550f10100f652505500007881d105000421107c901c020f040140c06107605040c0d030395401041800c455000e640408009900442d41c0d6410b050a05148403031034403c0900501000c1c1c807081c08038001180080c40003020707a45101c41e40c0618828078001e0003c940c040401d00420001c04988102c040e040b502c4070281c9500c0620594031441c40171030700c4001c05d01c8040e0014680c90f0202d400c0502c6110f01c5000503010740c0390700003561072403c0c10ba400c040000e0750490340584001000c03002c00d03801c2002c0d9001482141e5210801c546103001140c00036204c00540c6900e20000950401002503685c0300700010f0010301000c01440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 996963696 1250 996962446 996962459
    0xa050d0c050702091b03070309240c0e150d0209220209090606030423070504051f06080702210705031309110406050706181401050103210516030216 65
    0x90740440380590250b003801c4c001801c200b00003a03148070342c01c00c04800d55103581e4603c41c048000b405801021a00e40c844091003803a103a000c03200b00b02e5950051f0314002461410900e0140c40109003691a80c02035420325000d1701c030114000e09603000200b1048015030b0351013510780010044910004021a04400d03040f440000030071680c0a40890801a10341d00001e03103c8908008140c04102c1c6e004106c003800c4182c0914502c026581c007814114244100c0ba82540c40e100040c1c00d9440807108c8040c000c400314100e109503140b80091800030441414003003102c1c02c01041c002d40b110061a56603402c812a003260420300442d1600f01d80c4901d400c5410b87ea150401c261100301381131790300e00c60610700344e05041240b00f02d940804212421111185c854925000f480d03547c10020b0720032008000007562002c0042004207885c0020080081c030440b00018440d810b51900f01e9a00004686121071414903810094100f0b80102c210790b941d1001c068840b504d2515440c04030b140a000a04140c8549005000041c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 996964946 1250 996963696 996963707
    0x41e020d08030f0a0b031c050d1a130204050a170a06020406200c0102100b0301180f06060906030c060c140d121a0a03021003180f0221060a020a050d0c 66
    0x9040b4445800901e0b1a04813001081e294200c0300d456254005801b80302105881c1c5030040705000160603d2414146041c00100403170703002c00c005e00004040b414550b025842c0c0030601c0030511442040c11401e05061501044032150a8020305104858074040308024800030000c0c0703400640d00a10a5540e940c58940040c46544401d00446080c0801244103110f0403000c42c01c1199188113070f00070040e202070050900041c000711640c190301550782c0d44118001c510b0814502c400355008094a1850644030b24203803080b60300550014413282e103001d0381840090006800f02040310034915080c02c0340d81450a0801c0a103c1e0700c0c411803520310800401c882010780250468503403040f543c404108200348040200440c1c03840c0c404907a80706081140c10f00c010714050581c2c040c599510302e00000c010078001032801c1c10b5000600240ca4041e4200130032411444d04046e450921301c0c6103400d100c2e95926000c0140d40d0b0b2980079165804264000c10124003540c030480c10f403000303e032448405000300400d20402615 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 996966196 1250 996964946 996964951
    0xb0c0f090a1502060f090c1e04110306090f01030507060518090907080f07050a0603020c0a050a030801051f1709010b180f16050d020a030b041b032003041e020d0803 72
    0x15004540000e600c2c3c0316034880c61882000d000010300078034880e41c002c000e07010800180a005040240740708c40c03240d07100d51040c1104c00c9692500c0b5a03807420440100070030201c00a106071203824840e0010720000d0030209584048442900b49141c0701c0c04c4906864040e44003100307010b1307003020765101001145100050040101d4007070f8010348440c4500703420920b8a4101500900b904000005d80400c82d0034803d2780200312528046c01170b00c0c0702c034015903907081c00c00200c40c009074005461100107103e01c1c54510b08044030000c039100c4c00216803000c180c002d401c1031450030038044180c191200260b220343c001e40003040d9841005120324402c88900600c2c0d0151f880c00d81d540100721081c000012041c030021071404103240015194241040b2400e501c0c8000ba50080101d2020581ca07102920313a43e444502811400006020b00a8941d4032403c000030201c80780c1e103504003a40f028850b12201042400c90071030342c000390840c6141402400703001c1c030724040e0008144003d421241024140c428805550080e50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 996967446 1250 996966196 996966239
    0x170a0f02100314131713050f03070312020a061103063304230108070507080304110405010303050a02010e12070f172701020c10081b040f0302010810030b0c0f090a 71
    0x85c00034030040c61490740e501a2084203400710b00c400c80c06001e00d103401e1003c0daa04e00801011955403540325940c408846101003144009a401b103001030040103180c0c043c449a40c04988400c1342180351410025402081541c20381602c1c070689940220310b0311489100982d01d05108228681d40c50b0744a4030400541084411495a06003a0181c1d114540c40380f12a85d016103510b0b607138142044065180c000c11584090402c0310303601d43c9905050442e44407401110300a5001e078540c10b80303071445020082e0941e104001c030b910660300701e804c0d043c05d18100001507038030b400c2c8c03c607201c00c8048401d4681305801e480d0350754420300600c2000c500050450120340c0300101c69503031555000c030240c0e0389200581e40d4041203402c00794402940150014503520400802d980111002c3c003038280721300170440c041442d90044d0015102840441014000d550708007098942194983c88005c441524507120f440c43c004000c1e10415050340001641050740d181c42055800604004005181d6107035215040612954000b501c0c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 996968696 1250 996967446 996967463
    0x4050a0f020414130506060f0c070302030703030807021506011b020d15051006020105090d05032d01080c031b04240b19030506010c170408031201170a0f0210031413 72
    0xe40e00814013509010314400780c6108c1c208540c410491255402c81d80602c0703880d100310389001016a50030003803280154001d44840000741885d46000742402d20341c0c20141080c0031030f8814800c40d0303640880b0005200c050300400500d4400c1610029507146070001015080c0c2d039000b61194407542241d0711403401a8244400500400d640385420790907120102e40c4040c0f00e40060190165480c0500f000f1a03004124600d404507640321100c1100a071503403a85512004140c0d00d0052203291420845694445800c45c000c02c1160040c003145040c1c110380ba034443c1c2c0910348505080f400d0780d412884200d01004102d0300e82e5841c54032080221040d8110b6080a401c0d04500c64200d071255019108550050206a44503141c420a90f00c45504400300c40d10b107045940b40400000821180034030140013440c01400040d60503502d08003110b50119a441c1104045800c40c1d00c800000640030b500e030b400310350b43c181d5007010106a125001c0e00104031083c020854044002c01b00a161a2071407031302500c940c0f280d0b050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 996969946 1250 996968696 996968719
    0x230c0a0302070c0e01080c090408160c05101707030618021b06400611090d060504060c0509060307030b01090b19180b070803040512070c14060f030604050a0f020414 72
    0x40000302230003528046c0c0810b41c100a40341101249034240c40501e400b60b000711820541c4c51010030100c41e01402190001150410000c1200042d003c81580242261509101050030400b40121030001038019001e01c40e400586119414510b98031310b50031500d00da054a0041c80c0000008400d0480c6c140c81600715000046020000750170030804400080100558040106540d65280e000300b00c400401c441c00702c0c0500c40c0021039616410203080c9584202800700d80c9050601d410006d85283e4104101880024483c6c00a03540713500c0141e03640325580c0d2070f020400072032580040c0d81c0f00d82141c1040401c07480c0040c403070004503603170500841c40c0015a5038443d1040c29a004110000301c1c14001d04a00080410108000c103100002841d0001d001d0415281ca030a45510301200c01ea21a0404440c0c00361014001c2140c401500e226040c40d10050342c8240ca08074090303101d003076a0310005000c140310f159184041000070286a100700c44a207103c10046580d0f0b80c5424200d02030351035907100701c1d2007101c1e070199 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 996971196 1250 996969946 996969949
    0x21f020f070b16020d05010e1015050306010312050d0b0306070f2d0c05030f1315020a02031905030702300109021e060d140a230c0a0302070c0e01080c 66
    0xc8a120100090f02e00102462660800101d020343c0f09058880e0344d202c2d80c042c3c0c2108820301c040007501401c046c0005850510324903038402c0b050301d544040c0c8250003440040005c11724042c4a4803c40c01d0501e0040d5403084003045000040c05012415905845404200701603683c00040e10401102c0c252188004114020002d50403020580e05c448110007502070900340c483c1c041c80b850074819201c2c2c4103885c10140d038a0700b510b00319000504035200000c1c1c00b00e0100420b01c06421080d04e807d4580c4041c042100031303070700480d07a02c505140084403226501d580800a004d810301c103a4181d158010503500c0c0c0004020203840940d1100705545020081e000b4503151102d01c1442040140c540c0a00107035009074400740e01e07180711203a13410b450b50080340030003c41751443c0652050000c00a86a1100041c500300001040100c410992a08030030003449121000201d50350714003c1d0340600307241d010550364401c825040300a4028004000c014030b41010000c00c0560100035280d058401074000c46092001200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 996972446 1250 996971196 996971219
    0xd060b060409022113020f0103020a050c0a12080108070b03010e04030e10020109030806030c150a030b0d051c0503150907050c07030b06100c0803130c0308120421090b07021f020f07 79
    0x2000350b1090313009107c5c014a50003038014145601507403c1031818518124081c0b402e00d0102d110442c0d2106c01c40310044080d0b0341180d0311901422040c00100001410301402e251184818003a070401d0713003c007800160030103116042c005003480016000358992117485101078080c05010108401090040d000102d181c2000126031544240c0102590014401c1d0b0700002a65840b88030301e4000c168031480001100e8503800750080e6001d102d403002340940b880c840750411300e9800c41e180035020000300700306022a001c0e6413403612407908002c840100094581503c140c0b401d00c15031071004620b0045580000601114030b264a205c0c0e58191440c4a55081294080b10f15100500c00103000d01c0043c400f05030600c0004080b42c0d50584600303000004951241c07103000043d0810811f8032458600c0b0410401042100940721100108022355891100e00e03462028001800501a160f0300316400314401043d55501001e0710311480c030303815200c400d94803079001c02500e0710070030140300c40c1314820144c2c0042c0000740b20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 996973696 1250 996972446 996972481
    0xb09010f03021b06130b1605121911120f070f0f05070b101410020c1e060d02041e0302030706120f14091b0d060b0604090221 55
    0x5940c0e44140c900030100507002500031200000d412602961140c8000f0b40410146018548202c0003040c160b44514095a41520080040c0c001c0384115030003801081e0084162001d4020308030440107990303100324203507400000c8503601040190500c480001c080030302c20010800201c40c50382c0c01140355941400d00c00000d005643c0c0e9000a965140a155660320a81c1d45074085c1c021450107a1034410941c0703404840c0e50007031302c00b007140085144080110703000c0380e41c0303e0320480e805a421200c0b0300303c1c2082c041d440d52030001400c0d010310034851502d004410710300581c6200003170007010503458030350b0021600001e42081c00351a4880000300c01c1645100e14118030702c812603500034001c01c041420260b044030018090030484040e2a143d807240a0008040c2c000d180c0140041d00d00c90724146002c0e4040b601e0301e81c0803c600c48141c075503071100100310f4961032951501380d600803070b01082c5920f0036004141d80744569400a403006102142189640d50100042904420382424900554540e200c1100c400e07920b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 996974946 1250 996973696 996973699
    0x60e010e060906160b07031a010c020a290c03040302010905090c071e02120114010f0806150a03080a031401090e030901180f0f0e09010e1207021302160c0b09 69
    0x14072008500d0f2900074014990030901d030101480400c0d29680350111007000340c07030b2080030944400e03442202034101c04003d2440182440c0007000c011043c0c012540110960003a10031a0340c101d143d481c21000d020100305044038110010f55a1554034000d5507440f40c01c18082240003520b01c100021311440d25540c82c41c050f51440c444186071130700070f6075050424410115403049090607080c2c1403026071344108005075030071191030021a0500c1d1060110400444c141c025098030b0f450080e060111000020344950b00454914424081c6100b400c000746011034164001004804001010344813141d054000d045402001325041e4010313601da1011106a480c401c13071550060f40305009690180d0703c500b0030a41d08030010305a06042c80c3d180c0003440c80d0002250803414644852100030401c010040c4100c0c0d034045940c0000b0000942c2d0181c8207a11115800072501d103200d0086140819950b826a803662540b2a981017190354000d100c14846241c1407410055883c40e030300c10400a07494010304210742c0f19000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 996976196 1250 996974946 996974959
    0x60306030314030916090504022b0212030d110a03200f130b030a0903110309010e060318070f0303031b020705010302220605190207030209040803180601030804060e010e 74
    0xc81004156402c010700150382480740714070005102401c0c5e030840c07000d8001c003000418180340500601074888001504060400da45104000d5034108002c2e03040d190039811030310702c50b40d41c2f1002c49061450151101c800c84003031038159074032a9804080300030080d1104a84080c07060a8140ea00a0780306100d0107004c52409e01d0800c203000050300c4000041c0842e0b081f00b010b4003917080d101c1da4060320b03a81088400d40d00c1d0303e590752030540c14190440e101d0310b408070351180214901241100004c1c02c0306103a0010314000c0c4000310228412810100159000d081114200c0320104c3d9203040906400e03601d844164013103450301c0140c001d26240387c2c0b00c000c1040c0f079a80040c02854a4000114000d41c002158089500200c0101a2500e12030400c040300516a039940c640d1030303209481c40400071f140308450754010356110b82402c00040e151501030991080d000b6080b140c40303a9501c0031240c0d0702d904000b034800840c0181e03400401003045050141040e00d0390360ba140e12500d4851301c01950080654020190f2102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 996977446 1250 996976196 996976217
    0x70f080c1314040f0606050c07050f0f0105090d0614041109071d041d03070219030f0f290703051b07080d0204031a0105271609120b0405070603060303 66
    0x50410119042c0c041d0180000030750601d90880e03c801c442660300f21000040c40081ca03008140b0040081802610045030142e0040651100094501c201c04100c4c45c1030100c0032440c860aa540c014860f5201e542000041c8189050441603a4081504880031100703035040d0f4014140e142407413244a4420307081a1600c000b40b00091080b41801180443d02c1c44c0e2103034450356103c02c51250342c8078100e034100008008544030303105881040040420110000c4015000c00c0e020808283d10f00c01c940c501e43d030001c2c5203000b0b8200c2818114100c031184007008043c0b880c02c4201c40d0521011801d000c0c0300700c0c1c540d50200010b840d1042e4141d40c1e9159103038408420304044c040e1201007000d1500400c5c00315407081c0c00616040d925643c0d402d0801c00345944c00380d102040e0004107c05d080920020324103004001c2c8200306010034907030019050b540a0204944140f0341420101101c0c00790a00b040601041d4414800441a0386004841e036a0304a0f0101e07054042d5403c0016079034080d014080c1a00e0f8103886156031038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 996978696 1250 996977446 996977459
    0xa090308040b0606090307091e0903050307120b22110408070e0c040317071506051e040b060418060f060801030b042a090506030d0e190806070f080c13 66
    0x540207032510342d1004c010032820300a0380e001c0004d031000302003a10340440c01003400c0308200d0104030807000603080c06080024490000f07078402d048a6000b031180c100000445d010300910001049180030582e042000c203030700d601612207100051a019044e02205010100c07121840c6121800b440c41100819440b1807004c1c01907461511280d03500075411904981490303607a03100d0a000c03803105c0300004c83c1c180c800140d440610681c00030300107815480c140d040c0300031450440882c2d4008410807841440f05240c802a020558550b080805007402c02410180c940c1d894100070200043d282a14141c040e1a203400060010300d149102d2003101d002c3d84071665039a12319100c4000d0400000d1044441d80100e00c089c0c01d44800b400c3c649002000c60f000c0c82c14a043c2400c0e9000110350024014078400c1d80090103949003030741e21101c0070018540984101102200070050f04c0c1d40307103075690004031540c06a03408014070300313500004550304e000c030507520642d494541d440f00400078031900b02c0c00007120071040014003d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 996979946 1250 996978696 996978713
    0x16060b1f0302090103140f0f010e0f060103050a021b160f0803090907050d1b030c05180609040906090f020301060f0b090d1a1303090b0c100905010603140c0102060a09030804 76
    0x240c3e00c040c140030490780c5220360402c0d1300f002d0484440303000008660600c0002c45804005502501090b9a5548207090158901044c0080103041904040d26880010401819501640e904a07007009402c03240c1007840345d01c1c03504c800329003c04245510308480300084184070508050111070703010004d18586910003052010b4184002d041d042072000402100950f00111b115182140343c034407040000040012400a0a9941d00c9608804006080c441100f1500071082d940780118012130f0003c1d620b94005000c90302509401d20058001c0b0b180122143c01e02444c58040c000c802d02c228002c014840c0c40d007810b030100a105025018403600c06001c07100250801103d030982c0940030b441401c6803070038041c604001c000000c80d4a207039407003101c8406400305074014240002404030000c0003030600c100c65052607920400d15020800d019180d80149040c0301003980500c01441d049845e8403000c0d546c04080f91b682d0002400c1081c014801c1100080e40c4420a1050201c200e516554041580e103070764a92401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 996981196 1250 996979946 996979957
    0x120c0307030e060a050601141908190c09051008090a151103090a030201060f050d1704050d031d01030203041718130f0b0306010305032b0216060b1f0302 67
    0x14907942c2d05100749200001c120862090608600120795464008001001d20b034040038800c12128040c004a00707524490007410044c10345621308031800d6600c0458641c11894180300900c032981c0380030300c071018042c1d1296851050300c1040e208a0010900315804456104045450f4001600284403400000e12480071908101d20ba2640115288600c50603d000c00e43c41a103810a6070350003c00e1140400d83c081c00b8940080088500c10700a9610b042c011034500201e41e03900608010b020104594a81301520649015000240108000a41c1460043d00001c010b035146603140c6c80500740c41510751f1003402260710651744280030013602d0241505c2d021241d0440d40600e455170101005c2c54016407550302c1c04070302c034103642d050200e40d400200726600125007030440c0d154045d8001d04010310104500000b203590707401e4038100a0307007000001580c4a8690b00c5d00c0d2069007400c2c1c00001c182d881641440307030150445001d140d00b0810240c1000400c0b00c04040c07400f0032a589140220a09005e0b0301940c043c14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 996982446 1250 996981196 996981211
    0x31b030702100e1201060305030a0c0c1e05120118060c0302071b181a010c020d1202060f0606070f030503060d0b040614071418060712110f03120c03 65
    0xa0800da12a800110000c0000d251000040d4581034940c0680ca4102e014807107068810000304000d508603142d41d610303803040328200d0b018804580c0c003074020840b0040010b4010250212401007c2d004040701511084035445103c2c8251103284003032107482c1040c82900c4460500c0d0304201001406680e802026001144d0742006040d82032003000c011404800c1000c003004600352401c0040c41c09d20100c804564121002c1c5031030540f40c6041e40305424428580c90b03a15040900b4030400900c0c6a2000840094040c0300080c00b80515850b02c2c40200c0c0c0006407a405190155401d01c403e41d1131005100843c09038800240c455401c166030b15010034001d01c010342c1c0000b0050402032245101d0f03200c5000c0c103c01a5001c03100941d80745121141c058040d00318a800244070314000210902450b0303200a00d0242c0c0005100c6000124003510059641e4811517050f0b41c0d00071450388513500d1900002d004c0008140c050281800ba100f00040c6108011040b145800d40c410407a03600e039100c10030060460b4200a050a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 996983696 1250 996982446 996982453
    0x80f0f04022d01181206240b090a14090f04110409050312060906090a020906070218100b030615031f15021005060a141302030a060303110f031b 63
    0x55a580404060b481c044041900c0c09200d0807584000050082058a540d00c14080752000280301d40c20f42400300101c0650448004249180500c21030400b03002c4c807030203180405001034800240141c100e0301814500504a4515010583d100721140000c1882881d403648081e00a0004d2b080c0c1c80d00358100da0300b140c0186072100e0814007000214045880600c0d044d5625030020405a031240ca004115a0740407078142d83d10000c030308110001c261429406803030407842607004611020541c980906035100d081c0c00409111100903031012a00403101c050790807202c3d03941c2043c80422851140803c0303a00602c0c01070080d0503c49040c0d00071045a03000030340320410300c8060009071501001044801c0e00a009031a403440d282c4810080c010b45041280c982001038581400100103607640c5042c0300c1c604440e014a2032500940d8240000b0f226034040f000305007480741c40801400480c07000390384500243d178444c0c0c0300c00c008550000c05040ea00c80c140038000c140c0341e008015081500003035181c0300001480760401c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 996984946 1250 996983696 996983719
    0x19180b03071d121f11040303050d0e072c041e02030c060409020a08010e061525060608010608010b0a030f0302070f0303050a081f06030c110a080316080f0f0402 70
    0x34080c2c40c3c0c0c00d6404070240c1c06404480080c4210500c030812528030440304204004120702c811001e40150310028062190200300342000030200d40210040b40b4041c1d0568010701d48a100042101780f1014074a00308117403014461211020717001505000d103410003041000b1856402800c0e1a41041c150226018003440c5075030b003400c0d2a214003034006445607a03400b50703c0b4030b20224024500601680191214007140d0b007030104d0f0b5150101c410100002410881d541c1d03901401c2044070030f5080c1800000711a65045440c0107104841d881002941c00710300080c80125903c1c0b0003642614080700580c0c0c0c2c0082c1074602080003502c00d00030080300f02d1117401510710701c540e1040ca0700030351a400d9000b640030500c0011030303151280d4407004c4903500c0410780c6d07480c492280740f50182c4941ca0009000300d4061540d29241081da040c000c0d81056003401c580000c0302d50750540c1e071410320f80e80d400560b01484132184a50141c080640503204251082081a840544983d1a02002c2310340c0300f409031050f80c204000449 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 996986196 1250 996984946 996984949
    0x302030f061c17070618030f0f051204050d0207050102031216020a02061206090f0405031902120c0714060403050d0e1324080319030209031219180b03071d 68
    0xc2400702d0030104070226100c400b50700344003003035600c1b031040c030300c80d500c0210310305d10000b40c1150701220102c68524044088141420003130310b00b4480c60b00c80030900240b59040004019000a2014a4103210340c2906c101569880040e07a4074007602c540320307950a40d124001011540c1e0703569194141c0c035880c8100c0f00750460940103c2d990b030f03014141c080b21072403000041103440ccc100070b41a65048200301640425600c2c3c55240d4980701d00403422858016609950041a968030801280400700c0d017200600b9940d151308203507596102c000784160302000759281c40b20f00e500d1138450309441c11241c204001e0440076000013822101980c12402031907028500b00740c1c071407218640e48170f291914407002c0c1e44007550000600725860181d150340d00102860344204100c0040320301d1001c92154405142c140580c8800c1c0200000303050080048078020f22100215803110307400c8141a40c001d0310107164a900300040210000780008e50528061245c1c03455042000c50350103481449200283c0b01740d0311541c22441181070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 996987446 1250 996986196 996986213
    0x29010f060315052715150922020a020106050a141203130306090b060d02031018050105090102040e130503041208120103050705040e1b19080d0f0e010302030f061c 71
    0x40b940a44501500707094505401140c2d1300a41020210340340400a20384080041c4021400d21010003e291010940341410b40718200003d0060310240c007860700712192485440001d401c090119001503080c0180010036007013020440d4251105104801410b440d94002c3c002116601607030105144010044145502c80c840d000801652003950b001c940010705003440d42e41c0d0040030708014418590500c0440043e41d00181d81400466072030b8020400040200300c510623628803c0025126500300000c00070006819402001601d810f4100300031262140018400b0345014a00003e02580c03080105001c02c1c90070320811903810748504010f620b0460358801d2031100304000c0c2d00486650b0b12007a014801850180992228441124024012944003000c1d4039840f0034250f0301e0502517a1083c0303084074110000c004442c00381481c02e040701c002e80526032000b005102b0111005002a1050710349110940c030034022a0b0007030020b81e001c40903503165001044410700e50845060540305d0000841c200051401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 996988696 1250 996987446 996987469
    0xb0a110d0504050304031401021315020102040b0c060703050c120705090f060a0905030d0c0203070b0c1608071d04151a0312071709010c08070206130329010f06031505 73
    0x38405551174500d50b180c02600f00300104c1d88440d80340d006000e900040c0700800340307000c100d41480708400c40c401c00000c402d9009100c1e03a0400c4005d0200000c8101003d4000620607006814603078003003220ba9100c01a60070350b4015140c1c0080102180404240c3c024441c80107044c45100082191070120503243c00036415070300c07212019020030303598101007190b45820304c1190807a80c030600b030a08540440c0d40c0080c1d12148940130348841074601040300f0b15080c80401c20800242000d0040030349241d00c51880d1980c1d007680d4440c41040c028140c05450110048c0242580215403020701038681c120701c03544410150040c91101c008182c80349400c0760b019641004601d04120400c00000d80d01c28203801c280c035141100d107420103c40c010412108010781da100c2100500940c1010340e0644805a82c80040c5040c42114010f039408000790002100f4440391410350401d591455031611304102682c0b0218513800802d2041101d841c0301174200f08021402a005942d000a41c180e03055441074a510010700f1500303c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 996989946 1250 996988696 996988703
    0x100e07030e010510061b080706110c010606050a09063b03010506040c08040f0606030203010f0c0f021c0f050712051b070b0a0e040e01090b10120b0a110d0504 69
    0x1241142280c0700020b103d140e4001060080403070343c80c1e051020207401d500c0c030340810105813004500207405004d170103400d42c0d007140e9000c2400d2082100d001407a0840340c006a580c0a0342d94640704002074110702490031600c0c4099103460300301340c9914003c000d07038150400440103a0405410401d540c0d020b5043c03031020820b5602840040e0418081c0d000745400c648000b0035081c0078600e8000030042e9150403011a6610a41c841039142511075645401c10181249520003901982000380b0804540c1c5d644e0061103200c50380350b0f5080040c0103040000c07a5150f000da00000c1ca101c01102e2654400e03031203112841e40d9001c007400c000e4544030b031b10742d110192104912034840000e00082a66070031010341c0150f1902c1e034003148000340202401c0070820982441914014810700ca0120741031902c40d140d50700200b448240301c80c000c00c0382428905000703242c048119407008410764180e10108414a04c410200300403508001c81c956588c0c0c0300300780e8200501c20014504440b480038450021640c03400d005040c4603521 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 996991196 1250 996989946 996989951
    0x20c0a080318031216050c070303030227090a05060411070f05071205030405041e020a090609090603030509090405011d07030501051b16031412090f0d05070308100e0703 74
    0x1010901c10707008074022042c07041a80c004001401d0410004039200d900030340c0c0c0e42ca440f0080002003005441a101e203032803840880c019500000117054059000e002c41e18203818001000c9041d45880c6080c1594500748103601114000201d4581c00f40c9a01203035125802070000074903002e100703203c0c0c22590003500048400140000c401420000280456001011b100c410140058010b58805481303005d640034044c0601c2c0d548603d0134a4060128210241d003407005000c43d070b955110035004140d0240c074087c41c0b0215a4091001034040e0443c45a04202c039010387d186070802422008009140c000a00151034640d229208805040c03031046107440141b820000604829196240942c2500c400a00c1c6032108203202c044d80d60301d001d030fa00c1261070541d12190042ea201e130082c88d003910341c0d06840205066090020903080920040c050455000740d03683e02c00c554902c98503c2c040f41e9602e0504070342c13a00251042c040100003900032036a6640080d0609900303c4000c0d16514400900103048440c2030000340c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 996992446 1250 996991196 996991201
    0x3040f0b041502120a1404022812060c091e09090218010608070e03030a0903020d020414070c02042405150c010903051207020a23010e01110a09090204060e0d030201020c0a0803 77
    0x600e02e2040c08800d581d40201c0c1106c85c60190001110804012046080c248017240b091941c201403011023800b418060f85c1c091000d4200b410108000c01c40f4000c81000304401a001023140400303400d091000d20403a10321090010704007030071800600001e1000300e0700070000350350442000350049282c5000e081c8958441c14240b8107004028400100071003031a020380c02c00c020074807000d640101030100362901030355030503840c0c00a440441d0080c00d00340101d0030501803103c20f1011403030f8000310350701e01a8021181031000180444607000c41444881c0300108000b644c8e101000b43d0300705000703680021110b8020290502000040c2d05003035618200041300003030000900d02c0410320790007064641003a09031001704220381c0b10b80d50300c2d00e109017001002c41e0510030180c007414510009400220010f144000240502001c0e110048810b4100c69045004106004004528a0340c0b03071081e98100d035030903540c0210300700d03030034051003030500d0510310640441d5001c1040040c003800402c2420401c61045059a6903071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 996993696 1250 996992446 996992461
    0xf03021c1b030501050a1403161410260c070f030320030907091503060e0303090f1b0d03090306090b041e020904060b04060e0c070b07030203040f0b04150212 69
    0x403901c0c80c58800741494100140302980760000240c05032104038040d0042d50b661640042c0c5040088a088041001c101c81d010400300b000d40004880103030191103ca4182030311a60036034a208902c0500b070018015501800c010b00804030342d590304546401c5080b0b0bc0c244403900c40001c0b03d0040582034012980780c0740030710301e071103c080e8011210ba41c0c00040d090950800910807601d648a07407041c010131586601105148180d201401002580d029008101d44401c100c0d2451302c80d0000c5601c1e0206004a9a2031100b8560124020301981807030110805091005400c00090507560b0350140d0270880400c0010000900600c20352000c98060b030000e030507901d028500b0304041c2802600390302682880030851401610ba00c59000d8100e5803081010400c1c181c0b54001c540100744a0344800440034240301401042d00c109802424800d0085c02c2640c480d5440010a90030b03031100b581d000f814001034040e410040341d80c034143c003600103115075000800942480380c00001d0b0b8201074058440c06404500380041c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 996994946 1250 996993696 996993731
    0x10e070206010b0f0a03090206040b07140c0103090b0711150a050a0f0c020309063414010b0f01030c030617010e06061005070206211503010c0c050d0f03021c 69
    0x1483d55901c1e2500d8501800c11400c4e190051800520515440d070111000319500c98080d5006000003079011512407031141002030703400520b010a00c1d0346016224140c1c075694468041d40000c0c5410030b1201140d620350880440c1c001d001190b200d00c0b140210691600c0200d28401c040d4092140042d000c01d032030508dd403000c0c00703c440009200403181c1ca0040030210294011041e1203500340129011a1150004d011803014540c5400484500c905104c0c40c0c1130100c02078140c0700750000c0c040d0401c42c40090003800d805088407907000401e540321100241e80c460542c442d42052403a0701940c6130200e8580d41d1035518a0b00000c09030301a05080c0d45403209910a40010064650f2092040340e060000d9032515070081c00a02ca04000139007c2e01d00060031b24168107000c0b0f40000045400c0c0c0c2c5074002c40c40c3c4003401d04c09042c10b03502503a11035400d220070242100d10540c4080082c41d04800604036040322150141c1300c1010500b1004189a000c0c000055a000c455003130f010b090505c2080810b4020034801899070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 996996196 1250 996994946 996994949
    0xb06030604150c0203040510091d040507260111090411030c0313080712030f32060a0f0906060906020d0203090d031b0609060b18130809030303010e07020601 69
    0x10340d20100420001c501c05140c220b0001403841d00010764410b1560049045105035042160040c46c0610714440706940031542d03108031541070007401c190b40c044c9030080313074210020780b07014005610040052054007195103040380500040c2140d0f10004100ca0002400d54a00c45c1c842000c43d0743c04141d900803400d1a0189a0012120031440c03403552a01001a0300503010203850050003c01c1582c0c0c01d1700b04462070045031042c80d080340e88202c840740380c0e050003406020490b07a846107182c146840c0a903400c8100c0c40c04a1780034500748440e44410146280c00e4504c140c01131400e680201461800259503160019100140001500119149040143c00b403d02d14030b40d8801c00c02c642c42240c02c81040c070360110550703800f218111009030f440c0c441030600300c541002400c11103850390101805402000a07550000070a144101820300c200c0001c1e20030400000520000c2e40c0e03481c1e10084c00a209841e0540020403200d1045100174141412040441d144d900f09800c450007a007400c82c18040c0311501082003a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 996997446 1250 996996196 996996199
    0x3050610030203120304080c03030f010f120503030f1f09050402030c180c1e030a200f220801290a1211030109150b01080c0301050a210501020409090b06 67
    0x2050714507408250b4a000c1e0b0780c088003140c00b021010400708901c003000c4030b98403036624049a8407410045002c454032807080c031440c8060704112500150091078074842410050300f2401860455071030540e07030301042400421842c1110b2807070319507400340081d145080001e00641040050507160920505261045c142e0f411841000050610f040c81092881d60652058180051545035038110ba4400c045094070908001e06000110400030618429808184c0c8440040c02402c804019046100101e10941001c2d03041088100000300503a11188900d16030803a9030943d4002140d9920b1180f42180d200f9507282080500f020314852810407000c08690785a00200c4120440314607044140b801c0d029400801041c4410074040d0881710760b02980a130600300c1c0c205079a0140c1191060f2010300031b1640b0081d040c042410000803076055103030601628143d4402401c86440e0381e003007072100c0781003481000402040038800002c2c0000903100380054802003204501c0030424009a2a100400107001040e60b03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 996998696 1250 996997446 996997471
    0x120c0807080717030705060708061e01050f160c140a060201051501030c0e030d02010509010c0804120c050a1b15050c06011e090501030b27030405011404031a01030506 73
    0x28010814040b0b00d8030200d070036101100c0601601240458194082c09074003400300d01030f00042200076908400c1440c896001100e401d40b0b4508000d00c4402030502000718140010414019040000720040060a05a48140c007401541070705960300e45410341d89400400441c00441c4040c242d5040204006016106a00080c4091304e403010021009001c40c180306c604042e20781124881c1c060107080004c1014001a0945406110510000e806000e01750750300070042d880d10340d420800c0c2d44584a482d02445e4085000044458450000c480d90140984c0a540d18007a40f82841c0010b80035142e00c082d040c50441210009a182c603240110303001a01000e4403d0000070400c40050301c00c0414854196000c051a95840301050ba1030304400c00d2107038214a40052070f100c004418003030710700c2c0c2c014030400c0c43e6000c070811a01c0c10b00012840000c40745148100d9442070106025540c000c07004c48141110b01da2920303040c01c3d03682d2156402c5984245081302d03d090000018400d000341440180d0703028000035683c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 996999946 1250 996998696 996998699
    0x40305061609080a08070201120605060c0d09090b0904020904170304150f020405060904050a0f020f0403060b120303160e130e0c01050f0412050a0503040608100f060e010e0f030304120c0807 83
    0xc2c5c002d41d100700c50000341000640f0314450300400c490750040f0017070705006c0c180b81c2d100c508004005956040c2c0c440f414010900c01030340001e4000030360040c004200009080020a0f886681c01d00040030f00c00b80007103401e040c2404001042e001540041c602c504d00075012942544011507003031040300e44040b41c0344103103801003200384280d80b80d640448144002c155000202c3d580d0702d802110040000900388040d4a000107080e80407443c08102600a5a0080c1000c201c0010004104140084900318081c019002800003801d0408840c00c1484c03100740908081012104000000d8800c2d0314001c800b0210603552042c00c02404010000a484605c080c24454541880a6584400d501840c418550614040358144042200601100c60a268848110703a210b903110f04001d04482d008a807081080210700e100021041d20424000045032210b850b0018402c492000444a00c1c103175950158122000301100c442d00d0302c04000420040c0710340c41c40840b80013420314011410b00500d502400c400c0d0b200c41070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 997001196 1250 996999946 996999953
    0x10509040f050a05061f05090105031e07150504080d2a05100501120317040b04021519111b100f0909150614070b07080c040305061609080a 61
    0x415940054001541484807580e91400300d107030409401c0000c02a00840040c0402074a038403c0300c9240034100403005124039103034424024500002d00c919949640640d40445d01c91500f1034002c240800e03011f040e2001c1d070340c44442c1d459003900108500b50001d040050100b129507c14005410452031624120f040202c003940031920660f010b030400020a28640300d80004c1000401921209020f08103003030040d90781d00d010350003d25140e52000c2d4041200d540075440d0109189020921640d03011a03410600d0300c070740c0c09100703407821030441c081000c803420020041d0b1181d941c0e000c401c500140780c0c0d0354642c4e030051300350140c200665010034802d52030000c4150941070359580442208040f1602d401030403080c0488080b02c0307a13007040c1c0c0b1907258a854411100d05044241d44401c003680c0d099110005004a412040e0500e846000c40180442070711101040307285204210b40307508110051070b11418240c490b1030362400d008003540c013203543c500d1000c1c078400303016002022900100100e00c082c240b901c031242c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 997002446 1250 997001196 997001209
    0x1060f020a03030f0b031009020103050907181109042c0a03120b060f04140414010e040b07181d061f051309140708060f030a080d0207061401030311060105 68
    0x1c80060902d41c8608194400003450341c40500d008400808a071808142802100000c1101c5007007079000a08020001d0722000e0000790100c2241c0c40701c0001c050400e00118540d004000c000507240760408204841245950385004005038285e8201070751090b41c40e004050a44244440c10329906c035004003800c0c130086500700d0711800001102c2000460b600c142c000c00101e0601c02c2c0880c100d040301020801150340002e50f46c1502c00c608042c0c804021440301342d91285c4001209120340c11200c0c11410004002840c03426120307402601900702083c00700c04042400d44031100300c0d0480381c00092285014002926500040768009000340c8985400c0c0707188502c51009213562042c44001d200700000c0b1031040700c0101c920b204c004c14a4140400810001d0456040303020780a6560740c5c00a4488004500913241462a0444a0340000e00030400e00c402c036a81c69005c1c0d00141c0d01400e40c19824010b81c80416968010f407040034094010140c0d10f50304524020b000e0708071035250658a0b5105d400180015250032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 997003696 1250 997002446 997002463
    0x5120703120c3902060403080706050f01180c0315080a05010f02070b070809150c271c32060702060f070c051614010201060b0f090108130519020901060f02 68
    0x304050301188006103400409810f110000d4110000190000a00c2640d0010300b42c070310310460003400687c903000301c8881d0a0b1400e00855010760241c400121660340b0b02da001405019142c01e000c0b5080d050b01d1000f10414620790301251994002d150485c040000070b12503100c610b0641c00e421401c1400d1902c4003403d0801c010f001405020b00140813509071a020442086d1100080d50350710158640451401c41d15000b400030440d003104c0441003c080f06034690200c4000c040c0107001701c0b040b20007640319800300170200344050314210340e04039500ca05070300305e20043c5012440410081e2082046030103207510f030205c01071110003190000300910401c4420140c0781c5400190b2032a00c040d071281103080450505845e0020780308901042c031800980c2e48005070383c0c801c0782d40090b002000b0065031108094070034407411440003c495010000c0c03450b5580542d00c400c1c0c00503224212120f08000a0303a60529200d12401260100b5140d50250f004500d0510401409040c01c0d20701030440c27954006000c1d60f1501030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 997004946 1250 997003696 997003757
    0x13060b040302060a09080d030b0f01210506040e010603110f0d05060604050a020c0d0f021c02062409012304060e040b071812171e0705120703120c 64
    0xc0c405544c94811070309000904070084c140d468000c00240042c000f08000d280d1280204190344030b8030030540c06102e84621a032402820891021440d0120074014840107120552082d035840000c910060240701e450003a611070405549a000300400b0405403d11300c540052003819404031000000ea40428100e4004e030701944c010030306460b8250b03254042d0141c0c90342c03412184070304610003580c6a808420403010144075004c0d100c02982e40b1300601c282d1084211090050b910000100340018007010781000065855041200b59044007800100c0003803080e40444041e0b030b005001842416189400350840c2041110200031480c904405698001350080014140b00d60130f40c0010005806000e43c3d888003582ca10a584c0610740303030765202e10305495076071080d92030761700307070b03c26101586088000c0700c0b110300d207079404041304100d81c80c03514126a0224030100ca00c1c0c002c000003501d0345010b40c0040e0000500c2038850f42e03050b5400141032001c40d68002e8081d0300b0001c3c40b00d0b000c2c0c101d1640d03402200e81c041e0b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 997006196 1250 997004946 997004959
    0x1207030b06060409020d05040606083d05010303020615030714012718050a0903140a1206090c030e161e0f060c0519020a05060304061d030913060b040302 67
    0x2101000a0b0301800ba65015140d441d00005100d0592074460b40321501c141d105913410010b1944803d10290b441c410003554507a558002c1c8003103a014480302c103042c148005900200034844117050032000666800380c1c021409603000c04240000307a60041e281080c4200d09800404202e441c200c01600020780172a5800c0c1440075010b280117035120000030209c000c41c000112028165550400d04035080d07a40c801c42d0320003074a000041004006c40d4041c112603140c240c2c1d10079003100300c4055006e440303610880500f0144560305100c0b00d254a441d028140040048460009128a4400c00a429141021130810f502d80002c8134503601d04c0b0401903c2c0040c0d907807070700318861452000c0003d035071902c034035030403120008103160720000b10542d0003082a154240b0650541e290000300d402c1c040882c203110f10f80250b10041a003410f020605101d00a0359000e80240d84c007041010040d42c80130800b1001803008107407600009010015828618552000003548400c01c100b40c600d005100e0b41d550042e400300a10511 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 997007446 1250 997006196 997006201
    0x3090105030a0f18120e040209031b0105120114120a03120b0414100f12030c0f0206090d031701080c030304050d020609060f0403020405060103110a080702070b04030b04050c1207030b 80
    0x180ca41e80700c584450b64400080c0013420700c5003400b0740240100c00881e00041d403c825003840b01c0c203140c0241c2c1c04440026008085000c1307003a800300151188213584a04000d410711500000d106038810b110f009101028480c40c200c40040180000301d00680507000d660f0b403045c05c03420000396001200301c60006124a0000380c1010440014018001710400c2c4207081c190031040c0410b10040d445900205d400315140d2880b40c3e030303075105c000b0030803280340d80042d021800740482070022840c0150003030720385032009211606d0410f1103800500d800d40d0311300c8103400048800c3c0d0004514031001d014030307000d4503c100c01040c40f4580080001e60760b02c02c0b401200d00802803c3c101c501192500c030141c81408030300802558881c11001a241456040791009a2141d0f08110116400f540640b240720f18024103544414a480010078060300c8200d40501316400314410050009125050080a03001542c4240d09000e05800c090600074504480c883e02c880c441c2040d28007885001b403000884e40126580180c02c101607a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 997008696 1250 997007446 997007471
    0xb01050909060121090305040810060303141303080a0e033c10060e19060e0f15060a02010209090114220b0d081b0d0e041505030a03080103050f03090105030a 69
    0x502c1c0e566013590041c18842d41c0d5003019042400740c4180c85d600c000700d03aa090b0a21030715005484d4a88030240111340030f07880360002e480380000101403d104040c090300040350750f640c9610282d44056244c10014800ca91038500516090104502c0032005510b238140d40014054103074085803e843d014540050014020780a6800a000d580140000700d0420031445035124200e84240c6812100007611168402c5d01c07408a920a10890303040d1050505048050399440300c0742421020040c240c9502e01183e00000d14441d500da6000305000f9169500160704c1c0c1c3d06a074140f050055040c0c00c8440510003013442c0c0d10701d0b038a80081109064801d11012241c0c140010a80001450340744091a0040d00c0412105d0520580e0801801d00d812101303160410754044400b419212141030300c00340006000d60b41110100c1c40e181d001001c030300701e4070a10741c0c0100703580d000000c0c50b0206010003103004c03803454801082403000900c10b041e80141080c0156240515486c002071035840300403d13000b011599051143d540 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 997009946 1250 997008696 997008737
    0xb0d0b030a0b040b011805160e01021908040f05030303090a0227070206010518160f02031224100e1c05161502120403330203010503010b010509090601 66
    0x441e41c00160316140c0781440d0504658450090240c40300c0c0342880d82c0242c040130440e10885202d945081d0a4003c0c0b505400c2084807110100f101d62130451107555240c0c0c07a02c0c548103402c02c076800e00ca8004a9507481c90003640303c0d4042e1040e0f04c0684650001d004116042c603010844060741a811120960003502c0200d10041d651801e016503200c01c0c680f50200301c1d071a40c0014425041e80e1088403441002d40400040307403422803003203440e4040b04010602254003203024000050155050b4015241003034801941c50041c41c81c2200c00e000310b490380d208048480c45400c0003000700e80100342e40c0d8410001603980003400c01c2105e51002805607200b655100c0002c12110201d030043c0741d0002c00d54103a5401e40c410689025020300400b0204200c0c0c0603c495140c1c00001d065100004c62502e20341803520755121030100040c5c0000030668041000c1c00c400802d0748c0711075107a07001c09003c20b005849505140074942150140b002681c14040100009481c5035203015403d030b405102481c1c00c2a9000c0540b0f942040d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 997011196 1250 997009946 997009963
    0x902040207231006031109071430010510050304050118060212072a14060106021b060306010801030609030903080c0703020306061c0803091c0e0f04060b0d0b03 70
    0x6000640301003882c07660014000c0224030407107081190700c001c1c00000d0344000c8811a103c0100704c0a10300d40904098100201190b60011090821881200f44044103440d242c2c0444211000700c100c21030b104500144d01d0310000c084104042d40e12405d0f42c109404118502010901c11040c081c000c800034003004025003040c950480880841c0c540c01005e4504540030350091840300100d00c68a1002442c1c0714400c800c0004080d00941070240d071104c107030b22404244004041c003582d0030000b06401c003c426104100050080005500800c0189011031580306c159031040382082c41814104140401a1b9010050f10305683e0080000100d8021034902a01c6107a4190f10007001e02c41d010580c074152030310100f0000e0850f170098040d01c00a40d2010100403aa144500f9000d1011508015050104d004e84002e56846144002120401c040034070300782d094a8a41031700880040d520362560005800e04500d000d98000050b18244041820a409140075008040c40889100e0351074840b030040e59010000e284 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 997012446 1250 997011196 997011203
    0x1203010311060f16080d0f090302190c0906151e02100e150a0b0a080109020603070e011103040e0a180201120203130f080a0305070f05040e07090504020d0b0108060609130902040207 79
    0x41d139166503141101080d0440d1b4012030b80d03c1d1401300c240003030700c4a502568030110761660150a05840c0c074101d240c0d81d00823802040d500000104800304440f1040d10400000d05182c1c0d9664081c42200b1000500340c04203001440641c4943d420050125600000d01c2c0a000310154004100c80c0128100549004040100241e4071074442d000c4c03100d40b2031241d2006031281816a540c502894850303d040b4260369040340300039003143c42040004d13401032099601e094030010514007490b484084072882ea02d1500150000702e03414050071b05021800115205000d02030041451403038080c90180c0004c0c1007101c03142c00c0010b030a9000000079603800c20709044540c201d54020040503800d201410841480d4102c075501030003103850240132402ca64040c2848c0080803a03180c3d00e541c9001c0c100300c040a0225005021101406180c880105044d130b124005080b10380c0140c94000b9101c01e000c4001424502c0140815000700801c10a07460700c0d4540d02c81174440c0c8460103501064040903840410000d1040100c0036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 997013696 1250 997012446 997012477
    0x211106100503070524090f0d061e0e030304120302040f18050702070b0d090c05060f0702030c06030601020d031805011407030f1103070f030f06080f1203010311060f 72
    0x86149100d00c80380c041980e006a0407204002d0701d5034280b2486035080b000324815030359060304203049500410010b101404014200303262003201b03d400305130550910802201c1041e1140840c104005041c030100b0400c2c880594207114112289010f0394581c4406000034010000302c203440880c03180650102c1d0000c1c00307940d00300c400503170784c0c0d0041034110718216142e250020304181c04600700b0340c8002459030503243c0f01d20499141101c0c4002e4000109500401101c0c0701701c00310400102a502c41e03016201c0400000c0d285680c5650303600c100350505d5108480584200000d000340071850341d000502d2150f82d0194100040c000320040c9030048a40d4900500510765130a10f0f200142c2200c5014010b40100402d841c28042d0319010f04804d030a41d8030309011403e0303428003800001c1d030407840b5100300425105241000600700000060f504142c0d84150484161a404407070598080303201081b040c2100030000318400e0075075040d59200b02e121000100e50300c1c420603011420914816182045404003040c00203070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 997014946 1250 997013696 997013701
    0x10507060e2e05010506160c080106140f01080c160f05060103080703090f06231b0303010f0806251206060206070f02010902030a02151605101503211106 67
    0x1582c000e03100105100104000070804142c908080c014181a035100405140c18800842481185850f240c0c405441d841d1403128009025402841100c01900700a42c00003001c22100f81400b442300da014403114108400c5408002da80990380b801e0f0340c2c003411070588484100710982800f01c046103058401400c140240c40002040120b10001084540d21985605007204e5413141894002c00181c425840429811102072500e0180c2c43c6145c400e0300d030709049042c14121001c950301007145141c12800710b84ea0001006004900d180c0c01100000d260441c0142450f291007644800c400004007091041d810450b80c000203403d004070409400e00e41819010004107903101c8009580311025101c0f14082400b010f608070000d03206003c0e1101c0d0940150081c9140c507c10b500f840504e90b2201c40c0c51038100c00911081c84e0008a01c8503c21086004500802644182c001410110740c52800e0920007468421001c00c0002c1c100240080c00e0103031000c1c0c003d150311019409550740404d52688a005005103000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 997016196 1250 997014946 997014973
    0x3b0a110607020d12090f0e100302061e0f090a17060a020a050d0c030f15050a0512190b04060501050f06120703020c010c2f1b180f0405160b0f0337051003020f010507060e 74
    0x54104410215001d03c02c2c1170b65002e108025075021401050d080d003024000a1102c14550003c1c4007081030b91504610303151840e41c407002101e99801a050019841312900304088406006036400642105c81032913401e45004002140f50829108090050f5091184031404001c107228041c40c1400301050302c400010030746007880f204a021501101c0051400001040318204220b08115042d0098000c4d8640343d4250102004650010400f4041680802802c1341040c401e024804c4d4450b0300703844002002d0004020624894a907108903028404042c484400b1007100160403107100c9500b4000c00c0c11400c14402259503040f084010401c000700c10310900c00800000014148624040c409580740101d40d1400c03040d407580c0303e209400140c041440060500ba10303c1004541120b02c002240b00d45118132000800240f611582070180220309105070701031001c5900509500064035044c1030074980c1950700240e4000c8003442071904003c808903c440c01c0100d48d50140d05510403400031103401110044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 997017446 1250 997016196 997016227
    0x405040c08061317130f0803040311191701110313060e010e07061b05120327030a080a3b0a110607020d12090f0e100302061e 55
    0x12600140e0311580300040c081140d441c0c41e480c08983c0c000c00034860b0310508030040c0f25a4000b070445c40040178215a00107401207200c03035100f00401804000e541c480745941040380780c8101e0742c0829402480f0f807018a035807250b00d0f08e032101d0554007508181d0034040d540c40340c00e84c0184050b480d6000002000405d0001c5003554802c1801340340c2c170800f403c1c08085450a822801d031000c01141c803040354008081800540c6c001c03400c012001c1740101086598140d1f0b61501c1346016116004a072020a0010a20140c00c1e10f406104d6090f1202e0744019000940b481903266681c400c1c9004803042010402c003184090b5901d811842078002495040000b41c0b2080c14903c6151030390a5130300c0c00201d2001c03241c016180010410032866500002c80905810b424401c2c400603a02102040742d010f403903000c1c40c400050300c1440c003a00e5002160b940e800128184642c1400320b090940144c0a0603804404025440c0e550020300c0060b01e6060f0361080e1110307500d030203003030314040c01040c1c0310800030002c103c140c5908401d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 997018696 1250 997017446 997017449
    0xc0f0a051905073c11042f0a1e0809010c030b03060c0d020705061014221109061c0615140f13060c0605070503010f03200405040c 57
    0x1c060540a008450155590311490900610002080054500c4100c103154100441080b084020220030b4081301c24031400d04519408440c0c401010100c0d82c8241064424950020340c65003169000924115014030080040a40142c29180c000f40d002c12140c8511100003154160921107900360704c40e090007905802049a0440d4690b20301700300080450300ca03028141071068080c02030141a21020042c00003640280b0070003041c0d0741c08203c1c40001980c03c1000a00c103d170860703012031145042203002e0310030040c00500688650181224110100451200f003180b03480803d00000b1210000c60300082d03140203100c0560b501a0003c0f5044c0f07402189400d0301d1524210580b4104089525541d078035015614030380c04903002035150465842c0308100a03006000302120030f80e84904100422640aa107002d881e040000083c090203c4d2400f0401ca42c0a8290030408030309003e030441d0b06150031080700e00c0c039521000e065050705040b03040c6440750302c191800c1a0880500180403524003403c00e0409402355 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 997019946 1250 997018696 997018717
    0xe0c0309120712021209010c021203300a110405100905150a03180308010b0304080403020a1d090c0108150a080f1c08041a271b01140901080c0f0a05 65
    0x200c0c0d22000d01d0321110f0088641206050b180c0c200407508e282c00303004082d40d0300c4080003500d02c820004240311603600070542580c18044107155a200c5c612400034807464001411441006092a401d2414a1101002e6505882d8142c801040c00700400340300310b80014860380070713607000b80584803107050300100c44004003d02c4056403400c0c0144400b0300d4000303ca01c020403e0140010360030078014400f101c00780e00216049030140c1e603201d04040d100c0d000508078809590008d8112401c003402441d9401090b0a46a0311598200c0035150405110700040c0460703200030700c02d400194803601c0c160100c3e5242d500800c098400c1e101103c00502100714000c1e61800150100c203090782c0c00312410b48515224142c4648100e40c4820740440d4504407021240b94200041c16800d04500b48601402e07506240c2c0018190b049894001880c0094410050000b014000312006041200c01781e40c9008903800c0c6021034002c41000c0ca0151010740c0c0d42280b0141c90b01410450101d400000282c5841c2242c0c49800b4000f0000c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 997021196 1250 997019946 997019953
    0x301200a030c110607142104020a0b030613050603123009030a03050a060b07030801060e18010b0702010302090d031e03020309190510020a110105060a0e0c030912071202 74
    0x2c0410058540007803100c480d41d003941c040800602600e128215844099080d00307051400c0c01b0b0010b44c3c490301000060007400d19403030b0b810b0801003546081c8020600900b100d034045441c40c2010f00101d141c01c5221044d00c1111503c40010641c3d5441c00c12628403184900b19800340c507000300c6039582c188010a942c0b802c55001d955900340f0600040c100604c0d02803a10600203600d0104400c000360007800c0028200034505544003000a5a181c805005040b51482682c4440301981041800ba220744021440300d801020b12a02d1645580800b441943c10758282428490f15580c81e480100c020344104a5101d42003441070200008140d04a40494441e240c00d0040b03d1a1000b4140110100d0000702c0d058a80381d48541140c001c01404c060140d990710380284103445a4800206003501070780d00c4465041300244d0155082d80c0665000e114940e0004012580030300b41501d00034485e0b818050191903020501d5000010071201141000069000c5100042d501c4d201c2449003082c04e0b0025982400307802602 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 997022446 1250 997021196 997021211
    0x1e080d090501021c050601200c06121f080a03120e010e0303071e27170a15020708031b070b0c03060f03062701020c0f010c0f030605010e06090301200a03 67
    0x100b1a02030306101d1302042e901c0042d400382340120210013100d446140308071409410119130242e140c10000b00b50701c48502c6104155070601c0b142107000c2e0761009503900b0cc1040c075030300140a2a0750214001d0307801501842d08084003442040b1181c010041c0d0003085400e5841d24840001e170301c038003001651240b030054517603004a84ca40c402011201d107441080d400018481d5510011910760715006802901c46140407842441e00c50b581c4181034414414480019800300000d14104049000c0c424540c5c10300c00400d6092101551300c400741c40c00013814101c1c1103016803160407d0030400d5803e541e0340c00d40180b40e0541030708003926410300702d07402a24924040d0941d40315208841c10005842c0340035100541c90310f000c42c01c4140845881401c0e0300000c07420f55400304680c0c3c00e6a8800c00c41300c001c418130400005a44140c141000e031800c6003090482003410b013400c008100e181c1c0c121028000449054483e03694401c800400070b401050b80e241c1e420200f00c120185500814901005880c001105480400541 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 997023696 1250 997022446 997022497
    0x305061503060103060c1803050f3901020a050313031e1110020708062706010e010605130308070b040b09010605060d200403120801121e080d09050102 66
    0x600800e64150194071010040000070001d52008200000a181204008140c10041881140280d00a40d100d500007440660710500502442028140754441010301f824101550b00f203080e2110175201313a0300d800ca40b403219140d00902110100795800b80a4079a0381441107182c20750721040c1c3c0010ba410884840c4111721100c0b510110455180d044801c081171410000704201d9501c4001e420f00c011402091000107402004108482c00f0f054070186141c2086060b5200f402420005000000720750700c8030f00108a03507149980b0300e030305403545840d001c1d0303503400f0070030b400424903529501c0100203081c0003403442d050016429200e4066445400c01900544030558650700380ca440b409081c1d072100c81004916107480707465206aa1340000c50303e040702001c1c43c0410f009000d0704594029595106142e207120036442d440000b4074003502c20505209110112901c45000c040012841c00b04882d0803808403206001c4d6160540e502c81c50311440074030445a072841c10070b020390011581c0c150ba40285d807000c2140d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 997024946 1250 997023696 997023721
    0x50d0e060901020c22020f2101210609080c0606040e0c0616050f0a031805040c0c03181e06080c090105030408030408160c081b0a0b0a03020d15030506 66
    0x700e003016401801c500840b4010042c3c490609000100d03a440b00c168450780500490019221030040350000f5911000c03c584110050a621201e1522144142005210040c1e000300041814200340c0b87c0b206c003406c05e034a00f0600405c0681ca020302045c2010031031003014200013644502c59071f81030341d051200c011542c8001d03503640e19190b150355201340140b140b0b0f80325034140b8a41803c2240580110b03444e40000651040c02c2c5001e1000550000710207403035140002180783c0103403004200c00c1d1401c100c4200f0624005100102c0c841d8020104414180c11850102e04100b4001c042c0c201000714003608800c41c440600204a14800d150109070b030320300000c803048c1c24001503500d5545c040c2c540e20700d550380340e81d200142e82e400104100c480b40018051a005010710318840700d141c074410080100c6d87c40c1059003007450179118032070303204032003120f4038850200da10b40c04aa013040701e1002c1c619689a480c0003509401038080c800350151160700c2c0c200490348400280d4500d0382200c0c00b40c0140d40503a01c0b0140030514 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 997026196 1250 997024946 997024957
    0x105090c011407080a0504030b0f15090403200f161a1e0f0702090f040f0b060f120d0f050301030309060c0c0504021210050d150506031603050d0e06 65
    0xa990081190320840d54014514010402c1c000310055203800d50303070b07919000960844400280001d4000c00d01380100500c180c14039411581030400f04d0741d10300d0040d1452800e50000d00005004030202d41c086402c0500503d80400c16160344404d903004203c82030f6003c1e0b900c800544084031188181c184201a480b05008141c003603c0039014084540c1500040d1412641d102102c640840311902c520401e501c401800905031254014072540d81d00c90f164010000d100b40091f0444118005d480e092100048088440f001c0f4140d00044600c015a900130000c0d800c074145104894110b01840e007820008000890020810216038590420490048000716400d000900008000c140030f540244045800b9680506206125034040c0d00c12a442e000032074240d80005201e0103c89030440107202500c014062030901900d41a13032544010001526012100401070100411035903a500c045800f503103041c454244580200c0820381206552407811035522030160440308000345040b00741101da0b10304803080340d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 997027446 1250 997026196 997026211
    0x204050736031b0f0b071704060815030c0d150e010c0906111009030f08010501031104090e0f010c020d03050609010e04030e040b04110711120d0807020f030d0614030105 74
    0x41c1d16815a0b40e094010b0041c0c0032003145410512100049942c0072004141c040c2070340807540360310ba80281c175199038442450010500022420300007400207541c4501c2d4154032110504401c0d0415035040c000c01d0500850000d102d42221644035143c081c0030808000205111a481e420084114000c0d540c600f02d40302618100001035001a040005901c00c600a10b5548a16002d42d202c4422000030403007101c070710389000c401248030386660030380c5c5503040481300e4010b04080c00d0034000e640c0814240c0c02c042c4200e0180500321750ba034104540c1c0455081046510202808008000c0f040b541c060107942c909e08880c07002c00007401c2000040c010308014070701d20704803034075183d04001a0b100c07642c0070359031408407412250700b0a58400761180950b46d0b9014841c091010201d8042d6100136030305125000200b03c10840d030045080c03800e4440300f0000001c0050582d02540b402030510386401a0490078405040448000392001041c10041604140e011000f1661910300522402000d41c06150030b0302c00444566 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 997028696 1250 997027446 997027547
    0x60402070b071107090614041409071e05150c0712380a051006080402060d0c0234080c0d0314160506090607110c0d02040902040507 58
    0x1424003406a01d81c3e4181140788019204c41c5a11900c000003155200d0380108600100d00320040380c142010320600035100364a000c0c8104500e00a03c1d803e40d1644540700702c44414054a203080b0f0011b28082011020700390061080f54403d100310051400d68112100e080b109006a003c000742082070040c802c4201e981c48803c0c019070b8801e00c080303c2c06400854440c1c040d138400d40a000d034400121005214071800c0c000000180368140350200b9468001250040d40600c0b4514040c480075035100301c10340b061400d01071004200728500500480c01c4c4081444405107503001c02c507404c84854540c11007500b840042c070740042d1041d50785107810740d510703100769040a800c02505150720002c40d03ca40d01815807030300f20110b240d01d4950561f00d0000ca10091280503038041e0800000d11031002c200b0710155410000c00e291500384000e014000350b0300c4601c25049248140e080741e10050071511703150807503050705400078001c1085203050400031700100c03c403005111150141200e0682c0905109280404400706500d04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 997029946 1250 997028696 997028701
    0x170d02060f060d08030a0e0d020706050415020f060403020309150304031205075003011401031104090c030b01081009020d09020405010f0303090b0a140d060803031e060402070b 77
    0x70000c00d508040c050941080e00403141c200461503e03c01140202c024040003d0645603031406141400d10910340c0c5003c54204640420085a001f010303202a2144411203c2c07403071a00041c00d03490b003a0201180c1145005d60401c03c0240740d004400350883d602e050381d6448010302d040302102003034401100d0040200300c0c0c03150303131400f5810203a10152380403440d402c1c84050345240151842050344d07010701206450201c0c00c0d2108120b21650141c008000000e1180b12581656507c5001c05000c1401404ca04480c1c0060750402d5a200b0303045900300d140320002c00d42d62551114000b1000d0320403070400201003405c2c007500150340e5100780d598600c564100075810f81c13664204000f003000395100200030401641c590040c000503999501c00c0c18002c095010300c08541c50300c1e601d0041c2c0b036240740d507000e04540d140502000140c90380010920300007211074a032256459412083c00401807065400c410079901c404420032074946087c0b401c02c001c0107001510550300d03503180d10401044c0d00c200789004040d040034001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 997031196 1250 997029946 997029961
    0xc161701270203010b0a1211030303070c0f1118040515101a07060612030210050402060703030902190e0a18050c01141c02030103120806030a08160c0b04170d0206 71
    0x18024541c0748010008950690f269001490b101042d41001c1a283c107088003520410040d400444000e10059000e1401c600c0c00d2030300034018000313080b006404108562150020005007070720a900c0520001d001c80300c0b48201074003075114050300311400c03640c0b48908080540c544050b004254800d105004448107800c4c2410f103082c4110401d401e140c0314000341480b044c40066440d0040c03e001c2c040140c08680a5441414002d1810040300c9864a48070324090500000d80c9070003089490580d05810b010600045601c0410050b1418114950710300000c0600401d0940760308518600070f040ea084244031140c0d560070f1242d49000400401481c50f23000d91003264495010b0201107500104100d030300343c2071407030105007030f02c8414000600c0c002a5600000600400c04040404a2400c45d41d140089240c540b441c00700b60f8900300994041c1280d00f0101d8034914031078403c560031301d0082d070000141340e1540ea41c0281007075030f40042c0148007440317003070b03000d07006500d4000101c3e100342c0400766000340850340304c0d0388 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 997032446 1250 997031196 997031261
    0x50c0a080a050c040f0b150a030c09060c0803041416051905010504031121060a27150b0d030207030212030f040902071e05030912010506010c0b0c0c161701 68
    0x17000500d8080e154212066140e032101500705c0c811200c1d0b4040c41d694007141d0707002811910084440f909001c074501c4140280c6510680023200d413507003d4201d66032a02c81c1c0c1000d20118501203040c8907a4482c1700c50105e40803400659000c2100d8041da200d510401c50703200500c40010840c007030180000d60600042000c42d89c3e29106014070040a4408003c071030001c80000d855409126819000c2d9000e001030003d8001c283c8501c030140189084040088980442004482c40c0e0181c3c02902140c00111a030500b00c400d035124940f84840184a10ba18203000c0c540a510790b4001d00c41607104e0702c261083c540041c48040b04a42400c407040c0d41181c902801c204580009401c1b412040d04c1064003010b001c401c0d81c80d030150b11070106000310f005644171613181c07040114020201c5814800c1c1d90410040c0902ca9811082580006a012181203000e64808038007101c64014104e082c0482d129042500442c0d100d140014002c0d074800190050741102c3d0305022900303075540c002c01e07000303c2041c880070950f8402920 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 997033696 1250 997032446 997032461
    0xf020a0f21080705220e07110d0302040303052217010b0111011109010c050c1302040905060a08120d0e0d080702160f065301030209011a0f07050c0a080a050c04 70
    0x174250195129150048a02c900b04c0459450001c200c0310240d2184601003003103040001c0c4e1551070b095107424110360300103019000e5141c058a880050300395403910460030100100281140754800f100c01b141140034036001c0c0c510880e07010701041941e01d00c1d140198041c0030344d900e05180e4460f6240b411240c080110340c1ca202902d8103844a000c8c04201003840da42d40c0b0310700e000d45c400580e1f001d42c032281071000001c102d490180100744a004d46000801c00480080b81d0101010f03010144035448100c04050700c40036010003003100c0303c00e01405000c0340003240c20181e01342c01800e03c0e50031501c80c45044180414103060354080e540800d4501d030010030845124600d03502c40c0000e40036140c07400c003030500803141161200840080840003800c0c0840103612800040c100350b0242e20317028038419491071700030039101d902c180070300312868040c0c0c0070300c1802c6c9080c2c0c3c044481c8640023010141d615041030420a40f2807102203131a0f4031404000388009404440080c130505944d81040c050906a07807100200002007084 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 997034946 1250 997033696 997033747
    0x10315051e01050423100f0804080c0a061104210f150b040507081506040303080c0309010e030a050a080606120703150503070e181c0f020a0f21080705 66
    0x100008155549040c0301e00c01d84c5070f89005d00545e4907201000f006151240103018000b00250b240c1c842d001c040d800810503800940250300c040c0d80e80f01c000c0d02a8100010301a02800b0340e41416003a101aa9a1600810496807a002d480f040501c400f440c01c007513a5006140500041d21491080020a4010024961030b40c1482000100d03d00044e01041c2a240201d80c03000114000c00c0c00c1144020040900d1003510008507489480e09041d9a806010400003030207261000101100041c0e0250096000d001c6480d40c40c000c484d122114404024502c1d44030940240014012801082d540c0c01d299081d510a414158084012903071816421001001c0501e100c044154400d4000a201d850510040c3d0140c00c16552140c02440d04003102c005565848802c00966401312015581c9400c1040913000d050a0518101c109428441401c9180403510040a00200300c444035840c200500160b43e801108514030ba00c0c5403a4114107030640781003038125100742c0822420407c40d84048104540e40203c41e01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 997036196 1250 997034946 997034957
    0x6030f0605061c14011b1704080f03010e0702101e0b04240302120a020d02010c080706111908010e011205070e0408070c0f05030705060c0f010e0c010315051e01 70
    0x101e501c0307229410f5141c410b44003d180c110410580c02c1c02030155113400f003030392140c04030170100030a8000c03c140302029070590310240c100d000c181004144422241308403a41480d5a0b141d50310381242148110041ea400009849100c1d08540410041d008401c03c4900103603d41c4210f00c0c040300010007174031400003c00d5120759100c0c00b900390410b1040c80d00d174149032000415025641107205119000d40105119134203a48200c4a90780181c0e60700e00d524071125428079006941000614000c1101c1c000c1c4600203112a052401b241a6154040c010305010700d40540c858549201143e000d68180c0d0003030068041643c117040051161040000c1c4d407200151160049800c29961003e004e21391690559089801d8503000540e8414010100e20f0303a4080c0c0103803a580907500d0714100000307a54100e14401d2a004086c0810b100140700390912a00e202d192400d030080c0703c44c00304250700315101d603e0090200c2c0800d10741100e203a5555010220b81040d03540c054075030003440d80516000030900a443e080c0c50304200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 997037446 1250 997036196 997036219
    0xd0b011209050d0e0d0203030f0913020c1507181403150c0901200c090a0b031b150a08042303040605190c0209040f0203120c060f06010306030f060506 66
    0x38a20903550800e000380060084200c074400000e01c0c10800d001403a1040c280c030003000c07000d0baa020007207800310240c068104e41d40b207515501080c805081041960350307003480451003251092012501200400c924002440c42d0f0380e03801d4041d0f5840107126031110603a1209003060020b02c00c46000e03801000ca0042c222640140e00b840d04580b4000100d451210400d4041f036a1043c41d42c005041c1c4000c258182031100b0b00040b40041c140d912140e582c05903104110000124810035181e6111031049030380507003900c44c02207001304034005016080e40b80601405541d0441e083c0710301e42c2400c4c4c2e006000311380c1d2a1700312900c0d1a01d8459040040d1031020400304440e0038507860000003000208020f0100c0e4a41d907880b1600d0608031080240380080c0304051040c1c28000500580ea944e02440c0e001c0d900036610421032603c1d001184c981909200b42c00051003002a074207404900c006506c5100301031801c009601652800011002d27140144402055403610a00e6080010302035044182c3c880c6000d882158581e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 997038696 1250 997037446 997037477
    0x150504020a1502070504050108031c05060d0c060c11010203090307050108090f03042403110d05250c14071a2101030f0204053d05040e03040e07140d0b01 67
    0x54002d1400016904c5290100060300713050141d6401801c151002d5030030702c110005a10f098905a007604810680e95000280d4296201c07039034640c035983c1090001700d26079280d11001c0d080d80000402912003d8640d81d00c140550702c0042102c02461002d0080c2405526210054070a5075024155404034001c07940001001e101c00c0001e80010300d24451090031642860305c9140c1c101d070842101000705418047c021903061018001c43c0d40a411040c000112035423982022140c941d120b419134801d14038040c410100443e4441403898106019110501c1402c10718040140c0d11245032044130381c7c1d04c040380d001442103519403000e02034071303500000001c010050303030b1889070007100098208556242c2103828503003c1d810144910780c2d0142520001299030740600c0c5c1d02c2c460341c07080c44001c52081458001c4000740100c10300f01e124020100640705008045c80075400035180d030003d02074086690030b45c90010391150710800541003040760703c1d80014980a403441c5110041c004544545040c014120b41d0702150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 997039946 1250 997038696 997038719
    0x316050a0203062d010b09280303090612051603051314031e03070c020f01090909300f030207020d12031a100504092d020406080f04150504020a 63
    0x1034000350800540502082c8070360600c00c113400f0a030341680e511060052044955681c2250608002219480100703800c0d00e641c0d08089250900001d021010350a00104150701300800c9026a80303951100d29000d8007c20400048490454650303614800320001b100885019a12950304001c9a041620010240340c8825003c1d070f00070ba001d040254000900c2000078003011a0f00340e805802c0240c0c042c91410400c00003080780213000b0004e40301c1d00c00e001c01e4141c01d83c010340b004e60003003002315410311121902c0d0034401c15004200030380c02032481d45071110804106000c00500854601526102000c0c2000e2130110000e41001c502260410345184103400852240c290881404240d9135001c94901c400701600000c0403441c080840c09a6124214407101e185c025080d1025100c140c0000600e56101202e5014055804040c102004481c2c0000e9500384503250014800e4400c02e8a07600f520361a0113801400c291802c9401501789100800706603242402600015001400106055aa01d40720b1905c14034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 997041196 1250 997039946 997039951
    0xd020d0c06080406050609070e010f0519020601030203100209010206070e03011805010504020406090e10020309191a1e010e071e02070e060a030b16031806020d18050316050a020306 79
    0x204500508000c20030071180100395000391b050702c4401e440d05280b000500454041c200300c0d07042c01407032180d5018a5200b4010303610302c404940002d07a031100d010440a52201e00030301043e4001d0083c480c518030341607400e0007241d60040040e4028903031640c03001011244200352000d2190b15540b0b40c00078003160200706e9201c082442c0103500000d21803e0602c100300c22601d96070f0002a010b410040d10031000000840c40a100079905103000d0707500c0d43d4008007542440c0180d01c0c5a81c0c0605c1c0d8200740380034040d092581340d02c0b072038100c1c0929680da110f46074030195000f08510100302c00500e900050201aa44c2e101650b040046810040b170300d001111b04a04600c02c0c0105c0080059010074010007003225008005034011400b030741c01c68850303411903e43d070340d5405000300a01c542195881c81d1640303da110754402000c903030039401e1030030a1408501e0044081d500c0311030320301c00f0241408440a4a0082d401c1094541507000b00114503200c080f5042c1c468420455409a40d140591402080980c509101700392 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 997042446 1250 997041196 997041209
    0x30c01110a080a063017040614030c041a1314040b040b0f1c080423031603030f090b0d0b04240e13021008060906030a030e0d020d0c 58
    0x703840300c920001c0100000c0008051901d824105003003084080d660100043d40c54907110b185403a8021228841166100c8503000100200e4020f403603440c0c460f02d020003510035100b03555a4800019104000415030703004c00c0c1d6141613424420002008007070309c203542c120b60210034551000d050900708086c83c103180d842c0c1d920007400c21080c00d040d00700c42d1402d84148000100704039002c2109410a01c08212980194620300d8010000d401071444041910f4009051495200205079a01d54844010202c0d850300c01c400c6042140d1000c05c3c01850386404039008892000000941c500c080c41c40e00e04503400ca1404181c02c05008548801040212079a001442d400c0f001402c08070b034a82214050000700d4100c426594102c0224442e01000b00480800e42e4003101c1801700200d0351625000c40700300b000072005000a40c0f1141c541682e08200381c2100c1e20a2041e074048864074515620ac005241d2540c0d2a0000240012003035082c0c10030f940303040841e440b002030028140d0360b000c50781a611484030308110340142c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 997043696 1250 997042446 997042481
    0xf010b100309030804080706110a0e04150803030a200c011508072607210605070203030105220204051c0b1e060409061b0f1101020c06011205030c01 65
    0x2805050414103441103030900c0c80c0800c8415020f0320004c1419001502c0102014000560702040c0107598000c4001d000304441c03611f945541071040980a0304040c0c5070140250306151403a0a4030442d1400c6904690300c3c64091480c40c0d840c8500d80740206034a480f80b0010142d11681654500040350203816000040c01c000901071000031800c80b4548440d034008140c0c0d901440e020700000c541200c81110303000b040507800d1114100e0505031424000c103a0003103514409641107440340850006040e50f40c0c2070041c4002c00c12920340d41c1040362244424060943c0100e1410134440a03071442811160801080250040c105a200c40000e80c140070601180c1a40c3c00d14500c0307110034064080c1d00d80740c0040741c0410b280c40f0803003100402380c01d83c00300034456071203541c0c1c51022500b804000d4003c0500301c40c3e62800100400d0700400701038114031018038040009800310404045600f414030840e140c1400c20b2000b05802d0b8600320051b442c45482600484050006218034900d008090207022101c10241098 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 997044946 1250 997043696 997043711
    0xb03130c0b0405150301120f0f0f060501050f01110c010c050f0d0f020d0f0207030b09010b150a120b130c0207090606030615020114010b0a09080f0a051501030302121b0f01 75
    0x100821314130740c0e011070035001e02c040004120001c100e1070709480707540d0300c103101c8541100b00b42001e20100ba00d0000280039014140201d03810000e081e404141640c0e000c450f0050881c248000440e081c0701d910040c580703283d02144604c4c10946c0103d500200b881e2040c1c040303403805003e600b201030514191550035000700e0910b98283c4011030b0103000c00002041146003840c100e507080d80c0020742d188801c0c84090305000c1c494001c07490f05c58081d00701006000d000340c0940001c0400c1c40940450781c1c003901034000000e41d4044956901480780c0148a2580801080400d0181d203030a0401c0050115541040940c804e000002611000c98060500249a2a100010030a01d000480c69481007110f81070021a4500026a03020344801494141519044480075440d80d03030b6400300395940c60301e07078019840d18418024440b0608000050802c000d80c420001e850300720783c00381010318403e10f080c040240582c000c40c3e01c07030200c0d4040303202402c40b03066071a0381c404520007000542410050000d6000c4004e035140e049 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 997046196 1250 997044946 997044949
    0xc1201020304230309090a270c050a03110f01020a15060501021501060c0b090f030c072102030a170f0a030e060708010f05060c010e03220b0307090b03130c0b0405 71
    0x60100c680401e0070442d142002d0260156101e1042d0041548200c980d0400306142000544c091610300c4903120300e5910b610b01d40310742808c5407400883c1c1103621a141045c0460b41b42020125502141d030b00c4926152190040380411401c041c290366100d04500c2140f01e45408628030038480c8607464410040040d81d141000002030800f58924100b410259400004100003584909110100398001901c04019240c03040f819003811203d13180c0c010144800b10b0350b54041c0c030020600c41c08881da0441000d000d541594041880e0501c890b50207541508140313184004079070306244c40c801464618218074a000e82019100165070000b00248001070358a0204c16034806040000070b4104206080054540d80340c14040c040110860103518010040844d40142508007504050311500700401600d44565802510440030f0507502d0300070303908450603040003840402c1170044901075407107540c1e680001810b217404442076600241040e00c4c1e00d00c0c00f039003900124071842e107181e000e4105051601e507190725290 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 997047446 1250 997046196 997046213
    0x201504090c051c0209030106171501080d05040509090c04050415050609060a14061b030c19050c041a0916030b040203090a1103100212010609080d080402120c1201020304 74
    0x41120188402040f01e196003003042801160380d9090700c20b015a591a028011a024080d107900402c125030000c400350f01a1200812054591030251004010340e82e40c03414081c0d5602c58440c2c01c2c00c0481d90400c405d21941c10b000e1100c036402138441c01201c01240030304000c10216581201c00741c40126141e00110110013840c014280c010351300300c802c020b49060500000f040c40b40700e03200300b104c031041c90030104406480341d00035101c406581d1807141101d14800d00c0303180e0b180c8d8040401c88003640200311500040d034400000c0581003d0b00203004110640060050000800610110541d03078005035144c0145079554507041d0703200781000d05480a00b05c000060280980b4500b83d051032140b401401048484034000800207402c0342c00070004107690119102207030400b6698103140215070b00004503115802500130f2058102d5020b583c500c09110750781c881e00c0e51078a16000ca044005604000454054607040403404e4080c0005c8040d0b4422610881c0000c000d840700d02c101c400e00b65008010172040c0311151 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 997048696 1250 997047446 997047461
    0x30403031505190b0903011d0a05010e07030305070602130b0d0b0f011b0609020d0506130201080a0204060f032d050103110604030f140723030607021920150409 70
    0x6680c03400c0d08090424040f50980e001e40158134190b072010407500b078945d4007500085003440c10044821605100090480d0f1241070518094480d5030070b02103140140280014200f08a03905a500c03079092a0081d901e440207903019500311031106003086000b00b220303012003005040b00e0300321b0440040e2007076801d400e1007094100d020040f17044c0404403851001401c104001d0080d200d034000000140760200703100284c00311004600c05840703803184c10204103846003072890036164036000340c032003880c20740e00c031160382c4203903c524000c00002914802d42103d05da4000d800040015841e48a41d00c0003544e068110320350a9403000e0300081c01340c0c03542b00401c01d02c0510100a10358003019a002031526045441d0f400c0c95102241000749410b01c243d4082038070001c10b10003403014152070640c1414140042406c48201407401d641140702e4040c000110b44254000a19070303110b81daa400401c1c0c4910059101c100c1041076101c080701c05100071100e5071505030f9841f1940316150000954560f185c03400c0180c1c0d001202c180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 997049946 1250 997048696 997048699
    0x90218040c200a0b0903120105100504060f0c080c1e0f0c100c02030109110306100608070c0614010f1a0702220e06042108010b040e09070b030403031505 67
    0x10688200c420540c06001e0640244126440e82980b42c0790540d107a103080c400c040060305680c0071205200f031040001c40108003103080060b55140e6a6200e0b4104a07140c944c8035880c9000ca1400c0000704143c600800c0302c40c5504200f81400049104103440d481740030780c45803100d501c80e6002600c80c13040c41901caa0b0080707100000f40b4010034802e400f001042c2d42d103074a620401c6204a130000d824084482c03140860380511a4068000d03c1285075a01c0d0140b1004007010340e03503100740201d0300010050092080e4500440b04196910005500c80c00c2d0151074001a103101a180c1a849607034640d820700101e00103600030219808280c1415160a61856440814008451401508024100c0541e8030800080c0c041c1c59442c1004580300060b401000091a01003134030320403802481d08102c00c2c0496080d01600a0440039246244440b1000e07003164403050034014075140a9003840180700e501c3d00101740c0c5501020768070449103001d07164400a92180c10448007140001c0d1100c900c03941e440981144000140300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 997051196 1250 997049946 997049951
    0x4050a06090305031b1f053102060d0b03070e22050318040902100e0a0807241803120f110c01030e012012060102120703050901090f09021804 62
    0x15540c80307549902c02c404141708541131590700204e81060a210b031040102800041c0d00b01c2d080b00714915800f03480c0c00c0710b40d040c2c02903403141d01c2100300306542905d445283c0700205d05291880d8590070050540c102c11100d0203880e0380c0c5e003a410b51a407010004075000e0325805813010300c0b40c6001d00622010b48a02044402602070251016000a00020079119000a14800b11501c1041180420000c05e207164000c0c0d07005004103201e40384290401e4111900c480c06407090201c05440d00341d01e47e40c6904a01c19082244040205421070200400c01e10312900f4048c0742c6100340c9000c120344591480031940090701c83c4503116010194107900503014540806e101d040030500d0201c250b40d0f0580700c0b07204005940c18141c9030f800401c41210203510522154883d80640841c1400d08036030030074580c2110461445100e00440425659800064140712801e40c1c00b030003d02d4002c15a8040324140c100b000380c42c2c1030005003c0d000c910b201039260f0140c06841c00b200016150b441c501245100c4034600c040391341c090791 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 997052446 1250 997051196 997051199
    0x71a0405010f6914070807090501120f090605010308040e090c0901031407090204081f050103080313080d05010b0309011b08070c150204030812010605090108011809150204050a0609 79
    0x42d603003e5030449000744034031003d41d4101044410b04811001c500c0e0010200c4c94240e143e5001e480716110a40220079554070300b007140e0340302e0388207541d0080c050042c2d9004c0340c90008642800d61045d080440988001d523008140142965100c100756031080c4c0049404260201d0288900340034003060b141d005110070700411140035101f003c102551018000a03008600188010365490380401c182002000c22010031962140d540303500311b4031001082480c0303031010306110051011103454003e4a050f660004045403850300d464800d08910007070181c1c01c54103c1c4090180b450324041030710940e03009040b4441c14581d6440c0c003800450071942050107500b004c0c00070410201810307510040703c1c2d40c02480b40c14805c0710b40180c1c0c2041c0320303000d004a02519055000103408820800100040d2029030b60454146007036907283c10098075a8003901c0e00050004d012030004001710841c00d0140350504290342800100014a030300d80b40072030121407612608aa400050400682c11f102684800400c00361403c005001d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 997053696 1250 997052446 997052561
    0x101403070507030201090f060522080d0b03100606021f02120f07091a071202120d0c030b040f0912020d02060c03150303070b040302010c0302071a0405010f 68
    0x502014000c00c04114001c60700400b018000d41c090110260049007107207082800d4940382c400f400044920200d880c183c4107001500e21040760100c400c03030750b010040340c1c00c000b4031100c0750000f46098000c0700d9051003100700381d0301d440880384940800f0301120780c0944900c05880540040420210b141941030b10b10402c100d19180103440b01058202000c0101d10080d038072584004c0303c00c52003d4101881000500c400d054a040507003000b007003002d11803000084c002c510243c0981e120100c4084100cd4500c0411142c0d1128166921003c8000d003103040000e02e41c0d58043c00b14044030180c21075410090386c0e0703188075000d114811810b1102c0f00c10602c0248948040707000e00a4036404044c040307079841c0a000c404076185100d82541c0d00d90008025044035211281401c0528003a00309841c2640513528081007100d9080c032078001c40e11625004124103440c008410703038400e601e0754004d0080d02c0c255a00c40c1885803903e014080c00060760704a218032103210030714607050074248907072042c500401e224043d4800e80c0c0303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 997054946 1250 997053696 997053737
    0x3090c0604241223070c0c21081c060f050a140d0f080a1101050408070224041d010503160b03071119030f212c070510 52
    0x485091100c0e07460412a03800d5551600c060f40d611005400c01c0185405483d4010302134590111803090340d00d158030769000584039001d24900140444c051900180080d4a2880401c9801038910441c00031500c520388a040b15904001081050b542e5070350f034036040780c61650241c01c014114118840144038074140000701902c02520403000450b41120320b080032556542000d0703030019005140010400d10364600354401354001e42c16180420451318130130422080502c100d83c0304680c440b005a281c0300e565003c01c5400c0b0300d80c803c080c1c0d0382c00c4035402e030140078400440904024400b244800244122490081d80000f8058100f14082d40c40341445d8107480c010480b4400c00c442c40c40302410b6030f94a6000007212003100b1254260354900c200c07042c0120f0300392420444640e403802580c60421012881d481100c4002d03102900040d030001441c40d10740d0358801c9501007411030540c80d5102203049140d0366080e050000e4007503041c50759006040e0410003400d2840918032800224030784200325814150850a4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 997056196 1250 997054946 997054979
    0x10305100504150503060c090a08030301030201020a03050309031b030406020106081f273e09130507080f010606021204061b020d0b0114031b09090304030c06020303090c0604 76
    0x4a1900c0e4042e4060940d03483c244403015000240654580b480c118905060035404420030300c0c080c40311094002407481c008403d80c0d0590385e05902905641c0700c9601e00322000e8002070600c050074002042242c80e005440b038450100b02800b41d01840d201c1d440c00c54041c0c2168125400080182c00507480020009040749681a0590204e0760005060300844550181054038038025808000d581c590300e004d01490a0110314140903108030030380c22166558a100b082e43c03000c90b0102c5205840507121049240c006603050f0f2210702420b030300242410705d8070f50a140562507881002c50703810136004000150001c3c040c0c1409000725000031b01d60303990191400b89151180744144410030014081d0101400f030b0710300700741e03983c039030000c0564042c03290a0900da00300003000e205400c15014100028034550901050551a140a55560440c0c55450b41d003409201d840060001c0ca4038003040001000103064030110001400176a401562640740031030705c4618000b804503442d0304c1000306020411114500002001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 997057446 1250 997056196 997056199
    0x7050c040c0f17070507140705031e03090d05120409090b06090c0d0c02010209040f0e0d021f1e020c10050609010e1909120e0112020c060c07050c030a120e0103051005 73
    0xc600b81e1351084212418003458000400c0c801040741503483d541000a466070544508a040e00c0d00c1c4843e5500d0094000f41c410f4400149400500c03924a1758500b560000841c41d000364191038034103003401815030240c1e0103500008900c540d901e41c094240520408119031088080e509005035080040c10720005003d03d00c0e107407060b0354560300d0305038580303200b0340595094400190003440040c44240070503000e01881e03585589188290081f0013640b0b840010110b0001c45030520301200ca901000032040981020000c0390105404101500c60044262000b444a041054081c01103c210381120406490010700307502e100340005801441481d113270300700d40c2d60042c207241680c85041031503811031005410b07480800f4140801d9450074080d0903400000c02d240f9000241e0b40c2020721107824071110f04902032007099050310f511401c0068282c0d40750200404030640036200700c5450b44106000280b0704000480c08031516070020350041c0081c1e0304044000340881c02403c050100f49003104001c403000e185841001d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 997058696 1250 997057446 997057487
    0xf0402090615090a0308120915060111011401060c14060c0901030903031509050a0b01050c0d0c26040e010e04020907081009020706021308030c03070f150207050c040c0f 74
    0x114800c1452900f01c40f40041c0140c28211001d42d00e017000e800d00d400c00790b00c0c00780320340358000010804403000c952070321211141442030700e950319003500449401107840145d0b00c5566031500b002545010311a9668020521965039820b032415600d00f4908200048504d0a0350b68800014000c4419403071094500040702842d00007400c03941820100e0181580c0140310b00095460030b030210742d1000e00d401c00340c403c040c13159090100e070350403200440311032103108200705030740e00425450600f0030b0ac2902c4000d00140510358102c2d40a129504013400c041002014007032120002504000803a04204030f46d006001e000c05a00c00d500d45600810406a0001e1a81081051450000707100d80c20708090100544640c0300704545944492030410008d5100b00030940e80c2a084440028014000000310744409010002460411005a0b10b540e500c58003840d0440e0886c60944071b2103038400161001c0e1a4060190f0000e165200d0300700188401c4074020000541040b201003100400301c1c2d004618485c2d4060a01200c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 997059946 1250 997058696 997058719
    0x2506030207020d0b090606091e0a0f24150f230f07050c09010f0315020a0e040f05040b0c1e3f0604021305010507030c1205070b0f04020906 61
    0x50300c1d240f9980c1009088190303620a11044010010f20188a0201600c40790182d0315000d0b4201c5140020b5010700c0c80e01403018001540e0b012490b0015411071b00380c48808a00e10607014401001d0f001000354200c1100821103007000f00c80d1038040000c0009616040500a944030707004001c00c440003140644c0c18500c0d07014450300d03092182000f1030f60714081d4074a0b80743d03c0d03060034607101d0340b100c040d950420b00c602010b500100b008402c0010000403240d001c804160354006c40054507001c3d41091107201b05000700c1c5036840d6000d8482d4007505c607050441a000140310f00d05480c01d89498000030b4400e00c61010184201864000c5e1000344420740000030203c03e490340c24108402a28215000400141c0d406a0100b046038064040c07080140d0700c1d280c0101c6015075280ca00b408200e0007406081880d240c2d520208101c0381d4022001031480c103000745010f11420101e91150102888000305801c0020300000c4e044d002d02200d80d28aa070003883c1c1c05030715a80c41c04e0a0f0001421020060400352242c44076414 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 997061196 1250 997059946 997059949
    0x90509010506070f020301060605070507171510031707031d0f061e0c0601060f03090201020709090201020a12051804021c1d011505040f18080a020f01051305250603020702 75
    0x2c1c4c1d080e82d964024002c1c080d0301c0d15601d009000c0d4101d01c0c003c58140c4a00500030690a203240c600444261882d0020218000800e003a500030900c0a41900b08070ba005c50800320102d40c1505010710120100001980d031080d2900c1c00030103000c0d001241419040038110f41c010687c0c0e60f85e01c110038481c03046600e9500d03007040d940508208103140105180300c400009039101c0d07030140440c05904a850948801c02c1c40c0246030303425000e480a0040090042e00020418040e010700d507407041400600620440d0140349265460714079200b0071843c01008140007085010560031106c2c21900b81e0141501c0540c1040c060400d0b0a003d18814405040b0258407201404002074016145c1c4641580301c50003480440f03d908c0c4400882d680c64090580a142072107080c829400c040c2c003030113100404964810740e00c42c44548400c085a00402d100c43c003180548400c68a00550900405000b2810079605450001207413800510700011025502c0c3c118800961100c90208008610380881c0e04500b40035a0340c0e4450710 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 997062446 1250 997061196 997061213
    0xa09050703230a0c03140304120204110f0d06090e070803180316060306080c0f10080702010b060d0e0d090303080c0309161e0806063712050d09050901050607 69
    0x82c00d42c41548075860114042c4402c4c250300c081164052004c0c5440c0009032000c007038881c451400b504804101c2c600c000401401c0c2944450880c0d07140d000840d042c0100400d8040c0700350708c060101036885031910424000c6e040940f281d1405802040d00901a040c1b4000c00b007502c0340100300102d69581d200d1104400152014000e80c0c0d19101c1d8810210311590b01c400000c1d000301614014601a4862a054000e02c0d0914800c0b00c1e803408030090903414802c41c441c2c000c543c4203800400c2d41c0215520380e4842c1e16071380c075810089e2070300003070748000030840b080c2641c40140303000a09031580d0200b2241c1c002c2000425000143d0941141500791300c80e659940b401107aa15090075010407440303070240c00742e001801100072101070104400480c0300d1440940d80d5543d40781c0c0c03404151501c40e40940b140102990004402d0001d60600300b031084400c0c1d000b2555215020651040d80c0092084202505441f0030840300f880007180c0007201d030130191500c41c105030110350703201300502881d4051240090040140003840 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 997063696 1250 997062446 997062503
    0x902030c0306071d010201050714091519030f092f0d151a220b0406031109160807050d0f06080c010912022416050c090a09050703 57
    0x81c0894540703041455004181c00440740e07070880b4080300003008011039841801514051400ca507a03201452111680e040c01d02c1d4400c25400c1ea01c1088400e061403406000c001400020030b2010780540329843e2030201a0a0320250030030513000a07e404910310008100d1448104a2a11102d42c8030b400101064a00e503a140e01c0e2819581c131010303080d610b00800c0300f81410350650300341d0703950240080d40b00c0e1104c00c1082c480240107a42d03c821400609101d1000100400300350740c50908021840300842d00c0860103c0e41e03c3c0c0c005a0310b41c1c2a41c659030b0030741e042040c0d4554000d0381846010046c400c40180083c0040d8000e4140c00c200100002d500880c0d40b800d81000010144218042019654628840d5500c0c03241c80c41d03a0740401d21f80c081c0060840d903180810011103801400c02c054040301010718a414a8000a842040f00700c18000e600a0300034840c56090420300c20b47c010a8000811020400711040041c180c00d14941891403090000e100885e4003001c886d030050a46061400c08800c11801e26490f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 997064946 1250 997063696 997063699
    0x41a130b0405030a030c0e01020a08030a06030f080c07060914040f020d1a030d0f0509040c0201061e0513060302010e0d060b031219081614070206030408210114040902030c 75
    0x920a0109000003c0000c000d04103154504110030b01c4646404d660742d000c10b8038150301680002c02084e0104035414011030340411102000200c4680325aa001c0794992920400e0310f00d80008103038640d82e14030030440340010b00194100310b81d2217403620b641001076050f4003655500898690141c042076400130380660300c02c0c0b80d401c1c40c180f00c804441d45810781b64540440e03510740b080c0700d0a5652224603000f40c00c820424a026038a0a00e07064141040c0b0000c0c2025403001070456503110b00001d03c204417100d82500040d0041041340989190a04201000107a214118000d900d0701e0000c2005030380165610035884c0b03066840002d0180d0301d041400c01011054a04e580500403080109624034403a070040060080446640456520000341150050402c03241c0422040090310008050317400b490f00300d0a000d8000174203c2c5441001d60200c1c01c00d03082554103c8680402080f019132101421104401285900d10f100340315605d81605849501034414009018981c1c0342d8440c015500c0600028004100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 997066196 1250 997064946 997064963
    0x40333020a140f030402090c030c0403030e03030d1514010e0607200a08010c030e0a0f0b1902120108100515011103070605090c100810090e0f0703030224041a13 70
    0x3c001007041e20035801210128481c2c100c0400165800040780d080c0d81c092510804010b09050a60742c082e604250f114010a5252100b4440d24200e8861402015018020301028504081c034004240c01c1c44016051000e05000c6128034184841d00d4400a60350944d4200c18400d112001d0016a01400c600a881c03560b042864420003107010881508905400e5000b643c0c100044844110100e450f0084440010072081d180c030201c001040001c803240b80c00880c0a0b541c000310099012005040303034081513100a100d0702c41c20041000301c90078400c181c011107190030700340200d150035441500318500c2e014880741400700d00c2c010801401c40c10800c0d1402aa480750040005060107801d80d40d40d0083c00d00064803d003407030040041c2061041030403178052207800030025156410007000304040c02c0c00ca0001141d030712070807494030005142081402c0046000e60058403050b0b2410030501c10780510030820007000510301090200180ca0101700ca0f0313010900c50303040760190701d9600a80d800c0c01070300c003c05004100b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 997067446 1250 997066196 997066207
    0x303072f01020307090915030f050f03130f05030d140d02070b0103050604061b080613091208100801111e13060e030106051c1202011803020102040333020a14 69
    0x1401503000b540141403d845c0c0b00344250340c4814100c00c0d01d44559403601c82d4000030404000040102455010b00c1c4c0c410001c0c0c6010754001c14609240d42c2124545030480e891606082005005c80740b80407011700700a40103030007203a55840300608034510590880c0b038960400244650110b01640c1514102c40c1d00034003401c4107507501d0511503a035001c00c0d00c069594903d84440ba42d030040c08203c21003580c1a6907240c0c0c403501c1c4e49050820003261208482400c540307860700e02000000303450011503c0000b095440d00c61070b44c01c0040c00c10b1030310143d54000d034849a00d81011600041d01103415541d42118407812411550300c00355000e42640600f49000506040708500407030050342050000800b030070142d0003042200c4c0d85004200051990b0b8403080c8026510b032160801040540c0c0c0035580188403400081407016450380d1414940e0494201580186d5020400344104022000c081c912061a031003229403440c1c1c0d4000c2072044120240c202e2207042c3e80010071b07031a00c40c09140c1c0c91203003e2125120a40b0340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 997068696 1250 997067446 997067537
    0xf020f03011505030613020a0605030a060f06020d03050c040503070e04080408030a0f1106040b010909111005090a050a030320070902030a090614040c12030e060d09031d03030307 78
    0xb004603000e150711a014800002d09181540e5041c60a150b0300242280074183c5081025038817170740050164501e5584489012402d0665841e0442c020146640180034231404500014100d64000d08052b062784000c00c4104074039030f4005007241c00d44440da40702031540e85651a100501c1d20170340d0310452075030001158010641d90400e45000c0502100d446407081803480407113480d03c0c0c1100b150010aa40d0781c00d00140102c103266406109181d01c02c1c40540e95440340c1400044100f0030f810b101800265000881e0103650403c0c0729803900a05060b202d010125045950207401d08810309081350510541e1214040400c3d0100541b0005002c00501191703a420a040e5000103072510203425181507003041c445003940c042d00320400d0310554010407079222850821001a4020040c2c400a40c10443c01c444c0d5450345607509001030804800581d00051607a00314a005043d107a412129078106401646031044140c80101c2101d070300c02d0591400c80c801c03040451070021540030305660025151003540c00c10410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 997069946 1250 997068696 997068731
    0x100312030e0307330603150c050d0e06060f0612130503041208091807090b0c0a08130504050c0a020a1112030a09032d201c17090d0f020f0301 62
    0x20429030f540600052640c200c444c4007900e25601c4004c0507100840e01d50240d2401c142d10001480c42d4a142040c50100014960019a800c00c1c5d0b0b00807541e00900b01b030101a01e400c205500d01d1a4040c1d070b500d81170561b001000c1c00715040050444145c1585110341008110040c0112b80c0684419906803120045a04007014a0307045002d019000751004950400e03050020995070f40700306038507030b00c0100c1a4217004076041582c0042c80b400b506441000010b00c00140b00101600f000c181004007400094a13160130801034640c00b50081e010810101b2610084030b0b4007003907001002c0e030060319800c6000b0380100071554105440e021947c980c000882c1d0301050503031082001d0112806015882115420101030320540da0810740304295000d05400d02c100087c5032000b001c452512078011100c5540980c0012541c1211076001542c0e2a0007000d60010030003260016090400901110041c20301201c0d5000c03c01603154903030054040854407019100310341e1042d40d28904594060000c0c00820a070000d074400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 997071196 1250 997069946 997070003
    0xf07170c06071d0d03030e0d0503060f0103060b0406030504050a0f0311060604060609030b0c19090810020a053c0a170c04150509030703030504030b100312030e0307 72
    0xa1a008140100b980707584543c41e44010203548020784203448140d401040907012200702c0032001d01d40c861440210580040c0560f0010040c02d4440c20340c1c1e803600c041001011400341607418141483c20406009807070308c0c081500d083e03030100c4c10700045d40d403910304010340380c55881c19000301005c094218007000c141d40700c8911f040e030543c035034120b601c2d94880108100030794520340100c00005048600030000700d0070310782005802c42d0710244454079080c151180b07901c10400020318000480e03800d00c0c041000104c00c102162904414034421804c1480450000701380d84504181445070030510b065020542f112040d6150f034417a02465030b00f00001f08408425410b40100c00e0120208014040c021b100031085000c4511551a41200514080c00c2801d400c010411a0402d4010031000340241c03d203649041100c03901440c02511070586403407441ca0245000200140543d01c102813011040002449000d600300b90307603203c0e013404a9440d43c9040464618000c060b806492185248002094554407100e202d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 997072446 1250 997071196 997071217
    0x307050405130e03090409230706020d0216060e19180b040e0a0b04140601030b0a06050d030f050c010b0d0c060e010807020c0108060d0b04060b011e0203030402060f0717 74
    0x5295030a8890b01d0440d0004030381c03105250020051910f03c3e181540c455001c280c80b400310300029034a1814010855194041015a42d032701501d400e001e200d404000032240140d681c4010203028051649204802c085881a0003e10074059010125640d07145650b001e0b003d01601240412550fa0080c01ca25070652600343c0640c503d407441800050401b4050309a82c208148000e180000a50b43d81d001146402407043da5501140082480702407000d0092030b00131402801c11185908ac1407070540102d9520740c0c080c0d445000061003090003e500061505101d111a041c815140c540201505002d00f8a1480c02c0381e0007010406a0010003210181180a813101a9520100d044001006480000c8242d03880b01c05644084980c120940c403a01c14180d001c5d4020b050222181b140b9070398044400d0040d40e04a4285480300c6402c1c10321351340901d81120392a201c040c2c903100061040e201945a02c00a48064010a0000385c800c2002d40204119844190302544c2443c4006a80d0105500e40d00035940b442c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 997073696 1250 997072446 997072459
    0x6012a0b04084806150301020913020c01060e060f011d0301060602070306230f0403050909091e160e060d080c0f07050f0a060818010c0c05070e010b03010b0c0f030307050405 76
    0x1111002075000e09003ca19040c400800c1c0607241c81038607442e10003428811692540d001c000c0b0468540f10380f00100388001c3c4040000d619440200825402c1d1082a00024045049001080000e070740300c00f68100d040c4000c0c2005143ca0303070100c86100380710b49020f5030681c1641c00e0900014680b54001404011603008001c04c02c50617100c4030b4510395092046a60300151810711006c24005500407420a41052207420a01e00e01412840482c00c28030084904c6a9150400d800da01d00010142025506002c640000307007010b00c4040f850f0400720305c507070f0081910041c010000950079031140e505804070740740c2103481c5a0700c5140b880c800c00d955941120032004240552500007600e41050310082c1a490001001c03480c04c642032040c02c58102c00000c00441490b0074000c1d40f000e1303014081c824034490303020a075210b1041c0b0f441401c0c154600b03142c42e4425006521b00700010426088480c0907a4150f540c1c2c280000c2c1d0340c0d84202a110b180c65100c1a0142050100000340640b00c4d801c48010b00848409076184c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 997074946 1250 997073696 997073797
    0xf060c0a1115040201050a03020d05010b180f1309020f150c0f01020301081005070315150908030f031303180602060601030b0d05120d020c030d0506012a0b0408 70
    0x1d9031120240d0b010b03030780c03504a46404100190b008101810741d00315245001400c00590366160070a80720280e100b40c020403030004101540e1013060140c0c0b0f80c086c6050390004c0c814030140011a8800321800ea19204ae162307126542411940c440ba16440c8100c5c004201d0203c05148200800e4140c3c0b11844035910341c490000c0e240c20441d410700949040b60020005480b441c13420849500c09003100800280030190345c3c5400300103214840e01400e0140c84074407201c6000210070380d009800401181c101601c150720505c2700160250340c500403684e008181d40300310b54504900d440d09071213008c5903080c5801170619400020800075400101607104030310076a0203000300c0030140144075a142c1c0b0382d0b04c0a0581e80000d80b441480b80c802c00002e04501042000051401c000303012400c0c15600243c0c0061011500c1d4800d0003410369014100380034000c4141e00b00d021192a44050b544181e50b040c0c0010000d004100c0001c0a00c1030f40e03429140c43e400d102c2c841001c40c074920110141424118906003500100c002507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 997076196 1250 997074946 997074977
    0xd110309061f05061c1d10110403061109090a0209011d21190303090c050418110d0210030b0333130816110d030807030209030f060c0a 59
    0x50b542400305204020594070b09020900810340c4c4803d280b01c3c9582d00d607128401688100380b00303d02ca01000382c101034216041c601e110300d04000055854482d82400d1841010003001c0d260220b40440744d0001001900519602a8122074029070030603941c0042480108618080c154006000ca00b07000d983d4a011040400c5c484802250ba904000c1c0d0030174042e80803022000b0507092502c03030780c2066100b144c0e4080c3c00000681d024a000300c82c11800030380c13114000c00800140c0c58201c0041e010840d018402e9040099103944050400030020345803000196808030540c0703c040b0f0108880f9000340007140c05075450780002c0d01505060441a01a104d2520390603009050003050500c0560030400d1178010324841c8440040c0294040c0c5078000720000c210720b05000880b07030070040510554070f68441070503800c9410311540c2202c083c00f01c28041c0010f00d03405800a540680d40951017000c038203005884200c0c003000f003441d21003003440b148064442d03003041c4410310500d00003400d508811a034035040482e40d03084 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 997077446 1250 997076196 997076221
    0x70809120a051b010e060118050c041401050d0b04111233060f0a0206101502030304081b0115150306030f02012318010e042d020d11030906 61
    0x220300000031000d00468680018030483c2c1d07450602c4410001c2900170300442054181700080c5d1050055200c03034140020f80780c1c4240102544020000c64060406203440016030060a10510341810404001800e002d040590750014440c6040500100306096100e00848040c0d40140d5a20f140000e140001a42400484281c4da40303001d1042000c3c07a80012128907415040d8a00e401d49510174002d010380e040642845000c0c0003020420390003041c803400d1002c800d000c5014183c110b0509548028416480349400004a0341c100ba4088822651600116441c100d000003107002e01419500b0080d04c0f00741441f1800c40c0d0416074450340d0b61b2404640c070441080d42200d075903100042078900d990303081714055070240b068100c00c003544032a01c3c08001480c0e0001c10103548141000c0d00351503a41e02450001d941e02c200c0b100c481035000e4a04110030401e0f03008283d850303180fa40309440000720072521072006100e1034040e15081a0205c0c420b1125100d031051040c550741040b00e1580083c82030000051040d81d410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 997078696 1250 997077446 997077457
    0x5010e100c021903151b1103030103150905030d1a041a13020f1611091905090705061305090906010b071e0f03020f0601060206151909020307080912 65
    0x80c0c681c9140c0640e140e00340081500704800c8041081c112180000114441240520550a01e294001040790344d001c90703000070030a14100182008a600421881800004101d03070640e81c10a00c000303082e42d10701500801801a10000500d140804503d048882d0402d4101860b9201000c90000420b00f012040c44119400e413040c91105103110703000c921503400e204a034540c1120580b0000341c0340c0801d14241c01c039141d014141c0303004011100a00350061100e024868200e0b050103c84030350baa8141465400100900e80e540c0300ca16607a50b00110f105402c1c10081c050007000c0c0904505d40f68010525407000700092842294051040764000482800001c21001d060b51101c07420f05051561540303a070080281160700784c550300c50203035040101089560b020f003100140300768010100048040f105034100345041c1e205005545c401000e01501001b8144039002e860b00c103039440c5801c0d202c014045035219019912000f0914800810321050750750000c10303030b4801c01000741111809001c01039461028480c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 997079946 1250 997078696 997078729
    0x309170a05180316080a03022a100905040507030608070b07020a1509030b0109320117010f0e0105180c061c0902040e0d020106080106050a0905040516030c05010e 71
    0x41280c0d00320403010b940c42c452010300160458140a8812041303610101150300b0807440c0d079005030840c1d401c02d40d040140c4086140d044100c03010b4103400c0074500522010b818006440f400741312480c001c0c62445a602170004045c000e10921243c109501c029000700030034010070850707024841d07001c00c00d800e0000c1120007035607000d42804006403425155a00d5100400340c035104101d106d050000200b80c4900340381740a442c2c00040040e2904450074196900703807007884140000300c542482502c81203001154141110380400408a000000300c2c0301500600700c00d441c5103d00c07840d120b1000b1440c0d030305500082c800c40c102d078164210104030700300c0559106030741c106150380a5003c03c1003440300c0b00014280300d071202c014503020400402e50360019041d1450041c03800c1450303200c9001c0c0109268240900001414404020091a405d04000c2412150300e4001d1401140c0c4800114041140c204010800f42811512042085031a49403a14a440082c0b203810f0024060700800c840b58600340c1840100c0703110 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 997081196 1250 997079946 997079957
    0x10c050307080c0f01060e070f080412030b040b0301050a0b1513060e0d052e2307111c080c0a120c020316031710080a080c1c0309170a 59
    0x1641c2d54018960b406008266558041d81c43c4120101109000e10000f4054003c08080303e450060001448c00b05900040e01c104a80700c005d01c404194a43c0c206074424100707160104440300710001050291207404400342c0c140d860b09042248604107030b4800b0314400001ca0301d0f100015500c243c0d61401b401500c1c1d56410610040004000480c001d08818182000c0644801243c1d14991241424100d10032044110303a003503d000e8445508620500028240b5400d900f00f001c924402c030204400d08581c40310094440c5180b0100307000d28051208103180460b180126801481c5140172400c1110034480281c0100d1005000b20300c00074400b100b81c0f511450907030b50303c3c03000c0000c0041541c05804600e1020043d400104107107041c0f10342d221241701c106030083d01c1d03103c2141000c12091307000c400001c0001154583c0d0320414131801c040030032008103071a08515103e4035400c1c00c002041c182140811002c05005500b8140c0b910580c247d040000c0e0240500d283e030b4280c3c0c00c0000402814425480d44d00d00040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 997082446 1250 997081196 997081207
    0x3010506030717100203010b1e0a0c0b1806041a0702011812031e0204061206060e012a0b070f0903111003060e0109090c0b1e090102011424010c0503 65
    0x11528000c1c02035034a2507001312040b80000344a000b003240d000307070442000c1010004050240c40c0c001d0201c6000901c03131458036442c043d43e12100030f080c03d0580d280100f0b101301070300c04680c0701180e060090401600900645880342440d26180c4072014201c0082405005120001190740d8010311600e41c4d220007800ca0418454407541c3c80d207900d03c2064038800140f5613109101008410b0200914403452010600181d55900b40f92019000340f4281d0b03805800181403c07014024a507000030054000c020070f00307000c8410840a1110210100c0d20414070212040c05c0c50a907051040500c8400e0192b002d0351036031030121000882c00c80300f5400c80e000c0641000c119a950f00c1403801c0c501002c000010700c514000644944030046035508540a9101600709900c3c1c1c9030a01c14000c2c240b400304014401d0f501468136202e4051040c0c90300416900c1c2c424008440814240d4840e4000e401000061409200020441c40d00103441c401e02d0a10301010095140c6481102c1210b50041c80c02010300b035007220046041c107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 997083696 1250 997082446 997082459
    0xd0806090f10060309021801151b050c01050f0403120e01080a090c0e070e1c02040501060f0206010918051e070803070f081b0d020303091006061d0f150c010605030105060307 76
    0x170000410200e800114403003402401401c20665070b8060400e00091007080784415000410020f034108014640014503c2101e000400005420b5002c980c01c2c04c005031220382810400d00903002c0e07130b400900b1480c03e40c1200e00e0141c0e44250f240d010a42d09884402907071b15401d41303840440d10181c90041c80c44030b60b0b09090103010000714205d42d1000f1103250020a400c6204c020034400316422135850500c2c105040d04000f1450a4015103014058500d01241841c0501e0302c000d550303070018821054100da0390a2034000c00411186c0154030a0b0f0040221264100328080c1b541000e0700250310380a0b80d002c0c3e40404070b000c0101204443c43c154001022080445880d25400ca4550100b000c400b0100d0301485100507900341403100b15070100c400d801a603100c6c40c060340308c507040210a01c079044000b841c0c00c1007441480d1b04220224010704420104040c0c90941c80e0201d8110040c4e00c6a0603400051303000b24450001030440141002c518080c001c4c0070a0b44c0d0390303040c5420b03118152240360f4550400101030061 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 997084946 1250 997083696 997083701
    0x181b01051608090d030e1531090c0c020a0e091203060406090501030b07030c09031703070210020d0f0e06130b1320040c180618080d0806090f100603 65
    0x140e0b000d45071840ca012039580020344207101c1d9407000c402281142c8105003451800c695032500c0c1d13000000e400c51800d0460611032184200b40c0c889054500031740480c180444604986a501410988404104520401002800b1180c20900c100d2041102070800300e0880e861101041c05004010000d19100700c200f01101d1442e04000c05140e005681d566000501c0e01701802054002e41c00b403003852000d03040c2800c00506131481c15403030005000001e0342c100f000490010700310584005145000780c481d00c902100701d04000c00000c01c011260700110301c51004050a501ca021302c05d22a080822180e03044601c00da843d248120b50781904421050340c8070010403050801d0a03440414170303600588503080d980d6514001c490182210000c1d4518880c2810103003054490035075a02450f090045041c000c040804940c80554080e031802c20040802104245940501c50000740440c02c3c2036644148101000410408040323521a1240511030080340040f61040303e40b90050322144080d050083c10a8000e501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 997086196 1250 997084946 997084987
    0x1090f050d080705060a021b010e070b0c0102120f0115030b09070c241a03010203040f03050a020c15070605010f06020705010327060b01140f07021504080303181b0105 73
    0x103400b0800c000400004800b40a22481015405801038480340c240203110320301c139201051240701da071500e4420320f0f042038001131900c22150641c076400c1d0748450801e0138034064001d80f0080c0c03410000c03001c244021040c041e04468180c0b81000015000340d00c00c03000807019260043d0450340c0000541e004036800c0b600c5582520b0023940540074140c40a280402c20848001000c4113402c1c1141d41c1d08810400d02c00c80e88004125107804030001d40c10340c186500c070078000c00c803022001418001c1c001210b80806000384511a2500c000910340104101101642d070507aa000c068100d954034036003000482c03100381d0000040140d41040e401807400a052000550007816000019036803003050441194812040035001802036115801c08a82500c4950000d04901e00207c0036066403102032140354400d1340f004e81038400c4d180e0105d6551051000c825540d02583c46190440c1465010000800103032004526640801c1107552040b0342c40600341e03020720111001d21746181d50008004015242c1c1650803c00c0050307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 997087446 1250 997086196 997086203
    0x703030e16080f03132d081c030c02062e080a0b070c081c0f1d06071407020409080904050405061e0106080a021806040603061e03120f030e0303070e090601090f050d 72
    0x3943c001d500f00e000160142c003a480f58000d42d0165030300c2c180c0d231058084003044052590505001604030410042d403a05001800350714682d0001511030500081000070511070880d40e0301441d500c1d07884141941d21402025415510011800042401948600c51084205410480c914208000909102207000d52000740c0c0c80705680f2598078208485a51103080d503813070610820b550305c4204a8000d6401c1c04c400410003010701840c1f032050303850b4055031b1041300e008503412078001601181c2841e1034030841c0101c0c110250401d00d4442000200440000c444c0d002e400020500701f0761108951044621b14001d000b030341c001401c4c4001096880c40070350094940c0384500000000d00e06100c801142c181d4100380d11480011384c0780e00c410445660f00038084004400303041c640815080c10340d100d04e442c5000e518190010040300d50742c0c7c9401ca5209a00c500b81210810f020749a41c0c3c1401c10f00103140d180740c8032205e8441d00e4144082079966000341c100d80100c0b64903110000744a0319001c20802030042d100e800b034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 997088696 1250 997087446 997087499
    0xb03150d0c0323010f0c02060121050604110a140d2d08040f0e01140f0105120f07030e0f070e060607050106031a06030318060703030e16080f0313 64
    0x80009084074600340e0350452070544004070346061415860079101d4003031781e8126451070911156000c42d40417a41d541990071a22020444100860307811003001a490005003150042c80b007803104010703100d0603440110364112070541c0140e0305c603901c100d15010221100e43e801040b045030389002580c1c0155820103489d4180b8140c42a001070b1341d03d441c0301c43c0e07054011900d8000006081c03050780d0b51700007800050007070042c41d541c1541c1000d9030549110403164031140300703000c03002104941740e100d84104c500039100001e410445046c0114000100740e8140c0c1c803080400c0c2003c14004200400158903402c401c8200c0040c408203240284003040003002404560b00901c1c100800804550240510f000443c810a100c01460244a51210303030040f01a10480c4a6003041060241c8640c00b6601c180c003a0000b203403180da850000349400e50040c0035001140466000b80d14882c1405980c0455140c111388241e42502e04140d01c80100c15120300c540200c040051126240a0001c505c1c3c0a40640c0c4c00700e244840c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 997089946 1250 997088696 997088699
    0xb04140a03050102031806090c0919021b0a020a0b39011d07060203090d15091e060f0552110331180f060b03150d0c 51
    0xa82e82079a00446140541d502680d24101c2d42c03100400c0510b901030074031000760440003400b100164400e4005020b581c01d28294030030001c404511541294024480340030ac2802183c0c810717171526124882441c060f449503868090015404408004513202804040a2100c184540d07007800481d05518211015286da495403221315601000d2180344041030703019900010780180b100d0301d0b600d000740b150001d03030864106000c03aa00c513840b000005000158030410010200710100006002032602200141030280e00c52a03091100910000c0701c5402c5002d4201800701c41600c00c0342000740c0340b0a80d520061504000e00745900c050560f0a8103403c540d60b00034109403184e0090060410040c080300c8010180f14a4090305001d54000b52080118010900510f0801a008401020000d0f150b106030340518107424802c0303071421104070614054200702c459070440c01d5003256800d0090040032542c0448500e0500080b50020b121800c5d28032620881508201c50030f4038a061001d0703803190b03500031500221341c40380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 997091196 1250 997089946 997089953
    0xb07080d2904050a0c050f0c0a05060c03071701030213090807080408070f090b03060601032307110d0e1c020d120201090204050703050610050c150a020910090b04140a03 74
    0x50803505114040e0714807403901c48800c1004881e0050000181c1914050408102d6a04801036440c0741c02c5482e0629156405900b015050141d804401012400346030b08003e24010380d00c0186000e84095540d0002907502cac40070940710300c00c5c02e0001039409260500178080c1d03260a80c0000341850b110354070329810500955942a0103410a800c00100794111180034408003020040400c02807400704002c1c0007440e649004070361220009010a8109921008040c401080020745500e0514202c031a400302d41c89c10100007040c0246040300c000c074500686800d4002c1d1445640b10314021b0740c0c0100800c0c004d00d40c2407c1900e4030f00c1c1c8284c040340c108c0c030f580c984000800d0045242d003860941c0741c3c00103e41c0142510402c021030b44001c0a41e8107042c5000140030060303c0700031f1540c0e5520b940d401e10076a50741060704040d18000b8000300141188000f0402c10511807d01c0c0c000c0e109440068034a4101a409110195220440781c0121451b040d03003031100f0000f03802c0c401403020451402400d4994001e40340d84 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 997092446 1250 997091196 997091231
    0x9021327140c011404030f03110d020c03070b0a02070b0d06120f0209010e040f141609141003081e21040b010b0a0e1512041214040b07080d 61
    0x85059840304034081484000344010b015500d4500800d18142c002c018044054401134040d500021342140e03009140c003400c15019401000a50401c1e0b41200c0704961400e00c000e41d13407034403414100c0c06401180d00000c0d1101000003654000d642c541c000e02512410a0303982d00440e007091001c0c1c80441c1d15035100203081d40b905840d03c2d02c80c900580028450007258010f02c40240380c10791051264480d40c07420000402c008003210900c40da2f12028141d016041769040c0c03450803240441c0c0344ca001445150010324045181d1008480a4444510050940c0c4182c0d4080c9804841d00c4003500803081084032040521448101564070410703540f0143c01e00700304003010340c0e80460202c0100900004401404140800b4092050040c00781c410a103160804014000f008007400d021403d010f4090300d00106141034540b401c0d9014407402c0d0709065650710f00f13030800240051603a0450004a440801d00381d1613102e078142154207907a80440380c0d070316140e03082d918240f40d5030058000300c002c1c0e6501ea20074a0140802c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 997093696 1250 997092446 997092521
    0x219020f100f1e0f21020c0a0b0f1e0709090617011505030304060302070807122348030d1410061b17030403090504090213 54
    0x40d5200c003421541050042c00c0032185810010040c3c0000e5903140c0120751000c0c4000000816140100030313000d03081c0a50024030300010b41c07041d9641c0085680e81d51964001841980385001d49500380854a914400b640d2030541a112000005148140d0fa500203c41040c41a0841d06526201c0c0080fa640c0a030101100c400d030300004887c6d0010f815402d00da000c240515007000ba1641c818514962038000003a0703603807045200c0c2c1400d260700031810400744413005054441c4c1070b4024000c9000500e80400040010000030141d2810100c1001d80c07440351030044054406010240b4a04c1d00291b0010568050b1010748003040c0c441004403581003d8040745640890244205040003507031200d10104424064801c0100582c003c2c5145c0002c201941e24030b00c00c0c0804458107070800325500c10f002c505008100705d0902c4050f110082082c2e00c03031a20a81c14000f50711a5000ba0340740e400c525242c0d000c0100b960300790b40d00a544070712019000901088240c3c030085070898125410007007614046d400f2200c08554 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 997094946 1250 997093696 997093729
    0x7270e0312090c12150f070903080d0e071d01060e0d02030f0d020d020a231203040b1b0403020306040311013b01060b041e0b1b0c040b010219020f 64
    0x125006801c40e041080494100b281060040d04054103001841040b4050040240c1c804006e00b07000303e1780319801039115101850b000b80d107d903030741c01e441d4081c2c001610201c04080c000380f01d44140040d040e111101381c124200f11031036807501c05034a440800c940001104a149500400c002c48400c01650300300044440da08100e40501400701c201030300a03040541b5080c2880a64008100e540c0001d400d00c0080100e00141200b22014000340c024000e10f002d24825200340c4200c0c0c00011310040c0640c0c410100d1040030130b00262021038011182815090007240303c001d4265100c6401b280000b401a0a0850303525225000000d0442d4900c04124407008500141c446080c0c400c510540d2031801d90b030a085204035841c0080c0314581c9071800c2015248528880e17648001d00b28007160001c03100d902044401461024003050701c0380d055500920300401d0402c0c0d287c01c80d109295520b41c41d030400d401030310b0f41e40d01c05801904d01d046558460070003291240e43c040364040a01031403450305a89110181008180 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 997096196 1250 997094946 997094953
    0x906040b0c0607080705180d0f02030a1401060519060c020f03010f0608011a10180b03190c030c2c150a02160f030201031a03120c07270e031209 63
    0x3d107450302510b001d80145c60b500400000300642400c000c08a51107004440d01900c00c0400c466990500b00d00d070701420b440080d0b050103819000824400100303100c0031246d00c40c00080052a6841040080090305a0712a00c0340e0402c8401c200400c80c00b030349074a42403a001130040c2d0741c1100140c1c0064212500c1070000c28120340c0e19031081c02404401d2240840e59854510300c5246800868001044003020015040c104416036003400e8684000c0303c003201c01450201d100e03030b0b1203050810b2407001c02c0d12000d4440701d1b56441c1032040c0c81400c0c401d005644101941d0f890380019013526603510030f4005440c8165070100324442c0c00da46150388640d41c1500d1100440c0850546031084000000d040103880c0744024a8189022410300c2030700d2000585030100c035424200003071651454001c409150b40d00002040d414001d0044100200302500000c0c91050390240641c2c1290b80c590016000d5280011070350440ca14059409618046007903011285070082d2104036801d0a041412500b08450112112441c542 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 997097446 1250 997096196 997096201
    0x70603021e070203030f030903070c24230a0903020d0b1e0c0d05190c020d020106080115091a060f1c02040b0a030507110a0803041a010503030f0906040b0c06 69
    0x1c103a00c0c1d003615600040700c0018508181900081d960380180c0b201c00000510010126441d480d0800441d02d11581c4203541b0003490347c3d1000702e42c035440b15019444001c0e51100d03541e90141d41c800e0200003000040c1d403200701140a0103c110511603000300d91858280424401c2c0030025070b6a640301c54207198030400d04040c1e030746405811884000050b894480800382e1200510032010b1208060f901825101d544c0002c1f981e44803000343c2c11000c4000032150305286015503421420f98089203116800314990000d10995a4520200d4200c0f000c0c41030b080000300068006000c2d00d04c06400040f0301c1c1b100d040812020401180c0052a654481861003400040004401e00c0301d03907082d82040001182503c0441c00e1502d0f01c8102e0803d031007844056020142d071000050f14147c0240b03540d261028190048602e003d00d1460030000741e0b881544c043d038500404404030300c0ca07141003031b031002e05907080a0007450406000820440868000345103c0d98010b1007448082103488201001c1d00d1090001001803c0d5030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 997098696 1250 997097446 997097467
    0xf110f0106050a0b0a0f0e0f0405070302090f0a06091404020c0d0c03030f1b200d1115010f030b0406060504050703061502150c0a02011805030c06130302120d0e07060302 74
    0x1550141d00c02d0110107000d2000c5c102864100301400510003403800d011a02d05201400500103030600020710703a000b440d12091101159142e400317400707101d105440019071401c15a00b080034103ca20310a0740009895210180083c00305113a0308007090030007030300150405007103002150402e44440218400911031070000c609156060194103c5152440d104000b0700a40107403002c08080c9030343c0100305000f40323079210b40d500030303401c1e08000e14890400090300d00d11100041c0040c002c00d9451020309061082c944c08100c400c4007006220304a414080380107489a06e5550b403038003812030041c8203460895139060001156100c0b80a11351250402c2d80e40001c04a00704911000709100c12120002107500a49080ca42c010304103071a1074111661000700c5886000d2064200d01612a9104e000f4100f54004400300820074000050036000c0c00035000c2e20f115540c0d410b402d8220386040c3c2d0700a00140e11000c245a80c00c1c5e08440200204c101c0ba60001c10010b02d06080c041c03a180c855031148000950010310480d14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 997099946 1250 997098696 997098709
    0x504020a0b030403052b060b030703060f0803070615080604030903021011060a110c01020d06170312040f1e0c030605011202030c06030604090b040f0201020601060305060d030f110f010605 82
    0x20384881c0c10741e40d0a5080544006140c1d01039071800e800048400b0785401d2202c40300440b201e420b050701c1e0100b440625150000400d260b0001e40345003005c41d0070401c01003200490102c0707500079102e039403009504040a64541002030504503a0b007174050588400085002e4505010151081d80251110b00d4014a5441481031045d42901c2d00c900704465000044180000819081e42000052001003080e05001360030140d0342c8250743c40c6104641c4005400b001c3c43da819003029044406840d0b80b6113440a40c81a13583c4c0364400e07010b9554103102140c00007400500d58559405103280203500358580d00d01c4000840103503811226003aa40f45034103043c10020032010340102e901405070000f808120000c154042960f030f00c101942544103003000f000054203500c41d40e20041c0800c0d00180180824141424484040c0500441c140d0040c0200340020030003901030300940d0f002d0f40d00900341000340c0d0450f4804a44100d0200001800c0144240d0005450303079082040c0306038003c1110001400d149840100b03c407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 997101196 1250 997099946 997099949
    0x30e031902061006021f1e09051902060f1309020a030506030f120405091911070b0703060609030b040201030603080f1b06040b0c0a1103040e090c01032a031104090504020a 75
    0x815001a00140f056960200301102080e014814406e440406c221645020742a00310107003200c8517410840c1030a0410540001030342c40e019006450204540c1e0250190b9140c2100303001c0c0d003041c030400c0b4000c280c0c0104c0c0010f09490030110020001c1c50746503185c400581e4826440c1d040082c9e11202840b00b18902030210f0076001c1e02102c018040c8250440709404513000d14400c851080f406c03440003d5420100414808070949400c502b003040d000d412060650f82c3d00005000e985081c19480041c043c28002c0c40717400c042d40d0701e949822200c0b6146503541100c071400284200e04054840100100040520700a070a500c5018090684c68560141c040303a00031840c06c00745040d51f408071041c8008222b04c040c0359504400092244d0390b5a1000c2c00c815201000c4140c000789951100150004403c1400c50b1050300076030090382610329580c00c68004500b640d80d1581c0041d0b900c2101c0b8564402c00c3d03800301c5010300d038983e1802d001c5080700318180325020030381050f0f00c0018800d407980304200451600c05120310 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 997102446 1250 997101196 997101211
    0xa020c0105103f050c0a030f170319091103120408121806031f090501181e0c0207050a150806030303150f06160c05040f0e1c030e03190206 61
    0x5040801e8401501d111407110f8030701d259106294009020f0000a00841221503005460503020365900d00e40145003010300b2000341c1d0a000c000011100215842040301d0140008034128040c0b1080f00a4000080201d03c030308461101c200e0042586c203440621506500307107045044d09880314076004200c4e080246a1031310001c1010200123060402401c2615140d4490381665015140e03130f10445054049404040f0b84d4440c0010460005822003083c0c100701d050703840d0044009500078040a00030103440c101c1210703035603400ca0700c802e500c1803032038590150540010520441d64050307510b04c045071a40507150000320301050000c85c00c0c104540c0000600d81c00c034006500951451a000145040c041560028944606c1d00c0021a4005507200c3d01a1813454018403080f085178460351414985401081c030920b1700990408641100c012681d1080403040608040581860f48121103049000d9100140e010b090654405440c0c2c07101400300090b0101e9081c0c0000300e50301464000c0082d03e8804d0090189 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 997103696 1250 997102446 997102499
    0xb040c020a08070804080f0c010f17042a0801140c132711070219180b03160303120f05060604090506030f030309150a051501080a020c010510 62
    0x4001140d000401c01c07415a004020941c4401c00c510b090340d001c0c070440c0e011000300c0c03041552151160901003814010054244c03075005003d00c15180c15900254421030841ca1480700728006030204201050104441d070030308941c1001040554829402c0b002d4541001003d0780d520300801100851208000360855607940305e030740c1885117110010003800743c0e42c05002c05191407000d521401000724840201d048203000c500340f04958440580038410b4210b103000740d1040b1460800344d0f8119103081c055034182c07071303588040e50141c42036000000041c00202c001d0a030144607012800c0d071100113030800350010314441e80d241034403142082d003c0800c3d14284080d041c1c0051629041c0081903a82074211011503001c44000b1589503500310019040c85501e000d140007a0000100704035442001080114500385802d00d441e00a40321041e5803001c0340c5046034001d01e58288a840c9800b958001c0e99003e82c05802c0450152070a125007011b2425036000381c40b21084c1030a840400e000702c0070115007044070800c5032141c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 997104946 1250 997103696 997103711
    0x18090703200307030201210603060519051b0c150c19050301080c010f02190b090709090506040f020a0314150604020c0619020405180612061b1b0115090b04 68
    0x183d01c0314140d1000a043c000782d00308100c4800210401c03c1d04c00c2c0b80b080800c02c44180d0705c2c104100030306801c940c4075031144d035406005081e10300180b04540c00b032495070341003041f04d81c520300484400798408204500030380b04581d07002003c000340601c014401c1244100d5079888a00b90640c074070340940a4071684060000900040c000c94500081840c0030f1002464540d01e4900b44001c03d80c180b40002c0c041011942c1c0d484052414130400000c030900950988007201c8419a407580d00004a0b03a0300d140007462034100402040c0130903d104401a11540014441d1400e103503207a40d4000c0c1100c4c43e4910b4116a0010140744007030000e2648500c0d0300c00000d650540ca0034400e8041980c0300c2c7c50003081d4800300d8040580300c060103c241c0d81030b60080d03e4094041d0003000e1b40d400c00f008070008103c0c0d00902c40d600720041c0a000c0c150106041d40506403120400c040c03001402260b8030f603a0455007010518040210b03000c1c075814824001c1d084c0c805a091310705d04810382004404403d6aa5039054140030341d040001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 997106196 1250 997104946 997104949
    0x8090a0515180a120210060311040f0b030607020114061c030f03110a03020913110a0c151406150301060905011b120f080906040809010c021809070320 66
    0x140c88018480303540700c07801c560b6140710200404200200d5099500e21030000c0b804100a014a060508821503808403034086c00c0141c81c0707509a9a1500000300080009540d454050600c1d070009017148040390400b0030f0000502c004207140c01c00031522100181e441e10261503103002804041500030348107850720003007083c51886901c9065a00c00c00101040480850a800c581c032940c444500704a890309010341d00c95040c8002400780d002620403612074589480c410490440601c02c0301550100c814429080c10241c1d4415181280d5a07001550300c01120511079107401520303c141c4000c0c0e02101d003038000c82c2c1401d0701446607900741c5030410a14000204014800581c20600400c11100300f440c11548141c40d4061680300c4c0007134204000e02c140d041150711804150880c100451070611a0349441c0306959110b000c60f902c2c030090341c0c09403041c0170170451802c09503c42c40c0b48000d03d5001038050607140d0000e1540c500c001d00116400c01c04d68010388814810804001c0c41880c0840d4415280c800c803504a40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 997107446 1250 997106196 997106203
    0x1103011d0411101806050c01060e1302121009060204091a130b0303090a0806070807090b190c02090a0203090d020307020a120203120c0a06060617270f0d08090a05 71
    0x911611544402100000b042d1192260b0850016520311034140c40f80d0b42c60014081d074007c2c008803641c650900802044107401e2000161180510f001c0740c2000320f445800f0f1202c50090b130010200f040c024208007a900d00380d036002d00c84c419803140000680e40c40c50f0514000841d0215440c0e540c4c90400100302d00c941d50f40e10607508002c1306101f2800030750000400c000a146209503606160801c0c0b50b101c1c006000f61001c01d4003441540151202e0340f19036140f520840e14030204d405000f41540003030040e0030509030703040074072180302c5110b041081c0c0c418082d030001504882c08a41074100241c00000b00315114109004504615030140015400d103217440c1e0000c0d000140c1801075540b000c10500c941806d541c0e04000c944d02d900c084107801d0396513242040155031152204401624a02d04103180024030a01c00c0c1030b0700300740400045c982161511181500c0b451039141040d066158600380c400309034040d01c00d00407203880c0c1c0702040c0141b007618040d40e40689500c81c001c040d504c013a04040c074071402180010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 997108696 1250 997107446 997107473
    0x30b030102180f2107094a0f0a0c1d06060f13030b1f150c0203070b0406090f080a030c0f0c230102060c0a0e0f12011103011d04 56
    0x4640d038903e41800a000304400d0301210b6103042c065081e04a95030400340b03000c07400400307640349a0000e0003001e00c0302031141c2c110781030801c1c00b4111030081240000000c0e0304200c00b0310b902c50700340c03d0b4000e00410710308004d18003062442001001d030015081c0404200c44a581500140821460300c0014402000e000d008110001c16803401204001403600b06843c00c80c0031a40764883d007092601d480c039105e0a240d00b14441c21950317804010150308221402c1d51400000d0012255011400403000c80e42c510202d912000f03e82c01280c05221f081070208005a9070303006840545041c0d940c070301c1001d20345840006000101d03132010301c2c9a00004540d0000c6603200c4030142d01d40e9000920310400ba601d5250500c00c501c0f19500000000b031008802007640320703140240c003943e80700036401c5844645446100746c3c0715100c0d004850740070175440758507042c00f401c0040c2c002d580c040008240c000d0444510700468203481e03411105011410001006011915150a04521101e00c41882c8142c81c5040d907507090055514 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 997109946 1250 997108696 997108699
    0x619020c041116050c060c0706030606030b0609100c0611090a1a0405060307140a080402100216051216060309170405010507080304050109061e140c030f100801060602070303030b03010218 82
    0x1034040b50f80a011082001c4410100f020740030540e201010354045031125114000d0381c0009041250003d00e951083c02410a0031100503c0d09190481036410406180d103004103040900820106460214440d4032400d14980c2802c40759565401401c030401600c031603290000c40f001e148201030b10000001d482c05a80985009492003a500e8603040000c2d204036001000e0340341e15000006000b81c411b0f5008800e03d01903803003036031107480c41e00e02200241c0c2c42d202c0c1e0408451224030046010401d80c500000a185608100170a480703421500b032108690180b2140c100102003a11290060200820004103480174080050001d00341802c10700000d046100e0745034080d0101700302001240a101303080d4885c40c20264050000c200f140c8591525607007800104480e03c9205140c40300c000b04001a0384160751250034082100c628503925251001002c0c02c0180c034030a40c1800300100401c00c0a401d00c5898094400c0340c008004040c55450020295801110524003a900601102d07080c42c1941001d00d440400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 997111196 1250 997109946 997109977
    0x20d180503220f080705010e012d110715020c03060f160e03010221011a090d050102120702030d11040503030304030c03050c0d0c0b07080402030d050a0e0619020c0411 73
    0x54030920700312503019904594582600300c2e40008220303200045210440381b003030b25001d0750707850403000544401050003207020040e0030f2800b400d505030802e010040090040d1f8200f942d2800540000341d80b038440150003054814000c01ba12a812680421107a03901c510210b000780f0207031500c40c6040104200c040e1003201862001e800b401d40c114016906050803010180c003c5441304c81000d2118130041d01c0340d41c401d41c4182c03c2c10010072500304e042c100b600310320414583c503803400340302009015100f50140e000391443c4d5400c1c000d8074407840e290000c0500400751076000f9a102c0f031401d90a03800311070714548002d1406100300070030055524084140d0b0390181d00360600ca06903014504040d0396510680d600e415484c06071141e1202d81540081d014031035940140c02c900860f68a014040c0c50321041994040d50590101106511043c403690050210340c1ca41c2c5412400c540d12030000c100707103401c884100030000e8804203400c5001c580c108002d15004008071005d105144003214444043c2c410ba0010520515 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 997112446 1250 997111196 997111237
    0xf0c020d0c03020304240807110309150d020a020d12020424030f110a021c2705060409090b060405010e061e1203130905060108160e1201020d180503 65
    0x500038820b807001002202d002c0c41c091108a4846a0303d01100760104010604120100300650320400c0e2180d8102c2424000710319002f0000c04004200e03143c0048441c0040c4204107406001c0c1c4503001428110407503800034603a491050f4005001d00402c2203c4008091041c40104049126140d82c511101d203106542c4041400d402800c80180c14945140d40c00c0a08105c0d4034002c14404a0081610042c20703420385074a031841222202400e600ba03041c500c001951540e94121485030284a051076628070103c0d5101c0c40d540c2d10200d07480b0340040e0710165030640c5d60200c03141440480005982d0000040350200800d40c1400d1001e0b49501010f040d86000d1403403038807101203c0c087d00c040c1c8803003907070001c102c030040d45000f00b20345640e503000940036220b000807000c00180c0c040c030318092036000c0c1c0320503110758a1960b5400c11007010030042d01c1211080201d240d407019513039264850200310080001c0000740c0e81700101c060420a4815902e5455500d00102115001154001c410390f50301c803035400c01d0f40c803051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 997113696 1250 997112446 997112453
    0x3012301210f030f0c020a1403120c0d261e060301181b0f0e0402030d11030d0915050406050a1a0108180c130e0705090105011b020301061206020304060f0c020d0c 71
    0xd080c000402034100c8580c03c00410000780c500c0b10314a4030a0100c046550702e0412b034034000ca45000707a110720070ba41d03800210f48812003805180300700602e031401d03c5000300b003210000c12045048400c0e6a200b070785030f05150700d201c00703510418000c1c1d500010076802400130398414442e81c0e4007800c08080242103010701c6841c0c9140d10700b418504100030810140f5012510b03441b00000481144180c44c100d129104c0e50f500b00d41494007074004150205100005103052812004001028000d000011680600c1c18004004444d6851090074001c50003501300007164503010306004102d50030b00c000809842c18644004000c0e81c2d0051144c0e50000c0400d415803150468598490318141080754025448503200700c0d20307210600300c3c0e80300070060a50300e0304840302c40f0b13a50b006210200c0001c1c0900d50000d4400d80d204500484400114080903201030000a8450341d40c0045c940903445440c000c8a00d241c0000500041c8070050060f01070f05a44102d003008030420020001e540e442c507032a43d40040c002d0307a05000c0c090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 997114946 1250 997113696 997113707
    0x1a0105121008100509010509071d040609080f03040c0504060503120c070e01080a1101090e07110f10090b090303070503061011030a0804060e0c09011403012301210f030f 74
    0x10002c51080310000011640460007914003180e41e00381035071070308000800d0300100241c070b5000c03600382c901d00e41641883d5203040d2a050300020320644106803281b0400c1c00040c2c0b00700080168503401d01580d80c50f03040c945441d154511646d44241e2080e0b0600320144107943d00440c0c7d140307541c10b00c001d0340c17617903020240000750525209500c81c5403031284441c0000780c6600040350004025108550827429510a2401900e00400c0342c000c980c03d0380384460014085a00039a03280d1640c6003400111880070099021040ca448808141c2840d000d403500c07254401c004581c2da000d904240f0100140d030440ca04007030000d020b404010303c010b118082a0072003140e01409082142207200540c020359598100e003200140203002c059404541140c6083e0115106c0c1001180d14a02804010400130542e403901c1c4900c03a510454070b00c402e40c103540e14a2007066007000c00700c10452071040015401403a41c50641000f1003040440d429892520b281005400010301094000e100158103045c03a062042070101c8c12202b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 997116196 1250 997114946 997114949
    0xd0e10020a0210021e1506040203070203070506010303050a03140f0406090206040306020313110409050a080a02010e03040e040c29030c0904360302100506010c050a0606091a01051210 80
    0x403c14403866180201c16408114aa12141d003140b84125001703562902540c0c0c0c1000e00c030b100240c202e40e20045201072504d5001180c0110f6148100d909280305910b8071414440282d10440118a0000703c1c103070710036054040c1406180a003242c0400601d420403a00c2003048004100405803561012000110f50300e400c02c1c0c070055500325104540303030f1a0a200b044113030f03000040260340320000144c00c1c8040703107450302411004640c0000a400030039040c0d600d0380440c0e04201d00070800d40d5240c07400c0450000c41000070700000c000c00b08101846040508004114801c580c000f2540c1c0009094020407000003000c0b16440310603001c051035a03998032500d10282c0d60207000041680b0a040c0040d03e0382c1c58a03003401c40c1403003104208805000602e072880744012001c5248004016801901031515690341980c80342c2e038403e4040c1020003450aa80e944c8a050607203400d4111502c6550b5901400081014824050182c1460744016540c0c1c0114001922a00a2082c0d8540d020003d200141e64011910480030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 997117446 1250 997116196 997116199
    0x50103051c170601021c12061205031218012a03050c070f061812080619090e01060902120117030307090306051b0c071e03020a12081201060903030e030d0e10020a02 72
    0x1203581815040040140c1c600e00881d10302e41d8142235001c01d140b80c01d650200c010941c400021441c000540c22400d1003c4002000000b401d00c880c2c04a0401810a0040d074110100712a040a0030f41c2406400d4144071043e02039401c1014604801c10042c2a02c0310101c490503a00034410312070030b41c0c0070f182c9000a004c0c070500140200300708030710640c20031010080f06e041d0001140c84a203c1581c46905029402000203078000c001c140000c400c00c50100740784d2048020340c0d000b10000c01ca00740c0360310f401820303680108020151202c00000400003012405c1d00e9907401410500514510705000030014403400c190300001d46100c0d81c400106a8017150000000ca40d00d40c060000b03070701d8140b0b4129480e111b4a25109405090b142612210707442c42c020000c02d01600e41c0248404442414580404010381e43c4603c102c4045000704141c010000442c86a240201030590f600c014560540c50300504400341e1110b0140290301061418520381c1d009000400300d4501a1640c5449006041d8202d00e00b515882029 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 997118696 1250 997117446 997117483
    0x110a050d02090409121d010e06090a0506161506030b0a180c030503130e0c0f0a14030412090b1c1a0909100509121c020d0c03050103051c17060102 64
    0x401c1050f11922001068003d4541601d4070b001c680b8100c0d842c861b40c107074450004101c036440020904d002000380500310405403003c544a070306d480219030140e109201d0390b4203060f4040c42c3e0901700050021900c00f210b4000c00b09000091650781c6145803940080c1030032142c00d45030704061034282c3c4855403e00c14070f5000085601d1481c0d881c140551030b944690b14180128132842d9003c20805040003e1a000320400801103290030503004d261443d9400030300d514030070025460064a40c0c9000c1c0d202450003940100b0025034151503c00c00034003803c126610000940300c081c00b900d1040d0081c0e010085101c5811b24000c107124007100754142c4c86005030340720076074864801010b01008142c0080c8051440380e0040b410040368440c0303d10542d45007050312a612066104000c4240c400006040440c50040c41180243c180400c422041c0c06461155880400103a910340041050280c01c000d8414a00c0c0c2141100d00a0b680304080100844030703d80c5444000010203000c03529913442080039082c46000c52002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 997119946 1250 997118696 997118711
    0x6070602030a05040312060303121104081b01181815051c05010e0a080f0f160302010e06180a110d050316030e010212092701090b13110a050d020904 65
    0x199401800d041c0d405400040e0402040c140ca000d487c4261800d4136019180c602e5520741c0408044007034259540201c00c1b14a0500c00042c4404080000c0c01301c601d800d05085000d94050000140f440c40c4032100d20044500071101040000701d0080300246590010364086201c0e040943c00743c07028241d6a005540243d0042c0f043c140c003246111305101400c0c8100024041181180c5107103948400d540305c05400410100030102c901c0f25050001d203400c01c00d2403641801c0003000380c2e01c9500c28010f1301c02078005d0b075102e03144112038101c140500c1c0d034041802d00022111400d0074001955580c4d9000b4010021b440300c0024070714903076500882540282d032120480780c2e50800011040d00500403c03c08401103801d032241080c00c0c0d070011600321070940c00c6034a55410070440004020510003058150a011a01c20140d441c14080024101d030181c04e20307070b0000c500e20008009000351414007030309004184d454070031480e0311140d03c0c0d0704480d9030380d6003803500e50340307d1b081d41384164024481e147c00d95034450b1034805e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 997121196 1250 997119946 997119961
    0x90f0f07050f2d0301061d1237030503010905060a0b0405010e0a12080405010f020609031611120706090515040506031915170d170a0e070f0f1d0606090607060203 71
    0x20350060805640e000d00801f0030320207081c000006892501d180080d0400c21021554041c90b02c0620800c8501010310741c2c0d0354012002c0742c42e0300d0030301c01020380000b4400401880444424098260450425a420220a490702c0584c01090165019040c108400640c100d0125554111a0f00c00360a201e0441464031200f45032600c01c1e50b11511809000c81d240d001c0d83c0c2c00e02800400c0651042c40844003840c5030180004500403500b201c01421101c0703502807d5642c0c0b00d92615001c101c180510400104100d41c04c0c04800b5050013115800703184940240c442010308880300700c0a85d81290420f80d1655125101c0648110107941100c56211005107000c1c0d0040340110b0101e4010101d80c51000c0310742c41c4181140510b901c95440340200703004600d1a40284541d020031848940d4484000c1d200000c040340668440b9003003607020380c0040c01882a03404207101e00c2c14102d034548000e00b040c04100e107a030068400c000f00c5040303005080c0351003090049403800103070301c0c2e0000721600594004411952460101c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 997122302 1106 997121196 997121207
    0x3090c090f072102160c1a041a0a0e1c03030c14090d031e0806120f0607110a06050403081906080a20090f0f07050f2d030106 55
    0x700610b03a1000300c1c0b040c9098071801b480c0080b645488070801d18407504200600f40c100d4204030401581411655402d504980c94041e0750700c40d0303217144064a200030127244050b0030003a1400414081820145401009480b0f40c504028004c10440b0480380a809545c1d80942c500080000482c1403500c1c2d20702900d040d04c60719203805025209001e02d008814050303010400700d0f9074001070192a1814440d80001c1c01a100c004181c11614191007540e5181e000c1c2c1003000307010b90344440000003042403060250301500728000744174504043c50020510a0100d40700314809000080903007200101c8d004000c00c0740c000303c00034540038415407107004c1e43e018002c5901002100f07030b80c1241000d03181c00480c1481012002586000d6261604103942c42d594003c0c010420080204a0300300422011410746a01f81e2804a0140c01c901c001c00c00340d04012418188903007040c1010000007401540207 = true := by decide +kernel

theorem cover : BRFrame.Cov 996942446 997122302 := by
  have h0 := BRFrame.cov_init 996942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 996942446 ≤ n) (h2 : n < 997122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
