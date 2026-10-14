-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0118
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:55:54.728547+00:00
-- url     : https://prove2.me/submissions/9fde1976-e887-47f5-94c4-f8ad91b346be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 21043171 ≤ n < 21223027 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 21044421 1250 21043171 21043177
    0x1a010203120408040503070b030f090106050306070c0822061209020616020301090c0b0d0f1b0c14031c0507031802090601050405030a0c030203010c020609070905150d0606080105010b07080f 83
    0x1c4503443c4941001d83c2d68021030301e0550b668000303410005010040103009141c1000c410351083d5110000e1204030300d0140441d0f122400a841e010410a0030400030007400159012601000c1d00d407810018046199900034944021501500001520381e5074441c03100242c3d40540e4420540003084640b41174021a26501c510505c040e00b01e0b00340d5250320043c03001c20418043c040042c050180601c0e034a06000b110b0200b1030361301e4034040e89040e1902201019607041020041000107050402e00680300f03c50508040034825089124043d100000300702c40c80074411701c0f001c2807800100800740b0442c4c654440c25001c2d10f40c1d41c0b1100b22501d4101004001514008000325000201030404501e06522440441e0420310a00d9054850030a801010001c504003441012010359840c800307001c103428100c203541c0d1503030443c1c03051940181c1c8030740100703918810002501e00800e1004040c00402449407511102824551040035495440c04000140c000c04000032901c03055031041c0482e161801486070200250 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 21045671 1250 21044421 21044423
    0x9020315040c090314030406050f03060301020c06161d0108070c03090510170105010509010c030309061503031e05031003140109080304050f0d030c1e170c0d1a0102031204 75
    0x800100d030030011030300c0750b01c110160b5416540d03444a00a0950503c141d001000c401032400c1d0341d1007008108015079125003175640354031071401482d640342c54220029000e8083c00d50f40b032403203000d40000d00070500301c910000d410490320364a41d04d94808014484031010001d5010080c041404840020316a40c03040c60005600b40c42828020086520f178008260b00044840e28800850404060007004441100446004003403d1800741c1c81c000c281d000007450300750540c07001418151511904010010b003a003119a806a600c8002ea0109039242401410440390207a07a52041e1001d03500c00352031910070f900300c910441c11464110300702e0f403450780e421a0200c04032a41e510255618580b100000c0d814400540c00b0b140900010404c042c03110050301d041c150b407480c00d03505140c50022074500703031600005004481842e1541c4600e521600080075034035070803a0328400384000147e4040040c450f40c071101504d03040b140f0140c00c00081111004032100c000142c80c5903409a40188415014007100104d529401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 21046921 1250 21045671 21045691
    0x3050306030f030a020706030b060c0d0c0c0e15010e030a03020c060c030f0708090a0b0a0e040209040e0a0b0717010b040905131703060414160509030f15010608060102030a050301090203 81
    0xb112030307451a58115003000080800503000007000308040b9526015000c0000d500b10f40d0355182001111810f9529080002d0038402d000d941380e009001e200d407040020008000c0304007060302c0d5182c81301048074050410003409000c6400016191628100080c80c3c1024030b03071503002025188035801c00c2014a800c54444001c9920080007008119503210010f030000c1441100c0c01070301c9140c00301c104240c00c50950030042c281213083c0001c907100c59110000c0815100700303807001640c1309180e101045c0545221034404085118003218407041103072881d540303842603e19658100d030441820105220602080c8a40017000d10148001d01075010035034019a040b8034641c207030200105956840345210000c030301d0414903d0001004001840c01d040c01860b400151803044c500d0751f07240c0144074040c02170840c2a10303410400003190408080d01d0400851200f00c2000c0111104c0a44035099440203400074002e01001450b410040780465000209844105d030254941c542140c0c01e1202c45002500010141810 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 21048171 1250 21046921 21046933
    0x90c0918060e0705031515060a0306090c08010503100e030712031d150106050906071101020c040227030105040803040308040f08070b160e030304030f020f030102040b0d110a09030305030603 83
    0x140103120391098030b04040042e01c0000d203002d04240c00c101c0c00103105400c140058080180c1d00b001040c0808801d601210415142e20514134128020038454012102c0f0307501d06403108804030b42000d0700c14100c0d1070440c00c96019980f052078540940348403210b00e1540e5070040c8241b00000b20891040b1040c190980b0700010b41103001419148008261105054180c10000340340d02a40c171385010aa0140c805810032900d820040d502041e405d12a6180c007411103000404110300303584c42070000000a00004005540707070001745d620303100340300415601001c5030022400d08503050709041c02242c0c821900421641d040d40c1c4c03151810303034101e10700400485020700001a4440043e41a80280903807501403031490801d4500780d9114129641d44000d1001031160007203c011003a0b80000442c0c00740c0b50f001003820002d0210344085800c100d0200b403c0c59165001042c00b04041b4202d00c083c0c118003168520600c0f281c283d42c00d8440091290b50500300000d1040c4000740042030080d002190840350150031560 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 21049421 1250 21048171 21048173
    0xc0f010c0903350c0f070609090e010b09010b0c060a09260409050a050108060601020606100e0d05100219031a01030c020a0b09061006020303010e0f040311060a09031101090c0918 78
    0x1090016482104075450011901e0580300108000045c0c10468440090080d107040c1a00901002c5241c8140c64003030b42c8a519070b250b8600c081d00050142800540152a156190010210203070015a103481d07051080d84006600035201b4011f81203c075420071680700800184040c203460b4442c45891840307000714204030004070303440e491080c00d226048018001a455040000e00d034108000070300418115440a81800082d603140c003400240d005050520400c0d000d4141cac00b10300d00c4046400082d15a02421b060795020390001e80003049005401e4100105008285500b030b0100c54000240c2c42940540a0300391425500940c0440080d0f0b455004a44442150707a0320408140e000f201e80800ca900444d052120007129100f0200c090007e41c00a581035604041d141e98429500910030b546840c074410204d4203140c080c1414a41c0207801d0400d460140c40c10414420142400c84421800128106200c0201510620941080e01e81c400a2044200d02d40021140604002c141c0f80402d844c282310050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 21050671 1250 21049421 21049493
    0x1a0103020f0f18090106030b011409030a050703050d02060108060403090e040303020405090a0e0f010b060d0515030a08031f05100c150c020109050c0f010801030b070c080f0c0f010c0903 81
    0x18583d90102002d0414007000140440704a061b409441410b0804440310805da8000140d00d40c2e91541c1030000b52175940210009140070a43c440103030031801600b801005000340464941a600155002c440c02666110701803541c4030801c4801030b0028001710303401c1c400744085002d05c58000d80071380350250616131140001504e80000740e0b0f0082625650305400040c0c040103201c8503012009280003005225030034070104603503100d00020550050b44d5400001d9101041030b000c1901e5440260444044100d14580703c0320725401526240d0401140810244407515000200003c1c2c0300f0185c0855051a1080780030348116000e00c1080f22000ca041c4104403c5818601c5282d0081c02c640e400030507881080c0c2442d5040c402004080c43c021014811194203030390704031230f505044a510248c0ca526641d1100c40840740e00d490000c2c0101420b038000384131002509010007a10340024004180c0d03641400c0c1d840740900305c0307590f4089180481c403481400c1001c24000d01c0500c522805a48500f007140b41c3c046161 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 21051921 1250 21050671 21050677
    0x1030218070e12030a0e06040f050f0406030803070206090f03070c23030f070306050a0203090303040f05010207061407081303021903110105100609090c0207030b040201020118080c0d031a0103020f0f 87
    0x40f054941c0041243c40001c0e601144110500c40155001450941815800c0383d5420300c0d0f0240c40c0c0030b6031a05c400310800c3d072074a6201c44000e640144405480e803d0032000251214803e494040040c402c01041101561004c421200e178190f0207640644240e284c8411002c10800030140b400356950603014442c019102800452550a81c0c14041d0000e9810361a2005c100c40015092170240352050040000b1a60000304482e0416040400024144a9072a1140c007920414400070f0602c0c0c24019401462079101002600840c0b00361161181036442007082e01e441d4203107420190050b40000d14408615907904405c0c140540a450708003100c1c81e8900706603094030029103a100b010102d200017005143c0e808681c074005460f001d4024469100c0c250700003076440c000c1b808007611b8a10740b440071900f103a001b54132003001204071686602c54101c0306d0a15015a411201a0942d107025213a400029188207104071416150031102c04544031003580d0044000303401c80d4840219078442004082c51240b009805 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 21053171 1250 21051921 21051949
    0x5030601200f160605040308070204050c040f0308040311010f0c030323010f0509010b040e040b0606070b04031d0301061d0a02070b0108010f0b060304050c01140405100302030a0501080601030218070e 87
    0x2030991154407031160f0002c1d0032591150040000c1404280002103240c4110307a1100c1d01200c0200312500c0c0d0800310290341c07051780c1c006182c403080b03a400003040002c8400500104c074022107104510b24400c000540d840d42c20000c0e20400640c1410011001034020340c4000351034040d550a802085294a86a020544c0c003038000c0318003107a203c0000c210074038120240501605445007140e003031030715002d6903481d000300c090002030038064208001089078583c00c1c191151290460244040ba0900c0d00f40540664500c8036011080b03d01030101c03001302d0905000344011940305c046140070982c02031000005406020f0a070b1007420350200a00d4008c80c0040810901904001f40009021551203011804540001940d180210b0040c400c000c081031000c54030030551402070a213080d68910a80001c44d480c401d40e00100d9014002d03c074418107044d0301da80558803524942d2410001e03640c03640358090b81c070b8009120007544280800551090380880c65030b00d82d0000f4a605001d8081401d81c030007d586000c0604c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 21054421 1250 21053171 21053173
    0xa0302030108010b030a05070303030b01050702060711090105191a09060a0f02070e10060507060b0301181505090304120303060f060f020d080906010b0f0d0603060e0f0c0105030601200f 81
    0x144181102846240710b90130085000b421104096a41c40d500e0b0140e5100160134590355000410459000d003040350125035000b010301e40da070409460b09280181100e10590300491040d000442c040c140344c020322a42400411100301500d00d003800c1d540c0304250700480680e055005201d962500c1c0c03200e03c080c000c0d0404984a90383c01030f031411402403a00141c0d41c4039500103400102807000810100c28544140e0b402c0346410303903071860701c0d0500d40c001e030004918940c1c0561038020010084002d80301a132450505c0784403456142d0300802c14810941c1c1090b96034210316041084108442c100715102c000c080c03846410040740c0c141c1c0c0c6000784440c52503a980100c010924244c07810b0385050703060103400c55080c81802c2504043c28032908180c1c0d03030001409580d4240c17200103010030002002000f90344504040410030f001c200e8403032400c000a05501a41040c07107114555012010100c003007504200c814040e541d0710305540e5030900449403503071418080c41007441802d44000c00c0315802d001d10b0426240f454 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 21055671 1250 21054421 21054427
    0x12020a03080706020408100c09030209090f060f09010b0a050603010e040c09050708011502031e0309120c0a03020f0f030706090f0203010504060c080a0603081b0312090d02061005090406200a0302 85
    0x10303411800c02c7c1c4030405017001c440c60255441c0b003268101c1000790981340c0695141c0d86503034400c03404918114a00c009078480303100340003c216201c05130303a901c0d0384a20280300091203000800d0003400a201450f00032241d000e04248018020106412000c95016001d9483c201980da07640d0a00001c0b0396042c0d03000c01c00103050700300600102a074405041d5401d9010b2006600e0400d505203030f0400340802d4520b00d1100b01c0000046510100e0400c84c0c2d0301c5180f0508400c565407151009101e955106030301c400c80c05400350b81c030b81466540c004a10003210f0b4014a024510707040d541d40c0c1d030400074000f021044514805d1035100a0150700d0034030a052245100384c1000130138654081010703002120041030181501d040c03a4080c0002003501060310035200000701600e508032070b440801030543c0a800200d03039080c04100708002500c10005200040303a840f82d025a070040d1503220090036030881038011150480b10182c00320700000c5069000b4910590290b030f1001d03030200d81c00010982a40305040e403400180d004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 21056921 1250 21055671 21055679
    0x6050103030e0d020f040f1d0a0b0105040203091c020a0605010303050a0305060a0605120a091a070809070b180406030507140a080106030201081602011407050c010c090602030412020a030807060204 86
    0x1202e80c0a8000e08110741c0021409000e0340019100000510258040c90300c2e0340c04003044903c9500728491303640040001c0151300091108043e6164034401e400d03101c3c2c018020000a40e4202442207034011141d500c058a02c07400e03210030740f590b504030144d01c8000318401e81c3c2c5801d02103006ca100e001e000e0b6100b0b60b12150b4542600304010700340d83c805021144a000c070404108030070ba4000044404100841a0710038542d542d9141c444010250083c0c0030f45081a04043c04010103080300c0c400707200e1103498441c942c0c01c0e180c640001780da510141c080d619000404118002400700f000e0204034025800906c00700b0215100d0350303801c4c10003200e075126420356210b540b209455840d08030340300c0000e014850020890075107103800090100201400c10036a504180c407803d00141d00c02c1d00074002103140d181c42801a414465001001c0d5844141c4500d146d500e00821288900d00c81c2c6030b0722081f651950b004504142c00d00261444450345201c0c200e030b2003005440c000002609407405002c146024910060720b603894 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 21058171 1250 21056921 21056927
    0xf0f050601030b03061605040302060d0603021203040302151c0c030204050102100209090a05130c120b090105040c0611010204270507050406140310050301090b0703180b04110303070f0605010303 85
    0x4080c0c510350515092481804040d100001c040da401819102038148450407911305441c1449950800303500840c00040303040500c2c0c0950840402c40b8821756070300303103400c02d408601134980c080c6020095004240081503042c180c100405400820100c005d507115070310340d0100c01800c03903150520001c04203801103401c10456805001c0121406243c1500f0351500b00840c00017030071840d0080010300d24030390741d40c0400e401049807048908525807001c0100500303a280c402c5902204000d02e0110f596007800e80c001441802d060141c0b42c042d641c03080720f04c40e000d030416005461888042841228a650038400007540c3c454450299400b02852017000d024040c500703952806458004055400b803007800c00c0f00b04110b580c80307000090914081c001c503d4503070312030a62400900d800b0740e020503415030922011805120918440c0d500654150300d00300302a81d1400801090303110014006010030890302c0c000b802140000c0070a40c0c014100a054904d40348031a41d81e0f50b14007803591000e483c402e40d200014020550 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 21059421 1250 21058171 21058181
    0x8010302100302040303020303010b131205060a05010b04030308150f04090308040203010c02030301080a060c1b1110030c0509040518030c0601060807080c0712020703080f180904031b05070503010f0f 87
    0x101ca00c1d065203003074256240a035907480184544030b2010710000f240c800c4c81040001140240c409001150062401e82c2002070395498107580c0011560729104c000100a0610742c100c408032a0300d92a00d2010340d035090f04248040445400b415080301801c4440203ca556500c6080409803080e01c0d09100c50500b40141800c4600c022000400d55200708014441c0440c0002c2d0120042c0e40403101090b6044041e4040703507140091400030b00c0040700700c610311080011b051810110a80161800c040000c1245011004d48219402000100303c04101c0c0600c40d040940081c1d40c0308440c4030031103080400b4400214078584c006d8005072030340e800420042c0800c551000b100707a040800c91500c007145040c40c503d01c0350a4030800e00c0c002d00070390154588000581c000c2c8503901c000e6420480041d01d43d8401c40282800781e110341e611450600308030752100310a18024982d10b00a40e01580d900440300162080c0e64281221404155054490990700003500e075424040e40181101f26400440c0c05a00d01e11850240c072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 21060671 1250 21059421 21059449
    0x3050f06010206010302210105010f090b0a0e0a150f06020d0906170105060304050c04110901020c0d0b0c0f04030b100609060203120f0606040911030114120c01050a1e08010302 77
    0x26402024403000ea07070700040c481e042d80d4044841c2019180005040108407611a04456043d400d20000003042000034117810215407054609109410444041180486407401041804466800407942c8482035502903827005445050201925480b100c00c1d10034080c0f250321607401a809146030b4188240e100c04020024081c50800e10358200e0542e0108503010b105000302400303020080001014031001b040390040748a0054810440001440b50303d1446600507024140035102d41e1203490898104101c050f40c6076900401082c0d10307a25150441c3c5160b80c4042513100c0004c400348408030110354501152070045c00340c00b428100803498034802400718022903105070150340003803290441c0ba002440303451303130b0014240c940c1d0091561900001400e50050b5004600c10903c1e007000c0c0085113503e00000c5041c0c501c2d8030581240d50310740108005c154000413040c4081a000000084801d50081c1c01901070203406040060b811038680e62a84c10300c4249080345c0000441c82c00040040d410101081642d04c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 21061921 1250 21060671 21060691
    0xb01030c15080403031a120607090b0c0a020f0a0302030619110f030402040504032001060311190b07081b0c010906030506060a0806150403030908070503071421060a0c0305 75
    0x64814848050300d001c00003000a41410346860101b80c50218006481c124494000e00c3d0070603601280c500940d0b51076088030200d001c241f5464000c2010340e007072415190048907010042851114039828454030f114a00070440e0400c062901c04030042c1d4003400350510881d00c0c016a203485e0350322032000800ba00c1c1000c98441c1c2e03405040104003425052034003129449a015070300894039485500e4101c03010001c002d490380381f01c1d40d190803140408006400c04002c5074026040650002508010032001c0e6080ca034440c001c10811850070098241e452002c1c000d036500501455042c102c800b000c022002241940702c540c15003010140b841c031580c0159010001c0c01091400304034514000000c50000d11462039020240b0401d200014000d0f55070102c28005820200f0540d03486660703918000d0404d0185014607183d40c09550000f180364100010032a045034282080d03900c11151503c14413104d80e014082d100f480020031510036002200c1008100d0051043c0500003a040011400080440c1c0c0c01030712003a1302d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 21063171 1250 21061921 21061949
    0x90103020a060305040c0302040507030e07050f010f0807020c091914010501050906090301090f05060402030607020604080301031e0501060803030907060503010f060f05130f06090b120703020306011103070b01030c 93
    0x240e150700c688030064039000e007000111601c0e24104000400c106600080d40326080034104145240c2c16001032003c014800c5c11100040c2c0c48000f0014582013454000740040c40c604004110a445004100e40280d064015103101094150100b0100f9500b2100f4102401081000d140188600c1c07240c4005001503450001943d410400003e0161080400c0540300321004074002e42d0300d170340a5101d10a65588405800c000205901d4500c0d1103010444003603119014000000d4141400442e040e4403455000d9203451442c0c0c2541e03038000d2120403c481103081d405801d8010710000d0000d10805000c0c00300c4c0c10045480e480d0403499a0b00c2c140d0550403500821205000401961021200c24420703a842c078100242900181403040380c2e1401014941000f02c00300540c000b8642421402c1d500c143d404595a030600e03039890700c4c4500042d202d0041d9540d907070701e86007001900851203517000d543c00c400d051401401260100041a1440d00107142c1990f0890409004000708103482ca20440100440c08282035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 21064421 1250 21063171 21063173
    0x161a0307080606070f0c0e361906050901050105010813020402070f081201030b0105040b0607260d05010501140703020606090402030f01060834140402070b0a05180f1f0e010c020a03020c090103 84
    0x423000d60065050b00704074008a074115000b01c1408200f10042c0d1401100e401c404407810998080c0800b5618107620b13528250002c2441d51084d4055445000b01a501c0322800c801c03070303080c00000d40c40300e00255591685441c4602c00100b68000405401c9001804554103506500300400740c3710040e417102c0c3c031131846e08107080c0150700d51809540c034041d00030f156a099812010b0040e5040c03040c41c0e02d0982081d80011b401e0b00d2401840e8000390694600ba69100102007610703014112034071850402402603031101d00003030703198644400c400e980a803018003941d0560074448a004e0940d41e0760f80005040e40c101105e00184007509180c6102c080c008074800d00c40901c0844003100840c9050302401d40e0f01e00304268007205507203c0750102c40c44c2690183c1e090900349007250001c0020102903400d0000b4503413505040d020000009640441501141c01a02002c0701d4200c510340045131103007405c900c2c40e40f01c0d281d0b41006031080c411120880303c250003800c0381354403501d002820f000c4407000842c03145c001500140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 21065671 1250 21064421 21064471
    0x50703030f051e0a06051207180501050109030807030210020d09170721030b0d030804031209020913051207030c0b18031b010e0f161a0307080606070f0c0e 68
    0x110950720b11043c0d20800d529038a007018090001c1790009904200300003032483c0005400100802100c50700024801000341c3c0111850940b0020300c607050001d07070020702c244042100400108a11407003401124031107880c110292099801c884800382049981e94103040c24800c11441034800d01c84111003051078541c0c02d9640800b00750a0700b01065000380c038006c000d840f49019a0101e4a04d04005103442c0c00c0f03840c00c0c070300246003d400311422800603502c0c6218039101e2049004003807441d0ba00038070284d995550004c9001031420400c90030340f16031040c80f80c03607801160401c00910540d4082c0d99000340c0c0615a0400c9905c100c4050000c904101240d65507080d01a004410f403002c9800380e41c0ea520340c040c4614074450240070481580c100300d00030b00802640c4e00e5000a44d00403000100d240340c3c0314441c0c1e079040519520f41b02e61140031036842d0030800908000e1150079420740c0000300819031818108940c48054450f09a8035040701c103900a0f080030300551410240059100d004001802c05803000f1102c48 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 21066921 1250 21065671 21065701
    0x306080f070b03220b04050102040609050f0307050105030601120e030304061b0206010909020105040314010e01050106020307020a0e04030903080708032202011d1203120a0b090601020316060605060703050703030f05 94
    0x4c4820114150501502000c060b0a44241038208643e81003508250520300c2c001e601500c10301001c5100002c0010703660400c201d440300c15400080181c481e10740750400668042d48001d0255040062074401501121414030403d04000440001035407203160034070b4614115920140540800e031004013207405039503030005070141902d0001e14080f540314681d10042e620341c0610381008150480d9109010418441588446c010240034802404140d984460681c0ca0348a207a1020f5001042c102d003d10030800c0404850303801501c2483c0c0740100e02c0c3d503074450071a2600088000c030b075004000420301c0701c3c0c02e032030225564070225074880003143c84009074000781c20040382038440da06091055070900d01c269210501f5291000104090700c0d40e0b00b081c80c1000e81e80031350440e001070303c141c80d0100b103440f6402c10751503951284c141a0011464002c1800d802050410b10140031275941e0745074580459280c5400d070140428034882e0b1145900c40c0c0107444c01405407810b8000200e82246803108019260405900f1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 21068171 1250 21066921 21066931
    0x4020d08091807080708010608091005060303041203050705060f100608060f0a14090108060403050f0309070308120103151104090e0307060c0908060c091005090616030306080f070b03 80
    0x80540e5070080740082a280450308000b9820b1400072010001641d410440440c81000541e035180c2042c2e1b00c852054420000c1900c40c000300d40d1000f5a050002d41150340000c0e084000101120f0805584202c0d2586801c1c1c02201180040d1000c0ba071442001020010650000112a031813121403500e81101d1807054214440c680802240c00c02003034298030740d2290700c068a0740c050102c2d5003503a1140c2c00581034103103412020b400346810000000f01c000e4042012406268142d9660b85810007104a41c0701c140c00140840d8080d014080b800000264100000c0628446080781401e4542c5142001d20007103104e07190900d0140e0500480300c40da803d40c00c0c00c035030075142c000400041e03d685100b1264a1400384500041c00d0b640380c41144c015040d040000740049403851401c0350303280c0e039800e00c1014080c09410f64098100081c0d01c2800e105070b0140c0003a20400f00d01034105410180d280130703055605401c2190a90210740d88200c1449810002d000c0315950026070030040641e149001d8850b030542c840242 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 21069421 1250 21068171 21068183
    0xa03081e1809130b01080c10110c090612100c03050108150403050f0d060807080c01110a03210c18050102120414030a02030303010312120c1e090b04090e0708030304020d 74
    0x100040442c0703555a6101e58044c0c201c940802e1035038590501e00c0d6034062010b40039118103003a4921040300781c800c4844101401880010b0308007140d442041c841001c9001e00303941d03403200c440c0940018aa400300144484456003440105001c101000064116072040c0c20141c480d40040002070a83c522139040341d84c000e076151400f10307076031034900340c0c540c07118018035014141c8a810b003d80040d11040c001814010b40c1c801c0404e4801c1c103e2503100640d00e042684d1300d0700d00141c1061000c000400c0c02680c00e00c403542041d0309a174034802c0f8a0004101200c031100007410110301c0800501045001c004507110240c0340030300003040c0401409075000300c030740078a2064441c0c0e040365011204151300c0034000e00e05d0003070b80501141e441e03585a00e00203004107003082c04540002c401071480000d580f21030086031449d403840c2d11401d10342920b02c440d2510f07a08034075056034284401c3c0100084c11040b01c8000340010144002c002070700e090f00c03820480c03d040305a80321042d142c0c802c0c0240300c0560380ba540c214040551101c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 21070671 1250 21069421 21069439
    0x40b010504060c1716050703020f040e10020f16050f07060807140f12280207020904140a0210050a02070e16050715050c03090d0201091106090f0a03081e18 68
    0x2044001041c070607005c4000b04007440b482502c0c208000014000240d070301c00c80e03810b80010748100601084902d0301da8620034943c4071101d40305a03c00164020600f5100c0201060b10b0200c000c0256401e0b0030400360304542590104182401c1850b05000e80307000b0b410685000451b0b03043c404802800100250070348580400e00044205240013040c0442c0c1044c15400310042d0149400c0c911903000403444807292059203031311004035005100c64401c03184c001e98014090880c1d500c940c5c540380c00203041e11031030031490b1050601e200c002d42e40e0a64070201070380080e600c640c4c2c2c0e035003441d0000b42401226030040908401b20b0043c40640100c91f01c1c2a182c00d00180b8100d41c40701090300b082e00d10903030b040300c0390341000d4a0708050109469090004600c1078400710300701d440c0c2e0b00042504034225011303928064110100d023510012245000c5008041001c001452507040d5240040081c11803101c2d1b50040f1080c0c24002200d01d101c110142c250b10013a04203018240c01d21485090307102e0a22081101903214200e11 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 21071921 1250 21070671 21070703
    0x51905070b09060709060201020c030307050a050c12030a11040807030803060303040b03070c12020a0c09110d0203010e0906061507020405180a06060302040b0a06090302040b0307030b04060605040b010504060c 91
    0x24015a103000d5000403180e44682030440704140c564a080c1c840d04001519290f021890b24014004c0314404c001c90001107145564601c000c543c2500010000d20420104000801d158002001401e800b103100c00100303903a905081003420308071400e001c00c44031110030038070040204200101d02102240d030071601c0b95549a45e582c0000303055114a030041f80007a01c0c003100744010140e2161132104403d10a80d4403540f8404002c1d010303a81c882020b1001007141e000c80c102404810040d4000010000b00508580d081ca40050411b8060340c000760040e01c84034502900b0081850b81c200301c101e40111095078035140c0c0c424201c00c85180d900c52100c001e40115103070400304d4498022400103c5000720190b05407018200705162500160019100580c8602d0400503050707418a0000c004504442003511903402c0316245a09004c040c00c01002c0703240d0325004000c03001000c01d0510001c140b10b54411000003032800c0c00c21040004a42007101800e042007820b10090003a990414586c01c580c507001501c0c092032000f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 21073171 1250 21071921 21071927
    0x31a04020103020909070c0201020c090c0307030e191115030403021b0a030606080a0303060f080a060b03010905030f031006030504030e09100b0c0d030605090606091002010906180302010507030c0519 87
    0x1380090140c100250000f000340059219800d00120b500c02d038240d500d409040d0302013260040080e503090080500400108141c98040e5122700080c010760000c0d101e221001d42c1e90310804c005001c00c01d44a8428000318a03625141c015000403101003220341c0300c1d04505080e24003c0d600d9015400303117003c9206140d1548441d40d41d448015004507401030060000e6600c0e000721513111100003030110003090034507001242100b106180b260583e0b14850092030501480d031030f0070002d003403d92a42e98042d50b0350510040030810038001000d0700410804415942c3c1455415850041d002d540400100351500044c00006075000d0481c281c1803908403030020641c0c40342220707038203100e419601c03141c10352400080442035405d01044d030034009001c07600c5c100215a611810300c0200241159807641c418400c11581c850f501e000c12080d84040000e00c00094002001d90b40e8004031040d08014401401c143e00396101010707824014903500100d40e103400c1c07040c031001c5170028010340200104000240e425000d91000144 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 21074421 1250 21073171 21073177
    0x312050915040f230d11030f010524060f160309060306030206030106030e100c11070509010503030f131e090b0d0f08180409110414010602030f030604060815070306050406031a0402010302 82
    0x81c02000119841e0759446c2c0f4150362111410b00a029028416194040e0390040c03042c10701ca501c0500d000f041c440c503408003004a4240c40c920f2036038442d8060080d058203402000c0503051000381080c08294541a13810060326004982c2d001004044c241030050005844403019241100c510741004901c2000e80310403030741068800c600410302c1c43e10b46182104080d078019401d24458001c40290341d9982d44800030300860700424020140c0640c0104a0000300c04074580c02080351000b0301410b4051103454070348006998003001c024840041c404181441140070a100390b594030541190b81c2400c2152070fa5444c2400d5600c1a0060301c91080402d14602c4400d403000f000c0804103006104004507007140c0741111441e040f0040c03c50085280c56116040a0078540301c25059071102e40040d420184040070510352544005c04903034120707490300c0700000c1d4080c082028103500c03540c145e4810000d151044d402022a0320301e41c8000e01c10740c10144100701250402c00e0311440d04840348008107040e503032800103a000e84 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 21075671 1250 21074421 21074489
    0x40504050406090b060f1f0302070506070206010305010507030b01200f03040605120105060a0c0b0709050604030609030e010905010c031b0f0503031b18040c090312050915040f 77
    0x40d00308410401000b00c190300400344603100e502500440c0d1601740503c42540c101700c10181d080300100e01580d01c075095248218990101601c0c0151405619684050130300405035244405a40240d0040c02040350038010b0a5001c0c145103000c1004055820008203840d0b20034017418004d00340c201d4001c541540030701080c1c803c0b010030701c1140c0d038030f80d40c85000901d207500c1481c10a59410038203001103183d207403500845840b00d86640e40d11035500941d8071182491840600580300f80000c05a0000700b41d11018040c1006500895002804070190700300a46418141c3c40807a04000e902082440640c0c6c016000d4035a10742c00d490103010701e00f00324240341107000b014440503010390f1003903403001e08110b00000154400c28880582e18005c10007240c21a6190003200407606103100d43c208000b0702801d00d98442c520708086072030640c03581c550b20b44481c0f01081000c2151b10000e20f00180f0f5402c682080b02004009a40d0310b114a894103190428120031000103004641000036040c0000048000650190103c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 21076921 1250 21075671 21075679
    0x80f04020a03050613020f040e060105190e04060c0e0103060501020d0c0302010e03040b0712020604031209110d0602030a06080c150912030d020703090e061008060105120406060303090e040c0b07080405 88
    0x9405e1804500011403145001284100303000180b6101e58207013406442585048900140aa81d0a000c2000482280540301c0c11011403000750000d11500f0035040d060040c0e0081034000760801e07500c0300c014444000000060305060504004205c280d81c002034420305040c01e0b1506410a180500e012809024180180d101c184800700700800c242c00350320010b008040c8036954445412940d00c4060343c48007801c40300074010500301d64801901c50040d80200c401c441c8a8188504091040c0e00018070900426100365800307079020082149002d41031080e00007500101004100741480c0100045840c840c40c084107250007000302c0e0394070454440d000d01451103140301041d6502d030b21048a2810081d00000c0c02500040e030005000600c0c00c00a602c03050150601805120341038410200940721349030064001d40c1040700400095203900c0403003000600071485503602244292560500a03d802c4254102c200e00150600c18403001034100c0203600d048400351a40603403200140e00b4209014095603200c5900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 21078171 1250 21076921 21076933
    0x30b06090a061809060f090501080706020307290403030b0f0402070b0402040e0c0a060201290d02010e13060b190e01080f040c050604030809151c0504081303150c02010c080f04020a0305 81
    0x2403641440b06c040700382d0740d90b014100010703a614240541e07950420311444015070020065031011454003451680c00c807105410350380b034400800c1105420403000f02c0707054000a641e030300311070304620340b88a1500c00704030202d0b415410018103480e6018200ba006e00024415950389816415404c000d0064040ca4003004140d00c200540e1064080d010741804002081111041e00d0a440d441403c48440100035001801c031080c2c584940e80191990307550b0002c103d500c025180c00031038400185008501c00f41c1910480f0617250403075a107048142e00c24034103004040c85103d1314541c1083c2d03442400503a1004a05200f001e00b5211400c04403100380c00c0390041904200b0016010007804210700092698081c10340d4044175000c00b00741801103030300403414150110884e0011205802411b5041250404d0085081c1454541000c0b50341040083e6a1710032154100040849070142545101d50904d44000b40020b20440e519184014180307403008000004103000341000c1000d646500c41c8050140d0f502c0b90840745 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 21079421 1250 21078171 21078179
    0xa02031b0f090909010b21010b03120702060d0e031c06080606011403070314070815010806150a030b18060112020408211204030e100207180203040203030c100507030b06090a06180906 80
    0xf5800001e03030020312032341c208000400076080000301c4981c020080c08002e4101071b80e560800009600174020040b5076500c0309440464003030284014880c4035046503145180e500e00d851104240c070034a034040951908080304024080e40c00191a00c41c040c0301c417207000d44d01d588170241940101200b2020200c0e45420030704101400740c1010b040c601400b04075a04001010300c8000464080d0003c07207060f50842000d030780700b4070b845540401420608555040100d400c000103030203c0d4180e0b2084200715100000042403014558010b4101c070804200343d48190300d06030801c1c0132955a112440d0a05070402605050041c1045c4213409803a01009942068856410300d42002019032185201040c031826070083c0c001c6509000090480031600841e43e00c0814005820600e0000c0d0001417042e6050b01080280c3c1d09909024000045900c80300140001c0300c2c105410000c040307440c4c2e440e00c2405144104560000c660310f801940c021a04c961520958240d4142c6e2100d1011a99603c84000d081c14000045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 21080671 1250 21079421 21079459
    0x1009030509120303060d12020c060c030a170108071206021c06090608010e060105100509060406080a0b010918150506160b060a150c0501090b0a02031b0f090909010b 72
    0x31610341c50448008500407001e50409072244015107401c0d900c100c2e4007040e100003555480c040c00e02654640180d4000083d60b401140e0550321021010750fa81c0c00005895984a800807519810b0b5841401000c00703947c142041e1507600c0c0700b0b901aa140c29255103201d41c08200c9142c0403100303081507030380c0000003180c1d00d2140300c405042e080c01030f485180d090000c04102c0040500c20000400c2d2508020504e691030481480a0114400030003410404102b02044081d190107000f000140100d644449041c03030218408002c594441239580e04128100c0703020800b03030704a02182000c05100000004194a0040b81c01c81001c58a50245401c0000407607020444900e1034201e060a6002d004801243da80b82c0d810480503808a00400780401c0c003108a07010014803d492800c00d00c1d1180d0000103514407541c03180303008000c0403140e00c500c81d034000003006a0f1040b20f091407000c1401400c03059042540ca00b880500502440d078130107000380025000600f05410941140032804c1c2c0140c03190030000c014000c65 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 21081921 1250 21080671 21080677
    0xc1002010902090a0209010c1401020c010c02030a0806030d0804060b0a050411040501020118050a080c0109080304060603030e15030c09040906060914090705010f05070f120203090a091103010603090510090305 91
    0x3a8030a65038000001c613400d0142c000c84010f0300c0c0594610140310030940e64852a52030342d812800d402e40d03082c0441302c3c0e0444244510502c070360f0301d03400840c0c4955100000500031171009203094081e81000030440121030304043c0c910341055200c1c0b40800d448120708003041c08480e042d072281d0392103814841030b100619000300081042e1842a0300034005c2d0b5617075080e1a800942810002401d44e88030018120100b9800702c00382034100c0d125030011800c09065128070b055500181d0341617070050341e501002c1003090340002c0070100903d4143d410004c40b10b035801c10000c00740002440003000020014001b2016511a48244900c070752120707041104039222000000140030704010000d100d0000404a480140c0c00124001103500580d5000b00c9060a44011185034110071403c0724014003084901c0c001aa44d440314401c4180da550040d40ca4882e101c2c00c000c282e04503644176168461500011801c520003080469040d0362043c01c0120700c0f40502d1411525215070b50700180c851071310b00900c001c00c0541c80802 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 21083171 1250 21081921 21081923
    0xc03120301060306061107030f0c0b120a0605120c04050601020705060309030a0e1507031202070503030711010c110a080c0a15050a060504050105010c1401020405030a060207050601080f1504050c10020109 89
    0x3c20001035480c0c2d10241c414030402c182503005948050000c00024900c585032580c440e00c10141411125500d260f000d280f6000000744107030741c0e0700900c10002c112035240314400080404a40c852859110b50380f001c2e03100d40102c61f00c02d0003182c5800c00944164001c10202c402880041d107400d5a84c9450748036507440703402030b01280d000038054024a105c24541011580e1800d101c1c40340192505d207040d90266965101105085101c9030203003c03000201d00c081c00030b90300c501401e41710091211880300c0c2850845201645010520404084103480b00c1c0300001e0b01c0490f40e6109800907a91f40041d91b1151904a0140006121254580c0710900d091401e820040c09004015424440552154100026142e0902810740080c07068035004000c204004840e0703210f1060407000510301034860000c030b42403803030f41c007025941c16030005000f40070000704124140c014403080c1c0c090420719103e265440c0d00c074204040c0402040a1a070080382c14004140500c175203600c4010180c000d80c1c060810082e020b0800c101b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 21084421 1250 21083171 21083177
    0x702011d0105100b0702011e02010b0a0303020d14180d02030a121d1806090403030b040606030605010e031b19120b0906090d2c0306010f030b13150c020c0312030106 72
    0x140042c4204c88103040d1102c199050710707002140c56007a10500329240c51620380d4802c5640b0391072031440c25196600d0560246000303901900045501c0705010f080103e43c5038080c2125401000030010b11140f0680d140540501100d51030780510903400001c3c070344050b1000140600d803c03401304100795508505554543c03140d9880240300399602c1410004c21101820700c00190f5405100000c9d0345140080d80706620030302c641070028030b2400880c041000c5428035000407020a50741c00051026603000641d1801c940b00803401402c20406004829500041c00078025000718003502c0e4541f015610005e030000075100248198010350000d05103003071110000e881045031400742c030740030070400c2c0004500c0030b002d04200e886001480f41d04003036000c413010b400e04e240b402c4d14061307107201603480d90188142c0c1d00078052500408901800c43c00c1540d200040a801151108101140e10000641120445003641380c0c01c140001e03040c601d6541613044c04640d050b507a60501801005c044018130500c081d40c16104940c1d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 21085671 1250 21084421 21084451
    0x90204031e0b0109050403050c010501091d160e040f1b030201030506040905060f180709020d0b01021603020409020d12030e07050d030504030b0903040b03010303020c03060a0504030e04050702011d0105 88
    0x24003000e4034004403801c06420555410010b01409034980c0045410a1183c03130071500c0c2254105106085900a0b042030300c00c80d8071844d00e03a000c1009800718807008a61000a010540c580c042c601e42c0807030680c1725a0000713400f650300080a200c006501c1c1c40c03245400c03400f00e9500c24100484840e0540b41c5000490110340380002188807410280700d88000158440e00a00303250706c2e84009540c0d00c00000300440c0d094541b400c0c003d03110311014400c0030001d003030035840542c0340c1e90007200030320545240c000c071141154418810b055130405404024400c8940664000034543c3c03550021861080d051038001e404844501d5441500c80d83c1944006008580002580c007100d8940d4100002d41c041c0d00b00203400210103200c00d001055103004031a412803000f508880c136055940394004080c0e08240d10075400350300b1064526000d4101405415801280c2040400c003500c0c0a6401a00e480074446406001d2591b40f80080d002c94000d41c4407190b01da140d6402d84000802c075415280c00b070942142c1c03d000c202c1c0c42c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 21086921 1250 21085671 21085703
    0x213050403120509030d0b2b051c081803040e090a15050903070b09030904110a03050a0203010e0106050c010b13060f051f0503040507120c060e0d0305180105040b0409020403 76
    0x83c41a01d0244010802440c6090301d005c4038600030f4070004c0c94050707010340081c05a0b18007a400a10701c3c0518250b620f18024640d613141045800e04417a02c480900c3d038002e400c80a44140c2d4024081603020286141f44203c1e2200c0110b02c03407860095030400d0300d103038007500144200100d0015444110b03c1c418504e50007000c0c0100000c50586206480300000c55005224090002c0d074101040381d0706c11113210449090200c04c2c0001406c0e11821005480b880340006114004241d00d8060a039100b50000c80540c5503500d0a080e0081a020500c104002c00901013070001444e80c3c00c0d0000360754850000c0c80c400000f42415030103c000d0902d80307d03640d04200301800010b05405c1425504000c85815008003805440d84078043c0d42a0744010022139160185071400f04008801c103081c41a094050240311500d10304101014041c40c161070340341d81c4540f514a6050001070f40c4542114541c50951030a0030f2048880340c01621180640c1c5c100d04880200400c3c0403942d0061f580c041c004580c084c1c203141e01c1c090a8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 21088171 1250 21086921 21086957
    0x1f0209091506031b090402160203060a050402030c010e0d0b07090f0806130b0414010207030203070606060e13110904020408010c14031504021c050403020a0c060224060103090213050403 81
    0x103881c402d4101600b48000f42c4401d0ba0180803103882c40c4403280e0146003002500015040360b014a101201c14050b44104500390300f0108007003a03200e04504020001402c080c0c000a030340d0490078800074100030f11123502050b00d4950f42c02100c0ca03a58401d00c2d000755410304420142140d81240280e801d01c0b60386032800a440313200020b006005580302880b08818107482d80314080c440000800c151988005490b903001000c400344010f149807800307a4040c41d00e50f40517180620940d82a6072108040152401000c45541c0c2d6151040f405a40782200c000740070700180884840a00807031f0032503075100e4804200024001010340003501070480d15554134030074001c811585400c80c0802d440c0f40c0142907c0c8106a080e5060980c0103040e83e80b0701000e403180c0c8600c1c180b400c500ba43c1040724110010b80040c21290304112003110300c080079007410300140c840d404024045c6645e0714000d81004140c5114980400c407140d000f64071495081c0e801426000d6801c0d00311843c00048d00c03085d6400c03000201c945000504d0045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 21089421 1250 21088171 21088201
    0xa060602120f0d090222091e0203060a05190903121401060903030302070f02130b0f0a060c0803130506071707030605060403020f03160807090e0a02010503040308091f020909 76
    0x6881d0400303424402c070030724441e005040d002822a0001d4a17046c3d1200a0881031a01c28a0003003982e8000c101480c03203240c26071b80c10441034650341042c3c8418610100517900403075060f6100c3d641d00c4000506ea500c00182c0c58010b4802404883d21030310b00b41410043c103922000ca80c071540c91481050028800c034400794440b40c0320901c580320004001c04410710001c3d2290b0018002103020342040b0b95041010740004281a209002030142075568800318201c41c1040c0d140504500c200b11020310440e031404101601c10b4000100041121000000098500c20345402c1101c041d41c1040458046242c02d0300301901c034584491103010522050743c0041e0030f252003806500c5c2a1100500700740e08142c5183c2c284001100601d20b07c0780c5c18002c1d01c0010112308110740c011070003000038000410303043e4070b0030387d60504a030b0024001c00e6064102100c0a80543d8005044a400543c103103070000059442042560410141c080c0c1d5404180904240d42004820754001d0404004211010944e649511103000c2d103a903 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 21090671 1250 21089421 21089437
    0x40c05041e050c0a020d08181207021003090305090f04020c01020a03150e010f060f120908040501030e0102031b0703020708030d0902010801080303060307150302090a03060e0105061203030f04020103020c01050a06060212 96
    0x42d06c601004500c2c24400e0303007c1908040411021101d40402411190a02c1400070903a1f50000d000324649003503107090003040d2444002410100240585514001c0c142d1052450403070090003040c1d2440740c1c540712a4120b4420108407070086485208110000700a40f00000e07946040e2248000d0110b90106000314035030482e150030110a108c03914100c03040e144d610a0288040a0121302e8540c060006c1d12800390312503c504c641800e0380e40314100000034088a1904000d4941a807050040100c0341601c0c5c090b80000c1034040c034001d40c44420b0303407600300e24000340c40d08060414000401c02c0b00e085e60b41c540016540c0d40c801d8131046030603a250404541d48e03000843c0d40c15031550200317200300054200700d41c8d912641c1d6243e16015140caa000c40100389507081507442242c20940d10660314240b28420b10a030741c1c00c900216a401180c0d4801070503c5d40c0c1c3e000c00f408d0700b064140460045011a8043c2e41290350b00d4039514001c0c407913440c0a0404100071310841c0f140d04054020b00140c20301c440f420300c08842c180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 21091921 1250 21090671 21090673
    0x30a05010f060c06050a020d090f150c0507140705030d030e010605010c0f02040b041518050903040303020d0e180406050406061e0e15031204060e030705090f040c05041e050c0a02 78
    0x3d1911464041c0c50050040d040c02c56081100840d20607140c010021051300400310061014030314a84031031141107411504c01d109103000034280d1030b0b03944202254182a000170302061030741450817045c1e00b80784075a070100b035240c40380c8000c00b0000c40d095040b000e4034802c541c00810a06945200640d501484070a005103141d600759805030040c40d0642c001000d48001a00000300e00e000c040b0240d9016405400c03606002c81c0e0000d08001482044c0225a0f00c086100061820f0625558010b50307140c5a40d00380006100e0900e620103501c2c3c90342c0200004c000c40701d01008406040506050000b880182ca058400c5820808040358070407500c1000d990485038110a20540ea1030481403900c803d038043c020084541603852840c4440e902003200a00302110303040c0b410b6640c2e16108000c0c2c40d1203500e002c0d842c040e03001098100225030b15400b42a5025400c40341042c010394603843c0201c5140e005422455003e4504110380b92204d200303005052141c01000010801740e10380c01c9031480d60f0b0050030040001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 21093171 1250 21091921 21091937
    0xf070b090f04020310081906060503011104060c1a0a090b1003020a17010e0a0602040503060f01060504031203151404060e090601150216080d1202180108060d06020f030a05010f06 78
    0x40d0705080d80210340c0050f441260a040540700c2c110a81025000c024080007078030700c151f031041440310074451070b4000c00c0110000c00529180c00c410304602c1c0601e20034402402500042c0030244181104a14242c03452403448682914002e20742400038a019007090740c4d00700410340010000c1c140440b290054031740041041604e10b20705078106207051401545540a5526922016900042000210003140c030440016842d5414081498903040c0f000300f10303e8003510a075004102c1d20b901301081f07800b500e0704400200c1d00411002c105a02804803016641582d0884a40020b00710891034106090714404447c24015103079036250f243c07a007140035100604942c0200c40104a0196240111701416100d80184c031904041501c002c034031901181e200e580e20b600300d0000440c4e92a400304501d008085840e2046050107110f90520010600e0420442c0c103000016000c90080c1d940c94022060050780000155940c6440400c40f48540c4c1040da4912411420800089040510215580300383d41b07565407000c0c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 21094421 1250 21093171 21093199
    0x3030e0d12020c01020708270307031205160f0b010303080604021309022a030421110d0201050d0c05040e1806070302070611040801020c0607050a0f2006090f070b09 72
    0xd40c4215010f1103299030070050072000800030000742c03a00076481c44050808200365a11259600711a00c841c92094124081c01d100140e2400d01c881800c0e0740600c0c0191310340c007000b2081c0345010072500014110050008441c000c00149220960603039120b561031450340d49441007800305a000f4640c103450036045000f428490307a8219030240c03054000841001201140c0c0d4010b140c40800e48161805550700009070500608403440c1d4080407000010050004a2440d80c80d4031601886180301d03144100002c550b854150380c4554261014207404450400171030350704103005001a4824802d1050007650000010044003c20980003031141c103081c050035695640b48401c8000f503000160461380e5540e103580926400b00c03800041c00281c0443c10006036140c46000d0010315110700200000c0c00c00c2010070892490941c4075600300000039460401d0481c4c014500c54203001c07074040801d40c0d1000d200301003c011b40ca140c0001c03400b0741c0310142c40565806d0354a502210810388103e190315a080715444045c04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 21095671 1250 21094421 21094457
    0xf030807050c060406090306051b070b10030b0a0c1704020303031603020d0c05030a0b0a080309040c0309021f0f020f03040e04050f060c0d240902090a0f0e010303030e0d 74
    0x1403124454001d503a8061181c0001450740c0c0c105401c540001028a8010701c04c00200e44105c9030001c8001d201c124151400d0140f02c0340c5403003951401000c0d81c0104021a600142901610000c1c40e0700054141e62841c1503401c000091120355907080011301101026840d208079000b1107405103802401a5182d80d41d40d180d20441160500c0424040681c00c101c940d0194071385104607000d4000c42c1c0c2d6001c1d500e0614100640c15a0079005036035104803045601080b40d03070000000c441c10003000b591701040c420070303110080d00203220b0f42c0c1001e50450f00340706ca6000c5003142c2e4442000040d6031611440c40810214600300c3c1d9a800d60400c03440d0607071041209020032007480e1000d50307022f84207070111503100d051074002900b81481510850040c071008a03080ca6090b15500a8004241c070043c1203040e00d4010f6000c4448005140c4925420180d002880104985900c402030002d440240c0c2240d0403543d41e15408050755100340b1080c0c0c0043d203080c1ca00e181c00b400102e042c40c1e00e4880342c0c0e204860004d000c1400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 21096921 1250 21095671 21095677
    0x6070605090f0313140301020c0c1c0609110406080d02030406080402060f0a030501050901050609010801180b0915040f090b1602010f0609020306030f0706080708060a051c03020d02070f0308 83
    0x164498412412007a0340b0203070800091000c04c1c80000c01c500404d103440308070848a00d984854502c00e03401070100603080e400000300c550401c2d0003210011080310b020000a0740250003c007001c0d00c01414480341000b40b0005030703880707041c054090b581000155a10147c03540c032070000c000703c90700580080000300442489166090b4000b4001012a46050384500c91550258485012240440d0300c0341c004005628100609038014001038801c103140480c02c10000342010414040d8061800320b150884146242c20380c05903042c1c0300040c2007850a81442d40701c1c49042d044100085208a04003100c1d4042d800141c01500030075a80100c800c415500c40b1492204004e0000910500315940d6401071607400c1c034203000d61001080f02c41c0380180c2e03030f0a08005141c204450820300895680c4a002c0130428190f024001d0740c0c0c04040c0303282002507a2260000185841026031009074000d525030505401c9401500c1c41d203414030300c41d030220703050001c0040c01070342c581d0000d209620000b0000001080862461001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 21098171 1250 21096921 21096931
    0x120a0504060f0f0b01090602030f1209030f040308040305060109092001020f1c12020705120a110d0306060809010e0c100314040b0f01060512060f0402070203011118090606070605 78
    0x1000c242605042e5011040b120baa8420007002900d514006105580120380e01d400f5044030710103986003030300c000742288807407080141001040c001d200001d844e4020500542d40c0c0280304000705941d5543d01c0c10500b0494000340000d40342070086800005100a2a1280303041c0750f079201c3c94203030810300300f801d010307101214629815040d40030f0007021013120308080c000c01080c040784135402061003000c03500c018058001c883ca00c4d140184108020404507100007201304940c01070044242e900c01d1040400c0300c049850351304800c00c522442d6a0445019010307044001030b1005647c5c0c030101a542c030340344e0601380c8800702d6070214039401c03103008104282000e050803010300500b410702091071721035101c98109101d82203605441d00c1494205105a41d03028800b01c5006261a1500b581840d0000580d0449248090182d9208a0b403503042c031111501c9903010f5800440c0c0060003040344d4059882c80d92030652003500c2d03070380450311404464a51450300140035402854041c00d00380c200b0006550740002060041c3c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 21099421 1250 21098171 21098183
    0x1080c070b04062306062d0d02030f09030a080106030b04021c0c020c0306070e010f0c05011406100504030302030403080d06080a08120109050402030309090a06050307061d030102120a0504 82
    0x8000320200e80d001c01603a00851094000280d54200c2c0354183c0807208003e000342c049405103c080c010306950702c20945010010103680d036044500e000941d03202546a1620724001c5200106003001c0a004d140d000d07500c01c1c032456160718220390302c550b2940d07107920982d0204c9021a21500042c00407a00c2a0b001221044025000524240026a00e8024010f0f4203014022040e02c0e41c1124039010750600c0b4042c01c0f243c1c250b005108038100880c01521446010900364100480c1080320a0340314420340480300a590410000c00403480c1c103c4040410400850704540038088450760f514200381324008903012a038040d0701071070900341507a5070000142d008550303e43c606519184042400c020070f101140c140d910680540d59607035060400a400300341c1c140d0000403502d14200c104405600d0210480d05e80d8001104c008240303a6414010400508032500125051311540d400412b14640101402c00351080d02c0d90181c05003c0b03036000b0503080c3d00c140035146400b002c1c1078022852050725030b000150800d200d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 21100671 1250 21099421 21099427
    0x5090403080c0f040909060b0a080601060e0d08030906040209010b03100b0f070b0705070b0609060d030509030708060106020d0207080d020c010c0f020402031003020405060a0b030705090f030a030c0c0b071101080c 93
    0x2050f004443c0d08690401c0e51318a5503418404100400342c0f149920100e800da0308070701440c2c6407000c0541c44e81c0b0148a21402d0041d081c10200d25540c440101903142d41c0e0012140d510307400c01c800b255988060031181240110b40d04000401c0580c0d401090724404d2440b031400318103007030a0110841071f6030413040103140100d0007800b080c00055055450a481003140f51340304c0781c0b030340214140350a00d14806080c55014038040f030305114098845258012a058050030055614012040440c1c0b5040b81540041410b00541001007011503000c15038842c010b0541e400c43e518142c4440e011616401049094400360f0312804004c41c955000d1008103120300d0003040c0041d26041240c0208082e6482111002c000320200034060086180a04c11603030000802c0c0d482c0d6584a080981070000da10000c1c4c841c42c1401404104409aa920301c01c887c0808100941074440c080741c41e00e4090954115480d08891500244e200401d003500d0510550304d542d0f400c5000d810110f50700e80015540307107501038001e0507902420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 21101921 1250 21100671 21100687
    0xf050703080901090f03020a0504020702010512070201020d11180913051501090f020309060f090304080307050303040c05012a2d030e030c010905040b0301180f050c010905090403080c 80
    0x5004500056005000d070300d903030300390708030004140300c14a402c514103200030741d10b0620140e1241242841551020344006a0380e05072400140c0ea81d008546111540302251020032503607035130640240406480650062081c0390a80c5200d0003103000341a00141c2d40c03815640b61415500d09900305075000888000e40d03a500215035140c4a040660000504202d110300b5801045014003510076038001108140b170440c19403c4c0003002c01e031254800b82c00e80c421641e500340420034882c0c0c03c0c4101c400801c0e0650849036529000d01c1c00ea9103d80088909581c11328281500080650044180000c5620741501c0347e40261b808540c14100c03c203081760240d070150810115012505080e1049201480c1c0441c20b02c00105400d05e001007250b48480d51300c41c001d401650710040c080c0d0f0040074000603201c04940102c2d842d0001e0021030300400c00741d000006c400039544148002d01901d00348510300240110103440d00e20040c00019505c0d4515481030a400c01030200c0041d0109100d00b82840c0c1003c00030900510b09594 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 21103171 1250 21101921 21101923
    0x2040c0302070206130602070b0301030b0f090c10030506040e03030108101e0c0e10110a0204020c01110318060702060609060904032001020d050109060f0506030a1806050105040c0c1e0f05 82
    0x1156610301146170010005005d52038041210750000c20280d440985550705656851843e050040c0802d015000e81d00e0108101d00300c240080b8010300c8000e41034950480004030010040c203800d481060145140910500040d480402228180ca5005000704a00514401d682d001040b03086003441d14050200d008403d4400c4c28040d403202e0007016a2080c0c00d50300c407402003010704c54004426000340000c8410b01da00f8440701040600c000c170b0701244c0043e1070f10000c0d020345001d031031510364080110300000104500c6620403001000c100d101082120a50380e100201a60f0719801030b291240d100f5010000a25585041c5500b0b40d40f05129140c125007604421403c6103588040c00060007140e5004207012260b4140e0744a60340c0142030f266018000d061030702c1d070008040c45140c0100c0c1e01840d00080080da80001940260019403540c1d0100005c132000c5003080c50040500303000300d07841942000035112896110f014155001c503000001074120801111030824222000001141c080002000300340c04194 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 21104421 1250 21103171 21103177
    0x3080a0813170301051801030203060c0a09030506091e061e04020d0209190c0212070210022a01080603010507090b0a02010e160302090603060412030513050109050c01080604110702040c0302070206 86
    0xb0800825900c03541007004000c4460281958854245210401040942d5000510030307048105010595501e01e100d49044400d6038094001618510828042c011420310000761380098044810710b0380007443e441401151204002d5948a2101c40e084604041c800d00380b908054020348010b05c00104e58002c4e50200b410081d0484104c0388520700b030806901e003804079024000c804803a92000d801c642202c0b4440751320300e003c1d1440107030207910b038918540707040e5000300a000e00c1c600803543d006d0704110a00c980540c5d118509440c06002800190120304a810f0500900e809448541c651120042c1010200c003169000075046004642d2540c0001003049014032412142d03940001c5e410110350706600602c9441a0043c00d005d000b9800300c0b080002041d40031806200d921003c0c0fa0110301515100d103880d048901c01007024101d5442d040200c010040d0000700d01e44107407001c1c2c9410b001952080304000c1150a140c41c11880701504105540c01032400350b001d8003000010b4100141086429008104150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 21105671 1250 21104421 21104453
    0xa03030501091b020601030813050a03080702010201060603050c030a11220302040b0105040518071e020a05070504110d09020a0b0301030c17030702010903060905070b03190b03010603080a0813 84
    0x35038400041c40894058000c050940c000d010a18001041c0300c800203588050510015000500c0840c03001c2000002c1070008005107001072040080f9501ca080041007640403d0040340950700e050b03c0055614064026a07100e100c2c003000d007a056603a0100c06001030030104000780860141007208500d54034801d082c100d0100c0091030120500c90440c030520048401100f149414004140000c000f25590301101c60310300d100c1e4a54070082d0f6101e5590650b403000c41c01c0a03c0481600307000c0380c0d41605500145c102c4a6034051000c4848043d51041440f00301c0d11100c5a10214100411412000c002030750010720610b813016007817402007642ca224400c141e40081c1c10480d4480d001540400110460201e40000d094803040a1072810344241d001800c8503072607100040074035495072602e40034020140103041c014800307416003035501d240400d070040e241c81a801005040390710b032410414190505103d54000d99a204846034070b00519100140c0740c40500400c18049604143c0510b8009100314203400c401d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 21106921 1250 21105671 21105677
    0x50a0210020c0d1101050105090619031502180409120c050f06041a070203030609060d02040906090501050106090b0903060106030b060d06060504060801061e03021b0102161a0f060105090f030a03 85
    0x10a00b9250007840f1013081c45030031541e80e060100520891fa60740a50300c0e0040b104585444a001044c40711102101030f9a00240c2503102031040d6511051098000305210800d03180d080100c92031000401045501c89800905447d1070082170103c80d40c0910352809065010700202da03500d45103252480d1500d68200e40c112002c002d6030300000c1c111100d10b01015004034460000d1821440e0403404180400da000f00b0351449402002141e41c1551600c1d440101016080401440000c00700c0c203003180a40400c6c1308423400104c030350300001480c10110055480595005000c0d185d00d1340f0304a4110080c141803038059038001802c006088452509104501c0141420b898454aa81c80e05001070b003080016400303502403110003c2008100342680c0d404240d1a0040d040041e03d504101020446500c180d0312480f4031580b000074a0420b602107a4080c0115620078451460407078000010308020301c3c01903441840302500c40c0301042441d03001d035001d4240410003600400c1a006100e0011f49030081885c0f0035004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 21108171 1250 21106921 21106933
    0xd090c12050d020f0307030c03140a030e0c0102010618050618010603090c050108011d0417070609060b0d0302031905070606060305190b010c020603060a0b1908091b01050a0210020c 79
    0x100002441006a0690b4074005002c01100925220f82c5a03c0b440800500b082442c1407190308040c040c840c03240798214201f00c20368a0b200e84103c00380040c21041a19002803046030a0101c6c607610500985040d504414001414002e190032404d001d080050400d96000c00c26100701001e41250341d01a9000f01f07071325540840c0c1e8503800d0400c580c5400d86900102d04101d440b00060040c000040b4440507801c080087d88103203951039041c82c801800d0746507032024044200080400078044140c004d00c01c1a4000c7d0001c011a2a034281008401d15940c4130040142c0c10074004005504581e8100c18018506410001c2c40d04015642c1d800446010780c1245021030703598400e228607810582d2044141c0008440e0420407601160000780000030700000089c8528000800075143c1d03241c800201000781815010707583c6440c4041c1c48940e40c4850f02003032000189070000060601e0f5000143d40003080d00040f804002ca02c01100115266803080380c045040d803041a0b0b0500c801142071009001c00c441c00340141c49 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 21109421 1250 21108171 21108173
    0xf1c0f03050310060305060114030414010509010606080a02090a0b0705010b041b0f18090b04060504020d02030912030115030e01020909160f02060115210603050d080105030a0b0c0d090c12 82
    0x1d2008004d8101404140c9007508105480e43c020750b2807003032001c494440d151603a07502e10301485414140b0003503007015400c01051201e0424150410f1003035542c1364840b00c4176a0366800c204001c0380246030900d40d02c6002c41e1000c0205100241c01404514014000850140d6070400424281c40713504516041d080b4141e0780340d03204a0751101c100b00c050b42e0545403e14041140040c114240d0066009509409590f50041401c0796220741c004070040002410942d1140212201e0f10025001158060b20a00130020480d030200c2c240c9046a040e214686a288c012000c4c420049004140368502c1427600d40d030170003000c002ca40d01c252817903216440c0424121610600220002d0010020810050556026200501001c10044100518030199160202800240002d0403900d0581d40180c01c03466032400c440842403003c0480d40d000b280c2000d46881425980e00e4091641d01e00d40c45002508040d000d2000c41d034251200c100628210444041c04070b0036001c02c3d00c2d140000c81c400d40c4000c080c03040240301c01d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 21110671 1250 21109421 21109441
    0x260f03060a0b120a180f05030417030301030f0609320106080313050f0a030c030b0a050601140711060d02040603020d15050a0312120204090c17060f1c0f030503 70
    0x40081c000045625080a044031025005183d01400c019a0750ba1182000307001c0c0018206030712006074000c1310f0030081c0d654604102d41c4a510074002e003070002450714a10340c2444400002c0383e040300e41c030400400f038003001500d03450010301a412080f144400c0f038150310241480944c1c15018252070300d4084051070000c02580d01e00311549980030310a550414042800c07521400d102c4c1008440d0306441102d000001e030b100190103c1c16036003005000e05241000401408000403040b4440c40e2100020062911a94019a4a04c0002080030ba06180c20800351002440701030f40f4010104025000718107010503c88444c0c1070b07802c1900300c00c1c002580440e80c00c1d03000c061400364050038500c03245224216400c100110b0070550b55400b003d4120040c0d034000424080c81612051040036040c1c20844d181d98440241d013000e49401c009820020b84070001d50008550304402c030602900005080805c3d102c40d100c2884296102c1c4102445228940d00340d00001c191004054074401e44260344041c0c1c2d9146c040802 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 21111921 1250 21110671 21110689
    0x3030605091e1b09040905010f1401031403072103270501060e010305031e07052407020d02030301140103060302030304030f1406060a0b0904020c1204050a0602010b030a260f0306 78
    0x1204100c0507402000541d002168116004d00c0340c20703140821843d000e81080b80c0541400700450400d0b40c6800b01004c0040c0902c1c079403505892140d886100012250910996240034428010f0700198054000e502c40c0f401084942c0203a00702c0e03040205603010800c04142c002c4c00f862451145241c1402500d0003003240030722409001c0c01c5800c8071050f065044d0b4441c1a0b5a000d030700424903c6c14042007038647d0441d040c90680d540d007a8820120f4086406028445190b50041c0034000c004080030b60204002c5170003c601210a00d0fa42ea005504580c45d003108500710b481207584d014140b695a420100140e01c3c18030060000c0d42c018000030501014924014002009500801d48283c01640038018141d40e00c41241c0c0031220385517072154949000720700040003031080341d0004005125000301d4280c86410040913104584042b5007003004241d444100b6401d981002540d194150081c0c080080040c02c1a0384084200454000ca690042114002840146d205204c1030b0304200d008410002185400450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 21113171 1250 21111921 21111931
    0xe06090117040605180703110405060102070e09030909010501030513030e060408060907060908070303020303131103101407390b0f06040605180613110403080d050106030905060a0903030605091e 85
    0x2044154131f151110280c03100440000c0e4810740e00d9001081544c0c2c820030081c0c000d0040030744480103070f0030f100c150560349620026099004080e03030000006c40e9030081c0300e1644542840c0e40c102040e004140d50468000c10f00c6921945d0040051001181d0700c00308000303e9200e0200d200051255170708005001c1c0110340503a000c02c8807940030750010b00c0041da000c8140c035044210003c0c041040c3d082e502d040c09180c030281480640500c0313130104140d4148002d070403000d061001c142c00c401c60354450940841b00001075003a5092881121a02040b06a0780c0b8886000b1700500003402c0d0000e5104c55655000c9401c0c1070b56052070300da02050600c0343c2850302c2e202d108010042150000000d40c1031141600c0712000c001c01252181800401d8501b41e513403d504017100f49800e96035402e036695283c4c900917585800628170710041d285418008030301503001e44503100d411a000801008140d682408110240c040040101c08042d141c0c2070001d8a900d4070902d150156032000031541030b00713102d00200781c02c038040105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 21114421 1250 21113171 21113173
    0x1d010506060c030f030a02090607050d08060603011202010507080c030403030f020606040603030807080403140d09030e060705190809091003020907020105100b1e0406030203040c150e0609011704060518 88
    0x2203050b034404000400c4442d500b400c1048a5100c3d0340720510000280124401c140e0480c000050400c1040380c0410401d18005282d121a0066140c100c01c0c800c0e03a00003402038185241008801402641c05200901009072180709898601102e000440e41907800580c02280410140b1801b80181034050003595401081560704001951550703c000300445c00161200050120700380102e014144211a041450241050341c20340ea089000010701c0100a921070580001c1c0000e10142e000d8544641104c00050f041310007010030f4802d0000001810a821500f1540440100942801c50311080e64082c070451100c070107540520702c4d5006001e640d100042c450011640f400080040484610314894142c60310004070503200e1508903614940c01c0d450070302041c0c19000114000442c13a501d50021440f862081307a10032500c540d03030200e409410f40702900700c0003ca00c250740705c55850b060a030301a000d40345051401b40340e00100f8011710705440c1c5e41030710305842090300c404c20010345450110300300307100680c400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 21115671 1250 21114421 21114427
    0x4030201022103180a020307181d07050103021303150c17060901141818010e12070305030a0f0504060f0608070b03010306020a090b03070c05010605010c080909040303020d1d01050606 80
    0x140d8082e04502c00104203151221580d03a1a0781041c0341000118403580d4090704852105446810448806c00242010081039040c2842e61200c010700076558456030700b16900800c0094108001580690401c50081e00b550148080c00004201050b8102d44005088500040c1c010440b0800034810b81c000d95903000d043e6000c03c03c0c01287d03112101c02c0c504480412a6403909100e02d03000040b00440320700d884141c0c140c400d105004051104401c901c450140840082104030706003581140c40705130408030007444510a019039000300740214011540a20b90503000140f0780000301d2510121202500e090355020b0340d801e4203c8a044c030368840c000241001c1c00091882ca4900b560b0140c1034441400020030a5030045160347d60380b4080e040c40406080c60880f03440c0c69290a5000804044001d0420340d915801c2910001d07440d4000c0c4002a012600180c1d904c2c03900b000c01c800c3c403004850150044003015400c00400460000c1032181100300b050760f03c5498902d80700c440c4410b00307484000c1d2500707210358010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 21116921 1250 21115671 21115723
    0x7090909080319020d06090e06010e010305030301060c0203030403021002030d110405030c01030915050103080a0311090105030403051303020306240a12021e03100501080118021516080c030403020102 87
    0x9601582d5003c25042c0252100c1941410302c0d10103402104034241015041140120704c0320700365044000040408001c69880e03070707a142000440c500c005e103c0588035030030400040c40621300c00d200d207250f001c1c0060100c1e0329185e41da42c003068000d0362032115480103030404201d5003c0008180500031000c01c1c0c46145c1c40c14030703080000080e10b41168403d540e05065440558000304003061070f030180003070780405040001e980c0da81480c2050381d04c158250300010740b410b850b01c404545410305441d450841a950b80d400c41d91156010798055121900710201141c03280302c00001a0b43c1008040d2140a40c003001a440c003100c00c5520403d042c061160741d02c91800f800090007540d00e01030360144200e80441da03480078068502900c1d043d51000e00c054682500415280703400c6800260013042c100c8000c10000c00080c030340c01d0850b103044421031600940c400216140c50a40a2880010304241c0e5a02208103208814603a41c3c48142d501111245045820118080040d0340e0140082460ba6400c01601d031185104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 21118171 1250 21116921 21116933
    0xb0306060607020d050111030f07030203040c032405010b0a02010b030f0606010e060d020a0822020112110c0a11030105070903030e041107020409050703051c140c0102090a0b0307090909 81
    0x2004100601502001c00c0080555488004440f0000e803c50003c202d0340f110401000701d0340e13200301c07111111500448081495284207100b2284100e0b08952480c01c05070441d035071401c44200d0b420540f5100c0801d00c6000d44414000d206030344c020b003580e0441a1b603030080000042e0271b50780e0354003180388290440c03801030b804000085a0386900500034039100414610307200c0014101e001c1d080d0484202e07031021070b8400c440c582090340640601c00021054012201400e00206030048605000b40080c903802c11b50000f40d221904600c0c003c62206031072a051040f145100ba00e0b200b803c00055031256000c420b5501a4103080c8203044d00500f180c984068080d042d5100540154002d0388403074011540c4840c1030000701d00e4002a640303500c0d070003403051243ca00b041c10155502c10050000362958010201c041030004941c81040c40c2c00941d540710310711611031141010745150031041100d08155020440c40c01103039107142200c406000b015607580d0b141c0c02c20840060403e52144c010380d10031031030803401c00c0200300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 21119421 1250 21118171 21118183
    0xe0c01031a130204030f030c0201030b060405030a030c0203010204080f0307060c0207080d0e0a0b0a030911010306060e0108040507030203031b0115031104090c0308031e0f0f040f03110d0e010e03010b03 88
    0x2074444181450b450005a40240b19991000c0c0180004006950426511030300058a0758000d0741d05004040309001004210710441c8545e40d0b041d80f18a183e440000c0c062030000003040c1c0000e0006003007995514005090451031500314109420009244080280c10f200d090340d2030540d807004054a5083c4a01703960359920a00e0702c1d005021491841c0070203690343d1807003903025022800c8426111007040102401500b02c01d035046441040f400c164140c554460700c514021654a5551695200300600041d01e060070064002ea8050152110120260300c0c03c0004081aa03580f04644035104515a031640c02c48031503014030704503880e8402080001c01d021400b0780c00304c2c050403103000515080c40e107482e00c00f031001b66200400e0b4070382c04801c000f8910760f03d9041800104040c5101c1d0076581d180810a41c0d500d008840b40f003c01c0c00c0300710208010402c0640001c00044c800c3c10210602e44800c0341d820315103d00c902c19400040d4044005a5071542e2021107061b40c400254000d104d4548001e0009440e25 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 21120671 1250 21119421 21119471
    0x308010605030c040b0a03020901030e0a020a05040f020c060408030610030e03030601030e0f07080c030106050a05060d0b010917030a0306140102120c10060b0703080705040803030105061c0f0e0c0103 87
    0x4000b00c003140c1070645030403c880082c2403c3c03900d981c1c0c400742100c000d4041c0d040140b80e94042407910502030310f02074003c68000d00143c2e0091649100c5820501000014040740e046d90b054268248100202a8001c001490280740200c1d911034607450305900304000b010360300044034101400c001310391401b400d001043e81d801c4082404c008c81d030420114012868010440b203401c4081c03203409000101d0200200d1490310180c0f01340d0007401f0283c0c51320300f4400158940d01c54a40c10000070040111100d0340c961119454601c14500550455500c031241c140d02c01841490300c041d42c01c0020107401c00398161103900c00510b036401090301841e5036100040d454058607800d4507a03207180003034141025481030000c01040c0081c003904200d01e80e1500d401c0f5015800c1180110089404000442d0180f400744058900325840f800040d80345a080905010103904103641c0c12003203643c03a40c60074540440f540680130315420040400a0b03e10914000c161800803004030716810705103484001c2004a0180b11061602 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 21121921 1250 21120671 21120677
    0x9060c020d0f14010f0b09011401030204080601090204081c050d0504141203040b0907080715030902040203040602030708150f040506030f0f16050105040e041e020901080a0201020f0102030403080106 87
    0x50006001281c14580310070001000c11815020600810581d070250300701031041040208201180880c034181103a0001d01c4807580181d40100420026000383e15041c1a02810b01d805809e0075569103a65280000c280c101d0b1100c150080350038480100d01308180c001603500001010f0268807141005807083c452051940340b030341c0e01c0f1000101030100c01118000c49040310380855001c03040904000c0d0f02500b0958045610802c5180441c07081301000400380c1c15520b1080240209034a401d04000000c1c2400d00c890050680318010743c009a41e0790700c0590b1140c1d006034405640c074a8054001801c0ca00c008004107010166010b191717120351a290760104402c0000d55002806448080c0060302e000c52500410031240716101d505006200d000c5005920202c0080c540d040e001d840b04019240c43c015030040c007544002c0301000070049861018070b0f031a184a00f803404103c8000507004210250001d80001c191680030000c0b2004550b8100400142d2500c4440211304509142d58010034281c010b01c540420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 21123171 1250 21121921 21121937
    0x60403260c03040606030507080f0f070602150403030605030105010b09010215270c060f040501080f04152c0d020c0a03050a02040e100c080f090102070b19060f120c050a060906 77
    0x1001445d600c02d0303016581190031202e2246c2e03a0843c00361780d0703009446d0505290182096124110100103420fa003600e200f034000d440300c90054179a02c84001d00080080c2d003010741b01d076000540c6440c03e1040038080c06111380400d80d81d006200c00a441d240c11700c0c0041c42201045400c01c104649103600044e2011100d070600c8226034811402103142040107581c295118100041009401c09008000d104861081c0c82d000081c0d41d4000c0d001d0390759401100c01a2000301c10780c400100401c2c041e4032211580001040d41040030940c507150082d00140c9440c0042140d20020f04440e2168040017404803209045599510b41c030b0455030fa080d2035122140000703004a407140000300384040c00388486070301d03000d015004102401842000410003c4140d0b5411803110306200400c1e180217043c0220f401ca035810002650f455251a4a00c044003d4120ba041060360f03a10b032401305050706030382c41d0800144043c0e4004021040d20b030600071150355150b40014803407805018100329058010b40201c080361124144504 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 21124421 1250 21123171 21123173
    0x7090302221103010302091006020a1b120b090c060403020310050703092108010608040201081f090212060406060c05060c091c0503030a0c03022109070e09060403260c0304 75
    0x14a07414452201c07032414181001030b01142c0b0790740d02460480b40215000751080d21044440181d1094600074a030068105c20082c0b404945000b03040c0030018004000d041c045a07503409000d5294210340740454103100805c0070302c024400100721211076000129211403505207103500081d580c03803080341490182900d41c0005846980aa4030201d0f000e80c00c19500703581d0381c01070064070304101050302c0b00d01c002c18081d10000c40d8030351003248001c2c420f55060710389280948848680500360500d4880300c0ea80070441880100d094036181c0050040e8064540c02040c07136042400c1040283d40080d0055020401c00b803031464040b400c0000c040b134000842203102982c84c00580d01003a00e42148168020b0013616003520300b800c0280c000021482880145410032141070315400441c00e92051150440c81003040b1111480c103c428801d9964002100100300d45940d6074401c1d40104a44044680c3e010640050003000140f54000e0200e00c505404158400c805190550b8107500115000e84444003001021000030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 21125671 1250 21124421 21124459
    0x304030609050709020403050a1a0f0a050a0e1902040515010c12050903030412030813080a0f0e0d050a0201141903020706090204050901060518010302090a0207080409090312060e07090302 82
    0x800134051039036080d07698940702c0c01d0442ea1031958480c225050001031a00140703103e180d00d000c0f406012210a48000c507210b820350310f4003521001d441d10000a07540d0400a1010804100c230b00468031040709403406210040c0108011188005c09203000c002c10f076240c4185a0b0781c0200c0e918081c991004c01e03801e603940f50620484032400744690035501440005400304032a007001040c0240c50344a583e0b40c6070305590340140b041c1203c114010003080c0310b00070700c10542d41e24041d07450000e0718440340c9013510311010103100103007500703003c0b040c00c1e0360a40080d0074110665a00c0000305429082510701285000310540740340d842c1c60640c0e80c01100305a404240703c810000c490b0060224650014001e111606249903c2e600070324503840f0301c91103088a80e9403403480501030014141265001422270880c2e6581d140e008000c0c1d400408100c0b40c41204000c0480d141185104003124580070b9036400701c1502e03201944101f196a01d422480301c10001e00108920250f010700404180d0364107555403580f40b60159200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 21126921 1250 21125671 21125683
    0xd080309070e010303120c1b0206090f0904060b030706050309070909080f0307020601090506030c090604020a0c02120c1e1e0102070f090504050c0a0f031704050d1401060e0603030403060905 83
    0x140401102c007000000030b04d580a20808001d498004041044000394101035807176042d00d001900e178400a4110b41c801600d40b00004d40b5900c8005021a007800340c82f900060070550b0101d40c12141c1954a088143c040e0400300142000703030216003002c0d031460901c64442a0b80d21383d03a1241031002034480e04e8007820000000c05881c410121a02d40603200d00349480c000c2e44441d024050082c000b0718040000760340389400038039400440400b8148800e0303034440c00107000c040d40c81060b04500344842c1000d01001a141c860900c068641c0c43d00160a820150404021596409602d60303c3e012031003660010050340c0b103400001861041c1d04100c04503100c044010b0742080304a9008281c0b14032008000100380540c2e030012403042e031091003540c40380c000450810444020501450490340601c0c007043c000510300304146100045d0070351065040503507800001c0d0740f590075410210380e0b41c1070350b54210300c904000b40140d001030a98000d0482181c070b0b008000ca07a0b2800f1364400603108645502120060010521207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 21128171 1250 21126921 21126929
    0x1020403080f0306010f02071203050f09031207060c0903110111010b10030b0a090204060203090105031b0f040311150a03020a0507060504030206090d030c080411130c03051806060d08030907 83
    0x45107448000b614040b00e15074100f01d44040c0804c1031380d2844501d2600c003080038015100c03401c400e0030041085842c02c4400b50400c0c0f6599400c46d000300181d11455404202d4580900b040641c0e081e40d801e12443c02c6401d0701d0b1012854401d0041350b9074203100141c1c0780011202440300030b103044010007040c0d2031868058841d0003881508601c1e45c02840101741da268204241e114010ba179031000d025034886c10441203104900c2003000507042480070001540c4140011900703c11003640701c0d008000303c448652403c0d40a64101c08102c00005010010084084482e45042c101115008071001c1101d26560840c405e01c209581050f03400100030507124010010744507400d801107800c100314945813030080e42d1050140c9891040380b04100c59444582e12a000e02d583e828410f42d21030b90365441c2c0e80d50358109864181102c80c0e028090940c0041c00c044184030f140c2214031566004a17043c01c22000c1c01c41e802105282030f0419421002c100120b548401461115403507000310860340c0da03500d045406041c00240e0300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 21129421 1250 21128171 21128183
    0x71109070e120c01090803090a0302010c0c0906090c03050702010c0f030209040221060108090316020904170a030c0e0d050c090406110703030902100f020606040f0f020a050d060806010b160501020403 87
    0xc010020100009084502c552080c0c8443e00d170103071070f00329031035030b03401107000442e44120003000074401540304a0f18003041070300c510711103030482d03441d4400c1006450f407941015061079030740e0030b030541001ea241c0500d98000703c250000b0030104403415030062468401701910b1040c1500001c4801080e1529030440d2140400035840d0004078203807840404841030188c5030f95001920020205001c01400310894100c01d010626249580780940c2c00d0102045c0005c00555616000154418003481c44d80005c043c800c0069070000799412103400c018000003e07075540507000300c100310482070016030000f4a007103503000c084070000c400356900c0c681600648444040c211a15001007000d508068044d003014064510803213240c02e0311040603008031410244c0c80d07401d4005a2040001c600e030707428640c0c00400070f0600342c040400d0030307101400c1d600280c0c0d001c1d03520103001810008102c0080700d1075110b107401410114003e407603a54500402011103020b41180c000c61010403940050410509504440c001e6038000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 21130671 1250 21129421 21129439
    0x915070e1008010f090203091f0f020c0f070621050a0b060a083c10030c06050d060e010501020319050403021801030204050a0605010f0f020f0f0d020d0302071109070e 73
    0x10030040282c4030a20520b0105890350030046003034116402a00e00ca00342000040c03c09110130460321110704001c0f01003079241640d403084c8000140c01400145001950040105425030700c07400581e182c45074661010b0104905500004a130104c4584004021302c0320130b1011840b91142a0130f440200003c0c0d02e410f03440800041d0001c4c0c0076170015080791040500040300450341550580095001c00c807100020700b4110620150610b5103102642c56410804860000c080740d40c0700d50317610396405600d4001c0c002048020820030303030124050243c07601070000303181303480d005502d4600013035600d01407030f0302c40c5074030205c040c0c403d904051141054a00464006080f0011035400b54000240c031042030000380d0095040c9000106140c049005040481c0d0041c0d4075010805040b41c021550491029544411801040c1181c9882c80041142030101400c0c03001070110300420350400f070b2809014520400c00e240c018440c40d80400c0d0560f0151182281c19070b10701c3d00315520074070b00b15071140c9007104c1958001c0c502 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 21131921 1250 21130671 21130699
    0x190b030309041a01081b07080d18050102030612011b0503040312060609140d020a051c080c0c091e040209070302190201060e01050a0b0304060b060f0304030c05070501080915070e 78
    0x140d02c0c150301010b0a8a51070925114546c052a030306008040401591a0070000c2900060702c110042c400030510030000200c6100c61021400300d49440b2405840c544e4010003404010f02e0304040c80c169003800d10b00200038045485076640c06041a00704100d00f80000440000d050500841080d0842c501200b003c0003581d03190f40c03014101c00001e00503018048041300e140c81ca681490b80041d50240e4004020591007441c203001c0282c1100c2010b411b20040c541281d4404c0016404006801c000d0000c00c0540801d940400c1071000c401401044540c0003080c14a00c81e859130812410180c0050b0141c418001541d2038000a8000e031240c28140650800101426a2000d606603c0141584e600811a540030f1b41c1e200104103e407507442c01091208503042000c9400900340345d102c5442030b60050030701402e114000c903400c03265400072102503010805042c00302e41001000d0040c00d0280400342028181420042c0070b05035110400c04940c11190309040114004074080c0381040c4100c0c1c40104000110415 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 21133171 1250 21131921 21131951
    0xb2403060414010209031e100608031e09030a0f0204050c040308030103030503040305160305090306010e010b041206060e01061805010201020331150c030506060a0c020907031e0204080c0108190b03030904 89
    0x7c00d84c1d03038086000310454a5a85001c0b03000e12404c54846500131404c1062054191a83d00400c0154202440003001407038800e840503c91821814091510071009602d2070040c0410360b034000700700a54640d810030082c0b00054104050300d06582e05483c000e500c81e5154913003915107110700d8003034090a20f0350110980c10946d0000041c85006016001c1e1501c59a0318030042106d01030a02501004000a00042c80481048203001928074010380020500641c4c4d02200d541d2241d0a8001d01e00080c8100d6200b100c06810030701030707030040200384006c500d10300e00111000d80c0c82c1030240c1d16401e8200f100509440c460502061a0784450700509100300032845c202440b0300410f11040c090780480d0401000070030301e2034a07c0c10b0b200000b10a88414249440640c00c00c215044001e0115042c580d44090988917060716600440d80002002001640c8500b07060134240f408802c3e04003241080140c0d001c106005900f208054011134860b980490b890062000090550041009441c3c0041c5019002c0c000f40714 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 21134421 1250 21133171 21133213
    0x1030b060f0109081e03070c060305180f0a030507020409151506030b0d080f0d050103050d030e030703140a0905040e070302090112050a080d0902030a0b240306041401020903 76
    0x41250080d07001540c040040d1546000b41c89a040c0703c0d040750705001c1e008000c104410b909604494292443e0441942e511116103503150000c10029544101300511410741108032800c0b00100002030408098040c2160b0b03640720120001001c10101286090854a03990406100300d07074404a420010884c641e490002800c6402e41e111082c0d842c00c900040d058007070710908250b5034010300040c0c1c01d82070980b506c50b9581e1141440600d50301d02081030507508403d034451503000c1c52107500a4880c44841c0b100c020240e41c1c0f40c0380002081c2c0c004100c5a4002500300c1c82d0300f4101080004010349600c60a041507820308020780c040380c5c0084c208003405904100214940003074034403c4420401690303d40c0009131002f0b23000040245998410b000d40008070301c180000d03150300016040046035004082d40840e04149019100315403245034081070007041d00e03540c44018003039010503e41607a01c08100001940d40d500c0904040c2c0601c050440164211100b034040310a0f55001508981c06c1345104100991000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 21135671 1250 21134421 21134431
    0xf090b04030e060c0a020f03190b010e01090501180b0105040909111002190605040c051201090303050906060102100506030a021507030e18040210021c17060d02150304030302040e01030b 81
    0x16500103428105140083c2999240004840140010b840507401d00441942180c89139505104032000d00140c410341d02c00305000c061158801d5a0194540307111488410300c180c11040b0300e24240001844001141d28002c0f915106034080800d0b0f440c14030700140c8541c400d0344c1107107500c141410501801c1c000400310010207501e0941d5643c0d2614000c0740f08070303110142c0210241d03081295004641c04218542c210307507041401500e0036554ae44c0d5a40025a81d40210f5450b0440359460f20fa524060642511503a0b501a42c40700182009240960000b51030307201c090022225103690782c0c00b081864508202505141c0d40c003030100f030f103030030f038600c5800d103d030303040502c0803000900200300e04803c0e4200407a11008a1030702c10301d8051036403103540c200101509444034050440c411158100c004500714003648064040d180c94142240408a42001007503c3c0100901d000c1d0000c00d40b0b840042e190032000300380403080340d2403040e01da80b113a2400710040d104503440b02e17008584003c0088103002051141d14022 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 21136921 1250 21135671 21135677
    0x61d0d0908060408030601050c030c0304090e15060307120501060504090302010902090a0204030b04020d050c191505030105060a03020a020f030703021b010e10050d1e0506100801080d030903030f090b0403 89
    0x140380d0750305015544040440340100f07248004d0000c034900d54003c0000d442540d0107041a2401c1c010251402071460300941d12440c44251983ea180b403c00c2007c2c0301c800a1900b24100b4035060b4a05038011070758078642d034490001c1a0850f0424034007031100a6001802800340113105010403025800e00030302070302d10404140c0c842c00d00f01000c44c800050600c02c80d8102c0ea8803100b01065581c5507020000c003401c035401d0544560152815101303099844100c840c204040d400c030010303003950600c00b0b0101d41c80c212001c44410302c181003005001543d07624059410028041c5405a510321900c0d03000c134100761040c04a84803612010906808158001c1004100020741d0061340c84244080d00045820090900a468010650000c1d0303507000d9101e00010030700c282480e000458001c07122110007401c41089516055070361390310411701c80c03d0f1808510003103800072217251074410b5505212541d5100c0c4c104008079030a155680d841c42007018029040f01c0c103510041d550800006405081502041008480c11400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 21138171 1250 21136921 21136937
    0xc01060803040f080f0604060c0504030f030306090b0f010203030a020c0a0c0306020a021005060609010f18170606040c05040e040309050d05030306030d0906090501080a14010f0311060a0f0804061d0d 87
    0x45500008002c000c1702c05d80310041604e07454035201d0700700070a0b01d05803000030000700b0440032002c1341c00d1542d101c2c01035200342e0340008e0b964034107400d0308103d4403940742e00303481550804546403040c0ea0010640380c01000300c080050755001140030381450004260b000a1100c1041c3e078001040c0100d6901904500b0031a4080d070b40d07452200b810060448a040b941e0030740c03000040c04102040e5114400801000c00c041c140200885c00c1d2090342c980c05401c075485440008040c0104500704042880100d400410545007480321400c1c1030000b42160183d8015002c6410b01e5400003018944202041001040d001d02840b0107800c0c0c9051054403540b0031180d142c040e1080e000c84048081c400c86288089410590b250b0a1603400c01c0e00450f8801c0026190140f0103894484640368440000041c80c001e06104c4d40c000da41e1403641c54045019140010034620851061081e0300249401000c2000448402c2c503100e01c00340c0d141d203005c1c00181540e528400e40d840c6084c6220035038180001c0c004a8003801a290428 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 21139421 1250 21138171 21138179
    0x201e07120201091512020d09050f030304020d021012020d0e010b0a0303090b0a02010f0e01020c10050f07030203042f0f06070804050103090f0b040305030601030b04020711060d020c01060803040f 85
    0x4540e25214100070300007041c0c541d040202c0b18004894244201045c80c003c0b20f0004a001c0340d00998000c413000d101d9081d0f43d00014403c0090803c540344641401c20051421031819070001442005417100207400f406502c8048a01c0ca032040c005100c9214484104544881d1900240030060a0418070820198641898031000c4e103000e040b640104d030350664800ca401814041703180d226402c00f85031103044d5901c5840da41d40c03000c00750244c4c02d0340004600c00185c442000c0c0344081c0c5000c2c1c1018144090070b01e02001c0c4021f110703103c0f109690222403030802603a203441e6881c0030301002d0380c05010080081c0d46c140b030411551000d580d00c3c914003e401c0b84d149090308401b500f00301130ba20910000402c5c0800c1003208100311750198220910407030150741c0240c9010001e03119100590011035013240091000810868207603094841c01045000c00c1e203045043c800280c4e00c80328000d640d40011449003002048080d102d0907580c0440d610030813450001d00045540d400d00d96526002801203465480e4100e4000c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 21140671 1250 21139421 21139439
    0x60901050303070f060b0f0a12062711060d0513061a010c06050903090d08090a120b0402090c090406091e05090a08030c0f03011503060b030c0406201e07 67
    0x40e4803e5048040381e00e8003400d40c0e541d10700070b08003502c40e280c000d505501c103c44286d542550600007000036a104000d4a08a89414000c4602100405104040411580e8049984450403480d0380342d000403400c8040c821701c80062942e00032000030f002542e0a0508020081c0b40440700440c44500c143e50a00120b004419001c598000c1000b42c01e0004e0a403400b480e0205020f504075a81000c01c8009803850035602e10040f50207403000602c1510310381000100d900084c2001f5520200a04a01654004656065a4a00d894503001e840a4455081600468000603441046603041d54004008106059071038001d680900060699091661120f02c071070104000786010f024401c10002000e400c000a03203aa40358900e81004d0100d1074440c0d0107100341c903118109540207501a110400035030080c1411000c2c002e00382c618a8010004090b014000c3c40700e40e070030750010783e0150349050902100403d50203100418001110030044450311440501220f100010300b44c0d071898040141c159184103031114200c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 21141921 1250 21140671 21140677
    0x1418010c0201180803130609030203040e090a03210609020d060503071208030f07030e03030103060516090e06010c03210902011107030503030a020f1912060602010b060306010507030c0804030b060901050303 90
    0x254000c0544000d2240020b070713000001710b034070005c50b180b00c190500881d254042102c003000021009640005401d10052143c180400e43c400100780003058551019903004014006400b0b1000c0b150082c0000035101d41041e0b002035002c0c01045204544403903040207060f000d1b2030284941da009010315600402e200c814480000e25190f080311025245464152201e041c4000003440c1e8002c00d5035030491600550030130710086000314015000440e490900640803c80495850b00c04c0f414045a00c030200f08138907450307070801d41c00318007400c10404020050600743c035444410040c0450101545201c43c0d0040220b40c0030200950003030365400c2220103240038a65403a001400b01a10325481440021f000082903001000481404a0281c0c14010b50540a4200c20800c0400c40041540005000780d000c0d01803003124000c12140c0f00a10055101c2004074040707100150030f01c1d04000c00007860380141400b45015200c1143e211710b05036591540c90034808000d040c243d546034030401c21100005140c0c0350000036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 21143171 1250 21141921 21141941
    0x1602010209150c10050109060f0e0402030c01030c05040902040e0106030b01050c0604020f0f030a0f290112080403080406020c0307090501031a0907080a05060f0906010602070b0d1418010c0201 84
    0x11120244040c1c0c90005800d803c400c04405641c072815a00320301048281c05002d000740801d01010072a0350820b1003402c80130700070703800800b50300740b0340010003000d6a000074000344060400c5c02d0000d00d4040c940703401c4a2510030340d0000f1401034000a40002d05045208601c0d049401035070701040b041c0c2c1d43c2e400440c1c00348500340038450503501030000b1a001d0710b000e190742d1034419801040700000c425942d000c2810320440da03009a0304286910469020300010800e424a54415440d07044004001658041c00303501041c05076401d003c00b1482e811040140c04c030129000b039030700102120740340da13a1180001e540340380c00402070b03002c1d000d402400904034101d13014040c1600d601c040c260010850300101200e0101004010058030310401c400021303040317400c0c4880e00b08180590301426082c9800d20030041103e0000e4041c5c8450b900c21401003000650106070501562242000c6540d2014000c540d0400781c512600801d920348180003d0080c01070290000c0e1213104041c000030310104101060136400c9409803a1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 21144421 1250 21143171 21143179
    0x903010227010f091710090803040309050f030a0803041a01120c0503070f09020d0f0507020706030506100804030f0c02180403030e06010f05100212030103030903150e0307030f1106070201051602010209 88
    0x10500c45d00d200420000181c41d0240e0886840403620303e4480305a4103120300940b42c4c0d42c8000148028075601410702c0d0003030142541c5c2011502100c0300440e41e80c00a51902400144001c0f01103010021002c01812042d03021074200b5215584030785068000941da024110303442c011060001840d400d000c20408102ca0080500319002031800c240b840281d44000120b4072140e554007400200076140d071207030300d0288903c2d03070080103414240480903044640180c0301034404d40e58104ea40c150b05500c4150640d10a83c545081d680c1c9031200c407000c0c8c031200a52000290302c048011108103400b02c2d105500c030f2286010ba41c0900800f11030740030381c6485060a00900c005013080c0c920920250403c4001e180c00102244120341415140300c240d41056002a002100050380100c000c106110750003034201c00b000440d4000700300c503d402c4020540e8912071558005c0070702890702c0e5556088c13400760054525151a40382610840d1500920090013008201d13591655060003001c3c8007030907072052003a00c4c0b413000054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 21145671 1250 21144421 21144437
    0x15010801060e13090c05030c03010b030601090b01050403050d020a120314061207080102040e100f06020601180612030e0910050604050d11030a03050703020c01080f04020d02060903010227010f 84
    0x3a07086460004804a03a5040410106030000c003050501c00c3c10000c6000e00c0f01d0030075041c2000c04040c18074841c607411520036070510940d10039a950100c1c0050449154074000540d65004c00c005848502642c0d101070304501a208e02c4c400c10540100b40b40424910a01114a28030200c26050b811114500800c1d410080200b000078000c1c1040081d000390302800004550304d50f41d45030b881c6401e907841904008450b105e1720051168695401c1c104901800e000001e0b40d50380303420040000d5031400e052285201e0b896204245095209040e07021101501d6007040c40180803503c1e007409020400b403107140340e00801a00c0000b4041c06801201501951002000c0a103064942810014060706402041d40c249410346001041d5035010485200a10b22030740740c0d40d842d881c540c10080d045c101c0d900c076680e041c06144e0f420884c0500e080c074544e5500960460701c003001e9042ca80003042481c01200803054243d032001840c40008000811409000c1e400f581000c003001c00d0340001105c1003001e0700c10030008501d0072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 21146921 1250 21145671 21145679
    0x41505030108100504060e0706020109050705100f2a08120a05010602070603330f060203090f0d03020109060c05040504050c1216020a051002040306050f01181509060e0106020615010801 81
    0x41d404c92504075004500208000d501c0100a50504045070300000260795a40032000810906111120003468101c480e2031000e06002c00242041c02d00c0c9034100c003008914420303d10031128242605610701e00141c03000c0c1c0004000e18091000c0d0b400f1060001c68481c141c40003461409690207890305130b81d07495014010903860514150041c004954401d500c01c142002403081065407040180008903400f8900c41a442c5040c0716055121041d800440854204001c50343c41901c0798401d090000034180d80308100e000c2c49050890042000407401403845003016040d4903d240d0000190007502d5044074108055114001903801070302c038000c21000c40d00915400038650b0011200031181d10815401510300d4542c1582c1c0b400d00b0a03504d020300403034681e4041410700600129204582c2c2c0b20304801441500c65040c86009407111a518010309212a200c000d81c0c0c000d0350307003194210000c0c90300135400e021a0751240002e1140031070900903c8014441c00c4002034071159003c180095400041e190000d00d6400c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 21148171 1250 21146921 21146953
    0x90503040b0a0c051606110109170c010222090605010206040b04030806030307150203070f080411120309030717120301030f060b010e030d08040203060705040503030f0a0c0203070b041505030108 85
    0x100040e0501030282042c201404280140240c5d80c2c04604000d0040740b50b800c1c060068480a10040156500d07803404035007000158030344c0000309914500701c684a4942d860b4000050191207183c0207400454074041104800a0b000804030301500c4210006101e035989a0004903078814040310080c1442100398041800b01c6c0c001c42d80b264100001500756031074a071681c0c07034040d8141c0240c007940d0116503000041016250b400740d546100038025103008003140c14213441d420102c0007540d20042c0708180808919488410810480b1404c00340541030340c8003d9566140202d005005041301030f003d010fa01c0302507149855400440b8162540312190343c618401a40303e203c028042209458141f110454801e111503a040013826070449059440d00c40340e103402e02c14542020009040001803000a110520507503401005441c0300485500502d92038000c0000200c68101c142000039416010701000464080d130307424002c0c4203648840c49034511185040750200c400f48000d00c1400030790307001780d0581c101800c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 21149421 1250 21148171 21148177
    0xf100806100507050f0a060f050f0406050c0405041401170706080109150317031509070c06020c0705120304030c0621020c07050a0f091b080f07020a0b0c0a030b0301090503040b 77
    0x41c6600e049410882c0590300e0628080c00d0540700c9043d030740f141c0c80b400d0400c00700e401207113249200d14070240010f0414125120131400042c0006003013039102d600290084908d202600c2c0108002031062281103041c0c86981e04444d003c1c0180c0340d0b46540301c20041c6548400081d18000c5170309075130714981146e05e0804c4041c0104110703015110f02d40c44040700080460054240011020225076000d90350f800c22213060350302183c0038080c90740034a0031001003012094212100940f1541c01040150f51586c80a40d45070610125402c000d9001803d110750280d4018000080c0c41070b24880c5201e4803855484400603071380c00384207000340315011105144008200b19960007400c180c04109007142e0799503460313000082c040012030b009520076000d007907420410365007907000780c0b0807041034000480c40243c5030500c000d00625008000307075030351a868070124001034802c101994580b07400514685044c1420038068100d0303400042100c0021342000400326080c0760602c5044600d650200095141c103142088401081e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 21150671 1250 21149421 21149449
    0xd0501060308030c2a100216120f17090a020d0302030903070306020c0c09040f02060309030d0504030801090c0806010207031101020a05030c0105070201051012020f06091306050f100806 81
    0x9521160300000040340d010141d40615030b600400364442850740d4103014142101040c40c0d030031444101c1608040e0501040080d0300160b9110051303901d413008040341103208092032000b8980c000c031030305001c803c541c0889034025100c4071795111403e0a0721020552200641038400c003e1640040e40c0e090300502e4272034106c00e4894403c0c0181c07410541c201d00081d04203195544141c0f01c1c0c40c0c002508900c1c5c050b05222205940c201110081c1550400d44c40312528100600720007400b4440c00000715000541c100140c0322078003c40c200c240300780c1c500f500e8000c0941200384210341101c0c4c10581c02800250084010520403403041c2d0060800929548030700ba03000315240301160550096070400710101304107100030115204060001b103818100203d0080c2100d2009014803540003e030354091000010003050341c2c1116404840401c541588a00050711038815560a2507000c85071006075009005207800110032207104503118880000f80300e00f40701382c0034401c1f92020009000c0e0b80004001c0c3ca13124285807103034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 21151921 1250 21150671 21150673
    0x1150915021e0706021207061107060b0a05010908062403192d1202100603060b0f03060606270402040b1201050609060307030c0c020603070302040317090a050d05 71
    0x16503a11152000350001603000385006800400b050300d0b212103100c6a03040c128041500601c1c0891401500039107403680d01d4107010440800045c03050034050030307402a070300c085440420360b0b0341d0f00130030b261120082000541850140298020010399076005d140500d044650700c3c4050502030f610317a00400b5148a042c03038562034903003100d640d441c010786080000e00145460309107203001340b190b2420808010300104140c9940b1050f60310340d00303402220b4943ca00780b1055103d0240a40a15121801c0e824120011214005207141840010a1124a07041001644402e41e442a482c11454091640b40c0004840740f80d00020f04100400c46c8195185094809650a00c404030040740e03c0c400003403d0360701983c13011001c041c0108424242c64070000b03143e030043c00b084035014030703040c058004524103000c001c00600c2850b43e68164501c1150199410001c4035034010040c0d51b992500c40000f5009400c68002510030880d00c07654041588000000c451f0051f100511a10341b4515242c1041f030300f084d000d602200c60f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 21153171 1250 21151921 21151937
    0x902010f0e12010e0a0308060d03020705011107090f02180a1a070c030803090f0706210203060415060f0e04090507091806020301091a010f201603080409060b0301030b0115 75
    0x107940081c1301d0721401140030b0019001e10307120f03410b004004003400307010385201d4007440c1682400690000354880881e0b50a007000c800c039000845566081c500c49a00c1441300c28103003503036001585200c1d402170038002d149100b10300d0441c00741da050100180b0305000c0d4145400004d07110540348454400a4084030f84a001c00320000742d2244c3c2d40c0d1042360030555051742c065000913003505850b20148a640b01800f19490705120782c049541000c240b8024408000c0301680c1d0002c08500540c4454100b80061020b610000f0740d145e0395090010060407480c008940001c1d034000001115142034003031013800c10f4211000b4840d090602600c0c5006140ca03101c0c0c0804502004a03840c0000c3c114000386000389022000000e414041d141c120a4041c0030050b03460410281c1c07452404841d4000030380b40003038901346403190340a840349000d203032411500b1410080400b045240c0003041004400040003510300c01d03c01445401da682020809501080c00010f0840002030300501603503602003c82003041c400391501d00300c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 21154421 1250 21153171 21153199
    0xe0f0114160803151c2607030f0206010807061d0604180606030501061103030a0506060405040f021b0102041208070303020906030a0912020613080912030301060c0c090902010f0e 78
    0x94840840d1040302c2c0031201004021455141520311510000e058611140641e0300440f0209201d030403c000405081c15401054850b10100441d030704415204c402c0c00b90b0718011414044e20b803018401c1810018420032001140800300810381c1403c48100da01d543c01c0340b0407280b0381c62000151200c1041c0d04041c05000c00202d0248083c040002020350020010b080da040541c01801e88d44140c0024040c811044485c403a9440c000085951140000a00140f10348810307002542c5403043c0d6011a90107400d018980289159981c01040310180303800500210581c40c1082d2030a138080c9206407852002c0040d000c2010403001d80082c2240c2e131192070014980060080060b0342c5070800c0e07039401d401542d40c3d00d4810820075085d00ca80715001c064001230440303251080c3c41704110014001d004103101404070b0a040e0648956001e50804c0c445602907940700d42c0c481c40002d0010103d6182035a5810345010009013500152007850000341d01039403481071904020f442070320400744c000000740d084080071400030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 21155671 1250 21154421 21154447
    0x501020a08030415060312080a14040f0302011b050904060e01030c1a0c01021306030b04050105090601050a1106070f02190b06011103070209040507050f18011202130e060103030f0e0f0114 82
    0x1014602ca6406680e02107041200140741420007445851494504401c0cac440e0503020300f031056842a884111004500c5442c40c1c12809407001c3e50050001c210b07a54004504150440040c11017402c090fa010015941da40e24000c036081800e12010382035890514051144060841040c1042070302d460780d092610151928803402ca0380143c410b00712020a01e441032103016494090700c001c13444221401c0c4044e5050400141c00400c0240ca20341c188440001c10400f268000e0302c10f010f00103004d0302590158500300310040d120b10780a00b030900060140800301140d800a000607015840e412650030308a0341c0d200001950b6082d02c05400c2501c41c4001e002160050342c4440d225841207101e00050305d01980743c8403e022020100c410201d114413603c0c4910a108400d5020740e070b0444140e0048000030089a00200b00082d2240030004211401e1003540304071604000790340c50403240700b65500c8201140301d1500311205542c04d0011a1720642801501440703610035540c4082070010341c103440b4a442c100c25824 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 21156921 1250 21155671 21155681
    0xb01030503030f0a0203060a140307030c0305011407110304051e0405090f16030302060a18080f0301060807170f0a02190309020a050102070b1c02040302060c010902190501020a08030415 81
    0x300d469900000c2040004065880d10f1600802c55800540c00c6003081e0000030420001800789241c111a80092590141e4003000f100c0029038120b003003450125204e00740036000e440c0925050030001c880c1c03004100503e1194110150080361503001c1c0d030030704d0300f054208108640b84080c0004181903801504585a039036104450140b041000100700d109260684541080040c0c8010400560100d00030401f1913000f01c0c80545c006000706000030703a4007548541c0c8411000d002d034003070000c00c4040b40d406603220a460055059942c01d4845601560324507a0445001c0b1500080500400301080450210718074106c1c12a00141090409820a49851f102084021484d0004400039413901a48419820002ea2105c003400c000c0c4040d10b407550a0a480309074610807004030f0100c1c005603203c20070549001ea070680703000c4c59005080c1903170743c460001e625000c0e10204400343d01c214004400c200c40d20842070094002c1303500603000fa1040d1301d4103466126050b000288160381c203001036003280200c80c1c1c1b0780c421 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 21158171 1250 21156921 21156923
    0x60209040f0c0807030b1c03030513050307080c0601090203040812070c120201061403160b0d020c1603140a030207050d08070209040c03120203090312220902030a0c0903022b0b0103 79
    0x1540b0001d1600348002000d071b81d0120301440c0500428564800070225000e03850200741e41600b40840c182c0c9544000c010030084089000d0518040030900b9001c22074454002d0007245020760072501666203c00d04541244810b84c0c00030405407041244008038012040c09a901c0429400c1c110b901110980300d03010b407058480010001070b50f403200284680c16400e1400748156000b03400602440b9a41080d07050795526034014014000400b1850201131078050301248d90f420211030030f444604c14510b126000040f4035000440303802c0032003410240607000c00510502801d03096801400c2e054504824880b086500000a44849900308155405a1628004580600c0c07240c440100401c0c9103003455440a0440344250085403c20000c600c00e9503000078014400381440307442656160b0b07012600e156103078107000d584507011480d1a40041c140125602940c4a0f01c0310100c1844411903a00040301c2d6482d503400000c1d409101001c0780781001c44400c8000c050304002080000410762140c4035681817002c00d82c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 21159421 1250 21158171 21158177
    0x40f02130605181c080c01050f09010e060105091009020408030a020c06070f021c140f0f03040e0c031323070f182f18030604020d060209040f0c 63
    0x14a00100c4920103030900c0101001e1600700d04005040741281e00c40b1a400c07540d280300303030b0800c81420700124100148001d0f442d40f0851003580d0310020007126020b800d0840c4c21140501d1aa00010312040c01030061a00032409100a000140e003808104200040086d0161041c3c0c461a0000714128405100410142120100468440c1c0251030024900f0040c182d04900902090000d600007442d032040d0141c0e0240d0403100d100d161030681e0402c903030403158424043e1519000f42406110640017082e189030198031b100550314a0054a0070081da2403007944200c03501c0409400000b05440302c5070018503007201d56011709032101c80316511000d1500c03240035090219048803000e1050001410001030004054103000b4032126460118a14030680c40840380d4002142c54071038460503041000c0c05075495852100702079070840c0e031304e0700d10340001c0c2c000840f0364010303240e044c060001c14500051018401e6500a00b80321101c1183d6072070310040c0d00150030750340d000354940c041004100054000c071020b1618941d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 21160671 1250 21159421 21159427
    0xd060f030b0612060703091505160915091403010902040905060f0a110901030e1501120b09010e0a0f0602040510170a060b030705090a030f050105010303020d180302010e030309040f02 80
    0x7090000c8a024040c1103548518a01505850400404034150341d110b0031600f40010070b400b003810312075800308801c00e0441d80e040c940801c2159034441e0034442403c80d10640d0fa0402c03501d8036154190b01c14403650701580003040072442e0030001c001811105001200000d000494400d4140e4041010b448085400b20350640040f400c1241c03001040f0f0710243c0c0602244010301c40c1d612404000300e824412090158100350300c40e101c0f1091400200301c01c12410030540c071840b03419a9540c2e41854200c5104808907011101c16000c2101c510341402103405000c6002c01410708a1b44a9650540300d03100c0304002c0b50304940a0000041523503c50404262404054845c008194007800142d00d5441e40100314050191528100388100868501942d500020605000340e4a41e250000141511496800203100002084003481085019001039048902c203808885115180280c00d8510b035004424444002e8600c0d00c0820166200300c000c1310808001400b52880d1030340c1d030400324080d540c940c0b600100d856000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 21161921 1250 21160671 21160673
    0x2030106080c0901052502090c0301061106090601060c14030307030204050103060b0c0d050d021b01020a08011505121b03090c0f0402070305160203030412060f0b0f0d03080c0d060f03 80
    0x110240764030050b0041500e2504030340900280c0f450081640c40e4040c40039480c07178001100581400140310320f400034070341062440c2080300d00c041c5134800d000d500d002508400c08200f011400280681c0104440b0700a0000740c0c0c2044011240404100c0060300c07505090001d60840040a000450080c070940e5005641ca5041400240c00c2c1c40345a4440511035804204d5290f01d5000482e00b400d2060040c68541ea590a605c0d05120207401259400e41c08408031a0050703105060540c000c00031600203881e0070700c10360781c3c54170b40e442e1410210030000041441040044014404c1d4280558085c1807410780c181511103507010001c2d01d40048800c802140d000c2c02c002941b61a10b003042c42c041e80000c07030381075107003200558004103a4002c144e0740d21001d81d18480c040045641c2031069402900c040a904582c0c05003501302040585000c00c3c4868010b46414400c401034204200781c007000e441c0c080d05240c81d405031654100d41080005143c400c80307a03002d01c840149205240104c0c8001c00340c0c1c162014490f415 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 21163171 1250 21161921 21161927
    0x50108060901031113020c0f03040f0506030c0708030703060e0108030c070b0906090d0609051f050109020708090f1203130f0b09010e060f07170d0c210b03030c0105040602030106 78
    0x409004284250140001000010b0002c04c01040300720702a540309040c449113400d4103000c0c1c0601120000d1902500d045a951814004041d0049403c0503011610741d565800c1485403a20064840709200c000c10880384000c1903c2c0001582c20001070729001415985e103007c40c41c0c04410030b030450b000c590030000b110545002c04011140103070802d103a41c181f500010600185080c03041c01c40c0d0300d01540d00c03080d282003401020b902a52145400c2401e43c3c84503961000e80a07a00101040c01549161400b4008607006802d84295580280e014a040e45401d200c142002045690301802560050310900310030f9071140180041c240452801e80107210302c600b0024040c4507a001038101c10b01500d8117000c1101e950380c1c000f80c0c07005801401d450f00741c0d032480700c84112521842880c4000c0c10101d0240c412a102074050b4004061400604000708080f013410718003160007060b018441405034540c82c500c03031040c0794181d20043c1c528400400b02ca20b041100100c141c2903500c00c84003500c01d00d034044010055150 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 21164421 1250 21163171 21163187
    0x60609030303050f160f030e0105150118031511070f030302090f0301050c0f1e0406090501121a0f0616080309010b090405060c0d06030206070b041509050a0209130c0e010501 76
    0xd40a884884624002030702d80120700d680344001741004440e5800e2180d1a029501448020400c0c20081c0003501d09440c1945d0501c503860811400120405808d4045441d2210506c0070740398800550310a40303010880301d8020700124111859000b030b0801076000061038480c00d8800d01846a01d0168884140c08200001d008940356054002d90401d420445900e90340e00480f1030f040d000c286400d4079159072901c044401d0800d5941114108000240803455035000b002800c101c4d5401d90300c040c3c010881c00e4500c0160784180c280702d0800c180c1c52000b4020f074a04003411403407030307a03010f0004c0c1e080100819039503040b081141019110042c001003402010b9600303002c1c10100c901d00340d45555560916039146962214020704092081c040403510515504144e0400c0c001107030010a035a80340c0c078280c248103208280a45c0e088603907020390044004180341c00c1c054405401c1d0004d000d414081505d4007880740e12103000b05401c1008002910380d00001d8981c0100c10041d2000c5002d8030301d00c0d1305180014215607 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 21165671 1250 21164421 21164431
    0x60f05030c0f0c1f021602060703020304050d0c09050109020f03060d02280e0a0506010f0c020102070e0c0a0f0e06091207052107050102030f04091d0d02010b21030301061d0406060903030305 83
    0xd07004210340f13105515130b01b00e60300d8550350503112031f60b44032214101203046000b650400c0b0f500c1460b001000c024070050151a4041e100c0c420f100300010790b41e07565014124860407101d044502400e1000490700e2600c40e10034400c5034009030002d0480b1070902500b40500c440e540c540758803040d14650134010400305120403503101c2450501001a42041d10000e44100e045900a004100c0000301100c00c42e482070120400401101d6414411410b1410004906030050041400040d10000c00800c0032441941c0d1040c00c40405009103203003900d002c00f4003141c0341030310b682002984079a100004558465008100303a15540301c0441444807511185c00342804840c0d8000c41c1107501c00e101410050310000304039400c54441c4440003445007104800c1680d0b6603038804c10f40c035080c050700e15200e070542e4040d005019003402c22155207036200c5100401901c244640d039007000c0d6551061005100e0745000c0c114112445020f0050700411101d6280040d058a45582022001071014801003003056018080c0036004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 21166921 1250 21165671 21165733
    0x60803040303020604080f07050304060c1505101211060f040f060302040501080c031e07050a090803070f120903060207030302090906181501050c01020d0902120601060f05030c0f0c 79
    0x2900c1e41d1070096071a40040c10261031800c00140c62009028040201c4902c6948841aa5103403a50340c080500300c258041800d94006001e1900c8162010f0b06200d07081c42040064290041503003490b02e5003000c140001002c607800c00c00380712a0802c3c1d035108400b40440861108207140d880c4e08000c08034100300565400001854014441400980c0c1c2040b1032a50044010783c49507142c0c0e0314004000402c2d04080d41c1c86034a903001405000c181d540c0100204a09103950311240000c0d6501d141459480c410250058120300d40f40c01da000004107000022075065a29180842c2610b4032525024100c3e803154800300d0210f0b41c00079052015040051145070300580c1120005014101c2c01904140010001e140c1c1600c01c0c0c01046a46060780284240c50a000c1900c0085480d082025484070003003c1041d01607116a21500c20755001d03180c00161181650135a655481d000462040150343d00d0f0800750862501210074040c103003514200c0805011010960802071615401c144142105602c2410411200c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 21168171 1250 21166921 21166927
    0x1090b100504061d0402010c06180b0411010903050c0409060e030309010e0105011512050603030f0408060f060301020703050a080c16050615030f030a14090301090c0801050601020a03080103080c1005010801020706060803 96
    0xd41d01d10080e0f001c5c2e01680a0030580401c0d00f10785403000042481319149030305001020008004c0c843e803400c5007031181e88194002000c958403c80150790081d40d5210003013060f84150b00210607410117400c86c582e824466800403c8001089c1460b50443e0402c482e80380c01603554815110030031000740509401081041880c030010b440140c0300400c2c0c002d01104a051440d00c6401080203920100301711101040720b18955600c803030f120600652605400c1d0b400c00c00304850350010619916042c8200d403010ba501d512090f150000107001558011801030a50781e60800901c43d0a0700005041000c4e80b4207032203200030f881d9500d003023081c0030090640c200c030060180c0d1018030714098030f04d0000200c070300900c4039061444040340c0d109014040c070700c07a001100b5059420440355008104c002d01c0090305030380c02c0900a100a40c7d40400482c0d403049486800307800540c005004201045940b402817000c1c50030070003920700711307501002c502064a8003079000f02d400c1e0f0f40c002912010f0041078032406000d024900d000c1d43c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 21169421 1250 21168171 21168209
    0x207080d021c0c0804080a08071205090c0103050a06051f0306090f09060c020c010f0302090d06060602010516030207121b0203011a0f0409080f0306030304090501090b0f060309150901090b10050406 86
    0x311030b015040d004001d1200108c003154040d0b005010040030700007c208184254a0640c3c0300c1622405654003030740c040390400010644040c81400388030140c0f08003601c49008005a9000501100181d200314410b140d5514408a00030003980682c1ca0110f0841001056410b002d191010858408060190440d007110300b486103a60b138032207080c47c14508245800b685a117150000940203688020000340070350310300000040d107580c064100c40d01c9803140002c0c00d20704810b40041682a4851340303c0046c070341c0e2040e9142040140c0220414494921201c541c1a5180b0385a4003181c01c5441500c101381380a8011030042e00b042c0340100a842161209407424805c1c03400c550b0700c00e0503500404c0e800895408004c8001501501c2c10400c0e5001025030920034041c550352011084001d00035641c80c0c0c0d000300a0995a4a001c0c2003100440e4000c0610702c004011126410400c9240841c018141c42d202d9500c8840c0794000c280ca0380c08007402400902c04000045140400b0401110703100d91080b4404106012490 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 21170671 1250 21169421 21169433
    0x2206080412170a020306150304050a030206071b06050703020403140a02030d03090209060405040201180b03060306010b0c0a12050405030a0308010509070207030b041415070305040204060506040503030405040207080d021c0c0804 99
    0x5030000f50305800541c9986500e000100c00714000106142c0050000c8100810f02c07000060541089009400356003c68407294012260414040011528004199a40c00c0001d0086d800140c0c04030651400504194880d60f400022011422155945501000c01d1a0941c07506100404a00140b410200b2400c0070f59808101028070081a440c030940d0794400090079640103540d41540180c40c80b04401c40c0301d40b09c000c9544070741c00980e041806031050400120349000b940741224402100d200042c8a20790159965020080b422403c441c10000103000029241d00e040260110045c030a131203082856060000307100c480c0400400c1642150310403902040400c074041011500f01d500840c0c60425042c6a2003118034108039041006118250481044446540b540c08076001e5442200c00303006056861003008103038015401002d6068000300405c1000d89007590081145602c01c018030742c00e00e1141c0070703218202c0e00231080e54040000d4600101100320000e00c241b4040f841d80d82441605800d2946032a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 21171921 1250 21170671 21170717
    0xe0306010e10090e07050909060709060c020607060e010b0604060c0b0a11040605070302011b030b030606030a051e01110705010c1107030c140303071202071a040b030c2206080412 78
    0x9400602c4d41c0d03000e6483c0030b10091255001504000c0c12078192814072960b02647d07450101c8258002038104075010411921850810881a400800c4203040014a849403001440500e991b108903640e0794808611988619001d4001000340341c803480d000c9607160a00001e550380c001e001000c86031410b41810404026941030302c069480c14079003540c880100d032805070700501c030240410b6810070941581b071610b541c0c550020080703540c06600f601d0540c0c50b0b003024180e4940110310001c203143c110800808078140ba1001401c0c885000c28004100800902a440744680c4409002e5445944070102e0400281e000074254a151030503000903c140d13481c4d070300e605038007100c06d00a00d005903c12031000896070b0303001c00607a000560006050402c100102c0c8010303554030418462046a1010010001078881c03000058604540d1070004081c9595140c40080a150b8407040c1140b401c4040b0001c00c5016501040800c0082c01d01511544817906060400b4181802c00921100800507036043e1720080d882d240f050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 21173171 1250 21171921 21171929
    0x90e0f010509120a140301090c0e040b0109060311070b040b060a05060a0c030c080408010e06010303120902090c13080d03060305150603030703030b120a0501091101110303010312050f0a0e0306010e10 87
    0x480f54072042038040481c1c0014000400b8801020080000328400c4c0481d40000c61850041c0c46010704d41c00000d060005072441d00c1c612602068590004000a5000b900803010003044001483d01c0c00c481c0380c0d101520300c4401d4a00b6a07095444008100013030428050720409008101e80003410010030300c0c001003554242c610004d0401100721a020100301142054501070980c401c02409014003519400f03039034080074881039000841c034550315240c50a43e031255452003034010300b9800c21540e5240e043d1035a03030f002c00d07003031440da440c1020000351641007403007612410080d698000c00c6051a500f0103a140c20450440d8500c00500c0340180034043e03030000220b07681c00350306003400302c3c0c940990000104180c0901d0361031806400349600f4a000c10406511801c521840380101424030942c0400445403510105550013056104100500118113003290010420000385401454805903104c02a039642000190340c0c041000c0f480e0421035441c041c000b0307901502040303c0c0c14000d85003400100c00c4581440c42 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 21174421 1250 21173171 21173203
    0x5120a09030606030b060906040e070504020f160b1f0f0905070207030b010603091b15080405030910080103021e03060105010309050f01060b090312070201020d050a03090b01090e0f010509 82
    0x240406489000e4a2408010758001400700803081c3d507801c1400c1c120300212040b600c1078544400091310381c5028460441c2801072000201500760600007408000e6110070101c1a030710300240441611007100d072003802e40140c4520711140a60034618610700409034400e9941082502e030200a00c042e03010a44941e080310440703403020880d9112030b00c00703078104a0960000b070a62039a09001050701c64141d0880300130644546402c200040004016215100c02c83c041e2924150320712031003c2c0c420b4400c040c60760300f050040301036924003400c040020324010001440710b00420036500c010019450303d04945180403046402c00541641c0210001c1c1d2280414020b545c1899a074108034805d0140403ca070030804003500c8020495640c40c0c17009402079800c2409060320038405d040611040ca405842038800580e07040c0c005100401c0307585019103698119030502d400701690f41d005840851101d82c0014020031959400144a003c0e40c100c2c1400e0501000107442103a050030180111080000707139103d41500c03208 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 21175671 1250 21174421 21174427
    0xc030604180c080705010e03070e01060503040827040b040b030c12030c070e01090b060a050403030e041b080a06080705010212210103060608150708040605071b08030f010509040512 79
    0x4556000c0d14050000107400c0b140c03080c10104a203940041c0f2042552801d80f81c5042e005400002c15907608101e0180341062007400e40100b001a00903030186801c01e01c140500c508164544100d548460540c0c03183d083c40604120085043d410304d4030a1f15035803001500c0034000e0300304241c00700c0c1c2d40311a030303c5442c0e00607520400e0300142c2d1b040500903a1881000718003554541a6600e1301c0b06400142801000f2072203250511403040c6240040031200414500d84401d03003003e24645040c0c4d00e541c8003045068000da1200c154a01021151560700c0010900352202070702d80c1400d110704411038983d504071041d903900014007440140c1e000540c03800f00c800b0b0310006a9841d00c404c040014142c160500c03200084158900110400c035040d08054151074446044030003030300c414006c80b421441c041ea200d101140c2031502103030104110340c120b00c0e4041043d040c1000c3e45088e1451044c0c0c1e0034030140c020755900201006002000071610101c9005020845040c0b40d242403175100c00c2c1d224420751b2100e1b15000400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 21176921 1250 21175671 21175691
    0x6090207110d1b060804050c01030507080a0209040f060603020715020301060203040b071112030703020609010b0108190b06030118060e010819051c050a080a09050d1d06030a021b01050c030604 84
    0x20702c2c000f40c280c03440021110f9115a9883c000d8041841510304462900036080081c03030f694441d00c00c0740d104210a42d205180c645901c1c40030002503021150540c5c0140d100d103a44030580351540291030041c60640d80c0181d407400395040c0342c01d8061841c0c1e42c06203118010001080410341c000103550940d040140c2d400e58552140c40c2004294440e01380084c1c00001d074a06a40c00c0c034a000c80640700e8503010b5025540c1d10b0381c0e0340013041e00300c904080000d8007155403000414400035600030000d84100010000142000310140040c4040d00700b40d00c481e0640600070b003070b64034803110340c01010005c048092803469254144100e194503098210347e402079003020200340704180841000f80c030b8150020f041d00941c05400c604030082c4207a014541410100f2650804181c1400301071091300c9410790060701416410742410f104490402d400000514483d1f03099002d1340d01c580d6010019802018124001aa14000f80c4019a5001e40b00796915480780d1402c1c0412650586402c2100e034840000c6a000400403c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 21178171 1250 21176921 21176933
    0x31605040c0e040905150702010501060906050901050705060c190309050a08070c090903020d030b10020d05130f080307020102150403050301050d0201030e06070305010906320301110706060906090207110d 89
    0x102e42407195001d4200141c4030144880861150300d0014039141c1d900301c40d0303107040b4240d003a11028403d0400103078140c1800c10a551240029001004d0140340c418035007103250715001d282c82020350341043c81420014085100000122100f40c000c48a41070610003000380d6250140c41e091442c00c00381ca0004009810750400c44282c0694029103003080007002081c00d5802e0003075555011500c1000468601501078400b07142a5501c1c906261302c07a8020240c4202030503044546030000d000058060010000104680c010b000c50040541391f40c40055480e00c001b03000091074000b40070700d1060b50507681d5040c080485c0e4841c0450b419280140c50030b08584031103100483c0240384010448206002da00306004215a02d0b401030b40c102e81032810240710458554884d40501c1024480340702444c2c042c85203007050222614102020001d00800020b1040703490404c050003503001c460100c5505e41d8651052001055a21039200a02024002103050520a9990845881c07810464038420001d2220490801030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 21179421 1250 21178171 21178187
    0x6060813020d0506100306060b030606180102030d0e0a020405070306050901090207050a08160512030c0901030b030a050303010e01030309060e0a090b0f040e0a03020111030f040b0718030b060f031605040c 89
    0x2c0d0040445480d4600415500c1070a171007800100ea0041c145040094905d8410081d00d004800040083e03281403201d4403109a851245c01c6c00740c0c1540070901c490580740a051050150701c409180140032041e40e184100411520024400b17028140350020500c026150010b031941924482c80005907a46a941009460050780c640001c010300c8000404022100e1200e00045546109404a5010a00b00f4200c140a03010844080000c0b030028810f110003584644c201403541c0d20054151102c404e0302d604c616045510907040b0b645c0c00580380004104050740402031200806051078841e00301988400001c90302da5145c450042140c0d1200102c500035550184070b400c02580007041080300381d2110107107a4481c094804181e0155207000088020326034450f080300d100301e03070701c178170b0345800c0c0d9500d41e15041841c01c090300c500100000b00201c1152116960086c40145005444000641c03401904008050301d100b403240d0f020340c020721b40b1111462090800c0d81c041c0e40d000c031004070303440214802c11650a1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 21180671 1250 21179421 21179423
    0xb010501050a020307080415110615130e06010603090c06020f060a0c0315060f030e06061309050a050d0e0f180a0b0102010908040e1609140616060f06060e010306060813020d 76
    0x91b00004c0010f040f070f09000c05121715008a40716142c0300c10791a07800c9910303003c1c1141e200480b0200d000340c050441c94254080240000c00c881c00098025000300c00c2490690240c1242001c203030b903014241c0c180011190030034014100e610040c80c0750307001c40801e2a114400a0035a840300780d100c21200360007600035004000d01d50010303220301001720740d0384c64020034141a002c1c0c880003207403038145980001c0c08040355040c03103820040c0c100b5812621060b400070040c80032000c01d43e002d008500040c000504103001c6504075200d990f4a000542c4c10701420440e00c2215012054484c102d07040c1502c1c0c00f0001e00d07102c940d00c240c581c40700260107006040140d000d05540a002400c2d0b003170026001c1030440700c4a00c0607000700e51508249050807004a82502d07910002d0083d110920017035003030500d06140120060085181140038948481c040741c0d140e0040d1030300c0f281720003001c3e43c403101d041c07181d20350003c2c0629245409180a1050702d01e0f01e84003500803080501141c0380c441c901140c01040d900d44180717180760070b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 21181921 1250 21180671 21180683
    0x501120e0d080106140f03010b13050d0309030203060c0c0a030c0309150203030108010b03060c161104060308271014040308030412020d02011a010c030c020405071d0a030b010501050a020307 83
    0x1508000740080c60000240a03640209a15401c1d181441c010603003035500365162110442d14503402c2031074411540d0001a43e076109008819004500c0e910748904042d010352080c0c1f28000700313605503c105401d0020003000344018000c14041d00c1191480012041101905424480c45e03034105406d0850310324059802003445546101550f6902a034000003e604a442c5a8003c1284c0515001010744a441c103840307030380483d071062010078012513940b14444021403086500d541c510342440c011806a4129900546281101040b80c0500240c1ca50b00d0480c440d9a01f4021500101179034009082000030310310540400c100400c1100381c0480403800c807005190090001c4e9103e02d42450988040300d60039a0000050003824001e40410303005006000d1103d00701d140342c0c07440e440c1d024011240c10300b203c2d10903000c100d0064094030268580e441041c0c060401030380c4403000f0340103038111044d0010342203035594090040740a0820101c0c840043e00e0f0306554003440c0003036444101a603300c0c5903018409000e001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 21183171 1250 21181921 21181933
    0x606081609020c0715170603060108070e07090503061003030e030c0604120305070602030406020702011d01051c090f050f15040203070302010311190c021309150c0306081002310501120e 81
    0x4403582001b540c070724802981110702e156640c0c400601d1f440344c80a00c5030400551082c0e000340151000d401c1020742c400294600402550342e1100020300e00030b0b003a151480030b40401041401459444000440060426801084c0650603140412114881e070311800c110450034080110405115204480c0c160340c101d41309548038203160400ba002503219420490129100b49501aa04080103506200019058642d40c0c104451889128101501543e031000070595600c043d4002900548044c41114007070002080c070181401000c82c501500c08500d010884610002c120040e900002c4141c103490b820320b4040780e0040d0b0802d04407254002c0f4140024540105106540381075884502c0701540360089074040224031401c030304801243c00101001d0496600c1803a0305c40d0100803500f05c02c0403903c2a18001035025503846404d801d00a55041400c0482c0e0000b910601c0c040321488181c24444030240350041c2c507111a10183c1340c0300560301c28281400715480c2c0c02080100c2d140d0000d01400d06010660349 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 21184421 1250 21183171 21183209
    0x150c0c020415030b1801060f03080d0c1e020d1206030c050d0c0b190305010e0402030a020d030e0a09020301090c090602100f06091a010201050a0c020c01080a150806040606081609020c07 81
    0x100d95410080000095840c1c9000000c5c1c90090b01c1941003240c0e00200018a000d0201c00f5040c09082615002d00370f01c90055144003002d000b158143d41e07440c9c8558080d0903502d810a10003030500464465803084c25050110600104841019000031100e080782c0300301e400020f500d809486d00a01740e010080850380807a803440c4850140c0b815050181e4a95010041d42c0c5c0c0b10341035030021a409540280d0582e0045505600608003c885812418040e080c8801509100b0b00091a0a10710740c03c102c41043c2c01200410442e08103003d200850001810300030441070811400079503800380d104016551a859600c6040d6004441d40183c016000200003401100f00240e903002d0314101050300c0c46d005610b0000003810f60140f80c842d801e600f0202d517003c0c20300d0b043c42000440d095080904031010300d80da14900310300d031002c1c1030411a0090240c0c8010702904c1ca41400c06400303e8a06901c2541e442d0040c0310032010004070324003203105503001c040b001a2200702400460385032100907040306030201480c0c00401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 21185671 1250 21184421 21184441
    0x6031512030f03050108070303080c0901021e070501030b0306040201050304030f05040306020d06030b0f091905190b0105030616081816380a08061309030903150c0c020415030b 77
    0x540c044903072404d2010744d99514170207030303900d081c0d210140000e01d901c800f09641e084148010010f0000500c110349074941c12069010070f50308100c1105845612043c420009944c150040e0351969008401400311490141c0001c2e0052000400050801c00110403401d4924001c00039500510b80101c03045403140441c0400000800b52404241d0300c2c0d03800e402c0050040c80d0b42d01110303803251800310043c0c0b80600700d680c00e0380d4aa103000c140803641d80c040c040103010140e424441d0b8030300e007078050030043d6015450300b424541010700c058803030b0780e4802440501c00304182d040752001d508001c00303d1101411404001c1c2440c1000410040d015280000f0100010000030350342c0d070049107840c00e01c5070200707690010106490b01802c480400d030300b40400303000b9009028096880c00c0e41c80780000d00b0140c560344104088000303e1b00f50a10450100303001d842d0a009100da0754035404d016111240042103070102c4188058a408e0f80c0f000002d10071920364190800f5117000035603000c01103521030105035441c10508240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 21186921 1250 21185671 21185687
    0xf08070507090e03090a03060209030c220c140403120903050607020f0c12060103020d08040305120a02010b0a06020a0b060a0b0c0c03010f09030c060e030403080d0504110108100603151203 82
    0x6030301509207030700300340c3c0d40c01c0c00f00403140c41030401801a165140395980715806074105043c05541030040350b500005584400c91544109c007161021040c4180740103440c102100d85402c4601c041000c1840e101480349084403c440580ba00000c030b2002401212000f110900001d410041940c01420240000c0e2500005c5141d00c108001c000d0340c401c0305011302403003441c810750010105543e010b103004101604010101804450040c8903103403409440391600e6150000c03004503011010300000e038049205074203102c0c007050b8050459401c04c2c0c981c50000d0003560381c0c803841400750004203000081039442d9100710340c1c41c0c0200b4580200075118405544110f49901d91000e92a00a5003800d103d9501c0902600c200740f050b6906441d00b0700400c0c0c843d03d400000b420a1141180c80780f004010200214200700068141025280c101240d54a414645005c8404400c1c561505104600c024402c2492944500c0400e03900c4919001138200020824011030000d558014080d03180a45004018558042070f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 21188171 1250 21186921 21186929
    0x522110708090f120703140c0d0b01090f0603080403060c020a050106090b031c051b070b030a020319151a1605030301050a080c0a090c020109021e1306081203040f08070507 75
    0xb080052281d108280a81406400708070504c0380c01c500c80a10000d84100691285400420221503035542c5160108000200c0703100d085e121512203000410080c1624014030070b540e01c40a0b4248030840c034696072000280190301005010507118580040e1b801e10811601c600385810000900c42950b139104500300919004880601a009140b0780203480c81903514050070b00746590303070b0303607498070401c165113240d0b601e80c10301030b005240605540040c1c941d0440b0051400b58031005001070780c3e810601ca81080602d03560f8800c52400f402d02004003410501c092007102107031411424520365182031941301e0701d0781c4a080e0582e5840c02071043c1000074010300102a50507075909450b9540d05076202c4900c3e640c3c40c200352612560000405405024002507504203981e81c082500022400015a9001804103500c2840c88203014892290070441890030601c02c8014011303151042040506101816468102d80141001c90000c000045000c020b40d00c90729a080e6504869882e446804030f241003501c980c16480317 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 21189421 1250 21188171 21188179
    0x207020414040b01090e031c0504080c011a041805100b01030b040f0b011103120601050a052a010615050306060304110307030302010209090610050d11090604031a0a0204052211070809 80
    0x91400503644001045804554030b00d040c8e08007080c00203101e003000d400c0c000c10445001c802440b4150b84480240641005030400602c5c0012101c01c003c01d000484905000d8040781e10314907511240416000b043c0c511001c580302ca0f001c90310003940030050380604800c15085400600c0e0007a00312414541e0744c070001d03074006d00b681c80c0080000e26401059032030207501d68510740c03008524003040c0258021f40080c00904080d007022405e058496002954018102e900e040d49225604180c5980f00c000380303d40340280c04021130b40d80380615807400040180c00010907681c0502c40000c0450103001d03c41c0105802070030020200e850322512490003c0c083d40104140a0150003008049621850222400081258141c2c0c0f40c0d81000390f1042c00d40302134240c90030f040d50b0b074101c204114015600c0341c030000c0010718012615100f8402500c40e5039a42c060008044505041c411301003405160303543c0100404042d0b404464132400c0350781204480091002951a08409100140e600e0070004c2d000003900c400d01c0100c2d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 21190671 1250 21189421 21189431
    0xb040c060311030f0402030c06120708010504050705041e0308041d0108060601050904050a06080f07060206180d050a020c030724030b01020d1b0503040f0f0b0702010f030207020414040b0109 83
    0x104203030155401c02d402040040d50078030010340c1d0a4420406998440c0c0020126009484c0440118210740d0040744400211602d2908006503150000a030f1401044203403020051407428600040c0140104e0086030400701c1800100750030301400104003030295800404d03070742c1e55596414803074044890b07039061110262080700000680c040c010690f14803401040c5c581d20b00c2c0c0b90070b00f0104401000020503150324103a41d200c01084031001000542c2c000e518482c010032003141480006890103000030302040b0f80d1b40c2c0342405a0100c82005c0744191213209a0300b440394450300301d0603040e0b040c10452110300d60144a004400240681d0054040c00070901a801c0c41c1281d40c00540100c081c0c448441542d80541d02401105c0c017090701c5101691900c00300c034654660600384c42e54420f1300755230140d8070014410054020501a00c400b59940c0d80040081d1107c0714a084a1580040c14441c071003084801416800f01d140402d43d100e64014510825284800c00c0a038501403170843c1e20b0030400c0c024150968601 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 21191921 1250 21190671 21190679
    0x30405120316080d09050d03050601021614010c050307060509030702041d07061b0602040e060a0f080c130e010903020a060f021216030e030c070602010b06030106050a08090705030304030b040c 84
    0x80300700c80410030308160800b1080030079242d0a500d03a101e1a0031098036641c4882c0c0c3da010402c140130300403a0354002c2c2d9000c680c0e4100b8400091810304042500c4a01a8004004100d100d9107410310100500d42824980140c1d6400c0c10002d00b10301800350302411890410b01004540540030005122a80c0300700c0b800c02041c0030b00c01d9803040d400904a06196103038420902404850301170710f90440444801c14504400001655650050781c009130301a05000c0307101020b0000c40e103441d00302e42005d40030050300c0c0d4050300d280010603640c9003022040a8042c00e008c0107005d1600803075400640d0301d8081000203000a103494507001b9540c1c00400000d0380e400749085440c0c080c40006000b2594400400c00300c2440c83e80360036034950428601e4907030300e50600d40d43d92120a030a04041c0081d02e1481c007030601420f2040d05e07040019003034500fa01003041c071a40c0200300500a60390003a003035030740c201640e162072081603a42c0320716981740c40f41c0c0e604915814803002c07030004108048444440d1080384103124010b00c803552 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 21193171 1250 21191921 21191923
    0x3030804030816050a031a0d1b0b07020a120201051303030f02010e0d0c02130e011104080f01020306090408031305030c0a060b030102130501080c070204051302040c0c0b18070b040803040512 83
    0x303c40303140340c00520708108074a4098400c0e08403034207610036071900008458a21000904841074100b007240c80a484c00e0001440d000c2d10702511000b4100180d529241143c41e07800180d01c000c1500995040d500030080c19001d692186060b640c18020440c0051001a1642400340c5004040a0714000640c24001081e4100310041200240362506031500051074a0395400c01210b148a10000205556507508400b0242000d02408000964041d4950b07500c07410103440c3c42c10702e07540c05062031280c2e00400512845032a02d01c900c81c1c0c030a400c0b00103a61a61a001c400d06401c100380000a8114400400d040c520170300003041004000c1d12075141001450510701c1454240e00690075044d1110803c1c1104126650207450a60b50090b1608089442e1007002e50000f011076006441c0a8014122015803404500b490701c02c1456500450070070442900142e0364141195900914040140e103100703000044407032080100c000905103281d861a100c54075140b00c11b541c3d070030521032680710b00d0400f5000744110070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 21194421 1250 21193171 21193201
    0x303020405131b110109051b100801030503180d050a050318040605030a0602070305040803030112030305010501020a020a151214060405010509040c092712080604020906070b070c020a030308040308 86
    0x40340241c0824103210f10400391480190381e04819815500d50220400040d002c0c8031220034441e95104001000e00c0c0740c001e0003008020750019105010000c001400822000419200324151050030a60011100c0c0d01240708100980b10046c1280300300c0003d41c040060101c064440d00580580310304c6c0030394030341d02008241e07a407501c101501900101c4204000c250f054005100d01402400c1c030900d01907451409518581c026800140686201c0b03044108059060013907a0051100748014000080142c00084441e0441e11803038101c0038090188015084c000c0c80c0740442c01d10f100c2400c0082c403101000020164070101c2e000e0b07215a1614002040700d00d0008a054046d9401c80d086611080c01c00d081c846c02007029200001e0301e40c0900011048142001111901c52071041100540304110014098841c80d405080c19200703038014004810b50b5203400c000e462441d03400800900d42511070000c196400c40c81000c01030b40051072001c2c040141908003038400c0c0a68426070341c03040d80359034581d079031012a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 21195671 1250 21194421 21194441
    0x61e06070605090109020d0803040201080106090b03070e0310020d0905060115020a060b010e090109090b0708010506070201050708090d1b0806101203022a030f010c14070f02040207030302040513 85
    0x18050100c0800704000d41d1041c2e80c8500184000200e4609a800044480035491021942c10000008110440d41c1c030003aa540140300078104000201c3c10903036a017029000040541040103540803040f107090740c7c100728940a840c81150700310340e42d02000070404080c00c1040c000b80c605209080c0001607141c180400130071492250360203840340d40855079075032018090712542507040100c201c10451465440b200d4035402004c41483c006000060781c81c0c103c142c084000e000c1014070103e403004014940790b860132070b12001e0f8240390150342d500d16490144034134001c030081c1580004003903172a0010810740043e01002d80a0481e6034284007956490f000d95544d400711100c0c0c044140707001d001c001c03280c40d0b42c10306881c003403081c01511404801606140300c0c10f0002d082c812a04900e03010680328605091107112a0111480020b204202e02e004c000f603e11940000e0394800010000740036000c0c04090040e00714000d0740200203664404041c01e0040203504035015691140b029601c1040c1c1d012094401c001d920 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 21196921 1250 21195671 21195679
    0x40917220503070608130506070309030201050604090b0703020f0c030301090905060a0513060e01020c0a0318060507020d0308130606080304051c0b0402011d0303042d080601050906010c02040c08061e 87
    0x1503040040c1120071a00c0a08412401107000c0c1b180f4000074014800203110f01c1059400189000107410000d094501c0601201e000d41d2418601e03101061034180c0c5c0720f900c840c2d581000343c5c4d5a05c0e8407d03918020712031080f03250b21602011002080c0300b20f150300701107900c500600813294a1f440e0801510100c80042d203059a2400340c0540410000b030b400d41200e00e103e4000c000050070401c0c2110001d040000040c1c040740000c0070141c003000c103107043d02c0002014142c50718009041501c15804a041c0040e0604080d080c030403c80001120358070002c4007001c1542d0b125400340800c07586e9882c22666038215000e4a84204440305070852070b6200600c403007a2f0b10b07410031000503507912680c0041d540d1000c0724401c40720146c0c0140c100c02690f20100020001842514104c1e00038826031040c242c41007041e440c11401092010b041006020000600603041d510200d880c000c10f501c07000d0060f148460380c00c10094201d42010401ca184a4120304000d01c01c010940b110300602071461403d000030358a002e03100d80e01c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 21198171 1250 21196921 21196933
    0x81204090b010507050a1b080705150c010b060406050307081803121009020c100e01090203061f051005031504020a020d03050406060506030f07020d050301030b01060c02040917220503 80
    0x800d4640c0c0d0000301490708107043c40c0d46007214940704c00317080000c0749009503000d2101900c404ca4000c01c200302d8500800c5904043c03d0903030b00b0107000030509400e590700c0540b0460089040a2071032029485002100303801422150385503502c2030042d02c01e0304121140c0703001c219003500103566855107201c140703c030004142c080d40c43d00c0c55080c42c0010071034015040003c46514200d0220394003031588001e00c80c1d481c102c80140084000020b5600c10760301a401181016410301d103140700140c07000a101e6400c204510010941c1c1030445003190010030165102d298000704c149100440e59802400560050805a14130b80c1d09941110a0200364468500003000503030110308004800b5100e941b00640040c4070b480041082ca81d503600040c4650011388180c1044180d000511a460b50100300b076078030307820f0309080550456146803580500801e052240a00380300c01c100510701195a0b07540716818040d803000040020306c0000140c600b5903046200810180d20003040803000851603007440404852008000740a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 21199421 1250 21198171 21198179
    0x50108070807081503010f0222050a0302060309150a1406030d0203040b09010c05030a0302130609050a0506070201050d0501090b03152403190302031e09010f050901020721050601081204 81
    0x100900010010084001c101031840d03411781d403c1c028109850070396000136842e40c0303c0301c404d28685000c1d6500300c007110000c03520402550701e40d0201081100e0301242c5080d01d0f6511800c00c6030510400948400d4421120340030414a00016403009800301044c49001185a48840c107041d0748100c0070b840304001d80d00621041008100c42c0004207003c420614006030750a143d683c0306840d5400c2255600042a0080342140b20400146a040018038851400001c69460a004183d5110040c01101c0c02840002922025640544121024542c00c2e40b420040c1e036a40c2e2004030010201101f040b07100c2e01501144d217501440c000e500500982c150064850807281c40c440410726919942c0000d03826002d418000b01c0c9440800c622010000c1c0607401440e541d04003c140c5c1d01844452290480d840d80e020300c55180f090741d1250b038171140c0b80070500700f07195a40784080042c0c1c60069281c0c801d0380c07605c10500030884454441c0c140e4100f29481102154007907603c846260f6114030a0091152004100f400104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 21200671 1250 21199421 21199427
    0x605070e131503020303070c03050c03060714031e090106140d0b01170c0907030c09060c05030d050a0b0d0c0806060603090d05030a0f0f050405070e13020607050c100810050108070807 80
    0x6a45094000c4002c038040766640d011a095400001003030303651400d0b806003001444401d004c01c1400c00030440107804140350419018003d0703c0c000f28035010680c00400060000b40008a1048240c40c07400b0088201c1e00d4421880f41c003130f2030745005400242c40d902200301c5c10344c10000000c154403944691032801030b070b0074800c5a901c0c488c020000e2695034403d0041942481e1101d014141c003030041039a002c070f0505003442c0d020303003103407101d0340504108010040e1312404254040144c800100c00b4600100705921382c0054800602800c6000540c03102c0072021110812100e0680d00b0f046540040a68481342d9031172080080b0342c0008c665110154110105080d10184224011079002c0d1113100e00080c40c5010b984804211912140c43c1c8a003250340340144800e001c002c01c0348078020a1020300424941ca807001c42800101d60483c0001d004a00228500c001c000041c0144040c444c0080c21b01c0c080b088607480c0c01003070000306851b4082c05040800c008030302c03944a19100c0d44540c0312034071620501d0703c03209421 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 21201921 1250 21200671 21200681
    0x10203061503060d02270c0a05070b070905030d03020904060b04030507060c03050d06030b0114030d12090201030f15030201140a020303060d02060d0516021e0606010f12050a05040605070e13 83
    0x180740d202240e000c40030016a246c0314103c003108242d03081041700b1464044c000030310600190000e001c101062103903402807076008007110700c056407042034049d0984602c0800c0d510104583c00050f4180200010520003a42c194007421141c00f00b00e40034490155a10300942103445203000c06003c42d000b00300c0c18030250b03010390304883c5843d11903e07103140307400d1020060008483c4642c10490b0284e050500410480f105e000c0c0642c80c844044003d4a000400b040000d00502c104003a0800000e441d0160401568002e9212288040100308140180c0315003071140c0002001d9400304030f000c90708050130136034681d5244082d02c1a1a080781c005500e1900c50108200e0140d260840c100d0340b20608101c0b8000c40700301401400d015107035280d25401145180c1101905128210258030380103a201941440710100016419411900a080c00ca010100300038085540d103110091380324a182c1007909010b04040c0e55440380323103d213004060822064491941c01c480025070907040035441403103000b20090025640d404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 21203171 1250 21201921 21201931
    0x60f0f03080a05040306060305070e0f090604031413091407020d0c0f0204020f1206030c01020c0307030b0601030e03030c030103020f0103060302060a2a0506190501050612040303151401020f010203061503 89
    0xf1070a266595440034191005a00111000e03005030718108550340d035043c08503801070103c01c4c0c1c10f002c0e4544036414595070040104003a04010f81444000150740400781200c500c5118802c1400c441500c1c4c801d82d04c090310107600c10351602c640c803c0000d594103101250030350701040c280e91214040703041078030b4207543e120807014140d03030060f820412a040d403c1d00e900104070040019260604615000c42094103024540c1c0c1040c0c1590041080068a50b40c003180400989a0040d05802140c40341d20040b401000714101140782440f000060051820f94080514102c030b10032140c1400f05d01000e4011415a000d41c80020342005085c400c00f19420b0003451080c2501070136458050700101103014105020f0410f0b07506941a80047c02803042a1200c00d00000340c1d00c0d9076280c140219454074011034998814120319041114198000c2004c040c801e800c13804030402400c1d0707116605902e4048185183c0c0f480e900d040d0142c440c00d20003030007080c1c06000340c91113000000c00d200503072800304e82e0035800703a400208 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 21204421 1250 21203171 21203177
    0x1020312100b1801092705090c1c0b01060f05040b0c12031009050615030c0307030609060605030106030f05190902040204120f0512040e06060c0c090c0c01060f0f03080a 74
    0x400400c4030400d920243c02040c01804507810300030203150000d0501903181e0801e001d0f028000c3c0ba0206900e209240709104080c0e01480010f00ea500d200c8024100820000416403001c0e8040584a261504007411038442c0d000f4040548640d036144426134180304444c0900000c01c8007800100000800140509002040e51003640c2c40d101c03104440044c0343d44201d43c030400d1601d2800013413100c00f0040c402c0c0342d8400303010382d50440040d00601c116203a9000081003001c41c01030010004114070300c02e81000d4001c001e082818012280c54000180c00b980090043c0400646000da80c0741e840b40c460300900c0d0003952054a1610103904580c1c144000c1d05007428240c0e00aa000c210001c0c14030200c0454550440c0140c50840c2a42481d1400600700100442e00c80c00c280d03001d0006016500e060b18001c1d40142045400c83c0e510400c4000182c1000409404e0744d5012111008110248404400405041800304000c00140340c07030342c0c1442081502c03401080c1003521480f200f0710004644a0050a070048141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 21205671 1250 21204421 21204451
    0xc080c0106060206010611070807032303180103050a180803061203030901020c0706090602060105190302060324010f0e09041e050102180f010c02130b060a02060108160501020312 78
    0x126a19080d203000c0ea1101c00180c1c0100d00402c0b60643c82058034a5000c2c85601500c4680c0c43e2001440e5100254040a0b00000c00501c102c2c1e8000b2040c0c4240c090f0300e40d040d060303030303100d009405003400c0060f1000ea542c1e0100e410180003030314007880c80c0f00d5540034460308008048800f40340c4d1284203203078000802c440e402021140e80d050141c0c808001861150705220005a40c5040950f0000c0c1447d08990100301803042d003501c203000380354003c601941580d801743c512400445452501a009041c10350010b0b4100e040007084c40300c0d54110a41080c02810111050f0f04e0341c0c865030004440c241500c4000d0070008040803100c0c182860064800d503041801031140c503050340b4503582d500c002e005282c0011141a940003601c003420020744514090700703540480d89104180f87d0b0301d00192401114400c02481880c04006540843c02603a000360034140024002903143e07002030002a59488080c003403110903100d20040004a400d44410034000c1d40c0c0103038040c40c00c0080d8803402240480002e00140c0f6440705003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 21206921 1250 21205671 21205687
    0x80901020c0709090c0b0a0503130318030302030a110304080709020c0c040507110111030c0703050c0a1b030203070f0302031507350603010504170702040605040203040f05060a0b100c08 81
    0x2c1001901920305200300107010303082403a0000d0b104902da0302010141200340000700d00c0341d40002c16a540129510711520703106000b89001c940c40640701c2000d064906c0c0c2907174040305055000024000b03600c00d07174a41380c02c940d46041d0401d642c1e02441c401c07170b46542e2180320280b100501c1c6070054038402c02e4010841e1000321074200058103941080705e520300080e401e0003081c1e82c1d004003401803884c1085558222403440c10060b012005071310030441c0142c103100b0001491028640304108055109800c1012140f0450740100340800c3c3c80c0e40e9101c00e0340710b445500c00c0441c41440c2d1032070410860750300900030b2000e0b1411800c41c40d400035008200000707000d01503400d90741d100032030041380401000e518000081c070a022006201c4444010b0704080c081d03854202040001074100581e070000b2000d8446150322803c02e8800100648a01d420043d0008c2c0040305001c10030640c0ca04a0a465205609680d20350350344404079000c45a6000250358840c444401d205c1f0014040e402022600b40500c0d40d0514010030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 21208171 1250 21206921 21206923
    0x62d260d0309030f03020408060105010f053a06080303010e09070306020408010b01110c090c0c01060b04030c05030c010f081612050f0f01050a0302031c030e0d0201201603080901020c 80
    0x1519003140007198998224900305a40a4006104034800e0f040841c02c2a080500940d07491320140212814080c44500403400c4500800544407050302c440c5500102c1a0307282d402640b81080b900b00a22000304201303200d000c16140340036003402d40e003080c402941140c0c0b82c515100c54160002c1c03c0c10701c16004051010001c164140001d0002e82010000800c0905c94800018610302c1d072a03140301c1140c0c000c090b0f46542a079810b0b0b81e064000c80368001c01c0b510340c1c00c0c11140a0050600e03901c0b20782441000034000082000d1000d5000031600201d05482d0001003c10056560603c80d090300800505038100040001c49150341410643c5030614048000f10803441060701101c40a0f615100c09081e00740c100841c08015507400c030b0150400780c5031603050520f141c0c04680d881c040001540c081040d80721401c0344680c400e900c6414990001402c5403e0a0f400a0010b4024a103955041c5100030010042801000002040f5000a6076a4410295560080e142115103c1000d88140815502044070f0402140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 21209421 1250 21208171 21208183
    0x210204080304060c0c05100503280c0909050a05010501020a081606020301030b06040501050604080c040f0b031c020106050103050105010f030507020a0605150108090a0317090c03030706062d26 84
    0x1140d85501205004c42e08150000f001281d00043c4901a0400b07104402c036804010b9130340241940742c10050034903650101c1d9881e41034030b00c0461402403414010b90310559124668600f00c54031244d08102c181c4841115100b5268240107180c0980d0cc001c800740001101c00b002001840282c860708590004070f50340d107100307070b030310a03413003616081d4000c004d02200d8a014480d40e801000100c56141c60607242101450b240e000c000a02c6201d0b03981c2c4c1d406000b0390081e9070841503030301c000141551512801003480e10030f003903540382c0348000640c0390120205e45035010388030709410303a03105031180c611110200c1c80c114041c100080c400005c5000b003044031000141180100f60058810043d280d01d407801e014001000304400520031551503200000100c02700390425048071070700ea61560891119555840b029140c02c584041e910303010b2000084402c2400f80036481035041d07410141d1030031064699006074038505811070440c400340001c2180c082151010304c00700f01024402a01d000307031252410800c1d0b1170801c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 21210671 1250 21209421 21209429
    0x2010c0c080303150f100f0e040b04020c010e1605060f0a02030c0715030c0207030b150303041206020d18030f1b0218040201030506120d1b050a050703030809010c210204080304 77
    0xc140c100710b40740fa40740c10100302170440402e0350b90312140c1c150310000512540d150814070b0b0034425002e03008401d43d00d442c0c202190204c0040d0040d9915040920350368020062402501107038000c0228200300340d60049030080072108028881810b246000410000310381c4285d8001d070030343c8410845001030540c203004070401400a60040341922400803809001d460003980da200454020303190a00c001149550307519000301c0d404030020444980d290100b481c51247d80c002e2030800304101081c40411100d070700200000c20804409105170b4480340412620034002d0f00700140442d803840c4031013120701d1086505569103c2c10030b48014014a184d00420310070307403c03440c01c0703921183d4446c1042306558140c040c40750014816a00c0c80703407200380f0741c0e00c0689a0015070305400c108500c60000b1a50b100c8001048060b5507000740943e50f02c0300a502c0c1c15590341095100c02c6010844903000101e03916010302c5880100c2015894903104204a041c119400a00c0c0a483c925141d9080c070010136002c4040010304058 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 21211921 1250 21210671 21210691
    0xa090e1504050702030405090406020c03041806210f060c230c01180f0803040201020c0a1e06050a12150f0f14030a020a0509060a0b030a0212090c0d02010c0c080303 72
    0x1026011041c0420340b107004215406661042104028640350158040d9105420584c0142c65a01541d202800c510590380039907030000da107040100c2417201c03d5000000f16250400070070211800e11407030b00208460701c070000e048988289030280c0072600303e070404c1d84003c602c2d1602e48200c048007082103401c0710b04901020f1040b40046642c160f9100244144030142c3d1054030011401800703952480b1100100c600c00030a0001c0101c00b00d400c69008210403015250002c140d594440d0312029090802040110341c02401c050201d00000c416001e001100d0841d03005647d0007810110b20041c400180c12403882003550007006400020702400c130502083c004d44520850100c4040c544410382c01a0552000f005104e600300348100c10042c1d0b00c114000003107842c00c1d40c001a00d507607110700050351007603180d00840380c000380001040600c0110f030b0700800c00503900e009014011788070550740388da540303156001458214222540c6034000d503005562003081e16115103018801c2c3d41d04d50307455138155081a00e85c2116 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 21213171 1250 21211921 21211951
    0x2011803121d030c070f05060415030608010908121003020609040c0e100e090f0c070b0601020a05011b090902030103080304020904231c030504050c15070209010806060405010503030313080a090e 85
    0x31104c000e00c014001000c000c6962142d041c103240029200788660711420054003104034640e28030354080d03080030b402404014001c001004036420642441c3d40040d08005501c14100d000030f0303d42565030426420350f500a01210f01b0008450240401004240d031140103002d0003068100301503462080e000400c9120360b40345144416a001802002da50181004040d00d159504001c59070304040141ca00b0ba40c0c03c032040d02050f444080c0142d0504061145c06000b039401c010320039010150000c008220000c5582c0e590880d6683c4010303c030203d01007800006c09800c4104041000351130481d9070b0300e1304580100706400c031100403202444c442100000c4100440d400030084021500c440b100b0300031761510035003030900c500d02d402d85e500380e150b0f80000c1013030740310b5011000d0180c01c01014909031521a68007030082405035854140c25603485c082290350510807814280003241c02c0c1400f00c29030380039481c0c503801c06140105541d5882080e803c400218010000070120000d03c03040020701035802880d8000004174 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 21214421 1250 21213171 21213187
    0x807060902180417030612030703080115020703020a0308030c130e0901050a0c080402040504110303120105091f06050901051204060e0c03210c010609020406110c0102011803121d03 79
    0x2068608500b81981c90055100070040440c1c141c000108840e10550891990780d07951000140d07601802c07408801d2140320104824081540210110381070710040c0014090a2150f480203da07110320b5400f000b500103000c050104006041380000d0760300007004404071400c0000400a0140c52407003a880340d4810b11580090000002c001c1c0b03d61074109040d1340d400c0c41035400010b03010300001c4028100a00440e510000a01070192007203100348080c60040c283d03a80ca4104038055200880d080c00b402d0f1240443c5070100c2e10500d003c00a101d40f0341d81c880002d45140d131420b04103590700c1d00464140da040c814100030407054099a08242c0788610700c12040056402c0100308054500000620918003d07408803182e408074402c0d162004103440146662b80e035540020a510a006d080541d02206101c2d001003004503299420400301441104150308942c0c902030070100490a03100c44051b03120704421100e80490111307201d044130101c155400c12000c660040c0000001050086a0311220056040814106 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 21215671 1250 21214421 21214429
    0x15090309010c080421120f080606090409021203040f050612011e0503010609020c010c0305091c0201020d0203090703050d0302040e0a0203070201020702030706020706230d05130f030801030c150c0201030c0c0807060902 95
    0x86141306084c40c200154609204010304008d0303018001030b11034040481c030380310165604d420120719180c1c003400b006061542a0758060f0340b5042400f0f111001c098110340842c1c40d04100f001d9520700e00c00c000011101c0d928210000703c42c5481c2c0d858039140e001307a940c00401c0720385090107000001c00480400696410030841c2c0e00307027150421550b100c1054284014084c03441000501d03440c80c44000c0c040042164900c1100380e009101700040c1c22010790012040240001010415030212406007040c2e40344444500c0d412000c900c20350144450101d11500403898100c840d034082e680c000c1050000501d0319030703180c0009103000415449440141c0c00f00c0014001236900054000511100044805c01c595808000c480c1c00d01440501201e03190740e4100180000c8281c01c049001160050b04000103040141001000d800d000d02040d038030821812000071b0441c040400c4811144d1007035031402c0a184490380110b0140100d00989010000c0c40f00c074000200c0e48050040000a1003050f0019518440b84184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 21216921 1250 21215671 21215693
    0x3040b0a0605040c0207060302030601090905040b0402010f180e06061b0106051009050105030c070204060e310506130203011b051b0604031205040804030c090e15090309010c080421 79
    0x1603020f24289058920740f290005524015070721b03981009a22075403030100485a0032036a500a443c1d41d0306180070b101c01d02000341c3c2401d00540c000c1e82e50b010b1070865014141d44425411002440b5020f03141c5c0c0070403400c0310000d042500100001c144918100c242c3c107254039109030702004410981d666407420801440c0c8441c440d0b03900c5c00ca80c1040725981e4608030000c1c2041c040107041103c0701d04000382c544210758542d8801c6000d4003245c0043d060340e003092008502142035450501000c03491800c0d010501111a0803500440c990140c01013a03140ea60022484801c1c9100e44202d1301076407035040340268030040008140c1004459601c003a226410902d04000703401c110740f180d8a05030044010700000c04e0b441454980c094081040116007900e0750316005000344110790014004c0d0f0f08518002c01d4a03030140c0c0003503480c4d001c035400f01c43e010480f03035010010420090f84d01c0701155000300b028560079405006a100c4d40c034065051075007829500c2c151141080d05804280810341c1c228015281004100854 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 21218171 1250 21216921 21216929
    0x12030915010806091b03070518150d121d060429040f06080403050d050c0a0305060a05060301090c02100606050301060f0f0906030b0d0c03030e040f02030c1803070b03040b0a06 77
    0x500050402401007910b80c86241c280d0102d9810001e17031000c450f00c0802011009010150403001801220300c0e03213659842c1c0c1a01c21610a21000e20707136040c14513200e1203040c8003e03044406110041c46001041c0c3d10360100c1031a00c0008101c0c0c00d00c00c40780c0d9403031070301400040101c04440701203ca1030083c0383c200000c407920386174080d54042c0401d000030716124444000b030b1805d034204000e15440f1400c0a5070320380104e2800610b16414081040002205072010741440000c0b030324217001d03e4a03450204041401540541030700407030103000400c004411a000820300605078010b854504001186c40b0341550010b400280200d580003004105843d03000752003810000d0349140004c2080c0060400600e0035007944150340c105501c51011341040d58501231502d40907a40300b40703a0020706580e4900075102c0d10100003240e11403490500207034540f000d40c3c002c41e841482d061039810310748041042803144510f500c4443c11b426200f0403202081c20001e003070046006a01071400e08142d86080c0b40c0400c03d8441d40d0300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 21219421 1250 21218171 21218173
    0x610050102010e0c0108090f030301030c051c050c04110909010306050103020111030304120507021201020c010f0b1009090e0a120503060f180f0403020f030d0605030d0e0d0602030405120309150108 86
    0x2c08010072610201380c4c02d6a5890928040b07039a511000f240b1490640d049071035039028000000004200b0050011000c100c900640e00c0802d111501044a00b540c540e007000035001d0340115440940321b20b09940111500411002d82c1d5003009480000700d030402030260000c8070095031712401030041d980c00030b50075982901c0c007400451442c6499070b43d1580700c0302a50a204180580030404104643d5030040a0f0003c40c0002c008544880040829a02902c12002c0c078003030162070080d444a0a0078043e540b0600c4103203a0311751940e00c0345000055402441e506e140e59049018106244c2c1c0050040c40726544140c030740e41c1d106504c81c182501000302c505406094184942c0068008807074240d400200316a115008030b0300341c055650341e42001e0782000c00300b110000380f034000064064010aaa036201f5415a4410780488540c918004000d90f40409555104c4d9889000c0400c00d170300007001a0003c5a22030312501c00d552008050710290704e50354001b80c45000c2c0a400918100b441c0e10b040c03810150060103080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 21220671 1250 21219421 21219431
    0xb0a02130902070602071a0f070518060c01060b04080304031a0f0402041a0316032a0b0a0e0604060809060702070e06060a03060b0307021f05150409060b12061005010201 74
    0x1501403012a1a00e1142400041d000300d41c0301c041c4a61641500c200580191240d0100808100f2180c4117650442d001d126050184010a10f441d102d801600c0d41c1c0d001c0100f80c00860969002000f0301900725a000c10744564a5480114411032000054001010018000c585850851a09120b000010030080422007021001c000c5021400052590000c0c0c05840c002152649044107100c004003039040703103070141319003d25008054480c00c01030041328090150840b6246403841070003041403900d60300da65240c030034007002e101e2082a40020030072031046040040c001418100410b1058000d54080e1000c1909881040b580c00d605215940d401800703071014050081c140070014101c2c901c094000303400345002007916491180240e21607400f80036405825502c80c509494002d40d25003007010991a229151800710801c15500d000f0b1300d010752154519007a10b00344910a120040c1900c0009944190700d40801c20690703180c2c080130030000c1c8071204c00340c0b8203071408000c081010b588941c8000e04580c581 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 21221921 1250 21220671 21220687
    0xa32010207051e0309010207060f0c0b0f06030c030105130b07020a060c0905040b0405060310020903010605040e0102030405071205070308030721090b0108070b070602070609050f060708070f0203030708060a080d0201090b0a02 98
    0x104403d400c4d89c68078240308081b0080b1580c12100044078800042c5058012014000e4070143e010348240304a00440c1100d0241e104403083c5800d03158241d40740124041190481c80002d0030143c0844c1d448012ba00c1103500419140d102d40c015940c858240e180030a4508000b40003904240c020b4180110084d50f0070701c80360502d480441e42d122106500307042101e27404176149c41a91340030b41200c9d0092800500c08c0c003403450386580c80c0f07000b90702c20745e011590380c451b015000601540201440e20380700d81040142003000d15503181c410a42e880108084108030038450101c100001c407003014400d0341011480003c00c00c0583c030705494240f1045e004030703a0640c082e002c01c1200047c038070200c0e564581d00190161f1580c2680c5448030117803006c038030010302c40c0c003c42c0d43c21412000b001802911424242d9130720003468032180003d0312801c106204243c0140c10400002d080240a8100150492009000810500e81c2e46821a00b8011400041d0780141d44074601d0f0014003c0e00d40c415034000a1484007146802c0319 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 21223027 1106 21221921 21221923
    0x90605150f0105040e0405211e0f07021504050409150c0e010e0d020a051210050a02030702190c09140f090a32010207051e03090102 58
    0x1400364600518600725612001250041e1540f92a040c100303070311a00c9828004100703544c40e01c51030884400c4104840c02c031101160070011855242c20141d101c000b642c000c54004214000e8003403200021440741c182c100c1e41d010742d0440300108000040101500700d40681c0d032140303600a181c0003000007486403011105002d010700e80ca0030400f40b00800e405507070320b4000191040c0003a08050a521050905400c449400e9000a00e000303050b9170341c8e500140712803501444c89801a042088180f1005403580603080d0401c1d003890041d425443c181000030340d030b5280015800c4c1580c42402d00042406141107803103000d0521400b0a00c41407040040c9550880b03070a542c988640c001880014485800204900d4070b1103034050050a1307d016810300c0550166a418000e10000d903806e200803c600c0c40034802031211910840103005000c02c40d1007010242c1e9651000e0100640003040312200907a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 21043171 21223027 := by
  have h0 := BRFrame.cov_init 21043171
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21043171 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 21043171 ≤ n) (h2 : n < 21223027) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
