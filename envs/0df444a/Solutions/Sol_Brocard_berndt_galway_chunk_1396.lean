-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1396
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:46:05.601565+00:00
-- url     : https://prove2.me/submissions/1f684fa5-8e57-4294-8fe5-39317dc6c310

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 250899280 ≤ n < 251079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 250900530 1250 250899280 250899287
    0x20616020f1206011e0f15020708060103031e02151911160b07021b040f1113050a050d050307020d0c0509040507090b0607020f090c130906090e0109051c 67
    0x280445600700d02d08203958601c914011a603d03042c0c5074001070801c03483d204010341c03008148031886440c1c3d0105095106014000506c000c01c5680c00803881214821501c8a0351541001403e0344100e011a10128110101c14240c0341152003500003400030300805031407440091601ca100520142001c05840401240c04401e03034092803020380c0e085030351904c0d8145a4019100d0651040042d1140100c0c400021b00c1d40e40f0000b0032603540e294490390030080d0140041031002130b0001c0803c02401c50b848001403034501d80440054090070307100084255585242c42d0078402d44d0703e61030f00800d008a031032052060104e1030000442d0121507064580c8154503410381450105580c868126a44c00741060050000340400080c41c44140c4423040801c20414070302d0003c2100328454450001d40000500300540c5281c60950486903000b5400a07050f460007242103a01c503002030f0703150040c521650b0799480a00c0840158480c096000c07007214020040c080c0142c4440d40e49581c01850511101800400b40340090f11 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 250901780 1250 250900530 250900549
    0x1206040f080f0a0201050915060a0303030c051e0d0629031b1605072705070c05011e0b0406050a0512010f050a05010303170708010611120403030c03090e0402061602 72
    0x5044440d034883c036035144001e000c1c01050700c0780b600c0da1040d1112180b6104004030114010400140b08a08140c61650140c0250a0b441d0111080c440d060121a071050425181400703207000000015aa03030491f41007180c1202c0e00c60b00025107802010642500094020140708280c10070100416140d946540c05a031140500142040d000700c0b0200f20784003115403940b00302420b80d11a4003030301e00903a10b0305c11b4080c5201b045c41c610348100c042540400a0b00302c45902168000e030b00340c42c00f40e034040b607161250742c25a030300e6041a03240b03a000000b6080380803070288520708040d0412102809414640f10000e007131026180203c074455040a198035110080950210311800b00240042c1303d2880c00e24181001003109202c181c0c0802d200340c214040c0904042465841003e00313440310303200f507400e080d422200c441c0d170260740d84098031a0030702001c14074420030013400045201e80d0b51502d0850140c6002004121260701ca40c952a00403024080180d80d08402e480d0748501c0c040164410038440d0000455204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 250903030 1250 250901780 250901797
    0x906030b0d080409200903030f0a0c02030d050307020706050f180a121101030b04051023040614010e010504140d03030b060304110126010b0723010c0e1206040f08 71
    0x141c00080000f4400603907013154034803a174541c007020f400780407288080e0b240d8414540312a926030001c00007200b00e900c03c04040c003111007081c500800b00d10215804280344c8000c2c8559900031820200c204207007641e04010700710141000c1e1070720608021030030042030198001e41500070001000707081490050307214241180c0040c0882c05030340da42c0403494240003078030032800148180002e042104424190506019042c050a16024003400e040e1a041103000300200031a00c4442600780d4142d9076200359920f0041e000903040032403400c00101201c900141c04060021a0681031010a01040092071900080201c0c0140241d44c54040c44c0c40a1030b04400034100d14000036408140441400240000d0384000b4680540c00c1e207440d40002e200c842d1914180f403011280104400b1000e006105251011001d484400e10507c000d60b080a070460f00c100c1e00c4000d01072003409603035540f000c04160703d501c41030300b516031309054a00520b01c0c6039003200301d5100c0c000284050068030142c4042002c1040030411602e092 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 250904280 1250 250903030 250903043
    0xf0302180403140a0e0f06161410110d06061704110f0a0b070201180b071401090204230610090509060a030b090a03080a0501081f020d06171c0906030b0d 67
    0x1048460b00281a002045003d28000c4000000b20b00c03541c18600c04aa0340c0308d829107402410010541d945019862a00120741e5160081038085581d0410b5809510304040c20130821540702c25240d0980f10454616070700c81c602308034071500e0b4951050380380042c49070055004104a0840c00708e05000c1051a10000d22098120501c0c44000450617130304000380c5000f604c00da076500d070703460726407840b003c98800ca901031707101c06400800030000080c1148100c3da281c6100b9200108008942e500000c2c200e65000b181021111106038803500b8500c1f40300f1203150b200300200c83c0e20880101880d4010300104007801201d00803601d881c08102d095841c0400000210780c840402c107864035091035050740340c29050000f14080f900703460101c0e00070031081c002c241c1650401801082071100c940001c0b00c240700407540c0390713983d0baa080224000040c2280211070151501703004003036252900380e01d80d92606440b503c500f0204114034981d901d159501c144050100da403107260114000c1003a900040340c1d0b204402000b4041d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 250905530 1250 250904280 250904287
    0x10f0f030917040303030e0601030201050a0f030902091305071e12080c01090303021306051c0908120103121103030412080c040806130318031101031a040c02160f030218040314 77
    0x500c10080b00400a482c403c1c0c0d03050140c40800b8440d1561502c0c2808000d01044003403060000152040000c148810440d14003c41c041c510746d000300f40015410b641e46408000c00d864450240007003040407400408504050b09680b00250365805040c41c003070b0242d000482038201c410f4082c440711409940003102040001c010003045883d002d0000d5001e040b080798108218000015100e010b43d06850300c442c84500200c0c8000c8206c20701c0390041003040000c5803038150038002002e4420705485241e010f980318041b58110400c01c0d2402803c41000000c51078a00d51007002000001507040d141c085c00008141072440743ca0329000d188010501031908100f0a9210362010040c6441d180c0600c490f001d402901c0b00300c500541408036020581030380c00090300d01e0040ba40b240b40c855100341e01121025640e5040c100c05d0756441c0c0d0000c1d05540203208034000503480040c403080744a8820340d08a000b0701d900d032583c5014524580c08140200c560840d480001010710000800345401629002c0c184a610f0b4080c640d03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 250906780 1250 250905530 250905563
    0x60b03060a050a06051009140a0b04080c03060c030c120a0e010207110f010f210204030204050a051008030a090b032721090d020d0501060b3402010f0f0309 68
    0x2d0030300f2100805500d00341840015241480c0380d9910954078607580d02e140c46410135841030390300b40052040c0ea1700f103030514800055000101015102900d0007030040d06010200358101407a0190103041c010100d0340c10070500c030344042c01108441034003c0111405a41384e44001e84080241803001c07480c030795075000080c00002c100034860011080704040300d810b032426001e24011a01004c1c68051400490307400c3d030750300701c2025644801009882d008a005894140c407035011806031003042c5c803461549515001409519000c0a4124000d0b10303000300250709021101000612400c1a4031410f04c0d0030000201203100945170700c0310b580507503a650f00128484604504040c1e41c1c0c01c6011014018a1401c14601502c40d144000f210508003008008a110541035020080041c1c100081114a0f641c1ca0700d001400c4440c00003d801c100c1e2000c0c0d2410071070000050307040c0707420300314400c034170183c0e06a0203078040182e800c10103003804c4071513900d0145041c0c8000d6000fa0000d2203020000382c00a00072480720203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 250908030 1250 250906780 250906801
    0x40606090f0e19020306040f1502040b0406020f01090308150d050106030b041502130e0903070510050726041e060f0507030c2f03040b160309080d080a0504060b0306 72
    0x8a0445840708440f40c4040941440f14100441c02000354180c11560114000c688000a15400ca0b80901030507441c8600e8016004c0c1288d04c1f81e88000c100351008901008540e4043c00b10421204021009000444441d074000700044001030841e01c1010085903403030380c0c3e91a00310500c140c80d50700c03400070000039441f030800c40006403003110111052480303035211540170440d03802030390181c1c0240e5030480d403c681400c0c5118840c2c10000d00140242c40240074003400b01700d04004032612150100b40c00541418000da0040404c400c0c541100c4000c41c1c030300420382e00000c82c03144031355100f5044a481c582005440c41784020441d4061005080c1600342003007420b504004d903009030b0054115450070008044045010f0f140c110882c0ba1002600c1081c180b0202c00c0c80c00c509480303030381c15101c2058918054907100d028000c0d8105174846603010034200007440402d50416600005000b10310001c0144900342d120041040d10000d0091804c1c4d9100c0700401e0821441d500120070a401c02802d446540c0b07044103029 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 250909280 1250 250908030 250908041
    0x1020c060103170c0d05070201030b04050a050f0a0c170c0f0c010b0f0a0e13021903150609060503030304030e01022e05060f210a05030a050309010b15070605040606090f 74
    0x20388201c0080301c2001410f410903011102c08030700c1a400ba110030404100191510342000d4003e070f05260b151b014681860b40d47d84202403094030000400039060074032035042d00b0221001401440c6040ca0544030310399064202c2003203910246074110f144450b0b99522a104694010070140400c1c004022440c280c2298042d004141d401c04252000c1514a20f82030030400f541d0390b41e21405500507007050124101034200b035040d0540b64006040b4108803208a842c85407250190740c41521182c030003940c1e01c16100158015071000b4601c00d8020300c10a8140340c0025200d20010380300030140051103880d101964001d100304064064107215408000301c2c2e0ba0442007014050041c860715980c5424001400c918103406c0700303001e940000e88101184034a40101a40b12141420b111016204180b03401001880800091018034050360f03420340c40f801e0512109094032440d0b0340e002e101d030010008100c014000c540655224542010000ca5076403102d0824000821550b00101800383c01d004d10314140000d140c00c01d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 250910530 1250 250909280 250909283
    0x708070b01061b11060702220e1207022b08120108160b0301061b060c1115070c080a05120103080a1101021e03041e03080601082203050d0e01020c060103 67
    0x1e0103c50b880304040c024000154010052a841d0001c0c50350000d8280f8402030100d10348090025070020384a01d0042540e003000446840526407599506d0405400c1480f1404440703907100340a1342000000d600151038010802071044100c81c0d442c8100700301245203071080d88115000300072a541e07030381c400c1022540070343d0034000c4521911032a01c81006d01044c0426010071144036920060660342000e5080301c4000e898070f406003885254040382e201088661140c8060940e194450007050707089500c00d141804100c01e001c00c40d1900311008c00038215005600d10410a80c000c030166640d101c1c01c00207403198081ea4038801604080314002004100e84c0500506c83d980c040e441d144003031400c420844d400d0748240d2a00c591681040c00400800c1c0c0c0d4980c010f140c00c03500c2040d0700740c001e4004008056016200b214182e00003104035003030180a58010710099040b10b0724400054011a03003109407401108002001004c0110010b240d90410384184e100d54020300500009564030681c0b080c000366a64001e010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 250911780 1250 250910530 250910537
    0x2011407031d06191107050303040f1707030f0303050a0e062a040b04050f01030b100314060108011508060a0503070e0118050709060e0301140a0507030507030b01050904110708070b0106 81
    0x14407002d403601ea8141d90030004104100350070040d071301c14100d948280c00790711805144901c503c04105981d042c17014002034a400c400011138207180110740d103c0c48060050701c09450300402014408640c000c90810600340e018240460070340c682c50088401044826035440050040500340204184642016076140e2010381440861024501540e03c05124034465040c806004010411003801c10b0081d424400382d05040001d908841d5501103070f20250020306400020741e440b250105900c0c60f080c0c146070014170030320b0700340815814081a003814180c0b00c84c0e1a4180000d140000300140c0d68018040e014280240a45850381c0ea500310070100b0000078020710f1300c0b884400c40340e8502082c03544180e03840342c141e40d038514013414a8107005441484a24000300d425540b030f4104480c2c1045403450f064001e83d60181300050500d05103000030219400030b8402020541007082d0180a81ea0201c19502003400c02c940000d540da4500112a04520071010700a04016004c01c4600a204140307007140d04991894a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 250913030 1250 250911780 250911827
    0x130303020a060e2404020d0b010b130806070507060e280308090610120503120403120e0a02090c0c01020403020907020f070602150123030f0d021506030d0503040201140703 75
    0x180d41911001c50340c50719131a6002e25125140c0000400e100d403070308140090a44440c042054a03401d9800c0760076042005401800680d0070b10782051004504000c240e08006003d181c10020401483e1b8450024080c1c4042e4981501007840081400515090141c405540d409203464901902c03d2001440080c0c010880910001e610305002090461203848480340720000d9500b011010402c07000e600c00144e038a48814007902d01c60000306004180030754000c1d12141c01c06442001c1c61001d844070400b80b01065008402001c006841e45ca03a002d1b00210200001c64030b030001180f20b035009026030b92001e0b600c401c481d030038044403d4001c10412110711015003980d41c0316840d007070148c2e80c0d002c0300043e0038003036500e0300c004108182071039200000c81520400380800030980c542c0068a00064428400200e13040341540d2020590100b00701e88501d6003000380d0080c203140c0000041d4452440f51035000034881c0000c0014110fa01c038000c041700e0b86181003603a0381c1780c05050074000e1280649040d0102d4800285 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 250914280 1250 250913030 250913051
    0x207050a0b04080a170409050103111e010c06021b0a141608060c090a12061b020d020c06090a0308070809010f05030c0d0902062106030d0f140a05130303020a06 70
    0x10040b80d0640e4022030060590300703495034034010b4032a109105605444800d00c004141c0e2406402401e00a60040c410308a07084c00038010000080032030401c68a01c122400341840d10342c0d80019066540c46c0d084200180c0780d0055942c404180004001d0802d201d004070501382c01000b0f0810048841c0404440480f02001c00954000b07040043e14050b01215611003800101d00455242c0180328440000e007041000c1d41d80c8200400548095800071100b20b07480b06a00c0701d4400f41d10001042c021040c1c4010b01e00400b0f00c000203500c0700c040d03204042c080d010000e4000059203d2142c1c440c01103a01c084402d40d14030f02410a965541c0080350b4041c001525002c8040341c01c1e00c90000e880c0200d80310321340c8921f0704a070910100d00070503091000b00e801000901040d001a01125061071010681d08168140c0745440340416040031741c2d03080c8001c10722011603454903169604c04000c042c0d204103060b4480d620f01c1c0034003003994070f801030402341c40d12001301c0b50001c020036a01148040340c441c801d03101401420f412 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 250915530 1250 250914280 250914299
    0xe010f0909080d15090c0e040515010c0b090316050708010c0203090a150c06020c0109020a1e030318090c090302030c0405090d0f050d0507021e010207110409150c0207050a 75
    0x1000040c0884900744054030b401c3e0840d0307001c3e10200c13407144c0441051075904c0d030a05c401c3e1444056840080b91803810141039505040c001d0541c04000d85180c41143e03100840064042d01149002803d0845400c00080c0032580c104200c2d004845208034000426560313140c025030341d240c607009000455080c000c12901031400001680c00c20700001b89011051410701c03050700411081822010200b0030403c0860012420600c014162589454000b00d40b540150040c44018007071540500300403072640c07500411202c0a9030b601c0b0281c1c4c2c5c0c94981000394080e0300d515244107030020303002540d03410300c0d0648486100d90000d0001c3c084910a0f426203002100030810002110b004a40b05911500400000b00031070b40300320038010f01c007645818011b0070714488403a04800c940c0d00722004000f40e4011010b29003500f00501c00c3c103d0402406c4025403070300c461980c9020aa021003000103003c1c0d501d8070491030411890b18881a210b40c0d0502040158961400009640b000036110742c40c092042440041295200c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 250916780 1250 250915530 250915541
    0x412020d0f050a050c0109020a030c2c0604200f03040b060609030a02060a03020418090b01170a110d0b071206050d050c0d03051c02040501020d09120b060103060f0e010f09 75
    0x10a502e07a01e0900c1002207040e25030741e00003001907405558030b0240c5030041c0e464002190140d030050503403100705800d111012046040e40c4034894010210340091001805a05100760360004050390301064101180c9041e640b42218500d0740c503d04d1744003242c0030802d030300bd5001641c0725030b018006c4010344e42c64243c2032100511904c2c01030b076055001100070070094141071008041454017880c1c01460140d444926160792100414504040b03600e030803104d000d000404050314050306005a1848072005c207041030750f9a8100c56017000382505941c404608896852000484110341c01c030031103551515007444c009000390170808240040c0c038609800810f40b401c00310104c0340510791040080003290500320401c261a1302c3c4e03100c21000c111041001c0721904c40c142c100c07201280700290002d80c5503800c15001a0800180d05014002c02c04211002c101014408500d6504140c11440341141a280d0b140101c003c0c104640000358028901c04000030a0a0404602412290f000e4242d0280381e880b24085010b07101e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 250918030 1250 250916780 250916807
    0x90108100e1f090f0603110a0b0403060b0103140903030609070f050a0513080f0303090706140a0c030c020604082b08010b0a0e1e0103050a090b01150302120412020d 72
    0x4040d40d0006181229002c040302e8401da10080b8420282d68034441d04040d2901d52005024050316020100100040e042c103144581e081110b01d003001c0c904280c0030700303550f029610010b41100e07224101000a41d010740d206004c801d281400100c1107107441014a5540d6100759417250185584030001400c0510131740e00301b40314498969411f490400e007100106c8c1c81d0b8101d41440ca0354528281d4000940703010030000341c003c201d2003c020b0364603442c0003800c041c14400c080d80900305011040c103a1652103201441100c8001526040c89200c5107440e00b0219268952080b009412100005011507140e1000401c034041e046540d048501c00640380041c112000d104009502c0421098001840708a0380b2001500e007850b100d240070000c8052042c00a010a040d40c00c0000074903070401c0400c506564940200d83e8000070703c440a01000c0c0c1c0c1aa140d6031f4902051046100030300c0080c41c12055148290101c0c1c035131141180e400c07481410309041001e02220b0f09000d02001d40b141810b50140d1a000e01c3c103101d0a036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 250919280 1250 250918030 250918049
    0x50a0b0f10052d04260a050304030611090a03080301050f030313050120010f02031501050703090e0a0e030304050c0102190c180e030a020607020c030a0b04080c030403020a030809010810 81
    0x1144071101003a585482110070692100c02d415126840c44107800038000511005c001d450300701030200858400005410000304181d0051100000440c00000889044950000e000140e0941207540e01803503008050700c0d207502440a20002090240010185058420407111540c03030105940c101603581c03041d900798a18298846000304100e6000c0e1111301c00d85181001404851100a12101e0843c3c401c4603140305d00c1035010080c00a14078001d100305004c0702003030070309500e00142c40d01c1c0588101c10520424078080f80700c0c0001400022283c10016080754175604490700c0707042a20380f0540701c0c1c05a500560041c819103070020551900c16450303001c030617042920900c8840c18901c07048150403071000803400158031200032507040c0e10204000c0c0030401e01030b0b0180c035140c1840f00e0000e007848440796000c0d00c640d1201c1d80e00070200f4010001190419400801980e40c3c046100405096002d2a4400b0794070030301107007000060100b50002080000026078a440c49540c41210441c0c10035180d00850103035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 250920530 1250 250919280 250919287
    0x70201090c050411360a05092a0408031c020708192606090702060903090118091806060906060804020f2b15020301050f010f0c0204050a0b0f1005 64
    0x40c0c00c20313500100e5400740211140e8500414514407200c8100800c1c511640500d4240310080f0707001840b00c205100050441d19a4002440c090008100724809040050a80d03070098404034000b404036078030b140801199501a1301d4980d2030f40001e0303d9402040ca040816542c0c00f2810349820120f00c2152040c540c001c02c01d50078054102c504881010b0485240810700040e102d850382c04d82c0c2c0c04a804420a503007103188440500d000c0050110721100035004500f558000e0050040d10800842544c804000a1800392031420901800755181180c0342c0c01405024642440c0040d401c00341c2540c4e282140c001d13003091244030703918450b00b022609917100310000502420042001840c00312986010424000c0803200010300070b514007420214640c0212075862801002181041808012186100072803081141550702d8000403607400001400154100581148190349046c020f5002c01c041a4018004001503e45410690f00520402c10891301c40c4500340d030905441d1410a400300080c028981c0c84904 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 250921780 1250 250920530 250920539
    0x403030903032a290f1311060f1e09151b06090303150111073503030a0605090402011706040b030105091e0a03020601030f060605090a09050105070201090c 68
    0x42e4110000103d000b00789960a41190f5400c200c0c071400d40040c05950301481a181e80740008031200c80850a551180181104006104400540850344001c101c90014207807000c0d46171000120f0365050220741e0040340850310210075003030080030f0010100f5509802c0f01802110342c0c681168080c040e8441e41c080b2081101c800c0d40c078200300103400c410840b100c81d180c50082e109a211f007041e1085412051950011003000602900b00d003074800c031180d0070b0030100702001303045010301c0d25040c0714010040142250303810f8400703040c0e1990805024081e078100089008826608440e00c0b944103445a81410742800d0300841d561911840c040e000d00d82c141c5030041640e81c1400d0a03100f01d200203094603403040d602c0d00b00b84126102806400d100d03514034405811980e080303500c1d00f400301e800f141d02c60702e0726030080c41d014000a80018407a41900c1d006001c408007001e05140400192003d030300140d4020b40c4401c02c0c0614285160016019a4401c2000f8030450341c42400407801c81d180d40102030b20f491402c000400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 250923030 1250 250921780 250921787
    0x2120405160e15130207030f0201110412060504021507050c0108011a0a081911210403020718020d090302060f0c25020414010e010801060b04120602160c060504080111040303090303 79
    0xc2035070f009880d4890858980740070b0000c80c0c0105c081034010540400c03044401903030a100c1e100d00480d9081c2c07002d0502e801c02c010020f98501708103000704000d0740d900104040d50307940d0020007001040100c0d120b81e00c0300340740742c041d0f01c41c8014440b02d8003103020900040382c9601d801c0d4904000100000000f410a00030310000c46865101a08036400003944441402c030043c060701070b030203030200c6031082e41d9590900e001c0b90743c94002800880450640303500040c000000e80c003003800001c481440401d4000c000052805000a204082120780a0307407516008908141c0c0100340700388035500d5100d50f8001941c620144110f144108100307038558040b60583d4410070110f600c880c0340a140060030000307200d8461072200151003c02c0e000740c01062102c02c0104075412090140300c020380341025940f820103241c840c1d90b03c4048002c15006111640125207100c24828844241c00840c1e080551610103e55921001d0601c0e40180910030055081c5200c0c4a90500c10904503030407240d059903200040c519544044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 250924280 1250 250923030 250923061
    0x9051e071817120c0a080a050f031003060f090201081801020d06080601080f07060512040f050a15180f03030e070b04230409030c020f01020a020402120405160e 70
    0x14052002405450072400c8001501101400d5450400000701d210815407a25050041c011243d010700c04000b4803520800c0030841340c020552001e2110b40b40c0f00c1e00300c0305a401c1d001d29070302d034440f50f000842080031654a0241020440b03000340401c100b076a900c146003406031800490b020380801c0054000c54400d000c501c00203000c500744100018107080c880004501034810981c00003195500000c01446074207000d210b2018000320502c01010306615145014042c0e02500f60020740301c5541d00c000906000c1e08468040314268000203071050204586403444500541e8186456074900e4032506011200800c14020308264100c1c030348001c503100507a022000b50581c119042c00c2405807040001c0c03108901c0015101914910b0560100e120030410b020550110021640340f1607800d00d035046011a4201c0e414041064040c3c55503e650b08000700141d01e02642e0100003900684005403280002d06140c20030350060b44a00305031118200800541414442c0034010f01d0041c02e07500c8d0108150380103400d8003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 250925530 1250 250924280 250924291
    0x5060307030b030304030c0510090f0509040201050909090106061e020c04020c0106210201120605060d150f0e0108060906010b0a050d0902061b1203090c01110c0a0f0603050109051e 79
    0x800e0b031084040210382160080d51048882c500340042c10f02141c9007100901842404624000010500d0440b90042c00200c0307220346401280c8a002280030b40e40f00784204d44035450044d0120607581003e00485000381503e05c544000100c00000f40040015020040c002d800143d44c01402c1c510741c4c1404100c000d610004030307010b06640e60500060402d03200300f01c00401c05184040d5020440702d900001d0301040900c0180b09005152003000d0020365207900945100244444c4009a03040e44078841d0156585140c00c203079000e4030200030001d010b030010f030401c03030503640a441580c1843e2140d99009640701002c1c0034180d860803040c040c80c521984128050301036804182c401045622240e0040b0744264048081c400340d0502030110000d400804100303400966044c0c456030f07451854122000345e1907440d03440700141040350a9140c9007221320208a280883c1c24007d01d842011a079960028060038494030071003010a01b04000003454010520580d442840400c03404007101c294802e248011000c000c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 250926780 1250 250925530 250925537
    0xf010e070e060d120c0b0a0605090c07060609051302010909050c0301030b040f0c0e0601110c010818010605060a050408060702030906070f050f15060114030910022b05040303060e060a05060307 84
    0x20180070032204c01c0e210184005a499802c82c440190810f01014500101008203060510000f04420b4481c000c2140d802010003101300d07156100b0f407138070344007400c003682c08441c0305c90501080c00b1105210340e40002d21903200340c90355006103546215101c180c490848032424410000e000400100d0310343d28002d544030f40710b40150944400190390f0700f000c00500303412442c02e05007540104400c0d0b5802c4841c81d45500c610340e00a04914810400082c611a0010104107008903517041c02601d2080940056015160040c00303940c5800303c0c40720003491900130340715803030306d522503907010883d11400801110000240500001d103492031350784400c0781c038150090007110075118551943c2030651003840020f0900364612001d10302c5080c40000109103035400c030810a03c581c820000e1026032000096a541c3c40f2800100c05030312200740302c40000e65002601e00300c5503400100314040340403a60a034481407107580f10351400c0118944a902a222030007040300c265030003100c8201c09004071b10b13103040510351040c1e0514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 250928030 1250 250926780 250926799
    0x4120e010c080d061706060d110a030209010b0c01060e0709050d030504030501020a0903051221070908070e01060807110c040f060504090b0103060c0507030903030c050a08030f07020f010e070e06 85
    0x30360b09030803548103086032500c0d6a03403601d051001e065110f28034250040d070079009041500302074001030001210b03140020103100603124030401c25194001c1400c0219001401000c440d82d41c0c002e01c2c1350b107500640300080c00f5443d1201c082034070018094114043e1550380d41d03038101e0700d0030203050094800180e80103070180070081c880000010424002000303106582da5a980145141d80b400d1807400300e02c03680d00442c580090080082306100005407455614400360100e0903919000e5080d00d00750060b410846103400741c0710f400b14003000c0e02c2043e581226060764039010740d6610007030101ca40c07070f02c5407030903118640244604228034505600710f01d080d40a9003100040032655800018100c0300014021107848810304010018000d0502c07504c0e08400e01400c01d149840341555008141e6201400b001301404010f4000e0303824480c0422910024507804030459560b8200985030880101c02200c8040061056181000c507100f0107020700c0c44a44813a80040002d541070000407241414020120758001c00004c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 250929280 1250 250928030 250928033
    0x30f0203060f0420040f0e0309240d050402040f0c080f0603070f09020723010b1302030601080606030901061203090e07090f060e040e030a080105240f030c19030b10030504120e010c 79
    0x80c4208082d4401047c001e40da03c0b40f0500c24000000301d510000801814504d50861010700d0150881e100801141c50004090361203100080c02020803036503041c43c052070300421500064006144a003c0c0c2440c403c41c8038a030b91090304040d550641c502800300d0350f65080504010030803564001d0407059220320420740700c0401110b802400a04a401c10035a01e0307454031000030035401c0c241e0310000c1c545a5072505600d98076081c4000303040c0340c1026003e940500303000030000d501c0c02829400b90f005002c1e2000e034040b032920182801010303003440c0c0c020184840f20ba070002c0b40c04607001d800d40310b00b220341800300f0904480c54424181c800c1d054140c20710307820540350f5070729070075905050006095406070340c2c49800f03965041c1000d000500902d008019640c0342d44900c6010741e4400c1d032040d502160311000794260b0780d40e2003806407001d502a4070400c403001c5144c1000c50340c013141c150700040504407003079a880c4009000c005080701602c0054501820024014030031900c12881819684040c00c81030403c51b0007448039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 250930530 1250 250929280 250929311
    0x10050c010f050f100902131a0c0a2105120c31030501050f1e0606090603150f060a080a09020f030d11010606050a17100906030f0203060f042004 63
    0x4490003050025200100036441c4c0c00c900c0503a003c4c2402c0d50f01181030012528030202110b03803a018060680f20b4460b11404030340d80c3c0108580c0d56800341000c1d1030007040140341050300200d0040c0d121041600c00d0030b001c64010711580544040c446e1141317046005444080d01a030055200524580c501c5a1180f1340c1d00200002040d11440d0381844103011030704900d1420b00d00c0c21548043c0008185040352408e0000000c503c0180c4a80101c2e080344501d20350b111440003e64520800c107909401c80710100810180050381910030042d01c105540c145081e060180c1000341a1144082110100d40c000020609039030300c0b6408210724030b1001d0043c0101c3c0074440c002030b00d0490300d1490200040c1d580e502c0030490840a00540700100210b0a00e03c1c14119480b03400f91106482801080ba81d4203c0c000051001000c00b8000c001881d101c181009010b450b41002001a001d541c4240e000344161004500415042c0c3c4d00c09100315080a0b0303000001041c11040c0202480b0103ea45074825103e488408481c000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 250931780 1250 250930530 250930541
    0x4060f11070b0402040f11121005090702011d030f0f180303070f140c06030a020313020a0906030c0f0e0117240402030d0201060b0307050a17130b010b0910050c010f 72
    0x16075038001c030b580f0f03140c4108804d880401c21401200c0b4281078a0303100003407200d010750300c00350101d10b044949a42c9070910b900004096601c22588011b421051044c42c5406501c01d8655844414100044c401e083c43d007d943c034031640007080b108007001c000410110030204081c1129403c0000c000c8041104180043e10710b40000c42d00b5514000c10007013241c1000500c5c00d40030308072184c001c0904215504000000c1c05400005c1c841c0e00400d80010000b01d03c060b442003100c0b921a401840904e18075240c82c0180c004140e0303800202c450400c03030b039000305e111041001008121603004c020809560700300903c090200801c1210001180300d85101060031030380d2200c600c2d03000e030410180c0c03242501d442e0040503c0e12055403015000d591400f1028000c8603003c1040340d92112560a140d0707592100c4003030481d0100d450081108041404809001d242041c255441d803079640620380c4904640d032a400403c0c02c3d445204001507104520320b602e9000980038802134210300c00104000258008241c45903016503c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 250933030 1250 250931780 250931783
    0xb090d050102090301051e090c0904030c2108011e14010c0807140120030405060406110913020a030b0307080705010810030209090d030f020408060103080f071a010501021504050604060f1107 83
    0x200347d8070202608010a00009520030070340401062a440c100300070440e0410080e002408104c0304681050602103406001c0c6120f000c006000f0841101d2500001d10b044028002c0c10a44600300300000c10843c03455851400396000928406410750044c001502c0d900c901d50004c9650340c0b014040400854882d084085480082000100d101c038486c01035400c0c90400c40700801c50001d424003c0c4000300d400011550361060f84a8000984505034801c00c0182d8082c101c4011341c0881c0c0002d042c0c204030440d0700505407694003030f1402d0110b071400c0403c1645481b0580030740f1510391b2001808010750740c403c05006810001d00801d01520365105c0d00401d0607003e0895003112154483d4040d2402190b01d8420020780b0103441008504045c00c041c1640d85030300040c440940000000301e004800311034094103d41d6129404403031300b0f80b4421411802d10282d40244a02c03030140c010748101880d070000640300c141c8295404409001e1955440d96204010990304120064441e9120410b041c1030307042000400380035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 250934280 1250 250933030 250933051
    0x2070506190e09040b1602030c0d050d110403030c030f0c0210021f020310050103092d030206010504021e2b0609060b0a140c010b040908030a0e01060b090d05010209030105 75
    0x110300e0035009400140521502d41c010500142004040380120300a1900200c810001c03c00000358408200d103140117003400c1b02c2d10741c06000800540e0303d1308035005003a03103461207006004c07420580000d010b25020780e1002801040c1c1c03074400c0ea800071740701e0070f0400720114041c07c00031a0604290082003031034600780808409644a619441c49011039140e1311244550045015803552801c1d440722071001c0018030805040c16190b200078020000c2d402c44012000410400304111a83c40700c0001044035502a0250302501640d4000703c0c0c40d05140c0225003241c1c0140f16050303640711100b05007071000d42c030100b603044014043d000d061195141c210604248104a402c7c081141c07030a0030300788800c803189540300106820040001100389034100d00b40c483c054094510f52907c90002e00021405840c134400e982c0d9002e0325110b9200704000384440610300846680b4410010102030316801400c91323409025007500c0c00c41c1408410f0461416a034400c40c102c0c401c0e40094101203a0001107801e440c1c0c281c0354044030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 250935530 1250 250934280 250934317
    0x3110f0a0305030f0609070e190b0c1c0305070206130201050c010c050c011d0607050304020d0602040909061b0e240d020903152a0c0f0c0906030d080604050702070506 73
    0x5400a00398203805c1502114400c120341030404024000403108180e09004420300206c0d00005500034001074014010818000d42e01d04415410030340f40c410240b1020010076107501d8400c2401e00c00d21501c0d1042e506a0010b24660701d802081001451000c80200d0401c0401c10042201030401e001e0049081c509481d4581c484480c61802800d42c1d84494407442055402091484c0110002070b10b550888810304200b81c0e603450381d00209080120303603000901030600009001803403a2082c4d110010260003000100850526075640682c02460b841850000500b18100091249450f0341d04410440b005104080d082040d11034044940e007086c042c1868039940454001e450b1300302070000000343c4403600c14442c45480c082000000c0c205541c10b4180008a003220344082030100365080310301001400d011030380d40b040c2240c0c2207030390f680c0010b0710940592070b003201180e0503060024100c40030300070948480070315940d40414000100401450641148543c180010f000d440c0d50004081c000401a686c000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 250936780 1250 250935530 250935541
    0x20a08070e030307021e03190309050f0a081507050c0a110a0e0103080f070602090a0b030a110c030702011b020a061106150d03030b0d0b010b0c060109060303050703110f0a030503 78
    0x1c00c20351905140c000c0e00100030350b40050750356a01d440b0700141c00c5100000c0410609000c00e2038000030400030700c40c0c09105003005060507000500c50048690844480407514110010300003245914491001d0650268600d20701a54110107200e0784180c06103415800c001c04041660325004a0b40ca0682d45240c0c45c0074615510b007851018070b00a00395000901525501d0340e80c81c000b01e07102c1c042031a80d88000101e22242040155012587c0201c002081078043ea900c4005000c0302d94010398454240c4c52410491b2020a2030101c20b480400650001450a00c1495001034860005c8140302440300c8100050000c01030f52000742440250080c0e03550352040c003031101d08113807070842e0103010703842c100080810100050741c075540308072039069240c500442d8900700480440c0c0801a00c06005080c410b4010010685035040c0014002000914003180e1035030740d80307600c1c00044400a000c09000161308004250100f40500b400c625054a80e100b1908007031001c01085080015040c0200e00003003000042c0710 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 250938030 1250 250936780 250936787
    0x1403010f03050f0606030322081c1115010510140d02030108060c0315011b05060f10090e12090a0b07150609151a040509090a0501230c0306040f020a0807 67
    0x5000f080801d00520260411200180c0e0341d0084404400082c0609039909145043c105034490003082e4250407104580d049400009003480d00e200c4490005240c2071044c12100800504a403880350070f20700b20a066402c040600036074120b101a16420b200d550b04040c907281c007840c0020071b8141c1c01c043c00143c40b0350400200e1410548090135810a80f1014420b00440d401c0710280c0f5032200c0d43c00d080c1403030142038035040002c3c1e002c040d1501501900a06080207103d110510700a4032800040040c40c400b65260b080e100112071921514200541c0301c2c15000e0198020880100106e050040075400d0480d695151142c0c19445a00b007159045100f641d030381e1101002e0b0040b10080d103840036040c40380180646002c650509a44078016121500908540c501803107401120054280a80000868070384031841903034445031210112402e43c41d00741043e04211070308103003000710702d690074031a242c81e2a10a00d41e03200d500088d00da587e01c07940e6100700007009c1d48648014030581506407202d0300a841e2198025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 250939280 1250 250938030 250938043
    0x1d040204034409040b0d0609030201051f0e010e09030403080406020106050a140d0233120114060a05072d05060c1e0d0b10050c010c030603030f0309031403010f0305 72
    0x560032201e241076840d0190b940b001075405090703054a0004070002d005001629425803040c002d02441e18101c1c01c00c0905074103402040c0b29940080050354030914840c40c48105501350300c6880c3c0c8030710b0344d44010301c0f003001508035031034110b070071082102d00f495101e803500d151580c000d61100006d43c0d510314081040c0c2c104102140010103030366484040d00070400001c182419000308000780709260b2841c0000c000c00c00904075060704e07046203507003501814003202c41006a5012803206007440c844080005180c800d0b4001c400400c0070041c1c0101d0415900d100c0c150380f00d03003005404507806a212800c00c400d00c52403550262018903010011000290340c2e080032811f000303001d0000780d103009040040415140c040d09006042120350200d25079648401a071b410001d010211a079603104414802444201c0c3d4040042c10b411010380c0c008001d461341c00f080950803a140c5100040c0414ac010014181d140d029600002d5130901900f09140c24007400ca2204050743e00c241c1146d15120b40220040c0103104040040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 250940530 1250 250939280 250939373
    0x620040807150f091401030f15031103010203060d02090702030c16050f030705030c130b03100902011101060501120507050d110417030f041203020a0b0a0f0c02030a1d04020403 77
    0x90910003d00d000d009280c0203031401480e6201c0006011903440b0b91295001e51020803ca02c0c08002c10504142c018008031440c1c4019540f406c54440c10300a5480c043c42283e0250313070018041c001148403542401005000140204107500060000d4103510070240405580b114001014440040c00c14041140c00e6032250360190003588134031820310080d140042d0401d11030070119025250403d0b5000c400c80600303014400b0035054060422034006445e81500b1022005100b43c07103086c1f545a6603010203080750620300c991030000700b00390841410046694003c80d00242d0030f1400603c0c2103250001c0c10280c601d43c0c0d8620180040000b0f0030001d030700c1e203038184010040b400d002440c0740c08001040300d0380600690107581c0d000d190003070345142054000c0005501050340440c01d09040d181c116240c07801014800d4441d0603c9003401e419080c0c0c2403010089519500613901c03070000030342c07048007071100c900c5101d21311300d80190b0300b0080480412202c012000c1d00000383e18400f03503005141c0c0300450b0000380d140607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 250941780 1250 250940530 250940537
    0x111010903020d032f03041a1306091505090c010807030e21130e0a06050d030215090106080f100605030a1205031e0903180616062004080715 62
    0x90030001941c04610811a0301c024540858803103442000301004203a80a03540050a5400f44641c007210f403020050740c8118001c600d151b07a02d40307010b0715020034140c08903055205038528280c0000040c1442d840140031502842d017000b04c21100040c00b804803003065403951090b41c000c40e000d00342d5680c0582d40755030180c0c0900c0c0900800301e110300165580c007031b0400d1080310140d00c139a1034107545145a0944020480942c074040080342c2d80c43d65205d0024043d1040c0d0b084c6401c08402060500348a0114858540e060b401401d1400b41071048100081024101c40d0f819521890000784802007040610200510380e40038000c001c582500840481c0c3d915417105019070800d2205a0205501c9a10300d0340c40496428802e540c4d40d2401c81400e103040180790000141e0701e20070140881c48034000007400045000d20410000b101c0140100000340c024411000a803400c510800400604203810030039031038100410110348400302c21540501a000368002859030f038400442000712444e01c03481641c58268605 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 250943030 1250 250941780 250941791
    0x40f0c1d090c010e09040f120f0207060e0105030c13080d03021305100e0105030907080303100302040528020a030603060f0e0d050720011b03030506040b09010509150d20011101 77
    0x2030144c4034810740c958440c82015000030244145601e1056920381d01015004072296002c101900228a4030440001403144050101d85140512034808c1d10703100586a0340c0c02c43d5103203020300c1172990011036621100307951148009403105040118044612181d180540c5480800c241806407100603440180705800400d8503081542c0c1180841162040c20310786680c0da551008800c2c1e02d80180c9a2100a00d440008100600c2d1107070030a40384140c92086130140a2030b00c4015031101407003020f90011000400d9070342607140302100ca078024050103980d0305020405130340ea07460f94000c403005941e1441581c0d48030a020410404140021100400d4a0400c00d0601049842c0d09901040c661600301f0110407851180347c26030300504800c00718155404e541c01801a1500d00200600815034200d03022303e0901c090610149440001c0c1c90580340c0261500c6259500d9134901c00c01c3d1081c0c4500907070403042003007590001c01c0081190b205010b801da0185060340d4000300c0014402c0c00b00c120307480f5050345010f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 250944280 1250 250943030 250943053
    0x180624030d03020d0b180403110a050d0807030507080603070521070e060405010509070f050d0b060307110c010507050a02100c080301080304081902060a08090f07030303060513140a05040f0c1d09 85
    0xb41106c3d17041500340c81c20013045281180d115180c66245840a4698450188100e00c4290301c118010f1096400341d4080c01181c480071801c0d250f54806860031355064210060074061400d1402d003003109d0113001c01d140c00c2e810440ca52242d040402d180c21036200554000308000450405005850040c0000c1d21542a070f843c20b424010400381608800d14100716001404444404064101400840c4010702503581c9042281011302019048d0740341d14040c1c015042c82c18000d60207202074840f510303000805070a0502c079960810103140d40030200d403000d0280e503440f5400170840741e4020714007900b00c1c440216911400c0880360751a211103030307030301650324910345400b1801a164002a1051003849051101142d101c1c02141c6040c6251100b650300d0b203108180c5d00009166154100b00221001a5055440401201014425142c040d0004455110030f03070081103001e001e43d4030440d4403038021207500300e0002e9140d13a18540c145a44d03204041eaa0f0b002d40c80c02c00300f4105103501c5a000b0301024000c09291404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 250945530 1250 250944280 250944319
    0x30a0b01090902040609020c060702010c0e210f01020c070314010b010509060702041d0c0a0806060a03170403020406090212060103060320030f1e06180624030d03020d0b 74
    0x50103514807040d2554400411512203400100140910f10030964890b000da07518184d4880c003c840307a60042d8246030181405c82c0c02500720040c4400003809422280c20001d07041003517911070041c000c1c880c2c0301e03205080030a86821310140000000d0070001e402c8052550505d080b41d030000c000b5040d80c0e40d242805007a8035a0300042150b001c20002d9510581b19061400014024011164112000b01982d0b0741c4185254010501c0480c0e02c0045602030552a124600995100000c440050b041510007205201085040f4004024140407154480c581510796012a060f0f0301d40d513202c44030240d00413607518080240004030703950044081c642005000d10310340b110303d0007200c50f0380c0c219100c1c50f0801a603d4551001d0000700b00d0f2150100441e0f51059501015482100d60758611421030f0140b8004110007050260f00c0f25150420900149002c2d1281001c001c003c060305003000000098a000d402d200361020303c01c81041d541d1a880040c1c4560303103222104140c44040114610540c101549504014103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 250946780 1250 250945530 250945553
    0x906170103031110090c090c081905091e060103060c180b030601140403050717061306180b041113090201020a06021b032b09120e01121109040b030a 65
    0x4062070500219004865030130308203009088200c2e002824510040144001441701c0b03411210b400c242041002c16000d02102d0030030068410072100341d203c0d00040c580c04802d070001a00070700700d0003d440c29046800882400c03207201d40c1c00300007650000c40040090040d284101351182405060036191580c9800b074604140e8140c1c05500d05041001c804541300b40d1051070294421006c10300e0080d611622400c1030342d40c5000f507110344040d4900368180f100000300c02140041c090101040e1400c60b00c41903542701d401908815441c0c06446010f840f42c4000f290201000750f01441c020030b000c4d5090640701c41800003d007500c6c40b1a1060a090920110060f64000b9200c1e0405801850040c0c40d1001803020054200e40e4000d0340c0d10a102c00704041920148c2d10082140c048490040c484404005540da20159621000003401c03c8101c942002d41c82c50040c3c0000d0841d81052404100310351500c4021021074003080f54084500c0008100282241003030f2060400e264401c90013401c03243c3c000e6903911107510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 250948030 1250 250946780 250946783
    0x100f0e0a0e06130b030f1005060103060608130206090d0b070f0212070b0a0204030204090c151b0308091c030902010e030a050607050705010e0a0b04110907050405060a090504060311010906170103 85
    0xc40d0f1101d00800c1400a0703211a0321404000d0a5951210f174590107107036079605006c42c070180075141101180d00c56020b032050000300e4156485103a200c2e511510b109092130807464040c0d800c0582003041c20b081e0fa5a400c00c10311140c0c07140209141a0415007001091240718105840c1954805041465202c0100c000d03107940550141c50311580c0d5940d039580e000070340284e030700c0290464104016441041100c11000302503c00e0440704c2ca1002400040031140441c002820780403140c0708920b0724011900c01d000c0158080c20803821204821800960103108490f043d80e40d100082e6552031100c210743e4082c8802c0c1c12144100c004140c16004c544a00e41c640f08080e1002c030071f019000603c00704204003904040f0000005c40140c91441d8041e007000740d0540c008031011254801c1c260422520f074500300d454603001d04555a500c0b810705081100780038451b84002120402d10030710302c10005083d580d9000e802c001d58400d44104183c201c6541c00580900c40342c1d04030f0410310407480100c05014209508040c1120b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 250949280 1250 250948030 250948039
    0x3111606060509010b07050f011e0c0c2117060f0d39081c030b0a0302041a09161d180f01140102070302061e0405100f0e0a0e06 56
    0x1109440c001004001561095410101ca5000000c0600018001d007240c140035405540c0d000501040c02822640000c100c13140390300510b84804070121050380142c03401070950038400309890380c54498a00d02c080081b6003c1481030001c11907649954040c0d4440302030803411491050504107000003400d004500180540690344440a201c284955400442045004092680c907890080c0e500e00401041ca5036a4010b000800e0000207454a00001d2800040c41a800c1e400907410f04180128007074905c0c1c00c0c7c40344d846801080c0c040050b03a201d10818155604509041d03070482058030a200140d50024010001c0320102032030304801c00d4010144400c14140040ca070448507256800050751903c1310084100c440c002c01e01003050f03801c803c00b8682d040c0d80c6864120304095035284012640c5a08900000303422403000e01440c0700c1809000c0d48001c111501303a00780c2e0304040c4c0315000728103104825001c2e04002010a2503800d0499007250320711314000015120780d0f03031550501000400304140502081d024 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 250950530 1250 250949280 250949317
    0x112710140d0615050d110708030a0e160e061306031e020303130e04030206010b0a1403090f12041815030807020f03060c0c062215110d0f0c0311 63
    0x1602016403040b00a4501107100c188011015040142960420b0341c0d0302e054030740780424140200c01c5490603039204a50007402c4034550381d03c55008501814600b071111000e445100c3c5008500100a000038001d0041801001d80510b071440c10172820301150490040c003685460428400b01c0c3d4000b8200d481c1444400519103022050f2021a10310702c140300c0d400c2c15950307858801203070300310f1018029030142c0d0095003240e640717036212010140140306088100f40400c0d828010f1200551013030010b5a07005480d031040d83d5000650100f203a081c04070749035a900460740e00040601500f640c9801001101454034010411456003c8190f02b50030401c0c0400742c075503c80807a0500440d034901d213101c1591503001d805d44042e42803405041c04a50043c030340310321490080701c0c0010701100c1242b9070540d4040c010b50b403c1400d00c01ca5180c1d450151104610144c400c0c0e101d881e10300c0264141c8000303103c01e00c42c00000242c020442e84071001143c480c00301400405090240510f0050900c400355284542c1d0039840c0041d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 250951780 1250 250950530 250950547
    0x3030e0f030c06010f050d1b1208182e0c02152703100209040b030d020127020a1424070606170709050a020c0105010806040501060e2811271014 63
    0xc2038802c561007841e076804c4403604c040400c901d8102410303081e8540145106c2082c0340e401008940cd00d048544250508d080d0682c0c4540b003441c16001c0c00028842c24040c803104400c1d0041010b0340c50b803481c0e0903c11080040e007440504c2d004074191110405190b8020225044070000a8448103600c020082e81c0f5004246080c040c2c0e1564003203500120002d0440d101c40050340406030117030002d0a002038030b15520b04103611150b448011a150540c1d0300800c3c40c0c038881d003850825402548d10482072500a600c030341080141c0342d11102c01030704890012195603101c1005240ca07106503202034001e0350241a10381d03e1141c45410010f030352016a110010007050300c0d43e5001494000b4060306192600b503608100000950680106070030f0301841c007a90080c400143c540d19454a0140107a0304210740030218011072542007215031025007418010100441d0020140350350400d55045103602e00e0141035000d4a4034018016601c404410110544501030000d002c0c1304080c0c01c00202d9950300c0c030308100004a400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 250953030 1250 250951780 250951823
    0xc040305030f1b1c080c1806210f04020a06030e101d0d0905040608030301060207060c051504120909051501050c01060515070b0f040f080703030e0f030c06010f050d 72
    0x10380c0410b01c0846140a0641340e0190805213041800d070046a16a000304180389944400ca9009100b0200101c0d400d45800b810b00200360f100d0580c0c40c284401100c1201c600b49810400e260140c460710f1115446802c0c140100003281d10300380e002e003041c1881c4c00c0030747c61000303404520100500e6920030001250151900403020b12410038030881680d0290031501c10000340c01020410a03104107540400c00d60f5200c1006680c0e0740b0081c010640036902040c1c0c00c102c81c034891940b46100c03a20403c1074030115410480203060700039040c1c604640f1008c28101d0504a90b50003284a00101124401032185041040d0120361040881c0041c13410454002121554040b00b500311400a1002518550070f2014501d08000150802038007100c248114102180450550081080c01b0701d8004101200840d141ea4503001c0f50b9000940072020f158488410300d11164080c801c10540341800340c00b80d991201c0e0300081c04c0c14060140c00801480c100d103071083c0070603220714400d0b0421075402140b00c9164940c00b0040e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 250954280 1250 250953030 250953067
    0xb011202010c11032112060406120b1f0603090b0a0504030f0e060c07080703140601140d05150405030309010e011401030b180105090c100c0b1b0702030f070e0c040305030f 75
    0x44072142d0b80c1781405d10b201d120743c0c2c000748090121001c9420640c0c85813420072041e00d42920620700104820444040400c0b00c0d0000160080248803442c0f6803280034000d4a60f541010b60700070808203a940030f41307805000f410400e042d80505030760130400c00c61034159000b0302075034004120315081042d8510001920780303425044038088a81d120440d030582e41da68040586d07c5069003c00c540780340280e199059800c900049142c1a2070050512400d074002c0740007481502a4bc0f60b005407000c2c419140120011101107050078041e43c0500c02031581c1389804400b050a454107041035a0440c0c0c9801071440d011040d5080460540b0703840085112240c544400d441c50900d542c2005401d42e510782000c0c00540c000008080c1b241c40c05c15107100c44074082e49002a501254855000f1b0420180100003444a10400b1100507441c0320407041c440c00c00107150042454031307484032100c480c10780c4080d105019517050034050950004018076035602d02411903403026100c0c043c7d0780300c0c030320170b00c0d0041180320752203140003040b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 250955530 1250 250954280 250954303
    0x1104090b040e0a170f121503030309101802040207032c0303030c030a06030b07050d050c0c1b0301020f0703080105030715021b181e070f0f0503090102130b03040b011202010c1103 78
    0x17058554030144000c3c0441e0b001612810428a10a0320348007080c01d01005503880381c3e0304000500800c811030300551010701003202c021146800656026001a601c1d440501201c9003c0d580d4042552501e601c4d1440b07620720342e40500208145201116865940001280d82c0400c0723940c2040d0700c07520780e0b00ca43c01c060a0942c00042901001c0402c00c10400d81c854041c01406101e02c200b40990340726042102e055100307944060045403c408000c0c120b0101001d5400400000540010300e8010b91480c500030681104c0c504070b00040c28040108560b15003084008050460300c0a100301215100390041c0d95408600d001e240c0042c6200f50003012035546440c0c250b0003494480c22600c8516040510300c58440383c8100104502c00d01802140d0700a2060650040d1909076450300b070504904543c041e10280c00040c008444c940d02084403407040030070f1060708001407900700d0569889090902d840081e030f00c016081040c1e2441c2a400f01e42c00340c2e030300883e00c1c0d03222600801c0d02550710960202081c2030110000b40c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 250956780 1250 250955530 250955557
    0x2030403050c0606011704031808062d01060804140a06050c030708100e0c1e070309050111160515071a06030f07030f0b10091104090b040e0a17 63
    0x200014036400200810500414500b550080d589040054442c07440c0c03c0807222106410f0800540001e000c1ea0420f8a0b01102d408c3c1d204e541e0381d4600c156458100111850300340a5040e4504002c40a070500b8011900c00110660618960509034014441200140041c04005046843c05003001d400e005000803103800180a0109103807021782d504099106440d03110000e00715800007180c105a142100095402000c1c60004a480380d1140b40740d00e401034100c0c98407000b00c0c002c1203403030b0300502801403035a14440e8680710502450400050031114103e55041c105030040d1000c0e04c20000585503000503664203c88100760000c11140d181c030140100c1400038651940103a41e0300c0d20010107905244240d104804480406076503013801030312100d0500c0b00a0000c0707103002c1d00400052909d420154448403280f001d0174410385c3e55006c802a40d8252618034110600040c00340020043c60040300501da005503001d1041e40e1100403c166680e224080103048400000c3e4080f0790041d9042c01c031400108004c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 250958030 1250 250956780 250956787
    0x50c0f03070806091e0412181401020105091b010f050409020703030e0d050c060a0b1c0609170906120a06050d080c0606030c091602030412050d09060e0a0b070c0302030102 75
    0x30300080b6040e5080b82c0300d16800700015440c0802c070b1955110030b00129540010300c0d12903a8130340348001c148194031401e01003203048100e4078128052841c0000d010300c01d1420240c004450029007100d201401c03044050700040503402c1a41301a00742405403203001e1a0004000362041c80842e0780740102e0b00880007003800041d0000a0607459006010100c180c034081d03880c1d58107505802c1c0c801d48200418071806801c8a800540e0302500c645c0401440e10300a80400c0d006a00c8d401241c40010f416a4100c806c0c0d6074032119101400140314901408041000c0c0242c035140c9250002000f900410740081c9008801a00150581001d50000c0300102009424510070208928000540e83c0107140c4551092188034006075141c580022840599035000d030a4891584445c40103987e140843c551041c00d62004010005120030702c01803100c1258025006484280300c4124003d1940c0c074143e20102c1085541072291415698440180c0c04880310010601d5803840d451400e410700d0a1280c0c0065810352000c0f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 250959280 1250 250958030 250958041
    0x30e0d080a0603150c14030105030a110a030804120308090a02010c140f0d02010e0c06040b030117010605150a02061501051801140c07080d11120d0e0a140706020f0c04050c0f03 77
    0x9804c1505c0c0103005888250642e4003076410281c160100b4841e4a81c950300c44001c610215083c091a8114064040c043d852500d03100d8882004c158080d80c0301003494105103070f040b424140e22038465038101e920b900281c200940c280c4c000820030308140c54050100d0070740310501d80391240100080b403013203aa18402d42e4440141603401900070580c2001001d85130207040b045010310b24040086505860365800d40cbc0d4116400c04100501e030301108159030656658a54010030f0903070b0380c4640207400c0a0046401607580036040002030030403001070100240c000b2a40a00d8030b072aa040b105a403510b0036120803188840300581c00407a0440c6032001c403d01f00c4100040d1030000110089006c1c07081e6951034084905c401d9042c0030841e6542d44c00c078000c5c0e07842d8000786020806090f41c0c80040c54032150010012076400450050755041616030407089621100d56051005082014400e00c8014a1a4005451529a0b480703141d078503100d00d01c00300e0303203c0c40e50b6030000b4101150060070740e0110001506125240d1424 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 250960530 1250 250959280 250959323
    0x1081504140c1902060c030411010203070803040c03022d060a2601080609061501080406060302041a1f050d090c0f0801020d060f210323040510030e0d080a0603 70
    0x7803d6980c00003206503030065202d000246a50188001d1150141303141e580d500c60350f44100d44c1804260450000b0801000405c03810350142d409075014a003e1022300345544100700030366609a081c6038070b10650804914040d000c150003003c0e607000c15518030340c0da0400103401329034844004848486200d107060f90f0102180340140540e0513207424008859842e183c01104030b41d00c130000c54080c42c01c100c07001403030101c079403007081c415400c03520a40740030030307156140ea00280a5400030680c071382c030303124028595007402c1c40c140c2219124801070180003030182c030035580c00400511405249c004a140c881d009102008010301d8030000078811b0081c9291090380720400c4502075480003c20680c843e0800c036001c10340070110b800c003200301d0f03a0007103160500d1403141e4000c11142050440503411310003c00100d044040100900b680040d210000c000c2da00d90903c07082143c030422442e507020800d850041403d203d440e001480c00140322150400055581e5119140006804260030080035500000483d8101c8101c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 250961780 1250 250960530 250960537
    0xd03030e030f0d1e060b0a050a021504051006060503060a0504090206070204110c01060b090907030c03060f0b040503100e030307271401271e030c0f0e100501081504140c 74
    0x144d00280815010000450079a0320310b0140900e400e00801a4203030007070240c00280200700c00750050700c0c1400c1801e1420f400e81d400444080e5401c0c0c1020a139a00280c03040c1c440c071400350513075040250450074034038041740f41c805440c003d00d4019985c807404601036540707080650303009642c010301c00e22520890420098841d0481c0100500300c0d801d010000c9603084808040d5140203102038520101c55030361120480150004100b86002d06655103004114000d804c00e03940040c15001c2485030b9218540b000f41898210a0701031040640d180c0103080703c1d64031022080343e800090b10b00e040d100c402c03942c1c031021307002e5810525080865081000001841c0102440c445803904c402d807034219403459034491032070352403140f0704112024900c00042880084044281e04214001814013000c4a540302d695004a0a04a402c101d05c41085400200140310843c02010b90200189010740a81413400001070601c0d040940150308803a0660010305c0ea0340c90f558800301c1c800d00b407a0054017690130107280e80810342c2d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 250963030 1250 250961780 250961801
    0x50d0209270117100c0c05060f070f091a13090509010501090b120a0b07140f131703030a1805011e0b0109050306011401170703050a1a0d03030e030f0d 66
    0x50100000180082d00e00f07144420003440c4002078a0710050400c0d941d001807855882010a0082c0c40d031031100407c0c8100007031480303000e2480c58401107080442000d801d8206444198042141100042c45101170359000781040070111402d40e40ca610181042100086d110340000344160b18000c108002080150401c80c101c4a80c540100b065840700c3d820b1240050300200f030f1840315031240317840c10000f480c06c04140e98480001c0c500141801284120340407158001a85c0d600100700204600140300038031a076500090940c03041e03c0e51110591170001d512030000908444410b41c1e58441200810203002e00014213036400780080000c110705441098001c00d074220602c11442c50540f10100d6035010700892070a075400200200b640303030f103408040081a805001140c0c10005250305c80f81080e0501c00c80b030340c0901100c0d100845c0703520f0300900e141c0071995080002c22001d5080982601c898540205a01210350103160201c1c00c2c101031007080d4610721401004208030b400005260000c80034a82c080d00150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 250964280 1250 250963030 250963099
    0x18010506030c1815280b0708031603062312061009020a12020c030c15130212010902060712110d090519080712021206070203040513060e010e090114090d050d0209 71
    0x803910f400306c1c4e5015000f0b1480c01400d0b403108001203407124414428400b000705c007614001c0b90312a10780c00d03041d103022081050140900c2d030541e140d04144ca490002d0104201c0d03a08000d080c41d02e03180c6025090302c203840c07041e402d50690005903021075610603070081c03100d45100041556145206000c0759503941c03102207400154002d006020402d05031410b0800c0c0600c000c40d503c0030b42c81c003583d003c224010450902c0f9400c6590380d2010300c0300580350300c0050807140d0302842c074150039050489400380c586900c4007400c000c00c0d003260440100103500301003c00142c3e68117880d500340c4e0782c0500c0ca196941400a8210008a118400c17000404146034001241024802e4500181e600c51000a180c1e85150540700000540c20500c0700b4050340c241407450101c401030504011648956805161844881c00e82010760318240f4401048031001c003d01494115080262400c501031074003403845030316281c0141010b01000800140390340001c9660301038818000d4014450342103244002048850580300c8200072001c0f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 250965530 1250 250964280 250964359
    0xb070c061205060a090c030f06120302060c03040c090c0e1305010812040503060c09241b030703090302010f020703080414030d050403050c04051e18010506030c1815 72
    0x21110790140501502c80581085641810809800041d100d00148802099036030300c06100b031910382d070084a00519945041460703188160130001e007003980080c03003111680f4041080c080001c0c2c090b070080c822100c0028001481d107148a004581060084500d194007000c1440380c0c00c807500040e80070328100c850040490f03010b00c0910000b022a4040c0b440b500d60300d42c000b94002146d400c3c03ca402064480001021508000c50418221490100c1d94296120b8004003090740d041030030850340c4014034012480011400c2000c00c0c0c2c0c00a29240d040d010007810030180805051925008100301c202869000080544032600c6070500780030340301440c070b81078481c0c8505810454171038068401c0b9401e40350084094504c0049200500c4042d010143c0304101001c40800f8030000a10f4040000740603600300700090b02e03602070038079081d403d5580142c10309109400c0400b40c071500f0342da000c0c00039142410310a040042903481d1182c24542380c07120542c0d03d8100e0004411608015034500c3c0b03030f8001c0071103418188130 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 250966780 1250 250965530 250965557
    0x1090b0a05060d020a0c050a030206041104090209162c0f0a031e02270f060603060310110d1103090708010204050d030e0f0a140a08150408130b070c06 66
    0x8100c00d140c400c59030031040401181d45604020b0300100300041c0035052480c41c0b07220326543d2601d84580800705a0050f08608184810010002c5200c4680c5004403801d05c844e0106030001000000b02800481100401d414108a454068640310340800e02c50000b1040c8040581d00310b440050103c80f0130b602c148408925088580740090104085c0c0c0e402c803841c00300c2460301506074901390342140303007ea030301500100f607902540c22120964900440c07151828401380c00c00142002c6148400780c40984a0f500500400940d5207000034008060100d00a022544045541984095120303c244460810742031042c0241207502c41c07401540501c143c0310032206070303540d115661801c07400b0314014968842045080000840d110300c80340002181c00a06910704904c11000155031089940c6c00050004001d6181c48860b140c52010780340206550070152a070070110040da0520b8010051004011070801b1880542c00344549400e54048d1441c1d5400e6981c404d15401c00d010000024429400000c8021030a0310 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 250968030 1250 250966780 250966789
    0x40b03100509090f0f03070f02011b12030b010807020f06060424030b07080702060702060f06040f0606030f0c09050a1a040801021c2304030f030b03070315181509020402040509070801090b 82
    0xa410541060164111230b886070f00440741c030003890491011514501941d100865404200da14042082c0e85000502014140001d08000340042440c010754101c80c2c0350540c1c0c203101050081e80100f0850b000550440501455055240300480e0708103000b01d012404010041200031060080400c0d03107580d01d00b582c4401089035a50070440d85280103030024004581ca2000034010346822520007031010800908919110084070400d500503070000e921070503a0b0030324038803901c0392401903911840d000340e206d030522005c242141c0052040301c0304c0d011225104c80a07403214109481c06000b120000b596103001a9080070142c4080d0408400c107646000c9a02d20001f4021040f944800c1c0c094131400400d0303545840a4a54402c41a100400d06403960b2145100f0343d010700000c8040c41c8601c3c0000400f4120241c22000c80b8540c1109080c0c17131101304c14107008a0130141101920120a0f08042514001840450040d0050350300468000d00c026040c4109250000e0049050b14821081006042048820403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 250969280 1250 250968030 250968037
    0x30b0f010b07260310050906030111030f090a020d080304030315150806060c010c02070f0f0609090b0d0206032403060105060706180807030203070309050402040b040b03100509090f0f03 81
    0x34503070704110b0030001400c100000401080128006441c52684610510300c0d54002c480c848003003c0e142c0e5050006242200c44950083d6050303000300b02c2011202098076413840301070300d51110304030200c0000d8440041000380d004119405400403920081d185000c40342c03900191030440c0030a00f40600c1d14154002280c400040707400a5000e000682c807030243c19110640040d081a400510402401c28600424060120b10503200e42c024880e062401d94101d5a490740350700529198240d85a0410800d9031181c1e8003000d60b2141e01002480d4110000000e074003c002443c001e412a07c04000c00140390366002071a90302c4003003442d542c0e001204038030802d43c9a2800b4091780760300c11010302c55400410301507840900000a465203011440307803282c41d50305454004100c1100140e10008007a020154449103400007030000f40c500f90b081c1414500071641c10b00642c065505c04041c0880052942c82d40313148140020b0001074851440750032700310700454135030505c0c607140406485001003901d034000001040703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 250970530 1250 250969280 250969289
    0x1306140d0216050d020a050c030703020306160519050c1e060a09080408010f020901110712080c2b02010b06030103020a14011202120402100c021f05070602070804030b0f01 75
    0x2014509481184680300039044550034010394518480c0800004804100551841c0c120390005c0450000d1450880c0c070b041000d0350b00798069041001c041005840004510341c1203072005450114141a0ac00119514060018079480c8012806900034020f60040010320202c501d1900381c0e100c0180d0b41c070b441046203030200c5404940b5840000001c0f0100040d0340582401c40c4160b241914103590303503030407074250795000c41724044003230740000d4034030b02903800004240198800101400505182050144017440c1076003014000d000001045001302800f80919500c00800040350407201c098140c0e001842501300e198240950319100b46081c051903c2d1003501d048a0b4010140201c4605114420b031441d2802007226040c40314520401d46038005030300107021802030303003c0d01d103105d49442e0040001c503805446d40340051140c034800f4030340580c581e80c54844811403d80d15a98410301c1c1c00404540c0d910421764068280c510120f0300c281040550070040085034003440000c00743d074030750741003501d2680e90a00c80c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 250971780 1250 250970530 250970567
    0x7020a030f030e0712060204050111070f06050322030206011701021612020a080412050c0108040812061c030206010f0609180f02040e010e0603011a06070b0411151306 73
    0x100a0840e03200b80c02030000800f40009903a08156142400150f52031140000c403101c0d40c005c58140300c9541d000c0b00c000d111103c248000c0c09040e15003441c00c051480390380590760070003070300100184031441c10340c8403452600300d60503510728441400c1c1002902c50030280600c070400c007050701303446503800c1c814001d580307465a041d00c0d10084c400103543d03149040340f4501440700540c011a40b200e40401d0860010300f009142d02c0100914510b420b20303180741800d0300310065a041c00f100d20107010110b000b00040e03036030804c200b00019459450f003100003002e036030042d0001d0031144412580c01c420503034045641412541c01d100100718558444606441c0e03546075008050b95003e54424030189525150050216030031608401071402e40c031000c00c440d803180240c00009100c0200d80a006950402344030f00c001000d00f0002c950041140385000035a00d00c20340e00c0180100320287c01240501210312048003260000074141c40040f4680702550016800100001d001d200640c01c0001e810b500920f02014849407506 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 250973030 1250 250971780 250971797
    0x212031e030a15060203070c1508070804050f06090d020c0d05121c1b0f1d10110307030c0309080604030207090c0219050102090a051e010804020303270907020a03 71
    0x3200d0034a41d0001004403065a0b101c080000d08000c0200300c40c0301402e0564095070f9600d25a041070100320340541d1008003102c18120440c1070300d5520900740d6030403402c00d2031b00b800551141d08210749070404183e21054075000d03540c00d11203400300003e4540480e620640035a10b503000301504214042c14035050203017068012105440401840500900c854a02c0201070741d1040e90036201003003194588400300902c10001065807030710700c0c0c10070041a0240030515050a00d22025040780358442001c50703840340158402d08a280156001c2c0d10103400d0282800c00f200c0c1c4a44103810b0060107a0b100d0358003940802e00c00c1d0404904001e0100d1454800c0e13800d500242155071400d44820001c002d80084503045000d8800101140e000544d1140c0c0940e002e28000758540008401b0003040740c10340e07408a4401c0284141c82c003089101e10010380004202402c0c03a0300c080d079540c004a8214070070619400100c240b10041030421015840c01d41c070134200c0943d00c0c4186541e4031401669103e00040c40034000c51340c1c18 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 250974280 1250 250973030 250973077
    0x50d110d0f02041a1c06030b250207140f03011104030c0f0b0a050a090b0c0d030b0609030c0d05010617030403030306171c050f0408010f1a01080a0c03060e13021203 72
    0x5002002e00601005510b40d6442046070350f1700803549660000c41c2c0c51602901404940240701c400f00c540c9160840c680f115241d00a08003071341e101c4191288000c1c0f141006000c101550f20200d2103000504041d00074011503000090040043c3d1140c007044410b00d0450401003045001280000d01356903c9082c55480c0000c2100151440d4108034050001c0202c00d11000c68041284000b600d00f08050f07100504040c1020503016095550402e42d0500500c41400501080c0e030b00020700082958080c1d8140c00a0103060900d40d016092070f07002603003c0001504000d0800400000600c02c59001c1e64082181644918914200c00c0c008542c28610b0360101c82800004900c5032a00c41d001e0105081c041e00d00071000d210144a50016801241165542d407140c0324040d0040c000d00080000100c20036480154040001e840c8a1000e0002101c0907500c0c080c6049040c0260b2250b40604850003140240e0314290414604c6000c03400412405034000c400b0107266150f000044e1112640703610050341004a86 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 250975530 1250 250974280 250974329
    0x5030f040807021e030d080c07081c0e070305010b010f12050a0f1d06060d03090605031f030c1503051005010309031412040c0e0c0405040903050d110d0f0204 69
    0x1410641d2100c60402c4000d00503540e030f6500030110403076101d041044845a900301400c00344088410018442d032203041051401c0100122007000e644500982e490754052243d101541c0c003072081d5407000f075181182100007601c0c0092000c04692298009114108150004448003455181e0700700c042200640c14111880180c0c00170390780a181c2c80c43c0000c20401096200040c1c4441c03080038030840c0c01e141180c003401c3c50244003090b8400015140300d001d4810070b5500421034621446200200800403011070032101030449101d09101c00c500c440e03070119440c1d081c05200c0506038810742040c411000c0a00400034043e0080b60300c80d4113031040400e030451034a00154098080340c6001c900304030b00c082c42c0500e2901c2503405400200320100d20703c5004c0c60705103003030452400c407034000d02c1c1040e00b08002c210782185040d04403000e44105607400b00720f26102d0310b002c1c0c900c1d00031000c1c121f004a0500c400d500d01c0300c1007800a001c1000f103244084c403c4c4460b034101d0100724480e80c00b515010400541d040004481c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 250976780 1250 250975530 250975561
    0x1b06030a0b0f0409060e0f0a0f020108100e07090603050f0907030b0705070c0e04060605191a0903031803070605040b120c040512012405011e26100909030503 69
    0x38040001c000003000000c1c00300d80115604840d019031b9900100f419130300400021000c05031080090614401c242c48403440380d024648001d0400800d1000180c8410030080040014004040c01381c083d4140030f4000307402c80c0950301402000034130f00800200060800d80705a400341e0b01e044040c0810b02c1c2544c0710b82400b410020040410b0100400c420000201e2071008400184030203602e03c4803604203403608109460240e801584512180c170291143c40c5141030144084031813000c141000e80715240c202e225140660144180e041c00040f032150b0420840140c0004124030840a69800365110308054070f90380a54028007a21405c14008804034520b4135101c550042056020396080030707541c20001e0b0103100240e11a2411340d44540480c0c0c0c8940288800310810440718800b122058140800240081005558580c40316005a0072003c02d5025098400050703c0c00015288100b5950f02d018450709020b552083e9072100080c80094901d8203071064000c2c4503459680ea504d0b60702e1300500141c441a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 250978030 1250 250976780 250976801
    0x40903050906040b12010b03040803160219140c120703110a0f06050d0b010302120601081503030c0d0801151b060e0624100504090e100e0f1b06030a 65
    0x581008400c01d00d5544002a100804d45030040c01c0d583c00000c06048045d03001a400403070000028001c0c0300010700007406983c2e10110284070420070100c0008224038010b45025264880032641c8100b1041c4141c0040041c0d08041c2002150f15988007c400c1c00f2018054a62540340341d0410101030000540c50900d8402e069001440c1b030004584540d1a640d003803d1640c007020100380009840200706075240101d500e103c00908046003000900300e0a2020f84100402040c10841034200144540303400880b1f80911038005012079894003003100d030b816519025a42d041004c94003520000444211101e20001e0910a540d242c01180310624a0030042405030790703040751401d4850385000180340c0c003081640d02c100301c0910307603101c0b0440c00c5400402640105589500803682550002100e82e0410201c400700e9000c0d460014522210050785410f08628800c800c44075805c1c00034a104007070000035004030304640203054402c02060540d10100744e65102540b260403d5041c00000d54007105a44810b9a40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 250979280 1250 250978030 250978037
    0x10e0906091e0a02060a0207180501030312111308060901110c030a210f06091d0a02060d06090509030d0c17041b1e150912020d050a02030d0206150d020f040903 70
    0x10f05580c00640b058001141490059014090402c4110341001055821041d600410803082d41980ca00800c80401c5802030b450490300d03140600b80b401320907000c65900000d1071a540d00c085403280d04850322840d0a0382c1c2c600380c81d803c0c8a42d070030085a1aa046039140d4000f000154a440d0784164203507803200a81c41140650104080c41c44200c4501c0e0003241403c0780740000014880c1e0624107607030212440030460072001403041d800800708060004082090070307011160f041e00c0395075215004e001342002e80c00c0150b0040c10542480040e420010250090b0007807150140100c0300c0300d20302150240903400b480364244420710b0100b0082031100d5005d03101ea00628141011103a00e81075041c2c02d0001044101188e882c171030a041201010508034049034500601d4a10485803902d284210030070aa01000307880740421101500070050704009000810f5400380a562190341100c0000c1e4540310110b400941d1468241242c400341d00d00080082c8009500400440f0b10380848024480103140800c02101030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 250980530 1250 250979280 250979293
    0x311031b120c07060c0f05071104020903190209070302160807050a0803090c0f04051e130209011805131e020307031b17010501060207060c030315030308010e0906091e 73
    0x5100e01c0d044128072a0800e031440e02d075110240c0c50140100c0320000041e808100c1049014007803194403e0440e46100c0c1c10188480102c1480300002c0d00900c6170448143d4148508880c80c1d40c1408100f0f1060100b074000c8030350440c00d0740c40c030b070050b0181d1082c08462548004000038520000302c5600140c0402070046044501c81c402e690780c0c000b260361041c2d07001c9140c1d130300000d0400058501810502c0c40500f06680c20300c0f0a08043c0071480018100307021283e00c07458441c001a21108810000c03da18039001010341040356036822028201041444500341c80c203081c180060120341402245035001d81d44441c848081000c00c04a2401140326448101da040c0200c40c0c00001041804041091042d402c0052451603440e000d507410004500302c204100d41d0741003c004021180d004522041110050f0816440140344d41c5800ca00800742d000c0324003d80400c01d1804400d06038400031076411303a0f01c9003005003219220060f0066641030708680c01070312680100c00c10003500c82c800880d070a003003402c2c4044518 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 250981780 1250 250980530 250980547
    0x1080d0c050a0f061a19061d090c04061b0f020621040501051807080601050d021503150f18180c0405041a010e010303050d050c090d0f020109060311031b 67
    0x40d506034003034242c0e000303500c2d28851038148007032862081103505d0803520a40350007130400740315030131082500c10a02031045405000716442404120081c0d0501e00801110403460503d5507400e082d0894014000000e110f00030384004071212155241c8095009805440810140c1e0f080140650007050401c86140c0060712900050104400f883d0041d803207900041600e1401c030f080071010308072400d026411540080c404000340d200100700c60f81541c0080d81c0c070100c608100e0001c51004580825417501c0348000004010100c001c1d0090800807100445654040007000c0080108101ca1008904d500302d00c2040030401c43d145d29000c90a13180d40f4207064520104a010015044910888056400c1804051492003440310080a10f014002001401c0425415a1002401e6008091064000f03c1d84c910108031011401410382d005078500810381c000c4c2d800359250943c89001661000c0380071400100002c1082c1d800f84c06005e845588504065007150784000d540c0c00e088024803440400d20004012165 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 250983030 1250 250981780 250981793
    0x703060512010e061302090604020c0c0604060309020f2b02040b030d050d1107050304060302090d0c0b0d111c111e031501020d0e04050601021203070c0309090501080d0c050a 76
    0xd00c9501d00c540001480509805001d04100004103800241c1020980728801a074400b03d45503040941550010b849003000201e043c038100400c0e6655610480101e4005001540364001c0e20303400d8801c0d40c0c0c1e20740100b481c00074840038021a80e101c29600000d804029107000c8401400b01210380000c0005c07a000703c954000c43d0402c142d41d4002d0700000e400081c007600050050140c4c0d01100c5030140c02518000282d00c80d00d0300d0740104d0048508045d00040c1c464001e50b604445102e0240c0c10150600310180d46002d454007581c40105016071840c104000321000380068002d039801c141d00280c030003440e2010030600d600100803024036401d1910301402903c81143c000898030b504907100f807124907aa41803010180300f03a500021203050465000d0342034248071a03400803561458043c1520081034580711280140c7c10010010303c0c0b20795940010081120140c1c3c4418081e4180d03000e915400710301c54a941178034003514000d0041b429580e000880c001105845880c1130b81e005401581a544110b03007569508 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 250984280 1250 250983030 250983049
    0x323030903040e0c04050a05010f030603081201030b070207030c120c090507020102030415180201030e0c0d060f060806100b25050a0b151503070306080114011403030a020a060507030605 81
    0x20309141c1c800b02d03051103032400300e00e0300580041a904449041c185880009500010340d401414100700c00044a291440e0103604104003a40d4012130303007030700d50494400ea00e100c80300922060720080003041c0401e8019002084a009498100098800241c03c003110300c040e2207040c50044440700308000c0001000b06e81841007500402d65a800560360781400c1c2440740c01040f40042e101e8000d4945402c0c0c603a03170307100c9106c058104ca0703081c00c01080100c1c940c0341d1340e03003400410003116801181c400c0001003001072580c001c0b1803403078020408000c0075440b0621569520800c4512050075060082c050040c00d50309009044603800c00300340188140515800c9807104845030408542035446082058104404800c0e90b80d0b00c605880d02414030030040d01c00103941c810005261000c00c1d14000003003000c10744241c01284c0a40032010080c41444401c00c16a0380c441d10074440d882c21f0340c054a82401642c0b501008450100c0c940da4000c2c50380c51480e4641e100184000b42a0105066980d94005241e40b40c10104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 250985530 1250 250984280 250984291
    0x50c010509210105060f151e0f03070324030209010504150f0b04050406150e0d030210090b041103060105060d02090f1804050d0306060f050c01020702041d0111090607032303 76
    0x13141d5800d004060108142080c003055100382c10803140c0ca4140d042c0070041d24007002d2110291420300340881c020b140507200f620303d600c6030b1150002c03c111301c094050b000b25068460341005100c500b040205100805103103804000d500c094000b004000310318258021042d10020009811400c640d204540030b100d03545540868504c94022508010703900d058850300c0000d00c2246036549003401d410600819020051120f2071081c1802d40c4007030181842000748600c5505000c004001c106420309010b03444240480701105d01034000000090203080c080b600504882011f00328038201452960060003941103c0040e40c1c100c0131111801300c2598454594001d1146020041c20f501d0406086c21400c0c41d8491902130189410704004021107036106070704094000c01481e1040d10b0301072550725240640308110010f0340c8242010805d040442480283c4c2040b5a4118004c0000300e10800320400309004038003031503a100106200748004280100c4100311020843e801e10a4251010190781c44150000c1e60b1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 250986780 1250 250985530 250985533
    0x303040b0a0b03070f05060a12020d09020a0b0c0607080a0e011107030305130201140c1207060b0a0e1302090411190618030507140a0f060201021312050c01050921 71
    0x10720404014500c1104000ca4043c2c0c080c180040c1801c84030750000301503214450280030b00040441026105402c01c0008488410741555a40c0c030050120001d00341500c01a031082010f0040042c48003480310803942d01140907005001180d40d208802c0c0e80e40000140000840c41d00d03241c035500450801c1c0b080ca90f0840348601e05503291849414010100d03140148004900355503120b030000980e0300714840d51182c13038050250541c1c9021040c072031420901d0902880201031001324602040028030b410100c0401800d40e00fa120300d43c0c0e9100340c00600c03d419140c52240b0600c00d4000700c00342c00d00d03146c00c80c2c0c4640541c1505000b03070358038400f0074218100721000521409007020309004885e84064400c2c031192240111017100744c20354960340d0301c03450343d0f1090160382d19110381107000b15110046600014490031a1b8841c044e503550101038040d42c0040c0340c0315021f0100c6840403500f1031110120b50700c1250000d00070441d07140e00400558003a4071080000b0380c4030b15040084503150042cac803101504169041c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 250988030 1250 250986780 250986803
    0x1a12010501050a260106030e060f06040e101425140703140a080f0a06030803180c09090105310311010209040618110a080f0615070308270c0f060408030304 68
    0xc024200c030708864090110f9009001403214600c07080582b10380050f0110750008004031a4101640340220f0800c03182501c9040400121a800c7c5d140401d902c2244000d000c18010143c2c0b01c02011789207201c15000700410340400300072120482e941c0151401501c02d0600b0600104608040c0030349801c229924000140010100000e031407030800d0460b04a0b42e15101404443d0030b56581009600006080100d01403541c00b0a01100c07008120880c0360308130240092040b0b04180100a01078803086403c280c402401007429110062681000320342c612840b820750303c246000c0e0b942260700002d12030180300199000d120743d00c06507503140700350001800507884889014025641c4001030314030544186580b504244100340302c4642143d00740703070b00500910004e0543c0c1d490b14001003204030b81c7c030300c11800218007242e443c00301a0000034180c05456100202081c8070480700784010100615030f00034a00782c1080c6010703503180c01c0c8500340308554840204a5414a9150350911385150001c441c1902d001c0b0050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 250989280 1250 250988030 250988039
    0x6110c03030613020c0a0204110d05160219080406030914060106050c060c032715040303020301050909160b091203070501020a12050103020306150117070201061a12010501050a2601 79
    0x40425606406100600754217010701480910381701d801181020b40959160752603920307143c9a0a048600340443d164041241c0c0c00c08005020701101c0c08000d0720058442c804042003a556805402c54012364040324040c90030b814840110003512a01400b00e4a500c2e401c2000c210243c4103120306806401c05a0b02c8a0300d40f00c10060342031911a02800c9824002410000e00035110208071700c61949040c400342c90300d110f4081e14105450240702019000300040d0345010b120400d613150b0000e5040758411038502d647c40e01d0340090161034256102048104801c01c10040009a102c04003425076804003d1603540000b1a0311100790540d400403c04032602d0754000348469040350800d0f02c034000d22100941c03c00066040d0f1740032941d203800140c003036000701c6045080c00b0000e84c4640710402c48c58805484a18103070601402c064041c0042d800b848a0f42000148042044214081a0b4001c0c16000760ba08403039901c0d040064031075601070b00c00ca03002c11190301c0380c5038241441001d050710401584200200c0940c1351 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 250990530 1250 250989280 250989289
    0x4032a1b090b030606040903170c070c23090615040b0c01060e0103120c02040b040212040b0604090819050910050c2a0f0a08010603060b03010b010804020907080406110c030306 77
    0x41d8001d10038540c40e14405030007039240003611907803286007614009009505824181c907141c440300004000d10080c3d408010710000740e1400b51140520401e002d028140d1114600d0205204501152009001c80200446146021501a500040082c121842e000003c1d15000b806a22a0b041340540102c006011081c00109109d014010301c0700c0602035090394115943c0002e803115402032001003203540c40c150001e40da15035006070012030004208565604900707a0022150b00c0441c0c0589030441054000744050a16010740b0054070f0344480d8240c0707010070303014007e809240c8a0f074090040180500c0804c03440d884401c0014104100e0340c03285500d1f180040c2c03241d440d1240031055a45900121030301c03509011010700323801001e22001c642d0511036a141301d0101d041c80743c4039400742440390f0800384000207001702035002003051182a002801022020350054808880036903009401083e020b001407541485208000d8225215440118400720100740ea060aa0015000035500d074000006210080c80d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 250991780 1250 250990530 250990583
    0x12010e03130e0615030a060e04110f03060c07020d06060b0309070e150a0b090102100c0908010f05040b1303030209030a0605160c170f090901031b1a0304032a 69
    0xc1038800721800d0f00d020710105a45100c0d0000c0c5020103180407000ca0044960368001001030f101c0c0700700040c1c1a10781400d011792440200c40105005820242040c001420003203100344c401c000510640d031410b1050b50a2041c1150600015a1000d98404010a100c5001d100960044402400500f0054101120100b0248015006030420201180c0e8150310343c54490501040b181c44135900d42d01d0700c071644010b0b810b110401e807030040c000d840c102d411195181c02104a1041da143e4900800c480750084e80680110b074000c0c0c50141242826a00066600b04140c212440f2240300303283c0035003449120800300f4904449030500302d54050315a420003120007004d0300d60082000683c501014039006071344604000d585946010740a960000071aa00100811000c840c201c034030140c43c01c00c40703680d24100783c01401e081d00354204550103810800222145406004110b203806d120045183d40c96070b69080d1141c0c164120702e1501100c0340b454880340300340301ca401a075086004e08500b10400c529503245199010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 250993030 1250 250991780 250991789
    0x705070b0c0d031b030504050a0b0106051903060302181306060e01050f011809050c130b0c12040605180d06090b0a05070306081507200d14030411040b12010e0313 71
    0x1880d00034000d0121000394613002c01ca00485c00e00040c141c8441c01c1c040d00b0400c0c00100500902004800015855402002400c400380c4072407080010140b0300301d088040c0c420520010f5480703940b6080108040c905031020035041200400a002c015110742e65a906582c03040e80482510b0042c04010441c508000b400c04032010001d1034094013002070100e180414046e58041c0c140303c0756a48000480030491202194100320145403a0800d40f0350f10003841c1c15541c480d2501c0303d00c0c0c0c003075661500005c860341001d070303800c1d0303141910b80906004c1480420041b8000c1c42852a0b0300c012495130800c007240d0584907010b12203010707664402c0503250060120054a4000e08840e081526000003000b00410200e0707130000982d6502400c101c00d80f640c400c2105e840001c0c1507123041c8028030100d001c017030b100d00040032100403410352640c4d80801d04000580000340001c650150107602412810405417420340d00c0080c0c050001880c2104170f0344540410703402c541c4d100300030b003645a0000446a04100c401500c1c54000c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 250994280 1250 250993030 250993037
    0x50706090e06010c0f02010225080c0d0b010303031109040c03050403030c23030402060f0301080a03020f0601180f0f0c121109010c030804030509031f0c17070e0102030705070b0c0d 79
    0x14245140000c00e006513581c1e001e02910404449001107a1003480404003d00300d51040031070030070f490308110500c135089204c6c2442d140f084103504017075070400c201e40c00003264010801044a03803840c2c0b0181c000d45540d9020300750045041007270300303103a80c0d0b288201d04034070090759000291881c02d0b2401500301c1c0e08003100c2100740208401e04040e00f900b0811007407600ca03640003200d900c17519244086151801a01d06440b1405008000411a4007000811481c003038080c2d42214402c0701c560f86d407551183c00030301504100f10301859010303804c100c994201c0352642c1081c4800044090365401e10000f110200c2c078101c000078a825484240c0130004c1e0042820214841c0190b40c98000e1000010f080418088001010304c204000050149402401661041440a4152a01d15010b201545403112000c10884480303032400425444c1e10f072180c3c00100092a0091504840d901d55446c15142500c020f0089170451100b00851800070340188001001014517100d107a0700d50310f003100b20504250110f139009080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 250995530 1250 250994280 250994309
    0x123030708190606030b0a0e070603091a090a02030f07060f02010b090714120a020a110a0302060c0c011508070311060309060a090c051804030201060f0b03010314011805070609 77
    0x8950100312540b96803600a0381a015212a14058010700025400a414944d44004015516010760040343c50300d4160070035140f0558a446058046410074500540503106401040d803e41200710180754006c195001103480c12070b15940028940002d04075400c14a4100c01804c06c82c65030046a00c45501415000a02192a040e400710320555001014801080015074015511b0014076045901c000b407074405510a030b1500000c0800a580300c01d003500001200c56007a0100700b44085949509168541c1c081e1480d030320342e9807010283e6000b00901c000c5075540e482c0605a2401c8002c0700ea00142510390242640c00e03d0750802010f0702084a02c0c160050302c0c00c01c02c012a0710408075410758030034000c4000007420601401c210305d02d8032582d000360b500721400d40080091100d4410440d4802c41c4294000d006850b1a80e5841007030500c103100d044203065052006000007a04040762100402c05480000364540e58840c0500240811300810b0383c40d50081c4006100ca00d60080054004c3d000070441c4091 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 250996780 1250 250995530 250995539
    0x3907060f090303060f0b0f18120102030f0703092003030913091e0c17031309150f1413020c060403120c05090a03060c02010f020f09040501090c170703060e01230307 72
    0x806c0e10a04449038508080001c0880d85550101840382d103031880a00180d055804111445001798402d4890545e1542c043c00080c010324401d0040720b90a50b80805071950442020000801c01c03104c100c0740302c0c0d05000521000080d91a046a003802d545201345001c80c00144604005c054075180562032103904000c888900c0201d0b00140b8858201c401c448003504400704403507455411070080b2003ca042602244c04001200c1100781c11940c88a03210740300890050344c0c0c904c0d221401c0210f0f403091310452819084104910f05e010610300c10707200b83c03480f8050320384050324844508044007140e00b21b000c500c4ca03d5040380c0c01c002030310849001200e46d0601d24940860000000e442d11210310008208649810510360a40c2c402e400507950121480025900d4201c4240407042c07640003002c0c164052071418000149041482c0104501385400da200c00380b0901d0f0100d414034545070020001c10034140c82e900002101e0b0b0030b020300303d4001c0080c074041000100517504500e00d00d0044103101340c460387c0101000d01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 250998030 1250 250996780 250996799
    0xf170a08060f030c1e0310060e0603010e060106050702060c070f0305060f040c120813090b040c182607080604030f0c0b010b0c12030408123907060f090303060f 70
    0x3021140456868040c6803442c2a42030501d06226100d5815016800355109001c7c4103822032820f94040d400d9007025559221b0501d800c80b605090b41100c0303035004000400c04240100001d00c296130000d01010314042c920b001d00ca14100c0c2c07070f03407240d41800c1c60080d0400c1440410b12510b60413a80c0c120700e6502e141015140e480506401e07018455040020400e00d40400c4880004c41c0d4444020420040c802c983d9007a450004202501c54640120308014503510340c1c910506142228a9601301484201c81c1807070710040c044414107880c0840d42e20714013030300c0b0105001080b00700c008201c600003c0a952403d4038004200211071090f8005204420529400090701c0d02800f03419113040c00c94a50300c0300d0001c1390071441c1004207203450080d07180010030700c01800380440003041d1b50b240c40311840c4043d0300c446803260402c41074003011000d40041148240c4504c01d8000c881140300340b00000d05810b054a50f02c82e5011030380c4041c2c08014443e6a45800401c25816000d0f0500624007281801001c610304030108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 250999280 1250 250998030 250998043
    0x1406091807030305091f030b030f070815100803040b18060315040c03060909030203090414190e101103060f06030108030703030f060f1502070e040c030605040f170a08060f03 76
    0xb8244400899640411344802880a205811502c081e16209182c01c0011b001008c140c58410300900840ca40c280541c203000038001c007204d080380d0040500300c500400007203480350040c108003031034501c426000801a1003000031b00040c3c01c2072100e0ba55140740004650a8040c80c1c3e4006a004a00c188204100e850340da0350045030000046d18040780103044503030f0840c0109802e07000f1944081c945021f003018180c0c00800791000703079000d5500b001074003010f404042c000b880c200c6030010301d40c108072061220030f0084d4000f12821241042115402000a00b41006480d5400c221008005000c0200101c5103400d5008001c000d5099a050f441d65050018a6407a4401e4600207410300d52504054030090340c840d0300150080c54a07a130303540c8046455141980e8640403545a035401440b8100c0003085810949840b00d000c0d41c1d001310078520240ca16a20a4007500005100b50f86083c021850200403650030070301c441550343c2c020780e40390380d070880310402a009980207002580550400041141507460000f800c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 251000530 1250 250999280 250999283
    0xf02100b01080a0b120d02010b150301030f020130020315090412030e0a02060403030c0203240711010f06060e1009030803060603041707050a06231603020904140609180703 75
    0xc21315000ba0800b04494503c2180740307201d01d01c40c01c403503096480d50650205400074000c5500c0400c9503041c0b90b40c1c0c1c0c482d000c2030001a08115004d07120b00300560041006641c000d401d22440c14079030340c0c20000b522183c00c8018903030812039000401c011120251045400c45080100c0300b842d03c6060585401400240040d0507c040c1a912000003450b83c0c4208107080f0b080794020002e030f507140c1d00c80c078005104c0c1c803440c035040f4007a101d24560410f0140c0301e650b5101040c03e0099080c507640c0d4503100c0c00c880300c00b1041c110710000d560314890760841c004a802001f010b00a0394440e2181001c3c0c980a03c074400740b80c96075481c2005032480e0180001a841070449070009401c561441c0c59072151305146caa80c80c03604a0900d601c801c0010800204a00403401d41076aa0040030104446460005a2200c0d54071620031040040209000034041403550965154034441e039150042c1003d8151011a0480e261034010002103c1080200600e5160005110754030501e24403c042007075141d9120b007940c0380040d000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 251001780 1250 251000530 251000551
    0x115060305060109050310060509010f0b0f0a110f0c1002012d0605090117010606050309062e09020705010f0605010504230409060b28090b0f0405070f02100b0108 71
    0x4220b050384079820041c0601001000e80c0c1401c1c41040b90755004050320b110305401058000000518106201181001c036083c0102c814a81000e100b40322809910041c4000f061002c0070480315400942040200048001d203001000a5615a41040b01c184081c00400013107a06100c0d4501d014030700301d02440d84160310a01d44010314180e4031020009045a03412440e0040f80c00300001650303900030b00550b000508d00c800200715542c1c450004550034441100c45000340d90002000c00c44824035281c2520310b10f0400440c0015070800b051202910601c141e0250356500d0700461280c090100a03c6074011a014500301044880d03d004006030141c02503100d1240303001821994641080ca4030101d450350b0f00c82c001c008003c00326440c07420f08010319285150038014800d81c0b1002c1d100d00a001c0f41221b10f0107240c0070071001d062400d03842c44050000a02d04542000380748400344290340702c9005450103621240c881012981c2c04401c024500b41070b113080741e141582040b0303210172035981207001319410045034003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 251003030 1250 251001780 251001791
    0x105030603010608010c05030709060203180d0606030602030c0c011d15040606080a390b07050708060c03040506070f050d02090303091306181e021c02040618050301150603 75
    0x3400207005000550002c8a25401c046908040560000066119a21684400760f441d034079100e040380d070b0380900344509090310740c2e06242c0302480c0f80c2040c4c00800244518004111141c482d55010700f80c0e001070f00e007030100e42008681101c0b010005e0144d445270301d4044440c0c4800348000000d8540e80c4407400d030b072a200010141c020505026958206401400c400401c407086000c4510f0401720186821480c844501141c3e52004407600407081d642c18070407400d036405030015080c11110b0320760341d0228404a48501c56104009081c0c00180b00007480384190320303407460701c902c2d050501e80d061100c018219010000b207040400a403079008002d445016009050050310b03074540a01291541c49505203940d80903c10108446a290103500800192241c10130040c0521320400e40c218180c40c072203150964100c08800840410103040e6010301401140c1001c0004440900d080070401c0341d1090300400001050b0a060410810700103103140010142030300200846015000600542d41182c002d8134100741d00d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 251004280 1250 251003030 251003041
    0x902071509150b0d0b060d02030313060203040504050c18040f020702150d05010b041809031106091c0f1b02030106030206040e01030501060b2805130f0f060905150a09030803190f0501050f010503 85
    0xac1050b540712103803a078603d1b54866111030003e55031f5045031207030310710490500c00041c00b00c10115050303911403400080070007a03203044541040080e1501c2c1070b1001441e0360910030748015948440210103100072080c60703280e0324101541450250780050300304a4050384100010048030008030b42e80d030001c203482c040015502c0c107689811585070603210000e40003842644180842b202010450300500700002c40e0400703590005031f00564000d0f43e45003020000c03c6010394920703201000000440b10140c40100001003854880d800520207070800c0d00003066014603000103104001c02441002c014141d41c821260030b1821070000d5540301080200684110016020a40c500c80d0180302550f41030380901c03180b16041e03502c4032070903082d0105610400c46544040280042c50501454200094440161220100440702c0d4038401c01907100301c601908104640030000701103910380e000765002e4400070030380d003800a040300e0a030401d6805135400102c901e460640104070356960f000c1040c03c1a4402e0902d42e0b1a5500e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 251005530 1250 251004280 251004283
    0x1060219081306080703050a0b0303090103092a030b0c1305120a0819141e03100312111011041404090507060903170a0203040902071509150b0d0b060d0203 68
    0xb41440e10707a40c618218030100c1d849400614a9100d084541d804201603070b50022001c00340c2e040300001c103816070020041c203440e9521a40002c2113550056808a01c1b01f16500141c0c1540e1580b19900790355040c19460a1040082e2a101e560300040c20700c07119414086100e48800d000007040c86482d101c0c444843c02e0070340000c820f018580559400002140e10f5a0040344c010f284101c05100c01300c0051540746000180381000e80559402d401c0102d0102c50700107001030541c0e0b2613840a0f006207510460850000002040311003400140400d9641e45100e594594101524046500302440c0405003020306003005210340f00c056500302e40c0031298080640300b9070004100203282c0700801811a02440002080703c0ba044803d600489200f000203850007181214181442c1c00745a02c0030300182c03c100b01c104500312644d00507010b1203000301d07401184002011051070407240a20000c50750f041c0e2442071010103070304078450815007040a80d10b80c04505000d0fa01d2140c0b2b0303400280000c0c8224100e10101c000d6480 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 251006780 1250 251005530 251005537
    0x8060f0a0b011b11030c0402040b16020d050a06020406030501060c02010c08090d140a02030c031216080f0a090f17190303091b090f0204030b07080403021f0618050106021908 76
    0x5000c0c0c0c40040302d0030f042c01e0004400651440242c001d200e0341c0701c040b00c80d0404e84212400c50b074074218045c3c200211050b05104107100c201c4141e901642c0f0400c4036010540a00134003803603c0c45000b0050b6a00e1402802a060f80c605070b01103014402e00701580c1000d0b1341c0194038211003e60100d403a0703070b0303443c9004000b4130713581107169000e442c802440416610b608400642c2000880c000c5044400303480f085020140e03101d08407802003803c1e000a124a080c10148075409031080d5200304011810300030203c1c10f50300b035034004070b4258002405c00c030400c0040c80004003442020703011101041e0002c00d0902607007035458080b046602a00b0b02450119402c2c035220783d01c54070240c1c0d0b1013034083d070a030b00c00318500c2141580140a488030107440d2000d1046807040610844080b203a0100616420750364255041e1503003500180103405500481e248038541481d044064012071484242c001001d0b03003010b03110f001800355011a48901071901005005540c0c0000d00c80c4104401c145500e03902c0c00403441c00054900 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 251008030 1250 251006780 251006807
    0x60204080f030d0608030304020d060f090204020a02240105062506021b01060e0112140a02090709140306091f0b130902010e0301090206030a0f02191808060f0a0b01 72
    0x10703005052040700c404401000c1d40300a89006114450305c50515503140d20055400951240f01d81400301c0015446402650f0221211840012640b96680104043e41c0c40007405400513048405406880040600000101d052a00707005c6610b42c18100420598440d402ca55000140d0040017504004207100d40081b0381c035800345040d5101d902c00344d039030b41c420069102448240d5080c402c010a60400043c1081e040713824008050f1550401c6444070304115088901617103440c040c0d01c14240168580701181c80c0208001e507190000540b4000303080010f41c030004402d0b40700f03410010070302c4404030700020141c0000050f106040c16541d90100044000d20204100d00c6d04803d000502c0701c8104044d51046244074000e0f01c4407055000302e4402c041c2201c0356400020340c030a03010b00100e00310310b010754892883c0d45034420380107151240518220f894030514040400026414520240500705c200341424010003180f4020301c22070421501103034001c00000d05c07500e1500d5884513034580580c4030340c001c81c4429 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 251009280 1250 251008030 251008033
    0x309040f0e19030f02030a05190e19090606020f1c02030c010504050c010905010201150608070e0405010803040302120312130c0314010603020a1a030103062d0c08011a070b0406020408 80
    0x1c914900100c400075101c40303403d402080e03018007820b101d0741c004001c9072907148556032034034940400d2111980070b0020b01c840350380030015016119000c6840e80002015501c0d039490011254a25005581c0709448140e000441107401c10500307000000800514100d03d81c00b6500f2489522011903003c034a140155000c900c0d0380c1d800c0c01e0034801849404640340803060001c0c0da40c13001300754071680103a00361092003025400c213443d13025040000d42c2c45040b255030000c50723a240040d618a0450300040aa81e000e80150b5240d0b000020200118540388803039004445140c0d0145041c04000c0d8840903032a4002415890586070741580d076001c00040161401c0515401000e0703400350381445039071030b00901d0741c0e000890203011046408995071200604001000f110852200c0c030316800c0d5658603001c0c00140d04400e21a1083c0400303480e03062110b44c4c82541c1d2103890103001070302400b500801010132406a1100f410313108a00319888544030700b40215040140c029068079841d80b500c2c078141c0d00030b100b6035100841030b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 251010530 1250 251009280 251009293
    0x6070b0921030618040210030509070f08060105090105040603080d0e0109020d0b06100306151b080a080a11090607060207030e04050702031c02030702060123060a0503160e030309040f0e 81
    0x1c8040000145001d0041039403d4405481c02c000c94041d004000c0d203019611668500c0600c01c510b1103604a0f507840000d200603102005c0c0c0d87c50604011a503590000ca0003604960018006410141c810131b00400084074280f00462848c0c6480c1724034440d080c918021141c50b900c401902c60740075004000010b43c041c010001210f02810b06101c0740310143c074214820741340c81e0300000c5200d1190046200f61280700010103840394804c0f03003c1d01c29034a0b011115424020500b01c000108564070040c010a1800740c4038031445140242c040fa007245ea968907a42445401400a00c0d040d88503002540d9903140e2107980141d0300c054a007002e881010300d18a140c2d602078144010011000d5012000d413a07003010075007401c0b51101da00c500308001da02003100c410f80140d01081c01008400100c648060706401c1d0201d281801544040c08260b5030f038050122003022450010070f102805400b03520811000d441032501c58160070780f003030019850384112160b96115039161002c201c4e48000d164065143c0c82c800e01c085414 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 251011780 1250 251010530 251010583
    0x2701140a020309010b010807020d0e030c090702010e060702030412080a0c051246050f0d05191a040e1e06070305100b070308190f09110102070506070b09 67
    0x1a40c011144810f8a5007444d0405403154002d116031070041e00c150300907101e12120301804445252010113020786c18400c01a558021780c85e0103403403a004103059400482c0c0301d4194031259250841c0038140ba021544100020401842c0010000c45d036154006c0001e0360710484860100d8031f200d25a2030181440c00750108080b401c0060300e00401c006051654400075084040c21400c401869880c1c40032840c241c20a15404144003a4060311410915400c1c200c1c1010302901024890360031016000b0702d0660f94a0a00c0917803d00182821003610880e48140300e28080341c188141111840381c1c015019948a181c5410354a10500200c041c610704900c855880b501842d0080d903440c8002d46550000c03d213030001080e5400c98012a130301c187e41c0a40c031640c1c0f030012140c0d000c55884400400c21060480500c6d90120521103038000c0748020114604085001001814203034815405a5421070655010800422041d22000244c030011034010386903504c1642c41c40071090800c814200741c010205181c071092203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 251013030 1250 251011780 251011801
    0xb0c0d020c0118112e180905043c03030e030a170a0b030303070c020307030212030a0f0503090a030c0206070609030c0b0105010e0d080a0e101d0405270114 68
    0x503e40104080503084482d0f4090205448940c09030070604042a500700425842d25681508601020710300300140340011003081c0f15598003a0004201c141d10b07078007030105004815900c1c503010031604c440d01c0c010b0a007641010003490003c00c92001d078110010844000d16009078800082200d03000d00392981d4000c040002060b040304102150948005c003004500c4140941c411186d84200c0170f0f00a6240d1b440e040019a001d03405004100c3c1d0510a100300031005840781c480c0c618001042500031502c0c4c119095029022011002042c02046402d00c00c00020318000111296030302c0c0c1500300b01c08440d8250001c14001d200384c582c090040f03424980603008040c1d00655014050340107511510042e41c0b16401101e070031615011250744401502080400b0a0b010402006451080d0400c04170822561002c9800b56100d56040c03404600c1100d5611130000d507441c0c1e20741600508440400652404007124414400300308030b41c1030040381040080d940340714250300111810b240004a11058a132002522 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 251014280 1250 251013030 251013071
    0x9310501080705040e030405240403080406080105011115070509040f150f060c030c082508210f0414070b031f0902031b090622210b0c0d020c01 63
    0x2e0144d86040d9104401840110560302900d400500a404c100c3c0e03800c91407020320380704003440324101c0e008000000000b848480100300400c025125640079616010007d030414080c0e09a80d0025000b0300501309040350031042280d440010342c28490303220700c42c802c04100240340e44800c109919140400d00702c0000c02080030b14080710a40588111120349845048442508078034005010aa04045c494005842d0300c0140850640300c05240e00d480c031030b00c14036110350701b980b034000c0c0c50f800030008011245404589080c43c040000c140c507001c141c201a40a08c4551301c00030405002c41a96240c4210700030707000d0200d94010b109210b0b550f516400d20451001c00c100300091504803441504c0c1c4001244e070070b14000c4c0ea03c030300000780c600a881c200808119030650303c10a18180d104000300070315081c070144040340300c0251415030074654406041402144c03005008072291140c03142c1c00e5440e0360000d21a01da000d6801100c501c0030319214264060079102a0189201020980d401c1aa0070440c680122038403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 251015530 1250 251014280 251014289
    0x50a020906010507110d030c15051801060515130510080123030607030b1906030207050705030c1c17040803210705070209060d06110307020111093105010807 69
    0x1121154032807800554892041550090555000008011192925044190056020f4200050301c260655100754201d4084200c40304010f95503007d002c61f0f0f0086407104292034000c0002000078904203800140c40c03043c506503a8501810018444680a50b008800350007041c024000100710100520b001c3e21040090207405c0030b14101c01c121414100c101282203602d118041c0c050b2150f0b4550b208110080c2c4060400076802c110040a854010300307508074404010010369038010384464107403508070f00344101039004500c654403080c4030341380a41d00d074640d66491090030341d042080745145181036401740880244003505050040343c00aa179040c0030000b0f12000e400e00b1402140340900408a00c0045401c0d0b90020028078180240b00050030084040ca400202c000c00c4018030054541d207881c103607240707654101200b10011041c041c2441d024001c21007103030060708240742081500c00110f801d61a450401c0c904e13002940c00d0410104589411030304106038040000c0c0441d40e101c1c48803581c0d034110341c4036 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 251016780 1250 251015530 251015539
    0x912060405010e06152701260105070215100503070b07031e0801061409120106031e0b0613140c0a020c060c030f0a02070902040906030209071e03050a021204050a02 72
    0x40c2c01441e031402081d03851145018000045d003c148031070510015224084902c0e2071103a903081e442d407007840090022802003041d1490301061520b100021011182c00b240c5040076a070600040c095904e0700850240070b0032150800c56500c1d0703034540010410340502c960020ba00750150322004110480c1000040007928003079100c040340402284868410300070031a40010000c0c41d500014090248101d03040b181e1804240303071580c14144a80002018840d650005c01c0301a95522010030400500555048400e0400a07031034440b1000c54030303400003040d0000c20080c4038a0740310180819900d110340c0039001020181818640c1860015507009440d400182e8080241c0700703e441c00c002c3c03883e1803800c4a480321007a0020f94280301042d014000341d900044001c00560140072008240c1c12214030151000740203041c8081461840c0d4010b008400d030303010348200104100c41d5000c0703c1050b1031a901c4001d070380c01498000303241d40c1d540020740d00a02807144540c40a00d02c2d003080c00f0a0103400100000c0e2140200c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 251018030 1250 251016780 251016791
    0xf0120030405040b120c090c1213030305010b04060203040306020906040801092301111803120304060501030b07030207050a02010c0318030b27060f0402010c080c01020d0b0111030d050a02091206040501 88
    0xc104200500000f0381d00101350710012052085040129000c1d81203038812300180d040800fa02100f11074803508a81001c840c0c80501481024154940545401855254030b0300d8034280c1400802901c91146000c09010f942d000140ca0115031100406c49004100039002000601140c5c81c1c100405030300310710201d0707807103941a4809166000c10321441c0903c0c03031088012490001480c04031444000d205010702d925019030040c541d03400059200651080703224990000c0c0035819443d0a07005540d004e4644010140706102e054001880060b605101c1c580909040201d80030600e030854000360070034541503c07003104400010400c00d10728549070150000c10740042c2510910b000081c1a610400d0140421f640100d011a030700013000754000d41c1060040c9860041c250349a110350300e030f660004000107142c0c0c0d400100a0002541441291030010007440c00d50140d07807010a01d50360f85d0240402200c182ea5071540401d84081c0a81d0459070440c4014041c0d8100f00048964141c40700401c443c01d541550030701 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 251019280 1250 251018030 251018051
    0x30e01110910030f0e07030f06050f07090605031807092a0c0b07020f0d0504050f090115030b01031b05040f0b070f142d0c0105070503090f012003040504 67
    0x741d69505001800303a010480c0c1a001c110090003503110800d648680c2c0b40340044080c0d8090241d40301450044040a442101901d818070403158020142d00403044541700303201e00f240d40041044101d50040c54826180c5e00c1e05502c110b0181c54400c04120184a181d1001940c95120f07003064000c05007075160b1050840e0102e10107041203038406100400a046201308900240303201000642242d0b5610440d00742c8070488a4840c035000c041502c0130085900840d0070000d600c0c1009810f80192810790306050594901440c103c2070940b0100f00300c2c140f40d02c441c40b507405a442548140321030f95941c07906148090780b54101420641c0140038407d001c061030386021680420040c11502280d81c042c808801640303540c2c54031002d00d40010b000500f00d0089420700c0546502c90550409408192016500f88070041c0103800d10705210304c85110705101040c0104404243c000c015980e45400030f03100c0041003d401c0004aa804041c0030090712005822002c20380e0808001004d0000d907141134904000c0070008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 251020530 1250 251019280 251019311
    0x80a0f0e160b030108070b31151e120908070b01060e0a080a060c09030b150f030c031c0509060309100b0103110304030e041d0c0312030f0f0601020a060c030e01 70
    0x1740a40300b86603200810800000000c0001084401c0e69a528407100c04c0041c181040d03020380701c0244012011001e0b5080c4040c1e00c1e094011048911241001080044103002800c07007034501c0b00c48035003400459000000d0540d6990000389180760700500c926520740c550710b044200f01c20300703014000008001021800e014100001d0702c400341c1d1007207030041c07c000b44103a03541030290260138480030402442210020001b0301ca003420074010b00740c0b2164081000100028412081d1841004c0d41c420342c400d280c1c150043d10b01080e034803001c00d106102050044800c840c113035003511400c161160028400030400113122804540180d0348101002c081c041e06080c8001103043e00da200c034011880000400110740000d0140f44014910070780a040402c0c4143c02d11010204000c01e0004400da607000903945001c07514080c0403034030b8000d0008100c0b13415800c0121002c101c1071401012403070b040c0e0300c2c80e0108086070700030421849402d41c000018000895086002005040f903d1600e199960905801d503c04880 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 251021780 1250 251020530 251020537
    0x20f1e0d0813052e02101b020606040506010c1716081305030c0a09020a0c06020a020f061b030c0a27080c0a080606010c030302090909012a08010303080a0f0e160b 71
    0x12110344c403202000303030014948280001c41d200300c00f588550300700203100100300c2c0903490100e42e2043c04550b0703080f41020042d00703142d0002d1030180700b00d00e071808020650b82c0144022144a41000301e64043c29460031082d402441101301100d0b41582c901060004c0003200c0c8010800104540c504205903540d510a02d42c6e105603e9284e5680000000400c2c040c0c0d050540c09449080c501d450103440014050720b330700040760300a0781d01500582258841207290746003006901e07046414410035000c2003e02a0940001d8080901031511084001645c0c2000e02c0c4101c03000c20741c0d500c03886200001080b031356803440c1000b10700703100f01a4031b8010307148148264608204410125480031707020f0191592003000454850300c0201d07049050503030a001d8900e10f511401c40081c812400c03580009100c0314100318003030741454403d0f1140f80f0014030743c00366118070b940111003d044036807508102445880e507030f190700e02401e0412031407951986400e4400c0c513034800029540f52021142c6514681c00354032902d16074030512 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 251023030 1250 251021780 251021809
    0x3081303051204050f0402160b0702030408010b0a05030d0309032a020f01030c02060106030510030b0c04140a0f0509060a09051e0c090108010b0906071b08010b04020304020f1e0d081305 81
    0x1007203485ca8280906081c0c000b41a034030b0b1100c40001003203071a45d4607400d1580c2c1c1500d05c18016400406c090140311000d10981026000448281070000d1802c40000c1d500d91a1079402020151681e40c40c40415014202c44a8040a299002480c15042c074ac00138800c1945000d0503031041902130740d51101540a841100c0c074440e442c1d4043c00310f0381e0034174101b0742c0602800752251030101120100000031541042085018288810480d5692460102034217000c5a58a020600c11203030311104110107560b100c00c2104481c4150317201c8285603070320000a00c500c0d0300390344850f80050505c800c0081e8001c40038030701c0120740390760f8600d4031594071500003042250203034111103804a8484c0006000c1d0b10340600145c04a1340c0c3c0203104a2414000c1d65031002402c12080450443c06400e81d02030024007005c0c05200b10145060f5411800d600d015000104014100c0c2d0000b405084046541655420445103440b007505024043d00b03a0500b6510308504540d0259204120641c25120702040e41d107001c4003100242c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 251024280 1250 251023030 251023039
    0x2130618060e0904121e0e0a0e0c0304120e06120402100914040e01020c0f0a0b07030c0509060c070509012312060412050c06012705240103060308130305120405 70
    0x507621680c402c040c104d03400240e082401251200b03c044403451000c12503a00c401580d0304502c148110007230040d00358031500b001001e10088003c1015400e900d4060300c3d40203030030444209a00240c0c3c0b4041d11240050200c9580026002408080f082480c0c0001c0c1d009500c02ea543d180d022490344011500403155004145018001800e040b08900e030070342100b01d407404031100052030304581c802c0780b5140c05d100d004a000580c010100f6007085c84955201950711802c5130a040c4404e24440b003004040c0d20030381c440e06101e460003094407011101d08000b4000600b0340502501000d50710351460b11451440040f050349040b032481000105802d10941c0000044d44110041c160f80c1c8481e42c9014010501184d80310030882d080c041003203c0c01d030401c8840d00900e1070b0f040001c0980b03010251100d00d40d030400c1c94201c02500780020f0244880a040c2d41e8810b502d410390075035400f010a003004074082c0c203282d03101421410000c02c080b03000c405204103c01c1224403c40485043c10309410159109008920403607501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 251025530 1250 251024280 251024299
    0x80615060a0f0509270f0c070f030c0c0608060301110705030d1e02180108060d051b030307140d0906020604031205041103030a02060603070603090510020d02130618060e 74
    0x1410b020b0b10041051400b1802c0c2a42030281030303408a80b5414440c0395180d5000410144821100c05050240341c22803d40d5440f4041ca181440c0c00900c540306144004180c03060340903501c81414462103200d1015584019078031011592001e00820b015020780c1c1d414400c0d460040740040c000800c0c4115150550701c10099400c141c01e58400308000d00d241c2c0c500003410903640d520a0400103403440208904c00d150521034610a0010f8001498410010080342c019041c0c0e4075a000469400030b1280380720300c8624240700c41d40e146a03010070301314068101d005000c110144c00724110204040b554113010103059613011703200c40e9144012070b075501082d10041e012401a240368513511019400c450703441402043e003203540c0540080802e00d1a03000c03090b01c400682000003807188038501031040200410707491070709001c03928541d1a00c50b1260581041201c405034001004000001c094050f00e0910142e02c42200c90301d9601d01c0003802c6a207416248580d00100701402051542c05980002402c0c88040c090460 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 251026780 1250 251025530 251025547
    0xa0c0b10050607050105010602010c0305060609040e0c0d21080f0714040f080a020f061305040207020d0c0b03090d0801060c0210030b0a0605091207061715030601090608061506 77
    0x144290180081851020001010503103840324002040103034400c0300001141e606d001d6000f030031122507000d07542c101810441070101c0c55488009030303a143e20040364005004070080c44007030b140041d0310742001d0708140607070308810500910008420044002c8000b161b40f4200c2800e04880c6038200b1642c50307600003000c030045000fa034414046201c0d11403000c05140d14080c9c8840302210702150341c2e40901ea039540f04504840c1181080403004503909070503185a810070390301c842000040a014080c0c18066640030400d2800c3d540c03a02405009981c12404142d403090f01d600400c0400d1b40200e406103a030b4815001c008001c0f910518109040750b0701e5a41da400d00b24034035402c0014580201c5c0d5003008040d1203c0030f40c80559038221b0404020000354031000d641785005030512404c120b802d04551130306c4c5c01004c01001340682154402c615000c00140c46550359441c0b00078011090301141c80c1e1501881140c0021400f0a00ba501c20029101791100311b4500355580c4807480100c1d40302c80308140d008a424002c003403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 251028030 1250 251026780 251026793
    0xc28080714040807030b060102010c0306030c060e0118080309010f0e01020606100314010801020d0605031b01081b0c03090414090d03050c090603240901030b13030909150303020d02030a0c 82
    0xa0781e072004064240c074007030781c92001d1407900c845500103603a0209010180241582c092060b11a046003c1c03d0910030203155450b040321415141c07003000d040c0025007102c6c10145c2c1c490903d07400704611a400b00000c0c19203c46590303607071b074000b516040d0100d1807015110388170500a0034005582801680242841c0e81c0c0d1a00384200d1409031045c44092580b200d008440804100c04900d001e803680100050b140c9003007800c4042a0707041c560240d03019411000d002080181d0441502042400c2800d040b1116102c3d2641600131850f085100140c40b000403506855003000880207003014041201c0c2400300300080c50440f1201582510000303070740c0d0721000d56000b00f00c4c003139000213922404400c0d2440c11318117030a02144455108498820304030307c2c01590f0100090320005444d0080c5410340388500c5039070440d9103110060602811001858030103000840c10588100805c0028002d6104148503450392110034038102525800107d015000e00c120000c0c01620004c2610007815565964a2102401c3d4032041c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 251029280 1250 251028030 251028047
    0xc0714010327020108102d080a06020a0315080312100f180c0807120207050321190e03090906031204060c050c1005180102150c280807 59
    0x50303061607142d0105000c0240c42034403030080040084084074044000c3d200041ca1041c00a10301c070740c0b2030342c0e008062000d07100c40c43c0307403483c081001c4840c4850fa031042014202c204100e81e025020074803c0700740385020070030300d80c0151604104985050148071030b038050918041a140c090f40c0324682c402d000350030603e03643c10401d0f90001d51a8040104540d107a0021080b20045038206001c1e903000701d284941e07410302c5071240201c1103000c0e2800d02000e04000d84c00a10f00b54000e069552605c1e004103151081c0402031089840c521483c0c41d44038040303001300345c8810640300c0c1101c500007401d240c001845003010303060080301040004140614541450403040001100d0054001d81d0107120724802400c2c0b8880b014001c10160026448404c010f9209140076482c040c2d4050781d441c09102c1c130744492061a41c10800307540d6400c0440e1645e099800070407004030324140400440406401e0030a05211044640c84000c0c5400e02c0310503142c201c0c0004411924206c00a1001c08800052132800000ca941d8402e4202 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 251030530 1250 251029280 251029319
    0x16030f090302040c0221030103120c0302031908090c0d0c17120a03022206140a11060103061a0f090a050414060c040608010e07021b0105040801060e0f010b0c07 70
    0x903000d151607402050031540400760325405a484807900880b6048040130210b640004019418030355811030799801507080403e02c0c00d90601607901e0b0000101070090082c0d90700c03901d01800b00070710300d1000c400007801c108007520104468040c8052004c003d04081462440d05500031100c1c6100302d25017401c03810a100c0d244981505802008034030054445194018810501955005603c030f401046042480b94420110700e040358031001d8041000e0354100000ea200e5a00c82454144c403503c04240a4402021a0032000c90a000314000403007000700b994070000400c0c006040360840d003e621818040e411816100050b03002c3e0301000003c480d414035400003580280301e42e00d1500b103005130605007441d042c010388602440100124060000542c444811401000c118180300d030720307090840c00651a46c80d03204110131900c40340034550600c2d90082d003c5030000d00c2803d0081242c80e036680941c01150400380c40c14040840e49000000d5020700b44c0040c0c503550b880c00f1010309902440c01c1c0c20400085050101d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 251031780 1250 251030530 251030537
    0x100b0306031608010603300806040f05180d1803290c0304060507080c0d05060f0607030201050405010b0603250905060f0c0706050f09040b1302190e01020316030f 71
    0x101d20058600200c151008010f42c03000071818a003186401d082c96406141c0c8402110300f1745102c9284200b4410000003980070030308010a040e1280408078000d0302c220392007480380d14100380520440002800000703084d0a044010380d03008840002046030407504054090808945440080c0b010a10181441000c117002007000e18003600c3c02000c0f5022504201c90450088501100304001c0c0f0030300d070041c95446002468950b4103131030705c0341541005000d0403164002007907480c00040d0703843e110b10400301075804c00182201e807074440a1600030f0203070408440846281d420541800341318240380c000d4034019907c0d20380a144001608021612a0341c00591240030000c4480700080d20341c48003070040c9604211041c41c1c07540c6a1802c0400c601d020129481641003110401c99640b0040d0311405680340380d1070031a0041004d0510700300040e0b0030084900202021880000d01481c1c11101141c0803420300c0e1a6203d5641c590010401682c41c0d000c0e00c1c030044c0902035000719481c0002e10450040541458504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 251033030 1250 251031780 251031793
    0x302010e0604210c0605070b0a0e010e06150a12030c080309010b0409030507031704030509060c0325030f0203040b030a0b1c050d0914030a02061b030d1e05100b030603 73
    0x543c21010340b80a61807000d072042900c01010288008569000060012420102d1602c441947d44511101008000d00c0c1e51555815041559803401e4000c04180c072540c03812282c441c04e04440d0185500c252003a0103110740c2c44940c0000307400210012000445400d900d03025028003050b104c621860381b0042c42e03001c0c15581c0365000d4026503228450310407601d0080d580c9544a0381c0502d00a402c032101c001030307411520301e60410030001984c40710880340040780540300340c1c1d08c4291240d0030034914090f1001c107030200040140d00040b1118036001004000303000303540d1a84c00740000c4000381d8036131040780104581d00b1301c1000000d0001002e504620301041000e80001e010403815006010f101d80301404c11140758101d0038000d4001c0e5409a445000340900014071118a0140000240d594041041c004d00404000c030384e42d4010b24079001c1c003504d00c80285050303a45e19441415220024094400b251030a0300d810068044110402e02c02c2510444c0800444046507051120394009a040200f085e0713494861074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 251034280 1250 251033030 251033039
    0x90703050109050c010801061b060209010306030501021209120c0d081312120b06130e06010203040b0d060306060e070c170f0408150c091c06060308120603060906100302010e0604 78
    0x911420030b06030700401c081d002c40c01500000400010040e0f20140802c0b4168144100c000612456221030540c420401039540056600503405004158005050b651002c86c682041c081c1201c1c03450710a00308042038134820041d46610300740d240124030b4000c03407e40c844004e0013500d078002d503a0260484074590400c580f4500c5070f62102c020310130b0711480c54002050441020880031540c02440c4007148111102400c0034440f00401030004003500c03407811b130103c10a0205409034028800c039400303040c040c400c681d641c004c0c1c3e07040080501400c1c4000c0301c0c00c0c3d10381100000c1c2c192401c03034118000d2840e56a24619a0400c1c0c40300b914034407802c0c0035211094001c00080c58070134860b00040006040780e0010f041e856074100c9103220880302c0208850549401007154400a1340c4210343c4500c041c490303031080c840340a91810502c0090496820052001d040001d55146110414600c18814101101114455690000099260441a512800800002c080034001980500c180d5a0b403101e0140c9a603052071b50785c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 251035530 1250 251034280 251034283
    0xd020d1407060903031505010224191508070509010605070b10080f0f0f06060d0b0a0b0d201909020f0f0301090b0112020408031b0c030d02030a091d070809070305 71
    0x10f61404802184e07444003400c40c1c40c00140c4180c001403600740041d00b0301d0002c02c5140300c02101c20000c042c07407200024001400740501c10f10036841d8091440810411205241c0c00510015a24000c3d4000c0748200480001c0624054910506841047da1000d04000c650f655110301407101078040e140c5085c82010100ea800c20420032100c00082e1140141254101404814201042041d811010307812220030003400d43c42e001d4040840d5580b1202c0f05000d0f50710780121000508101c1145548142c180b508007041c491142d04415030790405c0215040f800d0200410030050090000302d000c50342100d04d50800110050f0340c09070249101140450780351540001c0000c805610176005004281c1c4d40b503683c20394079688012025050314480f0411442c0a04101d00241d483c09050400140940c80240fa900086014014140c1851029088849280410102a45a8001002441c00280c40500c00990400c41044008444100c040c00100703903200c00f01d003100c6810300201004018400e010000001810 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 251036780 1250 251035530 251035541
    0x7060f0906051906150e0109080304030b010e0702031e031b04170c0306041a040f02100807030b060703090e0403090e0405030d05070903050c01120609020408030315030d020d140706 79
    0x840c1d41e00080b249022181c0314803000030b4142c803214a514001081c0100f5107090641c0c0744c140301a00307241001000c603a004076a40c41a64000366400e01000c82c0000800c843d44001505856840e0310703100e0580d81e6400100d9a0740516150240010044c0035001e0004403003000558001c2082032244011020404d00c2d040143c1c090350100094080c010765242010105011035001540102c000c1d082c1410243c40c0c4200b0440d80c81503140c0744c4450b50f00030400300300d00c4100c911842540a0b00141e088099044090104001103038040040303800c00030071a03500d00d00f100032103045e260b05031140048103041481d00d64007607200400460510000341f0010501c2d28030560501d20072441003004640d6a50180d5101d01a41d02c064000010300140502c2400091000301d02c7d02d011541c20700e020308250105051900c040d24103a440268150f10008010424000110065224401e420400440d420350320b01130668a800360004000140c005100c0c4030308462040e5400c0040b80300003243d1a09203980c40d120601202c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 251038030 1250 251036780 251036783
    0x120408090604030804091103240103021e0703091401090603111e071104060302061b0c091819050c1c0c0b04030209090c030619021204050c03060a0e0c010507060f09 72
    0x1001040421040d00309000b81504041000207c506505101c2e5030034807202c04121603d0312044070441c00c076840b64400e40c1901d15a050b21040c6403a88000100f14030025070090f0410360007c0d40700c140c00304031610a60707031900012406a40345403216103400b004600a08881382c00114100b001c01402252070b101000e0f1808580360f81caa000d559240d94170304200301c407180c4170043c2d0066090075020030250b0344e810240c0740c064043e43c40401890101824043c201201a1141d9038060489400c1c450139800080d10342514200b400d085980c14120001d0401c1c130b29013500320041c29507016030340b0038145003070184855059008410071107004c2e8003e1358900c07609a9094000706002080814200107524003810210b800c10020300162600d08072110101c0d8459200a100101c88255039007102c4040149034100d4131860082e6182200b035080a00d000c5442c1c42151003040e11a208020105d200258071703104080356602e05000404010180c0c0005503250b0304041c03026070f002995a40da0402c694468091540f086 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 251039280 1250 251038030 251038043
    0x200f0d05010608061003080706180b0901060612090206041202060c010f140c3108070b0406020f1501050d020111030a020604050709020f0306280303020a02040c0c0812040809060403 79
    0x543c18603040626008000300107005980e80000e042000c10113880031540903d41000c4007064505040d1906400340d5a074144c01800d8554240070001f1000701940810240c40181c0c4e600542b00088035001d400780c88207004080d5001c00c00f00310420100714614003e00c0084d1001d4140c81c1055180b0b00c038117084401c0151510b0b40030f5100e1300d0001c483c449a1400c00d600240b0b14017443e00348070942c02210310100e8406102d46481c590000405651040515140d0092010104031010b40e0b07125481c1c0007589d000b9200e2030340944a00070749088a010701162240305e4846200580c1070607841c11003082141003921800ba810702c031810f481e101040405000a0140415a40040caa2800d15103052850482140d02000300180706224036190321100400f100d801c17100440700b081101103141c000d804902c0c0c560b00269080801da902c00001c06401140f40c01c0190700880c3d007000007011228081e5051001c04d040144082000c02c000c10902d0012807074140c01c07600615103903040c4150f01010072900c3c3e100d508181da16 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 251040530 1250 251039280 251039291
    0x120615030703051b0307021e0309040603060204030203070501081312050f07060b091006090e1b04080a0b010e01050d02010f0315080a06050108011103221203020c010b030604200f0d0501 81
    0x440443c03182e03560351004c0c20703054a1840c42c0604c030094179449441000002e210340004441c10a98040080c2d0b2032003c030040040011070340e41d1402100940c01480128000d004000d40080c2d9580210495841010540380c52040810a69110759840290007044800e00c20b00b442082d0b16154894060440c80d48249800140c50903944c00300702da900d1004050702007000821006000c00750740048c920044400c4000401c4564a40e10000302c03a8250340800800106c4012400082403100040c2d5246030350f011b12050309050741c840a10043c81642406001c0d004480b41011074015407003050324004c2850b0300d10300068004640000000000400d03481075605501243c007100c02d000c1c144c4650b81c01407029030000c214000964101081a00008001c01201e0040000c958000c080380c0c0e00c8040c8569010175008856040f251000d00203400c1240c1c0701500358a8101103941c54100000d902c1d0003107410ae000b0906400207220b4803290188045001904030301201400b50300d940300d0101562505100c1d10010a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 251041780 1250 251040530 251040541
    0xa0302062d0318280f1712160516150608101113140a09021204061107020a140409060906090203061015051b061501030b1512061503070305 61
    0x259800200d0f031242190700211100c9000d0440d103a03c60804110000c0d01d00041401810041c020307240c2c01d1005002e8011440c05064071a00d4000204a6a883c6a0602a01c0c0d140c010300900e24400030140301340460340820118001e01541c580503e20300340309880c0e03140c0305800c8410179010388210740d000124070b038810342ea50000807405010f01e0f0f0021b0107601040341400c4003120100b04203204c902c191381ca545020315900425803030383d003c100040d12103071a096603603e441c0c18000400900c200e40540d061440c10380c005520310010822030350200e0300141807000041c100300005042c0a400400e50380d00a540b50340324000101c59004103c01c807802a01d0014009489005050404400030410f02c42c24190103c1803055450081c80c03068007140510740380e612400030200d044485a28480c021080d03115060400107400c028005000a0460030b9a00380940e0482030f09010340d00720403805680e01e580d0144689090ba4611100090f40800000c1103812085e008140c4107900c1e03801616107400103a200e50030440c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 251043030 1250 251041780 251041801
    0xf14160b090c04090c032909070807060903031e050c16050f0406080d05070201170f0901110c03040303030e0703121e02030a051c090206040902130b07020a0302062d03 73
    0x2c45010b0358103003c032901d83e903101d903100f10041c000248102c500f841d0f84040c1c10403030122246401502036584150341000f012956507074200d48140c3c2840d119107000030421718071071804501129856212684100142c2c103d000c110720702c1001010420105028000c00b03040200604011002c203440d048100600745800d02600345013080c006400b5034207003141080030400020745e8400014052074280d8840c1e48910040352108404050300c005a07001138188003888100c400ac441c00b54540c24003c0081034522004070380c0c06d005032141800c0540060004001280c025000032010700042c6042c2c43c102d03074a96842d44c6c0d0148015210700c00190140c0301c24040c210084600c280341c0026030004500348096928020040e00c1191a101c2c10b0750240010960800015002040116070040106469613150381c4103c00a400c03170b143d46803600403405000201c0740c869000701d0350858cc000c0d200c412518150703001d1042943c4540d5040c80e407440000b02c0c10344000c54145104200d01011150300d690303400d1031103058 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 251044280 1250 251043030 251043043
    0xd060905120f0405040e0d0f08041e060f0516081f0308030106050301030201180308070807050f1f0b0109053708010f1127060f0c0a050f0703030f14160b09 68
    0x141b2087d4040c450000301607411400c0e5400740300451401221300c0c0c0c0c5510b00100e2500d25450340c01019034220071144200174032600a80c01018100108000c00d646914442000c03a41c0c194003000441c100d000800c4001d6410404070f481c9020126242d81b00c596a070341c6042c0c07240e009900a40010f00c0120042c000c541c0c0c07113040e6200007400d030b00c1440005030864645d0509441a29002040c0c00000100041001028004c181d000d02d0010f0603a81081c01c00340003640c02054004080045500d0140515580e6006001500503590701400140c60f0310b80030600740f0442c584403004003d0400c42da00c10104081a441c0d40580078143c10300c000701e02c3e8551494004140c9500500513107070ba100500c114800c0d11a1400c003050860703101c500d06c20380303940c0c15004907500f40710f107621a643c1032000096030907048400003044180f80344281d040f40c0c91140a90f078910340385d6030769020080c0050002c020300e001092151200e0006813070f4040e142441c0500401c080840a003036080e04071110781c4840100a407502c4180042c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 251045530 1250 251044280 251044301
    0xf0821130c150816030f050a0b0103060812030f0a090228151b080f07060213090e100b041b020a06060803040b04030303150902070503070507080102090d060905120f040504 75
    0xa0102c1210041030260405200a080002c4208079040c0c82510310b11a4100781c160700d04c2014200513a0620469083c050310b490010280804e040001c00101000b0010340c1000c0010b03060381050641c1c481a944403000c403809818032949030385442c000409a5202029040c00802100f4482c0455260034880c02a12599900400000310100d0150000365001000ca0714130007140b4200040802d21450b000e08580140103020f6071144020464504106a5a0080c80441420102d4901c05507440500b501514400900301c0030f42e0700b0980800881d98038a801a69801000401c0812044494040520a8982525601c005038060704801c421b00c07401d88100c1000d4200400514a09401d004410459218072310004007016902d400301000e540001c203000018020642096545000600342a0741e02c0d04419010303a141c1c002c0075070018164005208544608401411040c03500b452a1900801002d4a403010703a0305018284059940001c02c00003801074080740c051040c0c030b880c20f210502082792400c070310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 251046780 1250 251045530 251045549
    0x60f0c030d150f0b0304051c03061701020309030a1b1a040b070f1e021011071406040f0809060712180b091503060a0906091e02070f0821130c 62
    0x1d0220100c0780c8003c0082d01c2d0b80351031003581c03600d42c0d1400034501420b241d205000c00c070814034501d101c164160041411101c20075034128a000562070403c0c02c0788800d0300c01c004036501c20030241d200303580141e941000c1299a00c2c982c5455602c41d440341402c0c8600c180346407e140700c1c03031801c0104004014602c1d980001151509846400c3e0824000c0c01a0070342d111050610030f070380009280d07024030800c0395541c1b0301c40c0c108050281c0401d00c5032109064000d0340f401c9402c0d504112160000d0b99000440030320a58100305460741030846500e414034680e1200f4111034000d0003c100850104414208490094809540f03543d1140f402c1054858515a190440800c60108001c0210b540d0707100c0d0101100343c04c0102c41c03d643d0391a41000902c1004075580003070300d40c5050260000345420741d644601c680c460f1046111001c2185200c008040b803040040c02081c99100c8148035020a01d194060300604081003100c500c2d200e80d050007000c4540044030142040382c1e4000b9000e040019206003c0300800c0c0104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 251048030 1250 251046780 251046821
    0x102070f0204020309030912030a170c030103060b0d05150405010506010c0302100510030c030308040308060103020322020102030f040e061c020a0918060204060f2318060f0c030d 78
    0x261103442918080c00003a2003641c02001051a141381401283c0a4180c0100310350140044d10041c0c503101d4124144080110300c0220345a00d0080c02c0503120340c8640d201c3d40010740b85030700f140e40340e2000302418200707150051000c0540b40005041046003013494038500c0783c014030610382840c065007940d800500e11030410440d12000c80000b074002400b0b80c451101048082400c2c0d9907441c03005444c01d415800988003c0c80080000103040d08014510b000e14029692456640e48071030055041c1e220580750803442502d40f50725011084806900303548403500c144140c0e486c0000554102c40c0b03641064000b030f14039201a506015207840d1400c0c40c20501c500302c070300048071411150001038214809209415507680c4580c008900d80c0440d0364400c0155a0000045440300c0e100c4a00405502d07480000c1c2000c41e0b41000c805001400068016054451359840325141c0000046229480030010803400e4000006201898082c000040509030060b5035134002d40e120407141c544d0384156117888510210007400c88 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 251049280 1250 251048030 251048033
    0x120f050901020d240605070f02030a030512090c0114030414010f0204080c030d0e09040c030203011a041a24040504060e07230d020c0c0307090c090b0414040b011205090a03030608010207 81
    0x4c0c041d65048902900340262941c1c0c050411007007124020b20002d505002315141d43c820183c000e0b000c0c0942c541d4000001c0415621040465565160403031041e0100c1e08065403410f1042403031000315481031164104904514003041910309689401301487c418640118041c843c0c40c0d002c11050044840c100c004002c0100803510207001c00401014550003032066038009414440f041940400a580c040e000f003005681613502c8442003101c12100c54030442c10105d141102a850814060154100501e0900303c404c0407188c468200810700c840043c010400d1000007000c1d55144a00c0008122420144030f0b035151010000303110741102101900205d0103803103a4030310182c0640c240c806805079007800507075505450b10344900d410090ba03c030650500c1100c50115445406802c900c3c1c51241540700c25030003607141c2c2c40303412681c01540542c02c02d1a2042030880c10a00c0c3c0751300328001c07011040c103101e200c1c803070440c08901c2901d800311900b0149502c00d400c002c0400d45d2510030080104002002141001c401c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 251050530 1250 251049280 251049341
    0x150c0301060e0d0f030504031208240d0f081b12040504090828020106142b0f060209010e0a08060a0b0105090a030b0105090a0e0607120f050901020d 65
    0x602a0384100a58940c2a002d25150040e08031a42d039005401004400260710b80200720354003c0c00200d81e0704800d1b025180c207150103800342030301403609051511ba9182c91082c2c0800320100f4040c44545c81100a1001c0010a50040115178064080c05825686607413000e08080d0180700030707260840035030003001d120100e0079002e01510b0075240102c03408502c0b41e01380d00b030104481c002c903005030f00f500d102e8000c902801040c20416590034440c0e0740090002a40c0c400b03030b0702c149041010459405c00d0706c4c00d80c1c03420ba070741000c402010102641601c541c0300d420701e916440c42041401004641056000456070921368000480090403d401c4620302c04003070420300040d88400300a040020901d440385200700b0b06038050401d482503910094110224250390382031120a150f42803280e6030065075400080b44903035940d405420203a545110080010391a0000f048070400403000540458036601d9209407000100c500915024164913000545c542c00c40425150484101407214184030120017481d1301800b10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 251051780 1250 251050530 251050537
    0x70801030506012304020d0902010e01032c01110a02371e0516050a0b030c0a05030c070c030f0308160207140114040b071b0302010210050604092102150c 67
    0x40800d40301501c0d07a05a0100c08114001507401307030340030740040740c82024000702c0d50041101034000d0340d48640740c03124400150b040307514084445d45003d40c0e40108251030310340c404000320700517070302c1d4000580c2201c800e182d0519504000301c4400180c005403e100825107018a101d451036045403043d110300031702c0d61800b02002c115140024811412a15054040c0e903400340b444503420340013019076507541195005200b14082500800c0d100b51a84c070004540d140c86001500c2c411410f90380c070945001039002d030954030340d00002c203801b108203c2001f41400082c954040030300118811411311212540d2807502071301e03040340189659081c20444401d02e81469001903070408882460016103000019180121408640840900440c1e400010005a403040380ca0017408100d0040b6200d0804080c0302d400d008000029220190050388403400320040f90400303505c02908004001c1c40042d4100342941c1c6e500c10280019640050094048044500180c0601c074031140018010645500e42c9002c40c1c4400c000d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 251053030 1250 251051780 251051789
    0x9061401030c0c0c0801151202030d080907030c030b0a06090507082202150a1116051314040c14040c080f060411030f04020109090b0f150405060c1507080103050601 72
    0x1600c0302c68500d112406040c518406a81115036501c3c0c00b611900a140a006001c2c00a120030341480c00c0056000301410840b40406c2d4010068101c9640c0d24008488184c005092040c0b1806003070000400540440c0b00d1100442c40784005015a08d17010700e400d000c4440540c04816003a042408102c15558040d101a0b4080007000c0d01100c0e4600100c034a24051011075002074000c00c41426082418202c0000707020045507da50b00500e00806c4074500b511125004141415641d01d18002e01070f5188c44d07040c0c1480c0a950220014042070700510552400c0c10542d0255440c2d6100281804615490502e0b072194100968040c481d03510707101001440c902000340b0041c2e03c420410086046070741d4030b80041e05024a8a1003483d224100540d010744600320070b03274040b40071900d000d10019003c083d601544450383c0c0d004005121142441e01802045d010091540c0c1c1001010032010a0550b07a14024104921003c4000e0140c82d007494841c00034108044c0001050002140040000a0300000c00c1030644 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 251054280 1250 251053030 251053037
    0xe03060c28110114151c0b0c27101b0602030402120109140c03010501180b1f03090606080f030a050c03040e0c3615040302030a0303140109061401 64
    0x900700c0d4030807203403800d010b2410281d039401d0a51840c0b071420b0500499000340782d0f1200301041002d25070108060403103001c501c10403011000c00c4400100f2440c0c0d000d2903010300f00d90340a5190203a80c0740b0000b140300c0e0410103003248902e11490a80c41e42031502510304400d01c2ea051a1550b00341c00e298048040940410091020307800100290464460080f601c101459000003400726406074035082c07020007034468155856120302c14581c03a00386414040c00b8106c404103440001020758070414070000d084c0c5255110741062204c2c0d0075a00c25405110b800f2044a01a5400907180e000f52800f401990899400030420b540442c0506000c0200071003191007800c1c103401c04d265920302d02d01d022800c50040350700104500300a1010030000f064008000d2507102c0010341003d050500d1030303070b00d03008100c021056a00c0b90340c0c00c2c599100075401c11f20301103045c4000f80031b0110b0501d91759a0001c0d1034004103101c100d00083e00c50700c24005140305200343c1405001c641ca018042d0034140745500f485465606c1019040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 251055530 1250 251054280 251054347
    0x310020703050f0415021011040303080601020307050a0507090e0106030c060f14070501060314032703010e0303130606240e040615030506100905030a0605100b0a0e03060c 75
    0x801d030150007224000c0360500074181d2030303960f501c03040044010f00a1104025000c0e40e041d845804c2e0051183d01d034000d1508e0000d13403c007825510100c4070004028081d40c15880308000b42c0010070000c00041f5a5203100f0002046c2c4582403180720340c1600c0e01000e5450a90b81032200910015140022400568600b481c1c04412032410310000c0300c0d00e038011940c6008020340011198288001034103c07100f03603030040004c401c5003000d101c4026664030940501b207208200030a03e41e0720001c00640c0c00528680014004078041404d48410350942d0b0058071402c10580e4040310321402c0000c680200802408895074182d1050040180c042c05100751811850070007130b803641400d49566441c0e103e40f0113410000482010b207103201801500900d000e8070814404c1072913079189007880e44984124015980c003d0050b00ea03107042eaa1707070b02011700f00190032a2029800c41d0400300c0c1c0c440c0604060040130315140d403112040f0070f58100b03040c00c0c44805012100101c0d020040c016000120503062413109003a00d04810f007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 251056780 1250 251055530 251055533
    0x9050a05071a190207031203020909010608040f0b040201021e01050f090303010e070e0d0c03030e0906043b0d0503100605030601080c1e04270e0604020607050f070f03061a03100207 79
    0x42640a4000070600386481e41a911f1290741076000d400c8032201660f8241c0700d80d88070081558000d004940041034441c0e000b501c800016024580c007070304244180110b5100d6504040c1c1e2500300720340050560842d80d9100d08000c40083c6545a150b0810f01c07420180d03203154100708600c411044010450400d104140181c001c10f41c583d42c09040c132107600290b002030290346074540100b03082100010310740324510a002180c25450503200d2280d600040610baa40d0568007800341c03890080420584c044106111480c030006040c080c05424100d021540e0f84541c1e910b007035003994000d24060741111040001c144200304079642c106003c2500005140c0d8885c3c0c9515106030a222208410851440e40d1840890001000007172800200d003154021600f00b0a00d0f00c0880c0c1e0310341191421940031038240e0054020a016080c194001c046032402102035900c1002410308292400e0340d107900c42500f11040e03100c10418072000c3c1c07043d0855a4148802481d205900342c00003540c1e55200140c3d604880e074006034450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 251058030 1250 251056780 251056783
    0x19091203020c1909060321091401030c0302160620120423070803030a0f1407030b06040807030807020f0f0f130213030c0303020607050a0914120109050a05071a1902 72
    0x80003003508140074400070782c40f0b00e8400e40c081c50305030198041204941f4960a17180c0141d00020030344804450781c1d48550030b160011409071550351303088014142c0c00c10001043c0c4950342000c16460380103030808103040c860000d46454080c42d0300305003e00c214061084d190440140d00440360456000091400c81080c0300c503003020304403460b1080c05858402c140b00000d01d0301c3e010000d14810303011030800700f0400625007410000d9440c01c50341110800172200004603180c0c06a0700800101d07202a007880d08290316004014a405020b40003501c8407440440c50800310b10b410203441400340c0065134034114640358100450004903030034200901c5030260091400c4121520340c1916250329401000080c0c1c0c50f501d0524081500391b1380000d81c0180256400140e20b10b008904442d460140765407410585803425081c1511034080038049a0700494490040803111005d000b0200d240340a030014089500c0d035868020f00d400000c1c2c2c070128070034021036401441e514202c0d058800140142100a160a175010400ca = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 251059280 1250 251058030 251058079
    0x206060a14091b070b010e01060c0c180204030813030605060d030f080402060d0908070b010e1b07020406091d0c0103110711030c09100305060106030227040f0219091203020c 76
    0xf020300381d2010550700b0a104001e40e5140c106c0728598441b501c944d072202c208031090081e01d58041e1410011540810002d6134055a120104040603401800e1a071640c0d101c02007940a044401e1740032100340d10900600602e44105500940202c1d034900d1380111aa50141070404241c007203000b444600c0f00000d0a548031081168100040f80b03004000c012030a240c594080d070062a01a541a00c20400214001c45002242402007444641489847c000043d4840380d590002504a07001519030600156013022400380190b004e0710307807025484003102212414940500d080b07045d410141040303400301580c10303d00220350440b0341045250032984450070119181c8543e00d06850307082003550b410000f04c82d281b04030200a60384500c00b90b55042c0d80e01ca00031400d03801596003141c0700350b414045040019007034001c014400c0030003138008901c24032001800012600001d444c401034001d020202c2e4040d035030000000c40903010960040c0111421a1402583c6903a95089140240c0384400013105040070390055 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 251060530 1250 251059280 251059321
    0x304150828020a0e09040b0408070f12030209030d090b0a0311090d03030507111506010c11030a03031b140f09060c0f0109060e0d0f0f050d0e0705010206060a1409 71
    0x40c4440100c030800c010020b52050803040d0014044144c601e03264a440104035000d290030001e05803864035503481d241c1e03140c3d005075000c940b400034102807080041c56070100044012b4558400585607801c2c4020f05007400788182040081086c5940240030b038200c02c0c8140c81c0c1000040ca400a0000505803d181c0140318086000c1d902070360b2064440101541038000c40c0c400c404907075490814501e00000c060340c41c000d0030249a00000d40d040059502d510400d100072446016110250201d24030f9000319081020100c130960029850359543c14080c0302c1c1d83d442c021440d0742c0c0d140450500c0c0c5029440070b62400f4441c8418424840000e0f080308660360f030340684825052600c2990746000d402d5100c68004c0910000407214103041c4440c2e035000390804200c1d42d004032500c0e141d05040c40c220300c1741252460705840400e424044188920381d200c105a1252940c1c1c3d481e54401400d40d6801c100005e40340c510028a410300c910415070042c01025101550f43c900140c0941c0d444007ea150351414915410a4155 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 251061780 1250 251060530 251060581
    0x305100515040302040b030d050a0f0504050418051e1002070302010e0709020d051e0a0504020418030804060e0102040b070303051302040509011b030e150903130b031803041508 77
    0x49071164071a4010080007140e1003110b0401041542800707050f100e4100d070032848080381c2e050280740151401014885860740c1c003840d10500c3d09854000240c100c4030012819190901083d501d101040310420041c85400c0017041c007403442d00200300c4459903441e8484031400c801c13a00440c1000805000350007031071aa0307400c070054902d11074a50043c1c1000750450803c0d003d6050609021a4481e081803850310810900c0c001d90b00d5080d6103002c642d402030140604100c2e000383e80c4850041d922100001000c880601c40e564203801d50800c0d0505006648145895021603441000204007414190088903860b07035040c00c1c04626540c0d40303c01c1c680d600d015244042e400c142018200b14401006500c01c5c4d0220311227034004c5e102d1141c541d004a00300d80038600b140020758001c4685607040d090113221190301c80391501c1160728051582c2c4291522807220b511101e81c0b600003009103e0000c8500d21000010300b401c070015401d0a10b031102e4054000c05507640d03182400385100c041604e009000e28511400480c400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 251063030 1250 251061780 251061799
    0x1050f06130e01080d17010b16050f0f030a08090610060f12020f04091b2c04150f0b03091209031c020c040605010516120c050f010605010f021c03051005 67
    0x84207417140040285400000c40820380c5080e16103035408120305a81c0584841400c0ca085a541d0112850b2050000c0e241c80c4241100307254000d4040022140c9180400301858460b4071451001d4840a03029107580300cad43d0405c208000c61f10900440710303002c2301c6e0189007840b0802c159a5060b50805403070b8400d0b100c0c860001640d1980480e450000704225410010108049050f0b0482c11407a1444010220009461020507060315803c06007910006052464041030100c00c4c00300007001c03180440d10f95403042c0c01c0180c08014200242081c41c1c014444030b40407a00d14074203070513201d840701c0368417100515110000c01d40d030010b030301c2c00c00144000d1030104d427102d00106503152019650317800400324107114904000c0c0c0819554404d00913290844040100c80f0111a4582da615180d089108602c40802c5800c041e8500400c4007085800001220400001603203070a090004003c0ca61065400042d54882e404404008a4484105090040c0c82c80c1c0043c00c0d4594006003510101c00d60301040e444032690 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 251064280 1250 251063030 251063039
    0x3060c09050a090b0a06030b040e0610030c050a030f1b0312090f14150702150d15090920011e030e0706020a0305070b150a03111801050f06130e01 64
    0x508544180c62044941c070b6201582c03080c50388240e807a10000103030410344d0b80c4402c110301c5009400030b80710990001c10100f615140301155901c1c15108603001c04880f00c20040030402e01c0300f07481e40c0002a1409440d129401825a100c50000c0541c080c4020801642840f000354400b0740c4851b0300001c4e550004012002d58200d60b0003c0006050b401100400c0c9180c1e900040ca041042804c4490b117140a459881d1100b2a45e2420450b038000700c0d0180e8201c0c0c440288810320404c110000d140c40314032907900103680c03441d09408200d19400d94014a0403646004605004269022425000c2c803181560ba00084070140340100e07240030703608a10f0b12640c078103a03098600154250308030440382e04095003120304403a5140d2040707030755110f20327440500400c008002e8000400c83d035403d0307268043e0164650343c98050180020810079080d6034402d940391203030300e501c0b00360920b084807084440008126400c400e0f941414001000e40f011744034102c1c403030a0001540d13500d035030004401800030040510f03d8071a80d81c1da03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 251065530 1250 251064280 251064287
    0xc010504031205070e0409110619080702160b03180d09031a01030c17010b060d06060e0a030b060f04090609060b01080a02070b010b1605010516110109020d06090c03060c 74
    0x54404902041c203801000070b03110040c0c894240300ba030342035446002d00302a10040c000100301c00b03101520140301c091281c0c1203d4403050000d06d0304040ea0254036881c1405080700134034004000e03214008542044101606c0540514288015168000c043d10350b680c0310003003002075808070804101e445001d1010319580c1150003070400720440c0d000b10207404040c0c00060b011086524240401030440b04418001e10450303d5010000c804841d4100002540440e1030000407030740e030007001c0c0a513465602c500c000d1082540c04641100010700c00d8803000d00b4030741191303502480e804002303143c203000712403c0c1c00c9007405941c0d40d08060b20305500311208212050080c14050054415001000c0c0402c400c0b001254040c01030788207c81c1c900d900041208010307400c2c0f400710480c5d54000d100c2141089604440807010580a12526005021041c001c066481d884a0064041540c43e01400c580780d141181d0b140140e1240354091503081d0703000320005082c980b40e1800402140c001d4001424040c500310045241680 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 251066780 1250 251065530 251065541
    0x30203090706020f06070c0f050a0b04060b010206060d03080a1409060406110f04050103110f0a2c01080109050c45030a11040e160302041109030d1407080c01 69
    0x440e10a680a10b5110641a66203071414642c00203d0780c0040d0000d014144aa07100005061103110b44494201c00b82c0c171107a2030300d0704510058400840c08000d010030069a031242d54209502800a0036613490081c0000b0007031f144000c4060306000c44035001441c4801568000012681043e42c864020308100c0003256070761008540458102e031616110030032901038003050f18074058002e40ca15180500b0100110050804003051122101e814001000d40b9400e0b0030280404421698a6541e4100c0011039901588809a83e26101720403800400950b0b0f64403420f1141515031100e400314081d1642c00c84402280301c6d00802e0745211401240400b040b410f180d14000c070f07103003280d4100001e08042c584011a203404107101603501d5408510442c00061002010107010030008000240f03c0100c2d40d229820144200302c94100350180c50014411407400b0320400d200039102826142c1410004000300c2d541d80d0035480b0070014404a074202d410100f80104c200c803001e40e0f00c458841d44610826914034003820 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 251068030 1250 251066780 251066791
    0x1c0f0c11101e02210405130f02040509041406010b0c0312191107030e09011508040f02100e03061807210215030105040f05041709040609052815051e040903030203 71
    0x4011a907400c081410000d69081d91300050410340d01382000c0407d40d000380984810243c00035000c0c040001c2c943c3d0b940c5d00300391046000e02160141c07501c5000721982041d1050b008461003460510100c4d2402d00700005031048040074100a40142d20b82003000380d018000d1500b0054001c0c200003002c1c61b00c0c21039001400500780310351290450388222108020507042c0034080d005000c03140000c01185a407090750f0f002d4009006080145103d00c458011940240c880c004403404210010707482c000740e0500b084120780c0007441e03001030718014007140111910340c1821300c24094100c80402d2000e100d800000000c46442d980107010905920305042110100d800910800303100c0d9203080c0500146458a000d42842254443c120144c140b09803596681da68000e61203d0f504030340d480a010654044500c0764a0042c2505c12800701e403000711555007100342d4200000030200604040881d54070070b44040aa00a683c41114060a0f88080340ea403200c08584580c1030340d900c030342880d0b4a081450b40580c021806107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 251069280 1250 251068030 251068063
    0xa080a1706060706020a1b0506010807090203151504080a1a0603010e070e270102090906010203070317180d0306030c05060f090409020a05031c0f0c11101e02 69
    0x11845403900c4800040100c4031550041003c008100c00500303142e000b08217a150074144900e540303540c0541c0490252954000301c1d01da500001c01484a200204091030042c01e0a00f415442c43c5002080141e40f801e14080c95800b6a0f035001c1028081010503055074064580e5001300c44440342141800140c007011610b20101041c1d003103003c1038070307800c4c1030207440c808081d0540200302d601d1601000071614a402441c0c803081311541c5041d0600d1060100c14481901910000540c445001008000d07103548060301d640e0543d4800c01c00800081e07005450040da121080300007100d1a65415010408418041c0600d51603016258600308101d03010760280701036900442c50b04843d03645410502c842440313052840c0c5500d034400d02c01c0100501e45502f0861a582c40600340704109550760003c24074148074400d450b011540100003004210398070651400c074000d62131501c0a4610581d4841c240c0501ca501043c0d4011046800c03001c01080c00340c0295a4101e042c1500100c92101104c1d00a441c0e101c69030201400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 251070530 1250 251069280 251069297
    0x215090f0a0e151302070b01090b0a30080a17070503011a0f07060207080406030e01020702130e0a0c06050d05090105010e16020a0b0f0103020f15030c0a110a080a 71
    0x2410103000c49829100000a41080b588a000b03c0f2900700e4008a100c603408514200c100b020842103001030240c0b00d206046e80003155040040200688054102560144d52942410402101603420111880340c41290b01d0015940c1e080f82031200b43c081070005000681c0014880070050b42c8403030b401c01140c482c580660300c0717034940032030844281c0310038416000441d000c058a03003d00100c1c136004044800689101c10725102c0107070749080580e00614000d80d4074410115041084036058000c0c880c490680d0b00085141c400e5540c00105c0031041015902412903441e9020008c004081040c8203903260480030920781c103640d40310010041d91044d0041040581401d01240d030030340050149a041c1c94582c1c2d0030300907a50b00c21109048003c468030000045128000d07044000c20032078040103010b18102c1610784000e60543c010711518101000d007181c0038014100801c000783d10224187c0350802249908207507200c2c0c160320115940c2c4c01c100c07248981401401110010841d8040041c41101035070b4840680 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 251071780 1250 251070530 251070559
    0x3010905090f07090e0715020303010e310813030606060219051b03070b030702030403020a140114091302030a0516090311010525030210110a0c0f02010c021509 70
    0x45807098142c07515003941c0040c900b445030b00d106400140e07801111000312a40240d54140400d140320161942c030015800010042c40040e00c42c135090360f032161298000742072040f21444a291034890200c0c00c000060807401c40003080081c948101d40f58444100c0d02c5a1820b91207007400130040c0385074426240035118004020f0300114015401c88a0190000050441e107403041004003000c24190101c55414043e0700800306400042c2005180143c4031680119180e40c15441400000d026540002400400020b81c400e0b0070303030303021554110355100c05100d15210700d8010b0118010561400c02e880903540044104442d0450701d81c031080c481d0f00310301040c41ca0713201107400030356140000703002c01b40c800d81e0300c110001041d5020711b0040044ca281305588065519645400314201081e017003040740141c1003164600702114039402204402112418418680390b01c614000d058802001d10082003494030441e0401035a000300c0200703545d1034000e403c03010400c41e0400c00b030485178007040d0402d110b031100780841d21 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 251073030 1250 251071780 251071783
    0x110415030f0f020612150306060411030a11040f091a040903051207050403020a03080309061b0406030b15160606060f2f1f06090c09030b07140403080301090509 70
    0xa04480c1c001080c004030301500e445140030904035040036a00700c0810000d0720082ca440c500e600c0e218001d00420320181c56001c50402d400c101c009000c0d123209900f0b150841e15040307611000c50307800070311088000443c504580b20400703180c0960303401790f402c00c903a511000403512410b8015601d640441c8182d040f40113800003c010854400ca440900011414000d0412648410803001d0b0041d11074108142060b90740d0b8000b5086040542044a2619000c0b040c041d01990400800b80c01084c1a040c85050700005a0442840d0082c0d1040808060b11002e40d146a515104840c002d18a5031101c0c95130395210f10b020b2080f140c8000c02c000c8520a2a0901c0001c4c458480c402c84500c04881e6524400d10041003003c0c416280002a801441d4030741510303030030b6200d01b010005565200d04459840c500d050684001ca8100c840c107900417484641440340f40540541d0014080040d070b5408000355002d500c4448080341d58049070701404041038400640441030000d004080d40c100d480e880401d02c4242d80c2c501c5601e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 251074280 1250 251073030 251073071
    0x40c05090934030f09030e0108070906020606060703030603150b0102070602010e0606090408092101150302060a0f020f01050907090b0d0c03080c03250c12030c0b06040f02071104 78
    0x4001e0240c1c0c40c00000c550708102001000d40748114980422580d50448504d400c6880c0103070110045020315004540a58005030000d50042280c00c1909010b854090083d48512000303103028442c0c040010b61008050082d4041005590028a40400d0342902e80d0080c008240340d95185002d44903107040007540c04d105009080305404e205010301226110b1405000307064002502c100da01c11000e00a1002d141c8600041c0901a000780c194809008a8840110700f10b4054a03d510101c0ca0305640510240c0c45000403529028506e2070315000807402034104a04207600302100c4842035080009005003000001851004e076031203420308101e0500040104641c9011800d0014981a0480c20410120700f11501400c811243d040c20781c2d20b4604641c02090748550780015001746821845600b00501a040e40d019002e0010715140351101c0ba220344010300241c0352140024185201140002c0080e00c1d243c20514840c41c4040003551907800d03a00e40940e40e0890303c0c00041c05641342017401e20203828060050b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 251075530 1250 251074280 251074321
    0x602030f091c120f06050d050706030e03040608060d11090f01030b070905010c1115041d070905030a080306010207030f0503030411030705010905151b030705012009041a040c050909 79
    0xf5003092802a1002402422506810010352a551040040e05031145403540740085d10446c0604801e0b414104041c1c200c1c0c02c0d6540c54082d661040c44184061030b0089803541c0c01c6007084900a02c45110b51404003902d41c03500b00c29541083c2084117000c2030251109102d41644d108400000c0c1559541d0022140c2c4000c41c41154002940c604c5900301080d44203040701c100c0d003005000c0d0100a81c2145420b40300c0d500a0b8440340c1c0c02050005080c2c0e00e001031a0400e900a130079440c042e03050301c5c54180029540c0010640244c005d090000101d40d1907070003001410000d40e40408582c2401100d03082c001d072030b074000300c0e02a105c1072503900002e94989804a4254207841050710f41d442007034188010712401d8000d4000350134102c9030420401518070103407074408404120000040d41d0381c0d4000e1424509441c20b055100c1c0c00001400394408500000d4810741e0407001060b1000200b00b040300c001e26445403004403010703401c14a020200341090350701000501a8500680c1c000485031580b941076655100680700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 251076780 1250 251075530 251075537
    0x2d22090e01150510030905060c0d1401050904080c03090306070c0203061005061605010b030307120f0c03050403060c122f1606020f13060909050f090c09090a0602030f091c 75
    0xb01800070703190401c1600881c4c825032070005100b4540796611340c680340c0700340c80c81146417130041018020b0b034050f40502d4072602c0c2141e100303410301c6d4901008035140c000042c0009000c88070100d1224494041001902c00f075040040032500ba6042c492001f401001002506074041c0c0120400a41244c06400f0f11000725013025040d286054880305500100ba0544a401c84481d500d89030341d505240d4007080074006050280c42040c42c80003401802a000c51000702d00c0e00c05005004c0e1000021a400c4021394007266040440859040b0746858100d030452203075030407103107002e00d070001520060341c1544107a50301036035103882c2d14201500000341803400e018000b03d020003030b08481c0b4801d0025034590081e0480e00405940541011000345030085407e53300e8000000185940000300003180080c02816040700d8150800c0d181070074070481142e1644a8510406e000f54003c80c045001350034100503c2a449404c45421910b0781440306c4098010881595003076170610880d050380c6d450014a09c041c4c18205082c0c1c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 251078030 1250 251076780 251076821
    0xc1504200a03020f1c05030417070e0112032c030105070c021e010e03030301060c110d02010203161e05060105150a081b040906031b08032d22090e01 65
    0xd007001310280320008000d0b00441041002001001c000b07001d0f01116100f00081c40d00c41c0e080400c0150b2402c0c2c00ca215000d680d110344410050105803a04e020f054680c142c10041003200305040a0f507264065440190400c4002d018a0f590025610b0703031008106012402804141c59164013114407149144c8040e6200030700560b40d4041108016525034000c60604003424000c1c2e00c0d03400a401e5400176070105000c1640351070300c401080b500c003164a0403d0301c1190b542a58109a40000b5505d0141290862280d00d0208400c001d004400c201140d006030085081503049030507151007611280c083c40b40700e000d85407030308400c40750900000c04e880c0c5030440c0c0e545206850765004010609002109001e641d441020000820420788500401c00614003d01e03290f000065403c0c1c480005c04400d0303004100702d4200744403071121504006041c3c02c0c40c60b2039601c0700480c0942d1003180d0107103220391144450562101c03150b205403501800174420441e102c0c40400c0000099040045017a0b5040a01e40600c200301703103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 251079136 1106 251078030 251078033
    0x50705030106030c2312010603150614100e03010f0204030b0601020a03020d032a2c0a060305071209030e03071e050607080c1504200a03 60
    0x360020450b19186450311050182d6600402100c40c01d282e0000c440c1d441a501c0540c808100100002c0b4000c0519185a0003400c2c0d501c0100c40c1c03620f400080c0c0c21911894481d180031035507240c51415007030030100c040140300700c8000d041d02c051108110503000140c03024403038844824401d000041e591403c44c18401501507008000504651015481500082c2c1c04904404c01c3c0c0594107010680101600c00050180f501503494130b00c02441e0b0303c04070a25580954110000d05905c203003207801682080b81c943c4a0052410b8407a00a0841d2000f000b089110b42d0100c0e0b400602c915000c42130010542d29081503c0108000740c000558403101007500f40f42c28040500240f0440c07101000c10f00002c051a140c40041d031203618441c4502040003000c1c0700120003201c61700500002a5148042d1203024404050020f84042c0e41d5684280a4480c6a0802000e440036515000f4124103034330707145 = true := by decide +kernel

theorem cover : BRFrame.Cov 250899280 251079136 := by
  have h0 := BRFrame.cov_init 250899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 250899280 ≤ n) (h2 : n < 251079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
