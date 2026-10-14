-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1052
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:01:18.418255+00:00
-- url     : https://prove2.me/submissions/2c64a718-f9b0-418a-8bdc-acfd192a72d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 189028776 ≤ n < 189208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 189030026 1250 189028776 189028787
    0xc0318030f030a080a0f0207060b03010506010e0a14010c0b011e080312060402030403051908150402030103050c060903030f0307030b120f0a08030c0903070803070317010f18020c01020712 82
    0x1109003a00603001004224429a0300ca010300903100041c081d080c80000c018038807130307031140000c0301d1000c070119183c05450614100038038110f190140650f2074200800c8880d8020340c02c4d0000c650000380b0300341d102801c0c0820660301040c2000068148112488240e0008580c020300d24040c10344079407844651222003038400444d003240d903c001040d800c200002d0810401c2c1d000040d078001c030142c501503940e031610300c2c3c116250310034800b00d00791a002001748015581d50003460035001d0b202d070600740117081040b42d080200701c0c8420310005049511807900d21029050075030207002c40e40340040903a42030042e44001d421302c5a00842d00600003030340d038100c2c0c80340034035210080d28040001d00c802803503829404113410b981c4d030303602040190403680003100184401c00900b04403408004040c05550085a03540c5546980380c10201040300400c00d10036040403c0c510502c6014121014103100442c840d03c1c0640181404541c510080140e0740c00b009a512022001d0000380801c5114208200d400044540d00411 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 189031276 1250 189030026 189030067
    0x1207180f060605190513031a06010822150b0901060306080d0503040506180c0307030507030b010b1e0a020304030c2402011a0402090f04051806010f05090a09030c02060c03 75
    0x520009125440086000d00d075845903888031405e01a40c0c5108031480c41d81640ba00b40e10050005008003110510005903201e070300d000300001e88510354242c03140f4042500c91048650f9481e101d210062540c0007261134162107241c101b0010b54000b030740404807008182403950036004800030984418003003080e20310800c00030302d12100a00d02313107046052640c2caa58440c80040c1105840d03480c41651002c03403100c00d22801010310402402c0303e150315604d1400316201d403007500c0281c8900c0c0e080e400008503056260111142c1c9440c50f0844201070090454400c1150002c5003114210310040c0004000190300304000005090715200390000055003140100868002801078011a410100c100d50800480083e81c0c1511200f1a0003680b503070040c2011030b40700b230381c2c144e100d99015040c80b0600c6088242ca40003100c9000d014803d031034843c1c1c1c950b054601244040d100305a00b2009400c0083d070b001d416684a810900d2280c60064901000c0f500010351a801c0704400e8007154100103240d04e84810502d04848 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 189032526 1250 189031276 189031289
    0xf1d0405041104110310090c0509040504050c190608060301091e0f02090708040b07031a0111120d1b05090f0105091c06021804090f0f080c1207020405060612061207180f06 75
    0xd49048004001d049022b940002d9008607200c2c0081400c00106010b45010400040c1c80b200304040200d0185a0a1000784100004600384c02c000c00e4403801c0c1030182140e02c6420071940e003000326150540d09104444004140d400c0008182040c00594498504d64012407883d55003c0301800e03e4107290007403e40242207001810700c0c001c0031200356a40c455480c6002402401c0043c00b4211504105013488116010618210b5001580c0010304280741d01c0861141d1302c036a00e40384481c84550040d034041c07090300c186a51281c04403401b84525842800145080b59028011000c0c1081c00d07440c01e02c03034001403181151042c0d0082100e20010040301300122101c0c80c200ca0901001103d515840302001824002a19003047c00c0c14481c107026082d0122250f43c415a42110482c0382c401c0c002c1d142d16008114100d102d0741c04d04010407000e00d480c0c0d00391550303c1142079000060b03844000030400c455501d190b21030307081e00030494000b8980240001804407039140c0100407941f000300344003803022200c2c0b0707812a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 189033776 1250 189032526 189032531
    0x40203040b04060b12031b060601210b012114060f0114030702070807140312030c1801090f0b040306050109060b0703051e070609030f1d040504110411031009 69
    0xc041000c0700c0c05140c2141e0400000110019010085248982c2e180b9041c0f03503510000540004101d03610001e484880b44c41c40a441031915102c004603040d15120320300044003a182c4042200307110040c1e11a681c0398105042084180b0003440d22060740c0c01c0124512042e243d902c6403582c0310004400101980008121008a140c3c42041c001038000c0e00b078030f400c1c89403000000c1f00080700389000b048900042c0c0104021244c002d81e5808000c81c642100a091341d0203405151070f000c1c0401060310070b0720b003d44081245c1d0707801e02c48800030075080f00b00100d4069041051b0250002000801410f803c0041e1000e03020f01c968550646c107081c02a1803042e404440001c0c030341181040101002410307120ad40e945481d01d90b42c2c85104421200725108040304094000c040002c0701c0041248a0b4010151548292a50210f0003480001a5118900186081110201c80300a000d1514103580b245610134441c810302c0810a116038040b80c12604d9a2405001d410b40000a0103000100d2013005001440403803001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 189035026 1250 189033776 189033781
    0x81b15011703040f0803090a051002030d050c041703030109180f111807050c12040303020a080d0b030102030f040201030c0e010504060507030314070216080a02061602040b041514010e030303011e080f0d0806040203 93
    0x1e66038803030dc20326412540e903518041103200d4240c2c2c0498008103101c000060003201c1d00c4c061f043d00c0354001e1043e412414035000468894058605821500700d4000c000024208441d480da04c6621012041c1154061101385843c50a00c48801d00d41e400b980f00d0740c0d00c940e25411240d00c1189410001190060700e500140701c1040001c1d8000b07400d00e2036680c05200740741c650b05032418403005080d003c0250340d170550002c400c10a44e8441c1001c0c40340f00701d001341d070140001c0100c0340302900c1d035881d03141c0350a0007d68100410300540780241c0040c0b0704180f0a00d00003801095040c0c180407a084103a40202c0140c104407503030082d600300c08042c900607009640180c03800c10b00b540d0020386644070b50f9154400391265400d0345025542d40307901040060102a1040c004542207910030480510b041c0504515035241c0d0368000c00d03d501ca405404150b22029004524507428038410041c0c40c0e048030003c0040000307216011900c1c48003484402140c51941c2e00800c00f00858100203005130200410180c041c1e88180704 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 189036276 1250 189035026 189035059
    0x3060a0e0f031801030b01121a090a050402010806100e04090c031403040806151305040309150302040605071103160f03031b03050a2a081b15011703040f0803090a05 72
    0x1550f94511003400c00003100305000c001600c00c0c024a42e01c0800a0b4507000c0f800100550030b52400500e1102242d040a1030f030341d000051411070b241030318003034001074002c1c0c0010510700b052005002e032251282810b905800790700c1c0014041c1c0c2d1031510103d9000d00e2031001001009824130305403a0744000e403030103182458207040d1141c0d592000200100101401e1004104680c1c55047c8000320510248000b03000e245001d08000e86540c1d01481101c1c2020f48072040e07640314a00c0707407090368103840940d62061f16081e80340d00d40c803440c0e03c45180311075418000c2d2003011600042444046008115241e0407038202842c0d4280500002d504143c1c1603210302c1c421294000107644081298020521424400121004486444000e881d81098803803901c1300009a40b0a004e0610050490144c030b20900700b0000100d110740944880c040744d8403003401c0030704400510034102059038403502c01901008490500f555032080c050710022541c041da41540000521100300e0609800440140c141590007c01c04401c068 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 189037526 1250 189036276 189036307
    0x31e0901021213090c02011b020f07030b060f0621010905011523030c040306201c0b030d090819080d0c030f06030b010e01090911040506030c03060a0e0f03 68
    0x6803041c210b0000041640390103c0e80c0918030301411190100300005201200041c1c02030400000d4041142002000401d00d144000380841d484400c102c041c0050740e02d50303030794606494400381c4251340c00b00a0b9040c100b01c90312850b000c0c0045001e5500380d08001d01144041509c2d0480c1a040111414104001402649111500d00b0452845440c0c2046017210049000d1100c103448544048450b6000080c00403030403028002c0c0c03080d01d011310780c10007011105c00c00c0714070513030250304405208110034022032048058a45c120340c0211111400461104514000a41000070700d441e580c01142030030311700303000d240300401883c900000458620039902e0107640b6140d03494000c1c40c60440019855004801d141c0c0d2003500310000030301c030544007400000d4a903c1c042e11210003d000f80c000b007660750800040d510000b4000c603100c054106500401c02c2100d107050102505c0e0080000341c040c0b0680e0346c0405182c800f04000b510904510b1030004010150f070002d81d00300341c900c0725044055401480072041b4140c01e81c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 189038776 1250 189037526 189037543
    0x30403080601120612080c030d060308031f051011120703081e07020c060d11070803090c03031e0306010302121807080102360d080307080105012a08040b0c031e090102 73
    0x41b00541d2600b040c4403080d40f852207003809404aa506101001080014030009580500a030041c603408080c0200c00e00116810030703203d0035038442d900134441c9100b03e02800749004107055030b5040d00c2c245891403940418540c0070801c124002407030745c403c003c25050f115004520541c0d0300703601043e0394105168025521208045114405c420001e0500078035000d80d03201030442084007401c107450301141d060542090f00b044404402d02e0050303e030059900d260200884685040d0143c1400d540304005a4003245030f080180883e06040d420850a44c2048201004920602e80364150046030029511014103161855101100320b80c014441c00507005500c60b450883c058440d850071102840000121108055412803a60030a440c02d0422080c0702c1c1150017107100e00c1c410340303401c400d599076000110303410741c204960801502800d2212811b119200161051998001e480c05418a515494907280982c06040141d886a000050314021801c050070220b911000000032203091821140020391140d121 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 189040026 1250 189038776 189038783
    0x150204050d02091513020c1501030302061b12010305010905120a120506150703020601061b030f1803050d050d0b04020405090c0c011e0b130e120f0d02030403080601120612 75
    0x11080042c4c036848918940c2980b4550040400c1e50140410040c50001e50101841a0f20303401040c1001c043c81c079002c05114100d940c1a801003007180c0e42d071144042104446403074498214402c015210b040d25905400d00d020314068400081d00e5449e500d44145004501501c441ca484018070906407806d070400040d00e00d0758481a00450b260340d5942c0000c50ba07c0b0038070841c4850a80c0422420705145d40000c4c0b0a0503642203803941c640c2c00c1240c440c0c0c0608403a68000c0100024030302017603008a40d00c650f14081a505014a2441c042510395440a040003e070502c1400064008698684005002e001c0c040d548034064404510740380c141000710b80008801000e41503e4140001d0418000c2000d51101c035443d030007107850402c400080091070020300380141d4410f00c6030403100840300704a042e41c0300c0c12061903c0b0780300815110999540200d15034021404270001064280b0910a000a0a000440c42a4420303071391140180390600c009000200b00710700c1148503034a0503009011401080c07011402c00b940 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 189041276 1250 189040026 189040039
    0x1030902010314010b04050a06170a0b0d05060c0d0b0402031909021305040602130e1302010806010903050604150c05040b030a020318150601030b03010b0a0b070501090b13150204050d02 81
    0x1140010b070064084000014001404a800003441039800c0000d041502c2048585101c6940d450504488600d450001c003008200154003180281005034824035000c1c0002d408801743d45c0c01519103a0500d04101c4000310020000103000c2e00b80c95aa02c2200174a040c121011400d50a00da210a80011500000c90190a9032180000d06665940030083d008581804051005180038544140650002d114031021400310740d801090740603d03070100910400c440103617070140701c40540046410707030005000c880c103105c8403400c0800462010300440b8030440c0a450380820801c03040820700111095040d800303041050501050041c44854821650411480031003d41c59496002c0000c906124101310125148a00710302e5031140c0c41e59984051251100f600d0812990194105050a0b181c98080b001e5002014402c24003a8100e10005890907601400000039812031a0b60746142080c0169401d8550013503a640c500100510400d440c14000320400056007018640800708291121038038000f4803401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 189042526 1250 189041276 189041291
    0x90121050a140108010c1e02030c0a0c051c02060d0c120905250e07050306040f0c0f170108190501090209072a0c0504051317040f080604030203040e07031b0e0111010b01020c0103 78
    0x20320270426a210090044140c175007078921450100c004021034444e0b14011054050804e403d000e4408040c0c0b54581c01521461400e18a03000d41c2d002080903640c800284a6003446501c2264141e100b1201c50a00c104001d2820821121103407425007802c2442c0c1580131080107041c400074039002002138000409040080e04e035154100050081e0444445141d0800d00e0200f00d9145194001405007900b8150385800407007890408000d20900f009001c4d02d80c0540c4640510401206500410181031b4011000040d040300c0783d03400600c20301815244d04000500c4200070910301401c12501c44070801c0821030340315110f815561032a01c182820700c20544629605c0700061826100140c80442d056488903518500b0a4415440c14403504907008006903908010804070380c661000070b9a600540e095001941898548051400c01010081203501050385501d04559083ca10381d0b500c0407000901d071101d8412004000c00101080c00c55041040241e040085003c102d9801150162040c0000e280200700711 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 189043776 1250 189042526 189042587
    0xf2413020312130e0420010c020120011103010b1306180515070b010e09010f1404020f010c0503120601030b03191205120a0203150114090121050a140108010c 69
    0x81403a800758000130b141034108010130a1840000c034410002c038010100d820740000045425140d150070003400b05140c0d0041c043c0f0030700c0c00c0c580340051000c1075001007074442c0104c614601a41081c2c0c40700105d190040350149031542c8107a10385010700707081d1030009440350045080c90308042c42e5129807801900259030386c240451002c81180d1a00b500048051200c1d42d4440d01010900c20444000c2030a501c1c009200c04400b05030b02419003511450340f0400c0c0300e0b450b15000c000200e481d00341c5890521140c1420400021011720140031101c0313002440f10080d107800390014058483c40c3c40c0e45803194224607c5078842e4400281080ca10035045100c407110b080321000d0640b82d03441840030000030fa44088080008000c9281c00840c4240420088c50300d00580c81e03401901c001e60103000c0b480d0308490500000080303503c505541034042209010018a4459030341030030048036010760f03650003070a4491640e40500f902104100f801404050001c00c812090004010103151002d285c0c84440c2c0104204800e80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 189045026 1250 189043776 189043807
    0x80f031323030d0c050f0d0c380103020103050612030a2712140708060a0f0b04090506041b140108040c050a1502010c140a0c050f2413020312 62
    0x41078005011110103c008940281041c480e621040342c841c890585810800700000c280781d030049100b500c607029807605507070322200100003500350300101c000007221104c011104014000e00c0d00001c2000310091354198000103080c0c5900510704c40c020b0744458200c2040440000490308d10781c00d185000c640104407040480d0b03070860313100481401007244950228440000700701800740c5921071500e0661165803080c070f20b03131248240c1c422000d103601b140c03000904501c2250055410b4040e642400200c3c60000000241280c80700d00c01074030198810800c1000300710500c401d80740158540706c00c4840c99498a6500c11017000e1248095040003c0c0801180803c8615034040014040080c40316002503150400c0e0303c81710100c1240c3c480150b00300010401d15038013504240c0e50031100c072543c161a00036100b00c2615040d0b440da02c02c0382c685c840c4281c5452500020711100d466443c0c0c0c0340c40d049440e489940036181005001c0c0c04001c0b00b0191451210050750005a1000c0f194224030519464800100ca48182c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 189046276 1250 189045026 189045089
    0x110304120807060b1906030e0c060a140705070b0301141906030c03060909050303160306050d11131a030d0201060e010e1003050a030e0a0806060102070302060d0f06030c080f0313 78
    0x3003016410403010008000100c17a5419206070395410003880c41848006540c0e80c089a06898008000f04075400c0d00600c200410504a0540050035280450581c1c8092038a151984201c8480b0750100061081d40c1135044440d500000803210004e0440c1003412440c010385407440380100341a80c1e401280c0c04a13001b80c0000c0002e0900e00c00400c4182d2503070030b0a988aa0049031810540884110310507200f60283c46118207641d40038048100c140c0d030980e26040380350881204158010000081000703c0e0000e4001c840c5a80303800070510350500710400506281c4201c0f4806d090959041c1030091206024014940e4116000c141c100d401e40d8036035401450400003035030400703443c5000e91103851040c1070f08001c18044440c2c0070748100901d960382d2002541c1780c1c00103941060060b00280340c00c1000d480c041c00034040c14008408000f03040c1090030054011900141c6c4202c4000ba0090810003140b50f080c4000300c448000c1a01852030410000031124050095010f00c2c00038040400f806526484c43c0c810000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 189047526 1250 189046276 189046279
    0x140103090c03050a0308070503040c0b070809131a030106080c1302040509010603020918040b070807030b040905060a110415110703020d03080610020d1202180a15110304120807060b 79
    0x1c0e000c40d00c0b41021a01c64521280076008a20a00d011030004c0c0d101d0011240f041e90012000031a0354105803814040d54440b280a40301c610050150459035510344980c50744180038101d00140c0d007032441c045401c0340001c0c07551843c481d9241040070080920b01091400351810200d505402040803400c000000740a030ba00029084000c0c6000403a145406600519036070b001225003608200d24141041802c800894009008107103440c089042c0b175001340504c80d001662400d0100301005140041002c1700c52100c420b840301d50000d018840782034850b01c01c2141003290100c04525141c2804003245110a02e03140c00d0b030801445986040c005031060200320041d682c001c0804d00940301504008204c004143c034614071540404c195004178074000a91140d1440039030b1a00031a61010300c141d40000e4005280c00301417603901c100b561080d50745500345280945041c500b181405107c1c0d0740300810082182540743c441c1c3d403040006001107034032031903c450b526034032a081c503a450b0740d1480c211010349520003545 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 189048776 1250 189047526 189047543
    0x31b09091407080102091503040c0812040302040f0203130b040f050709020a031a0a05010c1a0a0504050f060606120a0e06250203040e040204021303050d0903030f0e010914010309 78
    0xa4003080040c0da00c00c80c200780380408071039059442c3c2d16811300700d12900c0c051981c0702c089001c2d0070452507040d1018580c0f040c0a5a0074030484d81e6210701d00c0d410027080c40c6582c48000350006042c411031420744590040c1e008051011070070b515010801201c1c0e00c81c8003001410669829000404006420801d1100580e0020584c0c919580d90344400c0007035080078800d400400e04080b88000b2031b440741c08407154845c1c0e008040d4a550307840c0c4001034860044510741500e41c10021080c0c01005580003000c280038082d034400c000744a1910b030410904091a0600c050480c0d003082d418800b10b56100d00980722110a0500c60306155210381120000078803241801019601031002000840307108000d08144c4407170003e00e44041c0190b8614100d0301c074400d500036108906416400318001d0709241c1c0c061306000d00701030030640f0b8160302ca486180c58904912a035400140000c94140100343c0c0c42058112443c040b4180030552030f21800c000b03005d501d003074014040d501e5050954480320303070300c2a004281e2658022000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 189050026 1250 189048776 189048791
    0x603050106031719030203060d020603130c1203080a0b0103060e09070807090e031e1e0c0d030525030605210d02030301081915060b0306120313031b09 66
    0x18034040c000520043d95604405007048014040b081d0440b864040d0340b283d201011040d000040c1d00940000e4100c1c4d40040800c05400010380310340005601450442902080001d40c91070312240226198000c038001c50000d800120000390415441a0452010480800e203288520012802001ca5920841580080105200e1b031f151001c1091801c1c0c603100d5054810040c4c0f1050300c44103403070008070400e249a0080080e14004003110351000c0c420700b40c0da1000e070300d4090f50b810000c600310825070740d905840c1d000140d0b0b205084020000070000d481103081c1404a450030401340c5e0140510000f81c0d40810501c00c8806030500d00c81d50000c0082c2400828065048946c0c581024101240080329160b605c16480b041040900001c01d1f281200c80c060b006000001c600c03019100b46803003241d001ca854904c903a407070368030103103039806200003034031020010783e8036860050104003281c100403280f114903420800c0052800c0014a01460036617070030020fa0604494032414110704070f0038036800040c0d26894000e6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 189051276 1250 189050026 189050033
    0x6051f0512270102030603190804080304060906020f011118031501060e1903210302160312151802180904030201060e09030307050307030c120608030a09061b020f060705010603 77
    0x400070b98120b03401401c10700390b042c2c50a54034200d102c151006a855401005080045e0804d50441c0c40039510804031282020742c1c03407a034586160060303003040d000f06200300d200740946541003200200d480d45510003408a1200c5180741200c3d4881d4118a070184041343c11840081e0b2070801814800508422102c0c0da150f9642100803e40001c1110140c0b26040780680740100038100302520b41a250401000c070b02600d1940001c847c0d50070030070b030303e401030680034000124010031100c41c012951f402a2200d100c2d983c100c0008004407064441c0c0007031030506601052005800840d00c0c00e40b00490b200c001030341c070700c40300e010940f1224403001032641c00340c84141044209076040d0006c00c202c43d40c8601d40910350b100d82c60b1244d00d82c001180d005002410500000705064466042084440800c0c104428140702132403018040c4c03401c43c0c0128066510000d1407440c813a502850f02c40042c41c05140a03c1d6400908030744043e0310091410182c8100c0803070bd5050b6403603550388100c0b8442c641c400020841e050341d070b26 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 189052526 1250 189051276 189051301
    0x3220b010e0a1503021c0201090906080c151c0f0204050901031a07020304230a0315090c08031314041e1a0f0d030c030e130b120106051f0512 62
    0x42c2d0604100303090030486916240f0104030001501c0c0c2c01000004952180d2580b0300741d00c029003038241c1c10841081d000041900c0107108400181c483e100c0900032290110050007407805013040c0107940f450381000048031001c0860290700f0500c01107200461865942e400c540c0190185030005c6038030801d814000410401001844005400001c206500341c2e50303940016070b280d00880c4240c817180140d00000c00c00b0f042c0c1c2e118001180102c001d0144000940303e445411281c004624020350381030391850407406201d280001300f0000d242c030000031071078940e50030010580e09801c4c1c824120442c012054042503a521a0131816420500c0b2802c0070002c10b400c800d20303001e044006c6030fa0880755035480e07005e00e950420102d21002904c0250030902e0480543d50200c50b00402e2140a4040000440120b42c644e6200a18205000490000400c52a80050402000003054000919103038074181040041d61204070080501e00c02c0f2000b6601d02c401d0b00c020980d440e102c0c01e0140360003002c60100304500030030540c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 189053776 1250 189052526 189052531
    0x41b0201020403060b0d05120702031009080c0c150d020c031e0406080a2307030e011a03160303200a0503210f040b0109020a0203190f11030a0503220b010e 68
    0x180014044040c17010180000d21a02d84d602801075003040c1041c100200b9001c000b445002c3c8050112182c40100c0d130400c408642210000b100d2034640000c0c44489004200b0050788141c03412039104103041d00144400e013881c49625004959035402180c042c1c1c102200b8400d032030080039a13800b1a4514007201c001e070b501c02e5005000b101d01090540021507030f8001c841c8522020952030760828003141c841c040c420341c801d880003400001010340710f0401030b000c7c0400780034600d815440c00300402c0f100102d10782050705110b0130340200c40300701d05800001c101103607006503840310311401880d020f01e01c82e0810300424202124100098081d202c00501200d2031541910b000d01c2035850402000707070075250814a041c040d003042c2c3d00940213541c507100501420389260700400191400d03004403450079031a012000d1400908600403004650040607981b0f0450300700003004004c0d01d82c1d4004e54901211060b01074002c0c04040d282e1b294465004201c903a01f00591280052083d401109030031083d079460f084a00303004800c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 189055026 1250 189053776 189053783
    0x200f07080d020616050c0a06090c080d030203220c080304030b01030c091a060309010603150903110f1b0a0b0d050919020a0b090f060703080603010b06190e041b0201020403 75
    0xc8a1003100480c2c80801e1460040c44a03800c08400000181e108807180d0308001c2c03045006000700c0034040700140642c45501c410a04c151441c00300c491401e660b80d0b003401d010201c0b8074189401081000280c1c3d0919051485242c3e611050000b540e005090100150300720b500000c08c030b13110004020090065001095040381d105941800180f03440b089006c0955082207a03d80c03107121007401040d101c0c5000790256a00200840000564980c0d03034480789440d01c6062002038005da0ba80780b1030070915520404000e40b000030500103190407803051780b080d40c0d00e420b02001c1d001056040d80c0010031035a2190070b5440204808040540c40345103500e8500024002910012550300c02d52400c00e1a614001c0c0c3c1861030250010021194a072800814181951200c3c501c0c507444040711041d0034455031f683d030140015902a9903942100e14100c7d060500315803841da803003407207840c06100c40c000029403000036100c02c1300030b071400d52078496038070000c64040c0c2088546030750701c1c18100041a0080e40e0560142c81103070701 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 189056276 1250 189055026 189055033
    0x3030603010501170c0d03030b210c0f0d0b041a1f0e070504060518040903051207050f0306040b040b0307080d1202250302160e0106030e0105010f06200f0708 69
    0x341e500c2415400010080d0710f00703440d00105c81c000c4052600502d40c0e485280030741008038940c1d070307a20001204040701c010b52050740112004044810502000560b0a003501038940071010101500007504045029038020a070f519440001410010145000748880c0e103095841d92080c00c121142001c14240c1c010751040071120404001007007070750705100902444103900d0310b528140c100301007103800303038480c034005481d02d10900c82001c80f503120b502c10940b450340641c0d5100d0301d815200c80e8040e0b8400307003c1c3ca0482004424054103403146504c0007240e0300080200c80c002a82c0d0000c0002c1070150405c04103c9901d0f01a43d0b42c0050070110100e0b183c0f0000401d0b56034880c40c00500806031080340902106088400800011040040542174007880018060300407180548441210034100491a0300440109001c1100401c01141c01d80507440c0420b54240091101c0e40c100001c084500702d09119030410011a40e43c2c2d4a8404000840740c0003000005040d201046c100703c600c0c6940c4c0102e48240000e610 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 189057526 1250 189056276 189056279
    0x140306013c170a080904090501060f0602030a080a1b050304050c0a030c06030c0311040918060501080c01030f0c120f0e07030507050f0102160e0c040b0307020105090706140d1a0d0503030603010501 86
    0x12008203280301515403044ca01400e0645039405e10000b406403082c12201596602c10110300318600042c410002e00716580111780d0384d2010b140c02010002c010b4824210581400885400c5c0340c07130b2070400360b9460400d14000e500c030390702e41c14981c0c0b4203005036542da600301000c42800f0040c0004c0150440964000f80c4041c8105484044110102c81c042c0e007140c43c0110003444140100d0149030420700880f45440044a40c9500684a441c1147d200f07a000090359400700300d600f00556058055400c04c0d4410310010054100c0f0ba4030050501c1c07603585c008083c3c0035980e981c072744030b4000e5581c03000d520602d251088407405038a92a14075035500c040e005240c03040700f000c41c8001880d8800504540f5a610100d01c0700c0080f45010a202400c641c064168410140c0a01020449100c140041c600c540720690020945d0309010f44000d042c480550031401c1045031030082c0c00d20840114044030480b9256600001c0c01c54000700c4100400c005659845501c90900702d1050240301000000d18000e5100314000c0000c1c0c1d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 189058776 1250 189057526 189057569
    0x901060303020d170f0601020102070209070201060801050106080c180604090213030209060901151d060a0206070807180506030603010b04020708031005040209010c11040f0c02030a0801140306013c 86
    0x100740a40c1001c013560402c00003a40d190300045000b83c2142040c000942003403602d0b0300041d44880d00315905001130b9900c040800c00d096090240d940180b03840d0815680074101444d800f5001d02c10110002080c031502c8141d52015140c000807030303000b40741d15401152503400340761000041d000d240c0300903403003030107940041081307440d0074070300f050490700b6003042c056462a0441c0c0644100c110300c510342041e440b8280301d91109441c1d4000030108802558080c240c5464080380190641070064030801c1004440c126a40c0c140311003c4042c019110119070450b100d980341c20000780500740503804171342c1141c008120102000088006580507450792003010b040c0da600c50b810b010407802443c0d4681d00198800b51a50017199211140b2058248058404a0200041516101a5044d040d14040186d00015030344c0005544600e0b01d40c05030140e02c948584031501d5038002aa614418081c0824186282c402c400c24080d0140b000100c010700b248200400020014100590305a03620810303e54002030074182185 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 189060026 1250 189058776 189058787
    0x91c030e07050a150c0507030209010f0617060a1205100c030c02120a09030f030507060e07090e0105060321070507060f03060503010912080603031b030d0c080106020c1003140901060303020d 83
    0x3034420344050f213a03110f0400e080881d096683d507082690240911100840941c0f03507010014080c24031b00c040c1c41c40140c64590010241c1200880f0b101401e4050014840b542d0b4500b501c48049581d54039408042a083c1e0070700504160140d210001c9040c544070100003055059001a131040c0c20f182c00f6611405c030404e8890b20319208400d5080000f0b42103440a00014100c070041d40715079406482e0032030600b40d5a60300c000c211030240c1943c84559001460402006105025030151220010001d00850030020040b03603598070001c06030329981c0040c0e0700c00034500d400101660501c80e00502121400307a9940c0001d4900502d405c156000642084c03004100c0741014020341c61075a41c03091505041815074581111280000f9100700d5050104210544c501d01101c4c10394507943d000103024590300d1aa006500c800c40d10310070b4009060141020041200c02d07004960b84400010940d0240c0c82c0d002c00007411070050880c1100ca900c003405c0700c41802200c9005502050030f4a2090b000c0703407052050040c0c142e41 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 189061276 1250 189060026 189060029
    0x3070305060109110f070f0209011e0306090302030f0706090201021203040b06210706211803030b040204050a06080417040b09011206030f14160b030f091c030e07050a 73
    0x81075201c04010003418546078440034142c498503101c107041610b13500d604a01a48030301e8003640c0107040410050154034200c03400500510307034441c2d54108002d40421240e031b0000c0d02e01c0090900b50391600a01e06150007032080b00c0186212074000341c0c1e2210070380740041c0241644d8806030700512510109d000d181c3e200c401100d00982d0054901c64003903031940300f0400c805100b4510030381041e00c1c288207611318480811035603002e452283c031052016800d007400b040010300b61600425665090031780d500b80d6202c2600000a5039501454081490f0300d1400105000c0e214aa01040c1c01c0404001c000070307699480303032031640140e01c106280d42240c40004c00c8803205005078068158040802c04c1841d030150300030544402880e030504008180580d03261940c800c0c0c1c0c03516604c1138595030250213603480001805e001c6071000602d0a00003625150402000180d01e000050121071513400c2c00020800540040142c4450020299800801c0017401c040040140c118006024403030b104500c2d0200311868002140070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 189062526 1250 189061276 189061283
    0x150501060503150f0f040507020706030b0d080319020702060a080708070c1e03020109080408030702010f090e0705031806071d01110a060c111207020f01030c12020d061706010503010605030703 84
    0x3e2103050700700c041152030348018480582c4500e80c030801d001e480d11036014407803052007a60094001e1ba0320300500039060706c030b010001602c15134450301444006100481038030381014014248245084619140c00b0003403085c400080d521410204419010342d0340010981e104031016540c2d400340f520b84030707000d95081c0241c040003404071b10000704070904018000c1205900601900c00803501d182652680d600641c00354100c02e0598000007132150665070041c6103520035010314500038604902d041059044410050464402c00030004082003080c45224150980c000d604001e6800fa81400040a071944d140c0c541c0361044245c424034401f41b42d60041c0d07a074204c0041080c001d012010200d50340c480c0104000c01d100c000f80911100745654440040044030441031602001e1507542900740108507043d494581542c3c105402c02c007281d051582c0c8030083d0383c0c0c104140103000d6151040041884d01030201e40d00050902c1c17442043d0042000400201c050403248183c00800240d9160307020b15483d01a0740c00040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 189063776 1250 189062526 189062551
    0x180f0306011a13030c030b130b0f06060c031306090b0c0303010e09010e15041b0b0702100915030b12010e060708042102030a030b12190204060b030103150501060503 72
    0x100b10800381c0d4a044401d00146048261074101c1005039034040034101d41054488424480e401d00810034184c8025412000e46502404c0c1c05107e5583c40d0f826040007000f61301078081d41e002150080e01c412003522401c48050f800c0d070303850f9020b1501e01034004101d4807031400048e2000c0400035400c8220030450304010140d1002d18170750782c00d0128038502c000d00074190749a20340d0388020520070b4040030300070b14102071a40da0101d0528105420140403c5a42104400b5007104204c01089045081030841d501305134113440d650103544059000391840001c40d8000b5420242403c13503041c100740d0540c009100201f0440303404d1a00ea035200003007401c03121101850006d6500810114003000d006400140e0300c544586010303c03002c40b868844030240e03a000510f171030269201103018801d503901070058081c0c0c00340c290780400c64a0900740c2180d5031a00c02c2512005441c4002c50413105644494001002a00b540040a981c07940d4a1030010440c042841c03041c581c0740d1801002081283c0304070110b9004198442e400f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 189065026 1250 189063776 189063779
    0xb090307030807021c080309120306010e0f042a110c0a0509280912020a12210504080702150a08010b030603030d090b0603010c05130b1605070308180f030601 69
    0x12a1281e070b0050f9400d907804040766024120340320b0030385c0c0c0c0c414a0500c918503080e12400c00506580c41c081401d03400306007103a4148204001e40e42d018902c000e040b03c044030031241a0000c10040f0b001000c210540c0f00140d07645480c070b42d1440700c0d0303020301060000080c0c1d2080c20060b81c034058561030740501d11080340d00c0b18040000300b040303240900b60030380c2060341d07489614078054400300c0c201000342000d1007098400741c0b2a001107080c02046401c04c2d003d4210b0340054100212a0b980704007580c14864003410900c03111040000b203980b140b01000301c8001c07030340701c080105040034182440e1942140307400324440c480b0641c002c0301040c11401520f1051540c0c3e15280d802d41d0030048407001581008010a8240c8024001d0100c1c0000030f024802c40c250240d000c407051414900103050a5034242159801800b03401c0001d03841c81c0d21080427800854031100c0354980c440040c40d840c40034000341e030784024085c2d11030b0f02804400c0c000600c00900c64550744156007003607402580c0a2000f001a0340e2502c03681078004900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 189066276 1250 189065026 189065033
    0x601020d080f180f010608061b0a020d031505030f03070c0f0f090f0b10030b0910050d0605040219030510050a0b0616020a05120106051c050d0309030203040312030c03060b09030703 79
    0x600f2100c910140c141e0b01d0001d058420039003110300c030754071400c1c296100500f84048001103101c20020615580d80311440c1030684000607581e1500c80c0403600825643e2821103035031020104440000e040c0040c141e420280250703140139620b40141e50242c038100100b050020301c200100002101312030443c4441c45141e840c04240200410710107142001d8240c6422100c0015038802c3d02d0016207040725100040e03c41400024001e503900000c002d200710004140062246550388544c03500c9550b40214045200d5640b4030204840450451164000c0031100001104000d0081102c40030b144816008001640c0c8081d541c2099070801c44016422200800c80b0308940d1802140392440b090016186010380750f921000b203078010020307103201d2a190355074600c280300070703e0810f0070010b44480d031085202c1c420f560350300e500d620380540c414140241580c078032002c020035000f481070350000c54002c80d80b40070307441031904050040c1c441c00340c003035000038607003c1c020450342440300a0301c440354000340c0180161410341c0e9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 189067526 1250 189066276 189066301
    0x90a02070201021b15190e030601050a090f09080a05031f05060306010c03090807080705120106270f0f020309160b04140f060406050403120c1205030a09060c080601020d080f 76
    0x2514503088520143c00e0105c201c040b038010aa110724001c200c100503408694000d150304c03811006503100e0f400c104010011a50b880b04040c042c1c0d040940001400009541f0090041c503421200510014011a640100e19005009144038204241c91955403138525000d07013403071108034058154451403c2c00486c0155118000503001d241c400d04101c8002611000303001d15004641d0b010194540c8810024086420041c08413414501104002e003d85401c0c00003c1412418441024402000b82c10b071850050100740c002c000382241640c4100144130100c0b07050340c00b960007101c940085116101110b9001d4180c0c0030300030100c1c0c000e5500c075400c0501340407910701c03a200444026076000c03031040034058959640000810003443d10341c90711543c4600d9840e2100741c0c003c00090341020310010042c50404107060707030301c19201001d0a29241d640c83e41c88404d14001030038030500151a42d884c051301108800d400c0f0600030f0191009808880b224a01c8210484500500f02c0348008408882000b0a1540c000c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 189068776 1250 189067526 189067573
    0x1101141201091a0a0e010501030c03050907050f1305041a0702060f06040f1401080d090b0a0f0e010507061409061605160323180a0509040b0c0d06030f02090a0207020102 74
    0x10a42254040000c600060b8071941c107405c035244040c0b81400410141da0507210f0b40b1058425400c3c00e004c0c41c5401009a0780705d40c0148240341c0030760800c031041c640e65038605201c0ca0741ca41b24904100302c181881c1c100282d0a500ca2125400454034880c00701b0103182c00041c00d9441203065038500c0c10140e4800003480040c18240404d000310b1070311211002c00030281581c140703000c6c096003401410b00d4516408014103060040d03116411490302000302442c6a0f9100d084c41400d01d5036400c1c180940d000c50750040314544035034203014050900c0c0441407030508404180160150800303508503000c3e6140e1008814501d0840c1d45480c3c003145040024840700010a00141c0c20140a8100714124141d00c0103c504841c150440300782e4409800160807400e0f84031602207809800050b2003001c1c109040c00b01090700c580001e0000743c0510030b0a00000c03082c140c0141111a070b24603401c02480b480780da07480d000c1d40070120b0710812807081101c00006000314a86209540c44560142d00030002145400020780306143c44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 189070026 1250 189068776 189068801
    0x5061804200c030705071d0c0c10090602070b0106051c0902031c08040c080d050409050a11180405060d02210a080703091d0108120c1504110114120109 66
    0x701d040304090703a002100a03081100e00000a107941e10164a8003e080008540003507008401090b087c00305519a07940d8107034809407080340b481d42d440651042c0c0e03242c40304003140400310508180e240030400c038981d005400018480c0c1e420350700350390300d03150180e07454054803e00f84040c400b030792055005250346400005240e80040d0556400001e241481c981c0301c5131178104400031500b1003081c00104086000e16000030200c2c54082c0c1440c0c81044001041403041d40318054956848001040802d01d0395800111400168825180e4580101e003510301040c04030b0520034410781c90326000460030b003020a00404200d500400d070702c034030005440300004c0500300c551040200b88100c0ca41ea400080e4100c006041c11402078980200303a9140a0004080388032040c003105030b0303a564100400142400154601c40d0740071050405403a5003060150525020780106000024041e990a000c1031200603d40802c00c002d0a1381c0d01030346141400c000c0309440c41040400803120481030b004212000040d48407031a41041d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 189071276 1250 189070026 189070061
    0xa0e030d18080703030b090901061508181509070909080904020703050f0d0b090c0c1506011404140405090a05030703081003020303030f070e0d0201080c03061f11010605061804 77
    0x8907180d402c07968105000480100ba50340301101c2e0390303180c24070700c913540280c08600a2116506040c0d520b00841d5414a0320420f0202c0c07500030607208503070401302e608110903001c01c0780e41414101285161030302003903403106400e005500c0301146809440c0180140d85411151013484c005920040c80700039800580305900300481400001e80800c0060014000c00c007040d480880d005010b2030811000b9000900725a6100000704443e003910b94022503d101029060300c0c48041594031100165482010007940d01000300b00001c01040740445852815541c04042d20100016928080d1440c2e0710001000003a00d258018065400002d1240034402d5001d08100b12001c49560749038046403030341e0000d4801d142075842c001c0c00c0007050760f408690900c0701d407401c980b15007009025070000f8003018000780011a1b040c0c800000980d081d00c03107001100b1440101c41818146203008413004001165140e2001c005508040317000030a4075224080c1e030040e04c20f401100309201010f4003080000c00880700000144203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 189072526 1250 189071276 189071321
    0x141906180906050106050304030c0f0302030409090605010e01060c08040b0a02031c050f060a0f050d06020c1c02100507050906130f08070608010e07050a210c0c0b0a0e030d 75
    0x6000340e24140c0d90001940022860740080c0c9880e40648005030006010468188208404280c2c0000780303241d541e0b04a84112030400c09820203c2c11803113650055000706040c0842d10302081820350240f8103c2d0078181280481e642c81d050100ea60020b0180040c004403000c0c00103111001d40e900041c002034200f401101d18100c2595007002d9038501c5048507480303c80d505d404200c40c840701d208010343d000d002103642c0c480c0c039030600e01c1e1004c005a460003420b00440740d40d011102004100e0303045648203184001219107182074010450340500b903101c1d0042c0140998a024254032480740030725030041146440c1c0e241812003c40030321035039411080e501c1500d18009080001d00c8090030742c40402415a110103031070313414148007014142e1807060303000c1030a8140b26020804c890340d2000c2030318100300f403034603008441d101499943c1c420101e01c0035044074010710b40b0789009080c0c2d41161154155502c10014402103a0702c40c0c0b5074200700c0f440e50f081e00e00c5682080201052101c031a900000310413440b80305500483d0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 189073776 1250 189072526 189072539
    0xc0d1b0206041e050604030c03120606052b02031005100c0206090f030c121c09050904060b12030d02040e09060601020d0e03031b0a0302010b120c0d0c050418020f04141906 75
    0xc094400b60f010802d0b0340d5000b01452ba2241105030307104d8100b2412b00101d403070114010aa842007652100c105050300c00304941071b80c3c042051108009251106549a0a0402001d40d2011041c89528840c001c040f125480650142010340c40854000f003401d03081c4031401d0140300540b0b00007e080c51303050007081c80741c4a85030740d955241200400100000c120046c0c070400c0d440000c0500b54444024003480c83c0b4200700035602d181445610030382c0080702141000e0303504081401c48100c1d4a8403110b40c04041005111100c0603800390080fa602042d86201903101e00b0040e5444003800d41e074460060308540010500e0341d02510801c5c4a29601504a0b4940600f1010b00d4007103004003d44444640c00c070355110b405040d4240102a80120112000603d80d00c680e200e455807249580034460091000000c11001c0c440c540751844000d180140090024540101c0200031907040f0303050172442000b14030403035100d0341014440d0340800c02c41c250710310010b5219940d520510003c0b80d40d59011450301c6d00001703c0c42 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 189075026 1250 189073776 189073783
    0xf15040f031110090605070908210927180c1203191d0306070504090b01021603150f020a0c0b0a06050d080408060f060a0312020111030c0d1b0206041e05 67
    0x500f03807001e8000510100501c0e2400c00e6510141103403003049030041085c407450703d002c151180842505061103540e00201c03103044000b80500c0001680c00616800a02980e00100800c1c0c00344004040c2c840c0860750f501c1d440c5001240070180782c80c00580c000780454045051031780e419218040e82d00e089a04103141c41c5041101005e05107082c5000a00c00d10311141c24800d00404001354650071000f405240c68080802402d0b805148200035800b6181d90380c54850780d00034460f80d82c0180030414000e20340d07600d900b0582d6089503103850040c080303440e281404035162454820b40780030301c07156510a50780605548400d00004406090145a165a07c0740000c1d650307a10011515400e21503004280c40d5031400c03c0b0541400c40091000c0c0d00b6500030410003425646522000c41600d601030504046001d14800c220300500c00c1d03506d4907074400c1d07000007440780d1000400c000d800118441c85051283c0c7d09141d03041403001d080c945061002d60b0100c40407400040440c2706042d4810748866106001c011140c0311140f8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 189076276 1250 189075026 189075043
    0xa06051602070503030f03070f0903050d171f060e010e1917160e09010e07060509030f07081915050103110906040c0e04020310050a0807080f15040f0311 67
    0x200040248038441280c05000c03890040c0003c03005181402400e410000d290300c0028016400c0054000c0d0810866002d401c10001440c0c09c0011561300582040d40980b0801035041d1800c90206103c0000b00201c190418071101c0402108008503e40e217010380540c1c5802100b1465030510070341a07410050f03500c46150183c10050b0030000b0010142c98445105814421100c1c5299a80c01020340340c40c441066200003822240c1c0304440074000d9450488640c0102140c10b48050306000b200360020b04c41d644040a40243c00f800c07001e8a46070344032546440e503103803054414449182c101680224005562841c010f4109006070900d10300d400b8041c1c01d0508946090700110f4680b400302280300d81a042030a00349500c4482030b1400c00c920598020007400707501e1032a106038455500040056900b0b034203c008900141000782040c130180e6207a01034a41c661555000c1c100c00d5104510583d036510000182607420014058500720144d11107803500c000c1c10201840c103506010540a1070178000310301304031420b07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 189077526 1250 189076276 189076291
    0x71b050c0411040807030f02011b03020d020705040614040906060e13110901180504140109111509060304080a0e2101060506090f09150907050c0d030219050c0a0605 72
    0x28880c03084000700022a01e4030401402214820700051207407030b9000070550103694101d10060300e241c2191004807040e001415421103510300000011007010b4001460b1018005a074003652040d50321401444101c942c144210914000d0200400c0c0316420a603100ca407100c1c2c003500b400b240701510b4180c035030707101c0d40c0c00d8484c03001c0d072004111a10203001490000814021044622200a5141c01c0250302050300303000d040700007640d9076404038040009503c01000400f1303001c0c3c02400308019508200544120360480203000d00c03514030f03107040310040b6101103940c0c03054014140c03030460f2950b4650090036080321009c1d40900c841100640c4540d40c0c1d0500d070384a2265541c60b05000f028104401c0c50a5414076440140145c0301400b01181c0c55881c2291079070024801c0d85e190003950783d02001008401001032003160054209024044460381c841e000382080320300d1504640800401d201d0807012446008400c8216a2624100c213555500c00d5001302811503202c000c5910020050b1a4481210425035414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 189078776 1250 189077526 189077533
    0x5040809060703090906080a030c0b07090e010602010902030c10170a02120a05091603030503150a0b0c06040b0f011a030403051210091116081c09030e090115020a0803071b05 76
    0x100545c21407400b81101915200c0d000d021a68280c0e9409407140070021002480c081400c40010802841107c42000500809201d43c80c9560340b62006070007000111400d0780240504810840c01c0c0c02c104118001c03041d4580c0d1209029103002c105500d600740301400885070a5000c1004000da0301c0c0300392000e8042c8803000300004450402c2c180417864107400c00703030701c15051450020400c04603030804241e81d40300c1100e50107481881c000100117a40c11000d07130031421208002143d048084c140024406101d64412042441280c0300c901e00b28000310b03000d10420000030006040c407410416042d020b10b070010320038240281401c1c0b040080c140e40240884803420342a400400070418401e10380501820321541d04821458009480d03481440d4221084001d44640b03030028810f107002e0f107090980c0300d20f880c0411701081500c00501e00146a998401e0002d840b50300039400105840240e056095240c402e260014078821140b41d81d040420f400040a00c02406000604644a150488403480d40544a900075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 189080026 1250 189078776 189078779
    0xc050105240d0b1501020304030501020403060c0905090910021b190c15080103120c020306040b0402090708010b070303090302191401060b03040c06030506040b040204090903030b04110d0504080906070309 89
    0x10003440d07020788151184030394414000e200226031400302c015080a50442102c0d006aa44d4005030700e10312030341c0d1008140f58070008001042c405907501403e1400801d0343d65142c01d542c2d800822802840540341903169400a101c51820a80c0365401800560b09148010544070108a08103040035140c18860300c08101180c041e404000d2461140741c013802001d4214484980020f000600300c2205010090400300190a1094058010034240242c03541c002c040301c0d02c03854540b5100c1540c8400340d400320f00030300d0001c0101308114001c800c100d059480e0160203505060740341e00c084014001080043e0103500074035a03401c1c0705660710b810810314030b0300801d14403050300c4880458508554543d072001c4191075062082c4000183c11160740d8003140d90030724011400e80c65000000b8014181e50b614168047d20010780061038440f66000300000314000d4908100b91b041d804207200a4442c81502d450204e00100144e44801c641359001c2c039005130080c407201c0e082c8180c0310041070065201c03460603000704070742000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 189081276 1250 189080026 189080071
    0x140a020c040507180b03090f03040b0d0f110d0b0f0301020f0c07080601080d1202121503010f05060f0d06060b0f0301030c0f060807030b010302070c0e1005010e060306040c0c050105 79
    0x100e681000e25850013500c103e003c0e0b14111519040b50203601003074040017010903003c0008114400e405881102940c0e40e40d40d03a1222032149500551102c281c1c2c0c1c1c18441c0c6200078148621a0314140700300b04440c81e140001480c0c0c3c4400a0010080c40da500000d84441490b5940b02440500801c0340b007a41c0305d9503100b1030b049405160503015400100558046c00052001d00c00205501d00f800d6164186808003820848490000e40100c03101000d0b0011042d04000301c004145848114445068008124100404407170000b034800480b109504910841d10806103820113030311503046075000d00400500c003500c9807a42615540f08005400d0340c02c0012005100b0310a443d502034009061081012854901c0e086000d4000b540003000a4103040d542d41c240e0025901940484869a6003e41e869140315100c50780311601500c25100c480c00f00000040226003540140304030000d02100401d914115034850707041001500c1306c8041c01c0b0400015a030b40c80000346090049030302414101480c2d01104041c1d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 189082526 1250 189081276 189081281
    0x9011a040204120b071119140d021e030405040f0509120a12051b120702010c030c020307020910030b0a140708060105031305030f0a170c090604090b01140a020c04 71
    0x11861441648100810071070710000c4032070001d007680c0c480164515590380b284243e460f002801c60b038401c1d0b4040e5407000824203e01094140809105500c030b002c25680746d680f02ca5880602071800e90242c1d000100b110024103540c0c230607000310802881102e14280e100d1002c81e0135903a0b207051007441c0d00d44410034440004024800308032405800c0321081e003170910a01e0014803030984803480d00e103115512008a4004848003d13080354528180e210309640707041101d105c841240c401c85030080154604030740d06102c0d920a000b02c01c1014031a43c029403c05805408015a648026126054201c1c91441c00030020b100744000d40e11422044078001842c072041104c3e807082e018028002030030840c084040101c035170b030440240c98100c00c0d80c8003419a8800985042e9140d84038030b904c11000400c3c0800c8094a440e070002d010720717460082402501d050740b26260440860302545d220558080020700c000c1c48a00907541c000750801b401403418040c807213403050035040240c2c050f0702d105005070415032000c0080d05190 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 189083776 1250 189082526 189082571
    0x2041a04080c0603040305041206110a0c0515010b04090f020c01150e01090c0503130f08030a060f05030a0507060503090705190501031a06190201021210080609070e070f02010905060901 81
    0xc1da40340b4070351716140d9401002e42c4035038040c00d0b0254400b0900c034030902416900090780c541d04035030030b99601c41006a0240c02c1312000d84003101d040c803505240030707440c0301443d00c120f0407901d10b036254600b00b50030040c8240103840c580200000071503091080c008041c90074014424079543c0e90310a02c0b04603040010a28118005801c4405c1150415200e544110390001c1102d62154020786803550310700f00c0d841c01104507254000f024088480200500900d00300641c0300e40c00b00c400e0300020098443c3d0340c809154492030390307010140094111407000c22a1900442c01140e010310703581c06803010240c030342000900d04110782e00020a0450044018803d958040c4100036119080c040b04c80c03401c49004002809038030400044580710560756210924040c001d40544404044080030780040d458001c810102149440c4030b6186a4031404012542d03441001c5030341c205440040140544996a0400c00d031001c043c5030402504665903040254080740d020b200d1580034810701e4001150769450704000d080c802025 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 189085026 1250 189083776 189083779
    0x12070617070e030a0f03180f090e0705090411150f0a0f050c0703060209040605040207050f1207110121020309060609060303040b0904050a18080d0c17041502041a04080c 74
    0x348201144a5a00141142ca03441d84940c0b401980ea08501e82107c00c20074440b00e8aa80041c07001010401501a281041c1a20b100010400800040c0c005e610303910034540c403030030744c102c40c00102280120321201410301210402814240c8021409442c88803140d1109065203084617000c0398400f85c00b6130010860b120043c051031301509000e10344102689031035a03480000c00459001400040b151100e402041c01404020421500c61400341001a10340928000c0340d40c01d8010036441180790109502921800c81c2c01c0700040c421105100c005688a409620b0441e2810003002400004000a40000d6124460710005081c0d107060034418000030040c040c3c0014031a8005004c203001d8041c0d41000e55007404c404407404a955191110a03030010801c4035071200c0b0945d20444600e0500c0b040000034941c3d00740c0c900d0100007111205604aa2161000501c030b070056991101050106e01603074210303040c0040d290001032519903101b01c011106a00300c80c0740203001e1310128040001e0348052215141d040700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 189086276 1250 189085026 189085037
    0x1501080412030509160603060f050306010605030f060406051c030e01050307020d081317030f06010e0d30020a0201020c06040b03010b0d0603050a111905100e1207061707 74
    0x40a40d25250780ca50a041c1d040109643c503000a84440820052100c1d5042900340070102c10b034654100074003420707441c054103559444403480040c1600300055030604a5201e5500c50b400c41e100eaa40c0b101c070800014001d103a105440c0d4402141590761000c1500b0007030107800001946028a190141c00d0f0142030000c181803080038010000c200c0d4010502c40c01e0590103241111a81c1d507481ea44400010014401808070025508200d0044100b00003c0d409020508041800342d9603c0c4011110030828000040d0400002807000000071a28404650701484000740000f070030003400da801007400240c4194000582c451000c1d0019960103014245403000203030380c0e49103001e00300741001031248010b10801403001030014030b0f82c900683e0b41c0c0c00840619880400d5901d02c42041c00d24880d1182c24050107446403903a8049140144a2250060102d940181c428404d450000b042502c1031400700304800d80100c003452658481d030505028142c050b00d684d03120009081808001c01c040040020011400e020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 189087526 1250 189086276 189086281
    0x6010207080c0d05010e100c11010501031101031107140601060f1806080c130b09040507020d170601050909010305010c03181e030c060203071211040302010e130204051206150108 78
    0x45010038110702c485026207843c0010394283c07a1880c01001d0a420790102401000742d561070682d90780d00030700204461a503c02940c10490ba030b10b58201c500c01e1000074911000290290704650003500064460080c0030ba1450402200da00d410316a5600c0000d40b122680160005005258004107580782d0030065140124200001c080010650f510360f0141c0400d00c01c800c000101d0000c107010445080000048459064940e1440135104c01e4100501c890320850030f000c00070321414800940300003810b100e0b0b40e902c1188030304481c0040b22a000039040504010080040d601241c490004641c0218411400065043c1c0c0d0400300804903103000f50503091000c6030059000c0880e050360b11540350000070590075141e8041380c5c0380030f035500540010001c000500101c20072031403940000e00103603036900c20f150a00c503031a443c000c460300c0d6210340e020090214180d08540e113401e05040b5422417981080c91001450301d03440c0d00c009000c52030744455400b4158071180c104000018030703404810124a023828070322190b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 189088776 1250 189087526 189087539
    0x15030c0f0e01030f06230a0b01112a060c0312010b090d03110c180402010206100f0b13030501090f0c09020f030105040f14100302030601080607020a03230f04090506010207 75
    0x2490622015001e000380c1e44c80071007070000d640c0c02450000603004401e000000340c4075940c203454000711980b2010341d24020000ca034035401112803505d144041c0c1d0252a0402894080d4500021248584411a01d13890365408054560100400300c00a001004646564409041c0c461050058215400444051002160b6906c03140342e0203190a5050030310a403d120550500d503c2e050905420799485400b10700e540806c101014680d41c0154001e9003614401d595075295008403c07c9441000411014101c040002c61110000340801400d0140c9020f019031340c2c1d03100e01d401d44440810590b20a400b094100e010007415000d00001030a10950030b6041000142d90344e40d19010500c10540a00d45601501c0500c1019600042400100943d418824100440c035000e6404c458082203000c2d108440020a1030480010300c50701c250740710350040690304001d82c0c00b02d580400901041d24080b0080c40000907002400e0064004422103549150710345140c8008170003a244003400850542d0800c150902a8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 189090026 1250 189088776 189088799
    0xa06030603061b021207060b090406020d1b090621050705040806253209040f05150f210319051204020f06070c12060b190303140d15030c0f 61
    0x105210203510b075204d070107d0400c2c0c406002210000da07402110801000108200c83e4080c051101c05410200203003903030305000c4034148030340c1c140f2000802c0b06d031340c0100000792003641c414221562050480180350002c030040002e64000362003405c049840418148041001003080543c00b05001000404007040500e6909204060040000400182d04500e01848800100d030410b900c07040e030780b150b00c002c5002429036025000904198440e505201c9050400c00d094060140600c015125006c00c01c03580d04104141640318489403508060382d203410b49816180440180680c404a8026550b40d03019070358000380c135080400c44101480000e00500c055860403480d9594001d81c1951002001d24a900c00a0954060b11400a14141c0f0300b401c0400d01b40080800e892019200f442c2c02d01c082c0080383d0070000800e6004100700c0749681c500c0c60810202c1c6c42289210b8503420a0750520f480d01c0c14415191040c0c0d607000010359140ca0074201c0401c10085008401c2d0000d1940107264900d40341050400f286 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 189091276 1250 189090026 189090043
    0x140307051c0608031606050c0c03041202041b02010507020c090906060904020a0b180f0a08060c03040201030f05131202010c020d030e070806131103150402010f020c0a06030603061b02 80
    0x200c81030300d40e1201ca96030344103038080005801c1c02d204a80c0c54802c485821104051011000c6918174104030204030b140002c034080d111580400d8000d0750270725092598218440409030801d0307a216071076121150b0350400e5984c40d2904520260300114582c988240060718002c005c0004900a802400812012003404608144c200c2c008641c907142c65140c6c0e00010301e030552140c00c506040040001c2e59011104260221003481a064070343c44400502001049420a00c43c46103000503002000000d40c5116603100840e407040c414140080e8464951484078216001110350f10042029540b05405005c65007109071001a6144001c1c003014582c4840251608000310800341415280c81c004002c0110900890018061400842c0c02c0303433401d044030b89407034140c900042d10780c0703002e05003000c086003008600034000081141d0070003c141c40742c0d4011103500709080c0e070880c2180a40102c0d80000c1c0d486003483c070000d100556001c201e82c3e0441c03d0540440b00200c0012007802c2001050704040380d0042014034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 189092526 1250 189091276 189091297
    0xa03090501210e0d120903020613030c080403061406040902030715020307060f0b011d011d120604050102180306360a0309170109111e19050114030705 66
    0x41d0b4150703103a240780031a142c40030340d05182c207410001c00d4224048001560700d000d0710075980300300d0341d8500c145a2500f11281020301400582000c2c0010381200031405e04400403500c071b8640428942080d480c1c21070140c0041d00211049525000d10715076541550311000d40094080b9403c1009080b1540042c0d07440480744502007200100380c0301c004296000b40309549065421030307000d00080c6042c1c00307001c00500380e440c072041c04205484004010705c4481b9444d000d0b401c9040e10b030000700b40c503414400d0021000140c0c6183d80580d000c400940804028000107000314030500c00507803184c04800e2030a085040146115001c0d9200000700944a0400d40400e04031003010032103901410317502c140706a010702001d1984c8100b80300d00802e200403da40a2100e0080310710b15644003104498103048c080c2030390801140505081440301c21084c883c03a0040e00c400d400c040d035031541e40441684501181e051a00d01c0764138180c01981503410403a958004001982403103200100314914070704545c02a0090080d0301180 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 189093776 1250 189092526 189092537
    0x1051006031b1b1a091903020309010507061d060f061c06180203070f05041119030e0102040f09021206030f060c0703090f0e0405010e061006230310080105090a03090501 74
    0x1298241000300c01040c1da031303820000b003400040b08900c40d035142100556010949102d416110001e04083e0940381803200d5041d405107140241030380046465800c031500c181c4005581e40040c40082e003014600d80b01c107480c00350140c041e5240211103013007200401441d56019904a4401103040e0150f001098000b0b075104000080700710708000c0b2040c3e41d49004600a40501c103008010035003025000401e005c81d4812182070042c5a401902c080c02c034020304030341e624201c100341c0752079184038066000881c0c0b46500308001810300c0d175100800c8007001d00c56480702058650005964808403003440751140e101005400038001440c0d0707401c0b816502d00d40280706141c02e03803000c0394480030036110b80c20120003040d0b000032580c0c4a50300d4410745117a10800780d9007212290b18101800c0b000007000700e05c0d18410200500f41e40d034180e1a0550607501881107070042040030f8203010f00a080d000341c02000e540a0086e40c011101003d0811040b5400c4660242c108002507200103603c20011360b1282c0d043d000d46000f072902 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 189095026 1250 189093776 189093797
    0x303040612110a050705010507020c091614040f0501171317091003020d0c0c0203030901120605040e010c020607020c0f0f01020c03010c030e0c06030606120903040305030c01051006031b 81
    0x18020142c5010390311180300d0000c1e40c0d030f16483e0301c503015011103405940200705946444c42c0c1680e9440345101c65980060311000040d800160000300300020340d4460608020180d014135032040740354016000024480d03d412418801941e00030400074401004610003515410400f000000c0402c6076030b0b00070080d00540b22403840c02c00c0c004094401d04c0c0d0b805001a2214841403c01802940010095881c074501d407105030144540f10f0364614400c0754020b4060b500d801e94220044403080024482050305649440e80007409072501e01c2203d030300340d0900340005414001c1013002030404001410701340c110341c0030508030601903550035104031b4170490450702c91034400e404000613828007400c9030312580d040d442c0014803031241c2e400d038020300241d842c541c040d03554401507c3d082202d50300054880940080c0d0901c0031568a041280217544c004003404110390a0a07601c0d610107107168812084104a65114024400181c0081c21128080e2aa504061190400307408c007a00c01d00c15103900400070000700945 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 189096276 1250 189095026 189095057
    0x121a0d02030307060216020f19060503070513260d0503130204060b0307030e07170a0821010603150b030402030c0f01030f0e030315030f030301030f08120f1f0503030406 74
    0x200d50f0202c0c0d0088007591076040818a40406540c5100142d0007145141084000361800e10150710401482c9507c561b14141855001c40712500000c058078280a400c0201244101c82103407124000c007450981c0c0d19003c941443c0d8420441d400e07404205595000d4040c0040482d000b078142d070b51141710201040010303a21800000e01410156000c0142c2500000904c0207150780754001468101d120030407180e090f555004a10102c050079440f400c41c50300215a04000a00c0c80b4006000001c0c40003140e1442181c01a00c1c04042e000a90042020035901d0400496815a061501c8010144000c4250452500d60003280c0c491003501c8503a8031468600e92000764a030b0282c0d0008800408a45042040c2c0c5000980d09a40c0d510581d19200500e410824041880c503001920304205000038000e107041d6440e56a585018644401007141c00c3e013000c1c400324581040ca5031800344180c0251180c0d119508050b054007250606607101c1c0c4400c26810003081c0803d4400100b00c600301d07001e602d000d0303039820901403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 189097526 1250 189096276 189096283
    0x150403301214090c01090e0907051203041505030f090c0a05041508100e1c1e020a08030403080403030e0c1e010203090d0b0f010605070b0f040f0605070906121a0d0203 73
    0x16020b120780424002486014000000c03418240e4500781c80b00f0017696151144c1a0003020122103010141d80b1400c0c040c00142000e201300210110b07880c0841b82090b494001c6201c1401e13804020400040001c0104440f41800c401c043e900303e0410030142c0342d480304990100e144000345000d014050760b118445141041184100c940c0100300b05002d0319100c0620b69801c0c000344c0302c5a003503a0f40328403032800300411102100c60f01703e0f00030328140c45900244540c114190b65064214842000790b002d00c401000100d000c4500441c0300b42d2099031088600c2c54545805811a055484103824030342c08035003542a1030300d560080380305074202204418180c2d481c02c00101d19500c01c1c0184503070450390030000c4408000c480d40700d2600480240182e44041ea8a40c0740480301c40c02140c902410f0b030b40b90700001c82d22041d450220f164106026000c400c0c0c0c51111602c86c181540d0040c4d81c5000014480701042203513035441205211400c0071040e050060250b440121850008040c0c82644500300543c2400115642003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 189098776 1250 189097526 189097541
    0x31b050a1e0212030c1005090c120a06020315041a030d08090c1903030305070f050f0f09090f1005010e0d0605130f05010204050109060905061204060b1504033012 71
    0x10f01d580f140d081c00a42c0079890b5081015541100d215100d4500220750003400b03010300c41c583c0c600091180d082c00904101240c0c44440c4a24421300920446c2c1d80800e045000951058030042c000f2050b4151000a0000b00d6108503090711088203420001a020381e004a54255481c07080e2615000944510a08500b80000d102c000ba0b80208826016034208070031980c8001241d000ba10108910740d07907050260742c0c000400d84620f00042c01001108000c18421000d80314071004c2581081c140403064010800200098502d889214207600c2082207010010030360320064407080c0b8048810a052101264000c0b00440b0b00810482c3c548000602101b140b1000c5080c89800c101c4010303440500e0b007810783c000e510900856002420541010074028080c8208908407800070f05800e2400500b1031b040840e0314000f4008031013541d11130350311038400da40c0c000391075442c9100d04c80c42541e11480d45c0340104080c020050b002c1006030040ea40c116141060100320101c15240703081003090807000580040044c10403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 189100026 1250 189098776 189098779
    0x203190c12110c0a06090b1e0a0510090501030303020702120118060b030a080a18050f100e040b27100302090c0d02070b01090506010f020604120c0302070f12031b050a1e02 75
    0x1c4888844c00d000b915040500b03a2801342c2120405611180e100c6140d0428078600102003000401c08515102d6040e840541c0c41020321211a64035a03d0f40c45810660b40d00382c0c42940026000f141f001c00350f1401402070340c0600c178590020490540d9100030a00c2200c4d0041003e840c240d500c0401c05201c1d102407240041c810341c06400290741d203000040240188810704c0071800780c654040004105400c0c032080107590800c0081c81081c4001042004940414144d854180c11a0301c070000604561a540d4446912070010b840c000c560302101e00c01561748480c01052540c40b40e0f1400c07420409a12142c0400760030408904807130340c0d47c42c20005114040e204151008110a00100001986c03a00951003d409500700b41c1c1c0d032450007d14580100d139100401d0304e02401da14036818460521501603242c03075000d248640140c2c2c00c07183da19200208008015440764034075a5900d1807041c105a484098410708600c2c80d144481c4840c03c9884840e601c0c0b10703050b401402d01c5444120a00310b0f04244843e02600c650 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 189101276 1250 189100026 189100033
    0x2010f06080c22020a11060108010e060408071a0406062d0b03101d0109050603030702010207140a0506040806070e030a030207060503060f030f0d1409010c080f07150203190c12110c 79
    0x12400700506c0e1152070181035070a0702808001041c03a0006004510a81c400c03440200721507241d5445240d0981d02c0490100c0b00110109403400c14130004909440c403803405200e0000d00c45141402003030075104402c10080801c1003081a0201c90080d114000056410715407005490b50b0b9001c003504960f40e00c60304500c40050480e84045801444480b10605a80d08014103010503141c4030213040c1c0d28025504005e025800c003074410700003445000100e105e0414000c0114204503614000301e11b45501681250806070401d200704800d00303130400d400807030b00c00c4154000c243c64011070728000d4032911207010b42003c1050002c04a030f0b06503a1504000040b80f00101074480c007801000e066660380c104096842c01042003000c2041080c110541520403850041c0c4451102ca059642c40780890307448481c0b2220350050030f02ca800081511024002495070f4034070700040c1d9a0a20094011060036418001d0b001c4034180800401030ba58007040200c0035202200000c5500c802014a44e0303081c1c0100c1c07030310408600c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 189102526 1250 189101276 189101287
    0x122814070902091804030e0915130b040e060103080316090306140a0506090c0f090415080a2604061b02060a02030a08150a050108041401050708010602010f06080c2202 73
    0x148103500404020720215070700c1c0703160440081031555005044174060049a89030034031000741e00709490365581c0300403a8141607690100003000159515000017003201d0b950f80d612001046400c2c98484c51403031030541d01c0241500e40c9180e44000040c8030040c8503102da0302a01e950300d942c250090088402541c0d0210013400700700309038103070700a0308d803030803140160302074240800b15555040c041c0302280500302c8008000c0c900b0b00c10001e11400d41d8400401c951f041075440302c0000302c9071010030080014050440241c0304507242400d00c00f442040b09c640e008101540303419055804039050080b601103d000c0c3c2404d003100c0b6031401017543c52807000000a50081e0000030b0000602c1e901000400300b01c101500c58580b20384452203240c9560484480560f0402d00c007820520056018840c9c0a921a10642071603a6080d0b030703d1140ca081d07800540f144404209010010b001e40d83e0280140101203403504020400c0b03505e844500c1c3c1d901d00b030070403030940119074451010140442d035940342c0450f03518420003550744a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 189103776 1250 189102526 189102539
    0x180302100c0b1605040501032c0f10050601020a060911100207051c0b010603021e0703080618041101050c010f1e1506140f04030210020c12281407 64
    0x7203048840031152014030000150948001001c400c0140c54a07645450a06003003500540c001c001c0c0d03040c04c1c0e00d43d549414242841241c8845840c207103001102c00343c045542004100f0303180c061540102d500447c1000200305103660300192151403160000e00c00320300c0002e9810071004050420003500d41020040f21108101900001c000048400c2500c88403048a40d0f5044c100c48241e0b0704c4001881d9800c903c0c0100035046c8260007a0062403644070503102d032604c1207005007610740c0c444c1c041103020494210170403480c0d1600c10342410310280c080340d0400d420300d01039403000941121310035400d061090106500341c1c001825403200c1c185402c03106041022088000c148038078048402810300006051407642c6d11446440c6001108541147d104c8582e4074103030881159681e002800444a10203080c480000540e440f182d0b140a4186283c001e05003589040052017012407185280c059290302854103034020401c1c099081281a6144801c2360301f403410b03032811144000744042c182d00d03503100329180401e40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 189105026 1250 189103776 189103787
    0x50703060302150c0a080c0c0604031103010b060412061d0304030b010e06010309030909051f0b13080705060d05060414044209020d020307060c0209090303011518030210 74
    0x60342c1c001c95400da0f00e00191402248240320b5a10a07543c103410202c80f5000041c0c1c00c0c00604501103540c420b581c40d00b584880404c1c2c10b82c125600503076500c20745145a032100c0c102803040d4030080e0425031304d241c41d140c24980c1214a20042d424010441c680d2500180c01007503440c0c1010914030340700c0742a039079074565908040d0301c070390820300840001000780408075040358040e10a840b6515816260340d0005845e2480040080c2402030681d00f404000e4040b06a5480308181100042c08140d0700301070310b8003121541d640c00900e8940202146a0000a013800301d6070f1038400b07503006a0442c4801151310350396040800c0c05001303c00350301c2c0040006902840100320200307410384902d01c019031030b00042100c0d00e0304030404440e501104001c60280301811940d10601034203c1c0d18041e00282250302e522038507502127031401c2229400480001d0140c44840300710b142c4202030503000b6052000030750441d410840d5401d039807441002203005004d1010700b20380020164800e01001190020144170807181100f00103005e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 189106276 1250 189105026 189105029
    0x1090609050a020c0601170f070306050a1523040e011418010b1008040f05150703060e1e040f0b04050d090e070207030204020c16080d08010501020a0b0a050705070605070306 76
    0x4840c1010700203980c035030305442a00c0204081800400042e407030320f0780b40414244002015403403401006441200701c4400c0140000039403003040f0002d018545440244200c1d007480c604400c101058620800104410810f20b40343c02d80710610900310b081e10400003400400d428042440c06500f0030b81110300310b02d10524464030030600c2c0304480707a086000103030b21804c8880c0341c40ca00d907101048081d00d0440324421403c0691142c42404107588240007a180c08c2d19000001d84020b822192403c100006c860341400740030700a20100f98100c8450402c460b0b5101000c2d0309400c18944034800c00c00040c24000c5180ca0362209540042c0056645c0c1050709009440da80c01e82c2c200400300c3c0c000b6000141410802c50603610940155020f00069804c41d8200000381d408035407446814441d5100f5042452100146003000b4030142000f800d007a011454080c0070403005901c001e055411441d0644c021400c0324061503400000c02200041039918400161030f2405a8007010b0701d0035140074100050650141c1c081d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 189107526 1250 189106276 189106289
    0xb0c070905130f05030a090b16150b0d0506070906050a020c10020a0f0b04110d02030618032205030105090d0503040303020a020709020d140615090f040605090f01030c060306030c03030806031203010906 88
    0x5100e551100c1403045140301c1c80c00180c428505400c6014080340b6854204009002070300710110b440bc3c0005c1c00030303008948015064841d80c22001c14001c601c0d401c107003050000d1140781440f0b0b00f045c3c000c03880030b5114601c030540c681c050281c51080d00740041c402e1040100c055817022451402e0040c90419004000c011182226500c040041c000c4091804081c0b54041a03030003070051405580b03110780c1e0a4072100b5141c5620a92005111f4244c1c032600c0c01103103000c1c042c0c072203146492592a101c105401d41d00080d01140e855000503002e5080c3d02d0340f080849034011b4040c107015a4881408100324508121540b2803411b031803012512011070200c42c0c02c0700c203c554800344041c8094507000d0070044c48104200424080c8642081403581b103042608428003608c8008000048090b55140401c2400c40b080751075840c10041d0800510411401c99051340152440e883c0c03c000085c00d59503010080d003901d02000d804e0041c20000207210390340812801591200c0e40c0021600c80d655424110043d110b43d00812 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 189108776 1250 189107526 189107537
    0x1060503010f0b04030c0501030b01090b0c21090a0302060a050c03030114100f081305012a022a01080c09030a08090109050306060a140303040b180a0b0c070905130f05030a 75
    0x1484201281c1034a0170760707030009101c01209250000560081508615290510608180c002502003003070001c0c1c00c9000064000e800a01c00910100e107404240e025000f04111041c0038108a546902d071901007031340d074159625540d450042000313845500404002518500c00040041514108840030800c1e1300010317511240116030400c0180e0354003117004070720310025644900007a40601c140341708100c158025000003810b070303d00c20048601201400c41c0641307000d1070b0a00b48412598100305080d5011143e0a00d08a2182001511141080043c12060420202d00003085545803101c0c211420b20b64010100e5840f440e503460001030907000340041901103012500300140e035080c0401c0c5548194802032858800340e081c108050541401d01002c280c0620041c8404506424440010400c1941d9040000c602c1c0207183c040001680741500440d40050f0f042c00421008140081ca140546541100c00304079951842200041c0c940074031805041d0b903982c440d482c01408404002081e03200015542c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 189110026 1250 189108776 189108779
    0x10215130b0105060711010f0908010e03030106171b0a030e0f06040507090218060d15030f12030605010206190e0304030b10050108070f030213030605010306020901030506030d0507030c0206090901060503010f 91
    0xc201c40b6005488001d41b075003074001c0c241103156201c1c0018031082307035440c284644541d4441180304d00b140c001d242180e003183d00000051003015080600040c001210701c10664091510300c0040c994601e155800d018030f1840814400003980c041c2d080040c5450300841250101d120410b00039945034419102030341c0c1406400f0300461010610f0003211840002420f24a680200302c4e42880029031001007002c980f141d0728080685c2d120968280400114051030710540b000801c0d041a0090f01c031a400e00c14141403416004021503600840c800f5808134440c005100c4400d446440500640b240e0101c6403503500000030701008000160320058000e50030000d980206907198070040d244150103507101b4010075a601a1007515078420303002000c0c0c100306101d1040c80a5580d80d0340409071903003038000311903294001c01ca1240742d590601c119984100b049006003804414908058846d204400001d020007280c0301303502c803d5480361700845100c1c15001d80f0701c4481e0740c2d588100902a804c2070180c6100c6030420b600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 189111276 1250 189110026 189110029
    0xc0303230a021e09180c2118190206070f060f15051806101e0507060b0a0b03010506090a0b070303090c081c050a1b210c080304020f010215130b0105 65
    0x16034104540c09402c12925074407211741c5400407a401410000204030030899070058130741100140a4a4819008281ca942002143c80600d54049016032040d42d0149480071040800300070800091070701990034942d10340342800c01401340ba102160242c4001d04046018109040c550f00c4026141050b64a81240b1902c0c0c1d410405d0307011201c0e50480d1300420240202c2c13860b11f40696082d5075000603040560070b00b5502030f080740400c0c003185c65038804100c002c00c100d4240440d42c01707007400040049481c21075071810105004814001802500d0256901007541703e080d071942403500020301402d400040d1900c0c483c0c0381c0103028011081c022650b01e494410001906a80065001c410003001a00042a1405900c044619030049140041008600246d1a217112281c03403041412030b020b100f4007107115100e02d04000d110900c20a090b0100010007000c0e10100e40b80000350798000ba0b04035140d07030850a4000c0100d241007021603e001e100300d02d00d01030002c00360030384002c030094070300c0351640035940e030f0341d420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 189112526 1250 189111276 189111337
    0x50303010611160603020a1101050c04090f2c0106090f020702030d170a090201030603150e0c27090106180c020c10020d11160b18100c0303230a02 64
    0x80b8056090b2401d44428001e130750094010b003c03a80418070f4046542d00399102482d0030b4a006403403001803283c0c0007405000820700740c021451005c1c6410340c24040b050b4984c4540c03880301068844400e900c035034244448804002900598000d08142c402402036522100b010f400075409508101e02c03d1041060b40d11040f030244e0b1081440c2050039a00e0751296844000000c00b03455440306c1241096515600440020420507a02000000e458400540c14200311a0305180802c5e02d01c005114514034003824904060100c0b0444081c400d242c42c03401c007901e600d20700728090b00d0b580d000711078858042a1440c0c801c503442d900901820407182e013183d2040c00c410050105012142d8441001a0060f00d0214015402a281c0c1080c41460038102d4002001c0402004518411504040340c011000900852000031031060380350703074031421500ca41d031803203000201a00240501c10024140744e03c5d11381c152000c440044c41c0c002400105181c0000c03070b1034482200c10095000000d84000d00c070002224a41000808 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 189113776 1250 189112526 189112543
    0x100206060607110d0f0302010209210c1201020d0504030f0311040303090b0313061b031401050a1503020c10020d0c030605030706050f1303240207050c0409050f0604050303010611 78
    0x900018074085040d11082d007040380b030120040e0050383e406040c4000584542289170104d01aa00040e110030003130040101840c00f10082483c10440c0f504900c81d5240046030740854484201c550031200e0928005182c0a400b625810301342e01c600d000e0400c400d141c0c01280101c41602180d0f420402000f80e521082c03000c0c055800041c0000d0022481802410030903801190445004020122207800b1980c070f41d015603240303100c000e40660070030b58030207100c40d094000c0d04500341e0040711160f850340c180b8003ca03080b44c03083c1c45030100008004020b00c1c03426000b42c3c1202c01901c0050141d03500c58103602151400f81d4801542ca02009144c8200341e1740c0740b80302c1d01c216015180d00070007620b00c031441e114088500d604201c500001c03902c001c1110401600e154070320781d00110702c41c942a1000300111740b83c1c2140301c032001c1070560310140104000c500050012406a0382032100707c400050816042c1491440c005241140d84d81c035100d603400b44030901030000b018604075201540e0301c5640ea6040c5001d140c552208 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 189115026 1250 189113776 189113779
    0x140f1207030e010e0901060509191508130b0708150603040309030212120c1005090a05030d05070522050306100302010903020402030a0207082d0901080417040b0a02060610020606 78
    0x600c4824000391160803a04907a00741450008041e0800600042e0204821303480304021a00000c2d49890350b084c020860050340b00c000788403540031460010060072009050202d4000c004525001412480c414140280e8040d00080b00d05100d20f132a180240c40c51500f40c40d100354141440504074128030708203041341c1c41075925540b034032038052840c1c2c02d11002a0500d0f0340d0410b0340c060014441982c03c540809000106180c0000384540d50314002c007070044403000f0700040d44a0300020843c00100e900041240c41c400d01c0164005402c2e981c001c0102e41d04d00880041100002148001d0b00003500095040c80695100300c0558100d07888201000402c0022031200078045045108100090700d020390145a00c003800c208090b00d407a0141d51500c1c3c03e81d00000c400d01200c0d0030200358103809569001d5605403002c2c16075182d8601118580003a1980380e00410003044c0d449081c0c400740c0d0a40c4030310241d5000340706003e40da5494403803c040c082d403a20011540d660044c0b854040e0402001c2c800100203018140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 189116276 1250 189115026 189115063
    0x603050a0209070207180f0501050a03032a0213091101050316080a0207080c0d02100b150c0c060301120302100c05030115030e0a0308070e040510060c0609050703140f 73
    0xa56402e00010724001032a503400e50240303030f42c0011000600c8030802541c802c510700010f5403280741c2020108950042e080785010348070a80041c00066000803203490700c8446551850100c2c4400459552a0086240002c0d00145202062090641d80383c00507404640b25034407000b042c0302d248004440900045038a80da0700c1003132040c000c0034640150552070b0000b01041c0003500d400321580b55405658000384641c03201d0360140402c640407036418414010b03080201e5806108040750a0001504581c520382c10310300654001860314005c0074200014404040050101034680d80c1d0b40e42040144900c8000c181e0140c00381da1841c218240d403512406904107016102c1c0d1703003541d08001202d1212140c1190900c1419505d10144188650401488044620a6031451000d14002c003000b030408a100400a0103503042005001005044181d0380041d1245440c00c2d59031513050303040c180013078a43c004014001c2e025801012007403103c0c2c0070380a9206c80312181200c05c00d01420260a64607941240c00c04180c04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 189117526 1250 189116276 189116293
    0x7030903020606120a05030408030319090809090c130902030901140f01060c08040b0403060c030f0902010c110f060301080a170a02060402192402120705070b0f0f0f0702040f060305 79
    0x80e292a0042c4400390a008851030305c04a59609407a41e400390300300170516403000c41048125021072003148100402c1c20170601c0503c3c617580d607400039805003500461082100e8030000d0459410300301900c40042d800703031400390107541d2050200025403050740c80c581e1355420118241e04a40d40241d290b4086c001902e28030507581e20b815001c850f010440c44048503418410040022400d1410b0003800223140030f04000551040c0c46a0081c040711500010044418244502403000d42e82181b02c0d004515040749401480c0f480c0c40000070011610107040607032061020001080c00d2000141a0300036a2250061f1200f05050184603030090041d030000d90010303405440041c00504148078940d41c042510029242c0940d21113403000085407200008000e000500d99106101030f40c10800d15050a43c40c400041c42c0000300e80f00e080e2a401c00d4016102d2407000040e00d41030302808002201c400b494407184942d120303e040c240514695100800c02e902c500d0a010056006980c00e00c0b4450072260321000510f40c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 189118776 1250 189117526 189117529
    0xc060304060e01091b0801050601090303021c0908100203090106061b1509080c060601080c13050904020f03010c08070e030d0504060309030e120705040e0c0a06110703080f03040b07030903020606 85
    0x60984420102e119521482041c0006032074800b200c001c1d8000080c0c1c3c0f0140d5050521280c00c5402c02044141040300485007000880e4000c10b0000100480b0251070b0391001c120f5000790f80c0d12245500c521428410703c00c50801c0c1c0740140c0c2c0994001da007100000c0c00302a9455034215803200b4021024854840e031410000e00040741007510803203014102c60081170190f0503817510072003908603200c25a0590018410041c80b50b9004d40425482104070050900b000000a03006420711800e000300c5010780807a60224080d96142c4506004101c1d004009002251380e4a10060046034151048404100900d43c41f60042c07401007401010200b031613889500745890903004501a00ba501c034180d0512004074044041512807401c15502c02c1103490003000f91504c0d100900c8200c6607400542056504442da0103c41c03a035980000000305d40725031401483c50308449208600702880f42d40010230030180084c40800c00303041e01c800342d4030490282860480315520010268261540b1500040040e007088000030043e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 189120026 1250 189118776 189118781
    0x201110405100804110a1409090a0312110d090503040f08030406020c1e030601060207061b0b070e0612070206010501030605030a020f0418050a0501020c01051f060804171b0105090c06030406 83
    0x418060f0003040745c14401d25011806241d0180c0120741c851085d0541000d4506000d041180c001c00c0c41401012203c0e190780f0300600c607480031000c0301895601c0c1d05e00d402c1ea0300b10b44000d0b9104144007450401102461b8030300583d80c3d50181c8103100840c800d049001880a8000c01036804071602e0790050515040880d04000700441d80b814252200d24014101c61075a442c00c10036540a81026001007160303600307112000e000c400764000444815440003542c0340000ea0007007200c542144003400c081c4088001000040e18a0182502c8070018081c01c50070402e03407950000b602c5e4120b85081e20100902030719441415110720030150007a412000500b01c1750480c2c01c25600c050100000340003070504e447c285ea0746403814144059001d881981d00401c0c007000c3c80b00c081c42141d0b0040d5402c055151040c0e180360285082044c03520680c0d050141403000074090044e01c3c10081585042035072200d03030700d010a841075182c0b09000303c100c07640e540c85d10000480582001032200300d0440000c100504658580d50b40302c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 189121276 1250 189120026 189120031
    0x60e0a060e0a03020a062007030305150f030a080f0c060a0b09010609060f08060609100804020a0e04020310020a020c04050415060905071d13090b090d08040305120601230a02011104051008 82
    0x41c0c00403141c40d901d03228110b07c00340c08020301ca59000305180c00c201c00000325032400c90000503c100c5640580310001c0e60002000c03150a90b000444a480c2c1460400b100c2050103075020300c1005000d41c0c02045100f43c410303480007000f1001115902c5142e40c0305e11080300c4003581c80c0160300110349070940f4101094055041c036540034000610f49444e00c006903010400f88405100d07160b0105129000340710861506c00c0042c005000080e81090f1545055000240d07100171101c55035440c0783c0c0c00211f03440381900c00d011006c00c0800162040c0300301d08280c40c002a14201c8002680007546c50010301040540c1d50b402002e001d1301c12603403002d83c500f41400b855200006890303d480d43c840c00817001d026100f100c0d0300030502080e026009a1108c4e14100075101c0c00c0520400050040000460070400060782080594111036445039500809070307103a50050310700c1d00c0c4031850100c0c6500088e5181940b00c0c5154010003400002d0750092203004030261403400d03e07001e01e019943c0d02c652802c1d1400180c1748070701c40d0700f903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 189122526 1250 189121276 189121301
    0xc04030311070f1403300a0306091805010b0d20010203130b0712020c090f06040b0a090f0f06050d06021309020c011512030c0605070507060e0a060e0a03020a06 70
    0x15003081c2c0d10782c00c8115603e1507610030b05440c0d0812404843ca45000d020710500d60311b1280c0d40d4001c0461318410040c0000c503403454440b04030808512804907512986c4040080d00e081700003000704002c8200c080d1284030881d0011521582441c94440c1603081840000c0c0c2c0310303a4032182e843d040794518080c50440b0748443c2000d44c110711003170103007213418095403142100030810240b0207030743c880c1581080c800ba060025455410343d800520310701e08a4172000d404a51003076a40c06811900e8407241e0006000d4243c8400d29a030012500700c000c1600300440d408565400c204500400c681004001e685007520749174861160301c8541400e140b030116035280c00500a43c802d108804210701d80f030300c03581c1d8100d80201c400309159039500c06203a001280220481e5000c1c220284044410003040d42c6c004003d04215071004100503100c901017042140100c090300c0c200b40d408a001d001001d01c010032142c0d42c10394408299040f50800c01c0c620080030010138a8016150154082d00c1c10044944514002e01501034410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 189123776 1250 189122526 189122533
    0x90a0c050f030123030f03090904080412030e1c0203061620060601080a02120a0917210105010c0506040f0f021807020106060e10230301030503040812030c04030311 72
    0x1036158400050042d07010300808007070901a80110680e280b00408010040c0b4081d5004032810708094200105076004984122691354090780c980c6803042c4180035586c800003c100c40c0d8442c090415412a41600c1401000d60364014241c0c03c04e00c10f02c50301e01c4042c42c065015006440030030190010102c00003401c1d01607090000a141d0000c0d107110207160f07200b403051526040101404641d41c1c2c81402c40c3d811004016007941807006d49241c10311169005072030043c3c06984e8503511001c0081c00b200d41560700c881c2840042d01d03808040307100c00b03000d000a008021007190050001c1407960103020301c45c82503600500207200030740d65943d4901007200340b8501521581c02c880c8a10b03005030341d1423095140026410350780003114100a000682550641d8001c2c07400d002d104070445030385c2c2c1c488001503158100c02e854144c09090104241122498080b601d8040ccc40700000004400d02c90004010411981d00104813410f80007542420134050005540100c0818420801040881c3c030601c6600c0c0c500d80c42106a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 189125026 1250 189123776 189123787
    0xf0b09060702180708060103200306031608010f1d06010314070f170c010f05030c0f0c1002071505010e0622090c05041503021f0909090501051005010e090a0c05 70
    0x202200d8024200f000c06100c039100300400940c0c04000150803001c00c2c2404d011900380004114022070354400c0700300c0c03000030100005120ba42c003086401c2a44503203d14560007141c950138414003030680540c5000000b0f044c000c0c010750300000111400c4000800901501c1c1d540d00795910344a409405541400003481500700c0440c0d004d5507004154000c0450040c55481201505032160805514001590601104994040010b80c005007101d0380001b541d51642c1c0d0fa100a802a0240d40c0a0060751f844507228000c0a60030703000f084c0d402045d0f035038085c11780450070440124001e0281c620034040c041c1d008001c0c8010556078103103102e1291003a26040980b08c5a41600003c4208540800c902560044500c0400704424103183c455844803e40c81d48210090a0550300401c9900c582c0350440c5068130004041069141d10480700d8102420007244144110001030400d5030191a080e690345000500182d00022150700a0074000d0940c60040c01d00100d5946140305103000304601060b0805200c1c04010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 189126276 1250 189125026 189125029
    0x50105130906180b04020c0a0605060303040e1807080d090506070204020702100c020a0506090d08030402030705060a0f030537020d090c0305070806130f080403020a0e06030609070f0b09060702 84
    0x164001411070016010301c0c5000e0000390f03a0070340d04c10b000c540f0301a0703204110440e6185804592801059008540440c241c3c640754082840c5d8441c035401440b21b44500700900661151741d140c1c0400c2441d003c0c0488480c6030319281e08648070701d1140124004640f0303541c030407c02070500c1d50103030a005000900040c20105660081080180601c12900001c0c880001d04c0c0110319020010030040d150680d245c42c2405e40342d40110f809a400113202401402c00840000c08550341040004090480500059126052282c003e41040a10380c0d424011a0034100080c0c510811103c0d55105030b108140c40c000154400c448030348000e42c0d0414216002e030380070007004603807000034041c80c17071058032a000b0740c204180780d400c0c00f900b01a0680c000d80c134150000001c1c41711040846500054841d00640700310407824451416100500c1503174402504510011400502c0b4031140304201e03c15001982035903616030383c00c030754151140e1513070086444e404c030482401e0141c1c51401d07000c0c181094001c1c20301442d211040c2c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 189127526 1250 189126276 189126281
    0x6110a080c03130b0406023406050a03180c09020310050a0b0714070e040209070306091a040509060702100b0d0204060902041802181005070f031e0503010308040501051309 75
    0x28904800b6400052075200c4658400e030071000404007841d0130780c242070400c00001d441d1413000c2d100c0c02c1907414602d40030340d0b000e410b03000d48503403081010860b010f901d5850070050031581001031342201180c90702c18598110200a41551607403540b042e404416a410030100720001e4101030314030041c0f5100c03d400440c850321364501c1c2d000a032029032125900c555140c6070243c9a07182064030080a900070600401043c104001c00a4002c0d41c1200c030b0400c29903480604500410450b88041905400c020305520010785101c80e1081203038050740c1c180a1540c4c1e2554142e52007109440160060307100b41c100c5000110254003107110584020903500000401c0d800050507034001d5045800e01d01d60008080196920884a140440340600015800c0c1030f00d04c072103144540c64805140d030090180c1107484c509184070700c08a8182d0355100e850300c40e081c1d44505000b01607035840111000664a4500d0441c20140140c003038a048aa003d801546042d09000c01140c031034000c4032506144c922102008901100b460 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 189128776 1250 189127526 189127537
    0x90f07110a140f03040806060103020a0210060303031406011e03020306150c06011e180b28150c1e03110a15050a0b060702040b06040f03030201290a06110a08 69
    0x3140e22220403440e0349441070a03c0c1c441c06400d0800e41c4100800c01410030b02068040e170140c401d00300140c8a0340c214105034100700c0c010341d07854101c9240c00404010940c169001c100c004d270800a03004550390361a030040d80c1121040340341017460140c801e110a020345c4280c0003158042001f034a0611016441003040030160480010f07000581c02c000c00500842c090720607800f131405d801c0c041103100c2c5440c10700b01c182003025402600101d03a031544000344c203507100d41079901c2d800e540c0482c4504e1087c0da04000c0d180003050600503940e840320603007020025140f0620b5001e07100ca40021340150078011514070140000701114048003401490503011212031818040045a0760280c1610068510143c456100b110001407440f01c0c440d1811002020a443e2041035500c00f0358165000100018040002800ba01966001c00d045d240041408002c065043d00007600b9640640020400d5044120b80e40700440b17a00004250020000d800404c0440d10500740c00400139401e4040c2c0b03118660589440b051903001c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 189130026 1250 189128776 189128783
    0x140c1002010212060a05130507170703092112050907050d0f0b0601230a0c08160203210712030e010c03050601080609010305060a0b04140f0106090b0702090f07110a 72
    0x4550101c0f410410715009500c010100c4060000a003000b00050b0101100c0e1f00c3c1c400000e56410010b000d0300e00078040858190310126502809144c0410300a002d05150941291907508000f130700150005403070384100e500720403611212813002d440e211103801000700406001881c032503c04009100d072070f05140c5200c150b00803a40691001e9540c14007041400d80a004d090400c241d05141010310448100300b64030078540e0609040d504c10343d42100f1a003034000020083c00d48a80061103014801081c034006c00d20f40d1081c0c05842d1048204600030000d01d51155031078413003000401410700080c42c1e01004400d003420350b041c00505014545600c9003142d042e0304106010a0742c400c240601340d85c03c00300301540110200d80050340341d03066a9409407104005001c107001e29444504651488d60b0300d42000c0614581a4403501301480c00c0030700780241450a03c0303880c0100300005004549104020111410150080c1a00111b230f107a010760100c40400041c40c650407c1b072140b0200301024028404d5000c2c0502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 189131276 1250 189130026 189130031
    0x50f030f0f0c040e070f020a0c090c0f0903020a0b03100321030f05060112051914100f03051f021b011a060c1213030804080105010612020405030a140c100201 69
    0x41c5040764120005000d803060b52500c10521003040341d0071441071220f92010140c60051001401c98806a1505c840403a00400c0340758114004980f031000c1d5880a860505169681d9900310300e040ca05640b640d16901002e9000040300e0001c0c0260303000d110081d034108204540a0b40003a0f925118038159980c100e58a5220710403c1e10700412143d4540603c20480c0c10055080213642480e00010b041806180207070390200f52070340300060081030300c0c1d80b140107041150101800b6041500400301030910342214000104400c00c030001c5500e00b5a9911102603a40c0040109003c009011603005413440c0b071140384800d903800f0481c60400e5032551160203003200401d000401c1e0034448500b0b1100c84150031840303c2c01a03070103010b9440350510024544414000707c509442d6907900d08034010403034101680000c2c0c132003000014001808101580b2480c101c0d15250b98000c00800b0794079030902684218400c20754950300c81a001e5002c112040061134203003600d10110b803620040707034010400c904d103004507950140c2d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 189132526 1250 189131276 189131281
    0x230d06020904060e150d0204020c1e0105090a03020304170705040e0606040b190b090409060524010207030c09020306040e100b0a081c110703241d03090d03050f030f 72
    0x182400b804004d0191015506550b15100c007034110304170300780148140b041034004960b2065444a904458901c041d01c01035a20518010f05900000081240850300d150301e004005801e802d0007160f44c42d165540760380035501c2d1030724000208541c0ca001d800190254000e1810001c3e99580b244207510041c5204005800b043c82e0040c200021107034407a0041c5d00039403040712980d803150f10b24000b14080e0340005095548807805000418000c00d85541c3c004c1c000c916040a0001e0a84c0d1020f0710b142c4950302d41d00c2d80181c0e001c2e071001240c9032502440000d001d4041d0f10f8052184803030301d401a5500440c0075000045840390100510701e0500156041e5220540d5401030701c000d070a20011280241200308014408100c0c00b00c0000700c7ea4244800d1041003122603418070101038028001c0300020360308030401300d0031128030944400b41c800e0040f040c00c00da07918001684402d05040a10405400041c5002c3c50814a4001c140b06070030400e1030301202080810031050104021190103540140d00080804e10b02c0d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 189133776 1250 189132526 189132529
    0x1603020d08090c0d0c0329010b070b04030e01020a050a0c08011d030d05070504030f03090e0604050f040803061909150602030c070909080c03180405150a230d060209 72
    0x14149034808100720140c010421000310002d4070450910058500103401c84150420035400081c030b800003000300f160112140e2440345c803000f004440c0c14100b0b20340c03891640d0300d42c1088814421040c0c01403003080b580e400100070a00400c61000b1134101801039890750055a0350341414030b60904011540f01c1c0307454100b407002000034880c481c80c0103030615060340c0c0080b1440031143d4030301492840c2003540740c8410020f1010f910603429134005552002d5810841a820f00c0c02800180c990300a01e40c2c3c03411090f0024555203024014140940348540c4103143c95120f98540c0030303081d40014009508100008443c0c030940f0306403012840203084059000030001801c0b40c00d048001080c0c1c2c09042154418031036000c8695012070340340c04454400700700040030303601440d0082e214000c00700c1209903400042010048050424800803248800316000c0240340c4c0d030321008114002c03003510314036001010850280002045c1050003120300310034600105200c4541c200066000203009400c42d81c168020031100401d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 189135026 1250 189133776 189133783
    0x9030d09030606060e330f211302010807031e0902190317030417030708060a051e011202160f051005070e2106011217030702030a050a0311160302 64
    0x40c01052074104071149901d0700040d816a4100e60a400010161106c00304151031081e0768040740910442c8251940c8030680007642c41d8200740c200311701054030103d008074210070426109100300d950343d006036200300e0540c00444134444010030040500da92500032206501d004a140d007103401441e0702c0030980440754814400000e10302da00c09c0052400f422070900009a11982002174801d84241043d00c0b0782c2c590070916247d030081004020721203000001d00044070fa2100345140300c1e44040e1000010581c3d40d80074071001040c001c1c07203e800020f000801c20101d6104007003800082c2440040075003031141440300c0c0c407258014008200c516441819007a41040803c0c0005c6444910103041040a8604003001030100d59180047c1c1c0c0c41103441000300740e1040d000001c42a182580c10048403032641c0c440d08030000c544141b40302039071900c040c07a45510030646140100c0740301d0811580551b081407038041c070940385600701c0b2503100181030b10384c40c1300e101e0421210040c0480d41f100f030302d80303011018140c20060308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 189136276 1250 189135026 189135029
    0x5151309140c010c02120a020a030803091908030c09060910080f10030b180f12041a030c09040e0715030b0a060315060f030e0307050106030b060d0b0a0504030509030d09030606 77
    0x403680c0011511020300d0784c01070a40c00d010342e019510000000d584d1000c65040a2074060001d500200919011080c4040c68010703612070a0100102d0317104000d840c9056003a503168200061000400f000091840c0b00141c3c0507010404016164904200900000a503444002207000300015044410032854890143d400c60300407150b064140c29040c1103489100c2140c600070b0480040084126200c0341d102c0080202d06c00c488072003020751340e4502501d2280c100301c0d4002e2003001e440745540115010003405604c1141d024414503041c65252202000510005d050a82c001305c00d0380c0600d0f0800101c400d00640310f0b510000f0140c2d00020079606080800c100b5524940101041600e004040300c0f04991160400040c2c80241c200742c03400b02500c1c00308501510040c1d84007011400045003050400005402c50001d40c0c1c45803007141110303900e4609105400e044141c0103441d010305071004c80c428800c1682700d540c02c213000e490030301c2c030384250b400c0441d00c4c06044400f9000050380c82d80007042441010700c0b030b420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 189137526 1250 189136276 189136313
    0x12010902010f1119080d05090a0b07020102040b0405040924021309091212060503010911040c02010507020a0303180b0411040b030f0a02120712080403050f06070507030305151309 78
    0x1c1c428043d100000b84e842690b04d40101401c83c900d1641014041d0120a50b00600b42d00801800249030050308c0030f03210f2010000c1104c1102d81c40020500711790040c002d81d010b583e159070001e800c10307203014200300c06002000800d440000200c190404800c0010b003260a00240941001d03903a1506180b0101e88104240e0080a00701d1415160800090442d190042018850b00d00881c00c10541d0500318001c21040c1e10807a81586031504400400131940507440d21850b0450b010030812403581c609a098074802c039000300c016041000b0803000030307010354440d0b06440054420201c0b005402d5440240a0300d040d201a10030150403c840e00f810300d001d0051107801c5e241580500440200801d00c695036058125000f80314403484064954080f404100700c8001308102d142100220503107082456481e03109000a541c94007603441c030b0101840c4001801400740307010b662039134609005910308400800b00a0940018a420303510340910660ba295201100801d4004d00051000c01610b0b00d8810b840741884140c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 189138776 1250 189137526 189137537
    0xa09050a0302060304060207030e0a09060315060e0f071e050318160b0c011404120809060103080304060218041b270504091e26030906150a0512010902010f 68
    0xe1006880f184103598004ea070003c1e004d41ca07210140707130590b08175408454164000c2d0700b922000030545071a400038404c44c0c0c003880020f6008801a00d40d403094030f00602402d403601d158580480d858140c0041040c0c4d00c04400d18101c5c000240340c030b01c01d00f211140241e03d80c0c0011808400d0010354192014140c5082128800411141d100e51320085222940b5100b140b159000110360f9821f03226080d0030500c440c55035807500503518038181ca040b000030300094071800d0000b0140d00004580d0000054080d05903508100c5d800c0c29a074555464070040e6101d0b0f0311540e20700b40800318640e0107031158047d81d00c600420641c1c40d12140c1484e113005111018804038460501c1d00522100c841141c504059000c1d00c00940c1e004c201c00b01982001703d41c80d03000d161503900d50f80004011905000c0501c4081c41380e002e982e80700500341c40a10030001414001542c0b81d003150f400c800b0219131150305250981c29603410241c213410400c0d07a104002090342444085d4010940d45a5200d8000c541c3e0104403841045440d0400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 189140026 1250 189138776 189138779
    0x120a0b10020102210907050a0312090506070b04020607020d0210020a140d080c0c071802120c0403050309040c110a0605040b0901020c1e01021209150105011d010e120f030a09050a 78
    0x289011034041e1480c1c294640e6a40200d04503403001e0001b1806002c000e0410608507507213280c0305440c00b400c3c10001c0000340c41c1d0b04c004a507616280c003c403012550000c0300c8540d152181d4080240c02ea114420490303000c02c08a8022005031210350100080241640150080030454204000c04440c41070200740a908001c2c2400416034202d02c035036811603d4207414648805004280c0783c549031940d04810b000c80d1151500c044100d05940040130300b0034801900c0072050725803c0b01c020507405207000040583e0820701c882d100c10b04059000b031410241c04d00d40f01204000c1e42d040380d030030504099000d0380c02c1500d07041000203208158070b0701c64000b803100000710b10b00304440861a8035400f6078541181911100c0642607030881094040e00c0364482201c4001e2000d007411102190360b01c5001c90404c6640c0642400010303650701480d15090440c458400c0129042448801180e0541480380266030000001c40740c06000d40702086030b140c401c0d0886004650341c0540101c0070b400c4656a170303c41072240f802d01030b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 189141276 1250 189140026 189140047
    0x105090d150f060f150302120a090c0b031806091615021002030a090308090601050f040c11030c0304030201081501051206010c0f05061905040b06060a05120a0b10020102 74
    0x208820041d00401d201068484004250016292020181060300c0c201000070401030041e1141c20101e40c80d11400c5088911030041c20f600307038055810904100e00c10b20000030600c4149410621140d8070a844603019aa1240c2d0301400e00e030000c0e01c10750024400e4501088840400f080300c80e400842d071200902050711413100c1011074940900550700140b040640d40184140200040795282c50b03000015500e9140182000c0c00404500368164001084840882c02e59000031443c070341642d201a0840d00703078005900500c40035000d10495503080100c00c4c0c0c24035044034414009403031408501c4c006940c0e294514000140800700207006100f46102d0000103e40c0e980c2c002c03045a100d1814034406031056562040185c85200c1c04c020042c00142d40d40040174100304000c517030780d4452480b100d8888130045040c50030004945080320028206444000880c0480c81c081001e440d0003026460518a4580700e1800100c10100075500c84144903140c181202c00c03403038038611242e641002803000f141007004028 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 189142526 1250 189141276 189141289
    0xe06010f0801020c0c10090317030402130b130b15040306060302040c0f0e010309020a0803070302061b0408070302120106050a0e06130c02030d0c09090207140d0509150a0302070609140c010509 84
    0x4170261081401a02d51079010b0b004043d0b00c0011504003c00010303200d0006c403c08881d600850f001c9100e500070319803117811225240f1500c142c071134010304400031510110001c1d40040c171800d000341c0e6102050b1070300b125960303950750001e1001d50702c00c28000c101c0310300d5841400305484020b5903900a1100312076540d000180e104840c105090400d1a011600300018004914070301a0380d0010fa6482c0000121101815000240140140508100031214400d141c81c0e201ca54051809042c0c00c50f0480c1004002526111845070101b9072424000180c0c1036032003000800038450b83c2d015003050401c0c1d0042000e10f15007407050258489154209100c0241541e01c001d440c0d04c039081e18206995604d07400c40710968400c0d08400d020700400c4004651380c001d01d0818194407540380c4988040c03489110b4078140b415220744255498060060111103681d0328800c0c0d0076940342c02c0050780700101070b828040f0a0108542e4000c40d50154021714552030300d007060b14866802d000c09403001c28181b000402c0324003041e44600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 189143776 1250 189142526 189142543
    0x10e0d11070902190e0f04110702090108060c0703030e0102090904031805010905011205070e03030a05091f08070503070c020a0e0103020102060a05010f091a0a0e0105010f020d020318030a060e06010f0801020c 91
    0x5207022615070031072170006501e050644c210150440d29200001e0740320b24102c4001d098040c000c407522003583c2c1c1e80d8080c1c0d036a00c88045460202d0340c6028040480041c5c020340108104a8903100054104000c9501040c5140702c01c55068000690500c03030782d0441009140c50070042d1400b0f181610340b00e401d040000c1c0240f000034110301c0c01e00d9960070001e1529445988c00001444000b002c2e2507880c0c0500000415907000868114840c10b10304030304c403a0940d60480f2902d00c101107a20307030302178607a5483c00075182500006d0400701480310b10000c1c074006a85200490000c3c001c030003207883d003d506500009140c070000901994929141c2001445002c010451501c200ea4068201003000501d4507584c0c0d00050400e150aa0450100070000c100156459021070688030280d854510a050144040b070369811044245d40243e0410444459030800c4440031691440001d400c03a1040c00c0360382e503054104d079016600d6840c5500130000601c0030221a80706240200076100086d41403050341074485840700101e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 189145026 1250 189143776 189143827
    0x70906020f06010b0a0309020a18060608011d130b010902040f0e0403021b0105090909060103140d0503010311010c0b0a0c030c1103030105090612100204051f0818010e0d11070902 78
    0x32917245c891030b1080d08044007181d03010700366200003540d44060420200800c4c41d405100c038200800841d259120310184d6040361946407400c61150381a51b4225642c00025050701884480c0f005403101250000c2d800b00e00a003106000140d50303c1c5420440030b481011600415169500c40045c040883d0380069100d5140240d40003541400c01c0080040e10f09101c3d600e20700c3d400641d14020482484c4020401c107040b2400f60001e94002da100300345443e1a20700c802e000c000410024001031020800d04410280d481c80181080d22207001c40da201e0350f03462482120380340600b43e128501100700690501074030906c03a0380c0341006107841128501c17058a900050040c0781c0100b06c058001040c5d0381c0d941c0500220703611090160351305a05454164000b1394000d0103801d0260010031300310b00c60751038001c0c19203403400d005a513060b5803511000c6058190700c401d4801000c6541d200e00e000310b0714034428001000710b81d030181c40742c103000c440300d42c150350600181c0d50124070440d10501002010b00c422480c2440480032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 189146276 1250 189145026 189145049
    0x90d030903050a121d0c040f0204031505100e040b070f140f03091e07031b0b0403060c0c1202280b0601050d0f020403030e040e01061a2a06070906020f0601 68
    0x72241c4130700d070041445550450704030440b10100020f110021540e251464801da4007805030820b40110081603104030710000304510f1050a040300e80d142e0344da10240d080813100700c040507290ba885000480b114819581580c00b00b41000c140001e09420000300c0a180490742040c030b601c03c0e0540780d8140c41c2d0050360f200ea291988000002402c00c0014001c00100b030350001e440c00340c1040144e001d19030f6510709010880d500b58000324412040d94510b12000101c4603035503a481d1500e130443d502c0d500a03101e9204000d05010040c1034190000e00700e0318a1594581c49503004015a44035070b00181d406032200701d14039102c40d990540d00320104203c0021550702120a080c5950b41e400c00700740b1440245010711a400d805031000c500070040590000007840300308000c4405105841520390003a08a60b0307103225a0407841420f01904540200c1d21020308007038140100f00d100407016000c103040d4400740d01c14400c80141c110f4810045000c1d041490f02018040a10051007181010300a11b5950340f0306000700fa1803242c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 189147526 1250 189146276 189146297
    0x705090409050d0c03020f1b01032f0d1808040302090403110601060f03060605090307030314070503030c040602010e15130c090e010c03060602030a020307021203130e090d030903050a 80
    0x88903500301d2100558044211140e48181660040c4001c2020700c040303005000b084508000c2180c0010750811101107940400c6040f4003010054000706500c804440079035982000011070f081d040d18007201021420179a2680d1024a10145c0c802c6501c0714850a0700091140f8180001c03e01c8682500d003502d5050303804960903211400c5c26502d041c3c1c400d0010301a07101d25000030031407640c00911000001c1c00740e2000c2c0121034542d4026200c4d030059580082c0c0541c410041040443e00c106000e041c0c50100448480c600503507070726000d0a41e48112030320840ca81d800a010094245d092040408003140c05003d00040310540070515070428000d00741d07000000c5040440414803c180c55908003d02c00c0500c10000750b0001d0322840d0281c0810f0414001103031078600d00240c024008002c9803507001c1558099817401d44641d08122400112460501c114070003402050183c4200c804550060070902c41e003120549011080c40d8030b44403002206d03c0805091014100000740c1290640c3e1440e001820801c10b1170 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 189148776 1250 189147526 189147529
    0x406030c0b0f040b03090f01111903110d020a0504030b0606030610081e01090b090106020607210204030506091023010e0a0f1b321b010906020c150f070509 68
    0x41c01660413801900c02c0000030b0085d1408001010852000714000a0040d1000a1058696405400000500d42c014070f01d542083e64840d071f000c08414021905d405080c82c580c0720004040760004108040800c800050a0003402158465982d0001040ba10145140341c00e40c041280070840d0341d450789c2804109008541d0b0755203c1d00103e1091012105180c900b584d44242d040094185041c5c41805003650b64004183e0600c042080c3d1b2007240070343c0f140c01144011201b0904058100c506010035164284400b000082007841740b9801140705400515800c2004160b140c100c0d42442c10842c010240c194403404814410030407507044800c4800e801006940c0d001d0751078050012810300c2101e451822414940d10402c841c520075046440383c3d5074011845041e05940d0000740280d0001c0100d00c2c2c0c00c04140c102c103c80c01c0003000ca49540019010313031900d0212600c1e007924401c0c10203c98058001c10304185850f02002460f0b00380e00d030803c1c007900d10b0400c0701c261624240090210410084000b5011106 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 189150026 1250 189148776 189148807
    0x708070605040f210806010e030a080c0304080706021b01081314030301081005130b0702071d0615120612010b0d150606110c01051305030607030c030b0406030c0b 71
    0x50640124041c80315203480d182a0100e2802c040d02224400c05031100050146041c40454013a0110f90300d030100030b61155801034071508510029030b945407152041e0400006c05101c003402744020800001d5803503e0138184440e0134034160b07821640440d80207604e00c0f00c80d43c101030b4000714004400c2c20700807025211302502c03c02044000d0303006030502080034002828080d00000450407600814250740c601510480500280d680c2500c2400c1c0860745680604e010509400310907411100c40c0c01103803130081ea02c10070095030300074021903540d020398020300300300007428000445c01460b02c840f0308880c6081400a41c42d0b1720b03070901034401400350b651140e0b4002180300961001c40680030041039030706100e156160810524a6500c4601078040c204080000d2550052000c6015030f030100e00a4611040d21000440d0190080410003070612040c501c0024241c406108890084440c2da40104800f0846c0b8000340546987c5a1f1071801540740800070004a0820000001030354525a11160b84d050804091104c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 189151276 1250 189150026 189150037
    0x8040905060f041b090609050604091d060106020a02010e0105032a0c120d140103120f090e012c09190203100c08100e0103111903050f24010305120708 66
    0x100240742c07541c88604c500c01c2d42242080461a40e94030300300180c80b2441214050114462550084410b100030b001c1d00e0340c1c07504460b031b181984810a41034603c07004429881c00000380d1100c00035030000004402903580c00410450302c3d00c07007800c10754550f060045828190300307412090301007818142210480d05c034049078100d88003040c400f4201d4040300210781c00506a58410148030039010314012039400d4154080f40c00d0390403640c00203401104288038200554021a400b460340c1d0030440b14500c041683d1a034407000e607000e04907140c1d111413810310540f400b01072a1508014024811860001c02110030000581030300f40401d524034581c00c1390f51605c0480e02d4140741c0304008d0305840c1040400c804481d0301140c080c1c4258403803c0d100c002039a44c9d0030980b110540a000180c08404a01141040360501e40e02041200c03a242560000741030344d03030311004e08000098500c040d83c0e0b003148040301003d00750507055441544001a500708903502d907542c2d459440c0d440b101ca03070303144007400301d0044103010a03001a0342 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 189152526 1250 189151276 189151279
    0x60e0a090204060e0a120b16090911070515011412120c030a09060e0102101a030709021b12070318090f090c14091b070213020d0b010c08040905060f 65
    0x15110b0b9100c1d0800b90034109190040e43c01540710b20800160700710110424802c5542107142a25140c84003000c00d0700026160b00c0d4101031000a800015401c03030740b8412032208160310540d540d00d51440789070650400310101c03028642500060010b02c503034000c1288040c0700c81400c865400111850030001800c0c41e1003080012038402020810100d054008001000c65404541d00c111702c1c1c0d51603140613103404030170084050041e0b2054143d51080205544000d005d60044446c1d40580081680001d25244031034200000d074030303004103505240741c00c500007803406462080007420103443c031400820a5806940005004c01160b5000d10700d41d110036a03c0a1f0150401e9041807160380e004c440c00030060040f071001100c001c0d001c440c0001e02115004800c0304c030498000d040078034940301c29941c0c1400d400c00d0318954000ea13608024150044c2c0d2410123029860b17001c80e1001d611b4102c0040810105c0c2c0e80440b046041c00400000d078400182104222400e45400410004054803000c0100c0c0c84030300105e4855 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 189153776 1250 189152526 189152531
    0x20f2110060602120a05040918060e01060303080a0903080f0c071704031704060e0f01030e0d1706010807020616020106031217071418030a060207150f090b01060e0a09 73
    0x2884060300507000401502ca15408403501c501c3d64101040d03c038841c01d210311001550912050082c01019001078000c0b005081e19100848210b8541d0307800c9404072840c2407550f0790744d41d004000b0150091032150b0b2003810300c40204000c14640c0c0300034010902c010300d0241e0400340f28001540e911820030903100040c1e0043c0d0056200da61a01c24462150301c940015540c000b00c1c01200c03401042c01000311420341c0c0f40d5585500815000e0420f00c8200691800c40f141456181c50381e1341c0d4800400c2000442100855a46005084003103410b80700440300500350604102449040001d00754000813841e0f001018a00004200c00784400128014640c03500003d10700084409074030000742e030110035818042d06d803101c50031103610340240c00e6a052050703640f02600382c0c4041c4200040f4803201c0703540c402030040180a50710814070b2651500101c1c1d002c1d090440d05940c05800422070fa040c54070071800081c02c00101004907095944440301903800510842d01000b40c00b00c1c01054239244c2045001c001c3c03241e818103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 189155026 1250 189153776 189153793
    0xc0b03070906030b09060a050d061d0a020a0e01120b0a091e0312090c0519090510080d090f0b0f12190b01020303010f0303050313050304030803150607020f21 69
    0x50120405202e4003001a0906206840078904030005601404005108006d21454601440003180c0c800b003040c0c0d00c5a44e14074001e112a1414000e400c014500000038150b8940303148100001c000e110b41100d42594640001442800440c0d0340704008542c1064582400e95103265640024040313811008110016141104020100b0080f520070040e00c0303626070030300c0a2100d480708800c03511400d0010740141040c1070f0410141c01c048064200c06482c030515072501c240c6a41e5810113640c82070324080d4048075070b07400802000006104c1442207121600d4110210340c034200180c625031741d160140074154100007c0440040c3c000000300c2d80e03101d02c1d20301070b000207207400380000d125111000d241010f03072420542c1c010340a61010003107a05840340c030070901c4e91450650310f0488050300000c150140c81441c0c40c03014408a08100050002103110b442c0c0d82d9503034503003090404003d0b4075540345030f402102d041c0200c1006a440c4101044c0006040c4c4980e0070300c48420306a8003411075120105046405115003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 189156276 1250 189155026 189155041
    0x207020d120e04110306010215060d0b090c120f03180a12030309110402090916090b030c0406020706050415140d090501021b0a050304090b0f04110d0e071d040c0b03 72
    0x8403044000d0b02180c00b006103c8001d5100050f601c011150f090042e04403000354415140718030401504141d0180074041c3d40c150365600c10009180c2564140d4540e88202903d620310706e442050400740801c002c1c0607042d040400801c9540d40c4c065420071662500c1203c0148400d0f840f0410707088020079a4041e115101400e030b0801400a0207491410703a01c42c4108544c000030f6007000d008442c48210060041e10880c0e50b510802a8051038661020741003200303c80001560140500180d4015040c20314901e0b5210b01e001c0c0c000e480c1c01c14a51101d802e12000344004c20461803a01c08101075203100d400c03d020514003031101c41006226928620710103d18145a04c0c05004c8154041d00051403003000c001f200d1340d01b0080e0b050307551aa4100050095204110a0005400039004803552040141503e27070b014a5050024007601c404440295002c0cad804124645240181e018110207021003901800040307041c820746034403a20252180900e541c0030100071408011004649030014151a4036668403030a2401c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 189157526 1250 189156276 189156287
    0xb062202030603150705040e132a081b06030414010e010f0e070e0112050102040e0c07060c0f0518010c12020a290103030f1205010303081b0f0a030207020d12 69
    0x48019000c2c1c425802c0150100201d5100140254004c1c0c8609080612303242109030710590080030041003104000c440c0d40020203040e407a210409600030b140e400000045003210108a072035014010a90012100b40c0c0d2940d4510600d0016140c25500142d480c1d485d420300181511150128036011b40c80d143d02c2c600c559006510070068010b55900520981c034031060b40301d03901e0388903014101c500e185d48001042401ca02c0006134031402d104900150a05681d1611030038201ea00701d407921120040020140c0c1004039910401c108005c440c1004601000501c00051080c01002213030034598601c0c1103880074036030262140c156200d600296402c4000c10b0000e00039252540c0e00c07000c950346807151262500c201c24164250060350400360810480d680703036440c21101d11544c001d41070705102807030150014030300450080340d002e103000f500e6055040c20440c02d1030300310010004010403200022b02402045180ca4003c0790300b0075150340350251301c692040c0009800240301450040044c440030b98094170366034004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 189158776 1250 189157526 189157531
    0x30709061a2a0a0b0c030a0c1e03090309120803010e0a020711010f021203011d010602070b0a08150d200f01020c09060f130c030501140d02010c0c050303040f14010203090109030b06220203 82
    0x100d0051003004031580c001d44800e007580303409c18210301201a032007043d140f003684481da1050191510660259075072103010841d4110250954441c1000401401190210005a41c02c580d002c44214641105070316000540a8980c413000e04000c0000c100090151080110140304035281411039500c0d6555101442c0054489041c8950707800010000107049001181d200101c6004810992422040301c000f1101040024803540c00103200d214075504948030703109081d801f148160b1713424404501001802d9009800751129520401042e01c10796050790740803c81c041a00d8081c2d400580075100c010011302903078110020640c100c00d159030714021680d043d401c0b0b0030b8a00000c0d101000240d890384100600c1c8145001d100e900704e02c0102c2c00720015480f0349506003060340600311980d502a200d60009045a100d80d00c81010b080340b02c201400001101d58030207035041d1090000350f107000321107400070f00020101c0c48060408144840094075131744400c180070307850703502c92011040d00f1402144074400a4105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 189160026 1250 189158776 189158791
    0x3030c01050415060302130f02120a0b092a0d09120f0f09030308040803100302120a05120c07060c0807080a0801060e10080c0d0902030709061a2a0a0b0c03 68
    0x1080d4203621007040e81d12400c1306498010b03041c0f04508040e42d4034140034050010319075045a070308121032060805c911100314042d41c03000f100801e80c0c90085007000603024001d40154407081080408040414111000300e9101410303c41080e241c0300ca81c20784000500442038054151082c4020380c070307421540a080d80c01c40200c19201c80c0400c0d11111012200100e19000c010b02007401310010074003244280f03026544c800351a12020b00c0c1d0986990204020002905080c1400c0d0310030031000c4200700060101c940d081003034078a03c60404448035081d40c0c0c0c03611b103441408c00348541c10700480244a40300d4102ca02075500141181d0b03540203200c8004107000000d114410004280100000349442c0410704603001c48019070307030090291107080c00101940e0046c04041c06180e5540d4007540107880510801000744508440014030300e1a01054078982e050014080310701040030403489034881402c0138a00200130040340103c18200c6800c50340c9141c00c130004e00140c400c2c5c1064040003a11080c1c0780055105000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 189161276 1250 189160026 189160043
    0x3050d060f0302090702150a27032003091f0203040306060e070905011803141006090605040b060a02070b07060b09040b01260606190e15102a050c03030c010504 70
    0xd0f0328508076202d840d0000c1141d854080200401c0008c03c880e0405a070b100c00d041402004006a1448070b000352140d00c0e0220081200d001820000d005800814544a01d40a024510b0721070181c0004050315510250486000c07404180d0252962080050310082c40c0d024400704041ca455140c0d078050054200c0d10b03040014180d001c0030400394030442410200c04001e00203290020305507038500340307010080050318003540b059415140a1704003a004002c020300e0b00402c0061854145414881a5004502c0060054004021070088503a002413200115601d101005442c0c3d0a0361424001410045030600e80c0304000005020900c6181d1803424122000581040300002141e04040f808000e060401035480e004000000c24904202002080b0018400003203a5016181e071640e00c2d008030291f0340010702c0008110309001c45c4c24555900381c0b0740b10080c10418160301c04800103200340139503014601141031701e0001e0345080100400070901e0f0035000805483c1c40324880045240209421203042e1740d03225 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 189162526 1250 189161276 189161281
    0x20c040e12030423153303010209041515020307030504090c090b07060b04050601090807170a080a09030b0906010b03010b0705162304020a02030703050c0a06050c030405162103050d060f030209 84
    0x1c1501c404102c04506c0c04100c01c1d60a640d0080702c0300d22040100c0700f9a01075408004101e46079841c2d104036502480c1c0301404608031800d001000301305038040001002507520401089010035040802d40341203c042a4001c1051049e00f0f10403581c21109030320088003c00c0c0420110204202d41d082107001c02025502042195074040c0116000500c902c030310381031600403107410b20000030140a41084550414100d40c080c020382d5032a020a54405c10850001943c180e1040c41040284c03901d481d08030781600001c1445504081e07a01c042071006208040d4038150016502c82000703428800005400744103204a20314a1340c0b00c500c880c0d0300c01c3e9460440010001c803804516246000d200380c801c030030f0842d8000c504055580d502901c1d60341c81000d14680e00e1103000444800907085000381c41c819460052003130703102d0801e4501107280c120071040c01082d0340c0d08050180182d500c43c200076088d1000401442c2c0f525141424140c485100d020300304200d1504000c1e001c115000d80219500c2102e01c02c0d500044070780d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 189163776 1250 189162526 189162541
    0x30e01080103030509060702010905060408060912070b0a0b12101d01061d22050102070201080601080405150703020c06010e04020f030307150218030d020607020c040e1203042315 78
    0x38902400020003054003401144540e0a1040240ca03200384181000b4000c140c0710700000e100c3e50800d074801c0c1e40d507a10400411a00e5078091022811104c1c9280da00c0d4104010381e61604507800d0018a04c88050f651a00301007802c0d80c032881405407880740c0905490b4081580031001000d807980b03551050703443e00c04030a00c3d12101da0510030b15040320700b0100303030146210f1801c00426400801601903910407180454007581c20041c41d901884035440362000595407503003440054010440107000038107001050080002151006c299607200c602c454540d8142c5540c0c00c8819002400350b007015103070786d00c181800815812055400c41d40100d000b2506001e181c0341d12420590703070f4403580b18000c03c8100381e181410200403441d000780680c05d18580800003100100d001203860542074032030010042c1e0103241030003c1142c0510940090304c406032800d000c0700754400d101c1d59550081212002802000000103400d01611500c082d1004502c1196555615503d140c1c0e2546c49003610080d080301300200c00481d018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 189165026 1250 189163776 189163787
    0x606030608070503120a02010b0a090c0e012105090f010612050f0a20010e0409061401091a01050702060412290f04080c16090f0f0c02030912011512030e01 68
    0x1142c078020003c0030301070a17040400e1559001003514209664075405000e549646d1036816101501e501d0743c000a404280d4036005250f011064512414424115034008400b450503043e40780405640c03074041590b85030880b0480c60000550a03024181d403070403001048075500e4071506400f4034019002c43e01c1e0805602c058946030b907189200102182460581d0b050040c5403140d41c007001c5d2a05062802c0d070b580c20100842e0507030320390100032112196103040c0a40790a5101100e1809803503080030030442001c2d103c2e110549108001d60540c10300101141142c1103544071400c850140260701d4500d600600f03145048183d03088184041610031101c80310804106a6568105109207000c040b8403401d034683d519943e500c2d034084503600046000d285d00081042c9258a0180001c0444003000601e4081030010341d01103da0a0f910700c0c4480d81040c26940265a0000c1070f14101c500448010010007040207010380101005003450031200310449002403c105804140c1840901913180c80e0000c0301046c004440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 189166276 1250 189165026 189165029
    0xa0b0a0203070203071e020306100e1501050306130902040615020d020313030f020409060e0d1409181017150a0c1e050f27010203030708060f0103020418060603060807 73
    0x1613000748000000b10b8604250075010300c01401d1116540881038010a04021044070130000620b2000010480c05071381031002c0c0d50001c0e481c245440f05035030040008050740302c082c1010784101500c0940c484400c10680c0b01444a59005108001e0544c0d501c140e426a8200f0526000140c003843c07616050480c0003104686e03201d04010a90301e07045095a954103c001040281681c00c10350b1410458002030b600d1080303030000b084800003010000b40031300c1c0040102d414000c0100e5901c0051111071000e80300d15030302c0c8559030502a0103440555400002e4014a541070b4007500710000240d0300003607201c4020079200048490610442c155540b000f0004065844110400300003420751001c0400f00c014803000c9102480c110714105151100c1e000c42c001154001c04030802c2c081d0303c002c10b510044a9150035036044a4000e001940c1149001d04003c0c250100003040240181005041c0c03200a0b80703c3e0b4100c2c0e014016008000f8210707140c114690009104500500c40801d00d4004081110800041c00b00c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 189167526 1250 189166276 189166291
    0x6080a031b050706080a1b03140702010c0e0906010525020f04050903030a3305040501140d1509020402030106050304050c01030608030f070f080c0d0207050108010f060f02120c0a0b0a0203 82
    0xf90151500500315520100102802611540c6808055513030440b20f00b0500c40c82c02d0ba590208644000c007020084c4808060310540c2907a152008903203800d134000d203011410100490f4054001d81d05c143c0180c940c0d01c10708104507010062006508101c0303508110314202a4000d40d4110f981404907000c0c48211202030340c0103803442d4014400204840d0080d0400703101e00065004002d078408400d03400d441818a80c1440e880b0043c0144001d0129040c0703442541d005054103689852384502d9100441d00803181024080d0281040b07040c1c8600b44000758211512660340135004656941e074480c0c000300709410540b0100c0d030381d006498070b400305503100740a0300e019540050050b500d085440f603103201c04d031f50100404407161420780700c0250101e03040a01400ca4035000c0f8010700b24002910717200904140c2250001410310201c540148480c5820305001000d07100f10b8100b0030406142031000b6860884041000e031303400d030000900004e20100105d0700f038281e01e20400d2805040d0300c40320400c40580c0001c40d0f015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 189168776 1250 189167526 189167533
    0x503040b1005040204140102060a0902010e010c050f1603030314071d040e0105040605180d09031403090406030c181a06031801050702030711030a0209010306050a06050406080a031b05 80
    0x500422a904109a0400520304040c88550342d0303000424140e0b081603000f09640d040b9609a040e02c0d58041c0041540440c03023400030801c403200d03607001910f62100c265000f8108030417101d4903410404100400c80400100804480c1a46104d030740c000181c3d00c3c5800101c00090400f544000709040b10207066009501948031004207540c614200c03010350410345455035205484401001e0781d12070030f12400f8000e6000b2031000c211032a00e040748825246142401241c180e005030035201e82a540070711510142c0760312010b00c0b640d481c1032a010b20320f140528164079901a00d010000410812203182c030604645040c10002c03400d070010043c0a00b21030030500d5200d0840304543c0b03a8046840c01038011988581e030146100b406580480d0b905007118011144035002d644002106024002100202000071508400411200307a0550108440c0c0c071040c03000512b0b02da11280070039051019a00424080c0070058030401180e0390300c1107203903a142210703501030300411a14102d54030000d0b43c407540d86e04c1860f0404020b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 189170026 1250 189168776 189168781
    0x30e070b0d060302090903040609080604080304060c0c0b0f01030c0f0605031303020703150218040605030d08040525030b0703060f0b0901020316080a11060601020706030504020d0c06080709150503 86
    0x101000ea41c031840504000c907603111004001642e030103490500540f0280c0040d61281d0800c140542090043c1e0400e20300340e031080c010170000402030b50859030300c158000c00209444d11903001c20343d40a13000740c2c4001e10b4035058604100700e2212400d145030490f800389003007008150740c90000011549507806404001841040062142c042d0345509800c00d91007881100d00a42c0d80c1d40b20310700d0080c2074076013190040d41c00040114003440e007400e01b9a542042198100300051500001030f41d02d418403004d071001d00c1503403000582408018007420084c40b56503603101100c890402c1d056000d00c1000d020445405c075001c80440d05503407091080c80252148420341800740b034180b440d802ea8680111454604510080107070b0481103107110200350850b48580d0805854101300d0704054940d03124042d50520b40d6100c007041103940e0380d0001d115821142c2900b400503254540e80045901c040035100080c200c103004a00000c1e4159020b602d040c03142c40c0300e6442d00420b54a0b10908140c00c1b130500d91071000a0402d002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 189171276 1250 189170026 189170039
    0x408070302150d05010f03060608120306040e011b030e100e06040b0c0405040c030b09060f090c070503120c0a022b1d0a080f0d032306210606010f030e07 67
    0x140c001d84a8581e040c0c0c3c2c10242e421101c001515000d030001001c2248500c41001005124044d440c040c04810020380312144807004085094000240964842d58441114411b07664080d400a0491b01c910054042c09210541c0060060301510510809912802c1007600b140038140c0700d091002403204014020649890b222400c07401c0c1e02915200366850b04220000f11552184103001e601c5c202910701050b0b0038440f0301003101480c0010f144a006da00300c980305040035550307600708513070040c0b0074500e031030300d4403040e003010781c5140109021240701307682d00c0c0c05114420b0b1040b00a8071020040380d00b01c030205202e039410010070800d8030391204503e00f80500301109244c01420b81c45401700301d02d00c2420010150f00c0c00104c580c01c59500ca8000d40c0c0110940c170010a01c1030102030f144090608042c00600c0100200d0384c20b10711100e02000d00e41844002092503a40d40050385a61310f01020b90700450b01820962481d11004240c450303d010518020014110034080e00500ba0103ca07141e020f01882d500d0201e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 189172526 1250 189171276 189171289
    0x607060c020712030e01090803031302060f0904021602090c0f0d09020f030604061a030307032a02090405030d1407080a0903020c0a060801140a0e01060c0804050a0305010e010c050408070302 83
    0x810020542c022a84041000104821484040d9000341c1e1100b5034911804009070404c01e00360800c003c40d400400402c00d06180701d8443c4084c80d68107585032076468a40d1103074500d16004170130030240d22030700014030800b07504107184101c030b4000e0003110581c2c0c003a01c9030300c3c1a044a03c03c0500f8540c1090060080c0354003103216500450081d0700280072101c882c00380a00103820580100d80031122641c2da0580300482d40c0b102510b203c0146c1061f0020741c03610829803005089a581c450a000f0b07035092010180d01c4a035102d5000c1d66486a0103040341e0141e051500d1700503202d0301f01c0c1c039042007001d1800c5116080c119030004014051045a29004101e8a03245100406040c11150903000c1d48601341c1401c3d041e403659030200780101101e6880644d55414121480c800c8114428014481c251406060080851040515045070a281800d03040c0d60f5603032814191500441d0f00c04c6501002c0010300006220041d001030440c644544020804144045001e554500407401101600c0c4d0041c0000c4c001424400c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 189173776 1250 189172526 189172541
    0x6010b030408130e040c06020f030904050a0f0507050a0201050c09060d09170f090f03070602071502010912030501090b0103050127090204090c0503120301240e090108030901090f05060706 82
    0x8070001e510700201403d0010385003034142d02c44610011030904010a100d480e20428029020a1015060710b0100d0b0b0301d0750b0317601c3c0195401c0500c40e030358403070100c0c040301c40c9540415030108107150140028508003001601c0707034001507180300c003550070100001c4028030350b00c0440d20704120061241e410070040c24040d000504c40802d049849a04441c15419030781c0d0040042c0182c0048241c203566103000000074010150030705802680281d00c00c4505024058001c54040142c4003400400040d980d01c11608a0240c4614103018140e2907465010124003030345504014140c4000c0d039800c1c0700000c030240044013192030902c646404000e00402c4003400314000107040000c880d03120808900f0560940000381250a103503030403109454411340c10002d6040c10701c10001d00412060302d060541d0315083c001c0b00300700e14a01410080015004018440d40d01500d030041f80580054041380d110342c0c50300c1000da580d0380040c20640c0490300031076000400762480343c1f03003100361100a000f20341070035100d90b00e00c4040c0001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 189175026 1250 189173776 189173783
    0x10020a022133040b06040e0106030209070e0a0e07050406031803170c07060e010b010905011404030b07051605010f050a09020109030b0a0b0904030e0418050c1002120a05030915070206010b0304 84
    0x100301240340b0320445080d050081d809000c000102e818817404000031a40380c000000445c0e4100181040540d49540c01c881d407001041c28031202c2a03484200144014a00380c018034254040721050080c001c5c2d0040181041d20080c1d00e0811aa080c03201d0310680c9000d400304d005000602d00c8004002d807041618401c2d41000e1450041400c01d20580d65040555825039260300041c1c1d51211100925a130114084005040a0a052043d40012904601e40b03124500014205210581c08a0412881581111900b181c03943d0034080c5a007980c41c01c00d010304118141e0260150407c004108400c059100d40312071258161240e64403c0d281d0340d2410352a01c001400d95200303a65030a260b0010303458204c406403103103102c0e1b0b640c4400b80c000c2c0702c1004200c0c4d0200d101200080d1810f42c211000800008103031400100443e8458059242d0200480c0703401d80c0200c549405640200d401d040480d000009035000b00050750a039032000010001508008908403000300040e88400c0c010048441404021a0000d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 189176276 1250 189175026 189175093
    0x8060c070302150c030720030d0b030d09060504090c140705060405010b060a0215090703051203100f0b070201051b2d0a050606090a0906051005120105060a210210020a0221 75
    0x307c420390350454025844000c1d1043d260501d400180c82c0510401e032551007907081540f4514182a03008105020790f0140b51101a511441340d08414020130021210644000b0303441d942d070b070339890070a4581c2c03410307207003210746600708000340c646450210185c039800300c51039008201070311850964601541c0301400460300ca024110300400403e1061101c490106100d40c2500e41d02e00300b04005500e81d119540c00540e0540c0012030512421486000300d480380d075024038081c2d4481c1c6000d04610441401e0500d01203192142d00c0c41c541d10b2009666424200740e2500c2030701c1d10059840b80c1c1300c584a1110280082940e08803030006a950715110500b035801014031400001c04e1003540d03840004643d410b4030707800c040102e03542d0b04011500c1c014000c583c1d400800002440b6070300b0088041041040a07010342500e04000354455442003582c0c0c0704c082c40894008100e80c072089540d90010707403035010b0340ca4140d00680c40f05040b403880002c0b00d140d08003000b00560042105500414064003138254200c0d1141c078100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 189177526 1250 189176276 189176327
    0xb0f0a1103070f0507091a2710050f010203072a080f0c090604020a0e090c0d060e040b10030c03110d06140702010608011512050708060c070302150c0307 67
    0x140800203000d42c02e1040e8620300307001c0078a040881ca04202d07944110a03441c1002c400c1c2030540c03808989840c420000b079446540000003c2d00b0301c2601940c41084d0ba00000c40c0600300076030110b0884021040b1081528000400d840701801280c0300c0c4aa00000b8103c0ea428203601d035400c50b0448180c40205048487d43c40289446520407170620702c044081240961129600581c02e10341103010a8010b02c04840441c50a0040c0b4405002080e107802128401c00745500001c00000d901e00403101c0280b0469400c104580d203d4044001c003c0e000e0320151080d0030b1440014445550006800302526009810040008d2a50b0307541c0e00c0301180e000031300e5017089014080720000341903401001850344810302a1006880c050200900315140e81c1d0041c41903078101203e1a0429000d5000d11013902c20030100d5000324103031801d20a2601071258059140380c0700d07400070014079000600152415078441d60030f480c203d507100710b454032204d1400d8542d820190300c200b02084006000741034060460a04041540c07440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 189178776 1250 189177526 189177557
    0xb19031b1e0302010e180f070509220c0c1e06110705060405061b0d0203060607050d09060e030d0f03020904061703130b0a020606060f0903031c0f05010b0f0a 69
    0x1110095241c0c0012070035800502c115a0400d40682000c1c00c1903c07010318486000341d446140050107403000d2182d06803100450001880303881100c101840107001c050804a206181c1d10003106130b4840750441c1450b01d502c0c400d02d680b20300454010181c220252510440c1c5a851901122070556021501d442c0e0b200e6505d0308283c1e440003e403d8003400b83d0042d200d1894941411400c0c09001400c56005101c0300380c006860802d0003060b607a00c50742c403800041e100c0e580d12000c03c46da48603000024045100789508801d003540e00841c1e440994019503921074085004205150f560030040511002140101d02e1045400340300358050f00c0a5103004001040b0141d9890100d044031007a03100d0076205402c00030b4640100f09180e000500100744181d1428600b203041c1c00d00949403180a05940e1240d0b10024400c05000c1c096410303500c440c00b008040d40c0e6141d121401c091200114400400c00c4e40303040c00da1040340d080142c031485040300d9004059928110325002080d02035800f82c042d217018000380d101c110810 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 189180026 1250 189178776 189178799
    0xc04060f050706050c0705010e15150f0d051608070b0703050703031404060b01020c06070203060c03060310050703020901030e010b180c0c2410060207060305040303022b0b19031b 78
    0x30301080302c0c5040d07441c4444c0c117081e42991074908070429680c2c8200444845052905c184030341c01040044980c2d08c0c0c03010000001c6034cc030000011113500c2646803000e6028044089128002000340d05281c2015076920210291500024400e90600e4181030006c6804240588018507040744a4903000981c2c006600400c1d034030f2607050f0307003c0d590703e5a03c0054144558040140080540c02100d1a030709014081d030002e903485c00000c103080018100440822542e480801205002030345082080c0310070301d820f440c001c0081d0081411070740028248510248545010f1040d00d607a8400502503102c0ca4a800c102c4598030340003c2d02014103c002080001e00301c3d803050007046890110b0f0b205c104011060a880340407050b03405403043c02c84440b40d4030104502a00040c0030000c40d8650304000c0755603503860500364024007a860381c4068001030a0070243c0742e2151800e1191022190107403c01ca40c014030018810300a20340b900a280c0101c501800340b01240500070001001202c95a090307440c1c68981f0003c068 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 189181276 1250 189180026 189180031
    0xc030302033705010b0708030118090807060b091e0f0403050f04060801050a050f030d0c1505040f02010201060b0903030720220b010f080c21010f0e0f0c04060f05070605 74
    0x300ba031422019480e500201e4052540100748480d1168181445500c4600c014401031044d00055107850790086001e40854004224150b0015019074440c4000e0601402800480340d50f030307210301206000078130482c2080c2e40b80d005115544101ca00700e592142c00d0004070341c6015000b80c00b84002404400040c2c22114000c01c080d01071540c9822803540f40500340442c0c1e81071508040c1c4071303403014070026050b40c0f000201d5801085862826291280a03405c01111034400c061040d01c030b980c107040810040c0004036889500d1300b4800c0e03008104160791403134803407928041c084c81c1c660b05070010051540840d000c084503003400729447c07e038400d44a08480001d2800380c91181c4401050001d40281c00e0b40c035103503204645005000f0300f0300490070005040c005046034001040c220b42c001c004900021003d030b0f0501a107215065000a8001c656110380258803030a4084c070664440f211000009091001c010304141c0c0030b806800c949500309420104196800f4007420700c0380f410040c00788408004658140203060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 189182526 1250 189181276 189181351
    0x3170106031a10050306090a1806050915010609150210050f04030219020a060302070f020909061f0b04090509210712020105070c0210020109060203040818090103030c03030203 77
    0x1526000d812201000c081c0702c0542e1034400e031495151401003030b42000443e6886081100d650105035200700743c40004003511010a020342100420382420040d05500072800340d55940c0485007080c40060714010fa110007401038000190104c0707010054011707801104a5901400d006880c00420400c9180c021103c044420303a2034107920800344020315405124580441c08041e1074012000c405801151607020345210f010304041c2d00140304030512450b5034041001c43d070f0090807c840c508010103039581e40c1e0400c2d10019110841010340350703000120f03014072000b22000e8441c0642020710704035012000b00703001041011103006401c000c5201d0743c5116810008103407282501921050242407000800440308110020b580c9420244082c0303d801c821a14030303055040398404c81c02482201c040b4003500703207500001d16040c0040300744820005600003416107945603c01c0200d00b0889030040150b007150a10004d40410751008040c00400d120b6002150b1141c15010b0350701071501c0031795202d8880c400620854 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 189183776 1250 189182526 189182531
    0x603151a01050a121b0806090c160201050403021903170705060c0f040510020307030f0906022a03100b12120a030e0a0807030305040507140609090603071a040305010e0d0c0605040317010603 83
    0x4480c0d1754000a00704d0300300b441a0359005482c42d1070040e4009611803a100d80035540d00602e000c0085a11802c200c0e0040c5901403c4204400695003003046c42c0500d501003260301e01c0748070441503c002064000d941c2c20742c2c0c0250003410152240003d6a003e540141a1440e080108105c045180e40714a455201035140c264011665501e150034010400982c0101403c2000202c2404100c80c1d540041d5203600c1441c195904100818454210315030007402c4d00e0115054064400014008130030b07640312041207181501d40042c01001040c80303075100c2d046000300204412007440000b040c1446944a80c65a091130011114540c1c201d489089241c4c0210030220000380e128804c02040000a101032001420188526020340b02281d000844030300440440d0340c042c03080c44002544035541080118010074079000441500c04c0140c034000b11720b611502041d0f990358208080ac013011040054058030000f40d41d07461100e04850344e514040035040140050703007000040381a4044048009080c503000f051140c500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 189185026 1250 189183776 189183821
    0x5030a030203041508130311010f050c090a0e040f0807052a040e0604020108060415090608030406090b0702090109090f050d02030301081b0306070509120307060603151a01050a12 78
    0x2141c15050010619010042a0414481c10200244840f40c005031f16007402051141d010400500501030f80100da0302d49030620060124654200001f8810b501084d40e12801107030f1140000ba84c44001981d005040d1604a082003000c100d404003e40981842042640c00960705441c2051925250340f207400c4038010321403443c9540d881e00c0e2013003030b00c01840703034003d85554a4030740c001a00340305005042034011078480c0302c0c1c2c85c50000c0590078400506890346003000040c1d2074490180e62a0054011040450b550420200e103801000701aa6541030740140035401d940e00f041d04e1200130340780348142100c0c0050b142000380f0010b6420301c604d04440d0040d50045490f0341c5000b0300036181920382c17404221030b07914100040f515502c1c04078a80ba0700074000c4c00c1866071013078a90046600c4402444c00104503010100d070150401445403c40000c49000303141c2031921041610000c0202c49002800c1c0b140c4e41000b02d82105a5402a40070389040302450410305004000c00c01104140c3d0003c1c459904180e80c00d044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 189186276 1250 189185026 189185039
    0x15140304061415132313020909060f0123030d030504260d09020307080a0f12030e0307060b130222270509030d0e030a020f0d050405091005030a03020304 67
    0xa22075840942c00012500304909100402c1c44c0503040104030440980300e600c1c0340070114440c200884110241c0780003200500c1c080411140b88210788008030b00c291a428049074440700e00040044c041e03840c10325204100c1e441c021055078a03101d520f02c0024070107042d031002452650140300304041981b40303072400304040c42d00d07150201c1d44400c131001d000c3e40d6150070242c0100ea0860314003520302524600d540014228030b1400040e00c0c10060360301030245031107034000b81c03c20003524286c240003480c03280c5044410060350810a4084e200c13118000c2c0541e41c01440200045546508002082103000c0e0004d60000200300c124010313a40080089030041c4c9200d40180840c10503038101c8401050801038000f90f603541d0f00400c1013403600c01c41540c100340d0f4445010400e241014030031074046840d21441000840c804000442c3c894111004180243c0100401d9503480400411071500c42d01c0aa030b1b90b20b03d0642006d04003d06e001010f040da8a8047c031044021442d52001c00001c040c8500980007981c88614151 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 189187526 1250 189186276 189186311
    0x90b01121502040803180301060305010e160501030911010804110411040614032509050904060606030507090803031b0403080a0e0a1205030901050f130608070e06070c1514030406 78
    0x1c0580c1055104001c10000044040140c2c0c1c9406101c8203a5211074094000113800751410f6000a0000d510784907070358085110000d2110340b000c40d80d05000313040c2c66450006508442c40803e01408485036020301d800d25601c40c1e02d001d41d101e449080d03000705044d01c0c140420100c405100454801c1d0100003024031105801c14012032a4991440e02189180382c000301c482403000c005a10141d401d000308440410003030003188210044c140280030f4008034500703402c04c500074040d036200c2c0c46c010070300e060040b4041340d00c5290300100351850079000b1851501d44140c0500f1031103900400700070301c0005200220000f0b507100d00501820320b031079841070213007600901004840e0045038054000f038015000c105001801c0030054494250090030400d858030704400c0290284d1140b51a040c0040315241e0000c541c1c0c03038020040d40d02904655a801004000c03410170b0003014480c03c1406010076001130800c00100b04544070b0410070b041c06c3e01d851782420555002240345500242c0b400c951907a00c40c17018140304003049 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 189188776 1250 189187526 189187553
    0x2070f1103151003030507020111011a090a0207030206041b120606062a0807020a030209090d0306060c02011d0a05090a0621261318050a290301090b0112 67
    0x105420b01905001d100030812071540e200c000c01744000400c0c0c510a6a0141250081c0340030208021701607803428002501041e5510203815124544840c081483d407216482070302c41040d81034005219545494845170f002011180700702c120307550301031000300d4040740450b801c00c42c051060001003a00760620078040e200d4a100104141d480d05400611442e414403903552154507600410034980d125140d0012482d0701105070006500b0075460410311001a200140c120b0200046940070007080351201c9003201c09085d8108060300240c2d0102a01c6c1c00980e1009074070b01d00150082401816680c1c0d14080f0301240c2046440c900e95075520305041101d0382c424020144184122055004016555a600200c00664100701c1c00100030414280c40c00c149500111035250544c42c1e80b00c5175069540180703030305007403030014030409640c10712001c5941c00e1581d004100506884500506a289895080422030010a00751030f81c103648662241c6d021550320b108007400f8202d030f2603519800d130b04a403c03c080c01b0b0006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 189190026 1250 189188776 189188803
    0x1c0b06010807020a060c0201060e250503130821071107080313140d060f090512040b070206031e071d090c04050d0221011e061203030b0402070f1103 65
    0x504041050183c0d000c030b102c09245611180001c0d130541d121104078010203103500600c000d500d6a50600c060341195400642e0041e511100b10004d801100c1411109130106442444081b03403040c40e9017001070460381c003070010501c0350503056828800500403c0c0003510243e034804080b070f03c1c0c00d01849000505001440207028908011031070039002050102d41c58a02d403080189210142c1d402c2842503440140300c03400320b50003400070711401801012800c010030f0060401c9420348200c58107000f905450f1016502101e926a1480d401c01160381c0034444181c1c002890301e041c15008807800d0108070400350580e406041a552564000514107220780107a2804286082c8198565400c101c1c0c40c184000c1110706a401c02d0700e16000784251440811103540105042c0c408210440d2000c0d410080154841c601c2114909280044a2441c0312200c04075902402030808104981c004400400c1c002e0f000483d0400c006000145064040c0e03c5002c0000c0c50840d080700c1402121090800c1c0c0d25041040030001950b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 189191276 1250 189190026 189190037
    0xe0702030913090201031404060203190b030c1005210403030609090203060a1805060c09040606140306041503120306090e01020408070e100b0a3207020114091c0b0601 73
    0x180002030b4207010703076030b5480d812107888451550459220750465407000e1083c00b00034010b0304040c54144042d410850340c010802121007050140d015290061140105025020308004c6148400b1b00002e410f942424805101d401c10401003c40c800b60360301c52540e40e4601009006d0700345850010f003500d01035401019400c2c109100e10016036404134149401002c180e81c0043d102c105120101c41a401d5030002500038000c84080006c1d000c4d03a00b005082035030007242d04100c2f481c1c4a0a0549004050078550304204030b0500001e91207040550104280907402d400c0c13141050340e80e9031140c0c991b10411200c3c2e00045d1b2034900801001002b4000c045c8880719100003542031500b8181e1655641d6598420048881d002038003207042d140c0b0107505280074100070b248840d69003d041c00007400505802c0c4000151b040703102c0803040d11191900850780c07041000b800d0180b03092003980044821000c3c4030920305508408000121140e41d500d0f50046247c9100100031801d051507061000d01c60760010407541c14400e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 189192526 1250 189191276 189191287
    0x80606040509160318030201050f1305120d0603060903052a0316060e0a12090906060e0105031504061401110c0a0b071b0b04230a1802071b0e070203 65
    0x40d24a80d425610400c3c0c4a200149000303100b1044010300b40ea0096841914448510745040c03542c1034002c20b200ea0b816610603200342c3c644122440c25002403443c09429a00960696842165084001e000260002c08003041c0306840b0380b1564111850f440c401c50108000141c001d030702c40c190f44079018021844c40741e0035002c00c1620490a403680b042c0b08107620142105580002000303601c1d4040015810400221108458145800c41e250108502e54001041304008002a191900d001d00011b590055840c001c4000600d801540c0710b03000a01080d40d900c185a0800040e5182c40c801d410003440c0c2c0d09400300300d81501d0301c0098900d01001c00301900b59041517140c00c10700d85801c401724040381c1e00200b48039900c480d6802c1000405440c181181d03519151a000018481080000f40c000d0760903000e100c1b00948460b4400e50010b02440d0000c6801070914001001101c44c0c9400142c0380202104000d40f070903140d070307991071005c0855004035908181e20990601006009006455020100380011450302 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 189193776 1250 189192526 189192529
    0x1063302060c16170708070510020901020304090522030513050a03020319021504030b0a050f0709030b0703110c1605061201090902120d1e090302060f0309030f130302010806060405 79
    0x40c031401c40c504681c103d6100496003040f0842a081c51000614071680b0f448040500c3c2c007801c42e9002c04030a4905101e03814610700783c600d0505c220740c604803050b001145024a0f00003040c0280c14010000c400741d03402101203075841d800a480c21344c40b0a110795107555440304035513041140b040c21a0451400b8200e011000e100503100000c0740d480080802c0c40c4160311050510004040103010320741e048804c80c7c08503001003003000d03d81d0450b00800d1804000d00c41603483c03030101c0841c00c3e0b04640c50703000520104800c002082445c207035290003260902e8007040303036041074102e441c01c3e92117500b03009441d0380403d12001c4950f4030075801d4005440b0841d1014038089601c0c0d0500000e03d07060142c1c00e051680c1d40d59400440d0f1f00d0031545003001200c0c000341c0340c410440c2c2802902d40e01c401c0c240c135034111184440c00840a4032910141c01030380c2c0e0040a15090081c0300400581d1600000c00503542844104090b01031000d8540c05040140b2103000110b01050039440010050103020340854000d000601060146 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 189195026 1250 189193776 189193801
    0x90506100b040308030a1a0607140d051611130e06060a0509010312030f0207060c020303041104020f0a0e130905071a03010f03060f0f020a11061e0f090106330206 71
    0x8440e202c40c001c107c1d0a146072044c040d00d031040500c0c0e03500210018401080010922101e80703002c44c2c04080e6240c2040000050b5120300c60b400b81c01c4085006031401071f000807030000c0010700442c005400040ca6040011031030007248d0120b0a0441d8640c042d02c1000b81c2031608201010180c10140d900f541c0c1940341d5030341d8004151541c1440c900785a00c504100c0c0910003140d0554452640001d028444504c0c03104c4040d44a9006a40540d00922307004450000d1742842d0007210812032404860514002500a084810400160f42141d0100403403407040722200b4540a1920310702d00031800340c0701b160b09c1c0030002051200c126403054850b900c11f100420609203010500021650410404644039203001e1000d0020080500505d040780c0c4085100c6071019400180d408018440300308540581e114131010f1403d28400d44c6031395460122200000310000224003245d074001400340d001041554403244000401c2c080ca240c648000c6800a0301c0900601e014500d2a0000746c0c01c0c0040e001a042c80d404e040c16 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 189196276 1250 189195026 189195031
    0x2010507021512010f060f0314012606090f0615010807050309030c1e0106090510090e0a1709010f110d1d040912030b0a0b0403020f0d0204090506100b04030803 70
    0x7168001c88001140d03040700e0300844a12403982800c200f49982c45004802c07140710310b1b0240000180030440b1515096010740720b0782d5103a81040401401c141c0c83c080034015040300034003c50f000e00740d900c15030000350300042111a000711801c502600841c3d440c46400b034600385008010b508210305072102c003412030b60407202d0160072600e1403415139500e5680b81282c516521a50510031154800c129010740c404442c106d50030540d40c400d50080c8005070b84c48005000352401695502c0b0890020401001081c2c2c1a60142000c10141003d55042054513121b0341c002d0450038405991540b0001a010020341e803100e44070119407800e05200e421301c0c5400718503d80d21461600d51000b4081020341e05510508140754070400d44400500c11301403550f1300e00d821a4801050b00003a004a8142000e141d128500b455081c4141c60005002d00e040524540070040d20410b0381840340c0c0c0141480307400e00c02503221070180310318190040c2ccc014000340c100101000d00c042d46562000f8030003042840140700148401c1c00701c81c2c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 189197526 1250 189196276 189196279
    0x403020f01090e0c0904110703020105040b0601180e04030c05060106080f0a02282f0d08060904110f0913020f0906010c110f0d15050109090c2c09010902040e0a0201050702 75
    0x6807070f03074204070100b401487c489400d080c0f10310b00450440201981504841d200368454000005035480340c20040d101140304442d0300315065010101032002900c14129154000d020b40b900d8100d5a48039100c80742048400e801510008915204100e18050350484050f00500003001c118584500b04501d43c903001d00c50740c04071014880041d1450845403040c0d11034840451101d14880b101c0d0070354411004000d207200307881d00e400c1c010024643c0d80c1d079000d440207520070480a400d0351025902d680d5203000540d035a280542e448120344460fa44107850f8504c503148100b020620b010303140c0e0101d004100541e0000600e00b417281004104001480e41c0c00600921090b43c031505200b113170401d81c00091501c504504200360400c100050680600401c0451524603014000c001c2020340d03280c1b00e50b5800c0c0c90f44070001400000720284200280192a24400c0c801e24403400103003c03078070403100540d65003682034641520581d115020075013549418030625400f01e0b083c0c0000c0090048590020b04280140200a07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 189198776 1250 189197526 189197551
    0x1706060901030b0901080109031d030c0108070306030605070804050c030109080f0d0f020711100206060f060c0c04050a240302180912030f0a060e19021605120403020f01090e 76
    0x82000e0707402504070030a1070b5002090741e260366851780116402025980340980009000145144481c243c581c0c140813546009005048203109400040d80d80c1880509068200741d07a681d800004a511071090324003903003107547c4003480750410b41840f07850710310502ca803540f00b645005427050000d000300e0200c074025442d1700d04164490380c01c1d400c1c102c0242002d40078101c4031800001c40504001c04207290382c040600442c1d04408044c2e8403601282d8802d4225065504601090381951091400001505855840100b11078003801070380f02040a60f141079034146200307038454900c1c00c2e2100c034498811008444c100803200307250349141c000601d04020f00490740958513810001c034284490500c04e0039404c09206c00d22a50380d040440c1c82c8444a40212113090213103203400f001107600c4081c4690740b030203080003058006030403105220f550004c1d0b20208509410082107107070500094800c1c0a4148203984c5020090744942c03942c01070010b110149841c407410400040800d2220b08241005ca0740c001c200d14660 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 189200026 1250 189198776 189198787
    0x1e0c0f0813061404030810081203060619180b120408090a0305061003051b01050a030b120d0c050601090506060a0c0213050901020d060b0a0e300319170606 68
    0x1c8030100e40079401d0240c030391800c048581680d4031100d218140034038440d81e228156961781d402c00c920181558081d485035500001c4010711821400030245400078030003000703140f40500c542100b102e55149422400c0c0031a0b00c50f07080402c1140301a03c2c04004101058080c0d00c3c10700ca100c4c20b00c401c003100500081a0000c089039212541c0c48003000790025590102c110780741801c10000d081d044181e00d1004498034800e804144419120b4100c0e10b00300200180c5415041006580041e0050b1011094031070300b103c004500b5005002040007000b500f00c82549074034640c80030300e0604c1c03400c01d003050b04032101050500b4284400794a13110101e840404180c81c0c0080031012510014a140b26100071a152480c28441130015048043d070091101d42c41d04402080050303600c0b200c006450095150103000f10354190354a40c05418076001261003010a521070308031100b03522041595803210a0810401a8408100c01c4060b00030001000c80988660600d03800c0050001810b10900d50010020780c014000410f5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 189201276 1250 189200026 189200041
    0xb0c0a02091f0302190915080c010f0503040807020409150e010f0e070b0a0e0a0605040501030506220213090f0b190e04110102010b030106090c14090d0605070c060c031e0c0f08 77
    0x2105c0240c04910030922080c1d541210603a8280d08601030300382d86001d40081c0c1040b540c05147c20042c040e1968541c07038110350381d940703c400b0b0ba0f0300036103002d81e0005e44800b40000021600020700b1091524407800156400244100307038211907003444140401072400d4040388041034001000021a141e13680480c0e50741004d60300464a50b00c0100403a80c10243e0000003003000c41d000306c06002940d00c2030360200f117035540d40f004014006280f024201c0c4c44c0f401403585040c01d60b47c00c0d0010f06048603140410002c8607a02d40101084402455a003480f40b55510400d030001e00c4c10422201304001031500c00040c8500304000929075050240c03005050184525074040340380d0003074114480c02c0000034006c01c040c95540c5420005056441200c81c0001c400901981042c1944410385402c01009001103030080c100381d42c1c0c0c400a102c013030001f409000071a00d140001507401c5c06074080c5003501d50740109038880c240b4a246050b10590344c1000c1c07100c2c20150640d25180d4810501d40201d046403801c107107035071903480c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 189202526 1250 189201276 189201319
    0xe0906150a030b040b061f090317130905090106051f03051005030604031d0a0602190f080301080d0f1716050f0c0313050a050105070f0c0b0c0a02091f0302 68
    0x10b00c014a8103419108000078444c48140c0710b4482d1205a408041c480096540798440808255503e000f00d0540d91003400451402c4134654001c10650165034a061050604914100540d601c004203898542040021045003801404010803042e12485808800752742c054080030f41390000301040542c1c440010b01c0d8800c08114440003410b0180580e070490500e814003d10f2920884903c801d0122032612505060511802c00c1c81151416800b910310040c482c800c84102d510844002e40d40d080b51500204040f6607000d00841c02020120001e00d084c04010720040c0070030303422010203014441080c55410039024540f14695010028417001d1078007a00182c82a50280a91000701030040300c0491300c1041c0d02c20000040081800000c0140d503d9540e070340421403107a00c1802007900040050240800241d2400104500c880c4a6210040881e4803400100b0280e00701700c0c55554203134407240300c14056040107008103030820703c40180110383c00f0a10582c000340281501c802401076105510b00d019a0981e003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 189203776 1250 189202526 189202529
    0x6030510030c030308041a15092a0a080903090d0816081801030510050a0303080a0f09030504030320030301050d08070c030501091a010f090e01021c020307090e0906150a 74
    0x5050900b0b920303400c1c020400401160202d0796800c00180010710a2610034001e1300c19513044581039013022020051100b124800f44c4205040d120800e8074044980c00080401a02d90f0780c40c51282d12995164002082c030b800260034402c41e03400030002a0200e440c0e072003035042c85640051001d50340b002d030b807090034001500c00c0f100905205800308030180b60414044440c80584400d80e024481500c0e6511040000001ca204455016452035410000240502d0001d54005000d100002c0c201510000080030b40c1c2941c1c9003200091400103080c020150046010350181c401190302c80195204103400315620310040c0103184c450910080440d040022080499445d15442501004115078920f40b03c0c0c0030b4480d101080300d140440d00f80e6100307000c00c402c0b016070485115030324030602c03d1310f0702204200800c3c48104244440d50208400100b40010300803020f00c0c4140e0b034200607520b1400c040010030b406003030b07080756407906284024010300820004503142c000e603071903413210100e0b80307840002441155603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 189205026 1250 189203776 189203783
    0x109050f0a09022709100501050d060509070b070c1818030e06090a03060f0b03032508040801021206090601020a0302030706051810020c120403020102150403020f0709020403060b0d0209010603051003 87
    0x1400e810086003410030034080d0317400c0d50032a81c0d4255501e2501055504c240111904001d54174840c101190321504038540040342da030b094602071512840380e0b080c540d0103078100303642002108034200444c001c054503046482403020010050f040541c03440d561102142803001e001c0190a013414842580d40d88121012080300420711804582d49150150240c070750540c040500c1803810300d05001c40d04011003181e03108180c0c054888007118005481c84034040e40d248044c0d880030024132000c1140a800d100602904041c02d4035203100d4508641000302c104c0c4001c0400d4115008001030ad00000c0c3c0000559041b240c0c04100420151346188402c40b1010f2204a071138500d2003245034089018029074002c05d200d5800f001038480c0e110030003501480c544100c0c4002401a07111001291003c1d002030282d070f411510901c190782c1d0070b1925120b510324040070b030340000c0800c40e03001408108000040c07046500840c0705945a201c031082640014a14260521810045c5525580024034403c0780001f071001540c2d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 189206276 1250 189205026 189205069
    0x40b07050c030711100f0c1203090b0f0414030c0a0b0c070501060b0409060608060a0501050a0e03010501060e0118080c09070e0301050c03041a01240908070803120109050f0a0902 78
    0x4140c14682071300002e058545015890a400842c0c1c414815030046c0e0b0b04485545800b001d0b125107913a22035000d1035080265080580c2d542c1e4507000990303c80906400360580c800c001456007400d04110054003400c24101401d0f601c2007103034008249002c10b01d001500c3e00710003071a1050f510162421524460000020255481c254010958150030b0002c1c0c820344e40d04620801480ea160344082c1c480c01400d03a9025444090040100700030340c03040e0010041d09002c1e1410101000020b408a4252402a08080045010a8011021540e02070311900700c0e00a080c9403450729502c9c1c81580364856900d0261180038103000000941990701540e200f011016003d0000c110728074029170351180350380058a040301c080780c40300240842c0d0141019890b05070b410809010107000b00c0c014a00c0c580e5010349410900340500204009010036090103640020300c4000f0286644030003800800950250580046625a280c0b0060052542d103010700103501400c0f0403000203c15040d40001081000707903250380f00740c40d075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 189207526 1250 189206276 189206287
    0xa0302061009090305040e090115091a010525050312090304050405070c02010905011d060304060605011416020906010c05030d090c090b0105031504060b0d1b090b03040b07050c03 78
    0x158001400303442000c151800c10442521102054180d0f041800d0280024000f8132040c003198201c480c01580101468000041410802d01101030b083c1c4207601103210940c0d91042c0418a04040100c181081424600103160010380e083c4410035100610007208035600005800b0704002c1c00308100c031503001c0229408610785c0303007600000d0396076402401024011420803003c5030009014880d00c800c5180d050b100c4070b442c0760905d0b0044800d20602c208004150261070070707213040c80c0c49140c0194041c42c0141c0001c5400d900340000074044a80300751045042c01410040c6409013031810b60050745c4154100c80d45502500c0c0c00c4012200400a01c8015000340400100080da4202560145001c00c1c071035260060300c0e0355204445c404a42c8403800350b9010030410000502c0192050394041c041903401440011020340354005640300350001e03805081415a11450040c80344030031100b485904c1030501d0710309006420801c1c401024080a000241120021004200300c20301a0060700d105201c008212601c0f203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 189208633 1107 189207526 189207533
    0x60915050d051017030d06120503180112051608090123040c030503070f17070206040b0306010201140c040e0a2a120c050d0b0a03110f030f0a 62
    0x3202c004500030582c401010b013060540002400115291417001007210229036446d04540c07880004405103000094000044903d04514000e481410b2941c2d0720058412207010051341c50801d042c0002c006601c00d10542c902c00d80c0c81c20b0b0f40d402803651100c00c5420308880d007840c0c0c0e00b90a4040e800300d9101181d1001c1c8480c0e041441140714421455407030f16458203680000380126030745039080d1008014485030303000400e1160f241172185031030b102c0d4503070019009104500c070350115100c0200000e078030b5a0003980811071100401030704030701303d2411300c201d50b46640c05409990701c04403604011540c102010300c03a07400804815480c41c040783e500d80c41004000500c8030364010421520180700c50003003440f8080e00038180025183e05031509030640b030040079101809101401400c400c42c1c00c00205900700401c061306c800c203a60398061000700d170002c01c0c1030082c8903610340c0e0148210417008040 = true := by decide +kernel

theorem cover : BRFrame.Cov 189028776 189208633 := by
  have h0 := BRFrame.cov_init 189028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 189028776 ≤ n) (h2 : n < 189208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
