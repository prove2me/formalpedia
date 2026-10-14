-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1155
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:29:47.810347+00:00
-- url     : https://prove2.me/submissions/f91b685e-7ce8-43bc-b20a-33fbe5c26aff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 207553956 ≤ n < 207733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 207555206 1250 207553956 207553981
    0x5070602161101171303050c1e011802030a062a0807030f060803030a0c0e0a060c0506060603280209100e01091e03481e06111203 57
    0xc1681d00d010911060b148030740c002c91065114004000603500300307554800c0c4900421640080980c1841f404103e115440c0c00240120030584072103900460a20302081d1955003100c0c205400c14010b1414110603201580c0d0009503001c8039a0700c104003103911408076038176220640c844407090710b81103801034821005030b40001d1894440c2c1c01956041080c03031810381c2c072036082c1c8010348a42c0c000b5420400110783c2c100e559070400c0558549a04103810170f10141004a00c3c0c82d962030f4401e41c0000c007100c58841c20004240109500310400304c5201d0f0641c107101d00d117202505041c0c1c213251203103514541d41a00550301c1c2d80641d080c4440003820403000c041044009040d50610401a50004038001000704425000740f14182031003080300b0b404581c29003140d84004554130400701491a4119003000ba10230107513a00e00c00000800e1580070f01c44040355404c85881c405220f9004049035102c1c01600030320614001008104030b480b1841d00b2540001c01e00051800c0c00010768480303448a2001080001c03003426070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 207556456 1250 207555206 207555247
    0xd090305030117070b03010e07230c011103102601050103060b032406100c02060406020a0b09070501020c04180b0c0a020705030c030c0d140a0c0509060409050c01080705070602 77
    0x42c80045054001c0b210f002d40711005030190500541c02480144880203000b05000c1c1d0241207803c10000c1c86048e95030080701c00d034190303145594041c0700040b140d880000a01480b003020070b03221100341c1541058501050b0000c202c2c003d0413481c003484000e40c04200c080381c13072401501108900030803265840382081d0b0050700078125403c0c041e12550b810314003d8020300e00b0b1946a540707111750100341034070780c2000c2001c00195440c0c0c41c0c0400140007038200150f81e400c6d000b8002044580c00415852456140c1b48808a0004142c0c0302d03560002d14007080781d660042203003580c0210456001513018207880d52101c105400d90170183c068104242004000e242510050148038519001c0ba0160b075541c01c00c05aaa0300f01d1180300782c05400c10f10501b192818040350b0002c03924410304000e4408481134140c10b01e404124001034500032000c900c104580d00780380c181160814001d480600054400303480341c9682e8449110100d04001c1d000c80010032942c410705c03d50b004990701600555403055802e8400c20400020b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 207557706 1250 207556456 207556469
    0xc091103070318020109270501080303040309050a081504080d09030c0605010906050a031112030d09060507081e090f16050906060717030604090b0906040c0f14090603030d0903050301 80
    0x1440381075603040600800f074000381c59059444880041c18212020100e1030b03440c002c7d444c05d50303a04d000c40c10907002da405038a0103461540c000b1502c9290900f0300901d072070300940c00503010305005201444010400b1600d500c6445030404090465102d038941062144103911030440050300c0c0078651b0080643c4140111801030180c081400035907210f500b0082100c0403032198030790083d00140100009071014002e802e00120081036924001c1c103001c4602d007198045881d41018a6582800300104020b41c41020b1300a105c80c81c000c03000d868100584611100c0c42401c2a09181c804070025820701401c0140b10080000c150070340d00d41290069428128503a14060f603071042c505140025800d00342007081ea0385407034120020180000000061440c16407010344850341180d102c0404001290620384c50742c2c01804030304001c01c40d52a042c10301000ca013882e6000a07071060380c0840c04005851f020801100a82003c82e0344055a444103400645144120091105502c0c10203011409140d040006107040310baa = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 207558956 1250 207557706 207557711
    0x906060f08161d1203220b120c090d0203030d140a0504021012021204080c06070206040c060f090312091e050102070b070609050f0f0c01030902100c0c0911030703 71
    0x85800102e8110b940800c07920002586040c402c8651060480043d50180341c05090130410210418516041d1b5001c01740b80300c170340008017903e00703802c0f01e042d46500c00400d5044a002c0c1003141104400600c0500903007044060709001c280040d9503942d8070b0001443d80d81c018202e80d901c0701d807040010082c0202120b520310900d609000207000c0411402451300c83c95004180c12503e10100704180c036a00359813074a00e00e200c0c2d0700380101032034444c90303000b844e0196001d02c0c0d6290701e4a20a0082d81c0c900f000051104045420550a01c800140350809400965036a4140300c3e4074043ea49100329500d444c10b0380003800382d400021200104c5500030340300d8400c0ea203403045000148a059005c012256285202d0280180d0001d0010081f10f9400000b51404904c10200800d909045071140c624080e440000c02c003c6400c0a000514404010020400d50314800c0c01c2c1400403e84a400003900b270103070a20381c07000b4008280e407203a0800816809000c003030b20860b40c01300700030200504125544e03001202c01901092 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 207560206 1250 207558956 207558961
    0x150901050a060f080d2303040309051e150a0c02060310080114040f1e021905101103031512060702010911060f030604090c08010e250302060f070302070906060f08 71
    0x380303c8082d01520f030b9040041c04069008078040702e01c003281c072801c403404890050030402406555402903001d1406580d075003103424207207410840984102e8040d80c0d400303402c203001c641c041d403280756540e41c1003d484a541071321011140f03010303105070703640001c02907004000008110021403480144415101c140d80204409251143c0d06000d620041c1c42c0640506100b8141500281c0e945d040449034903c03007611403a42c0101c680c0031580e40c0c0341a080780d14241c25101401d005500704001d03010401030300c9140c65280715040e00a41d585911004c0c20745400584828840340c40d546480705110000341041c0100e1f281d92615000080c001c055261045801541c4859024550701d0504103560140c07500f040f4462454030741c001040000c0450301811904904400000215181d082c03081d4042c030000c01028000b0105010241d07003540000184524a003007001a042c80561a280c05440c0605102c0010569034485170130181d25099565000300c040a0a00301c01040b49548020401992056600c0310803658 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 207561456 1250 207560206 207560219
    0x1323101401081207060509010b0907110d02010606050d0b180c0a0906080708060d050c030706020c01020609210a1e0c14060106080c070c0314010c0219030c0212150901050a06 76
    0x103d06001d003ea042a01c00d11104000c500b01e40d2046401c503c1c544000100818405d0100350203540489400b0081403141c801e090302204144808081c40070948002c0181c2424500050001d000d0301c06080c0315959690781b4081151640102100c560b12404042182840c200c901103491340d00103202c2c0c0c00040e81203030001403494001c030300060003000c5986407003186075505024040c402c07184081c1038416201e110315042e410345081c8501800782c40168043d09804008000281c5440c0d006090070740d495101542e01c1c641040c22070035490081c8600c040041e03070b5081c85001160400305e02d012400c200780c0a00140c3d80025003248014850390700c20342c00b40f03180041c450901e41c0c903410248124404503002e4000200d80340a074000031300c0254400c8a090032015140c1d21541c2c0c2100520805c41c025131b40d168401c19a003501041001040404a01600400c002ea42e0b001807240011040082c041e00c0106102d0908800602c451100c544400c072110000d03142c54001c035401303441c0c00d440d041d070440c1c40c045010404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 207562706 1250 207561456 207561463
    0x1140a0516110a090b0109090e03280905090c190504180204030201030c030203060a03060b0402131509080a030f031802190302040501080c03070e0a0b09041a0f132310140108 76
    0x1080141c4034401d0341c07450207280750082c000909d00b007a4035020030081c0d1401000008a0103141c1030444c96a6011210b0b800006400100203400640c45541c0c00400c0101c00340c0b554080760366014041e10381c0505c2c0203040320207031614029a0088545203100805170400c0d000c1c41d030302900c101c078000d903424440003460ba60264104c5c4410b40b505500804052130500118405030012004a5405000103180615526400f40003404035005161106000010440c0e059848000310300901b02c4000508021421340d074002e44182400f0762001c091507118000400c400e00603682001c0ca0940107070244a21241c40e5280541000070390104074400c0d407a0000108206000188030f00d40c240d00030b801007244a0030440840c0d0b01400040c00084078646544040ea8591a241c0d01640142d100d640d40500481d0000140003140d8801061900001c090100300849444201245450300b5000045180800c58660726040307207040d0f0011000342841250680301c5001c03016800003640300340229100c00e499803030345078150700d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 207563956 1250 207562706 207562721
    0xa02030411040b0f04020d140601020c0a033005030711011802040f0f140a050a0203040b06090601030603080309160b040608040b0a0b180604140601140a0516110a09 72
    0xe003034904455882900b055884200343c4a8001c0080d4803114001c0001000e0b07a000003401501c054440c1c0c40c10440000b070ba1046070304110240060202002643c011500c0701710719110140c00c880040184a00702c09119407a0708011004400c41d070b850226440b000b401300ea0056607a01c00013060f0240c0d55880303400601c078500c49103078080000366280030b44d5000c210181035041d004d4281c0a50340c1071070706600112845070081c1c01c0526500c00c42185415404181101e800070202c01c40a4010420000001c21014000713502440441300c0103126210280101c00408060300014a084000410311040000024402141300b9500d80e00f28000d6803a00154101401680300e00740204121102150006680074841544811603980000d040e2a0300d0000600e004458400d10a45186900c00c1c001e0030300f0580100c54400c024a08084000e041110001b85400302000c002003000e18007040380f11540d0712900490701c0000408102c2108020141060f455151b03082a000d442443c10883c005a4001d184c00f4010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 207565206 1250 207563956 207563963
    0x40305060f071e180905060907050f03040206160c03030914060c3003100509090f0a0803060d0c08100e1b010c020105041d010e0721230a050406050a020304 68
    0x5070801c0400059201e40c50103240e0700c80034088210f14406002c40d481e0700c0131008240e145000b06031744c00d026082c40f80018001d420305003004400c01c13016860000c0202102e410590603100a541c0d03608a41031190b503050855001000b0501c22440002810351000800003982d0302c2e00b41840845111108001e10b620034041e5040454100070480107414002070b40e10b2803a0440406007824107100314013030031200d40c000c44c4c2d88010b18407144014046801c100407255400120400204014044400180c0c0c0c0c4800390318005226017000400600e040d16010617180fa040c2e8046804206940c6414805031103803814580000e215151800f8040282400203000e101501504c1e81881d5030100b850044840728803c1109906011040000141c50894240324241c1c0f0701c40e031071203480c2a50400c4440c080c4c000024160074200080400b8420250300440b0f2201500d101c0888009107009009498029802520a41848202d00c0b40e040200c074941982040d84624460f00e0108042d44d184c20014041303000503100613 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 207566456 1250 207565206 207565217
    0x10b120a170408030703030501061d01080f041b0311030d09060c030f031104090c12020c030d0e0a050d021b030105040f0201080a06170f0c030120030406060503030708040305060f07 79
    0x34003080c07008055440c1c4042401445150a0b199000c192440e403181c04100c0002c0c0d547d0004200880d0f00c0701040740c5008900741c6444c400d510503000204102400b4056008074102c0c000801d040140c1074801400f4281803c080000300743d03480c204010402401c00000d0300078011500c00d07110304d81c425a000310541d42c0c1c81e02c440d401e02115840864082460a201e00c05159648c0200c1104c2c20001018000411085c00c8c081584442200024201c4140c4140c2c1714103113006121140a1550120607a00001d08031400025081c10b0320031a14588075449501078454003440b2056a5400d5012a2081070760207000c07045060b00807558149401c86c2d20032500a0110038980300800c0c0150321404406030444c4a000000c81d50b20b4403040c9141c1440c0b04807094160a601850701030740400c905100309200703200110001c004500c075030380002c5032192403d0000f412015000001a041000b5a8001000b401c0e000d021070351070310341c24580801151702a000640c0c0510643c40041c211804000d404d40c8a003c4a0b07850 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 207567706 1250 207566456 207566473
    0x9050105101d09030d0f090510060e01051c06020316090b040510080601020f1209030d030b060409110c4606020307030e03030f0703060f030503191b060b03010b12 71
    0x1002e01800003401500d4240810010101c40c9082e5000c2c5166521052038005008030349454503516081c503888246420908000040180798112204036045650540f401508a6604066103d03c101c482074020300342e901c08800c0c81001205402240042c01d983d8940c03000321916a000103c05020380d1044640c0310740c4406140302464400c0751115042a03060044421002d01903e4031800c12038074208880c60814042345500092404110200c0c80b07a540e170030104000c0301c001c03001c9100f40c0315a0003407141c3c541d00e440b010300c08070300520700300c0e0000c015130750a903040004507090400360760a0407440001c408079100b200d944c030300c204503041078070094501290044601580c0e6828000c1e40000b4160020726a68003100000b441c070900085115807511a040c55640c5080d0f000541203c080350040c01003801051803e00008a000041300d40d00c5031226071000040f48c7d4500211044c007000780c403103801d41e40110b0800c810086580c014280400044009014114507001401424442c25000b0840da8ac002c141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 207568956 1250 207567706 207567749
    0x7030e070e19090f1101080601030b0a120f0b09010606020706140d0b0307050d0b190606140d1503050109050c091302090a0f020703091a0310060e0f03100905010510 72
    0x6000c010b40044070307808619000a911248900140301205503108088003803542c141d580e2140c842c6038001e4003400d00308803c81480c2c020800d00c440d64002c0005984901c1c1105041c8400d540715444081c0d40549164098604a00e14034060540c4d4814040907114950307001c034a40d0300468a144805004c040414140101f450160303000e0110400c1041e0036005020001c14951503041d03d0104207401412510711b607091000440c80304074901c00c5c100d04150318014007440300a9111403998092080000d155466090209225009298000f05101500789088000041203019002018024041c805880f00038542034280040310b41c00303c40300c00541080301218401131420413080d5401005560700020104040d5102100b01d80c003002d802e60206203854010031030003000304840301c540c01000c0c11050540c10000040c000d912850b000322400d00840d400d0039103440d1030b1050100f03100f00c070080032520780000a12041d070041101d82025039180d400c0a0014980910154004040f21040d1042000510b814903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 207570206 1250 207568956 207568981
    0xf060311120a0902090a02090108181f020909010e0106030c030e060a0c0309050604030c05070b0403020d03031a0d0b4c03080301090204061706010f080c071401020307030e070e 77
    0xd203074046041c0c2d20107208000d40c1722420402d00c50210b140005940300c03140c60001d05103000017000c0c800030000f03103000022800404102269120280550b183e4142401418840617010340d8074150340108500c400000c012660031400c2e4100d8925032400c000200c00078000300c05491425440204a600c03040100da84d9200b01e0748a41503001d460f150015507071515580c0c00b402e00320191001c0e80028092043c44040c0901840310000501513039800034034251440d03000c0346604180c143c024050660360455061702d4548440704c0041c51400a01040581c4441e103490034003200c0035103516017031914481010b1000c280d8074540045003da13180b0543c55902032000720702000c4482d2500340950b006e411a001000500c440c000c3c60103802e00720030168031141000303801008100c0d1084074180700c405050503c00380b40d03080b102000d146000c0d403410b401e4555401a2181c1d030340c4a404c10051441100c07074008440804194040c50041d5620f540c24000d910900392440d54a044070702030b000c01d091842020030701010074030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 207571456 1250 207570206 207570211
    0x3020d0b0f0f1003060b0c10180b01050d0206120f090f0d05030c0706110d14060103020a0c12030204120c030b10300f0602030604050105150f18090108070f06031112 72
    0x1340341c0800c03074a03110f0301001801e41000d400c6181c0ea42c07208005104001d102d019507035031310603a590740000b05a141c1e181c05040b0b00b8184282c6004046060b5018190340742c200803501d2840402c000300c002400c001e1681d00000e0002c03100c4007106d00415610711003201000c07030407240c0c4216603500e603070842e110b188400c115170b0301c454421115180d40b0302d01c0750a4440c80001038402c14003803540010324010549011407500800429071381c101031041040d100c01a4200a4511210707800c5481c00c4d5020300b00e00c4e0700364002c1c807464000c8503c604040965200b000007400101007640d20442484107a0380b501860f0032210b4250f8060340000d0307035030701c64841c0365040ea0011800003003a503c1c50301c219460994071560700c02c5d80e50040540d00e103500042007102c4c1d0b00b014010f9034018031054071204001c0074451a00a018080c044404205540002d40c44070048001d81e0701d0050098020081c00c038950756900400d030b40729001c0c0710301000e43d0300903800024180c0c003905c038400e003580c0c0075880c0618003170185d06449034490f0300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 207572706 1250 207571456 207571489
    0x608071403010f0c0512070201050c07113c030303070804080d060522141015140d0903080c070507030209090f010504060f0b06160206031b0a03020d0b0f0f 68
    0x307600922080551074003130f070059050941c5a80b80d40b042050840d40c52088010441c0003507a04010600200c46819002c546800c0d4009c08468001801c4200042c1c04111080303060344c010300b54a52803034190300710050704507043c00582180f0b0001e110143c1410303142d00088030702030042140c0d100010f0103d840c4038014031203a1110800001c00f86e46400c00101c003556005000558194054100a04942c8a220303c1c10029650315607812145090220107403065202c2c024402140d07400030b40d100d445805024070b00c011014523107080340c4400702d450f0380d0002004054419800074030114003040f13000310740e00d0031180c07840d8001c07015080392402c54003400790b80840074104082c9841180e403440304200c0284101030085216140c00702e06000c64500e040700341c540e00c00029109107010801c210f400c5030168081c800545c1d056409507100d80e24100b00100440005030000d04584000407580e4107141d0542c000c0c620040c030610200880c06010382800f11003124140119080300c12034020841c0340c500560004407031200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 207573956 1250 207572706 207572711
    0xc0305012102131112090a020a1e0503010e0309030105070503070c0f020105070b070806030705030706050d0e0f120c0111120711010b04061d0109020a020712030306030b07020a0312060807140301 85
    0x45562818111255000c90035030f080d01c00305d103000b0620001d801054008907524024448a81650005000c04035030781715013654241038403210007100305160042001080010020054465103060003501c0c3e038007800701c1511a520388800618802c0c00744040c0da0007544a03a40c0d03000a5125591010380c00c400f06502607051250500002c1c000580b10350005100d00e240b40d80702c414a0600741c0034549810710323940049100b600080414480c241c1d001c000d40e1200c000c44240407450750356900b4001e052140403503085072580034102c08541c11400003001401040b00c00c600800640b00350900c8840c5074010000c0300c4102c442c928001c251400e01c504224900503102200000d00008040006800c441181d40424800071240c08421005855998201d0060000310019407510060f0a0000d444203281d009004440720742071100c00c180352095020700051036000080348054207040001139501d08446504800051a401d0710305540b082d01c0c050b5008407000c0d14001d003403650038458110280190000020780565 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 207575206 1250 207573956 207573979
    0x60207060e06190c02040b0f0d06020304060b15030702070603050421171006020f010212070c05030919240806060f0c01050f0105030f010e0c010c020105071a0a0c0305012102 76
    0x10022a00b26a02540d19110100344c1003545c4180815644c2d11a580e521030209420500541d8440b0b543d0080e80744e074840b40c01a600d984510b0880c00415400c0502d0381c016072150342e4078032868031042c0207500880450b000c03902c903181d890f6421425038100f124018500d15528050301858200721503090142c0c0704a003040f50b07130303a038000750964603884040307540011500c2c0f00d42c0708202c1e0907010b0044064030808903009601c1c15030010030700107503468050040380401181050700000d01030140251644410018069030f0609640c003008105100c032030049400e80500040d4580f0706c4525000e000103400566103440a1541e111001c01c07000750040c0c0341000d01c45408105030302d21030300280b141794400c8040280c9250b4950401c4c00b0b15240c060101c50791461685428202583c40e00c000450051032078092030f020ba190156840129071500031244001c0110710009941a02c600601504d1441418504030030480484504411019210284528142c1800440b00780c10340d08402211040d210340082c004118a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 207576456 1250 207575206 207575227
    0x1020a0609051f0204150c0c03020f030a0f050604060e0c0a0e0709030507120b0c0f030103060902010e030d02060f1303091e03080403110406051f32070c0f060207060e06 74
    0x2540080f070b100060b164001400d0000800b03405c4141c40d035201c6498807503542905651441e003c980e0601020344226403100042403030351350400007000700c260b10500300c003991a11460510744c1c0b9241901c0488055050280d582000c403000540340081040c01040900ba00b803405e05400a1004003030140d10800041d020003001244003040540d00034600900c402d04400070314240049121005824240c290008000500b21a002c0030305807030669400410010301013007a4401694000440a40343e500342c0910000294042c0c1c01044c4c042c400c004207103910941d82e0740c1c000c280c1082c04041c0e03002004074059903810310902c03251110301a0745400c002e510010345d98403511000400d40050307100700c07050501444441c103141001c0c003521000348001c4d511020074210302c0b040c902000c900d83c0102c0302008030b8a84403008030780306282c2c8071000081c215026003100103480b000e4803095209140a5440841c2d030580001c800481d10006400ca40c1d40394098a046030900c4070403a0112412052135034811010700c0110f403003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 207577706 1250 207576456 207576493
    0x1210c09120822030201050a050306191706091603031b050a1202010e0a081c110c0703110f01090b03040501090515040210110c01030b03150108060f0108060601020a060905 75
    0x102c0c014145140c481802c00310024905080f0b80409880110031101000140d800c401514041d07070140c100aa2207644d5440070440e02100c40001010105408c4400203010b054440c03086140c0541c401652080d039107038007425aa540043d103403000852403d5200b00702181c820220b02d46109807007a06001c041c00385440d8185400c00803130054403070703143c00c2c99140d100a40910499003181421805840c0c81400e0340c4503030032140545c11010004800d4a0020641a12035034080c070a0302110b4105a0b4440c20040a200d5079002030b07010465841002c01d040004078034104d0001c10840405075942c900300d5003411140080781c0c00c0a8130031683ca40d2501c0071000016810321030707661580600d08808150b071900d801040070320f401ca040b144080c0036003107102006941021624885003902800d000c9094010039002c02d03d00f200400d41e40301d540b052100003080d0220003240c0280039080c406540c0000b03980311130a450300c07101c06607000c60142c0d204005040009003150080402c46000e98181e694270300d55180c05030306 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 207578956 1250 207577706 207577739
    0xf0e030a05040501081302030601090209030f010c0e0103111e1e1206010e041505060f1b010c08160207061412040309030201030c02150621070f080c01210c09 69
    0x801c0000c5030620003541d10000455028420f45100c1c0c4042180e0340100362100c02c1800740c000041d8001800000c1074071304101c1c1c5607905c4450300c020400020412002000b41c4000d40403030703000a0400e0242624025100142c416440f40c0086101d0401300741c1800018960100c0f402c005200503006868091010b468058101c24040c0b083c0c81d650382c60035200042c400300e02440054844e9242607a44840225030f01249000d075031041d12816511100750b600c2818902640d0b541ca80c4203000c4110300c8400140642059064941a80300c82c1901d464005000d18985920401d680059200325000c116036440742d200c0c040c030b00c09942c081c00c4c034000141e14031001d4002e045500354040b80000b4420021964948562501c0f03905a00c09000441d0708000b1003650540b0282100c1d2251700204610b041c4902c9011040404101cbd1030100d6002955998901505505521400c600e6000300100409c15502800d4441d04086280407804052051390341002d0040c07a8019400040003075110303000c0b4185280d4500b055 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 207580206 1250 207578956 207578977
    0x145080303040210030507051b160f0806091c0309020a0504050429091902031204120302010606031e02071a07030905060a1812120504030f0e010c0c090f0e03 69
    0x190380745401e0050004910120014204041c1b0345810015066402010343e02c400c0110507041d010000121011807811081c1c40b02581d0324940241c0000702c0d811810410821500d48909680050b9251030f14a40c0721450000d45509015401017401d040c3c92190b4000301516200810203a2291344030f1380401c1c121202141c0841e2800361004031800c00340e010004040788038a00000300103e81ca07101511a4880f601003140ca80c0f1402034104007000c540e41031111044030040d030b074419512269504100c5041400c1900b059025500c0e005021400e10310a004440040070400e41e10050b000c0395114440081d8080303e400d6070700c40403e01e0003400c61007586820314000c280c59900486c4912040c2882c0307041c46005444440718a2400000f11050070490000461242e0001305071614070f0301110050340c40c21544d20509103124a004100030400d81c000445c0f8401c0702c81507490103081a0301e0001900e80054018010304403c001c07441c104005000d64001c54103024840401040082d4006c03465441c5030401407000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 207581456 1250 207580206 207580213
    0x1020408030d0c0e0f06040605091c0507030b01090501080c2107090204050a0e01050901060f1701080d0f051602040c0509060d0207020316150309030e06030f1005014508 74
    0x2480c11a0700040000c04d40d58200c42c0c08140101c00030004456204a21942050050203d0b00c5085036540c410305581a1644003140300c0b44070028540591a403010740001c5a03e04210400070440341a188038950603520707218000c1507120000001c002d02c0c01146c0c0c96040e8415440358172840e03007a1013071103d03d00802005c1400b40e03c850500e4100f0103408981e8100a580e100140010000d9030380302c0150350304441d100c1c00c21088180d04188200c4085e44040720b4443c071001c41000008955000040300020000c841d506d042d00e40c0d264034421545071080c2080280340001400780782c0d0152800d940088011034490030401d2901c280400132500079000a25101c0d031141c0d000c6190f206504080c401e901c20f0b44002a090305a403410006070764441200c046070388003050ba5a5603001c04040c01400700f89000b8800805440d00c03454459460303681c0c02070403110481c2c401c1c0300c15000075007940201c00f800c415200940c25102c0700203030201c00e440f181c41d01d0311020610303541c1c640000071410440c40c2060301030034500019 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 207582706 1250 207581456 207581471
    0x5030d080a060501020c0d0b040305091801230108040311030c010e010e0c040b0907122a03140c0d0e03091507050c03030a0e0d0204091205090a0b04050a0303080901020408030d 77
    0xc07610141e000d0f905540003818060765664550b00c1c20702c1c400c3c0e0b0015072141e403619207040803100d500800786a2a08640111128800058400c0d401e5048079403451002005c0c5400540f0054640302e242c1a150100740700d8400300d80000e00800d004244800d10404603400d0a083c02213060035200c101e03800007000d07503456005c80e846c1d000610200f41034860036102400f001442e0000f08043d0307000241910704201c512030707054903103600c141c00c030300002c0b1210f00d821003e042c1c2140880c9994612105900086032404912a001545014541d80300769108604a41408822079039034001c2d16441a4015503800100030812044d92070441d4140b0400e6000700f0b15450360043d01d412407400511005441c4a03a00500c5040c1107654882d20002801d8019100b00c1050b034180d1012402400c0300b0440105100141c0307c0c60f10a841d8000060095402e0896807079020a6032641d40600c0380c070560050a80241e012042440030038042c03d4080d801407410343c00186080c0daa80044e0303045d50482c1030601e00c0151501d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 207583956 1250 207582706 207582721
    0x6020a09170102030c090d06020409023108031603050405040507090f170316020f040c032306130c090b07030c03030501060810090e01110705060105041b1b0c05030d08 73
    0x9074501242075201c000c51440c200680c0308422400742d0340c1100e00c601031507451002044126010340d0004d15802800390b44170b441c0d40000010503503290440004e00d010420060914268240c0d1f02000c656428002d1480c14202c80c210000401e1100c0703056090000c03c110010f43d503103481c0300d494815141039030b0b80359025007020300342c416010296101646c4080400e2040340380850102c1280d02825952002180852031407002c112034130380e01040150310a281100003082c494054020f4000041c007400c40b1402030b54507030940c941c0c1c0102554210f4001c01a20440d500041042e803005d4004409410602c4030f0507079520f1b02da9955032001400b1400039007580c1c40c0000b01605800b442d4090102408c0c540e01a02c0c2111031041440f11900c202c00c0055101c0900181d4180b00307500168008980b0041c01745c0c1c51100d030500917903a070f030203108490181f480d00c0442140d0364420700e54240503101c9a80c0b80d134080c00c2c0c09075000548440c0300200741c514681c1c6920000b1581d60801c08168448034540303070960503141904 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 207585206 1250 207583956 207583979
    0x8010c020d02060106080712140711010c0207090e03090a0311040501060e0906010f09090f061503061d0a0f02072010020723040c02031c02090f040507020a06020a09 72
    0x204402503600101c00c400c26a0380204595054034541d10b0844500e90b10184200c1f12003200d0ba40b004082441d005000307000d044a001c10902c00e40b01a220b504c2e00008103641c6600f00d4902c059594016044620284900c85940c1c04c032100e81c010860032079050440c01e00028451140c0c40d4011691025a400c1c0d0f00c032107045c0340c018180100018105241c8100d031140104510f4640100310a04004a0510403080c1c10301647c2c584010309440d10b010010b1141442e074480081a8078082c0e445103100e02000390f09814400e01440b029245406050a000b0703840c00d88001010700054000e24200792140c8543c2e01300d049510103030440c68001c07040b0b5110320900140e5907400d10484a0203030301944815920252403900012031008464503070a00e12092450801d440700c40102100515600a082ca10025402a400000391030440c0d040045987c0c02c2c010100c0c15070403482030810b81d9800202c0000360004d1841c0030750103194481164010b403200f010080d608c0004a03442103107101c0115000000034880c4183d5070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 207586456 1250 207585206 207585221
    0xa0501050904120e130c050a1e0f2010050a05250e0301140405010603050613111002010209041d070506070c0323010504200315010515070f0501060801 66
    0xa48140066040a40f142890a2880200c16090040c012080c1695448006145407084070a000402c8200b8500350010b207517510940001b000150a0380c0100846040da000e00705140045440d07020b0b48d05440310054881180f50203000c0c00c10b0b40040301455103894140a40a01c000b001e032000103851403d040d030030084800103003c00d03c4030301020072032800141c03190214142d408698281154040603400c0041e000d00414454560343d5150b40c400d200401c40150032090540341b0a030143d40d45a510707110001100100c1c0c6070090701f075020030011b9202d9804e10148511741c03103032a44005031900c00c101d0045010749a85004945401e14510707412a41100148031801c060301048030700b603107880c0407074031215410303171090101421681a120703042c110400c42001886900c00020020301080ca0641080300110103d83c5e2441c0b03403c0c0d11303090000420f1401160f0490440c20101c00c22705144d081c0f000388040358105600c010341c426402c00445c0e010130008841c0d02c602034401c6002080a60800f1940344c01e40b520b5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 207587706 1250 207586456 207586459
    0x121317090307060513030503070f03020f060c030c0d2d1a0607060c03021209030d0b060c0a060e03040810020414010315030305030712061511120a030209030705180a050105 75
    0x60100e110565800314032041102c0891511603240d100070706410b508250103600040c102e1000281c00340c200016062505011406a02901c0d85411004000e075101c00d41250244091a41000020788403601d030701c0a05a50740c8111000502d108155007000f070b01000b400380c0250070b00d52540944118250301c0c0a200c1c20503802c16101070f01a000c0c040440c0040c0114000200403588481c500b1150a110354103541d01c800190300196698100a07900039107035400385402a0b0040e0509510143c01e041210884450351103400003064403520070b8039040c0085c40f250310014503070f0004101c0001c1440d0f0070000c0020610010100681d03c0b440e1a40120390902d02050340390516003400e0f2030250292070030075880200d03a01410821703507075904c3c1d40b0103d811035440c400716261700380340180128a100404441e04200c000725150341041402041d9800c0e980c5074165a01e030041c240401102d400c2901ca134014241d20600a422148440d4031740340090b0161190090a8982c0034105041000303c040138000d00340184070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 207588956 1250 207587706 207587753
    0x1e02120705060417240114010c0b061c0506010b04060e100c020112090f20010c050d0c0201020f030406020c0a1a0405011b150b030d020309091b1213 65
    0xa48804206140a144100b000518100c103a40c116113030107001e0040d40c04a90844c1d2813004031304800060180d1028050000300d02070010090180e54041c21822906582042c0310940a46d140c2e0100402050b890b25444034141030501108001601040003078040c2864904079a100da09000004040803aa50b0b111881540c140746c07030020707081c0c0040e40b0903850354086c64101800701e03030006188042c000440c0f000f0038402014080105125036010700d140740e040100a803101580941d0b0045564100c0d50300e000d44950800903544c81e800c1d0140d840724034094810b0040ea00074a0036004040d0550304141d200c5000740e04000d0205030f89207400d0340c082000c0c1442c180154607179004030307a503103802d0f015502903d418040071100c51004084140c80e103819640c0d101011300c650780b00320101d800203018900d00d228080c1c49908a50f1101c54000b205690b280c1002524100d4aa0707211800d02c0f5030b02040b0141c2500541c1c04000c001510700c2c803071121a2140b1140c24240341c000050780f40c14102c02c0844d0440400c2c1c0c04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 207590206 1250 207588956 207588959
    0x1b08031c140403200607020d120903090504020a02010f0908030a060503030a02030f0a050405030a050d091d0604020313080d090201170411041518060306050609070203030a090503071e021207 83
    0x551520079411540516180300e6054950085100000101c0c4c2c201d1010300c15403040100d20b0381e001840103581401580c602c401a030400b4000010b0300c40f0100c006010a0280405214905041d80034000e6001c00c1d100114034071300c00102040480b0710044099450080010400c01080040d000310300c000d001c240d0040d1310b0098030580084d00e81c09000c480c0c1001c079a000130f00c5a00f4910450984010388030003810313200103c00c0c80c42d2856236000600c800c4008100b80c2480040d00701c44841e402211003400300c0c0c42c0003e60f55040f04100003940014060400c0c40c0c0d06202c03c0c004600e004001d0700105000350000184501a0f0002401000751034030030701d2040c241c0004100008030b03010303503d2051039000c4e20b02054031000c00d9016504000d40d6000340a2a607114840901143d40301d4215400f00ca0003241d0402407901e82d00f06001d5074101c2210390342c01580c020400320b440c0002940c03052402d1402003082e0703414400c1541d02e64000c000c08212040c0900e030000351780c40035440d10080001401003031070700805078030307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 207591456 1250 207590206 207590231
    0x3110c10031a10080406150e070807020c04020301060f080406111306110316060515060d060509090a0201082a0d0501150903051c02070801020a0305010f0e060d020d1b08031c 76
    0x51301c01040141803685944044c049020b002c004500034085070030040e620741ca442c9000405201045881000620483e058800d49040510840c0c1c1a54142d5681c511504480b410030344001c4005081104e181d0750340c1c2d0900081000745005005540503643d82c146100345026401800807078500400307200c41d0400c122000f1808052440220031541c417280200e10369071148090b01c510042480801d40207180044c4002140000e9885030b801d8a2084a030389990340c40c2c0c1d2503038a0f96400e0752800203000c5040c01c0085544101e20120000840c240c0301582c5c400602d0111000d1401e4000c1a4070840180d00c0714018003c0c0001c8000d10204821545402d80185d440c40d104d59507510613035105820540002007243e000e281c0301740484006441140b0082d90360b0300d13190303c000380200780c03d2192018074504540d0100f480d40848400500039240100100c0e482e410507004c000005210070011209191411050f40c6a914240000001000d48401854450340f031000301205030345a100c0c01c00f0840b454001078a045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 207592706 1250 207591456 207591467
    0x30908061314100e030306180c1b0304090609050615120103141911120609071e05120714040e060a0f0b1909150503030703110c10031a10 60
    0x200d42c00c40b01c01c1500140782102ca40c00e10301c0c0c900c8050f041a0802c04d20b582e5204000000350b005180583d51b408411109000401840304143d40903802e41c3d0080106801c000114510040300b00c03025019a46496640d202c080304071811517000c0b00b0320035100e1040020914151040c03280c40b8010301d11461038003003030701d01070507500c00305002c0100980d0940301d1188079000300301b007036481c8145104c0801071000581d0a1102c018645c54600f02d21407641440e00d07640748400810300b03e00654820b001000e14a00308580c1c0e00405032000130303844501c82c02d081c00003051782e2030f0000d004031103030307107001a280305070414050500d509051f092081c00365041800d4140c032502c0000343c02d68880200704000410301640d90015010f046001c2800b540a440300c620300e10318014203020001140d0804108020072034862101c05050140c5104040c1c3c15001449030b0350200b800b4025a480660000c1c0c107582c229104d41000440c5c8080f0002c0150010b90b48514855040c805094001d035a9601299204200801034800820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 207593956 1250 207592706 207592741
    0xc03090d080403020c04180b160206010608130c0905070909020f090906130203010b040e0601020d2f01020a02010e070f050a06110c0303030103031d1503010b1312080703090806 77
    0x10030120900142c20715201780b00b01019500020401e2151440517511540c03031011082d0192082c014850200c0c25840007004010314100c060f030080c02d0b140e0f00c1c184007560b041c90018001309500307604403198000240003410080c040c020038200007401d420300400040182046030031440c521841041001107842000c425980150001c54000d0429510a004903440c503101091303503e5400d00202c008070300a14071030003803c107840d1541c28844460b0b42e01d8004a03a036041d40c3c0d0360340e40450b406c80e00700c03500462019284800b1500100c0c044400c2c0c48c3c402c1c902801c91344502140c4c80140d41d11280703500d9400703007409090018207010b08551401c506207000200e01d250184681c1050004024400c0401103003400221020310340141940c1d113039039580c1409000440d180e8908201304160218808080c54241500c004e480840b842c1346045a007001400c2c48141e12126890005c4032030420005001d143c4480c0e10303880503200f0002c2d291110400d20b4003400c1e1803020303000b0181a4210b901040300d802c0ca030104400c07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 207595206 1250 207593956 207593983
    0x80d11120d0e0a0b19050606040902090d02100e01020c04060305060708090f06010f240206270a05030d060e0108030a1808062502030f031f1206050106080c0309 70
    0x3903480c50914010001030078440d10110080c00340b655503405004d1848140c40c403800580a2140c20b01e9000302c0000116001100c00d2580020207001c02d21400501c1d5000e81489680580410f0b0340810307a80000da0040d0b030203804240040c2e40943d101ca5076507411f000c429101c02040d030707051241c50b003141e8516031280f500400c2d03001001000c1340000c180402c10440c0441c1c089a51082e00c0306561209054000340c215402003200f070702d01600c3c400c60b045207803142020210009601034076490300c4480c1181006812245050b0101c10862035504405105215105189104800840e6241c10300b542034819100503030720550307507201204010803510a010040b100c01d40070500c0e0004586040d545039600080868000070b40c540b14100400610706050081d072142c0c0b010f005403040080450302402c1b662449940ba00520030b00090001c5000c66032405d40799440c40780c200720520749258440e04400180041c441c401d49595440c3d000400405400a813250b4000c28211001840d5152040384990764005040c0e038032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 207596456 1250 207595206 207595243
    0x4050a05014101020c0a060504060207052710090f0207150501050117090a08030106030506040f02090d02010e1201050f0403090614040e070905370501081305010603060c0504080d11 79
    0x42c0d80e40c1c800e000800e0003140060001c1c0c120342e21418010f106d1340040c000e0310054032810b680451180382400038521101a07685a040d003026402c40300c440b4414003d090044034001c00c81d004909005580901500c0009070100141c0754825800c085042001c56200401c965151200504c4a664000220050074881003094a00c0b278036001025450288550005001080b0120001c00e11640c583c103d44c0c090721048609000000400c0038003002c034800c200d00c50740c0c00144112203400650144480b600301483c01402c162460701c0c0d0031425400c1d10710484084c5e0307103400c0c1042040105508016154041c0c0400e00d0300040c01807a051040f1003510890155898262040c000030f000c86204d41c1310040506406005001c59400c0d0524a50362143d898070082e1401c01d0843e0b1900c602d03c2103a5000c011a030051f51400a1603e078491100e60340c0f018400c1c2610301d5521090301001140580c0601c0f40f01680307645e1100d644034513006015040c0401d8008403001c10500320f4084000d480001001444666180b03020f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 207597706 1250 207596456 207596579
    0x11010807020a05190b090105010b18010203090306040302072904030f061824020310090b0d05070303051803010203090a0615051504080106060801030f2004050a0501 72
    0x1030b071400c840d004004200d44140a100e801c4050180e44c2c4c407100510402401403180c542c0c6842c2400d84009009401121809020030024000040c0144007848d0301801540d1510040740301007400c001c1e04440c1907015a10541040103042d40b484c02c2c2c400d0703038059418005917803011030700040c209100e684000381c000011b0309140403d1002c164440c4507101d01d4a44103100070401c80c034003003c900d4030241141c5211b000d20295800f882c14103000b2a4820501c3c5201c503401641080101801005403500c02c81d00141003000c1c86000a50802486000c1c41c000d40303c15031511190305201346000c014400d580c0c043d034018024064415000111400c0c0740360b0040b40410180751598944104e00041d41c0070079840082158487c0400c502200204252200c00c0b009010451301d849080e49c6821080c44001c102180740700110b0007141a0402401e0600304010031382e540c407440c030b4000070143c13003095442d1f2a2a0741d5407001001002c200f001804006020b4840081842c3c00b6020300b04100d0a2100030080400c0d9100070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 207598956 1250 207597706 207597721
    0x17040206030a020f0d0b0301050a0e06040803100b0a030516030209030312060f1e12010b01141309091202070503120d0203150603040f140304030b22080f1213110108 72
    0x544e844c081000e04007507110351a100070f56006d000d9401070140607510b440041a490032042c01208107050078100140300341d4442e9aa1010f8651000303209e0340810071620404500004928000d005a0200340e40224003400c1c204055440001c540740c0000c1894410004040552004030a41741c0501d2041d200403040d56604011443c4103407103100580d40003a514664444001034080c04400030102a2900340500754401c0c296800c90b1070b10f00049011901e14200802c44003000401008019603100c86c800c907055a84254a00f41c51810008443c0c08205003001c04ca2180d0401861000740011002002802c0720f02c0f802031454401c2c03450741c9122940001c0004d00c1c004000001440c110406407100d41d0740d1401c2e0411000905221401701e440c182c60720084420140c0c00000c0c0e509503500020784090607180e1036544030314070000802003c4448414401172000c0b9003a00060407034000358084c49591a404240c000c20807240040000d0107003151050607401191040300c1d034241072002030030003045a885441 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 207600206 1250 207598956 207598961
    0x1060228030e04020a03140609070903140106090c0f0206280c0203090d0305041a0306090601030b031501030b010602010b040608030d0b1c050106180b10031508061509010617040206030a 81
    0x100110f400a0001801162059042d0702c03802510211120651640d1500020410203d00c140c0c0c0d6680010004c00051000c0b4400004440340405800000910356a0f01d418a1041e2003080400401060b26641c1c81c8403502d0b0188201079100c070600710680c031110011440e00041c1e26484035041c44450713561144c14800d5000700125049401e00070b00c3d805154605280080c413070361284c040e242c0f9801201c10703031034003403951002030f240903007030041c00e5080c00d40c5c03003200443c0100101000190301d40f060401c1d07d4020345480d1803680c080d50042281e041c9542c103001b00070b800d40340c001048900482c600f403c1005101408070503682c0480303100746c01003800100301001481040e0f41c5d241e130314103a5003010180e81c104501581b0403001c441c20000c44034102c0e055459040200c0e0141149180c1000404028044141c440c1c0d03c6002402150a00300d04082e1310b505c145844d007042214900d10103c0c100303095800c1454108145401400d561424250b400030a4001084681000e80000d000e1030020000c0b5440f8607158 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 207601456 1250 207600206 207600227
    0x111219060e0f040c08060106120f1803021522060c030b15040f09140f0403020118030201050109060b07021e04110a05030f06090c160203030d05010e0f0106022803 71
    0x4551400381410b040d02480103004054804445020000b407000407440400708505041310a552a6a00b0f450f2058101401900200014096465458007420046030580c00018072090190f401001f21701e0003510341c0003440c980a030a846012072080e21441d038880049943c0e506099015034003103220291030000740c000d030031014240360f4480c03c40121002803070382c040c0190088680d41d081d1103041d643c1d90421001211000b50f007c0302a199958001001c0070810086507030098402d20001800304564912020508102001180140d4460004100d0007d85020740e601400d50303c1d0b41545003064030f60001d408003134440304003003074616a0f1100702c501c0d81d2241d000c1040d00c5034418845035100820080103100790f00443d21980032101d42d0380411464240301039150b11580b0402100d92805200e01801404444000000c07a4548030400c0b8090002c0302600820b8006d107010240d20860f8100500211800c44050704401d0440d4020070400c41c541010006021141610302c0c1c0c071400c2420705003401c54500c0402e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 207602706 1250 207601456 207601469
    0x5130f06030f050d030203010b2d04091509062103030b361012081c02030402010f020307020f010c0f0209011502100b0619050705011404020411121906 66
    0x14800c00105100c07401c00d584030302c24428000d0b2540402c40c0b040503802c901081c01002114002070010740c40c0340e4000c408042503048440900320f00b010606007182c00c2d0f941709422055860744c5640c0700d01400392044840c1740103468082c0d82485110308240c0c40d90401183c071455203c0c0c0701000c40c4003409260017544070300f032a102d01610400d12407a64440c3c41c00442220084200d030411030180ca612078004604210307008000d10000381c24607a142659400f03d1300e001e10380a4074000c100700185c1d041e0186490744101002d100207800358580c038150002500c1100c0b021100001c0d07400030070441d0300503511100c01d00440b80c400d00f421600300c030035401c00202c0c440420f80000d4210b20300d000041080619114103900100107a030171070311100d1002e25a1301c00c0d1030644046e00d170419818081103d40350700c20030858141340c80d1f03403500074101141e544230242503d65009421035640f070719205200c250b0420b402608214004512400e1400825240c00e4011840052104200e550481d41400d00c058154011030002c252 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 207603956 1250 207602706 207602711
    0x809010e120105091c020f070b0c010e01020c1e1506040510030614060a080d09030816050a0305030103020f040605030a151506020c090709030312050703090f0b072705130f 75
    0xc0c208130140c2c0c0ca070384010405508020140441441030720006001c039001400d207014005452800a808260b40c1100040750101c1d5210030710034611403024070242042549150041103c190a52000340511520808000141c1c001400c0c10200303480d00205550009810341e000103880d03942255240e420400b03500018042420010384108550501c1105405001c0c120f17034180c00f8950751944240d540c484501c05a01081c00d01c4401c00108445401403c2c0c081c00c18212461003003a260740b02800e00c0f1000070708401117603000c4014425820103036905900f541c03003a01c00f08202c500b0240020ba840000c00401801c035a01401c0c0e080d0005010380040e410200300700580c201007525210065290409c2d419028010b801ca070740018132441c400c01c40181100c0c0c140c1c540c00c00810550760484050038005242106160f150404000000c50314440c803000a400790866009030700740048000d0426440c500e003010300324400100d1807144d01c0c0030f80611049800854500c4001001c1001042c003030840351703450030f000d00d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 207605206 1250 207603956 207603961
    0x20f0d0609020a060e1020120304060c020606010e100311130602190b040f05070b0d0b030c031524181605070b010302060304060212010f0f0503010204030809010e120105 74
    0x22160416203940b8800c8424007962510341104032000c445040301e003640702c545c55441c1b04941d4001c01d03120305c0c41108480408007586400450780d16124400b10002c044800002c100801d10101c0e110340c00142c51684094440f5080000c002442d130396502405a02c201a46503036194024025484035001803041e000d00c60b2900321026806d00c00343c80c544224009400340f444481448526010003201c5140d200c4c000200d980c4079512020711124001c0412a00d602c1120004690085c040c0064802c500840300b01142810b25038052600300240340208034083d40c09008025031108601c600d1a85c06a58410007100041c484440d1300e00700440c071030341e00d0780080c61030800302c0b035034061518064803511814144440342500d815044500b0711070440e0240009212400510040c42d00400440e00705003e1000135043c44826283c1c0202c8007400c3e408020214a0140c042020100e0011814000e2408030001c50030300e403568459800c94407842d040241000f014102c0300c010350ba60303503147c60b10306100e2400800061 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 207606456 1250 207605206 207605213
    0x1062708010606110a0c0b0c250504060b031306150b0c0606010215040503070b04031103030a0510060201021c181401020711040506060a030f020d090302030304020a1d04030c020f0d 79
    0x280054083da8001a480103054110340300005035440529610513406c0d0f20281c0742c10030f000b5258002da00c510110740140c0c03017034881c1031340420502d4070b001581c920b2354101289070000b04030440e00ca95001002000046c01009140020700c484445070640101001c1408401007440c0f203040740b050b4010141d01100418482d6050500007603482c0b24800a8084820701e5101c403200b10242282120b00a0155000f0040e1a000031201c6a09503009480307424021a180e890160183c00c5402c219040347e0815034640c00c22000d41d00d5000380c3c5e0010076207400214500640c442c0030a40d89218106542c41840d10703032000c0c0500da1091020b81d10141d4004d036030101500b545000b80c83c003035440208207641c507940e00d840710760840c81c1900c0f41d0380c003501d4001e0890703203801c8a015080e4094007c43c440e00921070360034000d0000c0303004e050154095a610981c043c43c1d032444e0078030412000080c00e0304600c00e4212000b420302a05000b100e4941c2d08190142011085007140c3d10014007271700c001190395501310795010b0701e10080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 207607706 1250 207606456 207606461
    0xb040506010e21071e090506030c060f0d0213030506040c06050306030c040504020d08030903030106080604020f04050f0111011122030b043e120f10020c0102040e041b0f06080106270801 81
    0x50342c40f02c6c070060001e03442e000109a50764140b480600e600c044100a040800341a620045c80441d010010160070b03d081b9550307032071940c40303580d005649580149003048100b000071403003c0c01420190410b14218100540421f03501c0c0d03102a0558062079031000400c095547d20500c1040560340207890550f640380220450b80c9139002803040c0000310311008086400340c5018000c0c2e0b0766103100c204e0303030340d08092810082210600d0700311120380c1031100f0380d112951646020b014804030550a941c0e459030344d0384030b00c103152104110008035249820320720710180000340c465802d0b90f030401e030028030641d08481144c0f240a12100f40010700e46000980980c00a411743e0342403a100b0030040111900100440346582c855100c03c3e040500e02c0c4203400000000711040d006601402d601e0403140001410213469402441c0c5410046e9000d841c0c0501d400c403400c400d81c2c0d550045401608403082010503291410201500401060040350300340300c110840d10020075071038041081c005203060030352205030b40d5407008bc0f0300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 207608956 1250 207607706 207607709
    0xa0e0319051b0703050a082b06060e01030e0d0c032007060f020105190c0e04020d060906120507030320060414010c03060503070b0a0c080d0b040506010e21071e 70
    0xc40c407119810311101c2800101c0c90204503030700300b4007030b02c60301d00199100307440d5611901c0141032840440c0c100724111205100d144508108c0100001006030070300c1c9019003038000e1350700202d04050504144000c10580481c44c03242508160404070084040b6240540d1102110021890607001e0441000185400080c82004039060390712030540030056110102d090b14812206100c00c0103032058061041c40d00ca41c08000c001795149445102119800005026a8028804191302984810080c401011f00380720303110040852008190044009a840644841036840080c0c240320f22400e904031902d030580301c0440d4420343c1c041921901d151514100340c80240454003110550300c1e001c80203803003d0103441480140c40c2c1c018020700340c0c1482c01808038029400314810348204a02c5070714100000d81d03904040c02c42450441004507007503e0910134082111001001c8504005a052480c0b180d52140e0b17900008100c40c400010008224101c1d45074980500380d4000e00c00c0c81c0c03e2142c2c0f04060098058240d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 207610206 1250 207608956 207608977
    0x4050d0803150409080a0e0a09020a0315150206010614120108030d0c0e28030b010e1e06060403110d0c0801020c060115080f15130f0f050408030a0e031905 68
    0x32100024801440102ca44e40c0d5001442c55504000c1c9400c460b000d2441c0303401c0e00400924000c60f09856840703850580c1c01900318500400c0e00d0301440c00400781c0d980050000b40c0100a80560403501c130b208001e40e01c100603c502401e01001060b20722141102c1011117448030094108514036507074031000301340c0d2540287c94000c0700d145441c8070003680b18400c042490745da0345e00030200d2500034624440c090820541100082e0242d519013000000100342800b01e07030007085003046130501c61809443e0f41d01c0020068100e207445120440406c41d10303588a005030b40039660001704013108035a244000c101304501c50140540281d01408000600d2030b01500141700c601118401e48002b07999420401e11601c0c2c0c452118000b0a085400284418074034511507540302c00701050050050300080b001c100c145403040c003500d441c2c90b101c4100410b00107480c000c0e90702d0320390b030880c04202c985070075114082c250001038000800d003a114018444292002c000b541c00000c1440941e54005c51030f1003001d4426440319400c071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 207611456 1250 207610206 207610231
    0x90b010b0f0f161e02270115120f0b091f060e030f0106030503040501091e270e030301061e08010312021002130317120c09120a0f030e0f0d02040b03010204050d0803 72
    0x201c2844203440d0752001031b124421007400b541d0810046d40e048103600005d0404000503003824000d02c20090080c004098445131001035042000c3c024000241001050309804c1c1d01801550142c010701307074a03240c0413241c1034500000c045d180400040d0401302001d14100a039800c2103400710600201000400c2220800d88501000c0d90f07660000005070075528441030414000c001080104a4040e4403454480c810000c040070081554801300085070b41405441100b0303072000c80144807403600061903405540c1c1842c039400b40e003441750400074140340050000a0140c6610460318550900810140804041d402c0065403502540168a5a8a0758602c415a07005603220102421003030410110b568044480070b40740c020703a44c1c0061020842c0e0101503400c1c1c101180e0044850081824010241d460380f01d81201c9404030a04e09004010f04051054648100c00c900700410503952811030000134140c0c15500841c91054541c002030080c06070350301040d0480c0100380e0a0701009441401940f19440c0010384 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 207612706 1250 207611456 207611479
    0x3070306090b040908040504020a170c030114010804120c0c0b0c21030403020d0c020a090617160602030d050c0d021605100203100b030a0902100201090b010b0f0f161e02 74
    0x820051352400c110240158a040000b44000c0c200354000708240c1455040000c7e0600c550b0f03a0320100c40320708540d0101d5200b0302200521100e4a5140e21081d262824a812010741c146501c83c080b030009042e80c104203001c0301d00c0c44030040081e58030340000140780c0b411525880710156400c003900c0d00c00c0c145e240281010b01080c040d11541c540020b80c0e0003160554001d01d68050b84650985003000e005c4410381e03200e0507500c000117024025010311030207403030140a465110791660303401034602220102e0030040c1102d040c805010b40c80d800404e544140034a400d0106054a521812400c10301c210701c00500c41c280000b40c030903402603c0040c054074103172194003120000d0035044d208008074003060fa24061040e5103c003082012080c1c510146802042c0c9182c00101d400f034a40c00660660b8060b6a8100980d445070f40440c10300101410240c01011442e2125250010860700245188103010312104244000305403a03c1501c604c640819009500c858401000c68203004507251200c20f0035812446101d00d04078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 207613956 1250 207612706 207612709
    0x30b0901020703230d05040804090f1a0418050a030807020f061303030b060c01050103060608281b0e07051312020f0f030a0209160908030a0c0b180303070306090b 71
    0x310740c059501940c0e4054201040501803141c592240d8640006000034005c80c81110740f039201e000c1c06203102d000207503903a500d080e00100c00e54412210880446242c501c001090f000ca0f0300002c08280021900060222030904007481000741012000d4080e200340900141015040409540914440e0b0203c511a00c56180d03481e940f91000c440290321075004c2c0d141600041d010b50400e00700d50000810540c1801c00b421055800c44c1c000b64400e40b06144c0707030901082215030910961146034040ca040500e104080141e02890041c0400c0040502030079622040000d0726403c80c040241c044000070898604200074024100d8001c04115180810040000280000140d00051940740e018203c0c040266503181001144501040c1c40c81c0c041c041c480450005a0b0f4041809103d045414441a1600e440f10401460394030181c12410559000b000003884154020f00300344c0e40c96521170801415070b41c4014401506050400e0444140c0c4000b00502c845c80341c06800600a58150210411410107400c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 207615206 1250 207613956 207613961
    0x92c0c130303350402010e04150302130216060f0506040e0a021002010b0604121403070b01090203040302190f020906032a1c03050304030e150f0304150e0106030b0901 73
    0x21052400c410951508000190003402400b07030511402442e1094041d075200e0f071865103c4202c0721021a400b140081208540e00202c0c20582c0100613102009000303201d000c144d103065414003000e840764070380319017840781c02003150111280030f520104040182400707460900054040900e5001482d8103150008a45003010302c51500e013100e6440003481c0780b21554082c0003401c50b03582c1303000d070843d501c8038195020307500c07800d0007800144428810300072094680d003000ca42e0303d0b0307024450f000703560070400c080404203409000e140d064602e0400b005a03a44c441d032509034030344080400d444904190b100d400505104200c0c1c02d24900c1402900d403035480395280000c140c0c0303410140b48214030115441c0c15a0140d2001d4075070050b80681e0151036041030075610180c210311140c1c8204100c0c0000d2000080004041c0d10001045840f18141c0d01e60706c42110008040741207000d00c0e001d50070741c16400b1000074107001c45038070b00c03a10a9040c04d00c20407d40c07121444581c06041d06000075580c4030b10060204038a180c051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 207616456 1250 207615206 207615217
    0x30d06120f0b04020103140c07020a0906060f1419110c01020a0206250b161206060504090c02160f261005060d0501050907170319030507092c0c 63
    0x40c00701e000c1e0207034554800355180c030301802c140e0401d980c520f5900d0003c01c101e014540585414007019480350300074410031a10001a4210181460500c0340402c200b6400521302d021174122401c050345480d4250040c00c0d9140148600181c100150400ca10b484640101c040303800c003a50942502c802107040f00c01640e5450b050180250403400400040340e4080e203217100e031981c600049000c1021452030b6100c0d05050304060300d20403078580000903004840c581081110612403414a001e00c000381c507001d03001d4214000c0703101e0510110b403100c0d594a400e52090120074400c0551400e2441700503100c41ca800003000c418041c1058080580b404903a0600e011050350022400c0d4000400b58402014031604c0505000f41400390401e0182003002c0002c2c20a01500d4820807822004001492422904035201881d00d500070810350020024070480c110074544080000c2042d05010446444014048900c3d507090340c40110350000502c192a0769070f0300d02014120b00d40e0000301c0c01da91502c4012050303003035200b003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 207617706 1250 207616456 207616463
    0x602010e06061905130b011e0503070804080f0705010603030f1d060d061701020c1908070303110d06030302011509020c03030a0513080a02010b1809120702030f0f030d0612 75
    0x880000c00a1402c000c1506031030b40006142581e1984d100d000c5a0030068443d5890900c5460316001e86095a2141d001004254030418440ca007405840c8050410301c0f000e00541c0402c04071900003802e0016030002c0303c41a910380390b400c3d039079106c0a00705140240040c0c08110f0002d6056130403a03041c24803588003560004c03d50155040300390300700c41c01c0000e50b91111482c840784c00e4507108001002005084850141c2140354000b594402c001b00d0701e42e080185220840f0501c942c4c0c1079880c00826200720503181319035850b060006070120750a000d44c05a00500000b010601d0800c6008001c2550641105000354901c00c000780a280c0c6481181d000d07030140201010241c0e00600024079810090341100c0c0d00554003d0014000314a1602c1d00c1d001d561143d5410380c00360b912000800c000c0d00b00b1b0001c1d0210240394294503003041c00c000541540701d603440c184404c00304901040103815903505100e0003009080c20340c12215503881e100d5559440e9088210f0444002d4503001303000525030003c03801d203003000d9807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 207618956 1250 207617706 207617713
    0x50108120d06032301230c0702010903020307090c170603191a0f01050f0405070207090b01050904150e0112050a0305160b040602041e030b0106050c03071707020a0602010e 75
    0x1030112012005400c004112a0402e0301d51800101088400038a0403100b00510744515024020038609400d441050f0140c1c1c1c80c980d0b00c80701101c109022102029000007140b60415502e45031400103c5002c9003682003e90315000e840f4001034501b1039640207001021064886c0000082d8200f50070803985c1d81284c101d0707050b400035900d6944401a251906070030f00e00c580704440c840c007060399290b80212011501011034414810041c0320a1800300820015038600b158280070030325080700001d49034036042c414911016106c40040d11182e020350180e402505e4064030400c03181c500c4400e0041c0104540c0303c0c03902e5102001001140001006e05818611504003000f003e9001542d41c04891641c400c800121283c1e4680010100003007100b003040c2e0042c0d000e5000035032158140320020508128240359503090106c103100401c00502d4429407503044030200d0038104d8a802d11410340600314407a5950003480e10301445d04650000b80b182c000b80c07000500070b07200795041a40b0b800d03007603080340c8064642c05203907031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 207620206 1250 207618956 207618973
    0x203101e06110f0703081206030604021f26011508010605040e0705040801020705060f060109120f0303020c19120f0527150d050a1e05311401050108 65
    0x500442c601e6440b01181403c450959105018850401880b500101d501c0079000840e600b014654035940b6800c540c040b0060021801c1c154005141004041c44400150b00c0c14080c03061098000c038500c0e100ad01e28001d010b85906003011280c0c0450209004038042d41200c0036508420314800c3d0f407014161007450b29428903080c1024004000f006009190804200b03042201003400c20080c0060490980f00fa402400642030442440019180080c501030420289800401c100b44030a001c4051440d00800004018581410308401070b01c10402608464405e40720307229841c4a00c450040d40e1b01d4021900764855183c50b040c203c4a2030b6003440d464001550900162914030124401c4000118804031044840c46000c0003107030034206d03961448298242e02250406944041d40101680104000e0b800c000c40c501e030304410b981e2200d81303607501e00da030996030000100181006c0d81c0046c2c5000b00442942c0311450302c04101041c10500d50400c85135001c60485080c08036005002e00c42c1a6840355004e8140382 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 207621456 1250 207620206 207620219
    0x7060804060906150602030c060705130e090a0b100311010c030503060f0d0209101a0901020601151b06020307110c0a06050705150703020702100f0e2e02010203101e 72
    0x42c00d00c228252085a643c4411882c80d03404a240000100441d8010703580715160802d02c0341c18a4030040540c0103004040008000445402a075402640d40c18032110040da103c50852510f01001201c00400303e0000380140006003034104080320031280310b40c441c40c0c40c0c5c03800c1c803004461980d91240000c0c08150107002186040c544034580e03841c0d01d000038000c0000c5000301c1c0c002030826102030f1492a607110000c1000c0c4001c003409181c1d00138031000b03081c0c420704d0701d140000002c0d13840b0030502c51f2403408020300800032643c0e84686a000c40780c00c80c4540349100d24505040403002980280c0c1c140010450400f90baa05184010274482444003000701840241d500d000c006940f5540039100450b918007585030303188084101d401d00d5900800315594016220262807051105607040e03803d692051050000041410507802000744508880503118074580d0030100b9a4062102c41c0401200075408240e01c07104140303a0705502079481800140500304400d0750310364070784c12403c02c07200d1003d4000080a80c01c2c0300c039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 207622706 1250 207621456 207621461
    0xb060c0f0610030b04060902040b130c030b0303030402060a08062202040e1e0406020c010e06010f030302150c18060f03071713020303040308090303220312050a021024030803090f0706080406 83
    0x340d40050408507003116100d0016008108940740d08552f01d9072103032440c01e0158184034040b848241a80194a1401e29030005500340c05604019801c000c8203000060340c0d40c6407110b01e603c0c600d8121040e681108030510f0510b029400a0207030100202c0401300050b80303175901441440c2100164460100e09448030b45a6201944c41004903418035922003c41e100c4d000c1081107150300030559464030144a50643c40c1c003d0505494902d070700c036491142d01c01d00174040700350000c548070210b030544841c900100c42d50204005000c0c401a40c800d14401004000100f0740103540c20005043e000541030075076450038100d182c1d82214000c0031b50554400c1c001070000071000c00040074a030400808580c18040303112400006520031405508220800798000c20800642803442030b8200040d06200341804400c0348001c0d900d09542110a0246859000201c156044200d00b420345004589010510903201d0812030101ea005944080e0540b00e80c0d0411807243d280030603040141c50301aa1042c82e02d4480d620340001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 207623956 1250 207622706 207622721
    0x702041116150c030c0f0e0a05130213080d020c0d060603060203040c0303140901141c0203150a09050c07080c0f070e0414010b011407060b060c0f0610030b0406 70
    0x600c030300801041c1c0e8001c0008850005040c8214990904502004219800d44040380303914010b050600e4100b10800d81c204404c0400c00303816252024450004100040f0461000c0d449a50410550081410141003030380050140340c00001c0c12921896442c01c1d44c6035952585c0d2841d40058006144100091602400c050082406080e01042c1541c0340d8454004a86c01a10110ba080c60f003040b0401c10550024000d01364010344900d03090614000000191102c000790003c5885440b00080345210340d550140105c10503500400119120701c0c00d072380150050310b00c5807203a92107141c100900040450b01809514400c03808040000d040c100e207942d6000b1503411188a1106e640903110798940f8810040040c1c60041c00b815403000c109040904100f510031a440342091426414486241e0950340c0180c01e040400106a0545039140880c1c20704000501c4005180350303002800180224030404c00040840c00c11440c501500c9080c2c4a188a0300183c11a921009040712007200004001c540d49134460349 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 207625206 1250 207623956 207623981
    0x30c030a021e060f0a050901121404020d050a0c0618050301090804060302030c071208070e0607050604080d09021507021011060c0d0204090507080411010c030516050f07030f05010b06030408070204 86
    0xb8249095404403031300c50381002400c8030000e000480ca402903980d10912484248281d03140c20010400306008150498800800c080d0040700c0c3c0f10020402c04c4402c00080c5c0b401d54104100c10303c8651214401403201e40581c03c524840908104045054035040c410803403110f0b8000b03507091401385400d1041c2c020f50001840041140028002a00801c2e0303107030095840600165a10030592a0101010b49020090402a8003454090141d8400124000740711074200e0b8002c0c4495403940805030743c2d0f038058409600001d40190641d192012129041c1018004c114402c0743c00804000741c07848102c403a101801c095840d00c0d40880e010400d001030713040003421202c03803104c005031900e6200c500d600140d43c0d080e83ca20307000402c51801c000a201c022081d054854000f480c201901070340c00c0e1401030450007031a039000600003c001001080042c01c002912006501d40241c2e206c669890408099511040c80144e849500f8044502c07071f14a840000c0b6881140e00001c4070f82040341c141c088c00002c110701300b90700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 207626456 1250 207625206 207625219
    0xa0c0f0f09030f030903050706022802010f0309060b060f0702090c0c2112070e19050a0b09041d061503011515020f0615131505060307030b060304060209030c030a021e 73
    0x8400704605010b480058500c0b6001010b440721a000c01803140c0b19418029101c00102f81d0f11100103070307442000a000000c040c0b60110700f01c045800c0030320040c4880807600364000c03000140c003503e0a80c1c03203014002690080300d5102c003036954980f22514510409442c41400e800c008810300100380c03c1c829060303d1005e201002400c00f840000c0018400c0000c0c1c1d034203004155864000240d0349840305034a000741254814500d813061400000c50280159405120b0348801c020540d0351080e02c80b42d1012600d684400c41007090500300000301500c80c541a518101070681c03802000b040d0f4101400340c000f484a07a40201e502403880c003184041d4805608107400d0450043c00004d20890508000e154042c804404502c40a18010420018000d4410541e81407590824804149401402104808903502130300d405540799103510084001301507010480354001c50200500041c840c2c1a4017610540a0640840765444041c004040c0d41e120354a0000b03512a08004058248141060b40c0c0644260068440c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 207627706 1250 207626456 207626459
    0x4080c01050a05041b0b040b0a020c0307060906091508040b04030c050f06060406060e03070306090201050f0703120c020303090c100207030812070201060b1e0711090a0c0f0f09030f0309 81
    0x140c25590705039000003a0b680c075142030000b0300000b00c0300c041c031341c002480242e424140b410944607540d010341d01c1f81d1403081d440410b000a0541c001e11105201c0030005090740e407074070b4032802c02070503864142c014280084e44001010600c40001e011003c5851116121b141017a41c0da03651b0070540d440020401c4007000034400342d0000007103003000a6010044400090642071421070f050104403140366015000708984180a9002c94030082400d01c25030340c03c80804180c903440713800140e6003071080c007a00002d00c04000a4880915074048805002c0c2d40000310107001c203036803525049a0703030302060700c494500b030f0015400307070807646401c17010812038114a00550704000d9a9480d90321480e040b0350100074000d002d960420904607420300c50a400342695180310740c00c1c022800110700d141850808218101040000c3e01c0081c81202624682416070041058006140100c8064090245840d081e2702042d07958910390342040c0280707881c090244e604d07503980f6081e5107561666001084610416020302005e40c50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 207628956 1250 207627706 207627727
    0x4020609030a030f0f09050a03020603070c0510090201180b0d0510050a06120b04110d0911120109050c09071b0206090d03110c0a03151e0608010c2a02090408 69
    0x4010701c264081e03103400b0410134001c02d01070300040020741040104040c0140520255641410107000ea98042d5070030380c1c4a030340d840c0081c0d419200360803001d1b15502c9a1001c03544080d18580002ca0312034801c0e0313158426170583c9014510368648500847c000e0f035400b8440313003c84910a502081c0c0c82044404240b0314650741d0000b080c0240201e8001500203a0084454181d191841c001c0c5412001b00b03440c100102650010b01c0384050040e6120001d0389501c6901020900002c1001ca500d80381009007640202e50b60700c10304074003e1015450807070b5240129040031505180000030705100309140e86805103502c03460101c000898ae4001e0080f68000e07028031102e941500c4104401301807501c2601c0f0342c44060031107000c2d00e03d0002d0820750301d8422917100e82d0a000003018050400001c9076850004034000c0080b80e0840c1c501508080040046460075200003140c1505400202c5081e40540b14060280032810b00405648845240c4072041d01d01e01a200006082454001b64070074060003030681000c3c580c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 207630206 1250 207628956 207628963
    0xf0114030115080612070312050403021f021b01020616020304080a06142401030e01090b0a02130603020906160c0308070516060305060d020f060f030c0d0c0f020c04050402060903 78
    0xc006002c2e00310004200c02e4080d401048141c1c00c000300700c400141d070100f940700f255a2807009020080192000840a8079514058010344001d198010120448590360f071b0b00b281080b242c80e1010b14014411521b050b12100c1d550307100502c80c01e0301070f17003e05595030300c0300700c0d22024003054256041188400c0000250080c401e108001c41c40c0e05c0b0b03200c0400c1d01450100c0e0b1000000024102c4110a02c654408600c048a94908100e4503002800c0102c0d01c1c0760303d070500d02c0c01081918000360414a10004000c150340d03142e401001c00005030041068155100e01c0110101d002d05d4041c1070b0030800c2044964140c141c0e480e480c0341207510504030840c1e0b8603200d43d142043e036048004101c801ea030140304404c5070030000c046058040c0c4410b00d000c101d1072900c5c60000305603041c404c1c07000e8001c1c0c0d407100c80580140c032440120303070f030072210a02c1c066030301e00b04204010355660203c0c43c1100d00d540703003001c005c2d03045102c0c0c82c6403e01080070b0790080168110368410000140400b600c1268407844c01c10082070241c4043c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 207631456 1250 207630206 207630209
    0x6210509010c20070306050a091202061f050a0b071b08070905072a050715110601270b040216152a031a030304030b01031b0e060f01140301 61
    0x1000080341c0300c0c211107070250103180c40070003080682e209500d81501c208000558402246c0d00510003050700c1d114640e488008040c07080d800340c100303100c1050416440e82c0000da02400f0b0400c1107045003050002c904022242082405074940c00010010104400ba00e100d01428010340141d03120a590303580d08503c0c1d1806019075005000c650000c0104206007805840780540c8881641804044480a00401348035880040c8100c00726a01542c0c1e4002840020020b81d4054040c24144c1000c0010119000e0a448071074550300000b031003a10008290708101882d0404005d0100d030000030340d1111200e01c00060801d10285c60f0b0010ba09100c0740c00d20340500c0c00000c1c038140c000c50009001c00901c10440081c0c3d18090010b800042450000034004400091004005c101c1d0340741c00202101c2c9010604c0020020080a540c503100104000c07052158655403281204d10034000341d85141d8031004150030081281c4180f0301440c0d56800000d01d9810100c07903d9403400e80c14585140a00b40255000b03445400a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 207632706 1250 207631456 207631471
    0x6061e070c05030703121409060a0c0c0b04060e030c120a0f03170109050103060e0a1101050705030906120115030510030b0601170103030207060e0117040609020d0f0501091106090307062105 83
    0x100c46d036140e00184c10001c5c1540125031006181d00c0e00c08400041401440b0b1000c4002c10041e541c840c0d031050056070340459000d1311212654694031a0b8a042c018250502900624424010500441d0152501e1895010380d1500380c400b40940c01103580741c1c214a40b80b240000d809007c916420340300f09084034051240681210100060a0f5066040c40c1c0120f80d5480c0c50900c00c0c0e4800712803000401c1c00e0048800744130800746842640c0360240e142290960044a42058000702c001c61040d40c0a0726024415041e01e5112068056140413060308030103461099402d08a0656408000d00c0443c0800c0c2000d584040b040c1000c4d00c080e1040450540c95810980c0b003580180c0250f601444202c3e440000c15244000918001c0414a210545412810409040100003d07641c110140031500ca8030460720b88035800c009040140821405c1c07260292400f00b9086a4808480041d081c4600d8500155041e444001c1d0040647c4c500300042600d00c24041c03800a003c04580aa40351900e0461f4002d0a00c43c0c0c0c84d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 207633956 1250 207632706 207632723
    0x608181504030915270803030a090b09070b030c0d0e1014010807062f030705011a0a1413020c0d03090c05101706010c0b0a09020906061e070c05030703 66
    0x207142c1802011109581c12615240100030290159241e10040c094484042402c0184802c12141d80c4c10005500390361050300f10740404400c210420312594032100d019401000041015036522071000e445a07007034003500c00d40d094284007203610045400b000d0a01a640300b0000198142c03480219490003440c05581020300340c4645401c8140b50500d0381c0c0038010060710b0300800b180780c10f2a002401507108015641000141c101c403081d03d0281d54100025481d0320201580da6404140c18018040d00034603810000e82c2d0303184012100a030030508811400c4038841c0700080c0c201b0039090308000c507149106a04889070f50b024401580e200300184032040406115480004812000d0300c0c280664400c0d6502175403040110416007581660440b440149a04001d04c0841482e981c210040e40c0e8480c1c2200c014084030307183c00800c24a034007241c3c01405200d0007181c00c0003090303580c442085903500c03c590014603031410000011085440c02006000d03a684142d0500322140d85690100e4076140290303000359210700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 207635206 1250 207633956 207633961
    0x6090106030e070506030c070210030b280f0e100509071b05070906090f06050904050d1103041d220c0b13030210170903040302030a082109010e010b03030304020a06081815 75
    0x15142d8420810503600d400c062240c6040c2c1c4000940503004480b050137002d141781049020440c01a0b190b00241280c5006c803508261100800116080c0441d03001014500e41540410f1524244280e04d100e442156a0048082d00000d5a940207004107107080b9803511456030080307001c5107070b03001c1c4501409a03504009144e411010f14901078441c81d40c0402d00072283c070000c1c000440c81c08a10b09015070b2460504825042c4610152841d40c85158441c0e134000605500d0151000c840e481c40d240101103d0780c1c11003150034542c030810704040306100001c110322061503040040f40c02c0040503001034464100e01c0031810381d032500811220303242d40040c00f0014140c48844030100740c010055540100d071190007142001d00315404256500720810019003c61004500a42d10300f008940c0c46a105003607040014070340c00c2c49440302d4040d00e0311a82001d02942450040d62041c240001a20311a0303800802d0f1840c050b28042e401c0d01d61000281011050f0a40c6800b405008074041040303180584125600300340c01e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 207636456 1250 207635206 207635209
    0xa120e030601080c01030c08040803040602070203030409020313140d0f0f0521040501110301030f0201080a0b040903360e0a0b0a03030206010303080c0a120b012307060f0506090106030e070506030c0702 88
    0x310321507e082c0381031101e15400d20000c42c0d80841035a81c40703030317012400503034841c402e0001a01e14080c9521486069000008110000c3c041c000314110302c42c4036403440e83c004032508100c2c903118400e5228001c00190222100281144102202103a520090400b00e103042c1c85c50140401c0d42080c00c690102c246114400d0100b041400d100f42609502c80c0d074a030350305550541c4d0742c0003030004400c6000b90402860740d01168210456900c40411030000800402540e44246000740001c08201840c41001c0320404100740d01e1940408200440e003440600101043d00b00141d501d10003001030800000d281d40c84581041d29220142008080c40c003030f0f0002c145545c0345150080c540c4c5401086103030001c60902c2505240740d040038400311503440c111000b04401e454200100c44c0000c00800540300c0002d1111000045455040144415401418240568201d0105c600b058030030641d01c503600541000300401019110340d001c024003520410507500945d40e140001407058000b9100c00c60280070024124045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 207637706 1250 207636456 207636461
    0x306130623011701060b0d0c031401080a060e0105070507020103090c0302060c070e010f060518130f0f110406080127051510030b03060c0c070e041109090106080a120e030601080c0103 80
    0xc00020f00005c0c0f00b254117203005689140078041c40c80b4001916480f0590116000e500031030805035428400c00950340e9940b090641d10031a03d401507502a1800d504410181010700070a88582c00741d8032000d1420600364011401085520410f4500c0d00d00110040010381d1280000d0240c5010b11000f030510b142003080001c00648107a204150f41e20303403950100811600b050031388511044074205c0840d5102c01c100030401117406a9820020145840c0d4000a030300035543c001081050b00314020018450100c3c00704200c0d00c21030145001080700380e0010001c07900000000b0111046480c1031801640410086a05aa0081e949211070081d07600310002d031410004450724200000e0300d4144208024100425104d4002601c0f03400241000130b085903000c901046008011300c00e41040155901e05420000080201910040d02c5140314502042c0e03105014040c0e4415034245001529031482c40f9903820f0140500704150f50140b20040d4140001a43c0900c00d890080a51034081c00243d10004c000608 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 207638956 1250 207637706 207637739
    0x270e030405030f03090a090525050c01111804020a02160e0f25050f04030209010902090f2d0a05180f1f1239090b030613062301 56
    0xf102d0348140b00940d455031310000414100c03040e2003c005a26140c25035814640c80b0b496112041001d003062151220b40d50000c010203205040c480204803403003030715000141601c80d410805400e102c052040e000b2602e8158000c09000c0d01e01d004803840030215224083d4002199440440716011000800c01803034002200303246e1000c10f41d2034403420030190710501e01c038082c2401c80903400c0000c0400c00703200303e203100400c0b90099600200f00482ea981c0d15072000000c1d6110b110f20300d0060300800102000303403c16078a0281c0115030a1a090135103c5100652880c1c1143d01d68940d1340f2103c0032100040d983c03100c210403006050306007c00c0b14189045440749100380070260162140306d902905068000c0e180c51001010fa4050010211030220107081080058000000c801544441d90880355100d00d04142c04c410740c0410038003035448461b5590003034006c9a155102c0d050301500600300240c2c1018010020f202030341d01c1501c0002c0d081001720390b0b1448840d10b681d0b50004071312101d40140030203d0309000050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 207640206 1250 207638956 207638983
    0x1c0c08071703031302061b0c030c0f01020d0e01030204050901121a090d0806121515030a03080708090a14030901031410061d0607111003060b04270e03040503 69
    0x30301c00e07100d4181c0c2552480001d004071003281403c4078460466032440d04462070400d0500607000e0300844101c5503601ca07400c2030034203482489010200ca17054104000415403c0740c0c146c000d890600c407041d0b0240c0700382100c1403206041550800004c0b034a5500c40036814040d0020002007200300c01ea61500400c030100103a00e0341d00c042d80c40c60401c00f019900145503e80003815143c107181e00c0e120f440114508082088280806005409001c0101c40303c0706556480750300c0c88904c07104c1e403a009805140d2280a411000340000e13000b20009558107024117519500b1450b00c00468030084802e4407005e01011000408403100d82000a01001c00d40c0c4c503005500014210180582c454240b40c00b000340103850600c10f02d014080141c0100280c0074100c5035139411000301a01060381d0fa40546400729105800700481c610500e85c4400c1c0c130341c160b0b100744110016a00c1c246005460300e0b003041200c1881000e50b21644690824811031308804000034000c0e104c040b01904011501d803030030a0101401e0171080241390 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 207641456 1250 207640206 207640229
    0x160e030a060f0f140a02180306090a0c0f030506010b031f0303020d030f0203060f0f030a0b01031506080d090314010207081216050f09131b0909060f120206091c0c0807 73
    0x100c0740a41d135490300e0383c018060400c010303035403070a644081d0820280c26107000d80c140101030401020b80004140030704820300c141d5000002075103420344000c00d10300750302001d030203640110014010761400b40021a0401490180c00c0c00881a0030309222050846420480040e000b0594581107a6014000c0d820802c400d5003041d821442e01d000032540c107040e50141c141c4100c12404511109171400d03c14482480c5d0400d41409072581c580c28411030181d441e4100c903261503d842400240c2901c0819900c418000580ea02601d15245031140f0f0000d5040034410b0250395400c215010009a00f60018100c0041d0b0388001a0b4614101d185038040201440500c420301008121441149083c481125032120040341c0d510041c56010185900903c0c0e0800100904c917101410110440e40010a407000c48107855414000251541c07850071110700e40b4403d2250065011800d6001450007402074241c071a4050301501d071041560160200350031481209541802003600180420742c4d05005082c0a0410140d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 207642706 1250 207641456 207641471
    0x11010e0d030605100e0907050c0601030807020f27040c0906080f0705060c061902041206020304260a05030c090603040309150801050108010e0601030f0f06080f0a0b160e030a060f0f 79
    0x9445d107401310b9003082c8102c200500094129000d801603500e08504c08080707580d0796071203191034505c680c80a4801c1e4426222040c01d15507600d8048950311220148800c4201c050180d0414508003620242c01101c0c43c0e0480000400c0c3c070300c0ba603c42c2d00000d01220f0001c104000304000303104d080030895044240600000c01c03801c0680180090126002010390964108200300250303108000e00840e04800320320b011011105040c005181c000e503003d02d000b811800003070340740031030501d41d00d009000341011242001c0c0030780441e8130300400c055030340a1804480c0c5441c000041c00090b0450b40100d03000c40c00310307c0c8203030305003c0c040880356100e40720718050908030b11075418080043c00140e0144a1680c3d00702c132800000e50103920980003459248a0303904c0502240d4001c9100704040d10441c0a143c42074482c103034040c507400320002020b829450b001030554545884201e11094401c007440703104002d0010a0481ea24651030030088a40c805005030350000305080c40061003025201110100101203051403007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 207643956 1250 207642706 207642739
    0x17150915010801111e27040b040c090b09040b0a0303020a030917071a090d0809040b090c1602031c020115060e01020c090a0f051f1a1911010e0d030605 66
    0x1700d40240101141d001003a20381060b0100b000c0c8501280410140a15590002c1040015a200da40310000722424002c1400050502040300d880551b10300010b41c41140c20841c040d035800041601c00300103070004c6030500b4504d02140c2540c05587c02200143c1c000c41c00601415407060000c00a04030f990201081000c0c0d0802d040d6484c02c1d81d025000950400e022050800e10610003181c03e0300304050090503881000d030404101903001038503003e01960034480c40f8400d03440c0941d0389600c281c00b480c000034280a846c480f0900c45659407041281c00d8031a40342030003030008880c90b0204480c03485a002040c19680901e2905584280d03502c50030920140303a580c280c0aa8001c01c02d0804140d040c1d4000301a83c0c0e4030040440030786a8403602c0f0810918100620215030f0081c400c00340550081c0c8500c00c8010303036540c0300c50307203662030021800c00c03103103081c0b02c1c001510031041d4240044175420304c1d05041448030000b100782119100b070103c250030b902c0600105866509801054002c05040f618861b01910010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 207645206 1250 207643956 207643991
    0xd0b06040e1507080c04120803271b010323040f02060f13050901030b0604090309050d0807050105011d04060b01030209060309010c09051210020f040f060c2a17150915010801 76
    0x114014500c49002c40010102c640100d5445030800f80d030300200038070322079000300151505101c60201440865203070f2f8a181c10b501071f00a0950000e0f0710380b001026000108840014403030064011103402c00c0d01c480450151382d4500180c03240110141c141551061909440092407082d40c0c841d5004184000042010851030a034069201d01d0070b80f00130891130703040e00c4e04841941694201c2c0d079111022032280401e108a034009842014407410081201c0e903200c090800c50110702c040c2010841c0d20000020b000100c0640241618a4045c18058103002481d000078060b40c100721141811a95243d4041c04c8041c2d01815080090405542c83c424400c005504280c5454000c88086541600015154401c6940340c045030700800302100f01d00c07030194a4000080c0201c00e040400d488414910210b54800150641e031039031004904e05481d0306d100d02d0400f1006207112802c424850902a801a000341d85d91700e4644103200d42941c00c06000c0e0840320105208181d101038000369940d81c91301044107504000c55 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 207646456 1250 207645206 207645239
    0x30d050406032c030a08011a041517010603020904050f040308060105090d1403040303020609072907060516021b060a0c020a0312120b06090d0b06040e1507080c04 71
    0x3854003103200505011800f01d81568042c660111485506089280c0c11010010b03000e46807003503503001c81c51799985944121588180300d181d08100d800b004108143c2d00035051110000b856801c201c40209900d80390214680d000341c1c080c001190300000d4000c44c52902e0720501d5882402604600691304144d02c0052008100424850502ca00002c00840650b00c0703014a446150740010307030184a0298240c02a10382d001848220094400c0e100420490b6801103810002d684560b20f0484400c440501c0440441013158103000507110304112203400b2411034001c0d03910134400140700801c681b1008100038509440c0e182c00c14100207008400503c1c5075118811508103500b24540300c40f4004080c0005092210300740d00c000e0440c9440000c0c3d606040d0402c0000f425010400002c00031071203807800780a030301c0c1318170f04040c1d03407100310a0a002d0004170402000354010502400000c1c110f2aa5200c030b0b071a10b1000c0c0b000c90141454581001200c55100070200da00c0800c80010a0405103010555a11143d60 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 207647706 1250 207646456 207646469
    0x30207030e01030b040204090e0114070212030a020f040b03040309180c09090504062406030b0d03050714070f14040c0c05070e090c0607110306070504060f051b070f090b030d0504 78
    0x15140c4c80115a0b9039034055501804412a0030010b001110501c64020040000f11890b030100450004062a0021409181a00c48043d0b100d14590707680f40208000d5101512000350303e1418003001c201384110901540c803942c030984a0749400c50604809800c000d06005424040a0401094814003503014001004071903400f05c0c013080030703181d40ca03140001e8941403502c0481280c1c1510329503001c0d0500c1d8501030442d692030300c081102c56030310b20512121340e010440160110354100401d10000c0c00360410714180800e4076007a42e9078140c40f680b00d2034015080d0f501400b034449404111820a142ca4071505211300e01d50f00348000401d002c0d070b88403074684050788180c04140c1984000141041800c0c0301c07110026600400440e80e0b020240f40545480800d0100702e4080c0c8070300300c0083c0460740103004031010345005840b10080f0000e0702070100e5540c1d01c16171180100042280f140032880038104810000f0740104464004001e04004c2d4a5007103a00040480388a907001c621030503041d80d0401d0071034054030f26 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 207648956 1250 207647706 207647711
    0x1703040303031a0414010f08010207020907080a0902210c0607050703120c0218040302150f1f03020603040506010501080c0403080306060d0b0927030310170703050102031312030207030e0103 83
    0x10000c2144540f0800f400c03500981003041c0c4c9900b50f041448507a0689040044401c403003502e69480300d080b03010341075009401c01d80b00c00200301c2040c000c1c1504c030340c0441c0b4030b4404105040d40b503020520002811071405182243d00520585450003441032500300a81074900314100881ca8961a6903541d96100c090824050800c4000d00688203074800b00100390040c1203545142c07401c500c010404002154150014001c0b80405060341e00704000517802030b02c20118076903454032540d0b1a0000880864414181420b040c400040142c036520059032140780144080c003181d40c500000904001030050840040c400100400e00002c0d5030141960f4000c04190341d01c6481c3e448004140380141100f060807507000500d0400c02803540780a170120f4041800c040804016901d55a6203942e50f0700042e00c5c10700128014440502460240d005200e800101b00b00444d01c1c600e03940e40310642243d1082d01e0158200100004850600240c040d03980b03090705c824901180740c43d405807402816414002c81c02410141c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 207650206 1250 207648956 207648971
    0xc05090406121e1407080304050a0e1513022701180602070312090302030f0a050c0f03060c0903190317070c0317090f0102041e050f03031206180403020313170304030303 74
    0x184c1881c00848441c01100703c0e81c0b5191200301040d80c0380c004e0f1080c64807404100c2004601c03440c050011501500c2684540542c040c00da2041024082072800d00c140e060381c0c244103503c84c4000c80141c50800c040110320101e41a403103800010082d03494900212441000c0070700c104441a40040c0c410700300d0380c00a54511700c11040d614101c80006003903202a502d803254100c0200f195101154603081c1500c1032044451041001d030038400c41194040c60b0641c943c10050009001c00a40c030010154000300809852540d461130182d071603001c00c060002c0c0c0c001036044418400a054810b8101d82103005401c10b6014480c113039900074010240000b0078800c03002e40a0100d0788503902003050828088a200c020340d1120384a605541061200d50004021001c0c0140c00142ca82001c0410b490342c231101402661070803c5800348011604005400307560090f61810000b44001d80d400003190049201c1d40c0a140c3d140342030b0002000315000c0e17400c42e000014203840c014241e0b100000840d030031640c0c1802c0105848 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 207651456 1250 207650206 207650213
    0xa0201060510080a0605040506101209230c0f0907110f0615010e0f010503010b070f1a090c01030e0601050f1302030106080711010c050a0e12010c05090406121e 70
    0x5081650100390800301e0b0301c141c044290b4002095030b01c2503903410410007a16581e981040261380341a40c840350444e552494451143c3e00c159581041f41c0500040803603030300d00310f90b0b4402c4800030720413400301400004088584520000e0022200d082c404641545255100070300041c0d003084090000c1042c410502c02180e008103042c030070003c62a007440295585481d24128003000d0702c00c844581400201001070340c550a01c0c10050424150070180d40e020704580c00c0000401c0c20754040c14050b5880605100140001070007100300800340b8509072250794043c1030501401d403070800c2c41c00d5950b0525040c18100710341d01d8000101d15044480845111410280440100f85140100041e2070f40c0c07103000000100d0b046030401e0040380a0605c3d9508c030003032100d03040e2249003204d010185440004104100c038120241c07042d00d14811b00c4800404141d0703001c881a084a00b154411007224001c282d001c110324400380781c1440b401c030040100130b1030090600010f50340c03c11405009500d800ca900070301503402c82030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 207652706 1250 207651456 207651461
    0x20106210f02031204050a05010507050a0605180106090c080112122604050607080105030f0319090e090703110a050303040b25050c03390102030c1002040906060807050d020a0201 78
    0x615000f600b642d01c68080201c843e8a03d03817160280c540244417443c4005440d5118208440b60140c101c0081e15041030603136220006007101404a035864120038810641380714080c8a450014a00110000b40880ca82034014180c0c2405a00841d04550204428008140c14000290098105141241420700710404000b05400c502d107042c030400100508110400100145042c083c0081d5181d0a09682c3d881d4105640c8900d0500c1580e200c2d00300344007241c2540315020f854050401d10b8108404d2480d112031031031100c0d010841d0307441e90561010380201305014440e400721080c04c2041e110806990b0504000c82d0b42c901c6903210f40603052000040c940104d8001135501e41044400f18440c0c140d82d00320341800c5076564800c2251603c81c0c002e15a1203520074001035091403800480f503140d040a50000008044148007061129065000c01c01000341048001d00544602103200d400040e141c4d428480840121880e43e000ba02c148600f08041c40f504d55048016152010319003c009643c820440b00c0072800f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 207653956 1250 207652706 207652733
    0x601051303060204052803141e010b04060b040b0406050708040f060c1202010203040b0105010e01021c030606022a09040606030807080a030c020718110c07030507030b010602010621 79
    0x303054501800120420a42da001441205d10882c0c80c070480d005c03030103524100050410b540814040c46403804000195034007a001c01d030b01c64401e0554540c101000c5200081e0710700050020340c903954400c003100d8149400d2294801401c0400002400c1605080c50342086202d03074000c0750180700010418000308490300b030803280500603441d001e4101c0c40e504c80e00907240c01c180500451300382c0c182c801005c0da4603105200b564495500007802001a918140066500001080245045000740d040640301480d1070b201c1d001004415a50009065161080c020b0034100d001690303510741458006501401d91a2681c0b104040204489040054070365140c904000d10103544000c00120000ca001e00500c6001405084440484d4806100745001454120f84903c0b60b802449071442648010102c00034107030388100031b81d051030044549042d90f10b505c940d2410790980c0c01150180c2c0a00018420050202d03a8035005090f940003d00000703080440d80c40003031007040442c0a2900500124005002d0320045907407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 207655206 1250 207653956 207653977
    0x130b030a080d05010e0f04020d11040905010e0d020f070e160c1403030106090e0906010e0c090a1503060605190f14030708010e06060702030a02040902041b090e060402160209060105 79
    0x141c0d03602c203540048000d030009128203940803030107800203400f40803032800c81d0703200303550040c00310301c1620440d950401100c00f0010b80d01c0d082a03070346240d070300003900904c01d109034181a800101807402030860024038000714a800020b643d04000c40c200300100e036260240303401003401c007004080c1c0001848210b46008840002a028050516140f240002d0200c0118142c0381d0340d40c3e48625031501d90804000103901690030300e08a80c00350300104010460082042d8016600704101d92924038403d0006813481095008000d1415050a250212942610400004040a00b041410000702c1c0e4202240001542e1400b414840502009840300d4410401c10040602100b40507407a400c04403402800108240140c0404807031450100c0c1070703441e1550955010503070013002031507451026400c0c88003802d00d085089800c2602c4041208001411741e00c5443c140480c0d80e030301d194151811888401c1c000021300180c1c003892040102d42d4412400b04d91210000ba010744003249242c0312440121802d120700c00080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 207656456 1250 207655206 207655223
    0xa0b0d0506070306050a090b06090f010519020c03060601030e0d1101060e0702100c110a03050d06050603090a0b1e0103020904031404060210060509070801180b060304080406031406130b030a 83
    0x102c1030310780503481441034810940da90b0b80e150f9190890701c1d044904a490003a80100f05005a03200351031f103100842545101803510604003c00340807040c4000080051080c0581c0000480041e030742002c1000c0b0354000c5003443c0c00d001d02c80291914503140c150704800a010000c1d05c0c14090200d101c250481001413052281110080c900031200949980c40900005669400c04a160380c8a51040c801e0454098041c806007160b01c91039075060b1142c1d4840d0b0541c2c0c401d81c1c3c60b800e0000322543d5100145106900b414098004034015190040702c1c0c11004143d5002c0301c40b00c518069040e0004007800781981d506403104920794072241416a6858001180303c4d40c40440090089401c0d070740414881d1750a408a201481210b0b1221b0030090001e030b0071200000082e604600400000000c40d81c070380c040c03c070811000903121344000c0100d00709600c1100c00740da0713a0300002010001c0c254148a52039000407511034070700682c104940051480c0c0e801a0002080b1501c4900340c08036540d082c080d401a255008560703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 207657706 1250 207656456 207656461
    0xa0b030a0605071101060b0a053612030a0903080c030706090c080f030909131e0813060203192f06040b1b0d02180909060402030f0a0b0a0b0d0506 64
    0x2000203071038120f4900000a115039034018480d07005000d6201030b50440c0c42c01c42d0402c038190350115040c1e00042d079a018810681c98140361540c9070b9020b03007205c140c503c00041220203100701c144010800340c7d0110840030323030040082c907074559805045201a01c2c0c1c4812003983e11a014051503146004c0c0060141990303181400c5041000313907801000040b54021000d035101074030411001604d901a50f0246500401000000340d112040607000c41103080c8600700141a100c014003103002c1106031a10f044480f03820000e840107500780300d480f40100600151000b0752402400c1080703018028040a80c100602c82c1503c1c00242c0108800c0708402d50100b10b0300d03841450500d01c90419a100c07402d913030654010210102240e0075410a042e911000100340c81c00354600709000044000940c41101421084a4042e00100300d0355183c0c0341a90041200d400141450308040c0101420501c180d6000541365100c40c411300f00040c0b0f1005816804800101d0000e506980301c40481c000c20030b9410000c0850142104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 207658956 1250 207657706 207657713
    0xe07020f010506010914150408030c0c180105030c131b120b0108040f032a0303020a0207081f02070c1205030403200105030103060b0a08030417010f0908120a0b030a 72
    0x42104811080e00c0082c0125107461005541d100168040c2a80d036142011090145060840da80311074501e107000340e0f0346420790f40c901e0a0f0442c1c01c41c00c250901d0350010f019805051501600000e24035220506400c3d00d9498803000a550b00c08404407135000d40c2030010202c00d07081c0320f580040c6100c10210350300d40c12615500d20080c00e01000c4600003610524040d41c401455209124552042e0342c0040d144200c4c888544041e1801d10101c201191010cc0c2c400c0c00081e120343c181c1503504510701c01c1e240513885204a08010b41010300c1034001000f81d034080c01c5c2d107035074850511141156138402800d00507aa240d0904040e07003040107135004254000d0700c1528900c1004000001401141c1c05600b1002403881c0c03403090182d90600c038048041c00294284010300c0802c1c80359100000e003140090090011543d920300300c07811500726a0080700d03141c0c942c80d110305400f02c0c00e0054548049100004000420103039862242c00d0251882040d51750903200700180001440398000000200010100d401c3d0043c07514 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 207660206 1250 207658956 207658963
    0x7021b15030a1e2f0a0203091203041505120a0c09090e010e060f0105030d0309050a02041d060703020309010614100804020112020d1a0105090d020f1305100807060c0b0703050c040e0702 81
    0x8842001d030004101c0d1000b1070804c608251204190a0340c05980f80403411010400c401c5450f540303088050004000c005040070040c4084180e1500c640c035800e03100c1d8180b010608292000030540b4803910f042c140900e039100d030311410700340c02e80d400124001501051840081e00405140e040e0003400e11492003400110041c0d100300504030f480c21402c840140d00c0e84802182500c00504009189a0128540500514113500a03a840c8066a501540f05030b0250b04103a103480015518240403d5000090080b062002c2c01400044c0c0b03080d41042c0c0664248c0c8010501411700103c0000400008101040071680300c2c01c070340d0410242080c001d64403402148080801040303c07540c00e2a8074a42c0286544240d4003d0301518000c4000520740320f2510f03040d4083c814000c0f0400da00076808003035284074045038a200c2c815140030b0741110145039285410045014501540f0340c014505000a000c01c150004004001f402da00001a01d070125864481c000d21650a018582040680c1c601d1003041003000f0b40c1c0007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 207661456 1250 207660206 207660251
    0x210515090c03030f04140f0310090510090804030f1b180510050108040b09010f090c03020f09010f1a041a0706050a020c031e09040507021b15030a1e 65
    0x80050700c42a00015003019a0382c8580c14401c0346510040c407003002100c0303114200a41c80400981044101c070b41030720010342098680f8250390019640d13a99a02d050050410241c0114400214100501401c988400c0150b014603c00148801c000380f031020104545015034950b0140503824a89140b034580c0351000d150042503c1078075506247c2000641543e822022540c12514107845001d125180d030303103500f01420401000c0c01d100750340b02e80c1107001c0030340d041c480d41d4242806100071110aa04601c10000c621881c41c41e102d21a452640c01406801c005100000031140307000300e600203031081d0080e1140540200c2d445a4800b02e41d800d03900032450005002440c40c90f100d440e0420031903407040350841c12401038010344801c41d80144009402620050500d403101c490302c0d813804e8100202080000c0c01d841040301d20700b005070031210006007100c5c450717a490241244119a04085880104401007d42c00010007481a0035214250f850a5a45a1103900c0004d00c04500600c503082407620100101404c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 207662706 1250 207661456 207661471
    0x50109050319020303070e040207140313030b06040c17040302070b03010e1e010f09090318170f030702030c090408090d050c1c02060301031b0f12110316210515 70
    0x180c1d600b000c071151002c4212417041d0819161a40d58140c25401c1c04009d4201d0700003220756202c102c61003002075000300050b00340a8080040b0848043c10340c45c00101c18500905a14025810300c0e94800c03885030070410182c00c202017014001801d07078803400e080740750990329407000c0c4040d080040081803001c112a502d41c400e01c070754910011102061b03000d11010b49424810036482e013041c10007d2181d0b11980c0c00000795140245440b15a4800e080c17000700c549815a4444000e44007800c402c14180300c01400786403e0408440042c604104068020907162580c40500034441c0d0702c1140050100b00d41c0310180c50484401a0102c100d1035250320300541e40d001c915a40922030b142041800042c48000c51030036004c2d60b8050f02983c25a441d66a43c800070807054000c0c00241850003001144401002c4a810001c0440c4e00c1c80b0000e48100341001d03001c4035808003201d40240c100410b40050f80c64000030b100d04552200c01100ca80ca04400030880541000001c014040e00800c03214000b01b5001d84d110310b00402e00e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 207663956 1250 207662706 207662737
    0x705160305030d290402030a06180c020c030d0503040209060a0305030c061f0f03111518100503090c010809010b1002153706120b04030810050d1e0501090503 69
    0x4c0c0c02c80c04032108068001c04400241491040c0710040c10a600916044689400003250283c1c50304400001d0082004040900766a01c11410f10902d030f04100f014029002038015055050b0b0080300100307280b20040010340600c0b10000490b0444d154542034100454101050380c2d00c4107150703c401d589030756080e82c80c169111030501032241940c00c42c82000003241c0091811601152442d91151f00c3d10a0010b80b543e0b2105810403250010329159004004c04c0e902c1c44203c0803030508540412203154090170b290b00811106108120242000003141c0709841d10901f0b2480b403980d2807107102405492034108036074010f01c13002203a102c0582c00207202c08000c8c00900302e40c4419903400060781c40c404070711380000799095103030740c00f00c1c032035144e2a20031800200209001291107900c52078107038241148528101c0d608800034041105069020a0f620b421141080c1424882c038a0100001e9580602c00c002424040180c80454401f06541c0b500d048411351281c001c2c004640e140c10015266081042210b1030402c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 207665206 1250 207663956 207663971
    0x50706020309030a1506050319060c0201020a05071e06020409060501030f02210c0903030301030c06020f1b010e0609030706050403020118031a07030f0f020417011404080705160305030d 81
    0x280040705036080240e0107002801055819200d44488410705000c014000ba5650000b080fa52800d1060503900c0b007994040081d110a1407400c01c08903070b403802000045920500c11088901c2e808011180c03400d402800c404d0308118840035000c0c03555140f6100605641c030015000403401195004403045071800d8030100b0464048060001c00d0380306100040b00c4072005030704181040301c0b20305003060304120412403003420840c140005c20314640c03082c0c0090703942e626549800c0000590401c0456440c11024018103100100308480301502802507200382e0501244a0001c1074540b140c0050720882c01e402021031b0703181540c130388004c0c0490f8464003040c1e0024500c00704521680e11a00140400c40b0b900030020081c0c001d03004a08417007a00c000e00a20101030b2504000d4000c3c881c0f6010300d0344103034424071006a4440c89e2a1804001000107150235085905084c40407000c0929104032550180c0c00c5001c49a81d40382070320b0401d042ca9411690040b1902d07078180b0102c1440400000381201d03031041c4000f0000d56 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 207666456 1250 207665206 207665219
    0x521100b010212041a0a090905070c0c0b09010f030c0513030803060126070e040e0a061b03200c011e05071808060a0903030204080f060402030601060e060a030218100c0507 75
    0x103114a014070b200680c0361005c12200305041c28021300401140d40761548141e034844e0b5001c0213580e07080c0c0b041070010700b082072010b05110103403c0043c0103001010020b45081415000680054014415501031595403e42510014081c80844184192032031503210b600382c80f8540524280c0066680d90300041c0c0041981a02400130043c042d04500300d541d4003030346903649010494054045103102c54004d5258420040140d6042004940c1144039110210324101c03628004401c107104140b01000301428072021100c8008000a1300d0003030860307440d4441da40c003013a0040601503d2080c0c40e56040700f030007072509a9600c207075a108030300078056a610988aa0f072440340c41c5034018080d018090035500001d0216150514950054490f2482810050f0410b0396400c2908e00f00001c14980c0950398010408000440c941805240e01401e1203041203d03c03061140c0118105015440701c02c800d060f40001d90111181c108001818500802080300c0c0102d040e030000100070221140d001c40f0103108060000c60304 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 207667706 1250 207666456 207666493
    0xb031504150903090902160204290f010905011416030810050f0604060f11011503210c030804050703080a1d04060302010203030c0d0209040204090c090f030c0521100b0102 75
    0x2480c0c0540d9400c8445050400110007580a04034081847c859101c0c0307500140c80c0c178003c2c00b138a45107202c020407a40010550342c0b4090320b0310410062040c01c1225480d0f040d40e810081c640190740c0c00707207096640a0b40f109018462440750148004032400300100386c0e030402d40c0c41440c0b280328180610700d130000d407580e0f030341480250013112040c194004014001409028031030095114402002c1c82c040c000c20881e0b1009500711613001000c03980418a43d00180103020202026110340d0940d050291069905204001e010f002404070080401c8030180c081010b00104101c480c014641042e04680c0d41c081075440640217081c2c640412810851400c00c00d900e5240a1060400300d0742c041c0c014516580e29183e0031081c3c2d6110480d0418075660278400c094440c0c98a10140003e00b54031003000402150588000e040c0e410b1560001c0c080d843c400f18184001401202c10304215041510b40b01104040c84260041c0154070440040051281c603041d95075001c00c541014070200e20a0302542c40c0301800d008000c09 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 207668956 1250 207667706 207667721
    0x50a030f0c080d0f09060903030b191203050a1e03060e090313050906010302120f04020103061a0a080a0612050606040c09060c0f020f06180405101503050a0b03150415 73
    0x5038403d2242c10980303032190b0452110f05035202030000340700c1c05691b2002d007107030b00090041d000651f84400341985410700f00f507000016500c81b4005100d003460122207280b0165001001800c00001081020f41d140c001c0e8004405440d4280320000d030400c9140000340104000d101c0d2403040040031020035109000481102c03024404805001b010600300800d00104410141c0f01d00d0401da400c21904101030b107140c0d95a0301800c92700f1041c12540c01e083c0001400c1c0c403802c0d005800c3c000b5041b203036400c0c51440c00e000c5580c284145d00303001c51660380b0300ca14440103101640c012503024501450300800c010010030349a104407402c843c200600c0d100d0728401c0360000040d020b140e0100e00341040b1740001c180b030b280210340f200780f0003060030b01c004c80c41201140b00364026141c030001400d40048111100d250038000c260748403203043e064914080c0707048040804074079400c41481c140b41d6600301240c40450305401480d0030000c090b00312440c100030b0040c42144860300b2502511904024402c40150790400c1c0500c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 207670206 1250 207668956 207668963
    0x9010815030a1b050607080c010606020c030634030c030e06060f01050f0c010204080706020f01020a2109021203070b0a0902060a120e0106151d011d1804050a030f0c 72
    0x6550003565941c265141000f8140761400301c0740100050030f036581e900500e43d161081440c0754484000c800f1407825203000e90840700c2550819003075519540ca00103080d0703900c4490301c80d0488101c000c1c0e41c04140e070020031507040e00c06050078051071049140c050704851004552a603040000c0300040c0d0303505403a01e000350f0f4050341c08504025031588641c03040020b0301a0124a2650602e0110241c80e140c1c2242d01607440395087d40c1245c5003c02c41690140501403070302d103610009502d070951140c401401400c01d0706401005880742404819660019488218400e0f4050001c005c0d0318400b03012190340750815101240c40047c1c1070000340c913102144c0642c030740507980034000d85d0410300201c0302645e08101c111402a0126a1525104a4540c09006200052034001c0400346100c01406c0028602c5014400782c1e448604140a85070440c2d07440084040b1460801c034440310070302400d20000e004014480e00c802c4080c0da10740180400d0040100e202c8030203a12a882e40c11654480000a81d0000014135014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 207671456 1250 207670206 207670213
    0x2190b011403010e030403050105013609030e0907030f23040204050619060801150302120c0a14040b19110a111f030603061a06040306020a050702090c0901081503 71
    0x401c400980c802609000410050010a5640200350144c1ca113400030341c0141c94603910f40d00100900d01900e1008503c449000754290b026006980d010802001c0842c0048005aa90110350080c0344c45603203400c5600c4c00041144ca0541400303400100540300a03095040d04503e402944e080010341001400580e10604a4440160b034460f000c000040500030500c0d90000803402041c20444429410400a04540d4485104030b5050038190840300c0c155500039424948100543c0b00010404810b00b40e00c010b0641816603104030b40102100d240c44101003040072440041404183c803c1c0810107840c4404210880780e84480305144100c609110f000304191043d0401d6820700041034404800402101300545900a28603815441258207008400c03600c000903a902c1e000d100300300c0c280c00307003060305030848802c140e100f0141c01c00104a0b03c03e510006000c140e000400309641c0c1c7c0284103440d1016001030180c001881d0901c100c1c0081d61000340c11038009180c07000000c1c5412000a0025011413019004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 207672706 1250 207671456 207671459
    0x2010b0a0e13080d0e1209031c11010e01020712080f0403030b030106050603010608040c150f050c070503160e3303010b090a0e1207020907210c050a02190b01 69
    0x4041c0741401c05028140d0489003005080c0108220a0042c03c1e20f004811002540d070400c041403130304007802c0e20340d0480740c000d003080f0814050303400050504c0d180540c84034100a110301d01c10140c0304070811340800d040a50904241c101ea07500103501820440b40588001602d0b036030894021101c0e0241101c03d0f4514099810100300464403e0b80411404003000d000000c14a0315140042c025402c00d034000c8001810600c2080104099441e2080c001c182d9191181ca030713032490650150003929150100c4d4104900810280c5140b142081110f00400d0701400380c640792500c0b030548c200c1d0141640524001802100c001c134900c1444480e180390400e03010340c0e10391840c0804c0f10203004c10340f60700d48005502d507485005d520400d5607141811401075203001c10009000310400303031050800d08074200904071f2900c1403082d84090788031401030a13070000d218540403000f010520140d000101c04003000400d0a0b141039140241350b6041402020300248030b40854400f064044c544210544e1544001080404105c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 207673956 1250 207672706 207672719
    0x311090403140d0209030a150f14150301060906030f02030609120405060706020c0106170709091106130e0c040f0b03090d11030403080c07150f0c030c03170a0c0305010602010b0a 78
    0x40c2c00d500403c3c1074054644007115000a04d41041304006a85015074034100c05c508151a100700d210003036000341c080c04100019400250903d50050108000043c2c040c02d0800303954080d44020081d124644d030401c4150b8036400e240c6c407100300c0c010080740244180004248a0780b000219428541d43c0001fa4601d014241002c0c4409034020b40070884200e81c090100001e140740038040c220140117070090044a070b0071040e41442c980300303ca07803040c1451840d0003111b070f010401c0c0390300f0030620420595071035590300d0f000410b0205005480e40231403000d01340d400c1884090398410009000325980300214024050710b40815110781d03c01510040f1599102e800907500d124010321a0820904080d0709032420b040d80c0e07072181d20450340f10022100f141d4012038401d1100d80311101900784810043e25011001104584018120201240015041c8001d058200c010075114503208585070f900e2124400e8541002014a0081c00a110800c000300b42841c1c00868401c3c414418421031400007019140d02614044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 207675206 1250 207673956 207673997
    0x105041514010e010c0b07020a020415030803040204051f08030307090504060b07060903090807090605040509010b010c080306061e131a070308180d170a05060d110117010f0311090403 80
    0x80280f03042c0105d5407101000300b084a00140d03c5249140c015000c208000c1c81080111504214002c8508402c0d50042c40829421001c0c1ca901c980d040d540012070781c4814004c049441c150b284002491030071002c0100c1c4108000c400b07940103076810b0721560100b03529101000301380c1c1c0460090f000c240707105201c4540132628a0304a640114040e050024001d80c40d640d01c035042140580203032031309640b00e0f08100420700b8140b085075030003940b0100030412400301c0d0000074080c00340c0c010054040038011022411b035a48807030440310b4085440118000c0407402280c0d01445409c088180d043c080a00c584c0068072025128242420420940140e454800140c0e0103440c101d801034844a000181040c2c01074411008104401c1540340c0ba4660401031a4201174a02c0902401002206158209800e2010390786400300051076a590204242800d201240c1c0105c4003a110582c8c180140030740ca9000040d9905461038500c00d0b02d029000d10070800f030409051158100b070503140240051001c0141000031441c40c0e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 207676456 1250 207675206 207675227
    0x30207030309020907020708160b03070c06020409151701093f05041509080a0b060f130c0215090a02010c03020a0813210f02090a06170105010504151401 67
    0x1c1c20300048406090300410b40d6410101c032500301580c00303040c09100e000d4041001501c00328644600b041d0040c2495003d42e52404050000f00038004030303500c080704001094042d00c0242801d90300800c412984140342040000035885114400d0102c520282041c5406005402e100c1c0d401602c0740720028018541021074078002050950100e100e03014009103814120150903860000799a41d54685003889004584a840b000580060000901c004c00c04c3c2074021441c2200d541d00f01c2c1e42c99080713640d02c40101c0d14114602c212141d01450001c891b901c00380880d44417254640c401d5085032a402840d585c900150001501da0004650000d00d1070401584034508902c24244a40b054a94914013a076441ea0107800030908400441c080c490f050002e640c607160f510401c070f802e03c440107031601c1c4940c80780d4020320b20005e0003034090700c503100c000b50600300300342c21640041c11884900d1100c0d1954400040c000d000c2801124400d0b810843c0400502003c241c5202c280d5865400440034440007500549105004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 207677706 1250 207676456 207676463
    0xc1f05160806030f01090809030715090b0a030e100c0216061b020102120a0804020f061c051015020f1b0616060f0207050d09080706020309060c070f0f030303051015030207 75
    0x104d42c41460b00e10801e01400b2240e45c411480e403919101c10400301414502250801490180004c046c400b207168403a011a003140d42800f201a41c5206200d4120054185805910550b1041000c1c50308840b0b080e5003c850260318940c00d48960806898980800203074074411040019144c1c107810400711215002650b000344140116040c150b0f05060140c0e16030003482c4240081030b004400c000560402000742e0580707003030448039180b40c0040c140e01820034000341803801000d01d64560003d804510021303941e002078818410703056625203103200020354034200e0344180f0449028040c2d044040110100b02c42d0010000208030b18181051000b0482c0d40003401c1e42d081d10300135228044070040010920042c101c06015002074100408001070141c0a410141e2100002d940040c800b00105075000c0103559282c0b02c1100c015566058a05446103001c0c0c036600210001901400000340c05410101c080c0d04480c8203480921807030b900d0031a140503042c090f1044c03800c505040020544444d10036401000d85920 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 207678956 1250 207677706 207677713
    0x1d211803031908040b0105060306130203060114040b040812041a0c0c1503041e05030313020a03050d02060906090304050904030509041e060503010e160e1009020c1f0516080603 77
    0x19030303000380c4000320103000700403c6a01007032106101c800c0500c580500030503540245103007454400304070448900740c01e01c403400e54080013295882e88920400030084503274040380c0b6203407a10b64420340883c0d0700500c228286449001150300c0b04e03c0305031341074070701b00ea03444408190420031055503031003941d00c400b13211a418080c11320401441d554030700703a2a001d05580031001d034580c07620b0716107280324400d2540096101d10005c1c0c04c8200003640001125400b80542d14903c01c0c42d50144080b942c5c2881c1c1c3e400062150003003c401ea00e4890703002501911441d044000c641d2903469283c83c068407482107000742a0424081e500140c0828043ca0040007526030250000640303080040e0b404e20215a00f0109240403600c400041266282c240038400541203640054045817003605401d01c032508803803041c42084030f400c60015044981060340e910040000881c19955900300c03040180d15a1000021b651101e40340c084084980341c92072103180d11950386e503405c1c807803a115650802d441a210007000640e0620 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 207680206 1250 207678956 207678967
    0xf01030903090b0d020d050a2f040503150f0c0a0210150513050403080a02090913020102010902090901090308010e190b0f0d0b18010b01020a031805041d21180303 71
    0x2100000202212000d6620060322240da44100070259140600008125414000d4841e00710b900950100500607107627051410700d10700e810234150280580c0e44401c2e4140030342000920344220328502c0300d114440b50001420365560b010501c034600d0140c03201e0f45006078414030040d105500e0507400a078610f0041ca42d03070520243d03107900152446440d00400d0600039100c500f0702c070401d500070f202c481d00207000c00390540c100a00f01c0041a16004001c02400c07503000000da0380802c0d64000c1d070010700d000da0060050415480c0c207914041c060410f03107204400091035038000180f001c26007150507000c0d0040c841c0610b008081c0210140180c40b01440c0c40383d12841da150200d40c19919080f031842d24a1182101d03400074034044907101c40d40c950101007200142d0410f28540700c141e80c08101002c081d07506082c4401007106500300d012904485030031064016180800100e00c201c0c04030440b90309062404203c0750802c9070500d40405410b030300c510603628110140f00c4080b0003507011168906040c006811241000b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 207681456 1250 207680206 207680219
    0x1e050d0603120203071202060c0d050a0f02030903030907050402130608090f010f060f08010608060f19090317070207080c060a050c03030a02030403090617010e25020f010f0501050f0103090309 84
    0x18140c82c0c00c40035a00c006503400c200240420004801c8419002a100c00d02c0c121075000c04031b00ca14841c0c14000355070f542c0020803402090b40b02039200640a60300710b4480c81e10600e0140d89500541c0e81044501c1203500005407442c140c004c03500c600203000d40d00758000340340441c1500d802c18050042880e60090740401001d0790b00034071039a0341070b40b1080e44c0403c000345003a0342c05013107a4098000030741e16418600300703102107007000520580210a40030700642a03920200000501a045202c8032915804d1042c010140b59000c0540c4951b05204072425045444440d0142e03600e4415215503400361704115440030701d515040018042c440302600b072041c07510040000c0c0c0390440d0b00480e21800242e80c08014001032540c480341d28800b829507410841403200142c01180d480c0041441091503900040002542141d00c03507524903c550040c201825070320b10200406900c4400c1c81d1f42440081d80ba02c2201c442103400da008003412030340c02421021681502000440241546041c29003e1082180c00003c1c0d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 207682706 1250 207681456 207681473
    0x150d02040b1302030703060506032413060303030b0103050f040b0c090118030606081606050d0b01050405060a032717070201090509010303080103030206070305090606190f030b161e050d0603 83
    0x42c00900d54016644c0c0307400c5402030f04880740340e001540210400c0c03040100c0d90020304200c1c56150b12201d2045200c00007803001132004030745904041966410008004101609600315179990002600c0070300940c0c0e541d245800c9410011a000b4148910302400b08408264850080c0260074041c50040703041140075020040e0442c01d544212011a9502c008000340c02080c071882c0110851190003611261504000070402c1c02a04021064566600750320445d5a001d0b008850040c070b0083d000607160322802a000d0010089448148801c09103180c0880705202180e00042400c1d6001e00c880e9907540c1c9203003503070400381c0001004a040c40007a0401050a5503080c00b40d030b000310711139500c000840d0305604d0002d09204001d491030301854140414040c0c071103008180c0590141081e101c207400490054503644c07841600d50300c403c00f00300b4031700340100070710641c8a0404e110b002c42d9808810114200c031300072201b00071a161460741c0390080f6001011400e101300001c1c50403285074500429090b44070b8456810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 207683956 1250 207682706 207682729
    0x901080c0d090f060e06040807030e030a06090b190213091e050c0c24130218150a081605061605030307050703080a111b030c030c07060908010203150d02040b 69
    0x840f20080c1c0140010010b1038058520310f84d910390b000c0c00c02802e095441514a025140008083c030124684166460300c042081d14400341c0c1005040c8059419030600513407085080d262051b02900720701a100500607079000301d548101551350140b200c4c03441c00c1640b0000300321560f94000034000c035600d07042c41415140a624018003000502c00d0341c2d00740180c0481c0c03404088000401c511007482e41e46504c61507100e003506a000141c00c02c030708941d02c80d0f03100050905242c000c5851440061609110000707442c04d8140c05002015102005810f840d0744001d070369101c1c0342520700003d08107140288120305000d00907258603240716112102e54481640c801d400c603082200c0d03440c0000c4001c5a1103060650050304140c00204040040010110a514402e01403054400302c2400100010416560701e40c10000c8408142c0c4410903652030740c020540580d180c104610030080040c0c0c18940205901c4011300c03c0b00d005017036581c460a0341300903502c1804070b484a03281e403ea910a03070314400c8103119260380480c2031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 207685206 1250 207683956 207683963
    0x60204030803010f061107030b061923040e0606040b0d0501020f0d0612050a1205070203240f0f27101d0c1813140703051504080901080c0d09 62
    0x50b1258180395100c8800700700c641c400b00c20403502d40c0c001014130030040340c04000d40e43c10020a048075514580032038100e4401000d105440b200900c0006992003500e6011007070000d01c0203c3c241c2124000082100382c420042c04000150003031004100c00b480c00303501c46500b04101504205c03d40c0d5498071024226046248950707460030300011031a0710b8410500c11400900303003035242d20703201d408a42c450943d20244000d004200c0d040003014020ba007030144068403040c1368005c040b10050b280d1000c403002c901030412081204000c0d10f07800314420410038135801d4070400034804800119929402800042a0040380c0b40c101c4240c0000d0140c0003c1090100d010f014070032090100da488a08985044007070b48101001085800249c1102110b5591a920403000c0340340c005040e141c0d850744001004072400a0720700034400842407982400e681400315600040364091000d81e10380c46c0b03600c1060803c860040314028031046003005844803a6004500417500002d201504d00d041a00da07484204c22500340740003d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 207686456 1250 207685206 207685223
    0xf0310050601030c05160308101e0305010b1c11010519020303100b09010e010507021203040e070201150509070503090106050411070605090a080301270f0203070206130c090b060706020403 82
    0x2240e156018040c44007204e40c640b03001403800041c00d007150064481003200404001001c0d0100e15440d515194017805440b202c0485404818618044d6911074054401280c29500781001200075207490110143e4101c003036940b04964070304a0369100d100c50205c0480300c0c1401800c2c443c8440754410400183e010504503002141c1c1e80c00e245403402144d0419920140600100b000364801c00d0342c0c080c580c3c0952000a003002600d5502030704c00146880162040400782e4800843c0014100319003544903800f130340c0399800801100c10154500300390f03004076008503600518684007160034a1721860055600c240344400000b080c688800000c4c065803102d091001400a01203400800d03c01135203d081d802c40d0303845005200310fa082e03694180380390205101d00074002c010441c450754901c01950b00120310250354401004407070425610080250030a441c40401407240400182a9a8030b00e45034045151300b05280101c0d10745003203900b901401040e21900c1e0071a905010040000d10350740007078006140f095080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 207687706 1250 207686456 207686461
    0xa15090b0a06140406030c060c05030705060403020a1a06010804080f0706110319021e0703020708010f051504090b04060b0d05030310030302060601180b250c090507030b09010e04020f031005 83
    0x3014410b8050443e440b50b440d041080000403000c162484c100c904a091042c3d9544075814080d086004524010b0510302440f0100002c1607804910280203c2c4916a80010176041030094014002c003250168085801800071a010480300c10140a0005444d0152844e19006990303490940d4200360040700e9580300403040c081c2c001400c0300c5604490700c00700c03421400c101060000070246800c0071000310254000042c103c1c181031080c440000600080d200a00c00300920034042401010200d4880401281080f03022a9600d024050f001d0340c6500030001421507150307511964018100c2170b44c0e03d640808074100e65400604140040d5100750401c12003007100a1075400c02030305000d0001d000c28104003054420f007006250180c0d40c603040e00c50709110540c88130820190162001e00403031010481d20b5500042e41c0030070040c4902d6005544040d0402e0056488004c0705409031040350228603404090b500041c4041c07856800c0f810b900500042c020340e82980700700d020a0030400003868046103107858108 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 207688956 1250 207687706 207687719
    0x3090501020105060d2303070b010e010302040b1e04360c050909030a0f02120d0b040b0f2101061502030c01060608040b010303081f061206050405090a15090b0a06 71
    0x10741903001320309490542040070640e40e00f04403280e56070402c180602000d200419150300030015601d100b94401680320040d611340e0880031662000b444100c1c42a800d1103000c003000c4c103111000400c9480090340c210107603d030300303000c20014001c0b20524480c40a42010b2092000407801d0354000781c01a081444039002200b410130040b900c0083d00054010343c001da09004110a0000c111100380340a80f4103000b0101102000701e003440d0359188901c1c0c1d00b1002082080c4200c00541c00540e403090101c40400035807044206201d81501c01c032034596400b44580a041c5054010040b8800303039038007164000201030b51181c3c1600c090541d42e200840040e440800e1003034011a0910510340508003c2c10602d0840c9481d50718280910707070502000f020080a07401040345a10035400152101c99400d08070440d41751601c0c0c0c000c10b08400d4103070010301e003030030590001140e00b054030034030740a805040060424007605c0e86502d98258030301020000180c3da40c0504502080b0321603051400789040035000700d0f0161a05070f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 207690206 1250 207688956 207688961
    0x4090209190501051903150f050301290d0201142a030322030e030f06100b040312141e12011e060305070e0604170708030a0804020103020304080d09030905010201 71
    0x7822960748050909003400640c1c0c2050559400d003000490b4154150f40c1010124081d000030746a400450380c96140100e4441185a0341009440041d8020015120081c801c4146010826181c032900114000c504146040030402110614010b06017a031004035902000c8000d80d0000c0035010f12400c00040740c00720445540a01042c4d400140c00660841c03d01d1450200100068100d030781040c000c04000108050042c01c02031307000c2400506031807000b8943c01041380c03501d80441d10301899031482000071980090702e02c159000d0301c3d0055a4100001800c140980c3c245a0307004007074400345c0051003455160741c10040f202d00300143c040c0100713848004201500e039400d64182c002d584651446a180400307010f078461040112891403030b0100b52500e03000c0094070fa401c0b00c4299030390032003030004d80410f01010101120340404940d5003243d001c20703622686242c80e800b400010a0001e00d0070b40c04100035600c40d8018640042c0111101468011a01c4884003101c41e03901e001c030080303590441c00700f02e20360b02132 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 207691456 1250 207690206 207690229
    0x10c0e09010e010e06040f02120402040f0606051611030607020d090501080106080a2007050c0a350c0406150305010501030b0a090905010b060a0801140a150309150204090209 76
    0x644600303032154103006042c07240300014090003009038000000100301e07641d070f03030030088100442c1181103584418074464415030100446083c0c0c09030f0f00340030005040710118450300c5e0032105940d58417420300f07001011444110980b003a0659102c1c1070fa0180d00c1d80390754240701090095a090f0010700c0d00250955000d41130081540c059410f000c002d40042011980207a82c80b030303006100783c1e000115110003001c0844010115101c0460001d000b02d229020807a0018049583c03010898070707414190b03500c0390030340c0c60f2154a10003040f1800d554550f0181c14903a072400030404082407000d41d080b62071540007050450750551b0007251032020340310f00b004041e0b40520030940035080c20b180501c000c00d0a10b000c54190540361042c005d0556451040009101c820740c070414401d80020300841c0d0b50403007214000c02440081c0102c0502d600750842c40c0301c0700d1400030000000c60305241e542c9084c00215500a500500d0585415590071900e81000042500d0510081c4003520200c1d00058840d07a419060000c1c2e00c100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 207692706 1250 207691456 207691459
    0x702030301060f030c0c1e02090f1e10150807030c0f051b070f0e04020a080f06010e060d0c03060509010f0e030f1c091110020309220617010c0e 63
    0x82005100c0b4550101124400c10018200807a44000c482030481c0d004030340e2100a0444014140c2c0038000003810124840b245c1d00803221983c0d0f40d00d0703c050300c684400090340c084241100070700c5c0b59100c031607506906907402404030501311140e40c1d0755455400c50f8018586500300241d000b8040000c1c0e03542503c0ba011804c15680780c03005070088084400740c0b491103843c401d4460f080e002c1714503001d0300b503040113020003900007100d14081496a548640e504004c042e64101d02c82c5911031404110120006880000900841d000740082d034a01808a40001c001902041c3c100408607510004182e440c0c420300002c600c1400000b800d81382114515003100d00d20107080000d039080226410780e000001042d03c4440d010640036035507070b1441c11031514180007108800035266040c0b01d401410320400b5846000441c0d07043c0c0707041c0f09414091703004907240d01c580700f02c0603800342d0051101c1d000c9145290500f03d0221078510001000c9803241c20042044041251249082e9110682e030000f203030344001c1042c5030150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 207693956 1250 207692706 207692713
    0x42c0a050a06060c050d050315041104090c0512011203030b030609060a051305071701020702030d0f020105012c0702010b03010f051b042303160303051305030601050616050a061103010303080702 85
    0xc6503030b14191603211000c200340030401c0200200d484d0303100c8002700361202e05008200b04404140301c0740a2070742d07030458402c210380b80d403a103440e004405009000f211810005031540904503800c1c0707035a04080002c01c0600741c08040c2d840d502e01c010303600e0410610340220107060040030b82d407030624581029108010301302ca1110003580d02c5240012000184842940d8007010140252254002030900a0040700c078060751501c01c43c2822960907800c03442c075402060255000303015070303a2600c120340e0700c501c6040a12040100107103004180011160091340c0c01c07003402d10010900c8828403001038290756a425052821580c2d800601074030104907008055428100c01082d41030521702000400182482100c03501900d20b24070000440c2d0b40c00b40301c0c405080450b542101445500e03820000d0a41e000480501e600031660b100126a900d03000034417034103c0d18000d21080c54440c0814810f99049840c1c081101c19108490a00001800b01e00500200d04442000540c9a41c55403c00500889014281005640 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 207695206 1250 207693956 207693977
    0x2010c0c03050d32010e060105160614090c01022a09040f05070f080c22020f0f071212020304030813081209060901060515042c0a050a0606 61
    0x150015800391105030582407481d1185006030102014101d00c881d1150040b260101121040300c05203d00900c1c1c4800b05a207010726a241c9039113801010341543e400e800300704140300100c15082641c41207401544600c0001c120f00141c03096550154034255181c4032140c10229001d807003540e04200380c840035501065040707140e07405641c3e41c0401000300030001d802084036200141c148084804001189035106c012100303100d54030440c0c2142c1c44c4082c01500017034003518444007614500621810114480061000f4011b20001204402507101034010b020019050041121441c2c030300010340802b50080e80f042c6000f2110380d070004c00d17820340034041210309841441404003183d40b00d501c0d980e0110714903190704000b1043c0c3c1094580350050303140480302012003d0810013084408148c407030003400740308020301c40345032170300d040006000c0307003c400301c002400501081016a980b817003004d516000401441050f5441c446103c40a10800c0f00e1a40c03030251103000303001c1040313818801e010061001f860040b80c0c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 207696456 1250 207695206 207695231
    0x21c02030402060f030402150d050105010f0c120302090102210c0613050613110d1103070503030403080d0c1e08150a08030304030305090309030a03091a04060503070c0602040b0406031b0201 83
    0x50203a041d007101d01c4c14020000400715160881a540c10155081201d91240014220000544400d005113400183c0300628490b115000e5079080520607070000c401c82c900075036158101e0094010144c0141144a0580d4602c40c1748900c0c502e04207a03421a66050399980138117005903240000c040e16094411a00450741008942c000c10b44c280c210000402c1140503001d5801c0800251000c40c440b16070100c0b800008800b00018030081444141054040c2c4050710b51719000c00d501d0b070081e840045c001c00d40400c45d0450400040e4450306511a035418680402904040b0404a281320244203501288404050010100112012403040c05041b6816408181403042650300da0001038030040605880d400031a95441c030900030b588512502800302c62190342c05080040904405114805126400740c204030b803440f0041048805940325a16090301e181c55408040307031901e081070310584450b5070134000800d14281080061000704150703900801d4416280070109100d0180d180041c095a03d00119060742 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 207697706 1250 207696456 207696469
    0xa051b04030f02030a0b0c07020102010507261f170c040213030b060f030303131104050610120608070909140c031e010f050103050114150a051017010801021c02030402 73
    0x50729405242820741c0111440400d1402590000c0184112a444204501c5000b94400703800114000d0f4000c2c071071074913803801c01d841010481030220054415280c41801d05605042869040394401401584071600e0642c201c3c00042c1940020020650f40c466091100b031b07040215140d015000c5a0851400700e004400710040c0c4090b01c001405030b0f840f000050030a68070042d450079608000b609031703503483c40c1c00c8080d2032128140103000c4684021642079080c880c20a03114851003000d01804c2c4001c103860f03011040e9203004100302c9662440d902e0b10000305910109100b500000c000c01000400c84080c1440e0407000d0607030040c2c4c503180d950b100728014603044e68005840c03a8400241000c03a842d00200240c640d001d4001c42c15164860b03030501000104001055001c01c504c10045410881c46445144141c68108240300c0910380c00302802c0814051450000350030038008038141000d4201016040100115100983c001d0b4083e03540803402c4114024581440c0d014a0008170f411842c5103881d50001d030300f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 207698956 1250 207697706 207697709
    0x609071106180109120503010807061106041e0501061d0a02030709050609310b031501062015180d120f0608120403060c08041e170c01050a051b04 64
    0x11850b08801c40311004590039440705240c80d030001440894000140c401501c1c5502c01c0c80b03070813143c4c452010006074941c0328200d4105119141700150429481d16114117000302d19840c0104071503807000480c600010002d201c0d80000341009000041d17000c81c90440ca0000d41d00080000d00500d0041081005469002c100b41c0c00341d500480304261100717506400310301e885446084104424074048100700000010460440312000700041c01c2c00f12107252418961183c4841040c42c1116a281c0c005004030f0b40940201c41600c1020a01c180c001010101301d00d15007440740c10b0721180004004203008a50005c85145401e4045000c0100030140d42d0540c0145030baa09610707410051540c40e0400074034034159801840040070700800b1602da0603028100480079901c1440110355032031400d400303089034034068440d00f031283d604100e21828003804d6144510981d40360031411101f00c01d400c03d846a045548002900011020743c000082918001000e00304881c4090031410035075000d0031203c62040c06c94400c490 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 207700206 1250 207698956 207698971
    0x1e09020a12151a0409050106050a05100c0807081c09020907080115051c06150e04061503020d110c030d051003020f01050a03020c030414270a09020a030215030609071106 74
    0x5100901403809800c3c50700900207450303006041080703020900c0015081102035480840780704115075510790811407025120081600400d4500c071407000400c1d8070708050801240070700c48451602e895060444c0c19000c0f5900164506c1e41d03202010380035401c0540c0d5135540b060340c2d42803108980d414404148400201083d10408104002950400351810a041311565181e000810b20405072223800d040c048105c1403141c10005110210903500c0b80c87d160103440201c85280b60030a04165820108070040e40c01100da5580c01034407860301c0d40310362070010010202241f050010319115514680d175002915000350206185504c3c072003050001d0f0340e0f4810b030701001020900f422a501c0c07030012401d90184c05440c041e248203003c0480c00081c0f5400c040d4124000140071610110f41004071000382445c8965448284880c004040001750310007078035804540c0d0980000c1c100b0225039500e40c00141c40d01c800344281892000040148200c0d400d212021a0f008981410200b0b5007019281d031140e9503020040605 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 207701456 1250 207700206 207700211
    0x8030c0a0e040608060414060403080714071202071703040b03010506031e01060906030606020303090d0e040e070909021c050a030f03090b040c0e090a020604090e011e09020a1215 78
    0xc0c0105801080400c150190280091203c00da840b40d01c10344612040b6000d880d030203407100c1801101940030610390f1040740c0c19207502d41503480c2c0e1242110540e0b001c22071140c4a400c10000300004c80c159035000171000304141d00405111313080c0b808040c40d903217810080b400c01354400d01052000009484c10381c0d040d22001d403070450b101c1c0c2e1400b00c24551800d40004015101019400100740c1c45e504c5142c03a020743e5441d88041c0110380d65010103c3e901d20085681503400e800c800d0f6003140e0248a2102440c0d00d40d00200b010415004a043d0107091000991110150381c3d5914100c500310306001240582601c000748030200c0840b40d0b910b0302d070b8640c549110020208417194400b020b91034029032187e401542c11040001041c6843c2c40c21803c440d460340106120201c40e000000c4402d1000291309580607800f03406182040c0c5400051006400c2c1402e040c01d041d500d600400c1c940c4034004943c107148003220b400114a5036014014400c5a00c03454021028005002160314081610420703060403503240320320300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 207702706 1250 207701456 207701467
    0x10609060f17060d0804060305011e0510232a01020f03040f021305010b0a08160909110d020a090f060f0e10030905030a02150f0108060c030703060302040207060204031e08030c 77
    0x4c01c00203500c0c03c000c0c00c1900124001c110140d00d64400e506860380c0c0038000c1720002e031002e03200311413100d144031b0b0a51222000342460103040c425030325440c11300c050180280c0040021050035000303400800104001c038144550074034564400d004079130380e4490300704000c40c07409800090087c2940702c018005050040c00e8100c02e400c640720721504980c110f0b8020400c20a079610340111008650149605c10009086a404102c80106d40040200303041c00740d03211f03051102c0ca482c44000140c00244000d050070350041c0400c0c004008180001d008a0740c5d259a41c5c100141002d810082c0000303107030414010080d01c503c0748525160803c2c1011070040b411540c0c203101c6000c0d0041100602403164000700140000b24850520759000528014140c140c4403000205a03203c0030310b1304580c8801d01c5411600c1c5c1c01400440c4135104103400a5400045601e0f000c10800c0d1290085400d0f03900c0400101c941650008040050002800c14803140000b40c0c456840c00301d41c03a49030989680009080c2f0310124400041c1d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 207703956 1250 207702706 207702709
    0xe040515070504050915120d0f0e010c0c03050a200a05010c0203030910051911060f06030f060106020d0e01030e0c12010902040e0102070309050607050a031b0f0b010609060f1706 78
    0x68030010100103142e40106c0c0b030001c840c59081c452000d0060702400b00c2041c0d4140742d20001c40c1d4164580c03075654507500d030211100c030104c0b20b00f2458441141032001b01c116200206400707044134809075009100400e0000744624082c20045071500c40b098031201c0c864040c04955845e0541401200c80904e000011220303940002400e6100d001002544242010125450305070044060100319110080505220800c3c0206030740564407080b010101da001040012040028040300765048000079040381c68100c51400b0403440e140080e0403000160f440b14140103103590740540b1100140c1401e203402d0140594000d042c0ba940c3c03c045034514400c0c0c020806118280400350b10004070560014020703c20005420f070003a000b90300c0712200394005420848045000d041080407282d481e82c0c881e00501002e40701e600c0440d54044030040c11103814280055602c0803030600c4400c074404501800051407554540744001d0504903e0b60b00020501017080524100a9008840d40d8020a80c3c80c001c002960748400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 207705206 1250 207703956 207703967
    0x60606120f040c21030e0105040803090607261201051c03122714160306020a0302043506090d03020c0703020a180b010c0f0f02220e06010e04051507 65
    0x4110a07007600540c01083c1c4d40113844070990303483e6402601d484021044072001120036104030b0040408070303842002207403200d00701b85008015417030041c051901911250a040400d28146010040580c0808603050500000c640007030390041c28115010012015401c4d0b86072000806858044c0038012032291040c0c0c0342801d81c20144105012004585a54141000004c101c02584000740c1c0d0a090b4680381d01c07080784000030345107242d10130000c0700881c0074a541e80e11406035200841031000c0540900c0b0004a90303030249000e6540d1900440c0311200c54980341ca4a8241031009422104203030b02400074000400004244030b1030b0001189005070795080107208161501030f841c2d000030b411040b80c80700014601c00c1a20110080d00040f80c0174080e1031509c4c00111400d4028000103401c81d850601900d001500045000c400395202074001540d44414094a1034001c41c51801e08601c640c580f01d41c0800000b090120358050410314001d030200b07051031303220103540b00d80e10309804103104038800204800a020b034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 207706456 1250 207705206 207705209
    0x601050c01092a08070602030301030f03020a02060a11011506051b011e02120a15050d1a04060f2403170c03180f010c0201020606040f06051c05060606120f040c 70
    0x82c00c5501c0d8000c0000d0000ba61120a8020700f010344561201240302000805d00c1011034440e81e000b1402d590940c2c44032400c21040ca20124190321a1080060042c3c03692800340c9a01c6080ea21618203064215201500391034000500582800032a001406150b80100c02e490662200c0c8408003411544840518010300203a05603803c0307201c9210f40e80722240c5158004044240c082119074203691610803142050f120f1300400401550700074401485241814105000440e00600c000c5001150001c0004801d40d4191000d540c0385495000c11500d51065004540746081071007d10103100c101000500c074404518040148550750b4500700b003c031000c1c0074056549424201c81a20341d1ba070800f8901c00f50100c24140000c1c0200c80c00c80300008903600410301c50301002d4068024003843d682c0c1c14200f0000f043d41c03405c80f124180c3e60300c101159a13120104c10348030300741c0481170780040482d160814070710702440140440c1c89000d0410141c000203840c02c80782c9405c4020550341078401d40b92032614414a000d02d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 207707706 1250 207706456 207706463
    0x8090703050a0f020f0a120215220306181110020c030319030605061c0f0e0a080301051503010f0b09011209050604030809210705070302040908030f0a0c080601050c0109 74
    0xd2035004000d1210f000c42514609200700c400384020f1079800207001120109114040c0c4400102c070500015041058020202d01d2040c40300350b01d41100705050780401021040c0489810300c0b0b0550901c1000b09030300c10f414010000341444450318a241c1c0d80c15480e907808000e4980140528010014018000c003d940714415004080c0c03038403802c200341031030001c0141059000c0024100034001072542800c4080b02c03440c00444135004c03901c481111410b000380100c13107201d5196035618482e4211002091040789507551140e81c159580f545007408006500040940050100008000400c444500074030400304a400d06400c141e2030f841094010394041d81d40d039201c1c001c9035044c480400d00708440440c501e03206910036140d11000b926509104c9554514100c0b001d0b0801c601030807206c85208a01c2e001c0e140740d174802ca0480780015120350108041d1542ca0408851101002c018050b00030440e00510340d001c5840f0204000824400d40c00a04450000e013801c0c2c14880c000500e0382c400242074115050700e542 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 207708956 1250 207707706 207707713
    0x9040e10090317060a0303050304030e0102120316080105040c0504030f0606030c0b03221e0804090e0f0d020f060703020a0324080f03031006050307020f0706030b100206070f0809070305 81
    0x71905000d00142c3c3c1240c01c0c082c00912800000c0c01c180f804c00201c0c07040d43d4145d580c140c1142d82c3d942c0c090340c0001080400b58154450b04000030f00140811006511407c1501d5210400c3c415003840982001010f8118501c00c9050820701c400c21a0b02c0340c1542d0880707030060a080404613641c02c0c21001040141c0000e03060174008031000c100f0080240040d8019013107a2480c3c100000e01116510100f0343c4030034001d2410056644040e189070b07489410440d81c5009204c1a0f03c3d140e940d908030f0040b0f611196032031603c1d0704900240c809003c0280010079512029001038540d440c0d00340e10036030301d5035001461b0006141d8042500380034a803081e0b11080001e129400b080894060081005105d013a640c4103a8403244901840c501d44050013100b5240216507007076078070700c035641051426600d030341000b0001170031445035881103c0600400c00800c80101003503180001d01c090004144a0f60902c1c4c1c0f403440065520810070311516541c404110701101c40c00e4500f02007580c032080443c5042c00c0050b40003404510 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 207710206 1250 207708956 207708971
    0x10051b19170d0e07030b090a0b06152101050f220f0618050115030212060402090f0a03110108010f03050c01121b03150e01030b0109020901170c0304051506030309040e10 74
    0xc00007070b840b0245c03401004201c480c0d03903d0b042d0440d81d402c0c0c45035000b41644461000f1440c642171414080100003440388071142030a01010702c00c0e46201100c05070054070900040100003e003030507541c042034a80c040d210a0510500350115104100c180c0c0c03c0c4662181c3d8441c00240012100d6001202400310307001d54002d040743c17821400c0c02070721080c003455161100e031401701d030681344c002e100b1a0320005081c5106071040c1e4901c00ac000083d003214517000d4000d1b400000340182c03030b0b403115591009944505100c0c017151140300001003a00005800641012041c21400c0c00071800000f03089664081c02d00c0d0601c000a04210140090081c080391010300740c442031206403c03aa00b54001891014101512448881e660a07503401948800c1c4000741c40c04440c4030043c08200a80d8004000b80c52060402c49e210b000980c004039180d82d0304480342c603042c85011040c0700030840d0900051a02014030b086500e080e04017900040d031130780300d000307800f91085664001404034584d0a0180d00c4030100140d10801c80403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 207711456 1250 207710206 207710231
    0x1f06020f010605010224060303040b0313030f0e0a0e060a081e1204151b051507020105060d170904091b0510031b03020903030910051b19170d 62
    0x2203034406120502942060800f1a46510000704c0d0028a090b954000c803142071000610000207401070880f41c0c050000f02b1010520203841c0000394000d0b400e44140c181101c445040050031b01e103000c0c1c520402c021812060341c0c0740e9655403c040c1c00791080c91404681179210440092810041584580f00700d002c0c0f501091301006949008003407034140281a180c0102038010b4488191145000b05910401c1d0a8421055544600840d00301d5400713001500300c0e128041d0700c806182c2843c56600140044034501000302e420782c20300840b90030400c1690000740c40c0341907980b00182096003920240ba4403802094001d40d07903556421420034690480d01916007502d0480c940c04204506002d81400342d02d5058154107480e1091007017000711400d280040c8801e07142031000728040c2d030201321300540c184014004800980e91382c0700c1001c00400b007030721540d80d00d0322882054002415090903414207900981201082a4125040041c0650f400015220103903c6604a400e590040e6226080030360715021558071039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 207712706 1250 207711456 207711463
    0x4091a12010b1903020306070818030c030d0606032c1501081b1e060a030212100314190b130b0f0109060f230a050303160605160807081f0602 62
    0x20340010b40f0350b400d440340380411800d1411001d110081d01076010100081c290f5103d41c43c0c1c02d03004485182c46c004900300c1d2200c0145941c00070860b0540307503040016440710068092041d100204000d017001e00000d40084200d000ca1051001c941c2c00c2401c4041c0e5031003000030103205c0340340e900d0304c2440394143c5561500045a9151001ca50b40103080c0020180c048147c0380c0b5200d82d91003030369100000c10202d11540141b0106800c01e034036017401c1c55024090246421406007130140301e103101e40e40c0d05c0c400b80c1c514202241000503034002c180c620303044480300104541c0c0841c0c004062070380000e1000255120b0351005070f032000c41c0c06006444410782105000008024903070140c12030308440b070144002c0340c4580c2d00403c40e281c18031a0800c00c40301c54910f60301030540200800d1552400400740d148aaa940340860709580c05a01104000b00806c401d60f0208102c2c1e11440c1d03088519041d40c880071000226014058500190a000600204000103122403c3c1c6a0b44c0300741021050080810a03030352210041d68 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 207713956 1250 207712706 207712721
    0x60c3c02030c0306040b01140d0803070201021306030608120f0c01020f03090d0306060f0e0111071e0905010f0302090405030403050d030212070c08040605130b030103050c030601080303010b04091a1201 88
    0x7190007002c0c5084418940024154043c0703800c0858240a6442c00901800f141c0a11380e0306900940b00c01c040b000401e544902552040c44607070009a6100030307509100b40841a950040b000340341c80c1410600131101c000034641d040d811803111340383d500e640d0785900840a0103101c944900319800029189540d20100300514010000d1034200c8043d0321484e00f050f0261070660050360300284d60080542540741c41800c4901d240c2106050a0f80703203080c2e14211034140491500700c103910b103070208040c00d02c420312402503030001c1018101c100070950400c811081100640d02c4064416103110b000701d01032203810300803540255071000c110750284000000140c040c1d04061013038907013800d510700042e80c42c40c02070308194082da070311041040c0303401d060034802d4615804c50580c8a0180d242800c01080d000e04501c01540a0f5004000500308442e40004241c80d004c0160814443e0341c000b400104050303035032034081d00c095410303042d80030508072283c052003d599461820103d41c0401c3e40c4c5241500d00d401940860b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 207715206 1250 207713956 207713959
    0xc0f07081005130b06040e0607030c090b03041e02060d0501030309061407020f04050a060f180507180315020d020304030e03010b0a05130b01140c011a0a060c3c02 71
    0x11a500115541c6008888085070070107000c1541451010010b10501601c5a0040000303000041e0001981845494041c1c01c0390700002180d03407104841030b40c0da00614244000d11060a4042c0381d0305d03241d91000d6010444149400030240c40e10b011000315a9400e0948a180b01c01c41c6c410007030341d80d60307050080004c0824070a00340480d45110040941019007002c5400f0503030060031901880100006101c0180402000702d080e061381c812010500094501c000c8006010301d8000f020300581520041085a0740174140e1003d01211a1800014400602622040300e40000081d03520740c405008001c041d1040070b00028810744008104010942c00503030141c0142c40c1a00200b1611107103100b800588503d90003100d6000d009283c03c00d600d100c036608400f400d98018503041048004111250b8426000141607522a9445a0070010442400c2e283d00c2010b260445000b8902850170300060300d0301c20000d00c017038a07284400006605030756400300c0300e120042c00031182001e29565030540d001e01240014049 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 207716456 1250 207715206 207715213
    0x3070b10050103090209060d0c17030c0c0102060f1b0d0204180b030105150f0d0212060f06040506010c02120c03030a0c05010506040204050f10030e0d030912080f07140c0f0708 77
    0x1141c40e52007845244180c0b50301800d50f4080b500e0701c5040125002d1240d9040701d001c21038038404942c044450203c0414107200c00010b6454240c0700c04a0307418102c940304403031304550000040083c0701602c4440a500685040d206d00b090300a580c00c15a214840c250042000c0c40c00000c0c00540c910302c0840440365846140c0040140d10000001c0601384ca10030f80703c0441c1080141149140e0b454201001d00b03040d000201400d1070042c4590100b00403442c0c0c40704144450708084100001c0c0c02a41e030300c140c0c0c00313001254208a030b85801c50010700b60200d0701e540640607100c5a800140803070400c011610810390014101d035207030030f40c05c00b0013414001c890200311269401c01000c43c2450519000b0b40d015660f0040a07180001008014010702003650001ea0040603100d030203541a00c10248200342c84207619640c040b0f540a220301b481c0b0b0490802005010030440b44c94100088081058003450300070640d0315004510390611848401d2a01503003c070740b85640038503401000315040c0069020226040c48098 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 207717706 1250 207716456 207716459
    0x20f04061211091e04021605061003030f050c03120a05010e090c18041a0c030702010c05040b03010b090105040308030a02120711120c0109051002180904080717070803191b0e120a020303070b10 84
    0x1110032b001100d00c8028042680580100075690056010344510200d420450303040c42c104040a402c0420150b03030390f08489a60311300500500505200055202c6003680040c00911101d2021400b2842d50503001c00240c4070390340100f8204000b00b05054541819445404203c0c14412000c181030b030710a0b68050003561900307004800081c0180309440032503d00d02d23006400c5070701e04032803000d9941c0800a0903041100c00c12000c0000742c9598040c40c002e542c10400107803260000b0311980d240c3c1e9005000203041c403084424044d251280040c5a044400d8480d8850362070b050301c8181c40380900440507000784035004000354401407210782d5000d1309100038801c81c1880380d00c1220b02030121030301c81624080c12002080203281c0201d400305040b103041800c0400c0b09494184152203207402070304203441c115408039403410b86901407095800342200b002d900d00f0315001070999074074015104001c0b00e03200d14000d2081007614a400c420a1103103e902c20f4014068a07501c012034a00080302c214101d03251103015002020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 207718956 1250 207717706 207717721
    0x2040906060e1e01030b072c21030d0906020906120618090703030f0e0907030e1b010c0f02030c0d030804050f0309092404020f04061211091e0402160506 67
    0x143c48143c81c0c01d002842081e402d64560f41600c800051400303081c044410f14044025080e1303220380c205d04440c9103000d2011150a402c0200c40c0f01461480000c2c3d10980e040c8880d022004011100300701d00c3c00304001805241854080040e024681119a00c1600400ca00c003683c03500d07045061041c0021610320f205100441007a0028907020745100c4001c0d80302842c1400028000d051502a148c0c02d4140051440c0c405000074010705c80480380980001d84410f2414601d601c0cc010103050a154000000c0c101e44150780000c002200761080a000405a41c482e0815918180300303080079100050f00000789001d00c1e0030003910b0190b055030215040e1080c070701544590440441902c414020080107141f01d500c074003295a034200f0a003105441c41c414202d180140942d11031000340b070030003407540e5010303140ca00d0704c1b40240511aa01c82070701c0361581082004030348140054215154160b080340e00f43d40f20882c003030014482541201e841c0360024400078005120010100b012100740340319504035401540e400c007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 207720206 1250 207718956 207718981
    0x21e010513080d1503110405070906020c060a030608010504111914041d060f0a0e0f1207030c081c1b09050f0f130609150806010510030902040906060e 66
    0x84040c449900d01101c001e00007407841c402000001000207020680000c40390301d8000611081d88100c41143c0040f1110081e8102809101d5110600307050080144c1d10702a000383d100c0c040031400703500c151000640c08100901a40c0520701074554807008000c03600e41490440710300d401048050748248000e004807a018505035402100341c07080000039920709518001408050124440c1d2486005c1e03181c1c56846408034108010f52168004c16000c0c0c40c94142103030b01204564800d006000d95800c00e205100d0310080008250320001300c01110142e6608a81c1002c031260700c081807000700f00550001d200d50012142601728100c0d010401404c00000b1160802e06601c641200c0c0da62010841c00003003044286000e11104200c12005400d128403603105000281200d1040c1801d50402070795140b052100301c206204201e0115200e541801145081400c00340d61142c05118036885085444c0014803020300c00d0b040128403a5000d001840502c920345000d01c06880c1d10b0094031104041000040c01340310f03842 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 207721456 1250 207720206 207720211
    0x3031b0c08030c191703060604150e04060515030408030408090a060f0206060906011710051c12020d0801090e030706230703060f03030c110a0806090705040603121b12021e0105 77
    0x4a03011900004580c002405c1d1700001d05107030b232044041c80f000a4803911610041c40604003952244440070b040d00400c8111652504038a000d8585403103031021305080001140d0308a904030214172744039500ca10742131219214038613505400c0440920000340281c9c0141040c080050541c0030345210307a40e031409114460800710350003800114078205603520a00300d00c94141c0c000c446900c0100007992944045240851504c0e07100395091642000f40c8244211450407a0000742688090005403882c000010301500301802852491651001c80c40341400082045554455003c202031142c1e02100d00101c05203d4984c87c02e1640a21240004030314910a00c0781d80184d031010300120f4007250441d14210341c0d080c0d02c0d09040b5800c001100002c013282d43c0324a400b00c02041500001d0400e032502070803176410160303e5444035006074241001400050b1107040341182191840ca080c0409181d04415807404070944100503100708000e12020304803d6021491525980c11540b5030701d540c2c0c0c43e81b45291300f01c5104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 207722706 1250 207721456 207721463
    0x3040603061d04060e120f1308030c0604080c1606030e0609011104090902190f0503070e090c0423040305031006020a11040207080c0d020307030807050a080103031b0c08030c19 77
    0x1c9000240000d00285d0029140700040c000702d48050f0542008611703503610140b0104042c040204240c0520102d030826a005400900e0181d8201600091419078810010b000103103805130110b140001e032442000f040c22500c0070a0052100240d641c40d02500908044520039036900404000403031101c014003c02202c00042d91105150925010409008280b941d000f2680109402c0e00311400286034a01d245c0900602d601c40711685203000d080515220701076008041b03840c3c2c403408100c11050045000f4030307403c0d415200030400e141c80501980f0321a90030030105450b141484244003d15900001840c0303e00e4004000100140c1c4610013a80d0340d01d41840010000c5400004444c124207146c3c01800301640300e580301c02d040002c00e0403100d0a044924200000503030000c91090240343d80044000d400030902e060107071810301c043e8001090258140806000c1c4408007005003070540052640d44510b5411034001da0032685c80301d10306601c0782d000240400c00d520818000355105526650302c507017503591 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 207723956 1250 207722706 207722759
    0x15010315060503090c040e030909130812070e1804200d06150312053006120f010c0806030c010305010e0708040f080705030702011706060703030b0301020c07080304060306 75
    0x54441c08489a40c0f000301100b4490080001c4c07000380361106d00032120314000e0303c2d01640c1c80d40156010b203c1403500c010020305d202840050200080380c0c1c101c1c21241900d113010308400d140c1e13882420503a60700c0c114580003030f0410100140402070501d24100c0f2070049120b102c402e022a0603140080090913850000b45501105500101001803500d600c4648001d401c4c05001458603070f20348481506500c0645940c012400001da2900b960011800054610b64000b00751485910783c1c070102c0c0070340007000745203034001d03000d5682034054a20108034121201d0003d400921040107560801050300e8010b6800600078400c4c01140d101940c041d00540f4103a03030f50624101c2842d500c07010216a40040940161003e11249040344040342c07240d801031249500450041d035503000d640c4001000441c040404000800e034200a001d031551707030301088600e01605858007090042030500060300a1040c0c5060134030f18071078076500040d4014048068411105240c03400c21a107035032030701040c6101104e012517006911 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 207725206 1250 207723956 207723959
    0x803030118090f050a030507030206090610030b060a170c042003060d0809040f020910020d020303130611040e0415090209010302120a0c140a0602070302060a080910060b0315010315 79
    0x80c2941c0080110b030b02030a124200940140c5030700c0d00f02000d80d807081d00040c600049090905404015458200c90548014603451074054032040101e4010300006041d038440f40003051181c0d40c1c1c0003800c00a040c2c42c0b14001402164900c000369120f820400d10750080b4140300d200421184440101030080310f00d64205491a60f8240400000048411040f524010140040340003615281b1420340552240040165500b44e074004000080c6d8203000c00e002158001e08140300c516031b01000340c03038220070b00001d0024124603914005001c0c0404c0400c0d15021038011a00080c555100003610340168010780c9040e04c09246446440d040e40e468020103908446188010030050505d5a0f05030700c41c56080d0b003174484e044565038808225851551051074000030800a501d45e615128005030000e200c0e0703000400c049440c4d98080380b500d016106203001401408030010711011401d0103100d18038040490304202003915070744900d80a40050310107005400c4e9180030986694024441c4100d4650715504852480e0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 207726456 1250 207725206 207725249
    0xf0604030213110408010f05010f0e0925080a0c06090506030405030a0f0e0402070f15020a02120304080906160b180c040b031914011505012c1509090108030301 70
    0x40441000c0c000f1000c1d8100b1002134050300a2160b2220f1191001001c107070380d4503040101501c40310b0350304000083c0d403844c0180a2003000004000c1080307189948201c0503103100c51740300d00d2049640c1d13001c5290b900900403c40c04215401e0050030503030b413480d00c8602e581070f2100280056400100c5005045500c00c205502199000f001c0300001d4440b81e06d8291516002400442d0517600060011610f0340000c80503a0100180c01008603940c8851000c11400c004404000a5803990100444804d4840020104d0180181c83e0211a0040d801400b59969521803c0004800e603564903810b8070006004004940c09002c102c1541c841d405990000b84403030020f4a0410000b1314008250075410711078a2204c904906186003000314080c000d080780f003000480c0610140c02c0d120f031203d084806020041c801c0c4000d80e004140d41800340303520705480e81c11082051881c503402c6104021a40c0c000c41904524000f070303040f640108031542003901c0000e80c0d642d032450383c80c5e96400203001d6020500340d4502c0c5034210 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 207727706 1250 207726456 207726461
    0x211005130b03030d090515060f010c02240304030801080105011d0402062107120b030102090102060f100b13030318140d050a1a0f0112051207051e0c0f0604030213 71
    0x1d0700060540e4940100c03401e56008a0302da19404503510b4021034a0000d030110f0072014241d00c42015901603440f081210700081091400e40d03402807141c1c5c101d40d040d02c50038002c40a00034a0041d05070744650740381480c2c14042e02c14070092150007015802c000002c20700911551440f0200c032021101420366840d03d0b070812805401240c1141c80f0710040c003550050b501d035910300c80340c001c803500c5d1200031496059092150948092074a214004d0303004001242c03959a0000f00b10307170300c0201300d542c20b8442d842c2c440382c141000303590341d1000103080d4000c0384030b0640b1881410b818003102d00c29298a180071030101c1c1d601c0840c4c40c0e24401c92a603200c0d6103036483d10070304242c041c000d015032280084d50b58103481a51190b074414032018401a10b41080c204201d520352a40303103001e0140100340c400c1c0784250300303503030758a13a0b65003000300d034690600c00c00301c2c02e036003004001c000c240c0c210724095150340e658902e0300b4007007582d400e0180ca0003449491030342c0b803403095030421303400300c07000e4940240102020b4034145850502 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 207728956 1250 207727706 207727721
    0xc100506040f06090e0c0f0306010501080645070f11030f07050307020a0e0405060106030b01050903060708090105163207030c111206070f030e0321100513 68
    0x30001d803104001ca192020368400c00003d007464400008171340e0340d141591440d2401d14400640219002404035005035400100e650444109107808a01030351084013281c007026102c14045009204220700200b80503405400c8148600fa010300e804841c41c0c0b82600310401002030790208042005a0140458035100d1810800300401a004591a0514500741c000041d40a10400e42c2d0311740011804408510742034003500300800703645007419a2814561905901c642061051800b490307a985c010310301c036034010000e0340d5410900a007520802d20f0403000182400381c08a070000503039480d1000040c0551444801460300f0340ca075541d5903030051a64030514011400c00d4104401d011010758608210700202c01c001d1900a2080d2754160031282d2924001b1801a0303d840031600c51000c0d0ba8400703500e52000107096074031484d5440c00041910340c65406030000c0402c41d2003450315000004420b1040d940c010980b003c0052410031521035540c451000741601603490007100d038020003c1e10051036819841e0011035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 207730206 1250 207728956 207728959
    0xe1c0905090112060c3b120102120c0903100207020f060301080d020d0f170c07080c030c010c0c0f060b0a050405160e0a0e0c030702010e0a031205090615060d0b03011406030f030c100506 81
    0x1501b00f4428800180a644281311140d042c1e9000100c00540c10092000d042c2c0114200340c0342d03401c041491000944416443c0c210084803540815480103540d81c3c1c403200300200f007020307003082c0d520758440030043d0701e40d0b4106142c00094410381c1503080300c183c80b8400303d039144c1c00c8540d03803070b2105c04a01305d0312000300c8809404198907041c00c6c00301c84045100d08001307003560020329000b103239607040c0c07100f003c0d0954000441a6052107160641070b004540c051040c1008690320860010f04000140002890152680c20294210f45844200b02410f072100c103090112440d82e40b1240d4250b815801005110a85405010941865003000c10401407440c0090760300105940001314802582015080c607242c5000c60940000b042c94451446207440340c4152038000e8040d0000d0035162602c0c4580302c001c02e00910025020700c1d000a101c0d0007568181d0300590800000500920414664141c5210751510960ba002e00c64081d044241c104030b000007007100d441c0308004c000741101000c11212080105001071449 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 207731456 1250 207730206 207730307
    0xe0a0e011503091e0308091612061b0e0a05040203090304060302250302061b1201271a040b0919090609050d020607030b0102010e1c0905090112060c 65
    0x2440010741513008250034003040741000c8510102400c000307000400c00341a00e04290040d81c03240c801d001420344540305860100341d125070360070390714a420001080101d41d030f2040034103418a40d5419980c09405040004000c07503400d980240c0701d0003000100d11013a034029031164410001049000c4c000d402808100d03d84c207264201c418102e43c030a440b003000040040700103802035410413000104281d44d59000000341000301c1d062018040c0101032019042c020007201800c00c04d00c069001400170303103015403003120010a21019120004070400d03610310342070b414421810001240018107007102d105104142c145003030f181c07440d085d0440c0030007000c69200690b00c0503115400c0001040e010000c40380840305540c0140303094a4188401400c89203140585811a414904030700d00036800025490440b0408a40d550899100c0c2d80c000e0302e1100e00c65002e5a000070701c01000107001076090b400340305054020385082c030504964900c11605200b9050607403003c9130f1040c00988035103000d1040141c2020080450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 207732706 1250 207731456 207731471
    0x1051903020f070803070f0e01021f020f041e050303090d0b04060902100507020316050607080309010b121e030f03040807051f0e0f03030606070314091003060302010e0a0e011503 78
    0x40c2d00c00da0300c070381002d0325068800428021060341c41745101040d401145807641d4101007480c0000d4546441d40030030807495884594012240c5440e50440d1600b4001a880b155103540d102c515040700d11a42410140d036a82c15800010581030102c1242c0780c491005200b941c00100c00d82e1121110b810280059590fa6641d622940040e111281c80c204d0503205501d9594803603100f441050315021010800000b4440c0120080005440351000d951000d5408100652240e86003c01d090043c0884049241d000d217161140740031615022071035031205d01e0b07150b051b0261142407400195882c03203100d41c0010380360402c20019020a01c80d002038070f0501e110b102542c60b038140e59010301c82c0955801e009082007a556002d038140c0c101c0c042085218070085c0902841c2949001ca0005849000e52003000e414030000208560700c0c8044801200c00d240002004541d039844c0c01070000300203107400d00040303020811218902a1a18000d60324100b01e9240700003241080e82001c0107260507203000d035012000e1584500c2d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 207733812 1106 207732706 207732727
    0xf060b04051e09162a0c0614030a0209040b0405010b030a060807150e0a0305121213020f0126090a0201080606031003061d0a0510060b090105190302 65
    0xc044020525025082e152404000001c2d440b0717401080c0c40710b0401c0186150038501c0c82c020083e181c02c0e281c903105c06541020082141002c0710744103100081030180f041d00202240e04c00a8000700305d5291150209069071400e810014a040011003040085202445900018080130780145644c03440c2440d81d03160022114540410840c504018010944591400c0700007943d01500720390b80d0111038540c103338a43c1c125004444502141c240491444c1245e07008090440f500280010f0311514a0001929032441403107d40511030581014071811035802c8940d5031081d0444400340000c10903610004000b600010850b0f4803070302050040c400d500010000810940794441c2c00000c076044002140c0d40340758000070703140546100c1c9071030742c404210380841c6207000c542c4219002d004213512402600280c0c010001d00500050052010403582e6141e200082905030450600615014500700b = true := by decide +kernel

theorem cover : BRFrame.Cov 207553956 207733812 := by
  have h0 := BRFrame.cov_init 207553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 207553956 ≤ n) (h2 : n < 207733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
