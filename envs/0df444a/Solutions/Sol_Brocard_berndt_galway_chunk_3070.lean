-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3070
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:34:24.123547+00:00
-- url     : https://prove2.me/submissions/6b2ad17a-aeec-4d6e-8396-713c174d7efb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 551978417 ≤ n < 552158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 551979667 1250 551978417 551978459
    0x4170a14031c0b10030e01060902030a0f0b1801031e06050f2215020c010b03013803100209010e031c0215010e0f06030708100906050109020a082d0108060a15 69
    0x10ba03962140030346d40a5100c42d0092001d00b00555881ca043c01e0300000500a25000651551401c83e03c2102800c0000c102c40c01c0c1c0602d61409107860742503403608001d80d690000c0c44820703203d5881e00400055500d001e003901416120304203101e40d00b400350b0495a1500d140100201c1c0b1500700c803480300030400a498516100c8000000140d890701040c84550160688602c51a055070030188007203044448650a40c00348507a0302d036611712544c1c035610b07500e45038008114810b46c1540712402441d20075249900070010b0400c141004e04514003e03401013800c0c04c1c40c601c1010444401c80c5002c0784103035014001748902c03001d26003102065604080904103510320180c044680d209002c4005001c0351020004113015080303550441c0c8042041c5107865001d0014461b0445405c1c1c145000001d00c1d501d01e009135032564403240c03201582030751400704144030740c15500043e54468141c4591440f040528442c9140a02003c0d0064045454084002c5081e1850100031440804540504000c00755035101c07082c0c94450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 551980917 1250 551979667 551979671
    0x108060714160317070e01200a020910060f0206090703060203070903021801030302070b07050a06090201050f0403050d0e01050a020604030e041e2004061d010c14060a0e06090304170a14031c0b1003 86
    0x248c080c012440e0507003a400094124841006000f40414050103810488031159201001082e8400c012600d4500a94606e03c41e0383c403019040c000a9000c1d0051a031141346450004040e90f92500011540c0f48140603c140c000403090060081c564188148006001c50740c800c5454012070380d554a03079035460030001401c1c3c00e503a824800c0842e03100d4011030b01c2100110104a44454690624684400e2652449004540018084e11b05035018505541c100040d58001e85072941d2292000e50b0b010f6040140c955000b50340d8140184c0d80700a402c01100421a40600080d034443c407501030001c004c3d5500e00b0602c51400c1840200103003a841172140d132404500020801320000f4100041c0c0b10b030200c0c0c80006000b64590380510343c42a000240480c41078400202c2442501c002030000da403a1041030300c21344c201d07800401c414000300280e41a84016030400700700300c0d07445051946800f140c4410740990f80d14242c00004280201440d8001c0c4140c004e0310b80f100c100001442c140004032241c0702c0d0500e02090503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 551982167 1250 551980917 551980967
    0xa1428022b230408041a2503051207020c030115050a090605060304120c0206120f070c08030a0b01091a040e091b0f0120100608060108060714160317070e01 68
    0x88114107803001000305a07170f20f03805410441510780c9260017143d001010070001401f0070001c1040c502d0b84005040c0c040d1032300b5180022850001c145000c00a00c0f500079403042e001c2c00c1c05683c600340b00e0043d540d511881c15110440c102020000c4954440c0d0144001a041040601007652400d0407281c101703502c4001c0454213901740c481071300c14410001d00a076100c10003180300c0514000c07041402d441040c0d80c894a901ca6134500b00141c0e518111b2101c040d00f0050103000140a07500030750b00522918405040c20284aa81c9046c1c0b40e400421000f030f0b84c1a8100082401c00006042800c3d058006400c40c018110a0b0501050004a10040c180d02031080f040c240d603030782680c0d00444d2852002a004400b03441e510101c403064660303e140058910000b1460a10001840b0102040d05070503207840d04041d10154507102000c841c0c22200441c030780c070140c0c02002068580010103000021880c4280c4840300f403030031004010a0200c6008080c41d0078864400e54800c4641c1e400741c401050200c004642403010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 551983417 1250 551982167 551982173
    0xa1e0510050408030402040b18070e060405060309010f05071b060209060c0a05010b12010e150702010e100506030c06040b0d050c1603170a1428022b2304 67
    0x42640005000019441c10081c40b09101d0340e01e004501c100d00907a8207001e10300d86e42c4180001c111a41d0480545032650358085880f040c420424143d00c42c100400301420542c0300e138006485079000b5100d01c2c2c400ea543d4904100c003101e1901130079603c00c02908080094017014107800c030707030081041710080040d5030015400da005d42c1c902e0107031041b86400500b29900910740c1d1429a000701041501d5902c20030200001007804c035014000d94102410764000ba01180c0b4907041941300f1820003402c188255502c40441c28980e070790802550304905801500440c490420005040c00d01d11008081c90003004200403c2c070a004480301203e10f000050203001649998070075034100a4010041c90b411004506075000040c15070100c0c0c4500900b460005441d069203c1d100c03060700b101c1c1107803400041030040100050328015160140c4154a42120f000d50600721800b072403008a0784120b02c1d9195401031100a5603002010964808103c0300d00002044102d082841c250080480a0904c8100c001000002810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 551984667 1250 551983417 551983423
    0x5070212040902180603270c060c390909010b090c0a08010f21060e01320622021905030108061311120f0d050a020c030a1e05 55
    0xd095400196101c039203410b00e1501030740c4481c41c102c0c50021443c0003810310f0320b4000100c074081ca1881d040d0030340c0258074007074520703440302c1d0110380c2c02c00d0f400b502610300302513140c40f40107040751a1044080e1001c002220032141c10406c001045118030b010b9a6202055010022101083c0c5841100c8000441e9030b8070030351602500000884940002c0840c05129440d0021030103402445840d0304e80c2031050b03807525075103503407100d140c0b0580d4000c41c420608051120350301c80c00a040b16001d2440802c0060802c0071441c00d41d581c01781510380d00d0a0b000c501d50001c0d000030000342010160070305410aa8204000010303103070300da03150140683e80141540400108030fa07078102c1c0c042c268000c000d4940e1146605014000707070824441c03400039000380c400090361a808495074408440d801004d0603533000201040c0901c2c035107204500d003102d11604070004040d480810140402d200302d642c0b0140e890903c00802400c0a210082d039500952213130b030016000601405039059030210b01178200880003000c2c100245 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 551985917 1250 551984667 551984683
    0x10240b071e1b0905060a0602010902031018080309030d0f09021f05040f0b0904150608040f0c03021c120318020d03052b0510050105181f0c050111030f0406050702 71
    0x203242c0a0b000050784042608214400c07981152003000441d92403009030300741d60080e10029859040340f400c105031410154000c090102c2000310348440c3c814241c2d50302c54103600640d030300d0503507500101e15034030084018014074101188009083c4414103250f404120500c20300301c0c2c804040280302090b040c25030b1084003a94018410710100d5044282d5900c407900e11a800318940074050760034038004612101403810381c0003c40e1081c1d5a42c802c20b42d91519540d010b1000072004896040c420903001002d070740d0719007054040e0501103002e0b40040046280805421940b002144207247c1003200101243c112225000340382a0191110a11200300340703022100c80c4140302d102e10b00c05540d2120805514003502602d180b800022504009603111403c0307908480c50b0074400d49000500401958030f041c01c00d42e041c00c00c0240c0c045e180c03203004a02d00740c1c01d4045030f041d4202a00081c0030030001806001c4240a0b540c1e01500c0e00c08110700e9410a6405400e4005000300054180303520340010540c104c0c420040c8074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 551987167 1250 551985917 551985953
    0x4021210091b12120c0f0b090322050f010c0204090204090f0311120d021b010606030e100624091d090c011103041710240b071e 56
    0x20502800c2d10341940719103030a00d110801c490349900042042c02011011800598210015081924008404889400c2c03005012a070600e480c410803000500e1b2014081c0c000c05446001e1a01d4a402c1c6242c8444176108140c21031540d02020010401a100c119500441c003000703103040410b040560010501074164803800039042498003d418050007044841840140e100782e444801d441c03038220009a4590302c207803403d81c44180030840d042e213a46055005101c039011041021200206100c541800c58059500ca440420b41314880111185024030020024a90b0000e0030817689003422a8904c03400e0540280c194070b001c2448841a0300c03030264071ba103c001c0c01d100340e2200c90401c61a915403203601c0269154840c51107084206c21442d0301800002c3ca090645000031401d103440c0c6001c0d29001940c00c14012064001d0380140103001c0c1840c01071001c0076025103644010178940d9410321215010940c000300b44448280960b00c0012840c105411400e0800d500301d500d500b03514144050100200641c0c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 551988417 1250 551987167 551987171
    0x1603030209060d1b02013b0105100603230a020906040f06020d1e0c02060a030b0301060f080d21020f0d0c030608010b010207030b0412140a050309060109020403080304021210 76
    0xe0100111240c000c0403114580b213503045094419150b090f82610454001980000c6d4071210402d0540b0b040c1841c034088030308091075003062442001c26542115025502c21010400c0d0701003c0c0001c40d0135004150a0361205c901550300c081210402c80c000200280c0170394441074001484040c1c0b03076a1007090b40d0203402c50210714030519030b13142e00103135841d0700700842c000c0407544034544128411a4401e05050648245c1c8039104464032aa007084070719031042d10404245035071038007082c400392400d104220107020007068a113000e03818040c204c1c2c605503e800a40e81003180502c2030407c503141884a0310008448000702503158041621001e50a003d11490340701080d14052101b00328a900d60005001c5501c16002040400e580303400483c0c82e41032600018113030264101c003080014000c610380e06400400b1b4600b45401e8034130100b00c0e45155200034060b5001440200074840380100502086005150011045141525555620400703020041029118000b89082020110750900c100e010746a900081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 551989667 1250 551988417 551988427
    0xb0c1203010e010e0c041d0403021e1f110f0d06050409061e0608030a080a18050601030b0c0913050a1104080703231e0304030203060a2a05160303020906 67
    0x450b1510300402d205000a06880c0000700d00ea4494480451b400d0f00c641c00c6200a00c1303550324004114080f4043c000b1821840350a58506100c00c000615030f00c01d06645000c0c11041018101c8100980007141c0000000ba20304030906420b00c1c2104120f54010449980b0345407106041d0f003242c0010301441c3e0020f50020704011441d000c00c0030942c0103284406103149201d68641c0c0001c00369080703d6242c00742110503030042002007040c82c05003d803154010004400442e48240c440001a900b1005c0e0320110780310761100c0010f004001154030744d40d80c01252981980d051081d260001041c2110358106110480e640d100458070000031071700501d81519100d0480c036903555585901300d40d076101c180300541e51490b010901244a162a00200360000c0c4114010640d80c40790b000e102c8000c443c001d5541140788001c22001005850038800309208034504c681c000703003440c04035240d5850300050100e031031460541e501c3e481c2d40c0103410200340e480c01c6444d90a034600f50095458103070002d1040400040d44110301040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 551990917 1250 551989667 551989679
    0x130305070c0f03030224070c020301020f04030609051903020705041a091602010c0212030417121e010803070309090f060b0c030403030f09080c01080a020d02030703050f01050111070b0c120301 84
    0x421011248254200d50b2994052008200c6070b02044480100c486c2c5014003062070715104110b0312950b180024001450300c46101c2d41c8800b00c0e44558400c48402d9104c1c04214107008080c8941c001d100e1078214400380d02d2885030340082d240c85040c0a0913120759900d0401c0c0080f0004400100001c5101400440b81424203511104084c81d40900390030040d230074201500760300303480891000b04200f020b00742d15003191180d940b171029140140a0110b003c08090011006d0304150717802e128001e5180c08030b0507100407424028241a080e0513049444240d10400074180005d5020030b034041102c00c10100005c601c245110301d503000c2e224952241d5410900030035004030100c7c012000700104d03407080d102c00950070728405003526110b9091247c0880c90700030044007052540910810741d4402103103540185800c0c0f59152100032600f0a40e000b000180d85c0d0000c011351b1900502011f409440c0909001e10447c90210000c1ea58001c517000740003804001080410302107a0420541c940311007c3e0b602c8684a40e1243c13 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 551992167 1250 551990917 551990939
    0x219051008091204060203040315110307090f1202060d0c02010b151b06100303050f0403021c0b0a4503120b0a0b07030e0f041a030f030a08130305070c 66
    0x394042c801c90007410080c1d4240c0701480203e4048501c1a0082d504261940d1500a1100002000000b040703031554030360a41c81c044d40c4002c2d0720581e03885e110010309030300b002e101203000c8400c1e800100700c0d04942c603130000140e0350f0103040d0b600c0e0030010100420b0608120324102e01501c101c080c0c041c0c00110600382c401400c0480c002500707110304554081c6180b41070001c0c09075600c280503603040700c0c03100000d44240040703440b440c000e004580e24408103a203429074030f80c08100038543c0300700e0310405002c0100c200000c1201510400c0c0d00094034820520200c410804c00000501b030440c9581d03900b04d060914000c003441100003a880343c1c41074540b603031500240da04010304201c040341d06001c0514a0901c101d041071030b01515000549030112816410725403955415a64a4251180d20f64800107030f44064409650b039001d0f0480140c2ca03ea10760a00d500c480d41030614240d416800829603420034040c0100e15580311103955800644c903e07000d605114241820341f46480703540310143c850807840201013a000b1080c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 551993417 1250 551992167 551992171
    0xf0a05060c010f14061011030f040b0d0e0a08030105120a02100203121303090b0a03021614011503020306070f0c051c080106020d0818100f0606031401120219051008 72
    0x28401e04c108148004040c0c2d5541086035180c1d800074100400203001c0d03200d2143c0e4503102008804680c640220100b10307030b08540080c1d10140b50300ca0000b81b804c07484840d90180e021801c104100400c01d00e8070f240d65000c0a400140201c81c06042d20b01d00c2a10841d4040002c040c032160003400e064211404100c1c002d490f070f8007034154403800d0003242004c64030301c0c94000380007034003950140e440c90807442c14417402c050960f02030000e0700c00b01602072006044240034580035802d403510820103950203040e40d2140a00752982002910765580c00c0710010400f42c0c4012a03520f606c00d100c2d19042014188503042a0b82c030068119000d80341c0e2040c0544030705c20800494503403070301d100991625035080c2c1c2e843c202240e4451040c07158100140400010444042400000410015151044d03851408100500c04112070701e0400c0b018816444640401410390503105d2401203c01070740c40700c00b00e07606040f1307548500415560000d026555600300034140e0100c6940d204050b1078010701d040380001c10300400400340303001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 551994667 1250 551993417 551993441
    0xa12030506271009420b0910050a0e04022a0a17130e070201020417060103110618010c152901090806040f0f020a06020d080606090a0501141b0318030106140f0a05060c01 74
    0x212008c0d00880c94003a0050302c0301d08006503a00b04191010741c080c04042d40040b035580d444d00d078081c1c603038003a14041d046018200a00140c0145810345442c00d10144100e1800f85500d003856080140125a00c06134125005485482c110485035407101a0128024811035108490903286803541c0001e1400100d000f9048a0040d1803d101d415441c1d8108480780c440c10400e000d500034101c000300e515500514150310382501401c5040038203030011400d01d064030000403400c01640c082038001070450202030108100a9030070302e040f2166508110000d543d031003010300040c2145140401c0342040044030300083c2480c650140a20303032516500c80300a036440d20607902090108113554002a0241441003c1e203800c41001810b00c25200d2800d0015070740d900c0415440301904404201d07080101c200d0b1503101075105034042c025640c0d0900c0e812400e641d4a4100c0c4c0742da04c6039040400401c402d80e41400c9d104800c50048443d2221074110000150b1440100d41c40a070b0003010225181c00b54944c194481205040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 551995917 1250 551994667 551994679
    0x40314030319090303090210050a020f0f2d1501031208040206030703020901050903010608070323030d0b010315080d110a12030506271009420b09 64
    0x290000989449020031600c1d960150400c020008846040780c00c6914910b000b410001107152058004c16540300d035808451012802c0002c00f48203141c0c7c1080400c0c0c0d07080e0b01c04c01a1002c2101001156100c4101c034902003e102c042d89102013500d0f01f55000b5400000d42102107515074840c07021000b195a00c01d01c801d903000c003022488021468000d110342442f641e4000c0089256541d1040258000c1d08420740b0181000002d001285868600344030b4180506404030003021a54070714540309000c00016050980398802c150292944000c0c00800c1d101d0300032a038a40424007140440040300107140d2450203207800b80340400001011000030414800c2d1060940e02c40000515113003074250f4030342410a00078405130010700d44031141446540300603044900140164001d00d06610180c41101b020140d0703010408154050042c2909229503690080958000a0101580c50b01c17000c0c54407079000800707113460303c4258030020704c2d410140d0700079010271125980550300e070351100b0200c20960003081c21a40600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 551997167 1250 551995917 551995943
    0x905010309050c0907030906050a0b0918070312050d02390a0f1703070f0e0d11150c070e0a200417120a021f0501051c05031605030403 59
    0x54031a0107148407403600400103005050514007400074958000388202c00705560b481c0c81c800082c0c15030250394091405080e0102c0e10100e400300b00049102c0240c01d60031980a28000f880301158089141c004403a00034150141d500745000c1d00b50703800e1154007001219544002048000b01b8414114111780440d20b1402110f210701410218038000d068001502d665401100844c00043c1e070302c440e030141148204c040c0d41d107804000c0045441d43d001036802c2004581d2000c0d8200c0c44542c40f00c0101040c05c4111040b0068039800d407158204101410b04481c0039840d038402d0401440c0c2c00c0c034101c82d8000c072010112100d03559103145510000005039403407005681031450b00d01000a200f01207038200c10103141d01c2d07032406282508105403041c030310400c160940254111060450400c0c40901380c0c2d10620380150a00c0c4209080006c100b840c0203020010b90381c540001403207151220325000710706400c81c03860341c0368114940c09c00364994041c4240c40194019484c01d14410008080f014000f141e03c1032000c40900c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 551998417 1250 551997167 551997169
    0x90703020c010c020c060403081305030f0a03020d0e090c03130206030a0b0a090504120f03090206040e0103110306010803250506010311130e0303040201052b020417010e0303070509150310060905 85
    0x1c004c80d540440c0d0004c2c00741f20a10115002e0300c000e001484950a9112240e907680c408241820074407241080c050700200310b81001d160b014404407690340038031301d48404886019030000700c15400192030031014480c0403000507240041d40d9041800075800a080300d0f260b1500680b40d102501040c001c140c0244403003400000c400050340103c5000b158407001200c130010252400321062403403800004100350b20340c0071180140c0c46002c02080a0180b14520500e99030540c28011445040202154001d90000e0010441c403940030056920407039103001800e001d5000ca1902215650754124060014000d02c0d000200304a081c4005652500098034807102d10307142003518508851150f41ca10b20305420800028005620480007082c000c40310101681001d416481c60a425058400a480680d90b0004046c8450220605d002a4406c1ea220091020500980c0c940c2c0c0c80c1e00010705008280100407405e0292503845500c02c4003141c18004055480c0d20f4620103032036200c1c54600c9000080342c0160804112 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 551999667 1250 551998417 551998423
    0x90c04140a0e150a0902030703061109010905030d090b09060c060a1413120e01030e10060515130308030c0c060405030d1407050a120e030c0f0705010c0b0a09020102010b090703020c010c02 82
    0x81203540306003c1e44d41524080281502c55030407a0300d4080c0000101c00640345120f00c0c0b1941c05003002c0c042d1250700d1070001400c50813080d08214441d62100042c00c0913540e00456510540d5000e164007501c41141d100490305602400a0060031801a14200203a001056115410760312510000d69000d03201c4500303403030791a0301004018016181580c030540b441030294030000d590745030614001440802640712141860160280e0f00c1707065448000c204194035004603220f81540c807840c9944d2030211909000c40c2d404c41e00f440300404545020001811241d00034091340c9680d0304400071380d0017615051810940701e500c130000c461142407500c2c21281c00d000d0a9021240b00344825180e8614007241032100741c900e5420801c00e05e10250712042c070411210018005004d0700e2620070020a0720707903110940f5a080c0a480d070032041c1000540c0ca11540400c5000040c942c001f8180c80c000980407003a400100d001d0a0804459030300311400708140303c116603166000340392582d4080001c000c40e84600f4401c0761 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 552000917 1250 551999667 551999683
    0x20d1107020a0905060d120807170106050909060d06150e0f060105070201030218031f0f0515011107080102070f020306130b0c0904090b070f09080303100905090c04140a0e 75
    0x2d04070310a080b091101c41d0701544a26000324004180390003090580d03403070300c0503c40300400a1002071608000d1090301c0350804244d50010803032624030f4000b581400001005070186845462007aa10b4501107841030301d0300740f02c00d001140c200c1c41c1031124140d140170011355001a0300c100c03418070000d900041d52030241c06089030300511050355414904002500110060b41040407609543d460390740c0154880c0d54100a2003400481d000d08541141d4040586c980486100c02c0f01000c140341844200300c2245030120043c8541002424610b120880c0785034403915000e07160b08402e10941c40050311205100c09a01c02031031080c0300310120780f8283e48925440b00c0c403000301100107099000030804204505034400203042e14400180c40060320083c25110740c0c48444065134190085080c40904190ba2540907200f0409004440c00071461418011307680c0407000d85500c40c008400381c5c1c0e0070106808503014000300441c004024000e200340e0080301e0202d0990703070f42541d1015031030b0714200c0948070b00741c008580d000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 552002167 1250 552000917 552000919
    0x8010c02060a0908160311120910140f040e1005060c0606040e0325030206010509010b040b0a050f1c0605180a050c120705040e07051615110c01020d110702 68
    0x45039103820031048040d20030f00e0001c403080d50f028802e00208550311581042141e0007503441d00f6140c880190f1250034241052036201400034108109010340c0c0b40d9201400400685280503001c0030303000c28142e0110b00407000010740034032000030700103800545690f00d00d001322614038240800f01c0d030311420400244212000c1c40d034175400400005030203140540c03000c54018803130416689445601003c1c0f0300a161590710258004484420f00301c103045d8100401805030200b580e00454035414040b0a01c0b09000321f00c81e69808410018082103064801c10130344030051180c0440b03a4448480103a021400c5181034001620249801c03030008840c03414140c1c0ba2201d90301c00c00b8004da148c8070708148001a040082c501d0b00303604000c105049031440364030708071071207850b041e680c2a490354102403210280c0b103c090302036403c0000600c000003504c0124002c08008a6020f2100b5498411510100d0068565101e800b211450049500700d12021f0640080c184102018000c010f0208070380c5903440a13000302d030006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 552003417 1250 552002167 552002173
    0x1206060206180f030703051201080705011b030302130b211501030f09020a1805070e010e0d030c021504030311073b0112030f020d360608060a08010c02 66
    0x728081190b180060804221800c0981d03800e0441c90903900d00c0c5a02580d41240060b80004030035a040945217000c42c00362408601801280d840c0800080c5141010400c1c907803825110042c002c1018002c3d8129074008080181c04802e46903201f2403a8025045040d00240200341c072800485000f445280d56407007030a00100b0081e1003240d08004500a10302c541801035500d503142001000750b951502d02100078001c664000e0035450003811800183c60000c0c3c002410b00062a0412610342c2c1c0007080030b150414103903480702c0000c401d0306040311000054400a50020480400581d01100d0400244152402521509402c0410404490780c6904510400480c580d104d02800030140c8641d120001e80c03070b8511400c05510300d4000c92421141400c0e849001d1030646c09a800c000c140c6c01c419940c0c00c840382c6002a0800200c03201c0080d014588030784410525210030203200006056115a4130b81141814846501e801e03241c1201502c420b80503a12079119030500000010400014011111039040d242c0c0a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 552004667 1250 552003417 552003421
    0x210f0f090b0c070c0b0d05010f080703050709020c031306200613020121050702070510030b0f04050705040806040b0105011b051b01030f0c020d09090605090c070f020604090c1206060206 81
    0x1041d0043c1c100600c1141d082c43c8080b400a2210040c2010b00b0000000c1c43e8005000e5160107921046070f01c9641c040c907110b4200c03090403c080f600c0810500101ea41d02d0f4405a9280102d20b0260708602c0f07209426105111034110200e40360340d2203184546407c03580d40c80c0d00e07507804421800e03503950780c03049800d66800320058201d000154071603000107003400e0350341d880820040011141081a03e00072101040140d0060004014501d4050111841e40e0058142082110146404590441c03400107205020b0368981010521441c81041118001c0c0046000c3c2c6040342864900140d58403001c1c42207600041c080c03504801801c010290f05042c2940c440001c0c42d080f05840f41d0b484e2680c03180c1c4d2040381415620f01a10403400e2179402445440103413a170241004403070398034018041009640141c1886850070f60180050707150200016000803000c00d8030f9444007110315020a550395070710402504060041000501030031541c01c5079600c40b1583e15030464002d640c2e000c11080f6040d91142c01c00680c841c05c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 552005917 1250 552004667 552004681
    0x4032007050319020d02030a0506100603020315280e010e010608091e0c120114222d0503180402030705030708041b06020c09060616080a210f0f090b 65
    0x18000f010500c06000c40c0b44446031900081d00b403c03100c0c002681c1607000001081015803040142a001d07002e1801d00318114200482c1741403010702049134807030184260642d40185a5040406042181c2169140c0d00401e074581c80c0001d0249420301c41c1c41d40d09030728200086040f5028582607441400d0000040031144008840d00c1100111103c550200340140032034806c081d02d6402060001c2e611440c001304201c41d4004030b0a844600081020b441140390003250f0b030103044850b2206a209403c03044040382c945907020b40081d880c14000c4402c440580740040e4000b0408040050540240b8000e81c2400e0095068140810ba2108a803820000b990400005841d280030380360f85608036019507800340301c0d10f00d040300b06103c4101c81e4201c1c10240e4060360700e001052400d0103c080d80404140d6015052041c12103d00c00e4081c2c8695004010002c00b2500c0d48c1004e2144000c0851050310b910301810034500007115500414540300641225030509030b40356003000c0240219030b01603a2046400c0081da03100c013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 552007167 1250 552005917 552005953
    0xc180515070c08010c0c02031c0504091505040603030e010212041a2a03030a0e0a080307030c051c02030f1e040204050603010e010e16061103090603060a050306040320070503 76
    0x2803048940d00d10703203400443c00950900c00c1c0c0e0b0841000d51550110381d8458010149440c5503c0040c400400040c5019420300741e006041e1405c0b600c451070041140300c06640c4c3e4401c03021480e009036400c40d22700070000061503071207410700100f18130a070240d40c000102c1d480b2150052190b0301035060341d041c840c0b020300c2c40f000200000302a503110904c0010080314400c446600c3c406d941680600f2240e00220500c05504001c0c428500310140c4c0314000c0c4108566540e0300c900d1800300600c203905041c1e6642241d007140b0f02030411504070b01150010900d001c404c44110400940080d2619020302c0d035000005a08179070400c080100b8000e1581d580b40301d82e6100d908000141c40014200d507015520f810a00004910074000c00c0c409980440160120349008054042e20044d283c0c0180b04018410101040d4040003104840440005480155917651804041140311016522440d0140b04020401050541c0851180d6903c0c80d8142e8042008810600250703840d00b03940100e40d4150064030044130492002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 552008417 1250 552007167 552007177
    0xc0301120206070227090c060c150405011404080301060305010501030903020a060b1507050705100201090c0e360115050a14040f0c05041502060708150d080d0c180515 73
    0x24600d200d10301040b000010582003005d50540300f226684144000c40c0d205006c1007141c1c1d20b0545002e420720030710403003565481c6140325a803154808590081402e0107029000211402c0040c211140e090600d03140a075a0750b03200744280d0b4002442c1100100381076101c4d000c3c100c0660707010340c001c00000341151030310802041c044007030740d030f005810400c2c51112004000c060081640a04060b1040d18074200c180490703603910382180c01c00c692503c00f500d4000382d0b0039542181600c4a2003465101035480468540410744490382d02c1a44014940c83c0031403010405601ca0b071600e1402d0001e01c500e20b122181d0329060304440c09007a5004c0e58180b41417250000600c508140c840000700081800c07040c540301002240c0700300740010700082c00007070148160304541c80031034080381030b620082a50b4a070003500240340070f1010b8490540340041009410443d600c100c8088141c035003080100d51307210401c0700750a0050240c2e00303d08020450b448000340e008401020803104655000e0072009440120b56a14440c81c1d103d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 552009667 1250 552008417 552008419
    0x80c0a090f14090c010e06210414031206100c02090c091302040303050705070f0f03080705100606020c10050316051b01090605040b060409020a0312020f240c03011202060702 76
    0x42e809444a0008101c0c510600402d91400940001d8451500040170020010755040c011101000b0664540111402c82c0c0b0000082d80c0360071180c2d8586160043d810703038144071211aa44000f0a0803002148039600540c090307041110014082c814a040c2074842c880c0414011794095603410002d5a4214100002c043d078072001060f903105030050402000c01c03a000b0341c105500103140810785100f0003d040040c08085c20411148040072441c03e00610180d098901009203000700124800003045010045001541d00396101071000e251034010082d9210150039103213201e8401003004031002401901203a0044025941241104a1020b403d85031a40300d407010601c1003100c0040c0142c045000c1c03080c0c58a5611421000c189810141007803084428050302c61442245003214900041e52590041804c580c0c0c406141c28800b00d00090507400c00a00080e000141c1c0582410206c41c0602c4030115802c00d03409201080d405d4680401220881c0024021014044242803100c8003518140e8041c201e13440c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 552010917 1250 552009667 552009671
    0x80f1c03061706100f032d021e010e120304090c090302092e0506070321110304230a0f0f140d02010b0907020d0e0312070813080c0a090f 60
    0x9525400c260b6841030007010014181c0080041c4441d00e07031505103800003000701c400c20f580030606640315801c0301c9000049003a41c410700c01808001000011307400f0091030790000d107043c5c5180721001594941910039001c4d14000707a1803662001c60b42c600300c10018060b0340800011410070b8284054007006242c2c6054400902c03146210000050352044c0c81184110181d61402c2d0742c0a0100b02c02e0314030004225280406201004003c1c8520b407103440655503a13503054034103402c540140760759510054a01303450500b18030b400c0c4500040841c004030300850255120700f8903200014a40150822103015030802108607400031040000030403681c00ca4140340501030710f8030208200b20f5590b00d035001d00400420003200d03044481001416a020311494041c03207405d0700c0407192858103000c029100c20081f0307980810300071090802c00d100e8600700a04c81e00060540e0f60140e98041ca81405d0141ea004070070907101110903524003040c514408950b400c514207015181c4019a030501c55904041c18a0701e241c449003503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 552012167 1250 552010917 552010919
    0x10f1104180902030a030f02060106050313061805240c0c061b2119060305120a17010603141302060304120210060e0a1103011212110d0513080f1c0306 66
    0x181d024025140e17554070036117501d144500f807400042c0c10114143d102c0c0c000d000003401005254028414160406ca5000300001038107040030221a070300c60b0b03c080b0047c1c01441003500c041c9000d5260345200c0d506c00c03040ca40e001c00e25680c01241e4100e510503613032800340540014000c5600424600741441c96100801501418171924049200031b00d103061001c150030f840c0c03100901662144084003c5604001048103004490441d00d85507078508600d10306464500e0b0018000003190300c134818011032030702036410b0082d6559540ca4000c003c1c00b115041610b0220180c00410413004c0700102c3c451001d81d015200174210b5886484024040c01d00c501c2440030760080000d100d50000c4a0301c224405083e90142d00012030802c85905012124407043c02d81d401c10082005200110f484006035104550104120b0161704d0455004c4854080003486040c05214600d0076401254000e0003a00703000c2c0c20700c2d20030554030742c0e00c92209664400401c4c50a40c160060a0319420996581004803003907030f05410046030007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 552013417 1250 552012167 552012169
    0x30b0109171006090e0c1905060403060b150a1b0303060302310213030b06060c060f011806030f0f0c0f06020f010e0a0302060c22080f010f1104180902 66
    0x1910041101d1805504141001c04100341a4441d51000d040c0034031003008458250003c4641d41d5020707400b15441a810340d0b000c1400d4481545007400a803030040c0845032207507564a01507000d041d4140025110744550003040303540906c2081500c44c20641070b5158026801c1e12031024070080800d030300c00c0d8100740d12801d0200260b15014180600c0010213009680000395904c040703d5100e40c494180c90b061760040011110442064000d28180c0b07400c002d030f4101684031030000030800c1c03040350180a0a80110010800742c0ba0441070214100e509100d426070b40802e003c00514101d4816000081c00354150f00d540c50081144070044031003e500c540301e66081c00303403540081340b45035100d580100c006901c0f4040c02c0c0f1880310300380110182031001c80001c114030880341e58081e440303080c02880b11606910102d006618248a800040152101c0c01a04403e090b154081c0c035481e0b21700760465450a43c00c000c2c0c113010a0a0070b00c0751a01101c1a0400701d4102800c000c50601c0804d0280d4240042d140c55950700b0f405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 552014667 1250 552013417 552013439
    0x10203091206071d101d0a1e0905010303171e01140a09020903061807050a03120f1d01030c170f011d090a0f031e03020c12040302030d030b0109 63
    0x1400c07a05006190030b1900340d400030012850400490301032460007061070a0754580b50a4820304420301e080080031111880c045554003a4180e000e01c0e4080c80192000804403100341008ca2040c0c1c006140b4001c503074aa0202d80191442807100900103141e0103103021003421044032281c1c06c1100c420b14001006001e500c0d2442140b403e8204108400d00d58611480c41e107800500d100052110300d40035801c080d0a00c001035103075400100810021f144840c2101c0140300c090202001400b00240550780090300c0f82401200001051850000f05180d04950003000c2e01a2640f51800840c80ca1501c0d0b800c0400d20044000c0c01030342c020001808480c040c0340d920f60150b120071a03c030307130401129002c10790700d0110326426001e180c07086100c2c2004103000340a01c3c4c800114030540a250841103080d111906460708441c1c4184451201e004449000c0d000b05015034180c00626000c1e40e25401c80b00f0b4800d80550005003840b89102c0290f00d036102080e624070143c082d13040b20f25044030504013001d4482e590420080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 552015917 1250 552014667 552014689
    0x3070605010b0a02072c07050d020403061d19030509060d0f20030f040f08160605060a05040b06031602070e0108010b090a0513020f04060503010c0207050319050601060e01020309 78
    0x14a400012544860780c0c0d5040160b8070062186c40c0712140740744141c02130140000d901c0f0425001c4042c1000c00111642e00a00407260783c01c080e118115911507617820110010004410180810020036040f05922040003034a1005418180c00000d58031505550580d40c583c0080d00580d0005403c1c00707130380d11400b00c81c41514a942d021100114010800e0a8480c050f510120030050300f100c010300501c800c01d00c10545480e4803507480f60400000c07040b6410000054001d4410007155140f80f21301841c1000000c1d0812401108140c0d8084110760303c500800c019116030750701064112405200045103604050300060580d10580161420701352a64560003d050098008500c1a03440300000206414035620306640441c0c40b1408001600b048021090846d4001102034440c61030b04c0340c10f491a581e0b940c40003000300300090080214100038240070f51250030030b1040501c240500c81781441c4030448031444800c0c01d81e000001c5c013520703070904d07400344c950744820100e40741140320900c151111034481d18070440b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 552017167 1250 552015917 552015929
    0x603201912060f0e0a11040e06060d0c200c030a06180f24050105010c060c1107060c051e1c090330021b011119080307020d110a060b030307060501 64
    0x81035418050304c64407540f000f810b800c10702c078038068083d45610000740903901a21201a2541c20701d88969001031880c0c010003460a890501e01104484000e0700b00184483c50090807000b001e070301a42c0545141c9070701d440b2038243d406401004216000401c190711494035049000346140416403191030303a2002e200c466408464403404547c0f4550b04e0b1a081c620203111040c1010103110075814171000a0900c003143e14001c01950f00c3da540352482500407483c0015060880041f24401503940400600301100c11030155003500031a0085012010840504000d9040e40c400600d1100d802480c2c042d4490030361640e050400c8084000440054810200e004c40710100031020b502c56880c00b940340d44a19800c100e04429507002d100780c2c0d4078461429684160107002420684000051051070b1428000c507041e411707031040005000c1e8420011614055805510254212210340060742c005540030b20000d0040380c03155200b4810b00303000402030307042241c0048c03010b4262424400c0513504e02c01580d90a030880 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 552018417 1250 552017167 552017189
    0x60a030f0e25050d020f010c053f040608190c0203180102060403020a0b180102031906050d08040e0705220e060109121104020c10020301060320191206 66
    0x3054000030b050004032501e8440d41c400328096458100024105440c82500070300400501e00c0c00300345a8014104900d10641000030313a5004084500c1c480d0540090b00c0a442107a1b004045108495a14000303090500c90440000c5260504000381641c555038014003016146040c030300d8220204116010b0b5059008481c1c00a40c1c0b601c4205403440300d00e43e1103498490440d0310140c100400700380e00141e8002101e03044410715443d070722000c0002c20103001e0364081ca2500d6000005000c0d00011888813014500c000080401850391500d08000c1030031f40441010b040d140c4240000d0250f00640c9021582119060401c0da10740b0300751070600d03071108440c0c540c45091701144280070025442e10302032141d803140c02440e0404090303003040040740c1101d14120025080b07222030f141d1852320752915130403a885007040c03c04460140712440c0b1018040c4d4400d006900000b800d10789094170031008024140b0800d8148410b6905104540c1540004815039880c1941005522480b0703458419030b034032800d00075044903411707 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 552019667 1250 552018417 552018433
    0xc092d0c140a080402040c030b0d03090810060e1f05040609050a06080d0f0c050708061303020f030901050d050a0f020f040e0c0c03070314120115020c0109050906060a030f0e 76
    0x380c00703a034068040110903401080801d40c1d040c0d00c400f81d00d0780a43d04075400036011031a00001c50040100700b41c00381c1c00c07990394055442071580100f00101142c4100c8111401c40100703007051026681c00b4810301030081c01210109002207003010340e00e4103c060880e110102603075030b040041d00b960700a40c040f090507555007051003440052406800701400306a80207250104489100400c3c0c121400800400c200c0c2c8000d0000030080c0501494004104a00444401d824140102c169410013407108401600c1101c551600403200401030b501e000c01d05031100303402c00e90f03004098000380200030000a80c0035550195104242d40c01e2010b00240c4034509015500e50b420210407050a8401821050585070107020200610000104403031500341d051415010703c2900c1410304032507005d40c034403681d20044803000110706110244070030301d0b203021142e00700c0c0d1000c05101d00658003503d20f804bc81d42c2040b101c400080311420148000c0080e06100c0c50f0004841f400d903104501100e118001811351a041740a07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 552020917 1250 552019667 552019691
    0x1905130c0c23102306060f0c07030203152e180f2a02070f050f063c0310060f0212160b0f15130e06040c0812070c092d 52
    0x51070700e8103900030154803c0c19085c00000110180900c030130b03145e404e240014402c01050800e00502006503030140850780d002041e1018280c03000c0341141d00c0035070702010301d4100300304c6c0c0700050032506a028001c11a00707041f800c0105c8040300341170310154501c0329522010a00c04590302482400c0000b44048805200c1070074400c0c0180d43c684e00528102e0441d48174a0060100b007a03160210402c03540211401840111401d002c20071a01500c1160a41041c066051641c91100d881c1c2111074801010903165101c1c0c60030700c0584c060f00082c0c0c1c1482c01429400c00600406000d2034a200050b0442d0048a81816a000000f001503014440100c40ca201c210b040310200403c9040194001d010804000050b2030900d4141c0c0461082c5021248519014003e014400d030f95035101c020758140090a6892070b152508014030001194802d16503103100b070310420680c44040406032030000d036001028013140c0e4179014000000d00f21040381091205800071a00c40043c1a1034201c0c0c00d02800302c180483d1b0181140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 552022167 1250 552020917 552020951
    0x70357120909060b030121080318100207050d200a060f0c0203070807031b0b040f0b06011805091b0c070f0501020106051c030e1905130c0c2310 63
    0x2d80070685003400c0800c24032041c5240c00c00e807030558000d9500c031960032007222180c1c8451280e000e0043c0045000006005502c990310b620003080340c0ca00c904948030701100000718001c034842c0d4040a845604a0b009440c1c1c031501c81d000940407250100d2418282d05592207203a4203001e100801203560640d41d582111401c1c0d020300840c00210003a00140d402d010303154032800101c0c4280315004040100d0012125070301443c5038022082150400e030480341620f49860324640702d0650400580d280e00d4102e000400b250703c200212000c113044050068005c5192500740106030901421880014000710350354103091500b8000b03488941e007070b00000c2c02d800d886c040080d8400400b41c0c01c0b9504690410038240f20603203410400195208182c40e08000d444d0715418211910a94001c0843c0d0000b54070315000c010180d00e01c017020548508481402e060f2400e914030b072080b150340441220201d003074400014042140309450049062510300c0680900680b0100c103814482c10064103803045075a002c011000c0c2d1904 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 552023417 1250 552022167 552022169
    0xc0109050105011401230a1815050a0e090601120b040f0207080901110a0210050901200606010f03060f0614130305061501030c0819020715020703571209 67
    0x804c6c3c2008050814554204113229101400051000c5007000c020700e001c420000c90010300481c508a01154481a401481580062821000521340086160701c500d030212642d40210416140d5180c101e80c0415507001802c0c500008690150350341012a07110200e500003008214462446c45590b01c0390f00340050000d1040c2c400d5980507034800011a001a16800e000d84241503030b60510325111100c0400403210041e00d02e040b03004080300c43c1680e0f41d4119000a803540101402d81b10181c81c002070f03200071012645d1921a0003020300d02480d04103c440e016000403074002c114100507a10305000e180b500c500b10051544122000c2c1d004201f040340d003a001800160400d4070910301440002c4042030020100d84000c1d100001d203080103004804014155412515030b180d02c035014140103420008200000c0d041688203a002c01d8668080d1070b03403000e000c4c40c42e8145ca90310108010b04a00302c2e452400b034083d900c007224080b0516080350440c03591601d02450000c5072080c2d41c1503d2001c40248000d0941c026 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 552024667 1250 552023417 552023447
    0x2101061712070305030609040c080f0714030a05030d090201020111030108030c070b0f03061009150206060a1e0e040804030803090a02030c1c1103120a091d06010c0204020c0109050105011401 83
    0x1c14041c04000070361120480e604140119142c0303595842c0c5040400702101180c3c4555050700c1088008001e031040803030400115031524407a04d4890400106064807114500300040031364100f045141030345101507000300b0b107071030061000040450160384d2090141c1d0081c0c0044641e42e03c0401d000f24000c07010401c9801500c640001325041803003200b50880c103408060901d92103074002d04118500940b10b8a44030780100740360010300818841c00d01019480f0780301550001d00410f480003010640101d51000a1088402030140c0ca482d50b21b0980413541030100500119121542004000049080c00f0042c40c00380351440e0192882e00402c1c41014506800d0315003450182c2144103068605902001440c000c050b0881d540c09060004a00001c0c203040c181c440c46001c44101140c1d40e00c5e40d541c420302c500c0590714220001800303c40449501d0380d15000c200c460700d00040803a0003950040c105034024201807180b007800404c81050556a007400e4800903044070010041c030700141c0d8007540e44508410710350700e1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 552025917 1250 552024667 552024703
    0x41506060c030e090702010f020f04060e030a1a090309060a0503060301050a050405030a0e0102010e0d03060e01080105251701090203060a0b04030c03080901050c4821010617 76
    0xc1e503079801820101400305607030311481d5000c0004182900070b4001080441100074110740c1c80350107021000c95900240620342c00218680e801c00c07514100081d405200b2070300010840300d500c41a880101c11010014042c0d40d240c0018424594031f902c9543c09011101119166a91a0300c1c0100505007111402090603801ca81402e01744408035002008941142c0e001e0300d840844242c003103005034050182c82d4243c552a22a1500703404017180d150384000103484406035000110b07640e8084880c01e841095814080b804424140440d8041c95074220300c02c60099400c10110080d020783d41c000c80310790240e202c408000e8000007088084d01c2c00c100004081c1000041013403c0505503210741c4084d81030f6000c02000030b00c0c000303420344060b0f0040b01990345c0e481c0500100c83c554495610031803840313641803003070214500020300c40004080c1c400204080200c1400c4507010740c0781d585402c01010b484140c0c01c800d420300b11202c032401c1000081c0030303049c05003003010243d40c02d50140c8100d081c9050842510588210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 552027167 1250 552025917 552025937
    0x140f0f010c0305090105190e01200d0b1203191e08100605070b0609060402090a08010b030616211b031509050c300f0402120c01020c010c051504150606 66
    0x6140f5803501d0411f0300c1c0000c0d82100c803d4218010901100600034901c14000b201c24000f4182005002030304c00000140301201d1440240160310320700f440d2281d0660002e1090b201e5113804078640040510503850300c0285100c50550101292800c0d03a80074002801c01d41c01c01c50070048000100d001098540341181c94020652036440903554094602440342c01404c0205000e0307940c60f019552030070801000081440d41c1c602c00c0f94000c040a0b00d035540640a4034000689003c0380c0748038400c600055841e00114480010a40390301d40700322031909a45143e849034418581c0c0c1220404404040ca00d0320002040c060380303200e203000c80c2c50541c0040321040c20705d0b0400488000c5501914007134240b801c804081c0100c03c950906e1b041102c4810011030490800030131414290f0b8440d0036008900035546038000801b002406620f440904092501591012540101651065072007156180c0242e0030340e1102c4428244806810000b500d0503286640c2d84016040384541c2c9201c2c0e08010442810902405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 552028417 1250 552027167 552027181
    0x3007050c0c060c1509070906170d05090d0303020a0309062318030f07210503150306090303130203071a19050c100c110a03091a0313140f0f010c0305090105 68
    0x1e21040c4404c00008840e00041060044c0420104c0c000d440400c0b02030100545840c102d00d5599018050040c03203100e80580c48031400c7c0200122140181c02030400003c1d004942c8050b0081c0d807040d1004400c240d921610000800c01901c1071404803c0c1c2480000244401c0300c1005401c000003400b17050074918144101c8900a80000480380d45000c1d1341c4000d501c0d400581001e9580c0800501d000c1e03250001c00380da032116154000019031044481050700f001114045040c5541c412040b503801c0030540c020008a07110300315402c1d55224052000b0201c4070011340701c00025064901404000d100e030940824030400205062400001700380180c9856410070304014a21950740000b0644403d0950360b5040e0349809078400d003a00080d00708000308888140d0750782e240051070046540f107500140101840354402021015084a0050b16020181803a07442145c131181484c4541c190354a40c1807143c02640074843d00148102044d401000c00006003440c11241d01405482c40202150103c1c3d01d084c00b0003546c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 552029667 1250 552028417 552028423
    0x504032304051002030313022808011b0302090a05040f0207150203090c030d08040f020411030f01050f0103090b060f0420031603050618090106080712050d020307083007050c0c060c 79
    0x248580456840400f010009040d903070580c9001d4090b000270000c55004903224205400a103001105418403420a15507840304070700b24090700d1241c5500c41c0542d941000030345030680040d49030f08002c6500500d410b09659440481c070400c0503002c54107030b40120030880800c605001028240b401500904842c102d404001442114001c00c01001c2c07205240c11750f419910b90380c0c00940764075411684540d4a0600c2030f51301c3c0000b0300900c00c0502c00c2a110003000c209501c64080c115070150300491202581d2112000c212030020007039196034115560304113801e2401c2e2200030076003404135420030503596170410103000000310b11001003207010306040005101041c1c949001c0702c00900f1101021b2103158030707407155541c050040b40e4050405407081d03440103c0c3c10200360524810040c410401c8400d526420700060361203028904003d05006000d0100351005001c3d80d248580c1100050803414403403403404810f40c811401640c00000240380415684015442040119820038040710307140c1c140802d004140c4d0b5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 552030917 1250 552029667 552029701
    0xb01170307060c0e1c02030601090c090501050f0705010615030605030a020109060c1115091801050114180901030305090909070b09010302131a070312020304030207060305040323040510020303 84
    0x5036840446010461180301c1d05104c03090000c00c1c10f4289107484013044160942c040042e07210f809a42c000044200c2c80c1d10500880e0421034490301c040e60b1600d0010360b01c6400108074051440300401502c00022000c1c880c207009040a0b0300c210203d4402d9000041c2101d4450700583e009070f100f044c20310b001d0303a04411080c0c1200c009107400d4507066041e1401417070304002c583c0e001c4c2c4c010a00a0a880e44000d00c280940512013060f5184501c822240c1500015054280702d0381e400714440f00f403c01c030411800707002001c1608801003a200c10080c0b200219400340c200344e00550024901241c0c07002986020400b642c3c1110454004050a43c105004140c2a100c0e89039651b05265001450403241500800240004c102d003114500388011054484c0c02594450002240020342c80440d202c0000c1340c030700c00d481c012500b40e4000e0980f42c0c20103005070700800c0050700980500040c5900082e031049584001d038100c4c0342c01c50005480e589000144001c0b02504410081550410300400c407580310600a550 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 552032167 1250 552030917 552030923
    0x2040e061c0609050706140301290c07060504170604050c0603090703060f1a0d0b0703021b06070c0311190b070c0b07031a0a240504090609090b01170307 67
    0x20304080701c0c0a894926800354a1001058141048020014844045890310455400e5150070f001c3c1d4103c1100c0c950148000d009511511840d8203940091410515450954441d8010068a041d00c0d658005107031803503580c80302e400154001001c0c04038441201c2140300c41c8100740010102410113949807910f13904040c104500504011001407200b44042102c500119041001008541400c075070b40c0c0060500403d8201c508500c0380b44008980c05c04000003c0300540048140b075060316500c3c021006584200700b0030000e4210041000400c0f00240031721805201d80f6245e1070300c4030250b4900078003c541e0a1a01422a03040b02c4922040114043d0140c03030943c5d404a01c2c6491a82d4141c0700f594480035104010f4580c1c441201081100b03501580104c0c00d229185103941d104002078020805a41540c0c041e40e211440c0014001f100005001160350b612492424614200f68031a00703502d00320b0310700e58407000d08a5115503a035030610100c4010240036280c1d015007004c4050703000f02c100c0c1d62445440402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 552033417 1250 552032167 552032179
    0x903090d030e040608061e0405121804060806061002010c022107050706091e03080a2f10050c030601090b130308030a0c0219050c19030c2702040e06 65
    0x10107105480c180b11036600240100101510790704100c0e82d0f900102d45800d840903850950a03d0a001c80720780d5031141c0d602c02d000b030503001440d5000c400c660b006001d03010020360001d07860151301d60b1030703001d603801134080d000040019251020400c142c460307007058400d0969240c101c1e00a0101e03800700ba0070901104900d000c0d0f86442000300303c090244582c00c070180c40d5024109001c6400c03a4000c4240084506010146a10703442800201a4145003440000d1450b042000a891441d00407440a815400a0312404011010040303004044400c1400c0c43d2015030011090070b402440c143c4281900800030789081411442d014001904008071400340d4141c04801040c542c0302281072262078030196a01107410754a90030981101809005050b40c0c01c0050300583d420741c00e007200003c0d15840720f41d8006001f000c0030000c200c1481441c0380764000c04966038900780404004940240c010000500303a0341d00d800340c80d900003007010f03202500300072450700b41d540100020400d0442d4152a1034101e5411070310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 552034667 1250 552033417 552033439
    0xc08061e0109090e0f0d0e09130f240f050606070201140c0118030801140d02060c03090301020c0a030207050105041203210c09061206050d06050406180b190203090309 73
    0x60b5124100c41e4020041a8144184010f410700040ba4908200050000311b40d64400219001d59000a08015080d0452851400038800c140c0040c96400d00b103014030303404409188a521607903848a84600940c030300400300415900046401d215411404a140b01d00304468140b400000c0c105201d82100a41001207019291242600e5842142c920f071200340000c0203140709012081004e12041807007517001c982102c0c0000f0385405000303001c030000c8400800c2281c0600050b400c200c0c4942002c489840360348810302019800d5282480109207034209400103207140c0c00346213402442c2a800b60040350420209120420103015122900c8000982c18108051041038100c0e2440004503908a0110740c107060040030215990400070a80550700d143d56840c0751010341481190587c0d100b80700e040d0b00442040820340214a455224941103840f40c0700210301f255085200304004040d03940c1c161903003131030309007800500d13480d007405400c010302416000d50445c502030f169903841c1e015400d0810300405913030030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 552035917 1250 552034667 552034669
    0x82502060c070317070c0219050d060f06050406030c0504111c0207060b0612040501060504050105061b070314062d04020f030c0603070306090e0a0c1a0c060f04060c08061e 75
    0x36540d0a1a100c4042440d5510700005c0080c4800b00c0a0000c0c1c2c010141261b010f8070b000584611401aa41d0240151a2094140c0d69080007011560076401841d0340c0c4150200301d43c2e0300c0d402031400650107a20990304442c01d1504004c2250302c6030032894420709040200f40303001c0384250001c1e080361026460050f00c0303890900f03081e4054400b00191903848140051910b03000440c2001031801303140100001c100e000e86a0b4203000440b902070180c144c0c400c105003c0040b01c680c40039030803120040100182c0300444d94a40d2000d14001114004821a411100401505c1c40c0b61b0042c84110784d481c81007800a41c4800b41c0308002d14003014101900030300030a40e040c3d0460302c0401161544603c0604000e07030b01d00e008400140140264001c55240e1420070300c1e100a000c20001317411544640002c4070010b80381c984940700c8516101c0503902c1c8c01064050091902c0030805001c0075118400000b2085d10038034051920038101c0c1d403089982c000340b0030b4003000e000c00382d111803c8a010203200d45100c00383d00c40b8604 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 552037167 1250 552035917 552035927
    0x601140607050a0206070b0f1e011707080d02070302120105131e023f03030a0e0f0a080a091e05061c02040f290901030b0406090507082502060c0703 65
    0x2403c00b9420400c0055403504011191056500c1800d8003003240280b621242030b900c850070f284425480314200128018000350f02d00840b101c1811403540c1c01c88007510b039210461030410101a4115004d038020740e808005600300241d00d005a0300440000b00024549000c03034a40c0c510015a0182c900003450b29201204182c064011070b00342c1d00180011401984c5011050130600c0c2580d400c8a8000250034810f48090460390110706070f00c044015500f0355903044280740007440742c0540700f1b042d40700f18402c0034400d0209202051555001d140c80903a1540b00c2d400181c9002c0131980300c50307588920121200301c21000241184103640046a0a942e034845403240900150380d510b2520300da6605c002000a0400d1200754440700b11500d601d000d00400c02240c619608240d26a01816443c41c0c0403c03000b015588290302030088680010030014480b5203800c003601c1250011a004004101c2039014800407504010252401c00301181d4401040e031074409000703403030f2140640101d2800d5004281841014011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 552038417 1250 552037167 552037183
    0x1f150309150509070b12040b150604030807030e010504061209230a0c0501030b10031806020a050a12061d04060212070c030f08010f0e0405100203012303060114060705 73
    0x4802007980070340451500c14020101652091070754440c0d40c5001401c40d40e40710039104100004413010b100342e07070303180c940741c1019500030041014003058100d01e080c19030790000604051401745003000e48a404a20b4080d001c100c50545444c10300109010030030407180e21001010400598400107d01c900040c0b42100b004030450f42d450b914405880250701e00d0070400911010014022030040c00707415074070001501141d2200240f0782d001b00e0030443c9154094045d4011100214460301603141081e601e4462400302c0c4c00100c4031400241002541c881c01e40d2348400c4206502080368001c100d150f02d07140128607405900013203130104610480000d4144047d640c140c807620481c0c021886024a05500c004284d185d115030100c1c0894030041d141808244a4a40d80d4142e8804004610b400340c206054200c40910084c4111207a100f00c810030f4000c2c000e1400591300a144040c0c0c0c00e4ac82d42d80c4508107044000c10544240e0082c1e004c42c004101e4504a03103086034600e04140e4020390345100307505100e8101006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 552039667 1250 552038417 552038423
    0x60a14190824221211060a05070f0e03100c0c0807060b031b03030406050c0c0a1e0605070b0606070804030507030803101710020d140c040e1f150309 65
    0x9100c03003204007090700081c101c2c5a02c0728000301441d940d5511086006007450111110800000380d04424000351030303031240c0c0e051110f1609044660a0300c0711043d40c45c1c040c0440e0440611b0340c403501400152500700c0c5004000c0c40b60750610111044040703021a9a60f05900c08502840c0e458100c1d0006041c0030702d400d41da030150046850740d611117041c01c1c03144c090200000440d010f031260840420b240d00a10301c1c2e405130f40c2c5005000e1440c2c546416000c8685030007403400d402a030b003c0e54644c84501d0b1707603640032880200392120441441d030745684011350203030f08980d2001d41800010000000014520050b642e8003013001c0350150740b20b4403a030230070b04038074005e54000800c68807a1a4020040c4158500958032850380703840a481c3c5103849121064480240c200b2816040e031101d48640309294054001d0280c4091001e00020801028404010000ca0540d494684840e00181c1403001f0240c010015a2151403607205803100c120b1200300d43c40780d2407103109500007219540d508070410b0f0b100340c000c00d01e0260 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 552040917 1250 552039667 552039673
    0x80412032c07080601030c06080613021803060a020c030403060c0e090705030a0b1002150c09061206040e0f070b0a1205072601080703030e06040902041d060a141908 72
    0xc1007803039606004500c0712424032840703030940001e000a40003c0c610705803a40000089071003883e298056035400d001400c00c81c1d000713401540912070480d0910290900b21800381d081410244100e0526041c250007804020051740100b0240c02c07a40030000c125070440c0ea00480001b03155101c2c0108990507425204a582d12080c1c0006200c0c0380c03503200300034500070030b40740004000001c0075000300006058243d001b000580c10071080c1542080e4a480d41d075a01a03446c02c003141c5401400c00001d075155004000c0092542918400e000f4542042d1054010511888005003c0c016400241d80c4d0b40b00018030602c9540d05000846041c600d200e1180382881031104842407019081a60003e042c2c4003219244c1c402140b200c0312030919640344584498103c503001c00203080c3d031500359282141d02003601940c85822410801002600d010144010402001c5500c1c000302c444400c2014103000c800d000c1d010a1040000d01d000344000003904a060340344440480300c100c0244000c0340f485405000317607841203410740 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 552042167 1250 552040917 552040961
    0xd0608010213241d03120f07110a030803040b090102090406090b1201060f0b07030908030a0207030b01140a0b070201031b05030718081002130b1309140708041203 71
    0x4440c5001d40c2a6a0940800c0082c100141401900032a80110010006112001d4035200350104030390707a9041350001d000e41e000091503180303503503041c0d0002c0402141880002124010f00c08010b40603844c2060450380c0700509461900c8071000713400003404c043c080b50003400100300015001d41c125204558041c0080c00415a1040c040c4014104a82d4071800743c02e001119103d42003040c8104030a4504150b84000340034240701c014001c0350440a07040b003e00501520104c1c0061040000d0410403140e81d000384101410361034442aa110107900008042d00040d030348581c0c40c0d49035203807141900c5c09218007a45034002400124007820b2155220038014181601c01c4544685c0302c8001d5110703140585541d103070001410b250907604c2500780f08059a41d00b0241c3c560404d0356154000305659565400c4075180141c842040c0e29045d44246a00107800c1c0000bd400c1208024500910503025407891482e252440d01e030f1000341100400800040152003906010320040b0b0180d804100315007481d00c0030503090 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 552043417 1250 552042167 552042187
    0x90f010905150613060e15180f0603030d0905010c02071509050f0411070b0604051503070315091203020301030c090506010503070309140f10060f05060d0903210207020f190b0d06080102 81
    0x45c06061f101040b82c500c01e46620310f141c5c20001040401134400c828000030715a00c01080c52807001c8007070075099040c08100b01e15081c10006016513103080b4042c1c00000b0b05e60381c07002000703803138260301c0e904c01e0b01c02c017080049200f00103401131800e80c2218403e484d2803541c0100000000c2c000d00c1042588004035002040e4801801950f039031140c41450140c0b0b0410240c0c40f0301580891400e00d00c01025850f50000409000143c044840a503181281c02c002081081072613a5200100094649080000c1d83c044010014003860041d504010141c0d0030040145042c401d0009209200003002d8005141c1c1f42c8070500204013090f08a81c49411040059401041f4102425500d80c0c9034907031200c01c461f08005010551030305c0c002d80e4204a0310004c1c80c10380741c8610051018090301340e00c1d10607001e00406ca003101d54943c4903484070131502c03078004000580c1c440281c030400c90f001c0c81c00107445004883c081c00c62005500c0300d05005c01036a6043c20801e40364101c4040e0580501443d4102030142c0d4008240c070380300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 552044667 1250 552043417 552043439
    0xb18220b1516030c02040209040e0a03020601050901030317040c03020604060c020f04021213050c10210e060a02090301180803040b0702030a050318160608090f01090515061306 77
    0x81182101c464044840400c000461801400400381801c201d14030036100203405918151001803024102604103030f40341000600721401d89175081030580044145004055041c00031a0252808941542c0c1310750650f1002800104400e250394007a4101802160501803440506401198010001990f41d03860b584020424018104102d01601c03580756041160302e13040c000e0300ca030020035107000c1c504d55481e8880c405010514903800d0f1180c1c0241c02c130400040e107464060040390007094547d00081c481c24801800c1da010340d000218461850851030000003500810741c0394010441c0b20015072140c0c69500003c0c0180f007442c211803441a4440c0d1500c00b0040300750f004c0e62040b4000e21403c081565554001e0303840b842404030010005100704001071103041303405000c9074001d03984c5084441c450103815820241d286a41c100d41d001c03600031410401200c00800a03400c460904200902c02e900461765542d60314011f100d800801d08507450000b5107143c45184028041c400080c9051020599545064038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 552045917 1250 552044667 552044681
    0x5010b18060708070210050d0e0d0f0302090906121f1b0801120f0f020306090a0b07020c0d08070501140a0b010e090c1b0309030d08160206010b1822 65
    0xc2400054024040c6150407015900107a03000b210107450004543d003000340c07650981c1c242d2404c0c040c0c140098032844d001445804002c078220b0009002e4a03011352009010f0a1407003806004250042003140030b980c0780c08509581040050710016010105006982d0038000c4481e81002030f11074414205046081d150003900b1460300d050040314a1103280e91003100c082209000e416524030321301b43d00e0400a000c200c0b080e901c4601031a41e282120300d40350b0029003042c20507111810a81e008c0c00e20001440034140b000d5402941600007012318860f80c0c00460180614000040c00500010030843c0a214084d00900220646c1e1000c440710b520f041d02d00400182140d0f9803450005030b2502c0f0308452070502841c43d50149000204050804c2d025401c15900f4082401c0003400d10b0000b8002103d041d00e003004188840344003510b0345074140c40c02200c000d444020305400201154851401004070b9507000040700c403000c09801400401a00403804661041001409030462500d6010041440c2c2c1050707010342 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 552047167 1250 552045917 552045937
    0xc110307030801030233070203030f040303030f06090506010c0312060e04150f05150d030e031009061503080f210f04050c0d11060a0201090f050c0108070201050f180a0605010b 77
    0xa1b5a030340003500c0709040c158045001d6403041103d8070702e2003035034042c000900000c40c03006003140d14041e1a000150b01c160400e0703000b01d005c82e40f900c0701a086004a4025000035241c40c840c10019480c00b0341c0006d00c50820b40c6c201078203102c1081b0408100581c03075001840500000c80007a95503052500d0244440d0010b0245059490f241141e084400b0105002e814010f4024007003d14401c4400401c00910002087c001c6003445214207880805803824440500e912880c40c5001402d807203941031443c00d5461602c140a0b21b820410000c2c80010303100310544075000c50707540e85161203c070111450101c510f900392040c41e800d000310003040b4040803002e104621a40c0304e80300b6265450180000d010711000d108500925500c030800c0c24040906003c406406483c03220b10000c1a0740a107600c0307400b00510800d03426919030b007000001c62210f503048481b19030030984604c0200800c0c40c1680250b00303540c07000303001495040805600c40c10840b1040003141f04690700030781d042260f9690b54025074180d6001480d85 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 552048417 1250 552047167 552047179
    0x3010806070927020c010608030c0d020606130203040f2004180b0601050a02010f09200d0f060b0604090e0f01050603030909042d08043003030c1103070308010302 71
    0x14225441100840c003280c05401c0f0544545002c0065081c20800b10740c0e0355204640d00784601c04c8140000d02400004100300001341d903403120703080b103998100110f00700b411007594402000e204c5035449030010320000c1448800b0058503604d40b881d001614110101000d02412405499422391060000c2400045d080131038041002d003c810704000400e0501c1440580801c0c5014001000c0b5401140186295040ca1000142d42c140000c1c00e0022100c070b01c5010742d0001c00c6a483d01074980070f0400c10300c241b81c004440700200d8001565a03490000618940149078645034095681c80307482d0303442a1400740a80420911003214940015561405c010b14034010346d6080c24045203003070801004030344549401030911081595143c4071050041c0d81d4408000c0400c0c03a01c100103075654140907410b0300d1148201ca0146c0d4a500c2c101c09079003245403090b0031080602144441c1d580000c1c00107145440036070b1508003c280329150726420703283e1144202030380e1f4541c0800904801010b0340200c038181a640b0807034074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 552049667 1250 552048417 552048421
    0x50f03030a0b040e150a150f1a030115031829010906120f020312070c0f060305131b0b0d020403020406080102030c0a300501140102150a090206130b03010806 69
    0x1040113450f010312810003039401c8400c402c5104900300070780660020140300b000c02e10350074044d041c0c0440c0d006903100034091101504140182100c1040100c010140c211001d07085504004500300260000d44101091594440d21642403004110200c6200354004816400c00448103441448001c3d000113800031481160001213a407044030310400c002d036002100442080c04550791410284080c0100580e8184180e50b01da4800e101e244d030051004510501402200d149028000344509807184c12040074103040400b000498200301c224010354581102105c4071460244040741020800f41d08410a0660001070311940c440d119001801200d20031b03602001019992520640ac1340020303506040c14500400c8070b4040640718818800c0540d0440140300030110a2040600542c2061042070241c1a1560010802042d4121076200155000c1c00904a12030341c10000c1072249030018000c0110b55a00c1c0801d0301552101e2094900315100e0000098805480f90446c0c81181c00900c6540b81502c90200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 552050917 1250 552049667 552049669
    0xa0f03090b010501140d090f0c0e06010c060c030b040509011a0609090a0209060409051603110702010804080a090f0b130512030702040b06070b0703060510020d080a050c07050f03030a0b 81
    0x8240840603401c008501070300c1e42000011140710482c20801003c819003400440c0b60500d583c466886130310f20402100391a84000e00d42002410304e1a0320400c2011030780c1c401c0106d6a43c00140c0103a100340e01000006103203280d044180d000b0040c10512540051810041003201c036015030009070415004500303a40b2082c40a01001294419240600c2c0c000c68802c2c04a10400340750b030007400e00018010103c0d400c2c96102c3d4019011a0400c44915240304207100351000d0454040c130644d602000900d82151400300b003a0000703040d0b41c0f0050001801c941c0c0c001a40e00019104040000c05001050840000c05984000b00c0e0000d07000341c0c082103c5200c08000000b00c526001d428028000031b100041c42c2000210f0f000c21004081c0401903940051040000c800041c00c49600c07984a20555140011842d081070f00380106004111028801e6601c420026403c054210a0302d552000c950749022540d9039078444007034024050782c00e0040c00f91140040e034800039040030000d075114400a4408101074030b5000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 552052167 1250 552050917 552050921
    0x7050a0507051f020309060a110d0801050f040e0c091803070c091b140304020607150e1209010e040504050c0a17010b15030106081008070b04170607090b0706150b0a0f03 74
    0x40240c0004d41d108001014850500c80007905800c81c0500305081e0741003d040f1040e00b094203071001a0001925003006010611b80404841484801507800300300c10400c3c201c4107603030358001240e040e01c20404440012012941185101070441880d0180c82e01c0e021107141c031501010840c0948203840742841d04030680c404007900009410441680d030202c940d4684043c46061f50710150007660408000c00800300414a040410304000009000c00140c550300300c0c40c07290600c09110690325503000b08004c081440c0e81c2c070100305012070200301d400040c680caa602d0450300d044000c0c42d100b5000000c5082c0020b40b416600740c2d520340307100302d5402800706003403180030401c9007002407180075014030080c00103212036440b5a4099601150407500c181c40b81d6200e440d901cac580146a40124058040083c082c004030803014207400715000c1400052a40d800d0108002d130a5028601807108401404108030060003440c1d0001c007c01c54241d01c200b01c4054485d202c0e54800e03030002051313101040a501c1f1010b0518428 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 552053417 1250 552052167 552052219
    0x80f1c0905030901120f02130302040f20130315050f0c032a0d15091a030c04270303051e040b0106030b130e012a0807050a0507050a050705 61
    0x1d0041c42c980702c82d0300300640700e01200c460021200360f61110458101d502d00d10041011102200e031140b1007929500c10030080c2d1780701e00e21023601942410425158000119001100c80c0300600e5600d03243c500015180140d04180e070300180c1044841141615428950340c8200d001d410f503201ca60700295140041c81410380310598486440c00c028281c0e289440014074001c0750088050191a4941800100500d0944040550b0080183c0c0031050030800000c2c00d100310601c001002110040818109000984412000700c0c0e10740115180c9119003416100040c050201c030900b44594425000300741402001820f003101c040b840c1c0c1c6803490999805091400800c0c0c4560781c0010100100ea003002c13000c80160240031142a000940032039901d90440640c003130140c46140e0840001f900041e2a0304091202c00a90708070305804c041015150308440d808090180e228150341409940c5940d20035049500344904032000c1d201d07015860600041100118540741140c10441e05c0e411425261382c42c4e840348801d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 552054667 1250 552053417 552053423
    0x5210112050616021b0a030b0a0e0106051e13090b09011407080412140d0603060b030d05130902031009060315050703050105220f05010b210717040f080f1c09 69
    0x40d4170030340d040641081d40210200f40035140f071031000c0c0c0c1da0380d40d091038510580d074080e18927803510450140094244214401084211840d02d1040000000b08494241c1e65420343c1c0980f111555084030155150018000694040d041c1c12040c0b8110038110300901e4001324900b20144203d000c10b40461080103080e020f10b0300f0201c00d50201c1d1000809071010001c200050500301c000b408500e0241075144510401180500c00224941c0440302c1010b0a02444880345001e0000500901c17900b003103003507900820740380380480c0143e80ba15078104013400c540f5264080350f41701d800d005022080054403900c040014160040c1803142e0340750f80d034040c1c0c10b881e800d00440f03030403036070480c3c140c03213940001c0003060030000903448006000456454554207441c001d0f04111355801000822403000c1d2850640d400000c00000b1a440c840d08102000410020381c3d210031030078156980001c81c00b0302c00c41d411303811000ca5116024540c1d4003400c14041001e501300840714110868951094245400c0501942e450654 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 552055917 1250 552054667 552054673
    0x110919171f0203010b160c030b16020c0d030903140705060403031d0405360a060506030708060f01260d030501090e0102030c0a0302070c080d020a0209180705010521011205061602 78
    0x1b880701c051840c1540d4940050310b030340481d081e001011685640105000300803401d04c2d815013000f5070002030310301414010400d0140401c034070000c001c243d000d84d800d000d40ba804007484112414580c8140e16203140c0d908129401140014008105500300720b12401280e008890300c50603850800c200012507400b2a510314074001d88fc00792040103995240488101c41d45030300031030040d0340070114161809148100c1150001e0752402070148a1404000c004010700c200d6000700310601d800c0010020030a018452842d03c0701000c5a0003800c1d080b009214404c1034400340455650300103070080100600003e11a142c68286043e522b500380381818000c5030306c5480109600d62511781c034150110004e500c1a0030940c0c2045010740007080c110414894040c1011495004103039281003801001114007000c3c04c0ca0025117400703420745219040104416003102e009007041900c600700e280d0011161800102003440b001694800400c0d40c003201400116010702070030488407a5650108000c0b010403208a512000d64 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 552057167 1250 552055917 552055927
    0x1a031f0506060f0408060601090e042d020405090705040e01020a0c1121010b01080609162102040b070c050a0501021e0307080a02100b04110919171f0203010b 69
    0x1011581010350001c201401141c41c00386001c100c050160840d41061400b60055420300410b50b9001c4481d802400b940b130135500550400e40c0ea4a450700c10b081428150880b0518000c080351040803100e180400d4020380f050101340742555855450300614060a88540d180480704100070005100f40d074002450340c5c0301c0d0031140509031500640c1c0028020480c1e4007038102084503615443c440d08224444a00c0c00000c03803812a14070000d810344070018041d50003148864200300c400000c07604d00c0480c4510745d04003810000c246810440800340e203c0c03110001680001000114481c0090043c86594018031103050440e44840410188900d10301c500c0340142d014001c01d00401480c6400682015040c104603890010b0035560320b05280c003c9541c00015801040841d0042c003400d00800307501c0c0d40111000c0288440301c6407403010700e0003104c0289001304804010500c01c0d2850305c42c0d050280490b82c0d166090203920101082c0d075a0000d0444010a40c864030034454401c165009890507215095000b50030030b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 552058417 1250 552057167 552057223
    0x528060207080d050c07050307060c0303050a090206030c03130204051608060a03050309131401060917070e1b16112110020d140a0b040c020a020d1b08030d1a03 70
    0x907000150130045d280586c030400243c80d541005003900030700040d20f94010140450a000c0c046520003001644907904000c01140180d030381c0d000300e9621601c0c040c0001c2d2240c4410181042c650704910000f50030a180000307000c06400780d120102020703003896944240d2642c0391720a210080000c1c1c0700050107079000b0700c810701c01450240400d010f04284c0c0040090183e03004050550288001c1e44108023054098000b44840c216154041c00c2443c400c10044c07105519112482002c8400148001a00808503843d4030f8a0100503084503000340c0442d508030044d5a031810107030f8140c44048103042c45049925211b07681241c0483e44401c498002002038107118020707210341800b950266130b6120100c0c1e03860101034446070884d210140036007002d000029040300a2000d00045030201c40c008010b5500441c10070005a541a0301c0130031459101d01031111002c8200c80c19015000c09410041060201051074903c107126a0b00c41c20030841c1c4049502d2049000b4000c1c0f507110000c500d403a071480c6900c51110040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 552059667 1250 552058417 552058427
    0x109080304120c080406030b01030b24030a02040b070605070e1c0f02010c08120a0b120c0d08091201020d180b0a0908090a08010f1b05030f0903040528060207080d 71
    0x3000b1604160b0031030041aa11045075a01c0b80d08400017195a64404402c2075134180b1960441c2c00c1c094614120f2110008100d1a101c1c4450103813069a900000c00144080a6601620002c0c00c03000011500d5041626004002d04070440d03207240000c2484003c1e5080749020507642c0030010380941100c3c0b29480644030707001e4a40501c0000d0b4180025070440c07400161001c2d00902e400c580840d505c06403401c0580f49034060761242c40c0014481c48a140785910b00f56001f1a200139840d0040b00c500c01c1c101d4451810300424000c1c801181c1e0f00450b00e0560980c01c3c0410340041c041d01700e9008042100740f0820f000f88151842448015019440e43d200003200101c495000740c0d0501c1c001c0381068141203800e0300050800c010f0360000c0d00c0594603200310320992a5980a0050002c40d030b04020042107900800003885800000d0052900440d281d002c04c200b42c10500446002c2c0c88080d0007020340c1c04100702c07203110300c1b00f00001a908010345200c0c000741c03551011408000395075004028041c0038a1854084071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 552060917 1250 552059667 552059693
    0x1206140a1b050a0c08160507050a06141b06040c03110604060f030c0e09071121090d06090204050406020417010b1e1210090b0a05070207031716081b0109080304 70
    0xd00c000c000301000440c0c060f40c0501301b50600b699110240f11464075026052071503c0d80a1805480112400d111498014400700400d80d441070005440301c40341e940901e50840c03100350205140c0200010b00040c88554103003802642e002c1c1d07007900e00c0d000c049000d03c9124031881c070860307001490310442407270100c0c8a6044084044820710b04000141d41220004101186c2a01c042c0e002c12580d503e03117810707194207010f21891600300c0307440748812140420340307201c96100703075175003103101c4c002e00d0614008100942e441016450340240040115141900c4c00d07000030b52060017150501e0b000611140b811290502070b0b9400c0070809014071516044064404c1c0018280c44441980204001c4040c81e060364104011421074072501c0001ca07040c51075081041c0000f00207441c950709182443c0400031f0b07060700010310f1002c8035402070303171004803003603003c0d0001703442c0500c0c0c003036044100320790707010320140700c0300c0f0010304014800ca544100c078030100e1000d418201e40500b2001012040e0610000b0003040d0f800a08030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 552062167 1250 552060917 552060937
    0x60306010f0c021801140901140607020a21150b03070501030515040504060207030f0f08010b030c1c0c1d0d12020102040b0d150f0503251206140a1b05 66
    0x34010301196001035164658105903801c40385059004100d1382d031b12048030304072008050341d032801305505090b0030044c452243c07020140030300000075101c0115242d190701e4a008201e681c041c02074910512418000032811070700140c844074010b0506984180592040e00d8007010014001d240701c3d46408015001b4100083c00f80e100c040070b500f201c19072602e5500540784078611400f40141d443d04249005410495106010300811501111900b52250401c40d40781c10368894a8034a81c0302da4901382e41c2c03000c0723114a081d6010085207105908112083c1501719003024010fa0300ca030f80c07030402586400028803216086040d80404621b000e840860b00340c1074201491001d0344005494507803150b541e68641c2d40004140f0f08a00c4e0380d0001c01075141001c440c64400f0b40444202002d145140c240000d58501c009016030b400c84500b200100300c41c04007010880c0062803a0704024440c801d107820440010403d000320072200354a030308001586940c3c80d100c0c40018042c0901c1203070070314414100484098012015803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 552063417 1250 552062167 552062177
    0x51e07200309031209040608010504020d11060d0615030501090c1d030f0607110111030c0a030b01030605090a02070c0803090114130504020304080c0c0f09060d0813030501020c1902060306010f 84
    0x2107009840512030300e07913440107182c0160350b11320403201840100c0d0000d1307100d0190b40c1d14006c18440181e403040740b6488801e400880c0c01031700c800382000090b000d10410f21224003a51070700c030300041c4400304050b0702c070b5000c450b603181082980c0c3c0c1e805100c0c05030780181c0d4001c800618104840403045809404001421001900312103240181c03003010344c5800001d8408401003003a05141c601030790801d00403440e49404404105045082070381c0019440d00580c008030f4141610352800070090791180d0b0081d0002e10f401805400c0909145d130b024402540300d0034003925014044480450340d03440010440c0c40314030b810380d41c40c40c1000d04d10040c003100350000c0039207003a0290300440001c0d1a965500145010380d0041181c1030750303015000792032458107410030340c0385000700e1900c00d4007803130341d542c6400b866882201500c040c04a540705150042c01c5118002200850440e0344001100340030703055000c2d2031007814542c12281d007020440042c401e0302c40380c81c1000394090001c00c005680c0354070401416408001500746 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 552064667 1250 552063417 552063427
    0x1a190c091a0d1409060610050c070b030a0b030106030b0a0b0102070503060412050412030e2818060915030b0f0f0a0b120102071a0a0b03030702060f1309051e072003 72
    0x10501c21540300f6101c215059204030140006c928241a980c1070074501800d00e60311717084d402d40705152614a2032040c25038001000c4001094071074290018124040010020003a590310b92400100d00324056803d442010304c2c10910001c15400010682d0030303904000c00030406503032550b45180c40881c00074001c0040020500c00000c0d00d071003510049400e580300343c03035411812149101380165a1000d104e104110100e2b030100c1d040d841c0c0040e403000181c0e01c0c03a003e032101c120f030313400d00301400780007240e1048480c0c034070704002c0500781e40c000500e000a4034030070021a22031352501c0c030460106c010180d5940c4000c0b88080003050399904c2943c00044100d1000d006044144a07982da45c508a80144006580302c0d10321502c0038000800000d0362540c00043c609003005000000c0f00030940d01e019000000303000d0040006d01c0003000702c488042e1002c10311040700240d400c507202d42808002e00401e545c6010065403e54142580c0000720801e02d216605aa03a41042c1d5140b44401517203030168101590751074041040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 552065917 1250 552064667 552064691
    0x5060901080f0c130f030312050c270a030308060f010306030503030c032205010f0f0528090b01080708060121331a0a0e040308041a190c091a0d 63
    0x13850400508007801090501465414098420070707009410f15078a0345002c04000030f22480c1c0d401c1c6d40c4030300b004150200d0f03850a540d05080211084c0c40c9481d81c00b03408042c0000416a010785464882e4001fa18285880580c500054058914500009005800a0001407581000a80a50f03031140707204150744d12603d0384d000f4512405007841d0042d6241c9e51201540b4414814038004c448199140882c100308030b15000d510000d040100e00400040c03c800148618005030440d000380100e5074102d0380a000d1540d44e0b43e01980d540c07441e80703e095428001d003000018260541851004456140d80b190070f42c620079992900c3d2850034540d030425890f103544000e01c0680c18100039814005006050020b9010b800042c81d0f410121103000c040d2251104a006001036198900b9054009070701d41007110701e50f2240c0c0380c01c2000c0074100318840070f4207480e0410800c1ea03030705072504a0500100341204021054201700100d814a4043c040c045444d0003507001c82c2e0b9507041200003031490307051a41000440c104526 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 552067167 1250 552065917 552065947
    0x3040b1b040b04060327050705370303020d080420060d0c03020c16080a030e0607080c0705040c030e2109041a1002031c0213120f0b0105060901080f0c 66
    0x18004e40c0c00250384415015201e18403000000c002010600880b06040d542c1d0b0b5915070707401c0940546402a24007000c00c0e100791031900d1542071041141c14600e0f46000e501c41202d6504052484140e006214148541101500840c6100d0007240c0081c0685200c10781062550401c084501c04550000001c00444115030168441e013050803d8594001da034491504c8815441c1181d000620841020341c001e0400190400103010074005615040c80c4031803140e01c000050190290007009081c2c1040040d20040d40080440d01c601581c4044804102114041104404031014845503034038940c404100c030035543c0101310110f40c140e6900807a5616180341e403c045000d81c5c00444d91040c103c01d00d10305800103807400c0d440f0311035121580e10045007406600d640c01620f019140700070b4040c4581c00540749040541c1d0722407040c05040d03040180010b4207418648515007040071101603881d4650b80740080781c0da14008084a0100d101623440344103544074000200c00340e00c0042c00341c5071000000c110f00c0d503090f2040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 552068417 1250 552067167 552067169
    0x723040b07031d060a05030a0e010e03030415110301140906030106121a0601030b010912030c20030c0f0a0b130906080706030507020d14030405070e1512010203040b1b040b04 76
    0x180d640c0d81e043c0a84070700e000d085428584071030b030703c102c5091001c55a22640201a07139031020008902090072010000d60382d00600ca540c40241d8113000000801090012522031a944003082200030000340c5005014001c0ca40420300a080306000307462020601031408030512500b0410007800043c1d05580c3d201302d040c4060582d0303400c030b401100c80c04e41c650044144c5140c0680c081400e01302440010702000009140c55428000c04100c0150740c844902418895060350f045154400019031300400c480c41c2015240685150300c500c030344103006e52680c0f14107022894124002c8060b001e04420f50515001c0704140c0c00c08c0089940803200d040d0001040002802000000c2144030041e10010381071100007406e455004140000790342c0301c020307508400747c0d002a030420444600d408458807500d40e403900505000c1140d01c06811840e020301400707c11131110000d07101c01041141c18407602843c06000bd4241d00003214040e02d0070700c4010010709031007074040710320702c100301220005441c154031400042d0701500a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 552069667 1250 552068417 552068423
    0xe041a01080109020a0e010302180703090203030f0403112d1207060f090e150d021c0506070210091e0503160303060f050d050c04020d0f05041103150723040b07 70
    0x40b40c90a2041d810191041750283c20f0181480a2a60446d0041000712100000a0310b01c04407001c005141c080c42640051f180e00c0e4000c0650b903458036070340c100d907050780c006000643d1034400307200403131800e0710b0241b03c40b103400c180265801080c1d0b506071f180d8600f60707a4950182908900960300c2900c42040900c503c4000e0403042d1110700d21196080c000404d11401500102041c0003d01e041c0302c11040c800d54041910402290428042c00741440440c030f070401f089840b01151074102c02039404010b004200c0701c0c4940d00f5030b422141160210b0901c0016240103a401900603984028000c00e151340d920500144d160040c1c044929180e5000c14007503202c0d01c0c04005400203a91654203101108813510940c00500c8100c880b0302d41c0d103005858980e01c0e03070703500301034140f14590000d10700c2c80303551854000300386025030038038100f002e803615003880c025030341360520224403074010007900703082c107440b040d0000d40910110303a039003030703d1401100940c5141001c1000d150384180041c0301c0056a91044401000e01d184 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 552070917 1250 552069667 552069671
    0x91f020f0316030305090610230918010c020d0804174008030d05181905010516090e061801060c0c1703220302040203010303051c060506040e041a010801 67
    0x14007420f0090071550080d05601c2e0700c2d000541441840c0180c40320f507105171001404031001c050541050706003901c00c0d003410940c01080ca01e0402c4501d2542080b45031a0b20a400c0080c407604102c842c040340c0350620070720004041109080800c0200316800c200e11080c0b48003125240c07601019405c4c12034003e0400c8003440b000341c040c0940380340014100c021004451a507070880d50300c650034507819a03160b000c0c5c55480c542207a0b5a4000504030141000c905020715418401d0790309621241031403889800390520203484541c02c08011800c0c5a2101c8401c8058007010764a244a041c00c2c8090b5004041e8050882035000090340038208011300e0035200c9500a002945440f18922010301e0329000740c1c030842d485100d43c009966101170342e0321408011144003c08040280c0e89034026070220101c0c00d41c43d80c0020350010300c088004070815800c1401001205100d201154054406a00ca01c00f920054065150014001d00040090303d07504001c0603001340c4120601811000b0b0178209120021099010b100f060b9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 552072167 1250 552070917 552070957
    0x220b0103050d020c0d110f060c030c012007034d070f120201090308070302061b070c050904020112051603060603021e28090317091f020f03 61
    0x101c82044084a4440c49001800e02454181d00141c00354044040c068680c00b00004e0800b902e0780d0710300400f60000e40003481c5580382c006000c8403036560b0300207200070b0f501586041100d000001c20000d141000285041640c0c0c50500135540c1203c880a00300b408004203a05a5415030044035150720040100262040c103600c03810041501900c498009642e4520a401c0b00d031060140d00d9040584005075551035035680c241d014280b004031942e42c3d00780e20181000c10003240c400304150340804c000b030090140068116030300d10b07281c02c0c01406108600004040c0c0d444d012041200d8145000459445030050400e40a44c4000740d5010701a200100c403c1000744c1c10001000e45016018481c200c040c19151904508120700c03900a0107818241d0101920443c802044402180784919000c004441d200d0b403101d402030388220800b820407800e0703010450307142c0185403c054416860500351284004010308030315480f900c424100030510514003503c0210f00407501d0000100c0c80400042011025100e0071401f29 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 552073417 1250 552072167 552072173
    0x12032003131208060d060b0609060c1615020d030f0f02030f010501081e1812040609030c150e0405060f120606100f050a03021c0c030e0d0207060512220b0103 69
    0x24040d01070b80881409a01c0040c0301e65a1a80b10000c3c20140d480301c0002071420700d1a0006a641c010240429405200011066505040400c5289548a07610365000e1500c1d1504105200400b9082c0c4042c0107a0080c511500b1704da100c1d4001070a0807100c00d41c0094009081890301c0c0030b80c0d0044403081c1d00d0078030510040200f5680b0043e2036501c11694003400c4c0200142b0090803401100c041c0c1070340e241c07000707250380050b4108060002807009032a00e0340d041e90702ca0381e13503401074005800c9101c1038544942070980060340c207040380da2809001200355201850308180d1000c20004000103040076801c0350000116003000d072034207444003001941d04001003000745050303010444000d0140c0c10f09020081800c80d0f41004a81000c03d0f2001c0c10752500b805130b01d4408003034002200045c840c0d062680700d400c20041e940d0082d056030000a03104089810303030b074181d00b041d081680e0391104c03481800001841002000d40e296000f9100d43c0e00300201280402d83d074842e04038002019200c0410a8070f040c40c00308010020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 552074667 1250 552073417 552073433
    0x5130806091513030302030c09030102070507030309092d0e0706050714070b1603030207051b010f030b1e0301022a0609150a0c0318050120071203200313 67
    0x1d0496801c2c40c0101a1402480018400c0c0c01e5581c01010b03d070700400411207190700401514826400a0002c546610413802d18a40c0c420701440b05402107200c850010407110418020b010b124480c4800201c04110b40c02c0d4180008041e60f112a900545d036140704801035603090116000170720f80396507540d803950b00c242010140a0200c3c9260007159015110401001c1c0324141510440759090101c41078a01c1e00d81401d0340a40300e4544010308600490040303007a11226101d080d40c1000007030307075420141c1103600819402c4681d61345402e80d01001c3c2c042d4022498070300d000c556100c80c50150000d42403d007100c102046000c4800217035070f42e440900010a002c03050400416601c0741141000f040381045040c1c002902c0000074259043d0107032600191010075001e030f000608022a030710040202d1046034141a8001d0003411007600140800c00340c2c40070024400410b0b1002c507500410302c8081040c6840c000d60003003244038882103070401050918000c056112000d103119210040c404c1036007003654603000744 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 552075917 1250 552074667 552074683
    0x21c0209071d0f0d030806150705030301061d0307051306030c0807050f18040215040302060d0e0f0106050108010b03040c05060c0114010e0f041223090a0509250513080609 75
    0x402a0301d0f010001c08180d580104402e920f5405050040554031880f001c03d5001c1c0150400040c41d02000a0705d004110001000b5412a5056035500c1c21042001400904083c1000105603150380044002e005528000e24103920301032940d4000901e40d0b0b603036598101d1211180d40100ca041c1c010b40000c100c01d06002001942100c0d08454000c07005507044030a4041400181020780901c1d00e107125000490380e01011a8065500200304684400200340c94034040c0551902c1c6034201c1c091081e85014280e814011281a144161103040907a820b1031501101c541005000b503032440c1400c4400526a26110020801c11711400000b290001c80b0001402003404107034000812091030303508000364003168507420f0b03400c681c0c003111001440003001c4007100c0c05401101241d90f11100e82d42854280f1303007060020f090804054070030b103540da640e0340100408407000302c94480140064651540344071115441c40d07141d98117203007841c90402c4a9070144102508050300400c18551001080c817009807000c0103000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 552077167 1250 552075917 552075919
    0x6030c18060a1a031b07170307180f05060f040e07080a05070e130b03010f0203011403010506040c050a0f110d0302030703051f091e1a1e03060103021c0209071d 70
    0x11020001c00c10f8504480c80002e003085c401da020315164641c0d07815074504894811780c221740921580c000108092406a1055940d0707004240d41d0004024054a1031069000b141c0c403200c01c2000b49880c0501740700d5140c3c403008201c0094403080102098280111680e24001d44643c0e8031602c251178114000700c1181c1c0080c1c0a0010f100d514020000690740c0c8000b00c1c00f040c40d02c2100030132812807510100c0d02600303010318500441070020001003902d901884824a405a088009100c6a01d0751310a0200301c1e044030700d041002400c02c0103600605070041d580c018200c40c0c14508004a0740800f038a107418001944281c80000380c000040c40541c580c076010359908040c18041000032003e10400b55503181c8200c1c842c04086ca42c840000c1042c2d44689913003550210b5141c441448a2402c2018040003403001c200941c2c41201141d403103190540719400101680780b8090010b14103031f400c1d5001c2100d0801014015901c107043d041914005844401d42c41d40944601d8840869450301d000c040d85800320481050703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 552078417 1250 552077167 552077189
    0x312250507051512180a140c03070b04030210081806010902031009050f0403030f11031017030f0306040902040b040c021b2e020a12090f171506030c18060a 68
    0x24903076100c00b4504c1107412a1950300d030410403c2c00394000f1828a0380d580006052500e512251384008900841e403507941c00b8084041e59041e988482c0030b41818007540c00080d4010002d505420700e468081c914094000b200100c00940c01c0000300312080c9003000c260080c0780c030903401000303100b00780043c102070030b01605929200340594908099403107128040140050105600d52007990050801f561041e210301004100866a91404082c101441c0000d48200310b84105842144c400032140031068400145101c06036034a180c40300001c200c080c0c8071100050360300654070750a824a0780d681e4480c4850200040c1c004c4d00c0c0b202c241c401080802003041d44c8950203845981100e1081c1e080c018001502c5400807501c41d0681282c02030220725089001d2002045010900e0341600095004a05242110000106804060b49405c52007564082c2d0501107100b075840502c40d5120541c5940e03220b9400403018044410101c5800c0020700305550401041b054100f00606201305414080d1003c1d0140024401e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 552079667 1250 552078417 552078427
    0xf091107020609090606190905090702010b0a0605090604090204380d1505060a180506040303050a030b0103140a0e070905311205032403122505070515 66
    0x10071818070070060300c81c2c8150300000000c0c48580e100f8054a0a007a51030111401010341480060906230481c040c20b440b8003d20700014408510501901610300f10141c00714114502d400d03000d94030364001c24811584104140300100d00d000540c80904000d0407824000d1988038010309402c1e01810b002d0410201c624544d501e81d04429850400305c0300343d03514546002400b040c214a0208038600b241d0071055000310300146c0000342540c8600486030135034140c29442d0041381e440301002500e210700d12001b00465014003090f4503070b90203607010171282c50341070602040402c1d1882114400ea80120b45007040c1c10b0350b841041c049240c040250501030041d448080103e418072081002d00c25450011032515079401801c075a04146e62a8112029182c0c005c854000140c00584083d002c0d0704111040c5140b5003450080740042213588103074030020040940035107101d1a0400d0b0030306199105010101280e003c094140c40c1409502426010b0076000d10007504d9020b082500b0050942e1103103e068103050802e100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 552080917 1250 552079667 552079669
    0x706020d020a0f2a060603020904050a020306070c020a050111030c1006060f0206040206091909020d09031e32070b04051203100608150301020c07060831020105070c0f09110702 77
    0x92500c6020280014001315082d252000140955400c000e410442a40c05d001c100b003000505510010b1084003942d1841e640e4400840e900c08140401a520074045c0c030040040303500134030750308004410b99400e40b480c12142c03807443c51400c4a030442d10a00560707185401c0040e141e10020a01000c1c00340e1000d0011400e003130700061003502603060014400c1032000341c0c079140e00a000f00c0c0c850041407014015900c030313512800c1001c005c141640041d0042070762100c4501c03000064441444032501079444408180503028050101049038600041650400c61800d505509801024180a5109040361001481d041c60802d040442c9844940301d60b80040c0180003100056694990076100c0520744080155191050154032031702c08003080ba015403001800c041d0354140820007009581181d1a44202c68460b40c41c40b00184d442e80c50800d0051200c00d01040d07810003030060700b08403c0c4c01450210304201d4240c45041c0348030450b40c4a1140452048410003c00c4028090035001e02c2283c8449030805145070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 552082167 1250 552080917 552080957
    0x90312061309050a030c021507081c0b120a050c0103110712031103090604170a0507020d0f05030a120506011727030307090302030c0d11150706020d020a0f 68
    0x3034200d501c1444101400d428601040e0310041200760028200c0b0042d88040c10003901c100103038074007a8081d0041d104803c0d0541950780440741015400081d103860410a84008007100400c8442c5e03001a90312001c41aa05a07106d00440c1480e80d81d0401034030520b0881e290007031034238854080b401d05150070041045181074000080d60000c1d0b80007241030021000030b69045000303000b604a000355520000c01800002200000c1c401d220314400d1190911103020848420105e003d000032480000f1802c1044500504008601d412201d00c100700711031102c0000d581d01800c0d42c001000c1200000d40d0800034050807121350095a4010000b0700b00004092940f003001000c03080000d1000e0b14202102a410038901311401d8080209007242d000c1e03a403207040c0020004d0100340c5904c000da1291148400080440c90089000d10030f603a48000c011510006003c1440401a44800b682c84129000e201c0034020070041c0c002040141d41c554401030356103503405c00250105440700111740800c06c1c00032105510300318030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 552083417 1250 552082167 552082171
    0x20c13050709051e0a12030806010306050901120f0602030703050402010810060c12110d02030a020c0f09151909050103020a15020c0103050903070215030714120c0a0903050d0e030105090312 83
    0x284d95220844d1901c0480e0612001e80307040d038a030070802805000680d42c240005060302c5d14401d1340c03a409641c440c0c1004600342d075501d0050a03444090b4030010003100710300340c03c5000d00520813040803000f08890340310340c1c089030130071a4a1001b098a0300104001c40d03030300c82d1391241e1008000c82d29200140c1400c000030321111302080b000308482d01000f40788081034011000c0805000440c000c6a5100702d20b0f0f003000703460742c00407040000588076414950b01e0a00d800300007514480c801410b025040d070340f0000708800c1d6154415803540c10650b41c040c408942403001e20f02801401c501b2030046100d5146105100d074401c043d9020700c41484c0307105051001e481e40891341c4103040c882440d02003025114021500d0440c4030f004070007540904c0d2914108900310000d00918894840e40d01c4140078140c605480c03445c1e5124040480d500d00340349500040c035004421003c2c0080242d14540401c44a1f00c81e61410f15043e080741008001c5404024003080c50316003406066407140040d4081c0d420f0501c5803104682d20140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 552084667 1250 552083417 552083419
    0xa03050c01031d0604062c12030406140f010e06010c050a03030c180603060519080d080411102c0a0311030a050d0801090605060901050904091110020c1305070905 71
    0x843d4100c44456030f0104078808403815801c00d0790103e003410300e09072000b0032110b5656080300401c1c46d0406803140c65044801c804031014000b402403008400150413196100a1040743d1441c7c0e18003400d1082108182010301c00d0034500d230116100c0d4100f81d120500444000c0583d4100040035411400142020039000d004651504002c580200003040c1a1001c1d544c05d1210007080481c0303c800101d03140d06400107000c4a900340c44088150401130320034949500d45000300315a55004440449406105955095009016170b0740c00c1e0010319000005a90651082d81c511300045020010080d540031040d010666103125400c41140c0035108070200751000034074031000c2e0121404003e0380866881c184000c4400c150702000365004004214000b1304008402e000d000071443c83c021011a003800c1032000c3342e0600005840301e07810b0044c05070800018007010a011181c04006000842498861215082e280c0301240c000c0c0c19028180c1092200540000c2c4200c0755250404062005c0d154101c0d080800707840e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 552085917 1250 552084667 552084671
    0x206031305122125050903122205090105100c0f0b010305060c03090613050c040614010314011503240b03010e07080709150908190209060a03050c0103 66
    0x5500181100304162520000e81140a020180200c4801d042e004220516000045000c00310040c42511080d007000c840146031801200d0600100080e031a00b941d400c9000ca103440c6141481c40404a8242050b02c40303413030504000840d000d1204080d86100b010311403a070055405125250600040c103070001842024010200741004000031845680c80c001c61a80150070b982000d1903074030b441429508248810b48541c099640813820200e181002c13240250321032801040309442e6000d05e00440c40d8203001c11100b40c0710300c08036604562103a0140400030306c100c01d810305d4407030310320f50002d0151380300c1c0c4049140c1d901505005005481a45010f400d0905480c640004d8101c5441004415a04402d03c2c0c000000e4441900050344240d2800031816600403240c00002c40d203c0300000c0c1d62214050b1200c101043c0d03c0002800110f100030000e4403001d40d01d02d130000019607a002443d09282032503003510301e41d00ca4401034600b5030401554044c0c11074806c2d41d545885034a5900e900b5201c0c0786c1050080d0401d5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 552087167 1250 552085917 552085921
    0x503010b012c060c0c1513030201031a0301050f0a110708041404022b0c09030201021c121104030c051002031c02040e09060405060604050c0703030e0f0d0f020f07060c020603 76
    0x180002440c110b00c0708090501a51829620041c0b0364541c034900c0003078880e06d4001d00000e0340d108580165002c0110815620b2116425640150007404010030742e01c2c44400d108142509c40d507824000c4c28000d0203034405100d541c0c10150305c00030030b60b840b1083c4554585410030404000511840032202240e03109600035280080780d40005001e0312a00d1512600c50742da442100311044142c010808a018080700d041002103581c01c0c0030303902c02c18284406800b5030170207410042010600400c1c4041312425290941c040340100c2170580403240f01911a0894420101d001d20400c4280c0030f070b58001d440201c9000c1520343c14001c0080d178038810505194814580c040040c0c84003d02ca8042c0c6000d41040d003070a982c2e40c901007582940c1d85008a03000d885c14490300c1c0124541d401c191151501502c0c030040032614100f1a41c40640242600100300c51043c801c89000088402090007084c8007215590340e10b20702d4030940040245410b066100c15601900400390402041c4c2e0810160500070760f06031481c54a036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 552088417 1250 552087167 552087227
    0x3041802040911130e060d02060c0f07140f04060b042306030403030f05280c090e04081e0301080a0f060e1e1932031306090503010b01 59
    0x40c1c000e03a44448552030410003c1c0114148800c040d220400f00036501042c0e081d0391316446000650251641c54200200c24666009828400024160648000c04072000c811044140342d18150b0303198055206580e800038000340510349008850040b03103040710b003840214205944030215104510845c481c090001300b0884e030f5000402c00c01d210f5514001c04086d113a142c00e08000d009402078180480403079181800149581c800f240d02103044c2c0c06042817081c0d0700400b07503038910020100306124100340100680005100143c01000510030352080c01b0341c46e1100510413100d8070040410a03688040101400140001c903c00a0f280b0740300c0f900055100c190558504280000b40000c8414210038042c204800c1c0b508600038480c0000c100c503020403540d040e910000c0c804120800b480004000c0795185240c4400c680500c02030440700a801402d1200040c05841024556070200c2c4020b0340100ca15a420080e182d04482c9000c020719080e8000d000020904000030408035130074682c1109142480705e90071031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 552089667 1250 552088417 552088421
    0x18010b060c0325080d0507030e0319120b0a03080a0e060711090c070506070207170d050904110906041203021603080909070315090912050405011e020c04230f060102030418 75
    0xc0103401c2108566a0940b170101c01010304400c1314450b006c6801d0003070240e041d8000008032943c1d502940001007a04051207001c907402c151504011103032588a80c8015200d6845240d194000c6102e1186965600d006c2d080281041d001c1003a6503101e10002c0c0080b00108480704000c0076143c0c41100c48002ca56551007000d0414000c22a01501510590080190f40c1e500043e0301020790300c840c1241d01e03480304c2d02080d0790350316020310203e00b0008200f0311841c5181d0138203400c000400c5150071101ea06201e440404603007203401c5035008840c0e000007a000ca105154043c4288180d02e005040c82144080c00c60b213a111492007213112160007016000e00203070a0038400e905c01c0d0b4107407010a40c1e03e46980e40e0341d0003440c05400c1c8040d068a0340d0080d04c8000507024003074011141283e82c1a150300c2403032000940064404880d0342c0000c002d60050380b0118415682d14403950101c0d403420007810000070f52205145041130401800c0d88001d1002109200050703130000251001c0340c01065a400401e1010005040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 552090917 1250 552089667 552089737
    0x503160e2805090a050f0d1202090d0501020c1e01020301030804060f0c020301151a180d08040f03031130090d170a301a0918010b060c03 60
    0x2092442c20007480300c503907000704595a6a0340513004456040c25a00d0080c1d48400d4510515000319018030700e48460810350780c000c2d00014000070403422440c01c0c592640350980e48065800420f94010030200456171540420320450044984021800c560440e907030768800d40305500440c0b081c1308101500d5024940314407d0558803950280c000c0c40039a10b0310810380c40440c020b000d080103941c41d030758600304151414401c1da03088091105440350004170324401d1040606501c2d00940360700784108004110b04030720b0300503200290311a642d4481d60613506011641408208400305201c0c0745071848040e01880b48282c00c003100c24114a0283c2d81d800c803840010240801d407000103001011103101d0740103e00190010300003104051f244c1811990410b04600342d00c4411b00048601004030180b021302e40d4681d40c0c00b0215103c0780e2501841d80781e800300300280b043d440032225841c4c081d90902d003041c6400020302510041c0202912014100180c2410042d144d00400d000d02070741e000e10640303003140c0800003600b01c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 552092167 1250 552090917 552090991
    0x60d06020d0f0c1101050f0f04020109030b190f09051e0f07240809060a020d06080a0c05030f0c0109090c1b0c0303020c06310503070905010503160e 65
    0x541042c0d1525140a00740b003100c91004200d401a0311800f00c036060088900c2003e802d03448280d80d80d08c10702510f0b03074100068801e0b410400600030100c0000d40400c65503024500318000034502541c01c0c3d8140382982c04031100e540035503042040c40b60003d034000446020b08041c422540c0c0b24090412045403a10540000c100351910071100000b4440240b085549032214484410840c062100344068a0320002500c0c09441a40030034005000b6030a154042c0415880021000c58180d0f0f50f25540e5250104401003989c0c001003a40c000c1061f0729013008005c0c420301442003d00360445005001034100002441006e81c002d480c1c40910205502c42e6501600510400c1411002d18850b42414003c0308181e0108602601c2409813800d004d20b026001d640b89040c040c140b203c080302c1905001440300c000d078020b050480103118000700b62039800780a24030140c1345241d0300195542c5440700705480c05540100301e00c810403a0400c184000700b404131180b2382c002800e11030315566444002e030350b66181c0c0c0004041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 552093417 1250 552092167 552092171
    0x412110d05151b0a090f140306040602072105190306120213090f0305030a0c050f0913090b01080102130b0306012a08120627072102030f011e050306060d06020d 70
    0x80c144e54000c002001524000004441c0454440b05039228802991b000968142d02641c00100000e0740b9400403d00c45200300004020306c0032122050400100042c00381d00490302c00b00b8a03c90b41c48001d2100486081d9612b414401c403440c0c9040b07040725a02c0042e0180c003401030480c07e01031401050704a07108182d44040c0c1000710440c00d0900034101d410940d900c010140c00d05080071a8148a10103503119850503500452800c0c0b03000081201d0f050a41809504607030303e54041102081617000c0182c0200141000980c4e03030800302e40d00c092240010b0300005402d0307030700b44144011039030b002350480c2420003540b11a03204008904001c03400e5051203d002020301c60001a141051451903003010f000d15002d0b02c0703440328441004156400240700080949810400c0000181442e10031034806407554078480708054802042100042640d01c1100c0b44000d596918004001501c3c13620001c0c2c4a050740c14000300041814140081d40b241405008030b80b0a4601985200510505070b046904071038824100b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 552094667 1250 552093417 552093427
    0x1c0c0b030c0a0906020d0e120a14010f0b03120f030403020313060c0b070201181e0b040609020916020703030e1522050a030c05091b0412110d05151b 65
    0x400302140d0040c0d810b0000034035601d0700000c0315400000c1500c0f02e0403054440041d40b803060410712610601f4450145198890250280003092840d07480000601c5054008038161100d040d1071030079147c1c6949054001d50209150000b194090000c1d036030700400002146070b594640c0c2c01d042f031650042c024640d8140400d0310002aa054104600380c0301c0a00c070340106a0142e450300e02c1a400c03100c0da501030100c0c0c1c61400d1512400504074800c584d4204420340e94502004d40303030351250442040211800c0340c481b0395860300300c0250310344245025072200d420702c41102904ca021300c00a48038540b038440102801234039900500155682060b058040f4440030006d52501011001c030806443c044480d0002d40284803404601d138104010180107598001030807001175407400e0240856444028401c1e890507041c040342400c1114488001c000404406210b2658091607003043c025100340340510350306c1400c1c0d804200740003c8000c9070b514000900c10b0a0056980d447d099100c031415000d2541944140d40001d0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 552095917 1250 552094667 552094681
    0x30f0f030307030c0806060d0902060d180b060301060b120a110d050a060f1203050c1005010f14010201020a0c0605100503030d0c20060103020d03052116030b1c0c0b03 73
    0x81c620510340e6540501c5100c0c030301e0740d007601c61400664a26402100030021296407220f560820a0f60030f1000d010742c0d260600d00c04590080341c0741080403603507101c0e02e04448020300803107101c2603421210403002007080b540b81c024003140c03070311424020481c90000300d000580e40e80d61640c001401c290149514a5950740348440c3c01c00181801c42d030b04c0100515000000ca0200c072181001002c0d151f20b0325008442100a413401c2e078007508130060000c4907100b0b0000b402510390003402030314000e008500e10b2201181c28484010300c81210000c02604582c414001c1c10440e0344e00002000310070350420000145034540491403044003003282c008a4141c4070004220042c0e558540c050f0040101d16030301c10040c0c01201c081d20101780707100140705032a580590014805840c100800c00022440781c1001880c1404d001c00004540030700e1051358946e040380c8010040c8000c01c20303092440001207440e00308202e200020025030629100e558010200640109030f81c100005d03030102c0c50103080c0d85402c550312807601607 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 552097167 1250 552095917 552095923
    0x9100c051207020607050d0218060c070312030504080306060702040b0409030509041a0619020703060c020607080a09020d170d060806090c09010e0f1e07080612030a0804060506030f0f 80
    0x64445a041c07042200241802e88003107a040d001d03c4040d6107040c5000311135088200a50440b035095640c00703038154100c1ea0140c1e2150010010503d6a602404220f4910704040d0500400c4d400c420702803506020400000030342900807281d008100712a815110001b5001040c01803c0403e06103800c24a00000e401c02d054010740a000000811202841110380240e0761402d0140c1401902d50404070a20219044004428804d080c0390b41d40d10440b00d40340c0d030301d46680e402d903500b200300722026800050a2100311035000d80380962140c1c4a80007408512559404079025440540010b80740d601041020782a25821408441d048070084106200a58560341016220107041d40d03100c24512a400101e9460308040e043c01c0d04032520103800030025a0f4181c98100b1192005100c401e002b4a294104842043c0c3c81c80141d001d00703d1503a07142554905074091145119406012410310391061006400190b401807285078010360101c1c0124150700c030500402d1805000c80d9090244d40540146034040ba0400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 552098417 1250 552097167 552097177
    0x18060304110f040902010203090d05190b071d0d03030902151308060f040b0a0510260124210c06120b0d0309170703081c0e07080601030b09100c05 64
    0x110382c110100c0c407100d4100720881307000c0c0030000d015030030900000404d842d0080c01c0150040c000c409480c08803501d180406003101440c1011a24a400342007401025540aa1080140f403030903540b01507020307030305000501c58488440c402800c00d0b40b150210340843d200c0c0d40c2c02d03030703c071007644540c81740c5030843d09150071001d5440307001f0300c0347c14401c800005488402c5000c02078019900a01c09401540311112220007a1200800d20035000200c80741c0001c003244005103009035110000d9030541580784c955092405d4901d100d82c049040e035102c4904016079540c0e00d4442e8220b549002c0d8a100d030f11a448000701039105c070350b88050a440441440003031007641000d200b0352841c04e0001e0070031200c50207104110049200c0607002d00052010b1105210088121164143d0030691038111810596030f0756821140303a0028035690028189031740311300c007640d080b8001e0444240800002d04562030411110642d07500d0148009800d40049802141818005110350401c0c1084030304103200c0e40b00303411009003080d480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 552099667 1250 552098417 552098419
    0x522091a040e01060501080c0a03020408032808070807030c030b0a0906030b0109090c030f020303070204051602070b040b2a01111b03030609011824030b0106021507051806030411 78
    0x40568541402006118404c1038400507141c03511b954403a110030040300c0d0804070303540041c507900b040041802d9030104054503801e03404024100c900d070704400600c81507441492004041c8075840c03050010068020800c25440b40062400060481d0000e0086000d018121140c0d038010720011004118103560b90400c03415a40907503140d180c544d0366074104c0012103a100d08050f00700c41da2007400b840025540c600c0c188966000030200c0e41051456000113040f01c805403030004985030302501c0707910400c1c0c050000000a00c12080140c0c01c00b03103481405099031043c007100c240c6041c0c02d620b0f00c02e240542074070500380d8020b52000030064024031842086841d40b0054140c0d550b1115038445d0395001c08000304a074801c810140980d9000d0b440d0890402e0f0034920800003008494452200c1074074001c0b41d00f2007405820b0700c10304d0a100c403483c0d4100102844810f0300141c0840d0054800c009102148640494001a03149085c27a500c03414071a049109551000a25034040703000000c1c4400e020306405105c0300144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 552100917 1250 552099667 552099671
    0x206031e01060203040b0702150d020d06050a12030504090e12030108070810020405030a0b0414120322030f0f03140108011a010e0d060b1503040b0a06150522091a04 72
    0x601c034034090365130340114030401c0c542010801c1070000509005d48215510300900f0841801d00440903010707810b0340c0240c0d5284d150603030385800801042c035101e50024000c28090800060075620b03614000c010b0701c41d50242500094980c00030010301442000342c61508c040440090303032256164a034141d1221000e118104607480b45080d42040603945208540c01c80c0c400800078442c5c1419540c90741515617004005a038040035894250004030070501a90440c030700d040b5410740d9240b400800548078a500c88803c3c4041c09024040600040d4110103100d0703038501503040103410701c0240d00c011005024642162540c014101c000092001340540040e41080c0f818290440590017000c011240c2c030005041065124040301859400b00384254003d89204e1000391900243c01050b00c4c0040c0c0c80d80c41690304880ca00070010410180b2034861081802520703000300319025440c2c3c1590300500341c1c003a21041c0049080b9001065492444001141000303152500040c0000024a5841003840101c1d02c5c900b03020b24 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 552102167 1250 552100917 552100919
    0x91f020609071a0a18090c0f0912051e030d09140d08070207120201030b06070b010303091a0306130b150915030f010303050a230d0e010905280206031e01 67
    0x7a074200c0a280302441c500d015080c21002c20040702c030180545c20b106041d83c004600428405001c0c0140d0758210000d0329200f02014040c0300081c29411240c6c084000c030100d0352210b50000d20302107914024040ea011940b042da4111500c00350030f51040000d0180110f260030031000030403022020b500314480b409019140d15010f004400c0d12080b9084885900507007004405008920b4440e4125400c0c9006160009100c103904020807003560100e00c0c240c0750050394000410405901100407009005c1000300345010050005406005000241c070052103040b405000010060700ba0744100e42d403940c010903281510b02c400a0051444e84803820481c016648140440000401402102c5c01490079003d0100c440e840c6440440c0c49802c10b40c001030800c40038504a66481c07085034459603070906154000307555800b10714256412940056500410743e414254a41c010030408103215030b1041011001c5400e19083c0042c1007084140c5002c002d46c041d00220900c05a1810596285242a41c0741c40c030b0700207130b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 552103417 1250 552102167 552102179
    0x606090618090c0215010b1201080307050d0804020105070203150103021507030915030e0303180705180403080627040605090105090604080d0b061b06060f0a0b091f02060907 76
    0x1c044198030010500d04041080107003440e1580300c0040e211843c4191000c071305800100100c28442a400306141a41c041010b800103504104500c0c010403003100198940442550703115203603203141c40708500f0b1080c450300090559018a0444502c81c2c0d0007400e0f00c095045403611000c002c0800c2c00181d000302601ca88650040f11030404607400c160b0161641c2d4200d078540645100186102e800e54800c258035902400b08400c4204080e40c010352980f0080e501d0402d104510030314102c0305502041c850380501e02c0410012900d0f4100c10b82154151512840c16955400416800403d15030a848102c0f0307552180c166a85035825481d00440c8034a2040c000d64072480c0d441400d0300d00c1a980c0441c40d4000030085800038100e240106504a04510081425110381e00000e41540100754034192010004100d400003500c140010f541c403080440d40c200304c100c00000450414040d07801145810800007a40d440d0b141e440c0341001c66003620446d480515507012190003500d40c40d040d0b0ba00e001900c0760310720105203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 552104667 1250 552103417 552103427
    0x51606091505060603330a03030206010614070309180e0f0a0b090a02060912280203151006051b0d090509100501020303070507022403070f0302090a1202130f06060906 73
    0x14440b09102034010340a0f10080c503040c6c40c21429420104001c540045003c1e12207585003401180a900548420361602001034031000707182448400c0d009081000e0340000c2d0700001080b0580c0c044100d010b1822201255107801018601e001000c0d42c4510107552503802c6000400c1070015200c0e03842c82d0380f1504c9905038181da0381b0750180000d5002c0d80520440c141424103e00b4000503040e1901203e4411240c0c909044c98031a854a03062143c004c0e03220000250701b0704100245a020080b1510304a41ca04a03001c0103003079255000b00b908000000401c002d030103400607000c445031100403003070310017241003890301404c2c1c4201d5103c6c0d0703805940e0703420000e0200300d03505108604886040e000746180d6a201c10086800345e0221504a900041020000d4100400006c41c921009110180141d60781410030010f4404018492403c08041c01040841410344500040c001250149041c00c000c40c1c40501c0020200c0c0311488502c01110f1600d900364484081c01e0304000f040350126110501c001d900e42e007003258 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 552105917 1250 552104667 552104671
    0x1110723120303070309021507050a060c080709060e220207020414040809040f020c10090b0108071a07050c1207060306050a1202130209040f060305070f06020706051606091505060603 80
    0x1156003091002414a5000c2c0e001200c0f018401032400708800d041d01214035049d040105d056616038801c1168004100030f034411142c101e00315003809035251034404001010b22200740200c41c100400007010300100d495a07041ca2201d0a9030304200d9041d6803200d004180217400604050b0303c100d0905415007001304151804501071500a800d251900032800248005017280040c0074001550170080f8408032a01070055071020040740b00301041402c070314180800f03c60b5068000e030f1225000340404000c00c8202c00100c560014051145944810726403c007107007400e4000607a290422031010602c90303003090128090081d0743c1c840e2820001d460721003041c405425000c3c010200c80e0742031060724002519000c0c80881c0801e100744005468401c3c45804142a10341404114001d2901d0f01c10606c20000240150409030058410745c1440901d401d42c0203540e503d4612400090040005003071080042070f07540344580c01c1d040181802410038030302c1d01c0c01d032900c0c1800880c4070252600001c10903c0c40c24100b264 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 552107167 1250 552105917 552105949
    0x61011060c1e040b0306040b0603090c15041e03031d090606090d060213031401020909070507140303100602010c1d010e0d060e03032a041401110723 65
    0x40d6541d1207030211455481484601c00d0015800e032110003200c0010700034405070500606098884c01c01c42c051009842d180d11140d8400d00080c81008584c1310002048031a00c44111560200d550b6280300c1084540710703d4100b44e091240e00800103000101050329502141d11903030310300048a04c0040c0c003800c0755040900301c0b58000d0303d08022070550300d4803001a0800040040600003100303001e6031a07a0807a403241044411446180d0810000e000750000440e0300480e03250000c0d850300e803c85000a080c00f00050801c005d01801086c0042800408241c440400c01400112580c0e41481c030b2050010b20f0303052050303000642c01c1c0910640500d00c18022140d2480301c0b603600a1007042101d0055844640d290b055036003181c120306000700071440300e0160824030590b5501540e03480c14000000c0301e8081e4081c4441d681ca010222207118006242002c4404581d070140031400304c02c2c84400121642980c0079201209803240c60f40105e825000d600c0480204c080243c506d441d40c14080d81401201d0480390301e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 552108417 1250 552107167 552107173
    0x1031a04030f110f07060221040e0105090c07083609040602030a0f1d07050a0b2b0518190510020c010b060703020102030108010c0e031902011412061011 67
    0x2e0140c030380102800c1c805481c0850030f8404031404415060714010707050b4810310040c0d00c00600c4082500b04140c40c06100c43d03042c2d650500d80b6081090340f1036008010311032a40914104400200b4100054042e00c5407954086505035580000d9240c2407d41c200703072449038285d116075141850030981d03506000003503035030b010740881d5440d90343d0f44070300b8002c0d00010720000703a070bd84030880994041042d05c10300702103c4c5c00800203804d5400c2350300811b1400d400d90700150b0044403402400c3c4240f04110083d9031451101c030350f01c42450f038900981860b070140b2803696030008506160a01c5524200161100300d05101d00c0103e8900d81880f4141c66140d0b06030707210203003058018000140203060346400500020322650004201107007240e02150241e030069600345d0043c1d50210052001e49028055626404828500104090b903c0030000b070301d510f802211485600441000d510459025210504000009000d0280c0700c0072a0001143c810000711515031040c0a004251031086015200c034418000d240001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 552109667 1250 552108417 552108437
    0x606030c05090105032d0a05071d010803031b0412030305092107030c050c0901170f0d050a03050403120f060e01051801060804080903010617010b030c010e010e040b030a03020601031a0403 82
    0x3101b00c80e03e0f000c1485c0c0c4e000700001c20301021104003048155555032044009001140c0740001d06034003202103610b4a141d0280030300041202c400f00206481d00618a00007511441407200300000640c8038a030f01540210031020655810705030903500507841444a02b040d24440300402c03509101045140c43c1e200fa80700010f011040201c0d105e440f07125100f9203c0c408865a0600040c00150041c000b6886500000d112030003840c02c0740c4080c000301a02552244c0141410203000d2005000c6006505140080558600c00202031502c07580340c1817100640e0241c100545a09104031002400c2640036640941c43e11400001d01c40c10308c0c15040340541440c28140240da42084801c4504140252098514802c1031010311002d030f4083c030030107004100724101d410103042c5800c01c081c2035510550f070f1507109400c4008451040d9030042e51f000781800c402d2070410301d207a0710341c00010000c0170a0b60303d56070035105401d1200e08142c1c0000d003040c140c9004018602c0c07804807107004cc180309001250010f00003003001c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 552110917 1250 552109667 552109693
    0x702030f0c010b040207060b03071a1603051b0c0a0b040315090804080102030f010509060105120c03070302070501060306050f010e040c0612020f0d061404091109220606030c0509010503 81
    0x3001e8028901d480e400440c2e041c26110016003684c01000c1c0c190b0b0416514000c02201e440c1c00c1082c03000920000e000c4100d8041e001c0002c030440e001d50721509401124500401003058407a0041f00c00415000d200b440350120380d071484941c0c034a42801c1d01e42c014002050041381c01c1c000d00c800e80d42180d50101680341e20310001c00921024000b05002200c10607007e100200d26902c00303001842c41080008074a0b4110f40c9800200540940c001e4911030501800300403e0480b503402e510034590003081006026a6078484c02d508400a11903000058555407074100040108085034200901590803036503072030190303600c0f180d110300021000c0c2e80040005c0c103484e804000e40ea0003100c1e641403036407410400605180301c081095000d0b0340060f803541c078034940e1040c00f40040398141906e040b100100362010810790b08613a50f44242e40180701e900030b12500442c070000e61180c00044d00c03142c107000d04400a00050340f0503d841e01c05000030340030840c7e910b14010400719183c1010201e9604869004008202c150f00b818 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 552112167 1250 552110917 552110947
    0x1806040b042d061a0d08032a0307111c020106090f05011d0604090819110111041a190206070908010902010807030b01031b110c0603010503150c041823070203 69
    0x71000000314659a6071880c0c04e652003c04a01c00c15000d95403c80d500d2070f001c3c030060040c4030081d5010503240000c045509002103003106480e03210b040c1d4148460082a0840d85c41d01e003c01110320180c06003417050346080d005a0640044045a0945409022003280c0340c4d02c660a0f15400d00981c0301415812010340009240000300c9900850040d00000302c05209444644640e0b00001c16210b1010740b52042e902210b620441c0c0106c0381000360000c1160111340500041284100d100318a8641c440c81c0c00135851900071800c480030300860181038081c00003026000794850b80b08a40c41004560007500c00218404180915485d4030341c1691865010f42d1288400d400904044000d1410550788421a03400141d1000c0c07d420004c4032a1181041c1e00c5a20086624051203810114041c0350706100400c0b99442c0000c410854040000c60540c0c0e035034400c00000424040d66205600115800b1041c1c507a0384081e034441c000d200b4048008048014031500814580d040507030f000070040c2e00400405128414503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 552113417 1250 552112167 552112181
    0x2030c12060a0e160905060f070213060e0c0a0201020c16080d02060f0a0c05130623250203030c100501050a0603290406090203090d1715091806040b042d06 68
    0x117403c00000b010340310408142e1b07a411143c2041d0f2810b000103070400543c40c11924000c080c1841000511149040c9940d03100c0301c203c0680340f00280b110128084c043d0f107000390103580e01d92110b00111001040d05c0d280c010109201841000c1e494018140c058202c20f2000c1911445074141900c41d00045c0c44000c03039500203006401880c0200030081c0082009141c030030b01c102d00184195a00c40e40144414044035180d03071002240c1c100c5480c0104850041410801c50b41c4140155520311180040514000b09043d48115030752003000d40202407034094000c500d0b9004905a80090b42d102109544442040d01101c809424031072910030041c08000110519611480903c0406070011685039a42d540c5141a030b08107030781d041c2041e040750b0841c0142d103030300c080011f4050f150540030b210f00c1c0c28000e200621042602825600502e8164001141c2c055481c50810301c0008400c00c5502c249801d0412101030b01050700c0403145030360000e400000c07440314440d42c1d8050a200c1500c440e602030507503451078010208 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 552114667 1250 552113417 552113461
    0x9010306030803090105071409030a11030a02090103060509060105010e0603362503080d020a1407140606030606013005010b070c05010302160204180602030c12060a0e 73
    0x31103030003000084030540038500490070100007080c181403100d0080c090091014201082e01c105028914103036600151007126190440642121044d42e2800303e8100009a4000394014030410000801c0010f25400a80300d12440ea007510f4803070b41c0b51001104c0d100f03d8502c1c003a81c810001d20120f841171150141c80603240048440c0908109940d001540c0c4071840e0301030169094203d13080101c24000f4448400c080d08115801c1c60354160b0465488148600030340f4469103c0b039901040700713846140911004828851071807400c50b140c84140c07030500c41075040700104a00b94000e070004500310b42400998540a860141c50340480c0b404100385441c5455207904060035070010003001c141490007070b0320829010740b240c45120707036032040d041c100307180e000d0140d5114504252042003010600404c0c0c58541140b00d50444000c43ca800800303c4658038240f0601c40078181910000600140404000050800d00c9401070034414550300d540c01c0149510300c51092420b14200100000c0495002012030040549 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 552115917 1250 552114667 552114671
    0xb3016030e0d030b0324010b0a020708160302100903080d0902031c110d0503040c0621060e0106090504090c1715070203040501090e071d060418020711011b0206090103 73
    0x6045a807151910b405620980301081d541e010080031410300340981e03144140900002604040351075000300748074105228828180e440424051600751003400724000070729141003140ca81032503203080002003482a100480c8683e10099011420a015200384c004a980007102613090480c00d400780d0b0050291240200da06018404403020044100d4a611710b1046680d0f4a03070706c0e08051442030760310706090100c0c40c206201c001d1003000000703209036002006441e80d528090400c28101d002a40c03100340003c09483c500c6040c4040030070b98a9128040a0480d40141e132680c12a40c3d58009200440780901009842c881c1220f10034010200400c03042c2d00754607501c43c100ca01c101585110300340000b00c19a4100010f80000178104490340c0d0084503000500b03d160030b45071035818131010180071003070745041301404045140004005981e4070026100241030001c43c07041103001c0d0041c0e1400a5210281c100d820989029101032030303510400d01710030b01c000c544802031a403080031303000c100194229040c1141095 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 552117167 1250 552115917 552115931
    0xb10120603020a0e0a0507020615040b0a03060504060506031e03070b06060c0a030302190305160e0a170604140c06160f06180311061e0a06050a0b301603 67
    0x186910301e029004040b0501043c441741040c3e0065425034401030880e41c110751101042c007943c820621000c06e81103204480005002d41c0c854080f07120380301d03a60310140403507160000300814004075400c218400c030001ca0540e240c0c00e49000d02d0300024020049010f12552040c000c8500103100c0c846a2604040003c00711400c2580c0a4007840c601032000303400700c0010f90041a098140b80c184440d0b046c010290317060034803103442c1003640d80080c01c041902280421683c54012421516414114005081c40212890ba298440d41c0203650b140810344d000c071740d00b9010110055202c1808110519070030310040540b03241070803c4406c100c0002d8501e8040e0b40200030075443e007000503c02d1144242d141c0c03948101251a070080d0078044e0000f003d15080ca0000c2d0000002c110b0042d151000246140100d0a603041d8251a440c00c1c01000f0520f6400c4590000e2034928040307400c2c00490098210191a40d00041d0851070344e01034038a07070b440d04040c0003d0b40c0c500321f00451481400c040101d4958542803400061070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 552118417 1250 552117167 552117169
    0x703060b040f0e0a0b0709050618210d080a0203010f0506180913111806040207080c010e0304230109060c03020f340e0a0e1e030d050106030b1012060302 67
    0x2260341d84a240460b901513145081040700b104c0600358891040d05017140c1461900f0702183c0d441c1704600d10100122703900107503034415a0702c04045072010400c010f6503008440f01c0c1000c15681e00d04116103040800c41490004414040358001c49059070340d8003034111007043c6810b041c0b12b06504111b0103820481c01c00d482d404013903203c50b081140300302c010010400d00641c0500300740e0070628103201610f01548000c010764900340a6134445581001d000d90300166258102e04040344c003800f070600045515401c001109003001c5000025206a61a0300c0f040700ca824464011607807014060081c81d404100c0c80340007000b00d60f0082c2c2013119810f0003801034031a41300000c10341c54201b560714252410100004440f0413880707402c8181020221240c50081c0a485041c00080c0d9005580200751007591516503801400c080c1050200c651496050000c00e180509050861602c903000003802441d12032806000083c00d030311034000d0350422400601517080c0401001001c5981000b003490710082d003500c42c1000801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 552119667 1250 552118417 552118421
    0x7030f02030f03161b20130e03180612040308060109030501021605100c12050402060909070e1903030e0d1b080106050a27270b070f0906020703060b040f 67
    0x304515203041301204464041002e0080441c5e54280400903e4650b0004001507090382c10304a01618504d0803110400600000b500d0007204031107296209081102482000c140040a0403100e0030034110a264152144140300740d81c0510030240c40300c0101800802e011074011001150030803c1031601ca0304443e00c03500d580342640c1c030480d18a510212111000e10a11005202d1842000209070041c81402809080101008001510f5100440d0750304042811175a41034200c4110300c40c080c02842c1c0b540352002014040480c902011809141c4500d0907610714180c080220b000d480d40340d10b60000d00300c900c1c014040350211008040b211411112070018a5400c02a2910014140340c400410800e0400c0c09010324610355512420300b0b080c890b040c1d245a4004c504150b0b440844a900008485a0364210001510038540d00700b040800750b4001c19003031003c03400001e8801e00e0652154104421903210854401809100e160010f0304805018800035440350061588540000e00c0485e0a80382300400b103007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 552120917 1250 552119667 552119671
    0x5011d1504060b0a0e1005040204320306070c0c0f05061c060302040515150c030f0a02120a0c060b030f030a120b03060f011a0a0914032509060e04020607030f02030f03 73
    0x2e045d0380c2080002426540102501908080c1c6055091a10b085c4080300c0214004161a84030341c104155070341c450034907141905d0070050007400c49140b42040040a050002200002d94400e000d00740085408c0c80004c5050085410161215251050448000400f003100c1108801600d840b0000040541d82301d0003503d0042c0b42d0841010b0b4900c2c041020003595240c034188800301c90605010782000d200c0c0c0401903460b1194200c040d1907803061507240072414005d101071980c51082010541d103036202c1c0c0c4840898103403407160b04100620202d2904041d900c100c1c840028030981c2c000c21800306000c2c0305403420311002c1c0350703c44041180c040c114000390620404039251529001e903440100440700500310300301c011031840840c0c54600300140c107008101103403a015003082116a4080034a00b503d0401400b81d0070704a000301c04844c920350003020710790700200e03210f03e4801c40e08242001c6a14030344103038550b003d10b038028800c920304011650141c2d092000c000491055000620200040ca403032580214 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 552122167 1250 552120917 552120929
    0x70f050c1002091827030c010f0219050304020a06050c07030203060a14010e07050406230a020a170f070633061805091801110a02030705011d1504060b0a 67
    0x961100d003d0703001e000d00c00c1608120704988240036014002042c5040880c4a01c440904040307100390007202911038a14495201e80401540c6001400e0107141c0e85603005e40a11240c03025030310002e0041142c202c42c40c0c081035030065840110207004028050142c0c0091500c0c0c11110169508150340b82c000a0514004507101c1e0720440e03d42c200c44071b8114008800e10b001d04803c0042d80d80c5401c003045d0080a90265015110610198070000b5280f80c0b880c0f0341000244600d4944a0340d601b00701140292035401040c4101c0b050b0a034144802c03580e00050301940d01000200207000d0808006481e00005003400b590100c001a48207000c0300b8007007180602d140e02001003044118002072810301c005040c8022251888900342080c00188182c3d9100b9a00d960062241c5038880301e0211004c0030300340140100e070b48403100d001d400122070f0340458010028010650091008105580c0c044180301c451745100c2001c01602c0d00140ea1b40d844c0c4d5a19072108a82140c000d42c80051580590b42c00b2038a680c460390006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 552123417 1250 552122167 552122171
    0xe03040303080a06050402070c0e0c0d0c120510081b0f1c0b1e040201051305030d0f09150504031205160f140a08030a11120406020c0d020a020306070f050c10 69
    0x20364040f00340252801443c00361800c40c9800d9054880000020260060301034001c040000f2650002d4003006580d0900b41880d41003042c11440700014001e10f41032455100c03041d0900c0001003160141d4000d91044600d29030180c240d28216199034911141c1842d105130740444800300740003240e00c1707250b44049200031010b8040301210517420325141d0400000c1c90710710f0345245004500485085010815041030707080c00c000c0e803511041444800290840d030442d681500c20f003964180a10b5001d20010a01c030103039100c91600302d4994820b80500800c0c641c0c0040480d80810003007002540504265440c0c0d0b5161804509242a0f2a10009682c0c0880d0b42620002803000c0b02009102c5540002c8070062251402803444000e0390317480c001140002001c464035540d880c800300c00300741c2c640780c211000300740c00c5a5001003500d824076000002790001e00c1100b03858030805030420580e9000003040500c85400400400060b40ea040c800c94160010040000820205001c0381c0c0400204002c0002c4003100c4102c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 552124667 1250 552123417 552123421
    0x241e090c0c1703070f030e0a0203010519140f0106050a091809200a14040603060e0d02010b1203030f180a0501091709060f0708070c0602160b03190905010e0304030308 73
    0x201c4405103040d070050030b4010040041c00031550300590382e07458501d46410086034a0110802c00c0d8100b403208100a501542880308100b90013403c003208210700c068503503003000050000788403101050303c210368202505180720b006200c3c080c082c801421901406c0d01e0000041c503100c61410408407800da0040c549142c85149050400514019240d0030304044031410440b1410080001d0f10400d0510a0388c1c5c000d001622040510385540d000f800246401000900c500d8840304111907864489408401c010b518100c00034010349018014090080841c2c00150b08544900d000e0f1030f100f010240894450385044a15464100300a0040032107040c050300000520701450b05200030303918104e641600049400f0042c05800f0345d980c60549400c801207103003403a02e600951070241401c0c4202d1001821a8030048000a4141e5000803140e1081c200034260038a030035561582d84070540815603070011408401001c0d480324088075400a980d0794002ca0010076940020501c484c11907002c4d4106400003886074007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 552125917 1250 552124667 552124673
    0x20a0b070209071e200703031e03060b0d0c0c0b070203070b0c1c0e0102120c0c0d0203031e1906090c020c0d0503091012020418241e090c0c 61
    0x102c190341c0540ca5041030310405084003205180d0a60792000d030000e124140100300060f40007032440c00d4400d88944211060f041e141e080180414544009804040101070f03a2425902d101c1d001c2c601c1200c03501d2407d02d040c040f41002400260844004010400981c06101c10100d40800c281d280107001c2078001d140c0e02c92031030504480c0e25400030b1458403040c404109010390b01c0d4a0000444040b1013502c8005030300c50501c12003502a10800221605005002c4188290101014001e01442e940802100c01030740c0d6030101641c90f40004c4411290f4400e03001c40c00410034800a1a00d0f900044030541c0143c080008542081194041e40000c00819a00c07425a80c640d901000340240341c41c0e0450366505080e241d40d42e01c0b03941e0300c40c1c041518010400d0400081031117008011044091002003c25501c5645030340030b1171801004170303054038601c6003048031010031401070001c0d051061582003601c2d1401d50524100c200e83c0c164003498196082119103000410740c0b11481089650040c07544c400c12480f010381 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 552127167 1250 552125917 552125929
    0x9090308060103110d020a27050102060a0519020a0509030d0201150b0c071a0c0f160e10030b0c0702030109050105010609150801090c111c081f0e090703020a0b0702 72
    0xc01d558141450040a5500c0108070360689808101d90314025036280c010034000c9800042030030f025856460007200c10130b00d4407c15000101550f40c203070300310b907103980e0b40d04142c0d003c1e0343c3c051301c0140084d1000b4140381c01182040e00240b01089140c180b141c41c218441c804207142c00c070400100da0050b55500040c036003500c10340020301e004041c0c015595081c288490006a1245071500c561101c0c08803080401ea40e007260700040e07a06040c41391068071080b142d9640c0003070b150750103d0b02c0600702c80320007a400302d5941000000c5030b0107401c9031043c1c0184c11f41155645040e128001d80701c00f621840c1404a4001641c007405560f0f01c075440b80001140701c3d4501033028110b80c14980040f02d15078240c1d031810782c10036031007940d070750440b400c9840200c0d88041000302a40c0350340c0381842540c1c10b8080d42d4010402c0100c41e00440440110307690b960601c2da610302d4545400c4020040c003d5042015040d010802400407031525608021b528040d0f42c0d181d552a80041c8078501664462080810b0105180065103002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 552128417 1250 552127167 552127171
    0x31b12040605030a02070311070b03040302010b0d08180102010f0603060207120302090603070e0a030b090d02070b040b040302040b040204080a0b0f0a02041d1312051b0c01210e03030109090308 84
    0x1050045041a04041000d405800f004254966a41d40071903882c0a040c410840c0c2d0f4081c106090a64400710340b00c5100044a5000312001e034050360070840550024141001c83c030301c00c40e030404015410201049a2905500c0085800360304542d00c0d00e072480a08501031281d00000d51150000594a45403482c001007100b500ca1030030700500d4414800d066080c0c880c1401c507a4802c015203401c1200c088000e0000300003883e15000900541004410000350540004050000300f115408076060703980d950040c0703421403185000344034180200344420801410590021402e8010052001d401d10341c0328826103160040400e407e840818100d01441b0718a00705501051304500704030303c203510f0301c5d0a140201d4011f0b1009443e03015010408400078051500345000c0c4000c45502400c4400e001d520004001c0c082c0d04035000540e02c184009414200e162000100c5803141c20043e1541c2801c50504844440c00200122001019688031045045040c2041c030045000e040316840004496049040013040d410300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 552129667 1250 552128417 552128443
    0x2060a06030b06360708100503030a030c0201020c12070308010e0903040e0a1b020106150309200a090204081509060709030b090129030607020303101412031b 69
    0x80c194091020842410055520070000d503100340e842c0c04224200d200b01900c001e0482120012040b0300c011581c104404540100081d544402e050b0301c40d000f00442584551240551542c4200403c0005038000d03040a607100095000050070102c1c003a41107810060a030220017a40e840008900e02016000f01d006030150104c0301d1504c3c618508940c0a954070b10650250400354500d10780090f0119440d50440c10b580c0c004a42c00000c140f0041c00085e000c0d200c58003800702c505143c604142d10a500c207108030740c0361681000c6210940c0002e0010a00c11001044049d50030425205020603c15807a0004000600e40c0c0750040c60055150320b180a0710680180c5551b14a8002c0011b11405a60226501e001e90350004400c0340c1030303114001d40302d0051045410703021000320600310850310035540a41c12405210f0540070303074580da610440100e84900c4100d0340180c040c1034081c0244100740c906442c031445000041c1c035082120303100d45503503807454001005161000324040c181440f9220184a481d4503d58 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 552130917 1250 552129667 552129671
    0x1f0f0f08120408030f0d1d0607020c0103020a0e04090309080601141e180705041d01050907021c0509042c0106051f0311040506070b180a03080c07050c1f02060a 70
    0x20900c4602e5403070384200c440c071480c0c0c2c5c807002c1180c016070038640e4400c0003100c8a1040c140b0b1001c000c00c04051300d0342c0c0111080e60141c01a06040c42031035002c0d00846d200c441700c80c0d40782c42d0080e8040c0100001021030050a0f01081031500010495080400c051400b0b050f01ca2144080800c43c81d013002056031140c1c0118065140c0100d0003a495160300402a000074002507409a503980c41000c11a024042e5601c1000d042160001c1000e003610a40c0c041416030300266042146590f07400002c1e40d07511400c00b034100080060302c0ca00d80740184648094006900d00510105142600d1a580c55845040e8803408038034208005d00d2144500f024030828005180c10303185054602030304000102c011003900302420078107850b00000d500250101080750060a0003d00c42030301c1d00014108540000822200c124240e111441e1401c00703c1c00006460f140f03a5450380e074081181e034903113004483d181c000d0041101d10740700d601901d035010350b290180607061408003880302410034140071f00280f5159001e0284410740d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 552132167 1250 552130917 552130919
    0x13030f0311070f230103240906050402090a3b01140a0b090f030111071101091403070b1b01140910050f04020d170a0e0a090e061f0f0f081204 62
    0x1c03082c507a40102c1158041c4d4042c40428a01c0058000e003540c4a0400c0e54041100740c45400f0008561610054849800c810400e56858805020481c411805030541c40940c2d040100301d15060044420040b808101542c00214090060f4842d588400015941c9408c503980042c0309065a521007903030019000c44440c0600351800c4000b0710b15201d50358001e17016207003e031420040e588094000300107403100400425900c1e500ba04003c0c00c010a02550f0780d002500d030142c0050350a07190515510748640040c00780a40a2400b400000c155100381300c2c1444628400c80344030720200003032080481146200b00141c1ca1840c05080c5075040c40000110401c940380707400180201c0c00444800075a10175410390b4502c0d45030240303040c40300e0300500c1249444012403000a46203101035018880c09041c8509403210194241c8a4640b002a6647c010124105a205a0014280403d0720003858190950b0a0004002079160148240342d402c540e04070380c6072068080401c11604d02c0c01c20825460301d180141d000e00345 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 552133417 1250 552132167 552132179
    0x80717120901091a1e010807090b031605010c150c020a050105060d050c06210702240115080c0904020c0c09010509071205090118030f030e03180613030f0311070f 71
    0x4441c000c200900a00343c00043c0045010314040b00c5d2075803019942044541c0c2d01c0750680e60752490381c001c200450b41482c0050030241000104201c1400c01e01082401650504004555a40711380c281a52940b0403418400d440b0a4944103040b030a09060340545800021820641c1c00e480018110758040d41041c0041c1000c070f800410114a105012505240c2d03e0651000221400d202a100f0b505001d0139007040c4a107141e000038610100d142081c0b0280500d0141403690703005c0030310911440c12062141c541084869115401055022404800302c2d07040000c80e00c0810120b800007181d003003030740d40003040c480c0c0c0d980f0f0b01540242c010030303044a0311000c52030021002042c2a14441c0800d20040d00d50b0701003100a034003900503401001e5020b8042d4918121070400a00740b1001907155130210780b8014001c00c00b0a80842201d101e88001001c0c0004d1403003802c18424642c0c020048a00001040f010120001d0740c001c8014020038000e82c0ca1110360340c16603400c10304181140d8481014040030003410411 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 552134667 1250 552133417 552133433
    0x905210406050d090209130302071a0a030207140f0106050f060f12131707031106060f1905130b03060c031603090203190309080c1c020d08071712090109 67
    0x681d115403801503140c4001e000800d0282006000095200c1904810000c03425a041c50502001d03000e03900b26428555118480103040241442d41c020004d020000c00112038044d8001705502803240340640740401c0400b585a0070b01403460702030750300c59449100400581c038000740b07000740308002140c1d0145403100040e2816404d2040e08804161b404400c40000c83e40c00100f039002103440d82010b0140c020800d500364080c115842600e04134040f41c0758061000c100344000502c075104100c0500034149403802e0710100592010084c5640500c50718403000491141c0f6124407006002001c00d0380440c594064134200f40c1041c40c020250315034208240104409030300c3c03c100d031000d2250b00b0301b00012810514000f107070410b6102507240c50701940101d804400c25500c004c21200b1203107900c0c141c40c1c21540700020484030f9058401d500c1c8202440c80c1d1020301616055006140300391185404c589400c445a40e6046260040c20f40180d1280d4085940005c2c07010462249030311220207002040440d0311036031200c0c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 552135917 1250 552134667 552134669
    0xf0a060f061a091014032505091e0a1a07030306061d060f0408011d1006030302120309070503060a0b0a05010e011d030309041103041103030403080301090e070510020109052104 77
    0x482560136044444185000b84140030780a003000400c10b60360b1030701842400c5011100405201200803000c010340c4a07610075401d450700d01c0c0008202c89050344280d200c000742c111003d2240c030743c000315a001c00601c0020410085800e0200341d00c00e1130f00ca13812400e01400300d0b45036034440c42c1803194050f243e020045c3c0912034124119022248035481d11002d10400343c1c85d02658205890f9076103000c2e00c21180150381d8400a4104212404840680d2803c8002d40c0913107d0070700c0700030b0250340300c0103607001e500b801030010b1580007085104403600c07255103a00103480d00f9004d0300c0020b401c0c3c0d952442c01c05139080095440b40a0a02030901610a00034440020b0441d40e0405544625040b81d4405e2200f5a80500440c4c056860091080c06034031140c200034021948151421190000608032040071030170040f00b5182203d0b0000d480750300710781c80c0c01c01726000b4109002c2a005280600000802d403951050514079076140c0b40d80c00080c84501e07900e0458a0302c11144000c3c81078000c0e01002d052000b12850480d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 552137167 1250 552135917 552135919
    0x1b0311270a0507050f0d021206030106061202161b180c09050607022436090a110310031401090215070606030c030501050f0c1809090f0a060f061a09 65
    0x3950f0341d120f0608440a00a82e0001000c0c0d07440000e00d00440592a0058603108496181d01d5031152103010801d07003240d00a04c5140702003405000c01000f9084035501800d40408084d0300034210044a66519103244151090364001c030607440da00740000407440320390078020301e5698000c0000d041002c40250021605104441c821000000c0c002c4c1152100c1d109a06840c003400b005118030201c40c0d800d802544c00007100c043c64142c07650303494803400c0c031004102140801c0c000d44190600300514144154808010107014242d074030b07451080e1031614401f00552262107aa10304154250852802e1000038060400c1c904450303040500c03881c0941e81e010308814070b030f03c401d01c580c5a44140070320f401d01c090038090340040c01012000b04008140f01301908618440c40700c0d044582c42030356030300410000c940100041d0080ee08080e128020541c10f00010144d04089181c0488100c2004410924544080008101c1e0080d484141161440d40c007400b07110060000800007481c10703140c0c0d40c800c000b5405120001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 552138417 1250 552137167 552137171
    0x20d0903110904020324010510090b0f0304050a0b0405030702040b01020606220b1f09060c0f02041a0603041a060d03121a030312010e0606251b0311270a 67
    0x200b0f003156030401840c00d1040108100b51040b00c120082810482801d1042d00d0040c080c11a50440261081c01010706032201c000d18a400c021148c581d40c0c4031070304018170480d410320070603c02d0b1001c24030400c000d0b880782d0700c04c40086035602011301c1800b00341c2d1a4121844c3c1558402001c1c04240e503100240702c0102c200720a0260b182840b603600180244c0136a00e000c0c0d400c03e80d0852101440007054800c9020402292144183c80d55649412210756a8500b405000854046180801460b16401044450002c88902c55401401000045082d84103440c00c40d5040b48198008030030760b130301c80201c0743e014500704d403000001c10954030040c1012090302c2112503040d503611000d10b01e2114009440c9036040b006002c40340c0714000307034800a803000000c0c001e00054081c00070000d10310340383c05401c85090000c0c06880051031503406070610840d001d9507800b2501000300c02e010015001682c070702800207602894604c2c25420032101804032502c0d01501c04032000c0c083c41d80d248004035508480750380191f044000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 552139667 1250 552138417 552138421
    0x1b020a0b09031306020708060c0f041202040906020a170105011d090421050d060506090a152003130503010b012f07090246030605031507020d09031109 66
    0x1100d8190703c00c100d48866030580c104008550b05500140210175251401e08498885c0c40e082c10644440c0100901714454040401041c0304140e1f501c0701c00e00400c0d102034070100e00006180da4030030030b03a04410500c0001a07264858425000c6000e4113540c0140000e0130800342008a000c0a00d90001540002c0c1d03000d05a0900401c0030442803034080d0512003456852304410a58150004003142c0c405c06003119041e0600300045120710701130302200ca00f42001000c6c1584103207480511151010300f0480741090084904d1a0180200c0e6050400a9110010059981ca10642c05001003290350350704194001d80c03401c0011200e41c0d0b00b03c030b600c8100340e404224040d6103040c10ba0103210350603c18200c4e603002e40540c00e0005884030280d001b81c14503210380790101300d041c8030550300c10242000032400028a0018403050300210a400c00c40c2030015111454003280468036170012a242450501c075845000502c0e0040182c1a50f06201a0b005910903180a08007940303543c40d501c0100002040ea14070485800380 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 552140917 1250 552139667 552139681
    0x302100c1b0602010b031606050909041e050c030115030f02040213150806011b050d0806041112070306061404090b21011b11060109020706110c0703061b020a0b 70
    0x1c9009000801d10110840161681002400b03044250034050107840f0354482218003180c0f4007041015214140e680e1030521a44004100080001800940c0c3d2a47c04580c0e98100e000c5081940c81c0c494010001480d2180030b80051600719555680340c000071081080c028800920784070003101800da012600983c235882440681104103040750302c00c14501c003c9520100c201500401124131a8000340c071000c94000320f54425849458141200805c542c010100c1e02c00054000c2c150f041d0402c03000351000804802900f01605c1c030341e0001c0b14271080c140d409003c2220540c1d050040c0381c040c4c0030138602030420b04205240400d440c01140140b503403254a032000d10546441d003c801a0801d100000f5091004d8200a100d034000c00800f0301030342c2c48250054000100901420680c441600c810300100402e03841c00603c1f00094008840c1141d8854590030810b058102d10006048010300da800900100c503e0349c41c1107401c841c8980340010125103036075442d007469500071410101c880c5d0080030003000340e0f507426 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 552142167 1250 552140917 552140933
    0x3020304051804060f05040b190e0d0302030f220308090a020622210303091b1805091209010503070903020a09020901180305190615090b0414010302100c 67
    0x382200b038020040402d414030140c658011180140c0c00707464208802c004201d0070700c0c10341d40204ea015110180a6005c178080300e0f10382d0502c07400902100030000c1c040114461407421304159003d8000041e03004014080c404a04a140c2c40c1c20400c0400351a11a0802c4807030b03001c445020312009000e1004039000960742000074451074a44540c000e00b200d545108200710295000d00c1070a49030f0300c0204480010071881d481d40c5110f010060034038094840d00c580c4c0d540440140c2070300e120445070b030354802d0070401d00d00c4030b04140200a413000100410240380070850203411214000c101c4451540a0003180424904400441e0800b403401c0c40d009a43c0e03614294141c0317402980d944004c1d088141e040703000072520250340c06001e04c2c1d40300741c0c1e070841c1e5000394000f9410348049a00029010780c00140000102c00e5841c4410b1025a21640000c20180340c0e80c0d9101140c0202c942c00391100036201d04071001c2d58507040c481c041d200000300b500c2803013550443e00410300341e0340d645002c5014040c00c5024141440118 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 552143417 1250 552142167 552142169
    0x11e02030c01020f04151701090903050c0a060b03060705091f0c02130506010e0d171b102307090509100f03050706170c03040b06060d05101e050f040903020304 70
    0x1600940d40c502d040013007070400d9440307445851080c1d80079060400b4554400d0120040d800c1d20031440c0c140c2c80c2d090203d01c0008010a850890511104000d42105d2100a006415081d03001c0d443c00140e80a50740d05050600c03400916070302c100401000844001d0341d40c10400300c1c0600e2072500712008011240001d45481d8080d80300658015407009041040075455002a44104400ea803444200d400031014415036000f04040201030805414840b503910252030003400c0607a001412a4403034681c0c0d918180c0c20013100c44080c0100d141c1b01c1c5401001c00460310001060b0303003110301d150460b500d04098010818581805078504c2400f07058045500c1c1c01c51400740d00f02900c3d1b460049462141d41e840e0807540c40c089031180e14042212042c0480c00721002c140d01c9446101304480407459550349640d584038a01e8006d0480d54094400c1c0180f0030f5080292042600c00c0e4415034250209900b44260181c401c81151442500006411410300c4551105c601d102c821240944020134604200d140c01c0c3c0c11030040d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 552144667 1250 552143417 552143437
    0x7081b01031d0f0d020c0d0803070c0f110301180206030414070f08010203100f08030307030c17010303030902040b06030601020c0d260a0f0302040e01052101020324040b011e0203 78
    0x10501000b101c880000c1524030030b10b80000e00b10b4901500030ba0090740ca41d60f40c02e10466002c9440c0503444089021507005542c441c0e1a45800c15807444140d44003401d0507007140f41502d070b03003c51415030039032820248140c000d140049031501540c007401da800030740941700c0204014060319040320540e101047c10080000608485001c540c0490f88440c6024000d400480b900c0441200c01d000010b141d400180e00503081e180004e0141d843d69582040541c00b50040c00c0c49501005003003420702d00540281c00104d400385101c2c0c0d5011030341c031500380104070503100c100304580c0c482c080820a020140ea0000307200202d5101c10b0310803412003030032402c2c940d010050001c950070f4022035500c508098004003000502c0e0381d030a0361b00d03841402d07010040304400702c0c0518000d50b0342c40d50005005100516280c0d0b111285881d5440c41045228503001c84142a45c02c1a0352020004c3c841820410342a001d101d4880140c803800d40e401c20441b24041c0000305008034807607501d214440d540200c960345c24401c0c0126049058 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 552145917 1250 552144667 552144701
    0x60703030e03180f06040b1b030d020d0c02010b010e0303031b0d02161502120f13140c0a0803090904030302090a030b010e070801090e06040611040315060f050307081b0103 75
    0xc0ca80001d0f1100840c40d00302e11a0881e210f013604240303050800e50701074401e44000c40d801c040180c1a1443c62004c60880c0c5030340c1e031000307210704204e00789580020604280b451902140c90158280080d09441c18045828140204c500c1080b016440010035282d0080084160112400d119048039600d403103060580c06c1d40303e000241072003101030516203200b0210302c1002d070520a01c180c44003d008030701410400b2a0040b20b0200803428030144020110f41060030b000307580961002c2591a000140b0880610404c01e40200c0400c10b081e28108034400700400c2624081e614181c0302c4000500c004400030030007424554041022005500e03005106006141c0c00322690010b07586510980c80c5048045440a0000b1a000004140b0803000c4c003131401d18000315801000d60361656641c800180901489405008600f031000102137034020b445040c406907030003000144141007510b5502c048145400c082d00a91001c5020416420005039000c0410010300c0e00c20f030400140e000403005800d948a01504e030318 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 552147167 1250 552145917 552145927
    0x60a0b040b030103020f090403080f0606040b0705150a09020a030f110d0515070c110f0411120604060909080d09060f021207020106090c020d0810170d090509040b06060703030e03 78
    0x980c0e000210305132402250000c1c15a0812400c220b0081c4085074002c0001700010042410b50060200b0030340c10402c01442581090b4031001e0f00c03c440e40218900b0741c4c95500400e4140b01c0d070724035410080d8004c420084203200c01704032a000725501d1110340c40014684c0419245007000d215000395400840c01d00180003505820f26820895950020150b0b6100c0540300413000c00c0c03103540109076a00c0280d50003102c040c0c10a03801c1007000303804402603440941254640440c00a03134005c2400030100180c034584a0700f041d08011061108660442d00042c1d0b603549818010310202d005d00c1c3c1a210702d4095901c000c200e8001c1468550050310f0f40401c0410074070300118401301c826084041082c462045e6600800c22155107a450b1400c2e40c4010785130b8000358001c032020080b0184200c00855211584034001e1450950315007000c02c0c0315503031440c450390300c0d0802004007240c5a8800d90500040078221181a00ca04090311250b0445402802882c0704000001e910720405010345c11840401c914202620341f41e0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 552148417 1250 552147167 552147179
    0x15030c19080a141608060111010204080703050705240d140a0b041b0e04090519050307020901091a010c0317040c142d0a0b0c0d140c1203060a0b04 64
    0x1c00c1d189019034504285055071101c294030416441540410100c1940110000040d54071130300280500d8108280600344101c08a07090004200130090700f00106441861820424281009a00318a1017038a0381c4900c5e0500106103812004185203054070369030340700030706005c1c5401014002020303e040b20940040200c4801143d01490400106640501404002148402209500d803200e02c021a0f01942d10302c03105d04081d40503450440c4a10110303900c070040450540c009105164023100c0d551720008440003142041e400103401007084900c01e010700d4142c00b0030b07506968030b43d000160410142c00c2c0000f061611509600110406031250754417941080d041c22152030810b8090325180e05900c4213860002d00b0316491040c6511400044e15100602400707030360000508142403103602c4070a024001c41c80b200340310024900d1411041c014103803000642006002d03403d80c0005014050803c0c40000e0031003002181400c2030008020f9015a02d036107904c0059203110582d08000c00c1d0707070800315001c600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 552149667 1250 552148417 552148427
    0x312010305030a080c070209040b13020a0e04140f061f03081204050c0102161406071401050a050a060312140d0f020c07050a060c0b06010203070b04061a090615030c19 73
    0x28280e968a6580aa0f0768500101741840391100c000e401808040c0060046074030001d000e5084440d82c0006200c418041d00002c0a0110f150049030741d8401c400240070412500f0902e4036443c245041c06401c10b1107039000d0464403144010301482207451401d80c0d1003003109050910724083c5621108107500d072002a0341169014108490171101d510844903802080d43c0000358000f000c4100d071040624203030500007444510f902840c90180c000304180840c600180f04141c0002000e03c40d0000001c0d40c0c91300d103008400383c0f10003800e142d405620741242840130609058504201120780d0a002c0e07540304074080031a80c03500c200356115191500d42649455580c05540081541c0e4071100111071005071074004120b180d566a00c2020085086948504001104081c00c01d41c40001401541c2c10303d0714a0f107030140c1e24401248c2c00c4441c9039881d004111904095444512143c400f03652100c0145444000708500b901484040f60000388044009600038600c082100c203545041d408952180ca00c0b1200504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 552150917 1250 552149667 552149677
    0xc12010611100e0714030f0a120e0d080403020105210106020a020406090b1f05040b0f030105090901090b06132003070807020d0912060906091b0602010e031b031201030503 75
    0x4442c2c00340c403040c0c540c900c030a030169103c0341c420180a01429031070908040120583d040801b60140a01c02400d80303d20024031a440b00c1500481420106015034034004025186080045201c0c0d40800c0892012451103400e032000d6940c20700780300c1c0d5034403440e0800c0b0789081384030001042e00d104041d002003a0660301166000181d84259010301c001511011030340700b45d6074840c0303e403508480d03140300e485074030b050760740c05403110034141d09119207040d03120035404600d68003240c000c440001d00080100440d04100c81d03c03561000041d0020002c00640b6a98148030307480143c0401c0c400c00d004c1c20042515911a40512031080001074041c01444440302103103450f030000c4814602003000c1b000003400a5001186c1a204031002c4e5948070720071070800d41c51000e00000c0e204103642c440ea46456400008116204449043d40030f2660084545480c1f020500c600307400d90031039001c43e41000c1e110700c000c4a00200750b41001c0090f140c114445201c0c0804140307180510045100340c514800300000a104004c03000300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 552152167 1250 552150917 552150947
    0x30a050a090507032303070203061612020409020702101b151d060a1b080103060c141809010f0b0711010302160c06031b021b0f040c09080114010308070b0c120106 71
    0x1880311781042c88401d41302e0013203101c044d4168007c940002c54009505003051050030050405601e01607405031a401260001e412920556500044007800c1d03141122180c90448020325007400100090070b05000c94120101c4001c0c08110b6072810910500b4850f0881c12640010180908028100020b0740d940c401c0c0a8800b4159246004520341d0071145280300c1c50b0070b120f21510b600b40103902c0c44c0d94500007009000e0082c000c000c0d02c4907052812017403850003003403402d50107515041078540e4801004130142060344003000d4000e0880e002c0241e501102c0607038000b00d4004c481c10744004101801070700640b05040e10400d08089042012003040101d0403200c040e501203075000c01c180100d1501d90000255191200d00c0941d00150390010303911240d007803d921081c0b0191101050000c40000304054811040c50413001c114520400d0041031070034480c00524071010300254a03039500d16116401184200381000e40151605030010346114110800c980c42c004401049000f15a5641001042004a03100403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 552153417 1250 552152167 552152213
    0x1b0a021f020901050f0a0207050d14010e06160c052103040b070905010806040b04064205090114090603100528151b1101021c0203030a050a09050703 65
    0x49444400c180c401e694506106840322441c1507030420000c0401d0b0001007040c4110b202e07494010455444203041c1580d01d900c10341c5e100350b50b0a0b040f81c03983c0c203460740010b81c3c01060348034808100100030954869220442907041c144160303025401d0a43c03d1140843d1445080801cbc0d40022003072600c044021340c42140140300c2c00111392611003040f00c0c8590140318180c006070914002c074200389020390002c40c4400d40100000390140e9680001040c14600491030403000340c052010300c0c02200c00c803060f800e075132100c820803078034030351000b00013810318090103010798108000e4502c6086c0540c000e0f4201c80c04100c0062003580c50f4035100502d01501c035542d00034103000300c900c207481d0303030031522454254080803060203c940d02990804141c2c03030720240c150381440c041015141c070104040c078030240c004403000d0083d02401009003241002a14003080d4110100e20040f9800003041c4a41e40441601d4201100920100302512203ca010015024884000c0e1550284950000c1080440410143d641d0020b000c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 552154667 1250 552153417 552153463
    0x70315090203070e061f080610140f0c0f01110703090602011406060d06090920063a0c0f02070b0c030f070203160909150c171b0a02 58
    0x800203903558950000e4041e4002001404800c10003140c070b80d48103001400c00c200d4000110300c192130480810306a80301040300481030103464148914802c0e580b101034240304044030800c2646411512518038035000110010440303400044d0305021042c05103100c14000c3c40303189030403070380c6024551001400700d01080042c0e00008081d801805103041000f61559074000c16038440d81031015941c40b044640120315035446021814041a1045191090203001c2c46c1200c440c2003039180d403849102070a814481c03402406828842d0300829020b41745090b80c0c1daa001840e07000d865007030040e00d00d0b06001c44a62800c01c40303683c00250b40450110300240c05e0741e00300d5081a6a40030709141620030381045400306d800c10420644014510300080001038800b4003241d15081c15140c99030b44241468114038891034a60781100c06201e103030302c400b000b10300d8016001c0081d505500f1016120070440484900c0d03a00403d400542d5282c0c1d038090106032042900381c65a501c50702014002e46030803088280c040c1512004a03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 552155917 1250 552154667 552154703
    0x80d0c09050603040609020f030a0c030b071e0c03170106050c010501060e030309041113030c06030b09060f010305061f030b090a060302061218011a01080a0c0e06070203150106020703 80
    0x8000101d0310058140c0345141c803141c5581d07003d040070b008281e8200038034224540068400704180c01050f8040c00300c10030028110700d0000c14a140240040042010b10610092000341c65100d5046041c0c0504041151410628055480c4505107107030141d06007040000091840d085801050b1146002e4000c0285c0c0c0e8a40c101a00da2840c10703c031113601a41f05000f0305010b402d00d42c0c0100110b010403000c1e6420191b2140d08031060340c0c041d8008a5510703800c81010012035030107008100b2041d5080768280c64500d0120b02003071071054900c2c4024101a2a02c0100d04180c484095403040e0200c066030243c1c0d400034101026020340b0043c11420300507a040d00c0080c500600e02e00c103c2d010303603500401c00b40c54035a18480d60850400040e00715910424080180503a0101c00d2040409503200207508640c807aa00070005895580d004040301d10327103401c000c000041d82e907001421200650b8109d40700c03500d82086002180c43c01c40c49804100c44407a0070000490304940000c0c108007201d1140c40d07903402041d20300d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 552157167 1250 552155917 552155927
    0x9020306010e0a0821090301020307020f16061403070e120d0f02150708100b042c09070501210212090c0316060c031e0807080108030c06130c0f03080d0c 67
    0x2100e071303000540203911420402e41c1055074481d686840950b10390700701150000040d003268010fa810fa0050b80c400365404038002c10a10a9440103c80440c000b54142d141c0304014083d4403c1e21081c8280c288000002055203000e40300c031741c9000b03002410740b400c3c0d084003440c825a540b44041e14031000c1003c0b000040e40035807000030a8007189044e1551110162291502038600b00400ba1201c8040078643c10003040c1c05018201400c010088420030341c507071124030000095030b50085a0810160380e5030304200310071200c0000d10101100d90a203002005042d200000e200c40300d44403040c2e1140d660002403203084401c016030016014149180c1034514150802c0c0405543c1c100480401e03040c50390070350341000401d00808080d0800c078000d0511200380b061141f030300c1c00450510325041e00230a030f10109024005900c583d417107024000c940c008614044210702660794070354005242a912080460620080108150901000300f03440c4010172105901ca1401e000d01e40c000d14051310303000d40b401030410020341c458 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 552158273 1106 552157167 552157169
    0x9112203170706050601260c04051c0203010608030a1205091c02030a0206010501140405060d0e0d0903060b0603060d0b070c0b10180b0a1e030c09020306010e0a 70
    0x280360460484d00040c0c13032030b810010768404c0040404078100c0302c602200d041c42910109a950030f1000041c1e4455034008640003816072095114a011207802c1a480da4400c40c0244001600d07070a501e590f0340144860f031170024800c90b016101a42c0b1a80c07019170840340301801d680500003540034200c0d0748190f200505005070b03c0003809008080d0306008a81c05050309191140070240c08055429a0340168064540f00c3c050003d14041300188030750080304c02012140075900041d94582c00502241030901c001d950250030f000e400902881c1c1602142d202b041c0040401190304500e48903100d440c900140175000740a0b400c034820000c1070038009107a00c120341c29000b00c1403007401d00d4195110b0004516401c500300741041d80250309990744803445030540e550100d230f0b180040340d90520401184140e91002c2d1a8507448a030109240c81e940d00210300c138070b0702a214202228103c00601c2410001 = true := by decide +kernel

theorem cover : BRFrame.Cov 551978417 552158273 := by
  have h0 := BRFrame.cov_init 551978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 551978417 ≤ n) (h2 : n < 552158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
