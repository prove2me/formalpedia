-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2280
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:13:58.795018+00:00
-- url     : https://prove2.me/submissions/d175db83-e2c6-49fc-8d8b-7b0d5255435d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 409892086 ≤ n < 410071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 409893336 1250 409892086 409892099
    0x9080304240903090e0702030c0a060f0f0501230105041203080f1807150c021305221e020a0506030403080106030b010e1f03140c190804050c0d05030c0f07 68
    0x10394518407101c0da1400200c180801d13046903440d01111180c800801030341c0d0b01c42c003080742140140340800000e44100e082c54000c00996030040e801d0541600020000e02200b4460b24040ea902881a074401443c008a81c01c242c45440103203200c40310060401d50f243c0342d552485140d030a80d10190623000604405c0a014512140001950b04010b07501d18081074440310000c025240c280714842c0880030f06080c25076030b8400b4001c40050800540042a800710035003060443e0003c1c00f8100c0c1c6001202240390030711200f511405201805803070700050114114030814101140d08480c06c4416039200706c0d01070f400101c5680d48e000452160f84203a9030781e00103514046001d400e032444a41c0392418000c0070701c03c144254803441800d60044102e6400034411504003a0240c0042c4a5240c1845048008404208420303800c040285031040308140d0030507202340800011905981c05541c0102107030441c00300c088651a03d8120300e84424020019240b50802030600e007454541c94a03402d04660300041c1c01007000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 409894586 1250 409893336 409893383
    0x50d1a1f021006032427050d09060c0b040602070f06090b060f180a1104030c03140102040f03201f0305100305030406050d022a06070908060c0c0109080304 68
    0x60805520074000141541d4940c1d112241201c503001c00b01703100c113500390b8221409802c81441002005852a9182c0060001d250306070400d07201669507201e160003041503684101b007040300f110311a940d450b45140155a41120b40c1d078001c1c2094400d681c00740040408604c4290f060800a44500400510a201450301620900c0020840781c0b003500c0901035114940c84000c002c480c0f407076505640c55016503070440e09100134410542081301d10000450080204000d00c0602015240194990420540036030100790913446640103020703209080c000200005040341d11007000700040070401e0740514070340c0f90208100401c030182a1414401d5907400703146c90394042c0b00e1207422034060381010701041e04544420756203115500c200010041c0009040340320300e100d030741076420580d00b40f44001994032405a400c0c0c0d501c01c40082a101d2401080d0100b1205ca0050032804202c44000000d480d265507410983c81ca180c0043d000403095540fa1820600051503150007107218512400c50280c40c07a80445141d0103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 409895836 1250 409894586 409894603
    0x3705180f0906010c0c093b07091107052a0a1211180403030204150e0a140a03020d0804030b011e0e060d0f06061a0703050d1a1f02 57
    0x180300003145000c00c0d40c8800740c0c500da0000c42801c142d9a41c003210303d0402151245941b008418900d82200305100c40b41c981082c25110b0302c01c070390f005020214480a003034822151244040150312412040003100d804e9004400da07100341819050900c43c1c070784c85090601e010320028080034510001d0350100b4481c10380344001c40541c2550300160550515501d007001d0703022160003515000040c03d41c81855512201c0c492262040d41c0030b1980107080510b8050003035000360080c450074910201c81005080d1094209001405c0000c0c410141507160841e019040003851000607040a0852004000340e00d40a480b017041c3c0b48240c1d4801d507164079604002d92140c10603000402003140090b003081c010007218525105032446031503284003540361100010300b03040440b80001c1084c180300724820140301155000c101100d505890b007a07600182d18540d409103228950008021070340038031001e202c81c9a10f034004040d490030058071284c0c002a07080040d0704291480c2100300e80038480014006941d030305001014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 409897086 1250 409895836 409895839
    0x3050f010902061206040207140609150c0703080703060f06021c0c02090a020c0102040515090114030603032208011b030c1b0b13060e0a020a05060f370518 68
    0x41e9101d980000c006114900c3c258001c2e890b42008210355a0f101d504407102a0340c4582201210f042d442d4100f40c131842c003105d0404450280f012403103082c010a00d403e44c8100c07411200c031403408099540070b440880d4090309040402d03030307150300c08103401c8603210f48280600501d030000c0968941c081008540800030312010420001e8203840840180c41e03528000c0e402c54540640980c0b116144100300380203000e103074005540100702c04180900e181c0f08100600e40300100ba40e03002411448058865000e1009654094155108209844c148045100104001842c03012000c6510750307101c41326401c1d140803290096a6000a1080080c0103805104800803042141491308030241c5040f0f084030106011b42001e0440c594010004005065060392080d000354018410004550488115039071040c0c081c1c412401280450b502045500d42082580c090200e02104946401d83e45403d250550382081c124007a204004003200d0700b242e230b00400416581c1156a283c036100c103020307035050b5404c0c01130340c200c41e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 409898336 1250 409897086 409897091
    0xa05070309031e02210a030507080715060302040b0102010b01120f0b060703050a090806060a0306090807020d050610140a152c13090f0b0c070204150e1e0121060c02010603050f01 78
    0xa917440c000441c2000010b9010300307055440b00d1050900e40160b100d00400100b0038541500c1000ea1003540d0340c00401a00c0c002d550030041407900800585c225861503203103502040e010400702a618401d6008400700300c00300c1c40c0200b100440000887c0003604000b600310003042c00460f40e00c0c602c0740c5c010020703002842440c3c0207050b10700300000407618010b8139000203010181c58003064028445a5001c82d05695400751013a5425615414059100c0318191400403a641c1d249000240c00d00f800038041c500d5070401040c4405a03882c18a540c20121543d0020343c01b442000c1c40e0303424190380e1442903404080030350503600051641c018100019076074000c04400e82507252a40b5080441c0e45880c0e01c480895100b000ea00668403041401c4c4503901400d04000d6105080c554520040d508006007242241c0140d082860282c0b075611020039840310404032038092081820040040722520743c031500d61481c103c20044000555500c0740002c0c0c5035100500070150791074050800c200b0408110302688100f201008 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 409899586 1250 409898336 409898389
    0x20a030e0d09090507050909040c06020c0a23010e060315041b0503280c05130e0f15060d0207140d02070815040501020c060103030c0b0604050c0a05070309031e02 71
    0x40c00b207500c280105541d05a13070328009810980101c0403176044602c000d0403800070703240c0380c540041440e0b014000da10050143c071450b0440350402039007540c15140c50306992940c0203c113032400260000340c0b03160f060401066900381c1c013854032550011805108c215a0340b001200d4a401400240ca8208642e42c0062a00111010880e035004044d80c0d0800c44400d1400440032100214030285c51072100000348440c40d10664420380b0b80c005004127100c0b13040d03000d9040d103517564440d0542d84240c22101c3c4042004004001144031140425082c19a01d00910450410a003040c07024100d0300f000d60100c0369412840d0023010210400c1001420041c800d1000301001420200c026849901068a5445924540d03020804108080d01600d03100b5000704101c6115603924203000700403041101055a86000c0e0902007400c4c0d0800e03000e202d1143c414001c0347d520b0b1038038240d01219550b010807404e0b0100b10046a0100c0000c40228140241000d00d542c004070030022401080303105003807484071803c94144801d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 409900836 1250 409899586 409899613
    0xb011d011a130506030a060e0612250e0a061403010b060415020708030a0225080a0f03050706060305030c010f09050606091306110307030e010509060a0510050603010306020a030e 78
    0x10034400c07015440364464504031201c0c2640c44058000c16407165001c000c2185001d460761056007224440c0b8620b8807a034840c40b0500201140a2000400302d4202d40c43d0918003020911003411b40320022a40c1d038580d44d030781d861003064101d0156006012251229010001140700e0b806282d0121400c50003004a05607101c0003070b4083c4500d218610b94070250340e101c11082802845440000c01c040d03029242d4a0b658004001d443e05202c5034032440d8032200d0282502c0807803407016280142d43c18180280031445641d111070600c1c0c0508841241003047c1000300310001002405580c000b0b62103100216200c1602d0398178142920000000d00c0007840c41c03c50801e000c103000281c0c1c00e80000701a10b20f20708648a0300e413080e19115141c40d0281c005410612000b0828529600541c420b40345590304010904621000303600307a42d01a0b07800300560340424082042200e035039100a8003e4213401c299840140e1b40c10101e062a0000d0703009032000c035404a61070302c2c1182c050181380004244603000c0d004c004245031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 409902086 1250 409900836 409900859
    0xf060a03060f09151b02060f0109110f0a1d190b0703030b0a060206060a0501170a050a020d0603051b030304150804020402091e040c02010203191107020406030b011d01 73
    0x44054451625060301909a4940f40d000d050b03a140c0201d40e1154841481041802610000c0329502c9903500c3c80c00b840d0342d250f02c0130a140e03014041151208480fa40380c00c9004024192030380c80c031024004104449144030036024002d014080315502c0b920300300032150009004000e8000b03145030140e5064052003140094411407107003075400701c106485d1149190308007100104010401d02c0e8001065400214035141c00203000c51080c00200d856000983e22107004598000c3d0014901408038401408508003020a400c020382c0808200300060510003007200741030a07900580c3c001d6807a41c10400740280841c69040030f03820a0501070b0000c514261410071382030041d100c40500340d0100959800483c0131542e0b0780d01111034103600141590380c140011020024030f076140c19440c0d8452071904211045480c010700a90b4400c41c40b0700d420700420020407254a01401c0101e41084954004100304401a641d61181130040c40c0600e5100d1404e604004100c00304440d0b200642d1320810f0300e1001000040d1480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 409903336 1250 409902086 409902089
    0x50307050105070213140c180103020a1e0c051f060906050d170408060a1d070f0512160b0a1d0901060c14060405010218010e0607080328060306050f060a 67
    0x584440500300c1d5005c2d5440e001705090b5040c005051381c0702051040d900b102c0e801421403047ca0788281000358041400540480c411010101c0201c1c20407103903080c02c20742090640d182c2550f07a050802e02e0500503070321182804541c0c1c1890004040c4581d24440c60030032407282001038500340d03604200386414440028080c10100034010201141d508a2841c402103070f2055800620300c1800321503007420304050b5a00509170209240100420180812041c04000a103100465600350942c1803000c6c00c0205100c20700000e0542d40ca1030348180c8840d040403080c2e6134500401401c61b01071042c1c85644096004000d1814640c079002e03150000b80f000f058070340c0c920301c9a5045a20500340003411810720700c5c02903c0e4071091181005580034400c204028454107400905900400a407804640c262001c015601c90601a081d182c1003072060100c000042c4010707000315040140307024800e010602c5081945000417080c1265010701707880d52000c000300041806070a8100c01030313060400b00703440c003103000c030343d003a06103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 409904586 1250 409903336 409903339
    0x302031806091216050f010c120510033e030c100509040510031a01050f03012f041e05090a050106020d0e011803240e0303040b101503150503070501050702 68
    0x180c03044a4821032440711001c85d403020554048100c44d485041c000e1031000c0c005804110b40d04080b0008011074031403180708001010b0844003290954803a40310f0414080caa10140c030410400c41f803001107940b8540b038621000040303a141000ca20b00141030500f840c440c0c102d4028210300f818409029003202c203848241c1000d4034005038a541e54a54200405000d0744082c100b005604100c8482c195a040f109050340e0701a00d00c8034801501905045c00c84104454800d40081c8901081400f0300c014400c44400005050b0581d08140e1111522689044466104131005030303115800c0000b4200f483c8820380c8071038840001c014940c501070029444030085529541041b008801d41c03e00c0368080e085841580c1403803c80c4813641da803a80f42c400300141c1a0440c24010b2001c400345288660184c0c0900c0c141480040040e40c215116599078158940020707161015081c036410300032038008150548540382c140541c0e40810b070000b01400c2030625004a030040da009421403601032282d03982203000c684225a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 409905836 1250 409904586 409904623
    0x3100501450b0a020d022109040605100c030807020604021011250302011707050405060c0304080109150c080907170f0105090c03060c211503010c030203180609 70
    0x240c001491698001c09032007a00c031014200d002290a0314040c02600c20440d058007180d0a60342001c0342640c1e6a04122219442001e5a034680510310b000300d0080c2c10340038030140010603800c0d11180014501f203a0101428002090204541300303240e441048603400030a140064a180d007003d401013030b00201035800000030b201d0041c0e40c000e5168420840d950b404070403100c80d11b0017845008412500300c181d0b4130013680020700380c41d1442c403004540200315021b14440c1d1165441c081c070780b40c2440500d400201c1c000d1290b020a100008a4410a00030029000e115003040c09001d0f80003800b8070101d039041ca1050003044160020001c04180008865055582c0000307a08600c0ca82128a1803809940a020100b80e50800d0280200090000340060241100314203403403655641e00d42c10182030081140c42c1c02c09002040341c2003045100084040c1e0003440460070405500c1684006c00d0a450b0007001c042c00180e400420024803d180f072400070340034401c03900904994104507020b0755036010f0100c103c650200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 409907086 1250 409905836 409905917
    0x60f230702010503150915030f011401090b0d050f061909030212030901020c012c0607050d09080c0109230c0108040206090f1f080708041a220803100501 67
    0x1002e920404002001041b408103860700d0308004c5990210314007158007901c180030409460b4134040c0a0002207101d13110000140e40e10f40041d0300d024140140b00c6682002c40303c0c1c40c2d407011840c140640342d0901d2a0300024051340c148004c92081c2e440c2ca0160b000b40740782c6442881030010340d01040d8050281007120b03040e030f241d4440700c00b820300a105854031084250700e03181c00018400f00461603183e0409410170b080c26003000d00b000058807074804807003030800904104119404500254013a4044e107015154003410014031032000340c21101e8a200903905108840414619882005c03010001c10311414040c2c03e400d00d0b0745001900700d000c040c0c07009105960109460307149881d030400c02c07400064010800f8104010f0f4807036110a152402c40c03c00002110301f4005180280100b4645010310760280c0c18180c8800d0840c0241c0c603a4001038000c0d0b07020000503080f9040041c0c086042c0100c0743c00f075045c517030340c1c0c0c108410661101c01c003a5205a040c0515070721038690402040d81215500500c40c0c1003408003070f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 409908336 1250 409907086 409907101
    0x307020c0a0608070c0c080d12050604060806070503132f1903020418061103100609030f02060d1506090e01050306010b04150e031002040e13170a05090a060f230702010503 75
    0x90b500c940048840e4480c6071400e10304149d008a14484211012104101c00c5d1180c2c070500c42620954024071410741c0c0181c000c074604a115200940d404090295110b50090302139031201ca00541641001e0306500412a00d400c54690044040007084411100811403c419841d04201c00200748070180c46255500c1c2c1c2c0400d074141a41c0071401075903020000b084108107011003408550070039a40f10407040542c0401090303050140c0b11030429a900054414148106642000082ea00c4509001c1800342c446540464041012010380017820b03a81d128480000d00b8210482c400c4079059101620940c40300c0700402403036489600321003e88003c0d142902020040080c145c51001a0320802c0c1d405104520800038010142e601403c281d0b40401c80c085501d440c4c0e4602c682d40c100d00c0090141109400d031290207180c0c440c0c0302c020803000c0101e04000c5d0900307400400180c1030006a900070000b145035000500c02c0d05a20500c0c004203107080440d04292429002c1c007985140c0524031009051050010115084c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 409909586 1250 409908336 409908353
    0xa0f0303020d09083a0201021c0e06181c02032d1b030f0703030f06091a01120908040905010303081605090f011403090106030c12020f2701060201020307020c0a0608070c 74
    0x81c0d0080b02d605000c0c3e01702845000703000394008003010107070695900c2e8080124605001e40e08a112200c0c0081202c1e4548400c035200801c0c3e051110b05461191003130421101401d1541c29580e010740360083c42d00c0300f0050381a0315401148031802c5070782c40c1c1103038204092594a4015149010031003550300d01074950f42d4104500d58818603140050720800401c8890800d64942c20003150a0f02200c0d050140c40d41c0c070000300040d1203650743c205100ca043c040100c0d0b02c1b544250541c10300ca503900c09002c1000b0f43c403901d40350040d50158201c07851403511040148241500144030540181c22400002c01c04103071210020928061a0203d03071040a4601072015507070310410700c0c1c0386040040c000b61980c90601c1081e060003021284021685044060000111041005840d45045801412101d0001c0c0700c1401c0059490008440e02c0190482480990101010f045000d01800c0150001603503030130842c4010f880c00003500800c0744607040748181070110580c85100f460300507a45040000041d401458001c81 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 409910836 1250 409909586 409909663
    0x10917030c060c0c07121a04050c0d080904180b0c030a0f060b070c150905040f0207050f070e0c0304021e03101104030b01090b090402060d09020a0f0303020d0908 71
    0x903a20603403051120a0341800f005089a0124034111039102c2d90380e00e82c0c1d040380260b0280181c0f440242502c0911392400c1a207a80c0e40c41880380060302c00165010700010210b41d980107040c0c1c0c071410f01140d0440745080a10440402c80c91103044001481111b036540c800b82c04000b4030707104500d0004004070703103030880b650002c4070184080030040c850261141e1141703486400c40002a5452540000000340c1d0030048103070a641c03c0d4a56403840c1d0300c179050006010150050826643c00c0a1b0300f00b102c48007266080c0940400030a010000d0940709103040c11040ca40800030745400352020003007060000680d41d10b41e200b100550441c40450400400c0000241445103003005925024100941000c14002c2c0d10020000da0707204802404541e45c030b81954000b00c8840d16221900201c2c0b60b4040b60140c0b900340c0103020369800d0117a000c02c40c030400c1d0340420600c80a6601100e9000980c06040c420146c0600c04400c02000c00c3c541150514582038200c0c0c1d59030300154091a1006c8250b0000c1281c2d800c0105806 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 409912086 1250 409910836 409910857
    0x1207050a0c0b072106050a050f010c052407020706080708040f0f0c060f050405030307080304020a090f090b0a0c08041202070f0e010e090d080403081305011508010f0b01091703 77
    0x1a41480c2048018164544485500c1305031340340303262900920100d0f8854041501d60103004000014140b406204600f02e8500d07880d814820740c0c40110000501c10004001d44000c10b200c09410454100c030b80c0c182c0084094040000e6401030700b0103100080c0c1c842e0156900081038034040c4100d8840b418889828072013568050868003070002c10000f40481d40000c1c004a5211b60380351401c110110200f04c4480c0982d00466906806c20498100464803001c06107811900003040600081c3c1d4540b80d90382190720711191356040315203aa5400e4113000c40562143c1c1c0c00200758200b40203128903944002d1240e50010401003a683c40d800c8500c140701d2007040b0140207028150012008903481e403d1651028409229203928605140c0002e00e0f407040104402011800d0ba0711200072540725542c007924001002440c2138502404500e044010031424003c1072203404454010020b21828503444500b9640900d2000803014103210200c445030361300201030000c40b10322200d58403042121240c5a4110b218201000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 409913336 1250 409912086 409912103
    0x1e0206040f0602040510031b0306030308061306050d05010605033d06080a050c091005010206010603020307020a21020c010503060d030c060f151403070b04050904061409010c03111207050a0c 83
    0x28002c29055800058401045806130100328001002200ae46d400d40c00000e0000e0030380d2000c20041c1c1005094284100e4603501c001c20407503142c9001c0f8060f204c030840c05840700da450740b10810090809010390010074503020502941c80d4040b0004c44a0580c0c5a0f070007011034900700d0412850011654042c4c0090007403042503c000c4c81450a00d603036140c1c2003210680c442d1484034081031807006400400c4003240c038186c018019331380c030b402c03000d800a4100134060002d5002e005010300006081c860301003050800c01c01e1808043d900f06900920f81401505207038140704007001404003d541c2e14100c034034080e500d0319040c00c4060580c41c168014140604500246038144688a9400384080c0610070507189448003900454100d03c0030140e646100d817140300001c640401080c0102e00b85004074903845409184c1c04651400b0541ca50310f0f0b000c6c42128400d4041c0d6441e030900d51031651600502c207250190940c1a810b0044034556810100350252145050100000da105c0c00b142c010f410000d4100e4204600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 409914586 1250 409913336 409913359
    0x12106080706050d0f0212040312060503070603050915010302060f070609060609141f14060712020102040f0906181d0d0504030b060409120e0102030c06010f03031e0206040f06020405 80
    0x162498004945411a00b410001440d0205c1d0541c8203607422180b6000c1812026100c5071000d85644808412540c0d4140d15407a010400b134404105040003040c03217071342c00109450010b180508280e94508010304c4a00403400400c05070b540e41e020394264003d180d100680e0f410103440d1660007072503402e0005000300e06151000614000701e600003241c1082129044c1d510b952000150b01c000f01c01425401114242c4810511260b83e036011010f00101002e4201c0b4a01141910340800410f00750394540010703034002500307001d801d910b0160a002002c01e01c0c0c040c800942411401c000d064601c039404032145a440f00745206003c80503054440350001d5000b540c496041c0c10b103009010394028041610f4111008020401a04240c49045103003504000000b6a2030320300c14088481c085d0400c0d0040c110b03c01441400f1000006020445c0203150b020051680c2915525001e408090f8075090100da04500350314444c1000d03000300d4035580c00f075405601007203620410301c2c02d500280980c6d004580c221020b40b60 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 409915836 1250 409914586 409914599
    0x1a01020a06020d1d0d02060105010c1509060212101a04260307020a08060a1401080319020f0706031b0c08040e0604021b0a030801091b03110d050906010e10050121060807 74
    0x824500c0040154280c42048ea01c3d0303401592400e85e907075001003041d0100c1c560401942c5c2c10f607108a1245108001c05440c0c0101b0701c213607000404040d01c0c4403164400c8848100404403030b06800c8803050034905003440c1458546581e98003c0715a84c2c103055a041d02c102d142c465400030a00858a20f640c0c02011441102d46888809565100850b03a0182c1c03186041c861211782c69031111b40d28100e9180000842c606003840401f105003492014010b8103503c80c030200321901c100284116400f405031550009a201c0781080325041c942c1c10201d40c3e10500883e4a0928089082d81003140d064072010300c0140304580f04c90012038000d110b03003101131181320010003400c0c503901d0005c24143c0b0b0007402552050b285988850502e41200c1000d114040d20810301c40c4105170311400707174100b44030307094100c40c001c0d00344441c0c1001038080d10300c22035008000d80c1040b801480b102004140040d003040b80054560031141c10880081c000304035400041d282c600d0345002c030320484802900300c00042d1612009864810b41da0b6030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 409917086 1250 409915836 409915843
    0x5030304060c0318030f020111030a09060506120c010813050a030503151f030b060702120a0203100c0807050333030c060c120f040e0705030a1a01020a06020d1d 70
    0xa80c11914181020005881588640079880079100700640d01c0d80050360950742500c2e00d1040706189403d40d5250000c50012540c4d030703409148140900c0c04080354015071890b246080783c0e00182551b12400c002c40c08503198041c001004190241c0070f0034565180d490303103480703401c0308444c01000038103500c1042c4014080560010146004804100080418080c0318080080d43c03c42c1c1c0c11819950702c6120510450940700b9082441c14040180135030340b4002280d0041021441c240d0a12001544003815003811814104020100d00c10b0607a4104448002c0e40c03030080c142c000240002003040004004038180415186040b42465680ea400e1840306081000380501c01100c04100e0b4401d0082d802039400a050440490f1007072074815002d401c0814510701c1e10b46050300004152070072071000b40b001241c2907466a503c0d6014140b5511855168607111050805031442c0c408070f16139441c40714040505c2d50340c000a2601d92598821800351f16007440307400101c0200710151034600e800e1902c4070a0703504143d010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 409918336 1250 409917086 409917091
    0x90c211707020a060c0510020d0213030c03020f12030406030c05090909010b010807090819050f100203100f0308180111070608011d06090a0e07091103090607020105090c010507020a030f050303 84
    0x2560f00492181d41d843e0240c80140d0720380d6003d440740d0042d17400c03821140c0391507005014844403018010309023404041030084058464200302c45811001800380b0a5160440032034403265411608030504400000c0c1c401d07100e0042c0d00c900418561502d40c1c00c802c00d03000c2d0060311307400e038406007181c00140b03030141030305001c0c209401800d03021070b60000c0803801c1140700d0110241596040760041100415443c8602003100400d802034542d4014001e200009a4051020a00c542c0743e8400151b103900340561002c10060384c2d503000a1071800d04100410015044005546909201c09908491001450f0044c4e03040c0c1c890b0b207a00c001c5402040c1001c1074050700400014140c681e56404c150803000d101d000c0e040806400d8410951003601e000000e4425046074024842484c41042512078103036850f0342c2c1c88162542d072514507504001c0801048020081000b44a52050103480280030a0a081c000c01da1981207441c009070400c0b20006003242035485000b804030040d0b900c28811006110755040c01e036145d8005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 409919586 1250 409918336 409918339
    0x7060f020c0619090819031d15040e100608060607030e0901080f010b040c0c1b091406190b03010506091c1103160e0609190c020d0f03090c21170702 65
    0x442d400490780c181d00050641c50300d410414011090141b13604e0039980080310050301c0c400c02c020668810300b241c0b40c81c50003440c100036107d6443d440302d080200c07071030340160300600101100c401c4200c100400b96001c00103a0f0008000d07942c041d614142400c00300e900800c50f007403864000340d01342e0000070158400180012440c881400801400042004010039240e03032760030800000d003818050300c1c0481e9100c40030710040d00130141000c000c0c80e555503108050320030802a4000821200040000508088502c00c544003240002050704a003052181d4000c2c1c00b06000c0e05014940104094203a500d4401e48044440e1442d9003413441c211261600d003c9251010790071501034052450205420f5400032211010f0f215080002c080a507600800c0c41540c1c44000c1020303c02a000f00e640440659541c03040040d01c4c00d00703074040e0081c000b440b50f014220b041c01c806c20313004051404c0a40070209184130001030070343da0000c01c2190701c040440d010401110313030200b026182035080071003c9500d084030002030414510 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 409920836 1250 409919586 409919597
    0x51903123209150c0703080c36010f0f050a0203040302040e06010924050f1f08160509130902152107030203010e04110a17010515030105040507060f020c0619 69
    0x86503500e15034a10f2040d11454044001400030400285c018039105511854103420a401c101701d203111140a50405001d0700501d10900e074542c104080c4540204811101c01c0c240042c0240031030b8401008154240d020380c04100300803801c550760900c01d2007100e00075074004009110141e801d210302c0381c552307100384240c188452a0020010644154202e01c010030070340e03440410020b900c0c1005028880710503032030b000d0340000301c03a030302c807442d12510710300d00c0c03c1460281d0720301542c0c1c82d10103c14442011942080d03c103220041c44540d255035501440d11040340314103140414041e007284080b07411031003498004560843d000c034030f0300c2c40d8100404008901c24a4840403c40035242c2d48402d03400c0348428018901c40c00103010004001c100c0da503d0304401480050803209184d0b58800711808031a5400460751040d035100c2090000048036910b241107502c5045008124505203541e07034990703450080c4509410f024504054455481c02800003018600016164a0759880e809103110b904070031034660f1102050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 409922086 1250 409920836 409920853
    0xb04030c050301050a09120f03151203120516110a0804080f120708030103020f031c020c01230a11070f06052203112b080304051903123209 61
    0x8085e030280c2500c2e5038102400c15400301d060340084450b07045641c003032003c0c581c0b1800040c030822924804140100310404000c61085550314004028424403026038040904040522000410382c1d034061104030750b1410254480c4007904600c0c1d0412858140c0507010b00008940080c00c0540400d524211980001c207562006207040300401180c007800c6009000484180014401424005402d00c10030000501301c4492514800c2c1112190701d06869420040e002664440180d503046402945d8080b1041c0a92091440d90002241c141c010035036120200001e1801c1c0b102c1022040c404440984003215002e8035580e00c03520040c0465101c0c0d1868443d02e480207580d000e0382144103030a901a01e60041c3e031201c55003445010004021406414100b841c865441850302c086001c440300004a44200b00445e12407400307083c110f0409901d0501c02c60041c02e11400d000c0042c1e407090103082924080b031400208810440b80c101440000000d600305040c02205291040d210400601881440008121507810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 409923336 1250 409922086 409922101
    0x803040f2a1a0903010c0509150309030702040c260708010608060306180c0901030f111f2a03021b0307061202070302190c0614071e08040b04030c05030105 68
    0x1510100c504881d00c015444140452140454100c002071115181641403006400009007110440012903012440004000d8164241040d2500346a15145246411403505007085038491280e420001e100e90b45e18070780c00303010ba4064850b00f240c000140c180c016888004008414450300180e42d000041a200400060711340e100b981300324418400500a450240c50302040c0c4564000d04044031400c40c0a0301c0c85100050b29228003044c000c5002e6000c3d032284840d14100000700e00412500c0300d0150308008142c00d025904030301054410441840c000f289200012641c24014244c481d800d8181e1008a641c2824140d0010701c2c242c21f10034040d890085018072000f01a602c0640388038450114951000c141c0c281ca1181d070140001d14040d005a52218121b0074140c0540c074038a0034102d41e004401541072000d20b5214070002003102c07010003054a090040c0c0c0b1001800d41045000a64103500010781d401000f880e0002c0d5001060b00241c140c5c0c036903850b442c103203000000a0003201d0081d841d110005164 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 409924586 1250 409923336 409923383
    0x90c031b1d0d0201022e180c050612040b091e03070303060608061c05151905070905010903260c0d020f0a261e09030d2d020a0803040f 59
    0x2e83d0b070580040aa450100300c00002c90048420441c1d1403100781454800801c00e54010140c031249003c001c0b80700c448181c50018004030081d000507000303200a0105003c0f24904000f25900160000e0302403070141d03105ca0205180500149107002c05100c0d21410700c5012400101410702540300f07840620040361104011102090200e481c541c0c807440c144102110301c0850440b045100307010b4401d9400c4600702e2180017050341403e4541114620108804860f90b54840c460070340c000342c05241010b001c1d8900f60000702805000c2c00064601800400803940b00c19014400b400d204007c04040d981342c02c04221503d48034888206500e0260041481060404d040440d1100e085a4403002c0d041801310300c0d85080031294010094413440b4401008503910301024500400c014240780c524099030f0b07002c9402810b0074105d541c10741c0014044501c1c0e00494030070040d034840c6480d2aa101c05d400300d0603c2000c1c100d00e000203820b0041c2075440300209001c240442e00c0750326a0014000d650384400758601e01c42d1742d04d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 409925836 1250 409924586 409924609
    0x71704121116080c0a060201060f0501030f09050706080114030a0b0c091801030b0a1d120a0201020f03090105092109010e0f040f0f0c0c03020601090c031b1d 69
    0x4446800340c41405014045038500c100195040b070305040c01c1000e4251420007941c022202561140b0f4034003215140c81d030041c60280c85584024000c1a02c1c00c03038101d01640342030043d0b070b0615854210310303400062290f00c00008241c012084802c90381d0381d2b14000d000041c00780507200c3c0c8001040d44195041c03c0c0040c018161303d621061010031035440f0020048960412180640c1c0003180000340c06007200e581490034040d5004070340008450901300703840011202d41c003120074400801c84a2144c004e01001c41d607a040f1010400e030481d42d840042100324024403840038410b080e040d010043c000040f005600061054040d642104ca09a400c902100324000444402c00b0020308100880403013540300d000300810500300502710b00640040e440001d0b050320724140301da842240c0d9076001c2500504503800b5036168500e10b030a061208200644009403144814080e6003030389a1211000280248203900080301840482c0042d02d034a14000001042c02e0050841051821054070740f9807010703d8071521250 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 409927086 1250 409925836 409925843
    0xc090c05071104020403020909060f01170616030209031002070204060504060f0b0a0516030215010f05010c062417210a0c020f0a0602010608060108060403050301121514071704 77
    0x1401c1094a40e110541c410760486030300c3d0400d80a100000060303c402d9040390164003d00c01410b0395280001012145040591142c01895402002c1030381015001c1075035500a89283ea001d00480c003081802d5000c0d11900c20b4183c4c06104040c51005485015409000740320b00c01c070780500c01c1d503540304200b02c21345026014005e600040c01104100054100b40245070003485810b0060130302c50401c2107092140100030707003503002d6007045800d0364020708240c4002c0e003d4004807000a201300d047c9000203007018038082c0002c0015a95a1441200d07030103070700c9642558401c1c81c1c0d000c072480361202800d601d04072042d03003800020310130418042d4804a81d801260454105c43c0d49041c10f1241c4003200300e44ca0b01180740140e07080306506015600648503020420081e15042d0004203529241c400403610b040310590290031960404024400003a51040803a0f0440700000241c44001805081003425508040f1001120a02d09002c0282d034001c03400340180b1072105a11800154070100104007a42041102e005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 409928336 1250 409927086 409927097
    0x161e060f02091c0317041415070f270303090312030b060f03040303092a050409150b150a1d01020a02030d20100b1203070f15020f030709030c090c 64
    0x949010003038403648041134001e20740020710041c4010a03408a8034250340c141c0b89202090168035011404024640c07005002072000081c43c80c0c81e0900900c0944c400030b41d001001b40c044c14084030010801800324808aa030b4280340c1ca065075070714025198070301030711080302c0074500360400d031000c103019102e41611040007400151404411244078540359000801c100c0130b042c0c1c0c901540000c910781090412080501504004210000760907030045800300354001403159041054007000150281035510001c5800103000c559480040005280c008003089003100ea807801180a480040c1d011546800564850a0201041c1200001280c4500300c109000e50142e0100003070050041c8600040303082e2908a05440d031101c000090107504014520690811307058407000d8225040c90024a04070030001c400d4000c0d850807213143c3c1c51514010950002400c241410004440c002140350102d035038a014001845949140513000075002d6141d40c00305990482e07400901080015581c40340408030b0442c1d8454 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 409929586 1250 409928336 409928359
    0x209010e100e04081b0a0b0a060518060f0607110103050c0a051b07080d0905031e1b0402090901090504120f09180f050f011d04020f06161e060f0209 65
    0x1003100c90b003009801110462010811407000c0180c40c4940e421612510f070203400c0d0040d44d81443d81d001038025045030f52151401d00e08100700d543e0f0340300c00301c0020440800040c1c1136072007600091407280704036421504207600085040411600307410044161600340c030100450b031200700d0350141038081d411014022032010004c00b010340c40d0000700c807104092540102c03001181c82e14111810700c0250603015000c9a0100350078032480c41e05204440312420002c0e11a00c41c141c0381c042d040c0d5500c0510000e50b01d0742c0e141c03203810801912550116107680d60040d00f0003031a96035810180d0f004200845054031220a035041d5003040a03c2512481380c4d80303e00d551a440741a08000050000398000440c0c0310850b6503d4650300c03034030b909500030799105010f04030380044298540429941c8001c01940309a8010340c0590421005070b0310041d09030010581519030781d8540b83c04022420000c00090030180582102c400e10308c15078084084585400c503c01c0e0802e00460340048458401d9000d0400e0305503210211140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 409930836 1250 409929586 409929599
    0x30708030604020705120c16082404050102070b1806060906101107030c0306020418110406031a0409080a020f070e0f06010c12020705011103090a05060c07031505040209010e10 77
    0x83c04c02d65000c0d00079079502e8100c0c9140070000c3d500003030481e00150011245500c012000c0c0b4070281c0280a00400380c10034030300c10110689140340300c0c0a9464100701c2040400c05000e4250b05907024964418010896800d080d01003504441d09841c0e201d0140c40380c100051a141441c0b11a9809100b0182000e04000340200d01956076051000c00301c500fa100b83d80001010816007402040214010140143c4c1c41d4108076881514500c42030300d680025040c2821054070059840444049450b14940002e255802000b00740c2d0303d5080c10755803588141005528001d000c0045e00070704610116030203e8610016440d5096161183e40c46500d4840200d6070010300e0140c01503502e540c2c050b10524002020400943d20181d046c0d903001c140c2001030748a078000780305558001c4264115100624001c6082c005e603503000841c015004e0246600a000218042c2c0c016001040180c001d15840303084003208808040100004050450342a0301c200e00345000024002071100c02c060103802646141c0f19081d04004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 409932086 1250 409930836 409930841
    0x6090106181401050906131d06010b0403030801091d0307060605130608151305061602070906080318121207020a0b0906040b13090608030d0609050606040909140a03050c0d02030708030604 82
    0x86c0820340000440358020140502481340b0f0341c000401d05074aa090b50464005c0c6c51600605800c424900340d402c000034004241c205801c107044401d82500030520180411a440c100032039203040038038078800450500b040003980c0e0858000c2d208281c440008040c4a0107200c4280c2d05140301d24203180c3c000142c1114984140228194410081181e07000940807503950726140c04412102d6211200c24124007400140c0c1c10b01018008100b81c0c1c000707208040c1060065500d910034a5413112000000300c04081d000d4a90b0710000e410412414180e94000d00a4028040707030b544060300032445201080d9001c500800420295014244007038401410b00d428001c0740c690591010300c81440356250790000103283c010501400000d80091400b0759183d02101003c0002ea84607600004a424100b40801c5016110745080d54111809000d020804046504004a54410f004040314260080c041c0c0b50051540080040c2240ea00764000c80312842c02d207840490b103a018196004201c01c5003000030606070f19064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 409933336 1250 409932086 409932091
    0x5060d0f05010b060c0a0b010506070309052106012d03080a051c02041401080709030b060f0105071202010c0f0801050105070807150504060e0106060e060d0914060901061814010509 79
    0x308000100c50f000740000504503000802a05110b52044020004110038204400d005150981e07800d41804007607940a03201d0900e0f402041d01841c000e00d071214400d020403000402403c0300c4400e0340c0203542c598480075119281548003103096400105400365040440040340304032a044a0301c141402c003070b082c0440d00d9501180b03113480444051244d042c0060001c0c4010802804e03850940c0c00703003402c44c00c00944881c1e00203225500b0720038503900070004280c480c080b007503022804645426158490b0350059460f400f54500182c00350280e28800301610f901544150095881c41c0c551551918141c00300303d0311640c00740103c41c009502400050f000072186c0c3c2c05807002038407502405200038884051a0200c0c0e808682c1a2140c540310320040c00010b1003803084201400642c80c00440e408404030108a0612a5510300d400b42c41e51f07a075040050004c0215110912003450090702d0080c2002d92440d800f0300701ca40035000d1081004002c0d0750052001e489006050301202451484580c600020083d005400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 409934586 1250 409933336 409933343
    0xa05060a0c0521150402030f010b161e050f060702070b0f04030209071d040e03090d03020102070507030b010306050c090d0201030c1e0305010e060612040b06010c02090705071505060d0f 81
    0x6101d0304948142c3d0030407507503001d180d41038016807614105912250042c244510240100d05c10018424076680301050541950852000140e840c8010341c22a0280030201c0c07006803207030000080d80c00401000030046030205010314101e40d507211111041545070981981c8100240e8080c64041148550540103460f811348100c40c454242940d940116440b20001c544140c001001440f240e1044c145d001d42c8064620010f43d420048460040301c115600d10880045522560312661510308051013501145c00c0300b0340c01030a85214a40d6032800c000150401e0004031507903030500001402003a5900183d8a44032801040c0881c5803d89400640003494047c000e941080405c090407940000c03070f041c0c2d060280c000e5542c002250f41c0361001044444034003515103441024104011800070564441c0d094100f9001182503a00d920b400300181c80d8501052002500007080e481000141e03500400945600780c050945480b0140f40c6103c20b004980c0f089800951212690103405c02103209044400319542c803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 409935836 1250 409934586 409934597
    0x90203060d300f02060a0c09051c170a0806040b36070507020f0d050c190e070804020108060f0306130c080625180b18040f0c030e0a05060a0c 62
    0x4115416480c080380d00c55540200f4000c00c0140c51842d41041a594001041c1c003007045041d0400d20014080c0c080c500c1403e1240e0b91a8070b82e0402080c40e040110410382e4007520b0010030740b2480c021460715411460740000418042400604203060501415503940001040e40003101440c3c1e984002205100454203040280070541c40c60302c260082c101800f502c0c041e12225201c01ca148108617400c008950145d0245c10700003001c0d40051400940741c1d0b240074046030044584118514100c101103003503404440c80501e1802401051a000241203001724006e0b03807505100c1d580e80c020f21500c4450340d611580c05612500c0092940714601c01c200b003105114400b40c08000703544048191500c2e8083d600760b14a20145e410010500da6540c014000d0b40d40b140c1024040c8404440151000e11028422101584000180d0204000d10b12361200d510720381c000d1041001c0c6403503000b0840103000c14040c48022929000321125a010006040584207030300000a242a60309e8190140c0070303010f012040400c1c8038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 409937086 1250 409935836 409935893
    0x80708040c0b0a02031603031a0a03110907110109150e0607080105060c0c0d0b0915160507110d03111b031b010212030406020c060109060b07031103040906080610090203060d 76
    0x12039212500d0f41c054007a650115209c0500781c980622045580e030202d1007003030145010000240c002c20005c9140798201c1d42191140d4600d401a140c0700f50f000c0c0013800380d510f4011140c080181604805074800382002c1c00f04900c01201060668404007580e2070790115809000420480c5418001001810402c40540300610122400b18a10f06c0c80311504846540400d000c00c0b200e01c0f400c03c8024840743d030f04046200c4a080c101c441e030010b85c840100c1e6408000000034002e00340044d403201140c2212010381440d424a0850400034201609102400700500038240c2d403040d200b8030003511407140c0100801400d02c14a203150602d0490b03020804a90542c012000880c00c0d000541000c0d40c0301d50300030140540d50398000050310b07040c002d05070000002180390000c14800641076206540d14140e05040c114902d81090307032158903600441c1c1c02036200034100710001c143e1841c04602039001ba03802030000000252960300c0305042c2e0004035280354000c0300c0c01a005010901805004454400174490203032444c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 409938336 1250 409937086 409937107
    0x61504080102040e011802121306110307121a060418200d140c04091a1011060901090807020d0311011d15060618030102131401080708040c0b0a0203 65
    0x80c0c120313038000500d01c907088004100351014071844492a4003a03807003c5282c0720311051141c1011001810344131003929540341e08000c00030a54890902020300764011910b914001c60007d003200c140340d00c00c01c2d10301c0c10b0503d00d1044038420920780303541001c01010141081e0402109a0048591441c1c00038059181c0421480309141032103442904c4602c80c51481d59060f1404e19641031302c40102e000040605e0030300800880348805416101a200c48c64004204412801928580420400c40ca01d1740510102405d07002541c01280d005200b841e003109032182661000340c1e0600700d69402401030300310f0b07204001c2040185001d2442c030403807034460b003050310341c041030340340020300310391440c2900010b44071685c8450503049010418401a10758000c5412107602e0f19201040b82400303510041c4207001c0d801c11646c90f8694003034054031155680d0304001d00c00c0036074982802e8400e0070700095031404989900d0200c0e000520421f4010700c215044005402031a1403c3c01741c0703030603502030040e03041117010070b000580c0c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 409939586 1250 409938336 409938341
    0x1020304050d060b090114060403140c031204082b200a081e090d15060e042306070516230a06061d0a0b1c06050f0c09090615040801 58
    0x40602038400011340310220000d04c080001c0c107030071098500107082d0400c80b44d651a03004807826690310030344482600411107280343c40e200d03501c8203a560500540b102110900c24546c0940f0466214508840c07005035040e040c65441c40d8600d914400f07115008225040c00340c058451b86800d20442da000102c070510b891521070401c0050b40c02118491070024070148444034000d039030240720007038051903883d015040b80045c1401c0814000101185600700c00b00c10a005164454030081c0000d050b0210141317850300d001511061504840700100701040010020048001200307031040200d91242031030142e200b2480c1c100e0511030170080340d242d02c102c807120014450b020500801503840f10001d1a0030201d918000c003e85083d504200f0000340140c0001c1d0345000c080d40e2054001c00d4010000030000040000703c2c1c0400b000048040c854000f0818040800c19998042840303042c5201c0003a40e50f032035000107035400d8840c41c051241c0c40034558003c02c00c0d620700304102d0004645441040c5280c296500c502070709 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 409940836 1250 409939586 409939609
    0x120f06090c0f01050307171914091510060c060b0406080a0c0501050a1409120d050406020d1b060b0a0f06051317070b0c0a0501092102010c08070302090102030405 71
    0x120340c0040d4000003036410310200e034068502d07007401c2c614214584190001c0c000b10340c4000c182112030807400414600c9070719002c030078026a40010244281001d82a82c40110b0100b074407100c42600c20769070b0380200012060780d040c0c044c503c00c2c840c0e801080c2c41c00300c2c22603420280300c0c402d0f04c0032035490310000300c15900c5100d410010b08200d405000f4092940c149580e801c865a440386040c000e0400020340f80d281c3c0711103454441d072441c2c1050781e04d880610002c20101c4c44140340f280035038400c202c1c0c001c40450300318010303000716101682120400400c0e004219001c00d0040081210707000e074a041c04002410542003851903140240142c0c160a949004240000394aa0310000c08504002510341c00350001010b41d0b400303001e105004034150001c0f0080c43d035440740c0b00d10403080c4441e00410f00210310401840101020354100009220312080381c288905620003407008185004a03103020100e00b240103025240c5c0c0803d071500d6002d1140d0300d0001c00d501a510200e6050b046020400c00810a550340d07034400c41 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 409942086 1250 409940836 409940851
    0x3061b0c06130b090c0102071203050c0607050301030c0605040b030402041d0d05040f0b04081b03100525080717100e010807210807030c03030e0a03120b0604050a05120f06 75
    0x901c1d40c50b14140440f940e2070203070448140b50004405540c89980016203841110940300905074980400c1c00e04843c00e016001090a203401008140042c1c95404400345044e04e020344550800c0310790f0750000b40e41c81e109034861191341c900300b400040d001d0f15060f801820b21002da100d003140380b04007a826060801600c03540c1000410b0022409000364103135a440440074210640c80e0b00c0c0b0341414901030700d41d2148280e003410000c1c842d80080c82120b441c144048070345004100c0040c07284d0b00b408008040064115030014841126034070018006500c50004280a5440e03030f00c41490384181c403c05010309080c01000100c1010700d08400040e645100c09240d070003860710002500065007881c40076010003101c0240c0d10201c00c100013075940802ca062086a42841e410b0801c0600c251441c6800e8006d031000c2d03103011000303000c1d12503410180754110b5090490b90201850804c110008034007007084501850150300c2e040300c84160140301605081c07c21040d40341c0c18004440e00c419010070030070b1a0800485411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 409943336 1250 409942086 409942111
    0x7060510210c0e06301c020303130602160606090b040c080f04020406080d030b0306010e09070605131208092416210c050d05031909030c0b15090108010b03061b0c06 72
    0x882201d0402c0c040b0070b10146e01c500c150000300e501501c0c02075480c000036126400081d40a0b414004200f01030341160300d03c802044240840305804d080070030040002d4807c07400c842d428801040114035203803050300c2c1502416200c9140c2900c4408100d0103442c40200304070b0f001907032003e002c14a000100b2a81030081020f5401049505200c001d240c14400b06174811603500200105111051001050500503200b031880c2a41c0c40c0c003c09001c00c40048a15446100413042c070344581c0301403050710802488046401e0724011050308400c4403841e4008040100d803080740d00c1c09e001c0d5403c0b020120384810710031030080070b0007241c00580c44100601c43c240348070b007000131a040101d90010443d06024010301016641000c45c2035103400c200c0c09243d46001d0f03c2e8401c04698480040040501a03201410400d0b00a0a4494203181083e00ca0405054550426106d007440000010300c0200500903071481d01d03009070241006440c3d0380d00410788078010b0300a0000e2000306201a09074030004226052040400d500c42c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 409944586 1250 409943336 409943419
    0x204050a020409060f030503071421040306150f060c0501091502030402091e010501080702030c3f180a0305120a0809240a0207060510210c0e06 63
    0x444080390f2040e03115440400720f1040804c003251f00801511002c0750400d9254a00180141d9054104a040c00300714030450050304e5100310500401d0054010740b8842c080c100002d4100281e0744d8064941880b50b41c0543c401100280842407103440c004059910802c0040f91010243c0e80b10580182c200b240c5c81000f5901208010940ca40040110740152040e400345000382464000c1a00c086014000c4606211144000c104860700c01c1081311504c03410701041e201c0229800c0c0c001284900d818404066210300c0034506c08201c01114580f40c2c10724411a111031400d6025404208a44050b4900d540d00c0080c29000002003801070000e44922082d803500302e95182650b01000d4540c403c068461035440c3d0000002c041600c90318020324802d040d800e89500f40a580c1c040c0000040d10a4580084c000c60403c03042c000f114104000754000d90b589011007228400182c5013a020200070b040c0003908640d0801c10402450685c215115001480503185c0100e090417035100c441030440003100d080320103006226 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 409945836 1250 409944586 409944599
    0x92e11071b030f0605041707060506041d0a231006030b0703050c07110f13051905160507020a0b07051e070812090a08150a050f0601080a09020d0204050a0204 69
    0x2100003152101c0000300d81d09401c5480c0c00c0d10315026844014030503603030307100810b00f44249481031442c1c61000c0d207042a40c50501b441c062000d0a000e0b502580680c1c00d1901505154202e5188014900541c50040c00d41402d95203425206009200715050340040702030000128410074888100c0d13030071515602080303142c0384d4030b401414417200501080130540b40500f4003450380001c800b105c1d030440e000b03490440c292200c0b40009041040c40300469a119200f181d08009104890300800c0c411094070580c803900c0380c80399034070a054440c01c81e40c20034030008951848414601130708c0607004543c0090882564030b500c031480d19078598400038059450307900c400020f44202c440d2a960300c0100303203910003400300189407004595580241d20b510f01030a003400714204520b9120750050a00a000d514100c5e007054011581a144200742510f51400300c82c03d0000043c10740425040d0300303000c0c44060b501c030582666032203081001000c0a00d0100c1c1d1101c011039a82c1c0150303480b40503a500500541400581d200d2230b210 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 409947086 1250 409945836 409945853
    0x515090f06040636060e13020c0c01021504051c020a021905090a090201090501031d0a0303021b0303060109030807050f010e0303150414010504050c0c0106030326092e1107 75
    0x4e10031604859002078400100d1400101e00c4111000c5041c070300450101e03000002c4200300c0150504282d5440400c20028541c000108101d81030700a8007134541141e80740c4214080c111044802408681c418050118601051241404120164419100c041095500080c0020b01c951040c0300044008a014131203458020304d61038111218030303420400c4e80700541c000b03410045144151414555207028141514403a80200c4c3c400f00c401405a8407040040c0c600903009406c02c0c41840d02e25079a01d60000304105d03000044278001e45050711f840c4501031840d500d01c42268000d440803500d5001c3e011b55560080c409019203154021800c0242d074483c6801da00d462035007140314056510940c1081c496240b40043c954140d81515002e460100741a514624450201d10030b00d981e1308900d40c44e000001090517800586841ca69070710040b521003d0001e034040b20000303001612441c9440d00041d03c0b0341ba807880b80c080c00702640b070444031007261024000c0000e942100d0070319510040401d0000350182c10401c0c0702 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 409948336 1250 409947086 409947137
    0x30c0309050117010b18060d0204060e06040f1505160f02030d02031806090616051501090203150108091006030f06140910020a0216140f03070515090f060406 69
    0xb0301c0c2c0744a903602d5288030f0300500b10040c4583e0b00c107400009141c03490f01c041016403131025000035200c2c0b42d13121351410384440254050b125850000f4644000d01d01c862400d40101d508441d00703141d04200f0300341007500c1d0015801e03000d0006000e0000803c1203803900380c007015038060124000e0010140b424128010306090030940d5426108542040240d041415a098040e40c00c002c409d03104071f0785a00000000c01c00c140b00340c0d070b45907004031000964581000f60018158154294824400c030560766140140b1090b03000966140c80000544190000e00f548904410340c0c2c0084034800312010110b1b142c80e04800c0780c03080c1d08141e4000080041700d10502100c0d015030894400444584100c514248186644942c806030810340d443c2c1d00000c481d16014030820141c1018240540131419141d500c5c60042c3c03141382e4080030940100803c202203c802d00d0041600e904030707070010f0041c0c402d18148483c40b038061303400000640d17130040c1c0f640242503140c0c0f1084c020780301800303490720b41aa604001000c1d8264000300c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 409949586 1250 409948336 409948339
    0x20105091203270c180618100b03010b0d0606020d0c12120f0218090403080c0f1306030614030604022206090f0903080906010302030c060c0102090301090c09060e0f010b0c0316030c030905 82
    0x280814403001f511196400982803204502c45092a140c0019407200030803907502c10280000044008264500b01c00010061000079103020414241e480c94166190fa0040032001c000c10660795011000c540c0070026200f0b03c00191401000c1c4c031006c880701d601101c10101408201c140d0100c0c2e000d000000d90051003c00c11011615a030151516030780090034131400801c0c08058410200d04843d100b2039010595000b11420944c0d002000d482c0c140c020300424051184002d40030301040701206500780402c1c0303640696000f0781101184100d00b8480d14000742070704141e503aa030780d0324000011181c103a449281420065400c012901800e0340c103004104030000781c407041280d0046001000141e80008140300c0740c407001d441c21038a035440242031071f00a0141c6d00801c0c0d015400c2c400140200500f00300000305503807141e0310401c121030700c81c040200ca04100b01e90022842030104018000c0c0300f40c0e10041c10641880d0720441c2d03e400c2d00c14042e080c180280ca0006c402061600c90114101908000c610015050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 409950836 1250 409949586 409949629
    0x72c0d060c1121090d02030a06061428050103050717010b03060a1a0d1a0315040507170703080705011b180b0702090f06270f0106020105091203270c 65
    0x2103044020b108442c1610310440b42d526401c805c549060001c00422350700660300708900340d500e48481c0d031449011035241d803244201840440c00502190410400f42082c0840c1d44070301400c140055000300800340485040c062052100000c806001050f00d001c2c044881e0b0440c0c40342060b4040c02502810768004844c0e4003285400540a0011802910159000908081511501145919810030305a900982c141c020b038031405888034030500b081c1d805144240100ca1800d41d8920010307118200c070b10042d07180e035000b01c6170402c0404e1048001d0030350760b406a0000211000c28010703110b000e86030401d845010681aa001e9a81414a410183d005041039941c0e180f0340f00c07841e80024140b92004000212100c84070001c591a070703c80f540e0003d034210b500110f00d1500954400106d80e03210085403034200782d240e180e00108103e807040c0130f140d008241d01001401d42495508444080b0f410081241071011040841c40307854030b8403105511030300398602c0003038404540328400b40103ccc030242c230180c40082c8a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 409952086 1250 409950836 409950883
    0xc02100c0504150f03020f1209060f15060d02130f1703040302130905120a031a03160b0703050d0516080906070e040b030f030c030a08072c0d060c11 65
    0xc03001545981402c1c0e8520700044d0700c41d0111001e0f0002d0080001140b0b1200000c1400d1801a800b442d00f5400f9502500403101c85a841c003010840b502d204079008008900f10004034074071800c1c0710b4050030080c80121005402c5c1049031000c40040e41c0290f004040418050300104405502f0405c6800c8610100780030718909030440e00818601e4000f01d11540e0010741d141440024440d00b40903000480b07003078400442d540c505521005001e8200007104040c01c19801c8002140381ca80020345100f001059400c1d400d507240751a40003207194010080039004d001d410004070800c004e0074420ba6119141602c07102d0b0503110000700c018140b0500030030000c5254000000e012040760820b00f20108002d048034046021168400481e0a00e8400d10b0321900070300c000f04406540f0240440600040a010390301e00d040d950350842c040724a01030b04080007400c0c100040c442e480e0382040c00c0d0100314282020304040d002141e580c0d40d040850714121000c20006180c0210000d001d42c0a12064114002056800500c0c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 409953336 1250 409952086 409952099
    0x50403090f061d0607020907050a090801020c0d050c03070f0c090e03090f060f0403060f05041a041e0309081525170402010201061d01050102010b091909150c02100c0504 74
    0x803a01100700d16050002d1983e0f490307990b80ca01c402c981e44140d001d0603800d01410001e001806503003002d191000421028074000c6441c541c14070036180b03407044050003402e0381299001e003520310360701541c02d150035400104a1400400d110b01100c6c10168499020100da0624000001040780c40d0141d0070005078008001c5075086076100122215a0341007151210b0b03884442041280320b81c400da0380024111824840c56a10f03100d2036030b000d644254020301034984840c3c203000307011211607001c0310020002c13001c40700201800c011204d50041c00c01c1c443e0401d641041e469a00140c078112642c0e248801d441d10300070411001c81107001204d400c00c0c1103004c418081384a2030b0009072500d4113200c4a6103614014400090940e8402d410000c001c00044c91f9143c80c0041d08400200034080c00d0003014090360801010248a00300a404540f06a6040098962502d00d55032290064198244141c0c0e25424520503054564200d2081c2511078101d03070010030125000001d0541643d09080141003031200920040000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 409954586 1250 409953336 409953347
    0x10c03020406270f080102030a0b01030603020d080c010b06040902091e060a08100b2a0a020603130201170703090b1602060103080307180e190506030d210e01050403090f06 75
    0x2082001420380404201d542c1000c1c440d1036443d409811300c0201000c0004481c2019030085008902e9040c2c00e0040e07144803001135080c2ca00b24800290001e04003907000e401303c3c0c0c107903015190040d08680085016001e080004400da007041e0081d08041d60300003403000b101c0c503000c20086803003000300305030b0410008003900203001c501078101e01109002c50346002074510700500070030002600c003044001d500c50b80410108507032070b45032840300d58003016892180c04002400094004d01e00d03600406561465070b8000303856000c41c241080490600040d144842e0600480282c200d200301c02558000442003080e081c604844080a8126007611490318803980c00c165000c1407440c1540d420030340e01c0d50307641c440072800c40c1c1101e030f400c44150350210123040101e902403008160030b020390185450300c900c4584c410030800445105403900c95040d40460035a81c0301c0f5012380101c8203040b2442c0c441e01c2043c0c800e14010020381e035240007020405d954803c108000c040e000810840038107400902c0380e858500b17045002c0c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 409955836 1250 409954586 409954607
    0x12050c0904090602070203010908040501090914010b0702040213060315171504020a1a030106090b090f040b040b060310090c0c1101080408190201050702120f070f060204080f03070302010c03020406 86
    0x4a0300c580b19981032290580460b00e54941c042c0003080250000d0509440507001030040c0350004c1c0c411140081c5500c032034001c601701166a56500b4019034a84101c960307280d441041c1c101d0308290244107850082c101418174a0007414035031030110380d0602881100c07003009241c1c0c01402c001d900e00411501c000200003046100c01114004024040c0c44d0340c0009541c0034076980c804038014241d407410f082000c50f410013440c12908562100924540c603510b142180c0d00840001503040400500b004001d803501760000c1c0c00c50040030707100056201044c400300f44a54003c8079444609003a03030340104454032052061031070700b85661510891094840d520400c50154080d4035604000c40382c07010400780402041151000c076201c40082409207040003010307010f0301048a100c8094014441d2044a55020a04403a140015001c1a80c40d00101e55210003641c1484401a18425070038800031500450422846a019043d0070042d51035014030315000b0309603004100c08204041c0184802c00015800151001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 409957086 1250 409955836 409955839
    0x2010c0212041806150e0a09090807120e042a050915070303020909040f050c030d0c081c06081b0406050f010c02040e01050709031e030225031208010612050c09 70
    0x400003000f0b040d2040103072075150000c0250b4071003a002c20480b181c0061004071050401d49080d901182e407289a0011a804804064900d00c4104007000014290194071401c69040d400d00350460500f110100b4200c1d08032510648003180c0d030242e0500400074601500644400c0b51038200e20303101c0f0b1480410041990401c80096146020416400b054081e805841c1c2507400602040c80924103030400d60310328051100f00361640e000302410452582004105401c01d808a501c07030a03a1520070b60340b05000c0758800c2c4503920010710312000340b100c555514041c0e000100029002000b2840d90f01a103242e8411125205511407460504208101d4a0713440000440b181c0c242000c018402d810700208014100d04004a001c035403800c000c0002c1d00b0f401078420b8060781d000b80d0b000f030040d00000149204050749598041c025034002070000445560a200006100c2d603461040001960340b40c0e01c04070580d03840424540441c0607400180b00c9164014130b0070721105050401884103040c00c4c40d050469204000340b05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 409958336 1250 409957086 409957109
    0xa0501061e090507140d020415091401030504030f1b0c091e0c23090a0b031006110601090e0a0507080102310501030c0c0c0f09230f190510050102010c021204 69
    0x414200b2541d9048d50f00408801403c0e518a40c200d01c0d004200042030300070880c540007001041c01c200d501c6441010b02c1180d054440784851404071200303481100407100714546a01803000001c0008580000300d800a0401000101c0e00c0f1403940f16101c00e03440f94440c02180035140a1a1070300d283c0e4004030390911443c414850f0300844a507410111081e20940c0c100c01d401c40b20308040019001c40080003035120341d44440a05201a4a50303000301c4540da000055000941e0211005100b0016103901080040e46908101ea41d02c0182ea030341c0c0f1781070140702d50214045950125041d40c5181c080303030041403281090901e480300b40d580d40145071010441402000d0415540f4643c1c0415603010b00c007078880c0b07150822101c01805940e5814511150494010201a83d04014079a4a030f400351039480c0c1c1040c074585500f400b0650ba240920f8510480082000b200d54580d2a03000c0c003000b50310700ca100e0241c04028542c00056050000182c01d5403059902c3c0c200f1540200c003800100a00300094a05544800482 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 409959586 1250 409958336 409958347
    0x60c030417151e0a06050402130918171303050a080d0b0609010f030e0f030c06011d04020303040e0a09020a090527030f070503210109110901091203020a0501061e09050714 75
    0x10440200f5590b0406c03a0413034800203480d000713407403c0c0d05508200c03841c0480520070002d005404210790850008002c20f2690a0501451030403019006041c100300310202a011269683d100c0600d030525080301503401c204001899407402d1000e01440c0e90b03000041e02c2691a03c2c111400091441013044210030030141d8030070035185040b9050000c1e041c11035400040303d4131100705561194480c00c080c400d541d0400c0d10b3386c0c1a0b90398030808010451244d074006028608280c0741123501500441b00404901c007240c0d46401d2a03005070389010340d20000e8030701c4440000c0e651500700c84100301c50341d0000b00b103e194404030180c541d150500008440550784114851501c9000c01e2030800e19500840000f031402d806850307a4009074181a885180c101c422380079041c07080800c2c08270150380703a01c6034291950002d0307003400c0284100c080c1c111302403199500c60303c11515824000e84441d4212112504603519058001403421984181150114060b155400c4200301504215002030b005075003008607409000c801050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 409960836 1250 409959586 409959601
    0x50f15040e010b03030307030f14090703020d050109060f05070206090a051c0c050102070503031b040b09040c0c0501050c2221030908011e0c030203190209060c030417151e 75
    0x3000d0390b0f003000682182d459041c0350303070041c0c041d107400e0510f2400f841c54000303001440046445150302038150040502440d40c21602030004288610304280c1c1c2d10f40d00d070b155080014a651050815000103440002158244240001d0400001403c0e5084942c0550702c0304001c10301c003068404d01007802010412100f0080307002070b07403607808107440900503501c0032800c2c000b4000c01100952190741340500c00c06044101c2030f20b041a80c042c82c040c40741d403100c0a1014030000d04059010481e800c2c25410590180030b01070f0740b040e0950b4022106180c440030045060003500210341c00103a003800811002c1081130741411526031200d0302402c410340c9401c41e008410002d00d805481d81c10b000e020703102d00130f1001d035142004402c0f07030241c5035422070b450038500301d031402c207140c420702c00e4a0081d49240e80302107801c0d4580122002039002080c0d1541d0020303041041d00000c1ca820401070004264580e007840480700c110001d54144924139040a118545041c200700c0304941201c50141500c9280240d1101c940303030030380d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 409962086 1250 409960836 409960841
    0xe060c0109061a090105060f0a030b040e10061404020c0a121b200604080606120705130902040b0a030f060203090a0c081615020309060904020706020a0909050f15040e01 74
    0x52010b81001e1034045500d0b80c040d001d2000e54840301050703510071900c2c1d1340c070414030030107200b00c0c2004102c245083c880c1d42055403207a0010015840010f1001c60000007002c660b03810047c3c26001d2244455542c05c0c10000c0b03000505040a91600468046040021040b0907a4942c485014020030a5901c0103182400c50b00443e110001d0303a14610b150018010341d40b4100f469000520f4040040581400f0150750500d0690215000d0300d1030000500400d8840206215040180416140407805001800b1800d40c445401040a4640e66000031599118a0041c070041310112280140210705808050011502141d810b01400c0d0b4042c000594030703902c42c0750440c02d041d031040000f055101d4041c2d0004500c8030009481400c0743c16070382d81e500c54544d0342207c11060041c548004000d604203120106032850490040d1007080800762000d8648040350b0b84480403030b481103182038045031420741c080c0081c140342c3c40f410340d0010314001c0001960903c2c0751047c0e80d00d05d001c0ca6044c03040d6110011603000d24001e4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 409963336 1250 409962086 409962101
    0xf060510030905070f0e09010516050403120e042309210a110102070f05010c090e011208040806100f060201020a05030c0319140a0f180f03021221060306070e060c01 72
    0x42845c40002c0d03d409070ba030b540d020b0694058901c0c2d8204000f048003840c882000c0d00350440c0c5901d86a103803510350365a82c0002ca844412407000c0c07040f011691480703a100c50082810350a01e000b0281009400b80740350b49005840030b003843c91a503000540882a9038071810210000301420510700b5119189500110303007858110100c100707194004142d14081100c0d101441958611a400a000e201085d03001181c1c01011841085240010305004102642c1c2c2490300b0082e803070140c41c00600c1c003a00e607030100d031130800141e80301c203c3ca44540004001045880b4125806450a03100951904c03860020041060002900d014050a4000045040001120707420804801070603414042c00142500f44140000b0846034543c0142c201402030840908501c40d08a1420a4a80b0314103150020389a4108400345084210706500c42c80030720714000680c85014020910340c044c0c09840c0c80140400040c150600a00018005d81c48001803003556608640d101c280f200054030445c0d101e402c142300486c09000103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 409964586 1250 409963336 409963349
    0x30203060a1a04030b01061e030b12250602030a020606060d0b1c03031104050303030c0a030212130203010c08070203031801060f0b031f2301090b030109020d0f06051003090507 77
    0x1c1c0340d942c80e281e0720820042c00c01c60b07000d000c2040c8180c2c0da5881c15902040040703c400d29071100c2501441140d8020383c0100340300c0601070900c0c00303056130590702a071400c603019010b1925020014129001d2041101068014120502c06581008820b60000c1d50b0340f90003800142c40b85001003103000c100070190380000e9000724020704045044810000c52031064140200590000c2d00308240c01c5444144041110100c90010b001503245a844442030710403900545e07562000c06800304003194034411b201503030740c2c01807003030741c201041c0300380b0300e00c1058216940d00141e17005205120b4200110b40d030b00402900d0b842308011280e20200ea0f2455581e41c0104085e400c4200090040308020510b2806c18014600c14016001307441d200b90354036607420078076403400e22401c1c507061a000c820b40a1680000028002d181060403c1d04030503450700c0712103d058000740c00c0750000c0365003c05d841110040600071000d0f0380d40800d808112050a2101040200c0801c4000c0d0041c107407a801d803081082070821404006020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 409965836 1250 409964586 409964609
    0xa06230a0c0e0f0d03080c19020f0c0405040b0112030915030c030e06090604140a06050412021504080301230a0308070b0903090625050a111e10030203060a 68
    0x300380019600400c1c41c6103a441c0002c02101d05146581086041e111100100404c101400d4540f9a011940c400c00140601d15002050184000a800042501d183d07821550081c140002c07515110515000500c840079118504101c1400003040300e074002070741500c000e010641e011615505041d40d000f0350343e038404a04202c0d41d00141e05043e60690041648820039071b400d21032032501e0050680e031018143c0d442c47e05908880301007400104860752000b00740b1501c0301508c00e000d00580b101000c43e20211000e03542204c120924803c50f5a040c0404c000a2818401c1c08080d42400e07146e044460105000b0f0340c230241c6104180c5005280b0108401e220703c2c0740104010b60158032440c11046a41004604403120803c207004035101140c04020780341c070b0b20303800ba05140c180b52604844103a43c17a8040480308050301131480042c0810f0080c1f0403101d0f0076005034440720b107161620092055034001c051051020a0040c03010510a60740d02c10040c1090255290160f102d44460000840f20306040c0d100300c00010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 409967086 1250 409965836 409965841
    0xa02160e0105100206041502071a07021608010203240d0519030809030c0615010302070203010c0309050709020936070c0506060d02130f150f080601080c01020a0623 72
    0x40c40181601c0007642d0100da1411424400d0760380d000c054400404110300180001070800d0145d000d0708036140500b144000f00074540164200c0c40105880d45401a00070070000034010122140500c010500e100086145250846c01c1804410300d802080100841000511060b5624028002c401b2604941512400000c0f607079008036802c000d9000b200421140c5000032804e000100507501e21504070307030261010356190041c2d650507070210254a41803540c00c1c0028030140c2c400340324414201420307032000100c1c0c0c011410704510300744072503105100c150300400c5a0031050722040780ca0309081d13a40b01c000031000408505001030000580c0d2110a01030702c810f0410039a668010348900758503000e1000c4e0fa071185c6842017031001018040401941284007803030959031181c3c907035000400000070014001007070a0036801c1807807500081d9001c00f4410b04d010b1024041d002082c8005401400004000c0c03c82070303c04c50000c3e440c0d01d01810040e011503a101182e5204540416050050b464092403414861 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 409968336 1250 409967086 409967099
    0x546030207050c01030b09010b1c0c0c11060c0a0201031508010203090303180106030305030c0304062c01060b1303021c0501050f0405010c090308040b0f0d020a0c1502070b0601050a0216 81
    0xe401400003034034544500d080390300f010350007441441c81c14840a0183c4685a00b041d112a08550010310300d003080fa00049400d030b06240c498481c0440d101529640d10040070745c00d04003902000c42c0090381500c01c070801c0015001159000510303020042e820b0030f0103d403500d800c51000c03040c00c502d5484020319500000c10001c0c0c50b00003000841c40f0b5403052400b02401c1c0421040c06080b01c0090100602184003080070440d0b0b0020003002c2c6901c181f00d05030210704080c152041c80010003070b4140c210040b455001c56800d00308400c2c02808050180f101003a4200592142c0c45521400c0324840a0300820f40c15500d4588008000d8100880e241c2100c000c1c8032034145144d42e00004107048070241c64a51070708100481e101d105c1c0813010200d0340c004010714182810500c10501c554048000c00084034001c205142c240112030019001151690301d618118a580e424034640c41403043c2072881d0b0f81031041180c03400264819145e2030b0040000c0ca015511100c0380c84080c1d00d018150640342e00005411007000409 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 409969586 1250 409968336 409968341
    0x41b0e18162102151b0601140f12331515070602070323070f02060306030f070801020409050c040605040b090612040609210203030f0603030403020603070306080d054603 74
    0xc03910a5052540d14600e030f060b103076481b82402e0040b0300341005003120f000d416150808005400900090680481c44469451940740400516410b000c410100a60072069450450281146068070f000d0640c03a2602d502c0b1243c564400e2a00e4620071000d200f03000030050118816640b2855010804554500d101c1c14068800d695903041c49400610007802c05240c600c03410b080c0c4001c5548a00702c039441c449550f003040b005800081c03c00da0135215411401c1290b40f02040524014441b0b80001a981ca0400c2c42e0a8143c0e0750061055020200401c420890170390320000301e42c00c403440040d5851f10385c0200400170300e0f140700b607182108242c0421000d20042c000340e980003c0c021441440c2152009048051425181000c05800009a0001d00002d6884522100c0302640210024107491401d034681c0d00141c02030300144e40703481c0082e0342d44c2d800f40801e0b1010000e01c90f0150307240c00d1150802202403030283c545d540b200c0c00c50030440f59550300410000b11142032034614040203025444c0c58041c0c000000c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 409970836 1250 409969586 409969597
    0xd1b06020c0307060c030215090c06070f06061e060f021615030b0f0a0302042705070f0f12140703020406080d0201060914010e041b0e1816210215 64
    0x200f809540c40000e0200e00581094000a5154002c0e0002e8a05090300034001400104007407114042c02414041c076540e20070003042214030400da6003105028500f0014126901070300030036501060309490244401c1c40c05044403c8070101d00d0001d080c4040c21900b282401c82d40342c0260070b02c041018021030110340b451218141690565410090b44c0501010050382928440e40160840d030400380c00e1000d4140b07504580d031881c00e21806110716542c0380d4901c5e100c444508600341c035160024081402180000d000c244010800e11a2a104071420600c69a01c81c52680e030300144183c030030803020b851901c4240183e500964001b00b040241175035641d415600c0b10f0181000300010351030310801162228aa2041140c42c840500301e20b030f0036a080080076000300308085c206a400000a008290405110361080c9002d400040303580e42a506241451051034443c840241c0c899404c40003c0c00808810204050201c400f0551100c558101c0e405030307485500038011001e5007103040d00c407010f850003100718000c10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 409972086 1250 409970836 409970839
    0xc08040605340306211401050105031b030c030a29101505040b03010b04150e0108150d05070306021b030c0c1e060a03050a0c03020c0c0d1b06020c 64
    0x6550b84164085030410042488032596604075100800c2111414005110241c0182000624581c64140c1a10003140071240940c01e4004c09440804001403080131aa0034090840240500d50400d40040d4a80921903114280c10b000c03500b0400580d0303420411020110805002c1e200c1d0360040e820014a20740c2c28805103c51020302248850001440d5503e40d440707204858441d00300e5504000402810481d0140c008040003828000860039002c644010342c000e04454081607a207920300400111044610100d000a114280701072a482da42c018240c1c81d44445105d6440e039400c401400025056020b000c0c3c0030f0102c2c42480d0b40801080b01030343c000c0c0900c502e5400b401c1d1002000303103c40d031354030b20803646080042d0b0800010014030713041c5402d407030708149150303030302400041445404500150448414400066200c0052084407040c600c076400250555113000d52034980c00c945281c3d0303540d0702c00c0c1035140201050841071040c000c0805501000c51241454110a2941c0c0e80c0e000703548003031071080303903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 409973336 1250 409972086 409972091
    0x20f0712021f03050f090a02091303090b040f050a09050c090d050f01180606050a0303090603110f070b04030e1509130e070f08060108160b03041529040203150909100c080406 76
    0x16006c0b11001500c0801564024410020341e981c01d68005001c2c10300450031414012a040003190702d64000002d000580003812068110514090402001c1106c641c49820024a0901032101c038548030b9046580c00701d400c0d1a540c041022038941b41c0d1030114034104001d9a946421850540355020104034130110740030381c10070b2100c140c95904109802ca558800140401c400050400c00d840c02a00165407005481c1c60380c0d0300f0202c1c0b07180c181550b070780104c4046980c0a00001080308250b00039410b00b05001e001d9865264515150344580c24a1050442c420700c20842110301d014400303da5000411451240310a032920a95a079418064450b00f5001d1074442c1c2c011b240010035448400070718240c0b8002040100001945402c00c9034945910241050311441e604210000f0400e082c0d00940a018222078800992071940c0c1c14400740401460006900c550300410520400201860f4001d1060108440400b02d985a60906515180210755451521800e110f201c0c92210303049070700d1920407401035006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 409974586 1250 409973336 409973341
    0x140d0e010b06041d1f0314150403050d1107020d06020a0f0c0309051c061b020705120334050c010e011b03050f0408100b040606020f0712021f03050f 65
    0xc00c0481c0c0100d0203841c1da01400524404414884540801d41005c2c0010302c003c00c80c00c2e11440e450054115400941c4c40c001c44500c0304141083c20080303911288007042d820306103801e0960303006005124584065070700d280c9511842e801d0f42074a10840d90300c2ca600074007010b0710050501d04040079422081005010070695040b0b03c04c0c9070f02804001e4650369255030727002d418070b0034941003183e0380c050a00202d0030250800c0b11070b800103100344560001005c0b55641468054400c0030000e2a046180d0070150103054009281c0001d0702000049e00d07030792080306e00c4038105000c0d481c4420400c21840da128641039000c84406406025001ca83c60241d05d01c2a07890840c1d0140010044d68840380d05000c43d605440006995000300e0310070780141800308118018180342c50303610035081c5e00d0036101c5100c0d101d65030b039580b03041d6800c1e1500344505401426980050041d44480601e0f80c2c2d04e42d0700620a04007448003600a0004554075201c01c0c010043c1c40c41c02d041070310309552400400a08044610a03c8059041301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 409975836 1250 409974586 409974589
    0x5270604031205040f0f140106080c1e03190c060215010b0d0911130e0634031b0201140c09030304060e120f0f010f0606050304020402070201140d0e010b 67
    0x152548900d815403a20958904611092402810001d1003669004840c2c0114070029000300341182e211800707903014084c858200d4100c1c07402c49001d544071b550103510241340c3d5501c80c1c80341c0d55020640080040f45030b603501030b4030000c80d092081080ca404403030340b03c030003506041050200141c02502c0d140e600310703986403017508e008031401e40e028010108403000610921940750015008002d04034864010745c1e0224046c0c00c0801d4502d1000b07060010283e40381d225035201454104041544049100103006450f820200d08120394405940014485130240709110780032030080d0040e107032810700604006041056040001e0080005031401d8403420000c80108a1180640d41a6240130306c2c0140074501c0e06140c41d00c10b40d107801d1640d05040d0040300c100708011201500340b0051017541d2401000c3c260081122500e282141c5030140410301d11454480203010307042e4800243d81c0e005605070360041c1c1d82c03d21800161500c070f9024600d0f4150720000640c109007445d01d03400c49002e81c1038100081c40b1a012a50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 409977086 1250 409975836 409975843
    0xc0b0105090c0403080d090b0a1d030901090303140903070e01050103200d1d01111e030f0c0306040207060e010b04110f07030c140a05010203070f1706090702100527 72
    0x2c52042c8010828803091001c00c020b240206015844003400140d0400c00740e4807568111411280700d41c1065541c0058202201e022120000d00710800001e103152900110010b4174240003800040d08204204182c0441200d00e02c0480312513010040455141540c2c408641c18124000d008950000e4201b4840b042144118078250408000c402076a900b01452503055100900d2032488071002c402d2000d002d40b00e460001c0c45070445900fa40c4c018a036403124004003003405180b10300e2401000031010002c1102e02443e5004031504103460302a081c1d5079856505c005800390044030400b901c0f4625080040400060543c0301907454401035805000230350881620895500915010b00c05280d42040840b00003407142032064455407189110051000080d402030f45803074000d06c800c03a010380d400410f101d840b40e040801c203240c148803031408007181c80c030211401c0c42159010b00820700900900001c900014000e00c56594891030001c01080b0902c0c0002080291150450840750b6011568001140207030022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 409978336 1250 409977086 409977091
    0x101a0f0d0f060b041808030702071d06040f0e0f0f0f0a03020316170304050703020a0f12021005091203030a06060509060301031103240604050f01151d0d030c0b010509 73
    0x4051021030050549590010740035204000358804d80d03500040d001004440c0710a45c1c02d600400d05903460746410300d400f900e0118a50010780d401c400d5150301180040000c1c2442ea8030800c156004240411114072040151010312600b28580c00fa0070b41d040300720100000c4400d40101100203c03802d2909a090710364580d801c171100500141c00800c0325001550503e482e00a22a114800d42c43c2164010084240d10b60001e80301101c83c3e400c002000c00035441c0c02c000034405820303e026000c40c45071800b0200058241d05450003800b820401003802d00450140e002d072200c44501030a0300d1011400004101e40301e500440c6c0b0f000404e4502440805c401d0703c11000e450701d420300a004d15185074210344400243d40c0e8002c120640c0b5101c0c0c400c2d8640b400071000d802200555550600e4001d6082c2102023000b41c840043c0380d141030300c81c508010031482c158220b05043c2c03d2128100890003d920100c0d03d44010500d054094214516032045c4007095880f060004403240107802004051741c0301c0c07042110340e0a09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 409979586 1250 409978336 409978343
    0x24091103070e1603050907051017070509330406020c03100204031205220b0423090109150302040501030f1506082e0504050c041112010b0903101a0f0d 66
    0x10382150f5600c501036071203c0e410084040c03c44a81594580c00601c8103886040201c0000c0d0000f00c1d2110036840390602503400c41e07200e060481c101020034020464031400120b403c09001d074242291600085030b00c1c9004811004550460b590300d842e0351010b075031103640c2c1461500070300c01d0442d120700404040c0b00381c40503203a1148003030b04104070140048560342c101d4040348590007403181210203504841c0d041d0000a01407410007503155032070030b11034400d4140b02400e841d035084008140d200e016501e103441c043c1590800300e00010a003100340d1070b14401c000182c100a404c6403600340080280040d480b46410b46500c14943d1803281c1081d564024151001441110281d51106c0300d4000e060840383e104070140801c40c4125542d1507115a420415548207640036981a0804103501d90795040900581c4900d240720b61109142c0390b03440186ca15070010501c0b405013800000f04030711300e16541c2400303803c4042c00c09485c1440640049070a04100e2111003000a118403002c043c2c2540d40e08041900c2500380c0d40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 409980836 1250 409979586 409979611
    0xf06080d08040f0623010602010c0e0907020d08070c141b060c03040e070e0306040309030201090803091f1403041a0f060904140f0a050303010e09010501030c0324091103070e 76
    0x142c0d40c1c40740007030402217010001d42c0c1102c05a402e074002d42ca82c1018000c08907580085040552000b01401d201c4842001501a0034650304200c140c540028014100940070326007005281d8490408440d51106136000418164246000f0442e0510000d8000e85c80c9200f440030b40040710240f41009020f2003a00d1941700c8680003444100000c8040016541d40203442e810f2500b0701080c0c1d040060300b403d0301100d0031808503038800018025960f01c02444000b03069194000d51400e24a40b00040080c0015070300400e0380340e0030301c1003150050b1007101c0407108030480b842050f4890410307240003550803110101503504c070858900011541e07001210350764060103001c1c0c00c03070145446030384420010385950444c080c050710a050035030158501c100240a442c40c00382c1c0103580c4079418100050f003008005410320321942c2c1011f00500c003099626910b0000c40b84d000d104020a6049402c2044d203407401031a5201d00c09240c0144001440b0840642e182080012019503140307603200d48200102c41c80503104d140c10101c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 409982086 1250 409980836 409980863
    0x2070f0303050c0f0d0815041404061d0115050d060e0316140318120115081b0a080d1809020409090303180308130303060b03090109050622240f06080d0804 68
    0x100d03640f2072178240c048080c1012604070b0307106400010154054400301d403c633030f03901151982d042c0950324140c10001c41c0d900901940070000d42886581e0014040c0c9440340760130200c0340f0708020b0700758084a115030090041e2500d480c03611a50040000d96094103a45261840180c0030503450084200c41401c0003040301030303003219410300901000c041082d80c3c001103596602640901c0d007141e030f80503a00801200000b0038029079580f900150100c0c041e03180c0f900841c40344000b4031403440041040c0c6402029450700d00300c1c0340c0b001da10008001603103034000d81c071031031001801040d08030346a000030100500a46061041801007000441e01c41c4040700b01500241c0300c0e001081aa00c8000380b1882e0150003403401288003901c0b034104920503030080e01c210241e0f0395980303103107400c00c201800f0490703018441c201c0494180c8a0b410b0310725041300030000c0040144080c0120300d20300f15118540078403440038143d02001505048810f01c40104150300030b0307000c00e209a020a0b48924400c5a07018401c0ea44120405004c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 409983336 1250 409982086 409982101
    0x210f031302120601061202071205090316030b0421020a0615050616020901061106070302090109030b040506010f091a060a020307020d0807020f04111902070f0303050c0f0d08 76
    0x982000d4489005000103000e05009a5101c8420100c0d5010030000f9201d207516001c00680098543c02000d02d1031801440068003040801c5030400101c0303000e0902d42d50b15007502c00068240408c014580d41c00c10310111009c014008050078141c403961049501580c584654a0000c5821203048692070050713001c02030301c0c1c0000d48544c01201c0d02c514218009030500e43c0320000608541c1105601c406940d040a6011007985010100280180304500703011062080c91240140c039448c00500010070705400140840c1c6d540d03c85d080340c2000795006943c500b524102454919180c410070f11503052004101480810100c511344203001440108100404515a50109100f9690070404003001940018445100541c5401d039081540d03520800c031307007030380ca501c02d204010180c7c0540c2041402149051080145070002104a5015252924804120031030f8500c04070b10b4480c042d040b40d65110f01a40c0000308064108000d041560030001c1521606a91000d01c40d564a405581042c0091412000324109 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 409984586 1250 409983336 409983367
    0x4080a0f05030d0f0504061401030206040e040c0308040303030c020715121a120a050d03020a1b17180307050d0320070807032d02031b030102190903020321 68
    0x90900c20820760742010f038404040c00c11036560070300014405840c0d1040000b0040075108804051616418100307141d4115000300740540924065500e4007212103000c60140100c2502c580000c685c0404030982e5140c8924000f8081d141c200075142c007501c500c04000c5603031050150070346480c40541c3e80b050801410601000c010b448616005111403035a9503003152640c0342c090101009031306480c020041e01203545451450828941c100c2410984140611800a0b0b40400248090303d441e0664414029003810014054140080030640303681c00001c40200790aa0784444600240003182230780c0720070b560707101070018810420714020002a118a0003c620400802102c0718034105102210300c0c080c0c90302c01540c0b03001d000390010386011070784000071401c02c1c0d00740244041d08032a600a0340c0c0a02c61a50109540391843d4075400f0303280a5815056603181c6095040d0ad403850015020919500e010b080c02034410749142c04180e011307002da2800c51001d44143c916010780084072140c514034142e50111035410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 409985836 1250 409984586 409984613
    0x60e040b01170c1b01020c07150201150e1008030f0f0a091a04180b0f0111191103070e04050307020f0a05030a060515030c0d1217070206160504080a 65
    0x144a003510074040c02101a00756944500d12640201da6203500307800b224484c4801c0300750030041e00da004106d440740b0401d002c0b552070222102c1541845804107031400c26070141c00d10ae118403031642400c402c0052100c1059181501800c141140c0707242c581c0d01c0e2540c4540301c0c850188010300146041050000303100400000f420074003070618003003403883c0d00d0300103d40107440c045802409610740800c06000c03007529415502a420740740c11041001e6480308001c104283e5280580310706001801c00034105010051002e4803020b40f010300d02c1c01106403580b0f4110307042c0d03060202d002d0183c0f19401010440c3d602000301c1e24020741d0004011810441306038200310145200c41c540981120b01c4010000c0d041e03d0030421540c05910034400841c4c1da00e80345c10303019401030200418034800c0e40403c0505090361183c81c080c0c1409078025580e0507111070410341c1900e00d14421303c031407203681107240d0400c00c0c22035010601030700921500351080081c07040030343c084609008602480502e50008812800000c03080c9190300d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 409987086 1250 409985836 409985839
    0x40b060c0c0f1c0b04060f05040b04170904020a0309120f080c07020607020d150b01140a08220b040507141003020306040e061608060405010e1815010303031a0a060e040b 74
    0x2111003001c120048883c00c0780420886503540084144400c1200c140035440505481c0142048146046d880320301e000100908080d14108000f100d203550800158101c94001c40060070a40d07a50b04064001001056108810341e4400b2a030014040c401e8032605c03501c1211181035981c01d40584510145c81859403103180100d81c448020054900144c4665a0b1608501d0141001e56260580e140040d02642c4400740b49070b042081031040300c20181c480c0c4003994080351092914100c96910f10f005c41e18546600b4101e0f0300300c0307040c1c41c030701c24100109503400c2c5219512a6040e18003560b074034030300203540382c016101a940c014510040300319143d200794003541d030042c00100085550600e00800a01b49001503a10004031080c600c42d0107211904590301a400600580b0200003075803401da105034508401a010010074400b5204179009140c0401c054012612040c2090581d542c2d40e00d40500200001c83d008040c031041e4612184688c5441c072030035812500661541180c2e00c145508200c010144460b805 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 409988336 1250 409987086 409987099
    0x30304140106090507030501090b0a06050d09030905060708070507061b020603060102010f05042f0d06092414010501051602040f1503110f030a051504020a17070302040b060c0c0f 78
    0x1035109214003e542c05145c05440006055040c0058041583d40c2945094000d1034140c00400000d9031000071540c191440c0c0c5000680002e06260456200069900c001d40c4001c0202c0c0b0f010601c40b00000510449105004417040b541e520031041da810340b02400400f142041141210025080680045601000520001a0f918441c40140c0121002039070140d403d506942110188907c94030fa4885010703400b545000017041c118400121503c4130a90001d040d152240d030081d0400c055000780c221130076400b01d0004403a0f40c1c41201e02009107081c28041380c1d080050800007602d54001e0381103804844030034842048500d125024000542424500e0681c210b03900d1104920782031840c910300020350f1152001c0d000300c1038010b040081040d08000018803a070010480310740003c40000350300f0b000b02c5504110740368990300c41c00091142d4125034800701044641c020304905500380803408001f5240300f2601080203075220030520645000b0103080752042d9000f070b07190104518001c2c410400140d0000c1c0032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 409989586 1250 409988336 409988339
    0x1503051005060c0c10050f040b09030a0803070f02190b072106030308060423010311150c061e0c040504050903070507030f03030e030306010e010509030f12070b100503030304140106 79
    0x206645500203e058030441d0400c22003902107103801802145c00c001c0905d8414103001d088010786d40188203070300c200c96507060300050521003074800f84840c858039500304400c161a842c00d00000f81c480c24030490560014058045044032181d030b4545a0090290800d03049480780e518540c040d100382485265003406e100a091100e01c4204650080c04050340c8030340d90b4190203041c0030302444241c5880c4c056001031001c08500c48500d07403a4003084035046035040341d4103030208822800032840500810242c01041200003402800c481d1001482600a15811032860312205000500400044041c9d4001401540c2008100308518040c0c002d40c0e003020740303982560310f4510550b0701d6030304d010410b900c00c9a406045801c81c200345a050311510340d00c206a00c02851840c41c0c10400280328403c0344208a042c40710100759080181c9013000320076214a850741c2254101d40c4480101c2c0c820ba0041402214802c0b08040060888002156260102d40d07001d4000c1d429522031f44d940400724451181804415913a0307000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 409990836 1250 409989586 409989589
    0x16030509120d05070b0108072909040204090501030b160801090b03100f051b13050616050d09080c030102090f01051c0f1506020a0f0308180a08030612071503051005 72
    0x2da00c05407000c588039280c0d11001d0740b03821001050305901ca420310b0b4000100812080b104a00c003400941018240310300380c0380151405102c540100c5c1c9002e1340003032000c034021a0052070f070389c021810f030f80c002c10f4a03210f295038519041140402001500d000107200c40010051f03440c0c903030401b1a4040e4020140c4080300d1404136540c00300d071155009000301a8840c0c05005c4980000560f016007544038282d924a016220500009500c220b0f10a56029200008056001c5141d410704081c5066119040c3d481b41801400001c280d1680c0c2d0007810001d00034400540820700d014400c4807240d0703101422502210f100c000040d2110f03007048000701c0300b201110031030660b004a207104403040c6524002c800541200d0807008410054a02e811420640d405030402c10045103600038081d01d178591516003004030340d803044406160490f00c149108254415041c19008000142010354803408054929056410030b2104155441d483d5104810001502006000c603151203500000d601170f014840c4840240da4900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 409992086 1250 409990836 409990843
    0x316140708010207060605091003031d040207050d09090606110c0906040209180115030207050c0f13090804031709060d020307260711010b060f1e0318070b1603050912 73
    0x1c0444417259142c40512103854603180744d603006140910362121450442c1c0d8007801e803003092840040019240c040c100e085070b0f183c4e0110b405040d80301c0140c4081e201d041801800c03000990141c01d1180c0d04100000c99111722440448400542c1d43c1c00505120084000340100140c01400d042c0d04030341c00300f181c075a190b1034042c4440c0304840c1800144003d5803401005480440e44080e130802010700410000010650002d0610100f4000315072140e201208103001603107003289000031500722810030802d83e09002c0004064401c03603002e00c0d400003246003102d400090510032000341a501c2102401050200b10007980074551051050400da00500c0d4540c1a1100c1e00740c01000140c510b400e908200103207154803600b003030750903d990002407040e001840d00103003071030007000c0c10f0480c95500401e0b628220380c0d415107030510903050381c105a6a28205a0040c0c041200c40e800400c5a91296090000326100390341c0c1119907400f00541480756400325035404031815070100f208180d20402030525201500020b2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 409993336 1250 409992086 409992097
    0xe13230c0a020c0d030f081e0c0c06060402040b120a060306020301090b1804050705221b140a0504090902060714060702010c090b04050d03110703051e03161407080102 73
    0x816265407240210032000b468143c114030400d000d50344580b03c41c0002a000b00c40c4080c501c0040c10290f003142d0301d01681c40701e000e005220701d00c050038192090102042c0040c006086854130101660780a55800060005a128034890b45190010800140000001d040440c9800c4004908089411562925203005a800030b0308001841a6501c41581c482d00d0440700905007041116402d900070320b0640c498503100c11507840707201c0c014200c0b5440b4020820940c2403403440c1140c0c0c01001c02c01d40b40b8408004020a46592108020800141661803551080c5040d921042421756540e0700c0d0500b0000c010700541010f403030490300903c0501607400000d035140d0700200d00b030100d90010315151070043c13030090966601d411490305000e02071100b0f1018084880848003500d109403100c101d5001d10b450201c40c8540110407412aa02518070048100100810030807910020300c1441c0c04407001c3d5007803540c0c0368443d41c20401e902e1035041c040c0e140050945a00603058101220582c1c0c1110755400440d400da9100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 409994586 1250 409993336 409993351
    0x4090b0d06020f090109091b030b040f05042303191209050105091f09020f1e150901080711030304030e240306090c03010302010503220212100501060e1323 68
    0x20886407131a50303001240d40001e00000030103118200c0d100d8805800a8030b81410b0000b09074980309000515251900644034076000700c04108264a040d007080000e0103805600100c0104980455018040001003503400b03804e42c9101384c440d09020703100b00342c400940c0d02404611198640d04100d010900a10407144140ca200003c0c020402ca51118920805a010000ad601600c1e021661000d80c481011280614006560007404000c0c000310a06415070f00400b05a40b200200344108648134040c005010f2a0b14203889400d01500c1d100800d072454a180700b040320481d8420700020340803d01ca01c00158503a240586202003105028200d440800c20842c3e0050f10030700c00005000b120308064420641c0500c1e02c40c0d603d400c55040d40d00080c421320020340110000200c9246600c04400491241029550b0041110803500582409141c031a2102c1d010507140e10b20b003800018120f4003030100c0083e00c03003000b401c6a20035022402c45030024400f04000242e0f00c440a02d50801c41a40020914090180f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 409995836 1250 409994586 409994617
    0x8130804180b0103020c0a060515040e15070e091f08060c070309090504030503010303110f0318040b0a050310150b0c03070b0a11120a09020904060c140c0304090b0d0602 74
    0x640000d003400395100c0c8582c0307904051040148400f02d140104044107965032002001c20b650b164041d100c652a0901c035605507009251480360845510006010014040d0003410260746030348016041d603200086452440d001000d4000080a40041c2024140c081048030209040340b6203509a880c50f00c1c1d000c40f2200c03405103000441105150b088605c0c1c100806410405000514090b90014200d000600c80142404145a000c000002c01404246041c00c940300c2140d80707581c0f026041c5403d49185640c8a40140d1030420a01c8450600380b5403002035401c007800400844181200c21002481e851440e2007030b03411403142c0407039041900f400a21400b07540030b004580720542403e00441c1e0345d5002c4c010100c1d0711714000d000042e20170802c060b078204425441d500801c590310400d03100007500703240000a40c8000c5000400080103540e81c03201c828120301c3d030703101032200e804a181c44009214a41c0c0d87c2840358000c1c4420054004550406070344c0a10207040d0080540541c0c0da043c0c140d8011100b081d58921 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 409997086 1250 409995836 409995869
    0x8040b040822151b2001050412030206060f0904200105210a0c080f040f02042c1216110103060e090a0302010b01090b070210201c081608130804 63
    0x40e807003441000f5000004248000444c05a6181e10800c50100b0807150b4040c0e0007844d0641c01e030f00402c20341340201804a525000300403585002502c5000c2202c0e514442e80418103404850300308070302d11f41e202d20b030310448510840c00030800d1007904a10500a00c0e04000040081150107046222944d0341261303090320182c0e40703092541024003510b903101e4034041004880d50070000702e089035608194129030004d51506003403040e03001040180c80c0b10300340c040f071107120501002c4958800d1000210150b0149040e206258002294040103110708402001900410101040468101003400240c04814100021101c1d540c498120b401c0e801203994081e035820103031041092640a004044800310b0910300010707403506000107100c05020700240a03005240d0782c81a8000140212a49138626a101c0c1d5140925001546c4071951020700751641e0b6403292880c000c00007071078040c2d035045000e0442e807402c0080c0b840c51400200c9e5502c41c020008000e40d000c4034203400128085c54000c00150129010304003019 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 409998336 1250 409997086 409997129
    0x2306210a02090a090308180a061407020d0201020f04092a050a020c0a0f0e090f070807050a0506041a07080f120f07080903041a09100503061008040b040822 68
    0xca4014200f140003810100c0f6200040e601200142d8005800e801c2d022851108031240352034010203100050070b40e4030b0088480c1009518032002c80c4184156401c5801d0070b81d015204a00781d002e00c1c0f421441e82002403205218014141d04450701042c1c01003a4401d4424903581c50b581e00000010754007011840000c0c2412400f40d05004e8903d0044090b00c0c0091000d2500ca803140391a215403046602c0d1003507000c0032a080200500002c0c615140203021a94842d448443c1207495555502c1981d1003512184000910350503c3c50036101101d2022010305021400075000c0c454a500241c8100c4140800704440034605264201420300c04020b06030005040c604980785903940040a40000d0901c0350000c10410f4082000007103505407a0100346400d0200c03100940d0520501420204c2584814454100c88006a002000d9403244000302c900041d030b1000c0000940720700c0400d0300c000c1c3c0304140900014020a07150001044040000c5268941c81414410450046d20003504200c0c0c24108202820019 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 409999586 1250 409998336 409998349
    0x6090303040f0f0f0e070528090816050d1b03050601120c050402070b0a0f0e060c0a0906081e040f020d0501060602012004090b0612190501092306210a02 67
    0x4c2d02e500e8880c1d01c10281803000c1c00d21007090082050081100008580001030036044690f05039941000f03050340c000e040c0000c00b07040d0000a019030243e0340308058010300c0304141c04d00c200c01240d80c0500a980380ca086030b12640c004001d908910008008a08400000182c04011580c0200503500d03210140038003525243c0b0600c1703425405140700c2c50040c41800b0204480707011517900b008400b80b000840c1701c04841c2090141c2590840c1c4580c50180c607007080340c5112030340c0017040c0c6000396a890a803101c0c1c6641003602e60304420340740c03010102c06110760b440392030080d4601ea540041c01346100001805060380054000414918204c50f0760351036800820411350240030f80064007081c1c150810244044081031609402070b0f21070f18140d56190540070400c1d0301d86404481c2051415490400c07140307004010030380c60b440c1d0988048140ba18010000a03007001610030307684100025400030b0301035080d0080a11401d00081e044c41da11039643c0c2c1c002c5001d2580000301d030303040e580c148010780b05241083c01007121 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 410000836 1250 409999586 409999589
    0x30f05130527101d040302030d1e020a030b041506020a0b1b0301060f0e03061e0406090b07080103050d08070503010303050a030b030f01060503100203010803030f1e011202090601020111030a0b06090303040f0f 91
    0x10320b030b144014171002a401206650203003a00180014003006412108050501700b80a41c1c1d61036440010040e4411780e05402000d0100c6050f14180220740004224002c240d071284034880040c0c210b260008005088103d201d41c00a160310a80110481280c0b01100310794802e1f8022404101507080140d021074008040c0d000104088000c6c003081d28001180455050708282d82c860058425000202007022030362001101680100b0801e080349080760001d458840c003070205450920070800039040b02441806124410a010341d9000d0469107540d0341501c0300d4000002c04000d064840710303100c007940c0b03040003000318440b50900017003001880e060a050034090509022a02a4010001401000400805c880d00318407820303185001d030717500c0d00710503c04800e100c02d020a44484040c00010082c0303100d46800310680c0212140d80d016243d040c01a800c0302c103c40d040220310b003001c0c800202c0c200c513203502c401c2c12000090140c034544045580000e0131940305401003142e01901900a11134180f0700d00a210 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 410002086 1250 410000836 410000879
    0x70e12120a030905030f030a0605090a0b011704060b09070f031505030c15040e0f010614030f01050f010509060f0408192103020405040207050604030f0513052710 71
    0x500001103401240c0c03054400ca44103041d20f075160902007100801c22200d01e020310f960704075260b041c040e031210302520503881968070400341c4d04040703035541c540c0d446102c0034508140c441c003010070150300318020115001841690501ea40c0c0643c0113081d2144222144a40c15507075507041800d10b5000050304850301ea00c41c03003034010120324062040b9100081c0520204030304541e01c0b02c00d8074854603810701780e00c100d8114011303e01480003030004041c000c240c0c8038161400d0340c480d00601000b008020403940400c40e00c40d0300102c000d5004100d1820000b5005e0740c68441031601c503261078192070118045038890000224100701c0090308002c0342030f0a01521440c00c0440184c01c150345803588031040d40c5516010700f00440c21180c1c0170240280c0c0a039044400130315005e03000b035490784600d062542d00e8240803901600464100452802628810301c101c5400000c184070f05000d00741003900b840420380b10040c6003941c0c0d0314461000d418048000c01a1486500381c2c644e0600c3c81402c0c15040c0c501d40001e42901c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 410003336 1250 410002086 410002093
    0x210b070c060e0a02090112080408030a0302070606090902130c050c030a080f15030318370b0309070308070204020f0301271e090201090312050702040b0312070314040905070e12 77
    0xf00016980c8040c0681159040210001d002c1010305041e07820f8415a0b00001c66440002881000180c047d00a0820325008410422203d695401244150388100034025403140007500a194010000d82c41070f604401d080c40e00600f000202c100051851380100c0700c5c14042000c003020082c0e0580d02e20100d560000d0310b999558100342c0c1172000309a580c043c00440c602070b80025030100c4019265416039040090f07404040c114080f501e40a9050501032210602102402c0c030708021030450080c0f42143d000b0f20a00c0000c0c10498507688844010380c21400040781d200e6000c0002002c3c88004102031406441201d090008100b00c8210600300002c6440801d9040c40c03e002c0c820400310807618082c9500d11070740002003244023103407004030b500d0105600002d050810714400420496031003070113400524400e4130b08014015001041590700d404d601500702d4071501c10004140000d203e0242c0898044000c1011400e05854200c80c0c819150115052030026982c0e04c1030159070704d4145040252141c2c4003024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 410004586 1250 410003336 410003353
    0x81b010c0e0f0a06020a0b13050a03110c03070b0f0702061e13090e0a0201080702150408040503070f0b030103030e01540314030f1903111201210b070c060e 68
    0x651506c0750402c002d8030780721400002030007002221120300f04540d4048269000b076009850f02400e084142d003050030b135030310644010300c4041c1400607061047e510607219041c00c0071904290340101c2c0d4000c0d4800c0380c000300e00380320f44040b140249091004490b00200515281c940c2250f280c1d642c050a41c0c071010015040c540e034040c100101042d16600e068080c0b9000e041592130031000c1c0d2518000c1d0b20200660007844e0100710501c410340700170304241c1e44220182c6111031f81d16102070840703603080e00a11003035081c10801040060b010700305059075084c060400c161004000c0704200070130f11f000e0710b002c8084480005030402080e0990007012200c048504801c0b548818070100c1c07044010280030080c5040c6404001c2c0f184807204000340e0302041c2540f00c113655120f5000210f14044800c03120b1250104c2c0c01c020408168110490980d260f0441c964000f2084c4d038032f0140b801100d12070075552400620583c0e14100c002c148406035080c481e00c005c0c2c68031218900c00f40f074640212040c44c003110090b600042d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 410005836 1250 410004586 410004599
    0x110303030408121b0c070e0601210c0c050703060609060605032215230601090312180b04061709030307091205010b12070e011e03081b010c0e0f0a 64
    0x54030300c031100381d2840c800f1a030307181c019034103000c5650320380a07024401c04034100001d000300081920a95034050200c4081d91500e0005480c19502e281d0f610b1080c1010781d441c6101501141d0008584102500e4500080c1e05951101c1c0d0601006410a41d40c0a0f00c48a09016100f41b50151200408a92070064610700e85086200841d14100e9110016180510340607018410300d03404020100c100e52a0400c00500841c44155026103607d50b280c10410002c0001101580198544421660403140420820f122403608407000401c2111605180c0c09114020031a001e00401420151401d030702d441c0b80b49000003031403202c00d0100410f040c086610400c200650168801600c4040f260509050103080200c2d1800300e000d801350403455504070b09500c9400d180810006400000c0300c280e41d83c1660241d0f212409035001c2030340c1c500b00b0307118070740c00420030000140440c0003084580076185201500081386031460382511010b0f21080d001401548003007201b0710f030000d081d100040089491400c014607245 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 410007086 1250 410005836 410005853
    0x6050d1b1a130f050a2903010b0d270b1909080406030f060311060a031103160f020304030302060f07020f012409180303021303060608150a091a0c0c010906091103030304 74
    0x518486105080403034507542451b0804c07013400720b00180d000f5200d60311000e020701c960b00100c80e5a04040c0c02e0043d203001c0f0403a86d101044022411018611080708103803980c2480b00710103010f2142c280200c0800800042540c0320b46641148180c0b65150385624120b0010f01756000452122100c0c1d16152042001403c2c00c1084040c84c1404d031071147d2203040800b0146c0c003c0502045290b08050004100642d20030703207403811f41e401c26180d00c81100103441c0441c201d83d070b4042c901008016038803041c00b05030365141c600a203642c489038500c116520411b0f1551000c2c00d580078441002c090301d2620780c0c0001090a41d03106100600380e10391041290364400110f0501c0c4070782181c0040c00f40340e40040c1d00902a010700103d40041c5800c4075090080c2691003241c59900c1c2d083c1010301c2940303d0900d001c201903030210300401c1e5481e80c105090104190700d4002c0c543c004440541142c21252040090440c541c2003800f0b4002e540f03026000c00a500040c5082c01000d68040c00e542e0b40c8260020002c0000184509 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 410008336 1250 410007086 410007089
    0x921030d1b120f09021207050a0e0c03060409021f02070315110409090c030f030203030103061a01050d0e07150e0307060e0108070302130302130509070906050d1b1a130f050a 76
    0x3400840d81401c0c40c1415001484d80300b0020350000312200e0302c2240c10300000703038040440702c0503a04e640c4240e035604610203200034192a105001030003040441c40d01e2030580c004040c07690004190004d2514060461b000c2d003509200080003503040940200705029243c0c1c030400a50a105005000810410a4101642c0700d50f001d91511151f83c0c5040c201030001c1800c40501455210402800c030b2201c81c1000b82d03480c0c00902c400c0350103070705105017600000303805420b0850030b04040c0c441508003043c0c048402c020f031100c0150b00303403d8800e2032000505001c0320b080c4000070302070a8880c44030b091488003d0604001090700004240310207021070072266641314150907404592403a00507255504645401030303000d580d0f40042d40c0803489044901c0c80d400720b40d010340c0c001c07061142101c080c280e40d4115201601c60b113110300c030f0303100c0a000940d2011690301c0c403600303140c941e40007400c40b411500d502400ba1085c41c03c6a203202c40c190f0204010604480500c1030102401074030a03a00701080ca0107000a40c01d8004c0e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 410009586 1250 410008336 410008367
    0x3010216030c05030c0d05030108061302060a0509010c0203060a0b040b0f09070810030b0f071205070806060702060c1212010609082d0a051b0f090402060921030d1b 72
    0x740044401849818010340700100b0640c81946c3c1c49420b4104010102e030400e000b40e44140c0038600104024001900b00b50a4150f40039210b1410500d5845081c0c81c507800c200601810302048416582c0140d03801e0108038401c0900d1100000c00024400c14001110b009141c518000c10148881910036074401c00d44542c00509444d01b0362541ea40e00001e00c400326003030351008160101d079006110001c03240c0240c092007241c1c1c41d0f850744d81103190503030304001751201990003502003007002001c2100d60808070010300c02c2a0006d0002d91810340c0540b480c0f480c020074030f452240080404511320700d00001c800c5005006114920341071411509040d080703511081980c81056064550211092000803c42220304610740c842003a5881034500e03041154603a1115807810750f48104544140d0500d10700043d0715240104054140b04040c0c0d6151b09020f40c642c00071400030f0380710180381c2a5120324110011103a06071903542c03000c0e589404510090340d0a0301e40c901e50f64003540b02407000c010103242c0c0c020085403205c1c51 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 410010836 1250 410009586 410009597
    0x714040b1f0513030507051f08160c05190308010503030a0512100e040506070f05040e2406031f060f020a0303052707030c0b0325050d060e10050301021603 68
    0x14010301610300b0b200f07194898140040d600301c000244130000c6400c004503030f401d0f02d5020320760b0344641d844004d10341c0d840012000708200d0740102e0030701003a480c1c04034a180440d08000c401520b683c0c407250701c3c00741c000d420314801c40d44240045040552000030b10380144415001103007030130160b02d40a0228054140c2900c0c07581a5400001d26507800307601100002c10a840e01c0444500b000d0600c0d075120901101c90402044541c0c101408042c070550841c0c08494100c04841415150740244613a00318040d450302102080000e07015400b66121402540180404000d03174404019254024102c008990720070300a11800d03030341c00000c080e00858107030311240d494540000c1350754500e1041d24810301d0207680d6007441c24140c0807029403008002160001c4d00d00a21a10111641e540d02c0a90070f0310003207422a1258250b80700002030381c0303440c9454038004509401c000d400c005038010f400313084444c59406818207940b85401d0200e0300e011200c110014140c11b6000f5460400400440b03482c811181c6801000c016 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 410012086 1250 410010836 410010889
    0x1d0706080601170702060a050606031308070609050f030a090501050301030f0206030603070321030e280510020304030e090a3303050d0306050a0f050306270a050714040b 74
    0x203224500403c5181804502d40b081c42c20800781c000e564500845003007a00624100102d4820f10f0700c40143c07885142010000c4c0c1c1080115900c1c048150803030a4100c0f03040d038661552200180c0c00b4092200b249411000071a02c4207210040100f6900d0103602c540e043c03000c01c000500c0852b4001019844c0305070181e610f103a5948684000c603142400f0380e44080c0c80420044504d049440f5070702951058803003160b405105901d01e071402691107800209900c039200064140c4400000100800122014007e02c256104407185465250a0f40d1007161304400040b0f280007841c880d8a85450107a40003c6030b00e1041201540d074404e0384050001a103100044000f811005100f0130181d40c5a0001840e4410181c0f003000c070107064050003400603400ba1502c079046040e00451310041c0000f010b400c58100800030203868440c003040c180100950ac041d04241c0c5941042803010040c20080415014481c1004218140c5005c502c080c1c2510307060503e602c03ca0910072103010650743e03004155444031210802403c000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 410013336 1250 410012086 410012089
    0x1090e04050c0411090301140a0b0a050d030807090e070503040308010915030201120605031002071101020d0f03020d0603021914030c0d0605060105040e010306140c0f07030c0305040b0c07091d07060806 88
    0x601842205d0b030307850340c03c111030110a8842407245501030301d0340000c00e003c0c01c41100b003000388064450180f06e4000c4110030300d035404281315111080d0001464181000346036281c48442030b0281d4200c4440c0c010440001c00e20003010750208c9a82e005146805003040b4400c185c01015013603030528440a4100410010803040d4a03505620603001448002c040341c926544140c021030294102075010b03500d02582d10302c40140d0754000702c0d1178490300c003803980c411040e10081803080d8001d4021036220200a945d61344044010713187c1e80004000d40c1710140c00c9100b00f918112015204401c694400b034003940141c84000d03810703160030501b486011b90100d00401c0980c0c0360001250180121381c040794182070a10000420300009900400300310021490a0311260346180311100c0b60322607004258603802c020040000841c3c441c43d20010032a10a20701a031400303984800f2180c050700090300d103c05540101c2c008020701c0900703101e00d440d040d000c2c0c0b084508030303900a107619854110521aa5040c04030040009a03d0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 410014586 1250 410013336 410013371
    0x151d12030d150305100e031608040f0303020f0106140d02060c011407050703081308040302060d0905060903130e25020c031507080601080f0601050c01021201030506040201090e04050c04 81
    0x29000a0715080101d00840e4002550701440b81c44103492901a84c221824034411034003c512041090800444c6040d59080000c5003600001c0010f542100f020b10010682d850440b907204c4c0110301a078010b10714072201c030000508482c10761784582d50b0041514440380041d150340d204520250b404031800d640b21620f9141c8070380540030f44406120880003002c1004803c94204005c0c2c0315060181d951808a951684041004030748807841c043c054031401d000803c01443d0880041104101d40200071410071065a035251810f4401d44429125400c00701d00c0e0412040580c603034000070214048d00f03466600780381800b007080302d82100000d220340260000004049000b040b011460f168086e0441e01c1c5070140c80c4540c210158241d4100700000d075044041800c07903114850a601458502d0400344640d01e5200040d07800354002c3c0031008944d5001d0100185040314600707558021402003024144500d06417000510401058210f140710080c2d180c1404045500041d460344a50019036000810840960210741d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 410015836 1250 410014586 410014597
    0x62306093c090307050f0601080604151e1e090b0705031305030406080f01081c08060102100e0109020117150409020f040c090905010501020f03030a050703021c0204151d1203 76
    0x50140d100380002c00100000800c80240580150f131041000840310759183c2e0003c3c03165403159401000400e01040c2e66058002c0c0c0c0a0a4107400203200307500719403c0f0304092440802c48242907a440c0302840c0c103c00d54030424950451180d080240308003687d540e0410500113000c40c401c100c0040000ba80c1c2c041541c181040c40c5400c0400c40340c540355036420003270400100702c8220101003140000080c6c3c0c07020010780180034106120943d07042240302c14085030b84450003005103045100328480c8152020462103240641642880049020b024600001d8042020054074050a0020004005015009021495078483e045a0101c0c030b040b51400005c0181d84c46402a990061810030748044041d001902801190b299079001d01207aa6a0001a81c0380c10801895002c0340d0010400610145e40c9075100c2c275400030781404c0c01400c2c0361041c500c030496a000410240803007075000905004014002482e0403025007103203010440459150a8821002800b51045015002c203800c0c1002c011002c1c000d60700b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 410017086 1250 410015836 410015941
    0x50102070c03061a01080112020d03091a04090605061303060f0b06031302041104050a09020c0f010204030c06090506030c041205120a1d03030f0f0a0c06230609 70
    0x1055a460341800f10061406403400c003460400340310203458950040b40200c0c100e40202840c94001c0c450b680030301c29080100f2608134100071584001060b07003181680e8042000c4103411400ea1181e0428114000310340c40c6400c26881142d0a02c00d01c26040c241d9410384050305c0c0d01c001d02162003940349400c800039195408603141c2c8004080100080304d603080d1101e2080714021601801381010349400d6810324031a501406070048451074080c0310514984e0020a48402d100003140e40600080c00d4180c22038015400440e100d000222081003050b500c02d90030300113400d00b00d0b1200e1860a264000c803401d441035210300c0e03400d81841c4601c401030000500c4038620354020a4005035680584400c0140000e00148280a0b0103982400c82030a038100001640c0d9103958010141d80341c00a03100281c0040c2c1c108083c0c2d0070410241c048050000380307c3d4014208100e0081084140450715403443e242000d400505441c0110f40304400c00040000c11000c0390880607034440d964100781154000458401c03400f12000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 410018336 1250 410017086 410017103
    0xa0f03020d060e0603190201080c0903071a070b10080703062403150e0c03190f080403030e010801150c1b1e0512160b0a0908011d0106080706120905010207 68
    0xa000142c001003070344110304c2101615072040340717817107100c44038150100080d000818950020380c0482501c8002d06407042c004044600c540e41e2100a01542410984400490500454007208021071101c10640086294214038211401e0090301e81d80d0b000da074440501140d07110baa5164a1000c65105c0c002c0070549080c00350710180c0c40f42804041e184040150b4034146140c0a0f0a0301078113408282001500c2d801006405540141c0c1301c1d1050b41a04202c0580c1c403000f09400303541c002601040100300540c4280c82d00082241848000751000c1c00507800000010300903900e89454650048807941142c0d4405a14605900384025081c00c420040d00600e644040c030325400b400444100701007004030b440490b02e4030f881a0003084030310f031140001c03c1075904549035202c05103c1204820083d0940c91868030701725980d00d0307440760850700b03540541c800c14458000c140354030390542000b801010098141d607402040010b1070858020400103c03981c400000c640e461240d001081000c0d01115013460304150171 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 410019586 1250 410018336 410018339
    0x90d320a0318060e070605130b03040203030910120516020604060e0c04060e19090c06050f0d091406060111030d0207020f03010903090905240f0f090c040503120f0a0f03020d06 77
    0x540c010700104e40603440500c600400041c07114410b800700c80180540340d004030780007441c060302a00319800180040768076000902501495071a800c004203030054141e0b4904035902604032410046440103000500764012603602124155000905680c000d50301c0000090300c501d011445500703001010000980c42420700400254030085008810700a003030032180c50004a10f00260b803001c039038003400010000c0750944420020703240140c000c0d00882d81200c0040e46005081c0e1009402c407281928116100c01e06a5000421107008028556110754282030610408d0b10179a40c256407405020005010207130002002421521449030204101c130024000303201941c81d0703140203040340d200d90241807103503850507002950311140b00070020101800204000405052003050103c00c02c5015002604003c030300000b40c145450300d80d07107940325014081c0b181351914144001c05050080804a0340130a00c014001d80c410903650b1740803142450b0702c2d41040e0010050002d01580a03001d91304c00c5210380c920f440300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 410020836 1250 410019586 410019593
    0xa24030e0d050c0c03030a020d0f09090203100e060f0109050d1403040815070c200d0b0a0b01030b030606030606010c0215030a0207151407080915090d320a0318 70
    0x74290140c0701c0383c2552480c070584400c3c10313070307a004071400d59005a220721104da02d00e50150000d07409507400362404910054482c0f403010240e90083d1001c1040348001c18040150b004035400417500003070204d91280b88500007400081c070041060061500c40c240c20000101007101041c0c854612114070020f80352a1590741055035101c0a91000f000551031034940083d000c2d61050340c1c02d44810341d00181d010302425041581b03401a113000c40300d040e084804000710700c001c00c00c0802d0852081c2095100803400d41d040e48001019100030140d80c82c0254401c900348071144c0d80205000d0350100082c41c060800a100e400041c1c02210303402c00c2090300d03d0001041c041d906d500c1e07400814409024402041405050302820000c645440703401c00c00741011b050209001920036240207800c00360040c2106d1580ca00134400c110900d60941e180700700390340100c840c055165000501c015030300800c01400c0383c043c0f44101c3c440f92020240800506003c0c40000c022002c4c038000d0307001c072040800c00c01d00c04d00160550718 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 410022086 1250 410020836 410020847
    0xf050a03020d050403050d080a110d0903020c010306290702060403291509040503190810080c1503072006040c09050106140906091503150a24030e0d 65
    0x1058005000b441041c042d082d0140044404584e4407000400000600312030441d1000385c09070040301c2d0583c031030307451b0300c081070389500546039200ca13256000803140d04510303002c2e142c9104410740905040c01c2200c00c00141d003140d4284c03404400c04401841070b4131b0340111403070b1440c403445100960024002c980441440002180d060758100c041141004549004040c8010248203e4440e4562038081c1d44000c0241032082d0b40b507070403511a00480307007850544900d945400344241452000541584200141c00200d512500014210200541303203000001d00442c24000196602540c059400400715003507074414107207800701507040d114400380e0780403022405494440c10360b0300b65883c15190202140880d040c0c4581030484203130351151084500c1190001c4003541218465591100301801080420340340c00c002c44044412241000781e9a02c0c2c044680400c1d080d0f5040c829004014000089c05100b40c4901c8076080300075068104021102c0ca00011800380c110340300005040d008600e68811010b4128 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 410023336 1250 410022086 410022103
    0x60f12060506040f03140109020a120203120a0509090a0b240c07150e030c0901150c05010612030210050105150705010228030e1b040203040c080a11040b04021309180f05 74
    0x54884561b030300c01114015099481150001c0d6004001010401422000d040180283e510240c1600d01500160050710300c107800c69502117003c280c0002e80c00c0d07828603010302d00c180d110ba00c0d42b004114141400c408a0080311280426041d41c1c4101450001c00c5147c0400751042c05c080310040701d0b80d003a00d941164100440a00704480820030340c40890030316140115506c02c3c40b0700702070452100d5a281543c05410424180780c002c0a008416070000b0100b40e0a0080402810f003024110741480510300d0001c1c030b0076954102d125006850f00e40140481d60780c000041400d0140361b020a5145d1100381001c500900c00c0c0010f54070001c948a81031840440080081c0e4a1745c18261420000030350340654240c1c9400d044540f1141e20345104801004d2450254055600103005940e00e040075a1501102407910f2403101d41030b0f641206c0740301180140c0ca0180142049444159429814040012800079030030605029108600b41c942e00c042c41c0b240c40111011400076000100010f100e0303418204191602100b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 410024586 1250 410023336 410023343
    0x4080f01090314090f1e181e0403020d080c0906070c0504060f0602100f06150210050a0605060315041b081b0c06040f061517010e0106060f12060506040f03 68
    0x242041c40b00c007a42d1900907140610f130090300d400c03c0550078100308410740308628203560510800080114164803020000800505c03004442d207424204075103040d889204058842c1d10824014082200090380410340e840a85040e003040d5039603480e8454449107a0141140454210348003052900a000101c00b4074022074005840070804141c40f503400107045002d6004800c0980c0c0844d0360154011400d0b801010900e06e4968002400d50301c5d03a602c17030286840404240b005a00c10759040200306071310b1040035000804032204002591904005c90703401e000040000d1380c841c0c40d440306044240c0700c540040d80d0342203000d01d000810031820741d001703080140203031100640b00c0003000c0c6040440b4440411a507900040d02e0003071405642d0307995130001c0d01507800b008940d1382d0f40b07030324240f02c240c00302100174006040e1103210300b601004501300440c01c5032032080b1100071680c10171204108a580008a4107214002440d040d640100051080710260181e40c0c0600d03084040024005215100e00310000140c034071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 410025836 1250 410024586 410024597
    0xa020901031127040f060b07030305060f010906050d0e0601080307051006080604020607060b04020301120b0709050f01030c210213060228050a1502030610080108101104080f010903 79
    0xa03021201803a50007070b54420b0354518400310f80ca41c40040c05110004072060010b002080d001500e016000649441d940300803156500819500100364050044a0b4041070690342202120b86c06400202054035a200d90420300000090000051406400c0300690480003402c070703103695940714078040d5294481c05050300c59001e008403540285090b40100011a01080700610309510307980c081003950350080c1b000321015a6030351503141c900d440714006127000b402006442c000110f102c0c109810000c1c0010050410040c00800610056035191801451424286000603400c000104180c40081c00703810340000c08070b0280c0b07118219044580003804118900207503541d4103030792010180d9888214030810540b2203001c038115040101000c601c2c00700203002d007045403200d00721a02c0b02c40030f08490200c4640f405400204004040c100491011a01038641c640a6000d40c0360000a039183c0c515486c2c520079039912426403c41c0031041d601a10040c0034040255868160300041083c000d154800e0b04902165 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 410027086 1250 410025836 410025851
    0x10905090903030c0a1701030f0201030e0105060102120f2503140f0703030f061d0405190302060c0d0902030f010510150e010c0204060911120109092003070e0a02090103 74
    0x1400d0115500824100009508640b81d01c224030a268101c244000e042020002d80c0d0082000c0c500e0001c0d009500403040003083c001240001419140d2280901c41c4036130502c01401896680001c000350704030400030500c1d46034070580e0180c4c8198408c04051a84a64015601000c0204a1118000b009101ea15410310b01154103000c0c000500901e00d240780c01d44000c1c0503000c0800d011b0b800070396a200d85501c0c0007a00750b841d00400c8480120fa901229400e035040300c1080300b0044c04100107100010740c03507003a030454059a64002c0d92100010100380d484040807901e0740c031400031600300d40455035004042d5000d00b554110094000c1c40c007202c603501501880000003840c1d42164209007180c8101d6942c0004c6802c0040c01500d802042d05400c0b60070917030303d1000188012542c810100c0341c59481e1002642c40c1c112170581e000b1040b060b040414003030b16105185001800114040141c3c0b42d46249904106041c0000207080c00010fa11001c070061001c0c0411122804030340c0104122034003602c0400403071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 410028336 1250 410027086 410027089
    0xc0c0f0309050414091e0616050403060507111209060406051602100f09121101030c1103040b07020414012607240f210e01020c0d0801061202190e0105090a14010905 72
    0x8006406000d951f00a000458002415540c400011408609015191554a40c0d034801144e400300c0350b0707d0005039110400788154038140080c00b00c421841c0005030412500000259003032049100c0c4000703119000648030701465003074500c64880c60700101580028026000060540311002c40c030740c00011100320b800b092500801c44259140f0f5008100308290f501c1c128019001083c29010050500003462030560b021030041008201034418000b031551514403620520056034a01080b41949001c5000140310403458006414080d5413444d44240307000140208490034030000da0011542d6010301411000303ca294a224280320300795968a080a000012508642c401c44c0c0300800c03806d810000040042118081d0032120402501c42e000502c4c0c1031110b0f001d245803c080c0004007020410f600010080950892800e440702c840a4009601d4071041c0f810030ac0700441968510400e22000718a0115030703900c00e030240c841c000310280c08a8085a00e0f05480940801d802e681c07a80012418440070030076 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 410029586 1250 410028336 410028373
    0x310080a03121a0a290f0f07080708030109021b0c1e0102150f0405070e150603070504050918060a02092b020306190c030c0c0f030905041409 62
    0x1403541650303650401c8101c098044002d03100c0e1880591019452540d852003503a642503605004160b203000c1110b011201a810300064000c0c84c55840d040601885500d018500c0602103546080c00e202d1001e03034554083c82c142c4064060408041d225003000320020520703811640c0206810700ca407401da908034050b501d1070036031703907500e902545d50300b264000580098020a0742c8e0407102411050055030215012070300f80014a942c120740c2030444013a01004e10091107c2030201c400078019141d00c0b14050711b0322a0101c11100314072070015002e2000000068061840b900a450140070000c10448440c1030030050800000d8184488d00d0316400799202082e4214100c0c1b08035109804040c0040140000c543d01c0c801c0d100410440c1c5000100300b030a0340e9030050f0303000d000281c8150580d0000201c2d811604d01220200e81c024282c00007030501c1c001d400140c45070030580100001e540704695132098000c03403808881d928000d911541e0450306200700c1c0c440718000c98904a105000040880740000084406e4088 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 410030836 1250 410029586 410029603
    0x20a020a05090c07030e0604050d03020a0c060915110c0a0801090201022a0f0402041a03070305090703080f0c010f020f07030e09010e06130902130b011b1e030c0606060302031008 78
    0x21800c121307060002c1e000d01e036890400c00e40282100c0c103040d41e507804603c98416038201180140c02180010703042042e244023100c042c02c0c552070482c07405410f05440c40054400007036007500f4403c0b45d210000c0b80c010208501d00020001030b044154299071180d41c0342c0608101741049000d8082c1c5444200400b0a41003800f20700f0108440c29842038a0307540501c12000c28124078140c10a40070400406c031540500c0c4000c940c1501d810340c655a918080100030107d0304081e0003500160044082080404d0a01068926184c2603100c4159140a6041710b83d005000b03000c54043c525001181700b10524094801400c0400d002e903ca040702d1941ca101007001410007402190381d94092140420b42d103040c0007003100400500900c00040760f148940010318407140c072070400a401d68403141c1d6080715580c01054085240100c3d40c5001e9070350901d58400c19016107000440700020600d1140c0024548200c458154a6070403400c02c00c001c82d15074400174040c2d4802c0f10b460307051440d1150b0018141d0320004003040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 410032086 1250 410030836 410030851
    0x120b0603070f03090609031701090b09040206090d120206070e04021c0e121917040f021002030f070b070f0c030203030406200d05190b010e0d080f0a020a020a0509 71
    0x1032541d696000280e82c444035020240c0209030b40d0f642035100245c007611a00d420720340252540c2001451404a614540b101600f1142207103051200c400740d503803214502e40d5003040d4102d650700e48862002000c1404000d5186000e094040780d48032030300b06140c0202e00240a001c0541d0317540c030014417840921059200700141c041d000302d202c2c410148060607a6100d840003400c40d0b4103491003907402145008042d001f07030b01c8003000340e02000718420110f0f8000c011142012036a4418110740e14003a1a88050300d98204004ad0265a0100208440910910403544118061703405030351202c00c203050550410808035007117800718400c520007e001e07a015410042d0080d42c542d0045140d5a950381da0040507200c214400080d41191070324900c50410b841c4007500382183c001100160030715110f80400541610082e0301013410703146c41c9030a06140da000b403070710744418010341b83c5107075200891030890901d104d801e00a06810401013850001d0581c0801c805d03030782ca40202c480980450b195010000702c0007003900c001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 410033336 1250 410032086 410032099
    0x603011406040e031c02190305010308030a09081c0515180117030412050604051b06040323060103030903050c03011407030c140a05070614070e0d050a050a08040501120b 74
    0x1500c1d500d050f80108103440d10340410b4906051141d41c0715a040d200480100c0700341900401c00c440280518000315056a2041c0fa0500195245031035400300c81c0f00203010701a20355160a0000148001c010481e040c10703001415417803100388201c0c070700d10061005803560a040c24611a1140180c84d1002c03611241c00c9200003022210f0740f03480b074403007487c101c2016503000c80d01080c0000a08062a10044001c15014501620702c6282514045050210003541c0005c0840a807403200340390384882c0191025282d200e000042d13501d40c2e403814402040761404040006114002c004020035034001e607658200c070720070000c135400c1a000c10101800e031a072801e280000010035500007820320b4843c1d000101426018101114200400d00000044ad4003000b444000b00c1c40016a4500b005101d20900079014151110f02d091030400310401050b4000b011469407027904034900b400180030050118440f080e81c001d08171522400c031480e01102d81e400c680318860104251010204089620740180c107141c14004001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 410034586 1250 410033336 410033341
    0x102030c220b030a060305010f0e07170705040609091202030f030f1f080c0f1f08041a041208060405070e01080c0f0409200a0801090216020603070f0806030114 70
    0x1040284401580001c040e051400d00082100d00d0748000c50007079500080c041603190440c1040f80c00d40b520748a03070450140c54040103280910f00400d045043d14408030ba1001d10501c2482d10f107189c03400680046511600d419000100da842c00d50080001038419020b100e0741c0108907030103a13180d0040d0200d000801404000081481400e90050b44e480f41460030780341c2d0003031061402c2070500d0b00e0a801601d0340b64001e41e001442071030030641c1c5a03480202141c101031190340e02540500c40071602c02500090004d2413022400300301c640f04084110580c45010b88102d840c007810b0540140c50341d000e41d1804141c1701c2c0041421800d0501807148940071580b00c1d452501120b1004603002c040c0140400101042400900c9070755600c0301c02007005100601010648a2422a081d13603c4100700c6000017200a040169980315504010f000341180c1038040c005890f030318035060a0003014141070001394000000020004c109030000551800c2540b541d40c0c50b03109580c6c490900d400c03210304405110260055400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 410035836 1250 410034586 410034607
    0x129032116060e0a05161e03110d200901050a030f020d0204020d0903091403010c0f0516020904080304060608061506070804050a0b07031d010c060902040905120d05090102030c 77
    0x5a000000d125410004001c101c401c00c01341400c60b00c1d20100c807144c101c501c2086250f8603004010000e480307240c40d244e81006c114007550003841501c5c03100602801c0c14440c141c410341e03250341c034103515682c204024403001c1d40f840250700544002ca1002910444c544c074008031380ba041182d810010b43e540f00000324000c01458007049000c42152408030782c081e80811900108054500401c0e200c01d21a8440d450f8640c20b1040f5815641070309902075009a2511404900e45644081c103184110680e04106503161b00c08210b18804041d030078030203900001c8281c1413000701f000c0580198030503070066004101c1c0302d4581000319180c81080e80c2c06c264450f403c8516841d2480c0500090400c8c0b40704030841460b10382d41d200420440c10355588000580d941c041074480c141500074490586c000740580080402c801030b280080d006404406018120340d41c0d40601c0411500c0e01e5214400e030035048000c68034450f001403030b0360000d5800150400102030074040031170120720050086d02d000320000700d44941071448028 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 410037086 1250 410035836 410035867
    0x30f020919060b0a020f010c0c0f14010606080f132d0209090606030d020c03060712150902040f1205150c040b0a03020310051009090e01290321 63
    0x10701203035145907110500400254140700b038400512010010300d4882c22411000b0b0b007840d52820040426034141694a550340b94003040000041d81c2c0040d1030000200a410040c20540c01060120000d610380300c004501c150b007101c00284569024a14104c19540b41ca1407c110403030350050050040303540070716500c04034501d041c0c0c1d000f1009144c50459009906038000078081d1405a0700f41c0d103070303401400c1400704a05007488003d01e403503030b94001000388002c1600071a0707542100a040904000d2121030302c0003010b0083d0000c00c01e40081c50041001039840d00803000c029030051140c0f05594107400030000c1c0d1300010b4222003006540000c0540b268541300000d04401800007088030860034810040412040384003800f500a241050707400680702d2030100300310015020240c0010b40b103108200f4107103050a600c0b80f40700013030380c0d980c03c0e021481507251441c99000d00021440711310103c0c0d050710810355440400424038000b90044003158800e0642d8003030700c01138000c1c1c41c4800301c8226080156501c03400301403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 410038336 1250 410037086 410037091
    0x17010b09040b040617070605030415090303020906030907170f0c0f040b030601140f0f030a060c0318051501060f1b0804030804030303020d0501080705030a022403070206010915030f0209 81
    0x1d000400c0801d500e03000075088074065048008070200d446280300d01c000c0204244000f03000f42d400d01c139203581003a89810240201c0e016034640481c1e01c9100000c1003621030707015200c24100283c0318a40364280714078980d41300c0890f401920150440748945103c02040014810030001c4407401030020310145006010001c62518011600540c0301e0340481d42c180c070f00b000018000d080070380d206e05a0362001c504000707015001c203903594824240e503884004980d5010606150203035003c1400900d81d5507140c03042e00a0410004a20072032029042803005004020410118000c00c800081c012680c0340d40e0b0650303504100c15004000a010004500b01e605041158483d8147c0185480780c01e00e03542c0c1e5240302c0503a2060b0030440000e0380104080800c0484c41c010303140035204600c041c4c020241441c01299450850320f00191142000080e06120758a03d035040302001d94600080c10742c0d034a0303c03030b0001c0c1d5542e17428803402050515003a24480c0441c00d590008054a50092605203803031000e408224515401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 410039586 1250 410038336 410038339
    0xd0f141915050d23030c06010f0303081f05030102032802040e040839011b020c0d0c05030a0303022104080901030507050c0105071e02012007050f0a0b0f0717010b09 72
    0x3130f4011002c0781201c50800b0001260400296683c0e44514009400c0c41c0b41030b07228850300340d06028188002600000c0c40f60380710380520030400104154000703110740c0300510b40c031890701944004144200810a810000c000c0c184026140c540030300102d650000700c2c42140b2603510341100da90041000030307445100904004100140d0500e0629600f1500005400e10103005030500f4000c540300c0404103400e008850445040d180c1107003180e400c02c000030b0740310030b000941c55100342c48114201e000c1040148502c400303048098221f444040051402500a52184112401e0032012031001c61080c02002c080510440e030111a5a080a40860065000c1c04024281100b03200c03050080b0601c1c1d00c400d120b80c912031609540c4940d40203004c0700c5024030203094189840e0442e410009161888805c68100080d001c0307001314510b588580c01c0c20300f1400c003060a03c1c3c482d014001d1854042c280440d40c507805014000c19104050251030340f00c000c2d103405100c40034a1400c4031010004000014150001c0c2111580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 410040836 1250 410039586 410039603
    0x140420010203120a1a09090c090c160b1b04230a080f0d030e0d02070308090307030b0708013f110d0507140109050a0b0d0f141915050d 59
    0x558920ba09406104031920080305503100c42c41030160700c03d4413103400c01480a0300e4405d218280b01c85402e464231400366a1f07d00419920010072074000740c403400c40d12052080915010500e403031340781c10160100c0941c0c2044030746540c511600e10490708041194203d609000c04080800740c540150042d88400d1250301c0d6000003401c0001540030010700c038100d07140c45004064964140680d4018048810304540d044480d4405481031071150b8000520900f075a400c034101d140c4502d04d10002038602641508000c007a81d07841818048059004607000341624501840880d406038113012000680400700d804ca0704698030410f110028404080811000314040e40d5002400021a0302082001c01224412640e0f03a000b82400c1115072824116080d850600340303054a03000340b030400058103408644c0588400036100044c2d42d0952403190380082d1000402140c148000c3c9147d10251645450403606840c00c00f03001e0600c8e5005809600ca500e0940500840480100d401e0205110185843d028225947d50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 410042086 1250 410040836 410040847
    0x609020f0d0c0c0b011203140a021207020301020c012f1206040504051c0e010e0a030803040212010213060507060c08010509010b0d1e090c120b04031409040f06050103140420010203 79
    0x1004001350a010708141c00c40c6208083c898a0700814000110701c0100780c9240c140121441984e0214040740c081c0700710b881c07079529410b441c00002d0084c451164402810340ca4248481030800c1603104602240d40850342c003050b8400030301001d0790b0780d1084032112a0706a21601c0001c1d402c0c603095004503000b41c0030f44103c1d19880c5802e0000c9030f40c00c40b1401c0c080e0201d100d41d05541c04941c2d000c55030181d01c1c1010b95038803400a2035503450344114000900000e200d8544250200034002c000d5040d2024a0104203203006540d9950340d0281680d400300b071041d02c1c0c103820201886541d502408500d03040324005004601e013a1f1030100244090f80210342d07000450740e119000901d01c0340c142c1108010b003a03214040013444000c43c0c40c01d030070740c81802e0b4080c05152403080e001c2004a82d205011a6000790141030403141103240711312003106481048500fa07406480c10000c0711003520254440301c00e880e400c1c1c0701080418000c1c0624444404210740040c40e0101d1444a80c41442c90701007501380034030307060044a0501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 410043336 1250 410042086 410042093
    0x91203051305160f0801060503060703020c0a0c03110a0e0601020601090c110a1109070c0314090d020d1202010e120403021905060414101106060108040809030d02100609020f0d0c0c 79
    0x10380f500d0100d11821000c42c1d400d1002c4610b10700307264001c008080080003554034160220780c0701c0c04000d01e024141580468900c4c016402841584072481d8045800e00750542c0301d1420a101c45039a10500c0d003d07884040300440c0728004031501b00d0295030140c0007028180e00c1c04541c3c81c007409204643c00d0400c442c9401d02e500c800402c0214202d03892007694460300c5883da1300e0034412409401002170003005902908000401c0e040094145400350300c1c00159070b41d000c0000810385119030a0b90007904045501503040078062140392440490701240c2c02401201801070382165034084010302c0c01e21100b401c1104200503d4401004a04450040b68860305550740d0000200550000c2e07100d4014039110403240c480b00e181a103d0708460040310300300300c03800244418090fa0388142c024050b506000030580480c1c1848030480a0b6181c2d80ca0040c1244d01040f0004402912640d0808080503030908105000c50a1400c90003658803626201c0740351030601a0a010040c080d06120316241d050044418100380403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 410044586 1250 410043336 410043343
    0x30c020f0316090605150a0504030b040611070302030c01151d15030109080a0915050306040c020703061113050d051c050d150509070e0f0d1b0305150a091203051305 72
    0x2001d0403c40010303503d01c1d240600266034119800390840c10000c20010003440e8102c415034040d260024160b01055031036160281c010100004070801000022521404040d030000045c0503134019000203209110741030b4070030b04085000307020303c00c0c844444107508500700880c11601c0364803540d101882c01c028820040031038211401d0810a9800f050005905000250042e102500901034041c0382410f0b00018103000b00140000391545100302d84071032a01c03850500c01c0140d4806150015000c010504008000391450781c0700c00404801a50308980c0090f0b240b8144214500360b681080103054400441c481c084d44107034103081c282c0103101052228803a42c420324420841d014051098030406c0ca42400c0801c0000c4c14010000020820743c07800c54a055210b80342c140d8003a0200b940d683c6504103080ca0103c002c201c3c0381413040c1e401000300c8800420b1100000300b05803074410310703d40b0600d41d407142031011040e615111070180141541d40b408005091182c3d00c12a40901031001d42c42c90096117030b841504 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 410045836 1250 410044586 410044589
    0x60703020721020c0918030a0f030b09010b04090614060702190e0106050d0f050402031b03030f0c010f2009091b0309010f0c030e0a0f0309050d050601150c030c020f0316 74
    0x50b80304803131890307041c10851a0b042d000401e10441c00c2c81e030410120001d41d2071091030041e504110452841da000b0900079040f20360520002010700b0035941c2c5601c400500c5800c40d00c200b9401d030341003140000c1c54a000d919203107251400500003500c2d2004c035400740038000e248800704101c54000400000b6103001d51510842c043d100c903a40d965031b00c6041a0b50f0000b660000e0003a10740013440c110900c0010f03540000c070401d05241e110b4003400d010403100006802c602030545004805500001c1840018106600075211001605000c1000e04a0000c6240c44d003c0003100c1c800b070b01c1d0380c2003001c80c04178079000300070301c3d4007007429001010500c1c80c130016091340d0740090b2201b180d260344914a0800c84042401002c42d8120346107001c200001c00c0100b540d0f925121400007800360140343ca0980e0601d0300ca94080c03000ba1401600300d00051300c462818565480e000d200d195914410072461480d254071400c492040a03070965101c80c1021a181c08000c0000c0d1410a05d56051103400240d10000041088030700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 410047086 1250 410045836 410045903
    0x13030803091b040605030307030f02100f020405030f2a0f1206061f020d050c010608010204080d03050c0f04051210230c031b130504050109050402010e040c020607030207 74
    0xd0515200351100346012050320814403c5080c25000c0c0190303180001510340c0c00e901441c0010440c0c0c042e25099042210303003010b880d400d509108420911100e1a0010320403964280d0840f810080300b030381d1054071910550b10380c03040c0c03441d11250074951640300585007150700b0000305540c04c440f51038030000e2941c005110041c200e41e04404108007040c0303056088503c00c0440a0b1107007601c20a010b200030b4882d034594042106106000c81c09043c9035000b5802140940010002155140c2d115104a41d4580c000803200c0002401c040010701590140815120703e000d4501200381000d0615040103031118a03060034184a00c101c650400e800d9103140540707203da513010081d0210926026141088d500001810f031820224200107100300003101c0341c44555100e4107a180c180e25500045040011900164881a8041d0501c00080740d5500c0039400707240203a100340c0b2800f017081500c0051009980941490740096000035001509460103034004203c842d01c602d6200c2000381094070f26645070200d126064 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 410048336 1250 410047086 410047093
    0x918070f06110118023d03050405121801030f23011a1c091403030108070e011e2306281d060702181513060b07081303080309 55
    0x80c2d20020a120700800b070812041480c800340025000700e00302242c4504400c41e21141da92180c488030101a00d00368503020010741d26040512240c0d001400380800f07440503102c5006109240e0020401d1004030b0f644084c914404081c00400d900c0150000c15408040da0304041e141d0101407a01781e40341800f47c0d0311002011400c00d1950410300107291ba110f800148061081e81007108441c04c1e422003260500c0100c50240c0420724410f0352520b04a01d1043d4080c0caa4580b1001c800480d00440c00f280da8000e0301c041c1c3c4507901040e0b03078640407000700240c200c807004283c14103030005012140c40c5020600800d0400c070421424050010b01203482640b0808101010414031006400c0046058905c4041940c0a00e8201d05091090380505001d01e0f00c03524007881424005005011034451000c00482144018500a42d41c6440fa49404107101c020030b40a114000080c40c00064a080d031180d94156228000010308001140d986e807170081d800542442c021602d00303680000062004070065214400c802c026 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 410049586 1250 410048336 410048357
    0x418180f020d150e1c030204030b01090509070302060a0507020301110301052121070c30061103130c0f0b0a0c0206040b0c0307060e210306040b09070906080f01050918070f06 76
    0x99021721607034080d80815004200400203c0c0080842c641564038882c80010140c81d0000d01030316000c92a40000c1d001240415280c2c002074224015102c60f0303001350000d01c4040c0001c0b900074054402401140d070b00031400d5440d20009840e50b01800c0c4103a1940c000c95644100e5061400076030484445606c00007000000c8038010407600003040f0b0300900d00003075203a006d00d08a420416140004400400c40004180c80000a02c035894200d02c000c40d581000b01e0783e0303c2c2045400541c40014010041d102d07032924500004220034200070050481d150900040e050180040c81126040102c040c241d0380000305000105010180c6030040c558203000500540c0d0750000361401b40180c0729403c502c0c09003900220b500201070021380a411042140501c0301940d00c1c0d42d030f040010018040c041314139410607000d40070815000e402541d03090646103582c64150240c4e5540000214214090040700d401040e4003000c55040900001c91040100d00501030f13409654580c0c3c00c860b004165a071104000800c0b0292 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 410050836 1250 410049586 410049613
    0x60b1911060a0c0e03010b030703021c020d1a1602060a150803041d10031a0a090c031415040f1707140304150c0c06051602060418180f020d150e 63
    0x111300d22000402c2d0700034000c01d4000f10010703859078090f11010b8001d18000140b0307119144039095004a403680106666039451f12820710943c070342411170403240c00b0f40340140420901a04a000040030f101d00d90300909030f41d99100e103060083c010004101e01641f002c0748011400e4141130001c4e1000d80516204042c80803948078000700340b028003802c201c00b240c0760140c1c00e10201d0701d905803074082040581d1301100c56445016442000304030b00c90028110a000710808001c10441e4121351500b607482500f240e0143c1900c112840b407040f000e0f0390080c050b01d80b03503c840b000584c56854007010340060607a01c6040107884e840350780002e601c0400c0407409410010b014040000d08284a181c481100d02c1d202031a0705083e660001444854003800041c0070010071810780c40c5941c609107194159010b45860744540d65000c40c0c0311454020003038442903d0030001e2401c1c10750714000005658941000394500c84014036024040300f9000604240c801d490684c62698880b11980141100c411b032000090101454508 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 410052086 1250 410050836 410050847
    0x6090e0109020f060a1409010e03190c05010509030c10030e0706110d05180d1401060f0905010803090901271107020103060b0f0a111006030c030b0a060b1911060a0c 72
    0x1400d44c400e9809010080682e580440d210303080103070340b841c213a99a043c2100140d0300c13001e0302014a9811b00c200c04625041500d01440907001a00c039000381c40c0600d40700e100540d1300f4000e01d00100d400d54803035005035019181041c0785000090180c100090001e1250300c2650420889410503030214031526070380342140780708000941c40c00042d40750040c144012144004190051410b40501c00da200310ba452041c00a0f6520701c3d0104008403000f00b2050351b55913048890701034180301d0b0b10344091519000041031200402103821454004201c040320ba13080000030b903036104600b01240203501e040402c23580f9005c014440e40071840e503c100d1460f140c850910004007600c00303a40188011306014028111034541e1390381911590091400c004074142e15400d901850800c42400481d4014101007000040c0520148100242e034020002c00026540300c80c00c081c10340c1c0c134078410310103e00003c001d04403411140002d00c280c215880c1c50b0482c82501d52021407807070281306581e48074405903510040384c003164012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 410053336 1250 410052086 410052109
    0xb0f04030e04050c09040504030917010624050f0a091a030a0e0a051c031103100f0b0304050a140c182208030f2a0a0318020d02100306090e010902 64
    0x440e0103029528104c41c1d040e030a8040d004510340241c1d20741c4041001c0600961554016010503100b5251100003440d003d40a0205446085c12101788804196a00c419503441d401440140d1786519103000e03020b040b41c3c05294040f10542d000c0102800f00482d54500b211040e800e08a59001500d44074205204107104841c4030150540945c0d00c080440c0c80002d80105149294900310404c9084c03032800403d080e0080d182041c103403448114000104401c4a11811882d810f41d02d10900d203039100380e00c0395803542e00c40c0300544001c0e140341d20081041000600d100042c4449001035420359013072225100110f0100507003501f030600c8440141e002c2000b4009049011200c880407041120000c520f1511400d84e540720107003002e050051b8080016000181c2ea10002c51240da050060001c58104c52080202c5500041040c1d0006410a582c40642d060b012402c050f4080d00140301403940c020316402c01c14001260680b0205058031900002001246407051072440e011a0380045801c00b00e40c4100070750511907 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 410054586 1250 410053336 410053339
    0x40812220f0228090203070e0a0801050405061003030206011202041b0e010305090307030e060f04080a050601260c010e121b0f06070f03030c1806020d0801080309010c020112090b0f04030e 82
    0x2420060200203c95000714212400d10800590301e4072412011103050004020711034012200260014000405510140c4114015403e95050351145407405601c3c0b00188005401640102d006101d080741e031140d54008140b00a2002480000d030610000d075000c0c15a24510210f4441001c0921550b018040c071580324003040041c1d0715040c40c60b9400703015200c0781d00c07085d805080c000c0f901010310082d400448001d007030340c002100c040075141d00c2d20704c0c2e40b00320034040e551303a050092880c58007030116003202005c100b03408800303015142000401140c040c0d040e41502c990000401010f40f2079a8020311041c0c001e24440703030500d1907052440e81031119915270304034140c1c0280c00070014000420008000320601d00e60616000c50b5071056440110b80d60150f03042c80c1001c500c405200000c0c140d8000980a00ca11100e4507020056a65500c80580b83e000c1d101070140810000c0c40c0d80001907100380040d030115101c010740000c4419107030b1280c40d01080100c40822440303422000348000d1540094224082e10360 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 410055836 1250 410054586 410054629
    0xc030b03070605090402040b272d0109030804090605012c06030a091502031509060a06031d01050403030b0a0e010f0302060d020c0a0506100806040812220f02 69
    0xa9004640d45102074420071040000100c0d5002d030305c3e642c1d60100c0d40241200b041940c0c4440c45c00401c0e0800034041141407140a40b078042d00c40140c00c00c00a500070400300721121150742030b04903010505943d100000355041150a1201100060100001c3d0014003903030400000d0040c1004009070a00303450300c1c00450030981c00d5030709011800010785040b03907000054882c41c2d1030340c8503910640045e051040b4010051981140300300924407540d406944140300e94030081c40007090302c40034800c01440940d01e154202516890070302c1154007a03000040d031501c66925200303a14443c4a00182183c6040c3d5040740000d80b104c0784440c140c40d04204c91805000d800d103c2d0100c9500d45400e00000013828400240240004102c42d906240d2641c1955080c21407001a00c02600c01031a000c2e440c5d10b822a030100301c40d12400f001041d240c2000460f00e1140d43c0c4190050701d040030201006c41012002001030301503000c414140d01032010341001c80080c141c41207545018002d8030b88100122001700a407891502c00c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 410057086 1250 410055836 410055851
    0x150601180b0f0a020a06060311011e080103230604050601090617070915081b030d020304032003011122050108040f3c0c06020c01080708090a1205030a0c03 68
    0x6034150112041010b4041040343d6810300c2030740c180d080045018010303210390318200c0e0000c280000c141100d40d403041c090741c8944d0a2100128000030700d407948541e2800051900b801400054070300300080101c2c1460b8081e001541c04400b030b9542c580314046404840c107420070801080142d626024600241c11802c09201001a00040550752106248150400325480d00a60650700c2e19a000c1c510242c032155090380c4d258080c40d01200740311100002d804c0e010b881461100c1200510100595003905d505c01c441052206038905d00d0301105014120480e41956202c120000030220600149500ca040c030419440700034410035044040f92855000c141840031100400001884104034008025403140a81404c1ca41c100f01607841d2301408a000319a1842003802130003884075468070220810720607404800750f0b41c0c58040490b100e440c2404500d012404890104a446002d6036000d07500064a0045800000094890158051001610201041000041c801c141d002d50065030100c0c1c1d80b5007010711641 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 410058336 1250 410057086 410057099
    0x21605011a040902102714030c0913030311040e070c0b070f090b18040204080a02030c030a0209010e0912070f110102070f0918080c0102121b0909150315060118 70
    0x4003440340c0d070300d82048031182501c1c07400d00781b95448001c0c1031a0700c240c1300d034000e440c0d80c0814090344840e14294403178030075500301d01070514205003c030340307d00048100403030702040300d6600f5000303040c14412006c40383c9014032003c41d5083c0c420780b1051040c070131f5903544e443c50f0071305040185100e14050242c0d01041103a141003ca56a0031551000c11203030880c41681c4d4621900b03414034603c00f1826a0300d94070500000700042d0110000030f611030814002ca040d80e0a10343c0801c03c05580340d111900094001d9042c4004110200c000d0004a6111610005640c510307094a007118045502480e400c48095180c07414900602c0590000002d00000a00050280608000c4220600c10303262082c9074155032074003507048070f43e0300846000e2a03441d401000161501c55001442d8040c0d08448503a0890044040000d240c03e60761100c0e602000b00021001447e0460f02014420300010091480049105000d07600c0c0c00303520b040208034130041601c141e40946040c0100018803c104095400c143c24825543c00d2000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 410059586 1250 410058336 410058349
    0x1703030903160201020c03011e0c0806030a020f010912031d0f031209010e27280b1c0b010906470c010b011803110f0103021605011a040902 61
    0x8060180000c00001d82403840101c1c603158110242a0305542000d9410041c00000c00f4400500209c0348001e001c117014007401100e003d20704890307a07545940410129030250a200445c0400e0000615140c410b030ba4982d41d0180d0008100041200081c040552101031450918604104a80204c4950000502820001c0ea0360811b00301d00e5664850001a8000301d68000c1c9020000d2910240042c058030101e0800d00040b0261001c104220281100c00034503000d007400030015160170b460000b013114007540360052000300f07542040c01e60002003221484000c1002e81c5102d0341481c1c411819a102da40c1483c160070140c0703455500c600300c0e404d0078801d0100c1d048011500450841091094107001c5440043c41401c45902e036031180184030700020307401502e00819000341320360b51800e80780d50844003544544980c0d88142e41c031000c1e0201640b006e10345264900001941a1080705141c05070800e040045400018142c1c0801150346030347d516950342c4030a8171003401505200c022501000400700c20f4020803507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 410060836 1250 410059586 410059597
    0x81b120403050604151b031506020a170a090f0305010b040b03060105061210030204090c06090807030305031810060b1e03010815040314030f0106170709060507050a1403041703030903 80
    0x96541320898070704c40000301d40c2c8186c0010441d18100006c140420102800802c041e84441c151600d10304e43c0403501c580002442160755500c1014840c1c050250328000299404c0003c41d00c00b002030850000a6100b20211180081c50040c40002890038102040000711080700380441c0c0030f5041800100015510032055901d2030007101d4a2140c507540c0c240c0002c400c642a5040203502034540b901440600107210280c10503142e403503c80206140d217854009a03038105600c030050001d901040020030111107a05190000104103044440b143c5a88500200b43c1d400340c2c20000300c1171004a200c40c1c40000183e002c02c61031041407241450355042040c69074940e04012803000744c0300c904c4808038080bd44221030217094840300305105616400d0900415807410020b03c01c0d9400039904035031500880114140c1c20303000d42d01640384c50b01d0091900c0313801d803110780180a06803580e000f40003541c0c020030400701d0343d04e1045442c8009183d0360343c18401c0c030783c0aa9035900c01130b51140d8400d004110081c40000308455 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 410062086 1250 410060836 410060843
    0x10f0909060e090f0c01080115021002030103290103170c0c100f020c0109140121060b04150509090f0903041d060103060b0f1e07140d020c01031415010309081b120403050604 76
    0xa0420941c0c9040e071420700041c84024100d403000000000348203000d410c00118554290452a000419010300340001000303010140c0f085078010300300004181d0600050442071545005c0e0344501d0003a900140d003541c03113010010041404403400154141d41880742500c0800242443e20b100c80c20b12002601546440905030b0605c0700151801155015416440f41d80c58004041801107544441050920790040e03c115401024810045010240a6416070f81e41c8200600318641694070009a1080807070050441d0006000801010860405102d204000740c1171801c10203255040c09000141111800d6010040c407000a0040c08047c3e00b190049401c810b4032080001d640079403480701c4402c1d034402c102c0b00801d50440480410b0900c50049040c1154600c99000c1d1480d1115907c019020303070340d080000e0b50b41d1041038000190285884003651a8011041c940043d008943d43c1d50003100b54401070002c01c3c0d04070b000c80001c45201041200d4990084003940302800c20b840c56444e0b82e5178040241004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 410063336 1250 410062086 410062109
    0x90501090e011e050916020d050301060c1205090409050606030f1207060b03070b0414041a0310050411060c06090f0d080703050405010b0616060b0d02030c010f0909060e090f0c010801 80
    0x511800f09800e00c0b028160080140d821420b00c020702e5600780e071442107004054010528000a654010000c2c6c034100c40c00d42c1c0f9100c04da101c85941d82d8a80e070301100c60784414444148105422501c89120301c0b06032511500c01880c003400c00302d04040c9000e2240d048214a40c0c000780a031107d00d802003080d06c01156000c0c8000ca00851014000b88c1880e2240d00300c0e0fa00c6000118000440520800781080c5000050b5400c10911034040450085071701081403198040d0f00c9640c0c00c042194541c0e11a40c0d100d402a900c00690944400001e20140e008060641d0305512500034440749400500c04100c40040305001001c0422030702c50003501002e4001c00141c28181e4842c002424000300f904440c4170000000c02c0e041c2c0c7d134404503140d03904d8680b90380da0a90b90945824130205543c102179054405035600103000b09415840c0d14011a40c01d45105031030820000d40420020b004900750141d98082c00c515809494a4a00100c0302031420069036014010350b445400b4403c060390b040100541914a0100c15 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 410064586 1250 410063336 410063369
    0x3020a020108071b0f060c0c0c1802070218090f0f07060c020f030109030513060201020c0712170a020a110d0308180f03040b0316110318040e1507090501090e01 70
    0xe45a84c4199402e91130001e800f80665020840d29008000d0070500c120340400c040c25012008441440340c01e540140700c285841024040d0351441074607000080c03500000545020856404251841004040f12000c1c0b4154414065203541c03d020b1401c20038000c20042503442c00340562a55a0b148a01c2000d050103189071506095407110800700a1492000d00284110351841c40d0051890b8003e50748060304134080c20b00418620303c18000c0701e1920300210010082d40313007040744004403048c0c510412505100401c5040441c0d900b60809002c400400d600949401d0f80c1c103080c0b9a001d000010394061154030f030080c000e40007a4004c000590003420b42d0743c4c840c0030200c00f94803e40c60408081c400309920b2201250000740e020110f0021071150702444c040b49176010040384240c60442a45441030816002440800b190002d5600340c40701460000704049031a01c1401c01050920400d038070f0703107040702c04000100110701d40c2118500000346000c0c030f04029507918040c2419848041809620740d5501460304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 410065836 1250 410064586 410064601
    0x40b09040b0607210e03060f090c0d06140c2b270c09090506131104060b0307030b150d09060b040e030406030c140703050c01060b0412021c03020a020108 67
    0x4150007641c1d0103890b56503106030030305220015034100e07104001582d16030f0f03c00050140c0b0030b0f031000040d0701010b002005581c03145c4416114103d4001d0100d4000e208407411184c40707139034006240c1c0c81103000700c0e00040d40078140c60303941018402c020601e00050504000c65011902a403000c16a0a005500030b00e40c0410f4000d04c1401410000451224007072442d07407030b442c1071170a05a008044902c20800018040d6480c1005000d4486101c0e001c1c0490300000000f59185441d407181701082c0e441012403541c103a40080005003111501e070032000036900007008200400c0d070544580311a0038411505445201c0a070307000c40d074042c441e203035183c2441d98462110f00108500f90b0003890036400005c01c14001c10b461100050390343d40007480344c00c001908041c2650580d90050503d880d02030315001d100c61509200e030b1400d650b03d500c42222101699a00d41c0000f8560840401800c0a0a014003800c1810b10721401003159901010300000c810303000b0240741d40c0000350000f5120f45001c2e42801d220383c4d165254034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 410067086 1250 410065836 410065841
    0xc0313080901090b130612050705030610140406030c020c0301090203060a0b1201180b070e0a0506070f050601090b01021e100510030c06020115060c0b073e060702060408040b0904 78
    0x14040d14030410013080300398841810440c0d901c00c0c4c0f8025550288504000071f142400c0d100240c403810003098003000850228103081903459448081406c1c09206030490600c9040300c0d501c143c0c0304400203a030700d44840d0030a9a05200c203004000040b4001d2143c8101c07500002e444e060301400c1603000307540d209050b0b8901c1d21403415030300041080c03038000c00810440040070300380c013415a0300407036044a40f0400500d0b114041d2802e0240d4203070281c0070f103a4041c14081404519407064038180c2e107151000406a0000c0c03002c000450282885c1e00c00441c4d03011250001a203041c41030014030300c08820700c92115042250000d600d042103650300402140c1504c80b04140484007119800217848650003a0300840d010350150044514241c1464a10302d055669101c22524102040c40080244d003409000c2515680304008000388501e0800f000305042034101e49159004150120b004840c00180e002107401042c1400303590761061082c005443e0520b010780d11182903106900a02500640101d1120300030388859 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 410068336 1250 410067086 410067089
    0x6190906021303030f1704030c1a10080d05120a0b0103090510060e0a050603250f030302060907090204061b060f0c05030a06060504062001110a08010e0c031308090109 73
    0x240c08641d620410729161a1000c2140425408260900c0c2103580c2d4900c10018400b0440c255000520640c480c2d590844440c1c0d5500c00c20360305a0002c20f450751102c01910740f000d0050301403d80001081d841c116a150502004012003000e0000070300a442c00075003a002c0d40d17030f40030542940000d0750000060050700102941c0f580070f07142c0d2003440a2130008088690144064449a4000c06080c5d6240070042042e21400c4940a405804c1072601075210107841c04400383c411a03080c0c00401d5070751a8411409081c0450b4005c2d401a40206d062082d0040e051003404050014004107600d081c0c02d040700580111260003007801d00401c1000228240a00b940c01821229000d5070103120f02c1850700b40c0100a500251011341c41240b0b402e400044407400390049904460381c3c2d40319038401c014440e0101280c0004800500503a549800029a940e074460000701194812902e800510394141400c5a417030000c000c0c12400415002c005100042c80d81841c021059a0f100e400c140d582c418400040311400804d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 410069586 1250 410068336 410068343
    0x5070215090a0606180509030f0901031d0d020d1416020108070c05060a0204050f030106030b0a020f040302060d02070c0906060c0f11090403021e241e070c0b090d02061909 75
    0x103014000c83c000e0000c0104100032100f40c24180810b40b14001c505880348182c07007820303001400070810b03050072f54040d400c542d40c204a000143c2030200f041594070760621111801c51401a040001d4150007035401001c0c14003260b4484201c181040450132030900c403042c00500280c140606d10000901007440380401d848072650007000d0314074506040d900f06000e17420900400f0700c207401c0310a50103e1420140318036800ca0703400441401c0b90b500d6918000300254065140414441c40030800803001d81c660703130b00130400c00c04140c00041e602c0055041c100001b0b01150880c003405401c01c0020058903900103025040c1070307008504501504510b00d400c140541c480042c1581220f6100100024140c0118840030b6045940008035070b1505080401901c9401c0c0680d602c212100d207280c6000d54100003040d03103034808500796448241c0401310700c4c0c100182c20b0450300313000062076150318141004518007246800200010041000707420058001c1d458800c000c050010b0201a08441e44441f0010707042906010341 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 410070836 1250 410069586 410069591
    0x9010b220e01031401020a081f05090c09040513080403120c02280f05060301090c0e09040641040302071208070c050f011b02030703020a1403070905070215090a06 71
    0x3992100d000c0e04034070901c000d0b100c000d030340d000401c40c0410600894a490700c00e50741c1c0117201d9450f140032581070710317819001c00004a402400890280c4990440b40c0c042c0c040781070f1a685500c5a441044281d0780014410552074000c000d014001610f0a029581583d6001230140c60501c00303070000b1030b01c0704032003034010354000c00c0e00e108412510394252941c031240002c0c40e04001c200b88c0b60940c0c864052082c2c440c2541081782000108000100d942c84030805d18105c0c40c01640d040040e90000e6101001030701c0c00d4034540e40e100300d05c0d0400100c07145a01131200c0e040c0301000c0c0c0c0b01040380e400d407a0b240c00c0040500b42004100005000c02d8801c5c020b4034007030151045004072000b514109000716400c90441210f43c017034920300200b2070b40380020211903940e0050b5996100061000800e04d90001c041d00101e8040c0305556020006941c0d46503c41d001d07040c810030041102d69400101440c04200d544030307041e0f161a200520506a42c00300c1c0e2902002d0811174111300ea0b40307038144810301e484025403024065030f2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 410071942 1106 410070836 410070839
    0xc0402040f031e06290a03031d030115060e030709050c0319020418020a08310203100f0e060907050604092c01020d1a09010b22 56
    0x1800c90f0600d0400041c1681d43c1e078141c0c0d001540c3c1c002c206010f420701c114142c008040c074016081c0300300d520f000040c0c40d41c1c8003e4106d0b11200c03004810004001c08888981d1400d41081081904038218071101d1540e501c0b000b80005454080603110340204031000994440e0380c02050300441200c030440d480c5d601d801d0403034650b102002000100f029000d201c0010084100c440c100b140580310b14000d41e8810180c6030003843c420004005c0c44070440b040d4581d0340b0184065030314213005c0030740d2401c0121038003180c000a450144030184030310f1454200368650605038560b130000c000605102d0112401034a400d580180c440a0703038010300341c004405000400403c001a042078103c0a5401010402c40d54200020b811980307064081103002e0b900003440b0480404c50f8030031780d1010303a0050501101d038001100060500c110600c60041c14500c0842c40040c28403c0b0001c00814414020050515a = true := by decide +kernel

theorem cover : BRFrame.Cov 409892086 410071942 := by
  have h0 := BRFrame.cov_init 409892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 409892086 ≤ n) (h2 : n < 410071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
