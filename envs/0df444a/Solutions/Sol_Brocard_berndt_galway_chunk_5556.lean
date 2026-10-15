-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5556
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:15:25.909045+00:00
-- url     : https://prove2.me/submissions/8b2187cf-8ed4-47ad-baef-800180473857

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 999100719 ≤ n < 999280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 999101969 1250 999100719 999100741
    0xf0717090d090807351509070501020c0a03020409050f06070906080a0504240b060c010e0708070807181104090c141303030302070519051e03040e070509010e04060923010509040209 79
    0x4d1200001c544541000840d411146e00c40030f902c00c0742801d00346d03510103072910012611424030880c000c0c1c0c004c441c00030500140c41c0c84c0d44400500c900c41c2c01111201c0c581d0300d28060030800111100400304984c050100a440d0b004003501d41c3c000e881f018104101c3c6003d54800c032009150008103070300d4024488041910b03c240d81e1000308003540060001e516990b9000049028207410700340722038036004038100007615480001c0c4030425101d022001c0c00b140341c1800042241385690619509d001a201d950340e0005103a02c00092010300403c960200b0000500c0d800039040c0314001c8050703044882c08100b01080400b861300c20100380ca07810b1901607600c03a66420240d00d003803881a6841c4a071100020030b602008000a280c3c65001c0d10104498198503c1c0c1c15600d8490046109201e240403409001139441880380b8000d000003001410444003c103642d0000c1001c4500c29040100c400c0e9507a00c00e540707003051040481880ba480980d08041d55070502001c5004260081e000a00503400b46022030301220340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 999103219 1250 999101969 999102059
    0x908030f010f0b0d1508420c131e0e16050a0302070f02060d0903110c09012606090105010f05041a01030504080d020c06040b0c030f0f0717090d090807 66
    0x11180c00c4032090001100300302456500c2840c3c2d1001f0b241003c002c43c4405140c1548801031380f0100c041c06c0d4040c0d4030416080c09541c0542e02c802c0040050700404154004850210410305482c8110340d51902d052020198a81e03001521002c51490380da01d4181109502808403504140c56150158840301d81d450062220140e1f03010080d8001804111000d007645140d01488509000b6586d122407001d40e207283e10781b58004401195002b550300c800500030030b421725244080303c003084071038070122011800d00581030480555640203e0394440c4010031601c3c10b02c61100c805070404560411202c42050340e01c0c00002c050b40c003003606041d1200300003001d0120300e1090b40d490407040d003c19561641500d140b0740d01e032081210100c9008400d080410001c8001c8800c2e28402c0a0800040301c054844114030400350500401100c200036038041094540c41c43c00c070005014104600007480100c40803880540344190603084a001f5500c87c00c030030806405014211880300980c2401008800b01040f010038245d20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 999104469 1250 999103219 999103229
    0x110618100908090301050f0106050d051003081611031501090e07030c08010606020615090402010e12070e19020a0504060507060b040c020607030f0209032e0908030f010f0b0d15 77
    0x4585112042070041540040000700b0b81113000704055074807015210702c01c80d401e009150005406000f800f000300d94550109401107a0440c02610203680ca540f2b034040c1d54400001610244040242e0004004107080c021030340308030440150040c6090f840440110b440140306106240d603c405800c0200d040510650026540180070400f0341521004c205000e45168810328006201d8440001c06402d1040d500d800d1030100241960502c2e120f507001100c21050020782c191303206403035026a080001d0304100d5007000708101c0c2d49a00c0d42d483c20318540325420b8200c0494070203160040101b066115488000ca50035601c880c1070407031302c1d80ca842c10102d004005441c03286801a00c0e004100402580004040d4403c0d039080e0340511a98051010020581c0554000d09070580d02888410040001c13004002d0100c020b40f02e205140501180151426a03100040030b64503190000300740480c1401084031300c0d0140c801030082200141c0303040811703281c034400d200c8032201d566550710f4000414003000c2e2041c0c006007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 999105719 1250 999104469 999104471
    0x30a0e06010b0406080c0405150c15012c130f030e03011406040f06030312090311070f03120801030f141510090f0b1318080c0606040c11061810 63
    0x90b85504808040354410f00803070001c6460080040c801581da1400c6605491000d84241c01800c940c4140c4501d0f5000f2001ca9000c9002d8401d0203041c88043c0701d140ca00070419250440700e00441500c241c03514940c0c6441c5c5480c18455a030421042440e804e13134824038564000c1c01e4600c3e0f0a00c50404540c0252550282ea038103500b081c283c0d0780c1040904401e07502980c0207d0b810041206507114100889084c0e2100030701103801107a4800c0d4210300b903400002c40324000d050603203208080b5090380d0300746005030f080b41d42946010f81c3e0078001e10910a051034112805800c200c0c02c0c40d415900e5550a030a03080000402184410912400e060b0091222200c8210785030002600ca08180030705190395a203900544990743d10b000356031280d43d4003a00991103051000382040c0c4004101b1280100a01060a0b101d0f100e08002d1245200140f4031034010002c000c00c0d0b001502d41c41c1880020041503840c8040100104695421010f00c101d0010031060b8010401904000c45040310061290a00321009040c010032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 999106969 1250 999105719 999105721
    0x180602070e0115111203040b0c0a140f07051c030b09040b06041e05070905030f010c050d0203040c050a09050f0a1b0c0c050a08030705010f060b0d0f3b03180105030a0e06 74
    0x1600042d8091401f40384903035540d00541c6e603400e108420034010400a030000034141c1d6240a200110f10000b46401c1503040d0b8180d02d80425502c48a10700340c980d580385003540c403030490f4140d040b030b80c984144c551200c3c0c106c84040c110304103074464900c011070290505124942d00d406445c4030443c0d10301c032050b43c075003d4441800649014140604030000c07a00c9000d001c0c2c01a54483c400d55030040c03260031260803264640c1c03800c1418a190100013034000030000c503558040f00784049029603075882c01c080144281040404d4514183c0503510880a018104c05502070034204a20341d01d0f0a0484d803446040f0305841c002500c1d030070701c1c149121001c0441e40070540201c01c0700030105d56503038042b005140f034a002d80002e21081400440a40c1125064855403510003003d01038120800c1c0607401140303030a401c8050100b0b00402c44204030039155141a0800100c1a8a0208000d528240d5080744491034480307010398101540000d07000c0070740c0000c10a0074100a0000b002410754a51540308400f1500007a00316291 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 999108219 1250 999106969 999106993
    0x102030706060e15040e031209030d141f0f031b0504020d0902121b0121020a03061d060609120f0d0c1b14041e0c180602070e011511 58
    0x440c070050301c0000e00381a800c001e0403640d09045c0201d81b4a507090a00441c94030303040b29204117042101a02070703201400300300014039245401d40038003014510014580c1c005d034103041c84681c0040550103d1554040d81c018001c100f084043d02d9800b08890b0003900d101000f00000f200c1500f80c1100c0d400c141d921520204e04c0000c0300308140e1081d62020710903940b564595000621b003d50b10045c000c4c2d100010070910300b02099951058543d03043c4603422168183e5480c41030390f401070913078103d84401c5000070350302c102c01c1100c104045461181d09812440e004410f040000100d00c103441040b4940380510540030996564500c100845080e6106103002e860115007007060080010351024030559980c03070851085124a07010707030744907800c85e190140c00c510306131500e00600002e01100311105059036000180038405030094000c2241d01c6a07165503806000480104200d001c0b9040d411400455000c0841800744180d0b010300e8a05491243d41c00341c003010300c103507011181240b0112648005008042c46d00031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 999109469 1250 999108219 999108239
    0x6120e01110c070b2a030c03032a19080903040503030d09030923040c032d0c020c1e040b0d032f0d0c02041104030f050105150109030809010203070606 66
    0x48520b5101d056402455031144240600d000f8001c00b00c90944141c40020030840340c17021001044143c035003d80e8280a00059090704603001117070070001d0103e401014038071001008009195154a5584240c14241c03900c0000b003a0a140001c03480c1400325000200b42c9048081050310b00500b001006c49980e46c0d9900c0c0808040c00804008401007884880081000102c550300c50107042015034141100700b81040c03c11000e001d01c0040c00b41803582d541040802102c22184003031030406480365409043d0004081c034812204125041811500441106400340c0e82c1da008250901d1100b460080145003c1000207000b07180303220f125540700171310042017820141c22400c1000c460382541d00703522070140c0c0d411031120b5458003881021066041100840300007805a00081070150001d03100162080403c1d016014503409900207413184d60091412201700b00003401480c0d484400c0102c040151051800040c1031102a4003004128120208a110b0310781d10070400c4c0c5400f80e0f04001d042c406265a4170707a4030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 999110719 1250 999109469 999109477
    0x60507091a25020102060c07021302040b0c0606190302090604141f06080105010504050d060f0203270c0114030a14270109170702030102040305011409070609030c06120e0111 76
    0x20307544030b42c00d8a000108481c5034491116010707000b903e07583c2c0c0e4201c1441855480f16500726030104491301202c840e403075144094005405511207243d80d50b49541c40d854a85500140414412071480e00c400b4802e000000d0070368120303541902c0d03040c3c141e05d4840c0000c001e0020016280c800d029200200041e111510565134407510225850715034107a2a107001b140ca0041c24050107010030b0042204001c103061803282240c005001d50300020f60390412010072401e07684142c601c00c175802d0083c103a10708845601c0f20380000243c20440107004035071804001030039010700e6642840e582c840120000700c4420803500403c911194000b0b5182187c90554044040b50533948101c03a100128189400d0210005100b40003010f90050080725113040703103200c801c00300d42c4501c00881c0c01d0b540921000002520902034a031002480070741c80141c521700001c900d8030300107140d4840303010481000c2c0100b02050728140c0950036103283d03241c01d40c28507c02a80c2d801c09821514a5000b00307629000043c003685004601038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 999111969 1250 999110719 999110737
    0xb0703050403110d0509010e0d02030708010501050a09050f07080711010510031515050f1810031b061d0418051617100c09030b100e1e04060507091a 65
    0x90f804040c41410320b079440d46540c2200c80030030b400700200d03030360380d030042d8842c070020000201510b0060b003869012138182021035000324202e03910303040184003e2030503404204c06058140f0003008549090b80d0050b2002c00040d02d403106012800c030100751424480d403d0358800080c2200203102c6810045030b40b010361003440c84181c800d0800c030740b0f4000d51944240602844c48040b000074144480c00c007002c12410318240003003298008014112751a0700c00c0b0401c00c10b44600e503840c555020951030340c100b10303101e46a1507400041038240d04800f8085503403c0007000c4005c18404007880c04034050171000c90018521040d5010050092180d9402000310000701c00481d03204200ca43c8503600c0c0e0344d0340b80103120644a80e5803d1a60026102c2e440c41003070f586d2200500c81c0c01c40c604021540d41e207880c0c0c0341e0500e10541744074041c81040601841440c0c081c440503a0054209000b8040c000f03241700501c00d038600042d00c002d00c0d664075240401c141a1165105501070180721030307075a06600d00c144620030a41c0c0072800c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 999113219 1250 999111969 999111977
    0x7241b0c0b1602060601121b090519030c14150d0c17070512040503120108070306140f0c0c07092c03070228180902031501030c18090b0703050403 64
    0x2401e4452403011018442c5610f8000b046039403600001902d00d500c0030628840340d107075100300803018990b00e50b1a2500340c095684034240302c6402e24050207025001b161004031a4000e0310030401c005501c01501a084981c3e400525941c1c6a107140000c4840b54100020350b280040400c6147c42080c042c0d100702e802c80d0083e10341c4844141c00100e0a00f090404072281000301c0d1041c81008a40d880c1a40c0681d8010700c01e01c00d90745000f08a181c0b44044d694280c103d2110741d44402c0b41841000454070844814200c1001d050105150603d0071000c01080240300641c015000300300d07074602d1030342080402c0140c150b211040c0440031001903071410080704d170026488107000420f098058860302100310360249801030400d0040811813011107410440504030a0840348141000151400b6501802e03030410b180f1a1001c111203140d801014502508030b2411551840381d40c00410000385c0c0c01159504842c2c010344c0512080003030300d100f84010400050044d04002d60003041054880d89036001c07070311452003612 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 999114469 1250 999113219 999113221
    0x1c11070b210f0a0209010c0204090503130f0506040605070201020a05010504110f041e0903090f180b010206061011011d0706081b0d11040503012405010507241b0c0b 72
    0x5840e2114540980c0d0520a40074800b020a04000d05500201034151043c102403c51001d103901180c02c03200c840301d0035161600003145240006807200565002000d0481c3c5035000c1c5030602c40043c150340f04c1c40c45a0024440005440c6085900038845005500d800000821030f0f850942400310b07100c14105507035032143d90113003e07070074240c82c1c04e2041101000c003440e1624444c5514000c0e0000a0800e81015030500401c10700c0010310f4001e00d62000c01500d011078420b04000081c0400900b41c0340900c0407141075400146c00c1051903103500c203030748482120034500f41a1110300c2c1c203510f0b03004140d8107103504054041c42da020900000000b50b100b044407aa5911003045a6402c00d8128440c0101e45110104480070000c0c0c0f031000d001c0303130012800c00010074070b00c0d03242941d980c0c0001d08680882c420402c483c0d8200c24241104d5946280403802007001703082091501186607074400c4426604910011103401039500340071060308030750140d9802d121903481e14020080300b410241c00c50301e04000444000b03014030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 999115719 1250 999114469 999114517
    0xe0f010e010b01020f0604020603090c12030903010513020108040b180106060c020307061403040b073506010503090a140a0f03090317090a090e16150e09091c11070b 72
    0x42c0307170014070b0480d0003511a54440c1e900b0000c860740060014000c82c07161644141c46d954480d032184002507510001155142c1d690401d2500799500100850301c146910008000540d0308610340550059111190310116524181c2c0c02c0e0714010070b50350b030081961030044007060064024040075940c40c002c50880d0313082640c1c0d981c201c504c2029100d80e2100082c06001080000c0c5600e14003a400404604003612603002503002d640b4071105003660340265400620014110180840104d50081c50a00c0d0462952900840c841e6880300403802c01058103861280c60703c0d400c00f0034441c03000c0c4503070f02039010042e8060505004042c1403682c00141e81443d9079444101c11100c01c3c000310b8030680030141c2802c00f000d10300858400101005206810039000350300b40100644a100340907005000b000d520799070b4825501d080280300001c51052180a080f0610901200c002c0009840f94420004401034032164001601107500c000307412030100291003450000705130041020060a04092801e0354080d00322820 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 999116969 1250 999115719 999115723
    0x3c1b01020412031206050310140f0f15010215070807140c0c090411091015022a060c03030f2e0312091d04050f0319050d0e0f010e010b0102 61
    0x1d8450a100100600102c50000e4042c140d08070b441c003c5180001125070359800402d0030000c0b900009084695180040c0c4c901048034003d60b83c01c008100e54003482858500e5024048680140480c1c103001004600c03624a03a10070825013039a481606500140d9041201000d008008180d039031802068a0003942c03500301449100390f40301402c1c074100030200e20b0003100072312070b08102c081c2095500202042c03000e0300540751034131200d0242941c1075a951920b4940464005480d81400d0b5180454100c0990440001507049071a05504850910018042c400400080305445046d6488916000c08400c0019145404444502c921450403001c540d501d0540300044000c80001800000b002902c3d07010300c04070700c40c40c41010400465040680d511034641c0c05a1b000d01150700b907001c01c1407a00004102c10030105001d100f94250940c0011800c1441140340301c2445030035018a230081040204030000c0c940f48582002c3c02111240f0306a511450031206101e003e080300d0700c1072607140e40c20030010034869440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 999118219 1250 999116969 999116977
    0x3f03111c0c080909090a0b070f0503010b0912060702030d150e070e0112292202070602090607060911030f07120503120f010603140c3c1b0102 62
    0x251024440002a1200d054990752078a00d001d03200307010103100c00c000c2611103e40040c01144642c0040003041c1103454810700e18000103200504210741c883d01800c0302d5800c101901d0555a5050304c65403070b6154000400c022a1001d5803040c4030344155010b0124841e000b0000740a8600c0d084002c4c0900d00420741c009080d26900c1c410443c6030b030402400205581e102c1c0c4081004090145003044414194482600540e480604800441640e17081445290800040c59070381074401612900000140f02e001003990504403410202c92580010340c1108000c10340e4122010140014003c58560071142800070003000300c401c048032522100e558969480c64009112655840d80500410703269060291220950101c43c000715100d110078007100c0d105583e40b44200d840703400c0d844031000003985403200080540d116010310403000384007141404600c0d51848216101d0b92244070f000c910769540d810000580c0c00702c1c5901000201c3d080d45000003418401c000812503840c1f81d200c900c040c9541c40c0303c0c86080303103d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 999119469 1250 999118219 999118243
    0x10c17150d06020903010e0d021b1905101b06020a02191e0206040503030a0509010f090b0409050606070507080c0301110301050a060e150309030a11030901093f0311 72
    0x12074211480008440307030011300403080054000f1440e0003403244558a44689800200c0140e00000b0503000090301c904402103a44004a400b07607800d13012000001d45c2019a4080c95005444210004404a0007090800f00aa5442d0191045419203040100080d00242c8080d00140030703210b156080341038207048503411310340c02401e00246c00c0c0c8a07034a480c01149814030f01b01d820900034800014a81e070140040c0c883c2c8411034035120b079a020711170700040580007200c8100c0280546000e050140c44108820341302035608075000012030f51140c000003401809482401007084c40384d00001b055421000c51400d00005054000b80149644c20040360302c0c0340800d001351904810451820071035640b14034240041c2c102c000d03042c0b45909a92035500a0b10b40d0040b030304100940c1c000200c003012640d214140003880603440d400346080c407000342c0c002004562180300d07605524208a62240c0b009031104115000d050030b01c8001032000c40300c0c2954260711103c8080c26000300b50b80c0360901d0a00d400c003042050b0450 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 999120719 1250 999119469 999119479
    0x2011b0312020d1e0902040501080307030503190902130645090f03030b010210090b16020c0406030c090e07051f030213030312060b1c02160203010c1715 67
    0x50780c6519104000d402052000b80380342c3c0c0b20745010b52007803886203080c0140c1d018840e01140003211030050005580b4180c2c41030440c2d90080003808003095006080d2504038824a05400303a07444c202101d90702802d41400003079030001c201c110344080600c80d0390101d0300b00c0b00802043c44610740c100307440400000c1d5507043c20014012500c50001e09020a01d00d0300403010071184001040155626138400300b4090940440100b5591407a0304d42940e0100000d004420000c0d006114440b825960810442d1000d0041c020901d043e00c40170700303550f000340a5180710482c041d20030401d0580d07030306103440780d0b9206100741c1c20000e2805003940072560010542605442c000b03001c03a17403c1440c00ba165244d00c80c1d11a094000c260b800d006e011200c1402c1c0780c1d0b40b4000c50103076490692a24040c0d07118402c43d4284d80c0445a80401007040c0540c40708901c51038604400303010001a03c0384003441c00d40c5148054844001d50652a0440c8101c43c150010f03040c2161146426500c0400e54400d02c02c10081c50034500c3c415440303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 999121969 1250 999120719 999120737
    0x30d2a030510031a10090902010c060b13020c03090f0d0f1704030807030905031e0d0e010c05060a020310061b0204020315030a031e08220c15020a02011b03 68
    0x50003a0032607034001c2c01164a5030300040c1c0d0780c2c40b102c29400c4a01c0341d11034030300c2d0f102092218203491842e240019011020040150440641c00a0000c46000600411642d101c00e05810150b5440078480112556103c040d590307034681d458032544907840f07411220301c81c2c4252481c40c081ca0404480740035601e82d00a1034010350704681d45660007002580200d407095807200700030120004806501401c1c100748a5198149010701b0b0600701404d0170020f101095102c0c03001500d03030b0501d20b4009202c912842c1c40d402c0054011001c100100c6106140041c06444c07481a6402c0c00261000b5600a511480b070141195038a180c0b61101162400a00180c11030b01c84030100c454005890719500441e000480c41504d15548031080380442d0400d01782c84030a9002c1440348194020701900710803a1803000c0b00601c1c01500f00c7c40c020789507115020408144107a0440d001c03011008016601d10200007420f45c0e020841c41d02c44031003400940c0d1760b9003000708a0000707900c2c030416049082c200307072200040c5502d5165010341c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 999123219 1250 999121969 999122051
    0x3070902091201090615050609030a0b0c0909010e010303020d0f080f130b0901140a022b0b030708060405100c0c033605032b030e070512030d 62
    0x40d402810600d03500882c40e002c00c9050840034403983c08150721070a0041481a95012291000000f0758040360250714100100281503401264841c4020360200d0410002e48401e6a0218107004603c6540e0b04904258000301e0408030340031030b03541201e10070b50884d86040c94800703088403000034906a502c00f082010700412154000000341d282d012525480661004031540c40c1d5064030380060f164100243d6481e004d00c103015504042c4140e1203442e4031010342c60802050910415640b038048181100306000c141020b07400a0364000303060310940182207070146a290411940c03940015102103600d0303c07501e2410707441c8104e9401809695240f0752a0000500341c50740781a109961610620114602110fa280c010402c60b00c03010285494201e19004403a13007880203151410540603a1500c4059010844050000c0c800701007076904989803401040c0003060b80310362850007443c0e0708900e6200926441c01040440c0000140c0046a5041801e00112421070060000c0c1e5250140703507158980c0320032100903 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 999124469 1250 999123219 999123221
    0x2040b07110126040503160b0a050603010e0c0f1503010807060e09010509062101050a0207030e191208070b0403120b1206060618060a030b13050f01030b220302070603110306030709 79
    0x203030045c0a031096929019400141808005c2c440c2812500710304c2e00b0781807240038019441480e81c0300308103400800c9210080050036558180d4001660301c00c41e065200000c00d5180c4041e08070004052011a940300d5844030800d80d11040d460280c440040c1d0f034000c2500d503a142540b07400f0304031807014144501ca41c54076810300605501068841c0003121040c042c3d46445607013445050702c0780c2e080703190060300c82c6114913004004c4002a4009072094005105161400e40b214503400c1c01c503100312001c0c0c48070f6880792502160a004d03440c030240501c04882c2c108424550130600101c1546065001003041c000b140d8108011081c14505060a07036004000080c064101030008001d0100c442104409800c070610004046600c50340421002a84a01180c0040e0800008d20381e030b0000042c1c000c0c0010300d8610650280608144000b51260140703402140044106010f41d0144804c2c40040c00000030340f0342000396580c1c2480c841d180c0083d2030086640d03034015954060b03030301480c0020054000030303240003070b800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 999125719 1250 999124469 999124471
    0xb040501030e03190306080f030c2d0601030f1e030c030e0105070b10032f010c0807080d0b0a060302160b180f01230603030d050703020d02040b07110126 67
    0x1200c0d0388001c000030300f144850501c04d00940d940700e60f03005c05c0280c02c12450700d0802e61100d0702c40750740764020300c0180d00982e80400c1c245036131400b5a0110004030039244500703461072241a5400043c0c0580c1002000303018403040c2107414140079029a0041e440144841c401000301d500b009030000341c02d0050840042d2081e000012000310500d0a181003000a459600141c1c03000d40e45564a030000440400803c0000e2160001200d1610780304829014001c40110000d424000094100156460b02c0800c1158030f80545410b290070004060b2034021071016440103000056a252151104000004800b8428002c80749000043c405c40da1162565a44d445004c101c00b400f0483c10400055941c05011020001c04c006a0088400441c0f03200104c021083d01c540c0000e0030202d0442104100812a10004102c504e00d401c6c110001445a5541908030001e0003008203100c15940000f400042d03d1003100007402c081400342c40e400c40603951500054400004000c1c1c0000000a2a002d5403c0b80900c45861 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 999126969 1250 999125719 999125741
    0xa020a120504050a0e0a050a050906040b040201090f0612060b0306010f110f011b0f020616050703230a1101050709230301090609140f0303010b0a020a0c0306051b040b04050103 77
    0x1040c20b050711600014806062500a040d00b12050710400c115003000740980761300b0101000f803c0000e41089416036403110700c0184003401421036540800c04591048004200070b0002d414803804041d00c07084000c100411005000340545d04244c8081a02103c10080300d021324416101c440b00266403d0041d600802c0200d200b800702e00880c000a84e04032802c0c06a41e0708000c261664000381030218030054030160110300823704640c805c80c02c0140744c2a01003000740c4000b40d141041070b203804c140e00d81100c43e00514804421030b01100300e10307041504092405440814220b03142d641d02401d510754450f003290012120f020001c1c21840003044050001c02903444003a44004504031202c15400109003900c0d0501d01c05c4502d207a0303582c00c05050040040403c000008400050404500c0c1c1c00c01c1a562804107008600381c010000542242003402008116890381c0e00c001c240302000c1d0b0b039080c014024401151100d010340051410f40010440420445040d02d0302060a6810b10703003801c00440081c14846c00d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 999128219 1250 999126969 999126977
    0xc030e010501030b0105120f100513170c0d020c060a03090302121204060c0f0f0f020a0203120316090b1813180201030c020102160b07050f04030309080705060a020a12 73
    0x440090084280a11806035003e440c040f40c80394034040c180450700d0542e01440d95290410840310010b20408039041495008400003c1119200c460002106c078001403c000c000c0c011b0400503021811180d4050b003040c4002d0070585002000c4000140d07103d10041c0140d0394800c1d010407030384800c07034000e0b80920340d01400b0348100d480100e1910320040bc9640f1154400c2c2d500340308101004200405409000443c04992500c030b007803d29081000750510004020344d1003841406200000384070700c200040600550014100c4049540480710410164001c0d00c6c010050316180c0246662903014106103421070740210306075841e00c1c910f41d078051242e15038040c080d9405426428401c030300500d1401080724004803c07030b105041c40c4180c40050200e4010a03a041c083da40103001c02d030444240c002d040200f00f90080e840c1441580c5030f100031505031151230f0455280c1c000c01315003c4240759107c80c42c00141c9070036a04480d00262540304001103401134028500050f481400712900264220134040d03000d0400d810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 999129469 1250 999128219 999128231
    0x11010903032028050c04020a021509030f0a0c0c050f011e02150c0a020d08130f0606051c0b0105180a0b04060512030928060c1506090506180114040c03 66
    0x1a0740c040c02010000084800a04090140c03c2c48003d000d00385185c0030840d0300b14079086100101945900b560700900300400700307420000704001420310880f59285030414069580318031420f0044c1582c54007480076550f07421010f07000301d9a4107109171f224200e48416198828641107072503070180a040c09071222021400303108080c4990746000000d6a0086040404140e101c0309415402850f0050411407001003120700030070f102c142401c030f58018601036045201500c2c03100030340c100305004e0007140d4071a50300702c0d5803140078454072040c000340d28080c10700c56424001241d80e40c40400892648071811100c15820200110364110340c01d40c402e0744c09080103000070803425551400151080003010f01000030b5000091000d107a07107060920881a1800100c1c250a00311041105003015000c0b80120018049000320325810701c84180b10041200080301d106001090301c1c2c2001030701030036065034603e0140010b030302e0320100c460300d0380700c1603040e18010045c1400c00c04c030000400c0003809081907002c0501d66500c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 999130719 1250 999129469 999129493
    0x10b0c1504080c1005070f0f030e06100e09010506090c0703181e08011a24030a09030e010e100f0c02031b030705180105010e1302070609110109030320 66
    0x48526440340b40120101a00c0d0b0b04048211030901e203c4194034070340b09182c0070420180c1c42c1c1090075811040d0403403034000b0b0748540c100e0040d0020b10350340c0c0d03003a10716129102c00c100b210003d0344905800e940002041c1c03009500c82d03041c0c0d5426540705a40041d80605c0030350000c0c0e800c1d805000a0400140245014598224104401800c03001681c0041e03c100400c0c420b00c5605030482001c520003022042c00820000001c02c0044242e418146d181a200d0100303c0080ca400e2542d1802e000e60b0940314401c01903072418600711520042400c05030480c0800c00c03070302c3c24030443c0d070040341e41e5400e030a005040e9030880500303420708840b84210f032031030101032110400424016880030491084c1000c2c8012038031409148040c10103103080e84690106105154a4118910022000f206a41101c5083c02c240d070a2910310800160000015072741581e0551010551800380265034020900c03060003240403144504540700111110800d500018010442c0c980d11010403902014207401d0504802007034403041d01c04c034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 999131969 1250 999130719 999130753
    0x2042607030c0b21070807020c030a020d170c070f0f0f0e0f07090b070f051204051e04110c03072a210606170d0507150509070e0a02040303091706010b0c 67
    0x75100b08000410f420f00b0064159010010402130000c12402070221080c42c1e40068004221a100103200240b01e0f00ec0c80000044241034800e14003203041511074445c3c440703c038200184228414810001c40c0b1700d800140395469207440b5410783f2243d002c0950566902c05035403800d174101800340020844c4040c4005050343c031000141003080d100d415058400300701424118a00440f02001940f222001c0008208070354030012203c800500510001460380580030001d001095490040900e02c0400140c625040b20003100810710380e842810f90103140b5001e180709140c0200420b0404414107002c5106010a50300150004202c0090806e8190280c0d103d9031021b0941e4115030084c0f0b040850851940203035030b0b050107070b1140d44d00700e031400d036080281c9500c80d44800c1c586201d420100f2076175000441c80b404410b004e000082d1030480c8002e403150030094040c030003c0d4001d120507000600c000001252004602e00712020104c0d1580017004603034200000c1c1804c55004102c8114103104400e0f0707000441e142 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 999133219 1250 999131969 999131971
    0xf0f070f0c061a04050108030c0316031818050702060402100c0f0804140306150d2411191103070b0c160803042003120c010f02042607030c0b21 63
    0x83c14189405144100610060b144180c0041020f0b410510140c191810000151a01c004802d61410243d00c05402d054600d15030200b408015006580000320300504d01740e540ba41c0162035800e007003140d5905c03644120307100d01d01914029409110303401d003c41068130038942c0c100366074003038a815140140315640b248450790040e40701080382e4008006000e0b00d890140400b0f507105800081c1641050740400000e21000400e210092000c003820b8802c0c00350400c0f2540103140107008030000c015108081c03000404940000801528824005496031a01c621890381c600c500c1414078000c50916000f0741e01c00c9109400107101e0014200305000c0e1107407480c0d080112102603401020300300c0c1c1d60300f06030a00c00e0741070101803481d9580200a0020101c151000203005d15240c080b1344e54252900400320301107014248691284015a0010501086141580c014020a20322012800c824800f2192442c6e8444106200142c081e02e40c030241001292504001043c806440c1641c02003240c450040d15444440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 999134469 1250 999133219 999133241
    0x50405010b1c110d03030e3f07062414030105150306280f140f010b0a080702011803030b18090d050705030c010c05070501050f0f070f0c06 61
    0x9101c100800e402d0405501c00641c00030722031085101405662252a2400f102c4031895004641d41403050080c90b20a50205481c0c41410090b181d0710303c00030b446e040303917890b0045014001010195a02d11486a07a4001c1c04480c3d8120b00e0b140d05115498446a00402c200301c3d003140070340d54180c0e81011103100b018520014005c0318110809002d011401c0c982183d2004200003800e03529000d81c80165603001072030aa200c5404c014894504188022a01c180b051013011400e800c1e0030192a404915419000041c9514001500c4030150751002c1450701007007800e10418145402c20890324241c14400e01c01141e0042190002003a009030300d0042e4006100d222005400081c0d80e2040c45c06646003080c0400401c0d4802100d00c420307400c007485410380310300c2c040d40c414041c00400145402082418826030300101800c0000300319002c0c04000150142d4002081202e5551030440080c039054201610300f4001d940181b001e00340d980d1180c100b076500031002c4c1801d5091054508017440050310501540503468 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 999135719 1250 999134469 999134471
    0xf0d05030a050c1c1d0102100e0a030806040b0927030a050415020a03300e1c05282c0a090509100b0a0e0708100e040309150207050405040501 62
    0x10703114000d40c14000f0842643c0052240e035200c4c0740d400c0f1761098152038070710340059000800c0f105040050780381c070202450610b40d003402c141e000b1001110128003202e600c0d0098071418265a00d940801013100c0c4001006d40e4804c060b4008190406c403520001100007080c03c040d030528141e01c10f0241d1541e04030120074000954001000d0110450f6080302510300703400da0004010708080d6540250043c2010300344084001040c810042c1c0700c9503507080c4a200c0d81d0554004100514119420b44c2d103800800e002c003c0c0c2e10000410304600144223400715940c07291071001010b00340e000c602c0501001d54051005004020341051a8a131031101c80d60100e1860701d0050358508075410380340030b01803031038196440310f002c2914000c100a0b000e180880c2179115210311003000101c2000b0707000003841600f0b85030000c66400020b1710405c10150341140407140140d6101d040c1011041e910707440c0d44611441150020009030000100b001940752602403840181c09a00641d40c1080d190408034084030000c4500b91226 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 999136969 1250 999135719 999135727
    0xc0f0105070311090901030b0a06091505090609190b0619020d02100e030f09030a0b1f0b0405010e0103111603170a0507050a0c020f040f090c060f020a020f0d05030a05 73
    0x1e074251145030840281001c200f8140030350640001d0340360905100140c90f004001002400e15580c41d849480a80040d020400010b6045140740008101d140a86030240d00384a0104840307141c601019403091194040d0035045511102031007019000240d2402d402940501c05101c02c12011900000c00c01d10700da00800c00d608442400a29102364074041e01012031030002e100c0d40c0000c02104071100030300c0b61606240e84292890109191160244018000b91192000d02c480080010450551108403a00080d9070079168100c1e10900c0c801c520901c0d02040c24540a09040e5010781c1100c00d405a200210078102f5000311008414850454030440000340030741014031403082c00164031500a880c00384100010329220344054901d1182c60455024400844515400c654800c0340014420070080c205102107000202c0c07100103000c049038101c0e00320300c0e4160040740c0d0078810b04c011402489264020706401303850750280501d90025030280c68000d515200c4401c0490001c0008101d42d01969607541c0c2c1e1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 999138219 1250 999136969 999136981
    0x12090b090a030f03020a0219080409091202061f1211100c150506100c060e15090f010c050405011809020403031106070915081f030804050f061c0e030c0f0105 69
    0x10303c0f50580c0c1107106161050064580950b0700207a445510900c1080005810225051501e461302070341e0321821a032400e0840d0b4008003c0d11201c140300340d061a4084401944a01306180301440507a442c070b449102e84200d041228070f2041211200550040d4901c4142c950ba070001320300ba0000c40c220100105400712030310020440d00303000c03201c2000746100007040141003280010f0700e030003036184680041141c2e40c0c0a280034480c80394410410910590115a21b1030920701c85d140c24907400b21211003603806442d81404e2642c60601807004d80000740d07070f07441d85403508140040d913003040c0d010103d00f090511444045042c0341d180c401440a14003035103c40e008510303104490752400704c0003031455040040e00784c002c10891000707000443d803003001400c00d000c40d0303664858a01a4180f07040340707000451240030380c0041405480c1c3c0080c400d0702c400340d41d849045172180042c08807078840c002028104095080c04c00c44400c1841d401081d0100580e4240c80c90003600e00452860705500354004001650341b40d003030002c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 999139469 1250 999138219 999138227
    0xc16060f0608070b03040503120912031005150c060f0901061a18190306090f021806030708010e060109090503131805012301030c030b06070b0103062a12090b090a03 72
    0x409001824078038501d030076520207807680200c5000b8000c6281c240b0114ae12810305010302845a4031321300ea2192030f03280c21021000401030074419180540340034240308918103c14002c480f401d4030804010308003602c0f180214502c18100405407152035503250070114050290391240840890464060340c0c46c4c0548030000c00a07031100d410300d0751140702050070316043d04042c0504941140c0c3c01210001e149507850400819030380424000961200104d40083c5c1d441d1100d80200380122000c3d170840c0c2107503890f07501d802d0072201c01515198042d44801300400041ca030a8100341c0c41d091281003600c1c01c0203180b69032046409a2900440503144c01151601c101c041c451084038014401d0b41a07104000e00052100c0c1c0d0701c41c0843d00c0e00c9040503121110f840c40c0d54089d4001c034a041d007000e000305a40f4031b03a5050801415270300780000c5500c9424400218101e0002c11401c10003080301d0003100001c582c0d00481a00c0300c070580c20000b94055100e030000b80c00f04a4040010b80303c0c07000341010708a9240d503460018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 999140719 1250 999139469 999139483
    0xc0f0d0c0f030e0f041e0e01021e0304140f1b01021614030708100c11010c09060c0618080a08060d03091e08030f09030d170c16060f0608 60
    0xa0204500d0244000100d8410481651519003605041c0e40751065280400c6441c0000e244d101c0d0001c5c20003040d048400300c0100700c55800b54015404000d11219008250300383c0c0709a06030210030054503080c0c40040f900c46401185c005220300d05054803910503060160134010345101e0b40039160000c01540c120741c89020f4500700103035000d101400103540705002c2d00a441940c0c0c0241424030740082083c0c0056201003003188060810f80c0c00311034100c032645022001401e518103050000850704000c608800d0014010054210420b4803100f40301420b00d407084450241d07112094070310030b46510b41f1003140a956440d8000d420b000780c10f460f54440b007140c4080c0041070040e1003940a50840c0707141d2404a54400b207028151100413002d030f030a4180c107201e810407004090f04031000c40e0100140031071801c03285500401700d0010641c1525040c0c440544203407078000d492000300c4501c0c0e4688000885000c411001070102c181400a0942d41d90f100780c56003000c0760903400071302c5c00040d0341ea14240540e2074104440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 999141969 1250 999140719 999140743
    0x1020a0b15010807050a140a03090209090d030605030c0d0f0f06091a011403060c13081e010e071203081b03160306080a050a0f0c23090a1b080c09060c0f 67
    0x3052401b4030300c1900400005100a904000046c08128a140540700e50046005950014034006440c14141035035030302e84000180c0300300443d1424000003201e00b400704010403100c1c0028021205230110380c54100f910728100348100c4980e09081801d20014003244603c201c4503026610001503c510308600c1444000d041e0010b007a0f1803082c51481712180c1d030004816034803807404034420751103411000c0d0780c514200700c03500480c3c4140202c211082da9050301c1d8100c0403058010030003d01004c000596025140c0b11140103002100c2d00140f00c0d1004a0b00825010341c0160040540c07507070481840c080c4610541040d204000030000e940010303043c241c1c3c180210030181401d03a02810602c1b4040d951503641d601040401403040302e059613032409004002032980000c220300813100c007c4001480030340704c00440c1d4803403140c0301d401c2c0d410202e4081d4105120740030500d03960b031543c2c41c2401c0d01a40c06445a240040c441040d1100c00c01c00c0e0602034a400002e0040000341c1d200500d0710341011200310b400c0044000396 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 999143219 1250 999141969 999141977
    0x210140a1d1e10091805101e0b070f0606090c020f010b0109030f11030303041505150a14040e0d033207080a110a05030103030f080402031b01020a0b15010807 69
    0x2541c040844500b89031551128119149030655180703500030f071641e400d1a40072503e01510141038640c5132540b604494480c00001a41850703503500c602403513065108002100c04160900c09040c04901d0841e0004e0041c60b002d0900003201e034915503598419100c464001c18a82c5d070b00c5000800209404200c0c0300030015440c00240880d01420000801d106280e100140000100181820521041c0c00c480c0c0b2000070b01800baa65a8945814181c0403031585c00c00000d075292a00000613506c20a1540040704100001d140e8440c980c40c00b413410038030054805442d07512030380c1c0da45154201c0c481002115259881d86d02d007c90085000d1211207410701d0092004010089040403840380b0041031003515a1100c2e6a05001c2e09503125803030300c81c000b4602d81d104210310303040025400546641000c06981240e200703550b2035040346034958003152064000d1b64003e401d81c0c800703401e04442091902c00d19040a20600c1200c5004480f82c4454084080564055040414541c0203030040e507030003010319500c030019040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 999144469 1250 999143219 999143239
    0x30411180411060a051207020a020a0e0709181b03050105150403080702120a05030c0304090c1e0e0f150912030c03090405130206030702060619080a0210140a1d 70
    0x40d103681105280841c588030303000000e01010004d003d0429118650b24031601b00319246032000c1c01a503501c80f074100a900c0f500614000249004611504c60711810907030381c0e140704192604081094442103a01c049048985650f50318440010304c40003441e0500d265900031886501d0501030104030102041c0300b409e4804100410703c00309420400b1034405541c184c403504140c1c0320320041c840c242014030394010468000081c3c1c048604600102805c151480c020b420001d1500c10b000903217070001e000c481003051141000341410458002d8984503c411009420400c4184140c03001410743c0000e036250140080001c11483c0050820110503482c03050308800035490a01910712856980c003d008007280300300d03141c2c3d00085601c14061440d03800141e001e058192203050003c0080e45481d400c031440d501848203031918103441b0f90b60303d00c810212210305c0090041d00c2d03115000d0000c801840c0080c4010302c402210b284918a03507010003400034a05035a54000f981c800907111030424508403200300e12412080d6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 999145719 1250 999144469 999144473
    0xf0a1106040311090907080f06071d030d2d050c010c0801031a15090c0304120810030b10151d0906060a0815030d09080606090c0a0c0807080304111804 66
    0x10407003e40c00c820440d400c0036a5540c188946107001c00e81e81200b00140240c894103129240000381d10b50003007100b61140341144a0007809242581c0365855910390503400061084030b024000c0782c1d002810a040e1030038645080c05c0380100100c2003149038021000840004018250301828459210910240c0c50403078030a51443c2c4034483c503074094486c0368110824001c04251021980d0320750b42a08030000c0e000c00f4280c644015152890380081300d050302d002c4000c0b0308040c506da20a502e032520901e4250418409a821500c40c41c01c0440000c007092000754400f0342c0031403842c480300d030351102d41c50541c1c2c5c400003112000214462900e1007081039030301400060003406103030b50b0340f0825500d021030140f4180419540b4049105c040801412a16070513000701000d0101c0c0342d0303100c040da4050717810b540b003241c0c0075450305024420b07402005c44280d940f02c50b0601c02c1103c114030540025480e240070303010250500d201c0d902d500308960b20a03601210030705414182c1c3c0100d4101908e40740d1440711044c600404a181513 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 999146969 1250 999145719 999145733
    0x901020a0213093002010615030905122b09020a06141b1c140702090402210c010815010e061605011b0e1009180e0f0a11060403 56
    0x8214020700c18050701a1200b841c40003684550001e540220131824800c4000305070307100ca04500b20554814042d8403070100e0040b4014000c1c503089500b040f02040328510503c2c400c0b401082200c0c0101d88034021010400f9120f1005406800d45000e2400d09140510781060111040c00e001c0c040180c016041a9101e009a505e403c1c0000841e0020309122411071500022107241e403041d9659410f64500344100c106d00320800080316440541e0886411000311081901a03402c103128400e00e0703040c11000c02851005041400040f03412030f2011703001100d00700d2071324008208208204c0c03003803000e64480000000b9569200d011a5008030a9802401d508144030340003d090f500d070000601d002d090f000609965184409082907483c5400000801032651a2140780b400d03030400d207040070000b0b1058098581589440c01055100c80029102c108501e4503000107803844d0a8108030409445075070b81c071002e01460341480303200200030250300070700b8480e011072901c600c0210300d81561600968003884140001032a1b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 999148219 1250 999146969 999146983
    0x414060a27080304091505010c1a0705090d03030e06090c0f040e030c030706090507060e09160e03030f030a0b04060b0301090b041b170a0c0207051c0609050619050c0304140a1b0e010803090102 84
    0xb1010001c2042d80e0bc01405540710300c40c85078410342048407648044189131f0315074000481c040000050390501d440300c6000c6550361040c005000e03072243d461940c003038880c641a0701207804510740005690070071440c407041ca070940d0000c01c801d450310f40d158824101042001c1c0003034809001d007414072221400800003c1400e05e540244a040c0c60400900201c0500d4021030b2422100100202101d990304048443c1c8006600f00f904c411801a00b459a19031840c80e09004000c255030b103240080342943e20b1301c00c0342400342c12080d4906401c075903504800c403260300c642c1080c504034440e25111012103417282c010104407094003c040040aa28060800d0701441e0302017840c0c021030308204e81e40511800c4690090b050f020b0703e244020882da2801c0a82803c001003c5031092258a40380d10511482003260581c0c0180d42c0c04940c1041048001c000080000c0c0b03103981c801c0702c4a400b810865a03129565581d0300c6840041c1c19106a1100d051401081500c10019041e4054409240514100400300b00040d40d0303080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 999149469 1250 999148219 999148253
    0x1060605030604232e060219030327120201050f18030418331a07050d020f160509040f051507050414060a27080304091505010c 56
    0x780301c1342410854280c2200a40301050003100585030350030103e905000104100e100042c2d500740c002100c5210007042c42c5404100c91460b0040c044c080b110b00341c1c05132044020101181415a910081500c204030160f024040d0410a05c10f45403100090410444044958a02c1011a0704040400c40c5c100e4401c421a500b040c0d6003041e080c08003800b491103130300350300076500b0007401210131001c50400725106030041c4008025084541a00c803407411580401021452201c4854440020081106444542015142010308108241000170ba03696041c145079142c042040140d05c15203400c02c1c1c145043c00142002010403d0702122507190001092140350010000340060149030b4204080c0b1101b801008940018002c001c10a403500c000094100c0e00036010b90000703d01a00c44580040c10000203d83c80300c1c00d981c039070802e00c03902070351a5901010180300c1311906c00c0030aa00080c0c0c0d0b1034100040d0029061402001c62150240880300f42140d2882d440203041154500c400b0000c0f48120301906840c071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 999150719 1250 999149469 999149471
    0x60703090e0c0f030c030a110708040312110f0c03070501030b0f090615121b0325030216050c120c180a20070204110a1b060906090b04120201060605030604 68
    0x42d40d4554806540e00802d42c251110300c01c00800c000049100c02d000f1840b503a00c1480400c4844400c040110f041e0103044801800b85408000038000300d8140005408074540381c1c50620b05034210350100b1400c00a01b01782c9000d259202901d03010003443c0610511010304028030742080304a5001c8005058000d24032401b0f40901101c2c070104203207494a070805950b213600798803c540d030341d0002c21102042040803268a00380315a407180c4202111409405c4a01030056030424529500c012081070724002d84455001d010316a080201c2030300d01441450520aca6030040c070150044000c0388080c0070442c1e105d420341d05941d03040320342c2c03109032680c81d0b941189002858100c80c0c002991034001070001001101c40e01103440400684004070300e150400104112071096900b401041003402d4816480c0c021904020080f500508900c1e032a00c21f5000a252024020700c40800d41d220039480300d07000ca901c3c2d131800703640b461b003280d00704014071000060000580300d091008114041c50310703000074414080504001c0c0303d6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 999151969 1250 999150719 999150721
    0xf060a11031b061510121a091006090b094902041503021c032d1403070e09060607140102130509010e010b220b0d0506060703090e 57
    0x800d50410940b102c0145040e5a2030950340e01c4100d95541d03440880380c1040040c2100c52420403403c060000142440c9a925052180c400d1820500050447d2400c0d480468255a01c107000558680f100580501e45501124851500380000140761511503044800c510404018019590701c65125040c11201e0b4012070b560002d000c05010503000c000c0900c4009401c03000e40c102c0004102301120b45552500c2180c0c20070410701c03a86401c0f1007484040c48040c1d40300c0344110280c080c0b0310108010801e0980b03e0314002c410752505d440d58588194411941c4120340214202610305a40c20404075401080601da0407411841c00b40c900905500c1c1c80d80d070481c09250070801107001600c074002914001607221139162502020304009500039040291010001e020001000520342008034545040c3d17031100600380020381c20a59560115802640410032002201000203168111018950058000100703c00e99968500c81100c0a071000074241b40e205c0c0b0402c0240100094104e500c0d041200c445100c42d94036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 999153219 1250 999151969 999151997
    0x40602180a0308033112030c030504050c040e0102070f0f03020c0a0b0d02070807060f0c12090206030a0c02160b0a0210020a0206070c0501180605060a0906081020040602010903030b0f060a 82
    0xd10020b10984d500c5c1100411182c808101e0b0303e041011a428140d50708100800300400c0c210107848040d43d024140e90841500d00011b802d05400c1401c0a100000015242203040d0390b43c00088042400240c07007a46e134806070750042641c184409014040200c1c0d16520341c504202c50b4181520407080d0b0240d070140d00007a03071000c01c03001005039540917410400411040002c0c0b603021014210360031100d000034100007402c2d8102403640c4a920402900a00103a0942e170b1000310420041001160311000e40c4034069403c0b00034044151020040c115000a035515950780401c007900d45502c05001482290051042e098402c0d800252203522810034642000c0043c101d0408600400401228184c280442190881406480d4024500401054951002456480c2540402c03a045400362154079006034178044401412030700208807000e48001c1c400d42c040c403031000d00d00e0190700c40d5100c40007607511078607088241a0036100301041d40d002500e04c2d1a0140c9114005102486140403483c20700001301402c6103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 999154469 1250 999153219 999153271
    0x90108031c0e0715030f0e011a0f0402040e0c041a0a1d120f0703020307050d11060c0114040f05010b0d03080a0e0c04020408160b0901050418090b040602180a030803 72
    0x1c0c00c108903018904104c9080080c050581c106419500a007450504210101c05101d1a01c1c1c081d0344101c3d80c800b0a10301c10400c00b42841c09104145e001f40c00380030114120395544540d500030301c1484005580c40340340003c50842c100c1241000d400404003880b5556615810014801d0241d84919041580f805100001070340482140b8016015110301c82c20900d058000150300702c00e0380c1c000c03000c03035400580d20010012136488003800201b94694420510515040500240843c4a070000001c0741c01c00784e80441c004000000ca80691b1300200c80d400e40303018400203101c1d15401d280c0c01c2d1030701d049041260724040d180d035201030640d04003c3e0743c8105415400105124051001c50020801e540c0d0315544c40f003099031160320100c0105002001400001c0e54010801210703069030060712003504140c9002942c0c03480459050142c2c0c0225103610f00316000a1a0030b4440b44114820100140c0f0b60741c214600d0303090b4018203c41a401884812014804a0369480a5070f074003101c02d442519801882688840d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 999155719 1250 999154469 999154483
    0x1050901110607020106082112040c0b0a091d15060c01200a03060e0709141203071419020d1211070f03031e1b0c0f0b040302090108031c0e 61
    0x19081e80980401d1041c0d8541c10740000085074a05001c40c1c505550710007002c80c04100a919200d50110100708080581d088400c0f100c2d0700c54002c0301e61b20441c554400264006a12482840000815201c0148100124240402070141d25100751420301e150110b08100303032010035813a00d44201008500340c05034070007d4201c256014120182450010203013140c41d41d05802c0b0b405c4440100b4140b030004285442d0354a0040d100d40515902d60103003501d03008003946a00382e04040c00d6004008030590442090080000b8040c89206680c1041d040b940c044985040070351103820425140391054102026075914100c044650360000c1c81c10404004030070054810220a10301e00d103450045a1000544400b42c0ca0030700308a07402922480d080c1c0c1c41c001d4802d000d2041100d80d01d00410411840500d00c00a40c10102e1003440c400e241d4180066224101c0885c50500c96109284400c0001000c1c003c5003401814540100780860065080c443c000540001d0585800708240c01a81d076883e040c250a1800c03c096 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 999156969 1250 999155719 999155747
    0xe0103110405090f28230f040803040309090507020303040201020f011a04110412030f0906090b0f0a0e0913021203161509062c0a030906030c11010221010b0702060901050901 76
    0x488020795088450103840040c0441750b0281c803154111b00c03c40c0ea00b1000c184100d41202d0440c003180c0ea123588100154001030815800c000c6814000300b071005040c0b051500802043e0001c5889141600c0028500542180312003000d9051416040404903800b058060b101c00c04c03a4042800404003070811060f008507030243c00c0009506041c0d106141d04280c0001c0c200405590710040142c6070041650040b0080c8904400e00008100807801611030320042d080c00c01644ca03010040c5070703500700051143c00701583e0000c00200d1000025003145868864408400c5200010314240507440441c00c459103494100581a10540e0408801d106072030b0b8001001564010010030214002d010b86510081841804088004a4004264001000040d10304620394540e40784540c3c0c904240d4120098440c45100c0002c0c1328000c0000c003164802800a00030300300d035461030054040c100040c008141401079102d065030170010040c05000d602c8031021200c5180d020b0910b150b03551070880049580c04c20803078407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 999158219 1250 999156969 999157021
    0x112110a12031103041410050c0a0b063a022b0c120b0412021221010522020304020a0e28020a0203030f0c070206030103030e0103110405090f 62
    0x3000c1200c11000c031601040364000c0c3d0700c00b1180d101c00a43c1565078403d5016000300140c107021003410b18602895028840841c3c1d00d4400e05101c00460214503011107814101e070b9550380c0001308000c60501ca8410703c1210080c601c1441c03540c0c0c0040f40460748146600040700b640d0054a862015502c4035500e03900e10f40704003c021034104c00c410b1030144c860131841204460844202c1c02c00245803503144000d5260b00c1d040044000350b038035a581c80c04441c00044030414254001e1440070b0381500e180343c000e01501c051103060103058440c8100c01c0342d034030f04058110364031401d00c0740d4840030821108400e413203810400400040e41d0b91540d000141881c0226808105601004000c020b141c900c40c7e8080b100744a0700c100078030111420b0030080d20680c00382c803a0000040c0d00600004660100c0c0e40c0c900c0d03410010500344103103030041d2a0007140066100340c05c00c2e00401c0d480745100d130547d44c2c18840c50303900034180c520b50f600741070030100000e41c3c0040183c4942088502403020810b41e03400303110005010200c0100e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 999159469 1250 999158219 999158239
    0xe0f0123030105100504050f01080603100e03130608070801030609080f04080f0f19060f140f010e07020a0f0b090f0f0c030601230105070539040c08011211 68
    0x10410207510034020103008180d100411031007680034a05a0302036650080402c2408a41c90004403510078005100a6051080c1c0500a4851400c3d1080c0801c07003010402541c1e80703001144641101c00000d52044040001c3c1004212450764812907080c1940e51114000c10b40c41201d00b8012002d00440443c402c940e200000d00143c0c00800003000c0020194a2040d9a0003181400115464440c50307580a05410841c0a49000040d50b030385c0034a284025403100001c000b14080c401b07400c0410b0884501d400d01030004014440d0100b03044090f07034010039a01c01850140000d546039503099881600090042000074080b84030359034244244828062000102d0f6040d40107201d9156664901c894294007e00500001180e0310603104000301c41c400c400e01c4560050050000112126800301d82c058415000e10f8402003109000751203582c004140c0d046242c010100100f1016200c10021000584198904141800015080704031507046885000d941d40a1030924100000108441400140c2c4055401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 999160719 1250 999159469 999159527
    0x903030112030c0210210e06071107030b0703050603060f010819030309050a030315080c1f090b04080a1401020306030a120903080c0d080718090207030909290301020405010e0f01 78
    0x1500c06c50242a400e030f0140c0300d504000d00c5200c1101c100e40381d1800303c0e800010008036801e000d02c0c4200301c004181e0080fa46200e580340c9036849082401e03120300c40000d440390306019440c5010080f8a401c003481fa04000d0381c5500d0049000d03620441280303004105a000304040e02414002d5210702c0d001e40d04481641d800d4030451800800811441d0356642a0b964503840102c1d5400c00040c41280d10640545450b401000201040c40d910000c03203066410442d850001003503406204002e800145030440003080110194981400392044500c0300d0500340c0c2c414020012070b0b0342c00042c84208680c101180c1d0449000c07014044402d041d090300013a01e04480000c07062054240001c030100c140802d43da40e61040e845051040361008048a041c0414103001c140c04d100ca41226401451003d00c01d04101d06400ea40b0071007502510380c001c04124540d00c0e0340c107944040c1c50b500702030a143e25004038001c618003400d100029040300051000c140c01600c8050104c1101d034001c140140b5034168060f01203403040458 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 999161969 1250 999160719 999160727
    0x303130302010501090c05040b070c121104060e040f0f0305090d03050c160302010503220f0807050105011a071e0c080601061107150c03030615260903030112030c0210 73
    0x29150490056180000019080f40244224141e031200c030799400b0b103018900240440c09030001c40c000e541c0d2024901d400034a00e4000300f5040e96241c03060060b80c030a101c05204010840d6400c0d4001092640e081c0c0030007001900074144600020303403080d04c14175011007a00781158a40180070b43e80d50041004113460080c90307006000b0700308a88072031085030030141494601c8800b01e046484000e0110703d003807000c1081c2c6a560440e00f2034440c0c200264024032102e0f9100e98903d0000540184d0340003070300180c131030180102070081a000d0708825501003002020a41801540e2041480140049600320300d010403034503071403540c00c5405401c000790112f0700384c031012581c3e2222000c0c46000003045c1180002d00c0170b01c0022074240d0455103070802020008181d9802960404006c01d021810141d40b074030003003001e040000001441c0c2400340c1e680740714100b01c201c004400004560540c080900b07810104211303200008210707070548101001080180806113400e5802404c1820300a41c004081c1070b040602d1640 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 999163219 1250 999161969 999162001
    0x4180e03220504090b191e06090c090f1505160606081b130b030307021e0109050f150715050a0c12151509180606031b0806041d0303 58
    0x101c074070252038540c0c0c0c440400c4100e41c51820f0050031001c040700011ba42425804080320340c10708015010540d0ba484101e50306001101b1203980c01d445644a00500c611b858a01c1100e42412040c14a648407504000000c007508801c0e10404c10700d45903090041ca01d2600c2801651a002e4061022600300c41c82440c151014282601643c141c1d0312880d42c40011a10705044071244210700a08000c0e003032500c001500b400391501c0d000154040c070081091100503202d00c0703048800d20a14141c0c0980700c80f00d00c40014030401e9164807491142c0b00410310303c039440d03880d0b83e180724442c007902e42c045941b20707130b1454444c00c4402c2082155402c24030304001c00003040a2a0040a2500455900c462100040c0300c80c0104460103c034202c01e4401c01944280000714910f42d0084407a80203040010885a4076000381d0201c640d20074030b10f4401519080c3c00c000a50b0075001c0c1100c00e100000710b00c81c1c080c45c981c00007400ca5800a0420344515100c29140c01c0320041200e42c034101030401c81c03c0c3d0395603107440c8031080f0714902 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 999164469 1250 999163219 999163267
    0x902070c05040506010507080708070c030212010b0907050c070e070309021816050309060604110c2a010c03081315050403020313081c0509180405160608060604180e03 73
    0x200f440700013899036109104a03502c0540c421803640c10b1020b107842e60b1a403504016400c030340c0c140d0a14008405a952460203d203a13038403c0c0c00104041c4504014410b240704050500003c2c0034062141000303000700420080196030244403482e20f9581d0b642c0003140076050010300690801600c030100d094203441078016611915038010001c8600350303141c800b21000d200455900f54603400001c0800c0d580c1c0743c6a080030700017003150081d06003046143c401c0729040c00388001c44410040c000d40c00030042ca0003c001480704105003400c04c511030341c4680d2806006800010701a4107501a4200300c2070801000d10203080c43c03e85160000c01c090700d4645000795581d40074500140c07201412500c0000c910000041c2540040340c1c041d144061001060001d131600d8110204a552142c44840104509120011203601c03803070143c0001c1694078170500d01400740d00650741044007000a650100002500c0b81000c0b64100d03005101c0310804c1030a8240e46400502c1400b800100c1400001030b00549080282c0d0f071440041c2d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 999165719 1250 999164469 999164471
    0x118080c071203141c0e03040512010c051b0307050709020d0e0a030905150c011a01080705090109050114211008010b030d0806060c03160c080a2301060902070c0504 72
    0x1500d4001c1c2421410154100400096008468107079040b600005440c5c607040c40030784e5404044400342c400b0309071080ca03100d400c0381307070700100d41003126290100160303c13284a103200801c07114071180c0300241a417141c0c0e95513250320180c202421258904c20000c460115030454181d50043e901d03005640c020303521620f0100c004504240003c510090301051001c8041d9050700c2d603495141c41c100902941d000c081c1614108040d0502c110280f41c2003c0c018200000c00040c941d400c0c038001900090490b600140800b41002803e0103100340c640d0304806401c0542d0002d003000e02c0c0d16a110391030500288243c1c80d0301c0e41d803104800310014031030000c800402e00417401041c41003c0203807210320642c01c9a00b000e50303050741580046d03407a41304e00b4001c042e00e681061002c0e00300c0e460500500401c40c51a0720040160713842900d041c0710141807040070360500000e800110041d110f40201e5449900010707150510700240201c001e240c881001109600200c0184040301042d074860516040500e031111181c4241d600079 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 999166969 1250 999165719 999165733
    0x5010906050111210f0f070303050106090b041413020a090501020717071e0e102408040611370e1f0c0f0f020f060408030a0509030118080c 61
    0x20b580030300c4102c520729000d54003d080345800b07000d01040c060040003c1e02d89640c010002c0f03034846a2410003c04a24124148a0b42d56200c0d5290040403560164084c0003009403802040c000c0d80050b408a5040b1340084000541190784034000a42d81c402c02940240d10301c1c40011461001d6411034840000c4420907000d59400c1a52070b000c3d0101200100340c2d9800b2608542400e0054809101900643c000c1c0305040c11a469112000c210300388809950348915508040302c00c018403c0007520413408440f040380c0c1c12500401003100a030000034090401403802c0c2d101c070b0101201b941e110f0103403110300c0c4860300714400091000d0006001c0b40341c00400103010345440c03000c11400300c0c0a020b5958a1401c0a40306105503006402c00341001050340c40000b042240030100a00411201100000303900d000d10203183e503200052040003c1020000a441d0044c0010310041042c0c030b0740442130350700c001e0f200e0801554032210600081d005190074807051100d034600503210030600c1044806025144100b008a56407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 999168219 1250 999166969 999166979
    0x501050f1501090e19060e0a18030507021003090209010f0603050f0f010e102303010b01090f05061b060c070c090510060507031806050d1a0f100903140105010906 71
    0x1061011032202d020030b003d040100107022400309516802001d58151044902288084506442090303104c028030781608024480010305030301c14405072080d25802041c1e0f00c6550358002e4658020454041d1140e440213000f0044503009404c6080c40e50380c01828295150b031102c0d9505140c1102d801103600013803070f03c40040ca08060344801c05001d911003048048040c0e2800000b800c80c524004d10107040c0207240100001d03854082c446144088116110707420661603040c0625085410341d40c2414100f101d220801c10800d1060040c1c0815181d0a0700d4080e642c00e100000028011940341200f00c0ca4482c210801555000c81006410417920485ca02050640c0e580c85480c160780e01030ba000c4040c0001c01c4000c0043c2c5000700000c001891181c05d0026941d0729201d40c0000e038146a6002c1004141d002400499030002c6204400303200301c20710284401d03600140003007804030780d1103003842c0d0103290300c0340c00d041c0b03400d004a221000550b07001c0d54132800841400c5000c0d001c1c00c800e00c69001c41030308180c00810 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 999169469 1250 999168219 999168241
    0xb1918260c0a0204110c01050702011409030a120f09140d0915090509070e4b120703330b0108061e060a030608060c07170c010f02070501050f 62
    0xc900750014014890600140c08100040012a841c4800000204040e046542d4203000d080c0c420340c44c5400005480030003200f0200408001025030020b07810070044501c0c21a044202c0804001d95000005454100c5405880082403032110180c0840b019900c20f610f04040003c46224100159072040b280702e07030703138042819081100c15840f000310701c414105214604011501c503a1203080b500d00300c410f40424001052554101d04071502c3c03c042c440f1264032600744614203041150584070043c148920310002d0b500900c8d81204121b0f032144003036140030211040b0400840b4080e58010015508102d1611205001c0c2c0401c2c184200840d206030f41b43c1110f0b064944030b160309111045c0c54464043e039402c1c04010b80c80381034807000c00c6030703913003501358014951a140701034903028a143d00c00040075130814004507d002c04c020a040c800c40c00070001c1d0350002d401c03141d400303e030a42e6158466032154005600c071809040002100100344e4800700c0e03034400f4004150041400345a854600324259218522251 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 999170719 1250 999169469 999169477
    0x309040914070b0909070f050409061401030b100c150609060b030709050f010c030c020d080a051c09080723030f07060b0301060f0b0f091216080a0b191826 68
    0x15407100c828400686e0981c011000005a2003491800d680380ca07850380f0404c012a00603402c182c81d1121451040e44d0156010300c00d9106032101103c45003250400285c005142e1001031400800d00080d141c505d00b1010324075040700c40608400c680034031180b91915190075280c1c204491038130015484020004c1c0e141089440b06800070f50684d01c1c299280031546080d034102803814812038220004590800c080381c00a0044c1a0300d07002a070300e4030f588020302c92102040086584203140d26a18014032080081e003894116100c9503840440c0f00c6099402e41d0202806110740c100c001040d000c00140010050021001000d940c0c0c03040200f007042c20032400905003222250302840084c0310304403c040c08641188005040d00c024800981460b020140010515822680840c503c0d6907006450100b580c0d000c0440e01d0024004450081410a0a540358003d1192020b810000e11148101b50b0320700441690b00500c542c400d01c032150308080e00e00b500d041e0840103002400c0b85900041c1201d087e522000031403c035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 999171969 1250 999170719 999170737
    0x2c0f0402031e0303010509090f070303090f1409061215041110050901021e0106030f1505240d020a0806270102040b040506160f110103060b0c0d0c03020309040914070b 73
    0x21130640c4c1c240414050f00001c041e0281c6190b21814034500c0354080100a07001c0654403da88005250b071411032091403040c0c103604610599503020108090382d4807180101c5601c484121040103840d011344030000e0070310b20894000e9008524000400042c05200580444844820740d0900502a400c00f0100d44034040d030021076006130018071903802c0344102c81c210b00121041d00c50001030040da0b241d07288260280101401c03600c0041c1002c000003458224400c0760741c8050600354003094264514905901d440009600301e10400f00d0311290301c01c0d500c90001d00005800540219030351070510545444240605010000d00b4a0080d80c45101144c8107000b950704617000a0100350a19042604001040e0030460304404154080c0f803424000c2441c100b21400c42c14040c9070260030003c1090001002d85055400480800008201607003801500140900c03c1418524240f940440540340407815031150648496100d414081d02605000003a80740402441d200e0048844c1c059131640100b1213405081c20b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 999173219 1250 999171969 999171973
    0xb19060e01030c1d01140a0c02190807031b0b070b0f1f0501120e0601060f02010e06060105030f060a0911040e06030d0f050c0304091103010504150f2c0f0402031e 71
    0x118507040202c0f0622000b01c18141041041075001150030380464120302c2e030150000c8e5107881600c082d4100740701d8488506c41c00742c1406099508041101e03503038070014031005001108145003440480d201c0081c0802070081c2c0c0580941d11105810241001e0406070703862103a6600b10404206400d406050750310103d0402c1c440344c00748629150064902e03e40c056030022005c4c0d11002c0680d03d0003018041d0340c2c06041e4a0f00c4803e0a8101b0810007400c5030205201d00055500100501c809070b0382050940b9800f0035a0b21034440305644440100b40200c515620101a090410103041180700e0018094415110760243c031224542d2800109555000c40d84064004a00d4590054491510480c0140022503845d030840e072400c7d40d40d00c2008104e0340000c1c103043d58a00c0100c01801070f46018000c41100c0303010408082c03801410300701c50642e009003d01c1480318500d050301ea060102410300740d426a00013807503181d03c1103d00e8111040d00400c4001c480c00c07807080c003821000154030005510004000810900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 999174469 1250 999173219 999173237
    0xd0b13050103050d0c080d0e1509060c030a0218090c0d0e07051302130f1215022106010e09040807050105130c0504151e0e012c0a0b19060e01030c 64
    0x1405407100c440480c2d01b91107036902040200760500c1d89001b403004681800c8028004080c090504a040300e002030103110031b540140c81800002030b007420507a40c0103405074500503900d4442080380418140d00a140c035030082c3c0403904200b88040840702808101e001504107100d2401100b00090f02c440380c0b40551580021074400441145074503138060007503031007210310446030b00d40c60344250b0200225962080c0106071105040c24100120b0f0f440c01602650800ca040d801c02c040c0c403c1c07105024140381d01d48284650100d0001e0103e03032003483b05082103c80030742180f0080c20b00781840c10750386d4002203041d6055800d0801180c0311140c4440e81c03c205c02c1d003041007590405d05001c2040060070f00d00c1084600000e20450205100e0607100440806c3c00140192118191401134030410008050344105d2200000d5604564000300b0005c00440d20f46264003c03c0050791401016002071482a500b542c1100c04100342030543c01c050801c01c82a00c4aa0300c8070040c048241d801101030366800070443c0002a1015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 999175719 1250 999174469 999174493
    0x50f0a020901030602070618060209030c04060b0a030507090b18030616050708070302070306020a1701050f0105041403030c011122030f02130e101e02030403170403090b0d0b1305010305 81
    0xd40901001b51049502142464041e080d650b03a64003040d60030b603013241d400501d8a025140c01c010201d003408007a034040c130000b803420086000500481480c0cc1c203040d12900011070081c841c60b841c0000e00b20542c04076840e602e010900049005002007054020300c21200030604a5207044800981742c2b2256854510b001d1603550313009000d4200220032025440380523408000202580080c0041e50388543e03400c82e2200010310290b6030342806a00450140d040200d0321602c59a00c0022507090b9010650302407051400381e40464030310321070619003000da54a004101c0c0d01d8064204014400301004271880e940103164034059107462b0300d00c1c0c480145a00368190703049005040c495954884100c03565800641c87d0a5101c101d0f00304560015910902540e645401c1101d0002a00d002204c084000c421811480c0a990203003a48049665130402180d400c00000e0416100700b0b10301e0054025400300c281c48614400f81b403c040e2081c1c00c4403610500e0785881240b040004d0b40309282c1220380010082440704144 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 999176969 1250 999175719 999175721
    0xa0b092a0c03070323040e0405010c0e10030e0c060f07030f0815220509030a020717060114150c0304050a211704030204060e0f10060e150c010c020a050f0a0209010306 73
    0x114441581710a4040c01c10390840034650045c00c0102610319910290b450180380142c01c4450400c1804203000c0500d41d00141c80d00e8440042c0d0381c400c26820000f41e0542e60320920707498034041012880e4805c10000d0409100400d100290034042d00c40d48a011101020308403c0d5a0848220780ea8079014a6111200c011460301e032002d4440002a58000c0800a02c400394590984500300c90000c1298000201b02c1c110550403c41c5000600740c0050813400d4244026015455040600c200180009440034103482a543d107403180c884203a00d5114207580d50041c3c403c050f200c2d00a849628810b43c02c1200005181080450280310708040f010625041c03841c950711b144202070200b941d50031440d0144004030060300c6a200b0000a0161410103014516114040e034119800007062103041303403a0080c0130010b441c5c04c414440e03410b650444150304401101100d510031806006a0070b00c40d90300344000b400303880ea000700301420158081e6065805030042c00c4201c942c1c1d50042d08009401c12000c5c3e00404c0840d0003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 999178219 1250 999176969 999176987
    0xc0807060b0301052a0702130908040b0705060106030c0903080a210e150604060e0403030c030f0f0507170705160809120736050a0b092a0c030703 64
    0x2003040001600d25100d804203085840455410a24181c0b2034092019101c812a12142d4210382510081c64036115501046a08102040c0b04107269141e00244080214031000e84000d44004010107071108000c0c103040f40d030b8080038403424000c41d06d095810381c00c60303115488190030b89401c51141c03072034600505401c0750701e854100320f1149071950900e40381e0600d0703095004600303980001400611711001c1c0c1611407080080b0140c807041c0b11307d1414408200c25002e0a0000d50301640608000480010410051b070240103403844080d0100d00d068a42840303981c082c2c3c0020702030552581c620a4070840b0540e000c000910540da8500480d0b803e0002c4900b48d824200c020440074840c0d4940c030709148030803011902d01400440e11a078550442c20061007011b500314480e80001254821031281e491200ea010768004c1c0c0d06900010b5031035101c40014070304c040300f604500500c100150107a4100d00e000f07580c7c4503c07682401c40303048030a110000503882000f204e0301a0303080041c2480c0690f140641d5940c05680c1850 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 999179469 1250 999178219 999178223
    0xc1204030e130212061e12030f03100602251a040305070b0a111501050d020d020a0e01090f02040521070306110405151806091c0501020a0813030c0807 66
    0x44154050703065182d0341e20103004282c0240015880e9003140a5000e9598001403115029807120030280b07030f201e004c54041030034081050711a01800710b0300d00942815841103a2003c242840000306102c0c404d10383c2e1441900312020f035800e5070381c400d0207030310845504070728540000004040040305000154050b40002c2d00e0007101c1500a04c0d299595a40a050202c65400700000000200702c28502c1074001030200d000c002c0f1031002d00080800c94036402c3c3c40320410b00646000711803041c044411900e44a107020151600140580e100998442035031032080b00034010340e090182401136401d81114030340299020b0b5800104402030050f0302903424000850510307100c1140d8803c3d142c0000102d41c96104034940800c903804611394840c140030a001524000c92603041024004102a0701e462016804441d21624100c4240750788050504c000385000c0139416000d090303001000c81301020000158010300088403a6155406140c0d80c550100d0240c04036903030040d010810740b00547c40010340d401d0061085078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 999180719 1250 999179469 999179477
    0x513051302060c01022506060f120b0703111c0b060f0708030408130314061b0d20040801091106090310021606061805150604180e01090c17060c120403 66
    0x303a06058042903070242d08000340d10b100360621b0600030300040d0302860300606280e9006041151031f0030a80c5145086294000e401c140c03640c004180344610130f400100c01a40d00d00780c2c041d1603580c100c0d41c868034119100f564007041480c3c0000c020792400d1004c1a50b05040c040042c59042c0300c1181c4404035950303c0100126461882000400790303015240900c4409103000e04c90120150040e00101840c2039000751041031400c0d009107400c41c3d1005035400700d9141022040010541034031088107103401140f840e000700c09401e404500840c0d0980c0551000d42018040c00c00341510b0142102400000c0c1b140340e0b10250113400c45950b0640742099500280b2040139240422460000380d61101d50845a50350031048018580158580b00309200c0d019040c0c001441541110341c1d28040000a00544070f1441600381200b120b819402c0010165440348030100c5840f0024001c40d07481d45000103c4941c00e0007520017030300d5210385003480c100e400941c46204072581203890745401c40c074046860f4101d1008100b02c0400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 999181969 1250 999180719 999180727
    0x20108150603130c0603020f0421060c0e031002120606180303040e01050102060603010e0d1809020309030a0f030606020607120b2d030105150411040803130513051302060c0102 77
    0x5444031801544501c565809208100e021440c00611340c0e08039a1040781094018008009408190012902110788a800302c0c00c4e50010071154507200d03404036002500ca03902d44150780da0a580c015449410b81e0b08101d080d030780b10020112040040b40900c00400e0b680c00041030015a41d820160020305050f4a10710032421000d03034120005c0d08d541e103d5000580d0001610300104040e58041003090b03002181240217000c1031910102d85070756004213503501d83c100103108000c7c001c54000e264410000e001400701c1990789107000582d0355641e41c42500107400242c0300d6030700580c80340d109105001c1599800d5005d80280d40b550402141d0a0031410200c807801030342c8080200040d075540241000311840b0307551748450002d544a1803100d50561120341402a410103041182001d0464200756040c07100310342c002061950b0310710010541c0220f0f00302c070344184000100e00f4240200201c1e01001c1324002c41e090f0038409010010300c0b041d5032007980c0b503404082c5c030400742c40010f1600d03001070801045c01400041c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 999183219 1250 999181969 999182011
    0x30b030f01061d0106230f130f08150103050601050d02061c0c120b09040624060801050a140906100201020904020403060f320403030908031e0a0b010c020108 69
    0x84956075803042201200020940701c0c550740442000d801044203081c102c5081901540070200702107009805940402c0000303510001c0f0341f003d02034490018403800c00701c80c01c81d104d141400c0d0160550081488509c503854003001c210110016940c1a80d0b4404c0240ca416440c080900170700d07510558049074425820f00c038002040810030400f00030071814420120f54107044d02c001414510410180500c0141001c0c0300114684500c9901500300707511030b000268400800079110034414090f0f041448100c1404030010700301e41d03c414003a06a40003103550441c0203590718a100d041e04844040142c100e0203c2c0c002500d10b2616020490700140c403030001500e00a2000c001a04990003a00100c811036074481d8003444d2400b07148520070700d5504499800d1a00d0714005000840104000c9018401811000001e410544650400320a4a6001c03082545078244100c01a1a08020002d0a03107140c1260300046c2a03603405018038a030546042e10303071241e08860358004403240000200307d081504010403003d4a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 999184469 1250 999183219 999183221
    0x304062d090c0e04030302031807080c130b040603031205060a050d0803071701090e0c1203040e220312140403050904020a020c06160201170f1302030a051203092b030b030f01 76
    0x2104d0b030720940e40165289007010302e00c501541005140c5c801544408005d0103017220004441c0f012043c00c403440e54030032050384d8130700c0040c10001c007640b03801508014000042581041405540114030041030226694180a002034034030944101948200c944000e1804200090019034005c0850f1903d0001c03440500c003803005400013a03004801199a402542d4200c03142440340b4044a0030440380110603101ca801e8295580c011401008801016100814607034110315400200b1003200304d05c107246c41d146500b400350000501070403900c401404c0c2070312120300815100b462031080ea81611a50b00700880e50b401d0000070b4028a03210010b51180c00c01504065807080c010b00491080c4c00101005044c0030310005054001046110001020f144207201842100990060384000002c0c22061200c406000280c0381441c1024003030614011650390305486003140005501c03a86030f01042f100a5220080422012a00802c00084490320050b022880603c03a400075401660018121904500840c0001e8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 999185719 1250 999184469 999184471
    0xc14060c0105090f15010e0705160606080312130203100b0f0301091b0e0c030601121815050c0405030a1b1a030709171b0301020f0f0304062d090c0e 65
    0xb002c40d480700400d080f05460400100d110300342d485c074117100a5450421909520304003d41b482083c0700012610104c003041d045491a00e0903080001400520342d1825141d480754071154244c0d00c001c900000007116280e51100c82c406660b4058024100c80c0c03600c841803802071421118041d4080b01110089035035680074001d0400c050b02456056000d103607a40002c9030411002c3d8851a170308410714080090707103900c0c80140c0ba0300c12401c4c2007482d95500c11810b81d0001300502e509801a072448000b0302014000611004080074154140c100244e88601030110241e001b18481e141d49a8000c3c008000000d900c001043c085038011044a40760300e448082040410880b0060100c0d1900007104219007075502c41d07902e200800c110a601420004140601034540c1841440503103100c8144070251159102581143d2500f645511042d8a80c880320071800740300e610559054030b5847c10a1042103184030821180b41c5085022140760303502e02d42d09924031024101448090703070500c0d035017200042d41d25002c01c403032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 999186969 1250 999185719 999185731
    0x1b0f031b05010f2304030c06110a11010608010e030d150f03030507060b0f0a05040e0c0915010e040c051e0720010f0807120e030913091e0c14060c0105 66
    0xb003081540c55408a0131110740d690b12000008a07a4404031002041422150700560507240c10030042c4801c0c00e220010f08401860729503006030000f810402641d02000c0d54003070044c00390003886842c0e41d40c507100b420381d034100100321140d401c10000003140501680c400c81750707080d8880a0300582651038941c00b510740400e5009401041001945604120340d82c442c115082c20212104040c2d060800e01140521095014035270080e6600e5130178412400c070410680081c200014904001c40c80c0082648002d410f4406065002c51819211000549418090319900b502640d4425003058540380ca0231000403540841008202c40070401c140104804240211451015007140c40c102909100014102c0e816004034504025603071082c841c0c41a07115100700700c080900e13103000c26140214400b050940c41030241e40303503200024a0f00003d0000c1c1c2904101c18031402004c1e5243d181c1440304800c07508000c1844010134421040b81b09001515100d075100b0311040c03020f04840d04007125280c030b0b2801c442040d01c42d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 999188219 1250 999186969 999186971
    0x90d05010509210403030f0806031c021e030c03090f13050408070b0f0601021b010e0307180608031606020a030906020310080613020a05040b060c0307030503070f1b0f031b0501 77
    0x206200403e4841d580c03881d00c001c480a09240c42c0c60740d10003c0002c0d0702e01c02c40408014224020a03056075040002d1402042e048815a10355903007903c020755180802078010a0101c00d101e280402d190010041d1802d0040480127145442ea1010400c1040d0078054540c550060311007a01d08034210340340c0f00d101c0c41184141d0525681c0c51240c14405c00f4110014200c800c440703108030410419036400724084401c606840407580c030118001005803540c0214144940c3c0500c6810400501e2190a01007040c01600c0000100241603d802c00d00f0346a108202c030008071641400792110000d40340fa4010000f07507903145800943d0b10090b58540d426a40705548508603010202e00601c5000014407030250002803090050908490642c041401070445106280c07007240e60304445038513611107008540c402c1d6003500030303290380701503d02c0c003d01180c00c10345544001a40d2103605000085c002c1e440107040721030703074001d21079004a6590380c04d00090044600304d0030000c0300511803c0c280110307101c07410414803601c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 999189469 1250 999188219 999188233
    0x2030603070e2412030c10065f011e090902180d080a02010b03030702061909050636090c03041b030b0118050c030c090d05010509 57
    0x400c05180c031000e9080841d581601009006402080c10404001079003026101052128428001019820803900001c400e02001440d0329110001140884040307082a400f08025034039010481c08041c07450741c15130b03100310201861100760346124480240b0000001d0488101324030070300d046452031200c07040109040780521140549036801ca40303664440c40122000c40e42c03024040034010002c500070f00c18525941c0c1c0c001900d0802d0b4207200104241041c000e04485100461450404000d500100b140c0005500e06034072001c40b1302d40401115074854005041c42d04200342100781c2640b00039101310340070a0088440c030005464440310003034a030300c4811134100550f010900e80c03076800340c468196002103413031442c5c090311880360350791701000e90026130045c0903981f25034642c58480e00510002c8200c1c048002c0e000000000c021550a68078180e9040071614400004240300e4641900c0084e50b0a28071410140b0001d0001d030020009010303603400060030700000000d141c4420f0b00719001a201c508690704110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 999190719 1250 999189469 999189481
    0x1e0f0302011a10050a120203131406011505180a06050316051617040f090516020303060108010306051009020c010b040507020a05030a030c0c14010c110106141216090203 74
    0x88a202c03000107400115080c901c120100044008200164890500002080c28410707141b00302401c25810082400456607410100e640320040620b0040403261050031080c05c81c0169004240141203c583c040100c442000041c0d050740c1541100e11010081c00d00b03a0036246650b51410a0b1000505d102d03104c4594904110044001c4502c1d44c050403024414208000301e1440500441920303203d0300010348282003040e210010b21a4130480e07200c0468810f401c01c01280c3d0620581c85503000f03491503031010200c00382c1c104083c0c1c0c40f0702088400d00d000c60b0b1010010404200c0c02c2d080554085403941c80a1012070b141e040ac042260807509818846079596908444541400c0c41042d4000f801d0b40000c10b803801c0719640b82507491182d03001c440c0400d6160183e1482060281002040c0030354001a200e03060300c00c100540b03000340342c4404100c001640384802c0b040c205406115a105a8110b41d1900040031818000e00215000c07400b08a0a144034405044041ca06c001c40f040001d401200710250b5207003490 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 999191969 1250 999190719 999190721
    0x20304060509014a01030b0108060d03090806010f0608100b071b1208031b03063a200a081005040212060f0103030f18051c0606090b010816090e041e0f030201 69
    0xc0c2005c0c14503203801d944180607a002105260312041c101d84240031f60542e0b29089520004660044095114160000c80da00e4482e52080c03007501d041da658840c1380c3d0749004245d03594440e9403196002c0036104110710000714920643c81c83d088030003100c0604241d642d41c106c44441d030074404d900f6150724001100b401400100b6040700309000c1c132841d49032800d6080107c002082d1380d10b0500c1f41c0f20300701410b40c00b140103a0380e2100d4511002c4800d41005444000a0030b0103100e881038940c12a1805490b0741941e1042d25050300c00300180c1e400d510082150214240752003004002c050016644455000600f01c1d900f03108202240c810b510010350300006514600e0003800f1161040b600c0800d01102446c0603070208500034110040f5401104d012400001e00b030004210a51004005448142031070302c0811801c2c1550404640c14200ba41c60b04025641d92407584038540000400340000f4284400421640c0030000184e40c009024102085c0003411a10001d080848500011541c8540804108080c1902 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 999193219 1250 999191969 999192107
    0x504060f1821020f030d082e090501260c120c06130617060906010f17070534020d0305040b04180f09051c020127050c0102030406050901 60
    0x2050f030003012006d2070000080d0200c400209a01d9204a4038560071581140140d5580800c2103039174000c002541c0c8901300740010701003d01580c02c18800303c02500030300c00d4042080c0d40c0d140b0551006000351007120010401880d0a02c0c60b003c0c45441341c1d402070005035030381a008080381c01203002c01f845403900e01032000c3c150500103201245154001030030010542c4031000500da01c10400d10341036001601324041510000c44944c200c8010b041d010341044038045d0400018200d4020720f030b03000e014032000e40482a440141c90000d0088140109505a00500b00080e20400041c86030405508007903c0b1040380c200f98200354000ea11000001c8080040e00c5210f10035409601180d002c02e00c0903852903100c959503611460810344554046440c1101450700c02c0d80003d101440c0d240c184190706900c0d40080d89203c0c85a08242e409004091440e012903000108840c110340c000e858480c2055174000040d14800c2c1001c600ba141c0a030b062415200b8042e601410082d03051030300c0c03880e0700c528140040a10078540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 999194469 1250 999193219 999193249
    0x30605010b0f040302190e070306030c05060918071e091805041e060b210705040e060a11090d060f15050105040e090109300504060f182102 61
    0x70400d02c40803034601012101925010ba86000f8403442c1a040c0e414011a20740c04000c1044602c0d00f0b01130100d62603003010f001c6074040ea403810398241c0c603030080000520643e0320311a44801c0c400c400101c800c0d000101c0541c09207031410071403a52482c025040050115882c01c4500154122030203014443d0380324420514049182010803c07890260340703541010301e00c002c0620b841d0110007048801c01800d6005881b00480c0548030345507071540c240c2c02d810401280d031460311140c00b0b4908089940c2c105489014081c21500000300416211001d1000081c61901c080c100c2c40d4900300301c1d040c819245e918000d400140310303840c0040d05c07000444550301150201e80c1841948890000104000d80e8480142c03000c0d61511503000070b894860756561070042001c110700400703d05101c038585810240158910300410403041035001001204102290031380300703502412001c101c0704c0313880d10079252040c002c101c0841000d050300400b941d00c03801001143e50030043c9038201542c40007002c0045081420310750350211 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 999195719 1250 999194469 999194489
    0xd0c1a09030c0f1935090f0906010c02010c0f051524060405190905040506041b030512070f060f0f0b01020c0d030e0307230406080a020310021b0105010b0403060501 72
    0x261a02d40c0c02d600340650414007525850313089042c80b12083c4010031304078400d402484544035558001860b01d801da000040194820f807c800410642810841c80780d030321480d8165641c0300c440c03119a0066402c40e40f0340030280c800c0b80107500b802001613010800b00041c0d444c0c1c1412401e683c5040d0000e13100e040c0c02190b5441900d0b113805a114050346508080d80c0aa41c4d0449030015500c0e820308560383c00509a0b4040200ea41c1860140720900c800882d1207800fa501482c1c1203403140d013840e07213101c905400038480244940c2c0003540d06c1d003464a500018110661290484006081c010789541c0150385d00c08100200040d078540702c480c040c01861080e8450070b0704c01c0c009070120f119103800041552607140006814030134901c0b001c040b103980034000310b000760050008984000724150483c6052492031040c0d640528500000480c26000c0020b21547d1681c2c000d00603c40314501442030b501a4002004040c84091081c6035004190340a0140c0c6020f4012126103d842d540740d81448025242d060344100625 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 999196969 1250 999195719 999195733
    0xc0d050a0605040b0d170d091e03020c12060a0b060705031b1603051903030b09070e01081b1602040e0a14010c030506150f040b0406030e0c01020105090d0c1a09030c0f 73
    0x50401c503451000031b000c514155849021545c02c0401a00380c080004204207044420010f030742e10410800307a1910301a0f030803a0301001c01d1070148403a00102555056881c0e001200003400c485640d0081c9a1000011b00401d0800d41c442e51098607540010002111005407000d1840000350b04000094508002c20b0094103a18955201e490721110520110f040504c0518101001e042c00303908603e403030310790182901d04c1602d020207000b007140d03414050582c0041c41100210300c0b007400c10000002003a14040070035103004440c00b441d02c100c42c0240001c0340c009440d00b00c8241460010b0000c4900c060055603c0041d11100140c40f50843e1000c40340002031500c0c16052143c5900e4451070f48c4601c000d42c08156070f45024219103084140526445032141b48400617002c1091035041d0414600300319244119290080805c0040e13090713810880d2420707129405001c001e582c0c17511801729092618042e100200d50005030305003d40c482c40d400c43d0100c109078400074503407031519020170152f0603a4010001034288 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 999198219 1250 999196969 999196973
    0x71208272b1704030209100603060b0906121e0109021e12180a0b070309060e0d0e040b060f040801050609070305070503060904081201060f030c02010b0a0e0c0d050a0605040b0d 77
    0x248030715070603018103242e10811a0107100881e0b241240c0103190020910b60147c40e00702e490041120b214002c4400007030512030b0002c0c0c60000082550031a05004140318246584a003400e900d50100500386200d03440302001c41000400c00c0e040f00c81c060304130344001680d140303d00320000008000895104141710740400c18240c0c400603400d05c1a41140c0e400301078903004c9403440ca078249400c081e150007501a403070740014858590b405030f014220581c42a8010701c4070107210aa8991079070b00b030205501c0461015400018a481c195000482a074401041203060400001014480e030b009500558010780d134440501a96103070030001a9880390702d501d0144020b00d40480000e00c9404040c1038540103a61440208041000201c16641c0c01700c4040b00f00e541035a914a0024004c0209105500109150080c0812214410302912006401c040c181000302d528110203000045c1005007400a03048080c4244443c3c084280a494003410340d41e840031031294103140400044401048050703100d4001c07240d603000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 999199469 1250 999198219 999198289
    0x11814010f110706050705250311010c0b06040b04060308120a112727010e24130204050d0605151215040c210501050603030c07120827 59
    0x410f1324901d1070034540314582803030441d05d03081c07040c419640850200c030700d01400741e40c3c1651007000703c1c0d01948039403141082c502c00540f001c4602d0980038060300d103d040018101c1c1000c0d04a030340c540402400005d80150b40745c80d600307a039410900820000440c0c41c01400783ca2040ce02034a0000f0721500440e40c6490301484554042c8400100c9072005070008160b01585a52090307a000e032140c96103c41d45a0b040310200040b400035000340a41c440040c407481c041042c1c8200390000c800da112020ba6608182417580303040200c200e01305840d02c1d800540800000c900c5444d0010103d801510640c80411503050403c28260030303c102011080c0142c9003184250010800003500600d668400c94140c1c64a8485080c0904c03a4001900100c0300c0c25034003c650040c2040f030703128411040d4007c0c07001300005e4640804061b202d106056105c1030a80c8005014400203039110000440c180c0703d5482c052a02e10b01c00301103c1411f59040b045034460043d541054028200303d20078104a001102c2d84100b420600e0444038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 999200719 1250 999199469 999199483
    0x60903030304110d02090c0705010510081e01240f15050301061220120a05040507030201050310090603060e0616051606090212030c070806060d0b06011814010f11 71
    0x2800441c2d040c0d080f80c4850319020012240c1c0c0784c01501c3c581d090300e01540310502c554010030084601d5843c3c00009142424151003035015180f94170049c00c03240300003800386041e5401d07010401300c5c15580e900c210815090710408046c104035602c88000e14071841d0100540b00020f07a5442890050200100894015030220881e415504181000c40c58182460350380c00c01405103e040d0381e0b01c05c0d020388a2008028026024003580b51107020814059500c0c980c0340d4003a20b00030703940102680d00402042c4010f60150000e15403044110740346484142c0e075800d080c41600c0300f070381c42500c4855035200c0c114070b000e0052243c2c03603000c0707003004012840c1c6001c090010824480c01e0410b9a4660030007040360100440c0350001c01945400414101808041520320341c0c41e90f0000b07800e0101803007001c5000800050129529106503001000310700d804185803031b1700340d50b10401800345041014501380032482c0040f803907000000d8905003042c0340641004500240c06006151803040c2440740c3c1c82120740c00c68100142c11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 999201969 1250 999200719 999200723
    0xa1e031103070c0501140f010f05061207110a1205091f09060513080109060b100f0f0c0218090a0b0903250303110d090b010603050f1323010605030c060903030304 71
    0x9000f55042d0034020f0044c41401c141c0076400840780248484003052541c0c1e1070680d00028840c140380b6540c0c508103e440d101e04040200f00780c0b0501e00048a45000c3d40407003070b83c0c40c03409040e01c0c2c545449030764100703008840b0b110701d43c08180040380725101030409818440009030318030380111806010b1030018011080340d1043c6800c10000042031031480c01c25032280001004510024000f1005603c0c04001800380e12070924016000308840d070329068410040b0074110f4545485e9148902d10300b0004940d2142d0040043c5d03000310320f80c2e100300d028802e00d041c10b92084281c0300140040da00d05145c03135443c050015142040700c1d401440b4851034212040b03c84e03000000d40e104c503007a1501c102c0c03500f580500075007108044070301d0380442c3c009516075050304441c840500c40d403004c001c1030780c982c0310035402c6400c10f0300c500c4044a805000101100444070981d035a45000714200b04086441201c0000420190782050407165120001000135080410400d00c4810003120b100d4104030111700880e589000040c80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 999203219 1250 999201969 999201977
    0x1514060f030a0f080d0606050309100902010801090f0920042d0e070e10140405041502180301050735190e010c0305070f0e060f0901030b060a1e03110307 67
    0x2441003002d554200e44a00100c0882070003016951f0001808680044840b1182070044d880740c02d0f0402140d1013920740996050715028226400c00c101c99005007450841031856650718080380010601e010355900f40e100d2032814868100d4070300024403060b210744441e008038080b10008041c82045003e491070044001c0020000342c43e28030207022500c1c040c3c0d240e1110100d524400d007808a480c1c11014610160354501d110109180400010300040780d00482d0050308501240d00d404d211800c1c2c6030018143e15050f0209868049050b5000908543c403d030340a070089580050f054040403640840480320814400364003540e9030207410740c004105401410544044200000907001c9600d42d40403c0034102d01c68001c0141520f8440c011b802068184d8121012a02000c00c0d40c010034030400c103074024201e014165034100040303504201080e8100110240c1850b81350b05400801d80c449802806425903a955100d001c0d0304007051201001980562001c10142050440095900b615003100c0c1c02200d2854 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 999204469 1250 999203219 999203243
    0x1b0f060703090804051e090c030f04021c17041e1d07112d1c030c03060302151206090c04031707060f061517040206030406091514060f030a 61
    0x10b005010f62040c1d0704000d510030080d11042600d114205400000d44000b030f203001001c1d40f1640200c00341c6020032074281100f0494200010b005043c20701c25103250700800d1141c031107604041d0740c82c1403803400c6421603040600030101d02041040d00110014894118034a180074500d4201078a040000c02d18a00d5541c83d040d0000204840030301c60070400003580c00d14020b03159210740303001705038201d004002000b081400607413840c2420aa4082400040c0c0c55080c10301181c80091002c040c2c026050511308201455039400001015032680f9402d081040300c80f441080e40d400301c889404c2c401200280a00380208a80e004101c401003a007411182920f4210080c0c02c0601503500302c0c848244a00540180180e05001908128410315003080c001d4071a002000340c1e90810307100c4111080c0800010782301031120b100000c04c0250a10781c0065420074003d201c046801c8040f80c484406040100001d01c1c074169a900c10040c0f108912001c185e041001161491a2107169100080d9100e00111000d4a40e2120300b03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 999205719 1250 999204469 999204473
    0xe071403120c0f120d0c03050606030412030b100c0213050408040e090c130c020708030a02210f07030203070611040e071101090c08010e060105030307230a0501060b1b0f06070309 78
    0x800d02584010216420803603130469104041d0030080c070200d0420304240300701007014042c1c000c0d244100d6004e8050380c01e590711500c0321001030340b11002480a0541d035000e4203806071110b03100f80c4181090360300c601e81510b04910601003007100034000030300118548002e110000320340c40f040750b084529100e405003282c0c5600c10b09500704004000300c41c0c0e2007603a43d04648821581c80d0441a0900110707000d4820959542003e26241d12590b00c552005801c8004150501c040714050244070301182c40c03030f19060400c40000e00d0401da200d51000d401682c03010038810304108050058400b10640c02d100c65081a1a0000115080102030002c01c1844407509040150500942c44051134680185a04401c1c546e103030744160080ca550151502c450003900c00209486c14004111140b9a920680c2800400030316048807544440d100d04040045c003400b0b58810224600740240c1c1e02030300010400700d5540c000d05000520a24108944906a40144010540d000008200f90f94003140906000c20410014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 999206969 1250 999205719 999205723
    0x606070c050406180b030a110d1106040b03040c0b040b1902161e0e06090a110d1a010905010e0a03061509060b030403031d0d0e061c0e071403120c 64
    0x180c0c0065802c18074003680012210307007880010003400b080340d100704011010141419114885007002600c11418040b03c0e00d040c0c00c103000d500e00d076580031f00c0580b80c2407007245001a48a5005600c1280f408102000f0f010900c070a45848000800c402c842903458540342608000e6a8050400d022841050103071510400c18000d01c0020400c4240b24103200f50b0301d441e180c0e00642c80c000d03c0c0f00020030b110100c2000c9a210305500c4403038000c02c0018000c0c225070744c072800d8240c09800d20a03400c40115074103120001c0e0801c21400b9280c0800d0420000c40c00c085140e0300010088803140d4001810014080d17501d0041e51a6140c0750015203400c103074041500844840c2c2813176016413691000072103519204000810202c0070000e103002e9403180d82c05100144408820040503036000030130b189140c00194403201081e01551100107020400b800c4181084030303655495001e2108405540011600d400c02010001000d11180c2701610703400b0880c0c1081110f0201007503071404104060640a58000303030784104a041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 999208219 1250 999206969 999206993
    0x5031b0a12120f150e011208090613080a0f1a1315060b070804140105070b010e090114150109080105011404092303130504020a0c0201050a0909060f081e06060607 71
    0x203491400c1c000441c00d0004071400c0c800302d1242c0b015480c0e51744008a9001224101c040106401180c400c1c00d200d030f0310341003042c030b54048000c080f5512810b5500003290441407240c81c0019000706455400d030790b014240180c2da103900c0e0303002170341d07082411040143c01480e1000c40e0312140d4000c03901030020921440e03c08020000c0f504040112400822600c0801003114010003d54000c115003c080207030060056480d802005c100500c2041840c00520256821203801d070b40c0041c99400210340620148c0d20034007864400d60300810301080d240f01e035000e00c0d600180e0000007000e00c1402000290316014214026400301c0e101c1038440c84e12000200148200c1150910f00d10801240191040c0c0031001c41c0380e42c030382c4480b11503c25408104000070b030074138190bc25142600c4203078413000c0a40e80c19a004455561200c0d00c84c5051012400021444020361710604000c1c143c140c4249100f282081c0c2440d15042c2622410b01d50070321000c0e10700e00c0c01903000c07802d640c209030152581620341d141854031480280b8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 999209469 1250 999208219 999208241
    0x603040b09150c041e0503070b030406090b0a020901030b01020c2b08040608010f090c050706230103080904180f0210170f0411270c120405031b0a1212 66
    0x1060001d01c0600c12a0307000034812901300d402c1300205200c0b40207076100c5044886c810654540c014020401c840c0d0110401141d0061040e40e0000c0c802c6400e48d5244203848069951702c030860390201c3d8851083d40c0500c50442180c1e4240018521040b0000000700c807102e4000d10f142e0881c0c0c1441b860110795610950318140143e00030700860b203035034640200030a200424428104442900c0c20b001131004400d1241e10908025a07840343d24005894a4000203044103500601e80025052680c900003030b182e555040c06075209480499880305a00b00300000d4910445485003a4001c00c6901e40016000180d100300c010b85c160799504d11020b04003400e440c13a03498041100c00807000b00c000c016080700380d911024420340c4910810414840f6140034482206107074103104050800007001d041801c040c1440341a8404501e400d40307441d01d6071100c10904144016101101da80d4008104450543c207866000c3c5945029032008000d00b01241c0c59240e109003041c2c030080b052043e4031b5040c8803000225040600d0b946 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 999210719 1250 999209469 999209503
    0xa060806090114180f101203020a260a12061409060d1a01060c0c0b0319050a06080d0c140f1b03011d03070209100501020706030209031513060f0b0603040b09 69
    0x3103040a617090fa00e0a044803040003403c281d04000c10011181d070f180c2500240c042c3e006040356103040e0345c0e01d81c050005800c00010030035010700091000312007200030700d451760081e0349101c08003aa0310070074815038006401c03076440e103800e0000c94062a00c41c800019801101102c85100c0c1100500384000001c0021070100e108880500020078040e4102011181c83d43c4901100d441032a520703c0301c600ca901081c1c03050000313402c00b00e1121001c80810f400481d08410100c0c00024156a00c1600d14a0480b5240b43e6401007484519100207100c03e2002d507a100c5207140b03020384803035013a40c0c0c6486d0f100d404001707200010084000c401003c41c0c80075480951100c00c000340300f528403130407076210a40c2d1b500300400c101e21031a103050020320010b04103100d040407a80e06800070240b00381000003da0294000345038040e010312402c94020f0002071340c20b00d5240611403440c0c660401d40c070a0f003050400e5030707280411710902a0400445c4002c039120901142d91040c0c200e020700300540c075841212800d1041000709a5040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 999211969 1250 999210719 999210721
    0x506180c091e010e0f0609040c03110a05030d12050c0f04030201080711010f05190b01210f02030f01081b01050703110a0b0f18011e022505010204050a06080609011418 73
    0xb0500c043d8a20301917008034500c0a8540d44607410000074120840e001068003950400410000d5188070181d145048001c0207001e07059101c3c1e010a16001100d03491600242c01603105080303103c128410a0740105108141900d04142d02e21900c3d194882d9210080c10001c0708800901024418204181d138a05614000c0c01101c4001d800c1c400078104c1aa5407080c1071403102c0707000384003010034411040aa44180c48035860303842110840c19224801c1814160180d0304c900b100c1140c0c2e02240300840c400e001040c0c0c038064035410900c190386080b0107000300040780e44c000c038044805a07800030182c481c0e481d8103207400306103844100da03c50304200c11040014448000b21090040c0d0b001120411031007028144001c201c11940030740010f01381d0704081c4c0101c68a4483c4502c0c5440ca02d5250010040c00d18031102c18040d660120300482d0550160701c07820b0722039942c04a018041444d01011503c0185958900503540b410b04c100015070b44c500c10b05c10b0300201002005a006142c541307900c40a588642e0760801d642c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 999213219 1250 999211969 999211979
    0x30a0809032112060111060a0f090b0406060e09060f1b090909070504050c13120503070b0106020a0c060e03030d0903030b1003060905060402030106020a080a030b100c0506180c091e01 80
    0x11500303c0280e11812019880026900354822103200c8911500ca000900c5591105c0b100300c2c0051940c1441d2125964540d0800800300381903498550066115400001d591807030082c01c230200c5440034040e545684c004c0018405401d803440c047c5a0402402030b0a4011026801c0034004584600300c241d40d0031001c40002c1041144020a20784100c0d4815102401b0587d0307086c60709540b9100e070b0344142c40340001c0c00c1d40601c61005000710142e101e038412002c4916103001a191040b190000741d11000043e032080310030b101000b80203080540181460300340101070400030b40000e0307202d0040e5808200d00c10380e10320858081c075200350403901a450001e0050503080600760b00045c0a01410b008000d2802d00b40360100b407182c1464400c40741202c050380e01400d005401940e80010983c132985404007016120450b00c044d40d66814000b1901d55440d8030381d241407490601c1c1c0b03503041c110010b02e584030400c94803090242c07081010500c01003e40e81155907a016a49408030b0f00140c41c460054407844c54402c100103e1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 999214469 1250 999213219 999213283
    0x151403070f0320061303061109061b0f0102091c0204110f090117040503040509040c03020402040b180d0305031b0c0f030702010207090911060a0201020c100c1d030a080903 75
    0x700f0000c05550a200b101c034803905011641c80b461040919020a802c801c0011412540c03048401c00d03041d8140628008a000c00921140c114030410107032500c250058902180040286500110700034000354101314445000074a011580c0c1150300f0000380c00d070400e50455580e0341c004521f15032206002034603100c04100d00009a0444510031740401d2004500178040d02c6540c1101e031245500c0401103241a090000340700790300da8050b20031a6207a080c03a10100050751140040d101038500070043c2d588030502d41154071285810000480e01841e8482142004298030130210f0303900c144030310f1240d0a23100ea01e00c6d429180e445a03500c10b50b624081e041d454466800080001c0001c42d000740d080740c0000d0344514081045640d0680c000300380d64031440c40c0c20303030b641400390250080c0301da140001820140c1d031000c05800c00c47c032140c00c80200c96842c0a00c00440d1f0704404100b00116a021a40b030702d41e48000c02090f600d14420402808521000c2194101580d0811461241540355604010f02070700d0071001103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 999215719 1250 999214469 999214493
    0x11e1e0506060d0e15012c040b070507050307140105040c05090f0c031005041b1701060519260405061605030a020c01090c06020106140d021806031002071a0a151403070f03 75
    0x1080c11f001001d02200203c4080d804140181e42118003031006890f10700c1c050310039034800a01243d0038081408201c000c02d52000c0c0041940c0d00f5800045954585450003107020312503030f04000d01c544980c00c203106182d00302286442d8021021124169a03032034041d10341900700f030326500031a0701608000014025903034507000d0156185d80c03071315802d40744050080c80241c00780e424085c000c005030301400b4081c0c420020038181101000141011814403807642003d4200100345401c030350050b0001024003081007000c1089940c071250a1030802114501800020901c0c4005030140b0309803a008510f040303c4140c01e6102c0700f49140e000c040a5085a079400d4003074060900d0b0b12070880c07241c0a5113004500750070141d0380c010b0032036401440c011000003214951030400d8005050b250705803082200303002e4050840d00c018103066005006d01035032400050b500503544203000740080300d03560a080b004685981d242e201ca0082c0c80340c0c14090340b120b22030240407906c1c0c5900d039400400001000c3c4400414026510404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 999216969 1250 999215719 999215759
    0x90411130f090b0102011b0516080408031801020106080d0c05070503060f04050d0207031502030907230a0803160807050307080d050402030d020d090611011e1e0506060d0e1501 77
    0x2400100301210045e400c071602c6071a003041e4408848441d1000740d114000805071452061180f40741c49141d500c5662968126402840040d0301c00148810076152259a036010031070b00344024440b05040040840d1103524a250b03500c24464101060820020144580e601500014084070340300e10f808004100400360a64094032180500000c2c050300c64400715031a016260800012007100e000324403640e0095000401160391405064404200c0d074102d036940f01d40102e900c1840fa80c010610004008210010b5400a01c9a0703008100c40c8012403410021220b00d00d8005001540342c84080c100281103202d02d40f00103064410000e42400b02c080180d01583c0100d0082c3d040310745d00800c200c4166904c04070f03030a00802140d45a0410003280e40724480c8443d4a200d84000841d02c0d000d501da583c10b41c500b01c441002c54013503c8041400c40b40e5001400c0440c0d1a085482c24003460401202003143d80c85401c2034482c01c00d49518015240f00740400c002e41e01265042408000c542c6e6800044800342111819 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 999218219 1250 999216969 999216971
    0x90f010912111804120e0103020c0d090503120c070902160f06050117031e0c070305060a1d030304150c0507020d05010b0112151e0f0f0e071103090411130f09 69
    0xb40f000801c0e00c00c802d1155030700c402c803403d02c11000b0380250b52480d00d101d500e90405400300311810320b04e0b4044c403c154600300a62104981181060304250810a45e400444040a42801034903902e5900064000445030403031001a9144501880348203e14488000034046003c10043c140400c10154001030490b0140c0c80d40c60749812619185e40d4803803103100407541500e42c0416140c16508084402803c1c0e4000c1c1d0030895040765544d0b03545a080110441b5010415503480302190540740310008540c580400e41d501551070340c5803e03502c04480102030324665a20076a00d8168469039801107040304c080a40040091007401200c0c40c00f00d01074080a850b184c005072200c24900d82c0b1091900420158101c204116802d00e4140043c0c90004a48800da2404500c0c09040c00941805090a91005840540a003609e210704104da11040d940700039107400d00708403401103d98807007000801a83d280d01c2c01258045205603c1c00c49406040c024410304140b1344200c20b60020303009a9a9045004075240658 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 999219469 1250 999218219 999218239
    0xe0607051c05010501022d15040b060109030c090e010f060315060803041a0306040f1d010c17070503090a061508011404171c060306061e0b090f01091211 67
    0x41e401921428030409001d0ba110680380b0307810b051041c415204108030005825120016044840d20704180081369124228100003403200b40828182095401002070030309a2425156075981c0160700a1031095000346540c1d41194008418290804044403120340c0043c03000307a48a080a51154240f1b42491070010320700400013841500c0402550708030340e0b400760a681e200c81664101c4010360b20080070325510a55440c8500c01108991180c4407003002e1000150078180708448a036421240c008100c00c0c10301400242500041061f011940d038004410700d00305841c1e494030001d280c078140b10010001d00386818560b014041540780c41d140030881c3c0d1080021300140211003a400c030f503500181d80c0940429405c6030001103115462009040e21600c8544001082000140b9601210b08a4000f1210507840700350130003a620b805203542d003a00b550915184121881c0124108051040040c1c00380100140f03000340310a070b03001e12003080040042c0507140300d02c44d8440c40e101c03240f180e4600c80b16119115042d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 999220719 1250 999219469 999219517
    0x1203050306090a1a060711041112010f0b09011b0b09031809090a0311152401030203061e030f07090e21031906030812090105090c0d02130e060705 64
    0x2008050f41c0c007598004d50030010a01406010301e41c1d0103443e050301c408800c9060544c5903112072003004071005090120948903050f0348040b4005110603805502c040f4006e103403c3c00003e044c1801c403000094242000440d01c2060440c1c1c04034490404006014000781504000c85000040001c1c0f501c01d4900c240d14800217039890402c840b4400545034849540d2201b20180d0002e400351121110414841382101e00320701070354203650250740046030000c64100083c0007500e4941d200040b0a084a0402d09007507013075241150103e180ca080d103001d151844540c184103210203403001c0c005484450590b1040c0e458039a01d4010a03030141101c00b00d800d03200e108000040108503020042c02c1850882d55859500c4c0d038072485000e01760300300c2c0c1040e00c07646a5502d500020000d0003040040c180301704003954000d140e00d0b0500320306085030030040002485400144a40003da501c84d07000d4803c00c1d07411500342c0b80f4001082c4550005002e40c2d4500c0f441c030702c40c20041c0901d032a0414050241c1038251506c01c54000524 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 999221969 1250 999220719 999220721
    0xa020a030305090708370804210b15040e0f0303100b040e0708090c0a06020c031e1f0b09071701150819090204061203030b030625091203050306090a 65
    0x1881075610741d030060030218900c8801510700c000301da251402c0300702d101d0b5011b58610700004c0820340111000c5000017000c10500c21036000c0b514480850300d48154035501c180d2940401704000034404022803d00341c1070300101d0ba485511171003550703020f90304071100140452a1103075a584161032254484c112614001003a400d0a000c07a4160b480c824901002c03910303500b8050ba9982409040f04c513081c090b0510112082c3c540958000c000d1241398020300703962038400300385400e181c0f805500c030201d01140d4855000c1001c001411a0740a00202c03a20840500e451040e20010400341c4030040c0d0050000c411301901c1540820b11188120344060400d9259036210f000d45c0da079000c010301c41800300b0851400111100002100009000503001020459507401e0740040e00f213036801d8004602c17421003100120b0505502d03114a6040c54000e400800650900c000707a000d80c0840000302d0000d1813000c00e21144001e20032540b050042000c010400410030701440c000e042ea03003084072200d002e241c0e8240014032034402 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 999223219 1250 999221969 999221983
    0x1303031b03271a071106040c090c090602120c01021e0a0908161203020a0204090305180a120b041b09092a0b09060c07181b090b090d0204020a020a03030509 68
    0x445014402c003894083c078041e0b09480000c080200f80711030700c10024442c103804d1144038480ca00c03c01d802c40f9940e0511500c4000c941c1e42c0746d400d03400c014040c0024001e19400140c14169004505c104a0f22601d040660034068070482010060800000041c09020450403001e40440c1c501a20b03156001e03603c807003e0503503a101142c3d103810f009206800c20400440142040a8114000c0c4140c440c046441c1d004203042d50480d02c01200011000580031410b07071540e800711541c0c06811590305c0d00052500080c0d440700945008081c0c1000254000700d020081000b901880400130740300340860f035580e50000c0320028403210b2002e403042401451400c0c0c60741d05070a18100c0c02043c5a201d485200d0401c0b112401d950840c80105800501c20800180555010002d04004002a00b40099003d6202d09100b098462202d8020540d0340b052845402c1182c0008800064803500c143d0541c0b00d0030300b800003ca40300d1030641d01030340052000038540d81c2c4960204107142014040c3d141400a61a404803d070f550b061 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 999224469 1250 999223219 999223223
    0x2010e0904031e12090506010515041a0307051e090a0905271e0601170d1205090a020607121805031b040e061614030f1303031b0327 58
    0xe030f00101c0c0b0010381d004402415000340d840d0850003050311030003080448140c0841610103030311441c01004146040c012003c00e0035044182c1c40e0401c1e00e0a260004070b564880c60207841c152000c800242e42511580c02e40703402d40d000900c41403c4d09044031905019a12000c00c55005d0000100c0c04207400c1c84501070b40340035410009201006418a984c2c9160040958050080038003d4690b4151741c1080d60300b0007a45031120b00080c1c0ac041d450107454001e0b440d081c1052400391b8108a60304043c081c0c00142060b4981c00152020500340c0e11005070138281f611600f0025032040b0042041c00500001d02110708040d4400c0c2c85070003559170344400a1284130140d105107580740d400b06400080c10b5205540308a4450b1021b80b001c5204500c0f8a409420040100e503d0000142010004178100740e1000c0c0340c1c06c001402510081c83c43c205000c5040100c00001c200d03918000c920251881054800c1d070007400e0b101541c04010541002c0ca42c0010042e01421862904c10005504220310f0442c00c40015a5100e03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 999225719 1250 999224469 999224477
    0x3090f0c2403020f0a081504110a02010e0118030818070f080d0201060506040501030f0b03010606020312100e0f040201020a0605010b0913020f04031e1e02090109090b0f1513020702010e090403 84
    0x14019170301213440c070100520980c1e40d26008224180301d51520300540107241d81c1018400d403600303c0d840c2c0003805c50b0b404c8032042407507170304017185c01c41d10003250079a002c909501031422101540d229110403664070600a0082c0552040140018000d050461050180c070f190030240c60300011012000c03820790312180500c0d40d00c01c000f08400c21940d80680d100b84c01011110101207001441200003900f1510b407640482c0240c0c200054958002d400720311001d82c001d00619510000c0e505002da00d52041c440140b441c400318268601042c1035a008001c1e400465034440428407003907846044c175041c150407411056000b080008240d4010380c28500a59400d0341c0c04c249964141895031303c842d455007009541c0b9195001404605a0100340f4000706070031606c1c00110610314041d102d1040c002250016800070031291325140a0800007240f00c0611500704070040f540c2103550b02c8072110010194a40001d1350380c402c08200340340300069090380107082818000d03224001d035500c10038240120954100da0080000e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 999226969 1250 999225719 999225727
    0x320040311060412050c1018090e07030507140901060815060f0f0a03090c08030a020312060a170307111e0d03110f0f061b04180f0c17071b0303090f0c2403020f 70
    0x401e019070007110f46160200452f000540c1c2d0351503030340c10300700680c04c4400c18100c3c00000c0041070801203a454010302c25490511003514081160740c1c030340c0ea12403124a100300360000b82010305000300703402d072001d0040c04011540e668041e050041d000b403036408400c4910001c0b26500151100380030096407a44145600038510f032901ca6002920600002450280e000b20740b1100894640c210511030184422079100448e03807012030381405074007010b008800034460b1f401c64011241c100d0350000b404034241000d072842181d603107042c50152014142c52a15425a100d09090103010507400104404140d24680c01d4590303e44422547c4001c0c0e01da02c40400401180c00c00c010000c03100036200d035018107840ca6000050300009010300000381d4441c00d0544001500c107404800344400900b01c015041104c50506039041c0d0007411100001600007d400340906a94001007400d000ca0350303c95034030f6a64492041c441040c3c450300e03d43d06840c60a14010011076500740380100f0340e8000c3c0b0031281c5611a03031001d5410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 999228219 1250 999226969 999226979
    0x5030c16020d05030403150e1b100306090c090501030e0c01140f130902190f08180106050310090309150801171911010320040311060412050c1018 64
    0x144020000049030440c0000c0a039001045082c400380000e544901c019005035404c29491b01d0569140140d590f081e500b0060400f003140c9d81d21000c0401912056a0000c0c3c40c003022242030f40102056809081d02c0d90805182c05070a5a010500c4800e650302604c4c1000b00c1c0790302000165035840008000e601150162501c02244007000015100010b6094000c40c42c000940551060750304196024250054000c540c00c5072900c0340345940ba20443c1c0d686000b10000340c2d44140140005c9010b441426903042010480c46500000c2d0880800f034407025045031900f6076410000e40040080405c1030700000d100384c10201e4084181e001d140030a4504c1e560b4007001da400c0403541c45000c82030303e008040c64452600c8c982d459005104000390304a0141d2486075015600d14005000c0d184036001100000610030b00e250b8000058405640540ba0001c0540d800301c1c050001040b201e200b250004036585129845140411200140d0034a40740c0c0190b40c560b0000825640c250790f007001c0c206601111404078601400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 999229469 1250 999228219 999228247
    0x905341a0702130903020105010e06031506090a110301180e0703031d0d060e06040b160801090c020c030a0c080d030902060d2f0c070806070c14160909060c05030c 71
    0x14035640000d000644540c2503c091600700d451841048000d40d45480040204031280d882190384450f00740c1c05004902a99400d100420788028107140c803406955002c1800c4040b90360008000d090713405101980c950f19a00d01e800c40b074a0100d0100c5e41c1c0d40c10400d510540c66400b180c003208482d41a1921603084280c11500c2c56414440341209400804015000000c1398031350281e01044014a0003605060a1a05194000190040c110118401d20301050b90703180b40d1003800c0170b04442201100044034070004200700c2c20002000111545031041400c0784043c40409a601c1040300c414000303c8015480117581501a1403034039101a500010500140c0c0e0707000b580703410a43c4005d56078041850741c40300026410b03012607000300341d541a20f0000303d881847c2c01010080c101c05400610002c103250700e00440003d01c0754540981c0149204d4403181e404142c1c8404100c80c015280300e400307032101019158210074005210310038068440074185942c0b142d443c6d00450031a4061180440400c3c50034049541e005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 999230719 1250 999229469 999229477
    0x60105120403030c031e091202072607030c150e091003020402072409020f0d020a0b1c0603140114010501090b0a02150a0504031103040f06030f0905341a 67
    0x8401d05da200d0f4219181c002c015016004c0e005410b40c000202000c45007800201118035418003c25980010414800100f241c10f4070f11038804810740506402400421403414606160700041520700c08000105142e40111030030301c0c980050f035441e510018100d008000c03154a040d21140300f28845a00e00703201500b004e17001031407018011714005448274020104007251a040304156808190b4490b0940d0840c640000b0328000751000311200014266150005a40714155100700701c10b44800203406c91441c0544100342c200810076680802007a903590070f10360300d500b0551510018a500e8074078000d11906a000c4214165071040e9100500c3c9420300c0208161540580425800d602c9566400400c2243d202d45452040604400c04295420319181c09454109440158583c0d60001e02c4180290054005010b04840c241e10300805d06866040c5200000d20180340054030340d010b03070b405d450b4124603c4000c8000c2082481c015030061140780a410b450b00c540ea0040d000d980e030818421100b400e10740340140c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 999231969 1250 999230719 999230741
    0x11010503071716030e070506121f1e06050a020601180204031704090c050a050d0c1b0b011a09060d0903020321090c040203070c020d0c230906010512040303 68
    0x20b000c40500b60b01182030044012112003150003505038414600d01d905000b21035106201d480140410781c1013500081d202d0117003129038860307015440009500e100010401d6000c81e4501c140c1400c0280d01c44c20b40b0106003039031118441d89080a080009195032148044455588282d800b07401c2690810401b401e942555012034401c4075004e20022000c03a400320a00d40c0703211804114a9a618503000345c0350207071108035000e0014080203000b260500c82e00102100c0031610030703c02c00900c1c503100b4442030340c0b20311440100c40310444201200c2010001c400303060354140d03078100003654000c1c0d4030314210140301c3c030030408015080f40741800030303403400903003504400c3c003851280c0156410011107070b81844003000b070f01c0f0480c8040c54010042c00145407091020b082060030644040d4518542130748098201404844c009024600a8180e84148412055030a002d0200810380c1c0410034034840d002038000303003094041c2c0e21036080407010591707075070042d4100c0310082203d611b801c0c0c5030f603207649040d00181004244 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 999233219 1250 999231969 999231977
    0x1e0804030e0316120203070e0f0a05041505070e13050601020706050706020f19030515062203080a0903140a05060403051e1b1005010819050307020307060201061a03041101050307 78
    0xd0304082444003000380050720313000488041c0b019940c0101403400071250320000042610109000c55048440f150311307406040d0200114098503a8644180c03c4e0f02c0103299014200c1c54101400050390307100c2403c1a641d0011a8512400031103862002c1c2100c40907105140580d100d018100038282c02200681400341c041c000040c00d0501c0e80301401c086e9400840f090a4081c503d944000d1420b81501c01c9a42111204a10080025904010030190303c160301f00c91080d208011040c6141a03da15000c0c000303503500400c4c1d2526003046076406800000c1c103001c1141e04058180748a50841c45c0010701c00c1065400c040140190340b11074400755100c1c0d02801008040e00d085401c94003202816030010301c0940207880040d84c4300140200f150781000b51a0400040c004d08140041000d003100164005509a5800d007407801c520151516610f10310076082d00942500440d0000165250198804230407110192500d0202446100c2c0d450307414881100d0042864a10607a4070181303520420145a1005071410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 999234469 1250 999233219 999233233
    0x2100203190b330c010e070302011202040b03070e0f10030b1003020f0d0209011403070207030c0e070c030f03090209040c0f080d050d2304210207030b06060f070b0103030903031e0804030e03 83
    0x9140c40c00e40700c041b41007034034990001004100311759103c100e50002d410800001c50616042001004d014440a003420003002100180e01015075514000580d04840040c40403071140e98440015018204050b41e0900c10b440c00305844a00c00e000380200c4200d4070031007005c90b18000554903510001e4016512180c10002c0c0d290715280c1081ca480000c50003061650001c1403428958030300b00204d0743d0141c1080c2d204041d580c051041854004075240c082075072504021828070484c210440003843c001c1c001035031000001050106101d28901039006840c4002000745d9402c3e210920305030364401e4414064005441041000c903518510751007413000300c0036001c104458101c807102c40428444256003c0d200c60b10031000050301018100c80301100c07542540040d115103855178584400c03901c001495030703019240c002180001c1e844040c0071120000c0d400083c4819030f5840f801d0040c41403800307000c1100480c45600c03220044121829440603122041d03030b541522965540e07001c8890151010031980c05100b04c030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 999235719 1250 999234469 999234487
    0x30f080d140f161b0308071806120609051e07030b13050a0c0e061b0703050a08030a0c03110720042d200a02100203190b33 54
    0x5090707a07000b4440c1d40030181142c20042e10700c0e054400044040d80c2401a059101031135044d4042d80303500c08a415003000b001302e94841780181c17072050000c3e0030703400301071000b01002c04d50b41c2c0c02007403d002c0508481f004011550b212501c1c5002c840003a02e91140c590160441122900c0c02200d00c40c0d0720200c2440c0104804d10032a002c9806095009840c152003030b1900c0411646034000e1054265044079803421100300e00c04403022070f0062042d00c42c405c080320b8084010903603154040203203000869008048420f1642d581c04e1102d25904195030040005080c010210401c0340300c2c0c054000d441c102c0b541c400d031030312841e41d4401055001d4000f5903054450700e0402414655500e01c03aa450b01c0e10f1020f000d1402600b0b008a0030010700c651003c00980a14000150f140b00a902445000342410f5281e0180e40d2072601405034504000a1a0700045c1400041000006980b032203024035100300118040c4452481c8008118140c019124018400c51401030b80c0c03a448417040030710922040d001d101b4507184c00c400c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 999236969 1250 999235719 999235751
    0x20903070b092d1c081306020706020a0c06030207030c06050c09030f120a0318060204032d380411120a0c0b0a120e0a021504030f080d 59
    0x980c420700d4107450101e40d0012074140341d4501a001641900039111a64400c14248580205404502d00a2105203603009611000c2c03c411130250f500701c19460344442e00500c89424440041c040c0c800180034034680020028000506000016400701074144481c0c02c0076421030094214050a804100c8402c504d030b000300c2c0c440c0c400daa0054150921259a44443c8007e25150200369121541a40d100c00c5c400c0c4890403140003920b004189601e000b1030f9150b80000c0c080354541e200350025002c036100003000410000305400000101602d034051004526080f29800032070303c04001c020340784610161461038014440c00000c0031030091191004001894594038070b05c1c001c2c08607412035000c0340d5241c51581a10f0f012880b407030400805402440d85c400c0c1c03907855a4943c9a54441e4100c1c258000c244148003600820742c504c50011155002c024452503074480e2070b03075200e00c030000780c3c000c541c050000d002c40c45984040314103903900700125401140c0030f955030522552089121000290b41c9030610801c4480c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 999238219 1250 999236969 999236983
    0x30c090b0d1b020d0e0904020f120c0a14090a0509010213090b0a090e1005060409021e010e04150e0604060305070e07090e060a0506070c08071e08030a0e0d0501020903 73
    0x351040002d21080a081e00c007400c420a103500400e640c400954840740b83da003c00203211040055030060036544481c408205050000c0c80c00640c444940d0310301890a000008485a09240c100c0c2c810030f403281c1c2d451714400004d0500703c8498100c01c1d04030002d1030316100c0d908902d4110360340310001490003d1402c242c04507a078082d00206400d54842090344101e1414128038009481c101b201048007004114601c0c3e55003016990850620351690002441030343e0310741c0192103d68001d8250070507000c3c0108131504c0c0346618003e40707000c00c000e000100814100b51103884a00306114614040b82030805011100408c001400b43d6482034035000c0110020780213003c0e401c0244030805070700c041c50074084009098141345800501074126200d0800c905961140300d584100d500595140369980f0440c00c002c0020301c41c40c0c1000006204000b4000307074144d07040d00d001c40400300c3d410464210507191080d0301c0c3c40e0301c0355041c1c01c000524102c014040301e241110700004c0a911038400145011039681c003090410b04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 999239469 1250 999238219 999238237
    0xd120203072d12090914060112052202120f0c0901120209010909061805030406030b03060402181801060609050f06030405120915070f0c24030c090b 65
    0x804252a01007010300345030352407008041c014034641004881070b05402000ca2000c0600103690707680c0e98405084c01a03032a64040c2038050b0041c084c8111040001107079050544207540042d0b00c621040c11901124417810340910708086800c00c100c055014141e203010724192042ea400581c0032065801d6501c10001d141d003919061003d004124401e104119140710140c2c0500c00c6010120720480041e55002c2c1c49034192044048006681040c90825000030042b0355070319000483c0014911061040c000003410840341c4540e401d0101c018400140b40d15043c0590b8000e401505c00d0550040e80720740b01e0080c9030300c040ea080129086042c2007141c01c1c00c0d15a142d00c910046030301c0345024071007420301d4400c02c5540305d8292901881c6082590b0f901d03580c0c1d0100a4254040c07040481c03038008076070315810300041020700c00c0c10b0716403500e40a040600442a80100031030707201c2c091190000e030b641c548400c00400841d011100f804c0e50540c80100364040c0080312100410003260707503404180c1c3c0074000c0142003804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 999240719 1250 999239469 999239473
    0xa090b0945010e01050108040c030b190e070519140d21080912040602153c13080d0b1813030305070302040807032303030f22120e0d1202 60
    0x2d40b4018441078010011707080f4a0400030850200800300d101d2001c00782c201c03640103040c81110b540b0b800f04410b06040c1d807800f80c10854240410501d0714400026480107480e411101d0340c0d02d03030b51030191200481146104003010003201d041040143e01e410305175155414005d80c025104815114200c81c007400c00c044140c4003040d080802e000c01c0513000c1100d00804600404154541070802c01c02a5440300d0900313003055182204000140c01c041d824021140ca59a200341c030380d201048041c2181c3d040741080e42d03001580d54801001030160341340180003004150300220b996141442440300700c406402d5180c0c2c00c0e0340124400001900c00d401d1001c286116020050706138266544a1030b0050985001500c0786003014014002030026400110311502243e9100700035840104403100f6428032061030f04414820b07030001000700b203070b1070a4480310760b40304030800624210b01d400307003c010300c0c00d46c10007070001303405046035543c03200e102030042d400407054000086c6280d0b51050560f81d280c22625224070042c00607 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 999241969 1250 999240719 999240721
    0x1c0809060a1a042c0304230d0f051f0c02061b040e040309030b0403030203070f03090b180709020f040303090b0408060a0b04090f03020d020106090b030c0411120c0a090b0945 76
    0x12003002c0c47d018001001c044020784a00c51031100190a815000e000505050f17074800380d00d42040020000800c060b5000203222014240ca429000001c2c58065200c4002d40900c40004100e090040107140800040f03030b078028103241c14003800070f124000041c412010f02ca600c100c0032001c1032904049911961180d60701607038038980740c14014021070a03c03166070141403e0240074400a42d02040d040e912858050140c0e1751249800941351400005034405035110b480021800501b524540007030080d203000743c441c02c2d00c0c980d0392140b007003040c842d510903640c882d0405000300c2c91a032000e411108442d0301c028000b141503c165140e041d40e000341c00000b01d0150b1300031078103104c56940a0084078014100404200520160800400c0d240d00709505410710540d69018003030f11104990003500d800386144107465000e450807280c4071050760700c0030700840e0200c6d940003000110200b0f01021142078031009050406440102e1502604240c25185206180c603202d07104803444a0740109110207a0003803e40400c01c3d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 999243219 1250 999241969 999241979
    0x1d0a060207150e0a0605060d14070302091003080910050702030d0210060801020403320a1b0e061309021f030f060801020304080f0703021c0809060a1a042c0304 70
    0x10b504001855035003500d0a01c820035102d540e002c00c502090702d4014001156a03541c01c400101d01d0707c22843c0c01400040c1c14119103000c9440016081c00745c0f0310030f4407080865100c400c2d640f42c00c098a488014140ea00801004010341010b0406060380b040c98144682001c142d540000d0601c01008070820059000e424099000c15540c0101002000c0100003145400d042d034842c4074110034814005618088a21584c1a0b00c44800c50b5190390100362006458007805545000d803038044504c408600d0000920001140c0c200034040ca440c0100710060450083d00c4800b10000302a1401c51400d81c1c0c0114801e90094212801000b2107070819420f590001c1e0320400d5035541011035889800034859a80705004101c00955013004a0f65130320b864016a40e08c44201340342c22450540c101414035000c500890190041d01d0b0803103106402200303400e055407000d6851520040445191304000000c6449030b583c01c140318101039000b40f180c1c10b183e8040302146d2500076200b12000407680d0448509510004003008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 999244469 1250 999243219 999243233
    0xf06150905071215060f0c02150a0c1103160e0a090501020d06051e060f180a090507020d02060c03070507110301110421080405040f140403050301060207050307181d0a060207 76
    0x482d800710305556403540c180400104a070810591400c1801a847c40301c1b4150358408000310000302020021680c1ea001c066001000545815800c031340010b4080501c41040c6070120b8078812410346451202c5140b85082142c040c4c50303401414480909079140011000f08100780010100b00f58603d034041911071806007404080141c102e00340d204408403400c1811955510b008a400e00307030380600200d8070f8443c4280d0391400003c2800f481035020b003a0500010b80e281883e00130a118141c95002e980d2040102d44090340c40e100200d45420f40c8050800009080a008401400340d8900400740c040b800403201c40840d084440e8003d0b4207903030030f502050800c8a00256028407031501000f8100010301451591a50300502035805114820f03134030f4002a488111ba240e01800501c0c18802c0300318030700e052500700174246502c00c0c0543c0340140155080801c59007070015082c4101c54420b1444850001810b0500c0d00a04443c4c40c4072020303050f12440180f00c513000700b040e100710500405005a450025150400d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 999245719 1250 999244469 999244481
    0x1209060e0d020c03070b0d021c0609151d07140d05101511061b090301051302030c0406080a0210030b030708031c0b130c0302130305160b070f061509050712 68
    0x4c0c4294002c440a0003c0304901d410f81da601e090800000d40c6038140c10302c407080c000400040007a082d9207050340014201e206034000c1e071100c03076a2076441429a900c2e1540081151003080301700c0003201003c03004c6a81d45214002107048201010562414400301496880c1990401c3d945050340d0070b0f6010302032220b036102e91640e480207069030910710800e40400c01c4264980100a0100c00302d08900c6042880c500343c1d400484009080007002000a440c2c1400d60050446141d20300343d000b4440c4c501303800407500300f500c690300548200384018203c13040079a0800800156410102c0d08040d2150010701280e242049004050000b00e0040e60f11007100004401c00d076a001503100e04001c1c02c004100000f5203c041000d003c010b14001c000c10f91043c1003505801a1045280502c05514560f100100f40480881c0c2412808400d1136480b0707085540320300202450046800242c031031340c102400303000010740a03401749641c280c140d100000c6840e52241403c00300e0b94121458008a071065100d2444104648201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 999246969 1250 999245719 999245743
    0xb0f03040512161e060227030601050109030b0c040b070807061b0503040308090f10060603140103030e060703030605060f030403020f060f01090b0607020a080703301209060e0d02 78
    0x1c1d0512001e81d00540a550f81504080c00d03111000410603124803800b004010040d030040c6055540e101900c5030315100825030310844010800c002d4100600740b40208000d03040b554160341d2001c80a0464542c1030f50040040d18000f82490100000035108503000040d002c2140a0304240f9124241410407000382c480041e0001c006884000350341c9801c68001050307940150300740c680901d455070b0390410f1524061201144040310f100e003001c1e26030b07110815080001562140d58042c0300c0d880007500e003010b1155013800b000300428820603220141c1d08041c5e000e0580d0601900d004100950340c1c130041890f42c3d0059489600383e4100000308010b050f0100400000144400020162407400840280700044107000e042000c07a12500c481c110b07940c1d41000da40205070014074108905644413109542d6112502c412100444840034480248841d003000781080b140c20744898101095008080794140300c18545440740d80d545801c08800b05001e0b100c0c1c200c2d80309210000748811100e0b134002901d00141b403050707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 999248219 1250 999246969 999247003
    0xb070f17040804062625140403020f060f270616030503073e0313050112020f0c1f02130905060f0d260702010203220b0f030405 56
    0x180000500d0880450b000c4484c10b26041d181080c007500b040b040c01034032880d40e5101e80ca00340b0500905030388584c0d158195404070f0b40146008409070304142d41e09481d401c10101110001d00c400c00140c00c10852103200175100400b100e18249031524051119000255000c1380b400420b030b034680702142480441046024201d81c0c050401d0400c0301491905514044010700704175000c404140028011040842007107154680b6800c1c82c4000f220f4040f0346188400d014410310326400d0011280706010040710840100412000c1085091400544020440741c180c584440d50800c034048a0204107000742c00301c070035800050070b02503140b44d1000710307800e0300c59000030b56403441040303058441c44840d03150324210b401c4124003250399030312040040d00c5210b110030002c2d00b2841840541c0304101d10659004003038240310709850400e0148400140040c002c541000340541c2c0100b200c5400310800080981da41001d1141c040006074540d0300015660300800d000c02024140442840308000042c40101010b50903030392 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 999249469 1250 999248219 999248221
    0xa15060507150905070801060b0c0c090f131a0c090906030303010b0702150c06090d030c0f2109140d170408031b09062b0c140901020a0b070f17 63
    0x100d08040100b40d10001d00c007142c1c0d072044401003200900980c0000c0a500f0003c001540e0b44040034011a441104489032070f01824440400f1072800c5c12016000d144a01c032518880d54034011607035120702810800780d03259200514a000719502401509101d11a07203020365840e8900c4105006c0c140c007014014910036013003400184295250b820584a1040d011124084018540401e51400d4894011310340e40710300921003001150079000801076284030841d5020001103110f45402c0781c0300504220b03c0b03000905c00f21503a00320420703001c81c02802c46840420009012038682c1d0f4040500a490304c6d6003079590051580c01e14130940154049280c04044045100a0b1a0655612000d44002441400d01c0582d10750348440700c00c1c035902502e038226009803143c0c0d940c0c555000c80344564001c05103403c108003d00103030411004158080c00340e45600c0b544500840b90075004000829810100c010386c11031094024290105100c0785103640910301c41e444801441d030a03284c000f03150f04c0c402c200d00c1001481c020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 999250719 1250 999249469 999249473
    0x11a09072a0c050a0f0e070507020102030a0e0117070f091211040c200c1e0307062304030605010602010501060f09140d02030f0c0108090106081518060a15060507 71
    0x1500c194501052201464014080c980122480302c240c010b02d8001d484c0080201d540700c1c135010b410040e154078441d00101507450788802c071202c0c4103858000f40160400c0c8500b230384250140e4010482d9141c14100b1000c1001e0000d603130180524201c4608000804540b01025101d03004000301d005400c80321515000c102003900c59510031050070202501803035030380e00301c40c00c003c1c824810711000200c0c0202c3c0360f9011145005481e603440030901c003148190b0710030030341001645030100307043c40d1114054060310f0a02d10b040d005440406030403252005103c00c06061030380da95041801040507522488001403076504007040242100c2050300040180301600030750140c00c80d0803038841c504a6080180010608540c40c01245181100401c0207400d44100300010040c03203408640804080c0c403e1380ca0070b43c00c3d5544200d55003a20101d21840315a600407850f03000d0b017083c102c8029075200700d00103c2030000307007104410203180a0341200d030100304030307030f644a4800e0141d04010f5001c000d01e9685803880c2480225 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 999251969 1250 999250719 999250757
    0xb092b0c090c1418030d020705010e0103090b0604150b0f04080705030d0507060209060d06060e100504180b0f06031e010b040605250501020f0703200a0b070e03011a0907 74
    0xf0700ba00758802030042400340384c000f80f00e0107442109034040d00340d507401482200065912040d81c0900c03400b00d41900200a5603500c244651116241c020010040c0340e2140c00a00c002888000c0081040402c0d20780080b5120b1805001046000c520154180d5130301e1a180c101c0e0f040c87d0305900014401c1c0c10170030b4a2201a03078040195141c09401520041e502d60490000460310300c5142c0c403030000f160030464000b43c80764001c9403100c0d08540070b5070540042180024121407503c0395004414100030055500c00403083c180d4000c01a07820058010001e444d04440040c0380758004480800802662018203014845040c40d0710b801041d000c0c00d46400c082c1081c1014103030b8000e110112402c00020f404074407c001e04000c1219180b60800000c643d2144550341d5130070640d2100c1c505401242c9442d80240c00221546200d02c040513080780036228241042d40c401280c80d6004c0c0c2010200302e4021641c103103643d028070070014180c0042048401c3c00c075050060250500c0002c03c034109000c009151110120b6034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 999253219 1250 999251969 999251987
    0x1b0c020307050a1208030a0605190602011b0f110c36070804140a140115050111030327120406031a031e070b0d06061701030c0b092b0c090c 61
    0x80017200c5601da030f0f81c03000b005000b41403d0340300e181d001052038805041040c9105070300040d108141d000f40705c0d560304d004910b07030701c08000f48280780001c41c280e52100e54540300c0c00c803110b062000f1100f41c83c480705c2c209000460a9080501c011110105c03201945101000c2c80c5a8807403400701242840c000d45070124000c1c0c11140004e00181110105070b1811030a108148000c076009640054501601c0c00c041300000d009280d400220540c00c1c2e400d6031302003603540c0540c41c00c10500180f10000c604e15a64a090704285c074104500506c1d5102c0c8a0440a2007102d0602503840c01d940b04c2221180c0f00c62610100030241c50a011900603034551409071b442194802254603019640d4100c40b25110000000c240c0e8500034040c3d000c19650301c0b000c207450420045c3d076041507040f102075944040405240b400201040b08003840700400701382c9401020442c1516440141c406000014440006034030200a080c120065554034000508180c43d204070420600e00c1440e0042d00919200300400040b450010b851440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 999254469 1250 999253219 999253223
    0x170f210a050c010c03050a0e03042337060311070b06061308010e060a060e0f09010b04050903030615090319060b040903050318010c0c02010c061b0c020307050a12 71
    0x1400a85405224001d408503280c1c40900380c000c00290180c0c110040003040156180c50740503040803081c9020420000659051782c0964901804000e0019000c080307050211803d1a0450003c0600b00c031010882020701d41c21908115070342410801c1c5804210103e080c0740c0050003818640360070a801c4105d41400e8865840c0d020380405140c1d180c02c030020302c150088800e140c080390070345040800c4510064006014074801103080b11031540b200804c003420f070340f1030b400345c0d09281c00903200041032014034001c8250000640c200025007020342c04c000c503045c0c030407c5601e1100c99100205021041c00c207154031151441020f009942080100d5002030f455448810f024207460350003180010500ca2141e10046010030010006c10080d038440c41c0203491500100c501001c90a40c00b4000c4c0b035151810300401754003045036076a030302450b03100d40d005680c202006101540e1455036503461180582406500c01c001c40c0aa8945c0c00103560244101443e114080d00314a00070f0f02c0c052070070010302c0007982201004170b03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 999255719 1250 999254469 999254533
    0x40b07140c060301180e0d0f1b0b01030c0512150c0a030f02190215040309170102130602100b030c0d0b060d0f060b12010b0904120e0604170f 62
    0xc801203000d20703001401500c2030348400004000101801e40d01c05c1401000c505101c203000b089112500b00e51038880c030300d2850000c035640d0543c9221182c0b19120081d40030300046c14403d840510342d100d04210b01e4098004981c11500c2440c180003e18002d0400c1c80769001080003408005014144211315080150088014200109648103c7c500a4100311403c0c480705404540b11009c4182c0d01d05403008060303000c070250180501c01c3c100c1d95107a040c281d02c10303505500c601c441d10345400140e40103845a500c810f400381d5401c0c010f400e031381c02c01201c00d00d00506040e4000c11783e040208102404403a03509040c4c51007a8011524000a51140c441204400b038002c0d0b411380ca02d559001c04150b110303804000044c11100200249010003619907c034402d0114103807141e09218807240070030303400c903001c02c3e019a901ca14418000f0f00041c1e20303460200489c104d03a00d402d4001c0c481003400701c0c0464010b5000105403110406045000d003000b007042c5481c03d44d0100050642d424400c01076450803a80c0007000c000c1c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 999256969 1250 999255719 999255743
    0x80a03021e03040c060f120e010219090803070b070309050a0b04121d0409030507080408060f0a0c080a0c18141f05041e052805090105131521060c0203040b07 69
    0x4900451040740c040ea481032080c000800e2303c940040c001c3d48010148080780000c0c0341110903051081c0e18030003e880c030600040d8540001c40d00c0d100340114004044508164072070140c000040d4050140240251042590404d43e0070f0078075000003107240c000d440380d04115480000c120030386a1400041e4101c8000c1ea00001d132281641400c035050720071008058059800050300154032000010b0091180103030030381c0c110b0903840319003080c000c3d2803044c1c0c500d600050b08000424401c07200c030780c440c1020107460f0410144941d030462083c1c000380d0195200040c903143d0943c680c074142c1080c04081d5a03101030010000031305280e9000281803800346000c2c0300075007132440702c1c98644c1e22202d80780403003e0200240b809003140c12112080112194a5041c54000b06a004000480c0d0070501812070503104c00600300d035541440c0c0e107403000041c1102e0070500d0603100c11300c43c0000c41090ba48803003140e044691000c0040d0303120508210b400d60300721001c0101154003c100030001d40711000c00b030741c0c00540e002c3c101543ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 999258219 1250 999256969 999256997
    0x7201e01050a270e100909030e1e10020a170301060801210602030c0c0f0a02010801140301090605010b130e070e010503091015050f010503040c0b1303080a03021e03040c06 75
    0x7000c105500c0f034200040c54010045503080d26940003500ca40c201c4c40914400540b01e40117841a500710240080120b00820140f140c0751404500398a0402520044101c15400c0100001d07003841c0c01c9240c11001d80c00c00d00d0041e05019070096881c0c0780982d40070f081440c1d54980003000340004014452081581140b03d92031000f081a0741001040507003001c425910782c00d1120340c0303818980c40740081103543e21a2100700440f15501240307920900745c058507004030581c43e1401020803181810311103981554cc0e0704081000036540e22845001e40700da23100c40361b102e09040700c02c8004001c0b55000300489091000401405950084107402c10100a1902507241e840c0c0080052400011180355032030f882c1008030b0505552180114403040301e000b180e070811010320000042d1498842583c0c080d0030343d05070709814080128804020305580b599041c602c0c451999940f101d4140d50030110a030b00000e034000409a41e640f01300002130000d1100748084518600302a5103d0340c00005034480c48080c024804803480c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 999259469 1250 999258219 999258257
    0x6090e0c090c0703080c270f180601120915060603060b04080a1b03050d1e051c090201020f03040603020415030203160e150d0207140c13020f07201e01050a 68
    0x101c071100c41c070344808042c04422141d0010340fa0f00d0f102d0059180704150350962410862211407a0750710070109c02691030343d0303004403941c40313200b07105211039a01c4a450000007403c3e600100c040d662800400076009042601c000d0640303155174029040d0b60018401444030070808903501c1070003540301102ca2100d100a1082c40c506203000d5101400b01e01410032080903041d00112900e8941182d07035810411860043c400761800c0c01081000d110030710b0001490b041d19520fa40c4200206401401214900c3c034058031643c0c610303809904110002600031804005106a000518601c0e04c800c0c04e040d0304610301003601041120341255940304200d40c2c445c040401303840b0f1440070440082000b00455481b0607005902002e903108280440b900202031f090105181c00124010a054000030028040c0444141502c80a500403400c91609008200010070006402224044454119803049a100c83c00c1c10b0810001d8585901d2801000031650100709150f039001045a402202904082400340f1340c201c1408 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 999260719 1250 999259469 999259477
    0x1240e071b0f05030307020f0601081b12031c06050904031209020a090e011e05010815070210050103030c0b100303210603150603020907090f18020d06090e0c090c0703080c 75
    0x24040c00c01c0c040c1090b080c00310100065120720002d4003150780d440320082c03074540c0d614024411981d0740e40185180d09049441c071181c105164000800703113110303d0740c0700003d5811a40485500014231b022200c0501500b0030a001703280041c1012a841071070be103802d44010f01a1441c11815180c1142c1e251003a030215a50110010054a4102d00401600e5040481c1c3e40c020004582c00740c0c090002c0041c14245860380703000d9903068404413406000c1c2c0c40fa11a401c0000d041d8003904140075030068101410020540344151070085020f0303581c4456000480c107140e221a00040d15039081c0e0404002c003800402d80007200710b440480c00e680c412104480c410020801046544c2004149c0e20b81071400a0f40703200d080d0810310650707000b220001016250200c00340d40f01d08013031141c050140c2049004001e4928040310311040d0031140c0102500c1c0036520006007003180c0d003d8001140032542c1c0c4241400c8072808001010000c007050341d41d005541040c01000540b03010b4080000c080141040000d8100303541c050540d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 999261969 1250 999260719 999260723
    0x1501030209040e07090501060315050a060c0c030512090108090f0d0e0a051c0506060108131e1a040c05040204030305040e06150304050705011e1b020f1201240e071b 72
    0x207150b0080d185c40101014050078410600000d08247c280640b5004011207201240c00040ca80e81d410351800d84291020001e82400f91524036581400201150003480300c1e810700c4038075070110703595005601c00161414401600721241c0340d00241d100c1c5402d140000b66454510110302b021400658200000740407036019400031500004080e81082c00d003da645c07110324000384502e05465155451000440e22000f0803515040401504403031500072842e5042961a40403514650f00b22010366512141c0108400802e500110300c84942008240501940714501030074046505500d0305246407801443c50056001d00140c1d1071091002c40c08580d40d0f100640d40c15840c4460703c40e100d280c2414079a07100c00e40c610550380483d20000c4410720503041d4482403101445152070300901c94021040c00e1070042085003003280c20008001d91300005a42e02500181d981d0400720020542d0b4607101550404010203606110614034000c0d0144202040c40300c80560010091a0001e510510101d117502c0342001b10f500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 999263219 1250 999261969 999261973
    0x61203120f14041101030207020904030810120b09010501060801080a06113001090606091205010b1306230a211b0819050304050103230106180e1501030209040e 70
    0x2c1045030841e2001000e00c118040d0010324201030b04c0d0300054003a4441c4486c001e5022603001c1c0042d00080c00381c0c0740e45070428035000f040203407582c07150200750861409010a45042400004002a204090081a0242000d840c042c0c5155151402e01541d1303160700c5000408150f180da43c1c14420750304c16405e171000b4180c000c642c0e160f00070b1489909440c1070045240d001000c504100040307585800f9010301000c5030031a90b45c8100d040c0c1781054048040411400c112001d540720488020b044e40e551030100741c4d40340d408400082061424040d180d0400c00c0307903141d440f00c00169864a4981e078558094604075680c00300d4680b80200700840ba015402c41300c00707005100d84124a00e108503034401d2444c12090f190600100c8682c0170140e171554114600d050001401c5a1040000707019039413198001c030540c1c00c00d2043c5d030304915502000c1007400440c260480380018100001140380a00c401a000380100001c6918000c503090940c0040c1545050145045c107041c0c00003551191501c5a50001e0030003d07a03202 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 999264469 1250 999263219 999263231
    0xa0f050705150906010e070c02010e031501091d0114151c03050316030902150906041d090c01140405041e020c0d03111c05100308071113061203120f 65
    0x4403800c01d20b2400d6410526600c1000f00225040c02c0d003100060046c442900c514401031903950044810000c18420590540140510070b51101007070360b28140a0304259401003148503404204ea00c0e1041141c109420396070414440b08203c03002c40000940008440c00780c02903020b00320780410144440c030901d402c4034540c060000c40605903c6000355000c0c10b880d603c010100030781a00e0413000d490301d038600650300c139500e240003184040e40d0000034070000001905140c1000e549281074403684410351a00320400400340b04010508809000304011004242080310f191501c42e00c4101c2280110b0144a0103103560f0403c00300c0c211007001f00132071130413031100382503581e060b000d40129212210151072001090502d0101018500700c0c0065030410104581e100285a51818151000d810040c248902c03804d00d900001c00891040002008094002c030907414445030b410b400c0c0b064803c294800c0404844c50800706021801025000356103440e010310380400001c080701c205100030080c00d900f0000003407600d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 999265719 1250 999264469 999264493
    0x30503030609010f0302030c280602030c1c1d0303190c050d080903070305031938181b03010f241e031404060212090c03030a0f050705 59
    0x20045101e08010740e92018144da83d00312800c080300340f42c04020b5140e0441c2403022a94186100e501014529200d5841c40041d00840842d082040e1a08a00d005800024042d0200e050030072400e00c0c03c001d00620b1400d80c0ba14540020100c0704120301c2841c0b116184060161207540030026550401c0c070b4001044060911180d01411012010b4001c590340d0244103d1841e105000352490740c480d0300c520000c0c6141200c599412102a8002403405c04101e201200407001f6014601c1840b1f034090702e100d07410740c2015000180307048014100d00301c3c12140f81c2c80c14010a454499030981c0250715030210200d401c03901c03011040c0d040c11000b0844a5510301c1e011000090103a100301e45802140c1211042c81c1000882035288081c0361803410f90340003c2030002c01c10030646034030980401603240d1685030011355030501c128200b40d10007040d10265055030300450009406114181c440c0e40020601005040c010007003c007185e16400340c4a10728050140d0a42d0f02c09a00307020754120f400031079000c0141c030700030300c040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 999266969 1250 999265719 999265723
    0x30c060c090405090705011b0c150503070801080304030f0609051009080a030e010b0a12080d0c21140403030b0f18010312050a0207030b0a020d0212060310091e050106050a0305 77
    0x4074680502c120704000100311030340c2011407000162403061307458450a010420415015540c0d00b9000c40d065180c40c0310015103880c00da0718043c0417a119a451690342d0034480380052000c081a013081c00560400c110400025150640d880c4000358041381c042802d00c81b50030058104898441c04000c02401c040c4000100102c41c80107154030525034504000035501d411300306080302c81601d0744c140c015180c110140218192110900c1c0044e2080c58481d207001d0f582d0503a0801d80d644810400d0103d042c0d50107110700c2d581070000216021038025030030096083c05035519162000d015101405065888089071110746034018103204c2c031080544107074510f002443c650401d0300000d100c155070740407025140e004620310660440702c030940c896000741a054110b0302d440c645c50201070b01030494107508200300c0915000c4c3e80041e24040c1782c100f00c0c000181c50801c00b8035007420104408000e8803881c0440c031100090000b03c80303c00e400b84402401040402c035141060050540381c2043d40c0c403c140040000c100080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 999268219 1250 999266969 999266977
    0xf0f031512030c021207030b040f0602040503030c100c08070c11120706090e070c0b07050a020c0907020a11010f02100213050303030906010f0b120f040302100e03041a03010620030c060c 81
    0x1300b0744041320707a494409139140e2115854040107010322052008180407420300d40b020504d0b1800703a8001443c080c0d4034000207186078803040518000741c00c100210740042e03d15220300900e42c9010704040ca01480d110b400185000d5400c0c4008022002d02000c0440544904040d882c030398000c1e070119002c454507a0000782c090030144c03045d0032034004840f0004501c00d02c1400440c040da9480440720089450b2070906440c82e801000500c02140300b888080c0c1e001d991408419405400d03141c0241c512180300381030801c000e24190491505101d2484001d44070305600180b51003004100f010010780b2200d08041c10241c911f25030b4042541480003005004043c540843e80f03604858184080d441840c2e541c40082c90381d070082080300100c030090600082c0050740c480322502d511620910540780c085401e400e001c011610b0010318030401d0760010a041c00100b5041203007110044414400d030341958500307079004001e0b540b402502e00c4003042440a81c1004038041080e11034031580d0405654203881c01410320707040b81d00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 999269469 1250 999268219 999268223
    0x2f03041109240604050109120503120a05220c230d030306051903031707030e0703060501090b0904050d14070b07081501050909010306020f070606180501060f0f031512030c 75
    0x180c418508451500404450446030180c687d01701d820302d08130040c1010342c0040016103150004000c054003485000c07038003a210f541403000010313441c1040e10700c0d1315031106d0201101c502e0aa403a01c601020501141c4000222751058034100048007454400c02c1888888403200b03038100690000102c205901500f00c2c90a031442900e80c5070152002403454031004210b481302a0206004d108074000e04201841c0d2981d03c8a401d04000c42d00144d80414186400000e50055510a90302c40c01803128908a011300034580d6800c0360340750440d0038140c0340c00362140e40c9140348100340016128110b00c1610340c0d50540f0750b00d80c0c0014083c0c0d80c0e03161181015102e000d0803260700c0c0504402c0f01c0503075050342c00b82d4144c81c020307540901568016825680c4610095015000240c4020000d10908001610b5030182070007514403442803400060000c0040c10940d6010b0b040a418080000d05000e80198030400c0b001c0340d40342c40d1a0120300041e00810b03204440308a9044485ca03416440300c248145904840c0d1200c1c818 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 999270719 1250 999269469 999269521
    0x515040801050903160602030c0f180405010f0e22080c060f0a0204060e0d05121318050906160306030b0106180806160333092f03041109 60
    0x3030389060b0980c0d2030740304140720003a440d645e0b40c5ca4036011651907030140d50300021005080b85031071101c15001c4016000840c24442c103103160b140104140c14680a15401000e40203c1c0c41c1c4543d0a1901003200384200500c030929280324100c510701d926486007a440809a04612090340c1c5883c5d180440380c0340c960403036900026040c09000f2450b0394907a07100b120201c45250743e400070150b00030000c00c030b509401c42000740c64074850800300340041910100104000c80c0d440c4800c4001c00d14007041c040303049030240804500249130504000c0c0c55400451039542c0125610b152000022021806500a00e1190406400c5480103000402c10b0307038004102030303040c0310300d0030403020010703034a48015680300d404840c042ca281080b1602d4542d942d010380c208551203100c1c130444515030b00d1901c0c85280c040e52014042a540041840c1c10030901c0c10324890b000c1030380407140038030455051840c0c500c446250141d151022004000000034184030749ca407200076600e0f1006211259608211002c8850510150035943d842d0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 999271969 1250 999270719 999270721
    0x15080402130504051006140f240408010b030f0a05071206020d050a02030405011d0c13020c0d091a04060206040b060f030114060102100e0c060304080c0105070207090605040c0e060310051504080105 86
    0x104040c41050794810310024242d0b0041c0c0401410701c20b000407281c000c5201c1115200301034502c00400004ac1011340a00070000030020710700005c0610705401c03403850f9840c6401000741d280c0815408540c0310203460301e0070406110100189440c0000784500d0030700c844d200c0e15202c207000c003100260300110b010700c1c0030308000e000044040140410f030750b00c503210000647d40a40c07021411402e0110f0160004080317807500600b444650a05c0c18100080107002600144201034140308280310b200a1644003000c20175068106418810040c2d44d5540c0608003600102c2180005021035992001c107020341c44001d4028002003c440040000307044065503c1e60250240709140d040043c10f92042d104013100d464014184101c8440c288540c03940064410b50300c01e9420002031030086400d008847c0070307001d03c2d030080c403400c0c1c40c0c0030f0380d030003162425040a0320803803c0902c488400c41d4455a0301c01c8040c030442d2070603507a8031003070b40180302c00310280e21694200c80400c91000c8280c082030060000c481c0c181000f0b01517 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 999273219 1250 999271969 999271979
    0x10b040f0b033a2a03091403100f090b040c06180b09300a060b0d240e120901030f02032703040801110409230705090109330203030115080402130504051006 68
    0x1187c0380d0482c0094250b40904070701709648205810204031034000f6940040c0c0d44a80e52504025118112400d65040ca1400020444e80e58018420411040c40c0022010140c0c248044102c1a01c9004503640c41250600c417520402e0040c95151140c51030300d41000c411004111100300e07250002549e060b12110302e008500841c81c1048501c3d000e03601d80c4500234046024031400396109082e1050041c20900c0e40e201d070551064002017040620008010f00c4990721904064001400d031180e44c1c808816850040c0140032035500e6103032180508030000c17083c0800c0d901d10f010405145029581c00080290f003030040c01c18604811034014819100700d40001d10040340626035112601c2c4020700c0e4284400141000900e0551190300640141c090500d0300016541d80d450440001403503031124645821404821000c0c00b1403603111b8600041c0d180e00181d8210340c0352881120708042141e2020051000c004c0c006011965128031171440c2d822200403c1180d41024200f80350703280554103503850114a0240c010031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 999274469 1250 999273219 999273239
    0x2004060e16050a090923040309080c03070e06010f3b030c0a0605070f020301060b0a02011802030d032f0909280b03010b040f0b033a2a0309 61
    0xd1400c50700c0b40b02132586070081c1100148406240080c1200c8018601102c980c04140803e00850103540da0b008603a04000c8480d0400c0c0c160f1300b003240310303910809007006540c80d130b1207030f007a80602d00b401c00701d80c90125444107030f07000341408085003a007240d40c114011120320070111072030000040348a66164400c500050581e607400d02c1215039444400d8070010400248610f0051804070710170395881c0da15641d5035020a0075100ca07500414034036800880c800f000c6030760912a1414080141c00d807403010304426000b0940f94030100601404164841c040040820700041c0720344803043c0b0740c034260b141c41c1c540351403028000e82041041f5482441200081402040b800c81d10700b1340ca1040c0b40700c0f190b03500c2004c80302600620184401d10f40554940709848902d607100d00c210305540c12031180101c0c0700d004a0703003010704181c0d080c1d400d111441c225081110404241082c8d40380d4810b4124400843c0d130403215002e40e550010021a41e141240c0c00140402da12980b60032148828440c2e1103428030310351654500d00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 999275719 1250 999274469 999274477
    0x308070f05070b0c0c030f040303022a0a090c02031e2109030904020d060312120605061e0c0f0a030203040612020403350d0506130b0d2004060e1605 65
    0x14041c0c05083c8003090000d48a4401007030202d41000444e4075005d1100c40e5030340240c0065100341d0258100d000c6c024111003900f41100742d070100b9a0001503080303110000107040f1000c0b5004030b0030307080c0e40c8466510302a4002c004840400c11118408a19140c0f07001551142d0781c050000c00040f4210405070340c2001d8210b4005038050b18040c0f0145080604103c01c0c40000c2d0840c0c0d0010710600c1e221840000481c001c8403c0244072101d0381c0d541c0340314442400b41001a215241d00041c090030042041ca12021400d10070381684019400c00199240c02c441c62413807600c550800309000310b0280403108020190004003d10440e03046499144109281401c0300c4200d014512000c1c000f030200103c404c1084001038180c5500003010b0308003108140d0f603180400030a80082894940c0709a44605001e503030301d8200d03002c408280f4403507814807111094401182c020442e14400401e6442eaa074852501030b50540442c859038400548200b0090ba03445200405110040e140092460b040c11520713400148980c04075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 999276969 1250 999275719 999275723
    0x100e0606090403230c0606010332040501020f1204110103230403091e06030605100c1e06110d0506030d08270a03020303040b0a020304051c0c0f0308070f0507 69
    0x9070441c0d4860310300341d400700e07180d1200c0c56130b00310361140b8440041c9400c006442040d4895004204a14244001504640f003a400c0100090400343d002c208440409241c000c0c0300c015040b0b0052141c0380c924145001e8007488030114441400807030240401c84421145621850081754100c007281442c04c0107500302d540c11240b06840045000e07840070b40d100403a501c41e80091003440c1c042c00d03440e543c4120388500800c4d050700114200c944801048480d07810b0150101030901200c001c220307078540340d001600c5d400310810010141988240c560f410401c82c100c0c41c00e0b08580008052007118103002c0501c2103584966803801d1100c0ca401c021070014203000901075004011512625822744070189204e61003d005040210300c40c224032102141484144000c6240520940096440f81420301c0e0140009000038004186148180700700004a45c000400e0355103170001c02c0b0030a60121a414080341c054021020207030031548114501020076502c994214402c010a550780c84d00f8070817540b0f0440d154031030740d500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 999278219 1250 999276969 999276979
    0xc090302060901050d05040804090e03030f01060c080705011a090c031306050a0b060c0a110d17070f02041b030501150c06050702030405030a0602040501021e03120a020409020705100e0606 82
    0x41400103040800c01400c9418050403c0b030b003000860201c0030260392044800300c44401000c5001c2000041e00d028000324985080065800c5d0310b00301036020302c803610501c034800400030204501414424090222031209130040028001d48840652241c01c072a810480741c0d00520030035000a043d44071200c25070b4042c4246180860003400c20345c40e02009020080d111805950b030350170190341652740c2d5400808064001401400d04c181483c2440c8102031412000309001d660785110110014250074500218032a41c0418241c40341c000c0d00b0b10090310503154500035041803400303200c1d801c40d201c0d5a41241c008d030210b0ba000e21541c1e803100f541c1e10b01d0051400c10721020030184c40301c260000e080c03038000940c0102c0d80c0c41101d04003552200041d14002501005075101c980c00281400507590500400c41290240007100c450840c4a8401d180d80b84140842c40c0000807081011804295140d0119002884002415901c4440301d003401500c0e000701c0d030a040d1402e458441c490910800100e03103a442801d0040c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 999279469 1250 999278219 999278237
    0x203101211121e0c03010b09070503190b1203070204290402031905040804060e0a0b0304110121061412060106110c210d08040818400c 59
    0x1d0001d40110340c205002a4050311401e0f10008001101d01515800c00000074482d1816000905084034a41e5480394020034000d001c001c403064210007229044420b0600c844215400c40900c040105008401d0300c2d80b08140c00c5402c2080c910010140030300c00d000f00d40c200a113004011280002c040f04a0b80100007001038011781199142950140d5888949881d140d01014040c010b80c00c200d03001120102d0710312501090612103a588101c000400210590703282d8000d5052210607527150000400060886c3c1c5100c0c0141e0099102d00042c0c041c000100819801c070031030f03074680000070b041d080c000c4503078a444807a003d042c20b24001041344440c0c00c5d40405407500e0703420900111004c032041d4001c03188500c500d0f0fa80a00c99110001040500c004100e0b402c040007041c0e03032100d030070300021440a8003006030b00303010b000209401604842101c100d0155a21040c3c400c4e4001c5505800c010000e0500307000c4200e00d03c0f1100c034007041c40d00c8540d41580941003681690a881c001110307403c03007407c0d0020780014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 999280575 1106 999279469 999279503
    0x1c020901121a0f0a2d1a01030b060a050c070f1211031c2001050a1a0a031106090607020904061a030a0b0c03040615060302031012 57
    0xc1e541880b9428aa0341400348110090b11114016a445142d9a0485d451352104e0711030317080c0300b41c0000c129082c22050b4401401090208181a00c0140030b1485641c46446817250301c0e00010b014500705000700c0f0b004c40326504000649010b91042c1c0c000452683d0445280030010110a100807106c1c00302032810070030400074206100c1c000d9205442c0030000c00b03100e501d04804080a4a0180030000f4030682000501c25517a12030f0503954a48024030000e46083c0d0403504510000104ca11200561700c002d0010101c0c032440040d04e4080040002c0c1241d140c45001003180700001404141004225000180352840681e0100c0304160354078520980300300340d0b06400c00ca1110882c0548142142515200c940c04d030002c1160783c078048001700040410629610017404c0203000c1c1490100d80341c440c0d5001e0001d500598070118210f569441c00203601007819910f40130381e0341c40070b4001c80000358a = true := by decide +kernel

theorem cover : BRFrame.Cov 999100719 999280575 := by
  have h0 := BRFrame.cov_init 999100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 999100719 ≤ n) (h2 : n < 999280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
