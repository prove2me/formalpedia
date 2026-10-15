-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4146
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:42:28.99298+00:00
-- url     : https://prove2.me/submissions/49200efe-d6c0-409d-8833-7fc093d6525e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 745503597 ≤ n < 745683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 745504847 1250 745503597 745503607
    0x6050703050a02030c27030312012c0604150801020a2030040e0115030e060408161106030f04050d0309030c02100e1f18050f040c0c080d02 61
    0x25854400c50b03a000c2d0480c14210705604000b00160b46900c22910544e01c9560340071031614403408812848100c0c2240107040320360310003400c3c10000b1191000d2044c0004d0050f14440c14251142e2401e10704103a200c1d216107030b40150358120403c0000c0a00300418030044510b00c00105071000c1c244005e05204c50152038841d82e40d041c07809641c080740ca414001d800303513070071410030441d5110b4081c00388a0a002070300071005201d020740f16082c00034052980110003910710400001290400080210a45001c0c0d0f64140040c0f0044800c080d60350070700341e0b0000c2402d8020000400280b507284480040b0034072851580101041041c0028611b400580391013503090544014442086820800203196003003605007449900c049840247c40360070b901c24041e024001445107a01d0540c8295502242110006c18905081c6814240745107202040d08810f4085100c10a0040314901e0240010048400003886c1e00e10b1000300c0c0302440054401c2c56114010701a440850a0014401d1b002402082c0e04100700181c43d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 745506097 1250 745504847 745504861
    0x230f010515011701060e1305070c0209130308060103020c01020f04031209080a030206070e0406120f030f090e0a09030302120f060a0504060302090708370c050c0706120f090605 77
    0x6280380d8407245051210094595500d05030b80700d4054112220b605000e000d404044012030104120080d050714041d2400c0d0410000540011244129900a0341c50480303564a0442d078020745402004043c0c0482d2083c800500380350710a0700108010003c5c1e030b002500300695a0059030058005400071600040d20358405506103501415850003480214010003800c9003a440c040e40300e0001512030700130400d0014030340c19030341c4558000000914000140114035412400c0c00d01c1083d003c00c0c003c4000902c0c428501e01980d1082180c142520203a4060102c2d946912101100411050204078280b6409000d10b102e21440300030340c14480c006583c0c500103649422010040b01442d0b035001584514901082400903803140e02c201c95100020b030031b10b0400758a1325540e0140c0c2c50300301c41040585140082d00d9511000c40e40240c010016081e9a05002c60001c41c4c0e0261a20f0041c200308410326400b100f003c00907584201920440c1e80b4078050001919000b00c540c440546514400549003261120b0034402d007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 745507347 1250 745506097 745506121
    0x212030f0a030b030d020705100e0103060e041202010b1017130c150210020f090904050f030a0302090117060d17090303031e1f260303070f08010f060c230f0105 70
    0x290303517024405440140c1c00d1800054030308a09088a10808c054100016240e034020f92142c800f40042c00000b80181ca0f251900085460b0f44400c090019428900c60303509904124100c4880c0c1003581e119000d41c808580b4075660180001001181d001d458004100003207070701c940030f060280232070301d4100c241007403031510282c5480c82c8411108001441048124a103007400815503025403403c5a2105403610340e824024640181806441654080018490102c1c0d41540c01050030304000c1e22030281002400850b0320705494101c501c02c0d002403043c0d16010001d0f000c0d0300d81d2aa400e03001000d0350300b071550450200b85076400494418800b00e4226400040f165a016045980036900800400c1c01002c11185803064180a1242d1540551303032404044080318400001050021014200c0e07441c2d14103200002e20f0b00200a008401041e00308002040b005500c01818042e6100c540752800c9406d000d07502d0682d404003148014a050001c45440c000044080c041f0030300c1c0103903a80020400e41813403102040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 745508597 1250 745507347 745507363
    0x90604091e0b0f1815040201020f0105011e080c031b2d1201022b020d150f050306011d13020d0c06120902031905070e010e090c010509010206040212030f0a030b03 71
    0x700342d04c1684213540c07841800200d125001c0086100c0c05890b44aa02c0140c0c9401c03105040890f055007004c00100f4191640b070946483c04170f01c3c000e00110580d940340504d03101d40c1c20700030700f03905500034a140c50640c0c0382c0d4840440604102500d425240d40b0407001c00c44070212543c41c45054000b4504603403c2a00d41311a5028040c88514000c601d072524020403c540c0300c0116100d10b02c403485102182c01003904682c11781c3c500210680c2d040c02541d807000c01c0000360b08424018030300d81084441c8049080d0500107009416503442c00300500e2003490742c1c550241780d402c00170054100a2003000d20800140c03286030724801c420340b25850240e842401e0801c0a0641c110140b0080804c81c501401c0f034015a400107070b0704116202160b059003c540781c40c1001030501070b03d034028681c0403210380000600311807880c103580e100d4030b0b581094910304141c1e5030045907d4884c2816850050b40040b0229002d440d2080200700c0e042a02c2c0d040f28503000c0103400040e40c5070807000d01c40020036511803a4100390304060105c4a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 745509847 1250 745508597 745508611
    0xc020d121812030c02032508010e0307120507110d23120405060705070f06050415020102070809040234052506140702040f051e06090604091e0b0f 64
    0x4500c142c100040942111480c840c06820800420007003c2951000d000245402c010072207411700b5802d91000c84c03a1010040d1095800340d43c0307403203104100488007100343c840c240d912203c0f038480b103540108211400d400c1000d09031140317202445403142594404034007202e01c601c1964540300840d115041580090003e0048a060750010031000344a4002c0000711400d81d03c089500c43e4480c01c0c5824414034017403180d0403808080405103808206182c0141c0031740704881c1941006054440c4c815012800c2c0d0040d03c1005014010078081d807240e518107134021340301c8840040e0040c000844050b030b801c031a44051103842ccc00c1114105c5c50307007418003000b8464517807142c1c28180c41640817906a94645004403451080314104034a0f07180701803041121200f00da40741a0018000d000c0306214070304030001070000303480c000d485030381548803016104a8894102c1c03290350014020345a5544040034040608410328080740c007100d60403c81c00040380c40b81c0704480a070340103601024030f500d03090a800441180143c0b0030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 745511097 1250 745509847 745509887
    0xf180b0f270a05010e030c07061407111207090213060207150e030f0304150906030b0d030f2304092a1416380a0203070c020d12 56
    0x1164030a1040c8481601c82a06058a001031010350103038108956518010f1055003400a80d03130742904000050269600410b0541d503815560b403000342c4840040403018801004c0c14400d08010490b40644132400007030240c10580e03030150f0701608904006440d04110f100310360104d200b2452150710300070703407000e0170450004092042c01c3c682c5887da451040c641410811400c80b00039912500c1c18441d4607140401e500c112600c8a4480304a028091402d03c100b100260703002e040010034038420301580c0303107100000c1c1080b0340604c2c40e07840c12150084000400024000c82c4007200444584442d8441c00c07415843c401380b5103403800c000341501590a0501c000c17031f4000b40c101002081c1c40d03440044c12103520301414040e0340103002c0141c042080c00340003410381c4000c03140e000b01410700c105500c02a50120486218009503004141e00c110428414140f040409500f6400a000444554001d6070000c4880c1048403d8880a0f40001e070744c4441d1580c01c4644482c0b402c40d000c4007079002001d034507140b00d00c0502 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 745512347 1250 745511097 745511101
    0x507140d030e0c0a0e04020405060a15121b0509090a110a120c020307021f090e0a091122020f09030f030406020705010816030504030c020a1221050406050705010f180b0f 74
    0x20050105d080036101174480d80c1d441001c141c041e500c240d120ac0007000c000120f0054051030b00c0340a402c4120407a007000d8528201200098180e4500402c0b04d40074100361129401c203299030091000d1400004e0850140c0341d070701c60b0700d00000ba801c0c0340500411171403607549280355210302d030074481940d00c108204001c0d540b0a00c0488010f80e40c2088000d40d88455a510242c11a580d500c1290400e140f5413101030310900c1c0b0002d005050115030003484c81540518500c0f40800c4280302803004c54507101c132104100c0600c124040303012911503001880d100030501a480e04140c2141d00080c00c10340c020031000515400000d00300f142030b406019120040c0024240400b0300e00e0400200c0c000307078040c1003022081655a1000508250044d003040d4102e940140560398001c1c0c50b421118400200c1d5074040e200e515031495a072030148440800008104504e541e160b0030070740382a500361040c0d005408112815500c5100c400c0060243d0710842c145404512007100304004036081605100802030800b181d0309070a001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 745513597 1250 745512347 745512359
    0x3040303110d20010b100804021e010f0302070f080c03030709120f020f180a06230f0d0812070206060909240a0204080a051b0109150507140d030e0c0a 66
    0x1201205515898010107042c3c005003246a00505201c1d80507580b2042203072100d0101e81d0700c01d0002d0300c994401d80f40e000b403420400c4510946444e01806403400503520980d010a405d219030041c141040c4100c103220441041550743e40000d400c410001c16035540040200403056910500000c028031090000c904d014409440d4101100800c0e10080d010340a12260903c0d0b50b281c1d5034890041080d484041c2c0043c2c103140c2e200030090031301d80c4910591140d0040107440701d60f21444079a070310020020042d00701005c80400f403140944a07a6000d40c0c2a04041c850040307505074140c0680d01c1003000da400340440380b03804401c0001049001d08202650352000201c10301900e41354034600454444200080c00955030400c1b1035001e071203aa003246000703010740b8042e40104040029800b400011000030000d41444003801190b41c0c40c064468401e00d50228420b070a4051f014400800c0b0080c02060001e6203070300d945806038900800582d5420000303944480c18440c18030140104080350300101d42002000e03103011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 745514847 1250 745513597 745513607
    0xc08100b0d03120c0926010501080304050a090b030307020d03030608061b2b02070303020d1a060f0c0c060309061812220905130b090606060406270803040303110d 71
    0x1251542c81a0790350212030b01d003540036103503e80041c8082269076455440c46c1d514140c40b01000c400744860b179030800b000460305600c003106643c261507014003450801c0b40361103103400281c100c4002c55901400204170200150300e6920001001d06c3c000d8a003c90000d00c1c00f40240e18000340180000c59042240f0140381c0c01410f000100c3c0d030094003840e440c9190f204140081c0c0e141c082e480360509289880024003004050b0141c000d010420015401000b04054078070b0203103203e9851025a9038031520400211080811142c041d00c2400c801d0f50450f9404080e502c045001c60340240c0d01000075602c49402c01c000500e05800707003041000c146002d0242c1d0b0360700c001000d106003d1514000d8901858400c490050420140300000078a072003c414003180c1040c0017030342040245007505070f40d2002c0d4200018002100005c0c00d6001e07180c040e01052400d881c1c0941162140c0745c400c00c0901510242900002078542c0407d1310b40500101d01c099030740e03145140f8004d014900c8101c040800c9410000f0b5151481d6081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 745516097 1250 745514847 745514867
    0x703090b06060307020f03040609090b0f0a031b05060d0b100f020309011d0306271f0b0f0406060e0f0a08060c0714060c07021c02030c04180c08100b0d03 67
    0x2d072005038894a070720805074103103007100410f01030b14400840c00040326035210f618182102d840c5001041a02c035400140050314080348005030300a054039004000250b52407a0065440003013182070705505807504005020703540800d4805100c1350f1618240c0c0d61501d000c8401562140c250b040801074070b410190003075201c2c01684840fa051020a89581d00c0e040004440500a18002420f4403d030703240103c0000b10110300009804400e4070b10219400309004000707401d185c0d41d0443da400c9040380810184001c0a01003008040360820b24080f84009152101d0040c03c0280c038840d103941c00300800c0394041c0010f420360303a072003070b1301c02c1c04020303003c02c614030000c070301d007500650492345d59543c54220341810110704444950380680340c0305010820817080041c40c040d10507140b0840f1040c5600300b04120500a500d1100f0700a949504034036901c041e14503080c0d01004030f4406d039590103040505540c94951854555603c400c42c3c980080440d0780c080d02040c030514030944011206c1e0010041d4a0310010551200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 745517347 1250 745516097 745516099
    0x218060a03080a02120d0c0e0901181802040e0c0301050618040f0501090f06050f0f010e0609070e0a0303020303011a030c03010909060204210c090612020103020f0f040e01030b0703090b06 82
    0x5810b144040c42400403c1c00c0586590170b41741e5441140d046c080044c107029040000041018000100300d02e07014080504891b02d107104840718000000c1104000c00c00f458000e42c154002a0400c001621680030782641000c402c40600340d10202e030414542500c2c4010b10b042e20412101007401d4034520024461350308160002800e01e076200c03103445e04600600601502511300000d8400c2d5004200182e04041d2003408107120500258079240b0392103250b40d000f130196080d01e0854800140b120f00745250403c3c0c2c4030b000703890003000c2c0b0820348000ca140c403035a1ba00300347c1c0180c10000042c0002c110b0020400070405855a00c00d241d850300c0078049280d40818012540202d881d088480103200c1950103540190180c03000300b0244040d420044100910680f41c202c0712101442c100003000c0701103101c0d40c022038101303447d0b00b24106140c0c0e0044001394004208140d15450a0000082c5e03007000f140600301401005641c6c8455506608244402c07490007440101014200101c500014042000c001d8110700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 745518597 1250 745517347 745517363
    0xa021002090a1e090b10080a090c0e0c0d0b0d020a050d060209040c05030402090f0f16030615050a092709020402121f060201090b0106110304210218060a03 68
    0x310060000b1103481c000ea110b0120100c000c0740e2800c1c40c1402c0c101c42c804a41414508000025850081c81a6940707400103035030104021000151058003990801c41c02e0078882d91110700e070f00b0f40ba07030510200000c040d42c803842c072101c000c03900c0e52118006109440124030201e071030001a4169034002000151140226405400c0c00003032101008410f805650340070320010001e11043c0611500186503030400c8070f05034400c96464001c50841070440c4c0342d140c01508440c1c3e05840b10350341e1406050700d100c4480e10210030142e4a00000803000c00785a9481403a00300d40d5904c0703a68680e0f039100145a1842900080d41000554250121010160305034504000030300700042009400c40c0000b80c02802101d80c0980464000c40c2001f10715803100090b10100055511040501c40c1c468804900702e44558a004081400c600014051140903019000144030303014100d0780b8140c0c89106610300340c4c0398421124941c594040505085141c0561341c070850100c040006001840d04200081000d4424800580504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 745519847 1250 745518597 745518607
    0x21e19050c0f03190813020a030210050d020c3414060f03040c090f0e070b0315100f080f0c030402360a1b05190e22050601050a021002 59
    0x1e0002c0c0000240038103030740b054a85641c41498a000b4120680c4840d0001590041c005060010791141071307690786401800550300281141c0c00d0000d1403450484400074400c0c14401d44840302424001011f81c1500500a05044101c0303a1400750391542c406500e03e840302c1c10346000e003481c9000130340303013000c642c0c8000180160035101004165288260200003444450000411040c0130151a02c04104d503000c980400440c42404080c90440316131a90584154100c00380c100170503039250001c0c540018410041120262a43e000075082c40c00068003080400c0c0c2c41502c41d4225504503c1c80365001080c2d00b0f0001241c42c1144408446100040000f0302c00e50109820075038412506010f4503002111030025090b03486410031401c0c8041c2c00b210000f0318903090010a80c041300c2d0303042c1194020250b540740c0500b0000e8003426803a0141580c54220108181c54141c0c01c04e40da1442c000e1b01403100d030b21500020030101d10f0050350a43d200281000d051080c04c000403110316a000480c4d217020703445a98016119 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 745521097 1250 745519847 745519867
    0x117040c09050114090a02090a0e180624030d0c080c0f0303010b041802090904330c0215010612091109090f16060509120a15021e1905 59
    0x100160340c01200d0060710308000130811201010b08401481c404986609440e035640c4c03140e806078030503c0f5010741c00c06035414040000c40b4036070f1041c0e0f40060302c00308955126081c01c5005490704004540340700591031201c689000a40c050801188406401c0e005481c40140f185400342c0401030b1802d004200301800940240540024009103413a0200242525540c0d6074981c140f0780e04d600240500040c1c0d801d580c180c910503040c248201c13070345420050401030385540d42d6180c0403d03440601c1810035140d070042142004012b01300c0d468180b4a0982140010303001d480301d034001c2c40c10110700e46040f884180c0c140103020054200d800d0180d5074003031081c04036003103205281c44010411291441e42d0000032030f806101084402042c2e03c58184541011200c21030084001c5180740e00303051040a0208208011940381c074201070000c903540d03907541c0040710b500c00d440c0d545584000011242c0e4060282d4007258000206075090503440c202c020140b4454113119100c150038102c01041480882800400202010b503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 745522347 1250 745521097 745521113
    0x4060c031e021b03030315041d0703050a0303060801021c020d0b180403111207031206030f14010c0c081210032405010b0a170c3f06011704 61
    0x801d101d40795030242450110780c4081e41c0c851030100451038110502815a07028203002003500d2166101d81d40d000003003480c0b074040c080180001c001c085c0c0c6061172081e40002c2207078104005402107224600601041c5001e003001000c89106030800b046590042011341c10704165058201d00b03d0110140040c4d5414520031801c008100800d91907030003015626428194245064411b4400c030300036201c0101e590b450001c02515081ca00c444801240003d00240c00400e210b06c98038210300c2070b4140c00040c40383d1262510145243e640c2c1d81100c00c00790195404440d400d080c01001c1c0070b20841c0c01c080c8011101aa6801010700801c0c441e041120469400540034100d9030070220001c64001c002d54608100701400c0300031280100071000d0300b00d810880009130b2440004200c07005465141d8610740100006480c40030480740181c40c007960081c00f03100120b8131041c0c901c00f1081031022101c040e040e220452400394100c3c283c0304009100ba040c84001c11000380d8000e10201007041d460014591680c0c1d0b60b141c00c0030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 745523597 1250 745522347 745522367
    0x60f0f09030908010b010509090f06030321070e0126060a052206060e090408131e0f080601060c1b1d091c1d0a241206050604060c03 58
    0x60068100340314401070507005089071094811003402071050a9485005458030b11628607038580040e8814000750081d80441e01349e540044005090300c1c0b034a040943c12081042400c1e1403100540c102c03806101c1d5050b00910041030f003401c02c1c241861022820513944040740d4031a060011070000c100b0024016641c0c055444002e0203000340011007401035010913202488042d20b5072900e8600d41140412801d005810b80c168203070004100c050710741d4407503450300d442e50800e100780420501001030100f0088445505c100d0300e0307000440407550541c0342070010780e500c038034030790044e40c10707800203401031214035484100d05d0141504074501c031082c0c0300c540d0b21090700340301190301440c3d00145031480440c00b02e82c00300c038150160030440300300c0c0ca54001c1c0040311a41c22103100c0b14203012810b200d1001741084c1100e40c801141c4031004015640056031001c0d03443c420312146985000b003c5102d1080c00a039038100071aa8440c214141081100303071304210220f600d030701c00c900a42040c4010b02090108041c070902d2070301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 745524847 1250 745523597 745523621
    0x7060309050a0f06050f15060405060708071a070f030b06070f0c0b040605040311100e040f1107080301030b010806010b090f041d0703020a080a05030417030c0601030c0509070509010c060f 82
    0x1c0c60f1400710342401070060800b5101e880d032400000c0007041d00412455000300d0b1814006109515141c50042080042c3d4445007040350301304028022000422520121203200182c0005074181c2c0c4e2400110041036260000b4160b41858603004400e03855444100941e4002d59004104220031103443c28103000c5000250b0094a001d41d0000d0003184655005015104072840f4a0099462110310020094410340b03001c0d603280045d0034104e4254151900e9001400224a00c00001614440082030750343d0a03440b004066801810000c01041001511844c00340100001d1020744003070b50418842c0095441200700306441446950f100030001d0b078850f4051030700d8014a041e5039510940f492070a41c0c0300c804911060348101100c0000041d011800702d82000b280743c0c0400510f15150a00c00c462252051244c40c10707e8510060082d5004c02500300186406103028480e003803041d51030b010030440391a20081204040240a00000c03a159807c03650303038200c09511150116a03c0380c03000c42079000300840b141403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 745526097 1250 745524847 745524863
    0x607080f0a05040f0b0306240f0f09090a270602040f09090b010b0406211d0f0705030307120f020a05190b010b120c0d02072906100207060309050a 64
    0xc403401500b060080003144c0c00104902c442690b036803d03008150100310349043e00081c0144540e41c8099424105800400d14907080604080e426162401160081c0304c8110074104001950740c0e40d0700d03101401c00e17803000055100707120940c0c8035404042c82d4070301d000441c508817038001840c00801c06a90107039005401d84c8441c11900c0c0c3d070f8034407064000d082108800c8d40d6501095002190b14014401200c0c00d94175031703072613580c3c20030141c1c1104030710f440851100032101e50b0388038101084040c0000c2d2059203282c607030000f052105410b125090074490a0b41c400745c0f10303074000c100d0307000028000b075005080780b405400c02003e000c490407016810450001d000400501580340e007030386038011015201c9140c1c1c0c001c01209145e40e8a0700a4840c10f481105404c82030510910005900d110710b0760300030528000c0c501d6001d810074600b65140d8140140a0783c01d0500c3c50803100c02c600740070840d40007299010030300704c55401300b40c501810043d4882c05607026040406031500c610b03a042c40f40c1006100e0303815500c902e06c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 745527347 1250 745526097 745526107
    0x6140903060c041706010503250e040308061905090c22062c060708030403090906091a040507090509060d0b1005010f050c0304270203150301050901020a08060607080f 73
    0x800e030099445405020300040070b0f55405030604c000004c200e410f0b10720240050101c80154071081801100c00440294040c00d05071002c500c83c1d0745c6034001c6020701d1003a00c981082d0f04040042056140702096084140d4401000800041d0b0340c900019070082220f500780c5a441c0501200603404103042e080c204040c0c25400c00016407a41c0c0403c044400070b071451009408800b88589480c101415130301504d0340700d5000c0c0034113008107503540e006640286c400c0c2844082e0315507038054903041d00d49a601c0503100c1d41c1d5400d1040f645064108007030304d496604450030802480c00d000b000c3e2040e481401042d001d1282d01001611344d0322042111030809801803000246454070030b03021091000f8501426002444030400030030040e000340c090310404440600590704050810940101c0b0548042c01c03484c4e0118000034418648000303200860054030703c00c580b02c101480310717028103003902c0e405071440e6200da104124624250740e11800b00c1c2c2e0048401c4500310b590f04000d05125041e8001e0000b0521000340000d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 745528597 1250 745527347 745527361
    0x51908040804052707171b0c060109140106170f04020303160f060e030c030a0e03101a0a2301050c0a050136080f030702101503030806190614090306 65
    0x4140d0365294038040081c4c1c40e03039141c410850300c4084496030041d030141010045844418040300440550206100060401e414804223514048086c1d100c501c40e10350310740824016815042e411401350591341046d08000c0e8081c0d400310b603a0400140b0003007131a00c200f000320f421541d0034000c491550154001c81c0da40e01406046c1020200c0000b201101d80311718203802c22104400100c1982e150222140103141001043d01e03003660f50b0310200b0101030385806904001000c4161511590f03407141c0640c00d01c40301920180052015410180d0001c1200d0048018007000c11949800b402504403028607000342c0314622581348501d082180200107005509000c100e00c000e0049110b00d4032645a11500e2440710202c0302603001149154103006011400108807000d5401030a00065401000a10480b150102c1804042d021106041d4420441d040c0380c620410030706500101076600000101d595011031084c01003148402a0548149414002048800030003021114103031b8130a410042d003514410302d042c0d2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 745529847 1250 745528597 745528639
    0xe04090c180e0c0d0b070c0506190b0a0f060c030c020a08030c0d03020a0f0311070213050105010917060411061e0406081f0501080c07060f150605190804080405 70
    0x7149440c1e0080c600207441681e107000003032010305490007030000b9060003100d44130010942d000500d20024442034018801c0028820450a0720031070a911110310400302e0380d001c1000f56200003207103901c0380c4440f0030f0900c407500750304105a08880e054180542400c000d440c0c15100e4107468038000c0c0d8844403500e0005a45400880181500c142c004183d0b0b0303178101001401e42c01c074020807180d500083d06c580788440c256800b0b5481946420618044c45003018031650002d140900c158402020540d00c40004120550b0003a03660400b0708400541d000d25900040320195a9800051000e0300c44d0703402030900b0960b03489420850b08032001e00d000300d100b103124200c0000e00f41e034042c0c81600c000900f00c1c00000d2a1031704190591100318041c122801c03e01e860b08004484a01001e4900300d4048420032000c00080c1044c85440034268500c1e42c0420001200080544001c40b158000405c0c0f11040046003240c091ba410740c561440c0b16800c20072140e403a64146821640110740141e900250030409030070107030580b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 745531097 1250 745529847 745529879
    0xe0304051528110a0c03060c020d0c080915040303020303090d0c0210030f0e15040210090e0a050907121a060a051509120601030c06030608010216030e04090c 69
    0x55805540080c00020221454829418004600344070026207000007103030b400c0102c0d10801c6514014041c284280441c509203071420310100c500120116080040110038090041d0705440d90001e0111000800c0001d0103008540070018081c41001882c0d60703066494000d070307100d071400e400703461602c81e5102e140207903490f441500c03000610711030001540d01d054410700003441c0081d4090304c0080215140002a40075110488503084266155074500903040810003180c0168030003108449130600b8580180a81d03000c10400501c1000034101c0284003507807280000c40e0b005040e208001800b540c42400103410f180c00d9400000314a54800c040c1800c1c00007915412880951040111025440f81810030105803520311440f81c1040001e40d00f00e01110303401f8041e10003594040e02c1811340c0c000c0d414401c1d00b8201c09810031210740424640c00d0044507414444d400160500b11700841c0303001d007690303402212500c8941004007008807450b003044260300c840d0401c0208070303403103090000d00715118800304c0207422003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 745532347 1250 745531097 745531099
    0x2102120d0801030c09110a08100302190911210705070510050105040f1505040f140a09030f02030a09140102100e010c020d0509090604020c0f121c1a04020a030f0e030405 74
    0x5904c0c0041070b541c0141c07040b4120346110b130324514a4070b044a00290b03041440202071559003402c061000001d030301e5082040342484141d800e072a0303505046c04034400c2111013580d00c030021110244100070400e46044681c0300c020340c0c00ca03044070b90b560f40d01c0030440d80380c854510020418011403081010014140d0007050694034211400d02884024101d107404450722a4900000c0d2610100100a40d0510741d00022010403540c03800700c1c0b030204212840500600603582c0f200c4032551207040744c05060303202d015046034056a201a500d0300e054144028500c040d0746c060728200c1228100e01602e50381c020040048401000350061215207481d140c0da9009000140f8420b0140c02a00c0140801c00d00c00c1d011200360010041c400000e03500c401080c0002900a00c20130541403042208052401208210040d03a48141c0c001d003a075a58141da84811b44502c0c2081425041805e00e601c40705150040c01c444046d281c001e035001600d403d000703076089029100001411809501c1d01d4072150018038007000034025a40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 745533597 1250 745532347 745532363
    0x1203040b0d050a1b080c0322080a02060f0114130e0105070305010503100c05030112061107080901180506070b3d0602030c03030a150b1b070503010203012102120d080103 74
    0x31113081e800f600500754107282000910700340000300c212001c4400785820801803441c440b102c60031890150201601e580f0240c1d8080c40200302c10f440194100140e8cd84218485a40542540f41c1200c00d580040c200d80c10b544122041001009954941d9100710101d04541d8000e2240b0300b01510040c008010070700500b80a0f010b03080340d40d61b07280502e0090080f4080e60317550703251071070303282010018102a02250485910b900e82103c203c003c0e907940e000e09150740c001c0c0b510668401c0d00500242550442d80e40f040c0582c1c3c0f80a200300a141c1d5503605480701150050340858191342c2d04050721a401080207079110120490180d8014612100700c1102c1904640d25200845a41ca0f0304050f03a890180001d032907500d600810000d0b061241302c0c0c0284103203a040c0100c00c00d0494503410011080c6c0c205040d500e08801010f01c542508100401c40c0b9802080150000c42ca95410408501c200c0394190200785060718400c0c034002e04540307610742070742001040d000541d0300345000c4d41d100420b00b4800b880141c0790f4607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 745534847 1250 745533597 745533611
    0x1c1a10030b04090f1112120412080d110307020601230609010e03070b09090a090c060c0507030c06080603010b0d02030706180b030103050606030d0f0903030309080c0a06020409060f030c051203040b0d050a 89
    0x2034800554244210300301c040250238a0b1070091480303040c605101048a03040014851480400340c0c601480c0350184155810548078500301800900c0c11030164030070356403a100b01449007011802a22050891482684c407140d03262082d0006807071144034071050a80612403900f00240e032511500240803025022907800096407503030300140f019289407003c003616880019104000340f9000d07200c100400d900c60b10607941000e036242c0740c81441d05c0e1035a00501c0071401e14403c001d06441d00b8411440318440884a00c0100c05c041d4002c00ea450200340250b10502614854180d034180440050034000c004000d08203035070350b849103400382e1624801d0325801e000f44620881855514080e103030a65804846684107401c0301d103191002c8000d0120f140003a82c0c07a000800c003201e0031440c00c0c0070b04071060740210000741e070b07403458102c4043c00c846c2c60b94092600b0040d0800103000168030260b00204480044030707a01d82298104100a0031131141c2c0c0c2c4600096100001e29031031054854122610030100070788100058 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 745536097 1250 745534847 745534879
    0xe01021f060f0b0c0319171f050303190e04091b03061b02100903090806040b161407110f060310032f01030509010608031c1a10030b04090f11 62
    0x1601421301112a542c00c06d10800c000745103100900340106103035251070302d096880c00101d901030601c00d50700c04640303601e0080014110801000f1070780081000740d00a6144c4002c07608580c00103541c05640c81c0801c412054250010f035100d4026070786154002261190314513007240443c1182040b44412034a45c0d052602c0d03082003e4610038075580014243e00581b02c4070803000c440714010003135a1030860a005060401155082041111903c1244150b121803003034140b0030302e4103203480c080c210340004001c40c9940d501070243c0c6900a981049510044070082d100003a0001861f000c4081e01181d0098004810494094101e840c02d00849005042d83c0e80c6885032a8403400c2c2d41c403132841410301030203d0f0030b1038241d07294840d91010350b0200f91040000740b99900c03000d181d030943e03211110100080c5440d100480616000d8419480311a0b0703c400000741d03601c140b4012036500480000703600241543c03840054101d8540d6000400b04961102030700a40741c0b440d252030700c10314003184651070240d140e0284030110 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 745537347 1250 745536097 745536119
    0x2619050d0f1a040209010903060b011403010303080603100209010f20010509250501090e15060315040b0a080706120b0d030c06050901050408031308071721070f0e01021f060f 76
    0x1000d011f0390b8500e405803d42e1100740103082c050007103a041042d9610407900401240b0003650103544240c2d030340b8060307080503c101441c2c010049051841c6520421205030340d60b07001850380c82e44121604141ca10700c1016512017081d0158508114004c0d400e140030800c03480004580c4843c00d01c0b000303074061031000300c41204440c2500c81c0d0060310b000c20143c80c424452140000c1d51280e200001072003501d048008036001c64010381094481c08405152840c450074546000d00620340c1c5000d050751909a00c500d00f0341c4a617500c003158401c04052119100912100100d01d402000541c540600b07240c00c0c03c83c80380740c0244200d0122106840032442c1101061800b007040c011180101e03044021142981c648918102800e03a14100803641e0706001c102c07a0700000d089030000302840c0c240d204001c1e103030600ca4500c1c6601d444007040702d03407103004820108200325400410403180d4002e545000ca03210300c5d41c940182d1511100c12005510004c00c12405001da44036604084282d480003140942e6141c0d80d130074030140c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 745538597 1250 745537347 745537357
    0xe0a05160f031a1801150501031a0603010e0c0d150608090609070302010f090801050426030f040813031515060504030c0504020d14040f2619050d0f1a0402 68
    0x21501d02d03442d1140d110026142c8a401904d40a0307000c5410f800065158215680030006d1589078291010800883d80c040c0301e246891a05d003080310480c05800d5000a02c00c0c80140141c501210101003c00d004030701003400e4882030700d0f00c12410007034030742d0039581000904014440d00340001e8040f070001c1c24100c4082015030090001100910256045a00654465030210401030800025100029440c01b003401464011070041c00d0f200d8050820050381c0b0140420301c500e58400700400c2090081c0d00e000704854991050308080304a407211140b524002c00044141c1c0041c0c0003060344c100030490700d03000d640700001d440742103010030001545d50241503450b801144006490510081420080c07803c140d001454034281850340000c16112404a403100040e00b514156822000e0300036038003c000c0356000d4210501c0c0c013221480d640203595204071001c1d01c190411140c0001035005454440341c014002c0d00d0980c03405200511002030780100e240020038030042c0d04d801018810b02c0d024080c2c113180c42150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 745539847 1250 745538597 745538603
    0x105090a06060e1002030c0d120b09060303180f040504050f0c0910031407050a032003011e09060914010b01020c0d0203030f1b0703030518090c09040e010e0a05160f03 73
    0x6942e082d00c01c10049807501c131500150640c002040524510384051010491241294880d00c0c114070700c0c030006400b00c40b0583e5215014130300c2c840a126290f503001059890304034071801c1110500e51242e012465030750b041c0c1764080c0c2050616060000304480481c424120504420840300c0613041c2000b008100c8505075000300b1907207009107091012802c0041a02041c035150802c0319642c039a200c0c00f0800345e80c503079407007520040b46a0050f0b01070403010071200c2c802d07803400301c00034080031003914002e070700454102203140b28880d41c809078070b01040055000f903e41640c0240780500800d507029901ba010f01803d003a80c6006005a4080f40400d01e404d4042000454014000f10b041000c2c0000040c2c00340d1002d00c0004c10441240107401e03400f0300410140021310700c030b80e0b6800d440303d417045205c442031903542c403645104400178410850889100e4054400162080320f0206100b110100c8503030051220014904081c06030702e01c2e1a06010b80020f0041030890340c3c1a20f03030000c0740d0f502d09030040381005000003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 745541097 1250 745539847 745539857
    0x20f090c04120503090d1b0e01050f0409020d0209012414160302070e0903070c0905130b06010909060b040609061d0d1109180f07030b0408210f0105090a0606 69
    0x5001864001c0c40c00801c0710f10400403070b46490884400100c01048944080314158210f0518401e00040e45c40518001c18210301e0107162541003500040c810200521801e0049964518642c155601c0c13030184040d03541c000c0c002c0301181d615441c0e60140341800b5214402551030644004070341c6449503100c412031059500403e400d20408441b58040c4e41301101083e4210300c2010070100d086441f40c1001070042e148900119950070161a141a80582c1603011690aa00c3c10003040200410070b0701a1108661011000003a07544050050b22000060341080740050316002d00801c0d1201aa402841504c5180e1100c0c0c03503c9582d00000c8411072801d0001c981c051464142800c4c05003030401e0714210442c801d03800c0701d00c03008504021034440c00c0104c80c2d0403c81c0c000c55000000b407200902114454141c0c003000703400000d0441c0c40d039192000380170300018294000002c002491030305900c00f02960308400c0c8440140350070101d0482c0d0344104280215803040381c001000c00e107186910720950301101d003281c80d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 745542347 1250 745541097 745541099
    0x240503070e181c030b0f030c01030f2405031902131104030f15051b040618050a030f15060e0f09010b130e0610030b190905060c07020f090c04 62
    0x124a18240010b846030007004403000020907890018020310f0440c420030034410049180b003000c010140d83c142d40341107010341c80740e0048030015100404d2900d01c88a00717003004a0700e40000d00410005000540400c40c520280a10003c00e85c191182c12108541c8200c0c201c408201400c518040203440c0400c00a501076411400700c030320003201d604000090700c02c1c3c41c0b8407420320b0740d80e403a0070000c0d6140c1d0008407000c10070b14410000a01d450304c00e65401212000c0b014840c1c05250000d51402d100d40e00485092107030b45003d50824026018440001d0040a42882c040d940d072442c0c1020580c2d044a002c6940501c2c409070282e10f40080c0c802d8070b0480b112081c5039101038440c1502500702035000b42170100c06d552200c0c20400c10b610b40c1d0f0800c0203104214403000928a00700344070380e030034140c0107032100300d07079520b070352010404103c0251029400603c4207203011201202e0000f0540109003811004045001c1c900802800c105c42c1405000d8850007034440640032110030b01086292007007141c46807902802808 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 745543597 1250 745542347 745542359
    0x3060a0c0507140304180212070801140d050106081005040c08010b0a090e0c330702030c01030c120e0d030c0e0109030b060d0c0807090b0603041a0a140a24050307 71
    0x311a842100f0300003e4070319280c3c4907031680300c41006260914030501e0300020507240030b400b2000b105600480504d0b1001c2a075040081d0005003c1080201c1c0d440b50301054812018004298011001401424221020840201000809441c0c00c40d41a205901c0144001036031042c18060b00680110081c403400480b814241094014880d410b034088a42c812084101e103d52030382c5031040428040d0f14030179804110340c800302d0048500580c2410702c401000340141401030314001400c00c000e8900342004154000700e008101e500c0e4151040101d0194207000b03d5045414002c0345010300e00003650f80a01c00b4004181080d294050300d5009a800500c10080400204808a869a4010310001c18808040d80c007a159103003000d2013500004000d030400c84081002010701d100e440b40100c03040d00c03a9402e40c5003588444160550409041d0700707100315040000d41e032810541c0a05841c18009503d103c0301d040c51200130009103040540b0100e40d02e5a00c3c3c3d208829041c000400080790001402020264107000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 745544847 1250 745543597 745543613
    0x12012708070213140a15150804060203130f0b010e061c030e01090b0a0302030f0a27030309060501080609060c0c03220b3402130e0a140a0203060a0c0507 67
    0xc2c03054407900d5034440300d01c18811340c4584018001d03c56004081045d130600b807004407070084540e003c40c64000c41c46120203415034002c03401581c131640003d80141c0307984d1001001040320b14414001031400502807508000c01000c1030719141a40c4034121381c0203003540c500003409101b10302c18001a0480b200b500010000a200d900c418641c01010714111500503a500118815608100d030f51101094012080041c09806205030607407103105e070041030002a0140c403400c0c0c0083c0c4080026070308044207400c03107001c0c940250040000258002c008104544e500c61020303407207c0065400391041e01840002c603507500030040a440000c00740502641c07a01c684810702482c031903406c007441c12241d041000b00182044622024112082031441600801c0103000b05a041d48240e025040440001503400080580c40e501c030018003a003110b002c0011703808142da0701c00f071070a0110354004000310402ca4006034071f6140072520071074852080d82221a0340d2145130a060580d9030743d014450014000f40510008100341c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 745546097 1250 745544847 745544869
    0x1a0904020402071b06050403051c17070314010b0901021c020c010e011b06020a08090a031b02060c0a06020c010c021b0d2f010e0609030a1709120127080702 68
    0x1000c588041c0d00c00050b0b404004c0030b0fa54080c9000c90030111301003041c400240101c01e0311950361001c203100500303041c1024040f5076400303844000000e204800211550700961048030f640819240092540da0b5a04411409034070000303502d4014080c0020501ca04d09014041c1c0807081a540c020300742900c80c03940116020754a90162a0420a12000218042c4c0740820bc2a1855008610260340c402902101604044000c0c00e001c0c41ea5100011240203c1d6000071103031901180030114040b07400043c000603115005140528106005440400c02002047d5000745644040d400023808103444d007072001ea0302c0340b21003210b50342d019100d000c80500030701d000650801d01d68801c96244211984909034405171411404903d04a41d255800c0d040342580c20030300c402e0442c8401c44a2070b181c07203071800c00702c0d0311010303603c000400400c00c94048000800c060400d0351081c100107410f03125a04c40030803a03980a0110004000200c0c4461510800c6903480590313084100c5402080d014540aa42d90902c0407607901 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 745547347 1250 745546097 745546103
    0x303040927081b0312220206030f040302011407080a320610050f0306041d070e07020610030816020307080307030302090a0503070503060f060607020406060c0c0b031b0702150403151a090402040207 86
    0x810000b1b500142e540e080a0340c060b0840d03008441051519180c040d007144c400d50201c103c200ca07a44100074505901c154074079400454a80081003034034441914181e140e0014022044004e091102c04410031800c0e0f03122485218200e03662401400c0707000041d00c0300e04c600f10700742440760000c00000c0c0490803d0f401401c105003050602c4840b5043c4040f02500301219034015440c210480303c284a07440b41d040041a17041288024402c903680d02d156078065640c07042c445002c50711004d0801804c290344d0180454001050403000f50390b0340e40e9062500500940c407800c2c0a9103e00400e0a000c100c41c02c0009040007550b00180c01010591502c41030081c2090004090f254003080801040c3c005850f00d000b0356005205e0342e2a4921010940d2403c004280183c2d08240451074003401007118138191118080c85c00d4020101440c0c0d540e205002040440c45c1e070800c0d210040c940010000100025034881042000c0381e10410010240d5003d5000040c0c1d90340b01c0c1c0e059110307240c0e8000c200945000d600030040c8600c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 745548597 1250 745547347 745547401
    0x8070c0509130b071805010f17070f1d010e1c0f0317071805010e01091e150503060105090603060409151d0703020303040927081b0312 59
    0xa61400000d6410800b282e0010310000c040c5110410007000000e50382d0008a1818408000c942104100008190368440c0d50304003c00404034140d650300448141855407400280c0074101d1600c0c600c0502041114040d50001070403002c50326484d840803018400305d4900503501c01c511496580108070b2240c101c40350742180034060070a5400040c2c4e001d1007403500140f19440700076507d05400c00c145540c140c010100018404c3e00501c0d41d44001d040329150f0305584007400e091a4044807003004039034490f00c0c1c5d04800b000101e10030344d800c1d0510303250410b14100c030140a4242e0700280e01c001d04032568082130310500d001c200180008581c0745041e001071544148094800a90b5000d42d84a9000b8150f04d6002c100c41550f0b10f417450b5001900c00c9da160390714080104020a1203d18650100b50703284900d00c100310b40d8564415194914029101e0801384401030640807600079022814800300355840008100e02100380b0b1070231601d105c0000b10aa890411100701c01c05815078070a80040521000f191420314501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 745549847 1250 745548597 745548599
    0x6010b13170a031209021003051302060d0e0705060a0e0f012a02010e0a1d06041506020708101109190b07080c0115180b030a02120307030f0504050d08070c 68
    0x2440035400303440316036100002408150203a00f0301810a140b081a9a001c1e80c0c100100032001d84c4504000e81201d100c3d6180014181d62046059403d01c545501c000754441d00004030082000040d400c45901c1c40d02613810303207002c2d80c0c3d25820006036110360007078040403844101400003145000c1c08222840c04e41810220704449201c0000d1090030368214140302050565500d1000795603000e5080390310000d0694103030035698200000b10004000c02e8004c2e44440002000242040d00d868102a1050389207054051025841f03a90107900c3c2d900b14000e0041c1d81c400d0301c0c880516011140120040460704140c001c0c41d0034510400c1c040c41d5a0700300030400303507440018800610000881e009100c01409001c1481e00c030047c4104450a50720142d03900d0030808800002400344a90b845402c480841051800198a40071013001c030f03040980222000c0c2d805019560b860598517800300041409501c280e941c0340648106080554541c052030107004d80100794038012100184003100200141c40c01030b40b8609141d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 745551097 1250 745549847 745549859
    0x2215020a121202190e0105130905040804080609030d0b010504030b06090a09082706090306010611010603060f091509050d141e1e1206100509122d06010b13 68
    0x607a21003030360013060400b08203c1d1590507500080280f203042003460001d141050407030410010781040e0088a040c2580c1c0d40216040041c00c000f00c0d00201007200543e1281c4c82c044400a403071343c101b0328100011b18180500d541c59903218004039010380f944406168141d4035036409202c211100181514402c03036a49a1440c0824268005403005a494540000000082e030980c614030f005d0840705103011380401d100722042c1d80c0e070110b4030a041d41d14030300c0c140c0e1a00d104011920301400b03503039001070411407034035101d1000900c542d00165105401280d00310308409010411070100d5002000140080e040440c100749490303c2852048040c200c00d0307143e142080a05032007041c3e202005800f21030384034070024070201070450482483ea46041850a032505240d17001c0b900055891005042920448120036403820311809402501c0d2030310806880a02102412000c1c40d07074851101c840c900e2006014000000550715a5a91001e081e108101a00c266441c00000000540000b4840c180c0c0c407150400c0410030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 745552347 1250 745551097 745551101
    0x6080405240114030f12160b07020c0f100207050f04020d2a0206070c0204110f070f0b10050f09040606030b0901050a05070c0f02010f142215020a1212 66
    0x441c0201c10907035907501d8840009002e0102da04042d010f030300705804002c003c15020545100044100f40da541d5070b501c8240902c030143c5c011107801014006064203000b40103a0004480c8104203094070030000050045082162054030b6100d03034801a441044184060b05181d00001c120040180015081c40101001034041d14541704140038528001c44a401000080c840d500da024400c2d800640104d0608010007082d0034061140a40115181c100d5007900c524190b04881c1c18551050007943c452445240200e414400a00c0603070342010031401082881d11004420f4040750310003410403042103484405d0142c0aa40200113503202699130200102185203030800e90b20502c80080002494544103141d601120700142c640c03c10410030100e102c0009030b004044000540d0242001c0401043e00d681c02c480301109400490780e0318401151103004403006030001100d0428a10043c581640c80f0304140401406503081c010040c0e101c2849140403800340c80c041802c7c41d0581c17400886440c40c1800d4002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 745553597 1250 745552347 745552393
    0x40506070812070e10081f0603051509132603041b061409040213080111070605361903050301060e0a0308041e0f060c0c0e09060106080405 61
    0x29110a00007032282c2803041116015600100d0350030030449130f840c44030115800120010004061100b200085580718050701810b2020f04000708106030300944803100200034210954110b0360b00c1c6990342e02d03207145203024007840d84a49207010110b41890504d80f030390392954582040c06020070224080b038441c0c0800800c002e40c07096005280401403000d446c6004102c0e40b0181e80008200061401c3c041c2041441d581281c0180000321005a140c000c1280900503080b03117a44103014541c40c0090030303440c078030801001e409040e02034030003001603544440005450b40c50001080e002000820704010303024100502c6010122803100c02c5546031402850484107403142050300380d000c24804001080215401340500c40c40440507203062042c0d618641d16a030050140340152194070840c045911908032071100740d400102214015402601d43e035000c06810f04040c120180c41d041c01d03104001c02c010000c07040b081c0c0103800400003442560b00e004000c171602c0c1e00c0980700315901e014100d040103840c00c0000c8104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 745554847 1250 745553597 745553603
    0x21b04061d0f0a02030c0d09141c030e0f06061c12120b0105090907050a020a17030411031603020d03090504140703180201021903050405060a12050a2f04050607 70
    0x60402d003070905a0b0600c500b4010300d04001076004000f0401c0c089403a8040c2c1d0002d81607030202282207092031404070354503080781e0080c1d0080d200309001041202601c0c0041070f01c00d41c06490800c000c00301702c92096111410b61290407a00d510071000f00d2168100b0120070049030140c0d004c118070a003810742d5440c480a0607055040c0028810320074260351110b82e0f100e0f440b848074090a00b186800100804a555124014041814000041011711595001b0304c034980f0071540c07141900c84580810501e45100d0781054805403114542c2245800316414001943c941c0340c0046d194601550b4507640c204800c201560b60100c04110070050000b40c0c0d91290301840d00b4202c91030313200806900c0c140c000101260341e4501b18a00350401c4294000c0980d80108040e2104d055440d180041c080c0d050809403034070b10a950100d900030000090308141d1a5105500a2141003400424009500d4020780079041e21840c158911400903400ca40745032000f500d0080f00e480818596007981060794038030001d015604040000d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 745556097 1250 745554847 745554899
    0x5090703110d240b0a0f06080601181703030f0f0702150c12010603140702010606090306050c0739060801090b0127052d0607030309020607030e0907030606021b0406 72
    0x20039a40f6003065141e014003a9a246c521845140c40c000071301c2428090200c40c14082d1002e2044045403243d1800c101034503400e581c0500740000881655501d81c0102e81083c080001c41c800319203402e0003288100c0c0969040e0380281b074a03112401c400e40b014100900105d001c101d0800007d5107911a0711012402808940c80005051080c1d4203c10f022a0340204590116454000e09202d420742014001083d00c1d08400c00080640d0f1f90000665036100d0500080c1c049118402c81014a11407140e500c140c3c20010f910000400c08040d041c3d4840c103015000312004681c1c20030041c80023000c95400941c103803005161241d11902d0042840043c0c0b0181d880320052111036000c01d00041c00e0030786000306032a030304000800a81e103801048100681c5203d11252080e0b0300003840d80c0601d8865042407100b150014600c940d0b9032030314a400360005000c0f21045003d80c40a800082c4040e010b48601c2040368441d07006403041c101907202540d03143d0070300080c403503201c0c5da105000b041d41550048603030451031f114119 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 745557347 1250 745556097 745556111
    0x140307060b0a0f05130e0a29010e010902070606090213050a0906061205061c0507090608030316030b010c0804140f01030c20150406020a390f060f0f05090703110d24 72
    0x51605600c2c1c0d00d80c423560480d50000100101c5142041d028111824140c0040e1030380507901d043d01c0902010f9100750452400440c00102c41d801d82d02c192400c48200b207c1b0b120380703656100b4003107050303a40314480c480104080d61074511075294075400681d0322000c020200c403150302d14030710400580400d0701d00644923584600001d01c003800ca00e10030b510140074164015400c1d450105074901a80444002c1a4105911034a1202c0c0d56401198501542e81d0b1140f48561181d4a0305080c1d180b02c2d200001c0c180c4100c41e45203081c03105501903c80c2410020055441541c000c0d030060103a1212201015614058841c1c109040418499000154066482403c0160740c030384040000a24081c200d25540160360207114650740ca40c042081c040c880300c2d201881d40c9103c030406041107103074516900e00260105040c40c2c0c60300c000300255807100030131002c803480c00c001c681c0351000b10542d01c0e8040c0c00000d00308440f0030020382c0d4500e01001e41403a840d110340c128060b0144424500f0724044003d100e07208e103450712104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 745558597 1250 745557347 745557383
    0x2031602060f0d140a0e120a03060b03071d060307052b090302010506040b0a0b040612110c0610060e1021091209060804080d020d09140307060b0a0f05130e0a 69
    0x411640c004400990501030650603000395507c0c0d900342880341003082000284a400036010ba040301c0020159100d1640d02d0f440c000102900d100c5221101d44582007041c0520207451a00030140da0080d800341c1c1d00c00f418620070101c00c400110010b881c042010303403d031021b402e514602d070003008100c0d880f9900210f03642c145a414070041d1803850104d0f0340315180c0388400b0703c0b4000c201c1d0b0690b012600301c0c1c58031280c1015060229001003d081140c040b0341000060f146c140c000c000550360740211407960014803115a18403041361005a42c500b9540d00944940d0060f071418802c0c2c000310714401400c940c4c5a80c0521902c0c0c2c2200719500d10104942000c4542c3e130f80e249194105404030003c100509202c0c0b024a4280d032002c403c2e00c585014540392a0b40414041550a4036030b00401031603074020403607038201c400c07401c0c242c1d520341103070200b100d846081480351141c50030040f1610f82158680951100c1050500080285680254501d20102030b0745140c0104602801c0128013040b6000324400b10425000b14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 745559847 1250 745558597 745558631
    0x1020426010b0609010503100b0d09050f070326040e010305061e06010807030e100c09050a05180402100c0602070b0412080402010806060927060f090702031602060f0d 73
    0xc0208005925000e0040615107401c42283c14081c4240b0b0700603502d47e9500e0104103000e10f690424080400003107030182c00030b41250300c03080d01c45001c0c000f1100c0c0c01991054043c0d581c801d41c040200070940b160300c03208e039400d483d01c0c56061a141c1107154904180c0c88014505507a00b0992003078640743e000b4400c1c801a1040c140d4604100200c4844a006620f401c00001c0c10041d000341c80c0c4820123940b1550050b40280c103116662003590070241c14019462100070007856100203024552044172804c400090500d010204403020026011079820140e030345800f007000258181d40040300348400000041c2c0051201d2009150307480c41850600803500302801d1100141c2d88040443c0240300458050001603a000907004c1c1d40100e044a1040d03840203924042280e03284070803420030380d01c0d54040c200890083c0115035a407290b07809840030302180301107004201c8000d42c2513480e10050f8008100040c8080b801c40b400404941c0060586450140c42c0754110744c007a0306c0f0400c85080d0642e14510000c1c403040034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 745561097 1250 745559847 745559909
    0x102250804030b0c0f0d09020111030c100b061c0609050705030603060f072f06060603040804060e0102120307050304020f0906100c05011515080106090e0423010204 72
    0x404901506450995032954948540d0001510358a002800148910240c1040b01e81110b044506191289244050100030f0312070107404902066041076405000c0070000151660b440c54030004218001d0440c0c1200002e040706a203180c0c1200c4104121028203000c4038582c5803030fa80700a80041c4d560324208130f407070441e030020b01722508000c1c0400500030305940c000307240390300181a5aa03251054032503c0e02070b5544031114852304c007004484801c0c1e1600d04541003001c200340030200149c440c01e5032a174042080700d107c202e0300180200d00c00e1006114582c4a01d881303c041c03c4041c0110360702d00b5102c05000c03119410403a116400204004100b20450400385100d1000d5201070f1707252582da003041e00c00100f401c400d1007001000c202c2c40310140750074800c0940120076209017024203000300d00e485420b164042c200020b54080030840300b400020b4006d210f8032640040f03070b0305030340c0850703c40c1c0300e6607921240e0300038280704051a00081c0400f40882c16081c802800240000b201c40451102e07812845d007144490 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 745562347 1250 745561097 745561147
    0xc0803041712090d031d090108150a0e0a140f1b030c120304140a0b0313140321071112040504062702090d050a0b06041a0a09020c0c0301020c0102 64
    0x20601042c3e5954541d00003500c1c41a605041120324800c001607203e0b40d4000d4110003560001c0c03c02c0001a2030031021401032140d8150342d44030700c0140e903107250100a81d070314907145001c0c59001303400c950080340041007030f20f03404141e00d02a18000715880340d28500e4000001816001088041c6910b021880c08010203201c00e0801d60343c900002e50b290b1a502e49a0155206000280d4452400b0414681e240144c00000e03111020203a41c4900300400c10700b0915a402e070b000c541203d14500d00c0da151038000015580c45a5034508412451600b840a00c002d0040203400d0805014002c100024214014031108550001c25415240c4961404040009a810950000c40030005903035801040e180b055040c101e645034102c10240c1e5803030607400400d58800d036074800980710740a04883c07101005901d002c0356018500454052001402500c0d198040d680700e00505070740115640b90400c503100082c0c001c0c0c90301c8003c400c1521804444107011900fa42c0c4800a400410303580012100340400c421a035112907030700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 745563597 1250 745562347 745562383
    0x120929070801090b0411040f140901031509080d020c0d0210110301050f0d021201060303120b0906040905010f061409070f080103170f1206030c010e15070c08030417 72
    0x10611009081c8807010b0080c440260b0b201c0c00000e0054580b60003201d80c402411456550f0303903548007080700203c1110300411001c144600001901ca143c403c200e141a40d4020300c001c0c8407030309551201d00c02031281e518103d4442405000c401020075861009d0003400000a002d01000342c00342d00d000f030410025090010440f807820502c80291a589400d503415500b0684010030180011000564003080c4030000035070003007a00070320303161b107243c10741001e801c681c401d071100300d1070411242a40e0165500303030910b03607080050040020568a000d82140003418054000006c091802800020030f40d080c0c1e41060900a0400c3c0e41200e00d0308003410000d074030210742d1601408222603541d00420400c0c0601c0090490300000c01150340c1c09018208a03600c40400881c034a99038680005041e00d0300a040703900a101e8000c280002c14154001e4006c004003400082030000c9103c004401603006030001402620403413411034001c40c8441c8100000c001601002c08628012203404400f60b1a040c0c5029406182030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 745564847 1250 745563597 745563601
    0xd0503120705250203030f0c030d0f06031113090b070201140f0f060909030c010213030203010b10050307030e03070804171e07260a0602041505031009020a120929 71
    0x21421a505201c50003e800404185050000030701d503002e042d2603040c58240c000340f407800c094000401004c0c1010320000602030b83c020710580b40100c450b680b00203088020348201d003c40781d25004444140c0c004002600061005581d2110101100120388420150b035580d404240d00d0040a44035a074400301e00050542140740181c03c00030120f40c058a540e00801d085404101c5818003442507c8901036914021034880d45281d012491401441c80103034000e520342620440c807418a088c451000360100e460712403464a60080450041c540f002c10103940340400c3c00742500040c003201c010002004401401091035591004003801c01d0342c5456100e5003400075080c9803031251004685503084480101460000f4840340720b0000740b40c0483d19080ea0140640c40c5200104240c03540600705840c03031081c11001c1002144019945480144d034815000008040200804000b94000b002800c5c80c03403074044800155200c00b04141c070700c1d44504844284030640c903101c410517541c2c02c691402846a03140c04140c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 745566097 1250 745564847 745564867
    0x306060739140120010c0c0c0b0316140c070305030d14040512030720061605090604050f010c231009030e040e011d03030906010801020403120302090f0d0503120705 72
    0x141c500403181074103010790f06400f45400800600104025910340000348800c00812034003d16280c548402151348c104508004541281c0402c03e4034443d800c209454480e0f0b40d982c0f14240c40b50151001c01d001d610a080000b1744003614140300000c02580b06000654646179004401002d454000c0c0ba0700c3d0300a8400400c002c04100e00080f288200d80c039440040c0d903a80c58180c2c04079501c0e41015544202a02a19884007580100080c3c091144608106220a829406804441070320034900446d07400b100034001804641341402c03e5441090050600b03081115240e41c407a0b8108112052241948243d90b0761040780e01c405001005564040c3c02c010030011003d55800707450913000c208107a02075a038800728180091030960200c1c80340003240c0c0b0b100060800500341c40e0350f65801140c4040c1035010741d2000041d100c505000747d5043d00e5014511111031080301c40304030003e40051400c2c03a445090000590310036110308554080132809080034540d12000f28036031840003040544540d04100040002e8020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 745567347 1250 745566097 745566119
    0x1902030702011b0303151401020c010207120305030901140708040c0b030c03070302090d060e0a050c0d0302120f1c0204050f01210209031c090f27020306060739 70
    0x8140366018400fa10544107040407801060b038580b20000d48420242c001c01c1581c5107007403e0714509801d9003100d60148507407004a81f2040d10348110741d500341c40c0301c10b03d0300028002c030040e60f0301000b0800000341e8046da04110011184003038400320045403c05040c0801d10850310a0b1030040c00b51800030b40c0c51400e100e1410031184c0f1004141c0710030103501140340c42e066640c0d00700c201001d81d0000303428021660180c140c42d480360000b0a0480c0d5600c40d210741d15045080045440801da50503030058070452412483c24200c66020400d10602c8040400c030510505c90245408450100b10450050311075040c18207000010f044012164107001400718035440c46058003280040011524a025841e1204400030901e0070300d01d5200701c444c0c0c01c0590072002c1d52035409801c110865030f402461140140d6240300070402c02410302d50b442c0800016004094041ea0303240c00564200d40c0c0603180c21f18118a9407034031401c1c062401003001d4841480034408881c00c2030503050b168598005000086800e20f0420382d202 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 745568597 1250 745567347 745567367
    0x9020403050c0607110306040c050f09040b010909140f0a0605090c0d060c23093a0c0312090f050303040b0d0506060708070614071b0f2402190203070201 67
    0xc0f0458000031000e08215628a100300003100103401c442141c105403800e008108418042c9902174151000c0008084c078058610354010b03500004804142e900300141c8502400c4510001d4480281401d00050380480030400d8102e400c5011000d80041c032142e240071015200045c202c0c0308690f0185190b48101da41704006a001b0b254051000900d90701e10039019500c0f070134419442c440b81c603108003131144040b010500500140340c04880010400388441110036903076007021600502d4142d0071900c00d000011180d0390841d101c0c09010202c0c0100c2d52584c07000c003440c44500e04900020701041c002c00000301c0141409001d850100c0240d410141007030440541c0d80105005d03e0821910303000820141d0311610b08036105075400c0b001c0f96959942606007800038203002d00d0340e20100048100000e101e1841520b2040e060309060111220803401500daa02246107400401d03580b240c0c410034a0300d4402900d04002c05108116140541ca580e00002d04000281c1040d041c80d0564004000d0000141c1c0d02c111200313 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 745569847 1250 745568597 745568599
    0x1b03061b05180906130e0304030c120807080d0f09050f1020030c12040305120112080417010f0c0f1803260d15081b0603061215010f0f09020403050c 65
    0x640c0d9540c00040e10002c0b5072017402d020280790500d05504150301000920649000b070541100c00e0350740b0b0310040c1080040079000342600300180003100020701c2500051101441c0e050b404501c100b8010410011507410480031101c50b4824000c00e412954240000804140004410451415842045500410000480c4810201c0000041d002c03440d8001660a60a00380084184900c0c061501605560003065030f0100f02140a000103841d078034101c0825400c60740306031480c1c00d00d4509941e1180c0c00c01c02101206241d500c0d51000c0219050030b101e0700414040b25070390705584914880c80034207620480c1600b800c1c0c0c0c5c083c9020900c00304a00411402540d84406440100340b01500020503540c01402c81e118002420708400d1082e6002c042050700989441c1000d4640070f080000900000010b4103070060b0300440d00740300140c018549003a0310707922403039000243c0d1084402e4a14402490000741c00c0003848c5117200300c0a000e00d6188004c0d8a015103410401146007500710340b02c5175660030400381c0701 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 745571097 1250 745569847 745569859
    0xc3209150301060e07050a0215060307030201030e01021e0d140411101103040612050c030402010903020f010212070c0e0105030312040b19150e10030b131b03061b0518 73
    0x850481d10700354000001000c07401c2004a46080000e0001c0c41d42d40503080c2640184100b589902c503001086989074040c1d0002001001e01c5031440e40150050700c0d4417004803d03107541c24842014940c050700b01180d02250125005665421002500411103076101d007007000700e8800c44108000940007408240340c0c40d00440300080795244510003110142221440d80005e0f02020600186868200c04148502c3c107103041c0601c4242e0b101c51030090280800c89000e40042c14140b0100094104003800010b91041881a44c0001e002c07204940340070740c042c17141100c1d400309a41c0200401d0303240d48403041c09003404801a5140c400c099402242c0290007a201800781420301c801f00b208544031241d105098100b000f0309100e01c0c013015020743c0181c0340c0f500c42e650b2460484000140c120704071244050980c0e5110b851644036031902031007941c081c0407a000858040d00c03d1180b0a42400a50383c00800643c402c1e180414070741e0460240074801c50b610b101c04810b2000070302c04012150346000041002e154140c0f18 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 745572347 1250 745571097 745571131
    0x91412010204050a080a0201030501050f0d0609030e151201051008041b05040e010504050105090d0203070618021c150203040209010306050402040b0406080f0c190b03040f0c3209 78
    0x104034024807a070b9006581c0011141e00c0020a40000719015007214001d8804002c03607030340c5a040c040101440700740c07568020700d0b0007490000100301d40e101d02d012501078a0182d607900c124030041307030740070800c0c40d184184c846c4c02064454a0700910500c4502408081d9000c050907001e084028050304405072008211048000d402c810061390882c0c16001000300410600c0351060400045000f008107940c1134800e54245000502110400119201c101307103a40c0c0154541ba80c0c80d201d5a009042c00b05a60306002c00f081044130146e40d44901c401c0541c2c41000b40d00d0002403551502e03000c0003020301c1c02240c00b18010f00420000d42d840490f00c034110b90b0010000b0400e5502c0348000341c014800d41030210f91181c90000c011a00040005070304904221032030440b5108070b82d04041005000420101c0c10b02009590001e01c0004008000b86400502c240c180445030751032569827542c12441c0fa00302c1010202d03a0b58601185e194600419a4200071200d100d140c1038501030085803c811001304101420560040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 745573597 1250 745572347 745572379
    0x10020405090121020d060e0d020705030d05090307030b090312070305060a060c05010b0d0c0515090d140703061b09120b2701050408090414090a390303020d0914 70
    0x8640f8403030b15402084034000d03909a1411400920400004800c58443e1702c1d0840791071400090352005881c4014020184003290410480e4198070a00c03009416003c6c0d180000009084410918000d0300c0c11005182c0b43c00001e40064190b840003000a0308250515082c000240c80d40b4032980c00366051440c00010244042c1043c0d805400c0050055800c40d500e890b509050000e1080c180c801d45070304940d00380f00d0202c2040c150050303001d4800c07201e41c82400c003a10400000d000d0144c07900022644810b55000d2642d075200c4408440c0211044c40d81a000143c1541c0400c0e40000050090201d50304114103020743ca8841c2e4101c40d5004041405c0300a0316009040c003110000125502c081079240240500d10b01403801c1c0080d038100300380150080b410000c9040f000004002c100b88220b10103801421200701c65285d2050382911240c24042000c004040d402020311a6a10b2108103070103203250910716459850028600030383d10f5030000802805600c14004640c080c10041700b50a400c071540005110050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 745574847 1250 745573597 745573649
    0x10e010e0c040e180607020307020a17120a0e01140412060e01290405060d05100507181d1023030c06040e040b010b16061d0d0e03100204050901 63
    0x103048003071080000c80400c21328401581203070007030b81002e0040c2d81107030b141e90500340c0c0e8a003e86a00258400c1803030300e05111410b90010348580d4021090100c6180c0c00090200c0760f031550020700320000203055180e41680d2960094155480d1080d10345815140900c0c256800c142c7e43c1c1d52400003409291a404500743c5058250002c000d100c00c552340000f0b0358400030200c0200f44c2c9511466070f02642c20140010764618103000140e0117141c00c00051f01c03d080c1c500d624a40103100043c41d440501c0700a9042c0382c1e1040d0364030050000b9040360110b1602d00741ca24000e02c015140c00030440c8005251664090205138400845400b800107401c03030580400361040d00080c105001c41c0113580e08003102080001d50f801c204292a4041c5020381c62500340da90b26044074034001d02c43c000d010401c0010288200000568035484004042d4007850b450141202d425119400c014089103c2d200042e0501504e101ea85400e0262486804140100310303d840e02c1c0c0b03404510848014441d41184400044044002e07600301c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 745576097 1250 745574847 745574849
    0xb1e0601020723012a060e03040305031204030203130b030f181c09080f0c090907030209280c050a021e07060c0309151e020f0a02060c07080f0c0117010e010e0c04 71
    0x10b005100015080302500c104000741080040d02e085090039040721f51b10402100315001d40e81c1204c0510305d80201091310740f81245014008a0440c4401c0011100c4035010442000203401504520795507030a04900b85255010003a105180b008000001d80103403100c001981000605540f001d184c4401d000041581c441f20558001d004074064056010312001e03000c2444550b40b0808c588181c9541ca4510000b9503850320b50100a401803000804250704c0d00010101142e80c50001c03984419100e00003034403806071242c01d2480300c045031012541512003138040c8000490003c05070030081c801c481c00300860350b5801691240c841841809a02e407028180b05138810070140c030b003025030140034039490307600200f607804411840c018815012050211241c0702080e61a1100015801003034058031903020402c203a4822407242d58103203d81d0000080c45d4a061048400c2550420040c00c00914000e00240c504d502c3c00300900d038420210401440083c820758134840c103451002c805d15030b0954510903402c03814415 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 745577347 1250 745576097 745576127
    0x51005030f01020c0613030903031d040f05040203070501261308040303020f0d0f052a0a0506040c0b04060801090f090209010b030910060f0605160b1e060102072301 72
    0xa89820301c104400150014510440c52008840b5260384031081c0341d050000b5200000c00003110043d040001ca44541c419844200764081444090342040000a0441e946030141c2400c494586c800c0106502e02840644021320080c00d1003c00e45110305000780c24043c003920b1040101ca00300020502800328803400020745039100c0601607440d83c880c14040d50b912424074240701c05102d400c40300440070740710344030040e642106c0d07448090400c00c05680007050141c00e07040d840310600d40e100f95103240003030411031901c0d494002c1000c4c15450402d0b0078141c00d1001207402c10845600d04000402215a2040791681140d00340c003c001a40c80141c1c9852019150080c0060340c0485040000329001410b900118001c20000044a4260031151495403d51780705100c1e9041e07200b0f40010030807002d80250000e0091200ca84105c401c424001e940d18001054103445e415600e101d452030320348004c05000c10341600324109000403c0c1c0c03d4a0107801004070121120000c4044661030036155659005004400d180e5003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 745578597 1250 745577347 745577353
    0x303090d0507381908040f05031c0b1008070c030908011508060a0501050a0501051b10051602060f070c0f050703060f060905010b071202030d02130609091e05100503 72
    0xc0d04281e52082c0b8030326030300a1203683d0300c10310300312100c4907140219068110303200340003d43c400162006480d0713800014815201100c062082d100020000e0004203000c0766410b0029400c00a4020324000b2a426082c5d820f00803a48204495090381d044440554403d020b071030050207030700c03880c507049650303544540c031000b081d6084c507040000701c4e100607540400352050b0000300c88040c1c0e280020841525005e108558020401890900040d4801d00c01402c50041d940c6000d0341410101c25501d21342410f0414040381a80d03104180240c550b21b111600c2000045071004054034200241c9100c1c0c0b004001e0615400d01043c95440c0040000012175104590f80201c190303694a681c07070410f0b40240c629034040e0300c01903191250100304030119118203416107041e082124189100caa07200010344e0b07040d01007001944401d002c01e0030100901d000800a0801d45054450312034a00803003d4407402c1c00d608160300c060b090244001014003030903074100c3c0c2c4520940000c141c9803100344c460700c4401855040990140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 745579847 1250 745578597 745578629
    0x40305070312020a142113090237020c09041703070903050313061e0c0b1e041214090609010c060b040c0914010f081923071d0303090d0507 61
    0x2050209200c8404000781042c0140416200300d101b400c1d2041000c0e410070300306514400e01c00001d0a42c0501004c1108404251440c6035410082c2c25445410440740c0803119030103c0c1010090b41806801d01c404015034a80455040c103070f481d59407421001181c810240c40c0440000c11041c81b54030301c50000c0d90004d042d240c0c2d44001107000e003100790303482c0241008261098100004034ae07100400c4080300c40c0b076680740c0031041410340e01d01e000315001401030141d60703405502a002401202030414013403403080d4540b01c2100082240603015050340c0ea00b01030049414084800a0340b107107070490310b03c2c040902e0542480d040134035040c001441c03641d0f042508107280c20800130569820000080c155000483d400c0118605c400044031a12560052080012000401709048000303002a02510b11060200840c031507503102115070707040042a1501d01201f07090024841641d030024118600010b84401100c907014040f4007181c0d9038441c412442d4012110ac1c15400d09110007400400d001d80f14102211a8003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 745581097 1250 745579847 745579883
    0x1090e100312020c1f02030703080c04091107050105090a0b01051c1e031b050706180b0d0207030809210a0e0a08030408070e0601080604111e0a0306060203040305070312020a 76
    0x1380c102e10400034082ca00501c1c0559040c94808001c1c0e018000a80c01140380c0340180d90704071500c203070103000c206c4070350700501c800314040c212406003042401654200302d840b00c41c5030815a00b50764000d0440251074001e620307084045820940e00c10f0554000340d510074228000300a40c0d84154503a00005030a40070b0b0b030842603261008450040f902d013030095903041c141318001c41078044081c01904004100e503208807401c0181600540940c64081903041415000d581d41c4d202410556208006101c0700542c00101d81e400c040d040800c41d5089030301d0307400524143e11181000840c100003150744200da001e000c1603411185209080c40c000e050b80140c281c0803051740c1e506000360349410902800b0883e0040c0c44010440410112a4031b102e802d0503501d5000946554041c04014101c5507015103101d4400c0040207843c0410704c00d0701182403d0318100c03d544448201005049480075001403085400030041003000c20000107614003565002103035104502d03080700c0c080e8541030031100014168007030707040300f00a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 745582347 1250 745581097 745581103
    0x914010c0e0a0518130206160c030204111603200715020609060f01141c15060b09150a02150a050901181e030224090f0c01090e10031202 60
    0x24090003952000716203034965082012500038998004043d20044c4005040340c80c0000c030001c4503070f00240200749400100c01641d1078181c841c0c0810381d00c0c00b010000410031800c00784203014640f0400c5400c0c40c10030460154040346040d20650103820031900000800c10500c95003481007401d10300c02c00301c4518564460040c00c01c1c21024024a0241c050100003c090001c00b180d0580b0801050034842c00396805d004140e4090302441818541061168203400504030352008007411b0503006101154820a01d40300c541c081d02d4050300b04c040c614503380400305c825201d00c00c040442e540361000f81900c1c0c1a1482c03049103040140100c025074410503a00303201401c0f05035441a4021003c0c000240100780c0c510804054200c1441401030030320700f40010a102c0180c0100d4441c14042c80b03481903c5403040041401d4440b00d090000e0504050250700c1840020f0f481005460130707007181800a8840201c036540080c1002030709115007080407001ca40000e0301290b00c140c069010b143d2100300f40400e60b10000c8001d503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 745583597 1250 745582347 745582367
    0x21b041508061b0306100807021501120c0b0a02031206040b0303040b0304050d0206010e16090b0a050918010b090603090111031003020118030b0a020d0608010c03020c0601090504150914010c 83
    0x41d808043c41810070704180c503822a13200e040041d00700d02800900c11011140440700600000071402402c014a0080c0106040a402480f803034011503400360b000d042088883c2226840000d1190080042d204026004070030b035941207401d1112007981e5554800468044c0458103000b6502d80030004020400f140000c0241d030045014100f11103c0b01c090b80403da035141828081d12000ea000180011400001100303e41c60603a503a14064910759641d6458003007503005102140c01242d00400d0f000c680d405c0092040e1400c0307103100f40e02c58145d458040e680d1000c0c030034002c825000d66000000141c5090094010301105050a6505a070b213292070310f1124842c0259010490000e801c0d0f4048482e0004482d51410a41c0e4220701400503a440750000c0d40001c0d0303c42c48100f80450b07114100090715040c00e00c030301c113140d4055031000b50741c1e44411802941040b205070002900245014107000101d8009100328410103283d440008240c001e909281c1000d890258a0031402e600302442c00707422950000c0110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 745584847 1250 745583597 745583611
    0xd050f0703230a0803060f010e0d0335040f050f06010b1806032404091401090b01060c03050a0e040906090609050d0c030804170408030c0318010f021b04150806 70
    0x5000541540303102c2e900e891200c480502828024404104a803815120400c15504141032001d0211080800314203400840c0c0400e50115442020001c2c8082c00c4ca21074807183d03154584403422142031032003408110440a03202920100300ca564110801004202e038140c80400e0303508855079984e5590f100c04599000c0d038010f604d80c0860641c01e4500d414520700342c901407040b0280e100c0c1c602503103c40b11042035050200c6079900984a0302c00b44003280e4a406560b8030242d204001094600c4281041100c60206034031210402408020003000300360f11106569528030340b498441094800d82002030007621002c24080e01c0140340442d8002049126449141041d10440a5450b00d02e40707000203940603050f50002401065111f0005800940d868a00915008100c1c4105052607145c00d40503103150020500204141d00c00500c844865611181c1511060400d10380780002074110070b07000b926400075450325504041001500c944a5480d5009a0012007940e0b40030003100c0d6850000c0c03666041c080e1258 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 745586097 1250 745584847 745584893
    0x20180c18040203010303120902031f090c080f0304060302070809090106020f0d080c071127103f1e0c0909020604050904060f0f09050f0d0e0d050f0703 66
    0xd04500301802034034100e0b901a180c0300c0c030350000001034174090f01c03511a00320f0b0325004132450002d80d400d1b0003000c04001c00c00c030f01c0002098129071401d021200c1a6420007904e6504c144d80580c0c00c524000111002c0c1c50a5107400340e164102450041120301031140b10b15800440b11001203015580012144880340810781114000c614805007a500100156119409414200504e0340421300742500410340f02c0b406000140080c0a842d50b01101315100315011403129101c00038001c045400c000c2c0303131015101c5161080c0340594000da080c0904441b4001103a0302c2c8516404c0c0850b882c0416900030503e61b0054016424111b007a0f0800e41c4a00001004072401c141d00e070004120388840f8813801c0005503000c3c0c0003a00d0309003010708001c8003000092044400503102d2079203c6409040b4054400d803104120b0000c40c81081e2450040c0c200090340031615060b45c002811607200d42c0d4004916044280152081c01c07884416003811810f2503902410170724580700e0020004100407801124501c21001d013589 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 745587347 1250 745586097 745586137
    0x3050606010c320d09050102100e0c0d0b1008030313030804031704151107020a03060908040306091b0e06130c02121b1608060a0b0a051818010920180c 66
    0x4262a4407205003c0c0d47c3c0140e20503074110046041c11390101d0850903607001203403114007208000407521082c10604945d580300c030303506002c0e0600c0030784a03a50251a03414055030a6281040707064800080a1070068104000c960200302170500500841610b2110034805c0074061401d801d180c8400e03815803400043e041d18180588503100580000e45038102d41c000d1120068a01d103441d410041c168409041e201e0a10402c0008001961480345100311440340c0c201954410081240041700e0746640c3c044100d01c01580d0800805982d034414804006440380400543d403d0300c030a0892038204030350b2420490280020f41d9281c05400c000e04c2c02d04410440c0111020030b40095004148030f000c2d032113201002e03801500400c2070f10410390400410f41c80007800c0581c60b41c0d40d92000502400c125400039507000c03440414003442e150b0022000c849400342900901604c260f07603484c840e00c051101d2110320062251820040240c3d030340c464184010300c40000c14140c034101406901c00e694440390810b545000c2400c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 745588597 1250 745587347 745587373
    0x50a11062110050117040209091c02070e1014040e0f160f061718190602030912161e0f052b1e030603080c07180603050606010c32 57
    0x180384080c0240d0907800b0186c1e2100c0c0d0134402d402c0d1028005420318003400c1c41c0c40050000d4044040783d003080990084c5066403905441070780f2030b10040d01000040510720341c00c3c4848028164203c040d484250381c00500302c2d044800582c101180249905800d00817400041c8102c00c3c207204e00000e4544120b00d00c03680c56625142502c800ea4412403030700c4000c0710f03c40003403204080804144d84050600c02130311900070072940c25800d08090440e0440780c8541c00b100784070400c0e81c20098440c1e2510380c3c0c4d009514044011a001d6030034080108020070b00300082c0c01a540c010300f0700e050591100d910041c1a0701c0d1700400d18009444400038904555498081c02c40032400910180607440f8a01d0503441740c030004040340c00c0e0605030712000c08101003490f485007400400501204000c1505500e180b01600243e0305150130070f4031081d00880004401e0741890b800b840070a0002c00e0181e0401003d0804050741c00c05840c1c203440003141d208074100e0040035040000904070000c0d0b9440300c8004408180c03110404c40712 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 745589847 1250 745588597 745588607
    0x4051c0314031e0f150d0c030209010f030b0a0b0a1503020f0c03030106022509050903091509040f291207030c03030f02060405070e10080601240804050a110621100501 73
    0x480c441040c1a1000030214242001b14500104034003444074054010348a03004209000707400e920405110b020390b042001030007a2051255009848e0500500902c04140000b990200c2c0c07a0184521800042c00000e54a600960482d091601200405900c5a800182050712508241701c3d40001d03001e4024500e4103080411004c80c048009010700da00c0305810000300400a20703004105c031110344010031450f8510754910041d443d00480c000c0c0d110369202e446800340400d07150951050144241805a10a04000c0c48400319014054101c405100291804005040310f2264000120540590280441400348007640001528080d4880a440c175040030000c9940e00c1048070003400b541c0007018144110b411180301c00e40c000c19800b604444182d01e03070344803a0900308280c1c099101010001400802c1070900c1d054410b000306242445000340c581920303016103400c103004c001000707117020400b4462240d07111010360301071034041d014000018100c100041054903003911030302c101d00a0346400240c80d601c25 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 745591097 1250 745589847 745589851
    0x103110d09050a03091d0c0a030f0e010b150a05041a1608040f0e01050f2101061715010e010b0a031e1d030c15100305010516080c04051c0314031e0f 65
    0x8101d01080d9100d1803d103550b0780142502c0409c050710b8004003010543c2d2030161000742c0d10001c3c0006500d0090000300011035002c1c6c40d1800c04a40244200d880c115005000c0d10b044070400c01d5860910b582c0000300c61303070074401c1000281c040f20507060200c091041002c05882620310000c034651005481d94046412030009100c0c0c0c59206820500120181c100041040c1c01e08403414007002c20f210318408620b0a4800580203421040e0f0303e40e1000c100202c04100107200f941320185000740d6541841c010342c82150050150071001000004c6c0c10100501c240d1006000215880729090505010076241020317201b02980c5250215a41d2180070320880d02200b10380c881e5500d000109002804400408104140249000c018502040c030000200d42c0a0252510940c58010740035401e042082d405840c04401501c43d000f20b04040c071040c056511051100c441c030b1500c07600100c0c091005460300300d0340d032409a9900d110444010050000351400c3c00c10003080c2c008900d6012046540f041100c0901c4a01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 745592347 1250 745591097 745591139
    0x9030809040207020102071a250b1b0f13090e2b09090c030b1201020c070303050306190608010510020109051009020d121706010c03020c0103110d09050a0309 69
    0x400140320319180542c000e00d03a440c8180151940103507109004c0c180300e0354080d4000d12806002441181c1160b80041d00c00d54003200c11081120800e86480e0300b03032404001070514441d07c0000308000050704a00007621802446a1407580d5141400c042070504070441d481012912070502c1581c0e4480c0320b01007900f400c0c400055118003605801c0703440a4403000d01d01070f520828800030100104043c11540100b50f94111281c4010070042100000e2208000c44c15420859691040c0070b07007107030b900003c90f09030100c03501031901c01e8903500d640c03000031881c0d400c00700361303440c40e4194000c0050040d4105003140d04a41c42102c21403210900d00b002a400d80d004048020300c41d4122062410454807140d000180f25030019000c0607030040107544d00c4440f2000509804041820403070300c0086102c612125a41c407080a180080b40c424060741d02959615114a9407818185c95400c50641d00010109030fa850b091401001d000003481ea0425035103940b07602c9026000030712800c8010480e6010719501c200540d031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 745593597 1250 745592347 745592363
    0x207090608060f0a0c0e03030d09170c03030a0228020d090b0403031b030302071a0613090503120c0c071d0f09060103120c0c0306050a0e0d050726070b040507060903 72
    0x18860084c07034010511000c409003448401c2c0d90140498404001402e50390101d0040003416000300d05140c1c0c0d02810b020141e07103070101304001d040700711003020040d603401107240e980250f01d90000304034544000c886014042d540b051310765500400d00d5800210342403005601d440301c050361030b00c502c05c941c080c0c030441c0006000b04101c00203403101c2d040c48664030038800340a490010f0808849aa40010700040010b0001c030201208060242600d08001003121890112800f00300001036940c0f500d450b8042e584100394142165000541401c51160407150001c1e4a803054400f40394480c900819850032011801c000d4900351400207042e40f030221400c50044101c2c200410580e80780d555225100d200c1c110b500010403074054510400900e5840d12a40070758441d4101250500e0407008100868803500011603495000e2185414113580003001c40c2c0c0d050760000b00b04140614101011000100d030040450005d04001407282d007807180d00c00d0058021b912503001c1e40d44031541c0e9102110080228000a0310f085 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 745594847 1250 745593597 745593601
    0x2f09010507020f13060609080601060320070c05040f021c06060e09090a08030a020c0f0601030b180a05070801090b1006052704050405030a031103221e030207090608060f 74
    0x443c220074144608580100020904d61100110394140c99103a8481c401203104010107000c0c4200911810703014125520b0104854a5041c0e01c12100400d20005e0036540b5500094000c1030001e901000005490302a1003488400142c030a00d000a40c17002800c45030142c565480300303400700000d0003407404860b81665030f01c041903282400c000b4000c1c0c024040c04020710561041c5070009048c100950b00c0307281d101b040140c4038003040b072003241400c075070060b001206e8000300d005200003100e04014540203a100980003203551404058249000034011018109100b0840001844e000542240e06480c1c86001d070002c1c15103400c090080a4440c0e40191008145e0500c100400a40c4484c500c000c1504500c00030007851000e00c001c900ac0f82d00c246d9017a070340c0780c000040261140c0e400d40103074a442801d10700081e00d10f1420141c4071140030b6031445002c0c0d20050007000744c002d0000c40b500403208c0030400c0304814400b20103860080e41c0d5514511030415010308003240010f46040100b2018418a800a2220341716 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 745596097 1250 745594847 745594849
    0x9050405091c170a050402180717060f0405012309070c020105090f0d1401110405092403030a05040e010506040b0304060b030f0f1f06180f0b042f0901050702 69
    0x641c80c0d44a0702c004100b5844480300150f20300348050340c080c1d450990009010700380380c0140a408100b811488100c1c220a01c20700414944c42921400520703d86205080d00c1c0e03c4400000e941c50340b05035511940039041000104002c06440710903441846000c01d02100411a40e00340098000d0440760140454203400300c034005940500000c01824400030b0480d811441024002842010745003429940b203100b03114003900e8071030248115860440310a826900b000d14140010300000380081402e8400e00320030381c0c40310700503607000204889500d000703003aa521040c81100c01410f941062080802c1d08180320b000040c03a040280840f03060710503d0b802b180c5943e8031501c0341005001070300d42d002d805100e241b40200d0220320900c421030017151118080e2500300301c0c011500300e00c1c03455103008466442c5000e03410003040c1043c40c803441501100d04408920741460304000402003000741d0b00240c0080c240a080c03d00c02c0c00350174290701c035031000d4810286400110100c0740464016081c9031404900100051005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 745597347 1250 745596097 745596133
    0x510090f0605070c090509150a0b101407060222091e02070c0f1d0105040b091b09041a180621010e0f010e0f12040303030f0b100f0905040509 62
    0x403543c002c4c0c082c00350055130350030076404841c000c907011b030041d400a800c1103654200220040350003126424041c031041d401c0b000000c1d140c0d044d990b4100c0070303c881098600c44d00080d94040e2174a46801210031519011081c11010581c048031600c05001015468081803075070103445950703b04180248041c6910741502c00c094001e510070304068a007800c000a00050942d00940340c3c0d006000c5a681c00c0f9014030307510203030000500d41030f0451031080f400d0440020031034a034003241503400321103440c0801100040b5000360403c0e20500c82615005070074418051802c26440300c85003642803007501ca00c03101c1354001d00044c0d1362810a031400d56010302008400c5400d030303200c00c0c14a4241c1900d40000281102a8801645030100e00864814039945800303606c0c000150502500c44102450800b0b400141c41081d410130003480340e800010103040d5100b945004920240d40080c2d00b2420140c4000503000720240d014114880303040311803001406400c80494581080d001e900d0241c040c0341c008241c43e03101e100007019 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 745598597 1250 745597347 745597357
    0xc0f051506013b0d0219170114060906190303051b1f0e030d0f060326070821040308240114070f08030c0c0114090a230a0c0510090f0605 60
    0x81e1000c04d810044001d0798a010100700040d4403030395049111840d0483c441001103485420059991402c0501550b83c10b42000403a4080b0003118071606035680c0200107908a07a040c2c1043d464540118404001c05030071000030007050015800400c0d50202551007240c1c2c0c0c20411040440100d100039003440200426086080129414400d8a05003d030710b211080c03c070b032441a0004051511a40104107006545910280210001008043c00362203015190800c4c800d41d00024a801400a82c09007441c40304402006c1c040c0c0700f0025141203080c0ba05004100071807d40f07540802c41400030306502c1250343c2c4200b02d40c81a5042e1030f050f40c80381c1040101b4856400011055443d180100c0c040703000540d00740020f40c8a010140d41d060748621441c0c41403800c42e006490307040c0380486120309100c000e000004940000550000c0c0740e21aa01280b0001040760102c0041032250381b244d092018200003040405209461094403266074000c040c0401f101e42a2492044a580f00080c0c6424820a0f1040c030044c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 745599847 1250 745598597 745598599
    0xa1e0201021b0105010f05061e0904061805070e0a1512060b0a0c06051006090e090109140106050111030412230d050304051501030b01060c0f051506013b 67
    0x608007050b00341140203101d400b008880143e599540140840620b602c9800e01405082e1403180c00c0000c0d688800a05034004190b60000250208000109540d56003102001d40038a0080b14884121014901d014120a032100408580d032541450074030b080c10000c070021a801d005d400001d44c2e20b0071100355030f011602800e00180a48890001c280c86e00c07404002e20414105070342e0180241c4103818000c003201d102920545022100c9401001440d60041d280029074260504031003141d107980c80e08500519880b04d0040c54100d50078521800c4940c194081d404071502030b00c0b08951203c0d104100c503200c1c8110b0140441c1d00985104988c0410400c1c0e5109018015600311a07400b0210b0404461420604003004000580c00208000030480705000e9040f0300407a8031446402541590b81301d2400030f9050160200300109180100e091080b01103014445070380007400d0301c08100800c84c0705240c550084450602085038a003000807000d0503000c2600710b8050342c0c07010030342a200c20769507480b0540c0358020403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 745601097 1250 745599847 745599851
    0x140c0c130b1e0a2705040c05012c0105160f140c060c060429010b0712030c0210020a050f1b06070809280b0702071511060c0a090e01090911060a1e0201 66
    0x2813540001a204185c003450041c1c2c00202c40500c0c20b800102004004444001c00113800101403001c4010358000301c0c26040700f424050b89450081c1080802001441009460b00802c0d00605081c011010398075501c1000b26016038844000e88814080d007072040100d8540168030034800a00402d220f006484030211448281241100c020611700d015203030f00ba0070568400c0750000b030382000c02400403800440c040e1581014001e0314006100651180b07100004240595000100c06500d00d1140c030031902900c000102031525900000c888480c011a000020b090501c904804070f015180550b440c07a200f4540300e0006c0005070002c980300c4421051a90070240c03078451341501c1d02c001401d25414030f482a0443e90060482c60701c1c00300a00d403940c4009510009100c0e02c0d00c040c0e42110408207103694030103041d4120302d9407220b89900c1141c94000035806040c40e43d052500100d80b500c950342088162501400c442d200b01c0c181c01c41004003d119010f17042001c02d544110040300000a120145841480d81c000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 745602347 1250 745601097 745601159
    0x90b0306030a120e01020c010903030210050907090603060915110403060b041805010b1e0d0318080102120109050a050606040621020408150c0a140c0c130b1e0a 70
    0x55100351580f03e201e40020034a140b50414465a0410200c161400c5c2441c1c07184036646507450294480c1020050317110150b469100081d40321200700007580082c0001401041503a59a0500b1002011940713001c5411641035070480c0040705041c001d403404010131410301d52405246660700c100404404003c941c0158031201e02240c004402460702c9030302c2d4002c400102e2070400c1c0c0c2d410090602c402008592020390000c0450b0055112412941031150b41070612400c400d42c100e0305000740b10300a41c488881c540c00040c0902140040703102c054120707521180b044c403558403010005c2d0265002110140d0700560284130400c0420311807208100195483d00f10745015036502c03407901d02668483d8210414560004200c0141c8a04140a0650214416070f40314204007401e0340c000c0120021b00681c007400300012810802602003803000105060740181100d00d1802d060410b1000341c1010700c2d41c03c0c071840c0090500180c4040c3d0055004031203800030070200205d410301c840303c50b9a4007104000811070401d046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 745603597 1250 745602347 745602353
    0x5060a020c030313091b082d01080f0609030702130c030b0414010503210403030e12060a0b04050112050a02011202070606030b0103020f0a120f06110d0510060f090b0306030a 76
    0x1072005000344d6070310200d09810b0480c03680c10307514094800d060074a10858a0203160350f006000d6070304040d101140d650340420324803116031580001c1042120030803280000064400b070000e101504010940107486441c1da0361044503071280a200f0020390006c5100b1071056000c1b60719889084000b1060800059448505001c607045030b084c40c06000c005240400141310b145010007103201c481c84801540070298824200701c00150140e0f21004060007402000031046559000400c940b065040c8119243c030b00d0141144006042c4528100303000e14900030003c11000c88036110ba02040d0b80280060150290917401140c0e625031040b102040940c1c04d101420010b50719016010056008450240d425410760041121074103004103002c1c89a07540381c904010910b0701d500303078190f000d402060001c8061050b040440142c403d5000c4542c03490b5000070281c41201c80c0e03a101d5800b0302c01d05404d03d0551074a90b02c042c4e81196003a4500c230042030640d00208144c2000350001c581c4808040c0039940307052883e0b5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 745604847 1250 745603597 745603603
    0x3041509050109020a05060703090e04110907030207120e03030a08100f1e0501050405031c0c0812180d0e1909020309060f0906070c021908060c040305060114030705060a020c03 77
    0x110040390165150403e1406500e0107001c440b0250400725a15403070242107030740182c81c2c400b140c400c2aa03061407010020303061101502e1a11550900580f41c1c50551500750030040c001e43c40302c00202c07034402407440e07044215881070388800407000c2c02900035407400c0d002080644909400030702a0105594644001c25401080201c0e800104040410f400c2d0224245040010017456908483c2c1040014002000103a40c0054a03401400101c1281010802c5505040352640311504014241c04070000b001d000140345421090b1050599000090aa03024140c02d80d48a05042c0d4602001036900040c3e000d0034a0705610032088503001c00303c40502c06945694074030a0381c004940580035034011400f0040c80340c04d2000c1403035000c0000f070040c00b0686000c4d50701416440b4420710103401007100901d402880108450040e010700011801c6403500d14194289503416800350108880502a0741d0000400102d01c0e20721082c072090041c003519010313050000780005d035003000c2e1691045100310b16402419807828 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 745606097 1250 745604847 745604861
    0x14150402090c1b070914010510050a0f0207051509010f1107091112070f0f020a03080703180609121b051c2010060506090d4e02070605070206030415 65
    0x100c20040b1741040746c001e9044100d0741c1640410700585011111481895000048070b41c0210107092070102d083c02c0100803460080207801140d04140002e40465400c00c0e210043c00300444240d0300d400100d0421030080321103031423000240f0036a6100400034090050180c10a0701d528400e01c00a030308000c2d203030780c1d903454401d000d0383d41001044111203544d5201e031b80700b40401c48026450005201402c05a03a0080441c50b009016104040d83d40460f8100041d038007060b658282d40144060280e1071913418064112542c405140000c14814241c00c040304105a250f0021150442c0140003d40d19510810100078070000400d420007020701d00304511801c88240c208240389464000f0190b200155002004542c01500b00510401342442110040d907610000035011a50028907202041b0b48a006825010240072446092414a41820800002c8000504843e601c180442141c000030410705a0f200e036050702901d00040c074100030350805070038004000e540042c480c81911810100c1607604004803614 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 745607347 1250 745606097 745606109
    0xf070b040501061d160c0203030a0906031d0615030f030309010504050c041103070c060f060608150901030f0f110a180e1c0c050c030a14150402090c1b07 67
    0x440030300c01880000d2190314060100c005a0110682e0484010005020000d10258401401e0750300895090320520142e010507074044d00702c0782c46403981c48000d040d6615a008075400203243c014414040c54801d51041640050640030b816241c0325119150b4480070310742496505489494108400307400b0800045100e0301c103003000000c05040c5840e10f00d0400c408809480c0c482c1e414000c100c3e03012090701c0101c94016a1a040940903510301b890301f80098070003640704400319850a003000881c580c0000600c2c0c820300401451001b90f40000007041f0f0090300070b01001d407804410b400c102000840c000362114180c0d004505c118900d444550010b00d1104a03504101030140030a002c0814410180c09101142002c80f4090078007045071440c00d40c441c00040c1e40d690200010510b0b400c0521a05021682d80e030403000c1d09480381c25069007040c0394101820320b400820380c03003002c2114125259040465005d10b41c010103e01c82d03916400c0c69115140c101ca1460340e003847d0441c4d14891044000c024040042032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 745608597 1250 745607347 745607363
    0x8030c040611160509090a151d01020c0c090403110106090b01120504030e281214010603030c03212d06030807060e030c191502091f050f07 61
    0x801c24100a12100201c1021400e99000700380014040c1c403a0981002515400d0365000c102d03550301a607551070201c0c0074002402880520112200e6800b03030380c001010100201c5448032018101c031480c80d00700d00c685801e41c1c0d0282c000c140c4000309454107040545d0400d0091828166502d05039002a0840f84594000901a9560035400d032455070000304240701c1c014074210402191402c3e440160411209005140c482c1480b02c511454518504098841035510044000100c907200d41c1040030b8034601c484162200c40310303c1890b407003030130301402040d09413507050361004620225541e003502e880088100c00e0002c10113503a000143d600350b52050180002042001480521800c240352000b20b902c04c003d184010b04104040c404100d809040300c1d907041d4040700000e103640c400b01c040360550154030480c9615008040e60000c08580d991039000c812030080c145000440d04c03114a48040b0f10810643d0341c0c1040c0c42501c10b2418602c0c0241142c0307071619604110b03281ca03403013035804e84d482e034041003003180d03080313 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 745609847 1250 745608597 745608599
    0x30209011e0f080a0504020a060806191d090703030f030b0d1b050f04020a08060915280b0a0c02130f061e06020105090a0809030c060f0d0b01031109011b08030c04 71
    0x294020610381c0c001013158001c00c107904098000c00c0c80030351039004d0101440181004a1416104e17020220400400b41a0030101176440324100381034048114015807000076980046407207203802003500c10890380c1c0341c2c90300801c4201e6514240c015114456010741d001d0801610580494104007040b55000c41d1101014449400d150070010f40e440704454450140f4414054440e0881e0045403464106404480c1c820303a56880403204101d0005416101e0382280c0c2d003006102130761120000404416225400314100759071100c0710740c2c11901400c3d402d00e00090b00c0648440c01340c00c0c0034043c403058109000010a9440c0908100d205541c4150302000301c0e4040c100d03490344020080c14512001d011035200078849418420f8503590740d0781b00d0781d4001c2c09003000060503501c41e03541005a403c0c00c000140485480707140c0c041c04000a5005001d00b04100c6040045600c02076101e0321030071100c9400145918102800c000044034041c2d80c5440445003d00b15000480108400308040c40c03192400484a554403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 745611097 1250 745609847 745609877
    0x21002030a020709020c151003020d120201051302090103150e16061101020a02071e080a120f02010507080c1c1506170106140a0e0d0c050f030303090d030209011e 71
    0x446113521000c510792040c00310b0841c4000c0810808040000104604000d80302c402c402484084a544000c0d03000c55580132600070000400740200d46104240c008100390760300c5003050300200e00c0c60240207520070a60001071001030003582540700740403902440002c1e155007081c1c0785490040c00c03010780b03d60200c02c0c1d6000c10400b40d0004030b840103440c00d50029414503c00100103036603102c1a0041c01c5200421030869202c5001d407030641001019120221034000d210b50030000d040000d0b104c2660f00194220220011240c014016540159060383e10780c2a41d80c1c0e07003066a4040e400506e0084402075110403204601c00781401080c0b00204200404802c0074540341028196490517002140000342c40d1004001464015414100d40a48c4010b000c3d56255009000c03541002024896540006581c52000a00102d00b504005440c02a200b01802c880c0c1c0804156807030000f11076044180e800743c1d101101e4107100c0d030050501000c0c181800561000850121a454901020120001403001c40c2403009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 745612347 1250 745611097 745611103
    0x19030b130908040b03040f12080f01120f030e010e18070305010f1415210a200d020a02010b0a271a01080c0d15090608030c0a060e0307021002030a02 65
    0x42010300101007280c0d544030b58401220b806907104110f0b1060001c0000b8081c081600802c440b6181d004241c0e0203a401212000b40080b682900e041c00c0c3c1030100800450308500038072403c81b84c9600602c2d20b40c040401d80d5400c485401c9800c418030304104200040c08016111400f6a242c9100100d80040e0356140c0010002c08440050b80000d4140c5d984280070800703510000b281e422007c2003a40c01c0010525040c00c00c04c500c1c0300344001002c3c04000440d11100c40300701d4018260140001440c107002d80003580c030703680342c03050030802801200020410410382104019070082090041e81d0002061004013400000e000c1c90b0954000c03012000002c182c02c42c04001d91020844503004480108600e048a0300e444000304903190304203041c82400c20201c0c41a9020710240c8032081070b02c1070144508281c14401c03c0c02a1078038803881c0d40c0c442c2805000b007488500803007552440320641c0003e00000f001512280702501c0790700c05039055408200550001b680341d441e084c074034002103900110f540301203002000346 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 745613597 1250 745612347 745612369
    0x12060f0510170403080c25020f0a05060405010c0c0918062a0302130e012309010b09090a021e0a080907060203031801020d0c0e10090e0c070819030b 65
    0xc10000382d1030008020030041c02400d608190103140c11405075aa0720124103045c45000e1244000303c41c081c8040a00c48007982c09590124030030b50780100c01c43c42400a00c45009141d00505030700041c184424042940f00d240c2c00d05246006612100d4520342d60b01d060701c02c80d074125116100c40020000e0050900505014042d1402d10341c05d0015003107100c1c440d1000324510040103010400d5000180480c4089050300c010717004d8041c0c4003d0001550b55407005411807030b60304440c09580300c042c80b60303400305242c07402d44c042c12100c41d902d51500d4010510300704800c400c0000e021965440d0700740312410500030219480d02c1c1f05900740c2181c613529032010b00c01400d049002845c54806d58001c020034005554080141c94005096002c920f00901d14080058064024462040c40d82442e0007074040c07034190b01c00d101013091070043e00c0550b4030751001d40742182c19004502540f410010080e01082d01e60741160001c0001601030b07040581412080f140c104058072014200c0400282c9070664001d0ba407809100c100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 745614847 1250 745613597 745613629
    0x310030b130809040c020109050d0207091a030c0f0319240b0d0308060f030328020f071505070b09061902070b061207240306120203190312060f05 64
    0x14044159903070b000305521410200d14010b84e191100741c4004e0b4001d41281c48150f44c0602640e08400c94114000e50321887e600c540c40385a81000d6001c124144100d5281d00002c0c0003034040d00d201a2480d0030f018014440e01000364251044a42030030760f02c0e0380303480b1000009100300078442100d41030f05103030102042ca0b504400911450160243c3c2265681406101c90950604002c0c0c0256901400264061000b48210390580400580f03c60010030211003820101400f81c2260a00100d020080341d40b040303113000040342980300b940e051042e9016400625031075040c0d894214a0190a5a03071460842c10a07608034101d940005c05000f82000b00d03051115640081907802c50a000054482800007400500081e0050760380c29400c80f110481402030038040e03c0030f41084800241501601502d9034009000400021319204000c80c072001c098800f14100c580060040c008540034900202803401600c0c01101400584014241c45001f90300a050082158414100c9058600001e000c01124050210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 745616097 1250 745614847 745614871
    0x60303020d210f060906060201140106030501030b012d180f0b0f0f0d1406160e0105042102030f1b240a05090d0f1406011818080310030b 60
    0x1d0b0b00740d607110107402c24203000d0700c10089290b40d20100c2d044003c0002e6004403101d2400c101001c16a1b80d01500201c009000354a00d40900303030707612141102103035002c2c0401080d4100c14001084400190503522118844100352290510f50441920b030302003403a548640f80d00d10b43c844402c0701d401c800e40b10b680300cbc08001d044180105002c81c0001030008003800b50b182d20844c1509202041d5484440d4081d9660798031080f0b20924440480c816580e8890032070380603104a0390705801e1900541b050100841da9103060b100d20b81881d04280340c2c20f070500745003a024072000c0c11580d1200056a02040004000101e44001d030403078604045803040082d40a031021402010007200c1900400f01901e103100e5030324141348000d511511f000c02c08892520030b841c50241d05c400c1c90385448081c800c0a40500c0a0b1131310424202c030902d0803065015403200c0003441499004260704142d218011015004080800c5040782c031640b03140c055542d20007544c0c00680b83c0703550f90844a601841001501501c1c590011090401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 745617347 1250 745616097 745616117
    0xe0103050624040f0e120702030622080703020c0a23031f0e07090f0c0306050103151a21010509070212071b17010f0c11060402061605030a03060303020d 67
    0x2414941c0d452664040b40543c4e902c50301c40f02c2c12000c1d0752000602d068200309890341d8460f40c6040c81c07856048400300340d11034050840413813071030f143c586070300000035003007444029190000307807107000703c68100355000d40c03e500403040010120350f00e40700507a000c1c1003d01403c1e43c03079180f9004c01c41c158400c4e0300c0100b8020307440a2284c0440100f144603013040707130f00409404a0715144080c18642016039580c0810041402c1c0000151800b80030303081800e4010700d42d0740800c161552071004405a6480c0b580700d101c000c0b030510040c41451019140f04811407101c20f042d91030610000600300c0390490006548030381240781da0050140d8075001d00c40540019040c0700600c0f0144c19102000814400c60900501c0540110705080307283c80d111701c50f540100b40c00e5001d41c0058015a8000303000e062040d4071400424030341034032841440d00907001c100b10041c242008000c00d907503903800d000c1580e0160094a81104085c2400000514100b00034400782c40f01e0769022441a145140191814050100c4030f030034000031045c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 745618597 1250 745617347 745617391
    0x1090510120221070c0c271109030a052a0d020d03090503030f032a030708060a180b0310021306050d0e06160e03010203161803020604090605130203060d12030f060e01030506 76
    0x401d803507162142490008501e0380c0b00f449413009203c5c000d0283d405000d83d54000d0207201021851801000a000381000d12003040786056a50318107374007046501003000000e10700941416400540c0c0203100c0d0034042003040c0c643c2c00180c1b85411070791030016040000805c22404a118805a1001010b0400c1241e5482607401c0c0b500d2003800010058410000600c001400c0c4e940d41204800003401c4142d07030401e40200c001d0800000e8240306211901901c140b84a07016074040502c211040443d076060301c50036003410710104595a92080c0c4043e494152103416070b00100700f05010710380c001c0715050100d120215900c00c1c00f41c980b400c60f00700e261203079105004104000d58402c110002d08003403858000201842403102c010060f0441d003010b500320a0108002c119001c26900c040240c3d1011a4027200181d88404c084050348401c03280c1b01c0e089100712407031100199404603011200c250074200400c6620740c00e1015000c5903900e030b024004e40c03958000100103210703050060a4100f00085080a80014008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 745619847 1250 745618597 745618649
    0x902040503120a05030c1321050c01020c0609040e0703020616120507080306010806030a0506090d03060f03021f14030c1902010216081b030d060501090510120221070c0c 74
    0x240110400307180080e0101071185851f264001602d45650710300f4660345040080c9400c9007501000711f031603110310b8001344025800000c1409092000402282c80c004101007808094040100ca1003041e104440020005030b580744040c1a0448103084a48a0350703080e420702042030a0381c82201d4091200800107603000c40e0406040360f40c064404e0034009030315144d00c0c02081c82d22200401c040c0072401424180440c0c400d010690b124075600303990703050010588400480c060400984002584211101c01c05170321264011031046000045d030611009034201105807c0595204070b0303828900301c400240040a046c00040c00300d00c007003282d100840c2044400030802099008100019000800203d20800103038803c40d203a09034000b00c4001c2c2d0751100520300d164405495280105404111900310202d51800c2c4a00c6c108501040340d40d4442c0300e100e418550b20025404918400859400b44100406c1c050300a40790314003816043d0360392624004a828052600c01185e000144494448124101c00b00c45c16 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 745621097 1250 745619847 745619851
    0xf0503040c0e06010504150e01020d0e01090317090d03030c14030610080a020d141008061911250b0105030f0c0111160b0304050610120f1b0902040503120a0503 70
    0x46120302c40ba544030080142c505029980c45255624511204800a20f9100c54500c1042100307070202c0c2c1030400c036005e00f52601440705400f02e001500d1400c08002060940d0745102102c066021400d1420050601107908945440b505070302003134882d0102c81200e5030114200b003100360821259411802d16070000384c25611552440810444000080750300001158110740c01131140c500104084001c8000007450b0040444418030109485480011a0040030a440b44981c92a13003d40e40104003603039022004048402550051500034000c4100104100d49900441043d002204ca01c01281c1c0c039005d44140d0f01600950300036040400011820314002401c011f0014090070400041c400180a1500d0700e1030b01c0c0020340300740c0052480002c841102000441c0918011800d44409a4428100030040c49042c41240b10303142c124881b44000ca400844201001845008204a810812907c01c1607030b41d0940c110440c0350380e0000701081035150800000c40c5001845940030305000101d05c000d0058000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 745622347 1250 745621097 745621109
    0x1e120406090e070306090213030302010b0303071e0c0b0301032d02031009020f03030a0c12020c0906090a0e0f0606030d0305010308090919061d0108210c010e0f010902010f0503040c 79
    0x21071000f05200a0180d04a00050401c0350005c64840c1107030069004400414442940954a81b03000050039090100407500d01c2070b0803021802980e0318119064241410040d030a40b0910b40b21040400c51048101c01503009500511060380b0300d00c003c0c1111012808140c0c0940490050000d1341790050320041510b04582d0480c0030300280d4910f00c2d001042c04400709400d01c690601000450840ca1500403c0a00d000e5000b00305000e903800c2c90700c6007070303a40388004581c0f19408060b4800040c0306290000d425684021030607408035410000720881c5181080c45030400c40c05410250407c6441c0c10700b0000d01c036241c0f00c00c0c42d090010f075240d511180518810b10711114041d46d04000090815081800f0381d449040c0c840d1001c00c80c11b41e40b007041740d01500e4000003410007906800300000d0001f20000700c440e54070354030510503401040c1d5120b500040d0352007101c02c643c19540b2a03820360350031607050000c00c800030000b000200b80c8218910004041c0e8450741c44500501a05005100115200b03c0c02001600c0d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 745623597 1250 745622347 745622369
    0x109180201090611100615140f07170c01051021080301120f08040b03060a0f05011d0a230301050109050c031815130b010608130209040f051e12040609 66
    0x81c078100c0007410f00e032810100080352410f00600260b861440e950140031050613903035600c0100640c4440300d2827482a00e400300d01c1c6000504c6180042541e01942c61350350b5101c82c45042c50541e070414a142980c1046445240124400f030040000a03500310030340303004000e80c640d045500a401d03039811b10350340410300035492180d100d503401404200101c0422a0415000b00c16180c48983d54802640ca9500c100c510174015000d1140009600705030510384d20a88405841f80e034002580c0f00e15100b960b05032018460b500901410000401901103094418040601d00c1c600321110300140c14142940ca040e808000c0040c07400003000702240580040d04e0b000001100f40b0045040080015442c080e0140c000c004050044424412001c07200e1100c0b039104d0788030301d585407020f80c0d8482003a42d00130030031641044034005611070180140341c0043c1c000e5105102c2d500d141415060707034455910740103181c080d0514031072440d03071115884003042200700d0131061749040e4289080c0c01c0c40c42c01007107082d20307100d01e0300050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 745624847 1250 745623597 745623617
    0x708060102030a08041109011701060605190e040b1507021503010609060507080f1207110a0209070e06131412010b01120509011803030f0609050c0f0906120f01091802010906 76
    0x10342c404542c0031544001c1454a1f82e5860320700c0f000f1110700b5807244080c030790b180140004220307000342c007030310744415240803a048540606442900d24440000009610a5451400342515543d144094040c00740020555880743e465206000d18030107a04c1301c110040c0b40c14001006001d074040f0300c03d0280c0c1c502d80390243e1030301c005290880e00c1c1d000300c4540d100071240c00f0540c4004d0301c0ea54041d070361050902c1c1d5141e803411620003c0340c0381c039005010030203034001d034039203000907035103401441460741d00480940000d2070600b5012031002c03000c502d038028031020540340181003242c1c500764854035080103c3c440200104a50039001904441e00c80ba2101e1103941c40b940019018002944249461728400c81080b10051103498018002e02420012003015850424041448005846103c0c03045010718006860682075040600e001d402a8000c95480b15040020703084400c2e4841d00d0502405444040d0041ca504000803001600c04070f0144101d800700840c420b0b400350f0383c0314503681c1c22241b050500f21116 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 745626097 1250 745624847 745624853
    0x130807050312041e0506071809110307030509060f0f040f02180f0901020a020712020d15060801050c07120f0e030d050304060501050d1a060d0209010902070b0708060102030a0804 78
    0x90240650203030540c0000300c0c044000b086021074440c4035a120780011054100304005850a88031303501c2c0050400e80c08000091045401100050030300b030380c2040c80d001016a154811816201c00c0c1c224a0040c12010080c080c0d50354150141c2c9030414000d0003c0c128600e4203540803000703807100509101c040880200031030700340b00540f1441c02c00103801418141411072010001000c205055903500740382e4020f003000642142040c8243e035060305041e4090100540740c9810a041031009a00c02d0f46c0c4070a0f64250800041d0b401d0702c08034101051404041034840c9481c08143c2101c0001303200da204488208554400900c00d003100c0710301d42d14941021000c070581d0400443d0b1040710746011075094882c0700d0f0640012500705014500c918441e4000344002ea80b0f4009001403204403003001003000e03030300507242c1840c1d042070b4184960001024041c00c103d000c881c1c000404c0c40b0f50a90107070160701d9000580805010303004008592240041c00c08141e941880d00000b5560b11488018608110f03c0802003820 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 745627347 1250 745626097 745626113
    0x203090a0906050f030102072d0f21020303090a0f0501111b0111131e080f01091b03020334030818010e010e04020c011d03090117010f061d040603060c0f030203040b13 73
    0x45c15400001d060344007005032420a14144d0b00652007100c0d0080512f080455034800012030f8814503612010300a50000c03542d4400313000c240440304131841c3d503e48002084030f80301c1402070030306001100c040c0602d0702107a1424038215042007015140c250410070841031000d01000d01d04044440110040c0c4550401540c0c1130300d40103040e0080680c030300401e00003100c4e207141500000021402009c2c1d920b000702c1c851406000d030007442e00c0006d40503040b0101640c200d2003090880081201281c2100708914880301c0058486c0146401c2150021000700380c4001b030343e842806070604010282020301000c0305120000e08001d0074900410300c502c1e000202c0325036041e001c0d0000301e50305102078190350310501c07a00240d5441c3d42050840c0c2e4005007246012044481080c44000c0c100c840c1c100d140700102c1e00700913085409904010143c20001d2008048030020b8556120700c1e0015801100001a00d4000700c400401511b41e100f40e5004050040c01400003281014000d039802c01000341240000143c00e18207800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 745628597 1250 745627347 745627433
    0x2010905060f180f07090b031906091e03170919060b2b060c14090d0201090b030a1b05070c0b031b070c03021c150c0203090a0906050f03010207 63
    0x43e1a0013000c0071041240b40000b05401651696a400e0040561300710905035943d0840349e4034540d404021000b100414603640c01080185c1c014440300c00104c1510100c03010a00080710200c0004814a402542803c041c045498202c00908003401101e102c002c00001303450b80e0303890080d04007544d51581910907601c140003170210b5500c03482e6098a403003401d8030074000e05038100c405452450030b0101d00e182062084046032290000b9000385d030304103680d01040c40502c00407201c00b01d041c45911540840da0302140c1c4050752207020b02c00d4002c99016800444800130924907203000007884814000d4500290b94070070000d050714050464640c0707079511440420000c505c2003040e0303102000c00040764810300c0704201800c0240c1e4000e0300d04580c20382c050070340844c5c110036805000d04003100868545a229006800c003402c0150184116418251480c0014003050301c2e42d48400d40d03050f5101c00420850801800f041518a8120021400d0003565280e54490503546002c0d04510301c00010b03c403404c4c90700030328480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 745629847 1250 745628597 745628641
    0x309120304032f1b15070206040b07150203090a20030304060309080f040f030303050601020a0305030c03040f05060901020d0b0609010c1b031b0e1008030405012105070e090702010905060f 82
    0x40b8040390014484130300b082d240c0702d00e5000704200b0100e1640020403a003159038050303001c0d08aa25280c50000d020354250491802241c540c0c440080444000e40c2d1400a50300070001030010309507403440b42ca4842c5222131500250950188045007002c0d4a030307000f00688045070464200482d00c0411464108054030a512a01c01c3c0b0242c049004245551094114020f0b2480b0740c03420400d580300c0400690f92034824010003000120304000044000e0101409590130612a01154145024640d9039505100e030441d0130010301c0c2e5001c00c04112170b00d00da02440f080040d0a9444a140c01e8000700020014929844050a40280d41030003200200405883c0030040d84c000450707082184200104003642e42c480d02c1003081420000c1301042c09101d01001c0701c400c40d600c074402145400c1ca4480150750700b45c5420840c400703410b40813141e0a0000001d005191151200340c1da5075520711600801c004c002034014020ba4110b80c5005030190020f680041e549e038000074040ca02c1e0045a40301c10501004c441c0f030038030310b03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 745631097 1250 745629847 745629853
    0xa0b18060f120d090302010f0201020301120f02031920040605150705070e0103030203030123031507091e05090f040b011e08011509060501030c05071101110d02030309120304032f 78
    0x25030203e40d4015240800e9134803d0f40c46103181581c2000c00c034241d010a000340580c455445040c0400285241c08222038144080c065410400080009100c0145803030400d694210b00002d0070189144a1010300c0880c1d03234115800c025403401d25020401c0059414050845684002500c0c028004104003440081030f606820000b00d40e1a407400035200e070400e01c10084003481c1500000d688000035404100300031400b8009050420450081d80b000ca00050944400e0100110020403611000c2c0c4415440010700442865038078900414801104002445c0ca80061344200520001901100550b41107620b4482114002202c0510181001840f0351084409628003019004004080144074048844150701040f03519070310070041d010754000e46410320008100700038684c00952518a03090359004103150a810604032050f500d45024803000109025030f20100410140b4081040180b01104e40f07101c0981c1541041e0340c024003c0790002560b5a4903856110400c007921210490503000d483d540c10403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 745632347 1250 745631097 745631113
    0x503152409160f0804020d060504080d02041d0901050f0414010209061902070b0c0307080d0b1c05010507091401081e1501020c0d0c0b0a020a0203060f0a0b18060f12 72
    0x89002d0401208506030040380f00e070003001100398002e182c5070b4499a00034001e96a44030550391007400615004108039240c48007803003d00100d82e040c0c40508050b00401812103511485110708410b40355000b021500301c0c0e070404040080250030355483c6904240c1c400c0c10000c68501700c80303106019008000b2105d41144011a10091000308040d4550800c02d66400f0394903e80d45a072110846440f03480000056984200000c4002a01c114010400c50a038641e0010b500c805800020718000328000c44020108070003590034003806000c0c842d460300900d2900786052450f1a040c88034a6502a003e401814402d1180015140160034084c007110008024a4045181390005e8401c4920417087c841500600c1600d100f09420300f0025503000e0280c1e00711120b602c1c43c6151400c2ea940d1540003198000460080315003540060703d0400140780124034000007040a4540000b02400321801407039802c0c0720314840006e02c2c1b03001100d511070316008a0155007003401107944c900403412b0381600c1651540c191090b20300b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 745633597 1250 745632347 745632361
    0x6220902190510020c01020c0607050109020303030c0319150509070309060905030a23030a150f06080118090b1f0b0729010e1306090506100603060503152409 69
    0x760070169141150b0761501030000810803640c55050300172036405a03010400380181490060050031301144120008101c0c156a81d0100741035410599000c1503d920110030311030098a0f0408c0c03070800001c0c0030420401d020708018502d0785181184620303401401400046280c00d8480e030003c1768095007183d414044013040d4980f0030743c0c0341e105080c1100010000b07803c020300051000740c46c0000082c000d404a00315111062850001c080c0e9180c20f68200e2285100003c5840f05220014000c106a44810040b580740580c01543c008007040d03403890051410030508005030400d40d25540081d02c0d648401c2000240840500141000303401100346041d0205001040050782c40400c0f070518010040040100024403d902c20700c98207010340411b54488400244144880c0d1404d940e145000c3e103c00301d00d403400307501c0d26410f190059030b00e02e107803001c02030080c0040d0b9003602560005140c00d40040441e209030900119207041c010349020105190200300c0c4d40e03c290100501c407246980140525882d0418a0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 745634847 1250 745633597 745633639
    0xc1c02240a0c0605060d020d080d02041a040305060c0c15180a05030301091a030a030c0206210403021e0709020c0a08040803040e060406030210210606050c120306220902 74
    0x5103007110b203c0d082400151042c10000e040d505003550150017800980000c2d0703181c0da60790f0400c0c1c200b0034040c1c1e401d0000040301e18545003410f40d48400580101d03603c2d42141419400c00c00014030740c140c6400c00b00209801804009881c030000046402135007115140e01100700c45039a08041c1603100d521800c0c0410051017000720003103040740c40d035a208118400600c0003210351480c02c0301942e545608000c200f40b001c207004260100c00d45100410180c03920205001050b5410000480051141c0b0300200300810150100181c1c980c1c0c2807940300f81c103081001c80030349581e51140c1e4001c201d1416000704404a40741004c1007140c1ca101c3e40025150345881d11107095039500d4000e4411808003a01040126820782400d100f0030090780c4c0c01504c012011484110300b80c405000d041021118030007040d0041951920911844020b40800d959940da40e446550170646803200500c480d510220b410800c2c404507a5a044d002c2800c804450f02d40b2038604451310952004000410b0041d400070050540e03035407811110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 745636097 1250 745634847 745634867
    0xa06060314041a04080904021813111602031002070303140c090d03050313150605030c04020c0c010e0a090c0503180a02010e0f2209050c1c02240a 64
    0x15039030400c010750900c0404010074030252000341082e000c1c100c0600f0b095a42822881c1e21034018280103103002d07101c50206040707a100754418118003035500326a80380c62070821003a480b0300301e280030140600f40f1081c8024686e80320b041c8111281403180c42d440b204544041c092081200c041d0101103490b003003d4180070300a04a41d840026000d0384a90000f1000030f07468043d62000c001c040c0c20340040c240c590358203640550018000c11b0100c09082010400600c10660140b070a1005031008070703025141000381450304102071042c601c100d00510442203241c80001e50701420000910b80900b1000d210341c00304400c203c0c96000700409908003101c2c401c55a41100055000d003400704039035140c09000001d60342d2039480c078410007070000340c04100000c010302d0130b00d032a0350314010002c3c58544a1404050f500e00110825521052210b0300c0720550f405111007800341003d1141c00303589250303501d420218650703c407007903520000740309a4030b20026070f246001e504500c004050258180d00d40d156800407010304204a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 745637347 1250 745636097 745636109
    0x2060c010605190303021506061b0d1421070c0b04030f0e04141f090c09050a051203120703140708060a150c081b03040b130b070f11030111030a06 64
    0x3c03030101c0e4614a1a050a08881c2c05a000e054201400307a20400740340740250009520040a100e035816002410284400c40d406060041c42d0b5600007060140c5594441c0c4525480a90706010914a1001282d00954003c0403100c0c64181680d07541000e035030b6010032800250a0203c0f2004000805400c18204051000144c440c240508807140402c01a81d00c450315000101c0d0703160000c150307014904008a8070b90907104030352440382a112501602215200c0581b0f50024003000c05c01c00c03441c208030348820003420040c0c0324194000388402d000c542d01e2060b18011700140c114100051107840c4254041e58481d0040340034001e440c100000c005040380c40c03d4911070b100c2c2c504c4c0d51001131035841c03140c000300f842c10300c0352a000d4104015465040d45500100e101c140000606035482c0d290360750a1000300060022400e010ba20f841c0101c0c14030300c280f400d5802804140300100688404a000350700d600b10a150f22000e02c0f8244281900400c0c0581242002da181c205c03004018000c404d0200d0700014103a5032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 745638597 1250 745637347 745637359
    0xf0c060709080c310e0d090b04030b010b070303090501060308030402041b0f200709091a0c0304060f180302030309010c020c0f2403091c020c010801051c02060c010605 73
    0x18980340c5050f02c035544081400c0d03100d0403c14044c02040b11503a214030011206500001802058444400c241c503c1803c40038095007000441e491810b030001c00000141100c1500d41c2d0400342196142c40003200c042c080c140c000b4034041080c07401c05104c0d4201c0803225038494000e0045954918221030150801d9a01b01d04c46c0e0f0900e20b80010343d50042c0c42c0b8016040d200da1301c08002080e00708040d1820300c0d0912100428164082c82c040700d10000300704200091908a400040304e051508001002d514042d414130080103401e42804416034912040e01c0c0c02c00d8200c1c1c000203105408981c01001007000321001042c40148030111804d15801002661082c42444001d004104500c007040b6101c0341d131049182ea1103014030b943c0c05810b0900740300400511900468907011201ca05030300808540081b503d681496000100251455102400508403600b00f40010040f16050400103003051405003c1e803401242c91800100311905003003180030365a600503000e80d50b1400e00c120014081d24a034061503000b08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 745639847 1250 745638597 745638599
    0xe010303140316050901110601174303050105040b192c03070c03050a031d030303070e0105250c0602150c09010915030c080606030c0703050304080f0c060709 69
    0x51040088a100b51a032804202c142040d10200b913030075400140c4006d0410500d5502c43e0b40c00345042116a019188209240603d0603540f055207240440c409940310501e00d0194800281d58442076520000d0000f2070f0800c0107030a20002102400c4080d40e0015000d582048280001e000450000b180200c000010070841c200703000c82e02406441034251031a481243c3d0942145106040c1010850400c1c00305099a26200080d201c004002040d40c10554068000303078120010036401110400c0300c2034801282c880003501ca0030000b61203000081c03038442840310703c01134052168481d0084540b5005894210105150985070418544c41c444c40c00b20340060f000c050210f6400d0000850043c51640406600c21650318445850aa03420032030701d0038103001051401049034203651030044081c0500355400201c003051484000d01d4583c0281481c0e01604080050180c0e4800b404100c500c03068141c1000342d80da0b00e452805880030711602e405030802480200b0f5900703154a0100c2d00700d005800c00c0c0d6600c0201 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 745641097 1250 745639847 745639877
    0x6050708010938040203010303090e0a20030405120d23010b0702011b02150706050f01030206271e010f080f010504051317040f0608010b310e010303 65
    0x3c4101010301440440c00c01c1a105403149030381e00003003012201e011062080000c3c00c3c0401c051360400e0708102c0100d1941d4800f4411600c582c11020741c803981d00340c010320448100c0c40400e007183c800c09618110078500000007400f8800104588100b0b24445040c050b40c0e04c0b0349802c110010112104050320503003070407080100190362240e800f4165048040081c1c5400f000380d0044d10300d804206411080318440701958070150303035044c5215040482990f5100e9460403035182400490fa0000c08143c00100305400500c00b580303806080e20048607001c0450020380030b14045c030011084090721041c0c0c4c4003400707002c0d45603205038901c0c0e140390f046800e0325030281c7c101c04440c09403420072085840b1000560400010401da160513000035401030300c400311040c0d03041c42c5902c56202c8044a40d8590502c40e4000034208038180d030000e0480b00611043c90310019950420300640710b03500c00c070b040c01864000e0840d0b05000450a03c421400e142035001d000f4034107907645600c843d81191091000f80d000c10840e4041c0d07945 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 745642347 1250 745641097 745641101
    0xb10030605130912031d03180114120c0f1b0a0b010806070806060f160f02090112080d051f0f090507050a170a29040b040209060d11120103060507080109 67
    0xc0035072105503104141c0c004c2c44210300803d80402d80300019402000500940c0341d0034002001c600e079002103039041c052061000036100440079140003a001c0700410511404000103a1a41c1c1c1186c04101d0882d81e0782c0c90021074000902400e0280a0a0401c81380d503400321003400071b03651410038403e004000041ea03941031001d440d11011220350b40400d40e040000b42507458a030005141103007003e10356a0900100078554403902128007011903000c0640a4902d00303515120030717007d00514842c0404400e01240707940e41a02c0b401149214560540c0381c401242d0303003075100035080068444030446a11429517542d040c10414400384205541586041e008c034800790721034012500c540e8616202d07024083c000208840d147d000092004c1041582c0380b0758a203008664800241e00300a40300075400c00c08000764104000c80d80d013108003603c981c3c41044514851f0b207410f000d5558902182c20700041c001c008c40444200391160514400020403044000700811030541d1015020345403941e203481c0160303220610030701 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 745643597 1250 745642347 745642361
    0xa080c090606031b0c07090e0a11100203070f02030705100503070e090f0601110114070e01030605032113030b0a0609232a0705070317210702010b1003060513 69
    0xa01908225010510718000300080515000060842e8002581c7e0807620301200c44101c91461903400243c0f2946c140101c00d01340205000c000c0300d120361245420702010f5624418880000c0010a00048180546d45c2c144940c01c0140f4001c0c08106240001500060040d40b080b5040d902196030b949400d45103080c608800343c1308010800c1c036201305888041c010344080340f00d01c503404020343d00c640e418a1607012200c841401034843c1c1d100c1c40001d442c40310001d07051f1a00ad82045009038000340c10070401c03074443d440069516030f40008aa9503150000384070461aa400d4001a0140029501740500c50a0a6111008032140f181e004c00c41c00d040150341c041c0111203c41822a800c03840004a10000020484010320806004070210105ca41c00744000300c5801054055a0503044480704000303101c43d000400c003c140c0d424402c0c40c80c0500c200c05110005000441d20325803c011600042c48050007540411081e40d0300030200300c6a819100c1c0001c0140900e40034450041600401801013507101c0d000d082 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 745644847 1250 745643597 745643611
    0x40f140f010f080106080d0509040e0a05070f060e0a031103101128080408160c03080a03060e1e060a170a05010e1f05222a03030f18050a080c09060603 66
    0x50b07824511f102140d17a03410102407541d20a45e64595030b1034801042014200b4544182c000e003892516220350760010f84459030041041c84042c044d4206156a400d1441c0d0584e90322000448400c04041c02003803500f019507500c1c40b08c19140c44003603100c880c0c0a401502d0114810703003009042c0b6010707002102c10500c166103c44041818440424009200031000e41504000381c4980e510349040750b100c2c1320b49141264019161804000b82e0303030040c254140600d202402d2040d03410307842402c2401100c0c52a0400002001d800c01030803020400c503030b80e00701400300140701000840000e149101c008580764400740004644640c43e10109021422001c0b5506840c8000c4002ea2240320600c644110080c0400509400c056a00304901c41141d45602c0d10b102d00c2349004a031404005176803402e5400512005816440150001c10b02c2000029841101000c0412951620a0040e113812806050032040382e00715560040c043c0d04007007000c2400040700300a2401c203d0b0b03d401140c580c0814007066120603604e00e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 745646097 1250 745644847 745644853
    0x160309050a0f02190605090a0e04030504060f050913020d060501181206020c01111e070f030e010c1e02280b0703050c06041415010f05040f140f010f08010608 69
    0x1490200340d0903506000d090b4009400780810b1445642c0a01c280300081d040800030078001f01d00354601d07040c0052140050008042d44150780c2c1440d45026040f03001e140b2800d001c201b000b01c4520320070f6200b00d05840e4048000740c4580c034140d100c441d00001a41110b031085152510b480d0001965610480c11002c1c0c00751180c140102940c24240204a2245144001d55145808206000c82c8030402d01c6648003103191400c0203a11005900b0320317403541e49401d400e500d0951105000241c08181050010706c1860b82c941001c4d2040d00f558001030340c45103e1000081c0002d0300c0d003100c0d104201c0760130401940513842102c540f01001e6a00708101a0003160710860481d0184021062000c0340e007201c010040e86d4040e00f001d82c205500b01d8407003403034000708540495041c11000c0c80b00301051000c00000ba01c10305a503405550030360401d140500b071031140c0e2084a00c9940c940c64018482c81c111b5002c10000142c08080300a24540464090f01880f4203214854102503c0745001a1104040c13040c4410355000e0000303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 745647347 1250 745646097 745646113
    0x7030e010b0a120302010207020315010f080604050309010804110a0f1e0b0724110a0314130204110c0105040b060f0618040209061605010b01030c0f02120c0a1a16030905 74
    0x50748445030074000214150342d420030540c009640c04000b10400d0301701412f052007256041c500c60180951566110a000780d00003000e020020b07001000ba110211001e190071641680c4074241084c030013884118041c2c114078084000b0902080848070681030700c1e9404e4500f150900c1204450320190058401c0203c0d10b01c0034012040010345036440c6404911455030354003442d540340b500c040d040b07071944804c1c0c004501e4001030302c0c0416901401800c0c482c00a11300801d28514013400001d04901c0b07084002031189981d0989a1074401c0309406a907407034070b04240208818580342c40e001c0c5c821075055440c0c504c81c00ba040e190016928006040740d40c2c00300f01d442d0f601c8924455205000203904244da919901803801c0c0800f6035422440120244030300d025000124140c00c244002408980c0b541107230104001c401c08840343c3c0d00b900003408244c5494104442943d845c8200141070402c1e40c005001400c0b03881d00c0300e0300984446400324a901480c0c80345105015810086000c0c0c2c100d500c90180103141e46c112008d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 745648597 1250 745647347 745647359
    0x10504030609061b050904050c120a0507111501080f070f06080703091a0f0105040b0f01050309010b10021e0a121817100501080105010308120a060302090f07030e010b0a 74
    0x40089106000104004010960b9500b4083c1d10550000001c2e1012450468511f070130b00a6540040700051140d290907031929800400400050440c061305441ea00451181846110041d00003588002500c105030300b42001c540d503c0c4000e2003000b900d44034840e2642d40748807010840700200d68007680701c0715500307103803510960703500030000e08507414540e450145801003606210080c0c034451410281c85090303d040c1c031450401d481d060300030a004514001103100d441c0c0724201d0044401109003071850701e07652a6124240540003804403030b40c2221500140c52405500003038107070100c5510502b403151500e840500c0c07035540e107106000a420401d0280241c064140a40c03120b41255200541641d031040d15041540310b80d004c41f0f44515000c0d41b010803041c070b44450921580d070240518000034485545141c44507140750280c42106400a1072920104023030b550302e64462001917a0103021032041e450701408040d0944030440f480070209040c401c00030525001842420040c807001000ea03003103141081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 745649847 1250 745648597 745648601
    0x306060703180815010914070905190b04090b030f03070309050918120408120405151b07030501140f04030801060503091f020a111515060d050403020a110a03020105040306 75
    0x200c2d010003240403020300421a101d0500020089440e1225102880d52415003000c0403912000321019410300000b0a1004040d40420440c0499200302c0300d80020609400182490340e50a60125580b850f0000380007a071076042d50018507580070110b00f524420a640f400968803442081d0000300002ca03607040501503490b1003421030b0707000258807031b4100b4440400d030a41d42c503180000f00c0940070890040ba040000300b10030084401c3c081c42c00e443d020704042c0380a01103081c80d40c80e03c0560404180c040740011400c1009036400c011101c4000c225120b06540e81081402030001c1c41e00034005000030800200310510399070680e0701a940c180e580300754681ca1f014048400e600081d1100889008050a0b03101e0030301c41100502001c4600900141d03602440c82c405410402c13602142600b64021591961004e040c000e8816803006c920602d06200c2c0100d100000e4861042034079001c59a40b405040c8024590700003802c0800501c60400c46844c03070882002c10504010610001340042e00070002440003032099 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 745651097 1250 745649847 745649867
    0x5130e0c07150504020f010908031b01092a0504020414010e1c050601170d1b030203130e1e01150c080d11190302090a060f020708030a0c0b0108030306060703 69
    0x200642500345481e6981d0300341d200c2c0c2c1c1c1034a181081912002440190b26009462140c9000c0c2401d11080340c6181c840c18070303268080c0209810380a2070031006140b41c04003c1d04030184166014005081e001072a440c20040d0300000c421495000d00c4543c0007007124242842141c09a8071181c80f801c145100341001152442d194000e1960012680020002100204042c00078010b1199019102030340c10040d241420100d480880c0c90240d00c800440707149145c02040e4025400d8030a101d15070030000d1418180e16600c00e03480300c210751035903400c000035440301c10130540b60142c8108102c03a20765194800c044071465200b0300920300088204540b0043d0280195120200180708540340c40c2441c0b5a04003c20843d070b0910440300034800300180c1d0b00500c02118030030000c02d04040c10f00318144000480440c0b0901803501902d000e2060b40132481500324000c01000c0020b04800080307954600c00448000d0001c1d84d034160880360340c1105000840d420302c02005072449400042d1000381001e49a45048491041c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 745652347 1250 745651097 745651111
    0x1a030907030b10090b0904020603180c091905060114090402090d0c0602030a120e060105060f1306031a0f150318010203010602060708070e01020d0f09170f010c05130e 73
    0x100340c0000002141c0c0154148540c0309031100c001d035a45409402002c0d2a20008030500c0b4424400030000140c0d030710300c15250854410100011a88544900c1600e044811491564001e1a803000c200340e02070070059800c0d02c50302d04071003031100b0b0302d43c90300642d0180e80784102d15440040a0103464241c0c1001d40c05000b058400074003501c11050152160800b4400170740140d001a0000101c0c6000c5035000315210f0400c0310740300401c20440480100f142d4913440107001d014070407180002d04420507003041040e6140241c0200849104c0eaa40b2100600181050421080c4581204c5505d0140c0d203042402d007100360b400500040b0001e030846488042c03650000744001c05c0d0921901c3c603280003907001d00c0a0350184c89a500102400c2c00c1090005e02446802401c00c0c0070009204120300b5240d0380400d840040d01840d040c0790f069094080c000f0346045809400c0f848010751400b86802006000203038554991004100801c40c242064104942610443c1a12184010300c2181004a91110f0041d00d41c400c103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 745653597 1250 745652347 745652353
    0x150507021e060904020d0b0301150b0f03060409050313080609010c050910180b0a08010f05010c0b060a170a0b15031b0402070c061706030c010f110f07030b010e060a1a0309 75
    0x10f11030000f400303d03081000d0450015990301c0343c4c0c02250409124040c441d22183c81750002e0685010322940c014850100c0c000044840400441c80c82e0b1125001200e095502100b56034a0300c0100d0550460f1100038410003c8501c10308020a003c402c0600c180070000d01b407a61070500e0001810144103140240d10001410012a4100e8007460042106203401405003200c0d650798442010400508500060f000761032031190070030781004180c0c0c000042c3d80940d64460107405299940f00c0c0041e218410f143d01943c000351515003110040702d004030307440b290b240c4120301e104007503160341c5035007a800000e4441c1c140d003607800038001d140f144452450314845500020809458540190380d10707120140c1d00d0f0702c402c0110b80105c0d41d0804000b00c00b00c6483d40000d0540080800c1e01e10100000c1c907086240400000740f01504032040c502100030301001100000c0f103c2150811903803407510f02c0c1509802d2003503180882c107420100315103142441c40b410440712070700e000c000300009003002402181d1000d070800f41c40b44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 745654847 1250 745653597 745653607
    0x4030f11090711071a070b0a090b07050418090302150c071a06030d0e090624040e060a060f050415020c040e010c03150e040f030908100501150507021e06 67
    0x5598044240c2c4180541d43e01d000480340011101031910425070455404510b200781d11260045503041514109a00417450303c1040e202d44030020000c03c200480509010484410048541d4220004000700d41807502c1c0f012806480559040032184004002001600103002c20b00c02c444039010940d8000031010541c40c1b07019150303500c008800190020707140d903180700d11341040701030b283c140400d58400a10741041c0c00b41840710070010302c40030340040800384a1044110302c1c09007080000c1d201d2502c01d01a40581d0b41d26074441007840c1c6a031100300c8030140302c0c0c0c201010205009220fa41c01543e86c0405803180303070820707003000c0845440e9400c0e0044c601c01c40c0302d030340b0003d80b0310b64a500801c4c164001c001d000284c4000101801820344102c3d0f0703c2d00d014010001020441c0040c2040c3c450750141d00030f182000700c04400e01d41219081101d03030142070907202d284503284051070380f80d00460403140441480e0321074401d4054140e501d80100100a5480b506044040800c2031400645c00358402c2c000b05002c1c540 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 745656097 1250 745654847 745654849
    0xf090b03030f18090708270a02090103050a0b10081506040b040c120c09060203040b0f13240305041208091c030e0d0801050a03060f020d1a04060b0f04030f11 69
    0xd60041002d901c3c0054101c11100035900f810707505560401c080d85406421490318010046d0451401c54001310600d4502e1030044c2c0d411400c0c0204282d5070b40c010034008080d652418a1940c4581c090816200c0c280388501181c003480340300341d410045070440009031201000b13100c078081080c58020031207900141c8071004a20a41c1d1144260141c0d10b032140c590081d44054590290104c541c3c2e88504424403030f08410900c60a030300001600c0440d0000b440c115a0781204050903401402040030500300c0030424103012818a040180c040c1d01081c3c18212188000c0d1204011025942c041d80c014000740d1001c070000e0940ca00c01c9280ba680802e900084441c0088440ba000071710200340548040040d982e00350b2071050390010321906000094070b191803441941000c00003140c590652100802e80c0359140040c074071400482e011340314a07034142001000600417454581c0c003900d440310740e5140316602e400408100c024514007500e0400d0441c0406c3c40c01c0504564609585108103001078030a03510001865002d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 745657347 1250 745656097 745656127
    0x6090602090402070818010509031e07090513051501050d0b04020a0509070e2e0c06060b0a0908060a0c120b1302032e0e0c0a030b150901090f0f090b0303 67
    0x11385885006010f0303850104000342e81041098940d1a410460200030111540c1e5000039408200c90110741c0c040d00000c9039800444c5004002c0c0e200d042894101002c00c800e42040c1495100424000d1040d2034100080c2c01075085003040901500b5441044690344c03902103441c0311007490344284007400441d18640c0307640c0058084101210780718005104c0040500d2a030070050301000b0f04517440e03400d1601801000010303020030100b10204c04104000c280340c07801400001e03048540140b29140302c0903544c070320046001303294500314001c00e0780e10f01c914030200d007403514984900c1c0c500c1c4d00346948012500b4542450b480c0a804500c44003a0300c050541e4041c468440244011401403d46d500000d0002042000b804104003460541c0c64001400c1c00b400c00c008480701c5081c981c01404c00d440785130b0b280b90201d400d80040c0031042456030000f0551840c0250200c01c0c3e0f0084c05009070980b90004d9196a91701c0f04000e001850103000284100d0581c00c01c42140c01d03030000404400000c041d01c0c103040342040e40d000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 745658597 1250 745657347 745657357
    0xf1703060a170c060c07170607090b03090a02130905010203131a01030b1303140307080103030801050f15130e0c180f011b0305090303120a05100509010306090602090402 74
    0x101444001080c0180340c40d15486080090107000c02490150a40c120303020f0b180e45040050f50700601001680d0f50036000c051010b10003800d40016148070b00342402003000c2c0e1707403c0e04841050100c2e42c008e2000c5145d0341c5102c2501c0c480c00d192402840700c0c820960a10400c2c3c00803055581c500341d00c070030341c4100180b400e00144d40b0030075040100e206110320310705200703801003011260f028005400d40d00600120319529400c5500481543d070840c85d946052408407501d0400c5032100d9410140442070250640c0c3c03105003603040360300a0b500c6d0411a41c90b6420085900d84010000354415104d500b08103850016001034040e902044802e415800e5441e1001d007070044085440c924406000600a182e40d50440500310301d203202542d182da036400a400c000b8042800341c0b9142003a036000907450303004161040048505411025058a03103404030304c3d81c03a80a545056500540d003070704240010320345d003035164254011281c00a01011050f46103466a00060048a138252031640e000c000c983c143c0e80703460000300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 745659847 1250 745658597 745658633
    0x60628060509150708030f0c3039040816090c09050d02060903070b0d0204090612051e1c1110050f01140f03161a030c040e040f 56
    0xd6510a4402c0030459051184204030580705002e000500218000c40280c030f0b40b0030403c2c0050303000c503100e403614404903010341c4900305010340d040c90108a4114070101040e841c85809140d508407500c0ba00310300c402800d1010743d03c551141e400850142022000e000c40b200998001d4516881c0c0380d22240c166080000054545811178244c840410200306c80e4810030001e0000ea01d041000c5508044c0000d0414065100c00307880342c4030105d864401686c040c05200003c0c14503905a0b03a8601d202255030019402a2050b1840b10340b41c100d00281c6000d65005910840e588040548510500081580c0b801d000d5036001441c1b900c0790b44031001c440c204a1141e607902c00d1454649880c003054000c5039600d4180c2800f0446646030410051002c81a500e601c410705592486a40c2c5224007000f80110390030811500003243d141c4608400782940008010075042a10100305001c600c004014040b0065403000395032603143c00c24100400c00001c000f0031406c03500302e4460050622640340b140c032424102c1079014110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 745661097 1250 745659847 745659857
    0x140702031903080903030c090442050d0f030813080408150c0c070312020102121f05010507050a02092503060504060909021e151204030318020306062806 67
    0x41070606030800c45055200b01e00d640103514600e415820540c1e03030301810704528091501d480d1b40c00b4462624071400e08000919245100e0008524180480c408210011144201880c41004109401c01418038120660000c9064a00404a9402322074000c4000d00406516401303038110030029035050700a0009006000041c0714084040620b40500356000e0f01b280c450200c10880c51402510115030401101d81081d0349070104182018268068495403010751507164080042000c00f20391044203056140040b080c034403005498100549992283da00090481d03806590190010700c2c0440400d948003041080241d41103c0c0f091980c49400d104d545a44046a03d0356001d200d00d050034401c510050156410a2007030000e80d402085a6010080700c850045035200500e84131500c80c801d05c01c9441c1d0a1007100f82e5144046150f544100b54140c80031070000382455245918840d0050294260301e40050103407119403503002c10441190030600e0200c141c01000711640320350943d4480c00f240105015110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 745662347 1250 745661097 745661143
    0x706050a05010e070e0108070e0a0303120c0201090f11030a080f2d041a0c03040b0301031208040b2206063803071d090c070308060a080c0114070203 65
    0x580d00a807030050300039a000750340072400c01c03031015800b15503030203204420309044485442d1200c0849004281c0010b070354009400d92400810503912410544010b01159010443c00503c0302e0202e003a02d0041d41c0103490306010001c5140481d04100040310918001011540c00310100d41c1c0700186508074054400303c042e408600c2d1000d10000540d00303d0b20500c800e02d21100000250b206118a000700d0144409001240783c0240c0c00c6400542200d04e04043c203001c9035101d039915041001c295009002c01ca814910741c0c480c0200813405000304600669001000041540e1007104c90407001c0c1da0109207100c40b005560b8802c0100b0319030320600300544441250ba9600349a58683c01d140c08031100078045480107070407110307822001e6403c141da4001c1c025240c041404203103900f0f1661a58003d0b10590350010021083c00200c62100c40108103140c071a40300c004a6542e070320f08100e8203a1607440381c4507458210590300121503106a01c1d008c50443c9641d0024200b04298010034904101c900b010400d0754801c1c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 745663597 1250 745662347 745662361
    0x12280c0506060111100c02010b1306080f07050105070803090307022812150b0a170c10210f0f050a0b010228080901051b0d120e030f03090111070605 65
    0x8541e001c00282000c03c003110301104005c2c0e54829501c081d07403916541c1c8510644040c400c1d00510001c40d002003410410440d44124240107143d14450146240310390350000004510203e4400225a4161070302e0303081c410107468040091340024000d8289000070469900140e0312441850240003a024940c0100381010307200001c1d455090f00801d076041407542d0f840d000a0784004465981100b010340c040b80c41070005011801c04501078228045517800510070100b04200061403543c1c1580c104c07140d00001d030303080f8815900a40300c3c51039500003c1c4012500d410240b020380041a140b44400d0340020b143e41c0960043c41250130940e5007242c40c6d0b440c0c82d490007640d0b0f41008071801000791110a04c026018498000c83c0d034100a9000504103180812900740c944c1c0208290380703036440000c01d001610314486600c1600d80410741d00d444040390580b08014000304544c800c0d6909503c9840c02103242c20780b0014421031a030001840721782c2035034807090058401c00c000b80140c010603209103008105030900340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 745664847 1250 745663597 745663603
    0x5030f0d0e0a03080409090539090603101a060a03020304150209131802120d0206091606030b060f040f0303030e0604120e130518010f02040812280c05 66
    0x110340a4400c461905051011851020031501120075a001c009609035280c80e008c1c1c20143c0d001c0010300c41480c20b5000880e00d180c09008110009410004503407044002c00421402c4417040d184035030160b100d0807800c0c00c81c42e002d50100c510203500040e400450f003854000186a68000c503242000243c010080c00100009141c0001004400c0c9006504021682c40850300c05204061080d600e951213012000500d000c4000c11401c00d50054807960b1141140c401d255a5039040980e00c200501c01e140c00164070107404101044039052100404180500c0d04c10200d000d4030505c5e80e6650301910800005512507500e1004200178038000c140c600d002c40c0785040190850b40b08190301c20080e08500c082200007450700480c12044401e6042142c801c42c04240811070b00c00441e03e036030884500d4141071010780c508030b01d45000080c400f007000f80113054840c281074069019a09c50f1a1880d44164401c20812690001409800200b12156000e8500c011260b0701480443c20700c1c4408207055a0510702800014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 745666097 1250 745664847 745664867
    0xb0a1d09121b06061f18030c120209130b18030409020309061801090b0c0a0c0c0e16051e070213141005010302070507410a05010f08061905030f0d 64
    0x44600321013080345160020b0260607140c0052080001280a81c03c0c0c1c40c0c00206c0d03a4000e141c00100040c406511103040e9481c2e00150b0f48260b02c20480c240010701e18064291070440707815886400042c10351130312074009030361402c0140c0d120303503d00013031002060082051000d544551030410040406051480b0b0383c22a841c1c0d501800d50080c1d041043d40c2c00401c0a4041ea00c0d004846811180da650320302d00c00440303907041110001462001100c0c0d0000e40002c034000315502030541c10918011984000c041552548581018004000c0e100c0b940c68584001040284c510303c0c0c000ba0182c025812450b4403201181c0254403105880d4154009004401100503d044058482170038110b160034600d480d015589e8005101c0c03629600b0810622110250a6000600d1003203001e007100d02c09020500541c00e544140b041c1500c2c002c500081000495610a0001614800c008d03204c00307103e901d0740c0e02841440804900e43d012613403052500010507803000c011003210f400444028081c03404060100410030380361 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 745667347 1250 745666097 745666099
    0xf0f0201030b01090807270c091a160b0c0c060405070f0b0a2c030a03030b0f1804032a080304150623130207150b0a1d09121b0606 57
    0x1485410b0101720300015018050328012034984030282114441c00b14065600a480d80c6883e082102030b0840c203401c06441004c0e1400d0303041c400761720356000c0c1c1e402d10316024020342e241e0203071901110600841d08021805402811082e0410700c0c0c000c440b901103261000640302180d066000f008108110702c14040c6a030060001d0040c0e05103001050031000300b95900b4551544028180300030740d5882c40d169101c6140b450007000c1c080c1c540e03079500703800c020740102281044280940c3d0049035851035494803242d80914010200e843c100903844584040301d0b03080881700d000907040c003204886401d060448207040c4500303202e00a41d59aa19251404000341081c100e03042e600c45051150034009403443d101407031810060408142c0c9800706c0d20000443c50310250340f08400d0f4500c00180c6c081440365410060b50311440303048090103060281403d100255800d44200d40f0f1100389101000351031205030402c00d07000700f18142140c13000111a5550344a82d03010700c45000c1000100480310180810030b0100c00c0d40410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 745668597 1250 745667347 745667357
    0x2060403051b0c0a0b04140f060a050a050c120c1b1e030109060f090c0f050f090a09142d071205120310030c0801020328090f0f0201030b01 61
    0x40640d805007903402600d114a1856809074030034203182108000e809241070004124104080d80c504080040345c0c01409502d4885040c20742030061400c01d903141c0401160050b00341031402d000c00318215000d40003081c401c41082801c004800c0c0d0560104150141e6840e196190f503a1440d401035003500d007000142c0c1d000c200311050300c10040706603240c100751503d599080c10803802c101c48060000b40180b01c55a0028111490101c1d190ba0b4800140c0c03241a4417841404201d452030b40f00c606000e040e00c101d00c0f40550180b02c00d50220044c1c100b107001d181d0031200325400420302c0c06090380c130088041c54031558050301c1c1d0310050f03010f8243c1040c6180322508104c019510180c00160600198440c803590089150078820501c0c0fa030200070080200c03a55183c16103013101e80320300742840242e81d07180f0a031200ba1070346062903401060005040c401c484c024503942840c291000c210f144584000920864124000e41d52040004049804071005180a511514502c0c1030301d4020320014080350300359882d080c100a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 745669847 1250 745668597 745668601
    0x5040501230103020d0222050102151501030218040e010f060b070f11010e1509102f0c030d0507020406060906050313020f060703050a02100b01171e0c0c010c0206 71
    0x15103001e2005076000003803070301607500c078006040035020b0321503141050f0907105410099400503088001e00e8096070026829070f0305000000040300603510303066a81c080044003e0030f4001403507000f94000d2000e41610b4840510403005800060100c42c41c802005079141d44035502001c0c1091280f14010107807080940c110308001c0652aa04141c540b00f590003000010007256084a50b801510508001200108845078594240d90480c495400042c000c0e0b010740390103a001e00c00c150040c030801b101140856200123000786400320100c6522058461403155004400c040141c0e5107080c0910060303011240c454694502e840e1041c801111102d034030880030440c01100a0102e9507104040f650003000000901030014803500024650101c5800450380c0a10001015400c041c0c000020304180b044640940d0102400d440180c401d0b650703582c1c40303540042c00e0844030070800c181140300075800c0000d4400700301c20440400060641c505c02030780c2c00c000718480030900c602c00b44024020100101c10502c0545003c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 745671097 1250 745669847 745669889
    0x1031203061e05010806060904020a0c060b01021c05070c08060907031a010302010e060705030c061302090a060e06041e020703050c0f1f05090c1801060e06090d061107080408030405040501 82
    0xc03049900661381000442c3c00828400d945901c1601c841c080300820440d9120b48006019144181c020001c030781880c24000c802d6000c2d070010403819800c0c941d100356400d4907400080100d030301d54840a4110342101020a001c59454030030891148559018002000c58038250304180e280760380c51030038026803144e0013030050005136030016404403a4001981c5054503124140341c035a0650040052922a52085900300900b04038075580151100d402503e0f51500c5480b80c00c980c0060350320714041d00400b085c001010444600700350f400102000d5803140d44022101250340840103a0748011015400100c1c04506440040818040c00e040b1142d07800c000c1c01c040014610500554800d40c0840500b25074440001e40d88060500c0700e804ca5410040503d010034140d020301190ba00c40a006020004100290008481c1800c10480b0400725008120300318100321603071004003401c60141255680c91041c804030001403d1000900060601c0101650b107441c20401803004840059010700e240755140301d01d00340c0d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 745672347 1250 745671097 745671149
    0x7030c09090e0d0c030c120207030c12050607080703140c0306010f0221280c050c12150a0615030e12090f040c0e0d0629010203220b030103120306 64
    0x150f54189800403003218202a649440079000103801070020700c03c9a6005580420118103883c0700b5800021140c0d200c90403121040407140008107540d01c580c011078103140c00707540f686500000e00d181c0481c400702080c00102c1c4201c4c0c00d031511007144c01e0110074001250307044200016001c5851000b0446100c070380920b05104100d5002070341c08028001032b108015200025492440201000365011001030990000c0c211460fa81d0250b51600031000105081c5c9818189120024100d0004000801c1318090b03c11120b0009440c503881c0980c0c031000001c0390503110140440c46600340d10000303158107041801d141000d80101201005600401c00d81003550ba80d00709c06112044180e0300002c05d04000d41040c0d42d40c410400e0082d5201c2080040d050401919820541c8030911038201e2075490030b20002c801a54244c3c13461403901580062200150801c17482c05003510004075008410a11661490040f130a58002e030002e9034044510300083c10440d4142c0203003c010581c1e80305005080b00e140c170707500d00d17 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 745673597 1250 745672347 745672363
    0x130504050714060f18121903081f030b07120605010f0804030e0310230601090b07110918060f0601022805010e03090307120f02040f090b07030c09090e 66
    0x122026510741c0b1111526141c0075a0300c89502d01820645e5166050081c500c1084400c0502d03103d0b042001c405846c0303101c0450b5031002e06420000c1035030481c46980d01a20188001818002c185a59180c140524880d010250f402540507030410034081c100450010104000c2d0703a40c88005c507040041c2080241d0f4400f01646000c010b03441c00700e00e43c0d103603850700301c441807206a032041c1d16108000304090304d00b2083d071107502003000310606508040c01410030b00e1229802264061f0110b4900c0030200503010071030004101c9a031180007019103441c121700001e4143c180c2034450000d4003048249640d29102c041000c56041081148140700c10b25111000035aa1071168519040c1414404a102d04280700580c6a0703060b207134020000c0c0301c02d21900c040c045d62500030300c9810b8803030701c1044170002d42c81d04405070101c00e20fa005951010b002140d5028400603140c0d26102d403070440d541e43d00c00400f142165507094001c680540e0042400030740350303500074181c68503500692126481c11a8141c141d400014043e2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 745674847 1250 745673597 745673609
    0xa0f03170f15031e06071d03060703091a040f060e010902030c0f0a050621010e012412020d0504050105092a060f04090203060301050c0406050717040f141305040507 72
    0x50405142c01190030711a0f14000c0700d1032424502401004060007084040c4038a00e0b955964510b414103541100500081007a03640d015007215011440d490700c2030300003044c09401021101d5000e80180c6500708100c1044500355826076201c00c0000806c4401c0c01041481c2000c80024000c101260300007035114900550050705c54090048140f0040e00c403000c046006010050400d0349600e1407682003900329400b501003178401c440d410000704030840028005030580f900c000c032009100c104180300a98038400255480c5c103000c1c0d4072501078800302c401e000a010401461002148034101403802d1070035100c0151031275000da084051200541800f4546200007040c882024a007200c0154000c12018412040d0748140d422000801207114840c980045025080c00e4000b08010760300c086482149016900680c0b000880070008640415615440030b00c407000c4011140d49803c3d907a41e0004205941c5500061551000c1d4214000070302d451807007621584001e010034006882c29035680b44d2104901d021f82 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 745676097 1250 745674847 745674871
    0xe061e03010b0304120c02091504230402030f061618050d030e030c1507080d020d111e0307050715060807060f141206010c0317250c08041701020702030a0f03170f 71
    0x11003a951a2f400400020004104038840c19200000050628804840c180e0180c03090b200d03004048040004d40602c114500012a18070011034102141c41a03a042544000c075440f09401048540c0c98090100e02c041c402e0700e40325407404400c0141410214042c4c06a80308401ca0701070025020840012140c0d11948171003241c0c0d440481120318070007800b4804400c04424a00f01078544068528001005000080311f5810343c080e040d108888598402104c00900041307041c040301c0000703407000f4035116046400c0c04000ca802d50700c0c5c0b0720072450002141d005000150080c0c032908100d503000380d0100010b0b0911040a071078030720f100711041c0303000d2070241100d81000381c41700022052500c103080075080b85102e0b80210040b400c10710031030203044030002180c1e86460010700311800c0f014054070141201c0d40d84008071900345454024a03031a0440d03600b0601e8025502008500c005075010701c203150f4280e00c83c410800e16a009800e0040070110074422498014032100705201d90440500d2401d58407051110203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 745677347 1250 745676097 745676131
    0x60c1801020a0605040b1b0a0f0e0315071e02012310030c0b0307090504050403020a03140405121506061201120f0807030e09100302010e061e03010b0304120c0209 71
    0x40780340500ba668003810b0b0328a801c092004020906101c10f0044d46080f100499031080308500c85003510600c000710000c01c400d000400100c900480e0400340b4240010300380e075298504801509005901198200300040001542400300c1c1104049284289001c0c8000c001c05050040d0040700c416154080095401e44240000d43e143e6070700714150040c50340305441041c0c15540300c2004046410170b6900c600070a201c110081800c1c1024404c203031066405a0040400017000c0d02c094a180e449481403040c0100c0070040820030382c0741c1e401c4800c1d00301500c000810041c400480c8000d440080500020310441003040002000c5444506103419503102c071b5220340d8903401c2441c0181d584601da0100911520f00401e901e018541c00181800000d5019103ca680695550640521003009408000e01250750030000c08410304241015040204100c51521002261580e00021542003607100e94000e50000080008100403e031120030444524100705591603c0760740003e1540300700406500d112458103030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 745678597 1250 745677347 745677349
    0x1080702060f130807240627020c0a050705040f0506090f0c1908010906060e090109020d09020411191404090b03100e06100f0e0c0c150106050703030b2b11030d0504030311060c18 78
    0x10452b00403078207150441b03110450724a0000d40b501308030310030300784158500800c8000200b094010103100d210000d1902c43c0303a5844c1c080302a00800b0107800c0d4401d416050003540110b840004460b0000c54943c1c4030080250314021040341990281d402800c10007a241046400603250111038a05540d1403444c056220000c82c0c9110b4000e02c11814082d40c07090825a916403000c14100080c0701c0b044202c10003c3c80320302c180e401900d02c48511024511201c1080108025030b5145500c55a41c90382c008040d0303003809009001d02010b44040f600500240e402040500c0010641450040024600c1880072442d651410810710540c41000302404144000014402c40b1f0328070070701900303041c40903840c0411140d50311540014141c1d00100c000f00c0100b450702202c1c01403807510a14100d0350a080e03400d901804d0540f00c810403200004828100d4181840e12a17134003695030300340042e10b003005080c1d81d5552102d00e1410020109401090391f05e003160403100c144440c4c000200b08540e004d603001c040d9541c444407000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 745679847 1250 745678597 745678601
    0xd0c03080a05090901150219031e030f0c08070219020d08041412010b0604051002030d060e0105030c0102010204080a0201050a0c060509010f0b060a080408130314010507020c01080702060f130807240627 88
    0x61404c240c0d2b112003201c02c0c00d87d6030b01a4400c060a5103420030812412040400546034080140c0722000580d0002c240c104540344d03001c080450440c805450140e00303120544d5160040c2e00550022941001d0100c40c140407401c000700c6802007003203880000c1c0840d80a002c00b10f02907104134000c1c0d42c052400075000c80c0150b8020000c070741002801e80c20800c0929030704c20801898260a020300d0b4800e018410020620f58414000d4030241ca00c500007504501a0701e5005490942c8412a1201482903500d040400700d0b50384d100703d5108001c0b00f0004210f58511040c40400c0307540c01d5484503c00c1e2014004800c3d0154030404031a8080e90102c00783d075403440198401003c0290301c0d032004024124003414001c40e85e8064000d80e002e88000e40858098042600055070b0380d00c030403680540168012030028070030050aa004640004142c103c4240003a01c54850280b0355100d054161a0204124440244007440615007960441e024400b0010903090001510f01d1144003030282050110b92803884480709559 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 745681097 1250 745679847 745679867
    0x6030318030305090d0c42080a0209010e0d050303011a04120201031a04060f1701230a020f0a17010918060509010e0a0c09290d0c03080a0509090115021903 68
    0x103039041c4070020a4010307c0508600070030402c01c071701c032060700700b440d52240c2c9074050340382807085512000c0650759003a00e42030080d086010a64100709086a501d0300a03210314401e1000e46004d40055a40d03581040c609980c6103524441d2400003041c101720400c1528207003d44600703540d07030919001c603410099541541c00b0f980d040340180d6015150802c001a40c450808400b012a00a90700407030020740c10040441c225504070456011404c601e1513100444410b02241340d60020003007100500b03101d9000c1d11a46540c1000c02e10101040b0002684180160103010003070042154007030030b21491448166010354400e0305c410040c4500e88a001040d0088800c1d048641001d0022048800d44ca04c9401c103c49007039410300c1040a540d190400c0002444083ea20011260007103142032107074010481d0600480c0351055805952400322130501000088814000301310680459841e079454102e0801044500f8906a222103110221181c000c008e03c0d40200b603840805d05544490030480095040c296444010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 745682347 1250 745681097 745681109
    0xb0106020c01120e120c102a0c0302032206030510081002090f09090c090a0b30010c031e020c120306060c060103060f14090c060309010e1006030318030305090d0c 71
    0x4080754500106100041f0041c803002e01180902c41440384c2078123101222440b81c140c51103200d200440000142c00703030070750f01015403103881224500008000b400744500914580c00c0c10340f40e20900c040068a40c14000d0300d40000009109072039151801c181240e46d020032041e456256500410b801d103050380c8003449021280000f52550b80c403450400d030515211071841c82e555201d41c48240110391034a2482c8250204803d01030190b69010003010381b12032040c134512040c04984a0654000b072800e440c20b0140c0f2031000b41031344000c14200c0c04888105c40ca24184100c00c0001c5106110880a107c0c0002c0e5000064040306030548d5642c89020106280e44216803007500e01d8441d4100000400040340d0110428070043c40c1c0070010145620306108110006455940d101d61000c0074bd41100d1070200015500b08402c14000911b0080800700c103400c4ca030f07000009180b0950798401c2041859004074140c00b001e0507507031505500508642d0003a005004407201c96000f64203a8080340100904a4a03410181c80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 745683453 1106 745682347 745682383
    0x90405070c0809210a03020c030f2b2a03140306220209030d0504091a03030d0218060304061b03061a0706060308030709030b0106020c01120e 62
    0x91480b0180c4c1c1422420312450580a07070400800c0d44d994030903006424403c2c480c408140c202600700c0d2140449401100080180c40d4036650f01900781c2104000b442040190715204645102d80c0c461841c501e11a048124084403402c20340f403001e29846966400c0401d12100c41060043c001541c0480d0005803103e0880144003001c1c400002d00260000018208030b400d40002e03140c603884104045c00b00342c0c001018002e44030300d40070b480d0428065004501c001c07506040466641d100304216143c05960219803d40c641070110300c038070302d4404018100d50301c81c20942850741c000d040071901140f1018844e492940c2190080c0281d104451070800303440350180c826100c81d01c00f9403010000b121215a244000700003d80007074050750054032143c2c1c07061b19543c2913180c011400030068008000790345c8104840c00c066030340000c007140001440d6902042c1c0031310350320b0640e146c40c40b58403400451007 = true := by decide +kernel

theorem cover : BRFrame.Cov 745503597 745683453 := by
  have h0 := BRFrame.cov_init 745503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 745503597 ≤ n) (h2 : n < 745683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
