-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2005
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:25:55.898979+00:00
-- url     : https://prove2.me/submissions/7b65e8a2-c902-4300-bd1a-dbadde3b7fbc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 360431654 ≤ n < 360611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 360432904 1250 360431654 360431663
    0x102031c0b1f030c0503130609030504080f100501051815040207020a06120c02030c1203090f19120801120303020d06091e0605030d021518030a050d0506030706121d0109 74
    0x700d150400168042c841c4404034903132810700302d24526060845c80120b1070310120003411240d031034140c0414903100d082900c02900148046500d04850a0040c5070740e5403150290400c89410071002040c1403c03c0000400c4c481941000f028440d10380030340d84034034401c1c41d04003240c00039800d1081c1005039451680100042c2440e448180d20100c40f014154140d411020080e004c0d50300030000c022681c400007d0003c00d04c00700003101503d039103c1111590400c00081c0da90007651090a10006a18203514000e99100d8800c851101085010b0f850503500c20344c0900c05e06c1414080144070b200443d010390020480544a900c0010340c403902c40c00130351700319001480c00031070314400e1683c10401d0250611504000d040704800410805407000c0000b0b6403250703a84e10712085081c0410100d480c5d0388101c208214061080c00940c1e0300d5021060300200035070800009400380500304008100030f800c0100740e41c0251a500ea44802d207040d141c0792240090038500340428800e0009460104800500703201e50a1582d115 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 360434154 1250 360432904 360432949
    0x51b100209011b050c0d03140406080f010f030309150e0a06021609140105060a051b0c01030615020a020411120a050619060c0230060f070e0102031c0b 66
    0x41400041c80340c5160f2402002d8501001100400300f0320008109000380300c1111250880d46417440c044802130780b84a9003000174000840c0c0480c80b50307000f0f01307403521501c291042c60419a03654124041104443e220180116468440922410910144200441d400b0741002d0081e11480c4020500c40b406982c490300c01030b004410700841c60507140c1c584c4001407254003c2840402c1c001e4922181e00441842a94418500012a804680d00600594143c02a502001074100c030040004a46686810076040d000ae481c008012a5441c61620410949001a030003082018440e90900c0002c003003007403502d0301070b15042c400d2003420050006d055101c0d2407000004a15424100c050001c1031500e1000c0040c0c0441051003440303c03940c0288120a000d404450f00e50b810101c140c0c00500010803000c030b100d00600700740301003100d80c50300151f09070241035030842105156484500840384000c03040c40043c0181c00420586030301c0d546440c445070300c91402141c0000e1103140034002610410043e044407002414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 360435404 1250 360434154 360434167
    0x7050720040b0301090201091e05030d03050405010b0628050c0f010603200607030c0f081612180e0a020c06091c0c080f0a090b031014180403051b1002 66
    0x406000700086075000354000d1105d080141c2c0040c102400e503004803500551441e0300141c80a41440c0854000c00c0058190f880c01552114010098a421070307094441c2c0d07007014005051400c181003220003000b80e0740018140e079014803c1d03c0300306070040c140c407070704000051050140801c000e21036103035603207000400014500c0c80d40c902001001e0707020031406140710303e802d0013069a840300c604849155a152a01680f1902149800c4406055140d0f0180108001050807001080040e000c0c400300303406030002904085560008450030b013086000714126810b030b26001c1101541207010140c01c41d4100d1409030506183d08075003480c3c04402c4440b12590751241d07000180600180c0d043c8100f40d245807030f0200028801e0389a21001c0d1280000002031088006600c3c000d280c0300f06150700180c440b00135400c4e03480c288040c3c402c40d028058011041307076010282c0780d800c540c0740c1244200c824036038501000780180d550791420348198124444692045480501d01c0c04031074030520204c505802c3c9080b00685403030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 360436654 1250 360435404 360435409
    0x5063001080f0708030a02190c030602030a02030103150e07060e01020c0d0f0b0106180b0a1b031d1c02060903120703030c11030304030e060307022d0d0f0c0b07050720 73
    0x546130307000304c010f40c1042019504030765001c605450002030035419509170700d440f45000014084958030103088c0a1010007031045047e4180c000314100d0f03005e0380725400b10109040081007141d05000b0b07801151b503c10f80d03040041900030403001c01080786c1401a108110807100104107100303411a0100d0b00400f6041c402020480b4a44400d8058511464002200080c50204444258140c085c86280700c0001c5040740d02544a8100700c240d11035039072603c6c88001d40525019080155003448101c0c8a8610700300e110407410304800b4140440304448016040002c9602070118a5000802c0c40d6014099044180d40440e800402440a540301c0d80d8001100c094111004103072481c203a00b102c500780c004005101c04254407100ca41100c00b03088800d40d54a031aa103c043c1e28010071703100000040d100702601c6006201075000301c880809032100960300490764244080364030180c07080c4002d001c50305901c1c0e00004900c402444d01d51000e43c80c1043c6103080015103ca2040c02d070b80d139400c0c2c05484003044c070b0643c1a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 360437904 1250 360436654 360436663
    0xe0303040b041d01061407080c030a02060a0c17010315140702060402030d0f0c0b0a0b0d0311010f2d18080306030c01021903030e12040f06140405063001080f 69
    0x201c08040c403c030001c2d414090010010142c1c0e90400360790350170104400d010300c124001240d81011040040340c1c0c2d0750343d0700312020751034500c201c0f0f080c00c109182076202c029150240308015541040300d0318034001750303085030380e580c509074120110032100c9940c4007600c811480360a1100c0340130301c0450b001040c0c0c5140c14410036260400b00780c60f08003001954800010182c6e0820220403845501c00000c8030340369100d5003144010401c101c215948800004400390516400001d41100b0444501c000e014000c5022851420b40740c100120141c0e0300c3d41e060040c41c10045003042e03030030b400fc15404003192141c01d002414046540d010310a480c4418000b042c49010b190803c89601140710a001800811044242104202c0301014000d014180c65181a040070102030000e1402401240d901c90345654446010920040b024040d54010030311603007a0507201d0f0f00072419501101c0d001041280740008101411440c01a82580600d58202c24912072805201c070142c8580600850002001ea0140d0302c2c6c2803601d030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 360439154 1250 360437904 360437939
    0x210060b1201090209010c06060b0408060c04050a03021c061401080f0109051902240705060a050c09010e0f0a09150b0c03070605061c1209090b0a05010f0e0303040b04 73
    0x194004001c0c20003201d966905050444242d48001a211910309005864407851040c0061a09280c40404110002500050406d44801c00c084902590350810980c090788114090030382d010860742e9003000117241890030701000030f20103904c100071070351075039580d9041c2c2d22218206000e91030240010f0141c04010800036101e803c400000b0b00c510450b03621402d44034070440307640480700046c1c1d200302000d6403076038110907240082040c46215031440020020200d44c1081c0012125809000c0100300d50324128041c02d8014000100308515101d0514010349503940030410741e640100c444a000091543c40e56400e0340101211480441c180d150341030440650307199138000b42d0000d842440a12082e40000040d0b998107036002c100010380d61103920020b42c561004141d00054090a50070f00c02c204a00d81e84904194403d1f5200d58000702c0d21030751070b00c050394001e6604a81001c8168010402581b090034030b500803034184c4c20580b040303080032004a800c55000750084841007100003000c0100305500e503d85000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 360440404 1250 360439154 360439169
    0x20a080f03041a15010e0a08101406010c0302061f08031b010b0d08090405041e1a0c1207080a06120b04120c0803011403030f030a0507020f070b0a14090a0303021006 72
    0x3d5152120b020f001c0031039400b4400e810020f03035100d503100c107468113116000941980da044403010010b210032031000d021100110210b2500340d101103040da5000300b88403500d15515402a0903a40d07038520900f070103400c0038904845001c14524000964000502c0240715004041030400d1642c00c000c4841d43c203644480300458080c2000d0b2001c000070400000948480e80c00448003c661512181020111940c400c1e009040c0c00c050913441000300140061456413001d455040030340d080c0d4600c1189910340c0501c68074800d80810000c00514880d100f0440c00c1e41c05101004000341003520350065600c0b500d00b0078011100c3c3e04608050005120104560705000181442d2105881666170781e00c4a1034041849a50032250754426041079654050007662451507620454685a10340b000300d00c00500402c0d10707000302600800c00142c074a600041643c00c184c6511281107460040c0c81c187c219240c0403c5501e91244102c01c5c40f8003000b5948048001000b10b029a0043c41509a641e800004076441e6912118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 360441654 1250 360440404 360440453
    0x312010b1207020f0a03050f0405060f0403060605011e1b0b0108010618060b09011b150b0f030606010e150903160510030b0307050607030509030f061e0912030403020a080f0304 77
    0x4c0800d080003500c181081e5261918a84410020b501a4954002e54000d294031210100b0304541c40200c00c005441140d000e1141801056070ba0b200640d00b460b440241615419004249148101e014040341000040c22030000c41000d40181c840c4490b1407420380106074580d4480d2410011100d03400303056500c0c800f0480040100c03c1c9805009200d61281450140c140203180d80012641c0002c178000c00700c410740250f0004070100c10103440400410100004610070701c000801041e50342000107020740300d0749043c0c44050b03c1d1110f4074100101e03c151102a444034290800407050541c405004025104010b030341680003545c1044200140b0b002c04801c510200741c42c225a00c022036400281c0c200440303200b40c0e1070685c2d07547c10b030034116046e218842140c0d0b094400c0b2504504007400000300b1030302c82c400180c01100d0344910702c80c90048002d0281d94030305860744407004108600c90300714011a00b09100e030048900007502d90b511b10081e50006550054094000320402c400c2c040300c0480540e0b601050142c65 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 360442904 1250 360441654 360441673
    0x6010308181003020a091710050702030f0301080a021c0201080c031909050607090506030f0403030507050412120e01110615190609061403280f0e100e0106060903140312010b120702 79
    0x1942d8108c0c0c0d0501000003a00d81d030114807814001e1017265203031642202240d64941c4c540e110030384c3d55104107504074000c8048602c48030802c660341c4000303c1c1482c2d0503542c9000d1511342d00c02b000306540014083d40107042055241c0d881c80c4900d80706001031544240c000d0300700c501c0c2900001d02080581d50040b8081d100400c100580d0010354030006a0042c1c1c5800c0004452700c408800300c5482c0aa500602c1c840078030001e400040c4a00c0c0018100a0440c950302d010320100b00c0001100e481800304031741c2800da81304202088070200398080c1500c144001520a00e994502d480d941d410640d4a03621540114030300d4141400420f90008500c01188134a0403e1451410324180580d01d14000c1c05103c0c0413210300e20010003044030144c200e941c00003075001082c08406030380c60f600c58441d218070004064103071812501015261040c0240e80441309517448004101e891911030900c1c081080303070040300038001000800c0103154102e8940303010741011520a0748a140304c04120307084031800340154065601c9240da0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 360444154 1250 360442904 360442949
    0xf02040b04090b07050a03231807060507080d1121060405040c060e130f02090a080f060c07080d0513051e121e2d07020306010308181003020a09 63
    0x1904d0b001406440c0081d41c0c1c2d10990001c43c0240106103441e0b01c003201112175540b03400d0600c03035200e014846608140c0215400c00c121990741fa0150310546000c034001307021031800305045001501241510b1070011508c0c294985c190b42080d8060b006070140246040040fa01c20100407a075140e11401c191010040c50038151503c88000c3e40c1403281108000c016120301507180c9801d080c0300040400018240801ca85126412000e134029000a50189040e20b030005000000002c40200060000020340019201c42c50080300c00c0c3d0119000faa11140f080100641c4080680710321442441c10601a00c00d4645034074180c2c0c1024051410400048043c00100c4140d03040400c145110f8a203204101e556007240e5008503032003c01e07090100c0004030000c41c20a0070f03c070321860403401041c00020b070704c00d0034059000581c145016181e4040e42590004005000003804c880042500d0080b141e600754403610444c002480008280d040400041e8000c500316500c03d40240c0440c000c2c281c2c048001a070b9103000200d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 360445404 1250 360444154 360444173
    0x61e040809040207060f050115020a0803150a0308040602060f1f0501030b010212070605061002070311091b0c10050c0403021806010e090103050a051005060105160312090f02040b0409 80
    0x805030900c0400103076619150703200e50480d411160f00c402d0900482c035140b007900000b407900b4420205041c0b0100c282c1481c00e840410024680d0b42d00c0355401c0d0550300d40c240848148501c4c01043e94216003801c1002c00800d51500c040c2000341120f50041c00b56140c4140c03041d40d03003030700a8102013070604001e100b802041e0030b02c6d640f4001e4072400c0c1380000c0c50440d2400101e141c107840f00081307884554001041800d00c02c00d50002e520551084d10a1030351400001400ca80e1008184006840c00038440c20750b203541d152000e83c0c82d0b04400c0d2051510001b584008190304c166020003070b000801d522001007501707001882d0040a03445111201e80a0a25242d5004149604604d0a01ea04060080c2c0c00050190303000d25200004000090151250340d078403460700381d99400c070600080c1c400e0711804a03c0965030105019a511480040c0d650b035043c042001c1e040c0c0b43d41c606080048082c008950151259000c0511a20f8041c901032501e10507541030741d00600c030840e0b0000c02d026018504252043c40030400244 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 360446654 1250 360445404 360445411
    0x3061a09041e0f0212060d150c0215090d08250302070f0b01060f1404050d1103120c072108030c070503090d0602071e170d020409050711061e 62
    0xc802080c20802102d4a4803500724080508690600d0302d00c0c4040b6003a0035034040d00b4a04044a40070100d9150b5400b0400350b4920404028050110701405c49040902c2c0c0d000304e0140425030040722a000f0b1000c3c842c04011004032482004e5038051070110341071960000186402055000006010000003400f500c4038842d02c840741014582c0000340f80c010042011200380c4c2954011081110f50f5859803001070034880609101800903901d4034040c4501c2612104850480700001c1ca484900d40440e80c840c201c0340303107032070b403040d8180034603541f80c0d110100320401044030000032000f03060586d04000f1144180d481494804010503c00c46680c0009810041141d820841890303100392100b00038688036107075226980c00140c020100001441c1002140c0c6c02030900c55204002000c0c10811520310f1048940151030050848a01ca103001c03441d000c0000c0c010103a00301c80410240c505503c60103c00e0956606540c4400012800c8420100119080c0030864100921000c00121800f241600780622180613 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 360447904 1250 360446654 360446659
    0x30d21020c07030c060504050907110c040f0b1e0a0605190309020d120503010e0609060108160201060e090706080c1206060a031410030c06030c12020703020c03030304050d03061a09 79
    0x103030301d901448100314002c02540c0c02040303035902c03540356007005084d50041d00c549400f900c0743c0c401090039036014a5010340140b00b814010000320116404001c01b07803001d074060001c0f2654441024140b601c0d50741a1003a4881001c401c0c9501c045200306111410f13445611220800600b44046540d030303039001d1b480d040d1501c0b042c640803580e6015400051810303200801c009095442101040c0403154212025504881410f50042c102e40d8840c01401085c60b4200c0c0c55900294240001a03220744010400300100072141c800098000e468030242c0448680a480d52111903012100c200031550b84411503981c0f01d203585010904145c00d01030b40c0c4a0039100038024520440c07008ca03042c400944658070540c0f03854500c040355280342c144040d088407682c4507400240d42a12038001c002c00e403140680216551164140d640c05407210310418400d000350084d940031021400b80707040302c404640d81000594001c500440252800300b4413880040e04407466603211050444080026803480d500d00c20035244c0d594000e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 360449154 1250 360447904 360447907
    0xe030f03041703090a030506010801050106480605041e0b01060e0303071a0901060e1005120f030712030f060b040e04060e010e010207060609050c37050306030d2102 72
    0x241c0450f0b040d0301403580c6a60300a9480b00d8008103000e000070307119040b0780c440c5001704681d03621464102d80c41000c1140080d0b00c40002590307004044540e0062183c581e01c01944410503001c0840ca100c600103020000b03a03400c9441d00184000e00c0748211040c82071100390200d20700c0480c0183e0321440301460501c04e4005101d6008020354031034806108940b40241c0c0540700e1090f1140050703141e17080b034105840380c108a600e0100c000c034104d40d070040141d014409088084141a1919013004500501c0304a140c19601800c0c080416045007040901000c51050750407002e00041d40300010200d031410f0408103841070400108011502012045030191440d0314000c400554590901801420121202c2226076180c000000c0702240194054480c2a11884007444030a950351196010344105440b850310500080202c5200b01c001400402030030100e80030b04c0e00756005690102070b06501c10240f00030114500000304110740c40d091000c944401c089041c440611240612400d980b20a032000a00c1c40e55070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 360450404 1250 360449154 360449189
    0x9060d0f030302160c1403060f15061309060e15130c0e090c090406060504080c01051b1b0411180405060d020a08070806090f0312040309031a0402010e030f0304 70
    0x800e8045a050f111190711030f04507103213203241200e4103400030b1054000d5800d0708685201945070100d01c031401520980784620701d0740c4640740200c10034034040039941d500050401030744d404159130300314600003464800c6000031010f107004454441100c2c000d001e1424141d080032902802e5035031282381440b4211010001488010040d0151000818405010760000410702008502d0300c4041c0102034940047c0c50620055039151019126030099000e01503e5412141d140c40040d40b251010b81100952a15110754518007240680d003005d050600142c0c1c00e513441942c03000142840d0043c1c9240601e528015803510b00c1862401c00e035024041071451295455501241481d690200d107041c5007600141030501c42941d540703040355190010320840016010f01c1c40002c01900c004a01d1045e0020100007441c13401004041e000f143c000000e2049090019943c801f001040d4000caa006e02c20004169020b01c0341090300025081401c15031000384030b41d11400d0700c10074201000c02a00c00b02c035002d8120950108 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 360451654 1250 360450404 360450407
    0xd06140f090d0c0b0c09030616020d02032107021e1605100e040b030c040204090522050706030f020f0a0c060e01020a052b020c071a090a0e06010e0301061502010b09060d0f03 76
    0x10032241087d501d445000302388042003c0300000f0581d0079040e03800322034460114880c00d270788030300441d814000804806451410843c0809844a900103c50700c10740f181e0b000b001c642684001400c2542040c2070f800419060024070012242c0d001500045850b4a409141c0800c014404800103014600442c4c5a4210034459141007046058010000b0310942d21551100c5000004003000c4807021070f526901030011120880024540d07544c25084000b5084160030594284c0c05403030050400142258200080c3e00d525036090094020b86c04581d030303506c00244541c00c00400b0f403500035803003330180d23481041401c80c5140c0180460b0445138a03408503a01d41d09130681044e103020000003000c20300500008070810030801c00301c1c941007510504441c1c0322082d007051402c0c41c06809014092504501d0084080c440b040c9a903c503503500800501d4000c001c500e60380c01003400c2d0750b850341c010440d844c4054036143e03a2030b4081c0620b500c5c650003a10004010720b002800242c0000c15040c001e082080e1400000d41450b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 360452904 1250 360451654 360451657
    0x30e07050306072105091e070306050103080c160e0610020102040801020403060e0706140901111906020c07060315060e01121a01080112020f0f0d06140f090d0c0b0c 72
    0x80c00001c09039000c515000c4001390101084003210f90254241490040035088075100e914001d45c1030400420080b2003002c40d41214981e2a031100e2401d101e030b50030000006405005d218080c501c15000307a40c4507039031300880f54900590300d80b80c0041e0170b80820040c820a44011901070348003a007100d000e50401c1144400782d00920403500804410b500000b03001c0f0a104041d00030341501459942210542541c521040f00d46031020680c2c400d0003002041640c0c4590700c141c03100308440010400381c1d0481d02e890000780901c481240c034201c03451900824142900c078414001000105141e0a082c40f2125406041d0400810107004800c2884039880c4581c0740c0e17034401c42ca004018054075504220320038482404425941c04032100d0342c0003a4030600003180680010b607020000c15070103001c408105103010200710611440c4042c7c5900103406080741c0000c5a00c6016490342150900902589410103e0034248590401032083d001c1c1d03407004040e10342556101c400b1103042c603000500714666464410a8041c80d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 360454154 1250 360452904 360452909
    0x21032d090b0907050315010803120a1107050a0309050f060409050403051201092004030812151e030f0703030f210c020d080105090c04061b02040c08100f15030e07 71
    0x2801c08680c1085861100040c400f4141c43c0200d04641c4500c82c1e240c3c806800b15024014502150404e100b1034a42e460084100754220b40f0590000c1035034416415000300ca84c000e01c0081c0e61962005030131600b41038000c65004050a0181c0710481d04000d040301107403141c45a80b2820701d18a036200001030034144910300f03403620588a01c580100030750b501d522103000381811003203400e0820030015851790390440210884044a5000d0000d07030070060035400411078114020581421001142108800c41e5602907828950b00c0b18115440040142c80b402c1c5450445149030041c203607404a4401d0000ca50458044614411985002c85000c0140100000900845070006281a0a04180e04c4003507801061104060000c3c0c0d541d6030070344e0307a607804100c98102d00b507500c810a031000f08010700225200300001e0342c09808040011121813069800b1404440c45600604006241d41042c086200303c82c052040044c00c0001440718094101142881c2094030b142c01c110505d0b035500740204401d4000d210f01d400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 360455404 1250 360454154 360454163
    0x21c1401050a142b0b0c1602060a09050901120c082107060e030f03090d0c02010509010c020103140f0612030c0601091e05070816020304030816030903080721032d09 72
    0x25402084c0030407006070300c02031070454502d115040000c40c0b0407952000d0f555855074050800c5400f1000e07030240712880e44022941c408000c00c10b071012038941c5580c069036008100070007000e80f1150881c2000b0b4069062a00900e03800d40001c03240a40307007401c8c818038042c648168a00980d0f210b01515040000703001303c200c1c0b441a4040441c1c60316603030768500c0246126083c41d8003503410f22400144110740340303c0c00f904000d020507002d01ca801d000d9440f500707490800701d1060500140322101219580c0700010100c2c1d44c0c0c40400d008200b00880b504004003902c41d560b4582c002142020081451203844100500074000020340d05c110000c4448402000b4084d049a0003004200a0600200051011104441d01d4450003800305400d01d100e8070003c00c031003c881d0444091400e00c07003800000000c51000c001e06a0801c100c034280407010603464001018900d100329003804003002a01d04414200703500c1c8001038140b6140c4403002c1c00e0301c2040c000400d0094440e403400c1e650710711a00c0300000100030500d000390 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 360456654 1250 360455404 360455449
    0xa0c0509090f011b030b1008040303020c0c090405210f180a0b03070306061d0a0e06010201150e0601021905030306040b01020f0d08011e06170601030906021c1401050a14 74
    0x18050003000306108541d9045175410300c490007424007400f01d0f41d042101303100000782008000401080c4030b60f002e800200c00000950b221522102e00007555842d05440c1510349400007052075002581d41c490f01d25807203c0b407900c80e604020704008004094040d2101c0c8030b1030031000d020105055034402410401418070451425282e0801d008014000c00c200d00030500411840d041c000d0040003031060400903140020a242c500905001f4544004c140182415065648941c175a0b001e078202843d090001e02201481003070700780790040c00245450140410a40510001800d0202095012048982c0150203407030114200007070b9030040f481e00b81e603242e840c0518003824031070b03507a500e500c241614102c0b0341e405600c000078010074425082d031040318030442002c2603a070740000c807204810403802036001905060005602c41ca42c0c030f851046e80c0c4488441541c0c401c008115206401c01846103030410001c0060440c600c1d07051001003008680396000347c0342c10700f1034007010166903541e02d800c0b04201900313001da4070b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 360457904 1250 360456654 360456671
    0x807081204020a14030307030c1b031a070305010b0703081b040801060503070e271c0504060f1e1211040608090613050c090a091a01090e0a0c0509090f01 67
    0x20403114241c80482c460b0218000c0004c20f06400321201d0500c02000300918074041d890790f404d0b100c080c82c05608845900042018403221441d180080005500404051000340182080c90241c40401081e64050600d0000140414142501a6680f00d541420402040d8460180c400110300f44041401d1940c540083c0102d00c0d10f00640101c800c5402c00d600b114000c980325400b20300600801c86a03d2079907410aa0043c507511f005400910204074a40c050303a1413050800c07501101100d4200080010600004040111035401004d1200b50a22498401948501001984480c1d1f403448088420000c155440188908441d40440403454004020a50b920b90300c90025147c0b20301101d030000c09000c0d14002480b02034011039074015003640000a80008001c0c0b8040001d103d001a10258403641e0390031207000003420b130003114481c05045041052081d85030a400f4016210045401c41c5150404560480081d1114190000707440301140c0000e420350f583e100092600341000b08008484d030070003040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 360459154 1250 360457904 360457927
    0x40603080c10020315060304020a030b0c19080402010c080f09040609060812070809130b0301090f020a080102070b160522030209010902030402060702041a120f100501050a12080708 79
    0xa080030101c0c401503615500c8003014040c103d01040b10300d640d200760301c3e2002a0341072030310000131580984001c089001040c0c503a00c07960780f41d0300300301d41c02500d5650025104040c940c3e040c01c20318602d9120b01d8440340625003540020100202048001e1454001103034541c1c40c40c232418141c5200c02d07030180c020490f050341c03010b40c08050100c034440d040d054081c590300c80da00c6617942c41c202c420b1140c02c4103a9914100504041c000031720801080c2180312540c1e081c0e00b1203995000e000b0462020b01540e011120380e900d078010080740304181d502c00c0d0400e82c810882c40000811079400d1550140182c540c041d10303080c10751000d0724039114650701011000340300c907500d542c0c0001041550b030549000380e4030b04070103a8075031550302e0491009490180d1f01034030a0100f04010319250300000030300480c11985074901a41c07180483c054010f411039105481e00050700c20040d05004110314101c40001200c103000c15490000803070403005007030003414169000103150074113102084003120322540d80102c0c4103035100d881545 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 360460404 1250 360459154 360459157
    0x30d060f270f110d09200d030507020a090f091a07020706111606020609060a090305030103020418080d0f0513030806120102070515040210180902130509010806100909030503060111010b04060308 85
    0x10b003110b01406500078040c40290768a906c004104002c0d007070000021041e201601d185d00030140881e44807045200100e9041801e009031801a0302100e00460100020720303102c2c03c88904006441c21103078000341005003540d40000c180d4120b46040c10150b107080b0210304501d0070444003600740c02d80141164400500580d00003043d51040707500d5001d841403070302c3c0c0301c0c02123085d03c02c804400350008100b403006101511745548045200b500c01850100009030a50341c800c566003101740d9995130141d603005040c103400780c513009881d40000e003d4450110442d10f560043d00020b00a441c95010b0291205c450040d04404d5048501c8260000d0032130b50f040032031008005550f641250101d008031004c84e000c05000d401020410b40c0c2e14118480e000c1030034100300c01c80c0c00079004103044005ca064140c00c0001c4c140c81e1824a280603102600181910745040c0e20080a5607040f0352110764050302e0309100002081c0d002d000c0d65000f0109182400b08107100031341050150022107040ca42c440c0c5020400800c0005110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 360461654 1250 360460404 360460421
    0x10e0f06010602061f0e190c0e040b040912050a201c0807092d09090209060d030e1c0b0f271207050708030d060f270f110d 54
    0x508840507540d0305005c41403824583d2030024495528481c092003061040d10445601603100319001c2c400c10101c010b01c60a4851040d121700208100e00528165410680140301e8940c00070b4900b03001e03002e100d90f00c103400400c0c80c40b1100200000401c800d80e01c03500c030f0140d010140080550304145c0f641a0410280c40340004c2c00700c0c88000c12820300c03442d5101d006481941c80355069450314507510345171410b090900e1000000440319145191010150303007201c00e01140c05000d0382c803c00034140c803e500c1800050b6102130030b6581304000c1c8038881c0000a900407081188640180d98075071000c0c011700f00000c0c001c0403012004007601d01e018100304401d215109814860103040030640761030303070000100f564010a174420780080ca40100c0d248d8904082040010300b5410b00c00c20490308203503070b0fa01840342140c1110600e08071150b192102004061003014160340544640251a807151151131507084420b007103502c011119580f1024002a024100e42c0900301400b00204000d170345042942c061401008a0b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 360462904 1250 360461654 360461657
    0xc031407080607080f04030e01021e0715030e0d0e01030f1a01020d050a090308070f0602030903030403090806011503050406061a0c071d06010c05031606020405040b030a0c17010e0f060106 82
    0x40b070002e6001841005014018184100305100360786480d141114410908403065055104889546040e105d01d1010229055030440140c07001c1c504040c0c035001410302269040707042500b4015003200740c101c0402d04403039440403810b00744041d8481c3c40041e806010004000100103180941c1c400c9504280103004d450307410240e080e680900c0714000d05403118015800c050340006c440386018000142c02070020449580540740e43c0c41018023607920601640c0c01100c6d8000c2c40d0b003000c02840304260300860644050403e480241c0743c0b5604010044010040c500c105204042c1c80b00041001d009095010300007070014100c00183c05042e803041c80340c80e0b5015611900d02840748250004190b9160484811180204c80c0c2c561500e446180044a58440c81441a10940020020b6100680442885801c05031180c0400758842d4a020b00704021503103904c039003a000e07802c0200d415002030750005698080c0c0d846000541504606820b00360300410000c49060032522508146038605900020b01504a503c2c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 360464154 1250 360462904 360462913
    0xe15090607210b010c0609120206090304030b0c1b01060801060f0503010218101206180507050307020604080c07120f110604420815030a030203040506070c03140708 72
    0x6252048407046120b064902c904070b011051072a804032150000d80f19030742d0503d4000d441158507128101143c05245003241c8041c0c20b40c4001c02840c8d010300070b0580c00503000000d1402c083c5561188804a9001484007800d944d0005000e1080c0500408113082c40800780000c0000a884545140c02413010340901e07031130207c0e5a540020030b45014021140000c0c41c0d003070648525440041440b0724202c1001440040c000b403083c0c100030008291050500401c4a4189140d801030070002c44003c41c2d00241c48441048010000c0220f80754000582d9a0813075840303040030342e40b2614980c4050418426810a0360001140204107051085500342c03c06200d005144000c0400c400004000c410321444c881d0400c0c4500c00f0b003e00d9403480d43c8100360502c43c1c0c0b002d00f134075908803400482107808141c403070800000300720010240311010810b140028046001580103104081e0303641c40280d0b480c042c030320850f40b04a10004400f0108018400041d0041d0303480744225004104041607240c4900e0f2500590315030340714 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 360465404 1250 360464154 360464161
    0x12020c0717010b011d0406150201020a120212041103010e030a05040305010f0207120e03070e010314010b010311120a0e070f03060b090c030612070e0a0902031213060f030e150906 78
    0x1841083c5100405131a42c5010f901d2a0400b500b440101040d0350b0340c80f95850a00081480a19100003000306041d03000607515a24981c0140003288070f0300720404018418486520240d04904c405a0055040003408111488541c0007a0140c6098074414019000201d85580c0076604100035100703880c4134a000303010703c40e100c1c8400400c86c09005409131501110100030b00e81d1502810140701c0a16018066442075034840070b180c6103440c020f0740103d941c02410341c0c1c1261140b50078031818407201d6013440c4c1030101d5440702a00015a0048403980800c030160040450903800700c90380640d01040f1200d042d950080c3d95141100c101f0503c80c4020780f00d20703082600d100d4079031030f08922291041a102440e9401c2d41c88450a005c0882e6002c501d114040c405d945000c103042d10342d040190300c200302005000c00e18031030320b105241c10550320100d1110001000d110821007020741c843c8070000d6500030724191041c0070114100720041c240ca04580e03080c07801100201d076801c00c1c03400846441442d005003150750544 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 360466654 1250 360465404 360465449
    0xb070605090f162420010207060501030308190b10030c0905031b01110d02190203010f050414070501030506030c091e04050109030906021f3b010506120303150112020c07 74
    0x2c0304ca46165001401c2a41c034902001d003000320949182d441c4400040c1041e05070b503256001c4a9080e0020750204244000b006409142c2d0310354540e503015400340034442c80403810f0201d04601d1102120400341138a031108007544521981d0104008c0c0801001c075a00d4503180000301c0b0030072465184113800074030200700380d01d01c45400017910041c0c180994002c00090300b07a0382605813051040e0304101c2c0e00d035403982210705010403a4092039000e213014802c601842580080c0c1c0620309121a80701605040c00e103020041d06030740c04242a86e095500b510305010310b41c4c80b003a841c0001d0754054020140c8100f04000e0005100c4154081e6030765038400d03100c3e89641a120320091782c1c1d03240b05c2180003e040c586000c000c1040e2406410400c0c40000042c104140e11809454200c1d0624092101007500f0100c068450b80b0034100340070b0b9035004503045d28075600c2410a10012500da00c4010501411200e000300d100c10345074030401011048a0181c04119101c078000c5d85150b071600464030910110001100e420742680 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 360467904 1250 360466654 360466709
    0xc0702030d0807090e040c2303010b030c090c0706290f041427070b123904120807020f0114271807090605040b070605090f16 55
    0x183c101d603d6a01c3c12070f140a0003031050b450018001c84403000501c2000840c1a400507074241050320311340d0300d00b100302402400c1c1804c60300b2038001584254030812540340552950070109800c00038543c3c03441c0d50b41c03034241001d401070b00c4101e4000e030030541d6503c922200c011000240120f1900704480c0c404619104408102c00e03104001c0d0800d0811000802280d4961420a42160b0641800d60f804445000540c060741c00c02c00940d00a4400f6840010560a03824001c004264000301c0d410300600600145c070360319aa20803403200700300000c8141c1d180d0840804d099005a40041540d04031000c0c910340145003035600c68205010490080c1190642c14001358043c140c080201001c513008142000ca0303441c1040d158405c41006d40c038640d4802c000c20201601e0b40030042e081072608002d40d81442c00d15003401014001554044403c000d410311042c440c0010400440b000342d600140c0226058580b05889821b1042c44271110540d4803030005030324200f41017950364404a41c0310304101418540b01c1403041e140d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 360469154 1250 360467904 360467911
    0x90b03010c210e010e0a02040608030c0703080a020f10061e060206070c0c030209041a010f080c010507060b0424170303010608041e0b0105040501050d020a090c1103030c0702030d08 79
    0x2c103201e800e07484100399045004111010520300080398940c0000300182c21100c80c40320b07140540e0000d50411381542020700828009000388001145060550034000da15503901d030000801c000360002349038004d244201f040d40c20300c000140545902010311049003004200d14816012070f988101008a400610107460204641040d009010f05070344181d0200c0d4110040c0008072800b030040b100200158650101d2140b01e0740c0315041e48920301401d4100031030b100605900403070008507031440500c0580e0021802d0385d4910f2003804c009485440d107240c40005007035025541c542017464440303c192800d0401c0c0581c2d10071080d0300c023240b50440d2211203003200038142a030500f405602c1000100002072040032000d40c86400f60301000034440300d11400c407080b00c5241c0d80588003580108014060352820b0301c24240140400c036180780700032100e0303400708950080501ca61a5015a582140310019010f0301344ca1000303201c00d900345c4c6ea40740740c00081803a05070020300e0b041e070081c8a02041c8680007801821134900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 360470404 1250 360469154 360469157
    0x1110733030c090332010b0a0f12031202160501090204051303050403260a08011a09090f09070522060b09060d1802040e0105043810150801090b03010c 66
    0x1070781d40c01c5840c1c0440001e01d540b404045d4640144600a00c0c4080088041c8010306640010a45402d030b1744c1040401502500150b1415a180e10100244a007800d07039101e1969144c1406e0f504020140100c100a0007107034854090018600300da50300f0058194818003500b4400c4404011640f200207440350f02d6003040c0310003404510108000d0001c02c5511403214501e041da4250421840c142d00440061500406601008901180300501c0a604503600c0e50300304081d0007a400c5d042205c0100085d4a811025003000100c403a8940803031a0044280146800342401920702c0b240d600380d00d03890b103145102d4880d082c3c080520f407110200e1015902c0007240d4558500401d07140c01c14080d078031000010a030410107941001050b50365000141c50f1030080d8940042c41100000d011724003804e110754a0750451030369212102c540101d06610000e89002c0c0f141c58100b81070809469502c072400142c0807141d503001901d080e08180000501e4942c403400c1c0c58103807140ba100a01c00801c41034280360036101c006200c42c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 360471654 1250 360470404 360470417
    0xc1e090b03070911040f03200303032412030307022506020706051809190506040b0625020607120906020a050705011d12010614010c02030c01110733030c 67
    0x150240307800031000613485a030198034142d554514030750071400c1584211146102c4200d1031410105804000c400400d00350051855480c3c2100d034198200070410803948450014801115140c40c0d010b802c40040044070704490f41c80c10038840180d51020312a00700044a1212403084001c04079100703061044446507002070070b8250a241301a0b41b9a00118a040405002240000600da0b204451240180d40c2c11288404401c0303208002d00c1551b80082515019605200d0403150701e840f140708a400e030b0710890b203454042d001d40b81c80c2000004070001029600400c0803c81c0402d0200e02c0b0480316035003100b515605902c40c0d50384016030711410100c10280403500450380401507035000340d82022a00c08210505185c14419800068403000e80802c620b034607071754510007030100e0b82c11b02d01030040580090800203400411580001d5403003192200050400055a102100d048020061000640b8003040c0d4a1026880590740d410005040d24106606001c01810655964024030503000ca900d01584c404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 360472904 1250 360471654 360471659
    0x1090e0d0311191101060f05040c02030703080402040c090b0f0a08060909030a030b01050408010e010f0c030204080309210318031006031a07021c0c060506030105060a0905090106030c1e090b0307 85
    0x100700001520341c003c090115812a41074003040a00c00c1c0e8000d0010300c21403100d803500381000d0000b11982d440510056510400540001c070307030003200060f44668102c1d000b10b0096542d190846840e440ca0b03200f03000006000c1920b00b56000004058000c1e01c44d01d03038070411703a50303980c004100440030f042e1a0304446810802544210350302c243c004c104007a5042c140285020742c2c0340852421640c00089186080e559000ea0100d5030544ac0070304141d41115180650401c4d0500e80c8680e202d00c144d003011441090512895801804542811410110288162504c84030305403408079503001c0a1521611038002d071550101030780c131a48281d00550760400c11400d0801da14040e44c010346400a418142940700342c8007041d00301c0c000c404103202e01a11a903942c41c4907001d5403038003106452000d008688a039043c43d0400800361500c850003801c0b41e0705070f400411551955407a060040c5415000039200c03004850001c83e0b22082003441d0129812551002d00380580d860b6810030131502502c07800c2e6415081070904 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 360474154 1250 360472904 360472927
    0x109050c071b05131e02092b08070f0525090b030a0b040b10050301090804051002120408010e10060803030c0d020d06060e010f09140121180201110a030206040b0a02090901090e0d0311 80
    0x20305507808000c248c94a0490f050351107d50f6150808007044030302c1d074400350305031081050500c42807622200007002442d146074010042c0120030f40701e018000c1e03426030340c50140441d075508200020030b42e50485030801e1942080c2c10300d4951000c00311142040d40440c000002880d081c14070841d190603410043c0c0900b405e043c58100a51107042ca0551000c500c120503c84403014540d000410003050141c00004090b280d101980713040941050103501c080386001130401c0042c04c00320032243e008c2030101c18181c0e52113003880d4202c0240501c6180c103c0c0146040d10105800c1c0d08480c0d0140c0000090300c03245200741a014040351445110b0144042c00d0782e0403899040d2550142034228103000800c94410162000c0341d52840854410581c400c540600c4041003c0c15560400c4214800e06103210107025521110b85001c1d40d03510340500002c01f40e02d00d4200240e18202d043d411b48200c400001c1208100d0b5030340303c03d5607011340a40624085c4900a02c8000304e005406482203488000f8043c00721411301c40e49000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 360475404 1250 360474154 360474199
    0x602030601020a02090a0e010b03060903030720120307080105061c11120412090b07031e1110051008071a1b0703030c03080109050c071b05131e0209 65
    0x5141548615441a0010395404805e54031030756560100040c1e42c01c1d103509060030749000180c0e041c0290002024004c0080d004170440b54802014100004c1e60000c07100e40440c0c5803a90b40100e2414001e08540c00f0f804400c2c1401540105520707990b07aa49a6241c8003088064400e02d646194103030500304d100e007582c44450708115a03415113a411141400c3c1d00f0111a6030011044908039001041d0404424055810104e040007901090303040c1420040580d03000f4283d00c641040d2082007658a003010079800c4e1142100710a6041c003032050700c5400344500d107507002800085c0c0e501e00ca41c5000c040f0114414400003440030031500745200c42041c034034110322004031560005020280c40207002c3c06019452008000d03c3c0d000314400c0ea10812a40014180103100a03010b80040c90824208000c1c00901c28104040d521203a4000000025000c818000040c4007002c6070f200580110132051002d07507041d07039980306001c007407660880101c0381d882114521040340702e581d104c242c1c00748100000c20910240281d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 360476654 1250 360475404 360475411
    0xf1b0606050a030501050108010c050705060f040c030c03050319030b0609091503010203042a1a0d150b0a02150f01122f010f02010504020f0d0303140114010f0e060403060203 76
    0x1900042207510380e000301d080c0d0501c540058070944c1d124001002104d07070034410042a0f0542d40740141c28892031390b40b03840d2180e2000c0cac000d8040301000d0011800780f29039200380d1401954842d05030301c01070b0b82c3c2c2e19225440e03801c90340d01b15800b00784604000f00454001d000f40d03d030850000780541e243c8400d540403c200c8070300181c184c2900d074a00744420140c50300d0901c001c502035400703011903524100c150b082c8009161103030421900c003203600315410040418095240810007070300498641d190800c0d00d030040b00a2000702c840d04d55a8500e2180003c404003080000c00c14410103500341c0b942212818043c5218210507188000e06c10b064400410085211040d200710441c856001c5d0007100f101d181c106410f000042902500c400610204000550f0b0080800c000c0382e01c90303000034042031402d500003e0403003525401e154000c802036070b214820584660300c01580b10201c3c1f0310801155840d8821540b0001184440f103011407007600c01c01341400d0040c0c00c01004c40c00018038052800342580ea40102a40014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 360477904 1250 360476654 360476663
    0x706030e0a1a01031e0c0627032103140601180305070b0901090e1b0c16030b31020105130b0a08090d14270603010e15010f1b 55
    0x30a0100d0002d048444032546241400c4a0710b5041d50550034040e443e610500d580c004021343d0302602e1000185002041400c40700b0390305007a12880c0c0e000b998160b90b059001107030503400e050504084204401c0c02c031109034244900d144420312600c8804240c0888000000a102482840c0d00190007584902d041c40503040c6d000d403050030a16a6980d5080c5041a2600402c0345440b001c2000d03800c82d40c2c0000403c0003060390f40c0c0e404501d82410941600c0d16000312171890340407000003903115130b0148100f0200c00c50148200e10700080c40d40e00d04000b035080c0300c203880d00001c10000303c21003034022085d00d1654188042e91100080c60548c1c560054890390301c190858414004425070024001f000070700039000140340303a25140343c0c41c50010307072841c10720f42d0003000036017408041505004c042c0d22000a841507581d007030712041400f4103c83e4000c00b003991b9000001da4001000000451101e404903401401200d1a050000c1c0040201005403500006000c80c4000154800d000c1030542225407623039202e49014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 360479154 1250 360477904 360477913
    0x90705030a051e0c060a0201020a020c06091305040219030311010f090506150d0c09020c010c0504060516060e01060b1209060106121e0c030903020601090c0801031502190e010f0c03020706030e 84
    0x40302c002c17810710340100c0d4419025035408668408220340502000c0300d15603040311918541124440011302e00c2c00d1810040120380c0da00c1d8005000c41d110340140300740c109120769545100a60705c0c60000c1c4030302d410509000b50340d401c1020004000d0501e000b041900740e03001c0043e1031640c1e5420f000301480480c040840303a00000041c24440800c11440049019285a242c090390356100051000e0030f4038503415000003004000c000c10044154031000b0790b1a2003a01c0b40d410301c500c240f103003414006040d0b441991a03981d440d02d003001659a00c80f000415202c80c401e0854401035442010883e140c1900340705035404501000805944441941d200d0341281480d1072292075800d83c0d200c1143d0442d86e050b104000030941d949a114281901040030900610300c2040504c4800b031203040c01042508184002440780b8204e203503010110480c1d405480c01700c0b60b9400030009400c80000002e02c8030010b840d205000c03502c0802d40003401886006540c1000d901500245603031458240d08500400354041c0c910f24a018 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 360480404 1250 360479154 360479173
    0x21e03100b0a0e0901062714041a03010203090c0a0b03060303030a051e04051f0506060f07020607060f02030109060509130206130509010e040c082404020109050d0b090705030a051e 79
    0x703070000c0da13030702a128a5641200c0f050150b0540e8203a80703040c900b8420300641c441400c005108164200c940c5042c401c0e0750110f08010480d100291004107840415455400402005a101d0001407085c50b2064120b400c8090301c1e54610000d1602e02c0240d0304560960030400c0084c620a540e60003181d013000e1540000008040400900c5d500c4271416503003258150008030b40d16522140b40c004207082d80d010300307104001c41d04201c40010352034031580c11041d03020038001c500c04041d541d0f400c0640e017440b5000801403014180c822a110000d61090107515a490304c3c24401203418145034400c02d12500212102c0c1c60404840e400704110f5030000d0f040ea180069100c1000720f00c0e5111b2000740d600800b058003c01e0301d1030901703107031980c9100c40c1504549200c0d030200c1221903111665021208502c16440d2000716a92100d000485061810340c10254000040804800c2048001d4001a21416004080d2245607485608044d11a49400c0d0b028007030758405109071074203665591406440b61221000c030740d0240c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 360481654 1250 360480404 360480409
    0x602251218080a0303050106030b03161502071e0323060604050903040911090907020a0b0c0a02100207030c0c06020c011d06070501180515070c11040906020409021e03100b0a0e 77
    0x100710f0441140060340f107900403c0529018090003942c484210050304138400c10030490b946250240c0704070002c50444080821199000344200400707088030040800c2c00c1c0d08107103082d0503419240d10040f240110000913208400c601510b5400072152180d01402294545c041004003a000192510400380030401000904140c00d102d2290030f0702000c034102c4d49442d945010400030f0341e0700030425020b54004052072800541120ba8981e84420902c4081343c4404810344202c0c500b0300707140e40e1110300c9840040e45106160f00810012091442000d001c181d1a0712a1004c0b62548007180200307012514110303e0040d101001040116a284041d11450421113351100c9081d616a209454a405180400c9805100b4103004140703860900744801c0c1014207020000810030b543d0084054580781034042490395586e900c0d00500304541e00442c0540d02d840d00d0307603984402507010f2070b600100700b8801400e00c1003540103d01500d20600341d50041185840c030304481c09421381d00c1041e45000704060101c180c50311743e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 360482904 1250 360481654 360481663
    0x71e060e040b0303210f280b04060f050405090c06030a0e010b0306180706140a03050603160312090e011503020c070f0306090b0601051c0c020a06020403060225121808 73
    0x501070300320707172009204510403a07046502011b0030114030b0290071010000305040e030b030000300c04038800d050451391540802007100006102c0301c0100740e800703420f0050024498194101c03020550303100310b6007007007280c0700e1250a0b80d4480c08060300c00d420038024400500080c2265000c1c05c02c840b04c2c82d0010406440100000741080390464118181568815803001e4040e410031505000c0c01c40f0b400c10840c2d0480383d103101e10385030103005140020140c0b92000562140c42c00e00c151a10700c80b150380c56614941d12481e2080c59000c0303c04008000a8810700300040e640341c8000101d0403584031903040055401810000c8010354065980d110080c4100c16000403906d40c1c5280e07850055005800024445031186810000a0800317001103040200078000c1006001c2c007002850b14460107604001516010307100181e060243c405805440244045000800e000e1a0340042c40c61400c0d210300044d00e081fa01071107010520110304041c042480741005070302000e000302d511900004034480c00c14000380c2c1e1480b105241 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 360484154 1250 360482904 360482917
    0xe10050d140f101502030304111201020c100b01020106030c0b0a05090d1b0509070828150807080d0206041e02060403050307061a0303070f02120f0f071e060e040b0303 73
    0x401e2500000c00c0f41ca545070030900d401030300d01c60000f900300b0207402030025034030b00001d40080d2100401040b01c10071580ca00482c818820702140c000e540359a014444c09465840d80e01c0f13040422814004213550310342c4184505070079a940441c1042d0054140f054286039070f0003002c00c290503c00c1c10800f00005558400040e103019118040d0306184c010110000121171040d98042030007142c883d02404005038000080d1039020200c00e10285011144042601e403416049984074800c81c60080d04c1c14000600f01020002e0700d900000722038855644c2e1040c5966240c000a1340801a0088070224000071b40091951228003210b41228070080d1080d0001000d0354003a5000329040c3d44006500410010580100d030609842841d030405d040014001003a10382c8030b0624001c141c803400c0340540045690300c0c0102e464505030401200d1244101c923618640c0c500c0d403021503112601c210000003c0c071080e003e19a035800310340c400710822280c1c600702094401249240c0d0881d40b0548440d1032940d40c2d1410030140c5038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 360485404 1250 360484154 360484171
    0x203030c070e0a1b05030a02070c0f090605190308070f0515010b0d050901060f051201020d0932100e0a060504050303011509080a030c170403080405100e10050d14 71
    0x7014200002c0403c03c955004d2001c1c0c14041e04249020301180d0020103aaa02510344980541d03590300502d0481c070140d5850300001c4102d409844081040d04659015905803041034400c5945144442100202c001d03403807000030303c20002000300382c00003142e00e20910b05062080003251803203003403100b0004a684c000d0300442c040e1407000c0340c200b0644d0828040d81d900010f07194000c00005007400c2200d41038129502459000d503036907000f0060124801d50446520010f0b10100300040c032818900b010403141503400d2803144000b144030000d40340303608010300038607003142c030b001001180d444400890241c0541005503005006c4e200900000c12494080c41d4411071040c40503540c0e03581080901c4200d60901c0401200b0042959814440a10001072600759103806081c514500c6155103000d00c40e5006186000491f1840070400208025185001e4402c2e260211020080400a404100c8001510144495105401a010320b50550049000f8640f10361089000b01d8401c01104008190356001c0d034052a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 360486654 1250 360485404 360485429
    0x5040506010303203903060a0c050408010509030c0106060215061c0204020703020106030c0b040e0c030604180c03030206060603061c030201180317011a04360902010311030108190203030c07 83
    0x1400c0c40300e0001c0c1040b000c1140200b9508205c50110740e841c10001c204101c2e05545291038010140a98107450080103400024803103071600300390183d200c0c2c02001480ad400c0d03080c1800451183d0010410103224008810500c0b110f545540820191642e0800c1d40407141c1da50a2070080507072a21b00062a005001c4d400110f105440c41c5011542882c0c2ca9001050f801e20600062182c08005c1c0d41c05a041520004102e440e51a02030002d4020180c0d0780b040b5842c60000c400300030400c1101c0341407000f140e02075001c0d650b9503a61502031081c0e80c84221021355001d150450051108081030701847ea000b402071000103541c03101c0100090f2480c1d1117110540118182d14a4100c02c1407441c0304550150010400e10001c0c1c00d62842c00b0f02e090701950080418581703504001c03078007146200410464220500042000010541d10700a00070031480d401a80028104030340c19000c81d1140b4116412150301c03200a00d4102d1441c0c0d1641200903481200b01e0707150004105404041c0d0003040b2074405003c00d5104c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 360487904 1250 360486654 360486703
    0x90501051e1f0c1115090f120a03120606020c010f0507050109020901090902040e0a03050412030e03030409020a020c030c01091512022b0c0f0e0607061b0f030504050601030320 77
    0x401100360f000e040f40d100d0f582c8404200100d541c4e65094a001c6d1505940c489600c0500c40001400c1d6445603185a0891040c2004041030551184915040005400c0b0401601e034035130f03404a071126088100d19010418800a05240e984a10300900401d4002d07000011200800c0e07002a500c42e0007a070007104000d4403440440250f2504d80b10b0081700d000c0d1400240403684d0680d40c040e0072070155120f5403400080405040003414040c514101d40104014150380c1c1d941d8581d400700000350401c00d001c82c01440303040100825400d0019044652410507118001210f1414800b9040d03a1400300e007600c1088540f1a0501008507540040e109030030440d90001405c062030b8106015003100d03000c0041415043c1840484010340110008800c0c01e42490302d00a10728409000c0346d02880f07070980051040340f8085480f02d400e003403280c204245034402e40d183c0300400c881a000702c054402c117803000f801e02e400810040000a00405a01c804c004642810500b40c4150700c3c00c15003026400400890038040d1400344 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 360489154 1250 360487904 360487913
    0x90a090f060b121602150c040306050f04020d080f0919150503150d02010509032b0906170901060b0403080702010306150203091201180516090501051e1f0c 68
    0x540c405000c40032103460810b41c0074081c2c101d0f030a00143c072420100042229030346900c0c0c42846440c4070389400b80100011030814581c42e188a52092000341e0300079241001080070600044541c40c013840d0010440702d60117082d42c440c481540d010019240d4500410040010342c1d803101802522000c0340e404605580b01d00c1e2a0750000f0001c00c0f4403610007040820008c00200c4a602941000700040550350440c81d2021440180c0e0203100c0c402c0c0540c2e04d40724070014142a00c620800f5400e400070b400000e80c0c1c2001c081e0a040d00c0c040c0300c40c00382202181800301c0c4c1d40e409009482446602480c11000450960343c0d54900700050740c0300e0740041d0f0b8204000501b00301956010302030300b0002e040303281c601c01680900700c03802074803401480c002c0c0c0c0c03007182420f09101840d902500300c8140720030002c21022050825262083c2d8a0550240c101c00d103a001a900140e000014858103040340c0300941036418440801440507070004104007045c1c1c0c0090040e9151000c102c25110300283c82c14075413114100d0f070030309041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 360490404 1250 360489154 360489161
    0x8270a030b1503010501030c290c010218030606010e0f030304090504050d08011a041401120c0f080a021612021c031a0d11010c060209100c02010807030506010e011202090a090f 77
    0x42c2c95000703a05210042000510328000d51040710865600c1446180060101c40d403001000024039100001c0820504000501036008005e0801c0600c81500407405040603d0703141d1104803012404591051411003545c10030b0380520050b000700400307891505440703503091800c0704c906030f60a48455210030243d80c101500008040d02405140301d401c0304002905024140d944900c1c083c034040c1510034407411071039901807600c1c0080f115180c402400705205072580100385c0181041480c00081010f000310390302e141c0503c200c608112143c055103001a01d1900d5403040c0740c600f40c24601c2148602c500b0360070407688500051451300600e580120b41010030204c40f6543c1c001d0050321512420042c1001c1000079801c04a00102180a00f400140b02029007410300007030040401e41a04405002c0000021551182064100324402d80340d150443d11604c034200c0c01c0701c40440c3c02a0210700024001160703503005d600513007000a9117031805032a00301031102140003480315a005a490b951115003001c1c5440d203900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 360491654 1250 360490404 360490441
    0x8010501090e040c03030e01030e0a03081902040503071a1605010c090b0c060114180f070809060907090504020a0305190210180b1b030f030603060a0908270a030b 71
    0x1039501102d4242030300c2d52082180c29110007018001068240c21140e4002d420102c59040a2000d80350903081c81e00b0003a14094049814101c9819400f000b141404001d20075501616809001000402c1c03c01d200f505401801007034004292200340700340616000c0210380d0a626502ca0320002c6011110321501800b802c201d90001e01e2001d5060040d01d42c600c000064482c112200902c0c69100010190003180030320481ca0484e460784510b0104015091100350f04080c01900b181d036404131a903549000c0561554420b40d142419a000036000b0441c054240d00400d4020340001e08010625680303680d128549103041c6e100c0c0844c04400c2610300c0a614061066404600c09420400c813041611114003600c2000c40c020140041c0e408100c2c2d0b0114203c2000701c1200c0f40300101200c0c0c3d90030340c020400c1c2e4039820031107117680f0174491100090003a80c8280100500182d1116900e8240141030300402d440e5140c00d800d002540c0b841d194680482d0345c0f00ca00e444015806881c1c64896414040803080d142c16660 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 360492904 1250 360491654 360491669
    0x705010f0506030a110609030114150a082e0f14061e0d051e0313062c0d020405070e0f0d050c0d060f1d011808030109020f070807030801050109 63
    0x104210003610042041c01403213505c00104410341e504100003030721038092801c18135055864000285801042051340d103008245403455120803039040020803d0000041c01200f038584c000800c881c900032a0650662101000310340321800b450040810401161500301c2e00981c481c0d114600c80c520740d1802c080403900304206131810315014002000d4195920280d450701e501507080c82c00d0f00c905100042c421010502c03111400e0030240310690030031a03500d030000c4400030b11818003043d001074480d00031141006c008a8903019110104840300009420016402c1000d411024403030003880160346e00c2c03082900c14071081c1c1b514562608900107008014a600c101e090060100000c42c402258000645018000044800942c14001c616010020f480804600b01510381080c00141405000b8011540307415020320003009008200005031845491442014109000401c01803140304c40940007003034252641000d42d403814402e07648181480d0b011081c2507000420b8030006101c00d692080c1c0c0d410051044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 360494154 1250 360492904 360492911
    0xf0a0921110108010e06010507050307080403110a0e04030801060c150509060a06050306010f0312050c0610181404140f0304140a0509070f0e0f060d0917160f020612010306020705010f 80
    0x1025178144501c54080c102505110340800e07188c1c10000200102c1e4515039101d4541a00e036640c1c0c0ca00b452a048031040340c1381c071603641c04002040c10003075105501d20864065891b511503901e0608242d6000703014805c140d52001a1203001c0c4c00c500c400b03000d624007580d41c200040040786007014045080f108140c204c5840b0350803101c0100541d150494290064030341000c1180e04400c0c0c00c940c02d0b501480307864480542409294100007200030003203004411074200b1012403001c0d04280d04c01c04100c4041d800129845d0200c6004580801c044810105c4540c0103030084a1140c02043c0d9060310b540c200383d0088040130100307013042c10035081613911300d0010101a141c0c2c1109081c141c2c400b80185080501503010000249160103441d503400e00a4030a070880a00700c503a40304003400e54000541440b60056909100a00000c18041100002c98841c0d03030104c20038080090003603070b81603140d00b40080180e80c0414140034a140c14080000581c0c002d41c4214401655418940740403800e55501040881c1c02925 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 360495404 1250 360494154 360494159
    0x4140712180602160f060c120612030e010521060f0f01170c090405040605160810052202190f05072a080613020a0f06050f0a092111010801 61
    0x541c00d000d44294040405a1103103011440000c02c10212200544030542c06211107061120551100228141c17688d41ca4a81001c0581c4900554071207101d8101c2c0e00d610700100707a0111b403040d61080302240b8140b510501d410700345202d01c42c15032903080544503a01c0068090212915013180e2443d105c0c0030a49011603107a141d4030019248031701e0041144a0301440400051201c1f1440d0203c402c0c04d03000410400090a0170b00700303030006040403600080080f02c18015481054000c03490389120700b03616009012000c1c105000d101d02d9144640010000e0b0001014a283c0b40486001400d42c6c18802070800b1200100020014650030b070201c100001d1100800c00c1401040c0d19501c00c020401d480054a1400e5840030a01d0050042d5a8403860041c003c1105102550b0700c000200c6807800e000b02c1355010840d464594800b901c144510036180490010003403242814040405404ea49060782407110006075a28007003015985e40e10181901034601c0d4805c80e04000d05003404882c0c80c0c10a180c054465170 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 360496654 1250 360495404 360495431
    0x21e0906040e2e0203040b0a05090615042c0303160504050d08280809010f1e1d030703020303010333110d110901020606190515070204140712 62
    0x2491040d800411071020403c20703042054000314603946a40c2d076004568034a81400e041d50402825509100090300b09404540c041c00009001c5014010318050314140c2c1000740200001040b865101c40544440a251040c100440f00d5181c500c010704040515a42d16084918041f5404841c2c1e100c0103200b414402030100f52910381407103040340d501244a0780c1d038401ca1035540550030072102d03000548000c54580f80168a0b440b460150007030110900030711000140c201010f068400c20380e2003102810200c1e81c138014030072158110012180c85503076041c1c00b02c0d00035412070342903601462055000d0790000004004024181034078054100440c0740746810307080510011a03d200617803c5c40c082e190340742c011044207040c0340000c580075080f11641c1040403442083c0c09403407a03040300e403c2e903015008000028402d42090f0b130100300c0d8402c1c0141009581828202000f01003c2c14518164403080c1c01e10004005840e64411680080f90761100c112091070269401041c181b0036122804000341030491010051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 360497904 1250 360496654 360496663
    0xb090102181e1c060507021b010509030a0206030a020403020a081b12030a030c031506090305010506090142050c06180a1410060609030506010b040f060e0d021e0906040e 74
    0x122040320700f1190703088406030b00701010308250720141c6010300d003005011159800003015000d48005010101840c0c1003000103458500400b0786003a05a013146000d0001860408019a130000c00030400604080e160f4000c1a040315150700011295840440701303810300404c134000308108031801c55406c2054030210001d03a031a0700030b00741328806050319000400441c50094005902409240340300d007410980d5207400400d142c04e02c3c407054070359510301000700302c15081483d945416a882c1035103203071001d1603c808040c010b40560a401c1c83c0106690102404a0b851074010a03e0200315520a600c0e1040c05d4082804e00364054224080040756a0036501e031420049803107038016130030014451420340e03400c07001c505202402c04002a207528002012076007d42084602c4240d80c0150201ea06a13070f20707010f681520b0301c264020b1030a280385060003008124401c440f4a58002c10140c15141e408843e039010803ca0b107144a81080b0310f5046200f00d00090030b10079006035000ca002c990a00c02e48e15200074080e00c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 360499154 1250 360497904 360497959
    0x10209010905060c0705100207061d030a151103010609050306161227060e2a1302090904050d11060c04030f1410050f01090207020a051c0b09010218 65
    0x1510081255404d5040c00d22100c2c0060801601072442400750354802500d5250078010340c170200d41201800c901c600110950130b030b00144090003d111340b9203940c41d050701c803082324801d1078a070a840e01440c20000051802440c000c050940312040ca96041008050410200410f1348401d8602c82501807240c40d40102d03d030031140307a103001c002003084490041540d030620040b5813403043c4814500c0e550401095602170040311114100f40c2e030f0b09084d800d20b2801003a01801020b0606101600036142514262445e80454000090010701e0715100701c000c1415104216420f4135075070008080d02050a41145407030316908044400f400d01454030158014960156000281c048c41031040d8000c10094030151720112015450700311103a02d4007964409000e403104649503c00128460000650840580241c5074095401040c80044504090520480b42c2d01484600d1107104001111804159808881801080c3c0f400000d680d0740752900018514a200d280040e010f0003091050101000403070b03c031040d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 360500404 1250 360499154 360499159
    0x708030c03070c15081906050a0e181f021c0906060806010b04030816050717060103030905220509030f040b0301050301180f030302031506190216060f03050603030706050403020a03030b03010209010905 88
    0xd5107406e011080020b0516401c6113401c03c0303588902013028170040c0c5070f541c400c000001512072140071000711030341c4421745010300108040060305c0100e1241c6440d000745c0480402c0c6900c40c107242c00607840400a40d10a450b00f500c00540d036034414480041c084c42114007410421518502e441e01c1c1d40d80d42d111903c43d020300c6610440d14101c070442049001d0140300000c103117141c00440131072940700395a41c03120028401280859000700300003965040032005640c140386074841400c1c211040540350f0b40a050010402441400200038000c1070448543c064800741401d402c1103030300d940c1884149400c4410800110025150b142e110400040c1081c2d11041040e50500d009a2207498400041c190405525101584840c001c144014180c00d6081a8054950b040d4204d80c82601c24150800800545006100c0007074040304100849030b01035009182c2106002d000c49182000c9500c6110171a1030036201180141c11040b100b1041c16410b0007926080c25007103008518140142002034055881c1c0e204031030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 360501654 1250 360500404 360500431
    0x61d040906060f0e1f03020609010302030403020f060c0c0606030705150a020a06050a1a01110c0d020303040306060b0c070b1603081305010c0e011b0f0308090708030c03070c1508 78
    0x801c1000c0d641010b07000340742036800107041503100c0100e020501000c803400c100c2915910442003091044c2c480d4507007203e402420103460101c0d0000110044e600090040d01903204089110030718403020409144218812040c40340c4966800100c1d50416034058003541c4690300500040c0565540d0b00b40d80d100c02485006400e544001c505c41c26800c1c40341c0d040000c6c02451810082040c90900e0380c001009080f5076070390850140c80400019510000158080c801e19030140400c0e09107030030402d0904802500090031a801c20f81d407552010141c81c02a041072480c80d1020031000380c010410441040030748940d51209081c000c0014810b004201c850320090100042140801c0e031185203108032802c0b03a0340180080c02041c00707000000c1e11103424499080c3c001114052a8003030280314040140301c05a01950360f142c810041e0300c046825100140030b82e501c42c001d400c000180c04008200401050380410b0103561104036500b020181c103047c076131026803a0011411404070707050307000c0e0307036a94003a50038a80c11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 360502904 1250 360501654 360501671
    0x1b1b040c1b0302070302010f020d2003070b13030206011508362a09011403191103060106080f1902090312121e160323060a061d04 57
    0x3221114010800c0c940a01d034001c01c10018140d0104195040e03034002c0c0c84030070324003881c0074080ba9280051a905d00001e10b950031980c034003d44074802c0610720040301003140d080c41d515441d81c24a9007402c1c0c3c1c3c2c000600040f05013f00400d03405205c80c0740101220440308050001082c0040d0015030000c01400c51104440326185102d03170b012140010008142ca00d01c0305050040301e205982d100c0c862002401e0070340742c0c58810700e0400b500c00d410315091009461302405900e452495080001106142d03030349805040342c03000380303943c06d0403150043d24010b40d260341d400000030081c58100603041c2c00100030052410200040440c0b49404c164200e048030911100003100510036900074000d5400c21641405020304030b66541c80e129010b0324010009054140440d00c54412101c0d1541007220202c2c40ca06c125030010301e0040a0401c040401281400c000c642d4128140d0744000c0c0d29025420b5400c4225000144880760804d484804068105424400c43c3c02c14800e1114042401c2690224429a1110002c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 360504154 1250 360502904 360502907
    0xe0904030f032a0201060504060b16061103040b16080402060301030209060d20091003020d020112020c0102030a06030b090d090b07020d1203020c190b010b2d1b1b040c 73
    0x39804515080b40d5000035a02143d000f0080051010103040c010340c00d010002c5200d184c1840390030120f030030000015191113100c1c400d10604881e00c0c0e100361880366403490010042ca501200075407007140704101070402c600d041030b03900c0084181e541019040204002c2000010f0722a00c0859066940440d402803081e9514800540c001d100c080000f0640a440035900799002d5070f950004034000003c650202003a40c42640d24162100310380702c00303503100c4441c1c0804c074059400b502920304c00c0f6071a40c00c0545030030340e02c0910741c3c02c2e030307105447c100d850643da05800c00900201810160304407925032f0250030a0a20804000d202c00140d02402001d0100001c40360110350b6080305460800d0f5104050016007205198007400a401202c0d440d8014091b81402888003d454540562059400100b00c4002c1e400d015840d03040307070070403669000505242400600b80f803510812035513000780c503036201075a5480700401c0d10b2701c06a0509850300140d44884070f00c03c3c100c030100d620380b2f0b440c4e801a1000075402024620 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 360505404 1250 360504154 360504161
    0x80f12031810110a0e150d0b0109150203040f2306031e010806010e0609010614030a02120a0b0f0a05030a0f0218070503010f170c12010f0c09090c0e0904030f03 70
    0x102c6611503c0c0c41071140d0b210080d2805001081d6070390f101c15415400045c00e01c0490382c200d401000c0408010440840301e84525404815408810302d071501d595034803442481007904840a400c030160b0b1000c01c0800022956206110103400042950f03080140b030946680d036640d40700f2030b40520070748010001555a4601c504c8841500300198608441942e50b21040c9880d9035003806000c000101c2d0b03500040040c208100d00c0b40c1211021f90b907111782000030320540b8a4540020348001500c0c1d800300800072808400c00d08660160b800d9040000340e001010007005001802100c0c81d60080708286400c001c1aa80492444110b03a08440d801103958120701c0016860449040c014083d08070000501c10000e5100c0d01442c1a20717503d401044a154071000440e82c17404c4445108127082e0310001c01c3e48e540781480e40030130400c0a0110000300e05150302c50f40325002c0d501400201070024482503800c100500c124000d819001e0554240a200540c540d00410a0500024009001c5c000502e101180d194466403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 360506654 1250 360505404 360505423
    0x80a080a1e0e06070315171009050d030f1a19031b031407032d06020301060527030303060d1104020304060f05060406060203032a0d0204080f120318 65
    0x4003407201580035000303850060140403101c03005846841c001a54407800b9204550120b0310070140300992501d440d0070507504020b5400c1d014154014480c4061450405000e100242d40c41003000e411038800d8020700904681403900950304282c2030051610380b000f10a47c0c0e01e0058a8291090f01a00640303805c100d8076441a40d000a04522500c1230340320401160000304401c1d01c0c45040884000ea9104100b80c1e0780f0351140c08040c1c80a140c482200115088010400140e082c2c1d114009040c100d582d01d800c000ca8200740d200714007044000a0b103070000c0c0c904440540302404074000e884c46608910000c40e9032400020405406075000c0d219003410701c0400c1101e00100c1038018000d6580340b810b4178002002c4c103901200000c000d03080c1000300f02c05152500800007a45e007294011429035807600140e083e100400007400c458a80400c29a0740840341c19802046e40c0d8400701405a540ca240050841c502102c0c0d0300303a00300e1070300581100c42d0b0500981c0c0449800004074044248071100f0082c0c80782c2801c03a801c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 360507904 1250 360506654 360506681
    0x1302060301060f021e06060312040e160e040e07060f09150c0314160c2106110c0105010e0402030616022d0a030c02030c0d02010210090314040608041b03080a080a 71
    0xc40c01c5d09166035000564500c0340c8000d8080d07030b5004101607051410b90082c0d000c0c0c03070300c5400c000e40010300c07030b11314001c980440c22480e241007200d81c031080021404640107100c42c0344080e000024140b041d5038000c50a00704907207140ca0240d0450b840c1a001080d80c040b180c12902c108488154440c003070602c60002020000b400c1944140e0b60158108030a1003035203083c404a0300301d00b440c8000108941c41c1100b09001b09501c0024100c20720b40c5a9590004151700e61a001d0360030307030a0001f141e6040342440f890f03028090204004400342082d004040c45c0020040c401400815110401d0f184107902040c0c0c2a8404901100c55a466045000480a440003042100c0192007004200c1d8141a440100c200b2058000c0c2c0c142c4045501c00000e01c4500f40140300c0103809070f0f00c40d4000c0070031846e203135100c651101d000307150000480350799160a522503801a480f603000560310380e0500061000b2441c040b01542c0207010340e0741100b4950740e074014031802038081c0fa03418050403d0008081180320742041c106020702 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 360509154 1250 360507904 360507943
    0x6170307020d050304030b070201050f010f080c0d020a0b0703021005061c0816060212070f0e0303160c03051213060c0210030207060b13020a0e0307050109210b0712051302060301060f02 81
    0x1c00001e00a0004460456006102030000a514000c163b002001d03036102c03070041c01248a0340c03014040f28030100d07a0200d03000304980a0009a14000c10b024080340c030f01c66405850240703201d48106060390009400144203041000964001060006c000c07001c0650050406465942142681030640b64410000d80380d24000192201501c01c0d0f1203980340304010300d0701d486504920300c4204452a0301c89030440c0350907503c10000100e40100300120340b12190b00c00c0d00301c0c5130003075102c4e512241000c504281d00d10030550b01080b4071001c00b40840e06940500304610740807051588540016260243c40d41c40b21042c50750005408040c406103403c81a14060042d0500400e03030443c00060300203501000b0008000f581e1910307070362070380d1038041607510455005964280f9041d0038400e450072424200e414018510401401c3d01c0d0000d240849824803444039038480c04200d8484400341c2e421b8800c0100350349a41100201c000006a4a40068a054407014039040100c0c07400020705900c0c1c01d40490a0a1070b1808 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 360510404 1250 360509154 360509161
    0x161e0e090a0507030f021206010b090d17040e01030c0806040f02011407020d03050c010c020c060a0e1305010303030b040608030901120e01090b0a020c0f1204030204050402060d051906170307020d050304030b 90
    0x481402c20302140d10035a00741f10341600c0310700403540b540c8081c003e04055910030420680cad18509884026255401025407031000d00c410410259954031683c401c2c4500707802c040041050141d030b1071038800107200700c0b0098003062805070f845100303240c400007000f4103100440d800d4003203100c00b4105803490039a00ad0603c501007503807410090034a40052018002079800c0c6401942100c1c400b103007120344080c0141c00507092652404090760048001c00c4000e4000126050708420303070006003c0c040c005c41c02900d0005242500006100c141c85207034101c04040d5104001408031a42d03c003030300c80c00020041e800004c465501d0b40f407942c0913116445000c3c040400c0303001441403811699001700306900c0124100e8400e000c2d00c590300c1e6264031850b030740c4141803041400704001504158020715031080c0300400d018a400118105041141d20541d014125a0450120703520444c40c14070654006e00f4003541d40b402c0b000c0710b500c0102e0b41e03841004402030084540b02c0002c01085810000d540c017560380038003065220324 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 360511654 1250 360510404 360510413
    0x50705010f0609050907030308010314031905040617090615060903100b0901050a15180b0316090801050c0706091106280509131505060c161e0e090a050703 68
    0x2041c2e010f810641d919003004140003a1300014200102d950503240d5001580c6907840c1c0c00b1222100120540ca00d0104024001007261007640034180030f40d071038841903112030400300010800144d600307114501e54084401c1c00124000007d40682c0217810360325091010603010b001c26820b0281c0d0903104d41501c51040c4c41c60001c1c07404d401003106220241c821200c030742e0341c1d0010044050021f100b600d100540340b070240c011381c61051450705108002e2420044045554a0380040941d2003210b1a03a02d0620100d006a0380540c4a41d0301802898168001d1000381010403641b0a140720301b400040c503540d60f9081d110708200c280021040c41010042120b502d805041e001c0301000340307040c0032002c140c0c00175400115886004a098440c403240242c1031301120b80060b0b2126009186680e01e81043d07150004000840d0350740c04005281c599880c00203040040c031540141007501c00540c00c0446455503100180c82031200c0103040c5421151030b50900700c0c4030b8481011550810040c82c0009d841c60195190100921 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 360512904 1250 360511654 360511661
    0xf040317013c06170604060311010f030b0316241b050c031518030a080a0b01030e0d0f030b12030d1e0e0a0c0506030f0a05060102070b0c160510140703050705010f 71
    0x8110341c40c1d2213100b90b90f03140100310031214280001800f0100c8107100c3c0311554850710b184920015141800655401200d001a281c10305520002081d5071805000780310600048084c803000c00004001442d064400e00c40140040300050084112081200c01c43c4c0140318081200c040c800740050251104030400034101503411400300e8189140b000300240815010728000704581d641d01d841d54a0070a561540c4000c040540010803150f41010f840d101e0f10120900e06004001018449407103190b1180210600582511510036900d446240190f1144030301010100441e8080680394100103041031285a8401081c460608501c15040c0f600d182074040303510001c1c084903030a000300d2400c0c10046d84c0748100060703803004071031402c0d5441c0c0010200c0e460b101d003070300290341100c414016119420745400340300c21705410055800c041d50b0b0041d161222941d010380074050260000780c59500111404030300141110200b4150001d86c48400119142414403c03016210742551110090100900410545019 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 360514154 1250 360512904 360512927
    0x714160c05010c120c061e0903031b08010e0405010e0d092111120f1f05060604050d081812010903082523030f040317013c06 55
    0x180030380d01022440b98010070f03c800d070360395010101e0410411306080c1190070354982441180d00c0c944400b034000c070890074000c04d0000c5100d4194002850425800c00406541035007101d403128040383d60000341e0840c2d0141d0a00e0544040190001c09921617240c41801801a600c5400aa0080324080d80780c403588070246100b00d48a5102040403110040d507507040c1e040312854020201c2c55059520350b4181446040500c000100a0981c0d00100c09142c5507070134400d0f1401d811850464821007901946400d2107000c2d08441c0988440303050038107180108120383c03008000030b800c4e02008121040950b028070102040444007515405240c00d1030030982d0301074103c415003180882c1f24007000a0b00705003108401d00400301c4503a841145480c074614240d541450311030724a01c040003000350704003e86ca41e200040d030091a580350030200b1072500f03040041c42c40751610001e00003503800800401c102281c030003000c0712101c007d01017480d00c80c0400d1456030105c0c0c40039400610700c60001400040c4030b074010303041c8000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 360515404 1250 360514154 360514163
    0xd060308120f07200a0605010b0d060b040803031824070e03160902090406031b061e1e020f07030b060a171002090a12080304060e0a0218071416 63
    0x7180e03220300c20000e00c441d100719810700018040507845944501402d2013079400d080c10b113058800302030094440409842d004d811209000c100010b0104000007e44142002083c04e280d180d4102400c28203000c2d2640f1010702a215417503442d00c2d02d4002c40324280512418849418a0f144207402c4601c407400c9001030031500c800204030024030807c0241004a500c2c0d0b4a00c806d4420300942d5814410321900030f400c80290b644d0060380e00c04010001030329044007180592a00d80500b80075a2070000010104445200c802144101c1202040c1d80ba03070b00003130f550b070703c105a14200e04110030180c0012442c004615110740042e2090314000418002c1a00c80b82d4003071002501e220304041d445040810b0302031001c0b050090709034040850151a00200c0d80070b803d9181e4001d120b0800c00fa030354542c803509009006c50640e9040000000d000030000c4902c114910130703801d10044c000c229030035000107200004800e05104007554030b10005907028403805000307410a8540300e40948880030141d140341d8260134000c04030f6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 360516654 1250 360515404 360515437
    0x3020a0210020c0102070314070506071a061504030209040809060d06090e0705090f0a0605031002120f130210110304060206061011030f0a030b0a0e0f010509011a09060d060308 77
    0x5107144045a14600b5100c180c0003080d600e45155110b898440e010300340003502c1d0140c4040410700740c0e1400014a0414010492401031600c8482030100205001d001c80d446142c2d4080c1402e8030b416144262800c881c0c04851a840582d11030405d04014400d80459540c004000a0003c26605c6e0343d91091094900c440001c101101510300e50780c0e0b840049009090380a2240000554444071030a03025501c0800c01c0008507005550740086071500c03500b9101220015008a0010b501054514040e5030114581340d048480d8142080e4150503207483d088040c0c01140d420302c003e10801d00641d0750700c4d841c030f010b0000c41c0e645580e100d0009448180580e40d5901c03403114159003100051040c0c1305030640c001818055803030517843c451180d9042e0b20403540310045c16242c0d400600c480d540c0a03124401480203058108130751a10103610300d280041600400e124240c034030014082c10031403401c0820054081c0041c0c558810400002803880d010300500006028204040441000843c0c400380124901c0f1480e01c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 360517904 1250 360516654 360516679
    0x9010b0d0509010612020d061b08010e060d0309030206180a0b07060612120804031e050414030a0302061519060c15050112110d0c0f0510020c060a052503020a02 70
    0x103900b038031401d00c500c51101714107984200c0549801140c02041c14428000007900085840703540b0b80d816528209280801c00220040050303241c1c0f81801c3d5130004049440d42403890711982c01070680d92880c00003034055000443d80e05a09991100507005d202d2000744803044482d921a284071050303200800c111202070410900281c1304503405580c14550350b201d80945118140c070a0b0485d81c1440040041d41002441a41c034503c0c0c0110030a0303958000385070741d9480e80e2281050400034502c122019070500941c4403090580100781d02140064021a403800390200c0300110000013032404c04444001213650745000720001300300e40c2040740400a03501c0741c65088541d507484011001103c1003407046450040988910400143c0b40e0540d07401d141e40c0c000d00c00c1c080700c1e2039a25400c0c0c100d4030f02d811000b146810f40605100c3da01e0038a003021100d8080344010170300c488100c070110745d0034000c21403000c3c02d00c0310104d01800030092031350070300c40d2031500031039070012030310180c1802566284940410b0740103c0665010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 360519154 1250 360517904 360517921
    0x3190e0304080f1218031905010b01110d0f030b010507150f151508040201050d050f091207170c19030201092006031501020c180f070810090b030c09010b0d05 69
    0x240d68a442c50302d6250708041c1c03000000303580300c0d09400c0491ba05004002d44110300c00c80c940103c00ea103070f014100000c0c1402148002400700e180c01026036a0030f902850014001c0c0d03521172170001106805140100e00c0f4a070560058400740a8943c00a1110307c0310000140002c406522170321007200c44000a1040400c1c2c111000700da02d10300c0c05100003070382c0e074150b00080072405291b545d50040c1c41858801c2c5482da403000901c046500075218245582000414004c58800c00c0108104094107081c007103141078901d5036486540907442d1000340d8040408591a00a654288042d1030326101c1d01031031860510340351400a0080c03800035000c0342e1424020099114040c44200000003401024014500c0d6480d15094510300140c80310406046224646520000d81c56503c601804800342115020150400710706107083c1d06402082d020030040e05804014201c80c1403a0080d003111400c680004211405102081c101030707900d0110303608041c400380005482d4022400511580402110400050711001035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 360520404 1250 360519154 360519163
    0xb060f0c010606050f12070c0606141018030311120f1c140a050a0e032d030405150702070902040b0c0c010f08060f12010f09030f08061503190e0304080f 67
    0x1000580c002c0920014600380c0c1200c40c070540240c040d044c441030b141010327510b000503a8250b8210002403207900d12010494209840c410740059564109040005c035468400719a550742480f024007040404e041da840000000d00c00c2030440303000c07040c006944000310f0180c640594085180c44544414418001c0c580700350f80e04c10b203a0b003604812110302968441c00c81c00d10180201404040850b03a82e252080184102000113059040302c01031103030b12520001d107011501c07150030071102d2000201041000000340010030031554078191f101038200d458407403242c02c91800010f0b821112000b4030001d03010a4101e4080060300b0424098801c0350302e02c0350300a004551421070100000081280a400b01310140f8204821250803940600302c5424030040c0b00b10f02e400c1d24100c1c00c0b81c0034020fa9603032450040c154003290800e076144e0070307007000c0340282000400319032016040404032924030008808142082d90b0b015001341ca00c555200203000a80140d04c1c1130351654464420f015441c419461018030f2001c0105 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 360521654 1250 360520404 360520417
    0x1b0307020a080322060506010e090402180403270f080f060c0306010509091e090d051c230a150b040510020a120914040b030604060f0b060f0c01060605 66
    0xd01805a85089989041d0340381c002800d1406000e450f00c022a59507408144c80b405040d001758008601c6003817000000d09122120600303240100303030354001c2202503200d41042c2d410410081c400c9012564550404443c200103181d072469140c060700c411003c08440a6003020241c4008601c147d8166a640f02240c1c1c0d9001c03d205200c4040e0080c200180c92802070300003031580040c0c103050152030300000200282100c03c0c100c03114032030041e507442d0030403100c0a0002ca065001e210710f00185690103030200050014001c00000c201024170058007001c40316030302c0d044498540942880e49050704504021a5076104080710745e1820b582c0740036400b4800420705146102200e10080f20507140c140dd05050204009101048a055110701c84e000c0c1c00049110300503081c0040300303a40ea00021400c0101c0001406c088500c41c0303104a0421207a8500c547d40801c449820a6002d400000d800c80c082c201107001e400f401554035480700300030131041c00c094400c000800216450200030401c40d03860304400d5500d8003d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 360522904 1250 360521654 360521657
    0x314090f010b0d320d05340602030a020405060d090611091c05071d0403030609050103150e0c090901140919030c0c050409150509010623060708070b1b0307 68
    0x4015564444a40307501400b90b81c5218148030042c841382000e40790034201030751500003c50004400f12003544545142c1500c500c40da80f1901410078015207210041260080605400d50020120328101801e60464005201c007a01d0651a4079066036044020305403100190b90351400c2c2006490030321002803c41d00204002000400e052200348138103490002002e1046481e03208005d80414031100c40120030a10b54841854904103140c90302d401400e40e0485d40c401e4559034107000c01400050000c0310219140303070621030700182c400c1402c40851b14143c1101d50480e0014810000d00c40f0030303d81900070509030b00c40d8000c1c04505490300038440d60388a40d88844a80d40106410696000a124004030410306026459004c165901c4000180886180c003508448988151302e20b49100d440c280a01944091054002c0003010b14001c50305108900401c3e00300086440c41c440c140203691850152072070303550030040c01f035114101450210100c240548882036054299460011912050000c49200d0401c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 360524154 1250 360522904 360522923
    0x2010e1906111e01060f090608030901050903250609050d021804050319020309101d01050f0409140901140403020a030507020d0212061902040b190314090f010b0d 71
    0x14020704450150101d401c5068a0060203040e04030300040284001c40c4030111000001c0b00c900e0105004407000f45a030048440320704040701040f4200000c4240e4078424000c0c00c0046d501c1c00c00c04002410810001135900c032040100300d1f00096054a807070f9860944425458820441342c4410401c106001070480003540146490407001d40d500c400042e054100740701e14120380c104048440100140d24480f203c450050303002185841c804e151010b0032142000c5c00303061106480061134030501d882030219003590b0502c03a0014000151851040c1180c00904a00300d042200421006040d0f9050740140c405020640c00d10741c094001c80300b80141d09000b44d904d50000c15038804141d0303043d1481e40120500b84da01c040d40040705409600e400020790070704841c000107406540380c84070b900c0102407450007075911910720610041c005020f4480c100e680401090000d070041440c00c64003100541211005201c014442d1014088907010002e00c00780060700305002448503407030540a101484c405c581e0007429104d41e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 360525404 1250 360524154 360524159
    0x9121101030603020604080a020301050a090b0601080702030f0a0305040c0506160b041e060e0f07060c140c030d021b2e030e0d0f030b06040e24030d0503010302010e19 73
    0x4441014166404040c100495031594980000310107030456440a078050f04500c9070041186000e00c1400e50195507070b07508000707001264036240c00030030300103002c1414061400c02040943c0e0082060fa1084100d882c0300300c0da1100201c600801600d800d6804480b5443d085501080340e103090400c0e41c6800074101c6e07a26094a40940724050040c1c4058010344a5142041c10f1002c40881c102c005201c583c01090003280d1111010286440c2c81380c540c080b5801070300f240b80140803499101a42e6107949402c14140704240c1d400b00211824942c810310b481d6418451000341c406415000314101c40410b1102846404078440c0c10144030100e90f04c2154615201c43c501c0c042c140700c100741682d04142850a18000a000c041c1c0f500342403400c07080c1d4500c0d501154003007081101c0694113011710985001c1c250740e800e0400c1e2810000b41d0140d280a0614080ca40714a6078082c070340e0405c00100c4d0b1180200408071281e10100e024003600c0c41d8000e0000b80d0010704e901c40c500905003001c00781e04000140f10100c042c01c0fa031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 360526654 1250 360525404 360525413
    0x240c071a10050306010b03180703410a0b0a0c0c0f050c0301090b0114031c1b08040b0d06090c0f031814060106351005030303040309050108070912 64
    0x4002401645280c0c0e10700008545078504100300781c064281c1813900c90703583c14064141e034055880d100d0084040c3d40104e400b400002d1010701300b000f00420303480007041c0342c071011204001906d140700501200390761102e01d2041205000680141402d00a120003012501c0303e20124003603421030141e03200891400c10361007000909181280b181f20f8003a800fa103001728800400203095404070074090f900006000b0060020300041c0b490043c5c0321200700e00820700c0702c44c564035440140032410103c1d81404000c01c0d402440155184405403400d50216085507030300c0e169454154207401001c04215098034001003c24000b11511800d6003442058541010152501c031084003d00f00f28541009603005480300b50001403070b19480a0b82c4881098054940c03581030030402421011000184803115180711441040b01d51024081351740c40c0c11080e50040c5a07030306d00400b803150b080694041505403000208000900d0f0740140808143c940903038481103544c0307a00c04103c40300c443e80e000e2a031407400740f040b5000c00907 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 360527904 1250 360526654 360526703
    0x210c210601110d0c0201020f010204231c1b120b04121209080702030d022107030507170d1401050a090b040605030d0906020105011e050105031503240c07 67
    0x8a05140c1003208100a0b01a641440960400d6001285460250604547c1c040c0a601400201a0000c500b0107142c05d082d480202c492158402d003000c810070420301d66480b01c40004200d85d03100d40c504008101c4c03a113005074207400107404807400030202c0d50020070181d1040401c07400c02a0091416100c680f501c0d00c034445040036254401c410b0058071403000d01500c5050055a0034107000b405d020b9151502401030501707002d07081c0300c8a021500b2000c1b810a0002104240000500245a0858030350b052807805035050301c203460300a0154001c6401c2040c80000050040154005500301480500600c81600e0803004080c050158800440d00041c0007004140c0c0c0110407031b07040244049440e65551003c282001101e1201100155000c00e0510000d074090086a0051102d00c00140ea6407008170030140300c0e40c13228002c041c10060000701044101d1900710801410401c000c0a460b6026401060300100c5050b2810100d841c40d41c81b000600f17003091540660b4502d039000001449600c1c2d2160380903240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 360529154 1250 360527904 360527911
    0xc0518040303020c070e0705090a0b031012060207051915050405030904020d06050d0b01031202070305031c0f0e01061a03100501030c050d0e010c090510270506210c21 73
    0x80c3d00c07610070001111104038a42d0303401007e0b01c0c1c031841e03a1885035405110510009420140d55140c0030014010746583d16070455045640c24031402c210008140f8061b00a0300c00c81101070a280700309240018a0740c8001400c4003203900c1020300360600b60020100000707540089801914a03082403040c644a42016001001c031042c0a541c0000c156880b100000c1d000d0340c80c07040640388144180018010852031080d903420070030460000300641440d40da81d03203a40c0c1c8500100388d0050311082942e40c420081541102418455681081c040e45150608080c020403242c403078038010016804200c80e44c90580c104490283c0110300b000c245990400c80154041c280c2c0d08117101c2000420072807000300d034849111380b040c1031118500104100c540c0e040000c0410040d60402c2d8801c1c010542200501c9130040340300002d200c5d400e94170095034170a03200c010300b01104035805190070800c0002c0300b81d1507040e201f42d00c1040c0b401030100300c0300316210310094243c540114440142c4091129200c05541c550881c0c2040d40b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 360530404 1250 360529154 360529177
    0xf1434050f0a0306050414010608060f01030609060e0604050f19030e040e0f030310090b06030105060d050a0e0f03040e0703020301030210030e01021b1f020f09011202070803070801030c051804030302 87
    0xaaa43c80c0d070340f081103900441c0d0503660203000803528040c40038207006080040105030010102410b11215181000d4010310000301840c6d5541c0c5120100800d98004500446214003620a00d00d0282860f50320342c191080c2e68000d6016424125040485042a4041a9030960307580780d0311000d4a0140001440300d105101e0043c8a49420000062001c00055100b5140000c2107800c403440c023103404041d607c0658103944990010f100610064990b4800d0303400140903201e010520703445030141d4030010480109404018010b62031848400240000144111481100c0d0b50380079a4444004500701d00003800000e60160294000601283c070035000350205031001c0000616041d400e0780d102c204200d81000040150b00201e00000145c460980c03030400d0329009100951500040b61000d42603446400c50850620410b121311201102955040d100100d42c03241e4041d40d01d05007118060700f400000d2204031030b00010881d0208150510b26004038841d010030080000e6910f407580d0650194024440c030a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 360531654 1250 360530404 360530419
    0x409020c0a02040606050c060105010201290109050307090905060a05160c050c09100311040c050406140d11190c03020703020906040b100504090c1b0f0f1434050f 71
    0x4002d070307846209460041c407091300e80d2956240740310140d50801c40164045810740e458000c64050040c2084403105044c0701910000b0420049680141c0ba2034841c0d42000d50907114035413000c10504d921394041c071200c500440451341e06c0e55806241c1001d68604a03180208501c60b1079034a0b0500b03000c0c3c1070100c00c4500c540c1c240c1c0c42c40562007022a01c20a001c03921a1341c103101c1c8120800c00e01c4a003035400f0505c3c40e4151030070310102c0d801c0d50b07000d403040c450f5100384000c00110801c0307122001c0c00c0c0421303a8003042c9641c00a22544100610884180d0050500ea03001c0120240900801030302410030314281d65490340241036400d01c0d64007000280e40b002401682c0042e2103500d5450250750b030707501c14982d011440d100d8076210342c20051040202c0398510921000e009440c29100c404c1441040030041c22540704803611032800d040e01d4000c036609a6510010503c841d05440518205070201d00540150b202c201100002c10100c801c0b00e0b01c03500780d0f840000203491704507800c0c0302c2c40c1410844003a00e0b407400b60181 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 360532904 1250 360531654 360531673
    0x4120804230405060418080f0c0a050d08060a0f06081012060608060114030307060c050f040e092b08060103061a04030606150909020c0a0b1611120409020c 68
    0x8070140030500c0c060010501d240034007180782600c203040c0c210304c00303075000c1010044203032140000203501c040c098407900000c41c50780303660035041003103410001008081e26003031030052400360f0f034503800001d0100c0031a072410b00240940c00d00084403000c80d0300d8401d08450641c0307008401d541c00000a84861600214040c01060700c499501141c14114400d441c0010914a03294510341011010380200b04000543c42001c101c2d554000152400709800c80f000040d441940002038074113110b01c6444144451000c240051180b0005181600c550b04c00c8094420303080c002e404020650701c25165107084900f00c10005108144500d045c660301c200306040005485031641c4075440d80049407000c50034029000102441000690f000e00750040c5030914802c040c510740c2590142c0110924002c106c000c581c0800d207605250310411091012607085001e080311810600803a031086040f0620003400305107150010050b0080008580103107405640b03035a03040c00e081044c00710196000c0b284504451080c400e18 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 360534154 1250 360532904 360532919
    0x4020d0b0915010b0307140a020a0201080a060f0b0a0206011e1401111606110321040614011404380406030507151d01050a03090609171b07030804120804 67
    0x440c0c003a141850383c4544900e0009001403144540b075a87c030311402c40520540f00c1e2075400103080003c890f42400e19040c00d1340c46010010051030746601101540d10440c40c005808101900140401011903083e03078079aa80314192126040c81da00340c0c0e100b05040d0403204210300601420f080342ca00005140c0449411091030783d00380b13811802800c5a6200e00c00b44400c0000ea500300c2d5842812007d60405141440741a9410600040d4141c1340b08400300324410000e0100440e640c04001c032843d504500c1022561625a905060010860000e0250b0f203070201c50446d5803d40740e0b02c0809071200c2c03061034164034070310032000c1481000480904d401a84440d00480000d40912100f8040c05410f500303c244003c5100001748400c0e0810444217101140d90782c04034040e60b20604590044140d402d0114107095076107441d81c01000300520107001d0030803013818400340c0c1d05500018070001c0c1804140c1749681100d1400e0a0301c030092844020142c00c02004104032920008075003a000300d004040d6039081c5a5200c41 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 360535404 1250 360534154 360534193
    0x207030c050109030e040b03070b0315030313080601050a090203250e13050919030207060e0d0807030f08090d05040e130c03050a1217060d1410020d0f020304020d0b09 73
    0x103040300800c80c015864105c50516220300461102c045006100c440d2030031090700030078032018161080c42010b50b24241c1d1692020021100702d8104582613a11465817100c0300c9031100300070b000f038a206109140e0700042c1281c050095901034135107645107600400301d5400700c901c20b15141d01440c0030310510714964205a600c02c000c00b260b544101c007012441e407901c2071002d414040711b2002c20030307058200030b01c950100368000785004c140c031140c1c00c080075801c613000001000c021007410001d0800f0800100714042551100b408084a64907446500290b2980140144c0340c1540340e0301600029400d00c020050149840074240d04034205c1080005440503980380d41510689903002034800d580800740703003010809201007484400c2e13014649035403040c07a044011100c610028211314401c580303081c040c0d030502071805141861014039804403002d01da808403500010350000c44443c0c2c00c0070301c1c100100159440368000c5070311a59000341603c100c41000e94450060040c042c003251800d210341c083e0710540700d81290 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 360536654 1250 360535404 360535421
    0xa11070b0c0a110301090c03030305222111100b060d0c02031b03131202041d0703061107020102030a0c080706090f020306070e030705061c0603080c06070c0b0a0207030c0501 76
    0x240c404142d403410400781c03400649091038000e0f850008420040b139400e0380340c20240c80c2e25150200305621188400408040100302e0b2407489070400c0d81c017404002c001a0030300990702c0011203104e900413000a0548010b00c00b1400211140c00421141c007206c0125440ba0802c078030000d000c0d0f81840122130190049a14051410000d13a10010300138400a050450040302c20705490002c0d8501001e01e0316000543d166445070030030a52000d6442011580e840d00311151440301c450b0303605010781210184540d10101072000765030b40f5141120881ca03084030241151103064040e0001c42c40d004400208070b174045080c0314207071400307002485604000b40050145143d040c0c0251450003150a03175004060400d0f8018040c03c06004002540001507100450302c0002c0b28422200c0315114801000c0d03040f0100304a1807090043c0e80340c00408002c0142030380103486035191034800c6030841e5840e100305690400d9541c0d0040d080c108403c000419810013500100910740c81381c0b42c007454101d825a0b58a007952040d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 360537904 1250 360536654 360536677
    0x1e052d010c03060f09050c04140301090f030806100206040b180717011406040212190b1809070e0705190e04090b01030203011b0c020d06111c1409030a11070b 69
    0x581c410003402c01c400c9134107000340074600c008012600707014583c21154411442820003044034a001c00d80d2541e801e52207a1181c80d040150340340c890380c00e403070002c1501100b125258414050003941480440c170019405215a502107006000c41c0caa080ac440710010500c0304061151050120100e9001180700748080400207050000c078400c4080c5406001400c00202020302952040c00400300c070b26100e407081d40d082501116000703025080040400d0180c201c112240d60028a803000441d61502d1034110303940300715840390a0710640e41d101c00800c94181820b8840f400041d8080c4104100881e0884031441e101001d410107044000100c1d02107401d4803400340040d110705110400400940c1001e0150003003544400000175804021074202a00920845402901400d5130481c8142000017590141d0740b1110032840c0e480d01c4904200e43e1003800c81030a51480321882c189648900701554900d003050103031007840702035410581d004c4021a9a20030100300804980f0950600003240a044002810200c009 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 360539154 1250 360537904 360537911
    0xe09120f040806010510082e060203030105090a051b092709010c03050118110903191401110f0705010b090108030a02010510030f0212030d1103041e052d010c03 70
    0x502d4103140c20a18160f00c100d001d181944a9010b0b102d90020b070132a80a0410003541c0c144201c4158a0b6155442c45003040440340c0d200140801c81e0b03038001001e14101c0303504a41100f04e9a58040c0c0b10010380350182c0d660881e00c403a240320341400480c7c8401601c05104060008000c140211640607a82017140541c5181c1e880c031201030083c0b2000a008402c000042810140045d5140411030300c2c20343c030804800c07813400b1b6030703000d0300c0400c0340582084481d5410010100e8000d03401200c070f441c08e000e801080440b40b0914001c0910003004d0180610389900d8446524170342030a0260700108215404001c080ba044d5603155104141c44d9203252800340a80460030007591030301d1a011011b401c41c5e002900226036840d48220820000c1c185041c40d03d411035041c4c0b030100e00f601c0c610040c41d10398080c01d40b4043c405030801504012200c000c1000e18442d6000d0a15000c0191895400d04003014070100003034890741001241450b88100c1d10141d81804003030340c1003031400c1004448a242102c080718548070000340c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 360540404 1250 360539154 360539159
    0x13090803040b041415010b07020604150f11010b0d030c030309050d0806030d1805041107050714040f0b01080f06012d0e0306131502070206030f07030f020a02070e09120f04 75
    0x4030703142c40c0c0e078000304108020300c410340d610089040c0179001403045060f0100300142e154119112402a540208400700c06107108c030703902940c090100c0e501148140c001401c0c860811390a20014000c2d09101d0b1b801030003810034500903880c11900d9004060043d018162100f101600003042005118030480b4950b03100101c3d410502d0415084c401c10304d40c03170010010000250202a85140c0d480011104111000282444000201855070003629006440d0f4085c4050000700c11416400561400d102200c0411040b8005841001120088841640051004400034a09102070300c0207981040c414100228451070603103110aa070034441040700b40340c0340c00b1035900c464607402480c80e00c80c01c481140905000e10380103896014030704039400d018049000258107a00c04c0302c03480d030440304401e4024104a550b45020104490710100c141c907550000381c03070b0000c0d00c00036540d20701c2902d10813900d03940601103140c034200401000440282403412240a0012042550710000004081d405403216015813200d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 360541654 1250 360540404 360540413
    0x120b130b09060f0a09031407030c05070608010306200d090c09020408030c0601060309120c060605040e0a110103050106050f18091312020304031703150a06020a051006050d0213090803040b04 83
    0x10019040c24074a1382404c41040009400142c1c0c40d81f80f819a096181d140d25031070400300d40965560001034101c1c0280d2402140f00e030b030721034166410b0324040c24080c011003954400108042e01d1440404941d68420700440010020542000e120180180440d012041d26405044203e078002d81c8150165440040d01508074842030080070b0060540d82010808200c0ca611840092001c0c0e42014040008040c01c03c810004594841c1c3c01808010748104000103400d00030942d124007100b02581c10710103515a48040c1d40c400c0c002ca42c185d8060b030703607540d0411500510040700c5d90414080740100243c00a0f0214481c0c41e10a002d500c61000b550303202c0c1102d503580c2401281b0040304040380046400401051000c60340300381b404541410b0118101d650f03a611090440305900b4034000c0907601c5a40b0103000035800f0350000d032001c0464000c1e0b050340c0385c084440c0300d640f044405910136150002d604c80f0082e0b01500d044100c0b032904640e120781c0030940790451768440c2c4880c3d0048030101d5114044209110502 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 360542904 1250 360541654 360541681
    0x30e031303140102030c07240c05090103050906010609060f030e03070825020f120a2a080303010f1a04030b010e07080901050403080a0b0d0204090809010f0207120b130b0906 76
    0x49215400131851424200c2e50a04d19220381c0c00040d0042880114150048003207058104502c0c9049000b0070140c0c1d1141c100800076070201c0c03e15400203080c04040340c0d00d5a4081452812200503480b62102e00e8540310090321400506070021092595030740b0b213120381a50510007050110300c100d04071f50b6541d49090035031030040360a89151000c0f594440b01140140c59a240d0441450000c4a0480c0c0c40c4146500c0036281040f0780c08020a40100408001d25034021848164041d0020803100c07000c45403251145540e03070109110b110203034120400108450001003044110f0380c19504c10552605440c2e4a03400c603584000c0c5d100500d242154030800c14103680c41034000c0d400801110003440306040c00d4074000c2c4001c00c05045000801d9403510a11501c0c1d072101a6812060343c090401d011182c0305003403041c92900700d400440d01107a100e04074000114400b10f0328400f80c50800304c403c0e2480003142c440040c02000184011000503101003510045805a010f141c8a84480c1c2d008101518001e100454030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 360544154 1250 360542904 360542933
    0x20312040e19060803071a13030503180f060c0703020c06040303051206010509030d02010b030607020316060f0902061602100e1e030c0603010305060117030f1801030e031303 76
    0x421a0a00060001003408a9000d422502c204002c0158020340b0740d48600400c180d0348140000d20001405004024205c5865034003500000c0090301070b40e8516454a400a41d101d070000c00090b810000208141d0302d2800044003003105404603481c0002e590482850b081d010b0364404007402011400b030003016130400601903c0d61040c0c6d98207042074919900600f0500608410b4002280d140d400910f00d6446036091350070040c03004089400c5200bc1d803034041d00900000d200709000340500000289190b0000003200e191541c8100041c62814907920750500500030800704441c020344a06490300960350b1440500300e00718012003801205680342c8108040f13035059100c83e6040c04a03400c5001c0b095070b960703c4600c42703440b41d0440015501d02c1d01c8000900b44515030300f102e40e00c4040880088144007001903468182c40c2c0b4408005940b140914605549004041e00b40651280810140312040c100000800340741e50103040c08100c440680310040d00396000036502160198801c8000c00511001503903482d40e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 360545404 1250 360544154 360544183
    0x30b0c090d050a20060403020103020a020f03030a0603050c030714060a0e0a0905250906050c0309040f151202100f0c0f11100e0d231603141c0f0203040e130203 70
    0x3403040910205086021b1884041d05040c0e0110b0048500c3e4002e0241407402a074040540340d80e40780a20740d15005000c1800207407120310941c034458040e400c00152000030340e0180340b4040022408034080001c10f41c071001ea254200300500a84404035154900120b000d454859004903581c41d041c0842528080d420003581842000c003088900219040f000c040b041ea4083c2c030f4096601d50307170716401030700e54031038810705c4c40d080b030315040c1a04c030400301c558060849401c840e1102070b60160f58441400461400140280d4000304212031484102e0264100f00d2000b016424003940000c15038490320601404038078240c40803080245182154030b00b01e68031311400e14050504030403603c49240440c0a0140794000181b440101184c91101e0b404084920090800310340d0807103400c0410361407040172554480c401207800c058504038402820b840458147c14481546139080c540d10741707510044954a10040080c1c0550204100c0441c00d801c0907000180b080c0265282e03e00484050f2060602d0b06805010004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 360546654 1250 360545404 360545453
    0x1f0309120315050111030f0d02040305010506060f0f09130509010504030f17040b0a0e03040305030a08011d06041e0f0b0306010806190902011205011d090105060604030b0c090d050a 79
    0x30301e0b45088425015a0000e02c0c0026110000c1c0d0802442c40c0304001ca004200d04010896449102c4a0340080069a1080c0000d02c83e6031a000140302080c002c0003880c1114032001c1c001181246902e002801e41813a0082403000301ca0385070f00c85001150802d1700c105c1c030b05944800810050540080c030202248055203000700100c00c0700c011782c082081c00a4001480c1e000c91401240941e0056040580340140460569988035960702d0b00b16521b501c241c003144081240303c40002000383c41c1c08620191150800c13a040c2c80c0b03a4465040000a0441e40c0001c0085158180b841000082520071500c0d4035140601c0011046035002c01c16103403c00582c003d400701d0f4840420000c00300c00303000987c1406204070ba00071417000401d02c010380d101c043c101e0310b1589191901c000012481031455201000720010401e40015403100340d200c900340d030400c44131180c110f80200403c200084400a00720781c0241d16013080340c00c2407008000902101007001c4203480036480100c04506010400c00315031003105407010080c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 360547904 1250 360546654 360546671
    0x103202a1009050708060108030c06060604060c06150f090204050405160c12020307121718060123030a0606030525060c03021e0f120903030313021f03091203 69
    0x21950350000e00040e070203180d110450308080000030400e5002801244096031925078490600503582d812090854a1911520f000b04507030f41007510031039081d80d042d907544414450607078807450701505100e00064403680c4800d1000402403600f241c4d090290070302c41d80140c2c0d283c1c40d0400b0803081d00e401a040040707000d207100005518a03000021008441d601054a01c21802812005d034114054104082c008120040c80c1036035003640540b030038420507034040ea420003d40391141e125004420740140100280d11100041c03100030004080c80d00011440c000701c0040c0410040440d0402240600449806481e40020b108228041c40b0346405500101c2d40c140784580340c2c2000845221040c8984024400d00b083c91005040c820b01002d0300c000d114a800e000182030040c5101c2e41c500311110413490038000e22404c442c004841d00122410b0b400d0040c011401c0d030310384449031204200e000c0f6003241e22262000c10f081645800503508054944e8039200004c40d41140c0c1070800c01c6017800c0c0b07401801c1500c0c0100340d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 360549154 1250 360547904 360547987
    0x8030406180509280c0302040f12050703030819090807050712081c0b1c0b1605030117010b130f18080a08070327060c0e061602010320 59
    0x25a603010400c43c0c001c00c003c4c40703070900031100904c8280e0403a140ea4104040740f00d0503034240e0001c00458241100e91059540d4401c2040a03406400c0001005500081c0c41000400c0c4078103a0b440c0c0042c100c05c0d40001c11000d003486070301110400201107840c0c50f00031a030310092002c284402c84c000c049100301d900301003070142c2e2100780c588100800c40b4040c0c42c101d400700c1118a00e692046d5000c4001a224044e281e06040050290021a0208884510400c40052210100d010983e030407181c50b0f4540a05613402c202d00b4281500880f03000003ca0743da00d0101110302e60b130382102c0100380382c20b0072000602034180611030800d80300048d0408070403800382c101c200001a400411103200c0b600501e4036031025122a035084019008070304007802030b0103004416400070304886802c0071070184500b404000140a885c41503e003807041000042e07100400707000440e554800c45500420341441403500040e102218000307004150b007540003d0864400204030b0001060002581c0740c800d01c0c3c1404110a041d407810b55 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 360550404 1250 360549154 360549169
    0x3050601060f0f0507110a170d030c0e0f030a05060705180105070804030b060a091e0506030c180a1b05042d060309080f04090e06100f0303030504081201080304061805 73
    0x3c14010800001603000901181c1d0100f486800c0703006103410360041e59102400815a105400c1e41c1c03c0c0c0c0070741003500c540036019100d100c8850145440d0420f20080e00350070007070072104105420f0b1b05030050356400310010b541030043c41c0c46203a09498013901c0702d440c50302100d07030a04c1c81c0301c286040c0700c420010000420300e1001030700c08a983c8415010429a03c51001c502200c0c140d038852210a8281004054100c00f4060701300c0a03040054030800459407540308040c1e030b988500c140242c0107005440c1e908a0382065211f510380c48044030b400490340f0024014480080f8104541d07140010b080483c0a01c02031a481e811030b50502441d011030030600203001c020254a614034460041032555903002d40003004881c00035100c200358000c922030f07210f540d58a24200034003400c1e143d00b1141d0081000140a5021068000c020b444a00d441500901d04503501603000b0f12000c0c1040d40c88103814010b4500d10b02d42c40078000c0c040d0a5610146450303510b89140a4811008512441d0903004038140c284456107032000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 360551654 1250 360550404 360550427
    0x140a080a050601110a050c1305061003020c0f071202090109051b2a0601030218010b0405010507020a0905190c050a120b04020702060a030b030d030902030a020f0a0f080703050601060f 80
    0x410004894480b42c0040c0c4486000008085150080000c105e09200003c100710740c0459042c2c0b00d0710b190243e00341c03018040b03078400c54410ba480484406900031481c801d0380600714118078241154184200007141ca0b103007042c25840324001c0e2a60b400e680085003404000280104540b81050145c0c0c20300305030204e0702d42020021600502c10118440141900b080342001c3d22210402c43c4a01c461108240301d40c45400c2400160302800c400c1c2100c40c1c8a0f808501d1581c1281c80130003200e802e160070100112691b0703000344003d0b40d005038941070100b80780e011841a035014041c4000007800b040d00d0002603000740c41c10071030100207005050220404003030b004000843c120f0144040090038040b00030000f030090262280c040d401040214112411a405900280520104404071004031074071680c1241502c20400000b501a00045200d5006050414104810140040240c007803070352103520203084840b45078400c16072680201d1040007840310520030030b405480c142c50301072501141810050500c0701c404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 360552904 1250 360551654 360551671
    0x110313030e0f04150e13081c02090402030f090c030309031b040f0e0f0c030a031209050a0b090102090a0905161d1504080d0c0b01120302121207140a08 66
    0x220110a5030b0796034050500c0e003004010002c10003040c0c3c03640c0190989a02c0e00590351202240c8006c00c09400088142c81b804980c0082001d29004180380406c130011a01030300c2141594090203056050303034590024520030034044803210a24904a00302901d441040b82090b40240c108200c03c0b2481d4401082d030084e01c0c001d600040d241e1800030404100200311042c0610700480c0341c549036003008040840d510007010030032801c07a034070309070314504264440303902c3d003c01000b003646130b183e40e00020504d801c415180c0d0b01a005a480701025900c402c0365078070040f0760903030450354009044c1c0072524100b00c140d0301509095208000500c0d145039440302507514003080f0380500160302c0c00800903a9070302e50028860040902150003540641d8848551a0040d01501c5018001c0d10300c0f07500341c1d61203070b010035003455048662491681d10b400600c0380c0c105052441602107001d07904c1001c0c0380e8440940180303040b41000f041e0f1a014603207018020801b0032a02c0886034941c0042190805441c2d00211a90b08842803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 360554154 1250 360552904 360552917
    0x315090903050c030313021203040b0d05040203030705100b040608010e0601060e1c080405010801092a0318080301080c0d1101050d09050f060a3602010302210402010311031303 77
    0x5060075074441c010f00140102620000040041d8150802c1031a000d0920a031a03048410022049581d12405140140542c3c040e044c82104000b451f6500031642160024080e81d00e400000d488071801c004520282d400c809481d44c0c800c200d81e0a10703101d07403c02000880003c2240d502c1000314640c80d5103040c850301e400c010549403c20166500d40e00c41e0011409030380400c10040e05a843c001001e50890701c100e502048812000160100b100c0c010080401c80349511040403104455600c1100c0f24284980b50030140d0791142c840c8038502c480b1200c030441d40074066407600da40c505821245011000b2070a23900403000e18948000151680a4a040203642400c01d5038403080344410030303c0189145840a08144941d0000e001c810350302141c41400b601d000380007440076984010102071803600c21030190f10790055a000403031106244101e0550010300c140b402600d09003180313412800f42c9030411905031a460181051008541c0c00d4414002c503800e1080f0040d0541c5000c2d501010783d405902c00240a1140c8c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 360555404 1250 360554154 360554171
    0xf0e1204060c0803072607120903080f070504080d051e0f03130503160f030306050906130914031c140705040b090420040801051f150903050d030c030b01031509 70
    0x64070343c25030489040401d103946d8990b00042c00680300d100f62101780103c0e24503d402031800000f40158603440d07030582c80f0825152540070411104030401800041003201c00d010200350503400384040359100c0100c1c2d13100d0b500c0d0000c041d42e40b0055214242c01c80080d4800b040f000a03915034030317800c0c1d0b42d22141e4034155210501c91400c3c01420351107403801030740403945401c030038030304000c1c110151004407800b9070b0701000741941341c10910500500039100554800360002c48104c03101000c0d0802d04005100d210b07290740015180c07014034a180c11004420703c01001d0520605180e03020b51142101d4500c498050710704d5414424030207841846a8060080b024100040806503a140c40c2c100214004030780d03004250703854030451a800c80c0c2d0054003400d0803d500b880042540b144031102030000440c900d90700300e800c0600d492603400c41d00011049902c1440300544d400404100c0500551a20540c191004688010005001022240c0d01d035140c6050500d0004000d0390902c02841e44025030310240e00009002e60b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 360556654 1250 360555404 360555407
    0x6100f1206030203030403240608100b120d0c051203070c08070501140a0501080f01060503030d050601090308030a0204140103091109060d061d060105010c111507060f0e1204060c080307 81
    0x2600c2e00043e40520001500108210b801820300c48981c90700d585012080e90144070080640301540309208c007950280c40301011078a01d40d48400c85080c40100720001245010341c0c01410203c03034007220b0f4042185220440d0500a050001c03145110240c044145586000c8002920120440304082e000f41300c0071901400f001000d6100d07185441e01c06100c04054030b0011503810242000b4000c0c0c0015000d403500344000f80805000701c0f02a914018082d5040110b455203413401090018140da0404c40013160000c0801c00c032300c0041d4018540103001603074507800d0401d440034420b91020480c1c10549413403191400f0424070045885410403c40b002030b5651100000140305217401000076162610740311a10b9074544154072412003801041090b10110b030398600040d20f2040c4241005410340c46d805034809968030b04188040c06001d44050401e0070415161503100071103070800601c000960382c9402c11010b50104111905c20007007900c000d9071030507081c840000c042000740d00e40101111004000328600f02d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 360557904 1250 360556654 360556661
    0xf07020604150f0e011508161a07020904060c0f2109030e0a06020106080601060309020a0308090409120302091801150806040209060708040e012c060301090803070905030606100f12 79
    0x30f00d281028011010380b04c00e030394000c28100065584072401100005000000410700503081001d800e00710250390300d810900c0c02c1c1303030f040c101b030700c1c02d61800030466900180c2c2d8070556140558091607000692500f020350103800140151110405d02c610b0009110b0703003d1100740d130f40100640e620b4011908841c0e9240559095000300d91441d400b000011020800a50550111040b44c1044045410170391741d2350016411a041d040b00a2b4109103900c2c41403001c02e00c158001d10754810301604c00141d00004e40c032124600b03403100d0081d50010741c0005840016160820049c40c5c25941240403a5095142c508507005985820700602c00b4004010300041140d41c82d64103446074040c000e03151640d580070718074004d806540a40212100001400004268101c041c00740b503200321403800060b0725402e00c1d90740c0992a050010b0804e941903403600802c2c0002403000010f980141d00f01e8039110001030400041504009004286900424141c44000300e07595019a49109102c03160800c110305449125001c03029 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 360559154 1250 360557904 360557921
    0xc02070e01062309010507021023030f06040b03030d091403030103030c03110102070215160c08030a02100e10050408070b0f063d0507170a02060f0702060415 69
    0x305000600008895800c0900b4000c00d00c540c6011035101100c1d1a03003011580500040b850015000b030060070010304101d05103009400c0541043c280c43e1a43d040318070003024540c1c4012402100100600288201c0da06100c1d4100c58200ca0500c03c4c107014802103035070781c0920200c0e41c0c019610784505900f80045004400400741c400400e070b9540750f0b12818068441c02d01c444046000a0f00103a440c80300250610980e001e143d401400c9640200710758001c02c0c1c1e542c000e10403e14124102050301000a079180c601c40700202550005142c45034508940a410400f00034051901181015031a411090000c40c071241d40040030f1400080940f1103042c40d050a000d0024020081d1802e8000d10062680808240344210000c88816014403058901403101a8060001e1980f0b40044004060104840c1c00c0161003010300e850807504122054884070080380c02c140030100840000941240c04940c14000c460f80000c614040907d0fa00709140000e40c0d518005002414500c0904801245c254498000401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 360560404 1250 360559154 360559169
    0x204021e0d05041103070e07050706110a0207081002040f030803100806071e0c0302031e0f040e010801050a0b06040306020c1002120f01051906050903150f0a0b0a03150c0207 76
    0x1c848079442188002048140c40c01c0c0c600c0c07800300c2c01d822214900080c0710010f0b2940c2d000c150320503880790181550103402014045466540b5002c00b41031503ca41302c0030704450300d0598002c1200b50315214009040a1019141ca02e401380100003e000070320600640d002142e40c801880c6550345d84560f400403d030250b941010915004078000d20820f00e50002804d160fa2246080000c00406071081c00d403841c14442e03c0040141e0818031000090041d040c001140318650100010f103440188144005150f2040e00110001d070000c000502881200344500d9901000100f4200080041d017070004580780038902c0300070911900040c08081c01301041c02548140d00310340d102951038500c20001c6040c509401c807034144d0030700d0601c000010715103010f840c22020190802840c4045500340702048800d5440f03482c080e90144644580031402c0041d0034444c52203846210011062800e2208101051740d40d11901207108a003145810310100300422038440c1080c0b48060001002040e112050b0b080c1003056000d5035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 360561654 1250 360560404 360560407
    0x40c02190201120f11070b010b0a0806091008030c160803030405071701020904020d0b0306060108072c06040f05010f0302130b0a3014040507060f021e011a0303160204021e 75
    0x5d405004802500c06a0300ca0700c01c9284036070b01d0f45141009070080400c0c032000900c0e140c010480c5801c10110050304411600f0a502c5103a840d07052061443e0301c034111300742e503640c0640c0c00c0a0400a180c80d21401a00f800b40155145051917251156203c816000303000101c030300d42c0300401903000250f045038020800070700300b95182c00626000320028000c0f49581800380c01000002107840d845240500d2107506d950715048441c10103060611702407a011980b04020500017940341083d5600d050140009044c41000181c0701c6081c00c0c001040036000110450074180148800214542c0550809096070902003d130390b2a00c402000c12100340000e410151035420300f02488004600e51030320140381c6400984400d2000a4113501809a203540071140a00305420003582401011b100d60061030680c2030701e1041700c08440c1020845604140660701c400000d80d95101500c0c1d00b074202211010031044203c003d181800750640f01a1004130241d10004d10582d40021040082e000001c000010f4000d00050503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 360562904 1250 360561654 360561671
    0x3210412030306050906090402090115120e010f060f030b04261606050606120604090311060f0912030106050319020f040f1e0515090f091302040c02190201120f 70
    0x20340101541c4c002d681c080c042000006201e030610070030706402254090034800b82e0785c1c41c1461010005a008604808002c1c000504219011003800342c4401d40c40c1944c000101e50329981c40401c00c81b241a03101100941402d181007000c2510f12505940c80b9400c03040c3c2a00c40640c1d10214903e031072007a1a580030046001c180c04070a007050101420781184a80020003264031203808000d114002d0a1500c800c040c3d0840000e00c0c0da0900e43c01900c100c601c03e007000100c40c00051101403c010702140e0100701d5200000c1044400310081100d948040c2017142c1081c0b555041540c02400d41c070004000d1806c0d10080001d0440d0310903113a04584402e9105030081d03840d03584a50700c40400eaa032620901441c0404072084040a803130308c030002c1d030466000800d90340c0320b0301d801e09140c06503410101305154000c040b50f600641030780319044002c0c4121184441700001c0c102c6841007004951203d0710150442d8003806030b514501e0004541c2c012440c2d02400c0c1b2010740b445510100d400b03480c401003003460250406290 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 360564154 1250 360562904 360562907
    0x3161e030305090c09101205010908030c0304050c040225150c0e030f010c09031b080703080901020105090d0905060705071802032203050f0c0a0c06110f0c0321041203 73
    0x1090090f6010029165841030f10001c00c81251001d0b541e981d013032084644101b000050702010411202c1c4640d0000c20700d4801a2200c50458004590380038480000100304001c210051044480c1243d0440b41141450784072003161956481181c00c5608414008002c1010301101206241054090700818040c11400c110300800785002908051702074800c82d100014024018050210f00c0c104550710070303094038955101c000001400031080c40f070188a40e6030224000d001841442c1c042c1d0700610140b9968103503100024210b0b40000c01000c0b1a03005910424612503015060304103e603811192035880e0790007400e100d403c240b417a41c00852601d1100c002c0c07021205054000d036107d0740b0b040320300b00110850703514507810030b492031031005000a4003000100c0c40a50700c1005003101442442c21103460300040e5555500100f619046075010600220140e501e0007800c1040c05407036182840548003d00d22032010075138600340013912645450340f201076039400080100a0f50001c100e030003690740200032207050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 360565404 1250 360564154 360564161
    0xf03020c030609160501091206021e210a1a090c12040b0702070806161b020409030c14010c2325021e01050a0c14250f05010203161e0303 60
    0x2d4008031004c0a0000080960044000604031807556070401c1c680d0141e603076217400940c450501c41c01800003001c1d482041c8080b5401a007440000140c80e0714800303040c00c241280c04107008008a04460802d000125107101c0c03140e030424240000e8504a100e61560001008140509000c01d00040403000c204070038050807c100c44c0c0a00d00b42d80954a0540e00c80403d2900d40e0011500180400d4a1414003103000d84543d2040d58102800b040a4040b0100c13070740005c007904c010403c01c0e000a100780c14050f082c00801070301c3c00307031016010000704032854081202600a5101d19001040450003100130004081c010b030403100c0c65100461108803111502c880006100360b4203405070f0290048084060341002e0481952101080503100c2e5810701c40d05c06801c403400da600b00421a5000819842c14082c203508101e42d8100c142241031982c1d0b0200740e20560061014294071119081d030000c2004c01c1181d80101c125080b0000652100304c01c07944608102e89460114003820120204525809051650550 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 360566654 1250 360565404 360565423
    0x15060a09180c1205060f0405070f1e0512100207140715030f02040f0302090a14070e19030206120a06030f030c14070302220e01061d010e0408070f03020c030609 70
    0x40c0b1005140b0f88680c05078038846a03141c00141158841c2d000308520582100308664080d01c00d200703c0301030030748503480000411125408a5400e01d207140d90078501c103a041d945080070b00070641d41c10444c0507003140416500c0903000d014403070b0564000303100c0c4203000c010004180b140d08603908440f0a1551010a140524403156500d4006032800340110b016222131300031a0110f5002101032039800d401d5408000000d80041c04001d80b05542d81d00c21000c0b0100700d035000c1c0c49032401d0b0312000801c0600303505010b200103140701894402d588030081840140d80c0c0e45e0503607054030907000c030668869079070002410060025800c054568144104d060f010140d11981c0d034200300e48203420183e02004100081030780e03081039002c0254404210a10000c004040184d02c800c000b180003030219107000c00c01026403c540e0b05405c80507030340c0d010011701c00c001103c0d041081d00500b6604241e294626094549841074082c2c00c1c1c00401c100da22800d10340515208000344010410f00070240ea0072130820003d03295440700c192 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 360567904 1250 360566654 360566663
    0x50105041a090c0a0318031e03050c040302100201020c010c18081f0c050d0204151b020109150216140301051006050304030f0c060f0e0f070501020307020607020316090903020601050f010215060a0918 87
    0x4011208c0c8852090165034000c994843d482410141140d0800410107000d5088100f199403d00c2443e0a100d0240100f0304004d0494071380d0480c9007010b240c40051115117401001e01c2c0d45c8080019500d0003080080140b49501c8000e0024070344640d54401c807042d20900b070105042d0740c00401c0100381000b80350140d040010540e11407800c2d02c3c80001e2103021407003150303001a0104210140030400045585002c0740103180381c3c0b050301d0801000801507110980306411682030071034405900e608606091040a400c840c44885981009280980c0101141b02c01817004003080440d402c49840d1074001e03207100d061240d1203a018040070324414440350050400c14050300881c0301c0d00804009503403010a222054170410782c050342c0742420035000c3c09a1a40a524220703054401c815041e0100c1c100b511000000c3c0907481000b185800050400030b15105041c1c0040d4400c0b0002900b5031616078001030300c014040c0c40442d80c0c1880da9a40c500140c1da8048d5940b001c02c07424101441c01002c00c00200c030840c0303950b108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 360569154 1250 360567904 360567947
    0x708090c040c0e011809140f0604140c070320030d0f05010f0603051003050303090a03030f270311030d02070512030f04080c0c03030d050105041a090c0a031803 70
    0x84100300410340303140003442c00101e03903c108494021351107107420001400030080c081108a07628000c481c200d13015041c003004c68414840a2200d0181e902140c2170300600115001c1c0301e06248001c9603904804082c2550456000018007041058040c0000d16184c924074110009040e03502c00b6415220750200c4c10390300c140c501e001200c8407410300910400b41621907070100c1032402410000c060300145800740215040300103580c00000081c0041008500c56268a00903040710303030304ca26016041c0d03281144806d40483c24801006003203500c0496001e01103150b408a07580403892070a041e00c000165005102880c000050007450300c1001d50003c00c2d9103031003403044510080741140050170354041a20351030b0041d4484000310b00840ca011028041d070250310400d46544102384d0000900d5070f0704c542d0380441c3c05a255001003000e46081d100e000d0b46134111180a000041050001521800b0f004040c04010310700883c15041c5581300750b000c40040b96560000900c03004c22070a0162200c5485000100103082 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 360570404 1250 360569154 360569173
    0x20d06060e0709030b0a020903030705060403050a080108010903050306040506060c01060b040f06090807260105040623091f0b0603040803100f03032c06070f020f151e12070809 77
    0x1ca4030f00d0f181241c1e0002c3e012181910350503441c001950040d840203a051009202c4000840c00903c80740380501d00c6520307000c1e681d80c80d00e0710142004c4e00590010400e81d142c0380300030300841d0704581240d43c04031041390001440d958200000fa62402690f0b00c41081d0340c039103e00800d0f0301c00030300010704c1900c00e00c0c1d115550301a42d815080b201d03815903004011313554010401c00c1000481140344241300c80f0304125070200101080303004a08540c0c0c1190240c171101d0f11220590304412102561200b400303102051400d6614004000d0f55a441c942c01031a0148000b00f0400341c8400041d50201500c2d13103008081668a050904040561350010703a0001c46091003400005038401e08141c00c041126456101c100d401e6922180d80c03048603042440d049020301244060700c0715542c0c0c0b14000c0c081580f20b12080f940756080c40c014860321058004d445402918000620322640703101f00d080e5468151204911030046241000c0c400d014001c006510444c500360b60280800c080d007021000b0300c50700310f18088910410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 360571654 1250 360570404 360570407
    0xb0906220317060a03150606030b011e0c02131406030c090105102102040803130806060607060f0624020c09161d100201020a260f040f020d06060e07 65
    0x180320450060114420032080b5180d42860050349a00500091034841c0b425a00d84030101621001358000c4100359561409018540d007620a5102444003840c00048110b400440f148540c8440b6241806000f205034a074821541e44661b0840307a081c804c00c1c10701103514140450300e228142070300e1551290240181b4040c040c1084020740e41210401400c070038040c542d101059940501507100c1b4034501c0c030003031141c0801c44990b0000304010f116100c000c0d0faaa9220501a2031405040e4001e40c445406c100d080c080e00365500740c00d407210b80da0462070016800d515400c524005020a9200400500c400c419040c0e240a8030018110300002c50b40955034400403000030011100b00442d09104504210110401000c0c418040f00c480034010344000c3d20100c15143c005170b41c44140600100c0181e40004420184d80e0b4841c4025602d802c401413030700040c1c0c002d00c403503d00c2c4900040c254a0181d000d84001828408040c946014194000e0403200b4414450705214000d000315000c0c0455100c4202c02190006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 360572904 1250 360571654 360571711
    0x8130611030307090b030a0e01181a090d03110409140f07090503060a0b0f130f0b120c010c02011713020f03030c06040b1024091d07080c04030b0906 65
    0x200d41c00d90f18484c03810309002852801da0405056401080c1d07888400401e043c10074401c60b0300e0500c42c06052102503000b49040301c110540b1415800e80601c0301c00034030542c41000221104020b0302804d001c103062640010b000914012035101504050400844044136030600000312b004499841c804040c80d03803040c10070707240f000481c0b04094050703020f0750025510b0301039603100c00f044450040a08219010380400038690698251040d00d1180e0b0340c502c0000e8050f103510a021a4010544480350151001a04035880e880007220803030500005400200441e0301c1068101700c0d03104041074125141c100320324032003c107c40c0e505040340100d184001800c400d180c0042514009041d1900420013540e8550300c03076288204c06840040a804100800324103907030850754811842d41009515044040c4040c802010071300c5d5540400450b0182c800c003e98100d5802500a85c04621402c140000341c03641e040c200e449202e0f80c0c2c0041e201c50b01240901294400201d0703200d00601d0403140d83c401c10700d690104030851 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 360574154 1250 360572904 360572911
    0x170408070201050906091002010c1209020906040f1e020a0207090603020f0d03050c10020d0615020601033002010c030f06050d02090910020a0f0f0906050906070609081306110303 78
    0x64150601a00005620602c01009030450280c20242800040b50100b0180600754407540d0160351a00b510b4924030b68400340c60010080380201c18002d249094000c9010004043c1903a0300507521507a264845152139005010380614050b580310103039050000d407a0081d0010903521006000b1088001055645d038080c0009484c0c00030300780c0d0071940c003290810600000065046040c003005100c18000c035441408443c11410051038096552030404000c0002c45400760010300c0c0f200440ca40301c42c0142d0b40081c4a506590344070501d0340c000035403041e980039425865010b003524a0350303080c070715140258190801e0755442c00540b424400c0d0441d000502d41528500d001c3d503a0403542842140707001d880c2c8044085d07048800a410782c0e40e0345091240320002e0381d00c0846008049803045410f40d0a03d40d002d0300d4000000b07481e00e001c0a0031800d090004080c1c2c80340d08009481a003001c1405c4040c0042c591001e10065401414240d59414142c031110b140d0010784101400304101d09a00002c0840c040700302c910 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 360575404 1250 360574154 360574163
    0x1a12070503160c06090206041403010e031216020a020a120302010f0902030c040c170a050f01060c0f121106040c08010609150b030709080f01050103060f0e0607111f0b011704 76
    0x802e2640403404980c50a00c0c01c10030b40f011600e400c05000940c4500c00204007412040a5407a1007034054414036007515030000b8061040d910130001000c150f1405410683c11142e02201001140c1440c0001ca141901c2180040d50100700080005010f000004041600754400e4000b4030941c0c0c0302030783d004219411090041c2d0580c100d031044d6401880d240e841060011018104207050000d510304400c01032408560100d0a99518024032002703002d100c41c2c20b401030010349001e404140d003a0303503801800c0781d40034402440c0203560410b40001c40d01552507030071a00307011300c11120689040e045c0182140070074410780300f0315460700501007a002c00d10301410314002d4951200c1c0c00914600500b40c001d0390300081c0310320100000e4010100c0c0c0c0443c00d010008507124140d0000c6015411400e002c02200e03c504c514a8000d80740c000d8030382d102540440e905511490504140354911400ca903410b007480386150a6070508450344046a021550960000c03040950aa0329080c040c40820000703164040103640c0a072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 360576654 1250 360575404 360575431
    0x605060d0f0803100b03010f08010e030301030c2903100f0501110a2a081b06031522020d061a03220515070203180a050612040501061a12070503 63
    0x1c003080ca501e008540201a0074580119265208901d120035002a0030034107102007192000c0103001000d0050390b45680d5010091865945581d8880041400d5841400c0010b1400b42d0690750190348030084042c10851445016980d29004026240c00ba032a8024820031881d1040041403d510170b0f007581918040d100c00500d081100c41c0c03100b00590030281c100d00300c0e00031138541c40c0c100d882c1c044c201400103013800c0000b408009030400140468100c40190180180c80500c10412000d20082c40074031144000d40e00d080d41941c0684c15022078001c1807001c84950350001a6040b48510280c0c004012100404201641c0802c103210100c83d6100c180c40c0c3d41c1c103101070291002181c6620000d42c0303201c648108100c80000044485043e40c2200031106940560800310f07402d0894030181440886c65170b0101c42c85810b0070b0820f40044e002e400b56160400f2404414000941006001d50000005e00070000ca40b0420071080a03880034071341d005001048005e0000000b0514180c000c50550b030081000c402d400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 360577904 1250 360576654 360576683
    0x9030f011b1812030f110111070209310320030307140403052a0a0803160c0e01300b070c03180e18070305070b0903100e0102070605060d 60
    0x31a11422592000741003040d201c9000210303a018408200010f82c880d0b1240d11400703140d20000740c0600402800f0a14507410301a1520580b010582140c60443d8101c03010401174440070b500320541480b040b20a0220381d841015583d400c1c440f043c2464000d48603644a01d0716002604454003004440540c7e0750303072030f4001c1c000708042c2c074024031080d10f141c040030105030700f055525180c0d05d242c89803c01c1c0c20303c0c0c2c0410801030070024400c1624030b5403124005031071b40d00c0d40c14034007032545c0d0756886407188a46082108101d84400c0010040c01040145840802c1e50140e50311182c85139000f015a06020211440085a1025140c40e11141d0311544e500805102a42c1d0344495044c2d40b003e604620490402c0b41d48050b030341a59030b0542107800903000821100e4054a4003521401ea010151070520f5465481040100b001400c009036034010342d042485140d4580342d07500c0c00710b458040410202c414003800c008074460704180540c09030180c140a0007040c821034a072001441401c50120038040c01c0102d48c902d28 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 360579154 1250 360577904 360577907
    0x303061502010b0a0902070311010908130b1e09040e0a05060115180506030c0d050a0c020d050c0705150c0303090a02270a0b0102030d09080c0f0303010f060e0a0b0d0209030f011b 78
    0x103481418041c1c09c041c01c02800550009003118a21306045400c24004580c44100c0310041e071741140a4500a1784151a103641c0c0340d50034004a2440d600720106d40c00025408049803101d030051000740030040204d40e0700501c24606551540000d0081640c829518040004120302c04c200007210616a00d50f0001400d040000f0721015520060480407182010004400703000013512905114000b21400010751220726000241040c0c411201d22081103400e20a1040c00c0d0f0000c07070070000b1034000301c40c041070014151281854901607120080c0442c003021040200c0d07031802145d9068428801c83c3c00c000f100c220f1095044601040710301002c0a01401000603070300d4083c9520075100c05c5414011241402107402002003960081d9400321400c036404244003025140402c4520481d00200c0041c41c00c560400c4002038000909114120030001d480702c6d1401603480380e0845001609003502d056a480900030540006035001c4480b19010748940d02813020428010300c030b0940480800030900c030b4240002d880 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 360580404 1250 360579154 360579157
    0xa030903030f030605090f070e01020606012c03010501080d1214070305071e0504030215041208030408070501060b0316020a053409150608010f0911160303061502010b0a0902 76
    0x20b94028590340701c5010609688501070380307104801c11101480c45107000d4000811241404003441e0655111a043c800140c0c2c2107070305500d0520410070303070440e0880c000c0020030040e02207445094140d40390500200c0d414101103007807031000340d6540752401c01c1c2c8808a0b03100c3c11265120658000c0c028081d0115004501c2504801c0c0c01c181c0c0c5140100c0d17a20081200c4003100e9400f0a13800300482c200007000c01c218100050010001500c10100c6410107182400c00c101c0785001080003021480000006010040e0000a580d2680c4e0024020045207032140c0c00c200c0c0c99807050303c0e0800d801900e0a045108103100048641e00c250380040a1301504900410102d801003100400511131034803450f984c0560180009000001d291945002c0383c2c140211404407605105134020074104144200140400e0076a01440f2003102c0b4502c50002e9803407481c141180c0f050088036280c004100c101c8420805050f41904180305503100c003901620b00c2030541d0b030168201d900300400c964105040ca0341c00c1000412550 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 360581654 1250 360580404 360580427
    0xa03060c020c03070f0614040b0906030c12070804140a150f0b1206071e050711180f010e070f080112020103091b03060606080114040c020708030a0201050f090a03090303 74
    0x407200000d40c810006400c0002c550014017640403181030801015501c87e031000622645c42038454942428100b003184244101c02000340203081c004081076400c042402103d4a03842d5900c61041c16050804008144040a075019168003a035200c5440301c8140200d00c076140c01c2e5210840301204216124104040c0c82e038036101100d41d9698203440c0201c0d032103c081ca41c0965811a000c3c1c4214580350b203002e032008040060300103075442c0c0401c045070415000000c4680e41504034a00b02000110400013070003400020910100d140041000e1044070012035030501e058072902c0c61001e00950300c1c06030072a02c040308036080340d0014120348010410110448a2038042c1c50040c500840c4c0701c1c1880e2a1240842c142c0711a05520440e00c0504205106180c450f9201602130380c40c201d5050752608004d600d100c0a108091031180d80c1d541c245000850007004208001c0c9101d4041c1d036103d40195002078000c200c210307001c0c00c180380d41070002035403e800820240400e56150b1501e13140b20b07045890803520141c104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 360582904 1250 360581654 360581657
    0x50702040e10090305031b0f0a0503130204020d0b03010c02010c09060e0d2406140f0f030f01050115020105060f0a06050d020c030d091a011a2a0a0c12020a03060c 71
    0x1481c4545802c0da40214000c8a000c0e840d0719649080c0400040700400444004407440901030254070300d46a8840103c405444292810980300c1c0c450304502d11504040c0c540086d407162000410840c5060960444844e20303030210300820039510110300507420780e60003000c0390300082c0b0741c4031013070012a028840d2404007207006480c5815011071039803250032481c9181c500b0480103480704000c0582050500940015006212020880b9058000419440302c0e1040e0141d105601244a40005803000c011101c05908444028040e6594a201c40140e030f07010a0002001942000700048450a240c40c003800041d1010b1310744115240f400004523440e8001200261985408000001c1851420006881d0584030301c4000540c141192030802c4022404e0303d6201c000c80803003001007000c43c0f480a0104515085114080d91710b4810000b07079074100301016440e03e55800100d89004c60440005008007400340304031800702d446501d591110607281d086d21002580850041020700004485400c090b0480c0f485 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 360584154 1250 360582904 360582913
    0x5060a030903030902030f2b1e030905060c031509010806010b0a050d0507020d09090e120c0c0d1406060a1203050730090605070203030403080a0203040e0a050702060a020a050702040e 80
    0x4c3d0b500007814014200c2d644030b09039002c0082d0360f03603440c0a004101154038184028011100044070050100c19440c40201030a50015000c51010740c060382103191401c0d8000140c0341c5a1420715458541600148d9591f002c03d400e0310310f03002c845d0403e03424182c16568040d004100e41e82c640410702000b40d002c00c00c22020000c0a102c411540c7d649401074078040d00c900c1d005000604c649110042035004145e1049a110b070400707030381003691180803610220054005203441d0381c4001d03068290f1300d410010000305801c03100c06521207083c8109580ca580443c40700344155015900d45000f0082401000d00030001d1070080040b400d0000381c01000100311a0f880351343e20200310040e14807050780e0980c21421510b40e050144500c03840d0240d108070300c10040d29032410418200042500841c0c0d40f40140e0000400f144030010341c480c0001d0003081a50700a15041c00010380503e003990700e0801800e429500540503110318000700310b030303001d441c02618070034a40c640e11103007080825000c01c0702402070209140340b10b028 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 360585404 1250 360584154 360584171
    0x801051005090d0305070b0a02070f0308101802090f031203070305060f040c02030711040606050417010f020a0210060f142202030a2a080c0318070314150105060a03090303 75
    0x48984140507054040d8891944403501b5041606500740e00400724060548100301460000d200001e0382d0300202d40516204805075668070994a691840d60004080208440c051300088500b680040114081c1622014000243d610906689203075600c0601c555403810320014203a0f41c4282e2140d6400f81004110444170501e900c045812a80c4840556006810000740c00b01400b03244030380c2400c042d506983c1007000c903103000340c010040d006600036410700251150340b1628202094200c802100c51024086654020000c0040d40d80c810251030428100d041c20000159602e1034025501120544a070000302d85804404101d1100ba0315800103284030810307210300d551a50184082c6101d080b914600040743d0240000c00001c01455105152040c16032003206416a648440700c6074108450030015626515480406440203040c00c0d480c80c0e540c891840300006001c0c09000e01d02400300ca0109a80208244081002c140300d424029180c1250040103a15038181c401ea10000c5400d0291034005004403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 360586654 1250 360585404 360585409
    0x9120f0204020409140f07050307030b010203121305060a020c0c0103020d18080c010e1c180305150f010b180f03011104090606090e16080c0f03161806080105100509 72
    0x200203400c245046a61400c0c09044118070b03100319500032619182c5400549001d47e4001c00d28400100044101529031954107070700d90003042640e00c2c03240414204140e0b4030341407032001200007181c034080d01d443c4505030100b401d2035158403c9400354112040174201c0b1210040c0158040d500c040e4101d14807039603c24449aa80100186028040384141001d51795000005d1030302d402d562005400b20b82d46d8204260340450045494541005a1700905241c40c10114a03d89d001282d03003268000b07081c034002c0030f0656045030a2a07085900c600315543d035503c0640d880d0050b083c0b49000c1d0b4482c0c90205050480d0400c0c0307514288001c69901d8400400128004403100080b400b6034226a00044140e03842c2d5400b480750300e030040d0f1014042c1c620803041c00c01310b281c06d410092400b44465030340790038404004041614143d185048408082510700225624140b881c0301031020b03055401a0400203040c4540f18005130b4100b800402120800c1d52031007107c0e401e00003040615080e032a000403c1c07010401040d92543c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 360587904 1250 360586654 360586657
    0x1501080d08061518030c0a0f0e0604020f0703050904060e042a0807030305090a0503010519020306040204030f15060b090a06030e030c150405060f0105091816150e04050709120f020402 80
    0xa80a9801d81540390b0408018149405440c84109101d003000040c04d00c40c1c403400c8c44201d01111000020345040f0f40f6000c0c0800c00a10400813030410a0b180020075405041e0007400815096600341c90420005950700000d4020600c160740040500744030003c0f03100c08009622908030308000d466a0141110f913120592884e00489510840100d0408036030349409140c0031441385c1c000c001c194002e01043ca42260880040400c0e08054445035601001040b02d50b21141e051310050b5521440345000102d65003001074035800c40d1820350344014100380001c10440e0001c0e0a5440440f0064400e461300b038100368068002e46101903031002c06202c140018020901c04008800100862110741509070400c0d003000390800303100a05d5182003400c0000104116150420080d62095010440c00c0003000d074050b1080c1050040c903600a411244e820001c00e501e82d42d00101600c040503515883c0c0e281040c2014081554812151038020940c00f200402c07040d441e0100c0e90320200c0c46140740d411201c00c542e002900302e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 360589154 1250 360587904 360587917
    0x1a10051903031106071e030f02030114041b0516030c120801030b10060e0405070513030b06040e1603020d08040f030803070e01020f100b01050408010219021501080d080615 75
    0x101040c810100207041e04103561484600c0c084015041500d4008805442005014441035198400000e110714803407103a031042d4070326940c0000c155030380d50b56110b2007807940e03283c01040ca00c5680381c010399601c58904011445803c2102d519000d040c070301c00303044c460072040581d80142c0a00c0904411400094143c40012141059945400350036505508100c1e190300c400400c0000c901d100d405060001613003110b08100c43c49811a40400c0e5981d84a01c100d506004e0080615942140f40d00c3c08070030005242102881100162410458085100c101c2551035096840a1400c110351460074405407c0c07a941a01c030540c02140341d80e1a05075101d00100d07840241c2d600c15200e820001c0144480e250303025140300302c103180034401000f814102811003511003100e0312540d1561681d07551108110390140e401c0d01c0007400d007507000b10345921800704602c2080981c0d40d8040018001e8103d0300c00751040e03091101c1d041c0e8403510000c01071020184019581c0c094081c01d5603034003510030f061024a00090310002c000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 360590404 1250 360589154 360589189
    0x50901050a05011208030a09030306090f0c020c0a1805150607050601150837110d060504060806150105120a0911030d0525020a030b010618031a1005 65
    0x1094a42076080c0d4003140c1e4181c000310607215000310802c02140d101001d0b65040040f155001a011340300345800d500900c025413240b4503c50410030207001c145090741c05111710203155026103200403000760401c4412801d40c003a07010300e41c41c2c1407020030740342c0460f500141c1d2010002c0c1c40103d484200c200083c804d9000040100c9182d4003190041c0b00e2905260710511405c4054200f02c285070400c02488000361100a0200d420140d050000003201d11519190b02c016090b452401c000071112580c102ca802c1d0b2200c1c020044547c01d1010000300c07070901e48152001c850550b03025011944a8518038100c041d82d20442904101c014020114080104d408490180058410019115140f0303c0d0144c18003d80440b264400c1d00300101c1800013640103000c8900503d503404451100d103074a241c079400c81e032302020700180d040785140e0404410800d100d5011410707a040c640b1045000c40031641202c0a00050740401010f00780c01c0d80032400201041c070358490704900c000c00d2441969840b40c000c24812012000180e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 360591654 1250 360590404 360590411
    0x100e060c060c071101020c010e0409051c03150b0a0c0308040c0504050a020405040c080f070c050f01060602010e0f160302040903120c050306040b030328052205040e03091e04020c01050901 82
    0xf040001d0508100700c032040c2800541400701c038500002c5e0400c440d00300e035170f8016a244c003601001c000c8140301c03401071030040300c003400314014400c000240102200c8082c40e11140210342c000c10181e500030103541100955a56944203c1803e5030220340e11172026108548482e10840c0104145e82c1e28041e144c8103400c103640040c0c403a4603180030031090f5940850440c040c4822101408148800400180d134000c2c0715060400100d007941c82c00034900000109610825440c02c4c070041003255042d0040900380000008450505141c02e4001d920b0344c010103512016110800703010001400c0c01c0e006070b410580071b81020a1144070b2045524103441403281f224002420010402c0010314180c0310303590807003106400031810103d80202c1d26000d078400c00308182e007000700c0001000180b40b04404031445104844007072030f1030300c0101402110b031820314042c8503c503030b042054403038040f04000241e83d000c210080103080010b207084105103c044c03081c0c02103500f05408001c8a10102c4090159500441c080760002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 360592904 1250 360591654 360591667
    0x50708121e070f0903080310051302040311120a03080a020f0c060a11091503060411071202120c03030a090c080d0804111807120b09090c090a0b100e060c060c 69
    0x1895901c001d081a05220080c082209082e138401600300942e54071481e130700d540c1e80780c0c12450854601a0341c00580d2000d90b2031500c0b00c910320150094000c0741d00c21100c48820076644030400524180c840c0c40640940c1c01302e07080c81b020900c00c0c00f00a0f0403c1f1000801072a1605009040d80f90341d21214810845501c06018000690030511034506000b21190a20742043c4043c0001445444104540c070711a04000c40800c05c0c0ba80c0d19440782c03a10560304c8000f65554145031030324003590358155424001500403000811440da20b004119041618070101440c5103541e0b81e14007000502a0358030a035202524920081020202049600004142519800014502440c1001400840c41c2c200b40c054506441e8010144295076590764000604e820101405000094117800a0000c0015942e2048140c0240145100049010b0520741002d941e032401c0c558030301c03020304165441c000d08140c01c06203912030b0441c038911888680119010042c01c0c00d103040c0100008515009040d14049540980090078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 360594154 1250 360592904 360592951
    0x306030b012601051302040e190c140d0b0604091103030310090506030d08010e0a09150506090f06090c071a071125170a0b0117010f0b090705070812 65
    0x42500e00801c04001380f02c945803a01601640404c0d0b010001c0c011a221100301606910170710030013080c022411101d88101c0c6003402c1c14410003419102d003890900c110490750f003035810441c8400c0646a008410001ca54841d401880010113450030705582041c3c039801c1c3c5003e9a0790030f0005500440540e6000c8039414104151a022104081d1071280300798805424400c0c099008aa06030440d201902e29401c99641d049240c0003800c44454001d0031031044c0041034216413500c0d40f125000d001d0950742d0b40c9160b80c5103101000182c0b4283e5a40760f00c801160005060301c4151070003400302e2445a0080311100d03c8071058074201c020251902d0000c55100e52270300404840812042001181c050b0031040c5001045440f1200000ca6004856100c802540b000c80c5041e81040f50000099004120145640c0c3d105000882000004168007040d400d0904a00322420140240c0c60407171401480f11b6100d4440c5c94065035240d0007080c00311108070042c42240ca42c1c45003040c0f00c0784609680d0b103400807a001d40090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 360595404 1250 360594154 360594209
    0xf04020d02120f1213091e0f05040b0604090f060b060c010f0509210412021206040b0106091403070519030c14040f020301180f200403050706050a050a03020a0306030b01 74
    0x840e0311000e042031249440440042c80c085c022540300a0000400070214106400f8080c22000550368480c1080b000c11480402c650000740b141d030203a084882c0540304e100030001560140000540a910341003651008140c10f41e00c54260b4090080242e481d25110348031b800d0030341c0e03038030003c0812256903042000b1402c08180300f00e1404480b800c50580c6803d21101d03408210340a07030b004100a107040b0007909400c648403261211080c1c42158121603c91401d46005924610240503039400510050000225069400317400010b5550040c042c02c03110f8202002d100b5080301c2c1c4c0e84034240144041d440003011469510328480030b40a043c0001208840d07a409001c15a0480645030712010701c10001040801c00d810581c405d4102d99510219210312000c480801400c20403046840406070240d02081e0f0310410720040c0b084034403400642e5100c0740d0f07481e010794241c0078441758040860000c200d030940e00d501c2071b40205002542c6090000b1402c5d01c075200c225055101f6080380b8182100900e0001c3c18010001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 360596654 1250 360595404 360595423
    0xb090603010506060d18060603120e0a05011b06020d05040308040b100510110f010f0c09050411030415090501020f0a02210a0c030512070c03120c05030f04020d02120f 73
    0x14000c2c4401d052450204800c0c0c032441d40c80300c00c025078600004450010000102032140e0300034006000c600e4503410708100000f80103030482c0100b100210800306e41c1c01c01058500c01c540d0140c40e2011403005107100b034040540c900000712200d81c1e0070091a1070507005449024001c5000e5618180189402d1401010241c00503103107000c4403404844c108040e5641407181c003420441403a00b1052880048206881c20542442d800307415424150b80109422090740301c01c8500001c1c1d0b9480e00030568070024401110020340040000c10005c0001602081c00840e00a089440348000014903094685400f42284c01c16880310389515000076410113441d5041202103111980c0410840410001c4101c0c0e40b17851003500000c0b018000c4814041c010f05000300c00f60740783d0340c080065158640c4bc004400506c08155941c08401040c18080800001c420300d2003901d842c00c40c55200d01d0b285489007811b030048000018022a405405030304c0010042e10360030176408000f964140100344040c00e92110314100140c22 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 360597904 1250 360596654 360596659
    0x1090503103903230403020c0a050603041101030903050706110405040501050306090616090e090715050c0615060c010c080105031e0303040f0201090302150c070e0903120916090b0906 80
    0x61481c126450342a0040307030b40d11221400c1c00a099540070303455a0b440b054502e4084c034603c103080108400d258002c212030742208811603d0486c110744680820000d400309079000341c041d56010440344010b5010340e01c4018074500034244181481ca00c0c4e5551002d8682040800240050100b002c100604081c0182805440e08401500d45c13407400940c201d507140c0c0300800c21000120300c030318504021401000c642e009401c02c1c0d6147c034081d150a00702c050750348226120f400b51000e90103e8200405110341e050b161014020400340201d600c03415031402c0d00d04a24000a0781c00101000b0b140441e9100344520300c0d2012640e200c440056262900f094101414000450001034020076280740100000c02102d6125500c43d4192160314814001295164156000290005116242140d41d080300c140030380700042540048506540d2540c200030700d1180260b5201c1c072541c0c810300840540030801d10009511072842401c480c01540e0580d80550302c5d13a4258080d07003080303a03142e00307090103824501111540000c05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 360599154 1250 360597904 360597971
    0x15080d032a0f0c1511040e0604020405090106120609020301090504050705090903072904081210050d08030a1514041b05040e100503010c080906130209010b090109050310 74
    0x141103001d40000000d420010030440c140003043c003001419040404100003501c0104485614900920704c0c2d980301d4080d682c0304c1c0c102a80002c4c66032400e13000b00c406a51000c0c0c80080075074039000d800d0b1004d4030b031452306462460316170030007042814580c401341d40209610302001c90b07582401c1c00c0c19818601d06400c40c60240f0300300810020811000400c40d050b499000d0700c10000341101384c2c5040c01c0812070f400c4040c5030007240d0080c070040c0546d441c00b80c68103003525424000140c83d01107000391410321620405411840342d90384480803d805102555000411400100d4240610f00b020040007100382c11040644002811038221800c09202e03011017000c0c1d07080c0742c0c4410b80c0d07150400341081c000ca01c00c940425641d07070005201c600035072158100424000d4000d008120001c40d0142c4842c6003140c51440900c115000190007040449201d212182c014240d84110b908000440205a0142d404103050045009001038551803c206019408004c42000204410101d142145e181c50156a42150004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 360600404 1250 360599154 360599231
    0xd050a091406010605030c09030a0c0801090317100b0a02010209030d050a1205011a13080604030302030a0b090f04290414010b09010609051309150c020c120c0415080d03 74
    0x2000400c03071f07030081d0028039065120703d00440007030300d071005040c401810861480400035a440e015041450b021b4404c1c1c80380d0040d54080d00402d030210008507400d0b48441a24001080140f0b00c0038003c045840e018400546041c5c0403c0100e40340201280700f11000840004080c6a0b880d440f4a000d400000039900a1203507524200c5510030802d502e0400b02d10400e4005508401525403007010802411080150361042c038003170802400075001220f22803081420601341c2c006510b0042c0055118182c3e55001c0007040e126910344010004011044006401e10400f5500721b001e07012107140c1c400c40c480d40c002c000100c031030352010707096130700c01d000c101e00179003100005104407508080703640142c6006a42c0d00466a0402e182040641000a40501b0403c485800d83c02000301a4122a01d04000360b001c8406142290701070040002e000014207001da000030a11114502d0700f50001d02010281101d0741003016159843d00d03041c642281c20020100381d60309000300c000f1008407000c20045030202c509841c0c509 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 360601654 1250 360600404 360600407
    0xe0406050901030b2a07060c090302090a1a030304140406091b08070509120c09220807050a1e0506010506030403091721090901090204050a17030d050a0914060106 71
    0x901800010308100e002030000e551501c0d000280c100f280c10341d589014864690b010004110717030107102c0551f00541080c860100d00c40c018883c090440b58040d218454559075190a040104440480020340104130281c0c0c20a82d903040026001070b00e030555441003000c801c00d00b003000300da51a91264001e1803c003407103c10440040d000d45071005045007000012079640540840310b6214040c203842e8003142e00300382c0389201c2d04009201c081c205401e03140c01c5040d031101000070702c00d00036a01442c141009030030000740000320791300043c00f08a44200c045803c41203280c3d9400b03240c894038548040507090b010f00c400c81400410018240142410b0b20401e203507062070b4500420f04036040c0500d00041070340c6481c424000c14200040329003c4103030304428042d03a0101d001c401581c0d014000251064258200101c0e8844403842220200c49008000d14059460036102078043c000b800f000701c0b251301041c04441014a0709011312881031882d41c00000c4c807081c96142041003c1004801200c140e4001001844002d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 360602904 1250 360601654 360601669
    0x108010c0509060c1c0905090f1b071e030804022706010e2107080c040b060a0804031704051005070f0801090e070305120c250b09040605031902010e040605 68
    0x814292802d9a851113950074035482c00603405d006180040b07004610054030b581c4a40038105503041150b0450b51511445010b00e8881c2040d1400782504984040362500b03002190010110b4510455600b98003a41511100300d490b440c854064010590140030401189004043c1d110048049044081102410241c0c940503003802407219050126a40309111560765000f80300f00102510b810011096002c0c0c6c1d4410b032600c0385482003036814400c9101c0304001e0314060094500e43c00003e0a450b0a1807103080003140c1c0c061001e0000c1e418001e0f01b4010400c0350349509003252107540940001d00d41080324046e40340880e440140038100300581017149000350341e0f02241c801d0444e8080400400c03014000000750781400d0450344000c0813445554041c1c0705240c3c0d00b5000d4028954044241d801440703021009500100808070b58914110790510207016000c2e103031000d8026401c1c0904000394103616000440d2401c94810400c1c3e07210007104110b40304569002200c0e2401c002c0a0324140046882c1c4800708256 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 360604154 1250 360602904 360602917
    0x1a1501090b0f090f0d0f050106083c0303130507060e0904060906060915150503060a090c02010b221104080c040f0908070c361802060a02030901080108010c05 69
    0xe000d0005090041c0d5540d030002c083c41c0c00c1008004401d844181e10344441b26070586107040b501c0c4c0d4200500001c411a020bd8500c40480c3c6541c00308450320740f2a00760064080c80c44900b0b980c036000320120030071024002c0010350710500d00038609074620710302800c00c146080038035440517041102c0e950704d0440703a441d0454200d400c00e038072542c0403403030450038a0114003030701d604d4102c21009440c2484400c0c003035044007215012210f11079040181e184209000711001d04c01219241d8000c45517a40810070035170181c0c0031014600d0030b4800003500c8405031000800492a054207072007600f902c440d1845a42020380320b05c0100c507001c0f1104c586014600f0b0401520751100d54010380c800e503030742c40c030020034400c0300c0d00801900340c1e03c102800c0c1e482d84689030001c2c030b04149028410a5100300c80107a00c40c404c1e0038081940490131000e0300740402c06400e29500291810040601c48203d24224050050302d44001821850a1980140d42c1b07418101000400c413400c164000301041e03040080c980a1640c114003152203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 360605404 1250 360604154 360604177
    0x4061202131217030a020714030306030a0b0a0605030303070507050115141e0a0806070801080f0a021509040e060a151802090604030507300b16020a1a1501090b 70
    0x10310090341092180c19403510b0f080c15001030000304001c1054800c0d80102143d82c40b418460802032041e004496580c081100c0039078150b4016441403000c6032000d0301c160791044013210040781d083e0f1144082419504203850060104201207032010410200780520354080b20001c915615041c58a1000c990b0609454200b601861399900700f00f00c0d100e1603402454000602401d01001c250340c9007100b55451404454075000034081000110748600041854092401a14001d0a0101c215020440b40c50f903501800e4040c11420400407a287e11180100000781100f58050000d914040c07281d24241c1e88081c405100b008464441484069203d05000d0601061034400586a408000104100380b1541d003000c0c0841c446c0c070070b001411030300c01c2035030a05d11042034035000c2441801844500c0190307041c44d4001c1500e030403400015002c1c0e6460b000028039020910403111001d00e00d880382da600c1c402000c134030320860900404204503080c1c4010140940c0000f840d040299525259003e2094004d18a1851 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 360606654 1250 360605404 360605429
    0x10b0109030b100f0b040512030310150e0d0c06031d030409020d18050604023f34060c1a09030d0c02012009010e01110f010603080406120213 62
    0x150041c3c21950000050202c05a500300441d4403100e1417401a00240700d018411746403056414000840401a07034041c4882d510b041c1101800d0034a102050203015050404126010401400c555501949003004a01840c0c03200c1e051414000014151041c07034202040d050b0859440107602c101c0042201c04a8140f2680107880707254405855000d000c46000346204004904114401d024000c180c0e54041d030701c221100711440055024040c41c0c50114910a4618000c2051103404100c400401c4038101c408402611000e45841c290111401d640605940c1401c0401103d22802580c05030b688000d45520b00308261501c030346541d9100790070412030846d11484100c802007038000c0000c10a40e6503490402d9014040c0c44801c0034000d008141960342095254501c203070310301c0c080b10498129004104181c0d2000a034002d40c100644662f120109505800d104109010000d483c00307108140c0614401c4440d1a074852810030004c22000c8001060b0310700501c10810044511904507244007260340080894 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 360607904 1250 360606654 360606661
    0x901020d0309140f0d030b091005010f03060b04081e0f030717071505060906180105270f04150c090e1801050a050709080a05070303030e0f01090b100503010b0109030b 73
    0x501440302512043c0818030984441c2e038401e84d40480c003441171110b176950421090390414100301d005a802d0fa140c1c60400c000c240140314039442886401c80d000c15500f00450501c6d0381d8003e01000b64055407250340c0e2500a207080c40444906400c0700350440300d0650040c03a8410140c81242c2e10b074810504014224540403a000c504042200300b6254070340d800c00c039540e0000702041d0940d80608001c0700c009103d000414000707452481c00c10401a4a0880442c4070340080c1e0804061004201c02003a03410450360384d00c0c004001808a612816101e00c0550031007030220308203843c00d0080b400151007810180c0d030415000c112900d5201d1b0000741114400f568a15880c0c0381c25654580c01c1c0c0140c0c1180180b9420801040b15460807a00064015119030741d84600c0c1030340c0c9403122521030b04003007002442ca800407101080841d00c250002d904040f0403005452403072081410035421554000f000300c4117080711404110203103104209080050009074004d01c004102c0a000900c02036660100819002070b00c00032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 360609154 1250 360607904 360607913
    0x10c081204141204150f020d0806030a0609080901031d0a0b15040f06031101090303020c1912030f081509131e08031602030c030406110a0b0f0a060503030901020d0309 73
    0x82c1c0c00c1804415007500c100c0c032407040c0b0100140d4840c3c00ba402800c41200c4c032007000c1c00d1058210345107403001c41d13003c2c0a00c0d00c000d1100703d8030f03441c02170100c41e410700c82c903108400813840a1003002c081364415411180e40c0d612940016050f80c01d1395001c59004e01003208074050444001c90080f0801e580550740c81d85c03d80e0b03120110b1361030660200d10141c0243c80c1204800100c1c185610880589000303000120724001c0110046548407010301000780140c00c600818400c0c0d082c81c0c040c40d485007041003400c1c0001c5407101e5007242e0b04d08a2000940c0002d907031901c00000f8a4105200070b17000500405a81280e016074800b00343e00304c002170000341e90324480b0440340742409610b411292150fa115400c4440304c07403c5003020805a0425500220b1846a0a14044100380008101e40c030311001d41c4041d41c105441c0030000e5480360350b81c91504060340a8000b48000150800450b00d100c1d488280309031206040c45840c180c00c5038140c2d0030031802139004103e4044180c0c4c000440440d146114680859502c8070b6281 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 360610404 1250 360609154 360609173
    0x2109020301090c0816081b040b0a05040e1006090204060801060810090501090204080c0603040209010b03090106030804090218040b01021e0a0501020403030203071202070311010c111518010c081204 86
    0x4001c0c01c030340d40b07000020400480101c0d80b0001c580004901c080b0b19600c031b0100b503032038a5400c14500b00c3d010a401300c990301801e0076040b01c1e031010002064800f10941c0c80300402e0550304040d0345081907410152982040d41210720854002d004003e000b18101405c0400140c4140d0044c020076050000420003e90a8250204000d001c1c2255203401d000c956550a80700c80650014041c1c49118002d8140300c085605200c02981d02c242e4000b0710701d00e401d07440c0088040d8a80d001508200c4103540300c501c0030002c80c0d59800207000a05c865180181da9400021419481442e043d80c060300c514140b90741c21086aa0000d000130040006d00b40d9107000340b00d40c4007510702d8841c1c20f07880101507500100c0c000040c140c02002815519000341000c041074001c03500d01301c1e100c40b01030200038424501515810042d5100700d860140052148407aa0b005000b5400040d203845825940c600418a00180c4203640c50182d2955040c51082070a0840500100d41d40765543d0340a2041481804000480028148480200c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 360611510 1106 360610404 360610421
    0x9131806060e071d1c052b1403090d030507030e120706060522230f010303112a0a05060403030c0b0c0f1911030a02010501030c062109020301 62
    0x3901402074100760301c00e8900340b0403007d251450100c2002095100601c9070f5590140c90099000200b040c600e250304030301c1090042c020301c034265000240000480400d4140450980e443c40012401404601c400148505c258020a200070240744001d000f4a40102e000344101515a014403a480c4500303401030001e00902d00509580485683c800c0f80300084404031440e1030344102c000d010840405440c042110031030600100101908040ba01d5200e040c49000340011881e9902c20220322080345010000069203507001c08541d40e10206c058010b041c00034011074403642c903418000d02e5200f60b50b504030340400c41180403a02160070001501c80303032510301c0c0c0c0c5035281081c900380176401c21550b01c103454180494042c8002e8000e00c1400906400780c0d039640001810740c55404c1c42090901c040d4000030510401286100080032034a90f40d40c064030081d41c0c003042541c070781c1c400300c0e00401444 = true := by decide +kernel

theorem cover : BRFrame.Cov 360431654 360611510 := by
  have h0 := BRFrame.cov_init 360431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 360431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 360431654 ≤ n) (h2 : n < 360611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
