-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1298
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:14:41.292207+00:00
-- url     : https://prove2.me/submissions/2989fba0-55d3-497e-ad44-75091d7a8124

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 233273381 ≤ n < 233453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 233274631 1250 233273381 233273389
    0x14030f0a050c0d0309090c03050108060a0b010c1202030c1f14240a05040207081305040c0912110a03060207050d1d041a150a0f020703020d0303020d0f020d0204030c09021305 76
    0x50800e01c2460585d598941c0c1d8082d8500784d8000612040200b81c942006201d410010840707942d1010400c00148241000c03000060490030050002810b140c03004100c005601d40200b08980661801800316500052510815814050398200c000d4200b428640c1000c4440601ea07078460043c17081c4880130030030140302681c81c510407480d66046038001c05658000500c5548510261820b2030003607140d107039100c1a0802100030707031201e41c003c10300c1645000c904980710340d442010801030700d2804450418024548c205140e81081d0702032020f52026402c500842000f0603038001d40700f003a100e041103807004610103205443c00c020f035035011141c8401e2443c5064141c1b40030741000c0c600000d4046100d003452107000100721030301c0c0030144004502d4400107050311541c1c2d01800200100364580f0141c880b0a0441e80012200f511103070740501010b07004103001001e20b455a202c00c10b40b080d0750b10115a51001400000c0103900a40b00079101d02048402c0042c43c0b404034021940925001c1a103401c1c4141060204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 233275881 1250 233274631 233274649
    0x70f0806090c0423090a060e09030a020c01110a0b070c021215060d0204020c01060f0e010611060406092102010606110c10050c0703060504060b1f020c010e0d05060114030f0a050c 78
    0x115182c01a202459900e032600c00405014281c155001b00c0d0423803d01c84200b03900c00c0081c01d0481b4940c01001f9450a955002c2164059190709203003211030b5a01801240e0302e4501030381c802411b0142404140980680c000900a00540c42600c60090407101c91403125120350b0b5007405000103514160005130300e403030700441810609200900040c240300381000d8050851305150000340c0c004c149044148407401056100300c0c014403052a21090f101c406411284d120b48001c1d200402450301c5801820822201c0840e41280e415000002620080c9103a0000d000c0d186521404010500049042c000494003040d051465080541620030703240700000111015400602d140020b03000e000d10110008005000d41c0340543c0c014200821501285410801c0003092181d2a01c3c1c070b10b0b583c07248a260940c0100d13105140c0d0b07509003401400c140c90300001ca05401c80f8040010841d001d0080045103201c5141e59030200c0510607000c840b0039005985140d42e0380c42d080701e0007601c1c0750f001e917541c001203181003408 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 233277131 1250 233275881 233275919
    0xc011403091615140301060212090a080d0c033c0e0904050a060b0a030f02120f030a020102070605060f15030604090c080a031d0d0f02060909070f0806090c04 69
    0x100d4042c040b40740c103411200c0425402c9080040290701d40140b080e0b03031203a042d9911568048045196514140b806551340c041004035541d109804601d80070301d60344103000f0741c00820001080e81d021814040004150855102c0c085002c05c01c0241d9180040008090080303c1c180c8800584080241e00c060011a1030748443c110001c100d43d441080502c2e4036002d44481c080e42c8540c00a007031001c450314024007640c4200030054050354034908100041100c03d46400003c1e80c06580306074070714a2010103d410300d8006000380d140c0e4400061070034a4140e0560040410714060031003003080f03484001c01c20804134055080c80e0740c400e40520380311134070f00c0c113040045411103001800028110700c1740d642c1507015880ca07841050b0a410004400c014960800d01901c00100001c100c0c8010886000005900d40703a465409408405100100011901c40c4001c8903a5524000c02c45d400780d140408000340260304c09501a00010312140211305141809003155001e00380c0323285030500b040d0504070019020140054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 233278381 1250 233277131 233277133
    0xe0910020f130906120221010c0503180d051b0723031b03061602070e0f01061b081c14040506071d01080f0c0d0e1b010504050f04180b0f06040e0c01140309 68
    0x78402d007e01000b445020b09030800b03500c07801e44a250138950115040300030001c28a00703400c00120100c83c0fa03881011100a210441c0150709a803920519462414649400140000c2402401e0b100000e00400b24240750290840c1110360040755001303226162051110081e4060b408031010420100c0e0021892000302c14034030445191564070043c9d0802504181d4031040749a1502d001400602e40c01802040107846e259100c03c101039481d0740e00368070392103800640181e00b806400d5503200f860790350300094001d801040741e06001c0d081604220b0b8030307187c098800801183c504d10410568004080c0c0d12001140d0584a8656550b9100e0b1481003042009006280d001c1c0100240070405200d84690b80c3c0112048001b0098081d1048204041d4040d450b165810302c00d081c001000b4030b694034a0304030784440050341d000c200300902c83c800c0c0300e40011a09004041084200c20171440303150350031459100c0e49044805004502036000c8481d145c590310500580040d00d40d0314203c0b40e8000b85001981c02c00701e0340d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 233279631 1250 233278381 233278429
    0x302150705010203012301030515060d02090402190329040507030e030a1211040506030103060b210102031b0304080a0e120106030f050c0402030702070e0910020f1309061202 76
    0x1a07245401c90340709800c8451135920126a842e0303c100c00502e0480c070b80700c0c20b086c1000103042083c40074010a0150303224074400c0200003050034820340c01d0780595004040141083d51030b01c85c0c040303c215110b051080b2542c0000e1801c222505c0e01c900f27510510611206007900381207040300c0b80080c00b01400e001020a414141c45840c110042c690410003007041c0502c90b5230b468004510404040180d540100c410118103130140400e12196403010102da0440b6840b050001d42044440c000c200340c95041e0000343c461000745000046a094190011441400845209100019459411100c0f404141c4015058034824811404158095001110726100041c0388000d1820048906400d4641030780003161408003504007001081401c0003102002c08040f20190b085280818000707589040074070031406005810404251400c0003131041c0084402c85e50b0781990707500c0b0182000161340d0b104207001c003440d560781c85e00055030941c0d0740300b8641600e11640070b448042120346c00b00f0004828440e0344688604e030318 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 233280881 1250 233279631 233279633
    0x510030906200d0f06050303120a14090304031203060609060516021302120109020336061501080a06080607030f0204180902101806052101080705100c0203030403021507 74
    0x4190607403000e01c050303020070707a6658010383c14400d481102001c0071025040072024801e03a640801915280c80c520424a5072aa5604481d200035044035002e006100c10168144602a0808030051055a0240d509404503e500443c11021603041c0d00c034070400282c3e2000c003800080c1c03041000b00078021454801c030a02814540007c0c480d1700216140c03800c07040d03000a0303010301d204880080341d005207415001103040d4a000000c3c48410103111540b031200003969900080c03442c11a01e0002203c1c4034200440ea00c0d40303044155107000310030985130700d03001c0b6020710300180f403403049402144181c501c01c001400181c0c031461b030b09801030603000f40c0090301140c09110101d2151100d0b1000c0c807100c09403e4001c288400c96006002640c1c0a0880b80d80030030551400c07001c3c034071070524003503001c84a4031300d071065880300b07410308440701c1250032118003800845e402c1c00042c55000018008094034012960701c0d5540d0008402900e0310400442c00035010b4005000c00c00140c80c200f000c1f100c20b8074a601741d4510302899 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 233282131 1250 233280881 233280911
    0x503040b090312011e14061801050f0d020306010912170a0c050a0b0a0501060813030c030c020415080706092607030209040b0403090e0c030a0b040b0d08041d010510030906 75
    0x241c100040b24422071448402d00c6405ca91150014044a588600c0e505200c81c04207489200f41000350600a00426400c0200d9110340e08840d00c2116444003c0c1d1240c1403154010301135032041e540c150000e041d007400480d0300c01c01101130720300c40c40d8460740c204101d018800c1070022a8003c420300070180049094081c2c0418828800520224030402840c900e40c0703040141c0008688060300002d0030440240708101c0d0445140c0700d1407150540600741000c4005003850100ca6102c44034100030340080c14450544242035174002c5090550741d104054412854884e4011180507006204008041e225800d441d0702000c02c41e414818046808001c0e0b40800c1d88035004074114100564003240c001e50808104002e25620a00d0040507000c0380c00c5606144c20444030303500036400060131081105546450141180e500d560158111500103015030108810900340289560414407543c4d050311640754100840c410070398143c074169000203101c02c12000090100310300902c1b5603070003203e60703e94980c0301500c9945 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 233283381 1250 233282131 233282167
    0xf0c0b0414100e01050c03040213050402031609091419020f1201020a0f02010b06040e0c090118060903050f06060a15050d0615030c020609070603020c0c090a02070b0907060503040b0903 81
    0x2c2c0c4644003007194112280c1441c01c40d0802061400600c80500c1807100592368155110359040100e9808521603d45000190a20110b40c841811a03880c41d40005080141c507040340411303a00a901b000894940d07112695200c3c03c00b04401c08a80184444407001407814610944203418098441d038250041c0d140340da0700b20707485840c031003020800315840c40300b906909004041c40541e040e1141c034289131800318400010b100c060300c0c40c00001c2c00451826200d910954562100c40814042c03141d4240d512100a400c07680d8074001621075010b0100c8210107120009250360040d10058030b414180303072501601c92096444a1030000420100700061000c64003140504000f800c0d000001450f165141c10b00581141e20107500d09007036400c04803c10400c1c0307070041044412900207007030145c0c0e0744004018003030a00001100703040d801a0342d14184402070689501400c4818407a020182c0c01d91100002075503100014410700002640030800680000c020388502e0790040c4116003168100500c240750150701403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 233284631 1250 233283381 233283403
    0x90309091e020c072d090203090102160309051503060f100c06020301090c200d050a050904060f0905090604081c09050d080f0a0b0f190302030601031505070f0c0b0414 73
    0x60b000c1d070810700405200004000100c6252a840d400d04005c07040440e00214852080282e41503011002405414083d0100c40c003204464904842da0035031403501400c404590700659000303400005001c04036030000c8003180d0103501c00038001c1c546d1107035420402039441007030103064040140341c0200800050850028501800045401140c204403486005201510350705008103400e40c0781d034902c00e041c0b01c00302c0c600c1e03441012854841c1d81c810101c0c03801e0f6203d00ca4a0103040c0c00510300600020194a07a92200c4c041d82c4042c1401d01940e01c9a8400300e9445901390340290101208015000603c5d50307070424801072410b51030001c5a0f00ca016191142856003072007603040819451020003101c0007040041c9079115034400420010151402e020501c0300c000a036109024001900c40070716220003800030500255802400c403502c640c0c40746000c0b080f180000504078071003420030010807801c5000e60f80990190542c0d954840310520107480d18012881b016006549100e01c14029a40324202406640056 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 233285881 1250 233284631 233284633
    0xb0f0903190809100c020612040813060908061810020306150f030f0603160b09040e07061206050117040201030510090501090c020f0d0c02092809030210090309091e020c 74
    0x50f510610a2111140060b1411000c000300e480c615001a680c0d8003c0d50242407100000c25031a540b64034295229200740c680d096062400c820000800a5001300e1150994030440c040e03d00f1500e5211315100c41101085080c0401d0300312120349540740e55580d000d1f6a01910080c1100e0400d1407807184c1c42c11a83c048640d402d140040002005843c00b080c0c169990815420740082020468a40442410640398005c14080c04000034a403003003560746800101449180000b59402e40e41e8031800500038821803410035030003d041400c0003500c1c1d800356000314040b1000e044a134400f40c1e5603070b00440061200400c3c0000d20b402c49103022655203410b00c0f44501a03e07020100003801030000d240030380340510781e91100029503c0304000481650748103504199071030b03055039510b8480e2075151800b900680015203005845440a00c80b040d030a41c0c903001945000d02039029510115180745801041d01c01004025020900201080081110b203502038221a84d50b10b22a05100c0104d502c140e0aa070b0040e0105052 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 233287131 1250 233285881 233285887
    0x50702010f08090303220212060603070b120105100c170a1101020313110109091b090816170c2106340e0d030c060e03040b0f09031908 59
    0x11941c0041284004540c1418105007074500b0040351a5a480000c0040c1d194118401c1084000d41c0d06101c45040180d00510914200a483d0b02d02590b450701101c0962103449000e2002030204000d1088a031011030280d2502c2090f0700384000e011803068110120410400d03107010720300200c4d4508410340117a03055943d03102d075141a4210000c0c5a4110380c0520802a4410400e1000100e0320002403802240d000b100360b040e41403c40016a841c0c0304a901c8001d5890905418018481c401002542030344941e03181c400501b91640f951654420405402c0d40996207a2602427140c618600200c0c00b1466002003160420100d1201088805d40702810b001607003201d81148004030b080501000f507000c0c4116400c2e102032026101031301c0304400e80840c01041205030038840c400461044500384000b4a004c0c004090001f01490300800d98585007000b41d0705586080d088034420680401110110b600c0c00100c9810042c00009441c5282e0014001076450f10940c112143c03e140c1c2440c00446043c012544161 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 233288381 1250 233287131 233287133
    0x115170a0f0605060903100506040905030a050301080d0903030e010c0510110d060e0705030705071e0807060e0142180507210510031b030c050d0803070f0306030f030507 74
    0x1040e50010382085100320805e00c40321070591400940d070004520543c0b00801c030b035281d031000b00d0020b1041250151080c0400075120080c20f4104009504072003041d0701700d0340030b5012040100c81c0751400c1c0c000180054030a002c50b0794103620a0f290220741c1d5014006a4000140c98040c0b24101c0d04610080c0f9060301d0003065800d49203810b0304c140f10061102424407103040c070300034038001c1c96484000c002da018050301054103410701c6460941c000c0035a800d400741500c8503000b800c0080081e0405202200c0c0582032000c924141c034018010a010b099100c0d0807481c005441940030751a00c0d44090f0390040301400d62030248100745244040c14000c2c12072440d4445901d00040f648410380300010058070a000302031001c044607581251030308040308185c40002400340c8544402c4800c0810941c009042110803100c0300080c4450401e0400403a4816200c10321455039030814048103055609004d40081021300001d41501c2c0907070540d2500381005c0c030f0f00243c0d141e141d0792085081129842c00b500045c1020503500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 233289631 1250 233288381 233288411
    0xb030322120302061602330604060b03010b07050a0f12091e210f030e0a05091501030b0a030b01060201140a020c101112041506120b0115170a 62
    0x140503040703100c890340c00400103440103595840c001c0d006080800e10000d920010078402d00560078048203c001455844505403040d4a0000095100c81c0060520034081000303880d0511840c8105c034001071001c0d0860b8a0324012584a400c00c41e815282d5000324003050b00007901440b00c851185214481400f070401d12010000c0404519400c8150704482e403076003c00c13202c41c262029a0456504d1032180056100c80c1301c40c4034000142c0500140490321321071800080542104e03011101034410b0315010340c119642c07070400800c46000d880e035511128111401e024503500c41d400c00845028040c01002285560381c1d03924807607100c240d004a0042c0d40d10440700081024000c0000e4010301002800e60400d40d46a51280e142c40d02c1a170402e0a042e5641c25803035940d030240003925071110300720403280e400c2c0c074003404c066540e005810740f522141403400c500410b10520406084003280e40220103048241e0030b0001c00000b0150101c02c850601c140c1d210007509402803a0b00031841458060030124a0542c000406 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 233290881 1250 233289631 233289697
    0x9010203040b1008060c070c0305031b0c030c0109090203060303041d060f0f01120c02010b0415080c0d08040b0f04050402030a020c0114090d03021e0406080f0a0b090601030b040b0303 80
    0x74035072440c0e0401c0804c290f00703000a41c0c640013840c20203070980d5585c1619258030340d0241688000d100d4000841c0034400c0301041c00c0000b11860154090394a0f400c10081050784842c00d910216001c1a50220140304014403a409964010005021a4640f80d100c280300080c03101c4148110007189600700c1080307814101001032440294090f01c1e00c00c0c1f5060b03040d00123080d91038000c500c07480e665514026602c1641c401d4101c040205800781041001c20440c0a401400e03280c40e001d070300c0b40381c4510034400d074050500180007803080340c000c0c441b64201390406501061a0380000c00c1c40744400c10a21002ca11940c0b0b62000318064411010010b0b5207000c428903950030f480c0100f890b800aa105041040300460340400d07101c035600386620b001030ba601003080554034000d103c001045175141010078081000303500401e04c14040d072100b034410a05d503680c0d60f00c03440641b130418003003a0300005004041482d0354080c2c3c01c400d04801d00140003103420440400481c0c59034020104a00312100301e001d050b00621002e040c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 233292131 1250 233290881 233290891
    0xc0a03151d102102100201091212050f0f0c1804020f07062913060f12051b03030703050304020d240e03030402030a12020a050706030501150e090f071709010203040b 72
    0x4115411810b031805916480c950950207800b41440c1c00a10171428801e42c0190440d40e880f001d0756810340c40010b0000d09180e0070780014041c03e49841d000c07808036840903240c14440c00c03103c0d0726884281d503001d06901c50b68012000c44402440f14070170410940c1d40d82c2c0090942c455003115615101c540d54180384058800303060b1a80700000c41d0010b11602411150b12018a040c001c2d14250ba41d125121352160081c9859440899406400f01010820382c501d88a08070f4020b000d14101d618100c40006009419828403140d1503165104201d0a80068002c0e0050341d80580014050b0b0000d142d81e8456107030380311401e41d021043c142a40c07548202104940304501e41c0e00340c0c00005604501d030550100b540d80c00c0c074400242c139080007000101d460718420412041482e03409400d41d0000b0f5625280507016041c00c0c095644440303c0e000256030014414840880a640000c056010b0360b1104201c0150001001e0580004c0080307281c0c840007880f12120440380038030855000160769190508140000f0f50010345 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 233293381 1250 233292131 233292149
    0x10608010c1b0309060e030a0204111209151b041707080d0309030c0b0c07080c030903060606120f220506010f0e010308040603050a18060912080c0a03151d10 69
    0x112107003c00d078450a07030703020746900382080d080c4c64800d0000a450a801080029031060406604000d0131500d08081c010400d00c0a20003010741d01c41c0704903943c07100c0d5a403d0518810b0400c0e400200741401c11103078885d1024106101a140541310f40b500381080c1c120700e00c5500c03c0d5003c0407013080b01502c01c0005001c00760079403504111008556800500040c0c011001810640001c0081440702618904968100d5405101c00f03a840100340c031030303e4a9401181d101e0348640030b03c40003e0001e05080e07003180c81100f001034641d80150f0b160300805c4d2203807a0150944c0d4803c0f0310361207140d0035104452080c0c2c2c541c41c000c100070100c540c50100080700144485d000f01c1058003040c001003002030b03031981c00d8400351541810085056035448900300300414050107162404d04801141d0414018298044121107000c0c01484a0100260400792000c05040c3ca903112800410004208100c0c860790201001c200f0001c010b422043d0387d43d110680100722407920610540141d000c1c020f421320140700303c20003015104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 233294631 1250 233293381 233293427
    0xe0312010f0b04050d08040b270405010e06041802100c06060b0f250206070606091b0807230301030605310609030e10020c100905090411030f010608010c 67
    0x8030040b60079025510600d80589800c0390b00204018a4a081c2c90282180050042c2c8404020a1051342550540d510403446c0803502219501802c2900034a8144d454080301b880e0a078845600713010081c400c02044540754004c3c2d00401005a48004280c54402055a100340003d400d03410036034100d440950010f100502c0070004d07005000c50600550301400300c0100100e611416000300006c00c2c40e0b0000009600900000e450020055243c0c444829210400380400051603040218102503001e254000301140e410400102802d101c0c503200d8246119100351072814100300c12110a658001781c100b250381c20349a03800c100c03a142d54440c045400e071040d1003009184890248020482c08110711000d040e09848119003002e0500031482e0a007800c038060848200030928032402510750803500c0c0300d24130030640c9501200266104081c00f10940d54010709503003580e29103655044000701848612600741c0110640b01d80d0a40d001c1c441c0c0304c01040194004100700b4580c038001414803c00311040f0552a2080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 233295881 1250 233294631 233294639
    0xd0501092a0e04050d110313030510060902092d0402190315060507330510060504050a090e010905031801180b090108100b0f18040902131104090e0312010f 68
    0x103034001c44000705080074150346d94542e0f0030030300790700c900c6c0c1e1075005a60518400004000c400100380c000414080070800240c0d0721890000700360b12a061180e5806070b125000d510b01102d00030f00d9a01408a00000c4500701c541030310204040c2d030003030903081c125480c0340c1c00491503203034040c0101c40a010000010200c080d08003413018010380503030000030303216594014801d04204120000c403548201c44161415010500480c20006001d00300d40407403a400b0701c0d4900044503030050007950280d440c0201f4102d040350400d030b001c00003001e104114010310340d00d0b102c0c1710001c079005100a04100c2d02c0041151081e65001c0005014503406210a160303285c041d5604211100800059030860310702446c2c5001d0a44600c0b08245440c0c0315a04030340c040a0001488026441c1c00700d0040c495140425003403549000c482c4100400c40f000140080d412429200541c12400728560000c0e1010b510400781505146c1c030b40503004c040f1070700c42a1800c2c10368000a1468841614a40342600512901c4440c0000d5414 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 233297131 1250 233295881 233295883
    0x120204091a0a0518070509010309080c0d0e0a1d100b0705030a081e01030308070c02041b0311040f0513150312021009020a051302040317030106120b030a020d0501092a0e0405 76
    0x4c000c00c02000c02a01040c0c40032903030300c6038004c10301d00c5070400001c0d51a2405111055199000071200300f010502c44a10312189041c842a40c0c002c4500920b5180035100300000b000540c00e070028040b0540d40741542c80460b03100402c2010b0040c0d103009a004603140d08a080005e40301d4131010f44003641e500c1e05204245070f601088980d503815039605142000146d102c0d6030060383c4118001c0c9000754070909050030b00c0f00d212a01440d200300d4000f83c0d5014015091400e83d0079015104034003d080e1100f100250030b016030f04001c4000c4c04200000741e80010000054119844100c0f482c4e00100c0f680b10b001203459400f40d034100074203004d140c0801000c0001d100964009040c640707143c420b842c016500c0c02c400a603032a0590307064400441e00950180c14100e00591244120350090003070501051000c510420101481e00c24468201c101400411045146030200076400c0b03d0103104548a64a80d4412000a413800c0f400003489041443c5072a402d001711700404900040c5908000c0d1020385502c00c00010880c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 233298381 1250 233297131 233297179
    0x1e0c0f060706020904110c010b01180303030c020a14010209010905221a0628020d0504290d05010f09020c0705040f0e07120204110901020c01120204091a0a05 69
    0x6412145141d45584501d40303030020340100755400b0742c014640010b20040c070801200520045050784003c000c0c10411000554092180c0c8181c240b610440c08410f10009019500281c00ca803840d0040741c07070440385651000145807c800a11003a41d401040d84080341d40c00c2245000540300407174031103d0303071003080d04212043d54a00882169460300c1c1c1000700310840d03400e142380b014041c1c00b8108565981c980240107030386000d900f40d6610940c40c10305e00c5244c3d90f44081094a00340280c0c0d92003500d0700303103002034441084500c4c00c01005240f01120000c080f000d40e03800203203000f03e50a0000304440d8035009468160a510b41e215506650041000c8016400b0109150090391021100001e40f01644100742c401040c1e5a8480c1d1114450401c0c00300340e041d1100310201280b4421101030062543d200e0703007070100d0301601400d280980d02038003441020798060307101000740c000050701c01800d05989410900541d8020b010300720005a1085406555041c8841920003400c402d44040010b40507030300c5503034a040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 233299631 1250 233298381 233298409
    0x20a050f0a0c05040e1b01030605120703050c010c0312051902030403021507050a0e060318011805010b0a120f1401020d020405010207300501060e01031103010e0d080a09060e0304081e0c 81
    0x14400ca64866607588c001c4e4014070103058064456000002c5044410340e40d0140c40c081507466218001c0d80c860b0700d42c0700b00022000d240d0304d540e80a620011034071103c0c0280038003400303015007000b214070320707145289007880036512503402a80205a45449013614604a6801600d003000304001002101400307500022661321050f019120705550369217072100340050104603919404a5400e1503d000030010039407207000e0442d070249008000000c1c0050800619a20345e10416003045045060f100c0415860301c00d40d031440c0e02660500c0382e4688101001c90032a44a091041c011a41c04101442254bd0400410015168058100f013401c0f032103030b0010103032041c1c40819491040e00f074600007040040a41203000100f001141105076561a0320b406c11130a1826225580258038240c05000f9441000a807081d15130b5003522800441d807102140e403000382030045400c0d1000d0742c0f034010042c0b0f80001003004100411014002d000c00f0010b1202500908025400030b181e990300501c0c030411103a8603c6a00c000300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 233300881 1250 233299631 233299663
    0x12060405031804020f070c0618080c01030905242d0a0504051204090605120115050114071b05121216020406230907030e060610020a050f0a0c05040e 65
    0x5040901c001802911034060906170000010803040e003004002e0f2030a80030b40b00c16841e0070059045139440b1004401e028402d80b859680900308807021540254400c02905004000303803000550000914107005024000741c18001a2100c10498148912840b10310a00c0c4001000320300e50341520032402081c90041c01941c411740d41ca0012408000302044048041d03031148803280d403038599850081004001c03038070070706015481000714800c4544061044203468403814841c244880d0a0400440d0750700c0300400900c01c0300d80100160004280181400800f40c0440d001c251503060911060200c140590b00040b6180d51150300e520203162108400c0d51300098061400001d507810900005010b03000950000c1c1400003811081c4000198844d001003107642c0c1501d0360b505035201c0e114103c0c112280c12444541f030380c014001040c483e1508241c0c410951586104560940c41c00f03485440c00c01252018101e1107a00c03881685041040780000700300140070403a0100180d00ca903c09084d01d0f000400220151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 233302131 1250 233300881 233300917
    0x50907030b01030606060e0f1c0c050a08010911010201020c210403060509160b0903210702090c0a0e010f05041511060106030915050c0403080c03040b0304030e1206040503 75
    0x404504004890040d500150001c241d56920f0401c44000c2c02c95000d118000340f070403001090f90741040e03c0003d205403006001000024402202000c15102400341141c0850035100c0009060390b4103003c0c0c90142c4a03840000540160620f464052481a120b4082c10340e4018010401c010780045402c08520030034001404946206100d44003940c130403034000800861a150620000701c1000694613a402d20203181440015240c111041c0d06004102c905503142c0d021030b4100200700c41d0a62221140104080c8541c1400210740c00203040c444212018414a0008107131589120b81c0600703075490107442801c119481010210005150744140d0181c4801c03981c0302c007480d024a40c81740001c0800b0507441419a1080c2d615194018090019802d0680c3c44035031401c2c09000304451072090328021455031256030715161950766000d19507000000c40381c0c0c03d030006200001e0780002c00c4000394410751181e03561240442a4208201c140044c1101d1009558480700420002540000c12a02c0111100042d21700d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 233303381 1250 233302131 233302141
    0xa0611031306030e0d021b010302163509150a0e0d0803012d05010c020d0b04080712020c090406020d06080a0510110304050d0807090504050f090f0a0f0605 68
    0xc6148101642030180c1c407550080001c4265240e40440421440300d810f462080c902c8410490f5114401081c3c401d0940400e02041025030090b401400c0c203407003d01c15032228041030745032410410f08400f80c2c0350b584000c0309000c00035141d00100c4100ca004510001d141070814031000f0400c900c5404002e840001000140d4030000d0303000711050081c3c40c1c0000d2403c070000c07480345030450317841d0000e1142d09002580e0025103201000d0340700013150100389076941c20354842d00d000d004440210450304140d07046022041d03140041440d208545120700c0c0a025003650b120a02d150020340765075599440011900400074810300c503038500d110280c129400c02d602581741e196605600009203520b600801023413203000e00d891700300305001c100001c1c030904581042040681c401d013a0b10952000311341c0200190040c4c0c08401d1001d00402003150004c03c40c0c600740d0304c441e8440340030404032030054480321030541190b070400c02245401c000342e16050400202411401c1e500d6925205900880700d0700038101600c0b0300000c1c0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 233304631 1250 233303381 233303383
    0x7020108061305070e01030c032d11040608070f0c0b070809120c0c090f06090c13050d06021c11160807022e0509060403080d0f020d0c020c040b0a0611 66
    0x2c14144507041046050030203000d001c403500021103d000c06d040810303400f200e40c007a1141d43c11150168140624107044803411146000c02e00e40c0780e00107c0e580b041d2072001415254090005000b494988403010f041101c4040d0100c550303082094200426411a900061003e000c1180c20900c1030400c01c6013603e134881901e0510301c000c0c4000c2c200b90400301d8455581c010010f1460050070041d52004100d1300e0350000c03000b5900049a081d5000070b20800455406000400280a1440003c0d142d880140c0c482c0c0004003046002030341a42c0076500811301c0c0c2070450b00c00d40104003114001204204c2c0400d251103845140c01031680007210224084808410300c682d0304211540c11750b0051240410300c100100102000e6400e00d0210003070041900c2c8141c880780200102c80583c0001006a401e192442e036030a08540c0c4a4141c118882b520741a1652104182d8009003124038600c030b6011030041601c050003403529082c001014403490034100031507140e03200c00f0f056900f41c501c54905030f1240c54000f00e180e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 233305881 1250 233304631 233304649
    0x102040608072c1e091003031202030405030306090c16080406031505010806010e040f0501090e060c21041a0702030307030c2a051e01060e0106030b090f15030a0c06030606050f0702010806 82
    0x107410851910411541b0442e00c403505090300e00c80c1d103980c002c1d200c1c2e04200300200d000407500100745900c02c0000c1040c034984050199802000d038038000b4940340d056000c0400441603020100d034032110205050000f10f03018095980342000040c03005140920b00320000703010000191089040c0100ea9880c440251295001440039088500c03041c07009507074a4010a00409006541e140307280103c0340840d08145101044540d80010407404603900b505588031612103003005081200d00040b161780b01e4420401e5103045911071489034001c0c54492504d050082d05445444100300c5c20400d81c0c990301070380e600c80030300104a20301a4901c2c4200841d1140350180c0350580405c10038071041c080242c50201c0f07102c150011000d640e44070f50303146003990343c5160942c10ba4200080c840d500c501d40b640090000f203040d000c0e940d4060801100d41041d811910082824403407881f00070740b0302902c0c0e40028080700e600350041c0b0004100515205241c248800320164441c0645903000341005510004200c0c1565020a4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 233307131 1250 233305881 233305939
    0x90604110613080604020f101706130c021f0603020d0611040b0c1f020a05090f030118061b02030a021b012f070509060319140102040608072c 62
    0x58141c0c094558841682d18001194101c2c8500e11111f4608961b060408119004229544803055000f91203e0310700d03864003000713140310740200d046002e80700d01140c2406001d006280d190050042080b6030300e02a58495010066200003504101080006880392960140569041000011030719800ca01c10f241c98403075a4442c1c42d066a000c40d040203c2440410020040d43e11f5010b60041b4515100c0c0c48000c0e0b000720360641020410900c400c801605001d204c010860400500004038a080c202540540030b0b40040141c13000d642d40c2c001504159100ca030b4030902d182590008500300504080000c0d625404141843c1c002c0798a500e07182c0d150303406007031041869124400c0141700340403080c1c0c02a0300d2100c45001d403086071040e01000501828076100c064041d550207005001000c3d00da02100300d011000c14400c8071094486c409440f01c501081c4080c1005d01115a50610070303042072140100444000c00c14030b10319022060075203d02104484079056407030016501c01c202c10340302d0b4030340e645144a00b000f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 233308381 1250 233307131 233307157
    0x3130b040309080d03050f04060f0902090a020d050109060b09010c210c0b070c0519030507080304080304051c090303030c02242211091306090302030a170906041106 72
    0x2400201600002d21000340d0305080b080759160341c00120110213413681070f1040d00601d44030b540802c000c10701d6904003801c1c03902c070410041100c1d580b0ba8007089120b041100e540200582c0420445074413460360088a00506c034100c0180141c0381002d818840ca44134500e1143c1c1444610f01c10307201000b298060140f440411140d01001d282c1e254000500a1124010100d40a0070300d00c00166245014295800246800200500e0041480c030580b03c50004548400e805001d8184121f200049506004510451090300b05580720305162800740c0c030b0300b038503610002d00700d80f2800001d03807000d944020100c00300ca4140c9004142115004004d03400c00d2001d030030426004048110100c0321001001110780500106850007803041224200b02d9070308008940003c040004145c0201342e035207008549039812140c001cac60410541305d03980c3c0b08000c0301c203c0303c01140036800101e082d0036400c0c3c00c50540700b110000300b0520032042c5061f005d4961501c600400040c01320810140d035001e60340b185416500040341c03c01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 233309631 1250 233308381 233308403
    0x10e1509041e18020a080d0e010302030c04170304050405010824040c05040e0a1103070506030c1b0312090d110d111c0c0507050a0f14030109020a12030305160507080313 74
    0x403640c040c03500341c00310f01a400b82040364800a05410001810b900e82012642e1b1207014a0f0914011006035001a1880010040500011070501105041d4400300c44111000f10f50b59442c00003440b042e164142c6c04051103030000c100001e03c1030303048000c440500700360343d0110080765518501410181406e4000799002841c0c0301300c5254105d400a00654100d0056200c41071844450381007540e01c118501a55400150a201262004900340003808001100c4428804036170148510b1502c3c5070801d00e113055100201c402808111398007481201d1007141140f13000154581d00c15001640c0707444142d421402c024504a14124070441801035000b8800b91121002d1100700c1090000c140302d045841c01c2d500360040580000d020701d002c3c4002d03001c40325140e03262541680b40c80d071120b40c10160010025055500c13091202c0069403080960f002038a0202410003684c082410010121500180080c08401c220740340c0e5245c4a0300300c004e44000c20f41c0074981c42d9595854547c9204075050440005081c10046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 233310881 1250 233309631 233309651
    0xb070312050a051906060f12110a05030103140d1413030c151106130f1712091b01021b010504050402181201090b0c07030315060e010e1509041e 63
    0x6401082c0903024883c0800d128044c07413000380040b0307003051003814003240e042c42001429a0280320704407100322010b84005900181044948020340c03100b0074a00c002031001005008000d03000c03440760b001440110080c1070201c041100039112825290f032990050b01c004c41e65800c041d83d420300d01005941c0c85094684503d988a96001c074007800310300e02c6d1000c502d40030181e400c1c0400004400b482104041040f800e9900d81d91103e100c0400c00501c2a02c0c0c04484820f20b0b210001e0701001084441c003408000d15861800110351802c005e000c4400d04800035400781008081c0c1e90014800800810b074208000e4155089070041e14184940d070701807030700a800400c203041d8a000f2550b0b6841e401000360b400449050100071054222810075000808180400c8041840c0e12804800340170410303c41c5c10006202800300610b03048100c0c1307036401440058455000d034101541e2014084242e24410b40781d600700720700c2410007002c040c0100d42d1804d0155943e0b8490707100240e42440500340310500500200441002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 233312131 1250 233310881 233310901
    0x100608010b03150f040b040c0b07050a110105030f04031206120f050c0a0810020d020c03030406060302102109020105221d0f06040f0b0a0e010321090b07031205 70
    0x140380300b801944040c00e030014180c0c90451013540b92865015895480c1d988400d4030800c05841903800400d043d002054400c0178000410b000781c0103000424521303000c1c0c50842c00d020f03c2d0120701410030070b00b4814807241d55180ea465a400c190f1500b0149000b0041000361002007201d5407280190007020313850703072060000c8140c00c80b41490207030080d220040c40000c20701581440c14800c0c5c51141d800100f1216660f6100d5024044003a51220090b1800700c000c4151480c41e00280d0b02503c2050f6140c00c10811880c104506214002007802d140840895410320900d006110108101c059501c2d11180c0c4c0031688500111381e0401417615044d013034100507801d044d800341e03a41d01035070700805500401280000b000c1e240044c41500c030380e1019150380d550801031001802c02856031648141d03e415403e00e40f07541e6482220041d181c004d1f500030b041c1d859418040d100c0c484204030b0b95261841340030192109948610000299000b24030070756135034030b018034086450890b0245015a41c518080910041c115 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 233313381 1250 233312131 233312141
    0x41101022103040b01090b0a090c090e01090218010e010e010309050f01060611100603170d0b090a0209040b0906010206040212150c0301090e010c09120609050a0302010c0801120c0302011110060801 86
    0x40965056800c5031b8880240d642214404049a903122034028000c02001d421500510807001344c0345000c440b100d0780c2d0901b44009803400c0e08140b00040e00800c00140004007c0300c642032024007441e114017101400b4001070105180104410304040d21440208207101e030400079585860781100c02048555601d250050000f800c3c8001d07450140030348402d24200d0030650081405032030704000c0e1804a410081045542544505204000705440c1c940c010721607a54001501e2081ca0501405640c40000304100b0045408401032548030300605000c0c04110f0740e0000ea4075070322682c1621050b96655188003a01e24201000b8031a50b941d031495030410114908032030245040324040308041c40340c00300111000b8242d5034900d0081c800504403c0003000f48079811240401420301a16000450035a02e0b215941045031400003600942e45400d01000345507480000070340100100c508904a107042565003055028151002a040150324240d50181c4403081c4509407240107054420480580c0d503020307590181c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 233314631 1250 233313381 233313383
    0x6190b0c06270303180a12020609010b0105030417160609030309030e04091205160b0103080306011e0806010e12060f040507090e030702060a0e06040611120408030304110102210304 79
    0x1000d126504210340307494001c031510340024406941155940780004c2040046880110750307901c11186c400c000311303800c00d800b1003400e403003680500520310340f4101690a44400030b440904201d030420070003000c154001ca402c00d900341200c2d010380d500c0c428000c165400559549014103254505a001d000b0103070981c2c0a08513091003a03c030840d4110321041000112041400040c100c0c4d003c40c503200458900c81d00051a000300c1d118142c2c481c0880c55151152072000980045420b01302c00002d10000f581c00c030007421924a0081040c10204006000090543e031010b040c00e414802c03c58441512640e91040550f80c10980c0011a20240381c901045100c0c40c0b010f48081e1098000c0003000b2074504407502400701084a0b01c0011898009103a00303102866000c0b600780400c000360b41c0e1240103207035120401000100031035510b5402d1a44071924090502100b1050002c0000c1c2c100030402060301e0220035254000d4101040340401050a4010307818200000d4a58422403400c140050004901e540514021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 233315881 1250 233314631 233314651
    0x21c0b090f04050a12050f070302010e01060b04050102030a0e0423040611090102070501080604060306060f0306180c090f0e0105011e0503160e0a0e0a03050c011b0806190b0c06 77
    0x941c03200a800c014002040e00c0c040d103580c0142c0d010704089404112110b403401000d00c1c20600d00b0420200980c125040311100b00c005035111060042d08060902941000d4000c03030322658035041c07510001035038074402e60302500d00b442018980381609035103503803007401080a08409202c07007801c1e0341e08401c40d2010441c0d046610303a281c08000c0d035030030750441c0540d0307401d01c410f800501e6114200b03401500c054100800703003940a81c075501c01000150076400780c80b000f05072503c0c84004060171807a001040e0746117401500802007801c6111000300b083c0c3c2440d0b40846409840000b010406010040080d00229030401429802e203800060810400c24910043c940c084060800741a140e004154540d100301d440c4c40c6145030130990501c41010004400ca400c0081c002c000203417040b0708007006081c603101710801c0d004280301043d0040340c074400b80a00108040e03031410b051051001c521010303000050192820380200c00c00f44107401403180c011200006080e42450351a00d514401900c5580c8000850708030441c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 233317131 1250 233315881 233315899
    0x8090c0310021207080f0c071401060e160c08030a0f0f151e030510110c0f0a0b09150a0f0905060c0414030f0d051303021207030c05011d100201021c0b 66
    0x1503071150301146e01030150444484001d40724440045420703040441c0640c0c418140084079a081c0600b407280d0300080200700c100940c28a00017007084110b4039030103e044148058003008100254000007103950040414200107641460203c0090040442c111405040c9240c80e00154500180c05c1c3d4a8084602c502c0c5141041c4046584000c0c58800910000b4015409415030030709102d603907040803500e20314501b142e0303042104c0302c4002c07458020515a10516900102e130003000340f02c1000d4103180d00c0707a41d07107004050820209136031090602c001091041000c0d903402c1020040005504a03440042c0c0107000c44c1d02d0390420900e16682540280300b50454148880b224144505003ca003070302410305102e02a084810070760754255410742c4071441d0700c1003440c1c481e4804070050b07452082d19030412403460010507085056207082e80158080760004e5060001e428081e10f106100407215002c0c420f019900900c499200d848140d01a0199201446440f441812100206d0030150702002a41781d08507480c0e24 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 233318381 1250 233317131 233317141
    0x409060b0a0b09090103080702010e060f07020102060609090604030e131e0f06060c062004060f0809010e0a0318080102160b010f050f09131b091b020d08090c03100212 73
    0x9181e20518080d544c0242241004202054001001d48251030060401c85500c02405000070160b0f80111903040c07081070003055010540d64104a10b592102050302c41d0400c1f4140002c01c1aa6800d000744010100319015061800c00c0d242d0742520036440709040e0301803120454040d0101c00041c18803407401d04451403c4e440f94040c2e855801140d08072442500c03014507240e05500c65034094100c10742c07903e03d500b400c0c41001e096124010010402000c680e510031001201c50032000f440000c01500c1481140c1c1448103803d80240081808a03516506081141e80c1110985448051624660180c0b6042d4800305402d1541c3c0b083c0708080da591413080c4504815603881c2d4584184411060084507004807281c0c000c2010b504020450079040a21414009200220b941e503800392580c441580b107800d816550b00c1000f01c0c008500518002441c030f918000a0352081d454000d649a1130b01210070100180f420200d07031420001d1044142844014090350702d424540308806c0060740c40b00004c0d6101594080000d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 233319631 1250 233318381 233318399
    0x2007020117180c06310312030c0806030f100e0705090403020703031119080703030b131d1506091b030a060e0a050402010c020f0310090c05090601171605090409060b0a 73
    0x6006007400c4409100d980365100301d81001e100c62aa0003081c45441c082010011882c07c81e501b4501007165030f0301250005c000744006240c040c001d4022070180d400401c80d00c80903840400c1c42c01014400e408005405800340c0b00303091601144d07a00c9076030052041802d02c005c5c5507010803404141d9010f900c500101010032407170255902d5036110346008801c4c4c402002000241c0003030003084180d019140104003002c6220000d010b858004005400b40d075940c581303d0440d6401880c901848a4558001d050740e200900184141e070000141500d20405201001800d920600b102c0c004c21844050030180e00c03480c241d09084000c241501a1041c9140c044000a00d5060740d4001c0510503513042e511850715490642c00d10900940d00e0b9400343d03043c05105010281c400061203464a518025845498401d20b01320030b10480e003001610b25410464500c42d811481b0704800040d0750088400e001038401303c0d506440440740c13801080e5040d54000c1c01d001459083c031641c0e402c01c2c0880c42c07040b40ca807015941d5500b000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 233320881 1250 233319631 233319637
    0xa0f0e0109171905070213020307020c03120406050313020d08030a090303050f130b0a0612050c12151803120903090102010506010f020a03080c04050d0506070e042007020117180c06 79
    0x1140c420700210f034404045403013400644981132000d450300414041c0d0b10340390000d80c0c00860712080164800c0c50f00007010305d420010207900a0314100500d02d084e0519600406510004240c2c03050b0f65411491031045403211008a4061b5421200c515101d06001c031051016001022040d00003a0802000c10030034601c540505000d840e625100003144203066541105102c0c0062245000d156280d500090340383c03507050004242446880942818240d034000c0100000c400200f4000f135500c4940c40313030300d40003c0c200e25542003a40d6003901d0f000003003030b80342c3d040c914401d000c94046104c415409004110340000301a100f6030109800901003a91038500454000c0c0c18800c1ca100107078480c0c0ca10f103003c64004c20825400030b030082462481c298403100071401c00e59440d41e080702c80da44050108607130150b005800c5025a5000c440601140c403261000641c04003456110507030481c03000070304c403045a02800e0b010b500300c102218002c2c038914100e000c0c8044208039480d40ca8a500602000088901c0e0220403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 233322131 1250 233320881 233320897
    0xf0f030109050c0a0f0305180d0203070c0e0601080117100f060e060102060906070c110d0c0303020609120a080a15031202070504090203100c02031c051012020a030b0a0f0e010917 78
    0x525111707030040d04c07040b00a810301824502ca501090001c01d070031894103204411b0721003502e030000c55655032549841107201c00c032580459a00382c0007000707001131a030340f0003015411250110320700027820303210b80e91a0341005e490a840b0303e821403a0000240c2d1284040d08050200c172440480741d0b40c81d0307807164016619141d0480c2d048000b50000c10008100c0c5014401e000074650213030704015050b03281d09012910f41d01c600401660000400201041015070400c201503201e19101b02800b852000c03800d04961038014111080140150280003070b9440c041c40c2c1c17240c2c4501000002c0700207919505d007404903207400d4071400040140607c0e18081000e080078012850426400340c000e24243d0b00528502c0001d0803200b12100840c0000c010b42400340d0401c85003903400050342c00001a6500b01500c05010000036540310302680300b5035088440c0940d443e00e18a0084a400451031012a502c18091400520000310702812891a210254002c0c0c41c055206240b0544140001010070680d949105481d00405403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 233323381 1250 233322131 233322137
    0x18120c03061b0405030f010e0f0d050703030c120f060513110403020405150d0312140105010807141b0a05120304020306041e0f030806180106140309030f0f030109050c0a 74
    0x41100c2d00c9105010707104010707280c1d0a140c14107441d000020306101c502c00c04007000341e4440c2107540100c03005010084100c40e11030b0090010b50002100034100f406110400307428941d441021a541a0190030710001d4818a00d804014041d1083c03111002000503004060140c003500d0401820900c0d180310303042078411150f204c681070034556403c20028000c0201003e048000940c001d2445480310f80e00d00a002d8825200e030351401021000d1181101c2c120800c01e0b000040304070042106980064010b50021080c2c50304002d03c06105101554a03c1030744840d54040300142c10481110f10b0220706201450311035800d481d030369030140d61071035210301090700c0180d41904400701090000301070003c001040d0a00340f4009824912a464042c0c46150490065021600403003c10513180b819504840e46501030824090a0b5414400002c20003042d649101c1810107001000c164504410801d541030481e000602d01c1d900c1400c00c141d62601d410070710400c80c005082c0408560381110500c140c62681c0e590369 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 233324631 1250 233323381 233323393
    0xc070e01050f0f032515030b0607030f03060503030406020d02060a0905070e0a0623040c1d0d080d0608011508071401140c060106210203061503100b18120c03 69
    0x80403c0900340e4084074150b4588110341321703406519442040d0f040f07010780800c0495119031800140c180c05d07811582080d020585000d00b4003c05640d820240c5a6880d05131405000380440c5401c19130041c19540c11241c0d01d48004100024030a40c006060f0078481803907400da0b0040c2d00c44400031001d4940c20034008109400900040c0019a4502c03509540810303160380c0451426074a254010200c1c140d1041200e9180082c01101c070345003041e0140ca1009202d034600701e00002d00305c0402820910360b003001280b0801c441d54141c018803601c14246c400481032480308010030340c1d0b6103203c103008112030458082070221010340001c42c80c0300441c140e02150109005034100c85800e900454070300703029114030102040141f10f41d40b2120010002c890123824217444020700300081141a02c4100180041000414010000c019264690344000180e1480c16404641c40f611011440101c015507500b08511490b004541c109103009152101e40c0448802c1d115031040c086100502c507240e1135002440c40d003541c07041c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 233325881 1250 233324631 233324659
    0x60f0306020c071a07030305010806040c03021017090a02150a050d02130305030c010506010e060c0712050307050a030c122c03011503080702121519020409050c0c070e0105 75
    0xd070700104031080e40c410a03079007041d4440341c03104020034901e8080e0a00c524082600010960141328850145c0b03c00c60080800e841d080c0e0b00d451071441c41d400020300a410003000f07103004901544840002d01284c9100299500d40f0500640d502d01c0c40810591150a84222464403140e256085910124090780c80c030b4941408486880065402101c1000e000c80724507000102094060019009161f0094004074040c20300c8400107046c2c6601050040c400d40c4200003110a103013000a00000711780c5d0018034094017191509200c2d0840c02100c0011301540500d5450400301a480021040c15900c40c04803010a0090440119130070541700820680d03465000d40d000e000d2082070310501100c6c0000600110f0000110501003880c810b00d540304540d4440d000c500c80007103141100b20a44030b00e40b10b200500361180001c00d688166407000d09940c5010403220005082541e0540407a4082c004004090100382031444039005241e01100025840c0e0080040100d004548003d0b001c0c12540000c0070f200d9030b0104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 233327131 1250 233325881 233325893
    0x40501050708090d0b1906080601050a031e060e0a060606030c0c0f230c011d06070807030e03070b0a17091b0103061805090d02010207050d030b031908030712060f03 72
    0x124540d440e034400d544d00707960000a40d09510340ca2146c82507540500604100d50448030540704160400d041d240c008000600c00c2d9103c0c2d102800071641c01591080100c480d4081e1140c0b10684840050070351b5040041e0752020701400a507080765240300b400c00b00240359403030f8000c808560098009100091070f0b01c0071309001c1501c449942c00c50038083e80c10040024107101045050500300f03412030036550001030145403290f801500e400c00c940c1043c80340203250b0080e00001501842030030401000b102000c65824241407060f80c41c03540b0014060100c8001c10b843d0401d6510a0f0032030003840c8002000300c1000b404840403039901c01d0141d03603201d00410300c80d28201040c020050122440a0402d07a9942001490510303104035200b2500101c100050306040994400c2c0c01d00070044003a1041d03a00420008000410005112288034502d140008621008200090420030030721001d41c00304400142c44814005440c0040d40518a6500c03035182e400040d200400584e500c41c89407030402a1003030020004564 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 233328381 1250 233327131 233327137
    0x703110a02011e2f0c090c030403080c0409020a12060501111b0303121807080601060206060f0a05120105060a0504090c05040f06050a0f060201110316180803041701050606040501050708 81
    0x31035051940e082003100000303060341400c450f103c101460401c4d80c151440c0c08148980710030f00c0e80c190759444061601d107a001382903100c090002420452210300040d80034103000c040d20060000e9000946d030301c0341b100300000d1241e180303608002046071414000054940c046d5088150701001000078104554402040b035221410748000160140410800e42c901000316214152140307001030414000d20440d801400c0c07900d101e40e003101500c0c0e4800c4c0d0041c08050f400140ca160710902c01c40b071200b072100b107040c0840d02102c0f26501c000d41001c0e4580d40014060010b4005c103211344400e903000c4c80b8070350b1307510100b000b0703038810b40341c0034220300070050091200341811b801426643c4804840843e0b0f0542d01c4000c28622441035021a180c116444010701090758280a0200e85041c2c01c0e40b03003800d60500000d592084000141d2444c1840091080d070301c00b1000c2200d03480000d148a0054a490365545c10904020f03050502c82150746502c1c140001c1c03020314080041d501940c0060750b80c0c605000d080c1e070f01c82445038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 233329631 1250 233328381 233328437
    0x1a1005040b04090f110f22051e1513090515090c07030225060f2016080703030c020603041b03060b130e0c010c170a050703110a0201 58
    0x458200004a06005407600a00c024030306080006041540034918000b03c621658021201800c00c01016400f001c10000360780c42c50400c3c91381500405022942600b2032907180d8445a0880e142440c1c201a01c0c00004501901c50340559160008840c040d00680d0944038055038441c040f2140700f800c3c000103405a210030750151094200010300d041c800009140840d080b101d20010001c0018803800b007590500c610380c5000c14020440780d801a03000c8060031000c0795801064104100519903a0680b48500d1011080f80b40c92203165030103501c1c0c0c01e04207440e00700880311040309401092000501000c0058028101c1e90180d413891000d180da03a00f001480d600140c402d5441c0f44010000c1180c840704140b030754004610500d0001440c1000d2818008240203032282e4802c801d15201103020a4000801c0c2101090000d1800a10380d0b820362801e10380c244000851a00c1c1c0543c0441e00c405140c0e0010002c0020780c0c083d0326048565803003005400d650704e1100c20b000380040d00ca00707510b0307180c038280700d1444000c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 233330881 1250 233329631 233329637
    0xf061b05010e0a030906080c09010c051006030c06090501110c040c0c060e0303190e10050a06081605042007080f0d0207061d01141603060806090a0501050a1a10 70
    0x2604003a2141825120008801c2c09a50003d40300c01040581010103800105030342d003071507070f170310701d8040c01a02243c00f50b100c94505018031a4208070800c0760502c114120440400400c011094803800d0540796035140307004c3ca0011482541c00480c0540c0250704416924541c40010604401c409050002401000c0520310034032003400c904400040c060701500592800c00d4005544a142c5440b6031102e4500741007038100900e280c050580111513000c50400343c0310340310b030402080c69190003440c40300814655001c60441d02540c0e240e01e4113140002070680480c0d20841e0300340700b800794020300e6952440e4001402001810204018400900e504d000703801440d0074458801e0030b0002818a60081e68080301044688540d107241d10409500850010110032103418020030015034075140c0c200c69402e015213030b450491018003a80718941d210b9001140640a4070082d111387c0d040c03606410790ba59250100032201365003080c0014403140114850210700055051111652000d21800c0c05444065040c3d08410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 233332131 1250 233330881 233330927
    0x3030a0e120a1d0a0b03060f130c030204080d03230702070911031e0c07060506060721080a09020d020d050c210106080601030305040b0a0512040b041101090f06 70
    0x10400e079a0028100000b00c588900b0b404076600401030b141642d00c00e0009104201116051184254800903030b5404082903500c045000c01d03210020b901c0300300350311500700001d0a290b203070000c040e81a009070088a101c20704071007030b114201c00190191814010074101da101400d0740c1c501980c1c01d140d4896001800f81c01500c00f090740710787c418000c1d1074400c40c5c3c03900c1c2c0d1640001845420300e030710b00d4041840443d01006221a0912280900031403003040070240c801e541361000f00f18030b540d80c0c000710b5880aa101403254400c40060842102456021134880046520358001450387d010901403407007829802007200b0b104046035800c04c1081506080d043e64103102d070703403081a00e51303c6a501da02c08101075115100c18003507150301c000e820354450781c01c0028150804001000040d400405407415143c010020a48a01c20b9141c2210315000700340e81a00c0715800d0500b4041404008141103000301d0048400c40d5000404074019112802c00c3c7c07140d45620001c1c5881088190b10a1150704090081a869052 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 233333381 1250 233332131 233332153
    0xe041509020306010f060e0102010e03030721050f0601090b1801080c0903010603030908160503070b0f0d060303090513020702220b03030d021809070507020d0f140604050d0203070503030a0e 83
    0x8a4803809805c0207503620340d500da06000705500000301c218041d400344028049061310f040316071340382c0c0000b0b4180818000d40090401d0400b0064003546640c03039110108010354982044c80c00303044101510250b010941885000c140c03019618200c49401c4d400d240b0382c00031411100011200880014041d07481e2640034014a146136800303008040c002c5001e5a1080d00590801c00424240410307100b070031950404003142000305d034902151001c00c44010850702600c0b01c1201420703d83e188140e00e40301004615201c3d01004051300540e000d02a0f41d010380700500810f500041c810101e01c00e40e400654881440c5440b00890400001030380900c00c0307890804a210922071021901e0f6402080302c0400f01d0740c01007410f0b43c000b2010303079003e0705491044034001d01d00d0030000341c00303422071184c07840103802209940444414080621641c400841d0b0000b002120340402d0700f8910303121a4103a0703044a00d40210942203100c10710000c1a205866040409949141c8070110b0080040c440d80d89a441580100b4010351 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 233334631 1250 233333381 233333383
    0x120c07020a0305160501020c03030901080c030405031905030a0c0c030e0904140102040e0a0c0801030f0f11060307020a0c05060906220504150317030412030209010c021c03180e0415090203 82
    0x140f0400c4c0310616200c0c6141084006424484109080e601aa10034020407029a03403101406802041001d0481d5503a100d42c2001403c610030b290850805c494160710719111143d004004500c0740e00d02c00c008012505120b141224820344031400500040c081c00024206440c000050302c0e003107441440300c24010341c10008820b080ea08541e00c001c1e0020b41c00c0040020b00101400340d0b4440700c0c11450000701d91f44c155942d600c40400c841c900a059111070b03100305010044072030a5a05406030080c1442c1d1240392281c0000e44d114103c46007196030a510510006260134540c040d543c070050000d03c00e500f8000d0a00b1038090180201d180510f100c0c1d40e800c40003505e600d90340b1070303d44541d0ba201480c0405d5825424410f0710040c481c040d12002040420821000c64a0307520700d110b48042d103107000341c0d469600c5001210f5103100701101a60040310100c036046540d4007400403041180c802c1e00c40200d803940b913518094096010707200e0440607140c00380000f00002c290020302e089510201d8000604007826402203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 233335881 1250 233334631 233334643
    0x1e1504030824120309040506060406080403140d2d110d0f02041203030b0306090c100305040501150902031b090a031106040e0c09042405100e03030705030307080705120c07020a0305 79
    0x340543e138000055503082030a1030b000c0c00394451802d4400a1520f40740180061251310024009001c0121512400e01d034811850121342d107400074580c0a0102c0341d0b00017003a00729103400006c8015840740c07078440000010b105000782100d5441698906007054066404a8090000455201d810076420080030800525141040555500950740040c003d0808000e06180000240081c030803a4080000414190f46014012241c42d43e80d2074003042d9500c86103010341c09041564040e1301012441c420100d500452540910700c034003280e04802d4a080206291061140300d500c00076901300c203d544090012030508030584031444005000c10303283c01e5840d5100e00c00c032070066034100003d640c001030001c071610f410300039a00c034442040c00821005500c01c4005400d6881480752a000303882d04601e110103d03000382040da007100c074054196a0743c3c9840d454110307202d9100700c4244002c668110040f40b800c0d031290003540c1c43c3c4520300b1902003164031036052042c1c10760032211040707038410a030403000300000d2820700607 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 233337131 1250 233335881 233335909
    0x80a0807110c09071812031425020f030613150b03070504150506031807060806130f020f07060207020411040509010614130e071202031e0a0e1e1504030824 68
    0x980c06d028042d241c01070444104040710802c0c00000c4c010368441c5c0e24506c426512032964010100c83c107429501c081802c281107c1040c2e540750140100700310304144d03080c0400340d0031841514180007403003007051500c0407201c11700c0d4015019800700e042408141020f40c03204040e04140810141c0b13641e0fa0380002a00f0ba03104036201d20307409094440c2c1106c032a40400c9107102410490500d081d0f1440e0840106000b1300303002100710640354071840c074407083c1002d5504490264841c270010664802003410214003070340c8461400c900451800004402241c400010b9406581005007a80030f1a482c1182c00c030717601d0040c246103000b00c280401107050300407201d54540b0003c1540e8000500c4910f044030b0060000030400000a4106004000f00001072448042420f030f000c090600030441038541c195501c0040948211004461003203004104038240007440c03200c1c41181c017a085400c000520309106600e002c064400801240e80f50700400e840540c0892032603c480c5511034900400038030701c0f00141e003107085160b0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 233338381 1250 233337131 233337149
    0x10c02070e06030a170d0614010c0210030b03030301060e0a050306041e0317180606030a08220e04080910020c0904170c07090e010c0309051902060f07080a0807110c090718 75
    0x10005040f5941f40103c0d80181110082d901040d81d0a80000e410a0100710f0024811f003640410040b6160082d480312442110260490f910396031503400c050140081c40c07145901c1030210303810004a900e00040c405200d241e015000144024031100320307000b07850012400301c040c001480a003940080c04001c0c3e49215604080b4502003c0c054500b0003400c202c00980014001d402404030440070808140c00c548030036486240c03030703200d000f80080403a42c00100d503080309031084210800e001c14032841c10040c0c8a2604200d50150008082d06020707a0b035900b41d1a9240c0e0008140f41c0000e01042501200740b0310440410545890550801265070800c01107800c00c0c400c26070340b0a01d04445070310034881c034501d821050800704582c9a03541c071030594078a507095030240c11080d200d0500c803c5481e50700030b0344c1c11103150284a588562262802810700c0e040180300d44005890700000682c0700d489400c0c050307507921000e0050034243d24050140801d02000920740c4040c400000306840301c001c0002040c41c001c020801d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 233339631 1250 233338381 233338387
    0x608280308180d080a0f0e1c0e030a1401180c231f0e0105090102070902090102070f080f150f24180103050d08010e0117070b030f07030509010c02070e06030a17 70
    0x1405c44c044076803819121489918004988045001c00a60400107201030a040c440c182019074049070b22648824801d078050160300080c0040149416402c1d5944202d440240b20b901d9002e0031016500c044040301402c0d010780c003081000354080301160714100641014040000722441d0002c5071104a420907440441d004140d00003d1040d40407a0740007001c0c07424a4a2403405511800007589c80107580202841a40c1c0010303580c10580c02004a03400900d8440b102080c8165140d08941d15101200903640450290215155103008180c00107841020707811345040f8180c036007454046c0501a04071702e01d4186080c02d03441c3c0d104e6940b01c8041c0f406075108140840720640c15032500c1c2e0b08000c29100b000c024004010300500c8800c140308103183c15100b0040d00c1c4104854203d9445182c14039941c001d101c0c001c00001881443c403081d0006910030743c2182c509024079114070500314200c505110240005800080003803102159000000b600b00340010f04440c80c901042c1c980d090500c800156589002e0000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 233340881 1250 233339631 233339641
    0x16030f0c030204180c050405010b12090a020d030c050705010f0504060e0114040906090b090f070f02150c0405030d0207030c050402090118260a050a030f0201021c0608280308180d08 79
    0x3c070310f017024150955050102d5450072007288568003818484460401402c8006011035401f080710018842c0c000309094602c0b0b40c18100680602c908540c00c1d9424000c61002180a500030700c0b0081c01407a0300c1e03075401d00e010328080080300c1e4140402c2d141410403032418601c100d0014201c1c040d1001e0820400005a146d01d8030013124129a0f540c4060385c09241c08c1810001e011030610500c503032003261400d00313440d40100d0800483c01d1091035140d01d0000c50b21801070101107401400034000355141503049460521148009aa40e1181884010b0040040342c0007880982025000f401d0043c8040c10544556000c40009900c078154030780041d11a60220100b920b045851081d0203840c101100015003c51107807500e4542d2130340c18411014052080d882e4810130740b50700c00d604aa90502d040b10a00d480205140d0710040903108512445429101ea0306d0750b01d12904a03c80b00c0080840202404050b04501c2e0350140e41f01b601c01009021800050b0303200d580180b0003801101e640e05203640d0b4038401803400b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 233342131 1250 233340881 233340893
    0x1404060c020f062e0314030a0e0d020d08090105090a0311010f0c0c0504050c0909070f0f0212030a0908160602040f0b070203030904091518120216030f0c03020418 71
    0x284506070b812641c04601804058201030801090501040d6110001c205800400b042004226840200b801c0c46180240b1405074010018105084440d542c4003a000441c00810000443c100406035111400006100020304100c004004c06681810a1800c241084001402c0c0920b19402540c0184820b10038031255a44107245460404032414a030328641e8564803100e17810281402100c1c040d80d99031000c00d105031203600070380e1500d01000305414028a89054000d0034044021103c0c0b0219045049601c1c40d240081820901c03081241103080c00d6980300c50640c00a403c40c3c610070744214008100342c3d206400080a0b2070b80450240381d002d42e0b914540b003101118842203038840d01d40751200340031410051380c000c411591505012200411040c00d1130611500b810b0301c0c04c19902c48246002c68620004035004c3d00c1880302c40c0115100c8014500162043e600c500901d00c180c1c0d841c8510031000d0000442c101c0710040740c103001741e220403803907034407640400d040310380d01c01c290030259002500348410418 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 233343381 1250 233342131 233342143
    0x108010e070f0603050702010207080c030a1128080903060403050415050405010e0925020c01021212070f0c201207050a09090809150c1504050c040207061404060c02 72
    0x340040041c6001458aa0032800140142c0509010136880700702040d40030303200f501900c0c1d0842d0401d011658901d1140401075a0303902c1407150002040b048071038500303000e00100304c5c400c01080c00021501c074060500740001091f0401242240e0074042481080341c5601d0030003110b0302c150302c203484540d5a1803c20080c0350f2a40c02c240440000c0110410050001d40d0384040341342400c0405a03161601030b00c0da40c1c42011030721000700401890840411041143c0e65001504444496083c0c00796001035605204144940c8213a524410904888102041c45a031044003134405802d020b1801c0320201c40d10f9942c43c59020507500c07024064030000c0102d5000d518003c0345400d000010703800141511881c25011a60710b40d424806d9402442d580c44454083c080e070802200c50b0300748024030110038242c14012035155a00000029001842000c844041420703040002a0041e50418018502245840c0411000c1d40c85003030101d0f1415120048104561981f511550250348a1500403400d46030000700240750030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 233344631 1250 233343381 233343401
    0xa021e030105030a1112010c020318040209060412170703030605010e01052a0703081c0b0324131a06010f0504140d0c05060f03010305061003050c01081f0608010801 72
    0x25010801040320355000501c40d89401e600c440e15000820000002070482c440c1c001c400324480d424a0101d01c51180d006c002080c00c2498000c400c80c4070f080c001c040c40101d01941c0300303a5410140401083c40000072107107a402480344038a0703a100c00e554405030b074540d45030000c42044000c03070b440d500144010368012480084004083c40c01d02c0c1071074240f540921040907000e089005015900d03001d40310042c414000c2602858228200c039075641c039400e00c00c50103581c2c9030f48204119880c01c0d61711401850b001c03c00c04000a41c2d01c620500e07086005003041c4101e5000342039460034120714618000042e126a03501032161144800703184551502d50000340560445040510800404000901c00105581107a1016480540d81304500544a240ca2151544250802944510040362102410310901c1c001c605880c0f041054404580b610198890807100d0380c04000c0107600010040da40035441190426031101442400d111161342c100844610b051280d013105001a20b4a401407094034024000d012200c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 233345881 1250 233344631 233344687
    0x8030f0a0c0503060d020a0f0b120c09090403050307090f0b0309010f0510120c080f0d1202071104090501062c0f01060507030c110402040f2306040b0705010908030a02 73
    0x100701603000140180b100600c4544602c2540580400350345a00d41c4a8001d42a82030581040381d48402c00030409070040001c100861fa103600000d56140401c0003550030340e08010344905c041d601c1e669070075070300d43d04010b010b0300c20010440f0740004c03404411441c1d00c0040281d4507080b81e40c1d0800c1848142581d107012040050107050009100c40342d0a2001e4a8045070100080da0085aa40303140c8140d0b044031540c80320065100b03254190b400f080c40414482040d100b551602801c0807440e0020109034083d200d8080c2100c0445040700035142020f422840c0514400d4000013a0303152140d12620224030440d0301c030240301100c0c0320340150074108038100c0c0d608403490640c2d0016540c90010004c1c690311640d4401820044d460911804209810300003011410001303109644840d103654822a6107213851007059810082c00101283d4800c03848002c3c02c1022010703110901c0d103828620f1f025a5640105c2040720590768034043d55020078140c1028600910312201c0141e0343d80190f100394036204801c403496481d2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 233347131 1250 233345881 233345891
    0xc030207121e05070203011506030e0f0d1409010c050d050409060f030b01060c050a05060108031903050708011725140102070e19090803160207090606050d15050d08030f0a 75
    0x141464800540380c250b040c5161550340c8041500c0864003400040c204010310300640d0002160541d09034004896101d101d500b01d031441c0d995649900d56400801d1840c070041030140c1c00703056800462034024624010181030410301c40c000c6a40315440e00341802240c0c000030b8008541802941c1044c01450010b2112203049001d03541191141c41404d44184105001d028181d448001001070070720002401541003801e4880070740e501c505c015103035400560b08500d1244a808580982c60082c881c4a02544003039403440b0302a82000724114840c5655500401544240308218294035031704c010460114801d00311900e05145889520001c0c401070040745819900b02200c01c0c415000a0140185e0080c0d00ba4011405003280032081d40040400300c0d00038007102400800c00070943c0524a808010038040d6088801d0103a030344d00d6110417038000b0f024410004804012521019255812101000321040e0700d0103451640d40000400c1da072020390048444170f10203c00c00c24610a0024000d510008010003481 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 233348381 1250 233347131 233347157
    0x70506010f050105091c0c08061003061104030f17040915090b040501030206030c030a11161203050c0714010608161518170109061e05090706050703050c030c010c03020712 75
    0x1103010b8140b01c0302c8251014100091092000812168000f4230a1000340d60700c1d41084036200c039402e0f170710b800180ca0040c2810074420340d5002410480c0c046a40044c43c80152070340c640d840d01e104c00d64400b01118007007024070001c201d40406120b4a03482e0346207050072000c098581001c1000b6a0b0300d5081d4a032050b441c1c00c0040025803107100481c3d9001e071403200c560b0b59a684a01030fa400429010440413125040451b996074800842100720008030700030700300134034010019032046041e1101260000d00c000014024000042d80f02100641084c0b00b03940007041c1561203c02c5a4900446500c803003a115040500800c0031070b026000c0896408003034900300030b5007581040b071985a04918803e81e03c00d000d20300e0041e01c0085007075002c1c416142d8002070038007180003410780c0200c13900e6006903501d511516140c0868281c880000d6001e003101c0c6151074807402e201594070180c50a401c2608501050b00007004404c030162003e03c41c8590b40d49031510016100c460609225802001c2d0b10b0710f6806018804903002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 233349631 1250 233348381 233348389
    0xf02130524041203090308070602070b0f0103150c0306030230010b0906011d0d03030506030f0705130203270303011a031005060c0a0209041401050f22080708070506010f05010509 78
    0x282c01d54000c0303c491840010146000c40d030b80881ea50010b880701c007010544004026442d0002c14545018813400b81880d2100103a043c814402880b0041c620700b4040d00c0698140190782003c03c03140110704000410315030340e40115000308084414070100c80001c1c6506001d82044a045048180051000308200040c1d00701041204801400e000d0505c04211364181c041042050300f1001c41001403c524942d01d990f01d40078020309802d40b01684a030080c41c4000140b40c070300003140d02c11275a00501c0c0b8900c008240603100300940c005000003100214410f010700440780d00c101804002801e00700207651302e40c5048000380c004400c2c045005010070303041050120100d0030000701d100362242180c00c070340c1c1c40300b0704800745243c07a0903108003c2d001060b0104000c144a01401c040c01002080c1c40207101039910503100701d10341c0b030048404640c101e581d600400300c40114800c81c00c442c0c503c20300040b41340c400151900507240d006460122040d50000005000d0b41d400010148003c007800e0030080e007003408281c002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 233350881 1250 233349631 233349637
    0x101e03140f0c0918031804270609061401031407050409020603040219050d0c080f010507080114011704060b01021507050d050c0f07030908012d0b040f02130524 70
    0x81c03481102070802107203c510001c290701350340f564807004699444a14200300c003555040c2100d1030b4822481c145001c85040c1465140c0032502d0a012030042050341c0365540d401c001c00300e001c4150351b080c1c5d41e031041303038180500c85031102d005e1340c010201241e105072101c0c2c60074503004039a00704600030303801c0441200050302c07107000381c0350499412217004200d49003c411400002e0030300d51092344c0c0f106da0403845806001001d210f42040e2208001600c140d0300f10000c4403403d9400070788150b0009500000100b0810780c0340103030044207185c14075080d070350840d0048910050240c00c0da010390380241c1e500008151580c04201d0514000b20b1785c5001900c80c500104050050b0060040c120301c0542c0b40c4001518411202c0b0454010001000f1200c2d2101c1c00c0d818010516107403401165890341c60169070810f2a4084602c80c0090121640100a0301e40e0f4034000001402050080ca84c0081d101e541d04018410030340041c26110402e00790041007603240c00c0421061a0b90002d844400c071440340a50a110380c410011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 233352131 1250 233350881 233350903
    0xb0403030504061401180501090c020c190b0a11060a11160524011a0310030311031611010f050f0304030c0f0c060305072006040b101e03140f 62
    0x30000305581c441c00d140019001d0700c050346030f4244609001065440c455111211066600c4000f001980e17229400344c401c9408000884d00540e10250041c1154078244488034000000c4a02069103181e56410035403840d0031003160358000c81d024000030001840c0030080705511091869060040020300380611f00c4a203d1030100e09445283c942030841800300c100192010a002c64040c903003d0301d40404a840705810a0060342c1d9282038024800c8044040402901e016120200c10700300c0320351541e50140c608401b5061400f40b035002c07d001c010000d080048088591034001d1551800203540ba20004181c10005e8007500c051000c10b002d59120120f508064a5002e070381803c03e00d107080705605182c0e03042841c40800924ac0215420042156a030540000d800344c035180d103402c10300b482c4400041903d10003034007880700d050380200c0019020800c01c0c01001c0c1c12603880380407082e4440d00e0381030b001a000e000c40c00001c4034010442080027005010045203401c1c880d800050304501d140d144032140c4031003401e00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 233353381 1250 233352131 233352137
    0x250c0303030f140c0901020d180506070c12050f0c0d0312150b030a061a03011508060f030d050711091306110906191101050903040b030c0702190f080a0b0403 69
    0xe001104207229a2203490078a145000c41080da19012403407180ca1381c4802c000a0050240c1230018180d58001c0d040c0070101d40710904001d80b2a42003005000301500101d400b80c5202401c00c034000380528040901004042c01100070784160070071482d52a151080134101c450080186003044408241d008c20f0404a480360f04001090543e003a070810141030350701740c01980e60008000144001c03000d03942d00110031900d01101c0c618200300039104c2c400503130000344900846200100c90100b09070348209815640301c01300034600f1000940c01c0021038901040fa088880110b07034005400d01c03d004000105000c0820203c070101410b03d8032852403044802e00b0400108040e485600c4088082c00500503145806c0000d410180c0700c880c002d080d903014100014201d404950301d0f4545100f0321106000e45031040c1a900000d43c6054a8080c040d0070513400101050b20380342c0c00f408000c00590b51003401e0441030407a010700e54070305030401d2520103003d500c0303510a0035258001220a40000c5010b4162903105405007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 233354631 1250 233353381 233353391
    0xe010c02040902150f07060b0603011a07141212060607020f1002030d02120105013b01020304080f0d020609010c02101e050703021803031201031b03080c03250c030303 73
    0xf00c0402d10082500c00e01090010012811004108510001e13002d0140989414400c0e0b01c09034003403021921080c050400401d0391640d98040d09141c034002008440e1050112035a07008500d181d1500300400d81c3c4070350380004000075400d503801c411030b006030f60805022a42d0030300c1c00016a0010b460514078103812400f800800390404c900600900c16282101c620b11419941d403050182503507100c0b4400d018081c0450042e4404900d161441d50031904495894030b03686a100111400302d4a494003030a54080c1148810000414664014015901040407203030003004280038920b0003030f0501030b00500320041681350482d038465007039002481c1e542c140070041c8009600307000d01040b4000981c0310302034214070f01d00300414003010b95403542c000d11401d56008c0907100c800102900305902e84c41185400c62408009000600200b211001245403030064005411141c030b03a655900c030440d4112030800075143d0004205140c07d1a5109240041c1e918005801143d0708000d0703940c2e1895928138080541003580d50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 233355881 1250 233354631 233354633
    0x3d080c030d080c040f0303020a140105330303070c1d13060b1f02150a1a120a0b0901050106020607050304050d0c05160305010603140102090108040809010e0d05060a0c0e010c020409 79
    0x2e1800c4a02501601100d05c00d1941c4a0901a566004c0b140046460815241740180d1078401031055902508800d01d07494203115200001d032011728045848407070000c501c503001a482d0366040008200c0c0318890240003500e5481c1400d01100f500203880585070882000081020111082888400300e079800b0300000b0320100b68501040c02020303000654120340c20060841250b894000a00b00d1031120750070f6070003079141e032400c0389041030390010182000750b40300d4242c0c0c6032902d140c10b170074800701075040c6400c4070441c0b85251618030480d481a100c0041d50307559000140b041c039a041c1700306984144c031801d0092460030240d41e4203566881c0c00c0e00680400030404a08801c0207814001340072640c0040e01c400b01e80e1900ca05110340200304600c4100d44145440003c104008418002d07950a000140c682c040c142e540ea03104d03a102e03607000c02019410858149150f191541c2c85044008600d4081d03002010325241c8107940c0012502192441014000300b108421016a80700d01e000d9049641034078042408445 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 233357131 1250 233355881 233355901
    0x30a1101140c07050609030405060702240708071104050c04140d020a0618050f010c0210140304060c120b0a060521010e0603071e0902033d080c030d08 66
    0x1d1201c05240d4820784020300c071070144640c015151250207002980d00b6520740e401d4480e40d91155110301a081001032100c01c01515041c4128000e8641c0c0e4040303904120107407216112a81e120210440d500301c8086019014001841d4904024080c181c40c20852801c145022981c54000d51041c1020014500c030800315a444961140036032030307409008400056110400174145c0503000e0911070035041030b582c00191620303045440a044600603103407080c9074802ca03024010489811390301d40d810310281c07171041a40c6403041350080d0b110307d0041c031001402103587c1c0c40c000c150031900005030301034030300b08846074100c1da0303402d010f00080f0740403800c05958503588841e110301980b200c4c21301e2107450002c060001510a13043e4400d41d1150300110203a03564140c44960000050300c54942400c000200080705022000069005542003800e80820ba41384031040a9003a8000c1201e008640d8490065401141c3c200341c55410040039008050207042e40030800d00100c2d0781c51081001041c03c102c001e901203500507203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 233358381 1250 233357131 233357141
    0x4060504150c210e03060f0c030606190c0201080601030207120302180a080c010813051c0e091e010b070201080c0721020f0d050c100b06041e0314030408030a1101 71
    0x20f40503581860041c08441c000c96200802c081035408660f15420a04039844c011030003510440f050001e08000381c03614041c4003074540008169a0700700c042001741400808501c1c1c0c0e040048011661440305007805817000608a200192040d410705006016200014100c2d0810f06030f1700c081850016110703609051604500842d0555498100400321000300792108040784c5008c00c03110070b80342c620258481205e9580c0c0040350510142198000080d100c035201030040c5542b2110700245410702e2906140307000034011001c262072440c1064404d5003c0c02a000031a10780e00e00400c085c440b910704205030360f000a05610802030099002d18000120350003080500c0904500740c120340b0b40701341044000100080e54070303915180416031512841600507540351107141103505a40c15140030700303d58000c559400340900550140b0981c404000e204c003040f03240f270000c0c4002040b4030b003465581000c1e180d402d00d00012a815030104070950020031041c41744010001c00c5541d03c003483c1c07900c0c1214103003409050780104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 233359631 1250 233358381 233358383
    0x4080409020f041712120c0d05090c01021c0507081303051504140712030e040906020c0709060b0a050405011b0b040b150a14102d09090204060504150c 66
    0x140c07020a1402142041c0c0e0054425141c00c1c0320000d51582e9010b403010b9481101a901001c028400c204000d1442d10ba401d51540114540341c40b01d080180510019003944c404840c1e00046a10030101c00d035240d80e0420881da10786464203030ba0410b80b0501407004189214401e40513250803030000d200159000e005607108001c64101c000d495403d1300c40d468441e2450000d071800d4032401c20b021000180d0100c0810390000311041c2038141c0d000025155000e0b51503030800300705194403640d21106400400d049000521602502c0380c05056480d0501e102c4800f203c029410412807644e00380000c14140d0340007021a02505ca01f42028074000300c9001c2514000c015040c0c000707100610980900042080b020400b500030010a040c5c4125009072405008030f20781244601e4070709003103015400c0001d050998400b92903280d1450000380e4140c0321100c1c501d068103e5000410080508146004030307660040b0540d0103880141c01c25172030b0a28001006146000d14011100c940d603c1d03200e01004140030b08610f003515 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 233360881 1250 233359631 233359649
    0x705030703030201020309060a05010819021903110a06171506250b0a0b0d0201030c0203070b011205060106050f09060f07060f060f0906120b041106040905100f0b12040804 75
    0xd034580c0750080c041e400070f40340103d20340f00b82c0000c984146030501406044e122058010b020b584022103880c24808850303407040c0d1304920040034000070720501041240145000e0001d0f001e01c50214000d0040078000c3c0c3d0301c09803c11500c020300f0281200640411034019141c0d001d0340840074150000180301f480342031181c0038441400312005c10740560502d0940000c0e8004c045c0354203107940c0c038440f500c251204807500300d5000190300c1c01c1800648c0694492081c1000e24070440c0e06001c150707a03c5010380c00c1e080c0c008800e44800300710708500f0001c1c1084550b01604280ca80541040d144050081440c010045014458440442c414031035001e45c0c0305907030651350004000d116050400c1604001404607000d10200443d00c0d603804100d200c003a0003820304a4600d40d20b407882901990312580003401003d8002c4a0510b6a0700ca0003c0b1070f6a104050300141010480c0002c55003040d100c44100150742e80e001490442d24280208200703075030001543c035040001003007044541d0f19440d007a41d40d0300c1960800d10305 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 233362131 1250 233360881 233360893
    0x1518070f0c0203061317272209080c07061d040b0d080703260403020706020c010203040b030a020c1203070908060f0a1e020c01060f0f050a051002070909030e0f09042102070503 77
    0x3141580400b12182c4040101c00c0d030b47c103441c2c0090012801c10380c41054034500079400107160f401075581c00222810b0007800003c2c00d00c5140303998641841c000b9072200c8001000c2041004c0310400d521100703413892000300c9082108102180200340303020844d5a014013030307101c04140748050500480d000301508142491072061400c9100d42c01e0710344034043c0c4040d40180325903400407500c0c80c0001007112a40310143c00550038545000e03459180b0790300051280c540d5907000d118090149400b0483d4030309803144500d0598403803810204c010000181c40d881000254852424460b41c4014148100d4101e0741352032011814a0000c1c0305082d140c200b003c1c103843d96a100045206090006602c0078056502a14030660803660b901010603026049000e4194030000c2030808018900d851140c02400d01000d005803000d19070356081c0c00003100d60201094000c200180c4034100d003460b00036810200404111440c00950405884400702d015000c651821200c1100c80d4100509000b044248001e0200a0403168 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 233363381 1250 233362131 233362147
    0x312091f121404030f020105041e02010c060504050601061b0210030e030909010f15050c0d2003030a090b0c0a0c02040b01300506060c10051518070f0c0203061317 71
    0x42d000c1030458080e0001914145000740d0fa41c4107018403030180d034001700c00501c113040c44c1c1800c40514603941f004a040c00507074969600010501c1c02035501c41e50045020b480d9642c54070201030652021003001c03401000f02c4100b481c0044e560114800d1090440749000030318110100360241c5144201040558010031000000604542c00d00a405c26100140c0e003851004601a07401e039528024190002d07510741082c8041040c0368424282400341e044001e0b948551040440031107402d5a1080c2d40e1254107649480741ea1007401140d5020071b0b00f0000c0382c0d03880c925201c100c4000904c924080d20000b44030303503246e4030f5456060380721380d00c03402405400c405015030748003081c0400058402c414101194150034080024124900301080c0c0301122a204c015000741f00122501c500207040061030300300d28519a04420741c0703e0312412541c4a80c0c03c0000301c5a1031904092070043e0401c25503240c0901001305c51005400140c07408034449030070a40043e90201e49144502d030414058003551480b1400400c0851625 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 233364631 1250 233363381 233363411
    0x4050303130602120c21070b01091a0603010b032e06030902130e030a0f12050106030902090a05071209020307050409030224010b071e0602180312091f12 67
    0x1c88909030200d03021314080040c1002c0a001390302e440c605982142000448800480034071402103c200003000d4034100700c9603204101d222081c0c01882040c1d0b52507040e8840d900c00c00d640d600790041e0072a003d508661404070038980d18400140516950160a21070035121101000d000395202010340c1620800358454000a009001c603610513441068250544403503000d4074495a804540c06c800554545040c09400350703504c5d18400b940904102c000c41514418070360034810640038202c1940c1c0414624200c2c010080c030703c034020306030800082c0f5100601a545401071840301c0300c119a00f40103da1000d040c0000307030410b1140e9000c07079001818005410101540031801d05a01d81d440c00c0d404403400051362a040c200c0c0b06c01d019540320458100004400308203405034190301c50030800d02981d15001c0700c0d1794000903604102e9110600740919002c01c4036a00d01403100030030344460069041c0c01e0080c080c00285401280110340a0021059552210050f204030b10762a030f1141812001d003d14002c6080038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 233365881 1250 233364631 233364667
    0x114030c060f0703120516110325060f0e190602040807060801030b0f07020c0906040b0d0819020a0c060c031803080306101701090b0f040f0b190303140d0204050303 72
    0x40300060038040111038011711a10515000399042c070b144402c010b252040980c0e04001100c445d11203072009011030381d011801d2540c8503005501104900d0000d40b490324066050300d20710550b509180f0704024145038513800c00240e110320807103148205044c0329902c1c28202e00912650308070b440b20380500721b008a09030360023420070f904883c07054802c01030b5680c50074646400a58152040001030700305107201d109528208104980000700144005941080900010422401000304441804c4049100300382c05054a4441710b106c2c20600150000d1100350782e0f803401e800c000380680c2003841451181a41072602c41c100c40044120000510110030f0380b03900304003580b50812a0b04030300c41c06000f0f03104d62619100b058207460f0b0305032545041101d40d003000003000c06882c00e40c21154201201c0f110030040c0f581c4070b001d2210220741461002030800d17880024424800306403080f149040c0503401041001075031241425013030564500766940c0302d4130b815a12401a2003103a026503854400401c03201c24500e0310140c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 233367131 1250 233365881 233365883
    0xe04020d1b091a0306060702120f060a230103020910050303030405030711060a211113030c0b071709010e0a080102030a050709050f04020f091c0309090501030b0114030c060f07 77
    0x40b911280d90b0f039400101021040180c0c52000d000610114a0506051000d0229144000c0c12400c056280c000da40c0d1500380a801003805aa1240d000e220350f500f103900c1740200c2c1d00802050302c44180052042045c03180f40611000b070054030320f03c0009404c201e107050240b01500009003502e640342014244581e481d0800d5405503005800780d40c540c0004c2c542107088601d20342c00c80e1110002e409048440003003000400d0401030009840720100c510301803202c03008100b5404c003841d02c074442c01c0c00d60504110140b00d03500643c140714020485840407880e41c036404440c54105143c0156a124003d00403244041850f01054010503404404a46088190055071080045030700401081d0350b0390030102d48800461040030307044000b00c1407083c1c460909800030082c3c0603c140c1c989103001c841c01e0104001d80c100c50ac66044256030445000c080692110103030000b0121000e0500c1154116101c541d00300030184120b640b03003241211903400d282c40178004185064402495036489200b95080784071541e00c0a03170 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 233368381 1250 233367131 233367137
    0xd050a110309010903081308100e060a0212060603070903020907050a1814060c1603050717150105010e010c0c0f05130603120819020d060e07031b0e04020d1b 69
    0x15508440c1400002c2d00d4141030140c0d103c2e8141403440e22904010b50140000e890051080c240114003110108441116586d00680006880529100c2d0505000740980250300c05d500410840c2440c101c441d54540d0040d1044070101c0c0e1b0313501c406c04140c2d4007000c6644000c0d00428245c0800000541060103000d991103e601d8038240c10604542c104402221401440c2c240d03078501c0c1101c0c0306070805001070803c08520808481264124844803c040540b80e4802c68156004110030302c00110341a2551009a100074000c00c200c500b00004240340300014020315041199040301c40080c3ea11540101d0141500141c51701c0300c06445404981c5e8682d601c0c012a07001c0c4804c8985208115203d101d03010450340c000f0040c2d041100001012190124050140002e2521090b00001c0c5200e00b480144001004810001a041c0c5098040404017200800c0e10040c186488440600034a02c1c0d96402544821440c1441c2400b18840c00180280261a038000c50b00d480c0050046120201c00510810100304d80c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 233369631 1250 233368381 233368397
    0x608060f0103112419020d09060807030e03031005011403100e0c0d230702070b0418290f01030209100c050f0a1a0604090305040612021c1d0706020c09090a050d050a 72
    0x160140d903182a08554400040c01000081200c14400c03609a40c006030bc81c0b801180300700000300c50034a55002950344032528810700340300300700540c1c01100e0a2510f800e0961101d0071880c044e00c000e09103803040d00c02d0a0301d0000000000301100c0955085468004032980c04010740000c11f000000c510080442c880c01341c0440c9000719588a00009204040303c094060403032500b42044446001108250520024291200c4154001e44c1c40f10781c0e020380c1034540710350401200050074108000528503003522414507204204440071510746003a690303900052400c0c035018144040c44e066240607441030000d54240100b042d100c0400480c45100341d032410540e0400d44194803000e041104646c0c103000b0013004580c1c10013041040c1030148012004140741c0c041d006080c86900029114460008100d01014560b030b2041540c07002d160300005903201034500c0003002414180781c006951004103400d25440343c80000000340707518108200303400f0076907401003e40d60184c803002da01803e580c11580304040490130340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 233370881 1250 233369631 233369677
    0x1505031504051b1303050303280207080702010c050a0b1602010506040c080103020907180f090c09030c090906060906060504170d0206220516090608060f01031124 71
    0x1034080c641c01040007031001402c1d0000c5400c02d0b20684d01071300c034000c9140c555040010110340d09002862250742030303100d00309894811940b040ba9004095070304140320391041c0003c0011900480668030511307420b003000c01204640e824007620b00100244000c05800d100c03820400994024520340507288000c0c0c0007032203a44c072560300704001d5403c001e0340c0d003000a222400420140c9003101d802500300186040c06c1306003441c014035408251540350414480243c41420400600006200d002c400300142d00e0000032585c190340d50300048150622580409076154450042808401e900030340080c8106842040190782c2e03124042c200f500a446068000c54808001240550001c40c0c49002d0b41c810382e0242a4503550320310b50701c08201c011180c6595000d80765400b1301c0090030400c680d207813500c011020600300600d000309803420340b0440d80040c5d02c16003003a4180160404501055415694040224003050840c1004038980004d0841c0c079541d4502d5503014511003c5500c4002c040807004102406506680 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 233372131 1250 233370881 233370889
    0xe0106050901120b04030c050f0c0906181503010b0406080c0a0b0403050703080721020106170109170c1f050601030f090f0b07031b0203220e0103150615050315 70
    0x100f4462031411071590a0504006081003128a50003886803e0505c0c0d60100ea48400e8980703404a5901445a4041800c00401d850000c80d400c1e8030080482d006451004c03d0f056034216003201414540720924a151482c0783d0ba5000e402c00519082d0203403042001c59621007090f0340e00c540301010745006001503800071030300b14541e400311420380b0382140003001918075503038a0b0030096011660a983c403413031600040e01c004c10300c0e10000030030910310350004c1201030402c4e1107000401c5030b8a511003844ea1400d22408001060b0f4501800c0c1225041c0b482d0303444688824086081c031406d040d24a45107101c1f0140c090441003c3c0e8400c03402418207a900f004600000d00c00c000444211003005030401001840703120000f188500210761100081c0b070082070013588294801d81c0d031840c210000c1d01580010821010405680055410019042c18001d000d10314142081c4a8040d040c04094020310031a0b101c40505141c90f000540141a001c1240c12160742980c2e00a125030010741d50113081d61009081413002c2d00e8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 233373381 1250 233372131 233372149
    0x24050109050703150b0a03060308040e04060506012c0a1a0a0201060501020c0d060209040b0603010b09180709030305072d1505190f0e0703060207031b03120905031306030e010605 78
    0x4130078601c004050f081000c104029004281035074205916007501000003500a400b0700001d003500b842c10442410103180c000261400200014100104400f03129003180040d00306c0c0140f0740900401d04855880003010074025855500000071064084040c0311030700310908003e042d0300e295940204401510b0720012038450b5113442e00950b1204c030200b410000b2824590052580c42c10090000071402c03002e0b40420070301d420907841101401c82c040b42100e5039040140d1009801c103140c103c18a201c0c600410050420055030101504010000c94810200410701d210396940c0031140c081d028110028548884100499500032500e104915501010481c1035002d41c900964010340070105a103a2604030a000388242c1030001d1855403038182d052072110060010102075406158050303925045418050507140400c00d900b1114440100d000020030740c4000c0420340c090780141d001c500c2ca1b8007800c0c00c030b00d075009120403c85940b0a600d00020429050b030b00040343c0b1081e0070002e124140d51030b005c110740c002c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 233374631 1250 233373381 233373401
    0xf0b152a073003110307050a03053103060b0d06090b060a0b0c1b04060b070f0b06030601030510090c1509080f0c03060606070804080604030512060904120c24050109050703 75
    0x1032000e42e032540000b4042e03004030100344008400ca03402c204440e01c0d80ba00e0803c0900b000e50100b0400503a11070003401040d031003030580200e41c05018912080c180c0c2d040904c18144009440d680d51400195040d6a60b05040c40105d41c1044090040d0b0449007400307541c01d070050380c04a100f90210034000801d00644420345614a501d00c02900c0d03803006100800d02003200045c002540191703241e4000c103003002023901812149000d00040d028509961800101c1941c4c0a000d6510942c0074900400004034002096405c01140d500302041c80201c500d010390f4090341c150050401d11070800116802c00b0b0744201c0c840b00b2991070b0380440d080c5441c008222a155a000f484940d010b0b00003100142c0141841d0000704001ca00c0350302e6a5140940d6030000e0f6040900c2594110009080011096441403001e50701030781111040303425000c40e051540d1003501c926440842a41485000640081889004040c42e103801800040d0080e500018514403c0184801d00603450307030314502004501c00318400d10400c0104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 233375881 1250 233374631 233374709
    0x5090403050712090b070501021e04081c0c0204020d0504061109010e1c0c060206150405010e01091a120d170403080615090a060e01030f0b152a07 64
    0x200300d03480305141603d034803000c0018820540300009100c105070004000440c0110001a1503080400c10706c2000d62030103071203190b003590130300040c081504045051a83c40c0d0170101c0c001d0002070006023350320314180b40d0010b58020700c0820081c00c0c0503030607081944294450207040005182c0071640c001c16005416130b0500041090010704c04604000d00c540d81c3d0060400000c480340100c90782c402034001d40301e401c16801600300c00c0600110a0500410990601003100d081c4030540c1462900f84101d02c05115900e46c1544803004000000e40190020101740000380890003030403400300c1c006568100140403c030000d0500003c4048882e050644030b03005903450b95690085494031010080102a080d0107800482e00c10030a1a85c1b541e100c1102d44000e04581e2a414000c6136504000b408542242c00044241030400102c3d4485a40d0310844030080701c413601d10241c07201884c2c0a03100169207128101500b00400d00d01c12084500001118070480f40c1c3c15a201d0722648110b60198001c03100d41e684400c0c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 233377131 1250 233375881 233375887
    0x9070914010c0201051c1b021507050a1110061409090a02041d0d0c02040c080f07030c0c0203120706060605160f06111c060503030f1902012307090509040305 69
    0x1962141950b1091a80145010b07030501d10030000700b0402c000411a800449070780c038070200780862a0310f03850340a026030b107001601040402c90902041701030014040c900300100001c0c0b40700c10b0750003010032110400f400d0017245d190441c5003c8d544010b2015009182c560306d41c8500d1403025103012a00e0070300c640000030141000080c07a50030f01000d01520f500000c0c075016640c1885c1c200c15800c100c901000e80447d6101038260100e0b005000032a5071581c0620104502d650400452101101c3c4060308942c3c245030015210940850884035507092880080d03041c05003642071129032034801c1c050101c440c0110410071406950703e400b80c3d01032041c14141d03003c040545c1d10450104a603050800882d0340a00404031303100c04591070354440340e03001e07071030300785026110502c00310044d503562082401a0009030020341c80c00030307440b055002c0c6010703a40c01c14100301c0103103150414086c803e412012210005180e03000403252032440d00007072904121103450004a09020003d064501040c405000300c0e0951202c2c0e10f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 233378381 1250 233377131 233377169
    0x1503050a0b2703041508060f010f020124050a05060a2003040302090a0e160501050f0d0f0507020d020114041a0a060503030d020403031403100e07030f021602090709 72
    0x4000c2074014022641440a422042c00484441c0700020340d00d00240061a950303800c02c020307070039008070b40c0d07070a00104840c503002c1292075250141c400d40c4034002402c01c0200000050b0049000d0048505c1c0d542042060b07005c0d820103001480c1c522000d80d40100c5044042d1515075040c0400b901a41104030006449546d5014288008101b0815440460410f80c3d24150f103e40100300e1800d4280d40f00c036202a50317542d00c1d822030a803c2c06401e40c5081924011031020b0b01d0140001c1c582c0c026000c0b54600c10390005188061460180c2c040c0686009c980001c0c0302c0b0f0b14083c80041e4440540800c41c2c00594281039615120f4411b810040344141ea115545500d1403e2510200001703402c000e1400c5c0c662941c4060218003964104042d0281a500d282e003d43c1e52811868020300c1c010410b0324040941c5418014000062106010341e019507c144040d0401562803100c110050302c050f0070034071000c901c00601c04600040322122040321070300a89110000d9140c0c081d0484031101207115155041708400f00d020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 233379631 1250 233378381 233378393
    0xa090b0f060a09120609051b1905031002180d0f021017040f110a0b0301170a11060307090f0e0106030c1d04051e0a0603030f1409010e1302031005041503050a 69
    0x101d07030b00928000401504542c7d03024a0100d040300c0004400180140d54890b42c901034480d580d001d40c018090805d19860301f00480e549079007502000f5040c51300810060310603101301d40e0b0b54001c110000d201610610890812482c04d000684059006100701c6901a801e036021b098564070761022002085800c0e51aa100d01014800501e41101c00100d83c22800f0700301e954401c040c03030283c2082c0e00c001c0c0c4e8951610b02c00d07100508228891440907040714002c20003007030540078038125507441542c07040d54075602c0d8003084034445820b0700440114450b842002c1101142d03401d5550681c1c0c0240c401b0419190300c0003098406020f00844450300219140c2c0d51449400e1a800c502c3e04501c061002c01d01403080c00c509681400c1040720f0304849566651802c00038198800d10780801c5176964106040b003a0800440400d041c4074207035140e414030280401e04003140d21800e42814628566000440d200e007494801d0b50540413aa1099511890030041511840c09960f05241e04480d803240007042841c92a40e541 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 233380881 1250 233379631 233379659
    0x5090d1e0f090305011b0e01020c030604020603060d0c03081908010803030a0e011e0f0f05010b0d0c0e06070803041103060907090e07080106080703050714100305040f020a090b0f060a09 81
    0x4a002c100580d070002000610901550720a9400b009020340c4200c01110018040c1c84043c201604550105600050b0f40d1000708205030026015104142d40399100b030042810302100340c90090a03103031210300000c1405424400341c41301d1094080d05512540c1d500200b12403019081c020409030350170800205038a000c1d030342d008200403001c1e00004101640001c5003242c809400e84510035480351107180d414002d07030303040c8038030364442400490402095040c2050100745004043d2207042c902c1d6210701103407145014009148404000810340369450b1120724060142e500255000c980d180c1030501744a81c40d14010400b5881969000c0041c40e030f4078600600301c0003070500d401010500f4040c1804c085121300007070040d08085c5c01d0b042d00426640e4911720707209140c104254040986c0854510000d4040d540303600c010b918006591401040302d85860504005400c442a0000e511400f040000110b204442c1c10600d0f020394100c681c100702090304414040701d4030820286500050000340b090203412400c00c04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 233382131 1250 233380881 233380907
    0x612020703080f04210e0a09020a02120a0915030b0316050102030a0309020a12240207030c03050f09210706020a0b1f0801020424020d0e0402160506010905090d1e 71
    0xb260500e8600607868a550405e440d034200001d60202c000303c002c7c0c18070351685401048203032000c514203c40c200000b92181988403070400819400240d95400700d00c030b002084042d041c07280011110b03190b9400c018004020b850a11070080c001c2c100d00c44401649907503814211041038014500c0c02c0407094080300103014485c82281d22401010f80807030b800350403030052142e15100d403250403e10b070440c0381a02d04590103490301030000f074010050743c800a035001e890340320541c0e41402d049848200c0d10b030305042c3c40d010385107043e504107501051411042540d83d040590001040050310461600d0b880102d894440484015100d2138154001c9440b036418800d01c1d43c000c0c2c0021016400068407454010b00303a0780301d5031200d01c9060f40102d20092000da45458010f210540f40003c00d442d04d402e0300007802e030b620700c50501840780d9800700380c03c80015154103009500c594050240c518968540004d175004000941d981c04043c8240a8042d036154004e0740c7d002c194442ca240ca40f0a0704000510440d554502c80d26 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 233383381 1250 233382131 233382143
    0x40c030e1002220905220f02041e02031f0b040605040e071e020601080106060503010e15150c03040801050f0c04030b040302030d06080606030d03060b091903020a06090612020703080f04 81
    0x30480d419640d41090b0100684403000000c2114100400714491b10140c03400d440302800b050312542000101104425900307136030305030b502080000c40403008d849180d51200c1030009440c00003040040c484003055112690035400d0020484850b140c420302850b45c003a40c014440850b10400041c0620410490700e10707800000b914040d1443c0d03200007410448001c00055800143e4004001444099001e01910000c3c04052400038199850260006000d070005025000e0f070003c000032880c040d84071244480c81d00c00f03800d014681c1d80c04688105940d070b58801e00c1484844e5280c10080313802e110540c041d59000e200c2c21406030341444d0440c0c0b1150401880944114151b2008100a040c410400d00031040100b061101818807480c05409045c05c1c407242243c20000c0518001041c0690303100481a204104411b403102800b410507030542d80324440007070304040e5108101440004046038048001001e071480d0740e403020114643c0950060682c040c1300d80090208003802c00081144c2c0c42d41d8542c56200d4000c0b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 233384631 1250 233383381 233383417
    0x5040209120316060606020c1c1406190e010506030a140c150306010e090f18030d06090203012103020604110f091501020d020604050a080a050408010c030902040c030e1002 75
    0x1d08038515070028141a03031031002c1c60010401c0c04964440d20f0014002e03030018001d01000b1900040300d11545100c80d00d01000da207094901408045030349051680f04a20450307400703007072045501e0b98100c0d941915400e481e080082c01009040180119030084201034001c003200c3d4084c0e502e94200c1907007100340034400e10404445003225510003581e081d40c440c000090301d0f56802c25600040402414041b10783c00365403242d00703100403a1004a0400e600c07600b48403d18810408424401d0708500c69080751185642c06c0400c08100d00c0e0141d40154100e038481440e64081402040c0d03440300c07800c190a400b50150704034030300140102710102202920400010160440000e504000a4060f00e098524250007030140000c3c9a00c6c1d40c0401c0030650081d2903000500d50340c40c00c0d940b841d81e80c01e050800105402000300c2c4104007a4040c00690300500041002840b440d0206000140103049034101a84203070b0602040d148694040e10644c031002c100007002c2c01c180c1c002c03440010065802030891a602000c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 233385881 1250 233384631 233384659
    0x3070c05160308071a04030e150f030f0601030e2a120d03050108071202030309040c1107080604020907050c0c0411040f08150f0709030312150806090607030501060905040209 76
    0x10122007002d184505503450b2507070640e0070035140705441459003000d6420705a0130b01002c603400a0804080d40743c02c486a4103d01c100241449080c000c0c800c003008a054007000384002185266a0030344a0002030b80c041203c03074030f060442940c03012a00d542c000a07144400c0e0040b405202540308a003c0301010f0219410030a10000035890850b1b54002c440000c1e641e28014031800005101f0580105032000610080040540009440e4071503004000d129540d0385a5102c040c0c0d005924015a40d1640b0707003a1018542d80d144c420317131140760894040340300304442c80000b5a0039000d0410b8a1040351610b00410b0303c1c16009061000500301e540102c00b84440503c40000c90f00c0f001161440600201c0c1c0240261104590400a0403840034140100c4a0000d108004125510809a0b400c40b9050b240a40303086140115200c020030540303500c200c5054818801064001001034164048d800c120100c40300e503501d005044085600a00030b000020f070a40200700400c1c501600548270030780d002000b2100070628 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 233387131 1250 233385881 233385913
    0x506031219030e0c010f0e0301090206030118110f16020a09050c0a0206150f091905100e06030c0108060f031c080702120301151b020411030a0e070b03070c05 69
    0x1011200c00c595031041c0c00050390641d49400341c0b040d150f10390002028003010044c0013801d201c800c0c074620360400c00500c2c10441b050341e0941006c0041034002c0d188558035610f514401c0042210301202055050a11944000303850b81c100c1220300301c5007501406418260070340d07490001c1c2e40d0b55030b40c01d0743e0081c03146c04041145100303440383d50300501500f4015542d503506030070082d0070480000d0404c15001c081c00005110303030711040b1040c0800c0004444003c003c2da00c106000c0201c0480e1081315400707030710f01401c0203031482203036031110b083c0d600c81c900680803070792201d0405654101c400f284030300044100000c18030324101100111541440101a9150204c1c0152280c50340903034281a20001200f07034042c00186c60701486040300300c0480d203070250f15560500e030950800d80680074074801005400e60003040303602d80c40b580c00b02640394002c1091001d5000403900451641080e0384911900e844d0000100d410400000e01d0800c603201e1051060a65483c00360a0314040c1501d48203032042d02a030b14040c420002e03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 233388381 1250 233387131 233387137
    0x8010b040e0f191b0e120a06050c040b0705010209181005060a120213050a0e1623120105010306080a230102091c05010614030a120302040b07061a01020c06030a05060312 74
    0x100c0c8040101300800f412004001c40c2280310f070305d402100341030291440c1c0c03400405c0300a55203810035400718681d140c01420080c6881103070310081d0a9080412032100300030b07040d0014141003008031010240380d80068009890310201b95031007001c0203030701c500800c868200580900b222554031308100440020800c0030700283c0c1d0141003444001000480244a00d241c400050009009548402031103880d19030f0815071403004400c90310050003c4690840f503001c88000302d20900d640c0c0c0c55551920340c0b4540300c40058080302030007910702090030500049081c032000903604015030b8100010100035540d501c0150134000302e81d00021040c0d50208100c00a07500e48400d0401e07100380d03c0c800001e5231000c03400c0050031100c0c0b5030000100316802911280a6603400150f20080340d0b00046a107200d0902d0b4001900203108681c00a5244200072410b00140400c581c8601c01002c2c107210880c480c8203810004a8440344046956a80880288085031149050754811a4841d50107000c0342d20005142e0f07215421a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 233389631 1250 233388381 233388401
    0x20102160801021209060403020a0f020f0d0b0a1a030703060f02040902071505060406030c050f030f070915080c0a030b15032b0c020105040b07060f060801060608010b040e0f19 77
    0x2a40028507504c10404c9010455403148102002d00070a00786640d0094442c582000064904170001160030250f44d548020041c4c070100c004c3c110b561003800d9141c4660940c100712060850a89415a000006d5055034680e0a180100401a00d905811665050f0040400003035407004075509020101c2d20b403045100a207491401544292114400c106501080ea07800810150099044c01020270008003210840016142c00311220840180c103580402d1915041c04c16205441c4154100022403c1c1c1c80d504c02440303400c02c444003683c070719122100c40755610320600c032668009035003000400100d42d0710a400c0390440c2c1c200e019603d0340c442d607000003440c104601c9400c00c9241c850524000701000a00b5074811812140d08084036402c84c1500080e105000b18130030301741c00e20400504ca070104585940301d6011182030000400c4110380b103024146c0205098007454000c07034800030001c21050944019603003251010b0301c442c0c4942da50500301241c0c41078041c004c0c0ea92001420701e08880e1045c540105041e0b8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 233390881 1250 233389631 233389633
    0x20102040504110705100b090114030c04050412090e1e040804031b05011d010c0b1009110301061814040b0a050d0f060c050c1e0f030d020301080105010f050f0d0201021608 75
    0x159085e06007136041c01b00364440341003414501103d9650507100c03100b565044031140f5100040b252031010110b4101228500100e034064030308003c002c2044007070f4810848600c260307590910b14a031204401a91446e0a5410880c9011500c00322246005508003490388a80b00b108185d00309581c81c0d6403122070b1030b0801114208001c90300f40501003564000d500745d0700070103408002650004e10f48000792074402d17821009422580050300180340001e1403000c2e2001050303174501c1004007040010b1301e0001d640080c000d10001410703448600c0102c170701409000c4280c80a80b001e500c5200c030703001300b0400104059909190090f0310040e0014036907481c0400458294003407010941d20003a181361500466040250707420504c60180648030302050009440060020011040340c0102c06030400d00c1d00e001d010f85c1d03101c1458880060220120b01c82500030b1412108002c0007480795980301c0380600107541341ca00607a5041081004601b00c07030f14042040184007030040c019900d480385d0409498035002d10540000502d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 233392131 1250 233390881 233390887
    0x8040824070e0d0327060201020912070501081f030605010602031801081012060b090117101b050d0b06191103040e1807080d080702011503081902010204050411 70
    0x11000a5550907a000106142c168003000ca04030004034100189440601002443c1c03401840c4034400c00b1080c3c1002000b00d06540e035051303440500034043c0d80b15202c03403030240c1c144440202048000165a10681d0390507140c800b820354a581e05110500d800ca6000304904101040000200300310f48140390103450385501035550303468000640410100520b8405041100402c00c01c84040b2941007210150340300c6569801c58a852801c0c000041d0001e481c0c0d0f00d83c85484d0304000505040b801203490b07500301d4404151070742c10103050844070403100d140e915290608800d01000380c069101d13100a2010006101c8006010400480451901c1d04a0b00318004036101d00500010000e40102c00302a05520712001075150500f011910443c0d1a005007200d008161805180134045200303100c0c00c1c002c0c000b2a021030b100304078040c030000e01c02001038038a440076519140b9640b010040844002e82500d030850103a500d0f000c001e400b4541042510707003121045540c01d01011682e40d94a00800c10080b0070341d040192 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 233393381 1250 233392131 233392183
    0x1415030a1404061d060f0c090307080118020910080d141201060206061203040b041703040306022a0f0604020906040608060c0c060108060112060c030b120145080408 72
    0x4da1803a510041c003500e644591700304000d410b9865410b41d8440c0d4015015900d9411100120b17291541c107401000030355007807070301807840c40741d406408808881c0211525031803034a5900d822520000d6a010b01c0f0280d410038070649031400e004940b582001c0d80c01e140601c2c501a01082298000c413003e0300300301b00603000802846036614110784610064100c0c180a18030b00391403c040b0300b040f8410b83c400c1c012030a540c2d0003187c2110500b40103035001150801415540d4030078116104117508407581040c414901402c41c030540f803a1002440c1d1031580d1154000701115281e5400b0840210030060009074002d481e05404140c808007805084e0280c81c0f002080303601c55510401190426005812103038995020700700401c099401201c41c078074000c3c1c100c000001c20368800c08003100a0039504041a8002c68058202e4141100550140c51050307450790300745451103809040000211540140f40300d2200c000440701c002180c1926054038200d00c100405480c11b03580e103515908000c2040794014418084000f458 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 233394631 1250 233393381 233393411
    0x141006090c03060608060906040e03030702070f0e0919060b0a0b09040c020f0718020405091504060509072a0506040309030b01080a1205181201020a091415030a140406 73
    0x49204040d800c043c01418100f400040620000802d03207803141c00204082850f544441d48a40040b549038000e40b980c0380b9040401a55524141c440c503500348100c1000003c904000980d403500174400c0301c0280c00d0300c920404001038444020700040d038060b55541c008202e5680d4243c1200010590200c0c820340318440c000c2008100d0341038020250554100980c48032050101089200545103940407400c090f802c107081640c000d00490300502c0d0042c99420030300a0b200841d2040b544019001c8038140442e984507801d204000740161a058007244500070b181506650310280c4185040704401040e84001403900c4151822a00380d9041e00400c1005d5818814480f030784080b14017503c03004000b4805642c09940d40c906401c05980380004001c400b24090300f900c09040342031104204020035903101e00701e502854a000754003c3d0f00740008510030001c00116808140645401d0000c000d064900c0d1503022160042154401004590b10b103640d143d082e482c010b9041381c070384d00643c0180d0000034604241c03e040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 233395881 1250 233394631 233394641
    0x906080c090f040210080408070f0c290405010c062306120703030507120309020a031415090309060304080d021903060602030306090402010e0d050a050d030c110a0f14100609 76
    0x81c0c81081d20030200005170300d401c050050440c1203032030b0082e025500c42c200300105004000000b401103050040318014820340203d05000e0351548200e034503807640b1b108004d60007403181d01e03050500d02c2c9050108000e158050300042110328080c0201254541001c4004244111810300b109039141c50342c000d200c42c40c03e203c9070007032000c0c45943c01001c401e03085880160160044c1d00c001041d0641c01d481070b1150038413a4200e4044140c0c09029038500d2922890445840e00300c400000c0d007a0300c5030080c88902d0a07249c0f00114050164200558980b80b25441401003540c00204141d8150b5001c005010b08a5820302c001e10803c0101c510154581d00502801015107082d070380007004550052060011581d1001c82c19600aa424207040342c4042c005e402041e501800424050304500800d5408030a1003000302d040c0300c590115035400c000c3d00c0580d04080e1000800004a481e07154002c0c444e102c0010601c541c58281240111801c0c8400741c06941500d150a5600040e000426101c0c20b0400c0741d40b90030700403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 233397131 1250 233395881 233395891
    0x306060513271b2a02130e37151d011d060603030f0d0f0f09050c0f010306050f090c07140a0b100f09050604060906080c09 54
    0x1624194001076400c5018440e40101c00400441600792a9070b1604100441c80c2c0350a01e503024844800c11900d01e8005000c0d503d10f8501046080d48216044110702d000c4000e000040c11010b9245241a001d00c210115080518082e2942d21240c089101c0070030418100a611100c0c0c030b2000700102c02c0d840412008a0400354080c0d0b15120070401d0002d83d0006580c02d2915050078005004101810f483d000780c6100070b015501946410b000b66183e40b401c281003074001c3c4400d8115038050301c8440c18580d40388075072800111110428007044091030b036035400c481c401c881980300c040b480c0301c00d600404040b20505002210700c1c6e409002a0345180c10210000402030509090400600d494100440d40000184407024800c442003800200c844500700e05132692aa0400803a00d008a001e41c402d170360720b4550100030b0710380d8000c110004401d0b20780030704414103032500e00e80310b0314076503180c0305803c80604030103042c090344661510404a00700686102c0c000c02840c00314010004000c0190034404184400341c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 233398381 1250 233397131 233397137
    0x80109122a02060705070906061214070e0909010905030a0507030305060a05031e031201080c0a09050702100c023c1902010e01050c0109080301030b090f0a0b0601030e030c030406030606 81
    0x12260010070080c40d50712044680560f0069a110304d01d107002c07420f14516403c041c14242c9800000704034103910444002c17090102c008100015131031600111000a8115103410014100d08081101c3e0b0800980c0d464101021400104070200d0a654460458209401b61380000e080403800400b0f040d0315000d030680050303040d13440041090529010944914480c3d64070401800009030101802e1070400807204055411005500c482d6110070351592140c008035040b6200383c440403000300c1d0305007003449402c0c0500201e400a16502864061688c040c01c901076110b404e502a1f2081c4414014070403a41d80c1e11441102c0c0f8241c010840c3c10300070b0201503100c01070b9918030750007942c00300e07500340c4020301030a25150242040d0f00280312a0004035101c0c0715450000440b9424080c04004000450700034506176441120031340300507610317a00c0403a580c4621204049455012102c2540421442880550800011315020602101e0711814038174580c4000c80740d403020343c030006040140715413600c00e800103092186 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 233399631 1250 233398381 233398427
    0x308120f040c0e15030f0106030203010c081302131407030b03250b033112050f0d20040f08070803120109020a09030b1e0a0b10120608010912 62
    0x144070202c0c040018000c0c001080e0001002c1469480003900c3d07140c0d203000060454485e41c2030210a00d01801043c8403c90280d82004d407007904d0740d4090095607219420500d42054180b82540800090000502c03006244940e02d0028a0401324a0340200d8490f80c15504d022483e041c00405040c5001101070840e45c0002e18500e4003044c1e201c580000c04102c405c0011282d46a840d200041e400d9020900805d10310720224681c4507440c00030311020540d441d401900786850340350080909817018800c09410f050100400c10405420b00c5071940400406400f50001d114004862010004250300ca600103d440d840f000c0d20410120a04000a5000d00340500180d0705041414815540f00c40042c0102c0203900e801103801c0c0740f81c0c2d20810450f00216003140c00800d035030911140c6805440308086101d40c03130501c1e600c001105020309016100101d24041c2c1b03045021401e00508581c0f40c03150004890310079488000c0040c04003424050b081c0c100d40102808400500d40300009403281c120b042d0211602c400171 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 233400881 1250 233399631 233399633
    0x2010b010c020d060e160303021207022b0c081e150f07050706020d020d15030c05041a0d0b010513060f060e0d0c0f082107030e0303070b010308120f04 66
    0xa041600420b5040d10202101c0c9010b28100018040b9009280f440344140c4c5440030403410f503c107090301100d003c1e4081c0c42445d030001c00440c04034440c10134081d404ca42c40045400c00b0010300340c0b003142c0300c031b0825003c841c0042003660f80301d101c900d095100c20303180d5011420416030300c1121000e000c4030740890401004104501440d103808008000d00a40901e800400018008c1d03000d0811528172030380c006400c540e131fa40d452080340c000350070189000d00b21600e4840e0105040541016140999812100300e00c4010702e402d04010203000c080960920038540c641c0800c8094550001c0300204512540704115150304000900c2501070328803104c40b03d69401c2145c01c1061f80e40d503c0914040ea6464071380f41c0c03c0c1c00c800a000c40e0a82402040c01044000d0300f22001407105c07804803ca8090f00c082c0d00c00c4e10702d40361007541d4045c0c0c00070081e06075141c0580d0030081e0b840080d0041203090728000005e02604e00341012074031114140e200903401075a00d01c20010701814140d10880e449079020f50181c03449010381c185 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 233402131 1250 233400881 233400887
    0x3080f070221090a0e0114040203070219060f050711070314030d0204181103041e03110f0a0212030708040b2203060b04050a0203010b0a03050403020c032409030903030f07081903021902010b01 84
    0x1f1056605004a5000000c520007500c00c3c09401040062100201081c006e5803401c0001880e2101d0b5100a503460080400d801601c9141074042000f41e14000b40192800d6495880b03003180e610302d0341900f51004221500036a40c0900180c801885910f00c1451900301e04070716482036540b0a0703015040d9a004204020006940d500c040012103c0e100039100c0c807146078513058800614192020100f48a28500c2d00704501000502003445442610903503a2419001c00d2541e80c0c0c003850100401d1048140802d2101c0d0b070b2900c000e0501210514040154801c1d01d90101c064103c0380c0d003041e240a070300e80807020f10908080c0907240d0000383c0364004500e10340c036120300290780b40203404141e010141c0701c8000c6424103108114040b101c0c0c00007429940d503d001c4084c2640c20100b44212850715a0050b400a0f455000210a455034007102501441c17510300800d015444951102508071820101842500c0306402c00d9004894000c109450060b43d480e100d0351540f07440c04401c0001d030110780c14000c00203c40e980c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 233403381 1250 233402131 233402159
    0x62b140115060917070b040e15010809070e090a022e1403040209060d06020d0606021006150807030608030d020702040f0627021204081306020a03080f070221090a0e01 73
    0x1d28200d103002800a900b58042c05c0c81c0c00c0b940710a50400340400c02003802c800c2d016020b8042c00c0440804070f07141c84500015600104100c1d004022070b00302d5002048030b01903081a966002e003405050701c0b2031420a034000340000071361005034000481100d592034003403000d00b14a01c04140380c034105044074145140c2c120605e0300c07000300000c0c042c0700d070940810b41ca602c4005195075450b5008005540302c5c0070590b10200203041070f201e85001407058501c01c40c580d44141c0318117030594051507a65403020054507400d9039103100c040c0000081641e0380000003080e80050000c0d120720722081c0d0001da503a94450041005903000010480c1d01c840c98010304001c00e40e00300c0c11804110b51a40714503940c121455020100078080d8a00d0f1402c221130301d40401c001c0050520081c03200c408842003102090f6250fa00490380c4a158513002404142800040741c0d904810110065004041d0b20441e404ea60254020140c140c42c6d0500078843c5d8130000c540f0f0390031840c0400504000e0400310a2820440d0314068201c50100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 233404631 1250 233403381 233403389
    0x30816050c03031b07150c12050103050c121e010b0108010611060610030e07030b0106030e0304230a080f160911090d1a0c0301090f020f03062b1401150609 68
    0x1070761180141060050f0030165100f090b04249001a144000f1b42d820025000300d4951400040040100b621078440038810641a00d811000030b280c118000d43c1804102074a500243c04244501650200811824020340072400440300002c0b030b07011800170026045960603005441803200100fa0380007582400150a90b0040302195070440e480c4284600b940103000107d003402050007000d502106000103614014101c4259070380410444a400038615241c0c000c031702074011000c80d8a11010424803144120b586801001050300c80d01c0c030f51f501d80032440c0c0800100702030340307642103100325488440c52162420b0060014030801d000e06260140304243d544a04000b1078820b00c184090328050102e0313142c400300910007000f280b003c0c500f00580c040e9841d810910a10702020304201188141e42000d00030b41d00c00700340384030311242035445400401001d07018a0300c12034000b54510a2101d05951706840c01407540d4000c40c20510900302e1564040e080d13595034036044d503600c440d42c4410405241d00c910448121 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 233405881 1250 233404631 233404651
    0x1202030303160509040e0609070f030209070c15050114010806030303090d0c0c0905180106080a0b0a1a04050a0c0201051503060105120c0a060e0102160515070203010612030816050c0303 81
    0x79006412040e183c1e0b006008000303030004c0c6411880008500700140710307401401d000f802ca81315aa6100c01260b014403c42c04000c0d041100040443c00d02c0b03015801a920301d81c45802e042c50340c00c00345c0740d42c03200300c4000342d11400006000410030001c0f135030810071154100d8000d50243d4614030300010182e560301011084030b8100305800920005000003610b45001a1a0060b4180940c0c00e00c05510160707031364460394501c1c6135442c1c00c1c40040c95050000740c0c201c005a000d100081e960340d48810002c014000b0307074200c1504100b0560800c0041c3c2c3c80b80b06882c81400c8092000602c0301018000030700311040280008400031b00c1b100002c180b55030000e011030450300102c80c603001e0344c15003101d03460600d109008813940000380c920000c264036811110810404c002a400c440eaa0701920342d218102c0403580c4101d942204a06508068000440004141c0c850014002040003641d07000c80d0544030042c900260b0018070005c0c240403044088651058409009150441c188106440c01c03d07260300c000340c018041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 233407131 1250 233405881 233405911
    0x31a07080f06090112020d0c1d070203070c060806030313030804140307120b042303030f1f180608070e0a06060c170706090807062018060702010e090112030201061202030303 76
    0x1b1580c50034449500c160b44010b100314480d6030342424120109000f0a01403141151000150f140d034800000d60340301580240d07030074400c0c0303107442400d03140700700c010b02001c1d054002001101c4100c5d03c4000400c000f0b600c81c060b00c550720b13071824036181010750b00c510004c0d129402c5075104000d800100c8042c0080160005070030001525a0702d0f2586229038981600c114060707066180d40003605021018504c5403401c0c0d0f08544460351340380146102600c542d10020040f29014905200580529503540e00c41c0741480400100c0c1d6898903511450441309034045246925070324100180840540100c00c000d1204e0304103030707001c4040f6688800700c451104801000c02030001c114070b414441150450300d1a04c1e0492121540c5101509250014080307101c142c1c030b181f0028102e05030580004608072442c22480804850000c8940400c100582e80100e406070b040100ca440000c3d050740d1401e2080740205164142c03031805450514000e425103440b607014166007442d088224025803030210403030794446484800b01e5031b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 233408381 1250 233407131 233407133
    0x1806090e150402091f0807030b0d0b0718140a0605030408070807060b060a080a05060a140111161d0c0f0301030b13050d110606030a050304060f020304031a07080f06090112 75
    0x78000c0e0b803181390f03006030885490220a000f05181c5030f2444120f40d503d0710980c0c0d40f000141e05036159150a00c2e04514041ea50401042d0f0740c0c0b151682200e51480c0c000d14841d4801804401e0407070a80058000c40c80b0039403480000e1410200540c01042e442c02c2031402d601d02a02c50840a0260400140114074000b601d0810098580d0101100c0c0d070000f450301c0d88621418100611104086030389080c618038000c041a01d030b240c11030b643d40848980304d145aa13030368400701c01111000c0305903002d40d48a00c5007500c880c403952000c0320140d01a005055031900340342461045140122400340c00c3c025000800c001d10300045480808403030540b034001117551115195184082d0401e00d110794050a00d0040044080e52a0b41c0100001c1041691008403030039511039004040e01c1e41c0c4a040d000340545e004000800909002c6c00c400c0e00100c06c84d00540f802c2c02da8035210a002c521003070000043d1969214104051160408111034020007a50b00072500d518100010600c1000c06005200e00c0c0211024400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 233409631 1250 233408381 233408389
    0x2060c1305030a03210b03060c07080405091509010e010b030621100501150306050f010f09030507062303130b060a240206090604050309090c0909071806090e15 70
    0x30004041c054100c810140c00d50a0090441c415003079104507160042c040300b001d20b03290f4003c0d503a0b00300c00100540907070b031110200c0d0a46a403082d10b0032507400c603062100141c1d50391041c2d041e0303210b11107580703141c910903841c0d004228040c08140c0000e144a104900180b2070690700109a83d8482d005407201d00b00869000c00104500d4001c2100301c64622854403050356403c1a504001c0c102c424001182040c1c2c80c000d0300070b5041c0c8070740c2e0060765007080c03006440d6001d82d0b10426010300c8850b05401d00070180c2d9200d40382d20f400d001450300074a011030004444c3c2202c00000d5001c4d010100001c161590450a001c40320b24003c00300100041d1514014101040a5654043d0390300300401400c120b402c3d40f0310b880c0100500c0405814015005809a400046c240900228004d482170758414059480c000028041201044c4090040d00a010007440800c130380d030721440c100900502c52a20f820f2000c000d40010f1511011154011008000981c0010000809800d00c0d4a40190250f806611241e06500c041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 233410881 1250 233409631 233409667
    0x10305150403050d0f0902030f0d0c020d020a231c0302030901031d2a03010603080d02070809130b040605121b040f060b04090c030212010b0a0c02040501080d081602060c 74
    0x1002d207045c84d00c0720f003c0c058131a03903102d00380b454402d4040d10049240a00029151040211503101280f104000c9400515180c0e800402da28030061030011035a45038018004444040c400d0806800c1401d01403c2552800604030f10603000300c4010100403048550b0025246c0c050711440c18140758441c84008100450020400c4601803074504407009101004031540303109181020700640d001400b41c082c075040c00c040c0541c07010780350050079003440c1655403c100d0009610a62054449603c20711010103180d5851030031452500d95444082203150494003048100c078900c2d882a4407468096641400b00301f00440e40c00380c1d020307a007404686c00c80c040001090203440c0c0b03d4040c40100d461f052021800c80304210241c010783e44005802c2040f49082c080503001c070720940401041400d05500100a8400003400605613000c0c20b00c2c004903100020350100e02610000e07041b404464025044003110079501c000e80503401081d865888074842c04021002e92601005002003031015400608451042440404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 233412131 1250 233410881 233410897
    0x12030213080f070e09030c030403080c01061508090606090609070c0317041a010807060912020102030d050c03090f19110120010501092f03070c05070905010608060901030515040305 79
    0x25551044011409107482d0700c40d5010300c0c040c04c10500003048150320000140c607443c118040c011450907096484081403500710b480c070f41d48a9900c0300e20106110b1076490504a00003026159412107050155109040000040000b80901403c0007000040e586081139541c000b034403410000941c49031b90600310381d40402c8040b03044504524500b8001001203202c600340342c0344100710890500d80d807107840c60303510392101d4840c0d54000307240701d6000c0c0070340d03d1000010400b0500c140101ca241c8400e6007001c00941d070040704d5000b60908040204004108140031030300e104001c40e0058052002c0e4003102140006160002a049032404001c1c1051640a016003d0035007440300e041d1304007140f0026406010302001d018413080107041003a610310a50880d4102c0600200e2521099003d000100704a0301c241c00040101082013014450000803e80034031541010304404000400c0139810090041c14010b0064101d6019040e040300400c04140d001c03030b00d2100e841200003070800d9512075050071a84c500925203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 233413381 1250 233412131 233412133
    0xb150301060e040311150c03071709010902010f020c1309060e0a12091d1515070605010e0c030c0d09020409020907110c12030904090f080f13121203021308 68
    0x100116400ca40b032401684500e1103503580036080d0a03100b04403612a11031010072a01000c0d0400892030442402001c3c60340001540f4102643c00302c2998a41c1030081c06960075915655110b408105659101410f4804100c0500090640221030001300e034440802c0c5041d4650301d42c0d9001400b0030002260003820309212420b04542c003544540c185440124591803a201c0441d017480c0000507090154840d241000b0700e0504040e0786036071a91b403030501074580210a1075004041d11032584030703d8410b0010300701c0107005040000315503051001e01c0e0007801000c1c000e024004028010070803524072200807240d921040800100d4604805c0c03000ca8003901c21041d00035441900082001090b81d440850520243c808008035807000d520031040c0001c806e04040020260b8004100401e45800c1a03003015412074801c00b09001c2c50065503c90f45c1e41500108103040d0064800070b118030001c503c82c06002e01803c0c1d0426003400c0c5440ba0340d80d140c400101180300ea814140c003c140400070f02d03880c4060400800760070b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 233414631 1250 233413381 233413391
    0x120a180b07034503020402070317010e0f0c070317090f1b0a0b0c030f07060b0f040c081501051e0a021006060228050109060e1605030c0f0a0b0a0302040504061706040b150301 76
    0x1c074015100f10810038407442d142b41c08000004000e031400c0c03515801480b030710031005199154180000c4059200c980254184100c0006080c102298056a1441009004058031388242d8030084642048190215801c100103e5007c55810b6985c080c080d104840d0512050b90752020f65904080c154080c0f45208040c11001260140c1400001d400185c0c1a0808075043c402c80143c034020002100d034118a8480050508000910748560000b46031342400d005042617030410f64038100c0043c200400102006060320041260f4050700d40400400b070420b000130300d00340302031814903400942d00c03191350724100d2031021500d1700288180a07040d07100d1641078004000b4409201d035400c0c650060000c0f01c5580035039120340e00d2000c5610342c00d480c000d402d44600402510048014208025581034100350056116480d40300019828205500514071020701c1e071000341e2035925050400003259182e511005565007d21a440150040814407030340c00343e80581d10f003d8a8880c001b1070301a51028544003a0550704e05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 233415881 1250 233414631 233414633
    0x18040311030c0d080f040b061912080c070b03070c080d020c030a1106060f0307030b070338060f09090a0b04090303020304060b06040602120a180b0703450302040207 72
    0x3c2450a0704034620f840381000707515042d038001402c8604440103841d00c1c41c4080406c55624244030004072402c40351409440b20394542c0d94840c08840c1c80c0e02e040f5448200054007904d80301e820301003040100942100310303040d80f9100708050079609050200030310426000a090140e5034403681a690080e0400003201e07220819420003078214150700751141c0c020b110300000108a072408042185480710080d018043c501e246640700c928000c3c001e0141c40c140350726443c081d01c907041c0b13040032045030002c00914001403030162400743c03d2009030480c14a003e50002c200d0b05081c1c070a00412201c4281042d904090641e4500c58000001d210400c00c1e2944181032074148000e041c0d241d0007442c020360059004011240c100000c01526100e03e00c20400980c119000c181150b03203102c030280090005508020450354002515064501450340006103003110200d030702e02c18180d0210040c1407402902c4900301900b09450040380c0c0e02e209911600001d038500b004c042d001400d03d241000b00035640940b0654480704e003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 233417131 1250 233415881 233415883
    0x203101208030a110f1c0f05130b0a05070e09100503010515030f030a0f0503041109070c0b060103270302160b03010312050403020108012102030601061107050301090218040311030c 79
    0x801e803501026142040e0b1044c129038099800c507000041da0445841c680f11640da0500f240707600d00c400b141981c50340ca51008580f1034060048070f100f0750700018000100c409500d40031980c0350300030f0030982c29a481c1c0010042c00e640c00901c80c4440a4080340c6e031484c641c5d103482d84113006a209800c615095400d04084c456840304106c40014400030490507034810303400c00e0240a41d02d0251101d2200040c80a0781018845170140300219041030003076410048075190034000c51542d800030f664003030025019800c20710601902c1d204940d0014000d00e424491400034490002d0f001d4408201c0000e0740c1c020101c02c2081500800c15145054a0a40700300c90a59950340d80c808540c00900c0240c902c001c0c00881600503a21035030403601a2a4141c40e06843e6034200505100981020400aa0191343c00340c070040140ea0100909802412a659036a06030240c0e60500b9090124507030065003e0781c1000060001a034600d517224400700504041c444055540741000c40d082e00d041002c003480e078000003d0206800310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 233418381 1250 233417131 233417137
    0x1030b09030c16050f090f0103060209060c030a09050a05040e0c010509010e1e0f030609060a020f0403020d0501050109110a20150106020f060124030f02090415030209070e010804060203101208 84
    0x8001c441c0d2060001d54001031250786d480849014040c0e40c20b400051002850782d501920300b00702c02500352801c013188002214550b6214a800c0c4012903a40d560401041c034244680e00e01130103041d1000d03c006004402c12a030b071020381484171070500c68082400070140e481004a01d40c81c440c01444074903004138226911508844890301703030340118001140c100b003c0c1070000d25207000d041c2e090003c169507a61808020300039000346d510404d000ba01000004050f0303941c8216100514003a0000103442d5250441c0401221442107215840420a020b06080c180e00410031980b04000950060941c8400c411018180703485202540403464480c1e0002c1501c5900041080d90609001c5c00c82d003840e600c03040222500302c0750b8000122040000c2c0b00840215100b604020049600c958000d801c043c40b80c8001400d46040807156141c401c0464003c10951625080907900201a801c000020400c490002040d200b0020405820075070004003060248101c00f25078002440034000b2072408034118900510f00754 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 233419631 1250 233418381 233418389
    0x1e04150e0a060b07050d21020a05130603150506090d060914010507020304050a03030e041b3203040b0408040506041502013b0c030105150907080f01030b09030c16 71
    0x1610b4034002050b600724160448500c02d0304040207007210301c8601c030111044030012559074a448040f22403215410030b2400a09140a0203450302904e074041c124040c0d000c141075034444400c06082c200300b144200101d295500503143d040d136003181d803600c030b810211b208400900002040140360102207414018040190204031040070000d000726220032000320f03541e0286004243c0d100b400346404000107800703031428882d9104042c201140074400034200543d4030340120b01c050081002d007402140004c201d00d0b0084c0300d8503905802d0242c141001c4440a4a60000500c005c041542150105003801944030540b001044003d080c1680c032a22007034845085c500691151003d503003894001d44030101507118015580c1e152031401da4401c0341ca1112110107114414a11615010311f40c00010030b03850a02550303115501003841c0e119004090002c0c0011032900610b960200403048061101880f140d44c03500381166080b043c801a02d40700c52101c43c1c2140704804002100d0300c180c00804104080420048080b0303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 233420881 1250 233419631 233419651
    0x20a09090b010b07021e01020115060306150c1a1317090109080c01021c0e0904050303100f08030d0c0306081f050a06210f1e060501060e1e04150e 64
    0x750342d8628000c0c0442c080c40c030009620640b0030840700704802540d00060310740c03c8144000b14089071400d2071403144101c16005000020340b508821b008030f808082001042c1c400d1841c10002d011810740740da003d5a107101c00403030000210980443c03c6000300c011619034254000312040609800400310301a035500c0100314078041a0b61600003c1c40340f40208050740e02041c1038001e4450b40c4840303040301009000603000e840c107202d10075044411903111070040511484c85880250b549003851801b071004400c0640c02920741d401c9210090100790800310650740c2c000d80d0984007080c0c0f0803101c40e080e030140025405c8045103210f41081c003149508404414030403107282007010017441d204e0f68107006c1070b2841401142c45002d420715800d40c00e00c10803d01112010b004000420408116554800f4100c1c0c800c0c80c00c410740c07032814010206000c21031050f030340107000f1810030071104440400401d0b210750090085070005c4c03405800c03c211a0b11150490501041003044443da2140c4402100b8241c20060303541e1801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 233422131 1250 233420881 233420903
    0x120412051f14060105040602061b0c010c0801050f090420010c120c02010e0303032403030c0111030708060d0b070503190c020f070803070206042c0c030103020f03120f0f07020a0909 79
    0x20f10350040d82240e0a44950340c0c090801555140d01c04402894900a0300d04050740030001c1040540003032081a000001c5683c44003020f502d86001c101d1182c0340c07400c16a20404d0703918103110000b00c203403452207051700e010086100040319400050351848030150020380640c0c5c0d070410803510f65902501441009200b41ca0708003001031104241a52070004458a400410640b4070ba111a684402e034800d100b410002d0440b0f240042d250203980c2034030340e034100c1490101c1011051000c110342044000754880010354609035503088584070245405805814907050110000c00304031401301040303d003074900031160000d1000100c03038080255550010f01c3e83c054035008002c0f0110750061302200703c80d0010340041c107643c14582404003180a8000d202490f8151082039005a041d040e895003000348074800c01c10343e92781c580d8594014089060304481c1614425088605110200d00c141c100340c0d07100703030441003e481e22410050200c04440c8619000690301c40d02d03400c0f0006801d15a0f0b04094001d900c10f00742c0d484 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 233423381 1250 233422131 233422141
    0x423010507121104080319140304030801030204050402120109050303090d05040e0105010e0a08120702120c10030b01020c060310030c050d030c020d06090f120e03120412051f14 77
    0x42256001e88020380014034192142c41c080c0720702c0e0024403040d26540b08292402d59204a20b03461648070158070403004c24002c0d5002c3c1e80c580c102c190580003401c00d6001524500d05560010070300c1c081408003d2046a403500428150b40f2883c160017a0181250700801a00744d032414180e50f40d401c00c5442407543c1c41140940ba904030722a8060310201c558040c1000ba181e42084015160f0b489a0200340760011304403400082d12a000f000b0136254290213810381035032480300b030043c0101ca401e8100c0624107030340a091100c10903142c082618024090515000594482e1f03140100c2c240aa80b215040c1e0100001c018001d002e102605101c084a1007540c4125500d41e82e40240b0a800105031000b0b00400c5265100c00e001d424060fa82c46c210314400c01e000500c041c4282c0d109060811441c0081d503805080300029030005030407141180940d4801c03001418406111000c1840c64807030b03030103855481165050004200f02007003001503002800301000c41c461200480c115801041582c44100a280d0240c0c0425 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 233424631 1250 233423381 233423383
    0xf0307030c03020f03030f13090c0809030304030c11040c020606090f010b07150b090705090f04020f040302150702100507260a21020c0f0c0a0e041410050423 69
    0x404036903229060350030441c95074003041810b1080c81d072510b4050008000e20b858000c090710040035403866150001e031109050000e10003c039001c100d4a20144805402400008440007080d69841641483e003c01c0900c03040c42c1c806403e0070541e0700c5035001400c00590307030030403500071034079522400044c1d440103030a507125500544408000e00c901052440200f0210010030005001e04072020000000400c188400c01d001c500c400e00e04030751070f0000510105210401d0f14100c032502c800503004960540c10040c281824580303510940c03000030310030b4403442010850401e94600303407500b182d0000c008005003541c01c013005e885a40101c50440350f801108588410300420b0000302d088804040d07110038100340d9048010350700400c02c1500040740700c18084076000f0500c601e000038603c80008002078081c0c01e5503402c81910349000c02400d288103514201d02031040403c0d0328042e07070384550011140c1040e0381c442c2c00201e040901c0c140c11101ca9508000800c01808141901902400d03c080c8001414024200d041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 233425881 1250 233424631 233424643
    0x20c06040f0e060f0d1403040807030c080f0607020606060912060f10080a080a08040201030b0a081e010e030a03020a1205092107050d030510050a0801050a1808040b16060507020c0f03 80
    0x8a503009110302c2012001c07480c1ba244002484a400046905c2e060302d9594080c40c28440741d00441e102004044140882d150501c009003540e60301030000c015a05041c00082e49840004003c1801340c1d0001c03503920090f607212103248103140e076090300b654850f040c900c0b000d203400001119401c001c408022000a0070346400140d2510054105180342d0070a40c4905080300e0034500944142d04051301d0310001c24066070f420307101400070306903203005011441541c5000e41c0f8243c0c81d403544100e01d0340751118041c0e00c59004411039100030170728a0f0040e91014250000d4604010500c2c822421524000c10080c00d11400161413107504401840c8182184002c60b060711544030b031850081060b00045440c1340141c1c02134004a800041000c441300c040d945030004203035400340f103a004115580d16201072260184407485a040c1042e80980c0c040802034168844d28a50b109900c510520316500049241c88141c41418080d20150300880c01e02440c180420b000750b40d030383c034020400d1068500c40c0048480d03103400145 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 233427131 1250 233425881 233425909
    0x1202030c030702010309020f04020c1513050a0f0c0f0f06020c0f0d020f01140d02040f0b04080a032f10060609080a110607020d0c0e070810090b01020c06040f0e06 71
    0x561030b100e80c9500450150186810890b00b04645054100c1140c2d914006405071079040720090003d640201c803001103a96010300100030303540d020040400441d03030110780c00040d02d0300519030594940041c540a1003600032540816510b80f060840452800503c03001541100da055080310070550210702000000c81c0c00d203036410762011104038448010b0401c540e5200c03100c04141840600103107143d50f29141c540c00000b208481d03a0340090144940040c9001e402d002d0701100c41e4a508040c01c09001550b901c4030400c0190603c03070f000840b43c1450130411000700d02480194404002600c150a11982e25500a18400e0107582000c0d03010410520481c804000c0ba81d084d0000d01c86c0c1c0071581c42d5207001581804c54190040c1081100c9800360300c1c2d45400d500d00f10300c9a114513049503d0000c110b12300c1100500400100480e2505000c0c0460701c140c0b55000381d58000100151465620006070b20705014503e4080d003008000c60300040c1c5400b079010560445a120b0b8103903111b65190420040f01c90000d004d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 233428381 1250 233427131 233427133
    0x509030f0d1d03030709031b05030d050315130e0d030b0609010509040902090f01060909360b040b0a0b060708180a0905010e18010203040c0e270a1202030c 68
    0x20180700d52400542000e1000d4858403088090303101c50028140c215401110394002088818400f042040b070658140750701c603110498069203072070401001a44034420440c5850810001002046400314002c040354218007000b049040304030f5021207060060300722030841c8216409100201404240030340103282c100d10001700311a203000f012000554003900460425904107030303031704401c0006072500808a40544a0700444011962410200a10b8520184c100440f41c0341032049440c0ca802c940c8003003848078035460309818041003607410400c29440180d074018080240840900007400102c0000700c0c0140000501800480d8004040c00780900c60340c200246861000c0198020b030040096502c50111001000524140c1d0b980010000307454003a00318422074004102030000411a42c40c80d84107010742c0078002d40c258582602d58030142c0c50903114528040416200003155201c49000405110f8400c2d0035140c81c03103502d80d0076180d0b2401100c1040300d40324052802401d40310300000590b11070005d160 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 233429631 1250 233428381 233428387
    0x6041e030e1e0402030a090506071b0f03110303040c0302010f050703080a02090102010908130603050a0b1e0f0a0806090606010903080d09081b0105040b220602180d080d0509030f 78
    0x140500010b0041c0641000011081a5054200d9074860001314054007401c0350103d803101c5282005c506140000e003004040c00b00908043d041100c10740c828210060708503010503103251483c2815200f00c059000b2241180c0800801c000402c0041d001240c20380f4001c1c1c1c1c444182c02c4040400740c82d6882100c002401040448000483c5512682c00600f1911410705c0007145c04032040d5600039954000640c04a080807a0306030901c8050303810f00c16250710280300401070140c0301e912004039019800301c506600c0608424810301100391550b1446040016000d0306c40990070707aa6010302505da1000b60b5603070555004074004200c096115a0b1010280c9801810f40c9280014000e143c400030401c8030401c440300481441a2014102c407002c0b03c8802d10703c00c0c0e0011440340b50901d018403610070011325152074620b201e1b00c10b800c0e020f2500702506840d503100030010703500c1400302c40c2035807080621005d241e40b03e007070007880408111030f4a0240c4040d0b8156881486035440d984800703a141c0c040ca411941e1740d89428 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 233430881 1250 233429631 233429657
    0xb0a05061204060b0a0602071401081608280c0314040b130c09020a1706040e06060d110d081908250c121110050121051e06041e03 57
    0xd03100160064840e00000400c00d00d00c0c0c1c00310717401c0d00c604da0119015800410f41017005041d0648a1005280c0901e40441c40785401c2c000c85030300c180c9103425281000312100c000b9004600054417060080390021052224041c504091005000400d09600003c0e0905118411002000d42c481c0d016660100c907101c00ca03a1940180c102c2c2048078242943d00418003140099146800c1c40101310318040b42d0f64515650092008000308410b0191103240258500418080e40d10404104950012011944401c0704c580354109046c040200242d4030342c0c0030100c1803103102044078480c020150020071200c07110f15001c60a4068508440440f1143c002d12000c1ca501180c61045500d1500c2c580c54504020000c12620f81b0340c0c42040322070040340c1c00491010030b1040c000d20750800513420001c0c00101e05004941c10110300d202c0080038405071080311040ca9010380100320301404040c039400c0740030750b454100c11688a8400c5d07480d0b20955040e01d950861050b02400f9000499503254000d07050b0711180301151803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 233432131 1250 233430881 233430907
    0x705090a051e0702030306040501060c0b07080612031204050d08090c040f091b05130627110a0e13020403110906030c040612050609070806040f030c0c0603020705010b0a0506 76
    0x914040b01c41006506805000d4110750703500340104442c0e80115101d290400c1400200c4006811640612902c40c0b070b080001b5410128840d880700c076502c0c120001d506d603440403a494000c0030840c4060750101045401460061401441c40f0306e008508841d03040e000c0c008240c0340044107071400c1101e50456403802c2042c0c101500200b100c000c0c2c20b0000290001a0b0719201c8080168030180c0030401140001004103141c06070140985a104100402000d450030900d903a981d282142a80614500943c803a0720b54a6281d1064188540e84e002917a620100254010300720100544014030030000c0b0101082e008406200b51000d990307101c1c003000e0400070940b00308030003540c1c000c010070f034140b00300d4000400d80c1d2100c2c0180402025500c1d42080450034070700d001400e0402c0100300580da9404480304110000001400b03a810640141001c2c04a081e03d00741102c1881540c1400b0b04003100c0368074005101d0703a061307004048040c00b950003007020b040040c080141e5140c80f40307c0c00354001d4062080d4000d00304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 233433381 1250 233432131 233432141
    0x609010c0b13080d0f060b030705090913020607080a0206010807060e0906040e0d020a030e06070f02150c03031810110307210e010e0601060306080a060c023901020705090a 75
    0x10410b200c0c800401a55801c00360350200e007008412903140e18203a020007840d03005400c05001264002411490032403001001402413042c40c51141002c1000700d415080c2c1950104c6610760060710703003036846030103007090f140950200200d00018860b44000041003000401c0460a40d42d5550b107905040207000100a03440c40041c0080e0b601c581e40d03000c010811001044078840c040382c02c0d0040c100c810320b0f50902030881c401c40d20310346002d0f5004100700e400080d504901034504550481d012418440e450880303844900880150f140c05100010500c810074130840c5080e40c444c1c2038542114041511200b0403c166400d084405130000b0080c4041108240103900980b00b5248440c10420118200c02600c01602c003441c1400342d07143d42d9080003902d000b5080c821140580b00318203050240c2890b0071003069a0f400b001d48041c05050b51a1402d500d054424004d001450301045141004900d9003280102e1800156000c56005404608007001a5001244036012540024030084840d46c0d8000e40b0f20180c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 233434631 1250 233433381 233433391
    0xc16060203073008060103060e0906010515070c060918140612010902030106090632150705061905090c03070306180f081e04140d050708030a120b0609010c0b 69
    0xf2400c803118500307010340d040b481c400090160f03a02022401c02000140c216844d81d00103e15200b000001c01c004076900140c0181180c10a0312101000c0b4500c55022a5034052814000c042e0030590307600013425940725040c9016038046046403501840084a520116401000709011006484001410a1800c100c003000c03980040f03800440d45040550013b400c481240d00600d001a44e03d8800740101c50003456228403201c0801c82c0d10071801800e5200a030102c44190540c0d129140303d040304208056406e0944101d2544441140d1460170100a070410354001016114161868a000251040d1000511142003c0f003d0003070001c103819900e4940152459440b4143c0c8230f048003040c0800603100440e6640c074240106e003125180c800a002c243c80e02e440c1c0d0742a182502034280000d01018440810300c90f040c03801200d242d10324500d07a182041c24140140e0140c0031600020410f400c0329900720078544400741c6008401c00010031402d00300855409440340ca280029071000d501c04c00902960380c3d083e00700d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 233435881 1250 233434631 233434673
    0x40b0f060102240f0a0924060909081801020d170c1e070c050406061d0a030b07030b031014190608070b120907271b02030c1606020307 59
    0x80080300480c08411003e805260418a8460030071840d160012111a08a011180140700c480c80c6911862607245205d4152210040407180c0c510304000254409001401e01410900104006040060483d0454482549694161031200c00c0c01e40c40411090400344440c1c80d1680041000622004251030040103620662010802087c841c2003440c178480c005607806119641d2501c83c0e10785007003108420f9100c180541c0c1403040600c003c9401c6202510218100031044940c2414403001a290b6400d541c0050b1040c08820144038482e90b040e000300c0f0440720150100e4054400843c0d0740c5088451110f050b6980c1c16108010481c1102c200300e50311203051780b9001c040b0300c490702c40041505000c1300f50b1007041600400200c50000d80b0008020701ea03c85a014081e1101c1ca00c0c1203030004c47c0f1264a041150850811020040401440c0c0d0190a40d021914100030b00c0d040160000f0795641e0042e8071451440c4101c010170031607480e10500840c00e85056902443c104081d030365480345241040081ca01318 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 233437131 1250 233435881 233435893
    0x60c03050c0604050a1b080d0e010318061a030c0604030204090f05120703112d011811041d0d081e100e010506040308090d0501021c05040303060608040b0f060102 71
    0x510201041001e00844c010390103402d6550852400660340001304200c042824212081002031645c04140300102007400d08040040b4001100120020403c441c0c0880401e03e0f801115801d229141e8011a450320341b02054070440c25a0a0405a90351a08a4180e9000301c080000344014200364001d80500d1348038040301040d8650310b503681070a040c1142100c10410601140c403100741a401a85000c135442c8140c00b400024060542400090f030107038551011190070242c02c107040080950211301c110307101300da220001301140e181031f22910600d504003510440c00d120611451942c10100c6035100d0340700e20020004040000820784120500800b00310301e00c00c00882c0e00d941402490580d40c4a595011052030b84075003000a10503100c081a00030502882060000b032000614075801c64418041c102c4096102d01140c0c501103019110b0782c4005420802503200c18952007606810040c003a500c40c1d1000e01c10a078076010100c600b81001c64000c0e04101401d404150006550458550003081c1841902d40d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 233438381 1250 233437131 233437147
    0x20103090f0f02040531021201020a110f0303061309060204030c03030c0203060a2309100221090a02010903061a0907050c010b0d260405100807020607030e0304060c0305 74
    0x220200807081c155080d42c1c684502204618141c4105580540d85403c4070101d1441144240701070040720300c60060304101403407000b05668541203010a0050306030f009545e54034140030000c01d61860225400344038031030310907600b880c0503010090b41d124410240c08844010078607440c82024080503801581e88603420031004c00400c81c5081d07000082c500070f0325106000d1a01e48181840c24800900c40141035242c01003050307001c8408045500b548610803200b108503201d11160038108240300004010f08c41c03000074100c018008501c0005031006204040078416030f14103100c03d85401300761000074000b035950582440040c5095100d85500740071040041a14442940800d06121064079104c005c10404520740039150003d00a00c0103105060318550840c40d40d80e03499120355020450f009400c21080c1c03801c650580b130740c6010303038009120040c4400403842c5c0d5070300c000d1304880040c2c44420040c080c103000901c1c001c0c007074020007001d802d0b244000e51a183c54800221000c86988404070104201000280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 233439631 1250 233438381 233438393
    0x15040f06030204140a14060c1603030c021504050102030f0d0209090403030b031209031b011106010e150f0a09020d0917090a0611070311010908010c0306090c030e0307080702010309 79
    0x3a00c61614016900ea05040025900380c00703007035205104440d003144c2842180c91501c050000340b002610195212034002c103804d8203100016000c40307802e6000c004008107040d8040d443c0b185c000d0081d24500d09002d11405e17290010b10940c010503015a0040105032603000d031038002802018405107005081482010010711880400c1e42c050380000d0301e90304128094641800350040e414504009140781c4181400170a4448032500481c2040d6440c2e0005820140d0040f000056030700d042106580c25036843d03481268001c0425100512142440c104002950a110344011070340b10004004001c42454003e807480a0352044241081094031032228000084c0d09440b141000070040c89055110f03103070f203824440245800d48c80b000c10443c92880c0f4001c607001c0403403400705498118013004034a88100b80107031528034030303036102c03048640c42c3c2030a0744100341e031581c40072081d6014a84184500100201d04031300340d444103400b441d820b40003040300200080100005105130380c818180401d00240e587c50b00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 233440881 1250 233439631 233439659
    0x30a05100f050114070b07020a03030c03231503121c0b03060f100b07051509060402060d0504020102010902060d0506101817010605030a080a0e06070f0b0a0e01020c16050406030308061504 82
    0x1d81c2c403c030308103410907400d4011000c0cc04043c0c501003002e07840300d181028a6944840b500c0885000b4040480c0303035401e01e80400c07851210040c00311103c0b0b00400301c50440303541c480c9030040c1a6201651a001c003000c49802100100310300107004016a80f10000503504038540076048010b01d82031400005502d412481c080c01d03915000d1000741404440c801c50b8243c2e51070005042e2142500602c0800005035609800e0ba0305c00d2450b864001502d1f0365034801072b8010041c0b408044d600101c042607407058a0500d81001c1e2254800b9144040b059a00242c10303502e07030f040000c00100040900000b80000740d080d80354a0307181c4031031000100d2100c1d40c55012a04084c5c2142c0161340803038002034188036031608032003c2c4417000c1c000c0e505030b80b900001e902e0321070041c010800c0051000e02020003240b0a42c445401047ca44980c64008641d25048400b800307686200d290f0142002103000c83d40041c00d49043d00c10b2008983c1c05840d1300c0c01a40e02c0d04104902d413485505201541d07581440041145c450005035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 233442131 1250 233440881 233440891
    0xb030702010b031e0f0105060a03030c110901030b09010c020d05160201090b040602030c070b070206040515130b09040c02060402060d0c12020c0c0411090109050f010302070206030a02030a05100f050114070b 90
    0x3220f42c41440b4204501c3c04d0118480c2c1740c894580c10001400141d4035081a10030880b41c042c640040503440c0703450030f618000005110702e0343c0014043c00101c20302c40300c41e610030300070036050008019460039800c0a988840111a1200c0828014091600000009030403a0324940c41450000c3e052038840518410755001a000000160302c08034410304081c8040007001c024114008a048c1041e9007603000809611450080c0d500517503058002c0b01c0c640fa41c0c50291000011403e0034032080a85400440030640c1040c142d01d4481c90510403032030501c50011039014007843d00903203c10714014840e804032015220900c1e150040158120512010000d944040d000300014580680b1038000c50708100000e40b402600200c0341075404010094142e130b0082040d00482d041900d4802d40304c3c1c01500103900070300699201a412180c00406c008424034142d00651068200b440c0800c103d4540c00007580d51a0164040c4906845440380180120b40c09003032034801d1401e12100951920960b5580d0885007481550 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 233443381 1250 233442131 233442163
    0x160e0316120c0f0b07120318030309050105060a06081302010905090405030c1507050318010615030203060a0603061206052d0603060601140a1116060207090b06130b030702010b03 78
    0xd119002c01140071003980040c0119030396107400c42d00346007500740030340301d154002400001c0564079801d0840c0650058803142d000605941440241401d02030081d104101d82240d80b5442e100003d2450301d80ba803494002d072101c0f551580d26130f90b09d040c200881d8009908090381030103117900c00000c540e512160014480c030301c100c01440e00c40e1314003400c02d441d00c02c0a40c03c041c1d1800c0c43c5810020301e5a031050580ea40504000c3c0180030300d07000012910700620054000601012004011a4003250550015030141400340d5407080b07140e40c2c5107800c4044a419006081c482e0f11441c40a401045840e0000b540100d02001a4103840c101a4806100c00044c030040c4100324101d07104000c8645000c1c090241d00c00700070308000b50804c03049542c00c0803910440030b811040c0700102c1100384032100700300410224450282d11840c03001c1d444000c06552858640308202186081c07406e0716040e402e01000780d0b14080c0d40b80503143c03140350410640d41d03a0760304020150402c41d0b503110300c41d09150703038200041129401d07000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 233444631 1250 233443381 233443409
    0x1a041104081002040e24030313030b0a06030f0b1504180b090c100c050c031e0708150a020d0e060c19081605070321020a030b09160e0316 60
    0x101500e050540d10b1820045141c4180410020041564805035001880c0406100420320800c1c1030204044501c03841a050311000c100d00b01006804030348442078a000d1701011116a503034034200c0b011b0b6021404001d107401c84202d42c840001c4c001c210100e41202c02d0702c51480030155020041011641549828902d800d034400f000801c1c0400500c040b03412112603005840c009540201080c251042001041e0421000c10000418804240400840030340010103039564499851604400840c031503e15200714050b00a0014240b440007680c00e10310300c818440c4a52680d02c00e5102402500201d40300b014090722505901581d102c1841003a2244132102d09880d141d02e0010090007840b108101d58109200300c0c4000c5c482c2240002076000712240301850300d16034410302841c08030307810710b1180d0301e4030404154814400e86100480d0090300c000906030394104104d0103c00c04000b0701341c00c2a102e1070b560010020000170010f11902d00b0b04d191410140898290020192170940c080d40d0fa82c2c81503016103104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 233445881 1250 233444631 233444639
    0x1050304081e1905070308040b060d140312181c12020a0804060506010c150c0e060d050619030809040e03160b06090c040e0f04020a03020901030f021f050901031a041104 74
    0xf940b00c10200b45850b15100e0706003034999034007402d10500540302400012542000655070f640c1d03442d18481d11030b8070000e10300e004500a01e1315640c0c3e400100706050f140850000080029445142c00780220078002c005060000300882c0c60068a480c2c2036410040040d100b90700258040103000a20202103996160038041c940303824200226400600420f040186014030b034004907100615074986840300b108001101c415072141980c4580308142d100f9048040800c11024188096110b00d109080c1a21080e0081551000000140d80079020092050720240a840d4003400c0c50f5100c01640c02424049030b141504008800c0d206549480c01241c104114504000c0282001c809040d004404044441d081c41c1c20b008102c1401d442c01858000d0b075152400c0068155a079210b41c02000b560041d100410750b58403800c08035118021400107130302658441d000c0080100d5002d502821190310341e40c5a5003460740c000011400b90a01c0c00c180503c1074101424405241e50740e00c902107007001c0411a40d6510b51034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 233447131 1250 233445881 233445907
    0x20307080c16061d03190204181e061808070b040c051306051f020705190317030105040b010c0c120515010b0910021504060f090c080f25030201050304081e 68
    0x1d1380c2c2c00b080c0282c025207035166203145000101001c1e168101e50201d900c0e08030160040c400e078007101001d040c0e4001a407810b15480366514250310154080c2c1420301500b44503802014402c0f5280f5002408120200030142c0403034000c0ca01250010302c68006d1340c00741c0b40c5d01d100065883d0740034110740400c50382e075140420076880c100410342c1e910102014034a40208140038060340340c12452081500828004881c0941c3c2407140c1805006158480840792203030000400304240398209000341c5000c0c0e481d0440344d0899600503515004002d43c440b160541060409100c04421074440744110b40b0f0348143c010345501c1c2e0309541400b5020305510100140c84412500800451050303408100d015900010b00008090311241030503603000d82c000c3d4001c5810181405e51100811051a0182605000f0680400e581c0350120f560b4400f591003c04440005400020a1020040c444c44c0e0300010720f859681003005500640141d6407041c0101403250414491289030f084200f000c1c044002008400200050380c000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 233448381 1250 233447131 233447177
    0x15041101030c090e0106031d0d09030c0e04110427140705010c120c020627091b07060e16030309030b0f27030c241501020307080c1606 59
    0x1414604400318901e13010482c2d01495040c000c1c28101038031403000304d81c18032518600043c880010400c495190b801c19400800540c2180412220205008000504c46400018080c041d0750040d40000301c2c0141c0604000c028413000946803a03c07900c1c0c200a1594041040c03003045551301440c208131041014042c09410304540340c001c0c2e0b0521000382080c0e00414415040c45480c0361040c2031001e10a5154000114540250030201c0c140b050014280c00b00c100121028480181c030607118540e0581310300104400f10722403c04903e00d2410203110b0f000c08940d01e500700900d511382c0c03a0203031440c0301c2e0b00d9800210080c4480e0001d81c041210b540e0104100200b900540d80d00c440200c0c0900c9460038040d4504040003a00e03a03001a00452005080e525110b06108865013100b5132421100341c0365454450030350701c05491541410801d0610001400801e008106181403c4144d000d18a48403042da103850294005010001552044200d001b1030322251019000152000d511004042f00c150240c2c4005a1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 233449631 1250 233448381 233448401
    0x8091218090a1401120203100905031201090b1c060605040c17090613081b010203180c04020403020114160501090311010c18090c03021303120809060402010e0906031504110103 77
    0x20f4500140100344198268025064407800e50180d5000c02d1103000181c0340c41c0080c3d40d10500a0318005100d0200800040101407803080c2580c5980180c1c1d90b403207998100d4244004c090703040004450301080003045e501c42120282d1080400207000c6482e81c02190448003542c2050000c50a0180c00e8024121401800e540c80040d043c0140704600d40842006400c020303200380185280e10104219580c40304981146100d10030001c0215100c0c64104624542a004803107241194014460410fa13282064000c85060703c0d01a1a448148850006181c011350f0004118582c0a2090a2402c000541c01c0c061440c46038040d40d0b410248182c103c0e01103007104e50020f008000d12507203503a101c4070f4054030750843d012a2818000010003000014003580603100740300d03044d00d40c0c0c40804400300401c810300d44601085c020660f900611940c07030703a049035030302e4a0944000c0e000c10030007000d16140d441d111140c10340c4098081d09844502d204251208010441690300700c0307145040e07a001c0c08407541c0c1031258011030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 233450881 1250 233449631 233449651
    0x80301080712120e130c09060f02061b0c0a050a030503010501090b070308060402030a150308040e0702060709050d080d0c08061906080f09070f0e071209080a0809121809 74
    0xc0b10755075424882400101060188a00e0580c00300b515640c000100d54224400c103418441d840c10002c000f40030807558020340020604282009916a2000030498442c40440701030403251111130384822340e640c012b11095052441015524030005400340b150050145c4a07840d029201c1d4108000541000e6480e00100a085410702c0b001020a502005454122201355401a41d98584401c14006418074100781907034820002c0c070020410201034010412104010700c0f10a16845489040b6140c10b404d49103200051200a01032090707141c1361400701c01070341c42042c106160103109109181510701c0d4101241c0898440310802c1158101450a0309494215075400302c2407034103161000e8030b001c901030182c0907803020039000076131800002c105000280054000004201d0742e00d41c0d111004000469450740000d03900e542401c3e00e42c45600078042d0701d0b640070b11410b09002c0a1101120400d1005120f02601d00ca002c528401c00610300c00140785249441c40759070f0354414040700388039010702c0160400101e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 233452131 1250 233450881 233450909
    0xf090f09050c01030c0306050a03151404050607210516030e0d0c03030b030106031a0910060b0a080702010f11070c080d051c0905061008061b0f0a0212070803010807 72
    0x1500c0450084903102090900062001704401304038010410340c0c012680018035500c2c04410701042c640400c0b00044409810b000040840044599010054800401d160b02a00c0822602d07800b800203c2030310118a01002e800f00030070b101440a07140107403401d40c5c84405001c81c0020309641805004900c0807410014114104031810080046850310b10180402d0790b25544114a40c0c0c081d04408003c41e04402c80c141036844a515030246040203403407010b071030700c1a80b0520304644c9082c09400115002011418249581e4400036146890000c2a400440d56104603c101c842c6252248110300310f0030251868071564503140a5020052030b40203018a544014901c0404a80c000300b03c60664101c2c10162109009071921780c000760030000c00050680c02410f0802100d803d40004000032280090b044403480d445840320103140501e0790284001038541000803da180e07002e10018040c4403200c3c8101d604c000c0300e40c800c14403650007407141110604000001045850b004001c034101130201034008405c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 233453237 1106 233452131 233452133
    0x602010c1805010912050a170c25050105070503070f08030609130f0803060f0a09050f06010503012909130606020106060201420f090f09 60
    0x6609500e030300655452611002007150b00c1a11080d907074609181c0109545010604156082d11078001140006400d19046240000048140a444400418485082099403003d01da050f0005841c13812003046003907915400c64038242080ca5a43c11780c0e05d003030360075405034290103858006100c4c034080901801c80700862041c101143e0b003401c1940c0b0803030b100b05020341e014405071241c1890f03c640000640d9442c01560031241c008e0103414034022400c001001d08180343c01400c00b40e030301ca20a00980c0025918032075000072003420306c2401c2d5814040314500c485540c0c82c5000781c00c030061103420908885030702111f001100150440bc820f68500b854107000c0e1041e03204440043d03180a00c001340c11807040c0b00790400b034082684184c0080e0303a40144c2071002d0400054009111051303c0310f0010352840086604000c00c60003010402a510740101c000445101c02da11403031040c1411003000c = true := by decide +kernel

theorem cover : BRFrame.Cov 233273381 233453237 := by
  have h0 := BRFrame.cov_init 233273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 233273381 ≤ n) (h2 : n < 233453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
