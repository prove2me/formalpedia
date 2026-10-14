-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1968
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:20:13.024988+00:00
-- url     : https://prove2.me/submissions/a16f36cc-3a92-48f8-8b77-482a2bd2da4b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 353776978 ≤ n < 353956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 353778228 1250 353776978 353776999
    0x5012303090a0b010f060206010e01081923010c09050607050703140106030506012904060c1b0b0706061401020705031b0315010914010b0f070609060207020a030b18120702040b0a05 79
    0x10070340c000c5c00290040000622500000090103202428458101c42688000d440030110a502c0c1d00d0105030241003c3c0e80c1c0c8148040d00e20b0b04580c2c0442c1e800161203550000150a0a07044801040303403960343d104910400e02071189401081003c40d080381202e0b80924100100c141c10083c2ea070240c41030768401b900034014800005044450303d0300136454081231802e9112072200c070300c42c143d5a9020341d000d50000501e01d03544038070004200980c0c1c400b05034400d5078201d160381c2c0d8601c0c200e070281d0300c030001c100ea13000d440702410000760b0340e902c2070b5451121090000e008003e0030034001ca40d603414505220034080c80c151040d494a91000e01100c003900e07050ae040070b801582c40d0070b40c003000f4100e4080030001206269000143000c840e440c4c04e641c4ca1a806105203441c100342c6840d00c0001e850714140680324140d08000380b0005030b0700c407000c02d00210300c1986201c01e41d250020501c180640314542031100d036007081c07000000f00030108048643c055030484c2d001a0003c41c107004210302c04215042160030a18406 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 353779478 1250 353778228 353778239
    0x30303011203030b0103090309151107060302091323040c08030a051b060721060503010207112d0d0503070215030a18050a03030e0a150b010905012303090a0b01 70
    0x140700a0324601a44091004a81e038800440480c4c18070040940000c0794078a00340700603040ca4040034400300c800c2c9006442114040101420158154480d401091703001905113028107003a103804c41c1006c0c55080800881c40c1440051418036032007502d00100544000c006030401200f5100100a854410210b0307444901107000541280e001a01103680400031079900c042081d00011418811940c90752400c0074040c0400390030400701d004015411003951a050b0100e02c9807001d2015158041c0242e00340100303035025009111480354003000c040100300e5002800c80c0704580b00040c40b8841d50003501c00300710111080c20820708500680e9002540000c4411b5500440c00340c05011350f0003200c01e41d0040110018540d00050340720300140b00105641c01c401c50310310100e0300941c49807072601c03010f40c2924814042a070b91032040d80300c480340b111505665134800380e45a50b84155403201a00e428203082c41004200603005505207444120815808000000070707005280502101030381542c0701c01c90842558540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 353780728 1250 353779478 353779499
    0xc1205070e0105040e070302060a020a051b0108160f0e06070204050a0515060a1202031b040306090b010510050d0b0a1a030603100228170412020609120901120b03030301 74
    0x5118411550001c10004583c91a041c440c149600702800020140280b955080c407429402c801e80d0402540030b0040d200c804610f042c80003840d201a08070020210390030050014044501c0a482d03000d0010081111800c00790f00091130711803903102030402030000346100000860034480c901c002900581410140400403120350440c5005072801c2d0781c0e00103a69014010701c00e080c00341540e482e0001e43c00d89542080c0001540c000c50b0000c0c40d5844140100c03844840410040d4001e600031182c00e9641e00344202030040065400d80503000498212403d0001c0c92001801d40c0070308900181404e60350300c8000340c035603550a1448003c103002488120042d1030080c2c00d00c81500225802030090190010112441d0181d200310780005c0f01c45041d00700d8a0001030b18040d640000c070408401404260050307103006509400000384207034414603103a400c01400440003800c3c0344028014413060fa2010719851070b002c01660503a5207140f400e103402c020f00280a00500044e244d120b2849425000010011601d640c85 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 353781978 1250 353780728 353780743
    0x41b0c0c06050c07061404030501050106050c2b050a18060c02130b090115090902031815010302031c0201060b0c0c0a0b030f0103020405072006070e06180d0c1205 71
    0x82408000441e5244000d440910541080002a0300481030900c00d043c01081c0c2d40a200c2c807102c00c0c190600f51641d4a4508682083c0c106101041020584024005d000c0040c13540001c10000d00408601c0080c5a02192101c1042d2017800e02c44081031001c0304a00c0707410320840401c124440e10103a5036403407101404911180c60300b40c2c042e8014143d1060001407038003504041c070078003074a10710700c582c6000c1066034000d1688121a0402080840c00580030030540007450098a02e81801e4403e043c40760b021034600308502120040569080004002607074021880c464022010306081c040b80681c0841240184165082522101d00100e41c0c00c03140003000030801c1c104903003901d031640050341300c002d05200d6020072510101d0241d10300d00144010304207504003580085035820401a4000180e5400921480040180700c4a41c4518200b00340d0a07801071744080264001c2c2c1c0c01620300340a11480f0002c00600c107509030b001388480400d600c01c01c112000301d00020315400b1807105541002d40f60403500c4400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 353783228 1250 353781978 353781983
    0xa15020a02090126070e42130e060a02130b07050102040305010612050c1323070906140304021207080a081206120a1205040f09050f070c020915041b0c 66
    0x1113402d198440e00ea000410009440410044201650700c00c42004c08500003102e24048005010340e0440101c030014030812103c2200908100c5000300c4401886241a003070100080424244448402008030100d2000c4d04880c80e898050b81c0e5030046100040e1000155120421540b17000031050103100d410340c0901b0603688a50000c0c84484d07a0f8446180b145529240050817030780141545200320b190080074020029080321021583c0d080c10305a0300c00300c000d9460b282c1e402c5c1146400300a0480e5004100300082c10860030048442c142c4020769410900005000034014107480380c02061007001001315000600c4020210751181070340d8034100311903401030480c0c51032014070303031001c500c091038a8104400103507440001049400d00c42e03100d02980c2e00100b42c1d61818004200030101c2e1403000c100b6190050085500c0104050030001031004101d100104840100940c480802d001aa68081c230700d070f08500c0180b1200c102c1020500010010019555000c14002010300800e491030342006800e4101030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 353784478 1250 353783228 353783279
    0x14031303032a020108010605070c21030f08010b0d09080415020a0302010b0f01050d020d0f0c0201150b0c0604151e05060102060a0624030b1305061e0a15020a020901 72
    0x31202c19041d14000351284000340441c4201d00144031181c85140a00365242c00f99064400c016590107010f00b07001031074011401910954403800c0c1c141600400c50441c022450700d41905158500000d480c80e6010301a202d0444603100e00d015814031005006660180480002c44d02e0009142d40c0040d40c3c407480b103401100594200301039000c40b0728060401009050040e1501071070450302800050081d0f001400b607800c0320386d840ca804081580e00d031081d05441e80242d00000340b91104041010210142d6a100e8031211000300311558080c03502040d0550040d40c02080c0c007040034080900c20000d000840341c044084051464440780e941c040b038200d035014060a03000c0d20915100c020f120300507500c0c94080c3d519090004658451440e03541c0104241709082450300041f03004001000070050f00c013180030f1407925a01c9a05000c0c2d145014003403032440d80c001048440350001e191003c01c440700c01d07910550b0480904a06841c840034000d005102c602075005050300050368442000d0780080f00102444001070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 353785728 1250 353784478 353784527
    0x150114031e0a02090f100c050d080a1103040203030901050a12020705030a080708061e0a0302030709050709150e0d06090203060f0403020d030207110f011e2312041403130303 76
    0xb10b140f007240d500283c003030403601003c070408040c0710409058040700d40800920f040b100c80820010b000a403641000c03aa1000c0090400329840300603260300c845140c0c07500c1c104006200050f0303000012580e560304c0a0038003a41350f440940c4241d80140b010003400700d085d40002000420441d000c00207000c03041241e2190342d400c0e11b500d141111040000c4803902e4010030100407082445483c4040c0c02c6a94100074046401540c5076404a82400e1603a03226040303154480062241e82030300044074601409013000003615810303000c80b00804840300f9415484c01814296050802c0c031849030030401d5241d402408981980c1004070100034010001c54058005000700341081620340d10900884441d40d13000380702000c80a22640806c10021031080e02d403414003a101e410058404c1035135800e00304110294a40da403103800e030039190810845e0500d440d4400c010342000766014220660070810380260308460240d030b51a0b691403d1174507602c20641c1c40c2148201c1232100108040d80f00c03041c0030311000c8400903007115 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 353786978 1250 353785728 353785741
    0x5070e041407060c24020409230c090603040b07140a020a0c0f080a080313020913050c0d080a0809010b190519030b0f311a0f150114031e 60
    0x2c25201402452036402d031904002d40113400c0b004285c586506640140b0341035580c4140c00841c4c07000000000018440b80c9420f401094040841c0e40c4021003e2074241707003403082c200290140c400104001c0030783c00120b001c202e0780c81c41b40380c0c507400c210071402001d640d41c0c012260281d601d10303895008136030b003044100006c02c4010320300001808884028000b40540122592240c3c00c41d000100095000d40150b001c200140c1c2c3c4810184d40100b6003079a03401d1210b51981800c3d807c00d401d001c0814015200baa90a800040000003100d0303001c440340c5407586190310b5540d140c5024004074210140e100c144d202d41d0380c00340c0c555002102c0888500312010622407810581100461049100141c00e03602d4000000b004031601e40209544010541ea01c84d400070b81503001c140318100d921903101d0034281080c1d11401000010f6400b000000c40c2404a0302c500d02d08811421090040181410142c44401448482e140d00400c100e6401c40590340741c3c1a100e11781400e405070714002c0341c98000004115040411817 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 353788228 1250 353786978 353786987
    0x60a02030109150f06030209061204080901020601090b1c03050c010e06010510020a05060705070312140604050901020306090103030e03070f09020a1407121809050702061014090604050405070e04140706 88
    0x41300c1c00c40120b0300b480f42c940300d0294000d4101303011082d04214200181041c1d00303028492144100c2c4600000c503116412038000a1615038160464a20286000c00c05007155035000d020411b00403450125901d0942e0910b8122820700030034000d1180e66081021041e80d0045c0840c0850596030f081c0e0b00e0120520350010300b241e0b242583c10000d04582c024002160007148501c00600e174242c02030809100d070614a5910000326502011158a10100032062110f0303031909024070358114000c10029800d5041c4080000c80c40b46042c480107060046900216416840901c0844010080c030007d0400c000d98032a0448042d6000806030701c00551500d140303401410081e07040d039142e6500004025040c0421643c00c0d50088211301d00e41065030604000002c04aa25025052240000c0e030b010300241d05000c039003114098800d4000c05a0380451400c480c2940d1910105075900042c11030b4007041940b507a090150074007081c1d412104218080a00300424003110b66140049011400708498010b03542d114100c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 353789478 1250 353788228 353788271
    0xa09031409060f0d1d030c0106230d060b030d0306050a0501021f0c032009040501090b030d0c2d1a060a0b070c0b0a030b03010e010903200f060a02030109 67
    0x56000e1024030400410b640500050403601c0501c4070001004015660041c2c0708070011542051740e5400007030120340c480428040c0b80d0060520441142c401c20440308000c554147c2c030f107080c074000c99402d1501003d02c00300c2d4010146045000e01036403981e003403144004010b003006005450181d05100c0c030004107544006a20101054400030f040804038045c800034000c0c000e031503c03000c1019122480701050b994181c513480310a00d600c0000c142d4130b8095030280025554140d22a4035200e103425a100130742e882c0411000e8a011080c9820b02c1c1e4416186000e01c002c807115088600d54404d40d5144403c090106c42013881c91038010242c10300044680c1101c030411100031924141c00a842d00400c11006080c5400341002030320888168814580318101e200458001503920400241c9840c0842d0440c1070038454074041840c0d0340024002c400d07690f10043d003e002284882c00501035001001504110140240f46003808000d0a80d911810580c0e9440042c1d0030a0217602070307691804584000c0300840da00c034003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 353790728 1250 353789478 353789497
    0xe09010903021e06180a0204060635010501050a03060b070309051e030703080d09060f05150a0302090f060a0308070303020703320307030b03031b060603072301050c0102030a090314 79
    0x802c1036640c0c1e85c05491184202e00300c82c007580c1c030586034903c005a4440c02180003600c0581d440d64a50141c144012070445845001644011242d5200381c0c0080c105911190548038203007882a91000300203800c030024080c50f444290001000300c0c9005c2056401419001219012581d40d00c1100078480c0d824001c4850705071480d4183d00c140800c200180100b009402c04240b0250300080803003550311003100380c2310380722a04900342c1d0f40c84040002c41031212050004000c000d0312080c1c40340e81540d020804402d0050800210009030100041d21baa8621290070041c40c1d02c070144030340342c042c9464050041e41101d1003c0740450080d89d140e4009580c55140700a4122291f180341003e510b600171807543c2580041c000c0c5040585a0715801200d403820002800c6c91040c086074081100d02c0401d10b64102140504924841c0d086214100b05410301ca10484011080c54441c0d002e00f03200b20001a14607100b2018803054039400482000040002ca45c800c2032403034040d4407003042840d10060569454820341880 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 353791978 1250 353790728 353790733
    0x18090606031306201204021f120b060708040906050405150f010e1c0506010510030608070911071203020d0c0302030106050d020705070e012301050a05090603100e09010903021e 77
    0x441c40407a9070750b0007000796061942c4000394440f04a110071425070344400d0080c07900205a9040c4000c6041070f400544001304500c008e07010b0001030120081602c0c0110720007030740c0350741c55161040156460204842e201c0340e0128410740e40e83c0d13503100c50202a003410302c1010f01c10b5142400144c014005100c03a0207030408001e0030700064042c4080151200c08182211540180389281003407540c00b041103022400ca800f89c0000e01003503151200300700d006841c400700340c41014180f910810010200060f40b2007079411421020500c42e162000b00c40c1c050280c460003808042d0307042c0c0c4050050307400d03078000d100d6066142002d12280f42c400b98280c040e40700a101e10000644104a220440e00d603650240082c5882602600c0d081c0c2d0b07945030054850002a00034030380309040c0c0c01101018010200458000102c02c6c2412814042880000b078094041c011405006400000c0050400204001c1c1040942412440103005003802400207009007a030040c2280036200701c1c040501c40403440c2c03a0300b15032080032400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 353793228 1250 353791978 353792011
    0xc071e03031403071101291207030f05150a05011511030a14040b070506070807030e0c0402280e01030c0e090406090f0503030406090201090e0f0f060607081809060603 73
    0x642c0e407520f43c40102400c04101400d503040700c8010080c00b41103c2e10112080c40101001c4101020359a03000c188511031050781d08080040c0002c0012500804581d000908501071b0000c030b040560600840c030402c1d107019500041049500c00382e55101505940302030341d0400c0002800c9405070703a004410382c2c001075254402c1c4280c41c1c20324810b0a00c803520310f60141e0014142076481d583c0c240c140d08007003070807aa0790f0020b004000c1c8072640030203959401100d0345030510040d18a12003640e2500c04500e0030600a9400203909803180351100410b0201071000072004007003034100003009104000108520740000c1c1406a6840c0305032181048039010f0600408440307a98880361b6640c0018800c04400301d031031089207280e0301c0101d90188040e40c4200c0c095071010400800384c0c0b0004101c02a40c0d08060b6294540605100001c035107441600d6000c204090701e407940303460b42000078803240500c1d44010181180050310051660b0741c0304540980d41c20036195940e039038641d8000c00589010490303007090615510103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 353794478 1250 353793228 353793257
    0xf2001020d1413030c080a03170c031302040b0913200112180b0a020903070e070206060906210f0708071d0a060e1501020f12040909170c071e0303 64
    0x10010103081c1c00103450f44400c55907903551080022040d5000e139040b43c000001c408203154222400140252010280c040d145c0b51002085c03045000150105055003601c411040031134031564403181d00000e00810241179854410850509006e0141c011541540c020401d2030794208885002d511909058444044894020305510000d200340d40941403881d4000c00f4010210b0030032100756001d401230103c090398132013444040c540f604210b40c4c0000c0c840c042500c104520341b507000c51141c0d0403980840b4941c1d0796413243c1000489400348201d03400e00710b007400c1d0312120003800d0004903118a00c8184069481695813040c84545840d854480c48079100e1a800490341841c6a403420140e021606180010703525489600401008600b1150401d030516000800f10b100d603010811100c0c100521001001c885600c090400200c1c0103500c100c589240d143da80c80f1040040c00080f8801c80300300030441d151907040a44240355200102e104c1d0140002c91003588180a050440003102a250540c41e8a80c0c8a98940c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 353795728 1250 353794478 353794517
    0x411030c03070e100b030708041a040804060e042702040e0c1503071b060b1206010b1c11160c0608090601030b13050708011b08040209130f0f2001020d 66
    0x401410002c07070ba413880400c52480c114065070090084c1d5881c6003051925180c0102c1701100c0d006c140710031131810f504000019445204880a440c03062400e61811460200400c2c0a080c1d803c5407080c1000340c0d0b03080c603171122240042503240325008a9050100070014410f80b600d4142c15456180c000c2202501c4000340302219006540040e000d00c4c1401500242d1416041c0591071280d00700c580c542c4800303182009141003407010404030004c2000c1d00807035150080604c45440703100d265107a075084080720802c040405a0107401609028543d1aa941c070741d403c1528444080c0e944101c45814558002081c8244503107250340c03003000c00d40c0080c0016429038a5400d94140b0082141d004814080890000100c0c148032010040252100110301c0b24084803449101c80a00b00301c000c104052502040090303500c551425401c800035002549845074103081c440c0044011140103849c00c100e0313080701340420800400d0100d1a908141c803684034214402c00480e2188403400a20000505c090b41520710035081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 353796978 1250 353795728 353795731
    0x3f020d1409060415020709110d061409070311071703060901080a150f090210020607120e0a0204050a09020d08042603030a0b060c07030c0f050a0501120c030618050411030c03070e 78
    0x30740112240c00b51f669001c40b09551015402038010500850071a0740700099018080280c02204565080c41010300007060203c04020304420405403107a03113003445c210740c83c012501d40b250094080c0b5820410210200c4c8154803e0b1040c074001c490346800000d600c42d000c1648060943c1c4542080700c0d00140c82c050310301414a01500d542150b0391201e8200059448503194102d10b0000c0d005040c50789043c500241c045041645001242030a0080d90381c052003002c10880c1c55554100c800250755111407201c00d0003882e2403d0000e403c14210003109003402005c101030811650034683c03600060700c100b00c090b02c5142604000d602654010320210b10a02e403150003a2010f403101414090504846140052401c0113950043d00e107160228800e0142c03c03038500a40002d082c09444406800345410002000d50f840e260220030b1280d076540078011030611903001a0010b00c80150841e03c149108018540101000d413022070b424110b034a0070912320b04001c280315031210300007006400803d1426014040c048030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 353798228 1250 353796978 353797019
    0x2030a11031006060315170c060d0f05130507060212040e1506130503061605041701020702060a12051b0f0a11030a0810060c3f020d14090604 62
    0x19000203040c400c8443c07103040d0080c0003170368020841c1e084000c6120908951034204400341c0304403096000c640b180010300d07500500340540f05d25070b4600030020300d903000701070455240b02080d0624051140d41240b081c103100c556805a070950f95401ea0b56503003681d07101c05040200ca030f030000600c410010303804003a4005902c4490406001001c0344240c00044241d405a0452a0f2580c043c5406000d682070030466103030302500b1146550301d1511500300c0542203010714130550804190b1036145810080b000c0d01030360080c41e4080c0c58262a1542154090200300021074003050b40ca251400117080000322007041454401c2603652a481d1071a4401070174002e40c0941c100906124a003241d12646c1c2c1030400081a2070a0241e50b40207440c02c020f5800380c011003059110b0300400c080c0c810030300d01080311502c440040405810b003030319550030103c1505985442c036000001010104660004140350003040c8138201c0e410581d1b6107210292041d00c48202e5026990445401200c288800e11060008104194a504 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 353799478 1250 353798228 353798233
    0x5090409021801081011031302011107030b0714031608070207180207020907051801200109050c0108090304030803062119060f060821040f0605031602070302030a1103 73
    0x1411500454a00308810022140c480003440040008010900c00c0c110400c109171070910500801c0c2c40f00180350700002c2c2c51004000001003071042168001e44006003000900c01c107030b4080540c1e034141082c4040c02102c00d003000c15000d8071420040d19541d821244507501303c0604965145ca0020120352800000b041041944203669003c15148200b42c0a030418540100f030250381c4020500c1030150042c0090300030400d0000c14030003480344180100090115040038038220036411000241650500c040a1035038009500c0c20740f900051220103d164100f84200380c031044030584480c400c8030756038840e40c800900f11100520104456103052101441800c86010003010f80010b41c0c4181030504214001402d490000824400e0401409000380c10500e00111010403c5031f01e0911016200c0c43d4602000c510a0340c00c80301004000c0103641500c02410b80429482070a0361038001c05082c0350310540d07290f14206680c1c15011101c43c40000c7c0030098030780c06400361650320003d5490103103880f6483d414641c0360 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 353800728 1250 353799478 353799491
    0xe01031e08130b040306150f0b030406091a070e0a080a15151e0506031003060b0d0c151428050d18140a0503040605070201120c180906080d050904 64
    0x40c0006031604042e040d01d03d0f155942c0c4d85146002401c698034480c00d4881d0079180b42c020480e204a005e1800c00321041d0f01d4030b0503940d03641c625101d0b00510b02c0c60401400108100005105114010880b5105d110316894410440411a08025030586540706421450380124000000102806a0900201149074021a181002c1d0ae20407040c1041c42d00b15a410781c03240440c2400302c200c081000b90040c84141c994a1842c203100d021b4203a038500d40d01001d00200d880e00707440700d041d4940d04055440300e078010100895140e1103400758418030200c41c19890000d02400038001c089500802181c01c1842e880003115103100842c58800310003803a03a101c1c9014044140010f00480c900e07809441400c00c0c480d0f405a040711080d2401d407801c12209820b030103160f4002d07000d40300020720000845040e561b0f54103009031501c11030302c01201d0901107151910645402c000c0303041204c036000781d0054141c032240e00094801c01d0710340070483d080702c00c5403190510f103070300440114020900600041180305c1001e0030120702c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 353801978 1250 353800728 353800747
    0x30a1b020a06030903080c0a0203090909030904090b060a0b1303140a0501053c0109020d230405150f01060806060f0c0706020d03060b090f030106080d0201050406060e01031e08 77
    0x1403071040d60001c40401c1d112201da8040646c0314442a82c4060300303000d202d003070080400c0001d42e00d0090700744260046200c580420503100c1c040065903032128004200b40402d044614010302c00c21001e46980340515026038011801c0030b000d40907901d14051711b0080d40885031031502c51010140f00140b100159003d80d080c25400b04900b8020385118490345c40c0032044c1880b140c4680c0d40710002c41e04000c060949411749203200d1161200320b480c1103da03541005030311001c030480f40c0c0b0000d0400c001c1012440400744080201300c200070351007920990080e010707251005000301d00c2e003902030011103504403140002e10040c04081e0250070181d0f0030040c064209400c01c1c00006c0314406c2a0300009907000309030700c4144204492a41082440700c107001502c0d00f40700851070300b1900036460240c0324032035109030341680c4003001c107071803d50200f00100002d204558068495031000303802060190307015108503007007070b802003104440da000082c100c0b070748280801c0c040d180a0640784600c00360a10101c0300d03180c041145110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 353803228 1250 353801978 353801989
    0x602040e0408070b0f072106050a080a05060606090319050c0d21020d02100b0310050103080703030b060403030f030509011d102f0a02010213180c11030a1b02 69
    0x3003940b0600000e07070380740740604141110702c00052540c0d00810102c3d04000320107034008140700701da40d04154403100c100380700085400500003a4200a411040309407000444107000203013659140e0103903055a03d90385405041c4000c074811719181c26095803004c5000c40b80751144603403041e4200e000702c0075180303980d04100c00902240380b0f0800a0303d02c00081640160004031040b034611030100316000030f2500c81c060b098007a49071440714046090359503071203000b03000c47d840c1030107070311084005113504001a44c0c5900c0c0041e21500205001c1d00080e29203210510681446000c88007500e0305901d4000215103c86004c4024010040511145548440030302140101d501d00840a07a52007601400701c401200a40d1401c038cd4141c0b4000100c034100e144110006401c0703034190f481e441d10301d0300380c0b030b6445041180680c0a8454101c175001411920b40d0005501700b08c040903105c404015800c28005006e200d0030451362151424440300d045e8004000740300c00207020319a02c4001190410310001c41c0d0103180c0026a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 353804478 1250 353803228 353803231
    0x90f08120304030e0a03080c0d02010e0c041e0903050a0f0906080a0c110706081503060114010c030522030201030c0f020c01180f2409270e0f01060e1b030a02070602040e 74
    0x2602c1c8100412204080310b01442750113008a05440200301c0c80c4842c0040fa9900c8602240701030085075900d602040000b45408a80f001c846601428001104907140046c41940a18842e1000170201e03401021164440e20782d4501326803440c1d40c0d030701c02e07900c41201d0180146640d200a03800e000460b2600c00e80100207100c404020403240d19000310501e8000d1080308030611070403880b48650041e50040c0720340401c00c2010714840c4020f10b8060810703106450306458600c03a000030341e480406444600401c040303030722403d182500d02c00c0e030301800ba14070f01500640f0340642a0344e000c00583c00102d90300e0300c0e03540f20f900034840354075100b9182180d00d65030300c1c41c0350702c40e01c0181c0022281d51508490360070b0300d011000141c3c003000c102d41381003040103142100007508442000704046c0601c94090343c000000e82c1942118400e010395000f5140302c07102c0b4114042c0240643c1c428860149828170000d8580015503218024002e010b0f102c981c40c698654444c4c10096010450071285a0b40c24000894070ba0811440b2a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 353805728 1250 353804478 353804483
    0x50306011b03021501050a1d0c0903100614010c15111306030501031103070303020a030e010909110702031b060a0302160813030b1303050909040f0503030c0a090f08120304030e0a03 79
    0x2e1507480410313882039031203810581003207002d000190402c1180b00001d07000e890303c09000004070002600d829500369150b103e06507010354144a030440400f10100307150700c80340031941210f0710100a4041d00c0c00655401c6031100700945800742c00c156202540146800c00101e151140e01c501d032908000d00000c26200745203801240c00030b980d07403006000704600500b40e2203078024110b00803d5400d155540003541e03180098001010804440e2142c00c0607409500c4850240c074210400341305070743c490200c3d04003580007500207901c40d1180444181d52144a44000d1020300d8010340050300e1300341503400030ba010307500c04100e80e0503081014446d040403564540c003812210b00e41d6a0440049407031400c283c400128060103101000f200d104080c40000d07048400c1ba466024151009041c994984c140b00e101a00c1c0c008010301039000000c2006243e05000000707281101701900e82d0000d0035141c1280400024550088194176440004038030f6000b480e41d0080e503442407191401c1c2d07a4030800000441d030a2100356004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 353806978 1250 353805728 353805733
    0x30f0c14010e250b1e0a1e030e281202010b010f17042d060f241205100e0102040533250506090105100e07050306011b0302 54
    0x202111040c1448200140c500844086540d001c408801583c02041c030f200c1d1030351400000039103511503601c404120600318800340880d621044102400b40c00040724107a0010390a00410039111141d000e0311811801c4001c6000030601440101001d4100f00d80c0c560000d2203032002652032070001965003c2c1711f900803c480e4004101c8841c81030024018014902e4110140312188218103002c52845000c10350041d00b0601d40300d10101c20850f6240d804001040800d10385c61080806000e21050f0307040b0304100018140104840e8507414442d600c1c001c10030036400d5401030407020802484103900d00180919000f50140d54440000e4a24801102c844131002e001c680d402103803c00c510300d40051721b0146085014990381c6640d0500c15510412108489802018a004034614040aa150b032000b1007501d2040d0004021100c00d0800360b6880320304031446603ca6003014002841d403800107400030100c03000300521608545803420251101d4100500480c100400710103030702c020f400d00c56441c82425000707401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 353808228 1250 353806978 353806991
    0xc0609121716050a0903020603070201240807031506170c1e1c1104060f030510060b0d0b1903061a03030405030c01030207060207060e03030f01060206060d030f0c1401 73
    0x4060401a90300300d11800302a0400104540000118911031a614180c0f070322640d501c52520003522014120b4102a41115022003044200c64056221030310182c0700a003104004211214040c440c001580104039203608040c104200003460507c001120b006814000f040e500c0d1a507034030610046030450707181074590241d0318200d140d080424007101c0401114031031140d00010039000c511402c8907092003c041c5680700c4294001c0c0440581c4481111100901c1480344642e122521984102d80f404107031098083e844504003642e070030f481030038211401d100e80c0341d00301030205584100a00c600d4102c5500510801e20000280c44032070b2011000e18072852000884c09036156001c0020344441e081e582c0203502c00c10007807013103503000220700040940900e00542d4580c11803070440041d010f401da000709583c1c10060f4100b40c606000c8059031107120302d44500155030b80c3e44d20f012170781d516085d90065080129011558082403041c401e1910024050510002c0c0115507510050400f00034015104940d55808 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 353809478 1250 353808228 353808263
    0x902030628030b130b01030206030604110f0a02010b100806010809070909031e080f062416200a05090601020307050a030f0207051206010b1303050a0501050a05011e05010f0c0609 78
    0x110860703081032290044c14038104513a5500721034500103020181c843d03200400001d2542c0d8503500250b038a24601c040c1140c4800c0b071000d04002c00d800540f400e9015508040c001902c0d410010011040c010a580e079401c5151103085c01035801a001800302c1d2004c0c040c0520200300442940a100d0820344241e5424010031141c02034011a21000b21070241007200d10301c188092030fa2a080c40c240c1010b07007214640120580c0c1035007a58042c520f4050b44020002c00700b0100700e0742c20681d644240c801d005034042c4081108103401c00d081d082c0500c021070f500a1142e0400e100d20300f07260100c26480241801141c1c60f062050700c41b249080000300b400c80004450075091410141e05000c06401010240e40d54010500018811900d486050042d003224104c0440c00c1c540d148410f4040300d0040d6085003d0350751001660a089010b404210b81c12000a410400000790921140172515a40307412450005185030074500112585250b050482040000034440e010200d001c0d031250011a51191111600f29010756 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 353810728 1250 353809478 353809493
    0xe0a0c080d090801090f0204050702030c0a0807061515030c090305030310050312210a240303020c091e06060f120a180309031403040b070803150a0f090203062803 71
    0x19001000341e81d040c85c2c1400c0c00150100b07003c07107046504507004106903440b40d50880c03950095042840352841a0300e580001d0010801c01001900c0c001c5006000c0f04042000800b103d44c228411009100b2000c070301040840c1c460341c00214001028501285810b5481d25220710f0b58006a82c0c40648040f440d104110341e02c0c0400c8060600c400d1078441e0f0781400f0240e004600b004031a041314144c400e44000004071103100729481032003001c4012211004040200e2804a03119156001c121302510688044041c40d00d010894144034034042518000010210342c00010302c00406002103410000178041c0c610b41000036400782c0180710f240c1c02e5240851518190110680f81c940322000e042e8496440b0001c0886e5101c51403905480e08094025131441170b50a0080c036501c25036002800841e008110481009004030055006104101e040800c114001c6c00f080500e43d41c81c400c1024442e04030804000840d290f401455120b103008021003800d0206c100d0001c4003000d20510300240142000c0f041c000c01019 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 353811978 1250 353810728 353810747
    0x50403080406050c0c1f0c020301110a17070e060a0c0c0b0307180e130f1406270c0108011818051501060903081215040603110a0501030905030d0e0a0c080d 68
    0x881c3d201c21082c030070b40628414003942c6c000800c100300d81d1141400c1991030035007002c00d600d40d1002e1560713034903c8940c40080c03d4110444110085803030b07000204290034410400d1042141c0000d00760340c60f01807072280131b03540c00c003004008a4112100c010006403a03145070026503c0b40c80d0a45034000c4844410809040407482c50f002001c1d01e098010501045e60000941640f1956014691050f0100d66080c4031700d03004002031410107580702c0c080c2044031490281c1d80d20025030f8102c0b4042028441d80d084480d44915035411504c0c002956140100010074001070000f1208802200015158100d10082840046003660554441c2e00003880381d8450100400e5460061140e483c0c842a00b0b42150f4604880e84910329440c00d10401400104550303102c001c145842c00e000c024010840c0981d80d20340703604141603540d11148104840040091294040e008404041d540b02d0050340c40d007010700e461400100100b945c585580d10408103c000001c0113241c0703000281c00da08000340040c00744002c008040196 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 353813228 1250 353811978 353812003
    0x1e060924040f05160b0433030b01090b070b0907060f02120708040905190b03011104030609230f0d0507030804020f01050c15041b050904080307050403080406050c 71
    0x1844a14944404030108826400a52020030201002e089040080c58860200311901c0000c0a0260004103641389030000c00031109030030f4800000e040d079140c04415181d45800d104001e00e19025200000780c2c403039801b5291103801410514002034441d40d0255443e0081c0c201208c400b040301c001e215090204000e20300040041e40b4199100f5506008002d484a98140448a90710404655241003104403420b4030007400038500b04000510700104001c403540b5140488400d030610302124640309040c180546800d200783c1039125450b051a558800008288586e0309442c42682801181100c0c2122158143c09103102001456200e11100c40c1c0741c103004c44c000da001d00b404401c00154000a0f00441c4c103960040d011108081d041950100584207403180703480020b15409200d0480788040346040f24240100d0244030b10041400c41d420710199030804a00445038004820340010b000515404011540000d1525100d41403a581e0f80d80c280032030701710341c01c05004928049400d050840041085212400c2c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 353814478 1250 353813228 353813263
    0x30f0d0f0b030c1f020111210121110d0b0c03010609050d0f0b07030902190612020f071527120201110405100e092a0304050d0804051e0609 61
    0x8904400150030b41d0b019038421801208042c0042c2d070241c5c000e5216403002c103410016155208095880304e1000c441c0d11b004540e080d070f907120010403107030951201c229071589200701d080c0c070768409500d98185d0642824a96a40302c0c00c1c3c074003844002040c5042036802440b03060030035038481d4107024029209121540006008001c100440302c08260410250a0758507001003109c41d003074440031000c80c0a080c0c0c1410203500318102e84024016180540704040803a006641c40005142114401e20168420360204100d1130f20140482004207d00c1c418604800c00010340000d00d00000c05040500210f0182030008419400c0f2901c00078030101c01d2403113031300d40c07510b10003001030f550040e800b0101806540515400746094203120f070b8805008400201d814000286003498030b14080020341014829101103014200100460460100f40030082d207009650001c0a401240f001c1036080b10b9401e4000d00980d514410080507070314404510107500c1e039103a8054060181460140b0f1520310300002c2d80050001034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 353815728 1250 353814478 353814493
    0x20a051b12090f010e10021606030b1509060d110415111507021009080307030b0d0f020f01030f09030f141305090a1401060c0c1401051605030f0d0f0b03 67
    0x29621541203400c4507404407440f212070442000100d0300c20005410007500f10140340c619a107081d800003825041110903540d0280039546402c403c40a40b000208010340002e1070300074150100e40b100005d000c0d4400040c00c2c0c18240030034544070005581c031030003039010500c40019003400b0040341d20306140d060580905040c642184924904d984e100290074840002d2030103003000c00d010a20900480755000001101032020240a04001001d0360055031030501007490b050b6466400d08003130f14000c0c2d000e60071541c80c50301c00c43d15070207020b20b4000c12000b060415a56610a1009001910404402c107000c0d1390344001e014190f05011745184400c0035011504031092002c8001c8000c281700220640d4800c0d5422129030701c89040744d401500b43d0b0801c2e8004003841c0000820a0395003c2c001da00700600800f00c44e00c49941d41c01e40c2100b01e000f160340881c0010010024642e000440000441e0710910810480f031070a050b00c54040c102e50840f2076240d0305ca13600c07203030200c40c03c4405001c0c1e9062400300320042e00d40f4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 353816978 1250 353815728 353815753
    0x3021801211707030206090601060f02060f0601021204060e03011413080f0d091a100f170f0115050405090304061b0804050a0611060a0614040b040e01020a051b 70
    0x40e44844074110040754000310014041210244058a5000707800d050741d602ca09842c54081e40380c0d9000c0300d0301f038443c0c45101c00001f05c0d03508c00c4011502012007074020b00079944030480f00f00a0010024000341c123501c40c444020b6100702d08000100010b2019580e012083d003816000c1500752410b0415540c10103c0300030600088040b00c260145815070b009240c2075070f0702a07030100f101280c01074180280e2036510b001503000500041c074003500d111082000c001d11844d0303a110180c8014008901178035584041c003840c14482c10a5080c00100038461503401c07545e40c650b00b007103410f0960350300300c105811002601c01f0030000b42c10130340103147c2c0003114000910306080c20820028440240003460100a1101304408000e008120080318080c00010b01f032011031644858010341410390348920144079210302c400051103c1040d119003802e03900310380d00c480d164413420020131016000b41181c1a42c05607944203410f4141c2e10900c0144100c0010b5196151101042900f0140c025491401102c40c2d40000256010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 353818228 1250 353816978 353816999
    0x1020609100903031d06011d0c0a0f0c0204050c04090c0306140108072105040210180302010f110f0705010e1005120a1805010e0708150112110d03050403021801 70
    0x462141ea510000700000305003000c03800b810040012201d2480c41c146070000200001c02c689040c2c0d5207122056144c5130126100c181401001c80e07103020546001e002c00c141180c401c014400d848401882c0020000000b5000a001c4800607030700344405043c0014100041881c90050400b0004a428200849440c2400c1c81c000c41402103d011304001d42c91f00000c5686010b40315825840c40c9072141c0d698100c80264847d0002c150a42e0705900c56810340d80b8081c440c503c10006260266002800d480900c0d2550380103444081030f25a1a40130300c461004002106202081907040512110005190b51450400050701d05503d00c071019009032b889010031103005800400702c400c0e80030513503961070260b515030481d10b00525840050041c1140380f15644824820150890f040d13003246403041e98240340d590703d681c541e103401c440200310540c4012801000b003c1c1c203440442c0d114600a2195118482020000580d04440d80c0c10882c040b41000c141401035052101d80140801c11007040c01210b075040c5515041c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 353819478 1250 353818228 353818243
    0x21501141f03111201030c090920040b03010c0201091106040f0e040203030403020d050c0a0e090703080c07030203190c060f0e0d021203040623070b070503040507030c061d01020609 79
    0x500d000c000d8601c5984081c42544019114103404102c540c5465405481ca1403d0000b0301c0160340503101181c001ca40e140c12071140c8022141e201c200c40c1080c1400e03034586144c0c0b0010081d01a8029038406070b50710180c5007800388907444040e0ba4000540301030503182c82c0300d0748440007400c940070301010301040c05405d80d101034000984910f0200e07a0490341e214400a8594422500700a41020300350070b170031082050020b003403610298203d58040f55180c84a5100e5601e8600b241c030402254080c59040000c11040701c000c000f000041d40a0312422500e80c0c010901e842d003020a200000540e122008080c45903607603100c00034080f2480d000b200440c0034034000b00b56046400c0807902c00c0c0500e4070304074115640e111028100b004000162a2610b0f82c0e55005090043c00d080d00030a200322090b030001030030040034102c60841d80c0c40300501d4800d44a10348100c0b0507410042088840d4030904078084041a420703645a4001c0416a6480e0001407030348800786040403841003200d040d94481c00a00c402c8600c04646075 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 353820728 1250 353819478 353819509
    0x4060b03040305220801021314240904150605040519031110110106140f060405100c020307080a0f030912030c031404180209120a030e04050604060b0a02150114 70
    0x43c80c51a8003681c0e0004032180c0e905c90000b42d0710001c0c0071a800005400c43c2c000329001480940100000e44040c0048a20006000d0741c0c0e401003a500c0d40d4031044010041c050040f0042d0001401000421000d010ac14060704090045200420104107038500303101045055548a04440441495551504034035400100001d1145901c0d14040320114400c08840c15802502d60080c040340341c0c0ca050f00d8070003c00704041e4078061904140c801c4e0103800c0480c05c4038101c0d0406442c500e00e6080681d03084030b4981d1003200c100ea16024100002402d000100041802c00c2e00900b1519000002da1402604900140d03000c02c1c070070b0301c040c0b001d100465040041c01c0344150700f40c140991080000000420288182d0b00702051010224007101442d280540c0941001901171b60341400300d2500c1a00159608011140100041d00003680e071000703410280c201d01e8000501510100e109a03d40c810f20403d50488404080168081e142c003031107015503080c44c54010801540c4d0281d02c290b004000c10300c61500d14446 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 353821978 1250 353820728 353820757
    0x51207030c0803040309211a070201020c0601031104050f060618060d1d0d020c030714030102040b0a0c0b0f0613150503030a1e05031006030506040b1c0204060b03040305 74
    0x5081858000c07451401040d901c0030300c60b0342d01d2a140c98042c00141c0d007401044156140e000100300450f009808032206960069210080203145613400c90300001c008015504654082c002c0c03040707210040240034040c510800d41c0c00c110b845002c05100481d1001070809107220101028444140c464400b11030b101c50464280e400000707010b4012584912541a094080c40e1a011200c21240c4030190354071100001c00c000e55505000da014100d945100340e15081b681504000b60400c5061b040006074040c120004c2c0026091035510707610240180c02105d8200d000ca65013002c420100400400401d9120b0441d101100036801c041c004280d22082c5881e01c2c0c0001d03aa65424074103080c00f510a541c0090400070216070b5500c42c0220010700d0301c030b41c00481114521806001840450040090324410341c1e1030000e20600c50701d4414110090100900f180760007580d074402482e0143c5070341504903120103aa01260403100075034814401110341c15405100340d00018420700c0006a4840e0480d07111600c400003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 353823228 1250 353821978 353821987
    0x9040213030212010b0102010b1020010e010c0f0e10020606010c0602070b0c070507060807080a09110904030f0f030b090103231005060a06300605040e06041e0512 71
    0x386228040c2540c01c00307940700c02d1040c251050702405400044ca2020203074000c1c8000240501071102d094421400344011030003801410000071300a09181c0904810440080b408590282d020b90848200d0113001d40002ca0200301c06c0000c85e04441034031500242642c109000c061800381c003e49400307024013183e04000030055040c0c1409001d405840c205a0032200c0c0903c5801c00c0030340107000ea0312580b811611070203500800160503001c0d030540c9102d21038588500c4016518132411000800181d54100d80c00c2855a0000555071900078200b4407451180e21200d154040c41c5a001d07042580000c041020142482c0c80400350f500d94040c80303030440e50f1100e05028100c5a01c0d00701012003021007084180c3d403044000a440c1060640c02031400390704281c952514841e11070000b2030754000d124400c070303810300491140700d07440d040b88111b10030a000c69290000359540d00e03800000e0540d544110307402901d60004040c00240191a07110390909091140403051041a0f80c2d0b499450360032082e865500c40d00d0108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 353824478 1250 353823228 353823247
    0x3171201231e0108010e070807080c160c06020609010606050d0903021504080409050f07022a060a02100e010510153014070e0909071e06080603070506090402 69
    0x40e030040e80450080000035480d041c001182d00d24894448210300064200c400040c405d182040100e0040e1030541c2d0385020b03a960700d64280d405c1c84000e409107250742c1c0d04025000c1c41a11503008c2c200f0780e612076801d4031003035450309200924006020705500c9450b40341c14801c200340350300107003203c0d141c0710032440200707203414681010703400c15402140f961424030a03030b020070080002880c000e200343c501c903280030445921170040f0ba200681d005c40e138101c0540d00443c80343e1201107040821035010204240e00594121344ca40118005400c07808403400560301286030710a080d45036005036500c1e251001d008022a203491104001402690301c02c5c0c02902444000d040d000704c5c41120400008040403900c01d207008074180c00d0309480318420f41171103c1a803800f640c0543c0032100d03a69240c020f81b455501d030350000d002c80040121201e805000c4000782d114544000822080c403164034080b2010001e00c0c91032582c82c08074060090140200401d04c20b42004200707110035a1900103442035400300755801070b201e0b480704 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 353825728 1250 353824478 353824529
    0x515090c0d11041505040b0909090708010606120f0507050703050a0e0306040f030305070f080109020d0902030f0a050d0203030708070e22020c01061202090105040e2503171201 77
    0x491264041c0c0d410500031080c03540340c0000070011150b0501e40c4441da0381c00d001c030032101409980a220000002004548800c1ca011202c4135009075040f8180c41010341d4030340a103070840390a980000045541c10f410600c00c40420310580c890f40e032030440148124036100000500034420904020103105010415550307051098130728084018000d011184030313051031300386080104c2035281300301d001904100c0044c03109845029074500b649035076211801a40d08104a10004e07410004504402c00c1c1e6445880300541c0e030400c1300d40004501c03a0080c0440200504010381899400c502c0d0909550007082480106d960000380c4590020b02480c20180c56107a0340c00092810400074000701041004440841e03040c001d990080c103052010070001c211a56407046031040c08002c0305406944003280c3d03c010082c0d4249908042884d0b001c00041d6075000b00c0000304118003014101c40e01c800d1b0b04004809004109480c84000303482c0c1c03150380326142001920034247c0c00e200c90501440180c00000c511614000020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 353826978 1250 353825728 353825737
    0x2160e04120503093d0e0c12010908030408040e01170a0204050604090b0f0709090c1e051605010b090c0306030a120905030706021f0b01050f0a2c0102100515090c 71
    0x83e069065103a4070061509140300f022800304202221104160380b504017103600c120001e000c4280007805a404030302e000c00400c07144208014191303540f25400000080c40040080d44070320312800f00c2680f19410440000f103d40e4050b00000c140381d42006414040000000360020074541c103c5010840780d445402050180c54210320040c01c51510506000907140342c1c000d060700c00c1c3c40550b140015240c2e10203020f0142da018240c40c0c000b188482d05c440341031301036412a1002c14022420800c0c034080b407a01c480a01c02c030405c681070315165941d01c408121441c0c0200b1080d0484850281507003142021070010340c8030446240010040100c00503030048960245070810020940107064840080d070703551b0042e403070f9108100301d81c0668901c843d41140e0403c05201c0d020100030107035030303603801c00710702110f900c0d0268028014602070010b24581d401c14032803400c030035034000320741e8020000100c0200350002e40b50000380007208070050300b404200f20344101c40000207020792100716a0420300c0d131103018a0711914882e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 353828228 1250 353826978 353827003
    0x7140301020f0406050a11060c0403060515030601061107050409031b0309051f0e0319030503100b0f070b070806100507020d02060301090b09011d0c0a110d02160e0412050309 76
    0x10b01280015401c0e8014000c2d2000e14419160603030301c00c0c1000d904c0c03520f03104d0440e00642c400b0780c18030090022a4817680031035440880340d01d500b00c1c60884074000078941034090703209000184450400105002c024043c5100a080c19103090243c08800d94015020205003603140e9100103150000b002494820662103006100241041d5442d80d1a0000000c2c40030308001144045010f91b100003c040c03c00140c02c400212030300f6281c411004d9195002c1340c2d00d6001801403103503a0310040b000b0905140381001003000702c000540c00c60391000da07031a1541402c40e00801c84001c1c09101c1c0304114071a120582c41d000e0750541860080d41d122003034400a450031184242c0650082d0b07000c000414031a0091303001ea650740742d007100e07524004da9079040c440408001104000142c00c001c040414000c91018002d00001c4805091800e0b084c50b115502030301d80481020503100681c04000100c240036004200e4201410300b00c9407102030351070151280e4a800085080c0340e8100440000081c2c0d4103641800444140c21 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 353829478 1250 353828228 353828257
    0x1030f050f06030d02070b070209071103030a0c0e030c03120a1704050615061c05040f0204090b01060306092007030c0b070503040506060409021e0301110a09080f0705030714030102 79
    0x24003200101d0100380481e9894028800c0440d40d442540c00081c00c1411140e5030f09281e4540080781c2c3c01d0010a41010700a1014002c3c420445101603000b48041c40c403d00100200046900e0f10820003011221030804040c041e42040e00c0e101720b184c4001c207c940c15488110307510b40e034071001000103c407a0b912400055600f801c09000b40005c0040c0403070510b024081614081c00e0828210042040e18450f0f4803001a030140104003070035121560350010b40d4440c0c0600305d840956150354000c2015035680c103e045402c4951440103100d40c5030913124080103411404002c000071810201700403081140d078000c03040c104c0b40c0422003a007050700c20113240000c2d035032040303124006040c4004080c10b07582054072b04503050700601c0c2c00101da0741080c1c403c01c0d164503002410100045c10010854502200e201892078165403200742a84036000c0f41070003400810f101d40d0b0fa0320b400740d14080c40d40e800c0034050f4850290681011000304140e40c0d001425100360303240d40481a202015041c002402881991801c0d48a203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 353830728 1250 353829478 353829481
    0xc130303030b040b030706050d09021f020d032f030a020906040315051506070b071e021f0e0d1202120403091e03030203160201050412050606190f0b0901030f05 70
    0x1a4982c01c1040300180a07242401455641d40c101500d60751140107000001e80240500e45074010350b44c010000c40d9001420b03055100c42c284003c500c00180050350b01000d0780c0034554036041d140e407521403804e91707480c00d002e61a00b101110018203001c020a0696007500c0c0c8010000c55070154841d8100c44241800820341c0d85e80d07640d40c1c580100003800030303254092080e281400144442045201d10841840020242e81c81d0070101d64544c0c0c8201000381c41c0008002c802260f0707082e0340826400f04242003103a6001400980c04080118404414505448510604290240b8442c3c000003401f44080d064500b80120101600d003058002400b03405081c050030840b400a000506810422a10903070341f2441400c00c0b204408541e240800c20300d03110040040c3c0c0200326001101002802e502155881403408600d1300b9038454404040e80c490240907203903034214400b13000741441c0421005065261059040904038a8245402c69800d03051013070711b901e95400620081aa8403943c0704019001c000c4d207003004203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 353831978 1250 353830728 353830733
    0x10603031b051f0507080f0606040b07080d1a0406061106272b03140402091008030d05060102010b100207050f060c0607031a061213060b06030f04031d060a080c1303 72
    0x84d21050301c0390300c0840c1c03180001c12581c00007000c000d842580b010340f10134605850300001c0c04036036000b008141c46108044c01000c071030509601803140d45c00c9550524036002c1142c7c20801048980f072344e1100b801e2200c03516030381520040207e03496a00c000414065406100d010640370411500d031190703405140181c2c40d940600c0e1091100c0307802d200040080059000c2d4480f0b40c1035040300e00607880500a69000b200042c01444c0c20100144d00603920420a1090356542c0510742c40c541250102c0150717283c45404000b03180d40d091003031040e82541290310004400d024200a52680e4070381c000c09000345600007109205444207022128032a080d042114510b103000c0d0402001045003030362502ca84801003052420901d009c205881d041d0400d41c0032040e07180c45820030f0401189124404072480c0342c503120358038000d9803044041d600c5030f40300c2e410b00c642c1440d0619005140940130041140040031844000e5541e4881038181d41c00d204450070f00086985400c51454054051554110010180e45001004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 353833228 1250 353831978 353831981
    0x201320610050412080406030c0905031f1803020c0316120807060b060d05040302160815090703050f060106032f0c072403050109050105010806190803030106030e0609010603031b051f 80
    0x1100e840388d07002c00c0b100d80581003c81703d00c505882a00d40c1940401c2c05140000680c640382c115220041c880000c0203140c2452102e13540c00410b0007600560000340d03507002141428006040c11190058603550f141f81000f1200c40d0404403840060300c40400032071b02100304082a842840d500c5001404640c56818110004001d064120f0301100107002d10360a10950914448002082e100d020000e04590140209031140b101002400e22043d446902000801300e1403d1006440041980300502140d6040c0000075007500c08814039455095169074036003840341c114202c00b0001c50b204840042c0c0d40d510b44c0310f28618040054100544101d002103624032000001c071803100c001d000300c7d10f040c0001e03039844d0302d461b04844c024440d450118070180002807540c42d003030311004001e00205440c1d64180e51281030789403564100b41c0007000802d994500c0c940c8020400c109540d230000d440002402410f0540c0c0d4010400407140120030301070902490f14030708112007030006c21109540004001e005080d110007100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 353834478 1250 353833228 353833237
    0x1e0a0207021e010504051207030206040905070f1b0f080c01050705180102191415010905010311061303030513090207050a110904050d050a120c020132061005041208 72
    0xc1c4666480c80d50441010b290501d03051101d031058443c1820280703414180681c54003c503040341c00c0c50145007070100040c2c1e50300c009000035201c0340c0b8001840f0702c0d018001802500500710300c00240607100215001c9180040b1442da08a9842040c0c054a038040d441c2410150040d1080c04102c1d5080c81c081028050384080584540c15859004d58240d071504001a40c4480024541c3c2c009850318100c05000305190540030680b540e01302044031011300c15624070840d02c0d40281c000882c80c680b20710040082c0f241404501c2c04105e02141c0719442c01c084903580b14880002c1b03100c01004e001c1d011030f076569410b60b000b42d0f0380010b003030462040d55500301b5031401c00e848a244080807110324605551504039800d140042500c00e43e401b40007000002c0c0b0788007094a15421031801d1400300001c45a0302c135030401d114001c00d08030404a400200700202c020010310f51031036900048640c000000b085100f54043d107920032907080002966030102c0c9400e015401c951030f100726040100c00c0341c1144504000c02209030010f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 353835728 1250 353834478 353834483
    0x51206040308010902090d02090606120f010602060703020c06160504050d1a010b0405180c070210080402040c02011a0409062304140102031e15030d050406020609060601171e0a0207 79
    0x890640e13032109a42d00481c081d0a5680d504004034455640040c1030214800380c111000400e41030030084c00001c59441188115507160310804450010040307150100903050b000f0701c82d4201981406410002e49550b4040100108000c402003001e0401540c001c00c101da0190030054062103c3c48001c0c10440046142e00072100b0000c820341c400020a42000d00c259000d548000300030040704240101d0008108070003601c1da403550f40e0100041c2c00140d80700708044500d0714250320f48c007140c0c2c0b0f07082c01000304450480b100c2600b0f590400106c8130881c806520307040c1c1200070880300000c09c41d82c00d0130710780001c02120b14294503443c40c22a011120209c00510329109a10902c003003000c13607040807006401c4c1c0c00240e0f4202c50b0b1081d9031120f0300c0380380004039060b0340c0300040380d02c0448001c8011380001d02c0c0036a00b100d90740100b1000642444130aa040c440154054211401010381d42800750000700b59a07031042d9001004451400802c00d84c5038003503007042d40203030001c8414045042c1415007000950004d50b04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 353836978 1250 353835728 353835737
    0x4200301091e0b06030106050a1407111008040b06060715060b09100504060804020d060b0301091209081f0509030c0a03050d0e210c0c0409080307030b060301030b0a0f060512060403 79
    0x608500d0b040c900898030402e1000d80700c41d05513480c0540544654104c60f42c0039092100581d0b400c03c0513141700010302011402280d0964181d03031510240618007a005841004000341d02c0d0800000c1001c001356941c0250041d03484660b641c0c2d05003003c034020000c081d007500850b4180040014a40f0f0510041c04880104981c0c4140c2121040c500b52000d1082d032080070041403140d8005005417a01a100100140c0a00b1010500b001c002000030b084801c904021586180050300b10b4040d5a408070b040805822001e00520901480180c40b521035103101141412940d150700003e0300c82e607000d02c1a1380d440c49510701180d481c511580b6021b011b982001411000551030503c01d10801c04001440c0b02180850411002402d81c01040102d85071f07000b40f000041c1881081040501c584840c490383e5039060041d050a9143c0c00d00780801000e031170000c048a846030704144018004140310000054100c400e400c00084c0790186c14202c0c102511455100341d6001c801d40d96045412480460141c0c855403180da034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 353838228 1250 353836978 353837021
    0x80a020a080a0c09020f09030610030b16080f060a12030906080c160f03050c0d051207050306030d05090409080712140a02030702090603160b1201080d0e0420030109 72
    0x10300395940014034400f80060200040c104044c0c4090350051015400384071000740350850b42c90200e85000d20503101d50b801d0700071202003042840016559103802542c0030107184550f000d900e400600c4104050215503a48403e10042520f555404071102d0041135048000c1904c42e0b02428060091403140c4100d002082c0700f10001030340d844450080f522001800007410f41c0c51b40b413a46075055a9480401c0840c240002005445c06003c001c00400703c2c3c681295880d550303507c490f15042500c0c424041c014100307005050007402166540401c51002140d20307840d04176210300380d610000b009001e40105c0600304010025164080c03200e501c1c101c144404564442c5009501c207400c0c400314030b21400030b0b00d41c0107810500c140001450a25410307600424000e084443c1d60300da141c000401008994800214400001600c00e903e6010441a600405064000d07003030325640c10401800385000007a082d4032a80e550a0380180380d08410003031410140d6a2650107807650b8681502c64000c0188620104480e1036060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 353839478 1250 353838228 353838239
    0xc07080d030f090c0b0d241404020a08191425140406050c250305070e101a1210090e0a1203180515061c0c0e07020c030601080a020a 58
    0x14401102c4ea10100d0f1800080c41c01090120580010b010006001e0f2218600c02c000608000c40b100400e0440031010b030003900d001983c0350324072100104640110f00602c44401c0c002c1e0850302e0070794001060105000038140c1c2000c15001400c2c46003070764407207000d00014070036821415030400001c074220680c0030340d40950780d80e401c1e5032031820303c942800312480401c01848101c0c071540c0600b030044140c0c401c840e031440e030001c142000c60f030200e050210f401c102c02404000388941041524000c011002d02090701e81009500e002c0754540a004150b21038003009405010055100d088416110000c850200c0324104101070280c501441e10601d211541400150801d940c408500c1030307980c0f80d220058411102040314141c01401c8000384040c444039660b0036405c080740d014858440702d00c001c40700c2c240d92481c0243c2001064000c038903a08941540c042941030000d00c05200c840150f482c0c04468214540e0f484408070301d801c04410300300c0c2e014052040000380e5118002401c100e028421200f06100d2030f11034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 353840728 1250 353839478 353839481
    0x601180806160e120a021302070605010b120c030907030f08040315063014120f0d06060f0215040c051c0c12080a0c08190806030c0f010e010e04020c07080d030f 70
    0xd0400c14003500a040c5c54801842c014407407440c09886d1020143c20a0b08580354001116002da100340d00400001480100e03142c0103071718055124000d20714250131420b080c00d4860b902d5a06010003801c00960a0060040c80320342000d40b4025588804050584088110080f018002c80e1040318440080a06c113420000381091000032290340380c00d621804416141c403400c00c1c3c0c0368501c0c0824018094400e44012032055000140741c2c402c0300b80d031101d1b90b8000000b6203200b101d41d20790280e020804a02c000006642d4081048620006101600c00860302c0d581090040c41445500c070380c2d80280c26103c60146003103070130441c2411501609050105a0b1760312400ca07812114944001c0106100b007001d0110180200000c541b0b9500610000e800c180f4940749540f540260011001c02049010041010525003000030100100741070380c8568181d1400c20019015120b402c1c062814000e410342124003a49403941030b0760064a0703041c01c84540c83d60361100350342c4501c18010304038000ba041c8079400001c996103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 353841978 1250 353840728 353840749
    0x906021c05070c09091b1d010608070e040e010603050c03070317030c07060212040605090f060a0b010e0301090305070b100305060c07050114160221030601180806160e 73
    0x5103015103519088114212907540c031080080b0340c0103070750403008075003841c0e130348910550b0501c00c1075480e07568407059841d1151032405611070340d80e442c115108a03411003008034100b41181c544d030620705c4d080e844008003500c10b43e9222600d00d800619084000d011000c0c1500031000b02c0f030080c0181e84005001030f080c152600903e0001074451000760588400c4905140010b5a2203030318400441e0401c103450391100c080e42d200e096130700c45241c035070018007040c00307024403039030380c00070900401041c1c000410f1110302d4507100000c0219083d036544160500442e4014000a280c0c904020700800448000f4a0041c00941044006942c0c0348071000c0001c4118440c3e01c4480700b520b401c2001080141c0e80d200008010740c0c8002c50844d01950ac07031035017002034030318960780c603004401c18456000b10b2750f400d010003032500003030208d4901d48030641e0321140b01c4504e107002102e800440c2031074034100d28500e09000100f00c9240b6031010007248651030420032100300e00c04003182400303203d9841121450406040118001c04c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 353843228 1250 353841978 353842003
    0x302070f0c0f06030e1b1201050a050f0603010b09041202011d16050d0c030204180623070203160b04030c051c081008030316090b0d1b02060f04030c05070e070c03090602 74
    0x6c10801414030740c20400c10b48900d0005210940c602d13030004a06007501c80a9400203081c1c0d4823041070041c45171300c2007032107540100e06400800c800c59102c000035410360f00140014003548519641c1002c143c0c400c0d00a1040d2041074803401d05010405181035944070341283e4591030a2000781c0c4040b0782460034644901805801c00040c130b024030b0458082200600c46a4103161307455120714034100010b400d0340100c0c880218051005890009182d03945c4440d144000d00e20000c54000300046c40640503d00d0304107003240d030080c0c001d05140c0d9417850240c83d44040d0041c0513245100f40c8035405a003209504201002c0c00a940e0b5045040e1a0f03d42d0711801844179000305803803900b05000254030007a0383d10044121000c149041c4d514240d44074544101580130500e80103007da103030103000742e903011181c884070704848086c80101030b54a440c04248243c1c0e400a40001c04204104500d0f8051280800c2480042c0030700ca11504200c0c100702030013802142c80b581d02180402c24660000031108d0000c103003c0720039403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 353844478 1250 353843228 353843233
    0x50712020d080f0702070f03080c070602010c120506030a23011a1008070e100e0109170604030f020c0a06080925090b15030702010506150c100c0302070f0c0f06030e 72
    0x3ca403072003a1009040010004411441030290002e08039a80004010086002e1100155a0850389c2603607801c0540c5908803c05680c180b841d18881d06a019040004185200400054940b20b98000070306140034140f000c0d011045203810328101413004649800c4951100000700201c403447e034100410074001081007a0300030000c1c0a2021540d0190302c0284c1d02c4001860080c9103d50b0140019a4a0241c00c2545001a10410001e4441e50304078115030043c1203540ad00307078681c0306034507000c079540d1400402c001c0c1000040025403680c0ea00030040c29010354001419544040d03140c0200511080c004c0710050803612840e11850450400039070440314502142080582d070a0130290644d000c3c0184074240e0340c00c0104210a8103681d0080b0010b5401100c441d03001160030300b410401c02070404565049140c0c070304000c001c002e8502d40c0001c1c00d1114101c4040c0040b54880d00c081d801d4000303014050002c0e1a030412040d0304800c01c611040150141c1d00748c0420701140341d4903a90102c048070302402e003000c40799 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 353845728 1250 353844478 353844481
    0x80706031109130e0604030518030a020f04020c100f1a01050702010206040201030c1b14070b040f050409020604171f06081b0a18020301030201020c0f011709010f0c050712020d08 78
    0x14107104254030612411040f0124080528402c403a2824800321801c1c0d00181b0080744100c0030901821100c00d003040308800520601e50550000341001141005491045500045c0ca24040000f03200300d030300c450f0346100c00300300c8426620320b800c000d01b1546401801c03240390b520780a00c07658081c01c00d5a12071a0181d00504280d0303650740c0190300508070b09105405108801d40032a06501c1d42c20141c003480c9209144021402009542e2039160403425080035140b42e40c10f000902400300807200130811103a0454010500035418000324030b1078407450f0004255503644407000345903403100081c9107a04002d4203561088450b041d5480e18202c44860280143d56001030010b5058101c0001d410b10b2141c000038a04d20b1071640d43c1d20002c00c030b9110400d03e50309964012004000b5581c040c0220b11030300c072080d0b4039a9010004440000d1010b01c5010b8076402d030342044000729011640952200c9284402203038204652411200050b045802c1a00d049035403c500c1904000d86920110b04050f90550f0b81e100c1c2843c0d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 353846978 1250 353845728 353845747
    0x60302040b220b0703050c0706050a1d060403080f1201050103150501111509061f06050a03150b0c010f060f08120a0c0209070504170705060d0b03010603021305010807060311 76
    0x22842c1400c050b46500324000c40443c188040d10028519148070b5140c0556940b000fa5425051a00c10ba00030820700000b41700481c18540c00442c07200000303400303214141c02600d83c20002012402684c00c003420504002c1825803180c1c880c44000c01c00c0364007201641d0841e07a42d6100440c20760304145003039408422110340400c0994050018803244580000548035820b2080e1f2920b05415000c59003d00d19034401c00902148840d900700d06d48100b20303d03044031440e65080c244060050300c56030803e1070405940b200c007116070f111342080580150900d10041075441c50122100c5018103005c010707841000f880c10100099211100f401a4202d40313210000e04010000c40032001c400c4d400c20211074041c09941500080140e035a0503d0500c50034858484c2c41d00d49041c03515604050524001c1c0c006aa8000e4a01b070000b0307907500c0b0980d641480c1030100030030300e22441030100c0e015160552000b50451501c41410740c003030b0a070b9001a07040c0d4610704104c0307424076901d0104038252414203814207006082004103000c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 353848228 1250 353846978 353847007
    0x30a051810020904020d0513030f020d0930050714042708040f0b1e0315060d091403190f05030103030c0f150902090105030a02010e04150f08010b010207060302040b 72
    0xe5100c00504c0142021844c1c103425060b03800032510281e0780c450001c19402016046039100c0c1814080780300600e880c401150004d40030020a000da104100550481d00d8428180c2d1000744640700400d00340707080c000e10702e0702e00143d40c0c009a00402030002c80300c0c0c4038a6a5400c00d44100c1106d164880e0191040410903c1d0002900500d104103685000c420400881c4220031801030200401984110766030304d400300c151107090b600c0d0010001c00308605c10000c1c000320100c50130b01c010020200f11401c80d52443d00950749001005c1d80000105001c4040321280061a4040050100c01c00d0000c000302d1080502c01d0101d81c10749282d00c640300885c4003030005102003846030040c130802078401d51083c0c9001545455481060f042d100313030800503d842e00c260108604020790820300405003600104a021080e0b03002a04030b4440e180346034010350f60b506840c048000320a00841c0140340c103c00b4070714903035241c00d0080d020b0000b110256016200e41c039030000c1c421340700380300f16000c54910f03e81560500103011807a06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 353849478 1250 353848228 353848237
    0xf060507020c0d1202070b0c06010e07081603051f090515030703030f0309020102030922060503030c1f090b0c0a0311030721060b0f0d06050a030506270d05030a05181002 74
    0x1085100e00840411041c1107c1d00429000070328100a05040d85051110407103980010720507400c001c40c40e02444454050007400ba00d071109a4200400d89580755042c1c51400011103800b1034400a040c0e00025210407140d100600a0b00b1383c41645004264103414961f031540c0c20b04c00100020741100046a14602c030b5800383d04001e10500c1036914240314480014025039440c0c50321410004044041081650140b081c04006d10040c0c000c0c40c10001070100b019142c0e07a002c5140e5000315140c21407030007200115442581140d034400c4581c8010f08102c2040c40050b0002021903011a01d040700b6841240c0c0e0303500650788541c0c031941c4c07401c040045003140e8140034000b140e010340d0155152034010980c5108200a070902542c2e0f502966200c00c0015010701c01e03525554030050051001400900220781e000c110140d11988040480e90291038208842ca80c1b2690400b0410460080d240f1a101ca964000002c41c0504207a5006008584808000000d00d00180040704038560091608103500002c640140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 353850728 1250 353849478 353849513
    0xf06090c0d0804080109080405190305030a0f0c0b010f06080717040f0f05070e100902070807032105070512070206090c04050907180212090a0803040b04060e0a0f060507020c0d 77
    0x940c101039a6107415429104484000c40d03081c40c0100b2300340090300b09410504280e20100740d10020301c03451510744a840f446004960030412041000c80701000b4000c601c0002e49507880884a401517943d040d4590028540d4040c00340021070303080201c1e40f036621641c001d07121050707540541c40d0142c80e1543d6024031160040d00850314a003c0481c0200400d9042c4010801040218009602850200e801403800091608103049882c411b00500d00800d000381c040e00c00d002c1e45410001c2e00c207651000c203500319a4400c1850103109091404014105034883d0241c10903e40c0041c5285841d19000e2099846d000222498071007640304120180c2d01d8030b050b40025070845000c4040d2910240c4440c68032040340001c42102c000b076600003032081c080c51040c3e18000e900100280140c1034070030040e038400c0000c2c440940003411001c0340f40081402e1202030f0f40700200b81e081e4007040300c1d81d84541d03290000d003105c5c0d1607400366440751a1000003040c0074008201410440001061040d04d01ca030303031356009202545070009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 353851978 1250 353850728 353850743
    0x909060a0b04260a03020105070809030a050d090c0b0d06050108010b0703020303190f06030c050306010f150e131811040608030d090c0302090702031e0708040501050d1509020a020f06090c0d 83
    0x14807040b05108031200c0c45d009038004a405d14000c14003030408c45001c0e18030b4403e40d204100d0240b02e41d5104082e698103480b4842c0215180005080000103034100760064114008009039408800005034854003c0724000c2e00d494585070703a60b001c11b000f940252030010b8050382041000034101c03a1001c0c1c41c1d003a1000e054400042110403d1180b1085a2140e0002c44640861000c18481491b042042d14014151908551140341c00c10703404449400446200f101806500300d044140c6a8850019100c2c0410340e00003004075800361420f03410560004881174440d240a580c004850381800e000f00402c0d94480c000030f61070308c0c0f00011644020b000b07880e016100100944400320040c0d5480035580c0c0151100e074000e6440e03042c201d000e0020f00040c8603501054400811000000034159002d03102214070900300305807945041c80c005000790603a0300c40718607401121103012031100d01c56400740411185603802c80322000c0c404007440e50380d81e40507a40540c1c180d200d111124810b00d040105030307017142d204452 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 353853228 1250 353851978 353852039
    0xc03090e01080d0305090616050318100c0f08060306151507030503070215100603050703020c0607020321150603071e03060e15090c1305030709020909060a0b04 70
    0x209020381a0082c1c0040c0601d810007100c0c040c41903814080c440e0046032400c042d128034103142072041640500c0340e4210040c0a008400130320103064105800c1414002001500d55040f004800400207081000d12040800e0a00900d080340500c0b4485c0076101e02000750080c400d07a226001c100100b04440710456038071002c0c00580b21030000e0404064080302d8801e8441c151641820348020b400c0c0036290041e03181545020040100b60904500098111040c0d818005201e4441080c114068810b1800c50251792088a062100307955000004080401c0c075180010700c03251b03146d082002610380648280f40305214451405d030380c1c0d2809400031508071640741000312060018510f681d401a800c0b180010120b9600c880400849000420341580003001c5500403110b00921070000d82c2034440030b4a5400400300104040901280114126010b4070004003100c0b0700583d610071f006d000c4c0d4421301c100c600a106070340c080b4116081031507003203050304d101020b100e00f024241600f4440d070741d4200700040046e12a644 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 353854478 1250 353853228 353853239
    0xb07031d040b0a0e0f180309040507051204030e03160506190302190801031b0b1207092d060309230c0913050705060901230702030102120708130c0302010c0309 70
    0x410f0004041c1c6284008082c9884400740c0544400244040e050f01c011030207010f100321000c012107000700e008803800036880d21407681c112080c0c01000c02c0420071036069030602041c1604507030321500340c04080b001c403107049040042c0d01c84c590406200321078220b44c007440f038502a80250035058140088a00c3e006080150140c1d09410108640c01d5000124196100500501007001e00a801104481100e519914645000e0b8081482640c030345224814101d0080741105200b800800b0080511640c02011102e00352040048400d0005007218400c2c1c49880c00a00c5901074003c0c648803d030414541c108144200c1c0302041400001c040c5160345018a414007492030355075000c1540618803080700e45074800750a1500c80c3c44d0045a0300154802c90342031044003916a8001208840d03120891000742e424811185280800e02a14a00950550006c90030410100e00c101045100c0d02559032214010744039890103407248260307010043c2401c8c0342e03040c050001d940240c2e0645840c1d4841d10b004d03c082540e84 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 353855728 1250 353854478 353854489
    0x609030f171c0b03060c030402040203061809010e0f0f03040501050d20040806150609062b1515140f070501141006090e0109051f0f0f0b07031d040b 65
    0x26800304082089a4010141d0040e40f003403628a041c190300030409401c004040c203440e800010402803086e41c0000000d0499126001880f400385d040100c01c14460511044844c0a8101c04e84607514500c644903818203103402c0066039074900c41050001e9850141400011611503201c420422016034556541003000389903c1c4001c9048819605500d407a6804c0291040c1021005040c94940480c400340b4142642c6d508000c0343e220540032281c895640c0040408000510b1030046245801d4030310694407250201e454020098007411285405a4181c448510801d060b449920f0703580010b071031120480c20f481030200145075207e280e43c40c2d035040c60f443e5600c26082d9103004246441d07603111001800403d461240000001e090700b402c151100c14144110155400414801c1c54a41612030b00401c060302c005440b21a10074819441d90400036403500e1030900648030074414a42002c6001c4400980a84d942f800d440450341d05aa64048400301801d0440c868418850010380c0565900c0e20321b103035035844 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 353856978 1250 353855728 353855737
    0x30b180d02060415140a0e0c03060c18010f050703120e030c070305060601140d0507140f1314030a14030d06093e07150204080606040f02040609030f17 66
    0xc541c0140700038a89071403c240f0b042180d000c50b00a25041c00095203025915170480c0754010326480d0005800b40d0070151140c6000c0400403000d4250041d60207012a20429600911a003415508043c0b0408648001114118030404020000030070038421000001d110f100b0184100b403500d003010900c1001088003600b035070b0201701500c81030b6211040401c104002840f01603845030007424200f0404200c3e10320083d05100e034805d045c50003136072400002c080600a90a07240c1c040f0300b0000c46a19105255540381d6560301c070001c04e042980a0b000300103508440c3c0848444c8001e001f40c0a04a07202c00d540da020b403249094103e0484034001401403100040445c4600d100801d085907020402c0021310391182044600050b8000c7d01311021a0806604440da40c0f14040d0900c684043c243e0303e51039414135880d078039003c110b41c0303180900004001486400c0000e150b8000e150880742041100d58000358542244100e01c01c913404aa035080d0100302140928602c4a100c6010b03040120b0015402d0034110b0241d4403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 353858228 1250 353856978 353857003
    0x6150503060a0905130b040c0e070f020105060904020f0d0f080a0201021315020d1101090611071101110c040f0f02031312181203020f16090e07050901030b18 69
    0x40200400c4041e140011104005002c0c072802088182005e840c0900841d0f02080301138040d00307000020a08101c5c40c204494014030030030001a071542004003005100100c4198410019801d20000c19803074a880c00450f805039600070518500c0100030380c02e008201820b100d003034402440d000c00480104511400400309041c41e503000603074503046410760300310300441c94100501c102000500e4040301c40d000920404100c07218281201d0b030300d24010706170b80948490007008000c40c0c00c1000650700301004102400d4054407805c02e54482004117001155803007800c0120704132580c01181400e600b41011390085030308494460700801c1045005060700e00b81d87c420390b640450010740041040900c5204400f1f02a103040610701081250482040c000c1070306544d002c0d5102c810f0b40f00201e0300415000f00200000300340f580090b0b40040b03d11000c0c1d1440801030741b1940d103542e0300f0b0041ea07500e0b0200114043c820b0b40c0009002552036400c1d611404440c20004111400ed640e01c2c101c02140c1c90b000b08126400300a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 353859478 1250 353858228 353858237
    0x201092403180b07110f0109120302090a080a0804030c05191502070f0b0309010506030a0803010e061f080601081501021f0905120a0210060302030a0f0302010219020616081003060504060615 83
    0x43c045c4d03460910340f42040c401001c041c0d243c480383c00b0024a807140215498095403401603220000000002c00904080e4000302c170601c19104070b8800c010034180980102d034022070310100f50315542d4081c084400c4910006030020310764143c0c24000000c25074040d404249692045440c500c1d16280758100141030741c1c100c0d04503080b0200030014102c03024069180d0100341500030303240d002c046070303070f183e90501040c0a818040340b4414001105515280c000c410340703500c1c02c007441e040b4a540c4907001e0608001038401ea80000c01040000301260302101e0900d4401c103040c0c0c002d03c3c00d080c44001280099103210032162605480e203004002081e001c100340788080d02d02000d0795641d9005d005000e860810142d00380b80e00c06e8180881040569030204000d110550041c1e619034906070f070340c50102e00901c20007400519491503e803403c402281e00003402c0344901c0c10141d407000400010941610509412145220143c0041c0014000200306030099a00300c4d1140034040748a41c1c40d10780e1014130548000c8040b0000c3d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 353860728 1250 353859478 353859497
    0x10c060f0c03020414060f03153106080303100b0306030c06070302030a030b310b190e0105040e030a141303033b04021b06040506040201092403180b07 66
    0x9965070f0317880e41c0c0301c03482c100c842030f00d0035202c282107005038080140043e1082d22440e165074101d884000d6001c2030003482012400103c0101c4440c0d50001520480f903170341c41850b194000c1351031640002141d0160044c141840880c83c0750003513902c2d0590000380044c1d052301482c4540c807442d032200400340c807010f4425009180c9407030b40c03420000c086410010324980718860a0544085400040d14109000700705601b4056901c3da40441d94000b804510000079089003801000b02e5200741c074220420240e6801c820415250f9036101c0420003a101d550382000f80c140c00400110b641d4034052101c5640c070f9100c482540c0c0c00e100c181c03d05000341480c580c1c0300741c010603003003000030103020510407000d480c600c0300c0c1d80030040002602140380300102d419041c0c1360041d680010002c903c0b0b620360035600c6802c40c4030411284d40d1700c0c041c40d1041e01c50f1030698007240420900800810002d0b000c07c0c202444400b100c07180560302c0504070044000d000e2250321115203801508019021603049060903200c0c404a0b2141c0c90300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 353861978 1250 353860728 353860739
    0x3120a0c12082202010e01050c01090c080c04060b0c0303070e030f0703060b0906030a2a03050304080d030c050a0e0105030c071e170711040f06170105150103110702010c060f0c030204 80
    0x8002050148907040d000f11a103090050307803c1590380400200c28a05a9100c0040080d5240146018100a4540380e10002c1c0000c12840004155489030000c1e01c050268a950304015201e600030403108200540042c800240920310034900302c806140c0083c1169180855882c3c41c40c148081074106035111600c6240070841070502c01e6034190060740c250300424813400c81d43c072080c41000f4410450307292030401c641c1d26900d030840d20001c400a540c00c001541c2e511075981c082281d64551001e090700220342007503e083c004501441c2511918070444e140e0b601105400c00c011580d0f540014007010308500f05016020124403500030a01d641c100c3c0c04e0801c02d020001341000d580040c03803402c05d00c40b2001c04200c40310005514944c005100681981d020801c401032901400182206400c420013044111007440006181504520b000c3c008910030780b00d82c40c0c01e040046052f40c0700c9140c0b190080c002000303100010352085500401190080a001905003a06260750b819607600f840a20b00194011900303105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 353863228 1250 353861978 353862001
    0x120709110903100c02010f1e0b04110315041d150c040803040e090712230a030903030809010f05090d03051807051513090905150603120a0c1208 63
    0x101180c9844418184146800080d40c1c071000b9a081c1240a911800030846082c000d4115183c5034007128018440301c6d444006924855240080d18800603080c00101052070820f8804d0000f8440900303070076455035648101140c9200000c0c41020703045a61035081034010040e11000301e8905010300085e0103603484000c407540078810b01802c4d65600c0682004204001c40000003250200c0d00d1000c000701c00c0b941c1d150001e0741811a15030041417034610320800801000b41004e840e501480e00c1c8224040f002d01c010b110700b0790718507102c64012301095000400b0b00c046409807010715842000900080b440c211420403d0065440c01d0b03d03d0000742e40200301d80324280d03405000e45503002c4112240100c40400d58614103a8654080c45114062000382e101c00c0d205107182000c03185004003540c003014035156103a500d0002003031048810b4910b8040c4030902d2190781008000240146401070041540355201c000941460348444528402d1241c04c2d0130fa000001e0105003492217248080d1102805480c0807104404d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 353864478 1250 353863228 353863241
    0x5130308040b04140f0604051203040b04090c0909021206010c1511180303090307060c050312130201030605031504060e010e0a21021606080711011802100309081603030b120709 77
    0x74403d8001702218040380c2c4411044d06c040f10000c540360a00c81070207140300c0b404c1d4401c0360031a11851400181c00300701b4040755080300c416401140d907203622896803440444200d00440d4070341c800c00140d101c08205150701c43d43c1e9a00005005000380c3e00c44005d0072010104079203103800c180d44000c0300455400c111002001c50101d031080b01750051442e001c2c0000019803101542d024850510070b4482c800801d0010800503501d46a030130400748040e60034104800d03c41581082d004a000a08103000400c1505001c81c03144070404106126600c2600c0d81d43c3d92402800700c601017400c1d550b45c0d607031801750f6503507007001140c110381e0007408400c1e0f4503550404214100c0108490704c23003d40d44459445848010500c0c9aa02107800700d01c1d0030142c0b900d501030100d82040ca03e4a65a0b00c1c2d41c00e044080d1022440b0400e24880c481c0300f01da8800224040000603010b4840303a510141c0300740313001c2c00442e4a00f41c000c6804910b21748246070003c0c050301c910000451540d100305182c0d215030b02c4050148119041071041c031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 353865728 1250 353864478 353864519
    0x30703271208181c0201110301080c0913050c09060303130620010903090b07021f110706092102040609180c06020309100c1a0702030703120c05090105130308040b04 72
    0x503141038088001141d03134207408030743c44003d448201c0c203001042e4400c0d40f00c1e2012011746401d007507407540d58014a41d910043c0f410740318801c09031303900410300300001084518103030384e03000d80074058032445d0608010710764200520340c980500080003046e190940c01c1c00c41c078000e4074803a210440307604103840100d80360214254046125a142c183c81101090304010040110b85440444541d64030051000c910744e0b194994603c0a0608540304d1105203a0700011902001c41e089801c40e940c0e0b56507240211201401441498132214904011015411300d001c1c2d415403460010b00080388296443c2c10703a4007202ca100300710103840149154400200820707601800001c015a10045082401c40b1001800348807803040c0341c00900c00283d09607010804400340303114200301d2900c0d602009180c00300c00079480391300100303046002654844095601c195984034295211034950341d45420f08800c1c10040d0f6050703203e03a000340918407140800200260300c0500074005080802019900ea515101003520000e403060080d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 353866978 1250 353865728 353865751
    0xd060b04060903020904030909020d0b031c0801060e1207080c01020709020301030201120f0b130c12050f060405040317011202040c03180206031b0f070c05011103030703271208 77
    0x1040040d0b440030402c800c0d01d8049a03594082e0700c89140c10307100c1c00450317802500440d001184400d03c01246c1c2c2d1040704a80b800340c1c01e41c0d0308484405500901c1c0b844468000c0b020425034001401032510814034000b81c01000b0300348010b40c1c424840780030b19181440e0300c043e141d035101d09851aa156414042a401454014415801d5504560001c0e10780038801110643d03d550b030300500700114500d9042a0040000900328034900c003401c262500240151060142c04103103034a4a40031034521600c126803003041e089034803900300c1c1ca0b40c07020000030b0100900290b00300290b91948a0404807100b07102c41c0200548100c4040382c19284c4144810344069148400c281031500d02c220030ba213501d111003841402ea044603200d50320360324065814100c0e01907502c05407400e0004500807001d60340c81c83c010001d440c001c0766a9050507035500d004545180440c140305003d034200703001040319030380260044040200c401052500503019550382440c0c440109000307407640c1e5900342e1900320154001c0174840e00040103884 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 353868228 1250 353866978 353866987
    0x5011407051203063f0a0203060a0b030f06070504031b0e04230a06050a0b0904080a03050703090209090d030f0b0d0b0402030307020a1e15090e10031203020d060b 71
    0x44081c2c9075a85400c1905a4201c00000039695076542041d0740000d20001c0b08140115100c50282c240c003c4c1041851303580e000e0f19810084500d0800280503481a500038024102030707481444101c064000402050b406116003030b071040c0320400a0001c01d100d200c02e9515542c0316461801d00d40c801d400c466a030300503032482d200001d020458840804590143c3c01a9800510903201c903400c00c0d11045101c00410a4040c200c0d01200300203842d0043c40c000c0366804401e100d41b0211600b000031a01007a20000d00ea10020003502c175440d402500581d81c840d850381000101141e244e004682032007402c85580715540c100342c0010b42020f41511641c0241003680e1400c100450404003c505551551080549045842e800040c00c65800b0012600c586501400b0242d07059a0b4000300c000454001c058400352506004012540b60b55803400441c1c18542540d54581e16803038900801409a0060418401e01c00c404a01001240080c000e201080c038542c0d170016658490034903030004845981d0403c5404010401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 353869478 1250 353868228 353868233
    0x30c020d0f2613030b0907090203090d17090622080d0504120f0509010302070501021326010203070903020904020d0501090803060f0906182205160608040b0a0c1404080705011407 78
    0x2983e0043c0ca074095008440c40d1112020149810705d80e5203e94001400001004482d680204844407080c82305d8590300034003840c540c00a405c03c40e04032031001480d802040000d0007150800c611020b241c460b00c9001c0741c0c410043d2180c0c030947d44864114200c007520341d0240020400d1400000310b80d5084c920300000120500400201580b01e40342c942410190003040b00307070500c0390030b604503280c0040300094018a10754174040202e14280d44294490390300c80500390060300754818002ca07803107a003c0d552004840340c00e51342042000e400140c0243d030012280302c20b0343e00040091048080310380c0126900c0c3d8481c50300d41c080210684ca10010359000d1010710040c822283c0f07840000340c501001844400d00745944500000244404040064100d40d64072540102803050110f11540541400c001540c9d441d92240000d40b07003101c09440041c910010600003a050310030641c00030201450078944115110000c410b0384805401c190441507050b000441e00700040d40e04030183d041400040c600f20b44c02e010458 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 353870728 1250 353869478 353869507
    0xa17010917031005060c030405030a0c06030509060702070315180605010e01050a05031f15030c0807050603010302060a0804020402040b0f03010e130803070e0303040e0a050609071b030c020d0f26 85
    0x181314840c003c1001040e280c83d004418070035200a00805030490322001c22504003030807890743c80d1241c540402c0c0b800300469101c200200d41c2501c150844c1d0000e1820514582c0c0301c0c5070380ac41108003000700c2030b0740745950300c000800304408881403030041001003007a504010080e007004c101a07000c14032404e02d00d042041640c402151480680e05020b4040300d40c1c42c506030750807015040c4210504100c1c40148004010002580760900950300c403102201e81068443c402d001d0903120a02010750710007014402a40302611032004942e0291000c0c0015003055951a4155500d0b0004560300300d0310750b070100050003105004010713544e00c4024890a9440c034100342c4c564283d28440540b10000300980244681c00b144ca08100312002028a901e1102c59482e040351000700600050310980d200341e03a24008203211a2160300140c18030000d8400d008650b1a00b950140e517030f6810700c0c8040f60000d04407a00400490f41940f04400050b001e0324800400c12800c0c5290110140c50b081940d641c00d1040c007114034904c0d2403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 353871978 1250 353870728 353870761
    0x7030306050405100b1608031303080a1e020c072102090903120c0a050708030a022101050a150e041404120c0b13050a05061602070524090a1701091703 66
    0x40030740c000d60720700300c0012102c2c41001c40c1001400f262400020700905003c1d5810709c6060b2030180d901d00540307486034508802501c2c6902c00700c9440010494074000807590030b500074200f1800725001c44070980d6035000d00840554503112008107000c0241c00070420342c1442e203001540301912402843c6002d4080884440d00c1c00f000d00107540440c1c000c250415018042c0d01113680454101742a0b984914103915528040e40c0700038044440c4111003802e00c8401660307508901d06899005250718101d5003461542ea417038448200405041002920717840d0145c2d04c4512440c0c000387c0350358484040d6031070903052000443d03d114080c0c2c000c00468210300c1e804100c0380800300c0d401c00405c0c1d02105070f003e840c0c1445440c011040300c020308540100801e100c640d850384902c11070580019002e4451a540c1c59081200020300d2030410048050f01c1d45a4052070940c1200070704003448000c0c08540c01d0b83d152100720050f40400885d8074103da641c1c500e02c01c00e00001d0305400d0240ca60341c41e01c0b41d1071484e1102c0014442001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 353873228 1250 353871978 353871989
    0x6040603090503040306050a020315060c060411041404060905070f21030e0613140103090327080f0f07090e15040c080a0b06090705040806390703030605040510 70
    0x307841100c1420080180100c40080d42c015106010700c0c2040021000298019205038924104500c88440b0b41d0a0401c01d03a1400780c40c0740084c02440d034407511545407136801c01c4101c41d44240e45400030a944004000c2041c080e0340150800070340880e151408501c0c003240764000100d19504010f04020000603030405c26a0084116921a9000d10713914060f03030b1050b44501020f900000100c1e071401ca080442120710300700c41d090082c1c6040c0a05480c015412078441606c05400142c25034526809480b820050030034500c40301c091424566075941f070180c180f1000c1c0c0f20b9601e03150050301d0090000c00c1d04100d00c07405013031811000c01001061319015a55190074000903034403201c594000900348400020701c0b50040c0b07803100a03984266554a03080e4087c00c411982d0ba072283c0002400f041c0e94510443c10f540a581c280802403a150b22400044071501d1307400500710050f0a01030418004d00d40c01c11031204900401006015200e208514014040d1241d5800440c0610314110800081d0300320305605408a50 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 353874478 1250 353873228 353873231
    0x80712021305091f151202010e041503060917120a1518050a060512010204030b1005030a0312090f0606140d12051b01180b010b0307020304090c0507020a0810110906040603 75
    0x1801c3c0b13180d04085c0041e04420301d851900c050001860f105505110307005180300b41d81c0d031164070300940100011110301440510400d43c181c4024800100b20390701415080e8014109c103030407008100c41a0b2455405900c0304ca03036030000d0b00280103004c00640981840c8642002088101c1c50410984120400880112a209a0320794001c6141c2e2680e5a01c810090200607141c2c1007040f2401032024042c3d8424803084542e85801030019170220380716203402080c2e4100801511900038161001c030b500320782e141c5116400039078480002001644e40458100000e100b03c20119001d460540301c80a5203a08400d41401940030183d03100000310a00c80e00203044115083c1079441e07213111b0340301c44030314003003580007511a601e4000c4074031440c1d90313020b0801c80d04c034894082c0e10516030300c07900030300d03100c0c0020b0b9801c0016a0092000b0320100449030000c102408240c9001c50402d1110340000d44080070070b80c84041d4a410a514603a15500d8070b00030003030a041d0700e00b1007501d8402032001252191040388101002c15 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 353875728 1250 353874478 353874523
    0x3030b12010b01020c101b0804060f032a14070c06030f05330409050106090c0903050c010c0f061407020615241b03130f051c06020408071202130509 65
    0x1103000c0c00040b41464048070b85002c0c1f141162601c5d0031107522a00804001c28103606407807882038800d01800348005604141c4682d000040c03288490301040b4040300341c00744913840404101d000e1400b0081c1040074061002000c00e2440d06801070111181c0c03003441d20486081008100c10f1994400060b0050030bc00c0307085540755500d82c07901d074071000740d07120215070701904000800c01407040c15080b210958030000c40411120070341640a940c110381500c8000c20725000700e03030401070540c003500ac000700740c5e40224016444000e60396201c0e0101c1c0e0103c80e40740d480e13140020a001d10f141e41004055400008490490505a010701c00034900100405441000340740385d80c03c0401e00140344040d16495584070440140b0014240403440d00e80e006555901c060001c440d10000d0b403c1401d009a5044800103004940741c40403d00803c142c4000706441030b200301e0b4080200181d105403c01007103004010199448103004100d1041000a100c0030b54a204103608103030a012041c80041210b0091507403121110460 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 353876978 1250 353875728 353875759
    0x1002030c011a15090a060509030703230606270a020c0303010e0f06030d12091b09020d140402031207050a17310b130306020703030b12010b01020c 64
    0x2148503246010210754209100ea852554910701d11081d540d10454698500d4079803140e502005000b5516040d81c4140f00240400505004100401a0901c0030702034413001912a01c990702c0d0010010a94903802d0410510075030100000e0098a41218040790240f50240d0084000b1aa150004c0b010703514240160010455004182d411910700030a50070980c1c0d12507950352088480e00c00c0c1180c160b9104404100029140d00d0003250710f8946500d01d03221a001204003501d040010200c2c004121190006000c0c916582075803c04030400400031001b0150383e80280c5c55084042d81c190703c802d4440d501c0403106000040c0c0c1c2c00b041c0b2046080c1c500502a071a11814107019107088101c0c1c42c040c03c1300c0500b100b445544c510180051582c00d405940d0640301c03442070521034032918a074465290f60061200c0062203642c0c0001d005180d82d9403401c02c124071079600e9444000c00c0340e00031802203002c680e035030704221701505041402c0d030381a0032100c00130040e000c1c103640080d45401c5c0305500644201402c43e03842c03a1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 353878228 1250 353876978 353876983
    0x15050c0109140705100e0d06230f0702010e12030417160605060f10020c0f13050901061508011208030c07050a060905010b04060b0403080307050408030a02030d0b0114091002 76
    0xa565420220220703404204030081c0f82c454540d8042c03d40181d40c0302c4c02c190401801280d0001e400e82001d80f4400b0406243c1d21200700030024480150001805140c820000301241c1540b2030107000340c2000c1d51200d052400019085038031800424686800c000d07402400706c40b001c0152640a60415020740040351840203080191003015403441c01c1c60341d210a0300d401d205083c2d0005100718401d0395401380c026000c004100c44081d5000d44030700142d000c045401d07071500b04041002101e04002d4610714552891001460548000b1240310210b41c2d956a010801c2240c180b0125540c2112420310080d00d504144010222020410b0007030506a0700202180302088880304444a464001d401e4489500c45032422901038070104005590075030030580f000c44079140c68480d60040300d504007801031a00e46544e54503410380d00300a200070140401440009182682800140703100d6119034061039407004130200390030460300c004041c5410840340461901c0e05e1042e4504171500b10b0402c580303146426400600891 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 353879478 1250 353878228 353878241
    0x10608071b32010209011b0f020d020f0a0909150e060115260403090b0f0a14041a19020613141c0c0c050402030f040201110111160b070915050c01 64
    0x710040c0084400722030204066020b030204131001d9035a0200003403241f03600703041b035041c004014185102d441008001840c00c0c0400c1100c051020b08001c1c0d02044580003d01080307030310780c40141241e4491210302e00f0881c080003015862403000d00d0401c4141d00d000412a5241c40500481645100d52000302c01c1c3c0714020782c0382c014907412240300c00c28948021b0850454044040c2d0b0101e012544094000c00c02c03050a0b42039410507281882c680d82040d4402d2400c5071030600c2d254507501401d6041002049481889500c0c800012800540590f91452818402c2e00e01142520813002c54203d2818010091000241c2100e42600000101c5012100e0354000d81008a9480e041c1c0d40341e021180a64117483d04000344018041c00355041c0310003e940c03207090000ba440b0480321141e600f0300b0100054015809503040010102d9100000144030700d030340c4060210342d0b21030410f00b030700a000104480b00300924551050741c82071941ca81000700514040b40c0c400010b5080c481801407041c04941c6034050381d070960090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 353880728 1250 353879478 353879543
    0x3100f1e03030f09180606030c030e03030606070c0e0103050a0b09030c0a082b05070e0105040302030c0405100801050a0b09070e010c20150d14070905060a050904050708010608071b 79
    0x10780d40405013101500062400d40b0031000840e04204c4114270f402d0191060420000c80300d8007440c5540d980c1d40c1040b0a03540510f100322036443d000300300415107103244004280038610030001464071440a041101400038010140103281c0e000300044910580089861004507074404a42921000d503400044d4035401a40114410402000f84001074100701d60005070103400c40b516044e0740034039404011610b5100b2800041d40640c403014000540f4249a400700e0f9215504c170000703078015030300c1d220214203403070068455500c0a52070380d940c400d45151505000e40c000c0e446080c4031004011070030000e06030300d014000140a0440b6002d200d4481010340301a0f0603070300001400040000104801c4901c0b94011170045414540b6001d041400c00c222410505c0c000d400030788030401200c0c1303041d0401400d0381c0400070807002c0001c14402e02e41c581e10f850143c07a01502481e01c0f400350941c10058014040c660080c8250100410010110381c01079030790301104129600b0a07000092382140154000c0c03141e4488059 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 353881978 1250 353880728 353880749
    0x60e01050708040309080a0b1503010603021e040f020a08040b060631080c0102031c021c0509010c020714010804062c0105010b03062b020603100f1e03030f09 69
    0x200184254042e0065200328480c0d100d8400c0e20340c807044c8030740d03941c2c5c01e42800078040c01d00840402c441c09070b142100c0380c142ca402070002c130348141c4940c0800c0c00c645483c1044404c482000c40405000c5ca003600a00038140218032045003808280d1600510444020b0310140400f0540808111203440740e0b411038826440380441010884044c0e43c410200c20080b030011080008810310104188ea00440c0c040b05110781640194240840c400c00e43c184021840a0507500e55400c114a410680c55182005480c0078610360000e541d1405011082c207440107124880110342020300f040c09030203511108006894021b01e81090542c0d5140f9100c0c00500e00404011801c05e50100d0102d0401420583c040c2c451010740001d100c280d0344c500080c8094001038480950100d581a00e034420a014480044040c0c44c4401ca03074240c001c03090f00441c000303601c15a49050800e44c040070a2000c56045d480100c02802d007806004c2c040004040400042c81c6103000007070070010201c01c1d0700449407003051020003a1558455 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 353883228 1250 353881978 353881981
    0x3070c050f030418060f05131b080601030f0c09120f02060c0a05151e0a1b05090109050607150b03030f03130606080f0709020c3919060c060e0105 64
    0x11050b81c90300948681c0d904d07035102004018485411340511021034000102514806080008014003840705a8142032a55918003100c04d40b80f500c840e0b108940006d945600006080c001e000400303440d111a2508642e078100395a01c0070281d4060f80c807008482c0c405404c140054881d280070000e04500c44000782d0300c11030115080000034404039a041c60f16204008417141c030a2004c00101d003001c02181d071010303601814603a04003600300425103182d02c00c124010028079054040030540784154000386400005902090201541d45c019010b00040e003c116205414030410340d0720003078001c0c1859040f129440d1103071142c211030b440800030384c0c841e00001d40d07480b40c0340c0c1703020100021000c03100c0d082a16090304040000640f1031010a422072403000700d40191010350f090500c100c0203580f110994000d07910541445103c1d48148042d80791501820030f412402c00c40d005400043d0074078020700d642e03214550a09014030303945c103010200b4084400d14101046003075114217152000309494a5204a07075400c000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 353884478 1250 353883228 353883253
    0xf030e010e060109050906100e040606050d1a011d04201e10080402091305120a1734030609050903090102070806090c010e150708041a120103020603070c05 68
    0x141607416502001390401450b80c402d80c3d9a40c1d10714041c5ca012030114400071041c0880081602c550b9480b901441c0c000c42c1e00c503070700c0c070110320b078600d00b03d42c2580e4191911200303038032020203811010300509a20305142640b03071611501c02841039020f040201481c2c220720706822481100718800410b12401050300c0c10500001d5484d400080c1010540d9104074401c0344110b802902444548c2d00440c1c011380048a11303a50541400300f0b08034001020381d80c0e8440e089403840046803241c010f00821040d80d48015041e61060a010002003010703002d00184902d4200d015400500640e00380b03003a05091321400380b0b94030981030582c01400c031794103c1000710b0f04090802c4417203213000004009d80708080e42101c64450b6140f14154030303030310207948420050304010000365003584100c0c1d014851070300042c28502541c0103031001e48219440080c00b04c81c0769002080400c0b07050203600e148401825040303041882d140d5007461090300a001400001c6c410040840402d4032644148603016010740c0c8241120643c1c00d000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 353885728 1250 353884478 353884483
    0xf01080f01090803010314011b021f1107120306120f020f190909020406080d200c09071209020a03030518011b0305030601140703030501140108160f030e010e 69
    0x901600025108524124060380014800c450065400c807034894210b90071940d9070410921600c00c21003407592500c24803401421001e032610501d10706074009204401b9001e680604441c0c030132114040580c6403480350340c2307001200400c03102c0055004400c02c03003040d000d030401d034028000760700f19000240c02e00c1c000f04100004004030030a03a900031504003984030000e030304010203c11051aa07140011810008000481954000c99291480117002003030480e1246003051805415000013000200c8401454106805880903a50300d1101400a088803e2a0368041140902c020301054108510180980e5180d01658851440d40d07074014004444071b5a01d040c0108a900b142001610602c481c2241981c50340c002c2988540020800d210100340b07401700c2d10190b94070380000b4071240c14001d0840f071030a0441e5400008005140c840d480000302075062034000701c0740b4807036420881e05000c100414003190b0301d451b40905144044a14009401e0504a10f00710040e09090079224050340c201070290001e00e202 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 353886978 1250 353885728 353885731
    0xf071502190305120a1802010e0102030409050c03160503070c031d09040614090106030201091202150d020a030b090906130309051509030105090a020d0b100308030c03190c0e0f0a0308030f 82
    0x41c0c0c1100c1c4d944699100c0780032548640c48404030000c100b151540154042c4420010000c81401540c1c06e01d0741c2c5070a44001d0352411640300d001c00c00008100710881c1c6510424402071641d500e0f00034111b1610a01c0a040024108000740070711850741c0f50710940c040701140c40811b0702d2019241072120304292900c94040c04d6100d41c2149855400e034001034003000c051207501d00b203a80595606220600e80081c04070010340c1103006907001101a14145101c0c04c2090051140301d207403000050381c0307804080008040b07402620181d881340c0d4401061110141000030501d07003100d083c01405403040d00c10310701034502d89020360010b500007000c0e6030705040800449025052846094000f8003460b5125070495072280c4110f24020f6005c24983e81d210081149503440c1640400f81a440103202a16500c0740c288507001100c0300c50741540000f080101644c0d5604182c80d0300401e420b02402a01803e44c0080c00c000000b000702e03030192003402920381c800d940e01c0248030021074125024030f9403420f14200f4103d0180c1c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 353888228 1250 353886978 353886997
    0x105090327040e03030a0b0102210c0f1f0e060f0f070905190303090b030906041b081006061704050d030b0f0a0914090a08180d0b0c1b0f071502190305 66
    0x50840c003803070032354008110b0401300301d144078410b06c00342e000700c580103100d401030300c00784920b8402c41d941d00d000f05004000e803490300c40008240451800b00b11110400b80c1d080c845500105802050a0045064200c8811500880520144d01d115941c42008859400c502c0d4883c030351042d0b10380301c41081091000c0d10381c02680d00a41e160f0f00c00c55290b010300d000c103201c03d641d1841d040d80b0000005000c80d00c01d90340380600741d074154400d1203040c0c5c0d0340001615068010b0410000c0740e40d1014100701b120b4210414046401117540f0044030351030310b0780380c654484840300e082400b41911014600301656402848183c94a0000c1c01800d1084e110205d89004005020110599540d2100400c040d2100042d0040c40d49922241c000c1c5404040403603d0b01d03401c01c134056241c0040d600e2011031300040a0484451080e0710902075280c49100d0700c03640580c40b6245041050045d003041000310603102000c107091050b203100c62000c0c1c1158901030022840c0c42d002c840540320204200d0381141c100341d8404010311740b564 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 353889478 1250 353888228 353888231
    0x812010b04050a0501051c180c08010c030b03010b030a030e040906090506010905070507080a1803051b030d090501050403122106030204050604270206130f03140105090327040e03030a 80
    0x51302c400055546100d00901116003c0d0582410f54030089960017540004c4001d076003000803040c0315a60840800d0706500314000c1651580c4504854645c1740c4100b40c1120340460081c03040307150840120f9200d02204c90080d08014186580c0c070100c0d180c40d00071003030f09513021100304070304001e070304040d9116075081c0207080b80e0b1410440032800281c400c40640f10940d07000f008452500f51142005e541c0100c0e40c66040c0350343e0b07501c188000042481800719000c41d440700300c00d803070303200300080e00300b5041201c0d00983d1002c2c4815034409100f166800019107040c3c0742d06c0840c0c80b5205000d07103819200316060302008840c0c120100f8040c04542c946800050840c0e00c2a1401d11040d120380f410081903504000315104015038058032941440e440da80c1b42900180090146450840c2180c842c3d000029250041d0003a07150b454800c20801200a1208080d02580002005107042c00c4881c80d13200d1140302580c0001c1c826181800b0240e80010000840404000f07100300704040f130f4010b02e680c50f500120b07140290039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 353890728 1250 353889478 353889499
    0x9011e0b0a050316120f0204020a02010e0105010608160e030c0d26070803040b180f0a0b011d0f040602250213060303080703020703120614240a0c0812010b0405 70
    0x6041c000707881d04803804c4660b03400c2c101d6030805c2c85c0340b005140b024409a840f2907a40341c82030050f8403240b000b466000540d900108140e43e480320050b0a450041e4800c0d401c00103210b00300003c1c08a4190700701c3c2d6000c45c030315180045c403c00b54002464200590761981e40a41911081010810584004000c829081c06a1079005c01c1d000c2d1080320300d010f42480039014000810005d4001070443c80c00543c040fa019480c13524070401601d2040c07610145001d00807071544082130280a0084140c0c2041c010100d80d00c0d100802280c44503040444030010303015a90b03a10000d0003140030050b007074060710f4056803030540629102101c0702e8190b611030207404050303000d101c140e4101e99818a9500801301641d8040d2201c00310354817a03400c21002540110381c184d04100b284030701c0442d1907980d400b0794801007401c01500030130342d00c43c00200252100c440100e21400c800d01241c0841c4404450305a800c90800380c14010030700309950134840141c2c0b040700c0806a40d40c50080003ca0031006840c060300540d00c0643d1401d602 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 353891978 1250 353890728 353890739
    0x302041e0308120702031209070602012d1e020304030f1103160305030a0902150301080f07150e01090306050a061404020a05031b070f060218010912030809011e0b0a 72
    0x31a94240030140c0500c1d020800c900d40010740303511554011042c1d00c102c070f20b0f007140d03060501c3c494101030b6845003440d08603000401c0704560902409503031103c1d00440c411056840d187e4614510032080d1703228101c40d00c812074401507904e009030104d4869a2804190750740d00d4146401495480b0403c0c20b0070103d00001964140314030b0002c04d540d2100c9506428110300502a2015280c0d9000107007600c640300d4071031065500584079840003181e240c10307241d2659182c0d4140003115080c50032590a40515070b1003210104141c3e811614640303080c56140c200b50103414546001250003d00a41001d03006a0400c030500c00000d80c0b5a202500300e5860a450b50074003650041000706030300c02c030440d240004400303102107102c61810f1007161300154080c000b1545130110640d540b07105440415000e48009a0101d10748084403005142d43c040035609190441d00309060031540005134070743c52805400c0140490025414420035800f00210040601a00c1000c0591441c07440182203001c40341e40c010480840001103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 353893228 1250 353891978 353892029
    0xb12090c030a0b1b030708070809100e0601030b150a03060c03020702040204080a0c0b19200607120b18070f02010e01061509080705011b0c0b0a030e061302010f0302090d0c06030204 79
    0x781c0c05a41e5010059101c8d0402280d40c01005040200d8074002c3d10286c070428016403064040c000c2c1e4000c0903145a41c0b45081501840c00024180326103000010b200c0c2d005950f940c40107406881c0d00c400d0005411095241c118006c0c001c604000750014400100403420b490000f0f00160503a1043e1b9a45102c1038441c5000c01150003030008001042c101c1c0b408260019014114860408600b42441d12540a28100341071802005a804001250020240040a01d00c0f40640c0742141c40036115052104038083c549452401c00030516010404150701601c01c030341c400e4100c002d58815100081c45601e0f180c8881145d07803400399000340e020412040c40003903a0440401c0c1c8004840058450440c40006900340300a440c0d0103400c11194152141008114a241701001d40301110503940c000070706c416980907141c90000041c081c03400c60607065a0040c0140e0340308049010000261038096101c00c507401c0480d112120311480140b00300845440400d0700e5078154040c1c82101e0f148203511096114000e500e41 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 353894478 1250 353893228 353893231
    0x206210a060e09010c02030307140c1005010608011401090302061602031005090114011a0a050d05010e06040c1706131d06220b31061b0203040b12090c030a0b1b03 71
    0x5c015820900010b801140918180300b85144000281840d01c80c508114900705104094104a10740d40d40c0018080e2541c0b10101c07501401c0300c2c0741046005e091500000c1d01d40c1700b40d072000034452000090003031811501074460621a5902800300c80d420360742c04032400060141114980140d41c64804420f00080d451040c0d1b034100d5100e520491416481c01c0c1c03400c000c2d40e00914400e418001e08100180710b040c2c0394071034035000306564141101642007002c03c0109880d8500300d040c0400c40c2c24180809010380c0c58110360381101c0d0449040c0d08050358041408042d1044055205800e43c0300c0c141150f04200101b01c040c8100d100e400802d49034281c0303591f89891091841c10107414140e000c0f000698a40020300340820101c1c801d802c41c0c810780740d8500700c4030801001e60421100c0f40d480b010b000718015000e50110220b01c00900141d42440d06045648100e80541000780481d10400000304098400c14030503080c4008010741036070f500c10654100b0015440b026a0000140a140741080034190706000659 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 353895728 1250 353894478 353894501
    0xc0a06050c09130b22060f06031a092d011a040e040602030405031b100e0102040501120b04231501090b0d05250c0b0c07050a0206210a060e0901 63
    0x245083e018400d03070407000b000403203007054101c5603140322210322800c0300c1c5a907420502d0020020078040d040c40c5210170008602d6202c03006040c20000c800c1c0070f00350f0800381c2c0302c418601a1082d41d056500d013482c6141c44501028542000c030b541d00c15058603044005070b2541030b01d04e00b07070140340c03010400b100000c00d40c480d5102e8003c04807410408034000030526001981c00c24080d1040b02e0810303802c0e2128510208002030410100c0d80207503242c10840466001708001d40d444a0001c5050a14203000a0a52a819071080e0042580e41540740e505075038642c00701c2c2112150044841c1d88008489840c0c0e00c59005480c2e803030711094462542e104642c03090090005460389103541e282440121814080640f0340600103043c40041c40307800c0748889803882549442c203907656640541d102d516091141c030070480030380f140c00754080405c85100482c8001510058255064844964030740d1180940c5407080150310440c1909540340c82484000042608032000741d581d01038208465407103c0380c285080b120101081c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 353896978 1250 353895728 353895739
    0x20f1e0c0603130605151801140f0103090506150117040309030f08191e021203010302210a230105060901140411160b010b130311150c0a06050c09 64
    0xc00c21a420603002854000d8201c02c0e083da01c0300d00030b50325001500c00444401d52803040d0360301c084170702e49404102000324442d44400b1000395410450078071080c0c141e14007514080d9103091080901a4466401202c03165004000d0b9042030031b0980d80d240c081005a10624000f8044554030301c5840107110099000ea41e042e15910061859a46e132403110a18207801134070030000c10f0140300001c0500b040141c01151889e030325005003031fa0300690714280c9912104045c045501a9003000c00304021441201d044d250111004c6c104044000e01501140103414190074050240384035110801c0701410300d00301196650010008540c0e0000e9025003228421901c01d03902a2801d40100a441d5042c01c100c0c40103200544041440e500d40c08844500b68041d45892101c9010001d81a06015105800d64050101c4010175480c101e400180801020018000074116035035010b90440d480d5140c0d848a07001032100c800250700c1d01c4544201a40b65002d1079030907200541030400080440f06000211840300078000d04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 353898228 1250 353896978 353896993
    0xa0507150e06130e0c0403020d1a0a020705031c02071406040c170a021012060b0405030c01050f18041407030203090d05031608060a050402070f17070c03060915020307020f1e 76
    0xa6031a0945005d0b040c28107840c81000b0100141c1c954880e0100114000d0b0400f9490000c548144044900004d03d203c40084c418401c0600042000c403ca0b20444081d01007140600c10910100c1c000b44603003000242140402d0311101d001c18000305255214601680c0214401a81c1e0b90604103413040d4a01b8100035500020580c0d001480d285424901d074168500e0a9500c0c603902c40564002c580c03041e08400104240444d04000c2c5140c100a0000c0089007840c143d07042101040c41c5580b42c0c0250340c1140480700014265010070b840301e504c01800103040c0022512142040100600294003d58040855000f9034511080c26030089048901034440078800004003214007004584010740648400c1c1c0c058450740c000206565540007401280b03006460341c0c01c21500d640307070080110241900300c650844080c0032400102c0c0c0b800450108403030700700c00d004c1280507152400103203042a0b00703049e510070307440441800030003980043c1c400b01e030b9203014003280d82450f01394103400003801e80e00b440c03589950300450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 353899478 1250 353898228 353898239
    0x528050708040b040f050f0a060612020105030621010609020a11160603020a02030405040e0c0316031110020f0604060507180302061b1912030c0309050c040b030a0507150e0613 77
    0x280f0aa40240508500e141c050310651700d941c1405911010050944d014003036017001d10009100700c00c0104051005001d18181d07513800642076001c02441680300744006002a02030703c6200e00c4910a01180000811040f84c845541c1c5000317400005142000542c0c14000700a01000010080c6078070020b1900c00d400c06192000031000395206c15980d20440c0801e10000505172118010510700040040140600307003000c1c1c051600e4251800c07103032312000c04601700c20800305140000c071015100040e01d00024008400d24217902d041030200c03110096104103030800042c44042c1c1d01c030600940303060b655000d020201c2240702c803011070b0b00c4c08081e51250040100101c0303d540c3c241d11b08001200c0909645515450310020301800c1540340068540070624144140039541c90721484a4914080c20104031004103070b20341541e03a09102c2001402242d071421407034181c1d9020003504444607845000c40d03007516250112071040d1074803089440040751415101460910b8400700761040003400d1000f00080e6450700 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 353900728 1250 353899478 353899493
    0x403031a03060f13020315071e09060507030c051608010606050a02100906060b0403150b0603160c26070b0f0408121e0a020a1d031b0a0504052805070804 67
    0x1071300041804800b26407044c0180c50901998103494945136400d102da1801c1030024008042001d0000d10031002c003095000f0480d00405800190307641c4e45070941c0c4450561074203443c1050140005040380c418010b041101c800940441e400341c0e40f200d8002e0040c01c0d6525070503540e0340204100400560131a28501c0c112454590200002c1d900401c000310751070b030356519140304a60064105403442c10102000c1d1748240200e00807109048000e40e0f0080c61803904002c84807030100c00c81a01d50412003080703602d600303000c0313260104030441d900d01c4d0100550840c0c00d01c9000660b8400e6608940c03038141d0340c0008040e24008414a8401d03034101d107901f481c00e50400d0440c002d500e4001c148100040c0030b814040749140c0710b502600e00c20b1103000801a40d80212400291008910344040d1030780398940c01c4081c20f144ca01249451001883c92181c2c080c0441200000307004d02481d40040f174106160a0800c840101002c4648002441e101b081c05c290781c0031001c05e03005803041202c1c0b0501280c051404100041c054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 353901978 1250 353900728 353900731
    0x51e0c011404090c02331f090203010f030209090a0b01051203070f03031d0d1d0a08030a0806130908040b03060423010611070305070b0a2003030403031a03060f 70
    0x89591061406840f0702c1890100c3c0c14a590080041c0d10481c0980640c41104400481c500c1c015110300160860855140b4a9000000c002c2059404001a00d120380d10149903004080c20010800750b49940e160707140b8840b0180c8520041c0d00ca1460480451110070f00450700da00803580056005040da8200000d00048541500c200a0f075880100f0000c030128402c00244648035200f550045025100080190038594010642ca070b0a40c04c001e03043d403061074102002c034a100c609194464a110003800c0010205511507210f0b98041c00000341c001d0075190700c40e0803a132050a00700c810104900d5141e50782030440d034050b0700091010608100078000c0e003511601841e0b000700d0041c07000c070f40141c5080350b80c1d60a2140300da60007a444030040040c04040c0d0000304800020241c540104603540c5561103403030340d5006502c600140b910000520071540b0f4403488960050740c0c1402c00040307524018155081c1d99038401c0303a0503800a490012616140243c040003d19841001001401d880e203903056060081e400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 353903228 1250 353901978 353902007
    0xf060e0c1308060109020909010923100e0a0c0201110a0504030b0a1806050402100f0e190506180a06090503060610050904090302010609051f0605070f1707051e0c01 72
    0x90010700054a031020030019000c4d240e0300d180561210240401d0242516040e000042c02e141042000303001805a2051107840d8050400040d0840d02c038004031440b004940c0e0086803246a116040000703481d403d8000200403d0958001c01c200c02c0b11501d12981401510801c100240c0304000030004541154030441e0070001c59680000c038038001a40c080c180046005040310742c00d444200b040107500c1d11810702209100203042025000f44d05000c010001d182c1850814030503d40c40c402803403e564147e13031910150201900c03079984c6003100d2a0f000701205007032a83c2c0d071052004050105096200700450f2088079802b600815480c0c441404008020300d0815180080220600c003002e4155224001c184ac418025000011501d0070001c10005030380e40107056400000e826041e84101440d0850444115484c6240075500c64803507141c904c00d044403000300500f030b0841011000f03a0340c214800090038a1803050040711080700030f0104444c0300500385d8062134000c0d001000601400e5004011101e800138 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 353904478 1250 353903228 353903257
    0x60105040b07170403110f150409021b030f03090d1806051b010218010306090203010510050c0c030703320607120e01060b0a0837020706090b060102010f060e0c 70
    0x903900b400714205900184d0003950b40c038105400d00d606c5401c2000158402d039038159070003200301c0c2100b0852030741403280c0e00c03c502c0016070009642aa1005483c51100d1a420080a41e9507940403c901d20b0265041a81d021250b4092102080d94241c0542c0300701d800108074060b000806403416005540d03a80044a050701205281030124003158000c0c8000c0030700e048055466805480041d00040131240545c0010554910410040c42742c0d5a400090f00700f400864a402a41e4002080d001402c11901280c11a0181304005010081101041d46e40d403007281e02d01c0c0c690211002d004113024009024440d114030b140c1180c03002c80e18003071092043c85038501880b000440c40035241c501c40d0782140d0f02035110010b089000702e0741c3c140c55584a2440c2c1d8100c00c4035002c059000c0395a0700b007003401d02c544085604060030011a480501c1e000ea8040d0380d01590040020000a41c850030701e01e0b42514200e0748a401075103807100c2042c20700145c0c03058000b03580380000f01134081d9640108440d00c540c0031412104210 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 353905728 1250 353904478 353904503
    0xa0221041208060f1003200708071b0e04050a120804030905041a0603040b181c03200c010603050f0d02120a1e1d0906130f1e0203061305060105040b07 66
    0x1912903100c1085c9150312603030009050983c3c070081305064004c80302e00c121016020480c1070301160303070901a03940168200301c00c0e1002d0051041c25a40440c2140d0041d110480f060b400c11041c040c0108589842902490f82d0609221100c2d004541c030301c50443c3d004000c80e03c0f0700c1040c00a41800c3c0d0100444415014194040002ca94006556034000721030854001441908021072803000300b03060940d00550000903d40016042c08000c5000501d1004804059a80c82019000304030314074900450013080c40000d40c1c502d0003842150281603140000c1d26584503d140410400e1000a0f0b84106003040341e0227419070003c4a00d914003c0d40c043c85800c820000c041c8030088110f10103a25005140c03c46841e00715045400002d050116119240d525110b46881410494913490b086210b001e030400e035680c00180034604040311401494029504070800c405000041c0200c400703a8001e6024880c1229259441c640e10302c200b1065803003c8a6990001e642404204085180040035142c40c0d84a4040d80383c0e03c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 353906978 1250 353905728 353905759
    0x102010608101b09050d0602030a09020d030c021005040b04060503090a050f07030312021c1e0f0207021804030f05250b0a050708060306010b0a12050a022104120806 72
    0x34507425002c40000359a4800341411510b855a88000d0b041981d800c1c00000b03a8544000103081445100c03001d0545900000026654802d40c0c0c080c640c5194024816108d103011800c0007070851080500803030180c0050a0950020b81c0604150341c1240c0444400c10b1405003440000c5070280c001a0071540940f04039150034001030002d0060024041c031712001400924a141002010b42286a0700d00450074030400a06000b0602d54540c07189809003480c0101c0c0800309885047c49920406196501d62403074001c42c0140358119030020545140202c0e800c44a800e1464042d99404406950003070109c0d2103a00000001806240944120300460030190b2110780525000094414003440440d08c800e080c1c405c1281900b5103102d49900200103181500c0d2920307190300403d59507034040c0940810b91501145100c00f00f0f01c5078203c00c00c00486090240320504003603009101942107408030146843c0b6205030107801d0194243c80034421034214206200e03503a500e0702c09540411010701050307000f030003280b100402d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 353908228 1250 353906978 353906983
    0xf0a090c060938180d08130603020702030607110a0b07080907060203090616030c0f032006060a0b0c1212160807020604020d08040503011406100f0e12150109061e0302090a0b0102010608 81
    0x1d41806030034083d0b03481e91260a001f10140c41d540104040c50720600c000703405600c000564680c0310f0340038207202e50f0a0300030103191440c01e01d04541c0108082d0a40b0104040580e00c1001940202042811a41c41a440c1c0710241d0f01e0380a2b50f100540c1000082c0300c0d500038020284800b200c100e001c1d0504401e50906074544101d40f40c41c0f00401c1d8049011401c0010356011219209c040c1e080c001006407256090280c0090191411071099008402000ca1050042101482489000e4510003102d907507429040c510405007002c212021510100e801d18026031050080b007409100c0c04550f03000d410b055466a00300101c11580075401d84040c0e6090201090340c0d2001d00c10302c5a4407103030400b024500c1c41c0240410000810510020f010000c000304002040358002800c0040300204840032080c400f403508086150a00b10306901c1a805c2d8040c00000300c0d400d0580c010004c4d80e520700507088850b410b400f0300e00000c4030a4130009401400020018001100d9640040c0041d40c0c1440007080ca01e60728500380c0d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 353909478 1250 353908228 353908249
    0x6020d1e0c02122103010b0a03050901110703200708060703182f0303041d040203010221011701021602060d0f1d06060d0b0f0a090c06093818 62
    0x100345a1019107984c011103049194012900101200c00d0b113590b0400085d1000360042e107140c00245522440070601c55402074021380a41c6242c3c01c03100e5203c400c6820010b01516444088284810380785042d020351800103d00c1c0801d4407003000c01050f903600c0c0c28104034001c151803c92820001c03200029040000c61654010036a030034007440c40500114901d03440d1840300e44069800d031090703204200c00c0003020040c1000000307100c11100c805a003a070305c41c000f0a000e4420700305900b4110505074018204040310005c0541070300c92180c180844a4180780d40e641c201e120305501820700c0c0800204860041ca492030007442c20f40fa2a21010a40b502c04a00ba141a507000802500e0b81001c00024201110b004000955100101311007500204095445803070b004040944614011a00c00c0001164401d41c0c0d048a124190312160040b802641d51900600503501c50103400c80c200103010700300301105600d02900c10720100348001e404503410a41e981d0071a961021011407215400d030000f60006503503002c04503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 353910728 1250 353909478 353909509
    0x10606030212060102014503090e0709030c031202010219050405191d0421030f0f050417030a0e0303130201080603190f060f091b06020d1e0c02 63
    0x580c4aa00302442e807008003034001d012a045a00d0106004a45c2c0f8892490319007039014914864003201c8403161966451130301a00c1c0303d882c0070509080d0010107600115680498140409049140c0c46401c0c048030111000c0c8000340c0803410508051021900c424021910b41c1d11600005246c250768085104104881d8400394000ca0800308042116092481c00c10004141c6a000c00c840b0742d08003610742090103d003007500c65040002500180800c400c0e49584c02d00c0820070a1a64825110884001e001e03011014070020001c0c1001190205241c80e030080500855101900a2113111401d004211303d41000700300700c04940d164080c41d12024000e00c007e5024008150340a00030740d4680c00050980c000241c41640246c0c0247c0314001000d050004a00b0401e5110008054580d194205003010742004417501810a25013503020741001181562a81081440d01e0b07510800f581c0c5000a0762540c2d0040c80340c401041c0400c00d10101c83c81c18100e000203007821400c102c04445500d0300460319500c10120b00c1d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 353911978 1250 353910728 353910731
    0x3051602090403080f0105010f080a15030813180605030606010c02190305060a0c02030309190201120612050706030204140105220b070501050114010e0907230901090504050708042301060603 83
    0x174805040c50314851603000d000b082c02c00202d001c86403600102421401040c1208040d40c0d04a01040301c04141c028400454100301c00a40300e003420701005591400034411030641d88030300c1c034002900901c070b401603800f10341d0000c0281074030340d41e54401584c0703820b0038035001c0342e1000e00b00004034241e03904804100b0103140910020086440d040360800200c4201d40701c40d0044d9801481040440640055110010b620f114504410b03809a480180c3e1203100e880c1c51a1940c5041c2880404d03002d0340c161180140fa405031044aa4050307990800f03404034030490040d5444401039030300c0701c40654003c2c0000c082003040d55240c43d800c040e03041b030f40c00310b001701c940c1100c240190005140d00c00d00c842405124050050040ca641c0401c035503400191480f401c003081d05002e1442c03280000c41c40c500602188c0221f4140071107404110159460782411a800350360702902192098030302003a1400c262007483d10844042d1240c003d9911252140c0b40406169034400a90106070510f5150101c020300513040205641e840 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 353913228 1250 353911978 353911981
    0x40b030706090303031401030b1b0708300c030a090206130303082a0a032a020319050f07020f060712050706050903091e030a05070f0e100f030305160209040308 70
    0xb8020305844161040040702101b810051000c1100c031041150010304c5c0e00300704074098408684140e498040c400000c0e000140101e110400c0f083c0c618601440d0704040780e5a4020014109440800400c0688002c0c0a202d01840054040d02040d880b070a1050b000811440c146a007201064042c0d4805030000c5000401c944180522192507203080c46000080d2081e18045608030138504c0c00c24040e20b0f0140d003c16840300c0d00d0003410039042050804a81120f03c240031548092040a5920f40c000160020710b903035844071009010b441041502c100b01c620449940c40c00c4400c1d003c00c0341d246000940d031a40000c04110802c0000d0300410a03914105150f2a10360301c0301c0003400c01804840005042d1000ca41041008500703503503508804c8040300b160660010240350b54800428540394041c0300c0103205110340600841d25001c1007200340c0071a03000d400c003101d40d0b80c1c45000c0658030000504c00e172010311919020030b00020f80034a002d0590300702a5244000050f07251303000102011402c0ea0140c000c18013103030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 353914478 1250 353913228 353913233
    0x4110c010204091401080d0503130f14060f0705090a1811120f010b0309030901080730051005030a14030f03010909030f180509090c030d050c0c0307050a0e06040b0307060903 76
    0xb108980100703441b030060038001c5d1142d0b002a1039888000c0c0111118000e034001c03d020800d80855555440303800071812200191081c118503a0b0b06415076800306040088000290964402d000311409040040c1a5418051900d14031058070304450180720944c54441140b00b000ca043c0e40043c09858500c01d010f480d2904098104507640041a000740000110400804c030400308004200c400b0785208ac42c2c102d0203951441012910000d85c07070003a800c54055040c9400034110403031000310544028070400c0000d6210800e06080f20b200303038400c003905074200c0391061020500200c2d001d4a000c0d400c070243c030300d00707004410486403a520903000a02002d6a03044800103040c1d205040305d01c0c12009040c14000030b80364410a0a2851052054030b02c18459000002e80c0b02c40d007030019009e030f40005422608200f05c0303449c02030029000046118928410103045484511740010202c048a0028120482d030394200040b076503044c4801800f80c2d4005894544640c0d0f1a1020052a0020308103696201180d50851 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 353915728 1250 353914478 353914511
    0xa02070b1b060f180712020609040f020c0c090f2206020903010501061e02280f050609010506120a020a09050604020c07091e2304150c0f080106020a050c04110c01020409 74
    0x200c01813485078011102071154800e04601c0c0014640c04544140e20380300081c0001b406001da8a4407160400d0011072a210f0107080007403450000328084400e01e2a9a4612041c030f03203020411941003112110051040702c0101110a1444100340181e50141c90543c0f85404039096500c01c2e81300000041c84402d1490542145c040025075081084c03020380101841c00310548100b641e054a03203003c3c020000010f10401414000c90440f46600c1000ea03180d03481c103460418001d04007210418001d00012108540211001c00d5011182d0390041c0031208040c20700e1a40d10080000400f03040e00280d01b00080e4a00040c20441c03200100740c54000840d8601d860b000b10b88003c010102411495400c020703100a44401c598140c2514102104900701242c0c1caa042c014038060031515564a664508402c41012650002c2d01d94800c80960b241c07076041c6d90382c90808a0751181e0884010341150400f00d4164098545500b040c5048481e28030540d00701f0849407440e90880c1c0c0154000e14446a4030b4501d03004da05101c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 353916978 1250 353915728 353915761
    0xc030714090a090209010e0301060e090f031c09061103040b090c06040f030803090a140604050c090403170c0405100905130b0310050406110301030f031101020a02070b1b060f 76
    0x140000e0500c0042000305111020b0b030300402a5440d00800d000d12103920902803000d080600030028042d4503070f13031070105540110940741c100b85801030900c003902e01c00001045464800401001c0710034040d8400c030440c0107000800c0100d507100d8560323a0b00401c0301c5480d00618043c5018405010203420540c103114a001c09c04000b00e40521014001000304100508034582280d1308414046d45c0e80e918000c00605018124200802420b00482c00d980010030000b80c4510641c032840c101d41103051242c0c2084541c020440d4000c00195800c2581c90100c9009000c4507004140a2156410303d6159000905c010f04030840b620006206000200001e11b41840080c2108040b8001000001d00070400709855541c0c252061050a855901003000c000940d03200d0dc94142c0d41c0200c0b241c170b07540c4078940a9450950355000380c0001c0d00b030081c10350b0381044c184202c130703103018194000f0403a05241c0200705501d40c22000090420000120720030718100018004a84500c0004903040c5c01c50ae0300d1404c035058074a2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 353918228 1250 353916978 353917007
    0xd0906030501061709070509040503040303120501030b04060c020c030609010c030518030a08090a0f0807050c041a0f030a0b070e0a060f05040b09041e0c030e030c030904020708120c0307 81
    0xc1074010040c00f070f0001143d165001d0052403520150f0784001000b072800341190301040e000403204080200b48003010002d4002d483c460713600d103890241003510540640f0000e01002e009a03100e6408100018a16441444801c01c40d005841402c644040003900b0400211341032401030b5101c0c402501e100b503243c402c50341e000e05c2c2c01406081850070500d10964900510340070005101041c808100c551508110f800c0480d43c3c0180581403180451404200c20b0300700c650300b1551882a00e040c80702d80c0c0b820b4005c016a00c054046e0801c40c03241450200102149034140e45501070040c1404540450741880e030b0a4405d40b00303600d5450f00075415101b8484402c650740c1c809401c0103019190f88864035800702c2201c2c01c581060342c0039503c0e4103600c0001001030050003403440003880c007100120000c035180e4000040080c41e9840030170a032041485115103e12130286102265042088450036924103a809400300d140180100b6042c003500d640d0282986030b0030390341c5400d002004800c1140e030310f0b07100c40b110705d4225 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 353919478 1250 353918228 353918231
    0x5010b040810020f0702061e041508132006070c0b030103020a06050703090626090c01090906030215031b030703050421210e100608100c0f0c08070c03050d090603 71
    0x314444c1032280140602075000380306440026100150703040e8201c0155821902c0e610143e075484d66a85200000303c0c240750030801003031600000030400c00b006015400901d0b00003031505a4103140c041203201e5495501d00c0543c1c48581440000045802445040d002d40000d004041e669411340c010000f4000d900e52000c010804100704080000364011454405c440d654140070842184441d1380240071600e01c415901407841110801100d120005104520070000f0f0302c2d0091841d85480029007900c606000194214904078000164084c0400095a2003103080d1240200055079040b545100c3e8000d40e41b1000183d03c0d0014402400b440b494041108108179807091503070181c80a020b42007140e00f0715105038034022816030b40e0000c1811307000214962000c6040e103c100ba482d041070f60050800d401001d005205019200c4001c02040c0304880085000d52103a40e40180240e8080b01d00001c0340c01c0488034400c0c1401796100181d1360321156005544100050000f40300c3e80d0b0b03030051006159030300c20000c15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 353920728 1250 353919478 353919487
    0x302011e05190c020a08030403030b091005060f03090f03071214071e030c02031606080109090b061005160305070318030308010902090a0f0b03180607020c0d05010f05010b04081002 79
    0x4800001200480016144000c5005043c44505070709000303400750050b0480c9000010072042540c140d004079001d400c2107070010501d031071b402444094061203004081d0003000804c40c07502e422040c00003a5601002100c01c5640c030340c1090720000d0441d0003d2808030380e85903440c0c4282c01030b5a0427000f0384201c8000700d0f40e03881c00d144542d100c1032429086250100c06026503040e020b0207041c459601054402d8024080301c1c1c0d114529140c0c4840da00351803054100240e21200081124111405682d001603000014640b0700c0c1c60312410004100c14108044050000c20400c16203004201e0600d080e01d40e00980b5055242d00709401c02425802e616100c2c00340c0d00c41c9031071080c00001c0d0040f1041341580c3c182200162607045801c0400c030700a000e50008030704800a4040007401c10305800c01584510920566160068401c01e01183e039a1000e5400c7c6001d608291040c2c14242000145107162902480010400c20b002050446c1200d134203802ca810070010006080c03080d14070811410110607541501103142 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 353921978 1250 353920728 353920741
    0x60c120206161b0c0b03060102010b01080606090108060d061a01030506040c020601030809010e15031e0106320a030605040b03030403080304060e03070c080f0105161b1e0302011e05 79
    0x1c20403461044010b0100e9202d010781c40d800c031903d0180036564030100750080e054032134140d0300d010780080b51458015030a0040c144420b510580c17640d03005170b901170022401e110b8908015640884000c020503080401040c907000403880c40e00485025020044c6a18080800c0500050a0701d40c02004036004034200a0200006a40022131504680c2c010040545a10300b5400480303c40d00e034000000c2e4003200e2801e04281e1070f60780c03500960103121841000b0400504d072408036140f22074240f00e407201040345000e0040024581500070b140030007600316654a1416001030b0b4180b5a0008010540080d556207010f101074109403040e0000140700b1402142000e00c0e6999514151000030310003005d544c1c0b510f81401640e54200291052582d0052480c41a60b13240c1c20003035600c078642c070141d48031507090a010500a44070000c13035074540e4449070b80301c0d1100d065111044a0b41403a0300f4040f94102e96071a90034200007500354101194921986c004512444840d404100030700c400e140d850750013850030301440203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 353923228 1250 353921978 353922001
    0x1051906020a06150f1e09060305061503102a02011a04020c0f01020730140304050c0405071106100b0703110f01052706091002070f020a060c120206 65
    0x34901e07441070003c645000062555651301d0469071117110f00c0b48440038007003903001207031400b807004c2c2c41d25182001107255114440c000b900c40c5c03841301504941168010406c581c100768090022281c01a00b1100460b250701d8400c0101e509841030a4644000e59401102c82c0317180010900c00700540344003e2100c001c00904d120445006c08800c1880340303030f001078482048201800081402c00c0b00c08004c5451381d01c3c9062840741800c4181d4046804044014803441156812a4054690300c4a95500030f024810400090450348090400d82e103600c1541c1084015175598010070340710710a142c2d150404180d50030f0700b203803034810080c0a085401070310800620810884030140d4540940514000340c4c540c6003004110708025100c0c20a42465081c84100504040c10482c447c8003980d00d06403521f08825140700803900c0d40130542c1c1c1342120360000106009444030a80261068901034220304204e002c0a9001826410380e9a1004000c5240003d1400a10484800c0c40401d02203034005007483d4a400c80c001503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 353924478 1250 353923228 353923243
    0xb100e090a0b01110f0c0307060f080f0c070c030c080c0301051b0f1e0304031b050d2f010b1f0c020415330f0804020402090609090a050105190602 64
    0x100703450b40c0d0350910100740c3c8100c2c240540d000500003a40d120689504943e91284204000c0b80e002e8032a2810014615206111405610055a41d41c0009032035a44a842c01c1e030901402c0347e130b2121b00900c41d1300301050014060324000c40c86228241c5d20303246040e5450307042080e1074030f02d203110f41d240404011010195401001c07140c5008801183d403000700c2c0078500c00500139144c1c000400025203100e2150b20007064011401103010b9226421054210380d0240b1101030041c0300144142c001c0d8150340441800780107041c44000042400000000d00c92520f281007204800d0310841e035070b440340c011400c9410300c1074181c1864040718044400744202d000001c1c14404640390024000d964952a0043e4440000b411901030031300d48150f000344c2840c0ca040042740440c40ca2803c01c1c1704800412450005009450403c041c20070390b00c800d4004e039915001c01009400030151170381c1001c410015021586e0f90301d5116841a050044000394550500d02407107800c1d009810700350f403407192026052105a80025955 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 353925728 1250 353924478 353924491
    0x18010c1106070e130c1701080105010501120204270209060705060414070302031e0307021c141914030403020a1d010803030408031f0e070203070312051b0705010603150b100e09 77
    0x89185c00718141c04860b0501d04182c0520021050400407940003411b4100f01e04994099813009280f0300340e5407841d8200d01c9544200480e110341382c141d000c515101c106415074480421180141856100004103c40b94000f142c21200d03038110300104001c200d0319818101c540c034000340c001c1410300e0542d070100b40d840000810040303001420b03402000c0c1682080080320050741d400343c4040041d40d08112061071010924508440c024800c04032111039490014038510701034031119440c800c1542c80e455400d001c40c440d524421490204000100240e00d440380c03c00020b000c113100012030b4003400780807c103140006070040b00c4280c10030024040815441000e9035000307022410001144115070f49685000030302c660080030458a070504101c081d540200c042c001144c02a11840303c031084d503a28250441c1c50484070344e4a020183d0545c15010491100070300142031042000085154490b10750700c2c0c003840200e1402c0708403500e400d681101c6041446080342c064125081888c4288019000942074505c0201a03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 353926978 1250 353925728 353925731
    0x30f1005160e01050f040906090507030c0816050d02070b130201090f03020a05011101020d09030201151d040b0403050f03240f01092c0a05010e010815040b18010c1106070e13 76
    0x103496507a40c202c4206d900a103c1c14404100055a40d5074000103000100d0f5040042454218041c0d60075001d5000e586c85200741c1c03440b16401882c54542501c07250000002905425401e01c034060010742c00c86041c40c055400141801c400300401c2c070004002202540109500310b440c80340400c01a12101d03000c00640c6e109003402c0e000c4a0180915074024002c50088005140c242560031044c15019480743d04507040c9d0714080b61050351500c5103404c0b00c0760362105240981920800041c00309060003041c0b82c002d0b110780380080c60710810b020000d030a5003040da0402201c0003030340954150582c008043d0012070170151350b4403a1000d0b00d24000f808420491142030400d50f0b00e1222a00e500110000720300d508400203041440780c0c1411810f0324018042402804020b10140c030001c607a05400040141120382d0408001109545a0f9210100c803c00900403112107803c000001c03a003000300780601d1008000e250b9604950031902c501103403800c5009451701092056005050155844076074101c6c0340c40842400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 353928228 1250 353926978 353926987
    0xc061e07080d02071505060a0e0109180f0308090105011406220f06091a0306031209150417010b010e030a0201030513020409080406030e0318040b010e030f1005160e0105 74
    0x1e20030500c0c4514034102400a20000e0180c0403c81010b0f1740ca4454480002c0c100300d00c1d526002400f501c8003440c0608e05000c83d8200040059403c2c94024180a045071803a00074081115912658003501c07070303e0102c0215003220104940b145091044500400810380300e08042c0c4c0401020038000e01c1100e442c0120342500011121424802e540f404000740241d950b01a04d5660301d91004201c844103000b0840c00b064015000c10b281111802038030300540009021302440c3e54185815000b41c0e000489098110a241034000001c80c24940500018411071081c028500c9405040c1030840300902d04060500c0440e02841e00961400940500f06542c203003400511520383e600d03640c90503040604000c1d0310904010f44c46040100139005070044500c6500d090112081c411000d41e1a4014030041014803008254825101d2825401489003240d040c140968400250300110741414903100389505168800b00002521a42030300c50715074040c907010b10360030b0392424801004004d203008003203a034100a000715 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 353929478 1250 353928228 353928233
    0x80714310f0909020307151719061203110d0203030612330f0402011403131a1506030c030126030a26090601030308130b090c030c061e07 60
    0x144900140c0728840a1400a82d60b60240b54081c00303c551089009000d80c03000001c01d0560b51425110410040d120300c001000035230028050301c40001c00d0240e0780440354160000c0c0da41144120805050451143e00c003030038150401418005180c4800a500e5202464002407a0b5001c000d8907000103040326140b0f0b0301025600360900e0408400303d40506403d5110010301c12035440510403080c0c4010162255550ba11040d41c0c03116013400700e03400703804140d00440301c000d0312140702d006680c8880301e0030f500711902501e070f121f00207c8020040000c04168030030781440290703401448100714001c81122011318500e0314000041160106101340a4141070440e05012007903950941c940719440c0300c00440b0b80301c8a0801c001415000c00602e8013442c400801c290310f0659518800d401d108405c120020280c0781d00e1a0707002c4503103500c01803120248078164042c000000c1ca040c13000c0e5000d000400700506111100c01d003010300b013800c1441503d00c9035108000c2880040304107c40400074850a2410540b20200d60 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 353930728 1250 353929478 353929567
    0x714090f040b1201110703020f0304060806192105101a09060f0d03030501090b040b030a1203020412050601150c150506030c0411030a0609270809060307080714 70
    0x72030780f101c180e500f8400400403450394800984800e901a03400c0b114500c210f64400c644074450b81c040c1c6000980300c00c2c0016860700340595054440700324480c106000707070365800c1c51440342030302110f80d80a103035007880a01007030050800031008207034280c45040100c181c05030520628804481001c0d17000700300740c1c1c0c00a00e180e41e400d5884e03025a4000f410192205445180090090209000791190f041c5002a1400b40c3d061501c80c0b40d0300c1301c0e07001c2d006040c00c03441c9441e04660b102c0300c2d05100040503000c120100b03901c0400c1e0040101d041c403804c010300c195414a00840c1f805500300000f201000b100303401402c0442c8100c00c2c1500740d440510b00008060f01d444021a04000f1001d2502e600300d03007400d0b000c150813840e40d0011340c030a07141d01c0f008110742610340352620261030381e03070340550584444240210000ea07070b011a4480c9151141340958607196a020125526800c102c1c0c3d004003207081c10301040007154001101d60850f040c2100450720f8401401b0405458000c240f0603120010120640125404001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 353931978 1250 353930728 353930749
    0x20307110705032e110c0d0314041b080f0f010e0607091e0b0304030806120c09161107060c020a0608011208030901020c01140601020f0a1101050f0d0903080714090f040b 74
    0x3c0000c1c444a80c172075026107443c1e03001d00d846103030034480c003d001c8042e00d10900c00c1d03441c04003810840b2212070f1070315200d03062601c1400c10722200b91075450307070b00042e0504104254207000ca03095000c0d01c0003101001c0610708461200030000559040f030010080000c4e442022070051301c401c030442c22034142003a9203d0420f010160840302c101c83c8000144001c4c982c100c0300c024401e038002c07582000b15501d41800280c903101c00300c8503183c00c19945404204030541d80000b0b03071024921883c025008a1500a1051802e01c8550002011030003411444056040a03610b802c040e0a02381006c40e05545011100c0f80009224440a8081c4d40088089841d0321400c0d011104004070f104005d00c2a15500090783c0304003502034540601505c02d00c0c00c1204640c4002c01d40c3c00701e5582281c901e00600310120b0065032035034004054094128000c1202402500c1c1034480e080c0300e00d000e03a03940f06d01c0b4500300c0c2c0054a9039214915040614006004164042d07542c07440046020b401594003095000e420b101041c44a0315 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 353933228 1250 353931978 353932063
    0x4080601031a0a0c0f3903020f0a050c0d030e0414010501020f010e030405040e0c03030a1d0103110a030c030e070e0f07050313170403120302030711070503 68
    0x114000041441020080b03640c00c0050040c0000643d1642c00441c401c88482c420100041002e0600c0e843c4100e0080740c01030780719a10210b0f028100100c140706003404004a0b060300d0010018803120754249a41045a1613681d171070f0300001c094440c03840d210b01d56610b48038510b141c0f00300d02070ba2807903040521403c2480400c01c0060401c1c001403202d020091481d01003401080e0040c0715006110710404414010280d41d450050b01a40c90181030000340b0010300400b041c60249880b0729459001c4a4400300020721b81c1040715980d148403210107803441c41e80095840c0d00507040504280d404010046000c1c12111103c41e2401c2c0050121036040081d400b410481011b0030007805804400151f512100120307074850140400024029541c0c0e0805036420f0100b6200c3c4001022480c50f0000000d11110000c09020003541503c1d0409649942d00e909280c403040700500026000b00c00c0c0503000303420285803c0c0c05201c1c100038241c280e0415001c60780e03c20282559400e000c2d44a01020b80e85803140e03000121551 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 353934478 1250 353933228 353933233
    0x20c030d050901140c04050607020d020303220e070903120503070e030d030b0301150e06060313020a0f0602162d1703340f1a090709060b0313030f050408 67
    0x6405100c46000785131065420080340c02035000520f0b80007440007250144d40b00140818200080b41d0203101c0d80705407546d0105d80600c4200000d010801c848032035507079064015201d41c407545081a00304180c0107400f90011040c8601280180300154000b481031458007141c0c9401c45c1c50b551140700454206030300300b140a4060154400500d00c01c0c4d8150040e0103150b006030020b10440030074059000c02000c103442860700d90b40c920f01c0803c4a61038050001c6400c15003424580180b084950009030400c1c1d0f05900942c907002200700c0c2000003d4050118202c0d104142e5181c0c0205c0b4034042c4070400400a07140703540458180760310b8009500410501c801c1c0684004240c10545041e111b00507696644400020042e505022002c00a4007250b100c281c0b900408801c2d840741289a580d5a00480d07818159045540001e11943c5010341c11100d11414401d04102004060341842e1023001000c0300d03200e03040b408080000f0000c03c0102c404c2044006605585441c1100a480f028013003103a15000e50703001500c517070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 353935728 1250 353934478 353934481
    0x50616030c14031b1219022b0801060804050c01030b01050d0204031407080d0f2003270607020a0e07030e0d0f0207051f0305040213090b041103060118020c030d05 71
    0x100020140a00c1d82520324007406035800010304075542c2c007042240311100503040004030081112010310101b1034015004445070301c181500c00001600c80180500d050518a8601d000c18541c40b820282c014074079410441d02c1400c2c44c5c1c94180d2100f140d910000c0c10305484409103081039114504540559090582c115200c580328508400c5003460581d00c9007051080410118443d00301042802e5002c24548803086449482c00c0d007526103601980001a162080c0f41c880c511105042c8000c0030714a60348094038103150480301c600700300b0074444203540f80651010f100810040c0c48444240080d0703119030200001580d64003074118081d09070150b1040c1c0d103010b6001202c507081d82044054034440c22a0b02a50301e840c0d100c10a0000b0800700038400c1014140c801040b410309806603100d1608640050095074155800d00c2c0501c1c2981d01045003100c5004944040000b4003000300b50040000c64114013420441d450618810400c00150140c1203403143d001803402200039003082101d03020341d041d40042c00305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 353936978 1250 353935728 353935763
    0x30d020a0c0c06110a03030b0307180203060a090605030c0f040902040c020604050706140d0203100b03011203030f0507081b0d110d050f010e1305070b041412010501050616030c 77
    0x707500141608a540c0080000003040050180702e48800e0420b2150081548131a103840c124090411204483d4060060242c082983c0031246c45118240144920241e540d027042801d00001111079840300024914040084c0081c2d5808030f4441100340d070484010320b805c0d5070100000c0091030030101c0298414a44001d0144458000c58582e125600440544800940d940025282d5802c28000144145010042d18401412550103142c00c0f0528919150446881380c01c0e400317080c3e1080c1c0204683c1400786072180105540340c0920070480d62500018070050a16000241440b040600b03e02101881200d10f84644950142980c04440c0d2821040c01145061140b0302043d41c445a00403142e0b40c1040001107401c0c1907800703c0c0e8101c4903801102045640d80ca10040f1a4428010302210280200b4400041c640000c00280015000c0419002c000c281c0440401c484214004c00c000407590520004000c3c5603101c005690308100017880c2000c054040380b9089985200704000184600c0c01d440c1002e40d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 353938228 1250 353936978 353936987
    0x2160605161104061202011106040308010306180b0f0907140906060f0705010c0804031b030c0b0603031c02041706040b060d020609061c0c0306050a0504020c070807080a020f090f0a0b03030d020a 85
    0x10717464000c1e02c8500c07a80c038000492a4a80030f0869001d000700d28614010000112254401e10382d065035071105048140c1d50781d403149040c103c182da43c0011042c0c0502801058807080c8103130710007020349650b982200360b03d05001c2001000e000380042e10924011803001c20040303c59040310b0400340d002c3d0080085107034030f040c040c00194080c0e4080c5c000442b200e040300b14400040b03801d61009034158031a070a1480c031136a5103040d070000044c60160940001d000001d50104480b00313040348410980070150300c5505002509141003000c80909409510035000d100200c1c01001185401c82020740e00034402c0400c030300100c0c3c0717071740300701e1804c1a00b00000044410100c03840910b02d400c901c0b0380c034405011124018200301d0541d03055010300c03940103c44640800c654507003640100084e401e240182c60038035903505501810302c0c140354841c51740c80c0c0215041c0c6003107182ca40311012088004460008a6050408021610792030062602908036540c030120301c0250307020001da0340f101c1c1c4200030a564541c04c41c10003d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 353939478 1250 353938228 353938259
    0x12030403120e060402100e06040603090b07020102070b130807021f030b040e07050904060608011d0105010b030106050301060302070303090c06030b12030a050702060706060807060f0216060516110406 87
    0x40020791001e00521201501e400355440000301000103000645442c1c0030407601d601081c0d42d000c14080d0a9029076410303180c080c040c200812450702d000030403e00c00e041c19500180028140c0045901c10040d80303000401c005080b90308000c0d80e4201c030a03102610f00d008030107485805400b80d44650002e11280115071842207811031603a01d69028072001100c00309000030f40c1d95150007214650030140060000382410491650b01034000c000c0492216a244007050841c1d8092000340d0200340240e000440903d801d00030180141901c504213842c5615100340241180018040d8108042d00000d44409240c403a03007112a036130ba08011180000f50341c40b0030140041c8440d21519005005000c41d541ca80382010060301e410440a444251602049608108060b80001c0301128900d56a81000c82d892008000300c07400b51003c3e80361101c00e800340f0600a4501000c800324840520741d15041031224907400000d807501100c2e400030504540d079440c946034641c0c60188850365003140c5000310000352a203918040a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 353940728 1250 353939478 353939483
    0x72106051009080303221b0503060f10060807031d030c011107050c0909100e0105060901050906030c090c0c010203041217013002060a1d060c0604080a050c120304 71
    0x401452110740c80580e009842c5104598440d00240001045040704001d00b01301145595008015180241d407128501b007421103403250360f40352080703042c00542020000c691300321110200040852802c8030b6800020020f90003613008001080001c990041c0c041e811459541000d01060980d01407240d203c43d990350082418920749600b00352100c021040707d207040354540f6810202411000c00b80b1424400000000391031141035110741c90150506024510440c2500c02c5400004a004d003803070340030080d903c031060304420b2160034202e06002031942c0019000c1540710060741c1480d1a40c1d912110b200c1603004040c0801d650303500000070002040740c031b01d0780c40da03813070f041c80d1250501e82400b0111a54088024002c0c40050307000000c0c2c10030401135070920700d1081e01d4030401407010701c00b55501080c219088020361401240d2030004c0d040c0092428071544c580400c0c140c64450400181d4040580c0d2072201a10242283c1000a0303026529072052040303900c22110070084803d00780c8520300c224425401107806 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 353941978 1250 353940728 353940739
    0x9080a030515010c0503180303040b0309060103020f180a24030807060e01060f030f0519060f0e060714091c05070e0903030402060706020c0a0209010f06080c090105030f07210605 78
    0x10501158000c4c0741d2810002d801000441c20002c99120103440030300305245071507041c0b10a0000094195004006501c180b03082005403c06500d9032052144040d204032405108043e00496120f010b044003031300070340c06260307010041100030200c00045c0d214a4105000c100c04004008007000b840304c0b0f030008040c2c03188100010001c0301ca482c401582255594040c1000f0080c0c000c07010804a10340e952195a6030303000c0d0080c0c07203071040405800303461030003070f04400c888150710f42564075034213443e80c815050300d8040d242c06804c551404000017004103151020701c106200010849030b00030b8464020040b42030019100004540c11181010f81d50303001d103441050240520280005c0c8000408001d5a0240d5405400e09007003110a543d940040d4120b0504071450b445075648240c096035a10790350724020401c0603140e00f940d505154004014185c020310a10a43d0002c01050340941d900c6412207902c24800710092081c0e85681c0c004035503c1c580070361100d074040c41920070440880701c260702074800c8075000c545 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 353943228 1250 353941978 353942011
    0xa1b0906110d1b0302010e011401170f2e060603020c0d0c11090c0904050705180a030b04020904140d02150f090607201c200309060a0309080a0305 64
    0xc590342d90b40480380ca0030004101c21250f10540c0744070b0181d5072900f4442d00000c0b444201043c011821980c030b660200c0b104071004801008040b1116031207100c070402c49001382c07200ca1601c50324295119104030fa00780c00d079000350074107e000c2501c0b1a42a4984402c03d8028007205580300790040c0170f034010489140c0d8502a140300c1d819420f004000310502c55900c00142e0303604a40c407a08000010800520000d40c158041029150a0740c55100b40d034412901515155282d03583c5030703110100762004c541010f024103110390051010400f592401540301d035040f540c000c22a55545402c0c03940c540303080702c0010184180404241110380104050442241d81c50200c00c107a610128540902c100a440b0190103070440c07404540c14901c05c0c118601030030210042c1c454440f2481ca0315620b00074200a002045d107117000c46102c403256005602c407000c000c41c0c14100300d620440401d40f6447e4800c80310842e108400001d4100d6100d8081c0c0c000303981c15034200405a0300c4945150700034020303110403200c40054400b03159 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 353944478 1250 353943228 353943257
    0x200310120c050118031a01061805060f0d090807140c01031b0c0c1a1e0307020d050901020a060203010305060603010506030d054612090314030a1b0906 66
    0x18510011241c000c10403224039481d20303005590210070000c2229041d0b044150104c003144d09410444a0081c8600d0300c0c000c5503141000080c0424161404800d011140000412450340d41c0d00595404010902009a4401c1c0008000c0000c0c400040010130131080820504280154124910b00322039240701030320301500f4058011803c03100c40310610b0b804080c00d610b12081107441a4a80c200c00f611422500c541c4a03125a84801d080841410000c94044005045040401d445283d043c40759010482d01c2e0a5043c0054041c0d04c80c1c1c2040060010410082000c0c01268420811102c19a4100c0300071541ca507100d00700300d80c695400301e0b00a8025801c0001181d2107090020305d0b40e5048c2160f0340c403941820010142481c502c40103002c02c80b0800700d280217007025001c04480c0800f506080e1207080001c1e4840003405862450022810400d41e03240c000b019001c690460101d0b04d402c48002006940d96642d50803440003010802d500c40240d00a08c4414038816400903100e8003540c8058582690068001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 353945728 1250 353944478 353944499
    0x4050f0c09040b090a0903031d0703020618040c1e0c020a17010207200937020c0a0302010e120c03040b0a1e2f06010e060301200310 58
    0x252004000a002000016a1180c0c1032016000044004201180c032140d010300049040c2825181110441d5403a80d885080641500c0fa41c25040c0c00d0307100e5805100e2600c0d103025214003640c800070b40140d80014000700954044212218820402001001070080d250741c0102806480c00850700f484000c821802074960168036030f0104c40303500030a81c0e11601e081410240c418809280103042641d000d010100001c1c00720107149510a440110044011080000b000340707043d409000e180c00d0300010540d02c0c4030140f804664581c590344060103494180c404049410080c4501d01d8510700304d003d844210401c0560640140c0300300e072483c0084410401c02e501d80609284240b0b08000301c0307903000b040304200010320390020b44181c01803420f1400784003941401c03040c2c6040c1030286410001d420722faa03502880c0065200090380d00d024240550131034040d074010564880040c0950403400d400c45001070510342c0c0940007490413040c1032415190100b202403030000d680d0000c0e00c21900b000c0440d440442e82038100d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 353946978 1250 353945728 353945731
    0xf0c08101a09070f0207081b31051314010c090504020c030702240c0d0305010e043c03020106090b030c150304030c140f1b0d110a030b07020d020c0405 66
    0x109002d00c6074507142e400382c844440061402c0254051207000041102d4240001e0045c0c0714015542c0c0c5510303050004000d461559181c1c075501a8201e002031445425a00f041d114020642d90000540c9450301c01310b200c07550b000044005c03c0d01400c4003108003140010b4000340c840e43d565859079480282c40f2002c2000781e02031001030003490391040c80b81300058078105081070408561106c0c054241d4140600b040d0007076024000507080c540c0141444c2185590500c47c240c01412a000d22000301d081580d98034200b1501c0c0c50144020310001208001d0800301c030007440350494a005030640c203928081c0f9020b40a46014440c3c8426a85413100701684c600340810720042c21400280002c550350000c00c2c3c8410150005007041e01040203412400002174800302d80386507003083c0ea200411812640d0202c003440c003000354412203080d48040603040b8003078481107071000e00a54084400c0b0b103c1c09010000c07900440c4590310283c04860603000348110039402143d405038414070380d42a145a40703144801c0c401035540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 353948228 1250 353946978 353947031
    0x1104050106020307020d060b0415080c0103090c0302041d16140306010302060a05030c0c030d020403021c020a05150f030403091703030f06090403230a110105010f120f0c0810 76
    0x40041134014904203410003000c51080d040010b08400d0b0501046c101c3d1822841694041a2594103011130328003000030f002c07152003d103028026841c0c0e641c0c130f0002c01022440001e000f02c0e185c90700424003000c0328107800100e21048046440f40c810780d030840035108101e0300c644006458440d0403007080d402c1c0802d50324141c0e50040d01c0c49241102c180320803900790b44001c0c11035494603014040e5010f400c6080c401082d0038150040d000d0b844500303600422110795150b045645040c40780030002c0d80161241c00e0540100c8504442c110050103190001900134800c1850a40340c1c2781c800020441090b4101403010191803141c000107121041c0c100c031a595078442901c0700841340403100001801e925203249030b1030740300740720746003201d4130010724000d01500d50740c25010264581c0c4040f80360080d8982c07007040107002d00d0b200c00c0240401d514000140302d40760541e000c1e8508070784040c20031030305114505200e145410f6000d0880700180d41e41e5000d50340c48460300300501c900380e810806a1181d07010400c0c5420385801c2c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 353949478 1250 353948228 353948233
    0x2030715060f090e060f04020a0b0a03050103060501170d03050a060504060f03051c020714010e090a0c030c0513030206030604020708071101030b2d040e120705190309060302090a21110405010602 85
    0x302c0366a0703800c4506c0b90041c4126803208040700003140c00d1404034098608007415440c0480e440d41140340c441b080c0e400503003020070380e081010170901e140130380002c02d01c0c40f0310414103000816841ea0291940039002c16004160170500304400004c0d0174510700101c10450340218260b0752400021781c000107611101116810040e404070b041446407070380000007151a40700504002181c4403815020800880b0122002d1005c1c0ba27407145004080f42d050f0144091000c090310b001803825408501030407082c2c202d40130280c003400001c030005940e6103840d81100e03030f129007260b40e05480d0310083c5400b081080c40c42d00e4042c002070600d09100403a0801c00c203070045603e021900343d002c0c441c0f084510040307021040d400c0c075031281d00e48a100907404030920010150000c0188541d80c2c400083c20464170300700707600010300c00700440516100c011a501c01d0205065402c10310700941da03480c0600c00604a6141078002c44003588144002d40303414180011015100d0744244402c41c070a0003c94100011510248500030268 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 353950728 1250 353949478 353949481
    0x60503120708090105041701021e1e0f0702030102130305070e06060d050915010f050a0506132c010e0f061203160203010f0c0809060a0513060c02030715060f090e06 72
    0x50020b0000c0c00d54401c062602909040c1d407030800d0b400e41d03400005401704603580040c0c11890102d06a02c4242d0307820b828400320f403807e40d070480d09861030b8400c503002c021809008603210302421815000c80e0b1602e41c00400a54440c14036000781d40401186110441e21072003041030014413034110445007481990000c100c1424503207400c01a0000d00f200810101e92802804906408080c190354254040c2010340c440440e494104000d00c003104202e40c02c40303842000184403540c0540b100b903a010040e50b000100c04456101c0c1c00f11707110201d6107541096904552074100100d42c68244504062181030034010741c48003a110101400903620f4100000d500d240c00c1040250701d503500c07248813101000c0c070123400011004d002e00d0148080b907540d42c00c1400080c025000344000224104034a50300b00035000002c004505016007002d4081d801080014845612606402e44d024001c0c030039250302e40c6c0c000700d684c400c8001d650100c0c0002e212501490350380034407184021031541034031b02c1074102c40000c00d401402507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 353951978 1250 353950728 353950733
    0x4050703030f1b0602090f121902060735070506150109080613210806010c0201120c03050402130905061308040f08010506010f0e061b0c1e040605031207 67
    0xc1014403640c40d418004102406032001c152038103200c0d40e044c0140f4006032100b01741c03420400c00c08404500f06104001030001607a008c840441d403a034900501e141c641390000303114408100c4038006c000c07011704484441c02000f00c14801c20f50070454103132003800360751a600c51f4143c0d0956a500603c01c3c042e00c00d50240c0e0001d0802800402800300c42d0b00141009080d0650f00d400d01d525010084401d0081d140080c6081010031001400c021803490000f40302000c107201c00c80c0010049500208281e04211042800409690047c00a20713904594104c013031004c000d04446c050060541581c0407401041d005284010b440b225200c2c1d9408658000083c05098a5003403441021003801c0307409845a01040100160b03c24111080720011316000740041260b15000001404040c045801c1a003880740d017004c084000e40d03500d002c0340c480b194081c00e486041c4d94070b200c134586845800e8070210780180c00248400702d8403580c042001e00302c03202100d00740b180e9507c1c3c10500d615401c9075104072446010511a0000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 353953228 1250 353951978 353951987
    0x62205060f04060602010f110405060706050c0f070b04050601080d170a06050315010f0803091309050f010c020307170412021c0501060e0103051006050105030a09020103060321080f0405070303 84
    0x821900c0186065641010100007030100c800a03030000b0302503991540d9103034280406014040048420164290803d03191030007041c660721680304000d05041e0f0701c50006102c3c80c4d40a090b0340e030203a0310050442d10b0f900c003494111b004080540381960644940c2000140182c000195042900000d66a0b4000100384100b0700b1003c00c1e0160100d45450707140c0c04c2c0401c1940f81082428022400310110007140d526041c0ca1001e100301c540c00902040d003080016900b16181c050b08a1164965040001010211030811a0402d02c8001c071050030703942840355003000560b000018048030fa00401d404815030f516444c0012682c800c038440c5a0351707030000c0300c075880c05490840301c95400d02d49041c4440c4500705041d980c80782142c9181c0c0240082c03102c12401801484410480d4503a01809001c04104141c18940040d04a00004040c84101902c0e07a65a0381164400c0e0022001540c0c8403145403500c220b031a54035004044803003003803800110403500007400444d1903407081e8000c0d0b800c1005402030f5030854a0485 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 353954478 1250 353953228 353953231
    0x30b07021b062706070809100504080312040807020a030506060111010603111c080a051b031c0209060c010e0c12070e070f20010c0216030308010e250206010e062205 72
    0x18105510f81464048540b50388004048240c032514543d5591120301c8204034007142030350400f0040040c01c0c0014400c401c0d0000480c2c1d48420340100d41c030300994aa1912402d2445171f03083c0290045c208201c00020440d00042860240310300340c031055140110041110f0890b00a81300190241c2d041c84110300760b50521142910b0214070a2144038510445a107030b088ca04d910902d18000000c0000604075102096448822070480300a4050342c98441414401d07032991007800c10010b00d427a030008802c00e242c0e441f002202c2001180c0d10003800000f07904400242c40c2c0d204203400e640100c004082c4802d140318007060728000d40c0e50344601084240c44103041100d072070012034051401d0000342580040800001140340315840b51200000c5070a02c1c00020003420018042003d00700c0c4030076200c0a20000b81c014544e107040d80d5070744000300020780d5031006961040030a000c1910389081e80c000520030203503011034624183c5d00142ea4400302c6403603039010f010302d40310500490011161140104514500b641d007149 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 353955728 1250 353954478 353954527
    0x1401030f110d1101180303200705030106030303090b0c072609090103080a030c1103040302060903030403081210141509030114010803071719080403050d0204030b07021b06 75
    0x14150900e182011a80c004072400b0140c90b8605061080441503a012182c81c158050100c9401c11141c9580c0d0054011004c00d012400000248030443c280c00008129080c000c2c41c00400030700c03e0999900300600103013294101600c00c00c2000c4e000840c00d80c085012100650b42c800a42c0c0040c4088501e19149003a109a4240d0300910070002403880390307552609540038601070380b0b0b80c03030f542e01e02d01c070010b81140c16401d002e00a000301d03042000407643d4044140d4044035010703074829030344882503c006801e43c800c60700010800080400c0c454240511401402d03c1008070001b14824580c4844240151800101855602c105c80940000c0d001d0207440103440a12000b800102c0c058091852003881110300360440c0d04603a0000c05d544041c03080c030841840a1600c05c24802c0d05d08014810755400c05a45240f00106000920001c50300b0035115200b1110400c244c03c00454580c3d4680c9001ca19069099440100520441c0050021440d05242d00308111000800d02c52a28000c0040c110b020614909003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 353956834 1106 353955728 353955743
    0x504091e0b1e19090f0b0a0911252010080603192604090605010e0a03020f03011d15090601351b0406091401030f 50
    0xc1540e07031281078400150f4040003809000c0c840225034400441c01c1e24014603120120301581c44045401812102407281c17551321024841990385c0e140c18408041c4041103425040c2d601c00c40704218401d03400c402e01c480070f48181c540b0b2003545000c4040107003200c1c03180c0107001545003006640915600c2420891018145200401d6417075010021082081030100015000d2001c00710055810070b000400100784422320020115072500240715110b0b10354101031010030990300407180c078810311602030018a6041c1c55502004452180030a555802d55602c1e010068980d006041d0342d407021201d0780003042c00320000c2c1c820709690240104280707001c3c7c0105005100150b42c0528800c4491b05402c00ca6401065804c840d1014030810704003803480e403042c044482004078440d03160088400c0304aa04000903070380c54024009075040552034452240d240e60051002410200c0da1034500c0780282603 = true := by decide +kernel

theorem cover : BRFrame.Cov 353776978 353956834 := by
  have h0 := BRFrame.cov_init 353776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 353776978 ≤ n) (h2 : n < 353956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
