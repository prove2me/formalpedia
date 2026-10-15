-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4008
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:18:55.164658+00:00
-- url     : https://prove2.me/submissions/85d2eedc-a131-4a68-89b1-27f5c1ca662e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 720683453 ≤ n < 720863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 720684703 1250 720683453 720683479
    0xd05010302100f02030d23360a06020705160f050307060e130c0e030102040f05090a02030402090c07020a1701020721021222030b0a0b04110a111c020c 66
    0x342d00404000000f60158000340315001c540b01c490307440200c0c905944070f02000c40c090702c64000c01036071108071603140720a1a040746191101c1074002148403454042083d07064100f001802107540d1310003800c0b0042104e500040c0074000c0003001c1c003151510303007961041c0b51252500c610306000c03520301d41c0c011a4043d10036034070001405403103020b40e0440c5c0c100280501034521540c105c80400fa10384106200280714840101445944003440100700401c0e0090803010301c0e6060604120407014061300b0311400e1401482071101507941d144400350403c0d2010096591040184089402403010b80d00175032a110860400d908070860640003030990310711a034100a030050610300049048110048401c0041c0d214088038041801500020040916500c2008041c012408036141c152102d40d00121041c40d802424401c620040c0e0081c1112448211000d010321000d9a00406490151284031810001145510300900100b07100650500c02140080100624110400f9580c1c017141a490b80c0102a050281 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 720685953 1250 720684703 720684707
    0x150910020f100203060a05210607021608280f2f0a06020618120a0507030f0e090429041101090e0c04030b061903050c0a05011716050702060d0501030210 67
    0x6170311540d0001c3c9528407584c00c02003071090620142442c02404030b11900c0a802a0004100c4540301e02c204c1c2d0300a000c1c030303034a101460691002580c4a0440c9a00c10241103071a000d4042244c0691542c10f110b00001200c1410700140003415840017424402d1141d26003461500c00d00082c4000c8240844c0314819046100140184041c1920483d00141c01510204940154424500c1d175100e801c41c048500c20442000d00c54000d500500f90709002c1000010f10808040e04030b52400003401040c1040e47c11202c011010881c01c244c01800140400e00902e5003244140c017901c02554164030b87c0c0c0060120703107000e181440200300312440307943c081984200c0000705102c21512451160f0707a041019420145035070b640f00c0103420050a501c2d0300080f04980700c3c0b070606001e0380c541d0056000d400240482c50000c418441d140340507400c03550400030211200140821450081c94200d40e0145401080c1103002e501140c2034014494002c0d4056000142004c0c1070b0110341045041c0c038000c490207030034a640c01d481 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 720687203 1250 720685953 720685957
    0x91802040b0d0507060e1915140a1e0306030519050c030c0f0d050a0b0702030d0b0d0302030a080601050f040e0a05181b0d0f060f1118150910020f1002 66
    0x300400562141005000780d13031080c1d400d6100100060701d1f009940c00c1440358603207462400e802c5103016101650aa104055102d605c03940c40203040c030344561402001c000001c03e100000110500c0182441401c0301c0304d40e2003035112100550b0090165102c001c10f0441a8081401c00d0702c00f9203c900c280e821062403480d000c035038082c1410000301250014484481400442c040003c02941c035805801701790302c04a0000296103200e00304580c040d40c0d45d005000b0681d4129510607507064090101d034014200001c3d0000120340080c856401c2501c025602d000049400380716401240305000c030040350025010011054240c090b07981c051f828481e41e038a081c00030803005090003014542d6030203c8000f4180d901e40c45181c110042014121051241450b00d03400400491100201c0306d0540e52400300e860001c00344200c0f911048204011440e00807002d044521000c0f0303048cd201d10601c40441091080401101264451000a08902650f00202c00301075100c04c96014128411701036000c80032540556482 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 720688453 1250 720687203 720687229
    0xb0705070f0f060e0a0b16050706021609021b03041e08010203220501020f0310050306061818010f0e0a1a0415050405010b1e1302030c030703050907091802040b 70
    0xc54100a10700002202c0c2441c00c5030003c1c0e0000409078006c200424040c00030603851a80741c0c0c0250450700603191540c0303442115406841150020381c480b03110202100e034000200c03620071b2405030301c03811442451040750700041da0141041c80300040004152095040d17480840304c040d17902041266407602d442d400d07403108031031012040b40459031a4800070b01145a0001440c09a0300060424007201400319140c1d0080d50304054000008104028518041003070650201e01911034001000101120710000300010f402012040d10380ba049000380324003503004034601d01d8180b1080c0b0141000d401c5845d10f40c2010310b0180ca1581c2007280112415201140386809140d00c0030441e80701403c4000b44900800700a002294a5522010613000a81da0118800b00c00540f0780500c41c4071960704410002d600030003060071884a40184100016450701d0020f6a034010b015040c0850a9a03503029514105450703908094082480e04180300802522a44403004280c42507504115035803125081242d0890145 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 720689703 1250 720688453 720688469
    0x30423060717091c050403050703030309020a05041e0c0e060f0a031107030c080706020d09050c130b0618060417030c1902030616230d0b0603041e0503070c0b0705070f 73
    0x4a2010700004040c03a040490500914080c1d0800d42c49230b40f92420850541c0c4281c0c00291944905000d5141400b0b8010091004079400c015828440c070b1024003d582c000300030002159115000840a802a0b5201c045400000c00d9150f8881c01b0141c80d09054202c4d950840002e460020704840c1d070712520007240c68203909030300c070f0702081c10003580d03403069079402000c003203a10030340900c4201110310300360160a03200e17445880606031040320407081c007007000501002e25403201c0c01c0032220009a05c600049400714031091140088601661012035550b2245070301c0104440c60300582e8045030780b8044044c01b40344a040d021344052220030500048004404180a58960071220104061030522030b10803444114500300151440c80d041c00031003503100300f0341000c00d120381c00162000143d400c40c42004140e10741143e05a04600b010744030580c071a08540c00000c86240746e08005801d0200c10411b40d100070b80d014000c007003400d0b155000454a50043d44049400d8071a80c0c50115030030301c800940310f066074681 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 720690953 1250 720689703 720689713
    0x1b0408030d0501171903090e010303110d081b07210203030405070f06140d0f020d091118040b0403180f080d09060509150c0303010303090e1b090603042306071709 71
    0x290034417a01c0042c004c1c030450034040a80c0340050f0340d40e4001041c0f80294000e840305503400e02194460f9040c021001c42e02c008010200b070401c41d60300d0180c00e81c407109400203000309403220355500d07160303100015810a00c8105481c2e12042c00c05a64008010b40c03207107200b5000d44103141c1d9900444150100c00d409650089684645c0407501c0c0c0c100003002d040c90182150001c211030303114000c541d040340e1101d48402c05140c1c48010060500c03401c01d0003612820300035150f6018083c0400c0c403055104401810092820f120800498141845054260303040c21102e46510304090303598043c000292258426043c65005420440810f640036050320800c968568948070b103062210800c004860402000e00380034064240036031652034a01300007075400b0f94842e403100021142800c0303013442d070003500030038050345c05121031018144148580c043c0d484580d0141c50140d01ca8032180713031492480d20410901c131450007e05a480f4041c64000070f1441c0500c030544c03a000c401cbc1940e50402c45103070f20101c0381d05003543c3c01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 720692203 1250 720690953 720690973
    0x902100309060902101e261e10090605040903080a0c11150907080a0c12031b0308070e01090608060904080c07060c020f040501060c02091b0408030d050117 68
    0x65000000101e1054600085803d5140d00003600e0024030568000001c143e050705141d4800c001440d1072801c811420015003d8120100c00e20310803055101d6414050060000b1912884824018444680d10a000d92070180341500f007085840c5024420440807900306400020340303080c548150405c443d099511a4620742d220f6890001401d50051700030204040e209002200107001c2c05000301400107141ca54035141001c0c501140b4040445d046003505400c0000340780c0c0018950b0310031104951040e804415143c4081c201038031000c1090254440f0031881841103c10144e011580c2c40c8500001d485d440746501c1c150b001103039101482d01a4070f01084441000c909103281c610300f500e9001e0b10603201c07140341202100c01c441c1003c100758045000b0540d01c1e55108118a0040c1002c1c0401e042541d08118944c9010f400410506980c103001e070103080030b0004100b0110013098038000149241200700c1c0c2e203d959003c40303552580700a41940001c5e14080020035540c0b41010309034104241d003002084540e070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 720693453 1250 720692203 720692207
    0x15030c05041412070801020706050402102c060d0204030f020406060e0f09041401020408060108151e0a0b030303130c150804030f02070e07080118050105130f0e010f090213090210 78
    0x81025022251260714000265840301f400280081481010081510b0900c1e10501c1240d104c2500382000f40010003c0d404115402040c0b02000018110040c14010003040d01080349840b4004800f246075000007070100501ca60305500c07200070341c070a0301d0400000c0d03a9000308590340007141c02e0b0700e648000030b8114541c551400d5084603400c60300603c01c160b00c81d08511403d508a134040c1c5d108800316001080100000c0c08284007441d05000341b0143d098283c40c1010000d012048040c00d0366002400050202c1c0e408140c0764040701c1c4c225000340890341d0368100f45e160a40c0b01d0310b403140102c40c1d424100501192001c13814900000300c085c591920300d034580b1255016110710101d000c0b440304622070303501c00140f042c001d542c00c039004010f9620760391134a506180c1800e03944101106030306000c0f410803004000ca910b5900c100054510100c40000341100c403031361042c01400f2034174818040c03036082c08101c81060020360310580c4018400c640d03501010801382e1188003684c0031006c2c0030754000003001b054a0858 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 720694703 1250 720693453 720693469
    0x1101151403101b080112080306090411131a0103021603051e0d050f15010f0e01050706060e0106020f2806020d05091c090f030602210115030c050414 65
    0x11008050714440c141c40c2c1448001c6411010160140c3e44294903a0307184550401002805406112540790159019403544d00451001405060040c80351500040601001e450301111510000340500300c07a607000d00002003d441d40881d1681001c4030203001c0b9603290302910031550030600c546600500601252030641e515000310020702c039081004a0002c000060010003066242d82102c0e0024650414100460b00b12200034440149035103991003c0049a8200c202d403500400c46141c040e507088208001207586000f1144000c00150902c000440c004184c01d10f4541642c1c80c550031242d041c4642c44045680718900305485500880c80c104008920b614a03138140c4090780510000740c0303081003026000c5d0840d074048030380c4006a002001003400b0514103038891090750015141c047c0d080c034148008201c65000701c1c0310041000382d00240800101760131264040386c241030006014525a51500c1d0124410310090311240024a80045042558001c3d000e40d0180c40300d55203161090030110b01441011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 720695953 1250 720694703 720694739
    0x61d0103150207150203090d110c0424031a0601020d090e040602070b0108060711030a020312100305010501030c0915060518040e06010914010e073203100303110115 72
    0x5a408020600201380484402040c850503054016074a140101825062008031034522040184076043c0d803845010000e8441c000090403200041c2d141d540d10b014100c103003660b4082e54810100a1400801d02c009108804000c403241034102d00f5994a94004a84803000c4814040c04204090401e0141d04500709445034080d00c1802e006160620702d440340c408480e0240c0c485851a845002040303086030380701d488890548000401036060a1074014084d4a03400346007404070000ea00f05000407150700c18540e100004582000081041e96101d00705042c03180c0c11400b0382500e00d8202518024102120b4181c10100e5219650302c03030030b0840400c0250740e20030308d14a020340d101d52112240032032090188000760003020207000000d84a05090703144d4004d004168408484d0b20180c40401c586a9008040c551241c0c10b150300c0a0400e041c0d040c80d000241803010001c11a25501004006110301800300f4841901d0107034a4000c0802c1c01e1601041c20b07034a40708454042c41c111848200407190b1210758913250 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 720697203 1250 720695953 720695993
    0x207031b09111b160b0d0b04020c15180c060f13060e01030c050c1002031e090604031d01020c010f090e0a14070f05090f06041e09061d0103 61
    0x5180d07a001e014040c1c400c0d410400686180c001218401c0e1407240c1c19032040300004002426402010018007200003039607100d041d01ca01000613813502c140285a00460304a400144110348509089018550f81d6510007040f001d0a00214086400044401c0361240004580c400400050a00320144940b580100b5845090001c0034030090201401910036a4003030200340d40d078500352502c0400014180e40e000d4246a049c401c0c100300b40c1c5218400469260500c80c206a405660b0341c40e03003e82090002803001e0b00901d000d0300f05041c40b03201c00000c00e5950045019994240c00c40008250030350300307201031100c114003680c0402501c182c29401000400683c01d07080c00c1600c0b000f40d41c0d540004102004807000c0d60b086541e0700e196504468440249600100646408d2809255080c00900984101b5195034130a103403001c005c00326580d5620444001d07101191038440e41920781c00d060b43d401c18050050209031414000d01242803d2580c050040e05100702c000441141d1a545400308500751040710005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 720698453 1250 720697203 720697253
    0x1e05180403050904110a030b0306060a0f12020607020a0605130510020a02010818011505031b010804060e16030b0f010803090102030912070e0f1812040303030b030703140f0c040507020703 82
    0x80c5548007002038001003601f81c40c00314110407000209030524070700402c03880c4200034001050007010b0030700e40d0240070307601002403419020f0f9540c0001507040c09503242c000d600c014401380c04940749a1000140c1407603a040007243c00c1080c1c803041017021140100b4080c50050340889218401340d031013081641e0300280c003942e00f41ea001c4420300300d0a081d110385400c0c09809107141c520030001d80c1010010306040c035041c00448030038103e02c140001c0c000807000c0c1020b440c40c2c2d2100500d0b0340c0002d09001038400601d25014081c0b2140e501d181602411108507075017003c200d0400000141c039036010080b41c0b0340400c140d0155103400c104800300034114841e08900c1034240300381800400c100c0c0f074400b5885d0043d24100700c503031950720b4106407501e450241c0c030000c070b0140d80244d00301079500d0121009880940381c0c1401c000c03980c0c8150001007854170410390700280a6000a280600c80c600f4081414800345030f4040951750062600d000b4001030ba58107171080da0050713015410800c0415032421658840c4041c00e481c500c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 720699703 1250 720698453 720698471
    0x207060b041b0206150f1908160303020c041401180f1d0610061b140a0606050103060b0f0301090203101802130e040507030b0a0204050303041e05180403050904 70
    0x1000c4035000315030b42e2490042124900d0b42540c041009030390081c03000200104200c0b03000c0201d0f030721600134240070b4022120114410710f4006101804d802915010b0704032410f0091041c0700c0c101e08640c0380720680140c0907400c4a140c050503d801006804003000034842007a928051883c402c200a150003200400d43c5d90b4030410b2060058000c0070501c0100014959450a18155441c02e154001e01075006a0110040401000d500030907003400543d40203901f81c1210610b8200788000012a4400a055000e80240c2904000155000c6810f580c02030380c04018290300c682081005110795144d401da40d034020b000410210f01a500150340c0038690b9a03035840b5065070760034041004040a6200a2502d330045400d0100800d540414001003824031180300e82c50415440d1240c54606d90702000e00f0038001703040001c000900d9901250028013000d8122641c660744c402c1e50841010085503401e01c29005076400165924042d680c00621302d01c1c5019865058589130350548060f0300c10240300c3c0e04251541c4101d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 720700953 1250 720699703 720699709
    0x70506090d08040f0f0e04030e01030f0216031e030204051f0912080c06060d0201080a0c091a03010f05010203030c1c09080c030702030105010803190c08070206040b121b0901030207060b 81
    0x500020304286a01300712841c100000a00c03010240d0b08100204e500c0041000007007548200c072420700740c3e000c0c2000521881c80030304240c0a4480c240c07000c00700550082d03081c000c05502542c4945040c030700b08590108210b000d9401c82c1030384118450a94030003044412281c5500c0b6059507150319044070b052040c0d400b41e0710752407925011500c200940b0504d2021502141300c3c02c091054513404002205c0c2c5869140190340040c10120016001c0124955140c84607801c4501a52520026000c501040081125842100303035555009000c0d6010b0b40c020700d81d00080c81d50000050700d00039020b9000c00341c240300b00d403c0703011007803508010307240b101a440707003884808a02c044000700000d84903400510764941841c0141402d464045c0e00c62611036004100013010404404c621040c0030700680341112450485040c8115035005c0d02c00b010358008400940010b00e81014002805840d5601d13010000a60340c1107884803103103006100741e03151440d08001307124040d031090b8010b0a010384a02000203464104d84c001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 720702203 1250 720700953 720700957
    0x1b011a091e100306060f060c0b1e150f190501110106241e050423090903030601140406090303120f090b060102070b132c070206060a1205070506090d08 66
    0x100700b0100b501614140305000d214050b8201425070860500065880d0041c014813101d12184047d00c25021080402d0394101e0f41d400380d00200c190b5026030360340e42c00e00300c400300300070202c02201030721880c00014190418184402c030040060046415900305134a004015229001c0031200d0410305d540c0d03440e01240c20381c46158240d081c50840d11201c0344111903044044c00d441aa1150355121040114401c040242d001080b5420354110044003840030000d16000d0012030040400c581d84107980400f0840d8550000004c0c500c1908240e94034503410600244150f243d100314000d40000520b102c038180013281c0030348490031010040d0407000616803800c2050104603102d920040f68020701800078401250fa04100500c0507100c071950f00c614040d480008012004a0b030f20070a078446500c40d0b0045500e0300348079900c80880d00c0301089030301c5a142c80c600094507804100c4809210301d50461001c2601e031020b0240740391150f80071004010f00d6040108000d66a0031150015512811100e1148005403030940 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 720703453 1250 720702203 720702211
    0x110d0b0d051510060509150c160b0c06010509040b04020108042d060b04110417010603080c011401171902060c1b03060702120307050f07020a0b1b011a091e 68
    0x2c030100c030b1400c1c00030903080544440d501c464108081400786d110b255607044544003c1d064403a0805070380c0c0100300000350400c803550b4490410110f1042c1c00240c0408000014140141c1000036944107a80b500c01b00160128250f40c05002d2800c2070300003a00550158590b1508180161092804107070a01c00c01071000b22020318185d00c000038000d0007070421903640181041064101c0e018000e205006a1500c05d50161b0b100341000103841d0302c03031b55190344020351004019507008240680c0e101c0400310124060660291803555600505c000021546045005a244200e038240540121000a1201e1000403003001c020703130340501c0411940c41495000c0080e845000045000b81411416200806081040051031081503412080d101e140d200403250499a110b4a0b90418580310100c1070745280305030180600094000c151844041400b5000001500041c0c11181410302e0244030310314103509030b07001d07144410010701d14500354032880e2504650b8158880c2c25268441642c92400c82c8002c50010203803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 720704703 1250 720703453 720703483
    0x11120a0212060906130203041106070f1b05060304080703030e160503120a05120a0b10050c010510050a211b0f060306030305030a0c1e020606040b04110d0b0d05 70
    0x40340c000c120700c60505554030241c11981903034585041030104840328440444198281c3d80000001c3c10000c0070421012808409482d650300c0700740520b4402c1d500c0310089010b0b41c0203000007220a4410080120740c905840380a0490f50035521969241c800b9034210f110120b00b0301d61103040c807180441e410800d00014001100c0c03006449890281810700b0080b01e015008102d2500700600081c00303410408480840d0f4403200251096030710000300500504c5200300c02984000d5a0769200e40d1964000040d04450300840e008000c562154080c0101603c1c0314401d00350408090002000350100e40c1c81c0c186080e901d50840507a00040a0f6500c400c01585040b021442d402d0b080001d0044a2100180c00007500c09400c01300040c504548010700180030050190342d00b03c1e1640200300e42c01d84502010a006217000a4682c1c600060306400b94841c2001c41c0c20601503483c2442841ca1403600d80a40c00080e8400300da028542410b450008002d00ac42e2281c8940000003034022030001603040000203456079140c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 720705953 1250 720704703 720704707
    0xc031e070b0f0114011e05070c08060406091205090102070302060a02010b0d0503030703060b281e02010506040f1e23010602060403030506060901022e0c0e0a060302041811120a02 78
    0x4c00743c1109006881490703410850010000700c4103403407110040417038030700314104103803a8401c615164131004d032180c000e066240100410700040000542024625038422540366100d1412319100b2200381c05003541044c0140d00c40d01d010009400d200c00200348440241c40040340450f010320110b15441c40c0c0400c2210503520000030006d0749a40741c41440d010308070018003249040c00d200341000120008101e914602c1c0d095000a40301a402541e00b554290706625084040c6a50100064002c1c44100e5890740a1410100401d852075481d1050b054001944401d480c0207005c8441004000d2200303000001404a00b100e0307030350001e070604144600a14059008110b181b0b40351800400f5203102606903400740030180440d003007580c1c0202c0c9106510880c00e03004403a00e00d10360007640060714050300040c52a4503204500720f0f502e50003860b20083c0071040c2c4440741090344e251821412807040b0711528922100c801102c12180503a80c11415001445001940c14000e0030059504815410313070310f0800e443e0380 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 720707203 1250 720705953 720705959
    0x1020408011a0936010b0d0501020d1506020d140403080408030715020f030601030509010b091618032a030615030b0610080c0708070506040c18020c031e070b0f01 71
    0x182c0310072030303101c0c01043c68840c10300c442030020300802c2c02d016403001e68107614003013080800c842584034000003d0300900d410211000c1e81441c50003540483c8201a42c1c909080e80751001c5080c030b4010900f12120385d8000c00c0d100c00d40a004a4040e900400031041c010300c20000000400c4c00360003d007000c0c0c0725080140d0350f40c40c0185070941103186c911841d030040328010b204507914000c0d404140d03640300f0402c0c2070104450752140100c50041503400310103903000302d18105200d1030f581071070040c422443c1035444005082d6111003506100110714400181040883c3c0213840314011038402d01202c995004286c000381d55225540c200564200000c0820441014082002400507800079680c2242e800d69900384590a401c000a02c000c2000b040c2c1180d0200015982c02085068001c44000300d41090075111a0b0506140820358002e80340309110300f1048a0040503c41d15692080741c4003174043c0c0000314600781c45e0110702d0007100b41014450050002c28080030b804900e0821186110381c920180c042c95644c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 720708453 1250 720707203 720707209
    0x2180607031809060503030d23010b03060307060201050910091410021207111b0f150306040c020f151003120201051909030e0402070609050703050c0a060c022101020408011a 76
    0x281c9603c20400e0f0750808408004c141ca0100c101e49010204200108001609000c2c00f034010404040041c05512118000a448a0143c010714001c413030031016503c80c41c2da0b4a804034240d074007d44800c4c10982003100c2100310f00c6100e034048444503104d00d0b09940142c070396001250030000c54040e4000a10740008040b4108140d40d80f900e5800311060401901c0300d101040030a68485c043e40039a01c1b144252010504c195448a46d501070003000108441c50082c001030381d03850a0780040d01c40314011401c11460082050010a500420010210003000c07021014207802650f40d1010340036002d48481c0740004000302d1107283d0403080200d0a50004226402e11300b108491100141000003245840c20302d40d0740010340d00030802d03c240e070300445001d40c81700c00506109004142e0585d0082c800d100f03c03100041004000700360080040002c9640010181d552007066641c1d42041e10b0080d40500340410295090701040050034003940f46000060420f0340700c20507182102e03244401c01c84052060302c0d01e82c140307107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 720709703 1250 720708453 720708497
    0x106060e0d080a080c040b1b011a031506040f0e0f0c06031509180a050d090b0a090b1309060b0904110a0207030201140c1218010c150218060703 63
    0xe05903807910078040151110303189405120900c2082146607404560030b480c0da4011342c1e016001c500c04a50790b4074181c0034245203036111041101c00340d500f040002810056002c401400c6001d016014200d071410380c04103d0340e0f800d8001c02040c5e006590b00c4032800445841c0c4070340c80020341d20000424008102c0141e292a100080c610385200321320400400070102d1860300b40c6280610251100d05590f1100c040d0340e8240310200070114018424140c0fa0000d010001845040c10403450303c5c0c803a01c403911203000034910300c610303405400860503651017001212008001083c4c0f0b480c000301c0307800400740c59054140c15102c0c50351000542c040041028405482c2a201b1545455500e95a4518001005102035103c035090f00c03019050001c00c11540160344a0b0004450841c14510103458031801010079000c0369420054001007a584880d801110030350065002040e200d401c68400b844010310314140d54040d51010300264085c00380f04402507101d41f9200702074002c40c0c0c8207864900303030307034540118400c401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 720710953 1250 720709703 720709727
    0x3151b030c030121120f020c0907052a1c0302090405012606060319150c03060f060f0806240706020918010b071511032523030711060405010606 63
    0x50745100c6060000100704445241004456085c074200346c0c036050400768140040303e080c10344c0007c0d403001041600c070b80c000000c0210212860340e41303802d807940c0c00d102c3c0e075400c1842b84443c085601c503406076084040801c0d41032400020f1407401502d00b084040126060340d9081e0b200210036038000000860740c15074840303001070b00315107940100101d21707002001a40d542c1140e1046c1000c0c03108100c61105100281503e48070500005c042031201114400006004282034441d005203594000345c046816032090006124004180c0d0300c2e15829281c3c8000c000b40d030121115800c1682002c0ca1001900d20303000800381440a0140d00f00588407131000c000c1c898082c0508003036003440603030a00140000082d071819100e0b03958100d01c050005000d04207001d0002c20b500c0640d1420800040100506003004060b1080840c1c4130a00f0317000c010303100c2d0038165409559004001c8131140c920185441076801d00029650001080c6010030f403011140348158181030040e1000c1d9004c0e5155402401600e4100d501e000301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 720712203 1250 720710953 720710999
    0x1104180501080c0d0f063201030b0a02042412180b1f0e060f12031e090a090207020d0204090b160e15130e01060c06050f040203151b030c0301 62
    0x194144c030741d076021925a441c00c002801030303940d03030881d840900c0d40b0050aa0140da40b620041820742000b4943c1c5200c99091000702e40301c02440c40001e040415600a80307003180c4c002200004d03d804003501007601b00d03016210070020019110b194610102032801103851540c0c580a420200703c1c01c500b09203880c03480003440c4c210400710311801200860701c2d0304160301c11646451501600340d1902000902c00309480c02c110f507840500761003c0c07160940e000c0000d2513034411482000303078480c5284102c1711302d0b40030303420742c582c0d0000d98500c08100201a903002845101d2008110b42c2020032030760300180454004c80410b890084464080001311000e03031070b04400100c46428000c0c1d0841204e0002010b02546400468040202140c2c3c01121654071280304068000305265295541e190308006000c00102c00e400d60706181881c0104068512095000d4020384c0c0160190041031010100d5101121000d004500512146c10080360031404000c06540030b84c0d0010415a40c0c0e503d02111181100e1440b60400710f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 720713453 1250 720712203 720712219
    0x11d030106060504091a0a0b181306051f020d050a230705100504020d0213020c070311030c0f0d0303020c030f0706060303030501050315150310020706050703140405101104180501080c 80
    0x1510f1f9039038188003012a0a204003840d80d44103132005038003034034000740a0f590f040240540c4004111041e43c000c01c1c01c1c0d40e001e64840e0f003600c6202000080c15901e12122101607007100d034801c03d29912940052866404c030f0709114855141141c3c9260000603580303d6201003200208541c000c0000500405502e07418410003072002d400c1035000126024003c540013446030160007210380e00d03080c564059450032564907040e40c00c400d64901346413805802c2d03602c031184130380a00081003030203290502d5503180901e000352949071202020b82d01a0025072201d03180c008207101c14001894076500c03120040181612841000c80e107a0f14501d0003a041d504103800041c800d820140d003000c0440c0000342040e500098a000420040e840e01c4040303824001e00c050300105e0503000055200c14052280c0009000e16415a0200848034254508100d80101171301c0040c0250000d1415840d1100140c00c220700c9842907a40300f91800ba0b550100d4a51015081c000c0d00809072140010040d81c03405000c400c13207040003500c00791 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 720714703 1250 720713453 720713501
    0xf020318041e02120103031b170a0203040e04050d120507020a021003060f0e18030415050a03060512060a050601020c0307030303110f0f04090509120306011d03010606050409 76
    0x450a660184129004690740e05160800090b44100701c450605000d9045640306100a405aa0306400740401e4002c01c03003400400c0c00d11050f5400700141d241e00401301d14445a84850b0004560b80200c08850843c4428030000c200e100c040c02005004501c120001c000d811082031001c0c00b84000c0f0500c0c0d2441300e2520040004664000c41e0320708c1081d40c1120b071081d030108101c100381c000384040e403c02d640211181401041c0c00e8480170a0038090090308041c014110b6111615655038810350042480364084001c0e002c0c0aa80140081c0c00541c0441c02c000c1460340d22900403c111240400403001076900040030302900c803210b03108540d0412001c1c400703402020300030380100360340d520345102c020202b568580e0040d008807207800c1924914270b600b41e0181c0d80c1e80e0400034001080c1d0018000c0700030540c604000300da00407800090000907421108082410769460b10019070740d40118180d2144540303458070030360390244c1d405e00c2103501400498441ca0340391400d00d4030300ba00321784850f910443c080142e11004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 720715953 1250 720714703 720714727
    0x1060f0801060e06070f0501054f0c03061a090601020a031e020115030507030b01140a050409061404060204230d0b06010c29150d0201110a0c0e070f0203 67
    0x103c489000281c030400d0317480d0940d140180c6035590800002d041075182c0b40900054260014240c50340516000b00d440403042e0032240444508004050326408220203034141c00280a205100c0c51010301503040340c1c44107035894540b4401d44514000c03525031800d0480001d2030515204805a800c0300080c40200350904041c1d40c003601600c0c0f00b250050a404803d035442d07001e01c3c400d400c0f5864110300720b000055882c1c0c0c0c9142503641c482c860b00045030404040340000c50301507010a860510010018030248000d440c1000307000050441020654040b5240c07901c0b07003005014640e000303009a20940300103959034502080344041d012140c00fa4000002a07400c84082962107a05801c0a15042650707001140c03141c400503030f49250f03480b80082800d02060090817850448816001c2c000c07900c1039600040e9038504c9103000040003403203402640140006000400f5501c84e240110112940008a850220858407000203c3c001070780840040002d8904210503143d024031220111b8409000850030710a08880c6c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 720717203 1250 720715953 720715967
    0x20316171005011107170708061608130303020405181602030c1e010e120c010b040603031e09120b31061113030302010b040501051014070809030d0801060f080106 71
    0xea070704001c0714440905588805201c8140284400103104405c040d85240381507c540440c45645c0c802c0c059100001c41d44840641d107004c0151041c0d031049040e40e075044e41c5c4c030741c0021515000d8003055400e000106090715101055840e000c8440303031100191801440720200110318080490440d00180100d0844802c0024200014445031118030740007243c0c0d200c01030044c0b031065501d10507489a50f00340c1b01c0c19142c0c10000d00c001d81842009125540c2c400c1d081c00709441e030350700c0010b001070104004c0804a1001a95240321003641e450f000000640d0b509502d03661600045058450b038091505110030b0015004807001c10410708907100c610040d00021501c2c0300d030281303800070700880d81710014280d094156000311414030305a0555060302d140c403410004e009103101c0b2000b80c081c601d0200041034034545961003d050804030754031780001210811610300280c12520341100e0050041c40100c81590f03003484085e000c500e00355683c2c1c0b0250b2510100800d0801e005840b0000e121141c1c0040c031025900c021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 720718453 1250 720717203 720717209
    0xb0c0c1b030a03080a200a08060316120614010b040f2c090a0b13060c080606030a0b15040312091415090607021f020d020609060621010203161710 64
    0x134140e095682e03a007030300000f13084030807500d09150121035072001a4501d12409042907000c256140501507070380000b0301d030f601c805000c0010701c0f0030b40c0c4080070820075440c1410080300901c1a030000c20380e0030588080180c500020f8010a00301c52000c14140510f0b0303c21202d2078024032100c403d1442102840980482008160f0105640c4241c00e000040c2210010404c00ca103656000040380d0041c41e01d0460300e9461803008a003142d400f810311021200d024441c6a030035004040c020442465501c0d01c1f0303041c10080c001c074002d840d0001232802e003110302d80610320302034401940a18580003845200d0500180700c4002500000101c55089032415100d849101c01d0740014555403681c15605c06030000066040e005508000354000b031705070700c040c0c1441014034800303850303c0250702101c3c4501c881c2541640c907800d0031544010680e000f200010072074a4040685034055001840d900152800401050300366441261000600305000030100d08440c0c1c1302c01421060020034092000b681080340e800303010840a48 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 720719703 1250 720718453 720718457
    0x1106010305060711340f091a180a020309070f03050a140d0c02060f040302120d0906050711042003090303100f050906090a0e10200304050a1e0b0c0c1b030a03 69
    0x58651002201d0012000541003186025150035a0747c410035000d00301c0408201c0a091058000110f20304083c4541c0308070a40c100010090707981d4041240c0002e400c010001d485511039044006080c1c10030000f98809035003d007000d813b50704020f041c40b2043da400420b50602c40c0e400b1400d0502d01c1035001007207101940e8102d4009549441c900203032002801103820295201002403031000c00c4010000d00400c6144051304c60220041c1d441905a40a0003080702c090492900c01100c04464034255005601031a00480404405100c142d942e4040b50801c5603029520fa0001090140d80c0e1260114100104041d002d0280140d0908012a1044c90b0103082280900004030124000c050141c004c2c0f20035841500480703120500c0c0080c104080c0025130401640c040d0781002003264146240100c1e4490b81e0400020542540c141c2e80f008480c000300002000c0450704d0306441400110000e0707a440c011585807020544a1140c0079209041440f1040b0410500c00803250112280c0c4005c14401c41c1c454040c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 720720953 1250 720719703 720719773
    0x2030d0509070303320f0a17060a03020415080a030c111c1227030228050d1104020a080601110f1b120303010b030f0f070c0b071106010305060711 64
    0x82580f00e40c06280d1756031980207420000c26040f1a83d207022018150800c082e60301c0030b8401950f005110b51500d0b00b07446813a004440ca072020701c094200358000401688070719010302d4401790364400d164206584001c0441c0050590020b03002446280050740b50100400c07124484031400c0c071850405a0f41e0004802000364211900c40c0c01c101d40211480101c00d0030806050190030707074001e4103400340100c0d400100d02c610424610404400c00c1a01e151149121409000a800e07051504104221608541c11103a820008a807034406803a1400548039140040d15600035070300300000054545c0c2c1802c10510b1865110480c4101c401000140b03600c100c90050680c0e0003100c180c3c01c0450804102c82c0ca005015100000000480c40300d01d60046104001c0440164015110000002c4640c130081d90b501002445204044c0c01203401803501c00d0300251030381014404a11000e90840c10320740240d2090710700303800c00810090469040701322900d00b581c0d08030140c8602c40500742c09400e103840c0c01145102c1d025003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 720722203 1250 720720953 720721007
    0x203090a0b090c0316150203030402030a02010e0d08121801050601080f0601050403060509100612120f090504090c1503062601110c0d030b0d080726040602030d0509070303 75
    0x418004032903c588050151011a201c0c503d02c0a5116010712581c44e03400082428440018800b10549000d01c0c2d00401404a080c01c1e6001116800300c81c2e26415131002c40e400440d000a64848010714458018a4980595103028140d0500395001c00c0e40e110890b0341080c040042d981e920260b00c0d070307125089100c82c4015469038001250f00d8012900010040c0d845c101c1807100000002a030002220702502041c0486034550f450700c4001d403c0b5500080090200c19000061f450140008407001500e6181c402c4d10103548800140075250f40c5001904d0032a11407200b40304903908494000303c1d00001e03050902c612440d2184081d030340c4004400c0720902440040405404c40420341014140f150301100c820b88611404d10042c0d11a00c10000c08004030385030103011001d60800d098a040345075009900755003841c16a840d8685e441c02404c21410702070007540105070005181c1030261014225a034021903d6456110b4007104442004d003c0d0825070b4480328040002070380c010031203042100c41040382c3d500c0350380d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 720723453 1250 720722203 720722221
    0x114100e0d060203041707020a03031d151806190e0f042d14070518060a1d03010905341401020d140a0c020a0b04030b09100203090a0b 59
    0x59030400d510080700c0c00341e60144041500030318080d0340180c6000050b080c514490084610034610002d4110192450810120b4018901c02c20000a41107890720070b0601c000008403071180d601d01845900c00c010513000c2080c01416411081c000302612840d20780303429440d40303080099070140703070343d08100d001b14018003681c0f64502d021405880c09003080c40600d00d0a54000d162040c04040c4401d2004e0040c020300444600c2e0041402c4059801020600c94031090011100d030341c400002c04460580c00304d40c840a58032100000c1c03016140540d40c84400c03810044a0018009510f01c00504c6170f0b040c03200c401c0200e90046059030044052020168410340c0c042ea80c8034081441d03050010551002840c0017907068009014019450426800c1d078030020b0301d884081d2901001d54a02c006020000c0c01012001e9000f406041e50706400180b81070480e0380d5030602510f89a0050304100c620103280000d01c40c0c20310040142440f0007a180c0010341c218500b0b0140282c0c1c41c04d072810040c00b200d01030302c04a1401342d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 720724703 1250 720723453 720723467
    0x5070e040501180e03130e09120f0714030c0a0305040f0906230a0b0304050c0907082406130f030210080705090f120604060b010807031116081b0c04060e011410 70
    0x225140e0f1001440c0c1e44101030b410007c1c048820b07500354007500d00035041440d0500201c440e82a0804c01c46400e2a80c580c072400c00c82070101c241040a0720040183c012524010400c0c0300b1054400e0341c8160381c4508201c118000140d0075400528900d050110601003060015103107800e01c42226800174450740c0c1c0d5800954842d0407a40940b800000010a000501070040703120301c82c6082c1551402003d480e1044e0072600c041e02101c42611980241c1c64a850010784001c1100c0600d00040c2103d08000d010b08202010040680c004030291450940c100110305146203510700060042c2401d601615000740c0280c03003031249292140c4035603200e1820010703580d10710040b600308025135822038000b441c1928001e03005164444000f40030403040d50000d002d080c803030b0003a8042c40c2403100e5800d04251010407801686143c010701150a80b80920420920654035205852515801d500909040801d001400111881e541018510b4941034006000c40e040846441e003100c1800e0b00c1030340c20003030700e044125060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 720725953 1250 720724703 720724717
    0x50c010f1e023f120a0e0c03030a233a050901090c090b0d0809040605280608010608192d050c030106020a021c0f0605070e040501180e03 60
    0x18800c1481d5003159090440310b0f004070350280c41010420b444040249186600601034200c0c80c003006040020010300c42c83e000b002868442000300e8407440d800c440041d0460700030201e141c0000780d105801c01c0c07029007202994403a10524070b110b03c2c5001100c03e07141582c030010308112001185c010ba101000d03200b0881000280d03901c48403013005203062083c1d51a02910171003000f0b0721a00d080c0400030412541500c42d000341040300034844100c9204aa8030748801d50060321503a130307100d42d40e0900013403281c0b51780c04010341c1e11100403100075140c03100030340700b408454440d0001400c01c06943c005001c0c2c150811803003500180c150b5030407000b12404407041009030a038065411000180c050f0b480040d051003102542140c40001c100b84155550810416401e001c24440d01c2c0050780402801c502604064002d8010f5002002031203e0785100b54480c0b00c500b850035141183d010303581c7c070100581c09903c942400107003001113401f8070055140485907403610301c02d41c8460341143c1c1e6480c3c401d03000d000100704440c49 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 720727203 1250 720725953 720725983
    0x70314090a050d05033907050915040e0613150c2307050d0905030c03030c1203060d05011103070305070e030a200409050307050606030d090308030703022203050c010f1e02 75
    0x689a600d903000d015402d4100c5443c1100c000c06c2c55198440040412600107845c0702404c0512982d484100e080c7c0003001c0352039911780103642e540300d412802006000040c410081500c59585207440c44c5002070103900b445000d050041d2070001284c41080e8003012910083c903800319040e01c40450000030118501c1425030061551284006004070380390480100302c201c03035084096501c4103460302d0070f2645030300c00c50701c0303940c06038010b40d802da1008100f40f40551303000a0302410600000c1c0341741d41c03440e08440640c0c81140c154400030042002081d854015903500800714941902c00034282e0f0086036584030300c2080240800c500c0d0014444024404d1000380d000c85004006000c0484a4185141c0780c0d408035070240e805002e500e0000f084c5040005115144092656529601900c2d544a00c0340540010b4030341030416400300300d817440002818110a8031f1f42c1d18649001011840d5140c410301c0c1004030701205040c07260340d02511000941100c4001c4200149080b00c1d00503003001c140890402070000281c0203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 720728453 1250 720727203 720727237
    0x4030e120109121e081803040b04090f110702010e0907030b100905040f020c0a03030b0102101a120d0203180f1f03060902070c0612060b0f070314090a050d0503 70
    0x10034040e80301d01c249030501007500c0d030601301001d03039455280054011880002092504000c02c99042c107211145e62071280c4c0c4019a410039488140e92480d50340130303602816909403562201169124030b0b201d0a180c80201002003440c02540341d0000e4004403485034024811509200010000b5000790880803c0c13602c02000f0000303150703c200b0040d2200c90711b40a450700440c03800c0359800620040340300311220085404004e03d1200d02c41d540460241c0b02c00c1c820181140107280c40741c0c5090480d40940c0903000b00e5000700d2103080ea40c07441440080c98943c000313000350b58844484a802c89401204540d40003c4405108550360060400b20b00c070000c2d01840182c1001580c1c50a40e0920031104450581240c00d503030611070240d880300044264020300c040602010f03034414080040500a100d5498052491840824090342e2440d8034000382d0010000a01111000120102059400341060040c030b0508113409080c91700342070105610764164003c139401030318150700200600c1000c00658450482d04081300c2c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 720729703 1250 720728453 720728471
    0x1060e042a1d0108010512010f110910180603020705150421030504030203090105030405011b110c0d1a0c1b01200901021203070903060911030c0d05030304030e1201 72
    0x1512a22444054000216102d000d0900103411100188006505a480c03880c01d90a04040101c00018407008554035076a4420403000c5c02014062402034240602c2103980321407981c000e00c045512000d03140010040c42c00e104160000812141d10103440701880c0041c1c861490f86401494003071740e14180c001034003890040204000c8103585039041d0340b00e16001e11464071880f52046d030a03580e0944000b80540c100307001c0c418155105002440d402801031002140b43c480025048807078241c902001d800150112a00c100c010030304101705c1082140584070f00e0407241003900c0350400081001c80c84000700c0d4008001c50080c10310314040e10140b1018282c0c2408500413050128000c040000c000740c4000162000003001c107035a54243c4101950607005807842d0044201c0305110b03580014800000d0113070070310700440410124421001d52a00c99403c07500120280c83c1018540041059058032070000d0a0020001903400f00c00e8a0300a5414200303100741c0411580001d600c1e80c1c004098078039943ca0b0844030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 720730953 1250 720729703 720729761
    0x201020d061214031908070e0904030801090617101a0303030a02090a0e04120f140c0102031e01060c0b09030418021209030f04030b100f060f0206160801060e04 70
    0x32080720748643c142c484100c403041440360302d03400f5502428804480900d42800348901908185034400710754646003008003000c10000d070781410140c1e02a800160407500600c40b00101d4800c03c0d028084e03016600000d07503a0703200510341c0e50100300134180805465100612541c3d102040d84a00c05a000307069a03264500b8080c040b00a422011900d071044a242c013000600c0f41d110745010703000d90b410a42c0a00503080814003a1040d07c403c0042800300f140030f01c0050316000f00700c40504030002482d0000f40c0d5a0408a050b48103a40e86480c1354640300007414010400141c1001d01521020391004001045648020f031540c210700851b404a03d200c010b038810709481c4580356004004203122403268464640360325200d15507a01803c221151003840410040c00842c0e03900d2801940b1104072880c01c1020b588455100360643e86607403118000c1080a90135001985d0140010703940007100f92020580d008a4081c02041000d0600c00c2405216208481c01c400d51202d8100301000c0144c081d815005141801c80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 720732203 1250 720730953 720730979
    0x608010c0519031413113007140d084b090415080d03020304021503131e0609050f15010e0c0c0f0616080a14160201020d06 54
    0x64601e400c840c0d0b20501105406886810043c90035440d02e0b26041c1c1d0f134861219001022480c00340e8900c2ca01040d03d400c00c0d41e0343c55010041c3c2da00030a283c0d445996100450140082103910803545c0d030450101408200800c543c1600c2c2594100c506041c800078a040100c41440781181c890540410150b1500c1d80340341c001c180319602d03180c0c002102d0500c0c036402035241fa4000c00c901c5901c0a51400c0044013282d242540220300041c10000703070031a805aa41800761714204501020b440420f80100401056180c80e02c0e1fa01c40e011400140706180d4549100440709003070150320300426024014050720340700d0300034000600c44030ba4000401c000041c01030520540da882c0c5182100c046100381100c2621800200b030203507040740e441030644141c5403a00c0407000225000079040c2c900b50b10852a5100194004002e4180101030811500308144181a4020b180d84c0300200303051909402d1101d071902c04e402c15038409074803c07844108140503225a42049029209900c01500350314180a00403980f0025415 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 720733453 1250 720732203 720732217
    0x1210050112021204030e042309061003030507020112090b091c050a0e060a0e130b03060a0e0c0d03450602070e07050702060c0f010b042c010608010c05 66
    0x341c4054400181145100368800c842400022003001c001060000b80a542ca501100b2401040810b401e0360503e80e104104240c101040300e54000b00060006d590710500c5010307004a000790054403418103540b00507089100c1c0340e000030f0400007130a03820280fa941c964400c18406600a09806c1103042400800360342c0e40400303568184107010911441c0c0c044e8064400c0f036540100c55110102c80001c15400c0003820340065120780c042c411103007503940d83c580c3c03550484a04029412030005a03440420149444c1040080010610740d18200106420302c1c4001040346500c3c00032109802074801e00d1130200c424480d01c040d4001c1d82070701001004030000d41466042e03a48428040b5400010180160500d01940144520380150700031010502420140000042d40302c001c0e428824584011a030208090340c0c0b02ca081a1103a4022016890a84c4801c0c010b82d2a0b0000498050060522656a5201e041c00c020342c0010980d04051155900f55029040b00f802007420704001c0001c06038a01d00980035070701c40c907 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 720734703 1250 720733453 720733457
    0x10b0f041205010504050f011503020d0812241507110103060e0702030903120313120521093a0201090204020a09080f07060e090c09220b0f0612040812100501 69
    0x2141d0307941e52440502c40c3c0050440c58055188032944ac41c0c0070301c01d40785502c075030607600000b04005e0203003032008001c000e0740103100307440e4031004074103ca012020103200c00400c501e102c1c2071619080d2030080c103030070700380c03211660808052400502c0c20300050b001040290702408403107060728104110b1607008000390002800a0342601c00c50805101846400d2000f190410701040400d00c800c8046403110310b42c070034041050304000345082c01c001c2c07403d40282c2c02d244001c840000d80d0070411103044401e002c4218081e21090411200600c1020302410a01200c03c0395081d181c3c90f010411103051007504085d690a030003038030855541c1103001e0300415007009030080c0c045500c12044500e118260001e880f50031a601c41e640d03400c503184940c0030030081400182c0141c0341c01d00240400c100c59629640c1503031030802c0c818044e000c9503116000003002e480b4205002c0e803090101c0700c8001c0345500c0e20b204980880e1000384405155a0f500c3ca030105240c021080003000c4002e01e04100100700c14170070702c030700c003610026 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 720735953 1250 720734703 720734713
    0x1c050f0a0c0302190507050f15070f02010e0d050927060a050d0b070c031e020105190e0c0d02121903080a0209030a02150c030c160602010b0603010b0f04120501050405 73
    0x34059060b413188189981c240d41003c2510341e505442040a0142540306000361010750300c0c801446490004c900c0c075510200400c42e014003002540141106509190a0000380208160410000c0d1a08840481402841000619030f4516541d4101850084000702d240e500788d00d9078503107031401c0300da422114070740510740d103d801041c10b00e0a507400600596005407260100c1c0d40f505001c1f6107140c4010011410f00050407035880441110580902180d482039000107194600416a0305104501304800302d11030703240050a0b0034402d000718181400341800d84241c1082880ca1001c00c1140b100060b9000c95800348904210565111050503a4002d0103590341070040d40b0b501001104074410742411592503401410500c0060800008007007103400c4030a1094141400c41580a00b0365001c2c0780700b4031107600002c1c800b00b6911610484000540031901c002c22041001901080c40da00c81801810507038900416444010080807003160043d18104200c1c2500041900c0c290b40a01410356080f1001e000d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 720737203 1250 720735953 720735971
    0xe0c1e0906010e0603011418090a0c05010e13020309030c0304030b070e1e04180605151305070921150c081b030106051308070b0c0d170105061c050f0a 66
    0xc5511503d00c0e820004007001d140d0303464030040ca8010003104a242c0c2d001009410010401c0c80c03000348152003203541c10b01400042d1b80c1842c110051001542056041c8030400d40ca8480c1e0b83c1310038110031030b448011030005a80f0707110034030198658002c10305891510f100000e4040304000451450034061609a222010303c6c921400401041d01200c60a10703008000c048442086881c00ba08000a038114010b604041030b115611603006440d81203407225200c1c51030030021540b03814500440c201402030b0074000c00150800319002032141d00c0c50301c40c0315010502c0c004d44003492107140d808040c01c694400c1e410b00c080e018800001c0007603c18000302e400400c0c425000280002444400314186501d0180658a141c0c20110180c903143c000100c82e0032011091030300440e600f5030411400c0c0181901d40c21307007516000308402052a0a1000c1c04400400006081609520710240f9489040d44e47c100c4006449071401001401003d0045100c64002410f01d020f01400c010f44401d6140266442c240030300091075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 720738453 1250 720737203 720737207
    0x40810050606120703090b1008190f110325050f0105070203070306023f1303080c0f07050114010807051503012d08010b040b01170601030e0c1e090601 66
    0xd030441d50507030800c200308a511030001200d50303410351001c264100015100341e03945550304c100d072080303600f070a20409400d01481600c1040040d000880c0250102143d503001591756591700c142201401010ba001c3c80106400d60340d001d0016280d000085003601d4141311200c00050400b801c1807051038001d00700050a41c2c07407540300d481111110f81d0040c00a040607495a55080007d5100a00302410341c109101801c01c0c0f08043d4103440e07140c8078500d500000c04284205441c0600c800500801d0306541d15030100e41c0041d40020750240c1c031180c0b040890307031200c60032420b03a100c6108464000f0180d510344581004004c2045c1040c905a41280b07048660540d1140244401408841600c05001d00f0500041041e19214048182c81520004038071075405145007c04d8540d0366a49c000000c0c99440340300151041c10a4400c10344518000d10f4a0b001c1c0e598000e0070104071040150030302e4101030f03d0701052959481c040110780142100070304186042e02a194a4925903072014940500c208c2c0b03e2000301d41c0b03940c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 720739703 1250 720738453 720738461
    0x12041704240302091206060f0103022503020a022d030d0e0405180a2405060108040f0f0b1603051008190501090f060e010f1109010c050705090c040810 66
    0xa0090810410000060101c8010341425070004000300360b003c2240f8549501c2e01002400914400c4008101c1800d104003040550007200800c503040500c1400200c09458486d1030240c58901b11141c5160040d6050504a090032740242010350070034070012501c0811907109040d150b002040c10140100300851408150b1070700a42c4085600040348440c0c000303218500740d800f550f04444140003480d0300461201c101410039440d06d03400d89003031003d00d030060341d507681c0309000c444901c101c070004011610301303100068030108001c0c1c00a800e00708244420010400012503485003190402c40c610110714107040d10a10b1500d960b01004002400d10000c1041c11402da2642400d4502c08d1005d0440340c00440b4501d80345058400d01680c2030764840200c240407074454042e10f01030600032000810460342d03034640c5034252448941c114074040e146c0388141504003190010f0390b041032400d2030845842140c0d81400e901d010401d800c0190310082d07074010302906500c1d80e8014011911010180e46c3c584403e00c110f4000c403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 720740953 1250 720739703 720739709
    0x308040806070c0c1703090d030302040e09030c10020f090411030106020c0402040503060c0906070b0702030a0915080402040e03040801020c013207030f0f020304050f1009031b060b0612041704 84
    0x20480c51014080c118128002c840d00c85c031400100e90804004100081d00b900d9a1001035011980c0080c2c00d0000700e6020000e5988542224021881c00c50400602540c50340c440041c610240d0b40481c0039041c0c5200d080880744541c4006009101e15460100085140e0f4001e10407640175105039407260f08541064005c1d02c00f01c0307000030302514155545070100303c04c035400700d42825408401000705400041071000d5890042c0255030045490340990f940140400780907800c140d20541c5405504902c3c1c0b540040e0a540c01641035801060441307100012038950700031a00a80020350020454901c08801540210321904107142120f09203403802c2c00c60251000c401d680a032240031b440f00041c440074069008856583c1c000306001a01090b00c002520490300161803c807900d400600194900c06410409424444400102003000e0142690042c2c186040800240c54400912a50005000103540312510300600904941c3c4d80e890b55400030b030410302d02198111050410700040c8503001155006a41c15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 720742203 1250 720740953 720740963
    0x914060a11160204021303050106030510020c030a1d3105070503130201230c0105090607120b030102090607030c06290120031c05010515040b03040602130308040806070c 74
    0xb0380070398102281d40641488000b680c110303408209081c01a512402c0000045000d800001403280c29440c0c0942090130040309041010f0040c401344d03c050002200b19021002982030040b0f001d050008030f00c40342c603494000d140c1d0051404101d86030702c0342c2840d10750480b40028404503560740391100050b400c903079003507816100041c07050001a0401d6520b50302d0700c541a0050600d1000c10003070b110344208012031421030050520011844401c0d5400c2401540e411000c17280180040d89450a001401c1402c4031110701220740d260003c0a01e1600d0030f6040f034403d170801030502a6201a142030184c5060030500c0120740b40c070300d018944c105940380801084d410301010038208071134800d81d00c01150070700b20100d843c3d102103402c4000c0c0160850100001c000c400140001c070030b07404040340c00d0601251030590140e40104000c242904051890000315402d940c5101d00c41e980769151070900070000d010f604111101c0204001010090048000140007200c2c060000c41d10301d42c0d944103085a004205080c010a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 720743453 1250 720742203 720742207
    0x10902130807060f0c060b09070e0315010e0c16120207031a0106050d05252a0b0c070302070b0304080403020a05180105270c0705160e0a1e0914060a11 66
    0x8100c17481100031104003400741c10042000610380000446605054030001c003c20200d2103021203d05042c0000d820748003100c0780c8411158503045c924031802d0001840920328145c00103031b1854018410600c081081d402140010b0b6044100360081d64a1101d404261906078440300710026001d242400346042c0c45540c2c1e6481c0c14400c035152050301812020300007841540144409416151000d40a000e95080380da0321460351404603401c190f070750b444818500800c0050851110045491540810f811054040d00f5554409490034202e0134542d0540112039900e500100344000e000c40326002d001900e00071101c041441e03503034208022900c000346400c0900c2e0f685401c010020381c0382c40c4501e01c900d141140310008002201c540300c280351407030450f8583e00d140f0000c0307450405d02c4070801101d0001c01e10075440b4030788241014004a0034600c003c02030b011135078907041c20400e002501c80b4600e03012403072401c0512800b0201e2034102c001c041c2d00307010040c1d039115510005c1c01c50000ca014400415003050303080e41c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 720744703 1250 720743453 720743477
    0x23030315041e0f050a0f0e190c03051b01021b01020d030e03131d0702150a05060d12050a0f080c0901112805071a250b01090213080706 59
    0x10014000c01d04a10440801e0401c01110312002401100f20084101d68001a94900001c941040310369203030320300307800c10301c3c24a0302a40314000040729103c0080c9800010790148951a0000a100040e0401840343c0039650314403484070700421250700d1085e801d07001d0381d0f08009850282c0008110550841380103920003106c40725264001e500442582c400a400c3c1c0b40740ca0101c2e9031604040105070321810b40d80f104c0500030b503224404e000d882070b0040800d1010301142050b0b9a00b000780b1990103072584101c03d544402142d042c0d5101e48046c0406a403080020480ba08d421b84041d04941002e41110302013072039030080d00c11251048500b00d10a08400c20301e507003800079001c01115003103940c4009801d14454910303070321040841c03044000080440d023200400510700c589801818654164010f44070380406080112040884d4010313035411200d40740e05128000c611880b2105219007249000d424842464000305000000d90001d0002604402c541c1000681d5241d400780e40361070a100d4040083c0890000d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 720745953 1250 720744703 720744709
    0x7080c062107020a080310080c041a01110109020a0314060f0702070603020c010e06160909180206090102100906150b09030319021213060305060108090a06020306060c01020723030315 80
    0x507582055280c4101c0c0c0050307135a6503c0c3c26a40d0300c15075522200211006081200701401c1042c600340020a1f03d080c131041c2c090406c0c0310780486004162505000c4070306c003036444074070095202900694004240c0074840d5900d0234041141420300750b0500140c0120000141d03014505010680256060350040034400d2070480210000d42101c41a00760079500c444141035141c004000307060240702814103a503d0100080d00181040c4403540c041140c0700d0802c194004400380e9190018074035601030b24071a50721a62080101c0c1405552032000003d030b49810140b03020f0191070303130242082c02d190350012250151280490882400707a448080d0785a4003c00280c030304001c2c0000224510603680c0100c41c02c0c000303a800c41d00c445421541c00494204180c0d10100401c2d64103004143d00550203081c141ca40f0300300382000603225010803401070100e0b500040810381d180c48200c03c403600c00601c40002c40d200c1409192464540500400c1d14545111044507a290840040116401420032030b0003c2012110070041c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 720747203 1250 720745953 720746017
    0x40509011e03060e0a0f1a01150c1e290112080706020a090b03010e07090b030405030a1103040518060a081507081306020d020a030c020106060203090607060608030a0207080c06 77
    0x600d4501d02034241d0700380004010101b6045000d2040d40803031900c8116110111140c40c0507400905526044d01d240e002440d00300ca02c43c1010f58008140007161442507101c8810200408001440344e0014400001a2480250542c25048002e1a090003036641c0381000684042207810140c02074401700100710000350b082d0b005090a141030308002c40416990a10f51400e60800d17406404e46050b028204148264450841000f030420082d0090a5080540311107980307006207080700003446940a885035102e00c082096500a05000b49003e031210305030080c07004a40c805071003d0b40140205140803c00c88000b041514201c0303c0703201181c00303131f5494140449401d500641070303103620004c200c0c2e11008a8100d00040024080f049005a5036420404006040703444448000e011a4508181844401c0d8040121810000100c48603900c2c0c0c90303181441001000540c1c4841000d11002030400c6419802140c11021100f014043d2806c5c02516400c0c081d0911030009000e000c55132501a280e00c0b100d079001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 720748453 1250 720747203 720747221
    0x70f210218090a151b050721030902010905090408190e130b09090d020d03150f0e011511070b030c0d2a021c030b031c05040509011e0306 60
    0x45030300714034107800008601024080e16010520740210164a0501508003d4504464001c000410a03280903450700d102d440c0200354100100f10700007a5180070b024440018a00c00c2c09480c0c4280709a0071203000c00740c020042d03c18120301280e5a0480000c40e4903042040768812a080b010780b91410b22550326040d81c24440d52920b0b000d0001c181000c41030307a290285180412814068005803200c1e80f682040b0240f03a0040010209038007c96034085410f0340815100540000303401d0204140500a01010030100fa5400003400b01d840f07207600003200f03c02a015a4122028078000100315103d405040321034040f03420302c03a052030b031207940f04001d1804594025036000c2d419200541c24202c481d0701080c20354130a103078000d2030410340e0031100440620401d111000c2a100740002c2074100d070311107487c900c1d58000d080260180350303803829280c5060705c040c0554000a00d16a0191020256400e0f02500d15005030003858004e607400e100100e910151065008103200000ca80d40d00b41e40c2c99649c40d00043c003d042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 720749703 1250 720748453 720748459
    0x604140607050114220201200a080304080307141e0702011b0f120e0a1a04030f1401050c0708030f06010315060314090610290d0203040203070f2102 65
    0x90344001c24002e111300607200071300060a101c1e0781040e0540351844401040203003c4413051800600060380c101030038203103800d075035004000000f8101002c00d040003c40040a400500004200001c00a40c0c1000703620405da241c031000b14814242c001e0909a00682158610070308480d101210140544406843c00610501d1b00c0c990a21030f200c10500141c4010508441080c00c034141041000072428034a05815031a00c1d0100020b05190000351400440744a10508045030002c41c40d40c0c0e05c82542140c2c05560401c100d0014945030b4030744242000300d2030303184c0b4809529050215a85140050443d210103070058160303030454031481d00400c44001d01801c4d031410700d070782c0303403d068043c001c0b92010303600402003601c00040f1030320880080780311b0031401007210f422a000901000380c040c46449940050320981007001d22000d1007441480d1140322140355000c4a0640420704c9084c1c00040e800461050384240e0a942051350341e031070b10402c0e8000c5070142c0c00a2002c43c0c007103076200560490400351018002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 720750953 1250 720749703 720749707
    0x190e0a12170c0a02040506090c04030f08091207080d0c1a090c030706020307030201270803041a0a1d010504081c0b09010305210301080d0e0301020c010510150e06041406 74
    0xc0403600180d544140d500c18a282c00105080d82075107417511445911240aa951541c14906030000c107003c0e2095000040040201040d41d9040c041858155280010098041c0c004d110b29007420b00c0c1e0314152840f4014585c4211898200014821600c45000c00e07803202a5000320356442e0300d036088085008000e0380951007907d202d6031095400b00460001013090b84c010315035480c3d590800900356120120802c00e9071300a40320684241c0740c808810112143c02003020360b05d0345c545180c65035130b002e41c1420b0000d0900da56000c1c0445040140d000c8100100e5443c14a510021410760a0b82030798030455000e0058141400140d40c02c8803503002000407224420000a20039260074000344140b402070300166819070099000f413011101c2c54010580d40002c440300c9600315031410a06540d182001138085003008040c00c01e00c18252000d4050300c0c20b9a071014000d103c40e107800008000c0080030b07403207400840c070390100f0012442400b45c5401000440060591440c050801c070664070b214143c0e0240c07980200003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 720752203 1250 720750953 720750983
    0x3060a15021b1c1b1410140f03090102040611010b280b0c030315030f1011040e0a0e010c05040e040228092a020d0315090f02190e0a12 59
    0x1044520b0b01c10300c24500c3c3c110707181500c0c09940d00e510389900055003178002c1148108450340c6d0041c2c0d072407079002c443c030306090300d007840c0c00d0317019068040c0301070b40794905a02009000740b006042d005001940c00558030070800040781441d041c240c89248081c0703508040728042c25040c0d450120003824110840481040c50360342e4903a5068500e1340002111904c2c0e400c04400c1c0b200c0700c6c084036a5488035420440c0109000b41491b90b40f1901c428103640c00c0240036540b50311019403580c801c0e05440040c4103c01690382145002400440034144088645900f5441c11000b90241400396055409849a8160010003595aa4280301d02003c17407410348880b206142c6254801813000b10080b4002d0500020b0100342c1045043c000c090701e0720071440103e1561000448100b60320740c001030352200000e070392801242c1001d103d01800000c08440c3c021444440c01d2500b041e00007120382d001030243d40307041030480800c50349408003182c12005c0d0592156000305045810400f450302981112030041c000d400b200e01c4154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 720753453 1250 720752203 720752239
    0x1060836010203060a150207091e0f020a030c08090d03091e051b010206190f09120302120a0b10050a1701061707030b030d1b021503060a15021b 63
    0x40c0300516902690000208402c90810020200003084000000f4030f02d0313100c116010352100654000c4844d125621904040401607064001c0701d1000d00c4002044043d8014000d0381c080d6000c2d684990203c0c0c240140d0302da10b548910f243d244139176503c01c0601101c6d81041021805005a51010b0300d900c046c20240b1a0048003111203146001c0c42500105086403041003140301040d00c100d0068155000310040007908003405204001080d0198030024000e6509600308004005076500640301d00003104048072502c1d00b682c024029502c1c0070b10150100d0f60303124842400e8609581c900740e0404440c50880c11018061000f80c03801c0e03022401c15180081c1c1601c10301e01800380980c400ca001441c407020409481c5102182d8a40041072450144141401035020903039408045428004006009000b00b091202081c2d21840180d0b004140252a0034220510384e036680042e15424810700d0640000500c1e45010310b203001442d407140c1c001e042408901e00b849640380283c42506078001c40045c0904041314 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 720754703 1250 720753453 720753541
    0x30d0e01021b0a02010801060201090206162405010503070906030206072405151002152703220b031302090604180605180d02070e0a0b10020703060c08010608 69
    0x2040710700042140c030f4814000100300c00f5040e0702c82c10a591620201d0400350b240c50089500110650581858050152600c0e00344e1084550810a20b140e884c6030200001038990440b82c12140210300300ca8809441d500080120341c0c46210003540004104041000180b151041d8880c00540c54090408007400b464640146c9204881c5c400c0a00b600211440441c604010303d115a02c003584014120a182da03283e61565580113489114200360301c440c4010b01101e940702d42000c2440300b50940751101e40c0006c40b42c003280303516240902d503041c00b0b2402058495490059a00c140250007000c1c0701c2040301e40902901140203003202c3d400c2507c03030040240c0403841006450310244a420b0004151500d5400900e09100000403004603401c540400307416154005082030a9400d112082e10098039400385490041c0800500e250708250004807c0c018650040b03852401c40b4000c501c14403a4401d0640f08031050402401810003140f2418082581d400b0011000c044078040b10f1610340c000ba46000d106180d013 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 720755953 1250 720754703 720754747
    0xc1e0402090d0b191b1110060816050607031209050307020409030e01030510060c03030e280b010603020a1d0a0e0c18040608031606110307030912020f030d0e0102 71
    0x2103030000c0c140400c02981c1c040801d032000c130305079040200401e01941807000100c008a0002001418242c42080300300505c0f0440704041d46c0c03c42003288990340d003000c43c0ca80d504644100040034140100040f070741480c00407074000c10750680c1c5030760b0b440c00310701d89000c004c210f9150103132020320040c040c00e80107841d588901131450b40a901c0e4502013000701b100050680c0e2000b040c0d1400c9856070f1404204454000e00018085035060401050202807400000c1c0f4004552855092000b0041d400c000074032801184c079110113028038050355503a07888950a40aa1141820000000d442105044c20700051129201c03e001c00c0100600e04e210f948442e5041080c2e4140c500c15542200080c2c60b060080701100031209510042c0e505120074ad141c00c01d529101d001e803011500498450399006402c01403554013081d9403000220741143c60781807443d070080c001d103e10345e41100c1c3c0001d41d01d00745441c2c5000040c100d19014480b00110308e41100f4030700740d40181410200c407444940d000d01110003ca01041414511 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 720757203 1250 720755953 720755963
    0x2030f090613020112020904020705190210050306090114010c1b06110c0a050f031f150501021504030f05090a1202010320032a0c0604060e0c1e0402090d 67
    0x25040100c42182408009401020a52060001d00c070060f41c10481810100c42c2c03001c001a112102030f004207000e4412540000c0c01406013046003d8801c2600500c140454000c1d91b0030364008144480588a52000341c0c0c201d80d2140c040001005040b80302ca901010a14043c940407401d04242e6958054098021032002d0000c2219801448103a80c80241d081649128400408071840b003c40032807501d000500890f0300030348806076003c00ca51003c2280f10003648250400d1341081c9010600301005280400384030710300d050300c520700180f1903200141142c4151340c0340ca905d01194841d03075010745844c0c052024502c20f200f000e02802245984880c610001080480c02100c40c0310041c0c4001412a282140c20002889650b4611481e030740c0000287ea40c01035070b402c14075820551158000b45420007540b0480610000091010075408010900d1740c05940704042c00e0200c03844510b01251a1961180803a402000084187d950700d1504803035480d00c1c3c81c01500040c42d01e00b003c2c0114501c2001d141d001e4407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 720758453 1250 720757203 720757231
    0x60902061b100c12020a1709060403170f0610120606080901050705040f030314040e04150e030301060c0209041a0106020d02071a0f0306010306350c0127090203 70
    0x21040d00c00c2c4140041d04110320010808140b42c0700c40076040c0100990082800c0e80d000c58561030300b0340034401c25003500c000c0c5001c0400c203140c40c0f00c909640b41b0084404a00160001ea0521800840e60949500459a1150b0113100d59506002e00100c0f41da08014642005044412401e1851441c0300d04400b400d4150380d0420245040c2642d1070075118080c120b00e080100400c410092124400e10340d8054076810b251810104022111060310390203203401c14003100c400a0144800c01103455012072821042d0201071103c00c240440e10360320380c00244180e60108039100d06007001880c050010591082c41400c071074540e100001c49520358400f0076040301004d40d00201400002030380410144000b003002e4010f0141103000c00b08035048501483c00b10811550010003c05c6440e070080c0c10260182420700c00d5940f00c2e09801840d91580074040c015401d211502780140311003a00c4c04244100342e80d138185c41d044140300c240d0359410b111000892450b8001c20020b10b0102d8111002c0c0000c601494102424071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 720759703 1250 720758453 720758497
    0xc0602011a060d1a0a0f2c010b0f040320011805010518060c0a0303021b07054f06080304051c140f0601031703160f0e13060801050601110c090406090206 67
    0xc5020a1fa03401400030900c0f02c44c25110708414605030303a41035426021409441c0c541da001904624081da400042006808a0000c00e04156000700590740020980e00c040c0c540d015116030002c841600c0c0505400075408010a8181d00001c1c0046048810003a07c0f2910b0030213001c000d2810051600000c03000280c001400c6419004420414200700c205c8030098981d09141400180c002140c0d1f415891401c0081010900c0d4140c00250102c4010726510100b008060300c407901d1045114481625060301c1c0c030301600031030850f60000030f460644030054095008403c40c140c004070b6442c0e1020381165a141e0903a0340c4010081d0500c003000740940a00000e04032541540350840d84010b8070302d402c051941040c010850300c44604c1c03604c031141014a00300304440c3c0c40162030485101400424080c3c0082c0709071500e00800f81180c0c0f11034100c4031440000c0229031038040c0119403001d08501e080f034060f071140b080d2440030318011083c10340280c460303500010200e41c103601251441d0070039598030300b5001e00c0141103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 720760953 1250 720759703 720759719
    0x304051b011709060106140a0206010504050c1603091701021e0d02070c030b061005030f07031a0a08032d3f0402030d020c0a031e080301030c0602011a060d1a0a0f 71
    0xe6102c650300f0302841d605010308c030301e4003d554540c14440e5610440d2100080307011590148212110000b12148401c81c1e01e0040c20050701c00c442500c2031442004890f0340c04010582c06109072040102e02c40c2220301d0707079030092411190340d410450f05c0020581c0c0c20810032000641c2402c40000441c03081520401514040c41003004079444030690b035003400010003c1005a140d2210802c3c0d03c00d145e8240000c04480c0d0031030780c40d0351071503400d0116041000103801103000c040000103007a001c0c061120700900c041203400304100c54201c09091480079207051007110500700141c484010a01070388000310340e804000007281503e000044440401d5401c41030284425401c050110100404484c001000102c0c030f06070102d265010148000342c55403003d02002e07842501500c2da45440d50350841c01140d101d58481c00c141ca03281d005481900059842c03d00c03109100c0700c4183c9415409140103000d50b00f0b20001e502d04402030311103030300300860f0780202d45070a10441d5102001580604000d03107a21380c1e000e08000403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 720762203 1250 720760953 720760967
    0xd05071a090706020d02061023060a02100e0c030c061c051008100c1413090905030c06070908031b0a0c0602030d0c0806030303071b1203090c0b0304051b011709060106 73
    0x205c1d82c21034006100300300409100710101d8023200d410440d2900c0b401010f00da102c000c4110081c6056011400117151807510b680000c00803401c01507540c1c100414149030040a694041c034004003070f055001640526a54540140501341039140c8c1400c48902642d004804411a0001c90b11042e060060220611040320108003505902d41401d1003040300c04690f0501402c0440003480ca4580da8100007103040c00250710719060002000d44950905c02c40d403d5181403900c0350400e100074100c6200d103e002484151044640d10100c8a01201440c60716400c0e10012144000c200008015841000c0d84c4400055130203812100802056015607182c44c03a400d646010b4803900b6a243d41001800d00c04e0003140c1c0e0b0b020040701c1d0044024240442180303810440300300fa100001c0380250412034000500d130025a01034111140a520500201c100f26854100900e0a8003050320040c01d07551200032021a0040a049501c407000c80504044617646c006140306804a002100c5e200308a400020040120325000a4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 720763453 1250 720762203 720762223
    0x506010c060e03070c080d0c061505090109140601170a05040204090525060e03100b0f090901060e060603090c12030f070813090b09070309380601030e0d05071a09070602 74
    0x701400004501d11f8004204801d00e020261519903100c0d40103004604d10b007560b100615012700b0203403507503030349403403400003000c04c01c4c1c01030180140040081c41642c0328503680050340f02079903a001050b80300d1a100000070180100100c0c3c10550b120301c4100410f008220000c20021850946100c1e038034001c021042030f0b016544801c06011243c6100c01c0c03540e40c00324803030800c2d010038100001c0c6081e0395000192501c00c202600c54000300e42006000a454064008070140e5510005d107081c951210020700c112440203c0d007882607908201d01d03e201c0d0380f03844640002e00903800006c490811540030700002140c0c5c02023100703c44002c00001c007803180c031414019001c001d0004240c2042910702020116004280080000080607a544050020400244260090300c058240300d501401e5603055119110300c141411602d924102c0c3c400252298070034001c02d8603206228000d0000c0c8140704a0942d91504103d10450321190840c0c0300c03110175203640251501c00c019200082c21142c0c68080007900b4406044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 720764703 1250 720763453 720763469
    0x1e1506030519090c0b0a0518190905090705100906090506070b18030d09080304060b04090503040b07060e0607020a0b010803040305031603030b04111309020403150506010c060e03070c 80
    0x24040001d0114503210002c00d0009200c0b010442600901c2d11052071050764111460f0b1100104600032040c0c0e010703020b030082e00303800403105440001c03000410198140c451400c0d022152011020b11100758541c1099030001494804c0345d9555441d81c0000b01c0000408003150001a00c040302044a03551107502c0d5402080151020307854000340b42c484261400000b80060406252510403240b400b408108407180c0b4034070800d0400a0a0f202d141c0100958801d03a01035a455044c5000c500203481d04d48500181c0e958004000d6217000d05d0169600041c0e0041c107001d0f0303140d903552240d000450030f0500c80c291050605901410755045c051808001001041e00320042643c018801480095000012180c5204405001c0e1840c00c17070318941240a44908440b0b103802a00341460707880403e52141c0604081c201880101004545800b0b4a404a01a03440050400b840c162088040101e85a03c0345400c41d1062601005080742c513101d050544001044100183e0b0000540c00b0074803c604c21604003034442c80d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 720765953 1250 720764703 720764711
    0x40e250f14010513080f0618030313060b0f0a0902040e0702030c0604230a050106050307060f05030627070c11040c0e01080a021e03101205031b011e150603 68
    0x100c55424011030808003042c1c18490002002540c44004e0290b0b10000d040d0441110286800e242c08182c40e600f050300c0b6040b021540c00c030740c00041c040c0441580d2281000e0084ac03140c8002c0c5881d04009014054606074100c507201c007140d5696280c0c0c0c8006000392081c40300240c0d0302c40c50001e128181c61801030440e002c541003400243c084000104d032058000da0011000a91100c3e017200f03c11120b4885520b50900b8800c0c0c041500030490107400c900100d440407000d0b941c00f950303204019180c041440c2c400000280301040051114a071030045000a1000700030041c0d01c4d08241d41d0700d60100d200541c1c140010820740c02c048002c014110140c6914010b00765024808403d0b40900039211300160f140b07007414010104001515194140c5c181c2d5524104903481192895001e29444c805501c107a915140c0048051030102e07022507078100e2907000c598050015480d12002400840c0b00c40701d150400345955480384403601c424564500c2c806a914002c01002500b11031225034205c05040d107900a40615041c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 720767203 1250 720765953 720765959
    0x160311060709030b0a0b0f091302030609060c0403140111040303091a3402061308071a0f0f0c01050f071107030b15010c060c05120a14070e040e250f 65
    0x34914103c5e8211505140100360380402100194030202c10940840c1c1165050341003240c4060f5001401140b14003c0c0e080d40c5294403801c1201c0c0d200c4808440e40405030b40d040000b080010412800c104100803480000181c1d8100061010004c4d40b15034000d0780020b2200509102d044002d40000c420b8000d282c41d524a840590000c0502001d032000500303035540c02524140568014840c405001e20b60700410980d9508140c45005203400090b004a80292003240d9002c01c1030f81039103000450441c0042e01860400e214003101c1501a4080d1f50354009030182482149603800090140750b010300c42d00648282203142c40c1000400e81041140c070101164080d040400100d9260b402040d0420390349400e6611640f05a801640c0c803200d05000102490b1502112006055004014200c0040d590000c0c0407a602c401d003160040d0347c2c1400d05600c1c4000c1c0030002c41c401e140070b0041134800010141c00400c8801121541340e00300702038040c11060a000b201030040350610311189000103401402c02d1a282281 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 720768453 1250 720767203 720767213
    0x609180b1801180b0f010e090d050c150a05101d0a1104080a03020705040b040209010806190b0415020d050a0206060904020d0803102c010506090301020c07090221070e040f0216031106070903 83
    0x1441151a40500000185122f850f11040c8160306e202c1011004528035400c00f0220701000307000440b440241c1d9a501c200124500074904c0704c0304041082c030190644144c0710500480012b01f0b20080e42154400104400a200d180602881c00140e010b5000380441e1490142800155014205543c0c801d80c4100503480d0642c1e0807a10303140c1c0180c41541d642000803120701110500071841e40080604510200f000102412510030400560303507181d02380e501c402200d04042d6620b0044003101d0002d600000001105800d14a0aa5500500043c03034440c1011958403546030030350050340e0744544e500c40c00505002448290704200440705648410128000000302d40001c540810b0040d144545800181c003103540c0d400b5019514003130302181c1562a10342e81c49266034002d60110103005003022245032a20600c0700f08250140c85089287c55080203c0544010413000b01480c8920b1070105034244405c18500068041009585201c0e071600e11301909030068a40c80c200d1b0041943c010855140701c02d01c0022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 720769703 1250 720768453 720768463
    0x2203080a150e041202071a1809010305100e0a0605180d0f0905042a0f0e060906120907090606020d1e0e060705010603080d0609180b1801180b0f010e09 66
    0x154100f024031984c40e090301e104a0800c0302c59070010f40b1075007050101c00c10ba8454080103001281000007241801c815840500c55a00c4c003d100c0603003e034002039070120040c42e1540158031000180b17801c0d80c07001c255035a80c0c8401c9400c15a1340514403200c4401c00080070300100030b4001d68400c6801c0c00682280c0e01a001031052045001d5039000c3c603110f40407090305c2051050030340c180940300c0c1c111445000e0b0b07043d8002d091030648040080040e4000324100682d00f40384080b1854100054160b500d05081040c0020700e010000c0c049a0a41c400c0d0b81000884401d14407a00f0058203290340a0701c503503650050001c0402d00100c4518516008004a10840700e4100300d103102c110009907691500c5d41d0990800754010300459001a013114000103031044248090b511800072b0741c2c400307007041101c440d90556480190a10440050440020300046040d00d07040a4000c0c0d0001a040004181c482045406c070340c85444048080310075200442c14030a00c080c040741041d0140c130040c0c1d501d41b680d01d0803410312640c036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 720770953 1250 720769703 720769711
    0x90405100902010e0d0b160c0b040b070e1908010c0305060916020f0726060417030a0204180506210d051809090a0c0501021b06032203080a150e 63
    0x12075469040c442164084c3d41000c00074800100b00c0700c1d4800150a150820040c200c60898030181440e124868084c000c90312000401d400c0440504035a07030716607400d658480b0152005081c86115152a0101c0d51050380740400c0d032608001141d5010724049860f400d580c0c0050010043c58200700410050751580d05400f64002c0070b8030035031950896120400e07400d080850040c17903880d008418000c140310240c2070a40b0740000307014200c40032160700c81400903115501541c005042100f0051002d40c04025580a0f41e0131036111503005240a555004485800004101e1031340072030b4a401c1000114648801c030041c0c0000c1c00811480e40984041d0f0700340d1101c0d0707001d05a1040c8100403455444006c030100d501b03135428101800701c80301401c2414007603544040032081200d0304c2a600344042031a51011444084042c1c444050301c00e01c48615041203c2074100400760301d44a0303081404242c0d65031403a0b003066041c0740a078540c0100d0342010a218400c0e03c0e4140303104c401c0490845c0c0d0400120000003c000c0d40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 720772203 1250 720770953 720770983
    0x7030e040518100b18010303022803020322090f0b09010b0a0816051b03030402031204050102120d09020901231008070c03020f070803130515220506030109020705010b090405 76
    0xc028400000341c08105e06209200300c900300342c3d0001c402c042d0006400c460689090442c25540c10b079640c0a1240304001030002030040e00709210b09251680040161556405402007036443c054071034002c80103d03032621114811035a203e40c0c00e078019040c082c0441c0c0c00b512400045a1804d075200d400941103c0010308800c848103041000d400d92140b15009a620219a220102c0340c0003400740c1516550b90010344003a4401c0c060f095580c2480039a5100f02c4040f504181c0142c0303560103008051103102d820501d078000e441385e15070143c00c0c0181d841e10000b5000c0c0a40b40020002800d100e0404058030000c0b0740c009002d0354081e07900c02000754004041039441060344c60412703a0030721280360403800c010616500b50460300c00c800c2d001c90481c1d808000303400d00d03851017050000f00c1642d510410402ca0142580d440c80d200c0d04200300480f041007000e50041c194200d88103241056900e00106207075070b00903072244070740e294082401010000207000c0e000c20407400b00c40107c001d080c107848854071410681125a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 720773453 1250 720772203 720772211
    0x5120d2601060818030d0902130630060c051c0519110d2c0a083103051501080a110906011106041101020c010f02060103030f0c02030307030e04051810 66
    0x1910a03404d03031080c00076440c190590f900c03000c840b00c407040504050041203100b0a00b0080954000300c2900c10304044801e044803150007030100c0e441800c00c80d03500e80d03080e010720814455054080b80700c03800398088100442e560b0541c1d800e003240320159000035451024400a080c001401540d5410b5280d848091612400024005000d4222901c0f50701c641d148440c012400d107441210407000c804610702014030003560000044003040c481070748850301140014a5084c0a0010110300300041c2c0b052481d022081c1c0c2c0c01c0c0351781a030754000d000303120070350b540700b1a21035001c0800304a00301001d00509006040c43c00041c2221000c41c0d07200c0c0000a04250b0303050140130800002007003603204031260101400202c3c280d070744a0506003840d09101001c40d00080c00b5107e20840c0e07405c50351060044c40c01900c0c5d00d90141040344d00715601203c0100303c3d00e08000400494401040243e50148003d045103480b0b03880320071440c1c01c5441400165400100342c0141102c02e8044004036a20100c2c01c1ca540800c0d0200010b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 720774703 1250 720773453 720773461
    0x6080403050f0f25060f060503150903220f0609081b1f0c060522110d121101050a0c0c030810031a01300209070905120d26010608 57
    0x1d0780c1406407451110f21840703603a086000308048544d0213000540201d41c00e2110050034114075094400303d109080e0035500101054001254400700c0c02c4d08280454162460000400300382d003800100085c503d40070300d40c400d01c20002409a50300c100020865800c10700003c82c50100c0c82074860444461f40c1e0040b00454400140a80d1091010840c0702d911803aa0401ca04c0041c00c01802400e03020000c8074031524080200b07002049940a0311041560780480780c00400040c0d503060316050742c00c94815080088001e5103400100b0b40d400c9041e00c0070f02d954406222641e40202c1c01c0c2940c10144c03240451a01d8100289515640005940e502503054100002140c40c0e140c64800c0c901c940d540040c1c1400e00e03100b5203501c080c0480c14140d04035030150901c05000c0c44c5c4680904030103030070090701500c0107103071b0310b400303401030816421036503028416003441ca01c1e4907074a80109260a174850074090080e04003001d00e495190f0080700140710382c807803036800c00340650740701032400c0c0d600f013041c003444040c409d40700300007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 720775953 1250 720774703 720774727
    0xb130801020c030417011a0f0a03061e11040b1b0f010908030a1d06060d050c0a060507021002060c0412140f010615080105090c0f04031205070b07080402030a110315090c0a06080403050f 81
    0x80011540300300d00f001400c1c209080400601840c332442d1000c1e0f4140030a41720f1030003e140958043e540003040707807880d000d44058a400342078520403071200a03020303c41818074460820701c10307902c040d40110f68041c1d49140840701a021910003590484100e8031f850010b02e83c135440007401d030380c3c8004150381d070000c40702d22418100d04d07020b084489280d21400c07107100800c01c25400006400014400e44034905002e20507101070380c4500c4101c03205100d185081c017003000400000e010400c4028020000201c01c881c160864a041484070070141c00569100d14040240341c0e1011528a4001080e01d002102c5506020015110b9a40039060030080100410b10f0405a000181101c005540c0040081500044601c01404070303000410161004120400040d480902920040e841aa80207011304000c50741940c1760540c00048118198040c03203001400d5036620900780e080c5d80110743e120020108003c00b10100805400306401c40400c002000003403000094000e03044e905200155020703d0f840756030908038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 720777203 1250 720775953 720775969
    0xb0a020c10120e0a0b0c16060c1b1a060d020112020d1b020106091b02251e0e0601020102070b151504032a050a0b130801020c030417011a0f 61
    0x81078800c1840d10f4201d4400340400504a0010b6105000300d84490341d400d518902240140c01080c1d601c0c4021005c80320010b44030b50f210480b004d03c1402d080d014405182c10440c0c4500c22418101c4182c00408007071020701c4046000300d9807011044401d1030a060a03170340000c011490f09100ca204858007c240c6d032454070503a40242c0044980d00c04503020352076400034020301800461255415031440c11900b45d08140c05009900b040c2c2205400410f00e1400e00c1c04040900712080b9030780240801c603000d0200d200f00f0018070300305c3c4400b004020340359880d003481040c821554020b0a036905581c410002d001c00a100ea2120541c0102c0c14039194680b480d9000105002d55140d0314a0395400354001070220401a00804000c0ca050811940f2001d407132200d0241c0281007918014254060305101c1c08000f0100b41c00b00034014044080300c90700015960360103032070982c0c101c01081e84603500085411300028003044c81c5140c2504540000b0b00401c83c0c01e001c0200710044900030340d8003030404405841c801c1d0b160016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 720778453 1250 720777203 720777227
    0x5030c010507060e010e0a110103090f150b300d2c03060709081e100b060705010204120510060b0a141210080c0d0c05010309020a090c180b0a020c10 65
    0x2000340050400311107126147c035810358048900341c1004038281e009511a120f8100b0050f403002082c406c8044c03503101c41051701880c103003404801d5151052941e0a4942e01d01c082d4039400441c465a6501ca8942200c603050341f941d11443c005548680c40ac8912035138400c00700304001c190255081e25421411210038003c200d410126500361203840b00b4401e075a6400241a07040710320030b45c2078034101080011450f446031003190302031400d644440c60f0580703401103d41c01940b10f0036008228a24012403a80c038036003aa00709910084403550100c4201d03090003400c0c0a2200040c0210300c00700000c1c0e04102d88141d0602403181004100020312060807407004030001103039428541031104120510b0440955082141c0e203005200d8a030045020400309810451111840d056101518100040c00c12004400a111808003aa84800c0034a400591840a48122642d800c1d055490082e1842000360810031161154008800501d040180314005a170110b4245040c8404840b854541114642d0454012207150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 720779703 1250 720778453 720778481
    0x172503020103020a12060b0315010f171008060a090b010b030c070f11090a0b01090b090a140d02061b0606011403060d060e121e1306050f0f030c0307110705030c01050706 74
    0x45001f007049040d440c091b521511481e0600402504400b00444401d1003c0d10303010041414520341190a990401046070f021020521041c0241e0b503440801d880d14105450408045903035400010034850130491083c050010051001c1c03441c105101d80c42400e03c501500031302070141c04071455041000180f0104103c11005240d1000da00b061441c0c04001d020401038070340443e044030800200f0803d00700503210000001003000d040c5900d8040001d64609204510f107910401d0701c0702100042c1e0792500a03250740348007144000d0204088041103498000090b00d114180540c40200030780781d104400449070b0100301542c681d648511380340b4024010300100f9240d0503550107113034054500160544040c0030741c410304000003400d540465009103a148510340c012020364401032400d0000300c0c060f0008007030801c940c42e1401d1600580c0340e1545030942091703406440a0030008203000f0401c0e803241285060400c0c00000c0c0080e60f21b040c1c002075441e05215102030503c54089643c02c20b022855000003d00040e01c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 720780953 1250 720779703 720779711
    0x5070e01030812090606060f0304060b030d0518010503040c03030e0411160506100e07050c0307121106090607020615191202011106040c061209020a172503020103020a12 74
    0xa442d11010395080703001821042110000002c94500c000121280200e001509591800746400080080c6600080080c2c864076100c0001c010706860802134900303080403030341d50180c4848094040c1ca2280d0200b0b8041ca040290074000d0202181c0c050796a98200c9030302d030401e000e84158020200700500003102030b48116440104a9142d51000d281512410512545c10746032203a0300e00710854100c290900908140200850019500310f019400608402080c0c0080342e04051041e0ba0b005c10000300c0c81456400a080500c45800c4150304208441d00100241d014040c903203000d54000399100e600030104908a0009500c91845488080d601d480a603140c2001015580e151070000c065110359100032030000c1c680403060000e100340803641a00031a40701c82e45598052a1010480360328480e030103605829595010b49070010380d01c1f0080b40c3c000703204003a0b408003444040259203040c2a4604038080c800c00c1b40c3c085903016201c00e540b0f050700752942400c0068a0b2104c4001c1241c3c005000d1096135206450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 720782203 1250 720780953 720780959
    0x91c0c08031b0a050d0c032a140118020f0a03060e150702030408070501180e0708011a130302060307050f2b06122303070f05010b040c1b05070e01 64
    0x700c0200080030400750510603500c09880c05a03a90222000081d1080e0410751081c5400c5201c0da1003022081d0003031070000c1c03154031034180c6504c86084005401c100460281030000030804003001c402d180c00f4940c4002c000034081c0c4a901c3c075142101d0140244584508440c0302600e03540e0104440140d900003808100046104158654501c003842c1801c0c65840990b0015181c54400021241036507407410251090525200054550440200b56050040c10701c84002c40c0940d0f0942e180c6215080590b03507070095514052211030b520048200600c1402070402a1507015040e0b11f1900c1c0c1140c2c0d043d28055076170b40d161141180d00303006403075000e44048070004262200e14400d105001c0c11141480960b40c5101ca016180011070b00240303c0c1d804030700c4428030001d0104403080c0c01c3c05614010140440903040f0340403101e038115400b24504a4070240200d82c0f50041c40b200b4030070b6030511041641d04000e5889010405402e0310340c0041051910b02050070b05108009080c40440024903481c05600e0207561 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 720783453 1250 720782203 720782219
    0x120303020d1a060d0f060b0d021c0e07170a0506100e100e01151e0201061e05060304022803030804030215061c03050712030b0a0e010b091c0c 62
    0x1100c041c01c0d010260401a140707008030500103000b0641a401050a440c021138032100c6400b400c480c00c1c00009159841e000086e442a00d04010b244880f900c0b440181d8413140380c1c0b0180203500c59581c80341c0215203800c1820b0450040000c1d6003041d600f52040c603c0d0b002800340c415a01d825150200100580120b20034001c1300e18103104502c054134032045040700583d5810b92561611a590301c00c0f40c0d081d945d040010441c4149840d21400c0121003480c001e00e0900c0e80c4c0390b8045a002ca07012084006079564541001a26a038080000c0364040305803010002e01d160030000b0750640000b40c030207486022401d00d245600340307a043d46040c5050054881c402015603034100540040c004490540250040c00060107400381c084c4036807482054001e20054181d07040d101810300381084020110184001006190081103408550080c01829550007061507a0b000c004e00411410a50042d4000200c0700e0051001c01050803e0f500010f0741910801c440e030055009500010080c41d6004c0e01a6001c0000491303001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 720784703 1250 720783453 720783457
    0x2120706150e160516140f0106030809120c030d18080601060807030b0910060f12060801060807051e0603040c05060a0e2403060d05030909010b04030b0c0f090d0c12030302 75
    0x8540203c40c25007003141c01420388461242c4100a140d2003100b01c1c2900014800ca02406103030400305084030101d401c1d10303c4181c00c60f60150000c2e1200c034404078801001d444e0819114600d005964040c2c80500800c5c800b00c2c0c0e403030380080b40da0000d0041d000c9510010400070b42d42c160082603208100d8100356034401002d030460b00240c40480c000782c01c0038014090740c1001c0301064010000c044992044c180f40141c2160b080010050410810001224454001c0907900550380030380004800001c0b0030b450a1807023458005e05030b00c514025481015190f18103600300315a1034001c64141c4119590b5aa5031500c60030341030507602305503400f803c04180d2414a580c450700c43c81544206440312301c0c6400762034101c013890609140380b240f103081c1c0030000242d0030304220090981007442101202d041441d4900000d4800400341c00881f90312501190030818890300034050340c1c102612410315031400c070074030441561910801401902900b02c1c0745010007001a01e08013040241180c01c03100b0b000440e140f0b4020065 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 720785953 1250 720784703 720784711
    0xd0804030c0626190903171602120a020a1e0c05060418090c1d0912120402010e0f03030307180918020d05191a1602120706150e 56
    0x4100040c0020809502070501008075801c0fa005110302c20100300001d456100d4010302181d0a8051244800d2801c4030f51300480c84254442e4494480c1410b48034101c59000600410103102039510343e80a040103900441e030a080e00084003241656900080010380c034180781079000078192004880703040302c403000748403c201c0c94034030a560810318a41d407002081000c0c0502c0c018000580c0c01a000c03440d0803115a400182080e10a400e00c0190554031071007800c450b10604403540c004501d1904100c07030307440d00b8001c03c610000501203060a00f22015030700d024500c0001d01c002e05108011080c04890340e0f40700750b1402c100400504a90356460101001040301641c50072444d02c561652001080e410078600034500807960040203603003002c0c0e41d80c0802008a46c1402d040d240d600840ca0b002c041d148202a5600000c2d00981c101d04282c280403414102c4110010030720207001e20000c520f00e003c268007084012040e444201300a450302020705019000300304040740340e00d07500314404000502c0f80d4503402c20782c40303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 720787203 1250 720785953 720785963
    0x216090b0120120d06090203040f0308070c0b0f1806010609050a0807080a021507050f032127160807060206090a030e0d031403041b0609030b04200d080403 68
    0x4105100c0c5582c0640760b002050010140e0818049090000b15034405800500d496107400f10782076076105030764001c0340e00c107882c20340701c0c405101c0100f0705054000d00c445400c000b0390700d401648400c4079107038a10005405000450081602c00101c0c000001d00000c084c41c00004000740c0d031465a484002a19a00341842403600031460304100094280c40842d0f82401c88480d0000780107000c1007607007000510035200c81d55840e05503080c081d01c000f02d00f0030003d585905020000456842003a1101580d041c20540888003c0c00c031042d08000d00880c4404140c4039414a11200c070402008090b801420400850110102001000070028007001c000070040102c841c1d83c1c0a4071407603224600c82c0c54841915800280100b00c1421002c2c03480e040c140032110384507000f4508020348911410201c0811b51099409450052240c0352010031140405466001040241408030a0302e00d56070b14450084e2000f031021f844c0d541d40582200c2640b01c0194100f200c60001031100380c0246441ca8103900b10b03000b5000a42d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 720788453 1250 720787203 720787217
    0x4031e030c0f141204030915020d08010509040201120f0e0a0312051602031903020d0f0f06211e171206150906090d0606080d08060306071b030216090b01 67
    0x82d40b240602c100c03001d12040800d1051410010148001080a004e0b00481c1080104080001c8000c0310a044110a0041d80e01800d043c2840c800700030080c3e001a044184a00039140a000050b03821410f14140f1501944d00401e02000d1801a84010500c2003214a030700e020b06841c4408150b403010b441c41c160000500c080109840300c480b843d081c03012400442c0b0140e44100012100904011a0150042c41c0c1d40750140c0b0b002c40310450f40054800d6a0009d807002c58840e0742c110001c0301e081c0201400b42207036040039480345514800300b02c04464070300c0c0c0140810540c4003403107603200321030300c110b2481640150400b000b015115407603003030300d40c4130f40f51801800c2240004980a8035025450341034080c85211032900300304988080050f03943c010f00d4627035071241d00056950001a09801070000a045034000340c82c044410003030203002140001c00c203a1294005a081003c0310307400c1781e020440c82c1e00c6080c0d82024900e031440d080e072030f02c0410243d0145038a01c034040040d12103030941003000510800c0c1d035901 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 720789703 1250 720788453 720788477
    0x30309010b0103140709120606030c0b04060e100e040207290420012c093c1503210d0b1008040b06010c08130509010f0e01060804031e030c 61
    0x29034200ba0607240c200c000f40d6102c404200c48807d44070350070130041c041c8000040350ba40c0c80c1c0e01c00e03804041a030301c078409603d40440c04202651b0000c10303101800344e05840c80e21303514201c0c0d540100500c0702080c070030b44250742c04905881800914846c10b05e03210900c10000c13496100314000404e1680d0b04540880c1d0291441c070081d500e120707881c52500322008042e159843d074001140310000011492001c40805840250031601e219600d408a02d03008811011031454440401d80b0b000c890403c050b12210b1580154011a01075015040219580b004462159400384042040061305006c0c01e0100c1405050201c00040d0a10031401c00808442001c16010820300354028180420b00388a020f8040228411100180114a05040b003d0703110105241402882c0d01e80e0f514006240c200c036240011403042c0e010f05001c00e040030301115014240403d0b0fa04402440c0151058185105006002c00c000c200d40120b420140241c0e2500d21040344100498000704d81005d0050061600340e0000e400100610086 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 720790953 1250 720789703 720789731
    0xe1e19030c170606040b010e1e040515030606040f02160c08061323160605120601020a020d08070501090b0a0e0c040203070215040f06050c1c0612030807030e030309010b0103 76
    0x62510b4100c41025004a6450304200001001c100e940241030102c251040c01c80e81e41c030b40028078010a54082c0b200c1d0341d000d1110600003102d4004012000600d040c003000e0001d540c0010704d03668001021200440c40b181091015001780c050030101854001030003410000b04618500e070721003594521012243c00d5600c5024041e00300b44040d001802344001a0740510f0840303200c000d004e422803e07a0080345c0c442c8664060200e03400c502c55000d980000c0700400ca5507442d0040706656500b007802440103040014240e000280303806104000102400c000140c0381040007400c0d0451003600750008213401040c0303030003054100503000a8841c51554014100070b0080352401e442620b0003110b880e40127201600720294440c0d40c81d040039009540310400003484c0000100c5c00e0080a00c00c040e0a9402c0c1d2700c40c3c5001003411001c0c40200301480516007081c0e003d1210300b445031000c068042e0113113441451a00d440d40180e0042960b40407808680c00b001040110700c60b415006112000d0013a641004050220102 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 720792203 1250 720790953 720790979
    0xd06110706141303050c0c0a120606090507020706050310050307090e011b1d030106030609080405090106050408030a030c031805010506180402091501050c0a030305071205070e1e19030c 81
    0x483c0c4010225100c600110b4410303400b40c86520105000c65541f001c1001c00030303004c65000e502510812008045d40400c011a501541006103842242801282401c00010351211f03c1360050908001d00400000c0610400d000c1d00c800800c409004e8031005a254119400036040c0c10036005040d6007003029600c8050119507603800d0054076541c0301d40faa8221400004003c11000d00d4865266403074240102c082400da01c515540c00c1e124682351a41d6514100a20855410580c40350091050510082201181c00300032501018220b250000d000300e96078800780c0081c08120391040d00040719a103100c1c00c2041c154403a5008d04d100f201d108203107480b582c0103010780c80d1040360000c1d08000581d0102e8840307819014600001501418554100308054400340e2501103c050150700090301e41080c0311110340c01690a03e110041500144440d14100c40082c2c80001002e41c8d643c000c40440203030f80782d03421076980403240010004001c07002d510300100c6640c10300b08803400180c4102c0080d080020701c160303007030750 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 720793453 1250 720792203 720792211
    0x5040f061d01051e12160206010b0d0c030e1e0c0a03020612070309170a0906030c05160215040b09100c02090a1802090f250207140d0611070614 63
    0x407040d451420aa001103409030071510a100c81c10005003180c480004420025064104e1031240610440c544941000d0240407150384400554010000602c00d40022804035140b440d0304c0c0002060501d441d4904a008054144080400b40101c48000c41c181c40c5020f00710f20340790601e02c105e03280c40b00d20303200b0003910700708520000b948447d081281134140c01d000380c0c0307503940300709507060004480e42c00741c499210b40e04103411401d119000009000c04195042800580604924501005241600900544a407040c1c8444188800b03d0265040443d0b595901c8100c3c00c008000285880d9a44c4884548080c1c12500442c0d124000003811485900d1103610130a50b1a40c00520340300064481c58841d000416640054181d00d012000c0d8010140e181c05403c030f0301500e8160383c12903031031900303040f11583d070417400c03940a0500d6112180c0500c40d5031b000560360207440c1560b07044500c81d2041390000b0751382450a20000c0031103091100501d21004a5806041201d01a41003884221080d00918a0f140000ca03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 720794703 1250 720793453 720793487
    0x40b010e010f06111c020a0b01090207080409021c0f0905150705030403121b050903010513170a12061e09150e150a1415030c0306060a0c1205040f06 65
    0x1e001004902c2c131860440e58501903074070030780703c103034050000501c013118210600202683c07082d80d040f401c00201005042c010106518211305082451b0342e131a51500c00d07807040c1000c940c1c0116050307002c0b40130a109400140ca40b29010041c204c800308030f0302c003e040c040c1015260f44c019012010301d80400c040f2101e01c151100d645103495980c03160750070b941c03c60117101c1c2940450350b24400b5500c240001249070500708001d49800d0740301d610b44e408241c2591801001c840a15040c96007103400034081607612000c0d401c20750b0401d6100c40f8442001c41d054a11050b005001c41d0074000001800250840d00aa2045280e4151908191226560415200703420402c18110804e0707501004408001011117030030a0741702d034240800c0d002d075100080c031240c01604000c1c84c00b4407008030014907140c540710034010403038103031010760640c40c01a825842901004000d50300900c800640400b03021f2040003a011071b690311400c00a0859801200140280c001e4090003415003e045408582540210f0180d90794102c02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 720795953 1250 720794703 720794729
    0xe0c0102150f0414030304030917011b0302090f040f0e01060602030c150c0909090d0806040c120f02090901030602040e0f06100c020310020a020f0c0108101419030308040b010e01 78
    0x4500365842d40400800642c0d152400402c140d0741c4950500c000d5018602071b5071143c00340d03820240c035a0f8408c407804100480580c5000102f000d142c0c504105030741280c01605006868204072004170717030310700203040001c0d2b400303440d100030708515100f030790301c41e007503609800008101c2142c880200340c1c0c2e64801c110340100d0039400069403c101807502c1342d000354081100b030a194103100913a03011401001e01a24000065002603c1c1500c10503440030b9200e0f070080003100e041c05240100c4a01610803d0003d04000c10340d51609c12640500000360121004080701601c40d500d40d680d0790400400035049809160240b024400100348c2c50340c0345552140c05007000408400c05a405510305460f440e44400040741c041c055007084085280662020f01290852600a0407984d1030450110f401c05004107030b0103060005200502c8040010781008005480c61f808202c800d070b00c20304002690284a464007901d603491b98407004020190b2110b12240154030428250310603980711008144091824081c0058104c02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 720797203 1250 720795953 720795961
    0x18060f050d020d0921030c09151211040b0a09060c08090603060409050723040207030806090901380a0305030f090609040e0304030218010b030c0a030e010c030e0c010215 74
    0x240d00400351070740303d440c00040065159403214100821407000c03450035050100c45421840d0103002c0c2e05203415881c50b05402c021f085c00642c6000c0c8480c02208010021103c800e00341038140340c1c1c032980302c1400050007a612680d075031070542120b50210650900049075241c0c001041401495a100c01ca9442110380313041c07012032800d00c041350b04001c2c00729a00580381c600410220300300b4003525010b006a10080116002070408009000d0908454980110310411008000c660b0100140d030300010b048070621220740781e115403070340905694424800700304030301c03e450942d540c42400300801d914104111003003210100300401c84214010700c0082c029030000c10414219241c000c000700312800f0010869800c0252050109080301d024075170320714450780002130501c154540741d030b00d1200494440d160b0703814545c10410304a00d6404040e0115800003008180c04a0b02806a040b140e14a19510001c002c010541c4600502820f161083c9004034042c0c586100c03172030b500c0810200304c254a0119442d4507515 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 720798453 1250 720797203 720797227
    0x5010522050d1209060f0f0e0c1e01120c0e0a060314010506030c1b25120b06040204030b0708010315020403030206040803061c030809370c0503070618060f05 69
    0x10445100a1603139440c40300006140c1d4407035140b1880c03a200001448182000300002143e60485c044403444d0712496103404107550310045400080b451812020582c0f40c1c030001a51481010a880041c1c03c0c1030064074036001c0d9000503a06402c84c0c1c1141d04004466640300180c0407140c00c600c542540594080040c03000741450002982c000c250031864501e4060600380004401d62205614071254021010340e810f0b080c1007050f41d284c040124007641243d640b4001414140c40100c1c1380061450503181c00103043d6a80d1541950000d40c0c201c044030380300349030480300101a441e0074001105d061a004808203c902000c8c800d442c10ba981c960010308007030b2155240d401113600010241507201044480c2d0030407161400841c424451320035100c0b00b002c5c3c2818020b030760a008140c2c0340d03102c03803444101252030501e00380003107502c0f0030071200c1c003900395000507060440380c441183d00320319010701c5040c00006240c1d611074401d0400c0c04450840c4200c0075202c80d0b04035420791307928a1540016a06000680c0004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 720799703 1250 720798453 720798467
    0xc0608040209042a080a05070603060b16030512041109070810050402030603030c0d020307200603150a05030610090e010c05070213020903190b090a0201050f0d0b0d05010522050d 78
    0x49044d05140c4050340c0841c1031419100600c5d00110301c16003000140c013080110400071500545001c0c2824020b80d400d0100c1c0043d580230303370852107a03502c002224103c107041c050000c82d18404020068052a40f40034280104403000010a1a00540d420000502d402c1e100303044080c0200e120718601e443d40c515000401000c1c1d040a424154507001c10020000300721410460f20900c1407075500613688801d10360500f85508207000ca110001884000c01c3d2004541d074010071039a100903144039aa0003450544082a9140d00641116415100d407031300b441015590000c61000311000182d00b441490203809903107003a80c04203401000482d009004000c010f1419100342100d80d100c007100181045500c000207460702140c170441c200420900c081c410140100581e0b41a8441160002040d6400040d40028114407441c60410100030340455002166401d5800c10b005181000b0403000100b4010704000e8000d0105941c4000c20f1003142d8041100011015515a10300e5000400303000092040d40c003e555030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 720800953 1250 720799703 720799733
    0x1060c0507090204031406071704020d1e08041a04050a0509070c08280302090109030818060309010b030f0a05030a03090305160c030314091309032303040c060804020904 74
    0x3600906802280c075410500c0a040210700582c40c218802d20000c80a50803c280075045008005a8600803214202d01000c816001641030300c00241d41d0849040807a00e80e0005100d02c0080c4201c02611f00501071780602a00580d01c0b88021045942c10300c0c40c85007100e10030342c410309410000702c0d2000c0046142207804594000b0480c20700104850305ea580380101030f030000003201120445000210440758945408160b4080c0e581070451512140200280844a252000030651170000500000c0c1da020f00301251902d07417011300b101d40c40c1c1c10301c03074451070103452000c450f00d02a20420707900341400c0c4070014594803003a800c00050742c03400741c1c0300c42e0890142c5201c08090b01485410450028a20301c0403440c3c40885020f0041072400b00d0451a0081c00394102d00701c010320541060100c40070640d649036030351409140410000954a582d8a010344e5a010701c070b602d61908107050300706440c049078101c00071803060307114070307680100d09807598070030754007000140c0e001313504071404000145c0040d4410340d56940c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 720802203 1250 720800953 720800963
    0x5010c260f0a0f020706080f061e1002010b0f030105070f03020d18030c0308250c020a120c08060c040b0d0209150f13080c012106230f0906030601060c 66
    0x141454015000742981d02403404000011807003150104000d034144002d60107820a881c12941508100800201c910f40190400b8818110310308110030300420b01034100c6907582d0250084c0e40e02584000003074002c00019031490b00869081c1c211410a01e41031064501c0354165481d04110700300c200c00114020b400400c40440c505584880341e4148004408110f02d00d203100c1e94030814482c03554600101101009000c0c00c480b000c1e0000c244807034170500c100c513904030341c12860005030365205400000c94110155014031442001854031500b840f8a00149400341c80142c400ca401d44e40310014034403402e100318491204032000503c00700040d10f245400405207100018854183c1300400c00c0090419400500301040c4180d000901d042010a80002c1d40014158500640b0240132141c001800b00b00d410000030030003503816920f19a64201c05d07805500507200404510344403064150001400081c410440ea1203030508408d4500107140c891b03480d070b22840014000d09056403a100c01601c41c418807603001c5071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 720803453 1250 720802203 720802207
    0x19060b0d050c2b06050a030807120c0c06050c011d060915010e0109050405150a0c1106060927011109010311091f0201060513150e040b2205100b030705010c26 69
    0x3a282d51103203441d6007d50b004059a9907501554641250030015000b81201402207401486000c140501400c0781110014106a40d039041c2900b070207030042c61040400c4840309104800140035100005245100d00c00b5801100d044000c0310309000b0b452002485142040d604881c014052003159030030060b0070078401c5048812044400000070305c13502080b038450900503545d181c181031181c0c6c0f01c641301143c100600c2c0604154108000400d0110200501d2085619580085003001c480d421042c0502e17004220000c05c0074450321140050141d001e10303c0a40001d081c01e65600400000d081250412900102807216800c4a400d80c000d0242c441c0340c00c04195540c07a4030020705e0751102d0110b00d0b92034507040340c00a55508922a2040c890071070b500060080301d90401000009894080c5080d013014005810f113400d41c0741012440030494043c54010214040c0e000c00a2a24025800c0451440b41c12019510110345440044800080c0d5280182110100d0750300f0721004803126006045100710000564 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 720804703 1250 720803453 720803459
    0x103170c120f1c050f16140a0905030a08040504050705031911040f140a090606080c0d061205030307030507020c010509040b060d050103080d0c020a030503060919060b0d050c2b06 78
    0x4001c0740f40700c8080d505580e844001700582d00e152a459254400d843c0c12500100b400a104001c082c840300c40707607aa0043d4000903114003024011a00640104802421240b5900d0f030303440c0c1244940c00910a0324021802d00300031492660048042d61b100740c00c000c0020f0210304404000f83c0c0981500907010741100400c00c8003207214240310144401a00008008810441c0700000f80040d801807a40051009498000d05001e59544aa40c29070000d21485101e600c0ea01d25040800041c400b03944203030f849200301e00d50142040390102c0558411003036910b040116603580c001c00d0383ca407000042c1c4c1c240051020080614540b03000d9000e800e050001500c1e09040000f28030314401192400e0f0019144800003050f481c100344040d0192202820480c4090a00100d9554028181c0e0202501d040e00c5641c1c3c00c80000c074012503403a0480522595540203125240d80d802d0061155440140721003411801c0000041900806200b11100090290065070504100c501002c0807036059003a60308500e80c81e02800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 720805953 1250 720804703 720804727
    0x11406012102040f0f0803040b0f0c0f0a1109060306070905040e0c1903050f03041d0403110a0309092301060305180f011a041a010509060706090b0103170c120f 70
    0x2403c054001d07a0300050f03540382801c142c484509401c0d84140c0441c2e00400003809007414810a1310840307141c02c1c850031348400d030316071015007132807080e0342d455070107120700d03030403007090040d01d5206600714a0140c0b190806a00c5142c01d140e00c41004440e05808666200000c000f01d0500d548503078080c2d41202e007a6015000d8587c0040c100c0e41c1c030420000f1a00b1803075403090050040510400c442504c0e02c1380250700c1c2600e0034036902816190f1144100e10310f001000000c044c50f0003000042804268074007510b008414603d409840501680120444149041c608030300000c80300c0105060340c04070301c501b610380d41c0c46d140048000d410010515484001c0111040030b80e18000c214440100d0b00500010641c04089041641c1414405103514803403030a05144080c0808400b0000c0f124031000c0c40d000350f0350410f080114209110b18071008040c1464401c626090090650746141628411200e2400c401c0c040c24145d2841c1c0682080b151883d0004101c040c103d84a0711300a028004181c154241400e141d8264 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 720807203 1250 720805953 720805957
    0x2070501090804060212041203211514030102040608180a020a0b040317091804030201110c060406050a0504200a0e0a1a0319080f040f180c02011406012102 68
    0x440700e42d1404242808003640501000b200040a10000740c1840c0c42e01c65808884100640c000d420b110780300c0782040c0c090040e46500d8819a4000509101070001d20401d010a4005886400c0742032001d040c3c140c000d89018003c490895415980b26101e036202c074000c480501e02d01004060142c8a0144100c00580f41d100c0c000d001040c40005a07502c451031400c01d035141144070704031108030400800160000740c0ea00e83c0b034900303c0d1000c054203803841e1751a454240c2c010280c2c0560503070030200104a141c0241d50028420344917030311420041c007282c0c031021400d50642c2d00989004201c0c020000c0420003e13a600c05d00540c0504005003100045965004a83c20883d02a100400b000d500d403030286600380102e203c04000450b06038000e001070a07a0100c1009020350f41c40004001d100300007480d011800450041da40076049000800901a0340c0b50f1241150390021246942d034582047d41d8641094010712803c032f01c0c1154011601c0151340c1b1000110b407074109840c0c0c50001d04104030520451200303d440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 720808453 1250 720807203 720807221
    0x23d050a060509042102070f031211031303030909090c170124141002030f0a09051203091908190609150b0f2403061206040b060f061e0d02070501 64
    0x412041204802420455501789001c00a015580090f00400c420100008102c0450780c1105401c6481420050103c501074180704610740c0c1d91201040b6000e04416428550084910a44990500994681100c0240c800f081c0303001c0c00d40464418100001100c04442c40012100130b03000060b21504045000500d41d64201c1007a014009081e041c08014000c4800b401c0c0100c044410513000c2c048088025030380d2140789115141020702040601e290741c05880c6500203007100070089012485150251035a942280044a12605540949030620381c80704903550240c1c3c0d9254013401140802c0038a24140312400501282e90799625100400801c0100000c3d0080c041c611001042c8006420304002d040880c148150744076000d50050600c044a01f40b404040b060046042c4540f40ea582c031001032000c0c03115046101c281c0c02090300700400c0000056080788503010490302e51540d40041414000d441c0101000c044828141d4103411392480c002c84080d01c0c0e00c0090440140c83e20b80c45590301c50075589005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 720809703 1250 720808453 720808463
    0x3180d120c021516030e0f060f070b1003030c12091d0105100e0307030b0714120901050109090f06110d02040e06211c09090606023d050a06050904 64
    0x4602000c40c40d000e880a00721048012550303013480001500c2c485420b80d81c41c002010305c4400540110130b510ba414184080c080005c0600d0b4460030f544040c620b150f8030144044800c5c841c95000501c01e9180d54201d60140c80d015a00c45a40f1182582c0701d01c1030307030041031002d01844402080082d25259140010650102c1030704091031652520050026440d1410790301410302c80b42e0303082400349807000100002180d800541c0d0b014030307444590094469031101e55801880510002c0d28015441c1940581c0f409090751000800c09070ba0b8500000003221500d1030000c08414034a804076011030310b00d8212108021605203618070f414182c20302c440c04c0740d2090384440d44000004082082e030307240070004507007008800c03002d0410000000041c4c9460b91620308829102c1d100c03090390341401c14070450641c0c000c4c0000241c1000032540303030721001e9030342c018082c60035600f44e40724481c144600c05203098169500c1046025810b03018003481c0410081c0ca401442d52802581c0c881000030503036200c1880c3c82c000d40c010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 720810953 1250 720809703 720809717
    0xb010b030a02091f0e010207060e1e090c030f0903070b07050a2007030b130b06060c010209030102030708090606040e0d0c050c1801031506270e0601031b0e010803180d12 74
    0x541001740400100a01d49419901701c030b0400c010440c0c0200ba03a0040d01000c903440d44c02d030501031283e41c5030420a800010b410400c134004100840100500460041046285100c4107039501c068050f40c2e449460340041c6107800da080800c3d40640100090200306010341084516110b6100c040e561550700702070320881b140e0100f4010800d005000140d80d4104030540a586a0102c980d00c900601e140701030291405094001584014050203505681680780014000d541d04e081040c1d0080c420001654a0320350b0f03004041c0807400300d141c10300c40e0301c04c3e040e02c1001912182580840903070341d9125001042d5900d0141a05151490742c80d050304515078a14000780c8500e550640c200359501d072181d050b049040614007102400200100c0071b03030308032010b81c04c5000050303000110340743e5000d01200c0401036081c0c4900320010040003442e07200340d00100d07284509240e84960303c1f0b4404180040a1213105000e070810410b05021001c5511824840900034052084500155481400e4140c00d07104840c005021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 720812203 1250 720810953 720811009
    0x10180902010c0b0f0114040204080c01050c03130f030204050c131a0c06042a08030717071e05010b0d170703020703050706030506010f080402010f1805030d0314070801030b010b030a0209 81
    0x8107501b00c4811134160740460401d820060650b9039418a40d4409061150110f1030714648201082141c14510350440b441402966032000303d0300100035800200d118a04140000b01c41c180c8a80960b480190710201c3c032502585001040003901640501020072a4420000646c0c0007804000c0107002d10321841440082201440303023010709090210b066144a0300c0c440080144050010030b5421054005030070144803000552500348034819034200a00308090b5100510058040810790071080740910024440f80d4504810007181c08c45841005029041042c000c8002c9014070f009031054512900480e05a00c2d01d0380c40d05490420300350311200000b501d40c41001402d5030311540d200200850340c10b2441c414281030b80080c16a40b00c600102c802c0101184c090740304861a8800e5500802004e02611286820120001c0c040d20014810f90b02140410300820078582c403828506048030380140541c419a401c0500c01e0f00c0591014003220b460b035400380300d45040d5941d405000003d071503040007080d4688403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 720813453 1250 720812203 720812219
    0x60d1121031803070f030308061c03022109030304030305032e080c011e080709170a0c050603011a0f0702031507021623010516060e0610180902010c0b0f01 68
    0x20300e204500e030003130704004000c01c1005080103048050b260704d404c02e01e0807a502e10703001c640d80507401041500c034800d460450009140c0c01084000101182c00c5280b41c91015502c05250284240618180c05901c20070040001c0381c82103000d10b81018011044078042800d078050b904800c4a000084810080c0c000030170800018200325650702042c080c00c2050300416200040310904544000c0c81043c03000880c00140420b20500d80791020b480b884407003110514102c600710356212300304030b8210785c1c140c48000080346500c1e2400a07641200d0402d14408455107400744c41d460305811071441103d40c403400303100143c010790b800d1080d15558003152070101322915240300300078603001d540251a50350420000081c46164090701d00400040c151107010004040c0309170040f50548102c0d088801c984503c0700d0b03850f0802225410040c03417400e1050031960b03a034950222603010b900d40c9108d050800c1c036040703500a07000310180d0030201025005040c56010000291034441d080d131821500844882c6e044801401120 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 720814703 1250 720813453 720813487
    0xc021b24030c1b15061c0c03050102180111030405190f141c051b011403090a020f0315060f0a17060907080f030702042705010603031205060d112103 65
    0x7196210091240c80d841041c040034500005d8166130241c5280644824017848010303060020039840304028008580d01e0070b1490003900200d5400c0c0002c4284400c40e0700355880703054101c2c42400d49401451400e4517003020030070b80018200c01c14070035050303001d80080c0c2c06020141020040c0103030501048250600f404000c803448a00e40c031500074000c44611200420000500a114031103100382e11041c1403400b90050740d01c140762415100d283c0c040001040b4846401090b0b040c0c0142c420344040406d04414020075468003200310201c822042e00000052081c07820485048031090064443c0180c180c0390607030815602280899150554410014032000000c2080030500820240024040c040034000d1860340301d104200000c0d104a44030714002142c000b842442c690100c81050440d0f2180129180c110301070001440140c01180e100b4900360040c00c1c1502515125107001071206401400d0350b0b0341e00d400427000c46040e03500580c41e40781c0c4503560001001c07103001c501d524000860b10f4103200380115a0070703 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 720815953 1250 720814703 720814747
    0x1e050906010e040803040b0c0d060609030215040b03070e1504030b1014011211042d0806010b030c0c0c0301060f080709060501140304060e10020406030c021b24030c 72
    0x2000e44810000071850b0b500c11740c0c3c2c01c16444402001c20792039015007104203008800548041c146800c9001500e036810002950407244250303540d00e060000004803405502036842075280b003080810000d0841e074800c01d142510030350000d010080014a40444040b60707081500102e442044000c14040000110401100145488031003d8060340e050f800081c6010b809240752107000703458511111442c0b07100f0050306c0c041d0582103400624801484924502c0810f0440000141783c604103020804e00c1011441c64161070101c403040d4990785550100700d40c1640880054299400340d2541d1224565080c01004001d001c0091190301d8a07080440841c05c004440c1e10130072100d8a841c03410000b998112446024240301e6080d0f050f1241e44604005000e0400140e010340700e8061030102c042c44c140c0c1c0364017a04c03d85669a2301000200e01266081c0c0e960340384100480c92000b102d010786181c83c6803251000b440c1c081c903003203034003500d5541c1101800e041c0c0040c0c607007a120f5240801c9064030398045200103045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 720817203 1250 720815953 720815969
    0x20d1e031215080c13140a02042d0b09121e0c180606070f060207120807110703140f060c0408010b1c060c110607020106061107060518041e05090601 65
    0x261503c0c043c0340c1e940c41c98000d51405404640e92070000c24005a100505403107150b100c817801842d204003058001c0d03019004483e410703081000301180602d81040d4500b00300054054021040c1e007840d83da09141d801400010f0b0780100104d42c3e40c080e10754140041041c008500c030a00c07030fa107032096000b030342045018100d141c024540d500019415002862072a9089081590b9091b0348440509090804214044000c3e24003800003601d070041080c102c01c0b40404480d01c0d51f54003096100e001c0b040b03c1000b0421801c0d074007684040300034030104402d601d180d901c0c0004031045400070f2088544460030070030b0444030080030080106007000607a03020b0007150701c180000c46203070500c11002d502c41e51607410340f0078000e06560368400100c032800707010b1055034803d068610200c424030700d000c04009001c1d00703840c050a400100c21440d00103020710001103050a40380c0588402d17060030f40d000140060107807290170710303640551100c1d6002c110002c56000c8900000002c1c10110311031603e40e00039032800c2010303400300b41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 720818453 1250 720817203 720817241
    0xa1e150803070507050915060c100f05330a0608090106090c02061b07060911041505060a080915190b0109030c05010c0c030b090d09050f0d020d1e0312 66
    0x20001d440130030000181d40003259001d1286c1c5418490040240c000440541c0201000030211112017000450081d45800e6081c03e12003200f686c0c800a040d102c05503001250240440c2191100119501500b408408940700c1c480404d541900040d94031000da501001c0450221428040c0c010401c0c01243c003d0302c103000052010450b603420003581c0d01d0000b002e48401c41c003070000048e40d00b0806011141d015810020510a510640c04c2035410365090011302445a481e001c0c4081c0e459101c4610b103021190f004000d03905000700043c0641d8031020051801c0035500480040c00d070342042802e910313409040151115500c00b041e0346452412641c40900150500480020800c00244e0010340d0354181d620a18107521181c40c02d14025181c1daa507034000514400544003088402c0f90002000d4080c2c685d5079541889075951442030100c240c0004c2e007201c0e000008062450301608056091250a920850801c1c819001030020307441400c0c500d00b400c0740014a0381240302d45591050040002c95015429401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 720819703 1250 720818453 720818467
    0xf0a020f0a02091f0801060b0301080c03010c05040b0f0412030c141504200904031d04111b07030b150f09060a0314010209280611150a1e150803 63
    0x1890f00400501000c6464007100e1040c4d40c1040c5549180000c00301c54000f400081d4031944074845030b030000d014a6156100e0592092514601400784402c903d40c00d4403240d140a060401039002684030344d00200c03c62030704000000d8410300520043c0c107001e001b656000a40d40540c501055042e60326003c150781c95011404c07003c481c04401d8405e5412540c089011a070701c02c3c4a80a100e13081c8903e40c0701c568407e84840400c82810b800a03290801100380e8000c000625204078104402c968203032450400940003400050003000066a07012600c40d40c007401c44401039074a07605c000444908485070b2a00300510340400e000b9080c840158031440008841003641480c00001240b10ba9245101c09080c0850003600100461420740c1180c09050003d0480d4100c40160507803858a0802d49654281d020411000012540c1c4540ca0700021170200388050461018005505030103240060000043c0b81c3d0b480e1209800500d8541e0704402614000c0000304406103290380b24001d01c1c803564028070b05500100b01003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 720820953 1250 720819703 720819709
    0x40308010e0402041b0206070f02030c030313060204031704080d0f021b010e271b0a0507020f040515150f16110a03030513060c03140d0e01020f0a020f0a02 68
    0x2034156550008500300c1a41d50340005006050250f044840c541d03011000381e440d0355808128a84114015119170303001802c40e030801ca030f40f44503e4021004075002400818050702410b441140721a000c0d00001d401c041e02d07a2941500017502c04186182c0802c001010000c1e40e0050110004030744080c24200c00c11031031044007a4a807468a65580c041c500c90070250200c2c1ea0041c100005a0000a40585405065940703800d4031607404440d81040040034900140c5080080f60700307a0020202250100d003040307200c210640d01c80d003007100226800000310300c8007070083e1243c2c03188500c6044406c88400c0d43c5940b42052191048a0313082c1154605410040556040321503000c640a41c0049000c03503108250900744484e454040c014450350150b00e9440020905900401410400e01d21071030325104103075500c40c283c44001c0e010a0003004282240450013980084401500308080320301d201062441c00114410300320b0b400702451000c041d501040790f42c2c0300d070760400450544160450090050041c0b035000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 720822203 1250 720820953 720820967
    0xe1f0b0d030804060f0914030a080f0c0702210604030c0209060d02061c06050d0b0405120406120c0e030718060e06060d020703050c01090609170a120c140d0c090b030403 74
    0x545031540320060300e05c0004856000b058007a40082044903507101665081ea1258001c0e00700b000098402004143c0b40100109018041c50403100350900c0e0071107035824007900104031445200781e500c0007100a444881c0502c030700d074440da201c2d55400b0441001c91042020050014107500d0107010313030384000300050b1281401c07030381ca41c42a8183d0b41180c3c000c45200b000030380341a4004641040d04240c2100810003e151501e00039841001030707941d040788008070307071009000b14451800010458181d02c3c412080c16445801c03103141520701a0341030350784600800d1030803407141c1c001e47e0148490f110882c0c1007100c504c03600b000b8141c5042c201e0114148100040c4c458021400c1003900150300155000801d40a0011100344500c070070300a00403d00301d814031100802104a007a50140c81d1680d0100110080380100e40300c5202c941c40e0fa100142540000310000d05424a002040c08005241442200400c0d40645100c0f61076140c0070401ca0b0207150f001700954050751080c0403240d424010300c0002500005c1d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 720823453 1250 720822203 720822211
    0x6080d2c01030e01020918040b06031c0804020f030d090303020712081210030c1206110901020303282406020f10020d060e040537030e040e1f0b0d0308 66
    0x42d0110f40b020103000c0c0701e030080c807503481010341c0414641f004405600711001201d00c198042c444d0700e041a501e441c00c1c1911008032040340100c1044204040031510b005441c001e0b0000d001414a0004402c40004207141c6140c0c3d18580c0003180000c20100708056040001c3e40142c400032000304500000f070703aa04000c6004201c41c100c1c584103800c0000702d00c850303d0340008005603000384404003616501d12030410a845e111506490790350038400b500860f000204102d5050000617801545960b40704100c0e10304001c0b0784184203a0126074000403000780140c0d0301900d070320721800c0c00c1a0b50b541c02c3c0f20380000756000d920758820403d54005411010400350040386070ba000802e075078005030362100350201101c0208015000450781801c0c802c107000501030000b0760b50640310340d03040c5114102f0b240c0c0104001a440d5050400020203038030140780c400a407107403020a119403000f40004c500952206481414045070345010002c1300d003400e02c00c0d20300406600407c0400c007025600c254208a04c7e481c02425000024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 720824703 1250 720823453 720823457
    0x406150c02060c10021b06010f03030c0609020301060503120406030e060603060106050c07090f0606201f48080f04030c05060705030601200c01030507021006080d2c01 73
    0x12032031545645051150034800181c0040855449510b01c80b8103a14100c2c48105144030b20500d40040340d001c0711002689d007520340640300d07620031940d1940d03100090001080101d03050354a440c40050951020000001c2c0491078103809071300ca600b040300040031100c2e150750341c0400742d02140034050303551400708245056503807a140c2650784000e8940160b25000c00d65000450680c42c1003103001c00010b01da8031502c00c0d1100d9039250800c10048000740912203d45421001c02a0080305241e4801280b11018040d000d06c4508003241c4c0300a21042c036241c000c02c064035410b07800301d090b9070f00c060080c2c0002801c2e01c4101540380c14950480641c0300801c0c2c1140100341d0f00090707603104041818580103058032034001c0c1c0d0203130880c1c3e194501a1b00042c103541080e035030903010450a44940e450140d84500b0311402c032074803100800003000c2403001180940f602130700050650041510381c001c11400780c007548014201c00c1c0c0042005c034259040c01880c0690300201c400150b0480c00c40d02102607a40c00079015018070074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 720825953 1250 720824703 720824707
    0x40908090d17030405010f06090209100e0a0308030411100237020904060c0905100507080307030b0d030309110405011511010f1d1605150d180803060406150c0206 71
    0x74904030501c0034040b407001c04210b20210070801003010540110702d101020090034099140d1b1100041e003680602e05032035038810b00c000310384408030703102c1c078018402000000e112409140d940d03194584198000c0d1001d4603841c00b100040a101e0a02901d4100c003841c0503c001c00748408180c042c0c99111000c1400641c60030b000b012441c4002c1102c00b074409070150024145030340e0b4209482c11400410101180b400132481ea0f040018107841d00c10440220720351192201c914003a2150b413181c6c029030000307121000740759840748592101d07110703449101485403180e00c00190803142410107001c002e4804445d248101e06010052100a080b00c4104045407040d04190000c3e50b000c030f410502605100014113022850a000041110050074040f01488031134001d0302c400a401071101d0407504214060140c01456114041d5054401c000c024940343c46c002d000090b81010340c00300104012220700d000d503a40400403003800b8031460988100402450088080401709540e06005001501c42c00c0c0082c1c861000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 720827203 1250 720825953 720825979
    0x8070b0f0d020f16020f060c0a0b090f120a0305060d0f0209090a140a0b100f0e101a04030614010311060c0a06180c090e060606252004090809 62
    0x2841e010340c3c51407209108900d440340006541800d802000c848140e10650b4406882601350809000b1185000141c1014020f04440d541700e155501d40c0141a03000d2620440740a03107010802070001f100c80c3d84011100713039518056441f00070242c07034010b05850b2190114103950700018081d0308527000b400741e041e6400e50b41c0343c0d0743d04c0c0c41d107040030300901c005040000056485040143c0c007003800506e5a1141c405110303e5200c1c06000d40e48841e80b4003a800501e0f604401c18842c5d040110b4035683d01040c0000c007014000d45404c2020104c2c02c400c2c0b4071619203180410288208582401442c220040741c01c1060396540c0f5503181c0c0280b010b04461f01ea80516800118a604450700f48034071502a40c01c09828800317903156540f402c200508510058030400700440340031030401c0c02c90142003401c09042c0e004002c9078450740c0410925510820990880792084c00406200c08408031041550a01403a42101c003001c10307089206004030008032903031049140481000000f07c810095404583d01540d4104120b0f03c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 720828453 1250 720827203 720827227
    0x6020706031e05070c060f0501090e15070e0d051203010906080118061505030604050f0d1b02090c0403050d0e190605120a0617010902012c040510090f0209090108070b0f 74
    0x48808001b13801282000d640c9030b08952544c000d079040714880c10080003580e880c60111a210b60002011013481d07107031203001c00c40880c419450b100704d081c0f0003000d078501d1895a544142c5030072912100328001403804401000752080610a40c0000d0407040000d0010250803a90502100d041c1c24004009541e1240f1400d1640f000801000141c080901120070b18101420055600c112241029030103118808600c1c411a2084403020740074810180e00c4906481298200015203000515082e8144002c0c0400008603c1c10886000450b08580303503103110303468607018060342c00520b807228032407244042401c0101c1a1f1003403c6400104400c80544501c2c1c40d401413610141c09254440e0f100070240d03184481090b075040d408101c02501c03d88030001c02052009254408a0030325204064400141150210504041d000223600843d010740508416449410180c02c4070451100345040f02c0d80400d90541c0c03420b0001c481405001580c0042c00401c3c40c2516005440c440c490150004820110300c03151401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 720829703 1250 720828453 720828467
    0x50418081b010f060305071e0b1209030f0d140606030115110a05060c0a1205010e010501050d1d030a031a0d080f07050714031009051002070c030c0308030106020706031e0507 76
    0x1c20f0080107000260f900d0130700c135584102038020b010380101c081e115580c880d24050254411500440c7c3c5540c10805400e81c4903d0480009001c1025400100200c0300c00c8010720000740f400c4009450001102101001130440031031340240700a00545040006000341c07010f40c4959524008203151a0b030019000204542c203090030000300600342c4c4109014410111a140043c0c41c8403c036694031a1941c1e02190100b0042e03407020b1082c030411034200380040c00700c0c0d4420cc00808144020703040124000700c100d2202d080d041110807003a00941c10102d44100616498010404107a01c103085404201031844d00007004141c11010041c09507a0000c0c0006401402100b0307500e0b0180c016041c1c3d9225507894001402c0d40c0da0301e0300100c0c4280a4400e00c6078440455204080c11107800c0401890110360b418000c030025030100c2d030103482c01e02c80201d0000000315862207580c0610721a143c510744951400c80064603202c85500000181824034441c9020000c2504400e5603020071860042403e8580320025a108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 720830953 1250 720829703 720829721
    0x50d051c050406020f070b040302010e010e030604060515011d010c05120f090a050414180f100903030605010914040519090f03180b160503091009050418081b01 70
    0x34610440382100681e008000340088501c140c0030307940701400001d201500e035103050043e481000800d02c01800903510a80803a5180a4181081d14810394110300191608104540480ea85911002004814266108ac1c1010301c6800e0808110140300000074110106850950904109030381413001c051040800c20010001d40132600c0c1660381e0030011003018260700030308490b4014440342d031000510382014461304907440f5818008000d81e8076400d051205206031002c9120040c82607003007558503a4010303c11421168240e4100240c511183c1c900503055690580c095414004165001c00001011383d0b010360112808407000a4a5a00c021845031120300302601c40d80b4451406070200104000d03400c000364214041c1c0c98a0000180c0d200c0030010b1401751740102c81032610f00780070642c582031120a890113441c0c03089007502c0c1032007459004a03481c00d400d204480000760045c80c0800070b5040a00c10b44082d102001080e030702110702c64958039010703c42c0c0000d600a1050718512000c02801c298444001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 720832203 1250 720830953 720830983
    0x2409170a050714070e010b25081309050609180319031407080f090303060f13020403050a0c1e030b060603040f0b0a140c03011508090102070c090606021b0a050d05 71
    0x98031000209281c4d240031a00505596000c0c04001203402d68070b0406441005417100c00013000c0380b0050b00504c4080740403d80458404005105150030b890900c041ca038040e14001e50700042c00d250220070040800070160800000240c4040b16040a000120440e8002640c140200f00101c1c5c001d08110001c1207608017111117a04050107108003e64040c0d8540e001c0e42c06200000f900d5298221226103c3c40f040e0ba50030352004500407401070320704188071340c036030207c0b4899401800c03d5030740d440b141d050001c040d42c1103410102c41e64062103605464a51290601c054110070290700382159102c072201100607101e03070700c82c090100021b001c0042000490503c070768801d80d6540981003603040b080180c0481807981c080d0300e0f190700014200c1c1c4d20000a41e4100c66500410a2080d8283c0d0025603400c0c001403d1207090755002c21179100854007251190000309844400041c1282c5810802414865100c501001404241e480c2e0300250b07480303400d00030a41d03a045032080000e010307a00d0301502c0c10070194101c2030707 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 720833453 1250 720832203 720832223
    0x60f160b07030b010f0e2815021e030405010e030a1203020d230a02030405030d020a0216060807091e0812091c150b01030e0a2409170a0507 61
    0x40080403010035000381002c1c0c030140702c00f0f04a180151030b180b01184410300064040c00f240d5015103043c100b40b21003c42202e185200e11001106041600c0c2026007255000c000007004070307a03410f5030400c40b1808001c951400c4a01c10b05604d091540c50384107178410f050410001d4141c001981d50203015901a00b40e20811112100a08881c003a000e904401c4030400b03098509106c0c03c01661034680c0c0030341c859521f041100401e80d15408590300940000d0416181488140108140584d5601c01409202c0e1683c009111a0383d40400d100c10032070b5250000f0040200d00b606105206170010b042006944891041c2100b000d02030341c3c2203400c68070f50752240300300e486103500351b400000182c0c0040001d48001d44a004407030000c40103134100a4200440104000f5410300d030071054001720340c041c00000340d0515011800c1c00d8241640c0c2e1522019440943c2c030030308030240382d014075006581541d1509a444d501440440856250800042088039880c0c000707910006030050050310a03400c80b10450b03481034000c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 720834703 1250 720833453 720833497
    0x8070206191b180b0a021905030c07270204050d02130b0406090501170a1a04110a080f0f240603010b06040f030b070516030f17090d20030702060f 64
    0x10815594500c5080340c1030701103d0701082100314401110044801ea8000306161640b20b4030a0200301040c00064039240001e01c90151003040601c01c2000030000d00c03c049410b0800365580300d008813403a001c015001c610400007000780c1d0310b41d5003490200d076070101c605130703000c801240041000d0003844440701c0e4040d16107000811041c006a102a042c0e941d24899910281c080c1444036170303134400c60380700606007038204698824084100c0c5012a880b910485c0c6824500020340042060514542c021101d01c1d0424003841003646010002c01021803007110003444000c5200030850800200c0d00c81d8400514800320019405840940011400150103482c0a5980d66500c11f035103080d510b5800200c403540008004100c55520400554400602014111102c45071a69064640003500c800c660240301421900d140b408500b4a403e911402c402070107014410303080e00009148005c1780d80000c20303004200011104d90703400003041e100b002c2c3d8150f4400d503403014081400d003103e000c1c590b45119142005c036442 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 720835953 1250 720834703 720834707
    0xc09040f03030f0c0f0201110901090b0d140103080901030f09030813051603110a0602010204030b0612240a06050105030415050c041a1c05060d02011d120c010f08070206191b 76
    0x2001501c18140d008000d090308d400050301032841602d900500080007002c00340130b48515170000f85001c09181c0c43c0095030b00d00d0440c490302c83d100241e00c165150340c0040340c004c51950309801007150300d14a04c041000751030541e5501520f05500070780340191240f01d040213402001001c010b60580701e000152448040344c0c0d80c3c5491a40c00e000003984034018180d4050000d04680140203540654f40d000c01d8100156841c001480030f80a0380c09259615031182007505007441ca8072804481024815413515820b9250000440b01503662641c0b141d41002070801c02c100220302d1206111001008419000c203107030b121100403036a18002c0350407076012503940c0c90840740360900040050078844102c80c500640c441e502644482100d0048804d160051202c2c400e101c01580700f070402c0404804120940c803800d000880c0482e00c05010702c1000c0e0203590201390740c00201e41c0c0040c0c050700ca0598900e0b00720200e240c0180025211070000d00280d920300402292406000c1b070316040b81701c980c200c800800907411503100300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 720837203 1250 720835953 720835967
    0xc0b010305060108150108030405010513180608010605010f12050612120703020c011115101d0109050a0e100c02031e0901030606090501170612010507080708090c09040f03030f0c 78
    0x4100304c034070500c240f9800d404000038160b4100e40007400503501b0540f0b0940103561031790024032840b81c5011412000b00380001c814800100c40f000c0c0e03d40c001490740c20411480c0c00c48489410150502140c01440300c9a41d41c011600c0d0100b035a40f0303401052a4a404001c900300241000401e08240111294262120303010b40150280e00e0107582114200c0e14010015180c03180c83d41013541c11364202204008006046440041e00314446502040304141e5541580201070302242421421503504001002901514000c007500008807130410405d07103c2c0355811035070b6400d410758a0381049480703c80c0a00c0c010b0080c03040d12011440e480080b1311200b208038640e0b07034540c410005180820b24001d40400e559205e40259000d0740c106071610900c1d05000c26601182c04001485194803040c1140d000d4582e880070700038980510f1450301c2c0e00c00c040c00c1c5084098a85d44c401480c3d101643d010040c00c18180c2d941018668000740c005840700f00700300c01424100c1c080c000c1070f020140e07100e041401d65001d442d446070f1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 720838453 1250 720837203 720837209
    0x7050d0c03030f0b060a030507021f0603020321070b0c0403020402030705030406140405210f070803011505070f020f040e0607200604080405040b010c0609060903081609030b06010c0b0103050601 85
    0x180c20458a0f0014007610111554942d803d81c10141c00e0025000d0300d4000d50255802903e6401255003070310703c007005c405240340c0500c0142c1c5d007240c03200e00410850800700a040491004046d42c51007040341c405020107540182440601540045000715803029440001ca17405141c0180c000d6584c0d1610040240060740195011a0400c0c903181c0c1502e846c070b00e503422803401580d0003c041c0507014a07045d48441c040052520010007503800b00519012511580b004140c86d84c818a5240d46942c50500d0307144020b100010584144201005654001101c204070822025070442d07040c83c2d45c40c001d00102d0020051003a400041c3e00c5141d050051150700500302c05c22080d1040e20b0b6261110540350074603120b09042c0c0b0000c3c401c0805020501c41ca1a09401460301414185021090180d5075110601954808403050302c0031a07a07240b03001c0034550310581e081c4d0320102c41f1441e0705025000e04001400089a8800a008903400c10302150700c1c0c0e0302c90094140126000284d0b00515616814450f4444001384 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 720839703 1250 720838453 720838457
    0x3050f063c150c1c090b0301090e0708030406140a0e2805010c030e0f0d080706060608060d020303070f02041e061706040f1203020d0e100f111e07050d0c03 68
    0x4401c0306510780d0042c120340d03001e200400a0030914000ca610701c1500914022254144514542d020895036a5040990700802403400003244800c0c11100880c2000540c0e0000c1030260402c000a00405400c076420031126496043e2850384c031941362104a440c04c07146200039030703c0400c40d1361030b06003100380f4030303030000d0030241c4100c0c80144682d640015546c0c5007482d030004001c1401011503022902c1c0c5407070000c204943c050104060140e039035039181442d91100c1d104a4181d56074950500c03285601c1010150f01050a4031016044411500060b81da4040d1500040c8801c60782a1464115181d50300117a1412403026482c040003010109000048e001d40e0289000150f0301d031581440d21500043e22500494012000c100400b00d07580303c0c44420007440640d4414180c080150a11840d024400d0b141da401c004000740400e01c03500b00b94101910208500c68203400c0c1003800000c01079006004940d21482080301c00c501d9401058594200ca008074980030b4440e00070210728240ca43c0e003011060216a1003a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 720840953 1250 720839703 720839719
    0xc040906090308010918020f06121009050c07020d062d0614042307031103010e01030210140d1a040c0203040f090e07060c060216080a020d03050f063c 66
    0x41d52040040310980084c4407030a26584806e500941403100c0c01e200f40c1c1d04041e0040d490040307001c10b5401d5001d010340c0c0350003080d0029074003007000c2205845001d4001c0e01c0c041006251801e19000164141100c10f800380880380d0300c8956010030f60260018248032107800c20b2141415025152850041415229004400580580b5001d8600c4c09114040081c68801140a02071912281d640f91b159001412002403580c2d0b101400d12032601c1c0000747d4021710380408035510700c2d810f52041c8413800b1000b1501505120030001840415000362040c3d5001e9000c291001840c0201c4c40301e82c80d00704003044502c4d604280f4101880460030303030100c0200241c401514245424990f980140411601852040000d90304400024814640f1641c0240c4120380190005400c2204140c52000c52105588040b503400400140c2400c40503014402c400c1e16504909042025203081c0f054500e441c03400a00c0d56109000c040341e000021440d192050410302c48180420329480120703019403603102d5480880038800c1940b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 720842203 1250 720840953 720840959
    0xf0d0908010606140d020705070e0c0a030c021c36080606030f070612020c030d0b01080a0c17061801080102030420010e12010e0a03031505030c060304140c04090609030801 75
    0x240501c0c0c043c0441113a88501c2c10110191980081d004400f00326018020b000307000500f05209000c850241e2210940d8507621550304002034215000b804203402590000c44400d400c40c01c09081500e240308850800802036202890314804a5402a00356220010381408401c66050000d003894180c43c001400c8914507220602010f03615400146c000c01c0b141d1040c0018450079206410300d10048800900150815040041c2e0904680007811200181696007200b5085076a02c400380680190b10140708200003204484000c0030a5858225098000b4101010a899803078241855102e0045040c0fa0b03440c40d44c4488509002c2e500648054500442ca12009400c0b49291000b410f4141ca0503100d407c6070b11962010300200249036620141c495580302c0c503224000d8024007414011038842d9400281800000c00d024492061315040940a42c2c0b0070825244c02e920b4440442c0e420a4012007a0b2042840c003114081c03400c020341180d1030b08542001100d40c1002540c1d0468940315100e61512503c0382c0e2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 720843453 1250 720842203 720842207
    0x50d021216090503060c0901020a020a06020c040c0503100b0f0c0d1e03060e010e10050901080c0103050a06150c08070f080a0f110c011409090720030702061206030f0d0908010606 78
    0x20361400f0f010340c10f4104102140d04c3d2146180200440740c010300684098049603000102d03100f0305907004002581007906007c5c42442c10f40700d0f070318035506281403060035400e02c8041d00c601c9042d203010340d80c0078007400927100d107000002000fa18144900403048889428079128000c1c00c51180b2244807088481e000d0f00c0c1160180613002d6081a40c0107440120243e0707103820110629030744041c1484a000742c0320200460543c07100143c15000e4441000100304014031600010b045803402008503640070b10b0700c1c2061140d0b109041815107400544c0c0f502e0b8800381c00d40e0428a840340b18454004148142d104003803010030220f803010b49080011030300c0d0303080e1072064490140d84150038030400988640141d01441c5a640c040c00b103602003281c7d4402a00d00b02a43c1c100401e4501c0c80a4500e0380110380100302c004035840135000c5100a94240001035410a54140e000c0340c03160246048100445510400145454800304036940422005408a0301910b02d45440540803110030b00034201d855007410030101e42c80b8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 720844703 1250 720843453 720843467
    0x50402010804020f0d050703060b0109080120031801060e0103030311030402091b0706180c05060f0d0b060c1515030a0c0b0d060b0304030522061e050d021216 69
    0x5901070315070800340d503141e5003040310f0410003400503544021922500000b040c1c003000050040c1d44581c1000039501040c400140c900310460348504c4031681400034035900207611901d0103000450b05030000341c49494154403aa1007101c01039062140350b2030008001058107181150030b04032400b0b628200910070040017a80118401218041c0d0404950800f1441c0c0e01e9480910000c4a4860a0440d0410000f45d9456068682e00c0c43c010050000c0f6100f02414001c0e0710120500400040300d0841c5014a0040c984506004800015000540c1c50500031560313200c820448211301000015200a081481024610200c2c20717100b41203480b0001c10300b0085400e0001e102144c036a00240c0e9008424a0620030aa40742d2000c504903a0580d02c2d04400107030034180c030303000e140510712903251580c03500300b5541400c60858003190341500340800610108520f54000803400c8858091080443e4146554002502c407841411a06c0032010310014004591590001d58140a42001425030b0341c2e050452104480403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 720845953 1250 720844703 720844711
    0x1d0304150c08030f04060b04022a1f0b0402091f0e0603100b07060204171e030f0301050d030e0303161b0501051207020106052d0118210605090a140105 66
    0x1030b91042000c03d940144500300d090380b05100352400714007410000089030698100302c80f01510112200042c03900c0d1514402c4d580300b4128154001c1a514400b035901030305004014002a01e07a84d9910181c01c46074a4070740480b940000040c0c074024440702c8080e15006c0803503080c01d05100099a0400500c0113141042c2186e010320850316910380d0382da04100100d07859900400c011070b5080d80c00c00001440102d006160404200d6620140c94520392810000a42c1c0b05410400342e8107800c10042141c20340d4030801528107480e01036a01c0aa00c921a203403c0e104d80041c140701d95031510001c0b40405032505c00011503030105208607402c0401c05c48100205004441340c0c041c0502050050101c18001c0152446065001c900d500c000300c2c000e9640c00100d03d82c3d01c08103000f0036030b04840228440944080703c60f8426008001c3c0381004185121b215180b4450f810382c02070072002c1001114050312246411006403138aa081142001641800145d4a544d02100e82d0200c483d0f202d44d01511400100c180700d4180302d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 720847203 1250 720845953 720845963
    0x71703160f0b1e340c06060306050702060f0702070e0a20090102010b09040807060b060721030605030a020906010503070207081b0405090304030b0f1003053a0507151d0304150c 77
    0x11341d501907018000c0c141004508420400482e05090200e04140070345401103000398800542030404100003810260011b013030f40ca54058010502166980c00200201100d092450f40c00180c1c490070300000c094142d682c1005048270800c4520744e0044419802840110000d030000c10010342c000e400d21120710022a000303803094909000080114030150000d0001503030013401a46050816900e0880007040d8502516068000940d9610b21a030140714060103000e040f0002e0000c030b40680c0c001201d4140043c8400d04125022000ca40d82c0c60080101d040949030000c01c2d03882c900c040f2121102c003280040703131040c452800c14002c9a507191703010040301d080e00d40296800d030095803110a40080d00347e01500d005402d0101c008004041081440702c90b581034003d0f05441c10900c145000f0141039030241c485021414a1300c404582c070682c0000845801c6540094070f43e180e0302c40c1c1201c0d0001403e440000e01c200007408580c800e22104088002c2080d1402000b8100d00c00c0c3d09008100c8102000200040c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 720848453 1250 720847203 720847261
    0x1080d09121b0f0306050606040b0313031b0807021306150e0102030904110702090603011a010323010b07031e050a050310180b0102071703160f0b1e 65
    0x100004060200519103401004114941225400070a4030b08070103a000501200e01a5001e10400c2000d01603141c003c01d00b00d03646400d01e41481e040302e81c54400a80399900240e010303020744003058041c2190720a0403101003d010765242690400b140f482c0d1040500300e105116046003010347e000359100f120107071152026040103040712042c080d10710502c1144e81c141540f0042c02fa200e82c9685a0082101c2d800503441d003e51240701500c180403040354040c002c58400e906020000c05030342c00200e00c03840980000d1a01003404054041d82e685145007400c1c01c03000090740080007103500c1626000030304003c2d110741d80306200c19a40c0062201030f540000c171030b400002c0080000710b50746845803002d150000340f0b544411303025907501e0342d00b17200b4507a030494000f003c103880390004406580c040c44144020117600d5164240119588a5140c9922400d080b03c200807040000090a2040d00e045901113180d11201e00c892034207107101b01001461004220704c1c3e0707a400b224006101c1c0e030040c80b911074001c001d80700144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 720849703 1250 720848453 720848459
    0x40c0b0c030f04091a0d02091504021e03160e090f0c0c060108010f200706090f0f060921020618010e010614010201150803070b15100e030601080d09 65
    0x2145500c4100e000810344014010b420000103004014401841c4003180010310100003110b1302e42c1d0310884030590340301d01d010034140c10168540445d4940e008070582050301c1d0501442c2c00081c000d00030310119105d0320820040c03504c2034810110095001d1800d5080f01c0411040f846012192031704982c40c510b400c00c0c11030303020544d0000d516488030f40069152071310508007404414064074001c8240d00055050b91217007202007449402d4810007850002004070a0072140c0f007420409404d109098008242503034600300e0400b800b100d14a5090401d5024241c5c10062007281000400b40c44d5400c0d0544020030040190704111003080c10042925201c0d40190101d550381051a2243c103400f084084115501d404900019000c00c1c440c100141c03403030f20410000041068002400c45e82321083d0b4010708400c7c51002d021500e0300009071011581d0101034460190b4072041030b0201c0c0c44120005e19008440342e0101d002980d04181580f01d5910158100d8070940c0c0da41034407a5a0b96107a40d40f000c0032400945c014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 720850953 1250 720849703 720849719
    0x180d02030f03040609120216060f09030f11030709060e0f040201020c0d06060f060302030916051e040902090a0b0f090601050a0311040f0f090c1e0e4005040c 69
    0x20b9503016004070800110401030741c0ba070b00001c0e040d40d1103160040c0c01000b0190808444820020f02410803881c02806076600b10002030724070400e501010300f4002c070740003410701008600c03030032a201220b015003a0f4070200e940d54602405085030740940d410340c0000c40d00155290000402e2a0310881c1c050b4004c03c100000102032141c6d80ca9040f005440d065191300c0302003890441403d00c03400a00040e03500513500c0c6454281541050b0904441d044200b944000400041e90b4003142030b5003454440340000d00d0000040c00082c02050082c900039040161001040030703650036580071680052007524402002d102d50010002c0e401022500d0300c0c0852024840e60f140c545c4a640044400f002d40500786150a03181c3c660503a008e00c84d82c0c403d030340915003d84140007000b1240604180350507542404510214402e100b205000c1d01410f5410400c440441048819918402100c0d0f0103600036007052000351010455118a0110f5850508240c5514000c0301c60303c81a8410030b40310302d4000c0348001c1814104107031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 720852203 1250 720850953 720850957
    0x100216060504151d0606030d0c080a02011806020405091501050d110c011107030215010305060a05150a0b0405040b0a14012d08040c0602240a0216050303180d02030f 72
    0x543d0031a0503c0c00440f41e098440c81081074070540c00007104000c00307180c6030071440d10b00000c00041c040d800440c0d45843e001d0b00f15140541040e400515103407142c140101c220b00401088150041c5a92145140c000b8450545e00034415030b081075070446080e5071240c4038640801414443c440c002001000914481744050f0302187d01c00a078015003a00c2c0052a040e142d003514100812040d0a1000017694001c1540400503079021008400500c6101c0d0724684078243c440c6402010785100b691100005002c1e0088540c1c040508140144030b0b50b42d0340d40343c0c000210150028081d05000310300d4400105082c0c540402c1d40c108660071850054401c02d1000d00450320b84030b803030b0159607a4840981c07800c0d510360700d01c81c0c44142d04005940c2d03030003407860a03041800c0740103400d9100304155084100d444c42c1007111004640c1803024801030105103515031000c0c0d94000c1c451444010b003409071071381c550410413102100640c06004a0480150300007c4542016180d180c490188005038bc410848400b1244800740 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 720853453 1250 720852203 720852211
    0x907030209280b0708030a0b091302040b0f030d020604060c1d040b040b0d14071d150a0b0f0c06010605090a151e021c0f1b05160b040303021002160605 66
    0xa0303640b9a5561020050344580006004580008002c02040f01d01e40c030034460102c40e0307401154000c0d00740c100340155034943c900d000c102a000342d031a501e4540e456100c0100341030203903201a0486030f22032041d64000b034503440e09a8040b42c4840c00c002241c03070014401d99030206200c02c81502c0c0100c040d165800c100042401c113030600d41280d1140c0e4100c5150383c80640110a450140f0162150341c2d0034251064181354075500440900d5620740f030b19540c0e0b2200e203070010340d014481e10b914a01401d075840010b00e84030010381c0214022200082e5040202920102401c13903040e800302140c403a41d803500000d4596001d40d420700da400101e199010000e0711907031004110404c0f840e0030034021600d400107800160b0b42c10404002d001d60b1200c18400c0307203003c02c4468610107009a1034500c503100210100282a1101c041c070400c95031071403004040c2440410300c22020700c1d0b62115403421249940d003100c804160072030301c426000340c010b0044140030284a40200e41401b854038810000b28007c81da59a001040058 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 720854703 1250 720853453 720853519
    0x11010608031b15041a0708040c091503080d0f1406060f0d020904020d02030601021011090f0f04020703020604020901080123130c0e061201020f0a05160b070e0907030209 74
    0x80c403da0940168107030607030040d03010b2070008030f00300000c011803450f204c0007400c90002c003d400d0041001251030109103006980840001160f44a60303098030407110a21500054003e020000d40c80d040c026803035100c0b400f00c4484200610038400500c0d1101051003088446640010003000565107111640000f080c08400350b100040c00c25440e40d0204049070001d4511074119a800000d0160070f60301009184100060740f24144141e02d4025405201401101c0783d850240c02c9800c61580da46e41c0d08801c9070301200d0098801c40d15150070f410005d5641d402940c080e40074080c04400416900010b025600340d0301e40b503c00c8071170350380400b4400071008100105107c0d01e4040b180030400c000384d007410743c0c10300415041807480a01d04200b810000020811240d9640e1030b88100101a95405e01c1d03810344070b0302901400d20580707070500ca5541c1c520207000303400001d062120442c1089003003030b0401031002000c0010340e01050142c0d20003505404a1203030a106540c0310b018419a221074441038480e04070070324945 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 720855953 1250 720854703 720854713
    0x7080703110d0503041430040905040605070f05032401141b0106050d020913080702030f06070f030903200f0106080606030c0d0b01060806240a11010608031b 69
    0x410012410030b50500644000600004103100078400340d98a0440c220500d40c010348170201c2c240400c41e0226010114070b0114020070303031007060b02192900a8130010726242c1000d00ca649080e00e4900018402103803014040350250301d072024120302c500140ca01c030ba00b03400340c100c945081c072a103080560381000403d281048840030480300104444005030055001d000c0e84103002200010369982951013540207a406071581044210169980015443c1c10251750014655060941d04000316984120900a5050300c105070616012020004d41c40d84901801c1c0d56500c02c900701c01008400307403058910080d0000b070030981d800741034400c0380f0000403a03800301004842c0d811560105013820354105900440303154100404010703860070b040c00100c080090850710707982d0075a107590f640b40c240c0006000c1c010810000400283c2c170341d12400410025034110280090750b102e5449101d1100ba03205d40044000a0000c010208140b403050182506680601000d141080d042d110004425180304207484218410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 720857203 1250 720855953 720855977
    0x309070302120f0705150f0306040b1903150501050d0201051b0601060908070909030912080d110a030e010501030c1a1e07050f06010e040f05030c0601230f030307080703 74
    0x40c107100c032001c0074401c0000d07000c0304501c40b10340c60604d5919800b00d4007440c0135507046613140100d8070132540001064400582c40f610386c0c2010070010514200d00c43e8000c0c644d9070611910902030100c01c82160320907a42007244030400113030002690000e1040e503411074420052a8010343c0590040c04e0884031529a2540303400350f145040345820002e0784090003198250b4001d01010105000703180c0a0080038006120540300c640c2d000b42514414441c60031444400380110080204c403030200c1e4070540c04510180011142801c009030340b030b07222050180c00b003468000551714544060003058100c034ac20401c0c4034455444c001ca2000d6250003050b054030390070001c104039484484c500d00c4600e01d1075038405105454024078686145020844143c50344d01703a1041e8010040d081e4800c80741d5030300c1039104840d5107c2d900d172480c155143d0b0241240c1c10506010366000402c0b502c03154180e40c0782d50054030b055544081c2d0b901090189000041110740d806400070442803010131203510003858828807900d817090080074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 720858453 1250 720857203 720857209
    0x50c070b0a0506120102090a15050c0d0806120c0d030f05040302040612052a010c03120203090f010c030207050c060c070b070506072a121b150c080c040b0309070302 72
    0x90201c80d41d1041a545000740b1141d8101030070000c00040442c0700861402c00340c03400242e072540d11031144004801d1845038216401388a142540c043e1132901c8102d81d454804140d019240440c111150f03806031030001e00081120f000002c000e071841130003400c0c0c02c014044d0b41c1c40842d04070420372010b20502408000000068031680301d00f0008158092542c10400344510740320b400c2c01c6ca40c0309107407448500d69050703403d40c030002c501081c00c40703200742044040e29003145019103840c0000c0750119181803002c0300b0003260340004244860080b070114000c200304105210160124000c1e030390054801d41c0701e07000040071807d0820042802c1c050841c229440f82e680d81e64140e0890b44541400c440325004002400a41d6410044c0503801040031556000e640541c00d21904d041c000210003e0801c01140a2403c061409060700681840d000c5500381f04100c1e8a04180301041c044420b00ca441914004005005521034400b05001d50a8641a6840c040c603051110701140c001810010582c000c8090000050f9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 720859703 1250 720858453 720858473
    0x10320030411270406050c0903070608060411030a050702060610020d05280216050d1a070e0301050c0a12020a050319020f07060e011404080a0f0c0b01030b0f0903070510050c07 77
    0x507800c1c490710f56607107000d1401409807500500342041000782417024810540e00400c44c581134809034600703130001c2d6076004c1c0020041c041e5017900160901000082c440070603181d41100e4812046502155959240e0000b0b014840180e6000000140c00211a40440e07502c1800140482d02d41d40f0798501c601c4203555160990800a0b6940c07401507480740041c00c7c0c0c2d100364400c43c4401080c04072903520101c00640c8410071400d40c6d01c0e0000c1344403483c01c00094200e6014845c495090f0102400070415842c2880d04001c0070707845076007804041600c4440150034001035000711460185156201d60854840701c947d00e038204100081c86540b25024011001800e00c07040c0585100b5020303100c04107200850480003801c6030b000c038560034050ba1049003003201242030001150741d50342c0c0900d0600d84c01407160030121029003d40034020441800706000106101000030220300444800481c2c4485444a414441e900d20031040000c00701e422510106100044a5100303640c490700300c002c000c3c60400d1a80e240b414403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 720860953 1250 720859703 720859759
    0xa030602030901060f270c120c08071101052403030c1002030709060503060307051e030111030708090604120305220609030210110f0a110607020c010320030411 70
    0x10fa9542d0b08100a030101c003a03020401800100754100c41b042541403032612145103501c106001c83d80b14801c10100d248641c4030340c0d02003c0340d81c3c02040780b074045034401051082300f500c111000542190600510000c10300c2450700800a51030b03240c000f0b0713428021a03080d1000f0f4980040e4180001d024a1407000c3d000d0007000c1000e000c0e41801a62031516403005400d48806400500c1040f0040c010024147c400140c40c1c003e072072044401d005a0301410750500300c9612801700b590f41550810f00145040c07010030020394007424054480904076074500c0410755a500c4101d8001d02003104990003800082e0003a07101d550031003903e101c00d2070100154107040341314100c0d4a40890304140d40703032031311414180e05103ca43d01070741041c4405c1c0b10301c0c0038140c002402800b40140b0074540907400600c0410445c0074201030340b080c2c0580300a60b881403900c0100a9110b0411170341440c0801d040c41c4200c0c039180f0101c1840ba541c1008044110b082d61125196182c0d03000c0c04080700d98101342c0f204610340b0080c1c0c8413024800c1c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 720862203 1250 720860953 720860971
    0x303230f041110020f161508100b0a0e041d060f060a0306090f0b01080607090303180e040b040b07030209181503030c01061e0602030712090f03083a09020a03060203 72
    0x142c0114580c660301c1c015aa89240c0b071000c0c000c1c8407e0041201d15200141c1d45281440d0075105070f1640340356642d0744034040d40300e82141e150004040d0301454010415103019802200c040240740410405180500401304001c9150f400001c0001d1001c48800c00207508650041e103c04411900c980d50441203d21200c4140e40c43c00f6200c12101c10440c4882c038040c05040000040c1806082004000d4480e03c0903000050074080d4010107800c0078518400c004c0010140c2401211a604150078903065015094a083d03400c01c48401c0003400c01d41c042d000312030b03481a003c0c20768100f810400f06010284640a40902d0b81101c80c101104102e540c204050501504260000500c0a28009600151200f9100c01c2007940c035816004200894000c0180e440064101e1021000c9140c3c645003180d040126410024151090000220a010428001c0d028040240c1e262252107804d54182880344810450b4080e440c90480a40c0d503030f803280035000110550305c09400c03143c2e801e03204e60b41c140980e08100d0701d00f15 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 720863309 1106 720862203 720862213
    0xe1218012c01030e100e07060305040b0402091825170705040e1c020c01030e0c0918010f0e010902010806060f0d15030f03020106030303230f04111002 66
    0x1013100501015140a02803e40c140802405a02c0c3d40b45002d2141300c6004c14003030b000f071003124013582d00400064038a5989508000f02c1550042c035960902c3c1555103007207009003023000611000114251041d83d0140c07200c05148001c2031982c0720a04420355400d908119103c081082c03402c0c4e90040e10b001c1096500860440c0c0342182c59048801944480c034151405580e0100d6000c445100999040c0700b100d4050070715541c1c0c0c24031446840e60200c0201d0118000714404006008425040720000c11422094041442140d0700a0403040c0c60341d460301083c0c01150791184106a2001080b83e20034100360404c91590030354061290026059a40e03034000341e10642e500180c0900560f8422504a42e0024901c0d0082c042d025070700c01100401e0030028107851800031a5004040259038281c2c42c1c5090f6a0122400300c901d034060400d403610100c4810744c0341d40e5140c82d0310220587c00c454000305 = true := by decide +kernel

theorem cover : BRFrame.Cov 720683453 720863309 := by
  have h0 := BRFrame.cov_init 720683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 720683453 ≤ n) (h2 : n < 720863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
