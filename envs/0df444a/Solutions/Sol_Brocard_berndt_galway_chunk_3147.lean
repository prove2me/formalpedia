-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3147
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:48:27.99746+00:00
-- url     : https://prove2.me/submissions/3516d8f0-5af1-4d1d-ae5e-734699de066d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 565827338 ≤ n < 566007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 565828588 1250 565827338 565827343
    0x61a10030603020330130f120501050106110a08160b0106090e0f100603050403020709020c10060803132112050c16060503070311040b03070e091303140d09050708030c0c03 75
    0xb104ca0300301c8240b03042c1450304200c03500c031b500491000910380180380008103920350f0506402000c0d0059405409019986280c41401c1d81da0580040c8200441c83d180060ba04000055007030a40394098501a2141b1810000e030300782003203054001e415807910b000000355080c0c12042e0402610700c402e1700c51f51581c2d41c04074084004681900da0351240701c110170f001c2152510950059030454801c1c81a0340d02503649000704d4050381c028a082c00f5598200d5104425440141e200d41d000030445440035500f0019030b1580014610705034411410f4500003452080d5680301080d40000301281d2050101c0500040400003c05542104004024622546028803500c0e100840303102d045500e50340e985440c59a820340f08402501205403040c5201c1c00c140008160309400b0780c0518410000e564449110b842e0325001c12100840140280d00040c0700d061520001c03076481842e441100e9040700c0c0f511f984555842c0e000004003000000a0298000c00502281901d40800204041b05015088a1404d5103d2003010b8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 565829838 1250 565828588 565828633
    0xe01060f110307060e0a0b09030a110c060304023109060b0414011406040e150f09040b150a05040c1701060306060c060f0e0a0303060303021504020d061a100306030203 73
    0x70010b0b8000e100702c400088036a0000c4121502d000300b074654010741603845038070011090b60003100d15007011aa000d01d4990024154542802c4003000780003050a03040812007070712000e00003900402a110314002d41030440c0283d0501c080300300c100552503021100700d0f01c000309042b00007141c1c500d0502c3c40030f8101c4d00e000c8c0618940719100c1410107225902c1c220403c91000061624182c101340c2c00c4c440080d201959000c0130344070348561070001692680d03050402241c080400002442026000103010110f840c25540e00d5014000c003100c200250b105030700040c3c0105040d4011640035090070000d09219070300400c1e52069a9400341c0018003641c039072400394140c40c06da0154900048080344204040391290300071712048a03030303e071000403408098031070b080c101056200c094000c02d444210400030941d0412548044207070001d00c5241e6401c0030390009900c19207104015107141c0d10741600c1e81a00d400444104140040202442c4e031100301880042d002c0d003044c3c401039100e03000d4012841052200000c440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 565831088 1250 565829838 565829867
    0x60c060f061e01030e25030210020f030a0815060f0904050a1b0c020604150206090610060c020f0a05060a0c050c030601060233010611100e0c0d030201090c0e01060f 72
    0x2500ba001510011001444800c0c9054003d11500d03241c9242c01494000d40c1c01c4280389050040801802c500500440081440d104011540f1035224103c4001d40402a1002410945810741c038035240c87d4002c03851450b00709005644003030b00083e07810034224440028202c8000c244c405008a07a0b490714020211407102c8020f0000c9030303040d09034500c1d083c07041419142042c0b00805213801c142e20b074a4085d9602d40602a464056800042440381e000030030031005620440f41c0301c01214160900e40001c00ca805e001c04000c1c0100d80b81c83c1d217010540c2d202c50300300e00070340f001501854070b130011024010411b00103041d00340d03014000d8040c014054100410300718143c0e8000c0e001020f08103c1440260000c0444040d02040307070040c0e0820315a2507189103200da00808084d078892002c5000300501505146a0b001c21307070b04151502d003010803a60004125001180011103012404011504059015108440f002000b5594803007010030f400d2045030f1481d060312401e60b1580000e0704020b400391640340074a00d44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 565832338 1250 565831088 565831129
    0x11010c030b01120903030219170a05070207031101050c01053c0c0f1209030d14070e12100e03071a0c072301090c080d0905010917010b060c060f06 64
    0x100500c1c50094011401041c0300781b40040c500030041d40c2c0e01110044021600e40060140c0081611a00c4407054094024a07202420882d609081e440655107001a00c0010205816490100b00036802074081d80c804040300c0d03000b031040c1c1c500f0480c0400c1190314444100940c0001030802281c600050701c0c04213000424285007121034a508030784103841c0d00f14038003118104e10104040c00c404c04420a810b401a6018001551501400e228030025940d0000e4070810700300000081040940e4010900c9086074002c1e41d04010f1510702948150409800d0043d800c80b840c03d02c03040315042c200000007000781a00856a032500c01e4800508200c100300141c0d550021144180181c41c0412541c0c0244d0048001d41c1d1402c940800c04201501d0944a4549003601c8500b00c1100c2000661030510051803a20107034680682c089043c08006810005140a5104180c0d001c5008810f400400d5022240d640c0c0c0040c42c00707440c2c46180c51000c2d5074050490309056690300b84c01c003086090a007010a1104050350190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 565833588 1250 565832338 565832357
    0x4210e01020d020d2007030f0b06011e020307171b07031a061f03020904110c0105010501110d080406090b040b01090b030606210703150603030e0f0907180806010611010c030b01 77
    0x2c070a0400e502072842105c14012484001f00150281068002c158401c80300468980ba015001400c803113945c0003501450124100b1061701d40394080f00b00c844181c0e2121010f000c01180d4024a0759034052401040940201c203048400d83e44400a41c8034200c0c0e108420301408035500300103400c81d501c0705841d4650000d0403209160101b10780c002010749005018980141400c542c480041e054403081d8000d41101d000000b0f06c07002011080c01640d014003000c1c2011048485050000c554514140300d640c402c101c00007000c00c00b0058039401600340e0782d0f04180803440d2402c1c582000000c100d02840380030566072514842c034030740e400c010131410b00c21900100040d00d404025486150010800b40b4240c040d1f02415001100240d29000c107007034070304140500060b101c1d08500d0090050103a120001c1d00c18200c4040555031907a41c024000d500c06800c1c5491103030400ad540150f06a441160001c003820300440c00007041d2a41c2c811840321030005084002c1c404142c0030300082e02241c90030f800d030782d000551101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 565834838 1250 565833588 565833617
    0xd091a090a05091306050708060f0a05030c010e041107030206090d090b0a0f021c120c091a09010212030412030c0507031e09051f180b03040b04210e01020d020d 70
    0x910103500406030300000000c804c4581d5044112001101d40001054148062000504194982d000d000e034040c1d40c0200d115007004006651024001ea140c0d04001500300903c03416204c179041501c0b80710140750103a854440713901e401b030b40304c2c441110031461902c0f441380220b5207a485800c0220464a0128480c0c0c5068200e280c00c03640d52409102c0a003c0d40700300750010000228a0f2441d004040e405da4641d01d154038081c01c0e207015101101d070200c0800c0442a0140414002c2c1c0591006849151110696403111240140e007480083c1000d241d80040c048208000d00548500e44190a0420759040000b45141001590302c0d001c3c510021f0002a0300e040b0810110b45801e0920b1103001150414800c942d68400010317450810200180180100320380e0461203d6410802d014245040141d21292290402c1c92882c1c00e4040204081e080140c3c1c82c8c041828000f000a012140e0303072170316018444090010002501c8030420380f01403801440b441407800c280e5840480c4041c5060055a02c8196441030706 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 565836088 1250 565834838 565834849
    0x6022d04061b050f0606010306080111030c070f05121c020307120b010908070b120606030105010f140d020304080702011202090a03030e0310020a080106120c0903020108100302030d091a090a05 84
    0x12000c030301032a40515500004164100104d5039002c0315a4000c2c40140b030b1070400103094580503844007107542c2c14000d074039920686a0003583c1d80150b12080f25521050a800d0050710383c11060340103007540c040c90054500d4802ca101c0148200c2580f00c00180e0343d2400b4035541d070100d200c1141d070003002031140300c042c9030015080d4001003441c4405161080c03505450300000c9042020a0b03008800e1020000740b42e03011141007000c0c003580124212000c0e42150325000029100d0360b25905003000300200c0035000303419104100c050b2040e152a1000442d140d1401c1e01c7d1040e401d910010342a804200711305495503c9181304e000710360760003034040c00e9820150b296507000e69150b03000c5003001e541801282c00594002d12584040e11941010707559140716545030100180c00c05403036001c0083c040d4140b0000c5402d180d0071000300c0c0200c03a420720b0403541b999600407070000c0c0d20140b07400007940740c00740350750b1030414540c003446203800d42c3c0744840520100e0b50340c054079265030b204c2e4000c459000522110204107502c2d09 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 565837338 1250 565836088 565836107
    0x50a0c020d0c17030a020705030105040b0c1b03070c080f010921020708010908040e1b0406110a020312040603150e13021305250804051b06090301050406022d0406 71
    0x12410b00400381d44543e0909070310740d10410703012010780c008151502102d030f041200c3c1c401084160020001c034101501d440110647c01041c0042100340002c1c05101650701c00201c000c01000581900d0310340340c2d07030310300020841003611909040b80f1600001151085040c03080700540c6500c140340c4400518003081c681003100d00305c1c1080003540298180051642421301034050228440d1441a958500380032901c3ea1b00e00d405003040321441481034260030f01c01c02880c00c03203007618420f00300035194008040703020345401d1840d6402501030003207144010000031400c02070000d6030001c0d02d0030b01140400284190101d003c6100310500b040b10030011490901007041da0b45050707800034013820b24a00c2c3c0a15528183c40080e52a480030b94205617000c0322070341071010316000180759403030581c20b18107150b200d869440003441a2940b01901c68000d481d4140d441c50700315415030401400a0000d450079003040c0009400003003e0603c0c241850b020040001070014408410042c00d04107142000c2c1040011501d4190 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 565838588 1250 565837338 565837343
    0xe0112050f1609090f0b09312102070906050d021f05130807031e110f12011e0b15040303050306010c08120702010f0b031203090703061b090501050a0c020d 68
    0xa4010400919034010f0504a1005080105001c01c806090100c407d00040121f00c0d40c00061a014903048078119211110081c00c0c004038518800505040007101c031500418503040aa03805a09030b001d80215000080300c00301e01040000c07070f5840040c00340d440144d070710095002b00b400a9490398144240701803182d0728214a856420043c046c00c1030615003160f0f40203102c455200120401c20041a0310001c480501030074070141305041645c0d9402002411403500328412000040f000c1140d844420b06203082ea07090100034040200507045000031001c1c03907808840700360f003403020703004203420151580b1024080b01c03010300340b030700e031454a0459041e04083e007840e04200c10b0070200c0011500c40c40140038400a076148125050510074006403c4a43c000070b42c6581c0340c14494020120380d40400c0681451031016a4240c0d00ea681d0300c0e40f01e050404a1700010015898012a1610800300b170a4100c40c103d045e49818281680314cc00568040c09580807041c00680400c0300b181c01403c0c2400c000b1007aa1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 565839838 1250 565838588 565838597
    0xb060f03190606050c0705040c081302040e1009110603090303010b1308030409061d010323030d14060a08060f011203020307120305061527031c0e0112050f16 69
    0x11a0101c004269542ca50000c00003030307004604403940d0700060084000404c4200c4040000d01000f010140042c0402400440f5000b9041405020341d1566049a0040801030301a18100740f0750b51484401800c4408080c2e425000c107800004090400c070b42281d001c2c1d1038803c01036080d0b03860404201e00b80c2e03001d041d40450f015451100000d80c25001c1000e0400780c801604041680c904042a40407800f2000800a0700e0b0a4151300401c082540400d02002550000880100c8075101070815480c5100c3e400c0c00400700b61524a8149940360404180380c0110700407604e0500e0b440d40c40c10038960310398090703803004504004000104441400b100079103013258440e0050b030f41004065104c03a0080a060001c100219807120208803440c0f40c840320b0f003040110035040c2c090070043c00f1114491204041400001814500e401c2c0070350a40d410820490f101f80c282070341d1400c040b0180c3d401014412401c0d20907000c5800e20303845003180c82c06c4d80a901d100d01341c2c240c1002c49565495038021580342019608a0501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 565841088 1250 565839838 565839871
    0x8030702060901020f030a02010c1101020304020a0e0a091505010914041a040c0b0c070905060a080a12090e0c04090b010e030a030c06110a020a050d030b09150307121a07030b060f03 79
    0xe40050007d01400320080d000020749141500001e03080ba1542c400100c2641d104104000059507035400031002d4071007018030500030780c2da14240714005002599001e041001d44555003050702895400c0703a41681c011883c01e1019840340381482d000024240c0c1c1c02044014241c812602c0032650309401076000d0b006100325115903503942c5a04100c8c2c3d111b0b5200b000e4603080114103010700c8155025142e082501070f241c50303c50a2800e02a251140c0011600502d5806110342400d035580c411003503c3d000c2c0c01c1e040d00c0b16103141002e40c00d0200c41d0f842480f442102c42d0030003151503200d40c040d2040e1085000084c0160000d86050b035412a840302000104a60099035404151455064070300079080b040145d4001300003452413030800500d0310b29020050400c1500301821025140c4513400800c0d048425205081d10f404180e0000a060800d240c0001ea0512003410f1a442840804406d0b50b075502e0101202c85250f407990b002c11020344a1001040341c0201d41002188200040b800040d81e21007640702014600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 565842338 1250 565841088 565841113
    0x141504080f0f0c060a0e030c0d0305062e0807090b0702042406090807152a15061d0108060105010f0e04151d01080a061d06010e16020105010803070206090102 69
    0x16000b507840c3d00b6031680401d080280b481460720426610480d510020b50606201c1882d90340e981d0035a11200c01003649a00126010b0b40381c100e80368103d004c40d01c05250200a000c11443c3d403100b180c00c0c0c81400214084007180c07c0c00e0042407030304d00b0307128000702d62840c1182030b80074000030f00150074400509648440317081c204040e40c0400303103001d4a003660b29030314014640340f8064948547d54000303000305824064a01c00f1190844054410352030100c010140040c85800c031400c43c4816084064150b14414203904541d50b0246d00c840e06444003182c0c04141c61000c101d140d40c40c81000d0107041c6140e0710240050110358000c1c160440304403e903142c611340c08a5440041341c1036a401c059441c50158402c0d0092000381039604103141d2040070960481019032401e180303035940b01d007440805459176564172840756128a90100c01e0502561000c02c540e12960360b408003a0100703004680030114210070680942e0604c0c41801100d04a88050005509029154082119a500015499040d0310882181050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 565843588 1250 565842338 565842367
    0x50a0309050a0614010521060103020405040813030c240f0305060f0d0b010e070503100e040c08031204020307090204080703020f04061a0a032a1116030f141504080f 72
    0x120303042c0300914601503502d00000d000608400440c400407070300100d0f1f500b0340280400520541140d404840200319034036130f41010b58582c4035082d0459040100c948012041c0710141c0b0f20304040b5051010312911502103d07450040404000b011000000c820803c584081d0740309800064100000504901142d403510000603000000b0903412112842c9080c010803406800d503031032a90103012070801c6407440c0b03828905805210218001c05401c82c0b0810089014401f045800c0e0300a0013005040700d548891042c200f8803002030840c0e0480c0320f88907000000c0b444010701d000340c904440c580e200901c0901e04541c01c00039520104008180c110b50f88603400a4248401c011103100c1c00d02803c05d503030b981d440444004007591110a0429041104100100c410580c0441e908101117400c1c640381c00c0d034038207506029003020703044100100e08102d00c44010040c440708e1040300c602c1501c58492407018010083d4015155110164559070102e459400a4085481a802017843d0034030782d81d5403031030100003964002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 565844838 1250 565843588 565843601
    0xa06120e101406090106030b10050304031e211a130e0d091d060906042a0203130e010b030c1c1103010312090506030c0c0a2310020406050a0309050a06 66
    0x1c0301c030302d001c000e00010741031281d2180d02425444c502441040c21117000319124031041c0007580c041003800000107041c10f11404904d0810fa501e00c010b1484d0b07485402c0d0003085c05a0501d10b05402641040e085141a01e06200e900e609502c5841848103d5403160108413030b50300b9003201c0568040d198100301e04c403003005026002e04884161250000c0d41e04118811804454205184002d81040c00a00080f40d544035540c1e0b174030000485011480d0003140c0d40d00042900340c80c2c0d40141d00300c1d150000c41d1480d90040041d10044840c0131a880f01c003580c5511f4840c1000080c8180c03075481c101080890b02030f80c180c10007481ca02c20144402c00c08d092040d9030304402c481b07620007110300c070078804401402000094031724422a030101c0d00c2e00303042150500c400615207200281c0b04d00b00c4294005848d8041d90824004140c0f1103401000c003142d8001c424940c0b070011a41c44000d540c5a00420742d11a403007003502d10985003903804c2c5603030f00c0b420140d00460603070081c504004162924031a000d0400c001405500946 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 565846088 1250 565844838 565844861
    0x7060c02070812120a2d051b0301030b010e041b0b19080609010b1602090c0702030105070c05070b0f0c010c021e011404060506150a0504140a06120e10 66
    0x40601c58684540c05080c034070900d4032414115400c11001000003110610590003181181c03001549030a500941401200ca014400002c007508005849031100280d0017284211800d413940110454094004c444520003400001c110790100e2005100c1d9402d003082c11540720744650118000903109a844202c07a0116500516440e0000614080013800328a1000980d0145040201c03c1d410100c0c00034215840500404204801c04100f03044090100c19101001903000350180845061040301070310b0f268051176040e4025030900010400a61054001c00705c0950094060b26400c0d0501889951a41c4002040c441003101448400d00a607420720501c00c1e070008540082051000888015240c603850040c40c0156924003c489000046888072182d4080d511610005650f690440013a00c250020100301c84180b40c0030440300c4019400c4130080c010345007001c1c0040881c8580c1410401e40302e00600650000914002c201403c541706604154403840b00601a142507020380c0c070b03000c0e0850701d24100d003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 565847338 1250 565846088 565846093
    0xd0902150c071805250203160606050a0b03010b04090906060302091608091216020604030b010e04050c0d170c07050603070f14190f03111602030105061207170307060c02 74
    0x4021407010341480c0d000340300d0081020b00c068501100c00071500d040d241105c016603a8010440b50503240b00340211507650010044900034691641000c07001084280906801010300c40004514850014140c9040b0341d400000a842d19050022030405010008401c44185498510100050340c81d40d03015881280300340800082280c1e515001441810060107401490301300d0f46001ca6a48a628225850324200d040c01003a140210320100c1c02a1041d540302900000d290303400404e81003061518140150b001d2000c6030024070f1108100320700314000200007000301c44100705910000c0e10040141c244541c18100b960f0100781d88402282c00d03507004450500001d000040040003503a008804a9031004c0c0020410f0700f0304225420040484038619001d40c14000c8401d1903090780d0b40309402101d40c41c503400c4d11075a160f205805210a0101121608a21a500302000a1300c942041044114042d003101c0c02007205518088100d00219200c0c04001c46a000801458000c20402d021300c0c035440c03105500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 565848588 1250 565847338 565847353
    0x1203040605060d020f240a020c1f020d211a0a0801150302041d0f030910020318060d020717031501022407210b090604020408030d0902150c 61
    0x40c14001c40314010011441403031100c0642c0c0150301d400e0031170090260b080c1d890541c10000442540d400301a070a007610405400010300b0003d030303170380070607043c5c140002074400490107a210001008034610b20190540160f00c6400848982889208528580c0104a0003030f59102190142103064070718800d50081d41e107500d2451220242001140c5c1001070003000020480c803101c04a14088c42c6506100c041c1c421521406200d04900401200c0c0c003400240c182190b8030048201300e903036284d0b00082c1c1414480c804040f01411100d00100c100e402c07501440051910f0440240304000340b0350007038100c1468207035003808110300040407695032400c100500000e0940700e141903e280109400b04800050464000002d944120852017450041c1610321071014540c5649450085500007540c80007044000c00340820707408807007465802040313103200565104d0350303d40d03414091100381c0c400c900c5400c005500400008444030401c1d40000c08891001740b48500b40000f00c00326440903003040d00e41c14555001b404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 565849838 1250 565848588 565848593
    0x303021b04140f0f130f06020903011b020d02071a0712141201031e0305030f131e03020d03051003110411040e0108010606020a0c0e06010903050d17011a0304080a11120304 75
    0x11a0344004c015500711070034140c1b0303503440e5000017140100418242d00420078442039942074000c458a0a045002c500c4014080b4030025a03c45484600b44054040e802000c12012010158001041c0100c2011031910002e43d80700c98210700008080d10400215440104600b00003000408500528000203502035041d801c05d0354400749001c201034091124484460f002a0b04042075907440201d0035400c03180c551711324036219800c210f0141c00400c1241d0340919101c45c03c000d0300c0803500290095003190a1191400300131b42c2100c0c1c0607030320540b0b80380000800b000014807503000c4000c080b07400703040420440c0c1800d41c2e0391069081074200400c048914001400a40743c00d01c500c000030003c42c4001d00c0700c5141078541c1d261015060154281c1c4c0c109240c0010220790040690700300941e881f00448005c01c110880003000300c003c0000398850412500000120540700405d0300f0000002240c4880c82c40e140c564880e1202d601c01c00c80f0328248000006c142e54488014420754480011040c4480e41c0da00c3d2a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 565851088 1250 565849838 565849861
    0x6010f0e031f0b120705090601050705070e010905070f03110306130b03240f040b060d0809100e030c0a080601140a0b1305040b01030e07090b010c060f09031403010303021b04140f 78
    0x2813907030303981c0310007420005503540c1c484064100500703007011551104641000da040c0b485030b41008a01c1905600001030000c0c159115074441c994554406165102c8404210300f80d4a0b9080800900700c010b0001c998180750120800d04000f5050000240303160408011a04140d0504203044409591803004031043c1c009516040e0301016160501e003040c80c0c0303a41d9581c120900544070501820b03600f1030103810808030804403590f01800800c011080d901150004141c010966645030290107440200b0750f0358141038401800307948608018001581c207003580c0beaa0714000314040c9031b20089601c4000741c1c1c600c070340006120400302e0701d0110310703081d08060a20050b0360fa00303801181014a0001c20405460300030600c8000e03682c0341d280200c0c89616a10048901556402000e0103152510304006501e490f540d206102036071094480803c0c0600300b040250690100b4880900940c0201c0d6008801c4060a144507801c024000d000007490450b02c405641c800004803180d0b401e124422041c0a000c0d40c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 565852338 1250 565851088 565851109
    0xc03020c0a12021c09060309060b19050a0b0403030507020f0d0f06021215061803160e04020306060f1c08040f03080a110d05040605180d0804140906010f0e031f0b 71
    0x90300e030141d030000c505980060985e4000e01ca400100759070f502c0d09508100301900000c030005030060003180c0010700f600500710310480910601c0c0c441c6000c0440010000300103c00e4404980e00340e01c810341881c1701c3d9028800c0301c1c0f0104030000c1c0d110b02441d0300100010548141708803d030b4002c0e80e0068a80d6841220400807900162220200c075810281040582c2c1c2c44504031110b150341312b207200802d55014004249407250380051682201850000415100307130403005584114000c80840d02107848072014402c01c1440580415000f8000710188140340302602030303a005492149040519043d900c1c131440c10b08140d83d0704115410300c4002014085a50300410751103500c0e2620010301441c4c80d4105000d41184560b100b09010301c040412208821052401100780801010340a040c8071a035904c0e208103e94800d000c0d25050f00305003100d014180c2009441035204130010f85420480350404801a0b404104038a0210b5152050030f040540c00818076052024030701e00c074440800d8028080b020041d15160 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 565853588 1250 565852338 565852363
    0x403021c050a12270902071403031e0c041a071a04080918190c050f190f030905060609130f0c05030d0804050304120510061d01050f030c040c03020c0a1202 68
    0x5401048010a003070201e120005c5500000005a4500d5145856107551404c050b00c19000d00010082000c03102080103100c98400401c001200941d0303400700841101e001343d00030306030005e40c030b0000e10703202c10103100003001d406005111a20380c134402000f0703060b030759801141c08580401e008580594281070200c0380c20507003542c0d10561003003841c2209180d50ba90140109d500d00c519101c19002203114040c800f00e90009000815141d5211210851301c4200a40c24460500164150782c10074126480391086a070102d034803a02804041d240c900c2000000712001c0c001141c0781c00300c1c41000c000540320070591468035106010110409240900b01820445520b9003181441a1b80c1304000004030040126003c0d5401d042e2002c0326140c150401070325020b15902040c210340d14080340400c0c0d918001044400381d01000381c1c10500c80c0e80340c00901090b2280c101c2c0b00d54169000c2202c01c0d8603854642c10161900000b40350040c14100c06c0d88582c1c0c40c21424160603501001000000a00c080c0d050102c0000c0b081c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 565854838 1250 565853588 565853627
    0x7050a1b08192009090102030f070c11040b04020d050a050a06060212091c080307050301150309080711040f0915050f1003080903011b0816080c0403021c050a12 70
    0x551408000b852105074800c02009000c45041e05a81e01520f0310905150640107442d80c4528a40800698005e40c01621a9880c2c4914500001c0e1582c0c85001c190ba0a03d5206c040e001082d51000c0c00e10014004288100c0e070302035000c1c003010703068060a215940c8035841215011900341041450181221800d40006c4210342203010b0008600342100212896040150f4550760f410a85100101200d003070840001e102d04000810300070803a47c00710107141030310000c1e90b41700c4459100030f80a400312a0f0450005182d0300c000c0c42510082032900300040002d4101030004101a010400c15008a5040308001c607944104491841c440d50070502c12250b000c11a40c0a6066034100640c002d00d010032030340302c000e2000d040001c500c860754500b9000714000c0d4000040c520301030b580c1c0c00406840c0c4e00003140c00d0003c2070000e07540524040d00c2007072914018003a00180310700d81421a000c1c803d01d4100c80074810740c42c04012607414005042000303426440b0740200480800440342c0b440060610074002c0c02c080c2da11 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 565856088 1250 565854838 565854853
    0x1203020a061109240d05040f050601051f030b010207080106090e010b041503170702030303010e0f070f09060c020a030b040602120108010608101e0c020606040c0504082107050a1b08 79
    0x58840e2040050300240b01d241d00d0000f13200310044141580f14003203103611000d0a0400b40701c204403c42c00c0300d0444501c102c0583d40c65071789800038003080c00d40c11480c0e456404d0131030034071501540c000d50251401c00010710594407410f0311881071a0944e22039900558a050350340310345041042c002c0c0300300090914201ea091008074848200041d0b0155540000b074044103e49003000c04d00b500034800c0307604960380602501d80325070b5601d070307810300200040300e00000405200d40019030291044ea5a041c1c0b846c841d80b101d514450514104968020444c00200d13005180303100080081401b01c031541c0d21941c032031100540d0300c10031040d02e0804e5640603804410580c0c14202c0602c9444070100300e1122205014200044515068100b000c48181a8007521921490b1043d01c3c41c1302a800f14561344180f82c2558180081c1072840c1044641d80314903c107044650f0423240d0503403000e0100003d00e482101400d80720f1170034a01c0e542c8540b07007040d0714204100c41c072000602d07014004a01c0b848010004005400103004103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 565857338 1250 565856088 565856107
    0x11e0906030b120c0621010b03100b270303091801060e031c030203061f0c030201051e0c07081b030403020301060b1603030b060c0f03030f1f030308040602041203020a0611 75
    0x150001e8074140c610440d03002c2940e0380d5007590402006450586c0750aa882035581d50307981d500b9240e0041c1d411024000b06210b0110704032440742e084458104909605180282002d0070101c001e180740144c00d9810b010030070101d041c45c0d035540000030403e40f560480383c0d0f00e549071640107072071141040c01483c001d402c5083d1214882a4558010000c01301d03904000d65207030340354030000d00312450400e242c00500c43c00240f40f54401c0e50100e80c3d20942c0c2d1007038008102c0e035140d4200c000001c8c100c0e030b005580c0784400b440001f802219800094001184116980c9007801d00808048400c420390405241c407a5202080c00c1095140901568000340226100341b4a40f5138031802003041444154000340a140e240c200140c05600ea40341200d00c5c0c089694161f51841c20b2010005450754000d544100c000c81070032000ca520508181e903010041c40d060049411054a15501580c070680001c0081ea40141e0070312000a401d030002010843c114805e03405801015540d10b00711040b00c0d008002d4101250090204051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 565858588 1250 565857338 565857343
    0xf010c05030a031107060606050304060f29192709080d0b01121503060e1605270c120907080309010c06020409020703030b12060c0a0e011e0906030b12 66
    0x50305040f0b00d03012807440c01200344804603106a080050845e0b00e0b20390f001400ca544400a14041c920840e0140401300c18100c40c401512090340f400011604408102013500841040e440341030080688201b4210003140410076030301e032656200b00c111341d4804410150780e21b400030b40c07180518038210782040084041d88450600c0c0c02054104802d00790b40300d2581c10389a0042d0442c5004015091041c0080c0208424129011845200c103d416a0604c511680c00820104013050800040c45000e68070302d00c3e140400000700c1800701203103040305205400500d0b1135a0604414452213401d41040c1d5120039500001c2d1103001c0041c18606541c200a07002d004142c8080201c40c031080c0300340703410b66070520395080c1103000b4859548510112440020316404040e0550044125400101c802801e01c000c05125280c0300e50b011214180d0010003000107680b914001e008180a2940614180078040030f43c00340b508107034407000313092000300d007060717004000c3c20f58035016080625109807003110405614509555 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 565859838 1250 565858588 565858597
    0xc0f06020f011e05040f0f061d0304051e0a12050325030f12060e0a0603060b0909070e0a1d063903072a05060106050301050619090519050f010c0503 65
    0x880c0c260312240485c042c03000300b40c100c8401c190811303151580c601440c07504400902116000d88096403502400c0a0104808000d4030102c40c0040c0c54000c241016024a4000c11203c0458a0b4048200d501c00700b15000402e107454540d81c850802190394001010440c6507041400f09904004148602c5a10000c2e50040060080d902365003070010411403010f5440010b021580c200c02c14801c030300010040b00c01c0c210b0b00800112401100c0400c001c010b642c051015070301044903640010303400b282c01040181e58040c00b040d440010f6000024402c0c14540c02200c00c100ca0010001c200c0d40081b044c0400c100705030f6040501c113481c00c3d04581196004007082d404808142c942e1141e01000800002c80381402805501d03030190b40701c01000d01c0110740c103400500003003100c0340540f5184224400401c0003070060081340c1c1030311130045c011820940c45140d02901c02841d000750000700001700c000045c0c2e41e1903030450341c3c8400c00c000d43e2090000d4104418010b841d0070109503030341001248107404010580c0802140c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 565861088 1250 565859838 565859891
    0xf090b03060d200d030801051c0b18010605090a090c081f09050f06040c0e01151d0415090905010b0f0906131506030615031e02160c0f06020f01 63
    0x3c221980109002d440846400f0340d48135000365003480b11008041d0300c58942c80c1a07a00440310f001c0d03900103903401e50800c01c1d85035600034801d01d10100414806082d4040801c5039404070b800201d52141c6800200b80342c0481642c00ca4001501c0c3c038000c0c01000340240030741014100c0f2a0041403003100303c404a0700b505140c10410070f100d80d52450700e002440000c1c400b40c102e0480080803070748181458600200ca03040390f8451500c0f1410b40c1c40000c52013003803203a1507001034520765a41101400c50075844a5001c030302402c406038020ba8507071400c1c100b10800f00c2160000c15142030002a1a866402c0090943e03a00b11210783c845c01c0d02c100c0c98482d90751500341d00e54000b03600765600450221008600e00c002d00c944420503181089142e00012860380c9a00039809039004005400800700410b002a01941e0000d0001140c80e810312804010f00c000581c050038500b007400c80620310410140e21800c181e0615901300c15a140442178040c01404d80400c1072202038240c010003005540ca6458014603003142c143c071803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 565862338 1250 565861088 565861103
    0x11209110f040204080f0f1905070506030a021908010801110c0a0303090c0306060306090c0e060a0614120c1801140d050a0e0118030201060605040f090522030f090b03060d 75
    0x81640ea1243c0d0305590240c02082c00302d4503900808041c041d510a10140b201f10703148100800c240406140704210034010340d100d001899014108820070845420052a0060441e0301740404804015a03001200c0114400d03142c4021950400c10714a0035100e0445110a04000800540d0301010b00001c03146082a00b40c40c0000d810241c070315003181b0b990fa007a4800b0b007a044c2051004810301a4590090709070740d210306089050b00f0b5507840d070400345c408103d481d140c0c070400300181001142d0065440d40c0626020150087c40c0c40503600000080703000907135605901007004100c41155815400d00e41b0825002400c01c1a01080d035180c5076400342c880d10110750101ca40351000f14200c400c09401400140d14400000e00c508002c441d45000c002841c440b044c1c00540c00c200340082c041c1d005100721415203450900c0e0252040c280a259005498041c04501900165005403101400e80206a4400358404d07950000d99143c0380030001c000b078001e0b810a13524003904006200d61680c507807100d07404456001c01d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 565863588 1250 565862338 565862359
    0x408070609061e0c1b03020c1002010b1903030f0c020f1216060203040e191b05031501081b220605030a06051c030e030115090f1d060f1003020d030e01120911 69
    0x1b030880c00c0c0b035004810a41c10100e01e94484100503010341142c1d404801c1601c4860440640080c414540c1d2000d20019003c03a0f2042c9694207080d05c01c8a20f0103003140050f0183c0b50041115012841010700c0c1c10f504400e0b41c00c20148032405108140c05d110003400035100450500b03051440c15008040007410710003000301142040e0440e0045c0341c01151000b508041c540c64403464242d03018081e680101c50107000c00d80d05990424075903000e1000203024043c80350581080c1c04030342090740c209600901580303d1803114000c2400c01c143c00320761301030082e200641d9095182d003041029041030307480b5500114459902941c4d82c5440d04502249540b900b60107203031042034000d030900401c0c0102000c7c8203007040d0040040c03011030104403135041940180d031140001c10030303100741100340e804804441c10052240e0304408040b0381d02420310700d00c1c1e41d08000034981100700c00c3d9a0340c3c000f0380608030401040300802c90f00311b6403400642c0c1002c1001019107604005016602140c0e54080c2c0701c1c098161418826024000b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 565864838 1250 565863588 565863593
    0x15010f021203070507050d020607050a0e030304150c030207092a050c2b03050402151e0304060c0f050702151e04080312010515040b030408070609061e0c1b 68
    0x30200844a461008207a503d08040c0d40c010301d150f000c10340903500c41c425107882d90030079440014047d103d040360395561800d15140480441c1c0c40040d608143e0360511050002164400c425482d00f000101da9490b9070070600c1c1e1524020341403461961000031030a20f0419403075486108c0c850b1a00461004e03490720780111740c042c14107a60071b000e100110799441c490120307c045d11901c0b42a0900e0403200503041841966507079101203007a140100c800a422803400a4001101c0c81c03641c014003084030710342d02202d407100b4101a0550749074004940942d103075500c540c0702031509074020300d101b600d0948514180340750034480d401092700b641892404080c12100046e109070406041501c52512898910b02c40342d0303071961081c032a6500d800c901e0b007481d2200003020001680b40f5000c801455031144042000341480e00c2c180f62258241c00040007039030054020412400041c50790700c12001102d01c01e000c00030714200b44400361000c0c44107a40180045a01c0c12404900c016080085500c60020008000e900702c0704030b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 565866088 1250 565864838 565864843
    0x1104180e0f0d120f05090a05012d020d060506120103060b0f030319140a0908010b040203090a140c060d15060509030a020f060408060702060a0c0207140d0204060513020c1515010f02 79
    0x31031006885601c0c0c08103002c86e10310082400709000f80680020f104004140c0c918546204a1401440c49906803080041142140d41c010b89140144c10380e00040e01d42d039950200c2c220368000d0107080046605140140200039240c4601c49113a20141c2d2500404030607a00440d90341e00c01c80046400f0110501074103000c0e02e110301e215181d120309442d451a110803400343d01810702881c070300650402c2c0d42071545050241c03c02d40b0a0324861080c03800105690070240e112103420001e40310704501c660040b8400d002490301c4c1c040c02010085840f81c8000b40300fa28031002140100e40d41d800020801c10204480c044950f00043c80210f5241c0440c0c104003091390b00c1c0c000aa1604c03550744002414010b5a0802a20a0700411803d12130428140c3c00d200700200c28004a0311407a00d07014252011641ca071245615080c42c074190302010744090000146291150b00141c04070150440181c0c240390001004603840e002800141f40c02203001a101c55642040607060f01c0c88100d0b50005410019101151005140708 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 565867338 1250 565866088 565866101
    0x3170a05091315080102090901080a050d110f0a031e0201090209010513180606081908030a0509010e0f010608070501080103050a020402070f0c0e041e03170a1104180e0f0d12 76
    0x1c24030345144013550303040218081c2d040000d15900c150502c400004d12000042008107055901c10301600d40344855800690f000d4849a11500581c85144072810f03800b901004501e1025009466402c040b07445154102000825810032030110790410740c40070010b841c0c2c4448941906c0049684011820580c0e2421000f8104e0502e44140c45d05841c00b03210174040d4581c001002d81e40244c0c2034503411402719007284c120080818008050031802c20020f0719115250f40b1403900444000004100303440e5141c035403464110020351004d142e95486e4000c2241c1e8208000020080400703081070700d01503141d5201d1503100da0603160064025500080e840c002c101003031005413a6507510022a0400c16199480e800200c3e0301194210f4954050015112228201c00000b4413003a51598a1307148120311803000142564000e000c0b072840f1a141c0d000f1010411b0500040e0020b000c8107907041c159241008020340507916065546c54403a0404210400d40e05004114602000003034100312000b04441e08549000300003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 565868588 1250 565867338 565867361
    0xb15100f02030915041e030807080d240f080111041503020f070f1502090325050402071a150105040e0705120f06180721020c061003170a050913 63
    0x7003214554140c4c0c1c0d510140c0305a03055040043e00704003120003042c5003a0040d020160440038240104d000065201008014030b07d45010007041ca110380007028500c8542d00c407425803040c0c60808041c00001c8811908800a0810900038004403d039015118124452030280441c1640c1c618511843d16019804860302401003000c036030f98a4400d401c2150001d010003400703d402c41c88500508000b54101d000b0307241d4a03540107010305044601c40c00302180900c03c00140342842c5004040002e0f065466101030028203000701c0d08941d40004840c1015040c4900625a80c04101c1c120321140c0780e641d0040545060b155140200c10894440310420303110b0740104040c1240088401041040c600707400180203000b05003c2d80c1c07914032601c0c0544c481043c1401180c2002c00110040100000c0d03d9000110710f00c5a01e0356000140380c520340584031400d100003211840b100030b944400810400210480050400c00c0c4180c2141c00c0407040d4000411900c150640644900350b452055140c0c80001d82c0301558480 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 565869838 1250 565868588 565868599
    0xa03020d0e1c081609170f2a031203011e05100906032009040207080d020307022503030203030621010603060c1d0f0d0c0e10030b15100f020309 63
    0x780e02c0c100150403050074001d8034000030a620f0218035440d413041e5030b0108900300768441001040c00c03c0001c2e405075400400100f07841c4a00c650001d001d1409000103544411000c40c20072105540e0301c4c1400c0544150b04580d8060703801880b540602100d9941a607041d00c04141c2c0c0d403204410383c541d0041c0b481c0040e0704007540c8100b2079840b01c6542c0d6004405d4004031440c90311b06114450030042070606035240b07040384a40d425010421490b2600d003d5000303202aa1098060b6410a040141c0c0c1c08100e810458458015902501c0300b196041c140c1c12844001c2629145684141419950003c4d224000a000280107a14a0390302e11007a021040d80c1c04401c49000000308080c0d0340e00e042000103414040d98043c045250360813094540348084c0424015075202070814164040580c0500015541c49641903a000b80c0d0404081041b95400008074090030f03003100c14103441c90a60610105048020740a12042c55407045015281d864840e48003904201c1070400b00329000548405074110310601a540d903011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 565871088 1250 565869838 565869853
    0x601020a1205030a05010918021c0f0501022104050a0f030c05060702010f0e071d0c130b03070e0406080d0f02030408070b130801050402010c08030c040b0301080c240a03020d0e 77
    0x1141e100700990310031607011800380720599850702100112a92340c0c100c0b11044009003400005820a00c0c401014059000115650000780387c075102c19100303510f00c0803551a500011500300b0590b128040142c1c1907030030700c0d01d540f060400e982e0b0310b9a100b4906400608400304942400c3c1454010b85007005000e4210081c1c071682d28040348001c2c024030310b040c4203070903040c40c005a0000304c100000f0347d4410354801c4101007896010030205000c40f030b0f03002444e840c2c84907002c0282e0b01c0071401400341e40000b00311404e04142c5a040c4060040c04003680300c400e003401342c0c0c6040070810014100165090a40c500e80c109142007614440e8101d0451240d900158158032031210002110020113004014101038010050031a64031a01d2050a07154285c0300a40000d00c8050842c01040d1680300441c1c00c6444003110703e2819039508500421500240d01c04005078000006080725802c0c42146c640c00700b0b0083c00380108481c01407511180300d00400b1020400c2640c089094407011145d0b41c041d42c04101c074201107030600d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 565872338 1250 565871088 565871123
    0xb040f090c0b030601090e0c04121208071715040e0115030b0c0c1c050c10141b030a1a0918070b0a200c040c11070e01080d080601020a 59
    0x500400102100d00c040001e0000520030a814280c90049405075aa030401c0d51503e40c0c01035240d038010f000406403040030080080c003481c1c00d1119121842c810900c0032071501e42c1690180c840c0c10000c090406129a54036400b240905810304d05520605c2030700c1c488100c14203080498010190040b0300401984cc10b1a101e110300d6058816404480c403602c02c0c0000380d07683c801045283e00850440442c42c2d4030140c10f2404d1b6003601d11540f80a2001d91400b00e08211880303168900d421030304103440c840503681d400e0107042301c2e032030071042d6500414401d000c10400072800b0b08000241b000030701401c00c11365a5a140704484000d03601c88401c80e040140b40940a0520030302510722106010345023161803042440004842c0c0d100c6003503681404058540781055007110309811280b1058880c03c14403402024490002507030b80e07104200c00c0000350380e9a480c01009240c161450700c1c1440e0406800c20002000400035031400040650b415152031910843c3c903107980006034540404031800500e21010301c0c180002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 565873588 1250 565872338 565872341
    0x8070c0606030b060324040209040302240a180b011e1d0612061510260105040606090302090a180818040507030501061707020c060d150504060509011502010b040f 71
    0x5404c0c100c0644165003068021100070b180001308070b01514517082e0000340546044e400b2580e0150203401602d1070f20109000110b00c814290705400e002150040a2207c58481407044018400c0384040c10078804150740c40340608800148103c0d8100401d840c10780540c1036025110f04010121a000b40e00303407420b210203060404004442c070500880c03100a40c68403141c00001c055000d038066200348014401c070344040c0020b40803110301040a0040c104840071ba842501ca902e405d520580007905840d550400080009071156603005401300443c400e414005680c0f440070544d046211800f00289910310343c0c00115100d041c402e809400c680c1c02285440703411600d1010016188400c4500304515514401c0503401c44d00213006001c0050383c5800076501d00313203560748c0164201000380100c52030314090340002a20f541c411020300c04050749803020074840303000b030202c15405400c04072b40a00110b03062401203881f0010501ca0300e620218000c8040300342c0d82c003c1d401440070080c0500284080503100c4000c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 565874838 1250 565873588 565873591
    0x70b0d05010302030c09060d060b01140c1f0507050a080402030c100825050a052a0c04050c090f01051c14190e0303310f03090e040206070308070c0606030b 68
    0xb8085c0c02050b0441140c0c0c0b810525403071140d04010040c0504c0010350b1120401000c1084036035050180c2d801031000c620100502403c040d0071250000c0500b503c500f41e0400f0020091104002100e08017420300120640000503604008014a040d81950b602c0d4000240b0388041070b000c3c02e0f080362034900142c040c80e40c8440c5186c401c4400e690089504180122501000c07140082624001003091003c2d0480d14410002400485c01d060300c000352417000d6110507080780b80701039100c54107603001c414944514109800f400394401c1c1e2400d4414104140103000c038000d00850081c1604100e03001490250a0020300e0144485602040c0100910300d8006105200420203440500304084200c0d0801c40184403402211816070001001e54219240d9051140c0d6200e0084c4100340401420310195405426071000c0c030700c005000f000c00700c0752001c00707060107000700310583c1107807080d04559001c110160321100d048860255052804c18040e599801c01242c0410215000818441c1024400818000103900c1c030b9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 565876088 1250 565874838 565874843
    0xa180b0901060e010f0f030f020f09160f09140904150e0309010e0f240405120a12020708030307140906030718050414150102010b06032d090a1202070b0d050103 70
    0x6040f903620707400480000041881034514011070280107100040c02503006403c0d1a201a094056604034000005c81c20f03141100d41007102550140d400300e40030ba002420304020103460501944a6090461100442000007032180c040c0048802041c1000001100200c07803503a0584104030f61403100c032505480b503100c000e00a0024840c030740183d8462601c6200144d10410040c514130f4a404036460300c14440343e440c107040403800c1003400002401d4550b8040002c94400312030160812801c1840d1659171221081000d0b011540460414007409000004480d0403000c141809401150503001c09036051040d40348090b00a100803003440b082c190006480401c0d002042e5420f079034a0340780c9060008503407190603185082010f10002c02c403183c188502c01259420b041c800800c0b02d490120105419610644410024648207055440c9591170080c11100c08500360049501c50304182004070b80da48030604024140c100300410290645008020a100a0100340303020742d02d400402c499500101400d1205 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 565877338 1250 565876088 565876109
    0x1090203060714031816030b0417030609040836100203132306120a0f0c0c1b0e010b1309050403020d21050103120e0103140a180b090106 60
    0x414201070286004150f520085010641559603440c0c07940d0302030000c2550328000c0d0040000c2c414444040182d040c01441c0120003851080c1458903108030625440b10b150301003203005009209841d41d0b07042d01240c10a82240d98991a0001c11440c41080001d204188010841c25030710b035800200c440c0b00c040e600b01001c03030310390320b40811003d000e0703841744500070a6800402c25404c091060305410707010040c0d00769586000f030461102010107c0d02550200500301191107501c410892904070300e008500000b11001c02c10b1100ca04541c1d0041c000c030300c003a00d00415000c0400705640c54440c0d004051001070411a05228903540d59000c0440300394052400c07030b00b908507101000704060030b113070140c18040c5501d0b60090902c0036030000e0484203241c0c2c1034540351407224013880060016015008a9011318000c00c0203811524950710701800c18001800600d042c035041281c040c0011a04080300c036485030040700081495020a0f2445441442c42480280103540c12003c2c00580d60701544a8001d0300c4000e4103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 565878588 1250 565877338 565877341
    0x170a05090d0801050f011412270304060f0c02041401030303020c21070303023601122a020c0306090f16030b04061109060d0b0103230a2307020109020306 67
    0x7007190b441c4024011035030030046101400816502c51815041000303c01e07111241002c01c02c4a201204d00d03402e5881c2200345200c40c03060340700900c8180000301c2182d40d0800031440c1a1074010041c0c503081c4001110345c140f01c0d41d00c117640255180d40d080b003c00c114990314000759542e100d240c00340c020b4004010860303880c070034119445401c840450704982c051030303850142400d040a666044020b5409031003041603e40001c680314481c1c074203c0040345000032249141840c880700170400149080d410a203400b8445050034a051000310b41808a40080d02032682000000040500c0c240d180802e04421150988506c20800c4401d0741d0104030b040701303986040c0640c0e40c0100d02118160f014251808050710550084002c100040c0d041e0380040040d14a50404038105002a00080c21542050441103a15521120721125139030b450f10405601c5001d030001d4600c002100143e007602a60010540480c0642e10b5a2401d945081e02402d80c50400e80d003240c8210524142500901800e02410100d010340300d80300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 565879838 1250 565878588 565878613
    0xb04110409031e11070b0d05070e1f050405060f0301150306031e0f240507020115060e030a02040203010f060e030c0922080a0e120f0c010c03170a0509 66
    0x401d4411a0107549850b6112420204201e680007154501428031a4982904180c8141031004600030007440b81c1607500e94aa881c0383c2c03016640000c2a5108100740c400088015580d1034012500b4400d84c407020401e8420110307020740700c600c00c40e0003030795114070081030301100749490714010b60507600d030082a400c0c0a00984c2041e8252011030100410340482c68491210503008000c05144140c0201c0c8a0740010b5482d0b141c6d2215030f8001c865440f03003a064003010201091480c0240c9812010902c001c200546108a582c80480e0480c01020f040004003000c1d00c2c0c165600300664503542c0d400074400c640d6542d4035031044500589a00c140740125502d50f0342600d041c0ba01007800860010040d01c803c02c03d0b521005108008240c101079002c0d503c8c05407907854041041c503800b0b405080c4007a156010001e012a041007001310142d11710b2641d55110380300406840300003040004201d602802d1400440d2a076103000e45841291031460300c0010710b41c00801c030240350396800841c09201010140c443e00c03002c1c0e8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 565881088 1250 565879838 565879841
    0x4080705040c05041701180b22120507060f05010605090a140a141c120311070215090a180213090e060402060901050c060906060a1e29070b041104 64
    0x2d291203010030f0007444100002102c0c02d500f00c2c2840500d40002520740010b081c5880555038200040c0c07420000341c000c0000b4006d111482081c259110040031480005903036071000080c0340c00c0e244004000700400d10000700002600210381031603c006040c809582c4802c0c00070a5a000341c2d50042c401c1b0b106040009011041c512400f508140161030b094840f401c12095003410005245d45a80006080c0c41c8900850b003142c514010861041c0140ca40d1078000b50310050a85003d800c6501190904108150060380c400c540c07a0206042c4080c2d964850304048002007036070290798008540e18094007248440b280d0994000e000c5540e04503d401d88035621002c444044840d152412207042d400580403070f000d403821802030302c5d60392414541540b405812003080c60602100381d0360190203030321210500c0306c00d00c1c0c03109400c0301429840c0840e41c106035a00c0d6406004d072030a8855010301a03000a441000400b07042c500c1c01040750f046c0085079903031040d46001d03a80c01e60100c50554040d6400b04009070f891405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 565882338 1250 565881088 565881101
    0xa0e0a060b12011a0c060721020427111c05070f0f0804051626190f0503070c030b06010e010201060602070905190504050a060b01090e1302240408070504 67
    0x7200b10760031940e0a01c1602d88442030b00c1d4100c200c2ca00c0c018408600c140c1420040305214054640d1410070050030b084095031400b64000c4031481c07481c0103005c28041140c2003440c51940d000c265103551007149034a880c4034001c02108000d00310b10040021800c0c144840c8180608450349420002c00207070747c504604980051001c0c64000001d40c001e4444022248203a4003250020302400c244c8032102c1910f91507284000c200c1c4e102041000304074401401c1064080c0038100680c1d1044040d11011b039031040d844c441001020002800d64030003854280511204005031488541d028000368081a04c905000c020501d089519074000781e21216516165407042c041d0704115007842c2c0007040c541c0c2c144090342019200060020005c45009032420510b0304141c00307110300403801800038117803520f02403c1400c280e800e1081c41906201c0210010800c50502c004440d40c4411482039004070400c0301d00c0000e100304202c1c0c03d51084489108040c9202940143c010412a55400204e41c0602d80d120140000e80c0c09 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 565883588 1250 565882338 565882357
    0x2041b120501150c21020a0c08010b06090d0c0515180f100f021c0305040308010609030804260f0607120614060f19090f21030e010e0a0e0a060b 63
    0x5011683d059060050040c40061072090108000d100c00c4914541c03480443c4451040050344100c04d400203200389504058007421071100203114084a11012800600c54085014042c800d040da030481030109420341e480240c0700040c0042940ea07003a850104850b00a0210002400d5020410120f142f4003174106140c6e03401d02801c1034411204c100f07000d54000038400038103801d43c015501220380040600c10401101002900c0010b02410721341001411840140c00480901a44800500103d20b424041c0e404484004c03c2e4000b0303d10482200c0111316410080c0d28050344518891180f0400c0c0200e41d842c45960a0394544802840025203242a40d41d030307120b103540c40004200c0500c4c840c10b02100500a10a004407001d103070150344c805c0300c02401c00c0c49807040e0002d460301d04140190b041c0c0380e40e13090042024080841102c4141c10105401801040d401001e03c1008510100c4a90154419a022150060034045920380c0e82545101c5042e04807126007006280050114444003c0c8040d90031201 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 565884838 1250 565883588 565883609
    0x14030a03020d050c01060e0f0f060a0b0d0b1503090a0302060604090305032d0708152d01090807060509090c040e13051f020a020d0201060b1608040302041b120501 71
    0xc02d240d506a403268045034619400303548580303001c907190401500301c5014101c2c20703080c41100d00e01203a40304a104009890140f1909641c0000c204200c2c01c83c0941349a4440404006003040b149000506284103131a05244c140c07001204100c0d0200d004124905828040c0e000d440481d61400708020072141c03a180000d020841c14004035250070b0000301c20442c0c0040b2000c404000c96040384407525000400c60310340340000e480000304140030388044034448150304c041d605080e45d443e506030101c0b0740070401d07210002c0707040c10919400f045070f2242055100a10170a000d480c1c03102e840d200c2c02003403039014000c510b0083d0001c4021a0016452104807022600c0301d600c0750929440d0501805100c0070400c0040c1c9080c410100c0a400c1040840d8200b1403640d002c220060b038a2070000d80103410074080d00e204400b9a4900802040301c80c0700041264200c581c6c01c0d0715101a0100d03440c00d0201c0c0d015581001c0c0d0041d1034510140720a0100e071007590306814440d1603000355407400484d00c109031070b03003405442d0011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 565886088 1250 565884838 565884853
    0x90f0e0d02030412170c0616170402010c030503100f1503180203150c09030607091401022b020f010f05190203190902041d031308070b07020d080c010c0302030114030a0302 75
    0x19901040804a000b8142241340c0f800001b103800516000b0243c0d0040d07250f00b011200004420340055035245992486640c84d1250325058002800c0e002181c2d00140134050004009a1026040032a02c0302410307140307502443d10b9440340c03044038454900a582c0b030081791901ba00b080b19040951019070f405035005004080e0119800856040a0310240680140100c2030100c00d1066409110030f0f4415a10b55031072001c442e20b4800c03800b41100165414034195041048001c07410b0014014650300c80000f01405000707003604007422842c01d02c11500d0b08100d03500c0c001c044000501c450b01b105000c3d04400428114003031075455104101d102c04c0d502c0035000450b003041ca06000c541d40d0868041e035800204005010210440a041c1640c4406940c2e004e58000041c2110050701100c0300781d0182c25080020081c050401c5005c02c0326114070307007001c2d204038460042030040020810840b8603076080b000081c0720a18141791302034040c0d013080c0a134112074460340c0e00040c030703038140000c00348110390b055402040341 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 565887338 1250 565886088 565886093
    0x90e0415091a0a0b012601060f0e040203010b0d0608030a0c0209040f02091504050c0c060c0c03040b041205011a091b19020a0203010b0103050f1609090f0e0d02030412 73
    0x5080d5020111030303182d600c0d0034004180e000c1d40c0d2000c3c4a01d040c001d0110b030030b54158000501c17070700751004607050916649003021640c14115401d030381910b40d6814054209042c00100307466080c1c00e243c07034a034030900010011804001e01000740401020521081c0b20b0603440300d13a0b4076100d003e8030506d540003a81c40b001c108094a04805580d8000b40220031300c0422010310b801040004108071121604040480040b14040c24248505540704181804aa00f08110303085204d8803040043d00101d48a0f0000c90040c001301c03814421500100034800c49659526900e8102140002d18050305a0f1507500c0c0154040807074400c0c81c091003280303200401c0e000c516961080c44e030780307407228000d1140141001400301f40c2c00d060710050038010f200099001040c00c0c140c284100b60a444600c00911304041c1010300340002c200301d5046560304480c080b03400c01024240c0340341c12245158541e01c558106030900c1d51240d20f900b079a034010101829604141d9940c0340d410b01040c0da4910031441281c0644201c00c100101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 565888588 1250 565887338 565887341
    0xf0b1006140a1e111e03040b0904020f070302071703120115031103090304210f0305033601150b09010311070c260706051b0f060a0c090e0415 62
    0x60302d035194140400120030541c0c0c1d40341044070724401c0001107900314540e140c80300c400308000d02c94100140401d250b011161004552680141c0c130880301d45800110700c5040caa83c8907010b81300303410034110f845925806a41030095545000d13224065041590350500e04003a2808421110300072420300c0c14038001d03442d141d401d248140342d0b60442d0b02059a80c40222501200d05001180a504200002c5445600304282011346070680b804500564840d0103c000008a4850b105445d00f9010b0400700c9c2c83c1c4c2d44503c03169048a404c844c81484070703000742000310040040c00c0c80341840c1034801c8000b0001c0b00c8050323600c12122001c500820341c9400c0103008100e100e600c01d8100c40d000c1d20a05000b0741c100243c0c0d99a00c01c500030f540c1c100803101c200d0000075521103a4203100351581440c4020051000d03901e050f00150007403003420484d940c000904100030500c120100552010f00c0d503210111806440c0202541d0300602c850315040d00050303444200050101a030581503800340c2e82212600c110109031810850 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 565889838 1250 565888588 565888597
    0xc09010c051015081e0d08060a030c030c2d0e060a0306020d09020f0901030f020d0614130b061002060a020a02210c06010906120b091002070f0b100614 66
    0x140c1d40c2c8504940100711000a00440088420440300450031a0400d2100e5041c520030b100c0c4048015100e03c070050301602c0000d0541c0c407820300d038284443d558441c0408281d1400040d0005032a0b107007110f5001081004a04070b9000b2203c1c00300d030528017000780c0c0b9200160703a404042c2004200092801c00d00ca035164103014180c010100900428910b680d03503880d4010b03600020f4448009a503100c1802080d0f09145514040c2071000b19a0b1400940c155515580d6440425030040e000302c1d5442000800c02106074018140d0401e2884031020030710340448030f00f00d190489002119084403000c0480e4a504080620030740007681d54010300b0040d83d900c4d1240f0000d420142075603046119032907000300d402401c483e1082c0070103501c2481c1c03aa6408214102441e000b81a03008040f002d140800400c4103998403500f42400d10362102003098940c1300c094080e450031024040030340c0340500c0010410100700e10412800120351245160450a580d6050450825900c0d840b03000d0104504000c49018143d03d0030007003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 565891088 1250 565889838 565889843
    0x3070b09010e0a03020105040b070903030203030f070c08270a050a170c04050c0409051e04120c1e060506040c0e011808070b0d15180c05070807060617060c09010c 71
    0x103001030382e4141551500111010a40160750748100344414048080c90481d4403403403d05000e503c680c69550000d40c1e900c001060181031002a00c0414086840b4070880e41005400950031601c03a4803a400340c00c0c0a50220211188110007120341c2c80e414108400c21008135100100003a030f04614244c092028040d1450440400f400f070315030301c0e48140d079451180a0003140003d030b81b2611242080350340c40032260701800c0c80c00c2c2c2c210802c0180110301ca0b940202c130b9105078040803c206442c000d22090316515050760740104841c2c5500c2d07603010101c4248070380d0881d007801001d081c09a0344504003400202d60400c603118000070f0008581d210294081c40600c0030304461504808005665600d0403400c0c0521500700c84424500042c01480d04410390040c80a107100850012500d2450a5254031403981d8035682241110703280c0502c0036296016005030340c1d00301e03040b4030483c0c0d41d400d1a02e081d000501d13180c081c49140207414030759010140c0000925610443d901c80c503180c9042009001034030302d2007840d01c04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 565892338 1250 565891088 565891091
    0x60610052a0712050d0305090714010c0c0e1906050d020103021e0c0607030f0c0206012c04050a0b0702070f09050a090f20010e130515030a1505070903020303070b0901 73
    0x110078a6141004400d00808040084180f030b8a45031405a060240703000f20030040600300400e0140c00c07400807404504a803070782c0310701710007c0c540d050040c1d40440a969002d005c0304400c00c1300061040a0790242881041e00c41c003041d610850015280c0201e8515000c1c0030b030840d00c004e0b10382005500a138020300c5c0310340b41240f07071300840400d10009181651168028401503007242c400c1c031088031342502440360b15041e4841c0900c4580180840250b549205103e40d03003512a8100c040152004900000c016400f41d01c0c001c80c031145003e04050b940c640201070300b120790510541c0051182880132aa802c140d0b0401e13010100c0079072400b41000091715000d4030b164200c50369034180c0c5002600b020355201c0702078810b486001d110181000120741842e2150a25410b001040c111941d10b51703119414411072030007c210000302c98648424048001580c10200364242c411403210000f8032800c1c6080d0600340c82c80c404280180e64034410101c0c0c80150b2840300a4042c1e20610860000401009601d640100c81100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 565893588 1250 565892338 565892407
    0x60604150509070306030201090f0e0a05061f022109130c031404140106140d1401060f0f0e10030231050109020a021203040317070c0501050c0a0206061005 68
    0x80c10302c1c4003e56059020a964400c10811940c00c070003184014030b000c120b0300349124a40940300c0300d2034000800c105a00355441000a6507942e59003a800101408030251011390511a84042c3d9100035050741c1d443c00709642081100f2514421080310034a032000f5121043c0d0351000c80080d0064012040b14400b0305444000000341091079440c06889140107941145245000c402020708441c0300f1f400524001140802d8407005440d092000300c0002d0f80001c003a1032401c1100d044500400e92a0011145070114080018802c00f1144568003540c070504007480040c4ca40280080b00c81d03809100080d000504200b48180c9490a5208020a64840c4034501030083c02c00f00c4100858409070006034a15070301184d501c111607410010307000358a1a481856286007456140500030921240390011814000d000213100c240c400c4481051855000c4000c1c801030804002649040d085802050014840d0400040300352030240440541d208060301c1d0546401c064046010b00c041003400e109a200e03b0859 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 565894838 1250 565893588 565893599
    0x17130b0c12030c19020c03190c05040c0e031005090c09070519051c140112080403140604062a0e03010b06040801051e04080d090614090106030c050a0806060415 70
    0x5004601c6141c43c0d005056650480c090110041040408000c0442d840079552400d5624000f0b06404146c1301c6211000c1080700525241240c80c04c540c210707a412034204401c000380f00e034120320103c0203190110161074010104140050858008895216481d4800c4451010509180701070380d070081c1007443e00501d408148910080f2410407178911200190000440c00c008104888502e1040340d00880c0900070300880700580890120103000f02c049107250725403140200039500003103034000c45d8031100301c3c580d6090115072103450792411a02a40c0386070401c110741d644180c801c0c0507481444280403e569451003c0007086600301144000f0540544d61504800700340eaa070440a04001c2c03595174008a03c40c90311465066084904c08910040c100200c01484000b07501001522580703074666400007000501070500202400004101c880d19000d01d40c14811803a00640080042c0c038000d51070107184070340e140c05006400c0294802c60b40f2036081031002c9840752030075800c0307500d0240d00391886235612a29003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 565896088 1250 565894838 565894873
    0xf13021801051201020901090504020c010917040f0906061e020f150a0b0a060c08070816050604020a0b130509130b0c0a1803030c02010806120f0a17130b0c 68
    0x8803040c088106410004108500e0650707861140311680030025401d041c44000068203540741405100c2c03265802203a8015a070300e095205034112a00b05948500030b0001007542403c070b91150183d04075612090340e02142515440c001c0d101102c0655a0f100c1501d01147c201114038003c42d1034050850140c070200c0d4244820070050300d126203520440a0b041400c0140b170490850f507020001601400c0009404c20060b6004600e5410158200c20302503a250342c8d078980424140329034003041c101141664408414020001030f00341c0305510a070350f030640080e01c401c090703005802400c0068810141d591014021400d24450309034012141d07034490a10007205640d00601d80c8402c444200310b10b0b4011540c1c521a40e1b000103030f40e4413068184421440941191001002400a400003906015202c001f0880c0354440c00100b42111101c4815103840380c1071f03110f9003170301c0ea20f641101362203280310709a039405007111b243c0c103e40c00883d0b1920181210b500e080c0040800d60060000c9880502030320328001114801c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 565897338 1250 565896088 565896109
    0xf0306121e15020d0501120b010e0c041a04050306060a14041508030a020c090f1605160f03090620030304060c050d0906060f0b19031113030503070204060803120f1302 73
    0xba003001589030034103040020101c5005901484c00400c0e40c62005001c03658032103d00f0305540260101c00b80300e503200010900984682d501c00040c40a081c10f40095021004010744280d07142101a140c00d074a404082010b59042402030b00071846013056030490510307055002c00d40f0780100b0000891421b503210070075403d40c1c00441c401405600820210202461f010500f41d9010b0800c2c4401c0d0843d04000e001000c0a50b8072a4542c42803001c00210342c00300c60084100d00c08030990040d07400c3c0340c01c041c9140040c8400483d100d600c01156041029414003260b0400002056500b00011411550350b501c42a0190074121411000d103c0100209101082940150309901d80070b40c0001c10041c1c17400e4034144034030455911a00d09200d00303004402ea0380000b206507102c103468625000c500e21141580d000441e01c6018190303440d4205d1813100104200000c006001743d68004c40d0100000f95583c0132042d143e118480c407110200340c0040006a00a00f8103e0144e0800300c0f489442850030070941c041210303c0c01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 565898588 1250 565897338 565897373
    0x204050a020903010c0906020a02011b0206070c0e07050f250b13151122080304031419052a090103030206090c010519050c030d110a0f0306121e 63
    0x10006802c08203420240212200c5079103918001402030314011000391034000985000b0304010760030105a0844c114158150344050300100000e82c1c80305103241050b80101c4a01c5640d682d802c1c0c1d10001105180603074152800080c400c40031034602107400102e100105401c4455010008140c61400085000403075850310a10600c00006e4014440d03003070443c1009884514840c0d56818000202000b5a0240503201441c070031102014a1a800313281481d00c002094000b81c5142c0b00108000081c4030b0003040720103010042d6420364400318020602c1007040c20780c03101f02600681c02010308103100fa00e010007511403000c5080401d1109410714002423101182a031040e401030b4040000c1c81910325061216044024007401d02d00e1820001e00f01340e49070410b160f00501c080c08004a1b0104a4480601c100e90b5410400007041141d941f5042c4031140e150050408140081e2484913021040c03030003031150b9005e03900868160403420f480c0355074030f068030761440790900c40c10740607400c0c15400200060003e000909 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 565899838 1250 565898588 565898591
    0x1201060e0c0a031803120504051f0b010810030b01060809010e1605030d080f060f060d05040c180504030210050406180803060f0a050d020907020f06040f12030e07090e01090204050a 79
    0x311000c2d004041e150750b522100940d10f0101803050001e5049402c06807000c02c415400700d200c1d80c40707082960401c032070300340b2800c0122000e002c8888844000d51002c00d48040c2601c1e20f00040e1580190390311f000d41103000060105141c800107224030390050605652100d10400007141e000008290b541c14007019200044d040880014140824034060245284403681460441c3c7c2c1c40c0b42a04520020590281900e400740e40d05809502d1103031502d0040f2030006060403028440d03410300c1e207015000380900d0720510210401c4030300d001d48810814048c850044e60168002c004400c0000003103401000c5c003030411100780703a0f6081c00003c4544498143d91005018031901500c0380780202c20302481d180780c40c81452091080d204103004070f45d203a46070b00968940555440880e603407103030010391904054014000d42480b448040204109a4030800318040344034048400902c3c80e003070070130b90583c5c0c161707a2080d1198024410601c0591040e92040301c00c0b041210000c2800050364002c5402c42d601607603413100d910b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 565901088 1250 565899838 565899847
    0x50c12070807111225140d060b010c06021b060c07120305070504050d0c0e0606070b0103111504151416030f180e09010c0507050304090506060403020a0603090b07030e030403021201060e0c 82
    0x14200c040b00f03100030181c20100a5106c40b00b00c0000390240d0000e280244201d03598403000c15681d2091031180f0343c03194814403c655840180e052041902c4a40c3c03410fa0061140710001007080e54850b0507500310550104601c1c10000d6594025030207090004c01c000c1c01c206003407000288564441c44003101c014060b410000000381041d000c1424100c00504260081108028a00010718101440c504584e0015006600603160750300040ba440c1c81d10014500c03621020030041000e000300440c0d9181001a07449034a81d1503180d01809605028034186030b000301000c3e074503c4011138012281548483c206290404240c4909030008060b5400c81d040480c400c003201e41003084000091113032050143c20390414509150160355090340e40e200d1070203420390a644134800300d511a11a08241c4000d50350082030b5500003525404000d000307081141054444060701c102003082c40b03009200b10415800100081c0d40350500715001c0c80700035400f505030960150340c0e4460001d40c2030900d010107805031400d180d9280d42e8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 565902338 1250 565901088 565901143
    0x31623070308061203070318050315090d030912080601031e1d01050412200106031a0f0705031605040e09030a090806090303180c0d03050c120708071112 67
    0x1142c020300c890300509140105602403a000400c0c4c5d10b040d82d040c68913208101764030b4801c080b11461680305030382508c40c1e021000e09610300e900312140b050740c010048480418400ca012010756000c40400341c1240403200e6681141840344401c207074450300604001c40c0c0c2c0030303a06601c80c1061244403003040750f0541d2441070b0b1000900154000201180c844024441401d00c0e44075106150001642142809140e1120740f03428200e2001ca490580140c000802c401035490801c004c0c80c0030300c00d4101380b112001800040307010b84c400f46428010701e00742c4d44450440d07a03401040e9018aa8000180003071001c10300000070000802025103105003603160145494054007880a8100c816540041810750000010444c900ca00007003503036031000c200c4481101036501203600d1403d0540006c4001c0d00142d15000080906030010010a580c103858002c850409803655252a2140202240144071182c10448180800ea21041d808030000c4000c001c6601c0e40c0000d01d41c2c41c90440f44282d010104038120b03112540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 565903588 1250 565902338 565902347
    0x1a060406080c060d0506130204090614102f0a06060302030c0d030806010c03050d020c01060501090807080a0b090316030c030201140105090a0f0b0a06021b150316230703 74
    0x74500c001c000c000c0740d080c0900082d0700d030264981d0400031035910b60000701c40383d460a41c580c203000315103d03085650f6515820b0660180c042c42c010b1001b00e25800c507800e0b0f102e003480d081c01001c88003030340c0d01c40c84969070382442140b80380d6100070304150302451141c25040c0300a0074042c40201c144104000100715213144140740c20003c116031010310408002102e03401098005200715401242460450030100c200c2c60b094805018071414580c02e80d10210755403480410543c840002c0d90380036210b84c845560384400d016960a024000c07140583c0000c1c080c0800038030f03c40500c1d0340140b0200203480c14035a88004003507080d0345000b4164001160440441c0c24142c0a1282c031110a044120340390755581000c01103010001d01820001095503101f80302000030f100d07688418072103030004056031092555280000d5032081c2010008024a80003c451401480d0015502002e2403440320828215034404902c0400c58001da801c02c002c2c401c202810a0fa2141c1c4001901b0030340e00e080c0043d075111505410000e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 565904838 1250 565903588 565903601
    0x209040608070f3213050a0518010615030b060706020a08070306050f0105091207091b090803340203010617010e012a020c09160206070c080406050904091a0604 70
    0x4103540d844045900105520039002600305201d1120301480e04c40e02c000c0b038404d840f001c0e11414070514180600c1440e1030560042c5008002e2640c41c032003c203000000403802c8440700c0c890780104995055444501502075003280c180101d0042403c1d041040d9511003005030b80c003d01200000403504410442c4441d014891040070704400c0d19004240070074040040c2c0944070342c0369039034801d8001e003064098131401080042e01038010900c06004501c0c0724243c10010080c084914008030f0144540441c0440c000002c1e1003109441c17050545294042c0701d90321908550701e060440700e99981d91000801360b1070034040c8a0042c40c0c121107903004e28000604031421242000b14590f0303183d05000000c0385501d0048051040c004481c10188000c06021209a29103108001e00c0e98020448108216401c0745024400c2481da6258003507420680e00c04e4402c60b01d90394040e60061040c031084c00113100c00c61140300a17040e041c07001380c4001540c20761500c58440d25030101d81c0f0410110030810030054070342031034001d86 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 565906088 1250 565904838 565904849
    0x3050c030d1103072d061a010e090103020105091908240601080106030f020d05041217160f170a0e010b0409110609060f0a02060109110702220209040608070f 69
    0x1c03030441c18000c01c1e194070f0703115054002c0c150707200307060800100b440c41c1300f1700c40081421600030f100b01442c2031500c0c1d8050311b292414952015a10300400c0b0a6502580084481440080286216130300f554015200384e0424130806801090301034400015616240d448809006c0b00c800918041d00c803606400d0b0900c0c0141803110300d030015601444460398100c0d101605492a604020174040c00d0484907600034011003050a0440d0b0403e4244000d1003954107240e01010125510810511102103a0888891b401e5641200d0301508104c1007058920400781020618032601d04101c1ca0314400326004200941a0307803c9c040d044c1c0c3c0b901b05040242c024070482100150a45091050141c076071100c0100408004500307002d007100003094107081da5540100c50740100e00e940c54079100c02c2c818000a607180824091a400700d49070005c18050102038400b60341c0359542c000d240c1d04140c0c1c20710704840c003108080000e030340394070b5001c0c0100b000b00c0d510b90041d14013030071266004001e01c0b49082892080da2202c4d40c41b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 565907338 1250 565906088 565906097
    0x1b0504020703051204021f0c0606080d020a03030e1507080f011502340617010506030f160c050f030d06090501080a080304080919150212041205030702060403050c030d 73
    0x3241d00198003c8140c880c180e82030358040fa0207a4030381c00801d0124104080661038030280003086d1100540061140d44054000c401c10400c2c991209801d90380c41c4005540364001d60b1049950900091103034202100c0f41e02440709451350345203120010307410729106070340c0c10000c24010000c2014152a090442e401400b0b02011070a20f6019000c000c0d454840304481ea102e0100d26031303038140c0c012481980c811070f80840d803203514404990740c0350000e01c00c40c0014600c0400710125400081e661030840d040e0b80c040c0381200d0550703010f911902c0712010300c0d20a641082081c400080307001004581c040c8600c291520404001c0c40e1b44d9107124403504112070290f00328208180c90a8018020340c4400030b551180203a2000c2c001d980d0741c45074200722446000324081550310070807510300765023180d41010782ea50031181900d01801f034100d004101661200e24008503008101404d10003040262600700d5150b41850080d000d8901c2d0119a401165031640720790000d69141d40581007210b200d003800c01084042c1c0095140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 565908588 1250 565907338 565907347
    0x1f0e12040305190309060c080f040602030a11030c0d0e03012d180809010f12052502010b09160c080d090b090f031905041203030f050705040e0c07050a0c031b050402 72
    0x6000e41400c01742e0243c0d00410008051450411a01008035010740c0404a046a180c0e0360b2000000c0d6070754031094117100015454a8060211500081503a10310202c400140402061840d0100c43c42c04030038004035810340d00d85a94000141181d86c41c1c00d0f0710005400000c000c00c03549420041583c440c401004041c001d402c50385000f04401c18256000c1807000d02e401001803052040c100c0302c1c4481c1641e40c1900318034041c00d02066106428811018400342c080c44a20424a658141e0807150b403148039540280401000030781113241c020088e81e80c10a5801c0003803410595465580e51504418503045009640300b401a0038000184d11450b4044200b00c0207004600800900070f8881c01143c43d05102c007564130142c90b045034010b1041d40c000e4201c2c2c0044e1b100480550030004c0c01340c0350341600b0360103092404010400d00c9116800f15400d9441240d10700109480d05d183c0f0410a03880b070f1409542e03900417a029440094002d880c00d00003035014005030701c8400080040c2411401c295840307244180e20412 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 565909838 1250 565908588 565908593
    0x20c0405060a0501050403020f0402130b0304120905010c120216230901060f0507030c08070312110307140f070c260c011b020d080a030f05060d0201021f0e1204030519 73
    0x6007203c0503a541030309c00200c2e041100000c20064040c40116520180c08880c011445096000183d446a0300440c0209144840e100040e5103210b41806410300040d0740c04503a4010031a0a21408403180c903034811264102e4150208048105071504420b1208454031102c007502c601c1e09107081c900040885403d403255141c40c0002c2c01c80322005000100b400008995002458004c811151300242c00c003144640ea165a032a000349010b19031206100600d141803c4d11014000355070a0300c1c030800e07880d1191040c0c4402c1180b4000c254200302e105690f588802c200420024074041c14403c01804140307040c8c803104501e08100f91314254042c4a044442d485078080ba9070682c2e001042441d0326a00420300c0d54030200034000700e0f0400031002c2e000707404044001440c100596043c0e04c40781c120745030b5540401403511040200000da000703080c0c0107401644071080d50600b00507003409003000c00e4031001002480214862020b400c000c9840407c0e5940d16000c1810000d020046c07140903078100010740c0c902002c00c1e01340e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 565911088 1250 565909838 565909847
    0x10e061305010b2109030a111203041a0906070f1d03100603020907030504020d14030c0d020c0109050a0302030d082707140414150607020307090e16140105030709090507020c0405060a0501 82
    0x9030707031f007004102c001c00754441c0030380c4240140c00030040051102c65403843e06041410301051003888208010103200300045004070080744043c000e11b40c03a038844c00c00c01041e240840b041d07040004d0141c0381142d800d00e50443d40c2e0307003040320150040c118080442d006180d070040180c113307402000a07080c542042c04100042c0d071b9002c3d074a0745441d40010b2606492840500c242c1c0755000e500d1003400360384540da290700b400702d400040d03021006409a94400003aa191001d120076005140700094040d03000203110036449000c0c007141580a1902c4a0244940420250000000880e01d042c0c0003641c1040300309101c1c14070000307c99404445c01752000d002d0760a41c1c1c080c1d121407800042a40c2d100350103202c041d0180e0b54468040740c100c2500102100c654907168040c00c80200b4004406400c3c038802c1c0038019042491400d07030300c2c080f10f4030f503026021a040c2d05001550303580c1c0010000300400071200c0001ca883d00ca1489420300883c0140c0c01851440042e0041c03008a49000d004a4803e44914070700b0005680e00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 565912338 1250 565911088 565911097
    0x17011b090b0a03020c060f0a06061403160c0503072a1202120102040528050f0102190807020a0603020a09080c0f040b0a05180f0f010e010e061305010b210903 69
    0x4086074141d44001c0140100c0080c010046000d84038001c4809000b01ca0540d960040e0042c5c00c05a009c00400c0d07500c00c07050f16a0951001d044c03400341014800503284072800c600c80350040000342801ca00041c5a035507020b0550b440f07114200c40b4184048903107032240002c008a900070002040d00c0281d0141000c2050900301c2c081e1000911410507100f15510850082d01a81d00521000c0c100c6041c1d030404a9011007450313000c3e01e00c04d249001c400b600003514a01030313040804028060b0090b0000155801180300d95020a104c20f5070004001c200e00e00042e02c442d649900140150f03500140c450b8100e11009250060580c094441544501040303580e6542c0d041c0c01c58210b10742110700082c2921071a0104040240329031015600030040c2c10848604000d805180b403151003038101040944e036505030f801d05507000a018141c044030000c0010f0005155030901d41c0c0d0007c90007018440b4044c800c012000075107600740c02241b003a000c0800c13046408506800c54604403414002c00000f41e01d05940e103907582c4d008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 565913588 1250 565912338 565912349
    0xf0c010822140d031a04020f0403020d110d030327080a0e010318030e10081b031810270b16110706030605120d0206011401021617011b09 60
    0x700c01c2001004500340c40308002014041c29207040c0d85103030342e0290050511a00c02c0450901416003040d91303140070b01c00c6440110740103048604243c119005e0148842c401a41240e18407003518807401c0740e507030b00c00a00254610a50300403404071132210000540c500240d42d0091050704010018001410f03000070b0f1a4030009500e000c050708180c20300101c010b130880398146400c4402c44d060303030010306500145001e0300490a0302d4104140c0c0d524a000c60300900102c450604682d40b44d0344040d00f012150008603000100c1902907a4540264144103013032030403e0030015003043e0340c0c1e011000c3c0c01161600c24444d200f82c00003500800c07105901c98103003200c4014012000c1100c0c45400fa080180a0308108255816200485505c83e44a1402800800382070003a94800e140f50702510300c3d11900002c015402c0c466980c042d025503440e06d8261b0b0719404003280001e0540c0108400c03e5106020b540c2c51030020188003110702d80c003001c1c0030303070190845040c0c0b58404c01d031003c81e2403000c0c0c0f10303074022180b0801c030340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 565914838 1250 565913588 565913641
    0x130c0504090f0602220f03170301120f0320010501030302010509010c020331063b0d060e010903030203060414040c1401051b01091a0112021c02060c0f0c0108 69
    0x40328410302d5402000c4583c2c540174904000004200c00e500c0054607400c0ea403040701c1c0c0400c425005090f924490109109000c10384425a42000001e03400380c02c490402d600c20700307021540415001c40d40e84a20030250780c6903c070769036500042050680c240034442e044540100200300d8038113910740094583c8501c0150170340c400b000039540e081d500c1c43c01a59042d410135840800c52102e489560041c81044181c081922103c02013a810309002c0d61080440f65504180d011032005071903c40070b000d6540003240e4140c9a10703983d44121002c5a4080c000c0c2d1005a2203580e00503541d01d4541c2c100002c481c00710754030300c100014080c01c0100181c1c001403084141c2e00c0761101d96416071750001c012111072041c00074408040940714604041260150424540b140c4584406e9808040400310001c8014003446071502549410842d1800341c18445041000c2800180b583e0682000036008102e4541c88a00102010360101518450011080c06902814a030910700b8010038242a414441d169461070700e81c0d07202d107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 565916088 1250 565914838 565914847
    0x20405040518070b1608090a0504020f030702070617040b060d1410110c030906280f0e0d0308070c0510060b03041a0112020f040b04051f170613051203130c0504090f0602 74
    0x32342e107004040000700030040083d580ca0700d075a00c2e03e0041c0d40003a929980035210700100881c1907802842484081c126540361982c0e5552151244621420040c0009030080500400c500c0400c80c441d01e40181011000000c01d01c500300301002c8000c4940e4101040c9840606003c0c90181c05008000c640c1f9490049600c0d44d00ca500a048200145510350407460712002035100c13a0754401d401c0002411004515222104022204002d0000b0892216801000550090700040209018100c19920240141c08950524120445600895103e0340040c0080c40004c020070003041038803c080c901d441d010041410155150522680c4003440c2c40f0f000034403a907200301528101e41c90b139034001c0ca00705400038011300440c240405c0802e44446200000c68180102e071001040107100447c0c59007407001404020030042e0f40b080880080740010340380440d6240a414002e110105040003d107010b407031003800c1404440d0f001d00d424801a403c55010b94040c42c00d00001c0c0703001c00c1e41c2981403a040c0303400c51000b607583d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 565917338 1250 565916088 565916107
    0x5070908241909050a02040615020703020103050c0705011103090607050c060f280b10020c1f020f0d030b0109150f0e0a150804200604090f020405040518070b1608 71
    0x100d00c0302c00ca0100036442c00790024103000d80011034550250003a0380800115031160070113041c0c541d510046601585c88a1000c10055100b98055540201d00d040068206420f41c0d80b500d080d04d111840003100c80e4404000d20409500a11010303030081040e040145c6445110310045444400050111629542901c0016802488000c0d00c041090444d8400403001c0203005002004020064403280181c8804c418521402d00000d042c22003000003c10302403081d4010021268009c034582d44910446c010a08881d2501e0304c10444400c80c11072a46000c2400070340c030000100a4211a40407980305034140e14030b034443d59045044c0c1c0c1e815041ca031510000d603d0503c40401c0100e241544121014a1f40e05a07032900180d105011030f001d140315020001c1c0300d1b080c110f91030754483e001e140c005500038020841003101d603080e5071210f07c210b240f0032800342c145540c610000f07086420441d5020303040c90070400310b0201c0e481e0910040000d005002e9401d4100903015011803034524031541c0c010404400017078201036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 565918588 1250 565917338 565917361
    0x5160308090109140a060b010306050d060e01090f210810060503040309030c080703110d050705011d090f0402090708010b0904020a030b0a1d090303060306070e0d050703060507090824 80
    0x54540200d81101100d0030307214605e40d2451100703415224680ba00441d20710540c031902401e0b04592004162042020840c3c440300c00402441c07000145d00e6603150f91680020703000c0c0707454401036070241030500310b4007480c0240c0c07205492904021104019408007000f44166901620b80152a0607280103a101d551f035141c10384103005280c00103030240080c02d60001d2003039000644038040e2481108100848050071090010a501030a0014403503000702c6800d010799441280540751101481c60300411042030400070622100c01031b40c44140c120140320410055007000000e141d0441001e1803d500c1c0c0e503140c8000c1e07075014028100d50511481c0c0009042d0300d240d10035002144120030081421440d603903100e0540b18024440f00c0100d1100c955440000d220860200c2502c0c410079001d8007410041e80c3c0c8004c2181c440080c41c0b68164484045545c0c000803410070040c2030003542c0710703075400182802e1005010301240c0b81640402d1031544200358501103a42007040b05219002d02230300000454940141648 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 565919838 1250 565918588 565918601
    0x1203150e151503011809050d0513030c1202120607080103020f0103060e0a020a140703020d080a06091b081b1e0f1801030506061617190201020c010b01051603080901 72
    0x1e0340300d0b040000d004240c185200056040f01c405e403081c0c0a07012404036580083c0ca05140c03001d0040d030000c0002501c012700420080820403078a402152030a5100c0e5034000420381150490420030310140c8888046007007203a00e8503088241040107011a19002200400111050000900520440c0001c440590003604040c002d03181c166040150b515081810000035003102d0348540004460388c080000c10030302507088640309038140d400307040712201840d416100e03040301400365001c1a60710300f000034807051a031082844003002450401c07100a11044010000c22004d003010344d04910f640703500f0b903c05034400111411400b81c83ea050780d1814206001d0300302c90007848252941e0800000e0100c0746402140c0f04405028000d0302c4c104590380b155000d01c0124010303120404102c50091210300e0100d00e40d0400303803640c0328901500c1d5240c40c4015490001c8040768002500241c5c0d004165540210000e00803c44010304c00c1c68100c0c201094501c0c0c090224041e00c0c806420702100e42d000c41c408010a40011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 565921088 1250 565919838 565919881
    0x4020f010233060402070c0905150a0824071d0f030a030f021c0507030507170f0c190201020307120936052e030b10031203150e 56
    0x21410111860380310890084085080e1100602c9100060311a240902c01d031220700e500700b00344d0f4510504003030405004000150646140d2880c510019150f82d0300d9804c0d1070064482280582104228484119400390080394101c618070041810807054640c0b00c5060044504d064924058061b5644003040b00345c034080e2081d54048c006c4040110600d50408003070b44000905a01711911144401a1902c11036041480000051020004400801d00c05c0e000341094134020459582d100318101e0145540d90302048080c2480080851111a1150103010a644500350202400500146580000c2d128440c0c10301c010286100940c290051302e110302c0d90000900030790444503480e0306a110615840c002c004074106920124501d900b2500441400b806010340729050303002403280f9400c03541000000d81000203410441118800001040110010b6805000140b040041c1310703041d400c25200c1c40c8000820001070501700020600501c84c0011010201d815100102c03030581c54443c1100c910f021822104e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 565922338 1250 565921088 565921123
    0x150904020d050a0c02060901060305070e0901140a0509070506040503030f03090f0307050a02040c021501091d10061a0304031707050408030a0837021b120a03050c1204020f0102 77
    0x200f041c101d00715400386010200540864140d81d82e102a110700b41c03a803d001c0102190000b031001c00205484420f210f80200d0450004200b01c0704c40321416840c002d04481c94042a5218002c4c000710350340c18070040e4080d00042d00c0641c60a4204030200c1d60b20f2291103e5103964240000019003075640a01507602180c10002c203a07642d030007850918583d100000d03c0168841c908c0c041654080b01d000095100b807100b02058070380c642c0d070300c0d240202c0002c0003081e01450740b0041c00504200100024401203010580038480007a086040070800d12002d020908804801c0784200240008640c11100c03001418070031620034071aa640d020000c503000c0c0190703446900c0610010465031025a040036015100302170301c84d06500401001c603c1c80f5401c00c09590701c00315807144a8440c150b07080780c42d0002c0515541c0c25a0600c01a03039160720b514034050a0200011000c10080340055801e6414012190442264440c3d2810048009000c1a016002800084c810001160f50b102244d00074000e100010031480d65 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 565923588 1250 565922338 565922341
    0x90907020102030f06062503050903010c050327060c070f0204020a0512150d1112070806010603061211010c0c050a0f052e0f05090402030a1d0c150904020d05 69
    0x1000c0c0c081d42041e503001c13003960b42c8500014001c0c10144140d84040030113440d0007241040c015169102920321890030b504101c020020142d45032424010808110b105548a81d0b03a89412010021052400c00124150034803001a15454200028a15810641e022400c07a0380c0c0c0c3e06482c005003807004444009400c103001240c012005034010009e03242806100b060fa030340c5a56000201d5100754102d50030150300005103160342d00811440c03004000130b901c015007070759950850315607141e25001c0701d58401d040c540d0000005009196042c000c42005041100840452200680c1c4003c0781d4a400381a03070341013009410030101400701e5081c00e40300810024143e051283e0f21140540c81005040c01148d0252001d4030111841c250f10745541c1c03414800320280700c2e29001c880c401c2210007118140409080000500000c2c000d60303203a10095029000815000440081180400c1c0481c40180022031003504061441d075016120294840b40044442c8160b0380d0701e807940700009009001e00e0040b084094075000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 565924838 1250 565923588 565923601
    0x91701060f0b1b0601290705010f270201090e04030509040908091903170903150705040e0f160503060d0f080a02012a0806010c1a040308060d110d03050909 68
    0x3404204001902a0318481c1181e42842c4c1d1030304203114680410402040201034000c400d1407183c003000490304070525207042515000d0a59000f001340c6c404065441540c624006819154900071f212006600d02021903541c00103400506d45100d01780e8080405000035040500c03c0c411210000001031040040b401c0500700f5041c070b0340020075000d0203200310740351604800341c0048a28040340e40c8000c0b81d008080403070b00031106039005581c00c2c0742c0511445242c1696190701c8102c69109034060f54a1a8640e45001c90030a02500054090841c41c201c000901407a07210642c01c4040d00785060612a6581d00c66101007000084002c0008c1d1610700d600301d2060420240b90300804d00010701d035000f0301c40034080c60800901c04c60090342c07041c807002c208151101204d00039000383e58031400506002400c00c02c591505010544203078804080351507848200401c043c3c12070303251078000c0d0f0213440780c20003c251039a42034401d613006020144181c442400140406114108841542a000d441481e49003000f0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 565926088 1250 565924838 565924859
    0x6210b0711160905100b040b0906131206140f040b04140f0a11012c030a020a080d020d02010b01021009021f020d02010b010f080c070f0b0c1e0703091701060f 69
    0xc3c02000b61440c100404203411041c030000f200107407558030440034600303071500c02c04590380d40c4140f00c0250451820b0000d04145010a94200700610007540d55044814041c5031540483d008102001c210b1903034042402141d1030002c500b00d92003980464044e40c55111401c0c960008030801d40380400a114036940443e010302c000c80d010301002c0c410004500c0d0380608900642c1c45111841c00400380d400603040c0c6401000c161400c50a016002034152501d1a826401180d8050415004100c1c2d65010303178030003681c07164100702403a554000b603c0204052101e51000075200c4403810100403100d500c80c1040010355440c20b0b100319440e490021841c2d01c80d181124084e4643c0d03000415040513510300740d900802940146515440c0c0e2150395283c00e61581e40c207140b5060750304200000d0310740910700c200c010f0029405500c0140521041203070782e81ca80c1100d440303440c035046c1010508000c0300ca003449240c00203030300000501c0035650303604c50b1403644011200302203005200c185e1010200343c622090004140340308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 565927338 1250 565926088 565926133
    0xe13150b09010905030c09040b0a020903070923190b130f06150f0503010315150303120b06040b03041115030f0712050411150708070c0906210b0711 65
    0x203880b4415815944c4041540700c03070286211303c0e00071690030300040c001000c00012540c041d0b0300010043c14800540c0209151042941083e0420fa40ea400040b00700f080d80066141488640c889880c01860300c000b030314803085c0030b5070440d0f1012910340e8403640842c0d445508402d0042901e01040103d1081048400d01410f00c41c801d041d040380001d040ca24012f440355031151034803122a19600c0c6180d103150343e0080c0030808105044103040d030321102c14040c0710303140b4201d41c010b40c060750360101180c2850000d44210340314034108921804e020001001440c1000060b80d5000d41c014842c8442c8010005c0810001f24040b04d200034a00d00c0007042210a03007049103145d000c0c41d99039560000340c0500e150304008850042d200544010106504c0551628220b641140d51071810301217503040c94a41c2d42c0b84210f542151008840c52080f0403020300c115451440340f54000e00c02c00c155810900c2c404103040d84652030150001e04035051100c00600310901840d2804520248103044404407420354258803401c110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 565928588 1250 565927338 565927357
    0x1090b15090606040b0a05130503030706271707030201021204080309070b090d020d150c021e01060f03030c0c05120d021209010e010c21020a0606080106060e13150b 72
    0x901c07101061050a00005840c10766200441030762030b040d206401a60250010740b00d040103404040000715158609001620541d882024086020005e250f504070500c5c485815440f06e40c01480d5090002c42d0200030100c1c4400d100d2643d1698074109410b04032701900c1200c1d12041d124040009000070018181c00a40c4148202c43c1624125615030b40300e00140c0c4100f000350340d0300500420000015103002081340883d14801d42c0101c14690042c400d010941c1c0384512b210000d0b801040301e00984010317026a448044403108020052070741031801b12000c41c1c03418003010b400c120301d00d80c1c06010400300f110820301800c0010b0007204a44036500c0e403e90340c3c101d05100c2c80c00500840c008070000f0061b81040ea00301c0032050b112080b9040c640c800441e104c001442080d941d14020f0000700740c03220605000100382816607030161140340000e0400c01c06030b070200d5204140503890100100301c5c140c0d0201120401c28030072601e103034210400c0180303000903001c4036110518110b4065000615114507500405c012071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 565929838 1250 565928588 565928599
    0x71715070f1b081b010902121515240f040e0a240603090f0b040605041209030b0c0c0a050f030d141b030c19090e0f1003060e01090b15 59
    0x10124400b03058025104010841c1e4804c0c0315080100c4120b58100d81a800c590700001080c51a0f50001429240c81b01e07289082c90300b225a140d0b80d03500803054120391010303560f00104510b003001404a030008001e5115034000798411005180c60082480856107500d0708061070613142c81d1075200c181162241a038402ea000c924000c445c81d1720406554000003c0c80740020002d10342480c00600341c000e000b02d22400c4880c03100c028146030000e0402488280940d0144100003400c0c80d0901c2d10200440c40440c04005000600b07c00b080011060385806500c1210250381c0394440ba12003050034a00110a0001402c50080c0b641180301e04a0002c06801c4540030310f00180300d8501007a640016a031003d41d0041c0d044901850790005011954004540002c00f8042003407610781d55040c00141c64440b940700c0c00000e9003220040085099000c8030540250400310155164101014110844141488001c0030191203c801c1d584e90542035115400464110300c07200014a018004541da06c2d030414010391041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 565931088 1250 565929838 565929857
    0x7051e0a0f11010902010207050906010201150803130501140910050705060a050912090f0d020a0305060a06091b0c0311011d06100e0f01030b0a060506041806080d02071715070f 77
    0x42c0050013000300031134043c0c0203051030500313241c148606002d00510f01410743d900c490b229082039144004d00c20040203030740c02440c1c0302c030007000f0011040350b01130b80200e04005403041d00b078520158640c1212209481100c050090341d42d948803c0e0389500500d00d01500c00e010300010040c28008a4004503c1141444c00396440310700300c1646030866000301035209411841841441140c0c7c180407040d0061075000400f0f0812040e40d96440c240347c11000c5450301092511800c040000f10304501038500d0350043d08801121081c0110001010705001180c06002c002038a02070079800442948030860b100aa00e407d04050021050071566403402075070f07010441d0026441c00140b60720f41e03510300f90041148121507001646036031142101c0020190100900030380d540d100048540d990300081c0000c21012280840447c80c3c02000002c0355020780c8907111580007034100c2c180066001c0b5201c0305940c61003100d45481000030140ca072a10019040507584050103405006009804c5412440c4440547d501c040c2e10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 565932338 1250 565931088 565931117
    0x302010903201b03070503070f0e0609040f200402040906030b0c0712270315050912031603060f03140d0212030601030c021c0503180304080607051e0a0f 67
    0x202c4800590702c0074640c10021a440062202d12001035602400400722450b144d102d1000a00700103196001400044994a0821484400d02038155014400311940041803519450701400c001c1c0856000300164400401208500d58280c018004140040c0045440741e40740c205900c02861240000da4081c0c10300d40006420140301011250f00319402610041020510081540c0c5c1c200c180385045990766604040200303407160120007400030340c0078440d04140240305004c0d100c00c0784c101400669071a007040005a07000d5441208a0340c01a0b02d00300c41c03401d8000c940700224000e1025800010310502e503084000280301c4802071100d000d080c554151602c20029030810390380c54480000c2c0d0052480203100148556009920101981d84a401601c52074107140d0165080b01c20031914000216901005001c081051168400c4a43c00148020362070142010a010303031324070b401804403040150004003104020000c4002c1da84680789080420380703411000001408010b0714035001000221702800f034805 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 565933588 1250 565932338 565932377
    0x12090b2a0901080c0f0307180801020a08070f0309021c030806092503022a07080106030206070209040f020d030302030a27120908030703050d0c09050135040302010903 73
    0x21001030305500d4a4070407194010348401c0c01c020440a040c0720203003c44004400800001c610401655482001c0100c1002c0700706501d50440d00311500aa20510120850603044898180c201d145030a0003a00c0c00c0c0040000c40c00f800180b80000d420660b502c4040f40d105c0410b40d5544030791842078580e0145c9075070700414011703080303400c44032040820076241d1310054802d05269025480704482c9005071070411000b59650101440c062180502c88280c0301014a2041c14001e0704050b01d1404000e0100c03502e1a0000754450080440191244051002040801140c00d180f4503a85034050180f94841340c03e41000340c02034004071421100141400840d02e2190fa4421a11480750745480440c82c00e940c0b29103900b14840f8850b441a024003090060125103000c04001818015200ba40c2e140e664504008a41c8141d540d40c014203014031180f1001482560307003080c007220141c3c0d80d20f065543c89121808140704408181a040030a58080700f0a02c0281a4103420a414180c040d454101032400103044448 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 565934838 1250 565933588 565933651
    0xa290903031305120307082e06210e071e030b0c0921030903010609110a050d0b0a09050f0f0114190806011502062208070312090b 57
    0x109240c000308001014000c1d80d42c0824290350003941220701419105021340b28540c0240c65601c080f48103a070030800c18001c203032000107641d00700300c0303810340a00741214021a5103505805104140003080080141c9041c00b50070308003080722900c40c00d20510807012921354640326940a0070728010080102e21004180c012040000c50b039020307032212165920a82c0803141500004c01807035000c1c6a6180c4107200003960003c0d0345a100c0d460000d0b41e5511407641c01c0508580307440d44041c0d0090306145808460351664829a041d144042c00e26035500c1c402510b2402c0180345014103039138800c0c0081c00100d202222540294810b41e40742815400d6a1200c00c0d003080e001200748500381c0400d4000c0301001140c1401c1030900b51465415090090060b00c6000e01c5081c05000d0708800320402c0c0f802e903031105590341007200310782151042014982c604031601d100c2d90410381c80c4101420000c1d0005401c003c00d84100d0344600b900102901c100038145c1585084603d0040130b40d200c070300b8100e003040c1d0140790303440c10214103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 565936088 1250 565934838 565934851
    0xa0f06080c09130203060f0a031104180b220501021c0c02010e0c0f06160b0925030222020c0703031206120b06040207080a0207050a0609120b06120a29 66
    0x1a00f104042e0310300d10295000800454001040041002030342c1c0f036841c3c0b00009144071f03401000360b0020b0740303003404220358001c0c8264445500710f007403050206101c800c5041e00500c6481645040782c0740c00c019201d40d05c00d00d01d0018000d40c400100584e4407041240c030015030a035140810320492700c0340341c01242a03034041075007040709400c1407030140c005140501c03035400313102d00c09002103007085410318504100c02501030080e00d260400c0d100300103680b0802c1c0101115010ba241c0119951100c030900c45070401c419000003401400081d09485071128841180914515000403d5640c3c0d0f180e1540c1c0741e280c501c0c92104401003144500c1c440c3c4100490302070031054030314081d0841106c03100380c0c0740d000c200000501516041a230800045e40840c00107030040400313202a070020140d0030f160409004c80380840d82d001c1c40070048a0402070240c52001226003580c50340105031484151a0f40c0b000440b4049013040c10074031840740c040d141e820000068045443c50a0300307690b020311070398004100f04d00c0c02000c40301c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 565937338 1250 565936088 565936099
    0x509010b16020112180c1208030f07020114040f060c0908030d1d012a02060415150e01060c0302070e040305041e0302190e09010b03030301060311090a0f06080c09 71
    0x1e204107000030800a040900502d0000700c00701580c4c01001c01c071000200794003a815943c80100f400c0c01180981c68000701501110b08000010a4440e412140000381040f070102580d4008034880e64800d4000c00d08010410302e0005403801d140c40d05031440a9220703c2100d44604062800600354010848007080300c0c4100091440c003a110000c10008182000704107040128182100309005801d1141c031072000004d9440b00301103060340d01894000c1c040c160700c800840d88441c040000158900401010400c04d51002150780880b810100034004810f421030030601e040d8100000e840d5070702c440c01030151802a000d4842c000e84a500700ca0061000b10f8014000c1030042000704120341047c40c2101c50381d00c00c0000c8030002c03038407540060014003106c4118040035200540504c818401d4400e81ca8002c60540c00130044c0d1032003c03000c6500e82c00305221f2041815510011401109050710865002c80c0005005000954071020b05520310347c0756016000000720b803600016030400f10701c01100d0031050300074030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 565938588 1250 565937338 565937347
    0xb070507031e0c02130b01140906071202010c0f020a0506063c09010509060a030210022401030515010807030b0a06052e09050604120303180308060102070509010b 71
    0x26509940000c50403070411007001d00e8031403050102d1041c244030468581d0342c01c00c0c0075000d00400c0301c12214020320b12034561900d01412070507a04000d029200021205c2611385543c00c0b600081c4141c061020094072100048084505082e41076000d070b03017401125201c17103030280610720080345c0d20041250b00620586c010030100c0c0044ca0031001002c00c504800620500607039400300b0b03201e20244042c401c495580b944120300f444d0b5182503800580540b409480e9a100351400000159000c009440040e0003420160f0b012000c80d40309102ca14840110010804c0400c1c140e100c111f007161714244410354280c003500311803082241001d0600c074100c1d00140c004145042c155220701c50610b0015068401d00e03580c402000940740c50b0501024917141d00d981d5107076079500380c900d0030002e54044906601c003013184290041c07100d60303107901c20785083c0ca0440c1400c980082c9549002d900600c2ca4030300708650b403440611214205944134070064440c41c42a4203443c001c0d6039400601034003010038000e00000e00f80510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 565939838 1250 565938588 565938601
    0x80c0603040609020f0d0809030709111803030415261603020d18030f120e030406050306030102090a03050307050d0f080a052701200721030b06040612050604090b 71
    0x20400b05200b400240b50003560321740b4134001107040c40f140e041201e401c000414035102d50700d014880c010003020300000c240800780150554090610480d0902c036492005e07003031000f40c980c4041003a01d01500c030352082903106500e140d10240001079141190500c0719881a41c981a800c12465418002d03035400807481c03503500602400354042d4000e940b0a48d101a13403441030074000030f00703401213090300390103519080c0030251000c0740103180c031199616041801d402d040021080420000032101140c2d0b10349890741d2640c40c0c2d04002800383c843d1017101c0754442080a000700510201100a02c00302d031041d000c0b81c104d880b02c90801e60300280d482c03001601240030306000030b1411419400850b480030920710034074850000c414140e0320740c0e85003628201540c3e40d01c441700d402c040c1501e04124031400140d05002d003008002c1c0d607428400d590000004034000c40c03542d00065001e010303030417840c1da60302d009010b41d46898030b44000401e0942c2e130070312410880341801c012a10a0400307100d115111a00b2200c03d04440ea40d40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 565941088 1250 565939838 565939841
    0x1906050f0c0f070e163002040f060509130902010e0d110315011502060402150a090f030516290a0e0a08010504030207151205041a04060603060501080c06030406 70
    0x15920030650240741c640d1000d480e01444001e0290020003006406400e14001c00d04411100030240800d106d0100c9518000101145084600350034600c50410040f01183c40c04019010310340c0030407580c01180300040307482134000740035200c808426150105109175011660007601c0e83c0d918080e0100d90501d40001c2c26007004200174442501498004001030555404a483d0100d048900701c2d40c14001c000500941181400c00d5040b0b02c3d842c4000e14040c2820340009405524810483c8081d100c00614041002d018644403c0109102e0315a0141789680741031060b143c0800c4030200c11a1890480040b50030b080103c0c190101c0b950b004d42441c14070b80da003005001c80794400b041d40030034494004404440340d9603034072914000e01888000454142800d1601a03d4500c8541012140240718420002c02a5001c5480706a141c025680410551624145204079107031914088401399001c208020030301c800358114400b02c80c0704002c00c024582e6030701900e035201d445004950394808001c01c0842e0104806 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 565942338 1250 565941088 565941097
    0xa150e0a11070f030e040c030c05030f04050a0515090c041a0f040f06030c080c0303071505060a0f0e1005241c0501030f060c1701030213061a04051906050f 68
    0x25011050b10b00b0b08982c0b900e14036000490300880004942c581090204d05041c000d281c98001941001d1003c00b40c0c0440190144c00020841411640d0400004046c090100b123064201d81e0400c003550100304851203907034400c20040b564040180700b00c0800e421281013070310803804581413503204140003948510030810001c038100c0016902070b8030788508010b940076500c94900150b2044548043d000d1608101c2410492108030243c401e820a100c017901013801040f580c01c0d25540043c00007025a21840001c81d1250690032076110304100410208188884201960180c02d10310f1629614550720410014001c0041103e0140c0c000180c840104070700e54440034101c111030140c18000790078141003810046a9099100342e1707001e50600321080070f10441d40f04094400c1e6091500b6070305c0c0102d02c440354103002010310000303024210365001c0100d909850b600042c007412500705180c840f401c1c100c0c000d2025800030f01409208407240032201ca450645100b604088540360703283d00d0f0401c1a41040c00985130003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 565943588 1250 565942338 565942361
    0x9010e040c08010c0c02010905031b090405190303020720031e0703080c0a120314070c0213060e0712020c0709020a090f060503041a06090412050903150a150e0a 70
    0x141140807a802c1003e02034412900e0700c1da510501e50140b240001013100d03155600540c0284c00c4021440c0040d5014140d0303840003c02603510818035256490400e20705075400040010881440321030908141d8590000d0101c68081d03090752110100415440b0082d40d640c0e04401d41c1580f043d503a818084a20b0b04841011000c006d060b19030741c42c0c1d6070701d4181c0d0592040c51990302d56040003000404110110780018224140d5207010485030500c0c5902d12200f10f406071610080c0042240c4000c215600c2014460000b0009081401481d03581d05111076000070541744000411080c00a081d160a0b03030344241c0703c0c444d04410042c030f9507602c0c211408000b0351240c00c2940401c90001800305900d42a0303000d0308000c01c1d00c4e80d01c0982e0392034107003000e40a45500e480a40c100200440620840b596401030494009412040042007040512400e030303200d1149410403a014040c140c2414200811030303003003034400c02103138405002101d080103040e01c80c449240034540511110700c003c61901e40c42d59000c1100c10341d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 565944838 1250 565943588 565943603
    0x10e2d07090b0d150602190209131a0603010605030c03151e100501090504020a020d0f050d09080301030203101b051606020c030912010608100213030c1706060f09010e04 74
    0x40d02c646222942d5400408850a060f890342c3e0240145104840303404000c000c18805021083da07916102a445138a050004e803045a1150110f03011080340358640d6426079105007800311403140c182c01d07151212012680c592195103805030000386401c1c0480d61001c0341c000100608010602590550700e80c09000d40007200404a040d0f010101c030340c0e6040c036240207911009039a1042440d00c00010581a0b03181c105031300403401404980390729034000450703250340003090034241d00000a0321000c0b59140510460303c90380c42c0c1403605920902c01d04200a5041c0d9000740d0a6402d441c403902a80000e50300449200f220001c61804200c6070580301d200609145087d5031807080216a0755141e82069030490500a400b6410000701101d0074a01411800903154103e4000c4c49002e25066403a600c8a80ba480807020807600001d440c0c81c00c407400408040a0755200042911085d19420005c440c20380305040c50440344503100210303c44c2c1c6060290705403041d400420b1300100c0d03800c22044a8194001030300854010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 565946088 1250 565944838 565944857
    0x4020607060906110a0e0127230d03050403050705030a0c0e090109051009060506060412032d20070b030105040e010209090903040501090b0f0a03020c0a050114070f03050f0406020f07080f03010e2d07 87
    0x82e5a500ac03000c0606000c1e541c1c1d192910b0440c01d1003403c002103503012500c02d41c010140c0c40c00042c800840d41088440100c611503055440785007040c05072052484c02012401a05c04421600c0b0882d030bc81311069000d4001000160781d00b00c140003003441113001d000004901e00354410000707441644e80c4450016840b0001e13680d0f01d8044c400042c481d0204100c007020880c402d4221904070300e4080b04095940c0c901001304030f1503150000240d014813040c014580519203076060b224505d13109404a9200c183d010b08006441d20b015151291a074119000d81e0740080c002a03800a082c011000a440074585d00c41520380c0343c00e108000c2500250b00c4040d200e40140100700012011610070700c0381e0b5003184005c98041d6020301c2e10300320040c0300000081d00b54003070500e4071045c0070355030110704601c1d0740c4190301440050742c80303041800c02c180600072032000030204203000492030344078003466001c0d6040390148400382c0038540f41c1e040d201c82d401c40c080c031845c0032031b00049045a9a91114018468001826003401141c2e07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 565947338 1250 565946088 565946159
    0xd200a03061a0436021c0b091b07080c031306020a080307081b0d0902010e03210705010207051b0411070807030c08040f060e0a050904020607060906110a0e0127 70
    0x11890001d01e101c018550102c0c143c0300884006c61104c1502980c0402004501c00c2100081e20b80311001e40400784000b690210280d00860384401c03901081d4200c04c1f0f4a80303c84031b002d01c3c2550b95000305c1400c0f80a588a0800168550001682c3d00741180c2c041c418500b1a942d41800b2a100c801c020500081d81803814015a00541070400401140b600c1080c086201c0006000140c101000d1512490103540404007000c071681002c203100f03405a00c46503000365100d00900b059400390140310f44c05807280c026a03540e13a2212064601c0b4558681701500e041c01118640d82c1900840e0040d0000178160b45070400ca00000244182c00070041644202546800c01da03c540440076007460340d80082010803a480809640c0c0d1401901d4100140401c40308800750b0710786035020801754082c1c03160007045140c8440c400e40411615401071828640c1d610480758440c03400000040880000078080760106100302d01c104002e048580340c118407020242d02e040e140030701d42002c915582d148010980c46e0100c500080405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 565948588 1250 565947338 565947419
    0x50a0303030504020f01080c12060d05010c080907080d0f0c05160618050607030c02101b0f0218010807060f020a05060f0105030d1d01050d200a03061a04 67
    0x694060740d400906403a0030300c18040e00c0c1c00e440c0340f0396060008020802240740450b00c200d440f0000288101c08841e1110808602c02c0d800500c8010400e5091a18030b02205170300004561040d0209808c0f6983c00341c1c0c94500302c0e1202862258400081c001d40030241e4400d010301b4147d9080c80c49401111004084a10301e800813002c0b90304900c1c0021380c0350003800c2e910880380c0c407200701821044800710720308901958060a0f0030740c0071000038060850f003845200340d14010040001031078060754ac04050b45041d0318000ca440003528034101c0c4610056010b5a0300e0f01e42d05a42a07040e210000020583c0b281041c40540310300c0c251072510021841040c2d0000006841408503a00410101e2000482d40d41032000b0076080c002c0b4080742604005030300e140d07055004032820001c88413140c00c2c20041d80c0c1e0400c45030818040e06007510541c0d41c80d40500d004044a200840003803005100d15942000741c140c403900c02040c0484d16a02105034080c09010502c40c0c0c070300100d11400807005490800203540070f280322249 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 565949838 1250 565948588 565948609
    0x10e0906030c040e06061513090b0114030103050105071106241311030702010c020303090a060b0d0b0f040209060418062301080d020c1027170601170606030a081305 72
    0x400360300b040d800e00040c7e04283c402143c060020f03250f070030300f005a500c5900001303031128402d03002101e843c0d8456207400d0740180000c10f20a01c60100441e42c0b90303102d09025028103000d580003400940544102510603101140c8540a41300440b59001c208000c1050a5102811000c010b54440025540110395129030303c20405505081250356481c1e180050000e42140c10001180c0250b4008200300860b007880807946055082c1d00c8000001e01603100b44c00714020400310782000b0020700341d00050046030110386d4035007485144201c0d5112560754a8a09110617900c40388090042507030200c240d01d0000d056608820302400b0720094151944d07801402010840e4420791102556800512200c0507440e4144403d102c1da42c070684550400e6481440024250520300b102e003406101800c20f200c0d0220952170f54038004001010026080384040d16080d0740b524820710552204460002e42140301101c003203005441180d00801600b06107600d80ca030480c055010035142088a5012400480c02ea51102c0001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 565951088 1250 565949838 565949861
    0x40305011d1c0f0512010b0d110c101d1203040c08070b09130905011a040609110f130b0409050a0e0f030a0f05090d0f050d0509010e0906030c04 63
    0x115022524003082828824078090850300c80d008614101d02100031401c401e40000380a00d0b040c8107900ba5804100c1e4940504001c0b20001a01c0000020f2250840c0380604140490680d0410604c0040c0310201017130312402e07003040703180d401444920b504c0b900c41d640300008407842800c5126803002c000d0405801c000d014051801902004024030060002c209200300181404074010150b19052120048843c0110900070740314512140e1030303044510150300503075034240c3d00000910600040812807841e078900b171100c81d1b005514116000603911003d002e5440c511500d40403843ca88400f0104d075211703a41c40340c0c81350010f08007200c41c00208814140b00501c0100030400d400140303410809280015a458180c8d21203070303613000903128940c24202108680580c0e10300c3c102100c1001e9980400c1c0d40c54004d84100c954000c98008030710091110407a6904001072052040c1d0302e11904421054425009000c07602e1b0001d043d1030007103086c0c0d040c030b1882150046e00c01403c40780041e00786400201a5040c00c1d400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 565952338 1250 565951088 565951091
    0x5091309080408060f06010212091306090b0328062403060f0c0f020606010522081e031c020f16060b040e0c06031f080d020718050c1c020f04030501 65
    0x100280f10040c005150860100e8800e0000e6040c0240000e40d01d410100c012a106035001540c0111540c5004031100000c048800034001a641e60003240c00400480c189a0701078000c86c143c00012007610030041081102110184d83e018203070ba02d800b0002d183d86c1074401da0003e803925001d500c00340e1070304042c002140f003480c0c04200c0038103c0ca10380003a00c01c00ea03230302414008504500402d198000c144150721500a29120b500c40581012000401115a010181d202d00d101804102c1031408162000000c030030320182266008a044841d40d43d01c6003294141e03414455540e00b00b10220580c00900d2628044c5900c54140300201541418155020408603103081da00c800e00003c0782014040c0c1d5540001e071002a00c4600c0d584004150a0303c00200010707420b00d06551f1420890b00c0e45104070f0b0160141408462104072441e502940c3c408290064480d48400c650801e00c40503554041d80e4424000210007504144d1040c4001d41c60440510803004920380078400300009042c803001410055005400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 565953588 1250 565952338 565952347
    0xa06030c05120a03211814030307020d0c020102150a0b040b040203060f090a1b0903140303010b07060903200c01080a020306030607230406050414010c0507060509130908 74
    0x106090144090350101d8001e00a0320203440c180800419000f80030b9415090642c0e5103444006808000050440c24019051030070061032281005010720120584c410301d206803941020501b29692404101c5820006900070b020b00d0120610410385020319078410300440f116072000c9564082241c60844410b00b2042d5140c4000b5481d01d020b0042c1943c100d41550210b242d801d00c2d80216444034818104c0c01d024100071800700e80050349991042034006940003250260f0405400001c2082d12588415220344460541101024402004030b0741222442c1d5038181c6004490f9850134080c00c00c2032426002d2002844081c8454100e0340b0008a0020258001d45001580c1310700151060f08041d11504825106000b0000180c80001d040c0350031008908182a55a62510481e81000e0515141c0c18100c1400300340051043c1d0014040e10075141140c906682030080e16004442d000003101000e030295100250810906016078010706c610380015000702a158058412038040e28a030f4503003100e44030b00014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 565954838 1250 565953588 565953593
    0x807060513030e0904020108060409080f0d05040308090c132406031b0305150d02031207030206010302011413061206080304030503070b0c0c120d0b030616021c02030f03060d08030a0603 81
    0x1110902d107003c040f950404641400d80000b0080440109040d0140740d4485224041c06840c20540703015001d81540c2c16038441500d290100500307401d5034200c0200c0c0c00c0c2d00125402070004508100e415002800c00d60103001301c1915200945441d660125005c2c203001c1c00b400d0f401076121405005820382c0d031004100c1d031a1584c0001a030343c01641c0e0040c2014900001c0c4035002101103075aa642200c11070300461000078600009050501402d000319280c100000c00f20200354001c504281228001d0f02d1b01500080000745c0b41502d07100f2558203224016600b0b1083c45603500904202000c41e15103800081c03015241c582061a5501942042c1c4669002162103420400000c600ca0340c003240c01141c440c02c10540404580d56500348100c00e02c0404004110b00c60308502507400042c180d10014115406420f11400c03069a100f800604480140039400980086040303644044c04a107400e68003c0d844c000e1010540c1c0515000a041c26512012910000011401c0c5801440c05001040300004d031003850761 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 565956088 1250 565954838 565954847
    0x2a0303060d06230f07030e070504020f0f0a08040b0a09080316200a050c040204050604090c0c0611090307080d0c0b040c030c031407060e0f1e0330040f12080706051303 73
    0x8002c501014181070320008003400122303062044480a60f800f40c1c0300c100180c5040c500d401104508000c010b8046064500e0b66400820345014500403c0b56000b107498aa00040540f40d246202924002041000c0f031020144d1007290180d090551038865070032414003403003410041a00e80c401000b80d200c203100b101840414800c15103c010304032001c61901d450000840c2050103644124003005550340103d01042d4020101c00100d00e038020020003054050240c0800302d500726406140c064070668130041024000004e07103c1c4225001d8950803186613050b1348080282c0001001114004052000000091340358907840e00654800c0d0f03212004480120542442c201c2c030303a4408800c2145814020003961a01c01e428031607a28191050304014003c801d15910094a00729076a40500c2644c0d00242444400c00d109400d030034500410032024070101b1401d03030141c065409255411420390004002811aa030100d5013544d1003881e0143c1404c00a454038402c580301100d1201242400071002420036910 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 565957338 1250 565956088 565956091
    0x6061b1f0b1f020a1b0509040804140406180b041b0801060f020c011e050912101113060f2706080112051203060a0e09032a0303060d06230f 61
    0x35503410030381c095100d90003940d60540c0d400203405c40d80541104010700f1045c0c551030000d014003500c000114106454240c996501c82d03c41c030601008401881c4113285050702440040303440c0d08088a08100561440600500c0c48200f00380d449565442c080c80c512810b4070030481143c8040e21408425031600307101034241030f50504518219000b118070403c0c0b582e007005201020384148980d1a003000102c05042c1c07602d1081c440d05c181c0c001216415121564400540a52404002c134002d004c1c26080341c510f00420302840c1c0e4040310320384150006100c0e080c8958403403d6040b8039407130028003148501600d400007400d00c180309070f078011400e6021701000350060032460040040e820b080c000a80e49440d455103601906a24562642e400404031700c0c90790741d903410080070702200308000466017029210f85940c1c2e808140600c4803d082c40e030903920000040394009040f00e0509010b50701e1542c0f604204030001d200c60000f12143e95864071200700740d2640b040340c10001410500c0700003950411200183c02100c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 565958588 1250 565957338 565957369
    0xf03140f03030c030a060302370506090402031308031e07110c0d0311010c080a0e010606020706140d021206040509030405030a08031902030907090c0806061b1f0b 71
    0x41014524414403000007100c0c0d000c00e00940b260780703d072038000011020b01144e03480a5845400d1607008180079141c45404903e08148000c02c180c00e11304031420940680c3c091041c280d10004c01d2100c850346040903001198030659000c8a08034103502944d5030441a0000e49454196070905051904410941e00295802001504005203201810384103e580e5000740c08259000700182281002098041c02c1d00c01a18511123000784070384003070040010040c240848005042d14107100c01345041041c180300359401d03204242c0c00303000d1070760400c0c03820780d0802656503442d0101c14080003a0204e26140744042d004480e02c0380b100a1041c285002000283d480107841d6841c90f400402040113640d8001480f406c0d10755200705840c1c0c681d62a55040300010b405040032503899800041048088800032400c5000d58000d00d0042184601c0c5020444443c84129070340380e0070032801c200e07000b03103c1626244601e41d006502c046a4a603081001034510103880d52894141440c2c507040d0114991400103406040c951 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 565959838 1250 565958588 565958593
    0x703050d1803020409050c0405090d0e060703051b07030606030f052a010e010309020a06090315060b040905060613031101121a0f010c05011b0f030c0806061b070f0314 73
    0x41e204024960540610711000784a195100545400c0040c10710250b8500080180104040c0c5482003482e600c43c1c044e03c00b00c400290500ca403440d80c501e046400e803407009030950743d0103007030032610b5440300c409540c4a0700242c043e1161140004c00200f40c0e00600000d18403601c2d030140200907910700b2610b00008a0102303401087c60069401241110035200c400d3b508091074032060768242640160028002c90801a4100d22007031030125050341c006101e041180d1007103248540c07802c0103507030a008462041c0100f10825008000030011016075410090f04500c0c002d101c6458004008d060758020340d0f140e4001c070354181c60400714402660304101310f41e40140c0c1d5810300b4480391001c1e01480b40720891010b0901c0c413405803699010026485160008009030340f0200801c5161105590822350388400c41d0f40c14001030101500d025100d209001c0e4201d82203094480c40c2c7d035a11402d0030400d607504a10300b140781d5180b40801510065004000d0308000f040a090820045c40c25030030701c00302c03070419030020180c181d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 565961088 1250 565959838 565959857
    0x2150c0313080d32010501020613020d0c080d09090e010207020d02041a0a0b0405100c1a1807060e040b0904030c081e0d050a0501061112030c0c0f0703050d 68
    0x700595034403111650340140c00594548050070700e03200400150b43c0480308580300000e402c01d40c0340d5440c028041d5040000c41c8810703981c0d9034001269280f80481c1d40d05601c202c003c1030300005041800002e00c07214814071b01c2181c0c3d40d1b100c1e03c101d4030b8000f070401c0707401c0081c17a00d035020801506d1a1285188011640b0025450082d0310b03000304210725600c2074020b02650b0740300e481c2d2210055000c0d80d041100c1d0000c1044004bc2d90711650509180c002d8010b5522840000d90001a240d00030001610b199510400503000c010359074490741c2a11070001c1043c180000500d50101c9506401d100440c060000354450401d001a01c0003400704803012449002d004080903010302c408250810031481c03405030b021b0156a5101c0071003010401c45000100304c0e02c140b64006c5400c581700d68450700144e218009400382040a41c0c4d9442c0c044034040d060b103c80c014150890441c10308a9101040110362000340c60800c5403900c07414420f01854046180010501a00000028130402205000c0441c480c10340b0715200303491 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 565962338 1250 565961088 565961101
    0xa02120f032d0f0c01061e061d040606020a05100c140a050903100c1e050307050c0a02030607050406020d021501090b01020a060903030b03010b18040f031403040302150c03 75
    0xc074400e00c42e804003055010120650311881150800c00040c0c411001c1d00d0310f5008202c031140e550740020a5200455082440108401c0c008000c480d40070791081410300f803032a04d481402c4d1160034048507200710308950b00d68174000940791405800d00820f00765008210741442c0e801d0660820074018143c0c0860f0342050f8a030740c1001d41c0003075074025589480603c80e82c0c481d5a0300d01a0340900c00e462090340c06003e483c6c546220415942d01ca42820801030300c0f00311101c405845080b05241700c3c04885004110140003050000f4842c202803c4601c001c1012140d06e008a41c0010386030940448001c0002480050203010607513040c02540d008401d42e00090080c0000101c0070304a01c1030500410500d1942d03503845d100703680c5c42000750b01c01003604540c0801090b000c0b0708000f0040d00c100d499960203982000000900c500b00903041d11702c5414a150782c104961283d503502c9011400a131401d40402c15480e0660134404c2083c40154061480b9030000c14800344004a036036820400100780710381d5488180f040028 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 565963588 1250 565962338 565962343
    0x30e0f060f090f010c0f0305070201020a0f210e0a050c030f0a2429100801030f020f090a0b0a0909020303091002012c070b07020d12030902120a02120f 66
    0x42041d03003540c001c5540e40d69003102c40d00d05041c041c1d11120941c20001d4010300150841d041020001c3c3e543d03014041a55004c0043e0b080c0d120b1000140b00050300d0000400c5643c1c4610004422031801442c111113204d20450554240d4056403000b038019046007036000200f080821600c41d03000750070340c081c15054940c400413944601c45281c01500b0301609211141c0034109049804110351841d90080256006074801e10014128808000d100003801035400380c86440d011880c0c5102c03070142d556a5007203a0070f40d5512429181c50001c100d03000351160740007075001d945084000f032041103a0440003458080100c20400000c101e035101b00c200c2f600d4480c10b0b00c050b031400b00442d4070f040401e0302c902d1800201104202d006020032510f0750801c82119081070a0495a607074810891034160741124800c588031106a80d0038401c0c80e030000d612041120300d480000385421000e0480082a0800041c094010340114144a040740124001c075002140d4130000c5241c24025003d448078400d00508a00d242614041da = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 565964838 1250 565963588 565963591
    0x90803070c1815090209060f18010206091c0315030507120b06040c050403030c020111070f0504050c0405220e12030402040e0a0302060c0d1e0914031303020d021c05030a030e0f06 78
    0xc4080345c0001c1d594000d41c540b40d0403522968140002039540b0080490345004107200318024900601408003c580b079400e00081e541c81d250681c41c9246d0341080d513802d0540c01040502d00048820007031100010104000344100b000a00c85498071440940c181d00c1d00b2200100f009040ca440f50789003100b229184c96220f0241d8050725494280800c198480707000589041001c0c683c9403c0610032140d002c124800200b10100407500103803401d002e81d882d81545403519000340d00800c0d4100302c40703d03c15408158180e0021030200c86204001401c40c1032403042504103660003140b8504010000148411410301e441441d1040400354064500c0f001d4995009407251000b9006e01d0281350003140c005d042110a6004100c00f110402a04840f1041c1a44103c0a0314038000306448281d1000504c0307076010001710446441d28100303075400300d00509540c00c04c907a43d42c503940142e07041054240301d4115508180307c080c0049003e0701c0110788985e45007900406442028000c0b0001e90400c91911450440c005800d6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 565966088 1250 565964838 565964849
    0x1212010312030f1d1506030a0210120c020616030911040e0c0619020c15160809030318040b030106050d060c020f1621030c060b01090803070c1815 64
    0x14420007040c094200c0181a5440355030050354074084842c140030750592400c03c4101c51640540b65032a017401d001c000810400c0312243d40680280000e400149400036004107903242500744507101e08030300080002111702c4a2a01d102503480702051007090f0742200940e544079203c520701408844460741c1c5100d8400103d1007558025a01c49440d055400b07030500402042c1c07580600002e855040005074003020140c00ca4031710004d801000108681810008510381840490491480ca130048140300d0181c2c10300c0641c0b0560f0a084144800060b6550038001401c100c520702d801c0d410740c19416402c00c001c90303d2842c0101d10a070f14100040189440da4400e1a400b40d0700014002205c1c03c411909070300342124000468441d000b559560b8840100502c1000b060b140444040c085803140001c0b02e100c1e0f5104040f010300468114510000042c05031b0704501d401d15410f01d0315030704490b9221215880c50304415000c0b0ba240d841c80320b05212036414117009141c030711128542407005070320f03a03401410301c01d186000341c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 565967338 1250 565966088 565966103
    0xb0f010b0a030b01020705031204030b06040e0703030e13110a18080a151803080a06090b0904021201090503030108030703170c160c0e0a09020913050615030a0b0c04050312120103 78
    0x24206140c5c020702c5040020030014096507034501100703d1801091340703c2d000403100480c00001051103400c007031080211015540005040903815600c4c20b0f01c0c07100828070f07041d40c04402003a40100701c803d58000ea06044400800454031280e22000240008803600f0060ba6059800f54040204420010313039141005d400070b8101d8a02c40004038a40b000d00000c0700032048501000c82444109940310081600c5403101003010040c8a031641b441805480100c013807541d00c0f00040d00801d026240001440381e81800c03400002031580140e958290561300b00340d003c01f02580011034007a0a15810503c0a00c000c0d04200d03d1200c2480d164501d4020740c0640883ca1143d80c21a8282d44100000e04048201a261089420203185440b40c030300405084c800204a01035284200403039451607800e00e540d644207500202410f61544c8142c1e080340302ea140d04450640c0742c400d100714031001c2080c12a0080c0210400c0d01025075480c144402d041c6480031303103031034101c4518003006010b01048220030000d065941c0141c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 565968588 1250 565967338 565967351
    0x19030b030d093305091201112b061e050a0b07060905030408030d200a0c0209100e040b0108011b020307122109030e01050403020a0506071a070206040b0f010b0a03 71
    0x10382c000f9903c070f40200d50080710b4400c0b6102c0da03150068058041a681151012840389520100c00c0c2601c8404e49406000f120502804a903181a1051013090207000050780999001034000076003a1607065115900b000b40c0e420152680389043d600ca2000340109079a081501c42c60301841507801e1082207005444566207001840401c03074140111002003141c0360449894a4556024000a240720450564000540b81010350031040f0803080c0d0340042503940325200203010070303000e101410b44000c00e41540d8404002001c244041c1c40e41e403d500403030007103160800317940c1001713141707401c564031455040d000c058034000242100c0e030300200f190340a9a014101062107100000113846400304c11004042c541811003503580c0700d500940c80900c1060003aa200380618007045c00548240c4150f000c0a508005180c03018842804e14500410314944a040300c144040141d0603540d0801d01d0550350b060050304071074144028031840021507904041208010280c0354901580b00300e03030788115005101030588842 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 565969838 1250 565968588 565968629
    0xe06030a020a06020f010c03290a0f090207060b010504270902090403230c070b030411060f03070305010605120703090201022b1e02030412080f19030b030d09 69
    0x40010030394080d0400d040503848800282d280c01d29049452080c0d880c004291555911074007440b0a000c0609201c040d9020b150030001880417548020560460040b0100103422130400d90104003c1c100b800c001612851145018020307a48645180d5040003818401804008414a2441a0524150300b000d1600d4100e03172010000c0d10f101c0364065409125030003003000780b5400440941044845010a804081c06201c01407454090030001c004581e0240a0500100d44980000d58029000d220b80c03c0e2007440d03c1e0001183c07a402194462103405020040c0b2035003613010b020341c6000d400c07a802c1150812010000e4101650001441402003586a01e490003c1da4005e00c002c2c1a61180c0030980f141c00703081802001441c0392003010f10000a40a00c25070f464511411400460010055029618080c03809034140554420f4a07015200703060108507803003c404482001348051031411b5490102d5000144e0040c00b2120b00640f5140030b038020074908240b55a000c0da0503001c1c1c0342c60042044000c080003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 565971088 1250 565969838 565969843
    0x604062c06041401110a0309090c122a170408070816080901180e0a022802150105010c121b0c03060b0f030a050303060d0311010c0914060a090e0603 65
    0x2540c805030006030018011a40b942212060701c410507081e00d80b9150310006080284c0d4881840e0b60140024800e030206100e845001c1d0403503c0e844602d4034101c0c4040044510100450349803510b4081e030342e558464a4440c0c0048001101002c40740c500b065050f00a05c090f204c00883c01c0240024003400700000d8800801036600b0903200e15080e4113a404119408510345120f15034041c0f00a1408145081041401103490101d08002d8841046581d482a1070311880d101c0650040d11703000c007072490f13502041014015a01942e0400304034580c02000d00c400b140504600041040e0000c50401641e24034410210f1600310303071160341034a1440c01185094000c4081004c150001c070004200408071140042400010307040f01000300c02c2294494180d8078040d080650314500c3c0038000f0440e4206000040452420072600340405019082c2454016041c240d00f6007141c1e158017400002c955101814080c14400491000081d20305441c900d00d050001800600706400754071441380030001101c00219592003d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 565972338 1250 565971088 565971167
    0xb12130206071b0807080307020d020d050c03060705030703050a0504240f09080705070915090509031308010e0601090c1704060e070308030a0c052106031f0b030c060406 74
    0x41041c1540c04010700703983c00401201c502c20341c5010304c525980415415008000c90f820030341d000703007044903116039a4240300c29944640c406071018000c1c500d150500380c4081c40842d11031207450755071555914107130f08050b0807224080c041d20003582c54103040000040800340026419045075081d1908000c40d2030035640604400148142c0081c203080c03240701040003030b0f0050000c0502c1075080e6020552900074150841e5000b25104400501080301000300c180c040c1d1140e41c00001c2c900a482c0b03041c0810090060300c0c0480d92080500b60b40d02c5400322548841840000d02401c022482882030b00900780300100602541c00303031459109101c101280400440b40d12070405240d5102c1500c501c156030f0f0605c00b000750011281110700030b0801c12400703402c52291003120281003c000c2c030b20b00007860305842d0f0000c0c903000070500358040c82a20a007070120107103010088500c016422000c070b4030b4404401030504103440034040b131340200c00c24001400500c0d000401028404c1038403401b480401010110100310191 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 565973588 1250 565972338 565972343
    0xf060203091f06090b090f0c0c0a050307030509030d1404060e130903081f0b071203020c1c0906030218040509030f04060509010815030d181d01050405010b1213020607 73
    0x80b80102005002d03858200008440441c541003140400480c14002d000804880456018a0300400150401c00e41e90107080d05019000c101e50181c1c006a031141c0c50b55200c8001580890b10102e610300891904200020103880c6902d01a94520b000c40108c010340d010b00d00416007840000480c0c0c2c0499202d055a020241c09070038418041c1d102281000b615155003600d45da050200d092140d8810780400440e8035003200c40848655240200d5074a40550421140121900b0150204807005004008100b000d980b4040303410585054440e003000508103400d1b55101700103250060200c026000031080c9461030a18090b04e020505940e6401050704511646030703841e055840200700459100d030320074042c0481c043c081e01c400e045034460650b654500f10f003e03040580e15500542d43c088080e8482d40500004482c1c01c40a40441915100f103100c8903000301c400f81a40c0311020004000034a440d0041e0350040003a80811807a12424411480402d8030082c021091801d0346203e040442d1961012251040d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 565974838 1250 565973588 565973623
    0xe0c040c17042916120b1207060801081603060908070c0906050405011208030402104512030503040c090203070216060e1e0307030816140a0f06020309 66
    0x34040ca40034a40d03020281c50a001e0040d40e039440803101d50708983c540d00071421001003900c0030b96844400c075039042032020b2540d1595102c4c03c445625803115901b134017100b611640503140003414104010903154059224420a43c00502c1c0300092441c01400201500d4001502103214091410120240d103c2c0c00001440c145c1940303000100c4004541c40a0142c03802220b0038030950741d8648607080c00da103401001610480041000c200140f4050b454110404035500f0407a041c008401940d1b1400481c00112404400d0030f0812070130751254480703056241d5020103030b83c002480d007894040e8540b0440400e0080030b00c200000800d00340140d015229000b082035060030344d40ca00d85140e0003915901e0071402140c40c40703440d082c0410304901030308041d207484a006d0544130800c00700343c543d1a64511074000c51074250241e54000300100355000c008111003c4405055041c1590070b01c0e1081841c0d00c0201c5015260f0028054400011521030503625001d070403800c0561240c40b050a13160811038a1904450744c42c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 565976088 1250 565974838 565974841
    0x408060f0f070503060109091a030706260405030406110109021f08180309010e01200309090c090a0605031510080105030d050f0a0302131503020d0e010e0c040c17 71
    0x45825030031840c03086040001e884000e4490507400d03a002e000c152500e80c04200a0b140900907010541d100780820314018245803400d104040200303061045607000b540016800c0005400304050350b0b2818240d814540c2c10140052801c3d446d810380b280107a009500c00c20800d40113606560300709411480074640c005001c88100d103080103040c480b4000c4040d200021410100002e0180c4d01c0d01e150600b200013000c00518034004500c0c00440d1007072042d00c4250305104a05001d070744032819070304085502c130340242c00a550703840140c000c000d50000010541200703440100180034050703c80b002504100c40c00d60401540700c2d01c0d00f088070203100d44211201342e0002da640040d10441b55020241d00d048800a40a481000c7d207051801ca48620404200c0000510308010224680d8401e600520a401e00480719002141c2c640c0c2d10140c0c014030440c0410f0000350081003110311001039200e00700c48246040020400003103450b01e0704d61a8610500c0f12845a541c07410303041801801440e42c503400e0003c0500c1c640d0380703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 565977338 1250 565976088 565976101
    0x270903130f060e01170604150b0c031e040305030d02030601030204122d020d02061b1b040f021c09060e0d031d0d02100203090c0603131401110d0908040806 68
    0x2402071920071100003891a003402c856550050782009003000d0703584020211680c0d90428032005d0004140d0f47c4ca001080f000340064103000b048081c02100c120310f006165200242d058040c0e000145d1603500030600c00400003000058000401c07600f08203207071080541c40c0d80c2d0701340040c2c00900803603002842e0110300c0c1082d14100305000c0010b01c0c480318a040c00d92409241e030001e0440100700c846000303402c5030200c120f203000b5140000150880c42104400c550300c5150002c010350524105070224034901820311014960f80c58503002d02555660910000c50804003400034030400c041d07070800541c0120743d44000c000c040c040d00303402a02d100c0c0703080e50031a100000510070040c01000cce038440940b0290341d0340704c40c0c841ea40760104141e8000b0303186600400600720380904c0c080081d0b00281030603c807840380354072a04060b1111009540b06200314141003103190007904118503564402228580389074903284000d424003458100742c84c03030f242481000003600301080ca41841288919080143c6611036101000310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 565978588 1250 565977338 565977359
    0x70318080d02070b0a02090a09021b070f080d08270a06051303080a05010b03160908070f09050718060f0c0203060a0519020c0303061225060e27090313 66
    0x43d00c52040c40b50344469560800210200e02038800c06550003862800c04200680c2581c01610f40c1c0808922211203803243c141c120b41c903007020303580840291f1401c290200810b00c07040c030005960382e0b81401d10220518000c50961140c0554034001e41045051001d10f8640b10002c205032000d03190300c41410000d508198044941c0c036400200c04400140800b80050300448141c094941207412005100d130a548038200c9120085880c25180d030200102c1440001d0b0800d0100020030003000c200014000741d509058101c010741e80f006106905124002522103250000301280f402140c0c050b180c503001c51100c11004403504802094040c6d4188105410300000d0a181d40c460307070052162032a00307603448075030281c240164010303040790031034542089c0300164560400c121440c480c0740140c0d050311100600c0f074080314050b401416005080c2101d4540903c5a5600b1500c900380038801200e66802d411254900317182903004d10182d041c41c192450300402d082110030130544001d24000c403a010312081d00e804c0d0491f03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 565979838 1250 565978588 565978597
    0xc0807050114011e0b03060d1703160806040c0801060e0a09050a1b0c030507020f12060a0516020c0906060708040e090a020405070e130b150a0c020f01080708070318080d02 75
    0x201c1e44684c40e600b003000300b08885004011030f480240707000c0c116503916003000009650f0000940300d164104482e1842c00b072a080043d4403500403000c620440c102e0340f41e8000d080150040c04207001d103190184000c0441d8000e1881d070304548152070b09044814007c1c010543d00010380d44113143c29400c050030b0200b150b445400030f9042155488095004c074404160881c0c4041500c0e01c0034012030030400ca404050b09002003070780d41160700940340d000b1101d00b000b4064500300b01240d18607441c60303840d020300400f80c440c10407221141210b48001c0401203403480028450540241c9828810000021110108070604054400a05120741507401e2480c3c0080616103c184040080f4400d81c50000040c651a0040020100c0c00e10090324841d180d90005c9990b900414890030321a5000038004c1501c901107034000003c01d65a04907a603086002860fa1050004000124414605019440040100c456800740300140d0110103440d000c20400750303030b051032900f035858040e001d02000c20000c1d4810b4004510340041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 565981088 1250 565979838 565979849
    0xa020a0219060909050601140a0c020f0f0a0e090a020d0812010918060e0c04020f040512070b071e0503071212060b0d0f0f0501080d020f010c0206070c080705011401 72
    0x48540c281e49040c515041e486401a10b012400010080c081c81c0c3c01540140d41c00201130504901e00010300d504065030307030440540800045c80120589045041048000241c200c6c2514100da00800040003e800325605016403900c0c03c54500c00a4400c0300100308042406030060b11000c0070380520304082850760300003c1c10300d41008400f4000691380d811446000d03041c8a41e0707150b41a00c001d00382d5808010b007100c00b0070700001c0d20802000712060707038451000784001080e00046541d61460038062040c140241c46802c0d4881d044640200a1400b0001c22a01081d0740701141420a4000c01e460718066102c0b07420291091001042c040b08004500206401003203064650403001d0300c10840e04000c1d242180201c075590039080c80451107000250704101d9120701c402001044d10380390100244103c507401d0740400c5055008505440e074071030701480714041d0301070480300a103c58280008040e6440c800034080e4420004401d00380000e0080e180151510994050000e115500e00400b0b100417030300302800344 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 565982338 1250 565981088 565981099
    0x4060c02010309020a121421070510110d0b0103050c0a05070203151f0503060717070215101d131e050a0b0f011502060a0513021201050106020c040b03030912120a020a02 74
    0x34001c604c00000d8601e80c100300d080501003008c4a0350b400076100e500302c40401c88140c441c031255940c3c508000c1c0546004d28940480072a120480d40980c4403d84214050b2541410700e40300601c00b409601d0001c07584072141c14107040c3e9440f400e07480401d02c2c01c0403445550000c1143c000920861800072078400c0b0740150307055014a01039441c0c10826807101d006561013030220351424040f07601c0000400f8101c1d030203000390050700c0b441c020441e201101c81c10100c404a800084120062041d00c41e021110707000442418522421032405481501c182c06002d0006003a031914045440350400e0000702c00030026a014045c1d0341c0c203000c01c9c5840d05200ba0251480c10603801e4420010035030300a80643e2001c0044194000d000644a0038085c000401c8094841041101500e10240150300c8946009400b502c0310304c0006110b40c942040207080c130b001c1c80440b0348941d0800d81c00e03820f00e68001090b6408617004075812042111340a654131700d00400304901c90720225001c02c92001160300414007280b070328000e441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 565983588 1250 565982338 565982363
    0x40506120601090b0408030d153302030301050d0f060f0f02030f0a11090f210312090a120e0d140d09090b0a0e040c030b0a0219110304060c02010309020a12 68
    0x10710754640517a000343c4c60141d206010300c9011808681080126880f405481141c40d03840d03402c4115207442640c0c120400000354450303000c1104041c0441000702e00144041c500b107505120000c2e00144403c800608500b409182ca5400d1040590000131303c1103c90508004000d0307030701e507168040d4000722080082d940141c0e00141000b100c80c01504101c80c1a1004c1c2403406620008000c01420054a0700d908038680a02c0682d645d10b130814001c140f000e0842c0255203802002c0c42100b200346000344509165040342d800751002580305e2603405651a002d00384500e51440700804109044810503018001300105041404104c101064440034035005e81c2d40c070b583e007584030b201c04000c0d500203251082d0800b00382d44040001540c0c007801a608075102d500300d01c4c0440d0703903929821075070f41c010b4540c0b03100b180d0b00241d882e92054000c000c20182003900d003000f20814035108032680c0ca0740078504c20901485030545014046a00c613030f11240030b031903000340703da8101900e13140d2030fa040c2002c0326022a06040c0084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 565984838 1250 565983588 565983599
    0x2104080d050f060f240c0a080a11060106030c02120a050d0606051309061a030c0c0d1812050607050904110c060906130b011809060203150108180c060f04050612060109 73
    0x6075803d01c0b40da00c5c2c001a010950121000c103519402110b60381064052080c858000074001030040520354401e6131200400003c08407442d08044040c0d00c46014180741a240a003c5a0040f911040042c11060215110b541c3d07550107440900ca42c000c1803c03058901040450710540050240c8800c0c0701500b001035407151144040c2044500d240110360440b05c2042641c850b0381c514070000c6a1005c403041c0f5103410590501101d174a010030206082c0c0110704c4038502c91007015120000302d07004201c4526000d442d06455151a900d03002c001c2c1c0304004110f00056131880c65119a045102c40500c0502c02035510621802016102d00080ea10300700031780101030218180b03100c0c00c03072000130140d084880020164a44444148440088924100c1c1592a040030b87d01056440c40550702c14101000c1000c40085100700040401000420100c90051107001000c449100060300481900098440c40c1c1ea40c0c10803402440d0701e00844d40225030004000030701492200352140c030140039500070703203031306030000e4980 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 565986088 1250 565984838 565984849
    0x30606060908120c0c090103061b0c03050702040c0207080a0c030501050703020c150910050f090105070f090e0c0702030303010305030c0c0a06050703030c0c02190e0c2104080d050f060f 81
    0x42c0300e4408641d01042c0d03880314820303059009041038006441143c50ba4110702001c118422000d910940b20baa5603415510003040710030112405d026403c0c0740c1a0300d040895a009001d17170042110182c01599110100c2034414003c00c100c0c00501240305c04c0380d06154091400c00003a107058007045440e07508240101d91401e020340240d80d403100d03189015041240303803092859078510000f04140c19921460350324039001d803079030720a1078040e0480e4400b800284c68444103582c00d440c400303000702c03080009400b03460b0246684000139000303488620b000c0644a0301c0c0c080e13854445000365031029506002c0000001b0400030004020111382c0b80982c00c2d5081c140b080010000700940501c911008035208100d40c0300041e200e948080c0188655081041201240b5004214202c034412840d483c0c640443d1401d0005c0c4120803442236104c0c13130016891345003c241c0a0082904420303410214a92400000800c01708051441070f640c03001405c00b01004545000154403c003035038203940d500d0042c28841001181800c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 565987338 1250 565986088 565986107
    0x1409010c170606220504050a09140c01080a020c07170c01090f03080a300c0306140619050c0303090615120d0e04060503100c092903060a1e03060606 65
    0x401c02ca08041503e00c44440360f0351a07150302e916070305141c007002c10b10791b686110f024094010340d0320001c0d0368502858964090580318803841c3c001d0b8401503501819a174009961580504c0d60100981c481d8070348050545040710542003035501981c1d20903003282500300001d0303401d008030007661140d00540d0746205150306502a4080603286050070010301024500446408007106008407030403500d242820100003031040c03540e041d80f44050311303a411a1241a810b021700d0002d8280309039402c208010401c001032140c03151004500007010004802c3c004a07000b00c0c180c41020550100390390b03a03840e2650b0b10948030300d0216003c0c0c075850215a070141031402d0811101200d0170180d002444081d0a510f4141c2e01c030701c2950401075100d034841c400480d5640301401408071010340300f2008580b401204202034422101b9400840b045491445884c05c41c240e81000c80c04040b80b050240d0350341c1d89400012850700d6845400074503202983c02100b01e25214003804050880780038481c03c02040752180d030200c403178605 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 565988588 1250 565987338 565987351
    0x406120f08180310060305010e0f0a06180c091e0b010815150a03020c071406070f0206120108100c230913151707060f121409010c17 58
    0x461610050009010000a160401d030069000190b2541000000d207419440140400b485454803010401c0101c2402011a030f40844e00203040c0702128100c150ba0380d0100c200001d840c00b82c0307420301e954442d10807443c10501182c000044082083d102c1300e03080c0141850b020660080e940c04140b44030520f829120708554110165104003082d1504036002107864039611200360300a540c0c0782034410f030040180040448900716100580c03254080261a400c11403158020510541d00c0c0441f1405a41c40f20203c96030950b2104142d0700d02041400401c01e40c2c0142021520b400ca204000410040300019131444003000c590341c00d1140e000340607001ca483c03030400d00403202d2403400000d0155100c50b029020f41314584000e800c00341d0101c058030594003590070f220800c1c042040741c00c000b8040c0030007144aa00340e402a410040500c245407840c020445200145c20a04009109205840c00e018035081403911101e2544034103284d08028810302d000f0151000714401140c2c1e0300360085150f40c0d0000940d4401c0c2c1303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 565989838 1250 565988588 565988603
    0xb06060711040203090f03030a1d0c0607150207081216140924072402030c09010e1309030522030b07050c0a050a0507180203060a050415050a09020306040612 69
    0x1500c481c107020280d040a0704080c013a000309007403c4006c40c010000b4501c681032204e0003013642c241040405500c0c0302c01e520ba14501d81c00252010320300da03d0701411100c0b2035500c40010750580c00007171940c10090098600052819500041b0106041a03154215004000801e0407908421103208103a031180f0002c4040c0080c2c10040c084d02c03c103441c0c400000f00d2a4011a10794191a8200c00c00c8442260300c5880d04944185081c01500c260740080300e0741201284a0720b4045203142440420451a401080c40290400c0f841507a4525142c4401101804400940b00103000d00d000514001e1b1107500811040c06000200c00c02d46001c1000c440100d004803a000041e5050b15218613000f1a040d51200c1900c08503807042c1202c0c000010b10801c10a4052806400900881e034203191100025003a280c0c000c0d4545070050050215903507035000c0c020b0455004960001e03650841141d9041030840c1c690000d580500081000503021009030000d500c141d008940410120762078401154040c456424040c1810307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 565991088 1250 565989838 565989863
    0x20f0d1e031a0f040605040504081201052b11060703120b010212041203050408070e060102010b040e1e0f2b030501030803180109082b0c050702190519030b060607 71
    0xf400c00000c01c014689000e88082042515000440d00745c80d000d0350100c885550000780c2c078102d80d0554040034054030b004c8521950b600551101080b451404480c40c601c4c98000440c3c0078104024800200b940348409000c0303988601c95410090111240d45940501031420511a03c902e580b01007581c0c1c88221013202d2240c201420031030740d2400000d44120840910000708000b003460b440c100b0480005140c0b510b07512403146400c1e400242929040044940928109801c1105981740420588500b80c01c4a05802c0340070b80f0f0804003450040c43e01500d42003030003140018545000e011054108003444541c0ca0604a145684101d00b11042440007902828041c008510000f01620003054400c1e4800008503c40b440c58441d5021030303025501b410118040c43d4105c1482c5e0710b40c00703500342e03490714103030001c0014000210000d0b2031740c412110003e1250500b08a040390050341c84e803112015080240c10904403580000d0f0b403440c040710600082d20000041000106940352100c200d03140030b54890001c0f41c42c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 565992338 1250 565991088 565991141
    0xc071a07051912111e1c060e010602160e040624090e0c0d0317131704050108090c030601090e03070b130b09010b0102030415020a050a0b060a091404020907020f0d1e03 73
    0x76070300306480351100102040b01b444c0303800209010b03c5024202d00d0210140551421801918003503200442d450700305220b40003000360b20a0509615402500207101040c5110054130f180300c001c45680c210248000025004500c1c0c22847c0d110805003448041240c13000e80340c10b404c200011011f0b0780003d0024070803204030042e0030301d00d030485030300031008400180c0040082d0707503900a402410803034070407101c4011404000c69a1700c21151a00400080b01030035003640e540c0042a200e8105003d0669242d8070b4000c400d4409034200100d82c452a0084142d00391410046410740464828600542d40f81c041000420403a40062003080318209058006624082c41d150180822012000c410415030203100c8810f00801d00600412043c03a110300d49030400c0313241a004008030907140303410800c0300f00c1c5440c0d00c000e0702200c81d040307281e000f0b5011500200e50740c0d25078074100d282944026410856000303c0001a03800c50700003c030b814051002d007010100e0605103810440864101d0604090049800d5a40651 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 565993588 1250 565992338 565992397
    0x241903030e120109080a0e0105090a0b0f040503160501020c010203130e060a0b030a0c090b0708070215040321030605011119050102040f061101050c071a0705191211 72
    0x75038800242140c000b07128010103003800c43d10400000d80b104840003034040e1885a0151100f441d11209080042c00d0441a20101d00c0114050041c9a1542000a0044d600b900507000340d40090030003e088039512884050b060020340b01c0c40c4a0079015201c0c488140c0001d40c0040203480c4240029403046a0051614000043c019405021513801844414010071005c1c0e04c0d1004520940c642031010928030365840d80203100d009030b58022075942e0818031800700068012800c0303902032501250784030018441c04c4100740a501c00c0350700c02030192588001655038095080d00d40100015203450811500380d560300191880d86042f66514051303086807086e10b40781c410020080295902590005081c280c64081c6e8003022009604004081800c1c1c80e005803148009028448c0e000c0c074045825824005141e07296581280b40e80a20740c541203081c00000ca403248100181ca204c00f0300c0018203100940c0d191005401076101e280043e140c141043ca19000025504044520709004c4140900108040700d81040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 565994838 1250 565993588 565993607
    0x10503150a1b02150c03100b130e0403080a15030c030219051c021e10050f07060504080c0105070206150105071103060a1e0e070501031802040524190303 67
    0x16503640d41d40c002100c8080c070b80541c07024820b400400a032016181c0080d0441c400501032508600e0070810810980d4030309a80b04c0441e03040c0e10f5556250406141034940c902c0c0550444980c3c2c1c01240f0802080c5648014800c1c0260340740c0c103041003d801d0079440709281c080d590101401c0c08038040320800050900110f52816040201580c60741c2e1500d440002d625103420381c6500c131140000e00034880c250b1602c5a881c0303406031088134400d481e030700148020800c41d070003061f40b0406108010034181c5007060040d08803540541d211500304400d1419251208040e00b000c00005030a611708000a4a0b160000030501d00400d050b1030845002004000111399a50002d101124014500884034400e0b46007080801d000f905200000300301407656504188041d48a500100701c400d0400100d80014200419248280d440038a4046290401a60b6901d01c8500e120f80003900075141404000c20144080d01c04540c00700341c3c121601d110301003107041111964060300004c00180c582501003002900643d0500c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 565996088 1250 565994838 565994851
    0x103020909014a04030c080f0703090b07050709051009110c060721020d062103030609020a080105040c2003030f06010c150f0e0708010605040f020301050315 69
    0x545803a0903000410340051080c0c0c020240d041d12020169200f4200c0c500ba80320686015161045681c518112850750090f040b0038845060820310104090502c904400c03002c59810000d026500c01407410403c0556001d8003045d40003c1250f40040341e44141841144c05998001009107001800d0490003002881d01900603002404010750000c1d40b0409070191040310114000400d03103881c4002a0700c1e041600040bd8076040244050500380f00c041d00415408a000b002130300181c603441c4003420302008202a4201451084070b000f0100b8202d48003110b0305503454407a60f014003d00d03558808000503405a22000c001103804c0b800141300d282030950120a94075801d15010401e491805010080b81d90b00790070301d06c0d1b5030308000100415014000b120b90f17048482842e0059664000d0b4507045400c2d175448003080b6a4a0b21410601c080044507002400084c0d000400e0300c02d01690381034520300a01c0c09200d820301881c1841542c6422085500c2920704071280a00500240f914900444a0000004186 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 565997338 1250 565996088 565996091
    0x4080316211a0f0303041701180b0403020d090b0a0c02061e27011218230106092a0c17030108060a1b0c03020c040905010c091202010903020f0103 64
    0xc140801c5001051860194004640000c81d6040c48040700c000059911207103020b1550003205959a480000c1103d0407904103190200403030703540d02c01d0503024191003281d140200c521100c46409005118030894040c80c8a40c0803201200e90f0601e080d0340138001403254a00020f0700307202d40e0b08140c1c09003515010503880103200034078080e0003025480d2251035011600100c0d0b440420001185a2086400c6009103125025107441c00c0505000814a1141c8210511100c0e190414143d40042d18500e40074040d508ca5001c0c140040740d2401a80390781c20090605030650b0030b045c000a502440ca120300d40b0081002800c02c0b08440340219810380710700d00000c4103070412000b007000802081c15081004210b0781403148155907949800d0300b0f6403400d000070340501d22803441c000356040e00d142c843c000264900c1043c1000f12840840c0c1c00c09a05090001001c00c2e045400d101203d03081040c190f01c881032a0240382c50f8041c86544a0042030704800240307400901145441600b8005494504000740382420b05140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 565998588 1250 565997338 565997357
    0x40201020616092319080304120f060e0c0418050c0907120603030c020909030307090e181e070608010609090f020f0c101a03031207170906010f0e04080316 68
    0x4041102c000500140b8413003040702c0400e40c2035103041008407441a82502006a0841c201070400f52640310f540700d000790800c0b502409504020f0301840905401d504808204403c6080c0c2035210f450300780c3d01c2140381c81a454480074201a04101150451a80c2c100c4010114400880140000350201502403414044054a140b0454160740030b2a400f543c40307540c580302108141c2c0b0600c46007500c05811403405070024070401522503801030148003220020108000942c51300010f0541c01080311a07850a14001c40c2c0840d50356000075002400e1039110241220b039110350701c0c10100c3c0d0442003802440e0014a03100360401590314903400100f0001859000149400751800d1803440642c40900d848440d50400407031240507222030b1180444110301d02c11100c09801010300000d403a0320890880c02c3e0a21302070008a601c091258040c4920200c0c00ca400c4039850034800211a0703280350900c20401803903401c40700403802621080344140100d07400f20341103085440b582044025008019901000c11103070304e1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 565999838 1250 565998588 565998599
    0x1150909080c120a0206010e070f030f24050f0612070c020a180504030e0a120b1306052403010b0604140d0602030114120a0209010e0c0708070605180604020102061609 73
    0x441081c0041500220321360300c80340008003a062101c160701c0b0804068128041000d1341d500000880a41881840c000915484515000c002001c01d02c000840ca20483c80e00d01c0c070304070702e0f2139a0030080c1c0f441201c0b10324445600f0300410410788141e5803440460300d03404010035141d038010314005a5040c402031200151544409a12500b25808086c1030b1140b03484400780414142c00024880d8809415240034000d0360409a40022200b86000c0041c101a0b84030001030038441e030190600da01c3e03035000d2030a1006040c05040d8621100c0700c98007e0f40000c1d402247c0701c1461405209042c841c242c05400d01c1d0910340380042e011403294002d25120b420001d00d205100c00103507035200031800313866011083d501c0c05420005001900040c106015890350046044201690769541158115580c8188003065075440d196079541c81d000d0100004e010840c00701c0c04408000a42d001540325154200401500002554420344c4d580020789002e405a0007003c0428100f07005105900c1e1181000c0c00c12924250740c55 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 566001088 1250 565999838 565999843
    0x150e01050c121204060506040b06040b07031106310f170706090b090f160b0325050a031410090b0609120c01260a0902120a0303061701150909080c 64
    0x41c02000c01c483c4007081004202c010703c44c2a420820a460401c80c50780d2550106030248076500071a00701c1174001c00d065003094030800903803800810360001d403055410700d111804e0818400e0036000c80e4921034030720803000300f50f0486031845289070000c0094100007402e071075004804002202240c1514420849140820301500617164407501c1140b0200b56440c1260f840341c100041058603000d1034200d000b41445824020304903806841d0300001043d52a02d030082d0500c588551440d64140c14140000307002280e94104001d05501c480a423401e029030000503041c9035103032004030f440d610000c8900c1c80a2040c41059070050b042c581c4080d1800d4a0480140b000501c9400e0300c180c0c00300031754812042140c15591055020880748450900b804041c50500c400b50a4100020011900c0b0f82d601c1706010150365600d00000b00c03000d02071040e2006041c05041c000d018220381e0203144100c500c900104151804144240c2048042401260303401034204403101d005800c8501c410b45a03400c0078440c161207080107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 566002338 1250 566001088 566001097
    0xf0b1905120115110d110705040e06041101020106050901061215081c090504060e160224061908011a0a0b0403060f0207020402121f06080c0d0e010c0c0c150e01050c12 73
    0x5e64843c200ca42c03082108251818207a6001180a642444140c0074211000100150440e91081110386525000d0340100c3c018000b50b4403480e801602e18000164403a0031080218034020b4140c02440070b1244503c0d0006002a81e229203c3e0540c00f50750410040b0540e4030092a2400040c03806480059071000044c0585d6000c0d0803c4642841000c14010b070508141110780308101d042c0090001815402d01e46000704400e2030840350b0080381c002c001121981c600501c40e0079403a9000c103072010306844904540c024207001d03c01040542035070415102d10300c1d24005400840c1c0e80150b58514003030965031b4201c040c100b904000065135400303210460040c0d40e81e0001d0424080348550f21b41c89854012241c0726a596015000c082c001c2c0340e6601800402ea1103400154000c10382d0110a590300d501c0d20a1400510242501a8070b6501c2d0a50303224000e9400b81d05502c8031800303034900c2c0c0b001d29102d1401340c0d2032650500f0701c000411801c20007100d165004102611002c80307003a0503501038404160900007154007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 566003588 1250 566002338 566002363
    0x204090209130902210106150806040b0d020a0b0f09060408031c1407050906070f03030b030f06151c061505120109020d02060c03040f0b190512011511 66
    0x801040a110a06141d02402e0310a60381e8901402800c0741600800c0d1000740164003030300300c03e01074103901203409001d401103001000946004664080005401403000d1029149039203d1820180e1190b1540b0b84a401d005001d13800400621281e460180c170001554840c03000403520388018030415140b40c4c0c4500c045d2006000300400385d99111007284600034132020007255590307030030b180ca10400d603610f03103024015074440300d141030440d614121080011064010290014041080014500c08150745a002071400380d0042e4200da140040240c139141e25034000311000d003150100a05a0b110b2440c10320080c2400d0001210301ea6a1400d01c1e4440c1030540321244108030000c0c1703d40104000c40d090440c0100820a1000c0c006c01c500c20070ba60000e07080c040c0d4900701038410350001c58142e5440c441170044400a0800328505211244d46007880070558100c42c0051004202103e41e0306d556500803000c5541c0316034030801030b00b200d070300341840b0002d245c60244044041041030341e8240f80c80001005008150349 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 566004838 1250 566003588 566003591
    0x803010306060f03032106050409150606030902030c041a27010501090b0a080c0c15040b091516030f02030112060f0b0a0306020906191101051f09050901060801020409 73
    0x40c11800c00300182e9103140c0c4110a4a2010a000c0020903407100c84204803111042c03042c4030300e40c0f10705003080140041d9001144c0c4249002c50b550300b0400940c08000c859030b5401d6007444440d988880035011281c0c40780c2d000c0c0d09034105644c85295490980e104441456000300084000341d211004107850203c12084946500c0103258003560808000700b030f060041109107858858035050103e00e850070700ae00580308080c81a044085803101001d502560040a441d000b200ca00f080603643d2941050015a0300361071198810001c60301038a4081650603050340c4800950480303031204020340640c41d18812001040560324030305840100d071580029070003402c86541c881c1140142e030405104892909400050480c07603e82008400d072104035502017100e0300070800503102c0108202040c4030380308580588200550704002205019001300f038000318020a08001c020ba9961401c5500f034209400240d000252802c410801040d04560000c950000c1103e0012416650307031080340d4260b8206401c0289003d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 566006088 1250 566004838 566004841
    0x501020426060105032a130c051c060b04180b041d0c090106090501030b01030608030a051b03090d0807030e04140a11040b03060d030c15021824130e01030803 69
    0x40720708020150140008030060075004103102c10008042e910040384842c2030510f00c05000169a61180b0305052804011092010329480c540040560b0f1200300c9100c030002d000382041040f811644660400e54102400300c1c2e140c00d044c44010364840511200c5005e4503170701c031552404941c445001d0302ca105840c12008d48880d0f003002000030300700001040d0550080b06240010051254054007482c12200f081c00c0016586909a0048001e0300702c6400045c1e040c80300054079540647d00c40700070205103013805007031080041c2d4100c80c1506c0303200b00186c4c5a8808081d40d00c1d4800b048402c4010200140302e81464840c071030300000850159840c44100483c18002c2c042000440980342c0244204076140c56426440d290401e80c0b5400e00d80000f50408e07005400c4501d414041502900b50544503507002a0800071480c1c542460384040d41c0840c0d404203a007840c0020f00e440b1818041c6501d03007a01c895010415000501c8068145035401c02d8001c0a42003605050015a2913011006c1c140654020740c0215902e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 566007194 1106 566006088 566006159
    0x1b0604140d0c06181704050f031207080d0605100201090506060a030c03110d200a05090106080f040524090705090108070308071a340c0f05010204 64
    0xd0f45c2610545884202e50030303000e841140c82c21211081b8902503c0140364403075260a07031800318054103004250000b91000054201c509201c00001609036513140000c0300d030035400443c400540d560b6801c903001e06c0000e01070315601040c15a000f0312850f06e1542c81e207111081c1e500c07001d030110030803040c40c902c0340d83c0c0c2903103440015400400c0340503001801d080108120005240b140c2c131078560f01c100040c542c104280982d04076916500d0b07010341a80ca61054494107180104121014080c10a4075181c1b1030001c442d035403000000c19403145561500410380c510f040c1d881e400140c030800581c0c004015020300052594103803a8000b02843d2034190703504e81507000c5d42114580d05000d04200e03080113094a1035a07554000307881d65080c0d80461540c03c10704a40d13842c8010f03464a000845404c0243e0100d44c01500c01d03d80b49110340001454217136140c2e1005507007002c189210038046000500c6555 = true := by decide +kernel

theorem cover : BRFrame.Cov 565827338 566007194 := by
  have h0 := BRFrame.cov_init 565827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 565827338 ≤ n) (h2 : n < 566007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
