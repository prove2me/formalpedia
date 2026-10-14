-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2906
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:06:02.578889+00:00
-- url     : https://prove2.me/submissions/b8b0171e-9515-430e-9b08-6315d54f5b68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 522482014 ≤ n < 522661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 522483264 1250 522482014 522482039
    0x30c0206160209071d0d0c06080901060308031e130210030e19060b010807140a0c150c031a0901030209070e031002030a1b0509090105060c0f0102030c071a10 69
    0x398030540084001ca00c0325070001c1c90a0038120f03036002c00103242070150702c40490304030f24903980003034140d03168580700180380c0f601048150ba6000d00f000344000b20000c14501e02007540b040d8011504182e85c55187c3c10701314080b1050031090078288203031310b18080104d144030020a003605081d41c0c2c01072004644600c034a070198040c000608511006003d8012070242510700000a07540c014404d500010313050500d8030026004c601e01a0100041121140078220181150030481e183c80035541070980c5400c407280703081c540503d505010340c0344d01810010b05401040e0503411540e11500c00d215001c08455900050040d444424413019520818400210701424001c0b015415840001b5091b40c264548080050342a82e20a541c4864500d9480501d10085030383c101c00500c0003049880c180d40780000300710000b640d1b080103001d42d43c455840054482003144c03042090380c3d2070510700e0f0000c0d900da01d080c50009000750850340094400d2050812412814407950300094482d4821210032643d40e0b05050014042c5d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 522484514 1250 522483264 522483277
    0x32a0102030405040e010b01020105070c0b0415020f0a08150d020a030b0a09122607080f0910090615050d0201020a0f0302071d1b090307050d15181b03030c0206 70
    0x1907000030440403540707880798024190440700d0f0b0030020407101850b40c002421510024640010054128901000141001100c6402c603800442e00b07444410b20001c800020301c81e000748c1a6513000002410f009164010741514401e011100340000140c2c401c405014a105144000035400000902c1c00c1c0005040941c0321a0003180071000024005020b64031a0400c040171091640031480c0203000030300759402541082d42240c0008480722503801c0110020302041000381c901c55940710395000089000c0390400c410f1040800004040c440d01c4d40d2400e000c0000d00101d403517024610122903020a0500b4a002d416600340c0c2c0c10f9000381509046034440d51f041c08103102c030880860150301c1c000202504181505050103000c05900a0320b414801e4080761010440a40420504400d11020746241e0340416050200c42c01543c03110f444101c1c0c0d00c1d2803030f01c00781c00c0042003801e103191000390001c0d010040c103031025843c402c004000c00c901407800f43d150719050300d01c001400208a010f88000504104016214 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 522485764 1250 522484514 522484517
    0xa08030408070602040b0d06050f010903030c17180103050109020924040506030a0f0e0a03021b0112020d0b030d020a170d0e07030b1e012412060306020702040b032a01 73
    0xb05541940c440e01aa4403640c4840000d000102d05800c405556116440050104a134804685020400040c1400203235100240c06e0100c0041d0307035400d000340740c88090b0b40d0f000000e070050342d945010500e02d120305d0300d038054084c0020316000000c1078410031442210304003c4010b02e0072121103441d614440722a00b4800345888030150a1100141503150007003d14000e00d0800c0700801c901590841d030400b220309981062055902654005012035008601240ca800c504064940001002801a40c0d2101c01c4030010940920001e500b000003026644820340721107003241030b503108161b1840700b01d07074644c0c0b030490140035248501c0f180703100203400200a141ca28100403010a082150300c02c111300b0402c8a42c401d40d401003c10301008582044440d40c0c0c0c8464404203103160055040451100300c0e07000300c000c40030b2510905402c10b9016401038503200d03208202c001d803d000142c1c892402c040a500310400c101d0081c0d080141c0c00107a4034000c50200440303101d1842801080c1002045803041a0007040640d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 522487014 1250 522485764 522485767
    0x303040c1707030609031706010c0c0b030606120f15060c0d0302031e090d08160c0809030106051f12020301060c03030b01140d0618020a02030a1107150804140f0a08030408 75
    0xca0764040c6625140c084e4071f5800c004035032114209900c2100800080c10070064865140005031090000c07010781da100c8101030b440e60303a8080400c2081c41005c44050280c00560200803000400c03050040c4149148600e841e07030b001081041c0042e5008030b0b107070703503444d5040100c02c425000e00c26405140d00818400340140040102d60b0720700760510090321842820742020207000c4c0c2c0180c100c0c1c41c0c1c0b5040000c0c0288464000143c0358010141c01c0000e1004010020014000c0300302d9609400c0f480c05042c000b0581c1c5c1d40d0303560940f039540c5c00720380051228010a4501c00b01c0004a00e8910a4034100d03010340e100c600c00765225a030100c00400c1e404021505004a0385038400085c40e544028002010000348005070850400c21041e0300061160340c0f0607007941c0100034184c07010f03a010094600e0110107003441c103d100d00000c0c1450034000281c0211105103087d6046032402036006414501540c09018400340c50070310b9103001c41c1c841000752030200d015800302e1682ca0029141c2402158840e00810360726 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 522488264 1250 522487014 522487019
    0x3070e03190b0f01080d0c0b100503070807180212040b0a11030703020a23040608091c03021803010e061311060c160608060f060307020a0204050405010204090e0303040c1707 76
    0x8840d1100d0040042d82c9080e10301007000311003804202ea0030f000d8140c4000600041c0c040d040001c001e016040d40c006c140144203000703c0d8800080000410150400034242c8802e01d862710081a59202203114190801d100d050401c007004407288211901c2c0a10100c1c611003039a01c64948100000c409841114501d0703465124800f8100503070040d5000e9600d40e9009681d560304090020031300d02a40f0000060740c030300c866816000042090442d000c072031440c1894042c41c0c0c3d5818000d03082101d60301c0c1d5003078185101402d08c0074081c3c1c582d004001300405081d44542e803020010916080710502c00c00c545042e8041c03800704031710a071460584003403e4801d03131511040403102c0001c0b5803d40c00100d030b061a541d1020b282c1c428840344025070580038003103520300344040e4981000062004111120100d0052500001145c0c0591081c03041c91441d5801a10901480c14540307080707030003940503208856141d4a03042103484e800b840401140c3c000e42c0c01c003103905111801d0a404201d071030b41c880045072480c030445800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 522489514 1250 522488264 522488293
    0x103050606220f0e010f0e0402010207030503070c0e1612021b1c020607021203130305040b0304030c060c05070503093304060e0d0321200903150c03070e03 68
    0x180d02c0140310003520480d030034588a0540c2421200d40c2004010840413401070000901034800e01e0304443d003c40c010021611a400140e0411105800140c228040002e1080521001c5013699080b15803014210f0544d035181801c80444842441c40540001c00b0000c00c00540100da4010b80f4100424102c240348a00300703d0100303403828640b50135509480040800400d6050b40600a9a0b88038a050020f44002240b0720421201440000e04050a0f064a840d840043c140b08100742c030050052003009a0b62401d01d400c0c0a480c1c0ba0100c0e80885000d420f1a0744500d45500c51015108510751040055080074252000c0110710f030380d544241c51201c1c00328605130755034035503000070b00060329035540405686a04040c80204a040800c800c180104442c0c1c103c0f40c00240c5c091000b01110112090030742980300030180d0003020f45108844180020307001e40411201e030110000412280b8070460803074658a00c024070100c035210040f1105e5605282c14000200c804e03024202d0038560660040c20b40d40d01d01d055500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 522490764 1250 522489514 522489547
    0x4140118120b1602030415050d0915050907140105120c091507120905060a120b03160801060e040201170703020c060c09100c020a0b0c0307050d05130b030f060103050606 74
    0x50354401404418440581030031850f1142c0c0001902c084c40c0303071500f4800204800d8103101304140c1088000640c03049043c560303520905035035038440c0d030403003401d441d22100300082c0100340d469026034000c40ba000290740035202004040158180c40e01410000f840d4075900071101e000b804100042401c12404000756510108011400c60990240b600c0d440e0508040750411864070b0950240101d1110a0189035141015600c1124413460401038406480b981400600241d02645405200c3c00d07040400c00c0030300018020a0b118410020045103641c2c029140040304d09640281c0401c1c030070444561140c4003101010760100032810054542001220361500c0c0070070880345a5010400070a54950350700e403841040700c000f103692074011082c10071034000030340110181c0324a569004c1c0004125a50480a01c152018150000203541607042c0c1e1110142a6900c09015440c88614040c40407451100307400550340191003041c243c0703482d95034000055004141c0605003550203242171141c084c442810300c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 522492014 1250 522490764 522490799
    0x101b0215031f0803070804121b0806070f05160f1e030309021e180907050a0803040602010c091409220c06120908180a082505040204140118 61
    0x298200b0001e104542e00811500350b4004510341d4004002c8000441e00440c150740640d2204403009140d10b40394074200c00040328001c51a0000d8520160000d9120004244c1710f00c00c1c038054540099003076220400f101d003071081d40785540200300004c1107000402c101009403036107035100b03e500402c20080f8030803115810034903540403000240ca840030a400c50074560480e124902424045400300b0001c0ca0006907440c00400a20840c180c18400003500403d0400000000b400060001d90405441e09840c6860390300601900000d0344c20050f4019000c2e1180c2c0e0204100d9091400e44850b00201404001307600d40d000c0c106c8800c0c0031510100c840e403250000402c0710118450701d404400c091502c44082c00414454140f1003813545804400c0d00881c0c662030446458944050301d002d01d0242c001c0010b035103409540c00c00364452161400c1207940082040c0e00c440c11700164507030320725116900c208100a07031286010703c1c1c086110840c40e00e5420f5002d0640a480704480e10f2600300d5451b1501510a402420803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 522493264 1250 522492014 522492031
    0x2031309060303030609020406020303040201181a09030c090906011a19050a1701120816050303040c06031803090b18040f09031202030103021c03110303070e0906101b021503 76
    0x4000070001c03d905442544014190100194106454244081d44a000042000c0c0c103128901c1c5040c10200115104100034011f21180c102c40301400c030358a0303240c40d040f06001901a11070030200c0103c80c1380030031489104002000c01401c0588c24407002410f08010000c0e02200c40d02c0c184500940302c450340610062501d1155185620380c203861ba402401908002002e00b641d50150006001e44506465105030b00b0343c004810503070302c40c00341503031030403108250704068403900002c800e000070400383d03071f0380c02c7c0803a07032075540501c084001001c19100030584070a0050200790003c10410446040c82e01401e40b014030b00d03d242042407061404241600d14a45400003103556410921041641100c0d908422010a01045003558150f45c0401c01c02d4511301645020140390850020406101c2c1b04c424a0505910b820b40c4d440f41041d1102400c030804d5042c881d0b10038080540090741c241058914962a100d05e9030341e030075101421010340810500e4040040c2e80244001c0205c8550040394002140070741d564 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 522494514 1250 522493264 522493271
    0x10308030916051309020a05040609061707050105030f0a0b0d032111070206090a030602040b03010f06050304230f0109050c0922120903060f06140102071a0a02031309 73
    0x296003402c100084500c00303000401084240500c0d02d4400395865199040d1100165800e12800001d4180c0c0f04d0350b00c001e51142c00c1040209410304c05800403401c507040c52442c2c1c01d01003100c072111038a030b14441c010b040c0061400d00c0000c2a07a02980001a00603004403400903034200c1e54008558224100d14055000c2000000c40d01000c241c102111032418a00f4081003100075078223240712004d4400d1b02d0002c0e100745404110b581203035031030004040040d94006801c555481c2d0320b0b070041031039400910801005603141d9400294450069040740e2080c3e510040142d608072040144007501c0d83d81100c000e1081c810203580944480f4240714400a4500030002480d459504908001f5525030040c445006444a440030742141c0d00349900540c049540003228013274440d07001d902190080525840501650308010003d00c0d654001d44c000f005440c000c03a03403918003a6001006a994a14610407c03401d4000500b81300c02107002c54011b40140d220601c1070760b01d084c2881074401640800c030780120601e03036503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 522495764 1250 522494514 522494521
    0x2193b030a1112150105060c1501060f090b0403080318100e010f06080a0506160203090a090b0103150b0a080c0d050403110723010807090e070905010810150c050c030601030803 77
    0x706032103191091a41e03d07008000c0d000d0b03614071800060106100d0390303014000100f5112001c2a0501c0070005516880400d4002c66956440052008404e00a8900480d05144003c90046c2110080f2402c3d03a0304603c1c540c0c9103458084000c1d2a01d850310f0121002401440104120f9009078020361201c0002e5400209c3c0c550780052401c0100c82065100e207109500c184c00404c001200456107540c0500183c0359880881e4075000c06a003548142909642c1c00704600c140420207101580c0315a07400703d0281e03820030591001501d0080c81c0100c9000303208288005220040c20380c3c1c41036411035071161088140c14145500140b16006461043e1800c40118003a00f40742d810f0703da020480c07200204005090b03510076402444a01705160111b440d51410040707028005221a8020001003004021580103241a4500100c0091500e40c050150600044c0000040740d600c440040380e40096410410b4003001c071215006060703400b40c2659000300c5940c010b000b00a841554140421030096000381d90013a507902c1c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 522497014 1250 522495764 522495769
    0x60726090901090507080c1b1501060206151e0a030803090c011d0a060309020609030a0302011505010504051e12060108010b1305090c0906060f0d02193b030a11 70
    0x10305070820f003103282c980420804881d038000182174012010300c080c00da4500c00a40d5000c40352070b146960000c2485a00742c190542010702106038126410759082e2101c5446803540c0d500d455844140c1591b1064511180c880505c000702549644607078010010190740d680ca40d582000c0e608111081101d6400005100c5050758101981c0c481d803548986045d04403e2850700010280700213801014100b640d6000c0352021500c1d20400c07600d443c60000e0440d01d0700d1205103130080c080c199484001c61004a840c200094650041c000d9400781c40000780480c4140c4284801b09a4603141640f845510183c0d0b245200c18030501401014003030312004001166040302c14050200c02d079a408182c60442d442c0004101c01e142c80072601c400d060b4800ca82c0d05440352180400101680262861000c2501000800c00f03022000355004200125400a40e81c144c0d54041006803809581c24200d140c400242c08401000c00021889440a079080b0841d100280030b0401c002c030789080030940d02100d100c915141c400480b403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 522498264 1250 522497014 522497029
    0x718030c060908060c041202040b22060605041a030a09140c090123090406110d05060a0b0a02071a04090204090f110c030d181b03032c06072609 63
    0x1820f510008114078140110300450500c0383d4420340c441c5910a5401380d0440d562a008103400240081401d1041a9007048000450309030b840e0714140f940c0b40039400143c050285054401300c0c0d0301c10003101209104511494070a600c01030807400350303650310000080021035040b200300c0881c0d8400000e0803104002e02c140401c6041c103820012030b00d81c44664008480701d65040720b8600100070b40e0117107a00c0c2c0307603450040041d0103032078441050440042001c000995440e402244525011076400b06103960f25182d01d140b920801c7c81c014010b0f00501c01c140081030030300207098004200c5100c92458550b40d12003641c103d81180d0803101055407503c2403000c1200b840d004060034555401600d0386400003264481e50303170f446070110024802d61621800d480841c211090070304120303040003542030f0341364042c0e10a07810020280800c0b4045404070112140714480d00600301c10303000c03000c40e1078800c01d140c400400000d034104080880301a20041c445903502002c0200694041c50185011900c445c030360307401c12061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 522499514 1250 522498264 522498269
    0x1060b03010b0f090f0909161401020a02101814271302060903030f03011a0c0d210f051e06031203041a04030206100815010303080718030c0609 63
    0x9040500c01400001c0007401101c2249403102c01d00b03591a0840008141784a0b4040c0c1c0c0254840d0601041003030050021820544400d400f13080c541d1080d840b07914900c86082c11080140c01a408005004014100511034101546171410700d12071300c52000e001d5101103031003a000072a00e2845507240620310300b40b51880301085401a0300c075004510b9000741504461200030308d220085507800c0c10302800e6407110000c885814201400340e9a44084400454001c0c5e07100f8854200410250160030510341c10389005c0d03564048a00d0081e01040110500c100c50b4400c00541c14034485155803d01c102050340ca00c2410040c48100e50301103081d240c0200d01e500c00ba0b00040c03860004441c0c8208210207640e01140a030120841d800f00103440e0f803201e080c14503039040144003074182a1103940510090640000c7c3d80c80c45800008928401140c95046039034a80c000741d19400249040c0c0c4005000183c001e9514940c006002d2902e0060310340507103034901200c8801d40c81034818075500401400400d5008051001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 522500764 1250 522499514 522499529
    0xc18112a1b310b0402071407051507050c01050a030b120109030e0d11090a09080c060426090d020f1009030c1e03030e03010b180f0906070c020d0c050901060c03020106 73
    0x2500c514460758806180260b03204040c0d8a98452600c5030300d6866a050324a03854000300360203680e51509070255952051400f95034480d00700c1241c3c043c600c2d40e031b600441c1c11041d80b05015000190b501e50041d40d01e90060000d039020701d911912855500c1e141c0b1099440700b0100100003252128040c1000fa0060180010b40b40c022400780ea03844007c82c40c0f111650110b118141c0e02c560040c0e90310742e01640104515100204206400100022501000500d840c012406428400305a48669030a01030310074440d4a03800c400803003444401c400d8500080c4004416002505034040d024002c0b00050b85801150503000105001a030140144103841000c81e0141001041c082e00c1c5190764442060b990388a88402010000f400041c03020031345082d040192107082c050480704181004850803001e50134216110340c0101c01d50030000700d4035000021130601170203440d226004800d4094080c043c9826010106590f10807079010300003090340314109018000c18055482d012540d00c0c500d00203095820a510001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 522502014 1250 522500764 522500809
    0x6030b09010c031b0c030e0a08010606050c0c1806040b12070602070e060402041a0a020a05031c0c17010b160803010603021b010c0219060b0901030c18112a1b 69
    0x2c20482d0080383c191700c2140c050400f003180c0245800000d229051a4104550b6542812000626950840082c00d01d651107442654081100741050161a0401c3c010641c00c07603d4801c045a501c2c14071b688040f520201c05040e60912031802101d451822480703900c00801640000420040c4070881d03d001d0f50449011101903240a203441d10b0482000506030014240c03c100144540b000c5000300100040c295001c41030340c0d04c1e8040c03001c601116603198100b00c4042418555140c9000f44906d1004440d81c83c2141d842603681d007044001034035500300c0105800c820540d00500004980d5038406103000340750f04e07038000d81e0701d4101d6044002c140c044030006403001c0c0e040844401c3c00035004212500000d40742100c20444124074203140003c2c2c02030a5405030403d142c1c0d4008418030900803004030944060700c00c1510070008005001d001c8540c01181d919119106209282c5030190040f410301181c0402010100319022915596040034a80e0352490f46c0d03032103600d412400030f05080b10480140002d500748507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 522503264 1250 522502014 522502061
    0x1d16081005150609061603030504140f071e080109061d0307050a15140906010509150f0f010c02031510050105040e04030c1e080c150106050f070606030b09010c03 71
    0x1080a00d0302c454164400c50012071000d0060701c960050f1085000365810809041c00b036428050000c02e0103503005d44803400c00b00040f06c410400043c203c00804151001021807500d4511102c41d841985d4102e0700c2d240a0080c00015280002d009507050a400380400180c070303d91284a10720744009030030000d820b603002400014003095020910110032900320000e150a445c0792801400189190b09444140b035211406010790000c0000c0c456050310340c15260421a52643d200f1410007002c0b6200b003943c44410716510303e8290800f4595900c2141042c1000c0080c2092030740043d0511401c601c00f21034040c0c2c00d80030807207040240d12041d0000c00085c00c140e8a081c4c18000c015801000040001c0d00780408541c1d014200691411262846120700c1203450214881e86031104c49075201d55980101845610f4240700c100100c0f540f040c1c103ca502d80c642c103140160001c40b0308101e0b0400402990660360781c04000000c0340320030503050311610186000285400c10424094102d40c00d10010924640024404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 522504514 1250 522503264 522503281
    0x10605010207062106080c15030112150204030b09030a090f03020904020103021602030106060c0515010b161401020f1c1a060c07080a0501020c0708150a1d16081005 72
    0x2002520101e10700324440c4d480c1804400c800034014101d80c81907520380000028800800700b00600c0c480c108a854104540c6034086072212400280600340c40611810b40703030f1740018002d105003d42c504c0034007405401c0a0b80c13915403508900e0102c1d41b404c80d54000180303031103413160300160520180c01c0c00078043c40d02d141150040307214650000c0000707040c55400a00030031810100103080810960040003400000d4a60b440142040b46010080740e4600c18800200641c07492241185d05844c1c100b040c007400e201c800211082c902c51202400e6902520074821001c00640a0004181d20f18480c0962651070780907501012136015110b000c0010140380c1022080710300306103030400c02d10301e10440d0b072903445034030300c004c4070382004c140354000407031403042d500740c401009010340140c00100b080c0f1702030300c10995603518180d840e10881900d149480160b5030005800a9503036100e10048450001c3e402c540c448600704540c61b145002445600071442c281007048034a90401002ca80c02c09031410034440780c01c00c03040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 522505764 1250 522504514 522504523
    0x61f0602030409090f061a040b0d050c091807120c0602010b010827060414060f040b06010c0c0b0a080f0a020f041211090a0203061f021c050d0207060515030106050102 73
    0x350f1030318240c60f10041030a110100c5198444690000d40030014400006602c0200981c0121894040c1e0f04209a07240b03240381c04c902182e0103982080103049040d4000080103174000f001400074040f02e803103c1c4041000041040440040d000000301082c13020003a0410841e4911203911400c00c43e0704013481c0f8601661700101c2140c2000c4c094240d840c0b004596000766800c10f807942c2c1e1807103861040b60208414400405415081340f04000240c401e161245041710300f112000b00c40c041d210401000100d000f0b54482c540402c0a54042c4000911542d01d9825414541c0c1c0002c1e10324000038450400e1115041c4155078098000c01c201104514181200c81d0b55034043c01180b00b452080c00040201c01c0a00203c894803001c8014001d0800d07641e4940b02d07052000a402c1500c0c1c00b401182814421011070041a03050039154603503800411034402103503846007204001106a004000c1c2c2407148140d00140d07030000d01601c620840c004201868103819402201240d100e000d8881c0c0c2c10007904000e02d90b00801e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 522507014 1250 522505764 522505769
    0x1b03050c0a12030e010207180b0a060302090d0803060a050d0f030305070206070c0201031d01020c0a030f09030314030405010b062d03160503180d05040302012303011502160305061f06020304 83
    0x1000c0154135142c40050f41030403400d0740940f080c0c0c031080c002d42d5800302d80c607403102042d40c10488550130700b207031141c0d0220120300030681401c0c3c0019008007c0380100349a4005180d0100c030060281c9005501c5802081e04045070383c20449035801e140342c0245c00c140e054010264000701600c0200700602d0a444010001000c14034080c0c18540d0b50800780042d24680d40d6102d007003940c0d080c02503640701d0344115055600e5000d410180d000458a82c0000300840c0700f10a01c100301d940580c0c0304200e40406035210842603101410854031990380e0340454809460300317030182040c40d005001a141c1000c0c2c01400c0e6000176070600c040d113030b0318408004112140261070a10090340985107029601c0b070ba00c0f50105052441100c1440705984100701c22840440c0c2d00500402c01e8034401ea03950a00741e015000e071101481c00d08005200280e10520051050644002d03202900000600c11200e21644030405850140c1d001c0d00152450b4001c40300b04140d0081d640d0200c200b01c4c016074040c0c3d14851401c00004e40300d01039070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 522508264 1250 522507014 522507017
    0x6041a06040515040504050106020a05150f0a0f02070c0308190201020301031505040314031f0909030c060f140c0301060f11030a0e011115070201050601230306010302071b03050c0a1203 81
    0x449800b07543d00d5104042d54003074134020344100100c0d6196030010b55546494003040b502c40c8620300d026810264641c0300c1d80c0c02809450020801c0f43c0301c441000d07018140c088104c141a6030b00340445400301d01d900700781000131400b1301d0f14242d4451030000c3c0342000c143d580143c1c00c19a801080104000385070b0104205040c901610300241070703110b03454100d41c4154200ca0301c0824080100900c1984040b1460002d4084401010442030a503a10010000c0d1154050061701040e071903001d603804600f03030742c00941410000038000250300d01d003440800d24020046d500c40510b0300f4084010b00c4003507000b0409040411140c00c0c883c000d4009003188030f50300c0c825600c28404102d03107082600f00c1ca074020f120303021003116400d05441035454010709201d52540110303184030041d820030b00070600b507502908140c000f5650303000f160b02c0b00b000c07882d6024485500c054001d5041540c2007203a0300104288401c1c0d11946600c40d41900861072031400d00d0b0380340004c00368082c2c0c824172030481c003005402105007117018201d905 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 522509514 1250 522508264 522508279
    0x804020409050f0706030203060f040e1005040804090603030309051209060301150512090f0c0f0a030b1302040204060503101d040204051e0a200f16050a021806041a060405 75
    0x2803518608003400f000e02896107101d4440d0100d84d268158010b1442a4025a44100300040440400c0f06070340039208000e28580140c8409088002d050f08442d50050140460360b01e056a5011350b0f408581107580150002941c0f503010108201082c014035a00400030b0382034500388420342000410300d20040c842d10306600e41c10f45c1b184900a0181d0251041000c40d94165400d81c60040c005680310300f9503e14480603070044d064182624501030310404540c00e0090240300202e0300b50703550150a11005000712220000000140300165a180000d002601459440301d03207038104440800100d00c2c2c0740e0010780b0034030500614103881c1080d032079000b54402d40468000c589610b54215502103481c54814142401101904000c00104a900005e0340d2030340c10310294908640c0b50108581d907000340303100c000641c1401c2140000340f054070200008028050010341c0c14008d03139580012818900c0441143c3d00c11350030801c02c0b00714a014800d1208001c4540134204034182c2000c0003810922a41c011544036020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 522510764 1250 522509514 522509531
    0xf0606091215190f060b0d020a02010603050d0f020708190308060418060b1201021804090c08030c0c27010e0712090f1b0e04020603060103020705030a0e0f03030a08040204 75
    0x800c21400d0750700d000541d0011030604020710440b10410220007007182d8513092000d1203100034061710940044515005c005810001c9a0079aa0080c3d40b20800c001c0c2159200c110220110301d0501c581313088210700352940104409044070181c204000c9500480b4142c00140404003c80c6840755100742d0960f061800e4001c603620580090000c044141610392a43c6200501008101031a0711403140c2e03500031545612400b000c03810040c01e07403150701c146c403140052500303076000c56003420b40012110710f100d40005006c2680310390742140f9581008510b038a903503204c2d4018100600b40002548201d03044801013446c0450b200500c00c500078410710a02034030700c80c140c0024032428420488504003480c088810720200c6074a042800c0c03c3c04480c0c40598240015444003000130000d040150112490040e0b5280030313a4440c0c00b00300c096000101014140740d000c004003800030b1806d10040c040c0100a440d52440e990100080c041c000c0c0d000207103207001e0f130700812840c0640d0b034001a8031580070b9030440b8003040000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 522512014 1250 522510764 522510799
    0x120b0402130e0307060906050901020f0d110c100603060b01090e07120209030d050c010513050a0f050313090903080a05070e040207060b10021f020301031a10080f150f060609 76
    0x200e0802c8448150201007548000c008980d00f149000902412003031245499040e0300710700305d01c00c0240a01481c0000c03c500c010b45a015000400400c0561100c9030402e010801d050b801e000c6c510440203c4140d81d8a814010404c845c07041e8402d100c42072078800c10850502c0303908200b03060040d00d104240044a82011400200c9030110303000100c6c0501564039460b140390b000781c12074000b8108607a465080c2000600a00d609410020030150040018602103146031103104000030002c130280c43e140000c0002c1241400040120b5004002445000503001090700b401041c01c00c0113820000500d04050500c03501e00c2e4000100c84564100702d030300503a1241d55180000081084011040d0400312015460390a40c2c2c0202d06a420180d058025138440429284010228802400010a200502c03c1c01c0c210700040c80c40c0040c4e02880010103168142e882c1c101c010314003007001400000c02c3e88481c0380c0710b01c640c6040b47c540d5003100302034803584a07034100600007a856010f080c1009000c0c0846841d5000d040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 522513264 1250 522512014 522512021
    0x30804051204060302040608060303180d030909091101020d080402130b1801080d08011a0307140d09060203151f210c0503150105120403081005030304140307120b040213 74
    0x7000c88014150b626541c900d405000fa402c14490341d0f011030711402c0041e0081c01c02100f1100d0650403981500c04100922040000301c0000369019020044c5400002c0780380240c0d440341c400014080d4450080441c50400020701e0242c40d08260800c010310281408010f072120031081e031140d99401c10102c0c107a441c4401090f82403030b0150fa0525910448000001c0604001c21100304440c8980d80344c050036a04c4485005070b400d1608074041148104000284840c1e00c5900c0c046050341000f07150070302d440c081000c06002c0d42c41565054075072a500000333102054132107000140d000b100c244c0310130b5501d076900c4a015880c01c04a116050601460910b9a40080e54400e1802007100e10b20f1020020b04594206c000c090760000c030384c0640d0b1a0f01501041035958001c2040e211902c03075a10700c81c034581e600c0350350894a004010b4030022082e1402c46000c5400d40d820700180018110381100d10030f80e10707103440070145044003d500145940c10702c490038902040141c1c1149a015406446481c29a994810100001c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 522514514 1250 522513264 522513283
    0xb04061e090e031c1b05090a140f09270304030803010e060a08030c010b0109090b03030403060b030c030a0b010f050405090606010c05010e12070b0a0e10090c0504060e09060c090a03020111160f0305150c030403080405 94
    0x5c4100c810811601380733240c0b00390403213105c1d0041601d01c040f650780c5007407556031003140009400c840c01800104079100300c0601301580404c001c0d01e11903989039150b55041c6103410598007443d280c2d4403070a41d00380c42d5a000c0705c403c4c02424518002d000b440c01200c082a00c174456808054402c94644582c40707071b6038408010810780200e01038100c84075070b00c00d8104804032500030700803040303420301e540400105882c182c0140d034050b002c01d2016042720f868480064404a0303e00c0d60444581d501c0b0b01c0c6070707100e01005001d6521001c00d05e0300305d81c0e9030b10020b2500741d417610001804041d605140081c4c0340722007600025004a1080c2c0548001070243c3d0318240350841745034079404980d025040c441c0204a614001c200b0702e01800c008401c0784d4498403034047d25601c2d40070308014140c01110082042001d50b2051100700380c5840e158094602250b040c5021004118250b0407811080400706c038100b08000301002001d400c000c3c0301512410070b0606020400e000c1c48098000b804220504011030140001070002419 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 522515764 1250 522514514 522514519
    0x30102130308031012111924030e370c06030c030c0207060e1003140f0105150f070b0a0b040e010b04061e090e031c1b05090a140f 57
    0x2000e81e20300e0b11904070341c41251a100d035100d42c0d500015940007810714805043c2d6000d1840300300700001c1070912060604102c0f070781d51028040100050325268041c221152030f04035215406400031600c801900359042c540140499500c91803000604400041c003807805914030001d540e4522581e1140304540b0b020040000e04865821800001c40c0c6816034083c16100219843c18040014121700c142d0b00c54005204290100f00d0b0f5281034112451300d50240404005207050000d203041c0e500d00b5206500c1021a0b64111480d0140300500991070010101840a052149140c4c0b50501c25401a0401d00175603500074003d400301c002003940150140c1000301c01031405442001400e40500450303010300007e0451900032890036101195047d0001c0c0702d9141840041840906545081c11300c10003811403002c0405c07540400e03c0b1480200b91840054066030380f4002c0c0104085000501c404210044002410701b4000100841529911081180341c11100e0308809070700b0074807491000c1401d003135007208260f9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 522517014 1250 522515764 522515797
    0x31113020406020d090b1201030b0c0d020c01230903040e04081c0c030b06040302011b050a0c030807330f11210702010903021207021809010911040b0d0201030b030102 73
    0x10b0303142d0340042c0400004102e035561017125965442c11074414801c041944011100f01001400410070107000c0e0b0350418001840c01d85003500750b0307003c1c00882c0c0101c0d149007040e944450b01c80b0780040140c1040d030701d602d09141c94a40c0c181850520340340e882c0300d14802c2d41280c1284100040034445100191072650f042000c81d211413007108a0580028400d0f03030f0220011034541020341c442d0782400780c165815a0340c10b0b1071384000c8241803403400d00b546d428a80308442c0740c0310340d0007000006a111864030004500c86d03014036851321a42d1a0214030311001c00ca40c200f08001e1040310007a250017041d0b0725100c000c2600400100c4511403080304020b4050190180091600020903401e03082002d91180c00c00c54140d85041d10383e40b02e0410480c241e60040e02c02400580c840c2600a800c042208001c0c00c40c5072004100b032603454031450002c42c8400048603280c9160b55108481c0c02444003031001400c106508480811440c801c010000701c6640390288040d04042d40d4800c0e10145840950444030013506015420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 522518264 1250 522517014 522517019
    0x1009170a0503090f0d050d090f02060f031519051215101406090a182a0f020607090618090609021309090309030b0c0d050712060b090a0311130204 64
    0x1901961064801c3d2100d8481c2c0b99403000c89440103e000060704d801c0d81d80f51490b0044070913164007d00b0000000ba00c8840c400c4110304e00680d01c4e40000d101c0120840021612407900300e54161400700d1400c646401407204030024986204902c500000380d40048444107842d401c44510f4034500307400d26805030000d01d010000e0043d101030402219007160740301003d00340f140d84c0c402d09020a5002e88291030b0b03042100508148641600709081c014000d02c80400002c00ca00c036501d0100b84d40c180814210300380303089003001c403c851350710505222130395803607000929103030403c400f0007003c80e03106100703d40411441d16901000580031070030200052121a00501c681601c455a0784000c1d889001c410061580043c0001500c9500c0d000d43c100c00358142d1294103800f4a0341d200c901411000402d80900c4c141c01308040c81c0d00480c1e038410349000b042266201c910440f00009000f0444e103940d0001c0f840000148001c0840c0d5a80320041ca00703813948039821306481403c0740081a100744100d90315611160020401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 522519514 1250 522518264 522518267
    0x3031c0209090a0e070609031a060312030f0105011205240a050918071505030c0a0306120c03060e030c1c140307120b010302070519030504120c03170306031009170a 72
    0x254940c0b811380603a1a0941d4805003600c26425070310009040c40058644403511040220245501a0016065401012130030546048035441116141050300d00000148260350b4001c0102c1c402156007081040241004400045c400300d0100080318400724031b8650028544915007440014580540b082d9400e0401480d800070102130040c00d61120f1040b800002080659820000003148160b2155865900c070301c012440998021400707882816105c1500262098001409a0140e4002c1c07100c41d50a44c2146000e2064401100c0c965540e5032086c46254200364022900784003051103560b10300c40d200742c901d80c1a03a1054281544c24034159010080011164000292007082c40e050301d02004520140c0c2c0054041740642c05c8040d01951004c0c40540b004080300001400303107800380c00e180e4202aa6109a054286030769602250311026000e001c20801401c00d0008010300d0f58841c1ca541913151140101355a583c07400c0460b51000e803150500010701101d09025000d400080034016a10880181c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 522520764 1250 522519514 522519521
    0x71b0b070503070218010317030402060f030f04050c060901120b030a0c060206090d031517100f02040e0a0207031b1e0807030e0a030203030a120f0e0a2003031c0209090a 74
    0x8240c1c0210178082c0e50b01d00746050b80b044076050380d07030000340510b482555a0020030705030402003003242c00031802c0000c08291002c20018600c00d48584416016074907091070000c1c100400d076491940140014000818036a03002400048040c2d1800c00002d5242c0b850030019240204082020b019050034070740114403a5030204415115110b030b54100c900007040104110212024582500c1c2038000d504010f2140d01c102901c0c0ba5004030b00e90003100c07400305042402408545e14101241072281e40050100b040c000014041a4081071800b821800e00c0d42d0ce0302c0140070401b4070780e0310016071280007514104103c14011892409408050f0749503220100f41740001051340a00e80903030118a60402610041c640071b0030030816682e001c0c0265080100c054010f40300028244002c101c01601d800480ca5400c185100b5403052618080003007444113190f0030002c0503540301c0004a04a50151409110345031400801c07201c0d184001e240f542602e9800c1c4907000024090170a5079503111180c8410300103003103074030382 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 522522014 1250 522520764 522520777
    0x30f0b04031b02030c0d0302150106050301080706020f030912100c0302031e1e1018020703140a090608040f02090a0608010b0f1f0e0a030303020a1b0206071b0b070503 73
    0x119500c41da42c01010614040d0448110000c2d0715503c1501c9208103400c0c002e60b8144000c1c402e0040700c407070555600341140384a00c03d8126000043d030200c0104070007001001200e004110070300140080c482c419240a44900c1346c01510b0380915080368500305210820080040c0714210040100500d09042e0ba0042c041d42c0250303185092074640c3c0040c4070380f80e0404403000303000c2c1c08480c815032124460400c1608034070000400301200b0b140c5612000900c204088146c1d0000303c00108016900da6061802510300c00034800b002225807003c0c4016450260407840b01000e4501a041001183d52146856444011001c000a4201c01d2007003e00001740c145d90400b400750346120000b0b02001c4520070902c4400d103803d0521035071200546d40043c8415220071895040c0c0501440c1400350036401101248030005958000c40001e03500089c0b40b01c4080c1c2c08031030262262410703091101c074240e107500024080c0c040c1d10b1000d092215008004180215401c00036402481e030308034840e880d11402d00303000781c40f5040300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 522523264 1250 522522014 522522017
    0x19080604050c090f040b06130207150c0804031b0501020f071520040308030a0605060a080f06030c09150d15020a0318080f030901020d02120105030c0405160302090a030f0b0403 77
    0x7040d0484a8580f600c8018840c9813204c1043d82c403580c07242c0310b000440c5000351490780c1081c000482c50304500703220300040a1050080c10340010360aa604045002c5a00151640701040307599001d02000a0340151450b007050304480c5911075103162403c0540c024410710400c00030140d0001800e60401401000c050106080b211007040300040d901e00820003142c4008102400d840b04010610002d0600400356800c0302c0020000070342c807915500458040d1340000c0c01c1d040444d40c400204800c90500d200c000c3d034001e4080c0d014000d0b40c85201b022075502e240c060310f80340c0c540001d43e074503500b01d032505100300d190543c0080a00c00c43c44030903041c0400952002400c280064100201611510314100100350491351290001e0b24183c0c80720007801040e08041c0441c6503d5400300f004106680650014113002156100e400103154503110406140021080405d4000d50900041116001d02540d00861420b00d908004da03440c050500081c1032450b45410041882c01c1c404192414030112650035485070303111703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 522524514 1250 522523264 522523273
    0x52106040f0605060a0c0507050301050406050609101211121e0708010501300606180f0e070302100c05010501080706030506010903050a021512090a02030607090f0e061908060405 78
    0xc41d5000c0161003043c0640794000000300032040c0c1e030303078820f07001c2d40c91840c064005e640142d6114800170707085d107034103840c02e842494450041c08039a18001c142250881e00500781201011310303060800c8070b0314480c600003810785e0314020005816a1100c4442003140d80c2e102c2c06482c003000c280441040700c10341c1060803110038800c01c1d00108003a5014030803103059900101c0c402202104603000f07011517400180340208098003848509000401034007a80c0e000d00000d004041d81291421500c4040302d840040a4007541e06111014400c00340108445080d240c040d45d0786244402100801d8501595000004115601c3c04000080262000c100b5030155031940d54140415110800111a0304005000c06042500301031510f100600d00b091081c441103117652501b03403c09001c607040002c040b4080750311000c1c6403c03030010310701149130901402d07074406240d082582c480c0741070180c6d090301825a405121905d2054002040450307540344240c00d034010308006240d101c681c485044c1511101c0a4404484500c134 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 522525764 1250 522524514 522524531
    0x2030f090c0301060b0d2c0c100905091f0b1b0d0212180a03020d080705281106090604031202060705030c0d05072109150507050304030c0305210604 65
    0xb07043c040c0340200c034020880c80b0700306a201d019441c01813007c10101201c80305540580007296a200071603d075180344c02400f0740300302280841442500c001c100c00382020000d00050520450761a980070a4100211419108103801668441e803200c011542102d0300614020030180502d501c0c0700000f000e0207a0312010740b07114907417003038090b07a50710019a014503900000f44198104c0c0081d40c254243d603082c0c010160070105a89402064215000c6902035074030407000903200e0f051000411001c40c5e81400910101003034510a400d1208400320204018410442040c0030409955410151802840000c04503651a5500d140c0411851f0707122040348098010900014039150181090300d10490f0610001441c11520800b21002003000030700e01018807111151f07030880e118110028148030301401c0c7c00020090b4944c18110380381c0000301040d10b51181071104005a10b0303445410307a60080c0c0e06041129403d161841cac2641e99000e40140040c0802400d0080107000c42ca04d842d1a004550030b9504101600 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 522527014 1250 522525764 522525769
    0x110f071b060e01051e0301030804140f010f050c07050a08070e0a0b03060a1112070201020309071205070b090d0807080307140a090b0d0908030f100b04060210150902030f090c 76
    0x5050310403000031591801c1d0300b000c80e5004030000c1c01c01c03640441c0320b4000d50421001c1d0280c03a80081c0c00aa5440402080a0003900f850150f5000865030803200c6010042481000900e010120180d003001c020b404210081d50540c1000342002030807005001c3c40800740c41d040b01039a01c144520890b5180d004e44130119500500324442c4210310709001d406400b0680d905422030000e0701505141191a4408100d000700760049800801c5c0203210990000d60f490810100242c5030000c01d8000441011503101e614001031400100c81049440b006440c40e110791030900060f1641030070b45409001c0d09400185841003292520085129100e1503d0f041c0403580004500d05440c01515070180100d49801c0051040944200142c0035035405881c0204080b603260b52248000e42040d03170820341d180501c40500211504054900e405403144102040c1020300e0040005d54600945584010361643d6071100c1038405001c0700b07900060100644259503a003071036032901c44811000ca840e0b02c032038000c07107481c404a032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 522528264 1250 522527014 522527063
    0x12022b18120303360309030204091407080d021e1e0114150d11030f0102130f1e1701150e060a05150a0e0d060608100e0d0f12110f07 58
    0x20304840c00314031031902c1d042040340700d8207800b0702c405e4041c440c0142d4000016901c42c012100c2140c4106001d4003180700c02c560741880e01c180d0350042a91504103c03400c150aa0740001e040c03511003040044000259140003015040890880106450710018007441d8015401500071254140d10807500e0b0030250780b8040181c01e120440418690720038505107400c0e010400c00e00d100d103560386008055170960149203011608aa125407031140100407990b000704106000c00c0e4620004080c0c0d6084d0800c106c000d034121440c2e0b00840c0c0034402510710031101640c00c8840075031004205140c249040c00501d41c0328038080c0c550000441c0c8070b500c240c2c0b2140c40850117003005100302141c1000e0b608500d040082401050f2552003521400c0c035000b64442e114140810040c2c0100801020310350060202607070341c06e0f24403055882440001c05560b020005003800550301c54840090b01d0300c50300e07201c04461001007a04005d4030040fa00d0511b502d0000c100314007d91221030040036214130408220500307204888c440e2201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 522529514 1250 522528264 522528311
    0x301050a05040c090e160306050303030906040b042603060906031f0c140a03020403051902030703020120010c120e060c091c0b090a12022b18120303 65
    0x4000024108480c2c1015000389603601d42d00d00300310a15a843e81c0c2100810401182d18000748983e202001d1070498041c0b092001a010503000f0314903614101320b400b0381e5100058801001548504006014086454080e000c2942d1240c2180c400203291300e00340b5030700e4000740e0f41144540350010204105180019601c0c42410280702212148100e41c1c00084c0245851100001482140702030f1a01d03640b01080104800b6005440c0140c946003503080c490b182c0b000110b203030000c0004130940080943da0000c1c0c428200d03503091070142c240c0b40134041400310b20b4a508100412075802c0c149038144041e0040800c0d9000c0014100800190740e200504070703540e14007691700302c8040008100c03206607801d116180d0503070441c100070480d8000810381c1c4c1d0b416215004440103020f40e000b0020b65410481c0540304140003420f1440103201c1c900b4040190080340e035591040d404c00f41c50901d0542d8403640240144481340004010890015554000c00b0310740300c40d0088101c000070700e0301021448520f03016480245 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 522530764 1250 522529514 522529519
    0x181302040c020a020d2004090b07080606040b040311011e081f0e0a1107050304060c0c15021504061b080603100203010b03130f0816060c03020a0e190302030a03180506030105 76
    0x20170705d1084c0c032903d001c898150088007001e903e0000d06003035500d5500514114522601c4a00c85d00e18212000134410a009071000e0710501d4100010883c46008a090303c059035044159500f1503582c10006031065103221100040b142c8d8001001580503400003a100e02c514a000c001441034514881c0f400c81410150042403a0044144003180f90f15420b82e121883c0c41020b0101c444c5040340e107803160303032454110307078003600c0041c002c1c412907070070042514184801007000480102010704a280065245c25440203640ca007201381304002000e10015400801008145070f1380c8507510608400014100e240464419001e4411054030000c1c5446034401c490490340586445070464890301c1039400591070507041a1585c20002c9074044c04910302c1002048000c065000c2d6010b841414a805402e035010810b08006252050059000f1260488080110f07a0700444d4174a4054018405200900a1503000a500342c4100c030380c4002050340080107003040300d500340c900501c8203079950208403551109005068 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 522532014 1250 522530764 522530779
    0x24050c1902030c0306040c060f050a0903060f0b1009051e10141c020d140105030607120f0507020a0c0905040f031409190f08072102181302040c020a02 66
    0x50030030300c40d0010940d03880c401002c0c1c0d9501c0f918200041e181100580c2d06a540725081d02d41004a103070842c018800c2242d0b0303401c00030701384660104090300c095541c0c40040c081c2900c1d00040c0610031041e5103c818a0320004041c81e10204200c940104403100c0c60103102d00076290040440c01285110341d174134000c040001c040c0440400107580031114107120141022007000180b00605038000c0c48880f404805003803120041c0c4800c801581c46c0191088440c036900000c1c000401400309071000316840d035020402e41404000900000f54420050031800a800c21482c6030400b84030109501080f03010b880c9004841c134161725516a030703040c4115601620010850b106802c61000020f000d4151b22001050580b0501d0400d00b0800110700e04040035240d281202040220070f02001c12810007044c0500780c0c2c0c0e00140403c03401c00121120903000e110031040302a0030700d8501b80c03c41d44e0b858048500014120182a864140f9020149403500e0102c4101d108508081900c40400c0c40010a010412b400400c5070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 522533264 1250 522532014 522532033
    0x60d0f0b091005010f12022106041a040b0c130f12141207201e040507020d02120906040305030d0e120f03270f0a0c270e031324050c 58
    0x51200c06c106444c101d0300001100e40c00385c820342032418075082005003600504460316240c90100d00c012001c1194060350800c401c140808110700070041940890110340190b901c5001007403d002c418540c2d4081c0000700b2141d080070a040d85080d000d00416449a1004000240c1b91651141c540b901000e066823101424800100440c050000702901c5020300c0341c0e015400000003003c100308441000c2111306510b103485a5110b0703410a0b106282c1e00100a10280194a20100009445007000c268416038a0070101d10800c1c1076690808a90055500c02c044130b40e0b502c0d0044612016101803d030000700e9020703001a41621071007240880d840b001d041804240345648801c071a10151105211640344002190500c520400c003c020b41c09844603000000c01004a40740341004120305540c00940350b020110800d40a011801d1046840003294070030301141521101c118141386002c1c160102000d0440094005040a041e00480c1c501da03070746150250f440e0914200646080c81600040c80d0541c3c0314031030b80c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 522534514 1250 522533264 522533279
    0xf0b0319061a130912020c0a050f0402210a0b061207050d0e1b0310110a0c0317040f060b04090c05040903030e030c0c18160503060d0f0b091005010f 65
    0xc2c11945024811910b0182d904012401c07541e10b42407414110340c1e40e440d103036050100800102403006101e02c0141041c800b448003041e09443e0b039101d0b842c010a01071040c04840e50f6035030140d40300f000c0d4020001c0c0c5c2143d403098030301151280540701c580e003251809031640000c2c24550704a4a851010141c6c6403000e4031441030440791540514401c0c0000d0b55030791100d07001000b00340301b080704007148140750381d4614651004150031b00003102d1070f051005223805c1c00040ca8441c80c8095910a190900b07101d68110b1850030b0681d0b0190310a80c02c010a40803a2040000301b06d070312200d11280030300400d001c000c83c800600610045a1100d403000c1e01003100f044041281c1d14040e000008068031030300e800704640408010591640d004495408281c0d00902020829410600c0006025080c801100c4501c4c2c204840c64802e0000c3c00c1c0e07108800c0140010010300c184e22240000d050317840d07010020350382d00286810310070003604081c3c562200300c6c000d65190780135081e00c41c01184d050f03400b140d44891085140510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 522535764 1250 522534514 522534521
    0x308010f15080702010b030d0f03060b040503060c070f050a0302070906091509020a0c0501050c1206031c08041106030a051501090339030b0915270304090606030f0b031906 75
    0x10b003d04541d00d0310784800050300c040c00404201170140e1100c48100350580001342c246c032680d42101c24000e4090108100c3e45da0009482030f00319040c0880d0719540c2049052a82e80d00710241c1c00544030f40300e000d4440c400c141d40000c4000441c1ca99100805c20075440301e0043e400d9518050040c0b080c440641d0003846030058560003807a000e21141415844000103a403944c0c00d54004980300d0140c03c0010495000700141c007c10030ba40003000710007802a001c1d407003800c8481c2e048620200300c208100c071400a000c10200360182d1100b120020001612460254000030260404441800200500040950055000b2141d03801620ba120b1218050020241a5083c00c2129442c080b07019078000c103d0b4040381801594440e02a50203007281035900c0c500010521b2031300c1c210660780e55411004a007040f181e07009941d80452500b14140c0c1d6a010f9a540d081000d180d80102c1e0440e10800745001800a4150b401d50300c0340025950b000018007240903140105612100c82246044129058038034500020b00241d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 522537014 1250 522535764 522535771
    0x9030c150e0d1206080307020105030109020702150721080105030c0904060626061605091c0611120f0103080703050d061d070e0405043c0f0308010f1508 67
    0x5000058803001c8058640c90101c0b920100c0c00401e2501c808105000c80600500c0041c1c08410000c41c94076015500080480c401441b850041030790105410086649281c074400e0752002e1070366101d48031901d03410130f1816420284590310340080300c4801c0c00701403405460706034103e90b80180a0b1011f1540c00e000c1c0280c06000a00031244695141000300304101c01d29007403902c028100c000b5800000d410704605181c00c00161000d11200c8a03000c0c1900400d512034100c520401041d12108800f80642191050407009554010902070800c01c9c103001c864180c10203000c00031070740d90500429440e01803103658002000e0002902d109010081c00f07000c07c2c003403c028070081c2d4062100040c601d65a80e886a00b01e020114029060550081401015070703002840312140701c0112410031090500c0d0380d502e100d20500c003502c9210130440140c0c010f0b41a811004000580076030440e1004104060314000c610012220400c4000c500d0035000801c882e031180078407100760b800140840e501340f410f050f805c0d140d03480000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 522538264 1250 522537014 522537053
    0x1e180e01020408070303020706090b0309030405010309020f03101b05070b0a0b19180f1e0b0a2606070216030609020609030a030305010f05040b0109121403040e09010f09030c 76
    0xc0100188030f9008018850045000768007508120b07041c007000401c501503a500c031040c055402d100b03200f00040c000c0126411240b00f4240080c61980601c0802d82e1002c2c10090b00b5807501036807040110000c195080f86001c9440203200168070941d03c0b0050711680100b0030040c1046103000c000402e9061141d02c01a0842c000401c0091901c040c001a94080003498100c48003002e040d80d40162031006500407400d100300800070a0256904450961641d002c3c2850b00c6440b680e00c40303055030880d0304c07070f81c102002034120800700c0702d11010803a82403e5456100c1c0c0003121903109402c00680340301e2000c640d00d074401240d00b054400192441e168503018007031000e81a42c0c410410000780b200c40e40c082101c0c8200724401c0d140402c480d031418070303200031000f90341d4402e6014030706058030006183c0c1e005950310161180c0c0f82d00c00304c40070345509014484441c1142c100c0051b03c00000e0100715501c00d04a030302c0c490030040009200d25014007205605a807660000100429007010302000011010000d400004100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 522539514 1250 522538264 522538267
    0x1b0219080714010b09100b22080f070509060108070507060b0301060b0315010305010e1006080c0c07030b040605010614040905061206010909020306361609061e180e0102 74
    0xd50b2a00e003200800c102038030925a641d00e49003c01420701e00b4030320391700c403861a8109140a180010320451441503945034400d4444075201c0000000c01c80c030041c4090005001140c40b80f603a45c203c000e65500003402100e124100a600040c103a6100350303e180e10544143d42c81030704000c8d880c1c2d00c840203050208249541552584c3d0080703034242c0180c0107140300d01d1411101e0181c602d0054000740c112681a00720790402140b0f0020080e004403020741031022a420340c81e00b1035266451080c80305040c0912110020203005084000091101c801051070046028240810030360360303030710016614481070170b80794110750200780703c20401072075550300003540048050408000a0303203013625141020800d801c00c0d40b100d603407510f02c14250f00342040b1090784007203800c80c0310743c0c2d820052aa06101040349234900c80060714090719007182c00004d100700c03403288115101c5042d032036480b51a0701000d0074241c080c04180104040800c410182c00c1c000242c00c07101d00d42c0f18490300703804654042001d80369840600602d51340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 522540764 1250 522539514 522539527
    0x1516050703260118141303020a050303040b0f09010b1305070c020a03150605030c0a17030408010204030804060f050901080403051b030f09040b01090e2a030703050a1b021908 76
    0x600d0b00314070750095115000d00e03007542c10040480c420007800c4103100c00c10707071918209440c0075000070700003600540440040140780c202413900302c0c40c04030001c2004049000200c1400b0400620340c1480380501c480394810085681ca0f081024200c0d405542030962064a40d0810744240c20142d000d150450300d640b40c03451405810b500428255103003a401210450710722040b15580d10701d0b621a13000644801c60284c599442d0801c00217540e031859014070840d050760103902250030700c403c00844d401448098000d40d203841da030381040003442d0407610410000c81c07001c004c0b000c0a5803180c412603880e840c058445c5001a1641d03141102c00e0740181034420483c04008018150f550420000703014025203295000b9543d40c07481c0b0601c001c0d940301e414220b05000d41d420042c007041142c914030a5010038610180080070816001803410581500a0310144040000074001c81d960300d500201d11034000030100740b0400480c031040040d5103140c0d010020040e0454a000f82010000184010340680604a81d82c01e200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 522542014 1250 522540764 522540797
    0x40b0a1119080322030c0b0105060a0e04020a03090f050601050901051002100c0e040f020d0f02090d080c1c170105030f0706050c030c0d0503100504090206030619150c051516050703 79
    0x5200301794049420034601004101e91415010b02414040e03d605040c0080c43c02c0240c10300c041c120f04588129000b10b0328150b01c91080e4000e024554204080c040441c91a0030080c1d240c0300c0a0150500605207800041a075003007104180c6102a09a8024031501030005840c0004103141c50b1000104209080380044a5139240120700d0764a5030b141300140d071041c80c028a60304540c070890380028428011303c01025181e4444541d60101c54022124590360140010750608002038400900360700242c3d500207d0782c00d50b01c181d642c0000b076129090001242d80700d50816507074031030048400c101e87d844500e05020862049001e0503807020300030100c03030522045185c0c0074145402400c12100189003c005c00200d0502014101300414060b60100514481038002c240d05100080c60180540b603408851500100b0b41c10b00c440040c0f0120049984850807484001d002240540f000c1d100c038401c21004d07210720a0f804800c1c0340078120302100d401880402034000e89850b00103190690610006041619021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 522543264 1250 522542014 522542071
    0x302030f10051005030c0d0503090d0f060b011d190302131b0311040e220c051002031801080702030d0f091a04051b15040b0a11190803 59
    0x360914400781c840800640354440c101c0d400103051024080c01040100b2860310040b82c82c9a210390300340c0e03241f010100d4505080b880d610880c80c0f09900500c1c050f1003c03040c450380b8845001128402ea6061007940760311001103400244070b080c03144500c0f05032060700005180c01ca9410706228024040b940ca4196030750001000c2003840d203141d00ba885e48840d0001c542600c8005030301c0090070141004c00024079032160511190090740100e000a5140b000803540d0b030070460f5850315590703403003090381e04800846107015442e03440b41c5c1c49013038021100b110300030002c28004415900342800e481400031030203059000444580c00060464420340c00304001c004012200ca0064030a080a020000f241c0320f1500c0ca0134040107145880502d40901c13405050000040010900760f00c14410022809104016100090b000a060028850071468001000907612600d01d029041850f49a2034449a803c0b4800c00c0644905641c542461440b1607902c0c1d517400031f602c20010b0f5410200101200301c48000d00020603150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 522544514 1250 522543264 522543283
    0x9290d06090c0f1203080a0c0507240c0c0b0f040615080f0601050402040e0a1a1c0c1202031009030215010617091c1202090901120c06020705090c13030203 68
    0xc03180302007020f00240c00b24145500080c00c5122034813003c2d080e42d8a0050a41d1070280c0180d800545a100c41001c0314484c50544d0300c86a00054100300c5584c0044050116128039481031414a08190740703564090300078083c01080035002030130ac0c00e990b0b550307502d00501141c0081c0210b031078507900d030700000c7c3c1c2c3c0340d0b405d400718042d00400004200d00300035020f01925259050748550f2080780100400e100800400405c15001440e0603800300c0e0b0230450340500101040b68422640d007044081004a11000141210b0202c00780a4443c402c402a02c1da000a00005050304000c2d41641c441c840011051070258000003d40d8044d1040d03510014902c0d14801098400780d00c4500010004500283c4003030b00501442c2c0c010b5015001403444010421085408400300070004050004140b55114440c043c1d8040b0b0302c81640c01050480c281d0307129040000d045a00441c00d131940b4000b508041059800003075554181c41000300080c105581c0c18510001c151700140c03000204c0d0812200000050320104802d1f0035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 522545764 1250 522544514 522544523
    0x405100e070602010b0603060a050f03100c0509040f0b1c0c1203030c080703050403081b04081618060605040302060715050a0e2a01050f121003020a09290d0609 70
    0x1a071510b400402030a4400030b286075480b41030300b08240641590340c40100e20442e20b054400940b140d2208d00080d00b48080100303400c3c080d5041082c0007104e0345d4040020415440e00300e42c00c000f8661203030800c0d0219010754458540206910135512500858100440000c503c00c1c90301852352901da15004490790100081140031940b564030486203580c1000710030f0b03480721030b901c0c00704210314154500404200b0b0141c5008007100c05203c0c1c0d91100c401d04001c0310080e00c1c0c5502203a9509450b1041044820f01911a202070072000785885001d014484c015070040b52041d5a403141424103503003c00446500804007140e01c2c00c081d09004510241c00e000300342c03180264010000f01e00d00b2142d40f0702e061001124403402540400c1c204455070b5240c820106070440000c0c6000390b210769035100c940c0401e200d92030035640118000b400300400005181c000c00c0c00c8c2c0b40f09480c0600342640e91043e080940740c811020140c68550f0021010400f68140592581d29a000340080342c170b8250354031003104075401c100c0c040d41c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 522547014 1250 522545764 522545773
    0x50a1103240f06180114010c06020c06041e0c150504091802120a1502030a090c081c0f120f020f04030b011a0c061503070b030f16080907030b0405100e 66
    0x16908107030300200f607001406035801c09003480204070013003060005010f42545418128100c1030369902c103000f070920140d400041195144184000550b6a660466044403445003054003040084000e51405c0346055008a00112280c1414000b80f11030012014510810006000000e40d840640c016100b1240310b070307421400c440843d4014840a01181c050301c541130740c080c01e02c0c800042c1c29118070301520980c9240043e181e40b0780e046548050903201d08003800714541840041109039000ca001c2c502c0e0040144011142490311300103a035030307010022150001c24041c09207100c0c60071054008055031401c2020051800c20350700c01034405074000d60001c1d1107181c00040184004103154408c01810b1030305261041c1020744146030a0343d900801014181e01d542005000112034504000d8003020b0180c00800701c3d101d24208084003802c403821100c10162802e05041e0540c0c85001d0800c5901501440014043e854115200d10b682404007800880e03092041044420021403140f040d88004d012240240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 522548264 1250 522547014 522547021
    0x3070b0a020c0f070b120406090605010303091401080f0408090a03061a01170103050c0d060f05010b0d1b02060c0a050f0d0c020d08010b03130503070203060c0307030c02060103050a110324 82
    0x2c80c50b1101c59812820b995100c400180300d207202043c29104007100010b9078040c90340d0760340783c00343c00381100c8000205254104000417041541040300c80c1c068880d0000503100940120004541c0e40c002a40d8030b0741924143c90100e008194128001e000016001e000d0480c0c2d1030741c039510b0a08403a61842c036980010000e8000410b5583d00c521100401c00100d10b203201c20f03504640700c990f21507440c3e942c007511611511004008001d4907403c80403075080c101404010395a51500070b00030a90081c01d2000c4107602d000d03007502000000b100d40840525207035000300000c0c0d68166160056900c02c0d00c1440502c442445041003c1f4481c0707004240100302024041007502800c68007900d8031344600d40080078041c0d094014018002d951050b0ba0740314440710040f01c05071903035007401c90a52141440c040e41500540c42007054a1103000011802021243d500300101560a50200d0b1118000c1c0001415038001d00d0000010552040304c261040d45c000381034070662289401e55407604c0c148865110003800b00c40c800c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 522549514 1250 522548264 522548287
    0x190f090203070e15090103110d0c0b040e040201030e160e062103210c09060d0e100e100903170718030c08010c05030106020d18050406090605030606040e1c0203070b0a02 74
    0xb55032a00707101780c0e1032144035411540c440b0a0007081000a030f000d855125104014410004440340003451000d048075030b1552680120161100112001e0340801e08000c0b10311500311000400038500c000312410030781694140502e41000050152100f50701c060b081c0d20000000f6480d00c04066400703c000000c5036928400c20740904400403030424035100c503444400300a4407000c030400b11350031884220b501958524511030000e004062401280c40244222903d00300c0c08581c41e80aa54614040c0040307034007110245001d41c080e904100002000180801c41c0343c030116440c0c050158100d506410050246413081a030034040c02d4083d8000c4d41d440d03512090400102d5000c2c840c3d0542c051862602519540c10004003950762400703407000d0010045e0058414490604045000e80039040003070060181a540c1c0344000f000e0105401380c284240214000310305146414400c0c1c5181443c11806000044819502d0a0700380001000b01403e5000070004940050140c071003040c820902082c006880701540d106 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 522550764 1250 522549514 522549541
    0x10c03020c0108100f0b0c0d020c0d032312060f040203010f03060902040f0e030a0f0e1c050f01180302100b1810030803040804060201051b22080a050a0b0a05190f090203070e 76
    0x7050096420898074030310150bc50300c141c010710079014200310101c0307501e01d1201544140c0343c212640e004c001c045442c2c184200c0c1814128060081240c40c602c900c80c60400700002ca100a104001850400e5a0104006000e68001512035070008100040340e00d0810104c4082c0d40081072009482d410000d901c628072508048103440e285054075044a5041e031601c0442d05151141d90000081200c035190030003044000c003c110b40044d03550000380711000e502c980b6010001d44440c402c402500070450048a084814841e1300f04030000100414613500401c05503002c903200151000742101c11010000c000f0845020045021310b218ac2803003039946250400c0203084a90103000ea200501c11400c021004400c10340c01d850030f15000d600100035901d441d40c1405a0710106a0000b51180103000300c038414031502090740c22000d4041c25543e061581d403908940c0c00c035007045810108482400140d1401d554807a0300c6514000f81d01740c0001981a0b282d000a40761031220ba01c00ea40b102080c3d01041464280d841 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 522552014 1250 522550764 522550783
    0xe03030f0f03040c1403060a020d020c0715200c010c0512040e0109050c0306030d050a0314010906090c08090715140d0b040e0a080909060f06030a05060f010c03020c0108100f0b0c 78
    0x3803a003170402c0c0b5060010b501c0c1d00340a0080c3c1805a0003240e24180c412041d8101c4e141c1d4042101100c0055030f0340c0c140c101c2080703c81080300d404a5140380783c505000721032130030019802c0c5010303010700250314011005507148188074034141e41c4c1d0b2040e2448102400c2488004001510703034660307961200d40c98031040409840000303000c100c02407020710901806031000a008842003400b4200300380c503882482c0c02100206041c01021210080100000547c8001a80700006071695284103004000e11840141e814110030741c1c0c0406280d016003030401ca8038040d840c104007949000d00e0108007080c2031603070900c4181c001c821000b000300d50318400003a1600e001d02c03d40b4410034164025002c0c010440e16840703581e00440180a001f40380c0c98000036002e03551052000e414160080c4119240d06200342d51400510003181c4550103030040d04040100c2c1d6000d140c1501956a1507401000f224005200440c1c41d800d0107415240740004940022850a18203503107400580401641ea64440c00184581c1e803a004200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 522553264 1250 522552014 522552029
    0x50d1d010c1a04021906030504060b030604080a1d0607142505060313050a080c1b220b04180b0c041409220f0b1f060e03030f0f03040c 59
    0x6845000000c0b11003a90988001a404901c00d0981e16070000c9150100d8008034080403150450700441e8940d003613400240103034000c9200300401d0006000313142d5520819a0302030840ca405105454001d881000c03c00c406244464121004243d0500821000c0d000002c007150041c1d102c400340d0b48444800c0260042c041640b6408080c6401c901001e1440b00b8441d00400c0d002d108008006510182035690020149900c00c084400c03801d010704151035241c221414488607030007000d03071000c00710005120750743c1c100c40300421580c10144032188409140240d801446145629000d20004a66440c49451007502d1612544144413030309140101100c0d5008203000c041c01820b0200384a000e842800c0f02c1c04411068540318500e032240c14411480581c0410100c1c0c0040c5a020b5030780400c860b5030210007000c1d10034143c005494480c14080815140b20040d0303c400c5440c50401080030030703c01c11030b005c0340d01c0014098030310340408805c1801480d480464040c00e01c0400006110402c840c000c41a001004c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 522554514 1250 522553264 522553277
    0xa21170106050c070b0a09030b09030403080d02030a090f0c060e0102070b04060f120e0d09050f31020c03030711030f0409090309080d030b030c0f010c140a050d1d01 72
    0x22a051001095040c010300041003004542182000c0d410000c0b138018080c1c0c582d0058840000040041552425000448034401d141d00884c40460b000401c1d00c050340e50008040307090851440e42c3c00020b4000408440c0f0143e201d103c2c02010800c41500604442e0068203079204003810448003400d1211084201d504550000400700301c528000c0b0240c0c0e0944282c1c0c6000462040d4004048581d00c4002c0315008900345040c031002d221010000d080e4803500825101c8504461742e0b40100440d10345a400c178076404c81c542c2003024000c82c2c1200402c80c203440d00f40d0030f240c507240e01c1030f010101260030681041d040342d807000043c00040c9801040e190407208603400114035243d5412101e054034081d80c818820600c0d102c0701444100342c06a84240081c02c91001100c031a5107010074010090a02d071151a4020301600050140307605204211107442d020603124840d0398000c0e5640d07040b8030403481100001601461000d070002a03000d05c18030021310381607541d40b002c0c1e56009078100480824002e595061114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 522555764 1250 522554514 522554537
    0x1915020310030f0f2f150f0a02011509020405010e090703020f0705030306180c0a0f021216120e1804080d090c06020f0a11010507020406030203060106031a15040e0a09050a21 76
    0x1031402900b1705505c1c0a44003c0b8440d6060140207282d0301616101812800d0b0119041c03049650542c0102d0100003c1801104c0c040c2d918070600040f0312544c0034075400110301c1c03c2c0e00748690030002c2009401c55000d20380186089a8010150f40680081504071490f40000090240c00d241102c0c54016091400c8080c0c621414000d030510f91510640b6040b400380b103000e5038031858140c024014038000075110301d00165500001240640800c641c00001c0300c8011070b220564859902c28400c280b401c400181c550f40c090001d03c0001e44c19072a0060045802403010004104d247c01c4500800d03800900c07400c9201c00003410301c1d83c00703828604404659545644102400000300782d60304120f680001c003e080c4a86c0e1818a0700100d0090103084e04041d41620529000286195050303110081c108201d5100e50700b4000e541c002c1000f841403840c500c1c41c0d501c0f02400140301000798100601d821420300e0100280f5914203a94580c18004001400c0d214180441000305c07004004000c41070f0303442d000303282c400910348 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 522557014 1250 522555764 522555833
    0x31905180616090806190c03050405030d112101150810031217010b03071b0203060f180a081b030909150103020403080d05091915020310030f0f 63
    0x301c006000881d0440030240c010b4040d4020302c50400501422829142c040c40c00601c0003c62114590a84600e140f822200c0c443c1d4500c00e01c07419000b0399201024519002120207031501406207040141c5092104100740c0d00c4a944200042d9261084031111030119071500c0054418809c084481e0301c14040d1140401c6203a01c4105111000c0d6a40310703010340d288584080c401c541c4e11402d50080c000c901d00e600008101d14113810040d40c859140740c0e640c0c0c80245500302030078890866041c0c00a4151740041b01040c081c188980e65180c0c001c01c0060102050802160300c249440c81c1c04400750382c582070001e0408041c1200200e28400d62400000030344c0391210880c04981111401490160840551041a080c03603220783c0444000f1500400780989818000912a0003400103451502c5907200d914aa96001900c2e500a02c0c8102d03040441c41445201102d10740c0e001e5071004040524513800305102000090b00790a1041c0518060210904000b0366407403d26440005206800580d00301c0c0ba15810088 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 522558264 1250 522557014 522557023
    0x4090e1c08040803150301050f06030d26090f12040905010f2414072003011509020901030f29040b1c02030f3310060302180603190518 59
    0x641c1c0f0080b900e64a540340400034071105400c54050342d1650a04041c000180c18030a0701c0e50041c0001c80588803021000740c4240c0d8158a104d95070b4202d44404050003d100c88040c4005900c015200c00303031520050040f0600d4102800010001418140410203007c80c42281c4659409000e482c0c0120311405d0800c0b403c89001c81d005002c026146c40007032400440603205e203107141c00d460682c180d410348907021494050300c92202d000d540d586401c00c040303001c03095103014011601800c4000e40240400e5040400c6a0301950040311814141038558640e010142218800c2d0042485a402c0102802511103100c081c200300c404a001d12460074000b450507103035aa10107480100e940740e8046a000c01051001c80d040c48010321a0000354003820a003040341c1442030070001c104282070014100ca070308405c0f10b1034010030b0042d181c00810321360441d400e0100074029402802c400030240b80b101d00490040c0001440c1e54001c80d90403140c0d1029070390074080c680003400303100d41102c107203c0e0807520080301c80c5049030348 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 522559514 1250 522558264 522558271
    0x30414040216080a0e090901090311030f040303080c0702090a0e19120513030b070807020d032007031e0e03150105060d1e0e012903060105010809100204090e1c08 71
    0x3200f500161103500c01d401403400440c0300070060114201072400c01c5d2154002c000b0f10009801003840481a041030100100460b0386444801550354200341c11901e00700c030300d030000070300c420310905d020002c180143c0e45031142c50b4031929485002184103450502014203044988048580072044a010040043c00c111007401c1500b00718684035880c0c40442c48141403404090348040c0a0b14581c40c14000030380d80c40030a4500c00c0000e5000c4403525882e1941c00c40071a506141c2400c1c07182d510881900a15000d1030080c002e0a010f443d03d204921954039040c034852031000c0c1c1e104081882031607400d0603030505114001302c1c1030050310566070035171518004c03929074451001183d25441d501c09501d0030307401280b030f08021031420040040108405044285000344100c0c0e4000780d440c03140303403004940283e8040120f00790f840090050001c070703443c010066900d0800030300103034032500601440500401892026000802d00a50081a20031003040c645013010b20950100c10190035080e90995415000802c0642 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 522560764 1250 522559514 522559523
    0x7020307090216020d050106030b1807090f0e0f01050402100302070305030a0507051905130b0301060c120302220e0108030405010f1409100c33050414030c030414040216 74
    0xb5500141d00702601c0c10f407800d031802076002010070681c07004d0050545c0030100b6284550580340940d1224800c039030703070160041c00550099008070b00030f00040901c1c0c0c100c08091018110081a9a0f100781c2c64581811502c041d0320180d41c9d524410002949883d98104681d1400c45c11704519120003030320020100e1100400035010b142e04c0344049103c0d01e20420848040c1d1203081c0d501800740107208001025035101e03072020b484c400e51012002c01c0980c0303c0d108903412540151188000d000050392288080364038011400e0a1690038003040f50204100100c40246e12000d1b074142d40c0c16410207074011080032040c2c11603d62640203002c01c2c00300c1d98022030704101761320040c1008100d0804945902130380c0e00c07504410580044845140c15422900100060101481150f650070000a045084a800e090038100410442c103410080a0342c650307103620043d0002e006416112400c01130b05403d80c071b5a41705007000c511079400000c0420080340c0015001c0f02c81d1a0840e82540b81c40400391904012074081c1a0192 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 522562014 1250 522560764 522560767
    0x2120601022b1d0d080c0607030b0f10030e0d05040611070302010917010608120301080d030e0c040e01020c032107090b1b0c040c020d090503150114011b2006070203070902 75
    0x1000c40c00310302c0081c0e0000e00c000b415003132500000d01d0170120303c0c0c005015102d802c4c410080132801c02c43c041d001d1510a10005411400407141400401841580110740902070654420400b0880181031090900c0c404068582c103580318905034005003401c0f441d2000c042581c00038001031005030f0340030410300101e8546103030401070681c484800a0047c03459a000c045076200d1065501030116042000c1c5040b103000c40305903161081070040503000d0b12070341401e0784650b0704240c0201c1c4c00742ca49603002500103407401d0001410440c6102581d032543d0710440c10b0b81c0414416480c9a03c00c2c17500818050340c03001043c506071556522f81030740501c01d80179000c03400300030810054011540312020007100c0c00d60800100300b4400d035100c0300000303034039030140c602c1202c0041c480880c0880c02d801c000800407500d20750300c2e66103591607117010016000001e0098005042000405000406c0d020400d2094101405419800850366074031401ca4180303100720310603034058903040c040400035a4010903c10201d0310f1510303001d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 522563264 1250 522562014 522562037
    0x90f0b0405061c14040b010602060f06060a0e0a030c1a0a020a170910170703020a09170106080a0c1509060206040b060406120c090510032d0602120601022b 68
    0xc6040403044060100e80c604d4a4112401e107502180320501950141c0400c843d03036600c0e000100e8840350115120030f095140240443c845007819801001e81c4041e5152240da0740c01c40e0400584541c07034540c420342d80c00402002c00d000c444010745001449150345142c00b45055101000a52910b401500103000032640d40007035181c1c424184100c401c10304008103a00c002d03111050000c2c1c09400c502c105011241c040d40300107460b4078024400c13903001e001c46454400303900345880e40307a900303054030f031003d01c2c096549034000018a000d0800001d10983e00c40d0307119100c01400c043e140c0038140e000648180070003140400401215030003141903900142c02c006600416514900400d0280c040340d8092640054109050024000000d003400c2c180d803c095410f001d152a114002044501e40380409481c90151403440c03a0341c0450840306030704820385218440710814a41e203c000490700100081004900010100030143da414030421448180b58403640c881d0992803501c40070203510013040c46060000c204040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 522564514 1250 522563264 522563287
    0x70e070302070b090f0c03010b03190515190b01021f091407080a02031507050a08091006030305090907030c210e0321070f020a230d080601090f0b040506 67
    0x40324000c0b500f0455510b4a420146009941e42150481001d2180508100d0080602e4107024100f2020402802041030315903402d2090302c03400c4900c03070413905845a921125131921a145415104090b500402c20715481340c0c421907c19907000c204000c0c11500800601c0445010400010b08440107105001900b00e09a02c1d1080300300004801007a00707441420b00c00038041c440000c7c40c88400b482036058405034950726280a00c40d000a03501680450300500c030410b4010b00c141c804981c4651000e080741c2c05030518007490f80c204c0e08140c10a8000601c0040d800116051403110306030048581d02d410001c414a5080c000c01d82d42d10400f0080040c184c0807417100012102c0d402400c245440c804c16644d0700d20386c00c0d440075521a5070640b41da0300302d03911100003042e050041c80005200003664016211092440d0384440d41028403c4040820f521401e2108401d03080400040351440166140c40307995041c00703000501140d8007940b0221020309207030010302203803204e0800d032011a4025a8190340341c003441c842 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 522565764 1250 522564514 522564517
    0x50603010e0a08091801080618071508100b0315100e0402030f060315070f1b08071a0a02040503190512030a0501030204050106111b0f03070b0d050a0e070e070302 71
    0x14020142d01c185148030050203c00c078001c040300181152051070b000010306118085820134030a41c240f6801550000d01c81d2001e5401d0380906d203601d4415034030030940300e07003041c2c42480c00d8950b11000145204c0400251141080540c0080d00040200a0035813074508044500c10500c07030344c59409a8600c007045e0211a02520b0100c0250400800c00d40d00c4c2c0c5850300c400440400102c5035280b1a210709041d030394000081c498814081c1c0c20300d03600c030110b44080c0384090300c2c1890312811034084851100800304c04510990050300c03180b803280081d08082c040f00e8174030044110001d400e00c2c00f0288100020410307035800180c5031000d5507100d62010081000b0342400f908000c0741c100034035158000007003007140111495010342d0683e8800c903000c1045980301c0d80111441081c015100c16a58812603190140f9101d20000b81035400c0004d208603c28144a4042400c1440e181e00c4081e203c14003184e1021074030310034020b15501410055040000020140c0030b140e90b407205208480039070100d031011486881c8072b0340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 522567014 1250 522565764 522565781
    0x30e010912032706020102072a0b0304051002040e0619080717250801050a050105010c0204051510050a08011d04080c0f0111030106021e06070e040b030d020610090c08070305060301 79
    0x9100c0c0d000300b41d80341400f0b4041d50250000b2101c00d040d500001c3d41d080c09049e04010b40d01440107800314150b0070062903103a682d02c042e1058509200e00c19001c4510725150004001500001550030118103000042c00b6030643e201d2007a400701181c82000b801200c5000a03a641200d61f0b000740c07444907a252108460400c4d0043d207568106030009265102e04d14001c4008004903030041000704015501d0402240845c3c8080c02400e0010b0013281901c40913280c245c104a80240100082850a0554500241410300d000d41d071040403400204140f49425040100c203401003140c2c104030240601e20405d000340c10b0000400003005480c0c00f261180720749808000c080c894048020080020b6014800200299007091040034014072900c1c4945142c0159854030f1100e500d0248010480c9486030b400035030300c030500424280e0b003155a0b000300071b01907076040005460b0700030150054034043c10045e03980440c42d1032680110713202030b007030a40101109038411000c3e58025014a0f0004654950b01c000078050280c1d40d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 522568264 1250 522567014 522567077
    0x522030b011212020c0108060d02010509040c0e130908070605101208070b06030d120b0f0901030c15020f030a030c09120309061b0c0b09040204051507030e01091203 72
    0x910000c5004101c024102e6450350140003140740c40300d40524101da842401a040900184290000c070780c4034180954491803061050600505149481000c14102c0f540c02074000d00180080010448a04040f07801c440180c1c1419414000f0302d0b0710342c440390f070719100b4000c1c02081c1c240c0d142d00041c040c605002545020f40f5502500856001c8241841c0b01a50821441a00e000d01000041211407600184c8400701042985805100d60b640325074010081240c070141c0390f0400003045c00c1840c250f07207031031699010b0f6106d800282200b50508102d4070b00c4403040250070041d54400f440e021031601c0000300b80e03002120540f4020407076070300303040c0f00b2191300020f50321100702802d600000200701030b00b00c0d2a00c01925003983e203100441600c8042100c1201c03400740040d200d0a1200340074040032011400405140030041c1015141960b208080344d910301910405501c520300203d510400c0507848180d40303c082009182c00c612090a1400a00503d200560700505200007030384990000e01210b200b140707040304031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 522569514 1250 522568264 522568283
    0x4060f0b09040902030d081014010804150b03010c050d050903030f011707031406040506091f0b04021e040819020a05090a090b070215100e0609040813090207110d03052203 75
    0x8a1002030614841940c420b41d208e40a1030740814428082c280d500d104260583d280b10050311252a00c95081c1c440c0c0b000c03519a6521059414a80d4409024140e80c403a002e41d902940e502004111000701e03140035108080c0360304100300307210f49a40305242c458103550b0041300b414551032984545901c5e041459100074140c4030407406511103010b010030200c0c0305070300030300c03d5440c0c96075800060350312412003c0116081103a800b6171107600d681745620002d9114000f07440146094900100302c816038012041040403903030001001d0041210a114420140c41d118090000710301c01d07607000134041400c6018941c060700c04170002800444003074101500c4a500f2550f00c0d02d45080c0040029244c9560b602d180044103043c6000c40e182021101d6090300f02d4080c034846080b1510307120100001c00801801c1503500d40750510529403980d0064001c1c0700101140100103a50700140d1510301c441000c1c14072110f10030103502800c0800701c0d0b041812607403e1000111000307825090801854118402d41c3c002500c02d120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 522570764 1250 522569514 522569533
    0xf030b0a0603020c1b03122506062111040902031f020c0c011805150706050f16030b090105271501080c1603080c0d0c1d04060f0b0904090203 62
    0x40560007070015000510651700b15020240340c625100d010000300c1c503095404104529242d0011001501c880c03903500003240a11a581000222002c401d90429101301d903582408005d903c0c00d001c4050700c4104400078291070003649848008200800a810500460311654014110343e814410384825507102e41b0706a0748402c0495244e8001e4000c000101305a1250f0010031079290f00a100341c07101050654111420715007014103200440301c8c440d800340300c08403041c01005c001030014081c10f48102e01d9609010801d241180c142d903005864442d441c000d140c42d0805900482d1072764030702c0e84d05485050322260326a000001d0b0f000030086c500d5059a8000507043c00b03000e209210040502e001050980c0c8451154aa4041006603485520000303400c0c1e40741c9401d9000021f00490104e9444021001c20b03500b401314080200b000d90b01c4c3c00055074001090b802e1041d0b1381d100502910003240c00c065404004285c10709080c500c26200c18000e0842e0f100b07000c1a080059078480e0030040d01950301800f03444040c40c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 522572014 1250 522570764 522570767
    0x8060d03090e1e0c070b0117070b0c0d020c06090d032a050105100501030209060304030309050309120a03080705031b0d061d04060506091510020c041a090a0204150f030b0a06 76
    0x6a07840080030b05040c0741800704c0c0c0c03001912015100c2042d0449043c61082c0d18200c81c024096510451013070860103440e00028801420402400751202c0d00b8026242a0105080007420505c8031402c0b140301c0c0c2020710503c2c8103330b02e8250324140e08681c1820b00f010203040048004607e805248002e0780360040f25402803040080c190403d034000c0303005c0e04003403060030f80b59001034069004102005802020510000d80461b201e80c206048450041c07003620316020b00e400c007258000c2d0310300ba20640750f036024070541c00406034444110340d44a9071510340345003142006902200c8520b4102d03100000c000001c03c410328540c840c2d5010000800b4070101c00c40c0300000c12202d00e804400216015910146030100042050070300e20f507007910841341c90054854483e0982c00f004401018441d9240071845040940c4445440710301c64140d014684c400d4250400840c2010800e0580004014081c454018041002001459206590121400c1c20301100d00081040100e005040c1110300c941c1c030045c100d80014205 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 522573264 1250 522572014 522572041
    0x110316060f110a03051615020f0702031515010c080d0204030615060f09060507031701062705091302121209150a090b0f16080307110a0308060d03090e 66
    0x40c0341c180c950b0220380031100c00841c1ca88400c0c0c5400780102d0760801c8610140d088040e4a1041103105c0c104041401d5440c48009089800003c0b1783d280f107102c0001c1c0d40e030039840c04203c01d5201111780d545904643c513050540803000c1d581084124113009080c80c2c001c08200e10300342503c100f5080c00c03408548950303032030401c0b00103000310300d01002102c610884081061440703801140001207241c1c0b0f60803502c901d404401c8079158844003050301040380c0c880c040c44101141880c1c03540200800d94801c1034219070b00b01e646624848004803107141094014302081503445419030240d20541c11031910000003414000302e4000300c10158000301c24028012013850000002d00901035611003a05c0d0304181c07400a51101c12203202d040d0b01840800c2c0403800401501d2561001011804643c10446090001c8403e048500e040c800000301e4103288084104a0b4503075000b5203a1004020300f074018441c1104546014101117005484c403400b850200b034480d002e16008140d600010412448410054905041c1c0764564 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 522574514 1250 522573264 522573287
    0xa0b0303070f0b09070303020a031808030c060a151a07110d030206010602070b120a05280515060304081e12010312020d050a1209060f0c11010c0203120411031606 71
    0x4640300002013070130008005a1102569416001440c54070116102600d94007140b0780000c075000b80c0010089000f00043c4042c042000d0840010015820190080c41c2626111441d06502c102d0503031040200202800c020350442c010650350950310246400d0802e280c501d017007100d0307800c113035400c8243d42003550015050341218400e0b400c0e500c1d1b107903c60700a14900d00c00c414800c1011081240440c010510a41c021900300022454910700004d041e09031500880c10b414280103269504d808008150720300c080c070230203122011510709265180543d5142801e001e40c8213100110000d026640007400120310032102d204180c840d4444903507941e8a40b0300328604480500c40c005001c1c98080c40300181c0200d041d9030310017409803101c040000845040d03c008180c01d03001950308544034514107004a941c2d201e1003100301d5250380c6407250040400712503420741d1500702452085520802100b5020b0b002880247d80056200386212201070301c0b100080c2ca84600d0a607810403864403401c0000303d40340c01541c002c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 522575764 1250 522574514 522574523
    0xf03030305010801050f0711161805100605041a071703010602010b0108040c051017160f080c070201050f071502130e16180b0301060e09010b210a0b0303070f 69
    0x6681c07074900032400e9680c251400012407003d00085101a4041c02c8900c04081002d811980d62702c4244240400c091100c0d8002a0324a1000c692840004e00d2405200d501c00f5250b20310205651800c00300500500c6984101c1c007184042d0166061607126070350882d0045600600e4000034107400032402c0b416070f44280b0a000c0550319000100140354080c21340079101c0c541084641c1c29803854070080c480c07000801c0310140200724480310452011043c0d081e40b540510300d5440f140070003804c0d0f014058201034072485003070103208074035041002015051003201c01d044d9082c608030b41c8a10741d12251120314028940d008003454090310501207011170039406001c24211034104080082d54881c484d460012041d500c00a400c42080c005205070360081030280110102c40d040d218205584445581e46900f00303800000000d40b122f00e80541c41d280c50801e0038090510840894588612414050000e410714603820198244a400050302c11b91168004031103540d000d800e99079902c03258034240b1076141c030b0f41e0000ca4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 522577014 1250 522575764 522575771
    0x10b010e181503150906040c05011d10050706021204330c0e0904080a080c250303150e0f070e010c0803060a030c0603020c0f0f120f070204060f030303 66
    0x15441c000700c0a4900d03080503000c0200c1501c60300d450501c0665804400c9405103e4201c800b2621510101031902c100810b001504140c146840c00400c0c0000c158009810408003c0214550b40706250008000c1c0340d046071844541b0f07403802d0056516020300384c0b0140c40c8610110b8450288010025420304c124030456031840400519404095070002e54030181e4000b40c0000d1504001103403030ba0214a6805160400300300461003400000d8014200302c07021103580c0c1021884d406510f40002c101354010f1640940d25040c03090200c285a042c43d000712400c004080d1280e00007060600035440501d11076a480e981400c943c0c0c54070755410310b030281600c02210014000c0002605d01c0d02ca007410b0700031114142d550500880c0117481c1e0148681010300502e40c808882080040001c0c41c501c15200204100c4d00d0160715040c540001a00307200401e640b1041d00d405c600f1034018078140115241d010100106025078543e030541407030000d140141a4000d4001e49011004150b00040c0803880c422640310fa507050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 522578264 1250 522577014 522577037
    0xe01060f09061b030311070f0311010b03010b180721150e070c0339020f0d0803160e0d060b03070b211509070e0102010c0e06030f09100608010b01 64
    0x4880041d0010000c080d59008203d80b070b000030348a0b0b0800c40381c40d000b05118a050014644620340400f542c40c0d03085002c1031240201e40c61800082c013a4101450f41180204013844080e80402e484840442da210300d001a0100000d24080c0201a0100d1100021040742900e60700000380c130004024007040e00c3c500d080103102c002240203030881654424401ca1341ca49545d50f442da0b48c1a500d1003511400d68886407040740040071003003958840d111800c2d50340490301d004019180140301441d10004481c074090320415103c407020030324480071280c001c00e0140e1440c403c050400012200f020031035203100c1d84441a869248180103080d0800c0715403400480a603403d807955119201d22504c507010901c82c460310901d00311541140d801d1a0706500090b04903003401c8400c6c1980019001400440300240800d8010032140c0055a0910801107200d94504004c3c8218030303010009040e602001b0103410428540380c2c0082d10904d424814464a00401101407002030b803901a500e02030004c0321a110300294194102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 522579514 1250 522578264 522578267
    0x21b0402180d050703082106030a02031c0309020307122102190201090e0a09050c0307080c090405010b1305150901051e011b051e010c050409150e01060f0906 69
    0xc54003000040c200c0301d6502503011041c84480b0041400a0307881c3d004260001010502190003404803c0c520500395510907104080e52201100141440f406039200d82000d000580300002c12588483d20001354510400008104030042c1014150094040c0200c0030000781180d030480305041994443e14940035032004092003c0e80510307090685400690141c40c0015088108c090141000360041c58120b8405440700780f0011405401d6641d5045155540c5500d001c0c850140003d83c0f031510124080c0c40401d00d04501c803507840e001c2c0796200e0300c6076080c0d030301117010404250b0001c2440400a00110342005140b0407035402020f0840d118289182070042c20846490685d00180c140d41d001011480c0035081e40d040c1c070b44180c01c0003203a1030500102090b803100150b01d40400c15036103132041d8028160010f66141d040f01d190040300e00c100032a8100241c05107502c2e00034082d1016104000b900003010001c4511080c1542019807240180003461000481d40e298480182d0100309065203079840100d070786200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 522580764 1250 522579514 522579517
    0x40507050a02190c170d03061a0a050d1401030825031b0507170f12090a050d0c0302060307030209011106040b15030718090318030f0605060619021b0402 67
    0x40e014010b030010b161a0200401c2c0483c0c0101090049216408968a91a407980c05200720740305c00542e94028000b50190035403600500001c0e1581d512991440d416109410209024030400030b4148000440e820750201160b030f204448442c5403042d100f0031542d4904251409034010081ca8103446401013205807095070980c1031003245581aa03400504944405008011140d1080126100d0052030030001b0074001582200d0780c1f00120201078007144074440f0726a0700c0c0503550782d01c4d141c04c90010310402d0126591121028204c0d041542c5d0a2140081890301a5200070240c2000b980000c0100c140720312030f541940a0209540280c982c1180c80c83c030600100c3d62544c003190010542528078000444105040c07454042841c0017508071003c1680b280c1c134408483c0c1c1d02542d80c10100781d86039406024160b104003003003000da9541c95010051030864894120025040502030812621180070840c1d03900c490007240e040305006946031440d020115002911340081031b807040040440e01412180c4d91038140f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 522582014 1250 522580764 522580777
    0xf03180c03260403060902012d020d031a040908070503030114040c051602060c0c03071502070506070c090506061c06061d0108040f02010c020d060203190204060c170c0a050c04050705 80
    0xc524078101844c550f0345030b02501942000305e042040551122004510300403031025680c0342038015543c080c071070110003850a0030710003c40d0100340c01e120900b003c0130109880440444004c0c5e5000c240c044007814000071521030300384010b2083c800000000380f00c034048000402c2e0b411080b103092210340c0d0a110101c6503400f038030f441d1005048003103000b180149001d0000b4042480310805968150003040c3c0002e09010150340400c01c940c007a02901110241c2c18403000300989030031594142008a0fa4607058414127050050404150390b400201d85a40e0758041a00c005005108551105011085001028100078410540843c0c0341180701d180000c41600034090345c13441a0340b480d502d40d42d01d899004081f54001401c0e4140010a21840b0258455103003a800007801414050380e60304004009a9410400c003500c038401d20702c180701c180f00d260742c40301103030b1a01c03500000f0364100b1610540c40c603100b521480d00005014030809048008000000c21000c030544012581000540c0e25400f0a030351900c50203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 522583264 1250 522582014 522582083
    0x30d0b0a080c0904060609180c080a1511090901080c090a020f0f0315090f180303010b0409020901022b17040819020111071a07140405010f03180c03 65
    0x101c10b00d0005081868640358018050400800c41550310038094049860b0102e1004528800300a00307070911181c0c0c1c8070140181040c00040840c00b045031034100c41344000400e41d02c1065151360806010088410956424510040000302c25583d114500c503038585c8908421030044160f000040c010050510035140007440e46061245051500300d40041031360300041c00000842c0600030120110f45480503417510030800240360101ca0708008010b101c070784034080b4101d800790380204014025901c448040d9012107000f00c001689a10b91440181d00b071118104044200c8040ea2503001c0000074844c40700003040000ea182d50081c900c00d00d403a0490343e20111005002860304008080b0082000750074004240c0a0380700001d20056110b01c01d90b29a4044281a1354013488050320810801c80e03482080d41120711814400942000d404400720765004a208090604c00e05681980c80c2da4086d40060200e2446c00d603001207039141e00d03d400c00d9076030140d01003500c0d400c0c4c0d01500b4000d0030f40f000040c403c412140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 522584514 1250 522583264 522583273
    0x60602060a021c050408070b18030d0513021525080403030809070b04030c050a0504090b1b0c06180705010f080a0b120d02010c11030a08040b04050a14030d0b0a08 71
    0x403007062502075031214010360400c4800e4a200341c24500c0d140b04050240c1c0c031030f1088941d40c003a9400d0803402c070f100140007a02c000c02440304a00a000001044500720350f81c0300400728140c0d0f1400c40e010b400b03008403c8003941190a003c582030700721080f4001001140300e10321010114407500002a0b0310408072200080c4070400400061000c81d0142c00150382c040b004d9000c4405c4192a04800c00480d00240e0007202c4591f030140040c0f0840c41c0c00c84d03640c0e014100644d800c010258007501c032560017190180030700b504403c0901d1018045c44644044401000301c0004656190400c003012000e41418688400c1d601d01500102280340e40c881c0e68048410785441e030b1000c0b02c64852103240801460b46410840e800f016803801400b01c2c00007030008851000302c507000040d0102042c60003601d00031041103004c50680003040007445454004160760780042e0026101c000a03581c0703192280ca131100c030b001d0181440302661180010850000010071105503600f80c20b00c80340040342c0511140302d841c1e020f03140c0103401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 522585764 1250 522584514 522584521
    0x20609040f1d1605010e010813020a0b300601120c020a1208040507050f03150c0d02070c080c03070608070c170307020102070c0b070f1707061e0f06060206 68
    0x509810004860403803140002e0480300020155500c2880051030714001c1d04801e140056031028207458000401c0c082c02c3c8040100315083c0002c01019000f4603d030b80061400340824203544521031142d01525507442003030b42d140303c460000b440d505c00b5114031024802c0003060a001c5045010306690040b0411385a803400a0341410300c842c054504880484118800c14400c480481c071098a0541c0c000d545880d1840c0301c2c01c1a051103800c04400350405130082d03041c1c861407041514009090302c0c00300c1c499204600c5a031a00c1400702e606100d01e03003500d90304c41d002250380000e000e0968500d034212914402140c0390202903d0505840f42500d100b22004640241c0c0042c010a00402486407103a200e802083c00f400000d50829501e50000d5030341e04e0060f980810b4080800207480d03451000340c0344442d420341c2400065a01c1080d81002d00f5002005400101030340241d0103604800c0d00d4605522060520820901c10805030b403504003000c420503140d00f031040200255140344241016502aa07000d003c9556 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 522587014 1250 522585764 522585769
    0x1804020307050d18050a0b091216060516090b0d150305010204171f050c090907020c1002150a11040803030109020304110108040201021b030a0b0f3301030b1201050f06031009020609 79
    0x11f401060f010030b07800350f14140e5403010b5041d0010040c26060024038800b0640030304085084030390040246c1c14200341102904140e41c2c1104d80c4104a501da400300c25503940440000c1ca01528881000027240209440040100641074014105a413030512504c00e1403600b082103541e440c12584200034186505a110004500c202e412071075001c241e500c0c0307080c0742c101d0500214071141c100300c83c00001604032281c64106450070824520040b00c8a10090003400000d01c030304811500f01070300880d00780303580d03058502104e40c1d0b480503100100404020389440c2c0d0f941e00c4049001c2d60040f181190300d0003a50648000560086440502558040c2d0080c0341c8400594100d40d04604c600000f6075041c070801c030840001a13800610f85104049210b1003103401d04040c0c9803401da145541038001d08058511504844d2000d0419201184074000d1030082a001c4101010a50b1036213290244400b070f5080004000d0206801035074a0b000d10f0054044592500e04a0748100440e00c451000960202042140c1c500c0c51 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 522588264 1250 522587014 522587033
    0xb10080609040602070f060c0206060a0f091503020312040503060a050c0d0f1e0605190303021506040f0207030c0201081005060a0503180d081e0c0f1804020307050d18050a 75
    0x14800c00f0300614015603505c8a1021015210040358140d40b80c58440b4192541800340039002801074a89803034003810495010035013101c50146102d40f0b6900c1c0e19506210840801131001035030003400b0354038040e840d034580107801d40c024051a4002d01c29800415620180c921940d840b6040302d40500c1c3c101000c04c100b000281c690030740090645500e070070910910b8011602c100c5c01d41c7e48154030000f90070386804103018081c1c9015030380c4440c4884558081020940100b0041d1020314111582126952205d001400402160801004a038800704d05e900802d030f08181140c6da41400bd80b1056416034482c1000060701d0494021640c21400c00c2c0045c00000703000710080d58009081505038003100b0190070803a8503101042c0c010b480000c5084051100d60a411070005003400740054103805903180506a20815220b10641000c0000d000520003030f5070501005100b8420f180104103640d01c0c10008001095600140f6916035410300c1e14030a001140003d80704072030300301d43c0031000e0f1061a11544070085d0340c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 522589514 1250 522588264 522588271
    0x8161b050a0e0604091502090102060903190c05031606020901111f02282003090a031401020c0601090f0606081b031008030304060c031d120a020f160302040b10080609 73
    0x6174580503c8400910100d00030070b11004400c20043e100e50566000925118025001da03045800402205040811441014002c0300c2e03603041210004480d80740140c030f144600d4600d08140364400c0004804c00150350000c21401000b6a102c07485d0003684c4101c107803103008031410f00002c460305800070102144250080c200703a00f120300c8540300c040d200302c0c0780e000022622101d100014004000700d40c1354800307282c80580c00c03e092034001c6040c1403006021518240240c00054603100b50300b0a940c3e00d250f8250106e0f00c40d181e4001c10b80710b45503516080036020781034101210411600307014020500a01c1180c0040c0710303614003540410b4055040d241c0134616070024203030003000d00c4c60301e80110f52002d08100460050b486004009940015110001c04486e07103040920070160252545140c9104002240340d8501d03401c161040d501c0001d403400360b280040543c5001003d004e02d88203134050301000700a101c11240240e07010f106023218441003000502c020710b109400b16000d840401c3c1c00382054200030b5030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 522590764 1250 522589514 522589519
    0x60324040b0402040305010e010606080108030f090d053703050405040b1f05070c0509060306181c050424210618091203050705160f08161b050a0e06 65
    0x30740d440c440c404107040e40c2c0103401c1903803142e442d981c40308507500091203120b0061001385407200903941059210b54491044070000e00d03c1c260007080c51121039a0b0400001901170303022003120340107203241507506c0c190b10b01d8401e00d110616500020f10403064803d44284501d079403590302c4500d007a040400f08801049504016604842c00c0c4400140c1d80c400b01c0300207000382401d03440c2c080d150b040c0c03440c0003829814240c0000b0701801c105001d000307042d01c000458a0700850500e20030701010421420307a51401c405411400c1105000050340c0301c00e80d4228000304140e6611040c1001c10030341e510b01056200c543c48481d800092080440c55100c24204508040800c0e454a40403807004c0e0f8849041c414404507215064580ba03503030f680380003001000c1c0413001e05030145090a100c940381820002d8294082c955031082d034039041c5840101005034014140c0085540141e840380c0300c251030360021601d000c250004a52558082c1401c3e4520402da10b510381c101e40d0f0090051404500305000c00300520000360000d40c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 522592014 1250 522590764 522590771
    0x4090603051605030d1b11090c1b0102041d04020f060d140f01060f1b1506170c010203160f0f052a130e0f0d020c19120f02060d0c030605040b06032404 66
    0x4071f82c2e603890340d00502500d021141140c4640e1007640600e842924920040c145a03c1040104204560180e40400400070401804007503070301c50010504050084600036800080051036084071003c1d64082c000c29229901c2c04a25a80d0301c1122a0b1100f1b028052340c004914001114060070348101000d400315174440c0c2c1c0b40c2d1541526903450b031201c0b246a58603030802d103441740404e0020028481c0031101d1040008005c18034840c1c0000040c1d102d124034a42943c034500210300e00c90901401c083c0344141164441038a940003a80c9082654643d8150a0003001142d50b42500030f00306084032840a035001c00003040300c1214880a030021005042c02d0442c05014041e0004001041c0418080a00c01c903a40c1d0300600002c2c0100820070461000c01c0c41d0407010510703e0001800b200c092040107220150b03100c11203090f180840d00008140d4059440155207a80c02c05540c940107641c190401c0c0c044030340568007401111115002c0000500048400079181c41d45010780e12906000c070342c5a1082c043c4040c1000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 522593264 1250 522592014 522592043
    0x5010809102a03050711030715050705090306090a031403040c09020d1d070602060a020c0604080d09020603041104180f020943140406080c04090603051605030d1b 71
    0x2811444070b54040b840429560001c100300c40f50403490540346182c4401c055071a00c0c240d0740c1c52107074003403c1c0d10302184d8486da81c0002643e01c81c0910200c40c6010802030480b03000f841c18042c90399036203c089004800003040c2d5400007482070b0958042d00c0c01513034452408000f007828000104025085407526802440e00d542c14071020000c0800311078844206400a007161905000c0042d04d0048058141c918441c4100804000c0850120310079800c5940521030680e2050007a0501010b408807441c00fa511800000500c410040c0710700c03014441d503c082c0c0d81405215001e111100c0c40d4a01484064020407501c11003400601e0b000a10507404105c402c004141102d003130220f030292038150040080c2083d0850321021450380980307800c55084040e8075000c1c100c0554280d6522050259128074005c4c440c41c0b10204001e8021001610044c0c900342e84100885a5a402c0c829a120100051185124541440401d0038107000c5040c00c03c0030b9141d03d82e1400d03001d02e201d00d45807152001c80c007a505a11010580b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 522594514 1250 522593264 522593321
    0x1209090501080120040501141e121f05010e0607050a050304080c01020705040b0d0219051c2001140f0705030a02070f0608040b15010c0204060f09060501080910 70
    0x3000d000e41107500000607900f10000c0280300718031402c02542400501888200916a44207000c02024218608010b854500300254010031000e110303031800c90103601044000c01c61a00b25030b15171042c4081019101404000c0b0700c3c0300440b1400c3d0007054000b81500a0703540044c1003600043c4141c91050f0103e03400c00c0c8142d1900c5055030004d4201d061580c00038102c103400341da81007241501820048404103d002818800070321a29030a0b10000c1c00341031a400349484901c2c4011502c8010b26001e013502c0c44001c052a81c0c130010742800427044130050a03018030318054413403080103c010040181c540d2504031a511490690a17004441804041c0790700b0450200068818400b41490680d503400400045090200d071b512000d402c0d402480030032400d4402c000c0418500c0356101d4014018001c04400203500500407508030083d0a00070750800d0a0400010340c00d40342000d120102c40c44080100416521000111482001070320703660386661241e078a0b408100d40590007403103200454810107a200c03980800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 522595764 1250 522594514 522594521
    0x50402180a06031d030306030a030f0c0c0806040c08031303080f091914060f0306010806011e021005060a0b0702120115030507060e060c060714040b1314010e0d120909 73
    0x400c1c80029181d1050055500140300050065613181000d141180b800e940032036920804e200010f01046848540400550700450520850350b81101c200159103446e041c5d0329640354020b0301c0407110034030303110700c0002c03106804000ea8080d40ba070100c1070003110303242d0341307900104e900102c0d0400000c00c01000725059944d2007800b0541521054003060b21580d1900c9c100e2007034400446480360080008104a910807115241203035400389007401c1c8403000c2d450740780040343c142e001c410703000d001815111a40d50200b60005000e00300580c442d001400701e5611316041c040030003018411400310310414032180340146050701c0b43d601340000010002134210b08201240d032102c007141d0b00a6846400010b800e01c0141c0e0b2140020806401c01e03941d0902c3d181042440b142d407040020b02200801403080c8004c000c00358250100ca0082c240007501076240d070b860232110740c903069851140c03100c410b41101c005031042d40145903496280e0001400c1d4414810241c0b6055907a860a02921013000222540418182020301c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 522597014 1250 522595764 522595769
    0x9160804020109090222081f110904020f1207030b0d0609060b0d12020f0102280306170705041a030706050d060f0e2a0a0c05010b0303070b10090c0207050402180a 71
    0x10982580851a2035100c900392035074110143c690440c0210100511000880405002c1d180c40d0001e0450349c1e08080c40c100303000e0200103c1e070003400051640c1ca0401200040d0400c3c0f007107000f0b414140c2d110110180c0c04c460304080c46941290005290b2004600140d004020704d90040e04003142d80d612240000c0c0410000000c1160700c0001c4e2010314401c1a8100003000c00008030000031460f04509882013403416400c01362095070901d05521701042d0b184280c00060003081d4991249441c415082d50250302d03001c05020f114055031415001845c2010701400381c030800c46000e00904151400d01c0001c50743c80e40406c01405410742c0b03c0100007a1500550007000040560412304a914100030b0008486030280c09803032004e40e28981706405107461000201c584011103414980214100f0f490711601410a40305400d9040c0800b04400b420701c040090744030f10519810920080b520340300c880f104125645500e2001c01603012000074000c0f0301302503006250843c82150741042c60042540000d00030300c8a034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 522598264 1250 522597014 522597037
    0x50c0106030b04050f070e06041815050603161401030c021e01020d060b030405070b09010909020f07170f0909040c0504020705071410020c0d0c0312050403020906091608040201090902 80
    0x102c200424040f06108080e100400030001d05442803508201030080d9001410344c034440d984d1403100e42c1004030944140011241d0024030140d0010707115160000400302103c2030390290161000d281e0740380c6030291103030050f0358509141c1401d240058004400038641d509446081d44250b1001101d00c45583e201d03940e03090072a50000d6900c4003c464140c045d50b402d0390200b000b20780248140310000e0310125601e019121204011520b801c1d032600100c0711186194070401d1000d2000503034442c0c0032a80b2005101d40740c040c0782442c40108506030700c2e10035841051285107520304180401601843c0c40c1201e80d4002d40100d8001c00c0301615800002c040364000c0704222444e601504041202d041c410036045070800046030000050101c52402940700c10303403000310741c0c402c0313144d1488181004614040da102554001008040c0b2007012607010302203034031900003a031113054140c2c001606450001380d00340c0b107071103e6064889200c0a030700b010703030300b203c000b0388101e060002c0000003195003c042d102030403040c2e104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 522599514 1250 522598264 522598283
    0x501020c070b071e03050904111b010e0d05040e010b030402010c0b0c090117061302030c1b0f012405010807020f010c03091509030509090c0d02031603051510030b01050c010603 77
    0x3e038503102c3c4010341c44000d01c4500228a6601c2c40120342c1150503100d8040060310007045e40509001031200c00d00c03402400e4101301c0c0181e0426084248154408040329032020110344203151034110980e85801988140a05521807000502020060354061500684103040005403c1c556641d0300c00400350840310798481c00400b280350b2a42d503901a03840100c101c000c43c1098240d003401d00c0840e038a0190300d04c27106802500000403440f00b610403805c03905914007015080304c41178182030016851b4490012031441c00c4d82062072024601d0520122001c800200e817401091140c6007000560b0030840051406003540200005401554028040c01c0440c030f5140e07400052550252178402d0f2800003444007000b60714944074444000070b80005c100c0348001022940700c00c00d130791140d21200d214410301071740020780780c00803007441602461811110010f65091301c1c00c0c007965a801040000485074000c03440e40c401d611640d8069002c2c000e03486040102c0061415030715051a5580041c2074418035801140e46051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 522600764 1250 522599514 522599527
    0x609101b03050304150c1407170f0319020405060d0b031e100c030e0c0d0c1502030d0e1609020d0b03160608070203120114061207020c0a060e13090501020c070b 70
    0x9001c5c020300300e21200c1010801c40c1d152056401850840f0418408450f2000004d200341481210310a4181480c0d9500314180d65008810300440d035904242c90901050900c0403200310080440d00075101a40c5018005505120b6003850401c050285103480d607030136020788410f510780940340000101d01d9042c108020600040d903040c000040754240403c45003014036161045100754000b10b6028207000c2c0842d0f0500281c2807500700302041109980c00300c010035042c4032076811103c1e004005001c1c5090105000c0020a289499840c2c0b00c003166001d0b80012007006805120460171070b40549002c2d084d25074002400d20b03580b40400d1034400440310610321100248010001070340e10101d074681c410098400780d42448081e0007041c05041d810b0154040600c07000080120986542d016076010800550003030300103042c000e80c06511a0200210369000b4010f140f8003180c0b49019040451300c010001d016810300103480301c42040100000e80307084505540820031440a502e0402034040035054140c40c03030355101c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 522602014 1250 522600764 522600773
    0xb0604021813060515040614030601030e060708100e09060f0901061e03051204030503070f050309060d0506010f02010e1b12030a0503071101090f0b1302041e060f050609101b03050304 80
    0x94990000c00c5d0800104024849550701c900180742c12001c007402c40340c998690300c00680180001042c12403151149a003000380e0b60750f010b4102405181c64180140e40180c4421000b42c90803005c403030340746003948504040b800c00d0341014030650f40148940d00020748103840700c41d0070700030103010b0100c10200419400180180001072040e007504860580341c1c11b25283c42c40c0da58644902980401170070306c020f80051001880b070180200d80403800700520030307962850b89031402401407606585070b07030008100c80f010030000b50051181150134001240142010001011044a2070a0296080d0340000ca4022481c540345010005013a0001141d00e80c82e84914100c40e00074114050290b01044c50f0b03041281150200c0d501041488200d6004961049283e41d156000300c40b81c49411002500140307080e03400840c0c03c0e107140c406031003841c110f441404101e580e594003990640b80d6020b4560b0200f0704000181140c03400160042d510003840c03c05494a5043e1607820558030f81c400e90581c00301e08000108030170030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 522603264 1250 522602014 522602029
    0x303060329010e040f08030912040906080c09040201021908162a0e040b1e010f14040b370e06150c0703081803061608060d0b06040218130605 62
    0x40000d410030070800d244c25110211a0522000040c2c204200000401c482c00e209006100c8141540c055007951181d807500200001d01c8540315100701d038000d03418000018913154980340e02668050340102681ca0110b00d40701108416005d0486000c070701003181c400b44080b11200030091500540f44206046003502001e150703505091320b106950030000c00148201c104e0000c1a580198003c0c1c0700e80789130750321003036000f011220301c0708041c010004a400000d40582080080801e803500c5000f08080c0c03640b8102400240c0fa0354400c407581c051071542c40d141040d0002001c054031100c0500849031a15290000322102503c0d0741c010103100100001080b26509041c14000c410b6072013415818500703900c2c0eaa206448210500004201c5400014420400321114108800c40341d401000e90b103090030f0801e400d0204813030303410040003c80c40719800504540b0300002c2d03100701c031500030340500e890f9500c00040000a40c480702000c1880c081508003095aa204c918846462904107140000c3e141e08200c20051003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 522604514 1250 522603264 522603269
    0x6061d040b0a0507110a05070303020d050906031501020102070b0a0b011806120e010e01020f041415030403030e030415020c0102010614060702131407050d0b0901060503040807030306032901 83
    0x1240a2000040151800c0341d80052215400100344e26083e104843c0c0500d5007420b143c1d180b007036200e95400c0c4280840c5041c00c82c1c0c443e800b20b4810f0b24101c80c5c240c82c0340c0180701d011b0358081c13018400070701040300c03502c84030355642c0d0144001450549035a440e0a41407100303954514100da07980c04c0440095070400700100540b180c4c1042c91000c0d03403400c0c81c0100011505480342184940b1343c800e0707000c04a000d42014080d1184240255100c181d0010602241d40107486242080c8408003121401e03420300090182e0f80c8171095440c40d103507070f0710b6440076000b0b04031070500803055100030400054001d801042003da28119540501880702000000909680c1c40c1d410084104d41e40ca007006440d0f5403010226810345038183d54503c0c403441c03003088a600500180c2901301c00780c1c01440170845a00d900800500502d150440200001001e80060044040007401202e0105800708007140100720307120b016004280c80703403402040c8140c40f6034850f5081480c51944000d0000340410201e0f003074a030f10750f0043c007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 522605764 1250 522604514 522604559
    0x60519110403060b0f09130c0b0a1205011a0405060a1b14060a0501050109180e121c0e030706020306030a0501060305010c1205091c200a0b0603150a0b04020d090606 72
    0x38002c0c0c170304001246210050802074150070902c010504002103001d04c031004200740e20809488285a110140810035050101c95010745004004a041406180307421a00e0b180800c4050900c8e0519050100b241c2c49003040c070003032100303036140c101c482c8803807900b4003141d81c3c0300e91401c80322800150580c0d4602034016001484032401c0c00c0060103d030340d11000a0084425003a0b50040c010b540c0c6021034014009030465441e14000e6892804110020354000e08004070401c030400c690805145a03042218440402607079150410810703200810300b280c0285401400060984582143c255552400c5541c1e80c1c3c41101c01e41d44402c2c10307844268026101c400d2008a0903024040c0b45402017440b40c949912074800804c1d0604040d40b1180c1612601d0142c00d5003601e0300201903807040200040f83d44040d90340d01203030502d0404d000940141404120704d4204c01031280e0100c2c06464582d00100a044020040b940203a824401482466800c1c010030810034024000000c905041074034090421482110301035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 522607014 1250 522605764 522605779
    0xa1b240e041404060b1c1407050111120901050d02030a051008070f0504020a110601060c200d0f061b090f0f03021503060301061701150f0f03060519110403060b 70
    0x14140040c00b4160701544c04100044e54002510002e094900e491412242c0241d942849404006111400c0d8204418400854580320b543d0340c011141c0c805c039031507100c802e50816202c1061017041ca10203010300190504105042502da04aa80102c0e08200c507100c11064455060002105040c00000080c01044014180036801e1109400103a44944502030149030300180c1c0311f060724411507500e00c2901494042c0c8001d07503500e240003000866280d200783c8038074000540d10700900b90b0320b400c0d880c82804040d0038055515403a84801080b0183c810065603d00c2d141c5802d1010223510302d10000003034465480e6201d4143c20020144140e80c0580c0088642e203001d044140003680d92080c040c13a4100548551030364039035640000c80e0240c0302c0c0794043c501c8035034246008020b201c03040d00107050602c2414240d0300560340e24800c2d81e0402e1010301c50210904803402050001c11b1590304015409280c022941c2000850f2000d03000c100c4454540708815203101040c244108210360144110b44101140c020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 522608264 1250 522607014 522607031
    0x9031713141c11031903120603031719020c0a11030c030a08130e011401031404021f1403090a030f081905040f05060a0218120a1b240e04 60
    0x40d020341a0450000610031156003280c08014010075100e6038120f001d416114000a07801d81e40003480280c180c04c4000c10ba82c1103000e200841c080c812441103d41591300c4800c0030b01c00d580c4038010550054003145074490b00c841d44403440c0c00d1a000824401c08402d0043c20a9001c5041c014100d0400c008003e11a4005038814091540c0000310300840c80d8000709a00d80e654250400d4000c130002e1a8006120f0303803a541c0000900210100100e01c6204cc02e803000c0c060305299600703d0f0358005c01254001c0d40080d4005100c015000003401c0111100c100e030070105040b05245541403005d41044503101d00c29400b0708800320070164807a11001840017a1f0030401071a007050381034041d400640000100f4030710b58510000d0103102c031003400c800245030402d090300c00c82d040c003012400103584400c070800f00ca95000c00c9a0341d4941003800d003003160b90800501802500d915a900e1200380d0341560782c20507000101090110396800b114024035200100f041c59988100d4070428080c040c041885000d41c400c03407808005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 522609514 1250 522608264 522608269
    0x3200609031801050403060c090918120503060d061b180f090b130903090e06030d0507140f060c030f07030902010509010e0616050606040608030304031704030903171314 74
    0x10b0b03940d40104441e51110340c581400040b81c40d805103038006000700e410891070b901201e4210048074141c0716074078030504c45c1d240300918170b08100b81d1801000b400300011414116909e441400503580042c00100f4000802034039803241c0c415100b90851314a800c1c884043c4c600c0240d50401da41d90071003090581540e42103440c1140918500c0c0b528800d0911581d101c1050b5001039441000140d0010320404041207825441e04009001500038080c8004a1900002141651400052541200000d65601460039080c0d0340c40818000c4100d40702e5081341300d1401c00150a90042c40310a01c545100783d01c0719120315101c80105c0751010003505500901d840c2540800160341d002c01110700c850003e0070000111900c02c0041040c0f403113003c220508044072848a84200940401c89500800e42143c0a00c0070a4a4284058891105840040c04181d03000214580f604566503160b6000d03000c1d040645072140d40740c44031f40701505980e022420360000044c4e004803601c0c0041508003e8540d68403880182c0d00491f01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 522610764 1250 522609514 522609517
    0xc060a0b010908211c0b0a05030613140102130321080c0301170c1906031406061603051c020306010f0f080a0f0b0301090f020117160c1e0320060903 65
    0x9480c9102141d8004c1e40180340d034100d440800c179214501d00c000d840200f100004103400074070b0b14841c0e003c00c140042c0c41d240029a15000d0f01400304003c1c0191180c0d500c0350140d007142280e0085554082c03010314a80c07511208000c008501400e185c2800010707202d284660503020744201d00500014205020416501b003050f2070546da040780c43d00400119030100035252100280c00300e54002208804540d004584000840c00c48045480c240814040c4a89010201200710b4145030888414040c4046001002036511200d0b8000d040444c50054801142c201944031f42054230720b5550000140943e0f075034803000d107940c9401c0d180b0703200030b0100382c240008259040241c180c0074011384880c440c030f034041030070390000e195160001d008200c03800440c5481c00c0d2007403020b8401da003c160040a45403600c01040c1c0018842c0319842c0e940c04540c00c103440c060741d17000d44038801600c1d03200341d132030034003180303400c2100c0050a8034000d03160351120403d4200d41d41e240201070380510000d0741100b0f042c0480402c0010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 522612014 1250 522610764 522610783
    0xb0a03030314010f06140306031c02030c070611060c0f1c09120f1e02010b06040e010311010f020a02040906230a0b0f0f040c0c08041706010609030203030d0515060c060a0b010908 78
    0x1140344c4d0380348c45900c0000d16006580070314107000d114040001c803070550004010103000b400c00b0f040d07400080c5d07a9007054030028140c407100307101504400e00207034401013a14000c0c5800700300d40003100c1c1020325002c100a80c582a0f1124408025911a010313418084410f403200e40314011407401502c00000c0074401401070804d2001d210700c012040d0b007200e9405000f90054200818050201a103503603171511142ca640d03000380f205546010031560000c0c1a54810340354000004800d03001494071039000d03802c1c00020040e41d1000e9070b41540e074460070500c03c401c0c01d0b88650301c0200c903d01ca44e054184882c0407012103d800a0f00e40c0b00c0c0c03000707a4244006031144d850070040e4000480780065500241e42040d5400124541c004201c00800100490303c5c86100c60810010840d00c4111041031b0b88a0340306a41c0c0c6011404042d5240e4001d01101c1441580c0c0d0700301650000482c6078030030108124101140c0c454111808190103504450208160740da6140309085801c0030034a003070700201e80383c0011203071a005081c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 522613264 1250 522612014 522612047
    0x1020c0a15080603030903030a03050f06040e1203040813030f0203120418020d0f0e03070605220618060609092d080d270516030503030703020a030b0a03030314010f06 73
    0xc40010403d68040c0196091b031400501940c1e030341c69048000900520003120a5084640032001066880c1440d100c3c85207034140c00c50040c03580c0c44006205040303507040144101c408043c03c000300c0305400840c08401c00114468980600515198810513003000c91801c4801c20a0b6000c3c80700304003c5c1d581035541000e900240780d0040e42e0344000114440070381302c241600b1014908080f00659548400002801822f014200400254403011003081010034140c00b0741000c540340c1e840d44404030b0b0042c1d0100c01042003a0520180d02095907852405a88455004901c0195102185014070403305c00c1c02c8100f41900c00c0025107003080031031100200300340c050044d20a910201d0300540c442c40940c410034030601505401e00886020100405e5400308441c0c0464140c0035074501a514102d1114410003581d52001c0903500316a500c0304120000c0d0001e520020030152500500300c0d00c0d4507252160005103010355808900e004420b220441c0300b4106038892035129804100401c203083e4003c440c000d100d1080d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 522614514 1250 522613264 522613277
    0x70213060801150e09010b012a350903030702120a02030a14010b19090507020a150f0b01050309071e0308030c0309010501050a121514190e0a050616020a05030408030901020c0a15 78
    0x100f444408003040c2c1c40302700410701200c41102180800c040b01002d007025070000c100d560303200007500312134405016036580150158801d000040c01460110400450540c3c1c0100701c400c1000c0301d030006071400503a040d0642d40c2c4181e1403142030808600780100c8103040c500b52507282c46004c1d0720711224070038021840f0386c05445a8a0001c03a10340c610a2003400e0001740c0202484090031a80140d050051554107000c0f083c0c01e240c80840314565000d9025648500d600c0d40213020507520b0300c141070100b201d41ea9901008040d00b18808000151200302840c081c0384090301807501e910300090654215641a00001d03c1212800c2041004440030b0100b005110390041c004030082d00d14190341c0018001d0703441000520f180c520200701703181920729001c16000101401c00d020365001040302985030f5818080142c03c640000000400c1c103547d403025a40c00c480b0a01c100d071607003907541c1c44581c2560495080400d1940000440012940c0c1c100502c4450100c100c903031516440c038220280c14180d0170281d003001446070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 522615764 1250 522614514 522614567
    0x80f1006091e08070b0a0305070806090610030b04090b0411010c2114040902031009051b0f070209010f03151a0d0507031e0213050c070213060801150e09010b01 70
    0x101d840c51100405400c8111880c081c2c58401c1c3c60aa86c0100404800081c606800110002d2007541018010100a000c0711825100e4030103101c400318150807040289a264280c80302c95071114450040d101d07008840380d406a080501d0800c1c00c0c4800000d207581042800d020340381c003160310001052001c03202e0108228490300303606410746110040308518603400601141c002604051900114890316200050861030303916003003440c04980040d5030300304034401550f50b02d408a078444401400c01d02801070381141826540d40c002428034800340c2002803540c20420040081140c0d1407002440c1c1d00c4c2c1c0c0607003408040b010314a508010a81d0a40c2c45110b008aa0316981c14800240015400365802c6601c00c10703202c2d00b00b8604514003004031800c074040c0184070061205e522003442441d006101c54055180350510355020400901c21020b08025000d079101c0002072004070900c02c4c80e00300d1144100500b403103445c0c040c1c001c200724030052201c01c0d2641403d141180c9070f07030b210071130500c505040200c1002504 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 522617014 1250 522615764 522615809
    0x30d08090c0d03030903030b040c121109040e0706120207030503040201080402010c02040e0303160302040b18150d0c0815180a0e010e06160f080c030c19080f100609 72
    0x500d4070001c1900300e400c410b0007406140c0d060f0045030025002e0f8800340000000082804212140c00100c10b002030b0390f0f103180000d00d8107075403c003100d43c400141e2101d0808040d00c4c00a07044036840c5108071016440071a00700314050b0044454600450800e104508100c09a02e01074154400140f0003810000d00c0720000d03085a02030044408401e8001e402040810860483c16079264401d84040b82003411300050302428a10078022039040d12480401d440c144203a05070b4259103daa1581079960282ca49210500c3c0c002d412006001600c4c0040d00201d451070031000044e01522002d800c4400c1c2c2205009070240c103480b21b203141c2d1121800c0401c0425280e46101c5404000c0580c1d6410840c654200a075804400400080190240c01009035148040029030001d46900040c011918040b8510400003403151902c04007850f40000344241583c40e100d001d5030b400318203c42507040c201c0880e8005013486003014610080643c400300340008c8845013400d201d4041c102403414411208030046100c1884a0724 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 522618264 1250 522617014 522617023
    0xf09010504031203091e021e040905030a02010903090509090318120a030e0f060c120c0109141e0606010e1e03342111061b06100302030d0809 62
    0x156005103c20211889555009018042c098019a2401a0440307510241e244013031500b00034603401840703424602e006005100c6000c0c059482194803d80d5088070101298050000f024500d503564000900710703030380f8a0050401079094101e64000d8040d00b040144a01d0000119082005c031100d24105082004e00095503040064060800602410401004140e04941c0300c0c01c070b011044403883c0b42d040440301030000074021a5031860880d8030507903a24688014050080c0001519400045108203d5071110a2060705070400385034550310a5207900b040c3c842c9150486581980d040c040c005605225000800d000320700c41c45588a004a80302c0521710000001d400409408054192000b88420070180ca010303c0b0150312940a20a00d85501e005c01c4c08006240c5082d01c0c213000c40c0311118642a556441c801000000c100c45032241c1400707c5480c0ea136400047c1008003580190040d0000701d00c11005d043c01000303400211a400c090200f4801a680801d42442c1096a4504903496544070301c140c0e441c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 522619514 1250 522618264 522618269
    0x228110402040b090a05060c0a2d0305030601030510050906220606050a08070e0d1104020d050901020912010e03030106080c210604140717070509031605011106010303050f09010504 79
    0x1501c00580007400a102c030740074220031007003101c035000040d941e14148079192280310704548450b0400703c88000000d1a40e00710400040040c800c204074000c4130041d81000c0b5010600a6002c91004003c2105941e414000c0513070000103000850070b0245804007140b48030070090a07180c424485060120443c0020800640b0500010b180c01e015850b680d81c00a403032a4803001c0320000050344240003600c6c0e90b000c1c406510400002800c00003c60829803504030820611703c9140798010380801c60764403031050602071540180300e08400140d540900500f00310b0b41d04050403840701a641420b01c03c8140f141d01000741e03811100d0300c1c180340180f9903c1000c15016031040850141520a216401c801100f07000340300b0398403a40c0265401c104526510204c080c0f0b04134216038640005420302c0c44c00c1c0c8001c40e4010025085041410030030f080800e40000a0308101404020500122076000100321640c0c2c451122941c407510500a020a5415078800404034401c0e8030820700700400000300e12050740d1248044400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 522620764 1250 522619514 522619519
    0x1c240b0303040902090406050616030c0f081801081b0301090b0103060320011b110f0a0f0e090115060c0f0c0b040b071104063f051c022811 61
    0x941e10b40343e80300c040094011855260149262107404105410210203c03034545605607184071340d0380100c0c0d0f000c82c0e400b4044130040398589c903051400c43c0014641406400a440b10340d02c00c9a00100310300004140440042015280c1c0c0250445001715805c01000c9905503000d0482c00b00340205400f0040c0c01401d40ca41c80100811000300e04100c2c0640222079082c1d5420003641c03400f01c0c55090003c2d42080c049400d0000e00040c5000803940c01030b140003110f410200c0409400e0102483e0384c1e040c003038113075442c175030150f240221100d08000c0c00303103004e10600c0d0345103403510038a594003030520000402409000e180140807a0f2091308690070301010031a50001000306a1607c1ea54944032214518075400240f011280300e44000007035a990306c0c060203140251410511040c40c00300c5035803148902034185040d91310b5402e5442310103407285403501c0000040035004800409800d42c2d84804080c000e01e03181112011500040403850200e403108c0013011002103891600c040b4203100341403c4810180007001d00f036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 522622014 1250 522620764 522620767
    0x1920070804090c020d0f0509010c1b090513050a02010f0210021c1508060a020d110406030c2d030e0c030703140d080c070f030c05100603021c240b0303 66
    0x10400114400070070540d24200e40c24400a04800026a076884025401368089007107070a181000c5886500544601e010501d841e010b9001151a40361000000030034265540345094014464080c2601800b900445540c16555a01207a40c403050345500501b03038000d041090981d120030400b4402c2100c5030740740541880071551854085886030701c01d10046280350700c1d0380c00c05028655003080907542c01e00316290000a041c00782d8492540100942c0405000010180d80d5000c0001c3d011303800c8058006012261800104903014120241c034044103107485400c0145400e81c0850b02881100280101081908020a000c0910440305041102d86040d0070341601c19144000241710b120f086211040300042d0566141c02c15080c012200440c0480d454611228200148070001d0508100c541c5601d009140810141890b0364415040c14003030003001d101241c490b00f061040d80740070903c5184000340c151240c01e0024007651443e40510380d0050700580b0501c4e400414008031095000000b4103100281540e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 522623264 1250 522622014 522622027
    0x2405060c032104031b1a3705160f0e040204090e0c04051602030304020d14060403210207200418140f01050105150a18031511031920 58
    0x8102c02c0324240d00080410160300c0504085411605002e904030100c803074190192202e0360135161024111f40b40e007030744846000100c0702e000341c100860303544417841403034554802d07030300c0ca00649030301402005c0c03000b124810581145400c9804062450300b5420a05a20841840024024000c503400418842e041201d040310140001c0b4650b0050704003111304000301d4462885d82c0300346286101042d00964400c0000c28050300c1e01107a010600b0f1310801c80591481c1203c0035280c103140d01920f0840100d1030140c1085c103000c100392a040114a000c54046041805a84400086160b51815401440d00c84c5084c0e44084e10346801c41c10090810702c1c4100c48511892800030400781500c110440c83c0d001c0c4408410140c80c060048034101e0f07030300410640c58002d8002d0340080503400340550074180103000c0d8210aa4294600280e0011070003a003640048600c0c0d0313000038098511900400e40b00f42d1040081090040256084020080c1700300c2e4006860950300010a1680e031625039451101d50000c00c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 522624514 1250 522623264 522623317
    0xb030f0702010e0d0c0f027c06080c0102150403090513060f090903080603120f090d1e050f06132004140601032405060c03 54
    0x20301944095000f04440075291410f01d448162041d0314000103041c502c2c1940c0072850902c400c0701220300082000a052140c04064a2103907060040701e81520203142c890481c003403074426400c0ba80300f00040c1d1081c0c1b0072401180c2005d210102c842d0b04500c868a00c00400b0066600980a011584074410812095803035098090380d494042c04090300600c54030390741d0300d002c441040016000300e0b41a2686100f05003004100b1800c100d0b4015401002d6a84901c006401005010b04c0e10003440744038030010381860181002014504003c14050180c3d0180740b5441030305504604440c1c0000170300c1d000c02d854100d003c0021304541014100600740c0d030000c038042099014107090b048200c0e44100c089038580b0035400f01d59904d8480803140c43c440e44020b4450100412205035650311008203d144650b05c4100d03107030020b41120315428000800c55640404c114181d60103100300402c00c252100c03040312009541c800b0940341e804902925005080102c2e21541044080003500ca080709105c284010300c07074900c901d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 522625764 1250 522624514 522624541
    0x3270507091508030306091e0412140a0e240f1b0a031704020109050d03030e0f21160b04060906061d1b0f0c0106171f150b03 55
    0x500128520380b0141c0d25241103400c0e0b40004541500d809142590b07210020080355403001803030701800c0054003044036100769121505510841c414501c50503503094480004000c444010200448103004200c40fa11040e0040200005c1d000300301c4110f01d50015001502d550301e22001c12100f4811400300d0117468055a9038060840b0303151125514001c5e8020007561303542d50a01c4800039012a0780054010405900d00c142d20b40c1c02801814080070340b96542010030120400020140e0000e9600c1541e801984400c0c4400d86004552400501c1c1c0d41c2e0460394000041c14061410102180700045d0700e0030503103442c04940455542105c507006403131400d410001d0203420118021540c1614055010400c280c0003442250800c0b0b4010701e6071038070b507142095003001402071100c2140301c4400f0320400c14080e500c0001450b540e12000c0000c1512031403c183c006c8100400b41c801003003504144c038040e80810b079404010201c400e4030380020640308043c62000241d40c017990414918034a0000800c0000030b02001e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 522627014 1250 522625764 522625769
    0x80d0e0c1903080a050d090b0114010909050709170c0301020408151612020a02010f15051203091503070318121704020307050609061c0b030f030408060703270507 71
    0x41d00d4a00c50800341c0419034081d055804014211501407102842007441000a07013040b201c1c0c440000307541d158075107418010f100241e01040030058102945121540d101102d20f00414101e0400d2145080881d0302511404440c09400d404d03004492400401260401181d80540005802150b582c0c1c0c541c10700c070742c94041c1c0380d1034181e80380e00303980110781284e001400e25007800c1c0381a07a0705090300010100d09404ae6003d82080c00441d034030f50480480000361032040c00000c8001d40719580c0c489181c401800720009400b84240029042408441003503102d421440641c005c050150590300d6540c2d403000c0e001840c014140400c0210340101c14010071055205420508419403560640c00f801502c1c400c0301000c044800a40680280e2400c00603400c08401134481064000c01c4541000c55143c3e03607625440001031b1900105840d0418041c85003020b100030700519628402031460141008142a51002c003d00a00205503540d140f101c0500f40507180304014070700036084442c484066007442ca03903642c0e150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 522628264 1250 522627014 522627019
    0x903160e062701060f0c0203010f0b0a1217031806010303020325050d050d0207020d0f02180c0301060e0d050d0906080a02070b0402100c17040e0703020c1504080d0e0c 73
    0x10001a07541d401c02c00301e40041c1600c0c04209000b40c4e0908808a401502d086078210038408068003500c0103a03000e000b6940e130035141c140700050b4400d054082150101043d84405400900380603108046100d0342c0301e08804144016056541ba00c0d94101610181e1000074003600740c7c0508800441010390110051658818101080898000904886260080b2560f0052031a030000c1e00300080e0500420203401e144d5480b100040c14041680c000c5581410114011a9422a40d502c504c045251032070f01621000ca11980455040c98416240d215911040c09900705010160701440c00039550800360030700103988a0f00b511081045000068040345031030190b00f02280283c1d0008480030428400e5030805500184400181c0c2c44607001c3c000c0c44880d91401c2d41c01c2115100c0c049010400c400006070b00c00b0208440681d8451514140d8021410090200d0003094010000218124000500500400c0341d45074010300f03e4641d450301c42d120b40f04050200c03450038100070784001998030101d103404411405 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 522629514 1250 522628264 522628279
    0x30c0c030a110114010e0a0504030e030703031205010b0306150306060405131401050105090102031e0c01140415060302090115031b02160e16080a020c030712030f110f0903160e06 78
    0x16860004c95941090080c5001513040300001000440980c000507001406030400c0b81d030340480f20000c60709003410342e0000d5000c01e0440900060341e4030240715190051100448003811401c0040015895911242c0350011840001c0b010500b26650001100c00034900100090010282100180701401d6070100c0d581019a50500000b402d5008d00d044603c00e5405074040d6180007920381c0c0e000c40c0003c81002c15100c1090a004000c52200c003445034040d4840000310050840c0780900d0601e44500344a00020007043c10b00104200680300c1000e0703d415212511040001e850b8051401c8004090380710074502c070300c03240140030341c1903680110703c5458600d42d120790040100c0e201c0d04040c0028406a40c0b41c94102da1358140700c0d200314424800740e5005004d04402510f0030062444262031a000400d0644400d02e400a01c40702d16901445400c400102102040c001d016115440c4a6607004100003005088000105a82c040c0d6046c00f88802204800e0070900c600e503240c50001c88000000c82d0014005d40c2c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 522630764 1250 522629514 522629531
    0x100e1b16200a080c13090b04030206040b0a0e10020d140411101106060f060c010e070e011d0c1c0f02040501020f030c070b070204060e15130b030a0206030c0c030a1101 73
    0x80c41c20300501580c040b80000c01600001e14240003407642500c8017000c195a66a0b40100000c2d0201d03980c0c1e02980c000d9004054070b00306401e105801c00d0010700081840c51401c0b030307200003900700460841001110790000680f109001c50340000034060450035007210451040400040090300e800990520100752494019264420402d984154181c00341e00c00c079600c240d0000340f551400300d056443e401009494181030200f100921820360700390031900501c0d6041035000740450045204864010078a01c0c0400000408181c0c1d040c8a40398098420214500001030191090012680b08541000b007107504000c81c00c0340401c104000d4109014231401400b550400421032a400000c0d1aa415220000f91000740e00d055804030305030f408840c003240c0003516160006094924990610b104030040003c541200007113070200000d074507002c1c480d000c4003846d203143c085c031076180041c0c0207180d01d606480040c0e480c0c641303110744603c0340120040002144030000b00101200d90003100c508a10000e10002c0c4038114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 522632014 1250 522630764 522630769
    0x50307120e011a0f0603040b0c0c030318060c07080a030e03092e0c080a030903020c062208240405030702030601230306010b120a06080d020d08100e1b1620 68
    0x81c2181344140e100b40148041004664201c403103541001d01d51501601c0c7c950703d07143c1c1e14150b030000c0790740071000c410340000c5070901c03070003444480d90224510b035001d8580b1215607146003040c021400004c0805507507408055840c24200201d42c0c081030002c2c000c01c14005407540c014400380706101c0c2403181050144ac0080300902039401c3e00300c0c00751310240040c20059400d2041b0000d0003416404c3d41184a044120301c00d54660300c0041802400700b440e01c20041b9820b0404010700304060344240480ea204408a04030030300210801c10024003880000341041d21a0b0414510f1030044000280d8140920340000a078010303602c40500720b28449480301d074030914070b030b20130542c558809118000c000c1004101a017203124010480c0e940c843c144d80e0b0005000c0d5200c07102589072011a125032000351b44039000d400d101c0c940102102d6070068004203282440c0e41444441085400094007444c005c1407402c603100c50000340300094447d41c4012603028049110a8204850035074207aa00444c0c0015002d03c4030559070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 522633264 1250 522632014 522632029
    0x21f0e010e0610050910050406030c0303030b0111031e07020406060e0316210201030f0603060c120203240622030c12020307061b200301060501020a0c0501050307120e011a 75
    0x3c9100401d0700c02c1841c500024003804800c02004011106038500c0c000c80c2c4d0b07070750b01c4c4144006140160883d60059040d40b81c041c04444102c50181c1c1070001c000303075502a031400001102d00c1d00e4008620700039140304076490447c00740a0390314000c1d03102d0300f81400803441c0c0350b100190915003c0100c040340c460130940c0b80c1c807680086841c06481403601c6030003040102c60210001d107a405070700c189000078049040148850440b002a0812104191910190713040a0750140c4248490450081c00310701e50f017402d1101c4503207298508001c0756420140310489070603603103107800d9170f1401c0c107010307600c1c0351001c0050741c0729540d8601d500003200c48a19601c00440e401100721014502c071503000d00141195420418150f800d101c40400300700c1c021040c10600d400007a0418000c010f00c2064490040c0d09a024130308050940300c1c039410040c11540031612000c045200c600c0e0200c112417080c00e189a480d00c40d030b101210150081940f0a0300541842d042c44208041540611041c1070048042180322000303e0400104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 522634514 1250 522633264 522633271
    0x60e1501060507060c0504180b0118080703020f03011104030b0426030718090609050624030109050403090e04030809071e09020c0312011d0106020c061603021f0e010e06 74
    0x1402c14003140000601c0c2d5801440d000200e410070fa400c159480003948030100b00c4803081c62009071100400b2086581203020b840c038900340308a410844a05098803965100c1003844040c0c403501121304aa03441c0d890a600c048443c40e9203626140d0345544904011104050a860854200c010f500410100d801445a0640c0c0040c842c800c0742d00d951107500c1c040701c0480b828a01e042c500158000c00280856080c4550382c003c01e0615808103c505d0160104400341c1c0318107044444056507103683d1022041c4030001c40341951040e00d400a0142c81c1e6007011240998103070400d120a0f844c01c0144030504d42c201900510900f50788085881c00794175549024001c2840c1e45070340009050342c010501401006030043c2c0b580c07000c0e1000700c9050210481040340122001c0e84110300c1d2070003400210750320884984149014040c02d0004029a100b1000401c0d146c2c4a803c01031064483d01e4046602014402d00201c803140d40310703410400010f6010075002e0014540448401120342c6000c100702c0f54100007080b102e20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 522635764 1250 522634514 522634517
    0x50706080a0b1e03120a020f07170304060c03140307120c031506052809080d0509030307030e03101406010215060f150f0d060303120203040b0103081e07060e150106 72
    0x11a50703501e48400c04031200f0740000c1c6030302d80541e046240f90b215812000c0d220000c078690003040780d0291108200e04122050f00301c061810841c0200c091000d07400012181200c10a00c1c000181480509048920703900c0b11203240342c43d60000040c032607015402107204e40100e4080004003c000d501c0e036821303400c40f202c514500c28134400700708081001c0e60045010307048501d13100745145d1854004031141786105a642082c00e000c542d101c1c00500915100700540c0f8000c842c1810541c4c90500304e000040c0c2e03a40920000202000180400f40000343c400748a030f400784040982050000445c62071403c00940307400c8902d10300603c100700c200c252031b4144e8042c0311b0159101030101c1526061031014810188241440301ca080c100130040c2010303409101c00204111140c080000a801d405d6240c000c0906104c040c060b401c4500601c14840030540039580035045a512a080c2070b40d51103d5100314003d01e008060108401c1004155201031043c00d801030910441b0850a42d600d540308403044a55611080c000c500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 522637014 1250 522635764 522635779
    0x2031017120a0c0503030901051f030302031602040e010f2f030f040c0f1d0703020f090111010e0106030602040306051e07050d06051f0906030203070c02040906020412050706080a0b 79
    0x40048841e50020486880c0620305442ca00702961100c914550003501c1d4050391f6907407041000032040b44030802000003110610701c40049460341d103000750750f4020944100e50780080b1204090865540340c0c002020541204024007030030000c4010078000340507070301c07102070480000316800c50041400520915484020240b1a040d0703101d00004240b854002002103514a850708008184507003074803081001000741c01c506250381c01031000c03121a403800203040c1d041414018803062030b4102c84401603604446007841c200c2c02d45800070840d45d015000300d1008220f69407820a0200500107203030001c1003500c0c0035420522154603100e440c0e5000861080c049200c1009040104440b584900b004101d00d050070b03100416255129400a08200500125070004034240c03000b00c03901c5034000300c03800300905842c02c1c21811890300802c0034000d41c9031204001d01c541c0c0d5464954003002403990566002d030408801501c0d28101310f207069969100f00c0d0250b034010600f02c4001620044d42c9002c0c801d8241409800e08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 522638264 1250 522637014 522637033
    0x6040f1b08062701031a040f0803130b0901060923010315090210030b0f12210c07060e09011e0302090405030c010906150b0c150603100f02031017 64
    0x112100c0201802d400c1c2c0c003c5091100c1c4020401c0304045020b080d0104032000740651551402e00191a0101031406030441e00358100705c0400c8080180350fa04d29040380070281d483d6142d1441301d16015007804001e046034888001d000c120481540508143d4031214001c221a03060947d440422004d600305803505603294800500004080d04000701d80c1c2d400890300450701c1801d690008000c074610101c40c0b1300007565028002450f1500c1080c88005090a9070204403c5081500300390712842319260200002c410b5145510340400c030442291074802c1000150365441e62200001130090081241c2d45d84245072101c004a10003100c0134080342001620440d1203030491455080c07100d42c0a0080096540380414040031549800a00a5458980c42540e0020b5240e0560020030815009600800d203442402e101d80505900c00217030072803400355030480e010420707561a0006440e10450051204146003800d402e0520310350150051401280000a00d1019544072030750f08a216034002e0300ca4045e60305c000c1d0403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 522639514 1250 522638264 522638267
    0x906130618171902010c080708120604090203060f091905030a0801060809060a1503081303050106080c0607080726030906130f021014120402030d0c0c061409100806040f1b 75
    0x180320f00c0361040c1044c80c00b90f4403640b6407100c81d0b0002141a03410010000e100d214491025520a502100c00ca07410043c124040c1c012a5031f5003c001d10380c802220040c008118282000c0000340f840d0204000001d0040b240703850070276140d400200f1104049512032001080080c0603030001481840d40d040240010394618080030050400b8158011031003040c2c407400700125805c4070084c22001c00004035543c03c00d186140076401c4a40c15803101c0d0b0103401500d00f9a081d0768600d001c5800c4150045000b944070a0503082c0306108410841220507200003001d0702ca9001e10a00028500c103917007001c26141680d0320040a54903003180f24400629a034000e41347e5900629208403035407c000b08920700607240412040c42802140c2c420b042e4a2541c1a00008020440c034041140c02961300e01458050800503156480f4070f040c5849005500500141605d1074096600040c181c3d800c030f03e03004001e080940001c1a019121001c1900c4540c000e40c03c2c4a0800c6413003026005100d84160300550950f00040210350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 522640764 1250 522639514 522639553
    0x403020d110a0b0c16060203090a1806050a030b090d03050421180807170a031418040908090907020a02060f09030304030203120405090703150308090613061817 70
    0x324240e00001c450400320f81d80d40000003405184e0090001000c106000a000030300c0c3d54615400001150f00030010f85c1c0701030312000718803011541c40c8480b07603e0f16403210034080701505598104582084280400009002008030708a004418800c161020702040113411000d64000700c8008c0c0402400070344440800102c205a51521811840c02c0b41101c01d030350040442c42d00b055031000d0b00702d5200700d906100120324000c044980c442c03030b00014104074142c0e03a0054001540d840048941400c0820003541c2c0404d5044c0b030301c8100034004c004118128062400c040799403c2052030714010842c1800040b411030000038901007054008001d42c3c00c0c4602c030321486825610668034150140414440040103032410002c001a80580120320782c0c540f802c040521568403801080407040600740102954200141c15550b0180ea8110b0040f036540d451000c00f00350700384150342c0300560481c805480007458560201c1d41c00b00c01e41c241508080b603176a9035a0722003400100121a0031440e0015911b105002c3c08071070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 522642014 1250 522640764 522640793
    0x80705030d09080301050414060d08070c0305030a090e01050418020f190b0d150f0515090d0b060901060518280f08100623011404030609170403020d 65
    0x4507440c011010704a14241c0c1c95050741141c401c100480103010714038241c01440818440d01c5691354080c0307071120000e00340c2c150780c0c14040e0001000150032800d1000c14070300359003d16000030440365100c0e80510010104c2505106030b040a08200c1d00100d101d141070301485000e01e4501440c60651881a000c1285801d42c00700000c0d80070215004100d04080c640c00d1780c00040001d80442500d40300000e00000554400104080b550000c0349000d102c60742684414000752001a038030061009000d848201142c4140c698140d80044441d8808003044000d0258610070b45042e50b003108142da9030703441a81d00340a86000c02c1c149850b02c1e010880f543c00c10481980a0700c41c010b4080042a60202106194006039042401045000c203004d21070441c0402c4428002990b21104201c11407600c0e230040031089545580196544180c0e441c641503a03c035100c00d400c003411800d059680d8a03a42d1034550010704600d40c0403243c12429111010306c040d4404103640480e44c010f07000040c094500d0352825050407816 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 522643264 1250 522642014 522642023
    0x81c02041502060f0105010212070303090305120c1b1902040207060207060504050d0233090a020a1d18072d0906060e03010e1905100906022107020a0807 67
    0x20310000aa52541908820140145401821190030441c1c858845000140c01c040d066501c030309603054080504100300d40318680c15250020b03a1000c5842c01316021301c40c00c0c80d00d081201e0b2403000c0c003601105000013450b00c1c00c0d14843c2400011814544240ca50031070716101f4a0781c0391001172100160034141c008244c10381c407421006107415016a1a141240c0c0240c0701503c3c140c0c8586980c000007074041110707409049405541d04d940d001030800c1c000c41d415100d4408484095820041025004104880070300e40764005c152080c029220907424155070390811100c41c02200d0500441c2c4105003502c4c8a144d40e24240000d0b00c06541072800910408090703509800314144803070804905101c00300e1800c405003a00140c040358852400c80000c242c0907090a1052090b4035101e03030000d01180000e404a030015001120405c841300c2341c1449420444000d0104803542d0030080e9440070052154020511440310051901680581303285400581070102d41d5400982e00c10044000420b04000c0079016140c401d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 522644514 1250 522643264 522643267
    0x1b092d2f0705060a05040c0f120201050d180b070906110c0603130b04050a0309050f0108042a0305010c020f03130b030406060909110108070e09060904020111150103020103060e04081c02 81
    0x242c0c1c0d4041c41c21400312035050340303540d54a090004124410080c40001c0c450110040030781414030002403801409284000d041c0311000a54807800007013a0000503500c86018680b03001c0300010b0919180c0c092046a010300012944039010607214024041e140c0d007000c103d001400c5000101c414040c2e190310181058500303036408901c1c48001244104400d124a02c500c01518128005181c080c2440480d50021445501030b807406ca41a03036405048158841d41040d00c491600900300719044402840b10340503803c000c011540441400360540213019542802e40c00c07545106211a031580d16402000840035038000c00761020001c0d01d0f07149015503001402103030001900d070341d21000c00040b1040e070721080b108444045800c540542c1c204a490b035000c1c500d41009c003101164000000c01c55040108928480d800c400045015640705003800c145201e032040031142039400c1d54008809442e424030049000909141002c2081a00501044d016a81c017514107814003101006180c909000f180c0c00c940d15990 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 522645764 1250 522644514 522644527
    0x7060e0d061d07030c23040506040219090f080304030305120c21070906031802011d0405130b0a110d0504051c0906030b0d020901031b092d2f 62
    0x40c1e42d01c54a52441c41c10000b40042481c521386407401303040d19400400303440e06841038152280300c04882e4a640750001c540015055a500002500070b00564106407054410251485e079485c5c1c100c00c4600a450786001c100100c682e07190300b0f45a0382d21484c0401400034205100c441ca2544c0c80301e0200341c0154a600100d03080c03034041d12003880c2d9038942d041c00072b2000003e001809400750b08480760320007815484c03030180301c140308401e81c0504030111940001d0401c01c40090100204044010080500704020024465410102d904010800c28010b087d140b02c00d1100225829603403620504203d41c10b140c1880313090070b080040b000002c18009005807410f0280104000c0010b85100d101c1c0c4494485899403502c0702c0c24030000070220b5001050f0340d40110260a50440541c0c2c0350b0414904407603010000c1c201a0554044c404452455980664200d0341048458140c0d8544e1400031030300c41041c1c04c0f00c140100d01100f80301c41611400043d1401d01c40d80301801c800318414604a540102681d007000502c0c209 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 522647014 1250 522645764 522645791
    0x6081906110d02040e070804031e2303010602060c030403020606090723041403010605030709020a0c14011a1009030311120d05011a070803011e080d030510050307060e0d06 75
    0x18422031600b401c060340040e05101c007900740040701d50030440f18541000203281580d0042c05820640107030500402d0902c0044511610410816180c500310120101002c0c2c50095074140c41d0b04207008900c094012400010180c003450703015030b403050780c05a0041519450300700501803060406040c0f41c04001c0d01c48a050552440c0e170124051131541485074035541d91078450035100240e884500148642d04010007000076540020350101590740024006940ba0000217096404110502c1c1c0244400f680e51465581c400e01940564040116120003101c6c2400210070042c2c010701d44641c003400300b08410400d001007407007a0142e00140445100b110080340d0355941d806000d8202900c120324168440e0018040381641c0e00c10120901d201c41d50711030500b5110741e60170020b4001402000900488401e084c0602c03404841c00d08001c05182d41654040e44100b00010040c2008807105255040302940000e80b50030001442c204903440c2e0f503150035500e42d040f4204001a10740140c2a502c01d03446428181a41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 522648264 1250 522647014 522647017
    0x1a0c1908092224080c030601171f050406050708130b0612010212060312040e010b090a030c06050d060e010f05090c192003030c09061b160e0108010608190611 69
    0x50303200c02241c1071003500640311088482030300280072176008589410100e031000588981550900402a8503c1039031005244c07811701c06465582c0c416104a00d581b00d116080ea01260185000e160284103540c1c801d401644d0941d003c2e128103060070811100a4007003503201ca9280c1d003051005142c10b41d0b511b583c2790040c2c2607800c42c00790205a42006010f01c01145010409801c0d41c1e490100d00314207052506086000030401441000b50310040003e124219030394000c0301c0c4000e9540021010300c84c5032a090018000d421481c1d6003841286000d0020600100f1140410b040344d210303680b085001800c0c142801041a4058210011442d040c0400c150152081c140024104907641e10040b540358818940c180401c0d540c40d507a0700e00d8000b0000e201601c9402d004031020704c541510403980c3c0d48a1100040c5050b99951000360150250741400b07941c0030b00c3c03002e50200b1240b01412064490b625040c0413030072540644038401d1640d01540d0800809640f4110007601280900000541c8910710072940019 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 522649514 1250 522648264 522648281
    0x3030b15040b040906081605090414120a0806121f021614061f0b0a020307051002040501090e0f0117210306011d100302131a0c19080922 60
    0x302e0401240500200455224450007010100b00411140e440c1c14020481020a805500d0017540c100001400b8082c143c0a1510340c500010b00300c650350705920074104019002104441c00180c00040842c140d486d10308603000b5102504030160000703101c0e0306808a0443c004a40c030100c115000d022001c0d6010307000035840c107402e004400c2c6243d9446544107250500600410040158401c00340c1d407440c40c1c18481c813007019140c01c40710f400d6881c1640b5106910f5400340f0741000b84244907540099850650b036401400840b41c0a0701c0b290340140d01c40888890001080300c20188081d007410040203c041b2881a48943d803d68505491000007000d02c41e50949010500350406d100001090121b156404100300b48601c0361031460b0031080340c854000450340c40e001c0501344209900480d401c07009601303925140004080f0014070903140c0c4071401d000300e019005090001c8050240d10f002c0d6104c00075a5402001c0294030012017890850804104031001c8000310703c4d0589240701d1180c01d00105004d1044100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 522650764 1250 522649514 522649529
    0x20c0708070b0c03070f03050702120106050a0f06051909030b1e0a0b1003050405010b04090c1a04050a060c1a01030305090a0503031c18020d030906030506011b03030b1504 75
    0x18290304040c4090300d409065800b0582056042003850014940842580d0740745520940e008070101c66420215414091480044c0d4490238200841500c60b0056011004442065030034202a139900c9500440321042407103100c0208000b042041803c00d046e0a043e40c5100542c2071400d03d043c0c81e601d0724100711904803140c80e0200f620900f041d05805041600d60b5000c9500b110600c07080611001184001c008505128245030719031b40402c0420400b074101d03010b4a000500200000a55420300740380c2300d2120711403040c500c00d007038030b105070400900001c5606842c1c020b0402001c5501d0040202c80d2521480402d0b20301401d4030328441c036449060010540214001c2c0d84040d04c034070510042151554003075010034400e40c01000400080901039090030140c2c03051100005400280524505200089080080d40402c01d406400101074010421034107590150b641081103559000054480b1548581d500080c4041907100d5070000b4800d81144c0716554000e8070f200c1d1480303c05060705181c2d401c43e822022 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 522652014 1250 522650764 522650773
    0x41b030308091603030906050d060e09011d010b15071403030a1b0309110409061509150905060d0b07110627070b040905100b030c1908061f020a06020c 66
    0x60764080800c0710003403910361105443c511034030710b96026007080c040380705440600401084038900d140342030340044000c01c1e640e00213000504d40981c4090007011a110008008900018400d0140704144111122110043c1400c1b141080020817a1419000f0040440d1001d510a42520210400340080e5001301999040403814010525075a0310051041500d40101031500341c0320030106500701284000550180c030001003140147c2802c401901c09140351406d68102c4480004014500c0d600507002e2610380d2100405013503e80b80f602d030a940d0b055903501c2d44007030098020030110314440103c507001407440c10002d0404d186010514100b48007110540b40440a1201c441031320900e4480d11141e180386880900307216410181c6009140c001c42c040c8c0c58030300380d491000030040018041034a024000b1712051071b442c2e150200300b40980c0d5201c0496421a000301c0200c42c2c207100d014404841c001c1e000100038800441400390b0705205100204419402c5214000030140401c505200030494a01d4900140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 522653264 1250 522652014 522652021
    0x11031608011b0206090c043305010809120d051806090a0c0b1c02070302030903030304141b060703030b0a0f0f091d07060809160b0c060603030f0909041b030308 70
    0xc4031000210300c941c0c2c0075500310340c0c2042500c80020642c09000302046070001007000064600b84028902d4603d600302d0a1442c001020703030398401c60202c47c1252001d90301e40380c403581c0d480519522000d00b0801850307138810501021519040980003141c0c1b110b2103e81d40708210f842e4151182c900f580a03616100c09401c0454001c00313000303524225034003500f1603c0c059460701007902240481c2d60541340c880984c941d80411208100b41c420b0040b01c9843c0d90060071a80c90382000d09041810540071450402c8510030900600c0b6110001642c80e040007200911460401000352019400b81180c81d1640341c3c00203030680d001c545040700c9104407002c1c01401e4042081c0e141041d492404031220200c24000c04590702c94002c028003400210384060381d00380e01d003060581d2206e1004c11f180c403c0e1160501c11000360000701054090880f009400149944011030308691150b005050300c0e03100e40fa156940480040002480714289032180f02d4000f80f043d6111429284149407014880c00150012000942d910f400d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 522654514 1250 522653264 522653291
    0x120711041112042001020706080a09060e060108100902060a18030533010f0b070c0801020a0c12030b0108150d060f060f1d180a0f081c0209030a1103160801 68
    0x14504d0b06075000182c21650400c4c100081d6441c4a03920481c01080700711400a85000724580040d02c03480d5010100788003140640132001d0322005e00f401034484501c90100c80524004140c000c00d0f5250b03402800d0b581c0742030f0703000400300d0301c3c10000450000180b40c500d0780000040e030100705052002ea14007094060110380c103a460403903c041807240210700310a01005110f22040200c11608461556088954410481c40d01e101181400d510a81c03003075101242000c86160031a000040d007034860f801c3c00a2944502030160204c40389000c020b40001c070317044000341c2c0c80e41c1d0211680340310b10b80050200705000c240380d54040c04c0c0d4000d942ca82c420251542d004101841d030014098000e050724082400c00360360315030166a5240001051104521091200654200c20520207809625009005003c3c911214240340381c8a80c000042c400e8100540181c9002c000707460b01c05d5400c81c000040107040140c24988545415200b02c003003445c1d0500803508540350743c2e1030b5444420000c1007650008070b40c00103c1c204 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 522655764 1250 522654514 522654533
    0x5040812010609060e0a08030a05160c0f050a0b1305040b011202070f120212070201030c0314040302070311010302130905060102030f0c070509012c04030e060a020615010212071104111204 82
    0x450003046c06503401c0c09800408405c0e5030a40f10341d85001922003c9010302c4284801c8401c1c0d000d46001030b4120046171240d41820b000302520419908030000c0707507580740400b2082c8a00b151107200741c945110103111902d4150401d0b5000203052400c010060400e0244000301d0340305c40d40854404800c8140c44c0c082059202100c0204282d5001600300b00714000b80c034012a1143c02c20003810503a641f15400c0e4081d01940c80f951048050310844016440c003403401943e6540c0c0743c001515010260f0712000119031180c021030307160342800710549802a1529801c0400f0380f4000e0a0300303043d80400c2c002031a2020019014011440148005020301458039003400b05910713068100d00d4070340544403401c07410005860340c845c0240c00000c1810180d030f503407400c084403010360551620354441c200140500e25564006400c81c06000501e1044d0030f00b000481c01640d460400e8101275015180c244260004a040d807055248040d002401c00300c0c40c00c11724001e9840380c0d4000c44d10481808000824801030140c07924 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 522657014 1250 522655764 522655787
    0x131d07080c06070f020328020f03060709061404090213060912241b0306051206010503120c0c041409300c010f0603050606010f02031306030504081201060906 69
    0x1000351640c00c1d040c001042070341c41603801c084d261120030310010045480030400c80d521010784da031501c0f03800c5c003000021080c0c880c1414016481a15100c0720702c40d183c0341c0840c402d030062030140c49258006140030b40690b108801c0b20760801c450710b028040020b803903500b070000b880300c0118031443c3c005242c01d010001d400c181c5070340c000c0080c803107480303009000003010148a4051140400181100e05569032400d030007a0000d071158003a69426500b25552461300b41d04038009460007103880d01400c108a03003116640341424030520303505a01c08044501000426802094808105000d5038100c0003000c001c9002d40d50b00c001e0f14a01c0c841600d04020b0703900c00a1108600d00d08000040826128100f020080702c070310820f1032094110302c0050080080364003540002c0e10240c5420342884400d5590030f0a03626940d040300c20f94082242e03100711064852000c0120742c00307064100c5075043c041d42450b100314000c000c0108100d6207a0f40400003401c5080503d070040d402084580d0341c400a19040c40c000405c103a000c2c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 522658264 1250 522657014 522657029
    0x90f0607080906241003020309070617072f0607092909031011070b130f171209060a1b0e090402010c02060706020405031e06070e131d07 60
    0x3030500c501c40002040140e00320030903440c2c05010040c02507a0a0b41c4140104d0f540364090520011290b00c1a003640203103100c1d03603925081c0d0304503650352442920300d58600703990185c0f000080400603242a0184004080c0d144c8025118007180440c03240404442601d0800c0c06c506030710600402001540c8104180c01030704a6211404031211070481c180540301003048191007000b0080707811881ca0300c0811500c1e59502d4480000d20080e031041e503407118690300612060b10101500c0300007034890b422081c9045071442d80800b004403c15142d8840d807141c400c81d0325a00c51954070400028402807021503c0c00d001c1e411800261080f8100003a407442141c044a4400750308038241690849604e401c8400805a1001624404859550b40c801218081801100298080740206e421014000325070301a00581c1c40540c00c031b4034003550002c85d10300d0004203c0c08025581d40b0007000039030340a200c0c1c5c1000624640181c000c0d072040c4040c4088a081d40d50620001da00c0d140003a08096031040c00f08401001071816 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 522659514 1250 522658264 522658277
    0x30412061b0e09220f12020604032102040e070215060a1217040f0b0712030506130c0e0a09090b010e0c0a0c030c02060a1205090d02280209090f0607 65
    0x44001e4520b440d1a0300c440e02c075003001e0740029014114400300311a100c013503040d0f04420002c07525201c030281a03101d0060390001524042070805500000d519401540c040c0c86036076095068005c070703c0b081c0c0c3d04441c9100345180c0134000000d5107a00a8001030007410310340c01402c0c01e2000801100c0c1642002000301d403182c04100010084112110b0101c0c624540040740325890301c00c5c03036071455007521481d0b120b0040c1c1d401c10390001a2803202c2c8405441d40380d101d0a9020f02c41240202c2c1102510815212280d124906071803031502d4050300e41c00600990702d181010181d0020090000d030070901c1a0780301c1c4080c113491b10700c11000c0102804a03540900b405514079996828130450400c01d40c0940e805070f43c00e01a1110004080c1402280901c0e405075009144c5550b46480400c010f003035000304070064a8590801c0301152914101080d9450034240d00c1e40141120010308852168000307080300403158000400c0b00d1003016840d07040341148504c0c03c680c000c1404048428556103031160013402d60040022 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 522660764 1250 522659514 522659561
    0x30a060501030b06030a0809040b0411040605070b0702010e10051e010329040b06040b060c07140406150f030507110703050a031407030c020f18070918060b0405041104050303041206 79
    0x84103041d2170413202c00f40c50002d01c2c2c52b2110b011400400c20003c0c17400a00348c0104001610680c028010140c1d40e104845241c4140c454101c168282c43e00541120016000a60200c2d01c10310264403542e4410514160f00c4180124200100ca15020a030000d0302c44001c06447d9014541c54100703e011042010003221301d05103481c0c0c550206040c4064160b0340b085407240d028140650322141540e20300004001551005648e51004000035210b00c0305550051b41000c20020720f00d80b0101e00810310020f42c0d216101806040e0b00c0440041400070b00d490b05004010301141d4455508109000c051417046009107000070940c14090028003c0b0790f103981000310304006c0500040da0002c11f61900c1039050304c00a11815461001400440c0040c0d030800c0210f51000c2045030460780b21b0780917004c44082000341d00c040e440380d140c03d4007961018016115104400c0104014604240d802803c45806030080300b400c01d80c99a00107403e580c8150300204c1c40d0704800d02c06c00c1c01d0000030b102e41421040303510355407112100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 522661870 1106 522660764 522660773
    0x5130b060d0c030605060306030303040b101208040504110906120903070b0915070203040b0f07080405040618051501120b2412090c03072102030a060501030b06030a 72
    0x307041c484c0000303142c140a02101e010b2007018010314615900d60303c400300900005448403203c0d421049000603400d01d041e8150685510810301c45694a1400d000c1000b40c4000c80520300c1440c8040110b42c0860b6640011504150040d2298455564036144a1410360051540c0506650082e204002440c80302040400040b030401402c8583d0341c54400c3c080b80e0360700850107883c03445101080180d50b000115005000e8a9210300180e51800d921000030609459299011410031380d9a0140c00040c58098050b513540b00f08003040081c1d90600e4500000c0041e2000640b594202e907a074006000e4039201e0b4041c80bc201c901c1004840d00001c0800c201221917072046804400701c01074440401c0c05000c000ca5040080c1a00038014a142404c1c0303a5481601da40c120702401c480140000e0540060f1001d1040341c65a0780940800110b0b9851800c00e61007544004119611070f400041990307000a = true := by decide +kernel

theorem cover : BRFrame.Cov 522482014 522661870 := by
  have h0 := BRFrame.cov_init 522482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 522482014 ≤ n) (h2 : n < 522661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
