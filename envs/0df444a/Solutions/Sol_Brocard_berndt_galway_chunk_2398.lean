-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2398
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:35:53.364216+00:00
-- url     : https://prove2.me/submissions/096e3e66-7ff3-4970-b7ad-fcd1a41b4830

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 431115107 ≤ n < 431294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 431116357 1250 431115107 431115127
    0x2121204020f030d17040201031103090105060a051e01050705070305060903071a061e0f06032e080613170409020d0506030c01050d09030909050f01080f1f0504050c1203 74
    0x38030300c4850190f00400f400e840d0140003610015102280451034200100000e01f107912a40001e140c3c8000350740046d4881c03c3c00c1c0b00f807038068841260b05a010b1400c01c2e100042c14901241210b95070031090800d80d66030b03c103520045800f40d0007400180c1e0035118189000000820810410703103d502d05801440d1100c0c103d280c08114059240360307581c01d038160142488255a595a20065250144840e03000c80d01c01d040003042c1405a0342251640c8148003008000c0f00344420803640b4624001314040100030b4105204103d03030514140625007240c0d01440000303821f02800c00d82d00c100d041c010b13401545003000c049040c4803a42d110381c104c40641034010840c2141c8201c01d0248507049802140505020440368000038164024840070020007034480320510300f418000e040360000352034004400d20491400194021354464280306103055481042c0480110b440c0c0403070300b03100703288034030141500072019002100080e000180c0159a6405421034280d2140d031810b964080021064020719111000a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 431117607 1250 431116357 431116369
    0x301080609150610111203161e030e03070b0114010f03090b07030203180a060e06090d08151206070e04060b161b080d08061003060b0304030f0212120402 67
    0x140c60021182c2c0003014524101006084860b4020000d41c3e00b400b080c03603980340464501c00010610500d134000c150740b081410580a004511034450300000c40d00484600504590000040502c400340442034000054020311a4004c212181d541c03c00716800d022081d1030707100d0780010a82c8a001c100824408072991540c003c0005000da581906040100142c1c98513025031450b40141000c040680c0000001c480c0700c6080c5d004242040c07024100c64640701d50f4540080102400b800c2a00c4910a84c0002800320800241840c004000c666802960741c407040250300c02c0e00080109194890511102180c0b038100800a251003040781c2c0ea261540c0700802d5081c442212140d40041c503003003030708020300d0754003240400300209020b40c840b25110448145111042655481350059602c0d80a03811400b40242d500002541c003c10045958500452024074150215081842101e00b401030501c0058082401401010705101d000d00650345c06211410000030582e002c1c402c03442c1518503440501042d41422 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 431118857 1250 431117607 431117611
    0x819020c0f040207110f03071203050c010f020405030a200d032102030705071b0b0406050c06060f1003150911070c1d042406090608160605190309020a080303010806 72
    0x9030b604618100761900c4010303803070038140c0c0414041d0b40000302c030940b1030300e0400400c2c00030041d640d0300c15040e050701d24005000c1d601c00c50151f1b502d98282418001c8102c000d10854084460042c001c01c000f44c00d541e1a41009034030280b01c0320410000340c100403c103442d806490206544a40d50f003102d800754035100d81e90004503c4800e01c00c154418000c000001f50010221903150350040d818641c044000c5040010000b82608040303403c04c00440d0006030650404060082800c101c000c0e5000d41e03440c4014041d51580741c80c200c0e94440c40103065080180d000e83d2141816051822030210401c1d21503541109039082e40d80c1e200303500b140000d515024010b00c040c0c104040c1c0303829800040440300d10008444c0183e801741c03000e00001c7d040d4640084103185038002d40b425078100c00b07051014a075550328003c000e145501ca120024012410b180c049000300001c200244c49003600e480f070070710500c010051301541c569000d001c1031566480351000540c2c0d41d05510320080c4407800c000d550340c0d81040301c500c0c204400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 431120107 1250 431118857 431118859
    0xd0f0602182403060105071104020c0604020307090c14030705091f02010b061218100504030f0f0509090a05060109050a03110a06050f030604090f0210020109170c030301050d0819020c0f 81
    0x402c9148100700d44201d0b04aa4000340709203499a00e4118508109000c6003110b0025544980f0000e011000120f021603101e01c114000c40c141c0b026640e44d45290411340d00c038082140009000601c0030108040e10703074050b42c2c0002c104c7c606603003071005140204011490301c20080d0009982c1140c03035a03007030350309000300074040109035000c40c2000c0111242c80030022011b021560207480d4450b2451421504200d1003d0100001c1030602280c00c007414003074030300b00300c02d441d403000120f11104c61000c1500520440d5401a009000b8484070317a28040d1110013010003400761030400884540010f002d03980c0c5501e0740061805032032a48403001c000802c02016109035488041806018000c14848508030401d480e40141d00741c4002c5081c00d054a030140407000340b03080c001d5003c03204119983c5040d0b415803003074501e0342c0b00e0445080385c00d08101107240075004407050b01d01d16500030030040c08a030806d00e01c0710860318440e107512030070f00380d10f01d800c560090038280c096001a80030748480e100b01d2522071020039003400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 431121357 1250 431120107 431120149
    0x315040501060f06080408070201030b1908060a1107062d0e01050708010605250206120403080901020c0a140313150822060c090f06030204030b0f150d0f060218 70
    0x407030807101825139000180b0180c1f03e0000495100c0541e4041d41001c181510028546140390b000040b01a503800c0d4036024002c414465136000521201542c81103803100c0c4d4848403040d01b00140d555419003d01039294104c5c07850131401501114030b020881c095000d9802c01600401c0b61184150400d007180d0004029000700141c0000402a50341c00c02c040364080304511495103081061009000070301101d886009401c95000600d12060011034441a07000b0fa100769200161034584a9070315080c2c2c0102c0e402060503811540c00c00000a69020304d561200700c152080d070341811100039502c1982c0400d94400e42030f425507060b031484d2440e40001c1c0c4541c050360010805000f08002d03030305a20003144103400203100a0f80c80700c00c1400a40106101401440742000c4a0300d240d48413040140a90410302c401c565030518000451010744a880820303106400340250755184c407240504024802c45000070a40d5a40000000d03400880d0b41800140306c5074661401c0c039100858500140105803c01c150050002d007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 431122607 1250 431121357 431121359
    0x170f010b09130b0a020405150408210d0c020a0203030307020a0c290a031803031a1e06030606070803040606050901080307120311160c03062301060f0e0315040501060f 73
    0x411010070004080e600f019501c0207036030300d012580001384034503040f050780f00c817040848003c0047c01400038000c0d82d004a05030f44002d00d15010b8549025410a07040e24904010701c001045400251300500480aa0f031044a0043e1055008030341140d100391380200068002c11500020701151f00c020000600081d030080800000e2407407100355841d001482040c00c5400059000785c1544241c00c81030580c0100700050070610420318029008211442010403e200400701c08081ea182404400041c42d506e010086510f50019080007401c0c1e20051400360f20840030b01c4610b02140e013000c080c510842c454880003c560b401c4c0b6080082c3c000f0140d1180e0703515841088041c0000340d090031944510415401d0220321802544402041400b03502c80041a460002414809006881c1d040400700c900841c420008001a9420325a10001c030010001810005000410440c0d128011000d196025440c0c000406c5410314006424016940100d200d152508028001480780a01c600d400500948054800381 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 431123857 1250 431122607 431122621
    0xa06030507050603160807030b210d030e03040506030703060e162c0904170d0506040606030605010219030c0b04050d0810060c031b050114041218030f020406170f010b09 74
    0x405d0b13000c6014810001d1070780204040c14069000702900c1c4e840246241c142c01048003400070707815501200c10403d0300c66404861a10b500a00c5000028140200510304e05810081803003000d500180c2400d04040d910b100019080c010001d24600401c4003507600000a0766105000b003071514038a40c0d055450b8240d000c05d4030307450450303580410150015114121103a9503803c16510a41c42c000b0f41004040d0f00141030003171588283e008501c2440100d800304941e42e01d46c00110200c4900d80a42030150303004003a050030101800c8000c0312420f00c2841d169528142d19542c51503c010155412203003648900c0d6048440c0d6006060258003011841da0810b01b20324100e801445c910000d81c02400f4083c4010105088a984620310303140150014001c0c0a16010521801c4c0b0401d400c035010f84107840405101c0020703510803034004101041d04080710548a00315240d00e031094902407401c03640a9603810340000d0901c200c1100703214140c0030802420200c900750307080c1030035502c128042e548540c034920104421 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 431125107 1250 431123857 431123881
    0x6030c1b140304231c0b060d020303031e010e0606040e150d030e011b0804090207110a06020607181802030910050c040f09061a0307090909121e020c010e01030906050a06030507050603 80
    0x5d030541007009824070742c4461020925480d0140d001a4050100004001c00d072542c44500000c1700040540409490ba0f0b210508101d80c0000d58220746d014000b000208802c401410310300350000c144e680400c41c4043c040300040d00d80d195000c0100c1c0402c4d554240000d60b50b070030000d100c1880c6880084a01d1301483c0da40c40c0482071043c0e00174007201d03603404100740c0c1c20b02224411010741e010000e031a12814076191900650348200c100d41441c0000c80004000704c1c0032214040600442c0c00c80407080301c1c403e40d091348960107500700400101c0103100b000c22100d80e0600600955028844a440c502d58542c1040c810120901d040d40007108602d0600c101045032095686800024511950700e050f10b030344500c5011a9500721719482080010305200307010302403002409d030382220f00c44a130715401c05050318140d8625003060050b1446001da000300300210107a5000701101c01821105240004100d0707140d65940d0200c82007030707520341840d80d6600d00600400408005a82c0648021070300b150035071a09001c8054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 431126357 1250 431125107 431125159
    0xf030905011b060e070b030906010305010e030a121a060d0c0f020a02030307020d170403050102040e0703060e04030e2706040605180a020c010b0409030507050706030c1b14030423 78
    0x4a030740e6488030200004070b03003802030201501b0004141a80c1c2c0c101003445607030300d42d070a000958241d40703401485504a0000022940e428006e52243c074000090b084207440149451a2600c2602818000000c00780c0d54890003000d440050038000034a681120340000d20100c15056640e0944d401110800056a4000265403c9581c1181c4581e88405c4500d44a5020314030b18588120814001c0b901004122040d00540103490030a1080c4807941c0e21884100c094800521508200f05140400b08000c248180c440071581c82c400361900305801c03030501c0f02641a16034040101842d06aa60910802e49018081c0b040100800c981000c40060616103058a000c006051540c1da00e0340000e01119009007900150a120002003003040088901d04028101e40c1c0621811130380e50245c60390204449000c4d108401140003c0d0350f52401c2014009000c1c8200005694142c440742e2500c4c0c80000b00e900c0801c02400500f808080100a2410542d6142e6030951811440740c480d4003a80061444403036804140d403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 431127607 1250 431126357 431126363
    0x2120706021e0406080a110301051309030c0c080f120309030f0a02120304080322030503060f0112060303020a200310110c12030612070e070305041407030f030905011b 73
    0x599510200008040804010750b000c6000800480c1c00104c0e1508407500303520070192002c09101602d44040c000c41c05110900400340e1150880841b6080c1e4030191780185440341c03090626039500056612010690500c1c0d51100556038032451540300d07155000d0005014083c0480a0300d421800d0a1807056241c0c010f00302000b41003007020802030310b401c1c8200100e01010300d001303500343c4e034900301810030084560003120024928072480800c043c0c102c110040300310085815581d1a03041d5202c078810409807950050303250f41000704480403919144041d10a0384000c601c01d400401092090780740003038201d2008a070f2a00050401f002c0c406c25510b01060051000900c00340014031340340710f00108a4180209000e05416100388681c3c00024950480254002d442c11581e1007592000c9072901995003800b40601c424428546012494540c0a038100c2500039210302220445100e0701d40300310349044415031040c1e54000101546005060b00074094002404013803078024910f03040d0704075044900080003002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 431128857 1250 431127607 431127611
    0xb0607110303120c030f010819030311070c1d06031b090604060b18040f06140f030309090703020d0c03110313050106090216020906010903031e030612061a0102120706 73
    0x300c00955402c1c4202c0c1c06030701411400708518180b032001d07040e40b504226000c4040001990010841c2c1e03138001002521250400d4107602244082d940440192011115103984120140151400610722210902c0a05a040c4a40081403020300301d1428034840503100300e019800850343c149088840e041c030085811410b49120826489440c045030060031250b100c1a06180040307240b803003000c0d1040b14041a4002120180040d0030000014003c541e1780d0310816107840c100f020182140d00b82251003c0c4188001019641402070380004100105421210300340069030020300c580300807403130344504045002c0525040026038070b90007a41c1c45a00c00503009415001c2e02a10b9034040160035004400948455441035454a1503c440600b02e2000a80224070404e681c600043c15540304030032000032650944e9544a0402c800545450003012202c180e00c10180c6809005c20b8503080100c02640c15446610002500809100b0701069503051400850441d00101841985248803e040c0d1740302a400c0200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 431130107 1250 431128857 431128883
    0xa140918040510090818030c130902010807030e0c130204152a020d03081003200103050a021315121811010905011413031a070206070e0a0603020f07230106090b0607 72
    0x1a12307081582500951042052024082d00040e075000103940701d1003070b210064144c40340b02082d425a4040f41c6080d00d141d1003091558140c0c0f41c958002d01c0d4080180e00010b1400c3d0700d4151043c89103042200e05c3c00400c0d02121031001c802400500000740b10340f510045603041040d58000390702e0a407103c102400300000800492034413084503003040000e60b48806250b41c03888030f06c1c1000c41c56910391607a150100e803601000a41c0c81a10703008031114000c0307011401c060142815002d41d400c042c00c0307280c4800c01601005216440c0303018403900104040d85002d00070b4214a501c1d080f0801c0301070f100c0300350401195002c01c200d07598205120745880e41102080b0740c1caa18030b00201c0f9034030404641c4085c080d01c4460008a400403400d5440c1c41c00b510840d800d8540541d5810720a5400c940d4000c030380b5030010384000c2c0c10080c8511950141800c5010090910701e0103c40b601c40084a920b00c0300c4481c442642c4420b00f4500350000d202e840c006200d980700511480c1003142c0010380c0c5010344032000c3c0070190100c3c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 431131357 1250 431130107 431130109
    0x70b180111071412160302010c05151906050105070309030204051f03140607020a081222030e010e040b01120903091511070b0f0a140918040510090818 66
    0x20326040145034210850b03000541d10418071140d841e54900050050700e022420040801c00132440e40c00c071051040710300d441d081c03450f401143e0258040209840c10f000781c0340e0810004141d807646c02c0c00b41e440b10481c0c481c0103128002101c00c070340e40341d0302403070500904115110010b03800000420449404480c0001c8555601d0165402d001c5000e0320000491683c440110800a039440400401c8003950216203080c1d407102820703a5030b02c042c041e010f40240010f2100c141c03900d10483d8119403040f40340800340f224030488204d10b01d9400070018102c010402403055a807055030300580a0042180884090040c5941000080c01c8004100b1201d00303c5902c7c3c0c02150280350059401c40f00818041111000c000d4030400300030525000b0320300c1d203217071801044000a01e100c1802e003513986c070000c41c4910614000d0304440941300e10110791130a80c0c14000a10594000e0387d41c5403040c2c0c404d045010100c215900e8185011414007079405903058501d40f400700000c001c22400001e803004541543d1014510584c110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 431132607 1250 431131357 431131367
    0x50d050d080c160818030304030c03060c020c041406042703030b061219050f040b0c090f100903060f0612031b02090a0f050f070e010c0804030b0c0c0f070b1801 70
    0x3c180c10b900c4540c0905600400c4102001020b01000d41d404205140168030205500ca1180d403102400c8484012402d00200b0b9a507400850002d01c240112400d90302441c0110f03040e100340d1610b00302c00602e903104000f554105802444048841c100e40348068880d11a00302080b14403004c0050100b5588161300c03410341d100d9608407240302d0317040c2501e240c05203850300a5003102c94055016000c0e280c1048045420290f42141c1d25001c0c0354030010290440d0f07103410504400350450405142c1c0211100804105c80c1c45c0c8860301e281c00c01d807641d2840b02090940c1002e505407030702c100d10200d02c203242210400c41001c10030f400c050007a505d85001d0003002c4900d0001d0700035a442990195200e42000140035044019603c841400c009030f080621140d680c5080b600c4041404a40d04004140502108151076204003201920680700e01080380c146902c903240e202032294111400109850000b8022100e41c008200c0d07250000144c038004c1c4041418001c0444482c000d10130241502c2d000202c0c0b005660f8060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 431133857 1250 431132607 431132617
    0x120706060b13051e0303030c0c0102070215030a06140f1002100623040506010c02090c0d110a09080a080a080c0403050a0c0f0f0b18010302090a0e0709050d050d080c 72
    0x181075120b499030315001042e40003000d248505441440c070400d00e40302c03022048049002c00340c0010040c504580e1945040d080e158409142000726550030807948006a44100c110ba81c01a41c11141984030300e4001c0380307003003200c920b50003071600c64940c40140c0449a46400240c40c0340700080d11980001c920808081e07281401641c18105143d040030700c0424111402c1010003a00d00d000f255a0b4840d8401c001440101d03103007502e006001481801d0504054205a020550000380c00080245021402d40d0100211410202421050100002c9800c1c040f680070525502501387c100152110030348503034a4114902c2580d0b041d10500c032880c400607400e000d02106950003150070801791410030b0041e24100308420902e000d5007451051809011801c002c60f2400326050f960403030049850105000510381c107040e0700384021410160200701d0079190742c82e1044628018500011580440c4c00c0801000d0285001900010b0081c000030b213003c00455000641c0d07808001d101d04140800b521100d1283c50035202d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 431135107 1250 431133857 431133869
    0xf061201050f0f100509130b090402040c27030c090b03151005060703110622020402030405071d0a0612030c0b060109030210050909011d04021e0904030816020f12070606 74
    0x681803904c1d9a60083c00504201c9421160290500c3c400015842250460702449400910010000300181071950000c05a50541e0805400f180d07410001000d14241c0f2040d4a900000344400c00c204100198400c00c0152042c02c070309018203100f91011070340d1080e41c1401c20341181808408510558000d801c448017a01c1d01400390b9684049509026002c03004101415040d80700d017000180360004085c1c1303134a000035a108034014449195408001c0650000380003514507006000000950b40d2a00645004a411100f09280c0c58501442c00c0003ca54951b4055081c1c0d1038000d54050000b0742c4200d03140c42169100303101d04a142c50750780040700c1c070b813469400094002825001c807181c810b401c0005846e454034111002c082a07031725010504840038482d210704401c440c406020a005107040001c284244079010621503006e454080015070104007501c068012031303889410701015804484551000342c106000400c0b81c0d00401000a40e21445c4031000405230401061801c00c02000e03410070001820 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 431136357 1250 431135107 431135119
    0x70e0c18060a0c1e15200403031e02070b0708070618060501050301271e06150e0c16200409120f090303020709090f120206060f061201050f0f 62
    0xa0300b8809040340422000655126040e2000c1c80d407000e10702601e100d03000380e011800406a031301c00705803040500304d407405815818001c80710f000c52040030240500021800303603843c994030b10a1100c0a4504903914901e0008641005000b40480150380d411525007950001e0030f56a00c214030300b00b8400030b040e46501203445807190010042401403d801280c1a40e070110000c10500c18600351102001e50701004680da010034201100020422420f1102c44880500346200503c0c400c5998400856002c42c0c0440311182c90500240b0003010f8040c116540800001a42460640c000c921008180080040240422456499461004840307064600c41ca50068401d01c92014603180400040900b40c10b02c000140440c1007140400703202d040b02404603034164000c0c0072100e061174001e401820403403100ba00d8072040c40146070000b44074400c1c4002310150a80c09040305090440401c034118080e00310380c0e0b01c1380c841030107400c56480c500f070300f07050454100700c42c102501e0240101050203852132000f210341c850 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 431137607 1250 431136357 431136367
    0x11030319020421150608060f040501230907050105040302180403230405090a020f16020a0e090d082d060f1005041715040b100e0703020406020708070e0c1806 69
    0x507050082040310fa100d0030240074040c040300c5485084400078070810040354455804203401a07014924560001d0240e0000304502c80c24a1803010400300300813291840e00d20810070424600028031280d00600003d01c2c05034940751868000440101100b2284010184000085001c1501036602d400081035480161001050002072051040d0094441c5c94068900c510020301c1a010a100310b41161403100f010600f4808030504d5890814500e01049802c01000f68011425545103621244120001401880c002c401c0b00d03401005d0507400307815403e4074030901b813110300c9420300c0030a1041a1500741c4105026070b27441600203064001074503241da4014100d402260407082c0c0c800020400d98200c0020b0900300c0c059000895a90b00c451002c811a400c0f071400418001505949800e40107600c0b0210030034080d8407007a04e0b02107404203460030408a0b0340003400300480354050049100034000b0304050076440f0325010528010000c0209803450f9803070006a9440803010144a07048100000b81090380c5034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 431138857 1250 431137607 431137649
    0x30402041d0106060507050c062d0403081306111f020906040f03110901060c08070f05031309150f0b04060f1803030512010824060a0305120a0f110303190204 69
    0x943d0103c24107403401c1c001e08a0746034890030302004603011a48410480c2d0111001c0700207121401000342b10300007a24100300400004a55000042d040101100c10100304031458004080c0c0103070749944403034000c0d070050039800502020f4100c0c443c0d0142c605003400760740e5200140024086200d5500511100365024001000380031607455150700b02c1c482614242c0e0707181d803540300687c0c1040440e00010841181003121000042010303409000091003001100d041c48605c0c441035041481e5500424446070340c03801d414110b2045008030f60f000346001302c10480402d0604625403007a00c40d038014202031101c00200505a1880f6498210140305410145c8ea08175490b841c0040169014210304448614890000301e90300303001089491841d050700c0060780004000e880c0100d1049002010540d200c1112680000410340900400701081d80c03009081d941d0304081d150150005000a041c40c040003103a03008440c07410400012a038102d83c06111282401490a50020181c03265402c002d5071000040c10101074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 431140107 1250 431138857 431138867
    0x18060408010905010b03120f090d0f0b0609070c080d0c090509010312140a020d080a0627141e06030a060606020a031403070504050402090f060a021606080408030402041d010606 77
    0x100b40b04400a20117545080b04056442d01c988000e5103c9010802c02c41680012200043c0401900904584400300355070700d41c1c0d00c203190310480c20313203017074203403908000303d504e80412200c1e80003040f8100200d130841580c440d410140035218403a02c200d80c0d0b80c00a003d01902031810540141401452001c0035a1a0700d82072400501c010020400301c2c614449038144102c0300001c1d1030310000c440d4001c260b00b264500081b01e00c0700c0301511710710886035110000b18103030240c0d03004002407041084e0750800740030008441c001107c070705840701e99665105800344000c015503c03009485410a40c440070380d65446060009082046040005081c41d00d442000152180c0120700c456019020381c503164110701c82e85040c1c03029840111141c00016008000600c15440d1941c00740c00b148a0150a03030ae0b200c0800f10104160303034441410640941d000c0c60401006050f00d110160240c0304a00d05140713141043d80c0d409889002c003074002441541c5030100030b040da2440000300e04200c2e6068000340300c11a659240030344 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 431141357 1250 431140107 431140121
    0x60e0607060f0e15010b0703140a09080102040f06090e010b16080f030106110616081602011e14090a08040302040f0212010b1308011506034701030b151806040801 71
    0xc00c201d43e04c000040c401c2e21101c250340f012a019100e41000101e002c4100070903a200900b03e4041c44107420020500303a800344060800341c5160040c0d4140c490515202400b10441603020006540000f401480203640e008142d0300851250b80407031030504c0c607918049145004902c06480300d504048000606140c0c030020411102ca45a400da0301c00d9281c400c4041c0440d8002e0131400b0211346030102142039081a840180f12030391440c80002030f40540003c0569044034525070039a00c031900c60b00d8501c154158016220b801000040c02000582c0082d40c4100b01c2e03004030701c4007034071580d035950100a40c000117030100c6001110040c0e514040d580c448254001035001040404400d4009413400300320854140301e03200e261021400c4a071281440e00708200c001d0141c000107141c40488405415544032241d0594001c031400701d0018070003002004941f140100c0f90903040c3c43c101410810303118410b48035060300c00c0e0800e042072685681c540350610610750002004808680050340014009503503e419070290b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 431142607 1250 431141357 431141383
    0xc010605011b03090302010e01090306111803030c07140f12011a0a0303020a02060c0102040e010b0306031506092a0a0804060f050613020c01060b0318010510060e0607060f0e 76
    0x50140b60b20107802c50308190032608000c000c100c02200c1880590302030b4150000032841450400d251f1600c036a64a07080e100f0b580c20007002e8210200c0c2c0002905481c0707840c9211040b06400170750600c1c0c900b500c2d090360b910f10351150744420207007041600754603101c10703003240e14205001e03050311300388040f1201e658000c050031611240d41040541c0d503106a440d0640f4010216a0140e000b880c20001c1a000c0000c00e03072045d120100c5640d0708000c0000d204200c101058028600e00d0b9400e80c981c54510141402d04101c2c010207000984e54074200305a0760340e000901500507000700d000000c55208841807003c100c1e0105000f0003c00808112584000e9024600d144103d20640c000d200e1403055451000595000303940047d8424100750080e0420003495001d040200044c20000c180256543c1e41002da9074015280304401c10740c8071407065140302013406500d400a01801d000d061551034104001c00070007001d0b81440c491040021140140919500f0489032203a41031070405c030101c410203a00ea0b844005695003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 431143857 1250 431142607 431142617
    0x304050705060903070e0a15081f0606080f09070513090606054015081506011e02010b090a0e0d0815091e01060f09090501030c0b0715020c01060501 65
    0x1c0303040d0800105881c0070710009802003420070b042070b60700140c071398008266500d0f241d074a1195030340d0300c0341801c204002403030108041d01e00031030301442001d4021a14228200301500b0301204000242c0d00c414846da0054540c43c20750740c5500c1d501c81c11410300c49958042d41e032040c002000104856050741c0180e843d5403045100b003015641d01c2e0b09105211070750f441d4051105400c20744501080100d00c0c01c1b03500e106008000c0f520961403801c014070440b0222540c0d456007030310850086c07100c91400c012808140005008248081ca0040d000800b01030142002c502800304420804440c64000d4004040e1610000c045d2917085c41c040c40044020140720307201071010b20841191100740c500950416014000d8905d001380c3c841c0741c1000340316203010701401052010030124058045060038020b8a4040c110075a119034502c20b02a00003000c000241c0c2011080a140c60010000140120805400c50f00108006601c4801500f1f014060144d44040904501e000052000c0d15600c1980481c080e510240c0790 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 431145107 1250 431143857 431143859
    0x1d060403030b131a220c02031908090c210709020702010906080c0301051c050604140d0215040f051f061514032404154101120c0503040507 61
    0x8030005403810f1100483c2d001010601c01341803800e008142902e164407026495558010800c400d1045407a0240c054006802c04a184007803c0e8006070711401e5007159240c100c149061141030f0f1502c0d0784003841401c0c820381041c04020240d0400d034a0720052080464107454000340d4500c1000080d51195000300d0005064450119085000e00c000d503016130b00001900342184e00381800c2c0074018664070810003081c1d070142e800750000b031f80c100202c510542c495603401c4d014040c2c1d0929a4074215031741110905540180030200e24118411820552091b0005403030225994941031050400c1c1e08410031803580c44010000150441c036980003501140c0304821074801035201404101c412035a02c24007200313203030f00802c0440c10b600240001c21305021104c0030b02502d101400000542190b001100006130300c81c060b070040080008034201d1060749201407104020007001009014802900003012011404040003845850f921498403003004a250714070420801581c20f00c01b030328507002240d080b5a24480c140c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 431146357 1250 431145107 431145139
    0x405040302190303090c0806160315090f0c1103030c0a0315050d05030301030b0f0f0408090a05060a090509010801020c0a0803070c080f19030e1207030219060905071d0601031d060403030b 82
    0x10720314441c0400c544000b014a082d40c1c420ac001c3d0200b880c00804c03010780040089408080762168016480030b462000414400e000c0740038000140c0700402d56100e8100380308000b03a00c8400700844010081078a40014000304201440f100c0c110660081c0e03401145a82640d000c104001000b5416a8000d0480d4001d0750b03128180882004d00849440305811004008600041c7c40b60010304207560009001200d596141c00209803075402069100000492941d0700300180c1c14001c1070305014025040c000d525203a0b8080c220b65446520140040c02104000000b50144c0c0c81002d03a040b4080e840b080d4a0b9460750151120240c5402000801d608a1034034a8410380190091080380407800f4400064070360100745070440c0d0040e4014100c29020344c02003440010340303121114a0800c07061701c00d01002401c94a20305119280c05106d40207010303e00c00d5611441001ca030115074007039104030246404100c44400340481070180300c0f0107c1780051885884c040c0420142c02d90411b41d24003071f0a442010403e01c03425 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 431147607 1250 431146357 431146363
    0xb0f31050a14090c1c050f01050a050106030b030703050c15071502070c080115090203070207320612010909020103020408011b08161d0103110c10050609040b060405040302190303090c08 81
    0x21304495100c20810846526101002402030310540940c040d62041c200e0204500d0035200200d9209448950380d50041c04069094031800f0302c0000c09400405000c0d003580d84a035a102d51006a0920910421840c204034001e1030b011103820b203900c041c0141040c886017240b10040d4110701c40442d84500000c00128811905104d9558040a020003403c0540e103401d02c410f000b54009801c40086010b4040041100a92828643c00600c030750b80e880703800b40391000b100c2c0700300c007201070f006130301c00c08042100c4403142c00030744041415606220f40014500026100580003031180c0e920402c41d950030480700040c491280f50103404050722640301c0c01180e540300250044200c050034152000300e0001d4140010f0140e19040f00e2050300740c181000100c2960701040340600c0d8000c006120b601d948041c1e00c211590076140166604414282e81d5070010b4101a5144518a0001003001c0c2c01195500001401c0c1442041002e2a0460760300303034210703031420504005000d0540a8000d0b0b5600c03c4402c800100c0e81400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 431148857 1250 431147607 431147623
    0xb0f0102150403030b03011a0907020c0105030415061d04050705010201051e0a14090d0e03060103030f050307120509030c0c030a0f0f0312021c0b0f31050a1409 70
    0x50303019040d10580da035103020030420050415810159110090a03050710240b10302401d01c0650395140d00e204085208000040788018046811900400c40d101541d036000f40076650025440794141740c0c0d0000c80d504e124000c000550045484030201206950f04800030703e00d0502807801041545c030425140c0c001682aa00300b9502180b408401c1c0c125103c880d01403030341858201032000030100301c0d0103040100d014001d1003510301d1711030b9401c440e10000c15907801102610b0b0700002540038141c0b0358995280a422844e1000302c007000d000c000000140940d01c2a480120b03c030038440d404000b10709000487d543d50b0b0304082b0b074055061188400380c642c0c2e032a0020713102c104190b115003880d800d410300355252420300344030400841c140002c01080c0c4c0c0c05c200a60003c2d240300c6c8104858654010450010721082e260203110f0705004101c001030044468807419150b40d2180819001111440c030f0700000905040401e407030741c100c0ca0345011b05103c4400700e0340d04030070703c4a0304400300034803035407500040d064481c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 431150107 1250 431148857 431148859
    0x23070614040308060f120703110102330c0903100f0f050c0304061107060e1c23030603210702090606040b0a121803030501050a09060317090f100203040302040b0f 71
    0x1003c0c00114189001040100c0c1244094140086900c003040034500d00307c9141c008842c1078910781c207041e44650b0f0400c61031032042d14400e0390b01c00c1424601802801040c049a8407104212500e000614148010044442c40d400280444581061903005040204801004007407118248601a4885804e5028140c0240407803071803549545c440ea601e42005211126040700713800320600c00000465104c0c03058161030161580038005c1750562a01c507041004024007030703070b0a011000e0107a0203044060003c3d80780c1c44441c0350310141e90351506000070f0f1510450741100840e4032256010890610b1030380c0050401c1e1442901d401581c0d8a5001c10404140641d005443c4089410301280c0c0f0042e01c01c903160034880c802d2000001c0d0f05000c6004d101c84841901c041074000ca41c0b40c400400482c1806010b0800500a8000820850381141e443c00303641d245c01041c110f4080004100360f40e035661610101b81d1140e100901040f031140410314080d48a070024401603114502c0c191521036130382003042000c0c100e500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 431151357 1250 431150107 431150117
    0x150c0f020615030a0203060f0a06060302030f060d0222020408010c0801120b100b07080c122a0c06070c060306080312041b0f0f031509020a0b0a230706140403 69
    0x39031100302e0388403100540215035040c4103410960380980c5060004034011625130700703004014a403c441a07015101d960b40711000300340c070400402103414541007600b904807408541300e13007080180f400000d011300c00d0900f010307030b511041e00300340ea9546c8015030041c0225440507009004100c0510001d9405603000d105001115004a55090001c0c0c01c000407503a02c69081520050041d0301c44804149503000b244040f40c6004001550030304c200b00c2048030344481c10840316050302d409a0846a040c1d83c4010342003906c520103a6038401e440c1c1c40ca05000108840034080d00e0f890f2554124205018004250310401c00402c0c0341000104404001104403481c0144010f03454074161901d0341c5550141440e20307190a9020950000456440c142030300d0280106110750142c0203160560421030300040e1040320015130070740b6050038140180c951060490850340103c0e001c907207402d507014044d180103218070380303984030030758001d41c2c008401c0d058201501300680240008c1100b641480c0c1c807110301210640b00500403075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 431152607 1250 431151357 431151361
    0x906030506242a0c0136031104150902070204060806070e01090f05060f03190c0206090c01050c071202150703080103110d051f060b071104140705070201080402040612150c0f0206 78
    0xd4068980c0541d00c1aa03c0480380c3c0b490418160a1981e40d45e0046c0040c2c03003200d29004000f4040034030b000b01610501202c040210203038a07071b0103d0810388075210321810346401040321800c3d551268402c07401004114140e55080c50000340003031441c1f0a035803180b8042004e90202242084407013019005407071000c0c117004d14007040c2c0540c01c1c100760001001d00d003501c4d0b20306100903101d01040c014944d1107002c1307400404103400c190403528240b103003c40ca410b042040c24003026041010010b9030b00c003101d00688020003100b5240c004600300c55100c8140ca640c054001580c1d0041540c00001203040364044e26214540c3c0000c02d0801050307500491001c0d005038002100f403035904d11401d280c80116007521a002038400d55600208040d0781082c00f059039142010195464130b0708040c061042e0324a0421820312240c40e00c03000241c0315005600010341000080380025046449070b900c001c0c0684048000c1f00d4000d109403900d005011040d00b50300c0d081c1414000410070a40c0504202d036080185034020f06115 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 431153857 1250 431152607 431152609
    0x6090108240402120a0b071d180402010302070807110a0b18011413470304020612040f140105060d0305070c0b030c040303020d0f0906030506242a0c 65
    0x40d08000d001071340d2241e240f031180c0c0400c2c0010030428000c144541042c002519207280040d0207200d080c4c81081184c00c0b00800023801d0b85d1000780d0b000d880901c0500325042c035101c40c00101d000340100c441c02000c0c10b20004801c820720004400000c0a800704881d40e502058640c1c00c50500b90140b249815004d517000c0c41440d5066000d910032003101150150304900b80307280011103405e1550140e01495224218a00000440c402407100c0300342c00e547c2c018407216401800c403c3d0203070f80107203491040040c14080081411551864200c3e0745014075080014400d003043d041805d280910000122542445403040e184101c0040c020907201c1c58009082150701e001c1902e09a030a0b0380300300e4049841940c000b5000c00c1e01c0220b90080c42c00340c040180c1594541d030542c40c01130b05d08002d91008109201b0740c1d0003000007841d44400200300707842551601041a07164003000c40c80703d1181d021070851000c0aa14840324690420001c1e102040450f849120f410410458014000d0324210554015400c043c083c1000d07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 431155107 1250 431153857 431153923
    0x1020a08040f060902031014010f0e0c0f0c0304150e04050103020901091805030d0b1c0b0c09060c010603150b0603011a070206120103030c03091d0103140304050301050a0506090108 79
    0x103524000c0e00003013850325155001070300382443c0300303088100141d850764891983c0c2402078066000d8910140e11a017480c6c00d003660240b44100003407a4400e003660008044c3d01e0048203906460004c3c0408088a4540f0b40b111403413541040409050400074520315195055450140150341c12281c010b00403049503400c22411502030101e80c0d60351761803622141c2042c070000e03504200824004407038000001c1c0440402003000507041a280c00c101d16401109103032004942c010002c41e0304050f5036542107503204001d9002c078225018620551002c0e519225000042c01711240c801d40216a40e4030f0108200c403482d034100a500c0c0030038051240185043c1a05801c01c00d01c0740020100b50b4001400720341840410035003080c1c0000709810480014005c400c0540801d5081108070f0043c0629288a240480d0b04002d490004038051001522181160801c40d031800703801d004982c054500070307001344180e20b843b19101010301000d48040f401844071600000d00c038900890302468294611600002040c01000b00d809 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 431156357 1250 431155107 431155133
    0xa0207170d021b0604020102150906240402030403030506031e2508031c0c030525030f06060c050d1b2a03030309110a0b0a0c1e0305130801020a0804 65
    0x307030030ba420000d0a101603140f60416a200000900610141c9080d00c0020705040441ca800e00e03052a02a06200b50364401040995000105090380e2020400050b0040d4040c40c1d07034001380e600715100200340300616500d40c1150344140f005070b040b82e152481038080044420307a50540f0881a80221031841c4401401c092400724900f02d04503101e07603043e200c01c0c5e49415644000070304100d420b814110200316089070300070f40d070100800d070808111900e421a07508603000c05413a0b083c0ea1407404034081d0304500d4013a500c10055684802420081c032901d440c005010826040001e40e510301c14010410340d500d01c14200036028294400850301a0001d81da00d0700e903561043d10883d04003a0103c0c0d4800f4024000003101d034000c1d4080d51303010405102c02c0c2821004044c0d00100c03c0d000b40358130ba0040c02001003000c12035583c0341d054a4407005540c8581481c0c0c0043d412621188401d90140c2d00345028141c0c0136000e04545c0507881140740005980324800d07402c0380f1607582403401013804803001034007040c0002e113070075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 431157607 1250 431156357 431156377
    0x1a0f011a04060806270405010b0d020a060f030f1a09012322021602090604050105010806010e060d09030203120c16031b0c0e0118020f03040b040c1e0e0a020717 70
    0x201305e03000103516506a1440e182c0401041c3e6000c00b00300418040240562155400c2c20f40b00004c10014603004540c0860a038000d8006102e0275070a0454990310035401100001446001046502801d250341070301d0803206500f16116001c11000821000c3d8050480c003c0d01c28901d40c803030804010b070800d000c1085c9058001270050821000614000092030009000c4040000e113056001c1c2254410000150000340032540601c0c9081d0043c00580d2300890034a4110b03800b42000300e10007407091b0000b00a4854245244951070078402144200340d00080030741480380724400301c003041ea0350360700345610340c0c1c050300c404a415000942c40b404082406120b0705070908141c2042c0b41d003001e80589480090151507405441c0c0248104010809200280d1000003c030240080552820f04089128841408040d0000d0511410007000c1800c101e07805001d40014854110481d840001400300c04113100114401c0c5085000600c00089400341c003407003140c1e601a800321849070801903111a4480031307000301100d6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 431158857 1250 431157607 431157619
    0x23033604091a0f0708090a03020a021c020607050d1106070903081b010c21020f1e04050909010902032407141308031b030a080a090206071a0f011a04060806 68
    0xb0307845400400b11203074412024000c01c00f88508080c04001c14840d0b005101d0302c101d410020307190300001c0e80800c01191540e01100c05641c0d0306240701d0403105104503440c0081d441071340060b52008220021401e8081840d143d203803403d03080e0503400200e840b190101c3d030f05000545802010300000c0c4020b005004040440c0c010500854501c81d065401c40c1c4500701c1c20004200001b802e040000b400c4503062058004443c3c0079400c0c46201495002c1c40d0003031041c000741481102c0405848019004142c43c002c0100820156050601c81a140e0007401c20030400d9000c6c0c040c01401403400782c002c0603d11a6600e03822040526684d51402c00c03559003454110803d80d02074200109a20000c13402482009081c06c28055036540c1a254540c2546610183e01005035400900c003010720301c3d80002e5880d03400002ca003004601d10790584002100d5100301c85000701f103c1284000403c00e005091420b61060100d0901c0000c0303640c9951b55001e103210407040d5503502400402090000c0380c81100181e801210251403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 431160107 1250 431158857 431158883
    0x2030a03210515030f030c070b0c010207050102040b070b0108070f06030209030c120709151a0f04050603071205100b092107080604170301120b042303360409 69
    0x200000303484042d40c00030304403c0e0b1280000110319081c0300c440c100c42102c0e00254501490030001c00c1d00c03864a807040e00c0b44c10202142c2c40fa402c9000703404441010340d01c50001c550b22521000e904510760000d82c01a07507007104c100000f00d50088005204001c5c0c40c0b5109200802518080c0c1c1200a54072417400703543c142c000c5215007446a264001c42e40d1110003031101400c01c95040051900498406000c810b00c2c28405203020092904411b060520305442004000d680e0400091115003503c15584643d0304003500104201c4c2240c0d101b0151000251001001d119503114280f10350301451450103000d641200800640c2e4403480c002080c2510050b00c00742461900380102040d606101c040d41c0251003d0b0000000c001c1000940c589240b81042400422402d40d4100301c100c0b43c40c3e20801400401c0951158045010b110b0000300f20807004080c0201c20000040c46110aa102d4215404840c0320914000d0800b520035483c40b071401a16440a503010807401c2d08404001c0506007078013042d14040c40c1c0b207136 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 431161357 1250 431160107 431160167
    0x70e130f121d01020a0c051005041e0501091410110c0409051605010f12090602090910031e02060d050c040815010303090501081e0c190206090d080402030a03 69
    0x110900798044642c440e00d0104214150b018000000100442d0464001040d10700002c3d107103079460720070344a003501e030150000a4140c00340ca09100b95003004d110390804600310004040007510300e0301614800e984d81d8010307070f58599001960b51130301d100b4203500c07210b01c080d103144c50361203003104088040d0b001080304c24101340c1c00003043c1225a501c40503070712504240b01c1003094901c400507620040c00d080c87d10701d83c8a41000d900810340b11600da0b141d0012603d039040601400501e07016902200c00082450040b400d14a403403009580c0c20b0321003202c81c640a110700001821032601e4007020150054416450503000c212544010b213002404004800e406000c0811045020011910940550b005111180d411401c0c00f5009080550000b07040001900801c03001c0c05541c11800310300c1c101d10003040c1e0701703890308000006940582d03201441c060003030301c0c2c2403000142e0000b481c03070182d4840d20079a043c01d840d0200407a44024120303130194169002600d03050010388102006180c032070080c814440303103071604130b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 431162607 1250 431161357 431161373
    0x10302090a0e0a18020307210c0605030612030901050a2001061d01081b0103020c01110c1506060307020a020d111921151805030304051e070e130f 64
    0x40c0008140307107048000c0000420003841604114a0248942c1c1813641c0c05500207a506e65440c01070300d01c04000d4800d0041e0f4030050040e90041c0b1640304507a440f000352030f5a8002c00395001120201e100307250440e80401d02c3c00012086400c0e22406035034403450005030680076030710556041c0c1e642808488500c00c640268400703204030f00c003402c1940c9200040b0041c0781c50032000140180c1044c0d05541041707200c0a4001412110340b5209c40c020300303001d62509241c50000d80140000c0364980f1441c0c1c40024800c0800001091b01050038941d544110030710748551081c4a20340c0021500bc0c005680040015405450241704030f03031041c2e11400320101401624404101003050013511840f600c2070303400c07003400041034050581d80c43c104040d0700c214000380d841e190002c50904000d420ba220315510078561102c44040b01103806044d80200c1100c0d07480c101441c0a69444034291005040c01891450f01c0074108004030b8403208980e40c4482c840ca00d500d481409000303c040c03445007141e0b508400d9100e107000032080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 431163857 1250 431162607 431162609
    0x403230423031005070203070b0910050109050a0e01060b030a02030c0f0d060311101e030906090503130f060206160309050d08070207060507200301092001090f03080d0b010302090a 79
    0x3881000d10400c40301c1050600e0721800400000c0b02500346420401c54540c0001641c0d912508954070307020365122000c2c070301d04048604040c1a070380e070304003070010541d030219401ca24020000640f080042c541c4407125982220000d028085c0c2c0b01c0400c2010034100780003500603640016202c1400d5240a03140a54400c66a0003001d5130b40c21251640401c10070301c0f55500c00e242044200360781c00b100c0f4620113140240301d15a03002e05a460b02c1d081085409016100754000c040d440d9005108029804090a0080c0c6e2600f1034181502d01d0800e9000224250f050b4424220032140203030020842d03502d5159015080b02682004c00042540c0d645840b40030070010001806490b400b5158814103040060000303061107410740000e01070040421030a00002c004880003540107003a001e115040b8a000c070300007030140100340c00140c0701540c4640d1388800704103109403040048000340c984030344d000e40d00c60110004000b1880003030020201440074190041d820b80103400441014500149010f0303903440003071415049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 431165107 1250 431163857 431163899
    0xb1804030905091e0a0c1b110a060903110d02060a0c020114030412030c080601050909092e0c0810140d08181e0907050706020d0204181404032304 64
    0x480703c1c2610080100c1018141c10108045c414840030340c4818015043c044800d44900403421401c10340c6c3e01b8492440700e041140b060080400d01c1c160768403407000f400604107000c02c0d20010110b5034044e2040c03a011303050044031a80904041c0c105159144107480c07081201800782d061080c003501c458809400603004510030f6114607100400380422441c0181122030000424061005900a1107150307a0000705580344001e084860103165624211310301c1c1411144d107015207200c502c80c040400e00d00c004c00f01425002c5080c400400044400000490f2003900a842c00c1c2c02a14000406000c0700740c004200da12200c2001d032030050034400c1907880f50704945c8030300501541d541c0c22004445203450701c000441035003a902c1c0003a11040310408009190311501401000c01c1c0880010818204840d0360103490301411a030704115200c0380d881e42c03441d80c40c00314020f07000304451074030b081c0410f02c000b00c5034840d014a030144d941c052800007a1111564241004c2801801c40009000c002040c817540c54880001080b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 431166357 1250 431165107 431165131
    0x7080712150f090b060109030b01260708031b070302150c030c0d1806140d2f1c02160305090102030c0106120b0903040b030f0c04081504020109090b180403090509 71
    0x125600f04940e01d48405041c0706e041254004003040440c102c0e003645419102100f102c8425010304c903a078010074528092003e07400d030040040c001074031817000c00940344802c0114500d04002480141860b210720311030000960112422515481003140200503104c46030041003243d1600458498141c81c0c070080d20400c90008900b040141c4d6141460759084008043c5400d0998800002c0d600444107409840b28140c50b88e591168840c00340d2603d640c0f0048488508000d400c2840d68040e40b629030780d4400c410f141d510220030707030a08400da1200d00c01c60705601c2c4d40600f0a040d20350a50780071a4141c2c4030145460443c8814429a81300610070320035403005001c501c105103903059551604103040d4070b00809101c84c0da001440104005241c0d80300300c3e544801102d82083d1203a0340c1d10a94207140c0181e0308503100710300c03400080034500c0301c4600c20b03c0c3c041c1e07000362528040540c0e25038140b020b0796280d88419070885000b0000f49004030350711a40302c0e0498480d007000704d110394580000c01c00141084980080f100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 431167607 1250 431166357 431166371
    0x1704061d040b1e1c200d14011a09190f0605040e100609110d27030809160602030703030b040603060e0604210e06070507170c01020f07080712150f 64
    0x1180c49101c84c585102d00c112483d9004d042c503140c1d005003400e01d080d568080d4098210413080c2d9612005100141341e0302100c46540700d2407184409009003007240f0103540d0b54140100003c1545803100c0d180348a101c14401140c40301a480481c207000e440e45641c12205135440341d10118035035491340241240c2521400080100c0804800841d003541e40552080c00107510300468108101c03801000c0f0b544c00c20404001107010200070ba590010010500c4c0802141562460400100f5602011150007940008111058030300c0004204000000c82d11403100964002c00910b80040d020707402041b12984c009000041e4655252070f01c5050b5580718501c0160b039000001004100020b0b040d083c00d800b0f107101d4141403072020a490107861880f011380381920961010606900304601000b801c03010701184071034042c8103038040100c00d0703403080350518142c054003403590520500040020317003108803a4400c00400c0751925011018610302d021980603900d040c40321291000500250040d05e510b0341a0010001c0c1407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 431168857 1250 431167607 431167609
    0x51203090d080a0203040209061e0301020d0c0f020f100c030209030d020604031202070b06040f1e0b10020a05030f0703090905040b040605180a1401020c0f06041704061d040b1e 77
    0x8542c0007031900c01418814018440035131100040ca6034010401d81d83d0f0343c3d80d03a50480b08224010842121141d00d0740c000558034842c04042d8000c3d81d10b140700782c3c840c2c41003612422010ba03100c65425484940c2903009030551140400303290040184044030741401464905d5060219050400c054512000344c2d00c176209010400d40d0101c9140e0000c21881c0b400c504203012a5100a680103015110a1095445001510300303114140c0c4540000e01003240d0b002809501000c0d0b2402900004404a11410003529040182d0b4004118046115841400f941c40c0070746c0c1c00c4040c1d0301d64024800c203508002c1c640c20082611889071090390301690103000500304c0c42c07400380b4241003510001040800a50408182005000310001d031188102da444015549001201e14803180240604075000410307224207601b0a400300c1d4003107031240c003540c05010300c40c01c1140e00d00d102141510540c40303444009482003040e401e103000100c0c64802400340061011480480c0100041c02d40e440d440d405043c03603031640c412a4a9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 431170107 1250 431168857 431168867
    0x91f110703050d02120a0903020d060f050f0a0b040b0303040504200301030302030310060905090601031d1203010e1003170f072109051504140307050a0b0c0607080f0112051203090d 79
    0x18001e1805c4007515081c01c020006100030306500c00240074440104803001004100c1c3c11800c2042181d2800300310a103015000f05101c0b14059850040180c42e10034007099070304150007100c05420019000b1444d15190205000060a01035105040b40c0100e40305c00b29100d031460000c2d4000d500a500964680c01e100030b080320014038540c82a010f03c82030160401c016240c0801440c1d05c5442400c001030501780320768a49000040d520341404c05405a1450410b800303c0c8107000d035050302c0d58000540029940c0d0341c2223100161b00740c040646000c415000503081c101048000b0080741d22491045d5003403003220f50b501000488480444840620102c0205241c00d9005901000809040310365404070080c41451156602c01c501603a0150b510040c2600c2c02500c04100c0c410007000c0c0603050b85d00180c3c0e00d007544080c0c3d400c000c03065103290203150041111070323100e01c201c2030092010380c0e1556216443c052100c0d00818030f2020450f0070f8040c0c1c00904100c1017102c4007031440f8000c0381001e005801c10011000700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 431171357 1250 431170107 431170123
    0x1703010602010b0315070f0309080a020109060b09090a02060c0c130c02062511070f08060402190f0e1305010c090501021005010e060402091810030b0a02091f110703050d02 75
    0x1c020342c410701e917841e480300740071000e180c000069052160610440b65411006400b000001614030304d4000f5502e00301d030381d05501c40701110b40151801c12407a507140040000b00030003030798600c05a81c0700460a00c05485c2c050000c1c45200740c20412661482c0140c40850944c0400403800c0c1242a580d00e4642c02c01da405200c81640290b8054003d24048004403c0c881c14018504c04881040702d940c0c2458507007442006008003803d08aa08042c01580e14140595a40411034040780203030071000e04504031070072010312034041d9605060391204841c10000507101540d4000c1000726030240144200000c0380c82840340310401000c2d0740d41c1c4980a82071400182c5010582441d00c0a500d00d030800400c04100f181030002e800c42c008a80c05651030480320001100e10321400c00064038400e401042c41104c0c0071091946003120301c120760060301a5031302c6080e00200d000f01429640c1010a80c5803c90035283c404243c044a02002e080c15110311503001c032424580f2186401c105c0d9181d20601100203810380401c0f80071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 431172607 1250 431171357 431171359
    0x1090b01030903170c0403080c0601050a0518040201030f0902091314151504021b010f0606050a0c03080402040e07060302070b06030106060507120207050d12171e06030a1703010602010b 81
    0x110442e01c00750303402004035142c80c4800401400c0080458103840042045030b005540201141e07844841a902040d1280d1003031240f81d1013422030040020b601c0c00e00b80008034541c040c5403030a4000303076200d40055014001c02580352203016512215500141e0318643d1283c064a40701d07103d00c054502720318007103182c40c242d858080324540c045450750462105113074046038000080c0407071003025412400460041c0c000d10004400d0f020303003403e02c1c410111056015007002804040c0900030303282d81e114161918881c03011241c0001d158081d9400100c0e000f101025049880070300f0010b40a654600e4050030001d90303401c02400a900014101e050010200300f254010350f0032402001b0356031405201604600c04c1820040410161803015048c890092162000078400544200446d00c41440d040107114602001e000218120706003c01d0700b003144a42192142c402801030f08100c40f1a0010000c24103002815140d0521074075041400240482c408040e2030900307560401d8036541401e001a0a45545c003881c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 431173857 1250 431172607 431172611
    0x180209090105150d0b04020d052a070c0605030613063206030f180d0804060e01140a0207060209150c0f060f0f1816170601260a0b090601090b0103 64
    0x143d55080c00c8004030760000940f2070303000614a0b40395000c50040d018035003140e45814600000c110b25280003604140c809003c4248200300480c3c0201e841303031603018401002e88206013005060105038018070003541c21441c010401002c040501a20105640d65504103401d802048070001402010303000d00003800700000180d546002141c0004601c0301d0100078111030020b203102d00450f007003071000910500c12001145c159103426040301e40107041514195000c444880ca400103004805006204880743c0741c08a88204115450b036641400294110b074206a074000e90820004556990301006003008299503800c0d19100c000c821029800c090030940f401c040e94203c4410404030100342c00c00a54000b0740018851b03040c1d2142c1c08030000c00500c1080c850301901c111080c3d007003903d1407081c0800c111025804a03071404c0b02410065601c2d0417081c454245120078004405404c80d4071800c510322120741180440d500302d000c6403640e091300e0b1802d03503044006030024401444003440c9402400f400507000c0c04c017 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 431175107 1250 431173857 431173879
    0x1905010609080d0e10030b0111190b150a050f040227030106080303010e06090c0c010e0c040b0307050d061a09040804050306060f1305090f030a02060105120a0302060412020106180209090105 83
    0x200d170020200802d07039401c0580d1440380d03010580c0202e1500444088000440302c4018110b03198014000c24908107617400c01c80480003c0303141d59070380c22130b621280c07000e400c03020083e103441e00b80907411b00c0112480f9809602400300014807045010314080608040c04e0710004400c0c51410726085860b560041d5045030810401402000102080590091401e0b44e0384501503840803001070346800341070800c102950034440c03403c0445034002108402404200c408100c01c134030240030142c0d20f003682d00c10150005d80b50300944001c07801b181c1c040308050384149500c1070071801020020700c03440310840b01120034001c045803d0010741000c000c0b40340d20500c26150b040316191a08005091034100400c280103a98036080000c84982d0140240040c1488402c12a49ca5500300c00d00651110801d004a90003044000b00d808910040000c0f05600b40350540c000d410552519200d03c0c480322040c98407001559240c00b40000c40704400c0c004c480700c03260f000400503140c8040a0030043c810300180e20040c412824001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 431176357 1250 431175107 431175109
    0x30c0a0b0414030f0f070f080f1308011a090402040f090305040305070f0b07020607050c100314150607151413140a17071506030602070b07050309030d051905010609080d0e 75
    0x204880b0741c10f400300c4103203440f0b00c01c500d440c00d8034000c9014010008600030543d100841c2201c009000c102000307092104500e6140e0340c00330b08840c014008840d20411580182c04035040c000304694101c2d002810100ea03130030140481c1c40076505007205c00c80025800080c20802d101041c03140ca005480e80c2c081d030100d60740c03514040f18540d0150690107445200002a20820824104442001c030200038018640815a10f80c01600a0241242d0b40e010002000c00040328140b80303031090040362400926039404c08215032170700c14407010f882000b158191303554030504050340055901240304154004041c22420319a180040300300c44081d1039680c1d203900007811400001c000c0654003140070000703035201e9101d004030f0812440207248048094240d5140c010088140304840d001005280d00402c200b0036140c4498500f11400c0c40122a4900940c0062001840d4001580c001c0368111060001a400102c245900c48048030002c1e8482008180224410000c0321402d00c06031080800600b0700c030b4510100c0724 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 431177607 1250 431176357 431176387
    0x10510052104290c0a05120a0f0f060b0301060804140604050c010f03090c050108071206080a02010206130b13140d120c05090901090f020c070807051c05031209030c0a0b041403 77
    0x6094001d0220010a05e000d18a00c50b1054500e04020202031084605103001c10f00c0050001140c40c00c890350070507414690f410014055101101d40b030781c20240c516842c12608030f0342524003410490b00d101c041ca11601916004000c2c07503000d02e0092020f010b414155000141072244004d12040515040200c070070041140c0c055110211403088c00c1c0302d2030503074400504503440c6418040f01e44c01c0c0c03031400d00701007110f4200040c07891409200f03800312101d47c0c503219951001c004c2c01c48801041d041c09500050b90045820514240f03441c424440000031076455480c0c075052801050f0b856000030325442e0000d24108140c05900e17007402da00d0600ca03142c82180c201042d4408014092110440d03200c122944403094590304841140a003c001d4610854440031080c0d02ca4005208a84c8114146112040004002e2862018040e07201e0011850022800300307041c0014401006144180000d100a8104810034040701340301c0391160300741081790725045c900304000b1603001c10111030300c0d030060000741e109035880 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 431178857 1250 431177607 431177611
    0x501020d0807020f0a0c051912080f0d020706020c0606042c0c0604060804141603120216080a02210a1b0b040e090105090d020601051005210429 63
    0x6850404890781d54001c0a83c42c180c0c111120359403a10585c08a0001d0000302a01e82c000d8a008403107a180d0b004c5200b40301c0d55015801e00440140014402c025400200381e00020310540241d001c0941c24044040540012600503000554a0540006900448110900050342c1c8280100e03802c00441021180360961007114081079154420401090b01c02460100510105e0210050950f583c940c0c659030002d1600c042030f941101c084044460741183c0d0750001c074003144e0400840540c0d4001c075280d42c90300006550100404002d41c02500c45800000c1d80350503c0c0c1d4098942c9400070301502e070f40d44c414410b0656010480b41c2c030780c4007504560620007001160811321a0f070008454511226a003585900c40c8416501c0100020070020303001030615402d03400c0c00c2c4a040018000c02650b0303541000c03240c0310005550f40030016005030005100b1417411448084841045290240c102480700e0700060702d804988001000358030500c001c0208000c48000c100101c0309001c0790603c2045542d40c4c0200c00b002c40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 431180107 1250 431178857 431178883
    0x70c0c2301080906070318020406120c30060b030d03150602030f07061d0609011406030c10031a0a0b070c17070e1305100605030c041e0203070c050a0303021c0501050102 74
    0x1c07800707c00890340c4403140c2c0c403000356002403080200b503581e0890a4176500c01c000040f107070700c40d454100140e240c58a00140105860950074116180c900b1482c1e12402001e81104403642952442102d440742c40803c90f8000d034140c50307140040d00c03190701c50031113186065950180d011580104000e00000c06004152607180c0c0d03010740c011944a0511240d40441c5443d0382c00c0381d903d0700c207400c104021100150820030103050051a01001d030345030803060544506050602d25000b5440d5040140c00d02d02c203500c80e0b07807202c40d6410700040002c5480d0024030481c0999001900e040c1c40850000305101440c1060401018001284e0325a0086140003c1c1ca030f19003841100511803151000441501d1820f240c0c5180741d03440410346e40454508401d00c0010b050714000d03d8040d1042c0e440c440628113017031154012060701c4404608080b020340907848040d500c001c0c020010001c013400100d0000700304210491410344691805a110034405c2071038605040c205000505443c10a0010000340c4d80104140c900120 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 431181357 1250 431180107 431180111
    0x21c02100e0715080609060108010b070209150a080102121015050c011e0e010f020a09231f140a0c0813030804090605120321070c0c23010809060703 65
    0x507500c1d01c0d410081c5581c8184001c041c194030020b1030740c0e80201d03410b00c1010203c51030080358407171000450341c03440c09015030055110100304070000b52510034900344c0e00c044111102070500c5140d01c04214031088607032107407103141e40100d80740c0c03041c1d00b0712030010380d0081034420318030340c1c3d01d03d006c0c90250300300740700510041800310000e60071b000b5400079003000800003103c0c0c82000481603a82403180c003d1148801c1800c071035181188042541002c4c0c021610948020741c1c0340c913580c50822101c15800c64004400c10f42c4488030240071003040e12030303003005040d90607503441c0c040059240030400341141c80010401a0341c100200042c503991504008a05100ea0700aa0900d483c1c1d40940b2608c0c1e42c005e21600003801000e00864002135240c1c4941180c825940d05442c10f00f040b0090002050ba82d00a100e8420000103a404100b01c0321b400c1564495070021440c80c02c161031100c15150b006844245400c00041c0800c040440b203105032125400742d45064003072808406501d4a00202c0351207080240007081096 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 431182607 1250 431181357 431181371
    0xc140a0203030405130204081b01020c01030527010b10030c020f0a0203070303031d07031412070b0c0c190f03171506130905090606011b0512030604061e0501021c0210 73
    0x1020590684008e00100300460f40100c083d00400343c00b140e403020452313005100304480948154401e0251f64040c0f010340038050500d4103041d44c05c940d25402074002c16441d41d600d000e845055170b075a8440190709081307628000b595840000b002401d11840c0a41c00840e5400810f07000010f8400140200840b605072070005501c9504406400808100c0034090f11580709184011080c07010714480f00101000d510b0490303400c2d8004801c401c0c402d00458201030500460742c00010b00000030b00d0000c014500803001921000000480401e165525008060390386071300c2e900700f04041540104030b280d22421120750701425450030b1740b00d860031480c00c50092402400d0129403e030641291001400143c1324040081c4040e1130115030f5296546412030740540001c40040307603a00d0201040d10f07203440150700000508103031686220400c0e050303131010f00001e8000b40d03500c00000e42c298404422813030304056075085e041c009140c14002440c1c51480110820031000240c03040c040150001102140080c1d00b00c8042191 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 431183857 1250 431182607 431182639
    0x5040807050c0102062217030f0f13050307080c16030f1203051603201c0b010e0303180a05040c0201020901030e16031401060305030a05041814070e1f0c140a0203030405 74
    0x200c00d0005801c0c20087e404004e1054071858818500e00c1680f08422011480c2c0c4c0e240c2c0150341100c0084400303026070308104240d00204100c00000c000303146a420844400b504444108252100c10f603100340c5074000c0441450082280d003840305620209649001d22007410820401800c5034901c080700c0080c9581c86a113411854880f29100b19907105865100c0e0b201c80039144107910742010781c44812405450141c500c2015030107a69000d40300f03007000d00198100001503100e10008107026410aa01201101e00080c1960300c03406604503a400c11707400541c50b00000e0340050140e80e00001d84a0b1030740c2107500940a5842140c0250084a030046090182a075104081c280100819080034003a8080043d080352030982100060045800c40c0301d03000b01906a07421440103d84042c9008600c0c0070b040d030082400d8a1044048003188207000304580303000b60110702038042c40b90121000031f0200e0114044c14042c004400d4500d04200b41c00700140c400c4484035030010307882e442240529441540d980c1c40000070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 431185107 1250 431183857 431183873
    0x12030606031003021002070816060215090a20010e090402060a0e0607081204120c0b180c09070f11010509030702061315080a06140121020d05040807050c01020622 71
    0xf960041c000d80305044c207202d0000e48810180c09421114030840841e403440c13444524411040300ca041d03020300b0480900031500e0105103809001c807440e038810140070f2000b1422030801e96003103a12401907000040c0c105800900031001e484030141c424100c0c0f204100158480c102212044505483c01480e11a000f03400181280105031014044c844045039118013005181d90442c01580600880313621040d01c00800c44040358102002400450040302107207500395518002e03066030064038140d580010039a0f01140f42098201c032100b00041d00c040519a5003504082954410b0860100a12482c0750410b4281da880c400c00000034003805001030041b0780012001820005040d007a207103c0401c1c500140018010482501c42c800c01518100c0c00117200c44420035241000d080607141c031040c0c8140c80c0d5080c010f11140e030300f40c2084a40c0030445504100c900b1b101311841148164500c2d901c801050801d545008011400581598040720070b00c11300050410070755010303032599030704501c7e159403602d88802 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 431186357 1250 431185107 431185109
    0x2107020a0b10030b0105090c0a0f0504030501020a0e041b0207050d1109090d08070804051906150603090c090b06030a110906040902030603010f06260304150f02010c02120306060310 79
    0x400400601e080c0000c0c0b850309000b40084901401d00300034076907214401c100e80030b1020341e19500c038014204560760319940103c0c0114068940e40c2409420290b80c1d032205421381c1e10a0780a600011103019215425160511440f01485c01c80c11000308100e00c490400381d5107000c00d0040c0d500c02d0080b942110204000080c002d903005501030b107a40e1050a01010b541c0e5200103402aa0000c40c040e0070000311503610410f0321354400e680110003091040e9107241c9070704508420200558019803155092811a154100e415004010b05d6070002503d0080d81441c9103e81002d8101041c1c1500b0300800307102540d9410f00792074201c81e9194001410b04040b24025040344101c040180c0c008501160000b56010709a02541c0300f0003040d8024000c0c11040c80c80c1408450795400b550700604c5410a027a40c00c0f0039818680581c14100310216031030582c0703c10b401028411403031100400900c010158001066081c050b0b491140400d0000b8020300194182280150200609040c0104000310000d8074600030f400d0098 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 431187607 1250 431186357 431186363
    0xe01060b0406140d09020d0c03030f0c0b0a0e0a020307080f070e010e0c0a180308090103150e01090e070915081c2102162114090607030908030406232107020a 69
    0x20107d0703040c030f01c3d00c1d414003c418401a0003142c4e031640d8040c03180740610f07443c641c9103a01002200055a9042405004003404904688584119515000183c40411040e005010090014a644404010b105240c01c0c42d640004030f8094516004200c80381d00c0c0205c20390401c0301c2e1f03582161200c8445c00d007100c01844040070b802d40481902000014821490010076103005c080ea4248203003030034181c55242d445a00d20a000100e00104010400c0d6042b81e408440403280b0002903a01469555001000351044015000d107402c00d031107c100010002004201a60b640b40c03490380760b25039141c03117000e0403150f00001d4a0001d2078508056013072004095040b81ca40b000c8070f00c0c1c0c00c41da46040c6e0030900044800714000c0b014600c0440801c1c1c0445005400404044d1500031810b0f03c2c01a20b0000c0c0845900903200440600602c0840428007000c1130001d00050140b954900f510111424184100c2860008200c51110340420000f402001029140001c40c980300346c002041e5100c0d003004900d081000300c005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 431188857 1250 431187607 431187619
    0x120a1e0f0c0501030509030a320316030c0c0308010b16080a0f110f071701060807080a1211061602070b070326010b071b0b07060e01060b0406140d0902 66
    0x25801c00c48441804800c0d02c400b0b03a000c121659900351400d90303a01c2011382640114030560582c503807540401c000e050510300c142c542c403081901d0060211500c8d800c107440c511803080110710901c056680c14421160404002d10f40007000700c1040e1802b03400400103000c0c003000f1040c0010a1900c1540701c00c0c6070707454103901081c0140d0b1041c01c408000c005800000304c00c5c0c00644014068090301c0c1d8009a984800e540900141c2580b5182c10141c903480e06008032602c0c0f8554035054002050003091040b1401441c01101a10f4500350528090b150350002c541000c0a101841e480322020703100004282c1d600950030302e5040500000148240d1600c20f051b03010130745c2001e0009071507080582c070102c008009081130600f0003c41d8250b00100c41112024002c40940017018400d5202140d5044d9010111500d90900c640d0380d981c60b2111041d0543c42207000381d40060f140e80f100c01051400740b14035001403040d00e070b58608050408800519505c00000182d030055400301c0d8a0b210b0824540c13141c0f042c941d0080030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 431190107 1250 431188857 431188883
    0xc1612021e0d12150b0c0f0316030e04090b0f04140d05040501030608032506060f030c0e07110c040b120a030f090905040c05090a0902150315120a1e 65
    0xd4036070310b0b01d078101c0c1c03480020903000c02e03260fa1052501490001a05840c3c0c041c200d0750400d20b82d0035558101d941404000d00c14140007102241d024802407040e0040142201c0000d041c908024001c807800c111780500451804e0f8400004c103c10001598104002c045c548503181c40d5420840600c0c0c0138806268001d0240000d070198403600b00e40280101e400030788080c0700c5555500c44140d181d0117503001012544941c0c08000321660f01e500202010b1912542001a41a88955038400b003003110350070840d4103005020b82404040c44d28000654000d48624003035160f0000c1050b0315495001d04080d050041c2d403140c01c142101d036141040c3c01e044602810031039040311214240203000008801d45075022803c981c2020036001d400e40034651080340c000141c0498145400e040c072004a80080120907950399541c0100010b9403032201100000100b1a4400d4030390a020001e0140d004491a901e4440c4440540182c100c5170301081900941c0d401040708100215441c00c1c2900303c03110788900412070028492 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 431191357 1250 431190107 431190163
    0x30618010e09190f0b040f0602030906010f090209130f0902182d0408070812090706030b0102031204080a05040816060306050904050a11060c030708030406050c161202 73
    0x1184038415400c24040320003024190704440074180c88003401610461801e146000410111410583c225200e400c4803040340301a503c808c0c089800980740b01d84560080d400420246c860494108040d00f004001140f812013500d00240300e07110155280c60781592243c110702c12000b16940a602001e4014244030012004c1d0409400c0180048405500d000000781d0304111460000c91481401d9892001683d500d882e9601c0340d1020350400201107507019410481014000403c04130103025080e0100100b800609110014042c0c840f8035400e40d04551040c0400c8169409056010350425000011250b40d60807034030040b40c0a01c11508140311500c00d00c02c04800b00b20100b0030550403621aa5030410406c0d80715410050b41c2302c010741d00544682d216003400404116040c80505a00100a00c01454052180709a50444d04030b594217172038010002c000c2006011182c010107912450b40d080031841e105428051110407115000c1c0540740400b1414042116802007101c80070800841200d210784043c070305 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 431192607 1250 431191357 431191379
    0x20a0806090c030103030842030d0318031809020a05040905060d12081f080304030b0105030a0515090a06060b070203010c14180105070c06030b12070f060503061801 72
    0x56646030040050310005000d1240b14400d490680b070b07250360349103055180c04866101c04002400103064844607680185c0d91240e14000c446a070180850f03160700c02c2d0980d18200b600786184d00000c1030a043c2483d4114000340325003480e15038030603410b0074840e046440e0f245584041c0d10041c1c10280c1000d01c00035800f0b4140d0340200c090b004440f1a960305011598079034003402060000504014940c04a50348020032050003002110742c00407000e05507503403582d0308620110300540d0950140d08a604001014001c1c4109088038030301401056008011403200340c1e40d5a0760384c069840c41140710302484e60100340c48050601501040c5a0460f00134081940c4450103442070380c4c4081310032032281d86010200b07100340780101003512103400c0002c0700e1400c2081d2051140115840380080314100101049001d0003d00030321102409080c050b40c000444842c3c030030030b1181c94030034107410880583c030480080082419451198003a105e503860195103980b20840400c640c416540c0d8000d0340783e07000034000b1410314640c3e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 431193857 1250 431192607 431192611
    0x260f03030c0418090b0c0904020c0628060f030b040c080304090b0a091406102102031f0f061218030f02190203071208160507080c0603070512041401020a08 68
    0x26807809500c51084610700380131a000010010305440a82e0001a022040b03400a800c501c0e00c058805460b042100750040d051a030300310380c0d50846051801c5e0340d102003041c40308480c0a110580f00d0811449003450321100709040c00d80b00041018081500240400140c0308c541c200901e81403048a0311140c60b01542406000759803401d601488001c0d03000243d9038424061103031220085e621132101900d582060080e0800c1502130007060082e01c0c4103400c1820341907812502c0741c98079904016200c0c1040c418442000005000183c00340c48281e20510035091822100e40c111807160400124800b150010140070700308070b00d4010b91a1495500d81c1d0203041d005061220142050760984d2036680b50240c004991f813101000203074055025020510000c00c91441d10021103004522560a01030381700044202c0c1c1e0702e400c000b2a540c1c1c01801003002151001c0100d0700e0841400c90301142940b4200d14010014080c03424543d40039240617010409000217640b0142c528142840259034030525030070090f10103401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 431195107 1250 431193857 431193869
    0x81906051f1d0906210d080a0b040c020613020d0b01030f12030c0509040f0213150809010207031b0309050915010801050d030504030320030409090b0f01260f03030c04 73
    0x1103a80c58108801c110b18940c1d400040c4200300c1a2a940c09000c0011000c2e204240c45000040010b00314080c200131814040d801960381c0401444d0084001041e03484000c0740d14065802d241d50700d00d09a801040e000c0d4007410340c24040443c042c1a00005400c408003c0000e8010800c01d130020050003008010030840a004410700c42500314041e0040301294011030060300090411b1051401c1c2d494143c00002d0b080303090140143c1001080d495099520a00354408082c2c1c0c00c0c40941e1725609504106030340c0d40228040c00843c2404c0c1c00d91030141c84e00e008680e0f6440508400d0b591481014080c50407400171385800b42c4040003038a0280980741c01007490041042c0800c1450000207074074506071400800542d8955a80d609013880d5a03010385d420017590101032074900c0404100030407100100003070f0008080580003c21070951030b00380111444009402c184c00004d5031401800b844404001500250816600013452984803407aa00d0a040c007440540030355001c00400c0c000a00748000c050b00960b01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 431196357 1250 431195107 431195117
    0x120b0907031a030c060306040905070512070f081207060b010c150e19170915070b0a0f1b0e010507050304030b041b0f090b0411070c0f0f0501081906051f 67
    0x100d110405a49144004c40a80e0001d020000100c0360304113a0081c3c0761781841841241c0c881c42c0c440c000105d10302010a40034446038040f901c2001404580040f1500410105020785001100b04050412904c1171f15006030a49459040702e000c00d900c500d50030108640c004111020701e08400c8154009803810b40c203a98668415100000c29034542403003140340c0d5550000d40c000105c940405c20101c41d8111501080e40050020402c009100441d0024001d407441256a40c11500e0328404041c111032005200c018660315041101401d015000b80480d51006a4144a02600c00f00f500484152180b0360005005003c0824000304010200307070b1250180303105480b44100100c01c040182d8507240b4030720401c01b0352440a6410081c01d5841d0340500612540500041600da900303400c0034040780c3c4000002c44499240100c104010740200361583d000c1e00081c00d50380d40d100c3c41c1c40c2c00207168560203001100c4c01c10800900000307540c0280d01c4040140009414100d0b00302c032210384125078500020755640030903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 431197607 1250 431196357 431196401
    0x60e0901020a0210050406110f040810020c0c0f31061a0301060e0f090133090506160605040c060806010801031e1401020d0207060e060402010f120b090703 68
    0x280180259041c1c0348803a80205290345100400e100501310207082130307446a95030020840317581c1c6d41341c005120207444080002da4541ca0300404074a428071000480304c07802c0c410711100a00d0b11000ca20f031808541c040340d00d030700424807a81c0001d500d1488086040207440703007003440244030b420142d003000c140c02903400c00700700041e5100c51086c6028218048401000e100b0401880f5440c0a00d401d5000c04c007000c0c040156400004000c42d18920081e04900300422a0081e0480100040302850040718085e071b06c00b90200c2c00c00304024203409550f015007849a08089441d5100714900c0746400605a00040180320a0800d420040300d00d16490090303000080561000403a99409024010b0482e40d0019030380c80900c00348540582c000442401c11600706060840d000c1b11407409002601120019000043c5e0780c80c41ca1400d07000301d64640f00c0580464000c0300c10070015070f802c9900300c0c000310500d0511900d5403540c002c5c02e200802c0c2c01d4202c598070501180600c0950b0b03506034004e44171031a146a080c800c030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 431198857 1250 431197607 431197621
    0x4180209310c0306020a172a0a0c231603050a020609010e03060106090503070503070338090a020405060906030d05090612130215130603020a0909020d060e 68
    0x428000c904001c814001c80e00c607900e564070120309215140c040c0240078442a00d9503a0300c0c0981c2c0c40102c07a400001d608502142c0848981d1840c2500321951403015001507030b080c42c071000b1041c08191102d120281c0401d8103081e041c001c8072038040c0c0c41d50000c0da0100c40c21840c0512048040c01c85900e0b005031060106142c58031417201035907410b5940050042880307214030340c204100b40d402004600c7c10800c600c0001a41071320104000303406802d05032202040c1c14144000e05290500541c4482e11a034884401007007c10304095044420b049882500803240140e800740c48003a2441c0844182c1e01c14501d002c12041f0800840c1e4244600c0c8201c03000e0055440c2c1d402006112003098504551640085071203d04103400791005004640303000d000345090080d41c075022a01e400045070b85450a209003c141011072420310044008141c800d03d240b801c0c8075172510024410041c44c0180c0c0f0074190300040d9044854015800d41c001040b00500039980c0300051840c0c5006000a4030443e90480040e4012410b5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 431200107 1250 431198857 431198881
    0x9020c0c100c08091813030201051b030f04080705030c031206040207050d0315180912080412080c0714100c0f0c02060d0219050310060305060a03020d03030b04180209 73
    0x1034042240c0d0307074801a00807034690b0003496100b4a132103540003804401d48950f8490070001c039032003261122003040c5040e05a08003c3c0c2501c400a21381c121051a1000b09094000044240e81e004100f00002c0d020554480c90000c45074401c10384c2c090001c1c4408140c60031a640c0c00030091070300d2512900d00b01119100c1c0340c184001c0c0e000b4004003c11343c0d00482247c03541c0e1807280e4401e0602002c00c015106402c1d0340c032503a440400d240500600d0076035481e030002c01d087c842548040304014220b40f4040d026850240c0f00c055481111100a0742040590000708250840900035604e4098001c482c0c3c0310070380301a103040c0343e8812100780207000711030400c515944000d00031205084c05030320540b01ca00020f1501d500700b02455101060920a10b6402c3c803e5a4607558806070b20350202001d5128166a1b06005620307841c4608160b018504041c2040304010580d00c8094488048980c140c0b1343c12a00388962500750040c040e64102c2c282c00500c3d000c4820801c004140f403481c070860080d03510001da80c4414100d00300d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 431201357 1250 431200107 431200129
    0xf03150103030915091e15030c14040f06080414030d050f1b030714130f0e0903030705070f050129010306060e090610050c0d0509040605060711120106080709020c0c 72
    0x101060300000108940311b407043c6999038130000106e0000a0540350703170170840c0440701d44a0b0751000a99a034000d40b10542c20406508400741c00071881400c161600d0300707501c09400640107907000c0050802c0410100001d1144d030101040703081060700d85a00315818010b0003001c04454020a00b02c0450100d602e2401e140142145404042c41151a691790000700355075403000c0c0c02e40d00c041c03800304102c04040030545c1c2c0d1004024150030b03494035618524101c5002048040034000e284142c1080003409107c681200441e4001584246c4216090b82d40e41001401071469462401c2840603010000700030b4040c101c1c001c101044241c0703040054a489800403240b1901502c0495000700c0400c020031100c0ca00b51112240a0b8450b01d02145059540741505050001007000400400c00104182803030780782902504010300010741c0c82c40d05000f6580c4881c140382001d15400c030b020b250071004490040c0b40a401040142c180d0703100329142c00d44d44920117002940682819902c90048003030203c2d491400800e160 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 431202607 1250 431201357 431201399
    0x20c12030906100e130b06120708010b100f0815040f0213060219020102190f080a050310050603060d24020a05030402040605030d020304150e040e03090108090106060c0b060f031501030309 82
    0x14003014550b61b41c04031280024154a920550840034400ca0300020440d200181c40d2150020441d09014030501a01c0524081c49100340038000c2c84504015a02509030f90f4060389280203940d280e902c0c180850002c026140c45028038500029912005840f543d81070412181a603003118200700030080050007004101c0402401a004509a80119607426204603001070213000c888001e5210f591b500882680640c1805001c124040200002c000f21144100c00131303d425680c01e880e524240e40080c9030100540d0008040c881c0e50040c8001d40c0036007a00c0704a000007000e000f1076613542e1000025120390412107080344181d003482004100342c28082901001d007690381c0c00071420315080220302ca0140342e10310825000c201c0b40030002041039440f409105000f00121000c2c2d030342e45148800040040c0001070000485a041031b404210081e80821301012903a00118101850b03101d050000d1680d00250000b40c1d4180700d02c1c906000c1e007920640b403170b41c12030f8465219004481d07500c1c00c0c183d00440c1000424 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 431203857 1250 431202607 431202631
    0x312081501182c0906011e060906031a03070f0e06060412020603040501090218070f0f2a05010614130b0d0209041a04080c0714030a020103020c12030906100e 69
    0x10401c080720f9800e04031000035101c40c84000d101c02c00d1480440380c88211600b901c164045030040100170300c02070301203010581d072a051036001401c1010141c180c2070503208070410141e40309820001d034a0503170b001101184004040d507110300e0b510823090043c4580c034003420400c0d8500101190b0f09140403c21901201e00c824090440c0d80016020400d054200a10545040d500c840e0241c0050755082c3c0842c88006840308001ba0a00301441c0003001e0403122201d00042c0081c507041c201520760800d11101400b4480007003481c170000000a40030b052000d511005081d98288100802c4c120f5a41d60003841d03085060b1002a4800030210500d81074030a1854025001000380502d0005824081e0040e64031078050b0000c031107080300e04d082000d01142c08a5080e41e09050100700082c145109000c010020204540646041079101c00041c1c0c03511909440241070507400507000d446080c00b481541744050440c0004c0c0d40780c1c9004000309440c3c45003118103940203d165000800c003800e20080c0d07107000c0d1070102d01c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 431205107 1250 431203857 431203859
    0x8090f070e0a0b130609020301060e030f1f0608100606020d0f0e0d060b06160b06041e0e0c13060503010f0204180509010209060a030e0f1203150a031208150118 70
    0x402c0002c0408654a070341002c032500c00b00300031030203901a002c02003640020041c0d8a41c5002c02c02442281c440103200c1c480c0d00410902850703c40b0015420750301e0303807661a110700c5e00517800340d039100200711903030048003140105101021448038607800384044a1075a001d0390219610804215140303603000c4c4460b0089007005811400700c1c203241c86a4000d441c4110b400103660300c0542c0004895802032010000c0030035590440d14100b1240c000340343c0d04103600741c41c184004d403901c0c104000410b481c22070103c82d81d0fa44622910241c8000c0200c80321428000c0d00c1c500300801e1056450016003000c0c028180250b0901e24101d80d550326500c00c44080360b139a007146c903c2d10f88080045401501c0041c2c10f9030820b40d000e00c00c69541e956030300020010b40c11151000130f082030400240c5420044204008121a000441d4a0815203406012207501c00010000801081440400201000c80d81c0c0c1010b400166000703081c2c10025000350b40507000c0c0f41c482011900c502540001101d0009510300180f88042091070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 431206357 1250 431205107 431205121
    0x10060806011502030409050f180105010f0308090f181f060c02040f0e070b0c010e06040b040f1e03050318010b13090201090b0f070210020a020102030417160608090f070e 74
    0x1290408003442e910641e444c1c1640d854514090705c1c4155003401c1c41d140c050040c03007014030309150082c041e01c051000900c4150726102102044284510019214400025890a09640d440441c1d102c1401c0244600c01c00485c5a4021244100446880907540010b1862032413080822510208440c0c95035210084141240e0074040a01840c5850300102c0d619480c224a50700420b2104001810f03100022503160360744100d13501d00f901c01c0c4c0400d404454002e1014130020a0840140d03684c05a00f00b607540c40c092007a0b00e01941c080d0265513844000c0140d81c0d103003004140d8800001c500501a52949044213a03403121400e0888560b0b000a6900c0104907403002d00750201074124250007070050502c0c030121980e441d0740440c1da61005203c4010701000003151011803800800c2d58602070202d01c010008803601d680040c0d40d80c4154014400e01c0f104121101802407001c0007a20341c07042d02400b0b150066070b03903803502401c1d083c01511044558010311482e1040b1070000502039040318140142e00003242c40300c0b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 431207607 1250 431206357 431206379
    0x1a1303110a060615030f0908040905100b0d02311a0903030705250609120c050d050606010813051b0a0312050306040b01030e101a0d03020c031006080601 67
    0x3034640340320307000c0c40300081d011aa50780f203110014452816200b134401d414120040072101c48800d04c00303982e45001d03084004101076000341d4080d910f0b01c40c0f000074140c80d403005541d03142660b91700c100d0340340c540007501030528206a005000199600d10740c1c0100d0510070140001c0481c04249200c40d07844100c13204005043c0303060449900c100c46034264525044011002c641075a02217102074806621054503c0619020800415a60f044909081030700c80d080040080407903c0310702c51100d00c03400c100707565000e004041040b84000e00008003940c045464518145845600c1116140e0104400c140018041c100c20808a00345c03d0b44038020b080540002a003082d0404a40c048580e0032955081010000881c541000c9000000c1d54489070b4591401e00c042009070b0310304199023030405003003800a203408100060101c1c1d54210044000c601c1a1160408403050b100041c01c00d584a00b00c0780c800d07400e241e0085540c8483d00c0741581030b00c8a941001d40403c2c2510450301c20701515030702c04001040030411301c07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 431208857 1250 431207607 431207627
    0x5030a081f03081c0209010c03030c03020f04090504020a0b0a020a031115010806160311090f010c0618030314093d0b1f050418060b0310031a1303 64
    0x21406020445041da8101c110032a0400c455031600015403200c00c40a07005514000035400b00190300c0d00c1540000200046414003008080c1034666100c40d440303074060703010349503040c98403210703241c035a9954075000006d40b5007654181d01400d280c440100724862244112054848290003d26092110b5a4105c0360300036012080d007120700660011070f030703030b0780000d02e881c0d000b84402c80040c8014145500502c0d5105c245144a0090500d469007003039849415809031142c40d44111046c9403d2105140140d454804501c0010400f61604220004a5060a0710190080e010790343c10041c44110041042810300c064881000740ea200c00110305410355001c1c0602820400c1c00000e0010300d17451240c6060a1001c8c6503d009429100d4088000c0c508000c090307094840008a0090700c1880c809030050160310580c050141e00358483c0d81c00c1807607501035800240040c5205a0b801c0c0d624580180b0054400e0900d000032039124070700e50b800c070600030102d011050003418a103843c45088a503a0350291120822 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 431210107 1250 431208857 431208871
    0x30201051611040e03070b01080106060c150f05070201021c14012105120d14101a070203030f04090606050f0a260702061501050a0e2416170705030a08 66
    0x241192211580c1c94500441c100302510100460300c07001b480c6445000c1c0c0360140c0024501d60b2402e40200030042d800b28040050540201203012081404030403803024150b1b60354008203450410003801480e560540c003c260a081c54002000c10b652001c0780c0d60b068403500d074090303c3c14440c10780050000603406102410340e00c4001710303045121686d82d602d880c200160044c00c6001820003140c00c2d001403081e4000c64889214603a0704010a00e0b00c20b0441803106214084d915a444412091303190401102c011100104d80050890f5211491503c3ca402641d116000f04c001c01418900001107550003002035900440c21480e00e203040c044034260450b0402c2170990300060807800304e20207074007800020b401c40f406003007a83d000d1f080710320346440e0100b00058420300542c10040304102d10000a0340c0294503a400c000f0859099800c29101100030b041612101c1094014990000d007001002e503604980e940101c4c400e5090100312049484010454002c001c4040c1c4a03070010040c02c500c0c9032085a40580c0006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 431211357 1250 431210107 431210123
    0x60b07060c02010e06070801030623040609061815060501141207021018021f020d031e020430080702060306040e010f0c110a0c0302010c080715020405040b0103060302010516 76
    0x4caa8022070f00e002800d844080200d0780c44801442030200a0151081081c000c5082100707100580b5216031040d14010300c0584110b03900d2505004018841c0c00141c030404440a40c5c0c000c00300103007017011203005044100020a8500980000c465025000341c1c0c00342c3c40d401506600349040340012000c0c03200001d225030114020020a001d6010705031284006140c11aa1840d56100303040c814801c480c03d04100008d112401c4415940100c3d900040c041c0200059190101354511400703c098040c2c481d010358440551b0010030082540050041e0580c078032148641400c0c1c14100c03804507107442c00c00c810005000c510701042050701500b09a001150022030180c40062400003d40103035003150340c00d400708040d1a40f5021803440040e889841c1281204020020340045060340d510101311603c1c900c40241440247c2c224601401403400546e15220303001107080785460b0030760007244000d5215020703080c442d0780b91079090107031940309200f200d060380e0b81078507840c0c5440c0341c000711200795041401044450034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 431212607 1250 431211357 431211371
    0x1150206091902220203070e0f0109050f101e02280515070509030f030d1505030a0f020102160f03030909020a23160501090209010b032a040e04050708060a060b07060c0201 75
    0x118901c02144107c0040da1001c0d00a0100c1d000c00c4000b0140024160400c40520030a01c034607561740b000180181e1048444180b500c0801c0c0342600d0352201000c0c56000000c120f4510860307980c010914110507401c0b2418510549501c9441610760b07031300201d01401036802040c1d00c1440e00110391045402244a060230341c00e24140e0b40000c1d15164a6410382c505070340000c0768044288005018220b4030811a00b058004181042e0101c3c1e0350701d441c80750140401d1000500e20303082d64001e000d0082010030b83c14400c2c8100303455010000e40d5001c14401100004c1d075070a00000ea940d050f10941e200940c460303603101c12403c005004182ca0a01c180c800141414040044001c14a10311020440303c91141c4004034007035032903004202ca0868168098142c0010420412081150303040f60740c00300980f9510900305015082001c1141d030f01894200710307981005403040c0018000d00140c04000c80b41000b04803061565001400e80664116100e00c40488006000131000a940c6402c040340100503803000096070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 431213857 1250 431212607 431212669
    0x100911030a050d11010902010e040f02091c12031a040e0f0a0b060901143601030803090c010914090a0f0c0906020d02030f16060b04020301150206091902 67
    0x200c08010700880d255400703184074480d11904090102c42c1e20148500030401200140c00180014101c40c02c911f224503502c080001c00364410382d054504200f0007078080b4001d104104100440307909001400d9410004100702c2d070251511a000c1d00980003031204040740440c000d0014000a411059104000b60080c24243c4040407420080b070303d46c20303014901032810360400c2400d002c43c2c3e0360181c210782040d400c505103400781ea846800b404080c1070400001c0c282c01c0780031891591011119050140d4210a0745000003041c80140c034051405015080241c411700c904100056030a11401e00c20f0752824451290700c0b03103040c42d064020b150310084a42012031544000020002120845100c680202c4c8000304203100c3c0e51790412041170003103198002149800241d03400e01d0100d01401820358810354101001c002000320941069101220143c801d644a5869902c113904240e000c0c041603005104110014120300800502c00003c1d000031422442009220703028050744200ca4402c2d5070400700d503007020140b1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 431215107 1250 431213857 431213863
    0x6092101060e09030d111e1605031903050708060906010509030a080304030c050d0306210303020d0c0203180f0a030f050a0b0f01030201090b120a02090a0305011103091204060210091103 81
    0x41000d001000d980e0319480342c0c000404451b654001c1c0c3d54280000d1000003414004881070440b046003000341d5548511034144000421869040c004285000100325041000340da007900119120b01078a062200c1e641d400c01c00c44641c03804a54066100e607514022510701d500544c01000100005000c0c0c0d400340c2c205480c1e45085a03c150380442c00500020705000c00d0050500c60608001400d01c0d00340107540c81c2c04100c005d0398a50180703403e0060070a070555410180030354110750f088840001d0500c8900c0f201c1c20040d44a400005000181d41e18001e110952032600b6622002d40d601c0003040180e01c14110340381c890030700794103850889042c4501c0b1450000b042a07070701410701c40d05c3c410f1104040c0358158030005210710700550003071030902d000380904403c1408948490782d00400e0620010b8603202d49100003000c666481e44060055441c4c40c24160f20022024000d6200310010003c848690040200c0142c00e03120b41e00c240b0006030011500303145001c3d660740080480358050010028100100310010b42 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 431216357 1250 431215107 431215111
    0xb03100302060c15160f0c0503031b04091e0b0d0305030a020f04030803010f03050c0616030e01031e0203010f0e07020703081c05131a13032109050f0c06092101060e 72
    0x58400400304110080b60321400200d01158075140a109541c0240d540c8c4c1c0e1b4070300001e050450290701d282c603034000c8091201c06031401440c42203801c0c45815600784602a00c0084a046a450709082001071000d03810a4404030790401d50503902c5a1640c0d6440034080c2c0250081e00a5402c1b1440c200400804165004081c501a102c85102e4410a40c40c6203000780c81d15540303402d5280104070911100c44410860352113811103540604044210691000048008200f002c0c0c02c0000011080321070b901c241200d0340510b06880a0200061800b030310381c01c003220029012112500140c0c00001c06200180241c0b000e400001e6642000c8611010014012819a4070454080381811683c00d01c1c0d034180711030403481503010003244403407140703500b0b1840000c440d61f4482e11b005414005603030038cd840444c021040c042203004983c6000c1000b01070518105484050400b0120814422007105543e80d25000081b14800c07034004000071141540c2241520b0409803540140c04655a200800501c1840000641d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 431217607 1250 431216357 431216371
    0x30606040321090617041415101701060308160f0204331a0a11060403020312010f060203161505070e0307090905100902120d02060f010b03100302060c15 67
    0xb038416282401007850b80b0740e030f20103001c001c107480c00540442d01c420350307498000d42c011089001010381e4522081c5090090162011034550040402000b402404203480a5844807140c4103001104001c480e402d0b9565400041d024010400c84244ca13170402c010700c8900d0610542c0c07803568219136500018121382d1403e805200081c01110b451505c0464402e61107100d811609444002600f050361010003481c0c81c50398191003d40000d401342d91180901100c16400c241c4d50101d0300d90346068034001303480703420400b504200c0517010000464007030040c0750680c1c1901c3c200e900642c14900c101d5920107000c401d0800c207440c4003140100d820010180c60080a202d00c503207032188450f1170808018149001e48542c4000b0009103090030750b00024002140c0944203000c1c0080100e044244ad00000310001540c00001580d8451441003c0c61590040f480a1140f103070019880c10746e0307a842e424240356100444080150440882c0d0a00c01460480060402c40c000385040b43c10a617202945801054001e460032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 431218857 1250 431217607 431217653
    0xd080601141c0203100905040f0233030406110a030c0207090e06011806150c1b12030305180a030306030b01080c010801031202031614070b0a0c06020306060403 70
    0x1101558210500c0155889454962460104034404180400c1c0d00142d0220b040d03030300000803a00c1c500d040d140324000781502410070800383c180740c41c00e40205044907030700301d004400b00c09115178009002c0080c08142c0b82044000fa080048121449006500040c801c1328590350701d0b050310a0391842c100c0900f102c01e080c3d031000942e00c03070013000c081c1c0341030010f038021201c590400030741503e400d00c045802e0341141c5428074468004100460020003a00700c1d60070070b140c0e5448804808446960280c42c480e1070758040d01c40301c82c090090f0519030422614034001e4440c129145445000000c0c0b00303a100d16405604404c041e480c040c402c207605810100720041c1030300080d0310b540c02481440380d1070f2859401010024028103644000f080040e08198052202600c0705500c04c00d40d100e028001e0080b0744203c1c00703940d2403484e4080540340c00c03121500c0c04102100035114080380415800c84c003001b01e5000380325540f1112115040c558a40300070354001020030790011802d00c00040000c00042c20000011000304c80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 431220107 1250 431218857 431218861
    0xc0b0d0f0f051f140d02030a02060a050a0813390f0f080c030c1504030209040c0e092a03070e090a0308090a0c0603020903150a15061425050d08 63
    0xca644125090781c520f03010200d500d00104a110725010764030f1340840040c0c800384030301800c4d400002d090010b607020280d00a080090014a21503000c0c0c01898001d41a80320324016840d44410407004141110000389858000c2c90302d110030075400002d288100000d2a010b5440074483c40204089040701e9000000c012958841401100640d04020380601102c0307008040d03d00c4100d0000c0d0b910702601c40740e203019101d031410700b1984500c0ca0044802954000e0030450044c202480d00c0d090560991040040740307000000412103042021810f8103078003a404a01024900c4400401d60b44072107410086981842461070000c1e0004002c95403901c100b9480024056400320341c100076000490042c5280701c290401c0d18190001166080d070305d002e50360f4901d40103031140c1c1024003080c540304aa100700045c60a400c0208581c107641030b0004065031001144026407142c0d24901a00d05181481c41200c40ca201071040450044401c104001c80c28190f4216031802e86c40c075140e003401d244101d507070000001c0340001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 431221357 1250 431220107 431220121
    0x30a060c02010b060909070e0d060e060a111c11070b012318070c11040203130302011a090402122104060f0f0f030e160b0c06060604030c0b0d0f0f05 65
    0x120300125100144c0383c4d0b51800030351000080503040010700d60028400310100001260300e40345030304280c1ca6400b000400031640503001c480d50743c0108980b1485180d0405a05519a1000c50b0545041006180b40707010280c00c1096110050100c04a00058982c41031118801190001d29254024000d02200700d1441030100c0b000c0301c0c42080c07440c00c40c0c0a0460030345155040c265944400758403503500d140c1048070036003e2410500e451070760000f050b4000d002009219828440030022400a40b0a4008024044032940406401d41110101c0d0b130707110310160006005400c140d038102e0310350040d1506880500c1844085007030020700d8080154540c40000c18103003c0b4076044000d16003145914141090682c10f40c80d00144481d4400000504050300c500c00d17128100d00c10003000701c402842c04018502251036500d200f4980d00010001103440c42120007094113400e09204440035282c03c00f10100495003000d004500c10303805140c144003000e039074800048170108103202e01d84112814800104060074058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 431222607 1250 431221357 431221361
    0xe01140f030406051501081303030b041b08010e100b09060d2309010b0603040602091503070c06050a0509030a0c080d050c0406030e01051519050409030906020d020708070501030515030a060c0201 85
    0xf0b11745082156402107583c0d5503a08101d40e10b0303000d480707410a80c0358100d80349400c9003d011000202500141005203080c0b0001c0d0f00c0c00f100003038461607510f00c559603036660040f0440c0c003001d9501d19200a80c047c024002d82c1c00e86030007403202d030002900c1c00c1e1400e200c0403985c030701301c3e0308401184c070002100c054a00490500c0c24515504000c510000b03210300f0700381c1c600150682c4400b40000303111070b0380000d2000035620f568001c40362510403102d0369512031405410250000385080c000303d511038070740070000e02807400521540b8001d07480b2400450415482c841c064802d180703509c0301950416000d00070403c8030382032802440d101c1c280d00c7c0d040c291101c1ca0064090181d500440502c00180d040108004031040907152850b01107000f02d0704142101d107000c0d225100000650052504141011011000c1c541c000545104a50442d400c80703118100c0e0243c02ca8880041e80171f05580c94200500c1081950b22076040306410102c89004003640700d034180002031070700c07640e4042160300c5922803145c4682d264081c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 431223857 1250 431222607 431222611
    0x140106030b0307090c0905060306030c0a03140f0f0a0803070207090207121205040b06040218031e070503030408070b0d0b1c1106120f130f11100c030f0e01140f03040605 74
    0x8403030203001d0b2070170f040c40c050140b00850080340c1c004c004c0400002c10035a4108190400c0d594040c01075116140c60341051180c044034a500001c080c07043d0082c0070103d03807001410740e00c02041100513004c008003655582d54030340d0021f41094110b20a8481c00b08481c2468401080d800d032244103070f02c6d00e02100304805050b0028421040740341528140c00c22001c40c1190130440e900c03590031240140c0d035080b40107042440d0000256955094410048065098403e031201e200f55011180110350300c1030343e101c5c10036581303200f18003540e0340641103c03070104034070480100030300104c00b116880820260796260202c0d401181c00c003000c1c0600604d0351108014005040c81d00381002030103545080c50b12542c0f210711342c1102400f503c0786076845000c400040342c645940701d009000d5a48a02000403482d42030030300e01091100050514410b080c82301041c121107000d0807840b0380441c1d058890040007010a08241c0301c40c1c4c4106080c5050001a0204001c0c3d1408a001000e80d007060f41b03110f43d1a803d02d402c2500880d840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 431225107 1250 431223857 431223869
    0x60e010e160503150409080d0c050c07090506012a0212030715050c0702010e0f0406080a110409030f0305100302060a18050319170c01020d1d07060f0c030201140106030b0307 76
    0x3c1090144407100301140c0d81035154140d03008a11444140351541240c81119040410103180160044000354031100900c0f803080e21008503022a40c03507000c0c103011102d0990b0350f80d012408580020240200c400254408901c9030901b4135000b48a86c0c0124a503070384000f07c10305007a000054240d04000038030741b00304101051108100319505e80304245c5e2a051081030400b90504c40e89c1c0c6045c107581d640c1d00e0b5070f6514210014005002450b903951280c0c2d52944807103c100e1f0b251660604c840b4060420388144076200e6059650a04441302854041d0002e05020b001c594141d181604007202680b05d10004008242c1c0030b0b80e0700040c117903403121084101002070300701c00e01c250083c480600c0341291400c3c1420300d19810100c504011f007001e0b00010381500c12910012895400440c044003001c1c503550040082c149d550321406060301004150644074820790042d4000700300c1000c042d48070240301d0495812214424000001e1000d410071026024000036840300b0300003510b460a08030305003000e004403001426 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 431226357 1250 431225107 431225117
    0x52b0f020a0302070b0706021e0a0f020c0a031211010c0e040b030303010305030d151e030b0121060f020705100902121605010305040c0519030308090a020310050a060e010e16 76
    0xe580d0340013512000c4a00c1010864880440c188013407140980c105e031940305031441860000c4081001041c1ea64102c0c240e02e001083c40b60500308030072400422844d260060003041c0403e01c40c21952103174010307922080f00c0c3d02001031405003403c40b0b034024482c1c5080b14003252180150044400304002c02d0310b80ba41d400c0c1d030003a082440104001500042900d03844030350220040303400c8080c1d0b19034107941e2170303103910603008001905503107140600f5050b1840250383c0074200641040e81c03039642d1000480028004004200c01ea102d5139808903e503640440c139090087c40d800744c5851115200d0500e04004203017a04401a0341d20342001c1149080c90220a4440801d8090184c0d503115940c401601130342072103558145500c1c1d200045c2049000001000038160040c040104000380030301500360001907000813404241404040741076100d001850b41e1045600400820b1059110412003010340005071540081585405000c0b8580e0080750714030f1b01070300b002162060545002c400c6902c3c110740c02068981444 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 431227607 1250 431226357 431226373
    0x3903031508070506120711030706051b0306060702090a0b04150e18070303111207051c03020c030403153c02190516200103060b1204020d052b0f02 64
    0x5141c1c00159900e100b00034489081e070f546e4541e400da941800303000380e04016010006212041001c1503001c0d50040d54542140b60807038022001c3d410007072000350341055000c4400c2c41020014a440009260300603440c83d0081210942400403034166030501d01c0b92511861003403001e2140c010f221346195403007510000f820a143d0000c0c021a51107002da4040901040f002c1601e41a40f00e40400443c45081480c1d00e4086d607490302c5092940d00c40114604070104504400e501c000034900c01c1c020b651413002c00c40c000c0c628080c40e40c0d4030030146000c003080025030300c0d46606000d03100c88160507c6143d03280d8030b100d1a081400042d180501100032200031940d141c0d2041c0070300e050b08808882068401c5a8504100e5980c03d00e024080c500707614680700040c89503442c000e05510050700d5000302100147e00303890074000251981031490700b0f405118680040b100510000078007500e00200900f8881e400303030064554400d15813882c00c5504510010a047c00c0900d41240300e800c50341703e00610007041407031002d80840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 431228857 1250 431227607 431227609
    0xa0c0b0606070c180b031b010807080402091909050d020304290405280303090f09061d040f060c0203121515090303130e07140a39030315080705 63
    0x100c0c3e440c018000c2d800003040022201080c903611006001c039004040780c2c2010082000c4c2001503400320503107400194410082042d4a000f001458002d940c000c0102005da0f40d8010304d0724072461030241d80071402d500c450448012034828018081c0301300059000d19512f6081080014034400c0180364400142542c400701480d401c1410159000e0350030446510101c00b42c040e05001c0d44824000780c45005401e904030000405030801140012548a00305803040c466854144008032442c0d440781003071200044440240c1001d0f400841079000d489102205890401703510342c2d40480710502c15000c05a40001030565019241599aa6000a1641e041e4041070380704800f040002c40d540d55085405940440d60004940d4180152607103446017000583c0d000d960f441540c20205801d452020200708015802c1551040201c111854104203172240500d5001540740d40c0e404100141e040341120340000811003102258404071014240a80d40200d03541410310400584d035801d55200b6205e940c0310602c20495 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 431230107 1250 431228857 431228873
    0x4030507120c02060d0b010801050301020a0813051e0303090709020f072006071a070201020301030f030c05032802070506040f12020d050613120f0516060609020a0c0b060607 76
    0x815510628042084541000548810b98480d000961046000c1100100d001050f03000b404540000d907551100342e41c0e1003043c1804c0f4442c0120140c00100d8540c0000c0d48481d03201080c0221520800448036820f00282c0030240316144040c0c0240d00d44c00000034001980c0c41040410040c19590300f046161030304000b0030f81c00ca442000340c01002482072020301081c40d03402a0344100a6500940700a6994509240c8005070b40281403203c2222000500810764152051007943c1c141e981c0b00c10000594001500d003038075980d02c1c111b82250740e4030041008146883e14089010828200c0d0418001144481c00b0b019003410016041140104d009000c00c1203004a203005540441d800010201c03115401400499888c045002c0045c1c207610421042c004070650100c400c5ca215070040c0c61316202c031840c1d501c0c121001c011803070b020400500709108040e820540d40c2080c5800501c039110019446584000c031005a800c00c00e03040d404694500b16036400e20aa00b0304503984034004480640c584200c60303681c506 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 431231357 1250 431230107 431230117
    0x7030605250807031e091e120c050a02040f091505090d110705030d180f080606011209050703080a170c1e0c030d021b0c010e1306030206030f0f0609040305 68
    0x100b00050300030441d03035402a8000030710112208504030342c0b8412140c03800040c1ca006441285d1202e0721409032072001c1214003072210f00f00d5108000708000080d202c1d017150148049034090302c40e4000c1c1601800143c3c0c0da0701c24246c00380e020140c0030481c4c50550030b2920301200030380d80c0c1d2281941050b04002403400c0204800044401e01d050410388a035004454600e8001175810880d0075100d64050340c604150490002c15100904849101e066078940d00126041c9140d0b01c9101d48035030100010409a40c0500c40c2080e8040741a000020160450340340c0c1d61800104d80d10a803488100066444035056001d0307803080d8404c0018001040c142404a81c2c0b003081d1140c402107000ea8086111071581e040d620400301d42e2500c90b00001c4039116070f804003250000303603c0b4040300200e12a0031110300420941c08100d80408210507106c0c0d036a0b20a440702401280607140c80110102aa650008001a42d92001442c0181340350400881d040c0b50080640e0810f9030003a004601c00d00c180000c0000103680078080312 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 431232607 1250 431231357 431231431
    0x6150806040507110109151815020f0c0d120c0e03070b0c01021c0501080c09011401030b03030415020309040b010309050a120e090106020322050109050402030c0d050907030605 77
    0x51240d50390002210701c0d422041012030304d9420015890240000d1202c0c5103a000781d0340c54100100403904c3c846d80400258a80700400c130448240d04a40300840507405040000b02260000e40f51030701d0342d0400c40c00c00086003201d40c00b28020000300400d030041c510404a8001150501300c80c288031140000b542c4540500c035003040501c1c000341d600000d07002034042e01da0341c0a00204105030580e01c254400040c09003402001030900c5103144c0c0070200e243c244c0f052412200003120800201d040100110064004801030340e4241c403040100040401c600301450500b21803e9015580b10110402000305599030701510904040c180041c48010410128000726a280d200c000d030388000c21300300000e03100040500c5002d540b00a03450000184245c0100c000c06031011802a90030040e0a918800d140d800703050f000301800110011001c0c072980c1020381c0215040900d1203c0241000c4005d550607081d01c20071a82800b003600f00d0741c010401c0040334040c00e90408955a01481c082e80041041e8000c0900c0c081c1030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 431233857 1250 431232607 431232611
    0x11030f011a04120803391e030f0103050c0603070503060607032c0112140601050a02010902090f01090e1b130207021e100314160c0b0103061d070518060a23040615080604 74
    0x4e0050041c6039583c6581f03a0300c0c2c401d00c1c02c7e2240f9200c403103100b04e120240310540300750003507910103141841c1080c1124461842a02d5403400c6459400c140009500050001c5062002c01185254280e03690159229003041d04900e2484540c0004001040b6074501800445600c2c10320901c0340b081680100c1381c07a030000c030a00e450307a1102480f14049014042003000a90172642042c14489041102c50000c0d040c0c41106100b480043c448000c220380c5e501c082103040d20003660040d080a914509480041c9a551a00ca40581885c2058000070710300300070010840f041c00319041d008000c9003004000b18600307103003504040015a44400710b02004072801000c2c074208035403000321840b1250096807803c240382c2e00500d042c025585c4901d0510018050b030b92000012091102e2607180342c03540015600161240981420301441c010704142c0e0000401070800d41d0b010110820125012400110b5601142011146055070249400070310044409a400c0349000d92041b4103100d0310560480c180541107017042d900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 431235107 1250 431233857 431233867
    0x605030c0f070b160f0903030e0a030501020f04030c050d0b06040506150703020a1e020303070807030225050a0f2d090c030b030111030f011a0412080339 67
    0x590450301c07407440107118241c0c021407020284074036801d070740b8803c1620421035050804011003c3c1c900c611001c00c2c5100180e040791050001a204541003070940710040d0160502c03544981c0c950742640c015000e1038003142c0001c1070400030301803840d1071000100019152100c07400c01300d46034441c88100c003d20050240d03440f100421003030307140c20052103043da490a203402e40f2846a490001d48070140180309842d0a03280900410800d81103100d030f0490700340e00a0045207003809907650034600744c0100c03105800354000d841c88a0407803014540450403c0000c028248200e604001c1000b642002d00c1e00480070301944034034240008003090500c000b0104000100c00c030818100b040d090b6019041d0341184080600f00101c0500e440e4154128610b8030004600a000742004840b0903821400115a00540c0c000c05100411000030303c28003601000200e03d060303900e0079480b99003d11070510b040c04100c404280000811446600c0c3d001d03421801400d10010480e410250b081491000c0c420112080490f100098 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 431236357 1250 431235107 431235121
    0x6080d14071406060103050108160302040902030c0a1d0a06060c0212070f0f081203040b0612011104060504140a0302130b04060f03060902090f0708280501030803090f1204060503 78
    0x8280c401841d401451141102e0000c000d00342c4800050740c4a0b4042820032001040c00308011400003c03844248100711845440d507000c110180c5402d07002a42c050180f00013403089600d40d90b44c00c501809020000015944010301c2c89900030100070041520b00d8541401403046682c00701c94001c0703c7d50100c0b143c0900030f290351080d504042a83d44030800007039414400140301352081040308211340921007520040000c9600ca007036184011903009084e1040c280025110345411034010381402c0c5c103840002500101c00c1c441d1011780e40190048008640003041c20083d00746125030f110300ca00350507103a2603551451580481c00944503080d00d032100c0c685480d03e42c50141c54944c0840014003180c00300010942e40c17030070400010311002c1d0050f4016020340c00042c0911001246582c000d0714556250f508503585d03c1c503041c005070101051044a180165402c42488580340549800b071409000e44c19582e00708040610b1030881500d0803946160030402e082c0310500c080b41c050350111030490400b42e0b0303240d559072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 431237607 1250 431236357 431236397
    0x90402060c0105070305160306140409080c06040b060f0301140c21130b06010207120f030e0303190e0d02010503150f0d0821060904030e010212160b01050406080d 71
    0x2007010315619100801c004c4607031680020b0300424074030390301100c12078940500710300b501c01034060501122000020300416040c40da010205031401080d0181c1440d24524034282801d2003568141c0d00f607840385081c450b0502c0c00314100070400343c0c00c8008011060040e0b03030400d00e83d0b038001c111a440001c04203400d003603a20030001c4034201c40381c1da00450b846481c0c2614840700c682c841d02400c0d85e10310b4015000651550001a81d08242c48100c1002d00324020107035a0740c50305807424507003103040140d8541d401000791410000381c4001a052100c0c400180003204000380020040340065100e8803040d89124090f0741c100c401c072504085070303901208130a03101c28045004080400307075050b0802d0303620700460180f201000240c490800001881d010304510050079130a00310b41502c4156124285a02042c0044e006448058402d031060060f42c4103040d8008403608940c20210500584c0d98100809504100101c6499805400c04490400c40c0302d05101a4594486202030341314280308c400c0c5603480b201c240c13070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 431238857 1250 431237607 431237617
    0xa120b0f04180b0f061c050703060204230a0b0706020d0e07030302060709050109180e120301090906050a020307171b0301090c20061f05030307050604151a09040206 72
    0x80c2080c810040c900100d1140352440031001e036449160440800c0e01074601204e141e0040744001c0802d000c0c028003415402c51004402d10845182c81050b000000092480c005040109441c1c5e14412031007600c505001190683c080340c4034801c007000c150a00c01406040149d641c0903402640041e11030745020b040758014240244800980d104001c0000308259000943c1403080c030340e56540e1680550f80c0e500640d00c0a907075000e003c0e5410712929442011708842e034030290008803402d08031540390440d014407107031561080c1c0040c800380c1d4480b0902020321072280146a04409040011440c521f01010000c104000c016242c180300242407021034029900415160b2006401421441c0c1c0ea507583d04002c2d00800800750000042540340c00c907491501c500c8211820040401d4029018039980c0074407000b428451542c514503101d07400d200c00700d040d840800182c43c007140300d50018009410641031120b1034805420f51400e5160510a9490055054a100c001001c00c181c3c3d41a2984c0c07502d02c0020b00500074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 431240107 1250 431238857 431238859
    0xc08010204091d061b03070201180c05040e030f03010510020a05030d050117030c0a1103012c15090a0305030717040302061b070c14030f0a031d060a120b0f 68
    0x2150202ea2110345612402910314402c8403054030544036541140c58072801c880300f0a010300301c280003c20001c4a03900841d40a49580b0001995610405298078106603044086d1500e48080e181070040e418903200b2140b03182000f400450600000d00210502440f05005042c01506d810358000c00c520f000f00702c04204c40750310200381c9460381001170314100208030034819000002403800800c4515100801100d4030030030308d00054800d5011507115405d1813844d102c0196050340d03860501d041d07002c44141d08800c0500400a4a03504004909203107444c041058400810071030000083c44841600010b130040c84030b81c10b05240e034480d03507504029034149804d03480320030741c40700c088042108040d408141d09124a00d2034185040502c2c151601c10b865018204d4020509a50181c040c080c042078038001c0c0210110040840743d24480d81020a0704002c0300c0c040c11008100003000d4089038125030b0366442d038484000c0c0c13811030824104000040c1382410a40740d40807d02e68840182001c0d850700c41a0f0181150 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 431241357 1250 431240107 431240111
    0x80304141206010e0610050702010e0d1e06230106050a0809150c090a08010e0a061e020f0a030e0309090a0b01030f05010b071103030c060103122705040e01060302030303130c0801 78
    0xc1e61340c0c2c2e0035452000460f04a4031412460305080b0700103000d1019501d0154042e0f4426000704e00e0b540a00c000d02d0310700002507c4c203503070126096039a80780d151009074500e44540070204800340c1c68845658112641001881c0030794400d001481001da00a00365039402485190100c0a5118003820604107410382c520b195001107907070200072003072251a00801a01c142502c0905c0740f196543c103030500721520f6008010b01174000140c24000b250064014045d03480d2404003e680450002824008992010f00503400d03e850110304000030507091710420b1034540d02c0364041e5241600000000b0119403000b40b80840b0f143c2e448103110081e0348658084281801210300400035544c403592141410341066034103c51038850b020141c0d1003420042b0030340d4181500709004042d26425903580c60f0b04040b6030341e01d03030041141d20811303014592810100300da68450ba401400225038241001d002c180c6200342d4030022140c4c1803103010401038600204981d07210042c0780c101d0080301840d103048001044583d0154203258 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 431242607 1250 431241357 431241359
    0x70306090c0c0201120c08150a05030a06230717220602040807050d0b0f061203030406060e25051305030604051612030c120507051b0405010f08030414120601 69
    0x1a03000403001d030780345001741c0b42c401e103030b00f03100c2520380503911000d4902d000200400c01103040c466006280500700500240500c1c4d2481e02d5002292400d200c80405594a0340c9441e0201c88140b1200d24a40d4203920042c1c0c0c6014a2900b40000b800c8001d001104080702840340b400602c007010000710b10611318101520ce18042c0c0500d0030400c001c0c2d080360081031030768001c6010024003441d0001c07490300f1a5a102503400c0381c5039500c0c0e0200180040c003d14031904030402c0c0d03518034081501840210300c43c5115200000303c003410b000403202c60200003010440510042881c03004040007581c11100b49540d54a0016543c1e941c0841d000103206e1654440303a00b621407501030004010012407076952980583e441c1d52030b903594078815503007480c0c41c0700e4000c0c002c1104c0e000108045206100b810348000d841d420303d64644042541d07124503003140c0c03514011072204410a9070449103450f020f200e00405503080e000c04514108016982c607445544506140f060402e01c070034400303485258503640d01046c00001d50b0599 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 431243857 1250 431242607 431242631
    0x30e0f0d0b1005010306031106030402060708071b060e210313080c0310090b07050702010c020a0611250522060e0109060b0a091701110d090302010506150f0307030609 73
    0x300c402a0ba164800b0300700b0394000700707580d4480e115040c00c59401c01c52101408844070184880c6910240090ba00000700300032010100306803c0c014403070944540c41c050360500d8840c01c0c4003544507843c0c11400070010b107402d10141503a0b554481881002c0d030046800718855402d03602038950311405840f83c1c50904003820028a0107030215119501210035419119070034180c1c230300101200d45030100140481d084801141d11a803080c0302401700b2034410304010006e0013140d000294211710550000300042d00c44c00e03c000e9110400e00c00b80600c4664030359080e039210003034144d18001d0100b44c06450300905024425403403d100f18640014500d001322000c00900b134450b42e15142c120340034000c0200041c10007400144440c00c280446080100070b564220320681030040c442840c80d03c0c0351624a0395900c034104101441400b9004122542d02c0d0702c400a4181c5684c41c0c06801e40d100200810301c03500300328101c2482c450a00701141d1a0302c0307000c9035255582d6144001540180060b0b0040b000e40c9241c13045003010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 431245107 1250 431243857 431243873
    0xd140717090d0903080c07182f030a090215040303030b210c2e020309040e01051306022d04050411180103110c010203130b0f090604030e0f0d 62
    0x50000034440e041040c1d62058607103aa03030841a10080700143d0400c0b4100003045100000d03200c11583c5400b0348a01554075100d0780c034a00804024454440c0d995403006011041100608013004200000c01e801c440403400c400b225070000922114030a81c5a082000c2195103060100c01c02c90b5161000c1070b2a140c0340c4c14000c00601c0703032064841c0124012250700c070341c030b51281d00c1c40761104000400600289401d00c0900a0500700400b0110f184050141c444d64041010001c0b0400021542e0040d0b13100c5402c04200000e0b900d0842c0a088582d24280a100c000035800100164503a0810805030340c2d2a01090a0900003902000300000d0309c01c3c14401d056400c08000c020012201e045405010460f00b4004481c014400c15480019072981a005110194001e40010030119070350300ba01401e054032904d0b86400ea0303000b280c402081c5014885001d04224008803e0f07500010b03543c0070b0b2010342c80d160071240c1d96488058000303000d2050b142003206071036450b039905030340a6070007034202d840c1c030340c103a283c0262 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 431246357 1250 431245107 431245127
    0x409031b08190c020a093b0114160c0c0518070206070309150218030609060603010f05060d110a090204090504020a06050f071b170604050f0c0a0512070b040305030706050109200d1407 80
    0x6565420100c80c20549c1030f407036210702e000311004000c00d041010a00402c4d281500111000c48600891902c00500d50303a840d04084042018000c90700032525200c440282403890050102d818103207000c23400e07000306003d40000d000741c421800d8010303030300c8040007224000381d02c0c0018040c0c0d2510507541003240346600850007a000e140706500900c441082c003803488050f51012130b161500040c100b6030b240040b46203a50180d62424000d410003800c0c50b1202e07202d0040c0c0e405a0802549240c444080c0300460401c4045040240030511b030160400001d40e984110318424000c0c05012803c02511040c0080f80c1620b024006001c10035056650010104215803510011142552240294246800c0004006c00d84511241e001402d1044a604040807c00c0d452050b014415031481089004a001000f0340014801707540144000c40d05d9081e9403420900350740050300003600301404d1940d0084c00e0320100d0000c4c540c80d43c04d990381039101d4001e40c1001000300000c08005035586804000e0118880c0c001c54152 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 431247607 1250 431246357 431246471
    0x31110020a120606031a210f0a0209091b1e03060103060f0e060c030a0f020909090a210e06070203100920010c050307020409031b08190c020a09 63
    0x100400d0340e122130a504503403442004808105c1450400040c52a00a4980011000c09140e00504038400042203141c01103030308031440385501070f80c1e4181c11352404000303856100484400801d002c950454030b410f40e10745401c00003070192104503650110f0b082030f03020b01805801c004c2c08845240d03940c0d06240303000d096003100703c0c040f980c07400034840d80c4940d000c50441d108440f0400014955203e0401e40300080c4140c100b02020550b0030320407025103999242c01c071400f452400e4010100d071906805c0038000000c0d4100c048030b508500c658140d8802d41c128040310301002e401c688241e100e0001d800403074142184951070b5000d0900c3c0003071101c10410501440c013030003841100702035035412000c0c00559048440c1940900709a206200c1000180743c1034101ca14014460303d44450b01d5008088540301000f1a59003c4401c03000100d4094104041801d0000c01e072a01c07490407046100c3d02e5004548009014020104200c0e203402d407001200040b0510410000c8030441c1c18048002c0581090900c0f400640842c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 431248857 1250 431247607 431247611
    0x30c040f060507050c0118050d0c060f08220212010e0d12020a1205100510050c0d2a1b0803040503010509010c080c2505030702010f110703031110020a12 67
    0x1c62501d20030815203060315400307001003503014020030065884481d1680700054030740d038646010403c0d413102658604aa0700c81d00750a8589410310402404140392001041c003085402d40030050204001c805500b404da040740801c001c861010300101720440d84540220705150700342440005075030400558000d410007556104c518004847c42070b5002d81c8240d5100750300160307040a8807214200254401500603c2e034100c40d22200d6070710310101c3e5482a40264040c0071a10200b6485034086050101c42101c0116240c451001ca160b01540e01661010b010200c00f4081e400005800700102c140e06940703003005104010000701e43c0c03502d100d60b50794814014070340a5400d100208070303040b6050060024060b41511405a2541e0b40c8080c46040e030400041d10003010052032813455031280884c2148420750007040034503610001400003401d02030340760b081541004130800200185400110b003d105690741880d2401c21054451007046c904503200211204031840010b100e02030a801ca412080b140d082a501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 431250107 1250 431248857 431248859
    0x1303080105120d03021605070e0a0b0301020a1b1b12030221250605040c051008070e061617030106080a0209010f050c191b05091005040e1002030c040f 66
    0xb8009002031150605070150b10070255018104d00a0b0068520b10410102420028440f46c036102d18250240c0c0c80200596800d070103000c0031584070b01400995078815402940b410344180b000401e40580070300602c00c8221621400d01c1008010745000c1c0441c00c00d8007038202541c1c0c480300095118907401034100c000d031217020407500c0c3c0c4c4202c2008420009030601505802e140401a081c3d0008000c09c0b08042107044240040c00003841510540e4011401103190404c1241441c0512601140024414043c408104200700300310380c3c800c0f800f14a007842aa0069141d0b05081030b9821101c0b11480010012080712041c0102e000011000d035040b24040c0c0d98081c070940318580010100d102e86184107000071f4001d01d65404440c0240300411440e003102c41111400d184402c3c41040c18200c0000480d4201c0e088d001030070f0010344100003a00a850100c6640751a41410380c040c5003080c02e144100c500070381c4c03140741d422051581031107100703800341c000a800d558a25000c0007185099201d801128480c4118840c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 431251357 1250 431250107 431250109
    0xf0e0f1e0f0a0201050a05040f080a03030b0d0f0212070305251d010e04110907030e070b040608010905090703300806090414011509051b091c03020c0402031303080105 73
    0x141d0462100401d00c0508215500c68004503042e80c01403580605100c004c100020b401c01c8082215002403080201611044025240080c10f640d01d43e851640320755a40840180820440b1000b1500c2560484803981c41c001440f1040b0304018507a40080c05600660500c55003100281001c014444012125000c2107900e5220f00000c0080aa01e048034a410307550040c040e41c000c0e03141558200780551541c0030140c003442c000507108981200c8000019484510301e002d110700c10070a61018211094440703007802e0078064014401302d01445000421501d0f080820f010a405101002c040d641282c0742500718040c2110100c14204032032000440034900c081c6d00b040032407051092a0007004010b000c4c1a0703035201c98032403103c5511140c500f10401d541e1040304494840070400003000824150102003420314110503402e0111a000c0000c03c2441020412604e0a5a6a15442c40f0f140c283e21043d40e44080c1904007207141001c00502c15402c18400014031a802503e00c410281a900c02e503640c0c0e9150707880300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 431252607 1250 431251357 431251363
    0xf02130e0103050304060e1801030f0209010906080a150e0604140714060f21091e0a0302120d02040519080c010c050706111504030e0a080307080702040f0e0f1e 70
    0x440b000e001d03038206000c1441001d1140b1403c503209440100350214400c14140c1c80803088001ba4002c071044a03407803020804500300722601600519100f1410001c1c1031034034000e2a11585040c070000c00901c1d003c01c10b44482005035102d0842c0100c44812648e03180780030b00e0312a00c0751b030402040940d14880e10200040000c5543c0488000c01805003005042c45c0901c0003080060b0400b1002d0070091000c00c20b21402640040141c9100302c40c404010510041c810300710b8821201c941858003240e030002c0200e940426000290710161712541c03080c0c503a49440c2805010300a0195403c493b40c8001107042c6031004c0c40000c81d030401550680302c01d0301e01c1800000c0041d40c40c8014413000134500d40003444104001ca0140888418811044090300c0080000340d4540d0f005000840741100403a045580011460402156000150070050003c40ca4900700d030704c0c0c03400c4c00c0c000c0210003441346d52078405480920400d50081160a49444226600071034001d100d1038a40d0a02550b0041d5100030321052002d01c4800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 431253857 1250 431252607 431252609
    0x60f11070602031b100e0309010314090601121403070602041d040c090b04061d010f06090815151003050402030c041404020d30080a020406210f0f02130e01 68
    0x5030003c41c504154403424107010701800c0664110344c052a040c90b400c0c511103003da080d410701c0f280302955039044100005000c964108940b00f403d001e26008015040390002200c0e810755203c0c82885000c420f040c6819089810b6904024081d804042192010014030360040c0c0240c2d41402491168800030000c2441043d10031900608410103441c810850604594040c0101b0b0102130320100c0c0503a111070009012207105945050203116450041205626001d00300c1c015048601e0804100e91829031110341c0d8421030171076141071440c0740d0080b0742c030f0ba200d14501658545c400f610001ca00c040700c20020b001410101c8059029000302031130300400707290a1094551202d0400d40c1040e09486a400b8480c440041200c01c031030394000400c0e1416078541d05194040c10100701149100ca01c81e60760030003000030f407010b492020502d00521040c054950003906205078034140260820020440540200141050b440041030780392030320980840b1110b041d0000c110310039003202032804090343d4950601d80e030502 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 431255107 1250 431253857 431253869
    0x106050909070c0203010b0a0308070606090506010c1b030209071107050f10080405010212040b1006080c0702040b01120c051201080c090f040602070206030109050a05070f02071203021006060f1107 86
    0x4501c0069445800340302d0003110140060b0000500f0020369010480781c814540042d516608040752440400840c0c3c000c0401900400100380003904040d000039081200c110401440c0e007507114013100601219040d0103000310780051060800b800d14041c0584503090030401c0b12090301030520b020905090072400031520070b030054034141c0080b50b100c900302c1c1c601d00050300031540c2e95020000e0075050515929000d0040f4050080c071003440c14880e4600c03504072115449002880300c100e0400015418000c1522031142cbc05441c0490100c0c100170040790300601020302c0c000c086281540c0d0340d4034a6403000140c0308450080305180381698907905940e83d81c1e1090402140d00041200004060507580b00710581c01c541728041c05420008190300082150300b090b04103450303882da203004103c0540c1307140c050a508030b5039078100301c54407480b07504000303403911100c0c040d410440c2e0300c4103000010903108000d001440d02c3c103c4000c00c000c0f0303103460300201840c15040607180042e000d400b5103101604042054000c03100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 431256357 1250 431255107 431255119
    0x6041802101413030503040816030c0510020c101d0d0b0411030a0807030203092706220f1b0212250b0a0902130903021e0a1403030103060501060509 65
    0x80211412640140788100400303641d0300074032000c00b100f0400e441c01e00c0510311420284d901ca60422502c0380c9000711105088541c1070300b00a0070030102c0c101c52181f20580c0d03c00d56024503400401c80701a4035140451b100d05410214100380304040a40c0f001c010003d900c00040f20880d003400b5001001707070800305104081e103c1c1d03000c4c5010070b000590050b89008146400313004d454510b40d0544481c40d041d003103044290b000da0400142403071145040381c3e08640760701d600945c58103150340c400c22081c040c200c010880c601800b200040c41d400204100040e10282100490510a03840040380302000340c5143c40b60f10181348808001408a140081041d03001000d0080829013014610040007864640007040441d102c4412407507a40403a8030314082d00d102e0010110040f03205001d91061000b090b4185074501d042503e03042e1090006580880c1c01340341c94040000c04001503584540d05810715980810060410b584510060348418002c80518100c5e40155003c02c4640e98411003070f210342c42040480e46d40301d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 431257607 1250 431256357 431256379
    0x60e040b1006360305060a0f06090204030302030d0c0905040204032d020108220f050606010e030c060a05070822080c0d0f0b1306111b010608071211060d020306041802 73
    0x20351101d80c00e8101c1e5102200f00030303440340e898071260300303000060b54803202064480103044503082d060b0141c0c1004145054003107103080d146480003510703030040d0304180200d00e44882c140c1c01ca491140105e82c3c080c110082085607116601c0c54080400082241088110030003154002081d00001204900c03654060b100c0d035846586580c40d001040131a0880101c00301800894071020804802d4002081c61003000101241c0c24884000343c00e04100c514250310036446201c4240d2140c58032015210665054200640c64070780a03d8200454000c80c443c1401065514070b030003200003000d9000b6001c8404800640394009a800280a00124540006017060721042c0c03030300000032606111a82d101000003509400c1c186e042d5a8001696440130100c1d65403080400d44840d2000321115035584003081a008000103458240d8090701c032410340c420b404850307004ea4520014001d0040100c00f61a40c018103007a92181c00144840c0290000e580d0280a42e15003100040700d00e02c01440328907400e8000348400920 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 431258857 1250 431257607 431257667
    0x1b060518030706092105010c05030603010b0f1f050706091212051b070809041401170105010f050f01051204150b0d0c0b03070203091c031404060c030e0103060e040b1006 74
    0x1c20703403403000740c00071204103228580446c1c002e1161040070760107551005c0c0c1d2070420000305400d58461410301c6208800040c145011a603408128220304e00200d134501c1c01d56000d20101f550103005030400604070908180c101d108004181d00c0c042121442c030380304e4060354821014000226001161010705000680005c004102c51032030240102c18411520750f40b900345048080703412f64090f000010800e08c070302c0b001440441c1504c82146201f00c0d5003802000250b25040d9541c202540500c2064041c2c03241e40d0340c0001c01c0c1d100f00c0c210b41098541000701c1c1c200741080d00d00071101051840c05030b074140b031811101d0401071a001c0a0041496000340203240447e00b010114029030340003812080643c403080001d64650f0b01d42c00f8014000440c0001c4288101c1c01c1e80c00d000d040c0c40458071014000c43c6080005102543c0c1112458013619007520707001c2100e0f8401d0300182d00800311341d0001d4071402080030070401040141016a485000054000b030303c3c03150359110640c0d0b5101d0300c1c58100740e600317010b071120b00071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 431260107 1250 431258857 431258879
    0x1209080709051017010902011e0e120a08040305071e030305031603060f03050606150703023408010f1103070906050313060203010e0711060c161b06051803070609 71
    0x407103c81195034010a40e51520702c540303202c3c103036440341080e5114007a500c1507680003910809109000303400d221200100d401c0040030111100d441c0c0f40b045d009123521517403442e000c0107240c00f04c90f40212000e5960b07450741403c60b0342c0c111611592030b10400140218882100c0791501c8421a1360640341c4034250b4403509171038031980d95809080010036036075510004892002f041d040c030046000d03c000d4000c41c00d00d0000c1c000076190100030000350303500c10051800000d5001584008180c000350000400c44060000d80c04074212120b0072000990f4101e101041511040d480605542700715042005042000c5580c2601400216420400309140302420070040340a500195400030741c11aa0781c00c41910340e0b0765074040703030804e0f000090005010170800c02d002d50800301c4083c0780c080301d0006060900d0311100009491017440c0000102150040c100f41c00c0042a480700b01010b20891030607030202c1d80f2400024a0350700005210004c150785920744d000d46040101e80385040d00da60b9601d4400d4241005000700d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 431261357 1250 431260107 431260111
    0x110a140c121b1b0306010501051605060106031b0c080418020909070215010b0c0d030e010e07152a02040c020f010f060e010e070c020108090f0601080703120908070905 73
    0x141034001c0300e80040282020200800d4039060881080116404451282d454042468035001102c01003400951080c3e40000b2010304540c001d00e03001c0d50740d000b2040072802078903142100034028031034480003095003131309904140f18001403d1041000c002c0c0d4104200c075104002c0ba0050b02200d0704100a000e0640403465201c11003221180141c903040e00000401c1030404c00322030200c0160801c4070810000d01511110030b00600e44e0803451414080c0d1007e0740d41c2c8540303110001405043e035175520741542c2407003900040c103e0210039065552081d540c401c20200c00b40e00c121100001782c00c0300240440500461500004032040412202c15820b5603428171005100120041c0d05501c80c080762400e0700b41d001d014041016090f807001280d000d2510078941c10480c01a00941c2d0850035040411032140d5000070800e82035602481c0c101e105460754215181000940034005c01c0c0d40c0540000410010310002d50041180e00c600d5600114041001d402c80d1060311902a406842c1c100d07107030803c1012401d0704416 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 431262607 1250 431261357 431261377
    0x8070804021014040b030109110703020316030309080a12050702010c0c020d05151906060c080a20010204080f1005010303020d0f020304091d06013f06020a1101110a14 73
    0xc40060340c80440e00c400c4d03006940300c0700e5000000001401401c11a00440c4071068110180506213075041da000307900c902030b4900242000300303c03c0c10001414882d80000400f5500480c5060b90307038002c24001040c81d01900919800c413801e00001c10007540c4140f0801800b45404d039240b00585149070b0810500035960300040d1140d04c1000c205401d1007035040141c9014100c820002c4d96031440700c021030b03015070300e4541c0b01a007400305c42c1d0400401b00c1d60b440d04541e002030030344c6004000c60b58860a030010301c80f1035030400070142d8408100484c0010000070026820045142140e078102c00c030b0040481a1a800d000007030058000c1c48100c2e80585c01076205030541c16207401901e003081d488803010f0b8111100c01c0300035103d04034240510b41e04218148031441c0901000a4010502a984103110300404241107480e01c4d00140351400b0703400c0e0b0b40243e01181c0084d030f1110040d5981c01d0521001440001455035164465107465909141051610219100c0c98460789411108912030400d41c016500507101d05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 431263857 1250 431262607 431262617
    0xf080c0406210f08091807021006140105161b03060b0a060504051c05011814010606021c02010e1219111009050a050604230c0a0506133201080708040210 67
    0x1741c02c0300e9840b80104c1c4e01c8440c00410900c45480c3c8108028500398400b18400519807400505122495082100320318030402030174115510808104140880c2e149024098400301c240d101c4030928940120141d01200d000780b006010a160a00801040c0d20503032040c0320101d0742c00c01c420403260820380151041d9080c140e28080482c56141c5585007540c0c1f400c80e61005190300c580d05a010010401c03103034440e850583c1c0c02080100c0c108400030b5078501d6a140a444440101545900700d04d20035000f0f5400f4650f02c50643d030b800101742c0d80c42e50058000e0f1041c2c80c010204580011580ba100703980d491f48110000c4006c20728101c140400b00000d02701d694069410740215a08800480d408102483c002c0748590082000c1c880c60441100c00c58070210001e10035034004a9aa198076a00c00300e1074001c0e00c4080340e5a41e910354019140c242c1c07a484d141d000603080b008107000e1440c2c148207400101e100d1000b094000710b29180c00401140e1801088698002081d4004041005800d19600e101c0b03540c0b240d070a007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 431265107 1250 431263857 431263867
    0x50a140105160302030901030e0c0108070809030c1903020f03070f0219090516020c1c06110c0f0c0118060c060905010e031204020a14090406020a090f080c0406210f08 73
    0x82c064050b042c9020980250b07000003072908403542d051041582d00c010740d001802080c012b40000030031940002c0c1c503001c00c200c02c0c000890b400050900440d404503051104841564082d412050007155000e00154054000c0c00700c40c09002501000300e605999004250128074915603081010f503901d26080002400600480828100110710483d8018040440900c50860412800a04c0e103407107a00582d0065680320003445c2c2c4c1281205140300550b0384500b02003040611102c02c082c0c40d001d1148075202030300c104070402c0d90221022540020101083e6909620345494a444000c248440e22964000801110700c01020032000d600003d803030b520550000c164849d5800c1827501e10f40240045111050855042c40708510b48036400c1c00050001010310072108183c8000074002c048014006403115400040c090701e0140301c1c0104101400f8010f501000c2d15840d0000166520140a081c0e8001ca02d030040c04901240300c0400b5120b0720034603441820440106603521140d010181408880f1072100f806 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 431266357 1250 431265107 431265127
    0x30c180603080c1f0225110a170d0503060a0909050705030d0527060306010f020c06070b0103062a1d1302030405070e07080103060905030c0f010507030c0504050a140105 74
    0xb00f8280590030000e00a0f142101130781d1a0b00340084840c2c1404a1041010b48080072010340c0d5540c1581c0340b031580d5460b14402e8108903040010031100242d1010207602c001c1900d00207508061641100c100071180515078419041d50b06110944216500c40c2807070302300700a800c1c025003007403482c14400e0095945050352100420314110080c246203010940101c0c0340b03040e01260300b5503a5010142e070085d000340f120060002c14024400075092070704000d02c80100591042c000c1180400d00c00018121681d500d020741001c80702003100f8001200c0d41400c0030020f41012007001080c03481d0345e00c0307a481c0145080e494041947d0401482c41080b004406e0000060004e0b61a41028441d503034070383ca005030381c92600c1d25029080800e540c0015114038040018018001d5002d0704090640e948000001034502160402a2550213844001200307440f800c51000c54940043d08080c0c000d0155031814402204c00200540320b0340100c1c01420707044511880c0800080c0141200307403000d410181050b1f481c080c6020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 431267607 1250 431266357 431266373
    0xf01020a050f0105060310021c050c2701080a050402030d081005061b07050d2402070f0c0501020706020c0d111c06090b071d130e15010512010204030c180603 69
    0x3400842c9941d43d60f80810019040903c0200c0102103d9441146051400c1c0034800100d0701095268410690701c07400142420407050488040240c18030740c203e0040100c0b03161649101c0000390140c0010a140c020a00a04003405010f00880d80180a46000d00314588100ca8169009041c111040e07541030000030f00361503000081c0802100288084101510b80d585240b40150740da20113801340503654603290200b80c040204c200403442c41d92901d500103800c0302c5104083e000701c0b03101616122010300a0400c103e045000c034421140700b80c00707540c40e0300d075181c00c2641c0750811441c4440c1c00910f07902c18480010007417015103001030001804900e091501d1030100c540985c544908445580d0794540c40010310600b0400180d100455203414411441c0c110401001e600400038001d00400c1a07c2801440c1c803c42d8000115a13400d00007150301c0005841c0c040c00302c40c40c0a2142074010801d00074000c410034018000c0320700356a000400030003c140342c50143c00d02c00107070355411408140d4030080400010491 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 431268857 1250 431267607 431267623
    0x6040608060d021f0507020907020f10090c0e01061d060309031b0115030312060509060a0509041a10060908010506061b0708070603021b1b04110706020f0319020a0c020f01020a05 78
    0x6584a58449086d4070500c240703958064041000d560104004516010300010783c3c2503528200031011900220341e2820f0302230503540d40c001c450328149a00010894951010b820141400d6540003020345076042d206110030340c4400e88005010760010404154554042818144c00407403440001403240c1e4102a04524001c9581003140001e800c004182e1411007075000d918040d100489031030545081080000301c0f001c50b98442c0b140540c0540c2c00003400e210f50140600703480403080790300a400e482c103c501d800100300b05005540114800e0700003c510207005119051007814080c107664501007542a050019094080042040744503a0201140031070003844101c0c02402503440c0581c442c00007003e00d08501c9005040b17400070754010000380388103218041d404503000000347c800066202840f14410303003511401c08090501800000c50380454042c6074011071061071009d400f1480307140c04669100507807255070409000100b118210402510700340080c2448404140111542196641e8610f8105094 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 431270107 1250 431268857 431268919
    0x609180a0803160206010806090304060c23030d0e030301050d02041d0114010312050310150507020312030726060603280b01090603060303140a0c0203120d0b06040608060d02 76
    0x1103c20714010507a010420540540400f20240a8070b10b801300d05d00c0c3d81d0b402103100e132904101180e480c4c4001c0c0015540b00e10390f84a41030050b6a000802140c6c01c5540e03074050148081010714043d01e0f03100d954808020359046c1c0314003c1c40303080d07803452940800014049058689615940310481015620803d2048d880b8450811004c09410342c50345c00c1070b00082d00458100000d11204004000290800701d403100b060342c01d40e140184103501e10b504c00302c2d440e01070404001d4051180d44007000f4503c4642000e58443c04903580c0b5035443c5110301c8540e844110030040f039450741d044075001040e51442d006000c0d640c00124409240303c400407200040c50b03d49443c6004031700e65980c5c0c54040e9520f580c440c00c148054155030400f840304610b036a500a002c0703001e00903c941c001c5004548a4101b920460000008a070001c046824894481c0c0010341c2c03e5020070003410380c1503e8036000a0703040c2400819a412581940c4030b4100c0743d0b4845042c45030100c2c40d14412039025202c80b080c40001501510b0340303564101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 431271357 1250 431270107 431270131
    0x80f010f180209060f0a0c050c1c02090a0b0d0f0519080409091e150b010503060303070605060a03080307050d39030e010e07080f06250c080d050a140609180a0803 71
    0x11223030030454201850b0000c40c40c010340c0110703440f0320b18a040d040502c1f640b03581592081842c1e5254003000c17000b00302d100140d039840b050340c1000c001803046038005040100d0049080d90365100c031008611880c40301c401c0d00201502c1042c002080a0304040d44200480e03800f49141d039400c40800110781d8045c0c0c110f06422150450240e42a05171410384d0300c10065411802c0c02c14905d18100b103000640d42e130084860007481d01d81c940c070001c0c103e500c40700751140055501c805000c0c2c81c1d0501c100d01502903042900100b03842031030700844505110820050642c00c84054511400307070500504402c0307406004510000a15440d00d485c044190000d00c0b400f07a1450181d0301401d0814103000ea4281844e218602e218516407288080c404c1c924492030304001c074030301c03489103859150101840555811510100142039140d01107030038411840b058005601c100c00380c00c2c00300301035116015a1400c9507011344926030040a000000340c00d6100f44402e0007080c501c0c00e000c46541074003d6540440544c81201d040034081c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 431272607 1250 431271357 431271377
    0x30d0302041809020105090f010c150221130308090f1209040b19170f0715090501020607120c020a0f080403030305130f03120608010507080f010f180209060f0a 70
    0x1d100500c0e038903400a04800c00c3c40350083c81d0300000e201d8056805c032580308030580c403442e042d1070307004050310004a50300404526560b548090480000e400c0b001d801400080408100c480704030303a8240c442c0c802c0710b0f092000000b20460303480803607074494002c00407c072601c58601d410110361030405c815500072001c2c0c0001580e40301c0040178001680d0340e801c24107010b401d50103000650002006003040554015408203900059410500c0d0301c0c0c00300c81410f0540301c0c02001e00c00b00314040d00c400202000c84064448d01d001d5035680004a80d1105d00725182c0d0001000800140f10481c195008410001c01038070448100c0c40f0143c1350a013400d041204111707074050300050100200b6416004242d40041d0480039a030401c5d043d900d8698043c88003507002420004020700f1141d40702d1050b40003201401c00b95001b009989030007030300940808401c0e5081ea40400420000040601c0381010f104142d8100e1802103195072074581180010390072101042c0c2c4e01150520101d085150b0940107040460510341d00c0105007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 431273857 1250 431272607 431272619
    0x50a0b0405100c021906060e01080102120f090c1e0301061d010f05060316050d0609050a0e070501020c1c050609030304060e150402061629182109030d030204 69
    0x40301d60980d0142090410a82043c0039802042c4800411030302803001e0705001ca1490b000c0300424440d003214044032840030003c160380e01c0560103400b000b04403502c00402c80e10341e03000f00003c003241100d10b096940d001c4041c228040c20309003500c800800480e0510884c5809080c0002e0035500c03250007400d40d92002d010014a90900b4143d234900404000450703a009900301800300c0c68602c00100303842c2503034082c00346004070184920304031100074405400400400e901d8000650240006031001c9a0450031b00c1605141c1d5070001c1541070031a10160000c0c11410355a0052104040d0f01010070010184101003003c04038030140100e41c41050f25030301565130ba240600d041030844540b4020420664054403048030002c1400a4030354006404a81c52a110604820180500100d07188010080c01e01c41201c44031115661075103100b00310251141075629541d00e6851400744002e10800300c405d9010710306407650030404c00d4040703030041c01b05c4120a01e040d1889000c80d1400001580440c00680d0003e020460 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 431275107 1250 431273857 431273863
    0x3090806071214360d0503010513060e01051002010e0a05010504020310060305030405010c02131a011101050906041b030c0303020618010b0f040b06070609060e060f071d0d050a0b0405 80
    0x980703d200804010500b400c1c200d2084440003100c80380c0707000c44911005011100f4000c80c1941d20208981160b144030350415008045070800c0c4034690040c1165407141e1101d043c1401508140c90350307001103520582ca06020040007840903e0554195541c0d0303086c4c0e46900030140710b212400c6004400116840c14240706041c42c020780000a040810f14014090001880110883c4c0071518246450a0030100030300005449807840d82c074181100b45031800150164001e140b00c451440e100741c0340c40d079110000c0540182070312400c0742c952015410100000f000a0740e0f111b100d07908015545103002c119a26a951001c8024a0f600240d0241c0e120404118010011072050200308500c58001d1101203114400325160300901610b00b4070540c1c0b244d840000a403110b800f50790159030080010b024411560a100c0b004103843e8038094110b00072100050040b00048074018003800c2c5540d10007511100030310090910300c6020044641c07004144141801144c4200049040e181c00f901c1c00c030400342010316040e49 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 431276357 1250 431275107 431275121
    0xf0309021e040f110910020a050a17040e0a0c090501090e01030b0717090309040524010f0315170d1e050304020f1e0906150706020f120415200d0207030908060712 71
    0x800c5500223500000000c001023044a441035000d190050f10740224004d075401c5000d02e0f0020385414003180300f00a4200201e8122020b8410662070700300100c1c1d200e800449072281117004004801c102400100001000300309000e6200b0781506c1c015075021400c0c44217400080040d031701030905602c045011000c5103010712540f85c002c4481d03817160705c800f030410f246c0d0842c030608100d000303042c800e03a19411041140131f42c00441400411045506056480714070520741007040c080441110b00c104600798194034000c2010144000d80311610007600b6140c0c000856a03275200501c12038004505440714130f40c588494101141c2c00c80154066405011114107020380004002c001500c1915000c41412011482504880301142c0000c809aa1082000c148810703522402c0400002040008100400d05c6402000c5200103450144180110765000f00c8004030134074048580c40d100300c0c00f04412485005c00707a0007041700328400d04084400030340c1c5544090600404072814004140e240c15003400202e0180b00d402 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 431277607 1250 431276357 431276389
    0x31b05091302010e120f070f1208031305030702040906022701080c09030114130201020f011103010b090d0501050703050114150318160f060f0309021e040f1109 70
    0x22030600d00058440008021104040e0600440303181c2c001c426200c0070704c0807070640600011a00c1d078a1400c194160341c0c03940e030b1058003074100190102151800c000c128085003103402c000f210b411900d5130001c4a0065484040c01c88040c48200716400058465000b4004128000c0000580f911038083c0441607814074003004804600b07254882840907a04408101e80013000081d0301078803441200e011900603c0f00704819032012010380204042c2c0f41c44801c070468070034400c0c0c2c26150300c090001d0105081e00d200400480f65507009000601c1441142c1018240924004104524664440d112542164801c0c0c0e9001e0020740c4600c018483c200b41d080c0e003184813402c19200f155080314004020741c4c20307000160071400041011b0351441c08080342003202d0907804041544032440740359070fa00c0c100d40e1442d1604c5800c0c0495005184405454002d109040e800f07a00540702242c00300610188025013860075842a50190b80d03040c00d5402401c6901c01c0c040c00c03565154020b55908680c5003001601c2c3c201404078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 431278857 1250 431277607 431277619
    0x50412081c0c2708060f1b030f0f0402150c0604030927020c07051e03010b0409030c02220c120b090613050402030a02040c0f0801080c0a0b22031b05 65
    0x1a4102990000f40c0038510410611480c3c03104208a02c2040c8240c900c0c1e100d20320341d00c41d02c000d03c0a900c051010075801940100924101d8110f401c0700d41c030303041c0011103070740c0c40c91004240014014a940c1e613000c0c0e8031620040102141c450500300c3e03145c642d00400000351040e0b001e40e0812003015000660400074140001c1c10248100c0a403101c191984c02206c4204280c0d074011418100d9508100160400b0b00070051288803559981070118a030000640e4004d07101e076081080741d4065041510500c0540c5400d9a00c60b0141d06854090003980003c15402e541003203a040c10f2014502c0d440d01c5044a040a035076544a102500b8031550700030389a1085445206e101c08500340000795440c0c504407040c401e10311a0200c0c0d555a540002410184a8440a50001e09210b031081c00c5552040a20007210709503110000f407640c951040594584101d05200e0f0000010701b801e000da1501240548508450b64481210481040b0010310b62001246d0044031501c0200b00c40c1300c500004000c65a0161800b5541 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 431280107 1250 431278857 431278871
    0x5031b1204080c0901060503161b0206030c072d03050a0207150c03020601092a03020f0715050a0504080d0b0a05030d02010606080a05070f1b1406090d0e06070201030507050412081c 79
    0x312040327040b208440e0001d00800b0421080480030003c0380c0c01c20250028000c23038503894010465203050303020610854452913200c1075541d60540c40c102900000204110105034034204e5070303085c1c401c0d520000307036034040d841a143c00280d001c8a62000c070725100c44955031010045014640a407074048103812a000c4036061842c84800120304d030030880744d50300c804040ca0f91903110b0130314203030000c0c440c07201e2440010200240d10414032120704800e00354603100a6003000307135640ba00b4031b1400301e8005480c01000030b072081100400c00203040d0000f90728004010089010150b44900107803504090080c044d0150351a40003c00c00c0c9a00001c0d00e0780d000711900782c14001c601e01010002e004000c0d10f80c800050101e006015414207652503001c100684e4018000e101c0c0342002041c1070340e2110101c031110b0040c0300708001807039814401d40110141c3c0b40f000e4580c1d82400c22650041d005000000c052170104031041c07000082c05a0b00000400c1c442c3c2c085c0d16090ba0b10039184940103140740141200502c01410119 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 431281357 1250 431280107 431280121
    0x303021015030b1b040b030c0403020a08010c0e0402130f23090f0c03070e03030d0e06131a04020d1502071b29130f050406050a0305031b1204080c0901060503 69
    0x40c0294420b82c4d200061689034182240c1c103819008a8121035900c1740c01004003c6800140b100038805d0b6402102d00d0103026039914481403d903107100e46507100103100180850194109a0054503500385a0385202c880a51104042e1003002c1d0306501c081c8021000107083c410a00c0c6400300000b0382036081d1103903042494080303c0c0349580078000e8400c02c20300200100056551707116007107a403140361005099a03500d64400d441140079090102c80d1070118010b0304040380c000404d14181000c0c135039000700e0340d1880c084c1c54a4203050040e002042030380c02c00000c0110b8000200812000c014010010800684030125401c210000d00b04031203d5080c0a5641c030014030220202c0c002082c10340d900f1038120003083d400c1c0041c07403030709003c2c00c65100034090b210800407403038607580c00341c0205413282902d0070042c1e155103d0800c92183d250744009041c0c1e401c02c025081a44602d43c4a0008000070181200d1100300d1880180c0d14642c0a94081300c41c0c0d412004040040d45841c0b000580180f4462410b2815800c00e02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 431282607 1250 431281357 431281373
    0xd0f0b041506050903070306090b06010207090605031e01022101080f0a0b06060c1606091701200c031c0b0108060405090c040c09050d050d0807050c0309010c080702040501030302101503 81
    0x10260b02e0512030081030800c0155000c000b41c0d4083c2d58000c4050165504078981603954040560358030b40980129030003c10380e000c00c0c0c400c0c5011102c00500900c11400e4607040709010f03d203103109100c1c2d02d54081000d94005000c1c2d001036119244003025a451561424042504000b020340f00c03c01c540d0050014200854030540007035800050403038225036a0034002030f403503141c030f01c04500000309501d00050008400c0d41041c046400c0306e03007035000f16142c158404640740c01c8600d56801e03000340c20004401041c00041c0c00f0f001e0082c00c3c0341d540c1141d2901c0710001890384404130a225a100300c03512408120f40c030703507880040c0c55040201510140f14138200301006030746401230900700303a0243e55904030b0300c4881c600ca41c444d00001c08001e0101d0b804200300d428019140d100481268003c07810031400700d803000b8803520807201c11100e240040c60410a90200450b80518119003d4440c5042030102c0c00250b661440390900962103500142003120f0383e584101e041c0c0e10f00300b52500c0081064941000414030702 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 431283857 1250 431282607 431282609
    0x10c020d110703121d1e030c0a03080a11390105070309170a021306060e01082a07021809071703030606160803090109021908150702120d0f0b0415 64
    0x180c1850010f01c8081d045a102800c03840030342c01d030b0003a502c4030442400d406d1180340718030034403054090f281000503407003d12101e4800e911008109800800c41a070041e440f822159104803100d1080e180c0040240e010f83c90b00304000750542120b4800703141c5141c0c0d0301d0082c0d0036031404580c00703081c010b0400240f52400783c07101040f80300e80450844ca2142c05e140a030303014800680d1241d4000c00360720b040c2845e044002c004248a001c1d507000308010b20580d00c910360103680c03940e00c144071b0251801d504900076a02c60550b107007000d03a2401c413500d051040d0801651f070908400f81c07412001107a03040518000d0700301e0b440d181d51540140d0b040c00d555420144d4001000c42100d61086007501c00365034a440e03110b0a000d60104030720010384203900c00b10501203200e1064101404035802102c1e0508007541401c89540380c401c452080040a0380a80058000d0404804079140d1110550041d03480c102240c5a1b400c072660300065059411075518226407908918038820400d4240b4144d50070003918050900f907102c4d405807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 431285107 1250 431283857 431283893
    0x507081b01051e0421050601090207200103060b0a0206090d03180305070c05060c03040906140a0501031a03070603021c06030206070209100f0b07030f0c050606130e010c020d110703 79
    0x150710b602c1443c041203007114000c205108007401d50981c201c1103150000090002200c5501840000145807101c900a0360304146e0403c410750506c02c1d511000d540d40c1e41d000f038889410f00d500c84100055a00540c07001d003482400b150098051441d141103091b040040301d40b80001454544414400c4038004074009081099040c1402651111181054001107250b81c0c0019880700c00010b12800b40038021001c0d100303e0b10521414071a8035162601c80c01d080e603a8203912600b1040040b4200b00700e40c8207400c01d1460480d41d11010041d00c0318400130a0500c03040da081140401d400040056041c04445190004844445400c004050855000555610500c90007070707c590301300408a10602c0395040c45a004080c1941d00800c2e259035207088000d81d0b049480d00f900462041d52140ba02c0340d0189a003071612582c483d0261400b0340c9c94a04201c1c01140c82c071085151203036a29030401d1501001d20803040040a42c0d00105621076480000402e421400c1c801450380340c000e94000c000181c007010350305843c846 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 431286357 1250 431285107 431285137
    0x521120610051c060803041e060201140a0b010c05060a05150f060406050f040803070308040308010b0903060628030c0806160503010902030604020d230a060e04120203160507081b0105 80
    0x2180b078904000740c00950820207140c000010300003107623440d400300000c42030001200005c04660b101c600b60b0803107003c0e10031071846000e0840000c000d81034a40c4200c4410f841414018151101522000d1420200311085540300d03546009200e1003040380ec5070341f000c2c3d03441240c00f5000a0814400324a0f00d0080340b14100c284240801d110415007412400d94020b041d9040440303031070310300e01d05004008a9048c0c0d010303008a4182c50010503a80070100445010801c003400904850b11144117205a02034002c1c46c0100800100a071020000b40305400303000114000c03400c2ca40e01c40e090030015410001c1c0505601160070600480701d00b0b40360024242d9044503001e4400607160ba03030b0480840c01a100e6016000e00c1146428400c030016200c1303080300380c114102c44000d03400e103545d0384220404480c100e00035801c0100321032000900042d03058881a0001c407603031040d04c3c10160205c000103406103c140c8125090f402082007404401400c204140c0104e4039480031520b10101d210000c1e10a104135011550020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 431287607 1250 431286357 431286397
    0x603040201030e0607030218040c021507050f042301020a02011e020304091e0510050d020607020d08030f07020c0418260307020c01090906150507052112061005 70
    0x60b010307511440c101140c810581d0850b15007840b00030002d5000c1d21441e850f1000042d1940d0640c01e00788136901d040005a0010a01c05101c024103030006000101507500700130082055006415070600038000500d02e009200100e084050a00001d0001201215045501140f4558050303a44483c00c40e004c40e912a10544480400000407030071441260440b482031402e00110260259070307a0740f41c000300000c1003010801034031008500d030401440d80c8615948100b05180390b00c0986001002132114030b00c02000100704610b240d4034010180c10450754040f10351101d0040107074007601401210403554040300c0c10000c889a0143d0546080480e200191550810108844288003c40069480044060b00917500c034580103070020359600c0c6818606000801c0800001012420f0b8050340007a01d0144440c25040000a82c2c1165507421202d000c0e1101e10880030080c07014082d0440d41c2528108900441e42d4480c0922030941050a01616081c080d05040703000c1d0700c00503440750941d00301145c0b107d4020910 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 431288857 1250 431287607 431287609
    0x80712050706050403050a020d02060906010902090a05040c020a03020d050702031b04021c051e043503040f0b010b030f01050402030910050c0307082202010c0204141e0a0c02030906030402 82
    0x50040c1c500003403549203070105000a01d9007020241191034419402c940000010b00022130f2281c1041e0f824001c16071140e001400340c0f40c144e8000d05540b20380a02030031042940c540c00907054840c2c800c0c5000158122075640000e040d0706118008955040c0e00b4060314120040d07011030380d14030f810422600e4900b001a001c0c1c5881d5510340490700d20070074200e4003100100c18202d100000b0002910710302c10440180c1035002c00016070a91403849035400000240321000d102c3c00000106c0d80c2c101900324040ca100c44901c0c127074085c1c42c4c042c40c09a1300451f802880b0403440e00d040c108811040e04078210301c1a00b80200001e00445081d0141900c02c2580d01689a88070070f10310074540048500b044194a041404101e003414103039001d184a00c5540d40e0b021801c1d118155000682c00700c07040001c9070034000f041158090b50003074024880702480a000040c0354502c501d2100c0230220156404880c0f45050864148007164940289420183c1d0050401c0309080c0118080d5a92066154a5006480100018040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 431290107 1250 431288857 431288867
    0x10f0608040c031b170c030303152116230f010e040c2c010c0b060613140301062106050a0e06190509011a01030f0b03070602100b03030304080712 64
    0x6550061128800d59001100c1040109107406550241c0060000900b19254006480206c4000107801342d403441d228950b98014520240c0e0760180c00c01c01c030340e07114681d807a0003c030003a01c40000701002e4a10080f03c071184204410495210b080305007880c5140d4010604603040074855003c0c202c0351845007440c204010b07a084901c071071a4650013440c142e603c501c0715130410302803a20f0714010458071048442ea110300700c0e1510503003402940000c0700400000002a00400d001c0c0d01b2510003007096082509903a40101131070841d41001450088020183e1041d0909000341006004813042d291035180c1640c80054071488000809410980c45401154118400b44c3c0300100030700215040c1d40952509640364140c140920548100c02454a0001410800f040c402c465040001c056890302e8010000c004401901d0030f0541c4030300441d42c6e090401c0381c0741d808101550040101d600503050000c060070b1f80303c044500e10200d06000c0c0d0403c104000005080c1021103900551000b04100034400311102203903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 431291357 1250 431290107 431290109
    0x30406141e04060e03010b0d0b0f0a0f0216031b05060712020f03010b0307140306180a0e1f0c081003080703020f060c040e06010c02010c140f100e0607020303010f0608040c 75
    0x3468080009001c110b540d03020f9100c4c4820b4200b80c0003407141003500414003c40240e064000340c0a000e510002c01d014542e01c1842c1500300118a9003c510019145241c0d8100d1388030084900320b41c9500c450120030540c01c1400c07072020908e0a050814011260b0f11480e03161440180300408216000318015805407850f415102c2118403044480e84035a107500d042e0056500030340e102c00203d41d0075910700907080c4000b402c8a1159101401000102600451000782050701402001c45540c8400340444210b0f001c02020300b10381002441a0200c440000301801250f400701d0600041002c1c4900300041d41c3c0007074085000710307079118401d1581c03840e45040072810260003646d00d400e0f600980003805240d0780b245000e041603c0b02818554010f03152900159282140000001d011403914158a0086001c5450503801b01e10307414203546c0c02c1000c0703043e02030a10913903011281806580c0d03005901801e4042107115071105050005510b9541001c01000c052001341c82404100f1003010000b031b00f00000708000300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 431292607 1250 431291357 431291407
    0x1e0e0f0304090b0f0d051902060d0905070501080c04030222150e06030c0402120a0b0406090f0e060a060612020705010f0905031c05100308071110081803040614 70
    0x103615030303842d00031140c0a00040f4040d103114002c07080703151031240761081e403000e1a540d0203401003050030915482100b8034510403c0580e809441813000554a00842c000c1c0c007880e610440c00f07440110f041a00140801d04060032088480c10180410300040c0c48011a880c0101000c1104842c1c02d0030400d40301c030142010000c85204c94850341800200031290504150040c1412000e0700c0c040440001488124000c10480e514000150004039800003070036880050554409040829401d8a03841f804061710b000d403441417403103a41c541c40c504003000b05024150f0012040e8800703210940c038002000702220742c02191a03107a02c0e030008800302005025880598500c1540500307203c060001d00f03040341c980d044a04450004500f1200e003c041d080d462164903c00e6020340c540e49019411a1920180ea402540c0d040720240c84ea100303208040d0343c84021001206150fa42d03001604d190000654000965007500690150300501c4240500c64104401000c1e0340e450703450458407040540000030301880328011b00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 431293857 1250 431292607 431292613
    0x20913050c1b2808040603090309080106080a0b010e060307060503070e030610080d0806090114060403050a060207020a09020c030a030506040b0d0b0a1404021827060106080a1e0e0f 79
    0x2442d080d003001c00c0c1d850045034040001c0c00ca4110f036283c110040b1460490007401c40324100404d0203414000d500070940341c1d000b80390140d000368803429020300b11001c0360420589507004130002c02c200081c05070304901525175029140224100000400da84100c00e00440d021301101000044040c0d01c40c001d403200007039000b000c540003400c14504516100409002d20b01c081c1c054100041640c40c051400180214005032801c00183e00c0c0503031001105400e0354074568801010040000419000c00c100400103020b440700603682c0b410761042101307142080d4845281c2c14010b0010b041000000300503104500031606007c2995500d080c009002400014051a8031841243c5200d0501280e07080c0c4500c20119540b00308108214107046440400c0c0c11180294003144102c0408148015020b15540060400304020422007000e08070780494203204101c20305c030b6400540108842caa2020360a43c00c024a218100000c2040c0e00014001d654005840000c807611111a906160000c000b101034040a16003070f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 431294964 1107 431293857 431293897
    0x1a0a0c030f090b03090606030106050306010e010902090f1e030c01090b0d020d020408030c0a020114030705160201050904090620030f041212020a0f0305010603020913050c 75
    0x5002080202c0c901c0c00194102c603000c0a1802820b0a0028000300e1801406240c21178100d40c0c000c6120f80d000d84010002114001aa00c0c1550745080b80541c0c0c030000500414112004104840d400201000b0055180d803030211141441d55002c5041d56444501e000045601000f140030781e81c139481081024040c01c0f626a4003c1a100b00050409402c056640d0101415904500e50307216440d000030301000210b40e4880721035200e8104005110b415810002c02c01401030090141d64180d050100348100c0c00e5a0141c001d440320440028800d2000071090710b00903015011000e2190b031783c800400f81407101c0340340c02e07016284540030800004d4056a641d88602e6422015840a001400035200809885483c02c2c00108442030701e98940000c8140240c50080881d501680840100b51050160030860341e11000343e51035078240500041040d407660071260b003c0784203211038500c55640103d5 = true := by decide +kernel

theorem cover : BRFrame.Cov 431115107 431294964 := by
  have h0 := BRFrame.cov_init 431115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 431115107 ≤ n) (h2 : n < 431294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
