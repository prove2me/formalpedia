-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0637
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:51:22.922976+00:00
-- url     : https://prove2.me/submissions/fe13a37b-68a6-4513-bf42-0391a756f9d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 114388489 ≤ n < 114568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 114389739 1250 114388489 114388501
    0xf04020c1f0b030304140406270f020306010c061a040c05130f030809060a0309020306070809010c020c03030f1c09080a090905090307141011040f0812090f060409020a0206 75
    0x24890500300754007800d41003641d25016928007200ba00e0841c4c003d440054641a803010000d00501125001904607820032400c0b00c1e0280504258a894003050100070004140c045d9508d40c268801100d0742c6011441190008000030220307401006005007015a0044c1d480c41c44c00003038162042481d21800080c0003240da0300c1481141403041c802401c03400328244140d481d50fa501031031030240a40851040d1004109254224000c0d00181b885903402410386485242460b806807c0c030b00259607410aa40c03030080c40429541c0001000700d04104020015814a121000702402c2548a210100e22107803025031a10b1542410b4082c1080940c8241e600c6921038081c13000051840d44c41c0d5001032107081c24101401601c403004402c40d1135264000714014a0248210000ba18280c00c41d89580c1e45c3d0f910703080c1721280216040c4007902c00e8440051040400ca030740c405010b03685100454070034a18010402070882940307001d0342c81c04800e150252150b400e065079605440102d802c258111809600580300b0844 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 114390989 1250 114389739 114389773
    0x50f15090712020a2106020705030703110d092309090703110a0e1b1908100f08031b0a05070f06020706090803090103050718030501200c1b0f04020c 65
    0x1020300b4070301d19550300590071500041e004160a1242e44504a04102201c0704422070511850b00140c102c0c0007950707515682e00e000c3d41c0e640c0c01980c0275800100b0f40842041c030a0004079040040c4a207507035480e410030307081c03400158000400d404c100581d0000740001800d50703250b07524a81d114500300c0d005849154590b01b8507020300c1c4d01c60010f441c41190390301c409000040408520541091030b0512500c61000020303116003d41c42076400c071403000c1d40d4000260300c40550181c00907201750380c8522640c2c07110740d5070500102d0310025400780f15102e030024400002c44c0c087c2e800020b11110b000a0860304c050700035417282800c10810740c1040c10f0141c0690014000160100249002403800d031402902c0f807031a250042d9102e0292107091410540c03600301181243e0300c24110640c507e005541c4004440347c0d40d1038080d000380310440d403c0c80e1130101c00210341c0d41c4071049400d580d164076805018004c448a00100c001c110701c1031500301a0b120420009556094070340e8406030409210440040032852447ca0180c1c1d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 114392239 1250 114390989 114391003
    0x2010f1e050901020a021e1212060a08030c030d0207020f12030d050c03071b020d02120c12031303020d08040807030605010e0a0606051e0c06090d08100e0105010804050f1509 76
    0x42c8903680100042c00106500040d040c07130003141541d0303204015160080080c2822204880c1e03050240b40401d400c40c0401340d002181c4e00803002140e03100e07500c0ea500c0e881280c03a03000310704691a8903001880807001c0750100350028485c15200038010100307900400009203140890080401d003581c00443d4000e0f80304102d201e040c0d003111b000c080c914110702c0c0c100301c01407407022404084014040446039981c110344920050400c680d5006210760030062418000507601c000d40a107236441101c00c0d1a4040d60000b020044802c1c0e000c540343c112000f1b81c11364091181e038490045003140c141100700300c0020741d43c00c01d00c1030001541c403400b80030917154500005001050001b401000c031b0b4514240c02044169003280441d50820091890208004011302c00d200d41c600420325283c190b4042e803402c102800c0c40c0032400c000d0304001600d89607a580c03160340a8642031044e500030303400601c0440740144019070151108642c170612540444406040403d00c26051000d84000003028848560901040d05c00c248041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 114393489 1250 114392239 114392251
    0x10e010e150a050108030406030924022709060d0c0905040807020a05120615010e1207080d08040528060c090602070503030703080c130b0c06070305010f14040b0102010f1e05 76
    0x5200f5541480307512602c901c030301e00c074050615548071004410840c01110020417103140d0300362148440d2408a5020180d40140d1822113545c0508400042d84080c2c41600202200094046180d1f90384200500003c1241c22000781c0340090b00d6a0001811010390107900e218034455803c0307a480d18a14418443c0d59140764108911074400800c580c0002a0001500782c0c0c070580300c500b90291800b900e00143e07410b440c2c0d56000c1e50040340456062081c4800011144110381c050401c0b5000103080c2c510407a0042d005a800038040d40001d01d03d4901d049030500615407006090202000d0810b85a50b01400c03a0350220034400886d440001c20042a074050041000600065014524001d480e90300100700340340c002e000a66100c00803078030709115284040d0b103401400500c0699541c41034555205981c0b10804c0b101000000d04180001c910701d00303c403c06500715141e58281c4001d6030074902c1003201a2078440c00c0141103640c0c1d10040c0d0f0704060035001e40000c64801c50320500040034038a203880184d030001098 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 114394739 1250 114393489 114393491
    0xf0d051003020f040902150c030304110a0303050a050304030203160f0201080c031905100f3f02090604110f0d110a02070302090702010e0303013203100e010e010e150a 73
    0x1000582ca40400710f050711441214000396080881c40003440c060783c0948010f1440b880862800300011000004500070b5028205c520f0590400c2010441400201c0c040140040c1003485807081075805100956041b9100c0c0c01980d080440061242c183c4806080081d590202000f1b400410755801c8104c0e5038000485a038554590725003c00c2c0f074a0a500d40604003c4400d0b40c03074001400010240019074080d100d12040c42036000c1d0b031900b10052043c130014100ca0080032110f6a1499505510803440100c0d820511100c00d0035419020442c2100c4000c103495000768451800403210b04d1920020080211600e00c00703a19030090311a030034201c5150040c02d12908004228404040390001450b100b1a079040f2a06071050b0783d448030884c05080c10490312a00c510021002040c21110316841c0015000801034400c0480500c0714608403078212000d60710303010340000104c02a504400c0d004440982d4400c0000f14880940030449801c680c42c01d0709484568010b8800c8117110502020101e41050b50311134 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 114395989 1250 114394739 114394771
    0x60302010e03070303051801090815090714090103120c05010c02070602010c08011226031005330a020307050708062d07080636010602070810021e0f0d05 67
    0x1402900e10f110f80c9404055031f0390342515100c1c3c2d42e84a0002d10b4007409a140c00d80724003440c5e0b0161103111030020b07250030140c1d001d540400b2900d103111448100c08954010a00d240591841e1103640a840c1490032a06c2041841d04080380890f10901429480008a81c000c200c000d181c6038009003114400f1031000c04002541c00100940b1001c40e00c00d0003955080f600710401000700350103411aa07111000c0000c51203601004008039650100404000c40c0c0050300c1980f540c080003542c0351441c502c0c1000303120741403042e031150212a03184c1d800a0010003075240100c0b45001056200c4a1134242154071411290b4400400c010a1002014080b83d1103c0c40c02e0180902c204400c030f80e2200090300800b1001001603120000308140ea645030040340c080076401c02c82d05440c2202043e5000340e41c0407015840c0550390781c400041e00f40e10001d01030048400c0c40c03029000c145403004007000650311504c03500108140c074840342030b0240c45507002080f0b101c40d07211502d9901c0c000502800c0c240c3c0c400801d10001455068 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 114397239 1250 114395989 114395993
    0x2060f091f0c02010204030f0c090b0402030603100e21091e010918090c03030e030c0a08070b090415170c040b090703020309120307121a1503071b06060302010e030703 73
    0x3851060020000c90100d01d0703030242e9000724020b0156500144c5100e40c80118101071200c410800c03802d0300d01c0700790180040e504810a0205a10041c0e039466090f074407400061014184c5036101d071005d201c00c141642e030301c513040f04494050006896580b281c00400050030861b00c0c0f07010095511f10075900b42154000710122000a410801644110400e500083c0b16100c00401d942e400301c03005551180003030340b00640724280100001724102186010388a038121201a903c1c08568a60449609000401c2558105040b44005401c5140e4564009446800207411904251500806808040940000c0400b101031f00d07850003102c80700c1c0c140036919100d0384001c1ca4a0381d070907072540304016007030141e1707251a00e00d0700c203141c402c158201c9149144044184008194040b4000d280341c5034010091141c044c084450a25094070354150707e501c02c0700308a160a0421924001d540c0c041400e0400d038940c103c07890f00b4100f00500c10001126043c5d030301d40c0280115030b000044000c8500781600103203201070070743e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 114398489 1250 114397239 114397273
    0x1909120210080a0615050301080615090604021602030114070206010e041518020a0905011d010b0702011115040308040215090a18090c03060608010c0f0804030807030e03070302060f09 80
    0x2103908400b0401c403100010b011003440d0300600001e000200c650b0341c03a0565041d00900503002070003149818000e01020484024076564001100c45004080300000e031500070400c002503000100305450014a2100d20300941c3e000e02c00c41a41c6815602c01046a141440000381403040c1600b2240302032032a00140f00108007600340f003c00c403844030000012075035009600e0744074032500000005c0d8403201514011420918581186040341d40d016126a0225001e44650300705503000d002d00b014003042440603d0140d84a9845040030041d51015a421102078200c0d00302581c00403901a40810066000e000841c01d02043d600800d01c0e0114856040c084500009100100c06129524100340c82012200120381d00c0c6d1b019444141d4000da00d4921282c1d80d2409070f024008a00c036002c029407901c42c1040307005011710b0305034440ca02079548598680da6113944c2a140c45001a12103801c050741c8000030f0340006810401441024001e40041c091494103901600040c034005050504540180901e50503000704 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 114399739 1250 114398489 114398509
    0x307030c0b0709030b10090f0c051608250b07090302100c050f150603070503010b090109113001080c01020307060e01150f0f050301020a0e0d020d05010219091202 71
    0xc07040030303608542ca51042c1181d2480094002500521040081c0306065524000c0c5204031031050900b4000c11842c000700c5e00413550605c1c07403840415010000303103000c1d04114600c200c115108020303850500481040a003540d20078203403c02d120750405043c06040c0411940004d40c05502c92408241c403a0030340e8013194804844c4004c040a10401044140801c40c003448042c141044e04800c80e130440d44034610190541c0c5090303130b500380240218200450346081c103004a40354902d000d070191055910f481c0038140204260001c01405010500c03c0c1c06014055900302840818503070301c40400213002c20f55000003001c040e84410404d80c80740c5200380840c0d8001c01651038868001170000748015094080b94007500c2c925450f071500541400d00410080c0da0003d008065919540d90f10180341d07120703010b040c202d1107203000c50700100310b4420b200c550900d07000c0c45100880740302400841001c1225510b00c1e00366040400300c01c4040d420700b02d481d4a01607108040d5001000b0000030440b500c12907030007190201503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 114400989 1250 114399739 114399743
    0xf091509021b100902010e090108030306060d020d020703050909060f011e020c030d022a03060c1602040c0509100203031b03040c08100f0605091006030e1501030506010510020307030c 80
    0x34010a80920b41d02201c4030441800025a06071940c410392501290300402a80001328045958628000b596041c0030000e141a40c03901c2004602c2c644030313142004204e4102c41807201708076408000b41000c005150014100140c4a40c942c035440720081e10400820b8a40200f2541c0245094100701e2401d82c0d00c0090b0240041801c420680c4200303c4100c200c2c00e1480007000c19800d40302c0c140d241080c96500041d005208248aa44054a51050900303a541d441441881a0341607100c1400b0400144180d0024030460402d05888803104c1d5250380410155034003042e610020030004501264282000f044400041260744080e40c998503044c91106003a10545450802c2d49170040002010401740450034006051800b080b195000c8850101d24040c240c410000001541400350000366420640040b60081030056540074500b400c010080b03004000300d4001d1007080c4176071450086205043c43c28580694000c00280001703604082c240104a8142c00503841194001c21000300466070008041d840c050f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 114402239 1250 114400989 114400991
    0x10303080709050a0b0d0e1b010f0519030c020106170a0b061206240d020607060c031b110c010503010b0d02070f060c021e030c0d051e12010f091509 65
    0x18071100d00840320740103190415070b08a105648003080b03002414020b404816403090080c88841010814140c480c1c0485400b840c00903080707c01c00070a0760003140c801d886040d03549001130424003d110004500c0800c00061808a65030705100c40310554280282c0c4042c042000a824141b00c1010b56559203ca00801c09400c1007030110114869581c1c801008001c5201e20088907401d08100e61500f84005190015400101c0025504200c03400c104101e82c034040e40051540c0d003011900e8441c00c0161400210f2031041654401c1420301088024003170759541502951128080145010130500d001c1c0d07001c000c01c0c103001d42400100070600c145421602803112206000d038403442c05250200241c0112900103105509003105000d61036400620720107810640c405011005400ba00740a8907072040c82c035030741820f4104030000c2d0143d81c01031000781800000c1c0b224545000c00038411500141c0c1000b140b1847e088100c03801004500c500d100a000030f4031080c0020001e880d15110701358a40d801178440d1008107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 114403489 1250 114402239 114402241
    0x160807090f06050405040b0f061f08040302010f060b090901080105100506070302070906060c050c0a08031818090a0507080601080706030e0102070215040906060302120f0c070f03091403011401030308 87
    0x11078016044100100f002030300c00e02c1203040604c1e24550b201030031075541e9002402180080c640d03150005030023510b58441049007100c42e2542d2011143c0d1040104243c2c00e5640303c80c0016104403413072054100a006122105c5e40307030181c40c41000b2004806a200d041c01da0b04100600c00040d55243c1241c00b01c5504070380300b81e83d451040c50140d04290007a071080c2115460068000b889640011025603207901c14010780b00081c07404e008100b149415402aa04640c0c028065020425003101c00c480c0c54103401491658080c8483d801c41d0000b5504a440e0310079900401302100c1000390030006400605a02c0024007069070400005650300c0d40c041c0705650030561565480349100100f03504865103640c01408601c5e116040c600c54400c90785c03040c420144594540100052003500c83e101b40c42d000703500d08210465030380b90704059404d03045003c0d1003034030348007020800000001c800030307900e04c6040d20a8440b41006460204007150400281005a0007070741008001c41c80302e21250030050540b507142c100b0801e1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 114404739 1250 114403489 114403511
    0xf0609030a0b0903030601140c0a0209221a01170d052506090b07030603030c1403040b130603110403230c0301020d0504050606010507080d05040f06140916080709 71
    0x36110701e248000d05044100c0c42404030b100c0000c0f0045220b041c00f030322010424100d0b600c22034942c4c032440050b44256000009903400514101c0c1c0c506070091002d07140340449803010301d11582400122a821103141c0c0e124020340d442e59010b859202d00520210440414803181c581105403101514001c0c0070400100240d06020000030810907032085580307400380308100900f0720301800241000303e415074994040c1c4000030000c911900859044c2c0c0c1e803580d5142d80303841c2c2d25524507100301c1e059400000140024072000c80e003840c5070405020107404030341c039a8110900d003801c0502241c5000c1c0e08901005010801400814003400b06401c4c040100d40e0420012212000c0b894100300768456201e915500004c1c1400101205810aa02890044050721115150a80192071500c511030009001010900c03401d569922a80d21041e8001d0180b5808000c1090035540d210480382c004441903217800e40d1005000340e01408115070581c032185100c422240345c0c244001160360b03214a10807a20b401e80c984c0f0712079103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 114405989 1250 114404739 114404743
    0x102010204210209090303070f0509060705060708010f05100e0906040b270906090c06070503121603180309120201050d02041512110d02071e0804080d030603020f060903 74
    0xc0203010030b242040040d036408020601000b10104103030700c42c1c00b00c40e0103e000c590300401102d00810782501c941da202e4416a0301614185c20801e0078a50004051081001060f820b101503845119260307640c64003981020184489402960462409101d5070120f800c58282c01060308000034074102c0303900300c82c2e50f29040020090100c2100c2150071444100f41e084d4800440c1e00c8944070341c1e10085000a8558841014a940302070441d6084010b6005044848203400c2103402081e05038080c44c00d407403500104c0445540b90038400d072440002440740040c035440c075a5051090499180241110000100454600500100c3c9900442c010000161040b4003160b00840803914481c00003582551a50b43e55025600d072100c800c50041c01040740741c008003000005500c500b1201090380d105060410440d142032000030740010008450020040c044aa0f00000032a070b1125414440d060a41c1d846050011290408032211028010306080410500042e5a000342e607000009083e11003d03140e40080000074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 114407239 1250 114405989 114405997
    0x4060206060625121211030117070b04030507030201171b0c070305060405030a090b12220213061e0b0304060c14120103110105040308090907030609020a02071805061c0201020102 78
    0x40d003c241680e44050400600b10b420341c5811381c2c1e5854020910143e000c49800f6a01c030788180a6601c0401c100601c4030140d0004c981d00c00050810458103c9505d503020181d0583c4643c2040e1040e6000000400456034410714011282003c1c0300e187c02103041c83c404602001d10740584901e125030002c142a4810074040150400454018040302c0c46801c0c01d04205880e42d0000d010309000503c102c070003240a451075001c442c06051995494000c960b940403010032a08161500400d104610800480c0560b80c5c20708009182070868200041d000d250641c2080c014245a0704da00c07550b1000c0608229858001040da0340c865009a00070620030403400c0101e41c030007003c500032070b078140d008100c48158101d03003042541070707921078000013604c0d00310319005540500582c031005100741c5003001101018104400400e0b000035035030030080381050301e0b611284242e1700304403d1240164012130b410031000d03050b00010494050710940c02c00480c2001008901102e2441c2103003074412003160015400c6900c03d504072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 114408489 1250 114407239 114407287
    0x81803090d0c090c080601020613050114010b030901050a0b010504091104091811031614010e130213090b09041b09020d02041d0601081801060b040801050405070605040602060606 78
    0x400c2078545150240c2d06902c40d01504002c58a00001041150300540b416030003820141c00030000c5543d05080c190701025400c00440d0315540b01c041c0c0c800503148030f406140c0a403403400900c1c2e0f10303440d202c40d2403801c64800030300e2030008a080084c01d0803581d03003040403681a540a0540072442d210845410207141c81241c1c8582403503403800c5a18035500c00725800228400303118103070044a4075181010160340b0001c101c2c0110040d2007440c010465812244240004140181000e40c00c02282100055420496008030040701743c0001c1e002500006c2020060702402d0341c0d9808000a908000c0400c5490000400007810383e4075660402510001e0142c0302402418019415965620556a01d1020350410b00c100703540101540d103850300c5505804001ca00c9580107940b4410070740e03511159202000c0d8419101655035685030000714042040d070005001074650700d80085010f060070320300146030152940c041c43c2045000c8c0810f01101d40d010849030380090b070440e4032549809a0640c08880c2c4c0c1d452000e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 114409739 1250 114408489 114408499
    0x40807080c0a0e071706010e09150102120705030703050a09090c050a080c0306030a111201021204120504060801052101180b060d03090b03040807050d05030402190608180309 76
    0x400240c505000810180503102030340d034400ca035541c829030b080c01400d068401901040d5100d14402c0c01240b9400342c00d5200342c2c14905600300707003880d0002c6884840103030341c04010900295204241560100a42443c11491034841403a00c65540c641940b01c4c0070300f103070088c20803074001150b208403842002200041d114110040151807140d21000d00302c1da102c0f00300500031a2180d1b0014101c0e81c1d50400780e92142c6000307000303400c8003d4184d54945410421102865002d40c012480d03201404003403019040441184695075801c0c186030926000040080c0c4c0541c00304a0700f080140b20040d84400c0c03280c11100d05803801e42401040c2c5115444104041100c644c1a619000b10a4008568075500780c0400c0d020341d9614805844142c2440103c40c0d040c400a004510a80741c2000035504a2004540c828042c80b04182840000da941c9030820020100c5100003d5021051109616258045062203181e5030840300c181c0b4504900a0b00e4520014041003000c41702000c807210300601401106c05440c40208 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 114410989 1250 114409739 114409753
    0x131704080102070519030c06050402061b07030510050702070e0411090c12091b01180305150a0b0105040509220b010b04090b040902060304150b0d0b041208010b04060507080408 77
    0xa414000d41104500b519184207864032150030120360107400c05019051f42d40c46e1429200c0b80c942c02c028040151040f604080100230501e00380f940c0380c1010000381d41180c0500f00c00380ca075041c41403510054001407840641f40034103005190f41c0000700c50b02120603c4100c20100d58a03401d0008000c1c58001090b034010318203404026000100c0c00c01000d209c03c5000b07039060252200070001c1c0c0d4580050f0040100e508030300240030b1903903000702c00c501241c00382000c10740002da8481d66200c1c284030340021610450f00018007032026a041d00e0085080d6150280b80c4207042074546800030780b20010103400120b1b0340040c19442d043c855054005c00010320341250038603001e541e40300010b240a901030310800a0041c5031040400c50361905004840e4100d0b0020222400d40c1c940d502c52401c40040d40c02c0102c000c0707944024601480e110840100903490103140c0a00c2103142c107061400003032010500d01c5041000d50401401700d0340808090f2410741e0058603129880e0210741c5400200d600c5079400c465020b1103000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 114412239 1250 114410989 114410999
    0x90513120c0f0803010510081021020301090b0402090a09050307020d1e0b011811040b210a0b120105060a06030f0b04090b011a0408030a18030222050903090108131704 73
    0xf00c001c5048920a4030306035540f085001c82101c80d21300549896103500c00c180d404101c070080100da442d00a00131160240d609180c0e40d40000d0848440740003c4648019190800c010b43ca8520821a402040320b04180031444842e0390b00c5807280b0039104001d2052000584190a11030038660446220b00003a403403141000c002e061601c40450244103400c004081e1072541c082e0501d050250541e00c815090300725042508081c11800780350004139002140480845150045400d4100c5d0580100141d8000140c51154401400f80b00e0400b0071800c000c40c0e040505104030340c0c841d150160101d640da840c0000e00d0550300302000740070b40052040c00703611138141140383d000d11950226080c108d94404007414080d0010360340d402580e010354884d881302a08240711582c51b2a000d10b000400c804c00c1c004080203c00d8883c0e0025800c0c0c005100e004c0c8032644410307040c050103070f1588120f507042150381f4019414148290002031111000802d0000d0728059007680d0020807040f1101240c40030302d140c0c01030b600c4548030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 114413489 1250 114412239 114412253
    0x12060306090c17010e03090906030307081c061a030406110c070e090c01020c1008040201020109080307050d0b01030204050d0807060e030f07050c010c150e0c0a0f090501090513120c0f 80
    0x1e4060f038046019034228904070744070140704070112401c0c08406903051000b200f0401540c04001098540c240c0010031640002031314040007401e00116106400d00d0100c04118408122035403504044115a00880058648003040341580c1d44030307510001c00702c0c1400d00621a4441802400003102031442100e0012035030383e00d009081c52080c82e24600300c4014514140049035282203003010300d40c010f00e0740a035245c00103204136156139210b401800041044206940c070303890035920880302003002a0022039958450b501600584c1101c0009180035420241010b0000780c01c0300384031000900e0801c0010390f9004001a030b8014507100848002540c0e2642c04005e5241d8060b40300c680700311028010225040300660242c5103a080031a003002d0354084400900c21030300010440142d01c3c100768410603001c0f0312281c0d2040404800b0381981070044000900e004007550591700e040e04115940c904080030044000c110a20850140c4d810071500401d8107020582a11060311012010f0000c400c0c903900b5030184109 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 114414739 1250 114413489 114413513
    0x1060302040e0d080f0103020603010509090a0c06030c1701080303130f050d0201050126030405130e010e0c011218060c050f040b091807020a03050c01060513051f030804061206030609 80
    0x1681c0b9010304c2940c507100b076144c00800074000258002d40c00e0006000d030b410601070040e446480103089465400c01e075160f03c82c80c0d051550018000907115000c10f902c42d58000d420030080052014040c0182d410011865105d010003090f54400c890a500c2c090180111344084100c820b80080039194121020b8100a020b88824050704140c882002104502ca0300800c0d03203a10b410a65102650134181080300300001c2c0c0084090580040ea20354402c1401d84400788100c00844011200410311700c0c05410014018615452807480741e185084411403241460b07150010340315a009000041c00b1804980070303500d6004001440f4506100440d0102d1503c040c0b070b00400242c0300845415104400300321170f2030302600d0111644d6006802c141c2c08600024043e40242c001e48003000c0000c01c810391150042020080000451041c180c1c91390305022100c02c0300b02c01103001001d01d00101c0e03545401c3d920740520300e100300c0c40ba00d0100202101c001502c81d0300f68dc4103401541d4000814068892039041010240c5a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 114415989 1250 114414739 114414763
    0x5010203060306010f120206090a2403050a0c02071202120708030d1104060e190513090b060301140106080a18050c01180620120c21040f1701060302040e 67
    0x32a41c400494074000503a8003200b02ca0444000800406d00c46d82440103e4001040113504800e1101c0b0100d001002c090000c0d01104140408000749013901600805551000e412080c1181c500205019941d90205070141540c09548480e081e0046d0b0703101203100071a126040454500564002203030171b41000c0003d000902c81a0301c1400601805d00640701240f04a108240c003140354960780b042941809902c082003840340d032010255065850b0003150001d85540c4d0412503095940d0700e10700030480042c103110b0f00654107030001c01c040c1840c5552009000010302a40d0103100024001414102060708a4100000903910341400d0b003a140c9010be03a19500342d1011408a6011041503144141c4982e80301c04441140d902da2805070b814035464040070209100f07915042c040d011070304103d01546002403401c0e401c058014501d110106045100c42481a241c0381d280420420041021204404c89542a1052203083c64030f0181c2d00c3d0500350041c01a5440203400c6401c0040c4140b50500101d000c450001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 114417239 1250 114415989 114415993
    0xd1d1507020d050a0f030c170903040302040f02040e071101060302040c09080607140301120f05030301120b0c0705060f0a0b1815010e100804021305190b01050702010c060b03120304050102030603 85
    0x624180026541401030884c54030018034896100151035101e40c0110782c121060f0b0610490744100c90f411030710154000c032020005a440000c0400460138544100c1d0000800700a08508082c200056520010005400201013040940d21416807003400c0d80f1050003140e00a0041007020700010307000d414413645100d120f44600a11000413a100c1c080d02c4091602503444814503c0d41c1e0030b01c070498800c080304010540d80e1400710301500002550420045000c0e06030014042603045540c40c24601006005091440740182400184000741c0c000582540050040d040181940c0e6030304480c900402c9520721441c0d1000e1700002e1441e12903175940015024480d09445144020308540040d00c501d1010017001d5000008191001380c990b10511801760002c2c8001c11000c10040c5800e540010f40344241c0b01e1403c60a074286510400060700e2180d030b42105001c3c2882030a002c070507000070700307400d4005031301401042e11503441030029907081c822a566056070840c0d0640700d04042c2040c40c000c0d00f08840c614024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 114418489 1250 114417239 114417253
    0x62a0b0109050703052514040b030a0e070e04020609151c05070e030c060d1506032a0e09040320060114030708030d270b0601080601090b0d1d150702 65
    0x2113480303405694411000f0410b034175000f030081c502000d08440200c10345000c0014201070310212588120052008140b0781c46010b480f81032200845c02154032143c80e070030642e03000d07030740030844c00300c80f111015401a01290701c04d840b50801c4000c41d00440c0c45084243e260100002c200003038001140c040e04d011101c694040180e42da800805982c0b401011280641c541c0c400842082c0c203180002c020002d080f4101d6001c115440070030141902240c41e80c200c0e40110b0f0712504c0e6040c02c4542c40c2c000701d1400603150140c1c1d4130310b18200c80c0503001144001c0070074000c8140d00c0024042c10700030728000e282c02c40c0345600140c82c10b4000c50200d48503a0203002c0c106051a95894900051400040090a980c40703040954640252018101c000b0041c4140d0704405e182c4480110002d4000c1d08460016036006112002da140391072800180452001005035050000c1580d00b407013001c071b07020196580310301d40180005590300002c0c1304005011006074580994420014200181c08500b010180515225003c075114 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 114419739 1250 114418489 114418501
    0x4020712110303071205041a0709080f010501050a03030c0501090c0b0904060f210309030b160f031b0c020402071e0b0703020c0a02040b06120a0b03070603090507062a0b010905 77
    0x40c0d03c000c0d43c803000000c0c01c04010030090181d17640501e400911640d050004042402842141080c0031200340012a120910403c400b40041c4144520040f254000700041d60418001401c80b0040b800042c08100c1c1101c1c0706001c00c4400d5004464403900010b501268035a9075807144003e5121b402800d001c1e1b400c06000007510060303214241c090395030303800f20640641c05014410800c080c41050a400700140c0c4000000451940c1e8589400382c03041c1841d0000a0000b940c5c054402c5030000501401c0602d84200d10300c02c06144c0d0028140310482c0c1c60a06600b1480e0300028029015011000c0c00e207004403400c0c8103d03421182d442682c428404e0441d01c5c0d190740e4502083e0100c0c002c540c07040c8800d8212818500061905500014464000400c2d09007084120362003505031003401c40d42101c2071740da19040c0d0340c520b160800800004181c585401d11140c0c100d0fa9030151100040d10900381403103a041c00f00c4200d0381942c501003128160380ca050085981c5542001c60502000380b02e01c4806901c0e20000c144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 114420989 1250 114419739 114419743
    0x1214060a0e0c0304080702150309010507090e150120191a0f0f0402061603030b030c0303040f090506041b030609110304021c03020c0402120612060403020d1d0402071211 74
    0x4402c61128000c5820741d039807078031584507035440b0701c4007243d0103002c582891221190701000340d0f016850b60400080e19141004002e4041100c80c0c100800c0011104100940084c2d46442081d00640a1800301c101d181d0b1800700000310719100050510a006201803421004104c92490507190301401101075403100c0d0486051152009035520408800500700084456400790b0741c85401620103003980345044500c40c40d0300c49031400980c08400107034440d01c44121070b1604100c81c5003000d000310b000c6c52a243c40c140504c000d48d455885800d00041c0c40d03034002800c541e00ca9100c241c1200b0800c0c05001100c6007881f00070300816450095241c014980651050700ca41e110095a10469020745001024004407168440b0f103420500e00b00d046202c0c0886040d0107850f540003a2492a4040881103040c3c1401d0b41042450000c0c01c01c05412135019a04001c046680040c0c100444035490905403206a40c450022210550702000d064000e40009200e09c1005201400d402c8956290758580b90000b6486842035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 114422239 1250 114420989 114420991
    0x403050c1003020c0f0a05100b1003200a0513090612140a0b040503040e0906100e04060f020d020d0b0907170c09030d0807030b190501120f06060503010303020615010f0507031214060a0e 81
    0x550428a0b030385520710242d01a33440700d040304d80c01400d4103146203201d401840300e42e40304580140000f400803940341072141064501101801820609001c4982008100401c2c804140800ba01300d110030851056085014052444406d42000d200eaa041c80e060811030b559610920400d0a02610103000601070140843c505010f000611000300000303203410601d07441882e01070016aa900d03a20390417141490060700c003e1142d05942e2101503141c00c81100140125441300719080e000c0c0f10814100400103502c01d5800510220780354101000b03403a81d90130400305000354061703550144580c40855542c40e41010785139218201300d035403d00c43c0300100700a1143d0728a588000400280300020184546e41c024090052200e5200c0e0000441d01da01c080c80c00b040d030741940e1084000c1000080184141036041c49800d0340a0145280c4030408000c0c80e000070092001004410304010000c84d01c0c0c0101071240056880107420f81c1402d00601047c1107480c072641c9001c1c0c0d811413085144190001b03c0f41d0a5441e92 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 114423489 1250 114422239 114422261
    0x14151b070b0a0912110d050318100b01030605190b0a050d0f02070b06180c09011112030601090608161d030d0908060601020a23010b09010905060103060b0403050c1003020c0f0a0510 79
    0x150006c000300b11400c0d26241c03c054048030404004500b1186181001c104800c2412001030307020070703420842000581258041d40155014843d286011f602001041071a941210301d40c5802e01d582d0008510100c84a010f0840d00101d060f0030150904c401f104250041c0403100c0c05240440500c0d00c0f81420041040600241010310003603050000341c50041d0240a88110041818492000c0c04100046030501e00c003081385c48211071004c000e00c0b10551344002040007800050400e02040e040000416031108140c5d00d0b10b00420444550040351140da045011110490240440e01492032070300380031b0081c1805010350081131080da00000c5041d0701c0001d044800c40e400460200013080c0401c1c0c00b200c21454020044550b40d2903414101140c1c407031614180c0200306a01c2d001410b400c0600005045d6035156009440e1030006001c2400030580110b01500c0c20941112109684182c0b1001a406805001c901c00700078042c40004c482803040c04125005031500c81c0c0d007500e61000b045200c01040700e04803414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 114424739 1250 114423489 114423493
    0x80a0903150e251d1005010203091f02030715020a02150601090909020d0203030304031106070e1c0317010b0a02010f0c08010308130e0a0914151b070b0a091211 70
    0x2210020042842e1162100d241c2604000030042d251000560301c1384a011081c0581040001000041d000400c0e00c640500000d201031864030260b000007a070203a44e20070050418801c00703c07085c10b04d030340200b0481c6d0506d544041c0310342210440c2c7c1d07c07043c0290045082034015004100d401001440d030401020300c0381d00141c46500c1154180410f0400a0280800890700715002805803030169034100080c40c40f0b64483e944801d40200809566418520041c16803010711203680041c031810f0741d500c14208042095000755401c0e046060404503040320610b191034844030001000403030b003292110000c240070070342d6070000d11580f04055030b880c0403601c3c10790706000015400d07001880059584401014440321083e2081e00058a603103400d216898265080c481056580f08048200210f10744010b00c1c440502c40a400b1401c1202a0b001800d0001820424015a01e50303d000e514041c02d0305076844950807003c4040303645001011000202801c11041ea5400349044442090610800c0200714a85007480 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 114425989 1250 114424739 114424753
    0x1503020909090c090a150b181f0212030705070c18060e0c0403031103070606060801171b0907110105040f0b0c041202131b08060a0b0a080c0703020109080a0903150e 72
    0x10400520445011042841c0d0b541c9001407101c107800080c090581e0070031042c0e4031003640b0a007002a10030f0500c16034550709270140c10300c2c0b2036035402140080e2400125600165641d590751403c88032481000c40051030a607414130081004406002502400c0300c460320204122a00c80300408000702c01150b540b02c01c0c040802c410700000e407103085145809034000c0120390801d8030f56503403001510060b412950009506c2d80041192a800403212030a406c66440a82070303404801c14000c0403101d010041340e0040f0701e010042484580b2400900d150003220030020000c40c2458074240358454141242a01c4100c0118003261072984100202d5085400811050114120681c2407041140040c03001c64507241c0d6076400310a080c441801c040e642141c003507883c0701803440c20030200100039080d5040355104041c1031210708005900011921740101a00d60125103a00d0545012400b40800520041481001280c145442500f1469420540c0d1041c60521403815605408a085a50407a0f85134401e6028030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 114427239 1250 114425989 114426001
    0x7050d020a0b0c1f090501060603050c07020f0118080601050a052b08070b0703020a03050a05061e04021e041706150405130203060903070212010509030a1202041503020909090c09 78
    0x142c0240380c40c0b0505029101610a00f103400103002c10a008a49000c6807900c8442e420030100384a4079000c0d2945060403c42410407450800b52070040302c8000b0301900d61011450901c2e03004100f501219554080b01240b0103407030b00300103920b0755407c3c86098010260a100802d0303a03e0b140d4542e00d00441d00071400148014000500308142d0241101500c3c4160100007040106048182842c81001541c5026035101c041c5d0800900710740c4010b009141c403a20f0001030145c0c1d0780d6541c0181c40200005488001da41c0701880c0010002d21585d003a1f00c03072200c0110784811b03010440034050070440d10903401803400e11b01e0160301d07152584011034000c1c05508442103001910b19240e84040d4108040c03500000d00c0d041540e0110389069419640b40700c9660022465030118035102442d00807002e45d4100900260800a0340d050b42d0f4018071b8502c00030300c80c0f0f1311201c0c0d0104403142d06450040c2030603020326002c5046010013030002d500c03520200e80141840310001c0c102040c00200c01020704006054090749a6505c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 114428489 1250 114427239 114427259
    0x40e0f1003050313050108060a0311010f0e040f050610050421050f010e010f06080f0c01030c110111040303080f130201030b040213090e0d02061303201e07050d020a 72
    0x204500c2400a4184011021500400c007510820020107030304440c89050800141c154100101207a200d040500d005000148140405100c0d05030282040810108488000d85041e4034058003550054900144001415001d030411801000c3c140c81c10031003100b03140c3c002c0b0fa092040340105442a09a41c658884c035209010000318018003030707019a180c1031030b81a03a9909664404038240e507640e45543e9500e542e04680d214401c0104000030080900c144402c1c3c040f61500401c55409060660303900d0505402030180b2152440070720400002c2004005005150302035410600003980003401c030000082c0c800c2e110403400c50140c00c0861095000207403e60044000c3d00118a000350029000e00401d907581c0d6000d2010340c050b2070303403400214031a510809072070310700006100d9041c00c542c030840500408420100c1d0a459064051425509505046c49081038142200a5071605031007548004e00c0d06032000b0b040550120003103426104159031f650f0030004c41c1c3c0600c800181d030103a01a1001c000100c07103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 114429739 1250 114428489 114428491
    0x70f110303130c090507020f07080a02030c060918180c0904031e030204080706081522021303020d0302030d06060f02070b18040c0f020105060a060909021b030a0203040801060506040e0f 81
    0x2281640c1c43c507064448118000391071081d20400056805984028848102489030401905600c030040c49241159000607a0303400d0010151805254005810511a1281c040b46103130440032241c600003506105004007400e100d0300000f01d00500030380444140c5841c2000005005a406941d00c541e10f80c1c3d40c0800802c2c03094842401c0003807550030440007079103400610800c001008030f52070700c01e00d0b0700d400c040c1030940301140c0d14454850303190314005490115034001c508500f200c070322000507283d02c060703084620b818025800103507104540300b210b8400c05900000812040110030350903c00b803079442c0004d40e8012081d64000700940c00881c1d0034440c01260001a160000c091610805018200004141215000b04240c000035a500044515190702401880d411407810344a003040b07185440801082c40c8828020750f1100e035000a40031140650028540e600c0000003001d49545001c0c0c0c071000b0f90707207900510070240c0d15420300303100045903d001c1d01650116040c902c43c2c0e0080303507915101b0b80143c80c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 114430989 1250 114429739 114429743
    0x9150e0f1f02100507020d0513080601090b040e01110d110d0e030316020d0c0201050c16091a03071a070f05030409090c05040e0d030b0a1a03070f11030313 68
    0x311000550000d41d500c0034903041149654031644040941e80e000241000c05850403000840d04050503c18890b42c00910740c0d10b100102d11302503444102e107403403201400b50240d100d0581da1003090008104820194848440002c3c21101000002212004142030b9800441400e04c0021300307104417a40c200c101d401070b0111040e010000b9190580f02c134149030494100d00700303c412690002c001c0046a034103101c40982203030a540010711007505d50420040144002c0040241088070200b03101300ca405042040740350f41c030328008000108544030b2041303400074240290054004458503404101608020401c0300607100c00160310300401d41d031180c403000f4135442054101c400441841050001c6941403002d00080d066044001c112040542003010120340c00e500310b00e101e40d15050350403690740740000c0d0008849030760742404912541550001a0a50a01d40c8185030b5808030300014205140f0107030043d0b105000710303201c0b0340201d1140321080700d540c0300c1142d060403194002c001017582040c4000d81440114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 114432239 1250 114430989 114430999
    0x816090903021002090a05041d0d020f28140604020103060906080a0f08090a12020f0f0924130603060507030209060301030609050109020d0605060103050124050306030106080109140106050109150e 86
    0x95543c1020a00302c0b240580d00b003500c20030b840007258800c400ad01c50f000d0110701d00e200504019042d0b0346000e031600d100c00d107210b80c502000002e0765580d52042c00d00364080d98004181041c0d1006110891703458040846041740080d142140119161100303224210560714410f0082403001866920500b4050071701d207060317038240c005006d04038559a4130359001c4043d0001210303e804010403481401000700c01548045d100d44109516189140c440702500c69001002408088115516024400d01d201c2c4c0d8044040d00138241181003035400c061070300f2a40c1101c1c07041c2001c124035a500c80c0101e0490040c040500d60001003000100045100c6400c01c0072000d01907000056040303003a90001e0a0301c150b8200440303500d0b40307800401c100e942c0c16104a03401400140d501b4240341c5d403900d80d44854403656043e541d062180c0400440c1043d102580a00d0103803803032100800c0b910b03119041c030b40030b020041c41c41e480380c0d582015400700d030301c1d4440c9042c1000c59103040c1a4401d050a03814040d5102d03010300d090140c1003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 114433489 1250 114432239 114432259
    0x150503180604050a030e180613060317040f0b0a02030a050a02160e181c0c1103060406090507140109030201030c05070b16030e0a110f19081609090302100209 69
    0x145080c001c00b4042c038410002080e43c0382c11458081d00c5404240107040c8039246000d4000c11781040c1440c0c1560050084580300c0050550101c680018441350700301410018641d641e003009051984c0c0284266540208884222980c85091581d50b1040452520068000303100038070070b690059018020088460042d00c02d02c46a01030a5003000106e44d2110040488003004d1240c5046d201c021968a2003d54016002450100e01000191002d41181c00d040095003076490341400f04251400888120050640e42242003900f4100013424114034240c52070b000311800000c440550540507030700d142c41a1581c0d081c5a22b15001500123100d4a844c81060000400c8004002070202100502c22018505c0106048003408402004c07101c022070f11051950000418001280980c85001c500d0101110809c2d100401203021800100550311030021148203040b0100e00e18001051031114080720341c0003285c8003542c40c0320b850103450101d04c0280141c1c0010201104940b1990010700c00240301030325041d10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 114434739 1250 114433489 114433531
    0x200604080102161a0f04141207060b0907020d080103030309060b0310060806010f0b070b0604061d160e0d03030b150a0203091513060e031e0a120306150503 68
    0x2643d02210640c0701d0b07680d041c01e900c020010014040059581e10500303103415071500b0041c10700c0170200600098803031103160030841c2400004012080b4400718404003103444440518181000d40075503c88244220060b800240550784006220701c0c20502c5035541d260f2503403a64500f58000d042d440000d07521142c407090240300c02e480401030506041000356002440e14a0704442e02d0400006801c04500400c0403001000710254403c10380d00c070140c111680345041e0321810700080c0201103d038001048810300290700f02240c1c2d1000c0c017003440b4081d0010b0122958215040450380d105c0c000e01c1c51750380507102c4040000424841d5109055044000d00001ca13030300d070104900e098640002c00c1c0400180c0c03000403428420705080d41034180c0c2a400c44d1495090071001d420b48403000c1c58034040d103010851010740080660b41e0400501081010140410441c8405503400c6509c0d84590361f0b00f511a84080d0380d000e07c0d003a1207403181030211880101102407110a894084500e80c3c0040c001007040041440c034094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 114435989 1250 114434739 114434741
    0xe010e120306010c0b070e0411030112150e0106120606060203030705030a09060b0307170f010e0d0f02010b06040e1512071517071701060e010507061d01050c04080c0306042006040801 80
    0x409000c40361947d051401b048010081562a1880e644060100510040004107a4410343c403108642c00b4a03980d40903408010000f0003420307107540a150660a200340062960000740c01d0200440c0541824400740e502d400c4140d0340c5c0d1206440700360000e00d080000860404482c0e100c180300707034803030308000c1080c01000340000e10b0844076400c44c540c4800c1e0221525a900c004000140d14a0301100080c89900c80b002c3c100c07511050541d260406010400c5120907040c1e10079445a001403200400846c1c8072030f16003001c0c00703820701c044450b180c11041244146e90185015000340d05050b0a06c802060b0f55800c01c0d01e138802c0013050300c07024810321000c501d03080c01110b034480d0020300c2920503580303100d18840007003540354110a041e40010180309407001000785590f8054103c40f20140c00800c0450105560000c041100c1080c8602d04520b510307000501ca04042003800800403107114804907005143c824080540f500c10540300180000f240c0140800c1401e4a4465255260001002c0d5400c10b030356005124 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 114437239 1250 114435989 114435991
    0x61206031f05070f17060103051906182d0e0705060f090118180c090803071103060a0605030303060409170d060e0a0e150411220e010e120306010c0b 65
    0x40480c2c1e12903040080103540304210b040300902914001c1c820300d130000210b0982d040f02804540c1059160b2000403c0b981074050004440c005d404010400e40742e8a0104680785005951401460b500305003540b02d04c0c11103148038221b07d03062000c840030507408481c00c2e84020120030b960441a03001d0b50000043c0c85d40d4940c050940e9840b01c52000d0f6a82e1201c50005103000301d610b0385008a0b0441440a00c03100c00c074082a40207003018000e000440040e185010340e5010103541c0b00140c1807200261442c1006262100614100820350403588540c643e03503518400d80c0d4503130144982582c01400090003038a0950403403000301d802051125509a5403c120040580c002500320035200d807111001c02001c0070460880e0341c0000b072101d0821100c2c0281c0c0720207403680c219a0741840e90000c0100410103200c1c0580492803034180c020724200251001312101e801294080c000c01c400149050100010070f0010f002c0c020250b68800050b00c804400d03006001000d802c050300e05e9041118444500001541816921b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 114438489 1250 114437239 114437293
    0x50105011d1f0806040608010905030708031e040303020d0f02090607030e150c0f1506010c020d0302070b0a0e010305010807083409050f062e0210020a0c02030f070506120603 76
    0x41540f5181203010b0005448540e03118503800c2e031400d04103101050000c8291180c6991020b040c1da41c0b81c8441034403000214011910985000c1c48800784410190035500070595040e000e001800300108842d2800100e00a607015140c000300100224400030b403048550601d00e1100901a0f90b509041010010b565040149442d0055100c4004100a600304100440403440915070080051401038002000c1c5490900000d00900d00807440004040c0280003040140001c5610181c4a00c10031800501c0301074101d08103404a40342c0b00000c9000d24011400006682781103004007400c1801d000580700071500d40318560004141540ea1123010303402c0e400254018101d44c0b1011907a800c2c0340e088840088d0000d8400d5208070010300d6014002c0003542c0180810441101070b40045130000c01e000e0381445104010302410a00c0052407481c1790780c0148034004814001e50447e0740c5030705030041d03203541d452060144681c000810711450b0303d006003c60255170f00c85009029079210f2548040c4d9030b20480540124 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 114439739 1250 114438489 114438497
    0x1c0f06080f06150a0e07031b0302090109120206040e0709122105120f190501080a03020705030303010303120207140610141c020f0f030d0c0302070603050105011d1f 72
    0x51000c030501d0401005400c8007542c00c07a851001410f10000b0901d0b0b5451107007030b812941c07907800100c0a900036071020700b41041d11407080c040083c0070400140203501c0100014085016044041079124508030700d40c0c112607028028601d841d050800c480019100280203504002660380301151300b209a0078030791b265602c5a460302d0700010032200704e40700c400d102d881e107131040100920200450b20101cbd0300c0709030020300e4104200d65640702c0d1540c10ba5035003490f0007003020342c80c140740002610880000f10b59290324041d41c00d80301c0c1641c0714002c06490344400c0c40041c000640e0a02c074100102d0595008010281c414a100c0729560b480b00042400c2c00706c103c4060024804425003000300c80e011112400c48a00102c84c01c251f882404e451040c1d0b8400c0204000c3d000d1800b1130080e00c256103c01904a141c400300608607807640c02c040d500104104d00d2000c0840c0140680e110025019000c0e028250503174005031140303083c8900055140034000700c410350b61903000c0450700c040242054011a0358001c54a103580f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 114440989 1250 114439739 114439753
    0x106030302101a1905040e070503010b1c03030e03041d09060606310308070c1815140a091803110703020a030f14120c01201c0f0608 58
    0xa0203801c00050988000c1d0b058180614615620f2202c0034a116400d400c42d42112061070900200c000c00358030f41c0100d0781052900c00005840f21000411a0459000710b00a20040100b881400f804048800e20309014954421007400001d000c0d8001200e542c5c61a4204ea082c940c1d03078012400e4040390800e42c504403203120030500c1005041480910340c442c0d01512640d18050900100003198142c0900c000c0425507501d03c19180c580240803110000d5402440c06a118416410664995800c502c980c3c8011403000d0380e074100e02c4030540904a1329803c180080100a0716101c103807920010402c2c3d80765400b9515100102e20a2058444d0400e0070035079050705a048002c45c50041c1c600142c1e040600925480003c08000607a03400340d034801541c0e40b000c01007111140d14941100c0100183c0d2808501c0d0140241d0910318405401c081d1448441c07007030090005182c40219540203c603c1e03202d030b400800c4204519880520b0010103030500603904ad100140105010400c40c0484a0340d800030407890300200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 114442239 1250 114440989 114440993
    0x80c060a020c0f07050303041401260708011403120304020303120106090609050108010806070507020604030c0602100501090203160f0513140405070914010e060c06070816050403050a110409020a0305010603 90
    0x80341c00d994a4003e0000c0c582c0606240020390b41c3e0140b4880d503a91020411862442c591041c1d04806c615802d10004103070b070380030701c1101500300001102c821000074094000011202a0b0b4042e01d040a80060090130080300c01413102a90750340024416605807000300010224580024245030080956580762013115041c4a0018410304480c0d008074100400200180b15003500410015006900c03403c01a43d140340700d201003002d40c011940041d002103408003000400781d4004c10440102d0b2840c9404106d1680c032486248124001500d5070300c000e8102d014000c84c840c0c05250a40800f03413580c18200c1c1040c4a9484141038a96a500595001c00380092503410509250007040d810818a00344400c01605291600440e070034030b03490a5040000f0502c403144a501e604049030313009030301d07001500c20501d8004005004804240e5003941d04c80000288825481c2c4150f00f501d040c0c9a102000c5c00490040d5200c54080e901d403218a079030300980d6002010010b0340ca8412100c02544140d0003c940180f42d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 114443489 1250 114442239 114442243
    0x20405010b180d0f020d0503090a0f0303020606090a0b100302070506070912080a050f0313021906090b0d020c010204080a0528060507030e0313090b060403020616080c060a020c 77
    0x69200254541c0c0074002442c0480040d0340c40c00405038241c0360b1240d440e95038100034040f0310149202942002c400b103210b5040c00b402100030a10a0b40950303e040f0303110f035100d000c001c1a1003148001350050300000301051451411001c040d402c0741c00d240c4040351801c20307a40021940c581030400c42021a0780090034500b048021300946030b001c509410903000040c58141c080340c0641c2211030040031003000080580030a40124165030030014480f08050300c0c1e1411742d1030b0310002c490001081e0311400011100588140a507480c00090702e480ea42e4809280d8600401403407150440d110011009070240711200c0000e9091024100404c04c002c0108914401e074200a0f0800c0b006545681c16104642d55081d15201d419818843c216440f8400061940d501c000c00c50092114000036107050000090424152441c2c1341010f090720704401082100450300c0c81003100c0d42c0304503c0300035044a01400305c0c0000da000f00c644404d4140c010b8a80d50f00d809a60507041c0d040260403150403130425030104240c80140c0302 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 114444739 1250 114443489 114443491
    0x120e0a0204140906010308030a0906020a090314010507210f021801110d08070e120105040b0106020f010e07030303020f071506091b02062d0a06060e091b03131401050103020405 77
    0x4001800760150070a050f403251a5541408082d199050000104261124560180d41c185801001c00c540300d60083c180100729581602c800d0320501800000702c3c40d410018401e41d401030260b9214180c07090784a110b40340c07120480348480703408181c0d19181d41200656900040540c14441d09005580d0b2480c1d00001d00720a500c0c102c17091166000000304000c02e41c00c40451900712581c3d081c14a1076180c03840007d100c0341030700903c40b501c3e5401c000510040016114155041c1d84407502560819141400c20741e08171001e00c4440d0603540d010315070800c0801c0c040c0d03006216000d01d0360025494030556803a03050031003144500091202d5515041040840380c944101d203d041c5000c3c0e1202401041100000c0da80d5802504400c146413200440519080c4150040310703074182c950320784040a10340001e018004081038450940841d024642402c402e00c0c101d0141071080300e40d048141c03004259107003045001d0308024982d0f210038119010500205194200844481d80c4441c000715842d0f04503c10703c0241c0754 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 114445989 1250 114444739 114444761
    0x501080a0b0604021c0e0106080d0c050a0b04050111032409060f091906170c0312030a0504030905060c0a0302071a07060b060d020304080a0e0a12060507120e0a0204 72
    0x418a90540000e81c251407481d00b10700115005a1540c0407480d04c0750900510300c0d60444c0032480c09807004540c40d4103400c118100ca08086c2070b42c021440d0808140c0c0c41c0b82180800400d26000051040b0000d540c90844540060003080005441010000354110b5036000350340c4040202d5001260307001c040079041c1d81301d408a0050b1141d000c503007032803c00f1481e100c004103000d81c407449840c0c00007400c0301ea40403000351030f0301085d120500086917124024100d0b02000c4960905600581c07000c84800d04000480040359400b40e400d49246613036500c0a14001c0c00054002c40801454403400500c1d9980d40d4050304c2d4403103000c80036003040f1480b450064a86119688945540c44882d210365280c00c20a4043c8e0f0301585c0c11240c046896041e000002c1c2840c81004640b0701d1143c804000e010921000d14043d0110000301d84401d041020200c0410503c14800d21440c200e1041a100d40300009a5980209401501904204180c00a08030030074082d216400b581840d0b640c016210041035103001e000c0c03150400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 114447239 1250 114445989 114445993
    0x301081609061a07060b090c22030201080402011d100809060a0501060f0c0501060b0f120c040e0402100e120313060305150105030408131d07080609040318050310050109050108 77
    0xa840c0c00000700704198850060f4a04071008030740c020901146410125240c50018081078161900d80046416030300714142c002085489080486a1a48001c806805498051f11040394540d1036900440c3c1c0d500e4404130078059028544a240f02d1a103036400f14021420b41ca4032131038050316201c0022842c01000400880301c082c1001c004121254000703c04904c5500c051505680400c6681401409004903078020982000001084c0481e48072590144c14503c0d00c58000c2a01c58039800840311260286004000503a418000070400602c0c0080305c4400a110701d040c19010000c440300055249503216040441075000054940c100a089514460281c801800c00300564180104841075590b04641114140720740040410b0901007680f0071b841c0301c0205001501c4403581c0b0380c10600d40c000185011030461840304000705490a00600c20346226080241c580b03026a81c4a480c02c40314900000610041c0003c0504086901d46091107507107a1900001c07030200b00f40d45000c000000b2910142d202200603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 114448489 1250 114447239 114447251
    0x31b12150609070216051002030f13080705030d0f080406090203030d0f060515030406020c0304081002070303060510120b01120905010b15030c1e0f041e140a18110301081609 76
    0x900c0d0105001700a50b00700380c800141e0301c6403060040e440c0d48699000e0040b14140898046a904140e2181c00184c038500760a403094143d4031424159501c140c406044041051410b621071224428550594420300602000c9420441600130908560059941981305920751280000500d50381c06050700500341034868090702100002949114017010300024842500022040e010310000c005490241070803801380c0d000c1e41e04014000d0001e40c40040d00300c0c0030038106040060546044800303071034518070680340c041c42c440c4208511002031504109050600401850303c100364140b92141c0110f491080000051240320b84080001100c564010301460711802c00411005a00311810388080e044e10841c0c0620f0b580458140d4a498043c0c40c246c00381c4200045000950401c550b6107150a95540d41c5819040585030b4001038413902d100400c854210708110000c00c44121000a08075140010900000702280541c6c2100003035030003030b44108540d40c080e01ca0040d4014803206224018440040c0402c0702c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 114449739 1250 114448489 114448513
    0xa0b0705030402090f01140d2306190606090b0d06030501022d0414010f0905060d02190e06191416021e0306040b040f0f060f0614031b121506090702 65
    0x81c61403c05410b008508c00d0800d17004201004000c2c11141a050702e05480349801900201da8910040380c60f40c18070010314004a44800c101c0c42104240c1d0229030321a240725041c65100c0d040ca9000d045903016181c1c1c3c8240001c045042803014121421131030341034040e16240036080c4a03e10590030031000000804000410001410001c02d07011a1004c1c204881c000c020308200f41c507028002d5000980010340003030010b0750040030fa8002d02880c60020700802d207444240d10211084041d02144640140301040050441e8a031764a2720381d4041e4580c500050402f0066901c4081c40c3c00000b02d00c010902004506c00841c605040c0f940301e100d2a0b454a040d44807002c4001a550b010003603c094103000003540401c05000040d001c03440b400347c1060640d0740d1581645406002405100303516204c05142a4001ca0440203043c1000e188140043c000d00810390460100c00081c0002c22701c103588402c00d000c40c41060b0000303000c412100391a000040b4641d103801c009000100400500bc01c0464004400d0180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 114450989 1250 114449739 114449759
    0x2a12021f1806050c0c0d03050609012106050c09030a0f05120a09091d010219030522081602030a0302010f14010b030406051518040c0509040302030a110a0b0705030402090f01 76
    0x41c49503000b100c045071640750458030b4122442051118021406250855801150160841c9005050550303070207480303a90740c09042d99011410740c04500c00c480364580041c003217140b039002187c01012007082a450034000c000043e25107100560202e030001c0050411400340308050200c1121901411529403500b81501c000608a5585010f00700259554800240907038813818040305070307451154001c40d80c1301c4020700f9004c400e50301604104c0010303080c20006003680340480c24582400300c15800a400030140ca503144600303a0030604440458010095558015039410091045414041c0d0000035201028a203484140e942003582d11070300c00d00240041280c07443d0f10f001c50303a00540043c070019180e161242c80c01d04100b0243c1049a000e55140034000e41020081c2000d40900d2059290700384140d5120144443d8100c01c4034050056001404000f03039460181c9000e40c041031142054500d1000d040d55048030540c4140c62400005d0340101c100b004500703000c445c05400a0090b6000c550395890003603502 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 114452239 1250 114450989 114451031
    0x30f150109020c0705040203011e080c0102120915070c0807080d090b090f06031f05090609070f050c0a0b0a0c02011a061803060109020304030f050a2a12021f 69
    0x40000781d0004450700e0340c80d028000e00c0d011707000007041076503a541d40d0101c1e0f04603110510302c0380ca0049101c082c0000d20714000504202e2040c01a0043c0407062014034844120360403586e10150801c1c609200542c0000e1410000d001c6113108103010a4143e04041819280c010240c20280207540048030b050901d46c0c110704c412040b2480c2401c026507520f140c2012407204103080d442ca0340c00100200030302104040c52199180e40040804005601554410800840b100c090710081c0d0000044004541072070f1146400b12008101800c3c0b46262052001c031a91030012002c000303650001d6a4030610a40b8400ca00a00925226501c001e00071341d0722160000103107102c2e5035980e5101300000650b00291000d4040c0d4003c5000004095504a60f9262030701c4010b94800c54040b130000e081d1820307000101c0e0289094440300501980c4003102c040c1c0c0001611381d8040301e0031049c840b520520160302c0026003035018404d15400d1540c050075040c48003108400080c001c50011400183c1414444803072a6000d0508dd = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 114453489 1250 114452239 114452249
    0x9030201021c020f06090f010c050403151808030405011a060903071503060801060f03030905011103030708060f10020c1c0b06091f03050a1104050105010c12031d0705030f1501 77
    0x2004a081420701e0503454007404c0f80192800c3c0c002c0c40104841030901289803095407060f88020300940140c050704480c0d0344903500006103110746840545044c0700003a401100c020048204510000d940b50320740c124107030000c841c11203031603464186010701c415a6424007800e00c64191032080c101000f14000980f0b84030640504041e0b0307862100307030128840c401e0304850010b100c82d4000b00441900c907090722040b081c2c540420b0b004510003581c002082d5101d5140d214003448401d0141d41540c0714540103e031003240281030103a206540003008030180da688070031200208200d80003042800c000d1000e01a95894041500030340ea200c40305000c01050011010030303440441242c0510307095a921031110103080341c0b0700d8482d005250910001c0104000000c20280b680d000d000803d45e00c000401c100300541d402405030b80d0010707050b40841c0001600685511803401840e0501180b2100300390010540380d0340070200c040b11544400820055402c007881242c0610090101808661109043e400080384041c03240c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 114454739 1250 114453489 114453523
    0xb0f160f12050907170114070f0519140c0105150306090c36011e031208100302060a0e01081815041a07050306032a0d06020f0706020c0d0903020102 65
    0x70f010000e0611080000d0002140941541d540e0840d00c14024030288851064000c8000081001c160140d00a810050392a82c0c48038a008841e0f10424000c02100f080001845901031017404030103080e00107401c588104000025140c80c00e0143d550b440e4441e201101e00075002007040c4a140000031544079400101034030100d07a0300b9000306680103111001103206000f04001d80f000710100720310743d0841c0d040350366189842c24030117800809020312601901c0018001c0c91b50064005082e805010440d90040c07142085c0312855540703801181482c2e000d100c4040024100604482440d03800214032904034019a092030084ca00d1401201e0752181c00500f4411440c9102001904120031f0284010318014031126865041c100140094141c0e001600c00e00e110780a205494914041c4a80c0720800d54000d1030216a40d0854901c1484030840d038501094403050707020010803a088188030001c1c04500c0c42042c0c0141c0e95041c1c0d01c1c810b400c02055015a100b001801e10040026030b90015040304801100d0342 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 114455989 1250 114454739 114454741
    0x405062b080909040c03140c060307030e100f020307020d110703061d0d03052d010902030601020a020a0e0a0b0a030b06192102010f090b0313030c0b0f160f1205 70
    0x1041c04150168245899001c42c020041004000c000480e02c41102d100d40452040c0c00300c0745400d207840351a2081c646420030418030009260714440c0d0032400090410000351240ca85039000030000345d856070751740300000980000a10020542c100050700c4400c4082c64040040d4403680001764444180344030140c51a5250304248071051918500d051180c000342c81110304003180c105000d405030a00301d45001c0c6406500141c40707090f040d003054035540c4859000a03400d42c1c1c0c0c2420064002500040c081c20b0441c89a2460000182c4480c0e100c00040c0a83c200c400d202440c1c44110103040d18158010380c2e0240d08880402c10014130059550358001004079102d8201018ac0701d454282c60700795074042e00844084110b818a001050340408545600030390700c00528000d04001a0784d804501e1040504040d030070070000300c240d0100c03034442e2082c83c8a4600900f00c400907880c1e101f6101c2c010340c0c207949005008030a01040b20564040303228403100d07500700184848060040605081c16007142100000d4680c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 114457239 1250 114455989 114455993
    0xd080a0207031e1b141e0c010c0302030903010c0503011a0913020702181e0f01080706110a1403040816050108060d0c1502160e0114100207090504030309020405062b 72
    0x1907411070101c0c135804802410901c0c14200030309030014a05441c003003406000d41408031a04c980c00c0040070300745440014622a403600d401106c51118a030030a0b0118007090044503400d507800e00468410511960ba05912941481806030070340d001110100d0400340104406500340d12501c285c0035400f01c2c050001a1640c205002040c80c8088141580c0c1c4901020400c108a003904648807510817002001c4440c520359a580305030001e03103401e01680aa980c00b0280803c03410b882000c07064016005282502c2281c03425669844030b202e544130302d0b1107841e04040790034050000b04100c0c402c41c501103c0361200955251000103441c13501b0242810380501d0603002250203021018146000901302d001c03a019004010500082d1101900340d560800442c961000244100c07054552506031001e09c90014001e0840c10708000e4444858030900055009200000170043d050b4031810344038a0080c6c50100304a02640304002c103d44000f401a0301c03131124151000c06014000300710f029400d00f581e0b02c04001c1100d078 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 114458489 1250 114457239 114457247
    0x50f040f0e24100e0c0c0712291b0906040f03020306091209010e030a170a12050105060a0503070c06060e01050424060f0e04060b120f0403141e0c0d080a0207031e 71
    0x8134003845064820203070b00054801902c840d041c61740d07004400d402891081003104080701040d200c4645042c040c500f011a1040030740ad10b000e0f119a4401c8242d40c03400c8001c5010440315041079000b003402e40354480c010000c0d0b01b01804060b034040d40c07007000384c1021100f02d0300c40380c03203405100c1029040040e105c200c40596201042401107407a0401c1482c1c0d0200034100c2204059071000c014100017072220f07006002410003d024640c1039504c000d00090900c6000c400481701e6401c010140760810030f40d00c0c44600801d82600c1038074043c00c050040b0754029030405050005445411100c55007040c00923128213078042c45400d03850181c0301c01340307018940420102d10880f000d017401100e490b4001d10f02000010780504803c01030001c41a080c500c800369030344510400034400170032203010b000310340201c0844200002d14001081c11942c0800e030903c404150121291090300491821030680d4030451141074426000b46007141e11410b15038082d0324201da150b07001865900c2c0000d0b90f1b429030003900d000d214001c1c01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 114459739 1250 114458489 114458497
    0x60f0403141218010c0201020c07150306150207091d061305010204091515030204060504141c0b0a050906011a0f1207050a080901090309050f040f0e24100e0c 69
    0x202d60030380000c6003480804040d01221041000e01998613150716502414010300958040440a02c045c04a83e13150802108400940c0c019a50400d560394001082100103010002c0c880403a0794002d202103401e1070b01e241e00300e0300140d25040c104138400451903d03916000848507030000c000c0700100100d220624040c0e000e8000c1e40c110b82c101d2820100203851900c0d5100c156000c807003a000d141826071140d0714064080344154001c01c0e0000740c00700170520624080840045000e03c014000d1080400c3c03003604405c450300e09540880e03041000c0703170078400b0a200d24001c0e260007004071380282c0215403500b480d440c0c0c03810b02d45d10410030f1060086046042d01d02c0060640364035202c1600e03880c00d140f13003062000f01103602c1403c516012582e083c2c00305508e8081440751089490f49038480041c11414a0104003118190300541c0354019100c4100c3d051080340e60080419414444000f051148801c082a198072500c0e11079188080742c50800704403801e05070904440448011307295508058640800e214003c2c41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 114460989 1250 114459739 114459757
    0x90a03110312030114011e0e090403090b070804061706010e010f03020d06060f020d03050f0a0f18060b04060909050c0d020316060503040c09090201020d0e010903021f08010503060f040314 82
    0x48084000a0954010b402d1480008801d90710480400c3c7c000000c1002000300240d62070004081007200b50311810302c090760642140c000d0400e000031566450ac440860751060b18100d0382070304040342c10020300d40c11013080030191204250701105851b024000074100c21008100504010050028252250196040303c030520590074042c8441515450040d108070301444407980144200d1900a02d214441c0c0f00b051701070004010509000d841f4040e601c00601048400441d00e15600d86098101c040c100c001000c00900c5100045a4580341714100030440b41c6a80c4150141e0b8200240880001c0380070a0b0b513008030a040f11103009000b05030000c6860302c0b07a0041d603105800038010001c1507103034106010f1071242d4441c0a003881c40c10307100c80140007a0b81314044024096440b10050104032409614401102c08040c03400400c00c560b20b40029940d401e0340341b40040c3c411001c0c01004042d07540300c6800d9014141c158024030050500c0c401e42d54a030800244044d0400141010031000d050b240812908410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 114462239 1250 114460989 114461023
    0xe01200d06180905060c070506040803063f070311060c0102090a0b07060501050d0320030c030703050903070501020c1e1825080903040303180b040303051905090a031103 74
    0x2c04022403500104a40e9406544c00d05c5600700282d20303414160704035101550b00801404039511036a403050740941001d040d00d81e009841100c1201c14101070f441400c4105424590140340002174882c04017040c0c011120110a80c002c10b0040c00801c500000000300040b0942d0703140d0740c542407614424024014018042d070b0000d14208005030214068018000c1d07603024110070040d82e66240c080114050f1400170041c0412a981840564200d0501348807902c84441d00c20340740303041e01040400d0700f55400110200c010a00200c0c11300b080c1d0608011881c0900420700062614040c550001810307140c1945c030641c4a005e5203408072070951a0b01106800840c91450200c09a0508030514080726034203000303940603290104080b000f038611510104c3e002da031030000990f1403d0300310303113003151800118403401c51003016811000680c034a000d8010320086000c0e959064913841c51036406a030b00e124410317001c0f04000c4103000d126010742d00c607080b850413a50302c0b410709a900400070b400b01e810560390000e808814 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 114463489 1250 114462239 114462269
    0xd021207032003450d030e011a040f090219061101020a0503011e050a180e0c01080613060506030109020307090905090d120b0a03060204260d0305040206070f080d0e01200d06 76
    0x11007000900d1030030545e920f45040c88a0404d801c0e4071802c0354541043c0c03802380500710318070b03500f9810715038000b8044d0034803181c0200d42c0d60740300d07004555a88180015072002a0203c0703401c00c110703580701c04c0440c0410b07001d100a608d002c007904001004c0d80410b002e40240d00040c00d10700b1104140b0341c00018001c0001900451440e966081d00d003212a0a50030082440c4e411706403011107400c1e011441c01410b46058440301c0d129200c40060188034401e101c0002c5115690318404242691100e01441c0280340d2998096134078600746a00402c01620f5600c1409502d00f042c0c28011040004981e41005200e14684000c0500350025000054040f104590380c000740c030402c002c000c2c050340e600107009440c84442d0b40341054041700759074210b00741203180201d1641c100e0f2f800400158402c0e0000d540090006040da03040011584901501c0d240b821401c0321340c40c070001440b00595a190080031070540450f8000c002156800036103401000340c070b191150480ca800110707007805800780e1740070b140070f00440c42080303400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 114464739 1250 114463489 114463621
    0xc05060705040f0603090210210e060a0c020a080708030c0913060501030b061c020a0905030d050301050315010303051209071d040611090a03080d021207032003 70
    0x1254840d0107402c40030000e003c0d000c10024000d0140707a10340765001e0810190045800400c5403c0b51091101545031458000102480360f0603014070425102510050011801c15446a400f01d8000441040a43d00503101c6400800c040c0c40650b0340503a00101019aa5030394500c0f111807601c119160340d64404514109020020119407060050f01d1003078030200500700c2032004008044c090000c600389804103002e00c4000b914015000740000c140141001c01c40c4075202d500090911181840c20350004401100401203440d081004070628039590140b03128650651b1402000c5114003013040e003242440c480030490840003000100d00030b00780881036110443d1880e6009548100a480903030b145818a0500010040b104040740c006041c000c2060b041146182d03961961600011440e0140c503a0a000c0020307103000c03619809216107041c3d03230300260340240000041007684078003041c0d100d800f07814010800e581c00344001e80c903240280d500111144d0b800889000c6007000c48448007031400d580e8920b89901c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 114465989 1250 114464739 114464747
    0x5060f090f04032307020607051207030503040515040b0411010207050a080708010f020301050307030201111006090606022a0f0a030f080a110c09070305190e060a0b040b030a11010c050607 82
    0x40110b1103981d07505105081d21034288080b000d07540841300c032942c040140400516152000f07051f42031081094a0001c1a220a15441900842e1094012a400004010403c10248030101151040890702c4078141000e1300d41c07041030900103000405031090460384c03079000e07070081044c00010100100030341440d0340c032426a15181c0d240c0e40700d010015820041514a00b0065000b664181c442c041d00906146155400440b040f00170621421164015010600c034010002c1c010100034000c0308502103111450b01500a244c6000ca62000408244011000031525401c41c10400c54440c101c1e03004540045501c0003c14444441d0300045c414640346811204021034140035028000701503d0b01442b1040e80f80300310fa00c070000c4001c00c0d0750000401c07002604250090b0300c500d811003c4c2001a5080f030860007049400c0340c64029000707880d42e01c90001c006011416001c1c4881c2d580080c1c3e03090204d015100302082c0d5074288210000c0500d40803c4161819901ca0642d9001c40b5410000f103402504019001078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 114467239 1250 114465989 114465991
    0x1b0b011509090902030c0427030201090c050f0904020907050405120106030218010609091104032a0501030e030301030605061c0308070e0619230d02120105030a1505060f090f 76
    0x40109814000002e605507080c843c0300980381d009000b4204003105001003000400c0911940d06101600e0500e203030703008144005520800d4800d800016074003405050203c00c521660744401d10030460700c00040c4c810f0b2030300c148668200f9415a40d46407580c171440030949443c0540e0b049943c100d40ba1400074034201d10150004800c072030007914038002d03101c50380c0080d4000380740074003915001c0b03940c070741040104207100d40c003c40c4411002c2e90300700e007095100d40e2401c0c00303050306170000014248903200d034006a21291074040004d280900b001c0211a0744c0c0c4400343c3e140c2c081440042c0070702c4d036104000341300d82d01c44202601c144034103000c180c888030803180740180c41c88506685803000030701d40e80d1085e002030814074100d400000c400b510755820030443d008202c681c1c0700ca0b01048039080301c45110364003001d05000083c4c1043c0707421034000341c0c40302c1c100825401c03c800e050f413206109500805034a400314000b0685e942e40b030810240c011a032a550507000c16449402c50900a800002c20ba0030000e030010409001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 114468489 1250 114467239 114467279
    0x102030c0a200a030f0809030c0d150509030c0c011803020607080309010b0303030f01090914010507021011040303081b090d0b1602010b0906190902040b040f120b04031b0b01 76
    0x500b9002252000b40f1050b000c03039000c001d114506034412907000c01c2c45031014100b601c00003801c881c21942c030304000c50560b920304034003110104002d07108417203420145d0142a600c60310a1000710704000309140b45a070380c1e021030036040c1d040c0030001040b0510b051224403842d002d0b40d00607007031503a40d000c14500b040301d47c2d10480750240c45510744031402c000f500d0f000c800c8074040c40c0c06001421485c0d08001403131009059099040302c3d4145c40401c40000d02d142800f4092245085030090001868040940420358150810010b0711900c10482440001d0f0081609034201c0c803047d080c070400720452410b08032240304001d1400ea1007c01c0201d00420030540d4810385220f15a00c3d041d0038191072500d44141d082e9601c0b6561030b5030082101001803504d0800094260610f0207801e9200c3c0703016620840c04040368001c0d004100c94440c00282407001400c5014080001d0144030b0b0001d605d1007480d19801117034070015000a08020f544118001001040382d00d00301c1080d0013072018001c4d540c2d64070b103c1803544820404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 114469739 1250 114468489 114468533
    0x2160605071110020a140105060406080307080403060507020a0f05010903030b010302070506061203070c0320030d08060d0804090509070504060b0f031f031403040e150f01030b0102030c0a 82
    0x104006218409035203815502a80310030144003240100314580c007001d0340c0d1204602c40d2011172000f0680d04445507018000f0000002281c0c140541403109543c066040104980e10401141000038004400c8078101c0303400000c005101d071100300c8102d05190300f5003070160603080200810405c0c018198003052500e40700303441c1000501e5001006409038001c400015009801c040006085030514088070040c0d44191015607160a00b2a507a0802101e030a4006603480407070909144482500920f00001045c0114004d01c401c10540e040240100c0b00240084e001d9441e0b00144001c019100b815076000d01920b0009002600d854948103580e0412441068452404c0c0000014038084000c1102e81c01d08003645120729640e142d00d41030202240c107031000200b103503481c0310000100b1003030b480c02215060b03018051956103140005040c0b0030b4070041c02c41d41d048070341c072000346c242951422003100c145a02070030041120700c1c50b800140c0c114000d0480c00b02440c05000119010031000750100030049003103600d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 114470989 1250 114469739 114469783
    0x4030201090f120e0906061c0209060c03190c02061b07051201140c04050f220203070207031b050d030804050106081006051c08160c0305011407080906091e010b0402070302 75
    0x10410170811410394206400c03900030001d45000e80c0502c400c5402d9401102c1000d480c003641c181c04518554040d02c070f00515a0008200c0050b22a500480b03107903241c5040c074100c100040160001801361040402400c211705030480e010718425400e011050051400418101802c20101c0100e8040c00560b03d03c40b141401000c0040c801c0c49045003610161a0041d104d011441c3c440000d00c8003041c140449091410080d94440b0303032020300f9000861182200b9405001180c5c910b107007a10070b0b003846d5582c4c0e2001c00713100c4506004645920f000c01d1503043e018500090107403540e0906074018040307900705105034003e4a2050414481d40e402200444074140d5102e40c078000c488030078103d0031071501001846020100f11030262085404110000c0c0340c02503010124450f925512142100c41c61b001c0e0300d000c10044410030181940040d2116400031248014200381d282414405c3d40790501d21001981041081425515500d42503101042c00d000141c0115034a90702c4d0b050103903440380e00076140305000c0b107054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 114472239 1250 114470989 114471017
    0x105060d1e0e061027060f090603020a12020306040f02060c010c02010e3009150a08070905090402010801090c0302071407080d09180c0507050a0f2001050d0504030201090f12 76
    0x81c0c180e8100c6590620200030b031031050046045d400940c0110001c0c03680c0b98503010070710b0130b10300101754000c0841d42c00000d5280e2640c07050004d060340c035502c0254250404811140507803001700d030480e4001c0d401040108421001d01c0051041e0085104070384856107082020300c20182c05504c036074140c251000403038511051000031410028540009c0004502c6620b030600e100741440d00113081c0c40303040100603079140781b0483c9500f5240e030444c0280c01c000506840c01e112160750054a038802410040c0c4681040749041d80010f06000c03410b1280c0c030040741d41c80c2904013200e0700c81c0e81691340b61355210145201c10105070519035a92074160060006030300650161804d61030003042c00c001241c0300206548200c08881302404020301540d40c00ca01481010441030340040c4040c401001ca0b544240092805602d003410844001c03905c00b001c40c840405c104c0200070460307070018143c40c41d00189541c00f103040d17034862808a0140c042440001d201100000d80103040007084000c50121815070f54610004580301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 114473489 1250 114472239 114472261
    0x2506050f01080d17090c1e0411040815061906030203010311061e030901092f0102030c07030602130806070804200d081e030c0405040e030406080105060d1e0e06 70
    0xf01c0c4440e0208698a42c103216115882e503400e58000c0c01c51003a50011241034010400240350020840094040e1844490040c542803060441a16170440300500b82814000301c190b541c908581c88101c507284510028005558003120a5000ca004c04030703581900d0342d1250060007030340081c041128680507c2844101a007041400da50600d0f4102c1b00b003200f14281020008500d500c0034100301da055403a04018400b103541e0f5844054903a55202c2c0c107c000000d90202400c550a00344400360454104000b0b1201010f4001250415650010001a940d13004000d980c8000100382e48541042e01804003082703003061700702641900c11402000324002503030724030a0414041505881c801d91001040c03d850011600f802c000d8607002c5c144c4d20702c0b0003074484000740b4580c0c0d54004845c4071105100000c1d00344818149030103088280000c0f0720042d0305090600c10b01a02c102d03014000d85014560200d0b002c0c00c540c9080e000183c6d00c1d0026864001038000c2d8210310405032159480b42c08080c03041801081d0700c4484 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 114474739 1250 114473489 114473503
    0x1090b0c030306060708121302012021120702070609170d1b020919060e011802070302070b0d06090b0f150903010b0a09050a0b060a0c02062506050f0108 67
    0x11a201451640e41c6080c10071030380341c10225086d01e407980140314800c0c1d0482c0c5030040c5130040c080c0d55a0003081c04011320004048821299210040401e036a00d1003c14400c002040007450351464615400c90004036140d107682d0041000180f25041d02c2410701ca079654004c40c07902d056417500c0d80d801c0061078a412a0f034400c1c89a040800300e01c4d5014144065040784a000c515411180b60806a0f0180c6a260001500e040d4143c8030ba1440701c050040c1c419495100d0700c0342c42c0080c1424640c0c02540d616280f034402c119101c42e8001c1d0750f503a40004055080600c2801705402400008041517100c2090100d00030080000e03018041c107540c60301c07845c01c8851601490004121400901400e03110404c02c0c1090070a03048a00402d4041d9210741115841d95241c800b02c0740a0b00e00c00c2e200040074030b4003455407400c1d102c00b070707020034080c074400c01c817a4644a80c400740300040c080d015500740e9500d00c12403c880300c4007038201c0050349990418a82c25010004682c001c68040c40401801c6034407a40c881c800c80c0d85640b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 114475989 1250 114474739 114474757
    0x602030f09010c050a0309080610080604120306170c0a050f030a11060c0304060210050a05062d090c0d050108011104050d08120705030a0e0319050d0905010606050901090b 75
    0x12003800418a40c106500081001e0501071500790021400f50f540c0354034100712032a0403804a00d00b0035040c00648810066180d02c408a440d226001a203040281602c90602800140440805859031141e4a000350000001810004030001c0520941c0d5903464035150b040102038821840e02030000384e40e02d4101610f00c4070000050192002000b503543c0c9400e00c0529400803600070100b4001549001c4061000c0d100801181d00505a42103c591200e01140c0d0024002010340745000240314440c1c0f12440400351840d08000045282014070010000c0e9804501e484c41d800040001000a0303049000007901a45804c0b400901c49a603c51205500307039807030114942c0000c030052008005503e407128468140e5070045001c0385c601000d800c0d011100b032900701c5018011030000003e04c900e5079028852800707122001c1024608001c000140032040d001c0381c8180c1c50811501007404881d2901c15440310404943c005d008118181d035800002c1c2494100d918620301042c400003001032002100021191810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 114477239 1250 114475989 114475993
    0x20304030f03020a0c06020f070b010f0b04150203040905100512060f0703180203010504060e160e070807020115030308090111040f150c290a0c0903061806090b150303040602 76
    0x241c0340300412002508994482d0f82002100c0782c00f1800700301c2501c018034007455203108450340d8120034101a02c0f4210107a018003100c4282d810304001e0000440709840c25035550301800100e818462100324910300a9130056900d65103400c1c244401859500660070441d041550101c1400e07034041800303a102c0e142207d200c8003910741c040000d90618402c0d805210f400b00704040d10b80c180c0b40030b9000300b800c6030002c03102220143c4d542c9070282c2100b0402c11815045c1090920780c80b00e094207056642c444290054002c0b418003042801240d5018001e4201d04400080703104041280740e680d0400074410b913802c2c0c40b000680e51810500d10754088200f03049130f00b07954081e461042000d1520302d821602140c2c080f281002c1040d44c404800005400164240e51400740d036031039651301c184030182d448228030003070200c0c11250f10302801c401c20b0030b07089900d42d01165004100002c8030803540f442040881c04041c4020407051405491000300704855240328000d1a8801e080101c0b50300c22006e04d662441a030003078001507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 114478489 1250 114477239 114477257
    0x5010f02031305131d0a020414070210020f090306090a030e0103090209061908070906030b062d06040519140105030420130e0a060b060906040303030506040e030712110102030403 78
    0x7414812107100a44040315070014020a441c40034810321091008034075850380104071021b0a525040c02090507401050307a20901d242000300003c0c0d43d42e4480c85c0880d40c1e80f5004a500c1100d0010041540c140220260a95000381b03016510aa01d800da107030300c2200800e03080b0008902c0f551080c4030305101c11342d015140c6001c42e29050704009905070700d002c620f0184809080c01050070f481c18844040100301c0c0710400f02c0c1450071031810840300c00000300021300400480d031080c4500c140c64a80d100c00d803850451071407049150036001ca500392003150022900701c001c10b4031101d585004012101c00300d81891074a160000d00c040011251480b060318090680101d101e840303814030850700d0402c46040c0303008100c4444001c09000300401e0395003100360f101694110030689410b10030140a00c80c04040105d5902d403a1504407000100a4000c0d80005820551381d500010000e4845500c20111907808004890321005d5074944114071440a5083d4000240c000c5014044402c050003036070300031949030300c6083d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 114479739 1250 114478489 114478499
    0x304030f02030c0d0b1b0a1e110303180601080a050a3518010306081b0a05121f0c090e09210c0c0a030209220503031005010f020313 58
    0x324000e1040c00380c0c0c0c90b0240054552480c0d4669009440051080c00e0340380291030708900500c41e83c2000e402d103240d52a020017100840750790046640d07000e0800c3e8806c50a00304106407044992000f002d000241c140700000520481c0d0a000752a040424040011075103260307280d44001c0e4582c95465030040c1154844e01d4070b800013998680107208000341c40c410301c80104014266074840d440c842c100040c20344000062a01c010a45501d085c440400c007800d0521000d4586041c40c1d548084150104c0100c40038843d0380c145990300d010a0600400f0014040c50b18010045491500d50311800344c2600c1e80050600d4101000566000c0e1581740c0902e900c4d80c01d85145400788060040b84000d1655810b07008241d407074500000034100341c1485e44001c4080e04e0b100c0303d01c031480b5881c01c200340304124419007004408100698482440c00d03805440a654a808101030030400d20000103100b500901030f010120030440c01c000c0a402074011500266101c403190700c01180180d80301e225000011602441280c41440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 114480989 1250 114479739 114479753
    0x3021e0f04030b090a0c140103060602010b0901170c06180a05010c0c030f03050c06071106060a05031209032406030709061202091b040f0f0602070e0109050405030409050403020a0b0a020a02030403 86
    0x384c008400390a076810f058150740e4002c08075940350852145076030040f503103442d2035034180718103c00b030a064002080000513010003d03070050014071038240071341800e00c400d030400b2000b448250324803200030305501c2e1206544074403400d040c3c048120071360043c0d1565500194640c865282128400c0e0400030b80e045082c21a182d80c007507640c4001d0144d051000c10400b900c0850020450148030b02025582d0b81c040001a40046041030406420144181201c8000f40843c5e0b80201d0800c40541d04045082e580d5503000001c0783c00c0c80f00c0c0740d03182891082d4140c000017101c3c0c8640b0100d403040b10200c054a01d03994591400004032145400350740e0700c01c0103012841005017800c0c00603075000030f4403a40710f1120007240c0c442c001480c2d10503000518081c20311074040000248081d00040684614005800c095007010040c484920f014451841e566403180081380904c041403048601500c0100c1e4148a80d140906000c1d5448000d050111850010b030030005149071014800d4603952101640070754030f403500d0350321070b0300b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 114482239 1250 114480989 114480991
    0x60c170a02130b0d020d0b010e101d10080109050106032306030a1514090102030c091509090a0614010e01020d0e01030209030a29060d080a180603021e0f04030b 70
    0x34401d1240100041102990800135000744d146005026990740c054054840a451500c0d64141c140081c18100c81510358600040301c1781c0d6803032482c200c8010550094809104114085699008480701c08259540d40c0d01c012881e040e1400080c040c401c50741d94030400c4080300c0d80c3c414142264021034102c138000104000c50a6040a001000c9800c4040c20f80c54901040d400041c0c040c900701d90b03400e200580b6400d01100258000742000003142580f030405002c0d69148107582c22244103019403607818154181000a45191440c05003500c0300034030740380c01c01c84010051406121142407030140c0c100c0c0a907114000102c2da14406074080c09042c0c21401c010380c1d800b0540c040c02414141c003441039505980381084204101405104d030507150406a03100741c00803198025500811551074000c204107a01c0c0c40d503a40581a80c4000d80729920603880e031040714202485881e03083c2c091828440015090f90640103000c041d80308008100c04140c611019850030f00c40c1c000703d80c0c103000c8240000c002155100c1105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 114483489 1250 114482239 114482257
    0x20a02100509040606050405010314060915060706020c01090b090f07140102030417150601081e0a090803090c0a0b07051504050c030708160b0c03070b09010b0d0807060c170a02 77
    0x90342c00c103120040000c00760340c640e8014800045000c41c041040e0f683c107005880c0c2800802c0385030002c505000c000308505450080c414031089114003840060b685950b4210b4590030342000046465840030f1300c42902802d403254090f41e43c007031030302c0101d00100d0300401c01c4030151888a00503d911886e18031801e106001514026043d40018000042c1c1058215800d403a29642070700a4a11703c1c5a1507001740c00007501401d05070400126404103e50180306861030300d25007040b10b2280d0841d03a204100342d03014202680d001042d1040120030f000c12084005280002d4a504891010a003600d842a1440314004c0540181060713121440b004841d0541d4001c00b5045401902039640c00b6540d04017192901d4020350008010383c6c40038000780500080103850102030080700d2040761420b40c83d910229070768001e10401078581c841160121f1507020095008916855003d00700c42070081c4e00d400c0c03081d8190000c05054543c41e0804040c454179038400c0c1100304c09080045078040507034035008040e43c004d421400035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 114484739 1250 114483489 114483497
    0x7030b031f020d050106031b0302131d0a0605010305090c21120a0306091a010f032403110d050a031b0b0c030103020f0409080409020d0f020a111903020a0210 69
    0x100301040c80031000440c8800704400760240c0d441d0071036a00b030070860b041680680304246c46c104a03408204034072240112031b0f100b18038016844d1400240e9696a504442d80030f440e001c203058114000c4141a4100b040c07161a84a10410041d5515030043d82940c0040b548103000c0d4000a40e51078843c5403e6501d4890300d006501ca11a048841c84103080c98003ea900752500c15460210b01c0340000703070307044c0518000b0f480000381c140b001202d2044039041060788041c00034103202c2082040a00c6502c60351101c9625011901d05002c00011400b03203910000070342c041640c0c181080c0003070b03c000b130501642c1144c4050b480320061001d2911514115400419203001803141c5c402d4429480c085010320701c840740228102c088003a625459841001180580e545e00755004a003480e201e10041084001510211a80080301680d2500c4543d00107008242c0402403118031032000c2524241c1680c080e85e507103c0116460200e84c901c140d007190501c1c055805d00b40040050780008d281500501b031841e04203502ca807403410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 114485989 1250 114484739 114484753
    0x1120c03050d020307020306090a0b15060d09120905011706010c0317010608061807021e0102040f080106090b0603090a11060712080403030c05160609020a0b030a0204050f040b0907030b03 82
    0x140d060b052149645801e00103900101c5d10f9415850280006a00507040d0f00c0200f5111002e40d407541c107200d0b8000c080c089480301002030780e4059100c08040b0b0b88000d5440104008440c914030b4190000c5d044400705030005001c03207034003007083c2d40617400c0070484010700402c01e0312540c2c0b44001100c3d6401e00d22021000c00c030b01258111940c500c08003445020703103050784071000245000b90900c1201c0000000c104c1101610354284042035401089452040c55240c2c0b421504400074089580a48a00d511110185008000c0040c1c20b010640c8000c0507074a04060070301c44244d010701004200e00090381c0805042d040750268200040c5c0d10700c9001d61405000e4001810088241c0352880f07100c0700350000c04042241d00302040209503142c4951015110305041040c10022001243d40b5058042c000c010000c980e2014001c1c01e666848500b00c0c01001d0307000e2440e40c0c9160008410019400c80d11489000305140c040c110a6450140140d5250110284c4640150390b80e41c0ca044018021100c4401c0d01130089007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 114487239 1250 114485989 114485993
    0xd0f030527010318121d0d06020c1603020a060c060b0d06050403020c1e12120423030111181302210a0e0c0108040809060d0615080c0301120c03 63
    0xd078654015540510112900700020360000d420b031826590852074601010f600600080d0020400c40d100440c1443c03c2d9005001510000c109006180710326070f807000038030020004000c2943c008000c0403d8400550301c030701040a018121010b058000258050700407a81804094455101d000c00b42e40107000c00306001200c50081800410b11020654080e0b454100308000c1c10380401022103038a005a0346054042d600c0310441c18003c0f0a10a89882003030b172080203a020050400c09402c03406c2034000303144d076100e580d041011007500303400e45038290801e4515030407082403070103100d5203042401c440d95440c9424082071051090b01240a02d40c1c3d84183e26103406c140425542c400380841d0040c1c107503111420f10509403029a402c000a020f04042c40c00c3c469195140701d00810f8a0309040e500f070034101f6003600d0300e15001440e40100c0520503000840801e0350b4139025100e402460442e034010087c0c0c29292904c41040310302000468a5005040041004120821402104e000424060156107481d69101c1e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 114488489 1250 114487239 114487267
    0x30f09030f0807030e090c0f090d050d020d0f05040f09090305120103030905120303091207050f060f01050a08010513081b010501090f0e0d0e01050d0b100906031503020d0f0305 77
    0x2240305607402e80c400b05a19081680140d400303080340508940d204c04c1450003074210a540c0c40b9003107000700c3d900b0005c102c900ca03c1d240c8641c04401c056000c01070380d05078903e80300000d5036414030805084c00580350b04860f4074564014004c41381524010b4104000c3e042c00c04848a01510134600e0813400c010b01000141003140c1c01d903005030b01139803090b6102c110051510b0b007006170806840b41d04101c240c00030014040d20402c009400661580201c2c171003621900b00b410010b041150f0807140c00401d00441040010403285094014180d030400c5841404440d2034118950880704112707040c0702c100845164600218141d000a402180c960101d00c0503000b5003003c88a007510000e13444920810b031520300c4010010b01c0d50103180700c0342601000800552100e0000102a0b08101720254180a00013810b41c595159075085042d51340c501408100341e0280d04a40140440264840c410008e4034150016003621030110f2940116500104005c198464607115250045001d910803014450b040000391141d00326 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 114489739 1250 114488489 114488513
    0x8070e041808031e090708071509030c080307020405070305060d020f06130906050301110c030d050a0b0d12021b010f03110c0a120f17040f02030c0909030a1b020d030f0903 75
    0xb095400344c04031100d0800e104003e40000d45480400e4000403004d01a00c1000928007080b14944005042c5121005a041d28002083d4102a0074410308003000b060340f0300c1c0003005000f458404d0b1010044e594488004404446e02a900c0941c400702002c0ca4102510b4422450651036030024035061034505041d030007001c0c1015582c4207403800c4d074842000b04050303c1c00780700e00700408600d0a403407403606541c0e0080c0780c1c6034454903248003842551040800c230003040c20780c808020301c88040c1c4180c00a003d035041000c424520a81d8641c018814515400144d0119140903d0000c0c4180c481e060192500401a0007a1801d070300c000201c40b4003071148a01007201001840c144c1c6009410890f070f1840c822100400a11010300d060090001d650940d8110b5408503400d250712a800c2524403011034a9840041d0500c46050845076018991b5020f2282c00403001c4002c02100c05035071110503404045040303c1b11103000d004400795020019001e49004607010308006240241c151400c0c0c041d0310345a941e06000600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 114490989 1250 114489739 114489751
    0xe0601060315090c08060105030711030a08011701060602060703090f050105011410050a020309010e06070c060905040b010e0d080c0a0b0106030204030b090f070b090409080c0303041208070e04180803 87
    0x10326284201c0c0412580700404028080f03000c014410361a9090300508048000781c001d40c1084400030016000b84e201d50700e030442c0c40f92240c050783e6413a1241000142020428010011006041e40d034820b094035052103441c0482d015074000e064565181e500c284c1c0213080480c8183c0e0b2500130a181100002d10070310400303000e425940d49200342d60030540e0a00440da010b00c0e22403000d200040050f140400c0d000404d0300e00b851000d00c1d241018071202c501280c0765000760013000300506200c030300c00f00e41310f030300094803070142c0d00d081d14100122a5400011141001204026504000e2101c00e05020400700401813000e040220201c0360007910036a54a41002001d900100000364085014020006101070464200b008000101120003000303010903241c90b402c1c85602072a82d400500940c1c5a21280c20101119401c811910303140d8610018031078a9610844081700c00340d0300b1900d81c814050080c1055402003001d030361340c8406003180000384801040040d0b070f0744c1d041c00c0a10300d003840040c0509000758031402d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 114492239 1250 114490989 114490991
    0x705011d0105060102070305071e08010203180d0201060308070809060403120f08010905010825120f0203010b03011808031003080706020a1709030a08060613030b0108061321030e06010603 82
    0x390305030803050840314040d10940c11504074282c20404aa00000c0b017100f0b5441991525109115100c1403d130940d8050b44880c059500110400145040040f034209400c012201034450401c40403104900b2a0a40d010080c86408140030b0803000c40c24520140003400c1001d01000d161039280d031500b00c4450780c0c0030b0311000015099035499074001d901000b243d004004010f0140300e02c2d41411001901c90310b44100c0151002c81c04908030f4207000c3d82c03041400007041c407945040090001e905010301051001c10050380250709140c20038a41e414148240050300c40d40f035410103042245980d0f00d1040d544040c4c8001c80070b0700b40150100104501000510345184039100c0140ea882c14004007400307081014030b02468542d0550100452640b020003101d044440e2460480034994500d00080e4282c010844403c0344480c0380748001c020003804892060507200c00c80d08850082e41c0700d060070f043d416040f05000301100894400388900c07071513081d05020443d08a0402082d5007074503004c0f643c94810240c0c4408006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 114493489 1250 114492239 114492281
    0x307080a0614011a0a0c2126070507050f120c010b0117060409020a1a0a09150e0603040302010902040e0607170f040f020312120609013602070501 64
    0x5461160310350010007048124003c1d890b142111041d800ba5a140d0061401c0000d03e8189191207a001188021341c000000d0b140f00300081310241c0702104800f0080007103084410000030b0305152241e10343c0b00718034603481c042c2c03103071781d440d4080720360340c002c004c044940f44100101c003541090300340200816150600c4c100c940302d11100c1401802c0d06e5aa80c1c20f181801041031080f114181505061355004005540c0818080c3d15803011074007828887e4004162400341c031585000a5047c00c00402640929a40781c0701800e4548101140e80c50081d80c4101c0800c0c07502c43d4099090402c000650b903c60b0081c000020b00907401d4002c601924400e800c02c8040742c204078100612203410508803500c1542c40201240fa51030041c000c1c3c00440c3d030140c80a8000d80b046800c035021560104004017800c100074824648900e0000700318480c484003a6a06481110940b0011a000d80f1101c02c0c50340d821111680804416040e08204407100c0d8003113002c0b2901c6400708601d00c04903801b4014541080e803550620090 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 114494739 1250 114493489 114493493
    0xb21030c06070c0317060a0506031305070b0c011506050702010f030b03010e01090204060b130504020c071a0702030d05070b070e04110a0c0209070306050303070605061305090a0b01050411040b0f090307080a 90
    0x1010140801000300c641c816021b11039146c85103c0940e007590b405640095481d20360981c04d410000c50303290000e10078450030001094640d41200680050361069000703011220444032031165012007030240c00c4c00600107001030005584074102e4500b0940f0b90f03040c00502a04c2c0100400d081d12440c008980e5269110f040d50b0741141030502ca500014041a92203505003001c00281041540c05842241e12031a0081a94840c51505120301001003820064044515100c0a241c90b0301c0d8000b15000d9219000d22121850458002c40c00c07283c407154005c1e002c0c1c81c00da6a4050039160300c0580030880c0c1d08250740d1102090031440c1d50008040d0034546407110012100c4610400812000080402003014100f40c001c100b941c5002003174401c9554131160100d541ea5854020035403050310070102d508036504090078031610560128a140c08203005801c816034580c3ca41c802d01040e182c0b4503c15841102003004100a104100f501410b01d0100e00c3d05458030b4072a242c800646444c0b01600800b169401104c24041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 114495989 1250 114494739 114494747
    0x3021305150304120906140705030c0d18050901060e12070b0d090b1b090d030c020a0b04082b030b012616021606030209010302090d08030612010b21030c06070c03 71
    0x5204e034000e1801041c024209080102031061b1842e032001c01c090003080403000c1000920944001c103140f00300316011030f4001c40b0002c1454051140c41800c071040648081198145102003506075500e54440c40210610402030110f9616107031170710300d82401070b95030101d40710b5400c400074510007800d000c001c00d01c0100380c24074090001002d000080391101d160303404150421540301303130381c911a4200c550181d82d41d228141038500d60074240d8002d6001c0301103000803841e60760400151082d904950308803075180030001500c1c00150312402440445603030440c881d902a0344a0303040045a0381040c50900d01401000040b0301c01c21081d03005000850861700204500c4407210400640d8084040c40200310200b5040c03482420300307006000d040c0c100740d000202e00032507034007940446001171405040f4101284a9051403c0250801d0755094803480041e0649210080140918018004000c11800d00c000f10111600900b146450a040030b600051004054200b0f080c04031a06c1001107489008442406180c014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 114497239 1250 114495989 114496013
    0x31e0f0506090f0c1f18060c0b0f061f05160b010527270d0305041203140613090b10051507081903022b060506030402010206040303021305150304 64
    0x18400c0e030044e503c810195540030080e071590355900c100c800c81508a800121054030342000001d11000c00c00e6400600340c0d40c0b01048410050180700c10094645a90401000008007603a945a111501e4119981800650240400c1a6501e4104240fa0403441d65620405064817a02580c59030054001040282403080c5203840401c08c0441440c0201c000f01084000c401001e0f02c906800800410b5031040100c09903100b9440c0700b0042c0849445000e101c100801901089604480c10b405212061926a00074020318014010314004514259991030074400403501c0014018000d070f0702c809000700403038031041c0020700496030281d07119900c1c0d080400340130084920603c074140807401000020040f0725604240c851890301814548140e0211000c118082d005036440e04c000c610511040c6100030040c05121484c5501032141841840e07078601c01c228203808201c81c0a40980c00c00000240003d10035402080400e400d010280f1400b5201c1d40400e800c0c031803240c400141690008140018010898044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 114498489 1250 114497239 114497263
    0x100606210509030a12140405010f06050603070219050c151e130504050601020a0204020d06050301062103050f120103030c0203010f06060e0f0310020c01090c060e0109031e0f050609 79
    0x3401141095140b8030340d00d20a4280202c2045a1031100562000344c64012644001000040c0c150f5401c142c14084c2c0201540d103070316408103282403000503107814010180c1b84191440c0d0040c0009886500c140c0380b00c0003100100321810b024142c900c1106655007001c0348205a140f22107951074000060645503c4410051310f480200d02c00c0c040304a0341c241d440110b200b9960b00b40c801041c1d039111200142e00d00030354080001d42c0f01d03001045400004203541d0100e822500d044000380b080942e14041403c040309803080250100590741d1204011074090001080c108682031003030740c6000e10381d500c2c80c999502c081c0c0003200014102142c503015883c00b40540034180640c1403040244a1800c0b1000c7c6c046520641e03000d0055201d001003203e583c1d010b00101c2d2a102c00301d0025995141071a11a41c000c003000c10048030190310090021908500c100681d110800060f142c05c00d803581107440c0da424600d82d041454240900c001216030020b0503466040031034511541c003d00c51828208a800d007411100061 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 114499739 1250 114498489 114498491
    0x50103020d02060a0e090405030315150a0e06040906080303191506030515041b1b08090405270d141c0c020f1902011409010c1410060621 60
    0x14009a5180d00711110015412074502d65074036013000c0252440d0001004141d480a00c13103041005103e008002948202e0304d41a604138140c4022040102107a0001c1010384405070605c031111549002c2c114a20344501c008103030318281035940c000031080c3c940e5034000070f4040d0004418046000381030410001e1791041624203120002d6524403410b00d04a0502c580e0007059111030202d01d401014494000590030054020701801e4007421412101000c0120780c0000035404e03010750148000f03500380d89900340781c3c025100c9103001050403c010241c1009445007580d90260741c0c1101e907540b0554004080710301c0107000380c11182c218440c081c0c140c2140242d00d05400004002400c13030001115140c2e4003074040c003080090708000ca010f081b850100ca042d001125131040c01c40e0b04940d622010003203130184e8800d0781c840c507080501e904c05c10b4090062090765801b00350040500702c0003d000550401c0741d101400d003100c00e20069204091300b41c504550026001c030741e1210071007000982c11005c0d0b2410074000c0c80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 114500989 1250 114499739 114499741
    0x60507020d031809060e150306061011121210060906020307240c0504090509150117010906110c0708010603030c0b1306020406030203070f090807090207051501060905120105 76
    0x81440e0021201d40201003061164a01c902d8020300840f1030b020f004500d00802c1038030f07154901001102410b50300d14000080b0f99401180902c2d0006290f407141c04c0103014807080c0541328200740c0b00c0029030120400036018108c090710020a403c0c028040b450200d038808101401d04060814046215400c50020007524070000d005060b0000211141140d04c1b860403080020b44180c1000d0402c0516880c902c40341c01d00d4611100554480c01400644031030320300401c0241c41d1119116900c017448072600a0030103a01c80108180c60819000b01c4503041000c002040085041e074800f8211040c807000401004004542140f009000300046805003a50710000c0091a045031000303410920309480042101c180840081c5084102a00285075141d100400795203681e120380b030140194208135a484c00091030040e844068a100704a114100da07050b001a014080c1820b200e40c0c040d42c044203003500c1a204000d07045070403900c4510500e0080c00d550b035922401a045c8000c000c083d0880c03407580f1f91300b6810300c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 114502239 1250 114500989 114500993
    0x50a0b09071e0912080304020319020f15130905011401020601030b060f0619020a02090604020711120304030203070e04051c02100b0a03060f2f07060e0a0b010f0609060507 75
    0x1004640c0c09000100d00b0b1000da400260846840f4050781201120441d50071802c4100000d102c040c40c01240b08400fa142152030740c205035100840000c202952010705582d125125007440320000c070b444d48500504ca89840c841c01c010100319001940019021582e85004210940e603201200003031090034400340209500d10344800d0b0320200007070300c43c0f0322420420301692100d558090884201440c1d91540f40702035031207264003946810144009a000f0240c4800160f410703d890710846031540d50000d6601111b8803144180b194a81d03030252003e040344001c10001c00546c2d810418a0014010070801e05103a10342480c1290400c1404642d0703101402d91002820388007a0045500300105049500000c0c0016100000440e00c006590000d03151a2030404244860210b641210036002c4800d076081c00004007140c0d00100e1740c2d4020320303e4103082030700388580e00018950346c02c00704481c09510210f813510100340d120746480310020713031003640c00d50a40101009242e80201e82034000b41441d05241d8180001c036 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 114503489 1250 114502239 114502247
    0x1b070f140105042c010b0a020615060d0507090f082b080112030302070b01060c060608060c0d05040501020705060f070e0117060904060f0e070303020c0316030f050c060d050a0b0907 79
    0x54000e542c1d0404440c58081d03190641444110480c206004c41ea030080d5940d94030b204c003583d2205038140c005000d40c50020f81d01c10000c003032429480304040c0500b880c100d44200c2d0301009220203072480c4204080000001403480805c50b083c4080c000c1040070b401a041c1c0c10f152100c8a0407425075884680306041d18450900d82c00c80300311070440c1c04040c1c41340491001403404030700901c40d09000505c08132044002040103580300140e0f0006074031440040202d162110f107000d540764811510901080020001d1200300f0510f07401c07541e00603100307070005802c240003a42c940b41050001c8170307502c0c4084541420028495400840c0c1240d40e80c082c28080750300d95204404600b0000018602401032401c240880c04100143e8842c03840101c03a60401c105000c61580b9841d103c00c2d0501c020b80041c41050744041759840c000c5007002c50040502c40c2002414999a1580c0d8005032000d015140d0740602c40c4480e4058640c03000800a082080c0300005d05072070980702460840d590b682c030031b90082110004014146401c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 114504739 1250 114503489 114503497
    0xe0708160b040b0c0c100804050c04060b1b010f180c09110904050402030307051b1011061f030b040c05040c0302070515060a03020d0b04030e0316090906021b070f140105 74
    0x440340350613079421151000624080748100d080d40c01136040000030b0503140c0c0c440043e5000c0d40c0f08030266010885c00d403082205039082070103007054984040110905103070b10150b0b02c08190030120004540c20404070150000c070b490125107145104910056001003020004041d00a0581240d040101e507a04907810300d03190181283c003a001e1a5108041750030340d42c0400603280019849000c8600d01c4010a040d10800000710001310700036605050030103401c2e4041e60400b100100900b000701059500c003e0720035240000303030b51224002e0100d0100070000c10300703500810b48110701270740c0c140e05100d21f040c0920044400c4401868201841446a50000340c0041100c00100051189100040d102d00300003400d19074a59000039031080c40301c10560f0402190f034411911550094480c041d00c90481424103840d5418062190b40c0310214039010b21541c00982d0061050300c1c05050f0050074000494004626138044115081059010715002c0040049a820140150412100d200c82c01040600040d1260023 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 114505989 1250 114504739 114504749
    0x5010504120b0612030c0a0201031805060c0d090b070903020a0603111204150e0606030613050a060c170711010b0a05010512040203030c2a0109030c06031a03010e0708160b04 76
    0xa10500412050313540e4a481c0700501c55800306480d60b0320081140140d40d00c0280500301e0120b405e004849202c545d500c02c0303040180d6048070140460365640c041c444010781c40620000da915641e409118045420100403500c5000f8075220607281e02e007940108094035050f944001d08050170102d00190b480280c80c199420003200c481c40c4862074840c2d14000d1094115625010301c15460944149642c0800041c40e0b800f4030030650949401c3c2c1c40c2c08440c0b00c2c0ca1070781240c02070b00329403211034114001a43c540c0076003050440c42ca08003100c3c2d00d1602403082210000c2e00e030b400018600c00d4102c2c4100d40d007849100c01a5104480035902240b0b0440080c1207801001304168845201600040940d10705100b298518285003041d203050910a041556030954035841000d080060000c190b0321a5000d00c11a0007520740000351070b0001e42c94000201c01900440c154456031441503c100b07402520240200709140440e10042d0100506042c107003490000c1074100e03081e107202d900c0c4c01000039201c000c044400b070318 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 114507239 1250 114505989 114506003
    0x16030309090504020a17010209041104050303040e151c03021b011b05010f060f0e07020109080d0923011d0c0f04181a010f0902030f06010305100b031603060501050412 73
    0xf80e91400040c1800200d640101c9140c100d0114010311054194000d02a04800300c0302040610151207020296000e03a000d1150154402c1005100120b0a070284c1540100c1c45c06011000011180108660b460101941c8103c401c80c00d00c040100754050109440f12484465010542c014400c0001c200c203c040f402c600f20300410900102c14007100307400600c46000100403e2111946d2900c0c0614620814483c41e200c0300c2e42640800c50651040c0200204190001d000e14144801054000010246201c0403200c0e00d03507040841200c0001c0002d000301201d402e200000fa003038052401840340345410341c00705200da00b10744201c06c0c40e596080440003005905079000074043d08506000310005003041c0015006001103241e41c680300c52000300d002c0c10381c6e210540040903d961600080180d02080e24070800020000000840f2544250720003a40b007a800142003043d2690359a40c003403e0307401501c60701c800b00c0140c222003440c00d8050207a00002c0200b8a000e600d040c1c81c00c12007495000c03801100170041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 114508489 1250 114507239 114507241
    0x60b011209030e010e01051b0601060e10020a060f0f1b0912050601150504080a121e0512151c05070e06060a030c030b101205010b090607110d0507080d02160303090905 73
    0x51f40320b02c0699001d000141e03481c1e10795501c10b8072303170550b107031000d2040600007400d900c5190f403103081814032860240ca0300e0b00149049035159840074054444c201035a00c00070b584001d80101200b160044c00c1218003258070300d01c1c15144080004004203180d4004020f5407040c48410000a0310000e00d141c119440150300c6401421010421251882150700001c080c0c41103200000a11404044807013500d00b007522801c2c0c85800d9006541105480301c0d1951001c1181032009003044050021460f6000703070410b948001d200c03028400100410390385a0900000c0c440050040100312040090801410802d482601240344c200000784461203a030100b07070100750300c6550855680d40260408061110300600040d4115040e1000a04a00f00001480c501d1810b200001402c4201007003100c13200c200241ca2585008980e44404102d140400b0419400c1001082d0a10100301c0c144501c4002d450580054a15100c2e00c1500a00d8451115504004080c003143c00b00002034010f5800002c603002c241d004105 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 114509739 1250 114508489 114508517
    0x9020a0f0b1b1006030312060e0c04170a08160209060607080f0d09020d20041a0607050705060403081207021c11030702090c0a0207091401091512060b011209030e01 72
    0x8007003c64009516090030264003004040d0420740d0110ba1044030344040181c9561408404800e000940e40b020603000b04200921905102d511084445003915003101d0104502e81d44903107050b0b114484004500b01105116011490000b1400d60405802c40d4524249440740d00c42d0000c0340701c0c02040200580c00020202d05103180c68110040c09900200703901071261041c10b00040d8100301c110b4900a03500040e15140003407405105001d5071b100c83c001200c41c01c9203003405209007944542c1090303030644100f410002d0b840d034400d402000914409e207400b0f6103c0b4004000140080c50240c24082950014082200c04c500400400300d14020646803a142400d840581581944a00b61000c0e41040c4e801c0200002085483d009001800d590742c00c036290316a84603820805ca410310140302c21070510280040260003800d41104030305002d60041d0b400c2046c3c0c0c542c600b000c0b01d40c1480c0101c82158035041d40c0a00c3d5a00503815000655403c0d00a000e01d11403590000c06980391113006906000261440c401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 114510989 1250 114509739 114509743
    0x50702030a0b091b010f0e1003020d0504080901090e19051905070903050705270c090a03050c041a100c031107060c050606120d08060d120309020a0f0b1b 67
    0x4440781c10110300c80590a0802450740c031220045001000d0804d06480740e44a0351082c210310641c0b900d0b81e41d942c0c000e411074100b0440325684207034a510405400f40a900d42ca10000e2164602443c490030060340c0d40c4448070005030002c0942e500c00300710400e1401c03c00541000440a55403000034103600010165981d0103d00301451022240c00380b840d142404201000d1b03004000380d800e5070702480858100b1540c9200300b0612400c0b640b0194004890904e85200c1002c25003095500451412411070a00000c4008500c0a40480d44143c1d06035000c2840440c50341846d10031054010220f1045100c4e491b00000420440b842070341c1d10741e00b000703050714050040c94490110741859400e181d00340c0704001e0395402c00a04000810105480c18043ca0020500e246000101c0203a81390301c620141c60041d001d10419a140c0d54002e02c1e940c5c0040d403010300c003000148a598078110b540d80c0303503d0024000c090bd0040c4107d0744565000341c00714640c001014041c0d48040b80c1983c40301130700c604130780e2100701036001c10038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 114512239 1250 114510989 114511003
    0x5070606080d1202070201180905090f0f0d030504020d32010603020a062f070602010509030702090412050f030a0c0e0d031b0606030503030c03011a04030c1a0c060a020c010e03091005070203 83
    0x601c8d2054102000704d00c40303043c1e1308114050b60040c0102c1d000007002100c07c9848480591130b003001640000300b00103840b0b00941059601c075000600064600050b9100c024100d940300e06080c420a40150701d1a002d00301c003880c64521005048000c10440d42150b0225161404501900c0300344101e51200b00d51507040c101030740b19034902c1d00b2100c08160b046070b0446595020a805400007550801002031110b10340002a2549240c001b8a21a100c1d1290303141c030307108003254500c0442080820020f08000030b04810085008031001c40000440b584105401482e0810a52a0a101d100a06040c2c1d012076800310303080c502e614131184a880e601980d490504003c1c04154002419400040104030201c2404406181210303c04803010203851901703400007113a8030490100420000291100b4040710010039179400e0340800701c90b0186d183c4480400c1503071a00e00101d5100c00300c10380015081003503e800707000d5040d660a01200450401101da030000d01c014400c80114010424085018419036030104020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 114513489 1250 114512239 114512267
    0x903010c0207050a060804020a0e0705042304141614220801180b0103030503040206070807060e0c010201022b1d0c01031103073c05070606080d1202070201 68
    0x30003410000010294940ca458411144a01c1481ca0b001130981e000e0310100b44181d034001c18147e000c500f0b050101c030b1002c0010385900d04100080c803001c10310004580000368402c8991007000310035661f2a08200c00c0d81c8840c02440b08842c502424404000040c8001081d08546824680b00281032110403400500170305154001a00c0080890700b1846501411102590424030013480b0180c0815840010520740c1003004102d00314003401000461301ca2005507410600c02804030303180c05495107980301c1075080b5060a403003656443c008450428070410002044540a0000b0f500704241542045040c550140030311048404142a104400100c0d500c2068400b201e2000c1600d600545295a0b9851341300f00c50003808280341c880c1c080d0301c8140010541c2d120f890182c2e10b16000c050048a04040c18411003107080040310642030f541c0c450900644c0c13144000e09550b44460b120b440a00f808400d071a216400600d0581010a02c030884980c00140212803040c0b10002503614080c2c0c0c80103d6200c0103240340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 114514739 1250 114513489 114513491
    0x2091008060411121801020906040b18091f05030105060f0d020d050f0d1d0a12110307150e060c060601050f040306110301090c020601080c011103120702010e07060903030804021302090301 82
    0xc15544100c8607201140110b5800701040171080c100020070f800c030b01c82d890312650b1003002403204000c2d103881d607001065070f10262a600c8188002d003801043c190b4030309850a10804150803200c606440340f4000c090002d0800710000d0085051000214041c00300c00d0f00c60a020300d030059007120079521a80403121a0551000494000c2e08607403a9082e00ca40c20125140001001c88a1501c01c1801081c4140c44031f13070b00280300700d43c1d05181540c8c102c0800d08260b8211407520200584040c41d59081c0030307080c0100341000010108002a0400501030800c100c5d01c41d100d41380c1800002218000003a00344d0b88000c0a00341240d8030303000f081d003c0d4000d005a40c0010511400d00580424960300c5c0300245040755401c44041c0f02c54038070b61780300f80e80701d071800d000e2100140c1c1b1080310300c00150711442c2240c118078015826030740352000585014040c0d2400304d84c00390160303441d40006501d155040000c0e80c020206464552552030643d50000c00441c806031021b881200441d110342c5108400340e04aa45101740100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 114515989 1250 114514739 114514747
    0x9020a02030702060f07020901151d1c06050108120301080c04020f0c1c0807050c0c040203100306060e0f01080f0601030303050703061d180f07050415030209040b04060b0402091008060411 82
    0x315100d51b0207400104d0140c0881c07030000410122072030300b6201d010034540300c0405243c40c40300d9120342c84000701d6015500c550390060345420084110025000b07240910740c08501581486900d92901122000042010904200400c4130b8070010540301c502010840303015a42c0c4000c1c800c01201800703030b040228001d018108840710300a000005045104c6902e0300e03040c03025540e000080d81c0500840583e0175458012032103800040c80c1550065901c0225a036980c0202c585070744400003126002d0f000029903514000611003202441d800160040003010010551011804889a00c414040c4001400d068079840407403802030080c2c01000c00341c07110100c2c4240183c40340002c2c011054081e1075480c00000c074001c400901d0300b00840c080102d0409400204155881e00d024030000345181c6082c0c00850301d4002c8040700595640f40360794001c50080800380d0b514100750600201303d03130b40d8030900341c0306904c1001000542d1312070048042001c00241003045040e5907920101d809401d52030349140c0c0c9610000307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 114517239 1250 114515989 114516007
    0xe010e10140324040b180403051b071403070302031207060f0513120203042105010908190905010518010c060e071e050a14060c0102090a03060c030c0f0909020a0203070206 75
    0x403c1c542c118072840051040454006000c125000e60301d400303801c50145102c0368180380503041002d400621030b1070240d140148030466603900b41000f413004882900850360401106008034101c4115900440141004514544c0002e90f510005010301c000800049590014000182d0106605c143c09040900030b900c3e0407060f011812420300e00c201c5100c40f0f505080300c003442c4004251025035154040e41c01140c80840562200c0b60032440c0101c5882d0348812503580080c100202504110800705000001820358034006001c4000d10782000c1c1c1000300034012100c02500c89280c2d408011000c5c2014401103016041170390141046004d107a81c070b131140b40b2001540711441a920701c2c24010141a5010640d160303000c20507215190b21883c1012007101861200301d28111740101854800903000601c3c014034a40420340b0209164402e43d07025039230b06000c00105405001d4402480c0c094500504199444040034207614041d001c1c00541a0380400c11281082c001c004684181d41c0080c0441d444080c82 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 114518489 1250 114517239 114517261
    0x6010f21121e080c0322080d0b0907080c27030f0d090503010204031109060d120c290c0a0302120f10050306040506070f0c021201060f05010e010e101403 67
    0x1042d02c0c1c580e0060104404001c07507100e0f40d205030250840002c0c070b9156032241615903000c02184d000181c10b001202c003503100083d45c250000c0151041c2c080c408609104d4607000c101c41c0e800020030006c1032201c00350800200c003050100311168080c034800d0000c01d80c0003840817054450516010190103104038071244c2107003030f0001101c1440d020155070701c004a41d1600e003814241e01481c40300802d500d0b01507217005460318140e018143e000d94043c26a029562054130703070680c0c07410848603000105508010310303c24004078000c108240031144070102201e55040486003e501380007028030a10100c0800c021a8541c4250120303001803c542d034000029082580c80c0c0100500309480c940d14aa41c84840000c007401c001c250184955044000740c601560750040527541d0405180e01da40411416620401c0141c0d100c00940d5122104c0a00014550782885100009080640c10960501c00a025100d0b441e0782d200800e90300000058a046129500182d0265042948100d80c1c6405100100030086a5182 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 114519739 1250 114518489 114518507
    0x2120a050105030c09010317130b04060228020f06040f0b030603010c080408030408090604090e0a060506041512051c050a02010b04090c030209131205070b060306010f2112 75
    0x41204102503680c1e20101070390382c54102c2200b50481081001040400e01307115901e081040a84841850b00b0360795120f045070740c440390f084204201808541440a5a070400921441d00e40d02c112400e03108403003c2e042c0c00300218242000348540702c040c0c8042126100d80064500502040b03070b03490240c1d03448000b014210f4200b00e40c141c0c040e618185401058a200e800c2c0180256000500355240d501c41c0d460702d0307a003a4030035030040d40c10100400000a040b1b4403841004200c503090f10150581d4000b6182c0754040d1900500b1180c400c40c14130744415541c0b024644510b088030035440c03c0c003821744064a8200c1c100502c0986c0414406401742e4120440c0390044000c005010859000b0011130820100b0403088030341c0114068150406660248018245964a95081501b50081c01007204081c0d40300c4404d2041c00908000250001c2500d2082101d014040c60304407004402078011076041041e54400a0014400e450001401211891680c419840e12000b901e0300080c00c2da40f101030100703000e846407035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 114520989 1250 114519739 114519751
    0x40b040b0405131e0305030105010f02120a0507060b1e010e0a1a0a082211040e0604030e10050408030d0504140307050114010506030402010903080a02010204051c05011803020a03030c120212 83
    0x1142043c2c4200e12800448003002d04e0340c0c581c40c2c0d02d0a41c0d0070100110382c0002c011030010198896640e41088110000000c0c0c20a0410b6940e1241d4403021413405009030f40900071054020001e114101e204c00d42c1000071240d101a0070700e44401101103980c000740c02c082281d88440001d4540640072031030030207104010008412030352a20b503420f484080c2c41c0d940c0a0403010b440540c44191501c03000000d00018091000c810f002000416200003071460b1906000094608a0208005040b0f50601c6d0600c241c10314207032003190802c10f041502d018070b03407900e03031103252504001c807a600c0001408000e20783d0400100c1584500480303440f00014500b01d4024814001d00d00384640d641c400003d003d141c5181100c0c4580d0b4107039298003290b855030f9580d0909801451600096540034800440d42d5244c00401070220744d402c03404040c0500203414454212240b17003406042c500c600002000c08a40c00040d8030091960520300090724006c404400c4901100381c144082c1b1041c00050800c0b96012103501d0540a0031b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 114522239 1250 114520989 114521003
    0x92004090f11010f0903030903020931060b0103110304080702060418050717160804030e0607080d050a020406050708030703021b0609010b0907120510080d120f0207020d02040b040b040513 82
    0x24100482178401c3d00107440010001400642c0c00d00040c2003050f507064100c55030b6008014512520581c44480058080c11200c01c40310341c0b03540e1418011280180000320f9001e080402c5038021000c0c0e50036071484000c1001e40750743c400060301421502c880c801c5500406e8540119000a001c0880205c09800f080e10004001a52513a2660520480d40a181e000d600100424076002c00c0509040c0c4905030002c0041d4203008100364400340903100c04c0001d0408911400d42c499843c0a0b40783d20700220354028041c030b100301c2d10501003800b04542041c121601d8640026403143c403a500d58008030b003c2d114001c15058101b142030403e54242d0390000c0e11600a1000000034041e460700c00c414400302c4101110f1000c005100300500f18419000c80c0d00564200451559a07000242c807994000d107010007820705280003450f035000c035442c0740e6014404c0e00151880100c0a502d0201250001004d940d10600040c0c8519640c500c07410003a600d943c050066003d018000740072600e0299501d804468240c10b00b65002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 114523489 1250 114522239 114522257
    0xb0f010b03060a030308040309170313080304052101090f060608010b100e0f040b0d030c030906020109080d05090307150b010f0c0503071b090e010b040b04092004090f1101 75
    0x1041100d050764400c00c0d028052034600307440c5071405c1710301c2c00b8007030015824401031040c0881c203042008400541c90300c4440085a907900c00c0340703002c062000c8030303031085031650002d0009220301e954101154182400005c0044601c0c4000d606a03401010311113001881e03004a0801c0704100710032900040c1c1190130480007001142c11040602c40800d000b4104180080c0410240d64881d1400b18048541c1a0020340001080e40c480c2c80801d01c1490807190a40110b08261f0060301015884404a00a0304042c0b0081c0100c40d0181c0d500e4015000d650b00511140ea203900010700046030410944841c0c2d0b070080403074004107115100200c004c10200043d83c0c0042c150442400c03202e4021340c640302d0341c0c40e0300000444c07800740242c403410b580031b85070421482042c9000304000342514481c0141e01c0400150400081d016030b40100f00310840304110b4002c1e001d141004003510108890020900141d00e0003245600514501000a0000c1c07410b050000e003d901140914014801c00c2c05045003600b034280c03651061 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 114524739 1250 114523489 114523499
    0x70c0201030c020f06040201050d0608010509060f060118121401021b0d0309030806100212070606090501141003050c1303080702040b0906060406030c14160302070510140903100501030b0f01 83
    0x48600034820160203a02140101c1c0055101d04003c0000c2000b00b18001071454331038910390300b558001c0c6d503040030720f5000c4000c1c49416144052026001042400c103024108074502450080e4081ca02c83d0980c1110384503000c0d0248032110310b401c101604200c000315612041300580c0116214240800b403014441e041c0044030303450081c0708201001741c05840d0280c455803034504002c80d41000013240303000c6000c2d018008000f56090307405407950700e20031440811100e0804410500302c6105902021210900b504101c0954a0321003078203c1402542c030340426542c3e54944010030070710402843c07900085801800209200c480e50240c12407510848003403006800b24010800714400c15500d259000b00304010030807089000398402d0207000c40b0380c2019100c1800c6c622070482190400e11404480c0c4082c20749a0041560600860300500310440d0f854103c650780720f00080112180ea003070028104000070313a041c8130755010040702c100c2c031131243c0081c400c642e100e180a1480640c00c2d500c02c08407403400d000101c2c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 114525989 1250 114524739 114524743
    0x702010e120904110c0625090b0a0f0c0c060207030b0a0204060e06071703011403190309171005010602010c020f03040501020309090619030b070216082d06070c0201030c02 75
    0x140c56a22140c1590602d0142c104000043c614480c001c1d540b0481000044122581400680d2040c115481082454031914070407100014101c01700f10304201900205010351520356003520f0749910b90342340048020003103071000c0d244542e00200c0909140010b450011b5403e42c0040e1800907030340324004000b420f0710f44560890a0740070342d001d1500070500c580c0c0000c00c54107003800602413440c000c002502518840c1985562698001c1c2c2041480403040300030f26501d07080402604290101c2d80d61820311510b00e546000b401e0785024010481003081906003043d05090030440c6da6144240c07240104070950303650034040c2c020b012402d04900135000c3c41100d100072803170110030b6400300d9030b068002e50701d842c042c0010000704120083c180c59124034030419009805480461341c0b80918460030b0042c100d81043d04011b4540f0b00880e24071420301121110610036041c0c041036001c4680c88a800da032035400090010385080c4001886280654403405c41008019a40001300703141c418000e807010010042403860803a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 114527239 1250 114525989 114526003
    0xe0307060813020d05061006020c150319020d02070605060118090e0f0f010e0606090f07050f0f07030e03100b0a03020f030a051b0109060816080414010903090e09060402131812080702010e 82
    0x1540589000009800081c040000755484800380905037400761050100b0822030300301c00140034030680d0200d50401080300c14481c1d03a4000409003400102607442d204d181c0e505d445607010b16443c554942c00fa04844080c01c0040131100d02d0344000b0f0f502a00540c85013503008181c4541c01c0c1025101d440c0201d051400c03c00349440c041c17440501e0490750303603a070360b60207450b250b206081250041d201003020381d0b03504807900084c203a91842582c8510b465001c2c0c00c20580f03800300c1d0b2084d55560b1458522001c04558488565000b100d505407811405555003100190824107604070241150140350310000b9494000c0000400400007629a0f124403034030740384200c1d94502c0845040c0401d0000320454038146000c0e80080740e2203449a02a101180110240142512040c000840100300b40e500188a80c51441210991041380b400c002c01c5289040c4c0c0029141c2e00503c8151880c02d0398800f9620304c086080318145202940100d510701c1001c5e5a0f81d401003001c44102e9000c4015440c20360003041000000c2400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 114528489 1250 114527239 114527263
    0x602180a0303170403140705030c010605040b011b05190b011d101202150406050c01050c13031b0806181902030d0e0102010e1c020d0e0307060813020d0506100602 71
    0x8980f641c04921500f0f118020081c2054061018280605d003062030300c80002c2100c0f600c42d80165442d0300d5050030f01804d40f00c1c6034100a02c40c6007445141042a6070100f2030b0150482c026100450306841810700c0c6040c500d0b01039000d03001c1441d010201051108005460f4101c90100385480440b401400f04402020801d0f03505012800c5112020813a152004008003441800104200b520402e001d40c001d2140d03000743e0103580400c02c04100c5040d842000e106032a13002500d030900d245080301440f400c0442d80e02501005002c0205e003500c041000308840d4002024052140484905040000e4050000c400d210403014061003070100c29a40701e94000c080c041402e0b07026000f040c0b507030419001a42d00041040e1000d0456581e80d40c08401c01d10104540340c402502422003004c00800140000d05020980c6511018007142660140c1c060302c4c00035a0504131081442c01405540b0341c56000e1900d800040c0c0042c0d0b01900581c6014244200400c000703019006c401c003148243da541d05010b0ba2105080001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 114529739 1250 114528489 114528497
    0x5090708100b060d0504110d030801051005040f21080706020403111c0605090c040f0516080408030118021204030315080a05070b030403030b0a03050f010f29040b04090602180a0303 79
    0x8130320100181e541000d034105200380b400d0400d40a022020503c1c22524640940000e101b10703004100754105644901d100b61034500e800c620301800c061144403020603a108502180702c28603400801c01201c02c007042c004540c8480d216a858030241002c1001e0b4105001c00e440c0d049a0210b4100742e0715004c2c0310344042c0e00c2c02c4150902d92071034036200d090042000812401d40390051601c00401c56449110b004035421b0100c00005050809910b051a40350720203c21300240428030040c4000700d15003400380c0341110000380140e9001c488504a072800381c05441284549698903006000405801d5003143c0407110283c2205d000ca1603865104c0c5585000500f406001c6401807241401400710000c010f69002e8042d045c042821801c02003c100354040c150310503680703500404022800b0400030300903404134041040c002c3c801040380b00009034058a085485542c8806410300384a6035803616001803031781041c010020410f0440740e041401c003952180e90400186541c3c1d030004d680600d480b28040c81035039019a9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 114530989 1250 114529739 114529747
    0x30c07060b0d0c030b0726150d05010e060718031103070f1d071b0201030b04141008060903070c260d0507030e06120601050d0905122a06060402070c0905090708100b06 73
    0x50844103031f001030b112a03045c20710a8001641c903160b204409074094400e0000083c03501c4030290071800d015024007100104001358885400004081e00d810042d80c4d0070810300c0f0441070690001030700d400c24583c070103490402c03007160025402100720314100d00010302c0e4403121300c0d969416074102c03411403840d040500390210702011180594440c1d4402c85440c100900001000311400c1030900c628201140c0c20100301c04280e00034031034408117201070b9030402d4600d402542050183d0740e0710088980240604080d10401c0b40b20346000040c0040c144100c080c804d82a00d489140720b4100070019130103550240e002c103090580300b0195040400440d43c0540e44050180c2c042d8903604011565640814402410342d0b880e88000f102040c1e0a20001c0748456007004200d46e1400401c959240c06201c10503142e07480342540d0b202455540012415a0780408104e9006a423500680780000240c1d006400c4610307050f103014104000e5940000d140020b49080e202298810215070040c101070715240142542c0120082c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 114532239 1250 114530989 114531047
    0x4110909100b0d0615150e10030c03140f010f050306010e0703150b040b0406110d0e040e0f16080715210204053c0303030c07060b0d0c030b07 62
    0x75004030b5008000038020b940c0070080e41c88007001d40d440c500c481d0000b1004520100481e00003000c41c41c012160b107003444080d131040342c0c00090002d00c101c80c0001c1419100d60000118901c243e1000d581440320b980b140700711381854031030401403000034000c00c404d040c000c2c00007084510b400900c5504032aa1140c40020a0359018400c038040c1450ba0400d205440304c0da500800c0003941d02c0c000d0005020382c004200d890354a0484014640e10620030107182e070340c0005900b1080c1507400010040080c10541d0080350020b60b9803100c9180a00c03020b010050350081d600d00100d0b00c028503105104a40c8440c00325521a0b485240240400c010741c0e241e070010501102c1081003400050711291213041c2080b0006007041e54401c0480c54a0034080c55500d401d914884007280100c015202c110121000c5c9030b5404030424030000484e50302c3c44050940131041d00b020680c0c4040080b0354010800c0000301400b414003007915440c0c1850702e00544d0000f1a0314070740e09000511054403c0001070483c400f146804008801c100f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 114533489 1250 114532239 114532241
    0x2903060718030f02211c050f070605061f0206060906060a2703080a0309050f0c100e06070501090b0406060e07120515030f03090a0f060504031401090b07080411090910 73
    0xc1c40100e0b002444140701118503550380300703000a01d0403241c01a008580322000c1401460100208040c00e019088c440e1500b492031100682d001c0f25408400000c813522224002003264883c030800344c401c1c099038422600122b0340032644501480d400c0c2c41c001c2d0f0a455000402146000718072910000501202c2d41c0f0000c0c007250340424501c0060794810b041e0f40354803502c2e090301e00c3c4e01032061040480c3e00c50790031804001003003118042c2c810100000c5c01c4480c4d0780c0c0000442c21500368103907004002d10040020316560f01d10f0100c6405d254410020030641d03480e450b015890440464081e601185071100010700c103245841e913944100c01c0383d61070015550341c11201200418005c1d1980a000e640c903030500001d40c4042000d00c580c1d84000c0e00464980b21150f0411040300102d40040706500c0410904010076500502501c0541c1d601212410285c1072070034855005088184d0040c224501d070701d05000c9099040031409003d9409014042515441281440000791040c0c0701302d0b00c00d510080300c0c0001d00c03a01d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 114534739 1250 114533489 114533513
    0x9040b070c08070f1a090f030f07020a080604030207180218040908070c03080904060b0f072a06050403020a050f1302031b030c0c01051b09060d290306071803 69
    0x310300c0da00c83c201001078503050900d6401010480c1c094816110401c58544818100365102c0389400040014484c041030b143d07203901940b181c2c00103008012414100b1984c0311640c0703034060304280c01182c80c40c1c174150034001e60300e80d000e100c0c10f0610103405a0204542002d03000312030b0411050702c032074a0920181c0051100034a00144160355481003404040000b4440c10401c0e001140164445078450800404100403030b81258020300584d241042426840814082a10382181d0000c034102000d6045109542c0c4210fa1119800810341e2261004a81c0540001c06402520300a48591080030384070428020603801c2c0124055000e40d080500c00c03d9081203400031a40202c10200040d0007454034100b200c020f41081d190003a64a10115400031124400d102e81a4081e9070000124002700903c02c8415040c481c5160300c6000d418001401100c20201d500b004018001c64001e00c42213580c030709144000c10b0000c0c22564881c1c002d0801044403148107007100215003003200c04c40380f5484e1565691500c4410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 114535989 1250 114534739 114534743
    0x927020f15070312050603010b0a151106090f1902012001060504090302030304020f0301050c03070f09051f090902040501050412050709020f030f13120f0309020324010509040b070c 79
    0x9101d122203904400031401074001a44a80c481e07900000d202c45070001078800c020b0142c0d000360700d0640b0050b010340e9880c2550081350b83c1502400703425020300d0780c1250320040303149108a0b584242c1017804040c89002501840c20340d0b108055079240350b0750200f1700c4a41e52050202900044402c12050440d5040d44058400c20b02c20a000060301c0780e55401090680c0d608013415400761304044200825801c0c038088050840e94124000c0285142003141034200c0d00024000704200100b050075502814041c0c012100544070060100c1c079038a68443e52a201042074882c4280000d0b59030b0300016040300a0700a80e001e40d90b051310340c14141400d00f00403031070546c1188400e0f0340c144280301000615400610081c5a0701c3c00188030582c3d00e02e05521000713800030003c0e004140001c03c0401440124140c02c005402000701450840c0e000c1001c82d80c01c4020302842c0300c0103503250003026422030300e03054104101d164138590f07840d00405503a0b0300e20400409400460703003c0e1211188100082c447c5124800c07601c1054 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 114537239 1250 114535989 114535999
    0xf0c07030c120218010605070b04140105010b0706140906010b07060207170304050d0207140f181f06030b0a06031107080705150a0504020109051207050d0506010927020f 74
    0x380eaa4581024150855000500c9900119005015401c1440e400c4201c0e40402000c4691545414170080441c410030341c0180404c125400490100300b2140b42a0100b116900f00a00540d42c42d81d13403940056000036011501c0500c1c1c01c1454882c1c404070a03640c2d105002543c0540b006a00e80418600c00780d100f01c078202c8049908000d091300040603001055102815101f1441d120715142c90301a1070414004501020b6602901c0208409464114003248141d810b8a2070b2a0980001000c40d0707014603810201140c100d9900c0030414102000044d10700c0340a80e49084440d803944d500400d038200e5903905140c540041c200c0c407052201d01e00a401500140108200e51860608030b44c845108a420002049800303030000c00c9002d800a4100d07242035040040da007020001400c0c81e90000c1c181000c180b0405000e44445900305003185403d20003a001420f0262400301500c4072881c1c501c0c0c5070b00b02409001c540a2030902015040061180750742444222404140c0e0100510b800b0030800f050700c42c407020703400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 114538489 1250 114537239 114537253
    0xe07140402040b2a06190f0f050411010f0f0212070309050a0609050901210609020301020405040c0806031b1806030106051206062d010509120d08010305070e0403050f0c 74
    0x1c0c5140f008240e501d4040e407050907860301e442c0300408000903e94041240d40c0c0310fa03051048503a4a4041c0000044403007034006a103042020800002e03211060410706c041d480c0c1004c01007480740701e00c500c112110342641d900c3e402c02482d000a0740c010020189200042e800034102c596444401001400640d00030b080049403c0e07540d034005050603c05400c80c500040984030200141d090140211b0702401c002401680e4000030000350340c1e030035100c0344000340c40d040d182d500c040250348003903040303801034080503205020740c05c183e0001406c18001600c42d98082d100b14101e010945004070149012280d000702013181500950a00942028002d408254155a00c000005456440700150303544100b059020740242c0c6421410003a00702441001c0c02d0300b54030f80340c01c5a00850010310300c50b03194800900b0110b07120309020300072450600101c1ca8040b51442600d014045031034001c0d81c140e0403244100103c0f14012780307814201c441d80c442510010003080c030900070070580702d5a4001411049400038115044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 114539739 1250 114538489 114538499
    0x70603050c0412030f02010501080606010c080a03140a0b0a05060307051218030304061d010506010905040c0504090204030507030b010909020102060a090807050105150f0612040609020a0b2106040e0714040204 91
    0x3029500401300d0201d01e400e408691484d8083c051280103100c06000340c14203190560010f04050041e460041c1074202c00208500928001d5003c010030b408a040b0499003490b1a500380401082c1c0e00e0581c6108141c2000c00103020f160080403280700e0101c07651210308000345601b07014120040a0054200210100b403200803d403820006544114011500030600180e0601003c2034100b404184181ba64105010406641d03042952001250410740e000500d240ca00c40c41143d41c0d004640100510a00018000060140014074041a00d0248000d410580d980742010303400c4910408009000d60807000c0055000c0d0388a070b11503c0d50600400085150041c5c030f0b6255421148101d035410b8521032640034034801420854051002c001064910f00c0c07814000100007000d84a00410042c0038680b240328110440d00c51070781c2c5400401d0500e4040e61a040032000001080ca4074041d01c0c074102c1c026200084243c81c15008080c00c0030f00040181000c02d040c105003028105d003101d030b001d41054080200080b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 114540989 1250 114539739 114539759
    0x90f0d05030f120717042102070b0d0e070501050a0e060a110a0506011e08120306031914060a020906120606130e0603060609010f0902220603050604050604020c070603050c04 76
    0x100b03c42241c1074030668136203600064110f055003004900c20034005410000040c9903c0f0100c048207105110064240380e011034100d140038a00e801c1004092404140003d001350550001502106042c0540d00c0490b190001103505014003584c00b800106060041d034250b09040005011000c00b51038514181c0310102d1344580390410300c041c111201d920035401004410031034400001a00f603425030350182d4515000c0e103c0e42d0b03140500c170800741c5a50000045807150b602003041030307501480618010035462060401c80400d080004010400380240c2d00061201111842190f201650040c0364600300b401c213080035000000700500c2590803100c01c000b00f60516071300503040d9006080d0341e004108140f4107031041c10708046020705640c1c080c0111a00500c194810200c3c100c0540c0e4442c04016102c1e00b403541c104045c40032904d41c480b11085180c80c0170070030701d03490b400051140a040d10306021135140d40091004903c19a04c0c500043d030000d0000340409403090f046941c103c2581080782d8245a200c0b08404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 114542239 1250 114540989 114540997
    0xd0507080f0702010c0e130b0312030403030b03071809050a0204050a0b1e0603160203041203030e0f0d0905061803032107020304030f0308190608010c020111090f0d05030f 75
    0x808241900108140c200d650540954400b0581c4000c0c401840c0307001020b044c0ca003040c9000d600c5110181c54803458003401d940b104855800003001c480d92406007106503840390744141d40c190300290a046810b1030606000401004694816030050800c8400b5002d520003801141c0e4110341b28000c0750f018a002d640d40b4050a80120703601c000008001c5011420440c46c900844230400d000b180f007411440c2c080ea290003d81c0c4d4001c6d0700104444810f00f02c17031800c81c2148201c2e00800401194454100149541648106280104070040341c10000031110300c250755080c036044060010310140d0041c485410030383c02500411004210380f210700f46068001a003144c00450f04203803400022807404892002d81c81c20380360891641d001940c601030442d25100740e000c94991018041c0036400001c1200c5c0f840700c2c016501d4601080034208a12600c03080a580a4802d40002200643c200aa10400180840304403540108000c5c8803901e03c0d10200c06001894010b0002542c540c00b040c4003d40160304128010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 114543489 1250 114542239 114542251
    0x60204050420041401120e0c0109060206060d030e0d051f05130512090607050a03080603070914060d0f05031204020112061404050414070308040509070e10030b03030d05 74
    0x158440342404184001c0340c0092141c00d0040b018144441da501c41c80360111425103003d5000c41641000300c000584650740345000307035038040b4070708008448626808a582d014954007613a4680520f65604012a17548a040e00c40e01d13405064002d80500003801620040d1040c0c40151141010700182e8a4041c01e100c5a0301c90540c0c5909a44000070035049240705107640306140e4100b0b458400d83c103484081c0d6071a840144a40d0190b00014100103698400058591700d6078800d0880b443d8188502d4024400d040943e81c550180c4600300001c10540858000c01080320082810200d482d550340080120305100c104040d10b020040400303441c0416010300081082e10301c0307440000708605251000500c450554010f24403440c2c503000741031141c1d0304155410181000200c0b00884d40d038807030703040000d0078481d800e40d04403961081d103100008010100015104a030400c480403a020740d9091010b8070b01242c00f0700c50680c400501c080c1c03404001c0c029407061004001c05000c4a084c0405c2441c141304850303040d10a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 114544739 1250 114543489 114543491
    0x1030c180803431e080a120203130611040801020a170603070303080a02090a051306090e01021201030b042f1f05030114060c01060e07021006120303090302010f050406 73
    0x12080c094100000c00d151500c0c0740c0402072000c4040400300c100103155403105407030f60301c042014820701180f104200c000000d165581c103000d20a40c40c0c03440041d4420001d000208440c80700500440c010352080d2803040c81d40f0765042e000e00001d550bd450040c1001a6200b00c4141c05000106460509202601100c602522041545051043d00c07003180d43c001003200e8400c2c2c3c40f04406200080e809250943c100314400c0380544c540c2100f400040d0200b00c25003107a80c1206107039408244600c1d154000d48201c8684c440c0410548111000084c241d109494080d041d03502002c0c0104005074034103059a500c14040e41e01c10703102200080404c120102a601400e0385003000103030f9403c2c2850405282861081c4501445411101145011f0401c0c0014422844040c030805110320f055112032044401c80341d00300001b002205d0f2140c0032844000f400742c030060014440d0b20300034031880d4114812001a10285481042005100d81d02180078100c2e82c2d40880c119525a00b000d4000803041c040d450180e449098 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 114545989 1250 114544739 114544747
    0x21f05040201170112030f120c05180d081603020a0b04030e010806010305160809010908132405180607021f030c030b01080a0b06070803072703020f01030c180803 71
    0x1040103d9040101c0ca003030516100410900000c01420000c0c1507050506002071301000d04140c0b511005404504011400d0203900d0700482c0e8044000c1c024004040803262440700c00005000c07044104040040aa010822046002c0c0c0030514401840301d03c2441103d01640d5140d403280b01e000c0b0292030440100e480184101103d60f00019003d500c0300c001c1c41c04002c185050307098154551400c10348102070100a1000c10022042900f10800054001d54415030301c0350a0058407d04880a105040510480111494030510b000c0608101e101c0940d50321410b220342c400304c001000c0040d0700c01c0d030740c0868100310104c01600d6042d000558403214020318074401140500140030b440d00394814108241c9400e001d108143e8003c0c140e190840ca19982c009515008800032a90320300c661074008d006031201200308000e840e4000750559807000c0c4840350f95411100310800110303c0815010007940001e60f0154024194030a80c440102601d1602c0c008001d2540344d900c190100001d600f0041464000003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 114547239 1250 114545989 114545993
    0x40902070201021b0904021e0d080301080d05070b0a0f090605010e0916051012410c030406051015120e0607080f0c13240206010506031303021f0504 65
    0x200607070702103021045850500703c2c11040000d0385d07400c00420003849800040d45c81c6035501e0b198124402e00740805002e0902d038403554244a49903070824892042c05114034610031204c903100c0c3c0203030391010703601c01d40201a540740e07000924050301003030007100c040300e507200c8016000c95800c3c01514024005007511500301d0502981c070604009404441072080c1040f004100195181c1d0b20904c1c40c1540c49241c0010006004401c17203001e00b00450b0003c1040040140350107002d601c0114941d00003600200d036403143c8020364030f495451082141e182e80d100d40706100040c0400d4580c1c004a60200c1c0e0005e0640141d43c88400d1000c4500000001c00001041030190240081c414840c90301c1e00f6203450001c10440c50107400c02440203030300905c1c0800740c5400002040d0000a50401d65284820a84194040799200e81d4507414000c40d148034074455a1202c071140c0320540c00881c115058801c0688113520b503541d10f000c1c030715141d82884000c508510940070031130311101d00b1004500880b200004c0c046203070700b03080c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 114548489 1250 114547239 114547243
    0x10030c080604060b09010c0201050d06030309081618050a0902030106080102040512031911070306091104230103061109041a1503090a300f030c1b0b061504090207020102 74
    0xe08060269141c000e0a00c4800204016174044810929110342030780010720040364940618818001070780d00f00300c400300030543c0180107401907800d24000c43c0c001614428948070a4246845064a21ba0500c4140c10242c0102e40056078440e032105030208510304240d01190840341c6660000301c04c2d940c04038080c803103498188140c4000040c41c0300254144814403481d401000d41810507602030108802d8200b034070841c00d000f4a001540c00040c100b240040ca41052070290041d05e0342140300e00d01d0f00814030b8140e042c503105148502003101e10b00802d682541d58200c000c1c60562900b401ca6102400485c40700e43e81c0e0b018442da4007078a0303060a628070700c5503410f0051018440381c0d0032401440c00c0c01008145c4d040040c03070004881d080210101100f12600c005100360f400d40946250f0200c45404001040c0d810181c3c10034080d050355800c00040c00c02d80e000b00c40c1c00e15040c204006100340c18407610089400303d0481d0381c019000410550840385814003089081d40039900480c1f030680c02141c48003e643e01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 114549739 1250 114548489 114548491
    0x5120606100201090302060a02030604110309100c2a03050c070f03230d12060e04060c020c0a08030d020705030903061003060606020304060903060509010902060a111e070b030a090210030c08 83
    0x140000d1041e0710241e17602a40754880100440d5090750b000c40014055a940d400036a40700000302c104507500e0600341d42183e1140c0d140c414002041c0d0901010700015885160f9181c4110012014003042c4c240080e200441c90000c10000d608000b402d214a882d50b0170181324600080990f02d00ca80e4540b0702d5450b10360705403009540165400100b1451278100074901180d030030380c0504145045807407203800440c0e0100500940d00080b001d6015030080008000701c41e4020034214216800706c83e00300e2429010880d0403184c5010b03a501c207030018403188908021036000303400780740e218005480c248291480401c2c50711004480000090319815400c0050107001d1003080080c1000d48042d6240030701300840a00074115610008007141d9480d0000f0344051829404441380e207500509150b5240103030040284490300a0348000003034003038180300b2030316100076509504e2215003010191614038502120101590001811070049540f82c2007450010381c2c5907061241c4050135070710006004203500c0b10041031450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 114550989 1250 114549739 114549769
    0xc030f07050705100515030f0747030402011e050a03020c03250c06080106050f0d0f05070e0a0f03020d020f12060c18061309150f080d2601050405040c05120606 70
    0xb010b9012b00156140108015070003103800261041004540703924491070b02c2a0000102c00c04da10054002c3c401540703c0254007860003680e84c0039014900b41c0c031a41000311744c0c820307401c040b440c20008061842d02a4001c2d280c03d05940041d02d0a00811075201501c00ca45541d500c5c2c0d94191a50f20907040180e001c2c889009004d551810144541c11f0a030f002d407071440792501c094510036000c01c4808400740c09400c041d66186810703405010b941440900074004102c409500c41c440e80b041c9101080d9011410807a600300c0b0740007001000075000640a020704107030b502003060b8000c12050b011100352841005401d002c1c02c4040c1d2125541c18840410b40c00020b001d44140e0304c109410040a0002030380e8903520340030344989000c0080c526020460051800403a079010b04555481c141e8002030000000c1f400041d100f01c682c659900a4100c14150f44480044016895030301c0743d00340040c0120304040c0e02190f4402d2003081c42c52038050300c0d280041c81a18104c052042c160b4008002c021190810056400d0003030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 114552239 1250 114550989 114550993
    0xe18070f05011e080c07020607080a0306153011030412030c0e01080f0720070e01090b011202070203012007030e062113020a080304030b0c030f07050705100515030f 72
    0x2000402000740201d4005e000c43c0b6042c139010910505540d41e4201700e03900998060405a52500c9151002c3c000d0710b80d5100d10350120701f06441e481d00c4117003c0d1188507141c0d44401002c035071228803140d1000f014141802e9a5200e00d5541c038400d0008000480114010f034080c1c42c40303e07420200c10342c000302607810041e0202d007040031350301d00070788140d17080604540c100d000c2a403141804c0c1d60300d880848403040301314020030442c0c0f2800408004040c0205004041e24891108000799070381b03030008001540c00101034075000405541f80c026045e15260f0140c010380d0310080c0041011b0540e00010500c681708804441c0b6000c1000a00c1c0d820103400c440300e28440001900d1070340c10a001001e111102c071040035980800c081000e00051f11155071159214066640142a075071a16217030010b46641c1d800030301080350400d14a00209818041070403d8074400e6540d403042c1c4069582d001c00403103458100c0c410031185413140c80d0030144407500c540682c0c0e22420b210900b560444200100705440e080f203c0c00d1300c007215 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 114553489 1250 114552239 114552287
    0x11100c1407060503010b0a020c040c17010911070215040e010e0a1d06070c03020109050d020105070809030412060c021005041101140f07030305060d05010c0306050a140a0e18070f0501 80
    0x503e411006807411604030030b03610350310344503030744403d9090070128038095034090319080d03110300c2c0c042d044400c410081a0290400c0620703130301da1b40c080342142c228445403110007101740700d03501c014075241c040030703004581c10841541055900c014403044c9040030b07080040343e100235a04002d0b541b41c0a20589121000b0411410400c2040000d80754807520007a011000308814800c08406150003500403440403944841110400842c00300000d00814041d188040042d00c1d401c0410f01500b8000266016915560303e6400d0414040d51a00000c202d0f85050000b07501440d000110320620350703c69180f02d5030149400414a55010000529540301d80d000c04010000c2440100d1410b165030044c2d61078151b16050000350354544a0005031100c0c12294002d16940c01c0c90b50210810307078560414400c440007034400d002009d4075680305031540a0544030b0b05400000b141801c0150720310000742c00ea00040051400e50100d82100007070b80c20500585c0044000c404942d004000a5038495014002003944400c543c0036 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 114554739 1250 114553489 114553499
    0x1051b0105181f02160c090b010e010212040506030a0f090302010e160f05100309050f010b0405060603060310150803070605090d050c0a12030f050f060f1002100911100c1407 76
    0x24107459400307203d00c2c19030101d5812054841d11002c029a90780041e03a804442e542c0d2403588018120040362580090340ca500c2c1030f925940001a249004000d05900508081c141414080c160300010007800c005a110850b00c00500c809105500c0c14034021b900100f07140d13030752000305854956001c50f143e00410100390b082050600c551140302c1074600072103c0035070140c01100224064510300002030414018070100d814a818154030041c1c40660555052102d542c844040008500084a00540682140d06a0104ca418551104004035907003060030540c0ca0711020034a1843e00070b041c0c02c032074042d910024420101400c12802d00d42003854a0840e10304004441a0390310340c41c80c1c2c072009003880780d41c0201184590283e00b00720200c298906041220b40f414002a070703c1c0c0300003079540900406884082c2103448c10502031041d181c0c0faa40e0018181c0e148104046001025034900030740c0d46001440c24020141d50359090552145110b40d0380d010f0001c05810714505064002c541e800c1c80798031030700c01080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 114555989 1250 114554739 114554773
    0x5030709030303090602130f0e0c070305070b100f06090810020a0c020105250c0905071106010522020403060204061d1309080c2b030608060609040201051b010518 71
    0x10603242e040c80c01056007240c6261540c00303070041030201801031036011008074418010300710513404c494500c03d01c180c25032a0214003440c0e51144140140004404000c40004101281f0000c0c1c1c101c0300c002e0580b68015500e07580c1c030915280781d03040a00010b0400c00c0400c00840104008080c015810408510b0034040320401382525804950081c18084041001c0c0c1c11052104100c00c08110601c0e80f480c02107400b858141c0b4041507034000c20802d40d2800c000318203824031580410b042c2c41034040060159074244010022420100106000100d1545640600090b01400607200452140da00540c4450a251018007450640c9011007009059928124502c0d45c4510840c088240d15242c000b0b00703036000c0e05107070626101780e20120540d0312910300148442c051403c3c8013981113080807240000708405480c00c9098070305c03c2c440c11065a20443c0428402d18082040c00d03009441410001c0c5018401c1210020740742503044420380d640d646904000441405c01c02c1d0360369001d001809051246d801581c0c4031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 114557239 1250 114555989 114556007
    0xa020301141e093018040c0201020a08011802160f060c0c080a120b0d050d140405030a110102010b032a01030c02060a0b0102011811040612021c05071502030c0d050307 73
    0x103a10750410859641c0000d207204e01011a400d003030613080c0d40d102c01e5921641da40e89429a0140c1c040d0f4030b040002c0f107086206100343c5a41c044595100e80482e403034260819480a0503180d9508200d03400c02c92103040c036942140c0361001078894180c0c1009032032142000001c0301c802c0c140c100c090049494950000414200031151036060b181442710b5203034402c814400090210401d070301d800200041a002c20f0240c0040c10484240f01d596420440b5248202c0040180c080c034030076250194000001b80000882c03002c502a0300306010301c0000b0ba00c1c84400700082c50000b052201c0c0c44080550b8070010813924881004202c1d0103000c1c24140088441c07514025035407c030007000900080d95072240714000f07a00c03c0d080140c90310341c0d80107103548200c40e41c06c08020a9011103207151045140c07041c00641148242030400c4441d40090858a010000851b0b420400324540c0342140c69000310000410000d412054400740c1040b248d00035a101c102c42c1a40ca850112a1030110041c000c061007040030040e8400001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 114558489 1250 114557239 114557263
    0xc0509040302031b070e012306160f0204020d02030c0d11130302040e0a050d020f0c0406030809090a060e0c190801030209070509030109060516120903020c010507050a020301141e09 79
    0x24009030501035013460804240d90005240360040d1800000d4811041c0c0000540c00c1c401100303060500c400c3c0c810011b085c4a03070a507114102c03444501c802c1c0880c041c0c1c03110042840c0080c0000d40391180002c1c01c801240d00458804038800e20104444141000c5845580000303014144414688511118004142c00303061000901c41da4807600301c110003440a0201030b85895102c400c64000741745014010351609041d0301c00009900c076401c9100424a454081c05003100d0300907403440e29050b1410140520400000c1185259175110100044c1e44210726064520540403950442c0d10317641185e8501d580b00948040c801c0400150200600140c0c0e105603541c2d4001c000c60a0031076580000b0408640940f10096016001901e0801040700c078070035074407442c020300c8007590782c0414542d0301404981c00c4995108000c6d006074429012441d06500a00c02006802d00640845180c444035a00003802d540050300d40040000c040130a008009a43c001c1e007440001440f11054680c0c90003d092503038600c001011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 114559739 1250 114558489 114558517
    0x6020d08010513020306130507030b0f150a0e0a0f1202040b041e0c03090501050411010809070b0d0b0402120901090b06060421020118080a0c1409060f1306060c0c050904030203 77
    0x401c071280c0c7d81002084034060721071002d0025207050340e400360060030700c00104c0b8003d4500d503107922000c0c6072140f42d1401d408810808070f030601c400d5241c110342e110003c02e81290400195100440c4204a50542034010714106801d40210101481404160b8104980b0785010b10300340314016902c1c031b200c10003881c0303580242c5000140328850124110003500040320040e100d5480e00c000e000c00c0c4040c140c0080201542a02e45840588402c2e60300c90780c4001c1c44c403076005c110710140800d0000780820b80141c7c4070102c0084c0058241007072524410540e00c400c3d180ea404c6603645071713111010024007007003c6502120842d041814941f503c00c404809994074548680e08079a0040240110780c041c3c24044089032144111420441d02d8001a9544588200e000d44040b003103c500040c0e81c80b01a4a0100195070140c01c4205a490301028000c0004103014420343c4080c458078065540c8403107100f02e81c01080c481c2d070740c516682864200342c07181910f15000240103108101c200030200340c0010880e006030000e080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 114560989 1250 114559739 114559741
    0x140103030c240609050a060b0a05071709060f19050405010f081017070315090f02010f03090605090c04060f0501021914030a080702100509100c03020408030f0406020d080105130203 79
    0x180c014008a108020728003040c0c681080130034030800540c05184106050311003000b0143c1c841074407840501403070b03d5683c00610304100d40800510200c0e401088a6041c00d4228200002d200c00140e164000c9101d4401d000404034440060380030003081c5042d4400d00c0d05125180a0500000904c4042c424084405210810020030800c05001c0b60b440d00074140601c8564440f10010320144d103d681d03512013039484040c4012240950f00b902c0c4030780c0b0001603001c4448070a009140d4010b4400328000c00e61603007490f0352481c0c00008150301d406803501c07840b00e280c05080d590141a0400c0704403082e90b0030401210144030801e21003a40c00050303030307001134013003070268019140340d460711341c0c130703412948201401c58000420030f4500d0f681c1140202c0c1c0164965020781e182250f0b000002422280219074900d1260b100f521442416400ca6214884085603807501614154403082801c2c41d40d0701a400c80b00044500080c10000740b90305100e0107a0020503481c0c9901907500d0800040c0000c891102d950841070381c004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 114562239 1250 114560989 114561023
    0x50417030c0102040603091716030305151806150c031b0709020a0206060a120308040204020307180e040209180c06090109050d030903020301050c09060d050901151701140103030c 78
    0x4103031100e440d5120002d43d600d1741c0302c0c5002006000003240464404d140c80f000324009019650540f901109480081c20310011a0b44084010b0b0101401916002100c071840700d510342c81c0c2444074031000e0350302082204182030103030920500348410100d0307106019080c0311703a411501700842100c810300382c214142c6611410304445d00742098241e038001981d047c0f000400d07400c015008070b5000d10503081281d094010139a1000301ba26145511000200001c01041c0040c00500e0603078061030300300400b840e1403841400c880b1001c2600c0c000300d0300010000d45c41e0004000841c80c12080c02d503881801c200c0d050fa26008143c45442d643d06005090500c10040440d0368501a486103810800600c0014900c0028140c90306001d020102c00303010030ba01075400c1c01c0001d14850380140c01c603102c45202420440c60002000e801d40d00502020b0000859552150b080d07000fa000341d400044081d20044503188400b40c8070711690390844429103d03101500c007485e401040840e0f04280c0000e449508001d407145800f46d84 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 114563489 1250 114562239 114562243
    0x90b0109020c0c040914030309010c0212070f02011202040909030306031403040509070c0827010e01030b010512090a0f0803180106050105070b2502070f080a1e080d0203191506050417 80
    0xa40070400981f2001c01000f00000c4150003582c0084942e4081c0c1d03070780d4000c3c00f501c21440c1c801e080740544450003020681005500c5010040b82495819a0042c202504d0f41821000c0d00c0030140241c00090301c1c0c102c14824841410007010040c0d001000540c0f51615143c086052010010a8181480310203c1e0322010712216500320b40740343c0801030141c1007410001101ca040e81c0300358400c03d0300080500c0e0014400d0350080c4a001c185581c1610b07950300b030075030400c0c040d0f020780c0380140078050303500070340c001752002648007144401c0161040e000321b0788903d403001c0e4031380306030102550310b4000d6030401e0010020359801404580210b6004409d41c28281e40356120307070f0700243e2510114803418158444084c950303980400e840c026a4948101c1c83c08540e50f510318503035038510b440c101030001b88400c1e0700f00c00c40b0000340c100f04990502c200e06441c02c103090b121002003240c20032214810460707400511424520824450f011840d1059600e0050042c20000010201d0040c0e00030176001405940703641d40b213281d003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 114564739 1250 114563489 114563513
    0xc060c03070e032d0f0606060a030908030408030403080a050106050301050603041a0c1b12161704140405010530071802070c17030a180b030a090b0109020c0c0409 71
    0x68102c3d409200707084848000c40c2030421010312008213003121030382c00380e0000c20b091040c20314440060001341c8800301044500d50001c10110305065440481c8400900b0034070240d841035010707801c0c0f40d450f4a083d04014102003c0103010150461503c030050125903009420740707042d07a200b96031a40d1259a10318109a198845449d020181c02c80c0c07070304111105030700000500f40c03203141d002c0c0d03819843d184601c100d50302d8050240742c941c2540140203800c030121031400350b846418058907074039915500d18000d8914a40c0203800880c02d01e041000d41020750b040c10b000f520700611040c0e80a2a00c00070344a4010101002f0703410032a4040c2c196512420006c1c0e0405c040006041c0c8169a42c8840c1c41d41c0900d0340003907000100c120f82248044d600090b0003c0e03d1412001d400b4803030701c05940307030250f058011684920418019404000c2d1240c0c007213020342ca154081c51103514814000103009845003801c01410905130f02107892580100403081c0508404034200c000c102090301d000c5140c100c540380844d6142c030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 114565989 1250 114564739 114564767
    0x50a0206070c1103190201020f010213030f02010c0804060206060a050108040b060906060d0f0207050607020708030307050c150103030203090f15040b090a15020d0f020d05040b0a021617010b060c060c0307 89
    0x481d403020043d0f174070380001503040003602c00d8088510180c01d070007055082c0e008080c40e2508100300540c013040842d01c49941503078a01d2052501441d080281e40d14000140c010f5044000103a0000c0108030050404418441c054542401e00c0192481c2541e60b11a01c90b0b80100302e0b45c0a20014000b04891341c681005841c511000c45209008000001001000a405c070351400e5807a40b11342d1010640c4180042500401d40c0da18001070351460313a035100141d0701d9502100c078000c1a442130a084609107012145598040c610a901441c2e9541443e010005584841c0100f03a11955580e4081622039103044c0803141203400d08210181c440018000180003000180e1045c201e040b403101d264203801d0b80c00302d10138664882503180c5d40750010140301c0482e070301c924bc00742e01d0001c141c04010903c880021400070300083d1061740304403960340c419100203280341c6899601500380e0314410140020036007003e001d0500d860000351a09030804440c0c0034900d544080240540c400944000080303840c00340b14107100414a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 114567239 1250 114565989 114565993
    0x13060c0f060509012034020306100501020f070f050f03011503110a060219030302090d020a1721121f2702090a0e070e030114010e0106050a0206070c1103 67
    0x203d0310103800d90291138a40040c21150f41d843c40691004060300c0107031114064440c9280140c4042c80641261a41c400c14052000146803082200166810804a4450170b5120803548004e494a4000b91816010181503417150308040360074801d0008800b0740c04101c0700c0403110704a0011440340424010421340001d0314455450007404001d00000015011241800b03860911a0590b10403007242c44905140302c0c03880c801089020040804c0c800d030050040e000c4002c05201c203104450340090f9072032600b580180c6025110755007200c0d0580742407200708400308505003122540003441c0b182c0480c0e445020b40e41004d512132040410820298218909000490030003002c050755142d10b0307481200700d050451400403401c040055601048180240d9200340005001c03404202c2c106035055650600c000c1500080048012240116640c2401420300c10f480c540ea1b43d01c272035410301c0300ea25850744050b0080001e11100700910f8200643c0002c074280d10050300d04c1d0041111103217140900d0300c00070011407036500d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 114568345 1106 114567239 114567241
    0xe040309031506090504050d1107050609090405010b0d210507021e0f04090f1b15050a0e040e0303090615060a11100207050715020313060c0f0605 64
    0x114036003140443c0303d80d1150300035800c4902c00c41e800d60761135101c041044251a04001005290000503011f0445a800c1c040802c0591051010041c0650407020008040c40000e40c840c0d00800030080000d41858854180340d88149055400b540ca01c800d00048940158003400c100d81d10540c1c00f03041c6044050f00003240003401c241130404282c011940c101c0c2e266080d61284144100103101740d0b10b0b04180c1d6054100404030b1101444154295000f4103000e0082c020703441035151030001c45241641c3c0d10505064101d8840d0342020b91150018200110854900030100c01f45100740802d104540039036071200c1945c1c504c8000700040641008040018035004c51043c000f0f11100c1c0c4029045910040b40360395280100da1058070b050b1501d0b000034a0078044550f40314580c205400084c4010360400d13040d0341c402204210070f807041d80305200e0300300340b1101042100d41070b01050540003e0100b05c0c17 = true := by decide +kernel

theorem cover : BRFrame.Cov 114388489 114568345 := by
  have h0 := BRFrame.cov_init 114388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 114388489 ≤ n) (h2 : n < 114568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
