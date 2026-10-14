-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2519
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:57:11.326369+00:00
-- url     : https://prove2.me/submissions/4977df23-721f-4108-a1f8-4e1f29ffb556

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 452877697 ≤ n < 453057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 452878947 1250 452877697 452877701
    0x507020303164202030c0d0c02071d0f07090812180d0c171614010c0b0a09030e060f0a120209030d0815030109020a1502070e01150809071d0a 62
    0x1c00700e04190f10008242052901c07250142c8021503070b4400407150825511000c00c60003600d00800c4071b081e00d07030b05007102007007050003803d0141c1d04042148582003000612524014084a004242845581c250704005060302405030b0001c0c40300c4144084000c00b00038040000648010348620034048a880381000090308600b541a40003103944000c007025a001804590800c00d0100e4084038284101404882d91007507d460008190030038218000c1800c0010820100810001080526000092271070075035504a0341603094a6607001c0c99558010202091741001c0401c0c03020008503085410141ca0800c20b00180c8251642a420042601c083d00ca040403617070151020050028252404160308000042002804440b03d030f0518892107c01d004a080600c00c01c04100c2c1c0280c07003c0c201070f0600d11203401c802d440e1034040c0114425030400041044466008034060b0041030309100300f901c2401c02c0180510b901403e24600c641000ea401c101c060b84841e5250044e800340242030349569030706040c403c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 452880197 1250 452878947 452878973
    0x70f0935010c0201050603150907140402071b06020f07240203070b09060402130b0d2a030b040515090c010e060c03130e0703020403020d0212010e0a080a0e01050702030316 75
    0x111503082c22811211650190850351003600d0540072280c00118044c00d504e1041c40a84a60ba543d4221101c2030100d90555807142c116480090405443c080d07943d07407038610b004442e8010a0406070000786c00e1020300d03418403ca070400c40400000344081c07800c0541c0d2203010071001820420301d184100c2c0d990307101402882a00c42c0131350803030f019601924010252507101c5008440480c40b0302c01710218541401254030581004a502070240a0042810394031915244d0351404030780088042c80c40c910b049070900c01940d1000c0c6124100010f442c0c102842c14500c0c26040504d403600203001c0204006e018000003441c5c8500c1350091a001c00e40c80703000340114003103128280311980c460000040301d0b02c00b50341103c4a081252480d01c240412a5100ca0b41241240650302000b544284004a5070001d440d00203038104640c00746070000200844d400741602d18102800404848602c0f0114001459070b41001a10a0020707082c2000c41c5400381590000f61640710740d600754400202d503031402205100c1c607002110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 452881447 1250 452880197 452880299
    0x20a0b0304080408010f020406021510050a08070311033f0a0309050705010503070903030503181f060f0e070807140a0c060f06051f020321070f09 64
    0x6603032400c10303040c070204690243c00340c00610741c204a075a0600754024800c903008c407126503014190070021888034120951014040c00c01c11000b8200100706039542208400042640000901c121841e519112030014442810140300380c00003c1d508200c09152140501c0e0303000c1541000c0e0402102c4030220401d11156401e040c519600880d2041503aa059030102184078000c10850b5000e5076902c00440c1d981c8011200b907030000d0070b101010130000b4002e50180d03401607089500104900c1d612100103240502d00100c94900f980c0300c0007030aa18400300d00c1550701910840d481c1616550030f000040c1d90a0300003030581340c01c100c0f00c8400100c203188a0305180c0750b902003014445565055084004104c002e100c64280c03030091a1000361081070a0314800c0038200e0740060200402c03561049084850301d0031118194055020411040703044103035450340d807a00420b1904824030315090881c1c005101c403003524410414002911800d0015000c015503d0380c420b08055041c0c0d1955410124104007090ba0313170456 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 452882697 1250 452881447 452881469
    0x3020616050307141621080409050703020a12050114120a1b090617060403230313060c050c0a0204020c01140901021b060103030f030f020412060c030605120316020a 72
    0x3100802107a20744e0f00750b40200600403691541506040201150b4040c4100c48549050b5101c60445003407008400780000c2c0680421030502d99551414403d17200c08451800009900240c8031940580042200d2850100244204000e60404c920044003280582c1101d00c5001c1d00481005041c0b010010322641d654400c0c070440300382c9201001c040d48400035014074a8854200507011520300ba200d2054034440e030034540101220740721510140c50b451b14008001c07400c911180c2515118844040c021800b030480200080040d1a1070305103002101c8544500d0010028200104500413400199448000d80c0441d4010ba50701251840b95005080360342003045102e881404101c6c0ea00c0040d03000c0c190000d01c1084880c12500124806501c0700c0c02400b005000c5503000b02c10301503051007903001048600c442b0701c0051034103444200350f0b440114030380c1003283c213241c41d540e4410344103a050003403000610080e2940c0c100007140c5102d050300c070301500300381c0702c4100700c4184218207654905207480000c2c0030f10540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 452883947 1250 452882697 452882707
    0x1c0902060c032a16031209170703061401060f2d02010f0f090f0b070912060c090e1506130e18070605040612020d06180f0f0b0a030206160503 62
    0xb00d40641d0f410504980c034501840c00c0401d0081002148240143d1224940c2104203400d50351102d80d46020324008104210360300b440070804106131a0f6000404c20a01300800361a4030f076103810030556104100c00c04210f0744250042106a03040208540c00500d103042c031494080600010700742c020f03040031001400041c0c9a02c0e90100c40c0d010b40c81002801c82c90032083c00008081181d6000382c03040400010420300c0c03059102c4000c105e007040c0340d640043d100d19085800a9076003669a031511041d1038103403045507407003c0b02002c203034014001600030070f80441e0400c003501d4088166042c034106000c101c1d0240800281002c800c0482e0781c64100603004c1c0c007840ca0740f50306018045501c5014906082c02c05442040008180ca5000ba03003514101e034810b50301c0216900c10340203c88040d42001702e0030000d250310750b034000c580301712040030f444070740c018001d070000b00101303101388150645410718100700c1d0030341c40c209400c4400d488415241c0c090fa42c041e80c02580c1c900708d070b10452051051148000c1d04a01010517 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 452885197 1250 452883947 452883967
    0x5040e062d01080606130b070804050306010f08010c0f050a030b030708030d0b030d020609030d0b010215040311070e100308091309080301060305180c3007090e031c0902060c03 77
    0x21254265807000e0742d48000b0384c4e6985050050611401003460070054110760108014a40d50300141000b0340724100807070403e40d4402c0841c3c5000e1007a0040c65010304580414003a0f0b1b03000344a1000c4844c86450030003d401e0290002070305600ca0b4125000415484039503e030201e0300c04002050040c10030404495072900c021000e20020400380c43c4c0c42d031090148a032038060007440003d059014650541c042d46c5840c1c18200f1220044c00f0080300c00e81580680c40000f02d001410302043d51140d4040d8039200700c9400480c00290a040c82d0303410218800700050140f0200070540103a103002d03a40e101d1012950781409400046000346106031285501d4140941d403420003510b20007443c121000f03520244503d444402c407400c01c6265904882000e5489610106000d2a00d80100c030607059003101440500c0c10000c0750b5920500310600e84000d0b50b400000c1c00c10070b200b40c40c80307841401d0021a0145092140200c50600e90b421000040c80456449594007030655954100701c07064061001c0440742d2b14041c141d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 452886447 1250 452885197 452885269
    0x12120409022508031513050a0b0906030a0c0519050a1e0b210406060b0c03071407030b0417041205011506080c04050d0f0206120405070f030305040e06 66
    0xb0520b4080500c21200000301d045540074102d00035034449680d60035995413140400030300001e805c000364840300e52002040482854030400740511408080801c143d04c1c004240000190090140c1d0301036403011031068007080901c0c03a0001601c000f10f40c1e00b00e10401c12203148407407500940066034452200140029040340c3c00c0c1180d041d0483d41d41449010541c0c135a200041401584501c4d200480d00501c1540c1600e2070510315540720b4441e420008180745c071105140000d800c040d4400c4201d5000042510500c40121000041d9416100c0103141c0d140c19070396000051000a00300900310300c042550301c2c034042c454000b540c020704580000b03440050702d241811401381060100703443d01110b00a07004954603106101007445082c0c0300e00c509180610300790900c00c9586501d8400e5801e15030201741720300140d85820003002154920011044942464141581480450340c482d40050005100c00c00000780c03c0030941e000c0707900701c05803400d09544040119503001d1508102c1841508235070184550a2110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 452887697 1250 452886447 452886457
    0x902121f060e0c0306120f03130302031c0e060a0c0f030c12020f1f0b15070203070803120105100c141f091a070c170304120e0d021212040902 62
    0x28010600c10710766101e50b20080c1d0841501c205000500030030004046044c0950803c03030003101a01258030a074981032040e802c43d0001c0003100450501c00c2810429880c2c10403480160408100d1300c1900c4400f10880a4040050210420300404000c40d29803c2e00b40904461592680c10031000c2210821743e103401081e015580504440c0d22283c44102420b4510008038038503100802401000c581c0100c0322580c0c11f91030f0264281811681f1030300000c100d42c03107054461100103186c85000e900c0d0350003481090308040e03403504616566070060014105a50707000c0341241c1102c0e800d65001d0710164011200b10703030f2440309200180100c00d42c1c4100c42c2d85800c0000709880741c50f20841c903141030030b09000640416901082d8014010703130a00950702c00d42d8050101d80f1900000703d0300346180d8105103592a0310000d407051044e1f0350040004010403041c4418003507980340c0411246005010f010292000494800314460040e0241444d03c00b00c140d100c4082000003d49114900565160b42d039491450b0f000e5804 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 452888947 1250 452887697 452887753
    0x222110a1b0209010303120b040e1b090c090409031209030e0301111303140f1902090609090307060f0b0402131509030c0b070c0b040618080f0a06090212 67
    0x2124892000001c0d0044a080840d50041c00c2180c5a480c5403001c8407420003078800d9a10856444030361400c540e40e140b259829a4111340c0c050440280e8400004808a001030051401450f451040109007807070082218808503088900007606c02c200d040c1100c00300c421107807010700c051501c0200420b258004111280800b801c50091003110942d10b0343c20103502800d0300102d80c2c071a000b4020310026200c2044c1d529500b82e88004c440500303841c04042ca281800c00c07290440c80c045008200402c2d811301c0542c081d400281941c0c4000d0034101025060b41c3c911840c00c002c0c0c501030303540710005440a0190410742c0c80c488020415501c03840030040000401c003e9104007000100d07400c2c680303010769004000045c1169003140601414602c1c1400c0652039034015101114200e20421020802caa454005007001d8109544c13820920b11140c1100c503d0b160b029006001d040c1c1c0112845400c0131000128011030590001c004140300b821840816002d90f110000c07110301c1d015184081d0400800ca00c041102541 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 452890197 1250 452888947 452888957
    0x60f0f03021e0d050a0209010219060b10080906010b030606190e0619020f060c09091308120a0c0201060308190903020405040819091a03130c180f020909040222110a 72
    0xa03130245d0801240b1800030258096004100d81c4500800c68001a00d0558040c403004504e00c0ca890000919000001c500c1101040c03c4102b80f0164030310801c030743c5001d4002c0d1214a46181801d40008034903008010015400b07416108804502d140310f80c0c11021485005400503441d40b41c1600c11040f00b00121200d80014411520140594640020340030b0049a8401c5403e241400c05400d01204284c010b110000340e02103a0004000202c468009082209010821894a08228080758240c0b4209001c0400710780c18003a0034400304080c1c4084031429000581e959011801d030000a407400301a507440a54041d203004204014402208000d02e00b48000c0841000c00a04120054503015140d02461051343d1050000c2e122501070b1398000d54008410112071000440309544041d402c01e81900000d80380c10307600000c5090030100380244852480010030650a0400001c04112101c4000f00082d20500c0c04440c048021100300d000142c1d28441c0c00014420f1100034901d5054039405070703903090005a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 452891447 1250 452890197 452890201
    0x70c241a030f0a020904060c0c080f0909010b03040209010608150414010e01050a0806150612070309020108060109180216020901030c18021207031d010c0c0506010f060f0f03021e0d05 80
    0x20000c14034210f42d5a0050100e802904e4945400c0c00401c050000c10040c0030003040b4178004502a04041d02003018103443c550741d070b80c10f1442800004d010684c0b01d0072202a05205210060f41c81c45a1241564854030384082103585031b003c101000105000d0903030f0085d1512504140d404020034906043c0c5240502e18460343c1d907079509005404d24184100c10440e00001d000c2407040b201105070081ca80c100810490820b1403071024400515020b0320b052000c2560392003110b085503008108140e0285c001d09081030300f86e260028542d8504080000c99503d10b5000a401045032244140c4489a42d0054107800b00343da100c0c501180204081d0040101441525076072200d00c8040c1d000f201c10900010350841c085840d803009c03c1d00581160002c3c01000740d00c0c441c002c0c3c0290400d11a460005e40e0b590364921452101d0f0405a05044040c0c000780d01390280030034144985074005800140d1401c4504c1c0c90541d945070305008900901580301c480c121442014681c038007041038074004d402d0b8140700c044100195 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 452892697 1250 452891447 452891473
    0xf04020325172109130222052d1309030f080606040311041509020a0f120612080703050720040f0e060c0f190302031905070c241a03 58
    0x109041410102c0c2d07054406403c80c0080c0119014250b03105000e8284801818043c079010143d82184804807107040e00c0000301007204500812500c01001e040d200c10389041d00c80c1a081c030211980314150707041100101509080750315114008040c007088038000b00701c00d803000e2400800482501c03510303400164003040444c40c40e00e0204211811030750f00c000415510b503070501c2448083d200d86d94a00203200400350780042c010011780003c0c04900344580c1d80d003903070402614010b0601c810369100804410300d80001484107494004001091a4006903020b496011501e0121203510800c60b00512010f5200070215080103070071071601603030f50100c4091040000341c80c010411038401d601110030a9100001103000920f040c8004c003030b8442c102c003585e80340011031030421400c0203803401031f04000b0794004100b1070207100071540740b820845410340520070703420300d0600101200c0b940c04c00505500c0c2010b100d0001c80c1e10b41d03104d16518081c81c40b030500c001990411049140503c00c2c86843c089c0c00750800e06010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 452893947 1250 452892697 452892703
    0x30f0709060e090a0b1f09151704020402031f030c0e0c07050c010e0d020901030f06050c0a050d0b010c060507081605130b0d090b040c080d08060105030f0402032517 72
    0x100100a44811965507818034007101820138600d417070341c010314149010f0344003016050710184500740f15201c426200b0320704017002e288181d04402503c1049086450841d05151201840d908290129400350b10b1707488642a080c840003542045000c1c1c0c0c1c40a0b50000304014040c060a4103d90404d0940381c5540e8036550640108d225401d401009a0407800f10b140056003d80c08440c19800003400f888000c201b03135800701e9080e403001e8000390b41c1006034902440c104107140c0031b02e03039209004100c0e0505040005d64094098050881d0183e2080c0c1c684c000068a64803500344480b174290401d105000c00c0c109210064441003003501c1c1042006902080003402c1d0340500708440d11000c030602c0e8ac4940c146052182490340c1c1003100c0302942503407990f01030b60224110740a55801540111502203000d458202c1d40d51070102d60011000c00d201c9050200007642ea0000141c80e4404101c0c0c92140c02d42d510345c800a82040c1d10340728503610210348040f110212040721003000056070300c24400c03202900318a071131440c0c2d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 452895197 1250 452893947 452893967
    0x80c0708070204200f180a0501020d030f15141f090e06030307061104080c09010b040b03090709050c120f09060417091c0b0615040504020a02070b030f070906 69
    0x400d00003000404014203295029962010001402d05a0180b080e00048550340c0132071088490440040350490110010314090f0401c448121803002020b40380c0301c00030792105000c0c4d2000e414180d640049002c40394082c1c104204402600e0410110b00e600c8603d041a403110200d910750081d52000f089101c01203003800c0c400c3e96002a500c0c4d6052031441c0c40301402c0d4a40000b0001a0180010300000700041c8984c010036403005190b0240383d48460500145070710380356500103014450305185004011081100003118285c50361b103203000355240da5096100c0e28040b440c2c4d02040c0c016180408102e54810020040c2000c1c20221b45400b601d61219400410308030760580314120142c02078000314000450140980b0710383c10440614600b410a8500004d2120b0b602c807840c101440d04d0014400b003005a100c2e2640d600100454050038004000c0b21420176034003c60145900a0340d0014010380f41034000c01240000780486060030343e681c504146441608502078440501049a10030b001c560b45011b022554 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 452896447 1250 452895197 452895203
    0x40501030b0a090201110102072301060b040b07020d0515011404060311190e15100201150306020f04030209190506060a020307030c0303110d09140c0f060a090e0f040201080c07 77
    0x40750540b603404251008041a05049060100030201962211000e0010303282c501d001e900358140c07104440000c06074102d44e602000c496640b508078207100c400c007604180c0b000c2c0c03400403074a16100e62107840070402c2d18408040240851041c0c40782c070034002090702c501a0507500c4006889000200f0b050601c01550300600006100c8a0800582240d90402c0e2442c2c0d0b500503401010f400c001951008402e10048003035401d080b290340c02da005501e640c00c01d00f600441d2081140300802000c00354801c1c54120280300d010081205030001903082c42c4865281c10f0390040d5070010010712032030402d20000341512825000101c8040d0410b80042c0440c5088401d8030200c0c94960040c600c0c00340180c0c0e0480c0c410340402001c90905075503001704000a640d07800500705d4007240440c0050031178200c2c2083c41e0410800b00b403550b035071707070090440307185503140d42e1750031100c0c08012f45220342c8485040300305880c09002504061158141f4000300405c081c0c2042c00380d40a58001c0e00d584d0942d40311210703030400e541f16248010b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 452897697 1250 452896447 452896463
    0x501120608031206060f0a05030103030e120a11011101020f090a06050702010f0e030a0b010e0618070212070510021903060602210307030f02031501020c0307060f39030e04050103 78
    0xa029a01c040003403040d40010020710141c86c0100210a110309174002c6006400020404030040c82019007041e00840c5480045074420501c4103640c64940e540c0200303003402048080c801e80540040e0740107107091045503e40000954990882d1314886445400c142a041c0c4104c812a4001402a005000f280d171000e406942d2140c03802d040030019500070801c1c80c0d2158040c03266100401c0845d04800301c09010300a41c854006c0070f81841001c0011030350303029001609150700b800c00e012409400040c0000031201030b0203c9911810745003419414071307240f600034006041c00003407610710540890004506003144c1d91402c1001c2921800120303aa00c80c1c0002c50440c908180c845a00d4480c004805142d0001032403401080014882d0807a0007079801c1650140d1080600c4c00b1040301560b010f00c40081e01d203006030002c0485070b00c0e0000062055003080e01c010240702ca0100305c0030b1000d0480b05442c041c044051802c1c41307024603144540380c0d609a400002d5001525200a100319440c0c140107980c102d0b5040869 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 452898947 1250 452897697 452897707
    0x90903020706050c0f010c0807031505060a122901110c03060a090f1704091a090402040902030f030703021e0a0c1505070c030c0501031d030a0806060d0213050112060803 74
    0x1c1a9125408013086143d68032440203105408402405100050400c5aaa01000742004c20000c0c0c10b9900e0f201c00c40c2506060003006200c9900c9100031380d107015056207003c039041481e05440c0401001c0320f070078031034104030344804c91040701010f180d074500c1d904001ea80300c80400b216045000d8446400c44a03d0390300d90060404034160900c203030086d141580c081c0c48008401ca038507035281c0c5a00340b4041141c0800c8000402c00b08020503d134424000c2c040902d914407c078042030000069800c00f4001c0c4000d1140d0307038912014096417402c1000d0498000c40c94204d917aa1015424042d54400d6480704401c080b0444a0079410110b40216000d42c01c03c0e40288400c0f403c5003466030001201c51400e02d9070003002004d00c0701d6000305200d034400c2c50096025102c003400c0c182c2004001001e03604501d03800d000e8501d0000c0503400385a400021541e0802562030700d420360352504000510b203803240c28421895036001081c50795100301c40d41c056000f21202602e8403505034146a80e1007042d0384a81c407600140d07400501c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 452900197 1250 452898947 452898959
    0x606030c12121c0c09050307080706080406151a090901060c15090825051506061e040902030703050601030606080c0d110c1603030305010e010f0b070302120c0c0a0909030207 76
    0xfa02003444200c40c0c01c0c1408001080410031101105403010014681405c1000141000e002040203812960080c04083d81080c0c0060701040002d00020300d00c698410115aa405e1600b031480302600d011549480c143c42c0300b450400c955048030780b10301d01c500c03455000010038501683e9141071407075001074440c004a212544140c010300e40c1e030700c0981d40c10004201c03149901e4041004c000100468984100c810034490030800c0c58000002c0740c02155181581c01d1060607519101911030000048a001e0b4801190b145070009c10b000d1030f07020240701030000c014044515056048544250401c3c2da0411020b5074510080300c0c01c207015280c3c90038000040028004c807821079000107c2d940c003c1000d8034900905040f940c1c1c549030344181182c10000c00c0c800c0c10301c10140e26014541c010074642c8146441541800c0003400014403038481d8003455640000c141003058000c4c0117100219142d008805d44407041e55401e65190001c1d00905031150034846008291104e440c8541c00c4243d4050340246403013400c00c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 452901447 1250 452900197 452900233
    0x3020d0804061b0b012d0b0408010f060f0314010608070e0405160b03150102070509010303090e13020307050d0201230408011d0c0d03020a0609050102180f010e04020f07050106080606030c12 83
    0x1907000c48020346c81510680c00071030140b450b4030080c0000100556a9881e064407903084803e055000040c450506104024100011040200396034000160740420f00d000e141407401403840394001c103200c3c01552000120103081000e440c2c801c0f40500c2c150394402a04008648842419016050402130305101040c0e501c03401c44a50307055508180111201a174540e07002407075901090303000303c000514403a01440072031403082c482c42d040391645001a03880e05403a40000c0d00c440c0740f805030501031404c400d080c20540e8424504502580c400c0c120b600c2c00654003020f1404244d0183c0614415982080385804035569158400c80c001320348000680310040d40501081741c60079507080705404620070b92444901140181c400c007441c0a2007074000580d642c1c1c40142043c207040d14003070614429410342d008003030181d80058004244001c1100d0060350b07400d116103401098000e064010f0915071901d000899240000200140120400c408840c40c00a5040402c000464154a00b1445421030380721180162815 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 452902697 1250 452901447 452901479
    0x6060904080309070305101a091b07150f0e01050c13031104020915091c0203100c03110a0810141012110d1a03120901051303020d0804061b0b01 63
    0x1c0303c1500c4c1003a56a48039a40b07451044d44007074500f140e454400307440d144041146540318803c19502506640303441c0d141c500e80c0c0140400c552020404c00502c4500300320300425009507060110394200503094001110740020324a080908100303600c1c14011131490011003090320344081d044400c00350460b08564400a40d4040000a69040303030302400603200c16940d8a0f03044403081c140e80e000a460740c81d50020000e008005440901203007604801d42c40144e1404500b096051144010207e0b150207640411801821480c02404600001142c24010b003a88800601d008003a89814000101e03192240c44410301005405c069000c03400010f0800f101d8080e0130360b806043e16032100000c1088002911401070b40c0108440c00d001a51071b09004034012507035012070911802035006210b102041080c2c04114802ea003002418440f010600c01d42c0800710b819184041d580c040c04094450206241244040d0464000c400c041020071082d1516121804004040320703402114003403040c0d10703104c81003400e1200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 452903947 1250 452902697 452902711
    0x3030613020f12040b160905011e0207030c08030a08010503030a0f1d0a0306090b07020c06030106031515080f090d021009020117090601061103090a1a28030c02060609040803 76
    0xc3c04100004001c0c1050144114005c00380e5003118540510307080c0d01c10100031654001e02c003039020140116603000c0411000700441071081c0d02460f02081c01640b60031440d900c01440b20410401c08101c444010020380310681035610b0718030302a40c840c803c00d40c5074007e42c580f80000031046d40b13000d0340440c40740503102643c1c02000a1441402c005c1404180324020b031303800076030b01c080d2102c0000007004030a038003069000501d48050500703103481d03800140c210301c0103220343c2c000c040e240c45d0a0706e01450380c1d00b003110080000350400030340fa51541030090801402105d214030b603550490001003000b074001c5400c104455040e4060070240c2c20f1030130b5140042ca08080140d0403c007000c0c1c1000b051140b100710050240c0000b000910f065803405400511144041c00500c0e104c1e041807002217030a440d20b0803175000f565200c41d0a0105481c0100c0310f840d41d4044c04200d078031a001c0f4603000e84041a0301941051041400d44e4090110034a8200300faa600c07c2d0550348203402c0035160b80001e0210301d40c80095030708914 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 452905197 1250 452903947 452903977
    0x50c04140915071b031d09040b0a110d020c0106060306060504030c15110307060e0d0306050904020d020102013207030c0807080703020d090516080c01080c0306130e030d05090303061302 81
    0x280d202800b071350211200390100d01040c4401d4882040c0040103e010340f19110843e4030103c07510301982e512454100103051020403546420b04a000f209099040c0da04c2d145a82c13004540f00c04c1d070784034060702034055031080c1c00c08680b80c01c030045186032042d41258240c0c0d070003400308018981f92115090074183e00256034002c01000c200500e00409092004100c2d1500500c80400c1028031030b80c040e801c240c3c80000741c40616103050010170150b207401000c1580150112a00000c03201c040c00181c0c090300d40001080c0702d0340144128102c0b140c004000d22003010000320141310341a0b89030714041d0225024506004042020000015007040c40380031305a51002c414900582400b41455021b010b5400042c030403221a00a030310a1003c140904040d20010400b0000800d1000140000a0700200c0098014090024000001409070301d9207138210282c0341324414100182d6440107100c41d125009100800c0400d8140008604103110000c2524050701c0300404800d41c070059280c2c00802540074008045801d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 452906447 1250 452905197 452905217
    0xd1d010503130308090a120c0b10050d060b030123010e1605030406051810240b270303032e050306060d030c0c06030b2409010c020f0d050c0414091507 66
    0x1100c3c01c00c0c8140500007500d4001d904842d900e0020303102007002b00b8a842850168804200540c0c1c1c14001581e51a0030000020750303c0881400710780513081ca10031740041d4010100a104000c1d00d0907400700d049a0716103007013403942e44505003183c00712100703181d00c03038001a024408207000c01c078558840b80d006000032000c0c4116100c14080c00b403d240c0c0a840074003a50340c0d6001c0c000b2450100c1880324000c1c040c2854840611810300d114000c0a0258488070351500959030590341901007100258098020020100d070380740e2030442198544448202c1c020b8080340340030b071422108050740030100c1054680045c05041c01d40d03070b441c047c4960607032510001d03002c00c09002c0d2580c000c207880c0074000c009020556404213104204005101f024560f1b0710822004821203460b0500c00100740043e01c0b1442001d18000c5a4802c05000090307549510181e11548401c00c00068000c0141c001200240904252018840d48100509600440c20111400015a00408145840c401a010700d084e4070680c00d0400301d81c66 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 452907697 1250 452906447 452906453
    0xc030b090c0d05010209241e1606020306100302090f1302121501020f1f0b01051b0106090f020c0c0d0c030b0c13230f0a080d1d010503130308090a 64
    0xc1a0b410000c0d540c903540010981c400b0b0812004040207818a040c6034801d04419881c0c5241c0b501c100103404201030890000f848001140700212080b003035040240100c484510f04241c00298000d442071446140c030b500484490f1402030081d90b25204000302680104012042408080701002c10b601c00c02a9003000f01201551600c0d0300d040c0203419140007460a60703500000a8034220418031303688003a03804414040c506407142c0080420001d100d000c081031b40130458005036441d000e21140380e5455501c0803401108498158001c6084a2aa00c0140488034404040f08102e1090b0140303803a0300c0d0000d400c43d51300c0b400c1821000d14601d2181c0d01000c0301660b00d071209092200142e446080105c0d000a4000000400b0110300c0050328241308241c4080003c41c0250310081c15040145000e4500d400072050184d40358100d90000f002500250f4015803602040248030807505911100d0005500411200c207500ca18141c034882c003101c480c01d500106140e01c09603105a80100900d003544110b1600d4000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 452908947 1250 452907697 452907709
    0x40b0406030501020706050f220c050405011401020c06090a0b07020d02061605060c041d0603151609080a0c031502090310020315180601050a090b07031e030204030c030b090c 76
    0x7540650001170329003400d841c100b425504003400008400d040328060000050055440c541100c0f0400c1e4090964111392070059894121030340038641c031524210000441000b07040781d10140c00000d80c280e036030311100001008020b004038054503400002041c028000b00112800a246c0e803400108051402c0c000c1b640014a0755100800366060303407401e403c1c080e00b04402040801e400414201c1460700b803500b06a24804c00c140da8400e5000100c01b80c40c0411580e4505004680c3e0083c501c0b21000d12620784040e05d51091b000c00001840000c0c2201000114070740c0106080100d15402126280142d15607100c0011454030b20500f1a4003644c20030032070809030740030800f850740d4610302c140240e144c0c82d20320402602c0c01c810022b501d00480144810b45d911450740d0f0100d0b5846802401e02e51303150960441c0c1181c800003950410350400c2d4000a40c0410300d50001e0300c5030303a030301030b003510900101a6241c1c3c210140e00451100030500b0801e650306000007104a0b001a0f03100c0c00040c12500c01050400c00128 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 452910197 1250 452908947 452908949
    0x109081e03010302090402100315030615170601060e0312120403031b0c14010b0405040804151803120e040213030c05010c210c05060702010f0b0a060c03080402040b0406 74
    0x206404000340c440d414114208203000003803000038246003150303d181c0105214180081c03009206d19030411491410718042d6114a0301840070042c240b80706a140e281400050128500034007050034010030018481d5880c10100602400c01009013015074030f13000302651a21800421154540641c0c408100880384074800b03450b10a208002c1a080350416040140495803590004031034440070303a151441070760308110203c0440b5403005e003000ca0344c0080c0c1030050040020480781030b4442d080c4800c3c80305100011028200703640300d8010001c400444004280c3e00200c40004507a000b400180b01003000c50000c1006c035a0a0441342030071400c80c80c4040c005022039101103450751074491701c003400b40240030f680e200ea48081c0a00f0300700354902000d15203446240c2c0390303152200c81500c0e105c0c400300005e81d4420040510f541c0d174404102c41040c10242806406890f0035003800f0309041c03401c5504004d501d0002d08950846080c0d49400d4141c000c9502c080300c6401c0c3c0200103a800c00c2d15aa1404615203a500c00e02e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 452911447 1250 452910197 452910203
    0x19020321071b1a07030b0a0611011a1f05040f080307030908010b1809070509090a050613030e01080714030901140f101e05041517060f070e0301020c0109 67
    0x2216203008900900001e0840494442ca200c10b94440e9000074550031005080b032204501c104083d03603a110044002d492003012198100c200e9a000088094000508041864002d002800100700070030038501008014131105900000c022004407400401100000c8444030911f4024546501c40104102c0307130641d503202050a920008008062507405030400c0c0c05400204000d010202001d400180f482038038048000703090404001140510108100072801460007038424181440e00e25080742d1640700e240010f035a0b41c068480010345c1e04e00080c80d0000c4039a8035440d942e06800b00c0500450f0351900040c000d109000d0490011400920744201a505ca1955003001041d400310031308503903540360000381001011104403401e0001c0c10101e4441c84003070394a440c64542c10380b850540c05092000351a480207400502d00b80d0300c5181180012280c1007900c58820448500c03451410b001541e0b008211500310a031040f410201d443e40b40700b280b422401d200300900241c185007007014003a003140c00042c411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 452912697 1250 452911447 452911507
    0x30106090617070806040209040905010e0a03080a0e030403171e04060f020c0303030c091c061a06121f0305070f1502060103120509061219050a090206190203 69
    0x304803655000120902c0b05240b00d018000300d041044000d40b91180280c80a4403807600450700300ca150b00c861344510702803608840284102807040c0256622554001401d034009840440050192001e9000700030411400f40700031881e151641d00c1c0e002c803000c407488806940c003000304800012018809188685907030150038444e80e481c50120050324448091480300c6c01c0d9008011160010b50b07010056039844054060100d954240550008140140d00100541c51000b105812014050f0f207511240c0320580c00800101100302c8002000054002c10f03056031905142100019000a802c20180c4508590b640000c8800c94030b9036500c0342041c003079401c03410030411b085000f001040504c0c440c10044003081e0014149039415611901105100e000ea00418446c00040c0100c882d11020300f118000c10054040b4140790810724581d2205083c900c40e4000401e0920001c10128261442040c190036802820365140c001d01003403540408901d031306510150701044c44034025100c0b041c0d010191a101c45e41103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 452913947 1250 452912697 452912699
    0x2190510030f05130b060f030a1b0303020c1e01030f110c010207050c1807050f1215040501060203090a0519090507080714190818030d0603060515030c060d0905010203010609 76
    0x70b00c00480354010540c00c05a5240301009021032a6003505a801a400b507502c01003030314008011a00d0f113019000c0003170004400280100041d001503a822094901c20f40c00d82d10301d100d00c1c2007000740c0c1841b80c0049558107a031007402480301d5030103580540084480344201040140ca040000ba05a4004000081c5165000031f0301c3c0c0c040110500c4140034a28007101e005440d0051a8444080420010a10424448001812102e41d4110b000b81d490002c1448108801c5181c04030350014000700485816000f10300701400429003a0000c07050300e00b41031000e00407009061804041080280da4041d204621503010500440c03514414040d041c4a6900394075001068100100020b01c002c0b80229146a070307103014800c06242801200302503882c103601d40303800c0f02681c54000b0410142c08002c4d540998520000480c4240503000340c221074100c90003403c08000c01d1b03580f0700c03810620702c0c0b00b04100d60b850382064481100a00d000c5010704078440c40c103a0300180380c042a0381c0b01030886e402030b04800045041810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 452915197 1250 452913947 452913971
    0x60310091401030b01030b1302091006020d09060203090d2402090901080d1b06180b100506030103151e02040803090a150f03050c07020d111005040b070219051003 71
    0x4041040d22400716101c015851600e500d130a040f010300005100501000c04620026009000100019001002e101940c204410302424002e020b11500e40540a5070302c2c003003a002d004404207801c81d01640c000e1450f207a605405c004a002080b0300c02c44040c840490a40140180d100d110a20811031590059845805c0c0c8100081c0c183c0503030000f5210350101c42c151510300d40c4001c880d9094071001050b4211036820740740000280c0704c00d100c403100e0a41c01e022100103119100306998004c3d80d540180140a54070b43c8140300040c40f0900002d4451038200154840000c0d641d40896101c080c245c0c2c004c19103411444801c01a64050380c0314032455032010070700e04014070f0b100f01d480e0001c19082041c10742e10841910050300c0568011140170500da07903480060b01140101d4201d80300583d0007030689060b8005454441c01103140740010310700804520055084c0f40d40500229003d40e0858a507844c1410255801c106403c581e20126900e00403005000145503182c4406128080c4019100442c441007018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 452916447 1250 452915197 452915201
    0x10e0f0c15040303090522050f0403180b07080307031506020705030105060d030c02040519090c030b090a0b040b0910020a0309032c01050c0f03044703040c0506031009 73
    0x10709612180745080200700f00003a081403a41d4100c59083c1d484446180c00a000c00510400310710400a08504140c01c10070010f071500a510320a0348203848001000030340032140302202e04a40100031358403004100c2d62000c1811302001d13551100e401d1401003054800b924007124040101d0b84035102582c81110300344000d01d000c1c0035542c0c0c000d10541d4280903480315510018080e000291029010b0781c0d1740c50100e25480d40e81442c14401050440060241c1280f600e048444441c0c10300c0140c0319081c03c1c0c40803030503217039012079105a40e6400c510401100e89503500ca0562001002c8c001d0300c0180b00e0b034643c201d040070050024201051081c0c6000417451440d04014050070400c8014010800c3d040c005824070000b090000059440c0038606a51168105400c00c0d1900b100746040c4000c41c800458002580c020a010305d86c2c4c5c02030b40c440540d1b140e003038a1000701800984480000c0e104036154900075405a00f00300903681c4140030701b806011031951440400c071507600070759982140c030800b2101407191804034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 452917697 1250 452916447 452916469
    0x5010801060503031812121c1406060702040902100c06050112030e1201060302030d05030415200a050913060611010212070305152e0c0506130f05010c0e011707020c12010e0f0c 77
    0x603c00603c625083c1840c149c5000340300600892003081c02003603c8055441d5a4005612039070b0141c4045d10078030814401400340f0b01001000c40d0307494141400461008642605120700c40e906132540c1003562405006c000381c0c40a43d9088542d06d41da40c0f0030000169808005036000700c45240c03121a52410142402c0717500101241e07040c010b190500b074219226116480f80c200d2a0000500d81585030344400300c0848052142c88032581d48500208481080e50400e91301040c11035607280c03600d91301c3d03207a40c5090310700340d0080010359080d4810080001e0b5410b80207402043c0e00c041502c1c2c0803401000e44100150301d866940c00721190310b1a684002d032411540c6500d58521040c1c00303042403041085103030344159076081c3c024542c11010101c0300b1034104100f00c00c2c003e0040c0603481002803000f5441e030080201b4240c03010b04140e0002e241007541c520085200a1250301072003290f4083d02452003440103110190070381c1c0c0e44012180d0360364183c1100c00f400500c0070f411140c80c00409080305d9112101008011001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 452918947 1250 452917697 452917747
    0x30912160b0112260c060a1a0913020f0402040902071101081008032d0703020102120a090503030f07180602010b1002070806011e17030304060501080106050303181212 73
    0x50000f9050201d0820321100d49008003001440c44407500b21645003040b030060741e06030001c500c50242405050f030031070b4005000c032008003e0036503505e00f00e6204104042c0303070a445414900c0311040c0c5403409410304034401c2e1800400608003610345a0f41c3e400000032a1f00c01c03e010348030102c015210800030741c1d0001a40d50800040807243c11060305150300c1c19204e200c1e420901402040c00c1784018040c900042c0d1102100507500c503900e807503141505000c0c0c080e5001020303603200403644800060190960744120446581c000b001142180da0b40c0035041880100584103105011158a40b0203a14503261000c0025026036400031803040071a10501840004c0f8581c888295000120103001010340003d0382c50445121010610b030031100d0901d0340840e038945404c940c66028444034500d8812200200460107503104203010002c4d40e980340c0e80b8508842d102e0040039810f400403c0707a002c1850750584c00465800009155100f041c00c4c1e20f114626203c949042c059140c000441c41421110b04001d0100381040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 452920197 1250 452918947 452918969
    0x51204141c0203120405070b121503061302010f030f11070507140622050a0e0601081608060f2704150b0307180212010b0d060602010204080a08030912160b01 69
    0x702116010f900c9000f13000841005070044000101440001c114543c01000c0d0104955034800d144180c02618500c1203660b19801504141480250705001030503a1066414400e501c40c00201a40115560202604640b04142e00ca6a50f60380980e1540f18003040400010b28584e41e0b0b1001e490614201985903000000008180308201c0054441400302c0b05402141c1c1002400001e507118656a02e03031085d0000b40d005200841d01090b04800606114082c5101b46c0315183c10756905040c000303180c1c45005000c0c1c0080ca83c1c1011070085d040c43e0480c204a008010080c0701010041000100381218020305240200b501c14140020b120000c84d42c81e5400802e910700b07004c40c00c0c1403c0400d40c0d81701940724803003441d83d60f0300904007242c400e681518010100412040300da0f5030348150183d650341042140050705460188000345071030051013110111124035014090b08011501c500190740c1004148004500910002078801c810100082c20b0129444a00240440700780c20461401001600303c10403203a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 452921447 1250 452920197 452920243
    0x3070e0c03041101090314030301091b020d12020702030f0706030b060f07030e040f05090d0216030b010504020315030f010204030606090c05070f02040e151911030408070305120414 79
    0x10280c8000c9a0740140c1004031944a007910348012540b008036544003810000010301c0111015402000441c100c84101409002841400010784c115070a510801009030b8014102004800c1c01070411640716120641e00505004050f00400e0a18030f4004d8002040d802103001031041d43d07018414189103040942c0c405082070a40c0b18420707194490a00041c05110301c522009001d6030781ca4020030b0a10340070f03d00501c03660810b00e048550342d0b003803192000d000d40100d0150024034200f604000040701d422000c25a2142d01e8003003440000e51001e000d44031420594130407446262000c01c8807140c0f005844000507565861800d1110445070341d90855444507007018001554a64044103803130019401910404600c80180b001034010500e1803080440d50080c034807088640c511420b002485201c0042d111411a50a1407040007242e1042703d4109114000b0300104001c81c401d0320162075841e00ca82400c0b880c04141500290400904507011540c0701c440034111590707214144207802d01c1a40f0090005520 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 452922697 1250 452921447 452921461
    0x702060a0e032a0909190303090516080f010501060e010906031a1002011d0a0506180f121b1f090c030605010b0a110c150309030d11040503070e 63
    0x40c030a00e0041820480c25005445507541d060100c1d000c001d07440c82400060500c01400c503140b41003400d54540c030454003900014825000462462000880c0e5520403010004a1f40c066000381a1008103880500ca005909407a501c0ca501c100c2000c1c0c04e01400030014282101f0441c0d0959405802100c03c012806240c0580c40c0d070040103160645100b4140880d000d90700310070440d4000d5140302d8081e4090180f10940341c110b034042d0b104030080340e25240300c00965600103c0e5180d444480c2d40005090750b1003100041c0b207200d031041c82c0706803910200003038605008103000d1080c42e16500300f104c0e4001c0c140c0050041e0390910003844000d480603480000e07068a1542d80303e510021204801d075100425110103481c810400c080740c030200a9540700341c04100c296110001d00c2d100e50030070304032080070420000000c2c61910340024941c04001000340085890b406d40d4680402641000d80a502d881c8400e0082d04003010f0940655840a80c070002d602c0d4440d45094200751414005070300101034a900c0805010710 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 452923947 1250 452922697 452922709
    0x2010b15070b16020307060c110c190b07170c1b09042102160e060103062301030b0105090d030c05120406020c0f0303041d0406150605030612011b0203070b0a020702 72
    0xf01090b0008035004849030380780c00b030f030031489244001810035107800b0360407620540010164005254040c00c07100100350401c00e0107180320701e90651094015a01c04101b05003030b41c6500420b2028400c080410752000148003070242c540000e18650095040509445650780e50612010307041d0700202d60404990901c0c1e02c802008150b89190224001c1007180d0810403640200034008841c03d040304124003031682c41803074001c000d4083d81d885002070300708000040c00d100207c028070390304c05040c8004d000ca50460300055005110180ca124140202407181c2c080541e00c2c01c14036030800d4004c0e26a90880812032510314182120100b40c01c031100d43c14007062001a600199000051200303039030100d08a005440001d195014030383c09501d44030154040e0001228000245c00d000d2840ba8400384080c21030b42e004410095807d000f488009201440000c0c0c051510403003103001c1409050000500802e08000d005089021204240141e48000340200c10041003d501d06d134461070315a8214280300c160740c0003840d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 452925197 1250 452923947 452923951
    0x1510140901030c0509030304140f01020a0519020103110705100b1c080d020d0e0f10110d05040c0b030c0a0e0a0308160515011418101e0b0a02010b15070b 67
    0x4100b6035101112010240541c1c201c81d00fa0b1300c0142181d440741d1340c4940c001011224102910b0143e0710140c1004e80d29400000c80c10b80950b4880050030070500c0d411a64001100d21100c10b84c10952100e8030780c640c1b1003085000306802e5000e90040e06c009418145083e040e01c1210440e640074840c5003145810f08050718110752130b1907a10100241d0340e00110861513019018601210304001c1c40c0403071900408100040030703050480f62006680090b10106415401c50f080b00910315060001000381c04070900e09075100d00d80c05882001810300c055224000c00c202e9420031203002d500d41d000000c00c462099002044140d69000848a004001d400c69503482554082e01500f062251500304420341048828130001800c03a110a424210641e501c0840c00f400c0348408510a0280329003030ae0f05040d5020040038148580f005001031200c6e00d10b0003640301551400459051161a020035000c60381816110080900304040e41c00890443c107243c08101100103984201000d4840810440000580021580e0303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 452926447 1250 452925197 452925199
    0x1b060306010c05100507020c190f150c0b0405160503280305071b050a0e36011401150206010806040308070c0b04060c080705040305070506090d02060315101409 70
    0x140c0c00c00842d10f440c0c0d1405036000c510620450401c8104144603500241048440700200e850003956140e5440351101402076004d9190000352004083c00b0150342a528114400c910b4546241d480f6500e848502c425241500d007220503070020a025011200b60389841030140004602510403034294000c020300240b110042c9090305411034100005140c043c03801c2d0741002c0c0c0c1084000c2c250b41490101c01c2d006880d60b01079075215501401c000320b40c3d80600904c03140f213508642c1e0350303001404440400c03548410003100c801101182d1400e03a04a0040e0a01800f28244080400c190455040c12409411246084070003401c40d4030440041100000000302d1030b0b0000c1d01820280c0c038648900700122081050140f010b00003148a070b040c0410010309a020a00341440c90740c80d6a030f03545886804907914807c911000c0e1042d0b11681c014402850800000c1c50b0f0b8130750042511104900c3d55021a102c0d8004943c01c000c80c54842080303c1660900c1c01e03201c1c0044210b440c200c40081540c0348080c0960041d14812 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 452927697 1250 452926447 452926457
    0x602011a0904060b0a0e0a061818141c030522030512040219060c02030114070f050c010e0a050a0605010b040b04090c030b130e010b15030f10050a090c021b06030601 72
    0x41603121768088174041e00c0340341c2c03040d01c181c98000404000f505280c0302d00f14001c0303800c22070701054200074416008544103011484940d51825100c041440401d016400903078011a0301281c0740c1c4402ca0051005141c080c0c9011406181c4416030010b48600003100742610340001210900096000c01101e003c000d400810660300e44441c00403c0d140c0e9031151216a9118503038034003103003450f0002404044213200300d000b03010118041d00c9004140800b46d4440010484038549019950302503005004001003100000504280980189140c942c150030309840070381241038008140111401083d01400c00e00100501d0141b80010119070b900c29480390307000e650760390b0f03000e40d503000d10036007008007155001088a6460381e50811a80c0003070014039642c500310341c82c040d050505401d01400b0500605200e16402d03042d030395480403149401c00b0051080b4140d49000f080480e050795030341e000e0790160450f1a000940341541982c00f038601800ca07486401c000344e13a0b15000c565075580e881201d510240030320380 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 452928947 1250 452927697 452927711
    0x612150916110622030e03030a2c0a05100509030601030f030909021602060901110111030a06140609040903020f07060207061106040c05040b03030702060c03130e0907030605040f050303100602011a090406 89
    0x101b1101c082220603c540e25000c0058110301d12540444c4502c0405900d01184a0f104907641c00042c41e2026001c24580081c41900200000d02e000441c3c0f070340740440c6003400d510700441400040d00f4030b50300b600308454806001461800b07244d8007403100c601a0210420440c40c1c800400c1e2022030511700c201009108200c00501d0750300d16442202180074440d5504000d200d181d1300c1810308a42c035081203401103802d52520700002044024180d6110300760386e014000c0d030704d09040310040c04017408544006a0941c400c02c0000030a10604001c59070003001e19502a02141e030902c20f00074540d41010b5482d6096a200310b090201249400039244100ca000b00c400282d001604c10100b4118010404040e50112011804034070b0400b0120060495100c161304203158641c4440c41280b0004003520951155400300205000051060340120340144c0504081c00c3c1801c89581c40034910b604c100e86e403011100100b082000300300c0c6c0901507100c07204000d404c7c1c41c010020800c0811000100240302904068594138 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 452930197 1250 452928947 452928953
    0xc080603030c15180609100f021309091113021336060f06020106050f0a0303120c030f02070f1a130b060d02100503100b03060612150916110622 63
    0x103113040e102e00340005031a0146000c83d002d5848807021448090114100007d104540d444c40c82159490038003640091041818005400000c20b28082c040b1440c100000d014a140d40c0c0b010840007540d0680c0030056a07554400c151004c0100c800d9008000c6403181a401c140b149080c05c02680101c440c081c40e40e41d07001104401d14025224035804088403100c1400302084031a819000401511016941407a04588100c24802c10300c4e494800900010548018800c8401d1180c000d403101c0c036010320f004152480d0300d002d0841242c3c0510802c80d03c03012403442ca00d04200c2e5007610400d440300480000001c503d0804455002c08000c00750003090703200c52400140c00355827000030031910a5005030200c0c02081071003901600581c001c1e00d03041081e6121543c0011003040740300071a4030614001c0d100604100407500040b1140380301a20305520702c01418012280750700d41a22440c450b407080503c6c900e5030155a0009425070016084c28441c4d43c0000d8200711580d151220401d0321824880d030040d5140d2680d003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 452931447 1250 452930197 452930221
    0x50a170c040e04200a180f0b040c090801140705031b0405090f180c03190302010e070906061d100503040201030b0d050606040c051801110f010509070608130201090306020f0f0403060c080603030c15 86
    0x8c52101d0748079181500960205a0098001082d25000b03c000c1205024102068440e1401107500000146c0704000080d891b40040c5c054913248540c11078454101a00c4100007104944101c96100c04103000008102452948007641805000508090100e000c0070402094075414141d030403001c600601c1c4010000c252003507100401414620080c0c850310360715024030001a00344c1c4d05c5520300181d26980c180c1c45940700280202c4051300d0007043d9100161080c5015038650f040207205034141540e5214140b00c42d154040d9207048244114054025031805d40104003c882d0074003100030800c80e042c420344881d0408032000000c058402d0a00340340c400e448400715850f12906c418181c00c29400c0c07a0622552034000a210004e44030f050325140019a100000031148003034003040071b030014030f00c0c4078100045101036006100e0f11002051040c038100091440c4501c59105510890340705a0382e4039400100c9070b0110b000b80d003214089025528104241184030742e29040829040075400a03080400c0c5842001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 452932697 1250 452931447 452931461
    0xa14310506010b130812070b1005030307030c03031b050d09060e2505090702030328110301050a06301b1806050a170c040e04200a180f 59
    0xc101215a00d68541c09440541d4000050702c1c80440d481200208800102064100b22510041d4889003004410345440302c0050300903101040b484110b0601241a4030300f44001d1115900036198050524400d00e00202100c04501c00804584003140c15000025805004c4451003441c002022568101e035080440040420110303400d060303c07406021030103404a0801100389070740794091480c2010382c1d6100740710303a600d000c9540c4030041e00100000398120000c955481b44407820395442503c1d045035808180b0854007a54880d503810500030004000c2c61900009880282c20240713007001c0c100b0000b68200030b483c0e0410051520758060041c210001615076800204001c0e1002d046861520440c2c001a20341480c0c00901c1200f4540d03004003060441c020011205030885950740c3e010050303000c510329052410301405030302c46507208000014400d51001d820b203009600034001c000600002e00c2080e10185001c0c14002c0c040c80c50031508114502852a601c5e40002d0494000305007850401254030041044e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 452933947 1250 452932697 452932703
    0xf0209330a090303183308040b06040203090f0d1205060a031703090114190e0f0607141603090f060c02060403021507060e0f011404020d020d020a090c080a1431 70
    0x784160704141c48141c2810061000300c1201c64050076011006c2212500c0d07080300c000e809202a500452010308080d402543d00c00302032402d84c0d640003d441045030924100446440011f2075125542c0d0340c0040500c81c07030b9040b038021030b01010814699924084401030410a01040310404400079032412020740208060381d0b001140c000c1c8502d04544400308010410742c1002d19145080030024144400192104460111000604840c1d558100c2103441e0306400e01c020186260501c454444412080030b84d22001d482501c60203001d900b4000b50302d5812515a05c5001000200c00a01d4090303110801100d0603039805071168404d40740c0030f221009080c414000700405281c5000256155144041808514910048000d00c419025200384000c131000503607010390300c0071511051000500d00000c0c103401ca144007901081005540d0700c0010103d4111403600f00c0440c0d081c5042040740702c3d852090210b8000c6007402d01c9110f0a01c9001c2e103802c200c0002d407075040d01e82d4101d05940240c203c504404082030b8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 452935197 1250 452933947 452933969
    0x10516080c1b0d09080a0b0402040f18060b090c040b0a080709080f060402010801050409020a0918150b100c051b12030f04050f0303090d060f0209330a09030318 70
    0xe50107010641d1403c03204102c00014010345000304102c000480c80305040c942004c02c15109494a4081100800e074241440715035a55500010754180300c0ba0071000e0246000d240005482c0300318174184012240000c0480b000c601040209000094400301038981c039100c41e19210080d80c0d0b030660180c3c0c0c4050260401000c5100307424041e002c2050004819120720b1003a03036101000e9980d0b400b4041030b03030700000d4002c1d07220a0452060208081d20b41c01110310003819500d01050518584030b000e5424103e241c800e0a05840703210780c01403810030a21700c0d14420181c0c0303003143c0398209940b5174035268851824482444400c1040b00c2c10182e440000c8040c2c0f08805400b038075907404180d40c1c40f030b020382e100b48a1300e4040c81071010302e110a840c0100544080802c060000200107205a80b044010881c048400201550030300c26164513840369150100f20791001a201200b40030001e01031280c02541410007411510200900c5a0b55907002c487d84080301e40c1070400b1030301004108000c441c40c038690b40020711380351 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 452936447 1250 452935197 452935237
    0x30403020705150a090e0c04060c0615120b0105010503040206031f05030d030b01031107031b03090306060e01030201031a031209150c060106180f171c030e0c0102010516080c 76
    0x30343c000001d04204907161188100596110000c0c1c030340c0d070011900b45071505401c0c40100700c40c2d4080d001c070032030180c0300d00c400040c1c43c1c003a03202c1c806407100c86420462000e5001244001004070306d800c12809080c090034014114a071035400100da07440300802000c15000c402211030343c1c05180c0c04807180039103801402e0701c1900341f020b20000c00030455101c51b6030019040c4407440424400c440115440c0541503a1780034400c90384200d4620381486601c00c200c040000703140d80080850201d100780c60140985074900381d0304d5451400010150b80b14070009502e0501502e100308400c0c0e500080000c040c800c0c80d05c2058444c03421000255a24083c0500700700030200005210a0319000400c14905031816625914880d141030a0031080000103030040c03c02403595020b0a10480c120004070401c2c11072010115403061100101c02c00070f40c149000d5020101c2c1d12406050714490007401081c070744d85005c0c802000b0b00e1421030a50000c0c0d5401c5030181040c884880007041490030301001300c40c40e500800ea54035202e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 452937697 1250 452936447 452936479
    0x102010b10120b0d08070303020c0304090204080a03080604020c07060e0d0b010e040b16020705040203130818010e03010209010206010b0a0504170a03023c030426161802030403020705 80
    0xc101401030441c0d110302d0203802c4142d41c036000585160480d0172083e03280c00c0c08029a8250025400301c3d040d40c032144003d020004100340c0e0380c00140081e00e00980030700107400c003924001d4140f10000e001103110f540184250480104c0005075017003200e00600d004d00903184403001040c40400113903006464003622200209003500b175000c082d800f40348201030b154607650b40e242001101444100000004bc0c00c41581002580b03403903009590000500d0540400485c81ca50326120503600c0840f002c000100c070144504110740e088441c4c000f03041c1094000750b01e803110303000000707440705030500914585000215044e144d03035224a003503401511440080981044003402c00903078500802c9001c400511502016038196040603868204e4481c94042008200800380d14004034020b00000c20340035031000348400a1107051030210740014040c001c1001650500c480c9404c5d00b0b000c001000901c41040d02c5008001348560b11120180fa558a0b240050b2680c86602d03040b801c0c4101c1d81e002941c8601e907100e88081d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 452938947 1250 452937697 452937707
    0x10e0105220e151e01020c09070e010f0e0d06050a0e16080d1b080706091b051f090621020d0b040b1504050d0305160804081216110102010b10 62
    0x81d6402a4010702c050b5845400280101039445401ca0300155002d10512625503503108000f10250140143d42e0160103120100b000d8510440c1d5001c0040d4041d40e01040e5940c2020b600c011101c490304d0079070141e01220001c80d540f40307031200c001854142c0c0d5000184c0c1000499010700c43c14902001501c0360030415254042401c90140241c0809005052001c5001d6008800e03403414654081d0103108510076036160001240c1001d03106980d03207070311208858002205000c00c80a204111025502144d05103003c0c880c1c1402d48a2004e001c1e0504206807c1d60a40c0140391403040300c900d4070b8240174032082403403080e680403030703054a102641d4004159820441d401c0e401880b4809400d0b101041048074440c2004001501003c1d5154580c0c0c1c108400c0c003040c280a603074440014080d041007807410407610144003003d40c82c0501514905c0e03002c00d041c401d400d020700141000041014085003050800c154202c41110702603002086030800c1510305000d40d000f90407142d42d21701c0040c05d0007a018070604c0c015103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 452940197 1250 452938947 452938949
    0x4020717130b070209190e01141f0e011e030609080d050a05240604050307080c04110a0806041d011a04321503070f0e0a09030c02010e010522 62
    0x1c010681c00c0801c56941c5881680ea8090300240030000715121040f415080554680d002c2428a40b5036404803881407003401071102403041c4d094207402d2403818681803111140c0b9000d08000a9410300420000d02c07000d8066039040d81d40c90b50045044400034040e02d90181d24650008100a04141c0a2004d114254000d440c414184010610680c0e0380c9070394a500b110400c07202004200d400d201100c0f21902d81d10740e240455400600f000d0f00d003075240d00001e0329198980c0c1c81410b85502c645800c3c00c0c0c600342402400106014845841d040c13001c1401c014040000044c8800d000d03030b41c0c1d10314404040720b241c10407449072803510000308030400400c103800301820090003900c0c0c0680d00340090150701410120103170a1a000a8105040010f54085020351149014185100d096910600200c49981c1885404003c003446800000420b1a0406426506400418001802e4608801c0c2070100303801c041c5505140741d0900c1d11018544a210050303c00d401158100d0392140308140d95280800e40c4d04403410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 452941447 1250 452940197 452940217
    0x70201020c072c0703020d090501091401091a09012307020c03030421020316060807020607020607080c130b0d02070201090b0901090302100915050405180f1504020717 73
    0x20700c54540b0352a01100044a20303d80c0b207003650801e051142d2043c189004250045224a03015142c00c81a0b01c40b1011381d40c3d10300e82074072140d40d205004230030040b07180d4842d80c0c03022030341c0300a00c801001600c46800340d420100d0003601141c1c0344c4001030050070b8294840d060015031400c000c2200c1000402440d20400c1c110348410244c4113074400e200c0d5070700c0e0020664040703450303d00483c040e5481c0481c207031218502454007240c1501c11614090f160760341800f240c40140c17031183e84101c581d10303101314024503018000d0601015074100c1002d220740036900040042d403000c21901c01c6a55003080c0c4104c00c4c4031a415600c8281146401f082c24000621641c004001d024002d0340c451082d01d80312441007804e481107000445c082903020b9400c00050030700801803181d98405040c440e031000c0c0d54079400e80100c814140183c001a038006018051880c10088000104001040340c03011440c00c51032629050401800c642c4040c2e1a22030312050640e1941c04642074150310580e14a8480f508403998800c0360001c030145 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 452942697 1250 452941447 452941453
    0xa05030406180f02280b0903010b0a120c1a0d050411090c1306030b060426060705091002060609040615050607120318110f040b041d07090b01020a0605060117070201020c 74
    0x76400d85c8650704441e900f0303080c0729000104281c40e046074111581d11007142583c041d501e41d0040700d03155580d48c0a0000501003622a445502c82d0380c80c2070305100e0702c01d800003100d2054443c90010140c8048044d40d0341e00f1000c600004541d11581080740c41e045007441300170390004c04441042400f10404001e421400d5030b01000413201e0383c44200a070159604814100c4c0c0020007400100003a50075140b5404003411840c500603400c540740d4018038105123003107070900040b0b03800190b40a40340c2031607159481100c00328400352072282020000a124600c010f000500b00544400018101d428a182d6000003081d0040c40705584007140e14040d0a20400c264908020900d002800010300000600306003d80c1c0c1d02c011071004840400007003001c00c452641c061038115940d881d0702641615181f00e031000080d81c0101e0718220351a9104c4031403420005030020441d00d810001e01e403c9a90b00051109200c551000002c10302e6031359200103c48a11f00e052280301c05140ea82d084c400410380660050000503000c1d015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 452943947 1250 452942697 452942719
    0x301090203071b12110a1e0201050f16120f230408030d1401090b01020a0807051501270b1305060d0b0c0a0f0519230f0a230a05030406180f02 62
    0x42c1c5c58640c0e410308005400c030324003000b1101040120b1038500d405503105050803824031300d202d83d001c00c458014414211281414602003024405006c064000142061030300d8100d6883c031510082c500c0c960f00000d282010010030110122440044c1624054030001c2d0449441c3c9400b030b0a86005052111042c0003122031500000c948411a030107000f540440c10f80041600104a641e10300301980171050640f01ca00840804001c0340001d1071441d40201000d4480d511a41820002c42d28520400c0c100301c0010351030000c440d4810340310b240c120b00020552840008003a030300c0300081101c29000d424014038600c3c0f040c0030003a0300c540c070318081c0c8400c002607640e0100c0c86200c0310f001c0d24a807281d2440000e11314400d04664490b84d100b600d0b0100310583c440285511100d008040880e181c00c00c642c0b0801d040c4006c140d40f0309d107540c0700305022680103044e4118500700c0560f89940b10144500d019040030407030004001003d012298000c02c4480d00307440e440160800c04d030300700840c00e0003520354128882c0303103a914 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 452945197 1250 452943947 452943977
    0x609120e130606020309191d0a140108100b04020c0102070b0f150f10020c1306091416030b0d1a0109050f100e060315180607020703080301090203071b12 67
    0x11401041e0f070050b40045180c803a81d03600b00080641403000302610844944404aa0320891240d8074031a00d44403404100141407002020090740c1d8003400c40e2003664242c00040281c800000740c00980b40c082c01d14001452400180460040d00c00c00c10b12464a60001851030100280305040b244506100341000400c0d0710b81a250005c20300b8100d030023341c010000149a2103615007031f08041c191a23403500446124001c16000704002170075018101080c5551a03c00304844400b6001301407180741c5580303c4144900d040e5050b008150000701c626001c0566800848655865030100001c50703a800003070b160b1a02e40703140500f170700049090103101105404d00010440f840400f03115140514580300d54600243e08000c071012520100405203641880303500140c06560881082960180d541c00307112441500d48120802d1401d44041d04400866004140070408500710300241c9041d11416807016a81351140300d412254010107030324421810903050018000c11941601c481501e80082c0c80310b004440000e9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 452946447 1250 452945197 452945201
    0x304120201090506031501050d0207020d0f03030501050d08030420130906140105010e0409062c0609031603081f0803130f050303400f08060c04120609120e13 69
    0x3e586c41b40d0240000590004540c000e01c0902034800d10010700500300a5240c00080103a2902d04080e0303000d4490804400034182e240c09594003400090360400f41025540d59981c0040c88000d10181404e02c8842514020400f411841c10341000d004040241441c000e106601c01450205021038040340381141c1d80308480c4480c4c0700141210300507140c0c8145e80e00a0b40a1001030f0044240031100c0e6270b81c0300e0400c082c5c0324000c0308151070078103000240140340090f841c00346c1c54030902030700345482a4001d21020701c2415505410b14282541441c0c00f49568854042014104c001c0401e0032056a082c5d00b000b05004500001526040c0b10300003404100301d950f0122502e0518950003503680540003000a580c109000d01c0d060700750000c455110409800301100001040070001c22000e009070564041001081c06080001d00900002405050241403002044507544968030905026080d60180a4180030305544004c181c00e400c40d015100c0204100c2000340320b80380b0030034114403608140d80135180300349840c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 452947697 1250 452946447 452946451
    0x1006031506050a051e03010b120603010e0303072a03050c012a03020901090306020c030405030d02030a0516110a091b091a030c0c1902130c0806060c030c030412020109050603 76
    0x80c0c94442c40c04001c03c034110350513407124100d11641c4069158911754030001000840c020481c420405484480010814662a5015010a1103a030500c05404020079012046a0300304400d401c01c004503036140054602e0240528091105100c28100e402d0140758100d401800c030564103400030049280d00d00303420440b8003c4c580d02c291480070000c0c01611814000e60040031b2000c0f05040401160707a981da5108c0507030740040084820380d04080307820000340c2410000701c00000c009002a60070282034090050050081e81c406024802004840c0028002d25100c2e02c52081c001a1100c0865522104981c0207403a01c2901c0300160009480e200540e50301c1282e0000030760350880381c610445115003d181100c0d81016000c1800036401b0881c003604010104900d011008120081d03513804e039080e004002d803036003502e41116034050910202c070110641c8940c03110b61000c022030b101c0e91034100b01002a03140d40036040b140b0328035200028021444070081004074809903c01d984007400742c9c0c0c8610901c5454007003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 452948947 1250 452947697 452947709
    0x10903021005092508070501210207030e12011a0102071a03250801030203010b180f0a0216050705101713110411220f0b030a060e10060315 61
    0x11048400044640c150070241d0000043c02c00c40d120704003850141c0c0300050410040100e0645070040c100010402071286d40b0040009007400c14040001461154130814035031119140943e0000d0f8045c01c05024504401041c9005884250780180c5026000e00901364117004060320400b04000d10204d6100042c008141ca550910707006000d13054008000c01038102800240c40b4081c0700405000f45000c40815000100140d540c070f40c450351540c0145030844031080c0c01c0301e0041c420291404102d00c0c1d000c494580000c40002059642d9032000c801d81d009004000d180d02001c1b009144102c20311200088040684200311842c9010020000c41a202d5581c1d035248404041e01090000e698070048040c0e840713031203000741c1c0c802d4810518a4001022030302030303186200c00d242000c1201c5500c40d15a4241e40d162108901600e244281003000e95030900304d25109840100c034002001401401150308070708002d25507002d00b02000c0c01d04401e00d0030f0980c26400340d180080d280100012038420040c04450032168 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 452950197 1250 452948947 452948953
    0x702041505102f06070f0509100809071710060503030702030d0f1e11060a1a10050d0c0509100203040e010e04020103020c060901020d1109060d0510080f010504120201090302 76
    0x10300c01064403000c244984400d044080f040c1411040140d00b0080d001541001c805000503140910000e0078140070417000004001e81030180b00c0c41c0b500c80c03035030100c075200c42420301c815503a039440181c3c3d151004039041650603144201c4400c0c038100c000901c243d19038040c00300c1804040e451710203040d600d0045040196041e0321184410908a018100c81c20b01200399207008440745c2069a0122105521842c1510010b80818080c0c00b003668180031042e001200c003d000d200c0b411f200e0000b001070348600440c0307511840c0700c002003042040c0944210f450300e00c04050b080c862508413000c00b42682c0c208040907401000390200400d007082c404002c072016178a50b04c0c48902c0c5070f42011400324100d50010000c81c1810790030007003122400c804001d12407048481800141c0e0340c10003828010309594112a07040503210082c0030a03a1551356041c1512000c03504c0c1d400001c0d241e030b03d1a6542a00100030f5004052030300a40842c2c42022030190001486a0300912001400e0303241c4002c100d0032146407110180042e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 452951447 1250 452950197 452950219
    0xf120702061e040e04030c0204050c070b01031b0f0305010b0108130b0106050d021b01051b071505070c02090903032202090711010b040e0c030709050106090b070f0c06050702041505 79
    0x10ba6060165014484200307040e074106501c0307aa403800350103000d4800b40c0102e80000b5205045140030301442d5405416400c2982c10301d41203035141c140c4078506010041a010790103543c04250141103131388200412031039000244c51030341e0741003880c0207001c0d40c040180003501c40030000d010800603141d80c44900740c1c04440038589a28194040b01c81c5e4210032400215a9002c120000d1011000010070061500d071800014407410309014000c4094001c2c1c40c240e86000080c807004002c0307203002c0c03540903010401d00d0303000c00d0030f558500c0115440e0303d900200035840f0480c0b9050000e8524000040c6104454240039800304203000c2d406482d20050510b030084d400b0701c4002c00190403503c96540c0e030020403400c400200d0300600a0002030140d91074410032001c186e2104410300504e10301004100010a0030074003c00a03035041c80340c0100001d20502501312071080000b1000c0400c8135101030404202c2d00032a60099140d11408010000c0d403019406a1056040401c9402c0340700c0e044d42c41004645004001403442 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 452952697 1250 452951447 452951467
    0x309070909082803060503190b090f0102070b090d051305012715020c091033111005160311190e010809070305031b0c030f0f12070206 59
    0x180c00095030803110b001c803d110f800f40b2040f00d03080c450340103074841c2c07040082105810001811108940e0001e4031a500c02524141066900d00301d007031b0980e8001a0302d14150703032032103030079460150000d07041d11840d03200086c61000e00c400b03110001d000f01c5840c41600c1e40d19500300022200c90082c1c0c911542c0c944010300c410001c7d036000b81070144141c030b1000c08140910741c00280629452030710b075000c048004600303500c10070f0b09507050005a40950045540001300c0c1811044244108894099010310541d42150001c0d48050390b1401100217042070303400b5001012018000785881991388200440d84921011092040c00a0007000c0c424a4074000030001702c03603800d204034082d110402e1000b00b01c0c0c104200001d64048185c0034603250007001d460b40d07000e4100c801700041c5500c50043c9144102e81002c00306100203030001c801c5680a0f00036048800e52088041000790515440e01800b50f81440b403000c411407600f42c0882c001700c0000138803050303e83e83c01810804075060b01c01d11900a601c0501000b0343c03110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 452953947 1250 452952697 452952701
    0xc06080601091809050d090f090204030b010b161b06110f10020d02040b030a05010608060a150c1103060f0f100602071a0c0d0809120f09100e0604171203090709 70
    0x10101c803c0c04081100185505c42030b003002601e54409002400c0e45e001440b0001d01c42d90480c00a000d840400c5180030700d1a191180410018000d0309140c1000080720041800703402c000420540c0c02c13500d261aa05920a841010209244030380c0010500700048a41000b00c08508001c11384038840243c03000c00b51141b4480002e500030304c03484985503828040030030340108500146200b84030011002405505111000d064604020700d102d11503a01c100092006003121050380c08018454107000300052400c0c1f43c44040b0109941440340c0502c1443c3c00c00c52298041c00307000340a00800c44060390a510b07000d81400380075045000300e4000d40d214020402c40380000111107a079000c50744c0035031824003244203800c501b00709007000c0100004a1440030701c8a0480e041c8022128020750000346882c044d2011002000341c0076240c0c01030b1050a050301c0b0940f6150090005074100c0200610443d41e03251500905c1e041d8000d80341040f81144140c14070807207020b48500c100c900030809000104052481d2140c0f01d80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 452955197 1250 452953947 452953979
    0x150606040f0303210b060d0b0f09090a0b060102070812090a030c23011b0b04020d080f1201050f031905070e0a060905130b1503010b060f070c0608060109 67
    0x1800040401002404444244028000c2d6200e540c40341445203501200c0303a44e0b0003800c81d044214034582142c5150503650301046500c91440c12601242920002c0001004030015101140d00621201c00b007281c05080400e820303c00b60312940c01c07480d4503121840120b0303550b030003402140034a0b0302901505c800910359102505a03150000c0c4a510f007103840341d0741e2820910340b45e03124200d178031046840e00c0740300f01d0304428003070b13a0100c02c0c0381c0700014090004050509443c8050301030000301a03140800c080d51103010781c0c0a00f00742c10103c059a109268120f00a6560181d5200c09080400a00205162801c400718292005005000707201070a80038950000c0004411412500e911815500181d404c0364500c40511070641076100240d1a840d0001040640380014041030b000413810900c6400142d2404140b80c0010000c3c00b078032758801e40c62011034014030341d50050030751000c004100b000b0301c2030340c402c01072290313922644284d0003950b501c00080d10b000d28240c402034085509030000b44001c46190400328 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 452956447 1250 452955197 452955199
    0x6010507060f1508060106050309031606020c0d09140303030c030f090724030e0f07150306090f0501080c01050307080408070227070801080307150f02220305010501090507021506 78
    0xb41e24000328100d20444403180c81140306181c66003400c004a001c14800640182200c2c24103500c0c52400b81c1c0c1060b01ca02c40c08005214944000c0c4421050000c2d5906480400103880220343c00d1070803564019107403608078071030300a4040c0c1c1c0c060041c15a0030007000750317070080594081c814119103482c910346840e013200610300403041c4141c000010703c100c0c00c058561800492180b400c03a05119104000b003c0d030319946510030540c0d000300c0c168040113200145c0e1004550341c9058030b154030f4103406021005048590311100c0c1c8641814000102645a81c1c02181206c40b500c007101e11071055040159803034003040f9101c1022544c0000000c001c030300e45900503c2102c0c401401e50b2280c03010f6031310803d0110000d502c018030005141042212032030b0003000c1a80500f910748000c41c14040140d6503107107141c2403100a40c11054513020828240c101e590181c50100c1040c5146540790101e940743c12030405101d210540d41d943c244000041c007c0403d00c1003c0c02541290f000d4200ca1502445030049080090251 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 452957697 1250 452956447 452956451
    0x1170c09010e040f1e0b061206060f061905030612060403020712060609020a080a0f0501080307060f06050901180c0504031104200d0911090106020d1d041a010f0306050303030601050706 81
    0x203c006181200c203440174802501d03601c0e45202850620010f6008028030050050710f4124100700c500343d0009007113600c050112180000c44543c64040307400c6024603075100103170750300d00c041c0000525040400b440c0308550503180c01c03128100212500c2d650790020f0781c001d80076070040e034070a004c42082606c803c46c019000e41c0000c500e03180d541000780100e0740301498410014042c0703c05d2100010700c034018218407400145050003103505054401e0b449128116000b03050300e0b55401d90032400745203234010034000c0400404c592181e607900d16107210b602d10769000765458103280007000c4090314000e4043d203081ea9080b401c5070428841c00d40c14080141550054900980b0003443c01d0749020b08007000414088034510301c042a40c84191410454001c0440012441460920700500415070300150340544194289850030000b0110340c800015451803901207a00103050410804e0300e41d12903101444000d20a03607503ca1864009101107088800c140203107a410f80081021038250340c0300d1005814070501401c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 452958947 1250 452957697 452957723
    0xd1112090118030f0f23030a031a0a0803070201020609060c090f0d150608070f1401030b0d050604030513050f0a050405070212032514041208040b030f01170c09010e04 73
    0x410140c81c24541c011540305210903d1202004070007429400c849002d8150070003071403c1c0d406c0f13690b100c0c001c5045a10030981d071108900c41c0c036405551000440c42d0090440c00850741c83e092002e0307c036072040300700341e01510441c1c020440464001503200e02c12000b00e40058140071a0b0010030030b50500354170f9440c4d408500c400902010407141c84540b1034811015030300107885407800ea081800e10f84a0780c448540c84107180703400c001010207050803d078039110902e00060300c54075102c00100d4040a400000c1d00b0b40c4564400c0104254000d8010401c0400c0001804007443d503820401c411450051111600011102000c00c003d052642099030010b41c030f40160ba0300d00301c9180000d4005d8000301d84a00c00d03501c8400340c0c2948c014188491018102051404400050710b00c912201d03244101c0c4610310482c007040080d082400402019200500724102411b81d490a1070b5000706120007007070243c190303031031101d0011212210300043ca41e500c1001c06040b09859a1a03d051004d0002d00100180c074a2030907800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 452960197 1250 452958947 452958953
    0x403050d020a0302100204051806030328030f051314011b03140c09010c1b03241406150c030f0a0914091012021306080d111209011803 59
    0x100d819401456070040c01003400509000b4603004005c0070302e01526104000620042d265060716006001c8101410681750b20b48201003891841a480080744003421644505041d41e2909244428020031781d409200e4041c0c411120021680103482c03614100742c4085803900090b007082070581e5100300e480c0c0001544803541000f141c0e044245500e00d00041d40daa1014100080c0b14240c05400481c0b8804640c24004141d0000e801c2003c04400a403060603030349402e113880110402107602035030740480e0b1f8002c2825507081c2e00c015000c045100a0800381040c01100b007403d070500c240c0e0301c101c0e0001c00004018503c104e452900d544207242c2980280400c000b2200b010b45900010f14510500303a8580d4003251401c60441c0f080004040c810703104aa2003024001c0440c050424803080d5403480f061100021807920006180d1a205103a10900fa800c0c0b280000b00d000000c42c448a100b1440d850720941c150303003d0070580d250149000c00c8650440c0511005405510410724207038200d00c801100440c05031a51 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 452961447 1250 452960197 452960203
    0x40c021608030c150c0301030f050a0204020403060218090c09040c1404030507170105010807050922121d13050c1b1b030d08010603021e0d0c02010506060703021b06040305 75
    0x18005406035400001c0410220204111004e0080a00895011582848081c0b24030522040c40b024080e041301110303c0050040c18031121140702d600031f00840d0b03101d540b441c108000e50480d1040c0b440880c1a001480c1782803c040a2440c412105001b2451400d002401000000d0400b80e0340101081401950449081d1216008001441c00f40780202017513403518030044008481d405401c02c0a07410480100308440e0006010400d0f54004c660301540b568038105c5806404ca40171154050041041403030308140411845a2a221201540c40d041480041c03202c82c2104440610180d03003001d001c0c113079820702e11000c0e480150003076841d980c00c030301c1c142c0d107440308003115003c0c500a00c0340d40d00701c9a6034803400d000c00b424410201b0310a8003e41036400000c1d2010349564030500c070745828140c0006079141c0724100103101500e08454280c629441d58944003804000303210034007100000d98a81000700703860340b0300305065503403880d41075005083c240f404040911032580782c100350640015040c4000b100041c028 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 452962697 1250 452961447 452961449
    0x3051305070e040b0105190b0711040c0e0906060412080705070816050910031214130603050f10050d140a080a0e13060f061b0204180b1b0702040c0216 66
    0x400e00501c45401d013420f04010148040e44032034414070000310910405082044a8070031900c04406440d00c40005e800d08806500403007001e1503000b441c080e107000c4010380061025018090566000f11280d942e4028032030b81d40300758029030305091004c20007680080c000c0001070004901c82c40985013149d80c1c0d00b407080d18014205020500000c0c0b940424005410241240c5500020f0011140074151860b16250600040004000104042c2d056103581c4150b2100031160801642003189200940d5480300400408099412a403034120b004041094144442c1c0c8210550740024103c040d0f814440c0c0d102c0655a201d140302c14254019803581c01c010404040152042850a854504250289108122080702d03013000c0d00175418645542440b030254140c19841c00d07a080390078007100e21030540c9502c400002c0c0200c0001e61142c08d060031f4007030071a21082c05032001c1c0d100340200f080640b1211004a01c10415416101c0c2c103010a104880162404e500304861006a500503144e41c106031010b01103000000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 452963947 1250 452962697 452962709
    0x708130815070e010c0317160315080304170c150c1507020304091d1e120c120a030209030a0321090c05090601090b0315010f17070305130507 62
    0x150041080c00c50500440c0e140141c0300850046510708a24081c0c081c1d0f88541d425410440803070f05000403d801003030040451092a1000d10b030fa4a4503a1a031800c5040e0030540c0400a42012603e4502c41c12400d89801550101d801460900b4207082158000c0f0307041c2c030742441c0c03940300380d8140500d191541145030184400711281107a80300001c4070030524040e0689011008102400201b0404035804400d8400b81c980c803042c00302d006001190080c000002c4404e6180c014002c0018008551100c0c41c0c841000081100c01d45c0c0d82980c15000d9141d881c010001c656840b904550031181019000b00300500600000c0c3c2001400c00e908500864035203045504210045050200d2022544081962001007940045014010340513169548941c068052081d64026584100420071583c02100c8a0024007854140c240c0c81e85030050141c0e40c00d013111000e05000c0703403407075507515009845501001101010410000c2c11500c881e0801c500400e4000d252402c2d0500e9070895030001401804a0802480 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 452965197 1250 452963947 452963977
    0xc0302010c0c0b040b181009050f010e031f0e0a122d03090b0c040b0d0b01110d03050106140c03031f050d050304030c0506090d03030203070504030c120c0e0114060c01020708 76
    0x200700401d1b44101c00030314a0461041041c0c403200808668800031400c00d452042c1e0380f502c192410a80140d81c00500d003900d0750340c14090b03000340c002035407600d124070641c0905214080c0000a800c05032542c0728a4203040191689100102c04a00c0741c0c0148140d0003000051010001d1a001c0000070340c24586a80e801d01000a8840b080001405544440d030f40d04401c9100740f2a14091a200b0700352100d01c40c00c5880000c3c5a203400008081d6030044540422450144040d90440c0d0720a00300280142000d01482020507003100740707006104c0000040d1f0b282d4005000045146489100390b0380c59801c218041e4070140041342c0e001140540700c41140200891107880210f44075811880c0800205119821a5019410910603d6990384c0c80802408500b505401c00590329102c11030121070740c1c80756400282410744803440000f2800006445031681500428503039a139503844001800701d489080c4981d140000341d400364814146401402403111034400d600051420030950b880e0344407500017940344c0707401d44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 452966447 1250 452965197 452965207
    0x30601140a0507140f070302010c0503072306010e0f01061b0503130905180d0503130b040c0303021005040c140d06050702070501110106030201170604090b24030a0c0302010c0c0b040b 80
    0x88a0300711100200d85030001d0188003420040446d076a4071180300113410441e041020b00144481842105c0c80190032210702c48050306a00030030800c00c420320b840d8000d18030509000140422080c0d42090107840250200c0c3d0480e443c00c8812a0016501c1509506100e03000342c960001078030401c0205410041c0024600b4054035000488044802c020166041c1c42d2000da2400d40c4071034085401d44080c1c0300c6050440d00d03611000c0c18022a0001120000c00079071444091105001340020b182c41200c0c8694200d5441c22080b00401003038800c01e075001020300049040520404031241094031810a020702401c90300802a10f84130144c940564025016030003030041030016507803240b0741005851210000f802200c0c80c5500080c1241243da82401a21424001042d81959207410a1801c3d176084944140e41d4100145e1800031480201d0100d03800d55299440c168840c1004256030055a0300800350070707803503403540d00151034654007004100c80b0400441e50226003541c90002800140111420190b00d070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 452967697 1250 452966447 452966453
    0x20901110a121725020304032a36140a23240d080a020d12360c12060606320c010f0203090d0801030201050f030601140a0507 55
    0x15001401034010810807010800114001d602c18404a0410309240248840407060080342180188e400041a0848004100c89442c458100441074002c0780003400c5445175030740c1490042c0404441c001d401100c8400c03100002100010408001e090280402144449100d004050450720840d03c0c032007410754940c541a4141081ca1401d41c10031a900000d051505100d0340e030007800b0404050103095100d481038910343c961644103142803050707400b6000c1d40e1a603200714400381d110071081c80c1041c0014101d8100c0c00004032240113010060307001c0c07420420125842d04076094140c2d0b44029403150324030107502500000d4030030056803000744005c1002034071070a130a14206050320030940c424000c0110000d040d00c8482903c8900c1841180c070700485401c0f40d00c01c1c402100d034074000d11222041c503503c1e1207107801c86c10520f50010b6106d5110201070318142d50246000b030750301103420b00001e400103030309100c03680071440304000540d04118141801840c1d020642180d45856220301d40e0754000030804502c0c5420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 452968947 1250 452967697 452967707
    0x3030c27170a08040311010c060501090e28020f0a0b0c0618010204050907050d060312020c130903020a0b0a0609021c0f0b13020714011505010906031a04020901110a12 73
    0xd407401000e894040d8071502c50300c0e030502442c00041d00403c1c106e484d00a00e41c0c010386541213425803002080c0095a59018080300810604a03000d5890048035000001c1c00e50000c0c10402c3c5d1002c0709810094040f1580a05c08400110f51006820400c0004003296250020f0090074007950b0382001031805240410755004011541c07080354020742e0040c0b1041c4425070b41d8a0060794802164603003a07403550301d2030600001a00300395202908038014022000d002550129060403c1c2405803a60321030b01d198900400e0072102ca040001d00160400700111001600c14440150403031282c1d180442c40b0b82d1a000301d4422a4000b400d90701e0002d081100303403030010446008080d00f83e28520010000c105090011400243da80441618130a90009100c420446995004c0c0d28400c174000080141250794242101461041d00903140070602038540001c4280c400c1c000c44a80c0c1170011181a4010001e400f800040e401c120442414000f4030510310840d06820010950302d42e004040300307412032180e4900540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 452970197 1250 452968947 452968979
    0x1e070603020c0c0121060f0501091e05060c1c020709050a02070c0b090105070c171c0f0c11100306031536020a030516060309050a03030c27 61
    0x41031600511400c02030a20115000840881c2801c008110021401c461a6046044101d03411181d00c0d003040810a901e803251100e00350b0301c0a032a0761002030307261030031a620070150050248001c0c0c8200e00030b00c000e040c44006404450310401c101c0c1c2201404040d944241040e03c041900180d10007030003041380f040240549508240b400d04114548620741d00c60b641580128040c0c00580400000c80c41c840d0303440303041203482640d003000a101d20b0685070707008202e01d806074071160801c91056400000041072080301c000c0c0300003260f03100d0f9007250b95864001d5501c0c0e82c400d0416120000d200c0c001c080c40303441d040b2000c00000090b50380000d00604500d0442200e1500e80380d0800005e24000c01c5040b4510f41080f07074040000c040045141c0b4685241000300c090401010003904403003045400404c000000070b0300420f0790343d1a413103010426241d0794110300700c55541d107004e40710340e12110070440404d0180d408a08a40528640528501ca44580060020080000c80e1049100c1c4000070840b051000761595 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 452971447 1250 452970197 452970209
    0x120105040b10030c1107030b041103010c23040e0108010e01060e0c04050d050102090d0f26091002011d1f020405010c1209181a030d021018051e07 64
    0x180c0400d000104401c85002c40c0594181a5207004111050340034603042c000c440300403012505c03129100c4c640101c8034441907804440303014100e800c1004502e0103014069620075141d48651851514a01d203249020140030728003880780f02003102081c81d1900c8101d41c0c0c040d1402c900042000c4c408218180d00711030907907010000304820346e010302c901c16512501b190203e800c00c480da450300310900d0070594020b201c1c4d1480030703a002910b000c10204020701704180980442c003403040b003252010407a0024221020000d100c0d00814400c0043d08040c0c58414400030b11000c85100004142003a4500d01649aa95001d07414003a80101c8002c00e09402e85040070340341345580d0b0f10940c00c19191070300181c240195164010011a4040300791450144110780d10001003c4610120b181400c0d142441001406026034a980c00002c0040c11981420005141505036074030741d00420300003c03414811002020440d1050400c05c08003a40800030072020400f101d60752140c240c2608981002c1d42c20b0501c2c01c2c03070a502c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 452972697 1250 452971447 452971451
    0x70806120615011803050703021f0c030c05010905011a0411090f010f02031e0409060b1623030f0d050106020f12030c0d15030c4b080312010504 63
    0x108a110004034550b500400304460800400e40d1800060b01c4442c28803804840e00190090000140100060000d0450740280c501041d03402c19a4510f46444101403103a00101f18269840070000b40b2803024210000d008000020f00c40825503249829036075405186800f4030120f8000d000a4a002d104040c6841100c0a8031840e0000c85404900501d240402550600950140840d2503500900448040215a900340b45550320902c0340c41c10b16802c43e004604545203042004a14a00308100304d90240e41403401e0038054120969907480c50000709003603017402d0a0502101c4040b030380c081003d458800090000a526040c0f140180030803200164841d00c00c40d40101d419502582021030000901444281307da503032030b95400c2e100c2034140b040c01c041c00480c0b03150415100310540b001150b0007e41f882848002051076445807200720500449004150401000d1786458080c0290550107601e000c4040411241000f85031a810b00e20406920118581e000000c2d040183c1114034030700c2d0702501c012102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 452973947 1250 452972697 452972719
    0x604030f031a10021203010b07050c04020304081c1d010516210c021e010902010809010c091e03021206010305010509060705040603020901180f050910080a02010819050a05070806 78
    0x809001030b02080050084401c001d010700110302c244500900e4086000f9005d81da56500c1d502d61034550300039042540c00f8051407110f101c103454107008490059410884441c10100380c4a0385801145403040400b0407940d68200941003210044413a910004c004c0000040a2a100b15a0ba50000c10040c43c2c1040198002c4101d640c43d00c0140f41c0301d454141c1c11030014079603495010a91900c0802c5009006010840705c03500311241054206d000c989200307030b03119201900c41c02c5002c0d09070342050600c000401c9484000780f15030a038000401441c650030740110300c100f0b9504d402041d012443c82210903c180c0000f4018400c2c46070034000c5541143c40030f00100110700c0d20180040540c0590700945042540000e0101040d070310542840400c841c000b1040701701a540d807540e041d5606128031800c0d00a08480f0005034405148800510072115520040d011086695004452138a001414800642d5482c8080242104a441024800c4140e02c0c000521400c0c00c01003d42741410041c141d074070031805020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 452975197 1250 452973947 452973971
    0x105070f1103070206040e18011a01120608060601030b0303090405010f1a070201140703030b090903030702150c0403030305450c0d02040b030c06030406020915120f070507050307050604030f03 84
    0x42180c04a40d45500402559140d12001c42e461141650039030000c1c2d0700300004072032420012b6920303600d030980903210494030480030030300c80041d10141e10408849410040008446501a40041c81c1d603500c01010b50349850190000207040b9030b021780104461611004041c0300e420390b00c030040c103640b01210500a042070525400240304054030840540d034084049030403030070540690007402c4940b20040c5011010b1030b000184503925001140e401d0014880c44401c2c0840c4c5803105001801101c1c1406954940360450324160040e08028080c0b0200300c13a0ba0300e030b050422603c45800d020702003d10051501e01c07a091580074001d489000c0000b4000d420072140303441559240301c1c0c030480b400d60645011440351100340000341410242e540c190741200c0004108001c20843d5401095640801c485c140488400c0003100d000030b0158460040201154401144100c001050f45541c071915174030342580340179415950b00d41503130400c0d0740c1151554485010f0104040e04070b000c0030590100341c5010401003517500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 452976447 1250 452975197 452975209
    0xf110601050418080c0105090c010c03091502030f030903071b0b0313110d03020c0405010b03070f12020418140708060a061d040507170603120d0209040e0105070f11030702 75
    0x2215042c803031035581c04107861803c0f00819042e0910342000046848400280c406070181800702c2d1500e00c40d0043c401c0441c00e40d8058003180c042c086e01942c0e10013000303090242644052100d10500c0007503100070320500040e0711004000f1813280803550003941e140e507050b14181810a14040c0da120850300d0300302081c03040b04400c8080e668007410030554800202028204038076a18034040b00706801c44000142d0310b09050300010036009444003030314104241e07a44d5404c0884180020340d20040041ca022802c55005c034824604442c400034030020040c84d05a4501c0b9042801c8a82c03040703140e02540710b54030110088031000807198421454200480140380840011790b505000340a100184000c49080700c411062081008841c1900a0000c000030b051010000e080c540c5007054150718141000e0000e00380d828041048026648a5200c0a041c03515901810000c0c2d0070040d201344d0000d82d5000d140765804400d0191a028002c00d40780c61001c0500558018014007040c44c0451541d07004001810050f2110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 452977697 1250 452976447 452976449
    0x203120c06010b040e041b0e07030603051b010516050c09040b1816290705070f060f09050f01050903070906050f030a02061e0409060602010c0e010827101103070f110601 74
    0x44591840040003800748040c2030740a400144842582c08c08009955406074480c10070340340118203d0714103c60108080c000b5031241c4107854000b5a040c4896103180b07544020b201d03402889002a10a070b10501000300b000342000301d40039182c03843c0d6201880050100124042181748a902c090329003041c40340d000c1c0050100501c1030245042850048240c100942c80782c42e040d0002c1e11a004da82c5174003604150396100464010b00310048001c0d81c000030f13902c0c010003a046e1b0140780d40d156042100e1501c820065404030502009041c0001004207403039594082c0a88400f901c07800c40d0000b0401c5c10030050008200d650f900450081d844840d051015a0b990010b4034004000c441603481c3d44003040b840495035000e103911a451103402c00c800854000e806401c0075030f0580303850303545140c4400807400440d0040303400e0703a00c01041e40d20701105660076103c2681c1c00f4010340c0c00d04116491203604401c0601211211840350300106030100600c0600c40d80f000c1c0c00000341100b4904036104203001500540c4420301 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 452978947 1250 452977697 452977703
    0xf38070e0117100e0a0606020f0d0e060708040806040f030206010503030a0519020a050a050601050f041e0b15042709081c090204020a0203030403030b15070b090a0203120c06010b040e04 81
    0x400000207820b85500c00e01000542004c0141c180d1a0030700010701801741001d402050054083e400302d130851600700280010070000e043d43c482c00e41d00f210384280302d000c0d48900d005881d803050400011400200402200340642d1240300c4040504840b820024200041a04402d21907042080341d001c5044e03001c0240c0b889000000d07086110700c1c0c41c3c220103924000c06000010140d019a03110413051040109140707041369015a40070110160040401c030890702c0e00d150441c48020510303603c1082018941c0b1501002c503014001c502d65051403003a198031a00150302030b8804000c1038804488450002c1c5200e180616000c0051240e4421540c860200f80544000840030205000820394440025001003000300d0b000b03041103680741110200203403243d001700e0381a000321341444180c0a0300c5c1030842024002200300d10300d59040c08116501d0020b42039001d0700c00c040e24460b416000300582d4013844848081c0340780d1030340e0b20303503542d040b080c1a820504140d014003000c160034002000020a42c0901d90b500581c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 452980197 1250 452978947 452978987
    0x906060c1005130f03050c0f0102070309090b0a09110d0b03010c08180a06090605010e16090b13080303010906081c0f0c0203010f050a0f180206070f38070e01 69
    0x941ca03e08a00315072014900608020310b091085070a15812000505c204843c01e4240c84c0301005071440306090344900d50005001600c1d020701001008a568000064108020b21410b411a41c0c3c0b01103000303444003220312740c6080a001071007041c04259881086002c0c04190000d00112b045c11202a1a00c0001008003100c5030b2036644038011024148039003044075a004038100410495800c04a0061a00740260035640310103401088124032102c6011400010b240e86000c52982041454617082e048861107070345e95040c41c980410309940c240055030207803982c1d403000124a443e120040c1d1510081201c080710441000c0742c920b040c1603110390b03912000e4005040054005440c0e2022a0040101c1701884c41d04078589010f10140d80140d4110642d2128004028845980214501560ad400c1002c009500c4079040003042d00158059050b0314080d805411150f44030344010402c0c0510024800304007503500d050b60307401d086001c1c60001c0550046046d18007801c444c4003410000c0c104444c0040c240c0ba40700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 452981447 1250 452980197 452980201
    0x91306120807031215060f17220503180a0501140409050601050903010507030b092d15061c060b031306050406021603050304060e06240a030206070b060906060c1005 72
    0x50140c4c1000e2201215900104101c1101c52241c04d0491140c0c01060005082424050040d9109008483d44030302d0041803003000c2c0e25011758400c442c0c2d000c420507140c20b02c00d441c407200105500384090009040d401901038500710400303041159182d115001581400117903c1000c0d907954629050f036094511100b030000d0340d6180d42c1c0044c0c0d40c4d8010707010791a50542c01c00041281326940341c2c0214a00c40030503590b064003500c0f44030880ca000d42c3d403400c0004600c10032495070f61078a15488a41508071281c01c490003003070440c1c0404504241d20070f5015003012501561280041505881410000e209608841d8214102845100318a903c200e8000d40342e55120300101d818000e42d035041728040d181420001d08041c510b40b80c09070283c0c100b00c90560784a4685240c82624440c0401c841e0b10401200c0c00c00000c040304150100c410004101c2c4494001c00e4400e408401a100c1d00b00030310a450244203c5915450820304200d40c01c4001041503001c1c01e0140031040c4403a40010f801044610b40101c003003210707 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 452982697 1250 452981447 452981453
    0x30d0e03190c060f0905010f0c0203090607020d0804050306010305030301080708030a0f03150509270f06041202031c09140a030f031a0306010902070308070305100302090403050c0d05091306120807 86
    0xc0c0084d907960040c1c1502e02001d4408201056205254044410b00d01b4480ba94528074160303140d0017a1003010307401010070802140140340001b041c0c128140302d120580d04050303c501c0400c0c40c1c00001d07082101d03164000001408031010800c199030007490540c00461510b41808402400f4840320301d06030b8145030b16000070781d0882260a48020107064060503d1505d480c1c00c4204880541d42e40c3c6940d510320b403080f040d808130180c0100302d001c00300805000500340380c0c649a4801003202902d201101c00c50100340003070144209841c0100c006046e03121380c00b0480c1b000e40e0801640c030546440e440e00d0700b82e00c040584000a500103241000c03020f03281c1400030700c40b141e202c410480203075124100d90303242c0a6000007042105003503024216890280d503d00304030350399100c0198111101510149641c2e00120000c0005251043c02564040c0c400e151460030202c040e520f181c0380605184400c00030540118021140c2c1c248000c020114140d005d006010f03451030980e08104d444040c1c80c0203010031800041075424 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 452983947 1250 452982697 452982701
    0xb0303090d060c0e06041d060607054903051003020d08030f06030a03080a0b0402040e090d0206071704080d021e030f01120b07181205030d0e03190c06 66
    0x348001c1d041c16801025841c05100605003405a08003080415103112082c0c100780d4240ea041d50804407072080500e54203283e81c80b500341c00134071321603001d001000000c00054007444103034004074444442050380704180ca0f14503041f207941c0c1aa045403800b40000c5c007200011219988072a030b01242400556500c4001101b02040d420350406034014495038040d00c1044014001184180c9075100312540c551503802c00c0545801000c400680000c0c220f00205944140c15030007480242d0004200518160783c500c61070302c003880115010a042c0d00a0003036003007141d4060200a03402005850b29840c1c98502900c189800c84001d40043c001c03100105207100c1402107581101c1100b4100b19091a2200e108000740529500c100ea61986410520000140c43c00b203100c92414016030080f03000082d079486400c00c0340d240c14000740d13010717560301602c3c00029080c007420389100b03019000e000a182e540724284040d900f92a0080c40045035a4810040544106400c80003c241c2d8005480c09181e804858108880 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 452985197 1250 452983947 452983957
    0x17070e01050c0a053a050f04092a02010b0a0b0d11160606050303090a090906090c120614153c09070e011e1106160813020d060b0303 58
    0x12903101e0070300480c05000001a01c6a42c4501321490119100a99180302890700c101c8017040e00141c9141c1d0108040c0b90081006d4500005106011403d180e5035404281c10f032a442810b100c841640c0c641540006425642c5010400a40e40028800040c0300d0012030036018151055502035200450555400074a0350020020181c81a4199840349601800030340401c001100c00c07913041f440c0001c0081d990601000341e400703415004101c1540d1038074121405c409440d000b40211191540c44042c6000540c1003540c6001500c0440c103003a1850406241c40c904a80300f08600e00c0d4141582070400c050088040da0703c58941109458201d5a0740005000c036180c20590743c105a0381005290044100503000b510ba64000f100071600a401500d9611054841c013000304100350006601c081200e441c121140e940514014003031030300c1d03903486012406441c185101642c0402c42d50f0f80800402d40303031960000c3d0036608041c1004460b83c14840c1ca6000407040e40c07446130001c00c02d6469280c006c02540d001c0c030540f5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 452986447 1250 452985197 452985217
    0x11011d04021605030d0b191401121409010b010e1903020d03110718060603150b0c03040e19060501080f040b0a0b0306090a03030c020a0510111c140717070e0105 70
    0x1c5c2d124000c14540303c024001102401e8003c0356080090f2540103121504031046510b02c03003030403581d803160000440d80c5c0c0d090120415000b40e04c0710303c0c05404003400050144108085400007401184c0c0728001040322000d065114448c0240c2c87d514206810450030306011241d04888980c46038400f4035099442040c0c20f01105030a0288560001e21981c1c0c861024001030003040041040a0b19070f1800d4088840c2919694000d03950b008060200382545402040c0150880b0304807803e01c0d40d143d00e605125001280c07488441d681c5108040302203074190141001a0a0900340451180760080e90710580003401000034080290410115524866a0b80084124507000d0151580d0307281200c0e034641d5914000380100d00180c50600516106480812424483d650000290841c48958140300d030107485c070702c02c0c811000241005041945505501d0b413102c40c015640300840c030a030040f52880d020b00001041101485107200380d030901e200e00c54226503403218645c242000d44210100049810340148041c0be = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 452987697 1250 452986447 452986453
    0x103140408120c12040f020a0f08071d01081b060904090819020d0507060f020910120501060311030c03070c1e1e020907120f090b0411011d04021605 65
    0x300041c0240680148103954080c80b58030030948584001c40098400e1440f41112080c0060200d000286140800c6280d00d000030080d0b400f55844994a118071001540882060360050300100a5182c205000c1c184a2013507085035445c540c94190080e4403442d11581410108222045400081da00d100c20b413001d114002d401000211034070700d8442c045038000c080c0500c1c14181495000c1904e88005102440103d20b5078403142030079265980c50005d030860401e13000d450ba80a0203064103640b01c044c2c1c0c84601001030b5403410785607003448021030100e58041c1c00c50000c241c1001140c0101c840c44a0849420004e81b0040c980c1d66aa404011038514034500d000030512010214000940309040e900010303140e00402e940c042240440321011200c2503410b10007900440003c0c001501680181d00c0b05c0c03460740203501c0c040f642d42c1c4d00004110454946207800c0301e040740b8400910080c42090109260032039020300300090240308001031022142c141c407800724490350b000100569002030742d01c01401099808022 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 452988947 1250 452987697 452987701
    0xe1f090503040914090c010905040b01030b031212010b0405030c0d03020c10050c0708061e04210c0c0504050403020a0b06010c0b1528030209070938070c1202010314 72
    0x8180c06002040f0a102040034013801050401c90080750803008034005840300e00d085d03440c0006200242040d40f08290505aa44500722060345083c040480290038400e2001d903113103031041030340b0600c41c5e0607008000d84080a01003440562000a208003001c8400c9450301c0318a0200d00d0104d01e01110340101c0340d007003641642c001c200650003070050320a460180c1c1c03d4070050f03912074000f540c0e40e0000b00d411142c0210700103003000c1035010030402c5079001401040a03802c1000c020200f170603903060309010360002074000f07a07400040c0b1031003000032009404200c0d001d02c205d0810f07441c0203540c0c04441e0b030050100d0781d103400480c503141c2c060944e1035802030b844050202c0c589040100f80d02d13900300881041e40181803001c0e5003440700c0c0100060002e1641d031003945420312421a020310a00810051000b801c0c854140404500300703411046055001002c0d40003131300820801162800d203407090260460f00003206000440000d030074810300100345c441d5251501c52452150004070701404020303418011003005402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 452990197 1250 452988947 452988959
    0x8030a030e120702032812080a050f0402060306130612050c03070503060c16080906030c22180f02090d290103211709011a03010e1f09050304 62
    0xa965070344401010750310004010044016a031043d800b009501d500401041ea01c40c643c40b51807075000070308226030b14040c80d80302d54a406034210980e103c0703030110b800081000308036541c9028060b0311803104103500c40642003030740c0071840600019005a2107212100e001d4a9610312651140c2d0040c179050002c0b00c443c10990520701d40b542c00708100503019010700700f0042194200041d2090040c04209a041e140c030b01e0185441c00c81c0103a01c84221a120020404c0d0242559500065405002c201801035600d48414044c001030580c00103c0311004002504104480581c0d1210340540b81002c2c8d5011420034407681c4e86074028800c2d07000c0c4683c8240c00c10740080c24451084903500c0021407060340214049410030310240b001c10248001024040d8070a4100d00d0415a502c1d42030b070f03104190625081d000c042d101803c040c41011aa1884160341d140d00620700c0d910081a94136002d2801d800800950180c032001a4480c7c40d506000310118100d481058842d081960040305c0003078108007501d07256901e41e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 452991447 1250 452990197 452990201
    0xb040305060114031207031403070e121506010c11130504030f08150d05030d0f1b0309080406030e0a0b0a020a08070201142806080304031a04030903080304020a08030a03 74
    0x1000540d028855000040748580c00e40880a03004040140108200d5140c0072601815a02070790b8100e042181c0060401200416080954000c0d001c035110b9502d8034503148180b119085080d40c90382c1c40ca9104048021b1003202d04440030340c00150a19000011802d81c1c1400c005250f40390000541085d904601c0150880207a4050b6006510076130300c0c024401000350044034860700c2612503005d00c3c00640c0c10075002e89402011180054403031001c0d00d0510194020040031503002d00810030400d6181c9044818900140f01c0c030750380b065843d0034100700c00509515140524000c1d402008241030759180344e1051080c0030001c1990b03456218100d44102d141007104a0060341010212902062080c408145401e0041c004c0f1080e06038071128000007940c1e80410341a4404a0600c801541c1c0c210b00307000c800741c00281c0620005040c490004694179487d5142101000102d08262507403031020005100020303a22070002011650000e00d0a034aa4645000242c14150700b03601c40c20407848001100c1d01c52a8140d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 452992697 1250 452991447 452991449
    0x303030c0706051e07051b1f0605030111030406050a2d051e072a0c0e0a1808030604111b06060603070e04050c0906120a0e03040609030807020112060b04 67
    0x5078000e100c240c58003ca220100c58a034244003038220381344400509050f205402614600301020310092051100202103410203011f5442112220b40d0307601212041c5040b03016140050100358020003c0081c5102c0402c0c0e81d0002410003081140c0740d40c0402c4984100350411822441d001176146000e44864802500213041244041d03102424980001c15410003a00c04180a03507112800069641e40d0f8541240c1c0c14011b00d103400007442d003009810680300d42e0307900da4400c400d101781c2e090030070507003407502c0b100e4078003030040408666134100400c60a0903440c0313010246003d0741c40100d2607280d854a03400038000d0100100041310240004c200078203544e044030309000281d1740c40402d40b441d07502c8072402d01c11a80300c1101c01d180419001500d0a00324105580700c82d60003410b070480ba13070425100c203000480c16446440c03604024180380b81442040c1d40d040c030804c02920b4242c4001d40c50f03d071400c14007400d80d911a01c00030301f0020700841d1040035a40070300c5100c07000f803100e400100407094550614824035041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 452993947 1250 452992697 452992703
    0x50111160e16030902090406020307090e0a060816080d050f09041a01030f110910021f0509070b07050c0904080d0501090501080d0801050a152a030e010804111903020303030c07 77
    0x2c0803654034070050280c415540344c580c0152100741503170f880d03868034801395001409540030402803100c005015a80b440c40503000b840600004502c031442c211006240c80d45020044250070480301c4104503003140080c2e45010400d0505045885004070800400c4034014401c50382c0d040360400580090001e0b10000c5550f91480988042001a02a42882c001c459203508181070b082c1e410003036002d01d450b041200c0c074260025481200e0b050b0040703460740a5281c80c00101000074039119424031802d51070601c00300c2c014111150072942400c101c0d481d000c0e0f4a203203005100e406048010082400e112000c801c0310100c084030681030000303503503c5030103000400342480b070303e606030080d5801c0c3c18416104012803812514001d06c103064060400c104c00c0d10400d20071280d401400001c580400d240608480da901d0301450503140c846183c44c043c20054415906942818100000c29080000259030f0040d00e0340001425a504011111281d2800b0104080b42c0c00c065450310002c0204407401544070020014588 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 452995197 1250 452993947 452993971
    0x60a1e090804211a0c0d020d020904051e04060b010e0301090f0203120414100507051e070b03010312030510080f011e020309120c0c0a1508010807050604050111160e 72
    0x74540105190552050001005400303c1506502e130001d4004040303030072904494070f80c1e00c1c00f501c0c00c01da0b004980c452590643c1e180e40114003950686098846c40350301c10400550840075140c0341250380400c440041c0b000300200d54910b14066182d02c076208544a00b80d014000f0010141107040c4140c240f540300800b24032a01c40e440488a07060340c0d071010b03203088401805403000c1c2400c0d080c0401c0001252101c550041100c01d00a44000c59810050003c205c105103404182c0d0522400500c2e0a0030002d402540a001c404c0004000050845040c000981c0c41481e00080b10385402e640c1703949800c4241d202c020b4901c950b5a000d152650190302080b600b80f01c20a0805001c141c00304240140d000440b03203400c06400021142e021401c0d080c0082c4404140803003628101c4000000003400702800d038102141e400c0c084001180c909400881040c09400f8810040418900d0100082c00b10b10560180030f0401900d8442007410403420042602400c0c1e1100f40120040c1c1c68203140c41d241c0ba02220307080070b000c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 452996447 1250 452995197 452995229
    0x10f0f02160b0c0127020405040f0f08180405040f260f0d06080136050d0302030f06030601030209011509030b16090902120c071a04052409060a1e090804 67
    0x1700c83d504907020066040200300d01002d40d0200401080010304c04d840900040740580d0020b000c0b039402c402424800c80c1600d843d0345082c1c0014070b80b01d00d10080e0501a516200902000c0340d070840030340c40455400080c0c0c0c0d4000c404459181052020b0055a206c8074001043c0700380305000442c042d002c98142500100416552181510b00743d480c503440b1250740c00280c56804c00c031a12145800c950804481c0c0300040500c450b0343e20689000310909100700060350110512102140d02407006401400445c003c148a50454001440e821010301c030f09800170361040d112000d038078059424000110303000500701080b0b00c4c040b040840c450070021482800190410b0020541600314800d4500d0320101e003240d8022552841c101003020b034042101519940c14031745c045004800f00c039450b144640d100d00003400f200074014603440045215001c01d041e40325502c000308091401e000805903070181090102013410010102c403803124020228050808034180940c50040c444080010000c0354500c011030f4510fa = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 452997697 1250 452996447 452996471
    0x2306070f1418010c120203040303080703050411062101120209060603070e1302090402071b0f03052d0607020a0201080a0b030a11040204080304060306080d0c02010f0f02160b0c01 78
    0x6900e510241003514000340429181d01c210802c84445001060418418a0301c2036141e000c12031072100307082030040e88009028020164045a01500042d10741014001f900702aa181c200001d08003500a00644001c980c003001c0d41108520032004500024035403016507110000e0075464000c400c0c2c00c1e8041d0840c0400300700903041c0201240c1c03080b03806a940076000c0303814200700000c006005a165180daa000c0c0815a102d039074910040455600c540d80c0b00c901c0500321981401c0e9041b0644c40b0880325124050100701050000c24040794500c3c4500100310a2802000c90a8041010700c2008001d48103403c10804080d40024400d81010b000345c841c16815902d455920b81522650100b00b5010781180901c400015100781d4034a481040041c40541044e489884c07462940d08141e05c82000aa211101004021400e11210404214528024080d5030039034002920b180d031059001000c105000b48031920b100e1090241c8048c2104482d61000c06503680c64039000250040240b042c21540381107440c05c02c0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 452998947 1250 452997697 452997707
    0x807032405090f0f01030b150a0e07030605010f02150c040f06020f010e070f06111213030c08011103070c05030d060b0c150103031b051905031c0204060503040204092306070f 76
    0x3088103941d44c2060785a0940d940e110303040c00c0203842654060b403640403070103803aa14240100043c00c03880c1d03418003061410020040c1560215813105062103e250250b00645a01082e50500c0f0880e01c500314080d51a10281440280706d283d00010380320141c0e6201042c415404683c0b05034046095000b0b1250403c9060304036118903a80c880d031400003100c20020400a07000302022014a0340000545070700c002032008502d0240c1c80844003420401929600380100000600094007805040e0000c0110401a4400116a10002c1c05240a020710050108100300080044074a01c209506051103e150390307001100c50341d044204685d030795008450903100d050894540c1d0303074101c03600745d81c03140c000c90414011060140140841a5514041c170100d070580500f81049454100384207100440d500c8079007800b03000381da9503400d00c0145098010401001055481420749402a404660006150215190070b1000e016148020341c80408454520504186c0c00700d4140e102d03000a032107d0822695480781200c0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 453000197 1250 452998947 452998951
    0x705160e070f030f060f0f0801060e0c03040f050a05100e0c0102120901050904060b0a021e062d0f04051002070803130501062d09050c0a0807032405090f 67
    0x14140c9000510391910601c1441c070001101d080c001507401e503c0d00070505982140e0481b0180e81c03131100040260b05c00c500590b80c01094038100802c1000e00b003010300090480045d010080402011010609021961000c5010740f50f00a00316404441c0ca49410b68540d143c0005651540b49460300105040f44045190001140140d0181802c036412440c10000c0d03401c100001410070802340818000e5840e05d1045101070a008021a510784008280081c0340c2a100c01502d6084030080e42da482d03501500203805174001200b0030f154042101c15015a2850746d030500d036600e290708060028086210289910b00c2d002e01c0c001c01c151002c00e442e42c2c3c0e400082e4401c0203801008505c04100144482220110b2001480c0c41b07540003084c669996000600d40044006a210b082003041010b0002819004510300c01008445400d002c607140c0b108a003442d90080c031000030103200d840000140e0f024400e9111240303181d4032000700c405503841182002c6809400b8007406018805445c081041542100c0c138040c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 453001447 1250 453000197 453000209
    0x91a04150e0a1b0e031908041802030105090c0c0a0b0702031c090203070e07020c010e040b040204380f03180303010f09061a040b0a02070b030f0405010b010918020a0e0d08070516 78
    0xb041d1404001c01c107618081c10309a059840303001c240408030740005002270300c080541e085000580c89506103800c1051410b40a0800d41440c1002c07c1507ea448501183c1c4444098010b1401085540c0b400c4040e030442c815040080f1440f100e00e0130703020751540c091340410701030ad000350103d9080a80b240c44520300c1d40002d80e0b00c100540e000c010a111b156119900341c040c40321000d000820284080004541a0303001608400a5502080c0d0301d180d24092a407841150b0010452200c40d4030020243c450f0001e101d0a208000d01103400000580380208401441c1c03e01aa420103c81e940d40c0d4460541c903000186019103141603041800008803668a101440003906031541058074013460032140045580c010450601036001d46100061a0440c49010350b21448c03030380c1c6200300149030a1a0550866904400c0d841c144521080e051124a1860308040e034090b90b003000040e940c807150f0800340c4c2c081006000859001c0010b045680802c082840a80b0300d4912840072540007424550b042c03403140e02d440c0140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 453002697 1250 453001447 453001453
    0x105041a0916090c030e0a050a17120402040203040326100603050610030b0a09050124020a0317130203060109090c05030601030317070c02060c0610091a04150e0a1b0e03 74
    0x83c400f5a51130341c8080c1c8009181e0030001041600e07003100504044c2d14410542d555044100d03030710103210750494580f0140034030501007880c044941c0260003900d0005803020f801540d000c8002020107000340420007071010122000240900c03146960300c0e816404480d00c0c0304516014000207001402806501e0050300003c3c424008000c015404030b000707100510b51207a100366040c0000038007030a9032162038040c0040c1040b0440b105003034540f20001030341c6101e2010031580308030021000700358407811581d546000300300f050700c040e1034044655042c8441d042c00a0740c140910000012100000c0e03108000c500d204000e08400e1644d18010540c440c0001d01c0f0240100b00401c50f40088040f01071480c960000c0242026200300c50190003003039241e046150700c0f200716400301040c400d085400c54010401008181d005100143d00400128000140e8140c014019915000c1d205c83c1c4082d00b407111030251000074900c0380c0d145000100748001d0700307459140018600030b05a05698503482036011444615010b0f0007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 453003947 1250 453002697 453002699
    0x509030c0607030315060201020a0314070e01180f06050705010c0e090c0f0f0c0102070b061e1e030f0d0806030c280302061603080f1003021003020702030105041a0916 73
    0x7489040d5000c501c0c110308041d900c084130000210301c502050f01804003680016264180d400303014045600c0140c000030b40000d80e80800040035400040c501d2418020300c1d0206010500459070911403509400070315228404072008103005911002234a0303114003500c0288086000b500d010340300b50700101040d03604600c403940015115100e91000b0000030051040440c40d01e00c0d05451407031a50850b40302d10308141d400040c040c0c04d00440c0c0e001030741c0204044030810300c00c06201c01c4400c4540e0804200c58004d0721074405000d040b109420300b540240030003800740e840d0034000c03020a50b00e600340e10642c41c1c0071818402c045299400c000800340341c6590081c04c404e8005e045140480d0b8151031200082140101c2c09a011006848010180c102040700d1074003852021041c3c6805001190004e01090108180700204201c030130780c200c10b0004994040d0356444c001d0400090480c0a841381960180d0190709040a010030440c00480c101600c401e000d4038110b160b190243d9498803040148034a026140b0060b80c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 453005197 1250 453003947 453003949
    0x50702060708071e050c0114063703030c0b0c0f09040f1508010c110f0307030c0507031b0302130203060f1c170307020d0903080301150c0f0b0a0b010509030c 69
    0x1080e4110803503003402048030a864546245201200c4c0c03103000002d40c041010fa4449100340205440162120480c070b41a241c400c01207121800c0001d2406000310007441040140a400131000050b01900158140b0386030b01e9040240007030031102001c0b11b0700d84004000821003004442501e403440c10320b000b80d03403030b00720044204400380074110800c441c8142e0352240480e42c111b43c003142000400303c0c080040380c00041c01802920100e149148840290001400303059004808422914096414101070441c03107a5810700c6454003c02d030700020600c0c01048020400744005080b1002240d108482540c1c207821000c094400717074001070301c00d07541041c07022400e02c40c6842d01c5038420000c0840c0e03012070982c04400351100c20080e8030204501d5840e060000610002a03411b00c16481004018142100e840d481c5540308080c51005106150601d15880c91a0350340038031403004000c81507013001c0720b00080040740c00c001c240b114041d6010502d440c070303003035007016154040e4043c3c0e0200100100074000c1500024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 453006447 1250 453005197 453005207
    0x403030c02040e0102070f020910120b04050319090509011a090f040e030703081b0a120f180312050106260414060f07233106020a02130507020607 64
    0x203001c0368041d88440b200703e1002000d00c0a08503950244d10010900034040c0140400c030240545906090460340783c00341710302a98800005401c5030f0000c0d01c0102030391541003903030a601807510360303c000e400c03407459a101e0a9032040024040c0c94013100c1507407290340d0328001440b02c00282d480200380800148014030329441c219041580e450000340c00400c54102c0b6040c1e40d801c55008a6007280070410400c2404060000e0310060800000098400e614181058002405c2e090300019160201e94460754280585038a90b00105030b000705c0342c5581c40e0f0700d1016240140034560003400a0382e80901c4c1034000149144110308194054980c41609490044222410102020000e2080e503818104e100d601c6807511003085118800c59080c9107400d014240f4900040154a07000400c5c0110b904103000c030548101d089003200c00000d03001c1001040c9200d41c0c41042c0e022039218a03110080e2482181c0010696004101703038510620840d80c403d010032250103140102e40c01600d00100590000000a80440c001c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 453007697 1250 453006447 453006467
    0x60e0d1401060305010237270806130302100b010f1d0a0308030105010807030203061f0c0c09060504060f1802090d0c080a060f090b1f170c100203030c040303 69
    0xc0800441d5090f01d80e144c6070b0036030f441021006421041d44900c003411440458201c0011074078900c04d03030300c0b10b070b8803c1c030040200e00034101c10802024034010041d99000421404030040c18040c0a0b01c40a24141500c61004140381c4815405402000a5a01c10610520810000c0a4142c4540d607000700c00030422101020448141c0c0f2401441e005074920b240d580b40c1004c8025403169040725520340c1407500040c00301030702034028030a0600500602c54030f551000326606000190308010303964090008000c032414452100041d08120200d43c000c101c022a981240e01a68025201401002c1c1d8400006544502902c507081d612022240420743c10502074000308009807009000c40405602515040e00b58401944043c5590340550090b000b0009140110440558010010001103d258503480020b03000144083c1c0c44040340c00090040207081c0d40b884000c0c00030110802d2051000c0c40b01703550381e00010001d95208090030420381f040244004222807007104101000d50170a4034569055410040c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 453008947 1250 453007697 453007733
    0x30a0b1f0f051c0b010f0903031403270a05011107020117060a0f060c061104080606040c02100e0f070e010b0d0903021011180a05030a0b0406020c071e060e0d 69
    0x801ca16004850700f42c82d100300d520f88a07400001c0b4405140c00142034460410074580910425410401c04a40c1210040380707101201440980d89030b44442010f0833404a00d542c1000251302c0100c00c1740c3c008400a40000024802c400030482104032031a10212406a003600070300049000d44000d20f000c0c459030419800181c01782001c1d01c51600c86441a06c0342503141c20140004070b41072414014480d172030240c0c0700000b44240c0180d00e40b0782417440003a01c44000a00f403d00468403034861148051081110300c0d60300700718172401c121015400301d416460750140132200c01c02c0d00c10b824000c00d420401c81d2136541210f00210311035250180b405440d9000d044500015820b500584508120013845c80c0294044620312441143e0b40300b02400405202460101c03106024150200341442680c41c002803c2102d640c200d07908200a984034030f00711000e40318204643c0701502450b00009000080c00b0a00d8280180b42d0320084545500c5040c11140350310708951485d031240c40303011110080743c60080d030348415800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 453010197 1250 453008947 453008957
    0x30203061e0a030f120207060e0604030f020f0910062007060f0519030c030c0201090203061302220203013f0206190509030c030f0d050c21030a0b1f0f 66
    0x3d0350380c481501d050080a01981c555911200c44414503906110003400340809003071181c04041e01001003030030380c015804020314240c501e00118055554269aa910500004122803810725080910003a8441c16101d0301d40410f0040e0a204040500c0c0b900c0b0100c6901d9880c010709071145041c1c000c13142506640c0000d414050300300301c20319060180161580b00c4d44900c2e2000306940a851400500319841c0591010840e4505088000160b0b4003181a0740c00c890302c440f0b190004419800012489480e50b43c88952455080201007482c1c145600507604844102a02500e62070b0320075490a00145805030b986601103102c0f440c103004141d07514907101d10a001528403414001c1e50a800301c500311074000b02c000414004038000d122881c042203000d40d256001c3e005005540c0d080e03202c0d03e554240c11840700e030034450b011a88a00044080000c4040042c1c2c54040c42d82401d20202981c0307142d44140d4591081604100d4850031904000d1000c005250072681d11450103107041400700c580c106440034100804c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 453011447 1250 453010197 453010199
    0x41a04030512070e090108030309070b0a14071a0c07050a020625050109120f0e0d080702220b0a03020105161b1404050919080c03070605130b07030203061e0a 69
    0x8400c2c0d45030500c107081d10344130703010b802503c103081003039070401603002e41642c0c5d004208006240700041144000c0703a80b40e8031610b44075121090144c078201041c075480c02640101103403040a00c521001c42d9940d10380012022003d0b5121045000882d1103a44005410382c2d0040c003505006080400080c115130b0101d11260490f1450703840e0781038206416243c150f440369101d600400c00d11042103401c4c1d0703d01140c0e0401d14011460020068181004a00881e215203258505442480007000448800c01d40c000c00118007802130303510305102c0c0c088040c8458444c51504071414454245100c071041600e80503104c041c00c100001007d040d0004514100f00da20803034039441c002400c0325440720603001c0d007200310b414090403045406000171500000e100400c2030703002c401d80d00b01701d02c00e84289090040e0008240340c2d60722000409140f852184034801001d007840e00c020803650080360411016024070501743d0507040c4d00c4411f070032001da01080d10b04580c04a4220b034000461310941c0542c40308444080d190000b00303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 453012697 1250 453011447 453011467
    0x1e16080601020c0405160806031f1a03030703050c16300209150301050a020a0e150f030c0403060e0f1b0301090501060b1c0e0706140909190b040203041a040305 70
    0x564070a0f01c2c1c00e60400e03d010034611b080358101d40f00b26800fa8007680108180c0c0300c000305580c400c1048a031890000c0c0d540b041a0b1003402c0040364071480a0350b01404403036442c2c1c1c00346001001a030207000c00700f680380201000c0c8a110020101c540c0111600a5074441640c941ca0b8240e80c0e482855404002403000d840d8024001038640c6118648a88541042404e03507001c01800d05081d28801812101c200d0300c100000035000341c2011a100249005442c0100305072000c100034280c3d4403401141d581d00f01408002c020f40c07100080000d1061724071450042c0025803801d2181d40d6907100700250382c02560403d9881d00070f00c01103c0b10340d125000009001059642854981c03e007129110b03040500361400020312406410b040354449851200820820072560807009241511000319010340800c01403004041151036010b8070660b0a5540000c2500368030381000d03003e400412200f80b851208080c18561600707a5881d00d0301c04e5070f1140e81c04c0908130140c40d00c0c004101c5000311000b40204d0030310038144480070782 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 453013947 1250 453012697 453012701
    0xb03010315180510150e0402090a0504050a0510090309091514010909020310061e0503040f0303020702180709150806060c070308030109050103060605060901020a020f0f03030703081e16080601020c04 87
    0xd001c1c1c03100017840c00c0710010031525007080e500b01601c654000f10902c030060311000305680d403100050308005900e0302c8504d0414180404030101400900c03c031500800c101e03000340d1041070050f20985800051650386d100368010340c0c0741b00c1c50b0310003c01948c410411082c0c05692190b8003981052406204842c2c0b03503005070b0105e03002a14010101c43c401d010900c499a00103ca174642c3c0c94594460302d10348400d42d40b000b0064400140f0061243c2c000a007803808142c0030fa01911600c550041c0703c04a080200710003a564180101c07a081300040910b5000605910515400c030030044680c0c1e81c9031203da079504148212503020000b0304500f442046000030210700300740c01441c0038181422011901e5455810404151b60f450f400051082004004480141c0c2c1c0000f000c8440c00d078142c4145c2d1110481c1c00000b480083c15542103138040c04009481c0d401c06a0181d41d0311f00c01e02c0c0c504a0410010004008031070315140403110354008000c0e001d50b515015005420850384400c0500c11150680420008542 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 453015197 1250 453013947 453013963
    0x3040503030f15280b0c0f0c19030303090804090e03090102010c050a020d05030907030606120501111305040b2407051c05040b0c160f05030c01080f270118020108010b030103151805 79
    0x6d904203a003a1060f102040c41031782d0554908032081200c1d45450b084004000f0000d100003018165920000000c100d240d80c00d0350002d107c0140200003001001d0503440e2a40d1100c0709250055103001c50050b032141c0140161070304004680e008040500000c170f8241e48036070003d0000c81191240364400000900a130040d440642821010302042500f90324086003554110307641202d11042c14000d11f88802c0030360002908550040304c1c0441c2d5980e924000c280600d400b030500c02042d2076003559080d03000f192000280342d220f1003941140c155007149510490140710702040c5400080781004100060b0f091000901810185902510b000340038000081d000301075554000000020305650801540c1307000c0c8642d101014007030038a10507e04d4520151901d14000406040540c3c0c003001040c28114080c1d1809101c9940a00080011403001c40c002c0b070005000300c1c0124000f490070000030441c4202541664100d0b03500100402e00d04005960010183c080300b11200040403181c1030304004540d007086204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 453016447 1250 453015197 453015217
    0xb0705120403030c1a0108120304061820060f0702090408040801090f230a0212070f0f050907020d080604050a0b0d1506140d2603040503030f15280b 65
    0xc01e500350945466441e11404803008400d251020004007d01c0311b0200302d03228505a07210480795a5a690300c5c0c0200105a106812402041c0304910801040304003e003c842020380041c50103200156030713003005034a00c600c21030442465028015003005040c141c2d649904075101d4140d00d03003015100c406071803c60b20440c130f0658a0341a10046d40c0b003440171480c4403480a103203400344e100e504058407511a50b605500c290090051080c1d10300c54020550600c03150700a0050003180380c0b1119950035400340c1c46801030188a120714035000200d190309000050440441d40d8a4075400b1a540e240020070000b0100281302c040c0050300c0b2814080141c1d2500000b04503207120b103c081c2035001c000d41c81d040844100b600102004050f141d09843d2a503502028030300e0265104407010000d82c0c00c1010508200c0c202402d408a501022051008001010004d14440c040342180e1110b0b0340e5841084910360660f010800b40c2040e800307041209010090488401e450085021180c0115541d403a5511964883e201d04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 453017697 1250 453016447 453016457
    0x304080a030c080f07120608010e0105040c05040e2a0913030905090c16050c09070909051f0902030a110c010f0b030a05061f030503160506130c0b070512040303 70
    0x1640150380501c980d2042c2626031401d0740c074601d40103100c114508009405042807041e9184403008400c41d0360801d5001e09035103030081c03010300080c01c0c40b603028040c01c0c3c8040b0781010440703501050a04040c81162100303103050b4000c02c906607c52443ca10b1030402c50820401580079101d000c1550348450310100c1c01000f049108140d000740a0500400444c01508070600c01c034256070910540c010090203036801d2035400003074a105004545002c918005144800d15002410b440c104424070760007001620864140880622841d6220030304c5a03800011441d65281d6000011002e010703d006590145501514014000684484403031182d841e03a00103e61414861791a114000032800041c024480c20040540041031808126a2800c1e151500108000042e119450340103030242c0300c04841000454000003030f03130341e00c00300000f41ca01901d6907000103544520503000031030390f103503201012080340035041107040d4080e03820408101c406a000d0082580c00e4450583c582e2400440c1c80010002944640c8036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 453018947 1250 453017697 453017707
    0x60b0a050306120a080a120f14040203240a0f020c01110903010e06040f020609180a0c08011203170c04050a0909020a05030a0b0f071106040309260a02040908040506030408 75
    0xc001c0340f91000306000f01c590700041da0b12000254220155082c290281c203100f1260034050101400a0006e11801c401650406810000c241c002d2140d260096009805454140104072180c1d507203240e5003508411460401310000d02d00130310039031103a0029091404058540320b8a10b04450945000342d114410b850350000c0c2c00d0f00c6500d001d200c2c0d141c17401260340141040e880c05444041042041b074401078090500016a0003a03a6a000124043c001d0320b160ba50b0114104000c0c003d00038103040c5d1002001c103035550008281e0600180b890003100e689a5201c03c00000341e00701c41d80707403528094068221008184008180c0b661411a85409040c080760005182481801000a40105580002e00981001500740301107004160040d0380001c00420005040e2a001402c880428400040207410300548040c041055440100f5204607140100703c42c100c10075001324070344450b00c60900948194001ea0810f801030400d60000400c0354024440a42059900d20100c0d0181c1d008480c21102c2da000091 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 453020197 1250 453018947 453018949
    0x30f0a08211005040606090303090e060a080703030507020a060e0d150e011a0a0e010e0a0209060409090807050106050a06021506060405210622030c050c040608010902090c0f03060112060b0a050306 86
    0x8928170040c9170900e0806007041c5180c134040c050b110300740038545288000d80b0000c1d4964440e20b070000e00404040003107815495882c02c009020780c0085104a00c41c0941243c000b407202c0c41050513151745600141040d0240764a50f465040c004250f00c0031500c0c1c075840708078400281c5000e2003041c502c14200c040f002c4ca40b003d5001000311010f115009941401100720040c089014880080d81e4020000c4d20016034a062110001d0000d010380d03400901200c3c00c180d207a5040012003809031481c1d0388100300910001e52950100160075000380512001684215500b0f04001000705d885600700c18041c101034645511030010903580207140407030321142558000a02160f1004002042c2e1000440703070800071205c1001924428501020000b50411002c541c01005011091280054400740248108003480e1b0baa00a640640054841a4480c1c40790b0000a003e2000e0f4000b00ca0303044581c1d8a00502e03540c0d07150010360f00b50802c005e210303c2c100c0d55400045800d00ea00002000e01c0445c680745d0355144e140540c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 453021447 1250 453020197 453020201
    0x215160b011502151b0a02030708030a020433180b0a0801030c0f0320010e0405160f08040209040b0903070c06030219021c030b010c1a04030e030f0a0821100504 70
    0x130700c142c14860000c0c003048440200d45260280c19840c50a80c181c0d1601c100314120300c3d6000f251000361094000006101c851b100c6540180308407030070240b02601e40c1c01480d82040c2110340300c1c03440b408020080d07210420218441c0303802c0075243c9072078501b58100c1170b00c5803001a41500402e186c500800c1100006005002e11400d42d50b0041403c06138912425007969030720071030382c02c1e501082c1c0044030999000c010300d0f0303004008a410000b0081c1c420000c0d403400b0030010b1140c14400d41c442010030740400344d900300b9610541780b2a105503005481120961104d0303944808003940100040510702080c8403c1c2d00081082c41c914006000b43d41d4056140c000c90b015031031188981803056803d40d4010150540d6880999840d100c4880d110f0178006945000d244c0143d44201200d00c008109184401c1a41c038610194011640074502070341c5c0f101c4644101c4024503030380700004c020b00d403950b07032001281c0d4000038020b131700920180001d5021086041c1c5030540f00341500c18152030104e0402649242442541024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 453022697 1250 453021447 453021463
    0x30a1401080a1407080d0f110a2a030305030f070903050a03050301080607090501120e01021308010629040e04030c080a030519060f050910120b0103060b0303070215160b011502 77
    0x45800303000c0c12403405c1c0d40903030384a4044c917211040c040926004040c05028441c182081c060070000d984130051585440340d10104400e40e50005040181c1d06e250020907115201c1c07064a5054030344524549540c074540003c0280200b0000802c488440c01100046040c000302181c24400e4940503202e5062450581c18040c00524000c10407071603440c00c01690307a009001c00c0d403041401c400001e0810900070340030702a105e00d030b040c13509903016400c0c0080c0310801540040100ca141c0700c1880761001001c64615142c4211003c07015900318184010f204a158880200360498800e0402420300380403551044100c0d000710406001080ea94010085014141e4681100504da800030800090303080c0f101ca45644007044c001d150041c0115030019240a100c010100041c0c01c0500441c40c80b0710240c902001010303c00d020031610141041038260071420700000340c42c4a294018222224804240c1d4080195044115002207200a814100c80400c120801d4140a000200d01c1c0d80d07030002c48208068a010340c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 453023947 1250 453022697 453022733
    0x4110a180909030c020402070f080f0c1203090a15061211102f0c040203010f0609081507211407030c05071a180d0503070f0e010207050105030a1401080a 67
    0x4000705000001d0741300c821078840c25411580141c0f42c48103400e0065402c0700a241c01485904c0006014030642e8016001e03000e00344001040b18000b0004540c500030f24002030b00c8002503640404002800510800c1c031a440d080300907000042c29954950518144c080340d24400d6400c90004a091011800d100e501900d94240d00d0409402581a112a0a1070404c20710210118220f41400d01401c03c03a081c00340740d150b000c0091040d1348a58540702501c0482c04140b282e00c010445030140041c0b1002c0203d04001100c4603020103c640340d54071041030347c000021072012001d072340450201c035010910b940304904c20f406800d11701c00c0941ca001c1501800321006207010788140003080c80f1000028030401c210a041c080c0303900c04c4e000d850300d0703541c0342c80a0304415596851090040c00390180b4040d5202015502c00c1403141d440c482d00c1314844d201940c0c04820f40940b103005812009041c0010350241e0011074204880200004070310000c0820351250503020b8010700700c540c1007001d181c070906c480d0132000c84030214 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 453025197 1250 453023947 453023951
    0x207120311030f060603180a05160e0415050606040b0d050619030512090409050613030e0604031203050402060915070212011803080a0b101101150602100b04110a1809 73
    0x820340c0c108000f1410003480e10788101e5000000544445452041c6aa9010744004590b00405589421a2283d01e15003c50035481040030000584c3c1181a0003140030b00e0b04001c10b0600d01000030014400303080028240c5810203030030400041d040601c4030060012102030301001903117003056020070030030390051046120706624190050021900c042a00340b403c0109245065503100080b0210340902040c1c000030303155000394000c000101150400c042003141c800d03940d806251540b00f04104080c010f07400080c02c01d00310b00c80550429802580700b6500580020b0119091000600004100300041c0f0043c854514020681c1001c5082c003201e06841030070090024030480e00030030002c1c10642601c050280400000d840400c0c0d9041c82a80419802d4801420148002070300f2800a410401c04070b05618941d0f00c0e10403c01c1100824202010a641c5203601412405210402d10340c090070511a0b480e900c295544110305c0010102c10040000421a0700d402d101c0c602c142e009000341092a0b8084000c0da8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 453026447 1250 453025197 453025201
    0x8090c091605031b03010803180d0305070201081803130509011d06090408160c03021c050606100915020706120207120c1b08030c0d0c02060d0915020712031103 70
    0x30607090840103111940340c116107039034501d06041d80020442c00d450141400000002c100f42102100a1071a29100094024a1081d40d0107101101c5c00681c80500014400d1000000640c4900e030110b401c600e1407802003004910310b00381c1d80d055030700c007075014920071800c404100f0044c00c1c10264035004082415108906045d030040c0f04181d824000c00d214440c1680400181c05c0005010540e000500c80b5020b6003084d848901e8004400121404180c0c464441ca100350003000d502440742d00d40c4070b81e0040c0500311130744a80040c01310083c910002441449030b82e00d4040f5808212030170286c1c0e040030035070050212526002c8003800420180750103100b100c1c0100550070200710031a88000701c0c0c85c0f071072400c10381c801314609004041481050202018500030480050b004500202909240d0300400c203840c402c0c40303c0002035416581d1903000130340001c010f10042c001c0b000b580d404601c0030307802503455003881240380c01c15070100d900040080318000d00c12803035907141e0360b414403c8407000200e082c5064514 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 453027697 1250 453026447 453026461
    0x2030a14030f07030b03030c070f061b0c06030506012705011e050a050a090909030c060501050315060d032303090106141c050f01060b040306181205030603070f0608090c09 75
    0x441c4000f4005014035407103449444c119102001122410366002040e115441d40f62440031440c00901d21a140000f21125404150805d961055042d81c2d0351140c6088905407403c1015400380030010949030610504207c4542e0801000c0d0000d0103000302d01050100282c1090000340c0a6158000c1000c0d108580807801e0141c0c0b5080b0003140c0300300b074042c1072483d112410190100c8121806401850b400380c04c18568004058100c045250490310a01d028440c6daa242c03418103642d602034000d11106c030035511000c0750030340c10302045c0b040b2914082d2800f18200d104a400e030310281c010b44941526542030000410a070541c0038881d40c6d010340746007049901100c810030001079030b0001c03402c0c500703d50005404110080200401c410014102424020312000e0340d60345840f240741e00b0900c000e0b11443e050601d50030560300400f100004440e8442c0d00c99000d10980d800848594000820440d01886048000314429a04400f132100130080c650b107a0409140021109003051440b100e0300d40200f422100788051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 453028947 1250 453027697 453027721
    0x8011e0b0a2304060303020606040e010b01141b0601030c030506060604031109070c2012010c090b0d0e060a1b09080309011115090304080d18090b010509030d02030a1403 74
    0x80310b02c0c8a9480c0d00b90030003900c4403100340c50390b070707404541c0a440e12000004154000ca0360038410302c4100c404100c07845604140394240c03401074170420300041505040c00121100003001e4000e2101d00484081603c90300355240d0718000f0283c0064078400703c40c610810800604215031944203130286d135101e00f010b24555642c114520203c985910805442d0b000688261103032082c0700410340c2010500141c61120300b04220b0508201251500810641e0001c1e625017605000e0101240540d64624030103a240455804041e00411408001d450b21000d00b214000340030880c45020780c90b840c1c1d002540821810402503d40140007040040c001416401c100600307005c000d5902c06182030070591204010341740001d090030820300b0b5028400381c150302880b01c0848000080e1042c1c031280070884420046096090b03805868100d0410140c0700c0014080c0100c4002d5080600c0c214810705240e8100044a40040c0c2014103001d00080164004102c041545601101d1040d400c01c1101041d4070714200080c2d4944 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 453030197 1250 453028947 453028949
    0x1d060c070503120411040c11190804140d0f051b0f010c021c0c03050c090f010e0103080a050d180605060f030a02060a0c020d05160905091e010b0a08011e0b0a 69
    0x3c120801d480c000f0b020b028090421000d200b4006008000d85000b0f144c000d0008002d400904486214080a0890f19424501202403483e0000c1402c2c0c10180703820756009030a220034403016080303000344e104000004d01b0200c00d107081c1031144014200740900710580c1c00002822006480c401e401c07290083c405a40c200c5280400241c055601c200041d40310388002ca160118050020008040c600d000818040040380f40f015141d011a490280782e1201c400c030331098142805a40031042001d00100b00144000c0001c3c01c60301100e043c00c40c10103603840005421a184010494604508111090108480d51080b6607000b44104c40202d03545201c04082540c40c0c03801c843c002c0c01100005414240ba82c003c2000081640d4000e0401d40c0200003403400f03680340e25440d11843d040300a8280003080c120001e015051142400c00300503c42040182590401c48808010084007556540a014000c0c0c466103150f0000d0300041c1d0001c195503007a1550b10b02d0a40181216001e55441d140c8054019501c0144500c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 453031447 1250 453030197 453030217
    0x3060e070309020f0a03050705040506060a1b0302070b03181e030708030619060f03140705310b090102060c0405090f0405031204030c06140708070f030905011d060c070503 75
    0x8602c01107102045000c4c083c9070889500c8548907100100704400080c004040d03880545043c0080c0d1509018096640202903981020440e44144003500307006092907000c0f107500ae441110400c66807080b1201540d4003e80749050000079210000c201000c08100040c41030340c088034502e400d9040c039800581c4034081c482c4010120f070300020220b81e4a1750b8919800030150512000d280f4500c0e40c0e102c01424050300d0f41c58001c0400e00f0070852101140050b242544908810742300c0d2442c0c249072400543c688420032008c1141c41c01c94065545c4180c1c04000da02002e0045c180310642e5135491000060303c0c05400030a007905220741004103000c55140c010910750400c009101e43e07d0952203e01d070903811350040800c0b003000440c0100400c814140d00174030490b40c090180c00c041001071000711028400380307811514140441c01c6000441d5005100366010010001c491400182c1c0b080c00355261800e55000c00242c4c0340503188034100d4040704006011480d0424070079405c3d07500e04042a540c407616401440480 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 453032697 1250 453031447 453031451
    0x30924021c030902040204121b08030319020d0c0203030109140c0409090c1509180c0c11120a051507051309020a030b12010e010b0102010b0102060a09141b010f03060e0703 75
    0x7015916000390450b507003203940207009544403601d551209000032541f0f0019504107a138880c0e42d10b00078030134080d110151541003010703600d1075841d20544011450303032a81c1c00001355400c02c400030078140c00d4810050030030916400b030b5559524103c401019039074040007800c2580002000d220501c04107104540480b4003500002c01c001410b814400d031a56215848a2090f0102400c4850081d501c81007c84c00e88599240480748501c0043d6080212240b500180c1d0105001c3c4503001e01081400c59242d501800c0105100c15408100c134135642030103c02901283d02c0d902c00fa50005558900106c440d0b8050482d24016080c0022020072070200c10b21482400c00860b40022100007151181c0c1124050303001c00303802d82641c082039070007050007420740c964148015480d100d0700221961041c02a4400000c0c1613004040c02d8035003191180040c070210f00c0440350a8840c01e111119204c0c02d1004168001c03081d2028281440c50320000341c07800c000d121100c410036145c0502030102d03200041103070b500300c03126141c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 453033947 1250 453032697 453032743
    0xc0a03120b191412070e0103021f0c06050c04051c0b0609040b0106030509280b0105031f0b0604030f0f03090e1b0313050106080a1104060b09090a0b0d03092402 70
    0x82070039000130341c107001000c0c00b400f20f01090b82e800e6403200e54100c0340309440e019440b1080c2c041d0781400d42131110b01440019954001203020540c01d8203d0b0390449502c002e11803500360303140c00280c4041d45101c50740411007240b00400707041c4001c00f0466588080c6c1968000340c1391030603548010170620140141c3c000c0c542d440020686c110000c01904c4c0c105804400d05442c0c2c00c1906039108100c11501c001202d080a607032002040c42d0501040c8000b2400d501c004101c500c401c21200300c80078101c2110616003100703081c070000010410f070304403030880c0034001c2503219222066424001c05810310b070380141c1d40c19080d56081c0262920942050130900310740c45102d41d12500c4181040c03044111144014055600305807010800300008a00780c035520341308950000d1920b0441c401d02080e0b40080c480d1840713802c030601400b0054100010707001d510135140f804c0000d400910400050030091541001c2d800a03220000501c0450b09890b0f460801d2100d10401c0d00c0f03840c28000c0c009544034442120070056440d4134403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 453035197 1250 453033947 453033949
    0x304050d05010b15030402101707050d02070f060902031b1f11100f06140f100203070b0a0b09060316060f090e04051c091a030c0c0a03120b1914 63
    0x40300401c0e50701c005284514a60f010148980c1540050b42c0c02ea2142008d071140c6181c083c041d0050b00c04520b10070103011b1144d80c0d4110305a034540c1100354111040c50302040088001840e0040745030210f40305820001c0d000360240103052070640300100900a10350300b441000d405640f581c1e405d615003058100c1005540e40b010742c08450500c00c000403200b05115041b4503001ca4212600103912842c0e88420070022190b682e4175014081620602168021041501c3c60000742483c00440081e02803900440e86800c490380d8030180702200c22200d088050f9030320900800b1381c1c40d01e011175640200c001c400901072a030b480c007003400340300d0118454070b828001c0741e14070501903900030b003031510041900c00c2009040d803405052440c0c80e41c1c200f090489080030181030b1484036034050400c141c00e407292309000207c2000444109079290f4000b401c4034100210a11031518215410001c240c5907a1190b45e603100040c8a00c052802994032043c00c0b140b040d0b00740075109003892041c05061003100c1141682da1700b2000640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 453036447 1250 453035197 453035201
    0xf0919170904021b010c180f23030d272301120e07031101080907090e0304030f12021203011508043f2a030215090717010c020304050d0501 61
    0x300f051030313441c0404a0112000d10651007180d000c156a2a02032140000d50f02400031840d00d4080c0080c04001c2580c03d0017030030442c0c2c10800903502d0f550185013040540c00300281c688541000d804000554680608544006a00004c09003c043e42207018109003031007280c01d241a00c880e020116501c9007034060500c4c0c5c0c03140030035050b03c05c04440204071010500071041d440e04000d02003610203d040720718010146d40b180003942d10030001c41c0007400d01c05003042e4240000e4109880030903801d120038040400818920785001c41914454105011104680800079041030480d1014242004041c00100403001c058100c4990136411854040c8445d510381c503112200c0f408a01401c10403082c0000780305007010807004440a0b0403c1074140c4c08806040391000c60750429101c03444e15110f5210039140c03c001c44550141000c081c400d0040d9128107105c0381c2406020706007180c0301411540006020450050b1031000e45c10b0034034044c0000d008c05c805819001c2d5072403085204050040703883c0b000301c00c20b221086d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 453037697 1250 453036447 453036457
    0x51204030c11130609060803030f0708070903050706050d050f150d02011803050102120a05130201080925050a08010911150c030a0c150c020d14070b0f091917090402 72
    0x2c16110b0b100d601e503c0700710010300242c090020028034100c0c0100d1440000000e40c0d104403c1c035041100c2e04d0b0f07142101101d40e1000908250203001d000e41d8044001381c020f01155010f0922a0744580d00d03000580500420b580c0061312880a9040075014801d010b8101c280c01a5040001d48400c0f07000c02c00c0d440101c45070550b07242c441c10301c60070443d00070042200c190010200110b8408108800da2070700000701b01201c00c02d640d241000b40400c4049401940545e0a0307581c001c254800f078844c0700c0480a0030303030300c80200d240300702103c3c02c00709038148010720304101c1d600c01500e4442c001b002186026aa1101180d1175107203000e00c100aa0290178044003864400c031240c50b6a0b000036a92103244c100d2014001d4480002d08803a64400d0481c680f8a001042c845c4800c0d40b10b1070fa00400030000c03100802d4590401c0390703407002400c9208005c2d0368049250031030300d00e002d950348001d6018a482d2414000c0d00b4415500103c58000c1d0b0044400400b180441c10704c04000e6038080c07074081d6500041000a4024418 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 453038947 1250 453037697 453037699
    0xe07090302150c010609020c01060b040f090b0a0b0304061d0a02090f1302120a0309090b13090203120c06010e07080c03010612060504060b0702040e010c09090902030c0d0506070f051204030c11 84
    0x8191700414881203d40242c6016400c00f002400443d0710750720f061200c0c0c040c03401506242c043c29041001121259007002e0b0920078054100341215844450040b00c5900441e820f0b0f4506484003940c0c0308078a448a15810103206900c00303000d441c1890303400a0000700d805171402e160b06185401040c0402d030401c0a0f45e0100c2e9000700381d450030480e03091506840f0740140c1025000714840c420005820b03c82401180040c41005125081100e06041d100004080c3c0032002e80e014810680c021030844c0d0032400824250440c4001030036190b15003500300d121110014242d1080046032010b000188100b0402d41c0d05441c054140f034990780c0d010903400401072413541d03c030681c401c2c1000e42c0040c10300d99400040601038003c0d1028000e107180d0866041c00e0395035400c490f4000440c044c10410568015a1040da01e1601c010300740c0e14041659000540c230346403019015241e9070811024000c66a0308070706105403070001810300b03d00705081240442d0a14500400103804d1210740480c0008000c0d0341c80ca8400b080b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 453040197 1250 453038947 453038951
    0x203010e0a0f0b010501030501030816230c040501090b0307121407060806120d0e1e090a05091009020108130302030d11030603010b0d020d23060f0708010e07090302150c01 75
    0x9107810110120071000c00180c0e0f1445030003001180035440b0380a010f040e41d81084589140075248400115100b020070b03c1079907000c010312809041600d41c40f00d0704100083d0b41d4014800212910104002c440f0706030303c84041c0901d00403505d046074401142c882e00b00c0c2e00c1c02810310001c0e80076080240308651030b2540c0400c90f0040e030001043c425007260031203005050594803081c80d01e01d841d030303440e60b100a02c80c601008125178642041c0c161600714605402500d00480e000c0080311000b02117044400b064520079040f0743c0b0354007003294651042216003100c100c1340809103c86545a0006400001e01800001504075103580e6041410700810444aa2505044c41080320f00c01600c011005c80d0401e561040c400c0d402d001a100301890181c070072000d056001415492a881103a446d401500001c0004002c0c0a12640da0817a02c0e11060008604c03a02c03102c0f15404031450862801466590b058105000504c50b0714288451164002070540c1541e505990a07003506035070903c0202b0718004c1c24920300547d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 453041447 1250 453040197 453040213
    0x209091908090f0402070f02240a020703060506030a150b03030d090501091106070804030f0201032316050408100203060a0f0909031205150f0a0911070501061a0a0f1b030c151b08040203010e 83
    0x5500007081000c4dc0e01620082119484240801d81c8624034001d0241c000c120707000c14403c0c901110382c4170b0304003c0e0004003100e01d0003e0311605c00055404923030041e6016551402180c040c081440341b15242c219003280d0140c0303098051b80da10142030059000107040300803841442d0302164043d60044100350041948a444071044254000c040c04088943d00c41070203800088000d224000d01c00e42d01900c1c01d510150962441d4800400001d4000910460b8170404031351000585009a007495000341c4000c403004034001d0243d0401030704110074240880d038801d02e010104028880fa011402e010f040d001ca03655040740c808140000c4980c0d445400c184526841c1040500c24009060003c040a5202c0c0c0300074841a030303036440f2568910161100c11581c52000704441e04040707115140e203554040041c1402c044803c0c0c5104202c00c030b807143e81000c4002c680e0840c80c00c011300080035480700d00c159032004240074110141e0714000c00d2425900c0e9240500c82b030074003c54210b56003034218216201c000e604030f44090b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 453042697 1250 453041447 453041467
    0x1905120906040c060f0e040b0f0a0b030a050105180f100806270106031a09010204031e0302150601230702060307030b090702060609040209091908090f0402070f0224 72
    0x151609880883da42c06100100060b03007070142010900c10750843d15401005008070060101616559510591043c91070503c58219625160030a02901c0105507171500c1e498906984822640306810040c407810942d200442c400700c8165556601102501d4103d289031945e0f01c402960034420f03000f14103140100300403c805403030a4140c6a181d071048a03200d8400c4806800094200d4582e804050824240508040d1364482101030079a04852010001854280d81e52582540200e000d2006003616002c000c455092640c100a100c074115420070031300d5880c0c01c00d08006819000140b000e013000814050708104110f0300c14040d40c2c1119005070403280d49117031030301006004041407a1610b2207110701d0400b14003098030001e48a4810391000d80300070030580b5240c0030003192031001401000f540c40b900481124268144000400301840303080e074140c4400ba80c0c4104841c407000d560825009038418800c0c180401d560104801c00c250301583c21095545c213001e003400e6400b400e5006e850350340300300080a91070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 453043947 1250 453042697 453042703
    0x409020c1c050c0714060306060f0c150105090106031b0f020a0c0f0f080a050d180302030f0c0307080313051513380a0305150d0f060501060e010519051209 68
    0x30300e0144001e0384d00e019200c10180402421562240340c0105052000844604104004003841c42d040d003903103410a8040094146090740c0201d000c0d6050128100400003814a2131500780505800e0a0030311082d40111441e81d9921041425942042042068621001d00030f002d5030007407642103200d1440841e260240840102402d12030482090304d00580044c01c0e0401168400505901ca0054000b4902142040302c03140d0302446a1071108001500002c0165030810103800c1100c02d40e0007500c00341000d20101410201280d001521a410402c0506042075802690300f0a03034038100c80c1d05042d08516404100e1a008408803a520030307180c0107010a41d07030300c03a00c078110500110903901340350300045048a0700100c04030300403140c01c00c1c414000709030994000d0b08510350119442031440b40c05801f100004a9481c5000b000361541c0e0504280c0005000042c0100360160009081c900e5003415000002031040c4521000e500050784041e8010700325030f11940032942d04044d4201d001406041400449403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 453045197 1250 453043947 453043957
    0x9060f1e0901090905150709050907080a1a0d140a05030c06040615030b1314030a11011503050c0d081201060e180615090409020603040609020907140409020c1c05 71
    0x4403801d030920000800c800c0341c1c010b0034602940b00c030143c00300d42895907001412503030140102061181403600420350b620356070700c002c2c0f141001c1d0307403202100c0c00c2c64072542e0304072151041089003c4504200d408401e8852441080a49501201c2140790140e0200c000e4103003060300324020821b0200042c41c0140c400d001a1850055000d184104942c801409208036040c0c0c40348401840c000703a0030001400f0060300b00e030b6010bd007030007010081c10344400d4603a82400e50740540c0d240008184807103480f00f5030703000902c5a1100c0304104c2c02054846802d50b140c80b40d403810302d100c3c1d4502c100c031089407000800c1040d2050b82c4440200e20581c4170156156500604507080d17000000340141c0d40e005c514820900000070761805048041c180c1500d00c82c01d50411301850b130094004d150040e80b10400c1c030700140c4851000711303c40d60140c60000ba010140d4030400003030740406044241002003501d107605405405008850032502a40c40060340c07648004c407100c3c2030004030754502d40100380713504298120b2a00440249 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 453046447 1250 453045197 453045199
    0xf010e0607110303190c020312010312090f0e0105120717030d050a180311121303060b030303090303060402180303032a0f0d020c0703021c050c040c080609060f1e 71
    0x45402d0801c44100e5640e000454451121691a00b800c0034255140c0d8812005010f0510580c2c2c40d00c010001c001210810a13881110401400041d0700b140c00e50000e50350002d4031500d071065142074588039850480b16018000c4510410b40a0b0b10501009000c000303e000400c090f00f030100b0000103045544e0b031250008500c0100f11400e003c000751007201c3c180b00d034000e410a88500e4254030642514103d170000c9258038485c0246c402c0840201d44441e000014005c01c00c00d00505000242c10362400c00d0070f0707610306040307103019038020300500a411078007005a99002c0800c7c0c90050f1500d0085203201030107403294070401d4150100000303110446104107500000740d4031504042d0800c00c00380070084102c0c8036025003041c4c0410244040d500440803500180140034081d8100c0d2030280d2640c000410004107003003403101c0540d0101c3c10f2820080244a02c401c441400c40e010032210b0000303a00a00600c1004008620402c10440042c40303075a210364031000c0b000409445180e0100c54a11301802614000d4411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 453047697 1250 453046447 453046457
    0x5010c0f0302090315070212160510060602061308040506030a05091b0f041a0301050c0a0206010608040f080901090e0a09022b080f0c01140a0b012a050f010e0607 71
    0x1400c402030181c0200c41c034548003d001008a4561105c42200e00300028000100b14083c080f10300c880701d0b543e803020700980c114889100001003814078081d440c28005210080049040c0303c6d04011144e00820120f0340803810390f83d401c0c1c0040035803070701030154070550300400d40c411404014080b9211259000720700c14403c5174100c902c09045480c418041441000036190700c406030020803190f600b0039400a40d5844185100015800d5041d00080d0070350300308980c03d0400f10b00201d21807218907410032509004062504001a207400c1c685c480308187d90358820080d083c004000380002c410303403060948900901d11000105010304106240c0c002800706008141d100d440c01c9841c0c840d120b01e412512005180b40100d0030401484a90b58408698101100f0182024000d0000c256101006e01a0540e114150481d02c2c8851401100c00c0003158800c0c03c12a0403c0000301c0480ca04424000d400f104070071280c042c0110700016803424528065070954407411950074104400c6c051200016500d0081c0c21541b21 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 453048947 1250 453047697 453047717
    0xa0210030f0b0f030c0f0d23120306030c040902240318070e070f170103080a030f0b010903061a1c030320070209040c0e090705122a06090a0305010c 65
    0x812010740d951090803603054200d100c035611300d03240c9401000c1351040040c18240070740800d902e81074042c0c100c01a402c141d1141c1e0021208d0300c204148040149021705001d030380d045040c40404659a01013140596000d503a4900402c0150341d00c0401a008641d00d03810040321080d0181901201a0001d4030351075200002000325a41c0342501040410031384641602c038900e80e60701d020013107460007840e24140092001000443e043e514600601501a5001c2c40ba00759445404080080440f50580c841500c5245860f01142319680e0041d0800d007140e401040118400e42112403407500f0500610101f0350162403002c600d10003541c44490010300d54042e4504110140c0000c400b01d401240c80d000c4401c070320308104481c034014641111030640140c0220fa030001d00c65142c08600d50000302c15a841c000540c803541c01003041e0315022845000d4002104003802c0c00c1c00c50000252281440b200341d0f124041d01c0740503d1031480d1191070988455480082c44441c50940d24103210380200b8015006000081c40000c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 453050197 1250 453048947 453048949
    0xd030c140c190605030f330a05010e1305070302090406031104050f1003060f092301060b0c0a111513090506150307030507181401021023090a0210030f0b 67
    0x905001103d2070368036110b14641e18031440c0c0b100c05000a21040104404403400d00c4081c3e21030090036002140030f040301440100c50010042c016074680d100742d0404c44904804040364039420b10441e031141801c5008240c503181e1180c10740c00390140c0d0000c0d540243c90884000203102c0411412070712200180c80c100600c0d2103074401c00482c080212030690071000e460000b0030000307099610110146602c0c180c005036000c0140e403500e20030266001405028405c202e90401d94a0003031051400524038162101d2401600001c1183c95000120001c0d00000811500240d603445280c0b403401c10324014090956180444e201521a40b90070f1300601400740d00e804001113044c180131a41c0311200402c0c0d414141113640b1140f08a0140c031000b0302810400100c0c101e1443c035000e511403d0b00c0a0401400d0000c105c0c0300c03000c002403034050f02816030740e59141000c4040482c041d142c004035034090303103040303100304c41c2d54031000028900214008001c1d0002d2007070801e031000a6040e403050080e41c1c1408001d000c0c48540b94 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 453051447 1250 453050197 453050239
    0x3090510051512070609230d080304060f0e120903150405060f07020a080706240807081005060603070e0a030503040803040f090212070e1306230603070e0d030c140c 72
    0x1700170800407603001c04051000b07000b1520070700882c016488005e100c4940b0800410f8049507188070489148c0004405c0c8000c101d801d008000c400403601e50100224040301d1541640c807a009190001c0c0e90000040e6101035440074050b07040d140f034100c11200c000e0b007014074007690345202c1294000c803d4a004000300b0880d910100d06115034030780061700141011507a0f03c40400600c5100001482c426444034060003071010f0f048000010031040300503103842d62808090508001d00084c00e40701080c58541048681d0360355500741d80c0c00420514104401d00540c0d004110001742d2900060300398400410005600ca1002004200f514403482d1403d00c500d90311052481a03004d054240400d10780300b1000100e40500c40c1d441215944802849004140c07070000740070048409c581c0104000982003c1a003080341e48403d641080ea0310241c40c11451458401c800074405030105140d540f183c0c01680f1150285032288141c039407080d4005403030148103043c00813950340da4064050350f64081c00301d00412400070002c070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 453052697 1250 453051447 453051449
    0x605130303141603020a170703060303020d02240406090213020c01061505180406051504091416081f1d06060a0e090c07080c0607090e13030309051005151207 69
    0x92200100c0c0d00d042d90013900650401880c0d60b00700716161005201d403600202100e4014980c54900040311419410000c1c140040007800f0820340d8040401000398101e95a2440c800c56140c1d480024151210b180c9000507008820740a9400a6414110400038685500420f00740800ca0b008100c03590369100d00381c0400002c41108c070007080c01405410031054400d000e400c1402402040000c52540b03a40000341941c0c2c19180c91155900045000d00c1081d0b0503200d080d14046208070a00114034141000d032040362031842800c0c04100952020480103101e9018410045c01d03990f05d220b68460b1a116a010940c01542280c0d05248952020900d00e06242080b18025040c554030550400401c0c41030081c411400307420f600b0300000400c403000c042100311002e440e030309041c8000307000c650400803c010030f00b81e80d40d00101a15240035060041903030240e0034240001d581410042001074407410300a0034503034220716020361b23103003071900304131b911010603140f40b2003241f0486280744110381791002c0583da5111 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 453053947 1250 453052697 453052711
    0x61f090501140d020d0210052101240c08040b07020f0d150b01020307020301060b0316022a1306060807030e01020c0705120a060c0e04060501020f0a06020d0207060513030314 76
    0x1c1000b0b92192424018150802a800640910803041e801d03404a441d40c400d21408400048010036074420003801c280b5018045400f1041145a0394103091220209150046100b040c05000705020480c0a024402d1401e030a900314505585079a640ca010550316845107404901c1040d8900d20550740385066420840a260000f4a6000440244041000070046000071a0540c032085c881000142d40c2405484040c0c030240c280c280e140d00305030880f56004528013003800e007950003054400c01142c0c00c218940c402d05420341c00c05510301500c078000c00d2080003165a4492424100040407412a4110210754018000380e035040107013031300c00d904103400c0740144001e40c850f036004240c1c200724a203001c0d84036040c03d1250805680104c400c81e41ca410461b002081190041140250f0b4128076141910946000301001e0001d0003503c06c0c2c40e04116210031482030020030265000c9030300b10009081d03505603007049500800400003814402c50034049600c00740701c12800203060074800c00c510716421401900400c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 453055197 1250 453053947 453053969
    0x20c0f07080c040b030312011505090d060c0e01020607050a121e0b13140103170f03010e07080604060b0a080901021b0c0a090207030c0609020d0204050403080711070501020a020d0212061f090501 85
    0x1080c81c0d809d0708071004140001c0c080201c14400c201d41b07607482e01003820030035100c0c100008003003014000c080c4c01c602c085101181950000020001c103550040e048824440c801e28044810340c400d0000803000b01001c40040840c1d659450026030718411962112200800c22500000013010101e090000e40782da075021000c07140d0402d401007000400984a103507841d943e00340440d003401d44000ca85401c030341090b072001d800c1d0301505007402032282d00064101c2d04040241c038140441801d02c104420207100703246110040102500000d0091442907040d9800c46420310407504981d004018001d81d140b03c01e403c1240300d0704242c40001035881d130500c02c450060b40c2c1350b103030344020900c16281c05000300611081a070f004520310647e00c0060742d039072080900c183e102e6181c807482da007405a80140f18036091801203070344d540006024002685c00244400085070304071400d02c041034a5101052541c81800c41b407104512900c010b004400244c1d5412040c20344074062400c82c1e82d95034185440940e1b0003071146000d804 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 453056447 1250 453055197 453055199
    0xb0912040f06030b0a12050d030e01050606180a1e0929060a03090c1d060102070807141315170a03090b03060d0506010306020d180b0109020c0f07080c040b03031201 72
    0x50181c0c01040c20300341e000703122940b041d46da81941c0d01d241e0210002294942c10521200c5c21164052080301444031140c4001c1080386820400320b50180304000c2003d0303100c070510844001c255600d1400e1000380a040401666050b825601c00925440078001c034031146003488201039400700f0010107211520f049d50b8114a501d030848003840500c1d44011409030415481c0c4028102003030000054000811100c500485a0004100c401071602c801a101034119008900c04004402e800206401a03c201c0703c4040300c80081500010074074202000007001c100c0c1465821040c0405512107a01144c6001c0b4f000c108226042402c2d0741c444030020002000b10340302d20300500600b50360310061a40020041c24520808070681c0740c41c0d18102c001d81c02241c00640004182c6070a6140f401009000d04141341060038840b001e0381e0313400740e14505000d000403084e40030403404000201082101ca0031580d00b0285c414041d2a02022a107480003040d07943d00940c18040550050b040010403a0441c10408070070342d41136 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 453057553 1106 453056447 453056459
    0xd051206090405070509060d05150103020f01090602190f0812071b08180a17030403061a06070312021306030e010506150d180f0b0912040f 61
    0x2500403806000010390001484416100200c40003c95580e41f1030205003003281c3da0601914a101302582c515085c405a5122070503a402135230580d5850350520019660140c0d54810f2100682c441c80d05a5030000c410b1200c552010310540c20840b020800780c03240c80d01904520050301040f030400d024484003503044031801807064044413524141c0c101a07155034440340240006600d09420202034114290380e000761b55406402c28040c00559001d903811420b58903001400201c80c0c01d841e00c034052441018040b0101a2030000078002480c181d400d03981180d0294100290540c01b9400388601d6007114180144440038100d1940d00003031880c2c03818041c41c00d6400281045020f981415502d01b010b00e00d85088403502c04020320089140c20407080c1a14540901c400d025101c24a0b0320010400c010901c4206406800100201c8401040d10015114148101c0c0300c0c280e1103045044081081e = true := by decide +kernel

theorem cover : BRFrame.Cov 452877697 453057553 := by
  have h0 := BRFrame.cov_init 452877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 452877697 ≤ n) (h2 : n < 453057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
