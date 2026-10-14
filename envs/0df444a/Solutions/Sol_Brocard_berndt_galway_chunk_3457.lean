-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3457
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:42:55.862771+00:00
-- url     : https://prove2.me/submissions/36803fb2-14bf-41c0-9611-250b4dfb9dc8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 621582733 ≤ n < 621762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 621583983 1250 621582733 621582749
    0x1205030f060d1b0b03060f030f07091e0f14070c030e09180118060b0a0303020a061a030f0c0316030203030712020c03060f0702060604230a0b0d03030f0e010204 70
    0x8001c00e115003808036030b003000944102e0342c0d8900401c0110507100b40300c146074815204042c00000300f0025082090040303035001c9099000781200c0303424091080c0c903070843d4054001c107141c1ea2814410340700c2c0284031203044003110000810801b43e4202400002c0c0c90100e2002c54040b81ca103000c11100d51091060f0300065401d40d8400c444000e21600704565010b0280075255050b03140405c22140003028850807594100d44488a01c04d0701440c41c050043d51401410326224402c106420400300ea00441c0300603500f5441100041d4a9140c402c3c01c0107042412440c15416100f5500040f0301100f0004110120481c11002c661665090241c003003006407103400000e403d5081803113507600003110800d48804554050054880c5181505c0100e8a801022203e5440070030491003480701140e014092180c00c810151414014004064200c400c10a40c04919403c400107090018907203040319880705016400c002c2040c190425207060007800340041003115002140341c6912200145014400c40e030442e4916 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 621585233 1250 621583983 621584011
    0x6090406090c181b0c080a0f0c080d0504030201050c0a0f0309060b1206070306080c18070c060f0e071401140a030e0703060203090607020708060c2b09120503 69
    0x1980d03000d010780031002044070141e86000d0042440c0012802c007218034050224005031558820504078205901c003034010081c8440c0f802d540000c1031540007292103811050520095080300444110303440120980c01038450040883d14500341c11541d04054015400307a0700030712136911005072407640c0d4812180b0340c001140c0c00080c080c0c00c0134025082000002e0040400080500c0345c080401c0f440340340c009140483c0d400020810141903014800d000180c032075000108900c00342c80d40454000d51074034000c0321502c584200007512043c0309851003100954804800d0281080e80043c0e40007a020181c1d410585000c0e0010100b4685940c4400340c102e94016900c210119803008181d041c0c6502404140f070402d43c40c4c62007902d55020400c00341006500c5901e00503500d1804000141c107098000d4021340443d00008010005080000307500d80d002444840c60035940d4580c034100007268665401c14440c6101002130b00059000303507a2280308058000c85402801d00f034001c5045996220850796622083c40f2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 621586483 1250 621585233 621585241
    0x9030c12030605060d0f1e0b010f020607090b0c1c0207080d0e0d110d0503040803090f0f0d081b060f10150f031e05160e2b0804120809090106080609 65
    0x300350400301e5100036540000aa0701c0c400b1100703500c07034842803046540e8a07480e08d00c1260309580c04804011100114400b17040282070140c0010856000d034850114500c0c40414214241e41090202c80320f213480b44002c0e03000b0b40089c0750010f5155070aa20070b0034014001c405a034050b182c00303680c900d002c54000500e400c600e01103950700c1091801ba5091a50780121304c410402000a100304024001703018807200554942e201030003000212009840102e002e02c1410030198115103840b81da2000d80c5038060f150f030380c54804602908200f00001c0040541c10b100303000034000e102d020307602194000c2d4010607030303241c0d01c50f03d03200f001500c01e841c4c10032400000d05030321118585500ca070784214000c541c6101d0221581e0708a1085905642040e141c2502041d10b132307400758a51a030007096410000c803054911203106a450101d01c2d01404044612541c10070840c55010704000c140400ca601420b0781c0c1d0807920300b403034442c00c11389082c0d0010300105004200c804008103c0600444c5010722441c002000440c181c1d403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 621587733 1250 621586483 621586507
    0x10510052205090103081c0b060922020403080904060510020a03140717220f0513021b0f011401120f1b080c041d0705121009030c1203060506 62
    0x88038440e000d2200207900c0046250b564010380c8900850007031a100d5150b40840000210702c60f04108070300031003460640d41258640392403040d0341105900b22511422a81c295180b00401c4004072040d44645100040c003004101c0010040c09440000380c5041214a0720f070414010910b142e10340b04000f60b840a10341c200040d110311420320710030403e00916401c1c19010b0359201244440300a40140c0307048003082e400d513140305a03002e41e407200c5005a54909114501900e8902d140014056540664000d002520183c00660116011015060821544528207801c1d04c1c0e11240c010301009541e5017440350414020b5109419107050381d190355014203061803950f0303a010a0b03903901001120328103030120b180081c4c4044020702000408828010342121410f040411007280c02051700342c035522100c001e400d8440c55000400400351201903440c4e17151650300b213449600e40200502041a0300d418210f40c10100743d4044002c807007840c40342d0304201090702d0300c0d03074250140d900b58040d107038004400f844040d05001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 621588983 1250 621587733 621587767
    0xf0307020f0a03030204090b03070e070e01020102091c0b07050c0d0e041e0b030706050309070501050c030d02130501031a090f07121803180b040605070c08010207031701051005 77
    0x29085004440c0c000c80401c02140c01d080d05604190f011a50100c1c0c01c0205041078021483c0441c0114050a04c2030b040500700b0000d2003002d0301ca602040030807504056564004d60403140e81c09001424507005143c81e4040b008076038904041164140d8804e004103a040b0b006106484030350803500c01a00210f0128032046801400c15241c4a038002e4641e40800201480c21138050000e4074079180200b98504500c0501d0b290801a6100a081207020001c0041026010130b04805a9000740b0b4a0750381c8400e058000f0380303540a541c43d490001d80c40025204159a0f0381c0c13000c002254800e0b28288011410143d90301a00c02120002e603801c6141d501c002010340881802003a4083c269003450302d4910040301c00c5d6000c5650030f143c3d0886108141e85c030362080c59041044070200d90103100b00710030201d0030f0107884809400b640c070030401400070101d602000c0000040c205d201618100008544903102410003d0804890b4042c2c261583c065600200300d40c1041091914100203544509207001d0700b00010107504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 621590233 1250 621588983 621588991
    0xe030a0903113601061b0204051b03010608010f06030e06060d151107020315040210050a030906240b0406141605010c0809061e04060c210c0207090207080f03 69
    0x3c803101e20000034855140c40c40c11050b200c0d07030140800403403169000418071400180c1048051208404181c801c0840880e071403900c1c207a06036800324640e112144990710070001c0e0211000d04220220011402561083c0c0582c1200c500c00310a0198a5440c00154219074800440d14540e410601c00982c560070100400341e10188982154240c40e210203a103501240c84022180003007a00024128096240820291280064903c15882c51f814907078002009036580324150410b02c01d01003103c4509a00a6001140b816007002e020702c400d610301100c00c415018020030000210080c00b10100300c4002da203081d40d054840b1a00ca1028040d4035408154041e000342100700400411078803458006a420302504003240b15549440101d03007400050141003010080001c04001d9200701b031f40805401c03089017640c00541200b000106051001411502034102c1c00307810010704480504114154001c1e404019100d42c42c2d42512401030301c0310000400d901c92000081c00b117490078812000c64842c280c00841d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 621591483 1250 621590233 621590239
    0xa0503042a06030204030201120e0304050d030e090130081b0106031703060a081c050f161407061d0f12070e0415050910020a031517010e030a090311 65
    0x182041615a5181e22180340e000840007030340105041046507000300c0780d03801c0e44c401d5003424480035003103554180c0d990141d441054810380040012809140c02509407032611500503048003a2580c40f12107180518800381380110148414000c0464010940c01010829680c00801e0514103141c090f450407004154600707100f9075541c2c8490010004135050342d240e0308803071922510780d100c2c07400e141080741e00c140e59840a812600032a0340307030f180d44194a91030300d8035241034200151a241201d8007a09140907000754000d140c4814145031043c04400007800c04001403c404490f00c0607115401281c00b0302c0d0511800ca1001d0708820280110300e8149a9584050809081101240413680c00c19203800c00a03482240c0d54a0b40f0300c140018445440c0c03103013035000c4020f8810b010604003613111070394940b60f4801005038503601103003403003501c2c0c885e0704980000508680c0b5030380e0180e144c0084141c00c0d03580102904044d03103440c901c03d908203070101c10384010400d2a11b400750694a940c682c090118102c88091754 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 621592733 1250 621591483 621591533
    0xe090c010818190501060504180809130b0d0c03020306090c01080411150d1b110606090a020c1506031c09170102040b0f070309050108240f0607080c120a050304 70
    0xf650904030031003103c126020714000326080e4a041d0902040382d9581d0480c66245041e03c1184020640180485201306000d80d16401d50049580c2468020b2580c18142580121141030b61014820109080420f40c1d000301c06440300c4d42c44690501c0e54070703c2401c0c0c1d02ea01060030038000074041425240e1001225002030540c009811942e907a416580d8002019491400d945000d000c4007402e6820840540e600c050030400c1034854203011a6949040080c074036031094100000103002003400742c05440c446122403084440d0b0300b40c482480401c501040300c0d180e0080c840c4450103060394803203040b05003042034940c650b04c0c0d01d42e0a00200440644620121140c03541d02000f0000f0b242241c0c1005000c03000d195160381e03883c1d01032490001c150003c130343d2050741007101c24014000b80d1000b0440441000984120150018480e40e0100d115100100006503002401040748420300c42800e005080404c02e10b0300303454029001642c0e5110350b000f0342400d0030000e41c0c00c2c0001030010740d8490101d0b6861090320741c944 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 621593983 1250 621592733 621592753
    0x301090506070216080111090609012d2c09070302070f12031401080709020703111209032b08130b0c1c0504051c18080303010e090c010818 61
    0x40c1c0740140075110003005030303c005045203420800070015805840c0040c005d0201036481c401e10503090050201c0c0134801c0c44002904401a070154074210f1034024201000343d00d42c0e20984001c0101c2c04800424000300319000800d081408940c031000c80c1245400b500c0c6500300760814180442900020710310802e042d401c2052001040c2c1c4103c2081e50240b0580c40c00c902d952040d000141650306201c05421700c8142e1000510007400d020400c00c0650301c601400603107514150804130f8080c1a000c030084640e0142e407071541c06405a0100070800741006804035215111081c40c203076042c81201c1001081641c0400c04216403c0c460399483e50003841400440034007001c1034480004185080d1400c541c0c0c1d01002071219041c1c0040010401c846007203240c100080c0c40c050311081d071252041c006407100201005034902503203002c0c0c5403000d004034903404017200b0582c44142e00f0faa603610a004041d00021050b0005e89903c00010300c9007110f803010713510001039442c2d00913122040380501002070306901072000d11b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 621595233 1250 621593983 621593993
    0x12010b070f050303040c06031406220617061005030a030e1c0b0a0e0d1805090907120510060f121403040803130311030604020d03050a050708040b0310050118050d02030109 75
    0x40c60249026214482006c1e1070f248000c0d041724080f007900400781c0380040170011a03680c0d90642940b2000da2000c0380c44485041c8030142c0c0142441d4001e62a40700841c0b81c4402032000000d0741c00d200b03405444405801070386600401d0341d6090b49400c002d00042c001d610005c9241000c00f031109030070075002d561225a190361356996160210449182d00c00c00d99070b00d240c17801c4613010005e0513481041410502c8008401c1e584011083d0851700849000c1d00020020503240d140401241000b880e02c1c2d49400728400b424039185482d9509007100070401801c2c1344002c503850020341e44230400c96040322000b0032082c0c40355440f0000340b210b00071907008501042c000000c01c80d10a200400140f41d4040d6005000b03400c9d407911038181c0342580e4240d4002ea2000e4100320060f00c4402640034000e4050400f1601c8141c3c075441210380e84a82d2000504000d0003060020b282610b04020b58010f0f2000035400341090f03103071801119130943c1403503425011809403404105a00b01007461100550002d4000310b1100d90584407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 621596483 1250 621595233 621595237
    0x402190e0d060e0114011707060c0c0e0c040801290d020301141810051b0c011104030c0e0a1a0409050312040f0c0909080a2007030804050a0b12010b070f0503 69
    0x4443c40a07511980046011000001d0650140c6031040400c1c1e00b5068207a0466950760f502c2c05076509002c0524112000d1007000c000c0c01000704080c02d001c03046031400f20b101e0440c0c2e4000b03104e5005a90300740114455401d03154812601040c180100f540c0c03000c0c0e0400d0400ca038011012000341c0e00342d5684d01691441d60703d1184154071810140d0340d111189124032215925004264400a110501d86000d0040386c2050169968003001080c01281d16001c1c04011580101625660440010f00009000041200e50804841100e00072030f142c1c000e0341d0f43d180d965429a44100d41e000a21004e010905600d49000c0d4052120103009000f00c034100810040042001c03542564280ca58078181c240d0082000054070f000405802e5225081c81302544640d110030090090241020500a0b1030908920269210f011406001000c004440c0725660328204a203095006014807401400d10100215029540804884880e03810140001d1107070310701012014290042501180d00941c050085804a482000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 621597733 1250 621596483 621596501
    0xf06010c1505090d03020306030a06150f1401030e06060927010e1e03040e060405060f211c0203030a0c0207081b01090f03050307110111070909020a050402190e0d06 72
    0x800509424001d0300c50b8135003203120740000d0425004008001035a1000300d940350206900400c013090030300c0c3d0022440e2491650350481d40c4801040d040006e01c480d070703d180500340c0440a0b20108201d05680c1c5905407240403c58005400c00612008545108080501035011400038101001e8521199025a00707447c2ca81c03400c00c1003580031003140b43c5441000c1e00708601d0b04c00070500440c40d05180003212100d01200030f20311340c841c5075200005849038850019501080038002d00e14982c8014242040c0c031961040601c1d01c90303a10901313010820102d02204030b0742405155800450866076180202005030907900107020442c00784d00b80005850604005012150b00b10b42044c4c42c507840c000000400e40c01c1c460b40320301c008441d1680200040351001c800c641d170890300300d10401054010030300140c5440c1252010f4034030920613a500024503043d550702149a40788202d0302c07410000d035180f0402007a80940c0140302030462840104152660213001d068603105400f038004c680311400c0d611520129080c201e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 621598983 1250 621597733 621597773
    0x1807050415090302180f071d15030f0f011a0c071d041103030708091c0c090f0506030102070309060c17070b070201200406050d021204060603120f080f06010c 69
    0x4200340f08510b4030a0600d0313000902c5018001280c54031b80755141c0e83c0c800c00b41c4098188200c0043c400d00591140c40e100148040c06050506080f000c040414019881100e0120460500c140030650301a500800d113412200c81000300c000720744110b01c0e6201250700001c968215442011000210300c45c2c501103040362820900480c44030b928181c1040d10072404200860b83c460313001002003000213048032007a51101c240030b94400c501610b00a654002208541038007030540410420300082c02e5039180c00043c02c03480111742c244440c1d103c1380203241c00e078040c4041c000c01003685070304203201d241d204040302c0e00c5c914090211000344460034404600e0300d42c803004082e0364020100c03003001980ea409019203e1b101c07209040c1d02c80c41c12045d101e803c00c24080c070b000d06020041c0006032095900b9103501504c040104c000004400c904040c503101008082038841104c201c18200c1502100501408808a0407115903d503420956aa948182c0002c0740090001e814000000c8060000c0340c441e0482d60b2055500f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 621600233 1250 621598983 621598997
    0x6030503121503061311130e1614042019080c1e09030313080a170412060b04021c06051201021309020c192904021807050415 55
    0x40000404258801441c1041410410aa50040d83c40018015074420040304107050702a0007490240075a0045941003548820b1809840035000d5196000781144c4812400b154109920880c1481081d56544211700821041022000c0b407824640c020986800d1000703022103281a1911b004501500a0300c40050810140b08828174207541050020327403c50000e1442506003800b0381003c0c40c0303118407090f514030b0003170000c55022501e440800070b482c83e034009800030b5954103031111a01c0d40c1d200c440400031b4540201e0b101194010541501c2183c040d00d19000013003016201ca40c039003030054078001c1c0c403040d001542080049000340c00030310444000d03c40d00002240b402c0c40c0c4400c20481a60200107820140d10400c40703000c1d1070140006007001c03141010030150f16056540491824220701c1e000a00341ca014600415041040c50000140c104c080c80100392180684803440f030f884c03100101e60003504001da040140f0008004018582c1e0702c203c0300e181481c6040d17201e0802c0d051071a414000000400c0320 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 621601483 1250 621600233 621600247
    0x100f02070b09012f060f09100e07050604030501050a05130203120c070306020304080a030c080705250b0103050f060a1104050d1b090b040e0a05070b070c08150402031005240a030606030503 82
    0x801e0007159001000170301410b1041c1040086a038a41c481c901507484040d9841034a07140c1103905012b62401064028400b80e155a03a83c200180604401c68076088024503200000c2d01c044500340d0b002509035000740080400d4054031b801c108881d80244141882841034000000c001426800118480c510034610749441d00e034920350240989901e444080103016900c8200000b440e802400e84070040b0030f50006540c0000403e503007040149003075101400b084d0445c0008000d00c0b80006407590308001b004200d4640d40d88200c603220881e0800600501c44a004110410140c03900d41010448580a8401c07082c000803183c1d1200031282c890b0744921615511441000313200d1402e403040e201c890800c080580329210003940c0e551b40b6104e031401145195000410400f0902442c10784440280104a0444101c0d81003070340c0ca100c1e07040e400c40d4124071030f104d401d104810450541c023075940a0200800c8a20047c4101c0410340044d9804007460344d005036035a2400808034002d40100001540a00059591816 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 621602733 1250 621601483 621601577
    0x22115090c04110703030e2107060608030a0306081c1d1f030608190b0601141308010501030b07020f0d0e010e15092701030f0f02100905100f02070b0901 67
    0x2c41f4804000c0343d0020358030b8001c048118154641030b000c0b8080d01c0da1340c810003840d002c002408103412085083c40046080d5122a0305a4000d1082c1c5a10508a40d0f408180900505001e0101462007000400e43c502611041444114003120700100601400301040110440098507402c0c040400001e62101020000284240001705000200348540f00001d6042c0d1500f001029000c1c2030729041283c10481c4c0c910302044a000d40d1054288010390804841d07450015034080c24080c0400e50303400401e000030071440342c0001030700c41e500034085004d07103040f40e0500003d540d01c01d034001c466810700440c00c4200d0345c20769400c1e0b500c86c0e0740c0c141700410b191941101e074103221074654044000702245008564441e4080ca005081034112130303006082030210400781c80d1142140302040e000a40002000d41600d000981100c0c0c10016680282c0b444d003904410150103c1e03000c1000d2803900c02503000660140711409004005146083c4103040c06c01c2e031500c1d141030400600e502405c25140c03c506503e25081580 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 621603983 1250 621602733 621602741
    0x71e0c121b08030a050f0306030a0b0c0406080f0f18120406032403050a060c0309060e010902011106060a26030301080708070603060f0608040c150c022115090c0411070303 75
    0x420b0440c0114200303111401c0107800ca219074009403140c01404030001d8030359641000030741007280c1d01075a211024180b403804500d9642045c000c403000309101000140500644000e01c0b881051300140301c5005403510510b0402520301c3c030310104a54056112a08840350010000f000100303843e9a00007070600641d21600004a41501d07e00440800c0f0901040403980004002004941010001404422184081d001000c1040c0010401070030500b8280056034103600842c030060007a2108070005a0102c0400d40380e000c00c035072455104003031500903c10340c0041c1c260b4010480c0e9424440d2002c0903000710091550304264081401a44901c000303100108050001200400e864201804000d00303000c43c0d081d4040071402070313900f08172290000a0a10a905103c0b100415408000010407880300b80001c02c1c09000010690050364000400d21030314001814200c0344880d01c3c00030784508142041d682d05444005048050140310300b100400480d5120700c1001941903d203512a81e0781d1030b1901c4c024040d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 621605233 1250 621603983 621603989
    0x12010f021903150e0f0c16080703120b03061803070203060109061d24011b03230c0c0105300403080c03060102060604020f070503070b1506071e0c121b 66
    0x120040c42001001403032000b09821940d20b4403200100c0d5629480006c203400303187c6d8002c0c210a001c550107070500c400300c00102105406136440040030030340440100b060750b640c000034a40540c041000a00d010340c6100441c0b610180c1301050f28908510385d0002864030800380c004051036039555200b00301c58a9105226441155008200c1805192070340d0710210390a11203029042550b40d0a41a88040e0310400b200003000c1c50f00010700d10241060f040003020b030f07150007003200000f10300c405103400c0b6002040305550480800500500b01045200c3c01100c060300541c900b02d0032036a020342104000214500303408000d16150112100324903080c14018030030300010b0100761400c4030400601c080c60f42d001c580c1a07404070b01641c0140c1c5d240d0145c0743c145051700c29090050003900012030020204902d0400141c003407229640e87c0c18188c0000070411503c0e101e04d48000348440c0422082100341110070b806502c41a003c1c1e450808490360f85d10031181b14030420603084a00c2480000c220300042882003400c005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 621606483 1250 621605233 621605261
    0x105270705121c0206070e01230a08070813080702040c030216030c1209060e2101110301050f06030105180901061706060102010501061809050c0d06120302011808040512010f021903 79
    0x441c18110f0f0064011072082c447c2604001e83c0300141c1d0f170801808561880d0040c04081c0c00d558030f02820b00d0003007100d44103403044000a040d40d00828038820f8007ea0b292360076504001c0c498a4910b09608210041041c07000e03580c10b05809110f04c02d100d480844984200340d000340c580c04c03642103851812700c00c0340404206000074020a250700340080ca47c0030302035100c1075000351100309510030b146015501c00076241c1001c1101d90f0030046c01c0b419001e0000c020754120348055880810b284804000c0000a010902849401c41030206c0c184004107600428a0b030040f8400000244c1651266440b000390070580180c04007070340c09681446010f590911415004000624001c444c0b0700c24491084a801c203d8482e1468060716800418190300c038182c21200000701a4001b04040c6503203155520009120640c2a07015520340190101700d030040d4a1310070f0344140e1100405240c04d081008008401e0300356900e03801c0c25962200704203500e5009100422000601e00c0f40203e21030301040000341620303d01740300581 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 621607733 1250 621606483 621606493
    0x90506011a0f03070c06090212070503070e07020d12090c090204140f0609010c03030605300c030304030f030c240f11030f04031e0507060605030105270705121c02 71
    0x79840c2d04400940381c2121452400c481c081451b03060810141c0050070780698484025034415040490005800301240c009405481c203559030f03941c03640c1d00f5220898100c0090f1300452036000246114030034840200403881c070001500256a25030210030201508030030f03080c0e44d00040c01d0203d2080700c0b400501c0410f044901e00503540c00403001c200c00d40980180d26062018000460080502941180b0003903c0301400c003c0d1208c10301c3c07045a1050030410450010000d007048816a0000042182c003c0400040d0003140b8180c0b440d5588a0b12100b49281902000030130084800020f000c40384a840301e400d5900852a010700f5040010100c65191000ca00450300d4144054603c801c40c5041d0303680646070309400f510641e01c1d420161003c01010030400e150354900303c81c8000d9141c100019203000340c0a942c00b08500c0b905c41d018107088940c00d4070710355000000e03208030a641c540510b11911480e100d280640700ca003036407000030038260720a80c640c030045038102243e404da01e650340d0380182c2911240c43c80189 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 621608983 1250 621607733 621607747
    0x60c120a0e15060f0d060515120715140307090501020d1b06020904060e09010e011407020a020d050c12030909151e03012d060812040b03060a0504090506011a 69
    0x1551034034000090225055000000b404564403e031400c004c0c92000341016803811035a181ca8001060111901c02101040e020403c08504084101070700001c2c01800520429081079681e42800b0803101d4003a04204002902d54054054840034501074001a00c9030003503242050006414114480044420071516040154038501400810005560050b9005a968103441c2c0414041d0065070071007000c0b0080041800b106900540c8803030010080c01008210303651001108a4050350103a40e5080180d000a80a602600d01241c00d0040c66124400b16400c03c001907005c1402507030082e42e980080d800119882200d4149000200d900100826800c2c581600c10000602c005c040006c0d1070340450081040782e62a13407401d5200c08601c032a1500c91020420341c0710f500e8025440c2040011000d2414510300090032100090f452400701c00748501c460500c1c4c102801482d541d000106404d83c001041003000a054440f44103100031203000318064041581405032485150503440c69075810224100900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 621610233 1250 621608983 621609011
    0xf0d0302030702120306060403020307030f0c120c0306150e0c070204060f1a0a030b060304111822020114030f090f0c0609040905010f111c0504051504030908060c120a 73
    0x2800f0b1003080c0103003136900c1e03031507040c0854518069500001c5d010701c642c101c08800e0104040c0c0c0c0c00080c0b4417074114880026143c00034a854041407060040c251850801d042c000100d803904a03e060035500b15000344819625148002605800d0f909951500c0c400100c6806500f42409440301a2141c45134904c0b25500d050b902c0310a000300b1161411034440c01041460400d031094210f98500b00c0018001a00e03410b00d0300704401c120f40200c0301d082c4680252680041f20300300c115003083c42960090b080c4410403c000410007103804841d1000c84c104403024400e20441c00352100614064850701c4220b80051800c100450704d089a0340c0100c081f41d90103100a54002d6640c5002c0301c015030020355000c00c803c1c0e0185001400340c901100e030441d1482c105408042e409074001c0180c498006200c00c0070b4400c240e00c10078801201c8050310050034607007040035a0540b031110340c21400c4d0058400e1914102c2e042e90750740030605101068801040141d0001010700400544540058010100d2441001030520303011031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 621611483 1250 621610233 621610243
    0x1090e0c0f0f1c1a01060e0409051f0914060604060f0e070c0c050306191803051803120c0d020607050c0a151b170c070c0311130903020f0d0302030702 66
    0x6403901c10840d0042c2122103880c0315601c80d2a00307502080c01303002421410700400c2d0602090040a0005e802c1d2038200304035240901a5000407900207005d04004e00240181098100e80101d1020380c160b1108290301c00105000210b264840002010385920304159003040241c9966501400581060b10010302c42c0200400440c0d4108115013081002040c2c82d20f0903401e1440c059024a031325003d6a0208008089466948403c09000341410022024820003589111640c3d21001d000036405018202c007a4034a02a801203030b000c014103e49001284804040d616882085000825085813510260803501000752542240060404030705141c0c0171046a13554446545000c0c0c40200245000c5120b280d0f1580010b4480040c9607410300e4111041c88003503c40d10107a0a0b80070301902210001d46400b5150b400e4501c03c99201402501d12491030319000140410090740c0759121011f00c04030340310404a4425021064469006044103960703c00001c0d00f000300623004042450300400401c0f081c03d81c0421 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 621612733 1250 621611483 621611509
    0xf100201050f010e0f160909180204240513180305070b13020105070201050a09080715110d0e093705060d0b270703080c061807030818030601090e0c0f 66
    0x34428040030b1384070000312501c4510354454070115240c4544101d2075183c034010b849d1941d000761401c1c0f00462881c07240505c0d4003090f0200030195481100b09001519102d454108400354034400851000726010b401c0c58000d04522045001c50400225a810020141c18455000f030718240d18040004a070340000c0c00fa80b08003a0001d04016000500300922800350540c0c5026001e940300f103c140e95211001c82c44d50311040c07501c11001c100d540c078502d08142000143e807051032006039560034100b0860002e01030b2186019100589143c5030440360a52442e007540d440d512034a60044200c080f051080e060011941c01410150164904010300c8001c51103400d8403a0300001c101d0065003091000e806000d0025200c04040c8905001e09403002041c010220003625103040391009480c01030700c2d607000d900d0707403034881d0442c0d41c500360005403080001c00d22002c0a0241c604c804141c8a054004480009040903826000600025075542c83e81c0c0f00344004100070004440c056905c207154890b41400940c100070150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 621613983 1250 621612733 621612751
    0x240a0207030302151b03180601270e0d05032e030b01090b2b050330040f15020d1d0d090509040f05121809060d1e020f100201050f010e0f 60
    0x40b4440c9041f80341c0c600c9084c501d0109888041d41c483d1060781a040c0619080d00c0d40c611502d0109000080f540302d00d43c0ba208180d801022100d506620681d10f90b04000d08407006041c0391044007080d016032001c06001c0041f54440001c00908629040503c4801030300301e0300900f440c0045e4000b140d10380080d07008450000c444080c051303264080c3c0f4001c1002a10400420ba4000800c0d08220316080800d04d9112040002017000c030342d1445034002413035100031a005480e40440060300c4d00499003484d00382a0186031030740c1c054a0000640c943c4011307515000c000005040390b040c0041100c6805024654150303030140740c0300e45914501400190240e0028001400e002c500031008010044200502d503103a030000d4035140e88910794459512080c00c030540d402402000d0800004000c0d01c0d008861180341eaa0190458803100c03200a00b00144010800c003ca80006c90a203414040d42c1d50004420683c010035400032441d458400d4454907100c0c41030740708560303800d070110a0240d1200c19000c2158451011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 621615233 1250 621613983 621613987
    0x501050304031d0d030507020907020102160b06010e100503040c09060b091314040506010807120807200307091e0c050405220524090f0105240a0207030302151b 70
    0x1142c070300b0b0b83c0c141c400f8040c01c2e80300301c0e400f041d03408041c0c1100103010039034007c80d0502065502d90009070300780c1c800d604020303161054441300280020407011615420502c10302d4080080c040c8103010911410544681d50041080070007000304100603850410b002d848140303000e0207194076120b205c102c3c900030003036003901c03038a1140c0c540d200055555001d40d072140820940202e550615040260f1224001e01551071039014080c0003044100e0341c81143c6910950000c4070038503000c0c450701e541c03155000156907001400b0b422242c7d417445139801c020940240080c3d041c00070f40e410800301c41040d00c40c4130001d40c0300050700304064440c0c443e4124003030300c0803a201910394010b80c3d08141c0d201419012001c0c00010f45900e020300f441000c05500100c049282010500300d030880350a20b0411942885c1142e030355249040c01401485182010409030300400b00c82c40e1000f0100d6490321200710a03030408140c140c010b1b804400e081060590401400d08000d0021500b0501424040071090210310184000340d404900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 621616483 1250 621615233 621615257
    0x105061f2304120308010608010e0c0f0d110a03240b03060616030e040b04180303020906071505060f100f08040c03050607090e01090209060d0f090c0e1e01050105030403 74
    0x140660001c1c0700000e10303400942c0c0b1522110110301e441e039548800d40005600300000702da50390091903514140d0300c0000300c2c1c2003940c1d00d6040b08009d5a120b1081c4140310482800091440c8240c1c5c0210800308148011281e1a40034908008003201c52a50750b1031a449289140d00a00c0541201c0d00419140c2103407510b030381ea950340d43c04030b2001e104208407240b1541d61408520141039102d0350f0312034480f10882d07051040c0d00389801003206079400d141c9040756030070404d034803400040d00a500410412001070f1000d4141031254a82e1940c0e40b10301c0c0e8003801d84a03110b008010035840d05041115180100303d88102600e204004018003d11403003415005100f2108003040c244a00307841044001c507881001c0f03541620b00200003c102180f2842120300358400500080349010060003134500762240a06428100000801090042d020031024120160f41c1e6034481d03c0440c00035100d61010304142c080070385490422441c0000c25040510125003483c5010300103225030307a03201c404c0300c1c3c0080e01447e0101ca01c0c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 621617733 1250 621616483 621616517
    0x60a050f0a111216060b210f010f09020310050603071a070b090d020304090e03071514010503010b101404030f0b161e0503090708010c0903110607050a03110f070b09030105061f 77
    0xb07681c802184585c503101500301c003039000010b014119400d11074024400c4ad28092080d2043e05c290400081d8160010589011020025030000c0e038400e10003070486060658651200b1020100c0b5030032041401d0000540d41c0070b02c450042000d4203c1f08a00041051a03000c0343e00a4a074012405051056074491800c1d49203424100b0590f8180c90300402045003078410140e50500a02c0a12440c44c401c040701c000000d01c07458188112225140017802030303411260022811904184001001c030301e0301d1400d11002c80800c01020b46414464071590301050181811a600f140f1008410251301c100281d04880d41c805040e2942c44507882c0a0908000346c0f43d844500849007070100f20f401c0340c1001d40c645801c640b01d035548000050100c81c0100d0020145415040500a5505c191035000c1d1181d8004500e00b00028494040501c101d0490001d4440f50100c00310443c1c2400c42c15440744060101c0031450700c5007440d0a05c6030603002001101e201004034010300c5005280c0420365042c0003403003801000b09401c11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 621618983 1250 621617733 621617749
    0x232104050132090703171c09030804170301030804050907030209040e1c0c11010f09030c030c0e06060c0604140709060312030c080114060a050f0a111216060b 69
    0x15451900a44020720568424a07920140c1044414100c92040c0071410004000ca050f0041e05c0c5c01002400c28a011b54461048540c01130000081c42d4040c000390b2a24150140b1410403154481d5640381b215044c5070608143c1031400c0300300d62850700c000b0801040010000f40840d002c0b580155464049135071209002d0340240030380c0c01c04503045030804800380c0c2c4454001c140c860040c040b62800394012002400101e074003840d0040b000340400084010404150b005d91299802141d0503e4103030143c507141c0da10b9a40c00c148540c0111030b00d680300e0406000d1942040403140c1c1c004c0381500c102d13051102d1100300a030b07500c8d0080c01c0034001d60f8941c4001d070f0702000d00344100000b03000d0040041c000f03035503a403402ba607403d06c0300003030140001e141540400c2d035584a2440a8100c0e00d47c41811700341e1554900400520394021072032070050150800c803e5200d400d4110140c5031501c95030320345501034092403001c503040410015000340c180754104940e04640050301c19141e241504843c00285500c50580481d02070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 621620233 1250 621618983 621619001
    0xc0305070b0405010e07230d02030a0f051011070b04020904021f051b060f040b0a02070c060f031b02030418020706051f080703080906030702120a2321040501 69
    0x725450070001030140540240060070011000c50324802e07919110002404200342e402a0221391600010360a440c00c410868851400101941c080249941ea0000d15030805401128150040707400220032203080c0c8200304c400e80d2824649841c01c4201d42d2036602588000748000d00c1600c1c800042804c1d91500e000d840715401a0100302044c00354085009810750300070107000d030001d0400c0c007050500000d0124071a80034807000004050b6903100c0d13036603107405454024170742c15409a090140a01103040142c41c480105059113a080c46c03040800d80080170703035441c00c4a5841d00180c405401d0192130b800030484003212440c9210740c1c014200c0441c0400a0b1080d408090501c81c10030050010720303001c0e000d001030110340b1201070f500300e556543d2500d91203081510015208901c03e10840f12203050003402554030007001d1054802040d586401031003580c1041006000007904121a0901800d903070189068000d8140074444c10f04d8201024280c0e0440318842c5143c90440c0103001c18100030007500b04082c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 621621483 1250 621620233 621620243
    0x112080c0709020f0c0106140a1205010b030109031d0d11011d03030d02130f0f090207020f0a0303092306180a080607030504060624051b030c070f150905010c030507 72
    0x40c4210003030b4281105c0c0c2120701040c2007940781250000310b1400c82d440425204c1000390a100603107142003400d400c41d010843d800d581554031041c0c0c501090350280314080d01c0364400c0d259604070a400c02d50095130040c00b400d1450145240d1901c030f001240100c1c94036041070310240782c04c6480300c58000d85032010300316005c0c03c1f507058840441d480e0303108032498000e003c691b142106002001c0385c0d60340300c0c030550315028410f09490440007401440f11044540007003103990300162a15048403076010115101001ea03a1081c2c00050000750240320500e801243c080e003c160780305d13040300301c002880001902ca00c542042a00414500d032070800c55a04c40f00800001081c001342a40d4180c9004000035000d03250844d011a0000d1503e0808106c1070321030303180903241030501c0206081c5015045401c0e01c040e48050000c0c2d00a00c1625207000580e1030400090207406d514601515403145001c0c1041e00501c059000441c1c082600c50800c0040d0f0b92004001c42204c0d000d00e0300814403045810155020700c5442c1300038107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 621622733 1250 621621483 621621487
    0x506030108010509240f1005030a1110031505060a02070b0a03090510290406090c02030705071403030a030203340908010b0d0209090127030e0105030112080c070902 72
    0x400c41c0040d80b0880c46148038005a5010741700b0f0400d03501504004040b04030380c0c0102d0901045a0901c0040f0407a442a0300014800300b2070f0b200c400091425450101c01ca82e20f1000e04000030b85030070400200149d040c0d1901701800215210700c03069144010394040c070b5020b407001003600b1a100b482040203100800bc807080d8182e8640940703600a024203090f2005590600c40c0c07a07a10320a040301ca11481c00b140740d03808441d0034009078805041d1020000d81d00c50650050301d07600007103601c501e00e200e500c0f0008003a80045603101010320f481800d1281a40c000f0018030501d0201e2295910040103c0300c154405203001650b90740c80314804891090184a100507030711302d002805a003003400c000e8684d80d2410030303261940d219545146246c00d031b51044d0a03064002d90410008401410f21200729604918444d0011070841d51944540402420b00c50022600c01a0903444000341a00030100d030803408028607040340380d58100700204200d101101e4008014110018070500c0041f4284241c0002d049184010340d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 621623983 1250 621622733 621622739
    0x705040b0301022511090709050d060f0f0218090103080a200a030509031509071703070b07090302090705030705160f0c08031e0705070509130803090d0801060f020a060b030705060301 80
    0x6008044a44c4049582c001c1c4010207090b94589660018440d041c15614001e403d03082006102d800100c44c40201c80454a4203d1010300d4442ca000e5411070030800d8030016200c2c0a00c0c2c09010b040206441150301030780e006c0d0018004111454200c580403200c50070f00400b042c019a003500d80c021156a621440c40c00784070441c0003050ba21400a002000040b0103d82106c0f406c65266010a403065440c411103a111030002c2202d02061216984160354000a60f814400035840d002c010310f10896054000541c062014421464041890b60304102945046815460008401b41803440350640024031004918221000c001070802858250355009519920b013a666a070000d550b50001c010043c0b808410384003240d04030fa452800c0d03541c500c1c1c01900034032181d8a0b184c284000020003504034075004015070000e41c00324030072000460143c941000180503401ca0f111000380300001c180c0014003008540300c44003080542c001100304070700d9003069000450710020300010b0f207441a503601040d0485c10200c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 621625233 1250 621623983 621624037
    0x3050703060615020303060306011a0f0d0204060f020f10090c170d0e03010e060103080a090e09030c01050a0b01081f1805090d0804030804060b01020705060721110705040b030102 78
    0x80b108541030b006400420802229082c1d071a40401c80f81c0a40543c005001001000e56801c510800514120368080c504100036508d44c8050744180b81d1005166000181000201ea010648040d500b40c1071014000954039100300c0c5807151514a40d03010300707079207943d038250500500807a050000c000c4503850501c3c840d510138006032215194240c040106080700714940741c609040c0140707045801c0341d2020b403900760b0039a03071024410380007030200a0403c0000744c40407070001402a9405e011700c442d40000e40d12600880d807514207503500184090700e00f6042c10388034074081c0d8121201982051003c440c4828000580d00101c080c6181a030007401301c0003400b150840682001d40c072080c007541000f0181c81003a100030070305440c20581998000d00255030300700000c020464590000c490541c051040d00d08143d030b1100010702c6504843c50503181d642c50103164025840050104800d20429400c04e9800030442e00700342500c5594501c0b80d80e00a946580055086036000e43c111500045103030044041c40c5100d50b84 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 621626483 1250 621625233 621625241
    0x3020a0807052b1e060807030201050d0b092a190c0501090501050109060807120201020307230d121d120d060902031602121812030d050405030a09171002030c040305070306 75
    0x11020316052031130107100d10302c07445000344000d0312006401041e0305441e50740112450340c0081c1c1c1c00c0d03807020b50b1414172504a40d44c20705420b0084002d14212280350800081085090b91400203c070002002044800075400382102c010f14403081c2804d000d10f5115440c10114054a00e0b070340024069460803001141440305503005909807152a800c54080c140c84410140340030f01c101d034000c2d015038000d00505c0c2c006400640580a401d14407a007240d00c1d00a000c090618000e03101c1500740110380c6040024460702039510440084c01540380d000719082c8400254540c44d507460400100384040001171041029a8641240004195804c0b08555901d011981024001c41c03540203040140221401c040f04440c00e40143c0b0035650315284005000039500c0200a041c25000f904001d1901040c04480b039089002d118561045000710059590350403900c00082251402c0d0700b1170a012a00100040f041410001c0c0700e00b0303254803041006076680c40d0701c680e09031180150b0f40010014821524040208400350304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 621627733 1250 621626483 621626501
    0x150d02010323010f060903021c1407030f0209070f090302040f020c060a0b01141809040311030a020d0201110403080d020a0e100504060219020d030e130e07050a0603020a0807052b 78
    0xc031410194846408407511071b2144000f83d400650180302d448114980e07001c00c1c980c144116803150710901c110303d504d81840040c0e40159804001c80b0500302c10340c1807140c02c4a41c01241481c0c80f0704507503811080608060710602020307019a684140740e251141c103940c100d6100401441c01c031241e6103800300550018150300c14005000a12031445041080034410544140c911403140e0024a00c0ca281c0a002003690000c10540800450f01040c8000705000d000608840b003072507000e45002c4020b241c021303003900d0b840311001442c56010802080410980030545a0071481060050794540c40036000700c030f60a054500e8258400000320003000c00942100080c1300b242c1103602964900d004645240351780342201c81000c1e400410408050001034812070082d065130800500d83c0e46035404544404003150b110600025070340c0e1024070180954941208180e009003010314081d0726200d40420010b080960280000301401004141c0c070f810000490c100c4030054000070020786100c600310001070050030f4200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 621628983 1250 621627733 621627749
    0x1090f0c0c030f0e13020d0b0a051509030f07060909050a05060a03110103200a080a0e07050123210703110a0e010315060215070503150d0201032301 65
    0x2020214402805008404464900e500c0c0c960700400203803800d40b4144620b003541c4042210f0040e1009880e503c0c4c000021042200900050302c560702840603c0895110800842c03141c1d1101004201b140e0b1400d07200e40815503440c95131600e82c0036003c082494500780440b504082d0062000101d0000d27403003c480000c440411009105580f04da040503011a41c055910907080a0744003424004180c08071011102c52206140c00102c1c40b12400844900746180802201c4502d00043d001401c070398060480e03500074006880411100c0d140004030b941e10f605921849045c000034118518240b0400c0429024810000082070303a1404080100c941d4603454032031580042030f03070784003051a0034481c1c4221304d00c0d5134450441c14580a50f00030183d6600f0611049541015254040c0c4a150702542d02110020300d1107030014841c0200c604554003030000c009001000f045014010415080b0704d1083c2c680302020250b0300c3e4440c94005d4001200604400c1c020ba07110216840c141685414017001c3c110304951320a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 621630233 1250 621628983 621628991
    0x10810091806052e0323030c0604060c020c01020c0901031106040305010507031b05030702070b25060e0d1404060c39060315182a0e040504150e0f01060e0109 69
    0x2d12042d404d0889404054550300c04125210003801da040e0701010180d0b0a5411203090003080e0289a00c0e003001101e04840c801e8466055242c11030701088000c10b032910034000b0302820103014000c140c4c6641c05100203000c41c409a110840f943e15184100d178003030343d00180244034611700680b014014240003012644c3c040100c0c4111413107070744982e05403401521560f0140881a02d004010281a0001071880191482c0000c0c00030085e42c2001c1c4c8a00c500344121400b040003d43d445041d82003150240000342481840c0c01149420a450022036059510300e00300303544110322034141400134001281d0641c001001044a50130196075417101c02c8620f00c025021400c02c0b41c1c55650890642d00650080d04914401003810b0264440c05144c1d0f003404170700c2c010300065516402800c2540314180034048903101031a1441e44074203d0303100060500b040c40035101400b80d414242c0c0c80305c80d4040b4003944413a40942e211850080c1c00d0003071041000c1c1e428064028807a05807203800c0355154034000c0c4110b07480c4500d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 621631483 1250 621630233 621630301
    0x1b1b0b07030903021f080a0b010201110a080115020303040201090b25060e060106180608090a050d080a0b180703050601030603080c100f1a06033105010b01081009180605 74
    0x207079500c0d4171340700159617848200d13250b4200d03a0000c0e10054440074199500e8423081c503240c84200d000b9092040040d50b81d041c065160071200c20220200b11418421034108004000150b43c11030f40c2c04003190b407010380050b912024030109e1913800142d15240c50040d80c0600d0f140c41400800d40003002410b00f0a410354000da40d8800c0251000440e0707180c0c06070441202c440030001980500302d8244d004540e2019501c40448a5407410709250151200070003080892080c042002c0b9540700c0c3c015400c41c180d9201960444a42a0602ca26001404003040649031070004d04142d20a402c5580190f500408240d140c5000c200042d4440c101c8520302a80149880d141e0303014000e4a00031150150302c1d9100000704403a98009000c15680002c02d15019018030448200710702038941380b5144101040c0c60700494020461a086003544c0c2e0703034100c41c0e040010f1b400c184211201a81e21840480e2910070700025900c45405483c0507880034842d01130021490a0200166403201001d02e464442d41003032400142e0003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 621632733 1250 621631483 621631519
    0x70c021f08010512010e1204080f030307050d0f0f09080d1112010902090d0506010816080a1109150d08070201080f010b0f130302190e071b1b0b0703090302 68
    0x5010598400054070400100b150b03080016101186095803030000c140d50800040d00752070134070340108a480341c0d03800040801c0103642c04e012401d002c1c00c2c80005140341d4100040b00904e940140710310820030940c0d40e4161030100c00035a12044001030280c409101c6250035043c0034000c2c4c1c2040c0c00b080039250030071080c48184030f803900480b42d1011903450021202d07420103100c007009402412005800c000f9110010010540030069140201903040050030f0188441d0490351140c585503101c6040c40d400800c1a400141041143c00f41ea1442540c230700c0110744c0c89040e0415910103c1012a4112160070310340810f001d5604c00411486000703880c1c1c3d80325078540da408010940824420075009240601020064690800c02071821116844c803107002039480741c000401d1480c0403151944d400181c110104084016803582c240d102007a81807010740c80ca01d0002e2020090440d9000904030b034200008400d2aa1601c5d09100140c950010095210401e6141c05004800b45020a9220383d140a03c0e050000c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 621633983 1250 621632733 621632779
    0x10303031b270506071101020c040b0904260708132108031b0315030606060a140304080f0c03030106030e030403030c020108090f030307030f050105030a02310203070c02 74
    0x72280d07600260800d070660595110245040d20060800c103680c0001103555a09016280f2140600710000e0076003003440004e403511f600c482c260b0740180d040040382d41a0ba65249480342d07000760410803c0000e02c00c5c080c41e4410400007c040d2500320040411018140003000014000030001c6400b10441d05895803045010010301030f91503101c2d40c40c5c1342e9003600054258009550002403102c4000c44441c0090305403c00e6030004c50720642003141518070300810380360401800da0071a100740e600620b00f41c01e0100003003200e0905840c51f90b080c0c2000011501300184c002c00c0700d40c05450401419194051201c000d501d0f80d100f8450348000a0614a801c1008280402128200c070381c103803182810019207a00560b0b030404014003101880c081d403119101c00712824001544907440e29a0f0000c0c1b500f04d14094501110310681000780039074014001200180c4696500f0072403000004540090700d0890301101e54420f441c0080d80e08202c2c004402d11103029007000800e400d082c400c0741e06601c101c880100c595044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 621635233 1250 621633983 621634031
    0x6070e120f031e0c0304060305071d06040501030c0c020901170f011b0e030114010e1b0c1e0f010c180e101401050403020414060909071d0601170f01030303 68
    0x40e800812103140320b1003540490b0400f55220b510a5420803648007880350a41d0450703070001012a40301c4041094465000c25072411800031010302c0c1c4044a0b045010620502580c000c1d141450b036070359040b94680c2e000b942c110b411079034010281d41956071220054111101851803003d62841103008040e00318074180200002020900c5541c0850041414100c480030454040c26416558070040002d908420a2506018000390321458400b410404d65100001c00c41301c0804103100030500c43c0c0f500589011903800020309440010804050502b114242080c1c031040412070558a8401640e006070741095510b9880001c0c0f41d120101c055441844080c0c00208851407040640c0c01e90050001500031a00c2c1100c2c0390061500e5400d00d601c9a0208041f920003400f4081c240d010300c41040000d00e00140615481203142d0007500b0058035213046c0e24092036070404480805c1059400081a592080d03044004545581030340b44441e0410000030700d0b4000f030031701042d00000c0c1400740b241c0d81c039081c0043c91617135 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 621636483 1250 621635233 621635263
    0xc070e04030804020904020a0816080d0509010203040b0d111b060709081905030409141f051003020c01090c060c0317070905122e0e0a0209010306050a0e06070e12 71
    0xe0fa40e6a08100340013100130402c07030b4003529003032001c9200c0d4010881c4108414114660301c1969080c82e0880703191000105840041040030030103c000d03640d020003a5001c03601e5400b40c50380c5690040d001c1601602b212144d200b035601c801b0600e40654180c0d13001e98a0320907840401c0e94070766280d22100f248c3d80b0203a8000c03102039502503061050b061082d844950302990051003501e0a25071200304220580304401a5000d85414010910044100c240340e0102c51000e46880788918914160108140d42c03401881d00003450360126505050160030341203200b0040c1d0010044040a0f160384010300349400200e019400180310080b031858007403428480074059412600c8050030545801c00f040841116524800705600032501c1c140e044002040300c0c4034108010441100045051b0740c80c00f006c650151344101c1c0c2030b5000c6900a00981c46005a41d819681c010a0104040c1d80d41c14800004d004203070090040c500c50b210400002651042c0c803601d5000c02200c1c06c0c80031042c02e00807141d80769080c10507410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 621637733 1250 621636483 621636497
    0xd1407030f06150503151207211e05072115090201091710060305061f050d06090609150b030c040501030b0c07030908060f0a0509030c07180f02030c0c070e0403 70
    0x203960040c405554061035031602485816204004208502c80d5947c136100340c0e80c0300750018450808070000e021201c540030100340c1e01c0c414894a0b12140e8040301c6503522425002207114000380f0406111802c06400c01900d1078843d4901024ae40000041c40c4505403180c5c1c100c2e40c0007280c00e1401c1c0c041d2408041e0146d445201141c01d04102c0c1c1c109032640c445d5814540b250511100260607140102c03002180100064405854004001c406d03441001e1040c901d807090401041c0301542d501e9181607801038200c40300190070441c0d0302d4414000c04c1c03d604003900ca902d061103036032282040340d000035840c04016004d55508040300f50071301c41503802c203000080280019100062100b80200094003c0360b01034070b010321489a480080c5070070b259058a103480c2c0c00c0070303c208100c0c42038482d00400d608080104021841c0c105018038885d200e890380d0192030f0102d01400200322401010b03400c54800564040e60466890420f80b0402200758010802d03801d02d40600c180000312003d07444040e6100e6501615020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 621638983 1250 621637733 621637769
    0xa020103020901031e1d0607020604030f031d0d022a06030a0b0a0303031505010903050c150c01060f0302030c0105040e1612110d050c0306011d060d1407030f06 70
    0x2401a400c64404103040640d0b07200c1120742c034145800c1018040165020018200e1b07a100c119106c0c2c540c410902408070341c0150203210140f81c2c0040c1d01544190180340040260712030001c11009011a00c10368240031001301d0104007600700225640034111845d07004c464400342001081e070703440321000307826004c07218100620401034101180210b5001e051003400180c0c524110000991a038015001500041d648040c0c41c000a8200400100504001d0030210399640c0f1b5680c0e010340e120f121740d00d1280946020508501d0303c1008005680e4600e01e58030092081c541c03140310890781e05103e848180d00c24810304040388420750081c1c0c112419100f80c444201220341d50613200b203014000d1800e050040003250704801c2150071700c3c0d11400e812510750080856481303e00c1682481070b04c40182c1201038000c07042007401074070380e003028883c0b01905d407a20740c240d81c800760040018002d0180f150702211050600710305e42d04403048603902c4c0e4031070300c42c90302d0400c0003050541000045034068050f40c42c4e40b0703031540400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 621640233 1250 621638983 621638987
    0x60813170936010b120a180b04110301060b0409230c0c100b010927021812070b0d15120501091401050103020a140d210e090c1218060c19020f0a0201 65
    0xe46c04a01c400c00810f5422900c101c0d0301d03441d42481004d07641c0d191820144410026408070041d0b995a0403030082c01000e0401c4e40d19401d5106034460b00c41196510380000c0c0d0450400c03815444400e02000c4000103030f10b04001c2e520400d030312480c2140124020052000c801e101c0c2071245139040441030303480c411302c0c6081291000445030030313000000c4051035074a4100c0c000034103400140b080c00c08150114903c00f6a181c01d0001d80c00110b80034070115000f80c04240008041c002c00d580b62001d80c43c00105804074420382d11303400e000041d0440690032003250510030500005412050080e480307141054000c1d9810b10315903007214001c0c00000d5125404000421402960341c04040d00301c80014102c104083ea40d60b2650805000c2d00320945a0781600700680341c00341d4102c0100c040e809819605610145080071680206220781a0002c052000d4040401da140741002080c1c481c00c0b04013030031102c5c6800c1004a0159a401000003e440340040d0f100681d289807010035007200030b03610b180041049003000e07801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 621641483 1250 621640233 621640267
    0x30f0213030f1b12140303070e0411131706060111070326030a0b0f06090a031704120302073632010e01060813170936010b 54
    0x2c1a03414840010802490000d025007010052545003d0311040c4811440c000481d10486541040300b60818410846061b030020500060804201ca000440c6851241c61b030000c2c8c058500c12084130b0700d080c41c000c100c6000511f4a80002c000050072210716946d1400112500603210741e505030680c202460410000c1d034690300d00c01c0c01211140241c401540d40000c030100942086810118494072410800624203002001c420400b1058414501e000403400c04200d4a40d500d100090131019990b0400d403520740c034101600c0240400405406200406c1e0170020742d50b00003401040c42e040191071030b000389040c50030031401d0000c0d010b16460542c900000e4a40d4000d205006400c4a85456849091341d11003c14038024898000c2c56000e00392541442071045901c04141c00a40c140301c0c1e000d003400321050502000904045c1c0c0b2003503483c512041c0115410103030180409a036002616901d1514280381ca007044500140341520001c03001c032a20a4082181640a1040c4441c01e0b004000c0d0f0812060f00000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 621642733 1250 621641483 621641513
    0x60f061d0610020a060905150903090411193f0b0102030913020c0f0708070305060603010b060912030d020f0304030f2d0e12010209011d03060f06040e0a080406030f021303 75
    0x81c0c0780742e0020600b0401103c10100c86043c41608005408031a600c1c00e403240c441134020300c0300400c0c1898080c1d031040c0841c050807940c00d000e00c40314100340145848021401d3f4028650010700780c50540301a442c0c941021407a81e0f804042c242082c44010817548004103845c4094802003501100c4821229410001d512404011030180a140040700011808011804c02068060020042980303903040240c00c1840183c400c80c03283c0d040001048a580e507100903940c2d940011102c1201003e1070170740c2c0382d107540b1640010180550010849038036005400000d18492400307a15889490001104200c2d43c2914040d2141017078001a070513400c1040d030340d40420840ca00d003800c04a042e0540704000134411603201040c11996900000c0032a05944d00160860600c0c031002d071000400100240001d0300c0303403402082e108501c0618400208169107540111084140800a40744450030030700b40070003035511500520020a04101c0101c100f0a05171080f0396031039000c9290100c80c40d085036034144120038044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 621643983 1250 621642733 621642743
    0x3063803150408122502060112030807021c051803012003100e0901060302040c050406210f090c06080105010903080d09060213140f0109150c060f061d0610020a0609 72
    0x4891131080312002c0900078080c03a002006041d1a0703c0800b02c11034852081c2c4502011500710304010020800c4825002118030382c581000680795446c0702040740381c170092854401102050036245a55590000c00415943c0030b95008210901d18035000d15080e00e40999031004680041d200c80140c5c0da00f4080555003100c554198000e202e540c0b080b01400d2041b05540060341e50355900d40400840c40d151050080088041c1800c0e81481e00c1e0000c00380512954a1841c001402c12402e60b80e080e031a103900003200c0071848841000027400c0c50400304000b0701b0340d01810020410704030002c50b280d8014540f51044944c0300d458030f481e0800410400001c1c01c00b00808403080c3d074013440549140d056400f8070801401c642864a10060600030420a080052103000c81c1444408039090100b421903000c1c0305002c011034108002c11103164604480100320350b44200c0382c030364a4041c01140800050040fa03042c545452600820742e11a6010040c1e1200000c07000c40142c0e00c0560750100040303040c1c0010804600507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 621645233 1250 621643983 621643987
    0x402121c0302450f13050f010501030e030a110a02042d0c0c030e150c0d03051605040608100305060106080106020f0a020f060d0603063803150408 64
    0x1084008000d800980c03014404280c0200b40720701038041c01e405550100041c10401844080008400800c00441107140c034103038210140c0d22101d036190354056003800308001c2c0c81c0800c0d10014100c004010b001c29158080306001c1c030000000c1e030f903219000c0c84075035141c08009035191110383d010542c2d450903081c00103004c6009601000c0096601c82c40b8800b01700140010100b21520351aa0b23004c1c01180f41c080d2401d141d40340464140300c4d00d500c48146c003481503040c140204910442d00000d0409503140086c02d203100000a8a031420746004608036224001544050000342c84156407680072107540c144400000303509200800c11148645030141c0c2202c02c5005024555480e85c071914140b0401740c0010021590070001045a035504108801654000d20080c0074500000d90010340d03100c120214091041001103402101d812031540440015540302c1000c00501080c00b50503148044145620305240064500c280080e02d481c90109404c0c450041c082c00d04908443c140d004486d40c085c0050b214a002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 621646483 1250 621645233 621645253
    0x2011505190509090a050d0329010507051f0b0102060c0a0315031226100b030705160f020a0b03090709150b07030309061a0d020402030601021603150c05090306040212 73
    0xf00840320307000d600e0100c043c003000c0c8442d09103949403038040c59804040615000303a96032281240c1888001c1e0140f0941160b000011410040b100c074040d0642c0a030480c000d06071841d5200c100c1e0350183c01c2e002d08050342408118680001a178817244e0448590030701c4c02c4d0030840800064800d5001d05559902c810b50480d00c15101d84039031400c0344400388514042503c00130050ba244090800f20380c55031340b940da000d009a18082110f203c07030301800e1280c119a10301c04804118424020f4081e00c50714921032003076078100c3d40d150828000348131012600343c0c081c0c03a9001c4085908003c0000712440b521019004000040c90314610a008201004036150709062210300403c156920000500100b8001e0380c000c40d90401608020b01281c4a01250642e0031445c10ba10314003d44a40b2100c0f1032068040300c005880c0d64031840180c0c10000100e00e10200301001080120804c03040450010f003110020a04014182c2c0c051800d80cbc0314441d194549a26600010001d001481c0001d00301649200070001d4508982c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 621647733 1250 621646483 621646489
    0x50d02070f0b01060302130906151211070819050901050414030c040c032c0703150b0a0e07020f0a0b06190902030705090112050c0913023007020115051905 68
    0xb0080e0003150009400050813000c66001b0301d007001c05008d54007c200700d0b0a1900d161008550601d40400041c4040b649142e0854007030f40e4004400100301c1402107507205c06034900029a9807046286040b41c40410009280c01c61003081500c4080006071641440d01c0e0034030f8500c001e83c0c4200c41c0d0741641441405111080c0b40c540e8094041200d12545001c103d4241138060000000b440c107055075003280800d541100000000681c1a080303c0e008a0000122a2000311040142844000c2e058200342d001c08002141c5420303025152007055075030700740c41da42c207035040c40c8079101c03200004041c26110f640004900a8944505000c0da00c1480013006040141d036916000c050360022103820010070004a071a561070350304547c0001148418800c100003c0c5400c050218003030060103030035030007854884440c22600341507604484040600b0308010400301d201c001140c10000e41c04442c003900c0030110002c01d080301e00500803680c2c500581d0300c2c0102d11a0515003488480b41e8500a8080d000e160a8030010b0252 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 621648983 1250 621647733 621647753
    0x5030415050304060c020c030714031204030305030603070b04050a06030b030c0315162607050c10050105150a02060a0b0f04061203080c1305010f050c3a050d02070f 72
    0x9016441e080c1d01c0f8502424031100705d90a0098003400c5d900416002c0c0a50f42d0007107407540950300c258823018250428000802d00e0103114081c900c0380e600b0006030120916801c00051352240004404960b03550b070702c884402c42d085c000ea1080340d4001c10061f50a020103030003504140080000901140d03440141c01c4c000a01e450003040011140c090b211091020a0180c04207495521a80d810000300111529511001a0b03468400e000c06816a00c0c01250016100e10116004030003e130702107801a9400c5510580140000e00c58a48224842c1c45c4000c00d0b040780d4401c1c0d03460b500140c2c0140c15603a50300c143c00d901070401b240758242c0c003407140c4410b041030342c0c1d40384075450190200080c4005445180d01d805042030340044e1101c01034442c1070010303d410b080b6a2403903106813042880c00744403456165000381d40300d00078110000200e024031005406100b01100c902460b2200390007201640c21804601d43c5510341d001402000011801c101d214440768031034000300320251050248103568501500d49c0c004207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 621650233 1250 621648983 621649019
    0x2706160605011a0a091202010c0c0b2d03060108040305041703071203060e1302030106090507030b0a0b04120f08070b07080403081b031306110d020909010b031012050304 74
    0x5540d0300042c00f2940e00000c019020300640d50400e840e0070394403078000e403500c0118401c212050018004003000c6910415441700f807079500c00c402410141d11131803440d030140c00c80070348004c1054490140a0500f220300503101c854030310030000c03035103940c9840d001168200c00080090341401010400002c0d1600e950700c410b8103198280c006141ca0f64918070f0000445d0329540d00d0101014180702c024050081d01d042555042943c080c01690081c030640b0100e40540625801019030518010410640c02e416070080d8011070012558102c00c640c4590001106000c1c0e40221005043e031100c10340005039042c04c042c00300d02d019003041800d082d5156621060044100c540d0800642c1d1070040c442015048005103800c010600c50342c00c05025414103003102404010000380c80a1160791403403050050700c0d84002c06491290801c4c40d918040a0452000303036000054040c0245030340c400000c0c0d02c440300016280200c0e0107a41d07540e0b0681c0307002242540e0b21301003c070039186400204030008038581c09203040707491 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 621651483 1250 621650233 621650243
    0x60301031b0f0605041d04050c12010e24070c0b061201020403051002091206091504020f0909060601090e1306021e0423060a020606010f09031407090b010203270616 72
    0x1845c2c1c00c0050004990500600c0c8844085028080c00001a03010800c09107080058950034100301c64007024902400c03018a0800300382c0544115000e4041d0100c1004d460040011803020464452190032030b8007850095010f400b180341075002c0b603e1031a00c000c500403030050740780000d81003d4881d1100360614030001201e1101541c0080c155120341031443c9041c90241a84000e0043c3d45485109261140c0c00125102500e241400004046658410849900d44406420721405140c0740e0141c03a564003040d85d50034007013420003000080800480081c1841418045104d424001950703541001a40029100c409460310340c010310806103e0780d001400041002800c80c210610484400300c0300c00816460540c01003c04200e1b113040380b0b4000544070b400c6002849c02c0105603d054038200c030224100d8000801c002c80b1010346050001d400602032040d00c0c2d5074032040118100010040e81d0340d100d0010342060b2100754807c21300128920401c0000e00a1015002a140030040c0c0711940c94490340c0070007190 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 621652733 1250 621651483 621651487
    0x13060f0204080105060d030c030f12020a02060402030c06070222140c070303060b0403020904020904050f0106140f041b030c200d020d02010203010f0e06042703020f030702060301031b0f0605 83
    0x1202e40000d020300c80e042001641d08031100340954030000d102081c11100541403000b40c0200a451310302c0340a00a481800c41e080840d11184403000003501c4081c241c900b41c0c464810348003c179005241c24012580d8007503004250004c078917881b040c180440c8000e4080e94250a035558240c60f0700545aa00c0603105241d010381880c0d5564980ca4007408587c04c94001d901000010b001c01d20042c3c603441141e580140d01160301001694031031501d50310300b08142044034990750030880f0015100003483c9410442140460b0584802214401400200c800c441404070741030941520701c0c54003a010754010b1b241803403036180510b41c10102c0c185141c100ca626000c1e070427480e844400d50005981d4180f1103450b1000031440203520f10351416040c42d803286014001c0c4064101c4800c0810304554659009200b510f031211038040f0040107c84400000742c1c1e13450400d0b00503000b50300503014911400301c22203c1c0c256004003860304607401c40e160400c2461032103081304046842210045030864546d40d400740145002d81d9656 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 621653983 1250 621652733 621652739
    0x236030d0807080912090609040b1504050a0503010c051c27151103070311160b100e0402031c022506020106060e0a0e09161202100f0804060513060f0204 67
    0x70f02c2e00300010074400e09038110091002041810108030b800a82080320599198500400000d004184050f0003940c8500041c418005880e41304010340116002220140b03d0290380e101414244c500c070a0342e0500041042000c4044110300b01e0000181a50030407000135640526107481030108001e41a580141c011032905004200269001003640c0348028000d000300c46a4415031007603030102400080038103442e008200c05038101f04090ba0222601c2e070524202c66441400c056800c02820358108031003034448234010650780c5030190164040d81d405001032000c00b80071a0001d44010761000b440e0210f0046003c0c0107998495038550401441c0d17000000c146040c50408040d0842d01d0a52002040c030810740d0070b55419644014811017120140f607060b030301c41c0d91031280035400d0008108805441d2010440003003040500e418203410719a2082e1068141c0380740401090710304180c201c19030000105c0348000a800180300c2c0c0c0085410408404606141b054550f0f01c0d00d05641c0c1d214100203070340350302050030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 621655233 1250 621653983 621653987
    0x3010e0c070c060309120c0210081e0c0711030a0b010302060d091a060a090915020c0c1e01030f1a120f1e060c030717131a16030236030d0807 62
    0x100d0241d050908000034107c107181d0104010421440d000c00902605000090345000704440318a60441581c100e40304c0c40c9402200ca400981200d1810b40e180034601c48115041c1c200042c00c01c11154010580041582c41d50f4200003880d03100da600c03400c2d42621242048009003030354081050382d44035944050340901d0001c040c062803841d15800700f43c3c03d5003411461800304403116000c2500c1c90008030b000da0740d00a4a0501841d00e10818103140e041580909810b80e001d040404546a81034241d8041c0080e4421003404001d03145219900380a03500c110b43e00c0324203490550440020140e880e1300f0f031914642100d0951b4244040b0100f01c039802c1c04681303403191001304140030071940030400d40002c03819802c1c4664000c00d90b013560440b006c41090080c1c0400c0d17018421140d0601c05030f500c140840b6082c540d103540206186015540c1c081c0c0d266800715807400c1980a4001d40d441050b800a501c10384210f400c000e03100010140208081001030001d500040b0740301030109005591040d181c1c9403081c2410080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 621656483 1250 621655233 621655253
    0x10209130903031a1806040605030601060503041506150c06060b0f04261e0a021f0e0d11040f1d0109020901091b081f06020c040c09080303010e0c070c060309 69
    0x1e4800f50b2131161868070000c2d0b851000c556180110742c001010340e85e6a010110740208000e40103a035061051000000b040c0342c0c04001188100c1c400d003006c103010301040043d6130a480d00f0380208464a00043c00001c4200d02c02d00c284404c6074050310340840d0403560b400188040d98440c4101d0980000002020700c60620002e145552819894000381d4500c046c0c141d15680300c002c1c0f000c0042c1402c452403404c4400076410008011401e400070607418401e0001d900d03070f50903032440d4084140072688490000c0c071145031110640c480315400c528440c0c810f003c660104401070500d54060303c070650350780c0340340d0102540c20004044911525000000d803a8414010814032140c140e001052245c140100c0105d00280488060201d0400b070600300c1d441d03154081d0001c001011035001c0f41d11100c1401c40082c02d1603001840f480812000d407000c106002640d03d0807910380b4024054000180e008200402039000090422503000380c2c2d83c6001420320000f50784140341c10001e82e02200c0080e84856891042c4020044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 621657733 1250 621656483 621656501
    0x80c010e0f0d051c020a0b06040b22060b0c0705040b15090d1104020c1e0d1d03030c1204030507050d1e11030f0f100c1e0201020913090303 61
    0x203200c0048644400055058402220030038064a828480d02040140c00c1016070f02101d043c0403034844c0c4011045001390b80d507440d07030002d403040b1203104080342081c145031065003003801016061824010f0480501c140c09440d00c5140c9c080107039610400210240300e00d02801a607a6032401503d446440d2034200001c1d1003004050310f05c501040003481000300100c500310b030a03101c8181c07105019074009040000080281c500c16640082c00000d050100074004581c4401c00b15549600d01080e1115100b5150b4840c09200300c0008030b00c08a00303031a044588049640202e100c01400c07645403100c3e080305c41d42070040180c02645180000b03e41401001030500110f80603100c15078029520780c00503200d00e00e494685440422120003c01d00480510403191140a10340034090101c444000340320710603070384d2102241c00700e00c8240204140c604907901c00e40501d07213003808250b680500c01ca0030000f0034030600da11050140301351b40d42000100359030b458103403c601d405619030f03000140e01c0303a6a007805006d03540d0f188 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 621658983 1250 621657733 621657737
    0x2205070302031e0307060f0902040c0c051c021b1903080a080105031c0507030210021303020a0b0702060a1d030a0309080d0306030c3b071106061507031701060801080c01 74
    0x103140c11840c2c50010940d201140c06c1540410b03094141075a1000401504201941080c1003565803260300340c1000203491810310910454004188522040d8520300e42404054010b0b0840800b001c0030001c401400054014020140f808899075412904480d502507441214140404250581c450f034220390f80c9070041601394040e140c4802c5501e4185503a0400040714800d000740030406909140c420803000d4119041d40208664801502d0344101c3c101000d48400c901c2440c0e0f0b0380011440c01200c2d0142e0f8800c0398050704260814105202c1581c410b0354001c07126070107480000e405005564104040b110003802500c81614441c200906d01b800c20200f441d6520515040802c06c00010700240440c20465014208180702c1143c040008550802e0401c03007084401c010300c98900520400203421401413a00e5150300c506440010b800d151165012140d0320350215281503802d4a915012000f020b8003031103460540d40c51866403040c5500341078213800c034800041540006101e040d1080281c1c8142003424 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 621660233 1250 621658983 621659023
    0x9030f0f030501120602251113140a050c0c060a0c03060b0316051b07240908061306090203010203070e121203150114070305030604060e130308220507030203 69
    0x401801081304004440007490154001102c10184c49050701c00652125180f50090200015082468520104552031845a6081e039000301001000f407258504200444100c450a5681d0904030401044020441d003030319542007118140901c000d100052091168000000d240700501c10000e0072240b588d00720054040d8100203000141d40216100c50b000707025842e066590b8a0078035954021061401c0e03501c0300c01d10601c50003161075154091043c243ea0040020314000d80449034040b85c05c40307001d20696101c0e4200c400400c480c00e0f000809100200d00035800800e1031075240c2c0c003190032684101c0726000028804040d210b154501203441618080c0c0b110014a607024200c05882c42500c0080e0949444c0d65005844050a9000b0040540707003800101d05030381c40303007030500b805413082d481140c80d0340c490b6160080c04144040704581700d0703000e40b41c5074540c1200040903540581c1c0f05080078015507450039100b0010310041100690303540a02c0d1003400a0903a061461043c03624002c1c111132140603030116 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 621661483 1250 621660233 621660239
    0xc03090d1b0b07140403150f1112041e050c01030b011e03150b030f070e19060c0c0e0a0c021216150e010510150e240c0109030f0f030501 60
    0x1001d00030034056500035404005503210010196216410040e00600c898808a000810302051042c0003114545101040c0041d50143d0340d204210348030314000400100c420303c80391440c02d004003050b0360f1240c45040c418003024410810503410402e46e40b81202c06910541c1c0d21140ca513414003803002c400c103003801c0000c60015107021211005403504036050130550380d800129100780b0107010200c01006403114443e076904000a044941c29402c079614404900d03108401903180c1032880d0a8000c1c122540702c22003c0b2810320208071240c05030702c801035a0041100b107010a0808802c070310303a03010b003a0981d400200c3c17190a10019017070400c0c25280e059a01c0082c4070f402110850f20112254160780320b00818100c1449814080040003500d2540120350f182500b00688080700d941040c040d980e030040010310140440c4030841d000641f881c0d2190b04069040f80003100341c0b00c0080e0900c15600807100003030501a03590001030031241907071000d0b40040c48100044040e140c1204031400204403600e000e12031581 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 621662733 1250 621661483 621661517
    0x408011815020702271e0702070e0a090210030b0307090b0303190203071a0f09010c0909020f071410141b0906040816061d010804080a14030c03090d 65
    0x3400766014030741500090018210758a1408290a240000f541d014400c22501c20314000305404450171883e4548551040d00d828104542d100d109074216801810010304004e49001c0b81c1383c025000c100400e4a44408500580c0c4018119500c0c0c05c80d903400003501c00d4180e04151030000c40c0d600407603625191080d81500c07030310b000c822903140c0085280d0741c0c9448a9600000c9185116000c80078101d061740760b07a0403c5060a2141150080840095610031a100e14003000c1c00c941100500c000031482c80c9400304440d080c590058800c41c3d400300705190410b40706440f4111080096648042c0d244c04c43c00751034100b2a40c507c64081030020401000d6564900104072040c4d614a4072803249040c200440d29088664980085a019040e1501a0303280c0044d902401c2c159411103005e94008141d9001d5114003083c40e4241d00d0101810580d40d008951310386072521100c0c0ea006c0b1600404000c509031242043c0944803005501074152400301c0f942d80d150020007641802c0d07034610b0b50004c1003812203240201c48 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 621663983 1250 621662733 621662753
    0x60d0e210f0304110d061b030203220809030307050610080a0510090c03020a14010e09060a26060709090b030703030f112a090f060603070c0302012004080118 69
    0x8070068000950781d441d1402c04115801401500301d030304c8015a2414020080190040d4540310a0061408401c0600500136403c0e404203e035034121304400741510000800c2c0c0d803d40070101c00d01801400d85014000c2011a085074480d203c1503903203074090030134401440e4400038100001d1407140b0207801c5902c204d0b5202c41e112143c17004041c0c0b030b003600c0703030520b4040c0082e4424410045a00420003110b150303440e401921148100200c00380031400706041c10125003400001030f4440c1b1070052604480e41d091108101c0d6000342d1028544000f0f00b600d0824008100030481e050103040c154440c034200502e0440c0e5041aa078500540c00d000b900314450400c0040e410900d003000203070b0681444103a60b030f41c07440c8076464481040c0f6041c03400405400101d40c100e10801a2460720001624481d0040e0744080510013024005c0d00c000341c00c2201040010040f40c0f02c1c10b900c1c1c0d5064801e10000c10014501d0313000700707848000500000c000010000307003000f11003000d110b041420242c000410208002c0c0da140c41e074103d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 621665233 1250 621663983 621663997
    0x1140a020f4b011a010215060f060d020c0102030f0412090f0e0c090901180f0e0303060d03050d05012403140402011206090212040b070804120f03060302060d0e21 71
    0x40b003009044118002c00c000440d034244180b4038020000d26484014140402d42c4110203c0c0c0035000390313002808032910300c5000c5441060081c16005c0da212030314052040d29030201d05e0a6030484d07800d2040010164081c0000d50088811180c001e8150804d402c145414208200340c0e001071003411030342001049042c1000d2800c45041400f02c00c481e6a40c0c03611540140309069000c1d6004e0034000010980c9074415a90320041450380e00304010700d21092600301c003180d0b40e40c51a0126036005000003000392500c00000640c183c03180c501036050815890108043c0d8a0030b81000b0703000d00780044e9000c5610710400040710f0076440c0d850140900c00d41000000404140135001904100c200a00c100c0b41801580107100207001d00c2d2070445d0340d103150784901c407030354181500c003101d0a16008001c581210305c0341c44040d00440d00042e0318101d82d040814207540d02802c21100c40189512004000b01581d0b807103014040080800c030000c95062010483e05082c4a84490f03000c0d401001c0010b035640701801d01c03049d2110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 621666483 1250 621665233 621665323
    0x30605010806071b08090628091a0a09051305040302010507080601080f040203250f051206070513030c0608040507060306060e04020714031315030209060f0901140a020f 74
    0x854141741000c0803d8811003400c1c581003d030001c0c80224a84040000031407a28201302000c40c856600d060031981c2c0142441004014a00e100043c200f03200780c0786c001c014000060030441c4600e80d481000c64402000e0340941c40f00c0343d650703104102c10703d0f80a0048035403220300b5180c0040d05191100c0007a1104001514410300c00202d0300016045407010440620b19607128031400b001c000040820704003008150040b60208a18080000740034148210300d0192800c40700042c10040d907440e0380c1115507400058200c070106040e00300000101d1440816440a041565540061880c02c0c2c100306203040940c1d8031020030036180075820000d059200c842c103551b52104035000b41ea28801414107102410780d481c2410307058080002da007600b820755500100e045555400344bc074065010054190101c2c0104680f564015504015400740180c00c140100b91000d01410009a9144407541a01c85600402c51302c001603030090b9140800080200540441d0901d0f03100300540014a00c00e03100104100c070010440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 621667733 1250 621666483 621666527
    0x5011211030a0b090109020a050303030c04060c1502071a09060907060309030e1206040201091710090311120d0621061d0d1e0c02010e0f04150306020403060501080607 73
    0x303025034051160242c2d05800142964881c1400442e0500821007110102c0c81404041400196800c020054030b1080c045c401c2c6641c142450040c0660750f1068003001100c0390300010100d030660020b94400f4202d40c502541c1419101258651006460b20004d49109540d9010b602000003285000a145041c1c5500d8603000c11001d20318038068a119803100220303a4807a44c0e03c52032101402e400160b151045000340d0342c440c0740340d0b40d40003280c050700c004082c20080f035080102c424886105c26004868903d100c2c0c03600305510080056941d092098611556820600000c1c40e45141901402003030060a600d00700ca14859000c10405101ca9403202c4004000c0d54452009400c4c0d118119420007120030910144c50081a854030010708810884003a1500c10040d040302c042210701c80c032501103800c0c1c1d042c1c480000c0d40c581c401c00c01400b4100c01e0303c1c00340e0140d01c03440d40400719180d120308580254031400d00035849a040d03103001000c4e101c058000314420703031185081080082e48211400050b40808100706 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 621668983 1250 621667733 621667763
    0x5030105102c060d330e0f0618070c060b10021b06040e0903091806090a0519090c0f0605030403120b01090e0903070c1e090f0906180c0603050112 64
    0x18100d0042d550138680d940c4c40c0040e211300001000035903190014030790b030500800e1040c21511952440060080781400000c0030300050740000600c0e125038001100074001c104c450060700c03003040e0000f411150040050411610041082114021548450301c02c0747c99850002840400941c2d41c1003d0310741ca8034031034910060000c603480715070440e800750150404541c610300d80720b000240c0c0d0f0740c44040103601810700c0f000101c00030000a819280190001080e6a00586a501400002e810090a8070030541e02845640300c0070100c40c413500b0261440307124030640b2030749010001c00c0c2c8800c5070f40c04541449020000c00000039881200002c0082080500240c507405550040320400c150790080c4a82040343c030705014500c00000090f0040701d00c6101422240c81e102c0c1d00600744140b020175071400106c00c0c0541800003002d1a001441989100318001440e4642c81e00c1e400241c460000c61420b1032140440540b00b400403440180d00600503d05080c0000d51601e600f40a048104a401400c001006036240b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 621670233 1250 621668983 621668989
    0x41a030a0b04150e0906010302060a030c02010b0a080d0801150206060d030915090302031c0806011d0d0803100b04030203030a0530091908070b0405031905030105102c 73
    0x103003a03902000b510802520581c00c0340181d151105010f0360300d50f040810300103503518000241560590368080d010504090000c0402c2e409805000380f440195501d17601c4442590b103030741002100034903562006048650900a0240410790103800c040080402c030840a5501500020000d40045e03082c0d52800c00d20541c4e08040301e0110b0a80c20030210301038141e6054000340da101c00014140c0c4d008400790703203500303000540c440750701840c140c48034000c41c030000d0001758150b00440c010f521071040800040d1640d4465000150401c109103030840381003034040b0501030080c0c070303d040f1003018003035855403145801c1c19500081e6403805003002c10420400c0004d03400c4400c0c44094010384c030010304103c14614040ca82819600d80f010103c54604880c801d80c1424007106400054ac0d02c0640e4211a489207420302075100c5109000004200340c41522042004100c41d40d41c071402c3e9000030b8500d47e01d00e9120f5042000700421900000204000c002030217070780c5486448104902e4560a200f50210691f943d210004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 621671483 1250 621670233 621670241
    0x5010e13020d020a090608150103110c190303060f080303062b500f0312090d0e01080a050a0b0a030605010905070302030408070308041e11090c041a030a 67
    0x344032056400401c9141e0300340e2154000d002c080c0d1040d02c940365a80c2d158003040350340e61403c444024000d29030f00c03508440d65010364055085080b40045040c5401001540320346081420000910302c2899019a5001e141d89031281d14098455101030000e0140307060301c0c0a50b6800090806032154030500d00945200b40302c00080006000a000484241d02c07440c109481030700040c400c4503081c60304060005090010141d03280030b5220350641e0303030400042d501c2c0f070590a921300140d1004c100d104400d070300c075046801080075115244044003403456514004c44014184044105510188212102401000d030780140754194858000980015155982c7c84400068040d840341a034210008500200501c94190043c0d8140d507144e10041c00180c0310008110204d200c101c0d0302801228040c0006000a0f2089235100c1d00580240f5500210302c0601804401c4214000411208540d0301a81c10740582009800c0f00c2d03000101114940c02c05240528140340040302200751180720340d002000075500c1d8442e42c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 621672733 1250 621671483 621671509
    0x110102030d0c0806130216060e0f06040c150507080f0a2001020a170709030b1b13180b010e27010b09011b02060901030b01030920120c030705010e 64
    0x442800070356030b1003501801140c0280c80c003501403081c84103140d82444ea64002c403a00d14131a00502c03802c400307040c1c0310440240300483e100b90460290300c810b40380d82e64040182038041e500907401c0400c02860400024001840035000600b407000a10001010400044c203661256a2045000e40c0e51643c031380c070441d07030b409104004900341402080912080303c41580544a200300c2078807807005072008000c8070714054108503042da00083e80c4210500024050444c020340240705080b080248001140584086400c00000c0390140301c0d82d60030810400c04820203407440b18028240801c00030746070500081600010004180c01400005803020007940e094510580340006105000201d5860303c0c24212640c0c84054001d0002d45055060b802d040148040c251041707600401142c94000b5000065018000c0113034680c0c1410744e0b0700000c402041454000018008201c0c034405641000c103c00c0041408046000d2400c56110703a000c070410380c03000204c5c80d041e03400034245002076801c0b510014540e110200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 621673983 1250 621672733 621672757
    0x250801182a03050a0e19020d03050d0f09151505120a0206070615060816031d0a050a0302160302130911120105010e0601110d0e1203160b060a0806010311010203 70
    0x3010301d606442d41640900d029500c080002c2c03000d42e494000d41d65482c0b030340000840413444c075104c20340018035000025481592090502c0c600305007488410100701c4040c0f001c1d0181c456191ba050008100c00300a000e001980410070401c441010200c003903011001a00070036020f111402c0d100c0d19401c0d410040c1c05142c80e030003050035607a90494036010010741042e249940904085e400045052400761461034819280928910f510303000591044019100503c2e10710000b000b202100c00303070f50001340000b004041c050310003000050f446140091800c00c07010b050181c210711448082c8010b1b0b894840704c00b0041c55100c00800c1d8080d40b428002d0f06051290000f60b0b11800100c0e503841078100c19000366040b10a03120142d080d5a403805d006454a440f034070410348890700400c01111010380102c2c034044004101a1450b01180403405000d0b2642c1d0060400c040069184008142080310040085520010a0f141916264500014142d8821040c0401003100c2c617600001c3c1c0d1140d10800503140040000e07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 621675233 1250 621673983 621674051
    0x307060b030102131d0a0509060406020d0902100c0b0601051606050603070509090a140c06090d0c0b040b1b0f0d05070305121014030f1b060403050625080118 69
    0x10600f400ca000101700c0b9038252403c41d40d0000703800100b40e1042911805880001d0115582c9a64030b03000294002c1800d01c25450703039200c12402507100c07160105060343c800e03210001c805c1e4140c01d0842402100815050410a04210000c420324086000071400c0f0ba00c1780e40426aa00c8840020381018941d8000580101004007000402c0d00c0000d500c8203031a016054028402070b9010a40b6169030450402c0c94109404014802d85810f004804e0005140100b40144040d40c542c07440003950f6201d54062481d4034408101c0c0c0381c2c0d90903003203403822180035200000e0041034000d125080d01d07214041d442c0c00c10300c0408542042414003070f50407100003004441da094001c2c50840818003c80d00d050182251048108007650118140040c4034002d40c032152008100500048000c0745060a1140c40e090b0003031001d1200000003003007044058040c030030b1150344038090a0950410107d01c0802a042020805014010050002c0540d0380b0801221801801f04070400410781d5140641a401e600340003c200c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 621676483 1250 621675233 621675239
    0xc020c121e07031208070804200405040803010f0b12040303110c01020705060a0f2309010b0d0f11011403150d150603030e06091305090c03121903020a020307060b03010213 75
    0x110b107200550744180a6900e5102c1140811200c0b644200d0700c0c6008036001102040216094024110003588944859120b540c1100d011500b510800e540031103da40e0044014407501c40709100b900050819903407100e00b081e1032100705c007151407400b80c000f60500d40d6906c005441e0301c500720111041011100d00035580d074481494855654081200c50082c042d00c3c000303200641c90281d015201403800407200d001050070584502c080d80c21009000c50020359652501449151503070318010058074069082900342c0c036140d00705000c007500d03071070040e03810400045e40c1c50b00341002903000da80d00101071210480f1440309441c0230511903100c0c04400360112000c02400c0c090403081c1e0704101c00743ca100c2d542c0e9010300c01c00c641c207100315806012840d03a4043c44141d141c3c1c45110407a84074550000451040310007a1850b0f2003c0303420510303030050250044000007410031001c406403075007040c5060540340c118a044400300b0020744038040c8200040510b80c940d400304181d6036094068900c0d66603505003094005035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 621677733 1250 621676483 621676543
    0x1110607110714211905030904140601021011070602030132010c060209060d06081e0d08010510090801050106050a02160608070507051f0b0909010c020c12 68
    0x1124503059101885010800f194101654030100030b8010050001e01c2c1800003480d019050b40d0a1162200461244000c800041c00000c9004603403503014101035566a02150144000e555035415440c01e07042042c0d09002082e41d00081481084101b01e80c0050144074410180d1000d04c107103807001c0e113018008800490300480c07207240444803943d5101c0c0e943c5000c5a00d21445000e942c109401d50110b40410315400c00300b03049030021300d10000000c18103450b01d1440900c1d40d044031615040b4400c141c0c017034001c1e58602d076001003004143d41444401000b8007500144d00900b041c1c4140503841c01074501c400c5a0400038004d040c604040e00c180c40003406190384885005140d5005a40c1250042c455001d440c0e002d04018041d030741c00d031813803565000c14691300e001d010b0340e6507400b800d4211807511924081090030350242c0d10b40310300c40f07545400c00f0905040c010100078a045024201100e01d91600b00b070f81d035155030000380b400ca29002c240c1d9081040154a034200e401c00d4503110841c941e000d092910391050b14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 621678983 1250 621677733 621677747
    0x15091507052a120606091f1701050720060601030c021501080f10020f04050118090213090b030c0d0311070f08070302041407051c02071a2a031501110607 67
    0x1035081d01c41d5144042d42d405072654813507096035410341155100c8042000d003503139410302440040302c1002c0420115030703c141e0850380300701c01c0c032280030140d40d07a00c00d101d08107600c03c10000080d080c60319004c0d0001141e1100769101c240280240d0b05042d0744100c4070700c0c1c4a000303116401000c00d00c000c1911031581d40d284856110400f06a40e04003038002c00c075014241002501c2600e403814a110109410141080c3c015519441620703104101410103070740000c1c070420903000424412001c41c00d41b00c5120728158241d81642d60040c0c070980300360841c00c1074140a803141c2040340201034046c503100540014541c2c44a0a000d465008a00824040c0c60081189000041d8001c103c80c400e4408100311001c20350800102a0203a600c20009841000801c483c0c2c1e481d440011300d040d4105c0801417420f5029943d06c1c140d0383c010b1242141900341d020400c1003002c14810034001d20600c0d11514849505441203500540c8001080e400620700c15000c007a000d039210310200d0322492002411142542803040c4054101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 621680233 1250 621678983 621679063
    0x1309060603150c271e21021c0204061805090d090e04080a211508030f0a08090a06020a0c050c0d02060304120e060f07021509150705 58
    0x41c4401c0c02240720505414410081c5104450340c075040192aa02061040f80003001803113140280b0305400480d44100c4201d4512010020549101c001490300d84142a42c1c0b0551605011450500300c58401689888a400310b10140020141030b06ca80d0901c001401010320741c0200750340c0b406c0480a900312040f2640914050f843c80c0b02202c0b04101545811504400c0d00c0c0582d00078503a200f4003080000b004c2c00d02401083c0d009050254400340d403600140e992036400c03840c8c5007031503031900500c02c0b10b00504074205001d0070313010019500d0701482401c1241184180902002001010000500b07040414443c003140d05501c14411b550340d034921040240070b10b07060007060b900da0282040c1c000040c544482c0c41c11503182e001d030919003180d0300c0f904c4010000b00950f00c048140060040c505410b9500c2c00028410701d0180300200b40c0300e01d0240180021420189100c0031080c1081014818903070781c80a40c0785071030802e480303529610a540e20f06a800e00c42c10030045014091340c660745070f84210103940c0703103170342 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 621681483 1250 621680233 621680243
    0x3060111030a02011505040207050703170c03030f010e10140609060c01060303030c080f04050c0d0f050d05040603060e010e0c1303150531060221010f08011d03090d021309060603 78
    0x10b517030f07240c1c1c0c100022445042d4009001c1d40c080705e81000040c100b82c100016400a110b00e43c0d0a080d02001e2280c2541d00071503003a4503008880e00103100410300c05503010380190910740205421401d01c282c0f03d03190703105a00041c2c411030340401d4802c000e5464508907030820801800031b00c0065070307900c1d0180c042d0200780c0c0840b0202c1d114000180312801d10307421083c4500d8100005240c4001c42c1010301c44003500b072410640d405402c0c60306080c0403410801090307003400c00680d51165650301d002802000c803401900710711800021600108103400c0c0602c03000c0e4025402000c0c440d9540b0300e000c2521402d50296000610301e6803200c4107101001003e500152280080520b00000110f401c00004c01040014060903910b02e554900c07600462002c0d4090400ca42050900705148131010b00040d02e8400c09a100c000c15010981080c44034070b40c20f001c0d1503107001c0c0340c0c08965a41c07820100869124010f10034401d0044504d07201e46d106568408410855071416075000b0480c0848030304001001d40740724002564 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 621682733 1250 621681483 621681521
    0x1a010219030f03050c0405060307110d020a0b0609060111070b2104050a060f0f0f0509010b01020a02090a09031e0c3c050109051c0311090a03030503060111030a0201 72
    0x1455112014180a41580c50b80d594600c81c040503100f41e00500e00604106005403060102103004e4a80c40c00842c060b04040d203482511101c444d000b2031038400c0c165158811500b11041400000b140d0003102030300f00310708445c081c8055a602004075207a03850a41215000d10854100107001e1100900900000b001d400701103101071140d000c480c590440c10346008144d680003040e60742c0441e000d680010000307014543c0c01310b030034034040e40390f442600d40904210300e03181d81d07510602100d11800d06c42c1c28449402030010b0403590a050f00011100840181480c200d1620341422400f050300c106940041324192000e004100380c0302100041c000707000606c00304c80080101c10f48855942d0001c0500d0030012151403000381d05040205000700d0524924411900c1e592a00380d0440000c0301401b5502107a1040d170411910300d0002e0100505407400c80300003840000e0b04000e07081c3e40e52200101001520b40605040e540c035220300e07004807a10010b071642d00e4400d00001c42c80b008000d80c103400034201c8500480341c41c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 621683983 1250 621682733 621682753
    0x13090b190f170a0b0106050309011508010c030513020105041a0c01090c03050f010b090c070f020301111903020406020309010804030c0203100617030f0403023d030c0c021305060a091a0102 82
    0x76950343c5410501610004483c0c00421641d8031070402198056010000401d8031401180305080c0080c3c0ca410151440c3d4481c8011400c1030fa140c481d055000001090b044168000c640010b800c0344540d0140e42056420902c004405071010382c03c9400802040000b007000f1000c0d401c1000355803100f030200300d402d4010442003280050050190400313605e001003030080e80c0d48503041c803114a03a0012004454080c030101520015907000c2c032500181c00d01d1110480c0d6110a043c00d070940440c902d120000c00d061060105011540c2d0000a44807502020b00b00107086494508041c4c698112241c0b00952502c40c83ca200c16999416400000490304170030f00340029072041c00d0280d40c680c01044120204030398103000800261030001c40192414051000841e815400b0000d1840d41c030254403900007018048594203400c4940c548103804014610785449203900e62a0380c00150212854400b0070034654803100401c03e182c2c0c4840b000d00c010621041e080202507500b070001c03000391013403a41c01805401944560 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 621685233 1250 621683983 621684029
    0xd1805040902011710050108060f3003040e0610020d02060a0f020d020307210c0203070f0804050a030f05060c0a120903031e1505030a020117130f030203090406060513090b190f 77
    0x954014400bc0c411000c04600310b001c021019485d00500403880740b8055aa140320000b40001d0020344a034080a01c01c0e0702e481070502c03030703007223081080c400855010f02c001c0300c440d65000c1189900404075000c081000545000d01034080d005901c040840c0324800024030100c550000c0704040c0500e40c0e1030600c003074418510045401c4941002c40140035070020000540041c0c07859014101c114030502880c6d00305030f122008501c0b004e04641048a003c200301010b0010301c01c00300501c681c002840d808007841c0202c0040000d0003c0e084641c0e40190540700ca00882c00c040c001d8204142d00c0b90300c0341c2c1100c511511750000c42c016192040012012400c030003404155801c0100e146040e01d074040c0c41ea0315868444c201c10901d8888010f0101b107002a626900e64002491410301d194450300a038001e5071140090380c00c2104417441c9a119a048c09001c100c90303a40f41e038100d04000204d03040c01000017000d00c042d80114003942981d660744030349080751080101d0000115841141130700c03503002451107042c40803070074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 621686483 1250 621685233 621685249
    0x90203150109051009030f02120d0c0c08061b13090507090302150708030c1639080d0c080715150605090a150e03010c0e030d180504090201171005010806 67
    0x8020024600060501c0070808401c0c0015140744052701c1c0d10980c82032030022134108610f0200a40000e40c455084005006408228401500e0030740d0183c2220308240401d070140c600004560074080001180b00102840351589400041041c0003090040c3e02d02a40c00500104e45404201d115001407040040300e00042010360381c0240d40142e42e41d240d80c032500d921548a410414400850744000e00c89400090b5200c070544041700010411048190810240c0b40c11024250401c5920403004a03070410141c50b00140b09416032100e420008850140c5044c41030441c03041040c0644902107014208006041e00d922420800998207a40e0030a5500d07140110b48600c280d8840d254403003c45003080c001010481441c0001c9036030350801440407445480481d080d100441c403080003003035a260407000681000d009410035001e00d40340c80300c000b09240264070b06036005401498055503a95034a0400c590007048503040342000200c1070701c4549001000c200e03510302e42d40a0305d4001503405007c42d0880c10b24140d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 621687733 1250 621686483 621686509
    0x10c050304150e030c0f0303061c030e0105030901111b190308041203020d0504030e010f140f0a0309020d0c0906090204081005040809210f070608071809020315010905 73
    0x240c0341c5480000030b0310001512008510a00c18001048001c583c4c02d010001d503250140d21344091510791400e0303410019480c4007c22402c500d410343c1443d00f8002035008061082505090078001d840381c0701e0703d05080c010001c844c0e00c1d02c003c0100160b882401e501d110030540340c0c01703210f6048402074420921081d8854000700300043c0821907000100300021100da5524082d50064070b0010706008060501c0003d8900560b000d4020038000c4100715001d5078030119007090075013181012840402d0910900300640320b100b00c1304040003004514041c0c402e02c260400303200d46800070a2814946240d0400c001c01c10f2062281101d070914040d00003400f0200d5000769000c442c502401391031800c2802164502030500104126062070040002004030341d40d03050640041c0c1c00242e0b01c00b003062504c00600d0316040941b4444001c1d5807060000f0007046500c2050107511100d20700c0d00c43c000c401c5982030400c40c00e4440c1c010b0a103242c000f04c04c008024120014000c81c924090f0388a0b08029510340c1840111601d9031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 621688983 1250 621687733 621687743
    0xa1b09091407240c03020c0901120c060504051305131208100e1003030c03090e0109020702010909020711010c170712020138060c15040302100204060f080601030e1509010c050304 78
    0x105501d49114004c64009990501a0056541d40c400410010f42d40103000d0b0031010784101607101d481c0c24801060042c1014001904256280034100400601805c0440c20491085600e485c001061402038042c007440c10359201c0340c80010110795110103021600201d030380060003811503200044001d02c10220500170f2142e0070300200c0203410342d141102d502c000ca40040e410320141c180001540c007112202d00340200340640c801a250f01ea58800100344059980c840011580144504c80210300d82c8030107801852000d00709820241d4046c50301405445420581044400c030208102e014481e0421800c808420350354020048110041d03410340c3c0d004100e0206000c0c5940144004140404000340031425000041410b030400307610441031403030000d80c07854004007850101c0038002055010800c4103012010002c1c11b40c101400c0620003810218600c410600300160b4101065035070340264070020702c2c0c0300301d1000d84a42c00c0c103010f5425566482510480780c550700e46828a41460b100c4c80c00c5d02d004960003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 621690233 1250 621688983 621689039
    0x21603020111010e0a060b0f03070e34020106090605010c0c0b0c070504060312170906040f030c05241812070203030c07080d090f080a1b09091407 64
    0x540046078440301e00150100030b903503200320a040d03404c410001031110a204040100701141d554040c400c0300c1a1480280c0c3c041e6000703440601c640030380c10602070303808007240302c205048642d00c000000c00d050320341051803104901d0508607070b1303a541c1c19080f0320b0980749100c2c01408401d940300c004462880031140003070000e25410700e09102d083e5200300145a640090703800c6809854981e8001070440b083c80d40b0484030700f04001c5032202c610341c1081100400024140c5404910324140705003a860b0140103000500c18520080c07844205030145c644a420790b0f41110850b9001e03051428001c0d40d21042024500e880080e1000040005080442d5030788000d0b1110017414910f164003030b01014a41203234104a80c140400d20004000003000c0000500030141100200b4446c6520b01c4050000b0009820032b68510060742001d001d01d6100040c202c000c070b54405181d86801c1d5a1034000500800d040c0c02c192402800c1071015030510000760310022441e02400c055403a40c9650752447c1d00420650301c1400491101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 621691483 1250 621690233 621690239
    0x90610060c0b25020a050105070507030516022209212a1407090b040209060301180609020f091309030e15040902040e04120311091207030b0f06100216 66
    0x3540c0c02d03075801c2900c0c0c441c0c1c5845003444603a400540d6050b03004150041e0301c003138090018842c01340100313a0440301c2410601d00d040f119480050044c40307041c80303a0038549440f040d02011074071201c0d075a40032041c040c008801070701b081c0c241c6c1a0141620000c00d480f0001014606420b00e14014501c589078001500d40114041034594100300884140c40d00d964200705030413001c0d000c1000e6065503020b800b02c0c01d000d000c90605184003201159040e103801e5008520600c42e40b55161103400071a8151400e96000041000806001d44041c1c11540c00a007811400810b07041e01e001040000382548500484e4604403002201039814200c0308000001340001700096100c0300503003000c2c03000070141c030003883c0c00a18054881c02e191090340e01a61161500e41290001c100610040301400152a00c0034902803000741c108a031070700101d01410f145203204600d105008010f0381000c00031a001186d02c09036078009854078042d04420b0003021541d01c7e00800605c1c00031f22440d171020603c880b040d00130074044200503003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 621692733 1250 621691483 621691493
    0xb0105031302130510051903170c0f100c0201110331080301140a1d180c130f1d0304060309081218011a090103170f03010b03090610060c 60
    0xc0701402682c2040300024210301e2000c490050b02d03c03030301168107a048694584030074031200100c0320981da40301000c84c0302c2c2480040c803d010304c45400495400c0c0251503e0010900d103060058100c0c1000091250741411108943c00e900001e220400f00e4008029030900545400404d1100316107160358031308040c3e1001558000f40902e4082d10415000715100111240d0f1010440d50081c0c000310703003940a2004401c030b0351400c101010b01034200b40d1209806041010610404458040d2000d80f090b00b05a04400d001c440401c000c1e90b140900030414044650340c800c21200804441002108032810242c00036031030003d0207460808140824020342c6800e140c40d004600a0a01102c104d807000b40c10045061080c0056030090301488030460700c01c500d90000c100392030031a000e44c00b140384026001e0061015a0380c1f554641411070382c04c5041071000d0132001d800514903100c3c0c1c40c6581019100800082051036070100514403e0720100119545919030060301080c06526210301c40c0040c0d0401c040100040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 621693983 1250 621692733 621692761
    0xd0f090306090f0c090203160507050613140d180911190e09090f0c10090b030a0f021603090806280f0e0c040b0d030e06181003060611010b010503 64
    0x35000d8100860010701981e600e803aa040650b00800c285900072060003a680798a1148001416427420a10318060705542d034151102c070001e09003101040200901420722800621400c0d168286005032040141500d4002d0900b500150480c14104006840818005024807400e000c2d08108192181811031240c4100354030074407808010104041030740c2006054a802d60380070701501c40a00980840243d004160b0710b00046040c0c200d12031b42504d03803d0031a07980c001d40c40606840020048654039541d0144110141006100410b1401d20014213400e0351240c011010304094880c0c0d0b281c0415641e940c81e400d030760380b505440e081e110000c0c07242c0d840019403501c410064802104200810010240782654013110420f070b0030082590400001d2025a1070184141401000102e42840094402c0e4070000e020110440c0e40901a000001d1504200c20aa030100c3e55a200000e0490481410058004014184610401c400304032a44900c004020701809031224214040c0e450906551394444484209 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 621695233 1250 621693983 621694001
    0x30c0619020f0f0a0e18060409081605010b090f0412030e0a0204050a0b01172e090e0a03030f020c060c0a1101050f090c010801230a05060c010e0d0f090306 68
    0x3035a800c200e041c8004a848020b043e14840340712080380c490141c46030182c0000e2921402612508070003005a1411003e0500030360008400e560002e0310182a2921501904c149006031001540d07428414042107415048900c0500040c0e500c90140e40b20000c2c40520f00c101a1402840c106441140c901094825400f100c84100d901003200d008035449e401040458906540c1c5c040c01c0360f01c5d5500d10b142c84d60481550990088080c085a046203070415810446502040e50082405426420a140340c1c0ca00d001c0080903045510003040003000c2c800b4125522000500c08070007081c2851302c00b07218504c540c429074404003404e002501c01a84c505081ca41c89131304c40c007140707401d11541007055042c0180034440c1c2803044001240c1c008003418004011883e0140c0c102240341040801e00060003030500d4103101d45142200151500325140c0c0c51030014070300e0100c07a00916004400859084043c410540025118501c000150b03614a080d11a0855071034603460a0300c0089149400b0410000d50254424152 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 621696483 1250 621695233 621695281
    0x1d070501030b0a051008100b070201051e120c0301033c060e0304170f030a140906070209070c210c0f110405010617150a0b07060608010f0903090503030c06 68
    0x6075588440002d03000000e0a881880014021802c002c003400341c1f000301c0c2e405003010b295440d0030b004540d80002c016109002d030359400c00b0303907811100d00c0085024081e070311a200080354201c45842e04400c0b140c09a0803d200541d071500ca41c1089188550f03062844281030f0110409a0310040078a2500405540c9140000c48003150348800c41310781d8100c00e0000e007018150803081c950062540c1d03003803145018003200c1180140c2e0402c1042004085d080710000c0d000100c1c07201c000d61141c2c0c9890004e0414050ba90010790414242402c110713a85910400705c02c40c06101c1e00c0c0b07610152012054034030032942c580a40d500400d041254010104500e4884104c409110741541d81c070781282c3c0000f140a9075070a078800400b0425451488000c40d1400c80c0095001040b16642c0c3c003240007402c0020300b220b41e81d106401c000840080c030003003848610303049400501078040007803040d1200c003e260401055801400e40010b2614000031a1510f00401150b0180384210f0046c1080c0d00da900400c00c03207048507903190035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 621697733 1250 621696483 621696499
    0x403020f0f0a06230c1515040203070504091d03030114030f0a030c0209090105070c060207060e0109110f01020f06161b0b070e0301180b1906181d070501030b 69
    0x21503580b030700d480c8006001960340344005607411429040e5103c107007608039600c00c901030180182c841e0002800c0880c07000c0300342460190340c8a00040a030310654550100d80c10500001c200700e08503401000a00c2124410f0408100d001030070703a80c0058900103080361000c103400030001085079110042003030341442c00050030b541011030340c40b686518080314200e003100490300781804c10301546001400720350700c6048d00c40207010a241400d03000301380d215031800041140754041040390500419502549400301210300030050307540c2c0d030b04001a00d035030f142071003d01c02c00315420780f524954401f09548080e5074a9800401003070712152003001c0c03c10b000320400300800004102d0901800c00c041080c0715003900a00f003179081070508180040c650066084c2c40744c02a8108007240190302200700070724041d01d4201498613025100d44000b460103651070002041c0311410242c010030000c19841000032006030891003003100d080702204031071001c440d04d02c0c42d02c66600094002c01c075550003030b0007082d2050030082c503802c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 621698983 1250 621697733 621697759
    0x603160b1b03040905060405180d0f173102150705120a11011404080304030c150603030e040b0301050106231b010e0c120d0302130321090e010b0403020f 67
    0xa00e150800d0b8880c42c041505d4a0501202d8246445540d8100c202c118120b01406540c0040c10ba440c02050002c1c420811481000303603142d0b10075000002001002e80c050003030303824048410443c0c80610b170151200d0410f28104003101e9190940324010ba240d01810000703036000c010122800c030313800000c0d040d1064001e00c8120344022880000401002840340c50304410000208180f500710340e1110b110500c101241418030001c1450f031420707a0382c4541d0602d800d50001c00146814103a045c14000344044643c10b01f0f00100416800403420100d5100036641000072040c0582014244d032000c0c4248004281c128120009010b154801d6040fa5480c54020314a1b0000680000c02c500310410200c0d403283c0d66070207029408000600250f0b81584003154407103003000d41415031030f4546070500001000d04d907001400e0f02070000c0440305240110f4000c0300010310441190001100c40200303601c0e180000f10848400320728015014015070688080e01d1240e420241950300380b002079440b0405495011000d1b600306 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 621700233 1250 621698983 621699037
    0x20409020705030a030f0507050d090f0c08030d1506230715091406041101180b04080102040303020d03020a094506081b090403170106090e0603160b 65
    0x1c0070810321031002142c0d54584242c0040c100d5003c0c5040240a9040c2802d000c0e00b01da101080c1d40c60380030103600c0054034000b21300d0850380e0319110050052005c5c000e4a40090002e1707001c030260810155a41c41400008a0650f0f60f0903100c40d0f901a400200b85280ba003031001092200c40d204054080707204252828241da01e41d00780056109a00345060b0303460700880010014120750024900c0c490740000c10650420703a0b5042800068924018100b11741b5000c82e814041c50002c240005007050980b4580e195140c204c0381c0c1c007030f41c445d002c1038001d4441e070307a0109043c520074804ca03901603860307070b54204043d41040d003c0612104200002846001c07025003a020700310707031a820800c1c043e404458404108060040f06002d8609076070049009402200519400343c5542e0394800484104482d4440130356140d140661701a06036811440e82c0d60006400841c3e9260012812415074955840b400c1c400d0751350704201075841564000c0d05030018075a80d81000300c094403001420741d4101c1c0c042c414103403020210070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 621701483 1250 621700233 621700237
    0x1090e221407031104090309030b06041103010803090f01080903090405042406050411090a03120903050a030c03021501180b0a081906140402030d0f18120201020c090714030a02040902 80
    0x24400442e00204420820010091980000d05100366420b1100000135280503100c89801d10018008461300000171700a82d944d03500082c000845401520b880cad5848038a840d54035000b1862680c02480c40c00c0b0010045d42c01150301c0343c400c1082800440c42e045640003071001a142c080c2046400c082280000c05c2c0c5481c204580a4007070000080c00641f162070042000140c2e45041c0580b80151002c00000388107464000207041542e401034003400000040b00c0e022281510141d20203480c40c081c0f0040101056480340c1880b42040c065400c0380d10f007a0001c08600b640b105c0078131600b140000200301c2c208002c185174002000a00c0001c10302103580e669850600d080820000c0c05540002c04400d515040103032a00c00c0e4a07140090107060f1080d40303000e9012a540318120311403c42402200344012031418071600ca10a88480c401340003007007290b0f5070000c80002c1803001c2000c90144c010040343d1142c0e800e014168510400d255900d10b401021401d6551040d5480586400c0c20140c007004003045032001800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 621702733 1250 621701483 621701513
    0x80c0a27081f150b340201091a0a0e0f0a030f060501080304060f1b080417071208040b03090a0204061805091209121606020706020607050c06150414010f060e01090e22 73
    0x11001e5091103243c40010008c0c07020b0740002d0508940d0f040d0100d10304090308280c0d0000305030f90402c580c4030480b5a00081c0d0208007100003940c00f40083c50048100040c8000007a105442000d05011a03600c43c2c00860b22070003180614000a1031502d040140c189c8a520100d0038000ea5511004030b03a6082e407280c410b01d07401798018401800320911a46244501000860020b040d24192105280a1076482120b40c0c89a482909641040070001c40c5000c070003805107503d0103034024400c0059541d00c94007003019015080700c01c600300d407800c0c00094603c400810301003141021070f1100307440c101c14542040740e603081040808207544540400d04c00724040241441c009090b403600180721507031403d04001d141410080017101009028004040d41080000301140c11000b10700c400c4901b0840040414003c1c82a42d40c200c0f000080d060000802e6000c2016a13400d40303c160b40c981070002e00305801551900c40c903204203000c26114030005030341ca001c4d000d501041040e02c001806a88000d5032a10784c04040004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 621703983 1250 621702733 621702817
    0x510050d020d1a01020d03090b0c0f0c071203142b0902060f03010e0c040e01030308131209050a06050c1005040816051c080c0a27081f150b 61
    0xc104030f0501d6804201c4103e912080d85000d10214026a952583d5120007900201c0010004100310181c241400d043d0381e0641c0c01d41044520565440c074800408030306040b4280d022803080701c080505903200c281241c074042100216036102c2101844008100c1d0821950014141c0e6180013007401a500c240c01404054804000507840f0f5060914019500401801c055000e0f042080100f00001d140181c260449816051105130b03680e443d00e156258400204005104001811102102c9504951361400756282521664845a150042612a0312a04900740b0190b8412101e410024840c0d8001030b900030300c10489181821020340b0710484101c180901268260054003a4640114034440e29070741c01301e16440c2441e040d0400c40001d803d1481034141d86800c00896842ca02507c01c03c1a440d200b40350303003400a00450300d82c2c6101a07510b540b04001d9484c620010040c0b40326165442c0d0265010b040030414605080d83e00e8145c402a5a600200c452980d441c0c022038218040d010403140c94100c15030b54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 621705233 1250 621703983 621704021
    0x70b070e01050a0e0307150507060b0d02090a050a060f270e072d0f0905130b0406181220030c03221d0901051e0115030f0218010f090510050d020d 64
    0x6281c0b25060310307800e4a11500900842119030094ed6603602c803581c2012541c0000281c98440c80c0c0b082c3d0143c00b464100d14030300d1500400000d103200210b13810100e0401e004004414105a082080c829600c1030841041c040d840403c00340709902c122006e01c0350401050150201243d156090111080c0c91070703114520269007034200300179494050107500d03070041c100a00c01c1e0000000da50396902494001d84090300d09665003454501040c0c0003802100e0385900080000c43c003070800800201522182c590036490102811280b02514000100381c5d00084600c0c0083c50529041d05000800344110703000300c407118008400b00260a03540d1080c0000d440504088949061a0450a0720f00390341e4050b2244440f002410700d01e50095074281007103410354003001c9080326503014084088026100b1015034001807480041d0172010362150b003088644202080e05d03036458284070310030281c4514545208050f0098000c01e0f0111304d081c4514014100c1c4c0440700ea006081c014080c1c03e1300c1c101c412000c0d50050000d18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 621706483 1250 621705233 621705247
    0x8090319020309192912060301021e03100e01030515101206050a0b0f0f060901020a05100608060c03010e0115030e01020a0f03150b0904051515070b070e01050a0e03071505 75
    0x1010481c0043c240007880e10010005681c3c0e0161962003030315011b40074424040082807203541c0a4040303400f4942c0c80402500c0703107807844450301c0165209444501e039444848a000400310010a0304a0490f50081e015102000b4920391940b483c190041c50403212040320301c0f0104081d42c0700040c00742c0702409194001050310705400450704603030030a400c007032088a96142c204001d5580441801c0300281c01c1d551651110210f500607440c0842c0c42000400700e0080300c80b0300950107200d84c030407011203158004032089521184181a0b05210070300030300f903a08001000500840064250002003541c881c600003a005a04e40e41081c2284c00a01c031000000d1400c552400d01c5035071602030104480d12800b0045900303840d00f00c1c4075400d0311804900300d000e286c40300b00080032024141d02c05640700e20041d004070250700c0c072403504403519840350300211003584c8120040f9010070300c04e41c55100300c120b040e1102e500d48040e5400c150b0701182c41807520307079141c4505440412955046409070007003a030b02d610b40c0c0d621201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 621707733 1250 621706483 621706499
    0x3090312020a03030f062616080f060a0e030a1407020604090b0f010e06090f0d0203030a1e020105042a0305030c01021305040506090c18041107030f0809031902030919 73
    0x110f43c45260703410302c0c1000c0b402e02130740040c29070025150b47d075407030103101d404003c0c01c441d41404c45186000c00b50350350b19000050340700004940891426152000d95082c0c1c1d03520f003240c2044983c0191150700ca84d109205224209000c3c540050206105401385403c1140540c00a5150350198010601311500c4401ca42300c1806d01d582c008242c10340900b8001c80300c003a48004584603004842d905441480c0140d2140320588964100408440c3c01070b042d290340d0b000c44080070303000120700350040000c0e6418800c1210711610601c60380d03014a6002c0d10714440304481e0548a164141d02d82c10440381201c41500c00800030740d04200038154808010b00258403480151401e4443c455140e00c00d034021801e1104002d010341e54070610642c04666007491540303d05500035a40343c00b43c0055441c03030300280b27442c0555101c401d850001d410100cbc429603c01d025070228100031607101905032150701699100380900c010b903503003018601100d990030f441164141450f21002621589a02c1103248100140703920520400c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 621708983 1250 621707733 621707741
    0x151b060b040506031f181a0f151302093c0d0b010b1e0301060203070c0b070b0601050307260628031b030f060e07080c03061303090312020a0303 63
    0xf0754220080d00c1d8510982125860344c03115044501c41c156641c4885040b00405030215811143e0403442c121030061034410403030300900d015103805003c01c01810004880d0502038141503500200500b10984051f1000e03000c1e4041e400607075005501c45203c3c9400c8400040e001110b503a200c5480c0391400a42c0b03000240610414010140d55018000241018001c01c81c882800303030440f511259065611603000070501c1d10480c82c86004c0c0380c18000040005805035000019010043c00b0703034400600320360f41d4040ca40d980d100304c0d40020009048107000451541c042e10245501c660310f0b0030688440d625020440040c0891500c0c0c40e003a04040c40140410341c28004010340400c4e200d51003e003e10340042010b00c49100003444010002030301583c0c1d400340d406850341300e0760046510009448141e0103074645040546000c1c8000c8a0368451041c0000c0e521000040c0c80842200c040c0252040781c89030418540300040c80c54054061104200b00007002440e50050111107071080e40c00b03046041c0b100c0ca001000c0d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 621710233 1250 621708983 621708991
    0xa06050a060e061207020309180f07030e0c011206090f051f0812030901150e240a0e13020619031b090b0a11011e05090303010e01151b060b0405 63
    0x80100c10b40b0300a19182c0200b02c440120b44010b01030035030742e0780c80c2080b4510f100d11001186c005500d5640b18414041100b030050060140f0807800d0075a80d1075000071400c8030007085100040754091075a0515035400b540f000c03000b00d42d14032008140c494842d840070341a250b490400c4e040c1c2643e1001041500c1c5141000d00101112208000c1032952418400a80d9001d4080d00440950f2000022803e1b0400075802110031043d51084007206987c3c0d041c054104440465417410f000080b0901da146280c8100072603064000028096031003182080000d50755454010304200810f80f4251101c00035903141000b4081282c8000d4000c03108021046000b02903581095100c02000045041440c07007a40102d252004d0f00e00c11104a91626101042118a40010081042c0340d518145200f803580380b0305e0036504d0321460f00c46c0d014042511f40307c20541e40e0b88024818000382000120050207900451540c100340c0340e44d203151031200103e5060341412552641e65040f1603155507110031010604041c0941648 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 621711483 1250 621710233 621710237
    0x3011b020f21040b0d0216060903110601030c060c0f0b01121704030b0c0f0918070311131401171906050f01021e1914121e0a170a06050a06 61
    0x1c440c110060b10801c41c099030103a41c030062004030f046045442180d0588500804100d1040c02c1c0002c0d9003092070080520311000c0d40040d18032045005220000204c0c0e50480740c0c043e1245260b1403030064102c0c0d004580410440c0e0b01c084100705c2c3e9001c288080520b0703000c1c20000000c00500700301d524000b0300c1c6a400d00c107541645641400f0401c0480e00ca4980705612190101c01c4541e11040f10150091a200f04141182e2014254070407514100042904d035120b00c0d4540c230108881c03011841c3e4655940101c184800d22080f0007582030109081384001c2960682040c1059041002100d50004156008031000391007014464041c5142300c41a01401c0000c10702568011940d40880000035102c1d40c0042c4c01342c400d622130100758035102c541003020001c0d468066040401d00b0056203080c02c03d446080b02500418405c1225146045009904458440c071501195024000c0110040405500b1a0340e14505100d004410303004e100c4107030101180314224021000429070f01f044e040200e4001c07150800c0302 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 621712733 1250 621711483 621711523
    0x801052434030503040303021803100c021605030601030809210139082a070b3610050108010905010c050f120a0605040c0203190813030e03011b020f 65
    0xb20b90030004a81d0031a0301490056503480e8002408541450100003450b014817904090204080c01d44d4444014501c10f036080d80c560403e0304070a41d10a0416000f80c85c0d00d900188010000a02a076008040860001e4403079243c00000b045545101120b020002400380d44800c641600d001702410706c0580144064503084408a600380e000d2080b40301031900c00103021800d80480c098609000035441d040c01e0940c1100c101c07010036081003545400c49181200c86400c06400b00d41c60700d00c20119091203110400400346c1d2000324510039010f0f40da550070f0103401e6008804481d0200f0000c2e020f407234040c00b640d03800800c0c011207520300a0308440c0d010b4410300030004d040c09200b5049031480c01304c440c002404c0485035010340b5075a54136401000240e222562161400d031102d1000ca4011000d0001e40e10840000c80101000010946030240c044030311000f2403000e00c010324000b03800344101c950388010181c000946141202d5081d401e01c03030903410001c003590248102101c100401c0000f440e40b0744250a81070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 621713983 1250 621712733 621712837
    0x1b0e0402070c0e0a0b03030408161505031609050a03030903120215060103020a120f0540031707180611150403020a15020301050a0b090108010524 64
    0x40b0302c00b002c50007001c42074404040402c090b801c50f5003003440c0000000f02039076030f500d94894503155511807640084d80101c070250000a003030000204400840000750304d40628558445030039104c4041e0b6491030205021002e0000b082c0741d210a5540ca016501c280c80d580645811030602200b414a09940d0508560040c40030b601c805903042803268001d07100782000b50312020400c0081d0b40e01c0001c0082072580c00d14240085140150035000580615904800d841c01181400e01c00d00380d420a480d6142178080e01e1040207010300c0d01803240e40244a00920700382480010404031b08103c1d030780c00c3c1c54046c0081d1029903520614941d00344410001e03e01810180d12903140110300c0f5071241a400c00c00c0d4440030b0000c2c00201803500034080862980d61103103100301c200034250920030080d0428080c09010307094000002c101e40480301c088454442d0140c40303005241e840c090401c0000e5079131540d2148140150f8100682c041c4606010f0441104808030030414070101000f44092410039044088c00c0701b9410b0820 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 621715233 1250 621713983 621713993
    0x1031b090302100c0b15151305090c0903030712020c03010b0a050d0303060509160810180906180b010302091b03070e0f0a18050601300e011b0e040207 66
    0x881c0d506580c00180e08001c0721064030080c40302c05001d480d0760601c80420081d40c0711a42d41c07001000c400c40320002c41001503516100075020350140d04a14420740c48003031206280041c42c1c0c80e4041005030301a883c2c4103045005c00d0641d044404100c8594803120000c003040394060001e1b0320911805d40003040340c82666000034803240458030440f03019181e41c48104050502c66000040603142c09000070145050003400d500001d4804e0510b000040d001501049116450040c05001c42c1c01c2c0d051955100c45840354514001c0424030400c6544699850052018469000c3d821a41034045c1d003000341d84d903240d8014000845e000070f286c1501d030201c6002c0344a0301d1102c01c06481c0c0041c010b1511095550b406c0020401c0b803c05080c40e15405100e2407400200340b08054150038210342141400d110070703210500192010b1118620703a00f400d1b440d8076411b011607480560f0301d80d400c0741103000208150710721390b0500f03003111100a00100d0b10401e00c20350388500d40d041801a041c010043d81c0461805401d40c80e8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 621716483 1250 621715233 621715247
    0x604141b0c0709150f0618060f09030c1d130206120406060b1215040e120a02070e04050c0307080d0f030b01050c060109061401090e0a020310090e010b01031b 69
    0xc151058000815442950081001a54040c0c09199030403c81015082000b04c40795503035120b8000d0000006a001c00c145120b0340c0c043e44400f180315610a50f00307041c2842503032001c404600744020031444c4c407800000302d100050002c0007411900703c10081d814a820310611140001401a0f001d41102c254010040c0c07640805c842c100c45882e0410001502d55181c8000500171a60007504401c0c3c2c082140821099607030000350107070701c40501109101d0071400501040e03a006c04d42180790383d00010326a2078140303401d00c002d1003000c4151051304c030813a1701d62070340301031a9000b030380c0a035070690244100e6105420304100709000b5003803600040c0380480b80c00c2c0f0010318008030903501808041e1540c2c0c0c0d05110340d0081e41654031a82550068604a60712580104001d00c440d1280c00d4031565501040041940644844019192503440a1265035a41c0c90340c0f0009c3c0d031001d0300600c07502000b050000340d10400c45c8070b9910070301c05e80000851140d01c4a0001425918032840743d2000c003284660000f45ca5402c111 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 621717733 1250 621716483 621716521
    0xa02030706030b0d0b0a0219020f0c01080a0b03010e03040302030c2209021813020f0f0303071214040902030f0c0414010e01030b0607060603021804150203040503130e060414 76
    0x81d01040441c3d0400104e2071001e001e9000038541000b040610140c04070a80242c40f03004400c10484601013016903080380e03207081c200c2c440001a0804404030f001544550720705036210b094002c010a08130154008131382100c948079807111154001040900c114a010b2189041d2540111401e910060302e0b0303c115603039000384dc00700d041c6656441098604548650762151641c80359205009882d2078840703000711145040503402c138410305050070090000c2c9400204041da1420142c01913040103e1541e03141701c001d03039810132070040c080080e400b1007000300c00b00010006440d140c400540c41e410f00640a0b000c040024148100303900c0e040c0800c0c001c944d8a0700341e003440803809280510040c0c1d00070005038018040001c0b00ca8019000107550b805001080d041481202e03c2559031258415007442007200006043e507008041446900b40e14101000329006160480d00441c160303403030007551140908881c4113640c172000003c0c0c0c114080102600d4039115907601d00d40d0800403209d45182066000b107071801004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 621718983 1250 621717733 621717737
    0x21050c16030e0d11030d0207150507020a171c020106060e1e0604090c02151006110705090f160f020c060a050c01020310170319052b050702010b030a02030706 69
    0x20000100341441101c0580394110082d2001d0350f0010f45041900400003212440c9000b071203a051070703044ea05d200040c05000c81d0080320a281e0110f240e0314049070158040702c0c05aa00c000000d10118418400c12010340d034094003000200001c0305040700348040218641d403013009591400d4010481c03c0d0704514807917003216040340d0f602c5d8084220044440c044a80141e59508107002090109152a1650211281c0d074070399022568520001000102c110b001100c50b01599620540e0402980340140d8102440d04201000c4e80d41080d1110301260703030040d0480e04040e121100200b400031203940d201d8000020a018942010030441114020f0340e5242d41d9828a8080c10b0300081d18641280300b0308c1696107100100b8002e659034100425031000380d002c24094000110000c94503c100c421000048489a0112105040001c0e603000c10640701500100d0500028010008036601441d02d9070307402800307425140c4400181400c02003c000d00b19580400c109010b50701440e840400359400203290801c40b4198 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 621720233 1250 621718983 621719017
    0x40501140913151d1c020f0a1502030c0d0905070603060611151302030f0604110604270f0c020a0c050a0305030f09030304030818091e0411041b21050c 66
    0xd0404000213402542000f20500600603034146440074207200c070620300780c654200c0c1c81d03120744070242d070b40c44e901c0d00d56001703041c042008001d0040e00c1c22600616400500104d40c1c608044500ba0140103a880b510003c4803a5004000c0a11940f5050b10a00c03000c0d11851074030950070700f500500dc0741d840d0f41440d4020041c1400c0340000e0190344544075080c86841c1d0181c01d482010100c0c000c0c0c156503507803e0f9070480b4403008240f200c54071400d208094074221081123001e1450b0700d00754900d180c2d901011044042800303450740d000d100b41c18000d0280030200b0f1650f6009140a480c3c90900d1561840e494102c94032030810148100f002c07503800001e46800800035051260b681c101c580001307140d849103a000500101c0e020954000608071214440100d880c00c1d03801a07100d0307507079010880700740340075120107001c0e078907903002107004640710034040c105044002d172000402c00c41c1c2c240120451310007182d1480000c0d1507408109100c40304500c003030b481c1c0f085445091056042640a54010340541c8021039421240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 621721483 1250 621720233 621720251
    0x3060906121f0509100506060406030b0303040909110103110f04031106070f050f010c1e03020a09030206030a091a0645010305011407020d0302070c0504050114091315 73
    0x414030105020b50407804195182002c0c040021010300011111034465000d801c0c981c01d00b07500c660007000c1c410080140a940b41070704028094004090b0401f519405100074070020440224510981c44818001d8848403130408002000405541c520110b4180307141c1c0c140014034060455000391410389900003242400c4000c2440450511301800703002038069140156080c05100c4081421b84003206404002e11410035011016681120100402c0c98014800b0209206c094032907406426404a40d160a1214966030b0300040c4440e04155841c0c4100d071b90ba40b01d120100030a000350024601442030310900180340c200700089409104411800d1308907401544040051000c4001d040911241d040640d1071441d005603070340d41d0340c0c0240000c89580d880d0091030019a5045401640325000a60042c260b50020301001c5001e504100c00071207002200440c04101c80d5a58050382d806422000303070070201a1240020041c0c0c420003d0040017042d401240284081400200c18a04140f82c0da2404200b40036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 621722733 1250 621721483 621721519
    0xf01171b0c010c080f0f04020114030c1b030301050a120b0f0403120e0a11090405210f03090a03141201090203180d0c140d0206160c0b0406020d1103060906 68
    0x4215460303100700d5480c0064104031213400400e11800f03800d0000c0c0714481c81e540c0d003021868040040e14085c0c08642c000c5001e40780f60580400540d40480343d881c4807400e0803220541c1801d004102e0182011641002c0014000707410f0240d804401410f14509a048400a032b8071058113009010f0440c851515248000034140760103000180b1440490a20811580a5010241e600d840c0b003e1400c4421042000b0030018900d0040d0b1228012754102c1d02601c159004041c0e0710b00c001d005005080030303100061000b0742844801d180178611600c0d19102420843c5903a03d00204103c80345440ca040c407100a01444100000440a42d419100d103810010707525203820301080ca40101c10b240c68843c40c0308028024000951092199000a100d02c00e0240703520004100152038100c26211500160301140c0020b824800406120181c0207260402d90300b6104a42c844900d1008229410381d02540c00041c0c000c142405480388490001c0d50b00006811818010002051001c014001600c02e203ca103420301d00042e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 621723983 1250 621722733 621722737
    0x2070c0302040b04060506030c03010906050f090f07180b0903100c050712030207021f120614060313062c0606011d041e0c030e0d020303040210050c06040c050f01171b 73
    0x1001c004e002c291280727003003084802146e000340503603201141444000542401c00b0710054030240e800416951907035596200d0030400a6005003200704001c221000c0d0b02c2c102d4044440d01c40036003040e080403643c0d110309105062400481d42082e0140500d8250040078595020042c2d035032866214001c540c030310000e0b0204401a0141c000081e50004010f000c0c0401c800d01940c3c001e00924268540711421042c0c002d0366021500144601074243c0c4100c1d800c040145403040c0155800b21105540c50124040c0791a85d4048890301c945000b60f0b008444c0b07400c0c507000000300c4200c00b08001c0c0e800515581c90001c0000340251248141c02c13440111100350020b16030341c2c64000300002c0140440d055a50465032005002900034007015001080c9800c3d014070038001d011801902d0622250021440e54840d40e090014801640700010100031003803210b010f228009108040c002d9011350011150a800c3c181000280501c411105040c8146509074003851010b800001c0d0f88151603841c107600f400c901001d034031424 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 621725233 1250 621723983 621723989
    0x1202210f011a09061801090905012a0215150d02120d08060a05030f070b07050a17130801050906010b0d0e0601352d030703080a0c0302070c0302040b0406 67
    0x30754281018540d11080300d0b0880308500e0700440d00e4880d1511140280403150014000244400c4030000061040b81e00710b4100d1001580300358000a40c0400c1844261040712039601d65811550405c8810f02003994108404610f1124038003000c9010709008001480c170003090058180115120110340c025551211554686102c5180a48103c031106402c001d241800c00c640452103002c211201003054200066030581d021140401005c49d58140600d020742070300510000c5401e481080c05c1c8034001401c09000321482c40340800c1c0c2680340e880d81445680c2c080d44641102c04968541010030403200c00010741a0b0449094a0f02156150840140a0040c2130060900b07070b04c0d0b100300c400010301c8060480051510000394040d501380f541d1401102e0196280d40030845d8030961000f102c0c00c4100e0780c1c0e01100e80d00c003030790001e01018a4106200107130440d0400801a40400c590004000d5194545d01030984050f006190440c50301c82681e0303808001071444d006c0a4055596204a10090f444641c000009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 621726483 1250 621725233 621725263
    0x60a09020d05010513090b04020d0204020c0a06090b3303010204090c02210703020303041b0e0a0203070810050d230105010b18010f0e04150302040c020c03010501120221 74
    0x52038074a0001c1101810082c031841d4020306698049642800301403194040302c2d540500c0c401c084d600d0305c0c1c08200580c80000c2091f64055030030001007480f00800c00c91b00003000e00c10600400c0c004030a051418161000501020040800d1003c5280b50b400c1d400540303620243c01c41c040201c480451000ca40240115006034071070a1401c070311220925000181c50100341e00c05289012007040b080c0b140103c1d0300941e10300901590080c004140000c082118103002070f8450a140080d02d941c03100325030001c0c0300c1905c640500c0d540c00070500c02c1d81e80d841075150f0303030010000220710f6003a841d180101d81110205000508050480000085082c050071101117444000348001c1c841c07540c4503103c1d00d1071503011001140c210070503000c035024154081c002d1810400041d0700c2d1030703605141c4a000c0c400030305065551601c5410040300080700580e5140324074100c00354a94010030b5144030060506003100c03c1070304141002d804000d100401640d0300707000ac1c0000480c0b4491403100c04220044c00303103442030360b50107594 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 621727733 1250 621726483 621726487
    0x170708190501141f050f1b060f01061d030c0112090c03030203090315010b160206070c090f0c09120303020c070e040807060c0c0c0314150a0203040201110d080708060a0902 75
    0x51407203154900c031003d06034101c07094000c102e0400300c5142c0044403106600d020071814421050090490400361001c0240d642481490001e18a1624141201250f0260700100074500500025501404e002250380b200020781d000c010344000000c1d0340d0241c0326615810404502d12081180076150000c185080d4041110481c0646034500a9100d8100980c0c482c001d208086241001c0b60034400100d04a444c003240040c9001450300d0480b90501108100b0782e0444010010b0200050b408d8a4010040004500c00900c6c0700e10311142c2e5081d2040c2002c56006c014842d07105000f0100d0301c8842148195040c180140c0d140d0b02400e02c1810300100358041c1c103108419804110034003410034004d20026201d894100403079200408141c50100304a140504100c10014060000502c00407221842480d114221448080303254560751070344508940207410700c1d0300403050204550300401c0d40c0a00349440b0020389114607568030002c100401c0200140c081003560f802003803c0703803600385260014140d1108195 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 621728983 1250 621727733 621727739
    0x30617060a0b01020a1106030711100c0e06070825170c070e090c040c0302040504090602040509060d0b0a0f060504020304050a123002091c050d170708190501 69
    0x5840e04000c403000340d809030904031460120b6101051114a255200500d00e4200840c2818440a600000d00180901c80180455441c00c401040001d804e000c10080100b4400041d140050244a02c40c8125000350820700c481d40003d10038200740c809032848211142101e050030701e2090b00d003946903000a480d01e601200074401000700c1000a001e0281d40c041102e260569400c81c5001f12503089600d00b0107a0462100400c182c40d043c2c00009000085140240c1040c3e1a00006001c41d030018a0854080798001402c0142d414951031050348104200e51080f1122469194040265402041c2c0d22000c0e5039503428064284299118401604001e4800c54882c50a490650364030000d40030196003200541040034241482503060720820407c031000c800301e00204810780007a812208a0b0a12102c0e006d00c03400b8070360740f1a547d0324010503055881c040140b0b9001d0520b182080c3d0800e03940b82c01c0000da200c0101000b441700741140c0c0c021142d468503510a694481000d0600c01111201c845074900780302c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 621730233 1250 621728983 621729029
    0x702070906050303041d06030f330903070210021204090204081908160f0f0503031602061006120f050a05070207050402090d0b180a0503030a1a0a150306 67
    0x2405a0348030344020041e80d40c035034007095a41e01440c40707210050070302001c2d00c0546103034002c1260b40100014048429441212034028140084542c260340c948100c0f04904491030008110511042403420780f01c800d074205888401c0c2c0b40c0c8036598020340525940b107448ac0071a80308208201010b070340d0a5805031a15100e40110010703600500c80d8008038814a280000d9801c0f0041800d0382260344694a240f03400c0d910880001803034006641943d0711503508001c0c03c003113142c40c008c65005d90300c610003556a92030004411800098085200003c542c0900c0c01c10003511011001c41c419100c007420700b442803140204485020302503480403400840d08000a0112166040d04998000d80c0240c0030340322816203690510089014410286d940505000303a9003002c24140c07165039801800c900001da10b15001e00104c20b2902c010b0503001c8071598000810007140f48802e2140c0003c4a921080300150500071400069606004d0f004900c910141d290421501e00c1c06640404000d000515043e03044402d80022 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 621731483 1250 621730233 621730243
    0x15030a0804060e100e091803090d0f120903080405090a020d0e1006120f06050c1e0d05060603010b1e0c011e060e0103210c020a1203020c09010b040501080606070602030702 75
    0xc1c0a0054070702c21303003a0010502400c950407402d80013901a80866881d20344190381003822019090a50004200320b60f0f0780c1c0c9a07240007005050113075a2000b8401110300e03210701746580500e2014100842d1407002d000243c4190704540884000700c54800a0f9110305034100024825000001029450708a680310100804a8080c0e0031500044c400c112855035820007038440a04003000400b4800081303100c600044203a80040d07002800304070001e04025065400d905102d10038883c00b400308101148100003c00e2a028240c0d0140301910454207651610f96541c405016207402509144099094023241c40500801c3d03410781c402800081c8020102450440c3e280f081c0384482035140ca0800c6400318030190014100390490b580721848240d0395001011b620388140b02d070612041004860040b403000f41c0c1e110b4240708041e010500304031550000b0f918010b454005840d1183d0b000c0d868440c010045e41c42c0071416503080314020f080658241d41c1c2d0b4000607030680301d40c400c020903841c408030038042070a5000030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 621732733 1250 621731483 621731507
    0xc021207152c070602070b16050313031e0206072a0914010506310302190905180622060f02120711060105040c03140705191715030a080406 61
    0x81c01c1e4050303092180000d4650001c4d002e0f1002503403142404103c41d10030b0200500840c0c003010880c020201031076031010f0461f8844940d844040f20045003c0c424030110b1000003541150040c10f9080c2c5c80760a0f40031411501076004040c040c1001070800d00d1580d90812008170b50060309000414480d80c840352243c004100340100303400c03041e03c0d400001c034440c108141200c0002d55481c05c949940e103900f031202407081c20800c0b105141c801409400200580ba022440c488002c6403072818400141044c00030021680b009080c030203508006020184515800718610b504100b1060040c040107034011654600041c0484008041d24a081a02c00b0b0740c80784e80d40a8440180080d03080e000700c0c3c44080d412280300a461803024040d40003d0010042807802d507011050080545c1408280180110410303000240e08403200c9000ca840000d0400904803071844482c0034041d14144803503140304c3d011444008a800903c800050003183c00c02c0d030715a036000c11002d80300503803008615640e5520780c8001040c03010740607 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 621733983 1250 621732733 621732791
    0x18060302091206010e270307060e071203120c050a09030204020c1f090302070501090b031611010e0a060b010306030f0204050702120307020c010f030903022d0d031a03010c02120715 79
    0x420741010346c0740701005440754051400440c208601d58691500400703214a42e070946210f14000055045e042c0fa642440f114001d4440300c6200681e1001c6a06407081c6842e202c003088010080d42601075002540241540c0c1c0503070f001a10742030b5080240b4a402c0366850f04a28920080242d034089500d150070122031284030307600350780f07506559000640d040020703401100d4100c1e40a100150490b003d1038030369000c400c01d920b000e5401440b108011800c40f00300d419020050740040f00a00b05016540c003442c0826402864100403d502d551540c910b1a04000c2c1c000744510b4840d804a031903c0d20130004075440c0c800250480d40d40382401c80c406175a0302c403910001408119980e25800c5013602034441e001206806030040d24410342c615842d02c0700c81c0d0004140c1d03811b80c80c21031244064140208048810070589803000122030604144169a400400da074080c0720b0303814141c26144090340810022005440c281d40f183d141c10841c548141e40901000803205084e18001106540c0341141c851640c82819038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 621735233 1250 621733983 621734011
    0x141b091e0315070507030e010c020904060c0327021507020a0f0911130611100608030a0305010503070819060b0d080403031106011505090112020d05090d18060302091206010e 76
    0x1240c40b90040421115a804650140030300c0c404030703019030b141800515051506100c1f40007181c0c00120060000c2e0b0b41610490b5440110503041c68151180040c800d40340d03100050450f00d00c22230310b07500d240031b510300034000e1800d0305040e40409004010b4407412940100006107643e112010219890024403035031095074201504503401300c8680c4c04550003407401e4060041d55a00701340095030401c02c4031640c001140715003181c1c03c0803c00b1038821100a840260082d641d641030030100102a601e042e00321034420b811180c070800040c000001c403594130a54050701c28065201a0500030010102c0f071111b030b500486245425000c0004007001401540d21035102c01400b0786692281c590380711030900841110450344426288030f14001c00141020002c1490600b0590503500d03902d00c10307038001015103081030f0303164028403280c0b403014042034200f0700c03551a011840320119622810160b00520074130007415400915440241c4544c54000c0d000c104003001c40702036503999101408010b42c1201c1c40c648803900c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 621736483 1250 621735233 621735253
    0x10112a0106080a03090b070c0312050903010c080a140f010e180d0509040614091b0903010204120201090b070c0504152408090a0f170705060f060112141b091e03 70
    0x501c109031543e003900405230010b09810760740c40d80100c1c0304400600044c01400e0103074072080d030380900a80640c118265110360b01800c0c101c600030284e80114200902140041d020050b520318500d80550450b10300d40001401515280c0030303140c062071132035007688e42800707551844040300d80c2000003001101d034243e03020414103689000c2e88445045a100b01644011180041152081940c128010561150900d1440d00581d80006400ca9005034016242c840240c0c61103000c0d50382108030340005203036000c103251170b041702c80d0b55800c02c400c0c060088600c25aa150850407069008008190150111610080031100c112a104042143d43e003141d00010380c8680001c0c1c80780201103248510554040600c2c030400e42aa6601c1000024110302c108402400780404000705a00300315450245410790314802e03d505090700010080108101990380950038000c2c42e041042d101800d640d40a1010011541c80f038551034080307880c41c0700d10002e440d4803d00c2c0141d10503e209145801100c107940403800c0329030399a4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 621737733 1250 621736483 621736499
    0x10020403030f0c1a0712062c1905090c0904050c10050901170a0e010504241503020607030311041403100501050a0512010207060204061110112a0106080a0309 69
    0x4098040140031455544c01d0141040780c19500036045040d5040900c4003503410410082100d1301c55115241001e002a070300d41c00a0000f0400300d1062510902101c11840c1030058401d030f03c01807819840e0142e645000140303400b0b4080c03005001500000300405114185800c10a90340d0224486840c4154100c000305400f880c0603000b00c50031101b040e1681c448c01540c061001181d07420041c882c041c0c00703813103541002c6841d5080c400c0c5840340d485160342086040e4207043c0034029840407589024003618010b0311030300580c4202c641400b1203504581c050b6035140b20740b50440160241e40181d8411020104004c07a0041c41032034440b00b1a0000c1e42102c900c401141c0c0b000c800c0d24000c0c072070350350010303800705040c461801c0c20f00c03e0000024404001601c1c1a84170369a031005c0386d02c50340c06000040c405120b1600c1559042c4076080340b00990840501900290780b191035094403550303040716880804803041e0310200441c0545c0c0e1104040d814006c022a5a4640c100d68843c40345800490018044c0000815801c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 621738983 1250 621737733 621737747
    0x4030e0103151512060f080102040305060109140c0306030f07080d17040b060d031403040303021c02030709230a0b03010305010507050309070504200304031706060406080f060d020310020403030f 85
    0x50b000e40c0c1d540ba1100c40f22800b40da038291002c41c540344842c1c1707420700410342c1c0c50900580402400f9107000103075114514104a0b04020043c3c200525090804d5040c001d9503c44c45210b0b5081214817105940da52607000000380380403c4030700c02d02e48034040d00100244106020a004d1080703075450b1074148028080d00f5581080c000101c03001082c01c070800c00891445c0c142a401000700342c0c824148050301416880c481405604121402c40000380c0010385001e103820b05120712880309400131029402c0d03040c8400c014106100c08e00502c0c040c1ea000c684841c01400b9030f01071100c02111701510454011f61106044007071540300740016074883d800e07c8049a9503a2094048034840d0a0400142c041941044200000351007082c0741c2000500c041d1000e07409068001005500991213500e074008400c103000d07081c1100d01c0c2c004040c0c0f03100d08002e10080180a03040000c40740c0c85006210b9020b2165264000281500c4440c5006505441807040d404000400c0d03600400503030b070003034a42d01425403441c64110340c50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 621740233 1250 621738983 621738989
    0x10e0f0f030415090e0c0c121c05190204030b012d0e0c0d05070e012c210601081b030601050d0212010f0c0207090b09010621020702030604030e010315 66
    0x15407003000204000e95044450061a02c10b0b8a003240300c541d0348001030141e00070195001c1c2d80e41100082c1c030b500f10a404220709285e50009803540b504218030820700c58906a03295500e02c2c1e0b282d40351800610010000c481c5049003000884045440316107a04081c0c0700e09000b40501c0500000300700c181490609050120903032810403069030b00d103080c100f903030300c0a20340c02c0601001c445650510a1807500708032030240c5441407002d0750b510b100c0030181e1000102058003010440408100c1c220701114002e1400514481607002610b20170051400c40801d1101c0c4401048101c41a0044000100d4108400b09608090715266405500c48044a008040c3c8880307087c0300d125804480340ba04040117082034100e181d425031244000061071105044c40a00ba81c002200010061700059000d001081681c410350303403415001c0e00c4034410341d0304089000d00385481e89405080c22020210141c80344188540403645443e41c06400d5400340d0405280151985802442d0705010030305100e142402800280301e28422 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 621741483 1250 621740233 621740263
    0x16110f0d030f1103070b06090a060602060c0c0a1406012409181d100608010b0a1a04120305070b0105090f0a020a09030b01030507090b090403050a0e04021b010e0f 71
    0x2054000c0e590648101c00c02181c10800d0120b91410804240818005491500d00820088615103405800c010080000401582d0910f00d00320f0706110465001a07480d5002c074420412035540c45c03259102c04d1814a09100c020b020080c0410710f5112610086020744c102c1e425224895403038600b01060105221680c50a640094604d190400804446841c0c1014a02210000281c01103050b08103503044a03102d91413040300c2e070043c0030003284241319204000c02804081c1c0200075040340c540000700b000705140704020000034140c408040c400d240f0400c8070003c01c4031000d500c0b500d411500c2e010b4038a80042c0c405031004c004d81070000502e4201540611b10400012a1034010b540d80c3c06a42d60003500700c51024810403085060100005420314510750185003c1d400410115290000240a6480395913010303001c0e00c8018180300000b508170041e501440680c3c2812060025468003050090041041d0044010038840c0d200c0310000c019401440304114203405d030b6055068030390a8617580d0084503443c0c58 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 621742733 1250 621741483 621741499
    0x82413050307062d090209131703040206040b1b010f02030f07120b060d0b030607020c0a03150209060414040c05030c0403020411120903040f050109030b04030509011416110f 76
    0x904280d03c011603810160480114aa984c1d680c9003050005001c40355645540d15000e036000d500e00140000d901502c10a1200d460707d42690b2140c0000c41804000001c030503020010604540d03130442900c01400a40e000543c80b01c1003852000145451144640d40c103500c0c1404426500480d80212445620400201d403002c2d1580c038000c460307040242ca00540116680ca000c10b400740d88100080140d64512003001c00c100c8000c13000c1608118020703000c101594404003025065866000e0740360708036604282c038045600f5948803800081e2090500c103c0d03000741e0000b0089080c841213045008103800544040100809810007920544010741c0c618410341402d000800041c41d150700544004881d404ca9181091083c05200380555404d460312000c13900b010405114490071032030560300a02c424600740074071901c2c503100c000b00030101900103020842c0001e0b001c10f03543d02403000310460700003800006a90322a0742c10704980c009222242212500c441c83d8294a251801e19103102c440c0c01c00500c209 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 621743983 1250 621742733 621742747
    0x160b0c120c090d021302040e09010209011403040302070f0b0c060f15040906020c03070c03142811150417010b3709020403020f0102060709150203040824130503 70
    0x41040d007003402c100ea40300240340900300050703d81c000d07140c41000d4103e40158485080c0440c0c0c100303c8200403d86401c0307a10520041100307a81c480c0c0c58865003407841e10010382c4c2c2e40361400c0480c01c280c1c1d15003200382c2c600d84a100006100301503000400d40c2d44180401e80d00c41d51107a41c04410b0800b42680d0444038010b02c0d214140c624602980101e030303a180f00310383c01440d04403a02e141c54116080707440284c416038000542002440500080750600c45081d0b00a4160f0300c0c200c0600001c0d0700c482e031a030780010340101d804680c00c100d4569a40c110a40000344010100d4281c0d44440303c00f42e100e0b000d13410084554182d50401c65405000d4000031100091400c500c1419203041a00b81001300c01151030300d8036883d0804801580804a40d4010341030503280541d07514118018805001c0c4c00c0b006190466005004115100358008524801c2d1004078055002500000340100d03d14003031a0402c071503a005800c60964605504155100048030081c8801170598810045c0c1c940c03580b90003000380c502c0d04200920 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 621745233 1250 621743983 621744001
    0x2c091e04080d140c0927040f08040801021b07090c021207031704030c02040506090708150307180207050c0a06080705090415030302030a02060f0c0d110708160b0c12 72
    0x20307041d1448041d10008644070514580c2010540c00d070384c080c00c0740300d0000781e10f140c5081c9040c0c003000a100600240c0c07000c00c82e5104502260300c001304040c7c0082103204001c010003220200f00d600402c13200000b9521141d0b002401040004950341c41d82440c03042440004014045000e1185404580d4020740040b652501240c0300581c0b240c04d0032410001624070028007031441c4403485002d10b00a965081d401c107854414031040340c101030641c0348209603020802c2155a40300d0800d170b070302070f940740050321114254002203440c0c0700d40e42d00700c0d072030680c044001e4141c914025405017095034021002c40389907007201400d00c00107940b03900a403030018031480000f41c001d41c000c400800c070041024000054200840c459040e00040d1500700701e0068000151204201d40d0402805070003101140300e24000c3d0401c40e241034043d204c1da038038040420b42ca070780d039192035002c1e21020f441e407058100420543c1c40e9044020300030880c440c0d01c0300301c40400c101004507402c0f1400c0010f548004011000c800e0481c0c03141404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 621746483 1250 621745233 621745237
    0x1b010b010f120b04140702060109150302190302040c0e040513020d121710060f020105190f020417070f060f050304060b030c040603030504092703080402012c091e0408 73
    0x44014403d8644000e0000c6440d144110602000800002c45450a10f0f071070082c140201039000300d00840c1001c21a07802c00403096400c808a81d8125940d210711641c0103a61042c9030703626800030354005d00d8221408075440d002130004021400c115010400340c0d03240c0c01c52103107a0640340406500003a00d0710320400091034080a1240785181070501c0007103640180740d002a8804c00300c0725000d800f0030740f100c1003100d55080745085011044500007400507181c210303920140e04000004401006858002c24940300703143e50b040f1409040300e00b202070754400b9078075000c5589500da445900c20f001c80501000820a100c2c01d6005103807400d1b941d40303d2441c0c0b1903840703005c0a064400035256041c051216900d0007a0b0711032050400a6100341c0b0b4031612640b80801c04000c07104a1076940c14442d00d18a4000c940c030601140d148282c3d545420054200c0c0c40c7c0f4001252500041c200b4501414075082c6030f00c507200d42049031940300e500304455642052f0707903c5403c00801107101109296412920000c10000395940c40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 621747733 1250 621746483 621746507
    0x302030c0403060f0b0a050f1003020a03060e0901020a0f020a240e010c0e0a05030a0506190b0d03031a01320f1b100e120307020c06040b1b010b010f 65
    0x4903040c106a2291115030403a00412141040107030781d400103041d142001810500140000c68580b0030750500e00c808507201e659000506030405500182c8004403e0217548548054610181c08407810700d40b00215900070340c058a1108041510564101c03a0f40740300141480d045079100d035245000c0b802c41c0c0d90902e0381c0745250700c50b609565240e042e444030000003441607148c41c009599500108402c0c4170180031000f8900e4114174003e0300b0151100012640c005041500011250205014407140b52005002004290885540502e140c4481c80500d90f054028000b8540104005006156210700640341d00c1603240003440d00b40141040600028140f460074880440304a18642c40c107410781c6141c884507441100d000000c41d42518052100750010412100745005040040194129155a4966a2944070505040351070000001017071203209110040c0d8124020709015180c6840e440d18150fa6084005200c80700d40880214984162050064451110041e11482c03407003144002c040742c3d42a0565 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 621748983 1250 621747733 621747751
    0xf0c0a14251b0509090a030c0215070308070e0604120f020d14031201090903020c1e13020307030f0b09060f0d020604080c120102070209011403100509070602191101030203 75
    0x2803100c6050010900115504034400e0100c581d6044103682c1181e400451034000b40d0003603014004000103c100007800c0000c080c2c05040c11260410303284006103101d6008a144030340e10700c000c10040c0805801808986c000d03481600c80045540c41c407028484180a940b00f03c00d20200300182480215034001110f4003914006882220010400d4903130105a000c0c0301c982840c00c0d4000650302140c580344480b19405000e40001c14080c51005d9100203590314100c0380000d1080710500d001c012408603054440c6d540740c1d0090005207458500541105c02904106d270210082810000c3c060203440582c0f2603002c003808024a60341d566110720045c0810708a8054400340c114124a24460240c1d849002038001884c1100040c00008040c50a2149000c0c0203082c540c1180e00504c25071005039503001d58941503401c040c10704103141c45240c0000785010409602c180c0f58034940b1052219100e0b010641e501611000d808444082013007158001d80c42c0c00011018140481c800c00c03c643e95807080e0002c42e0442200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 621750233 1250 621748983 621749017
    0xc0c02120f01050103051e06010b0d020a1106100e0c07050d03110408011103092e09020d120e0114040f0b180622090c021b011b0b0f0c0a14 61
    0x12007001c81c2140c800b0380041d1141d42c80b21051504441c5503041c1040609021409030644d075140c0726030b915940c0681d8400b48075068010445045251107542c14225030300050080314002c2c2002070604c20240d880303000382d1300480d24101c006414810301c1d0b0200e40901707510500a0a40d2240e40e98210014401e120010070540020080022052800d00405032a102246802aa00d0505280c428075120413034a600e0304080d110200b4008940c401a40c545101060302030118451240d440012a01c401c11000185218496591101c403140d01070000d0410340c0080e01c4400700380703140b40482a928040c034401e030310b0300103c5160284541c0d080c4c903025001100720051b440e0b0b00c6009820004d295500300d10240140d001c940d90b210070106400405850040000410400540d8003540c8000c1d00d480ca41844942c1008814802d0f8402d6445900d0604000803040c0c070500008480345001041100c0595161401d40e5652020440c20030f940c80480b070700c0c501141c036002e845010b002201c00e100c1c0c2082409401e20001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 621751483 1250 621750233 621750253
    0x50c011e0e03190302011b0c0c0b0705070e2a0313020409170a0215010603090b0601050703200f0c04050f040f030302040305071502010f0e061803071403090907030c0c0212 75
    0x403d5030780031922442034001050b070040c2c4e400140450562454208100091142002c0200b0200c504190a6032030207046140e03550701c90308006141c034540d5070103160380e0103404081140040000b1001c2d41818602955513a05805c052400369050005543d0036101c2c0b1452a1494010700e0140d1165200c548608004204511880e840440c01e8008402c100c0268128280441240c0800020b0a001d000b1505080083c050705407030b141440d00d8014441c505004000509606040c001c0e05c1ca201c0d02c00b02804110403034140070301c5450f00c5850805030083c051082c044440854034250048512400b507a251005103a82d0340d88544400c961004016024958200720220105d50180030b00700103410f4142c005c042d0300c02c015a00a08644c964482554451f00e0151641180f1030081241c0d500034802040c5445c14204030703200c85045108060005100e0b140c1c03654605400b10021024003074450044034600007503607a800050707003951080c0b0b1004000a40304a074070070040c5490030200107030918040407143c2d1048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 621752733 1250 621751483 621751513
    0x11030303040b060a060207080a030e0f030d0e1c0b06012003030403080402010e090f1b04080709150b03070203070f03090905090f0609070503070b090414010909050c011e0e03 76
    0x3006580c203481c80903800c0100001c2e4140140204000d000c5440100320b11441d000d0031a40307401034000c00030108214404150b10a0b9554400194104d40050070b5070f250b9107044ea0040c2002091081c40d60090011543c05000d8020001d500d04009030031030a1511282d070703990011a03d00510032441368541720400c4900401100810146128501ca0b0721241c0450030507000141040d01942c80d0244900e041030104510118050309041d041207032002c8074069101c01c405100c8444c01240c0180b08603100c1d40c0b8000840092507000014401026000c03940c03140c2e102d10340b00301c42d07100454042016a00400c1003100140351684c0020340c0c1c038082c0c64069421602d41c5080740c10b440080e110f010f01c0b64441540640c0c0c00c00140100d0707400c140100001e014803441c00300403c1d15152a881101074a12002c14800d9081d03d5540211800104071240303c5101d6848403000d42c014500c010080e03d4520500c2e507401844e5000307251400d060aa1000a16248185144204c48001c441c46c0c0e02c40c4c050003525445a1050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 621753983 1250 621752733 621752737
    0x3090a0b011203021908121b0d02130f030203031801030b0901091a01050a0c0308100905090d020c150301120507030503041401030e060f01030f050705061c1a1c110303 73
    0x2201440c1620203003100b60600a10700030350342ca04040702c0ca00103c03403500004d420004881d5484540310403c0f005541d130509005c03480201e84104481100300080510004840da8004c0981c81c0c0105602ca00c1a40c030b880c41e10503020514003000307405500800500710344040e034101c1c0c103402030014507000c200c11441d9000315503c14000e81c000303a02a52903031480e000c44145941003001040013840d0180c1000c2d0071120042c82e220801c0c80c050700344041640400c01390440c3c3c01c0700f40003038400801c0a07c803038100305905c40d07541c41074030114000502480d0641056480d2101403040e00b03184d0303620b100e411a400d00540340c94008a03200e04482c40e1044220000c0020303010f01c05040140040c01003000003480794800941a940018482c0740c540d003006040021645404054034192034005649103000c0d8114039000b45850480d40141d0f90010000c40c0c1021192041540b8064829800c80300303000c2c403c80c1c3d4109294230781c02480940d9000304650720440d00807940c0c03545034a06500a4030320035403030611400464116 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 621755233 1250 621753983 621753989
    0x5030a0209210606041e0c0302070602130509101a0a0314040501021e030c180303070c142d0f01140f12070f0206150d020913050705040905100203090a0b01 68
    0x8140c52680d90302d458051240681c8560280c50a0240c01c4110000c64003030100196040d8003250b4420b90170002520940c1519441d60b030158085507201c50741e0b280034241900500c21644140b8a03000080d01d17621140c42a5000c5030700008030800a03280c00603503414245c00444880e8200360340d03644560984072203e424540150300440005903100043d54180b003c1c503d44012540451400308180311000c1d078440100c50003a004c10080411074004400028114414240e001d841002c00303103070110f131003640a01e600c00101c0302101d401d040460018010707900c40c03503003009001900700300301c0692419040412040c49920f40c140b41c00c0d076452030503d02200c16500005441581c01101003403841e034556480703144682101080c1010b404a20340408000d55a02d07009150a903885aa050a0f0141d80c0381c000140b130317040380c0c01409100c2c0341c940400c5001044680c01003d91b85403140f00400920340c1030912481a001e6000405000100300d8001804040e5001038400300e83c901c90018940d011802803020540a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 621756483 1250 621755233 621755269
    0xf0a0b06010c022101050c1c1a1003021801080402030c010f0302190507050f0309242104150c0905191203050a0906050406050d05060111010f0605030f070b070305030a0209 75
    0x8004151341c000c0d421200c004110705000d5a08001140b00c014055961180d003401094012980c2050391f0321703509440182c45240c030303000b200742c90304a800c9039015005800c50a40c0ca8405690350400c1c00d0044410000c241c80203034140c1c0200800c001c2e5035200344011001d28045040252804400e000000701240c03050840ca4001075000c40c10340308000061000c0c0140c0304030a03005504001c50a400520718503c2a100c101801d5803001c1d001c111862080b0650320364290020b00004402540d5501c00d80843e021036044481ea40d950404c080c102c1e900384201003410300c2c0d55035101d440c01e0501c0c0a01c1580d210703802da414088801c0400014200b65100c2c603800c0c186220381d5420f84c03680003400001e8243c00c80780d0080e4041c803409001c1031051a034440c00356211403100e00004100b5444441c010f07a040ca0551000d41c1c055404c0c030a20000e40100341d04060304842c4140c044a443d001540d40040d1105454001d44401550801003d80400d1007103000d5034003c0c9461100600d4010300400081d02108400c4401c1c03d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 621757733 1250 621756483 621756529
    0x1b0a0b0f0a060e1518160e0307061b061401030b0105241902070302151201060512040f02041407050c0c040524010207170d080903090d080f0d110711030f0a0b06010c02 73
    0x1b0505600c0316031202e440c0400d50061003403074180007000d410300304d0380d030020340d00382440b044028180101600030506000c045444082c40c0c0d6141c0c2407600610400b40580c500595000e03d14010886100d050908501e04030078086050040e40d031612400030703090700380f07450841c4542c000200c0940d82d0424040004c440c0d400c40c0c156126260300e52542c1c1a00705a0100052010500840d00725900800c403440d4040d134070803c002112001c520019008154034020303030011184100130402aa07400000501070004072508407030940300700c8001c02055490484030503c00740c00e186071951105651318982507a0442c14010307507403400e890721445121825145065019603000541c0c1ca02c2807030700000810340005560300558600bc0710071001c1030071240c822400030000100001c00d20711600302d00b0259109598085010b20030001c4245845905800078007003526042c014084698251800051440226580340b000d071240107110b40b182c00c144040188201d050100c50050740c00180c5e0780b011808900f600a08040c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 621758983 1250 621757733 621757771
    0x904060e07140301080a030c0f120804030e03030405060405040b03071d2403031b0304050d050304050901090501060c0b040302070513020d150602121b0a0b0f0a060e1518 74
    0x800503140300b00c69a01d241c00c2000184490040031800c41141505805c00e041c0d00d03e11490501d51030600395801800041d007400000324550361061416020314020340d10022000c00300010103459114510a8603841641084100172908042c0c00c255074a01e4000d00350b500041d640c84100108101502440c070755240100d0422508502c00d543d4106a01070541d260860008020082030b940d2251075200e100342c0c8440d01004c46844410404c84000d001c0c080c08454503120170740303400c036941e411034082d9a00c86c2c140c540012840540c070344642c81c100e4003540e1b55041c003c0419210b044426401400940c00c50041d844003042a45521819004c8141c0d615001640ca008002058046a0100e009a00b041c58440c03402c200c2e0660002c0e500402c000007a04c19a55620100721400d4030079042201003400d4020140ca02090080d4409003512541c03880348014007a5a4419103502200c90f14061a65401445004580621f0524030300850240c0b0141201301c4501c036244120b5107001e01115a44450000101c007a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 621760233 1250 621758983 621758987
    0x110903071e14100302160c1d0108010506010509010c03030603172701120c0306080d0203030709060513030305030703020d14180a0b0604240807050a170a0b0c0904060e07 74
    0x210004050707124802082895450002d0201032500b1080350404da0045240018890101d040300e02c2c2c40d40c041030801185686116100b10041d80c91210202c0201110000134014818051640b08510507500d40345807c00100054511a03403c08080d000c15565072400301c0082d0690724019130002096480f940c682c2c0300b102c0078020003200c0701119400d40e160080140400d0342c00c20340030a4180144030300419a041400d00c110000d10060744928503038403501d40824085034000c0020341c09801c840e9a110076254403140182c91074820040310008111034a20f0804c007180c4245e0145800201c83d18000d494131480d5075031030090310501151047d10800030300c148028012000d01030345c500450003000c1c0c485554552a84242ca51008080c0386c0500d031512044001400d040c1e0380390480740203504000813000c0e190b0038082c0c0e5400c41806181c0c015507885202049943c254054446460704060042080c2102d136980c1e041c0c1d170203000e81101400c8006118005260f42c441c00b44001030260229009024a401c40d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 621761483 1250 621760233 621760289
    0x60105031803030a1b1803290a271502030406111305010905030a020108040b2701020316050405030604061d03040b1e0310060f050904020d05040b010806011811090307 73
    0x2000003484842d0140200390b010100d01c80c001c50750020000d04840c04080230002c00540b4030f00b40314000c0c800030780403c503480000e9801040344100b0000000500050b500494004101014029010600307104d000900c840312a0011680184070309004202421030f2103c01c2c54603002500001c030310000040051000c0c0d43c2c000c0c07016004042c214000d210a03805a00081d020050142020781200c1c88100020625441080c4c074120707042d001d104084888042100b0f8500030342065485030701805007512204005071048040d00d05a40d80203020340601e0700d0303569418005142d030290301031106480a01d80404040e060014000070801030302d00c181d4952010641d003114020036000b4610164050082c8258003044040c800705440140c1000416210a82800d4849002d03000106038007e0001800c070b04d803110301e034000c00c2c0a148516248403850b621603900b90b40f41c510034042e151120820300384104004180c2d411050802d02d4002c002c40c50455180086400c0c801c103904480220f00e107808401d40c1500c88041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 621762589 1106 621761483 621761531
    0xd08090907110c01030903080c0c1c02030a02070807080a021002010f11091c05030d0b010c080703020609061008060a090311100c020f060f060105031803030a 69
    0x71009240c0310000305920350a00901e0a00d20310b80d406800368140d4030303526468a42c41503480c00d001d5061904070781c8055400c0d00c924013000174117a008008074030074488035501850740e0300000d90003e490700309554000840769000703070400c00080001140340054654100c0d031412000d11009804ca015107100c0c0f50040146192a2400780f40c0e0401d10001c1c0380911090320324070030b10b241c26020202541c48242c0003031308a400c00c0012500d0340c001e40d07100d80041d007014100720100038a19250117070703070f41c001500444c0941d00540500000000c100001c1354031241600c00d0480c03841c2032070b240c66100c0740d000d044a5041074079000d4603810580110f250100a02e0040201c5a5410389010300320302900280c404032001d0b01804003500c0082d100450124443d0b131a40d014030302184c454800455aa500c01010700103151142040c440c0c4010301803004500581d5468008100e40f0189035010131030500d061 = true := by decide +kernel

theorem cover : BRFrame.Cov 621582733 621762589 := by
  have h0 := BRFrame.cov_init 621582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 621582733 ≤ n) (h2 : n < 621762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
