-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2526
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:58:12.414655+00:00
-- url     : https://prove2.me/submissions/54662091-0fea-4106-9433-3c9c2699ab01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 454136690 ≤ n < 454316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 454137940 1250 454136690 454136699
    0x240105100e01140d0501090506030609060a05151507060b010e010903030302070c05180708070e130b010c060c050d06080d050313110607120e03060103050c0d0804030510020c0f0303060307 82
    0x21030685507503a03203040060030400015600d4000b4001d140034440d01c0c0300005c55624016406c000c03148080c06803446a0002c1c014400c1000c40041d4054110800903c0000c80d80c5450551100704d002d03018070703140c100d4034044100140c41c40f0303140600019030240d81e0a00c45040d25800440c1d00510384d19910740424840d0710103101007446035000c1c01d1010711a1003c0c104058a6000042e8800c11030705d6842ca603801c4840400c4456540000ca5a40040040c14a14200301d0560001342c500b00540c01d4810715030756281c82c40740c126840703602009005a0031160400c81c00302e480c03070014500d03804111846045030070f00400007090b1800249600000503213549090071a1111054086140c010a009072101540514016401c0d5a50401000b03114400c1380059500181e00501030f1041c42c0416801c0c1c8aa0043c0004002150000c02e481c10030020031200f41c0802401d40c40d011907030340a55040640240316030080d60440000960043c4501d110403000c8500e4103d800d90b00d20795901c8115025038040c1c110810802 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 454139190 1250 454137940 454137947
    0x506030706020304150509130914060f0a0903020c09070503070e1c11131e0518100b04140921180f01030f0f0f0f02040f0e0603011d24010510 62
    0x3092079174103180051410f20754034002995032030220020407920b5075030b010b98410400c005d2102003400484601400d030904d84001d0340840c40e24000d202040c1551503452400c105442841608880310b4002d10740201414002c3d0020181d4000715503240118010307a0f41e580306403811910100c03004103080010782c815841e6685100b280d101c47d5a41a4010100100034080408140100080c0d100310089502240c0c9117400500241c94000e45180104014035581c0c0246150200b4006041c0020f45408114040040d01160003810000c030040881c40701030041c4400318402103110004c107171408003a01049864500303030a003a0300c204400802404590071380340c42c150030401c0200c030500d44141000203200c1c41c807070450420740b01c1841d0884002555103c007143e0309030492107019040c040d070000450070141000c003860020750ba18010400b80c2109280028031300d545c250440b4401d4842c1d4183e100398002e1050400e552903040c0c082401460140f200400c500ca4901186e443c12980c0042048006079410700054 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 454140440 1250 454139190 454139219
    0x6060311042009270702100b0303070f081b0a05100b0d11010203040b0f0309070f060905011b050f281a04020d080a0203130f0b07021314190506030706020304 69
    0x1c5411039541302080c01c1040c41038081034070000700d800307060340c01d46800c1d01c0003400c0084821b13a61170154500626080d480d2000001d80320340b00d522403030016228070942042050750280b00b08030010800c0d40200c0300340100000c0787c40d0520500c03c0e41202c1e0381140e600446810340d08030100342604030a195400ca00801c1d040caa0030307075041c030041c015240342580310b850528846d440942001010350340002444109041000740304000c0c00000510741c04103040c020014403000503480384904008421410002103504140741c00c16180e800b508603460086000001074841c030031240b00d12813901c0307a610f9048070f5841c000d004801540d0302030702d80f40e020714491283c840520800380059800ca049041e50500149801c402411100f21035001552035440c01c115910500c4010b070016405191500c1c800c00c102d21441040e22149517044441c2c2c89100201d040f40c0c0020508010101c001030030310800d00400d075402051089a00c48203c40070320103a80e481d42459a038081d14880c00006901c200020007030742a510009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 454141690 1250 454140440 454140457
    0xb010806060603160c0b1302120d0807030e0106080a05060603120c06040b0c070c0e010f1a2b02070c0609050319060506040b0307140102071e03030c030912060603110420 74
    0x417146424a4440e80d1040d94100c840c0d0b1860304418583c2815460204c03124840e4000807002401c1d0305203100001031404502409000038940c80b44044488070400303402401c0034003e400116494500b079401c019948150907281c59009016143c410b034407c01050007151001080f81c001411651034550f00d074400310000070013841400909110000c0000c0543c9000030090203207095684180d410306144462000c26544003407020042c00c0380781d000440c0d10310306480404108440e2500840d02c0d088410950302c00aa1490248500c00241081000070200b030070015615241d85d044082501c80d01416950a444040842403402d150f4001d400220350b900151b0b8002e2002c5c0c0080742c08032040010a00c2c181582d080160422220342e07140e41103590400202d00107050318121145041c140d40d104c55000102c1d03000150070007000110b00024103008803403420081000392980348541c03c403401c04100034120f5020450302001150700416291415000d854003220000c0c50030381c18048074071200700e070f6036200382103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 454142940 1250 454141690 454141697
    0x6161106130b34030c02010e060a05061f030501061b0228050414010503010509061612060f0b070614010602120c0109051f0e120a08070201140907030b01080606060316 73
    0x288030640900c1d12008103400f940b454100154403800450180545100345101400c582c584405001e0507000000d0702c9812801403180042c640e240e00c00450f8200c84d040c2031149031170802e01c2e070f00900c50b036050f070203541224001d81d43c6860200b90b0030054403404243c1d045c0a0341c448011274500c0e92100700100e406030444640da02030000d080c3d85402040030355100c60910040344c0c400c6001000300d81021f0003420350000902c0080c156900e0003000b00c0400306a2520b00404216109400c1810b0a82c1548210058121800102070b25642c484043c1ea66074401ca000f242d030542044910b51500c50300954071410b8a445070050802034440d00794248080e004020604015905e4191460100e030051000904104120404c00350b01110b05940b04c0075107002c440c0d2001d40d50f00c4961450358540c4510140d070130305c1e05030789000100c54031000d004902520014800b00d0410410009202c1804c100285107411070344180ca0340300c4141e980f003a00c983c84074012166603421038810400600c0c103001621140c840c200740740c103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 454144190 1250 454142940 454142971
    0x80a0c091a13090b0109050c04030308070c02040501030b0412031a04020c0102040f03050303100803070201120506060c06070509030f0f060103022407030e130209031b1206161106130b 80
    0x80081e56120420804180483d51885810280a00030039801d02400d036041d03044c0300c40c0c10301c007881003140e118170320020b01089140c0000c03078801441045079181407a0000d00c1840300d96142d050408041c00d003503400f00d0b224010080030390200c5000b406000c480b070180c1e1000c8144043c1d59400c0c0400703984001105d5500b035601304004034076001000146c60285006200441e101d01d062500b00880391004d8100e00107035403062224600507a030151002c0d00315816007501054a44846000c65028028807480400701d005500c10000f200d540a009400e040c0c80880440d958a60300404490f00c031443c040d148141034001344010702c013506000380c40c0612440700c1d415104815442e040c3e004c0041c1c0108808600240820501d1482031a100c000c0e45402c0022000c114a0324145800185d80c944811180c0109807800f060513200c00d603070325168518998140c10070b0310071f58503000c440c441c1500c0d400b503502404035445a14a03041c1c1e101c00503403e4494040004203244e8003005443e50011703460020f0030f43c0182c10031030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 454145440 1250 454144190 454144241
    0xa0b0907030221070b1912110c0c010e01050a1e050c1c02070e13060f02040902040b07060e0a0804030305180406090212010509060f060c0f030a0203040609080a0c09 72
    0x103000208090b281100c01900b41810166600e0420440ba404007803804000d10803002801200e09021304060007d0800754048500c03005000b0180c0040c9003507414040740410302c403202c0b21740400c5000d5010b8003641c031803d264191100540782d03070150708084000030300e8410307011000c0c001304d003035076050b00d005401c00a04000c181d0a10615084088040c90340ca00c0f400c1c50782c0503401e601040504058806400e281ca903e240c500da05980b902d0224001070300b05a200c038000c1441442680c1150081c6c002000c1c191768540d102c0900ca05160f010b88011141c4600e010781640d01e011000c61580130455100d44924030f4207295403000c40c3c003608444408502c42000307c902c00700310340c0d4603c1000005c242015000d42c8613100300100700304801050380028016005d140c108942c513903640c2441c1107000011203605803585d109944a62504007c41d0012038680310000d07041001680010150045502a64810a81d6611161082d8031080034100042c00309071540b006100b040000e400041071a51008980300020010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 454146690 1250 454145440 454145449
    0xc07080a18080d1b020d061803090b03070512180601060e12070503250302100e03120403080a050a170a0218091302010c030903080d0203270a0b09070302 67
    0x304080045500c4000081e01c140c101a59103000700520806499848060880905403102c2c1069864a2042090380441150350b000c44000015802400c100301140d50300300400d0040c240031109030040f0740e8083d80011010005c6080b02d1003100c0e2991183d00380ba002c10070240925070040e0207190903003840d0481410800707040143c64020041543d8041c44907000c0d40038815684408280b40140b034220900610540d140000d04440340154920801016403e204502819450700d400007036002910403441200640d110301c0d000c1410310100c0545102c1540c8482000151045200003020b0103000d2107207450950181000e131980040c0f50428842d4803a80001c042000c4008a0700b440d84690302041c0780d21001d02820420340c2805040d00c0380d54580c01c2c40315111003549000100241041180150041010301c542500002507030710419031303511840c011001102a40040f45c42c10303a14401004849502110b140c60b00020f03111460103030140321510f443e1074804e000e0060040c001481184400001a03c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 454147940 1250 454146690 454146697
    0x501231f0c0f050109061a0114090301060314100b011d01030b120d0f0f030902090619120c0e070509010c020f04180309031a011a0d090c030516050103050115080c0708 73
    0x100700000282050185040011104441c4504042c4800c45208000300d0343c100f04d6a089c000072684805480740c0510000038090702c825000101001c2d030007040c000c071400002400000080407000184444401c1c000116030f08061000c1e18001d222000c14280c4040d4003a0b8012003034030380d01400624000c081040d000e0319082c032214040e40000c0351380c0c0b880030b04154880740451014500d4a018080c004203030300005c08807840944400e204d40c40010404810316103004510700100204d004008554802d0700700490390030a5841402d02440d44a00000c03446440b4908032525030105031185055600c20f41c0a201080480700441a000741d92a280400d100c41020706a10140d440303556000020350661405900e08400e441814004000c2c2e540180040054843c6c00e480c078003485c4001d00e0321142d0096203080501142c0801800301007492001209000020482c4000d825030140880180740c1e481d401142118402d220341b80707980d40000c2000143c944280d90658103c0e85002d81c481c00c0c540c0c4d41d1038480460f030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 454149190 1250 454147940 454147943
    0x60e1b0322120f033b030c0a14120405130209010c020604090b040f0209011713080a080f1302030718020906030a0504020a060201050402360106030501231f0c0f 70
    0x40010908140455145c0907490076025003001182c0c08801942001080003036030000480800b041c03c4540151030420000c0d21940c00718841250298500ca003800c2010074402000000503004102030310f210455140225400c60301c01a000d600701e00b03902540381000b0340281a50604210280d551140540d45140240c00035004055001541002500401003190307603140c1204202401400400e00d107a030000d031005250011880c00d4820ba0b99401da000918480c0740b10014030281010890f44810b591100f0072500c518496540e103100c81e16000c4404021241030300000b035140d804540c003400f01c0f60b0440503000c07420b00410340260074043c1e4100000c426410454a02c0007056a0b02c0401081d0b00e0502c1c01900141100d000802c00340c200b680114a0315030005400e01103c0c045a0300c130300e0840c3d940b24040c04206030551110700c1d140d611000000c01801080c8240c2004030303111100e911055045c0b0b0319103064080018280350040a040c4411820044411034200606c0005180d98000c5100d110440e600e09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 454150440 1250 454149190 454149197
    0xa0b09010f06170604020d02060c030408060a0e1c120f0e0a05061f0905070909020a03050108010b3c120303060a0906050f120111070501060e1b032212 66
    0x480700d612080c080302c41e03d03030012980c54107901406140340ba01180040e00070340c06956648040c2d4103400070510324414003260301c42030b11000038005048640480d465002d180019000d01604084181580d0380380e664181c00d640028180c4401082a4040e00462811074441030f00440c8000b0100c0c4d8400481d004180e100020790480b40d2050100301003807015560040d6880c0140881060350a1b034006403071214042c1c2000709030b1f100007041c01d041c00369203100f00406603034505654400028a004000d00000e108004c015070030403c04400c145031914038031124142600c41810400503000d030f652000d80c800d411a0701e0000c1c800c0c0044240d40c80d01e142a00a860b000c100455590a24905001103040903a010040c0c2520b0090240210354441810884a09040b25a461490000302400c3d0040880c1c10309201c1d0158001242c2c0100103040d003000c030440f420340080c0481d56441548050301c4144508003900001c80410005240c48a541142420340700d58001c1000da0000d503540d11810446010300c0c02020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 454151690 1250 454150440 454150451
    0x7092606010e070906030b010302121305120a1706041803090609060507110f0f0a0909030e040c08060910150905040506030f071802130902091008090c0d03020a0b0901 73
    0x506004110150040000e2905400140b614500c028503031070240c028002019101c10b00000113a201c4d405840d00005c1c1200c0000742800c105140c0703400c403000c01c00b0841c2d15000340d9100fa004400580191154800c40b501c444a00b6450400c0714040454000c20700c03540256a040c200701e4603403942c803000c40964400d4aa034100c0300d04009018007056920b0340311108220b0100403d000141513592002180340e0140c8018500c1c03020b400c0002d031000e1250104c907030061207051000441080b80e400440c00c0341d000e501d4111940e48241d0500007514a5510f010001c41c0c1e40b5000304225040040da0b040e48803441d03040340901561100da448040c44480200c01c00003c0200000303001c1071425125040d0072410850050011030096a55262500002e01c00d0030a02040342201c40600700d4190100d131110a1500c0c0c929014030780b1003170080001e4000c40c000c540075901c461200fa004601031048a40070350000d000a107284c0e9102400c025400400c2c150071011801103035650340020b5584541540101031202c0080781 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 454152940 1250 454151690 454151759
    0x70305030705030306310c050d0f06061b21050f0705030406091205061503010b040e0f0706080c0403061d0a1101020f0d0e04050a110708030708150f01080709 69
    0x805900000501071100b00102e040280c6e00005413690000d80c04c0c03030300200316440c81c0ea00c1584c0070700905611000341420484000304004407a031011090321a40c2e1605a5405c81200d00407807221240030f801004195030039880d1100703107000502081c42c3c289514102d450000c00600c078001c1ca402510b0112042c1d030010506102c40c0b50030a48071001f9000c010180c01c40c00b01d4035201c40c0d41d581400340040040b030581001c2904152421340007140c8501000c0c0092200481da000103076610340c07982c01c040849000320140030607058401e100c001c0c0580a40301c200c034142801c5486c1c0c68020f20340d402c40c03007003e080c080c0300f4980c04080074001045100d005d8100501c00301f050701c001904201214154500580003030b03511b0030035250040340c0d0140300401524000b4080d510040d01e030000342008802d03c8800c100c003244001c2081350900c011413151290703644030249a00c0324a1042885801100040d03409500602c40041c40e512030840c069200c0070314030b80080701d15076800320b101c24080550416803804015400540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 454154190 1250 454152940 454152949
    0x1030c050904020310050703180b0a0f1b030f0204030c0e07031103131b030501060806160e01080a0c230d1506081602010e120901020c04050705030a0e070305030705030306 75
    0x900030003055803034401602e01640043c0e03c5941c0780142d0040196100c002c551000e00c42e500000c0c2003051400340302e00a920311305285804040c2150030803031082c01c0504101c96104140104a1605a4040544001c10a15405502504008044191042c1d00703010001c041500c65052000401c4290a53329060030038a50003000e82b09107035084d0742e00c21b10800c14040f05400040301401032580205036200101003661356030348020350661010784190f09018010540c2140070071f03400c6c011148822007100300640400c0544103554000c64542c0482c00c0c5c540040da60080c2a044079294000d245000103040d031000f80c80a95500c0b08114204003110041180406c9914a100f4450a04c248502c00e9010781e00c0c2c01c900401c4c428001340101140b20901540c0800c0e28000d41000f414482c3d0801540d6943e52004c1040020390005034a0fa0300612803540d60300181e080c94407a20780550800d995417840e5540c1c50b88460b024290018401045200d41940040403074003c0c405004158410000b555803400c0c20300400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 454155440 1250 454154190 454154213
    0x40614090601180b22020a08070c0201020604060506060c0703030305062409010311070c2c1b0a0c0b09010603031e0c1712090c0901080304061d03030c070e0103 70
    0xa0340396400400140005491100c0d1680c80c2e0b0007400c1c0c04514085108040388810803505001660170085000d1440788510f00d8001d441c0401003540d8080c4240c1d00c2c06070850f5006403403100071b400b6030015404180803c4940c1c10403907100d400030300100e14041d4898400d034a4101b141e4400c0c0c00284e9a60240700c810310307102800544041040803503c490b2400304d0080b101600c20350024506040c3d403032000100840070702d4140c4040d581c010000b0341daa550b0b03c85481c0d00c0d0a40c0d0556500c0000e403948040d025504400a60502428060b842000035101c1c41d031a48059510826180d0180309518084100082807010301c03512404900d40080303500d521798640980034800e401000d07549070208441c7d0211140c2d100c01c0d4803003d2600304c3d811107072032800a4040304180c45000a0180c020f05950b00300041c81c41c0000d004030303240b6020f4803080c1180c0c2c1c0c0c40900c140c49002c0d07030092100180d0003480c103a0301610542618007d40c04001d050700e01c3c003000c901c8000c0c40d000700e940c428542041c015004005000040606 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 454156690 1250 454155440 454155451
    0x1f120317010f0305030f0306012c010e060f1902030c0102040f0906050103020903150403051903140906130327080f0706141b070e01140909010b0906010503041103010203040614 77
    0xb00c0000d20309541e00c4030f40700d01400003020315100000c0b0004596a21a9070307507598a80c00b50b5001011011101c0340c000625904000007804159a00b0f201072a5003001e80450f55103162040b5587e04050308141041026407504100e00110b220621418800c40801c0c070040004041c40d0b00d00c1255249820100b000b0b031801c56000505041c0705000070109034501051124602c01c0440c6202015a110f2405444a00590040c6207043d03d54002500e126509944807212080c20540d100206030317901c5000315503566003200e245d940c4120f41750016000070f004a5005030314014003c0180060001011850141080d9510400d80d40d80728804000804000f488820080c10051400a08140440c18020083d1003600c8646415580b85c80d01b800e00840280008009881d46410038007055a603080582803803200e900c00e2501c28490000454404501485507520b40306003e40042d17810381e201c0b001580d15805c002c0c0141c0d0b100041c40400d4046e80d501317100440c4681e20400e800600e0748461440d0a40c01c0300014030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 454157940 1250 454156690 454156709
    0x10605040e21040305070308030c040902071a0f190f0f050f1006050c03041202011205150a091b050702030a1e0b0f0f0c18180a0b0a0e1f12031701 64
    0x43c00170510201d032420650382c002540700c0d0b49480d0100400201d00c6640d100303036599407011452804010200d11440b01d542080010301000e41c8551642c590b1108083e14071000c5102c00901d0b4284040098010b00c4c880e0b083c5200c00514003a84107010380070345074216441c05e03051000400300326451500902540151410346081420514103e02036550391040f400b85c200d000d40040302c2c20701160f101e5900602c48071100c00d002c1c8070505100e070344074079990100c3c0c81c1c4a00c2807015103c04103541d94144074a6000612540b4802d00c0c00c0340024041e202640301e96410380e054080d4161540c0400c000e09802c402a081e030161000e400c2c0c5680c1015072014801401801c2d844005c08184070540b154012208d4012031580240c680d550000f803da01c1c1010206407615030400c075003180001d0b01c011a100c80c01c4c03180d4844031341800840440020080c00061078000c00c29040490004103e800c0592245985004e6100c0b81500c41c094640c4150180c1e40d42240c000c90000e1340140e40c2034601121071003468010840c121 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 454159190 1250 454157940 454157947
    0x5070f050a0c0f210906050a050904150503030705060402030c090f192306030f070312080a0b060408030306030c10021213050d14010b010f091403010605040e21 70
    0x108000c085100e280070080401009085203414416540c0d125052290711408524618010411500d0a0f070707103041455012a803805800121a405602222181a0659959031414644000300002480342080441404d81442e0010030701c0d4a0070002000e009000350002d001d6407030b040c4101480c14002c01c5c280e902980c211400d02c021060b2090360f141e0050f209940b03035030408282021030300007058402c103d402c03500303234100307a600b8101030341a1054001c10043e01a61800310010b400a90b84110a00c40140b08070740c2c1c3d620300d142d214480c41805800914500012507500c000c1000030f125078200c1e8001d031b62590800002c1c401307146000c004044a80c8019030b02c846c080354403450701940390712401902503a03a5800040300d480c0f45d9075020281010340310007800e1118040441c00c4c061203881d05000204101e40c6020541d11841d030142c0f400d0340230311a00781d40d0109120304040504950600180100d5055900c0700000724490b070381e90259500c0c189080000700071b01500e54600701140d0200340a0300480c6031080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 454160440 1250 454159190 454159217
    0x203070f23100c150c0e0111030f0a080a320a0504020105030105010c033c0e0a12050a060507120f02042102120d0507171303260705010f0507 62
    0x1c4002c0040c501c01e030410380941d00560030510780110030300e005041c1141c0340070105194150858002c0400079001c0e654078140e01c10942d8142d40e2441070008100c0340c194180420710100d84100030240e031080b0a5032000c1860445d1200d211310703840d41041e03100b000e5041d40407031190810260100c83d80c020a00d102c18452810f2a80004c0c1061006000c0d00741000320350034011080c14010107507110250040740c4030700e43d1101b8188180c1c0b5282207204002c501e002000e518108030902c1068640356055000740384180041c509003c1061800404034204c030070340a144001c2c4003082c040c1c400c40307128026039244c0b01013030802d4000c01000ca40040700300d1004140f05100c01d200c5002d580010b554800001100138060b0012400003031900c5072245440002e9115411104240c00c0d840340161842a200b103d4200006941018170006401400800000304980740f10803c0070540d004004114440400200e00300410300c1c480c6401151b04c00c2000380c034240c2d110141c4d044503091a1244d40e0703000f500380c42d0801503442030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 454161690 1250 454160440 454160449
    0x210e0f0f0411042301021e060c0307091d01052d0609060c06090c030d0e010206190f0c09080d02071212140a0c03020d020718050c070203070f23 63
    0x540548500403079480c090310080c58202d60440d40605144211034503100d003440102c1c225400c0654000c1e005010310740640c08442029010104801c4548015004640d0340600102c080c0d00014800410000742c410001079174a80303126565451030580c000170700310398140030a12080700043c80401c80c40307465212814401528102e1400d01000302107603001da90f465220000f40182c090400007060740d00611080c8103c4810001c0c52644500059050b42c0c0341c81c0c0d03820800e070303184006840c2c01c40c0540c02c00c40018402000c0c66602a00380e0000300307130014402c080d0703602e408101d0714802000000b0820004051100110410400c01d001c034080c8024070f2814103107100f2544c0c03000c02071001004001c4009000140d58002c400c0c0d02d4450b503054030400d40b9801d503420014411241c0c5402070340903008046210540c2031020a0000030758020103e003441000f8600c181c40c0c018400109901c0004605201c41001a0350074482c050044c104000e000c900641030604010b15a08540c0340c0c201125050310078040d25895 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 454162940 1250 454161690 454161709
    0x3021506031c08040c050a0810141312030f1e0e300f0a080103060c080f15010c080c0a0b010918140c220b01020105040c050f030a210e0f 60
    0x60340c40c03e0999601c0d80c0c0385c1000954103a4010650050b04130a001c94011000150000c48444005040c89840d07022400388050324010754100440d1000b600400020480100308400415054640090300d14208220602111600c00b4400411410360462407000d654074007a101030880100080d11906420100c542c519101da4114550311060742d00300602c010703903c04140c4104071902802650b4130b220301040240003000034002200c42624203000684200d01c24a000c40c41004905c000741c1841c2c8601307807880c500c00074001015040101c1c47c0c10741d90009104401800b00040c8450041451414a2411500d4804160004240c051030542c0484031082954040410b003504a41a07080112110b594542000c05901a05e03400c004c16551014250340343c5441d40c4070512215800700140342c0e51000490030b80d64151005030550409a40501c024135242c100160082c40041c11601501e240e070351034102451900c5c1300d64521a60008600500d0ba821003018100004200c0d811000c200d842c0001804104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 454164190 1250 454162940 454162993
    0x120212040b1f0801050103060c051921140a0b270411031c09050102010b24070203100c14040302011d030304081f150315050c090a030302150603 63
    0xa00700070105040d0700d4200c104901c060003510001e034685854078055406410700780301c11945185040c01d0200c481d4450001d03540300202c07003118800401400c0504990130544020780800880199503c09c417400560710486050020804242d082803030155045802c03910404045030140c501c1d5003600e4a0f400043ea1101411003085021000e50b84860a0080e449a070166400c3e4142c1700c0c40b032140343c0070581c111040440c106603079140491147c039031004a0a9a20118406030007030a2010110b00d0b4540048902d01264408070110b800c201058000900c2c00900102c009034140d42c03207600d29001d65010855240d40444031a14510f4980303154002809410086a0315030402c1070003a2078038040d0303014021240140454000c4422102d2101c13100d00c11103003c0f074400810a4540103221905108800e80341044941142d980d24210385440501400390500070589810300208009504540d51403840e0b401c0a0340c080d6004010150081a1441c41154040c0c00c052280d880b4149401c0d003020485005d25040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 454165440 1250 454164190 454164203
    0x9060f02030f0a0213120302030c010c1b0215130605030103050f03070f0b063c040c0c0b04150207060b040515061803030f07030509130209030a0807150e010c12021204 73
    0x90f1660303440c03003901c03a5030743c6c02004043c0541c1c0c410105241c1d0000180480700708000081002d001051000c3d21141000d0350b4800d84200401c4901c00580381a07000c4603c2c104014654900d0580908901a4070084503040540441d80100c01071040c00000c10400002c000280015440c02c8040c3c0c0343c400e00c8070484400241000c0004000900340d031508100c644114503d8072050144982078603076200b4000c40c00c0081841c81c02400c200306070380d00d428050708460a49545914045496a8540d1205d1520050007900c0d0300c403203c0c5400f0090b06042c0300400310f4501034072000a88820280410081d180301401c441d00074004a44042c80a82e510310840b00721710100b44441414260642c003090960154005c40c0c000b4550100e4900300f410740000c000c1c501260112260b04400840070080001c9021713100c8219019170241c0f01031800555098000d09586c2e000c0e100105809180e10031120684000000300c101c940d4446141100e00d50304400b50720b0505114400545c00c044203541c000340520300040c0060240d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 454166690 1250 454165440 454165447
    0xd0c1107030f1106070210120c02060f0a200301120c05091005060306040b06030a0609060501050a02100225031101111806220f0303020601050d120c0c05040f09060f02030f0a02 77
    0x2590f030784d108071060564050021a44c04680c2c0d00040d10116460140d952181d0401200c071809510100e5803134414084076008040917113841040f100200941c4420000900c08000d413540c40818480c040c5000f84050048907990000510301071941005941c8400d0080c5400700901103645054008181500c4040e03500304d4581e03440000003805000c0481c842c40d0400c0000041c08010846504407005440e9094414070103d0790350001103903103100e004084001600105100f0380031400c150000e10303440010700525021200344c10f080103e800b079201030480105031b541c5d41982001c8400c3c000c00300101403c1c038466082007402c00c0c00d489102c00d02071030107104150004400c42c5d4820075489200030300c6200c99550407015294540140c04041e00d003c150003500c1010000185880c0c07d0700e0820311582d2040d1a040c00010f0f4031001e44859031440d200b21403402c10380e5404035450702c0d1071080407260542200007103044103080c1800d008031418040202101801003040010198a000e03019410100c4c9100050741c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 454167940 1250 454166690 454166723
    0x30c0611070f06050105060702060f03040f02090a020d140610110307061127180612030c070905060604060f121b030207152d020c030d0c1107030f 64
    0x24565100c14800601001c1490780c14040d0491a034a0894440e500410590341c9030410024180901ca2000398065020452181483c0c0304401854220f4030540d451005401f0960004280000c02c50b90140056800f0a41e0645040c0b5409841049420303085400d44508181021442e4123500080080902514050500305210100100c8500030b070003c1c02040808040c000600c59030b4400d0030b801d5805403003203403980041103100b0400301100400825030070366400300c400c2c0e5000210000701152380c82400000f4204110b0028802402c0150410014101046c10442184200c60b40a803405005407800d101c01d108117078115807801d4541e40c41d410017a1880c0325050320301c2c000d41203a00707075004a1640e0054210704039826070064400d0394820b0003144110840c242c2a0822035003c200d28210020703101303094000200b01b41e00034505d02408680b01618060258450b00d00c0e540c080700759800000d6440301704100e200d034880f0300754003401500d4015005991071600c0d80000d920001d02d02030107082d00d43c0d003840c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 454169190 1250 454167940 454167953
    0x809010f110a030c05070b04060804060c230405040c0206040b0103060209031c030203062106220501150602061311131b030515060909010902030a060f03120906090e04030c 75
    0x32901e6050030480348680710518008011003a0980308842500c100342000c1070b2a0540710903102a070b1030135921220b02c0e680d691610009405210382d40c00500c81307030305600d000300c94071b1070304c0e502c04105034070421603545151005110032208000d0f4110110740040c010310000a200c403070b08504582d0400000341c0c5031505400041d0a041c45030440b03240c4420100360300711506d034051b0041c600c9060304481d9400488403a9a100c0000e2020359601d11242c1c004000251503a040a02d8901d462000460024008081580e0342c40c21100c1010840c202c0b03100081c020400703075504020351580070b4856801542450b10590391950b20144003d4002d114111081058501c2000c5510440d480d6100e500c003241040818200940240002c1e140d04c190340350500d0000e1050b00f0040100c0d0710340100075040c1001e5a180c0b290040007500007802c68004a500d40d0000640c1c04110202c240145010b2402400440c00030354024003900440e61040003804988202040b13101007038030301d40768001d405040c0b41780071198900c0d262 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 454170440 1250 454169190 454169207
    0x2060711031216050c0103060b16060609091407050312041401140307031e020a0507030c0213050f091605010c0b0711010606021605060301050d1e0203060705091c0809010f 75
    0xb0214440d003ca150988000c0c0d0711402140300d4081c07816140364400c010011829181c3c0390080703006014003081000b40025403030401d0090340d40611800140aa162034483d0300703984c5000010b0741c51a181c10040a641842800b02000400044008000d40c490111804100f03003d0307445110703410074441d0048080f0b80d015118640c1801240352103141d4910304403001400403c038044100c80c0400214010340d0034840188200c941c036030320303a4031203c1c100422030381c00712132011041a08036002015000d90f8505d1001328010309004010154280f0611718080784182d29008800b00804404d0442c15410030044c2d03001840842e03003c0d004031b0104030b681d403038010549404c1074900102d88150b04c2c1c20300c005034065007c280b8203400715100c0c0d40c1c150f090360b40301d00b040940d01003030003101d5001c0544042c0d100080d0780c0060020340d034201104a030f4505402500006d0500100700e4080e40400c000042070681403501ca1036814142c42035081b10040060291291811070149a84031414040340c40c02040041d03002e200c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 454171690 1250 454170440 454170463
    0x14011206091203052a031911070308040203160302090a090f0f0507081009050309040c020a06150f08010504110402030c040f181401140103110c030d091b030206071103 73
    0x10042d80c80c45410008000700b03002c955075040d441c0550400d50b60b08074080d680d1194001e25100d80390541c0c5880b406044d00307100100b00100880c1c0c1d01c40000c034000e2102005050401d0207602c403601685000d006040c200b000c000710621f283c2e8a082820310050b070314003103503581115100d0400502c0ea5032a280107440790b0360103500a01445050b01000d001c201300001c1110a9411800659040303000901986040c0d0303840100c01030158209000d0a401401c00343e00c15417a030b4003241304868100c002d64071450125a0381c890304010480c00900c2c140105006040c1c94401070403008020045841c0a0b180c07004072020221840388125000404103080200e0141503c01410309610070b07030000e5942d01070481100d0458031104400c070f82010811b40464001c1c0c0042d5040301c7c030503603a407a0500d0703091004500401c820342c0380c10740c403000c14000420450707010000b5040070303185540002520510341c00c1c00c000840c1e0307068402089010010061005840c0c140a031010250b0001c032442404000381c00003414071044448 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 454172940 1250 454171690 454171703
    0x16110303130602090103290f0f090103020f010203091519110303042301060e0105030f0102250218010902070c090b01020705150f3f060105130f0f080c041401120609 72
    0x200c140801195141d00207a0012180010014980e006001141203155030f0f0034ad02c00500301c010005030801c218080202801403050320300e000d4940b80051704070614640850304100d0042401001200c0744181e5085212190802d41200e604031300800b03907680b2008100a00004003040600d090480e2450030032001c001e024020300995480382400b1f00d1640091292510030710420000100200042c401c5580f10905600003004040400e03040d9550400f180000300e0300041020303440713000e10f030094045a000e0100c5003400b40c0d886040e400c10342000011604845516440c245582c4c210b6030300051901e0455005a6a942503154802c118011601505041104d0104001031b0610502c0380030700d43d4002d1544e465605903944031107203031890400000c013849014943e02c00002c00d82940c083c1c1c029100c1260138072100340c0101c2c1c43d03122901e622a40359000000c402103040301840b03080d0090190142c085403c1d181001022406404581003590600c0307030820700c0d504043c2a00c144180d40d00641003440c0c0140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 454174190 1250 454172940 454172981
    0x90f080102070605010504020304120809030c0d080609181b0303162a08030a0c29101a030a0e101103040b15030c060c1516110303130602090103 63
    0x84046001c0d6100b075108454030340c580030022480b41303024820b590150360041c0411100f04004401a40d90500190480711540300901482c540f264081014065541182d90342600704d080060038411041c4000d05030701d0714802850100d00c25690006a000247d1b04102c03541d504400904010070b0541c81004400a024142410b54000380100418007290903043c80001540049004aa80e0607220307041c0640011604104042122648109103500b4184d0080c1c034003100508610710400b2000448004014564103035000f00110340500c40c000c64014800d40300d818454041c00c05003400e80c1d220051401c41e0481c0e64202030801e04000300a405ca00480b01182005000040c02280300550001c4404403102c0e910701300000c00d0450304440c66966008060003c0034400002401c00600e42c1210042c040d81e0f128030341c482144160300028903409240150019800700c0c3c070f1a40300802e045040e03c105041170b80104280b20038141d1034010160700b9074000038016141c810b00c5004a0140100034a81030540c032428 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 454175440 1250 454174190 454174199
    0x1905060f03070e1015121109030105270a020901031e080309010f18020303090904170747090309060406021c030c210f02190305010509040c15090f 64
    0x18280c503014000b0a80000390442c0e0f503074880c07416a1745c03c2a644c80043c0d440b441c981c6814400d5040040c8148100c40c8403800d0150340004a401c5840031905000a011042045d40071224116003070034840329044d0251088083c6038000c0365a2040c18400100b100703d4030200e00c0d120900d40102c60848550118015540e17080070118240640340c6e58004c500840c2c034080c1d10000c2e61421039643c04582da400ba015604005c0242d00f00610304600800a47e8100114035415070600c07030345c41c003c20107244034201003528207007454058051a003200a46080c18491410079801c88100520124550641d04000c129035940316115242940154102143c00c404040781c0410019004182040c5900d801050906c0021814408900355041098550041034074007003009020003c007042110780c0000b5010200b03140200404c0e00c4200ea12484c10100c02c915001384100720107625010349801440c1c11103140980e402c0549501e612640c003031090580c07044039092258001c5000b603413020010803202c680e003010160b5a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 454176690 1250 454175440 454175459
    0x703200f0c0a0f0302061617091f0606030b0301060308040b0703020f070e04020321040911070215031605031501030513150f0e070807150c06050115080604051905060f0307 75
    0x81c0f40d01100940144070004685000031403199a40340e41c540e44404015443e14001218a000035098400d40c1c09090341002c4440c040c4420005402552100000c696281c038500408482c07507041d007240700b6410400200301040810042d141500c0805100c82c1d5a40f0a5103001d907e0310b807000c1c84020550140d0400051a8013070700b041940310740d000f070b000c1c0c820710190004c005840c00c2160340b00000090041c082030010081581c00403c007000d04010951038405a82c000991800a010351082d07601000002c200b42c14030320803020700c00c2c245c240c1801801c2d41080c2481015068241c2100c81c105595880000c0807280035100314060700342c12402a00c3c425243c0c01c2560b001e480d0f400e050000482c140b110b01c40c1d00c11000651541103680440180107081e0516403140f81840d1440380351802c001040e10f1190210b80341c2d103d258002d21003800460300c1d80e0005500a46074010041109106a1400c000c0100350b00701c482c102c840511000c0c9001030707166180d60001c0e0038070301c2d51103480b601840b4241d00070610a95 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 454177940 1250 454176690 454176713
    0x5070c080a1509030f0e0111101b05030106020606010e0d20120f0a020613050306070f0e01030227060c0a03020c0f0d020114030703091709090703200f0c0a 68
    0x40100c042912450415038050f592407500c0100010100030381d40310303428840c1114503418175051501170400a40d0000c51403824060000d0590156551642903003545101c08a50842001c60304040b401d56241c610023944072440100014103103c96000e80484660b24230580a6616a101c4540c00701c0d050380010301c00000e0744004100d400340c503c0c002114280240020714106000010008081c2180203a080c040c06800464202c2c1051240c40400310700b50f81d092140c00d100b511590380e816203034480d090b0002c21000340d03802420305147c0b04002526202210000c88500c98050b0000c210b003801c10103010032030318480c10103c1d814501034548071400f0140c0c04100b007412507508445522143e8200c5d01040080071640704001c2c0810300581141125032031082c0910b038480c1280c18001004c0f09580c54a107100d54510740d88096401c0b000071305100710b142001034990050b4051400308a110442070010070820350100000c3e40301c18002c41d0b40a84012048103d41507881c10070300350342d0303400514680454080d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 454179190 1250 454177940 454177943
    0xd15090501080c120c031b030307050f0a121803020402130503030a0e12010528090203030a0302030a1a0102030f090a0302040e0105010f1a09120309030f0601210f030e0105070c080a 79
    0x200520300c0d40840000045c030010110008026140c4000f41c0c1d00c00175010032003924026094001071004038003180d01030003c501c0300102c0101404200c449443c100b007900e0f02e40c801a0091280c070305d00c560a00301d000625601643d50503100166680003118042c00031902d03540c8001d0341448001819407949510a0410314440c0f001c0c2c40030341d040311350b140300f03d400e8400881c0d4000340f0b6840700259103500401c904e40c40420046a85000442c018180c002c213003103600042c48840841d400006000340211680b0070511000d200141803104002d64000007034a03442402009030708202c0201c0c041c4600da40c0c03c1e401800455000300100404080380d05e07028040c4c038091080c031400e00c2c0f00080004c0c2d07d04c0c0202140646518650301146881c07000320800203078106a40340c03c10284828060400f40792800c10450100482800040100e076250080006404500460b450b604080800c00140050b602c0e826441e1055410704080d0301e004421401254180601800645151401c0d10300050f4120b0100395601000e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 454180440 1250 454179190 454179199
    0xb2110081009080d1d010f1d0c030705010807030b040204080a17070c0b0703140d0e060105101709191118151219050606190b0d15090501080c 62
    0x201c12104012007111900c03600a0303c03044041001360300c4659aa80500e08082d920000c101c01407401c148602d003180e00903444401070300e668013811048403170900c0081e8460300c482c40003803d0014041c0e0220f522103032580b007400d06010010000c0ba0f02140a90055040c03072030094811525959254142a07032a0b200342401e0b030b008240d519044510f04103e4080741c00c6580c01c049542c506519110b610010381d40b081c1819400c211080c0d46822190142c14010b20401d8141d40b40451602d0b9180d000078140f1906900c801c2c81104150450a0b030207401803184406154540310342c08003a640d202d085800c000300c0c400058042d03411321080d4020012214001404500117488500e00795201001100d000704003541e035007803070034001c1110240130728007180492588102e00c4140c40e884040588510301c0406606011202d640010741080182d0805d40300045070221000040b082e207a00d0080d1a04140c4685024155800e13100c46001d03115040200704040107040750780e001c102e2580d465550644600e99140051b105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 454181690 1250 454180440 454180453
    0x30c12040e090705011409030705090a050406060503010c0c0615030221010f05040804030f03090b130509090303060609120a151a030c090c0904090506010f1703130b211008 75
    0x1a900003c0c00703005032801a19014403840906004e80740319041070007019030600c1000c60205040c0c665420031030003103007441d5020480f401c0ca4540b190580f503003500014040c2e032420641c80034160b440840c031048140c00c88400506001e18003840114a00c0a13080690880f0032030742c0004650600004d240d010203040070003007160300680c482113810340e0419180688a12030500003840461035211100d11500c0c400e040c202407241d5151181121508190008038144226020400c0076040c1448496032141c690300c00745103180740c403100040d00c5000e9854294021180500104013000c010820860000d81111410207040040700500d006407698060070741110406640d800b104e0b007000100d6504d13914000b410407025603a0301ca68005140c01100003180c0c0306441d00d5510300864001d01c071681c060910300c7c10b0001114184000d501c010900c0d074030b4030010f642c42000398143d20305000342050b0503524000314441d9a14000000c0703e030885c0c40c040000052a1410041c0916844540d011000b203070007100680d002c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 454182940 1250 454181690 454181701
    0x10f02070f0c080a170a2714011b06090c0314030301211a060301060f080304051503010807051c02060a1e0f020c09071710030204140402130905030c12040e 68
    0x84443c1e03041001045c0d5500b02c2d800382131880c0c994014007494400c52500542c1c100c80c0030140c41e0030458240c51003c0088408100b8465101101c80c40d05500d8030a0a012010b6114008528042c0c200d41078080c00c0746035280d241c0d00410215280c031500440d003010080c0c0300618041805a12940280305151258040d00c4900078000c3c005085811440e40140ba2244c001c2400c0c006031180b41401041710303034995a6124007080c4100784d01108805801c0a1000759111802c00003800700c15001c603200c0313454031102400100541900081c20006541054600300c09150200700d900496100c0720b50000d51044001c55491040b5510100c0941c0e0003400c0f843d00f0340ca084d1021005d94000556080d0440160020040e4032494105003e604e60800791301d141c1099560324681c00101d00907000e9a84030410118075004100307514003400385d0522200f002d0480340041c00e1544c0096050b40051100541840c0c41d8806c4109002d000e2050703800d2004d465007990a00a4224001002940a8041e101e0092603660110300e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 454184190 1250 454182940 454182943
    0x1b05130b030d0e090601030f061a0705120f041202030102090603010e07020105070f1d130c050c010506040b0607030c030903170a080a05010807050114070c0b18030a0b1503010f02070f0c08 82
    0x8450f8a00501000e03020b0710b03038900440180600c281c011072110307280d0400003200d0540307600e0342070721b1176104084d2307525007001d460006e040c0150614803c50b11a000d110940000c844a812541144c1054001080c10845c51010901900500104551240c000310000a4941d03017007054911540345075008200a5031131034400d880e41040311844038000340c44554a03218094101c004a949201d0041400110300c2c644103401055402203500302001a1000c15902d20031442400358a4220608a8040c01035200f5003012802c0307400307100405000c22482121103001d0500581300300004e15000900c611320003004107020410340e800440b0328400118203400246641c0c0c80383c41175134180c440e040b01511341b10345064011036103044401c0002001c84010013030710340001c0a1007084801003e4034048580c4450f241944c0c500344d518803200c5107000b90041301e050300001740d80020b0154440f0740c0d25101c6001c01c000f0000702c0d005004007817401d02c409200140071000d011200d81a8000035200c1d8000c06400c5403200c444c02d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 454185440 1250 454184190 454184207
    0xe01060c021215061c1e0201020607090b0d0b12010e030322080f0915041d0106050a09090e0f03070b01090e03040b030a02070f1b05150f04031b05130b030d 68
    0x381c88030043c01c008940745240090090b0301d1800244406403900d080c0352244000c140f91691542800321400701d900c021542c041c0902d135442541800c044030000e10b0700184180f6842030070358401070941d81309011441581d80b06401c89001d15200020082e0119591345e080c0e0703c0c0d20640310038a6400d0014108074040c9070400d003002089901901c000c0c1003180443c104400c03900141c4640380d104102848105149080002130001850407203000300004000e820040d540c00e00c181c0140702080300c1001400d502e02e0b0400c401104856807110b0000e000d035500312003241005110318030340c1c0e61400300003014420300403803a40c842d0588901b5003040040002100216559200f94410022040c0301480000d030070b07a00300d86c0070b0010f80c0c0c018440014603070410384d100c06d9070211524402d1030940e04400b0500c8203040c4041c5062400c2200e220903440c1c42401914105140968803004081b0343c0c181c1002228503c0581111000340005001c0000990580751140c000c0c05200130501d00034400d15901e1091984941c05a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 454186690 1250 454185440 454185463
    0x50906090f1e01060302130204060905010c02030c01270e220302060c0f0d050108030304171318021207022b090b031b0d0905011a0105220e01060c0212 66
    0x401140b000818040c84480080b4501d4595541c0c5000001c0035840e5502c0301d050b042801c460060340c488c107150001d010010503410050420003400c0c01500140c400040b41882c04030b00342030440c040355240072941440200542e003035030302c900d841c0800030300903500d900700c2401095481e01007a40804c0a8130304c0042000711141c0940142c0c065008a203159058000506018114500c0070785402d81c0e0750340d135130140c44081e030000c8220f50000042200303200c0c00d80071549641c0c24840c4080d1800d984280a03200c40442030041960340c050140c4400000300456042710781d07101052074900709614100801a48405100c0325528000444010000811030702482e4400c0c95066078803000d0131142080c260b9284e6810003880c0c81d11541203e032032410182d060320041c2c58290b10350100071640380e0b01b525016003512148031a65520494403803018085a0700a010795045416000e0300f07860140d1050031811002c102a8080d081800540d4004540b00e94000c4034020358500079225092070508458138140d13103441c500c03070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 454187940 1250 454186690 454186693
    0x608010f09210507120212070c03030e0103090b0601030e0109050105041407091b080705090415060e0d0507030611121006141c0b06070615031103150c070f15050906090f 74
    0x5044d00082403420340d5071284402d40f04664880d0000c1d100781c189640521015038030710703007120300c02c00c20150b1040001170030007001c0c60b043c007261030980e807800c10224000c0c09540c141031302c0b241e640c0a00402517000c641c00d903030010300a0000313003454101002412a006200240c5009844000c01d036491280607181c0310b17410f2070204030000c0411880c12908000701800c14002c0050421681d2202d56070b80c059a1038031442d04503041c081c2c501c1c0c20f03005402e40a03084001c2d03015194068400c1d01150300840c0501c01c0340d4100d43e01081c0204980c44000e1148500550045018408001d22941d00070303c920784c3c410340740c0580f0740c201c002c0803844c1c5680081c00354020b5000601c824070312a420500481c1c0205c051020003a0000e800d2a01542c1d0b0f039000c0c0d403d20140e00051400400701041440302ca000c02d2042d200b4181c0180c81741c402440d0740145594001080c045001400085103010090002d00c01303010960088114440c1c2170780000e00c6409000180d076041141e210b61008140e0b0301c100450140c1c10381031481d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 454189190 1250 454187940 454187947
    0xf050c090a15051602120102030f010501030c0c1e0c0b0403200a05030a020d02032a310221010902030f0114031f0f09150509120306040f0608010f092105 67
    0x19042501300750807100b06d0b008541445441101d0301e0074006140180f002e004264515810400010304440c980d013000801c015400f00d00d40301151b81031110040550a0366001d00c000f20142c00c15020744100b991141c0407c800000340081489100d81130940e03418000a00d0020074038007442048208031040c040c0a6150304440c0000d40103140c105506c81c04280f001d801d49030340711411a44281141841d1030107480d22040c00c580c0d807030076107000e031910710a4070101841c0420b901300b585090b07540c030600b4103804240150300144001d8102000d18108030304550b900d020000d1507031070b8803051029410039103001401074446030000c00c00f40740700e401200300d05001500500000c12310b64050140c42801004401d40c4075074a603100342d406200b50144a1400c0d010340c01c907010000e80030a030501111402014416182c1100300c82012450f60700c0c080340c1c0c1254086030b010811820181c03980000f0807065210044c658646408035280155a4029102d4036019001c00c4400900840003074020005074541000064000c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 454190440 1250 454189190 454189207
    0x50c0103140a240602010c080a0c0219050c10050d0506040903050f2503090e070314061201020c01060f1a09030a02060a0908030d051602030c0d0e01030f050c090a1505 73
    0x6a100c0e0b01c0001c152801442610f501004141003180207422010050351100307000d04981d1340100400b03800204007001001404090300d07000b9241c4600c1c1d040300c05181d090b0701c41c05d801e0020420808950840040078846580d01000016201d60701c01b10b44001200c0c14a00020114605842882151901900c0322071410341c442c6c600c0800340e40304001d80d103800f14a0351515003a02c01e41c581c0d4110800e10981fa261203413424010000030203000180705104050070128146201c1c0c0c884e0807075503003026095490586040c2c0c10b41045019010b03111b900442903207440d4000039a260100c95038002c84900110f81501083c01c240c0c841018851120401e801d640206c0d4247c005003847c0c00140b801501900d401e180c01500c9105242c1150b004000750441503484000b801030442d0141c40c2c00b0600002400110320702038072164042d4880c80312408070014428480382040f290b07400381c2c019000a420b04a010412031425001501490300424038080c050208000007040c1701200001c1c0e01d2480403292106810003651 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 454191690 1250 454190440 454190461
    0x203190e0a020f040c090801050406020901140a1e090b0a030902010f030b06090913021c06140403171506040b041401050304020a21080a030903030b03030f0f0f071707050c010314 78
    0x590034007001c001030740b13000007102c0c542885003038001c03030bc64a4096130f0b0340307200b000042c6485a20702c0b4441c200c9400f04482101c2c240c009003843c400f0000d5844c0c0541c4400d00307000c142d41c0a1556480106480000900d891040e603060740081c100c14800d03202c40e008001525821022140901180c03070700114100008051031a0000107582d1041e1112075402e8042c0031a1b01181c0c034490001002c01107418100e000d10304000c00d5000302220305981c0d9844a002d4542924000d00e44521130703c0c08400505a40c01040f034410b1201024001c000c0e001c0d04160341da0f9a02e00382001594858842e14a16510100203451742c2c2d131140045a0007036030020656030591342445124110202c202450703081c140300b02c90340c403800039000c400580120410b50720006076501c0c1c182005800d85800c4000c0394401d802c02c0185844c0c00c414601590320004030008032070740307a0701c3d0030380780d840c4a04c60360401802e90902030040d20001210000140300c00352140e8251011601404010343c01d4500c0000c000d080c5400d8140001c440c82c58 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 454192940 1250 454191690 454191701
    0x1b0f05251104060e0a050108060f010b030403090509070e030708010209240405031b0906040509030a030b01090b0d050415020a0c0f020f0a0b030a0c0507021c02010c060203190e0a020f04 81
    0x1a5400500015904001500f115030130f502128106041c90200b0030110b1651140c6030061003131030b010b0300302494411031340316410605008202c91000007102180a061240ca840c40141030301511800e0941000c030000350003503084010f964130a205100c0d0128000d101070081c0d0381c0c58000500300d2303880011501e0000803a809007040c80940c01c00240030001c0c00703580c10490341500e800f80c603d480c41556010402e00200d010010980780c00350f804c00080c420800d4001045950a901500e00000c1440c1c0c1103004a9403c01168442541004040b80050031086940c1c0400d004602c941ca15a00303030101480324030103078011568101c01098081c402c24000c035444011008485100408840c5580e800c1e20000e40c81c0440c0790481418400b0100030040240028031070900e5007442414000c2c02c01405500007a11648040c2868038424003030007a0204590080f40320542d100c3c0e0003c8195200e25101001140d43c18405400e0710b4414105111848a0000840c0f0308021030f070058020131500c011380c001d20000d0328 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 454194190 1250 454192940 454192943
    0x2d030b07020a051219110c01050313060603140f06070c0314160606080c0a0320060705030d05091c02061512030a050d0b01050f1207121b0f0525 63
    0x81d01040c00000f4014014503504200b42166903440c0c40c039072403c120b00404449841420300002d044225804180062003801203642460069030300c1d5605010203141410200b030051a4505000012080080b00c1886c0380c200131030441102c5103018041e05582da40c490640345480445d01c0350a90202003841981d881c9108092490700c6440d25001c640c08040000d2540420703142503030303960424820f42105105000c8102c3c002c0700c03022030303080c11502d9840c554031303440d0100c010301c080804442d0801c0d1202c03800c1d43e0b0300c0b079005002c1e20b8462280c400c11501920040714208268000d1520288001071801901d1001c2550359000f1f01e1203541d1252100f140721921690903503c400211070340b0355103042c1000100728071147c0da5035090711102161103880c141d440c0e000d0300327178180301c0203101444640c9062010341d07000700d500240148032921125415911070303200400004400d424400e10060f86102d0038520454901140d42e0803803001c008140865040c042c019a030302d81c5505449000d001700042415091006 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 454195440 1250 454194190 454194193
    0x3080d090203190f030906020c0618030a0206030c0c010609020f070b090f03040815010905060f060a051e2109030405040902180108010e0d0e01080615130f2d030b0702 73
    0x9000d403c40100a1400080303045882002810b0024105075202e000040201224001800e014030b070040003d619008103074000303460040050340440160340070060382410f2600030381040e545c0d052110001040f40d01192540d0482c0d800d180c800920014544226111420b10180031410710980c3e80d5007808035003015040c0d0b001442000134228200c6030520040004002800091071444900c03407240d030803200141e21240f4130f540b410b4104244c0c1d480d0300760805492041151072070f075900c41d00c920586d468000e80070103d0002d1030529542c0c2d0142032000040907100c6650f40440c409a0008400700098501100c1d0800c446d0000c0c401040142072903000210320600c02043e03940190448514041030010036807140c00c1603074680c0190715064105004840c086409880c24101c101080740020b031804d40b020f400c060240485d501050503544190082e50301521790041c607210200c1d0750380315403c5121654010840d00c805a04000b10f0941c002d105c401114002d01c5004503402491600d0b0022254001006070096 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 454196690 1250 454195440 454195453
    0x60705010b0307090b0a06080c0406110f01020d0f06080303040c090b1206130c060c0305042306071212020429130306091b210c09112203080d090203 65
    0x2d030360502811001d000e5403000001c10801c25030812240c41104e502440c02d0014120034030000711001030448040d22014208082d01c91040f804c01d40c90150034501d04503041d44082800c295101b4239410011440140410030320110383c44100413500d920090350020300010394140300f00140002500502c2ca0441c00500c01148914014100b034108801160700180381c1a041034941d0402c40d0030b01f41c602c050714035840e00c0060001c083c1d80c060b010b44214040c0e11101c5040401c0c0e01c0d082c3e0f400814000c94901c001c1d100d15100c01e402d1502003003400441c13460101140985910441d48461031007902c007280d1194031010b418802c900017412070303e1402228030380e41c100c1c100240195404503d01d07610080d407040200150304a06070829480c00480e8910300d4220604d4124108134880040c03405c1e90b04000040d0400d004c05076289031007030085a0355480b024160b42021091814401154060300001d6041c020b120309404010004464840460000802003001844142040440341d40300e0040c41d84041c00300c0b41c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 454197940 1250 454196690 454196711
    0x6090510110f2d060705310b0705010506061801080408040f030506040515070e010305090703120e0f0a030203030f1b030f1b0d140903010f2a050309070506070501 71
    0xc0c00405034042c3c2c64540c0451850300004025070362620141c0b04030020f0480d500700307070304010142e00c10000b00501c482d4040380d030012440001043d000c6000e0009807100d0059075031320348183c0b158020b88010342d0300c0c0d4a0040022210f0030038408a4840d4000e101d001c04e0161603120043d2a291406401528482401e1002060100002040d030f800b850003a0010100c5181c039182a5103407520080c1050203412141c01030255654100c9002d03200110b007400c0c049026a520342d4902e19000c840c0d03001408005038502010b10494219400e8541c0d100c040da00300d90341e440c400c82401218000c901c00250107a1042015540c01e481160140583c20004038511802802805045195810402204001610024880300c81014580c200f003401044000645191200c101c000b030700ba42e180755205101c184001030f5894050b5401c1d80090390342d100703145003000f0640d000d0b42c2d07a240310900145050190090104546003542c0280b0a4a1054407040002e000039401c203c1403000941141e17204441541d00c6d440703000c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 454199190 1250 454197940 454197943
    0x2102003280c050d140d05090f0f12031603090f120e0102060103050a080313120203040f09150905070c150b010206060312032206050f0a051605070f0302070f060c0c06090510110f 78
    0x1030003000194002d001c1c054003081490306250074201e803c1c1583e4420001c049100d168bc2007642d40c04071140d101345d1107200136220b00750301500f10b0f958000c2ca107144079803111042000c11802603108046a5807440040340d003140059903101d500307003c05860766203d102d9490014020600550b40040c940340c294a40c86d0203590342072100440b01b40c4a0740907808c041004d215080704550f01c0d4000709661a4107105202d0b4901401c60022203c0c010050840d480d038000030800b43c050840c2440460b0310403402420184586034000003881c20711511130050082d00e0104002d45400126182003c40c1c644845245482d49030a04950400661481c65590588508031000c240244036080c841c2805044910092410103641d004560009002d1003510348190a418483c0390721905403612598003800b001320866007400c2c181c1c0740103900e6225010344591f001c40814465032103010404468030451403100504c0e210042903030b540380c1070b004450b041803280c0d0302c0480d000d200b5801c6d10306044030201034441580440b00e81e40d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 454200440 1250 454199190 454199201
    0x209041b030b0c0705280609060b2101060801090209070e1507060212090f0a0213021605030a11010204030b0f071106130c0506030402102003280c050d140d 68
    0x16003d080c020504400f8804240603d4100303e07141854030b8a88003110962001c104110b00c1c010300704556800144040143d02c4d4800110004000c050324420842460700d03c04028401c6c00301031303165003130120010703024105005428036143c0c024040b0b495503594540499100b1040141243d20a44410703c18800009000c010014240150b602503581d566030b030b001468884014124000315807080c4503205078410301181e10120780f0390440d0b0355002c0e2401c5440f0600030740200d008182590003d400403000700440000142a003046503194880c064201c4941e01c3d08074003641c0f0024005031480000510301c0700b01600055404100307802c05411a040440c80c5c01e00d02001110840482d01d0901d524401380400c0c07107070980007824201c861a240d49030550105003d0142214900240700110103800c112540c13803d12000040f000c182200e071222040c5c15001451a601c044401140c91409051100280700b010740140003500080204514694000110f07641144001100d000b40700030300141041801c0360003007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 454201690 1250 454200440 454200451
    0xb04111503070201050718091a040c020307020a090209061206010c0f0b061503010305031b2401090e06070806120304030204060b0316091212110a0b09070609030209041b030b 76
    0x410362030b40b4100c000682141d02c00b40148082c4003034201e903004650304409111050300e420384400305200d003101c1a442022029945032603440307420010100d01c41c03070340007010300403040c02200d11102d1560390301c82c880100d1040300e40042c2c201204000b5607008041c8460401e800c030606140c810300341c1d503583e1610320190b5005601101d10044000034441623243c5648450b113482c20000080d4555490340c2c0e03410303540f441410390054040b894540c2118221209101e00ba2103c4100421311828241032007404129400074061601e009140040311501d0090001c0e505100f0b02caa5100c2c004141c0701e8070108040684240d031903021a02c410080807006031200d004e040c0080004040a0380c881c10510520981c00804014080401840c41020864500000340400721540c004d0000151360000e40000c80e80510720030020f262a208810101040000328041c2c4d43c130034966401a5a11180c8a0b1001c50707a01640b88801381d40602c0d41e1000c540030a04400c1940d00042c0211203200c401c9680380d5610755002402c850 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 454202940 1250 454201690 454201729
    0x30a0e2107090b1203091905030d02010204180e060a0b1302131404141503100501080a06200a140403020307060206041a07050418140118180f0b0411 65
    0x40c1004031100501031443c10f03000840d0b41c042014810b0000c542c0d240202c0018600c1120f010741d14891200140035044041c000c06002e42e299441203c1004e4003039840751140c680d00c80080d1030b80d500f41850324480d00a43d078203102d01516454468003003000142032002184e40d84480b400481f6015404580f00400c114440d1020603000700e454003200031503e400760b141c5640154104918289120390300089603500400800c041c0b003068881c00302091070410181d403c1e02202d03181c1070011401b03131400500c1c0c0c20003610070310046c0300019032100340500e01d41c0c0a003820300d1083d070244900c8201d10301501c10000010100c1c000c0c0e07410316030b0300e40000380f0303041ca154803010240e00302c44148000d1000100b4099400203428900041508203002d0003040340c03045120fa00803140150520f1f908049040c1c001e03650960650200c02d542c0c2d616508032000c03510980c42d862091514181c280780300b013000c0e5a9000041e5401a40307119040080751603807148144000c000b00c1d007200c0c0d0090700217182e0342c0702c41100141034400c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 454204190 1250 454202940 454202953
    0x210204060216050d02030a030813060501030c1e0609090c030f060f1a0901050901113c061b1b07030c21120513080a0f170a02030a0e21 59
    0x18007040c0100c680b60000c0c1e000e60581301149000da1800290f05c00b8065051411910036030341c0848082032440340e024010011070801c00004140007400640b1002e90b000c4e4480b41000700b12004403680c45660602c035070030104485000400c2008042e5001200c81c501034240840e000c40780d00c244804460306904000c1e4000800c0c4014030480042103040c032402d1140211007031a010144c000a0f010303020f42c4119904006030000070380b1650406101036415a5002452100342c000004510310b406550308407403000300741000440c840114000200540500d034a040028103580046011701480e9000100d0221201e1401c00d201103810310030085e54008502403514458518201240986046041c8a04d2200ca000240b60480415452a94401030103000d060041e99005413225850368071030a076101c42e0190080b1421030040c410b84000825849214900c1c5003150038018a03445624000c251030400107a105003c0401c03201d001d042c6c2c86007203410080004407000303004240701440f0104021a410725802a4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 454205440 1250 454204190 454204213
    0xa200714070501020d09030605071101020307110c0d020a0b0a03020f0c06060103060b25020a0b0f0c010b040615050a020c0405010b190224150904030206042001050a2102040602 77
    0x1d01844000c0d0401344058a03466165440090401c0c8150002a000c00e40d03423400b040c01c41e0b0081c001d20354420311401c0295244c1c54400c0001c0c1c04070f0182800d80001d400b442082014616040b9007011102d54001d0150203a41d09181c1d108206030070040c403417814540c2c00c0254490080000c00078080c40391547e8000c0c103403071900c0781c001402d58040b80d129000d5079030107214641c1e4803a0303c102508130820411042107055812030000400c3c1c1e82d000d5212014990340010240a8010407900902c10321043c2c000902a07505000140400c0b14023a104206070480d01e241d5203017246208400030300c040c0c92548110382d00400c4102c0014111602a448010030300c41c00600b020401041c0c105d64030100d051400030b0143c4e0400c1c0d1032a40385c451560084066450140030016040000c002080002a08041d01000b21032034070b454040d54030001a0f40a4810130315054850400001c68418581d001038180d5445040140ca10000d48007007183d24a4400800307241d1b8020301e04085240701030802000c0f258002d06841d00034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 454206690 1250 454205440 454205443
    0x10f030c05010c120509010201090209010b070204061521090209010605040e090f0d0e030a0503030c071a01180515030604061b0905030a1b1d010603060506030f0a200714 74
    0xc50748101d041c450601d042e90040740c2c5860740c40791180fa4505216940ea43c190300103d0051501030740096201865034008100f4140c0c8501a00c84a40b0aa41c1003010396100cbc840c80e08240780c4005240000340c403041318040001c1c91005113110107840a40040fa14002650000380031401c01d802080024001050030084c111303050103487d4008011602500003000008003254407040030002550900840e02c0d080b10b10340d141006402441d50304002a40c6c0c50707040c844101800b60f803101034247d40d1400e43c408113011a00003500c1d024100c4084642c00c08180d140000b08201908000b06115445100c40700c0340f040700d4070181f000750701c5288200e400195034100c0803a908250300507400740d00d00300300c04640103000c5078600280c42c5111079042038103034400e08582070b40c6218405081e0007103c003040501c42071002101040760040d06942441c0c40610040e40c451050110074002103640902011308000490360b020712075070007050500c03070701e00d041120104e003614070f401e203907100031021600e0054620b28071000100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 454207940 1250 454206690 454206713
    0x140102091c050a02100504030605130c0501110c0904060603060e0c0a090b06090405090f0f030421081204020406090207080904060b0a0c0b070507150c030b06030c0d021b06010f03 78
    0x4000303981c0a100c4a0a8031001d655007065000280215650345c0c80104060103041030741c0046600640902031480c0144c0900400c10071544215103a014860021070298028440b095101c14600d00400f20902d83c101040400400a0004d43d01541d03294004800b00701d0500400b1080e5110100406050b0303190710901c86200500c4d07209600003450290801d102d81c0d039043c1102c882d4030040720302040c9900d65920301d80c1409101400410717184540014200201d0002c0003500449000d04001004448440308103100c50b2040307080102200d05c10070610700040800c0d0368450304240090700004107136031aa00350301d08070313403001c2020303140140041107405845c074082c050f03d005040412101c90803c80300c1d40c0003800304403082c5c0b0014064900e07c1d0000740c070700f482001a20080d940203050011300041d081c0340c03030005000010034000041c0c18901c4100315428580f0443e0b000300f5015040030315041200e01050000d400100301c845140700030f100d035200c80b414108042800307000b0303140c2414241880c520b441c1c05440c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 454209190 1250 454207940 454207969
    0x5071b1109161e020709020c1606170c03390f04050301061202030604021e0306010b0a021902100c110a14011b0f0227010b03150312042114010209 64
    0xf0220100703680d0080d0702240f1031045400c402d0015840c0d00701d20303103041d0400701846d084008444d0b100030001070b526440702010201c84e4448103082c40d41d0711130418500c214801240c8803541442020000303551205503a075503080d40d031180c405070410030b00758004200c45075001c000e4a00d540300c4041003d00c2a80b4080c0b003910300800c000008002c8420300755011039151003000f003001e03200d960340081d2680d50341c04203c0101d22200c4010107844017580c40740f0305401c00781c014040000062254010141c411030328160881c03280d5400614000c90078142c0c450880c0d2084007c035040301c0c0ba00d15041030500740c2d190a1403401c06801c0c4010740c15003106c0b8903000101608081103050714209100340040c07012030358624800b0102d03501600c1224140e1172075000021305071005d8140305040079195000180c400034184c084d5028030740780e80c04003600c01003260402d80c0e078103e8041da88c011440108020000c00440f02d03480030303036801000001d4100c8803041d12190280100c110614110765000640420719142078644180c0d4030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 454210440 1250 454209190 454209227
    0xc13090c06020102130617132603190921020304080318040507050a0c022106070804030e100504090509250303020d050c0a030c02011101020d15080105071b110916 71
    0xc00e01f9509011a030a000c3d225801c07481c003050100d000d0200d840510000d19207150340034540709924001480c500c1e441100c0b2142010316000103403103c8001c601510b80c81d95000841e0850780070020482110a05060300c0140543c44100000210750340148041c18103d800741140800191a81c02030000303072580142403000700041000502d140700d42280342018215019517002005100309103450f021001d44c1c44854480d403240c40d08000085602c4000385104607c296070b80069590b1311000e100a40301004c03003c002080040c081880aa029540000d40c0610038200b228150100c10800c03814619607800d600380107111904060003455010440080c451100b4a000751402c2c007200080707501c1d00d28101c00142009603851048080d68424810303034000c106008002c642d60703105e981501c0014103640e44031888a624241d000a259078043c0305080c420f280036100d03180c02e4800d990803210110a080c900300e801c500020480e01850310340c825401c2c030421860401c1042c4541e10a809071005180c4000040035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 454211690 1250 454210440 454210457
    0x8060a0605130b0d0204060b0c010c030b3a08030103110306071d04061707030c050f010509090c12070801050127260d0201090b180c13090c060201021306 67
    0x440d11404102c030224162000005407160402000030140400800c1c040e6009090100205003165040002e290f4504454000c00c1200e0340e414041e01951080d420550b440000000c4000b4100c80d0001c102e5101021100100b4510121001400e4a2029410151420840030005108010fa10007580458181c110000e01d81c92406200007407090280c0d403054110b6410f01c0c1c01c8075156031104e400800207030080c02c50312001d0400c0c128180b9541c1c403203071200391179210301c9410008545c06c03e01003202428070103944503450551100148141880d021345010f030340d001d040181d04901d034454100c0c9030040d0f6142c1c0c0c801100f0352604000400014400b007111000c1c60155885920103040008228100e4040c0c1c10311082c40e000f9179a1085141d181903ca81540340030b503054662005606600940c84035118007444401c640790000c0111561340c107030000328840c0c1d204a41d41c510925008000b00b40720031302c0a00100700b11046541c1c94012075602d900131400750b900403920180800310465204003421352031030540d18 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 454212940 1250 454211690 454211699
    0x1020607030608060a0c031509320619090903030501090c020303091e03090406090608150103050d21090501141308120a0603050706080708130f030806010908150108060a06 75
    0x112000b010700000c179032541d40c61050341c1450203a004031800440004000d03000300ea6030078814001e844d00c0518203620141d42c002d07180103100c200c403040e0389080300c90403000c5003035031b0f00f40a00c25501c86101c602d09001c0700c214030004403a540c6000d001344140c80380c1d8011800b54034000d8020286d130310b80484c101c10354000780200075401c43d001543c0c004413141580707840c0200182141060075841481482500641804008a05c41000360045c0c3c089414401c02c80c3c8034500c0d60b128001152500380001030141d0002403104040620030540c015202c55200380480300310040140344002c45404140441d8140d460300d807002500311101d403056034821255035040707240b03450030794074100103108040449540f0010b540115580c4082607000e01c003d16403220449000b207844c0c550190540f0000c94800d0001181140012416030b0551030a02490b42d000c070021001c03a00c59a000c0c0c5000900030311050400254100000e860381c42080049000d040038000d598155042c120054148040108442c0c80c0d0b5081c03650821 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 454214190 1250 454212940 454212943
    0x3082101060e0f04150303021e01050603030a0807052107020606013f0923070302010c060f0f021306120c020616020f15090c0a030b0a0b1207031101020607030608 71
    0x20301c424122440f120210000002130010101d440302e03103146102c0110040304154000916812402c146202c003042041300c4a103440c03d0f42c00480d5070030342641091200e082030300d0043e201346400210f10f050807030070207a0313084107101c03134041c440303102100000d9a406010040c0d40501040350405002e180003120305100103070801010100404e03084c2201c40240101c81d8a010800c00042d80300e0616005020461884c204180d9040f441000800c420040b1541103a51241c0098550100c1f136041e1500715240d255615114011b190343e00f01c000c1030070f1300c50b03500328200560b41c802010004042120324071400e08020008043c54400c00000d40082e22701507000e081c107900000c400354001308400c8040c02454060904a040400007401820b00d44114941004824071407404d0a104241a100321003540708040b0800098600078071000d82411140c00106000d8030282e0009402a03e001c2d0081050440405081e40740c068603510546540706800400c034859a03060145541040796864180305803414030945c0d6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 454215440 1250 454214190 454214207
    0x21003051506090612072a0507140d02150d0c05040b030109050601141206011e0e100509060d020d060b18090604060302040e0633060705160308210106 66
    0x110b00c51800030030024007960300c62046820b408007951a1a6040c1003680003c0d24400c651440c00410055858800105c00f65450400300c4160300503004020003443c2400110150858880c0b050300410b9080c008400740e02c6d120030b035040c0d800c080180345a0301d030407481c1381e04225100c3c10100010080d0030081007184481080540341034034024000024035858560060b1000112148980850400401c148000e5030402e032216101d81d100303132500401450a590000030010300c0e50380e004041500503009501600300003802d040d41d1516818081c0c905003014002644640160303a21031041500064824400040740c003c4a0050440546e180e00340010f00600044002c01a81000d008100303a1000566aa07140d0b00818000c58015204100354400290301c4ca49030300c400c9490450300040301101d018000106c0c07482c3d04c0d2100020b0816843c180f42c0508000c002d9000c441c040d10184903400340c0d540b09441c100d290000840c46000200c0d0340b18040100704007a0001080701e013100c6940038004110507500407061703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 454216690 1250 454215440 454215481
    0xb0702030a12030612080d0609022502060f1201080106080a08070609082802010b01050307090302091b0a020d091d010501030b030a150b030120090907050408011802100305 75
    0x400841807010354049009145a80c800700e0389142c010140c0082c090310351b005281003d9821014841b8940394544807003030384a03002c242c00c14132130a00c242c1c1d00c5450500308005d140300c0c40105020319201c0c032040d071000c440d0020351280c1450000d1900410034524241703d60350017009001e0140c010300c0c0c19619401c006004102e4040d05058840500c0d1003000108002c4420800344201c0000c1c14a43d90107040c1d00111140050390055031030000008560341c05681078074820100d580c3c5a270b07115030450f802e02c0b8551034042c210603801600d907494050002078103805130a18900d02ea00030700f000c0b00e003220020051401a4080c501401e03207910380c11000b46418032494107540e801e003008212004400d0110340303030011195010704410a5400d00e14440b1020750400c1d41e45000860081c80f00480381000c2603d1084242e402d85d0400d0820002400f6030304102d4401940103c25082182c2010769070702c3c0280c00d42d920400e40c3c80520050001000451401c500b00421680341d0349010003040c0342028040d603441d81c2c01c049 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 454217940 1250 454216690 454216703
    0xa0b0307090801020d0b04051302060f0f0d05070f020d0c1a22051e06060f1011161a12041103030706021303050c01021222050d03180b0702030a 63
    0x300000e008040c040d00901c0c010000310b5581d10414421002018080d100d6031090f81040d01050120940980c003511290300140110b00d0710b80005c0c41c03144144d210080040291406200c44034401c1400c1c49081c1c424115511038144891200c01d0007800c10300f4101e003410034801e00380071002c00305005009201d40700e5548242c5420680750b8480300c00002c0181d050b4191008440350074142044000b02d041505280d1001c030488500560303103500c40c0c82d03d104807003a98000800440740001440d0030000c5007500d20345030031302038080c107402003002d400e103989190003006100a8a10400511203150907255000e1210f07201c1c2c604201c030b05000710070110317070260020303000c0300b41c94104200f1075509008450710917910540456462081e030013600708000c803511095a041c00761803000c0401e94004502003409c0e940c1c4850a51a01541c0c900c282d001040c040c5250668941c0e01d1720104094035443c04201c6541c0c025143d070211403070404a02d840703148041c5c0080b40340981c107120050068a00240900c5e82503403154 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 454219190 1250 454217940 454217947
    0x1140a081302120d0f02060109090f0209070e030a0c050f100c2a08060405010b03010e120d060e0c0c07081b12011407051306050f070f0309180e07080a020a0b 69
    0x9600024548043c1c20b40d0042e40d89080006801c103034090000c44142c3c0954034243c0e40d4030b110008450fa00c02000d800d00e06065200310061401d48003030355203c20607080604150302c0c10b00c042881c0c044403010482d0105d182013002d10907803802e803c43c043d12200403101c108010081c100001d0908400000042011007581d544283c910b1109043c092480a800a41c608032541c0340c0700039179117650a490139035542d464040700f6800750906001d80908041c03d2001410000f036034000003180303540702c403006c1c0141541e200008905405c054010038050780d55010100d4484041d98451070034060207900641041d80a8900f004075104011100840d190b000c4403042c488910f0041c940d80500346d00850310080201c044108100281c00c44040c049281151801c4c0742c003070352130b2501070300e591150074400c3d0003804062090703000080c0f08008075146180701e850050201a651001d080e010007004400700e420b95103800d0803106424041001c2d90040451100800d0803840e55004240211541d002d5001d4060001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 454220440 1250 454219190 454219193
    0x60b0d080d1805030c07060e0409051e03090306010308041d0f27060f0907230409030e0a03140d050415260a051b270316031101140a0813 60
    0x802c0e240407620707001800d4030b42c2c44102d50600380d103940e154043d010200340440d8041655041610401c00140e5103d0f0081c51176108054403030208100420b4004501c4c0310812104e03030603031414171005001703502c0b0300c079401c2d00c4030305001c0c07112000c1c0a520850320750000c48001300080c114030800381235084004070751191114050703100c04003090241f10b1000b40603486054140650100000d098512410401d81911717aa0360300c0c0e1101000b807854840b0b211081800c0300465800ba464140d001d03200355803090411700030380b441503004642002c40544c4180c4400d10b000340c22000b0701105000e000042d68852400502e41403d0902c0d10000c034800340c445808000000784032207111040c0c102030312601d600100070000d440c500344107810007811049038135011036006d6601541000b89020705276041d41e45020403201d0008450380f5068030600940054590610403103c0c1c0032190142180030201445c010600000709100032400074156020b03100101034800000c01c20a101254000c11183e080180500000c81740c0e20107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 454221690 1250 454220440 454220471
    0xb1e010906050306060f030906090115030b01030209250309030908010605010203250f05060a0c0c11090a0f020a020a0c06020d140c0309060f0d0b0306060d0303020d020f040e04060b0d080d 82
    0x2045400c0c0d0006c0000002e011018100286152180070700c0002884040104041011030030001e100003025042414010f10052801000342a40801d40b11502407001e4400442019006800441580400da40d64201e8003455070013085e582c0034020398402800118030380b8000035560f10034000740040d0340c07088180c10030394101d45c0c0c6640300c10035801c0250030a0b2000c103410b00c00e071510b10613107814001c0351a0801c0d0300342c014042e10310100400d81005410070301040794810711503440300080051442c9640c0e03418850040c021440900140050f5070b0003000ba24060f46081400b0400540201c030640d4805e80c10300810076440091020040180c03120280c642c203024a203d8994082c03c6c28480d03000201142d09040900e4800181c40e000924181c248414106082410b440742c0d01504c455400025051007003005c6402030300102001d25400e070005240420f40700380f512003504560014442003403580b007448180041401200c3c6035000c215550021043e09e685d501d140b52040300d00280d40b19446086440300c2044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 454222940 1250 454221690 454221697
    0x80622060e03070308070306150c030c0f120c020a17120c0f0601180507030504080306010e0315010f03120201180227010e01050a090e031e0705100b1e01090605030606 73
    0xd00040b02d4807055103180141060400b2540100002e180010008514005038646910408980c662002c071103d991002c64070094400da0a071a03041c1ea4184540014400300c159000100890740d842403140010700c1000813841c015441021003106180c2410105800807a41d808040c00711510960384200010341c07035051612054180e1400c0c01001c000081c503601c608103140f900007001d0410055aa511501641160810395015200f0f0f181400000e0b155405203200b109900802021250b202041d20001810290700b6005007901481c0ca803410000c1068000c00010520028002404541e00c0c220303211840540c1c0c0d00000c0c4c85100c007181001c40046010084031603241403030620071115070b100d031011510050280f20f80d50040e0041c0c030000443c882e8522030031030000c1068016518100c00e81d0005034103503400040c0605c44550070400100080d10810401078138520911010402242040401c802d00800074041e01440c1c1000a2404890381d01503550001c1d1000e42c24816100c3e128000400ca8500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 454224190 1250 454222940 454222961
    0x23071404090506060f130e011505030307030c15090203010504110111071505030403051c1d010b06040b0307030b0907080907051f0305071e03050615041215020909130c08062206 77
    0x249458a00d07c0c00403419040001102c1005800140c0c0780d039144103043c0e030b03403240403000f80c009001714569200040c0c681c0d0340b20001f90440702d03001c01d40b0070b03060300000d00b140cbc1c064404541346020900c0071411540c0080c0c58007110000940601811440c21140130340020480600d601005030010005d0201406601500d80044803000051680e0410714035445c010a80d0100c03104900100f01484003440d40140603448509201510803401c1030b1401f4144201a0000fa10030002d1640316003e25403036489500c40c035071044100395103904180c1080b5030304500b0074a00340c004a000d15081c00d00040c406281d01c006454954081c81c0000e11546c0350123084401040c10901c1e04003080300c0d07000d020004c5074140c02c8079010382c004903210032310740d0071b241d502071058800c40c850400c548020a00141c0407840f00000b0045e15240f95101514254482002030400f80d000c44855000140c0104904180f1007a00ea03001c01030003c0bc8000c000a041c0f250144100070040c0d8450b840c07640d02d05904600b040030703d401001280 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 454225440 1250 454224190 454224229
    0xa1a060d080304081303030c0204420812030a0501060504030f0308040c0329060d1a0c070804091e0e071a04030204020a0819110307080423071404090506060f 69
    0xc51b12843c00802c60214160143e1003181400000b51034070703060745806d220a10203030036038000001d04401903880fa81c200d00c2003404030b184103c400013400035042c4002481401d05000d119a21b1510594040440d00113802c80300070814240400d0001034051240031007066003500f41503c40d6a141d103042c240358011138000802100086c05a000d0160f21881004100201e081c68030290b41d45007020b03c2002e01c00303d607010b0140200140180340e8a94540e2a207078001490070301a0386848400d8695003000c0d40190b002e40481d51390780c0302c001035006600606c0d299400350554141f0050042c602c5c0f413a561001c0703000b401c03600c07044050b0813103444032a08120360085602a00a54840b80300e504040c0c4401400c640d074088501490446075440d940f00d00c9081d861005080c0001d0131500c45000c12513103c14000c00880c2c0441a5036104005000d2a560759084c50790101c0c0104401420f0500b000d00d01200b0840c101c3c09070382002c40340780c00076202045040d84060706447c1000c98504980001d0000400f1720303148400c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 454226690 1250 454225440 454225477
    0x11b0c0504050c21070e010815040917220504050615030703091a06010201060501020d0c11010509031006210809131404050d0e0a2409080f0a1a060d08030408 69
    0x1d030300f502a404c0c1c0c0700304a40e45038091050840001519405003c80711180350710032648061000b450283d104098481c0034003148149040500d206d644568428490504100402c412028403080c56541030000b0f840240c40510850030400c0c0031410000074120040d89841010002a140900c40d50082800c0d54118011881c00c60a103044801c0180342a69000d0055080c00e0000c10b165000059501505040e50744074062050b55031106110f080e002580340d0704000b020895100266000c015800e407000d484040003480501c1d011101c04003424614010042c55008002d400216255070181c40c11410241c42480c202c0780310b449030740c004204448104407034030000420700003403200c0000c18890030017181d00c0340c00c6080904170070400105254414080c000011002c0100c0c002c0500c0b200d960191420b00f0080c0071a40c03100c080c0ca0a1812440c101da01c0e6034006a030700e20030301c00d80140ca0019060144c11904081c207002e8040341c0030000c0000301508070f06000001c14108110701d41100c1c03107c0c40e0310103041c04d07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 454227940 1250 454226690 454226737
    0x3020a020303060d060b2205070804050a140c0604090f0c02580809010b0607020d0c030206041d06060405180c040b0a1709060f060d03140f030402011b0c0504050c 71
    0x14240d47c1000090455290200281d201401802c3e450701464210005000c6d40c20306686044201e10740034508061800b411005072425211074018201400c07a0140c041603154441d0881c40440b440015040c0c2194402010125418013242c950034031103021041d4000d0030700f22504014070012004826010811541d4154415002c40c801c40185c01c281954800070a03444030305103a03007071315a040c00d843d50100c0100110401071810300b003c410558400e01141600954a40004909400591200f0032808582c2c1040100c07150900040754410710844950381407a040030041000702d100c1c492010340205a500208510301e02120070b69000300700154003661395145802006040d4486019a200ba4072004004981070070070106450380325071003400d0480752031b030741d49005c12180c40e400a030f0603414050031160608204201600800c291b038025040150b0ba8101032000410102c03c0440901d02040e289000000013030780a1110400c076401103c0106007502d4420443c8450311648c1d1980020060092809a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 454229190 1250 454227940 454227979
    0x10612030c020319080f03193308030717040803040305030a320a0e040f0c0206090307150506011e12061403060c0d060e090c0301050703020a020303060d060b 69
    0x4440620079004e90741507500b82c0041c2038602400e1080100b4211050101e903074980403040107182c1c410004400b5005002d11040b404d0215559002402d0750f03034103a0358021080f081d9042c9000c42d00f4440100701c181151500403440c0d16405030030001840c91034000302c45402d540076102500d018008020582c0e60302c5a4a1410070ba40350320041128001c1101c4040d20110030140e1100c41c295440d103403030700c2010f0741e000b00031040c0c050744880089401d00c0621000c022158460380320304074038809801c0c00020080c90200b801707458004001c000803296401007000c5800282c4101c41c500c1403242c4003202180e60780b03130b8200503502d14141c03041340c0310400600c19101ea8019441074406250b90402601001700c80d490390310740840c0760043d503042c98041c0d1080c40800c03035070801100249818451a240080c0542c0c0700c00c00100320390301c02d0f21940038560107082e1002d00e500c2c0a01c5800e03000056401c085140400c006400707502c900001b0025441f5180100103041400001c1d000a203150600800c9210015081c034400d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 454230440 1250 454229190 454229207
    0x204020d090c06090e060f01020d030504050115030f1e0f0b06010e09040b1b04050d0b0a0615080702010506030a11010f11010510091503030203030f040c050603040609050c011403071101061203 84
    0x112680700b80740c01207032481c18684c0c0541f07201071040c1e010700289400d6103420f4025002c00b03041110030399690002075200100000403007001c0d5108820603032003805642811a02e4041c000e5064501d030300d005985000142100138503102c050b52160300c080c841da50303c900580300d49000d00c1400e034024108008100800c201880040d02c203d4154482d0303140300d812030010304058001d0b03010301508501a000483d02042c4102d4030154404106139010920907122041e6010f10741500f03c081c0b02041d980401e018040750213018095010100f0b400034000ac030380e40c1d11031340c1c101522090850b0501808400d0480c10a10501c0170702805282d11000f031000b0305022544100321022440380091103850109014203120040422900300d82c0c0541c01981503448403202c2984018000e002143d188460700d0380000c00341c030795602442c4600c0c09820006020111414400d003040c1140e28203a041180419012020300400c000ba2074208503507150603907040070504c460714010440d6420610200007050001c004059002400303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 454231690 1250 454230440 454230449
    0x30f031b1e04090e07050306070302180307080102070308070c02100509030307120206090d030603050607030b0a0e090703020114280e03120d0e06010b03071b02090a0b040b0d020d0204020d090c0609 86
    0x10002c4105501e02117403180c64500881d507254004001084116101e43c002c0d01c0b05264400615403819003800000b803400586074400c07030841c0d40108490b070074103810035070155210010703040820f90800c6540c002541c0c904210007132000e125011900e01c20a440c20015a200c0580c403404003494030700d110502070b40d59041140c20500d81e10803c1c645400540c403900a07101284c3cad00800401490f2a00300e010f90241803034400598112840c03e400040700c5a0041c4c42901030000b0001810f07486007140001007640c824203407441a07034801003014640e08007004a1804595031070008805080261040803a11600d400c280c0c658148240c1c80c0c040b0003185d400c3d0040c500562200010040d40035030310f02e41034a0382e00900c1003100480003400044d030182d0240c94800c60040d00304444840c3c190f420707400a000d2081c281c6c1e0441780140d40c1d0b00c850500382482d1150342e0481c60115040d400015a550000d4000c00c030340d5030002c2c0a5a00803403a2410500d0030b40010100a51081d0304002054450b40010b0400b03016124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 454232940 1250 454231690 454231709
    0x30f06090e0a02090604140412020a050a0308010807061d10030b1908010c0e150307050d02031f360f0e0f24040219090f09050f030f031b1e04 62
    0x445d000345040e20503109201107070f201000d841c0c4e0f1b0f42c1d02c601480a20015000e01540500030286000440500804825a1003500d65161950409180070328110003038010740e040c4108594441000307010000c20741009001290522510b40040310114007401d9509034044e001583c03030482c209081c103042182401d0301d2072080200034806602030110b900780c0a03000401e4003c2100b22000142402070390007140d00009905200b442d22441c1a52038003240c1c070484204290754540010440d6105408822000522265102105e0130804840e2080c1d070008641d540c102c170100302201c28400860a40000e800703041c801c00100880c0401d041c6841d217822400d090408240034001e0344c4c03006074200450345001e040d8842e0000132107564590900240a00200e03c110fa8102c40510014848100740640350941d45a448080f4440c80300c0d00c1c1c03080c64178030a00740421290b0000e00003c0955483c0c0000da031391001d014283c1d55050050a046481319100741d00d00c00c0f10910054003803d8001c80d060009104a80e641c49 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 454234190 1250 454232940 454232959
    0x2121308150f0f0c0c100603050d020f0705040209030f06041a100e0a0207030c02190f0e01051e060c011119020d0f03020a021f051e09030406030f06090e0a02 69
    0x4414402032081210b070002411480804110300b50040503010790322100c0d503107401c0d140440e917200151621100c400580d11803038440c1e07428401c00c20144462446103040b40020709022000300441034441445015080c0541d0340840c4a000d19070f01080080c0300b854210085e55018142801e140072050b0a1031001d050075218040440c3e040500c00100104071031030f4200f1031441d600c078040c06401a45c803140c000d80c2085800f91840d00960341d0024545003440a4a0a0011051031300c81c9076542c96003154000c1c501c410269004000c0c544602140840284580802d003550151501c000b032981c2c018210082140d61130201ea0744c110000b018000c0c82c1c04190b0415050f691205100100e0740c0d0300000f4a140000340c9030722004031031580a90068200c0e241a40142da8010f00c0c01303080310242c0c100481c600b01d402521501444082c200c80c2c001c41c05500d050844801c000d103048240140d403032166119030b0007007540d140a10314129586500850152154040501a08041b01c51240e51209182c0c000d074890704c400e2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 454235440 1250 454234190 454234213
    0x17010e010c09140907090306291c0f06060b040909031e051605100e15060d02010c0f1115070c090501180b030a05120406031401050d1202121308 63
    0x10300d800400ca030102c0d40d0f4071200800c45800d01c140440090196001c2c4008604007000251341400f49102c04001d40c440c500e00301c000700c0311000e1096200c2200c603000300c1312115514210006007a003001c815402082c0c000c0b6019040c90100300510260b4040c5010701030206006c1100039103500b01c192650f00035030310010417101c000784100502c00074044c1000840c0c0100242042c26a02c29044501640a04140d403084507004040c08195480b0340c2d01340e00160416400e03544003510105030917400c0f8100b503c0c5800714044a60018200c4080700301c0c05030103000f503e0004001c0190746c0c188441c45080240070300c5403146001c070745a42c10f604589803c0f168400f10035004105944c0d00d00c02c01e812138000308203a09840c00b21006d414000c10b14030b01c506405001d43c0101001007001086a40311362900285101da480c0d1030000020221210f1042020300b101640004000980e40c124841070000d80080440012140d500e401740e14040401c00c8402d0186004103c048003003100540b2002151150b1050b1902044103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 454236690 1250 454235440 454235447
    0x2031606020d110706120506030109020604060f4e0c11100506011d010509030610051302070b0f06040e06040507090e010509031605070905161d090f070917010e010c 72
    0x2030b1700030310300000c8a0001e09298094240c100783d4000002500000b880d81054000c10307e81e40c01074001001140000c6219000940e002120400d0000070300540ca04200c4045400300c0b08031049030070b503030b61400a82054140306003612802c040308809040204402c07061014080c0580c0c4922840b0b140d03138040e550f14041d0100603405200c0c81020140d4aa100944000494506c002c000e00f00c1e1030f0402c00e0610811400c2d4604110480c00f41d2700d4150203091051901040003040034810520548003801031206500003080c90254641080922680d4022966100045801801d801100755817521a160500c8244100800d6450585030168014001100860415400d0701d0040c0c420b001581c0c401c011180ca06070312103141a03035981c803940589175516942d1201005072030303003950301d04641c00c01040e409094a8004200c00b8468101c0d9900100d05a0f05e103001400c43c2100501409408090100051009108902c881c0c060408076240344de090741802a03280c000c0c04082c14140380c6620b00400001120302 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 454237940 1250 454236690 454236703
    0x80d0612020907081b0f120906011511030406120e01020d09050105010501180510020309060408101a0f10020c060f0d1503020603070e01050f12090c040e070302060702031606020d11 79
    0x1303609080e480605d2060110001303070f0081c1c028040c41001444815104c100c0d18050340c2c000c14401e4000c000795410301c0040400109880468000d0000c00d6216081400c80403003610100c0c3c0060419020840c54415180058a004001503a455100103086082102d80e50720410809005000070440c580c0c8800054520700004030300060768250b0301c07904100510300302d400d2408440d001d10540c0d0400704070720302007102504940c1015071507402075240541d43c0500740c0308141002103030340c0e880a18034a100c0c2c042412909800a80f6000340d000707001603690103008016030f0f004d10f0405486943e4070801c61041981541103050760588003070030902001910b1070076940f02c000f900c2d00141164a50307194500155011200e40c90a181840750610403008001200d2005d40004120314a020400d0302e40b0041250510400e405c109118500c1c0c07848209140d41d00180d0300042d254103071811503031004103000083c5441904e04400103014600140401c00750383c080340880d11107410b5100c2d1140040030000094417400e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 454239190 1250 454237940 454237951
    0x1008010b010c020f040608010507200705010f030c030e160f051e010507030309020a030f060f09080d0f0f060b040305061602030a030507050d0c0315050409120804080d061202090708 79
    0x302c0e0111450b0140c90880051280309000030030004840d03a8998000c2d0075100c084640d04041040100040300a82d00501c03600d5140001c1d0001d001424148000a040701030304408003410987d075807072040825402035101c0b01417680201c00302c0b6030120051013010b241c0d05003802801c40703083c51044000344a04128109104801c17803404c0041248549000448058120b0350b812303002c0546555000000d62a245c9000000c1c5004000d6082644044c0c100307801a61070340140c1c181c0c00c5180c00b04040105012405071040e001e208000850a06500300110f4003a05c22180340489040c81c003100040c40500d228010030460b031290f0b0680d00c079a5100d110b00407800300c4505010b0b01603001080b801600d24404da00c904e030b101c0b98608010b8200099001a00101d5081441240200350b0b1907407003860341005105140000c1c5411541484450b405955240c3c0180f04807440300180841000440c040200c1030098510781c40d003444040003400e81d0740c42104401107103e84140e02914400c0040b03040c0c0b91203480d4262059 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 454240440 1250 454239190 454239197
    0x120c300311041419120605180705120114090703140a0804142d2418010e060d1a010509061605010e15100f0e01060f1403040503031008010b01 62
    0x5843c01ca8050b07468010b00c100640d11040c030509949240300d003138090201810704016019654001352a1442c21030f03030b015040c0131040482c0b190b0018451030002c2d0100a8540644000504002140641b40540060100800d4403002901000314200000840340e040302c1c000d8072088d5643c43c7c11542103499844407400a411004204010302c410b080e904c43c0b0000044018040e171210018511200c1460240b40621112204038058049900e1901c1580c1010011424003d0b950000003888059410310540140d80c04802c0341c4803456001da80030b00d030ba01160490190120f6034a01041040600500b01e20005042480141c2640600340d442041640c03e80e44000c1c1c081441c0140d03076240082da41d80b07190021200356403519042c18030542c09104489c16035000403c00c5e50141000460070000d030866402102805040780390801403407000100d00d5046400302c4c00e0280550a0760503080707640c1380031003040300000040001400200b11780007004610503090003c0e9484d103036407560412800d90b00d480701d995000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 454241690 1250 454240440 454240447
    0x11090607030f0c060c1e0206060132040303090312050f09330408060c09010516050f03030103110306070c050c040209040b1e09090703020d120c300311 66
    0x2801440302e00203446141c10000701d8620a03a0712001a00c2072850948001245418003064800c100c1a8405103401c140c005494203103008000280100c081c107042031100303168420065044095940300c01c010b0351340e03001050382d201c0e141c1c2405459480300e0b00c41214060400041e2001036403199040d1402c6011484034180317000080b000b00410360500c00560b8110701000c1000c0e00000c04100d200d0030340c008811034001e0700c952811404904045006202000c054000c102c4c0811980c0d001d401c441300030022401102c04c01406081240c41c0000c1c07113403480800d100007c004000e020f100c044044048200b2400caa040d945e0300c100442d05c42c404010700801c10b80c08091139442c0c510702a006000000030283c400141d594038503000a18200074200100065040c3c08011482404d00c01c89140c1e12020041c01440b8903840c503404a00d003200401c2000c3c1450f14401c450080042c03050f900d9000e49500101c2c4454010140680c0e40000e120242e602042414952089a522806805482c00d09424031031240d04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 454242940 1250 454241690 454241693
    0x60302191b0f231e01022d1c060306110705060a020c160e040b010e010e0c1c052806060212070201020a0b010602060f010e09030703030c12090f020411090607 69
    0x64a85054808581030b83c8281000c1c03501c0540c2c2e15948412a501c00001d0206035011040e072940500302010003010790340100452824000e001816140d007090114034100c180d0a000d210500038094150741300c681d20b0381280c2034003001c615500058182c80c02010100074580070400c0c649058421000000e050b5000f031000662304038810341c0907003001d0307500c0801c8c1c0e08020f008080c0c90303004003503d40185030b40c1240181030000744585801d50398050540300d0788908465041400c10000c241c4004c0881114020004424008003401c10301c1071142151070390144680d00300240b00c080d0704402c003001e5001189403030103007980700c44039406000c01700c4540b40c010300500c41d10103103212100d500404c002c1c1d05510600986000240b10890784600904155015024606140503094130003001079201b0000d6030300d0300b410300c6000b180220440b810f02c1d605050014078518805030540e540b0303100415a060f858030f0b254501c420301c0b080a042e0a2014821241089003481c01e4841c031040303003e00d1180d00e410120a102c401c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 454244190 1250 454242940 454242953
    0x30d031406092514040b03010e0604020307051e07021201020a0f0f0c0b091203040b0702010f02090603190e0708010902010e090f0403080a060e0112110f01050d0b0d0804060302191b 79
    0x307070403003c4c0c40c1c8072904090b03070011415190301c540d1200e070075410004010082030a8081105400903c115029441c504004000520034020703250b1042d02ca00301c0c540031000c210010300450740d0b0154082c000303d841092100d030080c000d4010001c0c80f03022034100700d40e0004441c45000038000c030241a8460b020303514400d0b11444844840100080414480c084820f19415850800395104030b01c83c502410191501c1c00009095500c04041c1e218810300500811800384d9400c016240e02040d0740c1c1964644040108079030000d8441246a60002e02072034002040785401900000704c041d000b81c0310200d054240c40d091184505044a5503159003003060045000240316000c22900002800004034030f882c1c0364010003c4864003030303018001d24010442000d00301308450b03540780c501d10011540c0d10030000790300b0006000c5c3d20810360900e8943c3e5480540280950f80c0300001c3d002c440e04501201d40340c0752612030240c000d40c000c1015030314041c00742e401010503a03c41c0095205001c020fa10f002129a00c640e2034030b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 454245440 1250 454244190 454244251
    0x903020a120807080c070f0608101404330b21090f0706080610050315041107060609050a0506060c0d0810050306070c1403040602190809030d03140609 66
    0x2124641810071005000c0340c4c000000e000d030010400c1c05010b46a10b8814840380940c03055012200b403110140c1080304101e4108400d50440e409106244203032074107200014020301c0014020781d0401c100a50401031131401d01a00003071381ca98004884100360704c400c1c40382ca060044980128a8207044200786465100043c0859008812401215946490756003c2406c0c440710350414030000e41a0004c0003d18a000324155000b0481800d2440c6542003c1801003243d80b502c0c00214010390b01d4046005801c0e82c1002101c01440e004001040030a8036944034402034441a41c0030000241001d01146640c40c000c01204e010a00d01002016602c40400c01511104001000040400410240041d1070349090140ca84500190350f0b41c502e41c0422403500d441c0c404410f00b10301a19900a000500003a0b8002a10b101068082c0d483c802580707030907240402203441001c08407034140c0605070103000e40c0e0303815401c180340655800104000c13540c0c54600340141503d080320300041c0d610106400503907124108800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 454246690 1250 454245440 454245443
    0x250b040306150308030f0604060b0931110c010e0d020a11010c08030c030603010c0203030114010c0503040b1210061b082a0c010305060301090b180f2a010903020a12 72
    0x2d5808180c0c1c0792241c040540080f900e8410580190307080007882e25080c0306400c042d1203201c48060801c0c2c00322000c941e0031850841484102030006484030710303104005600340c00c60000c80340c0501400c2025450564a0b0b00404d24411440d0308000070b08902c0b10010540d42d40255441e4020002641c013500d503440e0800103034041d14140070887c10080701045143c001144104500344020342d890810005050841c4c03402888901150030900050103080104001400e09150034039015401ea0054100704d4118171665119056050b000941016980d0b4826242446600b11780c1212107182d40e1601c0554001e60743c0035201d84400291800540083d03070700c0c809480b0505011076200c00c0c1d0080c1d080107014200c84040e42c0700940d0720402c0f801c0010343c3c2c940141c82e400b00c0254024040041c607965101910b030805081c0410300d4070310914184102104115001c81218030208844802e412001d444107041101040303442010300d1504140c40300e5001c1c4103034a040380d602600010400d4541400c03a201640134880 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 454247940 1250 454246690 454246721
    0x306031c110111030910050f0703020a0e0402040e09060106020a030f1b140c042d090f06050f0f15030d12090b04111c03080610030b030609250b040306 66
    0x10480041d00920a901c5045244440c01d542c0c0d04103140b00e00e00d4101c182041c0c12056003088100644100c000200d550014907074180035032038078181c08066807142b80515100f500180f0208000449641c075007046030042a0f05003d541ca540d80303416040b61100300882d0090041810340f400360030918811190000c0c00310181d0710fa040c103000e02d687c4d82400e44a0940a101c00303540034109915003443c00c4d01c00d41ca0809070812400710b6000c602081102c4082043d10040e090035951800724007801100c54a003010158048001c100c40e01d001400c00702c12210590f18102d00800c1c09002400958509180300380707070718000f4018016402e500b03400b280c4c1c3c085150000d0741050f4803101300c0800103085003116409148242d035001031038404c0405002e0b500821911010040060b034104501094001380c0350340c0c00950035994040d100799400003c0d0041c1c0000c00354940c144c0b0501c4200040e4150218102480400a00503503050114840b11039103132451030300504550280812040001601640c8481e98400d1400b2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 454249190 1250 454247940 454247957
    0x6090e1c1b020603250507030207030b0604061d010305011103012603270f0a0e01060e06120403030504030e0f060d090c0807170106080d05041401230408010b03030306031c 75
    0x501049583d0402c0e00c1290305d8104078009460000b109034542c00201c201440d05030b00f02406524000e40c4e07043c03984005020300030b030000802c505803030360b40082014114420340145605040d0a175480c044000f44415a200d510305903401800b1000380040f80c0c122280ca003e261781c40441c141468801c1c102044910460b803008102252145240c621030101c0c251001442000029401d01400140a02c05050a03c40c1c031510000f80010840c0c41c48460545641e89481546001d011001c10007034410410321a0038110b082040004056241d00202d1140344a960fa0544150010007072118000d907080101d54481000d00c40881c0c038050365401415200c1c065100400415600d038041e03410040e041d0403c075540d220321445400003003000d025080081140b503004062036420b503a8001c0443c0203502030200c10014100c00d106107a0300c54645180c1c50400c8140d91541050b06524981b010340c003c0c4101c4445500b4804900b005240100940b0b00c41c490149c003421210700d01c0120007403d1803d400f40901070041c1c3d01c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 454250440 1250 454249190 454249193
    0x305040818010e1306080c04110a0c030513090606230a0507050a0c0b070521180402120109050105040e060c0d0509250e010b0a020d080601020a06050a06090e1c1b 71
    0x481e800801251002c1c1c00240050a06c0405400c040441c0405806a401c01500f10b017100320a030704580c10204286801e44011f0898601151541300314040c03606040e844032404550405164001000c0b02c0762510703a40003107841d11500c1040f0a6040c142000d02e050103004000c00c0d64001c00040098a103e07005a6642c4260303540d901c0030348410381d04a50016100442d8030030405c0001c0002500b10620035407481008030507400050540c2c4a100e0740c0c2559030b1000070034005651910b40595018801c0205540090742c0c6074521000202000d00c9400e22880c1001c0c85440e81620100d8100e004800c0310708264a404000c0c2486c0b4060300010b801000c1e540701c0d40c0751103c4844001e81d00c02c0740c211055150354000c1e626020b5070700443c0300184c01c01e00d4813850411440c442940c001444189940d01801d02010030307078485005038200384000344e01a0459040004105403a141e60344140c2c1903480c0104108500c145010b00c0e00d41c2c40054a100070410000a0154a0102c0c001c4400400001d000300d070010700c4040b507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 454251690 1250 454250440 454250449
    0x40e06040503030708060d0b07122a091e03320102030f0709060f082203211e0b130c05130503160e100305030c0d0207060305040818010e 60
    0x3220240c510350004010301c0513590303100d280550007030022206c09102e101c00b91641c02c1a088081d107c402440b44080340d040e00e20086810038583d110a170b00e0001c940d24512070a450b0000d0030203200714000360500074003142c5a552074489800300e07110803841c0b10f40310b401d42c1e9904c44014004607a10b07140c54000c880c2000744081c0d0310b00400046400c10300242c0c0ba07040c0507007034041541000e0690020307c079028030300703000d0164001c2c5051701c81c00451600350550740302d840403800d05040482c2c9046810014001c0740c024150011040004015500035010b000c0400240442c101c5100051010f84044290807100d05031019400c02e060f004c07401009490300940001070141107c01e000d211802003400803072003247da491160000030040c08150040c1408100c0c880c8416404e000c140140b01400c0a60300124884210030030050003d903902c44100c2e0703984c1c61083c001e16a07034000d40c816080140300384000400c449229000341d5005541c0300f8070442c20989140048243d004121000300e04100280d01300c04080da0301c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 454252940 1250 454251690 454251703
    0x3010e010204080a060b06030c0723070b040f09020a020601030f05030f070609060b04063c030309031b060207091113030605061309020a090c050c06280905100b040e 72
    0x554002072900300105c0c07408105807440260803610130340b030900400201820240c12520125404543c0c0d115544600c51850f1500215511000c440d01c90308001181d0000c18000400c190341074010261511a038402c0008164841c0700980381c01078105100400000e241d0703114803a01c2510074401d4a052001035000300c1030523004158140e40054a0b80100020f11625114203284540d0545051184900703000c2c0010517408020060380345c14400d1000d12082d88403180e0003881ca191034449a2001a07540d00b001002c1c0c250300d0206849803120189500040f105407081c0000715241034002c0c19034a0314008400008000001d000c10348032208000e900ca240c00c00380e038080300ad18072541001a95061110501040d285001014004a85000202d001580e9079420759000c81e00304d00008595095501421212400b4001c0e500c0b405200d9034040c405117240641514440c000c1000d5100307901c3c114698032034280c605105028100390000e2500c90802699a00829903886c400b400200318107148120f00780c5043c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 454254190 1250 454252940 454252949
    0xf0b040e0d2d081815070e04090b040506060a05011107050105030c090603040c30080d06031401020a030c0903022d0d0507090b010504150f0c02120a03020d0f02100203040203010e010204 81
    0x4140c40f040241c4401200040700c03240c2c845600628a80302c40302548603004501804d070400380008580100500c1e540d94010309919903000080d5821030520f850480e584100950ba11403103094902404039a652281d00c40ca03074040800c6005003805842c2000650322944081c0c221360050b1001c104980007500c540004501552042da007440c2a10b02d86004079006610f2000c17802034120380c100e079841c4c40c140110010f00c20350360070400060340d6a99110b42000103040c16800100110860303120542d03a41d00641c00360a00040c552001d010b0300301c1110081b01c104440307020096000d8113401e40c61183c07a00c2d8032240044c220320040003413450501c541c00140b88881d5032004480c0c0d80c0c030443e02800050910b001d000040403080c00d02c182000e0130540409104c90441e000031003000589504400060b105540b02040c0e6600540a070b03280540300d01681c1e46600100c0401c0c0d0140c868140030051180c483d2004170385d11126075025250049208120700c0180d070024006991541d211600d41096460a100400050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 454255440 1250 454254190 454254197
    0xc080a1a150703110613110303041e08122b0b030303010b070c08011506081f03080703080f070207090c050702211009080a080406090c06030f0b040e0d2d 67
    0xb80010301d00104004000300a644058012000340260320105800b03001020341c0c0700c040d203030714081c000300803d156000b564024442d4010781c1641d0840c1440300300014068990b0301e001d4a1084d080310010b0b03d002d10442c18605200000880020b0a074805c080d048119240a901c0102c0c1001c07030503001901d07642080e04000c41e50080050381001300059002d49200409010000f40141150b110f11140049034038816078060100c0c0c5400900a44a003514100840015200740e5141c581c60b420701140541120508030003180c10640424110f050080f10548160710950060503014105001100641010340e040001e019040c0103003401070340d803078103450010b005040c40680740c03400005005240071007503000843c4092501c03e4074008540158101c0d0130940300c90410607406e846500d0108001c00e040e07800a030030040403281c040f0301950300d5000320080940d5210184141c4c2c080d80200400c442e0300540444186d440880804525802802005d4060344c510703408600301d508400c3c080c490213904c0d040381e070b000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 454256690 1250 454255440 454255447
    0x1e0a140406060801030b0711070b0706090b1509041704030803130b010506040609031106160b100b13030f0311030a0e010f030e100e1f0603060f0c080a1a15 68
    0x118101885008020702d080e140060b80e6500d1503c1e000e0902c1009003150042100ea00340d010303c110780402541c0c000b0108400190b540c0c00e86800c0030002400e03482400c41e528040351010500714014140c2c500c0041e00010800d104035112a69a5039526080641103c11a42d09100000102300c01001840c410502c01c2c10383c0803031203042e1610717200b0780005030091817103040180014070915074000800c03802d0381c0d03000bc10300c1380728124400040d150340140d01401d0441025182c1c4030080003c08242e480c01103400601c0000990b8541d00440c80354007030b160b0203031040101c1c0305082001c1114400134061080c000e080c441c09042c84109541d0a560003200c6101c042604a0142c0440303507800080201d002c0d030300380380030030078500e40c050900c0c0c9640c0b03a2015240015240e889400c00c540d020322a242d80782da907200011a40118040414010b085544015100e1070b00c1c01c3d5100441094074041c001c40000556240f0510741d694510440040580b120411030f40c00440c40000c40c1e07912100000a141500303100700b140c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 454257940 1250 454256690 454256729
    0x1104090b09060d050a060506030a0b090a0b0603071406030402152206080c09010309030e04061503060b090907050a0e1008061c1707080d021201180603020603061e0a 72
    0x240c580041d100e14094004104080045040402c54604041d400301b40800c054139003c0000c1c0c60800c550030098070308600304c02403289000300005c0c140354a91180e02c0409556803981c080503210501841070318044103224401d410310386010030045602c1440100942c58007905900c003140141c0102d001d495020031604c0460080c0c600c12000d500040c6502e250202c010324144025800034024007074031a0605441c1d031009020140a0480c21103000d50290080108507583d0380c9044034140703001f500c2c50100e807070f100020a4640401e0100d441c001805010911580c88204040b50a0b80c84018043c04001685011784400d60f2080044114807a00381d82d96610f500b071203000c0007907042c09406500d02c038208252030b0400240711000f600f80b0385813009554580301d10203410651501c1c4201004400a94400285400075440c1c0440140c16650246944d09103501c0304402d2104031580d5010195011205000007900e5150603031076142c00000d8403941c04101001513010580881140c1c0200c0d40101c440b2000703c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 454259190 1250 454257940 454257949
    0x4171e0a030e0607080702030604110f2709030c0d08010501080c07051c03110310080f070e01050913060c030501031103071a0a0c0f050f0115271104090b 67
    0x20480985024020140309594080c220300e040440c0a0301070000800d0350030900c400041962042c0380c0107410349080d49018078000c69800c030b020180700c2c403aa654800e00680e40c10310012121a094003140002e0301c42050090341d20b95014003c103a10700c41d1104018071303440b0400a01058030b4040850f16003094035410a00054400c1d440200f0361001c1e041d0034004000866000140d0002e04855441c4410031030900c88002c070040c008040e003280038846d00000740010010701c850182d00300c03420783c1e0a88000d502c804001e1074452415110f6003015540d5180148060718140600039040420041c00002212031682d6160988000170386403008250744000400601c054076140fa913100300220060500c50f8200190030052076207161141c0c1d1500302c0414980ca102e409100e00108494010a881100000528010360768120088005805500b000700c08404040d10104080c2601d203070380040840f4a51040803149844c41c1c200703000108544623040f07402034018181c000e0029000d45500401c0d071110302c10900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 454260440 1250 454259190 454259233
    0x11505091909120503070207090207150c050f0f030108010513020d030e130e011d010c051c060806010e041712010512070b0d0605010e030f030a05160203190201030c020d09060c0303020417 82
    0x10301e0040c010071407800050303222105150340226542c80044d0111480710300b103409001310fc03003000f20640001084034950501c8400745040f2048040240305654889c09080e04594200d00004e4200300d02d400310313071b00203800340b0f00030195044041c0040e420708288100c0402a114225504949a55120651100c4200340c650400b40702c607a130300080c042c0d03040c038100081041c821880c85150400d414980412000c045810500041a00400b00c4005585542d04048201d0050b07404541034800d0401e410101044031054908070803240300c450f01c95078600000d0045e0201c1120040d1001e004000e40032505101c03c40181c40c12144c201c6d400100b072402c040014010301e2038003402d28426444400342600022000040b2440c003141444c200e0b4039000d015032221030340015038500075410b0180003004140d8100400da090007a0303000766028010829003480990710b0b194050102000541010001c3c8440c0c0d020b021200110f904c00c1c40c00500d17141d40c811300c4450300c21060307031828200c0d04000a5801118584d0200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 454261690 1250 454260440 454260449
    0x21c02090f070203031515040e10060e1e03031204051b18010504020723160504020705071401110115050a0e22030e1e03011505091909120503070207 65
    0x61000c24102402c01030344d40d0000900c1180007007205000c400013030b11500c640c40028000e901000b034a80c0e4983e510003003408070032520454a80c402c1d5000003082849007500c03005a00b00a0a050215500181c400c01e1040f40422100d805110800c6085078049070b0050341c900c00c07801240030308101700e40e1059005c501c6446402ea24403800502800450080103000841e0458400715001a03403240d0502d0400c0c0c2c1782118104520440340758241090005030049015a80c0c8444ca680f499121a29142044201d006a0001800b20303805814144039581c01e036808040c203400c05042008060856a902d14296006440301042c0304204c07190030002030800c080d0400c040c0400c10b0b800380c44c1d442c0c11102416042c91000d40d50031420284d2640105050141020080030000903260b100030000b6070300020031b40c030703013060034540258a402064030408014111010a65000811a80d803e07110360f07640e071400b69281150382c08440d9603127010b4400683c4402c140c115117100d54a90580320724000402078140b28280d0702 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 454262940 1250 454261690 454261711
    0x1903030e041104140d0203240a0c17250c05060a05010302030a030c03140c010509070807060f120f02120f130c06181e1701060308091507021c0209 64
    0x320a15140d80704252819a1034821360b9200d146603000010f900b032480758102a415003c1c954980440c55030340881031a0404450220a20b15200c0036244c034200c07580d000c031983c000742c0c0d20300e648910349402c01c4540b9082514001e1036000c5d1106108000c540207c0d0100c0b2001044100d074800c410418181314003980309003030050400036907165401007030704ca03c1a0100102000b10414100c410540162100d00603401402c1800e51900482c003c1940240310a80d01416944144500014a600006042400d40b4804d0f0358605030700a10180170354400d000d1804186c1e4480d16941c0e030108000c040c1c070150000840d100c1a0150303a0038031140c0b01c0c84500c80617001000d2003c954058a010822105040f01282c0f1507141120f06034800742c032100700c1414260415040503c622001c0f2a110101103040da0958440749000d03d861020000c4e182d00300d522030302c4010980e940c144429109071034000b007884248410740001c246011210350001d43d03c2080d0410205188083c00303000419170a201c82c2036507201c5d20200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 454264190 1250 454262940 454262951
    0x314010e0c0a030212010909030e12430e01080102041d090a061109010311130510020f070e10120f0b070c08030c071101140901031a1903030e04 63
    0x208010440c000051100c0300c82040080d8a44060380b01c0d6049500c0c500280520300601c3d610345545030050308041ca000d81c000b62015103448400d00c0c11114200104101800512164100c030420305004007034522690807289000100c003600c2590002c40c2a070300a0001c110f40030550034103074140700c0001c06801142d00c2d03030b105001c2404000f2183c0c58074001860700d110640340b60382da6502841d151803044a00100840d0920f000145d003d08400c01404504200f600c1c1402040d0040b0504a014000d00c41c6641035141410010081c90a000f070602c001c10a5901c1514003040d001c03442e0a01e05403082c0d01814001030890b00b002400090000d510000d81140840c40050900c9500e4080c2e84814051029085508003c041106a4081e48030310a000da4400c404584a10f0498100801c41d000b00205a48001ca902e5401c1c02d13661103031740d035281404100802c44e820002e0100c01100240013101025244009203c000c512513601d07180007070b081118615003220480e043d0325009080020000f1100e010fa800c11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 454265440 1250 454264190 454264199
    0xd02011b05030f10050d050d030b01020d08010e2703030702071203020a060e19230c01020618010609020706020d0c03021c090c05040504080c15071409010c05010e0a0201031401 77
    0x1c8202c94014440c0500e99100d0740740d07a0250b0002e00001d6100759844501000210108007010a444a001c0500c0c0c408002004403e001a030311004241c1268001030b50240040c040d2145140300b00c2d41003c0309401c11004002c43d82c03101d030000d280c0700d80c00402540c40401040509541004400d025040c02c0b0740701c40601c00c140d0340c0a0742c3e880717000d0001400281c03180c0c004d031407104040001c0040007880400c800c0d4240c2883c24588180b08142c4201d0284443c00c4c58203003240d030400070b40d40031140010f83c008c1950f5501d0000c4802404110344001c1040d5498a40c0041d2200d03d60018226440c01910016524410101040100d03402e0ad90b600b030a0600600c902c90352100c9041902c03c0c00c1c2050040441c4040d85440d001281c0d04558000e140d101e841c01050006004000740600054201103040b2803280c610740345021804603044802c0b00c00500c1c0c101d000c40c000341e507100140c0f06400040c1082c100f00d185c550785860a403003030454502c05a43c41a4403240940d0383c180101440c0002822a1081a5061 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 454266690 1250 454265440 454265447
    0x10e06042609040c030b060a0f0801081501170c0907200c060901050f040504050f04050717030a2717010b01180e0c070c0e0a0b030c0a0512031b0d02011b 67
    0x1082140341c0715075070744c44141039414080d800081801c80004c0c44507658010064002d0502a20848003000049490001007003048001a20026040300a07548010503807810782d05c541782c034030900091503d43c051501540000e440d00039415025909503110300c07404040928005403115201081c041642c4c0c003e107040055919100300b1079031042c40a01e4082d41d07031007a416601f04103114550003503400515020410031640029081d20340914400c00aa510441e41c0306603852409881003004081600100030105034540100700b03403e106882e01d08480e6444610417269100a03880d070748a40032002c0c5580c1e01c80d4008001f0711460480314401d0803e0201c002d03101d00480d89102d40380c05880080000704c0302103510200d408055491141d03200c94000f840f5034483c2026001c0c154240c800212590a02c40309251928000c90100009030018020600451400d0b040044400004c212207400307010030030032914484079905070b094900066000030b0130688683d0f4002821204443c580a1810146805810300c03142e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 454267940 1250 454266690 454266697
    0xa02010b10030b01141b071401020d0503070203090d0212100903030b0307031104020a02070f080a111e0918030c0312162c040f150e091009080903010e060426 69
    0x400541a5407100341c080701d01b442082d00c1c802403c8891040503400191400c900d450400c011100382d0075200c00005824003600c15000c00e40d075480150700b0500503003505051010311442d0b000e0000f454041d10101d1402020b051440106403921407607118901d001c149505400340001c888000e034020f10444d49551a96440510081c5045104507000107a41c0c0f2514030170000d05014011032201030300020741e2180f89540e24820100c044407550201444490f031458800082030100c081000008135002c140b0040040690000313000c81c43c0007281c421910046c200403c0503041d01e20910004564903604180000480320006104401524040740c00e45d020b158024000c05540008100680d01404002103090300c500d00d644400d90410b2601442030025421030700411640c2a1505202444645421000320610760440e411b040c2d039480341c400d0f03091500541c0d01120f43c81d8080c441c62400d200c0c0303410000e425617510520070003941e4480002d01060007003074590345403044107035031940d2009002d440c50300d144c0d0301 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 454269190 1250 454267940 454267967
    0x909040f03031109010c061e1506090f0b0a050a0c060c0903110609030c0607050106050d0c06030b010f021c090b03040807030206011517090a0c030b0a060b0c03090f150a02010b10030b01 81
    0x1d0320748204511801c1c0b00c0414464007008030406000050444000301c9444012b4804d00001403240384002600e0303e41103091409030f400103101d8500d01503000704140ea596121405810401100c0e600304030110700c0d14800c1d005000d9060b6034000341507265060881a031107564013054401c40040042d640c09541c005100c81c01c100c010741d4202e4513501d05050280c014105a8080d41d08000b00c06200303003c2103448404442a0b9000392810009140818011942204200d01034400b5034801041d50101002442c0e0302800340c41c2d181350520703805480f181c60303102540040d01c0444940f00302140308810560188080c6000d88132076030745030480001404005049000310310f900c42d110328000021502c015028001c1a02c0150000101c1c5d00f00c603928075002110203400c41c0c02c00d8416161040101c0d04c0c1002e10116203401c11082c0045040c11403c500704022522114245e0f58001e10005000064480d50009403900c4680e80e000020618011070520402102d80103041041520b0a01c020410380e03005003862034040d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 454270440 1250 454269190 454269203
    0x12402010e0d0c08040b28031b0809010225110102151515031504050601022d0a020a03140111032214010212040507050111060c03040501020909040f03031109010c 71
    0x3240f6810134a0722481144c02c80242840c001a5980081750328819158030502e101c2ca0040380c1e000ca0381d40031021242d400860b0314511491506001b4841d225200164001445900051401c58000c0101d8202001d0400c1201044003c000c80024000200e0f01900b4044081c0081d10317044044035a801c1c603181c0000d209041e4030104600da28004d0721508041100c0c2d07400f1088096581c28110706241144c1c00c4445424400c03801c09002039281d51001c5041d1a0700d0320b107482c482c00c1c1d000c0e460650344d9a00b480d07a841d0394418801c00344c07004056622004054011402a114124940c0060030283c1c25a1203120101c02000740420038030500c1c05001c1206003c40400c02c1024541c4400c40c45c104100340e881601c83c151660010401c2606207500c0610540658803441c101c81030300390790350b0042d5446410fa0380180301e960082c400007240c1c104001c0066600c44e225900040c5010002800076840a1080d141a80c40d040c0c40311080c0201a0503110341a01d00c0c00f1b01c20b0190514a0000008007907030903848000700b00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 454271690 1250 454270440 454270457
    0x3020703020c091f0f05062703120a080105010c0312020d09060e0d02070806040203070e090f030f04050907110c041125020907050a0801120305070506012402010e0d 72
    0x2403600c01d02c00561003007002803240300e6070300b05401c6046580b07100c00340c00910001800070004842e440f0240d1501101e9000e0070107810300520344a403400366150401c00509064845501b41c405581c140010f40d050b204500f1700544030350348084001c001500580195041c05802c000c002c01080d0024000c81210b0000c08000d40d071280a2201d0002610884070010030301410070030000e0b2000d0700402d0840701c10300c2c20390841d44015070300c0d541c440e0382c1d880a640103134040d0810003040c010f00034504102036012020306c08442116040c84a814615488274030312540c0508003050074840c52a20603100e5400043c0d40c0380c050f84d950034814803191034070b030504a902d20456459400101d61414042602c0065a80740c41e1a1001d02c0c41c040c1a25030141d07001e0049119103040c00c0069440ca000e8426589403c00303650f20303940141c1c02c1660075a0034800710441601400003d20510002030307020030100b40a40002c4280e403808920703c03002e109070110041000415641400902d080c00900042c285842e5003042c54500e00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 454272940 1250 454271690 454271693
    0x13031d03060a0c172a040b070b0705070510060603060815161803080306040c09080304030605041106071112121e0408160302090f04020f0f060405100206040c0603020c0a03030207 78
    0x2040000c034100a813507013110f00300f005200c0520301150262044035004c0d01d4000034207204030301803900c114091480940e40c10710003800400c1c1061680d40d40001e80d4107000b0302d03001080d00c48624010580c0c520500560f01c5610510410b641802080f00a0000e00c00800c2c01c2169201d0002060794028415007040c0043c01c040881c851103420700c6030841142d690308200a0b030b102c0c00c0203411540110f0300c1e6400b50341452101001c480c8034803aa001213400b1000694102400c698078540980405001aa104140d810000d10f0642c4e4100c010080f442c070030004480345150801c140300000d10039001101175a00124001140403c10004490b035001074502d9604e0051b01d030640034081409150080e4900780301e001210034400d03030818425800c0c0c078000c50342c0c1e171601d0b901c1012a20201c80211002904054030f007a6024007070400d034840422622000b44414100b5407101c020601004010111000507030042c1c0c180020b101d8045c1851018100f280350a44c0740c8407541c0503290342c607800c0c1c810003403c00da4005034100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 454274190 1250 454272940 454272947
    0x20307021002120408010f0e07151107090f0515040b030304051c08040f06020c100c0f020409080a09170a0f0b0403030f0501060302040501030e2a040b04020313031d03060a0c 76
    0x21041c3c6a8103511034a41d80c82d03545450080003058281d5802501d44040700b01c040d072000030840c0498400144c804400f2203d1901190014214100001c41e0322861001040100c414025411041c100b10400120341c070f8650f400280f00d81c03854581034025803400d9060061520b0100c00c45040e260709542d070a098143d008104901130045900241c4129804500070507411026880c40c0120f610729421981c00151420400c201072245e4102200800e400d0308940c80041d00c042d0101c60060700040000030180f449072103200b402d81c0b01072000d0001540c40d100a110150001003650b003111008001002802d94a64840030803600341c880c01740000000c080020205403003a000304404850450061144d5652003d024001c0e4200c1c0c050180440c2c104081c03d049804005680c400c00d650740b2440100c14106d03d40803500300e10380540940c0c1c00903124a40030303e240d00c85000460007000c800510141030011420000c1812200080456210301b900d14008020f40d070015400da0007001d09180042c03030001c04041034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 454275440 1250 454274190 454274203
    0x3081501020c0d0f0b150a060e0f100807140c0c01200d02011a043c02070c031106030c03061302070506040507060f230c03220f06030903020307021002 66
    0x1140e024551070041c030100150a440074204510411000d8940c0c1c0b04c0300e0840d1941b0803a4800150010070081d0100720051180c41d08440e200406002052000d603044003251228900225000c085110310040c49415a8031000c60160703296540030050405100c0041107803941200f8010714100710880c0544c00d180342000105c038000e8200c0d58200c8003040ca032404080c1c060909110038000050b1501d601c45410308041c0154940703201580d9042d074060b111113010750400c02480100703c40300d02003480c401540207814402021054041c2c5400e41d0802d1039851300814a061043c00c69005103030078400c0c4000549510300b1b49400a07021030f0740043c0e0f800c000d24803c00034000d0050280507480381c40207200034490003003208000d54000303503510032201c04c1e8101c09030b41448290120002490303c48208440e41440b54000e82404c0454505491401180707015924135036000d01d80c22806201c010204102c4503200b00e040100400290800740403c40d040c0e02c000c0c2d1240a17052000c0e015003202458031150a01c00e0018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 454276690 1250 454275440 454275463
    0x30040803040b070203030f0c060114010c023003070c090e010b1c020f0d06021b0316020f030f010e060108010c080609060402031e0c0c060a09020f130f020304111003090308150102 78
    0x101e0740711080c030700807189c0d80d800070b2180e0800c81c1d220404e040350952085820f00398458000c0c149203021f5410942080506156421881d05a001c54000701d00030324051004126003409050140a00390030840c50700101c4940c461240480e0b89428504280342c3c440b8007d40056100c40c3d21121522491030004c5000c01d0050078406510610002d2100100051640a8618100d1b0816140c00e00403281c034800d5900d2084100107601141000c601c04010314202c040e00c0c01d07800020f42502c520040c0c504032942525000c03108d0003510b030071540042c05020070074411001922024038180e211402d162022422203880030300482d02071a000400116501100b920316281180003000035000da01d480d0104100607005000e4900326030103400c001c10510803140c0102c01001d900102406002c3c12540204404168111004988182c450030044038a00b141d2001e14811402012540403080d900c3d0108100e421400410f03406161816101201003130707003c40d9981d0b00000c480302c00840080c08800613803801d00c51481 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 454277940 1250 454276690 454276717
    0x60a020d121509020d0510051f11030c010c020d02060423031c24150f170709060908030c060103140f1b0306070c0305030610090830040803040b07020303 67
    0x80000b00d943c01039000b0001101c000008001c280c9402240da6903240b0315100742c0b40d008800040d05008040c2e414400510b00784a4107007100c5804400f4546402c581100002c49041e0759940e20217410f4a40600c60301822032982c0c4003601c1c482c0f43c259188a8184c801140c031900740b5040c1143e0503040070040044440e580c80504441c01640902103041d4090000b425031403d140640e5081100191021054441038603600b41c0a10680c2504a070100e030088001c02100c0308100400e01565080d01481201e81d00440041d40c4281481d070070500040d0061996a1240c44654020080b0420680c0e001c88e440d41500c1e0b02084c0d82000e110a143c2c900e180c004039040c07062140c06841d80900e0f0001c00d07200b4060003100140c2c26111265640181541c50b0240c070080603021500400000d442482d00e13140ea6031030070391941055080c00e41c451078214581011403075800880340110309003111405201840039452340000303000740d180c41d080c05005a03e0740220300c00d600303180e4004a4000115034092003524004a070221 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 454279190 1250 454277940 454277981
    0x30307081801050d05090f0c0a03020a090b0a0f0b0c011b020a0b04080d0f0f1103040203030417070e090d020c0405090a0b040c051909060503013305091e06060a020d12 73
    0x4096441f400620f0034201c2c10720490580150700d0924011050440c5e4000344000ca800380342611a001a0110740c44280c4d01c1600c820021036240c0c68001c840b0041c2600440d103a840303601442003d400c5600904c3e04981d01c0900c2800d5409450b030000ba10845a035219504035503945a61815095501035640301000e040e0030182c9100c0104016884046155003200e01406102d0145240c10494801501e000c0e4260b001040306100e0b0b00c021254048880c444d04040341c119641e0340d00074901040081eaa840c2c0c4542041d0360000010394100b00704000c03a9030898040010342440c143e050b503204c0711304600802c0c7c03141e441c00281c14030448100c2c0e4402003402400b610400c010303402c22030344a0720103800b4541e4190700d048030216441c14140311719a101d440740c03a410762800401d40720060050001c140340741c00069480c2c401240a4480d84e6400f40121140410b50400c412a9511410f00030001400359026402c14808100342d00da001074030203500c0d1a0f1341021a00300402c0b00c10032000d80140a007101d0a2903422 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 454280440 1250 454279190 454279201
    0x12090503031e0f07050f1305030a0b1503070501120903020f0f03040611011a04021605010903030b040e060c090f030a0c03080d0c03022106030a1e060b030307081801050d05 75
    0x51012295985000150450b165150103c40d80006001d9a4200000700c040c00401c141d0601d032001440e0b00e6881304d44400d800d55072000000c2c0b529003204030450f820003010091140b12400300002101440c412070142004a06240008100540d0858142c40302911201a04107040c001d12110550f0f000d01c0c3c05485461044960312279580e071080c0b0826001502c40802d00d10005010b224a0b07030103410f01003201417440c00540402c07020350441c030400f000e41100854900c0c00100709106107044284262008100000924104000c540390240b400d4a581c02000c1000382c800020400c8a02d01003084030000d0030500c480c80443d217400d1100c80c008101010031280401882001d8010b05600482c3c0c450921144003072034070032400ea0203108145c0950070a818001c176041000704400961040e006000c613600003c1c0d68070703030110203402c0c0782e40f108140354803400035810b00403140070741160010107400540ca0300e0119900e011641c40f410395440c00f004241d07811800140c0c4140c0072501070710000c0506020302c0c10003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 454281690 1250 454280440 454280461
    0xf0525030f0801030b04110a0e1003110a080717011518150e0412110307030504030203060106050f0706050a02040e180705010f0c060b030f070608101d071209050303 72
    0x910009901140241800d8005584a100078070b0580380e02c10301c44032158569a44144500000c035504542c0444400d0000c101182001d040b03d11501001c40040803d515505000c401420b101031110f004840a00052100c110006807030402c5519260424600c80e8280c246540180791011080c18074042886000070060f242c0d500c01c03131851b058440200810345026030009054500c921400c203034542d03c8030000e004904000c20f1045041220f080170004501c444070098103590014004401142000c241881903081c100081405010f040c109070703140c1000a080b1007070500996038005d01003903c50000072010382198054030020810801e134030303802d030502d02c0c49021440742c419401c50581c8107401e400500d07588529200b007120a15604c510800b1109900c40c00f000e4092400495050300ca0400e6160840ca410040c4000511550340d8403143d5042141b809110f2040ca580518040012031181018690b800c5103ca9042409030505000102001191001403d600800984580000300402c0070540e036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 454282940 1250 454281690 454281757
    0x30e09072a081b030d0e011406040c021c020d120c051903110304080304021806060f0a020106030b0c030f01090b060a050309010b040f020c0f010e0601120314071b060c120f05 76
    0x2034804180506030b81c1c01c6d82c66080340c43d100c9104542407541004a00b8a04055200310407500711803040e501d131407075166095509030308240404001030740040030700b40c00c8035400a4000020038080703405101c0d0846101c0010014028182401040d601001100c802580607500000c140a00300035007903140d142138101465107400450701a800f07001090096001207801c0b10f9824401c040040c800c2d81000d48118460825400920300d1006542da2200040b01140302480c00e1031280115083c095a2850200703102d842c01441a4012407884d420050407517056030713400d41910034003c00c82c60116141d542e0000084d02601c5946500c039081071138207445100c0d8202680050401314013210486007000d504003409404c903504101001d0858000c50010702c40c0c00c4600e00386881940c028504450b4034007401c0c02440c89a401414122109120b904646210304d62000c400c000501880c105000014203a48900722a4000c0468800400c1604128001228080d03810394148502c0c4110a0030058080c5540c8a224132 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 454284190 1250 454282940 454282957
    0x170f0721150b032a121f05010809070302060307030615091e05090a052805040204061202090a050c0c0709050402041413080a0203090409030e09072a081b03 68
    0x110034007000c14110302400450b0b001e040a000c0000043d440410f030000d841000108a0411410400c940054600340354201c50013080b1a946003131102d01b22404981c0480301d40e0340901d06201400b802c0001c2c0b490007144410850742c0582d100c5943e0364807090b044005140c00d41207140380c2680d000290405a60100001064400994200305240300103040d1112150302132149941c07200248000034507201d0705030046500074201086200401c110340440c500010b510311310802c5503580d01d0007008150300d41401850b004190341130700f00c6030300030090b0041110500018080481281c4a10110310386038848000c8851014555069a402030340b51000d80c4081c280c19581648150f0401d0320030b40d043c120728000540a48500018081e000307000350b44210a0350040079403d02540001e00ca01c003902d842c0c0c0e00446c400b2501ca591010f00d0b0031042020048801c40c00740c4407001b0402c000e4580000394101c0400002030340d842c000202c580400c54036000c0b01da8841c41c9450201100c00d1984048078078000005000d0702d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 454285440 1250 454284190 454284221
    0x90b010504090c1224060507061b050c070504050c070f14061e010f060e1302070c1203020609300f0c0c1005180904060e120c0d170f0721 60
    0x3400150050001764480b4a00ba81018840703117800c10403c2c0c01103000b03000c41403080102017241070902d8484510b10b0340f01d40c90100401d0300055241070000382032060b6009000112820051b50501480340c100c00e00404030024281e00f41121580f007803080e2034560348507585000084603c1803a0003040c0034610180741c203083d04100505000440d124010350321500c1511015954000001801400c1000038003020030f501004a508001040204140c1c0c07038610040c000d4101072700c010310410702c0c000b40ba10000500d0115550003160080310403480c45140c041c01c00f0340d5800761b084841c401d100001c01c5071151070700801e000d550009007820100d1005ca007603401c50304211b03941340c045040c00200340c455205106804050754115aa0900035140003441140c215004510028900e400500c0080c5060511a031219840c280410a00c140071410005040220707010300e005210b010092941d00c1c0e10280160003150840721503000105541e2064410607004403c4524403600c1030805140da20003048240e2208110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 454286690 1250 454285440 454285451
    0xe0d05060c0a3015330e0a03060c03110d0603030806120607030c09030212061f1202060a0e0306010306150b0427060504060e15030604030207090b010504090c12 70
    0x752841c00303030800c00d440c0c01c035030b2103082e03e20b14000004001c00c82d58440c0f40d006903045201013000c0140440c0301034642c0800c0f042c2d0310311070b41c09010240500ca054035900e041045159246e481c81e22030244001c00c0325448a00482d411260030816400340142e8485080707403035000715107810013000076000981101d000b40c96442d403c0e12503200340300c80300d107003c148403186a20800114007824071075800314185845500c0d0044100e81c41f0360001d1880c003034110010040e0760202d4144549820703c5880101c6100780c582c40100c1082c945840c00c501c00601410103445000302141342c012039401203545012841004080e200c480d038480c2340c000000c151000310084200d851243c04a811f410740c0d401c42e002d0f6424581100210403500d030700b50b980280140e0a81c076880c1d03100c0c3c000103800e807510300400300a0211000c60003490702e4030301c0708c1c0d034221804407105600c00e0303202c90280000f09070042042c40c103443c000305020400454420041c5d0303482c8190b9000180d09498502190800765000190990380c94009005022 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 454287940 1250 454286690 454286717
    0x30b042405030105072c060307032a1d0307030b010314101e05100905070f080c0a080402060a1803080301080c0901060e0d0f050102040f1d090c010e0d05060c0a 70
    0x2284d90448000c404504101014481040314182403804415a0342102c1800400500070400f290015504100880d8407a640e001e0810000150b03c5985542003044462010341c14038001e0040c5176118208160a0703000030109020345051140001840c1c1000d0003c0e1596500c0c40e00f03254445038031401d0065809000d070f4a0314041840d006540340981c01d12040140d10941e510760000514010304000e02400d141d6038001400201c500640d40b040780a0f407101419100b40c80f4018005040007845020782e841c0c10010352070726a40098085030000d8042e40c443d601da0702c0d020f00c2514900c0c81c0400245c10601240700020401c22031070011816184444250380499440c501031081c000d000b070140d107002c20001c036000f203000d041c00c110031190a40109912070054440d5114603089a020340c212114021211809000d20008105065100d900c810790400c018035104003055107400340c501c9440d0402010301102500d540c0d4003241d000030306420000750340480c1064180c8000744c6c0e020042d06004030f20700c4424200d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 454289190 1250 454287940 454287943
    0xc0f0703022109130501120b130f060b2412090703060204030c0620120c010908120f070206151c05060709060e060405011b080714070303090b0f0a0f030b04240503 71
    0x11b04949010b41c107015000020b540321024071720010b05210010200d9015a000b044c079031a410350b040350040c24001550a000018013541d01304807080a5a03d5011092100e007030190355040315008504a802c001c20b03521411901800d100550f48007824035800410084203100c050040e4900301e8800b5203607026039540101000300c0d00f04100100c0320140d0001080e840050744101d000703159121440c2c0c00000c2c5250300b90b495148641100d040040c45140702010091031180c0c40100d6500465180001c101c0d6160401c491561a03440390680c6005041032407a0400b540c10490581020710340c00f1007503c0c2e0301e1500f004000e03c12032407445001d0000d80c1c04480c82d401820000c0c01c650640d00c060750b13156890500d031030001c0381c00c0181803401c46104208004030804150700d6803100c07448203410350140c1071141c994180103045c0344458126003c285010000203940192150459201007503e00f4281103400007001c2c00d034010203007400c440d40c004d410606400034420b10714030000210002c203440d18006a4403902410b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 454290440 1250 454289190 454289201
    0x60e0a080a020f010504091409010b010309121d040f0b03071e05190803270108060a15030e030430080702010c0c09020703110d080c0f070302210913 65
    0x11154100c1c28030305000d8145005008442c0c001030420515017940d4002c514103d4411241c8109000240f0003031101a580a00400c8400d00302441c2c24002520251110207240795280702030414001205020283d411101484040c01e003030051041050441c504030005c050100700f54118841e00480c2000b15915104c100c051f0391642002c486482c40e9400c100038482c00350144080003030701000141001803400b80c100f00034a0b0b41c81e101540c4101880b03a00800c0f070540e821b01e85845044c000310000300204c0740c0f50200381c4070440348800041240401e010005500400b5030000c6003015000000780810031014080000c07000c40300e27080b54003081100345a02030a03501141c1100404070101040500702540c412100e008002c1e00500441c1261a6940b070281d089911600301140400d00d0741080c100580b106211c0783c0f440e000942041c0040d494000d0100003188289040c40030002000300303a6100703140c8200045a0442031200070302d070b40500c0012031148280c2018107003901c5880d01d6400710300c141c40d150141 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 454291690 1250 454290440 454290449
    0x803010504050f0115120b041508061e07030b01030e0729071a0405030c07030c03020a170c1e040603080d0509030c06072003030f0f0604060b160303060b0d0501060e0a 73
    0x5490100b0031020860f107007001000b002e606c540d1034900a2a041d41d40e0300c100c400c103c940d1261011442e180918483c18030000030880c40c40a8030b1040601c00019098030080d501008030715000900ea40c991005074002d00003440303844000d1050b000e0206000c0502e0b46000004030f400c2101e204000c070a8060954a0b1140100c02480602880c24400b10007042d0881b02da00030740b1440541e401c10820404d070b9460507116620036a210402d2400400940c1400329413100604032017044144186400c10740e046d40c2d4890129110300a02c03034001d0091a2803a008100c8085100040c07040c0015507890418200541041140602d039518080100d448004000300301c0703c44100d000c024007407a1f234904074256400507107401260f400d5031014180d40051041400114850f144180c4070b032807142441001c030f03000d42c44000d00c201d019074500710f01403040070b020300107540a000101c0800c03601d9540c28039003200a050a035005117004000030451904a103ca50840c80c143c4181c0d40c0c40c1c03440d0b060502d080240b012064807c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 454292940 1250 454291690 454291709
    0xc12090501150b0a1b140d05030f060109050916050c100209040e0105040201140a1e0c03030606030204050d0b09030c01180b0a0504110607030e060f071e0b0105130603020303070803010504050f01 85
    0x103240b6485c50140c100c800d045000e142c414404800710503a4a061580709030340304000400000c1040303490049280c0c4103420080a00c1e00c200c032a4209404210141d2020304000c80300e80e100442d00c4038651051089800e0303180d084c02a00c0d4441000386540c000307504500300d418442d600b014002d800d0384074144a403505c110f0301652501035280101010040c180c2c081c0102d41c04000c107841a0100c0000315860110800c43d555507a4555040107084c001c0482d24a90481ea0030140100000c003c43c0ea1002e400c440c400350841c5905413180c5403c00c082d4030710320959149011950a141e050807100d034522482d0507000c0d0003032020440a6880100b0b02044500440b0300400c1517251401903500303400d164018042040c481d041410303506918400240d003036007003001620100000003500740c04000d11107080c1341c2001070800300c0015043d203664410b03525440501415025002c10706411288402c00e0f00039000440d00541940da4965840c103144940c0e52090058034007840c10324010078030007400060b005049030310b00907 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 454294190 1250 454292940 454292957
    0x3120f07020901050d1e030c1a07080a14010501050901091715090105042402090a320d0201140f03010603140114010e13141f050901080d030c12090501150b0a 69
    0x451b0390080f441904015810484180c0100000400c51140c070541005c0c003078001d459501d000c01e0010000341004090780001424102452721002e03404451a0541e0301c00d081494541039100f00480b1546180e503c10700d1244c26900014020440209114140038400c0c04000074559501664500380c0b40700765402030460552000420700042c0f003051a9950021007480540b90461441c005508482281c205c0d4440c2e04001c40000001d00c1c1d000c162040c0d401070f16603c40300020741000010711200d407450029040c0318015818905018580342151054001908401d44950b103501d07000740145080c0e14544007103c0004008038503070114103040c400c1250169aa440c03140e02003018030200b5000942d150305144e80b1445101102090040b4151041171429034100c041500301149002d00e5507642c0c403c80c065940c201c014400644040b921031060411420003180710342440000710340c802141c0300d01500891400254004001064102d450005448448541603c1d110200e9444034403427040c40001180614 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 454295440 1250 454294190 454294223
    0x3060b1306030902061c050a0f1a100201020f04120507060306120f0c050a061d1012110d090305130806010b0d0905030c19060c02030415050903120f07020901050d 71
    0xb504156a6148007030034260a004c0d40000040d540000d006c06170aa035500c0f0810403240520030310618405c02c50001090003201c041090111007803003507111207401011a918040983c50003501211a00c01750b46c400c00d0703644e80d92810040400c50803141c00304c0c1d6a003d04880040c0d00780c03080c000d11040e21a580c030014003074078095030348602e00d2403180700c1191000303010400000c041c1d4403007a424004048903160f02c112110300c20712103446001c1d0002d00d64819070048901c1c0c01d015034042903e09003541146000120810310021280c0e00e4012411041a050305004410b410503034040d020303001c071000518104000a445450303840d11070303009009000b074042c418021161000b600d90030030450603010740d054030315203101311003018140303801925110030310144211030f4000c200151141184494441c4080c2d8240750503e80c21201d072010b0144030004100c030118245056913014041d00c1d2a2401c1001c22541e0345100007030030a245d0300901c0d8260300c12841d0800000311070800203000104603600013084a00e007402d9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 454296690 1250 454295440 454295447
    0x170c03010b040e040c1a091302041a030a0f1e0c090506250b07080103020a080705130e150f01090c020120030c071401020310080c01020a02040b060904050c0a03060b1306 74
    0x3032040d510f00040350400215542c84421460680501c04112981c0d650391400703004232403148136085c3d141c1034810003007080746d20b5207000b45040c41020742d00140c1da0798031001401c10290500d00c825139003883c50300d05c0100d40c17010003211403078180300540014040b0900744501522030346907500c12282c20550030028403195a002182c820244d1300c20908403c045007140d1142d024180007210407402007804007005001b5850300c01e5a000c0100b003030700c0003406410704020102d52140b0303150426040c129203818145e0b102d0f9605006855550700d1340030380d46400f881c089080e400c07424400c0c402d100201d03151200c2c0400d41481070003004c2c1c108402c4240c99058800b01780000c4550750004001051140c0280800000100b507a648020908101c81c0090b840c1d040010382c01e03120348115030112625a0100700d0404403641c02240c2200b005030116800650001084003281c81c0c2d02c2468401d035405803901003040428600721001c3e0914250f559001c01c60745460b00103620503485070484c0d8200c43d001c2043c041000b20710 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 454297940 1250 454296690 454296719
    0x4030e100311040b040812030403090b1b0d020109060513110d050f060c180906010806040905011b0203041502150c0322030e0117010b0417160303170c03010b04 70
    0xc0c41c9070000c1c2001d051041007201d43c1098000302e140c110001800c02010310308000610002c8207043d0010700e1400c2545d800340901306988250307055140089101d42c0c420344140c5048580200080c103030303110380b00f84400c024000c248980b811190140380c07a000c00c605140c003040e807070b04055100c49880310460443d010080c03201444902103441e0b02c9620b130703074501d42d00302440000d000d04030300e622550b01c030f4240c022200b0300c0003001911140219150010030215a911004d034907040300f4180c90001c2c110b081401c15602605404000c0303d0f0f0300c0c8400c940c0101d8030394000004d10440325400ea110394039400c924401c988400189903004c5c440c44076440441c3c1c4c00c0100c00c00843d0805100011203290400c1c15032014600c0d00c0c04101580412031031210007000d9600700354100700351032a90704640c85645c14410040194011805640280007030080c41030340792142008200c19404c02030081c42e81c000d55030f260003000300e848500050030815031200890200c000c00ca0540e4144c4802444850819092040070560b1a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 454299190 1250 454297940 454297969
    0x306220f060b0a08070f0c020418080324031c08071701121407270b0d050705030d0c0b0402100e0a090c020d020703020f330403030f050304030e 63
    0x203664054010803a0a1441900024100b100c001e54680c03108420240440300010005428416207040c64a40640c0c000c0e440d141c0c40b6812980042e60f44008103921120340c0122030005c055010000038041400c02c1d605440306c842174806000800302070f80500703041d1601c0c0c03140d900b440c100c0f5418000d501418001e05642e07501c078100e450104c40126a00041182c02d64080e0f00080c1c00780c00c00c250110a01400c90200c00a03040d0400040c00480d203000070340100d011b21111303040448105154440290a00d9030060f81a40c0390040a41142c8041810260344580d10303845450710a10901034002102030141d40500042500585e019a00d5078441d028040079607101e444440030008040c01040e440c0d55641c0f1450090064054002203048500d44060b2500456156107015503000c0e1074200010796030040b020345080b00540381c004a210b044050010500c504081c0034007201c1c00b0ba04600103034402d202c044c0040300e01a94030b001c0030306500700058820744001c0e00c0246c001801c10042c51070030304200502c80b1142 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 454300440 1250 454299190 454299259
    0xf0d170f07051b091312180b07060b01090e0c03151c03020f070602030705070308090f0a080a0201020706170601080c0c01020403050708120a21200307080109020306 72
    0x1a5a5225800c0c910b0490f041240c43c414162071143c0360414440141d4402000380d88405044200c2c1c880c0510902d0f000542e400f04040384841d054207200c402c032810001c0152180d40d1351142c44a1078854003174100307000d503e400204888800140406040042d9010300901030070545161a4021a1b8520203182100140c01c54100e0840000860b81a400c0c0c498840c002d6010740320800c82c103121241031a5003540f01c04215401400b585003c1362000c5001e400700ca5211014a0340d03801c188001c103200f20410480140c1c800811a000149180d003c68101d542c3c41c401d0303081d1000180c81f8030044d1000c8400181c0c003241c01c007155000a5055029076940c5401003900314120303042040c203007001c600360f80c81a00101c40b00e4008241c1004101c41c10000103800e07035440c40c0b1448c01d050361001300521507841280d040002820b811034403550184250700034140e204808440414a00c0786440d0411650700550341000000c1c980c01c00001c69080e030344280c0740078080080120782c0b1001c58404884044100c040c648800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 454301690 1250 454300440 454300447
    0x1e150f0403032a0b0f06010e0f0d02180f0403090803031b090102010f0239030a0818150702060a09050d0309021305010617071b080a0513060503060f0d170f 68
    0x140c0d4485503000024842c50b0f030792002d8600740305005085c1001900352410f00004c4146240350b03076a1611540c04841059980310001c9003280009514016240e0ba415000da40e00d10500c5844030f15903100c503200f00d000e034440203026075540c9415503aa21080364500d0706490328000fa60604019880100a861414030000c144c11070b4204022040ba44518044c0d82003200c402c241d84185d0300c644100f60a0f001e00514412403261070b00d04107580340c1c0728144181003005024000508a8240070b19156803151506089808a04210041c44941c0d4400d13540500944200000502821b21354018045d600b87e2000240000581d04001600030307028105c400ca0f03010003403050100c040001482001e008042a65900c0c0d99920341d0794103101549400b610760810411001034507001d140305110075031666036000c03000942c3c80384c840c00100e450b801070080101c104080d510b0009a0035501c6000f440c020712040340c20304042c07040f80003004001c1c00c512070000c0c0a508085d801d4481d680d8004068001ca0b074070301c00c900d0700c4c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 454302940 1250 454301690 454301747
    0x7050c01021b0d0f0206010506041401020a0618110306060a0603051512010605090f0405030711010c140d090f180203090307080403060f0501051206060d030302091e150f040303 77
    0x5101c00001c90042c598414007040b80c007540d21405409075085070303001422007941890040741c41d41c8958026058080a840b10060b4103034400c000c410305464000e201003015450314114048603040c05c20080e01c504825042040d01ca103004034034a0f004174001000321446034684a41035015023002403290034042e006070400049074a503c84214661440c0380000507115050008101101c00040c10000101f00e400d810040013030700002c01c84403d1034000c2d00b11401350244038012507031880b5909000340b0800d00c0500700d41030b0000c0001c400300d00e0f500680369041c0d80b030788411080c41d06880c1441000241c49101c03412142c5030f80e40350300070b40c0c10002400a5a00c1c00d541d0351240e001c5940315920440f5510380c0d541c0c0a800010a9101c1e00c1d0161004070766205180d42c205090f80c1d03072800080e000b80e2152070112011303130400d4080da0440c0c0b01d0690241180110300628554000d201d48848800da025852801c8142c2040700310004441036015013201c002e00b0a800c0d5142210b82038851015001001000d0420a8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 454304190 1250 454302940 454302967
    0x9011109210f0d020f1c051806040909050604050105061207052206240306050f01260a0b011b051f09170d0c02060f0105010c08040506030c03061c0201020607050c0102 73
    0x111101c0480c3c004110300d0305c40c076500f1850400105001c01c1d5a07051070041018580c1c0c08001c44808617440004040550083c20000b0380500c92603021810380d501e401c00c9082082404100144103500550003000640d4075002400081c1d02900200c51141d00426014802d07840e01e6100c14440c2554541480ca5180480e8220812076109821040320415900c43c4c00ea500b07100f00352600b12020440c64148401c0303107001301280004042400b680c2c144001c4600d80350396512010001041d44c450381e002c02d41e581c02d01c03095010041c9810046140001d480107002d007102c1d04c0c250580c0180d141c1c440001c0443c05400109450002207008981c4d442c2910f480a582c0440ca10422100c0e01607045c8224981e1018201c402504440303412180c40150b41080040107408049900b68504584003801c0800c1d10f0ba16600d055400c900c1541c02890344a007021084c0117544550b000a180b01e01d81c19a240c00381e14060740c4d41d09442e041c1ca00c2000f40180e000d0300008144921403400341c8525180c100c00541022103086041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 454305440 1250 454304190 454304203
    0x80c03060402130302060f04030b07051903020d0e0a1101020d051305010f12020a03140a05070909150306020408030d110c03030c07031209050c040f0621050a170309011109210f 77
    0x1413451f880045000e0081c400152112a000f04450510a14068004c200030f00d00400807841c010174550f0100e000c4803044016007148031591b034040c00703440b0360344610f2030042c03034007550400c0c0341e0300510805032a801c9150082080b9420f00d10150420b0240e0703858200110340300e50100240b00308020b0850150821005031b400600809200c070345010900140316100c10a00e07120081079601d0342411700b024046c2860b00a01088192505d04001056501000e030402c0d00d00c44456000500107440080d0001d491140403014040d55a64108244000c50f20000d10424078000c6c41b0300c00e1416001007001c00d070700384100300c024006280309003031140541c0e04034400e84084681c00380c8203844030381083c42c04040a00c0c1c1807040b00000a0908820880c5905020250500609012080050b4400d008880041c00400c009000b0625407125200203084005c1140321455003007503170704806940c01d0400c403c2006e4200c00540d00d20702e10280000819034010401040745200301e03441d06e1103a004030b10088071140011f000b034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 454306690 1250 454305440 454305457
    0x60c0303040b071e140f0c21070213150e0c0304150527070b0c100b0109141c0611090306060907020304030311010e07031a07080c0306040213030206 65
    0x6140c49103400e003054400120001c200c2e804014041030b01070118000c0c2420101d1000d06417400c0e40034a1200d102d00c140c644a19401c2c031000e030720045081c80c4400c200288a8864101008002d26807201d84080089203004202d0000c0d0b100301008280d020b401501ea024000c41e0040000c202015030b40c1d00410b070f1102c541900c0f07400748034000004000600019a08001d089680c041e010040b62030900c40ea0007417624071283d1412081c40724038031008204802c0001324040c00c0303c1e034070040c3d079801c40c0a9181c4c0e8900d0710200c3d8540c0781d800d00c982c03140250301030445a42251002141c03c0449805501000042c0e0710002043c1041c01d4140300040c04034006101369074844594200d1580d41c5d010f8a0105807071f140000b4402840340400604010640b50f000c400e40e0205d0380d150070844446c414800140740940080d1000956520a0103000030600c005d01102e130340940700701d110400c45034a619004031085903045464074024441080400c000c2e0401d5030041080400c2d40030305810080d12030b8001485940800725 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 454307940 1250 454306690 454306693
    0x221030a052b020702101107180e0d0206040506010f060909021c15140a1d090307200405011e05060904060305030d200406020c040218061605010605010f0905090a0b060c 74
    0x48100440c201188000c004c40c900d400e110810796880205241c0d02d1031140141c027818281d440c0c00080058140d0410009940340e14140c804882d40710710300035540e980c121000e46041c812603000180415660010b8420b4980c56034030301c1c14181c1071120040280d80084486070b20001204400d07000c00c0c0862017004c1e243c011541740340c100f551502c484c0384000c0c8034028040e8880c0510a070104107410030409440380001c0005080902a0307502d039000340c210300428101410018071000c01c1e6510004030820500000000c072010401340e625824403400503015040e041c44200d0712103205200500d8950b01801c0048801000032078101d40b41d560b11801e682000c400300801c0e0b900c440c0f048a40c80301400d1029650b420160449041030f140a00084d500c0040400c1d15005a0340042d03041182880c0c0008003400703600152815a44186580d0f4180e00342404074020f407801e510708100482c0541c4540400785503200142d4034000c1c0c03035060204104121401414030002c2a035151180007007610740d440500b180302d62420 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 454309190 1250 454307940 454307947
    0xd050607020715051215090c0306130513030804080f0a02030306040c0f080a02030604180b061206100302060c01021e04080708070b030c16060510030221030a052b02 72
    0x300301034039141c00d9820082c0d4050162449811607603001040e00d03066160102c0c03051070368440300d000d68040b40a0100a075000b0060000300300c1c0d8200f00c0d40007540942820355416080c0015103004800301d03841a03911009920b140d03012600460720507104130f500a401011981d00d0072001c801d481d6203960103841c9100160b00048101304882ca0103203d0741500c40d80364204a0148020517000078080a4010b201c2c40580b940400410010345450740102e0814a601c5802400c0154500745507030108400c8450502c04e0407401c00442c10940049804c40c01806102d401c1d880a80c115400c0142c0c642001402240940d4207010813a01078030f00c0428a40548050260390f540c80e41006030301401c009194100c5d40084d44009020017a24090074210f9612940c0141c280391185c03d903010741c00c66458001e80180c41e660030f020501c441080d4450f07200302282d10884086241d4030f4142000e68034200003030391440c078640080c0320300c0c4102801580105000d06d030003003069a442e181440004036502515065841295010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 454310440 1250 454309190 454309201
    0xf0415270302010e0a1a0304060e030313060e0708120d1401030803010512072103020f010c05030a0b010804350d1d0f101503060e1b010f050a08040c050d0506 69
    0x204180404c210162a8181c0940c10906003150002e418400e0442d000030000014040c04410b070321100850b0304002c10b5954070305042ea0052000c0141210907038000c4e28001d044081c01a0005080d411203038108040c101c0d04212800b281d080c0e40000402081040e2501c4403900000b8109690602840c07103110059101d5061406000060444040c400300940c003091003030014001c80c25510a1506103110342007084080703450101d05018a84003481515802c03c540c00c0032a44e0070501941c811940914100303c81c90142004503000d03102900d000e096a039840720f0704498451004012951044860801c1560500019540b44aa070007860315512841c6c0c0d0750684518411281c4420308100203510013412106001068961144002803800c03031080e42c3c0b00d4601c2500c0e0400b10410000f1a0881c104003c0707103e4a40c807080c0c0300c242607011922400340a800c0b030f15681d030041d0003003031030078406599007400d016250000303545886026100b602d9145c4c144000080c20343d2400558030700e151045000c0c104038100b2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 454311690 1250 454310440 454310447
    0x306050115091a090d06021206130605180c04080a05010c0f03060303120c020c060706150e07082202060d0b030d02060702150a110403050a0c0b0f041527030201 70
    0x30201d9800708030401c00c080008058100c0b444404000c4144402d07513030300c0400300040c1400942c5500400c92400170401e508040400040580f00365420754405508203002450102164030300c0c054158000b01c1a0500c8040301c040940b055403000e07034400c0a9250a840d000384514042038400304850aa4540c7c115440180d8003c40c0400c03090b080f030a00740b00c020b00356034024200861091045512903620580041c10900c05c0180d41e400340310161039103a58281609141c40544519420301610700f0b804000010118401c003240343c800c2d0103075030381d1210584a0300c1010110a000c0c91022200407000c00a25016980369002404501900440015002013640900d81002c0c6141100700949d0003803c2040085034000c41c82e286858440c3d10b11301d1107035480c0ca282400924041c3c001a07603581001c64003104212000900c2100c040c050801c3c2000c413030b0750704841841071040c821108000c501c03d000070001e07002d03c0d2840c0c0941901c00d0815034460b02c161282000c02524400d66002004810001002076580 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 454312940 1250 454311690 454311719
    0x4140a051b1504060c020a03140d110c01081807030219140d0519020103150e0906090a020d030e180a0b0438060c01091505071106040215070203010603060501 69
    0x40c0c4201c503000c8281150b0001d40c3c00f40c0d100f2001402074440703101045544200003407024541c84981100085080103c1a03a101181e0154402003041900102700518002503521a0790728140d4654019035180b0928034508400314071841c02510503a20f0102c0140d50b640030420000700c8031081c462081e17141400040da005c145d4003840f40510101c01c0340202086001c1013490000c80d9070302111880d0b6444d880100e009022050714016041c21501020840c810130b404598005c22174203046620b16103c40e1031058031641455402503015070186084070000e03000301c0b03220311b91400c0200080503060000c050702a5449044038480009965900c400e4414a054812689151b03644400c11000701d1182140030071000d00514480291070100a0295482d5126011143c55031010002800202c50510b401e811900d414218068190704041c00190300f9441610b800c421018070f10024031240d165a000d101c221801240c213010590f41c200600c0300581c80901441000310310034407002500c0d6141058403981000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 454314190 1250 454312940 454312993
    0xf06111216020a090c0c020922050f010c09140d0c15020a05071a07080903030408150703050f0606180102030409062301080c0d0507031d0a12031104090504140a05 71
    0x14541032001784815400382000c3c118039419655201c3c0387d2590429114074901300b031810b2640303c1e040440032080090211380c81d01e50b41c07043c00007801220540c00c820348107442d007030045000384040801c04100c149415991500628002d45d00e08000c5502d5a1a9a8030301d08821920b83c096480f540410080050130040386005200891420b0700d40c0d5515104c045c00d030f1203800806400c050010400d6003481d50140200c0b002402d07900704481311040071182615010b0403ca40d0500460318080001e40c0c003100d101039951161800800544c6800c0340358035141c1e90412a0790b9190304611003480b010864443c1c1d4030580c40070b04105100d00a04001d00c920030101c9200200c44581081900000d01c00b80c255900c064500c1d103070000c5804034256a0b000c50860040c1002416180c1c0811900081c0d400d000c00031495100d064040e40c400c0d580c69040c61402c1d010f51360b991002400040302084100100f4000d035101c190402d1042c080030226200e615182403502c00c2519050342e80b42c009030f1102044c11842c2c0740504221 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 454315440 1250 454314190 454314209
    0x314030304032d0e0a0e0403260106080c030a1401060207170309061e16060e10090203031b0a1a0f010f0e0c0304111003061503060f06111216020a 64
    0xc40071240c0300004400b422a0711020301035852409160707550750451403009411b039592481c005141c50f00300280300d0080780c01c00c44100c8501e00c14803403014442c518054107840c41a01d60080603210945c0701c9070a0351006011104280e561035411000d007511029040c020050b07a4011702c0c005003003000049080c9c0f4061001801944200824081900c440e0295103040c0c21202c3c0c0302c611401c0d1600d540c0c02034031034410a2041c03845030590071002c00907154401b10030350a0590484608145501829040b1000c0d6031000e0f40c1f55000348a03080040e41000707240c041c450132000c140c802d4440503076141000101a10840c40036503220008020500c032000714150b004006103012401c09a103030021000d200d500c00ba000705104000000001c040c0030601c0408000d0f14409070541d0b0781d030400d000d0001c000384418010001e80c200c1e1207030050741c0315119015041c1035848400b0031180f030364604001911064103d07021201e09020b0058004003000c0648094007150188a003545088003403031041041800250b000324208 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 454316546 1106 454315440 454315487
    0x30712090819020610140307051305040302010506011b030f0507020d1a240f121902010207050607051c0509100302120a020702060304060510031403030403 68
    0x142c076581081d40c82c6500c01000100d8a452050790582813003c0c1c20755041c0010741c141400c41e50b040304020110741c0e00a654802040c3d20342031a050340546140d650f01007106140c1c080c02810342c003000910303010200c4182900e0203c101121888042c0410856481c08001d980c0203d0464507510303001019100522518a0040380304501030b04c40c482032a22070004180742484080d000181c940910340001d000b808100144051580c0801003140d0103014401e840c7c110802c18050714a860342c1581e80404842850300019141002551069000b91010443c642c0802c4010500f44003041c60044c0a440c40b401a02003101c0c2800b40e503090540c49844950b01e2038203203070194000c1214808800040d0610b0340e603041214201c0c051100042d4000000f04000790004400c0e9010940c464600024030b070810740c803901c0d4a80c55401414020704540e10000a210074103800001c85a070711036103513502011 = true := by decide +kernel

theorem cover : BRFrame.Cov 454136690 454316546 := by
  have h0 := BRFrame.cov_init 454136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 454136690 ≤ n) (h2 : n < 454316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
