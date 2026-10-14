-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3456
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:42:54.776468+00:00
-- url     : https://prove2.me/submissions/d2a415e5-16d3-4e0b-8521-4ba1fe00597c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 621402877 ≤ n < 621582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 621404127 1250 621402877 621402883
    0x506030c130f05100f0219020d05030d15060c12120905070b18030a080717120a02040f06021504060216170a080627060609060a0c0506071b0b06010e03 66
    0x150001882c01441c0300309112500d0a07110703e0250080390300380148001d003407000c06511750881001c020300c032101003088035096442d240894020154001c2c00c1d203030b4800c1e004080b14000c0c0a0110300b2002c0d480c2002010440d28003e0120b030035040e8009004003903086014504075604612501c0e00b940a0f5194441e84000440070440762003e800c4441c0110f45810321108103180015040101c01e1290784200c0850300030442c048101d0352540e4100f0741142550980d007840303280c544038203080782012121a908101e0541825400b07031055401e014000e28020b5a1480100d0b03440f00901c00075402c8680160114000845a0f4014440f50715a440c0c1c14100150f541c8880541400705003035040c80500005001019a500002982d4880340840f081021132038005041400b00003c008010080e1916001051581e40c0e02020f856501c00e0040c41c6c10b81e13901d801240100b07402c0880c4021075142c1f01701d10210f0102801540807210180c40020741038001c0003291161080881c011303000e14103001100800c107a00e0b482c18 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 621405377 1250 621404127 621404129
    0x1918060e0c090a0605150f160b0105032a0d0309120308060a0e0103031709192f0f010503130611030403080901090c030b10080d030e07090c090506030c13 67
    0x40c4041d140d042969001d22005900003040c020941d86060400e1005a6910481c00b000003040080240c9507101700302c0c2032039103200341a0b403d0320000141c5098020884c112001c10305a841c150161020417000250008595401e103001c0b0b504181401c214512504205800c4d490442c001e10b48507030010b594540c0d60410300340c0d5038000d80c0007410000400205041143e040401400c140801307513060340c5191402400084d100d10030780c1400f200c101c0890011603040000d81a83c280d2000c100c0504030051401060300c009041c00304c0744451582108071040c4040669400083c8405000300d40c1c011101401180c2c25403000745910341007182c1846075004100640f154803082c900e0b83d84160b5680c1000c0c02c0107059040700401c2048140e04243c17145000a00c4690550308032944040c5207085611190010605440306800054071032182c80355440015a141e0809034031090920151950991210044801c0c0c541c65422903000c01c51690040120707042910043da8820074a0801504004105103500305240107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 621406627 1250 621405377 621405401
    0x40213290301170c1008010b1e0f0d0e01050c0f13090c020a03090b130308030405191115132d03060506131506050a020f1006030b0708191806 62
    0x800d03018032200f250401032540c41440458800e902600140e40043c01e0030414001c010207004d0104801151180c0b00304849000545041641e4643c50103020800585d045050480700090602c0399541084034188115030050101e81091f514042c20365032403003c07580c080b08828101d030050700000107440480d0b100b0b144508480e60f018117891109810020050742c030a07001441001030420440e4656000344c0c0500e0120790313010030741715102e640300e041560810f168400c1045001441c08035010404c5002c442d4810655000c0700c1110b0030718a5440d88011030b00075a5034440c030041d5240c4041c00340b044c840894041d8034104501d101c2c1c445001045a5412440603802100d8198503202030002905c0d04000000d80c1c80c24182e0b0130000140d41c4580c08040d04d54030b2141d80c050245c0000c0030642c01c0e10912542d001c4001da0340c02c070b803800418070761280024135262105440c90001c0c000403030710b89442003503400d0166406a40c1e50603c030120076500e80040c91680031000056072120207800000d140c41c0100801010b03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 621407877 1250 621406627 621406649
    0xb120703050a170a05030105041503051b030717100e0106080312010906050907020307020d03030b18010e0109050f0f090a02210105090111070b0a14180c040213290301 73
    0x1a245443c4682d07840006050b0380030441445030420b000d9010061303e0454208880c081806501c100b05c2031000100c50300040c056001d180c3c04514131030012900d20b00690b4040d0119034023140c0e904c1d05280d00740c1c010105045550040c40520344452410f80110302484508000002c882d550360080b14950fa0002c010b031ba803040c1048004121480c8988942e40060400390f607401424036100b80005d4491241c000d009104003816201e80003454401d5008036148031010302141c080003806200c542d090b280901c104455401d607900003141c1052a40a011701459003503510351703405d4484506554042000800040542c8110444030005d6503403680c1c0e4400b07030501c1341c0c085e1800e1642d2013441400e40e0401801030b01c0b41da05007280c51625961810888103801c3c4c0213500084551100f942c007401034200407600c0d4032014041c800384595030303500302403030214410184101d92140182105010990084421600321444464400c10100c581e00c043e20f0340f91142c507010391003000764081c0111020740082e001252496 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 621409127 1250 621407877 621407893
    0xd18081e0d020604030504091a0402030108030409060b18060f0c12031501090b0418020405030703030806131103060d0f02030f160806010e13050f0607030f060e1003060b12070305 78
    0xd8207020308040401d5900c003400d0980b909407405445403181e0f1082d5101d6035510750360540003031000d40c41100104001070040d5501e5035503202c500c0c0e8940090040e40c00d028503010340040c080003d041100c0c0385034a402042810b02d1102400c2244170f80050f03a000704560010028400d0344041404801003004010040740d45906100742c9000d55401e074045070034184036401ca41408208114825102115007080b03d400c0050503400034031021340119440f0b142c0520924202004051300300407058031400050700c02da002102d81c001c0311026a4a080040307031a0031820404500c00d420184100d0045a009420740c141c0c13044942d0109290a41c2000c07280b05136040303400040c80500700c5180c040001e0459000400165051005d4050101c0c000391140d1102000035000008001c02400013842c602c020400307448440c0390400014002d85941207004210602d089030210302d2141c042c000b58002c41c118105048c4060031661658000d0001c0c1803550b0b8456100788020103420030402000d40130318800da015000e41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 621410377 1250 621409127 621409183
    0x715020304060f14131506180504030f0503040c05190b0327032517180306010506070f060f11212a03040201120e0303070905120d1808 59
    0x100e60f00540f00340703407000e071300103120b004052000d0031004a0303009010403807441040b046080080809078000c9109407080140307200000c2c81503000b513100b1402034544e000c2d540c40000d070840b864401210b004004504090042c841802c0c0766110300b0b00f0680c085d24091440b0703103030131003080980c00c211420181001801040360300102d2048517204110700e0780b40110304105404000c405596001032542c42c403410204c2030ba10522281e00720300201426242c003c1c41d0b446045419018018401d03003000c6009118000c0005050b04001040354807035500019a9010f01200c2e583d0040680344032080340d041561540180c850f00c03414500100080650200041d81d044048210b81a501e0002003084104c0900f40d160500c0407a0384c8074110070244034001e90b4030b40d0f959452006139681503003030140c1e07000b40e494003030111440f18000000b940038103004d4a652001a585804100180e000f0b0960300c180c580081030020b011a018120707080100c039410300003810b00c0d501c604140c0e00d440503203400154805950706401170b078 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 621411627 1250 621410377 621410381
    0x180801091704050d24180c060f050a0f030f0e0706180312082d06180c090f01030f1b120b06030f130212102702060715020304060f 57
    0x200040803159820b082ca0107002600741101001c014004481c2800e446458404140c40b052403800e440e90100141488020101c0002014107012246046006070114045000d6000d00c40b01074403e9560f945402c2e9800e60403680d66005401c5101815141c5501d042100e0f05806164880d1500200905180340380070750007070030101e01d000612461240c18000740302007032000141d02c00500080c1040e01d5561150064003d192188540c0340d40310203028294040c6016030018514010300702180c140d51080000404461118019214040351040c02c200d1201c2034144010000d94020f014100001c40c15501d210075825582280c032a89100030210000c041c07601d4008480c010070110680041181504041c0814402d1101504201544107840d0008110140c0c00082c1484650301400052228036105403103591280c040d001e4119042c2001c51a4007170034074901c403140940e8201e580030829940e0503001e104030741e03002e17900a40304025200d081c4184179115000650140344541e0000449011110080003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 621412877 1250 621411627 621411653
    0x90432100e04080f07021c08030a0516080106031104030606172109150d0e070513090201020a0b060316060c1709010804032d020c04060602240718080109 67
    0x1d40326a9900c14000400c140c00103549149014000b2a40d9807200742c00000c138214200b88174070700040340a02c490300400c0420405540a04540842403065440b07101d40659207a24000045000607001401001514481d070001d005005040042c5490b0a4580d1503160030f0301d070107800c06400450580290364114908100c020340b00700300031054040b804604440040d032031064171000c500c1070404411070003503805074004440000d05c2c0040108000c4804594407a2a9006840703418441d0041c0e2040c0322071440c00d8060b8003541641640582907070801c0741d0703c1000c01c40c4098840c0343c240c03045076015245000d07400c8252003d880d1944502140012510344207078150704080035004100001e004611043c1d8021010581050780760500502d141ca40c50b0040365612001010300d41000c42165903441002c1d00881c400807109020380d014040f032034a8101c10b03070340c403181100d107a906c50f100034414000001d001d41c0d15030f4021420745000c02c0d5020031090990200c01c51038200e02c40d0382c4d54401740c000c20440c0c13100d1080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 621414127 1250 621412877 621412889
    0x1f1e05070b0f0f04080a03021902100b090118020309010b0a0609151805010507020409050105010609090e030a0203040b030403230c0f07050102070501050d0f0c0c020a0e0c09043210 79
    0x150350718225103c100c515002400040500c2000b00300c1d4255280207405403104c251840030161041c1040c540001d644201d5049084104c0d4504007030200076082010290b03058810801507900f650880c0f07074481001b5072004042c2e80055580d0241030855680d640002401070045585001a09080c40c071805504415003c1c185d051040950041080d15010283c00080320f10900b0020b07100c484a0001c200a0110008010145c2d440c245c004100e50b41c100048009581d908074040000045100300503680303105100361080503902c20311080148046110007954424424600741c1c0d940c05602145655400d072002001c080f040020900e0b0000c1130041000d18134489440000307140140c60200080e450340c0300d6019980c100b2400044000206250ba0811100003014000c09c200c411106a030040141200402c108c1c4120042100005c410380c0148186004145803030302c6a203000d1080d03007004003d000301c9140e440742d5a05069012244020000c5100003010040320002e02e503e41051100d0410406070012 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 621415377 1250 621414127 621414151
    0x915070305040b06011d13020d0b190b09180123011d130e030301080c210c130609020d0c0f090303091502010b0a12170301051f1e05070b 60
    0x411060240310b50803000a00700207061302c8100006e045000320706030a1b01d8002511006403100c89500390300400034809019002c002000f60701c1300308908000350b0464412411002c074014441e019007000100340041000b401000e800b0200c18910610072401da10480020706000c1c0ae100701e0b00095082c45400c0344007440e04400f0340d26010814000359010b40c1a50303001d030018021a03100c0b140c4a82c80212a40b00090482e038680d070390740e03810503076902c2040300700c601680c0710701c5815032010400420300200c405640c1c0a0070311b0140b2101800704003c1000342502c80c840c4c40b1007001664a041d80b00500c4450403000d80420340f4036440e40e01400c403080e9180421308004031071030204007280e48801c403c004d9881c81c0321303440240301e04480200d014102070107420b07522205d01800051030600c50028203000c0c40c400d003000c011360f4240e911640700601092291030741000840d0020007a0440ca19501c15592500d414000002401820813040b240800e10000d8081007000882400b400b6454152946c40b0300d0090103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 621416627 1250 621415377 621415381
    0x2010f020f1207030f0f0b1906080a15050a08150603030c03070807060b10020a031107060e2101240537330e0a0b07080f030915070305 59
    0x1819074812106052541d103002c03000b0490b41446034000078010301e40c81d64188521101918004010100000c5403449081503080c0c1c1a10200c0224080007203a0081d101c13060544d0b280700004020b8580300260510b030308031810001c01c071079030342c2d40405001e4031008004004401c903000302d000c00c101340a4080d42c0b19034004d0005031541c2d030703002084401445d800740441c3d8461029290201c0035142d0020704591108007400e0021030942d00084891a085c0039540f00b1090b0150750304010788803552401940f0001e000c52030b4800c160b050404c00f82c1c50317000b09000e4000303d46001810702800c4489007904d00e46007415102d00b905480c60107890740c002074041141c0c080e861902e0300500521081c4403030b0380a20224048460750302008075800d0b8840041c10300204804001c40700a01e041d010b860101e02c400c40340750b10410700500c6548a00803a140c403142c003420782d44c55503052006501654024000864482c1e0003000184078054001000e9806241850010240000426100108208003c000904040c50300c41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 621417877 1250 621416627 621416647
    0x30f07090f0504090c03060c0f200d0509191403070803090622030c03150501080109050c06130f030c03030e0306071220030f010302120d12020309010905100203060102010f02 76
    0xd55400c5400c12a8001402c0005161642090619034405084146420301da0810781c3c9d0480030022924610395501d00c0c0900c018140d071b58010746584a10039080e8402c04840d680a802240100301102d8001d041410440000c600f90420b00030310f400c040c034100e00208085006007810403008000d428040302030350074450594086000c40c004d192440c61440d000984111110b800c85a400700610741100b0b504030030030384900749110142400203500000a16007000003550603010710840c9081540b11014081400e141d1080064541080a10302c85001000c8000160780c40000008001544203803c18140e451031404c00de4a48800300040320701039001001004480c0b0749c0402e421400110450303002540d08103107044981212045d0128009141c0000140070161b9644990340341228800c4504d440d0752140c0d080d00507219801d00d00da050108134140c0c450b4649045603009182c0c07040c401c00002605950350340381c06240000701c02811059a074000180b211650b42809072100c40100008154a0040906 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 621419127 1250 621417877 621417899
    0x80d0c032a0210030605090f01030503270a03050606041d07031e0f0602180f060a0818032a0d050a03090302100e160509090304120f1205030f0709 64
    0x12510920800100c04111095681c0d2110240581c0140c0884035912180001400606090003054800c00da4000010708000120b840305068ac2e610a010f1424400c802026030300000c981071015604c001321190700d4a240d2a403068900003103000e540240300d581020414030040301e17000841d03078404600400300400b500c0c01c00112a41102d51015904450307400f41000b1020800303c2c2c800040c029891307048003a042c410540c02408210a00d1002021b10820315010001055810b450040d0084014030143c1c0c019405514044d6001d0396a0304c040700c42d8400501d8040c05e603400545001240350310050760342c40032003030302516199002048000301034240c10341001400c580504108002050344554040d400c0600c00e0250100c4900c500d0814400a91080f603105d465032000004078075011a00e00f40010030346800e154050090100c41c001d10301e45410007082403c81000140140d07030718000ba03090440064840d4090060000d030030b5503059100c0c100980b485c0c207a041c01514603002c100c1e48000c14442c0640e00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 621420377 1250 621419127 621419147
    0x3110303041109280605130605010914040603060c0c0507080601060905120c100203090f0d02130e0a1b050f03030c1c0c05010f0204050901050108090316210207080d0c03 74
    0x840f0841016610098130100c01029040500c150f40c40000680c640140c00b03401180645a00f111248070f00318200d446e28007217411602c5501c1c0000c028100030003000c0c81c2c01e00041c05143e00034102203802503c98a40130141d83e00415040001401c3c46825003d0220070711071500900543c0001d4026545081300041020300c860082c9071042c1c075030440c11003188400300407414400308041c0550840742110440030f134482d041180c140e4000c085100403a5400d19100e07030007103080c80c0d00402c1a00d400b4054a200710042840c031031080514420082c05101095451190919211030704234803400c020b0400d82400000a00c982030070f0300070390090150910075440030418000405105000c503090030b10000d4101c0d82c0c05086c02c40580303e54a441900d40070310503150028002c4c0c880550701301e0601d0760303940011240040200c1700b00c66990410b0282e0582e40b01981d108410a90044c00010014a21884c20340000080500d04002607840a070341001f0100e81401040d40744000c6062605000f049901d007c1c0c000707400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 621421627 1250 621420377 621420379
    0x1050910060c0335070201050c1c0b0328061d0a021212042306270103060e0a1d0606010c0f0203030d0203160207080d120510090f0207031103030411 65
    0x240c1c0b080700b50640381c1c2d07500d02d10000540d103007006460a81900401340c140c200f6901c010040d400c1500241c020a01842222070061040b85850450548180a80d00906a080c080c1f81e050203120070305843c3d06040e580382c0105c61341d0714046111850300380c03500104031020a802080c100100b06250740d9814404201a1001501660000c803201008105641004129012841030b0400841d01094002400c220300f42d4812800030340100381d206260030040310303024400624004840b070a015003c9540c1c141034440f00c20b201030401007841c6458101c4110200012101101c40c1543e490003829812255040514034a040d100545281d080802c0020300044c25940041c03c90b0380240721070400c5440c104121083c030702072003000715141c0c1850756070422012403041421005101d8000c4c0441c0204001c600e92031244140c0d1908e140b039810000400014041c01041502c04229074007000420740e00c54090841d040e00c0985005a480b44d0910300500031008000d00380c40580c5c070a00811000a0207100c0303035000010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 621422877 1250 621421627 621421637
    0x41109040e0c0a18050a051302010c03031107060e01051e010b0a09120803070f020f0312060d060c02071a03010503070b0309030706020a020a1101031415030f03040e01050910060c03 79
    0x3030745002841c102d40c04001075000010340c84009104401d004490501c51103686090003a500c800707a565003034800070b403040003021541328401340066014602600517180301e41404103a0895003c0b111080b504402025911152604001c0b880340c0000c1c861241d2000504c1d4000000c00c006103414509110305000300c184d07444000a04e10040c50041e030491008003100401c5098144040c42c01411036001901c941d804200c0a1141400c43c50010811005441e00301d0015810f00740e0b403c00d2501000300140045400400d941c440c0e001213070850160301007920840c0c00903c959807400860302c40803020078040100004080c40140a1540c4c00b0a0000440d50b180b4949510303038454141c107609611851400030100d5100081000c541c41d00401e210700410701849000d41492242e0300150306440701410400103070081c02c030014000318286140d4600102003c0c0442d030351a030594000d1407a5602c9074105238003606401004000d6031403c9100d2951001c203400340d4203c00c514000c0003405025000b540203007800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 621424127 1250 621422877 621422891
    0x2070501050d02132918130e03030f10150c06110906120f06010c120c1b090509100905030f070807080f0a180f0b030c040b0a050c0c04110904 62
    0x2d00c6030b4064543c180c4402c0c68014405640724501d011500701d148481e00d1540d403444d10705000c421032030192040c100181003155100a500c00030002c00030910806098090f645650442195001300050352042d0303280074040d00e141c10300c26680b4281c00c04552084541d6803000c1064500103600000c008a03280d40540b0102d14410b40301d81c0502705004881d9515040040418400c0e42e4000c2d605956000d1994144e104009403519001181c070a502c408019000340c5d420408181c403144510800766031180200c0340342e002c14101c0310207040c0c0030029903c40c060f031170740764010301290500610140000c244400800c00c0706a209075100c0340c0328060704802801d0f102c0003044560505c04a4022a040309a211407440d40d5032002c441c5800c03441e0000b6084000013080100104040c089480078030090310220184240d000b450305002102d15800140307482e002d08024000050703d8011500070b4900d8140c50344500781c89000e12000700d031500c112080c01d14031580c00e20100c040316815a10842d41200e4045d100446c0724 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 621425377 1250 621424127 621424147
    0x1b03030a11030c060c130801021201050607150e03120f1003240c0507200603280203010f0e0702010c080a0209060c0a120e09160f09080106030c0e0a0c0207050105 71
    0x5000b2112011628011001041a100241e900138814070045200306d03004180c441290908038010001c2030340c075145040c8014440703031400c60040e211880c840c120018880060800000503034042184202d401e42c80070400d900090b41000c401d170b0340034801c1c0074032908a03c0e00f00402a141c850030b00c40900b1507412400d86400c2c040c00f002c201c24202d00d400f030307080c4804003136a04014610340c4039440560301c0f03190400790030301d5903461000c0300348000d1001080c02d811912805206850070740c000340300b000520380d880712042d5280c00c07a001640c0200340a03400a00c7d0246090b0030000c1440f00246100d003103902d0019903101c40c0d6002902c068000140400058443d28020080b03078041c0f00343c03d0412158420140c01c5000c000078420120740740d620654413a1a80544c140034000c40c25400d80300016802c4004140c9000d5030b01c550301382c110360509460109141030755005602d084400f146c1050714000c8000d082400020f4042c0850f6422040c00c9204004518500c00002d4503090103024480c10000001103402c11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 621426627 1250 621425377 621425383
    0x40507090803030f04031d030d14131202031c0219030c02040e0f0d03020a1409150a1101050f0424240906060207030507181112091b03030a11 62
    0xa481c101d0102e0360340713050440209608241c00c9508800040c031400c4418880f0070410326602c0b9a04015000f4a201c10260006840b4944400b92100040409001c0c1e800340a10103100b80c4002d1050032421498114280185030030042c03086540441e804480c2c8156403015400142844480c2c000030100704800c060b890b040b9018001c0e4034019610031b04100c0f80352484000030842c40b10140c120340484481e602040d00c190103900840e800d18001c6103401c0851808030b0800c2c4020719183c00010f0244410303140707404042c00e05400002003800020704000410f10075100034414580c00c004012002d0345246070555030b50051460600002080100d100b8002c8010032807038009254400c2c142801031880c1e10801c4c10000e41141ca417140c08660350070410000b80e070f1400851031009494109019040340c03402d01d0302c104013200c603140030010101c0c0d45111106024a08001a00d01d2402201c2c401c11281000f04015180c0310a420520031407110f0076041001c941d0b000412110080403900384000c20841040c01c0d141 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 621427877 1250 621426627 621426629
    0x4180209090c0306041410060815220b0a050d030509010215070c030206060a150f05040506072306071b11030714031002040501051c23160311030604050709 68
    0x1410480325824002c5842c0c072140510300c5810191420452018010f10241c08103070190740071015080b12150a02c103940c82013101c20f83c004142c054030042600f0200101e1402c054006088006034002800050000454000c243d0b1202c81255800d503040c0c01c1c40d0001c0c0c4810002c120060511400292030301c1c0c2a4000e0114503030f900c09a41c01118245006003000d020b66038628000c40042c0103400008000c0c2c5440d19080060b104001003040301002c40c200300790741c0701170075846000500000f84800299640c4250060526610030101e558200501a14911403040040b13500c01403070b0014020003060036809011080070740358148500139910110704081c0d03d400c04009005806005000e004941031a0701201d90041003000e40407a880d003001000c0d04000c80c02a40100c0c1c0c00200e0030441303a081040c4514005461078127202001030f1071800314008a170501c0c200d000c0c42c401910b0350f0040000c00c81e40040380c0007002e1a00c0c1000d01000b684104080b491b0b10004141a20407035440010a20703142c03007070220340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 621429127 1250 621427877 621427879
    0x180e102304091a01030b0907050105030f040303150308030103050106170109020102100f090501060e01210506061306080d0c030e15160602040f12021011061b09100306080606040504020604180209 85
    0x43d20303e5031281013030342c8200c40c05c55441d100b5200305d040000d100d502c1003040360712480244500c0c40c1031340ca0303654081f4007402000a030003103413041c072500210214640d140114000c510030000041c501d481d088003110511245414002164500310b24080540d030003003030b56000f030072480b000001c3c10040041114010440c0c0c80001e49150320340080440d104a003000300c036050f2598503412220b00c0c44811905030080c0007071440241190010004140a0705110446d412030143c24000445e4068640511070728014518201000040240d5500424150080070780700d03510800341d51114200e00100e0900c0c10ba4840c1d030340e0b45000604514083c40504c12650b0541e07003d0401240302e04119551a4800d8400c03003541c03801648604a107220110581d401101d40360799100c41c80005e41000d40e03074103a03140c400020400c44420100800c00c61546140c2e01c0c648900c144013026240045c0c001d042008451500c4801001140294501024000035964200a0780e08451117141d030155a200d8200c01070011303000d070507202d07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 621430377 1250 621429127 621429173
    0x31e0709090b040c0b13030b0712092406080309061b07030b0f060a05011706130e1e210c0f01110903010506030d0519180e10230409 58
    0x110800444540b4103001e140520000c044039a00d41182540c00d00c1282d01501d100c142200f010400a41101940d6500c250076041c07455503515058011402d495960300219004c0f4000c4c1070a80b034004100042c8030a4828019040040c42e090003020341d44e91041c00c219600c115030110b0007040108070100c03001c5803404004160b4904560724646020011010342c0c505803007143c2000010041c5c10000002c80031034505a41d068544100b181030b0088000020b481e07a40c008007958820307071000a090007000000f14080b4001e1401212901203a46514180c0000e203080d90000c102404099101c1c83e5003c41400842c401940d540180300ca40926100300b6a0302c0c032986500b0000460f8082050902500b1444005d40080c802d654415040544600c0001d035003c0204405006401d01c14031811500304e200000c0341400d00081203100503049040c17205178003c042c079440700810060643d002c101c3c484010500340d50400d0700401c24440f5840c074100010507083c01180d0b141d504000744045da070303200c9110340c000700ca038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 621431627 1250 621430377 621430391
    0x11030408070602010b090c0c0607030b0409050d0e10020a02360916050d0c0b09060f040315060e0c04091a0d050717030a05071106070203060901020c0c010e031e0709 72
    0x80680030741180d881c801e20034500e020019107007c0781d01d400c0b18009624600030b8034050380c0e40d0340c0503401860700340c11041e0025900d814800005404001c0101c0c0140e0545134140140d800800700880e2111981000c81190004000400180ca8100c40c102c0000030481c000d1084019410b5059000000e1840c141a0042d05100b4443d07802d2000c0b5400000d80d00c10003000048545a9082c0b15546090780d2004050700742c040010009546070b80301400070043c0c000c02c51450481034145511468005070410389100c030740d4951b1200c240740e661056000401060b8010300051411041000040c00f076885008005500c418408811661002219051410081c9180b010090741c1c10141da503030002d809900f2214a0710035100c0030000001080d1400341002c0e548183c5000070700e035200744402c0d59180c4010f4002d801401103500507901030144500c0f13051288001615204c100718490f1501d90700c150300714140304803100d01503c80c1e2400304982c1140c40e1400807450301481801b2209180015035841400e03e10325001d9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 621432877 1250 621431627 621431639
    0x702150721020d0305160f020c12030d05010909020120010b1509090907050a050607020a092909010e1311060d020c010b0f0604050d0318120210021c1103040807 70
    0x40356007910300a50b0849192410100090f0100c51040e22504030303101c1c1440130301c90002e00c03485856501409900c141c2d00e00714060804604034010490700820203420100d8503031030304e12141c072480d0b00500480c0014005940745800107418011034031071004508000c441d207156281400d40148100003409000d0400c1d41103510741050590708601c1d44036104007100d5021030925500001c00000342c800c02402d40407618039081c1000681e0380420300498105207411000a840c1070390b440703680d404200421a014a4121440054041514100d2160301c2800c0340381c010700c400180110581e80c001e000b41d41d00742c456000c0341010700c110703045042401c0d80044005588501060141c0103424400c28620007030212081c04420801511b0000d08500e40104060200f00321a28010443c041518041c1c244260760340b40c99000e01503013400b01d800c00c821086501c20120214206044c151a07085082c7c0302034a4103c60300340c2c132000d05200c0030300e40f00204510340311620342001c1c00744102ca00810500040f04d400b075980d01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 621434127 1250 621432877 621432923
    0xc0703090305060c0a1205070807050d090b0c03090f150406052502030c3f0d090f1101050306090f090304090e0c04060b31050301020a0c020301050c090607021507 71
    0x1040d8280011b0000b00c6144010555019240c010801500c03031301c1656442d1002200d4540005506525180e140d00104000c02c0400307461602032640310358800d95a141c480441c40c50042d1180c0c50003034650103e03110418644020141c20b420a0f031106d0041008d44400c0c4030103c40c416402c1d5103410030104800b0070f00145030004002e08503541c0f810b0030340300b0146450001c0b0031018007043c01000c00c0c20842d41c0000380500a0165030002c400c403410310130308110f00611504d04030351400034111001411401142c0601c2611b0040d04802c01d024607102e4990703e0280081400c2200c0a010b0105003111400031912000302032099501900c42a00c0410945d190707010659610740c441f5807010701607841c3c0700c0c02041c141d206004a0b20300b99035050b032900300074201c4803407450810040c040c015106440c50700042802e41e0280028200b2890300d68440210749590f004150843d1030140c10310707261480400005183d03031600e0003914100c5030101c82100c170107140b2140a002e548140c1d14010300c00800c0c240c4001e242c0780c90b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 621435377 1250 621434127 621434137
    0x9140d090302040510060c0605041a1501031b1e021906050109050601050f071515030b1e060f011101021b030d050609040804030615080706120b03150c0703090305060c 73
    0x2103d0522050f200c0c100030364071040c4203005200c0050b0041c1011350114103141c0159030420f10442001e40880c42d08560078496580a070f45082c103001c4580c0121945690502464030b50700c0c05002020006034820b4006032292a41742056040c024031801d000e00c41ca40240031b504c03207003814104100f00340300d0703189440002840300740144074881d85094081440c43d44a08141c0d00c00d000c03440015440c0c44a140c50303004100c0900e00b100b0f00c00607295910034289400d0000120f000718416103c0032050300340864007802d00030805962401a01c914030401c0640e43c1e80003502c403032184080c20504105418074528038060707c82c511600742c8059120741402c805240c000010107040b00441010403180e181c0c9003c110070100282c4000c1c00ca885c0c00e100910104007180d010080c401d03a24442c1ca842103595024035810b18006a1103980420b44420444822160501414221880441c058a55480c034410302074104103015010242c1c915011800000f054050003010019507003010451b416403808511407600740c0e000e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 621436627 1250 621435377 621435379
    0x501050a02130b04030b130602040305070e07120c14180a0f060f05030417030c070203060c090103140103050331080d0e04090506160e0603130507050a03120309140d090302 75
    0x2e04280010144601c000b601d0540303500080095954565101e1100b00200180c01521404d034200800800504c003002548001c2c9002c080b00c2c082843d00490143c5041c0d52000705880c0242001d18540b603641c0c2c05104040103c03d10b1000c00d031184410440c0b0300711003036282c4d00740e0f4100d006044042880030f8507000410441b074540d520b1556000703403010100c84500040e40c006107446030559500316205400b1001d1507100c0b0200320b0741070403c43d031a000207191040070740310b0716010040050005042d59050040c4030200062071000111549103540c4e039541ea20400c000100c4690b400302e172002c504040c00c0064400d42440203c0002c105460791162511204002c2007100440c5400b610502503040a00908105d80e0f0420007078202139890034144201303802d24006d02c204001d2811840c54560380d42d80c019500407002e400c0b0101030072000d4a0410301d07015090b048248504c400d03031001c0001035211041d40c1e03a04c0d4503d02c0e010412080505c0d05840c0e202c0005d18102c1240912400c00000540c400029800c41380 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 621437877 1250 621436627 621436657
    0x10603020d150e16020d0507061805010c09150507020102191a0103030f080a0e100c051b010902030c120a061e020c01020c0709020a050f090d02040212091006060c1401090501050a02 79
    0x8040c4d01c180c3c0e5a240701c042003070101c1d41c14410700c07000c16400e0b40160010903e2000500d0040015561942151841c2e42180040b864100301485800d015085d105442d860a0a00d149860903c2d00003039912060b6003129202c4007180840750303080001982440400c100c80344e56105895850b45006051815181c0c590030004520310005131142c00345000c2c0042d401d0b1071002901c1d03000d020700b039000094a0080039540a00008000311084104a0800180e104583ea0000200286c0501c1010f08101d41c0d41a00c44c0b0030100000c001851001c0810025011a0710200000d16507a00340407002c1556400003030035501902c049944240316070107400500300590b00d58252880e482d25281130300c0c201e02510803440c002800c00d0081d4044041040002c01c12504010080b4409104070303400102680c0c4040c1010200c00203180c1442a044001c0010341c0c0ba1406440090054506041c0010b01584c8410405030010000e50b42003480f0900a50005c01d40030b0300540280300e41c0c034000ca1204040d5000d2003148030560 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 621439127 1250 621437877 621437911
    0x130c0f0e0a0e0612070b130302030f0309011e031112070201050f0f0c0c10110a08010e04050a0807030302090a0e090706022103190216020411030f010603020d150e 71
    0x45081821142074a440303101c8520300343c9504060105000c0d03201d02840c8035224003000454400041400307082582810152900f00c10b0941c0305160800600c01d814429075031090010001d240c0c2c0084500320500700c00f00903080007241c0100304030042d106440c80000100d100007000c80381c0031540d0325528815900b58000340407075126402982840d4004840c0c1d010301d101e011001c680c618213104001d1400c038500c1c02c02c42d4030040a00703001d542101d191703180c0031002b908001450030700550003045180c0103004020010140303190a0b100c1c0707600c0f000b030030740c000f040d4440000c3c1c64001c0501a6040e15840d44014114034242d070785420745414411000d480342e6a0b02e103d805000240c003840068640100281c8000302d002d140d01007405020b854201070510405560a201c1c250104100c0d8030241ca0003112140030406040018010b01084424145003040d5024040013040f80340c5940048041c1152110728006a6445034105000c005081d4902208a03001e901e010000e148491699554050246086012105 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 621440377 1250 621439127 621439129
    0x1c1e050a020d060e0f06120703050709050f06010c03210212040c03200102190503120403080124080601300f0e0106030f03050903030403170315030d021b130c0f0e 71
    0x2004980800b8405c4a120000d11241841060000300d11041001ca6140d640c41c2c0c0d8a00e820134072203810488845945030b04012041c4220000f454122000b800e00903c050841d4900400c1c0c2600e06801c0014442008a14203182c41c0541c1100c10b000c00401d0710b0010340c1480c1c94113089036a80b0340310540b041c009918038204050074018581641c0d4a050300100a811500402044c1002e00d0b100203a41c0340c0400d02102054210012800744114481e5840700e4843d81804404c18003038102c40715082001040d10003625050381c1006105802c540c0c00d0a00c21045485020103030710f550302018002c00f1010b04150301c07105200464012100100700d01c00240071500c0389004190880d225440064414034010301607002181c0140e004005900e00507080e81e10709a100c6d11040318050595860100e0030000004101d00060b82d00404280180114042c0558201915009580c0c00a10805000340301c81c19261001a5032204001616420540f030700b07005c0503020070000b401c0d08800101a50101c3c50f81e40d507401c51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 621441627 1250 621440377 621440399
    0x905010209030106050f13090f080a0908060906010b030109050613180303050c1608180409210c05070501050a1e0302130801050c030c07050109140709111c1e050a020d06 74
    0x100c0c0901900003840071807c240c15402414410704142c80c2030700c0100d161fa000c180984010b050b038034595111045110f10b0030b400503250190081c000302c52a0840d2006004007062a021281100c0c2d118102061580300c100018800c5000401d4405456140c0441015078407144a05190068080e403010807056071000c0d6109400e00c078840040d07079a01080ca4219000a07110400781c90112566502151701c0018807011900b140d00300030342507403554500d000d00c030400180404007070602040c0c2e19190842c9500b55540640d107110754000c2e2414840c010500c01c2c0c155100b010460481c440744030102050310782e15030001d0000d50240368021801e407245030020442c2c040502529018580108240745180d640810b03440c943d4200c507004494654941c4144000315050b02e02d404030183c80c040180100c10b10300031003d070464424400c0f1440c940d01c28400c1c9141c80070f54066414107150600401308140044030503007198480a0a11171642a1508060200280003070b40a450304072084070040001585411780591 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 621442877 1250 621441627 621441649
    0x219030f030e22051806160807140705061605120a0b0d0b0a060603060b0f0403120306032010021501170703170310050604050f010e060d0207140105070e030604170d090501020903010605 81
    0xa0581381f40e011880c0880e100c2d88809921803500c1c50000003090401e800481c05610148041d00d00d944040c0522241d33031800e81131b0000000c1030b4189189008007400c2441c0308480000c0030490f000d5541d500740740c0c03142c0354003008804956100414500c50b24081100200a10f014011000000d20308080401e038001c401c41150f91549124a81e01d003400e00c0c41c0e5a4000001c1c0891900d000c060322028000009054403210610032100d000c0f00444802d0954184004010a0440c110866001c080c5860700100c01d201d040d415241d81d400810042007103103aa1601e002c90b05e80c402400c80300e45910300301e82c480404010b180541078140c2d148501560b0741c400c002aa006e02d020b140e034040e2006800c0c2c405036010300e804a0340e080300944294100726160703e04c2c0080f17801c00341060300d0b1421445503d400180c420f01c00c1c0c9a0007800e504005494090801c00300e540c460740100004c0c0500c543d51107191081500748282d5a4199400e90203200215030380ca000d501035004942e14074041e41c00c02d2404034a030b10304852048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 621444127 1250 621442877 621442891
    0xa0606030b070f0c0b0a0b06042d140909010e0708060f093c07060201060501030e150711010e011a18060609040c050d02160219030f030e22051806 64
    0x101410a00d5141c0440e8070700c5c040c251030b132210358404409426440d8400a88020031080392603480a05e9540c12024000c0d86030708944c4103010300034606000d08441c04070301c034180b200d05139003030101580c80c1d264907801019030020f00589407146000010f0b004030002402441004885083c410315200c01c1c07501c5a40b2095045214200e0040401c0038851400c181c000258000d81000a54003400f103040341d8504041c03c0383c01c20300c010703510342d44140410b58142c01920498002d84005004609055004942e9101c029040c030080025512961a926800350005802811000d0003007103403482e22084132500091440f00f2500900208000d04030480300784018520900020740360a10f03080c00c00c1c3c104001002070008d48018403600340040b00c44505076202070700c08540007000c0c0214241c01e50041003001400441034441003203114500380700184140c44c00c0300c0b0b00e5a250074860708070380060b000150980380c0c5081c60101c04610402822005940788c024502034520351140d022024180e150301a00d69404031801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 621445377 1250 621444127 621444137
    0xe0402010206070804030e1e1513060c080d0e0109110603040c06050a05271503040816110405040f0c142103250c05010806130506120a0606030b070f 65
    0x20f4031150180c410294407910a20382201c0603014400010341086407064114001052040d806409040500780060031081020a00307092481880849091440c20f0007048100488080403c00300070000055600c042c00d102e01c244628861002c1c030700e0003006004020b913039203006244510700d81c1c14408103c0c0c1c003844d000340007250450300300300c2d041d95250702440b22842080010054150700c10f1203c1c06400c2d1169903400c070b41d040d2125000410a410400b810140c0b90b002081050100160b00070045407121107030941c04042290b410300340403120918007584650000d042000300400c1080603d0396010316845800406d0800380c4440f111112010b142501603003084101034298202480050350302d0040b0301c41011a85041000f109100700d440200b003c241c0180650300540040090405003000500b07003e2804c00c41c1c2d4500070300001c40c00101d0b031003c41c104030fa80e140451040e4507034030506003440d050082250302a0303455280000c0180741c1c0b48002e54003004203d01042c0981e00c581043c0d80143e02594034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 621446627 1250 621445377 621445381
    0xa0e030f1f0e0c0d050f030a0207030507150f1101021204080d060b0f040603020d1d031e13030f0302011b0c26030f091f0507030b3c0607060203100e0402010206 70
    0x148000309800c004d080c0c400303100d01c50a03248400070400050042e9070455018044192552410300d1400035190090315940d8144030580b10602c0d0302c8400c5180c09081c507d48418040d00560b8998024803407650b0054482406030108000e00403504000d00300038007000c1003000f94941d0f40c0710024440c0151843c0c10001d150801c010401140700703802424400412203400242a001c01c002e01d081a601340340135036443d42000ca2100c800710802d4540c40710b00c0c42c458174124503000741d024803c09032b01d000d40401460303d40c0f00b00020051600c00d5104140d1071100c940000c00807941605c01904403041c80401b1548074a200c6400304404444015604140c06180291800c50f102c043c00700e8040c12005041c59020b104464003025480302c410070070b0303480d0a001c480018160922050040940e0054030a140c081c10800340f1b61906402c0c994001150b80340742c8030458002e9403002c200400080340e0300d61003551003600401d0fa0b0302484820360046010b549501681042e40b50b843d03c01f6075046004860181c0035800000c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 621447877 1250 621446627 621446629
    0x110a0b0a0f0b0d03081b0a09051c0b010f180e030702061c0c031505010e090a1e110405030114011d0403030605030d02070806070e0d080a0e030f1f0e0c 66
    0x80354500510151010440780290303004580d81c411022004e4000030a180144a0014400034145c0400902000b00760326045000720302611030381c1c0301d104444c060609885808805107000844840d41c3c0e500c201240d0003541e403080e03100c80303034101070050140741060888a804200414407800740103103071181c027950420449400f0045190072950b0390010390b2450100d8083c403050036100702104856170351000504482116582031402d100c60b00001d0500282800b11010b640d69819000e901a100c4d02d00070414400030740d0b01c010140403285e130901500c0c0c10100c506911408003070182c01503400c01d038020020100d0565140902010a21800c0701d1401c1c481070780d150a400119205500034042d050118186584801091800d01985141c10041c0c102034424041c00d0010700c852500401a0f2400240100000c0005048101c0841d00208a0a000548040001e000d80f5555110540041c25642040301c881c5105480f43d030700304c0e060b4004540311400b0344244001841000c541203184402044802c0d0964 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 621449127 1250 621447877 621447881
    0x90201021e100b01020708070303170f06010e090a0b0d0503071407060c080f04181406041a0603040519120e0316030204150e011d09011a1c050d030c110a0b0a 69
    0xe600f480c11805940c0b000300e485802000002c0095110b55913041114528200b1003190000103411a0101030000044c031459070b03800034201e4103000040720609120780300e4207000001031100405c1c058005c14000d00f01418404040050540c140c041c06902000c96002c01840391a06c83e10300604010461104079000401d640c0da0240130f4401e000c03400140390035154004ca01c80003076400584512280ca40c0d000620803000010456008070f8166000d000440c1140300c0d0080d4154480c0d00d290294030044001002d000040104091401d180341c01c90441e8240c030f040000341c0307600003900ca80c08150000f00d241054100080d03039102541c90192488611819540bc101c040e180c5500386d04c110740e00d691408500310390b0034004075000306400345035412070800300741d0a40c1d54014010078150302640340204100307001102601c2404100000c0311030603c140094084048541c0181c03001030712510548181d0b02035143c150b80000003141c0c01f51a24403401c0f11103043ca6545a00c0040001c0c0201c0200303001c181682c03699 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 621450377 1250 621449127 621449141
    0x60f0b041a0405010c140709020f031f080c0f0d120315060801060801171c0207081005040b0408071e05010209090906091509030403051906050c0708070f02060d0f090201021e10 77
    0x101040c1d9074103580e60fa24030301c140c2cac024080c00341d480c0c8400014003902c481020465108079010301d44041c0c41c81e140c50501c1e41c591094184c90b50245a450103240415a01e0141d0740d041c4952100720a17102d042207540090040070a07107101c0546003a00c90000c00c200c0d02610005040b41c146556000c0c0303913820a120070551a91204001c0c0b554842c00c4020178801c0d031420010290455135030f00602c0a9868403181902d000c4050031040c000914242c00e00001c50388010240b80c0c0150809135450740c0349818500242e1000080c0c941c110741066801921080000c190000c001011046440402036150442d41c1c540300c58041d5030b107004a0303010600c003180c1043c2285425070306c1034001c020b0300d00700b0350b0765182c1500b03015907403240c2d4500c200140203050412825104140d0405c0315203001a080c5080f5a444c40260b110343e54001e011007a560042c0e504550341c2070b0488040e041264030600c002c01c0b031103020002034841910124054000c0449041d080100724071461860026140204404548100140024161 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 621451627 1250 621450377 621450413
    0x605030f073003082703073302040806010906051e04060b040b0c0709020708250c0801020c060702031602150c010e0601090e070b040b030a060f0b041a0405010c 70
    0x82d903010004040260502c400060081e12032404a1a000b404445034929031448000c0e011207484284056910020544480b154424078100140c044401030303480403584c803058080100c044031302c0f0003c041d1441d006041240c0c946d5003142c4c2a662202ca43c1000c1d00d440b40250750b0040d400d50a52004204205040102c1000290000079042d454003103800243e406908020348110000a074510071803001c10881004044a10f811404c185e1141d66114691240203010700c1014400b0903404050030002600786082540100ca003001c0740c0c0d0310720a0794003039000f805c540400d03406080005100d80c2d00110484d141c1c241034041c03d4403061a5a0301308501d1200b81100f110420b031003400b24544880c001d119042c019101c02c401041c3ca9031402d500c21068030203490740b4007081d40149a0400c0000580d00c00d803000d4442150465031281c0d11640d019005151f142d210507460b40001c0400105610000f0060080d1512154121b100480408602107148228410180060140501d84000c50000d900803442164 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 621452877 1250 621451627 621451679
    0x1a0d060905030a0e011106010501170a1119080618060402070809040f140c0a1e0c05010603030503070207051207052b0309051c11091b0f04090605030f07 67
    0x4001c1d2a1180341d504109248400f290181c42a04030560300b0240441c4c410134502c0c000c1031343e50f0401000a0044110307646607151911090049280043c003900b2454051f8800f00c0107603164122002c1c1004681c2c00702200101142440d00031504a042c04100c501d1000c560900fa0351442c0c403103005003c000d41c4140015594404e042c080c070760003982d50380944848008401404501e20801c0042c211540740080e16801540300108451910503400203e0401d0ba180f404050b010302c01c0c09000d0a80d421001d4010050155103803080120400d03402c8405940614005d038220307510b10f511b0f84107210501511018140303030341e03000b030408100d5458502c01440340050221603606446009005614440748050300440100e48400014003845c00d2101281d480744a1202607015001030342c0d00c408541c0d0100c1e00f000350181e07048030b0015801d14180518443c800c50500c0302c0e650780304445194804103030068024003208070b007405000915887c00141080d0040d0703111000e000315924200c1c0c40380c40000e05414203501e8076 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 621454127 1250 621452877 621452891
    0x120d0e150c2d0309010605100f18031a04030f03020a020a06020f0405061902010c0302091309031b030801050a060509060f1809090a1103070f140a0f060c0302010c031a0d06 75
    0x11550803109206404605409440c0d08104d1401829500345810041c011404c1c041c034000c000d44d01c4004600350340c040b41414080748640716042d50306c0b900e4940019120380c2da140c81501c1c1d0700d0b140320580b41c0316238000c1c2e444085038030481000f101a4420782c5601801a44040c400c02c02241c250390003407a1800008818600d49659100400c0d06900103080040181c200c0d00d11141d0115020700640790540a00d15003103142403410303c001071305102d201d81d079104050340d2900c0d4901010702a1003842c03644030071040f868040c19842c3c500101103d00900845008040300440015118044e03410758100c0c602c0244103d0030841042001c420342c7c0c10030351412403046800045208161203100307089000b4100480a0140302c071040c140248291518150940281d003c0c0781c003049a40c00c14880c020684115042145c1038240c0b200000d00c28005540004c051104c141c003001992642010341200c009100ea002031000e04120441501100e4125100b140d035000c105451522600d4480c4100d00c04503c1144006600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 621455377 1250 621454127 621454177
    0x703061203080c09090c120615250b090328020703170403080a11190809040c02030d0501090501150c1703040302100603060c090e010308090904030908120d0e150c 71
    0x1245d081e40d180762160000110880e440104410725584800156031400020b21007001a24481c4100380e40031040720900c410b003c00c20039540c964040030347d03000079607920355082c080201503d075803001000748141ca07002200031140401501407118002c55030380203484100d246803115446c42d040c442200c000b04200b04030110000c2e800c44040c1180c2c10442c0d565241e00281d8428403071500b40160b00e0007140340b2210903001300043d1038a00300d448101050314081140d010106069184d4081e6040340302d00941401c001040344081030788003e040754500c0c41c0b038800283c0c4001c42a1740d281410300c0d028000403054860107115240040c001e50308a8401e20403680202821180c4404491302034204840711030b00c5848298123190b10401d09006840c0c0800e081c1015491507840d07140740e2040e1514280a5411000082d080c1800b5024050081c00d40e40180e40b051000d00d0903103c3d42d58880020404841c0c603060100c018a04002404840d01e80c00d0030704403040341c0300c0881c0c06416800c070205250600ca4091031108407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 621456627 1250 621455377 621455389
    0x307030f0c080d05151f03020901030609090b0403090e1311060409051e091501090b0d08030711060c2106060c010f020d0e010e0d270e0f0703061203080c09 68
    0x210b50000394002424141041400c00031400c914000c1c2c8101c0e01941d820301d03a5011b50202c802c03800707201d00b001a500c0041e10300603805454154000100d00703141c02002401d20445514092080b44241e0750f240881e070b203a90b2a69030140d000e84104810880c0003880304c000840c0090300c94405400105035030700301907495208005584084484410b469000c0b020701940d15005d5640c1c940008400000d80400d8480d5850131a0080c0d051140d51000b0392501e4840c803490319103a002c104515013001006a6a240001001c0d208254a0200003c00e104840000d80007000c00d5080d03c50300c000c0e00751141c0380c0002e1209051890340e00989500d03408034042181a1020a00744a400d244600000c4090384441d41950715404440c042e4014000e240d042c511000c1907540e01280d5084209050700f070034005012603d80103031081c26003040804403800030031404075620450041080c824100041003c0d0310b42d4030400100e06a4030240718450582d01807044000000380074603c100d034017031502c80c002420101d1490010364 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 621457877 1250 621456627 621456637
    0x60905090d031505220603021906171e0403031e15080703081603020304030c060302030f090106050f013504120809030304030c031701060315090e0307030f0c08 70
    0x85a540034002000e5902d4141c0a4070481c80181540b4240161505000c240c0c0302d2035083d0921400703400d62030101c09148080d480072015540107804103c8d003180d03202408002144a02821021800d0a05a510107a1060a00c91b1082500007940c0c000380c400014620b5000f000500210181602c801540d04125100c0140d030311002c8506402064141500c401e00300c0d107160329000106a60880041800855895411900480c0c12004c1e070650070091420100d0460003107400060038050000400607070140d168000e1401150b620b5081c851645035260100e00303c40c484c2c418242c0103107007000940b42c84e40c010500342d143c0031890f0a500300c40400f403a1000416421400d03812a40045100611042c04440c950f02102c140a03403c0860680c144170307029581e6400000c0c00141005158204503040500c00c013001844041880d01026035075856150180c0940314a0700d00001e0b840000c500002c0e100d8240c003c0300c00700c01104d00a1864038015880032582002030001c107005000c9002503440c00283c070f02c0001c01c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 621459127 1250 621457877 621457891
    0x2090c0406030f0e3301230f010905091b07051e0a0b13060207060e060405010c051813020c0f0102130e270f1e01050601080c180103060905 61
    0x25940d941410000303011200503034902d2408034a002a0740b95424400a03241c140c101c420304d94010b45a0504c2495000e1080501081040c0745000d400041c84440d507401d101c0400100c240c401c0508004107040c80b00700da01880502d0b0001d0a0f800b820466803c6c40c41e01240c0118021384050704081c0c10600031103181d402288200c0e603039441034041400d00c0c11a40c00d10369079068901d002e003502c810356413a54490440c001c1d0a034000700c45040813440800015504036031b807042c0d02c80310901c0841c105141c2c1c1d43d207401c4101d030244e4030741d405c042d020046580b250049840d108a010280316403280c200c1d0a00052076800c0d000c000c440d69003000481030505041103107d40d003180100000da51540c620403522280105940128600340051b0144040750142c0300742c605001070f0065035545000b100340c106924008100503801e90600a040b4200004810000e8408003020880c000303200c16140d6100458410710100ca2019410900780320b03132440d00a441210b100514414036000c40c4448e00d45504d002283c00c269080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 621460377 1250 621459127 621459151
    0xf09030d1a031002040b0307030b063601050f120c0408120d0e0c100e0f0405130b10050904020607050a0c060503041b180c090b04080717190b0601020a0209 68
    0x115001e00d010801d030b01d445090601c3c207505052801442c0692408042d10103418551650381140d101c5d01c4170310980305548403014080d030800803003091401c034443c0c08100d034a587c10000141001c2c0d0354010741c00c0fa40c0b9070005001e82441c1500001c18a05004005000071b03200050800001411400400924141080300060f4603960246044100c0c00c5800c408607004481e0401d0100c11804d0381e400100e07075503400c0e00b401c00740030a515820005411043e16444241c0c014504802e00c800740340802e2102150130b214940450307043e200c0180c120400c09130b5104141e840841c4000050050900700d0240c000702e032050381140d01c408074940e9016400c00c1c55410a0f40020070102c100014450b1030f040649294004034900340c50b50341040003201c0c4480b030200f4145801c40e29041a8200701e0320415007140141884a5465115510b504400c1c0d107540240c401d500610900c820103815000d400301c1d80d00081100c1c1c085e805002800c03980c0301c0000350002040207055004c1c1c9040400542c430f9039030034a4440c60300d400d41 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 621461627 1250 621460377 621460421
    0xf032b08070201062738060c190510020c030a030f020309101a040504050a032c040c03020405040516030513020a05090901091403040801060506070206030f09030d 71
    0x40146040030040160007160f0401008005045101c092808120760b60721181200f01c400100300b0f0080c2041c42d04004044030035075518800740440c51180100f80e0400c4a41d00751038401c5004212403800b4085a80307925801401c1d2070003191402680c210389451280069580c1104020a00c0d0226005206c3e200c505070000910100d406900d441080c0326200c407031104604508284d202c0340d030f031250715010200442d90b840511b0a04804403400d202c840c5040180184624945460915201c51070700e2011808138504030700900d0184103603c0070324a81366000845284c8507000e0307002c00001c0e00132070020304245a42000040b5480e156030089503c903048482d070b050301c48021144001c08030b03040100151050700040c2c1c40d00700141d85503c100e408580301142d1180c030350303221221340340d00400c10500014840d10008000046a00020024008444001d4020050380d6030740c000303001161250700340080d4040350400000b0b40d44801c1b12452030300310781031100f20390829001110501c111400b069545010f440c600b11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 621462877 1250 621461627 621461713
    0x9040b2809021c0b030c0324060301020301080a1b150809060907051005130f03140c0102060714030a06080609010f050a06030302030702060c19120206150603060f03 72
    0xc61034000340400c40045281100d0010340c6000d610003c0d80340d6001d00e0f200e48011500750f404001c42a04c81c4002000d455400442c10300c03403101280513240340d080802d038030b0b4002405440e040c1b094074100d6100e80040c0c5200740302036550000340b01080660110450a42e2030120740b150030116035018001c5a5241c00300326061400d400741c0340c0349000784514400c1c1e0124034140282d440b083d09030030024085003810350b114481303102210940e030160b80080481c014046400018410a10f010308180d407010019620003c090b18012600e81c0c0040b94100c1c08587c04480381103846542078011030780928941e4002503040d0704e9801080c01c10105030b07080b0020307a45034150f602003814540304203608500300300000c0240e24550340d806522400f50307000c041e20400000c41d0040d5070070420300c81902219650f003042401e0940714684044014460b958400042c03254800242c0a081807441b151081d0b030008100c241559100c008019580d00c1e80c02c0c601e0307014042c92181c10104142c0d214401254454264914070302c0c10414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 621464127 1250 621462877 621462949
    0xf050112020f1314071d0f2101020d0c0302070c0b040b0406200d02160503150a051e040807030306080109020a0504050c040504050a2301122018071214010b09040b 71
    0x6c0307801e51044400b688500c0065032080080703954044507010480030380000d14244c0c1d00a00903028943c0c0c0441c18003801100d01980340d4000e0603100d2041c881c0d0800b10351104400c006030300940c001c88103201802c200900c4818000c1c02d07030f600740e607030861411400d014188110781d0a1100c500640c1c001342c1d101c042a165454030400f583c0020341800c1d00140b1250f040805400d11598001e0125000a581c42020a0300341d81101d0951214001c0f901c5035401c1c074240380c50001450751200400303600080c500003020900c4501030180c00c0d07406800030312102c4402d040004100003003502402e210b0241c030040000180c25100ca001d40c2c0d100700350700c000c000b40414610039041d1f0402c1c1c0b50180010041c0d0003000500654407003580100b0390179001140100180c201c841d403800d5140c3c006606c240d20443c80101c01160300f07100414544642a2903454a0028129110001c00c0c1d45440e52201d81d4944204014842803c49001600c0210381c001c2020560082c06804900c00e001c000c201d4006041d481004417035201c40790 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 621465377 1250 621464127 621464177
    0x80c0702183c1017032701051c0b150304021507030f0320072604060e060f090d0b01031101050a0905101e030f050112020f131407 57
    0x4422114140460600002820408004907400e04400500403c6010012480baa07028003d01000010040d401c3c040050f500d8010382d0b98200c012060042c05000440180c45000d8200c4061b1241030030000040f100540c8540d220300081c0740a9640c200b0316440b0354410302c0b1251010445c0003102c1ea2410325005010007601042e0b03000040340800c005000000e40c4c000c041004024480c0b600080b5075800f8000e40c00110b003040e09421f00d01c0d1000c02c0000c10701000b10b038001081074848d4075800f80000c2002c1d80400d24061071080a010540515800d400c81c1442d8000b000b11240c40710b41c1d240303410a40000110301c7d4035050001c0d9465042e85006204003c080170301888a8034007402c180f03051101100c002882c138070a43c0a4a40914019030500c142c845c042c140c507480b030107640208461400010000140146240c10440c0c0c404d0341020000500c01060034560700c043d94000d0010025501c01d8020300c9078100126051401040c0d81d03165982d202c0c5030380041355014501584e1004080c003040440e5007402004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 621466627 1250 621465377 621465421
    0x201020c0d0c030f0f0602070b15010c2303090d08091e06090f030109231b060a031503050106120209070305090601091e3b0706080c070218 61
    0x7181d011403020070060640305046070360040340701444440e07900d030101d4030b1070754000700600c01030011883c001005040b1401078410301d524004490a000700100444405400b5840649a076801030780c002544201c480c000c210380103044007100d01d0013001501040d100c40e01140191101280410b501205250000c0240304001c02c032851081444040c60002d003c1d4440c04140c00d20507083e040c0d00c0580e0b0348003034029010b07107074200c1021807007090810104000d107035210400e00c526005402c0c801c0c0d46002603032a540d00025010301658100f41c07910005034000d0807540041e81030302c4808040000024000d0042401410034038100d281104054030600c0a03a2801601000c285402c1a082103c01440090306c94110f959403400440c110300c104036007440b0681040054040182490f845498650103080e00c158081041141041d420300c1c580300713030240c0b600c0c0c21200401a400981d41040507520035910250000b0240d44094038142d210360005445050f0368000301040d0140030200110400404800828004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 621467877 1250 621466627 621466639
    0x90b1906080d0905010f030912080a0e03041406071a01120c050603010b12150a09060f0e04020306040f020315040b07030f0c0509011206080307150b0109050a060f12060603090201020c 80
    0x2582e40d030243c104021402080d0400200c46030072201c0d0752094201d00e070055000340000c440d880301d10038000c18059084429000c118208003260561000c00011141100c01608196080c54440c9040007802d40c00002d0681d1058000300f4a41c0c003007520459601d00034003181054884400f0203140c080c0014506a00c2a031040b1010f000420000c19000c00321019483c1510f01200035039107800d9204000a565040540c0128280d00086407840d4551b01c20b00a82d42410071483c142c0396100e40307800e1454800c440003900343d0001004500054444451105040d1008040d00d40030402ca110b081000a0f084605079103c0d400f90042c02140d07500340c0300d03020768400d0b0140d05000802c0c6007400a8854441e4041c554100702d23411201801d0071a465200d24041d03c25101a01c2da140654244084298614058010507601d4044203005560044010100b141c40140c03c804c181e0380307007400c151901451221400306200c2c6c6040030000413140d80c82080060174103030b240041e00031800d0000a151980c21501c0034003d00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 621469127 1250 621467877 621467893
    0x30406061202060a0507151508010e01090305040b18030a06020a1d0303040b0901090b04090507020d180510110109050609330907030c091a040207120e04090b190608 72
    0x10b03c5880880300200114101a036842c83c59141c0306d240703100401c1ca210b00907890034403514003020700e00e01e20100b281ca640300248003090130703804100e080310255403006010034400c000411541c1c0d155005420710840c3d091f43d11100a041c000800e05003600108216a02c503400642d4144290700241015a802002250650301c8869000403c3d540c0c4980d0140680f00d000100c1c1000480c5c1c07041c46c01d10b0140c40d81c81c02007034450381d99840c8003018207010b542c108098050391200030186441101107115826100c0030b06819180fa18080c8400004018041d00c1007000215005101031801d0191072600c83c481c1c001080c6030b14102c202103003096000f19415001a1840c00b0f00705c051000c4c4030f90901c152114440c2a061750712442c4000c1e150114581c0020504020a83c000410b608150302040f17003142011211000409000200804c070320500c04018414a07407a1030f01c4034042d110302c1c3e10040402d40030784001031400c207035220450418411100c0c54042924031242030403181160046400a0046500400c460 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 621470377 1250 621469127 621469129
    0x207060c021504080d5403030203041106070b01080106091802120a05070b0307020d0c081602040f1104052106010329330d061503020402040b030406061202 68
    0x202d4010b48040c000742d030003240c02d030b140540036413041c08210700707111045080342c40e0074901e890701000c904589252142d900b0178040155002032840d0070b10740890800c035011025165803e800139040034006072007250320100841420748031030000b004c0540c003403031301fa4240d90300d080089401e5400940100741010b060015070000102d81550300300c0f0040d0f0440c3d07031011582d250070b0141c0c0b0b4144a00006019403107007100008440800800440c012650340d42078400701c5c40750080584a091100100a00200080100d03d43c40b913000c1c1c1c41e5600c507a100520215105188000e144260303600e882d0707400303541d080c002010000c0e4540620b00305007018070115102c0e00a180721822a0306c0c1c042c1448040c0c9000c02020f10001910103a00f00d40e100c0c0104503800c01c0403410180881d41400850710782c42004401000c00e15000c602144540b040400340060405070140310668507080a001081d2016000344e42e07100c0088010398450010b0130141034020356181d02c9140c1801c140042d950141c2c0b1529100c1c802c02000b07405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 621471627 1250 621470377 621470413
    0x624050d0818090f0106020f06060a030b0a0b19260c090a110a170a050c040618050303030106020c2d060a0c02040606090612110702010c02030f0a060207060c02 70
    0x3419401c0080070340c941c140c81102e03041d2040000e02c416407001048081011040101c48104d068406982c00c13144201316411700f4079500d10041e182c1c150b10405c0300b442000003c450070b1100b940f0240508010590a00701808508418000d8480b0358000e8014030301406001003020110001040c8010410003030080144206c0e20380d04840300c007600a4200e03030002503400603a50009070744001c12642c019518032140d0130003800d45590000400c0c0d03518140002c540542130501840e400303000008c00461510b4078000056410100c0081a104050585000011599414406140205525005001250300000412800340700d45000500128400c1d5001802c1c2074500030202d5281c1c00070b48015590701c0000e2810b0701c035090089402548503081131400300d80f072a4022206da0484580ea15040000700d959881c04040e140491510f601c48a030510551380598414031041c42c2c0e0310f0000d0192112042c40101450610f00303040000ea4009800003603040070040c00d0700c940710140c403692020741186000d4500c0612 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 621472877 1250 621471627 621471649
    0x8072a020105070c180b1c02030c0103150b03011e0f0602060601051b1b09090706170705040807140a0509010803090108190c0c050c04050c160302011404062405 70
    0xc1040b1010a000c401c110304e00c1c01c4880600920400b0100022000b180b01002c0d00d4400700150140f03c070a840844070400030f00c1c0b0100340d10340c0100038080c0b40210344011002444210004210200c00304000650a0034820046011307000070260b0343c107000141080301000d0840d42e8440300c400b4031500707010040700c0d9020416a800420074239003d45c0d00e001141d416214400c0c800525000b80c0540000307a040145014504a200305054901e184142c1d00c0e52040d50f01e0318001d01c580710100e41d81c4103517100c3c119800c152181e484000d60400c82d05054031303000350320705e0414140c0214920302c144082000c8907140003a0420000c1c482201c3e9011b05605101c06140c40b8016007180a0522260340013040e08a40d50a039540750154001e00100030b0000303c08030042c0710040246c01a940c9008000e06e40e010350400e130084a11031019103104503c2c082104100c0f181400b000c4a0a0f81195606e40400b2200407200c0380043c0114091440426140c517502c40300706040f103200101111070403107040c0400c00c42e124016208 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 621474127 1250 621472877 621472879
    0xe12120415020c04020a030f0501060e030705010806062214090c120403030912020d03150e011208041d0703050a0c120902063114060f09190608072a02 66
    0x200c4140c0641c002e0f443c083c100950b241e40715001084613854264164090049060402014002030340d9a5409030340502c0c4190780320707030036410441041c032165000d900c03040c0c1c00c514058003d0f403400d0028840c040648401d0342000340f030310120060800c42545500440400494100c41c140d0850030215000200740c8a00c02e45610a03c080d80700040500d4020707845600915040b050710020b003c64143c0080d1100783e80302404c00400e103050740c1e40c4244840000e0101c103a442800d0889460f90170450110001c03100340c18104d1740701c0c200b003101142d13400e00300e04065108500d41e80710800904142d24081c05403080146485861403070255186501d030781c003a5050216010307020001644031414008034901c2d00c0783d805400e1004000c44403011001c44404c186480c020b600f05581c0d400d060701d41540304104100e00b0f440c03a612100c05d00034500d8441c4a00d0080c84100c10003483c1c42c0f02d40d080300e142e028034004d1561103000031400c0c150801c5206134005a4200780300340c014440301000c0c0840400c01c1d041d0200301e000a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 621475377 1250 621474127 621474149
    0x203180f03101b030e07120201030b130e061e0f040b092103060a0b0403050a20090414060709061211250c051005030a0b130c0e121204 59
    0x19a400703031414050b09111a10760041400241001c014688403406542c2000d000203140c03904a24400a0210314002030340d4034116440c201c10031940044001c1c103041d050f201d40c4250901c14050104006210f01030720a029200505039920b824000902102d6070310000414580c00c1c0404c21000c0350504086a90103540844100c02c1c80c1c5070a00030f0780c40d01c1c1c0103034000318500b040d400440b4651043c2c034014520603002160003415103500d99400d5844c900030fa100080144e03001000d042c00007005500c0f03090400b2107030400010301003990400644000e10a960503a9002900c9a8144521a06101d41c1d58800041e0805180180ca0b1150041490034440041a001c035030303426080c0b0503c04c0c0d00d8100c1c0c90070195092130441a54031101083d030741201d0260300b128216400c5600040500f82214882480e024030b48032282117070707911884d10300504003005486610045150415400350414856000c80c64255950101c00007160410b121040603000c14907015070f07000303107011480031a0840032101543e10542c46 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 621476627 1250 621475377 621475399
    0x80603100e2d0a050610240c08160f0605060a0605120603010216081c0501050603070e0d0501020412050f0304080a1211060106081509060a12170c0c0907020318 70
    0x40c80010b070019000e050900656111105000e40001c0c3d40307004030390001a0540e120b039125615000907011100c240803010045107544c0566015041d90704420f8042c80d0342038901803840040d8450b90403450720486005140d1406a02071040c00c2c82941d03448031003034400d100500d04200c00a82a07020380d00c0c41c000340034440340000c0e20946003034040d07402e0000c4000e4400a640210320303204001c0c1e00405504441c80b0b080f4113a20010301c859002c0d0b1812120003400c464a0754503040c908070b0b60a21801e01003030304500300300100e00024400344000d20080c04c030507641c100c40714010700e0458101981142080310701c1d8424041030048a04c042401552258098081031940200d5542601c10300d5100d03803214410f01a0b00000100035801c2001d00c0d2140a80400780d8225404040c10000e5a44041d82c07980d8001d0000081400260b00c0080c08590b9180903840d48404070426001689541d800315921001c82e8000c1c5582c40080e04210803d0740d0080414006141044038501c0c1d5040c00c8503140350058454145000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 621477877 1250 621476627 621476683
    0x307091503091707140d050403052505090a200c0c0603101202152215140a05090303130314030f03040602071103100e0606010e0a0b091906080603100e 66
    0xd0807155019005058a0386c05070307031030009441a0418441a03405001d041a0421001030740c2c2e01c9001c1c0c484000d0303c0a03d2b0755081109008980303030700901018105994140005150722512040c9203448031007010680d0303880796000d40740d00380000c43c001e00e8024003042c002d00140d6000404818191740a110903040d10791480d00000c0c803491031600700316a030960700040c0a1214a41c5000b610440c4080c0181e0078038403580c4840c6450000402c05500000801182580e48500007031002095090103514160341842c01e11800a825036115026010207941064000c0082085c02011703090000015005503080c003014070490891880000c0c0002c01c071a5002501d0700030080154609441c003407000d42221054440780d00c022000f0407566551581e24421030f07000a131103600c104075108203420040c0c0103803840d6103400c01c414444e411000005034000305c04007040c1c5c0140c15040048000b01803030b031b48003042c03420050141401d0041081e40604502d04002c050001c4901c008bc04400c280d081000740b10310000203075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 621479127 1250 621477877 621477893
    0x9090a020901030b042303120a1d0c0a08030910050a14030117060c040510080a063804031106130e090106050a09021321080307091503091707 62
    0x4480258031101540c0007005210782c14440720301c40d03841821104100f18030824416804082d0b460400d400b81d004015071045501001249a00300030b0750390010420111900d90203c40c10740b030003952000c56100050894491810b038400c60010524800514603100e401d5011403d0020b55400c001c0a1000c0050f00c2620b00340304000804103140c602c541c0689a58403000c08200e00160800107181e10f110700000300d03071a80c1038001114104c83c401040d0b54080084c4000070303544810004c001003540d5958800000b58940400321030507915000071402140808100a0b2020026074285900088074060200f840007803030b2082e011900304411600d141c1c46018442c4000c0d003412039030704600490440a0203002c0705075015003002c010b841045035034020007510780034480100c3c02000d0b202c100e0000d40f4a000c04c004541803000d0a020700c3c20aa001100000a455800b0f4651040e41c42c880020400c48041204030010544503400c080f5514091040041586807100c0410345181210703400c0c100003610342d013000011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 621480377 1250 621479127 621479143
    0x50a09330b03091612210e040b040e0a050102090a080115030b090f100b040c0e090109110f19082d070908070305030a080c130308030402011115010611010908090909 72
    0x6a240307844a10744405610700f030043e42d03540803074065256a0000561b40080e89086001e540303d0341d201ca280c00c600c1004c000103030607100c0c0d00540040d55203208864504051040d032030352a02500c0050f81d20040a410b1041003045603201d03071200d91611802d513810400050149003182d070440860b941c55181c0c4c070421400c180408000412074800c4051641c40d40505401c20040100101c130100040c2440c901b094031524801c420241d402007800e4014071101803140d020610715040c05600038217201642300480704950011020a58407070301e110190045650040010380d020b031a803482100b0340075100e80110085408124000a014030010000c2d40051180c01110000c2603080d04441c200c84e03590901d5500ca42c08a034088000403a800002101c4001041c00c846071802491900c65a0314510340740c0100c1c5404c05001213040203112294203180c80341c204800e5240076052660040306d03514014029224480c80d41c0a9601641440e0030720000c2540c00381a500310850546240d001380d80e501101c0d609000e50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 621481627 1250 621480377 621480403
    0xc0a17070e19050a080114041403040e010906030c06050910111212010f0b0a0f12020f040806060307150903062406050307032d0b0109050a09330b0309 66
    0xc0202c4440101d084110308411110150340b03140000e07071143c440c0f600ba1100c01001c084424082004140010200c010000c0e400d082403055a08040c0c840a00920035007081c2d10000d040c940f20a424410700074801702c038000400075410a1440d149244c004103c00c080e441e007019003030000c000c01078103000e036061148074030090a410302d25a0b02c10340c00c01c40044100c004c0c040d101e40c40000c03040c00b04025102e82d0486900a58503190601c41c0d44d45079070f0407281007005900c1c1109041c0c09100005140800344042c0015040325005400d4034600b04050600d0708513554001c55500b103890242c000c00d560444040815a40c0040b004100c000d0003000c80b8001c291650b01000c1c046000710740000786c103644003001d94042d107140d580a200345098484101000500c1401201400c00d03071568028444507503900c01e40f060751040c1007940d1101d5417400010260805644951400c03512403c031400482c40245251100c041040c1c440413a16100001014802c20f550140d032040880000c0852441e61040001300c00d02c0304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 621482877 1250 621481627 621481639
    0x6030501051306060801111b030f07440f0c120307180807090b01110106060f0e060f03040204050702120a020d080112120305060103090501180b0c0a17070e 68
    0x101a81202160022010b0a0b10f5141c68600041003041d81805202a01c1848101d03550030300c504007203020410004c3e80008190b5100c10010000050002005802070714003030100c0d18a281e1010032240b421041d40146800180d905082d035204541042c19513441c1d8400744504035885100d00188040148500c0b201d8401da0310030603103241000c0d40c20b035000f54420501030f17640c009070344500c0d408103a503000280a4403495800820f0300340600708403a40419540501490b033030006251200d081400c45640d0b400490029089103660003410707410400c2086c01341130640f00c16240c00710140c0074003258000079000030301c40c0b501c40b07020800b01c0b4820024426a5142540b1240e5240340d0584081d5032945d48420700e01c0404c40300c1c2c0000400707141416044c40c00c20f802034402080001c1c0798208600a0200070007290605588800c060045503091040300c4042d4030411103040307189500d041060a5410050008101060800888400e42d600c01d001c4104e06a1180701d0b4902c5444d10300040d00c01300343c420b10064100c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 621484127 1250 621482877 621482881
    0x16060213050d0f050c060406020c0d02150c070e09030a0504170a080409020403150e031905040807030c050901050420030a09150209090a2007020406150f030b031b130603050105 77
    0x1c243d0541ea5142c25209001701c0f034089a42c941800142d0256118000160b0008201c07001c0a041c0503040e8082288014000c4001e200d0301c5101c00705c2c07074102c0c0e502820180e02c660300510000c0140350021b50040d01080003981840b034000b0000b0050702c99401104104500f43c448245140b10810603040c4041d4001354141d142c68603141104004d4200788000d0b240e00110501c4420346110754030661080900e80b00185140181d402d20154111040a00410400c40d0402002858110501000018501c92040320664925000410280040c1030308aa4440c80c03509880d14031060303071944031a080030307000341001c1c1d1030f5030f290440c00005100c41c0d05e0207000040d005409a020380816070003800c112408941c1210186c8901c00d8080c101e403a40281d40f84c6d4000c60403141c5010081c0700303010780f1003644000c101050454450103180d05025404076000c01217240305805150941c1c240c000e607505818142c00901081d122841c4c158070f060350a44501d030040c01c1507100c60100c6c42c10340c1c0044001d980c012009116034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 621485377 1250 621484127 621484133
    0x9060605150d0b0603060117070e031911120303071110060e010e18030423040603030305011a0a0806061b0a051f090c06030c0207090e0a120516060213050d 68
    0x1642c8940002c41d60a4a489a441181e02d080800d880c0181e1040e900e0200b9041c2a10b0544441071002e03021000b0301103030030040c0780181c0c2c04000e41501800d010080d21070420051038040b205161102005100d40d40840d006000103034004141d9a00c02418501000d0440b81da03007400b400e084039201c0c3c600d425403d00e00045031820100c076099040324403c5690007030743c0c0d503154040072508410ba0f41c80d03d0b0030340080108000c07000403c0310806030b00d034440e9280d201c088541c1c0c1c0001d0071200c1c3c43c1c1c021808039441c1d80c0104619040400c03140402c0f100203441516000040400608480004001c6072041901082070044100c0c0a295900394080e4101151709000c0b060400b0b60380c8600044122019400020900c8403c000c9409030b10701581d4006c18034105507081403c158094003021102104510686200080050040c00303000095080c18020b445000c0440c2081e83d20792000070340311024048100300d81201710321609040c2c0c02ca039810120058030717040540280704102c95242c1c06541c1c440781f403544110034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 621486627 1250 621485377 621485419
    0x27100818060a091401021e0d06090203090d020c060c0705010c080d0e07090c0306060206040f020f1507122c011e11100501030308010e0604020f0703021f0b0d0609060605 74
    0x4054050144404c040e0201944c0e58240d21903828450340200440001045030f003403807809440484024100821040d44400e4804200e1300121584210f640c0700100d0b07050400e8040c4001000c2180c181c070540d02e012840c0005a07501c501910400e410030499104030b40a004802041d1060609952401c0c82020400c103103469440b1002c1c010440100d241048042c03003a030080c8145c0c8207ca9040d009442c06a0b42c079110321090f510f03503074000d0342c020200c042100120794030745d0001d42c11010824441030302c0c0c0c145414040015a034820820083c00086a820107074071107400c250741d031803403503051003078440300d240c0401203030241c4000c0c0d40030ba91203c41000d860305c03103a0031101503c148101c2070308807012220302e08030684c150307502823102074045140030380140003221440081d580d06c0500980054501905030003101075680c03000006900603007052958420320071017140c00340c0c042500ca8805001010082c0001104c03000c400400030b140c55a12080001008441d401c00b0008100041c050003014101900c0d41c41c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 621487877 1250 621486627 621486641
    0x7020102060105120d03050c07050d05210402090f090c0901090e12192016031e080318010b04060605040e010603050c0405010e0d0b0c27100818060a 65
    0x102600400c1c0011515040004602c05003268803001006416850041503004100c007410480041508019200124000300942c2c204a1260358a070b0b80d130340106411110980c41c800310b403a18000e03141d500b880301603654404040d403c850303c44010080d6895106c441480e2285c003200180e0804002c40c00003610000641c0302d80e07240d80200381034420203c0da403410107415104007100000c001c181ea0343c003d0076461042d120714060b88081c0c806034403000c2e1004001492702403044500c1c1c0b6910300507501801003140da100f40036041c5a4460741800009410b5440c04c0241c04000c0405190101c281005010100c0941000c0c10003000078108018aa84a42009202e9445070081034916408940001281c278828420ac503c41e2081d8002c280c1010b0514004460384141c1e1403c4a500c07a00a40500001c24903018180380035080b44582141d40343c1850f50b40c0310b0f0000d0b03500f810301100820742c400d8030300c0e54482020304000c044481ca82002140e9540160381120028034a950740742d440b0700020400308101c5580184 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 621489127 1250 621487877 621487879
    0x71505090c04022d130906060306080d0c121407050c040e0d08040201080a0e01050f0613150b0f0c1207051b010c1401020f0a050414030c0123041a0702 66
    0x81d41515090342400141c2c030461003084841284511403641002500d099212000b8050810b289800c1a1540e000d100d42e003150480c0015039a00d010070840560144507007002014810040c00c090b00082d030002c5d101d010350072000b415141c04c50b0207295480b44100444002c0a28058540341c0b2204c503420141d0340c0e00b81d4070850a0282d450452400b640c0c0c40000b9981400c22900e6032486010799941d80110780c1400042e00d00006242c48032007640f100c8000b07014091090b0280421191345190410804c00000c2041c2910024649407505524a003580c4100301415140e500c1d20030351307982050780103145051180542c0d0324030501402101c43ca410707022000801000d03020700200e403102d00040c00c445400360041d901050100302450402000500441440001c4903114800142010080d01100d800781d440101e01ea00062030004d001e0180c3c0480c460003420500098000384140c0f1030307041c00603008030801c5480a00070601c000c49041002c0206e0201c401a0590300014189025140d82c00c100541000e4001c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 621490377 1250 621489127 621489133
    0x30602040e070c0b1501020a02041d0c01030507090b031305030a02100f060e0604180605010605070b09010204050d021c020d110907020a11011206050603070f1202031003030e0607150509 81
    0x2c00d4225102d15540388902d6004811940140c944940304c0280341251010345d410350050300d10700009a075035440b0341940e4003048654460860001e94201d41800540070000f4185460700c8140441c0c0ca5000441e18103485006845556170f403203418000340c01c11103d0710000e001e840300050040c21a40d011618404800b1074420600000040d40a40c070245c1c2e02c1e500800c241c03800440000f4429181a40002400e440c8080b1030849406c40c644412080c0c4400348c01030360200310b00140c410208003c1c1c044260707001948a00071800d080c100780010b90000c2c0b8450000c0d11400380030001c0c0c0b24944a209401108a5005040301c021402e14600302001d4444043e03558030641094001030200350001c143c6483c1107034821070b00c2c40f000d041d040c010340764480740e5a80070715102e03903d581c089541d860b0100214046c0e607098640000520503841c0c02019414075a605aa42c24014428410701c24590106502039903418104012100c1c0035034049890b034007130b20b20007510303940c0c0005035414040103550103140216070007000c1d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 621491627 1250 621490377 621490381
    0x1202031006060302091212030604020711120c031911061c050a0b01030f0b010c031214040f0507080a05030403080d020c0a1b0609030305070803090114240d031d011206030602040e 78
    0x42e692210220801d03c7c04501d002c1000403e1803500e50300820549103e000340b4203886d0510000300325007046c0411a0942c90703010110010091604000c00408005440342045d110030282c0c1d00c42c05d005000151080c0034020104050054820001d0080243c202d54542000a89001c0b03030b05070050500d010306240481d01e000100888100c0364082c2809081068507425820f100a5604a82280f554000110110307900c4550442d05844030000c0360081d4050840b9685040203820003500704910340e44034004c242d11003d041c17000200003105070b404403a0080380c0e0b580c88105100140c00030f0b110384e5001c400c06003d005440030401071f02c8096042c0c8030b450580903408264580c9015260036266001c003070302103a02800940002080400110303480502940045213440320800c18000c4120242c0c0c10850311442d940189250741c45a0201c0d03c0c031f0038000c4812032403460481c0c6001e04154013034400388042040b4100100d100341d0140c0030b040021403000704c08001d0960740b0309007240203405c180102c07254200240c0c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 621492877 1250 621491627 621491659
    0x105040b01060c11130f0e0c12030412061113080d080106090501090909020d0506012309060f010c05011401060c150207022d0a0902181801120203100606030209 70
    0xa9060355a4442c4484c081040803804200a1a9012000c4400d040d10f0380c1c20703c142c040903401404542100b030f10003000030a2201c0c1c1040981c4c0c41c0c000d1404000c2d4020702041040c03000c040301c29044242c00500c0020411150b02408416104040512107000014000000c22500024800946460980e201c107401c1e62900c00440301c140c0d6500c207030f03400078060a40c1802041c40301c0e440004032520013021950380314060780d1500c0c2068826809000f26244084540d00211403400700303450710090840f410807d40c503040d00028882a20815141d0420117211010070420009500c01c1040494641da145010360395101c000b0141965603c04490f0b2015101000c02d09003031074020b81e0b2426500404040d80c0884503031031540c0001030000d110b40b11803240602c0010644886011502400c1381c0c5001507610100240d5200c400703000c403080c00d4040c048606601180c0c10920b62910f066a5100008003c1c11040e8000070307140c4500e003a03040c0c81407485c1400c006403154141c0e008245101096651280102c4114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 621494127 1250 621492877 621492887
    0x4030c0305010b0108071e021c08090d09030b01030b06030a0c03050c01110106180c05040b040306021e0702090f0c0f0f0415020304060c12110a05161413090201140c0105040b0106 78
    0x281d1491b01080e90b8414884410b1421040d405a2298510455082100ea0100c1c02e5640d00e4804551000c81c004809228090009010300c8290754818100303121081e1039940c0f91800c1500500c0050058440780010400d140d900f0300c00d010800d600700000404240d1a42000c0d80c80d0104102d80754040f45006c00c644200308018081c1c101103802449020f40624008204003028020146442c42000340c204000f1415004c180080c2001e18040c5000584481c001100444a4112000c800c5010342c401d016070001651030780e11850340701a60607155566622007000664440c041c0e40320031003d440300400c052007880702c06000303402207c02c18000200c1d4510b0b0f000059807a84124000c500c0080c2c05c951400c40031036600803030504206071519140c040b104074100c1e25400c114401c00c1c01c0343d90390041c83c2c085040d111000000303000303411031811813041c0040144c00280039442c4580c11108961704c4881140039a80038079042c0601e40c551141883d80c40e0702c00c00c4070300c2c02810205c41c201e41c1d82041c00b0010031403a02c64 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 621495377 1250 621494127 621494131
    0x10020114011e03020418120905012606040c03060504022205090f072a0b1b03012d0f030b09060c0f04050118081014150609060f040b04030c0305010b0108 67
    0x40e92070408440c29502171201809266942d003500400c841409400117140101010a0f207038566a01c0001605210004207000c1c1d041c0140030100700742009180e40e032b403a86141c0e140c2041c0708440010344403200b41020781c05000d090b0f11041e40548041a03104000303003009500d114854141800b0070b5195100c100700000c88105907070a01c141082640010080d600500341216202801c540800c00140d2200e16000c042807241e00859031894614280110f0030054078900d142c0d0042000c405055604090511160040d03040d441c503107400e407981c01425800f0584169001034a0103266040300c254a86c2443c0c10303000300c2035036105414894200000d090f50240c000344c0d00e5603c00c140c40d40d841d0070f261000440350070210071069181c2c034082c41c10008174440304004540461521110100e401c4c03c1d09100c07a0507400004041450b054000d6043c00c0031a0b40311740440340703440004c954868451503a5086048c8900641d0044081100001070100910101084090840344254028000c1c0c00c0e41d103004503401070381 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 621496627 1250 621495377 621495419
    0x90b040e0d05030c0d0b03071205010b010201060503031603170c070c0603090804141f021b010206060907110f10090204050c16020906030a0614010e09060108071e051002011401 77
    0x20910104d80f07000240c0d0010000c9801c40040441c81d030040400090402c00981e0000200c140c000b44401c080002c28014030b9420032090008212036071801c000309441c0d00c1840c0910982d004102c4890041502410341d1100c408140c222002041c80d00c01c24100076a8480c9006964810440e10005802031082c018011455800380d480d500701443d045481864039260050558000d00c00846041003020a0802ca040160903900900c0110349a04e0350350356400c5d060150078110341081c0704002c82901c5100ca0203800940500d410315882d40403a054909100c903c0501400034003c514502201c188550003031405076000300c408002c2ca4580c120350a000f4030070203184404000e0105000c1016103455004983d001e84080c058031003000c100d0741d4500803075409860f040340302c5942c03800500c00801100031060744440301100a09480d41001c154582d180c1c4103100302c500141c030512448010800e0006c1c00310040802901d400701005034400041d000e81030007560504403070250000000c50f80051207184140b644 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 621497877 1250 621496627 621496637
    0xc080313031203290127060509040908070b0f15010e0d020d0819090905070c0b06150403061b03020309150c070f112404120618030504060f080708070f1701090b040e0d 73
    0x2203041029100d540007a0340d09c661043c0d031105910046120580201919442510000e0031490030001c10560520050306034000c900354148086116604101144013405007256040354148031480096181c5540c1c0b01c00410518001c2401804960714043c900d40e90505520390608664485200004643c01101c20900050307020b00c40b0408140c8609887d034002601409400c400c803500a0040030340d90055104540709940c8640f0b0200005072600c00311803c0c0e8ac2c624040d49181001906c4c6031381c48020400c40c5c14000c40d41408107207040e846100316100c05601c4800c07020710701c080341091800d160400701c5d030a0254841d0304c4a96013160045000f40315142a0060f8641461300f4842d4800081d1694401200c10503518040403c0008200c2c3c0d90b00e600c0c83c401e594a5a0740c5040c04002011b00d030700d921078001488920814401100d4101d880c01d584000c251a01049010031050229243c062420090820701aa1800031611540c01d82142c40450000d440c140110345a2100322036270f80e4030421011740010303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 621499127 1250 621497877 621497879
    0x602010b10111002031501090b03070804141c03050109050906010b0d0209030c03010e01060302100908030d0b060d0608010e0d05030f0606070503071205070c080313031203290127 78
    0x74050841c0d007402c208031008031460f20a41c400420102d0340141c40d00c8000a01c240e403410660b60340000c0b02c0000e4100f02c0052400d40c104098042c140c810007400003004284140303030009003650100208480b071403132a007180305180580003001c0e00401086c05080340880c10000080c0030700800280c0700d07040b5030401130458545914162140000d40202940c141c2c10301944803268100e9400740503003000e02c0e146400000e132891461040140c81d00d0421a03001c01c4c401e003c0010808100c001c810380c0c00c007100c04070780800c9001c0020001905c0b8030400300c071007040358270306030000c03a40000540c040c05030517204404881d00002c03400c0d0195124001160040c40013821a030018080703040c86800782c1300b143d101c4e0044a00b01710060340c1d0303107807011911021000007490100d568018041500380c490000c04158025626100b50401d440711100503601000d0010b1b245c214005079101d1095010010384101c0b0300601d0b1b01c14242401c0134007030003014401300780003400045110390104602880c0c00c420a041a80d070120503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 621500377 1250 621499127 621499159
    0x5131e12031805060103050d1701030825060f15080a1104090f0206030a140c04030812041b030c0302210a030809120a0c02040e030903070902031f0605070605010602010b 74
    0x780440740e00d01c2801c1c02d854590724001510401006000c0c5100e000501140c002c80c03280108030100c01e21142c4d9204420030b00400108141c0c0c0200c803004072030f4410300420071040440c1048a802007500042c041e91a0141c419020842e0741e008803440e0f07140c0c0004140640c1d1340c0000c155642c02008000d00300744881781c2c2d44c50103444c00303601c03255410f40f05006940c00e6a4464000410603003084600610741c64448a407a48280010038600b5407110301092400c0c242810b5448200c0c0d203000b4980102203843d4601d02186c18050484290700c10480c9603410421200d45074580f516a8078458407049010342401d0360200140d0340c40c2440140c821050f500188241b007100d4034200c0d60310902428080305401040704185e01d002004008021181d0139840e407209203145441030000f02d540c01020303845103070018000806140e81c081006403c070f806103100943c032a142d114200204161110011400c80c1c40d0f2580041c2054000c4080e01403a0300503030382080f8903aa0340d10180c0c240c034403061110b54040407c510540750 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 621501627 1250 621500377 621500381
    0x7060501050324061c1a25030b0a032013140714090d060606120908043011011403100506070f0b07110d0302041a0705030d05131e1203 59
    0x200c004010704681c51010f1400d0810411705140c1c03410b54815420034812842180001c0c400e503040741c4000140304403620340c425a10030041c2c1c0000c0342420951513100095056036400e6044001c0c6401103840b217150654035a034001d4851281898901a048203c0f900341c902ca818822061196100300c002c0c51640d0350603808403501040b03d202d40d44014018000e2820796102c98541150141c82444005003032401e014000c3c10307040d20700140702c2c402402d100c50003001a02041c10758085030328a204601c4503c02c40c90166500a10003504980e0081301007050109003c900d21404603490001c0c3c0340c40003600c0401e440d000c407611049a50700000e5183d00d100f00700b1800c1810040c043c250248025490a0358255180582e101007611032a0000d62490582300d6690380900c20910901c1d814102140b515103000c01c00c4003c0680056100f6070301d91302041480034440148119030f0300540c104407c000c2032070030000c0c401c14032440c4802030300c41c2d5030300f20344c0b062030044610b030801861500322009210b058540201240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 621502877 1250 621501627 621501631
    0x190c0b03040206040306090602091e0f010e0a050904200a030b060906060d1b0305100f12030507051005010f212301181208100e0c120403020307060501050324 69
    0x3c0c228038100400008640d480c400c290400d0310840700903a0301c0012074104000780440c0340d80c1800d5000318006211070355586403124100700a081c00c00548141010001440d01201640003c1d0070104000030041002445445c408003c243e5041074840e00007444140802e0070f1142c007005084c0c0c03003810b0200e8054038081060650202e401815580381201701041c24050760340c021308a2003030090003030090345015014011150300040501801c1425454481d05800b0b000482c0f003461720250784c100450003410b1080c1d0403144069080022507500e0103140f0000f46c01000c0912840104505000010030000034a81d484010f290b0a01040300c0c601c41d142c8c4907000e108010103030300000c41c02c0d00b82d2910ba000340b080c007484803181c0d4000d4000000d030030f030750500304134800c5c1d4604440e042040640800041c000105c800c0001e4800002c9000190740c0c8002c4178454600c255000340d90318203c02810441007690000c028408103200d010240000d90340c0e0014140d55621042400a41c01c040d8110070034888050100c841e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 621504127 1250 621502877 621502879
    0x20601030c09201206130209060706091401090c0f0504020703050406030e1c05070303060f05090718260114091b040b043206131812030509190c0b030402 67
    0x1d02c84402508241a035101c40400f041e04c0000004200062800c0c080b03829800800c048254038101c08640041d40311700c10124010310860b5140718a8050001503d50342c400c1c083c3e140c0c001c01c054202820040840c18403032245103001c0900c83c9022400b810709000355030042c1e504d611007900f03203410b20005901130092032146c110f852041e40c2c41c0311031050403150388a2405980303458555490300c0c1c5050013416500350780c00c40741c8120100c1100708810b485900340319510540782e1500c80410b20050381a00c51003545130340410300c07600c83d46020401c180c0600c01c0f40c041d007101580082103c4598200301c00705501044070402e156802100e5050b41750710a0103c103402c107c0004200244501c5010300003822180151a4400790384c0d240c01d01941c685524070300380d100031607440e0011b02c0203290580000310002120207041143c1074990402d42c00859038464161241795200101500965400c0c2c4000c009207400c88001d1070620443d40003d08113025038000076011504940035640f520705000d400c52559001400403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 621505377 1250 621504127 621504161
    0x9050f1b0d03031a13060503010c0e09040b1308040602010209010e030604030c14010e1203100b0c030708090d02060309010b19050105120403230903070f230a0801141006020601030c09 80
    0x1d221305c3e9512507050549000d0810002009402c0405050855030940c1c0b0540c188000094420b200342d035266412a4804d41c0b00341c69144640c0c0c0c2c24400521503030420801840442e000c1000700e0b0594064000d0300010300c01307076210004000300404250b960030003a240503000c9819840141c011070410800d1602c4002d09400200300b200b00646200e02c0d240803001c0702054080044280020340c0941800040109a1003111504104010401c03649900c142c007001408058000391541482d107848400032441500104010b0322480c100f1402800382ca00c80b096148144a03400c000400d0100172881030b8190340703040e52410b06042001c290004080f40140042c0e0621502e081e128410010070741034000343d8560b03903c4241d107075081c00f401d1510b4642d00d504003910800c0404424029803501c81041082d4039180381400e0701d1450060701142803103c503500301105035420304c0700b0328030154452642030340508003d040c4c0118013603a0341022a2244000e010003000b61491640c10400c90140e5082203000c55060070b00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 621506627 1250 621505377 621505421
    0x906130509030903100516110721020406120309050603090309040e010b03062a0909160e03031b1203010e0c130803191205010b0d020c03090409050f1b0d0303 69
    0x2032034a21000c01811111b0340f0764081060311864151880b0f1050420f081010000c603107603c80d187c036501d10b409081141001c240e81e0301c0c82c0c00e9007800d00e10714441e00600200f2100c3e4445c40c1c003807003055000700140c010a900070400500d50030103c044034400e82c001c0380558100305001007003101500c1415a40d000701c0d9207420540c6e107266424003900d4024605004003214600e072800d152680d14140c3e20551964080510884003d605d66030301031a80310f0340c140303000080c06066140a81d0300946018007140c051001007804268141480c04130211035078018102e8100032448141920315200900404018200303a0011a54501c20f5101800d0388035180f00040c58440d48580c11075103075030000200c2d003110751000c246d005a510f80000391904040d590800174003c540c1880440c100500c612403003160301c41c0e4001490021403100740701b0b65440e090020010700c01c160590400540e24490100728002ca806601c0728004c5650419000031881d8501610604100c0d0702d9072402e9000f043c0160f003942c25900007183e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 621507877 1250 621506627 621506629
    0x5060409021c0c030e0f0f060f04030c1a010f1208092704060c030e0109020a060f020102040b1902010b100e0d03050708030405060a050601020f060f0a06030f0f0b0609061305090309 79
    0x195400030851581c00141107030a801d82d25242541180d2006190341208040f0791fa901c1001c14001e81c4002d4080ca404440d482e5850210744103d200300015017000d902c034450441303c510f40902181203400d131505801e0382d6500d80303c7c80450201c50440041403400100807100590900420b850442d0504d8030703654100c0c500c00c455100f82000c04403402c0f03801642d240154100682c0521601c0180d4890100810115003598041103d12000d0b004440501180c00c1352610418402d40465015011410100b40c603103040071100503140130740c80c81c010095420b00d01c800e030882c20040c1c036241003607400e0f176135024003a8444002d1000d00b51200d141a020401704000100105064600450055101c2c60041c0362a1130710151100440358040d001a045400c00342c1c0558290600144581d0005404420030440d42c40c0d1502e40001000584d1005285030140079407401845421004180c05500505007022143d40340e0003003010080040754880d500000191038405440c0d9641d004941c045000c40440b450000208 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 621509127 1250 621507877 621507881
    0xf0501030e1507091e050103051302030a030e0f1c150b03100b01050708030f0610080910021312080c06070c03050f070507030c1e0e06060405100c0206180102061005060409021c 77
    0x170132959511925050410203941d2501c0f405070311001040311000643d0090b40020746507000103401508018245807c010150b0342c0040003131040780000d001440c0e180c002070380307820f210f45615005da070a00c1c0307039a4081c55002c019020305c90300d1001c01005015919005003a42000b42180f40d00c41b410000c00b801800002081c120045006070300c40d403c0c8001a00e400c100304410910111021020011203005000303425200064642102e400c4010168035840307500200140f440c035681c040325640a0304c826200030310103000018142e543c0301406540b0b190b610ba1009452501c2600001800500d0411425031413000c502c01400c2443c1c415000c0d6010103030740780c0303403410707101e416811000c5821103000e4810450020011300c40003e1002800c1d80307200c0e24101000402030b000710320415005808600780800014801d00300c485c821903004107401e44421916440501040c04110024058403516000c1f642c070b206407001d800220340c1c004218600d094100307010300c0080e420038a0480030b0030700464400c00710080f180c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 621510377 1250 621509127 621509159
    0x4031206060903140d0801061b0f060b031b01050307050309010e060412090e010f120314070510060501231803030c010f0b0d0f03050f0d090c0f0501030e150709 70
    0x9559000b03081411424414280c454003940b40085030b000d0080b004510340c105820764111005410001c0c031544c5102c08001c3e40940d01c00700101040a54140b175410402198869210100c090782210318220034409681500c011814801d030100354103000040d4014820001160711000f800300214066400d1004246071240c00d070fa0446030344d050180314900f142d9002c110380e401024a5500c15116500d0b241d00702c1c0380400306004104d0407603440100102410b015103a1440142640188540c0c3d441d028102951940014a90340b86803506082c40040c0c40c0d03108408006044e9003003543e90202e103400d1540c5234295403201e100220142007021005000341d40c1032002d4001800345c00b00114409075981041ca049980340341180b80310300da9891041021803680e0102e1501c941e81410025a101342412440c0d84a0045041d580400c5060010010800070f52469040807074441c4406501443d031150b00550070340784a401608001d5020916805802c0103042c0c056801600c5810b049021680300c0103800800c1701d207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 621511627 1250 621510377 621510389
    0xf03110a050c130c23040308041202100512180f0d02060a05060a150e060d020c010b180705071e020312451201020c0114090114070804031206 62
    0x40d090b107589505100980d4511807080000c10040c0303444c04440070301003c00c1c036101e2091007038000468400c02c018140460780510381011a031501c83e9540c0602c0c40c02907961940072801680c030301c0f9410641e98098810745000da4140001e6080b031303594000d0b007010808841c40c2c0d1714441e03125a24110030005001d10448203a03040726070103400a0310f898080e08007076480c007038040345c040c0115450400c21840c03042c0221416110354580140502503420020300c49004e182020385c1080d20005101000820552008405a200381c03000c3e00945d18035040481111003c681700b8001c42c030300300f2100c0002680451050055a8071125964110341d10340c022a10b00308115282e41e000120000b0a00d0301c84079a8003240501000001c0da504c0316540701c002c851110142c4c4042c2d0760300b402c80c02070705244555454200c0e1810b494180001c540310071b00d444c171040c00f03014201c0841c2d045030501030204030a01d106010306a45440786000e058125110640308440b2404014810750400400c0e001c000c45000c2c06004003002014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 621512877 1250 621511627 621511633
    0x50607060b280519030305030408130603020d0e160b0c1005040605060a08030a0f030507031b030203070e0103051015050705010c020c1518010e0612090d030e060906040f03110a05 78
    0x200c1907810b5269148160040d40c40307110501d22168040501056138404d60380d152822644948407480c100001740a4603081190902074048085995641580a0f000d50075203010140325a01420f040302c3c1d12101c1c0810000000d0f0310b0010103000d415150750092039950b00682c01c483c0589000385102007190000e4508460407911013043c00800e00d0000082d45c00b810014010318034005182c03001030104840301c051241495203440c00a16594020740c071907105030a920a0320140c80b40040b50050096000b1500c0c040800e00c40c035030001c4154800c1c82103500c610302e00303600385103d00d00706016602c0c11903450b40028104003040024500140c4280100100e81a560300240b9030705d44400c0030030840c0c0545440004107584140100314004002d242a4103440400782042a84c4042d0382000c541548501400030130383c203c560302400b003c0f41c00003400d201d103004169410044107500011584c1c940070166070203485a070000001c07501043d007804203440c070b10b8400c2c140385150008242c03080e42000c14809098550f90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 621514127 1250 621512877 621512929
    0x21c1107170a0c24050c041401052b090209040c0303023007020406171c03020c1504020307050301060e0a0606020705011202030c04150507050f030903120702060f040b0304110316050607060b 83
    0x4506070f5800008c6000909049082070309509070204000c0d0030b821383c0030390182d88580344000160f966010081203a0040c0c9040401e00c0d042c03c0c884000503140c8802c500600c80d81803106d600901c15401c1d036401e546080c070340c1172089002500c60061a00150b00c1a80c1c41035460b41c000843c0034080349140c0b110001c400183c019281d010810b01c01000314042007005141c0104241310b184440807510b1080a440ca10320300c0e889440384e0000c80d01d0082755402c0030b60590300c1c000000c2200250f034050207101d40d00c0c0d01c1e0140310311034640108a884072503c0c4109800305400c15070002e5410016005180d0100c9130900301814140e40b6000d501030032400c803a03001d000c00d2001800c502841010312103194460000d1009520381082507000c00d07520032401121402a25011800c10115940c42c2d08842070000813090f540d85540d280e840c80412580145c40c2111180c90346280100e0070308000c915210450f000707039201000b0500d00720510100d503001020482e800b5546807a003820f15910326012a2101c101905404051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 621515377 1250 621514127 621514139
    0xe0403091a0403020a031e080c0102270105030f332103160512040e010e070c0515091009060b15090a0504021c1107170a0c24050c04 58
    0x45603182141071200030400c81407016860b0010100308403a4040302c079803001c0200ca10503005074910700400030043c0300c000808082e210f505401030540504a2205001c550702107100e1850900e11448106010500500c00107071004640b20071a5404802152540d0800fa20940c68100550036005400320090f40c011000300e80741020540101c00c140c4160860100304010803603039560740180f500a60040c0034400c417440800205000840c40d038240f1150080d00d039625050700c2e0303084610901030306083c440d0320700000312107501c280c01d00704003144c02102a180069100e902000d210ba0014042030103441000e003882117000003071207117400240c000c40c40010541000420041003080c0146141c00309201440a004103a94002c51102155412100103030303900885288014400b11000c620b01c08540f40000c507520741c5103510003e00c0b60610680707540d461010202c031410b80c903004045954001548620411000a03041d440740c410742420003424405c4a52200c880d40250f80c011655682c40000101d400c002c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 621516627 1250 621515377 621515399
    0x1510f03030306120c03021302070c030c060201050c0a0e15090904120e03011509230108010e1e0d110708010e1b0f06070b0a090206071b140f15040e040309 68
    0x20340a10790241011030703125154840c00c840305c0c1c08042c0c460060254001c03400c01256040351096070340002c1402640340d990800031120010b0b8410303c4099420b1100041c01030b0b02440031035404075400d40310250f61810040500c2044140700030007007801c0d00104041800c47d920f003601c0a10451050303000c100a1901c1d2000109403068a01c3c603103010340e051040000400c11803c0b00c0c030065410240001441d0f4903501101e1b10241c41c030b503a498038000b0790a4004101c0c0740042d0048110341600104681c4403401c1c01a03245400c03100841896840c0d000b901518a6082c8585182d6844a08203c1100c1a40d5120701506003110400c1540b41101d0780484820564280d103254140c2c100c80084a80500303125100c00821100d1054042c01080302001000040e0322003442d5111150107a00605070f00d464552340d1800d00c5082c0301e01e000300303200004003120018803100004015403010701c0140135a40c5d140991018030116149002c20950f0b071000610000c81d00300101c5083c90300c41d074001d40d030302c642035031800d925042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 621517877 1250 621516627 621516629
    0x51e01200a051c021e030d0908040e1e0c07030e040c020705010e060309070e0403140d0515030d120902030a050604260309030405010c1115040801510f03030306 70
    0x2000c402602040c000280c01081e00c03a003101546911305171800c1009482c038154071039100b00800d600d2801030304400340408000070b80203544803140800000d481c1e4007140c840100c00c442c1a0b074030261a400003d801c14020030040c0840c18402e041c0548000100b800203010741d5860814040140e002600800c515039200100c0d8a400b2815030b412455414180c01c407686911060151842d008080008039007014815000103106c103001019664441c1617000120010b800d00380c440c084821a485c2d0701c031500b860081200381e0202255120210780c01c2d21201c401024244e0f01c0b9003a641405101d14013400720380300748080b601c9288a4051012901102d0184030300041c0501c588200d024000c0c000c015250600108480c06d40d0400d00b01101407014a24140c4018840700c142d9030780160940240021140c4c0c4600170f80b043c1c60114000340400d07000750600d04201100e00401418200b961005003a410302d01c6510b240140f8800c480c005d18000040c06500001045035100c0d0f40340c0f990702c14040003410b13032500c2800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 621519127 1250 621517877 621517903
    0x102090f01080f0a0b01050d09081306050a02333103020a1511120a0c02010207032304080a05150f0402060a031a12011a0604051e01200a05 61
    0x10410b0900c031043c444240070040880001a81c0c4104400c01603014038180c80e00020303080c0040c041d0300b1041c5002d078445c1e00318001c036108200d030f0120041943c50080040e03840740c05160b4014102203a58174804d00b06444403540000b00c000c0c40e0710000301c980c000b1140091150781480301113a2002010510080704045074071808009018400100d00040c1d03010500314a01500501da10490344110b1101d1401010600502450101c00040c0e00d10348807052014548601caa20604120105000409909070301c11820002c0020740303803a0800c1060710085120352004000041e22030b0502d034540b2065490710114410644250340000d24000129404036001e0794043d109428001050400b940807843c980100c041c00e500b03043d15010840c20700c00e08064064035040d40103140301c1c0340c40d00300c2400d1402040741e1002c2251503008d803042c1c40680d08200007107404443d07000d80039802c8161980709100e601160764803200d0410201d10701e04003401c0328407100e0403030100103d0b0203000c00300c4c0b84c0d14140d494920300030508 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 621520377 1250 621519127 621519137
    0x6031b03070b070615061106161b14150f100608070503131b03020114030108032506050c030f0702011b03020a0c05030f070b01060219080c16080102090f01 68
    0x11650030389012408030212021900300544034071040c540340c03000e00320b5a050081c14040303802000501590004002c00d56503594825506951a2424640c4c0351480da002040b02054030000d085084600c03109926a13120b015031500312145079640022030401c890b060400b1010f114101c207000c41413400101d4260000100300507000024506030700507100444c0145020240600840021b1070303184da01038444122a030001c581034245064074100c40c042c2c0307800d0100b6400200740340082e220400151044070705944c40d0800460034800354060040143c0c06e980441445a1003d50b0042c001402d18018140903142055070705490703242c0120b10005030f0303500620030740840e07040c0300c542100000100310b404902190381c54091398074640807800356100c2c0c1050500909601c000030381500b81124201c0a4207040388210311a00244c0d80e034000132a51811924000c00521402c1540100081d20381c000030000100901c0c142c80c41307448017001500c00d6a0302d59010910130303500041d00d02c25600e0410800c451404c024203003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 621521627 1250 621520377 621520423
    0x5120315100e0102060103110d021002061b040323070308030c071208161404030803090a0203070512030f0a090b160b06030d09090203130206190f051c1d01090602030603 74
    0x3945d030001840050b04c200114094484580c46260414504a8010748000c134520507040d070080d610841254480d2151074a209a01020907203030007110110798108031105265080307841565800d0b12224141324007440748280000c000340058001e148112401c01d88a1f4441c03465041c04148000070302040c00c100b00325401001450000c4180b2480001c240e40740110032501c8028803081d41d8401c1d504041c0442e840402046008200080d58607560380c0300f41c0640d1b10040d5100305002c405464240c00a500d500280401c2c031441c019840941a08401850017403015582c44400100075840210000341039a40310460324184440072041c0c54103d02d099008010050b0207050081c00c01b4168028000351540010201e44010143c1601102194000300215922940c4040c0310b80c42c80c81c0e802443d004140c4203000c0c132029500030400d075078110300c101608013462039840303484038000c1101d0b0305010952151801c1c0111581000d10030b0800c450300c90b280040c0c0e40c1c2090b90805240040c0c0041d00051040f10001c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 621522877 1250 621521627 621521629
    0x807080103050d0c020f0604080a020f0405070203070312230a2403030e040905250b030c030a15080d02030c07090c05041512020f07060b09091905120315100e 69
    0xe020300c840c007043ca8580c407a45400c5c40040c407141c0c2d50003080c0351b101c0c002060100d002d0101052902101c1d108945001a51062605200a8401c100c9002e00507800620021001c64010008020a05100c8400086130f01c06010019203201085c280c07060565002003c0141e0910248034590501c5094810405481c92064140038800b2180c04007e0800c58441c01503915500c503608060b90159001b0b050b40c59126010784d000c4d1403100c1603580a0803503001c144000400c20030354400c4038010310144000601c2d56a0342022031015100070300e40c104c51007000c07030300004500d002440b101060904940c040c642d01c5480301003c074500720307080d04003101c0245020351217041960481c00303c1d012900d00c0100e4130180c0840f0707503040d9914801ca22985410500010787d0760464400b40e00140325080c4110390402c1032404000900c4000b12086403015102c0e0300c40e05c041400043e0325119100c04512800842d1000d645040d09100345400503100c6507850901800d003616075242000d010960407006140c2100c000c90960 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 621524127 1250 621522877 621522883
    0x2f0c0306060f130f0e030a1b05070504020c10060305010b0406140d0f03210204150512040605090c120606030d140a030b1302121005010306080c1017090d080708010305 73
    0x150942d4031518500340c54140051181e00071820003120303204104030391500700207159203e81c4582c24100003c1e8100c00d6082d06582c40a20708402c0e41c0e0030400a180f0b407030070401803000039888080841ca6038852076292180c0046140120b2020310302c60400450000342013014002694074036046640c20003000842444241c0f00c1d001089a01c1d0b4000048000c1d00d2040e0900b40c442c240508613000140c54000340c41b28061040b60014070032035001c00b4150b0107030010400c1c103c4903406140c60b042d03000d640c40c03008500070900d00c0d04a6500b04441c0400c1d5000e070101100051110900c1101c070810070b41000e03040002c3d906c1c052141c0f4240000c14100721500c01c040c00707600c0c0302912549001c407044c5941d070702c0031406607203038a9040040006101c8046548402500146448a10441d01e40822003000348001c11554800e02500c0d0427039489100401602552a0811100c5600c66a03108100580c50341203c40c4041c00c10384040c02000309601500c81d682c040080240b084c54020400400e111500004000250f000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 621525377 1250 621524127 621524149
    0x90f0f050d03051e040807020d21080c0406022e0204060809210703030e0c0d080d0b01021609050a0222090c031806090201090f09320609072f0c030606 66
    0x1e4074159200d41520000303006840008018081508806010800c0cac1040c000000c0807014a449100c1c10350380b41010041140b246000c0c180058101c0500c0301441da1740300b44805c10482546203410305003014005500101c0e0000c2d80480005103804080c030205407030900c039a201000062856a0841e2501c0c007046102c0d10410a00604050391941e001c080e00a0500c008600041c00410300e0900003040d04110060b60041da00d603541302807905103068a190700004046a40300384002210b40c8040c0303445031140c010718008100c1c40c4060307000c1005126136511428003006080880340315130300361400d2903a20011125100e2201040c0340c03820001148a0841c0d20440390403c0c1c0c000008204441305100490b91203107240d0010301008112400401c02080c80d8005010341a001304c0c110344000e904024031180d06e005070150000417078114002c5101d508140559591010050400b03440801c24603d207020f004880100c0135840c0e084441588007000c00c00d00650728901c2d01200200140d04060000589401e68 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 621526627 1250 621525377 621525383
    0xc1e200f0301090507031b08060a0b19050901150905040204090e0d05071104020c010902090a0f0e07050a031b0b0d050a14040507051c0609050601080f06100504090f0f050d03051e04 79
    0x108068048100c60807815250140c032123242940c0eaa400d1642d50071019045114a03644211113108148946040d4024600c0499030010306041680c0d180c008012080741400aa440412070803c83c003040980791800200002c050414002509000030045a41004400d102080821004203c3c0b403010400183d42c0b4088543c5c110b07001a611601222143d004100400c0000c0d0000c081004111611040e50311150903541840000c0c4810003001218540740e0b16035015640d80165004402c0c000f0030000e20110035070411401071500e1042e11210010320036000b0600c1142d40c15191000c21401c1038241c002c0242c51142d42c45004224100350b0364280e107600d07860003014040c0004d08500b851442000c0b805040450b0801c01c2000800c0590802c0f0703031244002d00075012030340301d03034a4010100d000025269208841045070707032074082d00b841d013004090300a40d00180ca5810402400c00c020070000804031004501c680300802d503003208074101030262074004202c412050f11440030981c41031342504142d94030543c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 621527877 1250 621526627 621526643
    0x222030c1707051c120903020901050105042102210703170711281206050f040b010e0408130603050a15062a0c03120219030c1e200f030109050703 64
    0x220303413140e5aa079402084014103c0001c0000c40601c168101e1041c0301a00d00a4510942c540e07201c40040da2540316a1080040c1c060706114030401010406008440d00da100401100da0440b80d00d48074101c1d884241e074440050f405c90001002080f0244003850640c42d4601c644c1d909007070b402e48980303154a0000f04114050702e2040383c4914040e50350301e0f0000e1418501059001d00c2c944a00e182e001e101c030000c20455240b8506000302c0c0103034019914140c07141e9130007030041c26aa030901140030200407024008881c1484207001d02564640d207454120082e04090380d0024862400c1c40c9100161801c00c2e92107c0d0360b820000f814040714ac0c0c02000c000706009030201c0c20380302842c0d15054051230220707080041c098455a00c0d0110401c0002806881c0001441e8200c402810348258503801c8003680003002004070300120b04d0a40000c080c810701208681c400425443d12a1084c3c495034482c07410f0503039401c0070007010080c2d0300c010303e030594075011242002e170000c0180d42e00541d14a0f42e2100d45000283c1011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 621529127 1250 621527877 621527899
    0x6050c07050301020c070305010e011109060d020f0f09100c03090b09060903300f0406030f020d0e06191118030f0d020d080a230702010222030c170705 66
    0x2408000c403100820780a002151349980040e070407500e401c054002104d41c1d5003441c4e040080203405025015880c0c940da251940b4054107001000081d920105505581540038002051050441c07009000101c5550451541d2030340008108484030000300d02900c1408010079100c00400e44c0300729107030151100105070756641c03440200001c1a500030b2444503a030510a90110300b0361101b01282134001423510303c00005942d82c0c2140909801d000b91348814031000d10a103c2003141c98840d400000c00c00c0259540107140c4070b40d4101d581c0c15a4000c1c0c0007000150300c51403d1084000142d0700e040c54003810000200160880b02c40b41c080e4034031601803400d00c00c2619040c204000e40e0f00340107041c911500c1c2022541361107490076020f902c0c0c12150100f8004225291b00107491211607008844c80c100005007500700b070030051b11110060100241011045650912801e0180c5c03200e8007403209442d10001c08400b41e0307841c514004403001003e400c25441e6001020342102000c01c0060848180c403001c41d4419620 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 621530377 1250 621529127 621529147
    0x80f090106050619020c010c080d020a0507081204030f0f0207140126011401050a0807080406021e040e070507020102120313080a050d0b06040503070e06040207050a031206060c0b010605 81
    0x24140c103800c016401240051502d01016160104d1880c451460b000d84140220020055402481c010f0340980400340803c4050000e6000354000e101d4900d0300d0903c00e0802e00c4546441200b500800000d1407aa0b0300da0f000c3c0300034140c0140c5a81d800b5031440c40c15204422940000a403104418880e2058090105081402070703801611450413000c0162035205000f011030f0681944a00300b0300ca600091480c0a441c00e0481d4407900031030b4010b0303040f0b0f129540c0680f55150200c5071500010b0050740d009a0922518042d100308801c00540e4103d50b010141c1c5403800c0400c880591040501090180f100070001a401030f40c001c1189060314514040442e141d903101505102c000b544071000600030b0400040c0610043d4102c00a4009110401c204004031307040708051100510642c0102907065203c0b010801c8510b40701009e0395030084002c0d1015003444038aa847c145000c141d000214041a1646001e44445019105a80051546241103400c80c00c054468660ba50418019070040000000c0c0400c18 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 621531627 1250 621530377 621530381
    0x9011d0622051203040b10140603180f030f0702030c0f1807020c06040e071e0e060d0b04090507030b0f010b0304030503070c020a0806091005090d21060609050f03060403080f0901 78
    0xc00c0c000000140d41c0d174078040c1360001d2028800c03960b8200d0381c01c00c2c80c400300740302c0007261160440b6100074040516540b00c41c8640500354040540e0480e040c23152200d9201298000c0c40603020209550950039201c120600c10542001074148400d40101101101103080b960380550541802c0f0f01840000045d44030b0380c008030b04182c0721500320758000100040000724410401407551140c1d140d684d448a2680c10680144461000d0008a9000901e0040e4601d0702d8500b5500604880007042000500b180c010004203003561070000b815202600810000c01c1481041102d660b4003845c0a2944051503040224110a901001d0000784c00c000d000710014a449000c0c08408440c19001000c26001503581c000c140e555400c215082c0c942c50248542c4aa429003071401400d0054034140080c02c1e80100350881124800182803041c40c440e49403c04482c0840028800c040c0030309600d0303840034401d034180700c1401811240800300038041e0f4081401c0001096200388082c0c1c00c84004154071289440358038031180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 621532877 1250 621531627 621531643
    0x9020703121103011809052104030c080706020d020f0d05210f060f06070c05060c070e0106080a1b05070b09032110050d020303040314070e09011d062205 67
    0x2525490b11003204454401d42c1c02960403104000041118110390705000810b8608084005000340e1281074120080d0070b141c0c0c0601e2141d100700342d60380e0400f80c0d81c0c0c9403200985096484642c0740d40205005004d01a4140318062023290b180c001402e03030901c140311081e507901c0a030040c00d00308003000c0b42072240000020404102c60301a4003014049050000820b03400b0f04095661510a807074000c080013281c24000180d840f040c3e0444503001040e0b00d04428070000d46d11510b01d9400350701400201050304c0d00005800d5010f030016a44070021842c0c042d0526080394264000060081480700b01c6901e03c0d40e2001c04c036503040d640410094510b846400c042450343c0104180700240055599049040c00c100340000da105403501c04001d401c0e541d6540c03d012070f0304010f41000c3d4140c2c200700003d10101f000c1c034600c4010010900200d40c480b80d83d5048004031030b80c041d0f950138203e03511042140d07010084000e88014080104015042d02e0505601007a0a501308500c0c2005010350710700d949042c080c0600c001e107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 621534127 1250 621532877 621532907
    0x1d07030b090c100824060702091b0a0906020c01031b050a020709020f130f030b01120c050a1403011b081302040912030b03060702030702090411191503061a0409020703 73
    0xc03144903d500260a0500445010114905038440744010180c221480d11141c40c0160aa500c0c0c0081d54003031011040b4014800201c40c0b141d07010300d040c3c2645500091201212075a45e4900460421100034248820030030424101401d00f41c00c07a401c0d10508620554001b20303814556507e4014420503030500c956944103018191010079014461440c2a0041c02d200c402c4110703441880d0303110001601c0c84170260002404140100d07005010403072144d4032228916010744404000700d0b56071000280300090b1500107100c0e1500d0304000810f642800d0245445207421005440407444141100030442180180000e4010001c9110041591681c0d0b02c944051030f04600e4166544800c408003802500d4600c601500901ca42c1d000103081510100c10b0b260480c1c0c1c000c068082e00d84881e105c0d140a4840205065070015010710303141041002d204504004100300401d44030015010ba5018048910035809012400400c1180003004401c92080b5400d44080c0c000040c1c586810b828229501ca00100702d0b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 621535377 1250 621534127 621534139
    0x130c0c0506091b0402120a0c0c0b0106021005060f0d0b0601031e0608120f0406051c0c0c0c0f0302010c02100e090a14130f0b0403020c030a0c091d07030b090c 69
    0xc4620182c0105080c4042c1c0c8240c415001c28200300d606004c120302c10b400140c01c0201c1c1c0200407544074501074200d00703031a04941c9000101c10320b440d2100c229812080c0e10050259110083c034409504081c0a40795101c0c1049840040264645000c102141c420380c00080c40b003014080003440d940e0280e0300c05051b02e400c0121007030841c0640c0d40da2000420503806041582d125110441091150400c112014151000c04644c2003d1504809541e06d4010442180101c59543c640d42d0300c0f40d5051107030f2104d400706036903030000c4042c0c0360030000135001c840d401580314420a40000d1000d81d0b0800d640350a9907505aa981c0000c11f40658102c0d005000b24502d030b540008844144110603c1c1a0480d541101a44008009984801d0048050811601402000054020040340101e403010f00003a0788140a030041c0c1d255042e1034000281080140b0008607039002c3c2c0d00302d084c003225a103441090040260354105070001c0010384c1c48103a44400c1403200609078014000010300555044c00701001050000d82a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 621536627 1250 621535377 621535381
    0x201120e010212090708010225020f0607080306010909150608090c0411030405061521010b03071215020a022a0307121505070905011d060c010c080c0702130c0c0506 72
    0x103c001c850303c15525804d083c458140c010032102418400c075640308014042640d8161041c000858202d44d541409907881104020b07035440c0e035110040101010f601c40c03940241d07640b07082c03070000d407840e50b868000414a80c5400003c001d04d80c05194114140c5d21642840341155944403d0a45001c07481c00205030481d01380080d407402030f59420040c6000394400d000740c0d0101c0d59802515900500000c0e00349600c4205000307918500306030407922030034a08a95001013449507002c030203c0c3c03414100f50301c0106c00c18009140c81c42030100b4840034021101c00101e0540c0703002c424920095407883c0d41e40d00e661a1445010942c0300890b002420004113620203002d03121216951000c88200f0954504251440c611020884500c110148201d40c0b240102d034845404080c108801102c0400100b442c0d004002080b10080d46203540c1c001c0900303400202c600000c503444104440046c1a400c0240050041c600c0600848005039038045012002e50364807000040d20f09220502103410040256000d03000307010301c0c81 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 621537877 1250 621536627 621536647
    0x31503050109032615010c140105010b0912010b0d0615030f06020d05070f0f03050a060b030c04030c1d010b09060708030a06030519021f0917030309061b070201120e0102 74
    0x5181c501007880f610200c9810310303441010010041c0100c0700c190a4510010b1003011701c0d03000d02400d00405000d9a5811401f000300c40130182100c00a07003050300350344801b01d4488402c0c54041c50605240300d03040001c0c4401e5410201142203007040da02c00400880c0c55905685001d5100324030030009580110040100044c01c0c00c02c0c1009602501040c5441424080050b800d2800b441c111140340d01c0c01e03a520038111445902c2180101b501a0030542226103c0030001202d80c1036601542c051020b41e41130b20740c1d4514605d88020700055582c032105400711042810748a03400c19081176411150405c024035580c60415002829511401d003004005450200501110018a521003425240b0403c01c4405404100c055840e00500e0301d00002e61000043c4010176544e0702d19268840003170403500340301c101141c40e042060420404484c10001c5a8070100422101c25010050b0540040c032258100c0d8141091b030300649458821440b0280c1480744604c026075445215502c102c0e800b803440c000031511102141 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 621539127 1250 621537877 621537887
    0xb06030a0606120b030d082a09100f0516020301060f120506090105091213050604030308160804030e0f1504180b030607020d081803030703020d150501090603150305010903 75
    0x1000d1007001901d030400056000d403d900c9561031020300103004007181055400229001c6030004c0085010300c00051404240c98a04200c000420007130010031500e4a400e5000d100140e070034040e00008209099120914954110742100e058131841031020640c80800d0000c06d014001d140c1c08040c20800c65440010840d6500c0100000c0502c00c0c01624007584401001509035481562a201a0f40100300f449000c0d0100700028450300ea0100b401620103a51240040c026412550065020441000c208100c882c1c03031740c40300c0d801924607080c04501400c0580300107210341d140383c43d02c9001e401d00241c4800d20395a050f424001d03420364802d11958440d1500d070204011b80c103c0040310801414038100703414620f800f0580611503541175005000590300c540c021550800060281c543c5441d10f09010344400c2c105000441c0302d01c00c144c07409a41c0f850344280000440d215180601d1641c070718070380b051110b80c2c0d0101030700c012a0340c1d520380403e00c80c0040c0030424240d6010303400204198608640102016000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 621540377 1250 621539127 621539129
    0xc0b1201150207151101090b25170a0504030509040504050106051002030924070f1b060c120827060103030936140a0519060b04090e010b06030a06 64
    0x41405a820554074041c0e0b070b510740a0151543d50b03842016401001031248551084040081d0008920036019481d04201004150b41d500f11140303040c0c500955180700d0a080a10340c0c0054078084941d03c000c03049095501034086c104140542c0c44001040601d03104500ba1740d1501720060040000d030a1518086000300210301c181030240e0290f850300c8c04c0083c000320545200010140c5207070381007428100451201c40c0498071010340c041040c424000410090b504840700a88101c4041420f180b042412403d0707901b81c1e40c060b104004620421800299041c0280032482806040584c82601e5807030170041e210410502c25507045600361901c9030885400500641200e0094030341300c0020f41c58184448070110f1040c00003d2500c504180100e001d440302c10015810b1001c1400000d410402a80d40520484140c42045c09503840300d06000514640754003a440a650007901003003110300d05410120306000c1c91140e4020a50380f0070084401d40c03400e4101081030007004154a0351392070008050b070024525 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 621541627 1250 621540377 621540389
    0xc030c06090605100801060f1410091503060e010509040f02010818100203180d0f0516080706020703020106170c12160303020303221e03090f09060801050a02040608130c0b1201 77
    0xc08000092424012350f0400a0300c80c500d10114040d8001000d01c880724421501a0080142c2d0482c0091010703030000311400d0740115a0b9012400c07901d00034001501c1c01c01a0003c030310070400d0700c0c01e00002907269141c1c5030309540d0a090100d16969401588405224800c0e00c0e089030f405180242c41c0203110a0740110b108480511500844d00e006003525030355980601400c00204000c1a61046018022005072105840902c0c10094041d8140d17a8100c3e42c1d04188011180290086051420145c080c0543c40141c91803443e0b00042d80c1d01000e40340c0d5100301c00ca031924012048802884030f0110103005d42c000803014410a9110547d41e894007c0d90307070340100c0e000d00750031001c41d51090700a040c503d01102c09030340000c1002c6014610410b0100220074690b411001d116903641c00007040c20703020010718001d20b1659400503200345400586802d43e8001040140160300c10001400301c3c40c0c00015054000c1c60040c02011154042d192a21103202240c03c140070509010a0076000625200c1200f0f0507502 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 621542877 1250 621541627 621541631
    0x1519020601120f0308040503091509040f0504020a050f04020415020a03020609060c03010e09030721090b07080a030504080d060e100b130506032e09060509070c030c06090605100801 79
    0x81c2e200652030490880030401004401103032030690100e48205112a0418000c400b56807800e008400090020700c03c02580c04105140840c943c0304515180c4181d840b0540314078828051440c01d940003074a50242405094494070079010b41c0075058440350706a41c0030b020340c41c2907603400890f03188003c3e49d11200600f04800600c640c900240d5442d8000c1490b5004955520f10282581d0a0140c00f07620100f00030605011840244805404640e00350360908944104405405004112600090091403540c0001221010420000000030410710440340001450704e800129600d56113030110a501c6500080750089090200104035507080c540710340d00925403000310014545e0380700e0b00c0711024001e100c118682499510820805400c086008541c080d200b1100d28044004100307281c4103140c1c04003010f03d50121484420300c0400614403d0201922048034542501d1070812801031402c074640c5401800c00ada590018410040b25810055480d07601a2003480f003450041448000f400280c8188100c81d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 621544127 1250 621542877 621542879
    0x402040b0d030804021c0206030f09060705180f0411030a1a1008040f080d0e010b0f0d0b07030f0b06031612181707050303090304140a05010e0f1519020601 68
    0x12820072060720030140d0549800c0c42c10f980d56020002d081498045418000220000010050750b0725801984641081000c100e2142001c034140740c0723001b04c0241780d0b00c14070100300858090403104a907034034111182140d10a0340c0f00204804103001d441d008640c01482d800200c1401841e107a2500110036200c1502076410034008038104010030301904150741c0022414000c081404500e501e4410b000c454000c0307103e1803419a14091840445003044421001650744040c0c003801494480408580001c0403100407171100300c1500d46210807000541190149a95030880c0000714a840c0c118154200c0020102500e074a422011b2440355840359000c01c00155006e01c00c1d905400c500d01c2072020a09100b0181c0d010191181d941802c09800351034a10b032220414441003000900030401144104051000b940d00c507480e0011000c0300c0442d4080b11403007019070749012f01450740d000364405031b600412982e90361f0843e80c1d8804202d50440003407a2074044200090125020005108035050100c416400c6850326 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 621545377 1250 621544127 621544129
    0x7120311010506030d0909090303090215090103050606030408250203010c0507050c0a03050c0607020105120106020109050d080f0705070840121101020f0f0604210e060a090e0f0402040b 81
    0x41d185075076117140850800340b014010b48090781d0018040a200e07083c00100086d07144c0000e01e02d6404103499072440301000942c00c0d103a50345070160581090061b19064110309190380d8880050007810250b040400b00c0c0c40e030b0012280305400400100507000f600801080c00c00f040c0060090740501c07c181d03418460038240007500d04104411707070103d039017017406044109131007030403c055035214440aa04001c01402003e4118030b1400b85c4074001c215580002581d90320324900030781884010708084060203650b0040200c81c6d000d11504d9035000c85d5030720f410b070b56419080c030302078825000303001c01c42001d0006001c1600115130030b40346c07050864000081e0340c01d000761341d103c2e12a401001d03801010103c4100d18003c40010f1515880b9248461050051b40c4244544e120750074038080308082c80b45c40300e50083c0107120920260303800010140c5446451a5028154440040d050002e8400b409005550019255040c540700700341c024090407481415062604083c0303290200c80c0d10598081c0d01c15482d02e46118a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 621546627 1250 621545377 621545383
    0x150b030309030d050d06170615030d0203040905040c123e040207020a0503030a030c031d0604030807031d0109170319020309070b04030f0302010c030513140712031101050603 76
    0xa071030300140200303071002c1c00030f2003203403a500701003000154103413900e4020a189001660b50340d4000030400c000c029500d042d0540451342c4d1300841300b8030700a4008590340030020341c2c0403086038291212058041071548072071400c440c40400f00c0d40222101c140e514002410030000c0c601d418041a00142e110045140d42c41d12400c2c1c104880070f91540052055410841a0030b09401034a08180010940211350b0f544102080c01c581c41628031000080d0349114035080c883d0035100c0c50f2003070200e40c540380fa01850004089035981030094006004d20918600003500180b1980000b41144076400682401c0d1800c0c2d140c003800f8103d516000c0340c2e420a03c800401407a801901a82c0c41006064040000111060450b00096001a14000b85802004004101458048010070066120307a03a8644081c00794100203003118000c001040030142000e0074498450510180190201c1e0411203618241c00c019040500d00712407076104010b03c080c0e0151030014140c2044d0301c1d039105040c0c0c10007441aa9180006c16072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 621547877 1250 621546627 621546637
    0x30a080609060a090b0f030a050a050114060603040605131209051305090712050703020303160b0f010b0405060901030209041505010f0305070818031e0910080405030f03130f150b0303 80
    0x900075000540c1000408001c3d041416801d101822031b0105500a00c0424140592101c041d1410b50141a40c0d40401600b4402c0c80c0c1d084180359000300360750500900203103d512001d080038000300e4944005c0340320300b070001d04071410140c0e1104034103d2021040d88050005c001034850b10b841501036015030810042203009851080c1640030161510f0b0707040c004840700981c2d02c410b041c0c50b5482101d00202c0140c4003000100740c1c080c5a6808501c01845601c1c004840000050480f603040c01040010444a4009000d40e41030f650304507a403039110070001004a00070700408a0003540304c1c0c01c164501c0c2540740780200003c1a01c1d02aa551440c1d45000101501680e00076281c0c1d40000e80c0540002d55908a0f0400f046003038020b1405603850301d0541d0449040440010701c0c00d61a0074000038001307485103800d0707e40e09119021070820060354074040e02c415441e0701402c550f55101844c000001030740f440c41c20300d02030601c5920881c0907003140b4007820711b0640d603400303a4210920146051010041860001b095035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 621549127 1250 621547877 621547879
    0x702131d0d0302070206120c0c0a08030132220f0c03050f07090303120e16081c0503040605220609120e030d030f0204120f02090a02270604090905030a08060906 70
    0x2a2800e0a007e841c00c03103e41005080c0c0e4480030040c0a00c1c00b0645060007030b60040e07409400074603200e50500041c0e0082c1e042480d103880d030300300c2d40500d0201d0001031000c01100c0e580301111a841404060ba0090822400d0003c007542032a2408101648102c01ca900685540c0105c2c0d504205a41e5000000040208161b0b8400c012541488040000030310480700350701c5c2c400317403100c002c181c9040381a2650300c1c01441c140d0b200854601800c0c140030501080004130691010008045050f450060002d00203100c05800071f401e140c0c851002800340c0a01c80707803118420701c000c2400d03000352444d4180a00280f00700740040740c0008025098140c41c0e4480d82e03035907000c03a4000b0082c1c048908004015001449800010304450380c083c400041d60f00769492211081c50702a41d124240745c4100e10401a0060008000001c95841842084106038001c41d01005c040003003610007500104400c0000d24a004903030160f11040e0502038a03004004011018020551054a400c00d007070700c901041044000702201c0007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 621550377 1250 621549127 621549139
    0x60903110f060d09020d0b090d0e060f0a050903070e0903130503010605060a03050901090203061501170903030106050c19030c050d032723211303020103020702131d0d03020702 77
    0xf40280c1d41c0c0c0350348141da115100403e0610b00c6801581c555000300350886844070544c10a070440354220b41c00c441100c030600c00458000e4a09083c1c503079041c0c010b00500c00f41c0f008015012035811060b4408111620141480300300305050b6181c40c00c5170696a80c008144880c049070103c800080d94101402284103a40c3c00030100c03424100d800b03400f1402440c008101300419901c030844400541c0781400090b0140b0360300300c002a400c0642c040054503200d180340d20812240d864404000b24980d001c407c1e641515500d2409655541c21688098a40751111559000e038007031074032142080607017007000300f0821445802039451071701304c0301d1003034003114140303902400d4801c3c020000d918624040f01e025404607109007c036119140c00041c44000301c0003118100346180c0e200d04065034411042c0c642c80c1084981003402989081e10707004000101c082140310090505402044e40f100310b603921604285240c050301010000303008504d4a08500c0c4154800320f50090040c0c503000600d0501c070b03000711100b02d5000f8102d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 621551627 1250 621550377 621550387
    0x10020a020d11010c170a0e011e080915010803071104020310030308060d06060e06180112080717161101030c08010e1308030a0f0c050702130f0b0a060903110f06 70
    0xa103905014030b405005040060894040380050390183d00e1101050000800079141d0503050405400c4250126880d4184030020703403490b00d1240308407940107507484140b402c800e9a07120890781600d02500c032000404143c24103000445e001d5400009001324501550844da2482c51100500080b4402a609041c7c0c40010390750600c003203030069446c1034004101820180070b010341520303904115041504580c03815414603003800720720302d880d42141c480c44012840902040d45495180d0a411030001c0e0010b0080001140450034030901000080b1030044001404d55070740a81e20001030030050302c031030813500c01507007a80c0810154844c2c4910110000d030f41c1c84002059003041500d105800d0014845119601501c0003103002076500d03005140580100310000c0760340300701d454a030b03016a540c0b00c040702c0030040c0c280465400341e0f40e80d00007034500039019200022500b1101500c580540030340c13030001d504042541c100203081503001ca43c6400b01c9019480d0400641c400c3c80800140010301103c4e15070001c02480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 621552877 1250 621551627 621551633
    0x4021302072105041d0a0605060c0703060c030212010b12070207080d030b310e0109020105090118050a23040531020406090204050907171b0d050903040510020a020d 72
    0x4414102d07031595040c001d04144e030342c09040798000088001201215100024407441200c0d500408000e032408580d410b04012140745201d036590107030320011348082d480d580510307a05030195044840303982c001c01d4411261740e11407a410126074802c0d000d103a92040c414001854061000ca448400e440032a4050003003210612801c40241075500030701a030105024000d00059034503500c58100100201034055040d802030b0070b5800484611f40340901240c1d060242100050713911000300c9400349402d007000941480030610300700ca410700540245401c02e011400104400c00920ba05201380c2600341d0000780c2540c2d010040c032040c4c501c180d07441e0000c4003d40b0f03c1c041c0541b00c0c0c00120504102d14a400d0300b80c1000a03000a010341d20303039900c00701d0716130350016060181c5e06043c00c40903882242802c060003070080d0030301d21141c02c1758010201581c1c04c0381701c81819058001d400c01c842900d840c55805110508180d03240b91384076446489024850104920200705160000c1800302d000c0f40c0041880c115910076807 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 621554127 1250 621552877 621552923
    0x150709051201020d06060c02011814060c10110d0b1c260a1701090507080a0c09080102120f060a1d0606072109060e090c21010e0402130207 61
    0x100e0030071040e54003440b03044501d00c0380707100c2c4c1c40c0104a0341e0740c2c120300205070380005001006107024012907908030100600512a2003901c2c41c1100b181501c402d03a071642400202ca0400a285020740a61400d00d401d0704440c40d03101d4054043c2c488132000400018901400b0401c0c05444e260b6200c107049013013020701c4042010009280003000401c866101003100c00e10990011b540300700c0403180490601e0009840e000400f00001d409804041000c000c0c0c0d042c000d8000d4050b440c0104100c800a485080d0f00e55a10302c1140e1890080007035000954507107100c04d80450f41c908040f1550020103000200090141c0341640800701200c60405003041c01c036032044d4002c0a4400c00400f2079403c44400c00c0030b04002650740b4070480151142010403080c04d043c0b407000806004490f4001ca04114a400c000c2c5543d80e658001076801c40c0f0007030580fa0384c4103801c1e00980380840c180c0051111600c2420000036049402004441c8114401c82d02e6002030324000398820100d018420002d02601d04c42012843c191b8145 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 621555377 1250 621554127 621554149
    0x4090c0b0310030c03030c0303060b0c0c10050d0c030b09090c150c07031e050105010b03010f3804080f0109030f0e010c140d03051003030c1205090a0b040815070905 72
    0x10409102c400e64982d258140080c0c20355008400050071841034606159052080070044e00300780c2107181c50485d84c9600c0076a2108545039040c8034000c014203001050780a00c01302d69880315005401d0125040100d4040c009000c1c00f80d03401e0103400842c0018092000206880804a1004220003803650310925003d4060b04801d50891240c0b240d0355010000c64042101c190f946194502011491102d41c6080d03802e440e010f80c031603810080c0a00051100310364264019003694070020000003c3c044940301881e200046090940c00c195034009184000391140f001001681d03121401c850607002145425803c0b1514058054006080051580c0c01a44540e11200581e101458011b001030080d8840c0e421403000d00b4010022a40211094010650503009a0354004130110300541c1d81881d603140a071805c0d68014005011054200c0d501140c1d41c040e00030742d20801009450841c5c2c0c0b0b0b4075203900e030b20594803034014a5103501c542c881a10002d01c40303803c404d02c02d14070750f603542c105186840d007401901448 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 621556627 1250 621555377 621555391
    0x2041701051e1e0429060a05010f0201140109060e01151d030c0301142d0106030b06130b0301060924030f021b070e070503091c121404060b04090c0b03 66
    0x4403400e024450101d00003441c0128003034030380010030810145004900e0038017103120068a050400801542d90784013103000d41258001e0803c07098100b401030341240103181e9420543d014100d503000210303582405070310090a48200d0740114503282d0301c80c501112103c00d103070041070010318200f1800c070401e068004103800303105d000750485260b4483c00000a0070344140058000050741c112081040700b811401c840001c600005001017400300a6135282005404140554002d1545a0107440410f4840380120364400c0c80c18640985195186c2103030300c00b154402e200d01c0303000074818480800c00d0307508007002d81c000c1d50140136201c001342c4100c88190042e01da00703001e0180041c3d0074013544500b008107443da240d0b42c0864001a02a0a0801d403401148000181080040001c04c5c010400c41000000b1040042201c000d2021080c144454081303c82070090b0b6404c40c2c0b05401c107150740c080400035005050203188a04001c0c414144000f040c0400c41e14000700240c80690440c60410003141400021030704251 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 621557877 1250 621556627 621556651
    0x6140d023402030d0302070201140705150103080310050a0605180f0a0b120a151403030415030e0c0303270607060c080a050a290a0e090102041701051e 66
    0x40d0000070310600c000c0c5418100d001c024400068011460140590404401c0c00c2c1000c6040c8592a00024040c9151810150380680b0001d80c440c01e006d07040240d1013216140c2c000168140d82c60b442c1601c466003081c7d0307400311040d070655408115071801c040c13840300791b0300550b4500d4148140c00c0142003017000c81500080d0000031020700c01226440c2e01c0d030b410014181d020035403691014104070b940034821004103105046840d140d0401410304820070b000b021103607034000381110300c107484000a055200ba540301216428030f1542c08110141c04d50001c0d90300846400130744010f10603600c01c2c5504c1b8410040c540854007441c40c581d4064007641d0a028010744405080301d402d005003503031184204c440f0304801c82c01040da558204000890039002d1260300008024090280c81d05000c12414074122138100c0c082c0c0001040000c81d0301da2141000840201480d500b8120303d4204010014000d6100f40100100c000800e2030b09031038a00140170b07840c001c01c004440c4a031410315141c207094039500054118181c0b04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 621559127 1250 621557877 621557917
    0xc02071802181003060e0912090d060605040f0509162405130602030301151d09060f42040b07050304030b0108070f140108061012060b030a0606140d02 66
    0xd240c81e1000c402828441e1130008242c0d040100d861050742d0000c1c0316038003d50000c804112240f8600c42030790781500c01070708c01000e909020303d416030290407140c2040c1c0e00a85425030411040480f42c00c154000c851900c240c420012402100d001c244140e4041d40c060307a82c1e070828003a002200c0b000c002c90103950318070b401801c21080303010780036440b02d46a010038016840400140030b1030740480b01600083c2881c2c02c040034405000380c9003609202254102910500841e00000d03902d848005054400c044001d20b0021140c0100a0004400c82d00c89054a0003d050210f0020000c1c3c0190403442c040801140b0280cc1615090030142c040d40041c0342106e40d03000c203200020004041c079800b14042d21001e409000e4407030904108030350401e0395a000000c0c03402600d090050700d903048807070550409402d40c1e13810904080d4440503150000b00c84a400030803450a8000603070300300004044c600a8030030440174044556660b004850500c0e510418008000c0c04100b41c00c250600d55004200c140b004544010f685 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 621560377 1250 621559127 621559129
    0x31b0306010e06030c0d150f1505160b070e01020c0a0509071107030c080c0d031d120a0302210307091701140c18061606020c0f0d120c0207180218 64
    0xc1e041a40c01410484002c10041440122401a004440307c9940e820400c2403504400b5141c005852103080254010503c0d601309071445082100c46c2c174849010502c0c0b1001c1e06182c0b89000c5601181c08900045158106007103642c408071707040b461480c1c000c0400c0c1c200e500740010002415409455031080c00012005e8040c5980148280d00007140070f084900000c61a140485003048049a4414862031141401000180e000301c282442c400070000340c0301030941c05001140c1240c0301c4500000c0240710b003044440816030300040a805142074801160410b52900803113085501045da42c82011a00d058024401c51051510041c4402000e000115651760f41c4440440b5180003035604440820000520058548110030291607050054030610f160904114a094001c41503890042400d500010300807034100d8104214001c1c1900b03901074401203038400303030041c0000b140e180b021003c0ca130601345220492400445c0314002c481c040c4c2481d80c6a5400d400d601d40003580000891090690002400c0c082 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 621561627 1250 621560377 621560389
    0x8072618010c0503240d110109030804080714090f06221a0315010b0315030f030c03030403110105060d02010c1a090d11011e0b1206040b040c060302031b0306010e 71
    0x4880d000d4a82aa40303050030026090b082c002c500802c0c00d1741131802008025500c8813607440d60b001c1d8000760504190400c0c980100c8984082da40003514101010801250b800360100d00001103e110041a13000041214280800098111441d100c0034a44000103225418000002c000503c46882c05646504050f45440112410ba40344c00d0901c0d000b490801d00107013820000c0203044840b07440541c06640c0740c104c0710f102910005182040149440b9016042c1d41c60402c54480307281000000d90f61100711090b1031994a0300200d60039030024004484c6403401c03003010300ca110302904024045842001e07658006480604e04c001040b1507020120725403180340300d901d0540a000301c280401801c00342101c107000070807211210601d1042a4500150b007094044054200f0b46801282d4401064001c90300d400103420018111140d155070040b0800c03c000c211100311018030039881244120115500c5900071000c070300044504034410509000a60440412080070310340c04901450040c0b500380740a400700b00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 621562877 1250 621561627 621561641
    0xf02010c15020306120f1b120a0506270703061515120e0723031203010b030108070e09030313080405060d051603051605070515070f0807261801 63
    0x1070110360110600201d450001e080b500c09204540052074015141030099860700101140d01c031000500300140300da29200d01e005856030309175090a40b01c1c140002e0510580f54401111030046041e60701d1030050000f402c9a5a00340c81c0743d06138000b040d22034119076951000b0b0181800c0900011014403001408a8860b411070002c64603c0d919045000c0c07400c000d0105494074180021390680040c14140190214201c1e082805803500100f403014068940c0070030304cc1388600c0800c20140c0b00000c000705491208100560482d20384500700c034075587e900c0d500b42071203110a4890f40895041000899148078503110f5001444d4008c4185619103540c481c001041340d488240c5103c1c440340c49500f0400c56810b1480711800910740360030300388a84d151410380301d01c45144800300001800030204010040c0101000303172030482007040d4000c0e400c034240b000024011200c50038441d00003a00150005008620a001600d00a4540b800350004c910706031001d07684000e00140a100c4804a40c02201c00072002400750308 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 621564127 1250 621562877 621562913
    0xd1706041b0314010e1303051c020403050f0c180a09061d0c12030f07030c060207050a230f120a0e0a030605061507020d1401090b0901020301060e0a0506070f02010c 72
    0x1089442803640381e1243c01c050307110300394034090302d41044901c030b00c5000160101989031030150b6482081b0b008218031100c074102118005403000c100401082000500c00d13552903080b40464404040c2c0408100001d81902c00307829154030301c07501042690764540c000c0070841c0d214240100c0c2e45081040c9202c003054100a80c00440c2c2c1c884500b0240c1c0f8148081600d00e081b004001a52a2400c07500304400c55119120005003001050641101400282d13410b03244215404800d0700c410020ba03080102d901005407610b130201c80d001c00d84080c201500080c5a040038040303003015003151104080c94030300e25000929218180040404141443c1d558001010302540c0308d003d000405003413060a0048000c404040c007280320900700040405a9a07040b1454242507100c1c5144160840c1e24850a0243c0610000142141e40030030601c40411010b40265042c0c401a984803148010075404010302070080f8480d49030001010000000415028005150b4090040c1080c5108070341590b03400c081032407510041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 621565377 1250 621564127 621564131
    0xe030f010c1803020315040c03050a23010506030a081b060a060602160f33080708130305030606031b180a06050703270902160501050106020d1706041b03 67
    0xd411882d070403000070400341c0030706407400d0015421540401d40d614282d40d1603454501034240083d08102032005603a01540c4d0000036102010f049281c400d00c1d00400030307900b4981d0340c110018944c2c0744a051140c075114880007001024000e40070345440340264846102e000d0300d40319004c032100d0380071000c2102e42d0141d681ca25000a005140440003810441c00c5224041c1304045024100300c481d031415125810344115101c1c0079000740031807a002410901c4c180c000b11b0f40740c0685403a007086c0b54100c1840c6104402580750201c69a03900c40c40c161055400c20390040106000340081201c0b03040c01d1001d0b40c2e20005144550180c1960404003a00c41c2e000242c40c0c50b045055605000e400341007640190008189904001d1300f407102940d0701400500c0c1400030301118034140e42c0761000c501203030704410008000c1940304542d20f0380081403400000004000684507582000300010340d10748002002040307000c40760348103a200c0311a104109240788019028560181d1103054a0001e1802001c010316001d141c1d03180 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 621566627 1250 621565377 621565391
    0x20102370e21063405030901181a0901020c2535070e010909050c090c0903070f06080606160503030a0203010e180706030216060e030301030b0a090f020409030e030f01 73
    0x8111305141c0e500071003102221501001007100740c4507102d1181c01e04c001d420055160303a20121746078010700f002100505011051070490f81809412140f843e40207002d280c07250300ba41d5541b01054242d108a84001d44e256009500e42100320341220102d0703803108968107840c002d50b80c2d101f00208603516107915145210500303030382c030450005018001880540081d00a09000e0b40340522566445d0014418103001700d807500c1c030721010404103001d2141d24110081107840c2500309407050200c190001070049000341b01e00b02e0049040f0048416480482d50243c1d54411965103140500185420a0311460f01d03081820f00140000341007400510b04c10607880071b00503141d41c98000c0d06664244098064048008005003290303d42d0000710f11202074996030300f00940d0313503400345c04040c2211940c120040e044e145840d00c0c040781c0540103c0118100c0e40034a07544030803500ca410b09401154a2804010103032a2010b07124401410141c01020065010b400e2007207540e8181000700f03080ca4000700c0703030360324607552640 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 621567877 1250 621566627 621566641
    0x51923120901050112020f0607050d02030c1227060706180309050f181b0c0106050f0628030608190201020607020f100e010b10020102370e2106 63
    0x620181d000030000001c0c081540342036108440124403980c00f90042d022019404080c0d1285004c4411107580542169412401408c0080d2a0b8104000c55070f0980900c0c070300030031564660003d643e2031026421540c2200c0c61500050b11450007250a140d411100a210050210b5241e105213500f20006903200321011245142c020031098103604650b10419490803400e4460722074981003101000f02400f21007060301d505000c8a0701080d0301101c0100d0160010326140c2406064002c2d0080741c0c1e0540e000110030050504008136809120b03030305820001380c0d001046600070106912000f42840c6d0074002455515171a200f4200600604607010f0f00040505020455a0402246500c02d4003440036001014001503015103a14000c1c1000c00340360345521455844241c294400b0861401c002c02214072968042e5005c0d010390419201c500c004c80744810903910105da1030032072407035020300d41c2032001203d0f04030341d0181c4002d8600d4070410f402403405c03034401240c6003140300740c24040700d0050300408032494450 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 621569127 1250 621567877 621567907
    0x50d0501050909100c0915020708060a050106050f0d0f02040b1c2009190305100612021c05010b0402041403010f090812070507210816051923 62
    0x2a200c240140d0b80001081810000032540e90301030510400c011400c000b04050031140401160000d5401900d9003521403030903034002400c44d0449602800341e444aa0310529500112a400d10034080401c10400104101503c03170001414596140000000d480011500e048100d800c5500803031076281c1c0000e02c0714a071500049003807030481800541841180035032010855000160265040205408a8080042e03510000b1044815100c001c0c803603d071694904100d036031248000da01000f49854280c01090f2039a800c20402c41d990f801070108458001b0a64041c040305035100c40c10f903242e558070795140c0303641d660380e000600003031104400b14158001010101821101a80c0c880840750b4a80001c0344001000c2c003003602c0800c0c0040c660807802e581d80201c20781c0d0a1040140c01001351340323092503c2000340c1c04820039800707014072035460f940d04d1b556490703414254410038100003001c0f4605000c0b113849800c0311007203100080784174640441c1404a07413812330b2295200d08603145010070081154001d9100032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 621570377 1250 621569127 621569129
    0x82b09020301150f0b07050c060c01150f1a03071107060906030f051302120a050d0807080c07021e0406030f050a02010e0d0c03080901110d03051807060210090201140307050d0501 78
    0x2000e03083c1a0b943c54181aa01c00e1101031207036121a400104401e018440c0520004940981c00f80c035841e0750b107404400b454024142d611100300404941400407682d10400d844d0002a40c2030300c55015403102c80200d50303500e140c200405400820103803402d11002c1310000e210900c02409a40c0780c11100320f0070301c04040c094410160617040341c2441c00003004094148810410b00464040c2c41b40c0102d80e25800d0724504143c542e41c1c0280291180d00f02140039a070388550071034413030f4600307a03115101031b103407062000700760310402e80040d600c84501001c15158800c09800755114550081000440b81d42d01d80d01c40044500f02001074480e50031101d4403005650300800701c40b9103c0c000301e03030008c2c410348a40e0701da88a0b460b45000140c00104042810141c9174084c10170786075023000ba18200c80d0000b44142d00100a0482141c101142000342242e001d0035400001d088001d0342e510b9005442a02000c524100052030303508000d0f070400824251a00740012000021402a0195034545640300d2111250000355a41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 621571627 1250 621570377 621570401
    0x60c021501030f14030307090312080103030e09151504090b010503010503070e0c0d020d02070203010608010b1309110907020708010608030708160222020c1603020a03082b09020301 79
    0x210440181042a410840c15a82d11030044024040d113803c104034012081c484890003407100100b4072060980090300001141e04c0740a0244130020800011a10400203100003400300b401c5100100252500159603503106208100415900a00500064041d20701910505801000103130034428240d61340140c400c001c50070300b0503a1035540340a01280d901d070528482c21543c03503050400305480700403032021192062040d090031354548100a403084025030005008a00c60740c45c1c00d40002e104001130059445c0400010802801640c80100c40e03030142040e000d00311455175494000352000d507542c4001c18050200b0798014034407a81040c1c103d90840d9a40d80201525500601c1a4030014454030112030003e401c00005410150480c808500c410820808161580b000414030141c01e00c1c0c01d03405860100700480440d0104900003029900c00f82e200d0002a4200300c0c5440705001103940c240080191131030340c080c041801c02d40060150203c100320520a0049915003a5080c19880c0034041e401c09011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 621572877 1250 621571627 621571633
    0x120406050702120d08011806050604091e09080d020d0b040504140601060207050603011401032d0612020f09061804060506010e030d0f12021608092403070315170703060c02 75
    0xd084c03009403240b03105110307050045180290b00385551505401c072600400001d000701c2d4407241c84a41e20000ba218100607851001142d2100d11040d41d80c500a05001c0d0380c00c1200303140740968100208000c1d610080e07c40444648424051106490300d10405204032300440155003013060240c1d0241c200f4106900540866102c5d50007800340307584002c2164111000410340250311858100180e01405c8244034807103e2448031098102d100424242000c480c14074090f0412100d41c448004280051003000040e40180307451000301420b0030070081040d040080100901c6003000c031a002c2031442031044a0844200e9101e0080c0308655821007241c0000d0001203014103151b00820b18002e10340858a40d1a0081145030306418002029540c1114840d3707400c40e104203000340050800442c0ba502c001502c3c0d0148000c456600c0ca68030f0142c12003601525000350603482c544031100d00310081c00c000301030242071010407003002030280801410010114040b4000c0c0600754a5400c0c5242100c0b00c3c00c1240080d50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 621574127 1250 621572877 621572893
    0x120705071502030a0f0e10080a06080714040c2003040305060f0601120b0a08030c0f0d050f040306052701050604050930040e0f041101170106080912040605070212 71
    0x7a80200c00ea0785a940607140801c144201840100e0380786003042102074000c00315081c195030755544030108510540c121b20080c803800741c2c0d41d03940e40daaa0050784a42d81c0186050b0703108034020316082e00120b054118501d090f070f803010321007072401e05203040035201c182841c1c3c0005401c10410005100d803691000403030b10002e00710700c0d2040020f0302c41c0d403481c0d1181c0d00d442c0d036860100300541c0d10190100d024012000c01c4988071212517030b100e40d82e01100035040460748140c1c404600b00034410022211984c5d01d10b11014103051950b512035002c0c0c08082c01520350035254003d201304d01d6130515203c80542070303c03900100300c5003401d0b42440100c50f0083d00c98107454104000b40300820103040c00030341484545d02006c1c9001941701c41d400352a40a10781002142600210500903040d6403107040c81c5c00b4a000700510001c42d103410005494464000a07003650007040100100a20f41c0101401c5074032120305826104030031f5001d03030180610b600c60307000840800c3c0d001c41d5550650134052201c903101021900244002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 621575377 1250 621574127 621574169
    0x1020102031918080d0917040f03080d110d060e1003050c120312160f020a20010c020901090f0b0a050d110a0e010821130b09010c020312070507 63
    0x81c441d00022500030702e4943e2407407403207008060310002c04641c100400a8651140313010001c054810590309452004400000c0f212092040080310300f02c4079444000302c04607103155103c021317541050b000a8519a981d0702e411018a81100c01001e949000010004805040c81901c03580c60402500408410300201c409100080c00044c40c800e0502049500800d000001d1990741e10307502c101301c0b01c940d151030850240309043e01e440392010810007840d11040d15601d00310608030707692054441d000d0818140c0c805205d20212410340714640004040c54070f02c130414503c1d008259280e40a038440b00d02190741d201c81d0508032480348205110090100c0756070b02114580000207082c503400210140c411342030f406100d100b031780d44c000541000b09030402a4155075a900c940c61510b07007840c03004411450403454402c1400701520400c8402600008035490001c5040030380c1d0240a4100c4442e0505215034002c852000d41d500300704c40521442c40b20b04142d0b03515505e00c3e00a040c0360180e4030030341e01d82c81c03c182c02000c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 621576627 1250 621575377 621575401
    0x501030c080c0f0402030a060b18030d020f0d0c150203040507090506040b060d050c1215030d05070308152706030f0a03020a060902040204150c0c0807080309010809100606090609050102010203 84
    0xf021011200940c40352610b0850f84000c1c8100d5110554114000401903902403072103100030320b050411010703104032001043c400d0303032600d103c2186480c0e03070b030040101c01002c0360069114640e0b180c010f08403403c81002d81c0c00b8050032a80245c809951a0303110300801c000314030440c044c0503404582920140444170f50040452560702491004071501b030b45810003c1c00d100030050a941151071103078904100341c00c01015408811141c0540e440c040d0040095444505010b030b801ca490969042d61005015994161048071840c130b081d9165611101a8603855801c0f000c50405216030102803400791380c0e0742044410181b0b4095003490004c0650041d459680120b6000306805600c6038100d28089030240a43c80041d000303100d070b9006240c6980400b02c06001c1d00b40c0c490303110060030380724840305409076441d41c0d28195140300718814119160300800c401c40c51544101001d03a00302500e802180c401080301c0d0044000e40c0c1d016040340c8001800e842d410040a40e10800c49030003800280021461820700440c0202 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 621577877 1250 621576627 621576649
    0x30d020307110d02150a080601050f070f030215150102060f093d1a0f0a06030207030507051510091401140d060606080105030f060c0307030b03071502010501030c080c 73
    0x71001c8006502180b0303580340c82d40c40d42000341d801058030300d070311145200c07048031900401580c4000510350400980c40794040c030200c601074510400c0003400c3ca0410354661140d4205108100c0071030180310380f1482e400307010461450080f80c80e800703000c2050303080b000020b03d80000141040d5100a814050000c0c3c01400b041c5000199120545c0705a0350400c040303030041500030000b50702d07121400840c149165075000c2e4042e215405c3e450480b0840501c030f1508020752000c4840a295200d502c1d803004001c018041d50040c100302c1d2007401c080d4201700441d156241400007100007501c030401a4002c100305140c24040070400b4204542c0100304205d140000050948814050184c1510351600000c40075030724007003809130b0350360310160510081d0388520000703011850030300c01c040c028803814000c039900c10300c040703940c134410102c1c0e0311601d045541d90002100a0a1201307259030701400703a842c020400c4010f404030502c5000007034001041c0c951440c680702009a02503405265160001c0c04040400c4d5103a0b6080a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 621579127 1250 621577877 621577883
    0x509010b0402030f13050a050f030901091212030533100215060613170a060c020106232214130b06010c0302011503050a1a010f030b071b0308060f030d020307 69
    0x34001c03032030904d01b00d440e1851620001d0030620805040791901ca40c000001d1851002c00e980c0c400d1080d036070703140e1030110007150200103041700348050480985504c01e41c0190f9021a0341c070741c0d5050036008000700162550145100c078481800c44242c8446a0038001c4000c050b100507440200f4501c04590703c4081840c0025201ca4810b05001580c004050074401d5240c02502c1055808030420034140c503000e42d1800c036500304039080c1d030520074552000b6006200c1c0504403880912aa441c2c200e002d4110354014001e510226030180e840f021070030300e4104907030005e0218104410700050f0140c4400c2d19584508005012280070310342200a400000c020340522600310200303080a8440d03002c54503040c0e0150039540003200c8200341505000080c41000a54440e50300d028010100310302907041c80b005c407070442c00d01400d109052074402c1040080d0118140c1641b00a00349000d0701c041c0c0140c542c15048120702101500040c801400b8848180350803650f00340030002c12030041c244094900406922401601405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 621580377 1250 621579127 621579151
    0x5130206040e06060d0501080a05060a1a01110313120b090c180601031b0c17030702030703050d0b040c110d032a0e03030d020703110102091305040809130509010b0402030f 75
    0x891a00e855000c117441d64264002c00600082da107802e03081e9030395080303840c00381c510344a182c011905c1d00b4010321500300703500c040110b443c065543d0f480040d6550582002c55401602c000c00c042c0c01c02d01c0c02ca550328800b0784040714146034600070b1b908044c443c0000c0076041074440e030880303500034500303a40e854500c58000401d03506050300c6998210040e00105500c01c920a14818040070004006900010078221785101d589a041e400e400c220f800340417400116000409640304010340404280038001418103901056404504c1c00101c00105040c3c0312031140c5080461403001d0012810035041c4078008108100f49003c11506400b40c00202a0f12071100d2003100ba43c000010207943c1d544a492410704401c00903007140e55481000c22038000070742c0201c005600160f141d8281da030700d106045c000c0320010300000742000c90030502c1e05c180100405020b00211050082004443d501d9100c43c20480280300c018200015a450443d0401d03080d40c1000040c50320031441001009030003001c440711160000750b40c84078 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 621581627 1250 621580377 621580381
    0xc0c1703120a02160f210e150313080913020d060609050301020a0210020306040b1c02030c09011a0a050d09030c0507051c061a0d0c030204110a02030d0b0f0a090b030105130206040e 79
    0x44902034012915200180c06d0300d2074180110580c00c0700360b2950400080e80d2241001c1c001c0417002c4051300040d80c4030b002280d0301c8420707000441e030400d000e040300c100010041680000301400c030303204036400300d2821111a9140c2d24100844c5802c00d06803001000143e0081d4070f0708505120080d12501c02c480300440081d03000c00400e5841e10b40b94402926490090001080400c03140380500c00d80002070422842031060709030f642030a0800d90b840c6070403180420250303410490b0404140345290000d440342c0b0308001d4244090078550308140074404445000742c03602503500300c0b030f400d0260521903550000b80c040e402c1980b01c94a00640c0e00c00450010350410300001c0c54603801020349842c054100d200e190b0018020f884031083c0103a00d48203008482c0f00700c41c100f00c428141d82e1040c00c18020000c0a00258005000b401f102c170703031180c0012804a200510340300500c0700031000a407941010341c0000c21380f540e0f1070b0b800a64a09003441025040480d4504240c5e881c107a903030008086115034000c0005050000300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 621582733 1106 621581627 621581633
    0x3030f0e0102040f150302070c03030e10020304051e040f0510150305191508030a0f02190c15050d09150c110c010c0c1703120a02160f 59
    0x211904d403403403400c5040c0303900b0102110850140341c1c08211120000d0002c0000700007851290300c814070b115074400240301e00c8156808664007554410030080c845a0740d100802200020a00d03034001c04482c0e408088bc029201e8503446581a0b814a800d00c5000c0202819040642d420411a500542d080c004200c056603400d403407458003941001018a1022010303040a5030000340f041e14200426942c04038145954403c070050000181c003840f880310a10307070601c0300101407018200d03c1c0d42d1281c4c0e29242c10310f2010b00d43c4642d500800e02145a000500c0c0210284c0c1e01c40b91094500700044089401c0c881615059110980c040515000c13040750f540e0702070082c40e03101c401180b009015256a42006441888078000103403510f0444c180001078a40880203620201c0b20720f900a1a00d0708810501c48090382000740c01100e40a00500c4186e102d808a4940e003022140c100c0b50300703c442d0b10740781 = true := by decide +kernel

theorem cover : BRFrame.Cov 621402877 621582733 := by
  have h0 := BRFrame.cov_init 621402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 621402877 ≤ n) (h2 : n < 621582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
