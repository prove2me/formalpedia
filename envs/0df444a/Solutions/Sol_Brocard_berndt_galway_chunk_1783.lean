-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1783
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:39:30.145956+00:00
-- url     : https://prove2.me/submissions/108d2fea-3cd0-43d5-88e7-7c87730a1703

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 320503597 ≤ n < 320683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 320504847 1250 320503597 320503633
    0x10807050418060f050a081207030c0f080307021b030309040b22021206040606020a060203100b0f030420030a08090a0f0810060b18010e031203010b0c1608 68
    0x20405010088180004a0740b03400c0b90a1910a07070782c80b250701041c0d1a040641e62034401509920181c429009160b08100100c00891408140800442200e403900c3c040d00b001e41d04140055070042580406645036010040054081c5014001590031184010320382000f4410880407a071055030b040d44140301e10070b00e40c9001d4210300004c1e04081c00b01c04400301d001e00c0c0d0004030a96055008481500880c100264803a007944065214204403014071400d441d001e0b002c1d45801e20500082c2c4866000800500c81c004070000880043c0790004203282c5d283d03c61008042d050700165822516030094540c00101c940398040700f000f107220014041d08101c14030740c1e40c000f81c2c1c2e03000e4080550032a685410004204a000720a000105041c0f00030701868140180d1610407280e042e0001d520b800402d10080c001c3c0e000700d5003026640d1000703007030800302c41030714134000307031074a82d070700d482e00c0694000040013241c6c0b124550003806203c80100d08032010030a228401d2044a589805106050750040304c1c000c00c810391032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 320506097 1250 320504847 320504851
    0x102010501031a13050609100f02040302100516050615010206100b0301090c020c060d060503061303080604050a1e020405040b060301080331080105100e131214040e06030609031201050108 82
    0x130400b000110041075540509202d403c99483c40d1580164004100c0f01c0d130031303004004015004120451400d82550f0001e190500d03640307014000c0040108a02c59951010340c80e803c0850f030007408903001482e064a07200e4103003406501c254010700405012800e001d620841c64000c1c3c40c0d801e0304860450303007806840801130611265000c1148a520411b0086403200b100034030a804101c0804180d03d03082c0070a145c50706002604038030b0510035500781c140c0401d90041905400c114121000310301500c800300090041c0000c2d2004199140d0b84241410400f0050f9004208a507000e5a041c000025401e04000c1c050009107d00d100941080100e00c1d8070050082d01e125541c201280c0d100c40031130448000c41d100e4581c64201041d89d030364520a01614030344101e1807a0080049003000109442c04004040c9006c4548000501c0000c0220200010b02d0103081084208030601c03c0e134a0f01c881d41c0e070041e403040000c1507403170038002e000701404680403420100480c0e04d0f844000e0300c00441030b480d10004482c40440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 320507347 1250 320506097 320506111
    0x10f170d0311090411030109060b0a0c0f020406030203100516030c12020307110f030d0605060705030d0c021e0a06050105030102121b1b030315030c03121e04230102010501031a 77
    0xc1040c194a036641780b01740d03103d544400c83e04d01d4480d810140a4412200c0f641c0201031606001d02c011140250700c644213000066001592403140d070001d20115003e420140c00080d4140211030b401000c00780590f0000c1c4c4618001c0b03640d000240300c1d8800aa045035815462640007900e00660720f022210140c000f15084021480c02440c1400001c0d0f5032420000800c84010468000007808030205441d401114040c00f0115001440e050321581c0b2a03640e8454000a1106107480d80003c112690007480038103001c0b0300d00041542c44040c80d40c5c95984859120904031031040c680000840d4034101403090700c0e0405403414924801da21440704000c0c0100c4400a041005c2604001c0c07030f2140803a1104500150911100a42c2c0320300304914901d001c40d950400c8180030303510407610f002d01d40e900044c2d250b85841401c041240e43d03410301c10f05a110850818544031160300001030015014104804640b00d00e0502200c00841101c800012803d0703400030722024101c290851828483c8014041c00700c0c0d04884 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 320508597 1250 320507347 320507381
    0x3100e03070503040803070327090507020f0d17010f0303172211100c081b010f0903021606050909040210020a050a030e010e0405160f1205010e010f170d03 68
    0x1181e5503903143d41e010390041c110580000c00c0c60f408040d0002240c00b0440b00e4080c20201031501d20b440805000c0c0580300f151a829202d602088805000780801c1002428442c2640c201815901c40900400c030080a142200c203883c100014010b00002e0364139043c1c07a4150ba58900949640c8a100d4080501415440243c0044409240e2030a941880700700118859840d0002540d03600382000701005a80c0031140601050407414400954000100c031203003428070003103400b000849188a4010b21042501101803460042d500052580000e0030703c1c00c0000030300d60108265150441254036010350f003031180d0460b003c2000b080061174011025446040144100c0384007038601d4840e685050111101070380428180c103440b000035640001401059401036500748514109103406180f09481d04071040200818144034440d503d00c5002c070f00c204a65132070300074007032940c6032000003802c081c0a2003000f0a10403103200c0080e065212000c803105501c81c001c0584203c038000700e415400b0f170281d001103061a00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 320509847 1250 320508597 320508607
    0x1050a08030309191b0603090618210c08030a020d0c020f10090204141608060301020c071211030a031206050f18070e06040e1e10030f08120a05071d03100e03 69
    0x917074071842c000289020741d00450809902c0c1000703000c0b0741901e03269071000d1003004407034008100c00c404032808030286401101c0000030b003034030122140d1f40c603038000604101c030000034059251020f4002c0c15481120080400200f080e880c0203990300c02d1010318502c2290460380480130400c407160b0201a01e42e00140c0080382c1c0c0d03202440056010b19048805590104140d00404c0c0030540c031180890340560154001c42c9440100a00555992498824800407400500b918801c101c5000c540981c15440582103c1c1200b02c0e0b45400f400b0061a04810b21100d032421000180c0f07440d180c0d414204090020f4581880c0d02d24480c0300808600c4014000000d11240d4485c040d0301d91510340040000b04003441c403076100e60a002c1811b03070340c3e0106c05c4005004680d9400501100c8100501e01e501100e6000d056203041d040c051030561003070300403644a201e902a0500412a4240030758000d01d20034940c03592a03042c1c40034060700d4141c41c0c0740c4020a09406078400c081c2d491000109501074084a112030088038145 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 320511097 1250 320509847 320509883
    0x14190c08040308150d060f050c0f07170c060408030106110a020a060f1806120609020403020a210c030605090c04090b07110a050607091802040b0304121101050f01050a0803030919 78
    0x10054490220740031b595030501c055560500344206034008200c940c5d517614003103200c80c2e220303441e02580c84003030501d50b81d11000408101054040320f121001d00c2003660454501424000150740091284c0e4010804100c281d440c2d611000c95004110f5038001c0c00d111800d410300804445d94110b40141c041031110f12174074800100b04110110000302801c0d50b45100c0c0d901e10070056420f0b241c180e44184030300384c011300091006942c0c5050481c20750b91110000f18540710351641141201442440190801e12058004014400c080e04420b104082031002c95103690030a0051000300c0320f07400c1d009030500d6586008600320b107202e0152003046484600c22203244034520b417507541c00d2280689528001c140d11078020040300d045044e40d2000400ca071641141000e10301070100c2428480100010140100b410040071250b00880e51942006040350080001c0c0c034110724140d100303030028010244102d24454000a100f4000021039100d04c010001919a641006040d401c490003422421100004061119409 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 320512347 1250 320511097 320511109
    0xa0809030c030a060204092a0e0d14060711030901081b0912060a06051002100203040c1214100b031e030715020901030b0a0303022e14190c0804030815 66
    0x2016004d000d00617600c80c90300d482102100c0b0811942e485031140001c0c2d5400c0e001200e80d000001c0c0009060618440a51100083e0220801e0300c0007046500c091a004403022000a00207100765030940780ca01c002403aa1054558901406885900041c070060018080e051016411030240c2411a001ca040c040040d0014246100e14440380200d41e00c4501001074482d0b8070b01541d00142401c0c0e541c1d08d00e480030100300a40303074280c004110b9400b03600003020600700b00c91581040002d11840610120f030a41c10b0cd8012002c0004000c0001244104d4040004000c014031591190080040081540c0310044219030070000030841058414041400104081140e100300741c1c4400c8c010b190010b0b56825050005001c0300d0414241d1401052207001c18400a60001030030b802c201e01d40307201c140400180c00d08040056101c000d00d21002418000c0a20b522080012040d004140780040c80d0200b0748080380030707c01c90700110b0403500040c0600001c10f000c41d000f4295550084020054240300300145804100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 320513597 1250 320512347 320512363
    0x4110c01020904050106080408180114040618091505011103070f0b0f1b0d020d090606121709100c03030219112407030b0402040e07210501080a0809030c03 68
    0x19940000c2c2815051502d03110700340c00f504c15030500e80d9183c1455141c094950107034814100c0c0960040c0b600c68401c0c3c1c014480070003591b022078403aaa445071282001405e0020040110020a00c5520046042c152a004d22400f00c5c600140203ca41443d0100440e1840c44c4000c110741107000401c1802e000c034800840104055006612007007150500c405101110403008001210305580341c1803242c41c01c1b5103041203902d800010b03103002d40c50381c89a42c1c81b00001c21106500a04403458503000040f030184c0c0d07001c40c100345030080001c00035005011117200c85c1d51040c811041c2d072140c01002810324071800340d030342503802c81d00034a001405c2843d4410341407a4050862803400200d40c41c01500081d240303041101c00390444191950b0700528500a50360907004401074000828141c0302c40c408904d6072940c0d81603d0042c5541901c0c80040e00f0f01400241038400c20900c08a8861542488000030860314041c0d40d0483c0e001c20018072460b0102e84460b0003036000302203225418020003501c16001e07903040102507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 320514847 1250 320513597 320513617
    0x30f0904090b100f14010e01111921090b09010507031806030203011809020901030201110a08030a0e0c010903050615040e0102070b07090614030f1f060203040e010608040206090f0411 80
    0x190060341000048003503100f0540c17010748103401d0356901d050700c0c1e40d000d014809104402e09000038140c1d001521a420b141c1010400042981060300d41c2040c482c8124a400e68116400340d05122410225801c850030006409800315100040000100c0c42d4880c0c40100255800780c5481101c6501125400c10060400c0c0e000d00c00180e00480180010540c26562b89a000c40c508001c025040d0b00741d01260b85030005101c007034184a074140d050201b21030248008030031180c4c0721170916902d1030b10425183c014036041c2d2200f010746c0714103001322446501a4020b0004da81c0c12074002e211694903442c41c1007407074458040300f5030056107a0b2a8400740010034009040d00034880c401d19601c0c0e141c16140107190f01c03100da00a000300055032039000e000450500c01c5903000354114424648942e20b40e840c0f410500e04c5d18401210844c4401e02c0001e906034048007500c20b5030055807080802e1f91380c81d041191011400d9a000e0341c020b004000c1c28942c1e00d0b010386400c404640141c03011034020b1102501c0407154000090702 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 320516097 1250 320514847 320514871
    0xc060e0111060c0a0c0c06050315010305060d0f060e01140f0f091b031002030c09120105062407020d03020a03091a04050f0f03010507030207051908090108100f0b0d0507020f030f0904090b 82
    0x881b40083c43d0ac09843c242c68002c0c0b030704106e545010b07800500300c0c0d1407144019002e59a512481d00c140f048680003800207240d2200240015031007581c920440e580210361443c4000c0002c00401c072003800701d5038600c2c0901ca5980003440805500180c3c61010300c03144500e06d6252040e46086000c41950b40041d42c8204080d12080b0f403911550400d001504000140f20400e1740d00d40010845181d0702e80702d14410119150950000900c3d200b6280c80c1e81c1d11410344080e6000086025403400c042c0c0c00981020024440d645d042805aa1900708948a20650000d100f007120140814407036030400080b40c03100c0d47c100a102082403a0458041303030031514246d4030f110001c1d400103118000d00c8010060a844038410b0b50720101000e0300f58541d03541a004c2c0c1004103040182d1000031408405000d142c41001c0d0040404140e9201d81c3c44c82d40c00142c0e4040511429030a080c440000d8100e030000c00c01c0d40c92030306154007551614810703d40000c666400713003603850b40c400e60700d990080220700d405401c1441441c4a20718 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 320517347 1250 320516097 320516101
    0x705070c171c08071803060204030503041502010204030f03120f0507022104050f041e050702010207030905010c050a0b070201060e010f03260d0203130f0c060e0111060c0a0c0c060503 80
    0x41d450401031070118000400169188070000d01c2c0e48140c0700b6034009154503010780a09144c4d0400380c02c1103410f030b0025000d5400860003000b40103021008108550304030700010800c00c106401039090f8000d610014241c2c04401e01303107101080c020072155010500d100c400007254442c40d807a03002120b80580720040141d03c03203100e25000ba8806d200c0005d03010345105925040c40c1c0f500c800100f107035403080ca40a00941d181c88205185036014246504c01d91003021043c0164903015900a0003504041420740026500110000f080e50143e280e0f1004183c10a000e400c440c25291034800d501000900841d08542d6140c00004403441c91000d894060310781c0500e414900c500d581450366400d1068030940e50682ea90311503001060494074203c41c0b104200060148e240d5640c0e004a03000f407107802901a001c4031264031940c0801c102514914241d980c04e85440300e42e10301d01401150f040520700070481803030340a0000302c1e0700380b2501d03405095056104d183c491a001c240345c0d180d0800051a5116401107400030003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 320518597 1250 320517347 320517389
    0x180f041a10141e0f070501090c1a072004060f0e0f070504091802060a0e1e010c031812050d0e04051003150f051f2301080705070c 57
    0x20700c80540800e9450800000c0400410301d0500e8418000c0c0302c41e21001180201d407086141d01c064441002c0300020441d216500d50030305501920001710304480d0050381e068040b5691090403861110882541ca0b15400d0004075030f00c1d100602c00000d04c41140d0040c0b980a885655114022075015000503889c01244501d02603000c900304201a00407010301c2c0e4240d00300001c2d5680724080e1812192056030101d0092440c0054002c01310841700042d40040001560107001a0869243e8245201c29200700d01e5000c0d49527421041d03400c009800714009020944d0090100c1d10070344550141a400088031420345940b165050b11031640e40500b100c003034010300100c0008a400180780c4003c00c1c02074400380400c1ca0100f101d8001c0340183c0c00010000003411005241804280e4000ca11080311918100700c68141405980300c540c0303203c12404483c07220320001050301c07480f400e40d2003a503107e00c8042982035044080195100c0030014105030401c0800d200300b0020070080190000208415080114507503e500d07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 320519847 1250 320518597 320518609
    0x61504140f0301090209040f0602040308041203020d080c1b07080a0501150e04030206040f060b0a0b09040b03120328020a0302030703110a1409031e010501090b0a0308180f041a 77
    0x1d040c866450903201c0700141c0c4840045581c415404600170480c8051403412000a0190750005000c8150100740850100101540c00c007205020b03400300d41440f82c03411022200703c0802c441800e00700005000001d0905400d44400b11840001c2068521058850068510b0900807040035142d40e9110003181d681d004558449101919103158406424a016100139584200141001f006a404802140240012603208030011640103042d400d895948400c011401d4001000f1035104624106240180d0328001804101401e0f0300d0039040e00715503840d1007a050b02d0034802e503110a07041080c000c0980c26850740c40144034812a42c2c030010789900301214010b0882d0251882240169410008d4444554016840142900603480d01c150749a25000109041001c0104018410170390707000f0540d075161040d0402c90580300a00410030603840b5003c104286c4e521513200180105200f005425203111000341242c00854001d05481a040c0c4000c02060031281c0c4c04003101c0c01112200064400792800e0303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 320521097 1250 320519847 320519869
    0x406050409060603170f09132705120a080c0703030b150430020d110a180b04020a0f180506031602010605041112040512070c170d05070b06150414 64
    0x40405810f00c15101841d106c1d900c80d80b480984146d02000e00c0f40e0400a960b040041c1290407408540c1410025015204842d924524101d03442d0050002d07900b42e0007032030340076100805480d81d212a15034813008a40075207036205040c103030100741d01e41132080e8180d120301034164007410944411036038681c81c100c000d61054030850446429240111001501c40c03141e22002040340c2d4045907166180040c91a080d406038541e882950342180c0c5404e4001550301c0c074582d181e076035840d41c0c0c1c200703204901b04a41004100d01c10000154089100c0e5401400304c144a264100c80348001d9507101c0d401140c86200084050300216942e60b000000825100442903084c0584002400107803800d0040c001d0615404203e030044c1d00700040c01d2050200014140442081710010304044030b62003950701c810a06213450b00640c180201d580d070394440000e41032190b0000641d805849030582c0d07050700385030660f900c15540003800b9002e075901c10200d20b66841a126008018001000311002040605181d035091000c1c1c4520 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 320522347 1250 320521097 320521133
    0x1207050c1009030804080d06150f02070816061112131403060402060906130315020702210a0305031f0b091e030a0f0213050a0c080f04031d0406050409060603 69
    0x40442d00c40000b50442c0b4030329000790740304030925128502031206c640206038550000c2c40058600038074170300d03c9400110302c0c1740403a9141e080c0e910464858141e10780c0c03844841c01002400b503884004101c42840384d0098211100e03a1410340f0f40380e402c4200c05000315089a103680983c031040c803204111410129541e504000d6054018140c645010313000184c07240140c5c80414056500099a014444501d070042e0b07003d07542c00305611800014040301c0d42c0c000c1d040320300103c1c002c00c85195016000d03000d1400c030100c02c84051780101800a400e550403100c0350800f5007100003c2c0502150120000784e8014494081c0030121001d58460f480c000400c50102d107a1000803400c1070021031300d04290b072008a600305c150750f04440039a408402902c04a4079091040c1012440e243c540000d000000d0352580000900a0180c2e840c0c00e0240c659821420382c03018253f0340100856010189210401102007040680f01380003080050481c1d0344e0740114003074984185089482c19030b280d10510400600000800801c48 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 320523597 1250 320522347 320522351
    0x90d0f1112010c0206071d09040b010504110f03061009050d0609030909090804030b0403090b030406140c0a0f0305180f0f0105090102040b16060b1206190c090b030c1207050c10 77
    0x24440003a4960b04050201d208000da2030200447c071014072601e84091200107003816015240900b030120f0b0078882802018881d41c180b8000301c0072000030350160307840c51031f56040891442d1a141c00304443c4031010302182c8148041c90000003559550500d41161b20742c06560302042c18902403074010b0810070960003030b4803194030300503d0030041000b40090b00c003078980c005203100d40c9850398101034400742030a6003e01c0c4040f000004010410040350030613602032401d010040702e9901c91000f07240b454011101004001500f00b00b44074440352080c1c00c41c54002310340003405481e070030022030740070300b007041e0042d0b80b0301683c3c495683d9100466007407041c20744c000c503004000c504260400b44040740621401c1c08406021491034418000d2024541c0310744c40303c400040c11485006c140c40902500d13800704854a01844d01441340424003607209020b0a80300c58026a541c0420505101c4405065000605841c0580100340400a50f1300c00405030b480c0210020784807951501000000c09103010300308041601e0f014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 320524847 1250 320523597 320523611
    0x40b010201050712020d0e1903030e06010e06060d0e0d050403050f0d05032418150d0c05060703030f061d0c07050712050a0236010e0606090d0f111201 66
    0x707913010031049520740d00700d600542d07100600032060003c0d000310381c0c0d02c88050040300500c080350018003899001a038402d8030140000280e108106484110910076080d11b1154640011b1a5107080300040008184c031540010300060450f404602d00300c01c0d8041070012800003c0c0c1032090007000c105801d104c0d03110400400780c20f078400400400c5404007500003180d00303000b0034103280e0940081c40c3e04a80b406002c2c215144010380f8001001450310140c1b0814000c3c05092804501c0d401d001548062803900100e040940d503203803e09011565001840503810107603202040100343c0214040c2e0001041450000004208080454201c010303020340302c0c0340520002c01c690000a04040ba2210841d409004c00141c025003030304000e07013405801c12000350b200e2801118100741e1020f00307001805245904030b941c18248581c00b22410710420030701800d00600014000038010b45846030007040ca400001c0c0564641c404150390f19101c003424084100d4001240000401e00c2c0c1c208a8030001401c2d04030b800130300c940 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 320526097 1250 320524847 320524861
    0x6060e040e0123071106040503071a070c02010815120309100507050a06050601050d02030906011e1410030908040801050a0c08040b070807180906080706080c040b03190e0c040b01020105 81
    0x10310302c1070140c402c2402441c3c0020300460b000b507440243c0b03034005074113070381d0316140603d050343d100e038000403044801c621010510303110210b03039002842c414581d980307460802226079001950316100c01409001c7c80103003840701c503042d610340039000c07004110000e0040d603d4000150401810400c2001d22004105052041c6400304400080501202c2c0e04000f00054644400b00100c582c0d1044030042c0d20702c40e00020900101c0600020010b040f42e0300316090007034040160000501440c2d451060031031064a0012440c640d00e000582c03825409181d0800084141c466a11b40c1c0d4960003680c01040c050355a00100300c0204201d005501c05a0001e1400300c1c02840c01d079986480904001d002c203800c00050400290303140e800351f20500d48400c08484c180740b0940c2d07030f44111000303000316001d642042d011f500400192517004000140c00380c088020141d04050034035508068542000b0b1440d40141800c0d0030310102c0d800305101341c00000b0740e80f402034082c140300c0c07000380300903901d10071125030441e89030000700311034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 320527347 1250 320526097 320526131
    0xc2001020915070501020d020c0f010c02160303031a030706020607081e010605031f12151505090705040906061709061510030f0c09030b0c03060105070f1506060e040e01 74
    0x51401d952000300d8075283c580c1007050080c003440713003403402c800d1002550b62141d00000030400c0507841d42200070711005000c4c50003261647e84560384e03850100c40e030000600c00070b03002c0c2e0000a00c3c40d00d00304092404000010002c0d180240300c2e840180940c0042062002c46680a03504541c4400100c1064580209065010a001405101d030400b008404400b03d41c4a03810f140700180605d440d440c003044100d131141c100789502802c052048a00c01c130303881246202001239000d0100b42c518070700c80808a0900e0701e024814418002814803040040400c0013080301102885240041e14066440d5209280c55040001c00703640e02400017107240d0300c007008000141d1090284c1214070001031314403842402940b40280e001c0c00e08401700e107101c9070078152210200d96100f21101c044034002c01400d035541d1240036460100c1d10040d500c180c0041d00801144021a0b0100f141d80c842511403a0000c100c0010100d040088407100c1c3c1180e80001c0d403051511000f42382ca8002c2250610500c4000c001e012000040ea1603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 320528597 1250 320527347 320527369
    0xe1026010308090913020a0306020901120b0307051903080d05010501031a10050d020403050604050f010b0108090c06090d080d050703060503010b0a0302041a0604060f0f08060105160c090c20010209 86
    0x8482c0b001e42000880001c141c00c085c03400c26a024103405c41c000d40342d160280103500601c0c5038600055928005484402c4640240d00740790f800580a02005400e02d01800318000c5414051200c45803205400000201385000404481244220000315541002d00060a444400072083c00c8919a08803440b45a60f8400c0c11030252522428903544d5140c01c40341c41006800749500240c075500646041105001c1c022903641c1038955070000800a03003802d03c005444114060f81c801c0000d6101c4005250f65041101c002c0044100090005410010a940c1c0c2842c643c000c4c4000c914598895003400401074050185101030403086000744840700d044e10110300489403620001c3d10580c0c0710b4100340c1c40c07683d056400412100014042a66a40c1c95800280c10388034510b54600019030030b460b2462525110f68406e9016450583d205840d11841e41d180700b02c4410100d00548506070000c90000b00300300e5520442e60303080c5180d15101c044070075410400f99281e101420501441c0d00410405001b036944440c140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 320529847 1250 320528597 320528599
    0x70512160503310309140a2405070606090b030d0221030c19020312101203050c072309010905100314070306020307031a010c0209070f0e102601030809 66
    0xc007400d103143d80c0850200d9201484a000141c407a00724028964010000c0301500d006e20981e5090500d000140016100300340b14440c40c000f107020890550404000b00d102c80b400542c0351840c00e01e4525210300c012600150300003280d0b16070728000c068190600380b04c90025400030340050812140521300300240140c0d4030304400701c89000000000c3d2001c3c0f0b040c042d43d0450103500c8182e120f000c0001c0c2c01a540c0c1d8400c1040f10381c58040d01d400103481e0125641d400c1e00340d6402c4403108038042c069560079515600540002403c0f40900e800c045503010740f4043d40504620384030b0b444022421401e05002481c0410780010400a0402d020002d44004900090040b00c1c0d100c48402491020102680d00300b80c0c90b034000404c901c0c000428081505d074103030081c0e04680165034448250703c56030030044da8032000d5020001e402c001c0d50000610b85c140607480c1991085c0300b03070400b0068007603d0000210300c07080c0c5064404c045064980032401d0b075600c15440c1c0310310f072100728000e091170750454480318100d02981c4411 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 320531097 1250 320529847 320529871
    0x30303050f0c031f0803130e0a0e0a0b06060705010e0309040b04060e010b03041406011514030f0c0c0115030b070e09010609230d1101020f030909131406070512160503 73
    0x111440c0d040c0161301800a100c0c0000b9a40c81e600c09402e0300c918015584901008801041c0120f000c00520348645a012030a4030010691916140c2e509814010001e040980c8500c0c20301040d80400c1d02030050441409440c00030316501c08158040100f00d842c90110517000da0b00d490781c1840741890200d0954103403120b4a031455108d694514040c06900c0b010742c01000d80e03000350400090700c08002410042120002d44525240d911800b880c0f400b40d010441795903903400380403008201d10214180040040c50b420f00d00124182c4041400c00b0703046451a0b100329078240701d40c0c0070030415075880020b5100880040ba00d1100c15403500c070000703104a807503000f0181c4400b500c0029118030082140c0804004c48054001028030820b0b0902807207072a11008100e01500420b03100900502d0007200300c0e40c40841c020040031003910b03411351000000070300550841d040c0c1054281802001c07001c116440c46040342da601d20750ba800718142c9211818502400c500580200c0f00001054190410203603039010042c00e0b01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 320532347 1250 320531097 320531131
    0xb090f04020d080726072310091b090b150d090c03080c10050925050d080c010e0601030201050706020a2a11030304080309010c110402040e01030303050f0c03 69
    0xc0800c00d02120060144a000031008108861500040d0f48102e628500b042c960707505d1301102040d4499800000c0c0034000a030400d000c2e03e5449035048600601362402c03a14034803444140304d402c4075250002520301c600d22540110403038203c2d00144000c3d0007403a80c1400350300040e00c003160100901c20341c103091420022800200d2046141d11034203040f5000010141d40c1592030a00035450761214150515600a04c104018000c01c613028242c052443c5000800c4010380340340148011a0040a0300103d00901e03842c001800d03a00c020710075010a0140121580c2d4215003240c09003160281c1200c0d22458115000400c0580c0c0c1001c150340503d60450009a03803130541074000c80d0800080700641c1032000e400e98101000007441c0c280b482010744603d140140480c50041011390707030b000d6445007402a80c020461140039510402e0841c400381d200d8407101d91115401c4001070141d0300241c024030f1400100d500100241a45801080d0704015002080241c606201c00108182e2100520900c501d8194040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 320533597 1250 320532347 320532349
    0xf01120b13020403030219030e060c01020415050301180e032a0d021b01030e0d2303090c0f0409020f0f150310080601050102060c0d0c031d0a0203100b090f0402 70
    0x8080e004540003410712149454000880000b9001400f05600520600d4950003498126405521219405459903038510004404000d102c0d484031880401a54080c40000b45088040c003040000c1a25921215100e41c10000d0105210700c1001443c100b060070440200030300035004c400c65080040e1101c0d01c40c181c100700b030002411740c0b00240074500e40d48038100c0c40c10f20702c0342c0c0402c240201240c451340d0135000c24a0000110180c0300c00d020480300c9500040420f100b401d018510421201c4168034507144558006900203605030000c6070000444d8221a2103a80c06140130800c00d030700104215402c10820401750085082510480d041c0c1d40074590a08891505a540c088207420024100215950b646407000e07000d04c1c945014032070322005100c0c031400411745600100310f803803040743d05141c01c82c140b6203000001006401c2c01410f001c00e0550352644488088141080c45110715074200007032403001c00714418946040500080f440c2081c2ca01300185580382d50701c040c240d42080c034003520b28041da180c0780 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 320534847 1250 320533597 320533601
    0x4020126061e06030901060f080703020102060a2f0a0306061b06090c080a03030b0a050f060a081e07021c0206070f03050429041101031b030c0e030d02010f0b030c0f0112 74
    0x1842580118013008004800505401510940704e10950300c0002c1c6540b05400c036034655250000130702507003000001400c054529880343c1c0300604440c1300300100d05000c1141c1c84003542c1202c41c41d041d5038070001308005020340500641000b48010700d40481c02d00c0306040e07a141f1032030481c00d00400b603540722070740e2005201103000d10340064071104054600d21260303890b001c0e0040c038501ca0000e01410700c2c0c844c00642c2d803804603000b825484014140c18a00050710404541c82640149400904001c0d40b000144001c000a891840340150350010145558201c401444000d00d04079103008643c892010003004640c00dc0300840300d00950305000c24692201d140c8050180101d003012080440c0030b0200e50010305c0c50360b0701070340103034041e070702141003842040011800c0e2201c1c10a4500c2d10f0076a25000c0c50b4581c440e90180420310018540000c00703e50703580000f801c0a03802c03104603005039100c022030840001c071881002e5044c003040b40100100842d40c0081050030180d10581c6040c00040840015402959 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 320536097 1250 320534847 320534899
    0x1d06010311040f081b0d0b1008011d0f0601150c030908061f0f0303090e040305070b150118030b0c1e0a020a03090605072609060d050402012606 63
    0x1a280240c2c42e107840d024044111006407040543ea0300c1541004800310340f40d520105107400d400342002c20762012613101c151601001502400d84201c01384c400080e40344080c851100100c0300744990a04440d070708d90f070320b43c5400f60724030003810150080001000240e41c00c50801c003c610141c104048000b01500301610580c5040d03002d40da0720b0161408208401da2442d0760081e4107813140382950003164807044400c0445d6140d01000300401c54008040c0301e00d1500b40d04035a44039229291035481c10312966100310344240305a4030003008500d03c2c04007180d15a080303142102c080c42c01100c0501e5551071921610b9610f10060404c910041d4005041804603400301140c180011242c036080f0b580d0a8030181c025a12001c05a050b0001384c502d02c40844d28034452401c80705041c1c0c01414200c0310300e19605030716418420000c8048143c403010000104244c0f5010b02038040008580c900190a11301800054000b075030074150f6241c0c2504003d410008407001902e40b030340140e000e80d01107010007400300d034840d846214 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 320537347 1250 320536097 320536121
    0x2010315050d0803010f0b0a0e0d060905031803060c0703050d020901021c0f03050601031e27052805072c040b09010b192106090317101d060103 63
    0xa0707802e24010300000100460480b2607031141c613501541d61b20900b114900886030010300045602685c64040d18008028603c0c01d405100c0006441e252136843c1d82c6541d11094503041040003810225a007864288040c0d43e010441003011490200b1075600100284a1900b00110b0658041141403850b4800c0000752010404540c20344010221f02001518240c008005100020304001c0018041c1d442801415044452051840c3d154003a03900b40c1c801400780d1211110008081900d20206005448110740030107028070301600b010040300301079100750851502154803050507948410300290340080e00600702d0f2340000000204d041c0700c5907070500c81008a04070201445422040c8003d010038070a03101d0103110031720000c010348500310040c080400f21030314079400344241101d01001880310358402c00761204585441050717505542d640b48000c8130248041580000c0300781c99054194841c1e040416000f18401d1801c48840b40350040d410445c14003010944810100703c00807030b18690207908290300ca02d01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 320538597 1250 320537347 320537359
    0x120a02040501030b0a0e010c051605120301061d0402070b010e1302090c0a0206070e0915030322050108010906080a06020d0e152e0e060307081002040e0906130201031505 74
    0x40d4a040038514208140e03100c424a1b480e09501d55480e01c1c0511454010350007645402d0300b4000e01c6132410038881c05076041aa0540103c0f00b100342402101c000860290146031a00303998050140700c80350080801c059400e00840c41001b210012500d00b55140d8115000c0001009940d82c42d9109001f0b901008003009400880c610184641911910003415404202c0d07400c880c0c095640c11812105000008035054111f01d00001040840d04d0315020700c1c03500700e0302908030f13468130840c404040f42c0442c1c584100100d10780802c01c14001e540e408079a55004000c2d1410a008840c1041c20054a407495010002e00040d0b00166155100c1680e42002c4030081a440c00e6404200540e100602e04007000c03070f07401080071042150500690740d184800c4080e15549030121580300d0401e00060040c00700a48899410b2040d4680001c1c0c4510401000d01034000785d001c0503807903c0c03501000e200b0040029091074603c3e000201008901070640003a440800c2d02440c010a25418100009a104503150001500f1030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 320539847 1250 320538597 320538599
    0x702281b0305100203160f0e01110c0603010306470a120c0e1e01050f030705210105060f01020c1302040902040807080d031b0c170301151814120a02040501 68
    0xc804e501444c4500c955005a4580c00550b040032035130220424241c001090090019404a502c903806004861000318200e4580c200281c001650039082640201c0d252900c4960130210f15018161407001c0d080c001300c03011070f4560083c1c0d01180400015258810b101890007107008140e03100c82801c0000c0120008500c2e04a03810f04040382c40845502600c44c4404408010454010740e00f210300f8624003041c11070241d240d0170101007000d43d4820783c0c0703819030621400202250603a200310107501c84091328141201c0070080400b001e07003524001000c00b8410b0090030743c288c2441e600440d00d10241802184c0c0c0806202c00162420000d01880d0010121a88081004190060000b41c1740068034050f80072211130703003c042000c40a40c0d2118040301590142c1d0410b490029001d903150400c0640f244114000c5003130704000c0a44580c000b40d101d03500e031261404134a00011b400058520701c0c440b41c0c0c21451061810040410600c01e00285c006003d42c169410300002d0810178040844001e43c0140144125 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 320541097 1250 320539847 320539873
    0x40303050702090903090105090603060406152006060d11190b0c070506070206190c0510050103120201060b03070f020708060702060121170903150405060702281b0305 73
    0xd6009094100c0c0607a0340074002c118007030000400d4a8002d00141c6d2280d18040341401449007039080640f0b01d0790455201c0350f000c203032241041c041d01062a81c82d40c41000b601c00c1c1c1104540c440c9014600700785990004028800140c40c1e26a00d451003d4204080517052000c443c0800d0a902040c006200d90380015200070401c0c2038000000c0404840071070440e100d06031101c0405c010342c030640c18000d500a07020070510072020080d4080b035030f480010b814102461022919400c0c01c0280b04030710342d041c90795510010f20400007c0e80404a46030070a1000300085820702000341000e10001d0420b505000fa0080c1e242d0840f0b2003001042d000c1c0844005403001070a28001c069901d003401e0185203c0d4003170803207603008031103404e001c5a2071464022030340305900c500340c0e260907031180d01171480a07030075000b10310102c103180301603000175030140388244020000362030010402820084102122030940d041c2d031920031074081801c903100822540005514082e14100c00191180c07a0403640018507500461110f1109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 320542347 1250 320541097 320541107
    0xa2301060906021006050315060a0b0705011506030b100e060c10020a030c020d02030d051003140a0209070513031106040f09020d0b0a08031215130506040f091e05010f02040303 77
    0x11103000380c08980b1410045103041302a290b180c040c040d0543d120200700d05107a2003502da80b941002014000c0c01505403500400308065000a406485aa445003c2420402d01c40001070005040c58541080443d1407840002c0c01806d04002420800031b1b03032021040355654080c1214082d200500880d184d1403c0c805030140a50400c144880200c1d103401101c030050307400411b4064654180303a0145280041c5944000010705028040c80d00c0e814481001000154008081d107104100d110010405050340384108402c80900905210411109011400c01d90005c5511481901e6001c1c138920030308441000458a2401694040c05020352100d000044500440e030003804800403030441400111020380612040c50000d114030040d59008000d401e1103034160600d0503800411941090780c1c0c2c50300500000e5140d5400000b074504150351842401024038162182c0406ca0402080910209041e51241402044080c1200101c00384a80705881041000c2d4001d07902d0201c001c1c1c1c110f445507103030700b00144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 320543597 1250 320542347 320542349
    0x504020d0615020c01020a060203091e25050d080f090306040f0b1303080708060d02040501090b120105060306160c020a262e06050d0b04050d08010605030a23010609 72
    0x8145406140d00b1440d1030b1010516140e056410b800405000a00380d903020300951000740308207094001c0340100304c50f40304100300c001245140c034002815642d04800392502c581c4141002c051403070b1784070340b070801c81602d98101da464a5a001001030752641d0304450280381a01c55074003d55407500440c42000b04100d803c0350340d1454103004001c2c900d403a03038076004029510f0f080e468000d03002c0303032070301d000175801c14841e00b44580c0c04000680781902c82d55190380424251042030b041071a40b01c2e2034003103003803580c24040050624583d0a00082c480350510101107a2541005080c00076422034100c220826103008011074034456030f01522400c10265030301a00c4608040984001c140c01c83d84401c84080b8040010710f4055010488940b19440c08401c1144940904400300035501d2030303111400010182c0d074140e00104a18054100b820052400d03203000c0707050440440c618000d2041c0303503006100716944602500c0e0300040311180019250080302130085d4821000c034081d0319194451001081855000130200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 320544847 1250 320543597 320543609
    0x16060501081e070e0601020a02130c031817030601110d080123090739170304080301120609140d120c17270106240c0b09070504020d06 59
    0x340042c0038184084241d1500703240c0c0b152141d01c2802c040c400d120102c9111604010140115240340750710340c1c0419007002581102090b5265181c144e02e0407580c05015040c500110040341301c072558055074607817821031980f40b010ba41080e400300c00121164080c21010b644c5911400454071281c0802c000105008024003a01c0c440b00d005c041001402071082002606c00d03e0003c0052031503030364402c41264921200d4001c0d41d842803003400c40350000400c4000d44801c001081181d00c81c0001c40d402c01e060546401c41c512270b6030342401c20070480421010001d0f2415564006034111103007106041450147c140b0850240c20741c01181d441040c0d5690026610f080411152114129480c0320352405007240c40341ea0051002c142104407202d1a01c07200110150300000c2612a408402424944050319003d18412100540e41d689400e10038040460005510703021441c0040f0351001103420010b00b0480840d0700145070010410100b5074039032052011030050400a0800c44d110309802950310050681c52080d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 320546097 1250 320544847 320544853
    0x241c0b12010b040b01090b030604111605071502030705190c180203041b050609060c0307051e01060e060d0201030b041b120506030304080a030c1e150b01030b0a0b0c01021606050108 79
    0x5280254001ca0310b9100b01c1f40002c40076802d6070740700e0080c0006030044803c2e5124501c0301f0085441205d4035014001084c50041008211850400b80035060355038101070300c003081d5442400030f80001940020b00028a6040b10318080c401c03080b038607040c0c0d20400b4a0f001008039914000381c64038004c00e907601231403042e4024038101c0344070003407030f80c001c540901c19014054104504000c4044241411070003021140c060700700302c030314258058070b5942c01c1c01070f104403da40c0762003e000002680f4130309024100182114040446960404100194001c03144950003130505450b2281e0b6903950750750780c1c0f1502402c480140010102d20101600030b1200018202d1103c0d00d5250201203005410000203035425252410300030030402e501500c054490700a003d008a03041000301c0b0298240d04500900d000f1058820f041000c500c0c05000f48010550b0134000d0000d0406107002004038080e901c901e141d0f021265683c5e4016a2019522a6240a84a40b1000625410b0744500a80c2017280e00c3d400f043c102c1d8102010703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 320547347 1250 320546097 320546111
    0xb0106050a080a060e0c070206040b0304030f020d0e030a1101030905120a120504021c0203070909060b040501091418030c0a0503090a060f08061c0f050606241c0b12010b04 75
    0x2010045413403e001d1488403182c890002690021004010a07103980010070075410203540c2c0c80265800d030b008513402c40018198840b5082102d0701000004040001801c1100746511071201280d664410343d800504451007111981040c1d0340682e001243c0c443d00001907968080c1806022082c03603000c560304c24009051030031403c40301e1030a40305244c0100d03402080100002d02d8440b102e24100c100d101d00340d82c540186440088c0c0c0031950f02c6500b0480d8425400880c0032803200082004550050380610740c032a0a0082c6d20744102c3c580c030350256000d808103a6140c545458000b005103540600d00d01c0c4842845481d004205001000002c0e085038202114004030715611100110344210003030a07a040032032010070100d5044e24118280d41c42150044510000d005600c1e22005078a0f01900e0090310590450001c0c07108605203880d154019165485041c003446a2507610101144030f0201c900c0103044101c9030303c1c01c1410480d0031400341c2540040c0701d09990321491040500801c400c07001c65119a240000b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 320548597 1250 320547347 320547361
    0xd050412060b0f030d032406091203090b031906091b031e0c0e0a0b040b180303370f0e0402071110020709060e01060c030c0203160902090102010518280b0106050a08 72
    0x400e5408c0c2c81d03041e075031006c003c1d2400c4003001418040003011400d100c1c841202084140303030440030318411440007005201c0d1420348030040c000c4a1030703504140350107802c00c3e000400d90840c850001e107105c403041c0b8000500204d0000320303250b1444c4200003540498200b03004114105c0d4492000440020201d0b40400302d40d503103a4420503c2d1040d40304861540d0f506000c1544034400c8449040b00341c210107020b40385801c001d42550120511028204500c46828210080c81504100e80c00c500020990400ca8901c0028241c00340c0040c0340d5030505440b030354001800004006140b403480400300700c050101c0b0300082c1c42c0d03400030f5260b000c24015440b00b6032a100000901c2c42c10350400b503040b50080d88910720401c29540b0100c40c00b400c00c03070041c1e825200303001d0010190102400c01000400742d5001c01611380003070b01c00090950b00b0242c018195118900807208d4502400306a02100344101c054032861030700003003030b45408100d2403080a0040840c9100000d151030f0041c2c001d040800865403034054691b9109 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 320549847 1250 320548597 320548661
    0x20913020109030f060905030a0305071b0206090402070f0206040806060916050a05071e06061d101401090308030705041d24010329030d050412060b0f030d03 69
    0x150041d000400c00c1c4000c001080f040b03090009614018240407038481900d88500340303035501850080340000d949004000c025540f00d80560b88130b860f00b0b20140000350346078002070924010064650302c51030340010707410f00300311213180b00c0740d40141d004d41148d85403507441d40c43c0341c0c64100c00c80d4454024107040001940410f02c1703d24002d4100d0380390300c2d564104580c000c401c451030382244208451450484094082e420242400e80486910900700030580900307003029080743ea050340b00074100d445008410b0026410400070700c2c406940350141502d40c03903040c50004a4400c071184d40090210340d00001801589907015004005a0704040c008074050070000601100f25042210740e001c4007414024103250f81c1c0c15900c10011491814540070480ca01d90350384503d04008801400d00110310785d151781c40b4280c1000d22081c0e8090749103041042c101890001042042c0506050081c2059914a412281542c2d805c0c0080c00481010742211300008410901030000d03c1c002010f40b40e154002c03007240400141803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 320551097 1250 320549847 320549881
    0x82a01051b0a0e0d15200313030516050706030f0b030c130618090c0b09130c031d0a15090f030e0402040308041707091104051203070219090501080a02060301060818030d090209 77
    0x181114559039640c105108c1e40c40d0450412000c10004004075030900c4c40724181c0c1c4000501820191485e02e00d0228007808035070729040d01214960038000e18150f141d8010a110139600010380e0540548208150008014080364000d1398803d07100040702c6144100c00e500042d0507038840c80f090240756803078003042200781c05101405a0300c00c0b01004000c24a00140d040b81000c5ca44505010948100025204600b100350030604107181d0721190741c0d10b0500c43c602d60441c46d0214502000c2010911645460161001004019040c080e041c800854152120ba0440f0000c54025003c00d803a141c845c0c038403240510901c2c103003482510555402042d0080c29120382d44440b2003405100e441c3c9881c2c84140000022007003c96100c5000a000100250700c07500100408680d28648051025040921480131a503068000e59400d501c040281001030302c070002203a0542d503527801e0000031a924145800c00840d18500d403008075010101c3d020101c3c0150750004402e0034401c5850f8070603075031528902428820701d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 320552347 1250 320551097 320551151
    0x6040f020309031803011a0105090d0203010216051606090b0f13270506060913090501021b070e190e0c03010f051005010e030a0f0f082a01051b0a0e0d15 67
    0xc485502e41c8549c0150000c0219201c0602001000c031540c0c0c00117822a0407038503112400840d00382c00c003010000248405c0c0c0c203002003041250350803810900010304214490041900440000500c4000b81c5050800c2ea1003814081f10485c0c50243c41e22240e03504010854007080500d404111502c05a524034007849205481c0a001c0c50304010f482d104000d5502d2038045907186075556032580c1c0000c20303420300090040045000345c61764a080c0c0c0c107a6062134070390154081c0d1403079058802405070300000150b05000c540d591071004242d00441101e50340c101016150416819032801801c40d20107146078010520600c840307915000d02d5640d031001980d002c284490301a034141c05c00101c0c4800034155210000300da0b03018001841200c0e9940d9280030181e0301070314600b01101c003008401e64441702007840c188180344ea14002808542402545101c9080010940c03401d014008074107607030480d2141021f00740c2080000c0403c41c40c0700d01400e024a251001800c074280003810945e507c0d0500500000c0c885079082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 320553597 1250 320552347 320552381
    0x30209100f030b03030d091208010b0304260a0804170408070b0d020f030408040927060b030c060403110906010c050303041509060606030c0e09070f0806040f02030903180301 76
    0x180600229507002807040e2030030615540303405000560300e04101800c80da21150304001681141c90504104003602c0303541040800c449600140200c142800030780781c01651100c4a00c3d000f041540c001000c601c064031032102d90b13030008201a040d05501a2401d40190b00890902c0074600048094141d41d106038080c403507040e485400c0822007403403107074010824644141c00050800d00d1201c0e88602d46d503c01e50703013a2005800450184070000941c4203d804410052082d145200500103490313403018126080500103a96481e05a101d40d1014484c01154460013480d46030b4903912844c045c5c2400c10045185401000f1440005e0300d10350060034216030305038120006508698580d070ba0424250f20025280b40340a440750902c038005107140c052500079042c6901c02040c07441660b80010646032440400d0303849104807405002c00355812042300102354055180039205980c0e081d0118001d400a441c0c22020b891001080117a00c12003c800340c03042c407103003400420103805d40008050a0f00c21020300855030791 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 320554847 1250 320553597 320553619
    0x41b090f0f0b0c07120c150c031407020d060e01020a0e03060402060f0c01020d06060806010219150b0d050a0c050a0906061205042a18060e011205070e0c040f06030209 73
    0x4260103003007100b0190044400c013a0f1030382050780461074841000c40e6003400b401018001d10036400220405e1071018030b03202c000d061803903c0090482c0000100b02c000e0f510000340312820754403030b00c02001c02c40b60010414031042c110011100d000b54000d0070084001510401100721619002c200f090182e90024401418250310383c03c4400264065a4440d000d990300f0040b189902c000e80c00b620000380280c3c0c40e64076880c43c00c2c00001e41041071344a00d07642c02c1c6c5d2441d880c120000b14a095401c1c4081d036110700000d000c00085000c00c040c00307104e40000e400c0d442502038032001c0082d070188210541d00c05503101240180c2e9030303800e0400e403202e60103440e007ca1040c2c41111811960f561009601a01410f80c0d1058454428480428020341e5100300da0b0f48640e030078062000d91740000244c5030000d52404100040b52800301000e1040c11306004104078040c003c3d06140c1030140c10030400015240c030300190711450402c1d0b41040c106130b001c2d2140740008507000c2c0000508078020720035550782c0340014000501e21 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 320556097 1250 320554847 320554859
    0xc0309160518060109121209080f1c02030d1b0e03150a0902010c08030708060108090c0a1509030203070e061309051c03020f0f0c0c0603040c0e0402060702041b090f0f 73
    0x1001050030f810490640c800241b071601d04141c28600c1c600400000249540d030b00c20040c5800155003004d4015030010302214001c00d40050303109120781040c0b601d83d11007814030700c04900750303c0303045105110305007440c0c1d646807280f4040c648650084a1a1101c210f264000424981c603290400c0060303850000b0080041d1126820380c0008606a1051607d601740340740b00e5a070445d09400a13942940020710176401c1041c0b65030002c058540010b40c000081078003207400c0c000a11601098042c1803a80c1c102d15242800007402060701d007010350fa004003034806064a44228460054003200d0003449400e00c042c510011707105912030030111503000005449400b4100703400d480c80782c81c11a0350f1010542e0070400c1800806d06400070303001c1148100419940e400085002918014501080520440d010410702c000124030700c1500d0121a040009582240e4a84c00001c015002d410006500320b8244501d4403045010303081c0040031219503841c0c1e81080c0d5210381501601a01d64083c4400c52260881d00380310f2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 320557347 1250 320556097 320556139
    0x20d0b0907140903010207060c0f02010510230307080304030f050d0503061e010c02030d030e0f06070512040804050316031a09100908130803210708040201050a12050c03091605 77
    0x4444000713400907107014803c0d90ba41003140e46995000d400544c0500800105c1d40c1d0a0080c560081104068404082d040c100300c5000707501c08407801c01c0c01d10308040b00f00d8550b403403e200200007080002300352500c981e2f0364100300390f183d000080c007194140610030004c1d06890050301940d000d044064070010122001c4140c0070507034030303040602505100c6542150001603808101c4120440308658001c202e8075182c1e26030600d4044070900707803140ca0308108204001141d00000340c4040c1c0c5800700b00110303203480e0b13070030700740e0700c1d803040381c110a800d030203000c24040000c54040384a6044a100303000c283d44d4112120f150086403c815581e41100c0c1c3c2058200b58030018081d00301101050007001c00c180343c50f881d01d10a0401881c507a0045895401c04035821a800d654522400d480ca500004c04070183e15040b00000c1c9030340b20081c0024103100e00800c1411b1010b00c40e0100e00a190000d21040107181001c200c003994a400c02c03907040c40c29102d40842c0600421000400c9000c50307801034400400102c442c0700300c0718 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 320558597 1250 320557347 320557357
    0x6020d03020d022b0e03030408160c0b07030503010e07031506080c04050a03110907020d020705090a0f020c0a06060602011505040518061602060703110702040f0b060a0201020d0b090714 81
    0x110030b68081c010031329120000e01c1e180c80889200d102c40e0030a15034500300001542c90040b02d60300180c00034410000450502801c494800c15143c0700e11403001d100c3e240c140d00086082d003144006807800308a003010503801100035030580b42441d007522851b664180c0300b1030503034004c06446910620b21200c200422800b501c10f6941010311400c05504160302c41c030210b5608851030340141c030302d541144020011818140100d0381c0001c072030300c060903007030046010203582e4001c0c0c0d106413400f0748004800198031010310783c050111004411020740d07071740a8101c07086a843c040040103550041c542200060350600503c21600240955912007103a03500c6c04080000901000308113201100e010b40c4110365500050040310700c100a49110f0851080528070000e107082402070941c414580361034200c1034242c2442d004e0710500c3c5c1e411a40030503d1522180514003400210f481070b41c1201c00402c0e1100d00315010b40144c41c058031140410016403a603002000121101555100301207a105400702c0d01d81004480100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 320559847 1250 320558597 320558617
    0xd0203031909090f05150402040302031c050d0f0902120f120f0403050109030c060b151614060108070603050f0708010b1b06040f05010f09080d02070201090803041203140406020d0302 80
    0x7101031035840f507045080c0c807810811080c00a903100100250800711030500d05030180141c0f011400c0c40c1c1154003203603035008042020641000f0030901450200e1040d0115904030342c0314041401070354080883c420107004000400c074841d001802c2e50190501b80001e9030022422004001e01c9800c4100c00702c1110303588001c2d140d00c043c200400011010034001d0140303100e078501c02c0e070ba41c00000070369040c00b604480889400a101d500892124894101080152600705814400f4203080d1226032802030b00e040b04c80034000541c0e000c2e5400000e81c0c41400700d1024210b07842910144281d5031403052200d1401402c6449901050803440144403804031007016000044003803c0c516102d602e0032658518108045600f203078072410b1419402d041000030300039403005102d540ca003400710f2159555251130703a01801c072211401c1076001c9114015a846520080001e0840b00203030307a03586485418128815404010035404912011104403160301c041c0c085804584556010708800c1c1d0043c40c0480213503124000380 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 320561097 1250 320559847 320559857
    0xf0108150d170406021c0f0c030302090d060e0c01020d020c1509011205010b072a361d070b0f03040309050613080c060a1202030406061d060f0d02030319 67
    0x80d403480b038000c0c0080c40905520b400510429144000340c0500d00f0122200300100700c0304074041d61503503800051083c1d0455040c01d0240e2a40d03988404140c0da032030141d0028180a040204054902ea00800e00740c0400030203138240c401041c0410801d80c0c0c3c405590822640181010b2006200841050f02620001c1c0c01494a101c1e00314140a4141c190b550a030000da6454200040c3c20702040f6858400281c421042c00c103941c44404600b0b82103100005031320554070b80500d2802058031002e4911000c991200c140342d41d0441a91801c20240001c0000000800100300c080d480c010902d000010100111690316480e00d00d400304c69130191400303400181c403c5041c4440090301003091f60f220809041100100e09e10a43c004e0b00d0816281e150043c0007100703e004200410115500640c0704942d10060181080c01594a0301c80d8a4a00c0092529a20112520300f10050fa1242030000c955500c0c0240000c44081c400035503070b074082103220a050314000b035055000f0080703901d04c3c10702039120814003007090500d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 320562347 1250 320561097 320561123
    0x6010e1320120108070e0f07080402150a03090b0c0301030f14010906110304020a060906020307200a03140c060f090909070519170a0f080d061e03020f0108150d 70
    0xc20707856801100e08481c1141a810062114030300800c4040018100e203002c14901e424000941c42d03000b0009020042000304c80000101991500400851301504c240265a84c441c0350000c0200101460501110b0824500b00417602007482501aa4141c07030700310f200e511258541d0303981c142d211003a5441d4000d0f25504d940030400891440d2041341c0740b80700007030701855882c40d042c41002000d034050307040b110900507918001e010880c1e00100741d0b03131000c4d03120980c4000c107203e9190100244001c04106030b881169148003108020800415080d4904040101d80300101c40300104a268005c410300740000343c2081c0015401c6203444102d094010454a050712626900c0d05d0102e41e000d2520304a04c946c90100c0901040703903221103501c0a6051044d07401400e103c440b00e81d41e089803141a000701402003e000b003059240e49a42da1f014500a0980000c12298036020441c102490111440107a2081040640f030310030950255880f0341c410040186072000100e140c10801c400045031600030394181c800002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 320563597 1250 320562347 320562401
    0xa09110d060b13060905060414070c02060c1606090f05091902160b1008010b0a15200a06050109021c0e010b0904060e120a0206151f030b0906010e13 65
    0x3c44000c118440700e8012865906119850090f01c401800090043e031030f082000300e4081620845035081a420300d01450000b50900001d4003a015021140c01d050141c501d628031582c003c1040502191002c0d01c881042c41d0ba2504540700240440c4a503e400945440000303001c0b40c0140464040401c001e200107007400200c00843c0441900101c048911208900c14400740092440d09000241a00e10080c8114000c1901240403400e091041900d038551b1071710f000602c0c07030207401a01485401d08078007106249558040d25511680c41009482c110720340703000440e0305282c40c02140e8088103030484080d02644000c1001e0020400b48031582c1c03041d5a20040d441060b640d2842c1d59000303d0040f4000b02e0780c41104480d241c01e050300e00083c1220741c03404100100039107801080181d44156840b0100316468141e0010510b000b0707400c0c100b18000850824152480c2d50190b00c4641c41d2481603503444c5681c1d89000040d07a04154242060b40d01c0b10654406a42c007102e250803841c8504220141d00f410307281280 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 320564847 1250 320563597 320563609
    0x14060d05100303080a0e19030c140616050313140c0303070813080114070f090b120a05070503100306091b0b0738040311030c0c090a09110d060b 63
    0x15075000780c114000902001850f40c000300840d08403004c507400300201c030442c10a40e541d4840304000b095000d88801110001c0c1030050142510003600440401c002500c0d401d00103403070f19070440340d4039045409061000310192041d826688280b00d454614840c807005601c0b100c1d4040c0440c0b02864141c81165002c1e8000d0b101032000e065800c4c42080c00c5900c6100410284001d600f807034021362580d078586007810b0303440b4000308502031f003091071814094032800300100103e070102d07816003106144580c000b8020080c00314000341148542036410302040305455402c421201440183c1e2610300c441030340d9a0030302c041407071036011300090741c454000d02048408038440307400c010241da8404402c050b0041519400e2041d104e0441d014203040041c0d0180d2540c07150918060440c0d8242c0100e6a464000c0002d0304140c09458200921005502240c0d01c4040301c01002d56100442c41540e405007001001040881200e80900703403a281e4002e40000c00d4040c2002804101014943d064841503141c0150a426071146 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 320566097 1250 320564847 320564851
    0xc01060b0a0309030318080901111009081206090105030705270408120907120f020105090411091c0f1212110304020108061c080c0a0c0f0305070602120414060d05 71
    0x80c0d2000f00d005801803c01404960ba002142c08001720000c3c202c80010754400c00711140c1070070900304000b200e00211080b500d030090180c02e24410600e0036141c4020320443c04064900d0002c4100d070035402d6510003040c000281002e204c0c1c150590700030802070080d4603000e0091408101c510441521403800368003a05d08800c8103440c19904080700142154482d802c404030554014140002020b40c0e82ca08001c40d6035003190007102800501128403034030110ba200e841140c1c0301000060003030110b03202d468400c612039800350046510440c0c3e07035102985500281a4620315540d0015880d666000040d141c3daa803100c43e0415200c200604040107420b64070145c4103144c0000c00c1c03c0e050030b840c1d192500c0098031106001c0c003060702c0f139460250b000d0000000e9401c4c00780e41941c05001d054a0300d04c004140c0c0e2625000400042032101100400f25910416402031b2003183c1c06801140d882e0380e5079160a9840346031002c01002d02c00c00402041c00600b40c40140c0c0e000c4480007408445c5405411400d003001c503042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 320567347 1250 320566097 320566117
    0xc020a0b0c0111181011101a1c120306080d0c06050c180411041703070209010b090a090e0703120e04050105010201110a0c0204020702060307020d1103090d080c01060b 73
    0x108401450341e2003489604210814034807103030b1070b1108100780070700b1490f10645000c1c828068010000792043c4520000c01661515004035040782d0400d807080c101800c07880611000303c281c1030a08003000c0c03410488802231380d1001036210300040000d440e1444d600013178020300300c14180c89010024500380c040100882402d25550381c042c0e07121329450300205950b0f0241c40c944004009000040076525028411104500115400035642c0302000074103807240100c0d404080c2c1c880780f4044940000c44040f0080080b02e10840b5a2207983e0b88a901c1c07000940100e10b1071a80103800c0700414400c074001548010300502031f46046403103031a607980d250f0368055000403100b40020103e0701c1198042c240390190340e0142000340003e1080c0201100c0b503007214094411200e04100040003800d084d92120b90455a8136070700074110a075686042c8401035514030120300044000381d18000c0c0b03441c0c1d000300441514602c9074000c3c40c2100010b869168083c40f600160140c1c01a5561850700044140092000b0140703078513 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 320568597 1250 320567347 320567369
    0x91e151215030d140a0909150303021606140705011b050c160302031209130e0d02060a02041d280509070501020a0b01090510030b040305030118090b01090c0c020a 71
    0x15200004601a08803181c005000368840c1d0501d400998005800b040561380103080552500c21502045800f5140d907030000403202e140240d06104905400b0b0200e087d00d009408a4001881003460018258254401c01c0001502e0f05400c1d46c0b48640c03903006001403800799002285c0c0f1f054011000c017002e80070300007460105800058145065030140810402c01e0342090340144072500c1c6401290301d51441c0c00d440081c94000050341d4440e075a40c20f0760b000e505407001c0c40400c01c0ea1140300c0600e40e1980b21010901c00f600c82c8000044c0540058002c44c2d00355807414611030305845024205490440024045102c45e140ca428480c500c2c061030740c0007584412215030301045904042c0001c609145d4035802450441d0040083c10020510980c189411aa5400b4000400d962018654000d50945030030040c1361b400e60406001c03d150b4040080c0d4103813820045140403480484020314100c07400c1103801040403032080f0040044203420b070300410303003101e01d07080050708400c0300d900246040701203411420b0852 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 320569847 1250 320568597 320568601
    0xd030b040c080417130f03060507020705030a0507030b040812090607030b010c0515071707050301061812022803050604060b010804051213030c240302091e1512 70
    0x100c0d050181c51a003089508041c1c40a05064032031862800c3d44c400d451030f40e41c60003d41d4404075201e02942000400030402041041d981301d141c18800303044245c40100040c0b28800c400700c2c5516011884044269002d1300801c02545541e03512510650014015280300609200c440f011188003200f40c0c0c0301c0c08408001c1c000030719280720f000e8102c902c14480769041242c008601c000103a00000d6034442685100310001256680c0c400403034035a81c0c03803145005200300319024015803540040c0510306035091901c03461240d814102d0b0141545026104802200381075003d0080035040c4881701000704029042c80541000704500a801031040b40e0b402200d083e030010f0100005e2090520a01054120910b402500b0303007047d4841d6a81c0750720b2f200703400c0f01c2c0e041c0000d1b064440c0424a0b500900650340545c400000d00d0b135542c038000c10101e188495001c41b500a100c895003c505c00c2c802c0710618031004003500d24540c0803408541081d1108101380f500902030b135030382c00501344081019145848a001c402840c1d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 320571097 1250 320569847 320569849
    0x31b1212030615170a180309061409060a030e0a050f070504110405030c060d0b032d01060b0d09020a030203032a0a0b0a020d150b0903120309210c0d030b 67
    0xb603000c1d902c09160300d4442103031510032a80c440c4151902030510314100b613681d02c130011418002d05d66541220340c900b44d000c4042c2c0400da00440300304122040368498035140301c0c80c0b41460145218034000d007075004100f0807080340300703038042d601440e001c500c3c8030122880003155940b039a240c201e5005046150340d01043c010886460f02d03024400c0240e4080042c907043c107203042c0100303984402e50800c0500c2400f020038040500c4820b41e014200d085e100030121f031102030446c41181203024104003440a00300f40c0c0144a404003205014036011101c480301051315000900241d54020241402c0032a48041d0013600003001d41d4003040070b840ea0306460320340300303007c2c0c149400c00e4840c1c0304005d00005940c0d00420020408111207101c0d42d9032042000d100076941c1d048024020008001010892814802c004004102c0d00f408001401e49500160308680b041071688449100c103000c102c0c0e894074582e00028004800e21000603103032031020000f00c00182803034400c4a2a6080411103c0b420002a545607581c241d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 320572347 1250 320571097 320571101
    0x9190515182b030605031e1005100f050607050c01080613020c0c0f1203030f15030307030e030c012a02120601090209031002040602061f0906030506090106080606010504031b121203 79
    0x101c2840f41002c100042c5400007080e00d40d0b09213016620740700441134882c80e019500b4040903480d003800c4001001145084040002c602481d40100f070780d0601c9801c2c0c0440c050030700070700725000150000010071031006000011100d04000410b0b0030340020131141400101c41190001d0302d14020b18401a0000c40401004e0040000405c0c801d2031140c170b10a1550441e400c0044100e907003141c1c1070082a0940e0f80c0700c08400f403030a0b004452554142c0b0001800038107056000441c182082c20813402d036030501562030700444041d1007002d00b640700c89400304040844428070416002800b440a404025000c0c030081d00d480c28a0000d0b070152070407580002e100155440c00380500000113a441408608150803e07600075580e01c8000d10001c4407856041e00c00382401e4074188084001e1001540501c00c85407a403078132035142c03002918014001c0d82010030208203c600031804501c03481c410303074426050510710b880780b1500d50b406c0904520001c806c01004030712900703621403541b005402291500b41d8401030020082c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 320573597 1250 320572347 320572423
    0x1109030a03110c01081003030e03030405060a020609010518101a0406031a01080106030317040302100f02041409040f080a121820060414040605040204030303050919051518 75
    0x10402100e85c08100c1540324400c01602584e41515040300200c607044080ba140d40700c2d5030451940304001080d0b500d506580051035501c2004808000e00c003989542c00e11a600001940d512450ae07002102c80d18010320459106810802c24000e070440c0307030b04409011030220383c8150015034080041c1401d905072004826540b0713004280c3d110007003000f586580c074002e150204520482d09804a09008074081c18402c002c0c43c0100c1850910411030000c84809440c000e62141c41200f404071095580c0d21042d281c0029481e1240360000002c81e150b42c032542c5d0f10f00e159882101c801060000703035101490409020320030481421f19040300b01c1c1450807241070070305410289400038200c252080d9001445031329480180c90131100a018211190b8407a5800a4041d100681080d5009840480c0c000705155054020b00d02503803040d020798480c2c07540321601101050407541301030529440305800d0300e0804864155554840c0c10a2854886540e00c54242401e14600700504034401c8a04c00c0188400e1300c0181c4910 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 320574847 1250 320573597 320573599
    0xf060c020d0e030a02090402010e04060e07020706050f040605030705040306060b1b06040210081b0d0605010f0f1d060f16030e0301091109040521071b0b07061109030a03110c 76
    0x9010b60444000981e5410a10b000a0050903d00d01203001c6901074081c0d64140d1030018000d0009a490b041100011182256203000500c90350500040c014090b1084034040c00002c0680c0f8685410900c091701d0300d600140001e402c01100304800008a021032068101070b10200c480c865550001e0103040b03580300c1c1c250300c0ca5005600842d061000595840720819407116440c24091002c2d60f42a0505814000e0480c0c0c0d0b42c0031403400540c80a02d865181d00c07500903940262558661900580c000701ea00761040725503040865020100005d102444c0c0c1d03c52024460010095480c0046150500c0c00c0e9412521a0760041050b9900e15001c1540064400c3c4603100c0c00e0b402040030240350307200d221140d00c103007203594099020003000c142403060500c01c0d0f00d25602007403010705c0c8103522008203100365400b00308151000b2001d20004a007080c465120901100c1d42c0034000d07030611004e03485900c01403c1980141d0841142082265895101803050120142c081d0701c44590105003808000d0910300d040e0320321 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 320576097 1250 320574847 320574857
    0x60d18020d0b04150e0606010809030c0a0f02090703090302121c090b06010801050301021e1605010c050c07060f080c220b0d1104030209370c031d03180406030f060c020d 74
    0x200317031510000911542e218001346001c4130542c44540095041d44203031010700e94540100100082032103140f03400041c0f0700f4401c3d0344110703030342d51101e0703040301100c4071444000c0040c0c03c21078194240d00c00083c00b5210790640210100442c4038000c03c0c184c122900a01c048810344030140800c142d968000c062940105402d81c000d6280030440c800c0700c8000d0030917a5101065400115007540c0a1503101503883c8182d9000d4020014940103010140c02600000308804c06442442c1c00400c42d10720a030480c1c10041e400c0d40b65202181c44690350000b0703581003545980d5003c9001c0701c0041b141c0390208541c800812503400000da40c0e0070720900610649400a9080304035210410003000180c84146140b580098029000b004056000310882170780e08a1a041011202040914000880fa0703030f803000fa44000f558504121500c034400001c5a020003181d03444655400c20300c4071a400345900c074045c60004500a00020b8030584a075283c1d4800d03c1c000c8400d5131017136681d801021410f90100312000380c141c41401d00d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 320577347 1250 320576097 320576111
    0x3390e150306070311040312030207120203130311271b03090a030806030f01051512010902010903030311040b07060608061e04060b0f1e0a050f060d18020d0b0415 71
    0x400d070b4880020f8428401c040da500700310400b4014400658001e036038018000c4941c1707801ea1400402035089000241c81218079410105d50307090000048035100007040c3c01c02226180f41d925104004416111995009014001410900290103009500917a4107480302501800c001c1c0301c0d030114400e09031107074120b24402c00c03d2100e06440000d14064040c0d040c40c1101081d43c901d80440d0410079403640c002c5140d030a0009100d800d8804001703007001101c2c159402900a1641581d5509940c20f5600c01380c00304051101c1440441d10079007100c648003032401d61280ca01030b507030240c0c06540da001c2c02054400030340e00c070400c1c00555402c0c0112504080401c40c05091503410a00c642e04244011344010801340e60703079040c5880c41d00c50304040100c3c0302004000740d8581d1090740700d40341980714130850f040c40340d40403074004500c52074498501615280017415a904051101d000c4100074041c24130100b9480030401200d0b001a42c460b410000f0082c407400c031030701040c1414549903c90038030840920880c44e0504003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 320578597 1250 320577347 320577349
    0x160608091605060a0207051c11150904051f081608070501051b0a081c0609050115082a04150f0c0f03030b060408030a02060a0207020a03390e15 63
    0x4a181c00da8500701c40c42551100b41c0f600580c038003511644265046401082902980014120100981d501900110300c4031803044082051000b0158142c1019400510401815080036804140c3c0040008001e060790700f0202c00c2d1020791815a400071030540e04c0f185204030700940180c1c07100c0003008081e00a118290038040082c04034003036000f401c4400040f01c409401100c2c1c0c1000410075260700400600e5a0310000714994540c0c51040d4040840e0504108002803524618810181222000103807540482300301d640441d4030071005041c81c0818409072a80c4011598529401446005250100c6a44500d045000d030b003460018031010f014030a000408100150300b01000345012607024a082c0c5034408145015001060482801c82c1c00803030101c0d01051041c000401007040150a400301c0303039280d40d080500c006078411904000d400104500017000042c40b41c048506034425141402c1c3d03032410354440c4c4a140c0e10a4010030041c0040705070b2040043c1c0b0082108180c120441410f80c540c1010640 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 320579847 1250 320578597 320578633
    0x4080d020f190b1906061e1701050609130c0809240406022a03040501020709020702060d020a11010e07050901050319030e0d050109050109061103100b0702011116060809 74
    0x640c002c0e08200c2080f002407000c0308040c0c80701d05902000c2400304040c0b03840e214010601c403103d1241240301e980080940040c58001c0300ca40703100c0b00360070810f00100c0c2e0800040c0140c9400104c012071300441c0001c04920002414010125007503000ea0391500280707080c180a80c0b07402210840c1c00c01145411901d1480e44100000742c6a00681040d03000da81e036a000c4200611a050b0480c40202c004140c0c80c0c50640030070003000400464109a00b2640142d484002c5035040b8403a40340020750205d01040030401e44406500a0829410141848200c10046802103030035540440007415040e00104821301403490814025809840188c0040c444208a4501d242d9507003906d107405414044c0c5510355042940c1d031410032905040e0b003c8024080c400c002d01d04a4041c281ca007c04466040c01c000183c4589a40542520722840b2201304e00380425261aa84200541c4250340aa0400841401c0344800f840d041040d07149405508490281c0c052900741c0050100c00d000d0325001d11600001581034a4901c06 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 320581097 1250 320579847 320579893
    0x30206040b060621040605070e061911060703060320010f1817070806180714030c0405010b0a020c01020111090405091c090f052205041704080d020f 65
    0x1184a90020b81c071410001001c1e80503104940018120000d03003000d8194580000034000c0348540d10900194450100030344006104c40000d82d0011014030110542d08003a80c41c02d54a0041c505004030310741c150024131404d00d102110950b01194440d2810001c012545645020100e086031005504451520000303009140c0c0c0882181002000c4d0035550441c403454190b10020030465011b03103040031940100070b03100c409508c070f0340c002409540002031200400d201c1030b6800095405c0541030143c10024910b000031408014907800d44229048915281c450744544c0e8040d100020400761161141c0c1002442c000d0070245090459041203004680c864624040e0b03100c00314100c90115007941c580821500e44014421024980c22040300903d03044c80d0050000029620008d440340c1e060350301c1c0c10600c5007052018143c41d1542c03040e10008090700c10a0780c00725411030700c00c172035581a058801a4803030340c1d82c020b45c00812030742d040070282c082929010424200c540a400c0d002c0d044041c515003e0002d80d80303803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 320582347 1250 320581097 320581103
    0x100f120320030301091514010203030708040c08010911090604092d171921180f0825080d090f052a01020a2103140c030703150303020604 60
    0x240d40328501d80d00e14407192040d074a48894044036125079490001101601d0381d5a019090b00003203460100e00c400308506802081c0c603041e00103511f180c80340c0c0c0303048421010080055440c0c001e025004900d0070000c1c0501d55401d0700610180e00702003251020850601c1c0043d00f1544190f00d40400c0c01b00081c0400004e810340a41c000c1185403c040ca00401c0000300910a0020309001c90250001122002400501809030150040004540400c0c03410385540080810000408031511403114000001c1d0304503411980c918a0520003060241e6075207543c80f28012012107503080c0228840850720300d0400d0702c104119400640030098901600d582d4107520618106d1050b030360b10ba01c2450f06004196030440d069603848021a13000c12607140d00a45004140703010b41013107410040c08070302c05600c0010030b10012500100801c01c8014800003155011240002d0042415158500b100707420400c041c44521030303509400001e90720b01e08494000c007154500b450141030706e890b0000c140007180e0300042166000c1d41c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 320583597 1250 320582347 320582357
    0xa080c0903100e010b030303010e2208070b1302060a030501300206070203070f0e04023105060a0b0c06010e09030408030a03020307140301030f030216050f090c12070206100f1203 78
    0x380f002c010310b000d4851010050741601c00000000f03402c1910031a0070744101d00c0100d482b20454994501c4d0103800040c0000586103400503c064408200c1c00341a0a0b04401c140e05c40300c450601940c085403060700410b041e58007003661880104618602d00103481c0a007603010302560035204003051307400c0780003000d244041d0040c4800b154400454034100080b6000d080d141103ca0200396440741d10783e01d4043c003281c040b4020810802e078041c0145c010400b50650500b007006401c01b28260035030039401408c0c000c0c0380e2603200d5410600020303003200c180b000740b070000286005018030398101580c4607040c1c1030182c0000e003194030410082004403000310640e80010082d1070007503542e032919103080362891105840b842c0d800400100000801402c65198034040313200782c0035107021028920440b030a40080d44110b80c2c003c0e0428800789580c4c60904252039001584814a50410401d0070041c0c2c589c68080b070b542009130384582d05004008100401507070081c42c41840d0701280c0740c107140074118a003141c2c074001000d001c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 320584847 1250 320583597 320583611
    0xf0c0909020f1b0f0d03021201030f0302120c0f01150b0415030b1009090f0b060301150c0803040c1d040510020a0c1b05040b09270304080f030a080c090310 68
    0x2440004a800340408100c0c14400510100d2421391209040c00c94040248910035071070703003007038002e00030b03200c08201407050741c2020f80c41c680300c1d61810440c2c03076030450450240c81420305440c1d0090018020159944d001080d8030608807407a54215018004003007100c0c0752070301e020081741505908503015110f000380d110b940407880c040140c2c0544181d00110350700403403240041070040c2d0b20009400031076401c840b0500181c6400c020f19011145d0400e811a0485001c0005208804600090941d0081c251900c102d500043d40c44d000e903c1d80059408890b0051a52400c0050201202c6070242d0015030300541106803e09580d00ca0351418542e480c0c00310315402042442d00e150003480c0c140752841d080303041da036401c00c2c801084031064111030084d02c0c40741c2c0c5850a03e03d900d0400065051098040c0202c4020310042000304c0310750ac403107110028565203c02c0102040d40b50301404140204240c1800968a82e20900c4000e041038000502000740d4410a10450320582c0d0f000490b162600440b110014001c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 320586097 1250 320584847 320584867
    0x61b030e0c0418050d0302120c07021f0203090d060204050a060203030c042606090114010b1e03130c0611010c0305040210111c020319090b181309150f0c090902 70
    0x10b180d41c40000340c0b8502079200c5c05070610f50590005d02c20107012000e0040d80ea03072400541032a0740a548d03c003030f420118154210310304a101d4505001178240d5401140e00349584000020f14107803441a040783c1164010504000504200003c0741c05441540061400c524084018414a009a2140480c40003222190222030340c4420420803901d400d85040e10700314581100070310b000c0c4c419101103d800300005800020014011416550b071021488007441180c81401c1c26010729400103805070100c0700d00140c0020000341d0311700c04900282603c0d12144682c0c40148400c80c2100c40d100019000c0c03504140030000140e860011404e4030a8140c1042030708001c4041400b481c02001038200201c0c45150b00450b40400d80000252503c44110a4410b076140c41015040324468003a10980f040540d0a2118100c0ca80780040428030b0250040e1070f6841d810744983d6220140c2e800c80360141c0715201c0000d20000f496045019000c181d18020805000c000e29101d0014000303409446840201a1b0105000e400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 320587347 1250 320586097 320586131
    0x1050606270a0e070806031c200f010603050a110d020609090a1d160801020403080f0309100501120320071406040f0e10090b0f121603061b030e0c04 65
    0x80c0c0401d8140019030300c2e00100c0074000c41c1c020b4401c80d200c1d119030030023030070000402d015a80221155503203a02c031200c001000d00c140000341a80b03065090140c0d04d51000c4820302480b1740340080d80110010710991049007003403500c4000320440c0a000d8090000d87c940940c40d00c604654005c503003925190415600c801c03481c0e00400310405115149004d902d896698084001890b14615009100901e81c40366075240c01d03403c07481a0710005040d400180641c6880a500802a561240c10001510140d007922464142100c0003600080b488100391701c4002c003455030104082c07404070003020784540e960180000256032244c0501c00c00c10021001d07420070109440f011300f41e1f8014440c59264240060315200016296001211745600c600003070080000c1d080303020300900c000481c02038208560507810000780a907030000185905028401c03051203054004c4550f030b03418001c501514002840c50340258210b10103030081c0c0d802d60101414881501880d0102242c41e1008030000c0314005910340c1c0c0c20784207440d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 320588597 1250 320587347 320587349
    0x8030603013305010203030412200708030a0f031e0b01090506120f061c02010c030c0506130203010e030405031506040b0a06020f071d0a1508031b01050606270a 70
    0x5040c200020010300031858070b04445840c01260301c0b001e80c9040d2100c2c01242c3da400206c601030a111000c2c0c6924001901405035540c403034442d04860404c640b410181c592401c21298006640c43d4000521040b055a001e10707044a900b00f149000d110400e1945613219000341d040340505c01c0070303a9454030a4407d07802415550010100688100d40340c0b189520f00305c00300d503802c0320404154504200002c13081d2401a00711031607510b42c2400c540440c44c158004440e203810308441182805070b442c0e801070100b07034104510b621946001503440d90354141c5106143c00e41e15a88140e1405610900c014070080d900800c4003103803070308031032034504095540c580009c026150b1400c0032a00124030f80000303d80b065011401c0c0b600d0020031021910750030f61b2440e01c2401007400e07641e07045804100074007141601c1c0d02c90f00310140203c80f148001c451721b91260161801c50344410a400e038481170480b141200c0d13030070a000d51640700c1003c41e04030303080811b000058a003411f0603600a01d004a80a48001900d035111304c0980 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 320589847 1250 320588597 320588621
    0x7120603050c09060d0f0b071803060e2116020a0f0f0603180305090904230c010228021003110414030c040e0d031a09070206190b010c0803060301 64
    0x8890140c0d00c1c100a0340310041e40070707054041e40e500c900003001404c00003000c41415070f00c80783c40301c1d86403104d8840341c0d0042400b0b8014010400482200800400b014841d03501440c0030f00c0c00002e078606110741c1d092400a80c0c09541158000c00d01d010146550f80d00240d50004c00800c000341e050040b18400642560b00640182c086001b4401020a6a801c0009407205460031510700308008091481e80680c0310603100d0300200081c008210032031642c10002c160756002480b078810070780482e048010003080c0c2c00c40307003007114416401848210215a41003180c1003010b050358864000100c1c002607034840403401c05001900540ca4100101400d900c240d001c0700e10642c504042584480e00c40503614141c4045494041c0b091044041400891505119103480c81030b11400800045401c1c0d582a40075000780200302d8401c3e240514241c41d203458a04a4034841c0c02254041c1003a86000e9411244001c4100508101c1503e4003002404603604852042500d03908080740c03d0b02e07551504002405031410740c03800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 320591097 1250 320589847 320589851
    0x50c0a030302090a080c030d0c1a07020607030c080402030c0f150c010515190905090313090b010207120309051923010807030b060403060e01180f030914030a0303050712 74
    0x21824550701d03038050101140102e03201056541c0c3c91803030aa540034038560032607042d00131401007a0130743d000b40d100503a001d02c00d002c0002030b402c044008119003a004c480c0b07003015030008410010300d15810300c03039200e4a0519050040e607a0401d5008203540e0400e070030343d40d801900b02d04091981d503a01c0981044018003400200780d95041503480c441d01900381079507142480c8102d054100400e140c08404054449902d03200c80980c2c52606a043c000340c14007500110b040d010810400c9000c142c801c602c50f0162488060202d507216294000925055035540480040c2182c010141c00007503211503810100d6070100d55140c03458003c0800c0d03d614240c150b1064800d6151651503222407541040c02d0001c1030000d0300e5503407a903580d00b4000c1c0d00b0344000100c2654401030800c020b200080c5207501c800c0754400300c1e10000550304a800f09150410150030801e6442140054011301050341c2b080015000d0720404100e003001070458000310341d0320011a04e00805058641d000500380c80c1c8500702c001c400c240300c2d14003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 320592347 1250 320591097 320591113
    0xc020d02070b0705060c36030c011d01030b010912060506090f0c0d0207060f1404050106060513170708011104080105070903020f0103180b0118060803031303050a020a0f060605030c09091b01050c 85
    0x51080c7c0441e0301c5c003406170040c0050904691f000c0c01865007500e083c1e519505000703c02c880110001c1c2101403100d411301200e1080418503140000720801c86c20702c03c4c2400680e0741440b00c2017082c00da10051003803841c242104c0410070000025401d85a0034264040701507100c103034038904040540044180c134142140360503100f60350b07950304170401801140620000c000040c0c03603a400b102d2a01c6130000d1450300190010040101e00c16401a90740224050002d0723501050f00c5204c91401e4544441c10700b90302d1400480c050080440a12807550400507505101100a00c2c50380415081c001411045044c0741d1f030740c0818080400074100074565079a01240b409440d40e140c1b41c00f126108401d1101e40300240c500640410103400006c00c07240191024a01d5401002e900c0c3d4040768030341c4c0044401800c501aa8040e4400114103404109845208080106d0101e00384003c2c94a000d401d1070001c0d10840b4900c081c4a100340010034201c3d544400d03142c0319401820031a005886520441c5110807a620450740 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 320593597 1250 320592347 320592427
    0x3120305161107180f05010b03040c080109050a02010503090a060501030803090c0a0b0912030d0c020309120a0218060a0b070b070212030c0409051005040c020d02070b0705060c 77
    0x80403a01c54503148400e04414030038108219040120054028410341c4000424000e0700110f021103003510a5040021805040440c44003040d502c00307a00100c0326000c0071003130004014000c40158050b20000000b0003484070f031070301c4181d81c440409074040d0500c00004042810540d092120490064002c0d80911481d40e59242c010859807040f180362540703000300300b003003d071500c0c0418818048900c0506c030207040c41d20071801c000080c0048013180989100410104012480074040c00000900c40d03000b5545070000e010520002d1315492070001d019070007000364880140c1d00c0154152a8007802d504907140c070350b284030108800e9402904031800310300780420719404001035105d040d40319116542c00c0e41c1c00c10307103002c5440110f0701085c1d035107041600c1b041c4024002c01800f07038000ca80c481041d0302c0c0048a10341d21000701e412130709036940d20320041c0c02c1481c0521081c1d0b01084494000c0410256284c03508440b52070761034459101038020601e80000041b0160340c03800340910383c1c0420301c008580521204840c4d03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 320594847 1250 320593597 320593601
    0x8100605301009090209010b0f0702031209192108090a0306020c0d020606010f0302090f0603040f030915050702010c0204022b0c02150106260c0d0b0409020a050d0c031203 75
    0xa0304400d52202d111008540051680941d084056024004140d164240b282d50071041d0010f921020b018042400380c400982e50800a80d12a0860141d15568801c801340501000b0b040c084804802175400c42c0c0e082011060520b10480541c04113007820329100f6540c6810307203861203400d8500e0340c000c4d500354000c41484110350080c15103d540c01c04407180c1c480104000da8561604440080c0401d089a15030080380d4000d4000306003a20303000701113034050700400d00007410302c0d00b0a0300c00741c0d01d0f5032085000c1020503400c08510300280a500e813806c10b900705808001400381c0f00d00c0c60000e041054061840701191960780540300c07168810001140b401e641e03524900101400329144000280c01d061034090454004a0038030b921405520300200168202101a0746e03250750303003e03405610016001411210008001c1d2140075041006a05179260000360b8000255658401c0b81e5100c4c51400d0030010050382d4141c1800d080f1242030700c048580001d40c0c1480702ca01111640301800b031403120404c1c880501c1c1c0c95 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 320596097 1250 320594847 320594851
    0x150c020f150402010906120f060e1503070302030303180102040807080c092211060909070906090b12010e060d08120402090a02120406020903030c100e0d0810060530 72
    0x14021100600755101071454640415280a408078101c00c1041c06490300c510541c03008540c44002c00725100b044540640100d40e9181d1200c591300941c141401600031900c031400030003640c00c5000b00085801c6400181d120311010700304c0340800000c0010b02c91100000c1d0142c600524100042d00d140c070355214002c0e5155228200c0c01d500c1003114100103188030890004001404151680400c1c1443d89136940d4030503149049495507100005114400035940c501c0388051140303440e56101400e051034083c2c090081d540b00e40200101d48014460000209605041281102c1040c005485540c507500041030b28231022004c007901d13884c03001a106030002d210313442c0d15000324801d41d50003115a0381e0250383d40c12806543d41c8540824500000700b00800d00c070b60040d05c10f030180182542e1a020103006007a24207421145400c2085413603203d4086001b0085c002d40c401c1c56400c0c201401907181c08603030071001c50018051041403200c08a8060007210b0207a1b40c0c00404001461242402e01d40010b582c8260350003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 320597347 1250 320596097 320596123
    0xb22020310030b090a0501150b0904110d02070311100c02120313050709050f010e0103120e01030204050d15110304080d110f0301180c0504050a060e040906021c240302060304150c02 79
    0x245509040234010001d008001c552004904504288582d82008080c100c41d00c0407241030102840003074521800c074401000c10300e110b5140d001880b402181040e041078044084850440d260082e4200b140b0380214801e541030f4070600c03d0550325500c0e01d142100c0c8030f01c0180c01418a2241c8400410704d40d1060340700178040c00c150081200c4580e0307984052110f540742408001d2030490303007d8403466154084d1158542c0c12505040c01340c1000c1e201c0001c40c02c01d001c0c0302d60556030890120003034840c1c40348602c0f8440c4038004c0145014a9031a00d922500703034a100340751b1810442541c0704000146282500c040e1926080c2c40710800d0b540396500d84003045500c06002554001a1404a006012900441c100e80450b00080c020355420303841c00340c040e201100b0100c522038205894129000004401d813004020100442200d2100c4c460b41d01440011901202d01414181554800c21080d14002541020132a0750444209a81e540c80c0e2900c1d443c40611502203040131030811b0400b03440ccc0d50b000b041c0001c41d040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 320598597 1250 320597347 320597351
    0x2060d02040308070506310606150c060b090709050607060f020a080609090f0709150f122a050f010c0b0f18070f0611030c030a02030d0b22020310030b090a0501 70
    0x80d201f1841351080c040240203907140188480f11074a504a40d80303286030882c004c5200244d015a9822040040700d41e0502c120300040003040300d5400c001c0c084c0b040024442c4190341581040c40c0065008c0d102c00f00354050540314101c0450441c0402000c0c0e0020f039540e00d0140401c2d5241c407500107025003280c0b82a50410b10030748200000604284001401c0322080005c0c000a20080d450403884400501440000c40f0484404842c007065241c1581480070003850585a11029201c80c6d05058000c0305041152030b803050803801285110714180150030040d00d60481300905c100b8080c0700180d03003002024900421842e01d200403c1045500704084900c1280901c108520020144200702c1d20703940d19000c2d015103010150382c00c3c03002c14843e0030803071508110401120316184000c0d01b40d41c91a00700c542110b006038000503001c00303031140a0088074010070040d25044415864840c1e898604255174221340103d03a80031000502074015900d80341c0041d5006080d000179420f200488580301d0141d070740140c2d140e41c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 320599847 1250 320598597 320598601
    0xd18120305072001021213030212100b1002070923040b04030908030c03031303090506030906270303060d0606090f021e07241d010e070b042102060d02040308070506 72
    0x102e074480200850a0141e0240c0681c0704055030300146d40e041400c4040025411400100040e21454034404031070340050002d004001ca45850341e015512400c40c00b60060740407400c00c0f02115000135818041d100070401c04a400c0c5c41c000858024502d04950300114800708105220038445042607443c05140203950b00118991980e02c0d8540d20b01c0707440902c5103640c1c004c100050404d00b5000c4c84980082c400c6c5081903495560b980000d8a60300705030f5404129402203424400d01c015085401d5030024000d151200002c020280b1803900c0e80002080325004e82550310b001c10400c181980010007510320201c0c10000303d0000b00489000350403940d0419800ea4000c1e5407104030541c2c070810b0b41c3c400c943c040345640300c00c102121410088005046845022512410300c130b0070162040b902070300041c61100001074611820090185051500d80c006400c4680070003041c040f41c0125884c8100000314580c002680200c24400b08800344251400c00b200c40d440460084100401070006081c0680030f401125919 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 320601097 1250 320599847 320599883
    0xa240303050c060708100e04080405090c04140a0b040315060f060f03050a090b0105121c0807020c0901030b070c0c08030a0320030601091401021c05030604060609080d1812030507 78
    0x545001e9078050068034151b041000034020075210550b00c10b21440c2424102036695010854509003515003805401010806014000c1c100e501c0240780c01e41143c0d10028949000d0f208140d41c425800301500b04407030300940e03100203078454000c90020020bc2c48015403a41d5580e6000b01700398803010210300041d04101c003160501c1d1141c010701900582042024013244d10300000c00c03281c01c0503800d020034903004004010f40d0280c5070000081070044503443e0b0b070f401803a0910000741401151514940310f00f05040040c40440d04500d00e150b800403050031302c00c0c0300c4000f0703040400c1c1000103075004251621000640e000c0310759154100484901d8080c078001484041210340780490302045404c0c03800101b072801d04115010301035080c40c0e001581801981c0d0000040e07000358100c0b000014401001c20f000009000d46820644213020041c03000345405404242007242c1183c64500220180040000c5070000c504031a040060307000060076403800c107224101d4030b0b2a000d089038010010646600600e211b1803400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 320602347 1250 320601097 320601107
    0x1c031206090b0a05040c020a060e011a010f2f060124110a0209070c060903030603020907020115030f050f0303010f080c220905120406050d06050301140a240303050c0607 74
    0x503402c02480115107506290500c8010200c0c04c2220701140300c0c07400404085001c0b407044141d0030381c400001042041c82420414079003102200c07034504100301d09408090542c1d00c050600035014100100c0102c100c90a003400e2942500020102d40c107004510001070404018448171013200c0b04512054119814402e0640d6103418008200c101d5801c14004000140341000b0302c1a8003d11130b0074503855511540c0c1b107110071100041d40460100360303034030300500c20352070078180c0b40d81c0c040351a1000380907450308600820300068040c030005140780404c80310074081210901038600c4140d40f000c00c882e145c0d80d540030304a047c01a6071094190601402d04400c02c10300384200c004402e214401d52030051030300a0002c410050500701030954442c02001c50204180d40e558001704000e0040366aa980c46040110415084501b981e01081c032980c5806680b89a80300303100c41c2d0a40c000c52100001a490100344c4030b005418038030b10b41881454004100100030581c010707001d40071b100002800c42d0341c5540c9102054075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 320603597 1250 320602347 320602361
    0x40c090302011d0102010f1404061a031b0f0603100f080307080313060605090106172202010503100e13060f050906060d0201020106030c0905090d020a0803070e1c03120609 75
    0x200040707018032110b2580045281c10803c205042c40000303007102c0c00c0b41e0184100c80300c62642c41d585043d0ba50520041c00441e02900344000c00c900c02d40d882c034034101070009503100c8070503900070307035103200c202c58805e460342c03a0229040c0304080605860743d0391402030260300751040c0b14014001da00d02400c00c08140700c0f81c00400d071101c0c80d501c11038492075130321401d20305000303442404c0040310929203480000c00c0300e40360100090300034845070315042441038541208444203840100344201e060401289004190601481c2c580103940a003020740d982e441700781006a096180b138105a800b00012014881260314040803000c5640c060001084a507000d09107403800d668043c3e4400e8403030303804500030400c0b514040981c90209441400005285030758cd40c1c802903402d400741d10060750329a840c81040103101050202c1e401e034111a1001d0154034640c0e54521030140005400c1d10204180040c4462264552030034021503c00025490000ba04092400030100038981046481c07041c1031250006505031039000d460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 320604847 1250 320603597 320603599
    0x4051315050f061308010b030d140304020f01301103060a270609020406180b04061b0807050c100c0c0b03071e0908070506030103030507150b12010605040c090302 71
    0x80300c0380d181c0002c000c002d40e11801c25a52103001000512200c2a030302c100080200242800883c080c114502050300b0030340b14842007001d011140f55020300e03c0d40d5000444e980681d04450750034424607420012280311404039502020160b010541a000c001c01c81e100c81240a05a10180450144c0c428083d0b401e00040e0341003030300040c107004d040c0020808840501c2007451041d43c1040b52101c04103110040c1d070000d41c85411090b40c00078040c080954030411209030b51503040000b0072098030b40320301e41140d0311540c0300366801c122210131a0081490310b818015081908449101e4845840f814255103400c03134a6001c0d0710030045d000e0440203690085034403000c03564004039003114107841c0a540d80003d601c01003000c41082003050401c016020074900b0079114600ca13035a1008154203040d0280d16200860704020701c074900510040002035030210803111016440060302d80d05017200c0311004094914172481c1580042d110909001000c4158016002c0f140300300c030140603180c0028401d46022981d80006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 320606097 1250 320604847 320604881
    0x3090601050f10140c0d1d04020f0d1109091e0603061303050c16030c0611031801031806020a2c100c030212030f070e1009142202040513 60
    0xc42440741c0134654001000400703203c10781c03411220b10301c081c1c1000c085000003404100c0301740c402000303601a00710005507903000352400c503d441ca9038500903409001c1c01d49424074843c1c0392010010704020180075921007000c01340216429007003102118940500e40720800310131210b980001641850000360b058020341040180c10010f100c0307910121100e90000718100700501c0b134485103104030982050342c90001c1d03004554606c0c4250404900030442c0a01036922481030748288100800060714040c0c07050005001d003000a00303820420007010040440c4170025002030b10101e11001d4540e04031010f20458894003044231862808850101c0361027908180031504064401c4964441c1c1d4000d580603401c4500900480d0500a046440c0004d0769104031110100000d40300d00703001c2100c1e0802d5198108940071902002420750a00c001801c0350315505c1400726500004d0402a87d3342c86410441c1c905850380030031080ca00e4070120041c4043d501c01d00c5180c1c02158500e000e0b4a000c01580318000c4204224004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 320607347 1250 320606097 320606119
    0x607030b090a0c1e0c170a080907210312240614030103080702150307030209010f02010b0f1e03030f040303180612050403030204052e020d1e02030903030d0203090601050f 75
    0x41c1000300c0413001c14100600c0307113114002e0003007204890080b070f5581c0038194041d911420400e004115800103005504c040e805003805101d903065500100010141c2e10310f00b940c5540036814100c070004141d00060006502d8180b0840c05025201100c00100044209211060340e44140459100342590750784410078a0a000500028003294000d01c0720314001030480c108800c848001c4202540280c5100d0701182d4005034906055800481c1124204440e000800c5500000b102007808480d8884546208a1001c01d514a444150b0304480080e0440038040740d0711030051840c08401d42c0d00a000c140e02050621420303501e0b400f0b0200d81c1c40295565543c0c4c4e2040c0e0f050404110019080151044042c141c0074040824a5250340b881220f18147c0c8070f001107002c030700900704010b100e4102c50151045405c0b11700c103c24030b035800440c81020301c201c0e1400c4000400e0796407800c0f4110300461401c1545400300041c520840011900903500840818082d94040e0341d03103108101082113070003a40e5030030402903c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 320608597 1250 320607347 320607377
    0x5010608060a060e100e0a0b12010f03150905030d11070c08031e0703091d0a050a020414010e0301060e010b040305010621110102072409170c0904050f0607030b090a0c 73
    0x88801071764910342004d4890718140750001c0d00401c000d40006e400a0404219404400200600e1034014000c090071210303014116100c000b11803811461211569440c1c2d2110802c0000800880d1141c800341c280400c94045444032840f01035204840a4403038446904011496034070200c11940180500103004440b46030700107004034a070700088816424001e5204c000510100c0c005000d00d40141d001200e411f040c5042c10780d0030126140546800905d610500c020b0088160f1080b004411380b0b000d08049003010000000203001d0039940e0000014035150000010314041400702800c01c1d01d204800903c103e076141d5680444800d1000c900c41d800140515034400400c18002004448440c10f2054807c2c9680310241102c918038224685460026040029007090b54440c000034007900c070a81d502c0f05000c0c1c44803a22a6680c40c00f80300548600601c8000c1420000708104156000182105461403498859809801092603031405805942244000f99418982d44110b058440f8682c40348203011b0304a003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 320609847 1250 320608597 320608609
    0x30f0612010e0d0f030e01140a09060e25120803010501030f0e1606020f01111b03041706220308150307050402070809041d0304030b0c0906070605010608060a060e 71
    0x690060300c6075503250311801e200da805000000d00c00d03859480d0b502c0403460f08140141141c2e500b0031443c0859250005020a10042c400c0158212000030008248000d442c10850020b1a03400711204c401d11544500e000c95280741414005480765040341e29400c981e0b038800441c021a4012001080300c0410801401203600130b0784044032070f1600303c000050451030030200519001e260383c89a0001c0340e5410040005940c1004a14410f00344880240000a8071641d5500c0a0050f94807080740da000d20030400c0c0102c1c1c0f040055400a010110054180000e12003003141c03129815140c1301140d8802e40c03e1380c488086802c0c080c0d501117906075203030202c90344c40c4c010400b03031036600052040d41401440000034590f505c43c000780c0800c5000c0c2c2519607413404414108811200c0100000404900014a55210120100950741100d07048080380841d0768610311070310385510403454180e6110a01007203480600070135920881c161822522201029101d06081180b900704a11802d0b0024802000c841c405007000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 320611097 1250 320609847 320609869
    0x703020a1b050c030105070315150e03030a030e060c030403020a030c1b0b0d0b0a1d070c1403070303110306131509140f0106051e0711030318011103030f06 68
    0xd15181540261001981c040c01c0784000341030340d480d40104015120361500384900f82c1c00101900302001900102c6018480540380c41c810b4401018045510031402c0b0700078484070f004403200500307881e038510318503370f01400904643d0710b084ca82d80300f50f000003100c06107905c0841b070149801d50000c1071909203555044030100720004013200c603515100b005100d19409194040d015188456031951103207060803088003100e0308143d0991103a02c10301c000b0440319000c1c1700c11844554180d0a6200749541c3ca1030700341c5480080e440e006154990407042080d200310301001034039407140304e40da003800500c1c0d4400c80301040b80420764025a001d2003844000101904a0b4010100c4800043c6105501c170382d40e4050904441034240d003c580803400608002001249211080c00b6003002d0801a09064102003069550b0310080300e80c44403848005208002c0c402da29030341c181ca0140c010100c0b0b0340c40d1480d50040d1500000031409a02141c5082e00200c4840004802d80f40315608540111003141e4840003000380104d01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 320612347 1250 320611097 320611117
    0x706121a0607060218040608031b0c1507030e0303070c0503060a050103081602031903050c060f2406190302040602010b010302030108060a02030c07080d060e0a022805040e01090501030c050d0b070302 87
    0x24040c85141176031600d003c0c050003059142d02954545801c814031200c183d4541c100e4000307541061103100103950716440030344c0c04007000e8410152a4521458107030381c002807120880342d061001054210400611480d05030555200f54140d843c0b9448501059064600a001c000c0000400340700840780f1a030440035905906000504450020b488aa025541c012000500343c001400010380480014001c000e030319004820050b0007845c07850715032030040c40300a0f024640550029200303090381c00d80d0b0715074082d00d003854203c0c5c9600700c0e51551074001070020350040c41a4001740d402d29080b040346602a100b0b49040710030b01005020555242809400258001028003110f1070041c070148001c5207005014054200c0c800c50001085428003404400620006000e0701c91603004003d1024080c2488008005401700541100140e08100c001604c0d9809190401c2e0b1030b0cd4040000014a17221a80066040b83e00424080b03040701e80781c1003484240a40103c01900c0c3c06100404503510a10903402001d0b0184 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 320613597 1250 320612347 320612377
    0x60412090b0313020a061106070f1709060103200d02100516110103061a0909070e061309060501020d140d1104060c0b0702010c020c01050d09050706121a06070602 71
    0x920340c40d091907079400c103403401c0c01a00d804054001c214101400c4a1001d4400742c2401c0b0040d060034603020f03550f42c2c801040b41c802c203c602c0c0c4a8000e40c6018901444240072952800c0d2846c0c0307003d00c507140d510882488140c07a080e81e0414000d404001c03001100c0034041c409000100b45074299000c0c0165a20003000e0101000300c104030824981e500c9400c030780a098402c43d003030b50f000110b8000060542d2450f4000c0c50490350005280401f5025603000c0364180081603a2442041d6038240080e14042004a0305540108002441d1102d01a09544000c281d415040c0c040013010b80351401240d03600728040c0f03a00e0101e102d0200e100d6405000360060280d035411848042802c1181c0600410705da0450760051000c918072203404010464985107041d44014648000c2020040700c8100a44c0e400300401d000341480b400082d00c58000e031641e0080208541c201e411260a40c1d07030340344000c2140001032a28502c640c40c2250303800b441313004d00b140300d100803200412040c24507149032200c800075800b803105052010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 320614847 1250 320613597 320613599
    0x90604062d24062c0a050f030c1210320a0207051534120f02040303080f090a08090609040209040912031401030206030106030e030c070e06040c02010203070206041209 73
    0x101d0802c074684060f100e00d5076070142204080300003a41308034900c0030200b00e444140c4444440358540340c42d1a0100c8008a44581409a4a1020900301240755109030b411402c442d000041018002a40c0c9003100300b200c100300907041340b6144c05407821840111038119100c81c0040c105106240001164000358070803401442d04c0007070341d60320b407510502c2511055804107010401c494410846e03070b041c0700c02107554003640d04010103110348445a10030500398014018928a404003040942e072012203603032012181195202d4580c2070103405000112642211502580001a442d0360003080d203880e8603601c13005042c00c046e046400c2000c1e0340c01418209030060384c2401070100c9903231b0303501030780ea80280075842c44020f07144400402800e0316040d002082c02d0f04400801000142c03180b800322411201c43d85000903040414001950842c40f600300c0300061481040d102007a08044143c2e0140124400c803810482031b01d43c100242c0c242d00048890102681104c00001d000c1424441040890286031405803089 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 320616097 1250 320614847 320614901
    0x20912031303030f0302071101030e1213030203010c110712140a0303050601140a0e09150a03030e090f27071701050a0e070b0304060b041103090604062d 67
    0x190000300c0c40c041940c52814080040c5034000507144001c0101745015481c0000c29114034040d04180300303000703040641c0c1d00c1e00c0c0d0980030001e02c10100d002c24101c2d11155540c4010031f114030400c815000a034400e518240c0e00d440b1503030040b07103012101a032410141030b40c0c515003103207651905403000701584c00d030592070030714a0250780c140030000600d0310a072800100c50404000041c400d0000121800350f003038003008039044040d0401200e2582180c1141c07004003d980b0283c41480c050200012180c002001880202c00c0581201d10050034000648280d60140d442040c0e040c0c0c0050190740010f0000b11241ca4019070044400d42e15a600c1d0001c000c40d0441540e4040c64055950803074640b2410b039540b00709003c401e016070700400300144240c034000d0400034101005080c0b07500c40a84000d00c6540e9a00183c0720350784541c3c02c01c1e10314042a1807443d440e490204003850f1030381c00c201c0c0d0440315245041c3c081c01d5171032400c509050b4403911641806154a04158000c402030036000b48189165404201400d84 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 320617347 1250 320616097 320616103
    0x3020402031e01050a12080306030a17030a0c05040b1c0e0706111203100e070e03100533010e040b0a030305070c0e010501020a08250b37020912 63
    0x80c03038000321402040301044820b0032060340182c10051050761aa00c0c200020181c0101241301182c101010581c0e941b90240002c6ca01660403100401d5440306000c20000c00390100003840c8206440c200c01d01c2036055000d000c0b942d920a50050a905110606c0810b6402201079212140d1a640300c0d400240c400440300c01ca403804007190300410004001c1c40341e409034400d0600c540c600c1c00054042090550510345541078080c003080c01030b0113000c80402d0001b40c1c0280304810b1950900400b405071180c04c91103559400c086c0508851b0a541010814101c40484020a1900c21020740d82620406100b011500443c1c102e501c40007501d034803c2e03d85112408580c1d40e0500c01000f94804e031545580c3e55076619140c00d000c20998060349540c2d400300e0041015036004942c0d90840d43d842300910ba80c401c982d4078a50280354407881032507400c0009192004c10404144619406240c1c0381d840d409094601191040d85034100c25403104080320324030603030f901141c255000351113030074401000034100210804c00d03a89 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 320618597 1250 320617347 320617351
    0x5130b0103050c040e300706090308150f09011a040b0f180a12020105090604080d12060b0a050702121908090103051b030f071404091a010509090a0c090302040203 71
    0xd0310b0780143d600742e0900c0c0380c02e203d405c0d8221008005171250540000c40000e00f980000041790b00e52081d045840c00c050805800c03510325139801401081840002d0900400e09402128410030840c480c05610001c1e15100c8802d41340b4a0005001c600039a00b04030254084030100050803818402c2840302144010b0040003400011b0b0341104c0c1183c030755000c03801c1d1001ca4424075404601681c856582800908501c42011401507028240555240f034060045949031160f03a200e4a03150043d03090740585940c5c466989481d00007054018040d0940f200c1460103944540216000410010441e032001800c1c04c1401d0f00c4221007074400c0e0380030804000e55510844480c580d04490403d070000d141c15440d0380501c0703840d8000da01402080b41c0308a040a80484611014203d4030481d0200d80c000382c44a481050281e6090410302103003078071150307141c5554010308a550010700c0f01030b07a9000b400c1c60a52140c4269004190300070102c80311038076130b464014001e1074101e00d988200b00b030481010000d61188c1c00154 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 320619847 1250 320618597 320618603
    0x20100c2a060606030504080304080903100c0f080702010606020712020301060503010504080304140607120e0c0307060e01171012030201111201090b100203030a02090a1505040812030403020d0305130b0103 89
    0x41401509441e01e00c08030340d01c0da04000141403802080c0008036400a0503243d102c0d9000300310a544104c1344d0002441c2800043d1003404290070105c43c000703290743c044c2e00500412a240c8034001c458603582026400e0b56080d00521006911202e41004016032081c00714030418000350000680340d8541000ca820340d4000c030303020ba4a07900d00000307120420050782d40384411134030f03014040c0c4034605280e900100118000d290459039036403560400c0b50a02000d02c00c810f4001c100030101e80d1082d0383d40002519042c0440381e09804140244051104210301c80151441441d071448450401d0b401c004c071200b640506208140c0440d980c603407000701c900e118a401003240c5a148a03025819605d0408a2800d45214000741ca01504640310801030f5960000140c94010080303150168540800e800840d401c0b150f6540174003070202e0360031001c0c040980c0160040043e204c2c404196451604480c600d0302d0948019640200140d10030189020b000b4840e500207608000c245464100e042d01c030340c075504125002a002a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 320621097 1250 320619847 320619917
    0x70801050307090c021c0302090a06120f06032105040905010f0311010c0c03060e010b0a0902070b0108060106090e0c0d09030e1002070506090f0a05120d20100c 70
    0x14002803a0400c002c0c00202601401400300100d143c5009484803034441c1c55600745000e040c007a00d0303030724020340584003139041c05010340e01d10f05d80c6c0340c03070062100081d58410b1842500d0310301c04010ba410303203005110650b5007080c2c0d414540810780c4055480f100c142094102040030034403000c1140301607405202c0c002c0c41e00d4502e03805010704605180c0c0d0031210344580300d4180900c40301c9010001c1c41e4058041d08030703900010002442121700e4802409014589a0103600010b02e21012400c031581e54040d2194030700a13005818076a0300c41c090260380c0da20030701034200482e842e66010031100c003103404260b03442140400050305120340040b490382943c641d05811800701d010070b69400800c1c01e003c078a505c800c0d00c3e40c3c0700900c009032414020071001e100e5004000d00550019982c03914586440b01018010a400b800080598021650342c81e111252400305200007101c134080c8807001c10b10248aa601d003075000010b04480c0350b008200f04001e18800c1584018040c4546040341d240f10350440000c043d40c1541c0170 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 320622347 1250 320621097 320621099
    0x10020a1401140a06060f080c0409020c151008121c0e0c03250504090f24050c030402010806060307140a030608060c071a0a09020618040b010e06090f0a0b03070801 71
    0x800c2d01458070007030204061501e4048208480da90200c10040841054100481540c541030840380c600e100d00e070482203900b0b000013251501c01c800056060040200480359412903200c896126211000c140300c2c05180780d000d000020340c0091520300a001c40c0ca004103840702045a440b1802c425610404e21160786a080307900c5080032801c3c2070110390144003030300c071070141c403503400325440c1030b1400203405440d0065590358409001c0283c001803084c19950031082240c5800c0c83e50400b9800301d00c0303451901c00d41c6d50a0401050300f00d00d0342420b47c0d001c2c46e0305844a9a095641c04113100090300002c10340000c002d44910001c01c04140c1d48020324001090b0303a00401c10301c3c00c04d1605031401001810fa074000090802c9140046858034220284943ca00d40745070741e072622040c1140000c1e00100344081d501240c00250461190b000c0306035405000e01c150340901c101542c200055444011a00c16203400c803c08110b80340c0a482e003005070009041c0000d04002c11540c40d5040060190012503000010500e0707200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 320623597 1250 320622347 320622371
    0x120f06080d080105032508061501020d020102070305042309040b09010e060115050c0f01050c090103060803090901050609040905031602041401030f230a0c050103230610020a1401 78
    0x801da00500c001030074100d141d54940000b0035581d400c0040396a03a0201140c00070040c2440f940c00a0f4010720200085660600f440e10741a8003080f080c1080c1c3c0d016124052212802c1c50040c000d440045815856507400c0626106002c40c1002026294080c84000709110b0340d403aa07a0314100e14025801008000c445190650300303103003119082c44041d031039684907100406c85c565000251400c54070b040d20b8141e8803004042d003203915040d100c80c0c0d442c4182d420102084268407260002d403246200036602401050383c1c401c1c0c05903ca114650b6510b8101201d90300512841c20100000e01c4504005040040d4038111910703918115000009242c08030705240e1540340c254a02030282801c0100040c604030129495591a01c40c1000400002800c114480d00d2031120900007401d0310141c03001d0702c420358403200350a28100d8940703101c60040358007003813514800407010003902e007829010000c0f5601c580441c3d150f4404000c40508040d445208600c650103010380001c428140992089141c10000300e4041c052031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 320624847 1250 320623597 320623603
    0xd0e0619060906180c171302012025050409140105010506120411040b0603040819030b100c06091707030912020f190e070f0e03030c0a12120f0608 64
    0x390000030711606001003841022070003041640000d07025440014801e041c4502900c45280312020b1b201100040010862030352041e10005081714401d903505020b01e03501041804c80b0041e40446000750b94030110700301c48a135294a01d1840c40c40b45031649403440594a40010342a42d9004a0807128604410180c040301a000d024640c058901201d510b401d2114441c1d0220a1000050014203102090546840c1640300c1c2c0e072040c200c9000280c80036541c1d28160500418545c000c40501d4114000078085104440c42880391254624000b071020003810039499003100c003c205840190b560a9490bd00c2c0310018070f0b580e828a5250311100140d5031910b5040c01c02801201140e03210340f4103484400e00300b02c0181e4070a170100840080465503461840d1041c03501c000600d10300d80241000708680c600f440101c58124031003003610b00c115034950602d02c02040074182c6038024210030840d150b002034021000140040c0710444c02410518101c4d45036402d0040e01c00a4501001c2c48142960307a4010500820000b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 320626097 1250 320624847 320624849
    0x8030c1b0907020604021c0c03081818131a07020106180605090423060403030225081902030d150f060e030c01030f11030405010c0906080f010b0d0e061906 68
    0x115841e2800789080000030f0349414000300001e01c13a1541429014103031026030611901c00b80c1001c2003291840e00d80ca0001000c0d0703c040c0707824116900540b026109440d0200c40c40e0015140700d08651015260707040025070300c800500084a80e81c403195a6030610319080c0c0b458502c01c4820398004a18245846102c903511130003a000d00c038485051820610160f01c0e040c58154104d0752101a5810080100003003c1c0c04040c00c20b10480d650103207909200030315a068011f0300100312128881e160741c03140108031020200f0b0701203000702486014011110071010420003004101e00c07500590f4a82810406208111110052408508412280c040c040300344200c0301c2038040c001d0741c100401c507540240c0c0080c3da00c43e10850710b17034100b5840382c250550502c5941c00400444031140f04c00d1b52242031a24085010f003001052450001e40c5020002a182d07108944c440e0059000030a103a505901b010121400c6074041d140b08a20141c89500c064500442000b030513100344c4403544a03103203180d40c40c0000c900765526 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 320627347 1250 320626097 320626099
    0x2012307030e060903040303180302100c020301060803042301201b0103050c160c05130203040506070c080406230408030a110c01020706080a090501050c0a14070c030f0c08030c1b 78
    0x400004c0043c2d08500100712420740b40c05040611120b240b402d246c0b03080e031503103800007904224825907005002c0c2c0c022900607080c500c210000d00465844150050383c80c056480781c510b4050035201c80c03400f080b407080041c42d901c44040c0740c52908034500d081c80094140341a11940c445600000710381c02c4034010070101d42400f1100f4a02840542030442c214480b40c000c00c1191441010310144040400c62103180004c010301c005004640901900c003503240094100300c40503952400b60300c0003d2007841c072407010b040c250303540022014101030a0600c11610300d5030000f510003202c1c1d8000c42518100300b038403020344010261341d40110b5a85440c0b20005003844c18494400c01e455020448104060f80c02003880d5003558060310700a601e9503218285e01011706030b0500c001c0d0a65103810140b0000a44840080c005d502d8141c94030f038a9502c036000003080501c5416800341410f04100000e000240d84c0c200349151850080385c00a05d49601c405000c0c5c1194080002400b45a01010740c40103102c414a503204800c0310 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 320628597 1250 320627347 320627353
    0xa090c144807030f150b030d03020d0b060f07150b03030d0204080d08060604180b0d03020a02030706110a0305030903071b0f0b040f09180c0803030a0624030c02012307030e 75
    0x440c0d0b40d1180c108440c03120008140201744403e001509056a011140a0340020101d98000201e07003000b03002540402c0d92070041038104502c0c2100e80c2080001c0300c0c2070f5120001c4892409950351076039440720807203040c201c001c0c42e1030314094a026541000074102d5005115001aa43d62920700c103a03103004d40f1980c1900c1803004c02c0d010003e00b41c0c5d50303006076402c40b102030b07074900000410b09031214011328180382400e03840900c080324034051550014003101110f10940440749001e84a8070103994080c40e99004d021960310814828000a214070701841c0c02500640c00c680c2403100030303990701c0500e100302e040084580c4688a002c000940e0900810170003004600707400d030f01c1c103800e2a1401900c124140504407141e503d41d16801781c40ea03218001611801d80140014006588a51130251240d20545ea84014a8206030011501210044103030951078031950f079042001c0f00008055000d0302c0e440840c00150355032280041034400414090030001d21203a0300442c03540c07401000190441c3c4200140000701d81c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 320629847 1250 320628597 320628599
    0x51c020406090e09010b21161503111303020d083c07020d0b1b0c0102040801061a2b020a020601240c0305070f080c0a020a090c144807 59
    0x1f40342c414a001a0881c100780001a1480c0640880d140c981d82003220a10060706240000f00512400c541d0f03a010100c80d5170a01c0000380501c0c0c0000075025030a032000031000c2c1034604100503d8035420046a181c800c000c41424010164245503869035000c05140380e42003c01354014840745d4042c01c002c115055200c2d9241410300c0c42d00403400340e61070341c080280001105000301e500c0309401880550052003620030300341da42e040951700d14081d400c544030356025513090000101e90542224840211141480d007094140b140c00703801d250a50304c041c0840001d50040800e2201403080c00d000901402c502c84c2c000f00241e501d0321040c1d80e118440e46402d4020440f064048000b0298010941d0b1102900340c506075440f641c640c02c09088040c0c1c510802083d4000004008091060103e1801412130003100d107039010503662850481954490740e0601c4c00a03040c076814404d1400c4140240420503400001000440910b0802c01020042e081088070f04484800d865210021190404091207a0750390180c0152 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 320631097 1250 320629847 320629849
    0x609010b0403060e010b060304030207030b370b060c0304050a1d0c1e160b0601020a030806010f05040302090106050304022e08070210151a0c0a03051c020406090e09010b 74
    0xd4007460000400380c40c1c840107401c1182c1800d401ca01e50b49070001780f0007507a0b41040c0c40e01951b10b589510049641c9038010300044d4403000741c0034400700c00982c4990624a040c05115007140390240c0c02a80d0f40f5841d5541007400802e0310b51b5000fa1815503441c0001350f0b40c80d0f081100b000030303400040d44601981c280c8406003000b03015030740c0d0380c0c5a04005c1407180c4c81d459010903203080c02901c5c5892005694080081904a4561289180c2c0c0301070130300440e140d0700e15444001c012070300d52070f4145001d0003081c40d003c040340143d4401c107020109130341c0da45444c030301f040d4607a4006041050203a004000040003c41480706510b080c03542480d940b10520802d800c83c4041e95402c280e80640c20356090113016901c000621101d000b8400d00682c040d81d440100544c603120a4186440700c143c0c010342da103552101030071140c001030308011134481852003801000b000e0301c41d6034103e9095201481a032155a45101010300c031040b00d00180000c0c00703158031000b8505003406580e50f61600c0041c030a1081c1da051507501101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 320632347 1250 320631097 320631119
    0x503060d03021603060f1d0c04020702060d0207110406090b0306070f02100f0b041113090c0c0f030c1401020c07120516080c010e01031b0c0c0b070b040213050103020102060a2a0314060901 82
    0xc230700e6003940d0140e251102400000c0c2c0c680541103500b10a9400002d084c0100300306903020140b4503008031404c100395503c0b0b1901204441e0f1100da000e030168482000f1030711440c0038071190f2490354031a104450b8101904410710301541c207903100c01d181c040d1701c4540c50080d43ca001d0152074050381d41180c0c124101015803083d03404030051840350007103469450900480251051942c25031150700426280368840c607502e8020310802240c0d00c01d40e02c100d410714100388510018021980b884111030014a060b078100b0680606001080104550030700c40d08110010300c45224848000a0182c0005404456002c90001d400100702d0a400360406181c000c414030074456000442001c86681d2814049134212071401035070001154014608031000461407004103c02240d04620446c42a6419151a0f0a403200c480642d402800000d02503000f41c400903952440d90743c000a403507080012809625410800841200c00d001c141020010307032183e414003001d6400e00c0e10203810100680f814a03082d89086001e00c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 320633597 1250 320632347 320632363
    0xd06092301090f0b15030907090203160e0301020702030d0c030f09180b19180f05040b04140322090c02070b040501110a0515090d08010302010503060d03021603060f1d 73
    0x2070035943d107440c03c40c04080354041c0c500400003410111064071000180d880c5034000720b6084030b09100d000c80120f1070f07502d14000e07280a03050000700a01000d010030400d07039002041d030404907003544d400e0280b0005039604000c0704500d008980c885005440484c03c006120a048252070424462a0345041000c45000c900060048000c160005605401c40000030803c00e60201d101508059028012a54203941a40b16484030011603003041142e0441c890f00c0300303562040754041c02ca6200280014003003800c00500715070ba0111081075034a010a04400301c440c001d04003859103c0f40008440602509011f88511101c1110600013003200902d0840008024481c500981d4100b00303942c0b03680d0302034440070080d01e041c8035486015952114003021619035580d40440d00015503128410040c00054060450503050320740694601d451a95070303505001c41444031840c01c608602c40d500b01400c2c0c02500d40c1c80d0401441c400d0300049141801400b60320b0540301d0b01a41d81480d44e64100c08031004482c00990741c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 320634847 1250 320633597 320633609
    0x611180a06030b1c03180807060f0912060902120f010f0f20090301020d1b0905060a0503151807020a0203100b060d05040503130f0e070905060724020d06092301 70
    0x1013981c4520b000c5621100c85850201c580810035808244402c0c042581030540d541c581e5006003e421040080382c2c0084c581c807980c1700180c00c508080c00854219041642014000780c5155820100300803218035041d499105e002050f55200c0c0c0d050003450060041d145040712445050008010105242141d041d109080a66a40700014000c200b074500b901550f4520500c08010841014a0700059400c0039100010400041c2d8902c0086070600e011002c1c3c8130040c5103551660304544c1c81030902d4510000c4620300c207603c8526941c03400004503e00001c14414603aa50181045803d03d1044c075240c03041101021a48900b8628510f000d80c803180300780d441c0c440c2218008902e984444c10010f01b10f1041035604641030001c21808124202c0c0303940b1150440b035010145540544c0d84403012107800e0440d02a0759400030041202d0000b1a446c00d180248948410a505408099111280c4101e0380000c0c0342d0480d8a86400041114180a114035000c02c148001750540c0703211a08005d030000c090501420b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 320636097 1250 320634847 320634889
    0x303150515120a0f0e0703021323090a0b010324050c09091306060303020312090c01080103020d0c08190c081c0c0302240108010f0605010e06070611180a06030b 70
    0x61421001500075061380c401080c0d0400c004808030046a0301e81405010a0340070321401c2a580b119a036152040c0d14020440d039050144040010680360140c0710040c2c0140c1d40c41c46400d00b100c002c40d02c2014281d000714812030000d03002a47c040c80e54a00010304054664000349068204501c14080c0d9007201e0301d0750000c403a0240a556020079a0505010b503401c040c01003441c00d0380102c00c2540000052015075505102c041040da00c5680c6c442d52001810000782c00121907100400060a06603107084541d0b00c40c02a0003255030f107600901d440d286a5080e54150b0b10584103a04c424442581044030103801000c020341458186240d5407a64200c50700000320130058074681d0710703052620902902a1820b110381301340105c12001c0c00c2c01010941d007030041c00f00315480c24040c0130807900d50b0321400c800c0300d0040e1204141c248003801000301a81114405a0340241c40f800700c403000e0310186000388a250381d198855842c1c44c03804402d001c0401c40a8000c0030a1502d403040220495540c0d000c00040b91f20f480400e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 320637347 1250 320636097 320636101
    0x30105100903021f18061710030215090301020d050a0209011101050c041a0d0e0a020906091302150c060103140c030304030b0406150b03071710030308040b06030304080a030315051512 80
    0x200720707400345c207070710000044d0303112a0008945654440c80f80300d05540d400151800c0c503120082d03285c8042105100023540282c0c0741404504540c40d441c0030b4a0076107001400181400700c41240c403001da0f18102d5810981a5002551482668100501e81d840640400007040b00b4503200320840c81601c640d0050010422000b00404412415202126071400d2040f1090008003004800c41e076480d094020124411030f400000502e1300d04042c14014480e4100700c420b0727190004903400348400070702e00f0603452030746007800c003d082961402005018004c42c81072070040940c0103507203082d500304007110000c540301c0e400401040002c0f4211880540e00f1903041800090035801002e030b07556010846502c84025850b02004006010341c01c01c200c990441a01c046035541a41c964441c079103980803600004020402000200c0c1c0403a0240c01c18590095000e0202c91400f034039941180d20307180e54000114000303603c07012074134150107480440d01d0060006655495507201d1202c1c0b521a54000c040d1030000140403c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 320638597 1250 320637347 320637409
    0x30f09091b07080315040b0f0409110414190209010c030f1e031505010e0319020a0806090f0d0810060804020102010b12011d03030412080408040e0c03010510090302 72
    0x1441900c411841c041050b950b41c00c0380740c0884260412102041c40ca50b5080c902016800c0034000d00340ca0107401071843d20340d010b100707082000401800f4030503150740442d04407002d00b98880388130796000d000121041d400c640c0340030a140c12200070360046003070000c1c2c0144040704099800148040c0b11560508081580c03840d800000c41e2011840110749068842071a0700908458040c0d00000420782804070640417140c45100544501c06520010b603015402010342030307005d81032201b080c1c1b2420b02c0100b15525460360303111014a04081618401e03251f401c03d241080500d80100112108030107281044180762030840b100c842004a41c3c8244800d211800b800601107a1003980080c100c0b0400610742c4a01c2c004203001d8600a103481d6012111082c1c0094050907152800410350b8030a5900100e402c034404043c07481140c014401030401c40d0519014400810f51000d0f60958500c204610008907850358908800c000010aa4003800d10070300c200e5410a1000da1a000e030050031303550015803454041c403a03440b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 320639847 1250 320638597 320638621
    0x1050a23071e020102060a0b0409021011190b04060203090102120a0b1203120c09011704030305100e0f0412050405040f02090a0e1614070503071211030f0909 69
    0x1645121000d00100c48024500d4904405040c407140600b0610b240c0e18030986540440d40d45400020b400742c0c0c09000014a00c10032500100b0400b080640b02003460704040e80818492460344603c2c0c40899000c40705481882010462010058460002200d10001a0b1203001600c14003400140007250000001209060250101c900c0318460b440c80c9200d524041641d1402000045c2c8080d10034202c0c44e00c0705214010010035110007119200064405441e20110306045d41e000c80c51582c11700401c0860441c0740130185092a2099000740c5003c43c0c01d142c8030b840b100d01d0717007402d070030900070440303644103100f41c16000c440b407194010b521007041c00b840002d029080c0c5040c01117134070a95201c0e003061250758540704c594000d0f02107400243da880c900203403190841000300780d088401e555040340f940300c918009807190001ca020044225a40340c6051207540b2800d003580e020200076204081c890b500d0700f0000d54080b205803020200c6001450604240001c083c22900c5250401c511075803005002c00d481c01007030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 320641097 1250 320639847 320639867
    0x70303061d0a060f081b040b060703030b0916020c1e03030406260103080f0304020a05060c010e060f09030d0b031c091e0b0405061317030d0f02090a030201050a 70
    0x5030012660210000d07060419040c01225114031490410400040b000c0b00c19100c0420750748400054114039198250502c5044034030082c0a03481500d445c0d1080658031400700034240c0500a6070080340064280c401e1000030f80e0040c0800c130720342d00c0c4601d60b45101035010030150715601c02142d1124134401072a001680070511900c0d6144d041c00300044c0000c0c801e8000c4044108584021205501844480c0c000d640400c42444050130b42a01000341845502d0004011a88988002d03c035103a2242c44c0d001017041e50f0000250f1140d580e546001b488641c030010800950300c40c41050b1501c40904d003805103143c0302d00481d60368003803690302c580d494006607400780401b0142000c00003458081c1d5120134002400c40e03002c0c2c483c0074599a2a000b01000d1404109000c4054a290b000302d145014a020b06025aa034000c050b01c900d600c0c1e107442c002c520b4004645d0300150341d50220000f140c0321601e1484c80400c4409441c0014209481000f0907030351a16030900c1c81c821280c090038060b44072002d5241c00d81c1d2040017 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 320642347 1250 320641097 320641109
    0x30905040e15092b080f1803070f030e0307140f06250b010e060105030103140c040c02011a0405100e040503070c0306150602012c0c030609010507031b050f07030306 72
    0x2d140208800318100180680004e80107540226030043c09101d8840c0d2694002c101c41e00050b090f030300150610381d40000c5140c00400c44203076210a807260b18055400e541104404445141c4103d03540802d041d8056070500d01030000301d0143c1181864a00c089060006007084d56006220042070011640c2d9034800341ca1203050420715401d8241c5400302a00f04034150310504840b4020640d0000c2241f41f410704555100700ba041c0c540e146507034296201d0140d0f00080300364144c074a2045041d0030030280c80d24018003c416001e90004903040c0c80a910401030a000a0b43e42c034062498201001000301c101090001100d000300d4081c00c4544541c00c0188c01d601c511040900750010003038000040200952003407005041400c10062000c1c1c43d124120b00740c0b1001021502910440c0d9101c43d09800388d09541c1c140c01c03080d0000c80c0c440d00101c42c042401d00744220b550500381e035940d02c100008140c141c094030003100850f211840380000d8400300940f80d8013410039040101400400c03e101050700951200d40030303104e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 320643597 1250 320642347 320642383
    0x1401020706020d020415020a030c0b060a180515040908121b040e01080601090c08060f0609040e030c0d02010e071206090c030501020304122c0d0b0108160501050403030905040e 77
    0x2001101003c007a41c8144603034021810300d540881040342c800309a4504040e0325980d258055483c86d100c04140800190031070741d200c60100c00004818801c04c00481c0840c11594000c00c040c508914041e250044500302140103d00345001800020f0340d95080303410425a0a0401701540c8035950901d400002c4400c0b0000c03400c1001a02040d441c0345190403d040720701032021112140e032202c86003001d40e5256200d51011880301804030309985400641655801c00291506003030a043d080083c0a6881944000850350030015089021038428010040104410300091107440e0040c02007542e6030503d80300b804550080054840c0c00c06c400c82d003020340f0454011840c8240c90b0349a080141c001e50060318121120440741c1000b48819000d40030b808080b0201a1a41d0851503085081d080380780d00c0640010781c8a10314900c1c1c0000200c034880c1d52030180c49048010410b100341c004c0b00410505180d081b56060044c01e20082002035848205201580c4050342c0120b041c4010941e0b0904d007814904100601c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 320644847 1250 320643597 320643607
    0xf0b07081909230105041401031103131106161b121a07080108060a0c0212040e04030909201605011121010b03040b060607140706080a0203090a140102070602 69
    0x1552103207056058640c883c11881403046030b403905085031140c210015000c10f509200c03c1200c1e0403201d1980405078018140842c010211107140b400e5a032080700c1030100880c24524400a200d0384100620700c2c0c0c00262403aa00e060050300910301c03002680d040c000d10149100084a100881407100c15000300729518600e0b15400480c50441ea020a40700c0100d92250300a0300010341c02407254030030314100e4a41c0360140400303486103401007010707004d40a03400080d80300c4e06110742d03212001100204001c1c00c01d10300c003c3e03146c02c00741b400030801c00013980301107500d070b080c031842c0d40f00564404000100760039090030b01f90b81ca00101c0c040f00b171104003001c400b62455281c510640941426000208400a008044082e01d120032602c24000c0c3c00302030048041510301072000400040380d10782c040340c01c401d000740064281200d40c0c1c0c4882a07034102465881d4039030420bc3e010044140c024011540010b14120203500318a016009196503400d900400b6140316071055810612000030360448401581011b030a664903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 320646097 1250 320644847 320644897
    0x9190b0301150203030402011202032703040303030e0303070807030c17100608060d08070611040806250801030b060d0623150102010b060f070804050a030f06150f0b0708 74
    0x3500309200e02140400302031441080588044101ca10540e8140c440020348082000f001c0f0094000402001d0b800e2074009620381000c0b94288210664900d01000310b6845065240090a4600b0080710480c00e902c1841032103242c0d03410444035580301803140340c001020140c5010407a44840d40c90309410804a9600900c41d00a210f0f80080f002d40b030142d20703204c40c203860300006d1008240402002034180c40d41030107908001003442d041824101a40c4100c00d08094031100c24a041c0a0280d44020f405c0f614103205d1b42c00412120000c6940940320700309404c4075855070725a032220810090600740b240004070340d00e00030004503a21074441c080201c41c041c042c0301d41f1100e040c40d024105551221010a170b0b1001d00e2910740c414010341d010341002078901c5041c2648c404090020f5040b0442c100c41c0c0c010141300205842d114030003003800942c010a0783c402049005d04098003140c07040e400c40b08640402200503c203d00349140154215a481983d0640e0f40501d0308142d241d5014103d90301003081121244065a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 320647347 1250 320646097 320646119
    0x3091305060f030c010c08030907050a06091404110a030e0f030406020a0b01080637051302270106050d020c0625030e06010506070203010b280501050702060706020919 73
    0x300328401d603002c0e16008090420035035a5a0200083c038000f40340c0c0302882d80082c0c1488090758114094000312032080341c0320310005407220502e400c80800a241244200013822040c18171608054040d07504001d105038812030040548240781c001424507441d4424031040c408100300842d8803882c504107880e01d680e01c0741c9009403101200201954600f150340004030304002d020582030b001c0d06a462504401072901c08400e8006400c5d660b10400c4204002000080f204080c05402d02c50700500d408880042003910400c09401e000c111a11044001c001152041001c1d509076281522590b050070380d140c07618111a00068401e4038291866405020240400001e00b10a14890080e0340e54190b00c1c141c050107011012102001c0c1d0291031603202d50010071950500728001d055440c00500013080004401d000700d50100407640c01080800001c1c194000d03010030342402e800140c003091802c1c902d4400c5540014686001d0004080d140c0313036000800c0c070040d43e60a1482502184680341c0c07107503000d80c0c41d045251 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 320648597 1250 320647347 320647351
    0x9031911040f050c160309030b070f08010b070506072a060606110d0c030c030311031005010e060a092105060408070b1003020916141b1507090902070503091305 70
    0x40524241041c15040b02d01038014031344215500e40c07115091a41c1030070110820440c035032007642802994030001c000b1400201c58503205005d03946400d1601c4001b058002c000b028168802c00c524141030102e44002440412025000700b5145003d00c054040c1c4030a00400c1d406080c45101c96100c0c096117801007003d07940003d01114029100d5a0300014940a181c4c2c03654240000f00000400c0303040c4020000303008030302d08407810f4081d150001c2c07840849078115043d036006550b000010045603104205541e401180181c110000365105810002d0303000e0003401408541c0100c1003040c1c040c0d081c80c50300c150b00c141040c020680000c1114500d082600740f01c50365500c140020b90f00d004000000500040c00d010b0003170220b9501400903030f41d0b40d480d5100d14000790443d51b007071b004000ea030100c420072803074604d030103004140342c0071b02811120103001c041c0c1460128016240622000700808204071642c01c0700058080391090500540e0795911803030050b00354800e078140c01b540000120408001c0e1025617010314 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 320649847 1250 320648597 320648599
    0xb03010204062a050709091502030108061f06140706020702090f0406292205091005100803160f0b010f170a0b2406070515010e01080a0809031911 64
    0x700ba4081c8500c03030300c0e083d02036111016025510881341000703003003a958024503030781c0c1c09804440f600800f01d02c518803da901c2079111201642c40035092210154600c503810161182c0c02105980b030901e0020003130200c903c0310040401d0450041070364410710034160100e41000354001c02c0030b074031071606100f0210002c9003039800761141450126075151114101c0c89405c0b400b80d0307102d1500c202495070010888046480000070044450102c45002803021600401d806002280060448051140c11110071204000e002035180c10702002e0421280d000401243c0c840034821151003201e9440703050a180b00c2d500290b00500e040000d00000030b100d03003401c2403613041d112034075854070000c0c00d280125a50340c0082207003d032542c01c0d4203003c221550060707020307440024825a0a24180c0022000041258102240503503603078200103045068090304401c40350142c003040d814000745504240c03990740d42d80d144920081121100040c80f070000c0c0ea0800c001400803281001c148d4990788140740107145420b10782000303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 320651097 1250 320649847 320649887
    0x503031009150302041a030604030806010212090d38100b0703020706030b03070306020f0a0806180c07030e09040303090b06180f040305070b100501021b060304150b0301020406 77
    0x30440c00554012244a501d007800c0282d603031810342d000c01c4000c0c042000c00110460300580c00001e00d0302d05010061080780280c80b181c81900d4204006802d00c900011030904010703040081400b03543d600000c4645403900050107200300c2405103200807240664075820b0a801411441d1203107070019805400c0d103c0c003151076a200c820fa0752581110031500903800000c6c0541c012100922140388a9070110b81c00000080c111202c0b6643ea80300c400c1240c0c840140a0700440001901042668210b02d0640d00300d2001c1d104140b6141c415400c2094445015001c2000300b00e0005420742414810141c86080000044c8586a1410b007840c0280050050742d004944502615000039a1803030402c01d4150041c440203a03241003070ba01d0f150300720f1309038500400450a1220034081180072600d484a142d03c41c4200e003071181c41e030340c0c100400a45042c03540d06008481d00000003030324000b52580350580390026401030946400080e4140d580c0050400b2001442d0135620200b00050039592085da0504511400415 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 320652347 1250 320651097 320651099
    0x50d1701210209042a0b190207050a03050c1906081501030605100807030f0b01050d0f020c120c070f0501050f0304030201060b0a031d06040c03020d050a02040f06030209060409021f0e0a0305030310 86
    0x702c0b031700c1012031280c0307000301c0000c0c44540c80c49041e54a299081200310b1050b5120036442d00c001031050416a04180c800b64005c0d040c2d0b40365410124205190300b12680f011555280ca4402c004104540051549900ba0320740104911580d01980242c0c0140400520940340046807000c0200b00040071205900083e0808180002a11081c851190041410381d01c2501e0141e04c422030070080c0c040c800c1ea4a800039420490701e80081000d005181c0d4107484c2c05501540e801e4640c0c0d24900e40103146c2c104000b040304690041189a8025044070002c4c0d09443c84180c40b81d442c1d050507401095990301c120b002e0500001e501c851540d041d0301480c0500010384040000c0c00e0a001800e9459808450003428043d103180244094640188480000c61040b002c548101c205903000c64166900d003054500541e4942c14140b0443c03802c0800390b903208038250350812242c15141c0003c0d1510541c4031014004d105244240c901d6107106000700c080000c030240010f6a8190b03240f510301c1e540c0e1700880c2e00c14452541d02c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 320653597 1250 320652347 320652413
    0x412030309080315100804050c1014030106020319030e15040204020c0d080612061b0c07090c0c0b0601050a0815060d1a0a051002030706110702030f060103050d170121020904 76
    0x1b40c0d502454214000780b00d0000e0410a104085580070214004c0c456218074441c1d40c43c0e40314000f5030203880e040e8059500d5001101c8041c10202030300650005050800b03080c11030045001486c41541041548111565202d03400494001d10a5200b00203103030041032a100700950304024424041c6409440740c071448404001140d446000560f447c031030b1495526140e10303c05540d400503040151642095030304442c0c0d0364202c0c20450301100700c600d0110f201c268888083c05540080e00d0340c001d2084c01c1179440c01007040c200501d01200104040d20300c1c0303a03103071104030140c88000503210148000f0f0410403c0c1201019082c1020740200001d0740316200d514004075050900c046040c0c0072448070340040d030400c4d41c2551684040c10340045503d848030350038000503016035000c000e00c044c060181d0014260071350460400c81d040244c010702020604c020640103c0341c40c050940850f0444150711218404000380644800c070108440030040e5002454030140800d01800034074800080101002e12000b92001017 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 320654847 1250 320653597 320653607
    0x915090a0c1d0105091e01030c030c121d100e10090302060a0203090c0d06020a0f0f140f0f0309030a090503010c080103110d02060c070f05060f041203030908031510 72
    0x104400000c0800142502c09240c0214010000e54141400d07800e0640410100c4c03051140c031320502e040491080581c0c403040d60075108004012402d841c05021a482100c03015000480b03c0030002ca034565103d280503025004420150224801401692421600c10400300c01909190420a150b07000720720050b0fa1414043c0319082041e5895006420546d0f00c3ca4079003402500700605e03802a03800340140d03000b40c0780e070b40780043d404852140c1c80043e220151100010240460f480104040c401420340c040352154104000c1c41000a156a156649601110340e40c51203001c1c9a810000542000c02030004185000c0060029100c41d0b44c0c80d01c03031150f55182010700780c40b401580d403408a41003c0060001c10300d110100c5080d44000303458440c644219a010a10fa42d0010b4100c0e12282c0000d41c0600c05510242c41d440010201180d18508005002009030303414031451282c04854505160388004150184d0056400380342c2144140b0b0702c924101c20b4103898803907034802480c8203440c2031400c020070074010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 320656097 1250 320654847 320654861
    0x50705010b09011409180303040f03031a061c020f040b091807090e04061b02010b0a0501080405070b0c0708011802010f0302031e1504020403050a020108240402090f0915090a 76
    0x3001c00000001e0804240040c440020b040381d00040d00d20303282c846c06000300704020350046205241103040a0f60f00c0c14010121020074403e4118441101e440081c3d50b682d0780c2c107a41d102243e481c41c281c11410001900300082c07140c00403d60700c150000c40d0000392000c0f1400600080c2c40d0544010110707402c070700c80160010504503150000706e03e40500c14840c0c1e44101000580c0184070354000240d05001c1c124030084071b0b0000400700d0040c1c0d12000c1d000b05a0410045244c008c1c03400b030800510900b0305a440a445000c1e50040c2c541c01a400b24007102d0360707001002418011b104600003002001d003482c281c41c45410407100c06034040380c0d11003080300f00a88071f8822603102c0c1002c80c40c0c24444440a961240340c04002800111300c2c4130b000f0001d071940c0d80d100e1005000a510800042103c40240d10000d8081c1d44010034030741400e21420b038512030300568505801d01001c012100180d5a41101d00020301a000c01851250002202006c1000510420000d0b80d202c4608848800041e03503404519001d81d411 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 320657347 1250 320656097 320656109
    0x2151b0a0b1f0b210f06030706092d120807030201050f01080307201c020406050f010522090e0c12120a1407061503120c0b04020607020a09020a050705010b0901 70
    0x1c0820030440c0c184407101400365101a2005810142604000c0386540390090310841d00000c00002070041b640f13810010000101440d0400c6140f031032030088061303074000794100d4600b03003110064154076101010070040700240c181e41d0760390140b108031070800d0780c41ca03000010210701541c64240412018000030806504890010008515005540d61162418144122840c0452026400b24901343e0381e20a503580100c1c2c00e0700700301441100c00d40108821381da0300c0d80c030603802011202c201041a9074800c0403035001c0d4001c030300c0405804d801c440b14801c10b411550300c882c400701e05e40002044815004a200d003420174044a50014240d0300301522615070403440d00e8101140d100b003190001a82c0100400868074951100480c103040709902d8400980741c0c03444002094410080c01402000101e0189806031000c80c41c1000c68100302c0e40d1501c004840183c070203403140394046007250840d9506a14003002c1c001a04055442c1d107001c8401a02d2030f040070404032050750800c1c00e07841c80c03810f10300c0c1c00c1d0b8101e4070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 320658597 1250 320657347 320657401
    0xd030606090e0601050c0c031b031b0f0907020304150509190b1801120f050603061302060a0318200a1212030b03100203070c0317040201020a02151b0a0b 67
    0x4440c0015039480d440491503d086010787c0c20720031040d54003030000310f40b003441a0000c5043c0356000f008050505002ba804200015083e01201e5140d840d55901100346000503658051a52166003090f403450040350b100c5c076400c480e241c19401c40254854090302140b0002c0d070381070020b2400c0e03d021541d081840c2c05901b40b85007040c8030200c4070300c43d44852803014902c1814041a80b84004240e40181c80e01da10704454080c0c0ca074024082d15050410096a11508004808454a41030b900242241c410701d130300a002c15827249030808008010f8800307180c0451740508c89000c50484280b125140a801c4450240325038007a41002500d51900600702c0e00c129486500c1c090040b1214105800800d00c1242054061045608040e03240301c0a00c021801848180c5890f0030b101c1c00c6240c000c141003441c21000000003040d009110061b41c002410124640e8110380442d41c041d04840700d00164090f40c401c0b081044002d003211018104007041803541c2d45d0040e8284800c664880400026a5441501c5904841 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 320659847 1250 320658597 320658601
    0x2090402060a27031e051f061205100b0402070203070302040903140f0d23040b04021512010e060d03020d0f090b030a1a19030219080106080d030606090e 67
    0x71405400030682000079060800000c0982104801658007400000008568149040c800c0c05003003030070b41d0f22000801502841040e1165500380d1241d0110310b0300c01201c1000400700d0029000c5070401d0014007208003046030966002c1c00c1603a0364000440c03120f05458504020708000341403900844001703d030050010305490b0300e944e0a001c020301000d070301601006882c910000400400d000203190344468154115120260540c0040c11a48040e0010710780301c0c2d480c1200c01d000100b4140d02030344103030050521941640d960000c9001020b4001910522030070008041490059111509050750b8144100300c40b144e40d440d082c802620583c0b0070140246c0d20096080722071501c201900340d40d6000d0707451326078142540c61124203500d40013900c001035007030f80b2804002242c2517014400780b4a80d00442d9844116184207203c081e0800c81c501001e4000c00840d5107074500a4000d8a0b2600107040c46002009561390743d40b10280c81d0303501c842c2e00310000b1313080010000e00184900e252400365809452300e50030326 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 320661097 1250 320659847 320659849
    0x30b0d08070507030b040821070807180f0b0c100204050f10031b08040b06181515030f0718081515030a030206061002010204080319020703151401060c02090402 70
    0x29006840c1c11541031003807502c080005110000082e02551041941549440940300f1400c0b06a40d90303094109100490010050099413181c8c51907041051401c01000c240e8506000c0d00003d1362030740203416062525100000c22480c9000140f54150050041c0c036815421a07006405911451184a900c66024150300ea03140c6802036004100510f5420b00050203040034491000340d81f130300d04c04c0030040f54401081101b4004000b003c0e07944410200c410501c03440c1d40440780414a00007529104500c64481e43c03000440d111161030528441d800d490860b100c1c0707803074004119640422140714000498441c80c07000c00d4070211900d9015100104080c140541c10341c132240284050003088905a03130088915491a0344040c1f02c0034002c14001e5020340351030f140c19002e1000d041e400560000841e88100810419071002005032408415440358149400400d540c0803440c0c144a80c10182268140e00d4030120031500e0355000f00706103241f076010784c80240e0340d42d4000c3d2441221048081c2d00061060005401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 320662347 1250 320661097 320661113
    0x7020f0906061e030402090106050a0903030f0c02030601030c1403071401030f020403020d0606090c0f0c1118090109151116051207030c0c090605060409200a1e030b0d 73
    0x210501c042c140a040241d40000c3c040c00d84140d844640b9005000420311066062440b051405130841d41801841c048070314400801035941448050108000400103514a900c920103205c4000e400500316003082d40c407401c0a007040d05040c801c440840d0412a0722a20f10700380442d9400486034100c510101c40f4803444015005000f4403c4404200c0b5800c00c000300050f0b43e092100c080e018000c00d00004c3e094102800b030012181311380c0c503003414080300000c0d40080546c000c0c240b19030035600c9549110506441800b02c1d149200049910800d80003a04c100010366005600c07012225005e103030000d038034469848a0134211100d02e0391150640000704000c055a443d6031000d00703600c81c401c01c11199102c40302c4030700e08401d42040c0400c8000841e01c0d044241840300601208001c1c2c89225000c200b12072a000004040784180c0c400c0000300c4e43c0700d02d403103031801401407280e02c00d800048521a9913500c00c22001030003085030110361040c24042c031182e580710510070b00ca22480413101800482c2c0c000803546580c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 320663597 1250 320662347 320662351
    0x110904030522173403080408010506010e0415180b0a240504031a071e030212010e06061c020c0106060c0308181b061303140d020607080402040b010c050a0b10050607020f09 75
    0x2900c4e0b492440e000002404910050009140c40000040c203410400001040c5107170b00441a4803a5003042400000802c1c0700c0855821940c00c01c0b0030683c02c0200d1088003016161460416500460b40b10300000e20500c010411000c0026110010042e402c0b038901c02c2d64640103a000140c035140070740c6420484440703500c0f0101d4218229007007041074800c3d5140c120005107900c880c50700010790003003054001060203044050244c800100700c04171628200010070900c0c01604c06a50702034060301c0380100d550ba240e138112489185114000d00016071a124041e10010703901e0000c4002031030850000f083d1440340350103c800c2c41d03500d01c043c00c00c000e0700c0c03074800902600400b0615070182003000525048100910340c0c0004510400b01e165590f81119451410300c0d0104d901001590008420810540c1d4441c5445510590444000601504040048903200c10001c0c005120788510b101003400c4c401b034080307950301c0341c1d40c80412034990b9600c803010b00c0350900030315100075000304042e40d540440303140c180d000b2a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 320664847 1250 320663597 320663683
    0xa03020303070e0d06060906081b06091c0605101a0901080408031f150f0801030503031f1203030905010e0c0310020a111209040b0d11090403052217 65
    0x3001300c6400c0d11100125641d540c442514a5554501001000c405000368000004120032541c100c100b0301c0046480c0b4441c07044001d10601001c0c16112030110f00900f10808160011810400c2c0d1030486d1002400c01d256005010200024041e20410b500c2c44200311011000181d580003a5920341e0766510381e40750406003030030325580445441c064100c1304203000380009000b2014112070624600c240036049001007a8034a0070408244c0c0188045007000080b203811420f007142c040750030b4041e4960030829011540148001d0252000d142c0c0525906130800c1c4181d40c0075800800c0500701c044075280d40d5510030b0400d6501904500c03803081a2407015400b4002c40303031040c00c00040c440d0242607190b0a0010100c171901e500000480c0201543c1000d00c10481841d0042e94404402101c0740c13a8000d507004004491441442145e0004042511600654000390b4081d04003c2c039040d00011203880540e90740c0a0900e003200d0301c4010180c130100c000340341c07500c40107000c0c4108810714078441c00959140c4c405800e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 320666097 1250 320664847 320664859
    0x6260a451a07030e0d0914040203010303090b0f0d020d1d0f070306090501140c070b0a0506220b030d0905040509121210030203060112050c030703030e010c02030709020301030b180a03020303070e 85
    0x10404c4803024008100c161110750303140d031221414110303200794800c0383d00c00c0540101d20500042c070000c0d401807004000d981e10f210040d6195815400e20740303414412080401c07465800030078507480d4144240c003c04140c85000040d0040c1600640b01c6966840f010301c1454202d500c00700c010004144d407580509561401b6a001180d4485050304a000710001a2000c0504a000007000c4e02400768a10341e07540c101c06000f00500ca5400c2c03040019017003c1034210a9109121b60913440301c0080c86030b0380014091800074040c1c87e0042c0b144d03000074060b1141031189078010b605006c0055039030103020541030a0140c80c903d419040174400185000b0301c3c2c03001400c08084002880c07012015940c02c106050003440c030740c480c140c0c2c03642151800e2401c00e10501e008a000354050201030000a40201ea00c0c2c00f000c50030300c2c01c6014031510b4000a071810391154024110030b480007001005000048048601c00c9800503500484060b19204035588da20708503030080c0c010b030000d0001c03030740c40d6100c3e504e500c100d030300001c0070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 320667347 1250 320666097 320666111
    0x20f04051509030d03020a0c080a021f0b01090e16050715020c0a151a01080a02040e0408071e0803010e070504030203030c01140106260a451a0703 64
    0x105560a00d8041d595040490208108070b65140800c101041307480c00780303010350038030101c00e00c042c002c40b07c841e01c001c141d11004038603c6c0300e86108015a21102c40d00c03c030f4020411604980800c02004008010390010f221400d01003040341c1580e0310940a105e4600d04c5115810140c40220307030680122104403940916061100d800c10071600140201e640c6e542e0141082c03c010785011000f01c0b942550101020b802c00204400190b02c4c592810031040d42820050310690f00c1d045004001c0c400c980043c054000100188001c3c41882009010503034424040075a24460206140e040041e02d6003009160300c00400c0107000c10408103002c00e8101030030f810310030308050700c075030000c1e0a680108400010580d581c4003d00c480781270110b18140103045a0400120381500c50304143c0701c0c00d00301c001030381d146410000440c010100a40c0400b00780b6151300b4038012107170304600d4a216030290074070907072407031844000203542102030300c4c0004209654000551114201a8a250001079400806000c241070791004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 320668597 1250 320667347 320667349
    0x2210f0a030b040b040e0a1101051306080405070f18020c0102120a051b0405030a02011b0b0f070216050d031215080a031106070207120c0302030706030c030e0c0f0103020f0405 77
    0x10240c4001801910702040340d0b01800c05000840d04205101d81c481c0d400c12065000d10070010540111094021034001c1c21a89500c00603241d51040040c01e00a51681010002c0c1d0240e000c6452030040c0e10810a5540150b5070320110040d421081c0141d54189550030703141c09001c50315900030044400041d0000d810f00c600700c6000d584001c03084551030741d40741e02c503810001c4140a00b01104a12020080c40600746828400469070300d07860903d00070b040c0702c241d500a01401d01d1310a14000c1e01984481c0081c407030701e8001014640b281043c0e9003000984202d0401150001040c0600415154007900f40031001190352401c90b807803541c0320b4240e1780e1250340e003058644088030044120080c0a03418014180d02155240c0206003034090403c0b22803030303000102400016980400c1ca1400c40d20501c90038103204069040000d91a02c0d9944000d42c180b04011000681a8068005003484181d980b410040034410011b002d4641065541540c1c0c80500100602c05540c0280d01406900c2480d18a190420303880700 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 320669847 1250 320668597 320668627
    0x6030818010f02060702060a1109030d0f1211160602090a030c080705010810090207080d050a141501080a180f0b09060106050c0307020d020127140409030221 69
    0x1050000d00d4903060810581d40c101c03400301ca41040c144001c0826281c240b4000307445040c0501202c11a988039142d581d0700d0b0010700251740300c1c0c05009050301c080c100c0c003210203003140540545072404201100f5a001c0d030f1000034801c1e08004c8161403001c91034881c40b1484400e1000e01c91000301c540d0b503030070710010303426454604904000d14802c0141254031420034030703002d10f4520f0320b501403410082440204004042d680046c407003100c145100251321782c81603160002090054400c0008258542400c022908100340c211070058454100805901d44030f09030280440c607031059009002c11200f0010480f141882c1e80200c10303083e10141c1010140d14507690707051201c189811f00b039602406140a00c00351074800d0201ca40109014140300785005c1580108941702d0103480300107441455001180710959004070440a1801920f2203214081001d03010315035561b000c940901a031041180051a00c0e07824984900030700d254154009103109681640805800080b4600b2200d030000203205e4000c0000c816 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 320671097 1250 320669847 320669857
    0x91d010504030903260f0a0203040b12041514060906040b0a030602040e0112031d04021209010905010606110c04091a071110021905030406110f040501020c090105010206010e0a060308 80
    0x3960744030700b058a541040c982e070301140c3c017501c3e0141e00d070ba4030340c5100c401c046811109241e40c0089a10f0310b544031424107900314003803a8044ca402070700000314960407003404921107115a01c01c09104c0c2407a0543d880d0074045a1501130206120020303580420150f00e482042298440320080020603520030a1010541314102c642c0112203403900820103200c40c0312456019805070064019140c0d25600585006003000409400036850745845001c001c16916580c04031080407024101d4070215003044540140240300405040d2495443c0401c0402c0c0c4a11440b00220158540c0b00180904280780080000404440344200d50b0182c030003111891001d10003000b80d109102d507480c0c681f62140c9595169003001840540302c21694030410090304141e50f62070014110072400e14203942c0765503071890a00000d040750004c0c03242002010541410340b4140710000c0003070303620a034261f4078400040414082d01c0c180c00c2c0038460160f00f1070070050050061503038209501130f2410323001141207a540c1d11032130019440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 320672347 1250 320671097 320671103
    0x160212030a020c1002070501080c0d0c090302240f090a0306140103260406081801090c140a120f080d0903090f0806040b060105090d0501110a170709091d010504 70
    0x2001c603071000880d806200c00c5000c004243e0b214540200d040400946450356401703040c0c10b2003030203008aa20130707801d00f040d1030000401032802c2003040741c03015014181024a1004a11424107405260003200007071440317001f0711b14482d40c3e0b64108600b00c000070710550056191150000c454507000800709045019541040f40807041c81c94040d41035003000064042e0b444d0413040b0b5140101c00f8240e005209101700e030100c80180c239000000f0380301c410820150100a00020740550708000501050010130284d040461b1036150580d404910314900b80003511025102c1c150070718071950043e0020900300a0f041c2039013807040026515051080f488076088400c2e04c24141c00141c040c0909002c207002104040010304030500040c0311a140c0355403078107030103880184100d040041c085900c04040c0c83d05201d0703910040d8050024420440040740360440d5030400071064001920201038003d0781022008550b005400e00e070b8034540d80c542026a1400500741c0b002003134100c6a0a405040d2000074203105035800740b84 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 320673597 1250 320672347 320672353
    0x114100e041806020904230f0709051008010f061407021e06040b0405101e0c030e0a0303110601060504032015040e0f0609060d0b0901150e0108010f05040b040206160212 74
    0x8071007808125400051003802c240c80244014000f0b40703492071102e91107408c160312600382c2d03580c0d443c0c115903039002c9521003508100081081c0c4c0d05076401c0300301703039040c2da4000c4a00c035a1036588040c100c8040b0600d800755100b0803000c216000c0541400e0f9928a511441000c65a005103a104041407155211782d015a0440c580482c050008c3c1c0340000c100b90070104645420980c000c03410750902d04010400c40703c4403d00000c180314500301030040d2109004100010a80003031140e481c03e000d041c0d0400e901c99010b49004103000170588a00039010740e01900c0d0011a17299070b50003168202d0200100310705034640e0001c1d100c80141c8540590300001d0001e40900410340299040440300e80051220141074644610440e908012540d11844007110803030360040c039201e034662142e0070640c0c0144007600c148100d0558514011400d40b500002c2036040300c0700d000013080104010515542210000e8074000d10088560000c640540740403006888844000e500200322224540d0020f041c2091440d003103180d0350 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 320674847 1250 320673597 320673607
    0x3100b2d09072006070e100e060f04050117010807150210060f06030c030e0c040c050705070905060910030c05040209130e060709120c030f0507030b0c09090114100e04180602 76
    0x809001c0d5050758285030240182414208408003416846d0081d81183c010a009000300724001c0c483c403000c402841c1f000e0b2480e5034840c424000b00300f559119000b00c83c0070403482c034800d8080c000c4403482517040310482e601030000d65003440c1c1d452051a0101c4540411480781c2d0788000007200b4075119001c0202040d281c8014490715018020341501c010310140c1c0d050614003480e100001c400031490350480802200d0000b0882c0030140191030b1805400e001601c188180c05000c1281d21403584100d002d034a007140c2c0e40355595101d481c020184049800300074440380c3d103c10704100c5070420380c000d000c2c0c3c450018021480040700c041d4407803c0341c007000b4000c0003036403110062220b0540c10141d80c3e806407200410202510f40c0c0c030b44940b61409954840282180348080c540403d12100b40503020142d540030402c3c1701503040c03242c4075803001d802c2070460520850202c0300000365901654000c0c2c3c00554094018542030100074429110410040640f45d0880d40710700c08601108103c46001860603c103400c010380340c1d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 320676097 1250 320674847 320674877
    0x2003182d2b140c070e19050f1e0705070219031202060a0507020c010203030103080a0c0804030b070e01030501030209040b1009020a0302181c061a060a03050603100b2d0907 75
    0xb0000000601d402c928040100301c46000011558400384c801040d0904400c1d100c00e00040454041500b0a00c8920b01c3d00d4140484445483e03121801042d13004002d203003540540d64051024117080d204440854410402c03040141007103141c15207500080881ca1804903501d03102c1c0f1a0407115130030b9000058100c2c5041080c201018498031341c104d205803001b81101040e80002030f40e03a01c41800081c1400c180031a180b440c841c400c8051b50030090380300140d5522140c0c0ca142401118000b5600c00001c03d01240c110240c40d4481d00c0340d030341202d8008005115680f1261035020030180b000d00040b2011841150106501d40240000d18001141d41d4006030746010303103d11040044080d402191094600c4407890783c40c2002c41c000001d003241c100e00300003104500e80340148034151001c0c042039004680414a02c1c681d9406611040c0715490650548a00c0350005d10504125401310040b951700901d00d41d04070780c2c00250140c0255000d14890702801034014184001910148210382010028801042e84011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 320677347 1250 320676097 320676107
    0x7030b0403030b1002031c0209030c0411040e0f0f13050a02060c07030302060f07050a11010b10031a0907050a050c0c040612030f090501090501050a032003182d2b 71
    0x1070070703980c2c030146041c0860404047e0041c8440f50401d4051034011500700b10f50356061203560101ca0004000308001002e058000409404c1440341c0450019038800040060803c0c0103514455402c0d1506515942d450382c411101000d00180309581701d1207121400c0300141c131040010000e0107441070090200700d246190003490404002d20213100703a020f010078407144640100c02c1e10302404031030400e000743c0745c650340070207005154200b68183d000809100042616030907900c00581c07243c0c00c0082c032691254100c1030212040301030740c210f07000800c100501d1000b1485000900340c10803c01e070950380805118000501516000d421024007400140038100030540c1084100301d1100060030328040d01460720002034030700303007407031044506001c400640700003210b00c40d900c104040c0144081945403410000303060700711500200c5080e007088030030109a8044080c0003030418002c54059100c07489148414054002a2000c00d11240d060700c10003003509135901144030800c4400c07269a010248030806400b00800c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 320678597 1250 320677347 320677369
    0xa150e010906061b23010207060507080a090b0105150403050f010506010f0c0c050913060513170913020705010e030f180a15031109030712060e0102280207030b0403030b 74
    0x4c1c05803000c241206000321443c084007441d000801c101940600344079008200d0401d0220f09000d500c0001c0c60401c01c0b00540c06180104d105030b4400e655550741c13545503801c861407102c002c0d1201c105031004000a191031003881c018180040009801c041e5640c0e1180e10b405c000c0380c0782040e16515042002410359009401c003020081c28a23085030106c5490704c400c10760708943c0c02050301a01070000040c030190003919000081d91b40c403040800c039031318013501c01c6a882d5000000445116080e01150040383c00c251007910644040180313101410074442c0c400000950007403108030f81c255203508414811120a101400821400e091000e6860500001d45c280100031201c00b18452820306030207008a040140302c100ba0310506083c0000c018100485900c2c0074021444000e27450711410401099502600042c540481d205402c280f11800c4100821405d0f40546071960b0000c00100089800c80c8502d1100c0c07850100b6180103407891252aa15110740c0348000301c800384c0109485465080d01810081c84c502 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 320679847 1250 320678597 320678609
    0x424021b1f05120c160b040501090c061808060705090d02031915050a090f03210507091a040e0c0a0903050a0c0305060a0506011d01030b06030106020f070603020705150a150e010906 79
    0x241c078103100b18105c082c02031460380005d08000c10000000c0e04006e425444000308035005003052600d2651080000c042041c100c840410008a01a0000d1003010001d03450380501159140e01d4108000c00301404038070080214240d0341441540185e8500032100401d003640103005003c2102d00c0100080c04c034080da100074155044071361600c01e940c5c0110b41e80b42c800d03005040e03151034090760001038200b07686180c500c02c0c5050300540341b0b4102806a082d0300103041c1011900251103c0443c18544c15a80905014501c22840d05582c02400035000351708034801050480302e681040a00c0c680c60380c4429181c002e0b0384004503000220407900707009008042140795803080e204081030009241101c0000d01541d58500400e16000307541c1074144141c3e020703400072101c8030301c050840c903169030703403940700942c0e6050803007900d500340c0609603012844510a00859101eaa00800140480c02c0d008030716040e40034000b2311050310b81c0d40c0c49181c60404044000c2c1c6a0041010b421030807107550418a5010449009520170 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 320681097 1250 320679847 320679871
    0x1f02070e1f08120304120509090f06010e040501030b06090403050c011802130b010c0b060d0515060f100c08030c0c1c0f02030403020f1e0d080424021b1f0512 69
    0x160f0720504003107a80c0640d1042c004080c4141014081d01d0340d000345c59950707603c0308020040100c50032102d242648105001d90350201d6281c042c106001c100c0744203002c080e1103010038000140c168140881c0e4142c00520a1600d1880d003c2070003c52421a52014109000c039042560405d05600d0803d22040d00041c08840410111448100184c240f2103068401021550007100185540d51008020f018450300b01c01655072801c1440f100800c0d103142211840c0c4181c14040541c002d5080c00d104c41d858074046920b56206c200c142d903c4402042c3c100034903851300540c040140039070b050401c0c021080070000340c550a28284150b00780c05440910010601c07001c5500501c010000f5980300b5040604980080e50944500854203018101421540d01019040401e4186150400c854000188111189104c401f0901300074605844860b2484408550060b40401200e14070078078a034a02c28980b801c010140c0040c800c0c0c2540155030005a2402900480c0002c0b0741d084803070b12a020301607032101320341103d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 320682347 1250 320681097 320681113
    0x609060c15100512030d0e010e0a0302030904060e01050604031e0212030702030d3b0306070903060b030a021f03090212030a030e0705030a080f0f07150c0e1f02070e1f08 74
    0x10060b581c0c0146d400e811825925a224555800c000390f1180f00c1c1090380c0d8060f990110030504001e5920303448541e03414000c81ca030110004808a00c0c0c01054140e880003403c1c0317072420b031464951140c024400c0e5045a800e140d04031602005964680040554a95010145464444d180105401c1c0042d0340d0742c074028091001811160381a0300800710354002d21a072525a43e00c401c2d100d0103500c02e1281c205598242c420b44092001540d080a03441c011240304840a0200c00705090605840b10701c1148025004000300700e4030000420100b076010000380c00c0340341c0011404426000150a09400c0d46681044c1d000054200c10b950707454004d441c0d00201a4000300380d10b510344008240c1d181c42069016001280214004400103401011580c00b084007142d115298015420031200801e003801100c20582c1c40c0c1070841034014050f260070321960900502c000301e0400002143c100c07000c9501802c0d030440c0503540000c10030030511088240181140766250a2100802c020f169222829400480c529800410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 320683453 1106 320682347 320682379
    0x607060e011a0a0807140405040213060b09120a050d08190e03041409040b040818130204080705060c0703060209130e150a09020603060609060c151005 66
    0x1c000c3c030000e950b800036960300c810314440c03049910b0051001d103503585085e501c080c0d4003a00181c09100a10040318112013158130a40207080b03000c0003c100c411031030820b550a46184581c41004082c0130102e80c843c0c80c0d580c066403040e14100620840010822050301d0f007030300007003e00101c091010100c40e48680da142e810500401c04c199200e000204036030324242c003032240210f03004901040f10341c0303990321041120741c0070740d48038100c5c101c2c102d0703008240e80c58240414503166103440380181c4460800e0851814032420b50f2169110304401d0000103601e010220300c503011a079000a0050381c0742110000310704000300100601d5010752a001801d034481202250380c40d00718516050b007008a588188000085400081003e5000b49003800001d52900f80a00244003400740100104e0900980c25240707880d155010207981c500003080303002d2020070f00c00215800040d200c01c1380c4035410184204 = true := by decide +kernel

theorem cover : BRFrame.Cov 320503597 320683453 := by
  have h0 := BRFrame.cov_init 320503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 320503597 ≤ n) (h2 : n < 320683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
