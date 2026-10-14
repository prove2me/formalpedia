-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0435
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:47:37.886576+00:00
-- url     : https://prove2.me/submissions/62c6d56c-5432-496e-98bf-4312b67c8c0b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 78057555 ≤ n < 78237411 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 78058805 1250 78057555 78057601
    0x50f09040515070c06090f120f0c0602180901030602030907090c1707030e2a0108011203050304030903020a030809090718061d0301060303050c01051605030f060d02090a020d050609 79
    0x181d035403030f802c00c00c844054000401420691a2141403c100407181844407800c502c0f0780403031110121181c20503950a440000101e0100d8241481c420004405034001c12600c16400d0f801c2200c10000004201e030004240c204660240e0f00000b400030300700003044240001d0078061028000c0d20030706080181525201c10b000a00011303001c000c1500c5a0003600f0191001130203c08807403088120f9590345660b003e885e046900140c0d161100c6c50b2055200d100d0690603100b4112104034810b11a60f404c45540e40300900030307010404003890120050b03136000100070046020300f00442d200e0313a945c5c0c00c0180925014242c6010300040181101002804131031800840d09241003868619260700c641800c104a50703001e05a065103030074800320030142c01402810030107440100800c1160b9070300c00c0105202d507001e100c1201044050000500d03002a00c84201d034800f0019101c441034400c1075002c1003a20300143c804200340380c0c0118001e02e0440c0248520341d40315000b100c0d90707071603402c2448002c1c0c4220001030780c0d81 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 78060055 1250 78058805 78058843
    0x801020c0d1d1e040b030d020a06140709030807080c03030112060b010c1e020105220e070e0d060c021c0305091207020a15050c03030f01031a0412030b030106050a030b01050f090405 79
    0xc040ea4459011000505c409401d99034903101404009460382000da03003c075580303468844c2038109a107000d01c94074031990304d83c0c840e03404090450712200d405412500080315500800c01810321401c9062010314000d141c1020f6000380700c10203140402c02e841252803c20704210b0040140030106184440301c070300903254101e4456100c43c803400120360a210350140d02196084001c01c580707840b080c0c44042d00c1120320718144444103803503104044036920030f691945a40814100f940d000402c5080d80024101c80b55401190059130041001009207403030900c2c071030b000c280e07120708010810304240000841003040d00d0040e031078520123a0024102c2c1e0304d1400740e02c80303802e82e603542100310702d000d203007104c00580a8204a07500c91800003180c0480b204240811031310441280c0e072005000c42101803035401268001c00b070404106210004400410006050703985c1076488500000f144e860741c08000c80514058042103205606207018001100f80400701d05014003464410000801c1010600c0320890411703092070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 78061305 1250 78060055 78060109
    0x2030f04080c0a061107050706090803030604020d060e04050f010b271017030304050111031603050c0904020408100e0c06040303050702040207140102071208010501270801020c0d1d 79
    0x89450f00d05034000007040c4924120f41c4003030b14003003140070b000700622480491b000c4030345400c1c3c00c4a01d041c1d144645111b039801071001c98250315103034024000060180d800050015650300e0741030b58042d41554255400c1e0888801c4e11440c510a0207045040c00b01514085490f040303080d030340300c1e6817030010b0000c1064400c0280800c1070202c02916640c01040f03440215804400f0042c48940c4940c4165412581c41d840c0c01051510164190242e912070360844102001030b07103202c00c0136800742c04010b10411030402e04000350402c40c1da40d8409007018143c00790082c0354182c8200504e1080362055070300301c00b465101080348078450355940100c8050369403500d00140c8821031480802c0190003020002043c0d414030061501e03022405501400e4050b005400f141d50384040c00c074054400410038001c29001442d5080c9005080c0134881c4501c41110801800881d2141e8551210742282c10402e1400341a4000e4a45101d2041e8040d02d00d0f4112040c24035290250022000002c81038041c0310f4914400079004012 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 78062555 1250 78061305 78061327
    0xf0709030b04150222051e040c0207080607031d03030c0703140d0204030809091b090103330608010e0106090e060f040507080a1d060414031918080102030f0408 70
    0x754081c0d01c03920030640d150071454a42080002d1003007400681040400c2c00041c20b403800c0d44504090364550703030050b02040c801402380405000d1002609013988500340d000603212408001152051196941c001448800620303081c400d4003800032500c2c03841c0c1c01441845045030090003112610307503060600c2c614010f000504070b0100d004d0340100c40742aa101150000c14008070800504140000b240d0402040c1c0d994008150750300c4504001e0701a5800902200c95154040d0340a00032040080303440f43e464640c201443c1d01da214441e501611400c4034144100038240d00404500d0142140416800341581032200040c07042080703208095054040f900450342c20340390451448089d540c06002030003c8d103094000034020790350640300d80f4206890000d07858520b000354514104400d44440241c10365480d6925890250603601e031101c103903400b04011030b00708042c205881a1202e20241c68020465900c408511104402c130f038851081640100200709000503411001603010342d00c0740300d10740c5030502014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 78063805 1250 78062555 78062573
    0x210103120f1704050a0b060102010915181407050315091515130b1c0807110109050a0603050109150501020c15040807090605120f0d080406090204050705120f0709030b04 74
    0x682c841c0c600280d0140010702c94082001d5400b03d004544059071078503161700490807611042c1025010740c0c2d42e010008044d500c15084220803c2e0040701c500e407040900c1d02c400c140707091016540ea034141e1103c0c4081185003070900945201000d400501249490081419900c1c0e034202c9104c02c1c2410b19501c00100b2034801d0038122209101d01030195540c402800d000c443c01020307040b100f2446a080c000b51150700e1280c904c0e030001e510b0b0380081d0b00f5003000841c0c3e64690303c5c041c110249905000080d1004102034543d5240e0300e0060100ba50080ba5651524604004441528506154a964191081c400c40e6000280b0700c0d0750311703008c2e60000282082031000c400107009030b4100e0303c028080e1010008581245812150954000302c40112031611686401a03440c68a0410b5845079080403240c001c106008045499005025510100b6030780c0721540040c0072039400b120044003060020444030440c910b0240c0e595030000c21300d030381250541003546002d40811100e00c4004d04802c002c00003d0b007004a450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 78065055 1250 78063805 78063827
    0x16110406052b06020a02061806010b0a0e0307031208040b01050402070f080318010515011b110603040302070807060903031115060d020d0c0e04150b091603140705210103120f 76
    0xa4000c644a44e517114000f91500400c1e10383c0c14a038100742c001c9420340040071915a04913010f08040910b00509450b050b200001034444040d0315004403800080411005100c4003503401003a1345a01c080e2401e40707018139900e0010b81009000d24414003d601c00203614501c0b0341c080d140c01440c003d4980d900c0104d00c00055248038440e0100b94285801d1091800081c4801440c030a0309880381400074070fa241c0d9a10380b800402c0c402808070302d09822598414108800116000381c028415500c01c15100e50286142040e103901c80c40015001590400a1540c050b0401409914540140c40c400c1141c0b0340306c07000780300f000d42002d03c520340007111070046648460b0110500e5a20902080e02d4541c1d4004003852004225402d4800c8a01c121600204040f588101c88401100400c40605500c03a2540082441c140726208410706542d030582d40403440228040d07a1065805560741c60b070b29005541b0502c001524991454050554140180002161808503a01c00030030740c94aa040e41682e81d6048448840ea2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 78066305 1250 78065055 78065063
    0x40f23060c101a0102010b0306040809010f260714070c03020114130902120705070302062a1318020f030609130b07030c090f05090f071416110406052b 66
    0xc2031049070440100e100c107039010f8260020007080c0d0013a020306484050842e00248a20010000701c40a980210a59000800301b441d00c2800e84c6c40802620318400303100c0c24416071f2485071402b00909560300c806c0c6040094440e10709a42002030540d50703041403060301e000090611401c0e24112540380f800c54203652a200c2c401d4421102c2e10f9445455500950080c031041c8040240000005c55060150f07003103d10881d030681c01091030342c2e40d07400701400b18998034109080c1c02001d00429800665410050841d0b1107110402441c000d1401c007a0b03003115854aa54000468014410f10a200c02d03a4002d60394002c40640e400422a030f6140118040600509401401c144d2a0003e12422590541c40050f22034100c0e1505940d964549514182d03441061003640c2d030000030500010340180038135200903000030840c2445031340f440701c4410302207440e045603c2d0500b64001246054040c05048043d00410710800c1e20100002401c110201c0c0c841d031000214401c4170500603411029500441d0b90b420050b40d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 78067555 1250 78066305 78066311
    0x1020c010c03020c07060306050a03060b01050d1d07050a0b0d110403050330130602070201110d12051b04060f050702060f03060907020606060910030605060304050102040f23060c10 79
    0x3901c0c8080c0003034114070103c1c50395204106022804034080c1c4580360503201d000b0100070309117146903544000340c118a200b107410803609010706101d024881c05060701e034015140010000110002c0d000b8900700c065800580b040319215410400c1055003412261041380601001c00d00050040c0101e00c03521440e40010b0003480001040a46810070718042d1520805c00b0044c0300c0307110075810302c42400314802c1c5d0b440710212100032180f00005030305500521400e48107040c230341030200038101e896003403c1d46501c004c1c02040007002c00d221038564501c43e16a02543d1141c2c050780050040c00c0c81c29031401a402654180000a20240ba00074000c6094a40e420b40c010700090f990b04a2001a8020b07402c1a01c00301c1c01191700c0320114580c1800440c40c584605405401d107070803d844502001200d01510545105050380d9010114032522420001c501c00c07030090300090b0380e0740e00d800c0350318414640c29440f00d1300301084021803000b003001d034140b903100044003141c60302c0c0c0328800c54181c541004600f1494000c4245 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 78068805 1250 78067555 78067571
    0xa0c050a0209040b0f10060210050a0f0507080105010f0306140d020307090e0d0e010c02030a080904090209090309030d11030f0a0e10020d0210020a050d2304210c0b160201020c01 78
    0x34100044601c01d817030f40258000c0079124009044155959800341e030015800002d00c1e0092101107602542d0300600000e804103807020308440640895900707895940004840d6401031006d56008401000c0440082c178081040368a8803440f103030356140d20319801d8468403200c1003500079958100403840140c4120710341044000c4803259002d41e09d05200480704081641c040146a080d8090481d02200940150160202c0c0d0030590f91080703140e00499585500c0390fa608041e07000350b103840c45618402c1d403582c0015070b6030310070200400d890b2812440d00042000302c1d12418001c04039000c0709aa000881020301c03035803a0440d228060701d001c0054401d880d00700101d81030001e112540000c440004076080e4090310380d0301441c020440c0903403081480c2c0c040403c10802500300190615071140c00e0412181c680d0f150000b10f5005842c0140201ba182961044070121030b51070780301c00b9082c400c3e030190850b040c6040b9801240e0349280000500070b0541d0101d80200c0c403401c042c58000c1d011181100c15201c02000415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 78070055 1250 78068805 78068813
    0x504050f07080f06180d0e060d020a09053a030201270204051b0702010c050a0b070c0b06030601030f03050d06050916080603010e0a08030a0f110408210a0c050a020904 73
    0x5001c100c0f4039880c070302c2040d000c148031031000c0607920706464000c07000c0c00c066800c142090780c00c06450b04189800900805c841000d622a51004d0700354440c00d03944000c1018074003000c1015100c2440ca00810800442c10841110490400000119080c00c00e00208095540c241640145851401400b04d28000c00c41c0100880624010703081c4640b0031a010456a207558540d01800c00344006550f08586013000f4000c090760288100f0b0303883d01e10078030407107012080503074808151090640e010300102e0480104582088450842c090788500c0550044c05a0f42c5180c446010100b65017030050248100010311030390321b2416400c46409801d021f071580e60340307040005801d03192944061403440012032038008106c003860306000700d1030300c0d0460f04003c01c48000c4c192115059644042e01c1c18104070303580d103040e10f840d5045007d21140444001c15850700c41c1c0c5421001400c0501041498401048030b5661100d01070460041d9801100689010b43c000f0b5400e244c41e5140c0031910001941c030409400c01c2200300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 78071305 1250 78070055 78070063
    0x1306090803010315060510140f0d0204060908030f07060911030a030f02070504090b040308270102090a0b0307140309070815090c01051e03060406051008070f05070c090504050f0708 79
    0x220b04c13484601031194002d1810700c0403a001030156580c0540c3d040c49481a582c86414041400c9500b820321070b03c1c01c021460f035a4103940c0304c204c64000380c5030081030420281c1e0300280c610008000c01400395181040071240c05c07619120300c00004002c0c0c0c2d683c1d4058810b010800401c0446040081c08944000c952420043c200ca07251400c440010b104900380400c16003410300658042c1d59000030301c801c02d074942d96410f44960200518412a40041058949141522481c03180d41582a00d00041e5280d1814041c845001d1050300301c441a02c004200b031140065106100c04d1160801d51501c68494961078083c604100540c4d000703950522030010f00d4203010241d108514000c41c0e00c1c408540307220840400544181c0140604c803020b190443c5d210010100c00c0f00011540300f1401000014060340302c00c0001d0740441580c03045000a405281080481d07a00900c1c441028401400e20505001c1c8558400c0795000c4203008a100c81501c0388081020888104401e2100070202c0080c0c401a40d203541c81140da03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 78072555 1250 78071305 78071309
    0x9030821130506060906030a02030a031101150501081f0b0d050138070609020d0506090709052a070c03050a2108010509040c09020a0504060908010606080609130609080301 75
    0x4044625404100c400380d207186020482640503000d4151039a03064108040c0c010010856501405126182c8005035000c1c4001e8548610940715200849800504c2e6030844840c10904658411815000d011a07078100e07030321660081ca6181e01003015000140d84196140d50b90780840c102d4800411505c00d1203203143c00050680d08083e10160000d03074080c0020034030801e030221400a045840c13030622204010b080003030401c14010345000c0ba10808590124902034060782040c0c40b02d400c55410b118101009210090060108540500c803e0800d0407401c5044504180082c0c98021201c24003580012160143c4051a40050614071607030359904205c1e8517083c0b031003c11034002c00b442e0801d0740710314002d03841a084043c00c0d9848038010380c20b01091203500782c0090030544100036003440000d10540c85000a2025000c250344850700e030361912101404008a54110310660790425100384000d585c0f0075449988008200c410b0300503a180e1144030b84414508500c05032180c0c0c00c03c044071003400303a58402141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 78073805 1250 78072555 78072607
    0x9060b0a020c0604050604051516110117091c020c030a080703090b040b040302060a030905010c030209040e070e0c0a0504030609030c03140c0a030e041409070e010f030302100c090308 80
    0x9500b007424041203458402c034083d0340c1d031201051200780454100034500e89240124090309500d004000151480154050b000443d140e00001100030520350744204110501d104280c4400041e06107107402d40d4a80d04503a880000050310348084500c6244204056050101c02030255200407800303090120703090303000c1c003415004102101d00004100340c400d0301700d804640c1441111401c050550703080007807503482003002c00e00f0103456101d00d1012410070310580e5440d00e020346005035554030410034041070b0f1f5640d05803a40c683e003080c2c004101510720820303059400072201040581c0c0e00c895210607903045c05181c10250507589007040c010105508102c0d003040c1c0038029100e0750840102e104500805102d50050b0450b550000c803a02c0f00080d0041c503100140030402040401c07944e400081c5041084004c465004e0150b1082c64204105101741d10000e004d080c150103034006060860b1000b075500c0d44040d0003401420b0b51031080c05801840b40300201c010390741c401c10541d901e0040045210700c690300290018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 78075055 1250 78073805 78073813
    0xb22080607030e0d0c03031a090a1406060903060606090d080d020406140a020c040b0f040f090c171504081201031505010f0518041a180c090708010b0304060609060b0a02 74
    0x2c00c0403d40014060307074595036a51440c0d801142940d0840160a6551207541a00000c000045550751074002151250a0000e00066528403d01500c11710440c0940818040d40e0b04024012a9444c00320340f06500c0310054411641c0c90313036401c0114200441c00311300600320386000705229152070300a400400446021382d4460100303615440121401e486000751500161b4060700200c0c9172820150010145101b004224088444d017100108007070381d08a400c10340c40d195482d00b542c000c0001009008000e02150003a101c02c0507002c070000759840c140f40041c60b01e220002e01c00035003000090800c6840c0388580d54181201940d4a20344034020340c05001344114100d080c100003044048500c02c28104071000101392108a11030360034103ca0304e010141040d510010104004001601c8501c3c0150041006450a805690324003901ba4109280c62610511404061082c004c00a074401c0846054804a030102d913a203813501d260000c010720446d071282559500780440000c03003810030390252554914079000e079 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 78076305 1250 78075055 78075071
    0x3080c1006050102071401030510091107020a0819021912060906050f07020601061b0614070906051812010f0617162301090e0a0605040b12070b2208060703 68
    0x1662a445c0074026188034428211145440f0f40c031a4201e42d0300014848200c40da03030b175116590703001502c1c441e0020f808855000101d003400c504220281000928940001d440e038641c1c000f0f00c0c0703560410740c000e002e44203102d007848a080408040c00305e0f20003410b060004d102c4042d4680740c90000751660400035510b0500d0200020407245800344d45034440c2100b035001d00816820034034103a518076404001c60b12508140c0700c00000141080c8030f00e441042100114000070301c1c040c4001812024560048001c000042c0689801c84031624085981c1c002e08880021205031113003501c500601800c4401d60101e0704003280011000c80300b89104403a60b44590a84811014134038003010980030500c00c441506104040000c0e0b00d006040204500300e40c14074010011903030300c2401440003007090341c0500540740c4c0d4442c10492450b02d4401d240500d1011303641910721f0510522040d031a0303641b503c13070b18080b020000390100c41c81040e000011480342c590400b011400c0c0c0c035071900c540d42c2c10085443c0f8000c02e01e44007003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 78077555 1250 78076305 78076307
    0x90317120a02030709030203060f09011d0307060209060f12090d0c0f0b15130606083403060504021308101803050a02030d0c021c0e030304030204110403080c10060501 73
    0x440c0c4956069618800c800d4a88a2210000b544020850070802034803040120040e5418440b007406410403548441036814052420b80c210f9041b010074a1001454162841d0001004000e640c210f907080300c0016114031f0b401020814071711600076500c1c2c0045002803a130400c0b40c0148261070195144a044400748040301c2da05071541031401c1c00140202c0c07844020540040c81644210354480a000b01070302c2c0e09035034071011510002d10f05800c802c04944039075040c040d5550081200e548100ca01c01c90240640c0380c84c10010b41c9840c1c24485a00150008080250080c080e8104c40001c0401410465450b11103600310303405088207000703212190003240b180340900d0390140240010502006103504869000756410b039a0341d07000303200320700a501042c000c400c1807007040d00c941294a80c0c95005006402115020342036806a030000e101c0a101080300c080e02c0d5078a001041d0760982c0d50540b00010304224440e84494940030700e0340001c140e1174001450481700e03030010500040b011407161003804802d85400c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 78078805 1250 78077555 78077557
    0x7060206060604090f0b061306030e0303010b03040b1305070801060302040b04020c071206090203010606210903050a030f020903010906150b030402090f0c070203010c091802040509130302150403090317 88
    0x4426501440a100078004c04125602031600c200c058800015482c3e407060108046800c00d0180e1040303251134200400c0100e400d809100090016580650b25543c1002004051400054800340c00030440c40c001909003440d0140501c0607903000011107800039034074031069000c0c28450008900840c03c040070325101e4145402902c1451300080f01401c201d034144900204c003040380381c40c1076522646807658072000d0f880a111b440d02802850341c84070710401d07100c14038030b049088400410000764504603582d408242c0c04001c3c1e0752580034034038011402600880c8132030040e016070403669516520703040e007200401083da4081c3c00d04007c400c4640100a644411b500c407240402c0f10041e40040c0e0740000030b05030091805a15902484002080303003068115000309007101c05100344000030800138801445102c10b80c0c1103040000c0c11648066203050304080105802140113041d0320900404088400b040500038407000d2218910600550003e28150038000c0140c2d00070310041e1003115980c0c503000c020001c054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 78080055 1250 78078805 78078811
    0x1a0301050c040902070f170904050112020a051203040308040f06020715020a020906010507060c0e19050307050609010c15060513271707051b0301050112080a05120403030c0207060206 80
    0x228829042c030346007000c548007a43c0710070422110101400b01d5030000520b40244070381320f41e400c41642a1520340031400d100468006030400c102d00d41107407945200582d01c020071070055070401c0e1154403004802c4408585036014903000100002d001081c08280414500e1161084501982c202c0c1e81455076040c2000d22080c07011020310041e0080406c0348007600300343c1112504403034180f405c01e1038628140c6411040b604440629000541410001040c5151907000704141c140790141040146280c1800030303544101b07a110341d07800307800003007040c5400c4d07805150110f103020b82000c81040713080c0c2021040c000800c0c06018441c80361900058a040b140030300d210f4400340c1ca013081140c1039a2144c00303000b11045000000121915010310445c0740d40e092820028209091060700102000703aa40031000f80702c80e900d8034045000361b140074010010201c0191005902c15000b05005a541c0c0400c032045070148642666004612138581c1400304055140c5e100d990000c850364203844100b40c4403e4104d0f101c074016 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 78081305 1250 78080055 78080071
    0x90907140a080709031e030306050913060b13051f090c090512010b030102400315090609031106090d0801060f050d0606180b03010b1614060103061a030105 68
    0x81c4500019079008001882d0040940d04107500f80c2550b0350303070f2030720310400c0b250f200098240300ca001d01003055054040c181c0607050458000b03c1c203280052103880d600c2104400034101c170752244a1261251604a100c85244050b01000d1002c3d2401d8980c0b11034280d0350074060800b00f80b000b000001e1036106032246070101740303c40c0d031808140740c80d21040020083c00703510352001c555640c104010340c9076000d01c0106201c0c80f914252102c405d907102c1c042c0c1d400885d0360781c444010000c20b9801c50010740718007000d80241c0ea805a00222031601c1301711004000c261400700204040e150183c0c910506400140c15004403132440100c0b80e00307075120031006031117501c500210004181d50900500c0707000d0191000300d16000240c68814100044c0604041c16920194007000201e08a103000143c80100c011104000d85030460515207075515003109540315100f5810269900d11384c48141508200c082030789164141004003c9420030b503101d04108009000a101c60612241c00c0d038590718040c201030003614459009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 78082555 1250 78081305 78081307
    0x507060203090105031b0c15010602010b040e06070f09030611030f060f0f09090f01050a0b0f0910120c08031b010c0201090309030605071403090d0e010302120a090507050d0809090714 80
    0x40c021b68215a01114207045150700041c0000141060b08211203101e0140b910200741c49035162a002030b007101e00c0c80503007038000da09011021103041e00024007550002003130b2801c0c207815400303034030111940c0c40181c0000307000e0303410050b030030103115143d038095030103400d0030414001d070340d120a0200300710340c42000103007a08142d0350b07107002c0c54030b1500002d400e0740001c045041d0740d69050f241d46140c3c00c440c011627044101655401250040303040009003c0038508003aa0428440c0c1002c2c0c0f003820285196101c2d46c0309081d030141055003004084582c4c100100210f038200c94030707000c4c1c4a203040b84c4004250201c801c60740c030300102d810f103541c41400b0b00e00e4102c1d0552a094121415515175002401c0010603c9090020b8000c26502081c0c0c910010b500c13a40130303030018010700300e1a0a8000c191420b01003203141090300502140c41d074041080600342c0c218150b45000100d0084074548241041e14503440198004162103e0006111032030f4001c0c038014200301e0f40680310f03036a01c2c841550b020303401181400e45030f04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 78083805 1250 78082555 78082561
    0x10305130210020321040b0f0f0c09030703060c12050603010b1003050c071208040308011d0112110603010f0509010e1b0a030e03032d040809010c020a0f030f050706020309010503 78
    0x800c4100103210b80c50500c1a00e1600000d603103400001940341c402d6801d0800414100028001401c00c000c1c0c204e03800d000d00d02503031305048102814038400601086010307140090341c2d80d60f40d0741c1044800700660f401718042c8146034000b400a4500712000c035103c0105420300d4005003103841c0c103104681603030f01c009024150b0780528072011001410001d1a98044d440104400000700304000c0c20100e10055039581d4505030b1509140082c601101030b03016003010000361421403a0045280c0940327042d02c500003201d2051101f14201070680c41d801214a6411450000000c140c10344c0000c03881c1c058610585071074030503036a9070b4424140c1c07490071640c0c0c13030b80f003001100407214120f200b01c001e2104a444d0b11700400c4080840840a055900549508400a02c1c1c407041072020b41d29021010804507411005000602d415101c0100600c01c0c0300250781040090300b841c030115550000e00001610844c8294003840d82c80e4a41a4400c09461100380d070340703101d50400050564400000c41d440d00c20185d5445065803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 78085055 1250 78083805 78083809
    0x1805100c03030b060c01061d090604030806011707080115020a120809030408010204090903030b01111f0204080102070c0806060603220809040203130c050303040f14030106230f0103051302 82
    0x104040303030210109501d444007011941e8a50000e406000c418800001d286490444080f8520030100d83c4100080128010801011804681903620a0700345c181300105640e0303400100d0b810045100050710f0081d0260602c00050781c403404032410f907070b100021140040c25050041e80d4070140044010000d24091108024003441440076076001441d0300104d03801d00392250501806e9070401d8100500156440311a001459414010702e0b0025800b0b0801310140070038040801d4840c4080750149040c062801403070141040c10368115002442c41100854a6500524007040700444900c03403076290780701e658045a80c52410008590103660f10701d0030070310702e00100c0e481011200c082d080107681c0400d0900502c1050f456078001940b0445d10003940341305981c90703454000f0140600d070700228060350090105120002e600410b40e000e4888011782e14070601d03010700000b8094034954001c00007141d000b82e85103003294058a0604041d40c0100c403043c28031090f0500440440d50211019410030300c409035008094 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 78086305 1250 78085055 78085067
    0x102040308031f030b010b030406150506070609020f030a0b06240d150e011413060602030a081b1c0507020102030601050715060f1514090604170703020301050f010501180510 76
    0x1030710483d40090f0001d0380ca803929010428240c2c00314410807400020401086458402c1c2d405200307042281140184c2424080790660041c10030080c40c403540c442c0001c0540d078510140400c10100142200c0d00b40c0c0c402e152400714001d050f2421805160740c0f400d45040d4560303c0d07909924440d001e0b2000b41c28100b42c402400701400310101030511009512201080780074454001d40e01030000e42a900c000703ca0701c1402e2105c41004050203082c0c1d0b500e44001800642d80c003204440ca08902d0340f810310b2a0361600c0102c2d01085802c81c0d40402c46450014154500070075603505001840023146013000b031079903485010f900341d1108551b0240041e070100420000034170198114404010722481c001800d603240c6231780130088500782d006080600809403a05c0e410541c8511254101e044001d0043e042c82c0703e24020039501d0185000d000c0060300b14412982ca100400c2200f00000d5030001d0003400359051039018980d0a103028058640042d481c5c0540f81022803070b05c00c2000c221000030300100701e05200c9074011206 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 78087555 1250 78086305 78086341
    0x901050403140d0207050106150e0405090c0609060d1821020a06111314030c0d08070602091311031602060907090c110f060a061e1206020d02030405070512010204030803 74
    0x800784d8280401004070350244900c4000e17040174540352400c040c90120143c01c0b507070f940d10410f02c1107050004000c80c1034408104800010029211030b9140e02c0d1160018541e400f807003010703018141c9032410b000c1c00300c0030f1a010304075000e0080f2052000b1440002c2d201d0380756402628000090b900c0605403500191060b1302c1400c4800c5481046800c00c001d0140c04801c003640f0b5070003035174403542c0800c1c4098075290521100c540f000f800c03180194500415a5107441c5405001d6024090300e1b80802c641c3c00c15107807402d80d9280c400a2050806c05444d0002c4000041d400665816940d12040b07211000b40c140001103160043e2000c00003451040d00d40314462001d4070002c0f01110070040710701d004013403008040101036111240b03080038001c10302d0494424800c868250b88081004622100090003000104144e24180d40800554104000c0142030240181c40b840305000b640d644004100300500201141c1c16040e100708a600c000300f4480c41d0700440c20b07070266002c054500c52080000c50300c69440d0101c0551 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 78088805 1250 78087555 78087577
    0x11030103050c130b1801151d062503110c010e01120902041b08090d0507080a0507060204050603190e0607021b03070504020307090602190c0e07030906050106090302010206090105040314 81
    0x282c104c8001e000c1020045080510000e00045100502c0364005034615006840e600c1d26140080d100c248588612915036003540900a800000f01e4400e06c20b1010030202079036031030905407084403041d450000c020a000040820702801100c0d400c1a942d032242e09402d06180050352903070070000f844240003004000d07001c4d080344c1c042d40e40c0d00c4c070041028201c0c1449510441e00d40340c085192421040003410100f09107006010860308000480010748964240d60600040d8175045440340e1041c64664001d1150b41c01c100e030b10840102c20400c2c15031207005540070002380107606000c207681605143d90345100544d540e030056003104162000b8901c0540300f401d0070403002402c4815660380c8a020604a910613100c20000420884082c01241e40410508030004002c0d410079100700415207420600032698000d040340e1001e01c0c00801d500910a4000081035500b1050811035543c0d11480a0080e251501c0200d0241c0110380000e4a42c41040c881c2030b101d02e805403158942140a0351505006a00c001040e0b2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 78090055 1250 78088805 78088811
    0x14060906040b0a030c080d18050d03080a0f0603150c1d040b0f04050906100e01060f050a05070507060e0307060503010e06011b0b15181b090d0206190311030103050c13 73
    0x40410b00842071540100a4440a80440d07540024018140b00842008095800608d007042005803600100f11901c5509490050fa064030746c15595405001483c0304a07101509000001c420701c07200074011000c0c03120500c4200701c0b601f5070300002c0d11244000076507050f5840842149036802e04142e00716655131000204850010b000345000201100c0e429598861958083c504010001d200e00c140d000240c030a04544542c9076141440041444604507285410050f01240d012072041c044c205a5509681c08403e4074401500e46400826814a48580030701ca8032507000001811030150046034182c401c2020002150746e21500191103146034142c68542c01d0410070100804208082040c4e8018007481e0403981081c5900802c005c10000d4230b0b4101c1500c001074006210002c0190009450090b000b0700c0042d0f100e81c140000038450460740003000c0d4000c1000a007082c0c2c01300d41080224040702598030100000d5441a80d000e10030700003400001d0842c0e110300741c64105071505032036014242032450008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 78091305 1250 78090055 78090059
    0xa060f02010f050a0609050603070b0d02161202152412070e040c03150e2a041a0301060f05130b04060f08030901110c0a060c02030304030b07080a14060906040b0a 71
    0x160080320022031351003060550b1000b040c8481d103240d010b01604640100d009111540c100840700900344110201060104d03030005100346485402a040025180c0189900703480500005010b51507d981604194190b02414002202c3c0b0000c14040c841e2450502d481d6a5106180c0090000303d04600140501310320a804000400701d00201410744190b21404100410071b01d1890034041c0400010040c45106042c51001c412480000501e04190000c0d0b0b50001542e00340c01f1200054452100b100b10b4206040070051181071210781c0250349100c030160001c010580e81c901d4000c85015907401490b07807102d422601032114818642043c0c1c0d54003001030000171581d5690038699545c51299104003e2500041080007503581c0101c1d1907414100284050f000328980070340019070056840c0110300c2840035070082281551401c01c00c1d10040c56201c0488055400e00a1020f000709904944003454a800c08100483c88084071180034018400989081e6560f02d8050400014110070907000b50007060107400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 78092555 1250 78091305 78091331
    0x250918060b0a0f0305070302090906091503010e01060314060408030f15040609090302240109090311100b09160504060809030c01061518050d0b040201110a0804050901140a060f0201 79
    0x41006100c0d64503403c244008040002d0166071000f8203500915105000069983d2100c801240e07000c20708031801c482c00d5950034140a400401c40c0086031301913103065010312129105603c0701003942d0083c0300018000c480304500c503a07103283c101d030000c1600310103002090310000d01c0c1109035006584191000420300780c0c0e0000c80c0880d89640c0c000a4600d4880c0c040005041e010b01030400c5281460f854840c541d040c04d2403041100106100d04040603030ba0f41c0e004414188200c501d542040701a8007910818040e505401c070190006c0c4282038842d2007900b02040e041c0c00499445402c03c12191030740c0d4103161420a040d11603100043c07001c00540001c004210701c5220a11524020b0b01502083c800c02c6a002c0400406558044031000c3c8404080002401681d554404000050354030440c80001590781d48012204d82080d00306011180c880c84507070501b01300510b00900305a400a441035103060780d8941c4003100c280721000d01a42c018a2a1070700740101ca2140b00350038220580340c0004a052064045 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 78093805 1250 78092555 78092557
    0xb04031206060f020a02130f050a0203060405090f0c09070c0f05150a02040b040306111e0c0c040b011b23030d06090203010305060c1c05010806250918060b 68
    0x501100000e091540c0c01440c0919885154040e26403464021201c540107807001c5c1d51410a104041e210316a0301480b001e452001c0c0c0c11510040300340e4030040c04a0b05208400c200a50002e80708030f88107a09143c009051200001001400c0300d21070340c02010b294000100307200701d0010142c000340c02c200e480109000801c408031b400d030b04100c2c8248024032140c0310b421004018410f0140c003617181c3e2401007100f048410350000941e41035980007030740012200c1c100302d0b5040c018031034000710440140d11401d480d050416283c0241c10083d40c1d00c02661a4a03030380c0340811007207541010031140442d1001825025071040c40f0324001500f072003000201c0c1c0700d8801c1844160b0b21513000012140d02d078000640c002900c01c0034003900005100d186c0c07055040d54155a141078656500420880708003201140034900680440454819540a40010000355840b1464180c4585045515844516a40c0030711030051001c0469030604ca22250b80d600047c5050804030920080703501101030140e91500c20115060050070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 78095055 1250 78093805 78093811
    0x203040803040219050d06270b01081009021003020a030b0301060909020111010203010605040501052506020720010912050709180b0703110a270603060f1212050c0a0b 73
    0x9400c06480b4a800d1042003000044408440c00c1101203031020001c5460740d071003005409070302c0880401c50380d95900808890710316100c000d450302d5620040c05020702084604103416100400b042d5104a02c03041005000c0c0e8682481c002e41180c918407910952910035400703440d1100d640d1130041401d42c20030b00080d0035200c09400c03040304980d5480c542021580c119030950700c904c80080007036007998500100540103014038421103050007000202859136500300303929926014403c0307441007680030380c5080010081d0014101120120750301c000140c0040d480c013409903a1003405030350ba803070b40900740284180e4190318082e007180c407445003680104a41000e40030300f1041001e940141d4280b07240904040300c12810103411881894600548006c207043d02d0802c0701c17000300c1c081c10000c403020182440810311041068016050a00000c8080782240c0d250f00b0003400c40303503044031032016a81c603142d4804002c940c0080050a40703080a4605031994000c0c4e02804520341a50241d610301055170721540105c0c0c1d011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 78096305 1250 78095055 78095063
    0x30a0c0813030b1501020c0a090b030f01110a09051806130e0a0f03030c05030420010c140d02010b010f120e0c0307060305060319020d0303090516090e0d020607090e1504020304 77
    0x1020801d643c645018013401d400e4007403004200140e20040811041440d81c0030f103102d0183c641400e210f040c0c50411070b050185036040020481030040d83e81000741a00b2403402e00c000103026400010301c9180616102054800c000102400f41c0c83d2801003204180c5100c1c0c3d1a9400317034507200ea4000f807820a200a4000078040e9000c80c01e030b074201d4900103088903400026202401803d0041c04086070a03044030420f64225810000c1c5200020780060756000e034001002400000c0413011000013100100d212584056940c00034005034084c000195002580300e50004000383c2d5200e206c0c110017200383c0140c0f070402e8002d816a403101c0410760201e410243c2d9504280702003030b212000e0200760704003006030030540c91401c0c40320a007249803a80001d2102d209002d0240406444212000a2040a01884241007110340c1c0c4200b404c2d586403074002c040c200c1e110306084a8080c00510020490000c00c640740f241c91643c4c0c880701d0075401e00070070048002014081d51003117490041d00a481d500d032440107500840c01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 78097555 1250 78096305 78096323
    0x71703032814270303010605030a09021314060916050706020403060c2006060607020d0507050915011107060507080706060902040e06031614040c02010e0303010e040308070809030a0c081303 83
    0x8020401602c0039100e420110f0307030340101c0c1440550200048242c0781904c881c0c0c60b0061340c984555030000050704190f48065802005500c20700001e040390340c8001800800c40e2291440c66079000f0401c4031050003140d14003031150f103250609442d540702e5401400c0e12440b4800c0141001d0300e17520703000220f900409081d808104946194901805810340d48000a4410001002140350610200d140d03405107005c001d0081c0946546c1e441041800d0180102400c0d000d000d203c001e141242131560161b02210b482030102c1ca10085165502001242e0801500c010b40c44192810000e5a181d0106522816007507640c40d0399001d020030070190900082004040b2244058103d003070560802d0b050100e00d041d00f003110f2030142c0040011100103c01c000b903031442100d0000e08200c030084182c0c007404d5680360020355400000004512548108182d500650007980c90b00319598416200380ea982ea02035030080b40d10380c0103002d80340f4190711500142d4103042c8100440c509040b5610f50906501050307800460304a08 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 78098805 1250 78097555 78097561
    0xb061204120912080a1d1e010311040f06050309120301080d140a0806010302030a0e0a08070303242c0702070e0606120103060905120f07020102071703032814 69
    0x203070100402000e442d0005402c0104049542c4d003011600c40c2450440600c104214080c4c402e2501c1c0c0c414084092001d01108610501030051030713401c0c2220780b006404280307864888100d00b640181501d00b5a09020b040c00d0503181000ca0540c0c081c0c1006054591a205e001841899960144040d6000700301e40e2004008125880350040c089030f02e1501c81d054040d9091005040e855480250300c0d800038401e0800603944d807580042600645454020520b80307100b26107068040040705001464154040d68040001d0103900e1300001c10704007512400144c800003d003080c81183c0030031462440b401c14260b1880d441c02001110341030803580490780c940158100141c200300c9250200041c1354861001c540d41031511480b8440e00c10034040600000e03100540d261412000c102007040b5003a812106c260301152070f4400f001c08084a1780c45210101e00501400600080307584119611098011840d406542162358855660b0b030309005a090912001d40032000e02c2c21420000d21a4a00805401402ca00146 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 78100055 1250 78098805 78098807
    0x5030a260906060103050a0e030f130906050109170109060c11010c02060105031009020609060f0310090506100f090b0a17011401140c03040302090a09060f1a01030b06120412 76
    0x11015030415408103150010400390103004150150f000c802400c00240507140d41d0390718801480007107141102840f000499181201d0254007500c00c0b41f44148844c4050340c1c035201c104003078640ca0b10410307012862070001401810080f100410703902c141c101c000914003071aa20350000382c5104400000116007a210b007108480390130300071007074040c5180c001403c4951504002c00d41e210102d0041000d100d070385501100455603020215031188100418a5849880e0001080d00d181d1003960313000c3d0301d8a007540b00051b091410b4040c0900c070340380c001e0031009011884c507020f0700c1c444d6500d5164800c00ca070003840801ca0b604c4001c0600300ca5a426902e844440010005810312588181c000510541c2801d4501500d0b82e4031404592031042400e00250300c520007546414079601454100941c0526044104500301d00c05da030011445074000c1005002410f4514014012503246901d0302007a14204542e1201e694080d804c55488810081c254034504a030345200035045100540c2c1c100c60340704410000a6010f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 78101305 1250 78100055 78100097
    0x31d1e030c0301060311121e0609070801050c0a0c0203031201090510050103140106050a02070807030303140a020315060901110102071101170f0a0b040b061b01200301050904050a05030a 81
    0x282c00800c0001d040d034450701003c100c0640428815038204000802441c024488032a1010b01514a03041c84642245a0f50701c8400403500300d40c01c0e201f116800104181c0c14000d00d0300a02c2390300c041500d0300904d00b00071120141d0500042c0d806100c00c2042d0089880305c2c0000c0341c0282410300001405041000041c40b04000c82c1d80400c0c101f60a04070f08508481c210b18110341103c9950a02c40c7c0c4da103200c0002070341040b00760341c410021400b8012000080c0740d01508417010301d403461072510000d5950320551008078002540e58908045040c1140e204a09240703005018152050410140c3c0d550b00c512250309a9000788001c64103180d2a0690201d1f550300400d6220307101c0c90f107048c1c401c075501d0700b44a0824843c1c40180110304040c1c4510800032103840c0c650008160100142c10107135508814500140a24464403420200351b10300b415081d000c0103251003103d000714800011500d980d1070300e0104284010302400599280c010f244010000070310400c010500c0035101e03118607140f000002450f51003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 78102555 1250 78101305 78101323
    0x3040c0302120105010f151b05010e0610050109060f020c04090804080d0c05010501050907080a0209010c0c030602030915010b09090a110408070e090a1109090c04050903120c0a02030304031d1e03 85
    0x1503402807c0008201c60303089043c1030028100c03a0102410038900e410840c0c0542030801d100ca900340202c0b4140580407120f40d441d50250fa01c280c85201f0310f95603a9200f140c162442c0740d504030040e0401030140d11540381c079401c0003407407074003a40c040f03400c02e52290b200302d00306020308150102040c420b50a0300300300708080c015680100401c48980e1824a462400603202e0710303006180b0383c0c66550000300301240e0780c042c0a807000310a410000b005003603901c03441c1240c0250303c103880d02000c174814602c1e5040600803000ca001d0603141202101d606045e6204180041c400e0058240d1130b2a40d19003481031507060316440504002c2641200904d401386c80c00e40c1c050f251000141c035800294020a084502180303c007040b60b8100c260030f0b036100401d5a151042e140c1030078405a00c45500908110034440301c403200002802c21024200c2e21005a6120740466404502c140b5926101680082c000180801d01072004590100400c408181d07081c040c50001500140d5a0b418148551000e00000c0005050070091001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 78103805 1250 78102555 78102569
    0x60a090e070306210b01050d050a0f0308040221030d020a02010209040f061a09010e060c0a0210111905060406111b030319090b1503030903070305010e121c0203040c0302120105010f 79
    0xa4070803031905c940819000c14000c2d58002d0032090400e00411074100f003510300458020244000d0400c09160060040b041036606a00c10080804281d500c03e0044d4a4200d410400d84c0041d880c0c119030042c0e520280d00142c54010a40d5424086514152924042d2148219045c04000340050616514803080110300341d00d1901c2d00fa05024410450360802c800001d0b951003101c28a0300d0f1039400011349d01d40b00c140c4500941207909450070301c00d07031604245001c40c0d4101e60340a8034071754104508040705a540b114000781c00c5a1000300400c010072000e84c081c201420301080014944076241f44080130b8098201c3e207040e1642d10000c20842000c0c1c580925082c00f440e0824113100100e10b944550100381d8024040005028040f00012540d640070070880b454124081d06450030607503281040703402459103000e4940c85020700100359440e01262001c65030049980241c0c031001c00c80c680700f02d1009400c02442115000c0f82c81c2404005a0341e41894051440032100002c103456051200085d80a521940181 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 78105055 1250 78103805 78103859
    0x16060216060203030a020d0615030510050301020c0616020a08070803090d03110a080a0b0a08010f0f02030702060f04020d080f0a02010606050a050f070f0209040b09010b01050315060a090e070306 85
    0x4400658040104d94000310f81490161301d8003001040300c4001c015503404006401c10b841a08492682c140d002603201e00c1d1500020f40755030359690140340c240e1150401011158100c40001044900840d0000c0800340a40c0304841203071507542e5408001c0c1c0e0100c4415542d20320007004120010400308200682c080c80c0340317004d002103284844054a24003c14400e0001e125803d0001480a10540d00c103035082e03c00100000c0d4a40d6917504964020f07e08841d80664090900080f0002d04109000322401a17440b503000b00440d503039000c8101403005002d0412a0b00034045400385021a91a002904a000d030103038129680d0f48460030068215540da0f4010014400c090050700042a0818142e0f4060300c003a40b9440d68440c81813a014241ea9050b4000960205480301404140540070010606c43c40d000402048070042010054405010803600c1c90341d5401d01c000612114141a0f0244c515030720182090031300f541e10b4042405050b03404075803120002e9900d240411410880c000205000708401d6286 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 78106305 1250 78105055 78105059
    0xb0106030c092c070e010801050906010903020d0303090b0a06140307150e130c02150f04020d1203020702040501090b132c1c030b0a0902030907090c09030516060216 72
    0x41c2c099001445480c100001039018880c8841e02404244481c0d201d105030800c0b5403a01000140c04101c00c2d03a030f00b500042065002007503904141499a00a0005031a06404140f840d82006080c8455141c102e0805856124090000341d25601a90045050040210358981096500b42d110039030900079078840c1e03000b82c07410041c00743d21209140b95075040303240a1030120142e030003103030904003401e03c940c2030780c0d00e8005017101c00e40d030114401d40041c4000c482d0728581e4030f4074084016000c1d01524041d5200c80111a4a00090314108030002a8402c900703016050a4a42e0001403c440702603000e603800315110960040320b85045c500114000708403000402440d801051144c918240e0014242e0806015160703230490031000b007003101c3c189202071a200420306e452220007406080700c075000074050304040d040807a05c500a4005e030392103907604030002c102c1185402e01c04005040488130380c00a000c2d50001c0800825414000c8184115405460404091070102d0080ca04607200f82c0f0012041c030341c8001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 78107555 1250 78106305 78106307
    0x3151203030f0a050603030a270314030301060f0c1e151b020601170303040f020102030c070306020904050a0207030c020d020a05060c01050103050609010903020a030c06060b0a08061503090709020d0f0204080a0b0106030c 96
    0xa2626008002646a041d24024000415031909c5c66080601034504042c0e117070541c0034000000710706a134140c1e07450414001c0500020780c2d40c014081030083c8202e00341201000885040405071114500821518074003810b00d040f00b504842501885c03140784001650b007440c145404015136801071065596a0b00d11940c0c0c04007a44d140c1c000900700402640005069400396032082080e5000301e030b01c0c0b1056540d61130ba02d00e001c0300298007109404d40514205800542d00000510a40342c4464164880933840e06455007080403021310b40714100d0348801e2408010a83c2d490b0b90740a4041d40307140700700009465045007882803912100800a185580c1050803c40c00203034085070303c87ea0035501d410080b07009030b500e2034203c0207800560814522a140401c8800015a000082ca401003200350390080420102241c190b5607440300702e5160070617a00101d001c010100ca1640184030f1026000e1001807111082c6003010143c1e809684414581d40c40015020305110310120040d00400300c9003008c008041d24114 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 78108805 1250 78107555 78107567
    0x1090b090d08040e09060a0c0f05070303020c07090c02070819170307020a0b130b180304140f0301090305041d1005040b01020c030a081c05060603151203030f0a050603030a 75
    0x800a8001c044909014080006440584014155a521040251602601c01507403000300302c4000500c5414180d00301c1d20350340140300d02810a42e940e0b884615042d0325840540180d404401285043e01c85d20b180040e0080d060700c0b40401c0001c0680c054143c9900e0000f10a241c0030801c102640080b050700062030005011000c04100707007000048041c0c903907980328016810406001c074060290b91406041068605a910354050980e1007103800070951384503407110700c154000b52040045260320070042170082114401462200b024010103007103031000c0308408a400e45080300021000b02c0d00105091145010304901507200321000303007a58a0501d4082d1000620561070302c180c90007141d407099100d4040c0d209004d48201c465000d411510f9150091420030003980c03000d0000004482800c41441c916511070003800d009100040409080d500e5007500303070003200103207600940d00110518001c0d22960341400a58031030b0300342510301d00e22407a080e9585c00544000411007807094204012090001350010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 78110055 1250 78108805 78108817
    0x5100503161401092102010809030a090e06030307050304180c140405090a090203011a0909010b03120307090806010e0105010e0121050c131806080120030405031c020903070501090b 79
    0x1c0050b0400c2840307900103961004107604902c0081024104211710040c0308150016442d00c00e80c1c03404d000d0ba5403006e225840740100c001200001c1d80c0403608100c0c45595088941e00918001c017a00c0c40c003103507a0303036031450750340310754020a104140102958a01a22131298036031142281c02c00300d01703050f030812048507584181e0041a125a0083c00420719807285548403610702c80d8090000c1007200e0451012000c00b1022004541c071455407240040c2d03004c130f81030088144144000e0020004010a2941e15090b078100030b18074010002c2224002502e4401008500c0c028040500001d5055040400041540c0c0a0703014660612055150401800c040901c2410145012140008603911105c50010f050b21899054048194000b000843d09125626800d903201e07030741403010003005644404580c20b83e4010401a0342c550b5816601c0d01c1010f1003c001103510a00c40c00a603403416803506250f802052400d12000750442d80420108200d050401014011300402d080c001c100e58074080c8049030f244160 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 78111305 1250 78110055 78110069
    0x71a0304171305041a030d0504050a090914030703080106021002070c120c05060a0e0120030306090a0209040603120809010605030c0105130e0c0705160e0a0b010e130510050316 77
    0x5800b48039103200010000190400901c207000b14904030460b0310444015120742031107400b54081141a15000740c08440890b2409800f80514601d012002e0009056040703040d6800e003030090303508110110034030007040000d1003611014034550412070000d180c22124104403441030710421900020500c1242a001140c4041e140040200164902003c6c04e1119138055600040f0110302c030581c0640200c1c40c9103652100ba07a074184040300485500e20400700342c03e0011080c0c1c200300042103550a0010400358004601c5030301524001d212000308086030711640c01036407050b000449890241d035000c424540c021769484002c2c8945030034400040d8580389402045070622070000b490b080410030000c070b204001c00c9000e2100501d482c00c90006070580d03000c940100c5c5d5a0084545d140001d0400b40100c0044d2800d071802d40d0307515900e00385400c0007005017421490500512907c3c00c80c003a964811a00c0c0010580702c008191400c0904120403c4216504801d01c280c110300c400300920b8005c410503008850030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 78112555 1250 78111305 78111307
    0x1203050403120507120e10050f0702100c0510060306050f0609012715090608030c0c010302030a0612050109050c0114070803040311030a0203040317040b030f07020708010e071a030417 80
    0x1051083e1440c1c410424000d01c03140008221402e001d401a561072000003043d070fa03250f50b400d041c03d0100c9083c4118010a1440074080c0325010160600203040c0880340c0340c0e8200740ea12108107466480c605118008040980e82c3c840e00144100502c4d07004d22604013503907421582c401d082560000d54005014040e4100030141006503003482500881050011403110400300070a0340d00800814988202d401803080150804000055441c00041192404d030070340d201521030854400c0046002e94000b42038a0f0084e0380360540842c4205458070519141c5110380c0001480389194a0400e09240110283d94107121001104003054240794007142e4119500c6845d0716a25559072a0903214813aa00c000c60055100110300390703070740d160000010010349010b00140c61030b140703901d00110401d00c6140076800350000240013281e0480c480e17140054002c0102d0054030b40130380d140d5542500b19040d49228103200c0c3c1c80b045040000c8090480141c062452126880c3c0c910300e0980c441500e903580e02400c105007100c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 78113805 1250 78112555 78112583
    0x30115080406021b010605030d170a0f021902031c11040902070c081903030501090203060d030c0312020a09030b0901051302060304030905180a24050d020d0602221203050403 76
    0x10141e0f045584800e500b1443d00f0b4144aa045040e000700264002c0c603009119030145013128038014014403907010040c200100543d030b2064040f2028051010b000a01070b0780071702c05003640850303c036040a0701c0c450700c5e4015900d6917a0004c031011510b4900a141d200c1034034000800c81c43e4071101088406880e000761016035209401e02e004051490143d100410324050600b440100503000303051441a01d0082e0b070180416601c401d0240c04a10080e04d81e50b50100036213201d40e00080c0144840c013061402030404000b640c1e21002040140d03440f100700e07940095010041803040001c400e411a801502010082003185410600d407c20304c255284040c2c070504011000600300362098044501a040140518030034001c00d04102e01081e00645440100c141401509040803c0903510b45600d0005146400c0c516454103090090401c203104099811000401c4045c001c10841e00082c40607010804581c035000060800e5800e00060a4102048681110400102080c0d00c44151400d480e009404110720742 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 78115055 1250 78113805 78113813
    0xa02070c0302060301091e0b0306071110050c0306030d0302030f04060213120602030709121203020c0c040216020415060e1509040e0d030b061c0e030c1002030106090b0301150804 78
    0x12410740c8020b42c012400000410511600d0f0001c400c951204840251004140d000d580e084e43c8281c40c02542590040c000140d015100b54164820f01c005042581ca2856001c80c049095072002c0350034044164000084c8510743c00d040080c010055014a001c60441c2004c80d41c1c0449040003070000751a10340c000c9441071060341d800c3c00c250001d01c900c4825005040040c50718402940049903c3c101042800c0800100e1460321b0380000c0005610408200c4032880b4000e02b54001e40104400d1240740c41000441901a11288002c00c480d60680005884c2e011031441040250380b2843d001e16540d40b08171104201980d005507c00013400011a40c2020b8400d110b1202c41d0036002c0c840201d1b5216050080d2070f070340603102184030310b08080d0b207560a10001d410300d000d002c498810882ca401d010f105118010f5540301907030344803818280070181900d02c2c1912466165181840c5030640c441074560000041140da83c008031075200521070f1581035801c0d90324000084100081c1c400c101c00610580b000010104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 78116305 1250 78115055 78115073
    0x2060f07020c0913030801140f0108090f15010825090b130504080d05240108040c1212020105070207030c03060b01020a0602040b13050d05060612120304030519030b090a0207 76
    0x300d200680143d4a0b0f1501854804180050315416400309a122001003003610000040d0303810810054540c604180c161001158407145c0146031000901502c03410311404441400464001e101d61207200300c8a50600c60928201034030030010700d00d01c000003031401300441003032031205003221030025002403540110030204080b03030b0810003d03406480c0340408020800060b2406404d1400790404100023507602c80d100300066502e02d00c0c40410b8000c0c0110714520382d40c41802c105500600c2004900101d40c2d4030b6201c0c00300160900310407122040581030f601812a0309202c0e0a80c0180e0500c02440440d240d0784803201550418000038100c5034075410111101d9000308004102a58851001c5655075919030f90019180c00c07000c0c101040002603a40010149400c8a80c200302e00e4004025011548a0343d007081490b4402d5403105805000d0b0300e5061a089a00a005d544110301948500d5518100166a071040c07035404001c000505242c20710300740c40340d240c00400c4d0f64094400c901c010713503c0590f41017032540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 78117555 1250 78116305 78116323
    0xa15020705070906060f0801030201020601090f0207021201022502060405040e0f1b030f06012102010c14010516110d08091006030f02090c18010f120c0206090c1002060f0702 76
    0x65032080140019440d0180d9015900302c6441b603950000812841a003180d80d100c01303200c083e005034091030050240b03408079840381c540c040d5800401858040c55a021400c1c00b03c48a4110300c40d40d501040031100b02400f40500c80083c024803812041d50010b40d030021340e1a000741d000d00360045550310808002030a040200d40b03041460101160250010b040d85446103039000d2460b03a00a001e4100840c0154000040341030685da248008650401d040c0321200c9002c0c080d2240680c1040760314514a000300e60f080302691240701c440c2002207518a0414840311444000c0402c8008001e00d85140c040d1100c0081600203095070280760410068480003100792801c00b0841c0f88101c01d85c507000000041003581e03001e040b8114825240300c074065039054030383e5405000d03480c0380c40e0090000c1424565230b58441c480c10b44070b03007240f4104200003440f413544071000c9403039104c0320001507440030050042101c010080c41c100c800c1c04407030a118401210714003d4032680094442100b0402c0b03a00442c0210340240a5542 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 78118805 1250 78117555 78117563
    0x11808070b1809190c180b131a030610080114120115091a0a03050304120305070c080c0f030c0109050103180203060c03010f1202150d0f06080309040f02030103050a150207 75
    0x403071420000a520b5100c989494001d000918010390200c000c0d000e0418401500e5101b400751040a03d0001e41a046030b00103a0a070b020642d40c05008910130451480e801c00b00c8480205064032480c10600f842100750100310ba0806000c0304100400400b1400151000c1115054030780c0080e0700000760030280506152000c45e1404460118045503081e031950101004208868160a1006d00390f07061004c21001408050003640040100344038400c00c0c0032402c0300d260311a181080c6413007502e03101d25100702070035041488141c00014641d12146403000d101160858110060003083c034813000060308040d103a00c40c40381070686a5201d0a940d51041c0030400d031090300981a16200e141c4a1160381055000b4001c590000104d01c20119410500e000c0c51190f803503001e000300080303852000260107240c001d2452190925107a80b0a100090361600415004024820085446484075010001034641c1d42c14140d03105c0740f05000420206e1800aa50709003550001450000c0c21500000b03d00a481000c001034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 78120055 1250 78118805 78118819
    0x106080712061b080601050307171003201e04060305030a090f06081320031204090c0815040506060d050103030e010e01030c0f0e0d05010f0b011808070b18 68
    0x2401070290369801da00140724480410440703c07a803081c4004a442c100710800041c864070001940303540507000071500019103042548030044215040510803a003104c1c22400034030000d00400c1040b20100000c40c10310f0020700443c5040c8452808129003c3c14011619405081c800304440d8546586e80704001458009007075980e1420386140c003a2080505114004c20900c0b283c0001a07028072892a0501070b8800c0244540c0089941c0c4800101500080140c0ca030f9003e00980e803101c0356000c210f030303480c192540032610782c840b49004090012600340342881c400303001c4a02c040090807aa890b00041e4070390341c100c400140513150600411818041c81003c1a1441d18010000c0145074104003024200003003640c55181500c024401101601c041a860001050158180080e218014100d91240001c0500044140450781d143d05080d50410700400a10b1580c44a14406550307114a2030510398000809c1c00100714074200000f55114528411801d00220118904800c0d2032054151078490070024405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 78121305 1250 78120055 78120059
    0x1806030f060a06020a0b071808060907030b01050d020105090d030203041e030209060103110a0c050c04060303051206041803080c0702090106080727030b040501140f0103120203040311040b0301060807 87
    0x52031a810041d9041c0c0d104440d000c100180d428400540b40b03414652160004049840c0ea40382074400e0081c00492400e002480c6802003840b04080016510a1000c103004181d40351039030602d03400914040c3c04ca84d01072060540403c0250741c02a0403103050f400140c582907265400b0342402c90079070003a0b8010004c1c5900c83c500201321011541d100c1030a6a00850300d01a1644494005604403000c07809054081c0c10140000d583c0c07030340209148803605004030305031803007011010b0024040310329a402c102c01161000c1100d04148a054841c181d000c0c80c04d54003040b421078a84072f5241c83c072040c60380040401091200198000761181e007601c8806034091f26012155840e20400b802600040b00c004c4006002605034003c0301c00d00305182c14112120181480c240750454940442042e130081c0180c07915905c035440c010741001103d68480c40b6042c58800ba0402c0d5041d481e14202e6410001e8050382158002d2005101007006841106a00d0004403800110400d10001281c05820158800c1800f0f006035040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 78122555 1250 78121305 78121321
    0x1606080a0e0f030a0206150901090f0905030c010f0b060906040b03090307060c0302090301140c040b07020103090b0106030902030f060106020c040906140403090614030114040c020a121205090c030a020402180603 92
    0x44c00c07828a050302540c4c01c41d43d681c5284415522184846580034002c1c000400c01c000055000d60380303030b44402c4400b042c1804103444103451640005580c4000d0382d0346683c8000e41203664414540030501c00c50b1390303c1c070b03040440000494034012402034600c40d030000030104240712800c01c100d900066110000340000e4a00450250080d00041c3c0c10754080d5003001000342003041005e2031903203d01020055141030a09086c1c01e0345064105d40c2c42207040c160380b00c015001141c1d0452080703008109a540c040392105c0b01e03105040c00c202c0c10380c074071400640c0400010311649070080b070048080078080e203002807080460705108020b071101c42d440662512811042c8002d0540c001544401d45401d5181e081d400e0f00203181c1c001c100c0c4004d108a0b043c81c1c40c5030030b201100d407405400840c040b00d02c40c0304a480841c0a5107445581c3d8002c045040d02048a81040c000001c60178020160b12106000281c034040400303401007512003034580d40003440360307500040c1d11100d51000d5170500b80c5c25202511468880c5080c1d18 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 78123805 1250 78122555 78122557
    0x60402090d122c0a0308031b040312030b0105070302151302060c1b0307050d02130204050a0e0f070f020d0804030519022a030d0c0501021b010c030c021606080a0e0f03 73
    0x354045450102d020fa8841d119022020628030b80d01401d50f020191542d2260843c0b9080909942d8a112844500040e40409040940042c50280da0b941007850079001d4098202c1f40049445410320001f0302082c0c0109802240710120f144040004030442c1c4d8540711910150410b0303400081d03108601181800c00010b0004410b030203014610959150350b8900c204056490b210b43c0319496000400c100500014100303801540800580c2200240c103080c0c4500c001042c012817074001005614450042003100381054071201e8000c481410010701c0041088802074844485445000a209480c07000c030301014810b8045501c54000581c3c003050800300f0b070000030340312034112031008c0c4d4881903400c1e007075200f01003000c20307071403a88004006001c1446680026180d00d801c0103c1941c3c21b540c00e018007040303400015000251f0321401c600015030100fa10300041e0440c0c500d400008115480301d00f41c104111520307001d01041e5030403818202c40c2583e40d0500400034124501d1031006c02d00a0410503004454000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 78125055 1250 78123805 78123827
    0x204051e010305150d060e0106031a040303050c04030816110637051902010603120e09150a060507050307050f0307032006010902090607050601031b05030312060402090d12 75
    0x10b42d05000356218aa84114102c00c1e6000e2964421510304001000442c20752040e200c9400141c00811081d59940780d092403084503400e80140c0701014010001003561610416034080512051a0708160440e164050306010701ca030805003c544001ca400f090006510694250400041c401c0c5e686040e480a982184580c14800d41102c6400b900180e10740081c1c40360a00008806a50743d5003001c103c2840c2d450b2000d40e004038001903558808000c0040388041d00a450004681e485010b081100309090119515008007130710b90806605150300001e5031a034800c4c50407501d4030306e001a11104a0b00b800c5085100354000100944146040620350950100103040340354000d481d4510502c1d10f40803171180c0d21207140201c2c101c2e5000040144801065503010700050007010308180d003003941950307610b45010400e800543d81c50400c1810705866101807a52a8013a00c410b80245082a14446545403010b501a050301c2c40f1340e8000c50381c041e80e6140c00e201c02c2c00f041d0300440000030000401502601d400504 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 78126305 1250 78125055 78125057
    0xd12030b0102150609180a111e010e01140906210705030103120c0602070605180f010603021806030a05070902030601080a0501080a2006040602010204290415030204051e01 75
    0x40140d2560020851075030b0315000e031001903c1640d80030100081c500004004000f81000b42644400103103040016100f100e20548000c0c0707906040d44108007003c102c0c0e100000708983c1e0070003d080d080e40d101204514072802820001b4580203140d2224005000783c420140c1c10a07404508881d40003038100844914491f850801104d03a291208211544e00c000d003c060000c0b020b81c45801e603803501c240c003414201409404010308181c40307540c4000940300d0684e4602080380d90485001a81601840802241d54400c13008001c81403a650105603407448550303400885c06c4510000400541b01407048000b56a032040550ba00300b0740360000c00001b5041034400038001061071300000d880718285d215440c1a00c0340c050080400d41c1641e41c1d420110300c07450002601904500e841200c180d1235040150000d01320a8001586070b0342002445000e004144d441210f401c407840c064a03186010300001c136070a41c0c0e00c401d0b078280403060b80314041e03001e1710803603112541140010500c042d041c0b010280c0c0084000007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 78127555 1250 78126305 78126311
    0x2100507110a2001030908041701110d0b0f040507020c090a0f0c0801031703040309090b1f05070b0a020306010e01050a110703060501080c01031a06090a050a0303091a03041101030902030a020d1203 86
    0x3c0240114103c40f401003000f0024001040300340500e5803040c10801c040b403543e03c00800c024410765405551908110a01901923441d40141d81c054602040034140940061318200500e00d0300c81002951106400c8080e40150342060115010074269000415400705142c402d106541320150b0007080f0420074401924000c428200302c5060100800407240901d406030b5442c11201d00f807000900041c0500000c144e80800d01801c520148200e40a101800b000d003522502d494a031a0b08146020100003040c50301818410800c01c4441d07a0000f0711b0010080c028a01651200400d4505444c64044128440303100c1c07040610010400c02c403600641e0595131604250b4001d5a40c1d20019030039140e1601070f4080001ca0030342c1c04000d60400001a00c2142c00040c4000011540c620225540d00515007003900040d0540b4000c0c41013800e15124400400c80a415451035490a903c584542010780b0403000d041507119280030055507800c021650610f500101400e04548480c41c1c02c0c00404072400d1350f00c0109003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 78128805 1250 78127555 78127613
    0x806010f09020424050c070e090c04060302030a0308180708010c0e090f0406021c060e09060108060f190609050901092f040522060204030215090102100507110a 70
    0x154500a8800b101c505a070f80c0e020340c1004144d49403840001aa0300c42c1000070520212103032907001c0140c10020035404241e94090304240c5a1a030401e00162985800346040400801c010784002900241e079542603e450f05003500c0d87e805070782054443c10b1580f64944681040400c0c90f01040d8000c078095160f1340c40c2d907540455540144441030748201e410725000c0c51514000b5011130b00640040030980c4100c54135011400416000504a9810b03402684105c0681d0303081210043c01042068094a0744000818142c80d010764030000da054020310401e07a140206419643c2c0700d10503085000a422098001e02c91031901c0d103600c0d0300030190090142d50618140300c0f1208000b50041c0000b031100c942c0460a801d2941000511000d07041c0a46900a0b01d1880c411841440c3e03c100f0180d45801e100303d4001da0354030305e18010000c400304005c0075011000804c01c03a00c0389582c1c00151407556000100008102c559840302d003612103050380c0a00c40c00074021241d114040001b0711680c61000c0d000c003940500510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 78130055 1250 78128805 78128819
    0x70602061504060608190b0402070b10080102191214010605090a060e0a17031e0d0f06060f2607030f05010f0b0403140106180c0201050601020111030a0c1202040806010f 74
    0x1541d40c031504c000b155a80d004556014120400358030038500c502c1e00410b004861034003040c1203a0111105981841c0d0840a0194202c0004c22030002802e426009504020818841440981c4005211400e204a000303040000132a80e400600010700250741c42d51280d0ba540601030480d90194402500c280102c25010600a00504ca210b0710400e000d04070741d40480c200f8105207400c0442d0014500c8a2000b80001d01d210b8100142d12800c1c0800441c0c0140c4401c0e110100f0390a546010010098080c10041c0c1401000e50002c0d03040081c071043d250404250045001c8440c21160003003520b1103c440b900204040d60341c1540000c2030140c948001000319a03607502d82d01032490071a000d00001100104400c002141889085005010396140001481591850300000d60215548000d48141e100c600c1058074a40a10505a02603000c1c0000e2100d040a103c1c080d403244001004400b40c1c0d0740d40ca140c0d0150500c11102682da5004420b411940c07a07444640003aa030318400d20843c2a4510702c0f02001c1030350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 78131305 1250 78130055 78130061
    0x711030f1c05090d0c06030b01020f030c060c25060c021504020a060302071a01090b09010e07120507050708030a05010314030720040902040f06080d031103010e0402060c070602061504 80
    0x52409800c542060001c0c281c0c0407611540025845588034048a1a8201180707403456404010413035505c00040c0f2418041c0003a0504c2c0d007440140c8520340007444107482070f0001007802e6600240b10410309946124a04003241001184000810007550310030803081041351584c0b2000103800950202e0f064080000350100310380034104c500a402403140c207010010b641c000d401402800740304118591052210140b15541e2a400341e21511001c1d803501455000ca0801d1207210b4050080111074a0780c1c0c0c075003590003414515035580c400c411a940c50f0f001500842c071800540e1421540700301203079070303034100040c490020740000c0c00141c40b02d00040407003004d01d8400104070303501d0b95402100c0e405002c80c0c0c1482101c82503030003144136401c943c4448404006969911074035101180300c0c0b4000980d20b0500e06030740d2600e00071079420300500d40b83c8000c40308a00d15200a0303070704490124118031003582e22480455180d0095484510302442031042c08100180c001c03e649100e00000920740d00d040428000304429 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 78132555 1250 78131305 78131323
    0x2090a0603170d0216030f12050606091912030503011a0304020114030601020a0c0305100608010204060504090f0906050f16030c05070209090703051b010801080705091f09020711030f 80
    0x70b001080804400900c201c60003070421400445001828030300c410036951401d51282d282140011030142e2072480f599001408803482c0c11500508100514000007c200703144200c03c501441103034034040320b494060500c03940320003500318009103142c01c8a4503d4090400d810a004001c9882c021410340c590702488141640e1042da016550045420011150745401b1740c80505641c1c11402081f00250106000c0c001c00402140b1030401443c0c5480480e5106084a61035005112140d00421080100d03907031040a0b0b400790350310300b1000035900901c40b41c460000d01900c0f10081c0b0582c2820104100d0700c242045440c45401ca000040b80303030121110303080342240c90001020010407400d00481c07015050440110740c0c06024081110101da07140c2e1159480d240c0c107105a607820501d401001061540d003c1c2d50035004143d9000144000350500c40020002800104004002411720401ca6070500c02006400001c0440c150219514060f078140002e00e92099231002d030183c420038030140000c640004103c08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 78133805 1250 78132555 78132563
    0x4081005101e0504050c070b060d0c091a0d0302010204050a14150f070f050303090706140f0a021608011b0e0d1101030209060c010c09080706090b0306040608011802090a0603 76
    0x155a9040c511442d0030030040081010550204280100b119225442818000d054903c807041c0c0380c00d00c600d00107449100003041c071400f03400b1101d01c0d24006100180c40d50266520000c001c281c505c0c0d0704004e00c92411021050381da201035540000011f0540643c000e105442c000d80381c5620207038490740743d0240c034400c40c0c0c5101c2e040000d0311620b000380c010340c001170318128240ba031000d46050480c0e00c4000342040030b07640c01d84071904004240700302c00c40c0410103036008120b603082480080d42d03802a0103959001303c0d20103d1181100003284280c0034400c2c4050303054060b01c1e2040381103a980f5000858000d00b2004440300700160982003880046008160a81070300134001d003298001502da565080788421207995513814160213008540140e9104c402800c07602240400010b5103c0c4102c100034400c04142d80308241c50380024805110283d4004100c0050f40c040600b6140d981d12018082002050f055116500e194a000714080c200303241c0c10b8a00064600071911076500791aa454640d04036581844020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 78135055 1250 78133805 78133831
    0xb030106030207030c06020a11071703070f020316080a11011d0f06130b0325050706050403170406020a080718090504060f050708040312060e04241104081005 69
    0x258030035001060528400d00e41721400d41c0e090340da018180d0b04075031348280c0071500030381960825038001c0103100e0080000300204420528000e02040c1c0304e03c903094003e00700f00182624a070075501c0c1040580c3d400c106a03180b29000e150717205910f645a1384d445608540c040c0c20702940210a600c203107501d07840580101e1003403a411b804882040f682c809800903407500618180180004100d9200b82c000082c0750001005941e8030b800d200043e40141d4000081c802d83c007404000d0780809034044242e41456a01145c001860384850505440b4a03d803040350701c20042030541000200301e034980141047d00c0030341d21100b20944590a003602c050580e441c86031000300c26000e0400030724070340b03401843d00940560400180aa2024001001c0c1e80c4111a03e00124100c20140410141d000e200c00b0f04100491744100034450402180c0220400e018002900b02e4110703031000c80c40100510101c4040c190302d49000c1100b451011400c80054020740304270742c034a0190000c140c002c11403c0c05544d101e1240c1e10180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 78136305 1250 78135055 78135059
    0x71e0e090115090f061106060612040807030e030a0c05120705062209090b0702160e04060e030d15171f0c020304150201050a23060906010c0b0f040c0f0b0301 69
    0x291280c0c4090409541000003a100000705242035008413006014980ea0342244044031356001c41c036050000d4402c030b01a550400c0211820601e44d640030380c0083e4414041075a0f100242021a4510810507081d5490b0113100c1c0c03010200003454110800b1200d05651500c951860136014540350005807140e01d80025007044013030b0b04541d0307200c2c10408500c4200c3c001280c961700d80820700c04690a810084940031005020304c03040b40c0d0100488941d0151000300d19410030f05020b88146c0280f80540000c0c250307500cad50300b2400d13021401d0003580c00c08103141030304002580c512030070201c0707030800c0d03214080600f501800001511080404c2c5064601c1c0701c01200ba40c92034440c29004014500f000107407046000c06e20004c503c0102800c420801a001c40d4000305035410403d501c8000c031451030340f68104e854101c800721042c00500b0781c101d59003d042200c420f00103039120401aa11900c00c2034005215103c0f030300c10480310f00205400c1c140200d0096145c4241e2946404620490069901071300c11040801d00c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 78137555 1250 78136305 78136319
    0x60216061b0e01032708040609050d03090306023004060c02010908180d0c06080708070e030a06050c0f0a0201020301030b060a0608040f0303060b030a050405010b01050405061e07020306071e0e0901 86
    0x400205c010398080c020003181c01a042003084e0401e0302600312040000001e0400c0000e612036001c1005c1d00045030790300402107050707602600041c8144002050f0766004105080307150126080c940012204901c0124022070203120007c00030b6003240c0465542d07242144150100f0320510825042981c840340c4103103802ca01044800c000030806000a520480301c010810024a0201c03002c1c008040684540c41c150501080241813668010541001c00481100c3d4800c10381d80000c8007402c09800081c002565140e00804400d0361103801d450700b00c0040005866445a82d0550007541224050b081540710303603c0d12002c105402d01e4a12032076000900000c00729002ca000385405c0c0001d248242000580e00d9594540c42030345030802c840d102c800c2992601080f060200038019a00400424a4450314103420000040c0c000e00400c20b000045110544160040722207000c06c44500031780050444101d4710784124014101402c03402c081254440050000f00c40d64050206051013407070003002080d46a0030501 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 78138805 1250 78137555 78137561
    0x703080c032e0b0f0c0c061908190204060203040812040b04180b090103060504030221030c0c0304030213020304020114090d02100e0d031112090904020f0607060216061b0e0103 77
    0x91600060b07141c80310000f02001c3c150014050780300000c0100d92206004000c690070008040501800391804004070520608070000180002465040020544e01c80d0b010344004001000c546200c003500c0020049a010b400001800860f1001d8041b07541482c001c0c07440d429140190322900817921070600042c042030300d204011000e0300140c62400510307250350100140e0081c4081e8004e0b62b41c56a07800a1105044d814040121042501d8201000351008845101694440100100303410100400c5400c1401001e0088230000c1d600141610201e1002500c041c009501c1590301300c0c04030344070300d04020300342c4503c40035a804000001d01c1001684099001d2114800303038180e06008101e00c2c02814480e6a0b901d00c0c008a02c640a5580d020b5207042e2000405d1410030b8403000240e0240007404001ca650380d81e44200c951269054404848201e50f22020030118011044020a1f0070300100d98103000309088404c0310980d80c017454050100301c0040390f8030000ca03007184114000244c28004451540d5000e50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 78140055 1250 78138805 78138871
    0x9080c01081f270e0a11010212070506060102010513050a020402130e07020a1101020307021c060608070e06010e0f31111801030c0c03270602030703080c03 68
    0x1903030200c1030b0329150a18411682140c0040c0e00c426240704580c03c08030701d0010185883c0c2c0c1000c0b000c1100e5084080300345c4d0f4480080e2001800c0ea1880c51880d20036074828480c0400d60214107100c152a00e24030324166480344d004859090040d0300e441c001998010080d103209034165004000380403944615001d10007c1d5000041143e880821380100040c2100c2d03c03401d252240549901822131840940b070300ca903100240e80721540c11507005108100142e0760f074081130702c500d62241c08004803a2409207809005061958030101203401501000a10740701c503480c0803441034400b66034200c02101c002e810070200c2508400c5590b08080310042c0a1701a81c50300e4900d20081e20741186608580440144038409d9034030105a01c142c00324089541c0c0020010702c0034990230004242002d2205994840700100002c00d00c8001504001000440e080310103001d00004042404128031000d00544500021f5640e9001a4080f40082d00c14000100003400314001d50780220980c1c05003402c60200b0280300c280d071b44480703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 78141305 1250 78140055 78140071
    0x9041a091608030304030305010e010f0b180301021204050709050c0f070201020a0605010801140903040605070b0a060504060b041e080c1215040f0b0f01080a080d1404081909080c0108 80
    0x10034541c0e105100440031600200110001182d4902c0c0c18640102074403810ba214141e45490710780180140143d49840c03c0c1503c8502c1d810720b8492180411003000e080050b984075816500c005070b100d95808407907149603c04c5015034201c4100c1d0780d41d40035440071540201c6d0318170003115044c0300c4c01000080c1ca000078142c00d4014811a0507042c00c0d51218421240b0a0344001141d83d929800c1158024240b11140d5000c8a41070107503044c285010405402ea200c0c081006110760b01e4440003031000280b0364401009800054800c01a503a103800032038045600600541ca1041c0000003410070032240384d02000280e5005c4009042965062800c1c040101d03d000c2032816607010702401d41c0c090010700c00f0440c2c443c9010385180c036800c402c00e04010314104c20244c40d03902c1c18030b101c000601c2822400030b654020613038004e14880d615000d0010030340052403081c26020302c0b603003040144000e000300c1602500c0c219610b011170414007209001d080d204081e007171081c50400c0e0020a502c1da4958040d0381c040d5444035407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 78142555 1250 78141305 78141313
    0x809030a0207060f0c1202030415030e060601030c0c05010515010e04150b0a11011a01090e0c040b090619030e0705010c1a0c040b0310090f1a120f0d030f0b09041a09 72
    0x20f658410072203070030946d40d440040e4004a010494001d030718071a41e035109100e0a040042d244c1e110441e5440e40d50092115041c15203900100e04c1c400d21500c61044100c3d00013000304098100044020400c0c001e51410500142c0300d500302850600e4640700700a40800c40c50440c0760b0300f5241007030b80d416036003010000c03406000811086901640c0d0a020b003801c1101201200b49540342164005403814949400000121a210b004c10000211850480c0d05503088508666116441c000000e42e03e81305a41c0c038001448041c824400d1070a4240d00b002591600c1c88042d10041c54450004440184a0520180070008540740000c1040f00680c000b54001c0b99881d04c0c0b0b8a040c1c1c80304c0501d400e035030003034070b40b9004000002d0702000100c013070344500c1500100c0514148035844490a07910503520000711000d02c9100420400c5581c2a02000700078001503151003910423600285501034002e00c6601000f1145a052540c000a1ba190000d0303501c0c45a540002208000710f91840314041c0b29000030500d0950b803103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 78143805 1250 78142555 78142577
    0x102030114091905041713050a060503010812070206041d180c010e0904020f030703080a030609020405090a151a07020a0e070212031e040c03050c03010515010e0102120d0c0809030a0207060f 83
    0x103881b41c001c01a01c0310344001d005000349480309210080b18594405820040b0130320040c0015080401c100c50110600342e9625124450b6000050319441542e000d403c01d02320f51500c0c07003c400d003e8800144074000042e140f07110503403400c4e0b1280c1c8a03009018440e00080c07140080c1103ca150202041c2c1d00140068050764240000c0f00121749090140c1d00251203621001c50302c41401030b450701030440070f0300340c0303540075401d01c0c0c03901000c0b0b803007000041c00c9021115243c0c01c40800e07600b09014298018100d6088a4448500320340c9121405d50101a05034003c502c14400880c2d01e504559610340900c0841c1c1c002d12a4001c800c41e003158541014020010070540d0408410440800b40d440c1da01440c080d107800302c036052031032410343e1030502907141c00e034002e9047c0000c0110349542c0071807412182d0002e003800d40031f40a103040100d04140c0090380c100c2c10301a01250614030315407540d01c003001800312901c44c2c02c2541c640510440d40da0145024500050303100190900903a8890444108540c02906203195000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 78145055 1250 78143805 78143843
    0x1a01050a0e09010806010519030b040201050a0203130b0c012412020d050102070506100501020105040323090405041a0c03040b040609170a080708060a0303020307062408010203011409190504 83
    0x903400b03030301683c4c890f4048001802140703001600f0000c0b40c0c0400d5548001d151856581c040c15820040019040c403501146941c003860080c02126080c403e001000380c106a201c9201503080e400024503850369600c4c0c1402c2411b020b80540031154200c0024500786041450710207c4841d111003032000b05e0304181d00390b1200d00003030000d00107015030780e200d00c001d04400c1c501501c10000201484d031100341160b040200788401b0a41048808045091005025820044044c04681288135070181650054a814204002c0c01900c003122814070455108102c0c058660b000c034408140001c0e10090030407800d401c00f04001480c654090310810381304888034866035849500301712554101884140100301d414080080544e808080c1541c07225040b21598000da086480013941ca015203800108155681d0384074941003100360329200c0c1040e40e104800b0711060340321101c59001c0e40080c401c10982c0c501c00c2c16901035500d04029101e100c0c45651444213182581d40c060040030b41800303032058401413094004c0d800c0c88 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 78146305 1250 78145055 78145069
    0x7120302030f0a180305010b09060406150c050106050a08100c05030c0a2a0605060a060801081203060301060b0324060f070b042a06080603030a020309090411030a0b0106020c0102011a01050a0e 84
    0x21801b41000080400980050040076240204110302c510b140c903805100401e01501e0740b1420250500d0021250340092030041c0c0100100d4011070360141c10003400142c0d002d0009000440c814807070409001c00e4102140c103584078002912452070110741800030000d0302c0c5c4511501c1403030501425040302103080044200c540180c20503025101e560b1203108100c0113040404415008010920b06a04c0c10340c90007101c55140e480c0841c0003181480c000000c696142e4007500200c028102d0208115540e0a240e0000c8245120003130b084170503072502c0036071501d103841c3c0305041c0c40c0c0c014804d10000345420f0840d950005400401401140c1904aa0700390003a0804100503810f40c508030040448922404c0c000c014094000042805202c1e51040000400d080c4c0e005c001e9682d40c40e8141c4098419480c0c1340b0f40900520340781624180c044c800c03410481d092100c031038542c50407101d0580a640807051400012130070381d006181202030a4060350301c07584180d4400d80c028100500743d458603800c2e01b00003000250107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 78147555 1250 78146305 78146309
    0xa03050a0201090602040e04021c03140f090a09050f100e1303020f0a0305130e010317070c0e0f04020f030a0f080a050c071203020106060c050d050f0d0203040f0507120302030f0a18 79
    0x180387c0c1484100303c11030801103a5902e0041c000400701802c60f10320f590040800c080040c0e0b2482080003c41d2400412802d802910030048009048201581d01e81d58001c004260440e00000803844113000704502042050008050721014507031040c455446000341340700c2c2c1480041c200d04510070b54001e01020402482b1150302103109a407241d076074a4004040d40c642511940002e458043c8074401080060744d0400811002e040b00010b054440546080550074110207034058601c0c54200010012029800842c40341b2807071084548120740161181419541d142c46103004211a07107110b44140850404800b07081610302901e0038074030301800074403110f080034070755401545d0131804c1000300010150213002d95809052076160425207900643c503100d03500c0085815032001c4c0700d8000fa4070b00120b000082111502070303c10300255501d080074a02050700f00d100d9681a100d5000710840801c1c403000440310800510303010342c025418030505004500c01076110390600c0e428071101042041304128142c085c000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 78148805 1250 78147555 78147569
    0x8070b15090f0403020d03060602030418020c060106050405030712030f111e0a1106130306051902070506100e090a06150807060f11030909040f060603080d021e04080a03050a020109060204 82
    0x80a04151a005c0d16002070740c4503134004c1c9030a15a0520a00f0743c0007044e6011108800034685400c1003110303807000240300780d90b518292409094004554560001c009008845040c3e003160f51050b560515180100c40000d4000e0020311081c5039806840d22464820a80c402c04c0e4080d10a004026100d10b81480414080300d290341e00240306503020b0090302280c0c1d00c9049001d54841d854511150884d00f4503400c24000200340b542d650002c41c54410300000c0565100d902e80300c04640d14152170030459a00c00782111840c1c0c45010007140800e840812188442c01144803000426000e481c650703511011308840048041d1880c89044000390720348040141d80010032090700c45400848040c00c008040041205070304041d507008000080d400d0f1038080d27586078000d4200c07003100c04500203071900c031001e0151544040c1c00f4035004104034001543d190300810070580c8002c01c003c20f405401c0707190115400781d48581116a0030030b4000e0700201e8003503001170244008501c000580342465658a0703080760041d8016103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 78150055 1250 78148805 78148831
    0x30c0506070b19060e1f050a031109040302030409060308040314010b0901090e030c030a0f020708060402091503030c10150504050405070303050714061003120203030f0a0209211605090408070b1509 86
    0x300340c6c002c0f6139150300a84029a4401503c600315251131250907200c2c292180102d11160005007450b101f4800d0380d016101200302400559500d080204068025000541c0c440349408220b04149605100d0514541700103401181c40d81e10306401d450003010102c64074a090b002c100815405d0900c18402880c803403145c1d03140d40a440c250041d0091500401d50880041c0d0b500003018000541d98411515074015803500f074070407250036028082811030040b80641600c501c03805003110381e02c4102e5004030078280c0865411303005070b9503528108026140c041d50003800700c5d08084003d101080c46034000f08400c43c000c088074082c61454802d19441e056040702c40e4001d07106c0348141030003008608d4683c0003070301503c0d00c02541503042c040743d6103112480203010840d80550004801020b61030352107400384480980c400c400ca083d00e040c07900b640c4841c4004c044d0b0303811114580740400c0c0340c948002c4c02802a5002084103050044035906c1121058014001008090baa111700d8481640d941043c28130402e81c3c4c410307034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 78151305 1250 78150055 78150091
    0x120d080a0b0d1b17150a0b2b200d0f052518090305090d021302040807150f090e07140307051209071217040e10030c0506070b19060e 58
    0x310002c40303540c002e60b51300c0e600f00c003a18040101ea0204882e4000346c404038001241110380c400510301c85815461015030b86040c0a91182d1001c1451032651460b000c1e40441540c102101c1c00402d015085410740d07a0303c4a40c0700c24040104980c1050700c024584200d00310b9507508034101ca40940742c4003009000c00c00c00c0300c0000c1844804942c0d00204c2c3c1582950a0602c0540000c1d50003601ca40611100180036046449060f801d5644000460034403400c1100215619074841c2c08041e00c03030b0400e003e82628030414140c5040141e104032525410026183d0300c1c000c140c2d04103440500f104001a041030304000404100d24100301c1c41c10021030050955031951a5200c1c021144c2c1a10110024440b413020f8005440c2040480c1c1e488410302e0b8010b5110200001210300e403401d07040e55005070f030070481d005001c103020083c101c22220b20903c00d0340c4c001c080e54072001da42e40f030400c85a1301c50040300405041c1c6036008508c0e1003107111308103100c1b50343d4280081017040d150484960310a80484500c19070240030002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 78152555 1250 78151305 78151319
    0x71a07080c16090b0402070309030602090102010609230603070605040b1c0204180506240706090602030702060402030f060c0406080402120d02161e0323010515120d080a0b0d1b 77
    0x84c42c00c1c1e10106907800d5051241a45010340000800c1c8801747c03001d500000c00400ca40c0c801e5000e4000713440b2842042005e09202502d4070b4000345049d49c00c414603078446c0701040f020f250010f00e260440e02c031951110324281c148007408545811582000820401d01c450b019408007403400540054503080d0b41003e0f8008a41d00b011064807000382c8540d001c0c01a0000f000c1a00352800c01049054124041565803121149456030080441d031101904036840070040c0400380390702050080c040d9000320210360f03980064685103a100c02c2e05441d8124a440c04203c02c20040740203500c1c0c035034000d0006100d510a40c200115050030305030f000f440c0c0001600500542c0321000c107404c2e603080103880380c08000d0310f01495907038403074820380050300006c1c2104580c0744451020b80c8071001a101e4560310078009000608009000802c02d00c03507030746c0c0240718040800c0392546401c0001102c6400700d10031f2f81c0c2e000e8607450b488021070081c1611340e401500a1a408103a00200d079040806801144441c4140c0c0300c01c0d0f1404030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 78153805 1250 78152555 78152561
    0x30c09220f08070b1b031608090c04090f0c061b17070803150111010911040207080903190308061c0b06030f1b030106120b191404080a030b0102071a07080c1609 70
    0x10880f5281881401070048041002410440d07c01003030034403500d05e4555075050340c9030402d014000c80e88141880340500410650041c24015188940e0341c90007203c1c0c5415065690440e191040c24507240315007034840c04248280e0710908004416810603181108540781c00c03100394800c03030b070303800c1805a006001012964040380120000d44900e00820500000790f40b1210400085003845100c1c0d50081118014020f40400710381201000404580003400011100c007202c090a0005074082140703940000e00500740680c202024440d40b041c1058040c0760f6594024241101a010341d801d4441d400011020f080d080040320006404078640409903a088001c00d400d4941540100030700d00b805900b05d00006c4ca00c051081d8200821600400c921200c41090340020320200680015034000141844140245840104249101c0f96400e11810106d000103a03614105840340240040c0484a2081ba0040e20000340042c54410056149060f2203d506540b40078884480c15061f040448820010005588 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 78155055 1250 78153805 78153841
    0x304020f030d020a031d040606080901060b04030c0603020c1f0b0f03150105130209031209040f0506030606010507080403060603050303010e160207062607030b030c09220f08070b 78
    0x180200100c0c0561200252244d4881300c0040c14062141031071100c0e040d08041610400c02c0182c01002020303a1030b00000c1c05128251846050b5520b0104080303030b21326025081700c2c203603034100d1103400e5842c1c9416421802980841490721107409460074a4aa07001c240c040450380318030070180807036032649032410094400354150901d4403c0d8002030030305c5949042e0400300d40c11580225102d503400304020351441c0107442001e031516898000c0442c2c8990301140c6030064001408280d400f00300281f002110341c2c3c12140152105940365010310001056980f0400c000e126492244813103a041c20b50302d40e1a50180c0307140380c100712115000440140040400046c0c16544071411141c86125001184c402030340b41ca015004442c100030148464090072284480c20b0308420034030b0b00f14000c0b03d14050500030000c00e000c1c80045e10a000c1c215428086161230043d403170281c544641c201e200341c0c40b407400d5074441e00b074a21030854102a800d440325010410440c040c0500c203018800c0810701e442c100035400c401d0340101c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 78156305 1250 78155055 78155059
    0x114040e030c06010303030b01111c0905101710031a04141b010f03110d1b050705190609050f03030603071a1603020709020c01020c06060a061d010c02040f020304020f 73
    0x34071142c880d1400000329181161341505000440308007410040384c07030b11011480e103440c1d4420b89a030303031460904003022014049165a1041e400603114010070450844041081340000c04284046040000018886801204450465614680d65a54144074040718a48440501a0f007020002400000001135002c290420040d0200b180c04503d400c030b4071001e68504034100b01c010046645140d02a512052903142819030329034444005043d903001074500c07401119801e540c0d900035072520300d00031030980345110791180150807014041c2046001c042a02941910f200780c83c7c8501102040381841200c1540590402070750360b924210081c540b40c6105039201465071489441e86031200400c01c07041c1ca00395808048076900561050804a25280c0203402400145200003000d2045800550082c001d44110000342e5095a40d140c08020003041075118500119290441441c011070364031032403144180c4141040c041907941034004c101190240302d880801d03654004248025450803e94254100c802 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 78157555 1250 78156305 78156307
    0x31e0301050a0e0703090b040b041101030e072306070305030a0e06060d06090c09110a080a0b090414031309020414041a0f0d0503030903130807080a08030601030209090114040e03 78
    0x2502010904069442c45007140d03912180d40414042403286e007090307042a03041180e800c09400c02d402d0003d01006c054804032010030000b00200700d154002e0060f40a01744070f040c06850114508030607101c400c0380041c003444055990a03c0c00c0701e80e030b403070502410889009581d06902ca00c0c044114204070790303105640f40703410f60002041150b80d995001691001690100d004901101c4500e481c1c04c020f0200d4200f5590302e403c001c0d00f0030200d04604090800140036a0f5106215100c482c0070070119501151040e401100840002e03000c100c240400240c220890012a07280281c4914008051002500050300484d0005420850140d0200c810b255013041120208040c10761203450380c02e00c00311702c0b045074054580d03d0b00c0c04038255a400303041e502854110b010f42c1d03940e1801c0c030441c1d5200e0340010840b40d041e10651002007a000380c000b40c92802e50f003107080181840c0030261102c03c242d4100822182c1019001c001407059915024140d43c000e200710006c0b010700307000e201e08000c10b0b243c20426252003640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 78158805 1250 78157555 78157559
    0x1060206010b0403110d081c020309010f0203060d081606050f0a2405040b0604080601030b06030f070807180f091506050d0305070b0702010905030315011803080319061502031e0301 79
    0x602ea01c0d10001008115144d0f00b84030454600100140184030b848c81c041c51100380340300f2018035a03400071480742442ca03000b040f08920710303a5080304900060710056017240e115480d520004030700030014101ca506000410b9003074051640e508041d81c804892000242020400340112120305008000c0e1106000e440c0c50b100f2040b0b003207100c090709294800c00340b042c4d44031003480d0041c1d110241207034050002e90060322407941e121b0034241640801611054007d03c94001e407110320450101d940029500b10b10040d101d82803809074050207440125000d100100d0f60f51440c00c2e1310307916900c034400d12244102d05540c04145031809900844115500085c090828006107900103680801129050340e0720913500c2e055610380c0741c070480c018004407100801910000042c0617407072014281c00c0041c420240d882c84481c080f07410000304d50246511004001e0340051020403090402c6100442600d40403940005607295107058a4206104031859071000d6040010340c0503044220441c1d98240650390754103030346154 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 78160055 1250 78158805 78158813
    0x5090c0a0e060c0f031c020307050a03090302010b0d1202060a0c090512011b050310050402070f020d05010e070f0608010e0403090b180604091415060a0c030203090d030801060206010b0403 82
    0x84148803241007081142005419199122000d6510703656a407021502280d0020702c040380e8070340c0000c01261603400d244031045c0401c200c1d802120301c00d1500345d0b1000d0801c1074090042e0045c04c0f00040403801d5540b01d00d80c40c41592580c01c034080203140200c0842d810070b251408040e08011019044400050a00c6013090403141c00800080481d00c0a8488040803850787c8407150040c10b00c0c641c220046031030440c0c0e00c40d80b1076020000d14050810407031f1410303840e95038104020481c401d82d80c005184178161900000035142c0b0307800c1ca00115025400220b042078030018003034144211a007081c13103c0c03003880c502071020b99440001c441c0940b050510401645c109610064801c000b14030403070000c3c2c50300064075a03002040000100b140200502856180c070b8443c11780c14051702502c26100015104840090300701c0050750204a00008090800703440d0108240c1b04465a1520701c10070b03000d500c0208611032080d218511a006054007a81c0c46401d10750506000074101501a4401014141c062205001003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 78161305 1250 78160055 78160057
    0x50405010f080f060105130e01060203090a060c0b0604020702040b04060e0a0f060803030f0c0f0a050904050604050f06061809131a07120b0f100201090b0a060803030f073605090c 78
    0x1300900700300d41c4820f441108081402c4294020b240045207003000002d4031070b0004080c02d040c410880e080c00d035894850307174211145000d1460103007010710b00b4408a14039050070341c010a64940090030200c0c0001c1c03494007182c00d0314406d0f440b00d21044c00620410032a41c5080c4104000301480c06801d110b010b1400d041580c5e24040600444140358400010583e030380323a038100b11040b0310103285413030b512408410005032290f000011014091810500002e445140510a0910443d050b03000e03052240c96040500c0401c5d0010b11a02d81035143c1026a0070140d51101e40c501c2c4508600caa0022800c1c0980c541019414420003aa164101e2a6414881483c0d0000400050310035401000101c09190304006617461451309901a04101940740d044c0c03840c0d0b4190481080075002c0d046000003611000d003420102c49042c40784801981051010440080e02598a40c0d00021030703140c110300e44d9040a4a1140890703c0310900050700d034540120000d018050a4188001c090403540c0940c9450000b60741595 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 78162555 1250 78161305 78161311
    0x302010305090a080f03180d08010f0605030c0304140712080403140a080a030e0114010801020a0810060f08060406090501080d091a0d0504020312130e0109110403120e03010507050405010f080f 84
    0x40e8002000080d41911024002e07d9641c00741c034212481c03c0412000503040038801c1c090350541814455010920750b000750100d80c000d4054003125859565070f5240d50041c00c4076200741d621140500340e8005020b206615200444a0043c2000c95407285103150603000302140442e4030545800122500c404688004107980d00c40d849810007081d40104a50118010410b00e21800300302004240003045500e8154064009991540c594254548500e8444c1d200040c2910a5a0004407000b102c00a00d912410b8401c4e00118007400108102d07484510000c20351b00240c01c916019400009a50a080d500c14922001841d4000c41000200118016802c9601c1030918281c407054907603000c2070443d14104424903200801c408250307201d29003040c204030111040c1c4103c00ea00ac20100000c5030907001340c0f04002044550044c4a4502843d603a20703040340f0b60810b004881813040c41d0240880f035441c00e002c3d0070702c20480e56540c547d44905000c00500005c05a03200ca20030001864204060090041c00d15a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 78163805 1250 78162555 78162577
    0x8011109120106050d030c06050a05040b0a1e020304050f0d030c09090c05162001020303092d07030b040309061107092c06010e0105060c21090315010302010305090a08 73
    0x1000540703141254050001d60b4481c5811541000d0f50700d05140d48200b218002a100712801d00039520780048802c10380c0c00c10340d40544007002020102c1c004528076031058012240800d03249455846c61103440c022a0400c90f03041d02c0a41081950100605042c032036031020007654202001801c0707125100805002040c00761100641c0e07256080d6204500643c151181d03034003e0340c9541d0096210386086880070450200f80b00750402400305a5815600100980344500340c41401004004105c10013040c510715180701e9854503aa0700340c84039054503014403910010318080c0c0b5040343c1a0410303207002841880c0a90000c1c00700180d0140080e11003e010480301e00710b40c900b1001080041414039a0710382800c4506215202d4204000d40304200c881c003003441c50403640b2114101115aa0358000e10a1501c54080c20902e16048050061f40b68442401440c0caa080030081c018104030038000404d06c0c200c0700c4030100031000c1030800100115030b41800360781c0d0300c0480030b00a48200345003aa01c950b036500406000340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 78165055 1250 78163805 78163819
    0x717060601050a0507021e0405090a0302031801140a0f080609041a0703020d0609090c05040b010f110a0602041d07020c03100914070e01150207030b0415060312030c0908011109 77
    0x3d5260f4441c00c1a20315054004100c20031a81403000d0958840b20003042242c022800d100018200c4180803e100150039050b40165261400e9058810100035410070601d0500c000700840c0c2c3c0120035424090114010140c807524000c2d022560090306180c002002e65104035042c0c3c0c10800043d4050036a0034410306403510048240e01c5204094019001d0000c515026910303113a070006003031080b5080464420b00620b41410000c5e1070700d040c802940c41103150140815080c1900c2d45039a48181c010b6044903210009a854a4041ea5103481c103a074030541c424400030100d031291643c13401c00310400a4209020f400181100c45500300400d440300e0604030040002555180498180300d28003100912104a44060300c20050f260082c20003c66400e000710b51444075046440e1001500001d400c10940b03030400b881d001d01da617071951107420b045541400564181c2d00c42c6400030009000200e1a0b0450140b03840204511203010300040031003010f5130001c2850303030420301821000019041198482c4106440e80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 78166305 1250 78165055 78165067
    0xc0e0103030c0b1503031c0501150e090405070302031002090301180308070509030a02131b0504080c0d050c090a0b0112021c1113080102040f0905090705040e0f0a08070203071706060105 81
    0x4201c1e10081008042e094080069202c24003c06a5000c003100c00b03034111f04004036620b40140351809001105500c010030302c28000140c0c4c2d480c080207456406445207044136500c80c1c60364003090034034124510506c805600400c0380d90941c9420700403004510f0078000d0040941503103840040c40610b000c1c0032030051000029000c40903440505c20090b4140d0068640e40403442d00085000c01817501000d00380b80760740300c4d50809032900d1240c8c1c00c40b0201c030204001003035002c20a00401c44071200300c00c000c5031180300e0b6544a403c00e0702c1e60302c03049228440c504400142d019050001418500e84c1081d6144464810840d030000004184006151202040c1d00020150030a00c2c4140c1240b0807010389a46070f050000380081c40920540040007500c5650319080081e5664803400c1040d1081541e1204541d00410020301030380c1442d521100350015200219030410004039422424808841000c0d00c440740006680e600f94242000140010480580611504007025102d95120140a0041b9042041c00682 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 78167555 1250 78166305 78166321
    0x4020a02011517010b060304080706051302120f101404060e03090a0906050f0402190309031803050127120e03100c0509010207090b060a0507140102070506040c0e0103030c0b 76
    0x4402d10360b04a40c1040300c090f00e40e88901c840c10760001d5030180543c2801d444600c0750401b501500d008560051a00b400c120341c65540760058070000b09482c0010240381c3c286805655100441d00002003860082c154569102e0815420890500c94400d8100d003050080700d00c225081c0d88883e88103400c600002042040c80b2812800c0d8400d0950b0a580001d0441c8081168840c07070788200100ca400300d8040c60700d00c0c08001440309a024240c1d01e90064140a8003010b0601e003e41c0140c0342d001d10916001000304088985810300c03888640064030160340d81c3d0246010072080303100c64055022044074190745022140c2d2580040c44600302070004000074100101e1842d101008044c2c02000011018440000303035220040180c0c1044500f540184160200040e0385c038480d200f4998a190003521551520103032540c203890350740c08041b044590490a02030f0300302000d4203101420b540e070300c07a4020b13014508107230400c0c14072400d03d80c12402c0145420401000020340050b80804031070360000043c0015595180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 78168805 1250 78167555 78167561
    0x9072306040b070b01080105070801061403090c040e01020c2b0f031e0b01021507080606090d020a0b0304031106010503030d0507051b03030a0c090e04030c050a0f0602040f0905130204020a0201 84
    0x3100100903240411028200648603d510b41a41c1b8080002c00190751241002c6440c45028172138113000c210faa44000844a5080b8004c0d680401c41d070080791808810312010404942084621b00210795000c13a80d214896000c1c82003001d058001004070014403d11f1030311241401c81e603401c0f10240109400c403114800d009070003140040f2107405070700c0714600417941030801410a6034090b90050261100a9189080c0307070012078001c1945c4d54a0007502e68a803814000250722421030580d02403801e4008100503a03540c1520005009801102c68603401c113031401170501c0c4000b02c0300b2a01508803000501c02c2e5107001041d111080000580421f4a03202c01c24283c0c1c0c503204020010700ca034205c01120b201c03034040002c020340c0512818801080342b01e02075441216105424040c0c001264055008940401d00c14001c110782c46002e60252000e08241d0303542d858803180900402c684058000c1800c1118444664000c002003100b49400d002e41d08d03003021080a001040d4030000e03c030319070202d00b5aa109200358 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 78170055 1250 78168805 78168809
    0x150f03040221010b040606020303040c030201031a030a140705100509041a060703020a0201020607020a110d030216060309060b04020c0c1915020a0c0f08030406030f020f04060c03080907230604 84
    0x200ea52910b1982d41c03400076000e000400c9900340502c1c1050b400164452002084a2150390405100b140d40b030705590045010b000c07030150703014010070305401a4695543c244218107070035105803075054044d1803018026041c0b814540c0014407030100d44171141401030300441201e640003c00c5400243d20390450000748003402c040110580c004a002c50400308041e000075500d034141e4001d13001c96089690380e41040f81e8603060444018220f18854103a48203904081c10011120362090056941410740c50041440001140c1d1040c40041d8a40f033f814003c1c0030061180d205000300a860039441d001d50240c07907582d140801c204403400b402c40b01c00203800d14100303400394501030107542841c51480004030900a503a031803030f10420b8498070700c10748001900310418480030040780c608d407010b5820f103850100c040e0000d044140341841d2640d0200404101c001c4118000c1019200320340326401ca481450a004090769401132544665a10102040c810848100c1c10302402d2115000d4504007590a00085401030140d0f03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 78171305 1250 78170055 78170089
    0x105030a0c1418040b060414040b06121e01050303040303080f18010507090608090c03070513060e070906031d060a020702010302070503040f170c010507030c030309020d150b150f030402 81
    0x1150300070b035490040307a070f004400700c1c215001e214180c0c9020400c0f04c80d01c51485070b11801d0324041419000360405030007034814034a004003801e09207030880c40301c0d040d5960100d5200b2a000c0314864007114090042d8203d030302500b070540007941001d045076405840c04101501180c12041e900c000100003100000c82404080c00324002803019062060b0003500c1042c55000c0c00d4041303020b280002d400306800040c000266603000b4006c080151400062009524078100d0600507561142c802007105886020a40d028107102d175030300640c8924041008080782c1614aa4a0308201c4d5426030380402000015516007102451301c0041e6a80c01d0381c401603000f441244001030082c00041400280030809444280c02c9a10704402001944e440070380c49921440700da0615408030b0f1050000001091040d4044980148241000070b540c61250f00021094441c040003110040b04001e241d001100b00303400f620354440030644601c0321880b4140341c0ac046600842440142c070380f42c08400103065648234036a01c140c92640d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 78172555 1250 78171305 78171307
    0xb18060402090c070c03060b0a05190b0f0706020310051005070c05090703020403051c02010c050304050601030807060608030d05070905040c02030301031b0b0f0903070e0114040c0311360105030a0c14 87
    0x502d2030b10074040c090f41c075231092156002c5400001c20741400301c001c02601d2507441c001400141800b0201007141c00a112010440e0f1082c008000041c4d15440114001ea10700110340c07140601d00400c214200201050003001c00c04240440310004400e00b0340f5905a520446a1100c3c80e42d8014003140240929840642103118000d003050b103d200440a1440020990303009203d00703500c04030103813150311081d01c0040ca1035029200400110324010301070507a96104071004619640e46081c92842c503009000e00046c0c0c180d07280248520303181c1280900c0d0051800303543c00d000b03010381c442c8040d44a010501c00980018040c924410300d401e01c3c1083c6c034019001d0ba86029403503481d100b0070741520384c10a00b42103000780306118003c1078442d04d03c03120324121030085009070040040ca100b404082c020503440801803544418900401102d03c401500b501702c4c8112000b082441d2000040300012007a8042012007a64a501c0205d185d900c002101d5005966000200705091903040c2110900c414500708204498 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 78173805 1250 78172555 78172559
    0xd050a0e031303110301051603050405070b030109020a0806030706020a02010e0316030807290a0207050106030210050c10060317071412070b250e030106180203040b18060402090c070c 80
    0x6882c007201c2e0a607402604001e404200c4a41070500300c690a40c1e0804040c40c0131905e03101024865003185030310610400548820680d2208114900e410070382040b582560045401e000660340490f019910107002c074005d00240c1e10f003410181d01c480301c0e504081c0c1040408002c110701c0b503d04205803c1c02c05805040828180d0b43c90030801d0482c2c10182040b125410140d0703012024100d21882c00d501040f0354640d04080d40c54211209000350b106440845280d52211300c0003026a96070b04006003800c4468540c181e8810b005113107142440d00141130b5881103450140d060002c0740e401050000e04000b9030b2849940c2da0340a0a00102440c905408103a035131040d540310803103c1000c00c01411215104048820540e200ca665030b030f8005594841e0485031040c2d0a0f03030602e84034810022081814000340002900607122a403c2007003608403c42828826000030610080000d0080c14950040500000e00f503c500d040b54400d45440c000313880684118502c40110b4001c2c55401d080f076034071581c07101d001913070b481e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 78175055 1250 78173805 78173827
    0x60e01030b0f0a051b0307020f250801050103080702010509060d020a031422032f03090109081902100504050402220807050105030c0307020c3309060d050a0e03 70
    0x410101c9084090001c0680401c00d0703482c0c44e000d40e0740544a1404003e61200240c2003042041e00010312100442c0f0900700003214606050218090700c0c8020a81c4c010788141d040e0800c03001442641c820000c0da0314040c01040030501090640d012643d0910700b40b5660706040f4002030b080c0c0520341164041c1c510010302d58944a130940e00481c6c40ca0004c4c000c3c16001d0351401e500e038403426281129540e5844d4038010301c0d000648220031034681700a000401c00c4003405541d143c0042e54500c50680d5106902c000390548042d1b0b0805407074001002c5410040004414510000c8003100003040024000e0700e08692000005000d0429100600805030045498600f0b00240d2480b101c41c00b10000200b0200038070100380e043d4040303080016501c040c0c5030940f45844002d114207031a40018a601e085024000d80815140e856240030030308000b200c0e03a11042d105040d104500c4102e401c0840b00c0c1401c01c01c10070600141c88000c292940c030001004000713620394501c1840d9020740300c4c1c856800c00d10f0000080f948445 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 78176305 1250 78175055 78175073
    0x40509030f0316030b040c120507030e0706091e05010207060302090a030209040305070c0603020406140c190507081b010e010522180501080105040506010521011401080c0a0e01060c06060e0103 84
    0x5040f195038180440c1d0300c48000d20040f1005540310b0b50020359400c0091100b4001504010780020f00c62030001040082410070508081040d049800000e140c140104007040c5440d0b840003e10304c001480c10030043c503180010350345181c01e00c502d009064011510003002e41d00c0c0c0f60b10500a5401800410b40c601e41490010450750000c14201d0b00c0040038113020031300ca4403074800d460682d81261521080303280c601e007880c48075410281800030a84185040745006050250340549003602c00c40080400500340740f0381a0030031500b0700181681454007074410744244e80c4401200124102030030900d0f50fa04d00c40115044000d81d2a9442d902d03d2014100050000d00c400000e240d181006007007017004d80d8071010002d090350010340d00504540c0c4060010f01152400c2c1080b0400441c501074a602c030000c00c54041da003995450720a48001802e40700040000040500040c500b50504071001ca10980c1080011001c190041c0215410020400c10000400590344e00000c041c080d64003020806603500c0c80c10410b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 78177555 1250 78176305 78176341
    0x5121603021009051f020706060603051006020a0213050a020903070605041406070b0f06120105070909061401120203060a03060204080c010e0117040f02061c1a03070311040509030f03 80
    0x18881c010104480c003078288070341c0d00084d51000140c408505102c209080c1034950035403c1500e55820010341000a4092144c1c90040115480100380d070f240c084220300441003141e001c0340554002034240001079480507018a28401c8804c000501d030344695810400a01520b610b1030741500c200500400c610b500000540100e40d402d81610100c4c0f0b00030002d0007014001c411004240b5951800487c2d40081103e0760107500c804042c08241304102c0443c841800e41d2001da4007100411a101d80c284031000c16402010050310344180c90300700c042c520310002001140161101084070b58040301080c141d58070158560000c5170002010f540711a1602d0702d094945071a1840c0e14082100301196030095402004032030746409050300030101d203550355125211001c9460034105e0340000e04000c4000e583d24401c0c0c44000201980d0320003c1c106845091403e60320b1504a1000d219901c0a181080010b80c8254160010340b4155004111500d170350060b20304c0d500400c409107c0140b404401c0199401e0520701c00c0305 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 78178805 1250 78177555 78177557
    0x50405061902040e06040f1503080903120f070605060a0f0308040e0106030c02030409020c0a0602120907080309060a0c0809040c0807030c0c0c03020d020a03141506030c1c05121603 79
    0x9400844640d00881c4034502c9002d085200200001c1c00514060380700180a0949020101e642e81c0390300f450389600700e1141c0048070102b4010034100c056080821000d21b1082c40004024540684660810300d24007401d4001045589c440c40015615195290f40c3c0303008080b00a19050031645928103114140c105000fa001590038010002403018031a004110505c852a00030310710305801d08421901950041ca03405105110300c0c030351000010f0491008182c000e000ca40403205030f04000209600b0042194802c18480e8402d204045455a40e103040b511030a8490a255111400318900050719004908240303034018645180c02d0b800941042060348a0010f03950b0030000001c11080607241603004060280c0918244001400103003404254209c805000824403440d4035501d545407080303070204c07910000060b04400c0180801803000e80d07900360004421006000140c80e4400841c2503104000c3c0d41030b01d0310f9046004081402028804030092505404600e40d9440010240813818050007804030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 78180055 1250 78178805 78178831
    0x506071b080a0b10031a0a060b040b1902010b011202090109080102070b040507060c0302030a030f09120513060809060a020906191e08040c0b1b0318180106170c0d05040506 75
    0x180c0c801c100c1c1140e100c1580e5100d41d03020158100c40c46c0031605508020140021341c0c0e039440b0085064000d150281c401400442106551515810502e030400c5001d001c5140c15607051440c1801246e800c494084072858040000585850332580101c0d40d0403616444105254400107040050200740ac60b49880740b4000c400726070a1035a07a4a04607035140c806d0401a0040c2c0040c4144006140300c2c0d0090013801598003004205880c0e9134803502070b04151b00d04502e01082c40018014508a030b00c411f000010942d07030400a40c00d00d80010460744845c0018405c07203002d17900140e04501603503083c0548981000020790651480030919001c0d02030700380c11048205003284080075518081c8070318011445694805d00303881e2503030b26016200c40b450704944e0f80c401107500303220280100c0c2601080a084039201d01e2440710003500c5524144049d440c240036009810b0b01a02c6d0061000940203403c0003400c44a40c05101c100d90b81d101c151a1132406903544a014040c02d0000780414070500280440c09100780142c03203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 78181305 1250 78180055 78180061
    0x4022205090106020a030518060d05011403010e03120903220504060e04031b030207090e0705040c0207030302070303080a0b040212180d0c02120f1c030e060f010506071b080a0b 77
    0x12030444002d11540f80140c0c0301c03051860019100d0b80280c4000c91b404201e001c0d00c40c07000f00c00a40c46801c02d400b00c0c7d442c1582c84004100080c0c2e00c030b980c4074010350103400030440041c4201c00252207208030f240b5640312050080100381c14030001c000310313410b80c180d1090070032007800c491175001340c0e4040501c9181c0c07046052001c0400c5050001d05a14019903040d200d103c000d04c8000540030800b080c8075002e42c1540500e010010702e02000c3d010f0321505881d504064101d250904c000c01c01103400e5100b81204640c044e003c2840080e40004070902900d0b01418143c10759074440e101031015001c3c01440541142c00824a03009090204440d14003900c054640100c0103060100b03502d5480405465900c00904000401005801c1405040f9034890348581610050b594072045030b0701d0a20043e055140707400c0c150600c540c5556141c03140d03070485400503001d01590704205074502100f481c18020103101b540005550010004008000d0390103050b07541c40701c145681d4410b4004c0e01c9000301501524a11181000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 78182555 1250 78181305 78181309
    0x602031903050709050904030c06020a020109060e070503060f0907032f0d02130207020d0f0b0708070c0809060901020c0406260c0306010306111b03040312020303100317070204022205 80
    0x501e4400e801c69034941c01118a8170b410001020000380041e070601c642c3c00b003140c0100c3d005000500d0b001103141c0005c0340c0ca41180c030f0450304445036000b620b8041e401010301032041e1354012030b5182d08100030034521285a180c1c82102414209076600042001c210b4a00b54100302030202954595400c94130b1090049403096000d001401489000096011036590342641078a0a59800741584600142252801c94102da03140041c254550400340e83c03443e00d000401c07101c00e903c400100d60248081c80e002c1d6981401e039440d12024082c0b1441c09201d81e00c041501d0040740d10030010401c000320b00a00038080981d50301d101e0004103d1443c0c205841d031100790501110800c000601080e458000340040c01d660707181d0f48a103001000c20050a850340c5d10100b0880c500490090202041405220007440c0d0301d510314603080ea1803158000d04a420754100b4400c110b108014070700c10742d044a41100d241064070780c16005480c07651164000c000d41c450310100da0b502c4030603141d00c0b0345d02d040310425111124140d00c0f101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 78183805 1250 78182555 78182561
    0x305010303171b03070207030b0a0212061e0f18240103060e0606160f0606060f080105030a021009090609050a0f050603031b10060311010315080a020111160602031903 73
    0x6030494441180070300f400001a0380034011580319070b50384152000d86440360340b2000001001d07200c071a411a000701c1c2c2c03a07074080426080d0070340040c02141c0200701400194051041c01d80c8000c41c2c548540c42d60300d0610300d65110300300480c0b450000710050f04124981440c1640c00d10300c02e03014151030706d016000c0008095000b885608140d810b80b001940244d03035510100301c001d91040e070219003100c0002201d0000aa00c089000e8440303881aa00459400d041400c0203110288441c102410442890010030194038046601c0c0515072301900c0704506126030360001d84950082d54008048686800d100051416403580007034007540760140c09010306520507804500340c4006991065140d00104007501c0105001101b005003519440140d0b800c400c6031040b0007003110207075441903c2c1c1c140182c100c6c0240d036070301d84203441ca101c1101400c1c000c0307281001c05482d51380040007402418403241c00d2591000c054100b084015030540408000c2069843d40002901c0c3c0d041111140c426102c000c0103044207d010740 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 78185055 1250 78183805 78183811
    0x90a1205150405010e070806191a03010608032d0304110d080408071404020a0f081003020306010308090f041b030b0a05091510050c0a020d0206070506041b050d21140a030501030317 79
    0x2900e07e4003c06080c5180000ae1203510425030790700d07000800300042c03030300c0a0280b6002044910007550301d4044003800c03030360a008002c410b5800700040003519072a48400748140c82d001a00015403000c0e4141000100d400b4110131400030b001070354041000540d144c2d0004030351040d10581010015040042810700c8244d004e42c00821000c10701c10b00c3c0307012805100d284140c0d4041c1c0d8111200c10110341d01d4011908101c0d01b030300240c071800300c009001000c40c100022041c4412000b50f908000d84030011030010400502c0b025024200b544a042842d51a40c2e1514050701a1000801b01e46076030509116600c0c43c056000d0043d0b024041d05503c0004141c0900140c4100310980c2000c0c0c01400c006d039003000825820740300304a034444024826800071506c02c200291251b8406c6c82004004102c072a500840b07004580d2106124510340c0d513503600028034a0400240c0c064030349651030300114018001b40c40c28090b041e1815146203000c03031a501d10365455040030341200d020f07482d4400c0310704100c189040b01d44011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 78186305 1250 78185055 78185071
    0x30309030412020118030602030a06080307020312090a03050f1b01020a03090b1b011a0f15070f02040e0307050a020a090e0307151104090603120302090a1205150405010e070806 77
    0x1d2000704901803840140c00030051051411854240311340064802e681160740090301c4065000c000c001203002d0600c1000042e156600055081030b9255000aa0743c044a90b18020302c4840420240205c2e210740400c18055540725064900640140c6181030f6100780c48407031815070448024044685500104040200380d4150395411452824000903d540383c0c409036000c42d4504991814807601c80c0c2c20b00c203034207000307140880300701c640640c560401400303004105400c0e124024641c12282201000400c6030f040c2075020035946032481d010300008008090740f0f41c600495001c0007d0417000c010000ca45124641d100300e031950006a11085030302e007241c000c59528903040d8400c010f9003021420030703002544812422640403514130030064042c40544c200e50720040c0c1281d191031090040280101c0c60001070100d9240071400c20950200140140401c0c2c400c81c003420740c0f81da80c48010b00906000141c0300c00388109210680e1b0a00c1d1810500030700722051407900034001c0e034202003110b201c0400d03d030b4041c11035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 78187555 1250 78186305 78186307
    0xf0c04050a06080c07080703081005041116020a0312120e0604030e1201150605040302030f0102340b0c090321030a0c0915020a05060a020702060d02160b0405031b03030903 75
    0x2e0090644400c000603100124018050008100140d8281d0003042918401d40d298030490800800d4450302d000345400c00c9200e64101038821008040b500d05907910301d480f105421344000064008541c05218540000c0c1418400403624040e41d608106203000003404070302d00300308500c40302ca81c1703a4440d40155801800603002c025500c0312450403144c1000b070796880c40700008004c01055030300342004450f42e21001c00700c0d002181c10000d61400b4044d10510010260003545070640e921070b09892034110301b5080603540703030f40700e500c0f616082c0902e00c007099a54421000754460601c2c4000394101e8000402d03652291041e00c1c40100800b42c0126916180ca0040c95154115250040c81c0740c040c3c1180200942046030101001800305804880d0701c44d2810246c01602c2c003041c3c982400340c28960000c2203101a203004012040060726041c00311901d110f81d01200503159030b01072701d0110350100d4907030340076015542e100140024007902100410b11a80c07002882e0805074060285552a800202e40314210f03500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 78188805 1250 78187555 78187559
    0xc0307020d1b0f060f0507020601060f02030c07060f050403050d03020d0b1207060e150409050f06010815090c0c0d030c030b03160b09030f0d020c01020d110a23010f050f0c04050a 78
    0x15085000b42d10349407081001003417059940080710101d41e407c03a0382000580c0010010025583c005a0003429407515201440c0b910b0850414680e5403180fa10403141040300b038920007501c252051054030065584402551103102807e00d00401035042040b45144082c5801a183c61030b1900c00040c00071200b460020300070f46803410005a800d010030219054220f0041c150a00e581c04d9900001c0014055101001800c0c2c10004200d110942000301050306101c1c1e02000d203d82000b02c0c400310900c5030011a05025640d039010440d00d242e00800781100640e100d0510306152450b050b8000d0799004180303aa04100305140070f01055031310284085004010038980c001804010000802060030b8080541203400000c4a039030600e00d80f1496041c20001608100e0481a5a6074140440800e07030000e40b401882c5440c0200e280c3da15410719a0005200071101c1d0b050384038610030703041850502803140303000b0080792588048080243c08200d0313240f40130b0703030440f4000b8002c10350150954050b0381d005050981c1c018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 78190055 1250 78188805 78188813
    0x1a010309031b05030d0c021e0c061b0a06060e040b070207060e040b0607020d03120e120d050703141f0801021905030408130306020712080906060409080c060c0307020d1b 74
    0x2d00840070039141030104000509240406021b00c0800d006160700600e40c00203105041d02e04940360031041a10764104000b0140d2a684050071f0304c000c0303041c10015840100c04040c400d8500b00000000400503424030100050030020107065030b00c034901849102c0e983c0d80d200a0101d0725826280a0b48022401d98040303c0b8642c200342d4401c401c1203001800c2c0c0d40c0380c40c0c2c1d01d07000980c0b03410880904400003400e501d00c1640c45c000078003800c40f000c42d4000c0108504c0c07207400140341c068000c1502840280b542c45000503c6284290002441d14454504d8501e803401c0660444001c2d0045c80203418498003454000140000144215004600006d202a610521290782103d0303960014100751400f100602a0104507140b084094000b0762180314010f94480c7c0038a041150440040d401206201c040c0b420084030070808104503a1081d011034000880407a2403600c903015002d000314091040c8a65802c10003e43c0e8480c0046000e004613808944480002ea501122003818803924903090a000809440c006 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 78191305 1250 78190055 78190097
    0x2071202010201110d150b12041113110a02010c020f0a03031e18020405060616150f05040b0601020f2109010c080a020105011806030519021801091a01030903 69
    0x800d205100224400301080034101c0580c01520b8509a40b6580f0004103c45c3e002c031860031001040302550442c10a4158035600d001c603007000700003034880c040c0b042029901b540d0744503109004401e40e000c00c01035074401c03001101c0759800060180d000344d880d0074104644103000144003115010008024a546010340d038003200a0b00a04500c04d069507810000070010450901901d01c4034400c040c0c095114181900400080d0317030001e048180540c104208004030581c40f0052060203030b8010f5400721402c6600b140138401840000410040b040c5048240300420040300c0850f80100800d900700c8815a01c04c1500070b440e01214404e0100d142558500710105e0315007107003d401e0189050610b00429005071702d410705aa8010100c05005075562001400780a403090650030a10b0651300d02040b04508650f01c40341c0e40d4540c940580281d0643c82041070455035804840410f0302c002e2234440c84103581d41c4404101030922501c040306a001c090380c6041d0607500c6440343c40d035210b8044d83c2c0c00c00b083c02d00ea0090549 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 78192555 1250 78191305 78191339
    0x1602091b180a05091f090615180503031b010e011b08040203120403030f180b0f0c010b0d0c03060c0f08040b10050301050705090901050411040b0a05041a030103030215070207 76
    0x82d8440350000d626650710309080d203c0c44850341d008554404000d00d180b40d400c0160810000945492414001d00d03000e074a090402015605000c400e0010f51101a403451880d503106540c10f220014110200b1180b0041420100041000030300c0345421121080f402da52400c10040010b00c0c25030b10703030591144190302e030a4000d80040e06a034032011078403040b404250b008e50800c7e0042111080d03030003445030380b046107004200c90300444142c3c164201030050072244260a00c04200710004a102440180d003903011020142e00140b10307540b240d200345031400c6d0481e0b00e840142c54031403821000c3d0107914025100750440c00e1042c0c0d5401c040307507119958091025009001c5c8100000451004502c54400740706070740c003620141d2511900d81c400d0302c00f040400c0700305030001400350b07043c0710500d46080c9450040c2d0b01500d103009902c1e52952800e43d4100c0c0c150266a00510084020240c0640c0c4a10207100440c140c034029400c3e142006e081111244465000b41c48000c0164000e0604100641c140c00c0c880f12 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 78193805 1250 78192555 78192559
    0x306060f0705030708070b0709031511090a0f1d04030507020d2102250513050c0715020a03110315090702011103010f0815010308032206021602091b18 66
    0x30a00d2115242c00b0b28580110070100c070140c0300000c020040c0a407100480381c0c0301e521850100e6207103040d981e4404075104541a841841030b100e200354014400118240d1300c0100c0c01034130580384140e0748c43e1149002100c40c8660004841d0078060224964101d4680510568258489519184041c1e0034000c445568190a4411180885120020000c07070380d112041802c2d0360b4018400707601e41c02445404c00740e10303800350ba0f8034000040c1d0402c0070381c1b50100c0c0c0c1c440c078201d202d40000c0c6581d1a03020304112441804802089103100c00708688460702983c3c0540320690060343d0400190414100880051209440170707103c0c0d05034103021040615220405c140d201c5201e10000c11080001d0801175941d8000307170401c515183d0313030071001d01a9440801c01c200e01505a00c00c00801d551450b02c454001d4440070348140ca450810b621962640a010f55100c0c031400e5002ca0210f40e0303201411444c0b21030700350000c000c900c5240d02c1804141d42c0041412101261207840c20400d01d000c83ca00307940c180b0f104103030a0140d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 78195055 1250 78193805 78193807
    0x304061b08040e0703090c05010905030a0f020d0f1401051302010e0f01030b0a0e040b0702150106030b180103061407090501050a1206030b01080a1101020d1d1206010605130801110306060f 82
    0x410802d0000503024015513143d103000c1110001031411000c00c1c40607420060400601160400c000d540c0040c40c0c070b0000d500319910280e01c0d10940040307440d8101400003d04601301a61401e020490303400030a40c211040d120007040141c031064200c0e030894035004c2c0084d0001e001664031006624180100624104050400099103200030010400c041ca542e4001b100c9c141404081006001400b04080d03880003491025004c041702c8108885046030042c00394908059070350f020b0300c2d5141c9911002c0c1e0310400c2003c003c07210302d603520b20748100600102414451640c01703403408110307654010a0040140c0e0016140c0a0410b1030610044804002d007101d000c1419803200701c0000800c8128240341d011341031440c05442544024106210a091002083d50440d032190001c01d86042d8042c043d0900550f00b0b06511440c0da02580000e2040803913409a031290740280000003908a030820000d2460094911070111708568413510207080b104031500200f0000820000601340f450008014460454118546 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 78196305 1250 78195055 78195059
    0x1a030703290f04060302060319020904020f030106020c01020601030c062a05030c0d0e06030105010309050a02131b11070603090309080708061b13150207080a08120106020304061b0804 80
    0x28006a401c5040000a03800c015401c100315814000c00c4074503950070541d0b061001c145550301117181d80c80018000380039100311410b11030403804280c040b90304c1048000c03c15901c900c0d1545007000d0a40c401e00c10000544a602c2c00b24583e075001085044c100c030b4021100350742a40c40d183c1d0a0b203c049000711400c140d40032100401244080181408000a006400443d2510504040e9070300e4010707a4034030602840300703151681617942c0c2c810007243e0550720300303103404100700c6501e1401c203240130301104000754407000c80e440141404006502a8004100801c0200d1058144080645420003003003c924826000307514240b01c9603000350030019a0500c286002d690543da100e80301c0d8281a226044112aa0040c006201c0ba07250803401161840b00c0e40c507200c034603148165642441032961886800b00d1a50b1254041242034002d0042c3c0000300404002c0d40c40b824aa8603000e03000b0340c0030000391b62544440d2800812180d100005807400d8801303c7d15a8403041c603c1c0110011170580b192012141001b0803c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 78197555 1250 78196305 78196331
    0x1030f06030c170d020f07060c03120e0c0a0b090604030b04080912010f050a020c0c090711010e010f0e06060913150c030b0f0306070203120c0c030a020a060c0305011a030703 76
    0x82c0401800101e140312001c021003040702d402d0031856003000c801c45d0300c50700c6c0310112a01c0c045841401c90748282003007101c2014034030b000e40f241c125241070030b08003515204140100c503c0200d5020a981e408684440d4241c4d1162803442050261707a0341c507904000b041c442400020040e00d0b10301d4000380a40134460404a5000000d119261a10740000c00b59451301c1951303990003400c0c02240d402c42070703d400c02d50508800103c2c05035503070f11000c0820700c910701c10000f04058500964880c01e40c6651007009001070311000c84080d001e8200c0b00300301c1c50b1592400f00400200000071070200c0c011440140400352540360b03491221880d01d140ca000b666146520304041c1c400e08094414542c00484c1038078003241c040460713010003880d1b42840801131b01a800040401c9115540841198001c1c1d0120000d600c2584036a101ca000d18050b485460515110000d400d48446170000380d10110300d4444d10f01070284450030002181501d40a102d10300802401280300369051640801840e4482c0903442c000825032880b00c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 78198805 1250 78197555 78197573
    0xe0606030325020a0504020f12060619051c020c0a03090b0c0a02090a0b0904030905011806140d020d0e070e0a020f041715070806030d02030f0306040b061306030506131a01030f0603 79
    0x6c01d503040048002427500b000414420410ba000c80c049481d90b04081030042d20302e050000d081c10500400c00006100003c1e48c5040e040340301c0d800c00c0a04110749692281c843c5550700d14004005401051000c030001460052490440d6107110711100646503101c480d50a02c0915503010748152000c54036210403100d1501c440e0001031266000e56500d00460f403030321001400e80c0c0d0b6802a11018400d21500c00c3c011503030443c900202040042c10b1040c0c0d6150310b0241c4100030300640c03164054060901100300382c5ca81c0c0000b120402e0f40d25610002d05542ca032031000340c08034071a1070340901d460003044c0800c001070745811483d41405658601540c01d100150607110080620445481020501100901071241401c00101158400900080d4540031030102c035014540401004144160740751300203900760341c481c0d0080e40e02c0301400e4204421240d0b15043c0280c05803030100c4000b03002c3d504c00e00c14003c040030940120300038190f095003403540d1103007071200450103010094484920f107900d5840000018070750036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 78200055 1250 78198805 78198817
    0x907030b0408071118071803020a090606030b0a080a11010903050123060f090f0a060b030c0705160e040209090f070602100507080105100c03140d0e0606030325020a050402 75
    0x1c00815640d00241c5080c11841c88440f035524001d0041a214031740d41c0341804240c82d08001e442c00c140503d040d021140054030001ca4000070740240f1114000101c8000710740050054642e242c6060240c55035070420710104039081d218035015588000c64220201c1e2400041070002c45041c51f00000040d201d40b1402e00391660b1140c060b82030b802c81291001c000c00210046038015108440c180c01000d1844000b51034500c0140031000d1152544000c14003c01c42913020b00000c1c1821440662a03140074420b032203054100410555450080d000100690440341e407101060311010300400e00c07151507d801303200daaa40014890341443c03194508031560b84108215800080c1019401041d0080b5491a40019100040c000b1024444080d005100654402150b50003104051a04525040701030804640c44034200e09282110b0800181e80d030a4207890707070400c052502c1c030002180d81e00e40369181419602d101e15240d00346900c8070b02c0031411020024612540030704d8002400311542c19183c10000d000c91b4050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 78201305 1250 78200055 78200063
    0x1140d021804020406170a0605130f120e041407050903010902040513060b1f0507050319090608070216060c02030c100309021305060d0803130c0806011d0c0d050907030b04 75
    0xc41008114a01401913002600c0c6c8aa95499500d541e00300c2c090b900c400700c2c07000800703a945543c00114140b00c1d03501403420ba01d41180c0c1c01801440c107030909800441c0c09030f01c8440001c0150300c0c0068181410b0250f02e54410503100352480b0703a9110f4208070384c2508001c511681c15500c90f0341c00c01c0540c0e83da000e00d84c00341002196050f4840454540f0808460700d0011250060809004050b29010414102044060541000c039038811051400c01c0c2148201107141c071154010741100c00d62540d10800100503901640c8403502140c4034540d003aa41e500203100e0f03107400c11611200030302c1b0041c070030182d0b10002c40c40030342140c120514031000995a6080b88490000113075a40c61000103600d0220000341d158041c2000030401c500f00740010403624052150090540d14000000c180390142424100303080075004019409400e4813488442c4e1100800e1080c4070301e42c42e92a40b101014101d03c2c100501494060503002c2c50322040000c41d00c0545001000401603025002d0300201294842c00e409102d5445 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 78202555 1250 78201305 78201349
    0x1d0315070207060905030109050721080d0b091510050c030f0f0c01060501050c060601140706090f020f0a0e041401020405120d2c12030d090c03140a0b01140d02 70
    0xb800f0006090400541c0a04d100740e041c12540400318202148580544c0d049810600e000800b50f00ba401034801d050400401100000503840c4c101d90484c1d11015041340d00300e49541c81c0d500c51000f09040240094102a400031000c5410503560b4000c000510300400288281c0e401c00901001c11449504194595560351400140480c00c02000703100b00c101611003401c019050010140314140d50f4000209494140111001c901801c124140180c400340d0b81d0080062200518134030304413250075250001240070300c01c07000504203e483d0280f00001a108000c8603241a41d03501e07114104460200540c161003950b00300008078041d10380b403150211180b0312800910b0300000300c50340242210003c0c1c840421041008000c00d4040791501c000c03c87c0da40d0126800c160384144030f01903a003184201410245141d2920202e1410040030400c25421203000e050081d400340d2642070825103854043c100100842c2c0d06400601103c1802512500c0342d10002e045a20600d103140e006c26108204840c840d05ca40c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 78203805 1250 78202555 78202559
    0x20703020109020a080303090d030203270c0103050a0203010b0a0318140d1206050a03060e33060d03080f13050607031d0a020a1a07021e01020f0d1d0315070207 70
    0x1c1c0f80912000410030721740118076600c0e159581e1505d410006411500701500040030a501c44540c000800c03000a21381c0a003d1080034050700300e50f95560a541240c0400d00b00030020b00040018802d0b02d048868042e000c0d85401b02c00c031021001414180321030002c0c0740d9848414030224a000780d10b00181d512450003410200311824010f820b21311303e6400d905015090002c18003c42d203c4012420469603c80000f14821041c1903040b070422a05520ba880301c040c0d0400e21402c160a051120300002c882000301202c3c6032260b506000a44080c0240034020440d040d010036003a6514002c22039004ca00f41d10358500041003540c40f1410170100b6208040025140e0011441c080340c5450750034116403000006105900700c44c0c1c00710f80440c0c1a4407034071441c80155042c1c03203800505034003102c410310b81c000c02082d0324131408800c0c070b0507442102c00c907603005128a4849445215000031800b800001e141c85600019052100c100344886541c250f00ea0103028244807070000e002400396103400f0b880d03a03401502c01c040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 78205055 1250 78203805 78203809
    0x105130f060c051203011202090a02120a050105011805060306010e06040b03010803070b070c1a09160305010204080c0d0c050907030905030c01050109180209150103090203030f0a0813020303191202070302010902 92
    0xc3d0050444c0c181e4120030401004108082c0303c031110803580c1559040f0007540d8010f0044028021400101c600045e00010088208816030045040c1c8000741c9030204044a181c1304d403c540d250038003905400c4a41000410140d6000382050507400c070004198625103900d911420419401c20303400380c101603001041031420000a100320340c2d48007445103072020000c2d080d9201e181c1c1481d80642592900c006500100f03028000500c00c03903840d06e1204450000740c5607a40b8200b8001d40c4540b103441a6030040b0412151700c0d15102800c2c01a4030b41042110900710b04140c20080d0000f00541440107041d039858208001440520290020748a81ca000041641c9410f4042003036505103409910381022211000e401640c2d21b10650341c000c41084009201d441c04040160700030641014060361602c0003013003031045e9200100091019884607981c040690302c80782c3c1e00240c3c1c0e00c90000001e5041c0c00a0108180c030810b00810300390325031842d240c00481e90004001843c08c076405000140e0050351509a481700f98 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 78206305 1250 78205055 78205063
    0x603151403030313050705030708161403030307030b27040c21060209031504080c0c01050403020a050409020d1509050609030313021216090501060323060105130f060c05 74
    0x406100640309160551580001e03103900c001400340302c071560040015810702a041040001400d0050212844141c40300c20490382c9110038aa00b86c030305001d500b8080784090105c0445126203000dd13000354110b454640003039029280c105011038100003003400d0300300003250306800003800322490840000765040908001c0780600981d08848011680d0204c4003c80c0e09510004180c8244c00250050f00d48286c00002402c012034201c4010191000c0c000f80700a000c400001080902042011213180d81e00e00e100659080c015880007039804904100100440c4c00c040d00491000c2d44000c1200400501d10760310009078102a40c0070700542ca80d20f21b00700041041c2001110f40007a00b00700258118134150207400920706949600074020f4514440400d840d01c0104400c40b0701525850800e4051074540388c0010080c002403181c500000e0400903c6000d0394a4618201500c14425007215107641c0e89000540311944400038148412031a142c001440d000480d0088000d00b516584000d8400c1550818502d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 78207555 1250 78206305 78206309
    0x3081b010f0b010f0903110402090d0b070e0307060e09010e07111b10020303130f030212070f0303180f080f220801140f0402040c110a0507150c080d05040c080304060315 74
    0x1030103040c085c1403010902c440a401050441240c016a4034500107001c6100a01c04450050254402c5400d0108107a080a841180d403801901110081d6a40e03501c1241c3c01c0700040151034102c1d10f901c005102e000440c0b080164000d01e9400c21601c03403417030410300d9071520380b0715030f21405501c5800424900c58600301c86107802c8802184021030660030103600b80410004101c0006025641610444081500a001044017001c84100b029215031480c241403100341d450340e4040700080d1901ca2684c00a014501a060303031150400c00325841031845684d003210721351102d80110315180b0240000e07480350f11a14141217403040000220081c0a2070305e012903095824100340d4050a160700c404009400b039000341110f6100c1d404460104154000500c182c52520082c01041400d0045454480c1070100c0050410200d402c1c00b903401d1207819884a044413962502c040003007030b0740c0082041d40c2c0044001d802454119004c1c07507140322516a200c0e0542d107103900603403018000c26210b420692180900c0e24800d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 78208805 1250 78207555 78207557
    0x903021e21030f0a020712031d0907080f0603280b060103090218070315080109050d0e030309091b0301031506050a0e0103060c03110414030f0c0102060103081b010f0b010f 75
    0x182031180c555400d520783c040d0046000281101203a590200303442003240c84010300ca0003c0300344100308a810001c060340400b240014911305d18092000c074500340416003c0c803440306130380d9031142921020000d402c1d00c2809010b040c1d0520600d400d01c0f403140c02d00844004211030409148040440502c2c10a00c40e100003044541030520302641813001d40c0305c000e0940140e007034405010869544103c000e50003811b0022400c0c08a6076111404140202c05522841403d40140c046030304185404604540609203078030b0840e015001845007045a00b0840b40c105d4022007846001c120000c26aa0144a1900268000e0341d8148655035881406000d034498100601002e44122510900f0304040b4222002c061000808140c0c0d18445495024880da0100e00c00d42801e95042d66565525882c0321401288416414402c0c000c20740c81304920b04000600722828481a006443d69030f00c2c58540f0410fa8200c640925100f2051440031300000d10284540c040c102d2400e0400149407850b400010480041503c82e58 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 78210055 1250 78208805 78208849
    0xb030105011202061c0e07121401061a0703020109050607030c090e060d0b090a02030d0f02100203010302030d080619060215070c050616030b03030f180315010e04030903021e 76
    0x1c0c0580c99240440b2441c0990310196171400f804820100f0041c00d0802d10310300c2c0c500030800c011406c0b168840c6001c940074040c0303038030300351400b6683c040718200c410302e02c074040c00318210710301681d90018910080e04099002e8000012400c2c1c4a4590345e0500f2002c4542100190f920301590b10000d40180c1e014000e440100d102c0a0f185c03034680041180400c9902010303041c580b02500084100c1000c200d0b000d02030b580035083c2d881445016901070000000400c01101500074503080802e0300626100f564122600140181100656008140e03048500540866048204a140ca0038034103840d0340140e005100391350040c6250340010051800d0b0302c5024104508024500d1520ba02107140050019000b112800c041c40e103000390068141c00400071100749507014003020602000c0981010302924183c4072909090540790400c0d4201501d88058806031030181c1040401404203001131464190f20a101e0b040c0680e02944940015400d5500d14018007420b40140b0380700307040360901c506010303420b002031074101c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 78211305 1250 78210055 78210089
    0x9050c03010e0606250302010f06050303070c03020f010306210c0501030207120807110f060109060801090f201804020117160c0c17060405010c050a0c06091112010b03010501 76
    0x140d030007050081e194130302ca07800120b030122000c0c100c44400b4105401c0820484103003222860301074081c0c0a40880343e011a8a00100080c8504010048644060340810304248181c1180d0030440e08800e40040d440c1011340d500404521406540303840646d00d0030401c001154408103103020755005100f5005241094010700c0004000b0300c044148081c45210303406e01c0301040d40c910004840501d19110106400e20031100360a9046001194203410388480342c6091002984622405007a10030b01d000051034812080e0462011078468240414080e8117130030781ea0409640361000980c0441c0c10140c40b6194900c00040c04110b68104e61000342281c5040c0c81030400d8500603440582601d001403401042c8612850020b04200300c03030540101821000e05590308091100c0500c0d40d46503070442d022034080d880c0141030f0000d603020300d054912070310280d66000044030181c0d4600000d810640f000301d48809620704024040d41c3c1c0c4005800c1d450001e0800022100d0b01442014251241a48500040e0304c8103124 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 78212555 1250 78211305 78211319
    0x40f050a0e0606070203010b13060e0c0403170c0f0d0e01020c04050603060606210a0501061103040e0106050c030d09111810060305060a03050105040302030409141003030e0109030503040f09050c0301 87
    0x19680e80020b089400f80d807140c1050010078054840ca0398010b81c0402c2e03c629440910005a0048054902080d4105255a82d45071a0940ca101d9030001030070540ba41c6074001590009000101b10007809907007910303540b618903090a40707800035040e4480040383e40760340c442c0c01f00e50781004031800c00700b0103c40074001404e00a001c60b0306d03548050000d6008900003c0d1700200c5c071002000e0510784883c40081c401c603e1800302804c2004042c20302a040000e94520f5091110724800815035090b038406130300382055646404030668595000034400ca500e40018081403401e498240b0a44140074061075020440c150030b00c040000c40801c042070b448110b0218420300042200c2890310400703440c00d508000600c0d840340c0c00021003040050f8001030030356003017070f08000800d82d001c0081d100301c502c21101030009a1001090b04014142110705601040c03298030100007080c03142c0500a001c61040c104045260385a8035150b0850b801504000104482e22108218100c01c620032560302c040760511590941d414411 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 78213805 1250 78212555 78212579
    0x20a1e0903020f04061703090a0806040503160f0b0403110f03120109050402060c0a030c03080a050702061306061d0613021c05060402040504020a030b0301050f070212180a0308040f050a 81
    0x406402804020b02043c0c168132590310040150041c100e44205d080d20520445a4035441809164022154508002044140042c0150149500c0000703142001c480c0411042c0e00c0c1c0c1d07041415035031800f10894030004a20701c00455405240240d540c0908919030015540c42c1c040440e0442400f98010000d8403210500f00e440e00741903c400000104d895143e90001900600802681c29281d0203110f407802c040680045c20700d14880d203c1e80320074500e60384545041c4210786040702e21a000d60068030001d01580d80c00007007030460724407800300001e41b503465000c031600d101c1a141c44002d80c40c07a51401d110f0b1038a08441c0005150202e080c00354684031300010b0102881c4000c800b40605541c6940100c6c4460382c480c0c040e58003421000d40110344450740c0c0b11004000c2c140c1e125515010b54641804541103e2052210912030340715600100000e043c04401c480c0c2952012008100c40c00c4a8140d12080d583d614044d50700841c0910b070744c60340ba907042c944801c1c2001e8969000750302c117054003d400c1010700b243c3c407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 78215055 1250 78213805 78213809
    0x7020d0806032d01060f050a0303050307020f0319020f060903091e04151814071215290c0c040f020702030109061a010c0803060d020a030c09020a1e09 66
    0x440c1454140d1503081c0840d1400740188004400c0f0700b000c0d10ba03000400c280909440d0b20201c1a40240040c5a94021029100c0f65071f01540b504000368080038404a0f004030000d41d005a010700c100c07000c0c003101500d000d0035a00b20100000c100c00c000b48121818039410410a17464401e1000502014100048070070340e03030b11900c14a82d029011404425103a03280e4007480c04c1803440080c0040c2300302c0e002510074130300544843c024031000e483d82e0484801081014814260a13407000da00265840e16002d0059901e9824981e0300303141d00751614401550003048500c403100501000001440f80c5211941301c4003241c10302041c5108264003440091400c1c0310009080300f0681090350002882c001200902d80030303101c0c7c0b420181d010340c00d1210200030880c7c00d6000c0182140f2441d0803e003204114001100d003041c51700805072031002c05101150192030000142001148020b10a0a00036a29a034010301c1c0c56580d880340040d02d9020802c00d90540c0c1040038590100701800d10519210302c103000140c9008894 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 78216305 1250 78215055 78215057
    0x6090e0c031e2b1d0f040b04060f03050a0b07050307090608040f05150103020301110405060301030803131203020c0105060a03051e0106120c080c01170a15051011010b0907020d 77
    0x629880c1607030080c0303c0d00b05205001d00c0103e1414000c40807a161500000c41d0600c0020085921a10010b4051360460b8020740c004002050898003101084003a02d0031803101ea03489641c0b8207000507041d4914140742c00a5208078082c10004a5606010040030340060441d81400002c00801c60565130020b042c100303031091b0341440401c07a00d0740c0c201076401840510b0010b0262086084583c41070700ce1038043c1f4102c1e48210000e020300c0d00c1e1400c41c26114041d600c141307504500240010300014001e000515032203401400089d00c928016291103403407042d203e0481000c01d50000d00400307000400e0040551040064803000013091075030740c0d010347c0d0304498280054001150f54210345010001c0d04190010b01802600c000b2801e8a0f00304021600c0d03070751280d22414859480c406d11a075028541449180075104210704590340c03840c8500b0b0107006d80c003104900c210048131300030880b9607461400d20101c1e00c0c15901c0d120840740d40100c40b400c4542d5001d525129030390400420201c1980000c0b456421030b52 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 78217555 1250 78216305 78216343
    0x315050c0a0516080307031407050c0d1103160305070b0603120d0f0605090c0408060f13140102040b0d05011d0408090103020a02120a05070c0b031302062a0106090e0c03 74
    0x2810b4070003642e0000d0300c030700a003411303400030174880c82d41d40c1900110307803000c1e4107129250f060700c500c1400c2d40c05206408070707808a0b03000501c00d003000d140114114146103082209a03442c0410070350841011a05580c401c81c04a40c002c01d03e602807141e03090085507c00e0090f4001c1c031003201d40b800151240d010700017031101c100ba290010060001000d8003d50300401001e80394111901340221843d0309078015026560944c420900001e040b9000070b030102d402603808000007601940f0603241c00d10007984551101c00700d90340070000000d90451000051030340441c884000a01541400c50155880a4003071145400040d01800d01c40469481021582e0079282402d0060355428104070990070f048040b02c00001c01c0300701283d022042c1c8e4122000b02082c612607a5000e95507074980c855404640016283d00c0390703c07081c0e50f5204005082010051071480005400d104031071000c00400c0c4100c001103400040142d448070020005220b40d03000f00b00720500c040c1c01601c07000030381e64086640c0b08040318024052440e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 78218805 1250 78217555 78217567
    0x212030618010e1e130809060408030a020303160302190e211c020a0f08130801090c0906050402040302010e0d060902030a081201060905090a0b01020f010906060315050c0a05 76
    0x510340c200407070101408800a080c540c0c2d28892111101802c94040c0d0f056446818138040c0c852a40054138840e00000303444c0d8208a00d81c1e2100741c2c20760051440660021000c200104074400c0c10000b6007095516540190f6480c544040060002c2102d229084c040c14014000800d400c4c00903000141401c00b5071074502c2c6550781c05800182d103118401e4a0b031101c02c15425140d500b8500c04202800d036429412015680b401c030740101260b840420340b074094260318545048500040c00341005010307265005840744012901c1d030b103d00342155249081250f902101c00c13002c204882c618010f2a00909040300c0860030646183c001030f0080b01c0c4404c86a1113600a2014042005603651081d010b843d000b5084404240962824081682c40180c041c45841e00c08000010241c0c416000035081e1140602001d1281d100d500ca18000703004c4209415056001c1c0b03200c4240c1440003440b0b884000703802200003150300c2c0e00e50b041c44aa07030020f603410f000d4440d06000c100a400b400d40b03400c03690700003114501680d98076 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 78220055 1250 78218805 78218809
    0x1030314070320070b040603090c050315040807020105090a0b070201031410090902030f010207030801080c040603030c020f011e02031b010b0604170c060d0c08060f0a050418060207081201140102120306 88
    0x201d42080f550b0010101b0b000c15241d60560261420610034141428200c2c0c4440406a50b01e0b4901088110803001000150010b00b00f0009044868418100300d410445c1c540d000408981103504821001c010214a030000c0d50303414014000c1006c0505407003141070408441031141d4a0141c020001102d4940c100c107003c54404008000c10340c00528004c544070f010501d00284a02c07400c0c4100c0130107101e00204071529181034420a01103d0341501c0f0541540080d500380820f84101009041c148440d4400240240d5440200031450403002e070b01175540c0f1801c4000142c1240d04441d515109a89000507441c42912601304550036075400c051219500b041240c1f455241c441c108070300a80107580421000501402070b00050012003445d101e118141e030383d01050010071034200c075642d640900003031420495410254009008101c4982c40e10140c141c098503200280d07409101f0881d00040c001512076110b0041110f12030141002c1401d641008020f000005e5849440302c500c10020140000407440039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 78221305 1250 78220055 78220063
    0x1d010c020d0b0a0504031101050106080123030708031c0605060406030e0f031305010e2d03030909100905090706090303080a0204050d1b05010507020d08030a0b031501030314070320 79
    0x1039400005074140346043c1901d8009080c080c0c40403404964960f000780c480303040601945060f10041d54032420a40e01e80040c4032110741e040c614030042c8003182c0703121030020303141480960003411045004568420030050745846400c1c1941c0503440e264903110090019030f540f80102c0d421100305140200c1d0034803491040e6800d141c4107040e071241520000030802c541076980c64102003203540036282c3e0610502450240304101c5c0c40300c01c2118022001c01c0101110320034541d0382ca001c40c68058200da04158902010845410302075841c628081c0588804003c681c12600503264003a20303203405842c00d607240150140803540240001000c2c0444600059450300780350341130380c3c0100002403003a544204030381840814071780281c1c09040102c0c4a0030011480754001c404503000c41da0302a00c100254107103600ea2100035040909181642c035101c050701c80465408000750010007645002d030105079403443c40c000d40464400c42152180b281d051081030080381c0c21040040e080020048140780c803680140a007820 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 78222555 1250 78221305 78221329
    0x203130e01050117060d0312060503011805010c05040e07050d0b06030c03090f1209090a1d060906010608040308010311150c011e06030c0b070c09110a0e011d010c02 72
    0x60044049000400004441016040300c00c2a2a1914000b00130201c10f44020021510160070041c0099000c0002e88036013880108054403860020ba00c68032440040d096401031915820010360208005060290030b00c261000180c003420150b160900c2c101e1001c5504400a051005012011840302c00e405960380107020740384e0000713166550700d06c2e2800801d03840d80c2041c0c4101100340300f0551041c81031500002d80f41d01a4450034030040c100400740c0108001030030000c0c01da41207991513a40070024000da110400110030040c8000e0310652078004840703450305c20140d2283c1c0800440380305100c00b194005c041c46054980283d01e07880704144240209500d10040c048aa030486000504a464104194001c2d05a040941141c00845070221500001e4a489000161142c0c0800c00204031820440f0300a0110710310035482d1100d15a660130b41d40741100c036501c03840450000e000880c0c1d04007541c04001c10f16048002d0a280300510002102c1603070340601d00e0030a03070503c20840984001c0d542d5007048406 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 78223805 1250 78222555 78222577
    0x20111070209180a06060e041101020105010602030405210a030207050102160501120507050705160503010b03030913050622050105010f170106080c0c010923060405060c0f0d0203040516080a0809060a0203 89
    0x130469175007e590305010fa040300d041e121104901000d240941c07040c05450b04a44150740250308045c10081040b0000c1c280f161180c10355030f19074010030201d21050006030541746c084c0e0064200f4610b004006410007125019081050401140900460b0303002840290240c0200d04001a556900381e0244d03580e10428402900503c240040d0800c1a84018244c0d825204141c000b44031000341c00d01410b0340c900440031041d5112100c4602400b10f10b0107a80600c0d8401c0c8000c022101c032519880840300c0c4450448d0b00e13000c920343c81d0001400f00c2d58100258100c90038881c5021001d103212840d0001c01088107018031010000c5000c04640022401c4003900c0c19210359030300030826001c02b4586002001030020031030800f400300850b5540c5003480420a907100c3d41c0c2000240840e6a250210009079a0000540100001c4184019803203c051031010b18440c921030002010008110100c1103100c100307070b034440145039010701c1c3d005000451000c107503045c1140035103000e511040082d406a05502403071301124 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 78225055 1250 78223805 78223811
    0xd031a031605030c03010e0606042408030301090510151404050418050601050103050c04150903080a030f0501050f030d03020f090904050a060b10080c070c0b0a020706020111070209180a06 82
    0x6401e6540d01c61160848904034100c0d11502d1002c01410300341c41580c40701405541001c0c0010700d050034160001542103209e805030b000b8103102000c5868407641c194120108541c0f0200051140105600c152038210459260000d800381c50400d01707480c40f1070a0071102c0104045030002d0f400b6204200260b03009040024800d11000c40000c43c040000d002401c01683e01d03200d14000060194080c0c0706450003880e4040402c0d140c81d04200100c940300c6000d80c400c600f00304000d50b000000c17a00780c0001d000100e10994000c02c0c0c150f10100c1c1041600e00c181c1100380f0500058060701c186517800160480382242c136040c056200c070601640e5003418000d800c409a0040307d0300d4100401c02c000400c0c10704e00d00e8482e100400840800c0350601144010035000c210208120b41e0101d54448844005082054821040506029115201d00c15075401036503a0780e015901c8444180081a02070044158a1501c3c0d0305030360802040b41c000460b8004054412a155001d100d03c030480d0708010b0001f8609560001018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 78226305 1250 78225055 78225073
    0x40b0a02210c090102100b090417070501020d020307021b1003110c0a0b100b0f030f04020609131d06100b160803130b0a020307080406181e120207080d031a03 69
    0x24480b076a000040540c0140518031a41410b405540304140d04418040c060b00d5a6680b25607403403c040c00c100d08400720303000c014048800081c2c424001801d0088003240301603140c0c2047c900203031400c4120000081900c40d24500a006600c8030364408040079120b150100717421001c0c500e444014400c4d4980c03c002c030700400c11100148000c0041d0140554000720401ea03509603955802c60850250304030111303440d042040824004000c5805150700203000814241c9019000800580a41c03241044c0301061925601d805042c1c0940d41d0f1a20038520310240a4111443d00d00000e513944041da015200c0b0301d290100e03211404050128107806130650010700c1130b0b03503420142050400c8800001040fa03541c14240006145003840c3e009482c0258415201c690070f0351141ea4428002d420100a41e503911650020b9110104400079180320039144c182480190744610380c02d0060a0703401c0340175400290341c008102040030641c0041da101c40c4080b02c0c540064001904c14a10b4004074070420110703814800e41740c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 78227555 1250 78226305 78226321
    0x307090e09010c09060c1a04080f030f091b0307090c050405100e0306060a05030a020d03050d02070b090115030b0c0307051b0606040f050106090b0c0c040608061e040b0a0221 76
    0x110b15154800c80e2544e000d90740c0c0d40d00080302c2c403900c2004000c2c0b0030400302042101c0d81c0166842141c2262098403042e0400007040218429a00101d130509900302c0c1203c1401000d01003070055040070b52081e80180310840e0303d20f000c04d566080b01d101c0c03000701690721200200000d125000303950191400a104007400700001000038a0042460f1a152180c040c00012400c5450503a010f40c0858a018002d4803540340550204a000004803400382c0c1840001c00c0142c280c28100c1c4001c1c19410302c2050b50081034104242c02c5401c42d00300c1b02c004001c030115082c2c2400401c600c0c55943d03900001c40303440582e0344c1d654000d04850600442010b1003c3d03500f444040c503d500d20118905101d040c05a40402041d0880c00d50030095540a2144001090140406209014420740109000d00200c81140e080c4203042020800b01d4203d5440b12400f600000248509011740341c003a07640d462070002c1c410501e070800f5203030300609081c081d100641d11039002030001d10300c80c1d00c50f0700c4400d10054840980b10a141840c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 78228805 1250 78227555 78227561
    0x70f0c05030d020d020c09070f030c020705060f040f050405091c26010512062e05100801030b0a090302070501030e1c02070603060b0408030a030c0c0803040804090c030b0310020307090e0901 83
    0x70300413000d0300409040b00018102461b0300c43c821146603030303451100360f000b080076001440c00c046038504500504c040070550707840301c50050010030b040901e034540e2185800102c0c0110400c40d0441d034412428581480b080b443c00146064810403c2ea801285107203051038141d84210540c1524204104852903030590880340c20b8480341200d40c16544130b48802c0b00c9900d41511914200c460215a0144604c000310b1070103402103040744c1441c404000070803a600c550001c1c3c132030341c0c0e110288000505140014000c200b41103070b186401804520f828840c84d0310540c0d0294803a1120f0050300d04142d035801468089490801c1280c40b02060010141c402c0d12801c40000d490382198041c15000c40d0800400040c02003102080390111a1042d01640c01c1a00060003100034041c1141200d040066000205010414140007540540d00c51010318cd951071030b04c1040700581d210302040c201414903155003081c1340d4a0200702140300d0381c04405c0050780d941d581c7d0f205a5a40c0e1440e00003c6001025108000c4a00d80540c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 78230055 1250 78228805 78228823
    0x40c090e15100f020706110a0204050c1e180103021606020711010806010e2b08030108010b03100204080a15020c070b120a0504120f02120c0109120305010b070f0c05030d02 75
    0x2e1402000c05856441c2910200d04110107500145d00c5600708010040c03180300c5400b1018026000d89504a2640e000241514010741c0c40100c0715500017001404840e5055202c150055580940c0e828844842c10010f00c031150342030310310306054002074041c2c144140c4100d5615007540c042c0045403149041d003400494031414100075400b08400001040e480d40c0a03202145c100807004101d13514181428103d080380b043c60205002020b885103e0220000d91804041c5000c3e129220002446107138000c00c1614045a089a0b4411513104100038070840c3d0001c90380801e041c0d0040403695004200c0d0a0000092140c606801450b001d1044c3c085041542c0350010716808910001d03c4071107485003a03405049400560303005155012811045000c1400703408165100491401903c50103c3c01408005543e84083c60914107650340d0030040c01006041542c501702e011140ca0200002d6040414406080c0f25044018200720850144034041040d800080005001c1c05802c0e600b03c441142c3c4040e550700c03054 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 78231305 1250 78230055 78230059
    0x5130b07050a12091802070f020315091903090509060a030503040906060915020706201c02061e0c0705011b051e07030c030309020130060b07050705040c090e15 70
    0x101814556a07104240e100d003526050b01080d17403807082040310403000350301280c8211210214440c6802c0541c2e414040c4038812017040748030035041c0c41c0c03031205141080d4a07030104203202207201c4182c40c0480e41c4a8151416514280c501c0c6840d511f402d00000c01840840c2d01c018020300c400100401e9450041d08040b0032100107454000700c161f1191100c1e2106415010b000005031310030f650070000075200c1c1c4000b401c040200000801c4450940340294100329903421956911100342d07103038211072941006401e522480070120710840089034071440c51568000b03003660034201c501007240c509200080d40240e80340030340c90f04071000c0d1200d16100078105405c44140c5d0149400c601031130b86441000308088070f90303265040e640d8107440000c0e03903000d03401880c0214060b410040001c5d101d401e45281404002d1242246610700140102da0801800c180c1e90070f40c0000300350710070620110000940c0002e048050b40c0c811100461203038003115084896014590028180c225100700f0700c5045c3c0c4108100051454003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 78232555 1250 78231305 78231323
    0x901020106050102191214040306090212010209150a090b0c21190302030a020f030906040c080a03050304020d03020c03030301230402040e1602010e0d080906010e0f010605130b07050a 80
    0x203200700590301d0301c40f0075459110016188003242c0000f06850012601e4100310f041042240803a480700c54400c0c2c2151700200c800c2b0750359642810070751400c203003010f01c0700700010b000754604514040421074800c45076008051024010414143d1107000d440c40d44040c217841102d0076100c840d00d401269071032100c00e03000711410031031203605400d803250201162034100510100108554000d03104070020b50009003c030702410703402e000f00b0300d0b01e10714200154040d4417040300078203044c2820709002c003000070170b070b44001a1640f14054250000350418240c82e44540c045601e54101100760078107074180880344030003d40c9400008004582d48144001c1b03803440c0e05901c050307014071495a0301440228412405200c4104a00c82c00180c2a084a03048005540b0440d01c00850a281d43c1da4100d480c086130080c000011892300c01c01c10103072030b5041000070b00402d00b407114014182401da410800315041070041d10300b00000010506090f184500c00c010041168007103065813480c0b5810500d1f140c1c4011742044031035a034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 78233805 1250 78232555 78232559
    0x150f1e090c060507080f07030513030302031c0b13020706020d05070f0206010b09061c0e0106060905090906011a0d1e020711010e0f010f0c0c08010b01020f06040f1101020c0405010801020901020106 86
    0x4800c10541382c2c0071354441d111030310f81411260480303c1604600001c40c02c00c082040803482c0d1040c100d0a0800451081e0019034840484050480301c82048045445005180c503210511a5070b0310700c2003407041d040d0441c0069480340d00e8100b19001e0301c41c074002044c5e01414134003400071460f030001020710b86441c41da080d140780b640c0326440005503100e8500c000b507101d4824040020034881440340d211304001100f0000035009244001c450039a0740070b40c004408a61215004c200c0340c1411a90103900c00d481d03001a010030f41c14130314800103040c040f8603500005200450384010205a583c00404224075540074022a180b141d03540308080d60103103004403500200050b01442550140401e1a001c240080c45904900351807401100e42c202c018080408100c031103092900418804021800540190383c00402d918181d140060b01e0580304400101640e800b00040001085d502c100e42c0254981c00b0441c1b8081d00741c3c08004038500011001c0c2194000d00e40b500025101d4130540c000c08043e80280c0080c00308035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 78235055 1250 78233805 78233807
    0x71a0a0506030601171f0209040c08010b03040809032b090e0402010905041a060f070506010503030f070b0408120f0604110703081603020f0c030307020105010f03150f1e090c06 77
    0x310260799903a00b6034002c0b401032024400883d1140c1842e09400104c1380c5020362600607803404003450b0395a00134140d0000d000b00c1c82c0d0500740541c1000c00c01700e051005055242c10400c013041d200050001d403d000c0080380401c0f05030350910240c2640314007100240743c0248142008021340c001c5d482c014000c0354600c1c0c1d001031009000240355100b1038050b1110f0b1030f42843c000a00029024441081c240e42c2140343d142c10326a51880003601ea60000c040b81a91142c0342031801d14908601a04100d100341c1c400e11020810700c101c0012203803000da0104074000142c07107910f850070709802010401c02044401100b003000003e40c8000301c9108160403101400050300000600c2041c0c03041c04005000221864001041c0c0421401981944c1d089458018900a07204130f501046400c0200003e1554200000b8800c02640c240580384c05050f581c02142042440d583c1e031804810511100c551307185031141d10380000f42c10300d0391101e07142c69176041c801e00c07046010510080081843c00710407140322110300030102b01b40d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 78236305 1250 78235055 78235061
    0x3010e1014011d01020c03010c080901051513020d0204052206060e060d021324030c0509060702011b080d200702031e03040f060503091b011e0311071a0a 67
    0x780006840d000801e148061415440d4110001e60078150b200300200d0f0a800d48092151104002e080c2d90340700b40d581400010b82d070039124041e00c1c0c4400d044019400c0c00040e0795804944400084c1c80348010f81e154414003454010340120ba1000d40d1044090f44110030440d10320311610710840c4800003c0211613101d120589511044a120681140051019020400c1a84e00401c5200004417070700d50196030780c10745a180400e210207080300365418007444849007a05401000340c851600d0411034145440c10012403001d0041e144040d0422151000480881c0300260030039240ca600046415500c006030b1540c02c010341040c041c001a141c181e240030f6513a00710410b0960b600d055004019001c030868003840211650418190060a0f01080200040c8080101141801841c00d526155100c0c0f80050000d810511607240441025040107170295080ea80030180c09010700012070a9001440d03a01400c81c014003d25103101c00d469400110b900900900c00c1100342c2d03400700403410500320742e01c035244a025 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 78237411 1106 78236305 78236339
    0x403050c010206090703120804110d0602040518100302091e04030c03091202181b0408030405100903120806010c02061308070909080415020a0803010e10 67
    0x15942c051104543c080544009025180c1c17850311030004010744103080300c0401c20008005410001020311044061102a0060307030075201610301103009510071b016661061010f0110b2805405141c1c82c010310508074407580300035591555007803065809000e8101c851000400c1c481030020680e03140d90a1042e4000d940d00c01084100d07003400340650300340d17800c003d04200200031102c3c05a1501340303811050205003c4482003c0c0e0f07500c90b001d0b40011000d01c900e00c242c1d400140020703200c0070000c050402ea07442100c00f8500c00400c00c1d810794800e0103d12000f0110080c44c0503044a13540900c4005500082c18146101c0740d84075503000400301d901014000b842c52030b07090400d02840d0000c1046801072700c02c1c540104880c4041346c8a80c00140614420003400b2503c6283c0d044c030b0184207000c0d240074a41e00030341c1c013034881d61034800c5404002011203040084174101000062000000014161 = true := by decide +kernel

theorem cover : BRFrame.Cov 78057555 78237411 := by
  have h0 := BRFrame.cov_init 78057555
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78057555 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 78057555 ≤ n) (h2 : n < 78237411) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
