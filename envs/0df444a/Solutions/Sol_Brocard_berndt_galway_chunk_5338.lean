-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5338
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:32:21.015142+00:00
-- url     : https://prove2.me/submissions/c92fa5c5-c675-42a5-a681-487af13fea5f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 959892086 ≤ n < 960071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 959893336 1250 959892086 959892113
    0xd09060504032a180c031506050316020307080a030b0301230c07050c1c0212060c1c020c0703030e1305100504090c1d0105040e0f1f020903060421020a 66
    0x210b0326507180f820042e074040003080240c0c03003000f008952000e51801080c45a201c0b00785140356403400c1040c2803840700106940b0007644a51804100e003400007620782c160000380114641e107a8030540f0314020b10380e51245c03595000034220780c0020383d686400a15a04092040444450151040b80b0b142810401c96114090300100055403a62001c0381c2d81082000800c060f0f0a086402481e00c80c2c18445c00c0140b000444410300268031030641c242e400000000c01241040c05100a042410701e0710b01c09503a1407100f10048a001c0440d141d00700083c11040b0320174401200134510035901c11020280348030800694180d070403949000725280c101402030801021071401e0850744240c50105040d2080d081510200d401da41c044a580c031050401c6a40305620490040d06842045808000e00c80506600036541d50b404040000103511112031001c2560841a20100600b8050005403425022130003013418001e0036035049501c10a00c0c1d07043c010440051941c10780c070400300e1005040380302207525800c4004040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 959894586 1250 959893336 959893373
    0x30a02060d02070f050a230a030305040f0209040c0806090c0604050f01031401090c020127230d0c1203020c03040e040c0909050d020106080d0210020f090409050d0906050403 76
    0x750049440c000ca0b0183c54a590f0483c155103c01602c605000361541402d00c0103c1c0c00c000c0b503892914121860008a20400520000414401901c3e50301a40100000752040e02d06861006824005a4400c1156071180703205c0d0702c08001180c035003003140f07280034409001080c05402401800c8071a0b201c2000f0f880c211201240e82c5407031440303200e006800400101010114080081001040311807094114015145040d4020840601311251713a22003c04003003086041009180d281e100440c080b084024043c0d03030500640d48550307950842042c50a60140c4118000c00ca900c280c1100b80402c0b160940089215400e0946c905080b0408541e1240319502a80300003c1e0a18086424880348070800310240c00c0c04007080140702c515040c03065648102c1d55100303005600f02240411103090129610040c01070980081c100d0104111100300a90048c05162641c0041070103000417581d030305e004218682d400340d005054124043e20004250210344c0d004202840360401040000401110f90326090500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 959895836 1250 959894586 959894599
    0x215070f0305060f150c0c0901030c0e2e0e0a050c0a080c19031406040603081e070204150305060912181c03090f051203030403180e04030302040e0f06030a02 69
    0x19040300164404419414090b00311852800c10034030f989005c0000d00e0000c010000311182d08040307004000701c0200034040200310003030f001020010403960981403a000001c03a0901a842c001404041d5003960180200350080d654580e0200714410b411500309800c8030341d0718410b00107494040300c0102e507441440b002108101805000481c011b86100c01e90346801024501c013502181d0300f08009011708502040b0740c52080e0f0040c00b00d0000c1c1740ca44501001c40b0751000f020f0741481d40401034104619000380303500808400c00c00c007500040c0d450744148882e4513140780703c00d4425421410661701c1e01c4d10080c0741c00ca240e031020a10003405070601003928000c81070246400540000d40b0081150340010044882c03a500002c1c80050406403c01000c8051701c844824190146a443c0c0405c812a80e0300110321307546400400c042408240700f1202c80c504070f000504e8200b002a030f00c84007036072141d03070480707003030380040c0d40401d051014102c4041c0040e00034807054600d00890a003140041d86601010000030310941 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 959897086 1250 959895836 959895841
    0xa0b0402010504030c080304050f030a0b070f030b0909010203070e030316020d02060418060503010e01020708090f0301020c0f0d09051f0c0309051c0203151e1003061a010215070f0305 80
    0x20b01c524111806998401440701303d01b540c903810583e498100303025140c8241641e5120102d1402d0005415820701d400103c2e0b185e1548415100751455050003001d40c040513180d0100c548a44c03210004540120418800143d4078600b400b402401d0649422100d0300c40d4000304000442000040103584916804441480e1088407610008083d8410b6a11516080d81d0420350f0003841055a4000c3d412541c0540085c4010149a5a01030803131080041c010000c110512603000d0504003260074000e03541003d4001843c0080490038640f602e501c603881c0902c980c0c450341302c50808070392240010000780700030b0f1a100c54590703da04104c040600c02e82d1903041000107150031007017418410032044006290103001c0d150b607a9804000d90b0207011079014107034020720a034500e200c81c2d180c100d15120b02c92400304500c140e10390042c480000016401a0000c0020382c2c03c0b100102c08200c4d68840d00b0013820300c0581195400002c48000382c18172010500d44040844442d00700410950081c1300c1e020854101d1500080a5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 959898336 1250 959897086 959897089
    0x240504201e1207020a0506090f0316020d0c0f030c0902030c03060f04060302100908070e09070303050d2304060b120c040b041104090606020709020a091503021e0d060909050a0b0402 79
    0x10b00070081104401c850042c00d12007030640101e200041c050142c0165812030f0743d11205607980c0c40007012540e21036071042207525282589120382e0800c1c1d80c4000c0040d050240c0f561182071640c1401d800c1040361518008041042040036014071004108008042d0f00b541b0f803d649004d03003400014a224010034803500066042e54855200001650380140b04080c0050000390091404445006411480c0310303c85010501c4e101036401503119402d000000c01d64181980e9045980d90002061504015158440301d00d4039a0b8032241d0000c40c04201c540e81100e450070341400c1c400d4a070601c070800c1c000c060b10000151899000302d64031421001c103071740200c0c0c143d4100d0b010030010030441c49010503211b000325010802c40c2c0d10b50001402c94002e5070031100340c5529843c10500b280321b41c024960106011030001c01c28000c801210845014031400e006060140484a0204091070034101c001040000200302640da00c9501c44d84002d046010000c02100c2140c0d5242c1c1e81e96090340401070044100c0380005000c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 959899586 1250 959898336 959898397
    0x60c08070b0a020a030b0d0c0302010f050f0a05090109050f0901030204020c0a05070b131a03060d060209040c0e010809070f030f02030c1009051e06070b0a24050420 72
    0x129903005103260054584030b58554020340000e101a40001d083c00f542d000a842e004020b056429000300d021400e130b82c030b15030055403244054840d01043c00f506001d01041c100c1c1c210041d0843c0306150700d03100da8400315200014503527041034122034422140e80c12205003a440b004583c2c0d040d2a4181d0300140e48101e001c9200e407604100b0305005125104005012502a085601030202840c41e00b22001089860740e00141514803806009190f00c4000e03c00103816250144081144600440006107450107810224099031001c080680108105014270341c110b5a00421281d8000050805022403c1c20b14015198004041c44064030b20100c1e46110401e40da0180940b00070b500006220040700c07000c04c08041d00d14003251055910a45c0110303d519800d402400780c48000000080c03080340340446903582c948400780c0292070410b440c1e555080c0039400b4460b0b419240e03001d46410083d01c3c1e00c0d52414040000b034800c1e40729010403c603c0c0300314500b00030b1407e0050f19452038010024a510403c0042800300c2d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 959900836 1250 959899586 959899597
    0x5061b040b16081920030c061521031b030309030406030b0a1e2c070f020715020a050609010603121409090a0902271503030f0a031b0c0c060c08 63
    0x4191142c01440e440ca42c10802c3c91500c5c0361700e503a41030802d0601c503c4a035141d0003000c004000c6500140d0004000e03805ea502104d0f0310381c0d801003400c61110f9040f511542d000303040213070804195000090500d110240318a2071104440f642c4021850352900c228030544038059441101e0a2548848441c13005513100803038040508410000d40a04c0c2d407040ca05141c5e01c21040c070271088540380c491a040c0103000e5030340300d6641c1346042004e204190341360a1070807604881c103501c0660450098400100e010700006079403074050707040e5034000c2c0302d040b0490034030703c0c140803026202c0d1034a80e26000341000000d14120611403003402c00e050980c0898003118402d00a0b00c0f8502030182d121241104015031044641d0104c0c098500986890101078501640c041d40210710304d104243c002805000101c07001c0700c10745440300126000c0d00f641d05240c45129020810f030403142010020079240d0041190041d0402011240c145d5185043c80c882c80d0b050700d0300803a50000e80611030401841c4188034083c403092108035070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 959902086 1250 959900836 959900857
    0x80c0f0301110a05070c06050a0507080322050c100305010e01060c0309090c21050f0a11070f0c06140a080f07090312080402092a0a14040305061b040b1608 68
    0x5541e503d002c0d80c010201e502c0038400720707002400000d0104129124000b59800290380d520340354546600c6460b945c034036403c01400003004030f24041c0314060f61440d0441004d00a0710a02c01410a50309420810008502102c0310745d00301417800b0010418032484084490465a0f1424407004071a0542030880f481c0d10141c01c00c122250400800a100c15840320741640d80e40d070350106103160300441400b5036017950070070f60b403004a00c00c0540108920042d581e0001c2c08040e070800f60985000311603903507035010411810043e1035a01040104100032504816a4003140c00343c4c00d00c852811301104c1c000f5201c3d007805402000c3d04280c82001492140c01080c040000d107800000340059a01c80e414000c3c450001214100e00410007100800c071150741c0002c00d05502c1110200715400d500c500c5840390034a801202c640c5081180d0452098407681142008202444c0200083c100601d001b01c0059945455a43e002210603402c00003000b4180310103083c0c0710345617080f18202d001f4042908240e28640a40c03240310 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 959903336 1250 959902086 959902121
    0x80307180e07030c0302120402041d0d11010e070b0d0b030c060d0e0708070f0302060d14010e180a02010507030f0915021b04060e010e0c0c010609050a0e07080c0f0301 73
    0x2040781d00a2080c1c442c40b9008a80d414413400c00500d40843c00d90083d44c681e400303441d942d00c001c14018034040d0052460141e01c0d400c0741e0f10020402c55940e25003c21101008081180c07811046481030080c018000b09514a40c010701070a450413814025911070005a8940266614680b02c0c040e60f0500207004480d00042c8159110034243e003030200101414420300e0810702c0762520015034801301154120441d8409646402e03510302e16000d2204641c0582c200311007440e0344500d19500231169840c068041e12603c51000c8a5181c0560644840b01942032100305641c000200b210050303034050121110240c0c07510b0a2541040c07804829241c681030364002500c1d6110f40c500310000c903030f4001034036131803001d06a10542080d50020140401c44005019034184181250014400d2801050405402c044907000c500d01c2c09420303c01c074900312041c0350405413001e502d40003032100c20005401001600f002e000301900c00da5260850340ca039522000c481940c01440e544600d00100e54082d881598800b000c205035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 959904586 1250 959903336 959903339
    0x30507090c1b020609041e0e0f0709090b13150e0c28030809010c08040b190318060e010207020d0c06180b04180e100606090504020a0c08030718 63
    0xe540070307014200145000541001c0c1544521451021011000e41c014000900e001c0d4074409200c040c042c0c2c40100d4046481190900d0f026918600c01d2000c40b41e000d03806095100c0c0118245400e01310310754000ea00a81c01d082d48030300443e68108080d0b4100d0100144002141d070540741c40c0c0381d0340c102c400810030414a440d000500c2c080c0c010840d005e12280032a040b40e810b120a250883c80015010b184000d08082c440007880020030000040054020504009803050415526040e10380d006802030340388480017140c0303510b40340d01004400002605a040c00d0200013840a25540204e0351740001400c884c0e1101e40e0028510020340c101d500b4290090080c601154840c101032898440912a070400180181c0c130034800c10346800840030582c1c128244180c1307460f02d410503039072454101c2c1e26845d00640e626480c01e0407144003000061440100e440b404910b403440c0003405801511580e10603801036004109141341554019030019100740d01800725526a1500d690440d03161034014240e00f6500b18901c2c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 959905836 1250 959904586 959904599
    0x20d0f120207020f1806090610081306061e08070b0414041e060e01050f03060712050c0409050403081b09010c061d010c0809010e030a0c03121509020705190209060910030507 76
    0x40705c034400d03042a103403042d194852109100001200c3c40c0311700e00281c0000003040c507076a0558613002d00c40c1d00030100410100e03220b16601d14009501003840d46001100c0d64204080b5009120b208000d082d25100301c1d040524014180c2011104000c07201d104d03680d03800450b108000021195622181185400c00000c2e40700c00c1c1c1025120b40031f01542d8070030044c0b1701c003400c3c91785800200c0910801455a902c500481244000f0707000e810043c00c91035003040c00b803001281c01070907803240a1081d07001c1d50701ca01340ca040a210f0040762040b4016840f00520080042416598020703200c8220168481000268031085c80f00d02c0c0721464200d004a402942041d8542d03200ea42c0c060f50083c041e0703000200800c080c12452129940d248206c48683c008180701c0c40341403002c207004490965010030b0b004404036000c0014049080300200c0307500405840f070b9001c44c0100038032500300004880b4600d15000c0024918580e00011035214009000511402c080380025a5941080c001c0300025544801180d040f07a44540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 959907086 1250 959905836 959905879
    0xa0501081b041706010807120f0302070b1911062e122108010320030c0a0608091203041106220824060a030212010603020a080d020d0f120207020f 64
    0x7410450503100e04c000100e0100c10100302002111010281c8402c5442c0381d075500c0b510603428110950941c0614400065880d1421009103000204801c00104180304410b014103000c05246841441d940b082c002c000321a141c01e000444004051540a80d880d0717510ba0440302c241d4140d42220041004040c0050204071540c03070030f60030800182c2104417101d03800300e0703044680c00b400b480003901c4c3c1054264003840b1445210184500c030070700030b0b043d0741d540c50004c004035020700955072080002445007010010600803c1c04140350322103078101d01511710b007801d4a8444c04c2e40300001c8800c1c40751800103088942034002d018030841c2c0004020b10001c106a46004040d00d858819404283da400c9107401c00e0f000c80f50160100384104401001a1015800e50b02032008144030754041141540d6211404000341c1d490310310f0040200042001007141c3c4d0343d200c00003400d01404c000c4000a00451341c2940b1150364004010034011450204010780312030190000512500c800d40c50703190401103207e03541c41101c5959 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 959908336 1250 959907086 959907119
    0x6050a0e0a0b0d11062a0f0c030a1112070f08030415030608060703050411130603210c15092a05030706050403140c0909030c06010e060a0501081b04 65
    0x30030800001d42d0b039000b4481d0400050304000c003000e5001a180b142440c20201511aa50b03409084044c0100b040a0500c000c501c0140380b004147e00507a15510300c814108070000708a80d054000d00f082d4241c66403540000c0141504052040200700c080b0891510100550001000204c0501c01a595a0300e107094990f4032500402c0e030f81104810595039164004d00940c41180c0744c6200402a6a50f80d200c01c900902014104550101c1c0079034210003d0307507550038504103032042003000007002842c602c0e2400e000e1403141a404215102e0650360100250810b20710481e00382c000a000045811401011005006900008005004850141e54104801006120302c1030003010042d032880e4840042503035400072445510001882003205100240e034451401d10100c1c02407040b0b0f90121404000190010720072070702041d459101155606034041d0401c10540144504140c00c8140d04168010131000e10544c0a010306200001d4042804800f101e11001812032541e1070050f121500e52080c2100302855 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 959909586 1250 959908336 959908351
    0x207170f0c060105091b0a091e181a012106030c0608060316060f0c060c0509130c09051002030c0f10231302012616020d0f110106050a0e 60
    0x948002013054104a4082400342d00c800805005183c1031800100e0180c0c40880c0038001c000080d500003c8031543c1c018400b03101c000c10b07201c0c210560304200070892828230461103051110706280e0340f1100b085028180c51403c0100303207032030320b00c14211614110841e02e00300007140712145094000000c0c051205000c0c0281c4150341e035a0807194680b4410560f0b1480140c6c1071416010200c00d0800a5034003e941900c04407100c1d0038042d03d0248552144030464140c100214085800040c46c081c0b10324109001c00400f400d100e41c20000c02102c01ca0040c141d61203406103900890081d411f0740c0b02c680c0200140c5400b009014111548840c0c020713070042d10b4881c120100c8181038140600c60300c41c400700306000303a994885d4204500003540e071000d54500d0800d03a400e050341480b904803000e0001c0c108203a00c07010039031110142100720741001c42e54002c036000404491401c54004040c1c015030036500440c90a0404044c0c6094188a90f89500030f40c0184020390010b130780240d448030005194402500c1c0c0a200b03590 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 959910836 1250 959909586 959909593
    0x15170604030f081021020607050c0405060a1a16080d0b010318021f030e06010e09150420120d020606030d1e03091511090924040207170f0c 61
    0x41802d8103489959040d10b2035041130350424401d00010007005950591088203505100196080d600403510550041000752515040704111181a082500400e07070080030564540020364074040750a01034503d56000d1000c46440007888200249400c283ca10b07106420250199803a00200d10300d100405052036441d02003030910071100c1d01c50301400601e98030690094904643d504d070f45030070100c901c44030f114020f003410384d01c80c0091200c11040000314080c0122800c20300c018104000302614041001003034070b076503409a10400001411716200000329101c0f010201c2c0840e0403100010340005d0218901140c80d1240242d514460740c1d001640d580100ca0a405860310018645002c49045414030b8a031040154622216002c0520a500c42c42401e80907003c200720b000c460714505c1c000d5541c90180880308071004a07814a070f901d041e100721a0805501d10030090301110554088159600d00a03905110b80d50208882061103c4071040451020302d41072410b03501c0d0b2080201070b407623400800aa149910 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 959912086 1250 959910836 959910857
    0xa0c170f25050d060f050a030b04210c0308010b0414130b03060c07031107061b0f050a0c1502010501080606040c0302040803040906030b15031207020f0a2c0610031517060403 76
    0x2c2804050385d0070b80c0c1018040c0340986007940c45040c005100640111003117440704088000c00700603001031000c00d500710303954810680040e0600030034044040e002601c9200f006c000c200010504030002000c4030209840f0b541800c440000a64002c00c00c118a458050042004100b0745079400301c002e0007114804c8d2140400003503007081481d41c6903001c2c094903002ca480003071004041201c000030030064a12070a440f04003805141d5626040030040da100300c1d14248401018484201044c005040e0901d0300d200070000c6615010304107a40749405411740d40a0f5540b00c0000314a00d100c1e40440d800f900e408000c8940e600d503907240020041003d844143c84a544d214040f80010210b9461100d0105004000303100e00303950007004c203240313902c415012030f4072403030000101040d52680d682d44402805513080800c00c41241c180e8410360018508443c012000f542c03410440c81d40c5d21038615440a601c5454000b0b00e81507a17107007500c460180d0782c0020300c1200c030b2404500e00e200310010f0395500c41d0340702e66151690750 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 959913336 1250 959912086 959912099
    0x50106090b070c030b180a0b06120d0206041b08060c2d0423040905010b010f0e090a111605010b100c020612090309180a0c170f25050d06 60
    0x1400340b108000c0c801e411045080004c00c0342c1c0407200d5000410000d82c1d0500e42c141081207454142c00020480e0000b00b0346c4208481807402c44800c40c41c929a09000c1d111404020304000e444142c0104010101d03149020322043c046c03078414644000d015040110392060503c00d00e5004950495480e104d0700c40d1801d00300c080c50051018403510115800000c50f400d180c01c3c14080300078848000d10020f00d010400d18154450340d1140140d80d00c9034000c60000403030a4441c8001801040403410000038013124144080107500c03103040300356001d160321000141518400d10080d10a20600388400c00c00d01d0b40c091403909110040d4454103c030901140d084009070280780b03050310381942d080f1000e9801710081c4003500c0d00440006c1d18036805015602501d25007140840014101651090785a1103401c85404004400686115007002560a800c02c488120b1600a004e9508003006001511840c961404900b200b620020b40c121401c50400e850b02c070451844000628a07080711800802050900800042a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 959914586 1250 959913336 959913359
    0x22020a08150307180506010c060f1d0f0a030c020d0605010b0c0f070b0a12090510060f0e1303050c0a02100512060a0303020c061e1801091401080a0e0c040c0305010609 73
    0x4580141251481013440d9208140080030b0041c5600e0500000c804950005030321072081d10201341c8001c0d00090800b42c1e070300503108141140117103002d0b0781d800002c175071341208000200d80040c5585071500300144455440814001c11610800920fa0b5042800105420b12540054480440380c00112080030b10566030096403484103200d00301101d0300030051890300300d00c10300d0341005d03004071070901203800e0009075100da140210041c3c0710001c1a5540109101c1001e41e0750708030008116071150340000303041849410703624442d807004c024180480042c002c501c4da4814008004855001001000902d00743c032409091980701c10610b48180400300e0000b07010740382c003205401c00e980d01680200507041441c42400342e01e911118054400c4000c1100c0040c0b69000301c0300401e01c0010311140c0600c40300c101e000240041d506c80e004103c001c001e040380b404141e40d01c288501d5001c02c008501144c60614014410706003448004602d4216041c5804440d038a038141e00403a04a58095682c3d002959407000120300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 959915836 1250 959914586 959914589
    0x30617150c040302370b0a02120c0601063902010e01230d110c0d030c02280606031a010807151211090a030b070320030622020a08150307 60
    0x14410403217508188800740c0c5c2600d400d52441c4034004201c904050f408051001501540002070010001440d412280d5060200c401000d0741481c1e41c03414505a124019107640050107110108983e96054207007941c0c1103060b0000c950405030748942c2925a22520800400342c02e00b080e404200c0c0100070407030551243c1c40c1903240c036001080d40d081e004005003510f8040c3d403080da812140152114a4411518040802031020052070001480c000d00444005015990096010401d40d00805d03400d03290259440981105a100c01c400b50a994213580751003c02044203800c00b61008281c02d0500c5030007250500c0050603101820704076124035544400d18503440070b55407050f0b0005102c06080c8074020543c0c0d04110303410009200c55a0828040c0b2000c070301e8541195005803250300c15081072001d0160544149801030038a2600c003803640c1140500f00c842880080c100798010501e03043d0405401f00100109501400a48401d55441a8980c070060803110203403000703001d2103d8400d94900a20f00000da120 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 959917086 1250 959915836 959915839
    0x1912060b120a03030c18060521010509011712070b040b090105161b050f0607080a050601090b0306030a0b090106030b060d030e012a030302120a060f0b0901030617150c040302 76
    0x4410102c60750210042e00f903008a030f00c20f2004440e41e0350210905070f40c0001c050905651501c1c1c84081f0b0b200440584048000349883c2c1e02c00440c0144901c1d00d440405505482402d5180c40e00d8003104140d2a142030030b2003415040012010803440100a01c0010f00c07070042d4001d0b8a030401b507468a5043c1c2c2d0803a501274500b81c5c07568040c02c00c02181c940c01224043e00000c110502d400340404251903407820400c0142100a46030040001c02030074640110010307400c000319071820030080c9418000a80284102d0103180007299003c400980c9565081003c5410140c4c8007006000d582440c0c0300442c083c03c0b960104549901e030001c0060681d05100b080500740b1500340d40c41e520200080d10040d201102c01e0810340740d401664446400f1000070110100704400d10940c0e006035980b292050b0a050848080c0100d1005030074074500f00103080317540b0011003c1e18549040d0968031031109005800078446580040892086030702610702003070010540c40003030081560b4013031151791127420b2111240b00d5400001d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 959918336 1250 959917086 959917093
    0x706051003200604090f060305060106030c02060108070302010c0b2a090109050402131e0801090f0606060806012f070e040c0b0309030d090314220f180504021912060b12 74
    0x1084841c034a900910601b60711560000341a586a4540608185098001a001c2078880460760040c6034100615401440301d000505003490444c1e0000700240071001020709104104400b0403541800300600c89141c650b0759403588050003803009102859040800a80e01184500c82d001905051500032511121441199815510f08001401e500100c1d0104800b10003110b02030b0104408900744a82c607401800703503590701c1c00c80359107241c8841660400d030045070401041d80c0034001343d81d070420700c440e071140b44030b55019017090030115000c00744800b6038080711a02d2180c10310001e003840322548960f00850103114140c0d55a0b80701c1d06483d0903407006030f8089030f16500400c40c1d0140c0401c0b9034003a462081c0709140c080c101909e44041d40b891a048490480e0b0b056501c000003c1e035007004090040018203d02c1c0090490340e20746880024031042e82c1c02410740d020749a8000a0442d580c0381d01d100108844400c0c2d1010041d240d5400c046035060000c412103959260a8400c10f02d071901c1c0c0d0040600c0e0701024004c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 959919586 1250 959918336 959918339
    0x91101020d021f0e030c0d080a0606092711040b03091002041d13080301090c0207060e1c290702010606020a08090d060f0515030c06090f090c0706051003200604 70
    0x768401011140140d02d00e0740414440d000000e40240504036103102c02380da884a2500b012a051000c0718103907070084080c0165058104001460140c3c0404114104043c0030038880f4000c1480002d4a004a01e055804a0001e800304014100e00f001c0e41c060312940003294812007940c03e03050304030701c07031402807486d1000a183e21418250100d940540d000e10342040c13407084115280d5519016030820780000c41c005466207180346180d03a0400c007120081c00e042c580040301c182d800c8086009030211140421a50341601c0b0702400b40440c09408112182c10000e01814650b10f0074005803420609603078510055003082000101540700088118045410807141d6150901c1101045064414000103d4203e6181e60140441e452280304061042024056940c1c0000103e0700f01400c01c0040c46145100e0700d428020103101d83c80d0b5090100801300b0640358005a500e981c503140034a0701466400510060500c000c00900c00b4079880b254040b2071144081420000c005100a030f4110f552a40c81604042c05000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 959920836 1250 959919586 959919643
    0x2c1f0c0923190e0a0e010b030c01080a0207061805010203040c1413050a090204140106020d2d17090a020f040911041104050616021c33091101020d02 65
    0x1c03034111a002c0200754080c180d685a0780c40043d0001c0b0345403112a580c2c0d80d086904c80200b8002c44206d904101c02914865620400180925001805540c9010750200755401002034030340c0803008440c01030324650000c107014035025001c0d5000712411600c061941d2000600016030f444803032030506004200e0304012401c804005d00510000b01502c04498465080c0740c0540ca403072003802540f10702e5a5903122658101000a480c03c1c080303580721020081c0403903144400b455440c08800701040006044640306030440e4046880c2040e804c0c0c0c000da05540141401120100001c000b40014426201d003000314003540d00b00411140004800380019443c0d100c240c00c81d24060b400030841c103a020303092905040d103e0300031480940019840140513145a01c0c0001546820708a14212510a64001013215050303078918102c3d0950200d22001c40705244003010030a840c640762003400112865003008600258140011646c0ca540714050140c0215141c85602900c08107000c0f0703420000c4240b103c002000401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 959922086 1250 959920836 959920849
    0x12040303091e0c1401050412080903240f0f061806012003090f03341502010c120b1c020a0e18070503012c1f0c0923 51
    0x70088442d01c140791803241c20202d4032800c1c42c20b00d034040c9070703110b0710305040c058001c1d503502e985541d43d410702038103000c200f085000103901c0c0107c982d0302489049e21540020f010030b00d40783c0401a0721984d03882c0952007880700100d20480700d210700075001c1592010380b01c181c0811001c3c2c10a50b00180c0142d035400544c00c80c4098440d0b499007122042c580301141200c042c1d4900500004213400ca40305405c00100407000d80303000d034203200c000d0b00c007100a003680310020800101000d800079010300c0364812160080c03030b03081d500619042c010001c0f515104000b00403020028005c191800000b4040740c29480c0c039201e402000e10440700d64010141021861080c03100c480b503480d1444a000b241c2c400500705001c11680e400b0034100d400703810002e1012803c002c48107141400d201c1c860f00118000ea140007003a0034a100100c4483e000d840c800c0340120040220b0b0700d061410507400311880c3c0075040d40c4011141070440300f54003901b014859903544824032919803402c0b000301c4000d082d5038541ca641d0f01505601a29152 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 959923336 1250 959922086 959922101
    0xb010503010e131407060e03070b041502071a0d0c08090c0d05031b0c10140306061803010504030e18040c0e19060807090c020102090907030c020a0203151b12040303 72
    0x105401c0115900e50302c0304c8080980c03c0241d8002d41110f401000516040681d6000d81030b000c0340540010340c185200e56105015a204a142030810b860208900d10b0090040030060078102403018500b030001e17111f80399103034803c90142c00120315004e40405001d100300800c0340a22070781380c060100070380e000c000c0191010303809001307680d40e001c1000300000000031100f4028000b0b41200107000c100007050308104200d6408920301c4103000701003021100c0c850721441203a80c400b0040f034105407241c3d07140e5080104071052101c03464141d072030002030006264000407228007100c1c0c11504460f0601d04840010140c903c203a5000704140140c0c00b0606c0305140447c40603500c44e0325240d41c1d01c2c0d9601d0020440d0107881060b1310007241a04141c1050000901501030051910100d000a61a05002201155464400038404001c15964204015545100f40b00c0e801c3e04071f400074212a200103000101c00042d0b20150341002d01151100c1400c20000c80c1d0307600303903014180361003c400119a900c4d201900030b030481 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 959924586 1250 959923336 959923351
    0xc021b0612040b01051507050304060815030a05070f15021002030606130603020304111017040602040b04140a09150b03061c031d0a080703022808030a0f030b010503010e 74
    0x50002140e40c001500c01103102d02d02883c207842c1154505018040b4000d4417416064882600300010008a4800000c54088506a25101c80d0f140d98107040b003192040450b030310550501404a030003050100000340301c81903444c00310214140941d00c1544080380802040c0501c0543c01ca104000e02903517041d800fa40d4825005801986414003000308480714105a07000000803940c0031060000b40919201612001002543c0c448400900036101402c031030b11003001c0c40f200d02c2c0094001020010160103640080103a83c2916840325194003030300540110b0742c1003403802221036450004150100e40140b292000c0c503403408400c154100300100c03945070310061070740b6000410242c01808101000d100411200d01179a130b8031004d080380c1e000d8022040d145052591045107032140504c00c1060101e50201241ea0464801090040380000103043c514480b0400039058013062000410640110007401081255603076140505202902074045984042d980380c00034000b8401404050711a240c80e6800010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 959925836 1250 959924586 959924599
    0x9080d0509014a0a0c03030e010302041a0a171614070c1511030409060e06030a120c050f0a08090918070b0f0c1204090f0b1e011e0207030c090c021b 65
    0x80d414105071070f100c2c55030805c841c2e00c2c4203543c0800c14107038044803100611100f440e040d03145c5407030030648841c0400d450441003810a40000c203051158000c1c0301100c01080000041c403002d00c0c2440250004113541c0c03002c2c0001c55003806404915090701c3c2d00700c645455210241c40225030419040b901c135000380201c1b9000340b0407003c01d0410703200c100700301810041050400115080307040c100c50b040602d00145c0340500a5211011080014600e00070781400508680b8010f8003c2103a42451403500c816421122503501a0392400c4090000c0300c8000c080301c940035541d48031107480d00f19081001ca01c607000750721042d070814130090010003202002008000b01c11503d10341060056035490342080045441c001d84424000740c108100303d0a4040c40c6980c00826204000303d04440b030200d50403105070f100401110400d0030401485a000c0c6402c0f0740315960304003888080643d120300c003071364aaa02d40400d840f0503034107400000e0f10f8840d03405280e8048009902172b0150f4840366282000c0704600e03400d03146c2d1114 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 959927086 1250 959925836 959925971
    0x12050a06060801020a031b080613020d050c040602060702060405060103120c2406060320250b0f0f061f030b03030c100b0901030305031909080d050901 66
    0x8003640150741c0500801400160303100604d0b1005000c50351a100100c1c2d0126000304004044c5400080156010780c098a5190845140c8a07a1030024400c0600e66400580303004148280350f00040301810035140c0a07021515142c80d0350105a965030b00c100e400919661240d00140001002c102c003054510580d800d144200682d29130b2810006500000d09d00c0d030b08003410100c00e017115800d0213030038020151400d041000c00174a074140d502c8421408400242048005103440c001200441200e407480042c0302e07071355600780c110729104294400540700f0340d44241c16600409e100c80d506001c40350040000801100320310340d041c00b04000111103558003406069071620304000d00c0c1c800744000c0022000c41806089086c41000d181011111600a03045c06400d4180c01800000c2c0c2040c100ca41000128038841c0020074440b4080c0701070802220020100e210100c0c40000e48081504414050100b05009101d1604070107040c4448203080d98403c800d0140302840041c28a5103031910840d0340c14002c1c00c0340d5044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 959928336 1250 959927086 959927093
    0x3050c0415030b0d05210a0f050903070317030f010e0709090506130e0a03080f3303030f0c0f011a0409020d0507060801061101050415111308010b0102210412050a 71
    0x301d10300c20262100d4115142882c2810b8a000d00507441291b01c0120b20300f0202070301d0f401040c000f605224401440790001d0201c4080e034081100b40c005552040d60a55056006000000781d5041568002400102100042680c4101c080c82a1264140c2d0343c030b01031414036048a0001506018000381e03000b400c89141d060f440600ea0086082c02c162010041c01c50907517a280007040400000c100d00501e401140034003141050241841d030341c504000c08600420384040b103510090703404121100741d06100005482d20003a00500140042c03100c690b042d240729010601139142038400386504071515640d800040a03003494103a01c00108a400640014040c0f04a170755030b1887c0074000c2e008000420701070401005800d82c4041c003000841004802800315081c2990b0309421008601d1650925070740710101c0980d881015001d41da06840c06440e10084503a603800b4043c024500c0d4841e19005001d0030408401c00350070703150740ba1000c0d9085c480c4903140c03524050b441c00710070b1810b030001c40d2207000740388100010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 959929586 1250 959928336 959928349
    0x6050402040912051c020309060f0702030c0304141c051e010608060a090b061002060c1803030313060b04060b0d0e0c150406030513021806120109050c030d03050c0415030b 75
    0x35000f0303644819070340d01700c0d9202100391a80c580742c40040c0c442c0100200840e11101060580c0c00400c2c205c140e2a0640382c0a00c16400e501910004801364440814000750340b947c0c0500848400708252100c8190f401c840748100e44440c130300500034001d6171291041120241041d480a04103220326000065655102c1042c1170030f03d102030300c084100e06e4480d03000c08148003440140540024044507240c4540d03403a01006516001f004024100d02000860303540306400001c0c1e01940600c1c00241940d949140842201107a0b82080b101981c0c3c80c0d01d841e15034021810709205d110252550040d2080c1000c0117014808040d041c010380d8600a401000c5c29080396489081c0700d50461342500c84903585a0f42040e2000341100d030000e10301d0000904d07003031035580036840c2d2002001d030b5485000d024081a688007404076011034a9600c0003000c070741c6000044400c4c041301099180028108400341e4080040006049050340c01c2982d6a0001c03000801c820000342c10008a1515403000b1810003123264403612000910 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 959930836 1250 959929586 959929613
    0x9061d03071203270609140a091103041506050a03080d02120f01031103010501060509040207020103060b041d06060910110703150e0d02011512150f0b240304060504020409 75
    0x1c07604040506550b12526010f035806036810342040013481c1d00c1d08500405c541c2280c843c8040642d040100c584c030b513880d400c4070640985000c0c001400441d04000743e4048a61080700d0a1340c8001c009650940180424010308003161801403948050300d0458407881c4941c1e200303d5410407156400c01441846000714500305108400801050300158554240450602d0410314414440e0b45844018855290850217550f4064030540d00142c9a85991005800414031070f000025290008a400500040c00ea02d012005030b084c10300790351143c1c03036a40c18040d2074010a03019035841103206d40e003122540d00c500e076a400a2800300e421250025665100c00300b080c0130718080c0e181c909446a111000c0c0392001c2107440c1001d8243d02c020881d4410030a00f04c101780d4014004c41041c0c2c04000301c3c183c1884101c01d5090311800740d00c0300c00c200c0401405203100040502c01a05070050056100800b0142110485980c90b030101c4501e80f859592903a41c0c18008000048c000ca074007607521004100800d800f0722074040b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 959932086 1250 959930836 959930843
    0x12050a03020706050a09030207060e0105030408071b080c2103040303050f130306141609090f0f180b09030304030206040b07050f0c010f0609020708070f030c08131509061d030712 78
    0x30007039461f0070028203000045e0454401c0c4200000001440d9034400101ca50041c0c21002e5151550350b94903000c4100105c18102a0700810b90030000304840d4030120350030400030000c0395502c1000f0b0360443e0203c61030300070481144c0190414001000402e0040e0300409801d0f1564031228501303540303009a240c000c505904140d5844c1c1d03a86001600401d4000c10041c0c10506200d00c41d40d940f11941030081540103140182001a074032800050040403440e0403041e0a40c2d4111401c0c028542400c80c407079541c03119080160351810102002c40c03200d00000c02100d0080c0e405901805141d921503d90201030351b405080c06c0308000c000c0106d1103000b5032680c0075050a00c0f98000109681081c8140303102500c0036604602c169030301c10880480006d07000c40c211440141d01000b01140d030001c07400d055030751449002c4090112a80010650000d401005080d030030f980d00003030544500590310b00304680d120b1041c0038850100c1c03900140c1d140c41a0140e00880c014010050444094588a0000e40d004a03c80780c0102c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 959933336 1250 959932086 959932091
    0x31d0303071d1c03110307150c05070816031719060515070f02040b1203030a0507020d0906210609020a0201060b121603060902070b1603060312050a03020706050a 71
    0x858200d6001c0450408201c482030628010514940024040014030210042d000450010b541c1014010700798083d01801d102c003074071f440d43d41c1d03070030054080d410f07400b0407491003440c100f460300c10a406171058804940d0054680c46c140320700394209000c1c0451518080c0c00380901900e80400c00c441e03500700d061140e903082c025044070000c04070400c010b580c06600201d1040442400002c081c0c4c14140c1542d058680141e0355605100250021600900b800713441039804c0001c0c201d10400d03da01c004019401210019030400007681c4242003280c0320210040c0040000e0100030b810800035114180d00c10740d0b2900c1000c040c0c811803801e40702204498440d8400c840e00c58000c5007402d1202c0e02842004000c0544e41141481d00481108071074843c68000d100c0c5003100c100200041d92280f1903402140035040b09042151b880c1c00714244905501030860741c0810003080b1030f040710310b914401c0c051b0000b00d030380c00f01c004c0451003000030b008c0e40c0940201207c0000c06a092000c0c901185413801541d0040d02c080800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 959934586 1250 959933336 959933341
    0x9180e0d0509182a040906080703030807030b011202071a07080702070f030b04030503130f0605040c170a1e050a1a06061804090303140405070f09090c1203031d0303 72
    0x1440078948081024003581801841080402d1310465007074080b0140ca25540145286100f10508044c011500903008042c0340c0007006c5a9200d0002e08042500c0c02602d03441c480345c0d22603030b0490a9405050507a8002810324036600902052500500880d034425680d140149006404025003064111854400a032034001801400354040c044c02d000303072001100700e2440b035095882d06115040007600042c2084800000079a0202452010040095000020001d0342155040c80000361800703880030b03154600520310008640f41d01240f40d41e8155203070b0010700080c04841d11350a429003242d500b0003c100742031044010000d0024460311101920070451005031602c01203e40302c080e000103002038080c400c100011889100b210514041d0361404031408a4514070516044000c1c02a2190807491006c020b01804104400428a201aa12503403a2808407a80d105a15401d41d414000c001e085c0b605215014410b10081e02c8486460602904022441d80300000211460110381c40f16244150004401e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 959935836 1250 959934586 959934589
    0x1d030d1d010201060b03060f0a0803070302031c0203190c020309060706050118091e0503070b070806030c0a05060f130e010b0304122a0f06020a0201020a031b09180e0d0509 75
    0x31408000900388000c00c00c0c40c0c00c0c072000d954244005007406e032103046240c1d611401da0791180654800340044c5410350351580b520380b4001c0d5482e00094012500d0011800c40f2010241d46442520300c81d040d40072080403100c100c400c5003030007040b800c083c003005c60108102d070450907103071030000b0000d482c49008001810342c500316404030a8942d0b202950102810284c010001c2469807032030103643c08005034003987c000f81c0ca1900c9455032042c1c20006080c42d000c201041a40d6800ca08036510408099090391034044801007000349a180c68021141d000b001400100d9141d41031074003402851a00c0850070504a84800a03075400030000d0380868003421000040108000c0d030b094250382241e180d810402d01074a001024440c0d09100c51a40041c1c00c0c030300440c0c000c01d00010389064010150400d40c1159030758080c0600a000c4e501200c4030b0404213040072074003600d0b80011400c149625007a41e42d82030942d03092160050413103074800201c05140340c907103141c64900b05e0203000d203015000311525001e135a40150700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 959937086 1250 959935836 959935877
    0x1501090b0313121e0f02060f06031f060f0e190207080405150d050f01050a060c11040c020708060108010c0306140f0f0103020408060108060a0501080d0903031d030d 72
    0x108420106803092090121800703264003180e044640c01144401850600d110440c0c00f5907842c25200d0182c19404074000c0320070382003042101e02031099400d95019554a81e8003004151080d82c160750580d0264401080402943c5005290494002c2000c25056901c60102034402811781140c5100e2880000f442000d9002d41060561030b030301c20381d0940c01c00740c940d100c10865007d68480d040c0201c8580710380405482441c02141c51120180300d0800080c04c0086264000040900459008800e4420045611801449040d003582d03803000c02e4800a00b848814400a400148024400d41c4655140481d4020080c004a4040c2c0100300001401b8005620020285d0f03001d0390241c1c05180c00000381860310b07180d0010629207500242d5103851244840d0700100c2c001d00c2258000e41c400d00130340c0004100240082081030003144024818840c0ba43c89408868940002000f0389010410202007000043c0c002c0710740108240c104240e80c8003142814021a040c0481e2030f8401000840750a00d486100d1000c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 959938336 1250 959937086 959937089
    0x130b220509121c091505040506010605070f2d05030a031a0f040522050102030910061d07050f030138040b0306040b060a050c0709140f09010b03010203150109 69
    0x807001868100c180c1141041d01c1d104080100308014000c0c41d4030b40c4141ca281c0c01c48010941c0c44040c195028551004013401440e0598003110700b806110000200c240c07040302501e11154100700c2000342c018440e601d082d9480d0001c050384c0200380183e400140901000482c86085a000e0f002455640790480c0c0000c044540030319603080740c0b070008441c0380b429443c0c2000344d802c0c40c042030710002220389454144498040c00384100005980540039030908104064004c0d502034401202203800280100f02100c0039180c2074003400f04031210b00c40860070f400850690f543c0c0c0101c16818103078074104415845402c907610036000303d00e510a901d00b101d210354000b90075090001c1e52541b50010921151a40800c6034452071252041030b4101001189041c1e0700d0b0b0b8032010310040024100c540e104445000640300783c014088128040c000c8001c0086c600d9418000e51003002110a1414019514102c0042c3d0b502000b8010f00341965a80180d80341d2510248021800380e011918040d0307504104000041207400d01d0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 959939586 1250 959938336 959938351
    0x2506030c02030a0504181d010c08010b070b062b231c1d0306130b011406031627050a0602030408072601050a061403030711130b2205 58
    0x100030076000c10758024140c07000d840c1222140c1c50000d6480d40f840015013035034007d4400782601012103900e000f03415403240c035610f0b0300d50301c82c45050380e6070390801c11840c01088009003140d80c0b0400000c40134038008910500400720f04c5d40306105060400c02e200e8101101d0740c403c982140c0d000d00312820101c0c070010720240b860480340c0105641c80d80e08070074070380d0201c01075041020300800c2640c3c41d42c3c002c8001e64180e80003d000d01140c0e0b06207052403036050848000401500c41d100d101d0f0003c648800c0010681507039840117809540b4540340c0307640c070112010f1140d071100200310800c00110741c2404881c00440c203070203485400d0002141010100704014420f07900840c02c0d0340c0100410040340502080e248111400d10400211424040f03d21034541d000200701001d0725442c01d0100b06a00740642d20840980350040380021907412100700345981c80c403500c00301074040a030442d40144c10740380c6458241c6010644800c0411040d4400c404508420b40a281090300740850105082181c489841403980c01582e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 959940836 1250 959939586 959939593
    0x20715020304030e0f15030c0406091d010302061b030c060403120207030212090420070c050a080c0409050c0409030507050c0f21070f15080708071d032506030c02 71
    0x42030fa402501c420016035640d030180008003802002030b075418a40640c0c0b40001d04c50f00d60780e89440000426680e101e030040c10041101d039540490201081510145461900c009101d026400c54080084076080a0354048940304207501d0040c4c1c995041c4090710403641008003d24407410189005003906901c103140b00c00c45403040c80f554010075030000e41c540b20500b1000c1c0b0a582c43c203680021401600340400c102d80c4a40c104402d8218040c0c0000082080d68012554802c1540d04d80301080200d808512901030641d03c6103d4004d50740c0b0b01607024002c803d12460481d111380e1511b00110781942e140150680100e0404154201030003014000c602080a048505c501e10130b00318000128070020114440c2140000440c0008401204100c424040c0100d041280521a9140503070030381202d000080d900000c0100f00883c444501441c0041e004444623201d03000c1c04001386000300300d121440c5c060380303a040c072800c10450410410000b418268014003040402c20030305261014050300c1442c88110115407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 959942086 1250 959940836 959940841
    0x1212040b0c03090709050c09042903070e0f0910111806130e040510060b030105040e010c021b0d020d03180f05030a062409020417060103021309051009060207150203 72
    0x40c2d012414109461702d10000082d16160f00c64020303840c5c01118180354100e490a44183c0700301c20202404090814600ba0540e03a10000d4414140c850105210303010010040501084540c0c02d000700040d0b021800f142141d0907100a04500020766203c64880381240500041010101c21210940d58582e401642d007249808420380d02c4448071b40c41c3d407180805170300d2000041010484140b0040005004441d0280b10840d2920034566103a070080c46802d106038680250159560411700603820800c81030740152810705030710040c103001d41f60805040c0354041c0d0305031440340c01a646d02d081c10041030300a50b0b40c40b044500540707000010b00e00315081148a10707400c0b40100482c0d44d00103038241c0010b81c8010003291501030040014042c541c0000642c903a25050000440c00000b0703580500221014502c0100c0001804d46005486010a0101a400c00c003040000d188240792030308500c0c43e66125204980c002080b03200c0100c01c4a50303030f09089074500e40000d484d200b0f10070249a940046052001c0840ca1030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 959943336 1250 959942086 959942101
    0x60315180c03020418050d120c1803151d060106170108031c02070f060c0306171903050405030d030b03060109022a01020906182b080c1212040b0c03 65
    0x34101c40c40000d1140b0f4a42c0c80c4401c0700c0030200b40d41903410340c0c024204d1f8801d4120301409003008a196045580f664940310100c0281c1d480380410880221401e00355010144c150348410701d00844500e0380445081e1640b161405c00c104c4102e802c0382d02d00c0440090000c6505140d00208014000b0a00204003010440184170f214400700441d90800c211070007050b0300001641040c0068080c0440243c40e200c01b0700026414030071507810401d400126560108035850701c4411312441030754150740d841070640c0203105210188071301c03c1c8184815070003410482d0805540d6000a4070f000a070341c1182c0002503d81425001604082101ca4050100d00e0000c0d0f0070159502c0d42140325103841001c520201e800d0003045034040c2c07000e5044481000c00a00400d6407800f90103484940504648025800b682411411101604040c89050040e02081c84a00c107030110b0398507240581c1e0000c0102d5a414000e01584017400f64401c00141200410b1b03026444140ca01401c0c0444800301c018803840340e05c00c0410800c03c81 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 959944586 1250 959943336 959943353
    0x70504090b01200606090a06060e0f0d0b090322050f0d030c0204050c0903070e010605071b080d110d08010f09181712010815041103030d06031518 64
    0x196094000001160101ca80040340c034501101e48458010380f80c018400301c54100800c213280310705020341d01c1d00348680758000c9071800c992041c410000040c031070700d1401c0b095107131100c04544030240c001c00005e2072580343d89440c01c400005507036640c00c45e0300010b20003015442240a5002030318003203140294992074940424150344803209654480c5e43d80088a508150103080c40d01195a00a001001071745003071601482ea0380e0165548038400d2040c02800245548030400150580d01d40b9543c0601740301c407a5507000c92071000468003080c02103a040001c648010104064200c0c003801c2e9880281c0354508005242c20702c07001c07003400410440000d005210482542070340704201d4240e031100042404126900094600901000a081c60300d0324952000407000e64000c0d2011320401c070030050550340d0b0741e004247d840000980c1030030107844100009003c10380400d0801070004018040e00d10307021040b04544200d07a56508106c0d0148a649411903044020703202e18010340903160300c000441502e41e295050b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 959945836 1250 959944586 959944589
    0x112050618062101200304050709180803090a1a040209181e0c040c0c0f02190909060e01050912042d06050a1209080d0e160608010815070504 62
    0x10122008404980a82c55800d80550b100742c031040503040c91660045158060170080030041109803510005020b4a80307001d04480c003640d403003001043d80c9490416a14040d00010002825a440c4034400c040418201d000452103100588090030b0801c09900d41024410702d03900700060440504c01c1040010b1310354030201c2e40c000744010451300c0e418056244582c80c0019001004142d080550020030700c45000250089444d00100c074240011500c210003200d5a0305014805404c9110441c20740000d81480548030400d00308050b04541e080e911100700d2405d94410313082c01c840d896520880514124400c0c0308503904007100b80060904540c88080d1010507000f18082e070f0300754280f58040c150303103e1040000601d0400d0007405a14405503641c00c0907215402c00008040480c52900d080b000446403403107280007407a4850b500c1c50422551100d41c0004010141140303000f8850300c02d240381c407005624800700003003a4641c0d40310080d6050559440c2403213402400540e181c60024284080c1c42e8100c0c05450 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 959947086 1250 959945836 959945869
    0x130804030b0f011e0320040608010e0303061002150a02070c0f06050304050d03020a0e120c090405100b03030403020a030b0603010605120d120c271214061303020c060f0c16030201120506 81
    0x9030300d00d46c0c070000035004010f643e2061180e0342c07800110041c0e4100101c00b0710300c1818101c8210104414070442a1303180c0806400a1001c020904c000820345030456018101c41c0b402003085104e00b5440f503110325030741c810070782000b404a08007104001c1000030800606045d800d0510f02542072110248000d020004120849442020220f4521500c1030b0100a0f110b40c1d00c00041240800d070078503061184d29a00300e00305003007109060030324081c800c3c01c000044404490f0b028204a03456440c50f00c400c00d6641d400b80c101035055403a603078000307030907561782d0054509840c80e000078111844804a003d41424001a00b100c0d182c0c0c100564089210f8103c400d4000e000b00d00082503126015140c0c40b200c8000c0c15811290201c03803000103800074408510700080180d068101202c40c41d0300c85405481000031034190050059110312000c0c810b5081c804080d1030340c0102490b4144c10040543c0441b82402800032403803549003092501001950780c0598604c8064042c200e08000302d0818101003110700003a0091074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 959948336 1250 959947086 959947133
    0x60c020c15160c03141e0309010305041122060501030504021e210331140d05030f22030c0909030e040507090f0501090b03130804030b0f011e03 63
    0xc12890120300b24206107260301c0900c00c0c800a8680c50400650205031048052074030512441d084100301e00c50980b03246107501c0300218113094140c0011006043c0050081300c1528451400319070301d40b1031071014210b0303a0340340385d070b0000310109996414110358151780711904041c20301c02403201584500645601c03040c1d1006190141c00048004544000640d2880450700ca1a000e0125040b140200117803020a0109940da003400c600030000490440070446000284140b141c2d0400003115035038a1540c6405028020742c880700c0c01074941c141175420660f82c060b6030680005a041d44d1b20412040310415042203240524043d0950312245809566030003150702d610f035941e00d40403e250180c4036060380311030014000c5c0300a1400030401810289540b01e90b00e0002c4088002044030346c060880030301501e2400030342505594a1807009111156400c00c140e8001000700004004a0649507949200c1e140c01c404c0c0c581254541802030403025054840c130358000b40381000034800190728000c0d2068100d10042c41 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 959949586 1250 959948336 959948347
    0x30f0f02040515300d0503010e06010906051b1f02130609080a0f020118090b120c1e0d0609050f0708070e0109090c051903020411071a042d060c020c15 66
    0x34200031000d001c081126119511705080215804401503068890382d2031018001d4171800015140054607015010100e6824080b060907819480e1070300310042030314811101c0504404550f107515520704800820a41d400042401020282810050007007515242c4800c015140401541d01c4d060034140c000e050040c40036186003560310614801c3c90b502c1300883e103100d4182c0d07520f0402000384219054079000f00c40341c50f1a00580d40d00406c10007045c0348007604500c04101c82000d0700e840080001d101c035038090712540032031000c142c07144a103212161160004040180850101324500203407540904215444540140405086039680c2c03411101c0ca403201040b0160207140c00b4440d58050f030800c0d0340203020684004031003800d20b0705600849000380e03002c1050b14007555030341902c2d1289481c0501072540c1000042e120282c1001d105501600483c5503030416440c00c0d890418403c00705080d01010762680804400b4010300e4803403164001210300040100214031800b049040c06019070544000c0c002141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 959950836 1250 959949586 959949649
    0x80a0c0227061212190e091510020a050f0106051903030c03030e0309042d060803041203021e070608010e100b0c0304030b01080d0306150225030f0f02040515 69
    0x2070a01da04e844d001071544400c0384034509011240c000e071101000596000800c4c06900340344080f00d00440440001f6004070350000248074020700d8441c0101f086104500580300414802e115041404000000104081e841e0508009500c40ca80000c0000c450303c0b4001040000d40102082d40401d50505010540040c0c80f4045419806850407080d0810f04229112010059280c402d2100c0d580701c0310034107640308001c0c00110848003a4060b042c517a52003000700748003048158480b840034501c2881107442541c5203003c803001110961084944aa000d46c10601c040d940281d101c502415107044403444501e0135440c2e15802d400340d40705440400c080090b6580f4200c5050044801550300610104100d5946044403036464000081400c0000c1c9404000701d8040148402c3c02d200e41d00b19402490030110160b8032520000890726007100c040d06e480400400101c022001081a6000c4d054a62103014540144002d07a54000c0c182c0c0800120704c4c1c00b4041c01d03aa0450300c10382c1a080c3d40c01e207150714605070b40b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 959952086 1250 959950836 959950843
    0x10c140a121b02150c070f0b090a080711030d0f02060f100510050c06010909080301033203030609090105010f0314010e03280302071109060d080a0c02270612 69
    0x2e950840c0340101d18100740e00c0d400007030720600c0c1c2507540e0400d21140d69984e80b1440d103004134403004146411501ca214041408100300300d8004000360207441c03d64101e9a030381d403550307800000c080319030950a01e502e508625080c004071114441c14203040b0b05040ba2410025201c18008002c2840701c201c000c00300f510a0903581401d4040d0901811084c6000090741028100b6007050031400b2061146000110312004c96029854116a02c00101401c50342541d80d0b44980d21207031584038488060001c1c007019036400003280405212044000382d40d40781444002c1c003c4042008110360745c2681484010008140740000007003c0360b400004102c0c0d500c1d030f800000c1c0c0c00761010402405107440080713200c0003402070340622152444116440c03100081c0c0800e0003582a03004900000c0d04e05000c803d079018a9007001e12809510910042008051104580d1564202d400c4941c00ca00080d4040c8000401c50802c182038101c1001200c07568010030450000102c01c40c44000c0c5002c0c080c0921416200051300e080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 959953336 1250 959952086 959952101
    0x6020a02120a2c011719110d0b12071401020c0a09060e01150807030b030c03100203070e04051302150c01090f030801060810062001110c010c140a12 65
    0x11001c090b40c1d0418040020030f200035610101c0d2109520b0240c002c00c3d8032681e280c3e61003005040c1c46400550204502401400c14001c000701c400461481d0b00d0f0a101e0024459192180919203007280c0f1000010081b104650380c80d200c00d80104030103040760114107800180101100c51003a00e07001c003038030401c0040742803101c030411694116a01c00f101042090840e08130701c0a651044519000c0c5a90b02c00100201c512620016004940180301140c0030903c03a4000174403008000e01102c0701103141c4404246000da452915420450303000c414400101d52055982070407541c04c132014403040c100b1060311121030752191030092090401050140c0000c0f07126064440c0d03150345000130881d4803a18280f40300910305440c01280080d00400000c02c0150041c3c210302d0054160000542146d400c0075400c2da00814000d140d03055080108010b0070b50304101f4000d00b50b007807032080304c10703070310346040ca4080340c203507124542c10b5401e202090315200b100c61070084c150b45000702103250100d49111000805001041c0341c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 959954586 1250 959953336 959953363
    0x104b0515040e0408030a0b03120a03051806090c010807051e0304020a08100207030f0804030219020303040f08030705010e070e0a1802090f0601231c060e0126071206020a02 75
    0x1d80b040000388801d28001d148600c0e284041400311694210405071150920a18002d60000610407048403d00c254082035100840580d140f08480200e00480d01d0700904030340b26070301541b0484980c0280d59021080c40e0f001300043c00c1caa030400381e9494104181003450124074074101c2020001405658130341d0511401000d4000070303a1440346481d08140c0103523000300810341c04500d040038442003d61192200c94800c0d130b015030140c07400064540c09448481140300060f82d0511060001150805441501034010300103407004543d646c00c9071038402d0075502200381c2c404503604403002c10040381811050031036210500510004403030b0081d1349510244442003030b0113904040707400304001d000180e0301038607401100e090302c45402210301840c41c0c40d002e245c4003124041c2c02f50180030054502c0c0070076071104d171205083d840110b1000e440341440e40c10500c0980c06458110401c02c1c50b903c444001c800d544510b80c0d5001c3c080c01c0b0440c200b16860704440c0303400500a04480c0d0004600940d60320030300a0443c010742c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 959955836 1250 959954586 959954609
    0x102063304140915190f0b060307090f0f1d18060f01240917010902032407052b0b040f02041e030f0b104b051504 50
    0x11040d0802d09040c10449400e40c4521036980c06000c01002249110b11503070354038400520030541200700c140a4481a1000070300e00d40c60304040d030746907502c1c0c2e80558802c5003507558291040c0d02c4c0030110b810400c0d146e804049860304402c070034082c1500b40740c10717004a107048965144281d100c0c074222148a022200803100503006000c1449104007031006954100d42c01140320001d0450100141c0e841c64005450f0b00011030001802084005440101a90710722104000007911441356000b290904000e101002202084030762908030400e5034000103508554179142c468144501c440d400c036080c0b45100300303142202990503039010b403460083c1c121001c06d03480500140b240e49111071901c8065086801801008503c05a408036181150034182048a42010b0903820140311a1680c4000c0d19002d40603c03005025003001240b8405180130601c04e103e0441e842840082c04004100c051a18202c801002050313640e480c1d42444000880c064262603007140e9500c5185210300751600c1310310455200782e08200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 959957086 1250 959955836 959955851
    0x1118060f040905210d110c070e10030209090706031d12130801020a03151e0521030412030327140f0f1f020f0d09060902130e07050102063304 62
    0x105400c0504001c0c01d40217010321402402e00c002c0390131030148943d140020351001c08200070140c0311038580307504500c82c07034070840c10542c07a84c0100c3c440303c0e0101c40f10304550740240400c01170545d061003080b02000e40030f1703003207840c0c481601000f07901c44c07103c25030b07544a5000c086400c15143c0f0294014030010183d0800131547d070460480b0207405824040c80515000003004030002e841a001e298215000003086505814213003401c0411003c40305814480b024815414201e1040444c100014005800350210301c002080302c80c038004059400f401c0326841020400400d01e2031030541d2883c3c016400d9441003283c1c0c041d00405441a1800540203030841c800d1255089070600c42c500030a803030542800078102130500c2e000e018441d40036842a42101c0b444460100400450745400e5030004811610448002c83c10354055000100c16148240c5120400f41c3d0304c007440c04440508010400040200303002800403881e05401c1440828602800d1042031042d0120308404600103116070340c0103000007442005400c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 959958336 1250 959957086 959957143
    0x80d0f0f05040b0f0903120a090606060c0c1202090703050a0e06100602100204050d1401063c03021003021b0322060804080403060915091118060f040905 67
    0x1801c00340c40580b09042d000c0003080000c0c900b8404903104403901030056203070000341c2c030030b40740980c50003410190020307565444400014214011a00102040d550740c1c8580509400c05079000e0b031942c0d01ca00c1031a03007000001d50050b00c0e007a41c03603a40a070361410b0001b66544d505625a002e0550240c1b5050a80a64000c018401c2d024a9100081e1505036086480c0384922101c1c6808901c0345015003948510100c408034001500b1215807072503a2002ca0020a0381507484040c0514004078444544901440350780c002e0f92100c5400d17038140700a603400c02112034280b55401044600e40f5140750700c400c0640002c0c064901022948103503049404d542c08803507451403031240b0000c48000204010b05506044100002c20310304c90b41100f405075811404240ca850701d1951036000400340700008903180705213804007070349035186845070146a0b4002d4829502c80a800c00070040c505400d6030f90050510202001d11000f40c980019484100205440c009a514058105103141c0b50680081d1050003e000894001c0c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 959959586 1250 959958336 959958341
    0xb0d0803040f02130c030e01051e0606370203030402010c03080a0612080706060f03050601090f0608011d06070c080906090a050d03030207060501050607030c2a0b090a0b090a03080d0f0f 81
    0x1406511b95040012008a143d09400c0c4c40c011b90718a4490a446c900305001111183e0300d950b0801d0004000d80c0c0b80038096080e980d8105004242603001c443c080e2000b80c905600c1200d2808030b4000e0307101442c51403400d640007034403900303405501408121102001810b004101c0d1b125001a000a06035a80b00b07401c5031030040f60551000d00200c80c510308080d000554802282180f00c2a2a4490302500c202e07820003864000800064200181907511480c00092a40080c4900700d110b081e549004610b90f00c4141e100da20b4400040c02240801409040c040d01190855055992207002101e0b000ea83e40c4158000644000c00754205561004100d8848003c02d50140c1c01400c0382c0d48035a0b01400706030398034000c02401d401502005000328548000300c0000651100080d000590701e0b800158003610461840b456284040e00049111130300001c514010b8607082180d00b00a0140e005600e01d0040031a0205010302070510008000210202d2154100031142c0c2001d00d501140e079a08010910303103030034810b02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 959960836 1250 959959586 959959601
    0xc09090b180102040503060a0207021917061503030a0c32120a0815010c0c12050f011505100201020d050c0306100e1c0201120212010e09010b0d0803040f0213 69
    0x46007040c00e90038405071030040c0240d07030450b0780007400f50146546034007064000c0d611510003280c0c8000d0300c10080d54015202d140c044c01074003407100001c40807103c0ea503c251401202a064800317192070f40c0740c1a4040e41e0000110740c0c2a10040c507025007049028905803150034000360f10125608210807034a110014142c02c01035010300f20100b19000641c80a020414034441e00c44032000141c14030002131405030300300c26050700280e818500b400c9120030f1a103581a060081d41c00400c8604042d04803201802010440b0b0100105804000c01142e1219012540247e2051003400d0083c070000540707060443c002e606807040a00d100005110f0f5180202800b40780f43d1088524501c10300002d415100c59600c980a885c0700e0000c0500800a5008640781105a040c40702e10200d0400c4104c80c80e08008000e907001808202140a280100e1541000080f00c50040014180402a89001540f0b04a660f5607000c8201c0140c100c90070540e65201c0d420040c5100c00d0341c0e50043e401200c024001003000c0c0c1d0562184c0d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 959962086 1250 959960836 959960851
    0xc0d05030c0d0203031017060609062205090106050a050a03060c11010f061503020901080f0903041a0c070e0f0a0c11160e150d1106070b18070509040515040c09090b 72
    0x46e03005031100021205001c40c1100508a40c1c030800c006400f41c200504c1c0d03a60468801054140500880d05100704910b2900c0c2c4400455038031981441800c035002d0159101070801180c1505102e418400420403007051031002906160f15007442030720540c001d88030300c080700007900300a1082850500c16900a0501d500c41d0300401c410300542daa594070300c2032081c1e4405200595a16580762250301501500c240007401c96a51804100030005e003106920301080100943c07203020b40d4403448460b00f110b0130b081d0140d120600206070a001c02c005143c240d00601e80c00714400303100041c0d101030944216441c85121301909868800d00c485561414256101c140440d100440c07808865600c1f981d070405d180d4040400d4503040b0411204100008503501030340e0484d003002404660a084a5031113800c001081920b445020030b05544000300258002c2c481c143c081c00b004d403402c200c90706155031960358031003400d42e1551001c546030300400c04200c8900100c00040004282c14030801596061a81c42c3d170100b03441d42c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 959963336 1250 959962086 959962111
    0x418050303100b180d03030216030320030408070f050c0a08011b0e030307021c1a1602160e070909020a020c03070906062f06181e0c0d05030c0d020303 66
    0xc0c5903c81104540049940c0c080c5064190f80b51014040d001400701021000d0680a1020000361048200c4003d0400c0c0241d60100d5030b440944140c1070409103e141c81242c0d0801042040042a0050200c60070151f11030a142ca00c00c009040007400c00c4034680c0502d902c00b54205000614100541007504001c0c0440384920246000900685044c42c10b2508076425800c20300c410800342c60310241c144041c03800307010090303a2204036945105201c1010140440d18207161030607c4444841c0d40348500c24188180002e0448005844120107181d2491007401c040847c6900028007285c41100907400401c00e18000355101d2050900c06904ca94a41d5603c2c3c0c001e100741200002c4c2c00c9910b001c0c2c3ca080710f003561103009000d06008552015903100f003079102c0c682c13800a0307038100c3d00d03010401c00c0c80e103c3d40042560303000707610b100c041007802c10010700c1e0151801602c5401040004001055154140381c04503480403d10a03149000d074154020a460f0100c14050003608000c007a030080700440c40340c0108000c0307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 959964586 1250 959963336 959963339
    0x1a042c0601030c080a0c03060b0c01060e07080103020f0402030c0d051009110f0d0b0a210c0b030f01141206010314060601090b34050115080a020f0906041805030310 72
    0x4400f1210303401008000500c2440100f026003a203503001040c07000c81c034540494a55101c802001942e403150322a242c640e951810304110000c2c24001c0c3c60b80056a43c0741020440d4510740004800e40b1314004a00d11865000001c20b011a800c0742c11a010362203040c009001ca45051002120407160910030040b0140c28068004629182c04045408240c41017004600b0321003600300e410000c2000d28070032a00161140340202c3c8030164007007001003041d55003590324007141492400b02400c002550080c0d0581e60248140004038240320701c0a41984c00b000d650b51301c0d034500d0074005244182da449070303025580901400407043c0281078581c0c0d01829820822140c25884002c01158086210300c524000107800b400503203c0b0001c005020b000e0300f607500c24410718181c20b51032807000c000c02c00401141d00381c0d544c100c480405103520114800401ca40301c0a011464603940201e6601c4002d115034600c98047d0100041c01c0d551185e0214450503440201c80300701d0b40d5149041540ca0748241c031405a5039184400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 959965836 1250 959964586 959964589
    0x21207110d0e0607060c030b130e010606080103050c12011805330f040819120b04060f090906020c06040c30110310050a0c030b0306101a042c06 63
    0x7092400701401500c110300d4031815461707100040c02d02e07071180d004140d200c4040380040da8a58043d4004800305040000b200000012441d0071658550300c20020b010340703100100041200072036400e100070010360f40c0b9003824450f034030707128010b0140242500403a86809411401e1120000780310001c0d0000d8101c04c084008856040c1d01d44000752070b0041021214140014003200300082d006400c940706580302420616080b42280e000b81d040c1640c1d10004003528901403003102c450142c0050080c095408008041c2459110880b84219000b806155611000711804001041e81180d01c014107560130f58105040c01c0c81c0c1514001c006100d030309859040328101c00103070a04060880b1101d042800300c00c514004a41c1c441c0080d000c81460740364107014541d0071000b07914240c001c580c031800c0c1102c80007840d84203820015003225214bc402500039441141000309103550800003c09071000d41607a100c1034400031140e0300d00f621444c2c000859072000000c0c80c600c0000003404003190039070400c03202d1a01c4e9036201c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 959967086 1250 959965836 959965847
    0x20a03141201180e010203070305060108160f050c0c0406061116080604030c21020f1603081206060d020a0804200a0306020a0c17070c08070608010612021207110d 71
    0x11400c12030700580010400300c00d507948140d42d00320350280c012800581d40e07920103089030030444540c004240caa2003084071541e44070381c6c0f03240e00c50800e040d1004000c0c01305a0041c82483c1c00e070481c9083c82000500110740c45c0741000050313190a002001408401c0e00d48000820244140413002e030503200300c114440f042c03591054440c0c145d640c25070040802e6130322502d040303828400c2c941c02556056511140b10015003114140ea290028880d00203085074003101e02003a00d4404001c0e10000c480e4034049003400014912411208034030309803d50b10a041d02c40c8400a1080e21442500503000ca00c001000100382d40c014220305d20860143c00081c00c041c91004030a000d040e681d00c0b20720f600c008990410320002e041d075409410b070420589040300300c4a855540e0051b0143c40311200c0c400c0104041740903004c015030700e0a00c4000e00000000b60565518007031000e4008001070050006102c2c072000d101070400e00b01d905035100d54104544107501ca003465140901464415032501e036541c0914500e00c0310850161 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 959968336 1250 959967086 959967097
    0x40803070b101202010c08120f04030e33090d060c08100e070309030504090908040806180d0c020303070b1f0801051e18010203190b040c0c080703090f06020a0314 71
    0x1502070850f400c00ba41d0045501d00e001c0c00c0100c80d609014401d00042100d11001107128034001d0054040500b49418043d00d401001c00030307a8450b0b036000d40c804006401c02a1036840d050307a031610039000d081d508169904c090042101050300081000920014040660088480d1806544500249442c0c1d07840c2c00303c801200c1d0150000d805c180d4008940c45500c030f5840b0058260081c0780840c24a6241d417034010581d0707a0f800064503a507070081020f0100301024008150040216101c0c403089066189401e600e502c18091610188541308030048203540f001c0c0115241c16611201d1405280b406840e00c4984040da048030f10402c124005020400c48414420107000740003c007000704843c0030008840107111001400560484400d15030022f05020900144d0300031f2005260701190700758075562003001c0341d456040a502c43c1d0f00713040350904001d03041645043c000b50000c10321550303a802d9003020349940c00940e105984401c1c01c0040020311a03130218500c050107110703585030041d070030003002c0c2c10401b400703030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 959969586 1250 959968336 959968349
    0x1d07061d01050307052208250509180c04020a09060f080103030806120a05030f09120607082409010b09030f0f030405060705120f04030209070507050616030908040803070b10 76
    0x2003011509050290001d04030441d0540340c402c2046c61409160704940a02d07500c101c60710b44c440c40b101c4515404058108200d2400104607008461400300010007540c409000d05080c0d00ca0400803940300d402c1400340d8141c0c0e920280c425540e4085100c03005090642c0c0d4410345001078005494a5169881001c0d018100c0e90113664480e81d5803a14810481c0c0c011019584104520030b140940300042d0051024001201a20f0407180c0c403030000b001800100c403400c00d50f002d100e4001c03904012065030043c2550307400480e85800e01c192003d10304004070001080400d46607010440d0400028810069030041c20b504600740c0a0310322a4011101d982d0381ca800104124009800a02c03050100341041006040100d01400c1103039000c0003803d103642c00ca54000c910456002c0c4c8005014015801c20440e0310360440c041c1c0c03078074a180c80e489413500303625043c0151250b8210280c00c200440e8030340c82900f10511940c1c10000c002c0d0342d25525001d142e5280d0100d081150503414240006010305400100d41c0c5c101c500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 959970836 1250 959969586 959969597
    0x1b0e01050f010f0f051e0405040c2a02040e060906090c0409110906030a231203040f060902030f010f0504060b011e2607030905120406090512011d07061d01 68
    0x103a01d081c3c40740541381046004004060180014600d0100002013a04800c1405203503110700701002e220580c0c6182c80148244681d01c0c480c0513860030b512000030250700f0459406040c04215100080107001c00100040e07091164009120020001190391070140441004680c251100102030105403980c852000c1c180300e04903040c4c445903007460012540c0c07203c4010255810041551f80780d498480e0f07484101e2011030483c2801440d48482040401508010181d0040c01d501d02544c0b5441b0ba40020007004200720707101c03498501191800c1240044030070340f10300288001c4005149100080400b11070540300c09080c07407080e20595000360144071840c419001050203500074000240d40660702c07290a40c9401036240642c207201c0c1644944a800383c68540d4001c585202a42049490410044152401400c00300020070040c1c7d00024100101c80703055400250b1000d03d46d21041c01400c01c0f40448600421000300c00410700720118941040d10320030345494142c00c942c0450003501c80c2c10b030080140072a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 959972086 1250 959970836 959970857
    0x17072307090e0f07050a1401051b0a0b070f051c0f0e012919030308040812070903060515220908040306060513060e07050d0e07031217090307030e0d1b0e01050f01 71
    0x5101e0340080c00b20b4850040e50320a690401050707249058440c0000b0f41743350b4804000d0001030b40c1e2003136040c000305c1540d14280c1d043c50364220032400701400c0180d54500042d6900d40c624108c94075600031482039040c07a4003c1140040084010b10030076182c0503012000e001100f072541c92464189800344a21002c4012182c801d4190b9800391840400540300b40c8030403409020702c0f1107042c10302d000c9074450f1906568001e8214a1032501006443c400b40c014031040c1e1303001e20b5030503640e103c1c6107141d5408107ca0000c1340d00c2c00380a00506000f400031440140407000c00007030200610400303410543c00c845054030040c8009074084220070403105140130b1790400044500c041810a845003025215554110350b000400d0803054100c80e282c80d80a80c000c4070002001203100c0c1c103041e081443e907460703102c11101d1000030785062060b03e516881515001410b03c10a1070f207021003134440440e0801d1f030591155070b012002011460304200903040340318401303018100700c002082c1802d11899000c000071040e10b034aa030b00d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 959973336 1250 959972086 959972089
    0x604060b040f030b132009150312030705071e1e17031512010e160806044110110711012a17072307090e0f07050a14 51
    0x40e10b010f00010040c140f00200170020032028500c01e1062a040001118001551170511451030304c0101b00384407002d000703003900d07a80b81c4000c20707004210b551140125a907a51503032416510b5016000d070141100402110f100c542810049076110b129004006d42c803030600040f16604141c00680d6001800129161541c25045035010040e43d00090895544140c0800c0c0c0c50104030800e480c0804001907030b4484843c59180007040c80310070038074144503004004141c18085c6a503503c01c80074200910321f4134218451495604040310351002d42140740404001c1101890b070b0003407284e00c6c0000f041600e000c0c0b540c2000740f039a080d01c01d514495001d0440a4105403441d02c0f078540022513803004070f051010240841409001d194019600d500784040c0300e078010805400d249440303074018100611600010407601000c56644280b494280c1a51003000810b403a03200b030107504082d40b5500c9624080c0c20a061214902c07000314200e01310314180340813220300941d10420030407050b81510900220404940892081c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 959974586 1250 959973336 959973353
    0x81009050318030307082101080c06071403190f0201110901090302040b040b040f0e0f0d050f1e0a031b210b01021509060601020d03020c0615190e0604060b040f03 71
    0x42c104003d09071380c103007840e50300d0703001c0030358000b4591460486800e800c032110072003115882d90141c6148401456110102002b0a030288510303c0c1c090020440340486511043c001c00c1113809940c50501c02c4400ca141085000d0000c503140301d0514007550030800c480188909000a44400c81c04c141d407021a02c038615000e11004020241849400646664490f04035460318000c52200900d881c0c40010303c45080c2401e2400c00c5034050403024580c015292000f6101e0340902501c072600c00b600c410541e2840d008d01c25020038580c2070714041c2940d00c040788011031150190700c0004040755104184a01040403c8100c03030b00d1840c00204c0b070b03445150310781031007202940340c1c42014a0b010600480d5510200c0c9032000b14990790888141c6929409001000815603046c800700040c4001800c00b13500300480510180d4907604020041034400e01c00070400106030341c13a040300782400d2002072021500252900a908280181254800e010710304000300042e214801100300c80440300350140e4040c10506503542c9668 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 959975836 1250 959974586 959974627
    0x114090a05060c0109140c12030408060601030b06120103050d0906021c0f031113091b0c060f0b090f04021c050a1103010207050d0201060801200304141609060810090503 74
    0xca5945c440051000a40402c005111aa5480010f0a0a5000c502008440360340b619140748107810a00c03042105540000e54140c00802c00d003008075070002010003240c21402400c07041f09a410010000205000380401c0020005095070b41c1d55542030344805003aa9586540c0707441c03250500705590740d00000c5108900da81d0712040b0616012601c80500185100c0c2034004019190011080c0c07070040291229602c103140c2d61040708400c0d140c2c2c40c501280003504139001840042e00140e100c40d002081017a60f0303800141e40da00300a041320b03654100051500300e180002c460480c010502841d042c10440108140031501c503a01c0002420792451036a200c108400c01e40d00c1c0c10383c1564007800b211000070014810064561101e13400001c0852030103403406d0943c2d24103070030020000c203406081c20452250008495001c3c0d04820800d510141030302c24545000705e41003c502d40b40d860a600030500c504250481d008440125040b140460860710f446000c58940c1c41d0002c10700e910070400380d50600082524041b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 959977086 1250 959975836 959975857
    0x306180402030a2a06120c020705031b13060e0f010e010803070201031a0901080312070e01090603021623011406010c021c0203030706020318010603051f0f06140114090a0506 76
    0x4201c0207013007900c00b00507109805c0b09010495060a180e2266868422018004050320041c00880d2030103000c6520392180340075130303500d00010f0030302c08909440d50f5100041403004c0d10030400150340d1b80d40c00b201d40e8200603104610150200342c0002503081c001d810079070607204070f500618074200080d8015001414802d03c0a030ba01d51a84030510502d64032280518000c0040d100919a035649a4007101c410f40b80c000c091000b40900540c180d40c1c60b2360300160f10001d56440303040060b603604007220205010100b2040c0100040c508408122804a90701d841740c288400c00320007032000d030403013410b00c0b00301160031111340c0c0c006911580c55201500d00010541001011201106668003003600402e0456000c8401a29907640010038407003000c4143ca0050104a422002004071a0541c0d5801e40c55840d8181c01c1404180c10034840350a07102594403051921441100401c42c20390b4030b940c91b820914603c0e41c9240072481c81c44610001040c850100c41c44014000c0c401c001860030300c010011b070340e0800e0103a031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 959978336 1250 959977086 959977133
    0x515090406080a0b0610080c0304060914060a061a04030f110a0e070305101715070e03030d0902010905090411090a11120f0a09030806060922020306180402030a 70
    0x2644101c02d003c941042c9018280440062410a0a001e00e100911080108021652081102415800003641d403c5039200380041210341c41802c14280100d003103041610703c3d0154000340400061150300070002c0f07070f101542030810307140c00c840240b80c1405503101c06491100e2803541240000c608601000540100414250001c1d0322138a1900341c0d49800c4464201195a0381c041c0b06001c55480060b81c02083c01c42c1034404006002c1800e583c4840041c0c26089c00613006d60089001140207000c0130358420405012280c450144d104030a01402da0780c50305074007051322004041000e0808954242c401c0d90040101080030804000303010716404020441d081041e41d405108080c814040002d091001d42c03440384801505010201c401510009411390740e0700c528000e510b100007078110002e558000002c44420b502e458480000c603007914220050706040001150318281545c10580c040d5002c2c601c1540e02580c0c0030307400040b511140e001270718040d503d40d0180c01d000340080c1c4008041070440844281c01c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 959979586 1250 959978336 959978339
    0x818210d140709030203010b0a03050d111207080319060503030f07061e0504061a0f01030b3f1911150d020403060b061306181a04080f070515090406 65
    0x70381000c0701081d1401c0c80012004441042903107400d001e0156801411542e031b15225156550712541c481c6c80021010501000f42403644241c5811301003501502400007066640301503a00d007485140c3c0c0101c036641c141e031040c140e00c9000c2e0101c601c104010707203101034001c5142041103007a14405d600f1103a4112030464075001c00301071032203003072500300165851044042024105468010700340e4929070416151500d030303000141c403e942d541e00c040e0302080d800e0030000744921342d00000c1011225050155081e1207a00400b0030b4940c015898100c0001a18480d01079030745204c14140c907107852400c1c20301c0480b01d420500740404200c0e9054003140000700100300c01c6640f02d10030015986a000b5030300343c84149a021500f0400d010701c5c1d00499450140499009140c4812014106928102c6002d0002084092500050007003003180c00480603044500300c042c001211000d20040c103600c58020420349005000e24903200c040300250b62404d65200074140806000400c0c082d41103504842d001c20341c4583c48510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 959980836 1250 959979586 959979611
    0x80708040906151e05160602090409080403140d0c030302030a021c0b0a0608090a03050304080706060905042901090203060d150b0a0e1b07030e03010c0818210d 70
    0x40c04003d0607890b441e64914070848a025014880c000310300c6442c0302c0e0030103000b015154001d04950941a00110b031702900190341c10420006d000700046540c00c01c0c5480d110701d080c00045070250040346c2c403959000b000703c01701424154481c00e0303030021140480c0c8000507003c0000d01030340185610080d8501e0050400d01c1510201520008043c5a13000c050707610413959405080445007580542818103100940c3c0c00d007510419a6207081c034002504100f130100c0070504115041040750b01264100300c00344262a01d9101017401001d00782c0d4112184450340740c0020000c1d03440740d242c0e002d010030004074010986c40c10030860040c3d44004c1c0020f0748410811458000035554000790f0104291454000031040c8200c002d010483d10507030040311010601200304590380d0710b00c101c80102c1d609500740c20b0b030320340059140503070313200c0307035000c0169803550a021244101907400b4180c03a1140d84d0214042c4c1051b026120304685030200c0300c21520442084c1c85103840303072006400042c40030200314100001c04007548803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 959982086 1250 959980836 959980841
    0x120b06010c02030a0c08120901140f07080c0705180601051204140a030302030a0b220b061603080603061005011704022e03110a120509010b04020a050c1006120807080409 74
    0x4011501d02d0305c3c51109000d4018100b15220300099980780661906840c02d001070070041e03141c030800303403c0790000440b039940100703a4007980d030f03103650003203e0135100c402c070000080e101c041038015180100307582e104079140d49441c105540d0241c1410386a261624410003210940948010030075509102c98061140340c5150400400c000326011f5a030040c0c0f84d091001105081c1c0303054000703081c0b080d030070155100c11400003241c102802c40540c40002916014182c04510707240036400a0a0300c030203ca401e07040616802410ba24401c620480c140d6040b0b03540d0702e550101054403405428009446448884001080b0950190704680010030001e212100c2c0d40c0b03004485003085284203049075004400b05034132038240c003c0304020390002c5411402c05005440082802410700b044440e0342d40c82c0da0108080600030b600000d185034003d002903550b0082800e01810301d901c030750071041440c0300f5271b40134200426052066006864040c4800300e210b5405480c1c89560350456079050b40d4006c0c0c2080001000702451 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 959983336 1250 959982086 959982103
    0x1020c060a0201092303190c05071503180506060103020c010b040515100305040302031206060702120d090807080703170c011e06080f0a0311030c100e16120b06010c0203 74
    0x50b40007050001c024074020043d0400304001302440c040400000850540c0070003030b12800000c040310900300c20003418041300c16003410350000c0c083e8081c00740b021400e00a5424000b4014545403000e01003d40611070520140741a0b40f4081c02540000c4003203580c0d980b2980082200c8074402c4001b18501e0404000182190026100405409040d050300c0045003003480d0218482e81c0142410030040c40c02e610b02039101d10455080c00c4c40c410400b170000325140d4402058801e02ca070003508000c81e60318102c100d0380d555a42d122400c00421344100c0000b8980311b0004a62066070321541c050440241365542d404829410030011001e040410b100700c6a2801c001d00c62800100200b51030b0701ea4030004074880900312002500f0559454000380d400f00141c50002514400741c03589841c0158400c03907010180c0e801c6000303405480c0100c3c0103c0c07914000c0ca15458202ca125920301d042034840b0b5451000e0ba0303105400107480392114500a500a1034040741c40305c0d0f04d065000c2411b050000000015500103814070145 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 959984586 1250 959983336 959983357
    0x190e19090501080145050d200c0a05040207021c0f02040516020d08070302040f090e07081c03050a140f040b01050a0602070506030c09190905100e060f01020c06 70
    0x351001000024400d00815003c00406034030003413220a00400380c4840f4a035003601004184c5200d01100d03550880d10b51400130280c0040680f03038644004400204062423403506400781116202c00d1440d140404224409031100080622062504d48014403000e50004902640d010300001d42e840c0b10950380b540001003103440f410a00721012681d20404c02203440140607031906945880395603034220f80028003910015103604081001d50307030340001203002c4d00c1103820941150200840010b007010752a08071103000034201041c1c80030180c40d02c0c1e00d49e42e1050f500b20821b1180c00c40098081e507a5000340e12154002e0340c20200481d0200c0541301148104400307603683c0d41c550b080b170303801c000900441ca2140c0d4090700e41100c440c4511468084001e40da0001405003d10810000020880c00f01c1100211094000b000e490f002181900c1840b89070f240c0280c0c071a0010300c0c0c1c2440005004480c05110601c00e8a4640310011007580f074030301c10700407003d150000d03690651283c111180420b81c1c1c1c000241096248 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 959985836 1250 959984586 959984591
    0x20d0518030a050312070315050a050607060b130b0102070e0f010b1312030e0f0906060d02160f030503010614040807180b0904151d0a141212010911190e1909 69
    0x1844c0310007d046802408005071602a01e80003031002d9aa42c180010840e0710880f91107448100a040480c02088170001483e0701c0414503100d00580c4d0107d4000f280c41103026025204866034034034000a07680401c03110481d1070000c550040c07144481040280206050344a02264402c0d101c0081842e1104851826400300301550081402803070b081085d1410303100309039026192410302601084e2140500d551102140340c01160740180344910401640341700380c000517040e00760703030340c40c200508a0340c000e00030100011080c662901804c800d8008450480b03901c2c07070041025910384213507000c44c41000011600303640c1d1900e85401075580c03044180d60256009011110588181780d00780f00455402d10b0445514508501e8182000300001c212201b29541000c8007200340d80d40c100030a8200001421000e1040c0c1022a81c0c4a4591903001810f050342c10b110420445014a100d5942460152880c6000322450a000fa01c0500d48640250540c00c000509886030130f1070b100f03e02d4107000049402041c03c059 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 959987086 1250 959985836 959985841
    0x60901060e07030e07031101030b0406091a010206040b0f0717070201150501030603050345030c090c0a2a06091b03030c0602070f170a0e01020d0518030a050312 70
    0x20441e914960042410304040100d0a01c040e51143c0307510142c840900740b4002d10001c000e041e4025046610340c0c0b03200030420090241c03a0580c0c0001881300c2a014600d4181e140c01e4140c1c25400040d249000342e4200c442c0780e2090303075a02c1e525061a00020000300c1042800c1d8044103030008800c031118001c05a40e000400c0d0300c44034048105402c14a9805141014108642000072410100495022008071020842034001e03580e046055681c0341c207802c185030448580c4900d203000201d028240440340440c140d4180e10358001c100300d1604401c5d034000c0c040c144c040203801c91550007402c008607031680705c0d4042540c10f140030010030500c81c0c26140a80d450703034646c1951010048032540a000301c2c6100e49510103528103640b0010581d9003044802001c86500050700424483c81e00c0d003200000d9440034007210391900008550540c0e42201004c080404c101840032070304c940c004681400d4640d9a544c84600385400620480c50103448240310341d41600680a8032808a00144000c0c408048202d01c40d00060 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 959988336 1250 959987086 959987099
    0x120a05070f0b040b090318010e06071704030b1e0a23011202120d081918030e030c010e01121812110f010e0703030309031206090f0b1203040e1806090106 67
    0x4c0e0002c0440d0079540040001000d1007102c0d0182405d00f41080c607181e80c41c0c1c401031001c5030480c0302d9094003410070800001140545540c3da0300400541c3e100315103822460300c40318003a075409100384112036902c41c50000042c104020a60021074124900040c0300c03e4540c900324074900054080c0c210210f001d038081c2940b0150300301040300e03045d03441c034200040c445481041e00042c00c0a0010303041c0040c0221540980c81400c820f40c00480039650511201b1044400d0740c64040c0c100c00f0000059802406088170041036076020341d00751030014030103031105444014000c9a08000b406c030544e6030090074480201050205611001c0d136142c41d181526403104500880b40781610384041b0340c1600c03213541c1c10a120b80310a00c00c04245181200d6040c00c000c01c00300603901d002d440340902c0001501801d890010009829440c1ea00b000d66181a000c104000000410040c0300241000307010b04c4945a000300000c0200090880341258030400084414050002c0030b448982010012303162003000340c0d11143c0902a4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 959989586 1250 959988336 959988353
    0x118020618100324080d0e030a060c020a030908011e0f02040314030d05090f07060c08190c111c08030402010522061704240e030f0d060e09120a05070f0b04 68
    0x5420008000ca11351500d0700459585241d03103107000c1000315512840e032290f10104111100c5550185c41404000401100290750751040380c070a50000f124990005144801071089480b045034075103164000c0d60075045502c0117424402e0051010f80d90800001010460103c124940300785000042d564548982d1405801d440015011a203241c200740d500e40421400003070403108540007814042c2c0d0550660806142c1da00803614185140304855043e1200513131301c920380c0c0040511800e8280d50400c100420301c0301c1d15181200e685a81d9030469588408181140c018503030261051400514296002125032501c45c071554600752900c403061014010132b5000a0b1616000c0c02040030401c4030702e0540c440c000f5003241c40c4444919105440d92004541030160041c0180d05102002c4a0345c51400094400260744220003610416141c200d000c149840b4003410a802051818024074000c0700841003000b00da40f00d4401001802800c0025800055401a505c1c0001d4040d0380314500c6454241410b41c1c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 959990836 1250 959989586 959989631
    0x2001110706030207150e1507022b14250c031218140618012717060103050d0f0e09040803010303021e030a0f0207080709020901090801180206181003 65
    0x8241004286c80900344000380a4102480395400d550080d00c4081043c1d040c24003850074200b85540d014103910204007a440c8424800003d0307a039080c0790503010108001180030300da01c00031410300b007603046200c40ca01540f01c00e41c0d485c2c00f846121206c580e490760703101010713079520a401000c90601d003003491805522484800040c0590006102c05900460003d8148e202e4500d02d49440e0441c1e45140b9402d07441a1021500003002e00750f010041644101d64152084051080c0c51601a442205011a4a0200b11241269400b0001f42592401170a00740c50400030b07080d40d41c003048a906000581da55402000d03a01440c06004196620750450800030b04003082070000300b8640c10300c08590901c3c0480007045424800141c41c0c2035681e40b044002c00c80c2012a1a07002c14000d02c01ca10000c25411625802051032400036260002d180d0b6440e1724003826203140c5600d440010041c20784920242c2002e50080c10791140c00d40300780013811000c3d000103a00742515280c0c3c4000035a1021490b62141e0300d800c0007403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 959992086 1250 959990836 959990873
    0x803030f010f15020c1c12020105090f01060b03040f0302100f1d060f04140304030b0405071706281d16170309041805030c06071b2001110706030207 65
    0x124815100710019548101280702175001d4510355030710040b940002d0900d540b480368000d00c05400c003400014000c0c0603140c00d80d00c400c1c56014210740f13480b1a0078140300f140d00719020042e0b0301d42107544548a8400341032602405500b54005c0420f00695000c10b8407030a05821030105000840150b0398062806c2000303190410103255205100348600f0003c000441640151300079030307041076480b10311080c6055015942c07008100e64005001e0204000c4041240c0f025140024140f00c20a01c1c0c0340340003541c6003400c0d55054071068045521a0401d00b08400c803004080904802050071514110b443d043e1020b2200b0640c0305400010312001c0c80303008540c25600601d1007600e401e80070280700d080304d6220310454011904c203542e00c000028480d8845c0210b07401c401c0e00001965151b561500c4902e480b030030106e40b40000100041c00740c03408100c2c5400c3d000e40307031071300101d40040220a02034260880e0b0b61a00701d190611101e00341d00c2000d44402c20034507019000564026881d04941d00e0005203944142042ca03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 959993336 1250 959992086 959992109
    0x80a21080601120c0e10080f060d030c030f0c320619021606060807090b10080a0c2f100209090601051c09320d050a02070803030f010f 59
    0x60700e0380e40110001c1c05881600720008030703220740020946003485405811a000096810842c42090300310484600c10341504c40785d078806640f0541080f0941c10200c8008003c10a100d01c40004240300d07514118115250341040701d0099000c0e19100f812030408072043c817583c0042158003a0311007005078001c4030004a00010310030760405d150000005041a24204481640441c00440c41d82c014005200026080070040107002d440c0e091080d00c2d103410b8060b91003000d04201405802d82000c03c8881a1504039546042e03140c1c60301a5080c01411f86c0e0088030040203803a907020b40c104140b0035100e1301d11019034807101a5041c0b04500040c2491000380b521281c0910501c522005d50b00e42c401d55650204c800d10b442c2d0790b00c00045030b0303d24040c2086485400441c0c50191507604102c007030000310700c10841c43c2081040a40c2510802c07026030040d440e07444403540040e481c1c00840ca000320040d2002222600603500f02546031520039103103800032100e04012000e03070001040502e0f003110b5110054900c903d41c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 959994586 1250 959993336 959993341
    0x40b07030f0807271509050901141e030c040c1e080105180711010608060a1a032a030a06060302180106020601050607140a0c0303030605040612080a09080a2108 70
    0x1a08441610600309400d521500e61841030049444410018141c00d501520000c10345c100000c040704003d003d01170141d441c0344000f00d254001c80d011002d44030001080241c00300c0e01441c860401100b607048580d01031190045034091596140541c0418000c2e0380d41d0401c0d05d8030b030044035103240d18032020100700703010500c0c0042c48a03031662050300e0660b0b0f400d4001c1d5405603d840750100d5081a0080f0542a107518003640854004000300707906010700e0074500103001510a96450103480a400b0b44032036450b9001c40101c28241d15400300c0b60640104101d4409902440403011a040c5540060100c460507500c440500451502c0024070010802c644015085981080e501960342c01040c0a00c138400c41e001310704141003210002c0b02c0f172040025582a031340004014030b041c8071803d4240c003048000c44c1c01c010f00854a814075100712030131613400706800e2003c0f4009480f10b448960090f505441084015040450440c204210a0801621500202101c90905440b00725041c00b000c84203010000050103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 959995836 1250 959994586 959994601
    0x10f050117091f0c0e09151311040311030105010e0f2208040e070806030f1525050a02120403020d080d0906060b07110a030b0403080c0f040b07030f08 66
    0x1041000d807040e018080c0e055103801c101c1501d000d41d0840d50405203001c4880414a481c0d031038004c4200709119444201e0858920700400804c008121a010110165001240c00c03a1401048c3c032004140103010005a0841c0305114421680c41a0810f0740c0042c1404601c400c1da050910810b40100310740d01000c1110309100520001580c0040c1c01d42035400c038036070603088010524000740300b001a802102c40b9919a81c9a543d801150710441c1d11002166200c000940581000700d20100481c07920700141818102d1190342405014014104481d0400580700818005070084100d40c444003c6450f220303200d018440000341f0340700c040000501050801c5c0030810041e214806e8050b40c05074041e8410f6241d8070ba400004000b441681c0340602840c0c200407001031a0011700c0001c125150261102c00e18600542c02400556145484003c290710320303900019000c41d02c00e14520340c00424100e81140f4007079140c0400c2e581c0b40c0054011101c0034000084a10070517030030101402484419041c400340701e292100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 959997086 1250 959995836 959995847
    0x11202071e060f09061d07030b0714131d1003080304060f2a020d17060108071101020a03020918061003020307030b0a180c110c0f04141905010f0501 65
    0x450072102201459100400c201e26070304180104041c0c5030b410094940c10742004005003900d5204403c5226030081c04444d41722010a062007913079040200c200145c0c458041c1299500c10b0b100c84426a02014804a0340410840014400410940468007006c2c850380c2c403500380929003d8480360078664450801c000090681040d25842a00046c00081141d59200c55502401e044914600070f40d141c2c0c82c0b1850b808a0032004003440c24225401c03242ea1034405d050a07152030300200440c9808071076a4000500310b61080c2540ca034001100d2074925000705c0021545400c1e41c01c20701480700820f0300460180038904040306000e444c840c0c0052908000c1c10608085040c9881107440300382019000000030315150300039044628880c0024016603042a580d0044120004801c480040725508060480001c588203046103081c81e440000600341e05000c1ca0100901c0b444a0021981c00c580c13503c04070300f01500030414251084211f02001032480405241200c00c4070070582000d28412030110f4180050399101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 959998336 1250 959997086 959997113
    0x8131203020a240e07060807020c01050304060e0a0b0702101505062205030706020616050c07060507020a030b070804020a05060412230105042103050c191202041401120207 75
    0x40b507059882041100c0303605070502c14803e61228541058404d106503240003d19104684440d950003100c2d071500c1c02c1c126160b03810034014500181d0140080780c041440c41d4000c005002d250401c407001341c03040d80c0c0c8496001e2402c440400140e00485803010451060780212a1464010b8000c0c003806400e1500240b500d02961020341c0143d6000229410030300380c41d0680c8006464002d08030340c13220f40d0310b02000b076482c842120120a81c5c2040240940c48600907000c3d2052408181d003d00002070514108503080c0d004000700366440240342ca0000049030304500d42e05d01a403400d5072a000e081c0392a005101e81d030041584860b00450b402c0004011102450b52000a081da001e41081d501d00d9050ba81c0380d0180240d08041c11065180009100c100a404000c0826000700f001c8100f4145007032680c10703011540111030010007003d0030015011650a41c1a51460760503032070034040d52900c800d0011600b26001600003030380307000f4034280488056801c8034224080010320801546040d026a50b681e0404110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 959999586 1250 959998336 959998343
    0x30c030e12010204090608070b071e031b0c0e06030615100509030601060309152702012007051201061202040b061620040903080f0604090c0308131203020a 68
    0x340c1808030320369401030000000e00750750000b551640e442d058100010310a5215007044d62003801d40004943c1c0d01e034000c4c0c0d407419400604050a44011404940151328002012005c00c181408c40c0f082c0844207074034024185006070380110b001418010f0185900101030200c2d803207a1b0204080000318a0104607982000d074044c1d642d1800c0c400c407070600b5034150083c020020307454005c413000031891a50507170240c5002401070b120a804c0b4001c103055001201c043c0b013005a0080c0d01d441c4440c05440c00c0481c00580302d032041c90030241c1c042407072a8505040119020224268102480070011860090700c2e8807001e0742c0700402040003a1402c860680380d1203941c44000e00941c0c030b0782401e50040d9201c6060b00d0004148000d8542400c03050b103420140540040b07804a031050b288441e05c0707224102449098038265064403648520b03181c40180050000c2d0062410740d0060311226040c2c00a442c4124000041d0701c41c24603503464500f29071072103001d03030481e230020035241c0456480038011a5001030501c005640 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 960000836 1250 959999586 959999597
    0xe030c10150503010509060a11040803030a15180504120518150c0d0306031a07120e0f0f010f06090e0304090c0306170c0907050918062e1b030c03 64
    0x100c01814515070070385038800d5034107502c0d05007045821000420142d11408240c3c0041140907589580848140214040c0811990041c0000b458640e0503034041007011035000250f5585994a0350700c0381511803600310706444944c44405000800685c1c3d084152012000c0c02c020b07003400d005411380d030722499009407900c3c4604040380c411083c1d014000d0449a8224080d41541c141002c9058064058191803004907484581c0442c4001e1102c15020fa00e17000d0001d40c1d80e119032805002c815140588503805400025008400041c100320f6420028101106000d0740007051001c15a4032010490349203a001c92406402c224004403600f10110440d019504416000205a10014011002051107070040c1c91546010700d00d010070050002540c1d000c50000316003580b041d42c1c0e03258048900c0e000d0207035001e4100c0121549c218100d03180f20313007143d800000500802200211500c9090702e41c030a800e5591209201c1440c1c04034083d6101380110400d040385440448001c246a4000740640b40d06ca00c060308022 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 960002086 1250 960000836 960000851
    0xf12051b030a0b09040b0708100312050c01060f0807180b09012303011d1e0718020708040e0105150a0e100e0d0b15040e070b0702011b060c030e030c10 66
    0x70240c1d40034502d0150060302240c0304e0b1400b0b00d885201d1540070385034180407a070400c0c0010f10082c0c1a60403041a42e074400c2090031105400501510103030030801c07680c2659500c80c0d90208450855440300401020f0f06402020380e5440c15001c46004801024200e07800d506200301c1c000f6a44603990b9040c111240c106031070a480c0a070280c480d4103a00001c080c4c40d81542081210a8410385650851450039550400d0350110807400260020141d08980000340c141c001c0c0c90700304a44641c0c40202c9031401043d01001d49000f81565400265900503040781d541040b2080c0107000c0350800294680526032410001460100c1c1103202030301d0603024a6800c0d02c40c0416000c80003001344140300843c0a610041e001c080400300c20301e040198084100c40c100d10341d58806410380403624150042003642c3d0740001c003521540d82032800c000f450760300142040c0d05100016002c40c0000d107044011002086c002c1c000001c1100c4148e50060175500c442ca042d45455109200320031403907a010a000a010803400342c0003804c0d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 960003336 1250 960002086 960002101
    0x92d020d0608030412260d050609070e0a0302011404030506130303060519050f0609030303161b17030702160303020f1014180c1302071202030a02030d020a0e0d030f12051b03 76
    0x44581880c0c2c0d00b0546c101141400d020034080d00849e01400702120008120358a0900444800d00740c0d255060380910922030420155000382c2050040306241d050041c0342545036120180703005130595024400a4142d00f2000c14194144103c001915040307510030024042100740b41c490108074007801c1d20404054140789a155a18403c4130b040410190a41c1e0f01ea1411142040c110819513104902240e800c5610b001c000d610105d52a40c5030340d00c4105c41940d60f40c45d280701c10850304020f00d64400c0d803048480c2d09004803d12410341c40118860340c020101140803040450a22070b91030b482100320341c00c2c1235200074901c54080c41c566025174040d002081010000000380e20f403040a00405070007105240f0b102c203a01d601c9030003c02e039140c01400f003401000303000a01280e62740300b50007819005800900c00c542003000380b174009003075100003441c3c5081d007107580000094850350340c21400c9000c1504400c0c3c00c0d000e00c1c0c000d0315181280018220400207840c00c2d007aa0300d054095261188200400000052604c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 960004586 1250 960003336 960003383
    0xa020a08011a09120307060f1116150509070611070e150f0402030a0207020a050609091303020f060a24061b060f020f0403150e07092d020d0608030412 66
    0x100001301041c007824030504130785403241d102003020383c0c456080506c80c2052500174010440c0800011402c03a24100d55810756203201b041080c400c0729201152628800300f0f00380c0b4010715020340c4403000504145803500901900368842070880800781e030010141040090b210100c00341d07020f4110922000d01c0404400060254200304e9129940948040288801c00704e45a003e01603051098904092460b12001040542d00801c101240e00c0340da264001800100c08034100d806251103401100c9506003451040c0e410088110f0b1181075207907403480038801c40704040c01c29004c0d140d01c4040003250141010b90003880c803920114101030b607039030310024801001400d83c004221410704100464440c204250300f200c1d81d6120744002d446400042d41104003256a030b01c10002c0000694004001051500c3d52071400f4091082602181306261003031020203220000c405013003521071010050b51411501903101c21904141c00c507407151b6106220a111800314525a2000160044004084841d580c00d02085 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 960005836 1250 960004586 960004597
    0x1504030c210906030b090115210f02030709050f010f3b09010806070804120c080d05061c020109090f02071502120a0b1f020f011a03060a020a08011a 65
    0x302644107854003000d980c1c000d02d0074007500d800d40d6080c00281d42040401a81c80003c0c001c2d00d94000030b00260003c40c6010340030845c0c0c400300076440c168003082c56020940864607030710008031005070008100035032182d11210b201c3c050401100e80b507060f480c0750300c002440e0600110150080c44000d100000c00d0b0182c55001445a814540c041e00e07400203203202c1c071002e841a040f00c040c0a910b020001184505c1c0c003203010b901c074503c00c0d030340d004c915529030300c1d5080049054041d1509011215a041e008120500000d020900c5110b0340401c0f242480014080d0b88503814841c003034180d070703800304000043c0c4c0d020808a00701d981000003c20444880c038128002803080c0f00d0b000344980c42c0301c2100010050140c0140c040c40556294200c6581e582180201c281e80b54024851761044020460071600c82050b01288110b0303205204503800340c1c170401c4402d8216200c50803072405c0c140358200701070100e01d820010030b98008440c00d025070425a60400180c05900180514458144001c00c221030f0180360340c09848 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 960007086 1250 960005836 960005873
    0x303180c0a0605043003050d1514030705031902010302071109040c03060f020301060516170414120a121407020a09050108160b0d0f060803070309171504030c 69
    0x7801e680d0140034045034440d12400030342c030309041e0102d901381c5a0301c10070489074009489060010802540c003110b6030b81c081c554905034159510010b03420700d170f20304507440301a15030114446d09025440c030401d498025142d01c0389100740c0c021607022020501c1503960140c3c107542800d01680fa644c0380d2401601860001d50302d190008004000c100500407072300500400c490082000704241142d01092105900c024028000402e10030000100e281507007007040c0071030900400200064009207030030046154400d501c60081c2521107505020740745090541100040c6225000789481da06603070340c251800b0241106082403054240b55001600c451a08607010554028517454000780c841c502000106000c3c0144815441307000014030b40c1501d206085400c0e40c0c41c10744880e0501f4140b100440103843c51843d480c01b56900c0f92800146107204001400d0401d2080d114140e400e81042c04618803805224010985940440300307805140c60910075858205405291021080b8900e013000310005600c04045d8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 960008336 1250 960007086 960007099
    0x90409051504020108180616050c160f050f0a050402070f0f050d03050601020c13020a0203071703010311060712050906280206240d022116090e0303180c 67
    0x40c003003070a1107144140700d98400d0300c070300640b6141c40c00441010309a146041c002d66110001203510162a000e12241e48056441c00a00d01a0003024007070612080016412240d035520809000000010710ba80340505000d489400e1240c00500000358021001c2c820140141e034000b8801c82032002070740d8a0103440350449103444140c503c4d0302e41103587c0c50020101c680020320341070100d50307290f101107016011080020845507180c581e1001c43d0000358000d461510030b40c0700802071400044d0742220904d120240c04c0500365203945c51401c01100b02c003221007810344100d0302001200300241c0d01041c80711010810703240c0030791280000710200e01c551080300a0b10800c01c00f02040464130b8640407807a804a506594241c1302c02d512902d034101140202002081d0245150480098803400d11014200d4414001000b9881020380501c0c0142e81c6c240c0b0900c038044c65001407100c61620040c18030140003e0540510400c0308081e0b1a14040d00ea001c041d00500c3ea1881c1c1007115036031640c003045078144100009110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 960009586 1250 960008336 960008353
    0x80a0e060a050706110444061504090320100207060209130c090501260c031816031e05070807030b061002120a09180606030f0e07050609040905 63
    0xb0300036400507142211554104600030500e50001c80c182ea080b125072507104e940f1110401c8883c2c3c0344c04040074205040058500c2c400003012609102d40004400003400340400b0f05100300403292001c64604918083c50a200101d000030394003200c00720000e803980d501310101e00340c907036021400c000086040190050010506501b80142c0f60f0051040e543d00300c9010540c0c500441103102030300c0d009402440401c0d900c0508000703039401542e200940145868107655070610924415042003c2583c001421040c0841002000c0c4a01c6900c840103240ba4001021048000d00d841c102c0301180c1e01004084102d0120510b1012032000c042c0782c1c1030342d0f04c0015900140d407205003007541c1c4c40c1c05210580e01b00d0400b102143c0c9a041540034865007140541c064460354100928007040c5601c1142904200700e1200000201c00300350a4840044890420000c1042882d20300020240d491100709143e0161400c8460703c80d22400181440440d40e05450694550b2601c0c030000700185000c100c041c01c0c0f40501c444 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 960010836 1250 960009586 960009607
    0x2030c120c03100c121e02090616082d0415020109020d0615050402030603030415020f19031106090d08060415080a0b091501051309060c080613021303080a0e06 70
    0x20041012035603545c502c86418080f404d00660300354400c44016030038100f820800e45400c903001490301c113801402a6103011091203030a0035100c0501c034280d0300a030000c80c2c012110a6202010548504800440c030303c56881d5810642062241d48110b0080d00c5080300c03c00d091038003c0d080749901c00d400a1060003119041e00304007019110611300c0c0c0300034140e036000c08030316442c01d4401d40c3d0050740058000c0d42024200300170300d624681385400910a502c2403c00c91401d2007030030480c10000e540070f1130711604400c04a281c0640701103016880c2d03501c0ea0b00030310208030117000000b51080001d1a031b1b240840c81525420f000c180102001c954445c4080705044010032029000500a030009100c0c00c0d49003007554801c01d60f55110303d07240010160591040300108641e02d801420320300101111600003c0d04a51503a541045420a07607080c40450300c0e01c01000601e1070b2520300b904058240d204c5c1907190010500203d203031040c9e98000100800004540008500e00c601c606010007540501496510040c048 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 960012086 1250 960010836 960010841
    0x507090806180706020325031b05010b0a0605030c09040b010915020c03120f040e0a1b0c0b070207210f060e16080109020d140c030607030207060605030a02030c120c0310 74
    0x320b403412403040000001d940e500c00800c07207070006641041410504031032101c080e01d0004020094080050110034414105002403640072607600c40c02c00090b00c0a42c0000340448580544c0c003c50501c03078140300300b2411070503806c11201540382c00c0b21b00152162038000141c40b8108160040b0004a002c45000391456400207240408082c0440840305024407448522159201e80402908600414031040101480c4509002d8104400000201d45011004034035080754020500c90720000f9120840c1e9030900840b07034040c94205803588060700000b410710140121710302d24524090000700c1070342610800d202c80400c0780d5032a294002c0b414007042e14200240d0740e0300ca4410b1040d60742c00e0b040d8280040d07541c078144a10203d16a01401c40008078405444882c0b1b4114100d002c0080d5000b100c4041140365010310925124407440d07200183c68901d141464000c90703540b07802c1f2a000f68000070b0307410056135001500c06035103070046070380070000d82c400840c86040480c804070035a054480d07550039141901254 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 960013336 1250 960012086 960012121
    0x1104091b09181a0c04081006090c09141c0605040b0402191809050a0b010905010f17030712021e030301060807021c030b0d0215091807080a0507090806 66
    0x144080c00001d000740703450700400b03020280c018880d80d50f08a144015250070066190b001070200503c83c01e103130396015003908224103480845100c1d07580b02014020640303a4840d201c070400e800d1406081050501e9500c0403820303003034660644075400c0100d951a200c0d8800100c4011182c0c0b1440c240001c0c20300e0318203094000410354007244601c00c07480c1c08804036540201000304880c2d00c0c0522070828846004907034000c0116450688003405982040000b08000072051802802c0d0682c00041c01d624280c0403800c0c02e034880d0452030034014030000041c0c44240c004151101f0907004100f0180030f1101b00d50907071802105864510080e0813000e87d010482e8008030245040f00d03401d803a031418980e10340c0001c030b0f100c0e41006081151940c1c249076907110240320f98031440c1076460185c8204074054480c0c0000d5010100100307524014107002421021760b00380b49400384840c140b44040305001e81032040c8080c110f00e00040003220720b40d80c0c0703500081102d40324140600c001e08888041c0c41c8682044943c4400e8142d29 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 960014586 1250 960013336 960013349
    0x40e07030506010f0c0b070c02041a03060108010b0a1806080714010807050301051c231615092309010306090212060606040909051c1106060108010e041104091b 70
    0x3000009405540501c18000800384d0540d50007001101555940240220151481b401c00c151a88418016100d9204070b548801c1910300036044030506000701840c05105800840c0d05904180f0a40791a8542c552400140c4070001100048907010480f140c00601080c0d105e680300e8410400d00203541180c0c0f9245501c1d80c2c00a07070303615080c0e0b91501c3c001d0310039110a100c0c081c0c10084020081084280440e20901d07030303520403014182c0d268201e90004a02090b514240710039900115980c500407076008580c640244003828448021a800e110b000e89911414407414071100700c0102801d00c1185083c1c0f20b42001c1d90014856040740d612030621100402d0b001c0300490258400000d204070a1100240c840e00c5180000c020300d01d807504051221002d408041022a030301c1c0f280c81c00d4039032200d42e4096138904403d880d540e084202010b0001e5585007a0004d40150b0501010800500c10a000b8813201030b44950000d000308884400a00460010914944007904088415865407014810082018100c441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 960015836 1250 960014586 960014591
    0x21f0f180b01060503010518190501090b030f010c0203031918080a080a1118010c0606060503070f03050705030112030c02030703031d180609091e0106030b0a05060120070b040e0703 79
    0x300e40f1030545142c03000780141d55212601119039035500180320b800c6540550900040001030030110968000d0f100281c2114a0164448100490b60f050410441d40184900d2000b841031400320500030f516448090040550900c0003040710a03441342e141c20810f0b401000d9581e501000620741400c0741c1d5600424109030000b40104089414004540a96207126640b8181d03e032505006140e918210b030340e010002814490810f600401281591107010001c001340c1d00d07035070303520300d0003000c010705d40c2070b0b0040c2020030b15240c14140512240d011054a064980c40340b801109480d41d807c06640c6c0001ea0f8400030351520031f400d4013008041d800802c3c000c2281c2040840441103180b48100b0010340b0704003184401007500c25002a0f0703240350141810790072118110a640003501142e2003503147d4242121626001d030f44030304d01042002961810140d2054982908101c41e00b85107000034008014618900341c51701078804c400c52030400500030400141084c0c0c138480c1e40ca0341d03213050f080102d1000303c800002003403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 960017086 1250 960015836 960015839
    0x6050109050612010b160c0f090b0603010303090b1c02221203050327061806060d050c04051b0a02070503160308071b0b16020a05010f021f0f180b01 65
    0x400200b80c1c2c0e800500140b000e00545e09000d1170400039003001c88156540b003051400c030800b19900400141c0507002c11100310300b4142c10510010155150450820b01880c0c0400040001c00e601042c5c0d04103a8102c4440c103903603035101c0b54040503228590130300c40031101d00c00260304071024203290703d0072210705500c4041c40401d41d5800c92002c1c258116800580031070010400501d2041c1c510045c188000c40c800d4000d54052000c840482c5000c0044590b035011090fa0003201071101c90400402e60b0002c01268618407040361a034909803075403a0403a4990140d034440022480453b05101c10b0820a41004125a11411030940080d6100d030b0900c00c035130082c010541400012405047c140064a800060542c80e00c82d00e5926001c6218500500c103183e0b003100300020030101e09100c010700c03c08400160b4210f50007800e004000b8a078096501c154148003804038080a056004908011800900b52200e501c0d04825a40030020304011032a4002a500d042c2c080a90038000312281c0122a0188982c03000e0390307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 960018336 1250 960017086 960017089
    0x101a09010806150f030f010507121503030e040f0f0e150c0c060612010f020a0905120c011e0e0909070305070e1512010228020c010329060f0d0605010905 67
    0x42c0b506541481c100e000c06462101c641c10199034024031041301408036800741c04400f03202400c540701504c807440001e11f254a940c0a4211a01074600e40c200300350901e03910031b442c0d83d402400a2402d2010b2600950b11000b00042881c0301c1e920a103403180e10100f0034055482c24044035515070700e022204480039008032020071140101d000c182c45013010000d00800319a25100308210b4804800b2885034a250f40710010384025900ba400540101c6889807500c0c0006801c100030454254041d010007941a84450050303451a0380c400b07128100c007281d007032480d00038103e4003600f120785079448400180c210184a0500450320000a0408100d0b070040080d16069a120761a51803142401e440e201130b07035090b1f1203000c4118684101525040e5500900051401c0d80e00c0b0010f61500705c034410030403c9510880050a02d103074044c003030000804400d103000c102074013001d2408001610180c007201800041540c0f82c20044d242c090031101d00843c58040caa44401020000001901c0b181c09102c1c0042c40700207000915 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 960019586 1250 960018336 960018343
    0x405010b100e09010302060c0a1205070c05120d030b030a050f060703050f04080a051b0a050a02040b03010908070609080918250818030f04030c0305150408030403050903101a090108 79
    0x1540c0005282c801281d10303540030000c0320b030464010308c0071074096100c020340003d081c91940d038825501901d0780d03a240d040504008101d0912640b0031409000d0000f402030700c4074000b060341031030084103007800100c405070600031a00d80840c6460003001c43c851480c0600b4001f20020710310303120303000d541d405100c10340e1214607814520b4800c2e10f000f04041810311000031140c0c090340c054049842446c01071284024080c421600e000f214032002e0390f00ea001241d10b502541018003034001c0e0004250024000f90f403841d038902e0858072400340050941c5a450030910f08000d000000c5542c4044010b103050f0742145d082940d020195010303180320705a0f1181202d803802c882e0f10001d903d1402e014584880c507040c2d03200381c4680607004241414000c1400100b01700c1d4081108507024102540c028850803603d6821032500710700d0880e0045082002105000400002406190071244c1c0642d051420507200c01007100400d1410440e0b082500c0c0c018140003a00744a642d0b00751204100b0320b4100c90640c4240da941403141d46 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 960020836 1250 960019586 960019607
    0x1090602280f0503062704061104060903020f030309090709080106150f1206030c06021e01020711011103071e030f0c0503030718050406031b06020d23070b0405010b10 73
    0x1c5002079000110080c0100f002d9944070001600b103905003c188010b10b01c5031804907501c516a143c020b801d100a005051141c0b81a40759440d9219103880d06001d8080d0161505d48402407054980741403070411601c052080d00e10380a406403600d0500d090082d00a4583c29031406a01820343c60250300041c0c0304040c0b03040800d48a615101c0c030445441416041350b0b15400402200455a01c2c0d102c00000144440b40c40e00c0185101d5000c0c04240030589002803104c4070000e4010b601e68010300c801d00202d4140306005aa045007401c104d00034038941210f16095000e4040041c000c900d00e12640e096907034414071509800c0e4400d5441c1000c611071080103403080148080701500f10740c8140001049113004c0c10f18449006044050400381c0795403000060706452440d00125182000250300c51070303415003030a1303d070301a2005001916080003802e40080402c1141c81c4100390000c0c4042c200740212007010110b800007904050011154a840d00b4014007030121003003420300842c20002010304092042080c0c0c076 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 960022086 1250 960020836 960020917
    0x1021c440f07050c0a0b010801020a3e0709020f0d060e07080f070309050a050c090709030b0f220507030b0a0b03060a02031f030b0907090c12150801090602 68
    0x700e20b51502d03103080b42c441d0000c00c0c0000311480303854220000710f110309003100c0c002c0071040c1c000b40c0d9404802500404903d0340c400342800b520b004243c1210300b214076110000103541508030080360384800d5580075180c0400781d4014415103100154440002c22000e00410728070300c02100c240900c0d5070302d4041e02e6030030b10301300c600c180040d070705c2d001061611190f080029042507942c94041000b00700703032701e805090128840b000c940706d03403004c0040109420700031141d51b07002c20241810407405155031107800b9208801040d804a07d07800400044400c41101001c221400b002551414210003600e4801d1766003a580c001a42c40a0600000800c040c0b0b26005141d14020041c016001548aa004d00d04c003941011f400f11008800c4130601d056494407a0001030020b6002d40041000713400c1c070002c25401c1c4100c980024200c030b801c080d10a54103941243d441c0c80d80d60f213450400640d01c00b02011100402000790024a059401d04103841c00744a1f1a401070080e06421403840f41c0d00c040b1606000b401c4048100600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 960023336 1250 960022086 960022111
    0xe06030601030b2b1401140a020c150903120f0114011b14161d130f021203090312072a03080703030504060e0c01021c44 53
    0x1803595200c0d8003d0281c80502900007280300020320313506030f40124204450410000240f0440c010b03c8600754500d580141000004c200b448034074900d0031095503005145040550300003071102804401044041540d80d00c980000d4032a050141d000b0381c50b68480c11000d680f100314240444d2800a1000c00c00d030480d00da051003403400c806602c0040d03c001211313008a0483c002d07040c4840b0b0108100031150506028008081d08445800c00100e08080d01c00e0340102c8161041d05d1100741207542d02c01c5100307400041a40c0d250424030304a19003044041c2010300000e401c01aa0500d0320b124520000260100c0c0030210292100844080c010107101c1c0905e02c009850203142071a21000b59411108000c040e80088604c0d03001d10b500c03a254490140d00804044002950352002c000c1401218400c00942ca20308070050b00307000c01c0800000303541c0c0149610f80311100100f00c2144504900900c3c0903c01c41d460320b81c0d040e116880441d0420b88c40c1580301503a414101c04148030510f20344600d0181440307096202c480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 960024586 1250 960023336 960023341
    0x311060f01060f050405150705060a051504051513020a0318051c110102070503070605060607120e120f0606100801030c06050f221e0324061a09010306060e0603 70
    0xc450300f1072000c24401c148441080042220303140c0c40b00850405a45040d91a0b60700c009107072061400d00b00074104800140782c0703410300c100e0a414080c180c5d440301084030041020784907144101c6503542014000e0341d0180f440c3c411100c416169402030210510315850420080d1314880900c07080b5a862000102070382c000c406030103600d9801030b10101c01194280b50500c440c0b100325441c1402c903484004c080d245d41e400440c0c1c1004219140c020079901c1101031714000d0a20080b40e0b510315416000f039611400740038020501d0b609036103800454401c04110b40d811a030702003440342000381d2103000590700b87e80941010442840e516018400d01412650b0051803c600c40303280c104119216044420504440c020402060380c2e05103800c0c40c91000b208410341039203500392501e0210161840c1410000381301a5258000304003203581d00c4450200400d803480e0150100311240400303c001c6ca5240c10a29543c00e00900b2502659603540c0500030400082e01d08120650b00c0e50000e0310301203088a6801d600c00c004100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 960025836 1250 960024586 960024599
    0xa031505060703440405120c0d08070224010302040b010804080304030e01050f0301080f0d0e06040e0606280e033705031902120408070611030702090a05040311060f01 73
    0x4000802118204124503040e8610100103403132000c0d06040450449070a000610100780000d01504010044c050300c0c0c1210064480d440e040f40c2c00c60b550500908030002084280280543d8112a10b5402a1404000305210310390300da00081c08268010303803400e110744225502030301940c0d029941180e0038504580d91641c0840d5903e440722020790400074103101e1440d0b0820b40d14051406400c2c80c0c40070b414080c00f01c41d01d640c6810404c2401e50104500350100660f1921f8030070465042d20110308410b8040d560f00d4000c19114807841710428180f10100074000d0403108210220070540499035078500740e40c1c000f40100740c0d84009007440c082111180c1e440c188864000d0a80f03141d03881d07080c540101c00200746034a40a007990801901d48110f04941c911080403941c0c14000c005440342e40803c201e0801c1d00f0b2510319680c5800c94094642480642000f8810300b81003041980d05081e030041240c0581d1a10303182640c054003040e0782c07c6000c10003807000d6012202000c030304907204000800048007079038070301341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 960027086 1250 960025836 960025877
    0x818061e06060a0c0b0c190903060c301d0102090112050c0901050702011806110705011103040e0402010c0c03151d0a080306040f1d0d08010b1c060b0a031505060703 72
    0x610080c0360720000c008132070302030066030350100034401f036911441c4200346181802015a9a10030b0b0310420084068080703005444461030011140b050b1580700d140016001c45040300400210324108040c1640b001012111030701500248007104080c1d0b00e80328030429581a400a0340d90a403002000c8101c10310200805501c41d1740640f07001401498110885140e4070548616500e9580001c1d0008403980d0b04407003240d01c00c100c41c400404080ca0190708001d075288050791680100c3c00b03005d00c00240f001c045804d580c440c1400c502c60a800c0484129282c1c1e40f41ba1182c04d02111a070680c45450408855040307000301340390320000306005000a80880c003890740d2040555480108503030f038001d03906e049004c00c070801032250a4541103034816803100a000f41d41014603080d882c01411040083c0711006107d07600d00841910305403400408800b40d90f401e8803030b0013400b804054214940f01380000c074001c2401a81348d040a1000019140c40700700050310b450500009204006010380810b001c9200902a142e010303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 960028336 1250 960027086 960027091
    0x1d0d02030d183014032406030f0603010507030905030904050c041502010e060606040f061101020f0c0618010b0109030206030c041a0a0206060102010504120818061e06060a0c0b 77
    0x14000080d0802d5907501c0403a141c1d142c2c80080700da012074a006020110380040f95890305182410411210001c0300d8a00c0c4c0548401480c4914000c801c03100e003100380b640007940300000a8020120341e22494030420103001d402045039140d11a41c20705000c00d81c018024803807194200c0e0418003a40c81e000c461010320015080140826001078800c1000007a095a54503542c15040704680c00841d0f07220700c0b201ca05140210241101c1d200b43c4042204210504c003081211048031030b58200b1704c0e0081407018000f402401550305a0400c01d000040070f0110140100c1c2c403a20520a1300c1d0902100c484c40c101142c02c942000e8030701404146900c5c13083c0054035010010b55403020401d5100d03071400317450f940080c4c604480030421000d408070120300347c0201c0e5010b014003130340b1150a10080040d0315140d101c0701c401e50320880e408011301c404a000702c2c04480c0075145030b0220b80d0306081160100e04280c4c1d070303e542484445400780600640341022070100e1030080e0840301e408040d9500c403030340310b2a1034441c0c980300d1502 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 960029586 1250 960028336 960028361
    0xd021c03120c1b060213230301060f0b190c050d0c02030d02010911060708161b14030601090c050c061008070e06030304060f021510050f420309011d0d02030d 69
    0x41c01b000620f841d07407034490504880c4002400017034409900e0516007502c2d0305400840d02c0b91215142440f090101c1825941c03000780300310071781c107925030004001c1d5401094080050468040c06c080d0300071498000e00c45c56400c61082d011204081c080c00401c0342202e1004000501c0000344c451084030500e4048041e110640c01054628901420081c1000c0f22814110003140c04400b40004400700c100118090340c000e1841a507122000b1b511100001d8503105c050045540c907036603e8002c40019480f0b1000e071980d80b03602400f100d0460a003680e1001515003203114201a0b440f82c4c400106086000fa0855801114058000c40c100740c10a501030703c1000413404100d08603c100f54082c20b141122401603802290120f240c139140a083c401406610850600000d0203480c896941c19205180d00c46003860000d46545d400c00c1402007078200c0d0f07072800c041d9010140b61010220910441718019030140c1c03030104c1d0071005c1051400d20a1512900e0b5a00c02c43c0140141e00140711902c4c0c01d20498114114a488 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 960030836 1250 960029586 960029617
    0x40c1706150a1d09280201030911040f0b041d070521070905090706030608031c06330305010501020312040510020309010f0608060606090d021c03120c1b0602 69
    0x31903002506000c5034251050f0301601c0300b002031165260060004244002c884d2101c0c401c3c0940c0528200d002c0038040800904140e940c40152040c000525865a103069004005002069012081e0000341c15042c3c0f10b03510451404010703034401000200703400384010680c80a44000740c1f6000402980c1c0040104440d04803034030070401d848290703049c003150303014214a0100051508010100c10f18140303140c4c00c1803090515142040c040f00c01c00000f503a0715844c1c0f4441812000280d080b807400074001039440159880343d11906080500d4480d030081041e03642d040c40210300c0f0354020204400b03a50b400e00c06c490142e001085031982001240e416203a10902500403280b2005118540d04100d0303000300c03095000d59549a0240b50081c065001d440c0040800c1801082d56080110009041d441103603500c91154101185010854840c000604005040781e00c01c0c040d42c600c1401c2c080d1501201c4008030700d4061030080d0000f502400b5414800c5400c004460500044c61700359942d100135270040140e10100c29 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 960032086 1250 960030836 960030839
    0x10f0b03040203150423161203020f1b01080a0c0804031d09010b040302130b060f0c10181b060c060f180318081c0309080f0d0203040c1706150a 63
    0x20080d0714054029842a4450710220102580d00c0c1784445200840c1c02c1e41f03401202440901c03450400407442038985035005048420a54070b02a4505480300012180701d0060284d0020031600c52448100c0e01032080e2140841a51003054000803142c0c0000f201001c1400c1c00040f80102c2e00c102041054070303100442c20700d0035003424000039a60302000d9110722101600000c1c184110706201c4504101000a250b06018240c4400c000450034011340d1141c801e04140031418884100080244032884142c1240401404000d4100c3c0400140100d905456920b420888070006070840a040c5045806641e14088040000da48140c0509043d415641c1c0d081d0b104e05015500d515460104d000b4544240c49040c00340010424100d407013041c0b41c1c4a000180c00044901e800410002148104240d82d40b40000f80e04030300d80b03881c108a0141081c038141488002c109982200250ba0085010b60301901415180c16607880211182040660410308140c0210000c65444805000c500c24001c5c801080d81030713100e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 960033336 1250 960032086 960032113
    0x90b190f0c0804141305060102070b030604240609060503090c0103180b0f0a0506030a0203210412060c0801050405071e1e020105041406090a0318051005190305010f0b03040203 77
    0x98009800c00704180b13103200e003500b15170b02d0980003000789801c403248103000ca450201d0006c0e450f24510320071038664440000006446980d0360344010940f03840c82511074034004183c0d03070711428550799025600101d0340d011008603001c2e02400681c0d20503807680d4000c000a10319840110050b000c0d0504032404880c90644072000106044080c0f8800c0c920381c01d101c0312602d4500d003514241d50014104900039040ba0300880c02684010412008100c4695644e20001488503824030344c601c01c0b9800100d518011030000401c01074560010700079a49541d86078101a601c4004020403244261216000f058600400c000c942e90600c08042c045c001d80e04209001c41000351026603845240d105250041c0d654004200403c420031400485070300d01400108000d24004134511b44d19240e286e80541800862464a020300c130010328410054075018249a00c00301803100e0140242c0c110000d4900030503115040d2040281c03081c81000d040701c0a480d06115030302d1030021021641e601c05013050380c040c0113880c00c10010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 960034586 1250 960033336 960033353
    0xf0415110409141512030a08150a0f03061a010e1c1b09421a2d091504050603010e04170a020c09060d020d060b01090b190f0c 55
    0x40c5180310440303c9645840b80380542034154028a1501c1050780d40d0300004003000010944584e041d450524040382c0d11040342480e0030400a41300198080070784c0c030b000b10b491075064844000b1a446240700b8042c40b0000b00d00462001218a101030005080e14101e03111032404c03010510404940080030340d0110410307240c08101100d2031319034030014040c07074108000c2c4459901c0b074050030700600741c03503d46040400002040c6480d214410600c2c208100c202d140d216809002d4040028002c02180216070450540404c410360403031042c070328800705c0e51240c040c0b18061610b200b20500015804040c07030a114401007002c070b1a0740e0202c0459100c018840452280c4070000258080c0590140c110024900391910054840000414400e00f101c1805030f0b85030300d42c00140030301034194100c0b000d640380ea03106800300e0002d131080d517006903100311500300410600c9055030040b151034030b0a994410b0950389440300d480151054000c003040c184a100f04a01d0458400d18038203001d01d81903d1300d183c02805984030405c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 960035836 1250 960034586 960034601
    0x50a0807210e1e0a1104051e07210b01210e06040c030203070b0a0e3a0309050307030c090f020405030a0503091e03060406050604150608010e0f0415110409 68
    0x22940c490011030024410f1070b50350100042124008101312102580c410b000d15851044581c05140c5072008076014100981c2003c2c3c51200720240004a8a00010000c5c8101d4296600e001c0b25030a24190000c01959402040010341060b145c01c500380e100c0c0c058503401180000480140c0070740d503d0144013400c1007881124011405660700c0111075066004050030481250b200003400c0c10100a0b440000741c120110b5003224004588144444444051120214403e080981c03d001c0f9840c1c000d08030804503103071000003d8045e560750322642d078070b443c01d1503901e04036400050a4090000f4080040d09035903045031402d21035100c80942840da0740e80200349030050045048500f500003041031030547c100f0048103114080e20715124081810708501103070f100c0c0000350010700007544038800518103440300c2d0004118002007000b07581c4a907035078070001883d6101c28001c503a80d1313020f4040414041007641e41e1107030041c1d80200044601c04204646000144860254008820b50500c8000790f0900e4a104061 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 960037086 1250 960035836 960035861
    0xf090c07020f010915230c071517072001050c0d1814100f06050f0105130b0f0408010e060402101d030102040b0d0513030516020a030204050c19050a080721 68
    0x204400545100d580c0035006072569126182c4244003110001f40000b40d010300320b440303614051080486282c2d044585ca80010b528184e001800c4081c808040e5000e030843c0c108402828000d004040070140300d0342600c0d0b0640d060550b065007800700c8070349056070380d000b0300c040b0201c401074211081041c2e507800741607440c501e00e90713005402c1803c40526101c418010881c1414000404000e5035041c60f0005900400016485040000109441003000700010310302024181c06010303152201da81c2d0807528800c0e4401d006404055003040301e0f000c1080070014101c0d01850340101541c00d140d4110300220b800101060084840341e01c000070303004003034601b07100400c007a201d480d0303107650f6034030840c02d80c4402c0d12000303825112244d00602504011035444800e03201040c0e0f0103080804003244900004005c40c2d200e0f04042d501610b09820300035485000c800401c00c3d0301e40003001400703100c3c180105480b14003074644210b020501c20400210000d2003501e00700303a03070050f1190000d00d5020b5101941c003201d50342c000c2c90 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 960038336 1250 960037086 960037097
    0x1505091909090b0a0902011e020c030109050c010e0d0807110102070e1603050f160302030a06050402040e0901110c06062403090a030917031903110c0304050f090c07020f010915 77
    0x244240030703d04080e260700580004080c0504942d60780000c04211080e4601d8250481c0f41c419003510038824802c040c0e518200038001d00c0495000d0a1482d1500c10740b10226003c510001d080d880c050514140d21045503401030301803402c042440e00c4215600605601242c1140141d903008540f41c514404a1401000ba401c1c104046400141014048071703c05001850541e500740200140c10610441251100481c2c3c41c001d0380320780740e64240320040c21344d90704440c0c6c0c03103400854046601e400d2500c42920802d25800288400381241c54445802c1c440e4207110780c016044880060000e0500c403d095520001b41d40d403001c0c55001300d4070070001070740040d0b034484070980140550701c06055104840401070101c01b100d041d580a001c54a1658032b00c1020308e40605518514102132080f8042c0d48503c0000350b1350a1001c0d582e00b055a081601c0303a00c075001d40c03840b0b10b000c0e106420050800e010b40d18429982e401e621454002960200321003506080211810880901000300748414111040c862020840c0c844 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 960039586 1250 960038336 960038351
    0xf0301030c0608010e060d020f03190c0e060d06050705070611120a02031603091407080609010c05090a0506070611160212010504170f0f03010e0402040e06011505091909 74
    0x300c400303115500090400c16840d0043c004000c95035155a0458000c85042c0803071000c88c4041020b620b031000005605000f06441d0405040312804213005081c0b0407030462404c82d4884018645006054850301c0e000700f01d2a0910000404d282d02c4107401030027500304903040c103c0c944c3d529405c1d118a0b10301004420b00120f40004454024100c06401c003110000560031482c0284404010500450040c01059161042c030030a2100701f03240700e190328000209840d03125484540311551010b040e5011800d07507280400c0d94001034807600a59a100400030070000e14a4038241c204440e540149000ba22069a0341d180c0d2110142b0b02c0300208050740e504d07070091a403140301d0300400021200002031a54140d0405003041b0000e51944130b412500f06040f4a40b603224107024000501600401c2d000004400000002040c2c1a403001c442ca4844c5208803400d00043c45510741d0389072520001e00c90861143c55000e40c0001c5903024501500d5650005003510461100d00e03244049000300c41c0d84581c401560b140786 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 960040836 1250 960039586 960039593
    0xb0a0611010b040507050d090f02030307120908070503070303112d07060305040b0103021014181203070c090f02161b050d080d050c04080604050d0305161418060f030103 74
    0x42c00c44076030022a4200010b181004000d4960300c980d46285034003076915150842003255004842c6800c54018040300d44880300c0f0303d460002401807994110110381510b41c0001e6031003002840c1c006450025010700145880e683c1c0544c2c05102c0360301c09014602628541c00314064036480f25881e408000507600041a140c90880c50414900f81c00810416040c0b038108408074a030700021030b0440740d05440e0008040e90b01c410494442d095111051070b0f807040002c88000d40414034001d2240d0380803c5803001911103c400802d035032407181c0302c802008002500f00070004504960300650258144e060003525140f6100d400c1c90130302c2c8480301d0441e60400c8034412016540603405400c40602410390b02a000c02c080c640f2445110701402e07807400ea41503142c0300010350f0317403a008041c0c80080503201c00301e0720503007406d01e06161103010400c0307007900003441c020010303150450300d4644071044da00f40e4860b45403004600011007880d51100c02d8000c14450300044015090b182c0a00034920000d4200c003194aa50641c907 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 960042086 1250 960040836 960040841
    0xa08070e0307061e0c0b0103060203010f0b160221120408010b0402041a0313060903020a0312060f051302190203130b0a210905100b03060609040b0414010b0a061101 72
    0x44602a502c00c0030140a5240c0052012090502c1307000c4c056081e6030345110442d4811008840100907151040000080114a8015605036816241e45d4507466445440c07540c3c660080350504814501d40520b102c0c00340c20600c0e100c0c0c80f034410104c20684140604924a4540608111104004100006c1c00c1081540a102d005010350044409501d007504d001d55030b80d9410f015a17141034030205e00202080050013009140084940e02401c18400e4094509029454000c03581c7c0c160085591030700200c81d0750519205083c1950200008a01070900b00b0301803154403c03141042c00c070126802c101c04100048200078449803a040c503402559220302409800400030b02c203074020038511100707100c02811140c201d80d111505049160350644401e0027403001002811030520050060b000d542551501d200d004c5d0044102140154103c0750503072501d10900a400304100d80141c003000301000801c0005e060680c2d800d240326030040021441441a0001581a80c00b5600c200007080b562261082c41c5442070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 960043336 1250 960042086 960042107
    0x12010e03031306051015110a060c050d0b010e0306220b0f1b0f03010b07020607060f0f2703030b0612070c020a06020613080a11070306050f0133090b0a0807 68
    0x1904403140d201d02d0050319118142d04814603101f480604454441d07150010401c01e492680c00c02d00a000e00e480c5c607003001e003039684040c3c400c006090803e800148554002c1c0c021110143c4050000c0000d03075504a5001304000700e0341004103205510814002c003003000300040501842d5490182e2040f800c000c203004205041c007c5800d840c1103400c0c0200c408480480d030940c0d044130100565295140e0152001805a10900341c0c0113154526010090345c050b07046603c01928201138480810102c081600940c2c0341c1ca03141903906030700f0b001401c4040c0000b13100e6044840060f501130900390500400400c0c0d42c100b28800c499100011b8131940c40c0f42c0c00e601d0080d21000040855002a081501700100c175140706c14004100078203601e1000035080c1007644110707000b0340030f0002c190a441e26942c42c2c0c03a040c0d024020640b11140c550744a83c0002c99000410140b54043c150503c8051005414440080c0c403840008850002030060300c2400090600c2058001c182460712551007041624050402824400c0365 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 960044586 1250 960043336 960043351
    0x30606061b080702010e1809071503020c061512060f0603060f0f072f0a11010f0909090213110d24180608010c1707030504020f12010e0303130605 64
    0x303081d408400700c0ca000d03048072880341c0c0a20b00128a28200f001081c01c80075507007020404191807104000b09440c012544000784c0340710706042d074036010342001e04806070f01981e403500f038042c1c1124012415180d50002806080640903084080d58280d5920b400c0c14140300319003c90900c02d0100c2002102d01e000d008081e80258124168101410301000e038261014000308a1340520210000034550603981282c068682d1740041c80c41d000d07407000300c904191144030000048500302c0039100015a43e600070a02c0355500c030002e41d110304105240c1a2404003030501d440003030341c00052124912000560fa4081d1210005449100580d1848040d0500c0111020481c008003000d8100005030804408100e4140403500c0c000a0140c1150f4036151500c02054517902203d015071a01c8448034030990891f0511303000e212090540e0343d4580c0e0380c1c04240c0946200700d800079032001038080844180c0c079000000c07603d104019000054210703412056185958002d90305404d120300b002c02003070304010090180300d501444 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 960045836 1250 960044586 960044627
    0x190936030825050315030714270601051b0a060203250e04090201030f0c0905010809010e12071b03060f0c0302160605040219060306030311010c12050601050f030103060606 75
    0x840210102c801d0031502440c01040400004031712070135460007503d14040c00040540c3c1800e40c2c0c8400d4140c4650304180060700030741000c2040b44441070040c803100007012401503207003400da888000465140d40030303c40c11f1124000a0040e483c0488041048050341c070f00c118401a0303030341845109030451011200380389980b0450702c14000d0a05902085403803241400350303000b25071007105100580203081d040030001052441c241c1e10b0013a1341d50158810b0304448003a22802c40c181c5460302e540f82a20080940030141c1e5001091a04800003000024100c0c0ea000703658003860b820109550084c0c3d420a90700c02d03174206448145000b0f10306641e02c282001844c0318181140b900460105c440c000408030310000d0a110b555000107010354840c0048410a8040c1101c1040040e40790317a400341c0103240ea400140d000a90310000001d1540b014421140c0c16a101d07128851152900300509014000003002c0c0c9040001c148010600340901d80c0c05107018610400700800c1680c14014014403107011880e00183c00340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 960047086 1250 960045836 960045871
    0x80c010908030c0d0f090315050106030e0610050105210a0c0905010f0e0d3206061e1009090603060207120806220b0607150b1909360308 60
    0xf0b00000c0e03042100c0118104000174144044083d83e81300180c0c0d0000d881c4100303011610f01c0c2c44125500c024103a07005604c007005200128041a03136110b074100d61012414200790020f2240f9801000645210090b48203481d03142d11520500c0c054500040d1000158144c540c1a2080750325000560074015000c00e04e81100c3c0002c0c081c03002000c1d84031070402c10b802905604440000d01c0745141c8404590645102816000302e1a034034281701040329036081d51180e00079070020583d07a207003540180c54114810030300c42c040f03000c002d003c00c400f160620fa400c3d4107002082d400001c601549008487c001c5000e01001a2145100d04292174000c40c010740740000c200512040101c0d56545e68040042d107140203802d8040815900c3c030300e00c002c01c4940b07091a4880004030b62041000080104600c6203040094140004140d140904c8506032518807504203202d0080c80034441c4150950041100c1400507080e008040b5000960520114281c8411381c18120348005503000e15030804540d41d08074a03ea0001030110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 960048336 1250 960047086 960047107
    0xc01080106020f0318150403050703031106070f0e01030b0306181c1b0303020c010f29100c02010309140d080702030408120304020d1502190518040c0507060501080c01090803 76
    0x7031140760711180d103001d0407010140003a01c448514991002c8009a201e1f80c56071242031080d0f484009220403030016208003ca100150307408200b00380254180d4039040300481a510040e92090100c0045a0406560340105d180c036580801840e0700030b050300d99050040d12a4040042d04040900309840b40201420300c8a03400c0039400013820351075260f600c00ca1300c4101003d140c218064403540c84016034542c2840f0b001008179003a40c1c03201c0c400340d00303000810341e9406034400d101a04c5664240e08603400f071031480c06030207542e0140d91054059841403400050600d400d586010720f401d01e4183c012000c1d1702441c102030ba80c0f50003020941d0407542c1d500041d030903c0c0c0350007809540c0e082140001140b079000840403a04540316110a92035599004a40914503c070300704160303009400c041d6141d290b800e4207910001426001e00e0442d0b08903c0f001c16a4131006600c03234140710103442e503081a0f0042210802c95600451528031450703000c0c2032014068480b4040e000001071250405810030320b1070f40c008210500c0c92 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 960049586 1250 960048336 960048343
    0xa0b01110a030f090e1f05010318060e1608030d0c0c050712032c09010b07031b02030a0510050f011a0307080606091203040e1005030304090e011b020c01080106020f 72
    0x86030b814035081e49403401c49030b000c49040f500c1d6444403d103851080d06100036100c5c0d107041140340e40075000d4085500e0380d45900441c2074900b080044903081e5510515900070500c3e0ba0054504214400100c1e07c14814901c403014060446502c0040d041d00080f900b0700b08544140640006082d00d4580405c2030485901d8035911134a0314031821081080e1510040205405003191000307851000800ca405140000812448126008044c82c85450b0610000c03818041c1903040c2c0300701c940c05550b8007102183c8018521b200021b20082030b17034544038271070041000a80400042841d81c1410f10041031030309062542d84040901038201c6610b070024604002c88005980082c1c0f0750100b600d01c0c100b0031644658012600a21907034440d07680218103280103400b1180004000c1c030403110022282100d581c8d80801403e03140110b0301400340c1c1a001004100b10f420010307000510700c141c00c0c000000d90428014441220303100104141c50168100a400c88069a081071920b4010036550000c8c200b840c1301c400c000c0b500c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 960050836 1250 960049586 960049603
    0x10080c030706180312080f0a2c0102040b2109031e0702040603050706051b0102070201021e07090504060606110105060a05040e030c01022118060118230a0b0111 70
    0x1084600c2449401c40183c40c3d56920045410001000e0600b403800c00081c5039a00c110b620b82d00ea1465070000c00d002c03800318810700082c60a110f06441004440040c042d800301e503000070340c10441d0340078000032504190b010001e20203051000c42d0781d0700c0818903582ca0021f109000704042c0d480c3d04240200c41600703405040c4c01929215040b020741e40e90943d440005c00805040d040981944179207000840d001d84c01034018840c0a000e082000740e000074000c1c1c0d41d4280d114000c0002d0050700010907050744000d00071188011b50885900382c4003400d03160030400044900c2101d06031a40c6d5107a48007084807a030005000092014200005d204501d041d102088243c00315200c0d03180100d94070030310515208014410f844042c52180000d550f5542c2c04501e511503042c1140b00e41a1002445011a4400160940d0301c00c074040503d01420f82c580c80c0091312150a40c10396000c10840d81ca0f000000d00440c003101880c000c41403594000303031007410b080d0700d07031002c881e44c2100142c1804608807200f080150300003503003074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 960052086 1250 960050836 960050849
    0x3020a09020f0d05010b03180a020f0907021e0c130c0c0b060105070206120603060c03130602090604082e060807030f02010e0a060804150606170a020c030f0310080c0307 74
    0x140d0b070701d011101c2960390b80f04400c0450b081900d0a0000320f0010031240041d400b40310b880d100a600b50045030003050f02e501c04440300039440807415124403018140742c60140e902502c41c0c019600311940c092160322184110b1035031f82c40c0e02d410111500441b450b1407410310400200b1b1540400c18206440b2000d44220031790800600744e01c03003820000b0b181d42e20500440340e900d540640101e0f11442180c503a111041e1058625034802d005003400035150303c3c1f512007502d108015241090f4140c41340d40d11104000c1d4000d25a69820050411011491007810400008d101d0080340c50040e0703480580c0d804034200200035003107059240c01c0240802031454000340b07400581c0d410a0f0320090b00d142038030060340c1e100e0400b01c3c030300d4018200d4040003992507005400300740720714000e2100d20b00303501400347c0c01000c441d17513405000c0100c2d03059103026401c40300207045070354018007003500185002c90f04084180356404c0180311000e219000001c00482071042c0c82c0510003004540700030200c0c00b803103800103500ea55542c000c54 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 960053336 1250 960052086 960052091
    0x303040312151715091f060f0315110c0a02090604060e04140705090f011203110313060207082107061e05040201020d2d050403050f0601180603020a09 66
    0x5418450040e840300321005200c520b240c901964030182802c80203400d200346550350180040112105080000c035512490fa200080c0010101007104499a03222140c0c0c0413080f150703142e0340442c0c61400000d600b0091401109030141000d003130181c0720b05546001d100110b02503024004d10307902e210b0004122602c180e0407141400f80c4c0c3d40740301c0881c0080c007865005881844c2484103020604c511421001c81d081ea8a03000d0b9036036291244103100701100d054139408600c429060040000281100b0000d8109209150860082043e03000844c550b81019040d00d094002848082280d5a0100003200c01040d22001402c3c10008801407041354801140303100030303040302c005a440108201e42c3c0c80220141942a600300061039208016401440e04903000c0340948240c10701207100902440e03075075182d0800c084508005510084c1c40001071502ca84104091140c00d01021002075410701900406084401c01040c81e580740401d8024003070324180d03030800d1032487c0a0f4148090b0310384420490980d010100007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 960054586 1250 960053336 960053357
    0xf0702031911060a23090a0603060b1c09051218030c030d030513080c0705040c1701092c010c17040507090515040203160e0307081f090219030209010b040803030403 72
    0xa980881d05560f110034178a0103039200b07041482d6800060180c001007039860882c5103403200000e500303d4040707004080700380100b40a40b245102000d030442103085801c5001040180541d078409203000d0165801c0c06042c540854079541c2d200c8004500b505800c000c400030615610f0080100341c41c0e0360241e490008041d223500c005500084c2c20f21183c601a0b03408030510b03075950003900c140c5840d421103005641c0f1850501000550640c030600c00c80c0d404c40110f0944089a0346880850001051100140c203540d03442d001f00002c0d040201420702c140018600004506004081c03002800b40d0400c5c02c0d0990178400c24028440401c0e00001d1100607030f10920000503894407020103406041401c0c8800035131080c0000200b0244000016805c00b580d0380c941c461101c80705c0540201070b2a4a440d0052a0b1190b1141c070008000040100c01500010a00100041c00c0541303600030070408500c1200381000024205804c004504203150143c0c01003040603456814075080041c0305032030707110180c80a000c22045101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 960055836 1250 960054586 960054607
    0x305090d30030f02212703030114060a1706030a0c17070f0b0a0806040b0301020c1c0512160306081b03070803040f03030507170f070203191106 63
    0x3208064000385a400d2521550448409545495550752040000d0030101c0a05181000b402914840c8095048100d4800705940d05000900780041080c0c905003400701109007a001c0e5a50440c200c42d20b60406583e80e036040030000012501c15210b0507004e20010040c91070300c194041c10f015507401d599100e44926480d4880040c0c0781038030485019020071800c58002a1500d02c003809034502001e81420b0b200b529542d07004000c41c3c88410312480031070352810812010003c0c4201900c6502120082001408200000100c1d003240c0150401c080349910403000c0383c15080030355151011842075850550710b01582210a0303c400c0700c0181c00800410340c1c0e4150710610034060741011014205030320444d0070410764a442c0b0b60f00501c00890303031030082c05599004100102c0c0070040b201511490840105404e01c2d50340c0c106c5181d4080c81c400c1e20882e2402d161410000d0180c0010b00389441405020746d10b80f415401014101090b81c84100400e00240d9529400074518158801c0e2020007126140c0c0c45903050305 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 960057086 1250 960055836 960055853
    0x60304050309100f0e0102060f0121050d0906320c10150f0b040b04050f03100501030605040308281806050405070303020105010b0412020607020a0302061308190305090d 74
    0x110a580300004045503036405911080e61460b580315982e03085c1e044070140006a03203410702540d0104040ca482c03001400703018124a081e035500c0211100c0301c0e00c0f02b0015199507062000c082d40b001c000803103100040010603405130080e0b0b1400e5101a00016601c1c00401015181c108150400030800000ca000b802c0c449044c0048401c504445030300340149051b00341040d0041d00f6074015400800c01420340801e05a034074100b03a03410341d2282080e41c0c0c50b00c0d05000400002c0c445402c40680d05100c2d070501d0780c0811410b8050340e40250700c945400710710350609260140080b40020111281d0203054a0b1201c040e0704541d00c00a80c0700c0c210800000d8415070b80500c01c11010311045c000c0c1c800c50416061104020001400d078003100d020394000c1000c3e03622941b040400d485039105180b40050702d507070a80054940080180000c82c4014130803000c83d913403680800d0040c4c000c05400d00b8512682142002843c07800d109080c41d0b03c1d010b4040000c0c41420b40e8000d40f07640103c840c0507024000c200200c500b00301c800c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 960058336 1250 960057086 960057097
    0xb0703060512011b0309030c0b251e031427010e0318010e030a1407031a040c0510020a060e070801110a0e10050912071502030d14060f0603040503 64
    0x5403403842145002c4102c607010341804550003030400c160a04108016204e40310314442c155159462213100c1c0c281d9122102d801c100a07151070b4000184a66034074066001a105184503030440d118a8003170907411001860a901c014940020b143c10803000180c4000d510340c006512020304010340303041000c0142141035207081d044085403190320313010705083c04040c00800b4144155480050156480d1447c0c01103401e00311400b540c507010341c44444c4090000799040300320042001c0520841d61310694030744652a130003d04100c1e0710354152404040c0405d1050b07001d03180300500420307140303151811102c240c025540c0c03545c034102030302c2e1640d1985404550042030001c10020020031000f4000703030400011960305c03030b40903c03041c0c00420154800e000c29410a00c2600401d0b480c50f171502c40c00c105415041c00b84a0001041f1320a05018000307000c14450040780224201c1e500c0c035030045841e0100708680e00c0450f1100854003240447d400c04118469554903c040110313882034604607201e0310f4903d0103900d5030044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 960059586 1250 960058336 960058339
    0x90403021e031c0f0b04112203050d080c0c10090b090a030918090f0b01230603010e07032c070f150c020a030c06080a0c1e050a0c0b01080313061107030b07030605 71
    0x101200560100b00d600702401d401d03408101d40e00c0103904204070762342c0f81c00e855100041280d00158140c1040c3c50290300302681c421100001c0e2854035a2a0100c1c84c00e00304400d90080100f5039943c8224280402085d020f80d00010880080140400c2501e029000000700d105a5141081d0190341d0004035002d40c0100600907404440f48100403c1441d16030403045003401461134a020020106041410381301d400300d02007501415280ca107074207102d803584400720300404040c01c1c1130f01c409240f00030040304d00020441e03c0c4001d06a00c4448040d02c2d400d404c14815a004551180d070b07102c42400851115a00c0146421070340c100403110900d11b20201d00e03001625030000d080303c00300013400580d042d0015040c3e40f00b042d41100401007565007560550f403031400c0c0d11030602c3c000c107250620325105001d0001003040320054109440c40c6e00340c5950b50181e0a00c00d030859891038102140a034103440200000d01e0291405042c0010f03850798911810b07603034124900c0060132229841e000f0840190181c0d0200014200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 960060836 1250 960059586 960059591
    0x314010504050c0f0315190e040f0f05033906190e03280c2f06040321020d120f11181009050a05120c090403021e031c0f0b04 55
    0x1800a103258401006c03c5010340641c4182840300c91600d40541d0745410780d021503564590603115230703c48404003c100031f0300712045000d400603c40468400c1015000710420315264003a889559920484000d2032004000301c1d44440c81709040003204041145640421810000c003464100c5070801c8014103103882840c1200e01001902030184000c4240440182d0204107a025001d803000c207086030001444c82018089003141d2648440d202c60107031404680a52100c10b0441c0340d4082400111070340c0c8150700c110303284c246070b1451000c0d541d0000d40400128070307140054500721030a1030000d0006c0760025005003c1030368400e070482c9030544076440310161a2403c80c41640326a800c4e501c90302c0640c0c0c00c070b81145c0b00d14540d130020654188030b0f000340800c0d608080c2420461a1401c03062080090407899603c0742030145045205103611812400362203240681e000b00310b11411020003c0d2400d80300060610190020070501400707268442c0c000c804c0345001480000c0700f08039000c2000040c1020914580c2c401e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 960062086 1250 960060836 960060841
    0x40e0a03030f02070c2c040c0509060315190e0c03030319091e020103140105011b03350112051504031701030506070e04060f0b0a020703061506030c0314010504050c0f03 74
    0x4041881d2184403420103990f106c410f20110841c01d07402d080310002c00c0741c142d0307207400c1c802c0c0d00300742024980060740034003111134a0b40308543c2040b000004484200b09803613045103103100c2003050301448490070040f4024040000440010a860340300007045010b8130300d840341000b030326000700364401c2d05101e411440cad68003180703004042034100c48201c40041e40024145a03101c400e401024107020704a8205844983da690f0030165482c4182d040101c0c1a42032140344130012019051580180d03400c654204450030301040303584c4500c8170324441a0401c07882042e0040d6101700107800020903c902c0c10f540380350f4103000e03511460110744140044101c46400e1209000020402500182407030280301c141d1070368958440d07076100340000c95056200304030020f00f08460820010800c140101140103462068070400350b16a141e070400d4070708000400500203c240003c000d095410700c0390441c3c081403464180919600b006090356005010301441f4804d43e81c0f2408612090f102001b1103050000d40c8011985a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 960063336 1250 960062086 960062099
    0x6151e1e0c03041706060f010f03020f1204021206010b070201080411180f0603010e0a06150b03010b0405132322030e120d0504170c0d061a040e0a03030f02070c 70
    0x26003113449024188100c0e1a404502090b011a100d0b100b1407015140d0283d02c01d4442c01110310300c001c0103100341410303401c021014240a20f840100310069403000502c0b241d04203031041c40203e000030001031245401540c018003a88070f000003110b4640d03809181c8a4410303101ea00f0301000980c60505e181c3e90001c090007410b038004034403031080ca104801032a42d010b80c680d80e00080c03609841d041d21801c040ea40080c07078080d001450a038040701e120a91100d200390385036103420303101c4007541c0203810107410000081410441c502c1c1a140f500100c002000302032051280611414029804042d40d03240c0e06103400000032240c0300307090514540d51801c06000c058884683c200a414004080c407098010718038030010365142c42c00068103510b0f0940360360b200d0380b83c03901d4081c8400e80c415450303155078010b0240c0450f2040c190360701c21005c42c0c0a401010009902d085402045c1d155100c40c5200901450400040300b000c07610100309010f40b02e070513060118000c8011710701b04000303101d00e99000341514000040400c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 960064586 1250 960063336 960063343
    0x120f0f04050a0e04060f0b13110912060a061a03070e0d02040c031e02040e0c0309010902030303190f1a010509060702090112051002030411101b0302010506151e1e0c 72
    0x32070113000c5c2040169541075024080d030b02540955a0880d01d4900d038100b02400c40d41c000f0826401c4249024202111580024403d40c0d144940d200c40307510840501010440e1031050350018540000640000c003a484060982408010515014407008501c00340380303502c8550710749241550042080001c0444500c2c080d0050842a940709074440400203400881c04070792080300e09440f0900b141c0f01b844c0e030f0360f54101c0e02d090b4001400180c4954072001c80000607141000550300490703144d1060b0030205804600d40e01120003200c01c0301100d9090644070400b191840b4080780d0a8074080c42c28540d0754008902042e090310420700001d4121004200003e00040d4400f400c0c05294130880946940e540b801910350145e000541e005098000c0b5803e51900914007000c0c040d90040113070909101d0303002100c00401e00101c80360802d8015035103c204000e05450059002002c00c894010b009042412a2080b503a000c11503519004d00c7d4540052010001d40f034841b919000c6081c011406070b640ca0f4203044d942d45 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 960065836 1250 960064586 960064591
    0x1050304020301020d060602240c0f1b01050108013e0a0908060a020a14070b13020a09050403090611032b060b070503250b070e040f0f140702120f0f04050a0e 69
    0x103070809c0c02d440381c616810100c40e8076018204c0c1c0d0002e00e05041911080191035449181d240c0c0045800c90601d030702c4403100303000d035278000c08080000080310940c102c03075904600c00c031074039030340d1425a1085003a007001c502d0a80f00114400c0308995039220f01108601781d50503001c540110403175100d01e07001c0114100507900106045100c50b034680c02c10a414450010146c090f2480c014411b49003040012201c0043c0c4100a9100e80018050b0400580c0c0315034038000c9580542c2c05500242d10b00c41c0c10b00c07000c4d801c50044950b4580d00002946000360042c124210740c201d241c1103107103920544848183c2039081e41c026102074a0f813905800e948480034600300b41c0c0c0343c0c0124080c40207122500c02d1005001030380c603400c07901030707420000080d9141e90720081140e40000386103100398807654503c4003d17a6459148949080d1020350040003e58400d0f1911100b0080c00041c00401190700a100101c441001d0030140c4880c10480c50001e1b0b100d400d01c01011106001d2034101c2d07504003a03052000074540301c425280c00d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 960067086 1250 960065836 960065863
    0x17060415081606080f07031a06040605030603010b0901152015090d08010312080702150c040515070804120c03020d062a0915110f0703050d0e09010501050304020301020d060602 77
    0x22280e543c406041d40d00031000c0702d64000c0038034a6030000314024002d812a0b5503030700e040000c100440340c88100041c00380d0010381101c0c00158011041000b6070409100d000c10081040341c1c4c0194070342c94000c0301001c2d08518000d0720100320100301d4040350107070b100d01044080401da5050322030b94074010440b2049200d08030784000c014490b0b680701012550003541c805050740d800807030070155081c0105041e1400000a44200210b202c0c0701207a412051044a000d07006030324800d2165a40d6160a00304210f141e40023010002c403800410104000514030400c5034121100c4034040c5107810003905206800c82616403004e0742148086004000f04049980a41032504607018012103283c40759491044501c04159842e010a070680400d0142030880341030fa401d09905480c3c80080d82619010f12030800c00100d51000044d80100e80501c05c000d4140041e1102c2102c9142042c1d1234004400000e01c0c540040c412581844030000100b401d544081d01145c1c020b154604c01070102c0c981d03911009545552000584 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 960068336 1250 960067086 960067123
    0x1a15090a091a0a12020f0402071a10060201150506030103020d0201171627060e0303070507140a060503190c0c0f030c0b33180403030c080105040c1706041508 69
    0x400c0303100e03200b0031401e921900a00301c0d0810303d0f000d07401e0000950103d481a00c00c000881c2b407286411980079140b40c4200b00c2184140141031030a07501a003511018040c403c1201038100041c400350301d4070b1302941d046070340440c1d141599402500050710ba01404a503000c000004c9a01005441041222440700058107a503a400c09422120070800c0d1013a03c5c101400c00c880c0e0300f00b5041114500c1500409500440102507a1034415641d07207407440c0c0b1034a540040040b0350450f5005c0028504141481c0042106003425032a40c079058640000c41400810700a03d4203079103c9100f13101510420801b0000c650181c1c1c6801000c0e11030030050000c0503010000ca800820810009800741c60001b10801d82c407900d00c038807130f800b00407074480c0c1c0c10300c19a000c91054004420442c451615198041c0982c0154001c0c0c40024504d44008001080904160032242c02503042400f10b42c40c4940c0b0100c0f0407500c4c0800c00d00703001143c6500b40040c0c050039110707086820070542c1110100304110045206c04894040c10f155 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 960069586 1250 960068336 960068339
    0xa020414011b02040c09080307030801080606060403050a032703050c2d2e1d0103060e2d0c180409120507050a12080a1a15090a091a0a 59
    0x1180d42048440c040010b041081e4001001800e141e007101c012100c00f4103060081c551101106407840d00502c2c4242c0000300307040c00401c07551100340141a00800f064808914050850310707003603680c2135481801000c000000503510041064591850b000b10b03040c41080b80c81a60780d08040c0c2c3c0e076010b040020345c8100c03c5810803003240c00036445401d45440703100c8014001402c00310100102d25085024581c054030203804403001d040419648644440c0307040c0c480ca141084414000145001604951414149410002d12a000e080760f905640804101200559812040000c0711107491107a03200289160110030b00180d00750040c0a0207001000c0c540b103015200d600703020002138490342800604203107030003264480d640d84901c0040007105e01038821030f200a00d465841c070504c204c1c51120140010605824465420483d02811441a40145940c0911180680043c030040071030b0151155442000511240239100d8045190040188040c2000a90104140402c000e03078000f801500c0340890b060b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 960070836 1250 960069586 960069589
    0x915031d0105040221030912060702190203100c03180501050a29060307020f030408011a100f1805040f0b0f06030103030906053f070905011409180a020414 68
    0x1000c1c46a90002c01700b1405112807039924440c10200381c0c01c005540401c00c10040551242101001144e0b881402044035140415001b402d01911101140e00300a005801c04050380d000199809410035034840090404140130003600200214452143d6221211514a0a009040d480705200d1001401d003480031000b80252420030001260f501d6170104041c02e50b505003030501d00082e5521484600480710842036001210345142c006900c281e540c0da46420000d0f2a002e595006c603801c0180980e00d074059101d80002c041c20801c042400a41000446030b1140781041078080910020400540300b0400c5140e200c4c240400340100301481801000d0b0700748089c0980c00c00b20121790480e9016030b202255a428000e04580356881307000c200203100f2680050b185800100001801e000c060a807103d00300c003c40d00050280c1c0040149107005200d0118020006640c0050b1902c3d4004031801c521965a06410300041d1040503154905454006c2082044541c0c84154000c00503544917088642c01054100c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 960071942 1106 960070836 960070841
    0x908070809010e1e0f06250533010515120604020d050702030a020c0916050903070b0a02030a0e040203190902031e0a03030b0315040803070915031d01 66
    0x14130100c06103444c41a9a101e44020f40b01541000941d03078804151444810484907100e80009041082002c144a00c40c00d0310a81d0320781c410b0005105140495605044003503181844c1c1c81c0340007142d98540143d280755a4860141500e161a05282c00c98a58400180c11190803903024400820402418044e4601c82d58450f0300868503000b4400c0024030380840402d03003e0003041e145080c42024000444100898122400c045030790b0a0440702281c542082540f2110180c40b020031641070b11030340800148100c211f00e40ea20045400c202d002c0004a01c030949124403120142c0c0302c4201015100d4100b441003a00050a0f0741c0240b0250801e09258081107000d0b81781900309200300010541c262140c161a0b40c42503000b0322008a50008010035880013810103041e40d40c0100000700c1261260000d04058003000008811002018030003070701400e011004105081d06003800c00f046a001403 = true := by decide +kernel

theorem cover : BRFrame.Cov 959892086 960071942 := by
  have h0 := BRFrame.cov_init 959892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 959892086 ≤ n) (h2 : n < 960071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
