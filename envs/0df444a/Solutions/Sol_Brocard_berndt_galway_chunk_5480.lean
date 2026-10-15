-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5480
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:59:57.515712+00:00
-- url     : https://prove2.me/submissions/f5867111-e246-44ee-a0cd-5f7765679eec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 985431654 ≤ n < 985611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 985432904 1250 985431654 985431683
    0x207090905100207030c05010b030a11060d0b280b03011d0901180605010305011b02060114040e070308090102060c040506070b04080d050a060614031006050702150315010905060304 79
    0x4200a04000200301e07aa03101e4a20340a5500140340090b101860280c1c07204907000c10941480ca094481004009100c3e03000704680c000021041e1440c0038441006861090311a102c6075025002400e010781d0315648080c000c25401201c18000b00038031602d180d00380026408990b611204d4030240400c1c016485441c0b03016400002d40c220f04a075041d4070120410022521002030707030b0100755802200105a40c15070b1603000520501509004030504013400320b18070007080b043d0b110b00075242c400600071011080700c51415400d00b90303225048540320034494020340d010a45d5a150824640d40088080750250007a0000180c1448401041e241100c4000e8400780c5070010540d41c090354040001c0040340c0802046c06010003030121071107444e00c1440c00b8900021001d0600c03001500c11020007128149689040003008801d400d5000e256044409605106440300d2552001518245104064410703016000c400c0107889409404503042ca500d0a886605a640c2c0300c01c28802c4500c41110007074030f00d007218440b1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 985434154 1250 985432904 985432919
    0xd11030c070303151a090429060a3005060d0c0b070213020c39120c0d030e010e1c02010c03050c010603150f0207050d0f200d020c0a060207 61
    0x1c44c00001e1044110a561a15594041d40a91800300e6182001001240000c624100340c81004050f20344000e150090301c01e084980c9100c40c0c50460030900800022a10b08402030003943c81300070300002e40040c543c04824200c0749000100698400d0401d890404010501900303100884101c0c11703400090103104541016032848481d03000341800c80e00008000100c4440050b24400380c490f05446402030511403100c160b50b0b07004aa0455504142000c1d0070382c0d015440300800b009055500b0042c0c4184440c00c0c441e003501070a01c001b00d041c1c42c1e0002d640c00030701000c25600200c01507050b882603c5139541d2090600620155410f40644d00661045c1c0e440107501640c001d4859404291007031600501d08030540e017205003512031a038412101419034407440707403016181e4090041d56042000e4114102112510b8543d034500031700003001c0034820f0701440c03034024511408000c0e00c0000300d0095540107600004000743d842603070040d100010702501581146600d0118017400c1191115070040140740c2c1008031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 985435404 1250 985434154 985434161
    0xd1b030302160f05030a0327080109060605042c0109060c120507020703081b101521080729010608040b06040903140a020118030305041a010608010605030a021e0d11030c070303 77
    0x248c4051848648028100e008134540001001e0640c1c140089050344072440e014043d0303481743d00028030035828503c0707189000c0070525907011309000307c0b4420a00f80c2d1003542c9180c014902840e000d4545400c1008070350f425038000888034024003031001c00300020740e26410106c4e101d5140c2d0200809008040003403a40b81d040c1420041e6211200030155515204061718074421501020359520b0b01c0c503d440702c20451221460301d18402101c070f400c0303107416145241d500e0640700d02c168880140b9801d2510680120074440c00d2000c103000d080c0f009996004e503164903018041a0f004c071002c07910016208000390103410640100040244c2c141c0798010b082c1030155850701c964000200c7ca8046640e101021465000c03080124080d0303500035240010302d41454144a00400442c1c1e550607500c080f440c0c01003200b181e00008407411540d20380362582e160740b50803c900020380704110500013071350b221801028411071004003c2c004250841c80422611003800d811045502040b81d0440c140d003400d002e104007280c001e81 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 985436654 1250 985435404 985435427
    0x6070c140706030c1407211202070809120a1208071b06020901090f0e0705180315010501110a02030c090c0c070603090302010612110d1b030302160f05030a03 69
    0x200e20003054012a140c1c80c00815900c0303032000a480d008001c0101e41c104503600a040f80514089103003440903154805410607404074204004180f190a0f600944140703490403421210120940d82c4803541d05250034640c10000100c0d1090803035201c120400d2500086000c0e03415070050481d000410a90015990401c00804000a001403240d414107003c0ba101c0d00104114801c200c01a10340e005203000601400345508289101d88400c102408030740910407100d40e01904034074020381ea501e000c11010004001000c0307001d4240c0310700c03100701039001c8800049034143d90082e85d03547c611101088543d582c41d40ca85802030340541100610701d81c036044c0a5600d550154183c120319141001e01405903240001340e0303200200080e80d6004e104c2c02c060303080c0200001000101f00c803420350656034513452055004101842e01c6248500c54000800c1b0b8400f900240164907140892409540d0303040180d00d0703194046000840d030100e10004151030b01000c1c024420b60b0300107002820409865503060b41c400c119038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 985437904 1250 985436654 985436663
    0x170f04020f011211070519051203100321030c0e18130c0305210304170a0c050105010603022a0601150c0506100501021b0619030e07030c030c08060906070c 68
    0x100c403c003510540303000d6102990010001e1581d52000b504006052030400d05c540485411515103240200340c0c0060007441c402d4201c0e0103242d42c0c1c1c49d0301c4a882e050100320b0b071009014840d42c0b42c8020039001d5054244450180e103850511151700408411075038440400703190741c1c0c010341000904500c082d001c0700003503105203104552913045040da181c145c40c4082c140d0040751594840c2108000c80c0c00001084034050060b02c001078150704060750f0b4407030180041000b030003100c000400c2c00416280b156160700ca000d41c1103030081059503140c4200a0207540840c0c41001e0561200402c61203011442c024002d0007140c00003e403407243d00b0b04040f030a02200d41d00c026001c10a02020100128205004c07a602903200011064115883c250000e424150003c0503502d4208500c0161403541d100d180803070b8918072128461800b5101d51034000d1b001015100d0362030220b4440c404011040202d0115040d09aa01560484501c25582c0440c1547c807903084403c03065941200c3e001c03e86a90141030503120f5148035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 985439154 1250 985437904 985437917
    0x91902032104050109140108040b150d03030c0212040f031b0b0d02030a050a02180f060c0f0a02040b0604080c01080c0409020304030c030f0c020609091b1603170f04020f01 75
    0x209400307003100009404400038555000182040250780240380c200c001c10b103d268040b4206240800a006010001c0c005007449400800042082000410b10044004003c0289a02c468982001401020803a60309009071090403a0407456014900a070b40840d1100ca01440d802410b580d1205e00303a405400071200c204421040210718031201801401c20240c190f00c0040e01e0b45404071220007034500182680564910400203c0d0003203950200840d04864181c40516002c80100003040441c0300352220400c0c00d008440c11080740250114201207900d0080b85c1c02d000800c002810840d06104500c2415010741c05100f011005500410401d907002c070b1803140e1b05040a13902c200d820b050341e00407181240002c2d05003441f0307030070160044e4172400385490320703d0b01d20b52454041e40400c0c0d0503c2003045035442055010009490104500c20880c0d501c0e903501d801644624030001a00455424408110701086a10140410301c004580c1094840c1402d80145070307154981d6002d00403441c3d034288845040100e0f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 985440404 1250 985439154 985439173
    0xc090604050d050a02010e010c150b060d0606020a1202060f0708070915051b12070308130f14060a0c0f0c0f1b030b2215061206050f0f09190203 63
    0x88040002200b54000c2010f01010405803000610800c40010118140311200f28050085045110300382e03903981201d9800518000480d00040300d07801b4880c00d59040d1800c1980202e4026030103d05241d2440c0708030820f50000c00c02090030780c3c546c20100c6040224855410005401912440c07000d41c2103022820640c0f820342e219080b444883c0401c24888012800024841135400d40078244058241e07070a40c0078090008026510140e41d10520201901b0000d15502041c5010f108481102e0760039444200d050311020030303103080c1d4002000042c054016016100018240a880380200100022a0390b21402c00300b00c4072100f91110340a000083e20184265884000050740546041041121070b500c014108c41ca5840d040b9004140140b41d80035110314000082c22080d0040e00303071082c0c3c0fa403191281c42180400600f180c0203201c030354044c15607542001c0d83c500902409502c03550080a502440c2213680d03807080210b0307007002d40503200d2044a174003480001883d0640240c00c00c3c0c0071807005007912055070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 985441654 1250 985440404 985440409
    0xf0504090c090602061008190c0503100605100518060f0d05010b0903071403030304082d0703171003021909021911150f0a0609050f0f0106170c09060405 67
    0xd8140101c54046001c1c114140051a0100009a80007480c5210b505a1070f00740941c16072241002e0b0608400790341c001e928502000001c40d9003801414001e004c440b031402c464280380003d0aa03a02c201ca0280d4140100c0c018164421021540d2915106002c00b19011071003060110a901405200700c050308140801c035442821401954020005a09880d40303c07100101094180549a0722000e0b4094001082d5500c9480c0401541d41c09600302e2081c43d12a0807250300c0c80c00c8038030605c4143d8111518076001d40450a1072002403c06613020780c0d100d13804207103004940b0300e01074003e40300c02c01d01861040b410001841c0204900960030f60040c01c2046e001c1d030729501c403803d0b41c20030001200e481c003078503118040c055408904440e08815000091a0440024001c40c000b40c1015012040625002001500002ca01d800100081c40c00c40c80c00c0142c4d15184011000b0360000340e40342d01c1c411b42c580300006506440f034081d01c500422070008403061600e40c0b6184540941c001c4140d540c000ca818040050b40d507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 985442904 1250 985441654 985441661
    0xa020d06270b130c15050c0f01050a0b0a080a020907051b0a210f03020c1903170106021f0b12061303030b030d0c02010c061d010c09090b0906010f050409 67
    0x85401d520780c00c5140010b10b0180044500200007090a80c442044040801c5a030250f403022950110000135404101203021103030340c401d0105034a81d0b0710844a0201c1c41d5201580124032075013409104000c00c5030000c2c108003040c0b40500c82ca40f03107a88040d0103e009460210b2180e508403e440c10b0040c5406002c1d802590318500e0100a9410b40d0010300c40785080c4020720002544640c0445441080440c800f00043d1150341403124080030180c1c007103504094142c081012089252180f14048641031040c0f60050014440c4100c1c40010017180303000041d007900000d02a21196500782a10218140f070b04540c1c8002c1411156159100740d01c4062000c07100381c14412a1300810044030036500306500c0341400742c00d880b582c04040307000fa404030f040c0c1c1c9940d80e4010003829540f642417a00c0c5031018403c7c1030060140c0145141c00000000009424641060551010f01c01600503119210380035521117a03501101c0940d010300707030001c0c1184c00181e02c0350320580b000042003455091241c01c127074480182c030084 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 985444154 1250 985442904 985442951
    0x170f07032d020a140102060a090323040b12010302010e0a08031803160b070318050306010312020f0f010209010314010e06060a050403050303071701051909110417010f06170a020d06 79
    0x2082c10135038410400d56414040f00303038040b641d10380900806800c0d41d0028070003c1d814400c4101c1d520070a45c041d003505014000c03a001000f000f1805a1120320f002c400180e1101d00303100c201c1c0850300392011280c8a0525011400450300342001071402e10007111000c1e0f0581d100410301c10750602418582c20601e61803c0100c1e805441b85007215a240d00c15450082c010b0f803100301a2104034004080f003000715540c0020b010307054079070040c8103101c0b5900125090f846c2000c4c122800c0498024595070702000001503010380032004d400d176000d10007648040300c0760b10180b000380070b0b15220300380340b00c0001d10a0800c1e0000b0310810741d141c035016141694a895084c207580098036a01d00107414210b00ca50981005040d590141801329a0b81505a042e41801d42000c2c01ea442611201c5072550800b060796281d07036054400920305e5204900341d00c1d000050b410300030141110081c0d010340c5401001302d01001e408942910028401000f800340e00c4640c2c00308040f00059880c00c68440d0b1311110410a40700150801018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 985445404 1250 985444154 985444169
    0xd060e0609091507120204030605070824010507081e070c0f0e0c03061e0d05010f1404030507031b0602180102010c020303061c080c010501170f07032d020a 68
    0x8050408800300300070500c01070320551840d8014290a2000c0c151208a00c0d005222420006070090f0307240d441102901407940041c150702e241c0010000c0c0c982d0005000c601c58500300081d6001220b5a800c600380d10710685a59a002907018402e000c0050120070003005040c5080c03491108030707d0000e0351003156921807041140c0601d05600200170f0300c004106000c001c2c0183d845100c2091500c48a55600c6005c000c00762031040917403072154000590b2011814603d2040600740ca030303d904250500a010340030fa206100007051030700d0080c09000386030060140c000ca506541d00c501d450b80580701101c941c24110003103d203c40c40110104006881440100171013441d14051049001c15032002a08590302103040c40d0a54100b0401c000841d82c44051b514030b406c1c069481180c080e456400c1081c91401090600c048561904d000450103107003911030850402c00000844a018010000ea991158100e01c40201192000c034084518107030100b64244460708084d01c66542030765a40c0001d0070000480e40b1905 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 985446654 1250 985445404 985445429
    0x6070b0709140907050703050313020a120506061516030e0301060303111903080a02070503120c07292701090c181a1011010504050d1704050709110d06 66
    0x1081401c0c1c050b201d084100101c0d64503105203401140900319102c2e8a400070100680000007420031440702003013200580e0054200403886440d1030319911440400f0206440314841e100010340646855a401c9407000001c404190403c240003078241100780c071003072048090007240c0840050503102441800000c5029580741a403594ac0503400074202044000007503140c89a01440c1804660421a01038101c0c2c040b6400503034a12041c00c1a6096000b0100c3c00901301015500f4000340040c640d02411031140910740b02c0c45ca00d000d2400c54544903880400a50484c1480c500090b0700010200a5030b1030621b00c10b101e0348156001c0c02d010b600f1a1403201045900000c3d07101d0501c503000c2c0c019a9a126240680f904000c800301050080b0501905241034034404c00100581c4040107100e84514031115031940c00070311283c1404c2c13034101d0301c515045050000080d09400343e11080480401d110740a83d4000c030191002c01c1c14550200060903542d07030420380c511380030440760080d00c0c814440c103001882d100e403080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 985447904 1250 985446654 985446659
    0x7050a092a181403070b0f160f020307060203070b1914040f030813380127020f030a1a120f06100b030a0515130209010f08010f03080906070b0709 64
    0x240c40020b22500705400700c038900280e00819880019020040d98200800c203501c844100081c20b0091140711405103c030f1030310700442020441302c42c4154480d10b100302c1c140c8440da6190700080f40e0b40e00403044060422900354010506407980c80c042600c1c59544248003240c1300700080e11854504505a604131980e180a54904042c1580400b0440e0010041040400700c0d0449844100b5040f4107849c4404141c924000c1c01c1d440214130340210104400514649086903940e4181c114a2124610381000035050701c030074404030304466208071600940a00e4105066858111005000f020320100003a003000d00c2c10f4040e1019038079460b5501c5450546402130400190f01446d003800c28001815604924400032410b202c0304020b08152980303c213001100186c05d0303440900c18070101c0000f800c0d0380e801048a140120310090070382c0080a00343c40a0303d4000d0800e05d16141250040024801c2d98204c00c0d50707000520000b030ac03180060124000040c4014104602c0b80c407865044001030310710a0110304403103800c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 985449154 1250 985447904 985447937
    0x30307061a011d010906081504090c0f0b040e0412021e010c020c1002070e10030204090b0a230703020912010204080607080c12010e06010c0f03030507090807050a092a 73
    0xf0001c1440c40c4a1441000900c50400a040c0401078041c12081c030003000002801038800c10000c00343c104004100f8400d040090418684500250040c1d4112102a480109100c2260000c0750203e87c6580100741c181e0ba00c0340c840f4200c0310707980401da500714001c1e222040c40c0f8800d40c0d4404e50010807002c00001e0185a0341001030b240247e0700d04214011219801ca031041e6507004a485000c640880640104036035560000d5800c001054100a520a15001c090018410b111800f60305c16044a2410403e60fa81c01c2d004291038035800014010019044001509140c0301c0c1c0c001d0709a48070054002c9168694004d42142607801c50b8120050541c404001c00104951002505402c1400070034128507010082e0007080051005004840c4003030340510200e07640364491040003040f1a08400108059610303032034020040c04060b02c80c01c2c0010b00402c0301094106d404100c000071250020040c3e09820f182004200c041c24032190042c070051009034005d01c03000c0d80c0c1d0901c205005920703a03440462103c0c02d4030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 985450404 1250 985449154 985449167
    0xc040c0c060614101b08161406040b0c07050d030209030c0612042d060c120903030606080c0c2d070f0603151211150408101107030c0809030307061a01 66
    0x84e0810008140002800940c02c1c080070110a03410102d101e5403146004412071491481001c01041c10f50900c58100d840d13040404c030399000e01d20407050000a525a424084c0b00c0740260100600b0715000712000f69000c0e4003d40c000e04003414050140d0f10b404d481030000440341e41201c8018543d04428200308005c00840e0038451508459103142d54082e42001f001d12a100c0541180091505585402807000d082c001c00009030302c111403850034410040389103030003405040c03940300320b101003814040403540741c503140810f48840301d0004005120364031100346090b050451030b0012800d084821081d102d0404418022200941701d48031003460564a080e00003012156502000f50860640071001e010322024a010200400e811904210309401c0b1400010035200c180041c45207507050000e13000808000202c2d4032900810301810420410414004140c0e07544102d400040008540c01c40741c40004140d06c0c0074002c2040d0181c1242d09000c0a540c9610844502d0950341d502c41c014203a207070b103080d0790010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 985451654 1250 985450404 985450429
    0x23c01020d27120e040905010b040b0a0810050c09101106010603050411040b030124060e03071413061508041e0b070c02060c0d0e10030e0c040c0c060614 67
    0x1901d10220351024002d00100444108010603101100f455407812902c00e030003040c100700001740104088070940c076081d8000d22403000214012820a10400d40624084001c0c0003101e041c403000c1e103c540d001c4003603400205002081c044081c03000b0300c41080d660f120f5980c40c0c030680b4216281d00340c16042501615142c414141e110b1401c06042c0b408010002c1c02940c03544074440019075000c51002041c03400213016200501c0c500c1506610702d039101000c0100181040220360340c5440d20325000ca400c0043c103440b000140142400710301400000c4405040c18821183e41c0180d07003c00203246501e811905425071105130042c800a078404003800305101e1801203840c0749200e0410101200195590340c0c0240c000003c080c50b003488104a0f44c0380c1035486100803589014280d10548052002101c1c1c00350404150409850003420b038028500c921500910843e581500c43d100245024081c250030400504000071407502044131001d03c00002500e83e01807100035000f1102e14070214440c007814002e4034071016 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 985452904 1250 985451654 985451681
    0x2070803040b07060b03150a0f0e010b030303040201082806060f0309020a0b03131b0608060a03110607142b03021201030f08090a0e07120c023c01020d 66
    0x104001c1110382d10910845204591182000c40d071505180300090800d458490200289029103041040712600e552042c01090383d4440c0401144001c0801d460883d20b8260509800d0b07030080010401540c0101e002c036500101906000c220384804558003ca060010b510b00c000710358495505008941d000b12000a541c0171a1804201c19680364001600d05040c1d03100f8000c0c0020000f001c25600041c0e00c8000999580210076a41104030007008044002c00501c150000038000d00701151803864401c80e81e00890380c203c1075034200c0c0ca504004000840c1c0c411081140e04417008441060700e40c4041c00140750480c1182c0400c0410582c070355504a001c620310070179004041c030400c03030607001d4194142c3c402d054a4008182031440345182c41d00c0c401e144114850f4690000d0031000000300c0e14501c1c0c45203881641541e98280d032143c04c48044000342c44140d0390b0300000d80c002c02d103e40d9501c0011031100402c1101196500d81c0c0c00403c100701600f9040d107000c0d0f031550f030f500040c00d0029044c883c0203d8070600d402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 985454154 1250 985452904 985452907
    0x120c081b030607080a02090301060320090108120a020a120e01021e07060c0c0f27020913050403020c040c110601080f061306020d0606050301090b0405160c020a08030d060602070803 79
    0x10322000a440e81070042801e8244050180803940d2285141e06407800c11344058001c000007501ca0500080085600f07080f60042c41d448e0001742c00310308017240f501c0d0403260758100505654042074030030705040d001040700340700b103104035004240401d06500d0200514043c0d5101d500200002d107000a040003010403e0050340b065405020003030410000d41c11084840380c1c0741040108826107000300c44840f9039400300c04040c0c1b0b203000105440d240c2c12601c89a07403d15800076107036014000415030030f85c01790040856010710909044c50700c0018603000644c0c40b07807081c41910001d03043c1b0300c0002c0484280110035000100c2d03408941801860400440780985140e900424074149214810703540c0da000240101c0031003c1c1c414101c000c008150301501da003e405d10b0418800c0648035600280590001d2246408407404c2422540300ca0409104440c000d0740f452a40e1a2a110b0450096841075201007040342c1090a400002400080c00d00140646d6130003807802281492400300d00a2030a00300d50040340c1d440d0130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 985455404 1250 985454154 985454203
    0x90609060112050c030312090601060e030a02040c12050108010204090f0605152a03030a060909050d050315090a0249020c01020310361104120c08 64
    0x20005003541129180c4960001003203030b51a0903400c03c2090060590148000701d1842480402d0b010f100c0d116458002c2100c0301e90303030f072000201d500d40840c03070140d50103070460314085001d402e054100c0103400314a8100007040c42403252141084030803d0340300040356540810706005030503050280300500d00f032440042c400c443c01c1000144104444a50740000c00900280c04080078517031000d40801d0141741500c15007000c1503540c00d1510b0303074400c83d0741000803894504082081146441640040f5030400010700c2946010319050f101980f001e048401010901e19456a00b6a03c070040c3c4c40c4144201a005625170030014100d011032020500c070064170110f1900b50340e860310071095403041c0c0c4541100c00e1514030368100c0a200f00034494990700c203000354000410000d02c1c90340b40010008446085607002b02101d81c1c01144821040100b5100301c03400b0210f66111000c604030b81108060403043d4840a10b001e50755046c60f90030b003c14002c1202c10f498040b408001240090201d070782030300d2246d03240011180 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 985456654 1250 985455404 985455421
    0x613050112090b061c020a030302060402031603030509040e0c0d0609022110050408040f1202091b040603020903190308150102060402010c020120030406050c0c0604050f010c030509090f0f0906 84
    0x300c3c02840e10b400389040e810101841c030b2042d01c2040d8480d0300548101c0340d140c0c49040007921203800f183c00b6030280c8580030095609080c11406075044a41558616050810850030880548002240c02e50144140d03940d80d034407542c0d1001d0885c400e0303208040024030304031640705010641400e40c0d0f07a1060010403030000c500e00f41380814030440c00804001c5c0042c1070b54503460700740c0c4140216046158040814034002c200807103840024600306000301c0364201d080c1c0c1e4143c0040c8106140000012060200748070030460300b8020b40281c292000f0003010b49001403410012903420014001c004c6c2c0002e25450248003803000603d8283d07250305e6003031000c1d004e285010b40000e0400380c2d89034402810043c4c80c1200c420824001001c0940c00c0342c0d02001e9950b240c0c1e9a031030043c019000403090080c54002c0740107040c01e030304d440022141107400160580e0000a000340054800c2864088141d003482800c00c4055403c0d44d0300f04030107224900c411a80c0c485070030604496540d000004114100c40e900a206000401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 985457904 1250 985456654 985456673
    0x30a0215040f0501090609110f0a0b090303072a0e220219032103050f0a050c0c0304030309091821110f0c090c0424030b061305011209 59
    0x550010008002034446182c0042400c1d0300075409000c55180100600030002d03d600501180c502801241c4c014600190401454001c10300410340c1c0074070754075005c000e4601184041d0807068401001c0e00d0500500351107034035100f080ca04090408021141c0544a00710103110f1034000782104a00d200000c2c031341350340d4003081130800c2e10500b42c40d840e4541a6004565440800c0c0120380c041c1d400040e01c40365a4545200d071048402d00c400d1400503600c544048681c481d00c1440d104003800540764400d0b40b9002c0c001c400501c4003034801040500100050186c2aa041008100548c800d03501d07904098a451510011100030f00b850720000c181800c0c000020030b41d003103200c0c0001000d902c607902c050103c03030105844610340c0a00105446c090281c2100710b1020118404107a13210955034100320350707510317203c0384460300c9107015880f059450220182a45100c04a11443e90010750400094403103541c40062401c2d017221034070306103e8604860600103540c0c841d080750211000d049050005405c2e980c2c1e4031580 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 985459154 1250 985457904 985457923
    0xc0d05160e09060f0408042d090c02340602060f01060302030112120e101e020c0325050a182f0705070f08100b06181c0204050108031b030a02 62
    0x300d01c03240c01700d8180407514003280d005044880c1a407120000e01c403920711004000d248232840c1c0d9803030b01c0400a0310001c01e00034038030b1030700c0c040d03016203050b4071000341c800110201c41001494140700f1403510000ca454203c04000608041d0700141a00d01d0b0610400c030042d08160088000c05005200400c003e200c900c40d860a555030010691070b01c0300300c0c0303003003290303000811a18071794004055200050016001419040c142c1c03000c103038810888292030004c0c0e030358985812886405601440104107150b28900ca0f42c1d00b1043c1e1140c0c46a011795540c8005940c00034240c0141201c10703014081800b90030294460b03c1d041c40b840c156894072000c1e162102d504c4c0300410300a80c8030361b114001240300400205000c0c91001d880c206a140c0300c01c40e11801495030b5600d40c06c400485040c6407150b070741c2c1c0909e444425078000030049848800d1440d548414084a1401c0c503010700e020002c0440c60f040161303514007441e4040c0c201a0000c6440f50b9150601403540807030212803919540080040b10050346d03011590029 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 985460404 1250 985459154 985459171
    0x10513030c2301051801061401051e0415080702011506050a0507051f140703060e061e040905010e071202030a1101050c01020c0c0f0f0d03030e0c0d05160e0906 70
    0x4001e500ca8160900b800e0302e8502246554605010804064400c5520900d9001c50308020481c0d55200d10710f40300000600e004460102c2c005000b0703051086d2012020700b0180d0100d40303a090030555074150b4503ca000c9a80d220b40d020a500d4004c0250323465092080c00c580700030846c5112080d41c41d2040c06415803142d0740c2040c1c01c00600150003810710400704175030140c100d401c1c0003c01200002c1707000340d4000c1100b0302e9240c244000a202141105210b4029981580c944081d032484c5500d605081101400ba0a60507010074540c45190413220b0340d551003038504040c01680041041114207135440c2c241019500b103801c1c40d4400c034416102580f800501400b046a0019990b41b11901e6100161018020b09406544660000403104240c01d004982000754030011707201e001c450b010500c00c1020381c1600220031500038503803900c4000403e1103a040002c80036000000d44070082c0c0b54070081071009010540c140e0340e030750045030300f424610004c00d15038008044407a800c0403e420026507054071103d01924104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 985461654 1250 985460404 985460423
    0x190212121b19030c050408070b0d0501150813060e03130905010501092103110313151103070611090a091a06090102101a040f0c0306050f060d0908130b0c010513030c 72
    0x13200600850455011309010401c5402c51a6a01d01c000181d0340400e1240c400c1c14100400050207030031100c44400c0566550b1a003103895940d99124015103100e030017003611010740320000004000d605100600c0d59043c1d0140d800240c508001406003034541c1a44901e0402c0030403c07040094041c0d840f002280110090700c0301200708e5080c18225085441e425040c4141c0c000007601d1500307000c55650140c12075401032040340501e40fa00e070042c0c610340d112204c64034164008000c41800201c0b990701c0420468084901e0354103014811000c2920141d058100c40503d40e511060b260104080b2003030902c05110865031145400f0740400000c2d19a07010740e840c03110840d02c8040068100078042400012480042c008014100c500001da20203400181d0034900802c0c9045000305140c01e06008a405103800034040d42c0c94207010204080080407540d4054078070290034489405200e482d400d4840040c5001200740307071a1019284010b08449020b0205076500340712003480d4000a03002884d4005c0e203608280c1c403a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 985462904 1250 985461654 985461671
    0x20111070503121c18110a150c15020301270903050415030e10051f081f020d0608012012010e070309230f060c190212121b1903 56
    0x19500f0300207018040741d899051000c1c400f0f001c0d000302d05c0c4200050050010000c054425024001040c132280074075900b02d049040d00c1c0740994001e000f0300001d14420841c140350740d9030540c0410103d810a03000707950070340400c00d440d4220304050041c0b0b4003448225807040103d6038299070040d01d248101d00c01c07031500d00c1c0102d1084c000c0c640260b110210000114060700c07401ca000a4080d0300038282250300c810b03003010030010b0301070410309000e0362030588002c400100090010b004076030011409a004100c0d00f59020480350404442034040c000c001c100450021440540d008140c0041e10355002c01d00101308403d04c400c0d00140f652050312030444444001c20ba1040d250040100c010304003107000039040c0c103007080c0c041d80000c1480f1401c400d60318900e800e40b500c01d58828101030310303940305481c040b079400801e100118003510513500d0000100b0207401102e40c608030004c041030064100ca10351001d090301c90400c01110195445d50504400740040d291860103000d02120318004050400410030143d070796106 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 985464154 1250 985462904 985462927
    0xd0b03070801050703090c080a030815031906020c06090a0c0302010c081b070603050717060f4c02150406020f34170f0706050c030402011107050312 65
    0x3074444800248294900600042c000d020703100f800315009024040f001914010224034460410340c160350750342058a4120340e01c0d40920440441035490b019000011301c0c1c016862000c020018428031003d621070401583c000c2c200080200803004a401c4619810300080c5004030710000e2f6542400d0a204005183c20145510b009000070991551103410034407810050019840c2c00301c3d4000c2d034082c4415691510100d4285040702c2c1c00c0341c400c581c004049401494003083c642c000c00d030080c0c4104040e0400d075012800d81c03101002c941e842494005103141c55500c690007102100070790421a036400100c0c1c1003000b991030314070400680201071070101003010420b07030ba0101c0d41c2c1c00c906182c1311a12041c0344030303054036110311914500e90404d02608140b01402c8904544060581c2c02261525004226261280301d0b40d03c4110303140c0b42164100030182c005103642c0b1070180038400f0000c5850326071601c0d1002600555003012001c07140c0e4001c003020805642c0003d619038009140384800384c0c8502c0f5000d007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 985465404 1250 985464154 985464163
    0xa08150a06120c300606030225020607020603100602060c030f16111014010f080307030c05010b041b0f230901170a050f1303081303050702030a32030d0b03 68
    0x741c460541c141c45500030078800d44505a00101c0204c45007002100e0b034803e000c1d402c0744101d1805503450200c02c06100d0100074229682d224007400900320518021407070f40018030940c000c545030948803100c0351040c0066641080003e6021a600c0707409451402c000b04050031080004040643c02c01590700460800da1150041078034411201048450312000210000c014180c0e0101c510f84410220000194002c2501c80620449030300201840c6004d0603601c1c111100e5101a01c01d0b14199210a04c180c52511a4801c010415010380b4aa00c10003440380d0004000303907a008002d40800051107280b450800d14400c0c0b54400d0307190410901d560340140001642d90500b143d0100d07150700c4005040041c0c1c286180c00c19449049469018045991541c5a020788420f040b54094000340700c04c000a082d81a6200300942d0f01c9001c1c1c00d10605224943d40001e10308121030324122029200001d81d421034120a14650301542d00314101d1038541c650504640781d40e80640b11003840c2c5191150301c4441c15440034007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 985466654 1250 985465404 985465427
    0x40e0c0a0c05161409040206250b3607090506030c04021b010c1704020f0a09020d1d0114060d060e1e100209060a030e010f020a08150a06120c 62
    0xb0750f581c500001c1a0014a44401d2003507604120b0b040075080414600f00d00d020b071086500900c42410003a503003d000b5010040c43d11019080721142100402040707a56800a1103003c1404070100c0800c00c484541000345c80381c0d51900301c541410000c2080c40840480c3c00c80540301249000103050b80d41d0000649440d141c01c02c1b480d0007038400102a00d1203041240307048504520000203004510140c141103544511103140e0b617103101000c3c8042001443c3c4840102d05400b00144400742c21034480008904903880147c840080070343d01c140004130701550b02c454403451600341c1c00801a8084544142c01c2d0914000c114074860080341d03581208102059000d004040110021560005d401442c103203c00ca415012030821803090800500646201c2d000f12951441d001e40341d00d0424409905c15809450780d02c0012a06540303501500811429500c0a0720000c84075541d003203454181003003c8a505003140d42036a025005000082c00059001008601c02804040300003034841510300089500c01c4442 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 985467904 1250 985466654 985466663
    0x120c0b150307050d030c110303090105040e09121b0d0912020f040908040e010f0b0f0406030207030c1b06080c030f04080708040e01270e1906060306140912040e0c0a0c 73
    0x106004e1042c541c0c4002550100c030301c1034241c1201c04080008040e030300e000d40c100941c0090b0782000706014810340001a250849020011144200790110000e11150403c40065404c0320b684411207840b01410800107034480c1c002e0030403404890400c0e41800d0000c42c00c030400b80c041c030f204008107289a00e031940020300e295003012495031141e032944840032941c442803080a481007501d0b800490560b0b00310b000c840819400515284ca01450314409a01a4000340390903010310904d950401d0101d440600c00d80c001d520b1219003c03903140d0405001a0a20740043c0407560321150505c00c10041d42c20311810030b50820380000300740781c40b8680d070720345091a441590091120758401d5400090207101981d090910440d1043e1100c89200107211500115200c5406004681d07001c009010803003d01042c0200c03a81b0300490022610540382c3e1500c00c02e44d400103000c400c280c50b1600c01c004503541c040c8400c1c05814100d4100516040c5003403044001d184005d004407a400324006115038520340107001a441c0960b00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 985469154 1250 985467904 985467919
    0x1c1505120309181b09030a03030b0102030705300903190c09151a030402011e230a020d08090a02091005090a0c0807030c080c0a0201020c0a0f120c0b15030705 69
    0x101c509840c0d03a100780c6030f540c0c41019a140d13030542c558120007a0b500012000d4018201c0c0f00003a1000c0307002d004500f05140c19030000300b1042012803020300c000c0380707008004110074140c802e001c0541040d148400c1890b0807403104c284a071801640d40841d0716100c900380c6201061400d107003030404440c10300050f0300a00c800c500e41050313054010320649010084420403840443c40c0103041c070041c00310b48811103009001075840512407255560700c003280c1021031480d02d07001d114a400b10000c00d80d5040301c068401c6440c080412a0800b1076810041162002420714000f03001c0e08019020300d54074000e4450007440740307004800043c83d01000545060040500030000344107400c0c403242c084010141c0d4070752440026440780c0084e607040d00a001d4002804075503a034100d101c1e0340f800320002c600d0300300540c0c40c42195008c0184480d401d900701300c50750466010300301c101034046083c0f034104d50300829000410240400c01800034085540c82d6a401d9000c500203200c2e2402e0340c5010000b03410f200540c2c2000b58004003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 985470404 1250 985469154 985469179
    0x7090e0313030b0f06010507050a0605180304030c0f0f150305060301020f040b031024050705011404031707170c1c11070501050f04050307080d090f081c1505120309 72
    0x40695138021101d610910902c0c0c0ca608004440301e2082410240c4258800e480c0400050550703072100e580004420160b071401ca812960013419a40543e1003a95000e08600090010510500c1d00b18014800035540309602850031480d14002e203c510346c00c4c003e06035070700001107450301e0039011210060360300319549a8554603542000419002611b410010441d0014041516401001c00500080f80c100d03110801a13511442103542c1d5005c2d4070122803654803104404048014052118029803098461242542242203480c901c0f0740010643c40411440e1001c42d0011107145039001e0f000050074480035582d0200ca00800c10ba8080082c000255a02c0d0514805400c111076000e0403d81c0c0c40752009000c0ea88450300c2c1c1c0740f00c001040e103010342103030420014600010038110081000c0d44040c3c0011812950b0381e111800300524000d010b5500d500002030301d54048250701d44503060300600180812600e8541080e614041080f40100d0b03016030900204600d01d181c0400c1503171201d000040c0720012108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 985471654 1250 985470404 985470413
    0x30f170d0e0613151d0105010b030f070203041d0405150709060e12120309120301090930030c0201021b07090506010206070c0f0c080f010501050306060a0807090e031303 74
    0x8040700c2141400e0044001140f05040d06101400c01250402d1038031050118484080d401804046001d0500c52195400e1203d1810f081c092240280f00000e1450b4aa140192080c01d904400030101011500104018484450b00104020707292007071401031001640c542c50414509045000309071112100a4100320343d1070344c42403104040e6481c03540c5d1602401140f00c00e000060208081e498060703000041503105145000c0051a80107403004c0440d061040500d43c41440c9a0081c0c02c0110b00903140d203c0f85061100c0758021821203194500e64812124105504100d03000e4940303171440815031035400e2500814030035010f0710303400d10a40000250780c6401250302c564074203452180414950500000940541c004070300705105402646030214070004954130640407408146003100c40ca90030100200b0a130800300080c02405186a0000443d03505003810035103490001001c5501c00c070f1501070140304604010482d5030894a4240c4007203122011011a24254066424010302e166071210b000004d10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 985472904 1250 985471654 985471661
    0xd02030102071209051504150203090d032d05031512011e0c0908060711150a05100842040f0c060905061207031413020901090b0a030f170d 61
    0xf09a42c95040c68980e40d08107002620b40080b11103114100148400c00120305588080841d02d000d40c41920f2414070741c08002880e086c0150300540021b0528418015140301410540880700c414404090300c0c81000b102c010081e2000601483c1c10000260340035031181ca503085820551114a4000d100307035410070341341c0c2130501c20240180054a0034484001c888034010300103081551003410151502d56034020082e180c82034400c400300c10b540f00f1000345c41c214600c0358001500030689800c2c040b410341401d01039070f00c100000f6085080c00ea00100c1460b044807020040c051180e0b10342c89054482242c10f0032545415100b0350441282000780310080004004c180801c450105105413104500d80d9220002191441543e000c0c16070404420440c2041a680240034168840018a800305a03000c42210300c4255280035038507540d08001124002c41185060351003035025020032003041185030312080014444c031300c0d981300180110019001c140d0601c0700400031042c0c0d0740b03030003450299250b800d58200c4005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 985474154 1250 985472904 985472933
    0x61612051e09150c0a0614091b130b0d0b0a1e06080601030b0a021902330c031306020a2606011d0409170306010305060105070b040b04020d0203010207 66
    0x5011030489400507000302809030b5071035100140c4000d00b094041658021190300007580c50040384903000050300020424081c8508101240a03410264144844101d2614404403c00081400300402d144229119240344070f070104484000031511b440540d011801c04040e0090141c42c102d8403100f009131068150f00440a64000c4203014000c82d40c228003807000701d951900404865800420040001c111125841c41c0c000c01080001890811840c100e04c410b601d001544201582103002200c1c0d024124405100805960b1040c0582d0b208601400540b1a00001c014003441880130011640303103800844c0c0101100e900860440d85c030b600111015290b40f40703080c0c4248031446101d200b1500207020007151802000c06031600b03680d4030900c00d0842110340140414640265540c01d070240482c103403900e07815143d2901101c1550f00c1c141480010709482c4010006030502c04208120f000055411209079445074000c0e601c00c2d02c607100c40c400110400032212010f0752560020903020140804210140300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 985475404 1250 985474154 985474177
    0x411091503070b220b040b03270f070b2503030207080d09020a0f080d080406150e0906060303030403170403050706020309030d050916030204110c03040602060108250506161205 77
    0x1807808050806220784c2c2c0111865884140801c1180c0b01e59440915002184404000652007141d0089200c1034116009503805510002c00002c90383c0c0f0500000001e42445210702e45000390069003800541b4502000108142d15240c00c0010306110340d064403e082d610040145e0f441003696900b40c081c01141c40300f0b9214580440000550090a01440d1f00721000c0030b02030315482c000c2c101c09a17074800004205a0b20749031111201202030103260724640c0a0212804495985e0030103084281c41d00b400245082d01a500420a02000c26004469015420400500d151171596980f40480c3c039801050402041c0c680040148850006c021010b8010704131484d03000c100070343d01d40e0603142e600d844040303007000d500d0150070b014809401d0a030000c60702c005138200003903e03040d1140c0020703156038045e5010f0360060700b1403401030201d440144880c0102c5440c00f00702012817840c0c10038100580401d4492107110b040c0004503084a03a50307082005101d10381000746801c0d48081d601c0c000d0000ea018080849 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 985476654 1250 985475404 985475437
    0xd02040e030a1206080d17040218010b0d0614150705030919090b0d02130209010507050f06060108010b030c030a0216050f011a09090a02041e0e0703020a0e0411091503070b 75
    0x11891000601d131b1114000f01c0e520303402e05030318030412041c2451014005a80010b9060342001042081003035542c000e103018030070503a8031b840f4102400115502c507001511031070400300c40e1401d00e0307442039002e0010610000420b50f40d1a05031801c02d1441c480e045900da080288014070040303051001070350f401150301c6080184104900c44c7c0c1000b051101111009501c600e0040f0300146501c150383c06000c80c04018103169107084c0300d644500e0715040b0720100803900c0d58081e90411503256402194680107080c500c4440d400c0d07040810141b1403d0200404941c0f80340da012500460b040500ca00c8140415000000c0e04c0c104a003485070103001c0c1c0005074018a06804600c141e440c0c600307200c140c40d8491410b00c1c003d814100380035800c00001d00034043c41c0c4000c0382d4090f07040c0c071240d5146100c0c0008002c0010000c1040a1840c0705001580303d0355407100045440c40c10410020805101d0f0501d10b0a0007160b802c407042e81c4403098000400406007040c0c1c0c040c82441c401250292101005180000c003000c240b6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 985477904 1250 985476654 985476659
    0x62e21020c06070e0f040513050c0d03020c0f150304030c060b060f0706053c0114031020070309090b0a053a050619020a09050d02040e030a1206 63
    0x10240d11461100040951080340042c40d83c9108800010a01e480203103002100076040c00010103440050b651a8640c841005c0103004000c000c000030804110305441c042c01d94805a02c020b51142c4000e00202e024013071507500180b2503a50000020010303000c000c19143c0700d00340b900f4002c110942446c400c41c0e0044c40c00700b0b85443c42c500107064803a210054009245010040e92740d01d005032001512622156a001480c081c402050954540c0e0341c50404149000740c1d42001100c01200c00b040c0c0c01011801c411100c1d4641540f804582070100e040d500c4800300ea4050b401800d50011410308604601c450808608201010340c05010303007089400e042030070b01070441d0034000c000d07051200d882043d602055000820318006580d0050000b15404c11180c1140640042906659261000c0044456400c280f040010509031070501ca17000c042c000b0000c60503c1c802c134002405015240c00345500c1000300403400030455540350040d04414040800340c94480301ea14002a2601002040401607682444000f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 985479154 1250 985477904 985477967
    0x3120f090e0115140415020d021507200c060d0c031d03071704180b1306080c061b0f010b100c0c1701020702040903180e0f062e 56
    0xc89060700c58074030848803001c0f003004040e90000b01c0c030b983c90781d6460300038400019489003c0a885a00c0e0307480b50042d1240c41c0000c88003e0030041c1c8802c182e803c161403071080c0440e15034000300303800d00e0f0040788514081d05806242e500f850100d0620b001c513404100001e410410607500c0d0400150401c1d5038809100d000c0c1250300c0c000c81444070030801d5020f83d02c107002c02c0d408104502a000d01c2c0c44001e9103000c1c0b40584600e42400c40d45500071403626015240d40a500c098104130a03148100318540c42c0030804076042c50000c03500e441d007401405214260104010f000c22068040d0715201c0720420b011038041030300c081e103030601916909541030310030006c1486071240b1602404145114581c441c0c80510b5140c14100400d45031020311450460540d400c0c8002c10042c0c45602c2085001c0b40251104c503a4055044211954507481b030304404102d090000c240441d503e207144201340c03c0b001c101c568850000d10308200d40e105402c3d81e18101c8410300541144601c1d642c102c610204884000000318400d00d47c0b4400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 985480404 1250 985479154 985479179
    0x60203090d020108062b030909150527014e03090504051014240f07020910030209070507030e0f150a03021305040c0203040303030905030403120f09 65
    0x160140c0000d00c1d14011001584a0719400780d020304003c1176585040e00381503002072560b001303400444c00c0c05100c59009081c5600804613500034001940c043c082c6244229172040311051714071840d40150001c901184040c4c08004540d0ba110b074250815894643e5545100c0c1c001001070784190b888000ca9814003245141c41c80212500c4006020f50a034448824113150a5a030b40a14020f900304102c42c6030202e02560f80380030b81c07801840b0408030400044c0c20406e40c0f0701c035140320b03001241c46030342028038990221151841d030280c00050740700300395119020100307412650312801c040254488030301810020003100d40d03000d241c00e4074001d0b110340e1419036514600741c074584503032000034000c01c0884d0132243c01460510240c03100f558018111400114040c003000049400c201000301c0400c0e008900e603400d2051040070304005020884051041100741d5801035200d1080340405020591922241c0f001c2c001d0420440d8000d55005034240f5a070130021000801a42040700c924000482c8d400002881861024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 985481654 1250 985480404 985480417
    0xc02250b0301170106031403030403020c0901060c06020310030c080718090b0402090901110d0b0f0d03051213080301060c111f11070e0c1908090303070507020f090c0c07060203 77
    0x440c4149140d00308401039140c0c00005540c07091a6403142c4003c0300164082c0d1104100040c410002c540724107052801900308422080160300426694004001403a44810540071880d0803d2006035241c0b40c0b4178000104c041c0940018000034102c2034001000f1100041c4181180c5146031083d40e4461070444140580d00c004038042c0051340d6040205003d46098100540c01603005000081e1040302c0321104100c41e00900320300d50310305646140c0c000aa0801d40c2d1003c2076050116898a01c94016a5001d4850702440c101c0301481503d43c00080c40341c0c10141224208103411030b203140c2d01c079030390f0301d60003003601841c48000c40e42c20740905d076115000c0c1407400924441c10313142c80007841c0c520b5038030fa41110751110b00c0e00c09400f18450301400140e40784030703218802e000b0030310305c09456a100d40101e05108400c49010400c0b04014101c030400009000c04001d5075003060355441d00c0b550f03600040c00095031000b409031800d60320500c5a0240100401c0700c03c020303e1801c044a06664a06a56160903030300c80c011103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 985482904 1250 985481654 985481669
    0x150907180b1e011b06020a030c0305090d080711031810031523060c060a05060102060403021c091508160c02010509060f1c09111c02090a0f0c0225 64
    0x4014202c0030340c03403030052000210418036140264030451141030056001800090315801c3c0d00003115840b003941030045000446090806012a081400b9111b90b5890a140c20f8420030208a010902c01882070b690540c10182c10402c8a072101413000800c0d50b41c01c0c1c0d020b4500d2150b040e241c2200d402030f0083c0641540c1080880c20303214611300e499844031280c500f283d20b540c07002040d00d070041d5056840d00082e000e141050002050285050200346007184c0001d0101c030b040d0350202c030800c0b0000b035001440c01c2000144a01364141c228480c0000c0e10019015000100d03a50810005440c110303070b000e010f0601c604502842d03445640b02d4004103460300c0755204006400034004110070b017040e043c2100140641912402050700d001c03038425102580c0142005a00c00c40e81c0c40d00d41d940140070580c00044211413044070b107030780003c0c1c400120010f14055107030000e015441580c0061140f4026501008081560701810f1002d40710b4101e00035142c0c00e0302a01c070a11050071030381e68400e00c982e807461241560035a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 985484154 1250 985482904 985482919
    0x9010623061b0313240302120114010c060627020c12030606070c0803042d0603051e13020a0e01141c17071a0c0a11150907180b 56
    0x42ca07a0b000340030820304001c2e04540320030448207600f10152190100208024550a2808009010070306070081000c0613083c100360041c400380c6540314407154542e046900c4146d18410329001140142c44c000d030300103c040c01c014130704607002551420718112a03200190256044042c1e14058a042040740035200703000c40243e00444810068110590003142c10100041450b0308000701035a036119a01d2068002060603040803c0c104200d040d91000d40d08611150554601c4c3e000d01e03500c0c10300091000f4800c40080580710008030705a0820059641e103018580c034506001c0c0c1c03810a1341d181b41c090501c1c1b0200c0c041c0207007000020720856030002e1241a500c00b1003408440e600098104000740f0310002c8402482640c90101000091401e0384840c100e601c610380203911507c150900d60614140b08000619815208080005900c680d504440b03007101c290604068600225402c2445d1030082c40d102c1c040307080690180128003100040c640202c50980918100c511846000001031720440c20701c19802501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 985485404 1250 985484154 985484167
    0x311030f0c100c0f050d0809030910050d0b040f0c1701080604030c0c080f1f0e1f1404050a231203250c150603030509060702060906030901062306 64
    0x10829841401c041e05841c24010040c1a138440720702d4024008001ca5036540103d400e112070030b07080040c01e40d0248518010f1070614101030082054075401817503440c01c02200140d00b1b0740c1d242403580860030071040078004000a08010300064006c100700c507608004981c04502102c40d0b00c0c62001d14506840d1041c01414154890741c2c1c0684004104c440704580b064220030f17010030700701001c10440c0124040c500041c0a200c000061004601020482034008542414075200c02e1110000308400c280122540103803000c806082034a000b4035812001020000518092100744000001c440030000d004910700030720041d041d100d0955480e0742c060049015000300000105004d126000f031a8032080300c13190804407420000740d010442c103810b4520b8011440d0082d5440601810701d5012141ca400c10303204000c55400e5840c06052800303800c04c3c05110b403400003140011134940303e059440044014104907100e0904448550103010706016014070b00c803c1403602940190f1101101085900141042e442c040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 985486654 1250 985485404 985485409
    0xc090608070b0a02330705070305120c190221090a03080c19210e0d0f0f0206040e0103050d140306090403020703080d230115050d1103040c0311030f0c 66
    0x704442c0030001940603901003840c6180e2000040400c08205c03044403444a074000200e00d04c003100c040c113800c0411005008075000a42c0002c00c071551a00340002221440e0340700e007520000d6110b07803455200c0038a08603041150080d00041d66030041c60403032842501c248040a04043c86005408140d98000384050040000c5606280100105802c507010b0b00d20b454003154410110500d01202107408010320010701159041100c9111900440ca16050015001840000300c801d04c00794400b0301502d02001105040100d00c036418080f0542c0a4611510742d943c40d5242c0085110901c400c1e02c41e4003440c90006e010b5131040316a0070400364042c0e41c50707056886500c10720251030b10041c011400d42c070804101002040c50300000c0c001d440e071001c001042e4a003240243d8000600d07840224030349845c0c0e0360014480000604003000072078040b0b1401d00d89400341200d01102902d00c80b0000803d048001080c08103022000d18408190f80c01040e2480c1c3c190b42503020f05994141b0061003194070342080c0204040e91 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 985487904 1250 985486654 985486657
    0x1021b1c05030406092f12070b0c210c07060e03150603010902090103060c090f08150c04120804031e0b0a05070207030602130503070608071d040609090c030c090608070b 74
    0xa0090000164028017581d80c2554001c04a04603110089543d410303035052a40d03000c150410078407d0740c2c80e0111034800d0350000c1c0e03241464001d40744424000b08a16040c42020044944121820305105040c141c0c01907401368203500001000420f0300070f425001c00c249014843d01b03002408094001c01c41d40040103003620b40c1c124041d11103941552181261000351783c0301d000c828040d40c0103410010f01c0381c04100025110003490740c00781050b50000b400400c101440480c51306401c685a8150840c2527817085207040740c911560f004414100b0740101d09100b4045801c0c094000e591248000341ca2a0004800105440c0035000005042c0c1d002080014004003207a005540c00500900484600e282c60355204001d0741c014040ca0f200e144500c00081107185020000600103102600701208a4100f102e8002c0400380d01c01000726440074004800038158480c1d9018600406c404041003046030140c3c68150310000503031000340c401c0d07400c20300c0c0420b07488540c4c440d03c0c04540b8810000c00d2498a4840d528045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 985489154 1250 985487904 985487911
    0x110f220b1806030c0d090308071107080a0609080c07150305011a030402010c03090b07031206050d0f060203100f0303020a03030c08010f1701141008060a020906093001021b1c0503 78
    0x40350030301021070505c4850003001c0ca030500c2a22200098a00414000c1401d80205151061380d80804802c10009001140d000546a04018081414505070030b10200c0c0b84035086001c1c007a48100782c00001c034605454004260280c6581d000d10450740d8500600b08540100300c030b500c500e090204080350041d800390840c0c91002c0e01c070342050100380d55030341c0ca00c403090303040210140c000c070703020311070041e03030001c087c814103001c0c010454410220307a940341c440c01609500031038000d007081d6000000c240300d8940300d56040300502c0720b20020300200340c5074540203440b42e4001204801080c2000d03403a4020500484815040e10314800040c17a10b036251210080d0081d800c0c0b118140155641c040320342c02a00e05800361403240809200103400030749045144ca00e01203008000305021481404a00040d83c2e50f18103e0b54004c10880c0c2c80c00da107a90b001420340381e00701c1114410f6290200c100062082c20810b4001d072134540c900045529500004201c080c1c2c03103078080b0b40d6981d00b125545159110a50181028580 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 985490404 1250 985489154 985489171
    0x242a0d0c061524120e1b090405060106120605060f0a020c01080f0610030609020c25051302091201051501021e06010645140d06110f220b180603 63
    0x403004c058141510484511843e160a250400030b06101c0070480003401d01c10a40d4103540c20308151520791211515104180101020401d0b140c041040130142600820054840140300305c1d075510b4503041c0c0b5496640208500b101500840c0300c0c1e5491580a80c01080c03040b2160208001e150707503030301d081050f0900c1c04a01c0c1030a00d9543d14002c606c064541c405031100003041d0b0024441d004070840740740704003c551001008074148465040c0010380b00e042c9841c0300340024080c00758a401c01580081c078101c00e9003111030203961821003003010030b0f003e8100c3c5200019003a009e8550041102a1a16a80c0070340320800c101907000200400c21103203c0c0c0103c00901c4810440d07511500b07031400001e4840c11604071070b0b200c00f11610003070340c603101c1d0068001d01c01800020f0304108610704c4000420a01d0400d440043c0c40c80390703a5520b0440d484955401c82d180340064144503580d032100c08003194943e0703042220711101c49008680110b00040070030304488400d0580c14207540303071516000c10000150700003800d0a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 985491654 1250 985490404 985490417
    0x13020f060c0a06110d0908090a1e030303090609021314130b0c0a031b09090621031107050a090213080607230f030c0306242a0d0c061524 60
    0x640c1e4480b031b2007a9402d1070300c5030003680e950301400300400803a0009500456400c46042d03050200303040c0d031451054210fa525040207d401c07a400d050440040402c1003000e500820200c5d4051342c0c00285500c05d814241d81e84220b1001da80783d41032901c03407140171140014603d0f13000402241840c55460301a180d125001c0c03030081101414000000200b850400780440460b0b060b000902010003036008020150110032100c8900c0205080e8050007001e00c80809014820011114446044140200d90143c00040c20b24140c0e56600c0561600135400f0340c0320101c68426082c804103414801046a50007000c1c2c0d561450101100c040f1052040328904034140800201002480d0115007c1da0203144250208103500e81c40749002c905005032445030480c2201c0408131400d005829800b40c1c0c080d294442c148555000c101d2010041e50b510004114500300303018421a143c50140300c0d4080c0e807036817589104007014410820002104c4901050b00c2c000c81e98420f08043d40c0200011445111041d101014038045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 985492904 1250 985491654 985491667
    0x51e150a0b07050106080c01050706090302010e0607050d240b0f07020d1103011505090106030c030b12010203060a17100e03070b2706010b090f060706020313020f060c0a0611 76
    0x1651000880c0d0210015001c0400d1090038400d0030f204180040c10140060080d20301c0c0032000070524484e052004207503030740d140d00710002e05100b5804002454601c0b0100d0b02d007414454805401384d0418142849468145002070501103c4c54841000031229105040c4c0032070700300b00c001039990304055031880d10070100303000900141e5203c8100c041500d00503a00a643e541d5240c040c5407d55030140c1100c2505000318204000c6034942da040f450444d5a1444c0005010150710001c4024064504826600905c040103400e40d00701d044d4015402500100e40015420396542c1002d00080c0480c02c1c0320b51103800940d02c07440c549110f80c0004c2c0048014406591506405035030307203001c281c0241c5440591003202003c407036900c510649803c84075882300300208002c0d890003080d1842441002256402840d524032403545540f201c00a4810803580001c095441e80b50203130040c007600c881510140d200c0c0040c40a601c0c01e03410450100d902c01011100508000601030305c1e010b0103451450701d91490702034100013a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 985494154 1250 985492904 985492909
    0x305070602270d03020a0816080c060a0b0909030f071a100f05010c0804090c09030b1812182e020c10020d08070f0c0c0905061201051e15 60
    0x70b00b100752801c940c0b960040003451000d0740700300440941600440d010039a90b00425000079241e030015501007441680ea00200d0300d00320f0243d1074003070018400301c4080703598400200302198030703881006000d100708000e44180703080048021701a01e940f0f0740b40c0c008224000c100b0002400400342e0074058042c0c0b200702f085580b01c008100c40210340c07282c40c00200900034803111500441c03100003800c0901e480980d180c0c50782c5403100c10340704512501541e1981c0f44110807030b281c080c80410000f1038101d2080d5160b85012040d5404040184030030102900580c031070031011070405401d0f10244400a6842d21548140308140592004151021120505035265210300c0c54070509075604c2d580810f030701401702000a40140030b14800301e001d641080d90030010b0245121980010790541c010481d2500704911036480d0320a81d0540c3d200c09011341a0750080c40c020a14440755082580204829518040903001240d811030880340d0940c2d00c024458941c0311811086c0510408030380c0c008407080000882d04501800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 985495404 1250 985494154 985494157
    0xb0c0f0703030b01030b0103020406050418110a020d02190f140f1b03100608120d1e3911070909062405030c040c170103030801080f0102180d0305070602 67
    0x28101c1c00a6103800410300d46507407501a03503e120000307003000e40c00c00341094000380860045001d00404012842e013039070031b080c2e483e41001950300308441c82982c2c2d401c18604025218945039050300c002d0b210f4002407140350105400784585c0140c000000c071800c040c0d955903042800515207488903592280501150100406120200181c541103000700c062401000506007089031803960f0019007480c00c3d000700700b444030205080d2440080380c5005c0756501c0c1c00c00d03000c1d40101f400601151808108800e5800d200c40281d000400340080d4039002d41c2500d0215880c00049040c02e622164a0420106980c1c0c40a0040c4181c9034904108010703600110b448084042c12a50340c0c18007500d0881d00c0c0e411100b00f814140c011045400c081601c030144040c03c103800300b55600800e901c41e5000e203a1300c034a21000b540c455101d03c2400340c100703400031703016503520706005002e07200a00924210f8000c511410710340a0b0144222520301c1418054401e6424503034003004805800300c1c0d026414410204880c1c40011512310 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 985496654 1250 985495404 985495417
    0x30706020607030c080405070506030402150706231003061d0111090909030403050718021605060f061e0d0516061d06030c120613090f1a0c070b0c0f 65
    0x240140070a2601d4075000701504c0d4030b0140c07541401440c500b800040785022480b81e0959205032034040c2d4945651001c181903a10705850303405400d2021034031204010302a048141070003950070b03c00c44444160181e8007400c0c07400b03039860750100000000c03c0001400d1031300aa6495052150070b43d5103c6098031095080d20b000c4100303d446200c001500466920702401004d130007071011802103040138150303602c030b540d240f1a0b8055540701110203514040025081e03011500d034412109860b80d110038440c5002c6650790003d41d4114500703030700c8100003100f504003280320405524140d000e0024481d86c00d414046110780d03841050300d0501420103035400e404124542d00004100650722200300c420650040c1c0188282c2400080c030480f010400d22401e007241c90181ea4070144c21100a080383e40b90007000414500c44420840951401d00450740c040c00120100c50625a0182d1010383c4800e000002030940308200f1100c41071100b01c10f002920100b815400c0942d40700102500841c501815180141034507005070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 985497904 1250 985496654 985496657
    0xc090e010501030204150503060106111227010809120f0c1507080703020a0e06130503010c12060518040f030201230603011d060c1312030e120f0604080702030c030706 73
    0xc0780100214101072146030b01390410740580c2d185c42801c100000f078035804103100300d1f0200446000d02c000c0214081c41544021620300c07403400d9aa02c107600c9007007000800d40c04250045414010001c10650095807418804c0a04c40003410310360249030011495500442d8000f844060240070000344070008011500d0032029041c00d100051030101c10080c090440140003408050050101e000b0460300416040c0d050350084640d0340d22103554201d001c400310410f5008a034598240400034401f5030b0081c44445420002c94024001540c40d0750a012a850200c102d020001442500040202d40740200c0690028460700c0003007070701810000c042c40e00100110091000300b6009041c0019441e003482030f044107000d000d068a441c20050031250761201001401441142d800048032003002186c3c29203000034007655204082c03c504103080040c080c4060340c0410b030040400c2000b01d8800034000030b2026032061804000c2ca5240d6450782c54031030315080713600100d81512501c3c1280081c0c1c3ea05101040140617103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 985499154 1250 985497904 985497911
    0x15090e01030b040b1b07020f0303070c140112180215040b0403060b0f010f140c030705030c0c1005030108101d03071a1b030f04031422060912020d0c090e01 68
    0x213090852a074040900710702d0f992800512008031801458080d204055011503480700c4000000f008030341148070b03141d002013130400c000201058482980018504004084c1d840660020601b2840da040741d080681c4140c51511603010303c801494140301122140030a5510581050b41d0340703001008580041d08121140c0da00d0b26840c0f034150421100c208000e4009180c12030940d40000c1000e00140c240c030303142c81840280051a40d100300c008000b19210160301c00c04495542c1414607400d82c844104000c41882060311000c51303000c003440b0300c041c2c0e81039568900c00341041c6080080f03600b004142c505500078403024601e503402e06036541407000d001c400f070180821102c08024011049d00904004000d82214040c1b040d00d88859030080084c0c0754005400a44d5541c580c4a80c102541d0400070466100710020001892030720291700030000d1400d4544403401c4c00308030341d100c0c5000c1d1404207050040030100e168003214003003d80b80407122040610301410f110700043c2c2e01c400e0720700f040c2c0340101410341c1c50342e44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 985500404 1250 985499154 985499161
    0x605060408070306230a0b01141204110420031003020406030f0209013c120f0b0906010e070e04090c17070506070206030f15061c0e01110415090e01030b 67
    0x2c0c01d002c0c80a20312480c07001844200003009a4810302440901b8640c1e5507650341f9108070790382e400f07a0303541441105011250364641c00c540704d40611000045500325400b46003030b4082e10203814903000350000000c00600c00c0c8000303081d00c440302c0d0140d00003d010700c043c4c140305100040540c441e441500c01960080d10001d04600d10f500500c010344cc81079001c0c1d501c0507100041012180080d0070b07040026800610b07200c4045001100010362002c82c2d03005117080d50900d144c07005c10482c601401501d0148180900c1ca502e60301c5500b0181c50389002d114002410041100050425226074601c125802d0001e000085440c035a80704c41805501c1c0c0e070003000c100d41019100c1d420140042101c600284001c8403c2c61a2500c29804500e15000c0940403840170000c1d00b01103011180c20420480803806d020b0007480d12002c0d62401c42020718501000040d03900d25041513a00342c444107000b00e1254040d071302c40d007900c0c0c00d1416108441d411412403c0000304166001c0c049460300381d42d14000e0081d401640100400e05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 985501654 1250 985500404 985500413
    0xb040b06100c350a09060f080106080c07050f0d0818010501050f090c0705011b0806090402010207060f0e090907090e0d2c030f0a05011805071806050604080703 70
    0x321454002e00c003060044000056031501a07400056090380d004400004400c2e50000c42c501800d68409002e40114040c00b141e940000203100700c548581c0c810400281c00c0714165096170382030240400040b045000102c0d0010040700410765240700718101d642261001054078200340c1d901d05c80f000021400000c0c0603803607140c400032990056224008102030752500c800135020441c0801e145004000401c0084c1c1d03170200607001c1d603000a130014024031190013a0704595105115000304030002c0b4112a0206000d0b090016034039118a034180c004000c05030400358255003404811000000f0410022103910240d05c0300d141c528083c4040070000c09602d0700301280181610084183c15034a81c0c011542c806074030350f2185084550307011103400c03040d0b981e40100308100300b4884ca83c00c0740d4040c401e0500174000e038038000594006950240008214010401000b00020042c910001e061544039180c00d20401408001e100b01e2900c16890001d103181d518008270314244c100e50700804068110b00000c10a00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 985502904 1250 985501654 985501669
    0x60f031205030403110d032f030f060609092e030302031602040f090b0a0f0b10030c050d053603120a0e0a140d0528090b130512010c020307140a0b040b06 67
    0x182340c14042c0d54011f4003a103100503c0b0302000b084405d240c3c000c04041207035a221401250380e03c81d40585280214035100c40b01030400e0202d0356007005440c0d500088580c0e030304080010711042d203615501440c070f04203807000c241c0007150f11560140da0082c1d0720031a0070301c40d80b1540f0842020a1146610710800d00d01440c03000100d41c0d203000312104141c14442d90181554030b00010071110b44560500003201c00c0c07008000c9035240680b41045945519190602460310f5000f0707480c1c0c0124100c0c402d5440e03254018802115040725084440011340d20600036540ca110009110681c440440c40e00000c03010602c6056628040c84417400303403940d040004000032194000d0051150032062800d001d403405d10003503090310070083c54503120026040c081e07042030200c034800c001c0c0c60010400d10100603184c8010b05e2011040c1e20003032141c94482e41c00b0f11640004500180554440360034260091400c2102c183c580303000340124412680c0560186800141c0055a01c0005a000d6409a592600d0301d107001014403204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 985504154 1250 985502904 985502951
    0x19050603160501050c1f0209030d031506050d0e030703030903080f0603070302060d0e01060906140f06040905180604080d060803030f0103030f020c060705060901060f031205030403110d03 82
    0x90300407402610401c1c050020360400c80d8420b20f4020b40d18141075200c0e0b8240488000c84583d2075445804064481c02c0e5034000d8103030520200e0039522650707554881a802c95115003031005145040c25010088240208007401503003a41110104042c5d80249400d411366110000403000700c0c3d80e0751652014941d01040d01d0703501c1180d00c0c1107805c2900f086400281d85416501c4020301c200000540c5640345e411940090480c41d000e00000e01c1803d0315101c8210107081503000305440d024414510074031915144903a485660405081c080ca0241000c5184028000052000103072a44081600f00540e1040200510072405036101d80e032100e64142d8020140c031401c2d44402c14035030090090002d0b5103590b1200340e045079170608091400210f001c0c010782c181640280c0303890380310307030013080304001d2002c0882c000e442182404000c010b40750b10b4048420710200a800094003c07615481702c6211035014400960700580681080400b0f80d02c0c440740d0754540b201c803001e0700c0d001941303400c400c55181074142c3c0a49034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 985505404 1250 985504154 985504159
    0x110105041b0e07020304150e120c2d0d03030207150905010c0314070c1704030312060b04061b020a0504180c230409110604060807021b011e1106190506 66
    0x2030600f0103d40017940da0082e8001c0c540c581d207a41004649881c002d1004500c800000340450190301c00c3c000d5030707680360312a2119003405030700191004070030100101258203140e803103030348100d04004d10101403041051814008500341a42003000c0c4011840c6095074043c2440340e20404500d4030514a411825034103030011300f406040c10140e00c20054107008a286a00000618202d0052001030820b0703884641d58015150100c4400107000c403c0c50742c005414010200003200600c58943e803100d001e52a4840c500c22000000d101008e565440103611082e102c0c9613000921100d085603d600000781242e0ba002c540d07040c412050a041c504101c007240302c000c0107000c81c0c07010f4a205c040309541124040007030074001d0721584e80c0d0a40c0e1030400080c4425a085140094071180e2150788441e0090608001622118054881c1c0f9010300b001c130105070074581c0c20103030607561100c116240c880344021040200308008141301c4000c0d03848800641c2040940e110302c3c1600c03080103a100d2400d08040490f14080c103650f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 985506654 1250 985505404 985505429
    0x70806010f0501050c07031509050c091005060a02030c100b0f01020105220609060e0a031803020a17101b0f170f090f0d02010603020a0501080403140307110105041b 72
    0x960501d481c0c0d11821a0401e003070490392000400d99075428240d060300024044450020b1906071a03d00d944028003040c843c90844507910004820400c0b82d410072180c22104200782c8505014900b044000f07480c05003414011a414018181c180c2d40c00c0801458001000d184e0300e40180ba490b10f480b6807123806d40eaa003800200510700b420b915582020566286284540090255003030401034a41d11400805401000804c005441c10f10300b240c41c2e84000c5425070000d540d00c804c2d001c0c603010f03e4003d0030481b070f4014106040d4a2400041200303c000034201076034070b406040f4002d103259000c2c0c06072141c0c2000112503034442c9200103202404c0c0c503071800c041ba010000d00800b0459803800c44840150840341a01014500e55240b030384091030302c040140007408a0050650041c42641c0541044068900c00c444001d4100e860384011146402d045034040c000a1030b031142d403843d02c082003004542110280c07901c04943c0041c0b00ca064290354080e10126076417200307022050800700c000c3c0c1c5808090009041500c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 985507904 1250 985506654 985506659
    0x3050a0506010e0f0105070503030411030c01020304180f09050f010c08070306080a0605040206130f05040b040e0a0204051f17010606090f03120302040f0806040b0609062b0c0e070207080601 83
    0xa01d81203040100502400084e410640aa8002d0082c0d40e54140c0c01011241d84e85040d00e01801c140c001240d1003402403103131a40d1455607600100a81e17056514807440d20302c0c0412182c10050107403548030b40b210f910695403d00140454402e1088440401c0000008184d0701c090380c000401da80e030003d020b05d082500c0c0c40390501051001048504040f50007450100300760700e0303d00010724144240c003081d02100b800c020380048c0c15a03016040300b08030340d8121010020503171001c01340030980d07200c2907a1015a8000000050041c5015070003c0d4108514200e5410003160701c0000410002c0180c10000100080c0c0184640e42e40d4240241800b518240c03400c001203d00e004664202941e050000400c6100ea02c48418103540c031950645004140c000c050120556039124644e480b40c0d01620150f0710150707014001205070600681244c02450082c0017408445039403607040681140140c050740241d00071501c0100440c0d00414070901600c482115104030b41070440d0003070300d0302c000303a402010070390800c0004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 985509154 1250 985507904 985507907
    0x2a0a1706011b230303250f0c0b04172710081918080c19020a050409080d02070b0718060e04020304140114061c020906010311071a0703050a050601 64
    0x64030386940c0326200300610020000b039640052031021000c28240304c04010008040e4001854103000310481800b80c2840d40000c400321031511080c04020003080d42d001c003110024140c000c4450340300d4059600d040841d580545414002e50245500b141c10781c0f50485071509807000b4441740d800420b01141c02c0250000821009010428020000d840c55103403003580c4113240c240303a08580c200e003150301c42c0794044000b5440c250025801181c011030701d521035000052130300c24845028850890300280b60200756440c0408100141c07001c1d0b4001c0781c0c0b101062040402e030844600140010b03500c80c200d5411540b41001006081014485000700285140720041100d0368114859034288402a80c3c0941e0301c1d62142448001c2c4d00f00003030310090035840c044800d00f8002d101100140141d0080340d80010702e900310009410380244000f400f96208150f072011608541c000d9000f5664211829103443c00d126540d1240e600d85020426108980046002041600c1d5414030a450b40074014150130010350810000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 985510404 1250 985509154 985509197
    0xa030507151401150809100509150106030f11070f0b070e0a120501180f03030b01110d02070501030b01030209010203030c030a1d03090f040c1e1119050c0d05062a0a170601 75
    0x61824983d035240070074180c0c00d05020408000c002c00c82b958140b940c0d100300084c000c1c102248003407030792032500000100c0c80c00070100311016540c2110003988484d0040d101c07154254006801c0b070f001c1c0f04107090100c50b291200712114008003080b103100b942a541c9401c00f282943c882c091030441e80200300c000340c0005070325a010813510b10303010f240c00035084181d800141d80e1400012917028081c498041c0d10300c902c1e5800998101540c800b80c0e8144841444c500040d0180e0081031210350150f0814800648444500405554880b03146a004500c48204030441021011186040c1149400009241ca0141003840c51915003040641d410804589039104c000c2c0f1201e02e490fa585410940c01182151182c440c20701d56280661140580c1c4096030000c1e01c0c2d09200003490340c00c0312030b40510f144010542c540b000302059600d401c4809898655600b0710107103a440300c501c4203007010600740301400c5400d40c030700e9010341000b00890b21000300003a100d00f140b804820b4010714085c100180e079507840405001045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 985511654 1250 985510404 985510423
    0xa051606090509041e080c1e030a0504090f020f0c0607230d0504060b060c0c0a0e251103040f05010e040b06090f030c041b11030406020a030507151401150809 69
    0x201e8800c681480345c241c40c460b03881040084e210500101d0f58440031078000c203002c55a0b4140c038881c04480f50810062648170b0045000a401281e000d0004020010780d5800141c042034000500511304600d010386240603800203040d10000c0c2c0d11800c00c0146241e0014200d445441e1038440700f41c04100151030804640c032800c0c00100b40744d5180c2002c5000c115080d0054100030f400104510745074102e62511030b40d242100d0030741e20700c2076110442c0050b10201d9092514000c1003c0440822001c406404280007603080103440001c10000841070285041300b4005880134200380d80c1c04001440c0f820380010486000d05030611300c2686498107980341d40c2c0c2c83d1021075203011003da48104104503041e000900340101d00000603045801d01102c0880580190741454001e09113071103000d1a24940d5500315600d01072030082034050791040c002c40010a01a8024080c100d1084541e0b80562000740982ca06503594403d00c01000907078000103111440c4c040f25a044810041e113456285442e02080c4a582c514080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 985512904 1250 985511654 985511663
    0x6131e0c0303110a0b01091a090903160212030a031508010b0109050f010c0b0f06040510060903261603030b18010915121a0105011704030809010209030a05160609050904 74
    0x3a0300303d500071141440313182e84468000490b861250f86d1503c2c440084d05003242400320405094029417442c0c80c0c40d0b44006d00800566000750300305414031100c98a9000d401c80160781c0300038520125203648900f000248070f02d842c0342e50041841e44400c0d200800f1080c81e40c1200c840e03039051456141c40c07640e00c00107241c215a0102c0ba4201c400c01400f0041c0e1300ca6007030100c0a00203004c1070080201c0900201c00c0a400745100b59010812580d50501d41112411580110000140081000c03c0881e42480c1c05030520005943c00691688a0005401c0d080c0d1010480e020140d815114010506030507108842200700c1c155221001008002e80f000c201c02c8050049400d4640c1c0d80260b031012441da0018040506010300e23281040b107000381001321001003850018901c0940d80720001c1001c2d442003034801c070080348031114144591665039003540d041c200109101490341d400d0020b181152f03010040d04035034500440162601040000860241e811690080303030034828201e904210a45800e0110307a881a0403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 985514154 1250 985512904 985512917
    0x2306070903021f23130608040c0603020306010e06032406250c080a05030d0b0406060f110f12041e0f180b04090305030f0a06030506060f0a0806131e0c0303 68
    0x3104015518000640310404c0c81110030a4462000344c0c12100a00404141181401e900d5595540850300c0382c1040700d000703188030080302041080f24060307005150008414104145222100404243d5507001210040d1098440c0760054900c180c0340c0252440ca843d09840403482c2034080b0001c00a408022868058041b40052041090040c1c1c4400340c0c010b40342d10010344000c80128140305039290003c02660501502e48604000309150500c81c100403100f15458414180f032035600b003680c2c1c0c848004030441301409000c02004c80b05c5010300c418220403141071a0603460b542402002c411104020003202000182c0f0740c4140014080780302140e0440d001074109010348031020030801d02400303804000a401508000303000c4e00305a008030140d8814040c011514140e65200441035081c0d449511024045400c140b0209440d81001c54280380405d0018026403540d42d525212945041c004948170800d804010880340100721121240c4c1ca12007400240c9250500d41079110003140501e64031008041c00710 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 985515404 1250 985514154 985514209
    0x1b070c170f03250602121906050d02061b0d02060108240f0702030409020a0804030f080f0f060a05060c0c0a082b1b05010e06060105070c1e03230607090302 68
    0x240e200c3c503000015840f6005645402c0d00300041107801c10103854143e00c8075040076031107607070040798469101200d0008103400380312003482d000d000f50f6074445c4001c5400501d06d4403000800300b80400110700c90100c140d0061000351300d4144080d04004000700d4095070f201c0030b0a00c0b00b5165843c0041d07190864000c00c20a885911200c9003640ba5110369846401200e00100302400c50300d400c221418400c9009854203094071030b08101c00c41e06e8840c1114645018804030b4041140b01028801d50340c0d004a02a10401c94183c80d90700044098214541c2d82a8640c008421032001e8249046c2c2800140314210003800c820354440c00301641c0104094915040c480d92150f1220340703c0c401c4185c0705406080405515044480d82480760103003a1001941c405482280c010800d01c1d40300d9012640030540205012150504150107207541813800e01400b80c030b141c44520040080740a0a0442c0d0206c0d4a00180030561802d40a0450030440c00401c02414060046010005612001c8000280f0000010045000c02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 985516654 1250 985515404 985515457
    0x10b09150a170f09150405060a0b0103061e240c060b0609041a03010e2a03010e06012301020303060603190905161403010203060a05091b070c170f03 65
    0x2542c1802406081c000402031008408240a10038000c1c04104151045d403080c012a070701c8030040075a13008001d5445a0300149100780c0b183c1c80704019510514012810301e9541c03092900c40b42041264403443d1b18540320030842c055100c5100c400e0400c10710f00b0190180d01ca003001500e5254052005004161142c04102041ea00c84040795880800100200499040040702c1c141c07080605018034080c4d80f07004a024504c080006115058031840f400700300b200304001c4849500d000c0034806083d095034a403680b081010405200c00e9010b0b203d0f440540040c01140d002c107030350b0b111343c14450754103540080045c0320040d120b007030841e0340c0090307507d40814005008039040002400c0002c005020360060840401211400d080c12030112814010691070b481e12220403d4200d01c0191903255012001700000c00050034001140e581c4081c0344140000741342c0242070009030917805040103c07040c2d40030090600031306091241085844600070010074043c0e0184103015500d00c40ea01c2c07040400c0c3e40c2407052210741e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 985517904 1250 985516654 985516667
    0x7020d091d19060f030b1905240312030f0403090608010513180605040803060a05030c060412051905010b0108010905040b061e1f0806030607080103030302031b1908010b09150a 77
    0x340702d0400002043d1303640b42007079084008240d500487c050010901820640014000d0a00800345c26100c6001641500a0380340302044801c2416098040c091503058443c00f050041c61050703d51008208071317803070203140040c500c3d10b141d0001e40a01c5802c02c01448161a4405c55145425501c500010a461180c40c070181041c00050018501130400b002c000c10800580701941c010700c407d40d00505426150410103465030780324031585030040c000b400200440f2941c1214900b0041c06481543d02051182c5420000710100d41025034440e03445607401c43e42075034071801c1d95004001e144070411990070140d03100131400e40c019000521800050096900352082d400801c191840000c02c801110000704046110524603000791801050314400002d03072038280494100c1c40740003680d4940400d40c1c2103640650094102401c60a47c42011002d03809140d4802002021648d010342e164650790450120b005001d00e030141c1006c4050300003030000c00b2180c1c68040c0d40000340078103c501d01d44c66011484044609 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 985519154 1250 985517904 985517909
    0xa06060f021203241e01090902090310110408062806050102033708040b0705281b03020102071101030e15150d0f11010f080f0405120307020d091d1906 66
    0xc00c5c2c10700302e440c01140f948856030040404c00e0b05c5004015590303907054000c90040c11455609a0000c1c2801200900b05a10503000c05c100c00320024101611a40f02c1407404600300d40b2007440705107050031241e002d44a09060351105007810300034000c0300d0038000001d417030f400b50116a035640c0c54403c203100b1641c8280d040c01685000d100030459190031201308000d207910b070103450030740d240c01806010480162040c0200d03981c2400070303101036103850f66410080044001e80083c510410103c07403c9a0855030b610103288121901030341c000b5071140080d013070910702c6824004259060601e400d0404500c0354020a40e4554002d15900c030748003da42d03203061a4800c0940080c0785a001025210342c1e02080503c825000140d40550708000003446500d006580014294407100045640c22000450f240c010b030100301d40c414400c2d0152580c42510300f0004001c1c0c0c00c1910701e0740241e0803d51114503c290701c5002e030001031800c8030032154041c1404620519001024101d9000c414500034400a240e0107500030100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 985520404 1250 985519154 985519159
    0xd0506061908270c041d0606011115011409060a08060606070c0504050a14010f060e060c10151505210916122a27050a06060f02120324 59
    0x402008942d800f90b107484003041041c0c402ca20388500e2850007032824550001c9840c9500c001e02550703d5810040d1008401c100c1044254441c0c0f0100c980340c60000a0028020050090b020390881e0200c41001003841c0000d0030b2a00501c403400c4204104d440026210382c00100548175180d46280340d09045040401c0368101c079400a043c041408010451580400ea000b00d501e169400303266200e003001880d07a03041d4407031000040c00e010490750907498143c5c014912800004c040311780c982c8400d549d03030068503002c0e05807800c034010080c0200083e0f4138000042401c8689842c245103440c070440c1c000300501e050301400043d22995000000c00c10700301008019071005404410b00040f40d50f40002d280403050700c00044a00c0f65032a19a610400b582400b1a014074281a042900c2c283c1480c1900d400031001d0640245c8543c003060703000458020603c5401d000d01d0403040d01040c00c509100000d09074164a1038a0300440d817100e4030300f20590b102401034075000202c141c00070f07440584141c8004501004030a080b40d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 985521654 1250 985520404 985520461
    0xa0c0305030a060512070518072106080a03080f0a020405130e1f0614090105030a0308060f1e15090901060e010c1203050601020106050616020411040f03080d0506061908 74
    0x40000c803002031088200c58003148e9020507241c01d000c400e008201c0c2a80c8130001f05012000ca14040310310b0a504401030740d02844006411780c3d0742e44080d0300e000142d520547c0415404014001d1070401e5241503944940c02840c2945460b240c400070840300f2400c07071840700740c01e95241040800e11606122148003424581e6091412000c2c10305080d009001d03c0c42140c02c0c0807089280003944d410490304440c103d0308010060000b28046440981c2c1c80c0344005c20003503003d002c0c01c110700225501c00086115101c3c200d5a405401d03c43c440500c288040076540c403044a0f05e06009400b007690700c1e140d402d41910751629088500804140058a440800712002000000050101089a0750580c8071510400b4268000d0165039a1035091182920403101c0380100820b00c1d44400c405800d043d04085044240d000d040740c035240e07840880030001c0381e02d030f0001c582d4080c000400303422042c0c05000d02c07500b000044070344920380513000c0518400c404005c0d140c0c0052201010000d422400000380326402902c0750312020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 985522904 1250 985521654 985521679
    0x40b07020904081e0d0c0c0206220506182d06160506040809042d1109032e0605030607081e04030207080708070f0504020c0a0c06030603060605060a0c0305030a0605 72
    0x1d40131600610b2100004515045910030458407032201c80c24142d801620031031402038681c61103041411342d1038030000c40c810b049000041c203443d054010721001704113064010f55040c145040000a110340340c0702e038404d01c00083d1500b00c44440d28029041030b0b00100c603a5543e8400c43c00307241ca0282a00355010382503000c1ea5040100707000c041e800814907108120f80410400e42d0010000028144225019100d540a020b0410742e46100b0391100103c5002004054103010500300020302d8501100d60058066805048001501d101141011a80c1e5802d8005010703060801b400700356143d0000b0070714400c020382e110100300c0d9104404440c507041c032201c1155002514150801942d1010103200c1d40c2c41608c5101400500c87c1c60200314036060301c240021034400c02d4038044c1004060b4200c440d401c00b450046d9640f406c0003400300e1100100403c0b01d41c8001c2398070b901e9070030980e0455003541d1145005282c00c02000c80026404810007041d280e15041c02500d0b512514ad2490003411990040d80c0c10500040c0c0d41c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 985524154 1250 985522904 985522957
    0x60b04140d150618020a020c04020c0a210305090d0e130f0f060302010e010309020616080c0703110a050a1404110903070803090907050403051f14190e03040b0702090408 74
    0x83d1041e5030304990250b0000d214103061504a00c180348a00c5c0050300440349030101480d00380c00410499100b601124041000c80e2100119188401100c1c0002101d40c1e071003d01c0d55405009581d0b102c2c12420250008502601d00688243d450300e01091041d21010781c09440c4520680c4030703407103542c8800f40030424110384400440c010b000a00041e8089151200044d006601c1380c05130000c0d6540c003030314a0742880c0c403880c103070207030035050f03100444401310140001100c0c0041005a03100950103030a004000d07850500074080d8041d130780e40002b0700658003000c00b405214594415512400007d46000400c011400c40a082501507078110b070303030306006d1204001991031000000d003070190012210400300313885620f4152198403441c4030003401608540880c882a603840c5581c00c000100103c0c0c046802c10018410784100c072412551800c0c280d0589108545010062150703103250a0f0090042d0324083c180380160382d2038061003030002c2c421050940018100311004095460207001800c524aa14401812 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 985525404 1250 985524154 985524161
    0x1b0203070b0919140a051501090501080c090114031f0605090a050402210309060703030603110904150c0e1002010507080f150603040303020903070e0613060b04140d15 73
    0x180d98001d440404101841d00c0820146425081541a0b41e502c203199a80c07242c009000c0701c0040814042d440e01c036004140c0134058204241f076010440c5025605000b0300d801214010380042009500040500c0704a0b1524602039040d038450b00f42c0d6140c0700400b180040d240c00420580703018803604504581a160507141c0185040d070790300700c3e102c01e000e55800201c08102c03902128040d511000310884045407800566010071010804410b491030b105256010440c568014002200002d07641c0f1410000c0c0b0465004454100e802240c606100d411b2a0b150700c9800d000085036200c0726981d9282c01200c06000f2441044981c1018040c03211604d4040f2003e03000700b00c102c6401d40403c00c9000003842442402c6001481055099820020300340c040b0b06000741074000800440c14190308000170314050346c0800c030690003040c04900c00d0280d46000c000f80034030b01a030f4100c1d10001d14203200c02480300329551801d4070203450382c08801d0201200c44d08002080c034101081c02518052140c00c4880341002141c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 985526654 1250 985525404 985525417
    0x6030507020f030c03181908211315022407020f030705060c03040804080a060501140d03021207030c0b09010c091d0711010605030118020301050f010503030a080a1b0203 74
    0x80035100c1d1220b40d0b50146440780304001c0705038400d420401010700302d0703551541e9030301c81c1d004054a20021200c0c90315a9018000c01900b250030150301054011008015092055481d00c001d40542e5041403d60211183c400050307024401d07900c6003000781c01035014802c000c0b202030040b42c18600c868903109d4081c1085c0f9008141e840f00c0040c080c0c4110070404030390010444030703060b0740180209425510480700082940000c0c10868400804000004585070200029151507001e0000060b4552402c0440b0b9114089052a64068110124210702198001c28421005000034511381e40d00c003240d1804490a000c0c08a0081801503a0424040c203070105601c0800800040d483d02d501c2c03640c5a00c44501c0c03600d801507100303062a03a084c00107514503224410300c4c0c18041056001080321911140000d0940e51803445200b500000d0001d040113524003409425002803030300c000f1990550400010903101c0c851400300e10700b4091004041240082917512410155005070300100c16070b10f04d1300000392664000ca = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 985527904 1250 985526654 985526657
    0x110405010e040b0708070e0a090b03060609060303040e0a020d02131a131814070e0a050d0525050d0c15090f05010e0402040b03010618090924090c06030507 68
    0x8004103900c1d080c0103a490090b6080402031071295035460085441690080a20f810028141c00c0f03201c50b6101c84032100007804582901041800d09103040c1807505c40024080340c17240c0c4215003407002540f000300880d0190b40403820b01ca0740c02d03074800d00c5500c0a442001d01c04d83d40c061000940b42004ea2a25103860142c5404104802030310040084c1c40e1514091366424001d114602e0504000704458507540d000c100c4101c1e2008030b0743d44c0051006042c0100c2c229018000f0805408503002c1e0751400340e024a0207004210760f0382081c25482e8541c40c1d5104447c011803519201d007064000042e070081c1a00c9002848010000d02d24000c6034507200001d500c00344902c420003141c61220242d41c40c01403000c0025609070400c8901d026190800440700c0c551100c02490300281e00f00300c003103100e500c40b200541c081e01d110b4a80c02c900e01c07400c0a40307075008041a0322040307109141020307420018010080300b61982264010040c0d4181002414000500c01d00030003d0644001c550000b800c40d0b0560003c40c82070505 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 985529154 1250 985527904 985527911
    0x20f0d0506031207021f180b0d0b030f074a0609060d030e0406091415030610030602030402040b040e0a05010501080f0a02060c12030112060609091e020f04091104 71
    0x403a03400c0c50084c0200d440003036101c1c0440000c103d00c600b03090300b09080700940d0300e070800c10100401825165a02c02d03030020030304200c0025200e40c01602c1c2c0d00038034803102c80a40081200100741e0781c00d0b41d111043d84c05180030501e0301c01654059214074440030815590184409494084541008070750713070707651560070540c508402000501500d0080078003441003001802d860b2200e40290740851340010300450041c1e0056441d0800720ba0190148540980348000340a82d00050519550980b94100c020301c0c0180309600c920700b04143c060000c040103088a84c80360003d078aa454034030010b0050000c2e0803040750804d103007800341100880e0000d400c0e103050f401a8000c00031662100ca1380c685820356050601b441c0e6001800040041c2001002418030032106000d0703441e001100c0c070051240b45e2080e0300406000200701c445100b400392511501d0003e0500c800d08000c0b603000c0b0794a500184488080105448401056034400d5491b25040d01040e070500078020442098980703001c50804d000090024061442c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 985530404 1250 985529154 985529173
    0xa1206090504111002280b0907060512060414070210060e0702030a0503040c030b01180c0815010c05250e0109020403031b0302010905031b013c020f0d050603 69
    0x1031181d28001e5820414220141060805001c085251349482d441184540010112070b8502c0809506140c503402007480c0d1141c8090a0083e0607541c041c1006c3c5c2e140c2c0001004200030781c0c029080318203e980383c5500d030401d542c0e1140014003c0030a003003d50040111349040000c82c035030101d0300e89911070058004102c10703030301c8040840071242d0864004025900403c00d00403450302900166901900c1560200c408588a43d02e1030f00340c0c0c4c1d0a0303201c000f04003500a107140c030021250140c4900b05200b80b40100c0c5510741803040304500c03007140c00b02a050050003140c00081c88400c0c4000203003289085000d403000100306080c0010310260340b0522107407002c5240045403000d520300840d401c80b50166502c695100200c8501180c094080c0d10840035590703074900460028030144080c100e03010f02c84a030051a012610310756420340b907660b4010401001250002a0070700701e08100c0d51449680c000c079004211b02040031210003445100311030015140702148681092140e50043d501c03942c4c0c1035042e1001441c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 985531654 1250 985530404 985530419
    0xc011e090630050f100b040911070804090b12010c0912051c0905010e030f06040816151a01031b03020d06090f0b0a0e070c080a090b0c1b0105070f080a0e060a1206 71
    0x70a0701802c3c0301c3c24400c07c4104040340a6030014201700350132040d010f140001c00d030f40e000600c0c0e10540c00310201646514040e1124900762118483c0302c0c01d100024071488050200007000010240141500050b04068540502c40100207190164030b004248804008031030744042c00340481c600c1501c0c000350310b61780c0780c85c1170741004600c4082a03400b560041080b038540f44c0d00d0710419084070f80c111041c1400c1c9564440032a42689845400c1074a0305000a0360100c2e5410740e840d0040c0c0008024181814881c07081d10803084012034880c440b41515005881d03004601d42d1502515055016a400600b485100d400100e2242c1c0b10103150402110041c2015036101e903444a080000c98200740821041d107415408030302010000c2212000358a40400304a84034545014141c001d8210349c01283d002e501078034030501d10340100303400c02d0741d00342881030a10040e55114905070a8070035000b01081004182144050701506001214407002050591030702d4040c0ac004043ca428000c00b42e01c91410288005201c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 985532904 1250 985531654 985531681
    0x6150613290d2004180c17040b010608010905090613050c030d050c0d02150103110a050a0611060a05060d020d02030a0b16020c01030b0109050f031006080c011e090630050f 75
    0x101d200e0fa101171009440340250f40014401901c1050a01901426200420034010341c528400c42c0b0865283ca401c1d41480340080c18010142c11104040d4504070521912180001b800e0364041490b92603400d2802a5141450901c8200342e40c81e0b4040c0300f100652484503400401a010019511045840d080b071114400c9985000841e030350074007052403100502c08982e41072200c54440702d001d485144d03036aa507600811407500351584a400003406101001101075002d118190308001071140a105508083c0001103c0307052110000740f051148c0d900140c11501c05002c00806140c1000c400c00c030700c1c80c00c5600054000000700106006000e004e8030150190301034402c0031a10101a92140400b508000034446540514006103a05100d0900001142503070b50007410064405040949036041c0c0c20400544981d208680f100c02441030440c840060943c00358410b030465100d0701e418202c0e8040089009118a00d070000b10305034a21080100014044035044580582400030030072a007075840800b0003c62 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 985534154 1250 985532904 985532909
    0x221090d061a15130e1f0b0a030c0c05031c090c06031d0f07091a09090706020d0305040b0c070c0b0a020705010f111c02160806150613290d2004 63
    0x2a1142810902000c00c901d0201a442440c102c90a1640419140c986e40e05401a80c806110f004002884a548950500030703110100c0c282c0c24411704040a954030103441e40107040f0217524001d00700c1140b0b8000c00050f08000740752900440f241c01120703280e400c010041d180c0743d281e4200b142200c0403805500d000c001101070f140d409000c0a020a1400d1042c03ca001d8581c01076130241000140541418070350714403d4150080d45d1010040c400c2d20b141c0301020b4288401f03049010f003410319010030403021845003260700ba400444d903503c103540d502041c87c2c29944e04006411082c4204000b050030303d0010b07000135005040d1002602d400c1103801c84202c0441b88584d03915503a00702c5801001c414529008201400d075010000790040c1ca080c41d900c5240c0c00d1a1389090360118035198424000e10442c020402034a4900803001c0e113986242c40400e10451281c80e8403481550000780041c00307001c0040440e02842c900c030a01d400000b0b03035221038614440c006804080941c1600781d14090000c4c220081e920111402c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 985535404 1250 985534154 985534177
    0x3050727172b0e100e03010c0c03080a1107060f02040308040b040504060509011206050403020c2d0d02010c0327080c030106171b181e070221090d061a15 67
    0xf038580d529010300c41070b0400540b1030418406034100c15040c958080c043c4440b100300c11795030000140702c00e04006100c410043e02c400405441d09500421041c1d4074000c9580e855001140420703c030b0016068480207114a51020b00b209202007004110f03080400300810403900122404c1c40155292000c0141000080c401c0802041e02c0c0020300d0006141d035000a0391007402401a10001d914000c00708000020400b502c8a8014080c0c003440701242196210a023202020785001e0a141000d600107881c03d05948030103800c1c0301b05c040c1d4404d90100d0004c00e000400c900301c61109106d1b0b55030000190745080108219100b9424944041684c1e100b1580000c0e01c081c08800820041c0d8006031003103410f0003044002c1d40c001a000c10070360018042c10030b05600903001c40c40410a120880200310b00d82500107050881150000d40740d02d0f00d00303000040040d0440d5980f0b00c0e82943c809991002980300340a43d00c004209500305450a2a000030701510b0003611142070710361480107111071104c411035201d641900340c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 985536654 1250 985535404 985535417
    0x60b03031303060f0e070b07060612080703081909030c031b08030c1305120705030f03190f05130305010b0a0b09091803070605100f0603050727172b 65
    0x10110303c40e80c20130000d104009000048150400410608080701307a00542100e10380014601c04210303213441132070020304501c0302e422800c00340340c0d40d5044140b04690f009001c019868000c6800051b0f10390b84895a01748080b01000881c0c0704d440c02800c1c00005101c280e0225202c03400b2440000caa1204848480d0752180c1003524540d64031503041d03601d4100100541c2e056110200100b00c80d22010080200450002c0007060300354a001d082601c2d0030f03c03402070410503410a10120840c0c140d10455403018900342c2c2020b460080d50040100c41c107004002442d200d15048107800018402d06522406444205642d146101a1240b024041a108510171190041c0000c0000349007451090905006482c240d03041c2d038684000c60b11100140c85050315031200c40ca4102070100402c5180d404a40e00400382c50805220301d2414040240420101c401200380c0c194403481e00024030786602d0078640207016004548004c030410404650343c0c4403200030002c1160b902c0c2c8109400b0301400441004146223050f640d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 985537904 1250 985536654 985536659
    0x70f090b0d0b060708030402100938031f0f120b27030a0338150f03152202071a0103030e040507030e1b12031204060b030313 55
    0x100d095030003044000c42050382c40740c020090381c2d1018004d0140c10b0298600a4803814203004100c40060149040c0d030500c0f01e02a010008491101d840810041d101c0080b500c0c5440b480207801d403015490851140700c904000308112451021484030114000f5150380944c84c9070321030041188180071070150601040302d0040c103d001911034520031b41c1c041d9520000c1d1740e50805001959003030740c4601d01c5da000c1036000807c61258150b0b251003511103055048800f004510220702d0700c01c400c840c0c800b1404403482c2c038070920328500343c070303500901a102d2001d089403d85da040d40138082445508103581c05504840e003140d0100e0207282c000c4910300d924105009908130100c2c11a6008001e50000204a42402d0100c0700e5207100305981d03044500860080d01e0310010045044100300444000810701800d241ca0401d88101c4104001281d42c501d10501243c00c039103200e8000003074920f8069055140152000045c1740b9800840702000303a018900c510000d0120441031010180c8030700038148161407100010404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 985539154 1250 985537904 985537919
    0xc02070f0e1e070c060e03090901030204020304030e09090304050301050609010509221a070320090d11212e05130f0606051201110706020901020708070f0e070f09 71
    0x200c54100c010030b070074a207918842c480b100120358012140b44000c103400040000500000303018802841d40402c0183d841c1840c500d000491301d1206000281c080e82d80070000404060041e040c0109280c002005200d0030f20340070450741c0e500c0e8440d00480d4000e50802c1c02207240740c1050610181a100d0007410300b81030741c1e43d48500d607540300e10244100319000450034034580030035420309002d480c03041115240c1ca1241b404035030260503981b0444202d4481003020212480754800c1100b40c80c1400821205154035422a0070a503050401314104581d1003000e07110000300340142002e404050a03104070030388005014000f0861360f038107139a03443c00200100703420314a8202d80c0d171503000d103a009100b50b401910401ca41d45403040214041c02c0203c603a20b6072541c09010b145000c10b0780018098900f030080c401c07001c3c240c011955034003495100402c00ca0300401ca0303a12903030003800980081d00e558001c6404040e81e07010030322802c0100b442a1a4200044800300d01941e20034400d01c5400c00071502c40013080c03442c0088 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 985540404 1250 985539154 985539179
    0xe010515060a14220b03090705040f0b0a090507020606030a0302070e0c0c0a060506010212270114030403030209190602150c041e0801060e0613180b0a0507030c02070f 73
    0x81020030448040c100b0360300424a4000b13041d012036034031440e161440b240ca07040365038100c0c1034100208005041c4104070000c4400070390700b0144c41742514040b50024018081d1005040c250910740d612801684001c80d000c0c40603031000717126840b02d034200e80c0340e9207440040c50b44440414a020300180c11031942800507010f900c80680e017054100403c3c1d40303802c402032100c03030411503401422104076803104180725196a0401c680280440c0d01c0d9121403412443c240307280301c2407006605000402d43c003503a900000d40e009075101c40301c407006800c417942d6a2400745402002503201c1a030140c0305222060b144191101c469004a042c0e4805800424040b0f189051407001000028550410003100300000701d142d4180134081d140c0269500c422001082c10601b2203420f403001c81e04006d003810140c5040042d6a034a808011703045c40104000064000d4281801003907025110380086c040303a61040c24407015a101b030303000e540310b041c640d9800c100300c500c555012071303c455441c0b04034002161700000a108030541e010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 985541654 1250 985540404 985540417
    0x10050f070b190207050a03091509030605090111040308070c060503060f0f12070611070b0c070506030403020703021c031710090b01110a030804051509072d0e01090e01051506 76
    0xb40b400010303142c041145060703a02c0034108807100e400240c19642010b0300503081d440904550801c035121101d50410062626001d444040e009649650100d800c1450030b40c4511108a0302140203076031552a41403000b11a8040d6000311542c1c10080d03000204544a1800e49001c2e803c020110342d00262524100b103904400700f04455409030f8102c01e1441018000c0003624000c01a50f16080c40da10300300e1030f80500f800e1090b030000c18101400c00c124051300e02d010a219090300c0045615584036110390804034900391260b000250828a240c1a162080d0010111004070318403942e101c0da5060f218440e1841d15513400d8803940d480d2a1500303400d00c5440766a81219116070303018980054880b120007a00d03482e024210900b035000c0349054042c0000e007c4107002e82c1d61004ca20501c200c6032401c5c0801d0260383c82020f80b050000781165002e04075400c806a604901c010310841d01a000040c0c2c590340d00301a000400e01c40c181402d0300e0400c1042c0703c1001802046c0c800c1d966801444488414070301400074503805034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 985542904 1250 985541654 985541671
    0xc0c0b0904020d1b02010b1c020d05160e27060708070e061c0513030e0609060c010c0806041b1d06070b0103030804120914040f02090a030f0210050f070b 67
    0x80c40000c640f040203104c1c1d454204404101d002d0001d520480181c00c6a51040103980900345d566200009960b40b10324022034554184d9903038840303c480f03051807400c1c1060455400e41040100ea03000401044034070300d042c0039481d250641c03811940580301100b844009440d80c1d107515000a4000341c6428020310956500135075070305001c40324101a00002c0c2d403e60000501c40341c505404960040700c40715511a281c3d10041c1580911494540703920701030115a00311020910401e0006120401d80e00c0c0c410550780b0002000c0024002c01380032007406056003008441c0640910b180025840902009040e0030b28401081d444510ba40d001100308a140449030480701c94020708100403c9000420b00040c980c000c40c000d0369648154106450204084803101d800d034002c000600380280f10200140c2d40d40b0303c55040440d0005101e034600b0b038028002c1e0003010b00a95004401210000a00110101450885e8821034400d00641c0500105881a0280381d175460401c030014032010b800207030880842c42d00304000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 985544154 1250 985542904 985542907
    0x1a070e100801382803140f060d0b04110f03031c090614010e0106090906060503010509042a060909110318010b0306040f14060c0a120b06120103120c0c0b090402 70
    0x800b60681d507004d0013200380f15002015a1101040da00010300c054004a4035060000320444c50b44001d411001600807448494240041401035803000364146210f41d114040501625050400301107002c070105080e40508065a1204005c1c81c02000310b07211048046c6500c500042d000d1503840080c084a0811a6841e9540b5840a103641001050030300034914032801d01a19030604a008050b5000d07075100a14142c1440418080300d41c204007aa41514416510f070443c0d6903650428480e511044071880c03103511314101001d00c803641d030703507080e003080d6034064854900190f90743c207401c2d0440b8005940d06500440a10114200c80c0c14010f400c060210540300102e142c600d00b00000e4200034056070111031010480c1c6018041041402da1a0000e401aa010b0446454050781c0003c8500c40c50800318104900310200d00c5d0b000c5a5a804030310b21b14ac000d00712544031041203200c420a81028001921185a400c0c0f4042003140b00d00820b03209140d00c07040c0340e01000e180411030980754025607009544180c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 985545404 1250 985544154 985544249
    0xc0d08032e080601050102070803041406031f08010e150907030305070c18091e02010801090e030705030304080a020118080406210f0b0103050a0c08040209041a070e100801 75
    0x1d90449001d072400c08041c0c14554500400603181500540c840b080c1c41d0810b000c1003109115814106180241c140c03102d642e80e66801c90500086c824a00c012104c02035400808125001d05501914100b0001001c5890707604034800304400442040703500c04007603407000105100091140c4050f02040d4402e0381c106602c1a00c80404242c0000c405001954259880815400b40300c4c1c460000413907500d110002c0c0f41442c0241c0c0001344a4141406000c010a40f10300001084280400480e042d05400006594403030a007031810010580c0508442d40041d07013481214075000d40c1c0c600741c52840582c4444074a252278038040094034220a09046940c43c684050603143c2c003120360313004000d0300c01811135001680316a400c00143c200d039409019195040e2030b06000c480c10130703084a40a50400c0c0c044800c01a25611841d100d20058106c0b0541180045c404080c400780903040300b814010712000700c40025005489030000c9481d00802d106000040d540070212900348070000e200c03480c0485000d40358454502 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 985546654 1250 985545404 985545481
    0x130302011d0615010c0308070e060c19060509010b101115040f060e0316021c0804030305071403031b03060a0f06120e012307091212020c0d0803 63
    0x4412610704140e40c01407010030030140c42000441a0340c203400d0a020000003203d03200141005c000404039418840443c40c01071080e070711003040d501d480c0201303011224098070904407102c600d5055541103c6840c1050702040a10b1b1046c0140380111101615000810811030400c96900c846000192410300650080c04922121a00c115109a001c8e41d4803800390013552a00b8022142e005004c1501a001440a0348040c2075101c1e80412403a0100c0304469102c02d520b404a6040300400b40081c10034400103000000c0541210140c56018010a030381e01e09604810300d116180e12080351040a541044600c682ea07180a9001450b004a406000b0141040e00c1d81558151600760307402000204180c1c100500342d0706410700600c404103d0100090016080419500d18040a68554401700c0c010b010002510b061242c803e440c000c0082440001034007040f030800203400b40d96071142c176006004002c2d1401007800c3c405448032005501440007880c660718202858511400c00c2d2544003c00d035000d10500703554 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 985547904 1250 985546654 985546691
    0x615010512130203060c19021b1210020c250b0f0309100504061a0103091509050330010504020a080f07030608120a0f0810060305060f1003060e07030e030313030201 72
    0x1817013142240360b030711102441142200340762400d8403000c41d48040114184c904105c10703003240110055403441301998200c1da05c581030489400014030554800300d5598226907001586161141500d0050303094010400c2c1d280b83b400025015400c0385001c100256912403d07010300031a800502d00041ea08991075111282e003c0d0b51007650242c1c0c01b252940c48800302c0e40d0400d8900d5000c0c0c2c1090178100182030040e80c80821004152090b491440e80d120004000d011084c4200e0b010030441d6009040a43c0c490003800340e0103002484824013601103100007140c103003840c1c403c40744075141b03d03100c082c07072550f41112118500f800141301508051300c6030130010f2954001c1060308243e0030f482440b161280680000100392030000080041001000000c4c4021034030351030035900c152001458046501c0d610000800d014542084106030002400340084a4166240c0e000d181603840e50150384410f500c07008011019141403410450083e0400c00102d1200f8002e0145164164403900012840d0f411400744e44508 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 985549154 1250 985547904 985547911
    0x60c030206010b1b0f061b271810030302060c0c060a1122180606050a1211030a150501080c0406031e020705030415080f0f1017010e061501051213020306 67
    0x217070b9000506000d104200b0b5034202d40c00040b070f940a241014248940200752440c0b00810300e00c1c0ca90821b0007410b4640340e800c0600c2158180600804150904a00c0e203080d0700f406200940050041e0401f00700300f00e502004a4243c5002c5500416154442c84900c000608075511414000d94040203030f40020152800300c41c0c2401c2005031001d000528011482030718690055410155600c7c0c040c06001290b040400e9130240b0703015103411004510150610303001899284004a000e010100c2002a90141074102c580c1c0b1000312045803040c01d03a1900191814103040d100006420400c1c8000d0103054440e51042480521095031124001040105842240d1104509907810780001130f080c407488164424a1402c40c55900d010656881d090010224a08014001c45010710f588400300c0d02e011308121031030f0080c1100f144450340102c1d603140c00e94020142490300c04418040e0720001032585481c0540f43d103d084040c0c40d00c6141a040700301200c04180014040c251525001c00440301580742084a24031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 985550404 1250 985549154 985549183
    0x4200c01050c270a152102031b030a02070807140c040b0102100903090e01090e060702030403080403020f01020f060a0c030b0a080d031d0307060630020f1c0b04020901060c030206010b1b 81
    0x180c000b1b80200c0040b01c07100b0b40d040d01180c10300400500c4168a112100c0d14090b00c40e030842e09450351a8000c3e060080d00c200d00c5e0161003000085a1903080c407103810b926644401070704040300c8222004c00248000c0d22084049a80035130800d0306460440d800c144c00c400300d900d00ca80703402806503894800719200907100f0b030081a1034503907a02c001c0140d61001c101a542101d901e000031400d0903d980e56540d114426400300900848440c0c40c030b00c12590013040044904503000c0159207075450210030100041030404c4811001a007001030100700b43c1020700406054a01d0a0068000004181800e60191503034014644030404060311810f1441c10900103401041d220329008210a0318120513035402918419035080070030684c03a0803070750622542000309001c940c184c1d01d2095080030140054007148030044c508480c2150079002c9402c1140740201b143c442d034400c6800f002141d0f01d41c0400c80d18011943d0004002da03015100502c4414540d002600b1007115011005404200d2440d001e414640310a95600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 985551654 1250 985550404 985550417
    0x40503091023130305100b03070603020f0313050a1a0714030c190509121e060c0313080405100f020c01021c030b04200c01050c270a15 59
    0x2400340340c0004070250031103003031a0a000c0321800c2c22000d0540c0203240c00924648600046082d81c9003480d40b030380002950000145e807540100d407100c501c06401e0510015110740a40c40002c101180240f00740c81024024074841c1742190348400b81125040c4228070700790703100e01c0741030481c42c0010520301030703041e01050402d12140315052001e030242121900311b0403002e414034180b0412040141c05810354542c184030a081c40054041a02d00351072030710803141c8040e08030341c80000c0410440f0000030900039401c0e109104c5104c0d0750907407000c00d45030b50003038907191b840f448204041403529170400f03100ca1100e130041c24440d1500b83c2d03c00005042c5a00c844101010498000d62000115010b02554441c40c1007800500120b9100780c9240759140c0c005403481c5c0038544d40386000c06894486030f00c900c4100740050343d40c80c1c08064004107034159030001d01c0710b170380a582094009510124001d060f10017201c50175040b24208039404004108100070842156006440c0941c0001c0c410358607103804c2c804a04944800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 985552904 1250 985551654 985551667
    0x50307020d0807050c0a181505030105010803040e06030d05030103300c050d0c0507060f05131710090c030201080c070203011508161802030c0d0606121811010e010c0b040503 76
    0xc600f0a401601e0317240c41400c11000030408a08803080d0322280038550880021150310388402c1184960702504141d41540c607001c0007084440c0b001004000b0340301c02c610603024680d1500c0c01c1603504d41d00456220001a001c0c8010000600009000c00034640659036100342400300025070108080702000e0600050300782d15200080c05010701c41c82c040c3c001c040c40c2c041d90751030458903081e5843c01c4512480040201b40c81d03090118a100d102901c2240e01c0c0c208600681036610b02c00309001d0050300d8a03008860050310f20aa80001d007510801c03865690207a012184a8550b40040d120041e0040503900c588404004600060790b080c41000c4140c00010091000386083c03000503840c000d00300704a440301880e1640c0a0003664203e0842501d01041700764003503603c0c2c0d501280e41c075050052404444880c0d0074240d02007a007a80007426010882807031401000036504003200b14684d000e141601410080b5006104d03016544200340c40c80c1814010306180040f43e14030743d40c20507000801c0310103440a41000c50300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 985554154 1250 985552904 985552913
    0x628050c07080f0a0326100302150c0a1401060e01090c0905010219150b13090510140a200706020903100615080705040f06080a050f01360f0b0f03190609050307020d0807 74
    0x32258ac3c403800c0540c0c030b401c05409800c0c040d0b8400c92040c0c007038017000b030001003c088031409412070009045042c0c1c07400e101c1c3d42d403243c011001e880d510f80700c0c0010072000400400e0651002460b03a038020400d44004101188907225480511006503185600c1915000c206d0301c03070b854208035000d146450b501c000800c0b0ba844c0c00c1a50900c2c3c0241e880c00115801c0001c214070450805c420990820310500700054040f03009240c0124441c0d40022901ea11500032500c83c0a01c0710580c060002140c054050359820041810240121151401100741d004200e124500f000c512440080b6403001c2e40d0305040e49000c0d1203001c500106e501560040001882d50010010b11003e01e008941d08003260740003102e0b07154105684103441303004d90400d11070784044400c2d41c0074200f486040502c01c419050318041003110301100410b0098030f404000e483c0209000c0072121800e04001464292820200d492801100034550f111409044840d60550703c0307100500c021405650345002041d0114810801e096039005c0c5440c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 985555404 1250 985554154 985554169
    0xf0a02030408120439051201200a1d01210e121309061d04060b0910150804030509011b060f060f0b03150628050c07080f0a0326100302 59
    0x1c8600c0c80c807217680d6082c41d070b0700f60700489100382c40d01144e5102c455580d2002c0d00340104000d0f0080402850003540000304103241c4001080182d4095036458030b080d40410700110a0440c20304041e0001d580c40d94240112503c0200c0f10382c265640d83c4000c82d55409400c3c2e600e14081c1c000484810306030f00020f0007019241f40000f0040100031049085c406149881240858030000c144480410b821040000d020868180c4c00a01d02c0d060003000d4040e14100005c10502c1444d090041c0407404004400011a4a00a014151040d039241d9201c0c1d280c80e400710011114440d4110b2642d4440800c400c3d01d90014007240078213881c0002c170307034400614a860040320300c3e02c40c0c03071592290400b00380800a108803042d0080c00c20510b42c105072245589d40d03a1b1b81041c0c1c2d2024131400c0000c0e1000e15011006d1141680c40801030203402c400c041120255070301c91711019150b030300110751880180e0003422400d0000c1d0040d10150740c4500c3d00c88640003261041c01d03001265000c1110300030071072901c159080c0110301c0d280c030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 985556654 1250 985555404 985555463
    0xc09040302012906090607030912110a0918061d100e060c042313090b01050310021813020c0d030b01020d030501050616060e0d0e0a0e0f0a020304081204 67
    0x1c50142c5543d2460000c99114411100514043d200015100d0103140c00345201e10000e1407003071290b00e070307412481c1404030020700341305c503032a118481f025000114080240225008a1088075503004404419517512000300080103100f01d0851504009028001d410302c00c4046098100d01c010641d880001191400c140c4000c100c000880d10030b00060240004000003441660581e0880b01d200444800020345110240c010500e5020f081001d800c00300000e5442e000e04170f480c1079044545501e40b0444080a0b80180140c242c07040d504902d80c45240c0c9080300150210208010b00185441800304506081850010121002c2600c0e020f40e803255584c1008903040002c1d441ca4200515410200007400314499095124290044c4940381e400380030881d400300c1d044200b01d0302202d80d84002d101c400f9050000c005202031041800c543d00040100c2c529199074422640c0c030789408243c2e926180c00c60025080a8406d42d1003c10078460080c130782541040c8140179500410349550700c1b18200005000000800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 985557904 1250 985556654 985556711
    0x326030402011e030b032a03060906070806011e031a0406051c0f120c11011e050309011d0d0e0409020d02060c01060909030e030d030e0705040b010215010905101706040809030c0904030201 82
    0xc09c02c1000161007c076010307801034180c3c40c00f5001c2e5202e50300102d4003201c60084084c00e80398045412421103400d40d102081880d210814007106031a20320030041110701c1480388980150b41e2000000241c6260710b8454101440780b0708800c1c00000507102c0654002d080350184c1c000c9854074030884280920703910000c01178132091030f058a40c09410124914003a406450150900c440880070600240c070a4121559541040189500c00a85603040d155181c104c500c445000c1040100d0302c03407650070140120302c41d00c1c0d0007800305003410406900b40881d6134460b140c0070303045559510011030b4904da10f00602c0e20160190b640c40212950510805041541300e02c825000d041c6030090802d0444408a0b42e030381240d004650024140c040c000060741070004c0325220011091440e0300205400245500c03041c054609010070008540e2620141ea005114600c041100d81d8021400100040d105000802c004c01003c2d082d103000b101d161001c5010f1001c00c0e41c007180583d4403a004201503004c540380031240c44410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 985559154 1250 985557904 985557913
    0x30c09151603080411130f0f110a1b080a12050f1b031306020310090605180f10090e0f0c0301180210180326030402011e030b032a03 58
    0x31607204410300e1402400040601a850000800348049070201d849801c202038010f000c0000007040b180c004141e801901c801c89881c010810452294034803489021041c3e5007a2145019030a50040d204038601110320000e100b06402c02c900060080d8000d05521042038641840e4164040040001e840000303000d104a004a00304001c10a184403140241071104001880e03582e07250311103800610f100c1c03800060041400081840500d008600f9060115600e81c0390810901e40c5580801c44200740002c903201c120f4400c0008510b2020012201d26000408040c004081a41d40c1d4280020354005c01010030f81500700c42c6150346d0103801440341c07000d01d0f10b0440c0200880c1d070254081240340c04142602034082d016845c0d04a418501945844090114030350ba48088150303280341003000020710240c10056030303004854440c0700300300400036603005d6076050b11030400700c0407000340d003424296041300180e08250325048280080c2e1414401114180ca054507085c1ca4410851542e51200211500c014080d500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 985560404 1250 985559154 985559167
    0x12250b01140603092e0603050601180501060807030b0109050a1401180f0b0f04050a0806071101060e0a2f120112050303180a12170901060302010e040903021002030c0915 74
    0x2001702e1501191403011007202c480c5d039003843c09000190011004c400c04549030000101c01d000000603228101d031401e84485589403051303c42c0f0b4050319020320550010429481c04184e01078000e4000035080070041c5003411481c0e60f00c07800a031604d40d4543c0b003201e070300030f0400d8071400c2d81d41d100d41500c95183d01d244802c07914610f0501c2e800b80134402c602c2407c4001c0e00c0800d021103919610300c1110001e020040c4203640e400d0301c0c0d60720310381c84035800c0c0d41d000003027607646a070060f0010040c080d80e001c680c900b4082d40c045503038031100100505880700c1c405955001518604801c0a80307540c60901189401503100e80700c4034540080703a100c51068021031541035002242900080bc00400c803a40503d40c2c1180c120110050010b0502c3c00ca100d0318010402191000c00e40c0140380d01c01680c8404155030503190045880d00554142225070034040a400a0b1011003000c0003420300303400c2040c02502c01d01c1140c0341d05640c40060001c9800c2a503000c00c80490005500010749440400118100b0351541e07028540403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 985561654 1250 985560404 985560421
    0x6240206060f0a09050f1f050108150409060515040e0c030705120a0c08030a0e0907140a17041a070516061a0315010e0c09010212250b01140603 63
    0x40010525441a04100191541c80d120900b00c400141220b94044c03105040902c90301548940494001308604001101c1d8907581068808400c110b88e010384030f040207502e450034498810070f004d0703083c01d40080d03c4916200004800744a140e100320b800010440901140b2070030001a216500c00444082e800703990720710125a03001c06c1903422180d0880d100004290129001420704036014005844c550180000089420000c07009118074000c0781d540c0c0086504103010441d52000c1a608a07000615460040c1c5001c4114402009150981e040c5140d841110342508598581c003100d088815050000940ba080c2a28520003030b00074400c0d051207414010094080118514020303030103851076480b50907e01c2d0f160300380992030403555400b80584000041140c80055104400e200303050328060040700240540068600b03440b260300c816070280c2080da1038515584104e0300b1400b44548080394500412586a403042e2500711480d115900d0301c100d41d0301d08401661281d140c14034040c00344600300104101c50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 985562904 1250 985561654 985561663
    0x20030904090609140a0c0509070206060906010203190e1503091f3309050c0f1b030313110f0604061d040509031305030a051c140409062402 61
    0x120429100012400c006040c010060545640080d29080043d940c0c0140001c0115031544000d0155441041e21030303640e014002d030054120703030420040c0c010502003103141c50003440b55034100c0c04c140304603418075442c8060300081c04400d403441004070f0031a43d040b40950030000b103030b40c10b18100004507a0840c0741c1904070a0700e90508041d041141001c800d5403c2042042e80d001001895050b8030184200e03802c1f070a00a203a41413560309507400c194810000603000440d001d0036101c0c500c200220781c00d098900c6030800b52504440d000318100100d4010745403440508002840c4901402c9a050218801504100c0ea103d41d1715200706000f03e04180a818298585100b103500715466413605000c1724010600c4141450b640d01c1c995648241000140f061f024030000c0503000303900c00c4281c0a1880c07951403003010f640c0e5103587c00c010080c0d0810120308004a502d9000c840d1201c07040d05040d0040501d66105034001e0f8401d410a1287c1560307000144000d120440350044001e101c6880c3e5000580404806980c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 985564154 1250 985562904 985562917
    0xc040302150703050d050c0d0e0703051b0409050111032d160e0d20010314040803100e0c120906100e1306151e0f030201121d010c2003 59
    0x9500041a204144c0b045086a1980e41800b170208840d0909030345801103540702d002c0e41d00f1498140340300c0303011012010850342e08995000700245805c2190480100c55038402d840b00c0c903407107a902c06c51038011031000c0c0140e412140359500c545640785440c0780b1801d44101045040b008000360241c0c246402d002c0f1130880c1c0d40001100b4400b96241094141c12a44003040c80c4059400040b0952004200407800d1600780890103400120000c400e010ba004404a4141070071003810040c0e0b51003c140030403210801560041d1100000700a156201c030241020714900341c50608408000280880030210000743c000c1d080f07402c0c00c01030300f41e41c10042d035410283e807010f00030b481940f601d51000c9141038041d800b41c0f0407103952101d018042641c2d400b04900b2248840e20174000002e00040200454038403040d150f0042d030b6449001c1011090a540044030100c0883c0b00e95030415550b699100c945449540b200c60211410900100ba40312840304014112000340035000000d0031420101c0c0c0402c0c90200c1550384 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 985565404 1250 985564154 985564189
    0x1050120150a0e01090b04030305070e0916020a02150c012703120b18010317070f03030203281a0f01091208040e0f0f16141308030d06060201050c040302 67
    0x242c0d140c0d0024030008158041d4080e2a40d8a0602d43c1c2c0308000c02110b03014030507070103601c08110700d9440c07543c180d4880b030746500103a910102020004240e00c8103150000b219400d148115a44214643d02007051403c0394046200050300101729490a80c10902408094606040d6440f80d420314002c8801036190b02042d004042c02142d985c0840c0b0540c0c03542c81410440d0004100600b5810000e00300078070080d0a01041d90220000607015401d0001c04044900f400c0e8061880f6540320754a88084009400141090b03a011004144000c0e6032400c900c8906c81904c810040040e58450440f444031022520540007801425400b4410b08140e07040b1810508a4101d480d11045200c100d240142440c0b0803500b00c0c5064104603070500000310805403c45202c0d107100003000801b40c507980c00503101c407102e0102600004066030240c0c2d503141c070a0070141941808025003d02c144d0f1700e90f8010f9045400420f00f003020190b44803001c00480d90309024046c2c0143c28000c4261810307065401080c40301d22540220203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 985566654 1250 985565404 985565443
    0x2060702040e1c0f020f061b0c01020405060307110129040c030f020c1c050f0301030816020a0801020c0d1728020304031d040e0601091d01090b01050120 67
    0x99807542c0c18080d0740200080305461a80440c1030303600103060000001c900000512a40d00d045541400025070203004080365131610340d8854038001038000941c050002c0d1016550207000004090715000055400b480d001d03200d041f1054070240c4120700310713007400c1ca5038100c082c404203000b8000c1c548040c0050312400141c0700800c0da0224558150054102540c04864003480000c0c0d8210b5001d000c203400410b01182400b00740618002107080703401c0e001d10305000c60759840030401040040d8080380100304c4004890b083c4802400c041d00062003400080e40a03100a0750001014420400103002e03031141c010141c00c180da080180e078070b1501016000101240c8202e801548000200f0ba080e24419920b500e03034417021f559902d0a403030010a2031107040d420517840500d00c000100725103054091a03150781d5010f40245501c1e840d202c610303400303807241d541101d805006007403004040031020301034000005e0041d15246080d52404000400c0d00f2010601a40000c0c1003403c05859900c0c04544148801c0c079204a40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 985567904 1250 985566654 985566671
    0x2070515100e0a0c35012405180d020f030f0a030206010b04060e0409111309060b040b013204081606020102071527030f03050c03060d0201140409060806091006030206070204 76
    0x2a0000b805c0d6030000c8454220a6000140b0320340802d0541c1001001240300a404041000701600c01e405986d0303048400700e05488aa442d10b08101801c0300c504c900051a00c01d00301c04940200e8101200391001c1c142a4005409002c24190100000307030050100340b1855103090726050b4018511400502c1c024852501c441c1c1c0041408081141c92100800c02000580c0d51800c03c00f0520042910000890340182002000003003440c052003618482001070b11040c440e203c640b154141a84091032400510b203010f2500c00180c509a84090000380003414020001d10300d0710700e03003001d10114a40c00369003160300410040c0700058984014210445100c0c0001c1f58455078ac400d6440d01071000d03031030754000744804a03012007850b610060314040d40d40c031a01e0410603a25213a088600512040340c006400c000030b00d040030019403095180341a034401c0c2c81005401d01da100c981c41342c00ea032503981c0b2070078890b88200c003404101502072021000e008081d000c1040442c0c80d59020070054010b80802a1040c0c0d0b545800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 985569154 1250 985567904 985567967
    0x8060a0b18060406050d05060d030e09060d050303130c0b2a0a05030d0906290d0212010207050c0901060518010f17070302041e05060d02070515100e0a0c 67
    0x148140200003402c90f07460f035403240d000610301c0c0c001002c1088942c0c00c1401043c520706044c1c0d20000740540580d10400c0c004911418004408009420590059003a031043c40c040f45062000d507000c0e052121241e80000c0860a002da141c00d9690010f6500032010403445503561480d0240c048444a42d080b0380c40d40802254419003041e1040a000d8420b0000040d03409512007103501c04280c1500c11001001040c1c0b90583c131070480c0c01300742c0b0b000c0050680314140b07040510305508002c0046100409082c3c0d80500d850099007642c000750800c8a05600c009092921840e040e000309001d13242a10300182047d500b40c440d114080d40305507001c1c0c144203602020304000ca100e4001d441402405c0c1c0c1640c0ca003801c08110003402544144550307143c030f00781c0307008200d5500042035049040355001014607041000100c084030003580010b070704960912600e91a50548503030741c600309108030380d0107030305640b4540740401c42010341c1c5000b45030b400c03205e1910180f801e9050f045110192480d010717104400d10040039048 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 985570404 1250 985569154 985569187
    0x3040224040f0f090207171303201011030a14040302030607090f050604080705090a060302090108011b2d02010f0e03090406050603010305060a1e0c020c040c08060a0b 73
    0x208610314a0014001c034011900c0007514040b00c6035105102101992402c05208a0144444c000c141202034a4000d030244840b0b4003601c400e5004107102e01e411a0384e030351404002d011207249100c90280c07207140d400080c42c0c6012066028880307410940088405d541c4210307100d03c0b80c1c403041c3c0203220303507080321185010314041920041d690140448909041813140684500c00c0c030300c200c094243d4a04d81c040b0795030030031000761001c03180c0d420002d04c016410b11040000541c1300030040c1c0d036a5030b07450744000007681d104200345000344541000001c80305440c0040b0188400b1040c210000d0103611011404600240340c80112818564003400c490030210003800c034094100001e01036110350a00520159049012001740780c003041c111030800a0030303960380500805010034030014020341c00110004009404079046041c850710504e15020348034120322404c500310703000070031244c0c0180c2c009100f101c80c03410b1612035501c0ba110203003040302d0795281503800183c54040074003801d8008a0041440461b299000701c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 985571654 1250 985570404 985570459
    0x90a020d1806050402091501022d07060c0506060a0308070b07110d0e0f030607020c0904172a0601030206030711010902040c0e13270206070218011712030402 69
    0x240715a589600302d007010000360105907026032080110401188955080c010b905204000c10307009040300c0c1180110741d01c036448182c02e0641a0801002c4040d03159002881b00718050100c68850080d41c1c0b01c2814424030f0030400500b02406600c1201c01800803441c0071050750030469015094070060f903110002200d802c0d41120100c65a4490814078041d2643c00040b0221000f070203403145a5070381d4042c410559504400d403284805a003001c0c0850803241400821580d10a01815604540301d08110500080f648140c02c038018000b0540c20203400140c08420b80141100d80100421055041d600014024400504000c06010181d0740e1103c0108081d00040c3c00c20380c0050042080c07221440740070b003048c07040c481c1d00d900c9000300d074850b411013070082d00c00c0e400c0003000b1080100b00e608075400000032640b40c01500307076407103d4180112401a41c2d0482510a4420f1400e104080395241200008008603114100480d07608030050884000b1120380c203603688540c0448480018034100010012182d1900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 985572904 1250 985571654 985571681
    0x30210030b09010314010b0d02060a110a050f06070806060711041505060309030904050606250303020f1318112706030c0c1b060d09080405030a051006050301020306090a020d 76
    0x2d00000007404034003503030301d8202c1000c03c00901121505404010418056010095008106004400300948143e00d400c81c0c0b05031a104540c0c0140d140d8482502e80243d00120072041e6001404115004c0e51148445812030419131313400303081c260035035580c00c1d001014900f12401155580c1e8164801101107291000410000d080d042c1c0e6400c00180980d02c0394003d09001e8095420031002c522982070040881e03280740540c3da114200c42102a108140b00c80d0344000a40405400348030300020805110000c00e0301c465040c202e074903480e18000001c000c0258a0071525549071400d1496000e0703c100804442c104140900a02d4020500071020032405601d00741980d00900d020040100c2c244055004081440145040380c2c03040e807095201080e040003490045420050a02c18940c0f0001d658101700b5140f846030701010305254840000c203140100b01c2100361441c1c0e104000c84e82942100d4070848000d801c4c00e4009506c1d41c640403020407c0c0c1c08002c0c2840500a50000e401d08c107404c1e46910400c07001d0641d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 985574154 1250 985572904 985572919
    0xb03070f030f020f2b0812270715140d09050607090801050606090405060a080f0a0204051503120f0408030a120509010c0e0d061d0f0d0306050307030210030b 69
    0x9074241440a682c007604100d00441e40310540c900f5a00d410000310f6440013201c440c074800f008040110041503640a4000c4450000500000c040c8100d60200ba91180c04134280039041000b0140075501005025245111981c010f20011b003c0700c51400c00340f940400a9080030b00b00c1c1420307500c41c01e01c00d01c64401007040c00d030324021704030080142c04100300b4000d20066984200c0070761944a8903080f200141c03440799004008104100c418185500b01540c002c07001000790703151544d80d1000038201071820100c1c103c6c0b0380201641004501d001e10400350802c40b2410b10304104080351020a56941c84110380c3e421103140030660360141031404044501914960003902d858502d10031024000303948941c6101a42814440080c49021f414424460b440700706544800c00c0240c0c08041c00317129800b03100c2c00d0300c01a441d0342c213000c0c48501e014801d448a4861400405014500424103403c1504282801d020141052400c006598000810a0680e40c040b40e555149554842050b00248401440d06070040c50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 985575404 1250 985574154 985574159
    0x106110a0b010602070e0106050406020304150c020a14010f0201090b060603100315021305030307020f061c020316030c2102030c19020709051b030c0706090516030203010c1e030b03070f 81
    0x24080b9046044841c06c5009680710703625000244c800340528004c039401640148801c201120fa0f1000d1003000c076000b810300b51030071102d41c1c011070080e580c590007203046002d003e00800301c0c95a00181c403074a030300c0342ca1008114501c010350f01c0550341d44015100a00c5040b01100ac5800c010020280340025548986d00b0085a2a00392308400650412403891100859014001500c0c1c1804403c80300400e07401880341042d403422108120a94201c0304e04079000b00803042c0114607450071480218003400f00003010b8441e08500040007802e88003590206010003061130040781000301d0020f039038880608012000b42c0c0380e03600c9804210300d9004406c0100301ea604e003141c00b42083c0d070300072a0500c02e032140144240050b5880c0e1280c80490600c2c2d045a040034035080000500310100c1c000030f800701d43d21480000c2070701085920340b0b0b132900d14030684403010303103402070703c1002145024816004005c0440c10410800007140c11910700b450208580c1e00300303040d15800040480d0f07400f07000c608060305004400040aa8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 985576654 1250 985575404 985575407
    0x11100605090c451806040c050d090804180b10030c0c0c0b0a02070605030601020c010e0d080f03011403010b1f030b100c050c03190f03020c090c07290106110a0b0106 72
    0x3c0741c1c00391500d0403a41c0b001d0445441c1481e8503206442e03040560010401c0e2904020300000706411076124041180c14091882102d445006100b5624010006c1640fa141070804c045003401c68191407001185c0307030008000007615241c0e034241d200e150030b0500045064540d84169036044002d00300512041440002203011100071000d80301d0360815900310350507291591801d80340c6210944405026a000c048100d10a41c450711716450388000180030400100f406983c0c030a0150041da0038082c00d4078002c00180100c4412090300e017002c1c0006c03802400f010400c0000f0546040c44d42400714006400314554408840c043c2c0c100038040f42c4c016040e1400802c1030940100329a0040e2000c4515000321200c1d05450310380054078070f01100150807160b6030080e1582d5514100c0d034070ba50040b410f5020318010040143d0700da60791280324251900e921580d0f0041c40c5400c2c1d40008001d080d00013109959080349000c0880c1040030b906607456418904984502c105d83d640c540f8001640091203880c12200110301c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 985577904 1250 985576654 985576747
    0x903150608190b07110c060901110706030b100206060105120402040902120c0a050109032a0f080703020a090903080a02090f03160915060c0b0705090d0311100605090c 73
    0x250b01407088142c103a2600c0d542294030185c02074000190798410b2120280b980340c0140207200c411790504201103840c0d4a4010142002c540343d0081c004280e554401000070b00700701d144e0360a10800d51000e40304d0361601200107880d50182e020f144c1d44c40b5203054000740c11074403954044640d07140c0080c00604640d000303400c19070303882034050a528010b040c0c803e00000e2135405141403d007542c1d80035035103081c180d6216030200050355580e2511544210307480d60004840c500b120b6614068a0410003900565045006002c1403800d960702c00707104146065408400300343d2010500d0b400101001c1701503694210704000030041d165811030b455240c02600003030040b60b06041c41d000211a0b0384102480000340c1941140c079031460f076106600200c2c0e000341042c4000b0f503814120952141c1c00303083c114201988500400c000e040d03144c0045000c01d642012140c84d5242c10030800c03400b00b14605041c81054140000b06172030480140411442d58400b040c41283c1044001003403007101d03031019112000c50002d03800d2141c40d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 985579154 1250 985577904 985577953
    0x402030906010315021206131401150207060806030a030e06300106032a03060e04060e060610020c0d08090607080304110f0d0b06010c0203010203011d090d0903150608 73
    0x402c030340031138294242000b03000351a5440208078034160160790322402d01ca4140c2541c152010b445980740000000a000342c3c0e851400f03171080c2e03130a40420030341c0c031030010b8501030041d041035045c021200308000f02940c0000b4907003003040c3d051824540150349080403030480d01030701442c0602802243c440c02d91002e6481c020102c60904080100c0d000e982c0c82e0b5054003142d80c80000b6280c2e81d001c00402c02241760303218200e41200050380c600000c240c5d41c0c41e088002403410a0b5022030300140c8032120400c2d298000c000300394001901700e922405040d40f50b40c0c06591303107030003041c0e050040b0600090340d801d002c0760a050b80e86a01c0080c041c40d9954402d8580302141d548211000c07140340451901a0b81c1c10b041c103204c05200b40101a103000340404031501c1d40600f0799802020343d03041000035500701005803000e00146000b0030001d5106244000007041c17155401030002e203d4000c540c01050f03130a81c8a984015200216a04010010303100030b145011500a400703140c1208010348103240d1140c2402c4030301c0c90308045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 985580404 1250 985579154 985579163
    0x121f0b03100c0f18030804151701050306130804120c05130b0603180f0f1606080c0d0209011101020c030304021003021611040f061502070b03010f06030504060b04020309060103 77
    0x1404210710860781224021418107001900c0704042030030060044420b8403110391a014980003103662a5901085503010340c1080c0e182151820005c2c2240b81c016003811017401c180488442d06604040100360741d100010000d418a01c1038031154002e02003003030211005020340d00c1c40f07011099082d06055405009510500d400341c0c0c010319620242134050710841d000024014101d904c3c6482d5000104103103050020030280c1800b030b04d540000798801c10041c840b4180c04500180c228601214030040c03007a04180c1c841801c1c001c2c924100407032203030120200c0350f140600c0040141c031a000c000c0102d58605003012070704420b41c400604800c0c04074000010b18895442100c0c00d02600e80c01c80022026805441840c0c05000030350500b060004194807a0300c03480c0000584001100c000ca1545d42e4151342c00b591003004428001000d021b5043e6050022002070201041d000c0e186503d00000320040c0081c601c200c0d020583e40e81c01180030454160088000c18100403c19901d90a100210685070142072000f140c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 985581654 1250 985580404 985580413
    0x617070b03150613090c1106060621090f0d08040b06010c1e0206130902120c0c061f0b040308090f010f0512060d0803011811090d02121f0b03 62
    0x21030000403021640701d40e01c4100340c0e00c403080d0b912003840318070380160184d12641d8030180804035030218144602c0000ca440d6a031861a0290341e6500356003000005098940250300400c880d00f0814540300b0107a922070b640510000341d607034814400c0c500f020010480500c960141d4030528009542c009002c900540c01030065510781d884150055075004140e0000070003104020020001d19407106610400d81400503002900d820b54101407205140d0f0140c000041059002c1020b0010000410712aa400b03280b1084840c640641960300aa413440c2c01011203491800090040600c1000f00301004000d003d041c40c0940c84544a02c5d04226540150400034040c201100c50390b1030307540c418604d10540c1c0c540c945501c1c1c80d00d0407101c8000014100200440c0e00b04101c01520000070322140011402411590000d00c08000c04001d100c2c01d58044186844861901340600c2e04150f4500080d581401c2d8111a207034015001e240c0c0d014244900e0807030349106c0f244008040940c400790b5030402140c0450840986 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 985582904 1250 985581654 985581659
    0x7080c03030c0c10050f04030807030605190e0a051b0d110a0c1415070e03010204180608060106050f040b0a02190c08161a031e070306091b02061513061707 68
    0x1110030481e45038a01b000c0420104000c03034020740c2800d42010041c0340201d880b40c1c503680070404611040d008641100440c8808001d01000b5046198110080303c40600450902e0b001034421003811020000100c000041c5200c3d40000603804010480340d2a007449032512240a005014100b41030f00659076001c0e50700c46062181d2010907021120390340d00405000640358600b048411003943c0d1a1560036646c2040041000e601502d0801104001c080011510905140009041c60410380c010000d02c030f814408090050700290984060307441083c05135440c1d5000700412440c00848056509060007100710720030a10984000f250152408101210322075030f62403a101900813000d21a030181c00c0c04036011901c01d80c02050055400421014200e030715000040c4888115150565202000c25560101042100d45500525414035494008103030418140d560103910b40800814910550103907104840042c5e40d0107000151003014070001304400f98a8210f0305544c2e9844141c00001482040c000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 985584154 1250 985582904 985582933
    0x10060305040f060509010e1006080111040f23120f0d0c0308160c02030609030310060c03050306040908040918021206010312110109060e031e090102030f07080c03030c0c 74
    0x203032402240d008103101515901526403030000c140c050003030350b06552118804000601c0030480301c444001e03203044c000f80d40ca203070251050850b0b000030a0b000241d2410307c420050143d280c1d040f0002c50381000d0004042c11810a500c800e03581c00d420307026034001c10f00d489840198900090034a040e203400801c542c80b0040b40e4805035000c58010400031b000581c2880020240d00780f00c9400c0c103446a160401081d2601c00303500082c100340c002c403111040d9520101c00c004590b601c9c040c40e100101041e061110220840d524020310a00c00100b6480c0074a444a5000042005440c221802403815400c00c001c040241c09164100103011f070000c1e0305c06d944203490030352214008910300d07040b26031101c03c200c1c203a1aa10820b40768000034510381c1d000d0307560321020070b00802c045014110042944002640c0d64000d00700112025800301450741d992510700303115806080c1d03000000c891202165030000358440480b0300d001a101c1c0700e6020440101e020200520a502c8030002c054050b91440300117030b90740030030780e00d10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 985585404 1250 985584154 985584161
    0x813050d0f1716110334050d020603041101020705040e0f16080705090c09040c030507020d09080607030e0309040204030b01030b22022e0504051002011107021c05070b03100603 77
    0x991040b112009807103000413940074602d0000c000141c1550014240d2403620f841e05d09410101060404103400c1c0e0000c40f419420307042024042c1120340818130b01041d0017180990100030001000b240186440326056030080040d04002c181c000c000381b1114010114590311002c500d00003039842d21900e1981d106422000c41400c0a54828a00800001e403070001003091010025045035468001040041015255802070315821059520301281c0e0303040007070340245008000c0301030030100550703800c0510900402041e91504418280750100f8290920341c0c1e43c03401c1d4030800100d158071610000300001040100f400b01c07412039024600c10882c6d5582e50035000c030500b03014407502524500364000ca01c0103240c00ca094111044694079603800c420766041071080c80b04100002a00441d401107400c028500c0e00000158950440e8402403140540307902500b4402d005c0e03004000d2203982036207550031a890100700c4446409421008545929544145094041d80280c802c0f01002d09903140c04200f0900a02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 985586654 1250 985585404 985585417
    0xf07060f0809030915073201020304030e010807090e15030f12040b0a090503030703120b0301020901090b09030109150c020705010c05060604050c0921100b0a030813050d0f17 76
    0x8000c0c524103c900010044048007505001800c0d80061150750301140001451f601c00f003041030b54802d407040301400400304849058031044072603030040040200007075001c080c2a00d055002e0800c07000c1611280015900d040c100d401200d084038524041200c1c44254028403046e41d07009405840b200c0b0f01c402d0308141c8a0710100381042e801070003000308008903450075005240c495580c7c5043c1450070780b100006400c5501508059001803800a03c40c114491a403252001c0290128001c43c5441404800a0f10303200301032180c1002d205001c87c1030316840e14290409102d043c0e101074003e41180e028032600340202130070540500148034100003c101540550014071a580d0410020061a5525402c12018040060071a0b00120050000c4110746e214042c441443c400503d030400c018502044030286000020032031103035210f051000b161010386405c041d02007580e0b00700d5955a60352940b01103501800000350b00c401d4002d1075110300c903c2889501d01e018840700b4400c101500c2200e2400700b00507007502509 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 985587904 1250 985586654 985586671
    0x40b1201092003150c03151203030405061513020706090803101d07080c03131205090f0a03020a0302402f0c0f0703030903142116050f07060f08 63
    0x3c4e0110ba03080110301d0103198007200e403210f2220040159800b10b5004440e103a84030140b23030f00c080305001c10003005000603640080c0e03810b03d89580341030301000521840c08440c8010310b01980000d6500c24040c1da5080408000e80009c00207943c0e0030a014462441d009600c100c2c0340c032041c852603440d030015903a030415010b0011903550071816281c801c2c0c2c140859002402104601840400b03600000d800180140103110440d10340a8856a40e1010300c240f030050340d1102c40c8580c140c00002e00061395000306100030340390190313488100c8562a400c0c81451101d0724052000351041c0b081c441c0f03000b0265207150071405100450900586403a00304e044106038809050b24628608600400c071401c1084c005008000c0d540740440324070803280104181045065001a4002040c4c0c1c0414028000e240e0030325842c12112800074034a45040307111108171003100d40348030403820b00b0014083c0030388030040c610b1410607078210003907943e0100c4842150355143d900e441a0b8000c151054403801403c2e011307a80d100e110340c0c3d01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 985589154 1250 985587904 985587943
    0x1407080906060d02041d0d0905010f020c090c371103030f070f090f0807050103061208070609021f2a0807020607080f0c010e2109040b1201092003 64
    0x1d51342048040c28081940b119000c48450004290480410641c0311500841e1500c0d1070351802d000005058840c40906030095600c82c100030150f544a0f190540e0340a2103d21100392100c140100005000e803200c0075421280299000c074a00070708134035620b01d00760f08a07901d900a28100c4015900e45901048400190101c295800a031002d40078408120300341d162882c1c0320b4035864856649240ea08455001440e041d1310003002400341d540c042c8164000781038150400c00748180107030b450f51114441c0d000001c0140f070f22100314a04544952000124040940c2c001116243c0f03440c00003000c400300c0031302510f090450184485100343d001c000700307255203400600003482c01e011a0280082e541c81800125001401003200300807420030103010702544c07d1000c0c000b01c0c80312144001c4611709a1100c121030100da036065110340c18034050100726481810b00f03031800700b94140e40c0000a070300b00c0641c0702440c40c0d65081450b40d45c100301900900c4c19102d030481e404001c20500c4c030000d25a23150f01310300440d12000312 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 985590404 1250 985589154 985589179
    0x30c090c1204080d090f0b070201051b0c03090a06080403080a05010506090f0f030f1006140d02041a0a140a0803090105030708151903060b150a030207080d140708090606 74
    0x4182401c0c581c0103000b1000c40b880c14418000600440d0320455050b03a4619035103400408020b2014902c42d08803c1c5440280011f0501945882e07e03a40351010000003034200082048500702c080c4151081c15038024034201b08c413551a0000b0b41001801c50f41200040c82c040c00003008000c47e07104881c180c400240101d400d140054050010a100b0341900300d501110100030394489c0d590411070b031076145000401602c107984804800704103445042c1c0141cac00c5100c0708083c1c01c0e0315441d81011000c09030380444010400102183c25864190009903003181c20a1151001080100c03690400044545082e100b1038400c65480310080e869000d8040c0d090b001801c10004124020301c170b0000150002c0d00c1070313a061984100d400008a00011401003014001c1c2e51507003c20901c28144582040944140c0f58000344d07050940a0b22824481d5002480130300d640801da8400b0720000209507119400d0750f01c2c003003115810300c00e0078050a40d41100c0c0e50001560307800003e65180300c08070713480e03000c2e00700589107540510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 985591654 1250 985590404 985590427
    0x30c0f0e0f0d05010c03020909090d080f1801052802180d1a0a0f1a03340315050c0721030207080a030b01030b03240702030712020606030c090c 63
    0x780c80800c0d5018000c1e46124020480a21034a000083c2c59140146e07990750b8541841011030f00242a101e03c0d800c00300c1d2030584550041040399001e6076148105e4055a161004404020511420f403c003039031a1404100c1e41080880d1210550f00d9114035895880c00d00c10702d40c100341c6c4505052001710707020000c1c600d85182055420071034503030322a210340000e05c92483c031410420310341104d101c50240d0300c1f41130003c03000c15a4819294140140751541d03500005000c08a56941c0c81d011004240d11100c0c0c80c01c4030f00010035001c0c582d8040d182e0440c0c51246035030703007852122080100c030600c50036460280413409686541c4d04940801e613000c109003032034000300102c5c481713080001c5186c1c1040c19000c1240e400001c00c10001070400403810f0314001051007a450004085640e00301c00c0034001e521840c10000840101c0d601c41c01130681900d020041c0e941e50703a034200c0c298080c081c0010001640c540f2940c0d41b4513004901180700c0c0301d0590484110700d09c040d0400030030280544000c0c0380139204100c0c88440b071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 985592904 1250 985591654 985591669
    0x5250807210801052e1b060f060b0901021504020a120302030408120406090603090503091302031504051905180a08030f070206070504031b05150405040e39040603030807030c0f0e 78
    0x144c6a50500c0311902c512180001c0c0d403d040c2400031910190703100b488c0c40700001144034000290104020305c47c1011720850020b035480b04003025591040c0c602c00000ba0455440481c01000740c507a02240030800089460065a2504140035120b0940038070200c251000c0c1c1100e069400b01c900301d41d200d20700503141400581c028002000d0550f5607000c100702e000440c1d21303a4190b809140355000380c0103a41e490007440d00344803520310303000981c46942090184030052280b0b90701600311140b0481c00185c5501c40c40341459100340700946000e181d024240c040401e110480b4003551043d29841c0300360800e640d0f000d8040740c030354508851100c0420003e00040c00400c0d03045514511200e1a001c00250b12906c40b40040d1041c112030380b01101025001a0601c02c0b420940504003215407048018042c4e02c0a4550b0765004003500460100781030415001603230a046124030719265040090410481d0a4072420f005204200407101c13400480e05200900c82c803170788103084a401030740c095540e19801600210421110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 985594154 1250 985592904 985592989
    0x102150a0603080412060f05151507061b090806040b16021005160f0201020906120702100e0a17190806010504091b020d0525080721080105 61
    0x2410740d240800b00000300c80c1e00041c8050706900704401a181641c1c03030039406480c83c690340f02c2041e034217100a02c120704268050129030b039041110a0003151708200114009402111805840c107801d00dc102c418411075507442d010b85901c5580e690020545a442042c0e4606042d0780080c94040c0d07880c0028000c1d0050f11000b44804400c1c4140c9143c030720010395400a07130f00265424105c0c9103100c4107054500b6004000700c0d031080310750f000039401d10881d000011000c0c002c207482d042c0e817840081d0006801910030300c482140b9a21006003001141e1042c003c00d0795840b41c03140105c0310700c5840709004030f6204900c1c040c1c07020004011a000c41d41c52161004035203600020b050141031080c180000314400089006014012040c4c5800507000031340410020b113000790141d500c6040c81000c108825804000c14101d55620007820005001d500052502880610600700040c24a000016a16095405003155041c0d00072180d0741300c0c2010390300c1d04104180091008100c0c803540b010014041c05c070310b4408224216 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 985595404 1250 985594154 985594171
    0x6050703141911070906081f02190306150305040506072f0a0b0f060325030c32010f0813120f030507020a0b042015041a0702010215 58
    0x91086501d4001d051a0300e00c80048040f039003c103014891540204039610090280100a1207010324281d2070079200c500e001400c20600c05450540840192150100c0b10705c00542c01e8075a502e000060801030040c01180100340e5002141a2810a040d100c0e000d1035020302d4200002c3d2502da120b00c0c43c192a010560403400050401201461103103202c5a0010000441024090001c041c911320300392159140041c40083d141c038070181030040680b40041c1540d0098074100322540e00840d40f0048444c2c50185500c02820f0b041030309000304a8a4410f08814842401403c2d41c4107400022954841c807010a4049640000c1c40050b59003808e91140030010b130030a00419405421040c1c40d01c2c0c1030704100e40e034036640012400081c4200c403c42e62502c106940840c076407001d0b00a04c0030360f6481154840c80035201420904c100c0340003100448800040e040c0c0c0c1000104049003200b408120001540c2180c82402500c9407000d401160a82d1f61000700c400781036050780600741402c0003190021505030301a0a00b81e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 985596654 1250 985595404 985595407
    0xe090705030d020f060610050f071b0906080d0c03050d0207170d1506230c0f0109111306030803060907021903180506120a05090c04051311030303010605070314 70
    0xc85840034055080415803541c007602142030380340075461800401503ca00d0141882c046051039055014064030b02e2200900301981e0340c0ea0b0141040031f0100e615109500303004c41d85140c0002c81c44140d40c46113003100d114800f41c680350b01c03406c20700380c84149440038046c0204030100705007090303c901540244a1a841802c44101c19503014048030220b4000701e840b158429501c3d555083d8401401c180c3c0c0c0003e001340e00c0d28902c100c1a085915240074004007a007960b140c40482d10303a000250602041016a024034020807134012107040a10361011403082d45800756080c1c0d4031078400d210040c0101800c1c3c1c0e400c0790380c1d240f468a4280900c075103080014031007011809041e205106814900c140703004014002c1c1e40f08025070300c001d0a00241800d0700d0340007600c04c0a0411858032900c400081e61a4030050900e000100750382e90950f40740c00e04030340070384040e4002d2803c410400003400381125440e80700d0055400c0d00c001008070b400c1c595284000c1c0188000300300f05200b0000042d101380810680c0320340070000389 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 985597904 1250 985596654 985596659
    0x70b0a11070e090705030a150c03091e030e0f0f0f0a050d08030f070e130c1107080f060105060906040932150328050102040e0c1b010c090e0907 63
    0x298106241500000061180342c410b00450b06030401030031000c2c002c1207024000c540090b0395001d00840070030381e0101c9055250402d01040750b009500102800b600704404c582012180e03505003040c0040e043c0201c011400020031b520480c01c244051310620792001c0c00c1e0600340c0d0600c40030011110002c4034030703d511044040d00400c0c140c46403d50001090310502c003494603414642c82c4010b017940000c04090801c41c0d00b41005600d130365080001d000c0c60f5241d5400081c0d4222420b8200d03102032030f070524004203211b1608005181d040c0010450340c100614401e6410780c5e600c075001c1060741d10072008129400764040c08180200700321507200002c560380520885182d4a440807500c4a240301078980c040c82c0580300740402407100c20244140d200c42400302e0103004801d108802100544003812482c003d01c02018800d0401c01074258112005020454902002490203070044005035020408150701120360100121130903005020780c0d1101079050700e4111f019403c20101d500a0700000f880320360180b1820000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 985599154 1250 985597904 985597937
    0x10180b04050c101d030c09011206110a02030c01110903030703080c0d15030b0a060513200301080a02180f07120b0a0b090418020a0e10090507020604060507030509070b0a 74
    0x1400b0750300780313038903240c1c060340b0354206900d00c41000785105802600314445a1201e0742e500c1c51200c1c15500a641c070420119000d0a021005040003403642c08610f01c0011540c28280d000000790046440301002800b01c0c4071000101050341c01203041c40c0e13416500078445200000d014021044e4041c040002060810107403504100030340e90082d100c40071400300d031103041c404c0c841a88100c541c4035030900d00510881f403a000c04100104070040100f0006640c5902d860300240f985880141c55400c440038240e2656142c504881c0c4941030307074108a126405484c81040c40c4d500490280e480f9008001a09010341d607102d20656800c601d508102140070b903940c03c07011041d602d01c80e1040140441c0b070705039500e54000703100b44411240d1404081755940060840000141d803190900c0e4191404c80941140e140c0750450346440c0500f6a4000a60482c14001003203000380c0c0c0004e9091045000b201c05100b030351540c00f415000c4600a40795560f640e0050314045c40412920001051441c8280c40c2109d0f2401d182c049 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 985600404 1250 985599154 985599169
    0x10b0904080a11061303030c0806010215070c080d0b01080906070504030b060112090b01380f04050d0501020a0f0e0d2a060e130204061d060f0a0309020310180b04050c 73
    0x5c41400e4145201c0807601819403600c118484030031641071002080c10120b0010f940c440740d014658050400320030008240a100d89010300c11039611044582e26030400c06001009030110300c1c1d01500280781c0a000520002c8000380950203441d43d51901850241140c48442c170385600280300034107205600007824041070f02c0c1d100782c0180078081c001d155803a50501098000111201600b4482e80380d4104060301000c102d0940c00d050014549843c079600d615401c042c9100740030301e600c900d5000c07519175950424040107400428520301160f8450511101d000b405079841803c002001d074201402d10b91800028419110702c00640f41045980d0b04100380028030040c54803483d400c81000500192a821454103243c10394500c80c0080c02015800e15040110040464030040070891807000c03006418900b64841408451000c10b0080405030b0b02e81050030090b0240107059022402440340c501c403802e120840c3c2c0700381c00110070a01182d840f200c1d0716480b540c2080e500900251250300624905100c03a1f86c9641 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 985601654 1250 985600404 985600411
    0x304050106122307060225030203010e1014011a0a021002160302060a0c020c2101110a0806030c09070513080607090303090f12030c05150408030a0608010b0904080a1106 74
    0x190010031000031000c0c3c5101c0c0d44440c0e1450f1101c0d0320030141486030356008100d1039021854800702003442d8250303400c0340c0780c07802e055400650554609400e0749414100030480200d001240001800101d40400490300c800b0001d00c1640401148030100d40e1020421800600d00d85a0501c1165902800e41c480e480481e1310200c0c400c070101140907620810903405106199000b11111810030841281d108080e459181c00c5842600c920854004545100400100751155254100c001c108444103d50010156848060b00b100410081d0f00000d81c0b520f40006d9817426000040d100304e00e540c0341e600701990360750490b5400c40d561800b402400300d40c1c1202041000c1c8208555a10000e20501d9130034060301c441100d40007981010a0444284095000102e080c61101e506161811a880031820401d092001c1440c0c0c984500c5181c401b07100501c48020003550103142ea40000b0413241d40d80341d01013401c0755031082110750860100c50026010400c070b6406000710702da40382041070040d41c1038226582402c000700c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 985602904 1250 985601654 985601663
    0x10e06012c1518031b0d03090f0803030f0a0b0f060d06033516021009170c1201060302210a120c050c01090501020624130212090c0a0b030405010612 65
    0x229079503841010443e4607143c218400d4018022150b5a01e480710201c1c500329511602400c180400501054440d4041c48010090480070005036031f00c2d41913440c1c595005803982c07107080e500c81020071b02c1c604080c483c141c52004020054014404580c0c01c3c0002c0d60000b000072140c0c00d50b03c07000040414150710f1580d80b40d00740302660080300c1070381d4480d500e00418414003048003c2d000707120420102021202c40c0c8200c41d01182c4e540481003000500311000e039500e03081100b82c3c0c2d2200f011411101800a8010700700340d4201e4410303d8080862410a007220075600c4080d41c03120110008180c4042981c000d00300f4850483e040e900c140c805d40c0c0f0703203100c4401c040740350500007010001c901003401010b00286580b600c00b40303010750300c1c03502e4800000e5541002402440700004403c00c0089401258010a031600e20041c01c50348045a10081000c000e4001e14030364400d0381c811400244c0e00d0980402c2004400e50000c001180d5903040c03189441780f507080100704a500d0740d6620300100d2801012440c20040c00c2c4907 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 985604154 1250 985602904 985602907
    0x402091c020a060c080a05030a270507060f120209030106031212110a09090e0c150903070b031b1b1e0c010206072c1302070b010e06012c15 61
    0x8070710501481c107000f54815820402c0d01644100002c50002c211201c0e1043c620700240c8070b03241c041510000b4030800c001c5920303107140d1080b43c181340b040c0d04817803122540c062000d0350b10165a0310010350320141c42401800000c2c00804004481c01d1851340a000d54580190000071003d449944000105581002e0b03031000c69440c42031004245041d0103640c600c80c130601c48950800c241e01c14098801c412a0044a00907a125403031014444003c11290005c240c0c000e1042c59119080078100003103501c1815030743c2c06406003030300124100e10340c81c003101c2c01800151885008580814800e4200e80c0060425507a07130174452000c5201d91f4001c20031820f0b01d40481a1100d01070740c559404900c1c6c11010050729055401c20803c0107a6550040c01c01c0390490400040b40620f0009008410003080603502c1c0c03960f000760214855448541540e014114047c8034070605220390345c856007082154803048403204d00148480648884a803034110f49850b05c0ca040c80c40703411400c0c810100160200c086590b00d9248841c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 985605404 1250 985604154 985604209
    0x3090f060f060806071d22050f1b030402030a12050403122006060a09020f0c070b0a030b03070b16030509040504350415020f0d09090605011b11040209 66
    0x6084c40b42c160003c14600f0401130000404d000940303407115a80d11144a01405100c4c0260114064038980d124060031104103c2450100c0491001560580d155400d103c407888094600540300403c0b223010702d400a00410b034880c01603075040720160b02600711608011051100000144004040c11490042074603820080880c8032a020303d242038000000d40103a0143d01030202e180c03034415402c000e41d00030400c0981c0c0d0380d00e0100e0f2038446100d00c0030400e150348926200018a42c1616006d03103003002495409000008071801019914403450180000380c0c001042a94030105240c40c000441e64442c0c14210300f8810407600113000c0b03540448050b40d030307038202040080030101441c16203015102c40c000c10071000580949040300c0c030300550180c00002c02008960b40c4d2403034020850b50b072107141454100c450328088044000c1c01003041e4802c01c1c9002d0705040d404201c0f507010f42d10031038014000d46081c80b00380415890b001207928100b030056420950030424142030b901e0f4420303400f80c6c0d01031181d4608480b09 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 985606654 1250 985605404 985605419
    0x315040609081b10091a060f0d0818030715051303060903021c020706020a080c0c040c1e02071505160c1707080601050a15030f1a1003140703090f060f06 67
    0x1904080754044681c1751070300e4800040e44c0c001340210b03411130380d43c5000c90a5544d00007141c4003c00218000b6801440703003483c2d80030442c40c0b6004100c02405694960418021042810341d81c29072400380a913041030f42c551110324a131140300640000961a030304031100954070307140c0008507000d003c000e90040e000703440d070b48a00040504180062480520081100b07514100f03009445040c1e40380c0c01803a0b0580010705000d4820200048411301100820404c201100100084d0a0748a00920710f000aa0b20400740c0e18998004516a42140c080b40341c294482c1c0206a0201e078181d0000030640c101d44414808034000c03400c02005c00c2d000c1c01d080c0c240d4190301124031214034904000780e4410700c4240d101b036006124503110140d12004641190401480d003510300c4070700798007a0680c0c3e22141c0c44189400302c9103401d01503800344590a80025640360b10111140c243c201c094aa03c001450780c20a0240301041003d4400c0d440309030b08a0081c8441d80459540396290b80541d810100c03100112901e44405202c04d6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 985607904 1250 985606654 985606663
    0x618030b0a02071e0308190609181505011406070f0506070f0e1c06052203180504091a090a1502040509060102060103050a031206050330090315040609081b 68
    0x8500800c2d40d84d01c40781a41d500801c0c564000340f4400c016500340124215800464211201074039031903d05102e6020404c2150744081407240082c0c2d04815041c2d03120000420030304c5024103079420603885080100c05181400130325401810102c03803920a140e03200000c1002407090b54060b0603260b4640040c010b029000602c40a0a102080e10a00e410f60a80b80345880303400c40865802d5020b0303008220341d07480101100b100c880c0c45850000d0680c009001104141c0d00050b0040e03010111012040e0300382c1c5480c1840101c920001c4d0060448180820030700864108207001c0e03610012120032144110400d81c2c590314a0115284410403454000c28240900e1500701c010a60041003880201003662451b20384654440c00908040c09101d0300c0703142031440e00c100350441000350802038121082400030103807410707103009070f4002c1d030004601700c4a02c284243e00000455048a900800409003079074403200444078194084c1c0704980d000c0d0f403050a03400245030341c8094000b96042d10040c00300d00c1108000307242030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 985609154 1250 985607904 985607933
    0x8030a080f010504180f0c0503070314150601020d0c06060906060509030c0612040609030c08121f06230904090b0a0e0d081f0915180603030203040618030b0a0207 71
    0x1e5013170402c04501c190030800034005594021403ca14480d05505000500101903001030380c041c0600640801440902d24a9442d003007100c01c125075107640780e280d030300010781800d0b9401030050b0004980b80c03051610491014000741d00071207000942965039840c0d042168044d62080c40811804140600340f890240103103580c21900380d615626001c20501540d10400d0020300042019a96481640a052080e0355911425500c040301a0f030f542d0001a0342001d941003240c0e41349469580c03401038004d40300100c031908216911a190fa039000700706030502e1034042110388101d5084101c140b0541070345641c2c2d4050b008d2410700580041c842810281440c6040d1103040c0d64002c0541d211074010400c8076480b04690303a000c40c890503410100d004055103280851101c0d80170721031081c1403449100041b200004214102c039940500d243d0748111040c48501968541d11010780035030406c6c0000c00500d4000c0759040c040a08507046072420544a40d642c10b80040c0580e581c8451a5000c65200c0801000900c001761 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 985610404 1250 985609154 985609159
    0x1e06090e030703140f0c01020d05061207030206091e040c0f0f020a03050d0902030f0d0323060a06030b0607060e030a0f0e030706030c0212161a041101031508030a080f0105 75
    0x1034060243c030081c02034030101604100c0710000081c850803600906007602d0900e9a000001d5541d0070124000700c01901e81911900d10171b81e80c5c00450483c5070b000041610440c2d60240c4814240740c1c803041001aa15070f04044248403545900f034210095803070f44941800c00c017807900c43d00300c441c1c6a203400418100215065400b0340d4803021070300022a42207819100700c0420b00f0070201d4410090b1010a00b4104c10101a0005100d02c0703070040251609600121280400d944141421641001c610428403a09450b03142d0000e486920900009100782c0100314040720103000146041c03140d59428086903140e914a000310341000c0340402409a214030b190194031264070702490310707c400303070b00181e1505494880c03a001d0643c0e40c10070a103218000d00819400040104149840e58003048401c4065046504100c8500c44013044d0b01e502c5a94419455001e960400c0408c640251480010350042c41c441011401d4020f95280000341000104010b104070700156403421001c0c20b112030219010101a040140f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 985611510 1106 985610404 985610407
    0x313082808220e070912021903020d0305070501050a0204031a060112090c05092d10030b01031505061e01030b0a030b0f15010e1c03031e06090e03 64
    0x804844484003c842169a601070454642e501d900802000c004050300c00405400e00315400c08840e030038400a450740507140d40000d007800c95080e81c12000918001100750030441c080c000c580c1c115400c07a20646c06d040c199034454024001000003621a901510300040c4660700c02c090303480ca04031000c9000c01c130f03040d91800c2c498484003031030141d2801f03425680082511182c070b14000708880804116403203000075100071612000b00010740400c44c2d54030755902c044041034030705586900941c401c9094011441c101600e1400380c0301c0c010003091140d581e0b6076824125802018216620329800d1a0019400c5002c1000601c01d11281d0030103490381d5400c1d0108030306150700900c101d000c1d141240800280f0010140111010749415140a40000f000d0100c0584074008070007001c2d0844c468107002c200c100360804004805245440c0300d649003525840c0c10006c00b411032180802c5c0285150185 = true := by decide +kernel

theorem cover : BRFrame.Cov 985431654 985611510 := by
  have h0 := BRFrame.cov_init 985431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 985431654 ≤ n) (h2 : n < 985611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
