-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2722
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:32:59.045098+00:00
-- url     : https://prove2.me/submissions/096a3656-4d6c-455f-9d84-3d4e24c1a776

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 489388489 ≤ n < 489568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 489389739 1250 489388489 489388499
    0x204090207060c0c0809120312150114090a0311120a200f33030a090c0801050603060109020c0c040218010221030f1801180b01080102040308030c0a20060a0b010507021e040204 77
    0x32272008444030b250b2900701e2500826590f0388540000c0c8440c10350403900e42407902601c00300c0c0030000c03240002070941c1d89001180071070b41e40c0c505690002e049180200c40c0600c4440c44c004240c00142a00041901800d0b04074044610306a105c0600d168001307003a5200b180910b00c807483c1403006150605c440b9242c0c008602c1d01c1a0b804d040214480d040100d03003c5203460491038400001041d40d0320070a80e603490001031181e02d80d000720740d00341140c801810140c0c6900c1071500040c01c051a9001e030560041c80001c000c41c0000d4021024800c01109800380e5000110008031084004900c80e003120300c80c1410000200d1815204001640103801e441030034484039604403e8608560b6183e541d11002d0b04e080c0401410040d03154911809000d800000358100352039039884004600002d018400380407804980b40e540d491080d45030480000e203145115039031110103504151107880030b95044011030308200392280d0a5004a04680003103a0260005601c810f040100c4034403180018011980036800b0000017070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 489390989 1250 489389739 489389767
    0xd020d080702030d0c11060a080f060103150303080a0e060c1e070b070206061525050a06050106050c0705040b01050706022b060609090515010807020c040204090207060c0c08091203 79
    0x72000400b9200c04140385c5003400c000700600c1002d591716119a408100000d10140e00141954100707180b10561000c41c0c440d0380050b000340007840c40001941501d80c00010070305a1042c0c0240c011034240c601042285450804952185800c0b02d0305220800d0420803d40340303d0010040801c952040c0c9051820100145e071228030302542076a801005a00c0502840084e1404030340c0c3c0a01039000702080e5140c0740007c02c0d2444100700200007070238500080c04002c01070207414070281841d20313800801000b040da10b40c00040e205801070042c3e103c10f4800d031040462503060510480c1a2b0000c16115503050007030b02e0362040040d40c4503a0740d0a13180c9c40316200c2c0c010081074a20f00d21110080c03040f030104540d03041c175800903d0910345a0081c085182403000b407202e060314011443d8603a040c2840e0501480d0340300e41081c0e00d000025501241c00070303c002400251004141e000d0b00000e4802c3c007007804460703032a14086a0513000088003904403a1b00b00301d40102ea2509810200c078006224042da414940b107490001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 489392239 1250 489390989 489391003
    0x509030d050a0e040b09070c0507090222060e0f2e0e12060c0a0c170c0d0f0309020a140a05150703081f06080c1c09021e0d020d08070203 60
    0x2020850106a480d02c0b02d81105180c094124180c908018280388080000c2d04080c01a00d20814005403020000a00c8401d014003c043c0c03030b04400a41d600c070742c54601c159070f800c2d8000017110066100c0c000030411a10803103410b0b00300c5000508041c00280e980081040e11b41e8200d518a02401d034800d10f0400c524a051041d20346580b0540740c1100d00f203102070500c072100d60403a036008215080201002030341e02900090740c00b01081c03440d010102c0c50765850092030718440c1e038000b142a21000708000b580d060000405090710a45650384030f01000c0152000c1c2c00795014803000030362128401100b408002442c0046e841c218100401411125682c1c0e008500f003038002c5e10784010154400207108040c1600319681e503400100044d080c1c02c000c070319125110b43c41c2005004540401070039802080040e121340003948d5038900e00051200620001540032401408110030803401641001125a080291110000c0114101501800503c5903540c2040b0f098008608201d075880810300605000d0b803800c110003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 489393489 1250 489392239 489392263
    0x30604060f0b0a080303010b070c1d010f09020307020d0e030c04090b0a050106170c03060103060f15020d0305061516060e030a1101021c1a0405310305040b0a050903 72
    0x210701001a03000416181074104075070103007881000400855400004880c111400941c1d0640c855100f89490080b40032158030a803018201c02102c1c24103090980050342c100d4a00510b5162426620250001640070482c4d8110141e0018103c0e03444e610701888600105002c000c0a0302d030141c9410001a04407000c0a00556080d07004004200100d0211b00c03d05016152078104140340c0400c0d01c542ca001000000c100e04507594001c00480c1480e4000d070041030160610034088581941c0311310301150402c0d0900070b40401403003005c0c0e6000586009120326805410042d1500e04001e9400d007212140c3d5000303e40e44503182d200403198001084a522511420071810005155101507480005010600034034a0704100e910400450102c442202510340282145c50000304241c3c0d03422103401d804504464860b50000e0078001049031046038441058241007003401c5c0c400c942d848100754040740742d034045002004501c0402042c025862090301030100200b581c600707549000e41d540c0100c0d041150134102 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 489394739 1250 489393489 489393491
    0x304060210060f0f051c0c09020c010510030b060d0c050415030308090111030f060315100527071119050a1e1502030c07050303040b2224020903060406 66
    0x8940c03a500194080c100003400802c54000f50702e802d040b00030728203240b2803045ea03218007458551104202216030301844107076008956020803580e6910540702a5202e1010103030707154a45000200214615074190342580e0304000030801d80d60360582030040700c840d080030a8415000b00180001d031980e65014002e17421342d69003d600942c038914a80640340000c054181d4446904019501890300780796810303260712414042d4a446240c0f1001c0109050100443d510701d41c20309541d00304030740c02c80301440c05000c586041e60180c0c0124405030b102c100180000c01d04131103a1403440d001c82d0440340b140c03000304d00344010301003550301c0c00f580340c2450410400c0482e400c4a003070b0400401c1c0014000078041c0031034184c03240712103002d060720981d4400c2080028103038141d414550200c0810750140305907081e0703031540354010101c80c0c0d81d0400c0d0510444541085480d107421440700c40682c4442c0c0183c00c1c01d480c03c642e00c102420600151641b50540d405c05070700c2c810940755070034050040c1c5954100800360140d03000d00c00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 489395989 1250 489394739 489394753
    0xf120619060b0315060703140d06081b0108060d050f0303090a1718090c1c0e070911070f08190e031b010e0409060f060b0a0315241103040602 62
    0x1840c036040d9841540480700c2c40c5002c2c0200466a0041c11908200010448455584644c1454142c4514000403802c941502010030064005442a40a041510040c81c01c0300c0c0b020220114444c6000e104100890010b106940826600c1c2098406e110f000d902c00c9040d03401a0786280410740c55508104c0d034034041980200c5108046c801503501d07110710258204040e0f803825803103280c0e1f00001c000200c1028003600d441030005000d44484000c0c1c0d0300300c1071008a60280030130724913490f0380503107000c418145013800381c4130380028100c1c41489811202c030b95103440c0505169050301c44824146142d00140c800c50010000190b51030103a800c1c180d89030005440f01c0f109406100b040c03601c3c1a089a824040300d40c00941410300681c1c00ca03120003030468080343d000c42c0c0c80c0c0b940c1c82d003480a80380c14035031201c8a900b080c40100e400501d40c4050300e100c0301241e404002c2c800f0000780d003001c1400d0038400c9216844110096038614a0813a02c06001c4140f141050042a04040922899507220707600100051304112 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 489397239 1250 489395989 489396031
    0x10e030c1b030c0d0b09011d07031106031b160605070f110a05061503010603020d06020a080a18080304020103020c0a03090612020301151107030b040b0a0501230f1206 73
    0x105220090300050b00244418080341001c110303108845500608410300840002c1c500d00425000f514104920102d150b803081e02d40d0441941d03844450004441c400080b8001b9021400d1000030b880c4144003221421200f13191008022040364041d00190102454100034000400d05500543c1e0081110740d031100419072205000a009c645a0404501c0580146003140040740d800240b094000d180c031319817103510042200000c0e0040c9410b900003504100c0741d0044000340020b69016041b498030366290300219548030a840c80484683c456070204000c000b0301c07440003007180c1794040d551251060500611300102c00d02c0091804526030000c034000381c600c0409000b110f44c040b040c5100c21070706178019802e550600d80400032984000042108001c009a6501d480314402c2001000464005a0400103402c6c40e0601e5880c020b01190440ca1541c1030200001d101c903269030450101c19030a5060040040610b01001400c0070040504c5a100e2946403c0401248003403001ca4040d100700302504109803c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 489398489 1250 489397239 489397273
    0x50705030726190302090307080f01060801060f080a06200d0b1525030c17030105030106050109140411090406060c1209050d080906070c0603020307020705031603020909010e030c 78
    0x141d007076030703010744020700c2a040c50040c0b110203001c200607141400340e11a0358800c003023032614083d58032909a0384612820f044154106500c070106a460800007030203841c0d2110070402c1501000e10464503154080d00328440824015030214100c81c12038500c111202c1030306483e51516030007003001e2246440da1345a6071559450f01819035800e001058402034207249144280c070000305070301e06000300381c81600c9503904205403041800c0c8114990142a070440c4500d12040c255683c0c00074042d6501a40c40c00f2400300345503000b6280c01c42145c0c240c0c00d00d0001e0310340b4042803101402030b200c2d064500d2141441419010fa40314083c91026100030350b107804050807903040900d1500c220b641c0c880c05201b120711701400a9211051031604464100a04d10799680303004010401600c24140301030b06a50b11498081502517054004601844980d805c071940b468540d401c1540303a8103030494119400e0341000c820401420702c0b2140b25031100b811000020120f104201075030455000428010725134000d07800c3c0c02403020138 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 489399739 1250 489398489 489398543
    0x70516110306220b0603030c01110d0b1504060f0e130c020c040626031903060608070207230f040204090204030b180a0b0405010219080105040f050f13030507050307 72
    0x880f072860a102c01c45120056951004030300c014194000b158002051601c00304211a1049101c0000304030100e8446a82400c580020700d03920f621034100301400c005864851640308150101d070070040d144c03c0c0f404009075040b1006000703404c280840961401e45640d03030604201c141e80454900422101d00c280f8009040c1500303a180c2c0352040d441c01100384407810f07503000840c3c00041400c076203184c0415002e18141c51402026500004920030b4100700b03110796410f4001c44120f510640710b071a13054132128400e80e09c1e02d6903402205071010303100008480054510500785020940a42400c01d00f500c48000f10301030764419000a52160b0300068204208041089a030ba845075801001004400c00110700035140d10568801504207084d200c04079040c010b080d8100c641d4550641103000d581c058a17200509000d10910501d88524030700401d00380700c854103024489c80b801c188a0140c805594814650f4046c6020040a42c204413040c40b042002510401c02051060300440000e01041a240140202021 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 489400989 1250 489399739 489399751
    0xa0203060301090f030f02071a040b0903160b0711120a0b07090503010603060b03120a020601030f02010e04020d0b03010c0c03023c0c031006050102060615130e060418020303030c03070516110306 85
    0x10010149e0750005415000780c4d02038032401a4100c1c0d0f10a07d480c0040d2414a1000048a4407940003a0000320035071a44010710900348541d150a00b0b2208200401010320844040300c0203a401040090000a400300c001c140e200c0618105600c03840d45841c0840d0844400741c00407502540d0710000030507240ba08101d400050200e08401524000d2081c00094441c041132000800e00020000f0441c11a809001c20f8441104050030464603058030401c0e400241141d40f500038000d52030300728110502485030b2021106590160002d0101081584203108040b185034048581045059240004a014200d20740c614800050007008800d580b0010107041c40c1e541c1c0d03500c10300d89280400c10042c60340c010403090340c0311100300c40410500c0042d41001c1b0a40c0b0800003140c1680d00780507400710b680702e1411030840c01a40103440401c0700490385221205a2060040041e5165209100003164610010300035540160989480c07070602d6034071124070b040101c0000c000c44043c1c45001c2c03030700c069050800040744d12031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 489402239 1250 489400989 489401009
    0x71403181c02070f080a12050a020102040312080f0c03090c010503061801081c09060f1b050115031502030606040e0705130308070506091605010e01021606091d06090a0203060301090f030f0207 84
    0x3140e80c1d51f6508801c801031861302403060110340d91583c40e00079070503200219041840601d860f0b0b19040b00900401c4211000310004010b940842c04114141043e03a1103030b207c010080003c4518840199038a800c000c29059202035408000b2520031040c060b0240201251001040703800e124803080841e1030640105803003004591841040171640c042c1c402854950607042c48104182d020180c1490014482e401810540c01c05207a00196540c408030342048a010f020700381d20031070500380d65600341c0c8402c0d2205680050244800c1c800c1300d80c0044656000125410958030305290460048042d49155005907580a808103101d024030009100d20365000c1003c2e00a444100b10a8040e841142898004c803030412000110001d1280d000300725445101902d485a070300303c1a5556002410404a40208401c58038031281005800000502d0a4000c0e20020010904d96a030303084030400a4000404da1a070641d2109103880114031040389080003603000c4e9503980490000a1800307807a0a9091340000c0e044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 489403489 1250 489402239 489402253
    0x3051c020c1216240c11040230010e0703020a21020424090e09030a0320070b07030b0a140d08091203040e071403181c02070f08 56
    0x455404944501c42140c00c41e164030300d80c1c4441c2d42d034a180040207803035466004224000030a4000b8041103802070b128019500d100b041d00c0c801d50032120403246000c01010305001c0081e5541c6440d041c0c000d4048031400c01e0b55608200ea0814403d2901c800003424414030401c1c45005100915642d04039580c02110fa0805514000c42d41d00000d00080d10290110b41c4011031207890310401e80103404480081c6000110540180d51404100c0101901c125140002c141c030120002110244c99040d24070a12080011350300700311070072034158054041d51080705d0683d905140006c1c04514203c0c09401d81501501802101d450840340140071035007800601d51191400c44070030010400c503016104803803032007550781d883e40aa052422a545000358003525903c4184200d0b030170409440007000c0c0c4100c0d20b108500210f02d03141c0d140c0585d40008400c50384482508100300007403a07000d000b070401ca8a0ba100340211981d02d104801d010a450804c1c0c0784480050700000410030507240d010341d62002800064000d8410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 489404739 1250 489403489 489403543
    0x103050303042414060306010609060801061107030c06050702210316020f09040f061505010503040f030908100212010803120f040606030b131b14280e010305 69
    0xa6404000c00040c03112843c1d4100c03080d03810900441c5040080024418020840308060615001c6011140d0a010784170740d2000190755403081c0f040800704c1d40103407117041040e42420000c0341c6804005a06110707074410082c002000440d1503da281c010010b0b036a645481d0320413071040141e1003a02c2c8003034800c0c00b801d24100c80c26003000801191828004000108504038217840455400a4000a02c9500c0303242c03441044140041003440041c1caa11849017040700011541b44090041224066140041d00074000900000c0e00d100e07501d803030f8070700900744085880c0c1e58102d02440c020303859104030b2080e50007240000b1308045000f08140540140c50166084c055040c0c1e5a10120074002c1000c800c5490b00004141070058941c4000042c6030026007412403850b0034005002d01003116641226080001c01d03030215007425658981c02660000d010590820410000300308480e1482a401c00e0040350b03400c0302c00c20b4181954a00c10080600c00c444940f55031440c1415401d100e90300380810340009120186000b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 489405989 1250 489404739 489404743
    0xc0a0b0408010c170712060f03050109051002130b09011116090b0303030c090607021302070825032102120103110a0503060709050907092304201911070605040602060609010305 77
    0x85c0c000032078602442c0d080c1b410302030103000c3c00c4207501c06580c0d5500700b030012007488010740101110500840c1203891584044000c0070880c8508418400c1c0c00480709014048081c02e030008111b4a041407400c000f84c6410a2005c0b802e25040711885500e20145503010005071040c0c5c02191800300c01100a1030071443c007105554000e106800d40c0c00c0c030400c0009a03500455880c5440c040d00c4920455085403642c000346088281984540c1d0309050007040702580c4800b600c40c0d03035213076080503074507585100b110420320414002076120901050403060f000e001e0340443c0084030b602c5a000714001c116140c1d80070200028090148000c0d000323036000e500036000300000ba0303420004103030880d9000d64014000359074038102195055040d40011003060311034040221030131050034018601302800c0701d040242580800103190241c0d4162210300d003c420901112618405a03800b035001d00700d0314149102c0c0018190030b01400c0c90069084080032807008282484078550401a0507070113203080c0e44840b21941551140381d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 489407239 1250 489405989 489405991
    0x607180f031703041e030f140c19141605100504050108150316180b04020406020c0402070614010807030507050a030839031206030a0b13050c0a0b0408010c17 69
    0x480400002001c00c0c2000f90500117151440d8240708a606407000c140740050084403000404000111559443d503070403c400d1040350640e26414000308016240ca10700030100e0b00c0004020365001240114034180705405120700c218000300c9011181100f8200410080400d00300c003603150070810244014041d6036041070219410030485440c11006d8809200040c3c60700405d100c90640c11038034210300140c41c0c0c0006028074001000b19005101409009051004030300a9119030710043c0d1000c60b0076000307828990300a2000130b00845011809203200e07044102c405c802a07011180ba548143d808006106c1c040c0202c802030941120b2000456181d034840b40720f40c0c0181ca56013004803005041c84d41c107072403208104102205c1850a0b88455038408080152a03400800c1c00c09401184400050814900415070044841c1d021035070541548030000086402c1c944c0b118100c5880c071a856000c81d450307864900350b000501ca100030f015611800c2a18042c25280144038510521040803aa8480c0c401010f0f522 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 489408489 1250 489407239 489407273
    0x1801060c030507050708150405010c0e01020601090b060d0c08100f030308161704060c02150c18011202030406150e060a060e1c060203091204030b0c07140607180f03 72
    0x440c0c485150b800d1007801c0a290f5481501148140c12500c40305060547c41e051265018200030419451803040175240071410b0032a490058000d60010b0110340100da202204480002e0030460400c0c140000078030859140c01305910114a90f2803c024403005000c480380040c046100d0300c07004180c519034001d840300d02c0142166800c8004001c0c0c104101c0d218407035501e1203150364245a5900e0401d81490390041c0062414400103004e80302905020507007107420700780521051001c0340d00d45041010740320b0000750803200e0b0304c3c10400510490344c40b42d41c950020714020b174010080002d07684000c010040600c400781e408040710b0410309040102a40d02c01c1949070881e07407142000c0d01c03c0d000400c009a05220484ca0401103040d4124044040c0000c1d82d010314861741c03074242103a114200321140d008190081d07201c014008480100011040c2c20940b0151050502c02d4064031f008400f4581c4540c28503004603400c40010b003403c00d5810400002c080a4001492109010509181992601000c1c000c1c00480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 489409739 1250 489408489 489408497
    0x12040302040c1205181c090902090103060b0a030f270b040519031101060e090d050a260403031406011d03030f040312020606041a1e03030c0c1801060c03 67
    0x10400c0042d00981e00080d00203102030f070800240c548880801d41c40c030301e107482c1c144091269008040b24280300228004242016443d50109140f034803001a001c1d41c08042e00301e04154503210f0000c6c43c6803904001d40161034264501041d1421040c0c0c010049802d4640510b80066a080ba20038640d51054980d80f606600603200c0303069940e0b05e042c007500d042c441c43e8000b0404504251a0820306a0100041c02c244403240d0007448495038402203560b103c07005560070344443e04000c94810615008600505110800d8100b0319502c0e00502080c010903402e03e10011201e01c024000c000405604d0b101d0140c0e84140d641203851384d8201040001d0501d544040c4c031041d09440342043c079076965004c0082d00e81901034664819559500d903d441c0d0745200c42141c20300f02510418011a545103003e000c3d080c1c4c03c2c240154095000c3c4601010001100b1411403504612600c1c0e01c0c0d102c42ba514203000500301d02d0140401012148840c90078000c400071a0007140d141c103001c000050044c0c9501c10b024000303454140c50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 489410989 1250 489409739 489409751
    0xa110c090f091f02091f05040e150303030c300c0d0207020d1406010608010b03070f0c020a0b04050112050903030402060a1205161e0f08090f0f0a0b091204030204 71
    0x881035283c03034100c000918440700016555050f00c1c070a0f070010b00b5001d070151806c034540d64017010000041035007076840c0c1003c45e0342808180040065002d44503070240030784402000d01d40441c40403904603402030b103030b00703100000000b500701003210110100f860041c0c001154030000c03d22030141640440e006008901043c100080c4104900642d0301941c0c074031030700100b030b81b6a508128605040b4045800020340340902504000107103043c020390465040700c0c55149030b1469551041002c944000200352590248003440d40e41c900981c0300c05004101400d03044540681e6130342040000b40000981c1c0f007007054201d007048100140710001001b504e42003a4140c440303e480302c0d80500c081e2030b0101d03808800c55001d80340608000c044a501001c0c083c41c038015071102102c10180000b221000e6040d5603a04012480d05030b046e2503200d10440440d0390001120050712a02d41e90015298100740e5404960000b03580007080b030340c0901080d0b8441680200740d41d401043c841f1001c4c24802c030107010300e200c0a03100355a1a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 489412239 1250 489410989 489411001
    0x60c1a160509010203070c0e040b0c071121060f040308060f031f3201060c0f020f030f01020706320708070e1c12030c140705010f0e030a110c090f 64
    0x42500c01247d40702103118520f40d00c400301d60080708001c440950328400c801010a914920040803142c0c920380082014030101480c5092001e21403d0038504801c074000100300261560f0103001190003001c2c05042c00d665070419080c020728020380502490303ca4a401500386035243e43c0003503c2084088429003000c4101c0f41c038074051001b44040000000e011041c4680080864a281c0302104a400e011109003c20790322500100d960b8560340e0002000350808840354005440c1201581030702c04030041c119035100030385245080c20382c2c02840701158810786807603075844029601d044e80c100d41045801d0980458540c4580d09900d424007416100501500b880800d211510500f1844149040a011805480b007641e0b445c60080d44ca50b035003030f2684010498a101d040c1d200e802559100502d40d034400584055050074402e0300c4d8006401140c856596085251045180d03000c0d0382d03408030a0f0004bc40c1c98400100002d800d102c414107040c4095045210390302016a158a880c0341c00040c02041c0d503a6981c1d0b41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 489413489 1250 489412239 489412243
    0x100e030702011409031e0f06040804050f03010603060f02040807080309010903080315030a2f100f020115170708010905070b090609030f06150d0b01060806061201060c1a1605090102 79
    0x58284a5010301590070003101442101c60b2100702d044024080707690b500e83d047c0095813a0207003902d004001c84010401002545003140000d00880303001000040d203969259121011a1005410041e21a801040821240000f402000010441b80300594036111a01380000c0450076103000041a4110204c040b40507050301c41d80b100341e0b0070409412592241c0745d40c00c091071041c0046040c13100601000b0a00d08407141000030f240d1900902500920b4031a002c09025600101550008400c540da0792100d02083e4202d0b8540100820149550f0128034081e020420f0806070aa0008409070b03040500f4440050400580c0307404440f04d80e21040e48401c14040014001d00c541d540707a581c140b051044a0a004a020508501546a809a00b116002100140480031510a0002e8800500c02c1d004100d014024004e0356400300c0028082c505d4040041c00002001200ba0407100010b4140006902005228042460310540131384040e2800d10380f11a00400003080048120300700080030840ca080c0c1d03402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 489414739 1250 489413489 489413497
    0x15120b1803040f0e01060302161e080f030f0705031306051503030a0e12010608100f090209070206041203090f111314150a05010c060b0d0b0108010e100e0307020114 72
    0x3840e81525500d5503501009000c501d010700074541c102c1104400080c83c98000d10803600b03c406120901f120103c415100d81c0707520703480c1028850052488080440008495100504c0c030b4960b030015091301c07070800544100031242e000308100c06000c010018418a4640074030303081c81c0e1590004005c126907494801600150b00305112003501407001160f00d4100c1e5810202d03c4400000940e0791760070a02c0300c0040300e800c2e00c840744070300307001c54000c112410800341c035541201d02034041454000c0703051401580071410102c800c540510058000d0400d00c0304005c005a054900168a0f140a0002021070340300c00c02d6100c4c1c0070000a01c03641143ca1198000c1d00c4031106151041c09011082102101c0f15214400300542101c000302c2c030403240181704000385045080700080d81d00c103079111008800c1c1940d4071002880c3c0030385400d911131109001d0500155030004a94041c2c00359000218400c5d1401076494545100100890205c3c0c2c1800c1085c402c100c000019141c0680c3c09103801d5115121040b080f094902c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 489415989 1250 489414739 489414781
    0xf03080d0b060d050a0e030f070308060a080d0801090f29030f1605010806040603050c15070b0a0b040e0a0209070e040906110903070e060604030f02180103060f15120b 73
    0xb5022440014070951540000d1041e40404402d001300303090030303003259140c0c0f04901d00b02e041c0e00c009000d8a00840e1091450700c4e480240074051a82c2c0585a19141c1d140c604116041d030002202c180041c005c0e0345040c02060b6407410351020a018559481c9010880440198002c03c4490900d1700c590000359020008640d20346000d00c01d84400b4290044060042a81da00035140410780072000309505090134440c1404990304100500040c004040030040410740d0f0002446980d031041c041c2c54080303405143c01d43d01852803e80b001407a07030442400d10044e240c8480d84444150800c10150000d40c50701141207a01c0783c4c5510380500b990000400150040102205c041d01152610440c098400c58a43c02440b400c0d608408036103841b03030b940703480b4049110100c46542d00044103010400c0064440003010540d82e00c014424800020350034161080c40b47d09034402d440141e1038800c0c081c0030f0541449021820501826034a00c081c2c01c0201c0b000341c180864600400c0c0e0508140010318403a0104241001c102d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 489417239 1250 489415989 489415999
    0x708090f0a0f1d06030c010f090e0703021207030212010e0a0f180209060613030f0c03150b13090c050f0d05060f070801060318060e0304090903110106080303010f03080d0b 75
    0x40d10303046000e00035086402410701055a42d010f95584550355041c01d44a00750003001400300381c18810044079542e0b40c06441c0c0003400f40550340880c240b0342208240f07224a5865900584079003c280318040e0800c170190000043c144104801010f0310400032070f20307040d42c140c107001010030340361a121070005000d42695000d00c245007132000010040840d03071040c2c540c0c4c000c0341c0c240b195031070346d904000d020302c1564007207401516803c5003040005c8820301503045450040f43e494000f20303501c0d00c2d000817003120f030340544446c282c0c0c9020400045c41c25621310b044803991000704200c170b10000d58400203030000902515102d03000d00e80382221240d1f41c2c0d5040c4400c840d40281940c0031401c000341415451a0240c80101c086172000f400496024440d228641213000c3c0390380b807000d508036640c44540007402c3c00d14150080340410032012a18082078054185c0c401d10980e68140c080c000c0300a090300310351454001c0e060030b8008000402003008409490001e5a8105014581c2c4009080d03407000103109042000e5042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 489418489 1250 489417239 489417259
    0x10140f07030c051219030b030a0b01080d09080d0e060d06030204060b0703090e0705030f060109050a270e03300f011707060f0e27160207030302030708090f 68
    0x56000c161480361622079811201c9001c02c404d0920752074010a1004009548a81d04e08059240b180c0c0080245240c0a001e41d41c1c1c4040680f94040d5400c401d8001d0740742603000800684160b07038000407050040c01298094a00342e101484c0c010442c1242294062103640003054410800728540e11090003580e00500800445548000c5242150450142a000f00320700450002d140e4504065280c8182c041d40d42ea185160b0b92280c100d1802d0401502c254104000701c0c4000c01c3c291100c404410240c044540f90601d05802c21414998091440c107007001498101440182c042800005072403000c00d11604030301410941c40581001010716003c9182e200c0e90131014410030140d01c8408d54166030060302866114280801001e60764800d601c514400205007407400002584244007011030420020711081c0070301d14503022890030207403e82441081220700c0061109082070901940d4220354a8000340c90000e10b90746001c0e4603030141d5040505810400200c160050741c502c01c3c1480103540050030b00e242 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 489419739 1250 489418489 489418493
    0x109270504060c021219140904061419030b2e0b0304060f14040803060f030709020a0807020d21061e15031e2f070b01050a0510140f07 59
    0x3034109400c3c00700150040c404404c0803821614215607402c1d1505903000c00c0546060300480300140c00c0920384000a006000d50b0401356514004c403001044074202818040e0714603000c010700d01c40110b05185041001940c1000054400540d0365486a0310320034204074994040202c1242600c000c05401108502500200d21910b80c3c60146004034040c02c0304010400c1ca0b040b000007104c81c8500142c010f0303330001340000e0004103041c0c01140c0c4143e0141c03501c10540e18240129207003440355009251115008504120f03d08d50051400358400130031f100500012400c004c0141112001070080420700a40328191404070200d6001400209981c022180782612403120501541281e0b003e00101d1420021070303504040d211340105100240301413110250b18042a0900700140800d1000c500072805851108150510320917004414030400300d1055030750412490003203c0c482c0140c03c0a407044901c000184416201c00c101182d000150341002c51524280c1306100f0340314001d07100c44d01c0b1807060001c0c4200c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 489420989 1250 489419739 489419741
    0x10e0a0b16080108100c180f031707031707020a1202030d0f05091e0106030f0c0905010602060c160512030a0e06090109030509012111040302120c010927050406 70
    0x200c25a8511154505007050400c00c440031202841183c146601a405030854000280c0c40001d50185500b001340728000f8a9140248070489135020000c1c2844908041042c8025102c0e0300c2800c4083e079420501d054419600607100c070040b10800c1000c0c3c2e040c030000603000d82c001c0064031712041c0c01142c143e461801c010b03c000c2d901d600c0102e200c0075041c148640310b40301c3d030b83d40e0040d140146500c0016019503240150110745000c940640c0001b259200c400001c0400c2e40c04000082c6980591891071f031003070910021506031a01a8881c408640c4040d04200b50344c21410155000d900074003040c60703445459414510f241c4403c2241061043c1000030a0241300da402ea80850003884684064481c1a42da000030942212600c600281c041407082004400940c41281c0ca101000f69403181d0607142d5403401c3d241002c40b080c2c0c864941110324005820300940ca030203c0c4020f42c24000d44000d0858070002c10009007510864407507080c01c40d030441106200b44442110894501034282001c110915050030000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 489422239 1250 489420989 489420991
    0x90f0501031a071e031d06011a0a09030305070807050d02010209030f060606040308130f12021203070f02090c0c03030903280203031611010c080702010b04020c0c040b03010e0a0b 78
    0x3200000c0708610b0080280510855900c9072220b91128403200005101201c021044185840105562521454083c61190070f04450940d8110700411240d070403c0340d40c2c981607403828400641800c3c18891590f12640c4100303010b0950790b148c0b81060300d8611915080c1014000e0f0304c8000c5c0180900300381400319903030560203880803d008070210307524002c64072000da0f15000c00380c5d402e03504007a0801c02400401d96000040c440c03240030b0071800c40850381d54000c9898071140c54100f89140700800c0142810740c0b4000c1c03019921020150055031030610a0f655504040ca001d0074000d000d42c04100004450780b0145040e2030f41020314205482e07492900340016516980802134080e0301c20b8414041d04400491000860074506440d0019491504c9000c0c0a8410b4a030101085081041c540441d084000e028062101c11100d40e880360001424003c502034292000c8141c040e00681c4103115280224000040712490210b06490000c0c94503031101c0400d0140c001c130b070030b00211442401d00100c00c100c0c00c040d10b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 489423489 1250 489422239 489422243
    0x90f06050415060503030f0903190b0901060b03010e04031d102003070f0305090f1513090c021e0321071101050709410316030c0e0a06090f050103 64
    0x410460b4105240000c440d40c5000e0150554070901410b040861440001c2c40082401411907104071850407198541154402c1c00701c036111000c4091019501e4240a0340018060520b03c0d81c3c20342d8140000b4080012000704007a00704605a0700c000c0388003004144100032840d010300a4580f543c184180135000b03a6000c2a82810071902949a2038020300c01300955000d554001204035103510f5a480482d60343d04030702c0200e9409020810580000c2c1e95081d80a092145880001c94444402c40e1420000b000140d020030001820210590007059011501101c504440c101c0e090846031038a0308180b40d170040623160440316a804110700896140c01c000140304080c03d0340e9505a20720003443c69070030307a401900d420000c284001400d1220071940100249a50840a28072440019000c8070380c50b04880452841d8000c1d07d100d0681c8118141445542e0081d03806610911000f8503554a04008a807548504603071034000308042400d56446070001c800500020b0414440c1c4014014900002c050078401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 489424739 1250 489423489 489423503
    0x180b0d2603070f201c090905090c060304110301020d0b01030b0108010806060d030e030d09030c0618090504031707092c040809011206030302030a0f1106011809080c070501110a11010c06090f060504 86
    0x400121f0071414082e00b0f124440060280c018100403401b8450b45410243c0215071505068900b800d240d1402d10140128043e40000852100100c500140407030301c6600a2070304011000f001805182d0001624640180040d40e224400c40c0340b60508440840030b9613445075142c005d000c80c01d5151a031084032130703054030b020301d40025441e03a44010645d100e903000b254010103510501800c0044030481d5118070791190007402e101c000d0b040f4402c034000d1840700803943c2002190100c5014000c0000101001c000e58401c1c060220810080e1014856a0240200000d19840c0300290781040c07a44143c10030103100b4040382040c8051a2a89006500c0e5000703100700500040a0704031540240380710301e24007000300503c4409404a6401e00000314088241440d280d03a4640c2c84201c10000200114001c041202d6100040c202e142e040c000010040445a01c9000980e0b0140c1c00c07150116040c11f10640300d0000074200100300c4661031070400c01604038410041e00c020b07507900d4bc080620415401584c070440c0f141d03034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 489425989 1250 489424739 489424757
    0x12020d060e0105271b0418150807050f0f04061206051902041d270105011d0403080106110a0b0403080a1113180b0d2603070f201c 57
    0x1001c0050000080f800104c10450b140100d4600c00c1009020300b210b07800700d00140d180640702c65203c001021440d407540c0285944210118030550704001c0f80340940750300b40c0a8660149000001060107042c0b00c042449001040080100c65940340c0c8454020652003c003110030312241d0a0007401000111342e51400b508030000e900d206000c0303503c02c44054511a00c5100c0710a0340656503c80c1c80c8200074040354184080c804001654440c2079440c003500c0d00c028001068071b6051414460818407008280c000e410401028000041e40103825281520703601d161001c2c20002048110380b034407002074800382140c4078510a0005166001403002d100381c44c540710070b01004241d90603000542c45690b0701c107086020b1007001030020a99980051240080140c00803032403800850004503005070155041300e07a20104044118002c1a03144204000780c4600041e0342503182c000800f50410b8041054401044078085080100c12100e004603084112640c084500e000c60100603a940d02c0d0264940501180c1251 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 489427239 1250 489425989 489426019
    0x1030f03030b040b131d03030a060f090501210501020405090705040302100903050d0f140c060106090e010f0308030a0207120906110f0d0302090d0623090a0506060112020d060e0105 79
    0x10040c084540805040c0c040170002a51004008041c0a50700e45003403d58007819a01c1580e080000c2c5006031048000000c070700d40f0340504d01c1e401007017640c04901741c1402d00c0010001c00440300410403009051620403000b401151400724024400c40d001a6800a035071402d00c504107900030003502c00d80b482a40d0600010304290000e40d141c1e5414440140103038000c00803c40c10354070030b5000858800d010f0400012150400054107101d4001c2c1090300c000b6803103400104900ca40c08100742e0700910740e008101cce41550606c070341c100b280d98580c000500528000004148000308aa0441c5c44883e0040724111550071074550003004082c80340320300c0000602450040e82e8407400480c044d000705820340c000348181022007506070082d41020b8580c070343c4110b1400c45000815840e003c1c05c3c0040c80b0000604540c2d41400b200541d5040002d003200c1c0559208007010400540001201608010f090900300e07126070080510402903c250308210b00a1400d04400103903042c000340d10207041c0c0758202c506c1c880c100b20358 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 489428489 1250 489427239 489427241
    0xd0506150702030618011416080c0f070303020307120203042003010c09120503190203370e061608030a1406101101020d0501180c0f05040e090a0b01030f03030b04 71
    0x3050301a515030002c80116031014204440b45e070140804400100b4190010840342400d40c0c42259410b02c18800e004100342d44a5011580350303802007013404640d06081d09001003400500400c41e0040034585d0000c00f0440c071364001e103c1d0289041c148c400940d601e292926010404c0c1c42802110b00ba01045c010b0311012500d0180100759510304e9a5450a508500d418000d0155a64004083e90180010402801c80c44000107000440742c0d082d0700103654502d20044010045401810448000b984072011034030518815004001ca4121034500101c3c0350008500190079441031240503031002c0d4140050f0000c200b40040514454080600100f019440e031030000c201c41c1c14211000d950214402c10f501401074010f21007058034044640c001401d003d0001c040d01d04580d401e030808442c801160600d04580e020328050107502d00f0052170200490301c00e10601400900403070199604d4001c0b404005251010100310071800d9507003116480b00c4c1c65175030341007408443c00403681c240c00003800c1c1618000ba034141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 489429739 1250 489428489 489428497
    0x203280204051918050609030f181504060c05150603060112030c050d080412090609050f031c08061906090314150f060102160503061303140d050615 65
    0x5458080542540603801c00008180042c14004400302c0b003040540072064510840240342a100d42807400f0748a41c1c20920f1600c03400500c0c00d81c595008000c840811081c03a070680304619040b80d0342a66000c41080010250310000e591a40d81c490b0115000880d80d50244208905901800c15101c140111001481050104031041e982540c0194010403102400788000062a400313480e129810000641d1002d003045140a8a5000102c08034180020301401581001104003541403074040c6915005000d000401c1c24459a44100d0948010640f20f071018002050070f800c407502070b525240098078028001d02001d54009010b12a00c2000100806008003800f080d5500358a4000d13015245640710700f442c1042002083c202d00441000030400e0010304443d6010b841c0e02c01c0340c0011803600e9800240780048414202540c1c54032650100900c1d100480c103250000c602182c09181882c4c2410241e40300c01228254212882c000104245660029404075020740001c1700c5034190001280c81091382030103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 489430989 1250 489429739 489429793
    0x90525050103022505030f0309010b1804020a060f050d0615030b0d030c0b2502011a010903021f170a050106120902090f0411040204090b09070306080a080c1e03070203 73
    0x5030422414150b928134009850024880c20449103400b00d104154001504140c811f91041d81d1031380d00c0701d00c0b1481c0410314050414240d07106010645811780006401e030905211381818403503021030f804580b5208908032400140d0b4100184101c0781d4590900043c901003829030701c002807919456400c6460469808001d19815540300321000f02c090721400d00e242c0016203241d043c0b241001d00340030000c0d0400941d007200c8010350000900b0410a0341820352400b0034404060400c01c5141046c40103a1300e82074422282980e4039140444800442c5040e2101c1c4035a0b194580700c00780d940d04101c51007450707401450603216966542d81d8040c40301d40101d0152658001c00a600c29244000038141da00d400f140b031a4441c1c0506c3c00340d0740c0492540c1c0494200e901c9a00141b405544405d044451810415030241d041040b510b0200641454030b01c25640300c5d11920001050305c0e200041800c04018200306d19501320b00d000040808100415100340c2d944e81c40400304a009010703a1b02200c041c40d00070508200750740 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 489432239 1250 489430989 489431017
    0x40501081b0706090302300f1b0105040506160201021801050901030f0e0307170306060f0c07091107030f02070501050405010f0c06050a0b180118020d09052505010302 73
    0x501c4224001c1000c00301c001d141c1c20301c0e400900c10b41020502c2c0c0d008100f10395000750098868408900704180250407580403100c00114102d2880070314000143c1192250031401e1545511040c4400501d0805206000b02515643c00d01c000d20090100204036140180c80007a0401107070320110328180d00740c1c002c2414068030258070744040350255000340020400c03240c05240c001504001c1c0012a4104c40c0d0980901c02181d00104c0c40f40c0030000c01d805003102281c40c3c044c0e01d608620f80b020016460b4450007540200c080d00200d51500c1c4040104580c401400c0f110100344410400d4501644441c4c020100550001d4811341c46408261300100e0f0400507220107940b600c0c5050309000064030f07000303201845442000881c45004003c02c1c0c152251a001c0c01c5201c0f00881c4417038030103081040449000c0615220b070032020b4010040c0d01a03101e001c55402c40580e6015845120b48038035800141510b1802510f540070742c0c208070180c141ea00c42c40c04c011040d040c0c4842d09590311040110120701070768002000305 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 489433489 1250 489432239 489432241
    0x7080d020111041215111b1203040609020d0605011410050c06160c060e030301080d140913020409020c100f060311120c03070b0a0906050921011803110705030304050108 74
    0x3d2200d0480c1052180114426942002c17000c6517402204c4000c00c504031114404591418036154200f80396400e1000c0000070040782c484540c3c803e200d8800948000c00040d0345282000864484d096041c1d0402d41110081040d980e58450441c5101e183d201c07400c3c410b0050248699489000e40140c2d00329028800c010302c2031b5560b90f603080500300e8154100206000c4911002e20004055000d11035051100c103010b1074595140840c02c030716110b0541004402c2c00f0340d10411400b001c0c10341c401c4c4e4a10b0728085a44402160b0b900810000a03c91508400000c034000a081c0b401e0140016034907100000d1550100508506139540c2d0040342c225000c0148205e070902045800380c035110f480c8454504106045c0c500c5003c541000a1130442e11303a0201c45e1000340820208034031a00044180300914407030501c9850801c00000140b41c5101c00c4000904003c0010a5025550006d501c040c02100340480d151892040b00e05014024459943e00c1040d42e220b120350104e0142404000d07941201d4040e1030302d4000e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 489434739 1250 489433489 489433499
    0x10206061512041e06140601030501081f1407230c0a031202090a06080106080709180905210d060807060c02060a111002040e060a180e0109020406030507080d02011104 73
    0x120b12000340061302c40c0f001080b04850580302070b40c89907002d5031180800084180800200c55581440100014141031030a0300401c400761001c1100700a805141d01c180c2c0455850b00d030807000900e460610180c1b00d0942008000000e508017901c0001ca10440c40400f0480036001c0c1c40488601ca219108401e94220840340c0740001e01600902554080281001d410028890041000c0c28030ba58040300024501a004200b81c58204410a81142940c945007154a0414620441e10f009031401441020b17503d403201003c0c040203000c283c0300b20702443c00800b55016400741c00c030300c603400000c038200388145000400100c0c0040011003504640b0151905214481c1a80030403200f074009405040034890207603003000c100e210600400758860340d00c60700107860303e003040d18481107440d00030080c40c05500d4003031050184c0307007a803c410ba0f0043c1d030f10000030914042e4400d44501502911a00a40160a1040100810902041490949003940704a600c0311150540807800e07600005000050141c0c100010300c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 489435989 1250 489434739 489434767
    0x507092c07080d1d03030c0d121808071406070807090f03021005130f08060f01061d060d0605090a020d0506060a05030411010e21071205030d0b040e030c07050102060615 74
    0x2500300c580d014040e103101d513030b240400c2c1940d01c6040005a6034000c2000c00c00c9445d0400c50040010220a10407c52030301081050303c8031002014010f40500004140002005440141007034480d0b01003040d01d01904082c080038044d42401d4584101147c51200c001c5a0300c0c2001e11602c00309c81d002001c82d001e900c1c907107900703556035405a010540d000080301c0010402d10300d41d02c4000c00404001009082500d00100e80010000301a0020401c010754188030380130120368844035100028007250008d0381c0740c180040b0100200f070300307074441d6400051541c00c0284200d0240e01030480e01503017100a00030350b42c2e0b40c02000f00507c107034103440d1701299060000c03401158001000b00c240c0441070414503510040240051401e400100041105c4440c03480c0c5d8286006041c000c10b80180360001410342003400030303506c0c0c43d22070258005125500755220034000d4145c0d50743d0801c10040d0300f92070940e90340d840c102d0b10940c0c40d0f00d498090340c0d0162064501040c000c0c20303c03110420180044065550800e001803e03010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 489437239 1250 489435989 489436007
    0xa0206220305041a04150216050618010e030f0f070e10080703060e1009140c03011806390206010e010f050f040603020415090b0d020904030c0507092c07080d 69
    0x10390810b4180808908544101c03210511b00c08143c0003828800f00504164a600c950f07504658003650060100c00300e2034455082c8860090024208140b04c04800800f003482e260000b8450001481880c680d8030300785502140c400c05440440e07004859980d15a2001c00440c0d48610907034110741d001072070400100e1040d900070003428030a0402c0d5a03001d0718114803130f0203403012001c0640d005a144454858500010402c0401c1c3c20010303002440901780800b4004020b020444001c0e060071303212844202100071205030000f2010720321110305103031341c590408818500f00d05000400503114100000c02c01c601504000e904a0b081032050708000e90034081846007410141e9042170704036848000100041e5140d0041d401c0d1010b1050040e0344161901e525802540e040295080c024040320b1440c50260b1a170100740360b8056050305050828100501d4072514050300707a448040500e250064020145074008825070b0003081c01301540c921032051b840580d480d920588a0000039522113820340f9080f40c0585109 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 489438489 1250 489437239 489437279
    0xf14040f05010905030d0501080c030106051c02060d020a030e0d0305130314090d11100813020d0311060c07020901150c1704051c060507051201140d0203030a020622030504 75
    0xca40f615072070792481c0c0ba40d00051400001c081c3c48070014002d1100c2003002c100015812402841080d1900c80400c030401c0503c0d02101d250315072514054195154141240d2101c0c40a1204640e50161994010700501e001d6018840c01e0280d0031060507132510901a060160314141901400e01840e40d4055500e10740410b84194401d0050240500316a00c220b030100ea02030240030b0100d08403210800b080929100700e40300348140101a0103100e0042e40b02410200b0540d03055401321401c210500b030940d082c0060945030402c92103141c0c00c00840000c1c0070007400d07000e803003070fa101d11060740c0740c106640f14043d00600d540c000400348103045002c240403207680c0f041540c0904100e450f244d203c0c404030745c142e41d49a40d080d6040034500d40319000c00c000c500c5500e5001d00640b030000e040c22181740600d40e07486410300c2492a04a07401c101040b0380c2d0760b0281d071b41450a03030042c02c40342c2c0c8000126000e510f56004648109420303210701c085803a0380c7e016505200307a0690541c2c81510307090500d5009103220305040c0c12 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 489439739 1250 489438489 489438491
    0x60a0203040f020d030906090b040b09120c0310020c010f0e060a0b0a0807030305030907060e10030903090e091605040506030c19050a1d070c020a2607180f14040f0501 73
    0x1600c0b0240e100c02d126500c07068041e5941c41225401c0400c0a403440101d0307032000751760076420002000020480808e551031124121001490040c90004048c0f030000d54601d51079040c050704039829060a490b80c0142011781c0f00200a00500a000031342800711942d860082403c0d801c01d0340042d01400f6268442e0000c60380092080341d94903141c00c0001d10b44400b580040700890400418050102c0b401c11403030000744202d1601c005512100300109a925103c944410141a1900868010107002c1c0c2c407010007420307000013802460303d0044022070340e030b00b1841d00c0000751001e42c89010850f0309090050500c20f02c000780041c00101d94840500124031b64109420700410004030010406a41d132413032800040554072a108070b02203481c0200301c0c40d050003070003c109101a03a258040140c58081c0a6400c07504071610741580e43c1c1c0f9085064444080c0c3d0201d00e03c0b06c0c002e010340801c40320b031101030141954207519000c100b034080100c0c00908540d50b16100100e4ed5100c180001d00245040d000300c41040d100d400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 489440989 1250 489439739 489439763
    0x7060e13021e0f0c0c0406050f1009120c0303030b0102060f13030203041703030105011d0d080309010b04060303050a0e060f0d02090303070b01080106050909012c0304050310020d05010e0405060a020304 88
    0x100d680029007003414420400180040e5949003031104106503011410101c404211f018905000142001d41d8512018000c200103080c03c42000c3c010210440101041070480600e01058076050400750700f20300080340880e14090390041ca40d44001851803140c4500740c204004c0b921040742c0210a562040c0f4100c0440c8010400441c082c40b40b0343d1036544409141c00110f840394184400900503682500c440b0b440702d082504a0b4541d5a1a81d18501300141c2001c2544d5403911800d0441740034144103032000780c00a0400c2400420198420010001480140da598100599110402c1954800c02d010090400707000d00c05040150150746c02044001802030403286008182d56401c001c52707409900000059648601c00c2140741401a0100e40c00303120007000700291807042c0040c2c00800c01258070750340c03a800ea0010403148900c0800c102c0b40980320060849010403a400c020901a40c003c02e2501c1d401401d00d40005070700c031404600140035a90200150419544200c52a40250030040058443c00300443c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 489442239 1250 489440989 489441037
    0x108150d170c01020f04090c0212090910120318050d0c0b0c0a021c02040614011d03030405120601090b12030f0f0706020f07120f0c030c0507081e07060e1302 69
    0x413008081c2c0d0005560800d4846140c8043c60781180c0101e00c2c01c00654101054407840d04c050901155a1803130f00b00c408190035245d410002070031140c540c004c042c400003c0100c0c0c80c107141d04488011460764003c041d8080d069240c80c01c1c04020741c11124001c0c12449a0710090205034004409409900805012111950903540010b48584400c10f02c2500b000041b03070381d20040d404c0501034880501302c4074003801c10008442000910112140f50804c40d51780715400c401038203603420300449000780310050081640e105035030341550b00c58000303114042c00d20f40307400d001d080d203800c20b1a031895100d0400b0000e903081038110031100c401c41e80609100c130310030074003000880d002070400d20103094480c02d420700c42622034015103002035241c054640c01e8403d018419044802c240d52121000075060342c107240c01000100149401d07480c05125810051070340c0204140d480e641184c0407041160b83d440c0c90200c8102c507a6490341901d40001209105410002071070007403aa08207140c0080490032084130141501141d64 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 489443489 1250 489442239 489442241
    0x61e0301120605060f01091e080d180e010b0a050309010902030706031b140f16080307022808041a0702040c050306010e060301150309031704050601050108150d170c01 73
    0x9800050100c40803030180c03402e021162141d80c1e4801e100342d4000707244188039000038013a1615071086c040c40d811030071740e060351444191086900600919048419008a001c40a0b010007c0c011030341a4241160f800000d0710f00000c02042c0c1200c43c0c090f069498283e484400b2605544002c0084041b99254900e010040e20100b01c01c1c001024165070008020303010b04050080e0101d0303500d480c81040341c50080360034403006200032210b0902c0a040d07000da9803139203943d100c14241c0d44618082c084080100411510940214281da200b40310b052400320300c1d103007040c04443c100080f55000750101105000a01803909006104e13020b14094450300380c00c2500660026058030001d4030a000012004800d101c001e50304000101c07158101126142e0556041166601c0a0300d44d009802c0100354031101c81000381030051a80e40c2c0100788001b000300507494103090140d40c400c000c4c0301e01d60004140b80002050b50310b4858161545110060000d403c282c1a0780340d01e042d003045c000680c4000c0004110700011b048003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 489444739 1250 489443489 489443491
    0x601110601080a063219061401030605030303130605040305091003060e010b040b030c09010c05060c0a08180a030e03010f06080a020f010302070b0415020f2a011a061e03 74
    0x3aa00a01c0b200c1d00f54600f180c00e4038009103001d071103a4408000c44140c0045100150b45100e8030300c0c09031001c0e070707694402c28a542001c09118006649018000b140c44c0e00d4840c225042460280c80c00c0c42032076581c0007411f990340b104403170f00c050788070b03807124543e002500d1504150f402134060714085041c03111240000780c02041e074807032580200b5070b10f003002c000710180d001a1900510344030007214140362900130081c2c124403000f021a00d6a080019142c0040ea02400d5005a0560040110b81c01c903d006040011070b9444040310308040380d0f40c0400107e0000310320b5024811440004090000500aa90165a105207061042d03030316540380c41c040621000320b0711500c0010a00703c030041402d1130060051102c24000d10310030b94101030040050070045040402c800c2e81161b40b00d101c0790b11411640891400038002c101c0307034003034413800011700d51041c0200c417085404401001d08891030312455a4030b000d00700d07045214450090000d5450390442454448080c00c081c80560346a42c4402d5a10b415081071a80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 489445989 1250 489444739 489444749
    0x612070c021c020118080318040609110c0c040605060405040e0a0212280503040614040e010f0303080609010e010605070f0218070207060e0105070f0201030e010903080a1a15030601110601 82
    0x9881c8210b0103540c3d1080f4803c05800803ca450f030348607801d0007425a200d00c41c6015a08010513640c446132069166580305078010328449030708003d00404c055860b4819440181a40301c80d200d034a5002c82c1900e418801c4104943e40246620f00d82403070a8244005031101e054240c01c40e001c0c0490803000350702da06907124a902144000350050b0b0004045c000d85101d10360075000d13a4215000710101c0003550001c21917050b00d00b68105442d2000403110201d40c2c5104030340081031100c9004000141500344006041c06803071103502da540c00d80c1d946c031040c0000c01c6070920502c004540070200402065000c2c000404c0c045005010303451948903950042440034210b600320f844041c0300f84040101340c550610442c4041c000340d14100041661110000f01140111003018041100c000a0b01c41103a01990060600c080d82600903c041c041c03034200a00600c100700ca64018a81c2450003554020541074400100603500410034010415004094003490700018000c5050201c0104c2e10f00f07070a1010040103000300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 489447239 1250 489445989 489446029
    0x101107060504050c24040e0c0c0709050609011403120906070203030301030809030d0f1e0c0b250212030a15030c03060209011715040507050d02041202030105150612070c02 75
    0x100803001170005403044040300f201942414018426a0544141201c0441e41e0b28440114980c0301d0b010561910700c2941320501807480b81400006140b40c80c4e0304154030540c8100d6402072030342c0c1da03035000e004410a0034000035410381106042514200622011b007400510242c00c0713038102003055021034590750007a04255483c14000c2a0700744546410020907508400c0c915140700c05111707650000e000800c0c0413aa010b48102c3c09082810014071a0140f26440341e0040301c40320560030702011042d940802c00388211900f01e07125214141007400010341c459810b10f5000b0051441c0e4401001d10001c041e420307a4204032220940c4000007041038441a076010b50300803000160b480c1181340024000503240300310300c19861840c80c10041c00300301110000c46410010390700410560b8031400101e40600c10b00e400b11403820720206010074403480c10101561060301c285c00030401900c4004c0c003500384e0155070900c02e500ca0030400c80c8503889290301c014540c0000550800d04602600341d8001070241c0120344040c0004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 489448489 1250 489447239 489447253
    0x12020f0301182309100606030b010e3003070503070b150409030c231605010305010b030f012c010b0d050708010503030904090507030b100f0f050310110706050405 71
    0x300c440a070500c41d220550b60b401c02c0100e00308400007411042c0340700c680e0042040e14000a466040030f20818140c0f210107141009200d889130390160080c0103164015000070751a184001c5181010300342d86288401c1d103005255028207184940c0c10500c20761011000d42d020a01c980070010308104060b0940c036104030748100d443c1c908824400b0205041d0f1030150310640c1845e5020000c40d41005c02d40072595001502d00c20003220f00c601d001c041207100e200603641c83c422081d01680d41180000c1c1001030b03c000f40d80901031a6610141c11203036010949241c0c054012000041001907081c82c54940c40013104c066070090600c4180c40c43c09800c009234420000e10800141c8103510428902c03c83c1c2d800751203070810362529411f20021a5480c0074030ba030524041d580c0d4203d400c4c00e000e070401c1940019940400c00410602e89580c894a01e01640c2c4951109040090300c00b04400501390100415500d01500505140c3c04140c1c0c03800c060840c0903550528440104407203404a2440c0c0109032069001c2c0d4010288 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 489449739 1250 489448489 489448499
    0x3130f020d2406060f0305070e030604051b030c03060601110a0501050c03012c01090f06260c01020f0a02061b030714160e0c0d18050c0f060a08041212020f0301 70
    0x20058114829064041c0b5145041c04900c1c5c00061042c541606440c0000d8159a80002941c1c008020381d40c05034117218000410040000024416021a403a2070480c0381003420700062643c1c600a40c0120fa906401400001d40694480e07551240002840b00c1158000c203419101c0e03c0c2111001e4030300103100703080040140a00340354160080300e42c041c0f00340f01d44c5c418401c0c0000d000c5c8610040c0074080808ad280d02299081c006180c000f00c001d0b00058203080c06000c0ca00c4039403180d584020480c58454010300f5081f04940d80045940c1a501c0c5c0e040e8041c01d000951035007001940c0d8803060900d00d01c0c100701c4040c0805c2c2340081010781406171060140145440f00c0c0c4004600d00303041c801342000140c0244030300f80300c1c0343c0c206c2c006070b0b8005002e40105501c4164081001028000d003003c0044405d82e0703540c114040c4000020048545031b000e4508040d010402ca01b030000a1042e842990302103003640d030110b800200c00420074410380e41249003009000e00e00300c50040c1664040c40110080c0f8a01200602ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 489450989 1250 489449739 489449783
    0x315111207091e0803030f0c0d0e16050f012001021303050a0b0a0605064e0a020301030b0705030601090302061b07080118020603070e06030f090d0f0503130f020d 71
    0x100c40d480c510402d0a1319000d00700d966171000410390081c405996000c81c28940d01801694040265008148407a41c4002241e5585007003c00a0080305945203000140c982404a0158200c04040c0d41d441070000901c2c484011103244800f4122441d0f60820a0540b80d003104112030010354440e0015205882590078121483c030400b400020000b032403c24100f0403a5210303400c94000d801e094044032001c1581d1300d4038040c0542203440c0e480051101d03e401c1444410134200e10009452001c080700c40729104c2c240d01d1000c9000900000307011a09590109507407078003500c061907110a052410880366501c03a40031070310f45e412a03441e103e44070301c002c00c13482980f12081c4803200280400720001c1140c50712510184108400c100c8020380501d0000020855503440340d10240a40031001d00115964188260b42c2d503504c0102326803420460082a0701e4100a07403281b02000400b81035690b40d181140c503034214802c0109201041100d031242140810b07030041e10303900c2c0781c5c82c019401000003180071080550301d40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 489452239 1250 489450989 489451019
    0x4060c030b010e100c0c08070902071e030e010509040e07030602090406080a1e080d05090307020109080a0f12020316150606020f15060a080a0506150109031511120709 73
    0x381070040035442c0b607406881e00d540d415140146172410f038030780900300e0400741c0070383c0d0094010b4009070103441d6010540700700540050003036030300c582204455486c44040300b00e04c1ea052084024000382c4aa0080402984210054501110010f000050340b9401441251034101c43d40e104071041c1d50085009102890140314610007440201d002d04081c804960702c03501401c0e04d10052080a680c0c58480c442409035003419030f089800c100b041000281080003516903290480b141c1207000403000c19022480d0071003c241858440d03480208500d80c162543e5070140d00240042c2958210311003403041550024480c1c4810b2485030142001000e668841c10b900e200355900c0350000815540421400c0c1000ca03000181048800060140b8140e5511040c00040f07141350303260301003c003034800c008a2401340140030603114000c2554060f030340c0c4052940b10043d0b0324070a140c4806070242d080200b10044003901d641040c816038594a080f540f910785075100d41040e1003815910940000d240890078041651064141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 489453489 1250 489452239 489452261
    0x301021611030a0201050d051e01080a0c1410110c15130b09090c0a26070306060305130605131b0e061806100c051c120b0307061b050604060c03 63
    0xf038200144160006045031080729400b0159564680014542000d0b05c3c0c02100d1184000c40803044950b514500c556840441040c2074911950b100c2e00001d80303552965141c02d8080003c3c068112404405800703551500c1d0030000c0701100d020f6802425142d960b1508400d280000e0b10f62002e032600b106c450182102e0080750820b10b89014104190021659460012a405030300e01210517902c109510b0b00b1514044c905c0c54208451400211040405402c04801c41c45924070b03a0301004038994a00044003510780a465024101181000d450085040b03a00103550041d1200001d40c001e440c0e41d543d8032000c03590f401461421000040d81844503040300078005401c80c000310b03a51a03081c21498680c0740302400282c00d40d031254181403000104070b405407240000c450f0b000015141d60262060440080b01144441b20001590742080140c400d05144107210a0080281c0103000040c10103006445040f076240c44000800340b07803035810000540030440907100da807140c000861103d410300c1000d000d4601480031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 489454739 1250 489453489 489453493
    0x5010303052d070b060f0f01050d11040e07020d12090809040504050a0501050c030109140c030403080603030d061e060c050d1b06140906011a0415050405030102161103 73
    0x100046a400000c0d261112440c0c403851480b290710200c20114280e2408031021810b802003290000e110948203032034420402603c405525100683c1080403134036000d88420301052041c07240030f5005c42d440e40002d504824001c81c01d840c064460703c2410341d007041103070f807000140d12402d02224100d0348500e514220300900070062094559540d1401310500410180394015030352640028240402088020803880e0031000803c09070425440b81200c41c0c1c8240181840c5c2402c010035a814040744140c03071403007408404802030460b01d8980d421101131502a0203140d0500c001d1041d904108254400d6400500a422484021281d031008401e254155680140188122054803002160010500e01c07001e600515025201000740c0d0310400c540b444002c0060b09651410191445402000e08480d00aa140201b15640d80ea65954804800c2c0c250204910b46c10790180300801c03443d4604894210255014284035007015150f20110b0700b203030883c120055032009409000c4082c00105005141106001d0300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 489455989 1250 489454739 489454741
    0xf0609030703030b0f180a06080a0312020d06180504120f0c030c05070b0412050c0d051b03030d0f0c0e150901080c09060c0f0c030102040303080408130f0602010207060f05 75
    0x10506031203020346a4080c050644900c0784801c42e075070b40101101000401000226811074208415100590844a0843c0d4500d445404601c0000014404c0c0300a58940d84030b070a250805400b00c1c1c041d4201c0f0b49482c210300d403250000300c1c490107a50303003000100141c41c000141c60701d00360800650440902880e0382c24403565400038801c655100c3c400caa505a01800c0c440219031452400620b80342c601e42c00704000786400300d4046004d09070352071614400ba0081c011070751648008400c1181b9a0125071009010740e11036022040c10301c50040309000c04d824001c0a69003803840303484010059961204100082c190749a0b03400c025150000d5139a0070500003611405550602c80415a20310b11407010000e0500183d140000c043c051414101d0b1403082c0050b20703882d02d55407503200312a80c0d0496040303508258040c4003c4006141014800d0b02e04598141d52104074a80301c9071280981c80d48403e4941340c0206400c0f40c04204116810f4101004003141d500041c1d0740c0038a820840c5c1111030b1182c0450390b06090038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 489457239 1250 489455989 489456001
    0xf011112070e0904080a090b030a02131401050318010b06031603150303020318120a0c0e1b030105040c020a061b0f021b0103051009090f031709100c0e1c02030f06 71
    0x1815a00c517a11030700c0a940c4103100305054a40447c0795004402c880b03000030410003900f2580e00a0403070b92441b680c0b40308055890b0810507444c02e811003201400901c040c800141501900541c44d0390f65580140005188030300174010510a601c101c1e8140c003008042d11054000c0f507414440c4189110040c0804100e00e411a54020748174400d01c020440301102e1010142907030b54950b1006407036081444210348241040d81307000440c1210038840d8080e0000c58500040c203041480120490443d2070b1032a080c034580c2003004003c000c1503c5441c0c0400c522071485c5860000d0084d1260705050b031030641603079501d0300c03212400600000d21084010700b150060112011030f010b003000300c4601c01e002403c01142c117a4903100f14a1224025501141c0342c181400c0f442c405128005a11b103208900941d0380c803070301c88034103964914484c1e81545c5c0740140d60f01c00e181080d040030181c0e224580149507450581101b00c610800944141e2440c0c907405c80c3c003846403084070b0441c80c080088007c07001802015115034a022 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 489458489 1250 489457239 489457249
    0x230d06050f060a0e04020a02070509010e090105091902040504060603080c01050412021207110d0f03080609060103231015050d1404020a03110409080301150f0509030705060702030f011112070e 84
    0x1004005020315001f080b403800300307170003031100e20064100540702039251341c0d4880400d03e011380259501d001d15468500440da00d0341001c16490000e00e1010804241541540c0c00d220003050024001e07126203642d108080b0009440e44028400882004c00120303031401c02d801c0c01420090852144420b56118010261008001074140d0384256006074182e8004006e400100e07909803a400f200503c6d071541c030003c010400d03420184a9001d0401540c1541042ea1a0030054084810702001d003030b19800040031880c5100103050007036034030040c20443d10b000a0350303454a0b140c3c61426801d81d0004180301007085408618944140102150054035005d09800e054021800009070b0b800090410440e201c2e0035099611180c00140c20550b04c51441d80e134940e0f40e810040710400c01800c640c000546201180c501c0c052046042d01c2d0840401005089124649802c00c030303060307012900c200e8141c0140c01040305c41800030f2040f1709140b001481e14507a0b92800c0e41e81407429840041c003003010310505034026646a00d403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 489459739 1250 489458489 489458507
    0xd030c05031e1005060307090e0c0a0c110307032103050a020f09011d0306070c120206100b1c0906061a04060e060304140607020f070905010b0901230d06050f060a 71
    0x110600a8481d445a400741c2c0804003031034004c5030300b124000040c03003d80c80c1c0c4543c100c0c0032038130204149820782e00e40c15a110014403030080c081002410200da030002044034144a419807035030003002c49406170340c0d03503aa030a03545420303103040b0b000003070080c642c80310064060180a03803280040600f146402280e1010b000c1a00940c0c1d001d50411018100d104800c400300047c0242c01d04d070003001c4440a141207400103028608140040303500b0455110a54200c40c00000c01c3c1e401040d95680b80c800a50030482e00380703110340281c0c034004030804122520a00700304407031080c444135600641c00412841d0801c010a81c0201d0640790070380441d10108810031400d0ba0180c0554000001250500d07071329180da051000e4407541501542d003050041e58144001c290b00001c502d01c0070000c0c003064901b000d995aa02c0821990700344181070302c4040400150700f1075071151301c0c3e42c00e10130b08400c0401100240c04152040c0c581208201850f503540c3c0b00c1d0180040e14200d140f01c05811001c0320218605418190000c0400c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 489460989 1250 489459739 489459781
    0x216080f0106060806150a0221091503070e0f15120907080a030801290c0f06070c020d0f0f3509030318030319030915060503030a0f0509060c0d030c0503 67
    0x4401b01f20f0302d043c1031003030002d401354018049190004c1c11007202c7c518240d074081010719109071805904c8100070110070080c0c9120b808207480e030301c003001e04082c02d000300c603030714081501e601c81c0101242030003141c40000901040d94070b4550312009450000c104503e08031240d001104d460f030060b84144006540284c03180c0c150341710340c10307180410304c560340c07411050a0740030110003100746001c180d07080380d00d00c0055080d0b1035080c00d80488055483c1e1007000d8503401c3c0301d1200070b90407039088041000460081203021232030b84d2141280315803004498650303c081d04600c02c00207100f03072223501254070180203c0c0075103420301803072a0702286092006070009540c0d10980c1405804149644003440160758103000b600c0c0c980314040407100c0130650489005004002c0703480d049489613240c00c0c201c2c1906250384950300698030b020f001145080c043e414180d03040071140318140108501004080c6840d115403001d0040001008014082101e501c580507041e11014507100080202c24010440e00000f01082004810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 489462239 1250 489460989 489461029
    0x1203020d02040b040e1027020c190308090f0312150d08030a02040905160207030b0a0e1504021f0210090c080102030f09070f060804030e010216080f0106060806 70
    0x146038000c400064021940300081000c0040350003c0c0c80900714030124400c01481c61091600c503150b152040010701111218051000020040b00c1240d2a43d03008203c10b000d2281165640300c0442ca150f0b0f00f2103203858044001502d44002d0101441e0100102450f210710311024505254110341d0b111080c00000304070860100620f050b09a90b6101d141c030f401c6a0a4019280560b40c0c07500d05901d802a6225100709150303649800d00240412802c541680c050701031990191456520f1502c82041e00440a0700750440c0b1590741e94280c031800420410410001046021011035203058010040c2c9110800c0340102102d122011003500b031740d1701140d01c1800c14200900000d440303041c1c2c01c2c030b46140145908903544941c0f000040c817a072880c0040556200d21000e40c11294216252041c60310304c03000c10b110308404103d860020400080c000d0800c5030038620184110380395541c040c00030756010342c0298484400c40d0414880b03085205070a000744405010103046c4034229003009000b08081c00024004070700b1070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 489463489 1250 489462239 489462247
    0x20a0f0311091809071a1e040e161101020316050f040e010906032f0603061201021615090305070b0a1b03020a0807080f0a0504030e0d0b01050307080604120302 70
    0x801c4090080d5540031201a112145030b00c141c0950042d80b51083d21032100c2c0344206072001034480c084628041200f000e4220a9041c100007500345160a25a81014403058405200101d400303641044014442c440301101040d00006d00c1101800e40340c3c001c060140e890340108104107804201303003104d140072402d524085540d0024030300101e18038099a001040780c0c94a00c000001c8400003a040941070360300810002300c042ea18401c1405208176194546003410000202c021680d1400341e01171036004c039018211210030f50fa0701029600326031009010004051146401206102c100384a0542d000032001040014101c2520082c0c1a0b003d0400c00810903d6503c0c009040100c81340c01c0003807907a4903035402d00182d0b0701c540300c068080c0d0000d0074110005049103002950841c13203030400318080d038880313107552000b0b8171984400405040d00030000d1b03040c046440701119082d140c1d0003d80a9081c040d5000700d031154107120070141445402d5128003001d500102c1840041481940c0148144d241b03402d0059030713 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 489464739 1250 489463489 489463511
    0x160918030f1b030e0306090a1e020d02040f050a06170709050a02040819031214130f120e03010e030a0f0513050d08040e0609040305090616081b060703020a0f03 70
    0x10100115041e442c0060b40c400041c00c164010040c0313a00c0200450584a240ea02d881e0100e80d11102c9004c081c4c4240d403442c000200040080c0c403c030560a001410240600c0c43c90780200e000d442024202d4441c0603664820026804400c0c0f0450780a01080c1101c0d802990070901440d070b0f46c0206004010b5240c1e0b50b54046054510980c0c1150014407071481528840301d0403043c20748000c8080701b4160003041010802d856140505d101d0048154a02c6600d8581038440c40ba000100802c8000e003210151b440b140301c000410644d4800c10340c800320342e558400c40c0010140916095a4035021800c581d64818014030518541106039410f5100042c601140c5514164013101d00406096100e6500280c0e10303060103043c0040c00c40100f050f1007450b80c2d40442c2c1c0c0c0f00c003014820f0ad2041150080c0000c0c10070703c0010041d24003000280141030300e001402800b10502d494580c10359024265002924124151000a000081c85417a40c085c4130340c1021414000103100140c0880760101c146400c041d074541801c03035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 489465989 1250 489464739 489464747
    0x10e07020708061b091504031a101502030d15140307080703060522030e0f030c01090303051e04080708070b130e0c0c0102070b06010908071211010309080705160918030f 74
    0xa5242d0003440410401b6441480113201d5009000c1034a440312202d0070111440f00710580c0c28002c00c180c08200000c42d140820659500c0c6491482c40b0841c0010040c035010140b00e400303101001c80c040654031041c145070081071000c06504800c030382d0194120540401c81d9080c041540c0c0e085a40104c00403c0341d40c0c9600401104a041041c04070000101300c0b404805d06500c008074002c0302e4806c1c0d4014160168901c2010365400098140030300081c2c140c4024070009214002a141c807141040c20301020486e2920138a241d50030a800070305450340200703c10401d5200c1086520b0042515801c0305152800080541b440358881d0b0061559824400f0042a061550741084800801d80c40c030003191070301103e00d0043c0d480d460031b54506000418a000100c2c1158020959008a800c0f140e80c80032050210356800400b50107045000d41455915544040801c540400030010148900050143c1e83e01c61070210342000030f04d0b04280c01051428041208144c41084011225609420700400000440000720303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 489467239 1250 489465989 489465997
    0x161b15090204020910020a03032904090501021605030c0601091506032708090901170d0c170a02150106020109020f010c24020a021207050c010f1214010e07020708061b 73
    0x240c0041d6442172601a41e64081010158544a941c060050080a580010038803c000740d104d1881261300c1c0c4c6808891400e0b074001c1030242d109000141c1040302071a01001300a1340d102050306d40313030030014030482c000205018043c00f4000307160080003201c00d0105840c80248050041d0424141d9800c51020302402121100883c1d4032500507461070900c0038039140c0141e401c10311929015200140011401c2e15140182d5044000d40c0d500400b0b10b45210242243d040030241e4059807003802c0040503402440410303000340460410398000303048a5a500890070b0300c28138142d001d4400c69250880104c0107035a03440080045c60030902e40680d841c1640d0074020701140c00c082c0303c0c108504800d00c401e01c40b00c2c0540c0103403c0c1a560341c0c00b6038a203079140c085503400301d00c1107020007441908400070410466014049030041b500c01c1d0b1401202c20804602c0c1c41c0c044890f81c3c1c1c070450100c9000d46c010056080da000500da404206840501540d520340001a640c0f848050306e0951044620042140a030b242d96082d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 489468489 1250 489467239 489467257
    0x108160c1e08280918020915030408090909010603020603132f03121303240e0a06110a02120a0c020d08040915030b0703020f070209161b1509020402 65
    0x90380e9540500c0020000030341c10f8070090031128041000195600b0302460352081110050046000c4025840c0a03110003503118201e40790b804031020701640002d01c51440070354880c1d4424911160380702d42d20003c1040c032000c020655210343c0c0c1460400e10058881809498020010300c859403030851141c503000071581d01c8110785404d0710701250038000e44052085054010603000380d040e169440c51020040405126400a4920800d21040c1c10000a100d4091001a50404624055100c2d802c0c620320380603038010000421040d440070f401035003440700a00c0380951601650752a10318202c45164041c1d11034103403206030821000c0114514881e24010f01126410740e500424040c0103010301d02d4403940f60b03040390140f03001103484c1071080e648212180302c41c7c03400d036a0444205000b507580c03c0c1c400c42c042d6001546452005205012120050301d401d060300740034030591020703040074580081004014a042d00190030401c100d5206800101718680061300c4001d100720b5011840c8180707400424064814843e031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 489469739 1250 489468489 489468503
    0x405040b01090606091a0f120f0a0f09110904111c0501060e0405030d05070216180e01020a12150302060c101a0906010e01091a04050108160c1e 63
    0x8010800c22481000c034180c8031890307400c012080e03c502007190925050701030803894074503a000240b840030500024000711f00c03403030f800145051034500c0e20130703102881075503148808483c402c01d218800151b402034400203d5111020007039909203807200c0f41c01c00c08120840d0300072448440440c062210701e00c5801c40030003003e40749541d20356a20600e401c0740c468110702542c440d4689640030541607c102a11402290028015400c0c0440c0480d90b000404001d882801941b15410025220f05030f040e0080000b40b1280c216a0208880c0d0030007541940c2c3d076040c640d112648100803c00300e1540100203a0207103251207100040580e000580341d41013071015040603600c1800455a00e41100c1d000030546480320380301b1000d1012014441c2c54010f40b2010061081c0d2083d4a50300084182d4420060308081e89030524061340e5482c0d440000c0c080c804100c24030810400782c0054107011658100c2c072403c4c2c101d90440c2020200c04003859008003032600e04000240518880d1080c00302c0c030100c0c6410249441d41100c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 489470989 1250 489469739 489469741
    0x120a0b0301060305030c151b0901180e070f0f2c03033108070503030403080c010b150d0c21020702150d0504030f080405100c050d02040b040f050d0314180405 69
    0x1411f40d44501c04d03040d90b4100c030300c0c0c1d50001e000018491407540c04950200c10450800d4514001582c03240503511034901110301d84100010803500508025006410303d03140e60502c40c001110080503070b01c0d00d070701c19010310511402520040c1500150260307091605403503c1c105000500c0020b0a500c904240d000100c80381d60f009803a41710b49502c0c000409000c403202d00907401d030b4440070103440d601075201d041c1e8181c200340b00400c0030583c040010700080c400c04000180c0d52450100241100c086002c00070031021011448101d80c0030184145070020b541400d02c00341e1803070000c566110340702c010802002e110303401260700d40840d10b590f9410700c1c0302c250803925941c842c2a03200c6102c0c01054112002d800180c660340d0421100350260000c580203030b403c50050505914005001d030040c290158103001004020018054401c0d001d10250001e405041521552540351182c0c011080c4110f8218a00c43c00d85281000c2c0040d0304100315281540004039101c1d1a0368900700c140d031405205500d07442d00541003130 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 489472239 1250 489470989 489471007
    0xa141203040b06030f0a0f031803023a15090318170105070f050a08040c09060810060b04050a090b0109380a020c0105070c2103110102120a0b030106030503 68
    0x242e040d109600680031101d84c10144480c15070780f200422000b802e0103918003140d0011a10404004034a029480c400f440f009541e580483c004800e03184802a602008050040b00008101100101030041400e904400c11a58844201c841c0e1010f00031455a40e50b00c40c01000c0500a03c0213503101d0320030b542c001d0030700c2c3c0e0788044000c40c0e8011001c0000c031651034440000c0c035142c060103112410100d1969958100302085006607030084d4050f106a891040341070000400d003010340170320406031041d10080c10b24102c015404000b070b998140c1103069002424402488180c55540517a802c643e200c0c180402e0303070106600140c0340501a41c0200350940d49221900401081e40c2800d54004900c403040e00c0105d1410070180384690080140842c010303041500c080b0110340c8120701508089005200851685030769039100d454441206a02010080f40d42081406250b0880b022511b214900c030025403a092410140d00c02011780140360407070712a030714140030625403030035030000d4091940081125940c44081c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 489473489 1250 489472239 489472253
    0x111203100b03130b0702030304031407020111010203070c06050c07050a1713030c05030c09012102121903180602070605210c091509060304061806140106031a030a14120304 75
    0x1003e410380303080c13920402081641c0e100008891013207400d5510144036045601e002203a5610402c4160304105945070680c0b05810207200460056007552910b000b0060799240010035500c0c010301c2e1204101c000c0c00460301045020500c0140258040d1070f00d0304000d07800141180600884084102c5000e0045012040180050b040425164101c0441c4d206965030010855664800d01800814004c40140c0c0140c0d4040c11420105442c4001c200c03d444848810181c0d20b080c40c80241103e44242c0004a802450380105a6801d013006204c81349003460b0500703201035a208000c0c0b14400c02c02400141d404a2400e210140c81500102001c8006030703814113094140954003c8400710340b050241611070421400d10740221500020007a11407410360361135485860041502203800d0a90b41c9541e00f84100141880c89043c80400c00c801c0b008045506040000f02200e1440360042c101c0340c0e0a4182c41d02541c1e00003600c1c0c0d041175100384620583d1034206045401e2000105014011600104c2404100801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 489474739 1250 489473489 489473521
    0x8031306120504150507020102120a05010e130c1a0f0c1501060314060907030b031204060e0d02030c0d0c0b27060a0f05070c030f050105040b07111203100b03 69
    0x515039441d0510040d241d007090440360b003030758018150191280c07020f452410b140c0000c0da111000340001070420605010b40c54017540304441480c0e1140e60b44006201c40d541c01d030502d580081007000d6040da81385003a03483c550030180d00d000d5004d5001c4000b00c41105504400104c400b0301c5040000a84c41e00000440d2550b00c15200101c10086800c4200100d072980c42445203429240040a001c0010748a0005001c2640000b818410805803103044003074554404010101d10a0060170b5816a254902100104450f1a103248284039010400d40840981c0d00054184442e480484040314454205c1c5080e0849134410f6100100e5030401154000410f00410140314800e03414000c0052081201410040c19104041d11000840c0444043c100d82c03d12583c041c10a003882441e00c48091a26516002d1310040da1a508035066911481000100079031000ca890f0855031908210256003113250040d501c9a00794803050342c01d0a03011000070310a03aa0051030100405800c1501913490500455030707a4403041d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 489475989 1250 489474739 489474749
    0x30d0903081005031204032301090804141e0103050703090b01120b0109141602010b0303070c06031d1c030b0916090806060f0f19090b0a06020a020306060118080313 72
    0x1042ea4000890f400e0205045442d114141c0900f8a40343c19603450782480c001e64040c07403c0c40d0504408001801c1002d00c54210003034040d0b0220b0707441e98508003040341005403841034140901245007898500c001c012108c03c00d02c61090030701181d00e03640c0c40e000703c004248124000c1c2440e0729020002581c014500c100c003240c0790245188015507a00c828200040c0d070036a400846407880b0920002d0505074039100710240d000503510000c81c0c0c0202e910b00103840c541040034180c40060706480300b00075850301840f82d0302c80300c20f5044018503000c41c1e1450040e01c82d844844c803003903071040555030b02c150513209034008a4500002000c100f43c0382001d9103040514a20a0003581c08980d560310003240d000d10008a4900c95100100b00d40d08041081c1c080c40500700c400c41d5001d401c9031701c583d141441005441105000703840350200c00107002c1c90100410080e0750003588100d0640d0170060980001d030310301050041e402031003820301c01041c1c05080d11284100c002a80840598000070401c420a40003001c80e11045030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 489477239 1250 489475989 489476011
    0xe090a0510060503060a05040e0703050607030501050109080c151c05100914090714040207051f06090605060909060307030210050901030b010f0c061a0a2601022703030d090308 77
    0x80d886180c10340c0d980c0f00c01c0e50b171154400320002c130402251415401082070011400c0603121010382c0c030342d5010701d04901078580002203911103006100550784014010020040c40008081030200e040c081401c85c010b051f411403c610300007a914400700414201382c8041c2207400f00821107443c2c001807800102949010b1451140c1c205101600c091a041a40e6030250600790080c0c00c40500e08030044219084030514960416001e010f00800300b64144507503042e40d40b1600000034001d004030140811100d56810400c0315600d400000c0c8002e458010507511604000e03501003140303032981d07400a850111650320081d0302c00708100e4030401d80b690110181240c5c00f03003a2005c1c0443d031420801540c81c07000881c98040013911105000d004240250000703170b900011387c03031106010343c000408941c0310704982e0025018202001c500c1400707018000c0c20710070300c100083c000714201414017100c0401d04640a000c40b02022840d4001c0400b59820301c21280c030742c02110b4042180007100d01e0701030301ca000100c5040c1a18 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 489478489 1250 489477239 489477271
    0xb0703180804031b031a1b121006020708030f030c0d060b071415041506030c0f030302070e250909140919080a18180e1c1205070e090a05 60
    0x1320780000d203284281e035030002e20203110382200d4201e50035800f8024003038200b0011059004080300c0740c2d08001c105801481c40c03402031525205c06204801102903010f0320855120705810004840080180c0741706c1c091010800da035035162400403503600e0294842e60205140380c00d000040c841c1d00031000f0321031548100e20003040c03d00c03421100cd4841c0e5181c480d03224a01a81c44c00100081d0b02c442c01d08100b9049500c00040e102d48a44500c9194140b58020800b0b1a00c00b08083c0f09058040003a000201080c3c003212150f403400c003011031803280c080140f0300b40b944075418002c0142401002041e000e024800401c0124000b0b14050306824602030780c000c00c40f0300418031141c48000c0d201c5c000980c03103500045958507000598104540364943c0082042e590b5038030520120309030100e940740001a01b42518007180c4000d100094908081106098a02c0301c0615440c000c040740d040303150181d95108482d800509551207003829038030003001000c01c0740e00c40e04007000c000d4040090b611040c0135514105150401e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 489479739 1250 489478489 489478523
    0x170601150309050a03080618090f1009050d080c07201e010e01110102040305010e0609011401060903060f0b030a030906090b0a080f06040905060930070b070318080403 73
    0x40b00c09441001c2c0980d00515202e401081c0950700c03a0740c000728050103003101c0401829600070380d80d00698031021250000e0b42c9441e00c600c0c0c10402c10180f1407000008000c40c04180d69225a0f0704c10b00031146062203880c0c000201c00c0318400095419068018990386458049803503a00390140c0d0420410744203140b44124007050184146400f40105010384492100042c04401590500c0f128101c0c844903640800021002580c01c1c002c0a0050f452640280700e5800c3c00c085407401c0d244403088092102c031110b001044030a40c01000c2c0d004507604060f002613400740c0004518060410320078415018882d5844140406a02081e41002c48520741d49031440c40791280a80e25141c400c20100a00086103540030440035007413071011940003074000300002508180f96840c1c138107081302118084443d40010606090001d80c80f201d014540c048440d14030020800206006414080c02d00c01030072207110f501c001561b1600a078014000c40c0360704031030660701c864949040c503002e6209020486643e5148840811 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 489480989 1250 489479739 489479741
    0x30311150702030a0804230703150207020105040605070201020703061802031c02070302040222031b0501020a0215071412040303020c0301061a160f0b091903090504151706011503 78
    0xc09802282d000e9854101c1c0048111103c0301c000c3c000f9514000c402215000c00c10400380210710556510000d440c9207445d60425030012200e19141550181c0104045c500503a80719085a05981050502c01c4c3c03101400d0004034508290b6410003000c0c070386445001c00d488862400c400e441c9502c2101215092901d22042600c417000010050002da40006820302c01440e294028110049441045914640b4012901c9841601c1a0700c251894032440040d244002e0750f2011110281c642030009050f070410a9000c034442400e010010120310781d012850404010800020f101c9040b030300000c42c0d2007082112400380d800d0780648412005407149a403084200d04040c050041103a49007000000b090740490f42c40c07001c5134801004181351107640f4034404006003840300c400034094016a8844070b14509114610b24000f40b1072003940d01403180720121400a80e011051030213071070040d20301183c4050401d4482c601019242c019030802000958490011100020010b0403120b1502c0801ca01d00c000704400e030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 489482239 1250 489480989 489480991
    0x60d05090f0109110f04020d060f0513050f06011d1513090e060610020312040c0e06010e0a05060d0b090a051b0703080403031104090e0106030506060f0f040c03020903030403031115 79
    0x40600c181054603007001e240201030b17000d41010180026280a1801c84180d040303c0ca41d0b003044200784d030400014081c1c0c2c20500110000320b41407040800807810210004941110000c148030304201d646003100700d64001e4107203003158884000e08454030b03c2d5469804800d02d0381000e20000c81c00c00c13400740001244120342c05008148100f01c0050130341911000d0a10981c045443c1d60f0300d05620081001c040b00000d000310507407165009030782048150341001007900c1c00c43c10240003103040041d610341032104c581d41ca404a00441e1303011102140c0d070315010076858016142c000c0e40e01b548a451801080320880041d0050f42c400d90008c0c440800394194480f400c4828045c075a0042d00040500c00081c002134081d62100135400307540a0000d003030a42e2503010300241d5001a98090701c40e5100d04081040100400140f50050000c60380c144501c00e102e40400c4151940000c0507109584030801201d003140242e04507840c41c2405010b07296100d880342000380a9000030345082c040761282c40350600c00b190b0669421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 489483489 1250 489482239 489482243
    0x4080109032003070803011e0503070e010302100311030a0b0307090c081005060a0f030f06180c0e1c0f08070b0420010e0d030c1103071d1803070818060d05090f0109 72
    0x1740e402c590901c0c1c520040a042c85206810140c5602c03004501070780d0400414006004140076440c1a604510500c0401c0f40d001c8051400c3c541010300d0301001281d4142500c1d401101c3c0103000420441d03010010340f404025034800c00c0464a0a481c0c0d00203541e001038500d1045040310560080141c0c1e45060216070302c28440b52600040d82880240d0304588640c1024080e9148007a000c41c04680b42c0032264070400e079012580c5403050b95041201307079654004158005508045440700b080100f1440c1c281240051000028500040c030b40701c03801005120025034600c44d4201c034150f4100e14152910768800200031041915808428603854101d41c420302c0381e1280580c02401c08501d51841d40e40540303a1100d05841200d0303003005001c00740840e803401c1103007100405c040c82e8800c0d1002c01c003d101000009026011040d42e5050302c3c000d5000000000c1141d01c020750044006a9800c81031012501c4017041c1d00c101640301c20002a00c2109680a4102d00c0c0540a00340640703002c602a50b140070708a42c440b00c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 489484739 1250 489483489 489483503
    0x11409010b0a170712080c19031101060501050d0c020f100b1c020a1a0904092001050403050703080a050c030f070b0c030f06060c01140a2f0906030a020408010903200307 74
    0x300f4000d03140851038091009215141460400704071007d62414640900710800401441c1c080302c10901da4070424080d000d14008000700001802c00300002c01e240704049008103940d444084004c10507100f00911000035000704241c0c1d07403080a0300e80349005400c1550605115154031030340207030010703000008940b11070b900816008080e454105100c0e40a400c10041021f02c40702408050000d40710313801842800f9208405500456605680b5000c03e100414945c40c1009010f200c240002000081c0c0b0a0035070740c004a003141c5540390001d08403103610414644410501002c0b03031b100c049005290150003101d00c1111140101c0e80c69a641c40320600046804003c00362550b004105203080840080100700226030000c12503815101c0d10300c440ca81d06907000c2d01c1503a03981010300e01c4040d03d0001c00d000d0344040c094002d503005810040e12441e0080048192041d00000081641001035a040390018200b02c40280442a00f0b400c0c050300c900b68981c0b600c5408034424080203c0554040304480e0f10581c03100f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 489485989 1250 489484739 489484753
    0xe0f0f0f0a1e020919110f12060406083a0e1311070c03110d1a06180412110304050109090915060806041515120203011409010b0a17 58
    0x7114103904008a012034128520103402c0030158440b118490b00c150704084800c003000d0b2100c40254115901110a1a41c508007030045091360406402183c0d03d181c000d046291a50b01d0340380000b80108070350ba000144601c504070502c04441e80a01c03070a400e070302200f41c03500100030f00381110315007907034158038a071002400700d8403244001c0ca07020501c00306246206800040302d06110700542d111354086d2a00792005148a6810002c20685200102610b0004d40d08021980c40781da8603000006880503441500e030011100041c41a00e44010103102d20314051000e1a07141810309040c03c10980e21031540c00000d40000c2078540842c4000200c030b0880b001a5600c56000c0c0c900a0b101c0c0050070947d800710f40703d40703030300424003421201030252501400204016004030b00702440c00c1c0094844031018545802d04044074980840184509481114001078600e494250940300090041c60880c607011842d510410a00034a0501580051503100042e540b10444a44405c001000125154008141640a45 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 489487239 1250 489485989 489485993
    0x308030c07050106090c020c0424030b1302090703021207021f020f0d020403062906040504050a0e07030308061c08030c0a05040305030c0606090a051311130e0f0f0f0a 73
    0x1500901c001406000000b43d1aa1184101010381c2e803440e0754140141d0020702d001445140134807030b1a640c00804145400113040100c0c081c07240c0f031103c1c400500046440c0c40015555213080280b010420381c0107054003203515081c54003034025080583c0311074000d003203540010181d41c0005070710f0409002540080d400600b0080b400170184d03000e160011510042030281844a52080c00500050f600c108008551400140160030240c8410360280c480000030360b41e441c000c1d4445600301c800751607044d038000c00d01d6036603124420054880c204c01400341d48210603000080c964050760603400b039101120b504a801d8101c44a003420b25000c48001703860420100042009142039000030f012400706130034a50b003800c0d604d03210141580c000b41e260320b0168200030300b0800d01e4070300029003650244644000b0416400c1007a00300c106e190150710700619001540b42c1c0f202c0543e8070a9401c10340403c10030b0080c030121600d007814035190103035404004040e100e000c0e0b525445080105000c1d01500300000104103100082d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 489488489 1250 489487239 489487261
    0x117030307120f2c0c0d15110f1605060105150d090c0803030f010f09021204020d03030b030109031e030c021506130e0307050f0607020d0806040f02031306050a06030803 74
    0x301c450f44a16991914890652480c40b840c0020310300030000e60510400d883c3c0d800030b05000d0610b450034442d83e0703030031038804c001180e8403401a00031120758000100c240d6080c5898116210301d400113030f8070060210704190b03800540e0444039071891003182910b8a07030b60380318140210a02019400941000180007410014040d940201e000354010141c607540940d40f40106415a402604c01c00500102c0800500c0301c07000242c0090000c003070b214011440c006e0007084100340141e0107040280300f44601001c40c0c00f81842900114803440005008001b004000d140c09881d51111707051500303d00d03003c030b9000c50074240288100c41c4492229000362086034a040300f0006074030b0004141c00e6000001c1100d15079548500e00c6000821202c040040d9a20300d40e071309102b864030300e41c0c203903036100340c3d010404200035181e0105d0010042c2d8001c0c2081034558a0308400103004e4200704e008120003d2000c0f0400c40b690340300a00c00782c6030034080d50040109132071780405041650102d0001800484080010034240c0500c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 489489739 1250 489488489 489488501
    0xf03150b060c030316050405060403140c030717061005060403170d02030a050103030e150a0332011d060d03081e0925050f01050901050c060f011703030712 68
    0x58a00012455000c0300060440d4014440303141d4694008020050b00341d92050800303043c000c2501b0080d08041c909000200b07640314901004102d00c040144140105008100d60120705a005058596260f110303072518840c0381504050017054441c1c507020a941c02c0b0303d00122320907160301400040c1342074219112182100310078500c0c0080c55504208ca82000051807014501802c030485010480c1e502d5410000d100d84011820f40d403140c0300f61241d030202118007004403688622603090202d05071085020503052454120f500d8030303001569441100309820a840740d24140d030711103d0710000d21000d001540120310b03002c0300c4060700300381003070221000300c0e00076441700354000c000381c00c048100346405146e502e04c4d14040e1440c4085034002403409664824142d07169114100c2d1001a80c07016140100182c3c5510b16080003034180320300040c14601d6079104074203d40c0c6140601e401c481003802e10300b490a010b00310034070502c4440302c1ca02032510019040402220300600b10782c7c0d42c03411691040041302d00203004d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 489490989 1250 489489739 489489773
    0xe1b1e1e070503120105180601110a06090606050109080d0801030314070f0c03021507231204171204030b0708090120090a1202030303070507030509041d12040f03 71
    0x45041480c81051000c4005107040d5104001a41d101c409884200c10600c40681200c2c0c4544d0f094421046004100d800082d030041702440c10382440d030b1a080c1810b0030402074013800f50080f030924a6501c28000107400c0b140489400f0780e03480a085544100b00ea4507001c00ea010180003900200040001c41d1080b1145042c0410841c50549419040e90746c409020002c084112845400094100154a02500d08454200d902994280344c88406d680c0c000c8407000320000c0041e42c0035130242240b00204e08200110751408040c240039503403a143c2c40c01030303280c00300201c000c4214480c0d101107043c4c7c046181c09441c101d036031008403404580c884000c04d41c0c3d84130004000e0426990b94240081004509902c822010311002c0c40891b5101c2d901001d00404181a03002810031201e8441e04600581340041100d9021941d880c100d5102c510a290442d21031040096081c3d105060116040000d882d40880340c0c01c103000c04003215981a10401c0700100c601461203480c0304001900c008002040e0107a8150140407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 489492239 1250 489490989 489491017
    0x30301030b0403031e0204090906151d04140a1b0504090b07030b040e012903030c12180d0c05030d02011a01140c0106030c1806080d120e070e1b1e 64
    0x9174608801c0100d811a80c0704001254481d44580188503452040314003600c0d001150190003420900700f03090141c040e18400002c0442e50300010f0a0008041d030111013060704600750303030319a261806d02600720286403140e95801d454003000000c03103103850301c02c98481561146084400d5a10448142c00a0101060320b0360060744a41341c0e0fa00103d4203101e2042c1c00d0321132050145088400750692100355502c0354503503010341e00402804d0701720700d40041d00c4501c4140e10b815041c0c1d5847e64643d04003010100402040c0c12000110014007040403003001e010540b44150215a0706140d00c42d002c07420f840c080b60b0b04075a401c24498003c1b03010b5118a000d0f5201007020b000e141c0c036041e0800311080c2110020f40c01074450a00342901408010102c00d481c200016005c1c506021041c1403507403403500d0b084000441401d0004402c03104420741200d0b040301010200001c146d9403032641d103050f603000040f01100c0350f0305180c040036440c0e5039a80301001522100c5001e070a0148001c4045441c40c03259501c2000f60440741c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 489493489 1250 489492239 489492281
    0x807120c1101410c03070c0c0b030a141006180803030108060603071e1202040b0603040b040228052416021c02010c0609020103020c0a051e030301030b040303 69
    0x2071100f4010305442e000740c03448a0542848201041c041c1d4200380d080701100c80300b64089405110240d03801c1c140c105180c2d503140c9a49440307038181a200c05d908600010300c02c40d010800028441981c0d000b6511403120200280158404091941e5400700111040b4140665224050003802c0c442c0300750100c044401c41641c5041900c032240140b56800913407140388240e2205e82045040c0c1400d00190303000304440c0c0040e41d500c058202d0500c502940030f0140d0700802400a48020940d940c50b001203000d008042c003a01c2e0b40381400e09013400e6401045505034080d0002c000d072148002c032451032242401140c10b0540c040d01e4180030030001e80038030105110f007103d00110812070102c0301c0d82005021041ca031b080c14202407010381c4140200c3c902c00302c43e038080003070b01020b041e40940d0308842c02c080031a500504c00100120144010f070002e01402103010102c1c46124032640411100090b000380070700103041e403041e4000c0e12400c007a40e244024040100072080c00d202160019001783c00c0501ca1880032682c1c10700b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 489494739 1250 489493489 489493517
    0x140d0b06061b071406030103050d0c11060d050618100501030f0902120f010f2a11010f0b04050f041218051c03030b0a0803041e03060f1401060807120c 66
    0x11800300d050714000c50300002400c20140c0d1507011202d1350340380290340751825503256460741c41e02c0b60301f51007412080c044000340200410617111000155298000c10b015200e141456900740141303c21206a405454240b1208400184800341d440c03290388024900140e65003010b0046010702107200c0c1d0258000e8542075204010790794000100921181c0e40010551041d120740800d007940c14038941d400d15145480070551087c01d0000b900d40142036120740c0d508011054600480315aa54110700003055460700c2c0105075108144d40000b1042e00c4101c1e402c7c042900e0318400308000e2101502c006051544c500203001500c6d0003540b0090300790302d1007030031251619960408030b800e01d02402c004582144008010104041d01403040c44801c41c01561000000780c00c00ca00039590b44298059400842c1d181c0002c00019103102d4840405564084014081000841003001c003a10f501c20010403c00810030020800c0791007107400510464140d656070054141b00c2e40030400505044010f54100300203c0d60303c10b8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 489495989 1250 489494739 489494767
    0xa0b0301090b13020901140a120c120f050c0904150305030d050601090914040b0a18050a02010905061e090f1c050c06210c0418020a0207140d0b0606 65
    0x100030701c1d2240010586a01d05000c10903604001e80c2c4042009106006401182e640241280074142211091036511811110f003503410b9410050b44020f040e042c80780341400594030040c4104001a60b410900100048600c4c01c2d0039540c00f2103186000702e80a0203a2801c0c1d00d0290404c0c011200a140102d503000d8998075554210341c01080d4146802e9121401d01509590121700c200040c0ba402004106010350042440144280944003600540d004004210344410301e03030104005110703a40c48602c02804500c2d10548501c101442039001c1000b2540024850404070200e50380702c0400583c042010002806069068114026031a04a810740c1c19800c0a511103824510010440c900201003034190341ca405403920505007051030141e03038140701c0d0b0782404400c1c0f210003448140d0404144015641c40e071611005005941c404095180074104403000d441d01c60f401800e54521550a4071001901e5412050b4a90f8545411170742150b04128100302040794140304c2500820001c05941c40c00802c4202c80d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 489497239 1250 489495989 489495991
    0x14011d0f0111162c07031104050307080c1014030118200c100204080a0201050918070c0303060605071a13021509040b090f07110715050d0e01091e020a0b03 68
    0x83c801502c0c40c0c400e004000044000000180c4000c0c0a11001580350840d8103031060013902d40c00515407110162040c401805003507130040c040290848141c555218081562180300c801402e0044403051941d0000c0d81c42100020b440101001440349076034030704105042001c5c1c180d0070042c03003265170b0503007031100b108410540c0d04c8000009036995103908440007500d041c946441c10304040c0e40c0c0304001c104804840402c0c07001c0c640750242041602c0e00d5484022840d00000544000202d010020130415526006283c004495002e03550401071545c0300c90058601340300b461000350600900e0304144072141004500154415444903000303000180c182c0c0400c2440041c0c02e000d208894001c42c460207503040c548101a883c210485455002e410807200110b0320880c003800150821061080e6010105010480e2000a04944042003280c0703d81250041040d0443c0001110040c2010781d5030020a01c14020038610b01c0c3c02902c00025501002004401790114950880e000181e11b1400245a000d64010f1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 489498489 1250 489497239 489497263
    0x1202100c090302120616030f0e0a060e0601080c030a0209190c021b0a03110607170a0302030a050c070c060516050a050f120f04060815100914011d0f0111 67
    0x80700c00d04502c10040ca215018240d000641e01c0001000040ca05c4c40d80010307000b84090500041500700c03920030308003400664a00585d28403560882404020740d0f5400240c40100c58419111103988403401d154656158054455155002e1032140c2c0241c07500d541f10a80181c08640350510880040c0008030580d403010b02c01d44096040301801d17041c80700d05403007210306621044030501d2030a401c41d035420300e00c0049920054007658000c541c50040107070200505d8034101140301e09681310a20302400030040e500403600d601100342400c0224030760014000a41d4481580030701009101ca09141c800c9985400c00012481c0c090030000c0403a000c11000c0c072941c4551802180500a91084009141d00d01540c1c05070104421034100200740b0765000307440c1500c06540c0e043c07800c03041d2521202c07000700301880c0000d1083c1e8040102c041c260101070f04000e0342005c0750540900c880409071140c00665860410341e00950070018280c101411500d0440041020710303e050603e40302c0b41000340c055601c1e00d903c001d40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 489499739 1250 489498489 489498497
    0x2060106080a020906030c0901050708030408130f08100b01090b0408060a060501110d1101200703080106210509031e0c25030803060f060a02010c110a0f1202100c 71
    0x600200d64000500e907807040414205501e0802c0d201d000c902a84401020180011400720782d0000c0344e0f100d0003c4801c0d9680001c0059100c3c00c04d420003c040e0b500c421092100e12600740000500d00c054006520121807100000d40441920081841c000e002204100d5041101c141800303e4400f901c3e6000c0c00c060b00140c0e0040c00c20b8035050b000001143e5054015030305001e00c802ca841440c3c5c1c0005452441c1c21407900c1c00895030040b40ea1154050100044d6507103011041c0c000540400d41c7d0036010741030141c02a501c001480c1d90307841d819110546014003d801d6021511a950401142904403d4000310f003403045903d0810811920030036072802c28201c0c9840b0200180e45540c0071401c000b640c00d624602d45a021564800c2e140300101c0b4903291100034600d50380800000c182d640c404040407a1349801914180e0358000459000f03000f40b21603092400440e0f039001e80883c900d800080c01804580c4d00c0480c041720342019480701c01c540c100c002140d0085101d02d0003e03c0c4004240e0058102c410201d40f5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 489500989 1250 489499739 489499741
    0x1506050a020c0f28150e2701172a0a17101d0f06010501030f02031012171602090601111c0e06041401090506070c06050a0912030206 58
    0x80000e06000500261520640001c0070020450b903403080780075009071803454070300d003480f000600134000c56403280d000c1e06050103180d0500d000180c001d40c4403209440c040b1a0300d04240b030007a0000011414101c0c0d2000500b51010062004681003003800001d450607130112031080410449080100d482d102540c100103810000b80d0605003410448140a056240702c020781c03020100c200c0c56130f59130680080e0040291542a0380d01c0c80000e05165100b504040c1003901c0e01c01c0c11540746941e9a60080c82a980001d01d080760f22040d4444074420707240201b01f811408459503192242001045015001c1940c0c44058010a0b080d10f881034402030a03003030040c0c00042100c500d5401004141030004001d14144084040c09450720781c0d010031500345242c0101a01944030504402c2219180182d04038950404000a00070520080c2c034090200b0400e0709a80d043c1541c0c1d214002d000060140c0c5000400e44010708109125050140c4c024041d0b580c014036154126079a0b556100080501c00c1000b0b50251b04014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 489502239 1250 489500989 489501007
    0xa0e01180f060501051c020603060d05031204050607030c020a060e03090d0f03031107050604021203090d03080a0f0b01090902030601050f07060902010809191712010602071d100612150605 82
    0x10041a0043c00300301c43c100880b4001d4076946004050106c070092051100000083c0305a4032304100c804120381240840303444c0d4100001c41d0300c00d10300699003a6828800c0c000083d1106119009520041c4d15a81c05000407298079640d000103484c0720621081ca0380018803016015407140302c0700c403e0140c040ca0341902d880005080242c00c03501c1e42803031001050820481c40d0049030000400a402a40c141d0300004241078100090b4250300070032205070390090b070100289040c50790226559000c0c03585034808110071810514010f08485803c04024007080c20003104010071803007a0b01844d44680306061a03850b02c5400c2c00402c049a201e00c2d0101d6010303680d01c8c003007030955078481c0d2800c3d803004101000b8800d1840750f40c564941503034240401001307044013208140110640d1029114902310b072080c0038186503159100a5101c02c0d9602888a1400c03820030100d00c0390002c0200d140c00b03811a07984000c1054100715089517291a041c01c0c4814081c0c5802c0c074190310080d852500d0700102410741c1c0b015100d950030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 489503489 1250 489502239 489502241
    0xf1006060206040305030f0a090204050c0d0b030304030209190603151b0e09010b0703021c02010c0f0c080306090c070f2009060f09060d140a030807050c060a0e01180f06 74
    0x5800039421903015408000004e5080b10440c3d420012000f101c800c5a900c00100b1009082014030094001c1d04203030602c45601685000f404083c9081c0f032003800380d201a0414960f8074000c03848043d60028909012070032800c441c907030b411400e00300344001040450300c1307455540e03603899210510302c074566071014000000e000742046c030702e81c10b03001c1d161600003d244503000881aa078103000b400e142c8030340011160304050082200c021211045600302400c1d00c1c40c100c0188c02003019014440100c0d50b00fa0200140c03511505c010100d080c0d2100081d81141c59007010b00025803001411510304100801414020450046140c091903109031004084e11034064400c800c2400440e1445008010560a019195481600b000e10b1280291541449aa01d5400040301001c072818060a00d981c0c9540d40805031502207010b5540c140240c1360f203035180d1113101c0c00715000d1041c0b06004100347c000e00041060703055290008102080c000001165400410f420282c070b8892262048603c028030fa490f030070400c40a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 489504739 1250 489503489 489503501
    0x207030b0a02130308090604030c0e0a0e0d0c1b17161203080c0307170c09090c04031a1008030a020105241011011116020109090c051e0405030f10 64
    0x500000b58140030341440c5620b1000200d0000402da0080480d011905840f843c0c01d85004680003074100e013500d03a4692100040300000c1e00d000295a0030190f0780c1e070b514000014960356030000da0b070741d06161050545500e00b0203002000300130080c04010382c00141c401f5010000c241510a120b000c1c2c010a22104101c0380d00c030980707511004800070320741e0b00400402e03006101154045201d05003150781750741c1d649088601480307500d441462400201c00303000b0b160740c001001c1d024001d420b4407180d01c103841d42c455040d024041d521000b0108410064036003009000d0756034864002400442c00c840d5280c0351031050741980c00940b04c0b140181c2d5500d0821006c002d90b14081002044a245405010085800402d91044284590b513050000090f480000d640003540a42c01c1d01040b11841a115032003441030500843c850002030b40003850703000380410000400d00c29088690000d07220303249001402001c1520644450000301440e4005000c00034098405111035000d5a039000003034900d00e070341d40c0000401c50796 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 489505989 1250 489504739 489504751
    0xf0a02031305150d050604021b070612090b06120a020a4a090c10080f0f060f0f0103020705061303021c0c11040f0f0615021908030907080d0207030b 65
    0x740340494000e0542c900c0491313605801040d00868a50344000100d406407040c24000880050507180380e4010b40400301c0c2c9001514080c0c4d684800041c0f000c08050140d40c82c51002070102c1c1a402c010480740d1800d0348400d01c03e902990146c5013903d20640001e002580341303034080d10b02d04118441003002801d0903101c0e80640440e01d001c20b150007c410381e800741c007a80c4900d00d804840c801340c1d000c224140b80401c1803070040354005200c651500c01c151310040500c00300703440c5a50b00e00401d13004101c50011081596115100150007c95000402c900700100a11010101414981d08100ca000441e0042c400c03644903003030322018058000410b24000b0300d09281040c1034100c0030b803c62481e4070100e0781f000c401d42032590007080001500301c1c00e2001500a244800300044041c1c50814000300900c2a50801c034111028107000800d44507a4002c26a12509444090f8131280008403c0200181e10400a580c0000404007280c51181d1a002120b24041c0f1020a20000d42d1000e10200100000022180d0740b110b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 489507239 1250 489505989 489505999
    0x10c020405150432042102160504091a0a240e0708010305061306021c0f0b0a050102030301090e011b1e0c02060306040e0c1c020301060501230a02030f0a02031305 71
    0x662021001607090075141391101a8900e400042400e100700c51120680d884002c03441c040c51a240c0c554060b684181700d408402c1075807191200003840d8074080c41100781031a0040c961481041c20205d40f42e00103070b4024078000c0190350f40d405001160001c401d10034110b000c0d0302d20000c81c050414540790b02d4084002c114008101d64500107100182c4007040954001142403d1312780303008138a14044020380502141e070f001800302c3e12420103910805402c030040c0000350000801201070401e00380454040c05000d6680903910400041141d80c441394881c1c0d040541c40d100000b2100195407011181781481001d40f0b0014140c031050000104c1c040402404000050800b40c0250105e03901003640760000905040c0f04a945481010a154040c811500350340c0c4001d054a0824500c0d00702c4c00c841519080050b40a0340c41d0010102305540070b07207007003040052800c0300544041003913820160907511801581c0118001448982c00800da0700b4082c4c51056407c0d00659241c107140240c144060205500c098412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 489508489 1250 489507239 489507281
    0x50a080606130e061309151a0d03020618010203090d0e040204030c030b04030305100e0103080a021e0d182402030d021216031a06070201030e0a1a0c04060f0c02010c0204051504 77
    0x20400c01010700e01600c07d400104413005a89070400b0b55084d0401903580000f10710140104150380420014030403400c5428a10001e60b19010942c00c0f40001c440162080c0c1c4200966a1481d0151480d0406410005c2c0090b02d866107a03030b0b55152052040d03108645000006060200b0941c0500038268809802000841d0048c0390441240c0314810620003e4100c00002800d07004941c0300344042481c00802c000204600d00d00d240e03016a0381d80701e40081c1e00c009080e11715480d480400c80c0b00542e0885840310090400a421401407a180201c907001d5034040d44010842c42805030001d0000d0030202070903003d0603c59103409008800b04058404d01581050302d02601c000c42c15a480c03640000f12681601c025480302468401031b00104402500100d50348200a010020414044030180030040707043d4548501c0c2e00c0e102425541030242c2d01402c404143d9880c60300709220f10400c81488200c0c014501980d800310b00d0f401040031500300b0746026840090b200c0044100e42854055600c4d4507115003100604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 489509739 1250 489508489 489508493
    0x1b010e0703020d0809040501180b0319080a090314010603030311031e0603070b030f07030e0601060c0b04060b130b010e010f0c11040e060906010509010f030201050a080606130e061309 80
    0x54880c40d0200911440c1c107000c200d014002e03140c3c1a544a448064020805540c41301426407070003483c2c09050300400d00707005014080b030130302181c3c1c030760009902c6412aa1072010341d07407443c01981110040d10104000f052001010500d9610703035070500c100b44400013900505509005081c0c0c0d80070072995030140000c02c144105c114440c26208801200c02c09901c54a45407800000d040969a50012070204408801d21000001e58080705021740d040c0e8504004103000040c10329202c080034421741020a0f03c051408000c00d1700040f809038005c2c4111742c000380481802c80044c1c41200d1954440c1c0149640b0107251074556000000d0440c841002d0034802910f0b01c070307540700400120340103800410101c2c0401b000f106548540c1c0103a0441890303070041c5e8805142984a0954450003403142a1069243d140000380c4541a0195002070340d8041c1c1d00d0701e140400340300060740e48110162485030480810020b1009030014516400c001d4001d10082c21640d081900800450a0b844804100c2041c80e004510f80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 489510989 1250 489509739 489509743
    0x60f0a0311090c21040212030c151807030813050d050c12011505011b1218120201200c0a08010f053702040f0e16020c0f1c15021b010e 59
    0x61070130070400e5030030311035903461000c51302e400d900aa1070b0700280300c04104401c14800200348842c8400c0388a0056506545070b014140d5443c004404080304c5030070105050011500c0c2074001d00c03038480300060031803400b9510b0f00400e04071099003609944a40200050311114541009000500f02070407000303010842900d0502c018045144c0b14441c1481600c55103941040c2d0624002e070350f401d0b00000041154260200701a00d400314010422611814020020422a03140ca80102c146c030340607500c0c001c1800b0308028158207400c003201a1540380c030500c10000210340d01ea041038000741401200118040d0301025200003070b1080030700f4555034105030031640701d500004448072a00d80b100b001110034880e8284040c1c0c0d00207208070f0b008004807031200c00e40444c03850055030302140100e01d0180c00a80d06420010200d03140c084c584000da034040806420030b03001d490080300c800e1900300c40c10050101070b0500d503101c150110300220003c6034a500401d841d2912046400520482d070b00d601700a001011259a00507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 489512239 1250 489510989 489511027
    0x80a18030812241003060b040b0903070608040305040905090a0c0b0d0b03061911040e070c12022a1305160801080d0926100605190b090405060f0a0311090c 68
    0x68050703881c0c104071604d200c0c801c0c1c00c840e0081c10007980050351691154600c80b815400301034918002e02c038141000509601c600103c900c107641540d1014207217401c06600001405014240221910582d251140030451900540004195036210941d4690800c503596081d1209000c8040c4650031030401c1240004162302e0b41e486010404e20b0000b100c8040101100d05402144c00c819041008201003050321030300000340e041450302401c0b0710081c1400d110000c0b65240d1034042642040c502d040458405140b5800e000116500000c02c0ba050f86040003c0350300440b0742c12a203071141040694503d84425401159242c050b1544001410303070100d0168000d08404441e04c5018456290000b800810000d0b80f00040703100508041900e4124101e000d006001d4032a50041340d01c200401110b01080e103124803c402d0440c0d00c4050030b2403c1c040c3c1a0b080000502d0024070a94124011500c61385d40d550750064060090f52040e003010701c0c3c211810342400b107000e500030300c0d6000080c0c00308010150102c44031079407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 489513489 1250 489512239 489512311
    0xb0a0602031213051605182401030b100302040312140a0f140a0f090b0a020a0308040204060308030c04060e040209130b03070b03011706160c080a18030812 68
    0x1100b030740d0f100e03a200c940305080b009601800318050344000f02d01488a000e4058101c0e081242e031a01c486400f040c0b083c1c0c2c0c0b2a0151003059035880880010180b403855140c00c1903c0d07e105050028481080401240195003141c4040e00043e82c0080c040c000c122138030501582e000f0031443c002c809081e401340441542d102d0004a1000e21001c0300300100003c1c401c1d4a2001e0410b48801320544480319080f02600b205407810140c0082000100e0101e25582000c00751007620798503074020001110395403402e980340310001d842641c1090300c030302001c0089000d0000540c0944011150b01e503a0718586071004102c010320781e408520847c01000141c402c2c0d521050042030b542c000e10000200e40b480300000a107802c0003540900d05182c07001c0000074403107981804041d50b280c00c2030166003696948030348558098003086440030100364070b08200808a80900060400000c0d207013490303108040701c101280303041c00c1190300071180e280d8000b482c886c1007048442c02d160840c0300d40320f40a030246000c04000c00103115090701 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 489514739 1250 489513489 489513517
    0x80d270203120d1104030320150105100e0306130201091406030f270606010e03030f0d0507020a05070b040302041a030c010e0112020310030308010509010b030c09060c010f0f0b0a060203 81
    0xe180401d005036481300c0780d800710441405566a07580e140142c000729550281440d02903842080d81c00388030010a50254560108100d001c680c4c0c03c1c80200801c490b0801c1c001c40810005c020780c0400d40d2001c0044034001e0b8403c500254403c0306910004003a40225007001d20131101d12560110240c40700c01c03c5d030b50040c10341000922581d03580305c420462010001e1907a122424030400c0e16159000205880c0c0c051042079840c11a60220a800c0c1b6a41c1d01c21b400102d0f03545401003044802580403588001c0d0007402d6481075528034003e0740c6810745822030030b4115001c0954001010011840c1921a085075452004003403200e0103000e0300000d454034101a00141440301c400303843c01c09a17104607000008800640350854070b030300f40340d03123075040741100350100300c0209070080e00109a03490082c84032412140340100c6c1500c1c41d41c2d2140c13113213955004141c9068012400b03000030314642c9028004c142c1c1d03110301e446001620b02e100c1d0003800240e400c9018441c2c002ca43c0c0078002d00900f680441280e2034143c140740 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 489515989 1250 489514739 489514747
    0x1e030a060f150f0c0209130507210602090102010b10121803020307020103050c090a0f0e1806011a0d06030b060a1e0614071703190b010e100903080d27020312 69
    0x40d00307480d50300013450000c0d80040f0110801c468044181110301540d4019421290660f4440401643da1843c44901c0c1268000041002000494a8004002d034641c113100114203400c00c1ca01041034442800102c0006c41c04e0594403168420003031060020002071000d2680e0001e11686004c0c0d22840340c4800a4100364407080055010b0b0202c104407000e14001500115545a4030382100c101c203010750042c401d0070a008004141050003000b0301140b101ca405d40031b003402c1d9180c814002240a0b0402d2803c00d480014801640078844600c50b000055009810007000d03441d024040143c4940690000c10710286140084194080c41c011850107648460500000b00e240c0c141030442c1a000e8860010142c0300700341409044100981c02031400745400f580c036005c1d0101a0050f5000b62003546071102d00040f00c01d0500d0035071b4900340c42c0c05c106010701c03420403080c107640765111503100354841d003960300311300d51039482d000c03018440d10741c5040300d048460320403202d03e1030b035a8002521846a480b5107011000c02007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 489517239 1250 489515989 489516017
    0x1030b0a150512160e0c090d03020712030c022107150903050f0a120e130203070c0f03020609070501210b0111010207031701051e0112021e030a060f15 66
    0x40041c4041c0100034814500d28403c500070559501034801c0c002000b4183e80c00024403a10030150303040c080c240001d05142400030450a0002c1c01140c0300c1d0039821032041c0000028544403500030150004d00950f5021890b01c1240180100724042c3c9884031080024500303020303c41400843c00c242601c1000c440004100b0005078111242c1c4019080a000c5d4058494280c461010000f03c2d0b0000e86d108a81042300b069030101c040c1c0b0a103020b49110358101c50246991404035143da40110b50103001410028000c803c980c41d460120051141c0c118003592041302031280c504410030007000100401d107458101000f03070b0108a001c40341504503840c1056141c01001080340e005030b00582032500c002000715110840707801c0082c000d807071500500040180e00b0b00007007158208140182100c8403050040074403807a0941c0112850144400c2c03c40d08a0390038080e0452a042c00d04c0d03014507100c40489800d48a0038448070755400c40e0319950100042080c4404100845100f00107025001c1c62182040f00900d0984 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 489518489 1250 489517239 489517271
    0x90c040c17090616050c0a030f0306270612050304150207080303090d0f030e031c0b04090c05030c010f02120c030f0c061905130615171c030501030b0a 66
    0xc0c204007810340d401d80382003010603900001c516210b0a40e440005013070511009082e2410700c1100425010350700a0140c181c0820300a92691803040d006d4640011500e903550310001c2c0b489604252000c000d107240c0c80600031402e40e0f0048202511039080c5400b240c145136908d05030b881c8240d202e180d241d00803034200200c10301d0017030240c0001418844140da580c1d00d04102000c0c1c071401e6048902e40441d03620014185868170901c526100850f0000045140a0209906070304491091482c82e2013287c850020400726143d900402c80d80381e00c40c101c0c002c07140b41040205414034560f0402607041003a25281840304680c0040c400480302d41030f0400030703510440100b5607401c5d0f2041002d85107006074002255180104d00040c204c1c49103488803500080b044425900e0002e035242900e00c20b002090011740380020547e00d0740410035402010044d40302995603074820140200480000c034025030409031003000b135001090346040f610741e820b24040180d58116a00d4a5102401401c020b40303803a903c80710f10b20400d1203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 489519739 1250 489518489 489518507
    0x509130e030a090905090c0904110f190e1308040302120a1a0114030d050d020a0c0510230103020d152003010f0b120703150f0902070209010608090c040c 67
    0x4003058075030b0b8400808001d4000200c520030308442520304400641108000b049020829800034546ca5036a111502c503060402400d072359079584480800703d042c845584102c18801c42201c2d1202200105103070000c003441101000b0b24048045003100c11000000780414202e03001d40341d0403148414036041d90040311b441d01c08510401000e5252050007107240c041c01c026054100c034000050842012203401c14507460349165600903000c1642403026007110b81498026103d6250f0f985000c2010030344548a240c6008106070054146c5a601d40004c10225442f141c84012405a1b44841526501d180e0124032503e011a8010303040da035145141400101c100e801454642c8945d4a52000e8501c043c004020190b20138420b405080030000400940051b407941640d100c12001ea4410800d0b82d00c10600350017800c0203400514841a1000c0041610b8041c510040040d02c1e0b04540144c84043c503106000c0c0801068212034280a011000c00c00c1d074040000310f0000c0103000f070310003003040326900d0800e44031018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 489520989 1250 489519739 489519761
    0x1a0f13030b0108060103020a0b0a0206061c06020d02030702061803120a0608030c0c0306070201141801021e09040609060e180f030d0e010b012307080d050703020d0f050106050913 78
    0x71a000000380c0d050000038420b058070300807a01c030141d0b45d54610302071559200c0c0f582c012000d41c1142d40042d0452a04d00035003110205003441c03000e0303064102d44c0c400e001caa010203858103415901206001e07429078100100c1d9031001c01c40030f20710320003103a49044d030b556070103a060a0b00f40326034241d00240919500f41c112000908400c03044030b84510501d82c0c0c00b500c8a0109074528060310600340000d041a00c1409001441144407541101d2a01c800d03031040d10303045010300c00c0c2d900d664080003680038020f202211480074401420200752030b00c49d1700040105807240c0b03500ca129600e0400d070050100c0b0200b03400c0c298000d0510094813004c8640d00c1101cad0708011051381d01c103100303000200d4841040c0343e154001880309220000200315880b01c620054a5040070f2601c80c840140240000e01d40ca021030000030907400307008070905418000726601c9030090303420403500500041d4000c40e80381e440d0240780c0200350024542d0b00017880a581440b20051890140031041841380602030312000c0381d84100d601004141c2c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 489522239 1250 489520989 489521003
    0x30507060c230a081005060405010809151e0105010807082805190608010908040312110a08070203060a06270902040903030519020903030306040914060712061a0f1303 73
    0x1090450b4103400da900b00449a001150f028800541000c078224541000e4900080602d41454280001100c40d4040104610100e2080031818012000f1444105102d40074201c075505c109110070305a940c803400e0691120741407211240c180407405e074110180f16030000c0030000c005074611444a1252410f070740c852011240320f1400040c44110341e42205404a012902c01c8141304250b034070917609080320700044c2d01811407a0140010f01c0028464406001c020f101c500d0900710246503869024100a1510400c888480c000109981142010f0001c1540302d50707151000c020161404003010020b0141c0e0800d140c6400c8181084076003504141d01041d1440c1d0090b00420000300d880c500500201410b54101c5190b43e5035950144004181d402140d540600140c05141540c4810b402e10020784030424003224075a0203580c4003607110004000f440e00c00c4506035142c20b07240c0d006058000803114103822800003030800c0c841d4080d180c8151700455078074818010125503203c40c11018801c802940d81c000800803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 489523489 1250 489522239 489522287
    0xf030507020931020a0e18010509010507260708090f0106120317070905061b0a032a0b131109070c02091303080402090c0d11030f13030507060c 63
    0x243d000c0c4010151100c1c1440c0c0180c4010b071060302100c1d0768246a80003076110003040014440000882c0c54240c204050358140a0b070707070980e00989429901d003101d840340640e54031010400900d9120005400d032020f04002c40ba0040c180d541031a14442e4000d1407003092000000208040c14400c001407001c9411303002c001c20440b629010105400e03040d007003080d800241e2019400c66460a51a0200d01490403512500701c500c0c6040107201280c3c012940b540194417580d100110000424400300b20340ca0310a40c2c2d5a80d0117100043c4001c4940303499100072014107154804400081c9004001c0e58100390008454401900c4038608000341c60301c001c04140e044440801402040e0ba04840000e08070791085542c0e462554888400f6280c040030303070701e0240004010402090240c14404030007030f000103000004500d000703a800300141c1501c100c880301e8411407000100f0815541100401103400040341d060580c6040c040d030301e0040207409480c0b0b010307040a80e078081c03c1140700c3c00303a4501c280300325a1000703482e11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 489524739 1250 489523489 489523501
    0x1803070308100614160303140115081f05130e0d02070e0c12061905062d04030b0c03070c0c0603020408061006050d020a03110304050106030512030403020601030f0305070209 76
    0x1c0c1d518162007241d08810140e0001c15901d01801c8400050507841101e1402c1a0040ca05007000c0f9640301800d60a06907100e0804a0704554240010302070181c000900d0301e188a0f102c4000e0038440d00811800c6049080e0544418040110703107040211001103a098850740b100000302d00003090703c881c01d90014413660407404e20240d00441c4440444000310040d04055030f6102e001d00c00d070b00c030b0110701e8810407101c4000a078040c585040800000c0040c0113185513900e880e030000c43c0259010700103043d01500c0056003102006140b5250700c0c0c40d0744810140500381072540d40d40e0000748801030b01c000340e180c1c004070014070840c1c4a1080701b2115038100421300a00360303403030300050300035441406580c3c0341c0d000e28000500308c00300450f452804c59030156145c1c0e20307244207901602c00a4200c0e040e41410035469040d0b02440060340805503010303030300450000503098075500e080b0b85413001d100e40300f0102a1040c002c000209401144150440e50010301c0d1903c0382d92546012105072080701d0009501c501f146d030510030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 489525989 1250 489524739 489524747
    0xc0903020306090d020a080a0302070b0c030916080d05070807080301030308040213050907061d040203010f1e0f14011b120305060a120602090f03030d0e010b010302180918030703 78
    0x1100c0c0281c059892035126018403d03203c88550010300051380c044814180040d080500910200456141c01400c04003559220007000c00c0540b00c4605000001c0305010b00d4201c1804841c440c1d84110711030414061400994940350a241c070b83c003c00340080400ea030f40c14131a40d04100da0240341e104030307441c0c1e980d0307181c0c60040d00e18035050b902a405511800302c8055170b0701b00341c03007414020750700c0b04018410240341910803100f0803040303408180212070020466a6684484c0059400307002c0038505440c070b5070305107020190042d40410540d204002c501c0c0b41000b4405401c3c0070341c01170350000642c5000041c04040140d032426040000440513000c003455000038401c030321034801c0921159a9060190f03845080070013640300828000c1c02c803031000201d400b07000129950b0040c507034990080e0030b840302128940b0000c0d0841d0080510341c00502d494910103038410b9428880e07000d010100f424110f0034180081d080f581c0c02040042440e005421326004215010900035040308954003200442e50b4489403803030020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 489527239 1250 489525989 489526007
    0x302060c01200a082806031401050906060d2607030315060e1003091703010303120b040204030c030201080402030a021f08010909030e010f0509090c1b01090b1f05040c 73
    0x140b04049000e4030118028800b4100c626920f11583d404045840e6000304295984d95401d8542d4081007540022a00303010601031030004502600c03104200417640454142980c500801078803098200404110b029510340106940300b9410500d50342101d402d4850b5164800710b407140341d0340341c0300300403805500b0541c0c103400c00d4488a01e40340c040c4000a690b8041a00d144884003006640405114005122300c2d2299200c01407041c05150208100507140015042503070003a0010360005091032401c042c10348840c01b030526040002e9408500c0c0c9480e44d19a0f00b10020a808000c2c10010010040740540d60300708240001c1c1c039001426004006450150404104086512000410004000080d10a44070f200d140281070300f5480e08200c0822001c01100c006030320704156028040c0c24170042246445020100b0301c030b1000301c0001941d851041081502980300851a4119681442103043c00100301445c6070b908828034000f00c600408040490f0003140a40b40c2010341c2151400803601c0c01035520134801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 489528489 1250 489527239 489527261
    0x20c070f080d0c0b0a0f0b0a0b03060907020d0e0603090c090a020409061d040f0c0305010f0204030c05030c100e060913020315060f03041101030b12010c14040602070b0304020a0302060c01 82
    0xd6001a4001c1030a0b143d44011240203442400303510000348041e101600900314403600d000c00040c45001da100041d80807103041d000b4080221000c0104005418850a80781d0406054002454804055031000740301200400440380552804000300300600700401450300710750402803e403c800e19099501d103000f90810710923100024142440010200249039000e004a29280429500d07517071562030321520741031061011140c4940380240000402c4081c403446403503401041015076580d245007032021a15407580c01c101e101e60400004282d03942d483d629004001d00050800c19091b0350038000040060040c192070310741010f030a4460f0204142e495000314400d02816034806009884d83d001d200d4980203030300390b158040310108003242c0420790074840700e9900c038414980403130703140300b9900460604083c2140c0203040342c1d10b03500204040c980008110905417004c3c03858908040c5800c5000350381c0d142c1c520454803545000000305081d900c94403080340180d0303000750103250350325072000d40d03076000300725000107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 489529739 1250 489528489 489528493
    0x2060d14072003090d1704170705040b180709180603050d030509071707091415010e010504060e030309190602010c0504050105041e0312260103031b0303020c070f08 72
    0x19030040ca04940394120051190310000f1810081240184244241041015a00350841c040c20b01d518241250041002d440c444511000c401030480080380742000e243c010078415401c100212903180c951241031144a0250260f11040d9250340e507040c0d0344007820b03410000b2042115020107644014a40140003200d11036003c0b03804400d00307150101c088071002d031074015150700444002c04c4061520304100110a00e400d0596142c955155200c10171244c03210a0540b500034101c04100c3c41480610012442d0a020f081000c98034014070002800c0b0310035070145100344110080080b406440c20410707221900ca01500100c220005140c0080b50380d4000e1046800540c02c10200b400e00700d11070401d5074100c8006846403824103081451a00d070243c05d0100300c4003015102c800020101b00080e00000f0010340c0c603240c0c1c00c0c0303001510a00c8006141e1441454820f004280c0042000030b43c4021908120b041c111100d6031850030700c1c6801c8000c0d110f460380c480f8040c4225400895061a0710240c0c008032000701e41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 489530989 1250 489529739 489529757
    0xc0309020901050406050105121807060903030e010f080604021312140f03040f03060e010b0312180619260412090e041101030b121f050f011404020702060d1407 70
    0x1300b0082d2945402076900040b01400341c4c4000300c4255a031642c02544244004c01c2c4009542070651500107658404070009080b00c03070400c00d040d0051404d121404080c681841400c0b2401c0011b041e68030041c0000d801603900060000c051040d840c490300c007804440800903078000b102c0c14900340c0200014101c9005000f558146842d011000040720200d400100010001e140342d9181c0c4001400d540c401c0320300742d5484007150700003940e003889007254a01c9043d41031038460411405560b4190710800d0f946002e0b101c01c00103803c40c41c46860b05c000040040385007425820301c2101d01030918002803070303807683d44c0044103090008000d900b240d6016000c807941c3d105219160744460000b0b492a081d540942116080107980c9a00d5220384c000072003810000d80b09030114421101402e00c1e1180c20000c00442d044000c4509074012018055107401c54004000b681752035040c40c041c03c0f441043c00c00481d1003290300146c1c41d81107469036426100302909071041040040061581c0c418240303c11289000014a07801b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 489532239 1250 489530989 489530999
    0xc0801030b0a0213031e0501060512030f1e0f07050c041406040b0f13020d0e0c01021b150a1709011b08100e0c07030908011406090402130c0309020901 66
    0x1154581280c0d04040410560340303804440703038029440f0740c144900d1250020350100225480030480c520014a0441440c01c1104c0390621500b1504290411440360594200c2c45100303800000a84100d542240c0b042a40d0304030019610702c2d1941111a152140d20001c29002901c0c000e002c00380510a0040c815906c540c0c0c03002d42000201c620080303a0b05460894080441c0c3e03d0304241e03002212159025001c14000240700000030403006588200b10b100940000e41641d800000380611001c00e02c0765801801d411300f400300044c1d1641c41e280c42c1124007813840e0500c0310103030740d0310420b03e5402c00512a1847d030714a0017001c02803c1c0303003030515265204410f8101007070325000148141c419280c180440740c0d01712521200100c5602d040a081100504061140820b030391803401c84150081300003c040c0c50352002903140280001e2030070303442640603902d072400d2810499240c0a0003540130b0710480b44900300740d441e0703c0060240b054500b5034a62051410b034501d403c1503015031001d86924002c88204049a913030f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 489533489 1250 489532239 489532247
    0x15180501050d0804090218040f060302030c0f09071d19260601051212040915230607030c0b0405070519140d0c12030e0a0803090a031104150b0d0c 64
    0x50b84020102c0344104000c209544c51030f030180460340300301414010b450720034000050581c0c00007030021444e542c2c1e80d041001140340400c00c41022482c00d0707488410344101100080c100850007401309052002c45280401031040042d444c1c600380301e00900355080448581400c05c003105d440e001c0d290f03070480929050501c3c4800d0280d680400c00d1000020401c0d6800c11040c414006144d0314096814400c4051010281403020b0150025003100e03030300025910b81030040001c1c0c91120303a01003540040804040d00c824503201a0906100101750382166072038400c1d1170f0807140640e40c4840585810304000034007080160100d145000c65008072100360103084115038040c01910f1a02c90b0000c1c001c07514141c40b03160700f401204100c0e014010504c802d4603980d5680580c41032800d40d03074220002000320200484500d44000d481000d0b041c202c0c015824104408080b8516a5260101800080caa40040b2030290b0755a0020446021a41d56022050b81d8517258804540c0209091642050510034004d001900c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 489534739 1250 489533489 489533509
    0x30f0f06011406180103020c0309122b0804061a1003290f0d030302071b060212090f010809030d0f020403140a030c0f081308060601170c070b0a1518050105 68
    0x491381c0741e0402c80c01003005500a6110004803602c0d40414010014240e8a5007003203001c0343d0406002e01a4802c0013071841c1c0d0f01540c0940d1400c041b4050410041d034440c0c3c4100b103030f03a100b0713030040300014025108402c006100350b06034034042d40410105150006c1940c1508150303c00c0c50301420104a00365202d201d83e2805002e145020b8000b084008420302c140750500c0d242c40c1042c001c0c1401403800c2c80c1502c0e81980c00140c10329020049480c203208101c000d50421141140340c115402c07650429101e20000780280f000303215013078104400c01011408200c03007030007103480d030101e421802c2103004003003809080a504540720a4800058181191007107840c04246d280b40c295141e9240070310703c0019034403034180071030050098480b05403e12048034400030302c1c4c0490380a4001c10b00185031519100f80010000d0281c44401c0c280c03020007105010801960009840c003a581c025440055a0740c0e00e8900802046a030010018002d0514800a103646030544041e52151080505000581e00da106020100700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 489535989 1250 489534739 489534757
    0x1324030c0f052b020a080915010e010302040903031407090303020c0d0c06050726030a0e010902060901050a0302160803040c1a160807021005031e0c0304060b030f0f06011406 76
    0x210070004940c0d00c0c40c1e0081010f590800340320b0721003000b849501e1a08120f030000c40e075120104014405115a13040101b0460008000811600d40320350f0506041602001e41888024001d46e01c0c1c824980425002c1d800c2a42c40305060b00d1f01c00054031f410800145041e103580700c00e40140c001d241e2680e0041c2881d0440403007407a005000704000c40d2a003003080b0354a9100e6001030b902c0d940030520204400e24030f0320b017444400352000080da0b26801e104e00c01d14102c1d0004001508107a1401d1580801a1584000c0d5030403c00c1c00d0809036114400440140e001c0d01c81c290401c04102140c050440421040360065801036009140a206894403549110a043c6c4680d00720b0345c0b2032109000800101400c0c0170740d0307092644160601c1d410900c0d07560103d088458260a8003011510200401101600c441500c00c20355004030b5100700c0c07605010744684071078800500080c1149846170781c0084103860030000f5940000304201128440250002c005031a850280510840c1260344000625185442d5080d01ca40071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 489537239 1250 489535989 489535997
    0x101a130303080c040305070828051c090306060906080c0303120c210f010501020c0d150506040e030a020303060102070e040228080703080c010528021324030c0f 70
    0x50640c1c4042c0d903101001010341d5200f050130040400003a0041c03106000401c42d0740018040c00d403071015505607034445807040e09034680090410ba0081400015120300303010704481169060142c80340d04881d0300c1000c1e0000b41c40541001c42c0000e851301c1c5035012030100d0f40500c0668a81090500404d61244030b40e000820f00400208041207506800e80300034100c200840034202ca14200d216000450b02d00112400c0c1e08800b482001045556014404c0121203142141e07251501280d503a15500381d070803540c01a4080303555602c0010382d60307200c0d0b600c0070040c06c1151048030388414402d00000e40d0b0b0303442250214014001d242c0700160b00b00100c2d040c0d500842e402002c4000342c4585050070b01c0c2040e082c0704504080503540c0c00000b6000702c00e11500300a507010354500303a42e44098200741400c2d504040d1548440768501d07040705010741484001c00c800c1c109034110240e80c5501c101150303c010f004640060049236554240b42c456607280d41046035036a0010f440c140a0091140713801d0b1661051034a0610102e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 489538489 1250 489537239 489537277
    0x105040b03060f0606090405090d08070201020c100e120403080414040b150901020129041a0607080d090606090504060c020106081207021f0302071416091a09101a 71
    0x40c0c80d401c100350b0312513006445035042c100c03010002400d6841c16078484085400c0306c00c120328103561045c41190320079000e000032762401c2820700d101075452030440b1203100c45940d100070420029906214034440300c025090a10707151622030600c2c0e4101d9201340700d210010500030b8501d24403400c2074064042400e0006041c020311034007100c821070842d444002068115543d402c2011080c88104103a50311600b0b80c0e680c507c503591340d0341040c00215502807950341c040c000603104003269a500c18007102d0945610141e410b0b20b440644003104064030400000074899424100089090318140d40f029100710b01a20041c8190300307054106900301e802500420309250040100c20301041c04d41c1c03000304081880076148260900904044100c0030901248000020307800040120030b0207003007604100c560143c1005480c80103108039103c01504040d1107002400d035115844244a004d140750426985400035110394013601d06920b2410300800380e4064008401a006500c6120060700e00946407403080c48580c402c40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 489539739 1250 489538489 489538501
    0x916050a150e0306010306020913050f04230f0105040606140d08090a030803090d0e1002030412030519020c030120070f05030702060c0601140108090618010e01021c050105040b0306 79
    0x76951501d103600c1484010340002e0000e4030b0421002d402940541e00c0161540081400c0002d40e040d2480300040080c144414451440041a41c3c04d4100307500c4103402000205a80c00d030302c20000000302940081c091000c411a00d4601074103c944198441d4070104811915558880740a644030b9040d2500611301c03009107400100108000e000302c490040107000d81a917650344108403035108403081112600844074620106801c06003248100c002206c48400305032032442d00035568021449590701121107200d0701e50a00d4041c60031103000c2c60300f450f10b68955500008001e5924200514194080c4d840c00e10001340c00014030214459aa02c0c050045140c0010364440c011800c20403841a919408200a02d030010794921000381800003811002d0222980760003180351007203082c3c4812906120b20402040840a40410102d034803031a64000d141e40764071a215a07500500d00880300111760342c40015020140e4140c82c984502441410005101d00da03203070018030064903014038100b6096403120000c211 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 489540989 1250 489539739 489539759
    0x60806010e0915040213020403030504030c050f15030a06172506050a050c03120f09010b04060b0f03041b08010e06010b0c0a080a0c0c030f050f06070207060f050f0309060916050a 78
    0x113003040c001003c0e6120762180c0b03034284c000ca034444d034401c40206200040810402c070030b041802009140c101c400c401480d210a011070303004034074044500c2e900403001000440d103d5960340058080d0801a0324507480300d58402071b5540c0e03211182c080000081d030511030294a052440c140c0b500b622110344c0c0f5141000c0b440c103800d5803150050b2100001600051055001d0b03448000e20310b42c81480000310b00a40d604204912500b11295011828082d50801c2005c0c4080c025030011a1441100e00034019501c0c1d03a01d0507d80142003014000541c503200800c07000406000540040442c400030105941070f599031200d04031160300c6018514000c540081035000301207030700740024110011032818042c0e144800e55a8030418010340790070071a40580242c40080c20300c0300c20006428603809003402440241007141000e035032204103102e1502040308031502d401e020342c8a0740559014030340c2032070f0003030700c900784500b400391111422541594188549800f20072070554042c120360848030082c0029000b10b08102440b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 489542239 1250 489540989 489540991
    0xf05060c0a0503030c0406090e011d0a0e0607030c110705090403030c051207020d0f03330522050c0f0a03020901030e03070b0601020d051c270501060806010e0915 71
    0x415a0058807030020110740180025071060034070700328041c1d541d41003c2c030107010042c1540000403001401c03c0181704d00c821542c100281420440108086542c071705c50144003405801055035150b000b04010700120b40c1d0950400002401b650f100c2400c21030107152244d948010500c502a07225000348041000300340a0341c800e040c05502c0380751007403821031000213100006c0350030f8070b500005900c101000c400d0668043d810031082045480c013440010109107000d445049000c0244514207038803140c1b8a1000c840800c1003000f0b243c06000102003d032808030386c103211441c0407041898a410500022f0303248207141d00701c8004000b210020383c100484060120f0003500301c213950905040d23071070f0400c2002010410191400b14420001601546800f6000a00b840d00d9045240b0078000c0600043e0f66030149642c01d0b000c440200000081e0603124041c0e0010302e9009140a50450780da94150b400c1480f00641000050700c0f4048221100e0741d913505c2840200e02d0040b14036602542240f8400f81030f50b50240022 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 489543489 1250 489542239 489542257
    0x60e120304140f0a060e090109140613290a080d0f081509250518060d0209061306021207020108070c1a150102010f060b0307081f0e0403030509070f0506 67
    0x1010b808850400890203840840c0c000d05c0108902140d02030280c98454009405405140c20074440c20110b03064401c168030300070307140c1c92207050841400c00030645aa80f0024440d240c08400641b00c0e81d0722150025803244808020340600740c1d03c2c801045110000031002c01480290f50361001e0342c01044411602100d0107010300d15514a10305000400341e031207010b6240102c400e0b0000a00c1120141020300d40d14090014520901c0030500c02102100380a407410b500721401a19440e039110340ea4807507207000b4420894002e03802000800c0514401c030a0016400c1681c096408546d00582d02c20341c01941801444402400100603900055246104418050340385228030303140c0e41d02516080320032200c135508880d21181e484028903819903540c0c2c2401480340e20607562000700911814810b00344160310005014000384407460000c40e1880c0c5108038103401420300c41c1098031426172203181d291040d107019903040d03000038100400701d6a0001c010840c01c08540381e400702e60454900d03280511203603030400c00032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 489544739 1250 489543489 489543499
    0x10203010b041e180c021603020f040e030c0f0d120902240903150a060608040c031103030d1515030213090b06071401050103020306130809151b0601060e12030414 71
    0x501090008013898115004942c00300c0c4051906800034505030350704100001001c1481c008102503180c400da118101c41d02541c1c00715001e00000e00c501d10b54440d0300004034107845090141c030701e4050b01181010112409036926000c26950110a800b5103940b590040e500c218940c05e00341c42110b898850504001c815014582025180c40010382804410301d0f1090500007030a003003140d00301c0c0c0c5120b128058030071030401c0041d90816450700c1c0415a003170b00008210860f820340302185564208241c46059804500c2032198040f4000603090348207a512810070542c1c0d0260810a1403030180c0240c0b0104041a01c0500b10149043e0600780a01012510550050b000700406008107294407a44c076000e1f25001e00118040d4998814140303400700c002d0007988c80b001c45800560001310240b04440c054201120082e09030440034020003194400d000c941042c03088c1089186031a40070124005040351410744499049203618010312038808003070403104503160020401809125005600314110303a9020f05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 489545989 1250 489544739 489544799
    0x405120d2c0402070f020319020405060409031d03150901061404020304050a030c020616050a120e181b1b010509030a27150903140c09130f080316090503010203010b04 73
    0x10a090a6005599840c00708c01e01220000354101405229048501030394200800c019544000300108540d0700c6140e8554919030000225941c06c10003c00a420041031034901d1381002400e603802072281e4070442254150107020b29020b440c051080d00d00c55900900540280e07502603800300c915207416401240c0c800320078000114104a0440705040c218887c00040040d03070344500f046522120b541858004000c24001418a10344075100003c100400103d243e000325190106a5819003140300800b00d200d102c041415030003411056002e074079440003040200080c0d110040d019843e4492a482507002c80c440c154058140c8041000000c0028003410480c000c032074171404590251400c4600030790000d0365050302801880344244020135441c0940004290642140c0d010414008008085141c0d40840705a03041c00e002003030b040386040b1035003d8541e030750f60b18141c8140746034031007001103500c0092244900403c840c01c05208490580e80b012a07200e04051529660030310030010070f00c904c1365500b1146 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 489547239 1250 489545989 489545993
    0x101514091807140310060b160f02030d03051e0c0a0e01020c04020c150711150603010e0708010e10060806010515070b0403022410090507050405120d2c0402070f 70
    0x408450701a080d92041004083e480c9400c0624107400c00c60400306480c0b419800f08034201c1c20a00300c492090002e41e100c00c031030405040840c480423803c107000e074140c01103890000c055945036018511034002c5241c0341850503504440080017141c12a034001d249141000350007259801000c1c1c400c1030703110510480386101300380000302d01640c1000780440076903441000008115000c0c0070078554440640e03c0c01c1003a007180003100f42c0c0d03940b094038401c01c07070500c0c80300111b11b29480c2904403402d0140302000700c400c902c0d911040b00c0c3c02400d040000070301e180554980802c8000c400d00130041182c01d088010142c603424a010042e052628985480305100c0800070900043c80304022588603d0082d00074010f40c060640440303600e100c4404c0200001015002040100d5200310100c0c030a90b14640e0300001c0700ea4801c50103940038031441d0096944030914801c0c903000d2a40c0003540e510b50160f20b07070b61200c180383c00d1065003080b00360790300381c5030000c04000d1420000e904055014014050040d6034840000342c0316 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 489548489 1250 489547239 489547243
    0x10030e01091e0311030304080d05062106060418051c0c120809071d0f0705221706070818160e0403031d100b06040b0a021015140918 58
    0x1000410100b680d90b08402c00038550080341003650f140360a0f02451552415569456481c0300d41d00c60450b00a50b00c6020810503142d1400c1c40e140350048618011104400d01d0655035503040890342d40303203d10b0030f1403e0a2481c0c96001c44045505500c08020000094040b030a0b40200b0104105102048100c1c044840410034603101c0d03000b821010344518140f1300340b680070b26003030121a4001e10901c801d107808420318280344401e03280e803103102030001040b90346074400100c420b441403124940c2454a51301c00b140d418a506441682200e0b211110a509052842c1640c1d8540c001100c034074001c1000440050900c022261010306d440a40c00182c90008001403205d00b00003e41d070b041404422841400c100c100354061188001c502541941d444040d0080148070355107046691100c03003015121002661991610004d907000b900718122042d031101c4c01140025940c4c8010034101c2481e074288112105103c2d103030000d00c001d031011403000390058244c88007800345002c1c01821452042d41480020807180d001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 489549739 1250 489548489 489548513
    0x1b05190c030c0e0f040b0601090b0f12100f03031d06131403010e0601050409030201020d020a0804300c020105070c030c0f0f151b051b0a0b070210030e0109 68
    0xc03540025800c14150704240b02d8048642e000801a100f0300814007900302d9400c5440c0354040d030702c181500e030240d4504c00100c41ea05415071081d51400004503076680c2c034900c0c0f1400303010800e41e481d4a441c0940e44428528400844038841d0403a023500030541800420f1003070700418040b81c1003072500541060320710003155040d03204e881300800445003c0000e0043c0890f004280c4004d0078200c0c000d0003142d0700510180c0d01e07168188500d42c030650303075908544201030007901510b1401d601283d0454a51400c128041c1140408407000c031240b05006a000c00c108a10181e11045404103082c8a0f10b41c81c115001542c05c0c5070100b509074180301e01880040006450002c032003014500c18001c40d40111b2030251440030784505900712403001c07110010107000102030303200d41540c01030107840c0c40c990b44e42480404155a04502c80054004d0191640302c00a00c0c030084200d640d0700030251140c00c101959801c0030030040c010520001d40c8405121146c1100a02c01c0e040101c44c0e50700c000000411030050b540f42014151 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 489550989 1250 489549739 489549743
    0x1b09150c1509010b0103050c1c0518100b030607111b181e0c040e1302010507051618020901020a020d1b1d28020a032009041505011b0519 60
    0x9100c00c0804010350381401840c0e0408101c0741e9007410306603040c1c0d241138491040d03030a1132070840c0da03000040c18041140c0e00c042c42020bc2d220540789004582c0314400b01070072540c1d070054000d00c81e81020445143c8205080d84d081d003a080d010f02811004a00d82854903082c5160780e503480850600302c1800700c1c100804541c01602e0301170011302c400b0102c12030344c3c03c180e4005002500290040c0402c100480c0100d0010354040b411190000400c1250310040c0c1d030f9070042602c0900325105100c4050308218030a44c281c02a2020266910880d406444c4039406070300c01c0343c080d40e005070890102c0381c1c010700f448081054204e00c5400000480254403100050b141075641c130418000d03a44090741440101e1400c1059041200c2030810402c03c00c14500441080303e441503503170303000f0f40d0000e2110b01c2248a903004c6d03030444c0e040002c25040740014140748aa41d4006141c118401d900c1e00c010228850141d42c1d0090803508182c4565a00c0802588004c00c9544050401d603514012100c46c606034640703003200840d03d01c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 489552239 1250 489550989 489550991
    0x9031b22050907050105030910110c0a1b0e070f0503061f0909060f030c0b0d180804180c09060e0d020d0c2408040b07020c090108061b09150c150901 65
    0x4640891541c0c0f5048070340d8880c9060090401c14030282010200d0407066403041c50700003040710a00c0d20700400ea1841041040072490080080000401030310500705c3d81c000c1c40f84c82141c071116131540ca400480c07480c25038441000c12418032580302d082c6e0044000d903502c600700070030070007415105012031202000046161000298100014030940c08540f0456001d8070712200300601da030f42980c2d41e03454441c00e0ed000d01c800d80403001c100140c1c1003046400801403644c0c4c40d84403400c4c40f081d0389040b400d41d0b046401a1040b403656010005007203640ca100e18406402c01e9075440c81098944102030703a151a4221f500d40d04103c0076003000d0050303240c03003100e469454401c4e605607006a280814030340408589480358551049141a0100300a84c400d80040d0003607003100760383c0c0c6203484081059151001d1718001c943c008020600029561f078011400900c54025041c010946c0d02c0c400c1a011303410722501c80d683e41e01c1f1420500711202c458810b4003811900c0c1002c1c04440050303140144520022000302c032818926 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 489553489 1250 489552239 489552241
    0x525050c100203190902060901051606090b010509060f0108040201080603070f0803070c05010207030b010311040209090708250207030f0311250501080408120613090804090b0609031b2205 82
    0x1c071081c0d0951031350890039481c04019141d025400143c0c248100c0c0981c40c10408081840740340842c800c4000b140040d8045401c1100c50709038640115466006d03c100b40c460242e20740081c0c1141860f801c003205003c4165078030380e0513603625801504c480c90060001c80c0c16100301c000200d4072000f482c8640700a401101c0045031540221300c1d03c1c00203000c5940016045410a113030400c00111341841442c19250300c04d801d074148400100100b0000d0045011040d40701445005100ca116046414140203c0002d0700c913544050540c1203201c0240c007248409001a444510708001182c0030701c0701820600c2c402e03d4501889882c0d483d055141c42c80c007074042d1400b24044403520b0761180c9112411001041d003824800d0030b91500382c440181900500480c08a40c81030800080c1059403401c81f00c41c1c3d01e000d4844100040c11041c1000e8103171382c11034080c98a40781d15021200c485031804009682c1d80b4000200102000003403240a580394501e025440e9802c0306000b400405420041c081090089902604c00103003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 489554739 1250 489553489 489553501
    0x1a0109091a0c090a17101b03050402030102070b010909030801080d0c11061e1903051302010c210c05010b1e01180305101e27030905090a02070203100525050c100203 72
    0x1b4800715560034031045251943c0702d10300140020000040000500700003030a0307030f00c070300100380a4031603144010209501c8400114000d0b02c507610071044030f0300030b5032012141d070b0b00c41c403240d5512000804100b0100ea54001da03140010b071350a05040c9189070180810307081c00041441254090440300ca4911141b1000c5012800400d90384040b550043c900d02d4184880e0401c5240c0f150320103984d91020b4104403060000340103108003101d030440d620043c5003241030314203034020340103014a4800308100c4455003024280e0b10b40b894100d07030314080310356041c1c08081d9a82200006507a01b085012000c0c6c0000300e520400000f00c3c0040c007001c030491912000c046a19401d14200444d8940000741920761140b8040840810040d0b441040f8001306a82100200031066810160f45444041c1e00195001d0000300400ca46400a50050700d4168070075000c0b52100441c061400301035400c1240c5041000d0140421856060316002d203080140500742451450300607201001421700c0c140b08103c1c01184e800005102c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 489555989 1250 489554739 489554743
    0xa050901020f0d091a120108100e0109080a051b0604030e130e0c0402030a060807080d0206092107082a1c09090b0f0d1a0109091a0c090a17 61
    0x40344502031000340a001e4440320b40a4541e1605015003050f1580c04a04103065042030310444186d01002d6814041540e911490342c0d80da0542080b1aa034840c0c20070b4001c020680c814000c03442102e030302c00205401c00300c1c0c4040494031908600d445204a88110000720f084d19410f000082c012406980c501464200700018041d001200000c560507052500e640e001001202280c01c0441c480203c4016035641c581490000240200350012800350140507400a0307001c0d400680080500099000d40f40d580d540d140c0d509449a0020240d035075082c820a450b500c400d5603080007000b030a40705010880c1400a9132840307504d140d0407505450354082014000c20005401000750b441d0405600448100f0890034260080020806104071000e903074541c01d82050b01e94035a80c00801001000c0d2240d0041e82003420082d2002205e040100140394840002040401d002d00904103ca5003010400e001ca41034629140d54403540203000c4000d8103000c1c003c403c0c5541d075800b5950000c0c4031141c0c01001075045c0580341d41c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 489557239 1250 489555989 489556003
    0x30627040317010b03042003121b06190c0507060203041407090c02030d050604091e0308150f0f03071a0c01050a09050a022209061406040e1002130b0a05090102 70
    0x1c81d401e40780b1401002510f0400040b203910030b0788501c014801c0ca4917680c03005080c041440c0c41e550700d80038101516441841c1440941440d0448220b04400740b445400280c2c0c90307a41c01c1e143c440380c0ca1000d06035408245070b1604480300144107441c0491800e80c0e55140d010403a04240c404450301c403824400a440b40404010601c05840d4500c020002911503a10203035580c07103941d41c54484a07031608001540c658a652148403000d4000c20040c404641c4442029908503a210080300440c0c84e107404250301560700c3c443c0840810000d840e000000000004200144540c4101250703d4803400e10049100000050118804181d40c21029100c0540c11030050a4a100410350b4088600c0d003d85400030440019440d8261501030712640e0042d200311001c4024500c0303000c002c007086404c0000d44420400c0740d90104400d4a0b0105000c06161642e401b00000d640b0342040240480d0b1007002d6400010080361b0003010310100000c1d103400b00035580d2a41c1c5016801100d045408120081203101495130180104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 489558489 1250 489557239 489557267
    0x3320408010e0d092c040f03120504020904080f1b0f070b090603012601020315120a020d0b0910090b0901060501140403030507020f03010203150a08030a05040b0306270403 75
    0xa01150100700c4001004100b82d0f1140f41880d1500310f0b0005500c0405d01021034660b40c4554040700d030740c501401c0074035004010210880020311111240800c03174440c1d1090324001c42e80100022020303207079a1180e0b0556000482c110088003410401704100c25542c1c0c206440000643e40541184112084040d081c61803a0340304404101040240d02150317030b5002d0450b41901c0503024010850304040700b462807808400020400251310000901204420000304541141d00c00c0b40c1001203040030752812601c071030036268001e4100340500014000201c440c8601a032000d0b2102c00c0301c007036400750b050010030744079020411384600c1004428000a10002c0c010b6401805003802c1c000304201404110740e032181300303c0c030018042110100b008001c40d41d0300400d0445c0700d24014004d6440f410460341102007203040305801445224480380c0007840e0072010003038a4040529860301800d240c0342c00000d0426038002031104e030740598065070b05690f481d02c0c43d4010750078805e07801d98840c043c0740a19001d0044102c408031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 489559739 1250 489558489 489558493
    0x90601080c030613140604031e0e0306070e1f0314011203051c0f05011401230406140d050c0c01151a071505070c15060e0403320408010e 60
    0x840003050710001882070b000075110704010042c101c1401c1804540c407410385c1c802954003680c0d050100f8103511000740b03030031110140900c40c460020800203480a00c04c0d101c005030945c11800000e404a8061042d052101001520008000b0038000406002d4982d404042001c255201c070f030320500c2445211b0031405040d030344030071f840f4070006a10058541c0c0901507100d004002803080f4520f45100641000c4541280603070140203a50311081940180300d504914a80000c0e00004a9014401030110345603003400d8a010351840c041c14907004440d00d4413a0f12480c0100902003161101c40b28042c4960761140f14203002c010307222590904058251240c0c140710001c9807000c80c038103000b1043c0c514503205410505070511640c0d80c926140805030314a603a41c1c4602e40f10310345420400140d401c40d65003980c1034030070040f04210207500d50711070341219202d025a4409550090010f400280540020103640b088615035500d0b10b003902c1d14006005800d1844150b0003580450308200c2480c003405540c03840895100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 489560989 1250 489559739 489559753
    0x120608061f1508180c0603041104140c0904021303050303070504061d010f03020c0f0a031805040e0c061605070f060e040e1c0e090109061d070f080415090b09060108 72
    0xc0446001904c0100300301e00961010400c140208803c0e00c1c0c81c80e000d000241c0301c0c6842e00300400070703052489615009500f07003c15909543d031030448c29441240c06981003420007400780b061000a400070007074000c030715559100200105108101441c0b0030110b90b626030340e80d50308005c40100341d2410039540994156141005c0c0340c00e82e170013a0007864000000d10300181c0394800c0e41400c91814120440040744d9000d841e01f00000d0540c006007803e150405802401c441d0783d0380310180401c03190100301c0795403030341c002103640d60251401308001d00f003003d408600380c03401003403c0d12106e04012403a0700c40643c0704e688000c1000740341d40284072030800b548101d40800404281d00d00d0151200d069a5600501212003000052503901a50507952120f1018050010390740c0c6980d4900020b0403c0d005a0f403e00200904040b10403554070041e9120b002c0568402004c503000c2c0c0403c2c0c514082c09001114020b6006003040c0150803c4d00c81c060b03a00340200c400d40200c0c1400e0440300e0920b84182c20403c41030b00584 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 489562239 1250 489560989 489561029
    0x23042a0906090b152205130e0c0d0c1e0509010f03030e0409020603070e0a12110f0607030f050f070605042a1a0c070306062c040210120608061f 63
    0x6080d940350744015100505204000170a60700000303910380015521403040c003403d4048444030341c0320303401d00303075444040700c0c0c42c042030400304030612005620003001d14400b010144043c400304080c0244440240c000020403036196000100101c3c801d0b0031002007281465010414940e0004c2c99814480741a901089403040755000303c1c00d14440181f07400c0504c0003000c0402800c3e100c04c29080001d181000302c848100f446442e001d2162030a503050380f84208499005030000d40342000488030016410389030062910800641501c558200c44400c903101003090002d03101042ca14010184240c0c4a0700b0540c0e60466540c000b903d140e00c20300c89911150341c0b0300f04184103035225003100212410140d80019100d429401902d89019040d030401042d40c0c4c180348001800e1000301007545440300c64175022040500040c0c0d02c111141008550103544405510ba4118440d8000d0800c0211340401c0000482c0003622401418600941076801e29200d0040c2c15218103021104c0400c100076107200308425260084070307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 489563489 1250 489562239 489562279
    0x6010e09070c080318060906010e0f100b070c0501030f1e09051924140708090321010501120e03040b091801060903020423042a0906090b 60
    0x100010501819603040071402803030045028000403584034043c81c0d0703285041c01c110380101500c4803000302a48160008990b00000108650341602c1194144c10b08541c0c0705650601c1410380a0480192000a500081898003072680100150b80c062a40d400c03000c0d00d0140018100c03490407040d02c4041d0300d0030b81440c1410080001c1000660004140480c003454a030070f0250804c41c016410b24103407512030903004c040103a1908507000c540da80c4115a800a001c5042100c1038506c0c3c80300c2e1081c1d1808500000d62001d02418880307070010b0000e01102e06180304034000012021034000402e003051100030040200d580e0000200114400400f010301169400094260360307401140114507a01c0400718403181c03103440300c1c0b841c00302d0001e0100341030300030b540d41c4c0034082d02aa516000503401541018880d005070302015a19044050300c0100c040155542c0b80c07140300d1091070000c0d5a009170707107081c0d600c58010703840d00d560032010300505040058140d180810325412500707400f031214064030004060b09070386207031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 489564739 1250 489563489 489563507
    0x1505150616020405061c0c050901060c0803071812050f0106080c13090f021003020903011a01170403120212150904020105030f1504020d090c0806150d080d1e11030601 73
    0x2c1524042201d448400004030400c1c2e501c45082e902c10440b5000c241880a141054000c50b04140c0c3c00400030390300c41000719100c401d05a000740c1080810804540c03410720401501d002400c1d60041030b00200d0310790440100c50030520b1303001e0f00ea1341d0021a0007507007210284901c02c02001000b004192030304207840861403020000c5428100c065440b5090010301c41e10003580303520240d00805210200c64032800c058000d401c6283e005000c0d621f00b905409813510240c43e5040450300503140c5e110070b0440303450400e00c06440100224204241d07020300300c0841801c0d0020340b8600140741007060051601230500c142406901d40141d1040c03203a40c040c080540d800c21300b125005801c10200708007a40e14011003c242c0110076130304039000762000641c8010002240d2040ca000740c801d41c168044160340d6115a907403248161403020701d01500d0700b2000340d103113040303103a284200e40300b90704090404a0000d83d6008680c41c440f80c00da0051001c140d010071007121031140c1c0c21100080d0300042d0450034840c00091254031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 489565989 1250 489564739 489564743
    0x7080115050c01020705120307080109050c1b0115060e030606030304030809091003050d030204140a08120c01060f140120030702010e0105160c170604080d05040c031505150616 77
    0x100000d0b400d0007082d07003074040314030440d00f00c0229220741e40c00b010041d100c0e032300c115030380d40020309503400103d22080c0030b0007420300800f61460081c4c14034009142411804214850800e102e40d66440e1a0103100080c05485008080e2500c66909052291381403500b0f000c0001c000c0d0340300350800c000500000d803008055400c82501550780b02c025540e0716010b900a20070582015140e4407408580301c0031070303a058005000b56082128030200342c032040b2040c420f048606004800c2030340c01030f0854914036902d120140c1200100c0c100040307000c0e2340e07420b5122000185c40e0014894544482c0110b01c0e82d50b0082540034070103505400c1c940560b10108142501e038011900c00904000900081d2101030303208400361080251185980d4040028614055528041600c2201011001000309488510011034103d1049800c040d60b185803400c551848802044010300440701134501500200110711064440c140c010307a003120004590070303c0d14004500d1300700c002949120b16001c02190320850243e00c42204401c2d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 489567239 1250 489565989 489565997
    0xc290315010903050f1b011d012f0c1801120f06141f090b1e1503010602010b0a09050603150405190305130501020a03090e0403020c120109050607080115 67
    0x5045401224201c896030f00143c4a0b1003014004c81c036400303000c604d003c80b41044080c050701c800080401940d21a00f810f030020001c0c01c11403100210355028000828003600d200e003020303819450802000c10b101e200f1541d03850350390744290603120183c240464a41c5c9a0305015003103207030640c0340003007500340d0301e10b61031004041c80c070a01d50305d01c200900741d00301c00480700d100a880890f1740b0700141c400f414042c080159040d01a202d1400180399a81446902d040b800c029001d04241621801c1071284030281020640c0c00c0750400000c1647d0409400281d070207030840d81d002080c1843c809041020b10811030f0030580b142c614000c1846000d90300061030300c01d2410801002c05081d40d071410094148032180c281102e010000d0400c075030801d64080010b10521341502c4a0a65280c0c441c0012070381c03030414880017408644490014071408000c800e200ea402407203481294001200440412805807181080c0d8140c0ea4503401c2c09010440c05010460744011035183c80d1015600d0910b0a85c2108038095040040c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 489568345 1106 489567239 489567271
    0x100506030c0f07050f01060308040608090712030806040b0301060b0c15090a1707081818040b061908030f0712030e121809040c2903 58
    0x62034540c41d403281000419030900320355a11018041e40c0c60301c240d030019500c40030240a1440910320619140c0c0d00c5078603021000d043c42201500191381a00558000c0c040050340c2d10f42c0f44401c0b42c0605d0b01503095125503001c603005040c100c141c00d13095428450301068010201c0c4c0280f66121204046490308105801c0300404000282c0754408650804410300c33010078051425071600306428512907290526540e02e142199103c0e04a49540207203020f0001440c2c6004c04040e009400b20040f030000d00c0c5003640c0c500000d5240140558440d03d81c00b42082c102006052191001e400c405086070707a0754030341d41e0625003c0d410a01c02228882e1111040c064000d110340150750000014000901c007991510b16000211b8106684500302080d0188001c6940c0da5502c45141c0501c3c0074180c3c08040908082d107029401080741c6d011540240020703100c51180390200b003101c1e84510703448068240c1e = true := by decide +kernel

theorem cover : BRFrame.Cov 489388489 489568345 := by
  have h0 := BRFrame.cov_init 489388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 489388489 ≤ n) (h2 : n < 489568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
