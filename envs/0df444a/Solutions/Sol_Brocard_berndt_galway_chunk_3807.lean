-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3807
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:44:32.279474+00:00
-- url     : https://prove2.me/submissions/6c6dbcac-c265-468f-8b3a-60e5dee9ba43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 684532374 ≤ n < 684712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 684533624 1250 684532374 684532397
    0x15030b0a0e0f0304050420040605270d02010509030703150e0d1d241801140c2505090703020c010c0507021f0519020105041a1b0d1119 59
    0x65496002c021181005940284418441442c15600a40070003007031058003819400745025090007a005544a6004214042034a030b01001d003500d03007012008807681140310005410b20004402254007031019040050102d18801750743c500304074200103590440562015410b0280050003e06007810094400e03011320700620b40e00c1801640c2d018102480c14194032090550501800780d292524003440d0799141a0702142c0758003801840041490110105d01420600c541c10000740050320314142400600504000c0300314402004125a0740900d180f001800c10744c41a0411400141c003142c10681e444112081441901c54055008100308607000b8002c1c412111a5542070b60240500400a900420340e40c440e81800c551008910700844e0031400c2c07042c100442024403a9103803045100c1680035079996001d0101b070109022015016403510b504040b030b1481c0c91107514240d95407600340580e000c4008581e00d90350b4540780c1c01c130a4209800c1c62034140c545d16004100c0b401c070035009080b01c0c0481c3c12050b14 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 684534874 1250 684533624 684533651
    0x2091c0c080c032109040f0c020622080705030c120c06160819091205070c0906030f031b02030a060504110102010501080d1107080a0f02120105070e040f15030b0a 71
    0x1038540b038034001006040e0390a941c1400a115403248811075014600411250b0b20580c0c86110740f650141442e0b2001070389409501020b460294049c0007040750b0b075580c401000a104004800c002d48031b0740406015101c40c068904a860350042484801c0d0b5800340b40d00040c1741c00102c00107000c00c0341e031b210210340168a0f0f020b220000c1c000c030000c0d41000a018a400600c40b0b100c8a203c2207400e42c1002000501c480c080d45030591200d0b100d008190016800086074002e000d040b905c000d000d4104280100f1520f413540c2d480410344c40c1c078100024203019594851009140c007a000c1620450b40181c1a14201c0e1200d1510388010081201c044845016040043d40d5a5105218003416600c0160042c586080c2c41181600c0d0388904900c116a039201c4c07a01d000c100b00005012520181c1c1c4201e094080e00c103614030400210001100c64422243c1c0350904000c00079500030880480345d0000c0d10006501403260984401910089a20f01030a501c130510010811082d001e8881c0306a4151200f000f85500d901c0d030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 684536124 1250 684534874 684534883
    0x1f0806062e0309021009260c0d051f0b03031912051f080129060f0d0218030a030906030b120d0f08060402070c031e050d0203070507050907020a060e0102091c0c08 71
    0x35444040950351101b001f092030740340d0b604600e824050210703000860a0030004560010080c81250700350491a4078000c0022940304080d03048407020414418805c1e2200441e94a000742d40c15040324070281c101c0d425545000b8552180b00e9051110300744118500340c0c064501900380002c8502c1d001201020001d103802c0c043c42241c00c0051160031035a55801c100302d20b148070381000c2c01c4c0903500580401070b4001c41c00540c0d00a12034200c1018000d610b450b64400389030820300201c40440e0080c1c000d0144000000d901410220560715503003000a8402d0304503010a1281480d401c100c120391184450180031503400980c801c001e192241e43d000d546643d8001808243e00507084010b080303001c10f0342d00f032000a2404800c0c000c80681b8504407000086543c540500e84401401c005c400758000160900620409002c03401c094042920702c0b4515003042c400080d5290b100315409040c09a8038100c07100d04c00310a40441d01da1032402055907204800c00c2c00b15011410741d09004890804501d070001494040218 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 684537374 1250 684536124 684536129
    0x203060616050102090618030f0c0d030305100b0a11060a1a0105090d0507062106030c0b1b160905090d0e0909010e0a0305031f0806062e0309021009 65
    0xd04203800c1002040c41000311101015007100c581d5001d01c4000102d40342c0c28064690b8116107090a001110050b0a060502803048000c40f2950405000305445440d0704036542c0c011a030600c0c00142c00d9480b02c603201008071540d0014681001c0c0041c01d0b00c0e42c240c0c80743c801001c80c641c210640340942c03141d65090044130000400c15034030b030100080c01a2190b014074050030f5a120003805c00110b004440e5105c3c2d040801030b0304101c010a440140c205629410040082e1200d40340c00410400d00d411a00c070382e00100864411030940b018001030501d950081100c918082c2c0d1000e4048462031103110f00c107040810858000e4204080c40c25000400262001400c409480d034140c80f13480c2c4990126091101c6d00c02c00512020243d034851103c2502d00308200f041401180c040d0f0385403070726070400310034002c00c100e500f400607200c00718480c00601184001154281d0071210881307160845294a0080200503910440c5101c0f4414043c0d4001c000701c0e40642000d003205200711226210084642c41c1521062002d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 684538624 1250 684537374 684537379
    0x140f06090d030e0115170f011e0509030702041407030c3608030a021c1806050c1203100503070503030a0804060b041e1a01140d092103140a020306 64
    0x4500c039000e414065030001e2014810b00001080d840c00c2035404001001c1da5a000340700c0da446c21342c007021082d8000e0109100860402c0020b005540000b05c010500007103045000300c1050391803001c00d4142d1010004c86200301d034050000e00214108441c0000031420460700741700803e080c06031408616105066410f91002503204101d1504040d1003108000b200c9440d1520054440b1440440e119504101400243c6e542c0e41c0104440c096050030b0411681043d00c0001c14400c0e100720040307400d480f1a03240026607241d0324105e5101da46019103649030484040702e03ca6940c400105102410384920082829190b0640403142199640c4043c140e03244240f6200000046100b404100000e151340c22a0450120080020603800510f850840d618113072819204803055884c0301003d01072184083c003110309070090800c020481c00503150880070f0f02c200c00304008001d0346d882d021001c03c01d550245a240c0c02c2c425084582c3c00140e1f0002070010000d07620944031201c1108000f0383c0c0100140200e910a5901 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 684539874 1250 684538624 684538633
    0x70308090402160c03061109370f0509070c050d0305090102040302040609090318060c0f0212070b0301090f15120c05060315090f0411011d0904140f0609 67
    0x46449418054220214440c0d1060b0208910404443c003003a03d4414503010312540d445440c9503160a404841006200d403061001c01e01244445542d0400501007602e0095500030314030792030344000d4020001000004209002d08140494852089080352007980c86c152108c0160744c41d0030000b074a661411800084c119880365802c1003400d0700c20f401c142c0e0000407120015007000e44a5000030203a030007542101c2040b50740c0780180c20078581d0000d511801daa40c1c480088940c9400e181c00102284001e25004d00b0a0340022080c1c0110340717a09440120082e40c09098541640e260304d00328032107074400c1c890201d42c9810200c1801a044080c8640080301c040d51640c0c101e0103240c44c003070150301d400c40d03032042c3d0b494003400000298a484403401140b2452203695a01c0030b018000c4200038540401810303800c4912007c000300b00c0007940c0d03a1208100d5520900b400440d0050f4000d007002c144c075445400c150401500414401002102c01f4040402d00400342901c01800280200b40d5a800c0d040b115285a03900c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 684541124 1250 684539874 684539879
    0x10c17090307051c0215040905190f1b0e0f0604080c031018030807020a050706030e1603050c12030403080c01020310141302030c040905041104060803040f030b15040f050406050c0403020307 83
    0x18410304442d10300d146600346c3d90034030703540354100000c03104120382043d105e690b140000c90b0100602c1c441e814107251308190070010b03007003064130240b10b6001c0003d608080c44186c1e08030324001d07078030b1003440821a6002001035541d0341c2c5901901d91940b4481460701e00901c91080d40b14444c40c541d000d0042c506150722902c0d001c038200342d1011242e0b40400f44c40103066000f08810f0b0703400704006201d80c0c0b0242070f20b0384001c15490750648074145404100d0100c0c81005030240720134000500003280310400e020b01110802c005904140900d0b0440c031540d84000e025900000700300000c0d034030640107540301d103580300c200b110304c00d95504030440085440000643d21400440ca0f40403180c059074040c0da0800780005600c4c2c10544c503079942d10100e40081d10705699242150369003208929103401014003415109000d5400c051400050144012180c01b000b8800761664001401c0380c0000c40d000741054000a10a01030b400850446400030002520107641c503904100000f42c070b5041d40c100704ca00712640030b4010101e0a1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 684542374 1250 684541124 684541129
    0x904061a030a0902210c0111070b0d05070e030706020109020a0504180311010219110601080d0912080f0d140f01052d18101208070204020306010c17090307051c02 71
    0x4011070301240d02020085c0104030f412003030310a105003903140600a040c41d02e07240c1c001408044000d03018004540c480d0b00240405030b61082a0752007060320120125158580a405035040c046001c1c44a41500c41d105000680c1c6c0e50541050140030b00960754003981035164001d1200751b4800e0900703141c8403200c100104000a05c030b8605841000c0b60340b00014240303030034158200d04a11201702c007980040d4031080c00044900e014454107004040140080c100024101e00c043e000004603c1120540005502c140b400e2201e08030031a03040300c45000c080b80d5681800c030b8245000f40841202e45002090010015181002c04c01c58181a10002000c1c801620310105132810754410800f540d01903074901c40141c80440d1580c01d1680042d51501c6070307800c8280780020740c0980040e40e41d440096810070414890b40800c0f07040d402c0b03ca41540654025950780e032000010b031840031602c1300c002c0520110300c46c0420390040c0217014001030300c81201a101708a40d914204109241c040501d40c0320042244106001417 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 684543624 1250 684542374 684542381
    0x209010509060d050f0f060907030309031e0510020301084c0203010b0307021525030b15193f0c030203040c0e04032f01110904061a030a 60
    0x100800810409071030750354803410640203845c100d140b40d20a510301e001c0a90240301c03850307000c3c80400041030034904d140c134018280e0b04144000740c4204124000031a000c1c1050400c45051508001228800640c03000450000e40c401d214074038039030186600090b41030b00000c850000070928804010400c41011514021525490550700705200040d002c0580001c05800550700809001c0c4000c2e48910304880086d080219601c540d03030005512104000744040f501904800c00c078040d69041210b160000020350081625045041d80424115001d640d4803038000d000f0102040d81100303105542421123420340309800490600c8004003c20513032145001c189100002c200441e4030340b400d02540340c0c6d1211008440a20070b44400207038002040000340070f4101c054a0003840c03500812403207031401c0e80f001030007052480d00c40903c1c60211f1800000f084140b010000040d10990000c00c804909a40841005d61100304110300840c1003c10010b0300901242c2d0707000000001540c00d82c5076980701a07524004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 684544874 1250 684543624 684543631
    0x15062701110f102706020912010e1c0504080a1401060e0415060b07080316140406050c0c040605030a06020d1107080d05010b0a0c0303230f0718030209010509 69
    0x104050070120320304441d810820190059046806010111001a040400d88181c0b040009004a0580c0c02107003050740c01c0003a201d4650044801625221400005400030380410079000d203c5d82040780070114500d000c6240e119210302c610540360104401c0780103035828000c900c51206a5080131001102058110380d43c050044180800003504545903212000d40050650f800da480e00c40055511305011340c54407450000d003100c8081b942c2404070660703880041d03101c0101030300c0c01d00070341c50003602600c0c3c015a102e190581da0810502c0c2c0362901c40300000d1490b0810f0201d400345100d924519405401c00c0e00c0781c20240e44000d40070342a800ca960715000040d51050001c2402c25545000c5140640c02182c0a003241c60300c42c0c40349903907030a01015040190344040c1c02c4000d540d0000c00600000c26000b402c1c413000a549814041010b08110505005c0c11203484d0b0550b68580340c482c108441c5c0303140220aa0700c03410340390b1129103440500d8202c1310110f07407050100030341185220700103000b44c0c6004242c03140c2c07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 684546124 1250 684544874 684544877
    0x160e030c0a06081b03070903050c01030911060c101a0405011706040b090319031d0607091802040302060304080406020d080603070e0c090a06080601090e160c1a0f15062701 75
    0x4000e4032607604c06001342d008035250710000e5803014084c0308201042c0504c105010302441e0030301011106840740003c0003444a8240c1c440c80001500d1180c0100c28442c0707507046d03180e010082045104a902403000b10010801d0148910310b0030001140150409851805440116004142c2c607542d031ba40d003010703100010704a100c0902c81480000030340142a054000b1810b003558006c03802052035158550100308001800846812040801c09420381c06401802258440b0030f101c00500e5600c0304881c02803045400194000390004200018000000c0043c42100c03229400c5644241c100101169100d0f002c3e80c0c5136038180c111140070404041140c1ca4107801c20803480b8071a2a05007400009210300081d070380b00b9404a5410f1041000725070308629100300820002862403c41d25144441e10700880401f0309650500c440c0100c800240318492264200320745001220310141e043c40c40010300c01c04000c8510900e1001251001d030414107040e0b00303480d00580c1c0900407000000030040c0c000d001e1400031003443e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 684547374 1250 684546124 684546151
    0x309130615111024062c0d0f06140f070206040f0c0e070c050d0216150302091903050d0f1b0203030c0114060f04020403020102030307050901090509160e030c0a0608 72
    0x506004180301da00d0b000d05900c240704461a030004c00180680d085544004188074080c1401c82ca800020901420105600342c209908044281c000503026100780c90090400400424503008000b42c036842110039444403c000341c02e03a51201028140355104461000068009002140000c0d0b050101c10390101e00c41c3d043d804440751110200b40d407441085541d2000100752404040906c001400101000f480e14405480e090030b035800c10702d02c000d1180c0704005c2c181d04641c4100e40741503c01d6060302c1c2c075100000c002030070086200c08050344c9540c0318042a5464021803221100c05070003103001814038002f5444a110010640106442032500350713109a806020400450380072031400c1c400d48030002c40e00d4107900d1030350900e2424058000c0304030312941d009500c100003c3c000b50780c000040d40e9104d8040d291155541c0012801241c4031030305948a50b4012002c1010720400d034490001007048441243c0d1200c51034403844040503a206e01003804075800c2038824000b0704c01c8030320854a0660084640c101e98 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 684548624 1250 684547374 684547393
    0xa030803090a140c09370609110a0908030a08060603060d06050a0903020c090106080f0921030103020f0a03021e01030912080f0a05070207140d14030913061511 70
    0x160400300310038043c4000b03a04000b00c070890318038203944042d40000e180e90315800c500c400c40c2e0500c103c680101c3c04c24054500c0520403030b032241c0003541060b0301800c411a01070180d84c11000c1d003030300d0b035400003800280071034002d10002c00c248034004141c6400c56615500c4600c070b901c0e03080030305c00c4640c00a4034203074000d2405801e10011503542d0040038003c0f03118400014444d030403818000d00308140900124450b0202d10010002d4aa00510042d01b0203018402c0401c15150903414600c1c10480c64034580ea0505540d00c64003041000c4006181200e000355500d409002d00c0204200541410f400000c0d8460a50031840d9043e100b50301d1011665203042c100003035445040c1d118821880c0d40b0591110000f08503070200b1001650035014590490f1006900340918182000042d4480c80e0500407190701d078a04101c180f02c180c0c0c0e8903109044c15504502501c105540308004580c99510a00344240112030300707105490806518820502111307030750391001030b4060340d80031f044070050f002e941c00380640e00c20381030703035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 684549874 1250 684548624 684548633
    0x6021c0c060e010c1d030c03060a0b01021c090e0a0b10050307020114100801140903030a230a060e060d110904060207020a060305010302100912030c02150a03020c0f0a020a030803090a 80
    0x1e0104c50103041e19400d80c0c403030300c0c540d4050b0504511030030b040c040d0300810040d0042d1b44001681da03070803043c8143d011564614210040b0b1a140303001c0c411980042e003590b0201c460701d801080000666018030900480d6540e0510741209880726504c0551300090030154001d481c2d8490005990489500d2001240302070b031082c00325a080e403044c3c880d1156141464000c2241503800d00c10b12607140301c0c14101e45160320300280480d403240001010812156200c9002e072090b01d80300c400904c007518008080c000a810b000c5201c900800560051951030500c02010516070719114001a640b5640706003030b45866a883c0303090002415000e8012180305030280107030720040e940da8041c0400b80c1000c5d5030001e66036255004000759a8840306002e41070105c0990203000e811a10591650000c0e0035040240202c01e0601c00710f0841b40003850906c80451000c03e900007540c0d45500208203a19202c4100c403000c0b040d400707446403100b05e03000c402540081c12000805c00a00a20301855125030080c05441d4009480d071034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 684551124 1250 684549874 684549881
    0xc090903020321060105040b0c03090d0302010c021b061c0902120d020613151805010510080c06040e070c050102070c1805090d050d02090a030c0308120106021c0c060e01 74
    0x44000d0b80000c580088580381000ca101e00e20800c50300d04001e54140f960018015204a00803003040007030000d5141240a810021510195000340c200074403e10740d070400a00030b00d030803002c802c014010680f82900c0036134200b031010071101009244524001c07041d46000502242d940611300307500d0b01c0c2d211707400c007507603c0420b24901d51400e4400781102e9034010341c00900300040101000c0b4460b400107440c00204091005822141e8541503000816500b002410000a009060300410301c0d07080c00d04006100b1400d0340c1d1801100c0d4154102d8820194280801003d0700890080e031800081e45000603030494818072450a055006a00040c074110840c0c42c3c8502c40030312504030010b5505030100f040c0e1424402e2050301d50140d0024050400c1c081c0800c0d004003140300b50100390b142550003081a0445036540090f68000315404460451002c0d031320b15040c10035822600004c07910300307803003400000e24500120325079446450300e003d001c1c40c0d10710f00310307096032250300507a07003a1a803d56400001800c14024030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 684552374 1250 684551124 684551141
    0x903070e0a02280e0f0d06060308041703270109030609050303071413050f2b061413080d2c0705041802040b0315070e0907080105090a05040c09 63
    0x201c0036a48070325042c01c007015922000c1c81100800414507201c006503034400c109800040c421519050501000b070700040d01c071030303406001810003407804400100b00800080204101c910365070419016603450141203490740600000b44416411010814040d100000e10002401005041040034a41c0301c1d11004100c4a0380c61044426500001c107001425800095601c03540540000c3d1610304000c4160200401119100d81d80c020007aa80e070040d0955251159000702c0d20322418400b00303007400110740920300070456000b07958592608880550519030201035034850030341c24210a00c0c16019036203001242c0d201a4080d00038550341c600d2200709182c0451510b001104854503c3c19011b0030ba0540ea00302680c0340d2003540700c0c503d8000203010740d0390308913588850180c048070006107202c80f41003c80e0a04114100c1c1c003880c20f148004001c59550040c000340440b4006403014501642d0740301060302d08a4003800384035408a60000050308001d425048650b101d845810011040c6940c1d03c3c40105649110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 684553624 1250 684552374 684552391
    0x203010e030711150405010c120201020c0d050315010512040b040201050f0a021510081203090a020a06261b07050a1e0642030804091a10140903070e 65
    0x3d48009586152075421440c0403e50704200d5440c00380b40400282c048150000300412449a0031002620f9034001e6054500c107541d8007085c0c4a2004080c10001c0807070344120f590304840c1d000c02d2045c083c2944220241d0341c1e00c0c40c1d0140e006109884039158620030002c001c104a04000c410081d01040410b20000780c01c1c2c01d442034000f80744049403100d200c100400000c1640d102c0441a5800f00314000001420000202c1101d4100313070307039484450500d03041603160360700170b904544a0b4500003001603002d1180100c00c0201000c12002c4440c1c0660610080801d5901c0305101e400d8901d8255044110802050014070803c119520001c25540e140e0a02210751912102c40e561303810365105028040c0102e401d00740200240d028070b102f207203c404090414441c00f9091040d0000c81504060041c130034031b5006140c002c111075440f80d542d130000501030311540700e445d12801003404040d070190400c0c0b08150040d080d55120701000e0440d030306e4800301a81020400650522484900080c040752100d8001d000f003070700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 684554874 1250 684553624 684553643
    0xc0b0d060902040311120604120f0912030e13090803010e07210e011107120503090a05190c061b060b040917250302120f0405060c150603120d05040203010e0307 70
    0x51101b080740c0c031702c0441460841d0341c0100d0108000500b09401c02c00720842e42e414002c10340a1035280444113020b6603007264001c45604032600c41855004582454400e104035a80b05c02c408401d09404241d850f000380081c10841c003400103200c0310710240100d5600060750318140300f8140b0342d02e0340300ca4231160044910304010f40d2090321031403142d028080d001c2c1078841003c909150644554410000c200b54800700c00c20044040081181e10800340b0240d520650031000301c85151034403400b0401c5060a500e02200e90003080c910016440740a04200d52007184129000c014030426511220090118010410b5101e0340d81e101d0540002c02c0901e003d002c01c1e032030840075910b860711103104d4040c0100e040c007121400718417080c000c80040c0e80016403000045076001c0081d180c9484c40281c904074012070300403990001010034540c6110400007143c00c10156441a0302006031034030401d03d51501c691408040d4940010082ca444100003038000a802c144003400000e16480ba40b041d1605682006404650110300c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 684556124 1250 684554874 684554903
    0x20d050702011a0f040902180a0509060105012d0210180b011e030f0602040f080c0a1e03110f030a0b040b0907120b090703080418180c0b0d0609020403 66
    0x509101d001d00410802c501c10000c0018a00026603840740d2020703091040d41c90b51012811522408e096640240c02c1095200c3d0b5424903569001c090a401c07620303800944568000050198410504110746d555400064984a04d446103134440210404215600303511a11508480b140c215100e42c1000c50f1032001703810003800c01e52504508009060b4842c90421180000d0030030211046a000c0003201c0d4400c1680081003010f10f040c1c80079010740e40c45104255030071a80002c1151010940040d811070031505100c00a840e180300007110065001340c40c245d8000c0c18002d100040310324165504403400202219044002c40e07001a10f0004c403008111052a03e0b00c1c10310003081314418240ba04111010040d000050408440428a00410381d001c0e150403180b4003c2002c1307100074803650700610340107122182c0c0d40d41c48101c88010704448404006041c0d292420003106000c241c10a801d825601c15800d4910525103a0450925085440021700c1d25a0300c0743c00041c6000c56100820056104d00c000060350031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 684557374 1250 684556124 684556127
    0x1503080a0e0a17120714100906051305060c0a02031b01020c070e090316060e0a0501050618060d0212120406090515031e15030313080d0c0b040303020a03020706020d0507 74
    0x20b901c0e07401160034403803064811280c0c11020524007010f030680c100e400e49801071030825a8140100b0030345854540110088a25080001e41020710894000d410600941d242d00118507502c210320a4090010341001340810344144a640090245640c184122410052140c1a40c0c03400041804504a560360008030741511900071700913503000300b05407a1050721900d00350b0310f82c640301c1c42502002060f01014144103010092154010000f40c0240c400b181c0e005421860a18000c00c02980c4c5240b040a4541c0d140501e4512550100e201380c0d809403500ca400708065092142900c0859214841c070b014062440070100c1d80310002d84020542d590b9018041480c0c0000c0c0300482100005400a51108004116002800e07014103040c24440700c000d0300095403070911600c441028100020303454080018805020038003d07040c603061b28941c4064441030740c1c4150041d42c00b420309501c0182000324250001d00880c3c0254080c003803030542c44c06c0251800203141c0d03850049900c008440c840c0c0c0c2c0c1e903e100b84003070b45 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 684558624 1250 684557374 684557389
    0x5090d08091801090510061d010e010c0501140601180602071401110613060f0b010c0210030f1505120c01020a08091804052406180a27030e09040201090501031503080a0e 74
    0x342101d04281061400d20386090000c182d00308c0105041c0315502e1243c0d6410791103500c2e640c1003590000c3c000c000d809260004164000d0091315803a001070a0840c00140700102039003004100d580035001003164910b82046460341114040d140c0d414400a051505168002413200502c40d10039403040c1c92030303040c1c245000310803194401c007800c0000e80b8100303408140e641c000142c9000960119003180c40c54030b04120031806040c0342e070021040d080c01c2c10391000c207403048543c809050302d1003113594040000384207200ca603a565000e844180140d0182c141d1001180c1c08100400941d08013811450700c45220f03a070f0f0050100380c10f4808a4080d4001a1213503040748060500c54034001d0103002c48013440c01d000c4c0001d82c1050006045102c3c90a1280c0411070741c00460340085001c00b054a4085181070425661511500900400307070041000e010f04120b4514090354181c0c4942d034144c6070f03000003d043c00d0044001b0008036885050342c03034400c0340100116490704040c1564422507554400640c000d41c0034040d10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 684559874 1250 684558624 684558629
    0xd020d080c0313031808120408070503060c040b0c101a01030c090302010e1e040c0c0506010806040305030c0c0c1306050f061216210204031205090d08091801090510 72
    0xc0700e0078403d010012400d50081960306401d4640003048400325407070850029044c0c0c0c0b1550342032183e01c409100d82c0c00408054404c4610140035140c080b99200300385a2030300821919200249410002842100c0400d40074001c85001c00b402c841440b01c0d4040d338cc2c41158606424201c0240b0b5080f41d06805690501400c030b8920f82500c2d050700300520750350028060b092140340d02c0d8031a004050381d00f41c0503a005130001000180060003400462035003400981364502074481a199405588008140d11100103007441c001da131700d036895502c0e60303a81c49800d1119410986507901c543c050440142503036a241c03000214011038900c00040e0f00c034604010003502058040c1c0c49402080d062140c3c00140001c8143c159001540030021074038810103e001300c44120000c201d00c00220420011401004004c2c3e010f0010b4911407969030b03000450003142900c0742e000d0300110f281c0c070141800b07803800010f010101070902c010001e0410000035041025039503501600760414049940c0d00c1c8100048041207480c0c0400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 684561124 1250 684559874 684559891
    0x60204080c0f04091109130f0f020102010c02060f040809010e19051201061404020a03060302060c06090105060609100c020609210c0f0603070f0c0c090b040b220f0603050d020d08 78
    0x30810031940d61681440c88184001c2c0314042c2d210000320410002070500c074896600408e44110a04180f41281001402c01800c0c1d0056181820760201c0340d000084040c050000c5146448850b42c4070350360790100c0d511291103141045101a00d282d043d4851010364204480400503e0340c4460801080c070400001c140d1550546030306204c4200011205590b14640b0000240c90150b591108590254040d00141e80001d41045000458000807080403e00c5401850110002d0280c2d4840a04209180c06141d549662046840d18140074082c056145484540c0c4094070081c1441188400540441d07a9503030203009540c889204490b61040038000954010012a91628540d035268041002d9001c01000b101c01e20214280c10350aa038010822462540e9100c0f902d01080e548600d2490701601080602d40e024a0400e04a40042c0c40c0c88042c0c038003038503901842d0324131a080407078542d4003625040c141900d80503510540480440c4051121300749100680d00141140f4002840091582d1402420b512 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 684562374 1250 684561124 684561131
    0x1b0d11030a0e030f0d0e1501030308070216060e0103050907150201140a06270f1a10080118110702030102040801020913020408070b1b101505030a0c050402070f060204080c0f04 77
    0x10808451001900c00c0170011460004214500412541c500041c40001082642d0441d0002080550203150300c3d1043c3c01c07503420386000d0348590003440f08415407030150501055410300f0700003e81d4842e40c030865001c060303c0c044588240d564001e425140c2110741c903510060751918102c956600031490b001d1f40104507200708022271894014000046c144840c00c2292407405c0f81c038103061503100f581003000041b1400c0c0007003290700c901c14031041810200c00915401950702d10540c00c202402030312010304a6114400b00700745010480d11200007400d12130014410a00203004200150300d01340301600c050810382d030005a03100244001c00003c40030582d84d4840c1c4074010441480095404907040044922000d00251a0710801200c441c4801060510300790714840c1d078010310380300d00c0c26810100d07030300042c00d01c0001e956848200b4152030341c0346c011b40900030002d8044108154201a80240030040c001c2484030410b02d0581c4e07842d402d0341d00c40d610000840d844040c024003140740020300172481983c00c84040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 684563624 1250 684562374 684562387
    0x702031e0309190803040b070302070b18120309012007120c0815040305040911041d0103030917060114180901060602060606120708040809060f0403050d03141b0d11030a0e03 76
    0x41e56881680202941050042142390030140200010009032801c0c600140e00d0b60000c003400100100e00c0c41e0002c1c491007101e81403658000b40030045910007101a5507a41002e040c98410442a0032001501c0e54184208000065003880540c1494851031050064103092450711041d245042c07400b40ca29030720514038100740030000b500802150100d0389250f030701194400d51020b291900d8000c580c0454903480442c02031140000741128a42d050386d00c03d445200700345480707000c1da20000300361004070b00c0d0660080005011000742000781c8503c00c400105103000195003d902e4a5002c44160b40c044913036134507007805001c03907501402415880741083d5801d90520001c1044100d08400144c0202c0500200001042c00d0101c0d00b1704651440070b000d003056a5980d003541901845074050311040e5a05d00502340c080c41c00c5807003401401803001d0048101115510781410780c880311260542e030807408010801c0000046289401801040d0f0380304043d50b6184d15003070007600300381e0f24001c500720a150000c0100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 684564874 1250 684563624 684563639
    0x3042d14060a060605040e040c090e0a0c0801110d0f020c0f07080c01051e0c0a020301020415090b0c060103141c03060312020f060a180204020c06042a030303020702031e030919 77
    0x81d60201c41d40f000b4030407d640c0b030b58142550302001e46e400489100e07040000c0540203604c00600d40e40003601c5032034582055a030ba0180b035404c880d031010300c0d030844100811a0306a50521500b191381002c0700064014a041ca4032880c0620300304000619942c290001034003000581c00c14841600d2a50302800c00600d460740143d244803c4550200101c8911030000c1601403060b40104003004c1115400340c02107586030f846803034a0600c041d5402040c1d0000700c1900300860101303200801d4170844501840101450390031a1b50741d034005000400d25003090301ca020f0050118618444023082810440e480000d181411400c0a0408101a074000300a66024401c85081840000340b02a40315200040000e0408810f20070017140c804405406980079001246a40c840740c00442c116000320f00c12030241c581c40803400b050144074400140e441002e8680c409040001c0390203a00100040392001b815945407a151054814402078500f8040b005503101085074803440c102084008000c2039082109440d00d40b41850 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 684566124 1250 684564874 684564877
    0x108060c0703270801291e030a062406031e0c0212181c0503040b03041a0f06090c04050306150102030f0c061e090303042d14060a060605 60
    0x400700403c0b00740103501d05514800311030355040a803140c00d19140d680d4180c076018060803040064460400c0032030350030030340700105801503031107000e07010716001551001825900003100c0c5915070140581031294002038810b114042e5201a40709000585544800c480e44040d401500b251040c1490b0000316940d039102c03810b90258880514a0100705860080d00480c2081f002d40b128404002010961904085a90320800c55100040d20079a03c1c0508030f860340f2480c0ca24001000c2e00070340080106000000060005640c03040c0154107600310500040c8a001c01c010003161407050400b408024131480d03241802c030311a001108110368074102170519000a450711405480d9841d840802d4413100c20b164020300c2968060003452105035245d09040b9019500c0e0345d4207e80c407100c0340c007a12200043c0e40002c1215103001c0c4002e48000c44c1169901d03501e5150344100d0488842c2e401820800354800d0001907a10982c0c0c1c680b1582c0e00c02802c5401c0c00e0020700d40302006c0c5c030b16410a810658140171a41d440b10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 684567374 1250 684566124 684566137
    0x90824060f06040510050405031b100509151801231818130b0703090309090902011101020d060e131e030c06090c170c010e0d05070f060e090108060c 65
    0x4071540103002004001440512980d4001074202055031902e0200b00e4018001d0022110107400b0784000d51000e0300e200801242c00f46080d82c1c812181c4411b020307000c8c0305038064a400c680203011403124403140745104609401210078804a01e19207400c01d402942e21032481881c109000340daa01d000d44021800c00960701414030303500d05c64442080041c07500d50780d202c40d03080044c1d0380148a104034104800300d00c4601036506070641c3c00c00c40d818003161070180b0030b03c03e90310525095a184603032103044c5500803010f4104042d06904100b42149407501034502803005113081954020002141440d0401e1502ca00f51b001304041340388401c0500c0c40380845c4250310440c5050200c1c2e41c85540d0944c4c030b45400d8403205a070140c01341c072041c07400c91080c0c1003003032811580c0242c2e204101c3c01c41c1d80c078aa8480b22544d41000078031850010300300c803280091324109128180c0d2520b110b48196050346845104050480c0c0281e4005000125112a041c0d11030410791030640c00f40010b000030f00082d01d00f2054503400c5100d06d9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 684568624 1250 684567374 684567379
    0x3080d24170c120d08090307030e09060d060c02060907060c051519060e01050114030915070c080313031404290c0102030f070306090612021203040b070309082406 71
    0x201d8031508005042c401c1510741a402859840728070040444603944d0200c10b6064004200c0142c0401c4a420340001610101c560581c1c911003604483c1d8244041c000c0041c1c0f0340341d00200504001400038000e8010b11100407900da0080c03100c1d150020045241000c150302c000c0600035051403400c0070440103c6d02d190b82c5113201d40c4868140c0c03500b1010340100b01c0e03420191040140703485804034084013140601c504980c402d984485c0c0e005411000400e1601c01070b15400541c0c3d014001100d404201e20fa1001d80c019000d0800050b11001038803140a607500886403d5503404a00c140201019041480740c01c48080450000303041a042001d40701d0a901c0740e984d158110001040500e240d04020003c82d4440c1e800c7c000259160309204440b0044000165000c50100341000b801203801d00b20340c0708180444400e030048440c550420740a2004012100c1c003151900c0c01708200100c0e4084512008191540c0302e960b07601c0481d46000881d9085c1007483c041e80840c83c44001c0034500301d0303044190356904030008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 684569874 1250 684568624 684568649
    0x150c04050a1e08121305041a0f01020313081f0212010e0406090f0303090b01050609031e011d06190b090601032301120506060a150c11060403080d24 65
    0x100b05020350501d5450307020050301d205040081c000490fa007000340c0361261a212803103020684507801c01007034618251000c062900d100d41507040e9850001401c03102d484040c0180c81c07500c88031254000031440240c101c040607510a0300149480366240c0c0c80e841210841410460602c2c0c00c0d03c8514002850612170048002d282c60045018082154003165503994041c858031603000c110316000e4003070201210245d803561103800c0000f4560400a00311400d030580200a8020b03d1559003510b20481750703940002e0300544da54250880c04a25030200a04c41221070001803105280c0410322001e03900d4010f0078042041c1c100001c01c2c005407a100f10154005600b420086183c02e1010320b107a282c01c60b903088110750080910000102180103244080045014005807216961207030140401c2900790701c900b410300e401c4050304048081c82210038003641c901c51107a40e980b14050348009031031030700079030802e803040040000c200221913641d100f2130801d14100c2c5150001c0400600076003294640e076102d41500040c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 684571124 1250 684569874 684569909
    0x30712110904060c1803020907030f0e0102030a02070b150328050706030b010f02190303050405070308071101080702010902010e06030702010e0118032c1c0203030705150c04050a 78
    0x1944035100d12048003a00e481d669281505200c0c02401c9140180004613044088001e2481c840342d030008142c0b43c0180a40395982c4802c50120000c1c024244000d00055440304800d03001c0c030003800114016050300c40f002d40c60742c103281020150180b02070141501d24080140b140d81c036880c049500b0340e0191414084d1445580e8220405a5aa01d000002049030103150070100e081a0580d201e14107404080e6124a21a1682c40d800e90360381140c0719a040d80101000300c1300000912942109903c00d20640944ea14150361399290749094024280c1100c007e19858508500355070b20907502648034140784003c1c02019080e80010302900b000b441400d0240b00000001501d442c000d400c41c0300d20303d0f0114000c210240003007421490448040e50210000b44500a161108819403000d142070311034483e010340c46840aa904001031242412455424101c00407202d00150358140050b047c224020340192176044080341c103910303101100819283c4960018401032140d5102d460140e010394207142c000d940d0380503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 684572374 1250 684571124 684571133
    0x16080402061c0e0708030c1903030603080a0e01141c09141f1a03030a110a0611130e0108100b1c0c0608070e011e03240e090c030712 58
    0x441d042c803240c500c074140d14101d0b12111042d80081d07040b459440641d003240341c40b4041562a449010b0150f00a40c0c481228518083e104a103040c40031413103820002031150380c030303a110041600000380500126400c281c581c2c500d5600113100c00a402c180404451a1010f04018031200f007190360310040c289551010804104169201c901c03c031a0180011100d64051000e8880340415101603424150b50505415800010f21520301c4040000010055410b141c1078902c101c0354000c610000302d0b0b040c442c080340700b80843c0c0c01c0d228010b4010441c0414550340c91065542d01c0c150a01948580c18181d9030760f00422000f4404104819081004a0041690503e100020b01901d1850300ca49101c5403000441c4030402c01d64060304805c0740c40540340ca8002d9981c51209803030380c030700041d0181e000c80d0707207045181c0030b109080350181d1200e40d0358200012a44911031510384144581c48503140703c5106807100384100640c007420240d002812400038840c3d1040300011030345692142c4a41d01055910000c001d0800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 684573624 1250 684572374 684572377
    0xe1302010e0402030907140607111005040b0f0406020d1409042307030b100905010203030a020d0f110d0e01020412260c0703120804030c031103071407080c06031608040206 75
    0x520000b0020b540300d0a110449035100c0303105100d414001d41d29000e41004c40c0c00c000040d00d09268009a00e0803868540e58144500703d4018941d0301c0410600300f101080501407c00600011500358500c40d85850412310f020b49849007044001c070074444454191b000001e40c60044075003210003503070085038421407d000e900d80035030801c1a071007100c080081044411540760340070828580c411a03c20f03050420030b00341500c041105009040c0180c10800c001900a00d254004225030741000400082110b01d035044841110100442c07162440d400194038040c0d11300741d004402400d00b11a0085290030701d048002410140c0c0750b01c0082c51002e040c0c1c1d0341d401c03403000c40104114404040030415520341140140a49400d198001107403822180c004850a0920501402d44180d915480c0c02c200e59406440c2591a1402c000070720090344800c11114000800083c0211700641442c0000c0c101a03040c004001c0c00c01119070701c60b502820081c0100300614113030f0030fa1041120840d00704210030b5220350020440303e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 684574874 1250 684573624 684573647
    0x604150f021b1b1f2f0a0605010f0b04090b0105040e1806100b0a030506030f0f06090715050706090f020d0807050c03030306210c0301110a020f070e130201 68
    0x907103014a4602040040400c058504070f0700d036404500100c032010b04000701200e000c03c1380b607455111603840c1d01806020f208581c0f280c01e100403030310700d802c085035050710b120750986080150a5007003908503504000003070250501600e03030344001402107820400030f01e07035500480c0701d160401901d90002a00590040003141c02034200c0d0303401d4121034500405500c9015074001c030028010f1045c2c8000038484050100710300203172014a1081031804440301b000f180a400054170f0907525001d28001c001700300108024030980541450060181490b01c1074085003031818580c002041040b0303000d100310b00c950b0301c4403c9400301c0b076000200203201030041c1000c04a00c020150029084901c1c041582c01b0300420314007900101e48943c003201c2c409803003642030540b41d000c01c0e21180d82121900503200044600d0300340d622102c1005004949a02403010002400d648121102c0d055a14001031031605507981405000000303800680140f06071498a0a50b0f2418800104400200003a0603040c804680c41807500705c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 684576124 1250 684574874 684574897
    0x9060408061003120905010c020405040c0e3607120317040f1e020108010504180501110301062015070509030706180509090a083001170604150f02 64
    0x1407a202103106841501400292658000c458401030031510405c612416034106030b680807425803141d4280070103414081c0085402c010010400b10301800e800c0442c170704c13441c4100b102802c00506003040354416505900c900c4405000c0c6400410b030750800040d12002c40f443c500d5a101400f94504040382c280f591402e490403144028400e10003444501c40c4103000346409005013858a503040c074410121038054040007804a105030700100842d20701580321038041d02d0524181411000c10342d480c182115130000400110503408401444429845550080c2902164031101c4008190680c040d035908000340c0c40c0030b0340c1e140c000300092829100b8010342e81c400b01d018080f281820784590024040070320010224080310401c03e0009081d16000b200179000b50301c80c130b000d00a407540d2070b181c055a6600c1300d04040d0f450340780490b01482070101c0302c640b030b00c0c6c0410401d0701444950401c10920f0a118000c00c84040790b070710010078040850000f26205e02510640c9c030000540103a14500b001c042d00039103d035820b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 684577374 1250 684576124 684576133
    0x120f17010e0106030507080906010b160c1e050a0b0d020904110a080901050912180316170c04090206090f0310021305040e3f0403050109031e020a020609060408 70
    0xa011403080041c0c42c162481a1000d022540e201c0300100d0301180f048401c04043e50080004005040d09580200a03034680904208c203401c52a44419100c080305502c8a03900b88020ba812038003254045c02c030030020349800c03110485c01610704a20790110340240d00090402a50025000030960384580c001d10400d202c0b00161a1105003024024001030340c11031b5648055400d00300090081a00820310700c001a9044038450708004481e1000c241d0220601c02c070540501c0303a28a41441c0341c0208074440010724031407a09113034000d0140e070710300c0c10804100c5446000f2810440000016034680d02038031005907051b10803a103500c4040300003d2400c600762442140c071501c0015940d006403555a0f80b8403e03a40c00741c030240420108030700620381d500003962150a02d2488580d6001d0140041c040078a01a404905c2c8000021128544510550304c141c1c01103405a654141807800c15800103900040b05500605811140070f40c000702948800e0a41d800920440300010798050070381c1d904003503901412030941220b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 684578624 1250 684577374 684577379
    0x60904060816270207080408061812121501033e0301031208191a2707031d061006020f0f031602041b0905040b040207120f1701 56
    0x195140c44401e202d0000d251000440450031110500d20400418039000c07142c00040c414101c5070b0300940108804441c1560304100016800c4420080b05000c0c07001d440308130f4a401082c09a6900c3c0102003145100580028401c00000800304031107141d210395014400d096001803070004900030520a10000240e2508912203280c11708824030009524010310f038a8564150012003004070390109100050503403d0250303c0d11700c1a8410781d803444d00188641c1030080e14805070303e140c10544001e03040600612181d44110f9801e8a081d0070090041100c015050f600000c42c1d81007d00f03c010010131010034140c82e04100c0c04440d8001083e040d81e203241e042980c80320b04058280800301c13000380c8941d40040c880d2a012007000180450b030b1403090a0280d000758035000d802468071b40f083d84011011b903032046c0e0b0b603c2c0b04101c522681d403a0810000312179030303100411070070103040000b11a5034005450080b4418401d60001030f5410700403461100799814090440c0c2c00d07030181200c040c00d120b444500e2542c02d15000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 684579874 1250 684578624 684578639
    0xf1502190b01050a1d0a1d07031a0106031e0b060912010e061608010302010f0e03031b1c02060a0207110303070302030702030c060a08060d030207080d050c011a180606090406 76
    0x905050b03d4040301c641d406141d032540d0600e2a031800d03082c282c41c4a0002004a040403c00740e10200d50140184103101e1103540303201c050342c00e00c64140e0007961a140c684072720354407544490b500c0a024040e241410003400085d0900d140031400c03a90a200044d0741d607030301c401900f65074802c240d03128100e00030681503000342c0e03c403441d0740a445c005412900502c2844003141c0b1241c01c001c0807004100c0c0c02e83d00c4480301e81c07960700111000050207a2941c03d0010010302c0c100700f610140014100c80c002c41000d001c04020107014545080010380e454803401100901c0c3c0c41c0c801340c1c0810001d401c01540c20000d0788031003607824030402c400048a0000d5140c80b0000d600e84c00c16801001409445008506a4010440013001e0200621441c210a40000d10b0b0400081c0c4528055401103d154060710441d1405919001b29034600001c041c2920702048010507003810700842402030305945010043c1c03040105460002140d40e07811103514124400300c60000107003294842000f074607800c00e4010414070010b96181c11 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 684581124 1250 684579874 684579893
    0x3050d1104030c06020a0f080304080f0a110d05130e180a050f0105060415050907031d0a110607050c0105070807120503010914010b03061c0209070e01090f0f150219 72
    0x2c00c0b50b02100031000000c550b4008a045118a80c10213043c1912220700c0e5943c007043da02c02001150804410700c40c12a41c600300b0b10181201160300d0322a00107582d500c400182c50485070703c0003202004020445c21080408070101070701103800c0a4010314031500d95900e100700c15010a410f4144a2084500d004240710000418081d252111002080652203400c1840103890070100c203803004038003000c410001c07030510f00c007000c3c0d00c45a41c1c5400a040000c6109005404540c2041a4150742c0908916428000d110460f903100c92012100e241c43c1c04d41a5031426241c403441201d041c140b01c40403e050041c4001c200807201015403114641c1c452807503102c3c004d04150400c1c06040d101e6031a00141a00319500c00025606032003c50703010a080d40c1c0c0d000100036070f0381115000710700f402001c0c5c6101401a1100807059000d408103031205200408580300041c0300002c583d000c20088040882e0411058030303610211025a110131601d802c480000d010141e01e89801c4140c0030701c4d0003112581d50801d0011080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 684582374 1250 684581124 684581129
    0x3060b070c2303120304150501092007021c17040b0a0f03180b061c110f0102070f181d010c0905061c0e120406021006090515010c03050d1104 62
    0x2c041800d51081000c60100001c0c44460b80c1e4040d030241c1d803d01c5400d041400555441031184842c0740c0038003110b44040e000c4c2d490a030710082e16a07840f00510000105251070f8810715901e902c84d01c0f810071245400084005c012040406000c100d241c58200c28084c200c8500406000c080c0e10141d0344598641207402d10750b016220040002c3c00c007038440216070b8842d02941d103030741540b6a8000d036008090303201c04551f07000c003a0816030f104401c54030744420000d54103022401c0074000e14401281c100e050082c440718a5102c5009411900400010f00c0f81c1d00c03951b07401c042500c01a4200c141c0f10203180020b200142150502c000960102c22500b500c0301005400c050503c04241c0d55038001d4075501c3d001d2043e03d00540303039001017050500100320103055040d03000030110070300d03102102c49448000c0704850a60f4800d03040100182c20109080440032014010b03800140b207454030400075880c01c403481d1000b4980701c0000c181001080ca8040d003d02d4400c20540d4010b109591003000407040d9151600803d902c2071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 684583624 1250 684582374 684582389
    0x16030305010b0f07120302041e0509060109120803070201150905061305010b0d020c0705040203010303080a061a041806080118020a080d0203030408160c09020304050118111003060b070c 81
    0x30001241c10101d1600f0b66000e40c076420740150801c8596580e2000301011440c50b6010141d081c00000b50319803004981c0c2c1c24040f81d50401411050400040c4001c03002c4c024200c505006a40303804120f04e80307940b40d135040f2064201071859101d03180c0f25003c9014213420729080681d03044903800801d1000c601c1d4450b500540044a000c40915003080004044c0c1d06c003440341000f503440901580241c00001c5e001003404107440c0080e104840c0d15500010100d030004c1c1c000b40c0c00034012030208954800f0611a4102034502c401080318040019100700c6900d10550150f1000c90700100012050000d682d00250050040200240640301d104070f418039500d0080041a4420420100e000510758800f086002d84010356601a40c9165119265480c03603a00c81400d07001e00b4500c036588080400d100c1d0038004041c2612040250343d130309043c140340b0700356005c00c02c05903101034805000314000b03071040f0b80350103080030113465142550035000790640040103035612a0181d0840000d061341001001c850369800d96210 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 684584874 1250 684583624 684583631
    0x13030804030e060d0e01050901050c0405010c02010210050403030b131a0f042316090e06090c070c0602100e06070c1401020c010f020c0106080f06010302042705010f11070b06060304020a0308160303 86
    0x10b0698207030030b2b03510a42e124861003204100030b01143d440381c06141c0603240103004440e148410042c80708111001140e06030300103641c2e02d0100e01c01b803134440d00b456803140440b10b007070180b510b1074030014484440101c01c0600c1100700d1303541ca0900d0707100c1e40c011442894015660640c0074a0b1110005e80d168011111040c4901c00000c855550500540346601550390024510441d0b94076401030180c40c0001400c0003e0341181807103048005000e0030304000242482e036014100304540141400c090b50741d194000358003900b00e17400b0028520f6209483d8480c1980010710a00c60b41e50301095140207200d1324405028075420007069030240d004640082044030b9a000c02044590b90f2448200e03220a030341c0000140503000000104050300d02504080b840c1d0038031240030a000041400403001400081004550036511800c01c04c0300a4035030306c81c04014106290503a4541444e5035141a441d60008102d05d202d40760220100307003591180c111403006184c4c00030301e8555407800701009071014103d4403001c900080c02c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 684586124 1250 684584874 684584881
    0x14130c140d0f11010e0402040b1b010b1e0916021f02040f0906290406030b040b1c06051602030403021201060506121501020a110f030a08210f13030804030e060d0e0105 73
    0x2046c2c400c0b281107449d076003101e03810007980303400c280c03070f51603c0744918202992507000654240c1d03520b000154005c40031920100040a00070180469450010442d1a0b078074400d038582a0815004146210842e818280102e03074001e210a82400a0150f60458921003294240101d035601c8030303500c41c0f4143c921a04d4445085c5440d0425000300f036041c0480d4040892090204100320ba0003900704c068080802000410201f0f0400017040f5100c0001812030f000d2000706220009000c981d105482c2c02c001d800d00343e020b04034a8800041d503280704070b1100a00a55203100240907180003036100c8000743c03100a24166030b81100100a08802c00240d90407000d0214600c3c0020b50f56000003506402c40350702441c40110724030603204000206e070104910075090300543c0c0c1400e000600d01c44c000d11080c0c81045607041c5c1003200f84c2c085c40000d82c004015103000e400341c1c01805003001c2164114610b0544c1071034459419500d600d800c8a000c047d018919800802c00b0512406e4000307030380c01007800301c1c10520081046a5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 684587374 1250 684586124 684586129
    0xc060e010e19060c15090f1e020307060f111501050a0e0403021f021b011a12250e040614130b150409080d14130c140d0f11010e 56
    0x100200603890703402da10780c5001c021842c00760204030785690281001c4c00c40326218000440550384049421a0503495030910f0710f04210700c4071a150600303200b10312901480c078080d03400700e540d4114500940046c4480402d400300708920803510905d07152400c40c25600b440990140f00d400740c0b4000c1c040c95109961140001c80c000c1d00b4282da661045405500a1106c00c041980c5084800b00c88000d40c1c031000d03003c2001c4c0041166016103000c04d00031a400024504400e11100208401036510b4107205131204522003d9108000078400c2090900b110f85417021441c191200c44400800d600028042c2c200c0c2d0100b10600c03030141c3c44004055174a206a072203907a500f28a881000c0c41c808ca0042c0510804804143c015805154952aa22014000190311151a181d0980d0b42d001000107103a400d4580321240d400b0310003000f8083e0094510f401c0840781140c140d8901e51200303600e00480d0780519140360340d280b195a4403c0a045003039000b49a0516440343c03814803291600c2054403a9010549501e4201010b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 684588624 1250 684587374 684587389
    0x30705060309030409051015080103150b0a030b060a080607080f1605070f02040209130515010e010f0e04110a02030a031b0c030503040215040e09010506030a080313020d0c060e010e 79
    0xa85161018504d0300d401d1060f100000d0602410302c0c54000044240481d1a512110805e400301c3c40380d4a90744115072561902c9004a1520300c0e01400c91030412248003031940380e612f000d04c16640d029142010301da0740d941c04102610f0260780407019034400d103000e01c4942500000618052b9403e6a5141100d40e074a0f0340705661000c0c82480880022010000440802c7d842011003c0e402c0c40144090300d0701c00084005100d5100b807054036000107540b00c0c180303e400300d080c1c0841c0030080c4c4203003425003044c815000003030156064000d500060020084851143c1c0e130b10b07540800700c80c11030b85480765201c43d085040255241c1248107100301180c0b07044071040015a07140315828070041c150f91410940d80c1070f5034045840390000b03407040f80c03c00c11140480c0040e000507006040640b019244101003882c0005059003903c00241846000307420091010f004250240c0c12664403007103010303400154038080c0c4042451450b450b0006070502d4400c100102c0c41c598880080b40090000360784109618080e42e0070401ca8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 684589874 1250 684588624 684588631
    0x209090f04060905010e0c18010b0a08130611120601090302030303070c0602120108030a0f0e0906101e03020c010b120d11030d15030b01060507121b02130b0307050603 73
    0x111100006084405826000c980c018407071080410b070350200741d940c07a094482903c1490119001a4240d02d4030741031a900c120b441e0500b00c0d0f000e4080703503d003e000c408184600420b0008102c040070001c0c1503944e02da04801c003640e0f4040c40c100101d2060311450885600b021441c800194001404a50958441c000d0541a030b6001006140b4640307940c1016910b8101014046800030f80911640c0c04441c42081a58020180d803c003445d030f1100c0070140200401c0080034101c040c00440d00c011440d070b4841d8110107601c080250341648032403000d80800c0d10915140d41011705014410341040105560540141001e9000200240300300b440c51002c00800d604e8000a141c00c1d0790051200c81c2606108220b42d020003a503001c203507031814210500000550f00090144481d003810b0f0442003007007015405503280107080501e802401d00134542d41e11204003099000140400414501c05120506e102040009080c0d0007807014800550086c8a10050001440c0407480b90081000c009054180036044074071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 684591124 1250 684589874 684589879
    0x110a090509070e1305010509060708100e070e1c11150913020d14010305160f08030a03050a2301030b01090902030304091104030f06020d0c03060506042304050708040302100209 77
    0x82981c01c04481401c1003000030901d0004c0e07154a511040410000e224850089118038060604d500e01504003030070014000d8403180b0641c80c002410012030300020303461a0032039620b01d0100c80c043e00c0382c03001860f200c08600c80440d02c403803224000800c00c000c24890031007106094502040c40c205841004040b8050103150395084034104200b0400c4811642c01858038042041001912801484441c6c0c03100384240c0044035240c1c1301c41801c030111108039101400074981d46a900c14924140884d0030789034094154080c1c103040d1108089400060160401034100440840e244981500c04031400000307002071005469125801d800130032002403500920800e036402500440c136291414254030b00a0603214145c582006080c0070100002d00d41c46000110b20340100800341e2101040c40200080f100c040316028185441c01404000a03100d03a030580e0100c9070030f0b00601c0e1002c0d10b001001e001c06500350842c650700620b4813040001940d0480c01142c0682d009600b1100d14a548c0c010640480c81480d00059 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 684592374 1250 684591124 684591133
    0x90d03050c070b0405010204090204060216050a0f06080465040606090c030209091026030f04030f0c0608100504050403020c030709061e1419080703110a090509 70
    0x203001c10201c40c43e0075002881080010300e441d81d100031600490300550011001a004604104140e050a1074068060102181d01c0a2064a406181040c5401d240720705814402d0b91400981480411005080d03426a048585100000b0390a00c00d030201c1089000c24074041440c1d540c4400c01d5590132103080814410740b1300d000380041011212001500000d0040311803640305c0c40302051000b000e00030188081e40640300561500325100801c03507605c1c2d0092040480190b18001006520450040d00241c1c800c4184020596484802c81d241980b141000469903c0d40000340081001040040d07035608902666111103940d480b0380302211403000603100142c06800140e0180094a0258065900319220340100c40800034204040b0341840d03078990051280b00c0c0e0f9a0800c100140c1e0340c5042c0f00713842c051004d505071500d00703140c002401816401c84881c003444e89590305990303003941e070080c001c01390102c001183c04565481c0380112864a41c4a00c1c680128141c41d40024034400500520380190322410150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 684593624 1250 684592374 684592387
    0x30f0215090613051906290f060a14040f06030c0203131e091a0f0f0904110f1302180d081c06150507140c010c1401060914090d03050c 59
    0x42140005160b8213842c18003507011800318420000f481c4d03040041c824440866030011f0210003050100c00c41585c40300c00440c1c1001c40c5210f0340c910248a4000104541c3c0e2500c1c1d0868440495030800e169828880c4c4540010b0701150700c052045100007202d29542d0107014030441310f07000f03e85030300900310403605803000c003102402140029409804031160341006018043d503222010029902403065a07225042001e04466481c06c0003540414851020b0340c540000c400400701042e0f203c07800410207403102c0360380d424500c5d0582c2c0356441d004040000a00c0c0d1300c07002d04143e5011000794000d418005421048020340c007003600f041c40c18000065000200141000c80b0000080200c00c1071079810601c0c940d03106000f05000e0032001c4080d0303c800090755910340741c402ca450540c0703110100d101160314070750040e040ea40f02607a00048004500d81c1c040380c0d40c420160320b013010b1400341503030741c1018401c68102201c1031205607e00c00450300c28044081181d131304402500042e021030300d00fa141c408140e80c040014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 684594874 1250 684593624 684593641
    0x605060415050d1b030507020318090c1e030901270809150c030a080c071101050c0a0501050a0c020607090608070c020d1407180204060e0906030307020d030f02150906 73
    0x301c004400d150501901d400c80200c0d002c02101c9880e200c4940c3c0c07010000e21401019418811668043c0031400110f150441000803e846000595481ca2140482030005440b0102100946490780c4141d015084d4030214181030b2112508103d074107007035035880c0c80c0c1185444540840003144110700c07100c0109180c2130980b20b8110035400700f070766650001c03d5a00302e0141140f10074024080208180060740d01c41100f0140201810b0002c1d00100d46ca420500510004c203101404000703030120709003800343d640c0c55482002030801040e140d01421039440c2204209414483d0f41296007c01c42c1c903801d5440b903640d18001070b00c52036140c1c021580024140c000081109018074190240580001c06500c1582e01554800e02800c145805100841c0c010920411003240911071442001b602d0304406d40c00c240c2040300062600e41b0a4401d130b80300c0c2841c040440c0454a0600484200d5a0094151142034115080281c40c0d203c21a00e214014801c1250802c03189280c003e4180c001c20504025142640f02d0205 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 684596124 1250 684594874 684594899
    0x240504120b090f0a0c0f0503060105033712030f0510060e03031b10050c0c120304030c06020d0507020c010507030c0807171902010605010c050d0c2301091506050604 72
    0x100041e548180c882903e05030074100188000c01d07204070061414981010f2000c2075107601540402d000b50b218600520090b40c022600303000508041080ba440001c0107189001840040350702c029003080d0042c0e81a090000ca00c000c99190032294806224040310210300e00101d440407141205c015803072680c2840036a114980002d1146070060840741020101d02d41401580c40c0d07240c00212540c401809265081014020316502c00700c00402e00b820020386107a803d499420401c1e01c50805000000042c040500a0401d0036500760482d4045407185031100320f1900038403003070311000098494204810120342c441d104440c422641903440c48050682c60b9144102c50300001c00488150040503d0010f200003003c010b4880c002029124061501110f84040e085034080e801a50401681c1c4030722901003100000d028000e60901d142200c1412003e0601c40c0f54090340c1001c855501403800b508041d089415002401301a004008003071200c1c00c0102508201d6105100d040e0b0014414002081031080d03248 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 684597374 1250 684596124 684596131
    0x60a0512060d020f2e0306300b090a081903050a29040212070c0c060201060f050603070c02030f100b0d020d030f0306030c1503241401020703020604240504120b 70
    0x104044060411701020703c21140c1d1000c9100000b565080e041142500841800f80d9011982c21043c1170010f6444103901050189800540710200a9010880d1000100003400e0302c43e400040d603035140d0b1f2800580d08151000070300800e0002c0c2c14080410800602e51142c000b4602180000c4a91090039000700c0e00d0740c3c0030900d8615030003907082c8451a07941074045c5105201e0101a5580c0d142d640c08ca02d03258041400301d4100b0011a032601c9014000310751030108001c241c4030201c4246440355950b0104480031852000d009405005001c51415091130006882ca01045a8981071180c1c0a0820601c80c50541035440a580848100d1080d4042402026440030540041c0760205209440ea00d07400f5600c800d0740d01441e0604203140741c00b64501c1c0e0500c1a164002c04245010f0020743c5480e4001c40b4078105401581407099010301d100680c0d038002c10040f401141d0140c50551510b1b81d135003040d080c1c40103801c4000d82402044011011581c42801158140d50110480c503004d04841c5d261801c2604004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 684598624 1250 684597374 684597409
    0x906091009020d082b0203040b012607031b1208030703020702190312110a02010e120102040f08010902010e011701090b1507050a050f39060a0512060d020f 68
    0x7550f1400c08510800000c00c03a41c010954642d80651003610041c005800001210100901c14814040024608040541101c0800450500c0f000540c40101e827800c09001c00c0403154845c0c407400004001442255130302000310301c0c5410b0034007692030300c082504100f040c0b07004002e841c041000561407070180d4041d001150011b4454440c811205410507200b0362135030415135082c854003001d90310040d032000d1480410b0200d070020f03100442c103e90001c0c2c460262628441d206900340c454844100a095040da00204580107400807655a900c12050081c54821816400515182903081072540204442030384000c6880b500203440e840d207240c1c0e2000300034660642d0b610504803a0140c0c05410010003500116000d42c000c1e00750701080b0f103841c80c5480310320120081c45070801c04401010000c10792141041590171007881c202e00b1415014849e245d0350080882d40d01c03c5000c61101816036004c00a840801c070f410065500f0740c6c84580402c030302d50184180086d07020002114a54450074510b1040244106a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 684599874 1250 684598624 684598639
    0x103140c031018150f0f0605030c0409062c0f010e030f0703091a0918010609060513050a03030f0306061b06020702030c040c1701050604050d03050a021906090605090609100902 77
    0x1070358804408620501001303444a4550b2503161038001584143d014520543c10100081490301d000f00b40c5542c041c441c00ca1055640d181c190050041c540c210300b00c5030310091006a9049501241d03090440c5021031103404a1040c0382607412183c00500c545883d903043e8100540c10a94451b04516081d404100304808001d08088002208461841441261400101c17895240e100e4a401d00400401162300b51404a10a900401400e500184010300742d422030b1074040d0360b40d4905042c661280c4215405a908121900c80000c20302d131f8484070007440034845030740510810303644550403200084245105041d039025416100c00003903265000f005d10754800b4050f62010b10340031b000102103411611508000c940e0b00c0900c0d0b80406501d800d124050038085030181d007082e06100200d0905181d030304008080c0500010140d50050081203081684c000b41101c58002d004c17580b91440c082c2071812001c07506141002d011032102c01000c2840d51161611900070060300320000c5186001e000244001e0340c00c00c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 684601124 1250 684599874 684599921
    0x112050712020307050d08220905100e0a020f0403080a030e0d05070302060c0c0f070b18040203090703290403031a0102010506102001020c0f060708150402130509040501050103140c0310 81
    0x4104a070009004048c40305401180c0c90039503558151000100380e4003401c2c0d1042d60510050000401e41c2d600649460310041c0c80e00176030500d005d0780f4810707600054038006e4003280003414141d1580098605501c10310a9031034004006500391814014414000c015030132600c000b5528506010140c50341c40410401c51b40d82e09250002c0d181005001d405c600c00520780010700c26100c00c810a44070b0900c94040d00d04520f945070000109440384418040100740040b5212a52072200d071b0362940d49008648462403003041d06084c500500101204080d01454042e08442e0700392960061041c9807051001626503400a80042c008542c004d030781c1051031861000140564541180034409040b400703285900501c0079101134050075183c800011b20410401c00d01008004001101c06210300506501f6600942c4901d0110055180d040c3c068028a4005461a0800091200c1508003e041724081c0d41012400c15815019584501c0c001c05500d8041d4402c5546071444509540480031020300103405114085 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 684602374 1250 684601124 684601147
    0x11d030f18040e0f0c0a1a070503090306090d09050a0311010e0402272817031603050706050901021813110406182103050309070b030112050712020307050d08 69
    0xe07a04844080203500050304e0603001c51003080100a800e004840d03aa0405140c0105500892241c10505612000c00f10300d40042101c100259000d16a004056a0346890030818096030f0b90141b102140004960790307800552400c01c00a1041921342050fa5154034242c60b0006444130b005680c4650780069003000b21810134511100f96124032105004021052041c0c0410010040d1460a80d401c0b80305107260404207400440c4100c3c000c9500d6a48040400e140b0f8440071810760080001c060b200112035001982055807110042c140140f003800c6c10885501c40c140858202c0c081e680c401c403941115802203100c286484d407003035a96407500c14408680c5405c5d6258080580d003042d44007401007424556a114200040e0b070b604000341c104140d0b2624109120004003400101c1100702505002d800804919041c0061100304043c0146900c440c0e80c1e565034070400242e2503a404425600c0340110709001c074003456038140300030100f40c00800074484c01e81030170100800d1848040381150b02c000308000780080407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 684603624 1250 684602374 684602381
    0xa1b020d0506091515030a0210020106030507062604030e0d0204020712051209010b03060406111b07090f020909013b070323010306020a090305010f02040503011d030f1804 75
    0x42242d000909180d00f00070050701c112a0f401740031080010500040c0c54501d8500003540150b035501217074050082da0152800345e0041802e5000a032040c080c0c0c400106460f038101089503036003d454941d003a0f98101d9842c00d4420400203070390050004904561034941881c2c8062480045400103200514146032039941d8110110545544000b1881c00315840350f5090101141560284504000b409003980c42c100003525a00010b1008110307950b1a60a00351081d00c001c2a40d1481040c0344200900c00065800c4555a4500c0d2245820302410000f45514410450003602e0f03403094050841125a400c0603140c00c422002000200343c1003140d495254030680d5101c0c001d0306a014000c044031050f080020f4000c00360786c2c00c0381100d84003800c402c015003980071111281034110f0b0f4000f6801a16403486000c11180d00ea0250b01c00381031036080902800100c20356034000c00449404600030068210341e5024150355a070b8116400d4400c1e0410300031003040d580721b003004142101961f9029240041400002801c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 684604874 1250 684603624 684603631
    0x80f0115140d02040b070f11030a05210d1a0405010b0a12180b011d1b03070c0309081e0613030c080304060209040e0a23100e0a050102120f01050103020a1b020d0506 72
    0x35028a404840178000c00681c00040c2c050180d000c1d0614035141cbd2126a95252001c40b2000c0b11000b955a03c0b0b5802c80000941c1c500c03540f604428410f9804000a2011000c3c4403024a80f10385c3c0390100003d865499030007203565841b650b4950655040780704c3ca03054002d040c002d50f65104100303480110b4000604444899020300080c0260071240303041000c0c1004c5680c002068824007000d0f80c445020803007038180c2948c0e0301107406d1400c200426180e24080b59525920307400002c03544299a1152800c0144a0300c11101712040e00c11101560b440505407102042d0340d02d00a000b144440303c501d808200900029a0b200303008890251800b564030011070b04994811011000d1a0000f00f0b0410422021410758000c050b540a40b0380400d40d102c0b0003290f2100726241c804401c003a03540c80b0703c41a0803418414100304d2a0450000c64403249150b5005e40c40c14002c4460f5403d0401590010410b0340c00b0303200340c0e1001d904503030320141d1001040706180f024028069041c0c4e48031003144650000144100032980c407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 684606124 1250 684604874 684604883
    0x92105120304031205010b09040915050108030a1b1718030319020f12370207061107031203020c0f070605180108041115070b0106080f0115140d02040b07 67
    0x75a4901070500078010001140c000b01600d08020041040c003920006458945004440c006255089440d1100c092141990b00ba10f0b4141002c00000d8850300100c043c00722190552200c1601c0e42c1071440c95140c03a04e05000040c0342400e200052142c030000c0c00040c10241c0d4410083c20310203100714000a241d034000301070a001c0088106c46010701e266044c8010f5a149030741d4002814050f418040c00c0301940120784110b002211a60082041d5800501140001081c41c100e00391102c014500300030f40b20308107401044041120009185c03c1a10300046040803644c02c420707144160151500220081d500104000c05288119441110700c81014443e0000500d52901c4a6654503c680350007800c61340451a540e050014001c10803000c22551a5100b4911404548000303060b6a2091056018081d07140060403503040000040741264200d16480d015a0101582c1c00c2c890380d072400c2c00000c098600348008000307030030301c00b1044080202e440a41480c5400301c4015040944503540528070382c00c8880300b940c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 684607374 1250 684606124 684606127
    0xb220c050c1c0323160207051504090b0607051009020a080d0908160b07020409020303041a0c070509241f03020d0c26060d0b0124030b0109210512 64
    0x2d9003960584130358400040031040a0700c410b013406800c2140400b0090800c000705440000c96403072103200380a264084c0800038014400000c90401e4145240c20900440040074913040c0446030b50300d000410b45040617881401800307a941101111000b07016001c4089803c194849130100341140180036502d5060425581c00070002d00d040c1d0306030314100c1d45a0200101d1008900c040c03048801c0e82088030704190701510041084201880428614410b40c0e101300c0a0101240034820212107c00c01082e551228508441955880300100310541c60f007600e00a180060345030020a5400b44052101a011402409201541c001c0340c0d04203250084040200006680043d0240c1040c21611652200010914200c82d0030329804000446100b09400e9001a200200340002c00342d94070581c104610580c04001e200d0703103594030b15a442d40180e842880b03074010030003880003400080c03080c4216070700047c2c1650f491592514008480c00d0412144d00e426101689900004020850400241400f601040c4007903 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 684608624 1250 684607374 684607423
    0x32512060b0d0b0a0b1c24290102070f180b1003060f0f06050f03180307062309060121021c02100507050c091312080601030b220c050c 59
    0x74030880d02ea17400d00610039204049401103101c0c2c4e140300c06000f20781c00340c204250301d0080c20b004c402d907007094010300e1001824104420a00250008041402d030300d01c0c0c1e2810004880b2100598582c40180a4042e44a645000411803c044819880f6009407030701130000d0054420000310300704500502041011945841003080301a09c0102d140c0024400a40300f80403840c01d205d002032151081c8144440081800300101e078400d4801742d44107828101c000300f00c0e40e4440302e900c2d04401805d01105e00c61200c001c05c00c036900c84074801410b1180300d1940b05000c0d204983c01c121400c02d2101103040d104903403103210f02c92080162200300c0c1000a40c0200784060640802620402ca90b0101d22040394013000401d0121200083c27000a90782d081da1000c6800580c665180c000e8071a03802c03c1004040d05900042182e9003400e03800c00b072482d01924083c0d0f0b050085101010503c00b15950070f6449654114070078200801c0c02101e507010340d0091181c2c0c90810301d40798402c0251850400f8a1041c4006210720b10000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 684609874 1250 684608624 684608641
    0xf070f180905012318040512040306091403070f2019140118030303050421030e06060303070c0b0a1e03020408160608071116080c032512060b0d0b 64
    0x810f0700c141c1140b0380c9000c0030000c000f044040b45d2031403d03651003500c4807000c5030400c0300a01c0300040482040d4070968949641b400d044000d004014401c2c0c5611130000c03a10072544d240801111001a04003007000ca0b0f55140741d81c0c0d2810580e03642e900c07442850115205a01542e90010702c0d4044890200180c6107007420700780501c055010080e52141840b034004840030f060003160500b070040f01e4044c10006541c1d5100d08210f2031145002e80184140d42c0340c05030581800d5010f921219044680c14100c0303a8654800d801d01d82d03244500c500c050300c4100458010402c030303004200180740c103021030f2a0415200c0c4c116251407041d0703240d404400c8040307a00410140f002c09010024202610040b90001100a1600c00302911106000e4116002c00c1603228200d15078070b4080240c3c1000d00e0280125148140c1e031a9101902c40150041c5035129020b8000c40b002000302300ca074503981524800080d00c0f401ca103040d0804846c08003001040303414a403a003108800e0b40d520510790204540c0610b4460381a845c258aa = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 684611124 1250 684609874 684609899
    0x327050a0303031506050901140c0a0209070f020c0f151309020c10051311041d03030709030c1a0307080702070503030706020904180c0909080909010b0703020706080f070f18090501 79
    0x41801000000d00400c040da0389e000404c10b09484034000ca045c1c0d94000b00600700e06021081c00041e402a00c10390070311035410b900c401c9961101100d0f900359900c403581101000140ca1702011901d030b00c203d4042c0c1c0e1100224552009000f003130551110740080d507a540000d0400d980242098031480c2d0440016040c1c0f4075201c0c060913500030b203110200d4121841340d60b14240d01200c00c036070483c0540d0380c40a19211031060b51401e142c05a540008072a100d2038003080041c081c40850004070740c101000c003c0050a0b0010a40018041c0e000e800124103550761310100f00c40b41100101101d04520500c80001015101070000303000c0d02d406484003690b101506028041030301d80d10f04014014503856000700b004a1a1243c040d0252504500041041d01c0a424000414020b1003051640071078120700000d450504000180a01440b036000d40e4500355540000b9180950212880700c00c40000310001010148070300155041071989060904559a244a80c035980380d0b11a00300603001541c40c401803113050705080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 684612374 1250 684611124 684611129
    0x101515020a12080402010210020c0c1f030c110d0318060e0c10020c0108010612060b12010e0c0309060103030509060c010c0906090b090109030b060a1518050a030327050a03030315 78
    0x40c41c400f14102a80000d643d00300c540000000590302041c000002c1d00b040c0405103a10700c00a203940303080314408102d8030f0404140d0f15100d010034946040903865501411034004011090006022807940250003038019240b490284440860000444000a607440c0316014070b036506100282500e090703000a100c60b903c5000e030340030195886009460340c42d0ba8881c0807641580c086203814480703051401050340140000d90424002031f600411341d1400e1000c14820103040f690309090b0b07180662901641c03041c15220640720fa5110342c01600050000c24002d03001000030441c042e102e1840c0540d00740f0380c94219440642c81e0800200090380c10040706620403980806481c41802661030301d9040000a801601c0500c4010860f81054002820356640c0c005004000d050119600503842420040100540c0f002c00c3d00c0c8500c0c290501e004199030422510031802c1e82e51540310307030300810392004030503041600080d41c0b80801e880c4130300042415241c0300b20201c025807194a020171400314911218030341340703403130b8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 684613624 1250 684612374 684612377
    0x20403020306102304180506042a29070614010801051614120c07140601030f11030a0c14010206010e10060f02070504020f0d0f0c02101515020a12 64
    0x900c424071003c0c43d48000300da804c4c802c00000e103207802c0c040404500135051455094491158100e142e4061010200c0c00511580c070031080300c00d00400c3c5242d0041002d8000d0070304080c400c000803060200b40b500203103240096000071090740c42c9003244501c3c144940d0001c1c1d411904580c07580f12240c04180812201c0380500700c072400901881c50190320751a00000d0401078107081113030400b00020390104a0040303824842600d10344554030300e0100080c40499208243c02c4400002c0d2191411803000042074960580f03134171100100034031131140c89600c2152580321a850385801a154074800007102c54002000501e401000e80ca0068a80c0001900305a8142e1048504910704000c001503049c1c000fa001d0f0591381d290400d45003240488204a2070a04250400c94100d0320015640c0340f000c4400001d000c3d8095400d4003800075441042150040e1410308000c2e001690006009500c0b84041c0d4003c4203a404445480961055640c10300c03040d05084098000096003024603068140100400300c2030b00070b2400d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 684614874 1250 684613624 684613651
    0x10b040e03030615090607050106080715140706021605210c0c0d03050c060a38011209021804050f0a0804050907050417010e0f01060b0306091008060a020403020306 72
    0x820003440d44038407005009a1081c0c07031180340783d143e00c24407206464000c8409441e050701c5852a02d041d6000f085075003d04c542d07a10442000052030a4004985001e0300d02d01d5031194100950701c0760001203500300ba00304a4000342c080c0036840803000c9942700768415500400040a80c0c11034480c0003402031036007010710150b4039030420030703071070340c040006985049050b040d58003143c102407a0a0499542c06440c1c9400010b010314402d01a0f00c4a00d5013020002503400d40c42981e0300441805442c428104da041040712002e030103080100258083d980a81598400300800b1036030000b150300142580800d001e407081584a804d06010610000f000440c80c803001100080c11241e00701d803100e506600851055510440024001441081c4141d095400a0098003401c42180d1680380d21540038102c2c00c3e50b2440f56104800f8012070503001409034a0465801240951071500c82c070040c004030020007400011201c18118000409000c2003246030b10843c0822001610341d0b0440c030406003002c0003e851812020131 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 684616124 1250 684614874 684614891
    0x504080a150b0109120212030c0a060c0e1002190c0512012702090415060e07080f0f100306090501060b34020f04020a02010902130f05010e0709060c151a0102010b04 72
    0x4126544c0c52141b41c0444040d022581501016032a62003800a0b0082901802c10703002c040002d241c002e542036100079180e00400054180510040c1043d4201003001039011410b06058150b5440c800400240078007032040c4c0842d100c030049440580e40c01ca001410707a40d42ca08443c0d01e502d88a0b4050010618540e0070b2010300300d41d030001445e401e80500302500800700305000f80460703040380d80304000929480c00d000d103e81c5480c1034041d19402c03080b0b50b04e4910040c00c00005450000340c0c40681d1041409090040d60142103489020040107441000c9409641e10704010840c4841180a846400190b03d000410002580c900980b01900d00d0142d1a0000d01c11003800300503075540070301a0403c2419600181c84000030034049014099200c0003942040b0107030101002d00e400c1d03400c0801280c550a1050000341da03920a003c014050071100305001a0503100b0a000140c802c04154203424018001a040d00c2150f0036000100c0c4c0c203640c00e1084400420120000e607580a019007800da60781180e04122044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 684617374 1250 684616124 684616139
    0xd080c0909040305030c13091d060f011a0f03010807081504150b130908030603070f0f15020f030301060c020f030a0314030c1204060b0909060408190504080a150b0109 73
    0x4002d4001818400e000c400642410f209800baa13044d01e1040c18038002003940c48260000602c0c8011282d039010f188a801c20ba142c100006503075000f002e8150601c05540e1a091615a00c2e40010502c500c441c082081050512244080954041c002c40c04c042d28800c0e203080c04a40c5092040d00d0b43e2007100c14040100301c0483d1280c04000c90115910401117051074440b400504010010f07510500c845180c80c00b94014400440c0240d407080b0420f0701121082e6440302078580e050183c501c10010f2a0342a460103100c0014020081d02451140c0d00441d00c0a800380b040c940c0c10368009070003d0002525140220082d4540401032040075902540540100091618010b1201c0e04080d602903a4010001c08102014000402c03a942d0254103400907240f4105460820043c110382048588075654030804103601100c04102103000c0c40c0e02c100844d00c0c0000c51101c20841c505400500c409005040c00002000c01d02840540c0c2c05901c071710350080d40400c140044c00c0c112030201401c0f90400149031421300c120b5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 684618624 1250 684617374 684617389
    0xd11031e090f030a0c020a09022208011a061b07030b1f06051e04081b030706051908070207050d050604030801060206090d11030d1b020c040504030e0d150e0d080c09 72
    0x134a01d5142c6a040c800190001c9136009400d6404100f5403403000501e03001d469429800034000705004006441119a6400783c24281c40070b44541c90401425201e80c03440c2451700000030720344008180300201912440d4591181040000d81c0280c640c00d101c0000c1101c9801c10720019510080c10012040d1114100207004190740107842d0410f44c0c0000600350400c403034401d9410b4500500c0c0c110119849400300c0c7c0108000000101c04060180c8207500b404034030075001e41d0580b040142d4a960000d04a403014404507211a4054103940c250302442802194544900c000d071508507001303400804a605140c0740060420310168001381c00c6400440504c4543d4602042c04c2e0f09805152500c0e1100c084400180da0551040c00740d00c4100320b151500c5a00c18a6070760485940d2802607030281c0e00700b9050881880706445048400900007100039010005510703241201015180c010740c0340d46040448410004202da0107102032898680c4102c1031040100c0e4400320b6241c0c03011804200504000c0842d0200758103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 684619874 1250 684618624 684618637
    0x5010e011812140a030c021507020c0108040f0b04141b0102060c0717040303090e010f050a03081606050f06031b130b0607060f0204030b06090603070603020d11031e090f03 75
    0x101d202c00802c1d6008148500896400415154116070f41c4010103180a4002c061440c00384015000d1103045011200613403040511a450540142084500305001181c6114008000321040d9840512035004200032103401c80c8107034460400328901100322000d03c0c2c5450983d40d200f0021001c00c04c0d255615980c0481c403503400800024110351107030001c5c90b080b240703604c40181c206000358000c0b4000050540c0444454215420442946800e07621036840001a518500400d0741111a1a0003000050284401090307100084420210020800d6550505940303040e680001400d140303000340301403880c00b40000c02d44c0400419002d10740650321004a40c074000e0148043d45403c1e5606d070601c510341c40d00b0007140d82943d4440d1013004401c129814000003034126000607580070207080c000070000e00f0300b00411801910010018000e02c1e00c1c00d42c0840103540405d41d018081a11040d4100c01c0707040c0c2d10003850144041c541118507045008081284c0c05400a0082c05107910081010305001d101100700c880 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 684621124 1250 684619874 684619883
    0x61e0f1005010f090e13060e060c090609040209060304150e032502011701030303050907051203120601020304270c03110d050705040e1f05012c0f0414010305010e0118 73
    0x800c120810000c0c1c94590701d0ba84903140e1096403c0400420206d62886918681d01c030795810807924003104240c96443c8000c40304202e4525041110081502d0b084016004000740144090b140201403004922250020b40701160030369901603848030040c560b4015107516514200c0158108403107001420040c0c2c1800c160003030f02c424001103070001d5911520044411424600d40d041c81755035207150050042c42c0403154207125001c1c041003c2100e1034000d8812600c040d4010055003028415442007143e80340c040c05583c1544000c01000a500c2d6289003d408a00d1300d0860038084000c0051284081e250303140082010186070000b00320280c20f03c0820789111a450580000d4165151001030f1414851508040c484403900c004000f41742c0522403090180b0392000e6500740440395980c1c015110603032030748860f11080544c0b800000c40114880c2000c501404010030400f80c0740b0445d0040b0b004c55aa0018801c81649400014400c0c48006d000c0c88586060b030780000c000c0d00c24440d50b070020314591a0001003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 684622374 1250 684621124 684621137
    0x240c0417070b07050d030509010b0a0608090c03100f050604050105090415090602030f010611060910021303020d0f1e05060402010807020c03060f060112110d1805061e0f100501 77
    0xc0e040d050400116002e0000b01e0880d583e255020b081c115901c5a000e91400002030034030000414030705041c0528040494040d003103406603401c0183c1903804850040012805115001101100da90208281410700030300b0480080c24031111500c0900741c8000810050045080c800104540d8484103851503005401c2514030308407025450408014040700400541002d0020041c8001070300000c451504030344640d2655500c0416919105403200b9040b03649500c10380004140344a4014560024444003d0b142c04014007617442c2e070b000502440703000c00c050780e100301030322001c40800c400c0c03a4109024a2440301ca12031200301984e2441e0b51440018030007810404000d021591030703402004521030760b070300040070341d400da1401a42025100b2400c50b6194001210725070207400c1c070062441161a0b11803ca4440c2c0e241924403140e00025000006484008001c1c000560001c84e0042c01b00c140164070070a5084100110950403e03d0750343d018010718901a0b00307030184425030107034805040c1221000c2c01c101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 684623624 1250 684622374 684622409
    0xf040303200406090e160818070f030b07020607051804021c090605040201260406110403020a0303020f060c04051e060c07080309120a26040f08240c04 66
    0x18104488224580341c0e0101c40842e01190f2690041005000d603000400ca40d0456a1044407003203400148650100c081240740c00480c1c89407100350b5505640020030800c48141030758030090145001e14550040e0b4206c3c00d40f1081c40700c02a07061210b21781060051405c1030400441c030440c0160036100340d03512480f40d80d000800c0940e5480041d403403005004452003c22000c4411b04243c0c0c09081c080b20103d000400d00704906e81e00080d0710071020070888058540c004030781c6c2d895840b240200702d44c00000f90f100c403080c0030000059031204240b00c0594842d50141615090a50089140c0381c0058010045072206000a0105440302c00f03110b503058a24080d565100c00c00c450220b0082c0c4115a202440c900901c0c41c0440e65010001c0240900c0c041603607560f5440074600b540c261640b0f4644402080355020341840c00340c040c0142680503015480e451114502541d410000b020a042c550000055070042d03e0780740e801004400200e290b041000045405601e00b031040c010403440749000e0081c0603c2c001c0c80d030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 684624874 1250 684623624 684623651
    0x13050109060516050c151809130215091012060e0c0a08060109030219031a13150209061308060f16120b0303030f061e0609210604110a0b030f040303 65
    0x6115000c601801080b01704003416000006c03540309003031603141c08881120303180c3c0508050f101d45200c2c0384617000c900c602e00803a50030042c0d00c0d21440c2100034070403001d004c600e8a555400c10141c011312103d0301c916180c0309079103074030b40280c50841d8440c640035404c0340304100c8c04000712012503c5c2e8850070b280c00b84c001e980e000c0041e81d5914140d007010750080394001080d0001507401cad6002e030507a40260407100b04000c241842840205c001c40c1c410402410804c0003074006840d0340c4010b07810050052015041503e0417002c941c4d5900174102100103226080c8040000c030805000054000800f240303e00414030300340d20404102c00400f044075080003403003c10f410010700181d101031032080004050300d0f0303a03042042a2040307508058580f24850040b07052030208100d200c0150442018000d000c0d0341c208000e400030805115144410f107148051200d140c4001d03900d0a21000344500d1045027200102200c15040c8a141d003190740210102d030f0410030038480650618072126600130b5146c80d02192240300e6014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 684626124 1250 684624874 684624883
    0x70803150a06090e060f031501030b09010f060b0706050403050f0c0616020c10110a140c01110708070510050d0f1a0a03031b0f08030106050702040b011d0d02150f1305010906051605 79
    0x161510424230348004410040300c6450107000c0c49118000740a0300e180345810408440d03a6100b4110501c1d070800004001680f40d400040d801070013803d10702d04280e800308100506610194910400c3c0d0480c90400401a4101c020302404240318401088440744a4000c10b2800120300214030a00064007600140800300b00200c200041e4400500310071141840e450310b0740e40c0110710129012507840c4080d02c0e1713032010010382d40c001ca60701c92000b0400710b444c2c10180100d07a00917041070020410100003419008031b15005559500c11811000200048401e2140310351040030110640300381071030b103420004a503005540014140c080528110810b65929100003011040c03240280f00c0c0801000010f07000340c202000c2c1240302d009840603c1040b2008004603100b48010081e55450780c5031141500c03450800c415001b160501c081c00f10310070920707100301d81c000365001301e01a44035030640010360408403e5803d480030003c2c003003802c084041506200002d0154094000e8410301d9002c20304204050100412 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 684627374 1250 684626124 684626143
    0x4080904092a08010605030a0b28060e04030207141005090607121d060f0a1107090e0c1206040305030c070c050d0f02040e0c150a05070803150a06090e060f03 69
    0x41e440115202c015454442d00002407140700c1c0035510307003500050641030105405c3c42003a4482810300042c4d440c804406108040030f082154889076554000380c01500a1055001034071406148c0b085515007407078003d1074038240f600000000310080c40e1078023440d1145003000300c03520070345d00300a038580f14000b011130303400c0c0111a0b0180c0320010b00451610041c2e080b12042000c8448403280445202407802405664800c920300b54081c0c10042210070002e078440c10f040c3c0584060700d0700762008a69a10044810780307017203250380c0303004e40c1240110480e2480c19020410480c0c50390b0340034060901c1c151b100a042c41c04018400c40c1086030005a6004008607008100f0240c08001c00000019040d410014940b60300c1030780c220701841c80d00e540d000c542c0e0b500080d8a4804040140409071000000146481e10b410155483c2c09020040c045030f000518420040c4d0b00c2003050071b1305140018400c10400440c11319940c0900107018440000340712155078542c42d01e0784400180e42e4103a00300c6841c40402c1c60080300d407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 684628624 1250 684627374 684627413
    0x12050904020d2307020a030c02120f0105010801060918020d0308060a081603060b121b030a050102040b07031806020a080915030f163011041217030408090409 69
    0xf140301034036084a54290403c0b000c840340410181c1e40704407081c2d0f55001d41000c0900400c0310003507000014904a9081081c411050003900c1d0307000c00e032901c80c42c00d543c020380201100341d4490f2010300070100b0074843d10504504400103020308280903000302e00320190710507002e1b08000c103e0300041c0064803200c1703482d8018555401115114880703081c40380c8034920741d800201c4006003403039848007043c503152407000c1c0d480d08400c025149940051072264400000000c0d51500350040c6001e080c0031410030700c0507000800319018026903505013843d00174001ea9809401c00c0060200d03030810b0211075400501203040f6070344110510360f038a00303100010b801644041e5803011840030000400c4891130841d44040e01482946104500b81568000d058441a80201c4070020340c884c078032000c8880582d1441074600c1c02c90f900c04002414552a941218160b005420100b502140d0110a40c01c10445405a01c3c0d82e01c5c428150b1815810284c0c0d8a41c441e12980c0355042c421600c0b4800c441c00d01004000c0400c0d0550360b0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 684629874 1250 684628624 684628631
    0xc090b0604081515420c070503070b03010308190c060c020d091a0909150306070503100e0606030c180a0f05030f0109081909151d0a0312050904020d 65
    0xe2480301c510012044880700d40b0400598400344180c00d141015003042c404c00507076040c6172811062030a152402c00302440c01c2e481c8010103c6811030380c0c0c000040c040c04181d100905212424072007070520700743e248d034844070744001c04000400c0482e1060017074810354401841c188400c0060014219402c03d60f150b0050902d900d044e00c1d0705501900002c01020415042e20f0301c550311556000006c1c900c610f030009848012008000100300b615000c03107425444001d00105103842c1d00c5110109150030821500840452000002e018850070003805820040504d101c0ca12359524101003c514203001c0640103a070700c071a0210311104151040380545100c40409001c070b07180326035038084c21054140c180c03080c14021b028142c4110b14403181806503002d2950024101e81c40d02c143c5030100100b607410380f2040c0b8100a2249800315245001e0303803240d400442e0030b9a0b4003d4022401903800303401c8051103207107482001e8084081001400b1030000f43c00608190038801d403540c4106011801034030030409520107140c03a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 684631124 1250 684629874 684629893
    0x24080916030b0c0d020406050306010e10091a0d0f05072c0d02032104050a091401030b0c0f071a0108010507020a021203123408060402030a0b04052406070c090b060408 73
    0x40c0200a18400c241c26600d00c5841c33881e10090001c6a031800088100080310b680e0705100d400500201e001c000429444610301c4d142e4200300000c1101c2c031000150b1026511030050080f10340e48090308054800d1855003010b5000c08e9410340041c0364030a12511402688991b04000c01d5540500c141e80400c009403001010704007807800100510381c801d004442c41024441d00202d1080210b11403036443c2680c5170381c101c020780d0a54640c4940914003c06044802c8403c100e20403415004c003000e0400c0c01d10a600b0340f0468403036038180a81001c0f0581003e282c40c6c0c942002c100324660300003000c120303aa4041d565904940900d0440909500c40c0441d510030301fa00780003e001c020015010030441e5070710200321080d944120200700205600703a01c0c0c88180000e6001010036400d00c0d0650086800c0006642c0c0010a45141d00100702a103030222400c403c001003070b40c406010f4850003119004a078400303d81c050b203404026611400100c1d00750241d90342c52641e03003401441d191100c204440280003850202c610006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 684632374 1250 684631124 684631127
    0x4031721151c26030c070204090f06021e030411120c1002070f090204050a170c04091515080a1e0807050a06200f0a0924080916030b0c0d020406 63
    0x40030500112281d04280c900350303c0464400144541666050780107a245464020b440352072500444d00907a40305030b507400b804000400484650044502c03d10016841d44032541142e010304048540501964008000f000002a4840e4025031882c030101c9400031401500261342c0d01d044581e40025403c02d80c3c0668046005400160315030498000c00300315411076454003804c0082c0d010798030601e9041900c051050180040300402d0920040841044844101120340043c0030340d507810409441d100c04201203c500209140944d0550dda10441c061b4a0146402c080381d580b441420b0000e45003081c030445120b405001200340055031074006031400e07140c076240e0401071b440f003080c20000c40380d40746400d10702509003000114801c00820072211042c14001c21130850304080c1c0c04011580c2c00c210030000d001c00c000700c54620801101c4101405c402c0c00d506080d5015190850181611701981d000d030203052215241d24540d00c00f5640e004440c1149a141c1032607801040c01649404c60100b800800c0104005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 684633624 1250 684632374 684632419
    0x110909030408061303020606011b0b0705070201120608060105060c010b130b0306010e0105060304060504031e020705030115030803041b09050403020606041b1403060609150403172115 80
    0x640c5007409407503e9458400c101c0a1054034960024090780200d000240250b000d14440ca04880700384c1c3c0700300344003242540d80e07002c4510f045031081301246021a6400135540d103d1010751010711010310812801e03082410b100e556140511a035407003002c0004918401715002e40100c00104c002070a01e9211805890707000010f8400690154080e11900000103511141c100c00d440c100d641c040c04a80c80c58850fa199840905801841502402503110a031f0038081c50000103400c0d900402e501038407856081008050a40702d846802c8003603101c1c0300c802030000c40d401d2012a50029840708078070141c0d100703038081303800107080c90b034002c0344824a00803c120a058010541c103100c0d60040f00d080100386147d1052528420034202440000340245200c4c3c0c0442083d04010741d08018010421818a00c62a0008100320030442d80a2031003400414100200100a1002910b01c019440074505050300030415001e0003201c241c44507052111100418904070141088401940001c1e00c1080b490703005072840c0035034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 684634874 1250 684633624 684633629
    0x2030f070b010e06030a0b01051005210402011e09050d1e300c0b060319060608010605040b1503070c06060801021e13030f0c050405010e090609030f0301060c1109090304 74
    0x30f00c0f4440c00241c00d070301e00443c0e0380850640c48200070410741d0901041c4000c2030b071400f185c1c0c01404070030000901402814024100041002403800c032892600d84001080303142c6110403003440003407038810a0b043c5504461440207480b0240c84d980c0c030070030050800800c03103401401248103640700c0410300000e106000c065038142c4460103013403400300d266504048060f03e40325041c980000d000030580310001100e0680c5650484401012071304a0819130740003000d000d45500c2c08550140d03650b01c0c10017840e03800307000b600010401140c00b00f00c00b900d19030124070307108030560007140c1c49540000000c001a0062400c0b052440c1c0100742040641d8840070194006e40c04204094901201d00400d0b03c105a1200304803089001044401464540303150356a1460141061f0100e40c0740c20809804070720303500e492261a00a1046103103061181c02c00d002e0351403d01801808005998000300f000208142d0100700b203138111a928500346003190740c1401e11410301203581c204654019240d4040c017071300c1030001019005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 684636124 1250 684634874 684634889
    0xc0919021b070501021c050c010b1509030f06060906220231030206180109030812011505090109030b061c110114090916020f01050a15050301230702030f070b01 70
    0x1600b070748030030059a54a054038003403880c07035036503290480308180700e60050500c070b001359000480e0090544000980c3c6c24840c00505a0740da101048001261800300425040d02645002401c060700344000030500101c0002c0c8214001d0a280c40702031100f000c006071401c809408064110b441d5000c0c1a151140500c00044403000c0864070f00040d0381c0110031800350b80031a68010f017543d21789006640c8401118002480c101d0600c61003a90003c0481d402c9002061050070b219421886507041011040f540c0890704115400c00c1401e02c8050816600b11064000381c0303420269a017034995400e40011050b20040c0f40220320120148003210821030814904000ca20098960728401040b07002c2450140c022100302c0d503444003030400401c0922181134420100b54009106941036800d9148006003559011b8440c50b107107680d28050292102c41c1440b906001e000c045009002101160003010084c030300c1445c8030306200140300007203520306008004443d0b1510b040c601d4681c8074011414408000c074002d02c101803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 684637374 1250 684636124 684636133
    0x15010b07120807090314030412080c070614070308100305030a1119030509060915070c030506010e0906060120160e07050403201305011203030b010f020c0919021b 71
    0xc0301e45000b003003040d205088558030000b402d4074644440200300031043c400001c45c04100f00c00b2400d480c601204c001c2d45806444c0d09603a076582e4031035172032078100366511910800a4011441440c9640c4d2801c940000ba00341c82d01c00060385a140c800c1c3c0840030280c1c4000c1c000c0c400002c80c140d09030f800c01242c0401510020a1300c1803164000c0072a290115220001070006808110300303802032600301c015040b1508060812001e10304001c102480a610182003034901c0c04400070304104111080016601419800042c0e0b010b50070040052036403000c000d001181480082e82c5a041145d2805c0f0182c10b00341074100840f0f48a902c0300f14030503520b001e980606c00400c4111000a245a4081c1d8111400c880c1c0c4007034290105000071503610480b8003c50302040e07000407030003001540c845850040e00c0c060485410003d59040540c82d0280440c0d400f024040c0c18004500c9491400c0750f00131946c60300c10f10b01510f1911080e130b1030403054003000e14211900075030b403403010071a1100a0f4024030140260f5542c4800c58 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 684638624 1250 684637374 684637403
    0x30f02100506030a08072d050f030a090b07111302040503010e0f0304151e080f06010e0901050d05010b040606030c02070f0308031302030c030f0c19030f02100215010b07 74
    0xd00c15a0300441d207058242e440a804040020390312001461094000d441203a034200c400048a404a50f00000c0341241d114540500c200340441408401400b110001c002e41ca022a80e60b0003601e0000310f4460422a130f5004140c4406004440c04e0040c15a0b0340101424030003a82d100c5008000d4215000cac9901a61a01c51280c4900b40b002450b621520b1500c0003d6003007a00c0c0c0092500018038a044000c20000101c0c0f00900c0c80484410103501d0325040c1d15841c0c99880d003041c074481f44942c028490360421401c03000d907a146440b0300d60307841c1c195401943d0446444d240d07402c080c3d000d000d0010405411515000340041e140764954440c084c03107843c60342502c2203d0741d40c0401c80c0d201c000c80d000c0640602c0042012440d5002030040c06a00a8030240030b9460a11300c040010b801d2024064246c01d060700140403255061400b0300840340050030001c0240c9031385d03085403164001c01ca44a90004d0041e03404c0d00c1500b2249000b0805003812400c01030141001350f8580070100d0583c0c21414044507402100c1a92 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 684639874 1250 684638624 684638653
    0x50a0b01061211120606070f170307120b211207050a02150a2c13051501020115090b18010b0c1b0d11060c011104180216031218030f02 59
    0x32255441c0c1090078804d02034403100204503841d800004122544540e0011140000755038400306217030303000c0070803006450780b070310600240a404044031203000321850802032400542c1c803078100d10117805200e202c03081c02d21740031104cd42c42c10003041614051241d000c1840d4040100005400c020036200303680c041c1a80c5400d01c0b0b909183e0241850341c0d4081a112280c0d0303440040601d03c00c41441820000c00040c275242c1c500401c07400c90050100e5030910fa1100c041201c0c17050a03280140c50f40c3d0081c8001c0080500c241d2236400000050700038182500d85481410040340d071080a071072074004e000031400c686546d41d081c2d140340b680c0c0400b00012840c000c0c1d0304a07080704103e084540d081c2c00400f0b050410768048640e107002c1c081031078425882e0322000038400328100100c02d214821400340c4010041d6612400d00702d03001300060300804c1d40c2c034525004010322017104000320303c1da44200740e26003081705111140722807800c007806543e41680c1c1c400c0f4540c1350403800c0c198800c60340d800765802070702910559140ca100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 684641124 1250 684639874 684639877
    0xf11060301300b1303082508060a0518010e1003120809010e03040801150801110f16080d0902093d0806010303021c02030307080103020d050a0b01061211 67
    0x312040c0041010300442801510a082c004424200d54541084400c41d0307260140c12909492001c8000303414004070003003640203191260030101031001034450a12034209000070f44104002881040b0346107003c55030b00e0302c6a18028010380401080c0c101440c581e001150712680d070910910b0000c0400c0c00204200b44211440d8100380d1703070040c81254030044c507020280c822000240c2604915980c401503400209000e20140028216600012400b1403520788201c01e06969a00000441d900d0115055000f9169500312400e9460b003203821522a041d0f00791002c1c03c0729103a03001400c1c01000240942c2d080906e640300a04940c422241149a600c07102c9280b10810860f80d07202c0c2142c0841c20815000c0840b601c50640400000d0101080561701c4852003070030984284c1c000c40c0540d0182062803080700801001a2010500707100460940c60314080040007800c0600c0040e0141c15080703a1385041c0b00f014441c5512442e041000c105180d43c1d2071600408108580c0000d1000901d484d03d00242890b1a10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 684642374 1250 684641124 684641129
    0xf10020708041202010e04050103060609060611060a11070b010e10150e040b24041a2b021b070603110909040215071718042d180f11060301 61
    0x1034406040c181419003440f44082100400ea0501681d020011041d0761280603050107584601d8000c684146001e1111064902d5600720000380030410514000d031420000340c441c1c1c4515084008070f45d078024070390042501c0c460104081e14040c407040c001310341c00c1d000c0503680f400f0711350350400031707072080d5949446044102c130300203240340020004182c4e01d280340781c1034021001e190b17030007441035000107600d0407400305042c90003160318024000420100852800d280600f4846070148020529010707241001144040c40300405503084030340740811000b2206c1c50b6065401c50050700c5281340183c41105555644c4440c980704880000341020307520341502404005070790344410040c02101c05078640f9400c01c04000b40101a880b010402407000031701251a103034041d0010314001d00710695078442d904070140d1154030326080301d01031070600b41c10004903c0700b505034040b07030030800c000036550341c070484419000b401c1a02122000126200703101000d1244d003050480c1010312030a40d00030342c4403140341448080d000c00d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 684643624 1250 684642374 684642383
    0x2060c090108040b1f1403010c030603080d0923160602030a020d081e2e1d0402190b090a09060803041205030c031317121c06030f050f100207 62
    0x103801280008110310b1019410046240010b003c05048403141c4003800c5c074691080c07041e50700440510200303050030312035480c80102c9481e007409080c1c11600e6403005442000903101c0b913107540b080300c10b0601c101c82140c4160f080328000c80f202c0c40c801030344c000c694948010a128070b004018410001d50f190000017100c0a59074550040d04000d07804402c10381340b144008091100180500541c804011001c03058144102c000456100d140c40e0034590301280c003803a00200c03880c4c441c030031070090243d81e60300c48051031000f40d110405100c0f642c45102180c00e290701c1071506e0074201c003803c0c40890f10907a020301602010f2020b844da40035655903071540005a40241c49001000c2d00200000d10508084c45145400c0c41e0041c02100d10700b2a103020018550b0380010050552220318900030300202001005504c4503240c607038010040c442102c469042a846540302c04030300c0c0d006e500e4214510031303000d130050302c029908642140301002c0c480c240b25884401c680024031550081c5401941501183d100740c58805030070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 684644874 1250 684643624 684643637
    0xd050f090c100c03020a020402070303021306020114011a0c010f0f1103040c052403090c01030b0301090b0f090a0803040506160c11010f030b030303040f11150706090c1a0a02060c0901 80
    0xa82c09507804290320340140c04600504c0f10300b8000d170b00c441c0000c0c00312601c280d03001641e0300b040e00d0300c1c550a00c08903000881103905000d0455a0503e0340c10200341560150304001d0080380c8a000904601d11584a03600c0442d42401c20790811100d20ba4050103000002c00c00c117200421481d58030340c1151201321001060241040d4044c400d50030688c486000702240010420b4140d80c400c020841e030754008854005061348006800d804030350f41800740403132980d0f0030f6009120151840d40c8085580200503d03a0307440c2c4000400041100700700308054040039401c03440313281e90f0b810030341086601c0e10400c03141c180320254101145095180314034841e0500790781000c0f2100d025542500111744e0341c240b1318401010540c03030f40c00303441c82c55405000450107070703100391282d00c0083c07114a003600c4182c4c81d40302042e110b98002d045094911003600103c6d200e641d800720340020784c20041c1c909809e09020f10f0b0884101e40c1c0c620038034a8200c0b1f03144002003000c0c9107039408465846d40e84628004180c1318151481e07000540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 684646124 1250 684644874 684644899
    0xe10061d0a0b0f090a05041101050f030f0402011e090519060917010207210f480305070c050301051302041505060a120e06130807170d050f090c 63
    0x8503902089196000500f2041140e403110001001c400003502c000310019541e205200410500290b68100c80000b0300b0300c0c6040c96002c408483ca0703400b000b07205504140c00c020008045a00c11110b0340742d19244404162280360644800030311003500313030141d1401182040ba03501301142d9107401e0701c0c1c102d45071a41d03094840e5080c00510f00070120120b260000640d02071051070001a074540741f5140040302120403600d4036a1881d00281040c1e180302d501002c3c080018108041110284050100e0f503420005010510b003400741720245a2810a01040c2140340c04c0501c00100340c3c1c020014030070310b07000f0041d00944588550405003210025030754904100c0d0300b0001c51006003800d0b0003205122400907860b224242ea910007092150703100780d829500081d0140d02d5480b00854a2040201d045800c4d0002c102500d84003541600780d44c807940b009003042001203800c0d82001080010030004e40680d114854444005480b0840601003e0350100812411040010000100060854100c1500900d203071a07a01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 684647374 1250 684646124 684646141
    0xd060909050a02061c020712080709030309050111070f060315080118110f150c150402100c05030c120403110103180b15060c0303060117040302030708090f040e10061d 73
    0xa20202281802c021700000201000308680701030440f25000303c00a000c40704101d0030081203400c2c028829014040c4d841d106002190b400319000090f1b44083c02c3c8003907610340c408850791506c01158000d50b2440007426000c20160f606400c032030401c40300d06c0c2030703c0e810a4444000d14283e4001c520b5815604114000c0040810302c0038011000004018102d604400307841c001280c441c0c0d01039021180381d5031000402e80030000d010002c225940c00c54000d502d006040550010307040c68074449810b401c02803003c0c083d00501c00b00784200e41c50500318000715203c40001030b20b1800c450304248016200c920f0814481407465001e0300400300019030306000030070601542c1d52200002000601441d6032203140c180d0045081d1a002d00a0108070707000c00003182c407441c0c454001040c0c0e1f0007144050360301281e000107000c0081e400205480c0c10079440300c41d640d26074001e840403c20801042d0726056102d801c1030031f82180e041012070343c1030f00860713040d00500105855004200200240d10041008106003500041110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 684648624 1250 684647374 684647377
    0x4050c060d0216110a05030a02060906030a0b0a060e040c0305130f03050c0106090203090609031207080a1821030b010903081e070b10061b020f01120509030d060909050a0206 76
    0x1a01046005080c41c6003008030b943c5200341840110303506a0090340b030302d8140c640713001140d00804003100100320300c038078030340c0420b690707005585d04039002e000d011003c50213404064210108481000c1c0101400c181e031f03690002e1a042c000c0c548030703000d18941032151340c050380700340140751095490812424400e5103a55501101c0071100310709608100e0103008002c0e03141000e0207003078000d083c81c032009a100c2c10902102401c01270050400d000c02e6004000b10000c10a40c2d02286a00282c2c60901c0c1c1c44e0f90340c40d20310950140c5a50500c4151a250582c3c06c4c8080280041c01d014181007642111124415242d23000e034115240505080e0220b502a54100700096003040103084661250101c031550701a030701240c0e042a00f00202c01c542a064070410401e6110701e24280c0c1000306824034102e11401d103a002d807000c9214003c0c001900458080c2c903460b02c680d0280804041513004400b007003143c0e01c1d00005050300e81c0c1000c40310401d02810300400041001817030044111090f0000080c1001d200380d07071f0812000307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 684649874 1250 684648624 684648637
    0x430050706060305010204061107050f010f080408040503060408120708221b0b0a120c0909020a02190605090d02031908131208100603051e06010509130b1804050c06 72
    0x919110390b404000101c0a00182009085c1503c4103421441001289404d01005402881c0a00c0c50040400c01c00d07a801080300440480c1801d081c1c0c0c0a49882c2080c01141c440c940201d03405105150078402089000e200800324141340c1d03c0e40140c1a22003c00442d03914030140e8030218000280700e4450450b02c010444c00d038003184140102450786483c2c002c90303a020051540500007102012035401070302ca41200e000c80341c1e0000c40100704070445802d100a0082c0110380158039043d907000c5562a0302d14000c1010f0322007118040800c240c0d0f0401c503c0c007140030307110854206546004e484403400d00140000151113114140c20055440503100c030b10304444501000b4200030010742c1c0040d2001c0400c040300ba00509151559484801511781004501c101100c16480344040616102c200451540c8400c181080000c00d8030346050f0503140e00e0012621801280401648840c41a04100e10354106a001c4141d0007407d6880c511040c4040110b422810780c2224050407540111001c1e088625058004100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 684651124 1250 684649874 684649883
    0xe0f0d080a0c02031e010c08070903060218090a0b1516020607021903211103091504090e1e06060a060305130b010305030903060105031c03110702031504300507 70
    0x168041280c000a01e8500603000c5d460362080700d80c48010a00d18280680010030300c840c140b5224600345048000c007220124800a00103d0b0b0201d07101668682c0320032a14001c10b00101150420f081440b01100103000000c041880344030031124514203008004113a0301c41604940b0503200801c02e80e0213000465010701400c99001e0014501d06140400d0040150f0180d40940007482400c900100743e078401c9210304880a043c040c03400c1610702c0c22200001202c9100308280c800d25410058004050a28016900980c0184d4100b40100d40c01010018040e00382e44445c00041c4c01c02005048032544902098a02c0b582000300d845d03080c40003031b0090b08070030703040202c243c00211824000d0703c6241040c02c080e0001c40e0b194100280c900040d250412466014002c114007501021503a0100c10300071020800e5040140354444c40d00306203803281801600d81041d000f03800e40e0108500a40c800919100844040701c0803680c07110080168a04035440403003a0945464092000a5040c000c1d01c02d500110400c58 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 684652374 1250 684651124 684651137
    0x6061d01050c0724020607020613080a020c04050a020d14011202120a060c080a0b030f0304090b011b03050a1209080406030e2a030708011505191502030306010e0f0d080a 74
    0x90020760090395032134000d01c8110415903410345210003801c0220150001d4119484001404801c020f050f650340700c12640580d60940e01d1a007030005900301810301c0324060b801403a100401c503500c82950020105100c2e030160404c03091282080c00e241c40b140030f0251155140c07a91042d400142000085041040701e12030490780e105d4015034400042d0f03007404c0304810001c0c604805002c2103036845e001d00440300200701c02030190100d01003290303542da00441c407660b042c0a07124507050b030450340038541d00c40040c2c854070800700300c2d03601e24200900180c0c001140080001c0d40c003190481c514141e803241c0c82602c1e90000e000c0d8506481c2c1a4224003800c182c40d0000514094007400302000e0911410645008821201860070b80030300e041050b06011981e8410ba00c141d051604e0301490f03072400c80c00b2400340c03031041b1813440c1004940c5000403200381c4140c11803000600240b07000580c694002001d1441030100340c4e50106c0c5612554144001310b280b03182d40326040220f0503900c1c00040e607041e01500d0019150718001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 684653624 1250 684652374 684652379
    0x2107050118060501050405060d150902090c070309050316030204050406021213020a0506071a0411060c0c04150518060114041403010e0105090d0e040906020d0b0406061d01050c07 78
    0x4508407503044054120060a040c0c1c5641000550701030b60b07004042c11182003103649424000b00f4030115041100500c00610004000d66820580e8003034901c041d0040c044568a01c0d0172100c0e071440b580901c40c1034012840403840083c0350315001400805411071680c42c0c10205166a00b8800a402c02400c00c9519580912a60003041d450040b041e10804201c040c0c028043d4680c014030881c902c0d01c1d001140100c40401926021a45c001990b86034021000000805940d603410040b09070f1280e40409903002d440040c400807642800030300c404406038121010000700d400210340480c149100d2080f00d400c00000e41c020341850a00682c015804501810989414050030343c1c00368003075006810007030311207104508254440c1803d00c03030f0320350f242c840708008c000710b041c414042d40d5501c80303261040082019a5078229525121034000c00d1640340e04c040c0c10b6407200c4401204502a0181c00a0640142d203400000202f0521440da070241646035010100c0001d01082d004403040d5210204a5031070f803083d0f4000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 684654874 1250 684653624 684653633
    0x607170f0a020309120106050105040b400e040c091d01150f0e09060103021215010323010903090504020d0605030d02030304031206060e0d1505010f262107 68
    0x41ca840821a800b0711351356120041080030200258000c17070304a038900203092166982090881b0b007904c6c102480251280460103038030a5900500085980d81c0f01c60400005d03c503040c448419a0300004003040c040e866468a04c80c2c80511011100600441545001008107907182c0d8840003210240446840400003c1c0e403005080d500fa80d00021b03202064180304112489400442c000a0310b17450885184034106034043c00d60310f10301804042c1c450501c1e4406885004c20400100c0703400c40c2c0d030b50380c07104c0550f0b520704080954441800c1c0c4400200303c242d036007801c3e17003c06201c4c02c86e1195144c0c4a02c028075040074140700003900464040003840c0e951b07410224a5640400c80a0700c0c03817400341c3c01151b503031074140f80c01031045400c3d1a80540b00e07401c2000612006030001e1850458102c16194070400900324144217510940511011120314502000884d110510003c0101600d41c0b005242c3c80e000c000e290b0503c042500d00b812121990003501503407000301a95104c40320004c250f180d80358242113440d03c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 684656124 1250 684654874 684654877
    0x41112070e0709121505190e0304051e0a03032003030a0509190b060405061c12030e0d0e060906071704150905030a140709020409290607170f 62
    0x315035408010750400110b00c1d0b2007003021000d008035480c208207012140d034070795003144044801008070b00e845030005496280610300d90400c1d00041030092107900584c1d0011034880d03001d8042c26014031191003d00f107144520b603c000380d804070302074610404903242d910301310744990746402c60300b00d00107410b00741401242041000d50702400103070200150604022003850f281500400c0c0c450400c0c4091118440485e654400d01c03075008000740c6001c6a50703a1240e000070003d18950703001582d440351583c001014000807400340b401d0005a42c5040001c580c1e0840d00c169145840e581d0b4400156160b02080b01d036081c07180180100003400741400d810205140d81d40300580608079242e11010f040410200034241101003600d51074410b50511014840c1000e0200382c80e800c100f08040c03c1c9182c204801d52001c00108070920041500460454a80d80c0352104500980850001c40f2221000d08009030404c648001c0c0a403118240141725510700340b5259190300c8481d014804201001900f030050190b4132080b0700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 684657374 1250 684656124 684656129
    0x4060b12032104080a0318080706051e0606090f0409050f0d0e150307030507020c0405101409090604020108040c1208040503150c0f0c010219030501230904111207 71
    0x80103540c8614000b660a071080e0300b00c051514640600405120119000d00122104c0601c1c915011801b02d59820000d030381366034103910041100400180500030700089a01c200e0041d5003a00111104d180003c0c484140d1410584619034442010004c4036841d243c45000704074881c4c0d01400111355211283c403034600341040b090b1407030b0180d04052032084005a2007800e400e1080400c4803424034078181604056628080201454207240e92a00030031846030003000400b9200500a1007400705240c03103002d109020341181b0401d444800340020700842450320740203280c80380c48a04000d000e5540c56800440303029002502c2a214a40406c3c0082056220384021408443c01107400c0c0b543e480c03170041454a0711212009454054070580240210300d1451000c480c2499160350310140c0f10100c3d01546c50080c0321300c2810b0800700d41042c5050704084d03013641040d41281e041c800b02c049000c01a046007405078150344607282d480200c0c0300000700000c2d4501007241d103420010300420712548040c0340043c070306000c3c0d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 684658624 1250 684657374 684657409
    0xe0d27080313150c0b06010c0b0405011b09080c0108070c14010b150a02060705090102010f0609050618010e220503160b180a02041a030a060603050d03020304150504060b 74
    0x740c8506481c044510100c014040280000340c01890140c00a0404900d034100500c1112203031701207401c0c0e86c440c0f4400a01d01c0c1e04200c01018600f0140f401d0707402031403030fa076103d090b400081c0a0700e0b22850060480d0b1080711048006812404201401110840c10080c000301c14801180d54000c080b880d26200002d440b120b6000014128001c0420040132054079155034031225070401003102b10980c0400e09640100d00340c00c003262074216810050b409843d0ba100c1e0304054500e1f05400143c0c00b03a494214a001e0081034030003041e03c4203a0f442c1c040300000309010f200846445000898205415100c0740e041c072580180e0714000c0f1206581d2180e0441e4801c00504090008070b24040341440400c006064120441c21031007820000780030480f9845a42d034220103489143d40e803071310301c0a4140384032000389000001810703100807500c145840c40040246000c1603c461082100108040b0f02074422640100c3d000310340fa0741700c1d106840a1601603c0020011203015450f001005003e0710707610b20112014140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 684659874 1250 684658624 684658627
    0x50903040f0609061d131d0d031401090203090d0e01050d05090c04050c03060d0609050c04060b031b03060904201903062012150306010608010e06040e0d270803 70
    0xd11500601c40c17111101415052000070081c5a050b68502240c842d014041103c08900b0750b6209501da2101c80e007864030180c4d070340600f1003008456507142e0701000d030500d4510740140483e41c841034280100c8c041100c192056071300c0815045180d500403440c82c8856901490054540700040208005030354081ea20740a007540003600c814100d14040c011150f029002001e0117045203802340008110f10031406000c5d00541d40e80000105004041c040681d000e14003402c103000455950303500c20303420f0b030007180d5a0740c01500c0001c0c00392000c4508030407280035520041c24000305403500e403185000c880205558000c041c90701e841c0303c502034682e058808244414440600c032000d2541c01c00c1025999015006400781c02c1d03251580d92103010420544081c016100c40e110041d40d901110154504042e40d125580741c4901d000000d03006a20070000c034141c4043c20400303c05600c82500b80420369010082d10240703170f0040303140051098481d0081e050541e514010f08940100c10000700380d140602c9402680c40344c0c20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 684661124 1250 684659874 684659879
    0x230c1306050a0f2102070606080303010f05091303080712090b090c0f010503010e1f09020301091e0b0a051e04150302040b01021609051e1305070b0f0409050903040f0609 74
    0x8200f44000c40102c2107080c07603103080da404600700c4000f29540d0042010a61301041e02803c0c091550310400142405c07400b12603407541c5803082d9204017009032041900c82d24070782c80002c003042440980841d4544e0f05803607141007130b2a0030300c007915032150620303d4019880e41d9540c41004a1800228240107005040142c0102044107040c406401040401103040c043c081004126480341c191070264403c079055039448620000e1608051f0040e5280c0c402a0000d002000219580310a0b030701010080380410710780000b1003d6501c04a00350344140c2c00a50780300c96400b80400103820400380d0342c02c810428000c0c590755159401300080843e08500c845014607040401c052003141800c0c4101e81e02c0d99800d00081185902c000c40c69220102980200c1191075101c0c0042440951210003101c1400341030908020240740c145601c440b01221000b06a400e44101840007410a0402c011100030b10180541c0130329150a09140b10041e10000e016001184000c0000054031360310781c0c25403005000c83d9900c000d0100d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 684662374 1250 684661124 684661127
    0x3090f061b0f030c0203040509090a0804140f0a0303081504022502090f0f01090e0a0236010605070605060a150909050a150510030b061813230c1306050a 67
    0x10031040b80002031615005540030840c0d000400da80031500c08903448055540d5100e131075420024050030040c040203010801140f0441e40e00702c40c1150b00c0c016114050b845825004100d16410180300182c085019140413800c500e15171840e0341c1c21240007400140c941189c034036620326078800030072001c03a100040b41005003c61400c0070480f0380200b6844400e080a0901c1c02c0c49980300d810606c500d000d0681d466881041c000d04c14000f50001d079030020842280d032a5007094030501034000a48030380e04802031080b803500c03103101401e0250503140c0d50780e20f640c1081401d41c1c0c1d030001801c2c06002c00c0d40c061030301d80d40050aa1314a00c103200c0d41210036030726000c42d80d10b005103d805031000501081c0c5000e0801b07201c40c1040c03403014110001c0320360485001c0c0903c010464254001c05002d600590004000034040c141004040141e00301001c0079101104420401c1085900302c981070307a07400c0501106202809003070084a010190440d145642080c601002640018030800050f4404030103e03101250030503025 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 684663624 1250 684662374 684662387
    0xd050c03011d070315060903110316120203011503110108090604031b06021c060f0e191e0e1501151e09050d0f060501120c050103090f061b 61
    0x4010010114219410861142c6200d5100561200310b201402c0000d8801ca101e80c00101000701d0004410361501c1e01e0742001440451503010580d0038001c5210a8452400c001544c0191960a00f5100d075180d820201d52444d001b5100d6800d036495134030350142c1380303d2501c1428600b0046200c1c85244c00c4a2000c1000074250102c024000303c0c00e504040100b10101e038110f40d1848280ea480f07064908410000d150140080c00350a05c2c5824218036468002c9a00d41031358030880654036441c0e01540120395071003545000540c2280c4400381600c0c4c203642054030f8880758021404400c8001c1c11f06d000010700881030800ca0320312001c090555401120340307010100b002a034660160000d00c0103042c80807039035400581003401c0310840392500d1041c010340c40140c5104001030405000014052003061603036080c43d01c0c02c03984024083d50264948400001c1d22030300482244e41940d8001d020a440c0f41c42c0800540040861000030b03100009aa0f000a000030070f24440c0003030549921140740550310640f40000c0c0076 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 684664874 1250 684663624 684663631
    0xc03071716091502030304061e0c0f020106090e1906060e0403090f060c050a0318080a0b0a0c0503100311010c080d091106090616081902072d030b1008120d05 69
    0x30500c0c01d0400f6400303e0383c0030003141d600541241c0c01182c00000c89038101c2131340500240f80b6411038501828415510303805105e8103c0000940e00a02c000f5032602070b40c004503082c00c20740c0c2e1043c0d8440441c40f1805d1410100005016015050000712103540d508008850300b000c58048000807003202c0188003004401c410341e0b010b064103203020750305001e00741e9510f903450a540c00c0144c11300680c1c03101007590030310400654000c4c1044009651110b10385241c041c1c02c04030299841103203107080030110b03280944105d041e07034840c1701c401c160100c229181d0b4036a01e2011302000d074210304001005507018003041a1800412002410b00400070b02e054050070005007284401c000c02d48a0107040000c3c0d9100c0c0c0d0742c0001e40b001003101d0000b42c980004145003803c80e0348204840c10f81c1c1007410054032000e468000c921182241c1e01d1000358212000c1a000801403c500d4003190b001c10014500c0a001107031011710072070b9001d0280140f00d100c4584445003a07180040a94103000003071000240c040c031424460091680 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 684666124 1250 684664874 684664889
    0xe071e030305030105120a12031409060f011a120112030806042918040c0e0906070f0e03030d0f06050f0f090703020705030f070c050111060f0c0307171609 68
    0x405085030740080c903074401846054401e010303800d540049500f0500c140e8140950040e80d5a06065010174060040c20142c40b0100c50400c0803800685905c40108485126090800108420381e090000d4100b034030810a5848580034414407169400c03c02c1c800d103c070702038012994554016009403070001c0511200500780c41c001c5040040c2e50320f0070b0045140c10848800303035500c4142032410340710110b90003040d00c1c001200509000d50600091040c0c4015440944d00c51f103141d03d05582c0ca1200c495604d0380151150000906d07044910352009104e0780c80130b544808014281d034508119400c1d400244e400100c8891050782e0354a40070011440d1851048090000c2075a4440211200d080000d5a80c80001c201d08141900020302e082001802e000302c400ba110b480800c0d0351652401d040007920107225000315804115680301c0a02c4001001840c1485008c541c0001d001903940c58a480c01c2642028041d5014814003003401c0b0442c009048519220703844d42942a0742800c1d40c1d40c0010419400da921100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 684667374 1250 684666124 684666179
    0xd082116051303081806070c0e07090e070509011724030c0a030f08130b09011419210606020f010b060c12180d0f06050f0105010f0c02040608010e07 65
    0x921414482d1074803080f284c11042241d264014206001c2003881070360152907000000282000800994420b6407064032a0b800b04600c1c1d41d52500d40c01d5401c0e4200d80240220489110001450240701e00003d012404c0103241c011000f08041044140f840000d031402c1010000c1203d4071482258000c0e010307990f69008500601e0003a07102401f1131850381d40d5004c0a040203d41001d40c03810b021240c1d04440c00075202d01010707401c0550358000020147c00c260b40d420b00207101802c1c3e10003d012441e0950314802c3c1c004004a61501c038036001a101d04c0480c2850804214070780b101c0e001d44060380d10803e00240b00c2038003c0e040c8e130400d0258050031188140703500c42c4580c40500002c0340e46440094400800c4a0741540740355524001c003510040c5907880002a540b01020203d21030401c000990710785802482034400340816180c00c0d0246480000c00d006060004617403052049045105004910105001401c000740c100d0700c611925080d102c642d0743c10500d0398041441000b40d408107019035040b07107460002c083d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 684668624 1250 684667374 684667387
    0x1203090d0f02073209130c060c031d0a0306050a2403080a0f050c071205061003020f012106090501051003110306121c1d090c04050d08211605 62
    0x1900f8074031409030b40d002c0d001c42c84a4081c2e65607240528244c100500200452001d00c5e20a29041208881c42421500091503050000d600307070140c00031983c0e541d4561903d0443d4000b459080348981ca0582007607902000d150070010200302541300302802040180307008101035205040c8407000c4401c0d20619040c2381c2082030100f000c80e04000a03251068040e2070000307071040900300c0031034040c041c0e0302c044101c034022500c0c0084c40b00303165469081640d206100b0b56049a03148020030b01e800300d0390706c03002e034000c482a0440c8070158443c0013600c0178800c500c1e1100c0142d48500e0080340c104d40040d0009840103a4440040c40349140a005a001c480769a243c28007580c0340796009003800d400040c00050044080c040f032480021410300400c21200843d40c0c0c1540c002000c0c0230010900303c2400100d41090042042403807031428a1100a84140341100440f490107190500b484280102e914081d2032403001406043d84404100c81031400419400d0b000c5047c1d82040502c4040b2074800d46000710074010100080c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 684669874 1250 684668624 684668639
    0x6060e1e090708090a12031a030316061e0603080c06060306040f031b06050907090b04020c0a1e0b04050a1208090a140f0304060206040606060306060516051203090d0f0207 75
    0xc507030702c45030a1903c0001c58540000152808640d000001c000c01c42000c102c803221541640700d2004562048421503401c1e250100349620382c40b0780a1040420a40650702c0004202d50707410001c03a55042400b100a448069508c1000711181a0022548442c0000f045c40c484e0b002008016000034084001d0416814140d039445990b180602c00101030041311341d011110400c001003203203880c5411000034000352410503403098a800182c010070050078079003554010a41010f10981c0c070701d00740d0000200162000c5448041410140d008000700603185506008006010b00c4040b90140384208000c00b60020704e07282c00842c0700061011101003100000030441d03002c5000400e8035031140c00c44c043c683e05504c5c0010142c184110b51190702268800010000341c015030000d0902d101d24042d4008020403a141d800131002d0358080e200b10b50019030300b030000c2181a12442480d104592080302260f90a8941c00401c000942040b520000350780c00900000319901c2d0001c105401c0325100b0300c098004141404007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 684671124 1250 684669874 684669889
    0x141204080709180b090312070507030206010b130e1b1b07050913031112031f1502030910030f06141311041e05150306010216050109171006060e1e 64
    0x100a0036800d4004081005c5040074030888247c03114601c80c00040349446040580180d0002104a0040c8100c1c0c0c0005003100c00b000686001070554190000d6441c43c043c004190244043d1000001c0b402c003412100c540d11901c001001348a41c0e40b05814031050050310854100701595000f41d01035040c04007001a8851000201c00d49a1380c142072107000140d001050300e02e48450756030050303040701c000170030300a03d141c1840218a1010000003c8001561202d101d038490745821074010015030b20070f11403a107a500c0c1102c403241e8032840516001072141855520300301950f0380b1342c0c041c031403040386544201280c4c20907002050390591601001d05c8800345c081018002803080b446910405c0c4a00110b0941c420210071085008100c003c1001540e51440318a01445d68000c1da03d440c0544504400300c040c0b081049001c000f01c0f14140c5440d10003510f84518480d8a001030505040b69004985080b07140c1615841160060401036413090072001d03403c414405100c0c0e624400342c9011045500341a541d68a0b5403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 684672374 1250 684671124 684671171
    0x10605030124020102070209190c0e0d0b07110303010e070306060509150f041208030a0b0a08060c0d06030501020a11010c0c05061f0308120717071209141204080709 72
    0x60108034405500204138028014110300039403004c030540c240078414050260700400d0f5948040c0802040311106400c0e42c00e041d10441064001100d40003120200d0b0420023081e5000c0e05034180100c460b034902c05400d00350380c400d070800c0c2c40052090050040180d490b22440f40602079a0410500d80320300440022045660f9004040d406640001d02c0e001c01d00451056074020891a00401481d00c110320b130100d00c580044450020540c50104485a1403030304110340d50450369080b000d080c07552580b07800e415055000c448012105030712142e0000004a0034030003026182d28580d141454003007210b4001c0d09407501810798030100040c002d07400300480d40100701c0d940c0028440180120004401d00603802c01003070380c2e1000d0240700011940103040a018a003251164800360340f80400c00140341325804410710203403049000109600401800c0500e10381c0410492030050400601c0000e0b000c060b0703460701d8000c0105449054002c10108a10b40f41003100c4005000740c960240312003001c0f085485030004455 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 684673624 1250 684672374 684672419
    0xb09130506060903010608030d0b0f1e060f070303050f060901260c031906180b07121b0509030105090f0d0513030c09090b070c08090f0301180b0f0106050301 69
    0xc101066007a542e00045400000d000340c000e11800e03940d06c0b401500c80d0005113500e01d10a04000b245856850030311950560f40000401c03051000706085c4400a980e0008800d094226104200144060502d080a4602d0300d00c6aa004105490070b880d14401403200070703089600a4900d040140300c8800c8508801c0d40200040c0c01c1c0c081540002c3d1806840c0c0b603101030301c2c2605401441140030090005a456504280c0548400d11002c00901203141c1045030614000c1c3c08080c40d1404204028850851098105031a0303002103048890003052a01c0d0350707640e0411101252001982c2080c0742002e014203540702c0754480140100c9924032075240c2e107070310038214000304001002900742107218202605601a42e0040e030b01401140d10f44500000920403004242c1f8260101400140c10310b2184504140c070301c0e40500d0751030601500c10184402107551780c103499455501c1e40000300304031000260300c1c110300d0300442c0300d210141001c40d4141c0780c002060b0051030801804100500c103010402480c01c6068145 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 684674874 1250 684673624 684673631
    0x1c051902030304031203061707080307020112020c150105032a011404170a150c0f030f09080d0506040c0c2f1e09150a090e01180b010e010b0913 63
    0x1500c0041d05601c600c0c4c000038030103034100703040c0100c040d89641f00d4010340b42c0c2c41d0401e06490301d816181d55660450340c4102c42055100f003100f400154030940410752140b4500c0c40c09070401c102803182a042041a00180700c00d881d14000410540ca420008686c200e00c1c044040340d104d400d04d0050324802e01984017068103010821000d0000040108111001031104503410b0b001c100c0059100c039281c041200080d103606a4001000715a40c15a12038080e0004039926082c8001c04070f400181c001d0b0400b4021340c203003241d0310900c035004502d00350000e00c00000c00090018080c80c2180400044a0200c84007074100b082404045002a950462550245041419080d80840340301e2103000c1811550200d180c1104410150f620034008106540b0103103442110404807070f40d10756034900c80409114140540c082c0c2c00707080400c0440c00a62018007060b11080010440c1c2d841c000101481d485891400c60303061040100420501102032002405000840400c40c03a08901c0400a100b10018840e80d10b0115035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 684676124 1250 684674874 684674923
    0x1206040618020607050708071d1801061d011e0b0a05090a05040e03030f0c0c0337090f050906010548010b0609011403090a0c141c05 58
    0x355006078202198024291035642e1403925202e07485040e64881c4220a00c22040042007072807140e0180701c01010340340050180d560740d08000214104803000d00b030040355a101d40c00300b030701c0d03004a207041d0806060010300a515403401c1000f0000c00c0c5842d40480018101103001d00407440d070081100c01116061819a0711082040c00284890005a101581c02460145d080b1003440020010314460302502c42c81c408640e0f01c00d075502d1224815800031110170740080041b00c41600700c00825112984490000c440c043c10300e0000f86050b0545040b8690114190490412202c800782c403585018120a42e0360200750708080001800a004260035041d03030700e000070445507110b4414062016040c0b03071003982c0f145511816000704128011000071500c0d030350a1000c040c015040080c12289280010ba40d8902a026082c000f5403290b080038000a0032809a0200c0d0780100700025425005080c280d11826038040320081088081c00740f50100100c1050210182008914040780c140c0006554211405031941d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 684677374 1250 684676124 684676151
    0x50613111b0c100c0615030b060108091615051b0102031801110a030504061b030e070f0b03040b190905010b04180b0f19090602030402090601090b0d02090a080d1d12060406 75
    0xe908512011a1b10741301000006001c0007401442c0156020380721410130381c4071304810a0b00e425035000c540d054086003080400080b4101120113805a604d031808605050402004140f088811091a1240e070b4011080c451300194824040013071510090080001452900900065019201241c0c0034075546070001400d1080c260400407050311000317003001641507240f102500408540c044001c441c4591640401c0740300000c40c80f10b042d07803210740d0b040c0c1c21540c5a41c0c40c8903a070a0000c0c040c0c000b0000f00d220641c52116a4041d40400714031038000482c2e810081024001203a11442400103101084c1300d65001190100380815080504040c0b010b201d56a005111015501e002039500c50762482d0040d0241440142d0f80a5801544200c8082150f900d8280045070314056074094901d280c03d0422940008201c2680140200100641555241903035104a941001c114604610105200341d00100c40e000083d20114100c9404450040046500c1c1900c1507403401300400080c02180e541c4107403151003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 684678624 1250 684677374 684677381
    0x210e010504061a03010b0108011e0515040305160e0a111606060807090902031c02010b0d0302030a020d0203160305090d0803092103040b0406050613111b0c100c06 71
    0x10440000d100301d0400786054802010904201100d0725680c4041c60954501802403680786001603407003907920b074282000d400041d62092000040005010400503590711000240c0350040e4909400b80c0d01ca40c51414500c5c204007860401c6044d281a8400074803c101c40f43e102203402a07146403000658880c0305d500001030748103040c0901c2c5c11960208060041010325000f1a050b40c40b14025108910b03660701850041d00c0e84004025030540189a05084039a00d980213201c5525103480007050030103584003c1200d4120184013640180c00008400361501d40402c80004803584030301c0258a0075866a041050425034107000604010000800c0441a43c40d5020500c0298210aa0b0b0740e4038288800800d035074214011910443c40d58030024018000e21007400c1e280b24607080031422906035120752f6108002c2000405840d449218a16990160b00240c0710313150301034140c0140e0540e00c1d0300507400802c0210b0526032800340faa2140400f99103a4440c82d03200d070310440d070703078106403058168514041c07014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 684679874 1250 684678624 684678641
    0x109032405092b0f080405070b07030c0b07090311010513080d05091c0c0b0904180305130b04030c0308031b07060c0e0105030603060f0912030906090705030d21 70
    0x6410081400390110000c1010a101d022065244400551806a20382d0068078124260b011070850710602161078040c1701001d5002e40305000741d03641691500c5129101e5009003400b54000303650603101d0307401c1040c00e81406130030603403504141401e985140e55010070003144000c1203040020229036601c42e1015400d03145c01030800351050313994001002c071008102c4d40042203940c0c402d00e01451b0b00702019110001c544100d03178000ca201d410a03410041c070900581d2000854a07005a580e820080e6603c4045014040c882d100346e680c2075503851403406007040444030b03410031014100100401c00002e60010100c804032540040c0d40e60b02c9980d0346641d400c40400500c135190000c0c10004800c0f08200040d0301508a49443e43c07504003a01c030024004540f28082194156019802080443e22042480c542640d0040e41c020441e04a0726035400c03450000d410640e00381a460b072286d0140002500c043c0086006804e0a030700a000320b030b00c1c3c0100208000d44190300c000362550b0741c0f4422020701007107070058401d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 684681124 1250 684679874 684679943
    0x807031d1c0309020a0e07080106050c0d18051305010510020c0913061503050102120c0f07020909030f0408030711040c02030414011b050c010e01020c010e04020313020409081215010903 81
    0x30703190703a10445400700102c07c59074080094552400418424000c409940910f03e024008014076101030b50180e80342510103205103100036402c070700068196102d5200c0407081c002e0703e1021516524000a100341400c08103001c00a542101d4502c0600e515a0392031541c0c490081d400340c021541a50400200034007030141c5000e40038400301004024010150000d080f0300c00c3d04054402c280d036038090940c1041c0904200c0c4c1851705001c000301005407030b0060306035800100d00da040d00d140c440e008051814652082d40000300d2038002040450502011102c1d900d20404180e41c148914110740390025104c1c4914002c007050441caa19060501e81d1180c203041052072140810740003d00814204566035103000782d002d600248001d841c0800715480411009551a8180c40d250f440c0b0500e00c04000180d040142070007403020810004001503940c1d4040c00000901494116564035003030002c0c40400b140003480d02c144000d000f1540314250b640100e616040701d4000c1702c84c40700d00e8250841040d1410b65140c1246 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 684682374 1250 684681124 684681139
    0x6070e012d080f01060912060504030314160e0f09271212070c120e04020705030d0510120206030703180f050f0d030e15060d120807031d1c030902 64
    0x203032a0300500c08602030403c03a240c14007a0f83e030320482107400c91503d00541d860405000c41850001d9095085990407911904010444d840414030300011000b0840d50b00400350205e1841c07072140758010b0442c00840c007040d9001d444002d00740b0081914004050050003024030748858a4681c0000002d50700503400c1c445080d10b0b1200b0f200d00d00c103001c0c0c0e00400071000351150188045840c042c026448403031442d82c4005502d02c1c401d084030301982e007030300c1034420b00e5003082d02001140d00080c01400140080c00c3d490750300040d582400740e4a101e000f07442d40c000c280e90070442c00c0b079071025030388400c20340758031069900e000306038100ca9600c0d40b00007000c044001084000c140150908010000c5888241c6800040840e185448548821401d5580035134840c0c203260844c5000b100400c107031101195200002610600c891001540d030109507050140400e400107101c1418490300b1a418000c3c007119107071214464003c0e01d15100700589841c584120b801c24030360054000001c040c000c1e004661010b400070001c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 684683624 1250 684682374 684682457
    0x40533070807150c0c03080901150e01060801080f0c2413090c1d120309060a120f060302180712020f0c010e03030f13062c010c0206070e01 61
    0x31010350002c060403a01c0e5988425440d0a00b0b50707a20801500980603942c401221405440640b07003650040c2440d034643d500c80d035640e091081d1242495000342140c0104c2102907141c5480104232160607013161101c1e8000240450342e8060008141c21140d4088a10072203c60001800303003030062210003e8210020046a0071108c040d51580030300c200c0700704590070b11070082e400c4003c980010303401c1200700040304180700d0300d40715042c2010034044843e4224120303807030a02040000f5003990044040100000c58a20070801050480c0c040d204c180c0b00241028804107046a0010343c926005008004448620b0300c0042c0f01c1c01e2003001070780010031081504568507040c0225400c116031004148511a40c04c3c0b401071119118000112403064802d10f1040c0465201c02d600e04004c10610b60341611403030344607565010205580382c0d815a1621003815500d2074460342d05c0e40c0d2030039951b801d5982d10540d00700300c0030025015000b010030b4000388404d00e40362011009500d0075452424460841d1800d0380c3c540c0d20398 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 684684874 1250 684683624 684683633
    0x9090d02010501060e0120070506160303060501020304120b0601030b1c05060c130e0c07080409090b060d03120f020403080703020a350702030a0204090c05120304053307 74
    0x51a1254055900910032030ba20342d9000c0d614074a02c4078000d800510b02c4008680308a010201540c5144080c2d800c1c5c3d007040390f03110006690341d007024803160050009281400304041d05485081c004050a00145061601d00750502c81c641e01d440724040c046404080c00241160700c690f1000003060b0005000380c4c000c01151406446803040c104089800d840303503201041040c10b5100942da194481100f60503089420054810400d4002500c40c0e11020418804040001c0242000e44041c24851000160a82d014280ba920500d00a0265401000d0104005020a07808803100b50346e0000048040795203114840028000d1003130f548050b20341a0040341900400d5400b09001c8066400303620782c0d0101a084801000f41200450042d88bc81c5401720318101030281c10304080c0c03080900040644079140d20540200382990150a42210b051442d4030092006251030007446020400010049d81058100030106c1c050248200702c0c884640c010700600c0302e41ca91070740c400f400c1c503c211100302d41d200e9806140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 684686124 1250 684684874 684684883
    0x4110901142d090f010807050d0c0506072f0f100c02010f0903020307090506010e01050a0f0c08040504021603021603050c0d06021b0604020420030a15170c0420030106030c0207050909 80
    0x10890240910400002d0600d401c0303048020b210741042d0ac0315000d51902c0100003440c1d00c811070445005048008200640780c1c900c0f081d220b00c414010780f2600590403a000c01206200044045210340485000265800d610a440c0c409a07542802c0c909820054510b040d5070304070300c0b50300095144c41006008140400e4039006030740508400c5c1c80d0147c0019256005444038001c00503a400010103030b085400080348103555903601a4050042e03507260685640114003030303900994100100c1c100b60f03542a42099810042c843c0380c815034040341c11103141160345035034071584d144144521810b0511242814042943d0440300c1100c2d160001a5003010060445511100116802da10172494180f90305a001c844030307001c0a4084e5080c40407851540d6109040c2c0091030b0f030070b409103880c1501341c002250003181c0c40c41040900160400030071b2240511810442a00c0d22583d041444034181340c41a0f003009020303415a410758505040c0841d100004e103208920f003044a5120035446550f0f00240483c0c40400f15 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 684687374 1250 684686124 684686129
    0x201110d0203190e01080c130f03031805061602092e03030206070207180207141b0906040b0307031202160b0309010e010b01080c0a090302040504110901142d090f01 72
    0x4050354025064650705813800680001d0690114403100001140350354140c00903c1885050a16558110b80b51940d15515022a80040740481c901030034071908a2641c041242c02007004507002850060b04c0c810250f01c81d280d01c000240606102c2021034814010104a50300320541003908100f016529001021881040e03c426005800b4201c003040180303102042490564120040c018148800441042c00950181e0002c3d1494150540040c41c003003420b000140c4181169407400b49502c41c180204030b000e0501600c154131031307813a00f00d0038403540d180410084120381e00081c5152480d01110001ea081644100034200800c1a001010903180c00d800c014500428002000300900001382800d642202d13403d4007407501283c400400203008021140051081c1440307841c0c41017080740ea96001c5020744500b030f10200c500c1c050040d43d862540c1450241103004040c0c002c560f42c0742910100100b10f008011030008030500c256442c040491681d06003a0321001ca4014100c51002d00c0c000010701000d500a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 684688624 1250 684687374 684687397
    0x115030b040f1a1503090d08060102030910110709020c0d080c0d020a0c060b090403020a02060906130f0306140f0609060d0209150a08073503070303060e0a020a05030a090201110d0203 80
    0x5140c42e62134102c07541d00350b0b445140348a005040a4140d05010b46007080024181d5046100411042d405601c4a291241100e80c1507254642076a01002d4040c0c2410940d80100709494414082030a8a07000068154085600760810000c0c1c0d84500c0398591407441401d10200c0103071300000302612595400040e2030540c0f4002d5034200302c031400300da0130040c003030700c0c2070710060f0040e480340800401628020009100d100c10003003415140110210900e0021204c5910480c01c00400001c200203102050003485003801c8080d01c0c071000c0340f82030400b0076900074024000b18011903a8400042c06902e80e000c54962241d0010085402803030300c40203442094a40801c070b0341c080c1811032000982880c00145401c02d40d030000c0c0d0584504800b5485444486000c21082940b400c1000348105101001b880184051402960042821342c2442400f852100000e482007100b9031041150315505684081604c1d0005200c810110f042c2826000484484400aa007980d940c01546a040c002c0d6800200800c00c95602 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 684689874 1250 684688624 684688639
    0x22d0d0308060a1a09040b0402160f021008100b0717220911070f080d05090a03090806060906011b050d0302040f0504020f030f070309170414090115030b040f1a 70
    0x9900c04044e40900311503100c09403c400f403002088a2510360800c041c2540060b2005003031182490b01c2e400f62840e80e444c299100054007400109508140202c044910320030f003840007503070604104003042a604c2d44586501c48001080c0c060402190072116400718450141c999220304207503810b415040a50103107100a5000d0013000502c180880c0526441d1503011940c26090103001c0d15400d08000b45890700302c5170f03003108100e0710341c00c04400c0c468a03010f100168020724800ca0545005890034209400c07825450b0710113010440e0329902d000401750700560078608540c1164a40100d0f0b44140e107036002c002d2150040510605405500d540070380116030900c00304003005039a80e0107100c2203204464a940824100300002001c000301604900d8000c2040c0c60001382020964032410908603e000f224842f259000500f04600c0c001c8160125070b610045803400d226501d42440100001818440e0506040e1141c2c10070340b00d83da1329840324150040030f0b0300034001440300c6502001030102c10084948a1400e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 684691124 1250 684689874 684689879
    0x414030114070302090607020307030308070f2309031c0e01021e0d0e030304170a030e040b0306070305100806010f1a0304111c051b0109080307022d0d0308060a 70
    0x405000e035003980c68401e442070665031500141140a58890460795402102c100048001a101013008500460103a03135803071030700e040c0b50000505601a80642e0420030040c20403203419808007895005912240c81c0041c0d40c1c84100d170010a0600303118401d2484a100f440302d09a000ca03401c05003502064000342d0955041400440d01481003210300c2201c24502c1e400b01c0000d0800c0d50081440a44041c2d0080490b804c00790b0301c074030780b0243d848400100201500184151402c00d031b00300f07009485024040b40c003808410584c50100f66111002041030007055108c60110310b100220304c0303003000503001580031748540d583c4520b40960210400c3c840c000302ca0b0306400360004540804403d0707900980c2c0c803c2a204255090a00300a07540920b0300032b05a140d101c2c0d14401c1c001520410095003629200c4404000c550071000000d00f0000d1158402c0c21950403c1000c60016a5210780000d1440381c0e658001c0d07161000b0090300c020401d030900c0341ca40c100c00b08076807420a0507005038415201d200115000c000702c94 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 684692374 1250 684691124 684691129
    0x160b0c04081c0e310c0c1104181a0906090a030309020f0a090e0d020705011704050c060c03030a15030f06090219260109081b0c03120414 60
    0x400c40c030400c0036903040180740122151a07501e041410b030b145407620340350400b15000000d0729000c000c0380201281143d0070200280c0500d1552000d51440c03134100c10402402824030141694100e40c00007410001c05100f1444a61748940c0320043ca10306c1c2102c0e40e8920507151600c50201d030300b0751080081b815004800520902c500196640c0324a500c1005802c01214a1764190060944030b10100e034810700e1b03c030800085443d0402042c00811a6910100740080700c440700c00d0405489406580454214010500c01641c02c03050a00d200d00700c01a8200207907882d410071506190381008026400100051442e0f003001001000c0c41c06035494413801c103d04141c82c15640203040340e030b11008001a442d0003111001c144c0ca0740c440c1d0140c90026008049510301c0e40340c0c0d144180c0c525082002c121385100c0c8481347c00c0c2c003048144131003c0c503004000c008411350f0b9200c102444c054005040070309440248003110180041c0042d079400350001d01201c2d1203404100c40400c003504603001d0082e004102d440c03d840b0f1403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 684693624 1250 684692374 684692377
    0x120f1701090e060a06030c0509191b030e06061e06070206040905040212070302030616051303080a02190b0a0207030c06020c0a140607080c0a14040e070e010c0b06010804030311160b0c 80
    0x100c1c7e1119440f40d0301460b0806000c1d00707500041c48540f0b0021300140a40780c2d002a8001c81c07a01d80c1c01c1004440d658528144090101d440c040248003031a03000200b040010344541e0f00c0c1ca0b0030203d403c40403440e000d510000180f45403041410003500300c1c0022400045c481c3c03443d0840750256100301d0f58050783c07030640c0071095920815448081e500d0380c8024003088100c405404041300c1d1015038070b0041d24218070200303815615040740d481141d4200300000c00100e00341e818072a144030700c008031840000c026a903031110f90600302c000e0420352500390300240000030140030319084042d1550142e02503407108803400180d0b840341d0440e40c040d140c090b00a50107403940400400d0b280d02c03854482d01c8003910307500c1c2e1410a00068002c82100401d000e100c80080c000d03581410060401030255160840c001d240244004083c00c69a6043c41e05001e1003080080c0008c030750014582d4030000c02e1a002d032140c0d999080032800b504455082c038a8400c800120b043c401102c440040c61074501420311071110f91185d000c0000c05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 684694874 1250 684693624 684693629
    0x90307030f05030c0d0e07030c1e03060c050c100506030d0305130f02150409060312020106060f0509270412021b0d0c0503070b0c0613120f1701090e060a06 68
    0xa2030691200001e10700a0024613046503c414034982450049100350007250060450100b807540114003c20810400d00e60070405068030400c2d80c900c000010314603158440b00c0380402440262170340320b02e04007548124140c400403085401290f020213950403540c4c008220a5030558021700035601390400c1180207016a5000745400403501003c1c3c0d51a4442003400610780c0400c0380d100d00c849014082004c0c1c150040c2001c0c10010320001101361462604ca1001e4030300901c100196410400100881c64208044030504a9941009a03a61030b000c030000d4414910342c0c2900314036000d50300c5004046e01401419900c901d20456020700440c00d07201003030783e862007121442084101800002502803d00c0a60440098810056802da4a8444d0006801c2c160b442d0031000200c20b012490203808881040f505400c5605043c0401843e10f413a250f070790040d44415400700c14004e01c1054003140301d1085240034241296882d10381c0e91541c58040d10000b421250f8214011482140080313a0401041d01c941c404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 684696124 1250 684694874 684694877
    0x3010b0d1d0c0f04022206020d1e080a1e0c08060a0f1e0b0f04080c01080c04120c080f0f150702030415050d060b09031213050d17070516081c120e01140403030509030703 74
    0x424003200ac080300c120b000204a00035264482d080e0700005050741c0c41a500003004110049085048100000c0c100d000081a0520900c1c44d48000c002d089121404142030b5204d8901c0a14000944410705440000961040c5203901001912510700c80001002c0c0098803030076015501544214170046440070f1003540d50048980d0100000c0016882d003031300342d81c101c43c400c0700c002054036501c20070b0034104051403e0f20140b540212140f41180e40061240c0000001d81c500242d070340d4108460001e6032409140140d12029100c0e4411004640c090003d40d52190fa881c0028008540c179216072170201c0c0c010f05841e50180c800d6090406140c4403441c10b0f150342c1200c10381a511498548810008850042501922030b100c01000c080308454084000b0180c43e07000e0802840b40001a2111040d00d003890390104e00103400c42e181c1804080707280c5280303a4404051b4035003004612621081640140601640c4034129860305080c1d04151580da88421f21460203a181001107545000c0d50a0b12803203038080040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 684697374 1250 684696124 684696167
    0x60606030e0714030109051506041104140108100312031a0609030a060f0b13091e03020c0121091103060105010906020307030c080f03010b0d1d0c0f04022206020d 71
    0x10102c40b980c000c10f01d844010f00119580d4032541702c5505105030422040001c40d400000c11500342841e01074914010461a0901c2ca032600c0d100d030751000601904609810401c4c0c03403000c42c85041e68925001c02468003d20249103082c4100300140042101c014038080d60401d00c0101e82d1503182c26400d60f0321090300580076201c220510b0351884020140f0419450035165220041d000e9515204984403602025040c005448600c80c1022011032503100d0031442140e10b102c8201d00001e40c0490340d08200102802c2a000d050f5424511540070141c0c1450b404030149400401400e2000381c0e40106200d000540c162901d03a626038004480a8806014010147e0300c00c119183c0003a2045a06040c020300418405050140041c0340d401942c0c020307070017600c0c034000208000340c4141340f5101da241105400c2c481c00d004107014808080c1c4890181f00d14034403500b03101643c0901c40e1502d40440b0404590401085d0722104c0c1112200350300502c50164900501c516866851014000c1c0150380108950500b0710 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 684698624 1250 684697374 684697379
    0x10b03070f270203040f06060e070507060c110d17010807080703080a1101110d291e090108151f050402030601030216080306130504020904030e0d120c060606030e07 72
    0x741c0008038600c0c1c420900003416802d201c034094184040c40c0aa4412410048100c4140c01c01100b5203100c0d42080442c82692414016003a8110003101e00c20340c2d00603004230b45a007402c001910038074000030b0b100005000b40001c5c41c0180c1d40c80081114001c6c4181e12000329070b600c45602ca965041c4a0041120310b52120809201194040b000381468041c01e02d80070010700d088010240c01e481c2d406628401c0041d010070304c81d407050032034014035416490320031003651100c10109104907910010361b400e0380034141c80702c0000d00b40180040d2000032490040c0c052691943d55270710180c0d4401091040101807901c031004103c0304e000d41950a020320003100c0c104d01081f0305140c20800258005460141850360070413500003c0d488005507200443d00071040030780c8915004040c0000c80c07282c0c0d00c4900060341f50104210050f61028900c80d0055003518115201c0307040c010100d10b00304a503a002034400e00b40d9400d0b10780000d0340900100782e118807401d0706000b010781c1c4620513000c0e039a00c41d0301c40c100c541011109 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 684699874 1250 684698624 684698639
    0x1f0e0319180f06050307031406030d12060e10290304060b210c01030c090f1406070c0314010c17060907020304150315120503070305070221010b03010b03070f 69
    0x11070700291250900c54640d100140b910303000d510350001020600220130040f005805102c0c3c041e8090714006204440d241100000c0c0d260f801c000c04c1c0c0000d00c0542c2403000410b482e564092405864101104142810031321250310b81580d0601c6429a20350020008800d5100d5080003071024110300d440003030441c0c8a9070b40740310161520485403a040101c00000103001408240c4440012401401528040c3d0b1080d0004040e20340500d0501c0c107000c1c140c1c4003041301804940002040701c40000c0d42000943c3c2c0e1000145281c0310303101c80070702102203803500402404851244100701e11040da00800a020100000ba1480c0c0103101e40b0b8403041840c070700000c0440c28808440365000100d4030640e81313040d84442d485440302c40c0750807090b40001c0e550002120050f806c103082c030010b465803081030f2100c2900303543c510355603200d2a64000c00300300001c41d108046403104030501131400d240300c18a1100701d03c804050380c001e10700004024400d6080c46050f507003034200407410005541180f403909814509040750f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 684701124 1250 684699874 684699887
    0x120803010315090b070302130b0c073c0e220f061e0c020c030a0506061c0503040303030f180c091104080d081608070e10111f0e0319 58
    0x148000301d6902d503c6030b40000f8410040451255405490058882040e0238140020700329a41149000640c108030310030300028001a50b07000c65018a0f0500001d48904411041c110402d0040c1c994000542c0100e42c0c80004912410003035800d5005503202e85e07030ba280707000c00c450183c032010b41c030344c2c1012500d5040c049505d0400045072140129070100382100c030902000d02550290b003502940d9591040380d42e8030b45506101d14100c0c804228001c142803802074840e030340c8030a0040c1c189445421a400c0308042c0f01503219007035000c2500071007a2501c5a5032410b01401800044049911213458203100ea540030301d0030341c00b2000c0c5680040303a40300341d80e041441001c020708000700a400b080e90240300025a5403000c019503400b10303a0641d02c0c203509080c505440d080a1450083c0c0005028581007084040c550141c6d01d0403802d803085a400010012000c0e041d07550304ca40b00180800c1380039602c07401000d6500884501401030410301c0c20000c403081114895103d02400904903422420b807040d02c48010711500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 684702374 1250 684701124 684701153
    0x60a030b0a0810060806161112040f060905060a0f0e060417010e1603030c080f04031b17030a05040504150512010c0216060c02101202070501060f1208030103 69
    0x5002030095410400a4601c0c84180d0124425601c200144007100b80d041c02108000d1120030001e00c054202000303828050200d0b640e00c001084070040c103003c8010010441c0c42a001030111000c0d84c0c483d1110065890840315019107004a80241d80019042c1412800c0380d117121020755503814000340c580f00841c7d884000900b102d60000c014000455141c2c403c25840040500744d5000060300104006a94141440200c01e4000507000102c20030100350011030203610300c0e9101c0c5a40e030395034551204201060240b40c101a103009031100080542d1482c5101c1d0005903217050600d0401e041002c40e48a55034420b074508a03000a034207002c1000b02e8241900b0125a40d01d0701060300c910103480d00080b03101180d075000b100d485691685040540c0c5901405010b841c17406100d00c180c5940d0504e58044c0032500200700c001d0060809050940c8040c0c401d40d4003050203044140c0a40d91921203041c894064000c900960051521146c0700280d80300d04d10150002d0a03501100d814156840d54a40410010307110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 684703624 1250 684702374 684702377
    0x303070e01140d0504020913020307140310022a0105010f1809020301020c060f06041802010509040e01050709170102041a0f040503031606050604050c090f0111070e040b24060a 77
    0x1038141e4402c90000003601c83c4407180c3d100003d0500c2d06004006030100081d00e00b846d4194003407095000b58401081181c15507449400c10041d460300c2c1c6000ca0f14002142880b64442840032500c04421141499040c80440e41e5085420f40d800b04185000e0132603000307104845142231980403c10244622040c1034420b5606d04400181e9401507402107400d81e40411603280142e00301d0403c2000003140c905400b82c000009481c1042880c405030290208021007000103814080d01050070092941d0380d410041c0c0c1c058800d00280701e01e0805984c003034154030450061f50200a50034582c2e0200c00c60510968003210741c40d1040c00b0320698515003559156000300d1400f603006108100c04121901d08100500404442440314810b10705a41010380844201034603071803280342804240000da180700d00c00d845101a040742c1e100422a44000141d035103071011058014180030301d071000120551000f00b0640700b00d01a602000d025504e0b4100081d07400c4103042c4407400800801c0c150300769070030305d8005040c08210342d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 684704874 1250 684703624 684703637
    0x305161703041104110d0c0c0b0106030c08070212030a050a150e092404110109030611130e1b090d05010501030609061d1f020c030720010518040e0712030203030718080303070e01 78
    0x8c41d00c4056050030300f6002080400e40320050310000c598000b80e419402007941c40901035450380d035845141c26100c050034420805071070b1404252007502990105409400d0030411030444e44c0d80d920071140440c800c0b201203c1c80c4c01196a6015503510041202540400c441c501c000c007035403107564458034444c030f0501d07960402040b050301000150301b510440c0040d02c0c00d03545281e00c80c80700641c180b00400c0107800800388106400140106442c040754038403840d210100a16403550001004299858060400a80650b003004c000100707110741c41d031040708403d004101c00d03c00004041e1050782540c41e5690181c145901241001ca4400d00f6860288183c80380b42c072000d4a0003520f00300c000e155800012040d01c500300d6284101c0f41750118482c3c038640d0528207080c07085c2844c000c88482650760000c240b529001e141c80d4140c1c0110000c1c2400440060518040d20200c45103045c10004e6036500f04a40c1d00c0c01145003a0640d00b1404027100412007144e1501000758038690380c00c0313800c59045601c4891a81840f11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 684706124 1250 684704874 684704897
    0x71d0603150616021f020d030e01020903010f0b0f09040c0608070e100f021615030b031207030909050705040b09102024040804030305161703041104110d0c 68
    0x4034400208415070b03902e40c5403c031010300c0c0c0c010010f4265641d80c00003902e4070140314545140b900826144c507515014200003601c041b00054050183c1300300b0556076415440c1228480e00020241c2c4a01c00c0101f0548900d8100200c0c0b2050108861090700c01829903c8039050401c495842800c5e4107501811606e0304031100314403040420009410000b0030b40114044141d840030081c1d040111002311461700340c030504403d03c2c09003503100440060400c0c0701059101d104001198508000d0280b41d02880e00d0070a585403964103004050800c240070300c00e8028102000725251500c02c1003600c050b2040c00d8011880c2003c03400070070000c1d8104050301e20a10a80f41b4015140944100401c940945071340068040341c40c51296440040121450106802004906000c0811200030507601500c1d4507045c00f41e503601a110442e41843c26480d801070a5036031450602101c20454000345001c0c40c440c1030880b4408100c441000309a034401030f082d4010304000c3c00a14144200c90b000100c196115040c00404041c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 684707374 1250 684706124 684706129
    0x60f12170d2007060e07062a2001110c131805070b03150102010509030717041502010609050a05040b04081803100e07063002190903030305071d060315 66
    0x40c4486a0340c0a01c031800316900f414440f583c0034845006901c0c0c00540007150070b010000c3c1001c2030b01e095401d8201d00c00c0d81307038201c2103c010700e804644c0340d0002d1160719142404c0d0004000205c1c0d00800e140011503407004038424810000d04001b00c508014014140031001c010410001c040d912010030304100c5485003900800c80500040b000741c172901b08195907a1800c0040c2c2c0360241c00c4c91032818110380c9000100051030002009840806034001c1c0c0700890302c8082c5414044502a0340c005118413804a01440c580c10380541c402c200300c03006004203101e40e55802c2e24180c00c49004840240410a0303280000e00001d1095004040e11418514520710301c0c0d001201092924500545070032003d80d60b0360304d4030520281001018000c1400e440c00c4540b2070a03852100010800a182d0702103c06504040305d40b1411140d015100c010340001c0940c04218603c120040c40f5802522058000c01e1905c00070130640303846012a0540009004118201d1111050a200390f42e0300003407902007402c2c00e00c3e4000030070350f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 684708624 1250 684707374 684707411
    0x40504050907060e0307060c12050c07060903021f0f0f140403110301050a050c07060c1709061f050f0913020406270203252001060f12170d 61
    0x407500000181515410a40040c1c50b01880304d0b0b85a2190b840140f00b0001140d020982c0c4415035480414480783d501c0415081c0d410380148404402c86014000010501540c0210407104590080307807003500da01002c90b1069036a031409a0100c0015141203090721456015410402e00d03491640b030030000c2c40c4c03010840702240b900590070459040b424090043c41030b140c24080d04e6009040381d4010010b80c00d22210007081882580001005240c640502d5008540140c420690071080b83c81c0365401407401601c815100c84080b02c0c00724006a01441e807044080c0d80f030110905072903014200e40a0800e05c10100004004028040030202c070b070181c0302800585807800ba260007084011502c2005140c2e80c002c4c180c14500075000c6000040c41407041103003c01d0310000c521308144840740e904c8000741c0c214070220f0705080e221001d081d188800003c07016400c08d05501010484170007450381504075072200303009a6100e0700360b14050584162071314490000201000141188002d04400064802c00315644640d131 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 684709874 1250 684708624 684708631
    0x310030b01140a0e061c06060803070303020702180118020f0c030403050705150a080f1305010e101404020a0314160306050a050a02131401022803020d0c0809090c04050405 75
    0xd11600000b503820340c180681e8010282c401000164080d18009010600e007020010300748003640454041941809000c2d4007140143c0008800d80303a46881e14203020300a9881003c0c00c0707008003a1132500c3c01c01c041e800b103503d5044c0d6500c0840c00010039003c021000203504405902c1c0300d0f2081c02c009030029140100b0003000110310960140080a20b03180412090020b00d000710020400b0800000304000d0340b08502c507900000b6010f4142c0140c0794203810501c050280080105250f10384041d0075040307440000c00c8030b4600d883c00001d1001021580c0120600c40e01503400942000000b01d042c00000d070140e01c407404861005040701c2403400103d050700130110103640156546680c0380c0511290254034010b50ba0720038040d10040d0300c1d0040c0307100700d80100d08144c40b456840489001070b03480365a20a200c00c41d00c1e00702d945c000040d20300c0c03d40d03080c01003203080d1035085001d4412039486020720741c028802c003030417103070420541c604044660f002e0198098000303111043c0b154081002140a51311440762600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 684711124 1250 684709874 684709889
    0x209220626011b1e05040503060f09011a0102030f09032118060a0e010e0a09020d0501090b01021f0b060f0708130f0f1a04050409050d080606041a0310030b01 69
    0x15a02030000015085488483c40e03403924042c00084445210380042c0503054031402d070003030019283c02c621421101d41c025500a0340d0f00d0b0054009011040201d801c09900483c0408020011044503500c00004049602500b071301503001800000031410603031001c0c1c200424060b007552a075200c483c01039240d01040703500c0902c82c07001c0815090302c454074a031001d02c2c4020703003034406c0b914207001c98802402921070200c02c2070421506440640712a200c00d2022401852184025504c03036001190038005007809000b0400000c0c070f040700140c00d661000031380960f0550213041a003250003811150380061300c0365607801c90b0480d0040150403840744100b0000e0180768001d10002d80c030b800d080e809811301c00307109510144242c503001c882402940c01c410283c408030741441e28054113127614150400c1d018000c40e809264807920385400c0c002844408074081051111968403c0701c10398901003040014000c5004060083c00da21460184101d02400199000030502206403080f999a540300d00920340241c11021 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 684712230 1106 684711124 684711179
    0x1051b09091e0a0c031104030b010b0a0306081507020d0809030415091a070515090a1e02030a050d12140705070c0b1602090105030102092206 62
    0xb8107007041d114140079898030341d640d00000c140740422500401d0074186580c010945800494090740d901280030141642445130280a58000080c0c00d001d041da10100451004810007104420702d1016900180314901007100078140a9006044c1d401d122900702030181000000c4141d0b419a01005140c2c00c5824540d8070803103070500c181c4d1000b9504440c6114840140e41910000c02e04071b401041100c081e40e0740b05000c0304406c8000c0760000c1458001461840000d2001c09407080c054a10403800100e480e4a900000c1c20003000c503504a0f65640f1220025818a0b0820301c4042c814003001c0b01048584680803102c1c507484001004141001800200b003c1044442d4103a03001610304103207010784805441c0c1c070440c2c95204690080e8031030711080000180b185014000c030703403c0040103810882040d103a2002d50000c40c1d045801d120381c0986468001c20340484141c3c0f04103600406510a8 = true := by decide +kernel

theorem cover : BRFrame.Cov 684532374 684712230 := by
  have h0 := BRFrame.cov_init 684532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 684532374 ≤ n) (h2 : n < 684712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
