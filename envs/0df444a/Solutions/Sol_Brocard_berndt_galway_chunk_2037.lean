-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2037
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:30:30.025984+00:00
-- url     : https://prove2.me/submissions/dad6fae7-da08-474f-b552-0f060ee1694f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 366187050 ≤ n < 366366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 366188300 1250 366187050 366187091
    0x122007050f012a0504081009140102030708070e030c03060108011a09161b1401230906040b0903070b011d01051c03030504030e030d0f08090a050a0b0414060106030f 72
    0xf004500d2090581e185011840d41050700c4000041c4401000001403040701440200901c80391410000340d00b01440c20000161190740c03805501d40e07407040040100d415007200802d80c002416241c010500720082002ca45400418500d040d07040c8584400000c0030501500614203005030064041e00d042e88080070b11004000079104011107040650042c4011031181c42608016403c030a41900d040e41e01380c8450500c148200c00030445651100c0500b804200e83e1459000c140c0c1d070702648044985042c950b055107418002e080140344520110104812400c03c009541540d90002c100e4a00b41d43d40300302d0340a503071032600c02115001803070b00000240741c5805001c4440070310110606045c2c0041d070380d408500514006204070280007003510620030984040281100701990703074881442d0011a40300c0901241401801d0750459400005503800191021a0740d03d8110703806581101c0d0b9841c0c91525504400303101e0052455403084400010314164540c000318590401c11804024032240c400a6042629 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 366189550 1250 366188300 366188321
    0x181807090e120307022122030f0204050601120f0f050106080f04031b060c020609060c04080c121002070f0b130305190e0915270106122007050f01 64
    0x800890340120010400c0000f5a844055032065943c8805000c5044040e180c1d581d890340f60800010482001c40441c1d0b02c0c46000014601c50350000e420f165640311480d802440740000d01440d01c503004650b90b6401040640c500369036040042c0718408600340400000d184240036600b12034100000064a035010b41e21050040703c0001d1182520380d11901c013030f07500170303039040040c4018002d000d12540400c1040c4145042842c0643c05043d280c03d20b9141285401000760160300b90207802c1208101a00c00012441000b000c1070701d92042d207034050248103080c45e450282c1008914000251603040280044c0e5028034548251038040c042e8072890001c180c0c54161000c001d0125100300080311f0402e400c40181c902d241e003a0b2520241c050360050210741814000d8641003100680c50704500071501e0103008034001d0b01003602d07111680d0b140c1241c104442950622910041c004107035130254078540c064001ea55038448044000043c002140d0869000743d00c4000c0680d19800b0350043c1c02900c5106015502c184c3e03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 366190800 1250 366189550 366189553
    0x13050111070f02010c0f02030d09090c02070501050d0c0201060509010311101e080603210a020f150105040921020309120102030f011401090801050c090f010813060902181807090e 78
    0x702c429500540b0303a094141010381d04401d05111600060340e003040004100c2c1c56595483d55441d1030007800000782c0d49030304503407411364000e20018000750b41d11a05032503c1d400c00ea9804901d041500c03401b1707030042860b504006d40100704c030000071091000700c044803107045800784c0d4101000527000008407218014041c00b8840d40c1040d00c0500300040c0315003030340b64000000600340c0d20020604400340d007c180d50030826480c01d56010a03100705480d0140025109031580c9000340104e0352510701c10034a400303c140203540c800e5540c1c3d4000000c1c4640000d115007440d1090704c1c0300d0464011510003039501d400200c01284603a901d04205d1109480600940c0e00031182200c800405034280040b4104144408006038108100b54200052000c42400f40034000ca0041b4040360b82c4038600c109200051b24055185410720000100380012040341c0c007012a041c60304010001803080c0b9030320004101c203680400c1c03080e01c40340040600804410384401e90000a02c0401100d11180e035814100e0140d0b24501c4110115 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 366192050 1250 366190800 366190823
    0x3020d1805061b060906060a06090303020a170408070311100903150902040e070e010e0906090616020705090703020a030f060b1c0207230105070806090c0702181305011107 75
    0x214106540949054185000502c4111001810f070381c0c5408000c68001c0d095510000c148400c0d800e00c00c0e40c24000d0a941d1618901c02e40c150788004e50b503980440001041044041285002000d46100380c4000d480c48105482031140c1d00c2c1080544102451210fa11032294400c14040b914041d02c04241203e5004120b90f807039400c0c01c540c20f4001c00081c50306903006a110344403e080c61009104110150041c02012860b55050090300922220000d0403c0c4c43c940c0b12000b44540200001480c0c0c2e8895002800d42c0d03170000d5601ea0403030411074950301040e08840001c060000c40b64054020b807928030790940c1c003000351564010b41c44041d20b03603034070900e00003040401007240c4c54404880c04046904030440050f2805280da5602d2504c29100c0d01442c2d2a075041d000035041c04082801543d0b00b03c20b081c9400b81442c144240060082c03240a0324580d00048001420011521008802c141c911080c810101d468034084044076031f81d00c03041d0011038940d46040200c0d0f5285041c20144c0d03601c3c0b900480d00c90306 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 366193300 1250 366192050 366192059
    0x12030408060622051504050c04080c030102070323070c030305030f0615040b0d0b0303040602010b1309020f1309050124170606091b0301150305090d14031f09020703020d18 75
    0x50a02800844001400d0081056161558003980e801040b40c230340060b036520310b0100ca0300d0504c4521410f0501c0f80e40100082c901090b0710003240c01402ca40c4402c6400f9046141d800000e1b5481036080042202c00003010000070705421001541c4503002c4415629184d503102c0d000c00000003900b0320450303007800c800d00c014010800310700003a0061840c1d18000207074260100b8006443c5800c240d00000040c0e444041c0c02e149030901c59499003110300f0110060000b0f10b1030b640080d200440b0100e41038028000741041e14066482c5820084480c2c0d000402003100b45418100328a5075201d101000c0f01801c00074100040101c0115018004041c0d040007600d03103034696500300180090054880ea03a80c0e00906000050340710203c000314000c006264845148020408010b0162113000745a000c5035000600c0741e060b8503801c480d0030f0f90b80f014000719540e42c0e0b6881002c1d19040504d03900c11307061400f5501c0008a156480c690060100078000d0b0212004013072141d0085078911074500c4d20b040090704080b130401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 366194550 1250 366193300 366193369
    0xa030e0a080709050105010e090903030103080f0910030509070512030409020c0c060a030903140c0d0c060f0e0601030501110a0c080d020409020a210501081515120304080606 76
    0x1594054014255a82240e651500034036140180e00001d91269861004208030341c0c0002c0d44820b21141628050309510305440c1054403400705100103440c1210010304c1144080860048605542c0001c5c03140c41c010500b00c1000340108400c48106105104401c0007168501e0800d60682c000f089040045290505200c0c4080107504500c10403280c0c0e12402c6158441540c60308007030541464140c0d000599000315050007468201d40c115291500d50303040101281255010800c2d0f1204000d034103288000e10a00d250000040002021070480c0c00c3c908040f6580040300131134102d040b00e000d84003d0040c83d1480b50740000500c50a1044404100c41d16011400210b540020708005420b40400504040c0e6402124040c1e034008248540050102c40280c10300c142c40040c1244252901c0401b00030944c18000320f070360b035000d0220102c00c01340c1902000a402c00d16040310300c40505000b404402c51a81031030591a9a40c1003801024035500a520010382c0c1801c12a400310052910b041160204034a41610311 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 366195800 1250 366194550 366194567
    0xf0c170a061802060714100c0801050d03120501060203040e0903030f04140312010b041806030b0703020c010f060602150108010902030d0c05031b07050111030f19050409051015110a03 80
    0x1440180092050302c000361382d86002504a1a000c0c1c0302a42d40f4003180c4900300d060041400c2c0c2c041c05507140103200d5040301d6022202c0c6042d02d009582403040a0300c0c60605903140c080021641c080d19091000109001d9404405041240c40801c0c03122840e44a9081068a9001c100d0301b5400f01c0d07841070000360110b0002006643c190014201381c034039142600d2050542c41500340c00c0700110800c001010810503168072922403400665010801440c0d08660300e0410303010001c0d0005040680103d24442e1301c80080d0300100700400030a10801002c0d640d81c401130340300c521180c051001c031802d404c0001840b0206000e02000c0796030041c090719014150030030075a80c03081054800e41d40c911040c4421001c2d102040005c4540e2141040107000c083d01e0000010410000d0149024058000b8002c074074501000c6010307540d06d469a8a58042c61000c1154121494021980b10311056800c1c24240070035500c03041182416074104600b540b6492282c188180e030f1070141454010b0389a0712000146005c6441460704 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 366197050 1250 366195800 366195821
    0x10b01080c0f0a11010e070e09030c070b0c01062102011b03172d01050901080c060f090d02031608010506040902060a0f0e030d02010f05092a040f02070f0c170a06 71
    0x1940e0010144d41000d804c4071003c81364003543e030380503540511040780001610359001110100441c42c01d809590515141c03942d604c1607049099001c10007104422082d041600503010111f0f103001540e5640310308649650300608180d000c039000d400314031903000c1d04400d210106601611503524082118441554290008041c1c3c0220910070710621004000b4581510b9601d109181040c600d504000402489603030691180c403596100b50410f1440d0f44030002942c1c0414071008006440e58044004a0307000760709510300943c940500303101e500941c5040144030003940d60700c0c802041103503503d00500044906004000c6c1d809903080c09a415100e21030809003c04804916004440c2547e400100340b40140e4540048050b035102e05181071080420311605500803680c1000b444400f80e6641464028003400302020b0070000404074950064a880d0031600010290300011542c0344202d0070103001001c0c40c80d000311107124641c1c40010344041656500400c0c2200b80d0080c01816a2030b5542a008001880c0d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 366198300 1250 366197050 366197057
    0x40b0301181e061e05060306011208030408040e1801060e0601080f0604060e0a0c0e0409020a150302040b16030e01020604030905060a0c06021902071e0306240611010b01080c0f0a 78
    0x5140b80040d00c01d0050f900d2596001084400c00d150402403001502c20013003c25000e40c0c0141c0041055521040300c0242c03180e004148180e9a44841c14150000d00c0789400c0140b01c0107402040c407a418060491b01108890814000c001c51a212500ca0b908a40e00380c074102d0004004802042104c01c1c400402034100c0e4000713000080b501d035a4041d80b41b5a48007121500409582d038120f40321240d0300001c82c0d440d100c01c03c032020894094503500080410040c2d01941c03004903031310080500f0b0a0300950480300030f001030700c48440d141c004a0750001220380030b140c0102e00041c2d0380c410b0b0000ea9400082d2003409a0b5254032469505420300c4188491038020a211000308240c100c91701000c60b18910040c0395180d04584140d40c2603512180107480d05481d0b80c040007101c80395140642200440d8146542507940c004000306954139209000020018690300502c1c41907404030300019038079040150196009110002800b40350300c42801510201021a0b8510848204000d80c00c0c00741074880c02095405610b05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 366199550 1250 366198300 366198353
    0x1107032409150c0e060c060a1508150105040f1a060a0504050411071a0c0a031517010c1209031b2901031502091305190905010506040b030118 62
    0x100c46503642c0c00d202d20400b03045981ca000030300140ea400820306548400641d01c1c0d602d004139005101d40d82e440000c1403080d61540d220102d03c403411043d119003004000d00310071541c445440702d03c0d11141c80e500b0700c42d1a11561400390b00c076038900e11034004c10188a6030113503c60b24413240c4e00c0c240035143e441645100c040000c10400400c1c1a0364034411500c80e181100050380d11424949008134111140038203152201121b001040303040e558800c2111001c03d103524005c10b48480d000300d5a494840c07241c2100102c5401581841c0b03895405500000401403550307168a580c008100000c07045628510010300083c120400800d41c84500748000700f820f074800d0044a0006080c102c00c803100c070612803d9080e03030003409801001840b040d0345007007800d003d103c042103181c600781074001019a034040c180343d2495a290b800081c0002c3c144800e104a00880302c0b01441005a10715015000740300c126807151144d0300d04500510507080510904026201c040728115440c00d41d5110321149544041d1001d52509015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 366200800 1250 366199550 366199553
    0xf130302031312150207080717040f030f050105160e060304080d020c0307030e030c060306040506120f161517180a08030103021003090c050d020f0618011107032409 72
    0x2c24985009104060044004000700d2801c2540f1050f00c120014a0174010300207580410a06411a07000f40d5100300710040205800e0604c0e440c80c0120740c4006078101c1003110010920403040c0b549418148990000c12081d46e80001c0c090700303e0004524840010918403061b2110308005000303580040c09410500d040442440f80c15081c2e0340000c0e4105403a410100b012010550801d91182280e02e0403405014029a510045825400300400b1144601c0d251008203401e074503450998117205000d28251000401129143ca030b540588180740103030300c2001400010101070020300c0021402c3c4030b5440ca000300e07411051b503481d49100035210441010b0100c2000d41080e00404c01300e00e04600c00d447d095125891801009180d612651200d803e244c180301c43c42000603803200b483d1050754002c8030b16503584c05681c00803440d101207070202c20f40c000800291520318141004500c060341c103c01da0350794850849503c03001d626541c2d136110051642c0508040021802100910801c42e803030708940c0002c07480e001d03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 366202050 1250 366200800 366200827
    0x2904090323071a090a080d0b040c091802041206020901110a0f030909051519050d08090f060a020a020423070e040b0604030f262106090f13030203 64
    0x1507034181c85002400180300d0308000e2200c810003001074400b041c82c40c2c0b515040c10007a4569521010041c0001000510202420306c0c0d82d00010030b181001e04100050411020301a12995203405a040c1e0446a4515a10301d054140200c0d01030301c007412000031011440d40d40741e4019401042e0301c107041c41944040301d15460b6040004a0040d40680002108000b140c14040e26900341c0d5046a500281844100301c40c2c2d603002000003403005025a807090f020086220480c280310a1034015075444034464810505002075400a0040750710210f6004950201035420000c0c0e51050243c03600268200010180162900368024081c1d0351a495480c2c100c0d801216000202e0f4070100d8031140400c181c910ac1d8a16402c080c842c079000c2c0c26054800c1d03481c250031502d64400291048100601c0d46115800407080c00303100b82d000203080c0404a2000fa16000c011000082d5103c180c06a0400110304100142c540d14000c52580c0c0600c0f09010a026151074124068030010041d41c026400e41c0300401800da1044c51 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 366203300 1250 366202050 366202097
    0xe0307050f030d0510380a2601030f0605040602160b1f1d150a0303120b010c0809040b04110412020f0a08120706060902030f0a29040903 60
    0x505000d1030740d842040341c00f28101d0b41c01400c0080d0f882110b404c188a0706150b00908002e01103003c041c82c241d44e5003204d1541c0030000c070710501c42d803d105c003042000c0740d00c1c0c020f040d43c02c011f41c81d100744031420340c8442d8600003070000900c40a006d0b03034603c48030f070401300b035043c0d115940203401030b2000f503c1c0581c204441d80c03150b14500c2e02118040030210400c00d80369070071b0107080d1808945502400095280003503400b0322940c0e13100c0303985403c82e5400104a8420405441d00b020040203000100703026076900b006491b80090030900a000c03402c2001c0070b1100e40c0b043d0714000145070f00c605003e0034001047c003448020100341e045503800507507400b558141003041c100a000100501422102000494414030040607000000c2e07030f00880d2a190280250031001c24100701c507100c0b030046070b900ca10300c0e420030304060500c9510100d8024030001c1401074400340d800303507988240d0f00094180502111116a410860050301810445851036805014070345080d4010040d824001d20700241e41c8440c0b2000d4494401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 366204550 1250 366203300 366203323
    0x90e0f0705152704050906160f021f0203010f060207080721061d0123060108040f0f030f09080f0d080a02120a0603050609060403022806050f0402041b050405040e030705 74
    0x3c10001d00c55092615010300783c2c0c00f8030f000c0054110741c00d181c00c1003950200120400000c1c0035484481d060403e208209101741da014010088640140e50781c845c1009603c02c4c056018603011558000c140305000085141c1203e260f500140f14403450a24614950507400c2c1c05002800c0210309000c005c140203008a490a42c0e010303906400324070203000100d0855420801e50036145040c8807101d4000d5000c00012503006e2020f080018030b9a90360700d010885c81385c4600d0001c0c11030071910404400c0c150b01414a22046c0302e20b40f5202c6299484446141c1d86004102600400d640610504080c1c81d104110454000000300c1c0050b08100441035040005202140c01c201002d03580c42c802c2061000400400c1d4000710f900b800380840d0300705604d00a44407954111011040c01c92801d0703090103002c00d443c813200c00540000040000d810454285044120155000c2c0d100383d0802d060064003c8040203003800382d00940c4c0300d0514007450241400041e140507080c10a41d1f00042c00b071400814000c0c04064480f030b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 366205800 1250 366204550 366204607
    0x1d0907090905010f03020a031112030a0203040303080606030402031e07080a0302160902030610081506210c0f1218010203040b010906080d050405010c060f15090e0f070515 75
    0x203604000300e0400321241644801d9109050031020405611500d0f28401981d4109100c8540340b10008082030003046682c0d081c4420744030004800303000d10b80c040702400c20350f032103507450400607150711382003020342c3c042a140a5416080844400c813101d000300f01080c40420120192006156100348840c24060a504241e0150304442d160350440c800f11180400070300001d240441c00d50a140011901140d08050f00b60144800344000c6002205204e11004030140000d1400b0760310403500703c5504012083d20451810185148042602c030100101230303400200d0805d031486d0510b5091030820404600291417a040c1210030b031440c00b213209080c00150f110301d0054541100c40d515210002d000c4400aa003c07583c00d070800c11840c011a5401011941202c00928040e04200c8290a0004c0100040086071494034034100c41da07045401d11284050131641e03c01d00030040345003505200b0b626903107241e000341d0f641d401c2100d0078440e40c40c007140b00b02561880004040e05043c4015540144010034002c8400700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 366207050 1250 366205800 366205817
    0xc030303011e090507050f0708070803010b04090507030c0503061009080106031406070203040f050402180a080f010f02040e060108070215070804060e0316150f0203010e1806010f061d0907 82
    0xb84441d4045a004005030f200800c014680b221000b8083e0040380c0e134070280154001491030910454106940482d42c00810090752540e5421071005103a0051003031380e61007400e200016100500910030b200151180352151803441e0b690408001d551a0070b0002082404103140010605000910500e0051482000f06108041140d003a06103000c00080070300d401c540c010003040c0700c90850b40101c1d00c11100255005600c03800c845811011007280e80000f00c1d0045903e203000540c565000401408140e003400007008000c00019110059103c1c6002c0d9030b03c541103400106215504ca051550361180c19071058801545604031b0f010490340c8156440c5000900c0841480140500c034030a8000c6418510011440c0c0381c910500c8044119503000081d015030f02c8040b03056100c01030f070b4000320804500000111f55960715140c91450881c8d06450300001c8040440f80f00d6590304c80001e249040c0d60310722890710401c614051003100c0d20140c40164034039007808049103145a07250410074500500e02509e48056 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 366208300 1250 366207050 366207089
    0x30308061207140409021f030f022704090f03080415060e060d052e110426100c08071202040b07021201020c0a0c14010212030f090c03030301 62
    0x908014081610549a40c4840264410002802c10440d9491848103010070b4800000900501c03c0c0103021b5041039184485020403031a103c88081c00c5650382d1001c0006a199504074002c074010036041a00c0107400080420002e16105420403003454010408104400107a0343e246107a2444001140400c0c44002440b082090410100071841508002001510b1070a0280d101880b0083c1400b40141010068401401028010b8202240200e100000a43e0f900c07620307001001d04004040c00d0030f0385040c528243c2124110200e0342107075503445008050346400f10105807480310b0174240020320b2080d10356840302d4035030134011454414030303036245c06165107000030001c1c212048000e01582071030f204001c00d0000203007010549101503010f8480f110004403410b00d42d40244a140440802c520400003550100a80840c6200c141d41115048a00b02d4000c2e03401039036501c00001c106007544074203000043c040b2400b02d00150b846031807102142c2088132030a001ca03085078800c0c1c1080d403804019244040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 366209550 1250 366208300 366208307
    0x40216240f0203070518030709060b0d1a01081b0412080408010f0923070b040902091908031605190302010c0f14070209040c0905070c0212010b0a090e0102041d010303 73
    0x601450709400c2503103189080030f4014100c1c855000d0a856503c10880e0101064400b0490f0700060a0f52207801c005184e1036208525080c3c119141e000103107401c2805120403500450006d107592901a10755034000d8440d45040b50a110314405440300407142400000b8103402891210f5007200d0060217281c0c1c0d243c0c148240300382514600c0315618510b0b41000c0146000030540c03018a00a540c8030680f86001d80748c02b404942c1050070a41c4801d82002010401103010030040e8021700b40c04004603001010380b403e00410340042c1840b882400840c0e08280a0100d4200380c083d0180b11440c8204146c61420043c00e0121036400c911540980041c5e64030501c0c070780c0440c0c2040c0e4009100001d030070500c07500c44040002e050503100c1c90000a015407011400300c8d040020001c141e0b030241007088010700c000c0c5007082000342403003140c2605a1080540445d912058141840343c10748000005c1c000e46480c03402c28003103102505540d8982240da40d801c02c4000759050305142a40e4591413800710f2400154518203005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 366210800 1250 366209550 366209561
    0x5100f051e180414070f050c030d0b031614190e0702150c250507050307120605070807020a06090212070e060f030d02030a1b0b1816080c04021624 64
    0x4038021441c04e0030042407510700d03503500c0e50700030f540d80b81180c41c0d071855076801c544030700400b440d01c0301d02d110128420b070488049030400104290300341c04441d0f2540c54186501040d1185200f44500c001c52403151240c01d081107070001c51400b45200e014040c8560700c0045000b07504003210410016004000b100304512000c04a094103e00701c10708031420080283c16801062000c03c100c0320030071004507550b408003c418081240280001800e990500b992143c050f0340791500900121402c0d854040042c9426004410090003026954001d01d03040145640309c03c000c010a2105a81c41f2100e001141060302003000000003a1140f0b501c000d000b400c0c40000c0c8900e01b040410014881c2d0007803821080300d183d00005854250005107040c00d0030880602d9020210741d00c226001e0300c080301c9201044554803844018100011440007121004601c00b41e0507841e801c2c03240500b20060f0041126a078007803074a500640710301c110040b10007110075125581c0d4001461003068001c03c0c0040382c0041180c40f915403050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 366212050 1250 366210800 366210847
    0x50d0b01020309371d040212070608250e21010f0b0315040b2206060b030f0f0108101517011e05041505090c1002061006020705100f051e 60
    0x882200714205040c070000760354408034014214480078005800c1d548c1d4201141d0070411000c055801035a00c40348014045081210f5448140070406007894800034040403160860500756905015100301c0c01c2040ac05005207100f40c0d1070350040c0035000032000001e00c20f103c2c5664004600180d02036000341814107021103012000c102d00302035020007001c07a00c80e44c0095884544012024820750f4050341d402ca01200200c3c0c0030b402c0d00d151803c0450b440913250001c50003500c0c21030710031000d60380e5010400c0102b2000d0140585a070803400c4489809201031300940c42e4034100035071500100f9103600c94001440ca41d10504004e0380e44800c045203040390b15254040c424500303c070050040346082d40364603440103901c5403680d083e15038480004541480c28800f209003510010140000301a00c510700a40e06c84007034910800310b1001040004140b170001800c00c0c100d410141c031036100300782d203090103544100400c9111418001d04120051145c20b1000984810140300c1c04100d465980ca25400a0040c10701b408 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 366213300 1250 366212050 366212149
    0x1505120a11010c0821060a050d2d17070b0108030a08040f03171302030118020f0402030a110703030c0206010609081b010e0a030c031205070201050d0b01020309 70
    0x5490040740c03034007880030780c402000c0c03c102ea00100c403480d140070544108129074050810300c40d04420070484510142c2d0042000f21110800c6517210420485500744e4074600504000c8070000509203800031400c0451411030036004100703c41503035151031060100710100c80000e101c4c00a40c0c002082001c50580d4007602040300110300300345201c00e010f4038040004c0c1c806800c1045d01c0002604151007105080008074800c44101c085040c0450142d00303d0109a008034801e500b80781c03160385e415131001c15440400ba0000c08418841b5100f1b000d100007944080c011078030003502c410314424420f501e10001c0c18a6446542c00040c41c0c6a261002070030914181c211104200400c8000c20011000142d410909080c0d01406404e1303801d00b20050342d03000c2c0c98440c03251300700300103010010078044003510400481c0c1c010b4880c0c0910b0300e000d48040321a0301c1042c2000780405c105116606a80000741e00c440046501801140c1c42c1c50083e4000940c2c25648002c02c2d060702e13050030b074001040390001d40610b0340d5060f000c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 366214550 1250 366213300 366213313
    0xb0912010b10050f040b0d0c0e040b0a050409110306091b0108010e0402090a0b03061501020714150304031b08180d0803011a0f0a09050102150c0910020c0301150512 72
    0x10300048044000c02d6489081040105007040321244604c121030003401100c2403e81e0710b250705c41e800c00142940788040b00200f210070303150b2030300d50404e400707070803078800008148080340f07818401008028401e141040d41c52078903010780501c041c0c5040007254010300d1307110000c10285e00340584a00e10a440c10400c10b0401a8a500400031915000080c41d082a81207504d007007a5590400224014a100c03929654988920018000001c4403813080c0d000c2080300380d003603030f1850362074400400c030400c1201020741d0071031460b400000a81c41807401650b003080c442c0c508460705400c82c1c421480d40c0390034500300795281e090014000798081c05181c0c420741003003400d40c1c03c0482c0c1a11625000303401d010504c100d903111090f075007a45503598a800c2c01c0300e1100d442501c245445a100c0800106401e4031801124050302c20f100d0b10056010104440501c01c61101070002c0c60079074a80223101c1d04010802041041d84101c45141e1400e0340c080c0a01c0c1a189500001c41e004035140000b0001c5140081103146250b40010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 366215800 1250 366214550 366214571
    0x1e010b01090306180b1914190b061e0301150806030607032007050703030e0306010b091c080d0f06050d030203030a0b0a0e04050c15182202040b091201 66
    0xa1101021281c00c0403000499001483e83c581c2a0700a0000040c03500309207104100044a10702111086c040a11074200641603526509503804032040e00d0140c2d20210218030050442c0c01600078040290001e07100c0c508200750030080529032500c0e80b0341360026082c0440103110f40f01d5031064810b84000300e440c00380600d0415201281d1504405000d200416840f0601140103840001031249054040401103a5900850a0044d00e035022030004400003803451104407014079000401078140d0b6411100e0381d24100c001c03070800640711400c250703404401519406180118950308040c01000e0130303019009c12142c08601601d0210f410b10780015218441d9114400c02007a80003094a50018480d1400581c85200600223014207042c0c3e403182e55144070710020032003000004201d03009040001c2d11074410303d2580c03010030003082c001c81000503414000c0e00130121103880c00e502d07100302800b0380d040e607540401114009102a640b00e80c2280355174040020340740c400c03401d15a82c0d14a601e0b080b44020040e88850 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 366217050 1250 366215800 366215807
    0xa17061003051015020f0106080a17130e0103151b0e19030b13030f05030c030403080a1d030702010219020a0b1c0f0c02100606050a0f11030c1e010b01 66
    0x2000303240105a03940000400f00d81202c03140d03030050303d0410040d5200c0306074140000e555900c1d1301d5a141940d420042e00042141d000194441c0c99640031005c0041d004070101205c2642d00300140c40d006000c01c0c0500004d03004120341805020310b000784c06481102d00310f0200d03817003980d446010501400c9004407114082903407182c00e00001240803604030100e10000300c021095800650800b900201020303052103000c480301001c00034203602c60b880c2c02c10041c6825500359002d0100715a9020400803c1001400091040703100540c410070a810004a40c0134081800024550400034417040d0b038030001e512815983c042000401062041122403140003059000ca1141e6800380314405040c18040740010701440c0c0302c40301e01500d040c00c08082001d14840c0c480d007000b808144c00080094006d1307000c61500c50a45015640c1614690340f611440d000803074504450354842c4800104c101310340d400890030034210500003082201c000c28020555041031401c6004401c22a003181c00c640d1785401c0e500056a40c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 366218300 1250 366217050 366217069
    0xe070b030a0e010609020a03061a0406020d0509040905120c0709061203030225050a021018140d0524010f0305070b070c0510020607081602061314060a020a1706 70
    0x851500120b09040e40c6990540074180f25000100620300110b49506050752641c000303000c072010400308000303440c1d504085544510860180a0058010b6004610a14028001455190b10144c0001401081900c465003408980e4403550780015001032940000b15040008074003508464004101441c5085480e155801c03803014000c05068022419080300001c81c843e03d502c06d04402c02c0d5000c089903519040381c50b410700800c102d00c13401c0910818440e01c0d10030202c4090304003138120400c0e0b0245c00c140c00c031241c075225420a56840341c50302029100141c02400103081c0c048000e042c03044070300c6030420074102e4104140c120b0602000711440401c08070b00b001174075030121030b1070754a002d130303a460782d0704000380b1801e02c5400568000c2000034008401c01c1d0b0016180303105075003540d030321900303a21941070a000e450050010103005a0007003000c550311460070b6148105007440b071410111064071003845981020821261a145a0b901260460001e50001c00d00ca101d0010443d955007d8940540000c01c1c416 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 366219550 1250 366218300 366218311
    0x5160c06051806070903020112020708070b0c2a070501050910050a140c0a050601170d0e0613080703140303010b120a06090e010207020406050d0f02190e011401030e070b03 75
    0x94480011400100074120300b40810040d403025a20f1500e08000c002e807560140341700490000b0089020b20040051900c00d94203610760042035249885115110b079521020090b2803000350345000c220160f501900c4140181d1540040e11070141d8240a800140b03081c81c040398000390511104000c51011540c44e03030148000e007a0030b414411345642203c1d00482e080c80d02e100c1007500c0000300280008090b00002910f080b0303148100c089880076031301d60321404042d5640ca80050707100d9000030040e51059000f010851246c100240c00c0b01d00b0400340d26031106111101d41e00620b03e5400c041418814800c2c0c5640f41038017106118011031031035161005250a40c42841a03c00c4aa082c10002c103400f1841c40e00288014240007009001095040f207001e8000d40c080c02080b4402c6103401d00c0011181007240d0000b48498003300c18070705d81d08454003808048800c81080c04c0307881d841008007180c0004040341003400b0b0701945044503900c2507210005011500d030480d03070030340030b500c2210100a0705a01d00708032644207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 366220800 1250 366219550 366219563
    0x190b031b06071a0a050a0b0d11040207060f110c0615030a030c02060c011506180312050703050c1911180115210507180b070b0c04090218030105160c 65
    0x4540a0803e5080c101c503c0010114041070041803000d541c40039006a400358035090740800c6101800c0701000540041480c00030b08184070001c1d02842c9140c10b5024011840c040c1002061a400ca00c925004507085400032140d6504003141d40b100d106020040507030701035101a200c1e02c0801000740003d41e20500a1401000c201c0d00d621148119107d82054400701e00d2078170b0003032245030a080410080310009024680018031b042d601e00440f03204034481002103940084403003a05030105d040864040d400040180c0c18442e08108200e80f01c502000050001c001100d81001c0b103040e6440d011240c6003102c21220f01c588101d83d2941401109800c10a044032510340c0502400c54040405403482c003660031401c0c804600786640312000d110359401c1240b103600d50f5034860818000d00da603203d0b1040c0c03490151281d102e82c00d202c40d00c00030301e11401040e0090009041c640c01c6c55504c21b400d02c182e82c000040c0f41c1650907044800d6006040074040e680d00188030460441d440c001003100101010324540024240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 366222050 1250 366220800 366220807
    0xc030503011a04031203050106020f1207060e0c0d030504050109050609130509101409060109060602061501051b01021e03070c060b0a05040617070f05060324030303190b031b06 77
    0x100d4482500f254015a80154014040765034280d004e80140408d10032840540030b01c1c4800541c44c0c1303020a1140d801a440820300303052100702e0715850010040d185804000d445a810603900a60b250085000d0441c802c0e0b460680d501d0030100018a02807413a031285008200c1030001c0300b0b0380d944107890062043c0f0459000a0700340d48684001d032a0a030070b0406600308914007540603441c02c10300081da6204082820403204281daa441c208011603019110303460068000102141d41d480c503403061201001c8052518609002d50070b0300691000c0368801c40301004d03a40c0003510707100303000e0001004000c00f40d6030303800c03942545018113000d0149030503000014030b00c60b03030381840006903034030041404040d02d4050410090180c407040b20082c0d20300107607030400d22071054030400500c680d1240401e000746d0340f01400c02401e545804503032000007180b14510308050714600c440c285198808002441c4629110140c0c01105032256000404440c120005135010341c10a2284900c0015802a010b039640b81c1034401594 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 366223300 1250 366222050 366222089
    0x3130b0d0603080414040b0f030d0c05070e0a0c030b030c06183f01090f020609040f14010f06051911030d0905060411031603080c030d09060e010b010c03050301 70
    0x780660740006040c0c00000c580404c00981d0700f401003000080c156010040d40c4030880030001250942e40285626600c40410010038501c101d8528541394071031412107040e9529601054629907007229000c407042e03964944203001c0c41d4180600d5100ea4003e6024210300005500400d40500c81c0102c0d403108906a81b00426442c0c4840d613200000c2d03032030001f52120000030540e0412810800c15112901d139500220850320020062148001440d0701c840d11000c560f095900703104180d00b040014a6012b5900d10107082c000d801070040700154400d84141191640c10800c03610404582a0040400c10109000040019503440e030501c1c2d1512923802c018040c81d0500e2a8245188100d9030b0f030b1380d001410203030400d0800000240190256101d00c64003540b00b5290014503030742c1e81c00c000c55071000748152042080400c04200051003003510070404e603071400100c1c42c000740030341e070201d0002c8071342070354400540f47e98070350130300c00d095030590246003903008140030ba200100280010300a014103112001c074001c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 366224550 1250 366223300 366223327
    0x10f0e0a030204020c01020a092c0406091a090d05070308011e03020a0602060403120911010e01020c030106031a0c0906040b0c01090638030d0c1106070f030306050303130b 75
    0x500070740d40100155070701c84401801e80c0c080e412550005000c210322020100d0050040650b801a403c405a070b04042015541010100c044000e001a02c84035a20003140c0041400203400c84000d00090250380406c0c2001800549402540306101c0200a001d00064000950041050341100c0c101c04002c05d58858401c00b202800c107031036000039030110361000e0010310107401040e6548214002d407560000e1400c1c1424103820307562040d02c010700c584121a04001310390300407104208408010302c1154121104c4a0200c1d0840394a07810a03643e1440c034400420760744041001503075104010806807070410b10180089281070117503018100b042840441e240c1c210030406d602250300f0320303003064052140031405101c26211307a624013001d5102d41c00004001882c0d003812210005005e4020300207000c28a8024411140c0300d038030700d204031040300c04d8403074a580300e079034010181540d240220101201d9140ca460003a08580040e481940240c00a100d05180c006000c08041c00300c0720178849060340c907240f461901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 366225800 1250 366224550 366224569
    0x803160209100803070302160f15030c1806050d0b0d0203150903070c0f0501260114030712061b08090303070309110d0606180b060f071e030215070c02010f0e 69
    0x3d01444040f070b50b8002d00d90b0008140070785000404100783c038561a94504400b0120a0192562000103c143c00710fa00c3e110303030301103e610001e600d0500ca241c03101d452901c1440c01181e0081000480c04500444245424810340200100440d00810744e03007401d60100e40c461b41c501c0d0368140380c183ca950000b0780050b01841110340180d40b09000407505c5459000700010820140a564006010361060300503194643c0c1b43d1010741107074103100003075580c07030410601d2081c14000305042d010f02409400007009007040e9550f8029030711901010500034206440d0905002040794844c04000340d400501105403000302c101d035000fa1091801160a51084c20400c0c03142500120310343d0031100101c400814000b4507404102511504d00c1088841c01e190611030050b981d01e5005207500050030030a0145000b60800140000c80c0300784081e0105952503468810418400d0805402680041c0515002d05061407000c950200d000c1c145201b1000140d0002008c078011000c5007010b02c40c548a4550300350355025070700d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 366227050 1250 366225800 366225809
    0x2409150a030b0904050604031422060f170c0d0f0923060106050f07030c320c0a0b0c010e06040b040203010b1c03030509010e0d0203130f03050a06050c1b030c07080316020910 76
    0x28002c0401074242144904ae00761140a00198085076403a00103449801c0650f556009010500482c2c1c0f80c41c580c04000c0d41c0040010b5881983e60407020b00ca0825038054040d089001e46150980c0d5581c01c0d40e0319820784403050070355601d80c1007800180300d60b1ba0880141ca1b040040d180e1140d0312034a003440c00f50340c83d0b040803002070114407100e03044035800d2616003180013044240501c070320542e055001140e50380e02c42c00502140c0c0424403000030310414903000042c21885541d2700c004142d01c807402010a04154054805890513440c0008000550609018801e160f4400342e0340103980541402801c01212214034004080507200c10101d0300000c000d40020410041190035554020355044010f5902e500142002c1c915034240e8000007090403060a0316821642c1080c05000d21801541e1100010311004000031150082407100c0c011825041c030f14010a29070006c02141ea80564640c442d03e0500964414010381d032080002c02c40c1c00c2d0015031b941c40172a5040d160000b00391614010005500d485411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 366228300 1250 366227050 366227077
    0xa0f05031902210c12010614061c0e060a0605030a080d0510030611070c1205030f1c02070c030308060a061e03020f0f0405120604022409150a030b09040506040314 71
    0xd039049940f004620406102e0084901390008169041e01a00b070320320921440801d0204200c083c1010b051080061a007400c03022004c0c1f00580400221501301d5004803d03105080e40601c0800c54000d802e807041d140070300b00840003172400b00c0350b640d00c2160328070600440300e0001c3e450f007000c02d5039400c4035074002001c4d5601100a0201c4881c030400810281c00074002541d0311100c800c0000307100c01c0914980f11026404ca8051071070700e5468901020782c2e6000d08007110241031091803c1c45001c1085c800742c00c0780c3c0e1007032310307090a035a10f1814020224a0040c1c4a6440340701d0700c00e001c20103d078010090900d440c020800308041401301c0c141c107500034052000455621400016402e02c0d0b06e130300e00010015650112032008881703010440d01784d40c0f1001103400942064000d40c125110140e2040e9410101c0385244a00345405249004070752469040740c44002080c0012072400f2080c1d4150088100e6090b007513400c046036241030348406544071000341001e0144603003180320b000c412011000321040720703c1c0100c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 366229550 1250 366228300 366228349
    0x2041506050a0e0603060d0b0402010908070b0a032301090b0f090f041208010b0d091110022b050906131a0702010e1203030a051f06020102090a0f05031902 68
    0x101030032642c00451100e0018801d500790035120318000050f64010740c405060b110b4064840d584507031201c100a00180d042c400000030000d0907940400c04070b805009150152519051031310f0015055800e090300505070748652080c803103513180c900c0c80824110fa42d043c0010600040d9500400d981301c3c07400002c65040b01c5030700200321624801d0b83c4114081c030720640c0c140301030744407002048981100078010007c842078200b03d803007242c0030540c001034140340c058840c440003080f80f240082c2440342c0e102e40c6000542c114030185681c20313041d40581d00b41920810043c5a05100d2048020040e10600c40c00920900c0041047d041407070340801d001018000902c01400e601242e000018110780010004a0018150043d1040c0764206580c3c150083c0042000442c11500c4200c612005000000c0008445040800d42400141c4080304205c005010310f070001a038801860041c0440001c4c00c0d00600402c10002404100c281c41c00648684100e1800401c00036094440c40040e00700d038450aa003c110000302d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 366230800 1250 366229550 366229559
    0xe131d030711040903020a0311010b061b0d11100e070503071d0a020a1202070201030b06030a0c0206060d170c01090606060f1701080d0c30080f010e060d020415 70
    0x100a1141501400e600070200c2c1107481008280d0741560801001a0800c90f9400c0c00607000c3d540c00c50360040408000320380e00300d12001107038442e000280c0582151091560f08260b0a00512601091040d9482c000351884014582d02d9920000750030b2180801e0b941301d0b05542898010301100d4041c090083c107850000780d0f035110784440074022010a6040003810b102103046032542c1c0c421a030021801c1c0d00c41c440c0210b0a094404002d402c00d071016818141c881203290242d5032854000e501c100000040021074084a1b00c0c02460580028405030041b180100c0f20000704460360b40c02081140c0002200da5102d01c001c1206000d49948100181114200346d4046000e0f80c01491b2001c00103d42c0d66401d141100e07501c01c01c000c0301003e00ca08890f5410001e400801280700c2d601141c5068050000b451103002e5101c404c0c110040c5601c0320303e288107824200e80c0041c6902a55082d00409400c06220380c950400964900048025002510407500300390454119242c1e0f41000c0c0301c150100c40c2c058540c90b40d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 366232050 1250 366230800 366230803
    0x30e060d14010e091516050904090f03032c06130f08070f0b0c070c0e0a020f0403050a0210050a0806010f0c0503070b06031e10150b0408100b040b010e131d 68
    0x39202c0a0036030090b408402e04101760103181600c5403c503042c100e600700c81d0140c415201544012070041e042074840c01d00c00045010b0000f0b175030200348a6540002d905000050341020b448509080c089803900011302003a10103800110245c01000441490150502d1490804010349070080000e01c8070402142003418003030640561030019000300307141d000650303540c11002903900c94070900404160300c5100c00c0c0040d892a0000d10780c424003080b001880d000300c00f048a09190032690080701c042d03005070a40d40850405541c0c0404610450600c40e0411092010107081c0d1107005159504000c2c0c60f03440e1049041c8030340f00c01c0442d00e800200b565620f80e600e00f8510058801102c4041c000d104014003000c070369104000c3ca188603100c1d000035100707ca00003680000608541c945869440c10000e00100300c0500c00740013440109030641c020801e9400700d641400560320b01041d0b652050345006d0203940c0fa66002041083d540c402140e0b0040c00c030384890342c03100c02880d24201088507101c0e009a00b4011010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 366233300 1250 366232050 366232079
    0x3010204052101050f010509040b04110303040909020a1d04170403020607110414010602031b1e06010e0a05061003092a030c080109050705091e04111309030e060d1401 73
    0x4801d0091101750350b85021414059070038400e25402c0301070840010045003084a8864101d407080d6060b08290707440c5400645542c105412229400b030766290100c045103850700804004022000001c88a0302d41244051200580200003800c444202c0485079a074041401c1110003459000341003640740d800398144076000144004070140201d141188a03800c031200c05030094125a12072f40258585003041183d45c455880c0e41208003a00d2007040c8455045402d21a102010043d580c40204003d6151040004400b400176001c00c21991400045c400c240c3c03111039018103091002e08021401c0601d900c2d04000c01e2848542d02c2609100400c4030741c040703089510701701e400c03617001302c070301c903003415207810f8280e0032250f01003001480740e40300c440100603a0516180302070340030190781082c0103400c2d155030a031181180c00b110b0445208901e142051040d15003050200c01c108000c84c010002e054483e41c024108105080c14188140b10114a2414510b041d820212030f1900480015829581d50f545540c0c0111 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 366234550 1250 366233300 366233359
    0x70b07061d0c030d0509010905090f0727120f060e010c030b150405010e0a080102030c0406090602010c122007060902010201144b040210030204050d110301020405 71
    0x5921075800741c141c180010b030440414001405001401401401500c240c0e20100b0007e06000b6000c03400615642c03608400c612500d41c2ca440c0b5901440c00f2040200006203070004100c0d0414250881040780c0d1350054a0025100d1560001c1c00c208860f0030f14801e00340d98210024280d6042021014000d01c4c103410030103614110351020700540c0220405c00900c907603e1505421880d10600080010f50b1040400d1100c00f18054110034190361680c80290aa910841d03801064220000d020000c10b980400194000c09075440204240707c44034100074101850746880b81001c54a030401002c182c9204a8a00070000700b20301d4480d80c0e040d2a240c40c2e0003402c00e80000340c1c0036529002c00c0d40402c17079041e5043d62040da00a00e104101c0c002e094884491989c031085050f162202070f0508880302c80205001c240b50340c8031600649418606481007000c0c50340309010803400c06006210030012a01c2d00703150031109990040d41c01c840c1400700b00119009010b103030b1100354040b80c032140d0307403d00d0b0a00381382c141c540d03d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 366235800 1250 366234550 366234581
    0x7030e0c0103060b0f1b062a0405030a03080702030c01020c1c050310060c1e0615061103090906040b04021903060527040609060e071d090c12070b0706 66
    0x145200c0c0154125103091103460300c0201d041000490b40d402d40001004a9081403002c841c01c1e101400040e89050700480741d09040890010b8001c05a0010700100649030360a02075541c1303058102004079484101847d0300600380308584010894590003031098801d204000300085440302e00203808142d850304118604510726006e180e0b8420460310403001c40b0712a01e0b2075044042e9a6161540842c0c814115000c1603c0780184285441f0b4040720301038030741c001180500b501081c100002c2041401800d41384d44038000348070150380d980303001440c04401d03100b1314503040b1040e501684c0c2d01004900134281c83c1c286103a01600c0020285580044007001250040b403940e0200071003510303242802000c0101c142607003109800f00088407080800c03802e4150703101d40f0552020400319010b50352801518070010815031690450759040c0080a000b6403207901d0a98190224401800c0c01984a030315403100b40310803401a101041001c00001041000c4401042102001ca42e50200d0707081c4500103004148000da00d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 366237050 1250 366235800 366235813
    0x140a0c090b0703090e09070b070b01030b090a05100c02120a03052203080a05070509041104081002070b07050f0403051005061c0b0a0b040906180210021b0103020a050d0507030e 77
    0x100d00c121019141000c0c1c3c103455102642e41480404100c15000601221540c802e00c04045070f0070141c0d41c05444a14880c030f0188a103541075207000c10000300c000f020781400d540156140008900001058280741054500001e01c650b49031a0403401c3c0180524240748594000542003034450b030507480603200b91220b080402c0703c1003185585200d01c801e04003000d0000f4222102103030581c0e0703a0f9480306400405600b0074a180c0a0507802040a84500d01140044030300045820041e501041c0805071300310013844070451034010f8a1703a50307003001d11010b0101c20800c1004501d0b003040c44500d80848000e10380140454032181c170708030b441001170923080340c49a024040410a4002041c0040200f58880d60700071401141c81d0b480c0400540140f50b840d428039882516400030034007040c2c0601c0340300036410b4203410000500d2a14014840141118030000d0115800941c480030f89049078a404041201c003483d02590b00c035080c400464003401160303207441c0f04a1030182406115601a480100c3e14400c500c16943d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 366238300 1250 366237050 366237059
    0xa020f030f011505120411010318151d0304180902030f061005040614010f09120302030405041503020603010311011808150705041a0c190c0801111806090301140a0c09 73
    0x101c43c003c1039407801080c40101c02140009440407c10404036006240000c0c0c690240f40000013025a060300988090a40380d000702d0107150a40980107144103960102c19018044940003541c9200e41d1240b627000c01c624000440c0e100301d441e00b00201d8603400034112a401a04000c0450302c8000c00d403a620f0411240074000141d506050007054120b1361440405000c10b034061006544040100b441070b010010780c900d0100700b0801e011451107076580264001d60700e8505007002c4c0412201c801501300d42800c0010310400c0182c2d140c00460741929170004182003020060001601e5411052909141007a4042400300d8481c10004502d02c0b42a04015a803905171a881002e5400744154020501c840ba4440391040018009600801042104001700c42c003070094004050450302002204941214200c2c004210707a540074010064615010526640b91084040c907007140c43c050746401030300614002c10b00c04030fa650294081e40740c0100c1c031150410b884c079003a20350303000410705012101d0118001820105 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 366239550 1250 366238300 366238307
    0x2030118050318010309080421080d020405010e0f1c210e0f04090203210706050708060112060503060f0901150b090a06020a0807080f0c010c05070606091a090a020f030f0115 76
    0x35486c5800401e1146040d042a50030000611042017020305003070079100030000070301c3c00b0004080d00a80c120005031242d062030001820ba03030502c1c080522400c6c850354200c54070342e01c0c0942910356044180000005648034580010440c03840c0d0308002c0615811101d0003001e03900b0810010640c001180c020317092080800c10071045800402000e5015481014000640304c08000c14009400c041a610b40c10604030b503449006443c01214401e000510340014054a07582098031b0015901c0000310510413030382024046955004002c2c501c0386c8102c031460205480c2c6800303611035000e015a0100f2140c14941f19a00303100194010041c00c1c1c0540e10711080044c0c03561000c12a2014039901402047c43c10945498646503500480c841c0543d61004000074001460700b407007001120170158582d01d1f00c0344007509244044030140e9100e880d40606140343d0110b00000c0101031880c0080840da4642c6940301c03e05035034000c1c02148000301440310000203000160ba08024131504035030718402d2114080ca000d19085 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 366240800 1250 366239550 366239561
    0x1e160305011e0513080c0f03031e061f0e0109090207060b01081006091a0c07121b21050c0a0e0604050606121329090d020606030a020d020301180503180103 68
    0xa003404c001c0b040307154001825440185520a400b00844004454420540d42507a00698404008940003840140710483c069043c42d8002e404544a85100b078819402545200c1030a030340340100803140c3c40f5883e40e40c1c0200da00401420511004541b924814902200240072101e13030307903003c12000d9001405441080020a050b00c8142d82e0b80c00c549490980c4044c6140c007807001c19400504148881540c910081040340018040b0303045d41111001c45041c084070000303030003011100b007a0100209000350f49150070807504602c0f08a4504c400d40c1d046050140c01c281241d80300300d5215100404c000381c242d10342401d003401000100c400300095100e240421803d88a41001903840f0688000013601d07540700e180404054a0040951100a124281c20261900e0264085481c0741030070340300740300f2100c00400a805088246000400c414100200041d5460300142d0000b44644e0749417584800b1500c0130340003c0361820802e04407208400b8640b911503106e42040b10b0321400c9840d090000328207580300f400745 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 366242050 1250 366240800 366240811
    0x50910060803130b07060f05042103050105090708180111070606050a0f12060f110a0e09070e13020412060e0d0201140604020a050c06070f0e0f031e160305011e05 71
    0x82c40c1041c83d103113144000d900904400c2d14200d0360b0700d1401304042100e01038107118620034440b039488100c83c10303144059500700c00c600c081003510703100060205485014900390821580e080040359503a07420605c48248816004c218515400e000001488603206000f42802070700c11001803000740d4540d01403101c1c01a40c1e22802120241c900c40070844650560175050b00d450040f5008101e080c1c9054a441c251203001010202c08480040e000c9141c65000c02c0c80c180006045a40070080e0414250003030014960741ca180d4860000348070f1b140b40c601075950485005000c0c40c0f0100c030440c207450610350024281e811002d5140c0c0110b1402e0761200d4810700c25803001110341e121108481e2035040a01000f50400c0d41d1400521204201031600301030308102d41c9106400340d0791180761050000c81d0040019000c1801280500301c58032050080d0399000c5450203081c44003c458244008510180524061200002c041170349411072010003446010341248081e0001186410200041c1140071421640d00311107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 366243300 1250 366242050 366242077
    0x7020301141b0f04090e150405060f0619050402090d051c0f020f060a090f02191a040e04080304020f0a030c090612030e0907090f090b040e030702010504120312050910060803 76
    0x9010648060f803105005100c00e03030861f000c00095014015440805940540f00b0f68004002c00130106500da500c142d2041c02562504011240e080401808081c14001c083c072a540209103541c4a445108510716100e801c1411603962513405a14130f1007442d103011250b40001c0c5c1b01d18a0864082c0002102da4004030b4000040030240d840d003510100818100d00216180503000303000b07001580da4150b0300e00c00c011001e000d40222928010350304004060025400079115002d0004104000d46412410b9105800c440903039034a0ba600c0c030002c1e031a035904540a50340700282d10004070611054030f00b05000d503034404604010340d0b03403544640580e00704c1100000f400038515009608050401c1452180c20810500700a14030b584c440c0c500d440b0444d8240c0142c19a540e440c14103581070700e0140103c107890486080a03500e030545640000300a071280b409420300c4505903482a804040c4691070b800300c1081b8103035080245091a891043d142c0075400125400341d420140081219440031088440301071101d131 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 366244550 1250 366243300 366243307
    0x60102061e07050f03071101060e060609010305090c0414070e040605060d2f0c0c0d020f090424090218070f0e0303040f03120f03020315010e0607020301141b0f 70
    0x40340e40036030700300401c2502080740c1401441c0d4410089009103000e1101c41d15180000d01c10840c545007110480d61080c104140e100042c00b2458607280102c4250034420728000c00e069861100040c5800540c00c1203d80040c41d0001c501d0070701d0005042c160207515281d680b00e1a01001c5420001901c1c014084c05910550811603400d8200703481d40300b43d40e410341d8031240703001c400c1e00340788100e500c50b03405c2d112864080000900500d08030340500004039445000c5840700c450480540118802c3d0701112e50180c024041031001c07400b4040f241e04404540c1c0901e00311480f03181c076000030003c0649070581c4100c0c025960304411a08554864000e64030510300303907072052100e0250510441d00141600b0880e505030200308004a084008020800041e501400000003445442e680042500c3d03910b10200040510600511146070201004914100b5003481e114106503d0f003030004100780305a08009500d5864402e1050b5001c0d469040d81d48203104161145c04d80b56081c0074002d80f207100308216051440000c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 366245800 1250 366244550 366244591
    0x61503060f0402030604090f0803090d08250908030a090e0609070c060b0109050a0b04140603070c0201030f0b0405100f0902390604051f11072d0606030b06010206 71
    0x81e4040e5510171002003005c02c2c29403298a6841201e0032202007650350070340010030082c040358100720562008025140c0301445150524400d4030607000b82d4584010045480c0410b45680d20400c00352001e8400103055a41e40c032110400500044200d1003002c00610b8140d0028130304c0d2400442c001c0c840c050311b4640c20089003095482100030000075070090f0500003c00c2010410340c907209a1000a41300d848002c6580d641072616103d41301a5904031144280020820041d180e603000803401400c070740c2804d002c1100b610001000c0045c1100a10050700649403a04100c4130050740f111710380c01c5500d40e22259601c5a200c0603144140d01c00c005900050a01c50080c2184081140030450010311002200c1c180780b039159607000b400c20200b540c003a14540d010746031840c000c12103c1e100050106c9030b5001081080c5e00804440e07241c0c041c2103005848083e000c0c207502084048010301490000c0c20f0b2842400c04071451408d20002d003007500058502036000b00010b42194000140f29020f0b9900500214128404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 366247050 1250 366245800 366245809
    0x20a0501110f07141f0218041e02030c16050c01030608031e030a06080d020610060f17070306030501020c1b040204050306270703060606022416020a0c030b061503060f 73
    0x1c1c1ca85000a84920071001140007031140c1034555640741c1c03000140c7d07659580d00c4400c1c030156034500c03c584034900e8424044402580181204001e02813040051382f21340d80c075034014006001d0003440142224684040c001084404144680010000d880400010b929161240d90780e0050122031001500e032504c1c400c811102020203180c3c44038000c580410070544440045060420758100c20700560310241c1408007520742059132602030410f41c9040300b00061003040040c200100080b229500c4601d2170082006d0b24032a1708010059900b000082d95191900460700743e42d510030402c42054000c4441751403070b19140c2130003280c048400c01030052a00e5180c00d800d4050414000080801c1c8000c42c20144c115080305000e403000660080000003082c07840c0044c045d080030303080050f41e81441c02c25034400300d4602007000000d40246200800c40d014010414082c0d19000388454058001c0301c0d140030000800c00c5034030380b9900c00c250030344861500c100c40044a600c94041135503425401000c030f90302c10419007403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 366248300 1250 366247050 366247073
    0x5010b1611030709060e1501020607051810080907050d020609040209011b0c0e090606030a03030b1507060b1f080105010c080702060d06030201140702010801181b020a0501110f07 78
    0xa02035110140701e0620020385441c0031030344181090307600c42001704110302412183c5503101c0940310007180603107440c4000079101c000041c04902400350105030352210015a440008448002420320400600c52010103045400100c88920b031034842d814000c03440d4100081c00e42c4480c0d50181000d42440355500030080a504194066410002c0c111341e88100044e8002814030164064400d841d0401e05080280c642c40600030103900700c6d0341c800c105000381a140041e4204200783c043c503002801000002c00507a50088044082da1155808070f0701c00180809a07011202c070101c200d47c030141905000702044200c545001d003060124900b500100129401340940d41400c0c0c0c0b00d41d2a01c1c1c94a6141c1d80042d10a400484613081040e80d1042c0030300031544c0000d0014191482c2e602c0d00c0f400c00b03040d079000a202d42c40c140181b040c94003240742c8810001c070058110443e80b00040890815040245000030349d80d8500c0c80c0d00340c0f51582410003c015400c00d403003c0b06c601c4452071030300f01c2c5040d00d180c440550285 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 366249550 1250 366248300 366248303
    0x109090305032706040f030210090f02130b03100203060f010809060a1a0d0f200d061d010501120b06060301030809010e0102070503030c0102070c0816120c081c1205010b16 75
    0x44803d400000c0b01d507000e128075480760b03103c0c40300c5021910082c00e0003880d00d4000d250b62030806c1e00c1e00555001044010390149061603040700d981282407010101ca2018152034040560944141103503e09078104940285109003402c4e20611420428400112158003003581d840c1d02542104020030301208045e0428141d2016120902da81840e58030041000700340c00b924150b400e0f80c50800765904100748246009148010000031075824042940080d0141c6998100105003d035924810941d540500e02440744000c07100008110942e560380e02c14050b1040f00350f0458007007410800003141440c240094905032508206441e04090040d00151409102107400c18154407070b0b40000070312903600f0030060084114071000941c550031039203403600c02d00950380c10230100c98029140520700300d01d003e1100001c1b030320000c12041c4018480d007400008010300f42c020304c80e60f003c0e41c13000e00850070055a042c1d68085107580d42c41051041c40800310110348003030207003010035107040001e007a09000c803011541e11117 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 366250800 1250 366249550 366249601
    0x110112090215040303080f15060a12060f081002180405131407140109080a03030b01050c0604050a030f1d060a020106081006092004060813020303030f0f010909030503 73
    0x580c40c0c00294285607111071075080d5110000d014010160300c14000c40d00103441c580122030b01c1c1060000d201040340141c0c1c0c413601444000c16002c0b45a403085255903000c01c3c254408114854440110203110041d131b00800050f0710030401d039140b2005803442280e85040f80982d401c8042d049460810000d080701500c03030140a1074100318030b008201008946c0891540714001007031203d15001850419501c45030002c1d040c0a05c0400070030002c54041122220f1903814a0000b4180d01c0b40d5006031030300c1c05010198111442a6805c1100b04100003510071183c0b402a201c1040d542c44c418030480300349010284410495a0700881040d040c1414405024544801c1c0004500315460b1682c451030540040f42d08200162a0b040801070805c0c0e42c411911302000004006214101031a1010000c1c440c81c4162800c214220000a141c42c508000540318a0750040a80340e0700d091001c000000c2d0081951b4a80303603001c91a00002b50f5a041d8410f684240d649911282e017540d50f103a0a0840380d21b4030b0052600301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 366252050 1250 366250800 366250811
    0x100b0910050c01051905010b090604180204080a060e0615063901090c0501080c030114010212040b0a1101181b05090708040c081b0607060b0306150319110112 69
    0x20103404e0146600c81d019030401001004d003650403100c2510f0042e40604840d00f01000280c03856101c03281100c01b0b0381c0c5c1c0005860b00b058510320798840284110382c016409406240c581c00304016668110030032814140007100c816444d42c244250702403034066041070b4000c00801100102440a852019000d0700f04442c0944d040da13248141a0172a44000015010780d54803d80801005503070000907000d000d0030b00c1d0050f030328684074410840314401030080004809800fa0001e07482c0e032003004402c040005560f0348684550b900c80b815001c54000002c00720100701100011108090305102d005061902e03a00d1040301414142c03074035440803201d1103015042501120300403440746c0380c88080c2030040744281c3d103965240c42c1900742940f402d01a030300000354940000045070754010b000c1140d00c40303624040340c0d59686c900d19850310754020400f00c850260035008010803c040c03000c24800805131900250280c90558418540c00b80304401c0000c1d0003407600c1c00c0c007050805a54407440103030406000e40c1301c3c0002c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 366253300 1250 366252050 366252067
    0x210606121e1b090e0906130c0902040b0901030b0117160c050a05030c0f0106030c0b0d0e01050106110d030e060a02030c120a09020406080c0a052206120b100b091005 72
    0x90b500400b0451204510016185103040c0c0d015104a0007010740d00840c41c0c03142044245280c0b2903602801d00c502c1905d0000d680700c140303c0c0c1c030041c2c840144603400007159215a500c54001d01070700070348050b40c0402c2c40c00c1503003201540103440c0002084510f420354079096940c0c4642080c2c1d007010b950504104034080d028000021030410080a1082c050390003161180c070441e184610301540c0039180c408036410003204000244044400c401550a50500305840310399902c81640101448030105000d9803c0c1000080c0480c0c2000200c404954003105803a00c03d401d6a900750140d450101040116134400750014141020b00d602541e004031141a0301d82c5050040c602c141d4060781d0a80d82052210394a0300d02008625003442000000d20b1010090060602c0340c10000301c03400030b60b200e414083d182204011241c2e05841c10707115444149900c0400070161a104160010364085d0000c9a90440190100c1c2416944000da0022070304d00202c1c0602d010040320600007041c418084070303800d01c807043c02000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 366254550 1250 366253300 366253361
    0x3090301060f320f0112020711150c070504020c030405100201060608100815190914070902040503030301031101020a06110c1005060607020d0507030b040321060612 72
    0xd0042504580405060140002c2d481c079400000c1c02c0403400075640d1030801096449504403064007142c00c140c0401013803006840140041c1461503d4900c006a6042044403602e802c10a40c50b0548450818120034980701c0745c81e120b0303041810305c6580052800c0280c0d00d42034004041a1f003440d01940d080c1542c4502080c680c0c1d84410504e000740c0d4503001d062001a03480b0403a1540031140d010341c1030045241100e901c0c2c4412040900c60140302c20000020410309000841c051043c0249008024603c154240340c100d040c0003003804411030260000010f1016001e000351026210003c003d0351940c0d01c0c564030380c00c2d644e80c4140810f0542c020803041030081000751013450031048030700c40c585943c0c3c8450f00126090100684500384c0162816007231201701d482d62416100b4244d8103032a22030403000507041c86840c20b07c00394801807080ca640010402056800030b51104d0030209082084509103a1000030825603200c7d0107032400090701c07406000c40c1424580c00921a0356502441d10444903084000c05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 366255800 1250 366254550 366254561
    0x5010507080f2208070c17060603030f0301091a150406030e0c09061011010216030e010f080106030e0c2e0309050a120320250f020603091905060604061508010b0c03090301 75
    0x444c1111f80103800a40112402c1c88000e40c090320480145180c00324105e000e2000b4003044c02010407169403003010307030b0907142070a00a0000071001808015a01e0b40503201103a181d22074000c030b100182c01c00c03002e0b40714403200103800e0090b020000c1c00c1d12440c0d61040103118040103c0c403c001c0400802c9101200b0061082c40104115070480d00041001101801c02408a6503495a103e040001359004403600d1a4040341413419240349180200e0341c044803441803031400901514003944507c01038558070101031400320000d24500301d0341100e00700140041c4e040e021528281c801030710942104c00e50400040000b245401c2e10f07200ca01b00010307000440aa900001c0c040a40002d0044100082d40c1403400002c240131540b8035640300251104201e41d94804244e0554a04001d0141c413021002c518000380911806400c0c19410318034241a03050350a0007607540c10281c2c0c030640210703d07160020418003c400b068001800d110b481e199030310791030b100d4030b40250741c010344005850340424080303d4022f81c5e0a0084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 366257050 1250 366255800 366255809
    0x90d0b04060b09070804030f03020c030f1306391e0506070801151209020a030b040c1a04050f010f09050d05060406060504020c19050c0405010305010507080f2208070c 73
    0x10b9882c0b80b2000380301100002900c103c05000e10b2504001c000fa6001c1070300741002495150258584030300241c0d1078518000c0c850343d0f010024020071010701c48280b8245c071604844050742c9061650000c403080c0c001c541444595420b01c01e60f80010b40200083d44030f015918188a08000b03560306101242c21241002c40640490b02c9801c643e082c010700d41c1d8000b034902c2c05050b54009007501c0080320300d40589201c0c8140e046109558035503062806540e102c140c020029608401d10594034034041c68900c5419000f4064240032160b20541e60001004180a8400360740000d410b0000048071840196039510042ea230381030400c5411000414242c5410510840b403500c52401000141005e2a149e0183da900ea00818010b5105000301c298050000072000d50204404410714002d03200340c2403143c00e203428540d0a0ba0014144400001005030543c410b9100c0d00c82685c401209444920960200802c1680d003440040c42c02c628407040005031302510681c40f0302c1141128a003080e03c1d1b60719081d040440e0700 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 366258300 1250 366257050 366257063
    0x60b010e04290a0f12150501150314100512070807090c0314221e030e010e010905060405060f070b040308040b0c07020a031e170903100b030c06090d0b04 67
    0x342d205506111001c1ca00008400c8524490320303410321054a10100b914030803803580f05001905c20040c4100b116540482c0c0c500b0181c14000766840e0100c0803010030020102c04c0009103030218101d0346101c95441e07139000f01e01d00201058803520b00340400ca07a003071007800041e900b801400d0000a82410030880e040062107a0700c40400c0860344420050100c0b44804a1241410760241c1006102c03007a1328044041026040031500310083c003801d1107195001700200d05598141000c071244141034200c1c20301d8000c103109aa50312203440e140401180c40fa0000d101d041e8000c1e41c01d001c02e01c10351810402a0a50343d42c404500f5042031201e44451100700c000b0350f41a800704001034240000d202112203031541c41403812046500e41110344c1d0114160943c40e2001815810f0708001000c00d43e00c20305050b241c0190061180c10100000d40000407281c2c0c0b00040182c0b01c0d115051706030809210030702030340806200c000c1c0a0304409500d6010f00015030b2101c05c00581c0185c0b458a90b070001151030041c035015074050722 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 366259550 1250 366258300 366258341
    0x4061409010c1407050606100c1b030b071803120c0b18010e0a050a120e031f06060e03190203120304060506030618061f0b21180307060b010e04 63
    0x140601109030300103022078202c808004c0880810b0000a0300c50300f14009403a16030300491100e800316090044281c0003031a8030340c0d20100c0e9805004a074059001d82e40506080f8000307441d1440292804d6044031103da0031042031708020804290780140c21000304030700d82000b11850341c25a680c001200400c40d000c59003403510041c0c01c50b05090911800035008136410042c40034101e1a1112030f40c031600524024151441c0c00101c0100902c104901001c00c0c00180484505818000140d5044601c4d64160300e441d514081001031703040c3c4100c00702455113001030040c041008210103118a81c81e990759050303816100e2504d0320307500ca007110740c0250300c1a8012440040d44d41030050406060031070240509170f041c0d0310310441191100020902c40d400050505091175000a00035990490320b200f030340042c205010200e031558105051042a804000000030f003001c03c0d9541100c0507040d00988003205916600c1445a43c0000d641584040c40c841c605041116007030114500140586803500e51203006810300c071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 366260800 1250 366259550 366259571
    0x8030c060907050a0b040909020301020f16061b0e04020d02090a0b04150c0b0f04020d0b181204063c0c051915020d0e0a05060105100203040303020d080406140901 71
    0x60210b07401614007107400c1440d182c030306440090700d80a10700030b41c02074950300c26010003199425411a050a03020341c404075194900b0315500b40e400c04241c00280c1c0c40c14241441492008110f42c070f02004007045840b0904000d070705000713000c000d41010303a2071404903908000080840d668a00c0c480024130880850b181c3e01d034104031842c0e959903481c0c0c1000e400c1c0300c1c840c2207110005a03044d112542c000c1809030460002c0d540d0b4000103491030074684005c1c00c4241311200340300d106644148076010680f0041c0407260f1080f001444c2c0a940e01c954031500c00003660707a040c0c55580014152020524585143c1d005003415010f40c440d030883e0900340001c0005c02d0a4610907030810209000129000f0344005404800b0f103070680f079440d01080300f20000d184540e400642070040050300d41c031441d00245450700b00c0d15822007500d4035640d980e07030030302820f445141c188407181c440354400002c80c2c0c00c0d03039450743c090000b02e4a254410360305101c2c003802c11900c841d2101000340c2e03680d0042c00c8481c850b203c130800205052440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 366262050 1250 366260800 366260803
    0xc0e011e0602030f0406141309020310050108060f06072306220f08090103150b04030b090303070c020927011406030706090e060406050a030609050d171f08030c0609 72
    0x80d07072101040d50400d02440c02c0e0001e03001300351405c4030035908000202c29030103860280288288c6510701c05004580c0c3c804681060180e000e10305c80e81c3c90b01c40140f9020344890055407280f8040f505544d004600742c91786521030601d80c002e0a2a103206100d00c080c0c02100d28101c02d8009001c44046a01da44990200700d040c01c40a012162102c2410503a10300000d00c81e02c40341f80d002900c19010f400190700080f2440301e40d1007a0311501207440600790060281740c8614030b01095500030b01c02541d070805290085180da030f4021040300e00400c04e5886404881030036034244020078a000b400280702e2051600c0303443c06112001505101c419007800005002440c01d03203002c0c0d80d02d0014207051b002e0351000d070050010390380002408003552042c64141e13009036900300008024003e80e402c210703044071004400004004198000400342442113050b249403c107882c1c404c8071004003035040d08030b800928802040e00504014440b05040781c080014807400f07601c445d0041e18650009410038501d0340300b0010490310080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 366263300 1250 366262050 366262109
    0x4080310050d030503071112071a01060203091c24020d0c09260a1b0815040b13020f0303032a040f150c020307030b011d0705030703090c0e01 62
    0x4125802c1c88100180e490041007400014042c0c000d01410215140400404100c0d00d43c07805102035031030390356800302c0c40d00c1c210601e0040c03010b062203502200013055087c004425140500300c041c10074500b0195440388681d241809001c00d031000c1e030840a031000d50442c0c17a0880e0081200e85000903945d0440000c481044070644030882c41007104074402802940c41122000550801648601414503082d5040606000706400020901e00340135040c0301080600381503903c1164240b00544001000a10941c048100120383c01403150008000003080100200c55650540d4000340007071908018110119240d07500c00d0328151006481c50b030310340420304941003042c802e0056078003901703050500d003421522041140d4080e0402c070407411344004000c648100d5010300d2203600101291403180c0d403402c00d07580c55102801080c103000b0240150507030b400310840b0280c2c000d40d02a13503820301d580e9400401710001c162024048504030304054002641d000e81e050014003904415a00301c01d28030700410280c41192 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 366264550 1250 366263300 366263309
    0x90d030507020f03010902130b0a0b070b0708070e0a03020d08120f061302210405030706050f060111011503020609010309060204171c0905090c07120e0a230d140604080310 75
    0x207061491b03c0005841d601c45c400030000c6c0340200464045442c10025903441e00f00c0d00112004c880102e44c14060121520206008500e5522800200d4a0300c01007100c000380758011454010004440400040c10400b003d4105103001e80c200780d0400507005072000c014602911502c0c02c200428040c80071607d0151a0802c080301c0c10300d01145010100a003c10580000901e1a6510402d0b50000f405024060046400781a8800070402031403420722a103100070300084d26094002810010350340fa00b050705201d88081d80404d80c5245509038a075900704100c603800014080c3c10580c0b0b5034500030008442d400984084e01070741c00120218060410200d01c0c005040c02146040f6900c1085200699042003c10060b40d0054944d105240d03503c006001b600d1241101c000c20107503044040d0b81da00781c1d20206401013494121550b07548196203140c80802128101c1c285d00111134284504103071807600e80c1c0380e0084544200318441441703104040300c9080003c00c840a03100600004200b001c0000c000032070340041c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 366265800 1250 366264550 366264553
    0x60f020102090a03021e190f05060913050603031b1014040f0b090a08120906101404050a0f02070804090501091b110a02030106060c150c020a02060f090d030507020f03 73
    0x500d42e1000210120700c58800a4050f46600802d8200c00350b040d480c07a1003950019205002d841c000c0342c1c2040c080d1485118643c3d45000e401c078041010f2401c1d000300c51000c00002d000440403981840c05200822010740119030504c03040102c2410504c80c600c0700c41810740148081c00512644402060540d4807140c0741c050418203010401c070005001c11000c459040c0c00001c2c0401655a102c00d0a00e03065840354050240c0c540450010500013607408a64410040801650115180d00721500903100382400341c40d0030740c02c100180281e1414036034070042e80403624100208410702c10041c108101d0344142c100381c03060540040e0510206545005441c01440c82c402c00308000d401e0351030f80d0501466070300507500400400002ca0b0280b84410800154102d4000f0000c008803940c0c0c030405000e02501c042c0c01c41d5803001a01c402e00c407000c0c4070f00c11003034106016000760004c0010f41d801c002c030350341c8410301034114078509100c44c2d42d883d121901680c1c0310301e1080d264103540f0300683c0100415881d4101655119 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 366267050 1250 366265800 366265807
    0xb04050a1203180f21050606040b180a02131a04051512070518030726070801050a0606030e0604050703020105090604050303030a09031716050a05040506030a06060f020102 75
    0x54940962500854440c40e100110074903003460111110101851680c94240200b08040b401c3e0140d28010340072542034025900c14500c2100840c0c540a07484980a400d070b0f000b080c0040c071282400c0c0c0180b48012802000644c5809000071010149901070718030340f50b150342c00f00710a40703149404030f0341c50080d2080c00d8010401c01060700c2548410b00c200e0190034001d121680030640d81c0344c0c3c0f1206407a0411000400d04007146440800200316801c80c002155810440c40302c240b840e400c000c07a80744191241d92000601e625600c6a00c28110b0350754045c11041c81c8a00440003d03000c000784580c034000c002d4108003040680c600800202038480c2606002255000318041c040090b42c0090720000300c9034203090442d140c49040380002c2060203254031079500741c000082040b1100d200c80e8002c1400e644a0703140c4100055060b0030609801c2ca00715078100151507160041c1214074080c0000c5c20308940a403400741d1515890701c02044003500190381f03d101b4a9101c600a110954000101088191851008508 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 366268300 1250 366267050 366267059
    0xf090310020c0d05190e0d02060c0d0917031b030c060403030e060f010b19140c0601030b18030a08040507090c0203090310050721270605090106061403070306030b010605130b04 77
    0x4400034245c110300500c2401e56a848081c5c40d0410380c40c0403242c009100d0390300d0764000040380362501b440b03181490004030134510200301301000d0044400b407450180020b50901c6524a95200c5440a864245038184801d1010b8070b9941001c100d1184034600c0f954002c10145590b2440500d011405414514a415100018840c1012030b0003951142c0954102602c4020030b14401515410f82e0170031065841c4074001041041c043e000540141207a110300e051004a03600c007140306814100760800c030b0940e0303003040001c8180c5a1003001419000390062041c0c1c0c1005582ea50f0010840b10000d10b200c0c09038001044081140c41c042c445000d01a14030f48080c001072600200040005012144850240d41501d69000010036542d01030000540d401c4440815141c2445a007502c000000804460301820100003c466800600403041210501d48501d50014803180340c0c14240e400041501c0308155507508004041014a1100d40c02800319866440d81c1d8944681c4040384101c503034100400c1035004120422 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 366269550 1250 366268300 366268327
    0x903011d0a0b061813140d0e030f030a0503160504180606120c0905120102040806010603021b0a020a030803061306030b060a050f21030c010618050108210f090310020c0d05 75
    0x642c001034046125102e540e0b1407424003410031040c04851b14900c551300040c001300d6040741c0d58800610f400c9084072800034606001e10360324460345403428000345082c404070781000742d000c24503200700032941011810146c440c000780410224078002180840e48809081100d540c1190801106004501c2e040c44940c001003030250100c0710301d00c2001d00802122600c0f418a81003035068401511495007039a0700c5580d1400004d010b50002401107160780303a410003101207142d000849444040d40908804c1040307107103032603410045d0401004950410310309503a0310f8039159180301e4078019500c100c04c0d1075142d05150003401080503e80c0c01c414018042728403401c50981e41c90941c28001104014840c8200b20401421803c40c00b40c224200015802e10f0f0703010880c0c08507a04c01c01d901c00303c0c2001c00c01450781d13500d0b0000d0b07550540905401101000c0c00a03280a015840010709081d00320280a910717040210012070710b050765600b07500c05550360100304103110f1841445245c0ca802c00b145001c6003040c05c07481151 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 366270800 1250 366269550 366269599
    0x207020112141612020403060506010f080919080706240b161112070e010306050a05010509150316180b06040815090109020d060c0e0103061203050903011d0a0b06 71
    0x140304490f681420250342c6108003281403203401101d0080d5211603607403402c0800341005031401b5001c140014002070f0345038072400c186446001400000d100d909400380d954010608460401d4070081000c1141c90046030840c0101400b65011040076120004403a80000110310030740c0090222900c02c00c405152410b910041c960020f410080c0c0c50115017030000060083c40c101186d00c4114021403a0008202c4003000704d02d4101c0380100e00070b01031684d504001c042140c6003409420707444a0700c6d401041d02ca601d501d03118442501d0140844102c2449064081959060b1b1340c060712008041004443d0642c01c14011001d40380f40584816082c81e0a1810650312160601070615129030031000050030940c0940040ca5910780240031189602c280e800c2990203040c1c07a00c2c15401084031b000d10300406511a00c50350f03044425030b050400b0009131700d0b68129440c1d40312681c00d40c1e040d0348a100441c94203040781d0004007110204401070030030183d030b49040b005104c03000300094411b107468201c0c42c00e00c44241690 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 366272050 1250 366270800 366270811
    0xa0b0d051605041e030f050f010c08040b01170a08030a061403070303020304031502040b070f1208060109061202220f09050103020609040509190503090a0806130b0910020d020702011214 81
    0x214141054210011000010f181c4c005820786d40303078031190400d201c804180d0f034110382d402c04000d0296200c00102510720000a9400030200c21241d401001600382045544c1e1000c1081803d540064165032a03100d0740c5d420541d025400e45544420401ca240b0400d03c0103141264203501801d482d9203141c82c041c0d2a40a54031028100b40000c0c522410b6421540d411a405000c40021007925100c0f641031021040701c8002007140c000c0d0103010351179001c502501c15640305503130580d00c00e404a0706004040340d11440000054034070701c0d020b00a1041968502c0e04c040d000707120380e80e80c8c0050585040404100e9000c103a0004034003a1801b001440980c844c841180c869140c182d40118603510f582110718a800c82e154002e003280c0114010100130040084000c00016004039010325020343c45a0f01030b42c40c1c2c0707401d5071030b900b408031401442400a2072801c81c0c2680000c0040584940300491900c0d01c050303070f100c402c1005182d9400581031045603040070903000740d800d030303100100940c2180c0740c07240080e034401502 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 366273300 1250 366272050 366272069
    0x100509030405040b010212070302010c030608030903071401020f1b0a2405130b0a08010305060105060a020307140c0904050d02070e040f021e04060807180b0108011a090a0b0d05160504 80
    0x52132907860b4001c0115104020345124134503518079181c10000d009000103011400002c3c1054800540d0040002c06c0e101e0100c80203019150f924503100b00401c4040c040c1040d1410b41c026035011080300300c018402c00990818140e07503031421030b4030003042200f10415a0843c0307110701801c3d8107004469810744081100359026081c0240d0716144c00d41c0c1c003c80740503584d00c1001003800000d840d81805a00c442564100c030321501c103c44850740c0700c0c010803856000d001400c04c0182c2c024000500820f40b0745010340068268401900d42e003102040c0410034051048905441c0c2e84d02918002008542c108030078001421084c0440091b414155207001001403140c001031700c51b00303501a001c001c1040341c0b00780010a0340c005004000690740e6085098070b0f80750307512403003030038181e011a80c019090b80340c00344000580050f0348010480c0c2c205a8628912104d40801140100f4144040c0b0344a071161100800500b82d80005651620a00030340c001c2038800041ca0100502910310010380000d80060546050320207084 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 366274550 1250 366273300 366273311
    0x4170a03090b072001051b03150901060f0e010206010510030504030306080706200a02010509120309041107120e0306010b0c010e010c031e090510270507050310050903040504 76
    0x41048010305594580641045260010703c025140c02810800d0b02c10640292041038400c2c240469080394011600403680000041045070060b04500041d0b40c012280c2c070300c0841c00d505250114100d014241c01c0080410113464100c028150414003511601e9004d10003000c140d8100008038880b03800080c00901890f44132408141014041d8100710060050f4034229015103651b002c000301408a0300ca1286644d41844410b00820701020803814031084c0c0685a00d49001503c80070710482e40c080f403844401ca07000034402980030790313100d024116254003044203885e1555864141448810100042403060020506035400c06031400b190080c116031080b515145c58040403c035840c003516850502055652034080303481042c580503808074070300c0d9a00034204141807000f40340c0c01080f181c1010002d8595400703244448081201e54200d00031041207411040b162070141000960190030902040301c098014180522481c10200a0791b0840c0404c96030900032420414030b030395280c1c4a28000e1034000c80c2c0b140c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 366275800 1250 366274550 366274567
    0x1809020102240105120105010b04061b05070909110108190f0b0a0e0a0b061303080a09030f0f030f02150402100504031712010518070309020103060f080102030a0507080417 75
    0xd110707000300300415006030300310b40038078a9229154501c00d01509100da00ea52107660007900c014170601d8107855440300c6981c50503041c01c04c00d42c4e24181d6405460780030000034a800c070000c2c100b0700100c8000e2245903001b2070078040502e03281d0a045210250203042201c904204101e00888050304000400c1041c40014111100c2c080100a4044c0d6190181c00580000e00040e0102c89134041c01d2013445038001c1040b01c642940100545442042040c00f08070903503410600c0440d00701c03402020302d81c02c10b0405889050382d994841d44041c903000002c1c0c460306900340e020000d050b00030203070040511952019046a048071403400202a83c00341c030282c020380715224a5100307203000c0c030b04640165401c04540c1d5801e11486240041036440b8040100c816070203100001142d04210b030765030301c004034040c40c4903c2607501c06508400602c1c0c0d0300405e904040e02c070b006c00200d405078140a04c01401c240c60025030780745804000301c010740d00c001d8540c804229507281040042018a0710440710030b008a519195903044c031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 366277050 1250 366275800 366275803
    0xf0a0209041802041d03040e07021606020102071b06140906092e0516081e040b0423061c11030a0b120f0d030207050118030c0b101809020102 62
    0x110031105030080d203030940c04490701c0402121100001e200300e60610020303800d00c14913090a1040b59a04249900501c000d01110702c003005026402070083c0b0482e6603e00d0384405680304042160b1000d00546d6000581000384500c01c00c1e034280805e07442d0b0b04100f0061030034400408240749404810741120020807205d080c1d50b950b5040326100c3d2801800580700b880619001001102c4618180754039000e0420b000440700c0c01030065030903076164045150400009034071070700400d0b88070302c100712442c030001401d450039681e0000c06007018296821445440314140140c0304541c0c10f4103950361240030b2110502c0b40c020341c4d903e400c032746910503d406114000c0301e5010030740028040400c0311080001c4044104260200c60f94032100358034100b1125000640b410315011a114081244158195006076400d180400d0182e001028020702c580d000064000c642140ca004000c20100201e0026000345003407030501c400c400656420001c0d25480d203000600e07003000040b2091044080b40d1246d515030758100c003560300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 366278300 1250 366277050 366277057
    0xc09080d080105030f0703020d030c02011803120f08040c051903210f0305070e010f0c0204051e07050f0a12060b1602040e151b0c0715030f020a080f0a02 67
    0x1620000c8452418014201405501003405514001d102da02155081c4c0540002c411048030303006091040b014034907403003c482c150699401039042c0a001038250007c41090007407000158040c80d01c40b02450341d6000d0090100c21858401d40420034148c2c1800080b40031400b04038111001113561030405510301110807640021640060640c2d1400c0d50fa00115415072081d940b8007100315642c102c800c01e1981d4041c6c00311081950840000785030380d21101415405040f4401c1010000d00301803122101a5001400b5540c040b502c00400c80c10360002c0088001100340c0346c0d0303042403850800781d0078000714441020840c0162000b480400c042104015513064142e4070400c060322900c2c564558548064411003004041c0e100101d00403440c1c0b41c00c4603040d541c0402c4003541440d0041e0f004100351a013100300c0c0040d08075003000d090b840100300007608580e041040a00020001c2c096030754801102c0a81c05000c841c68018120b10150040010f075403060350040c01c2c1984402880416007094a4002c0850004e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 366279550 1250 366278300 366278309
    0x181b060c190503090103060b0f03060f0103182303030108101104030c080309030d0315180f0509060f090d050904230903040f051206160c06050c07050d11030405040c09 73
    0x1050720401c0420302c100840241444407003a2814041140d40381c0601400d84251803c00402c90002c0c000b08203145019144410a140d0501d0701140c648824407608444540d0800111002000c2c4101e02540455a0606c1403a03c601000510b0030b42d8500b501568980824525044100e580d42e5142c0000400000c2660051a040041000910b450382c10301075480e8480070a0782c0c0f10380700d210b03140c100313052280c06610348910f404404001c64515201c0c2c1c0c05012007401c03200741040da4903591212451402840741c00d210342880d01c001e2045061800f0b194a04c983c0143c0b1500541c0c01c510f1421300c0361a0450100c0300804000d5030001080b01c446044020070081c0690440d40c1d086052041c0410000c1c00000b40064900e0003506c041c0195560080040c88100034401a140d9004540000d0714003c0440d2107260040c0c50b41814041c01c4032641c1c409045440807900c0f890038284c00310f854010700c0410048581c006070b050a20003400b103202030203644c1d60b00591040900c40e64032041c034003620340c1c400c059202c01807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 366280800 1250 366279550 366279583
    0xc0803030705030906130309060f050d09080403030f020309030c010c2a06030c09080a1712011d090c010e0603060103060f150f051801120b09070206181b060c 69
    0x741881c0d200240300b03500c01d81da1820035108a0740401c40300c2030020351402c511070341a00c0c0c0b12845454007106032409065540084188007081c4000c80090250f802600042d912170f0fa030381581d880c21445d0180c0100340d1161314404650003030004180039100000e0a600980003400d0118501d00c7c68a0030f4100140c840c00220141518000074062901000b0801419245143c4044c86190400d82d000c42d81c00100703200750000c075806002c142000c00c108640c00c0c0c0000c01100d5841d882d04600b400e05a28080e030a90050401980d0820030f144410020701032a500720359000080c003603500c1d85000081425010250b0342d84120400404141e880c0c0c000d03804003000f01480d0043e513103d95031f81c021041141036100112408540c10610602b00d103441042144d244000d40c802c0c04041101d04001124035031515003900c14490355803581ca604540d280c5910500c20344c0c25074001d01c003515001800c115940c000300140c80d45640180f9032145001801008202488403d4402e207898034412089036240280113001007a05 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 366282050 1250 366280800 366280807
    0x50a03020703051b0a090e01090c0b1306050c0604034b0305190504020a0e040b1b030702031e090411041502060f1302010e031f0612030c030c0c0803 65
    0x1090340118909084a002c1c10507104d10301d190b5565500d01a10702140c00ea0b000400300c00502018902c0d40c004109516000d0000030490f426944d120f02100d00e07600300c6581844041440c12002c0b208020794005071825142150402c80c0070861150740e0800a44020148100d401c000541145045026913440020720325550052010910345250035010940e90a90011929a400f54040c0a400750900600c1c01c4c4510101907601014164001c280c080d0040b6070240341c54200181c1649120f0001d4041d80c000d100c0002d4078103101c4803524020281105038803c42c0400d008100020381c0101c15240038100c500d9070030f4480c50101c450404079110700081640c1c0a0320741209500301d40d00c42800741c0103030350001020b500707444004070302a41d40342802c0319280c019000d050700094030403650902003188244103041003180c02c0e0709a0000780c20080351005012805524492803100314255020f440000c0c06880a4401c281207941c4005285000d8540c8c05010f00c4038000e801400c11062600400c010013020081c0c070385 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 366283300 1250 366282050 366282053
    0x2524020702011103030906040212030c03030408030a0f0603080f0714010204080f0d030501030f0f0f0c090b1309110d020607140606040b010f090504110d0504060e0d02070617060409050a 81
    0x25003040c24264005002100d14076480c40c40002103c0c020340c140c00082045540e640d0801403482c0f400c03e05450b45000600021905150400280d4021481249503907200d10b0700c000104210703284455421105410300030f04101003094501103964145030500c13042e0390b42c84d40341071501001c103034050707004095840050000380010010035114400400d80040c0c0f080391058800840c285c032002e02018003502c0301c030f00421002408800081c1ca04a12030903170700f0002c2d0529150081e801c450b40e1f03c10f4952135154020140c00d450882d10010070241c41b00001c11030b030506030725000d01c0b40c000818210b00401c40200703160103568a280940d90444c0e40408a901c0c10954a03940d2a1100d406841c0c00d0300a90800304032104c40e60184c2d20f00000400d51703940340d030300b0345142108020280c845402e90481c040c0302008081031604803400382e180310358000c16001c14244040c00d034180c60070202e404a0710464009060a1060660019048840240d008047d04280d101c40f000540200358580c070040071072044406010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 366284550 1250 366283300 366283373
    0x1050c0f0a020901120b0a0b0f1906080c0f0d05090307170a12060509060f13090f0203070b1303080c030412061b020d35070903050d020325 61
    0x401d01c910960b906450b43e60307240141c5581d01c44d085001042e280410b800a1005500d552050000000040c1007100301071502c40450313450031850fa41c00045825069091108a420803451030300138004203112464851004e009650b140510b03c07042d17096646800105070803120400a440d41d2941045406a1b03051500d8030364803ca5010b07030303800004542908070b17003e500d1210f881660102c07803020308510101c2c0c0c3c641e8200045070340d912501e1703079001090741015280e10f0690312811504501c02c29011498840e5401051b141401c0c90388800d4502c00100420030b00704213411200411039501c1704120f03031a6039680c0c00b502c1c151b0041ea007001d41000d481032404030901c50305401c003c403e11005c0e0b81514005003030140c126254004060103c022078010b030b0b28030030640703030559000052107007082c00044040391003800d101c030100065400e10005100d20005005003d020311501c2105038060009600d403074007451040c48442d01e0f103042200320020380340d20704003888103023411403840e202111940e65a2004880015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 366285800 1250 366284550 366284563
    0x611070f0e090705010311030402041508160504151424030c0406030c0c0c14040902040204060216091e0f020c1606030c052107050d020304080d1a0d060b01050c0f 71
    0x1261040c26000122035000313100d103842170640e07d020189141c0d0740d0707024480a420035007070401061242600014018105002141c1101c4000d40480e405600e40b07420002075509542c031f41030b0000862801000101c4030040440e00030324080c2c80020301c80c4040041e041c0103e0025620780305000f80041004145114440140309a5840791004c00a202c40440c00b29455a8a01e600a014200b500e200780031030403100d025070505a00040020810f0750680d40841c090b0f80240c1d21140269208082220740b0041c20800342d006069105420841060344013500c598511507441ca070542c20342e4400f1000b142c484d19404070b52141d0508811100750150090201c07100d000d2038421600002d19007210086c3ca10700c44d404481407a90340c00c2c0c4100c4820090358042c1075140d000b400510921004200c8481010810b00103584968011982035451f40d02060040d429a414030224441d44080d0b81a0300f20700340e4958114038034541d00058001000c080d40801a10140328078010270209120300250a04626000210f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 366287050 1250 366285800 366285811
    0x1a0f071118090c01030f0b1807090512120307030b101809020a080606181003090209010f06020307060e070512071a0f0d02090d140307031112040611070f0e 68
    0x81e01588019001d91440a0030a860680c1d03150812080b41940d036120390810600655403200005902c01040001075003918880c030341d1088904610200014190804c5090004000035603100e500480015039294440412130b809240001000c00481c0c1c00c10b01c250b114140055014081d101c01010407000030b0701040500c15684a0b00c3c505c43c1d00030030a100700c0d000f1744220340c9a58a80000e00e448120402c00d03076402c01d071404007080d4121400e81e40280c0e550000f4400780714898800045140b0303035006201901c2c45c140c001007800c5010300c008000403540041120800e0750081300024040000644032410240250f00c8590310070121024024141d070085500e0084a010307400202c001002000103a8050140c0e0140803901801484111010300f41900106000d5200803ca10030408960b603e450141040384074041241d40045101410150001070703039003403105c80d10010b00400035025030b5151548214003450042012034001e83c0601c0400700032040c0544580925074010075155000d04808940440e0f1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 366288300 1250 366287050 366287059
    0x60b120109150f12201c06091707062a05070f02030609030a0e030c09010608191a190f1208070212300703030b120a11010e191a0f0711 59
    0x300284069004960245080705c082c0000c1403006c4440c024449aa40140056560035111240f080025176241e06001c1c000000a10740d6858007210b0918000700c44618015103551350703151031700340078081c40402c09400065403454030700e40d164403910b0800111110120002d41600c6044188800240080003510450341c0640d611140031003004101a526041c2004240e0404964401031204912580415131710402d03d00d40322801d1100d1251910403103408030b03c40f48035151440400c06252810707103840c400480340c81505a18040c1002a01d500c12003840c4078082c2c041c901501440c007041450320994070010b40040c141c481600d0042c004503110b11800c00300400d82c2001c0c014040500040e6084180b003541c607108e4030380c00c1a03050743d03082c0e0080c008091030a0b8809070690000c100000200000410b440c440d40c16101c0a0410000141201c928420002d01c03810416050781110003d03030303108104556000d0a603201801c00711762013010620620003141c4065a00003002414001a60b42c6070140c0c00c1d041d203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 366289550 1250 366288300 366288323
    0x302030105151207030c0c0b1510020c030c13090807081810080406021308060703060602061317090a12080a02150402032508010c03050a060b120109150f12 68
    0x105092103100f440c0c0c1075012240f8060100702014403c1e80101a180120305000300048101d0701c0d0b001c80c800003114100d0008642d10000303081c03030400c10140c006264960000708030703485180700026103d50000f425070b4019044811040002c0031036070400002c05400020301603440c5000e092a1030640d0028601c55041103100d1100b44160078101d864500003021a603039059940c56544c2c0d020060742c0503081c0008002d420b0800441c070750b00207001090241d01d594600151040c41d10346d0181c14580d00a00c012045c911131001030002c514101c8200e88001b10340c0b50001da80d00340d00c07400a03a40c0300480c0c0080d004c600550070b030785007003044590003000c02044a40843c2c03060b1801150644912204540003901500f0002e03140c809503c0100040c220503030346400301c081180d00c43e44200c1c2100d08042c150400a5201c409024098140e8400c0c60017403c14409010701d003103404545540f1008061103000c200795991076040380542000c040c1e40020f0f05c10360b4901120070303607114406100c020509000b982c1c40f03454403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 366290800 1250 366289550 366289579
    0x6020f01061202030d12021315020105090105100e0c0d0905070807141305091507120b0609010507080a0306030519121805010507020d0515012c010506070515070302030105 75
    0x11030340c2c0e0300c40c2e900400034003004c05541000c031031050001c84003102850f000d020410320b00d51524890b10103803081c0001c02280c4519500c0084c25146c02402d01c540341d0349403c0a000044281070703254401d03105850a80d0030952240d05a1211901c1034402c80700c03010740740c817140504006c1e01041c0301040b102070504442001e5101c601c42501c820000164a6104003144d00c40900e00c0002d0f0082a800700c1318000355014400311440e110b0f1f000c01b0480b55400004c190f41415845070149100b00ca29000e41628407e0500c18113800113030041c0709428000c0c04e021404a09000d600c0c1c800d40108002c1c683c030100765104600050b09245201010110894201403010a400c48a40c858650305d88480c3c0e584110080c102d01e8400195034603440320300c0607a00040148406804110104040c0c2e0032420400b006040641c54079914281c00480c0d1420720241080d2003000c1c21401602e90415810b54408844840e078544051820074070300410741126002a0080c03008200429030594051812a0f406468942803007882 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 366292050 1250 366290800 366290819
    0x6061b0106170d030b0108011203020f1203060a06020303061003091407091512200310020f0a020607020f07090b2d0f040905030304321c03060509040308071806020f0106 74
    0x1703d0b00b5400140c8000041041031003424000942c28040e0065480310040b81040a04000031000b103105600e10000511126080035106080203114620183d030460500c1c00024450400200900382013644590904c03061229004528004450740c0d8102c8020719600c050080180c4414244031640d0030251a0001e6440d4034071850100791688050404499851038441c51a20400d0709c80e060b4052107400c070984090840c1d480200004021442060740304c3d903090078001c0c0380080040850045400c091504c00f4002e20003d405410380d500c9010204a0484080205032802004c03180c1140030071004080141320401d00d0b07140143c83c00195900c89440e0341c09018441501c2c0c0090340240309074802c00c00680490885030100040c0003184142040050b01c0340c46180800c07030100d01c444c60306e4008214070b9030348001d2510800b9241015040501a080c5827800040248100030000390a0180c03480000308010310904c0c00084199440c906d200c0740c0c0c0d0b2141c100a5079510090800c0100c2e600e40100400d01e0640d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 366293300 1250 366292050 366292061
    0x60702060a0c080910151518050d0c180f09060504030905010e03100e1e03030910090807081804020a0e030601120c150e1e13090b06061b0106170d03 65
    0x10304500405010482c1d031580c5e00103116800e030140680d99a540c001c00d409407079840c0882200340750350f00c4079403140101c40803a181e030394070394082481400724070b0901e000200c5841d081403c5540041c0c40001a401c101c03400000340804205500300707240303807000c9413040141c980d02040c011402540e40b120080d403144015544164842c880642c150300040c020012401c9a070444040004110b05031000705e40b60f2208262046003450044c1c0b9907030008410807035214000c01200030254038400041c0500f0445886402d524440c0d0080170381003c00018044545c9041d00940040c0c0c0c0d400a0401c651390480500020540e00e503006516100b0700030304000161413110740c0250f25540307402c0804655014039113078101c8010340040412900f80681c1d07042d602c40d5941c515400000300055884501e404444403000c005150980031070949110380303800e8900d00880e4403506401d5101d10165442562490030207001c107103036600101055925070074040c020500e42200082165180e5260040f41e00704000f03403409405071071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 366294550 1250 366293300 366293311
    0x5010b032803020f152202060a030f15170f0105041a06031219030c0215040b13020a03061d1b090402150a0309051c1d12060702060a0c08 60
    0x1103100408504144800c0c800e024440c2c071a004440001000d520328a080800700000b0302400818071042100755448070030009081810b0364120b102002040c0c2c00030b007241c011114690101591408074840c50160741e44600801203d1041c8110340307540d40d2540c0d101100310443c00480c24018003c80c001c20003014000c0381d000320f900c41c09044a1200c4020b8604001c58010000703036052003050440025200e410340200109001c3c2070314007444002114010782a030388200c2070402150300032107032002044651000c0030340103903211202c0003442c2c9820445041c4070001d5100a0340c0403501180c0007082004941c0074111020500344a0038548080c9200e09494100360000040d14016600300340000d454100809076103d03100408550810311f800f5002d9007240c01c050390204c0880e40c0e070007103541400760401c4840c4038058240000800522040c03402040016056031080c0c0380380194090240350b50302c41d0004000d00140070110f4000b0b140c40c0f88025601c2c5c0e016141c00152a261204001d1150301c201c04492195 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 366295800 1250 366294550 366294583
    0x304060504031203060308030403030209030d0915140408010e0304080d09031509030203070b01030506100816050103020c2503140102090607140709051929060a0201140c040305010b03 80
    0x18a5603c0d101a5640420b0001d82010358800000c4001090b850145000d54041e60300140c035400300c40207140c0b03001d602d10081c0d0284034650008000a402090318807010429038a40b4003880c0c0404a0001c0c50390149400c00744d4594200702608404003c004060011540200c1c00c986161600384020b4420b0744450101400c1d50b0281002c4e00004592038006007440e034480d2040300c0c58481580c550194210382a08202e03569004041804092400d080f0100302030860200079200c0c2c540c80544443c40c80c491841201e05264020900940c01c14040c482da03054102c84280803910010680000103640703a050100b21002c41e810300c0848840071341407094441904000d4030071890580243c44401d0300300004441d108035482803140221300011107000d0b02e8021900b5440000d60704d001141c000054421501c030006221b9821144c0f030700303410f00003488500b050109840156070761030030074801c90150510a41c0008510a910244070500c05010f008000300c074024002000300b01c102d001095100c2085171454000c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 366297050 1250 366295800 366295807
    0xe12041202011d090103060207060e0c0109120218040b071209020102060106050d1b0905030c0f0315060d060c120c0f020c0405060a050d0803090717030f130806130302010c0203040605 80
    0x194018800b10018440098500d12110150f00000700d001d1402d170000c0b901c481d0081303004410040346010303004030807000f48003070914010100e00080c1480541d208aa04511b103192a45003591101c802c85400d054983c4030700095860300c1e043c40d034095902600c21000041440081d0500600f141c800c038607030150305a015181603480c00004882d16042030314003441203039540220808280c01036a240c144118980c4442c00560300e040100742c2403c1038420880d0080b040503c1c40c40150b503011455101c003c4007030420983c0e44e155a000b2655411003650000d190b0742ca0000924580c1c1d070460300d001860008642c0034804400ba48408560029590340b18902580c003100c1c83c0502483c0940040364003070405003901c80c1c000d070380d0800100300394100d680640d80074200000344111030f0b40c2400040c0c0075005112120508440c024921990380c13081c1c0d144100b41e110042410398015041051200080400350f084509600b44181c40c454004180fa43c120059840d040c5032043c0c00c1d0000c02640c045480a4444904 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 366298300 1250 366297050 366297053
    0x1b0503160e07030b030313051003021309020c010e03030f01030b0123040507050c070623040602030a030932011a030714030109060203040309090605030615040207020102010b130e120412 81
    0x44510026120b1070030302d82c440c540741000b40c608102030308202c0400030f006101c0d9031400c4117005c4030000c0041d03138004042c010400c464050564003503603011107081510069440e007407005641c1c01000d012403180028023000003800154900c03200e42070305807130080a403805166a0346014124660103c118140390342ea070072508030744a14280c0d202641c40700321418490701d00000403004030305004442c0c00601c045200c0c455400000400c0300d82c01005a0401100c03240303000d04100001e03550340604041c4a0070540c4035044d0008020903401d90b008118650003402104841400607900040c4007614030b612258a00400440107510704904000c4101000d40030703100e01424844020000e503125412076405640f1140c6001c00600203200940c86a4040d076900c0640500f000341130400d55000b81d1080d44a54425401c4c0072003240625840c00c45684c046030b0040c2da8040b14030060b030140c03441000c0180e20481704002143e129006420a44448410b001a82d060281e0249416064000d901a440810343c06460050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 366299550 1250 366298300 366298319
    0x8160e0d0f0804090c140c0a2405070903031206050a0b070501020708030708010f0803031e062d011101180204150905010b190503130b06010e09041b050316 68
    0x18050054a01403005405900c0e0082c0d80e50255108611180da03803c08142d9003944424800564940105e01500e03104c02c44010340c0e40c0326030520001d41b001d401c0300d600a50a18900403503041c41c80c1052401d0040c0d1030082c0c005801240284002d03030100b01d4904460b00b0401c07151041c1025901c0041900d4421410500004400e40086408680c2036500304492400329a054001d540b00e01b49503555043c40e036040100c0342c52803401986c4800181d500c00e00522131403203104002000701d0380d546000c410041d9182d400250342803907666018042c00c5080c1144c10091914a00481000d0f81d003a02c4000380c0307000d402a42c5003210075944803144240c08030040d4500500d050741014158a1000040412700e9854082c0501100e00a900c06402c0b10300c0095840007060081200d03101d00880c03400c101d829880c3c4001c005c0c8095085417402483c400201d000100b544c1c1c001d2411040343c07007016001d6406403520f8600307050002200c5e04c03000768441ca9020002003604e40011640e1000401451007e4541e14001144 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 366300800 1250 366299550 366299569
    0x70c0504090f11121b010e06030712020a0504050405040b010302040e0c0a0b071b0605040608070e0306071101060812071103010b220612050a060c080105010e090c0405061908160e 78
    0x155480b134865400c0165034a0304101c424a000540320b8811000b03000c0800160942840c105100d004807000d008008001c0d0700a80082101042e0f4500941d6803c03002d2401c44040c4995000386900500c0c2106010611030080c400f18162842a60100603003010303152040d58070407820306072650000c08003e090001c00d80c0c0c13038064140702d4440c101d1914003220342240c4082281c03203901b0500000702c0100c1c003085841e60115002e604140c50703061082d44032450380017281d217800b4014031a9007403020031000b0303001404d42584094001d100ac4030030f980440241c1c03c00c0714210b40c08103105960036840c142855006207011310801507001d8009142e559034804d0001080700050790142a03c003510380e07920002403450680c4101460942c440d1b030240100c61107074901038040320016400f81c2c00700300d107010050015036003103040e01c102c03248200c0310400c2c541e441e0590b441643c851600804d400c00404a10600150501a2211241c808a072188800c035950000395a03c00b8802c28100d8000400d084e044075101d08220340702 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 366302050 1250 366300800 366300833
    0xe1c0f0f032d09020d140c0a0e040809010909050a02041a090a0e040609021003050702061e011703131221091203030b030a1103071d0c0a1b0602070c0504090f 69
    0x2c1030f000010b0300003808009030f5034030079940110100d006016401c000e004c850002c5004641c9490f001f8107121801282400003040200910700c0000c4d00803c903800394076528001c1200300e10a2240e46450040000a5002886803c241c030303502640c42c001e082e8100007520b00c18900500012043c5150a004403503450024001f50341d0742d50707100810005626000d5400300790400e07540303011540b0f050040e0003c1c40d0403002803502404000c0c40d40b00c1700c411104000040d045560074a020300e02111512001c504522034007111003c5030104a0002440c8100c86100c94162802440c106010300f020080b08808040084c40c8080011070b0340005101c80498a605d00c40e80e68000d103000aa450044000300e07252081062054441209030711080074203160800214014107803550725030b042070121259103a1a95000b400030380d9519404a100c3ea01e062042207581c0c0302080444a079161000d079820400c1c0250303c0100e064822645c001c0001c9030b24146401440c0e045548030f42e050f110120162200903e05079502c8a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 366303300 1250 366302050 366302141
    0x20309060622020c0105060a09020307080c0c0f070305100e06012d2102040b0102010606050f1e030c040603060f03050307031d06041409091f0e1c0f0f03 67
    0x4403252810b644007512001050400002e060b080c003a0400a0100d40755100000b510300420800c5a125032105031550490624000142c80d00600e10307800381060300391f14030035295110b580c4000081c4540001c031030a40006012042298000024010b51201024001c440d15102c44944468855842900481c000b441e428601510203440745480f505100380d8032040c1c40c840d28421119401c1d4a418800c100410350240001c004a62400d44040e0450154004404d005a808660040c002c1c0d854000c0009c0c07080d000302d80c00d6072450324641031030300703604a4061140003a1034184003040814844407080e050b83d400c0300046081520720780e0101e0f205581445007110f07000300300d241480d01d43c4039900900080c00c4140700c0c511100086806000100400800c103900e10380c0001035140c4000c513009409402d41e0041203000c0b0748140065103140c5045166602207d00c150710144448480781d005d5440c2015240f00e58a10710078079010a4210103a0300f10b0800040300742c007040e16105c0a10454044c406103880e0850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 366304550 1250 366303300 366303349
    0x6030f0a111f0206061203090a0608100f12060c02010504170310170f1204050918071211011116060509040f0c030501081603080a0e0301020c011a0a06030203090606 72
    0x44068030259a41159000540e11100503c1700e50325081c0d04031301444020380010750802c401c03400018266031480c441c02041c011404049505402519080c0d4040c0c00910464100c1a03910f000c031100d031400d15402500e0b11441c0440c1220007034818000d10340215040030b0a52081c1d15110340d104072907800500700750f04011389100c000a0310a00070aa03100381030030034400340100c450130240340b9041c42e502c0c104081d055001007000340101d0b0303944108160801d6004100c4e8140180035180341d0714006940c0c105000045520f43e4841c10800000034450a900081c1d940124a804e080e81d1580d07140408000c2d215840c28808091108510850140c800c10070300420200d000d04014a5a00031168084003c00000703858000502846004104c50446c0000580c1800076003840e5803140800e50150204c41c0040090900c8088040c2d5801d4050303c516072607010003041000042840f00007098461100540160003e200005800340240300342c0c0d124549600140403107598800c10042d28000460b0303032494008152 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 366305800 1250 366304550 366304579
    0x4050f0d050609100608011104090c0918200903060f0703180f030306060504060c0602131d090d030b010207140111070f08060a02040302130b0604080d1706030f0a11 72
    0x108190b60142d0140c1010b4100e807041c1e010b04ca003c1e590113070000015a0f043c61960704c1045d4654003141c040b50150100060312131014038044540e5080d562040c1103d071002c0008030b000102c190301c4545184441003030016248042028540d45008109410fa4103801ca04000303410304000c100210340c0400c1c0391a0000d2010742c8042107000b00c80006030282d8840b000909004200758041c402d40c0e0242005041a034206460304500a18000c00e48030020300c107035000304441100100074003a18000d4000c0002903150800205258940c0000c1100c2c01c8030944521000021305a000f8855040021010f9018240c41402d02c5410140341d90b403240100c0c10411700c50095044a2005c0c0801000b40c21154000c1d04901d01d07101c030440c078003103001c0e04841e40244100000c00040ea1040c1e4054001685184041020141000011102d01650b0701014003801100c05070342c035003584100002d40c0d1132402000406140c640c1c3d000d041e502c00034820400010342c442c55413140841c15408041d84125030040c208983d05808 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 366307050 1250 366305800 366305803
    0x323030f0f030f1b0304120512070e0301151419090e030c010e070621060302031609150510080c070503271f030207020d0204050c12090601050604050f0d05 68
    0x49400803041c00701c0030051064950105110a800c440c0d000c09000d000f90684076000c80b02d12010388014241402c0b0f2240c200e042e4028420380f4181102e4019a41e510700e0540e0020b420010644d11580c03007546054074002d1558500c0100509494501140c0c503c040c1070903050044010001c1c03a0350000c5e160903200001d51040c0c0d030250740414104070000d9078031490100318003400e440307500c40e0182060300510b40901c4110344c40307000100d14040454a070011900c0e50b1400741c0007007082d5000690540100703a03500902e07010080000f421245a44030070008400190075142503942d044c0155544460000d010201d0300c7e1048a4150300884980e902c10724204065540720301d0743d408418030840303006803159442c1d034656128404002c10031090b650200110074110300c900c484103100c4820b01c01c2c507a01280c00320035034480344c499803d0300e80d025001300210705009603c1d04050b00450313424945c1c40802c8000503070095021800e541221400762800d420982032504005a00940394141d0307030080403c50400006c03980 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 366308300 1250 366307050 366307057
    0x1602030d0209040e030d06050307060801030201021c1b060c020f0106050a140102100906090c1e06080712060b030f07020316020103021e0703031d1b0913052b08010323030f 75
    0x46d11100000c5251078442854182281680504180800c48004001513600820001c046e0700c51a14194408614040161605120300015088000030b100c0c10800f0483c0039800180d03500015002c0b00d400c0b01c01c2942441c2070703800302c0c0a09a002070b41c00c0c008202c04280fa61711600c03030744414016210041040c6403201c0c1126100c0754143c0e10680c490f001032090200c2c02071404042c0803400d12403e110030070f101d01030640580e2440307003000304105040042c1c3c86520440d00c076440c551f041c0b0340a11143c2e0740ca9142050607041a611142e00c00c40070004200014000821100a03080105000150960710b80054000f074016802c035142c0008009000f8809040c0a030062061520a231800150034511f0250300c403103403060050b50b000c0343d801002c900d104074000d10343c03c00910600711035241081e95540321404e181480201300403c54800ca40c420040f4075211402c610725000d840c41c0741540954880d8048904078420300c00544400e0f2540c04400669a400d04506480c2c41c2100031240f8081503040312044030361 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 366309550 1250 366308300 366308317
    0x52061103040f06110a08040212031b0f010b03030304022101020d020c0d081f0504020c03160c0303120507050313140609010605130c0212070309050a0f0e1602030d0209040e03 76
    0x1007641c480c88041002500c18403032a13800041c40c150814450f154050030250028001901c510000d801c401e07030580082080790048800503603480310101591880a13039500461100710810750a000140c0c41900300001035a12840e0001d260014240d540c0407610301a00100d84072030241c0d5002c20011740182c1c481d000805402c179032032008000d944140c00c0014043c5d0000360003069550400305094074480308451403941030303c00485c0d005070303100040e50a503407451248654035844a5018103d0405018000c84203200700c9000381c03150040c284850070b40340100c2d0300813154500407490a0000c03900c0704000b220545141c62042c01c60b41c40810384081a20b103009011180401c582e91107034024002402c08501240c01600308050500c00e203801200301a464451000320f000072024041544c8080c1442174028500914000d44565503264503104400d581d24180d009141207012044017184100d9806841070728134110560181d824400840e0a01010b5400005d81c240c2c00303a00c071508120440d5040c4020700300603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 366310800 1250 366309550 366309563
    0x90a0b07050309060a0b030c01030b01052502030d17070e1c14010606090302030703022707020606010e0f0d111504080618030c0c09040c0b5206110304 66
    0x3d2510000700c5244c144010110090f560030700080303100c9a1400200e0490800d42407d01040f50908500100c81c00c0c010350594450b00300420400070b410408121445005500a0302651703c803500e10701054580d1009003d954603150201c40004541e18415001300e648850010107010424007558214000f1b0b400443d0150703445501a5010a1001800d100300c6d80280300a007802c0c42010b1560700001e0f110f03051484085c0c02900c04504a080d2010300800440003028844141446410440c400075074a040c1100c0c100e021912200074540b880c0340c0031704141d041160042255000042e1941c1c0d03054898443e0021680210003200080c0340d50580700090070140080a008102c81c1c5030080440180812040d8030b06d0980d041000355847c81107000c40c020040b2230007501c0e0300b2450b07290352138521880074695112448000c1c001c1080360b0040d288490503c2410483e00c09803940070b8140b520030155020030f20b04041a045000980101034000d0200c601c030150050500052291308190000d08951080754202d031007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 366312050 1250 366310800 366310807
    0x40606080f120f030709050a030506060901050d12031d0102070303091106121506071e03080f010609091a030a08070b0c0a0905040228030207140102071a090a0b0705 72
    0x10204000075942422018002d0502a00c0880c1540b068480d42e11180c00c0031030000000b0f02201c0c003401c031079401404042c01071b00819a88e814580d84070503007902c45511031041040002a2441e00c0c03015914403582000242e1328881103940240c0003000c01c0c00080c00c602641c44405a0800001e02c0a041c00a02a890129800046140071103a02100d19207580c401e410510580300e0440026800c680c0c00f40d00e101c42018444100d00003e041c5024852008100c0f15114541001c020031000f1a800c00c0341c480c2d2035580c210384403420240c1c0c00240c02d0003030000003203903c81c0c01c020000c002e4214a11469001c40c007100ba0030f0000022904060042c0c4c82685c80c2200098190100016000d00d16070091080ca001740c03d040d001e000050030040240715451061b6004558205000e8059103140c050740c00c9812035030700d103420854001d0060341110100351862120004207003d00740d0b040c0210743c6510390003030f124100f4605600c0a11840240541801998455204524005501c203c0000d0240e1810307280d040d01c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 366313300 1250 366312050 366312059
    0x605160b09030702030106170a0b040507080a120f0c02010206061c050d050403050d02030307020a030f210b130603081605031e070b09010e070e07170115090e0f060d08040e040606 78
    0xa4038496440944030512070301904000400101360049c640d503002c10000300a45607400c14901d0512aa00910500c2c041c0480c40b00411407030b03a00b050301e8003156071a00321401d44862000d454100c40c0400c080e015030880c0001420074540300a5481052602c1c2e0428a140f00e12502c445103800044070803000410300015082c01840010092941032001d20710055103149043c0e1802901d640154100030244241520300c03103c1e039401b40e80c1404072000c041041c003049080b5001104060001e00c401c46010b01d282c06c3c410504c54683d40a01410f50303402c654214500411441000c1d00c0e0307040980c06403518001030200c0e540340642080042400072000000b1600d80c041414541c29052025041160907850213913029103040000c100c1c0000c603100800a031b48541d648910690301800d40c60400714030b110b1a90004901740c5e05603211103041c40c40560318407a200740c8803210021985000d40701409d0b03a0360840d0016069143c407010003c0780034410340c1024103003540e400c1c000000000943d02280e03502e468a0b002e01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 366314550 1250 366313300 366313303
    0xe0a080f03071b110f060d05070c0228050907020c090106090306110703021b06041a0c0f0606030307080d231504292b15060605040605160b0903070203 66
    0x8040b00914480c00400a19554120116044514140951a05c101c00c96a607580d120558091500c00300f0305004506c0c01c984000c0060088820882c85185a00724241d0083c00c01c8074039042a005160026a5641c00c1c1410000159001001d1004510401070840310644488215900a003035907110008040c2c03c515164058071107100c40300d148200c00740301d0403010230780c0080d00c41c0f10307002c44440d514401405400402d40340c5c422500a45020180070383c0c005480c003444001841480b19100607550303221007880319640c8a00c4250340310743c0d155205010341400309040788014101420703880d0000884168041034603100b020000c0075072881400b00020002c0259210990415041d4112410000c50f02443c6043d1400324000203032039040c10b01c0708070711103607a00c504030346550000c081240311200d40c400280313410710000d0000003252094400e042e00c0580405500942c026a1005d868003030609040640072509a04554404282c05200000b41d80c04500200b043c1c5006280352030103555500c90600515 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 366315800 1250 366314550 366314567
    0x30308090f0a0b0a0207020118060504051801140105030a060e0c07031d0109090b0d020a12150b0a030209070203130303020c010f05070f0f030504031a010e090604020102100e0a080f0307 81
    0x480242c000041d4407000603c840401a400701c5400c0c130040c0c40e89218001215040c1610001104508079003c3c0440c02c540c001d0040c00840b5802c644a1203138001e00c2d1072200030341e8420300ca0500300c00c01425450320b080d0b019001850344004200800240190385032103c415122054611030181c0d0b030700155800c1810751203108541d01030507914034550307807076811000204030040d1171007035007000e55a895540c50300d580c8406140c9c5545030010119486a074590251041d001f802c108115900580401d043c00020100d0080e826140030041003010424619000d02c80070410045c02e820841c0020000c0c81c0c045850317651418007450080d030080202c1d04180c400540b040310b000d201303641440424002840060030052034140c1155020031007944407a00c41c074040c1d8050050b83c00c02007100403ca4454070811600d41146412a034019001d2030058462100c01030300d5a40c207840190050300100200f02d074504041c0c0191000010311801c17a45440e00f99181c005240e04410b18081100c07100106100d03169902c200038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 366317050 1250 366315800 366315823
    0x70905030303190e0703080304080306090f010605070b1801090b07121505062b0509010f0c2f0307050106030c090209130f0f2f340c03030809 62
    0x842c554200102805101e03001168032218054035940751528500d400d10800000b198803900c0c42d44c807410a45080c5281d6002114004d0007502010300082240c8807150b13040d412210700d511058a01000703a102c03610350b5103001301454207000ca4000d0b01c204003071091094401071405100c4800441c01c1c520002404d017500861007058160601e4440030300e070307081c46414004840b0b08551a03503a40100901c98840903110508505240d04004141c81440d201e60b01f0140c0b040301441d0007009a40c00d2040c40c4000c441520301032700001420b0952110410003940e010380340f08a440e20303000742c0c084c021181c1e8915550144030202d4851351188001c10401c19284c0010010700302c41e02d801e509100c3c0318800b05036140f00701d525200b807031911030007100082c3d16950302c18035a18000c102e081c40f041401010b5681c200f4501940c4c119402c0e0051901c000f41000701c1e080d15007a20791081012008400070102c40c800500c010210007168240020100000c0c00d440b00540c000c1d882919440841e00c1c0501e40d46040c41441d512 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 366318300 1250 366317050 366317053
    0xb301302100f020d0e04110c0d030c1701051908031b300d0b040204030809031b090a020a030605060c06010e0c030103020114031909030522050904020906060d1407090503 74
    0x203101801503008130f0402c1c0d00110515201500701000400100a050959075100e02a540000c46900400021650301c05811554a09000d41703d05002c045402c02c01c240340342610040f032400140003034940540400c0844e006103143c00469a101c5400c83d003150b10034604403030401c807000c940c482e40071402d00110524040207800701100754562408140070010440741400d00d410001004a40410306502c41e0801540250046403566141d24004105511004006101c0d10540c4042815520310009050045901510003102a1905584400607402025905080c192900f401040720348800e4041c0c10070003040f000600701075160078052030120740007030010412080100010300140c1d030045e00761a0750003425000075940b55546912086038000400c0d85800d801d00704803e0005240d03104019012001c4180c8807400079551004180401010301d10400d5001140b040025000d454503d00d603592001000e07200510300141d000c00001140d03011a41d1001444241007030091842e8480b0448014040960 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 366319550 1250 366318300 366318317
    0xf010b01090b04120b090a0507080703171c0e10230603030a0507080717070308040506010b0c07050f01140409050421050d0e0c0d050f0c01090b30130210 67
    0xb140d142c07041e030307130160107003107050f036040804c0000004000100403140c000302601c10b5680c4030083c09403503030360b640310544210300d441300c020400808940032104d404451a05102c0b60710f03c0c0c2c2c8a0038016106980c21401d01c0e00450240d84010205070142800a0361800c01c0151141001e44448030100d0002e01414020f074420701c480034617960060111194583c11010643d103954003031500150030600c2c11420144180046031400070980c0121080340614412420f0312500d03a01d8403080c4441d406049903806159121950800441c01c00305400b840c100c10624100c034645e84a40c03403c0d445607010354081550141d444003084140009504007010106d07143c902c03110f2101c50518001c0450003a0170800c1c0b10f6560703407198201000001c08c40e4900d043d802502154403044241841900c03070055034018482805101d81421040d07202c0c01c0d00406507101207802b2800d041881020784a2507094034000220a41800e4410010301120440a4455483c103030703d00f00c1c540128414415050a0001c1c0359040c00041e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 366320800 1250 366319550 366319559
    0x305220209071110051f05031510050a15020c04050c0412111203130504231005040e070306060e100b180406090501140a05090a2304030e10020a1a0402030a050f010b01090b04 76
    0x42280040c440680f1800f038074503200d91042caca0416144e0f6200592240500000143c44048500440001da00503000d94901510207014070050b0703981101c509840311400c00090141b0303098600c2121442d4020503035411415070700004964140c460184590380303940042409880c0540048002c40500f20a9070140054549984103914050f401c12001030700c168103100080340c056528070010000c01009200340441500d01c3e1909442d00c1c00d07800151078903800d002d0b0204481c03058600d01030296200c40e00082202d89042e0003448181c0101c1d038181c91044560859010955543c0540d5010746280703a40020954904403040e986d80714a14401405401c0e0540e0810a5980704840320b43d0200c025413002c2440a03030080e04040140ca506138085100c01d100083c04280b540c00640203001c000103441d240d08007450311000340c8c0c4c1c9100c10440240b0541e22683c51001049044401a41041c0701030b0885509000300d50303803030f42011810a400c07042c581d584c0f044a010b541c1e0014415008001c4596030600d0241031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 366322050 1250 366320800 366320803
    0x309120f061f0303050a0c0209010b04260a0303022a0319230a09090e070e131214070b04030e030115030506010b0307230301060305220209071110051f0503 68
    0x10740303c09000e101c00407443d80c10b0325003c0e6110702002d030f5000308810032a42e101c2c03400307058580043c01034820b0081e442d815460030f214064004c2c01c2494100f03004000c3c0145995044000e98010010380b0003203114030207590ba42181094485001c1020080619124084180b200214482c0e00d1200301c20480c480380c203205c2003d030500802c00703140e2400280940ea501030580554982140380d100c56441c51501620035103d41000c41d414080e1461070001d02541e440b059041c244221040030060700303613021000001c01d00b40c000c24008954242e2034102d41e080c00281e844005541200300d030283c0200d01c65843e803019500d028071911a07001d400a42006080d400e41c0c48580e96003c0502410100706000000b140c040b0f8040d8080d810510325a00c0b1010005c0d003050000e0116030402cbc0b04000101341004040b4000c10509a2001c0c3d030b00f082001480c100200c0ca030204142180003904003024450a490340185110080c441804940e484035030108107070030704284543e104107540c11080717162103240701d051106a90 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 366323300 1250 366322050 366322111
    0xd0624050d030807051b010b04060902040b030a020a020a0b040f03080919061109100f0f08250315090e1501030c060f030b0301230a0b0604090c020309120f06 69
    0x101890705404944e00c0800030781e00c91069804200000c5881c1110140050054204480c011003d4805000b140c2e079400c0c1e1030080e40254010101e0701030090000130b813481c04950207001c1c441c00343d00c1103444045103500e940004550585007581da030303004443d0710005d0540110341250014400340050102c20004c40850020504811004040903101c0204c81030203c3d2403400e58004100081c02004598502e5138003900070380380050301a0108200c4050040070600071091140304020844104058049408120004040040080051560301c4103443c80f2004600c0c2c182c8041c10100300005880303130310440001c0c40c19080003900000f4002d82c0c8014000640d421580f102200e0882c1000c03a4403c3c0000401c1c0c0c054007401600342e0b099842e02c800803010a417045400400c4040461210310240c4030380d0300c1001519081c401943d0440402c000411010070160b0090071403010510580e410005a0700007c0d640f241c142d11060305c250f0203040071501020382030083e1703a0400002c01400842507100c115007041d410703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 366324550 1250 366323300 366323303
    0x8130311190303020d0f020f030d140906060a05090613060305030c0f0c0a060309140319090602012901030204031502180612011a0403050f06071808031b0a020d0624050d 74
    0x152052806c0300d5030080101c184840c209401740ca40311110000341200078144405200e8400303692030040394104d1130100d91540160009000c074140c3c9401d01c0144094024080c09194001611180074020000b03a032190001561150b00910307a10751201551a2418184128103001c54202c006400c01ca556100000022070303000f810003180400e09401c0904110344a2500e00071507010000301550000000986402c9682c2c03030751501001030351902e90803405c0302c110600401410b01c0c1685040c00b503402070412500d440c01e05240252509480c1e6a0b02c0f6104202d541d8aa403076240c0118290103600c003001041400307948242c1e056800d002c003800f103c01a0410600c10341840314a10b10640b094034400400b03c42c040c54025048402d8496200c200e030307070340700130031590940003402d86240321490090b09004401202c0180c0000d600345401c00c0c01380680b82e15071070300c001000e00c24212184010307111644240304084c003a5500103502503401a402d82c5c0e07080782095003500d0713900c400000d015558480304000c040e10b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 366325800 1250 366324550 366324557
    0x30d080103020409030306050d050a03140c151519080d0315090e100614030606060a051e0d15061d090103080702040b031b28030f08130311190303020d 66
    0x13498030b410154000c00441d00b1094200038540c0f42c01e000d202d000034031600340d548617603942482d0089c10420501d0710b0141c5030600c140c1340c0006502407003480c041340a031b07078011603901c0e0001d8a0142002c0000d40f00d030310b103a114008000d481d00c010003078400180304514075620306081c14841d00c3d5000b21424418542c900420702c00503515440c2560705002000070584504556000b00145616010610308080c0c0c0d5803240d074820b2080c100010a00c0c00d200c0113483c1515002e0300d8a904005101d02c0790035180d1104040c0e80c800510500014003144058060120401d0346401e1580c59141002030042100c52910200b109042c60085108001d0f00e8a1a006045a401120482d2140043e10004018040019107681d25125240302c84801e44520100c080f0740b00e84c100c4130700e000c068025003c8030001109082c2c040044039041810004100d20111040c8101e10414400f490401040c880ea400409c41e80c00540743c13010007200e40a85ca0601c20001400d52141c1c6054404880c55940e00a55400c0300d50042000c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 366327050 1250 366325800 366325811
    0x240612050a0b01050412080f071401051b04060f2d02070603060e0f04030521011404140621060f040210030506030a11030102090d060c0f0801080d23031003050c030d0801030204 77
    0x11f02540100741d4181038505000e2940c0c44a0509200d003910079000013841840d440d100c0480c1107040041034001562102030038542c10549806402e030b83c1c107641304d0211002d002003030107001c6120015281e0040004003009009a511030a00e100a01e004030a400c03550906240940603c45110074030036180d48103105003803030038150355a4501150680030307a0f400c03502e648090107031606900c1200401da1341a85c0325110005094140e400812040d50007440711900001c04840200340700782070980b006002c800d02c20700c000c1e00a2014584403460017038102c481e014003030303084c0c4184421490201185921001a49010300060408400103621a00141001002c402c80302c0e103140c00b02c3d00c0a40507030f402a00c000b401050b202d612400c102024180802d0305c03030001080c0d01060f418640c062480325058800071001000045180f4406583c820700695651411001d0040d03290301044060303001b18030440400f500c0451a501d14580203141078645803000d8400d40000700721004040c1c4c050401811a41c0440e0040351 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 366328300 1250 366327050 366327053
    0xf12050c0405120d0201051509010302060a03180b0405240f040c050301060e061206010b12191b0206010605040b09061b0303042105030c030703240612050a0b01050412 73
    0xe492040364040c54200300d4405400c070044101041080703018005800a00244d0740d05207080d107082c0c0880314626404035155006001608241c0c025104298043c00c0000d5501501c1d1300b05000340e00006411240c90004608100c10042d0601c600420b003a180602108140c107100b46040d9550002442000c40c1100d21002a0a02c06d485000760002d00000d4001c0206a0f00e0703440500300244204c6002d802140c0d0b1400020210400007a444c0c12038191407015400c1c030312140001030560001515456040501da071900c0036404641c4200e100d040c2e810000c164000020103c00b03420310005074411818050103101c10020403404c0300c12a440e00b00120b0705c41d80d031401c05140401540c805004003290a100c00300c1000100708030403400118400100c2070b0700d0f20015080c08100c81c64030040b5a4080e2444003070001c20030340e50180e0001e6000d1044c81d00320ba0b060725104204440d0500140c2e00900020f4100c020703010b100c01e010301c03840313401c5254028180082d881120010304648264400c03010781e520380000400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 366329550 1250 366328300 366328321
    0x7150b100c110d08190318030c080d150b04090c0804110f0d1a0613020c0d030e010902040f0c12060b04170f0708030436020c03040503060f04050601060f1205 69
    0x2110300d039110004035154a150004601c6400d145c4030504e001c00d2038141032078080c84109061180740d43d49540e0390b0000a21079030701c1c3e60301c1c1d4001d400c8500034151100303210f20002000d902c0c0742000d00540d40c91243c039945000304400988280740390390300038041101e050101040f021100c0c01c040c0c42040e18200030000400300441d0308840960b00190081d0030314801c4a05000001403410b000f03800407500316250003641e51282d802ca21412103151550b60001c0d20f0180c0305400f03908170001d40002d032000000c0b122030603004902039802c03c00c0d0303181d1120365414001120340d4120003644c6802501f0201002080d09099500a91b44101e0090001c003802c1d242881500c0c4108010003607081032528251680f2690320a0a180d44e60401d004030042100000c1d03850401e40c0070240884400d0b0380e0300d40300b0000e2009070354200d0000d5122101c605224042004082030325101040701c240182e030326403041c0c01c0b54986820007500b4080d040c0c00610070000104840315640b607201140095510004400107905d03181d950180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 366330800 1250 366329550 366329569
    0x110118152012180108091b0609090a060f06171302010c08070507030209010b0c190503041205150a0506031c05040b040f09050906070507140106050a0608090d0806010215091207150b100c11 82
    0x60f44910048204181c41a10303801c101d0890306e0341a4426446501da12058030f5514100440d84421403608000a00350850c516105000e180181003415180c04103480f2540709a203c0300050b94980c0c8540c41c01c0046080c841521401414000c1e812410445505003180d102c0809410a1329141e981c0c164080038400b0501c101d130000c10076a155503600151a2500d00d841d003507104d02e100e079804c40520000e4001d2406008e900d2042400034050104647d425400f82c1801c0600c501c0e64040040c00d220114083c940040107102030241c1501c040c0d1083d14001d10304083d910b004000460982105d0b0900c191290008140c03202d49900c565100440d05c0000c03000c0e0b0051510ba030245900c242e60700c10015000c0e40080c0e64030f00a1148009840000614000545202009031080340c0164000e20101c0c01d07403100741280c0d50300000140241d440042031040203d4244c1c02442c1c0a860301102c010012107105480c0c8206101c01009650b0000c104084a20261241c0515040070f400c2c41c9500d5483c5000707075030342c2c98135 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 366332050 1250 366330800 366330817
    0x1f150311220806060105071e030c0c090209040e190f0f0501050403110f010c05041e0f03060e070e070905130e010504110118152012180108091b06 64
    0x804030040781c5071003200840c4100e10800c051400762001098255218800700c3d408150402c03030001340c1071058510144040c960090950400ca0501c0c1d00c400010320941c2c1c0c5000034901400c0c0035840e8803082c000c0000f00c0d541c6245c0c807150360b0303c50703082210b414910881140100d03800c0603049121500754109001e004c642c060000b0020b503e01010003082540140500b014803a04108840c0c0c0301118446480c01c0b220364504000100340103100400120307062101c20040d06100c03803905c3e10b81c0f0356039100440a4a41c25002120032a441da070b00014600c01c100310040007402c5841690317603d4200300101800101c0d90b400340a000300302050b10001032040701c0c3c01003042c00c4250002048940b8160902d1540c814102d20071a0000c1c11000d425007000c40401020781c2598590540000c04510f8104280d807107011489810311000100d041030b1002c1300c414000c01801c1c002c04440c09503240051a03140044403080e82c04c0034107101524007403140740e030400141040071b094400e510802c00c2c08203000050301401503984 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 366333300 1250 366332050 366332077
    0x180b071401140a05010503210a0c02030109080301050306280903050f0d060503010e0106031a0921030703110c0d0c021302070f0215210c0f0309061f150311 68
    0x1d03040d41e4411030b0702e5094407420818a0822450b41c0762002c06442c3d0202c1941c0180624001d5600b5003803104040c000c00c01c1c035460b82000d4000f46200d602188c00d56846941c00e84488101000400c0741d420305010007a03010803901000c0301404000c49400f000d112601b0754183e08150b44205034010540030340c00300c503d280b0080e080c0a48550b107a01c2d10324042c05850240034001d50800403c50450f49050103800240c0741e100914144403403401c0c3c00700c0f051141c01066840d16204600c106548407440b020586070500055094650701d1411150203003c1e211402c0f40e170a5080010000b908010070085040d20300c008041c40d00c0030814290307000060049400541000105100141200400a001704003608040c421385031490084080c040c43c0050b8007610303079840e01da00f07007546184214030f51040d1210741c0650444005804c103c11511503c0b160b170400c40e0510300c00d90194003440120800c000f4410070b600d44102001d8440ea090845500e0b40b0a1040c1c1ca030300070300d82c9604c1d24003c0709032203c0c150349e4414a80728 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 366334550 1250 366333300 366333311
    0x60b03090c0a060f020c01050d15060206040b010807150315050613031b030c03080c010207060207080c060f100603020f07020315061e0901060c0f0605071806180b071401 74
    0x1034800791a80201030840344075000c001c000180c1c550140520020b9030f0b400f42c019010324540c800065800d83d214106c4802116030728018520102443c1d20701d20050030450303000344114030f42840e0654407100180c0003509944c0c4200300420042091150f07601240e0501c1c600402d00a0705138845d07003403141058210a034003020200e103545a100001e07900004680c0509008039945110a91101d0703404100c0c08040c0030041051014000706071000000d2503001a0040010311b04100c85e01c40000301c0c2c00144e4125200c8400142c00000403c0400c552604100d4100d4006035a0601003d0b02c100322409100d25824960003244843c034280380d10003030f90034050b0003409544201300403042d114a10030048440b1449401e10421078940c0c40704200030380c0d4403550040c08162450742482020ba94000f0410030440d40c41d5800d5607680d001981c0c50150b54010550307904c5042282e6250402c00c1d0244c050b40d00000c080140081d2030400c2070b1032901103001181c0c0b00c901c00c0e5948604a0811401551300400100c85039824407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 366335800 1250 366334550 366334561
    0x20c03070c1e09110a050a020f010c08040c050105030915060a080703080c0d091202090604090204020c0606040b01110703061503020607050f1209060d050c04050324071e080a060b03 79
    0xc003403102c034289840710300b003502d94481400300e045030803220714030a40000030703c500401940180020200c0d035003c0d0040f01c490350340c020300703907130030740381034000c50000201c1340c00a1004000050b808400580002d0070820300f14500f00314001d5858804907070000f0300c543d44a020403469101c0c483c01001030120001aa601d144d100e040c200d016170b12405071801c091160700a1320503107510420f041b60645009400301d442e10003403a000c10402d1100600340b42c2e8820341c0d0740c3da040c0040e500c40c030090804000d01406440a4505001000200c505e01e410950500c10b0b8261041d10350400402c0b0301003501d80c071050024004484101d450501c80080c1c200a4005800003007030005d20400280d1049103402c200100e85d40f0280244c040050790058240d0660000380c1405a066054216080140d2090b084036a0908003669000000e1030150081c0b482e040100030418001d2107281a013980350361100b0703a03091108684110400c411000042c8401c01d81c00c22007031402140004035140c1042e0010500259103c0d2a030405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 366337050 1250 366335800 366335819
    0x110a1b111305190c020a0803040c21020a0503071206110c060702060406051003150f111605010b060c07051c020306040b160201110319110c01090b100e0109020c03070c 73
    0x54070903003039804543c002c2d0b414406403405104142022a400340002d1036044d640c07440c85400140c02120000800c3d0000f19503030031881d9080190b45201103074603180c45000d005224621003e82c0001c1d000350010130081c0704000c5041001d506c0340743d22900014038038290500d1840030340504407131010303240508814040c56031750000c2c1c50707030040d0300410081101c1d8443c001d03108441b89041c44014040c0030300510451310f0164039030010389805104040440c440e8681c18800002d40e200d444001419082e141040092003000d200c1c18245400646d42149003d180c0103410350340d0656841094031911022516001d00c40c0c550003000c81c0380c1c1d40501111981e060610b01841ca242c41210103d000600000c98459442d10500074080000744c00c05d5610310719103400c000b9900c03044c0001c3c5100c1285455418a810241025004200260b6140000038407400a868041c00307150003d4141c15030400b107070074180a0380305a1401a0704450440d0030041e5945464078040d421801265405484402d0000c4005003500b00f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 366338300 1250 366337050 366337061
    0x60804050f01060305100f090b160e04050105030a12090b030a02070b16080609060f06030a0204090b0111060f04032a050c040e0a15020f040612110a1b1113 68
    0x3148040d950303501d2100385114202c650b50300c000f402941c0075000c8420304400907800030042e414060310108102c200c5440d051807055058443c003030219807814007207031955480741c51403503682c1003142c05010765494140040e5a40303103201c502404410401401d40c40441c040c82546006004c1082400c0e00ca203000c1203240029044000241c0350260100001101e13040c40000400c041410350b29a49801d841d100203000100200812180e0811a80304103080c06540e00c0024520034040400096521802c2016040c15281003a204505010b00c0300310203510f543c8081140796000780165200d4950b0347c2e45007130480d91010403594500c502030700c0510f0940300c3c9403a802072954170b500500031200448003000070300086902402c0c1c0b01d603054000b440000000b51520701400e00c4681441c8001d400c0002c0e002081d81d943c0d01035406040840c240301c42800c0c84800c58060703080f4040340c00c00306605107000d04101600c40030130255459126400301020000300503019900411614000d080800c0c41c1d0b5484400700300911703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 366339550 1250 366338300 366338303
    0x10080103150b090c180a06051b2a120606010c120e0a0602030d0614060a2609070e25050c0f0f0313080a051908090415051002070608060d03020c0a060804 67
    0xb0017682a07002c2906001e000a4101c4010760794140c60040c11914405522241a501034607600070b410b2194170141c071040b2210341041d807a0a103a03007540d0508040001002c1200d81c40c040c540c0021080111aa030003402c0b00c88500d810a081a0405034038140880381e002da0f45106507880190500007145060b80040600b45081441d2010003600303403680f04645481c418000116480b44040042240d2113104204070290000c40c0c00c13102c0340303007520904170700c660100440781078046030701c086000c205900701141c80304d4204180c10504a4840242d080c0103501d0205007250405010002429000300d410400034000c109084c0c2041e200030390a5a1141a180e5209504d0712400c0c42240e4808200e40402141170319580354040000c20000e02c084440d44ca1003250700000381c42c22801030200000e03540390790081851403c0d200303001820050504003045440641003500c82c0441d80403007024003c503038000000d01c1c1c20036411100c035440d00409282c100e1411201c2c040e00d50b080506030a00241e1190403003003032800b90303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 366340800 1250 366339550 366339577
    0x903060901060515210a0e06090f0d0c0305040e0a1424040c260711031612120612060e1515130609050405070602030c0601050d142a10080103150b090c 66
    0x1c4e00c42c00c00c0e9179590030304032b01e140e40303940c0044620140719801030401d224005d00c41d052590074136903240149518207e04031780c01d0361100e8840d82403003101e142c08510280e000c800f81750581a000d8185044058561a001e01d09009542c0c642c6902141c5000d04540d03040f00900003610304d148048803601c016114815681000842c5800c500031801d002d001c000e0390840b4602808001e01303540c254a400811584411a1005102441c507220b800c9481e18003c2e40040d00300403240d880b4100142c03074804100c1e6800318815070180c114440502c014215a11004d800c060804800c4082e403003582e001036001081e0010020310b03a0310340b090002d4042c01c6500814800c0340103d040d20300081d82c13a04c1c16a281c2c810690b0214130398100d0001800503140c00802ea681071805000101100400580e082d860880301c5403545c041c640916a41445c04e009111092104000036590043c6a900000c0e02816031101804014040c00c070380c8800e200752003107642c04410340400040030072045050040380254198485445003109 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 366342050 1250 366340800 366340813
    0x90501030c020705131817040311010e130b040e03131503020a0807050d1e0f060906122907050706060f050d1202010609060b0903060901060515210a0e 66
    0x24004a149404c644001c0c0242c032403032014841c950000c1c0407416645200e10795211600c2c3c041440e141020b40d00c83d1211481c50354480c25810804c0030b542d42c9500310381c1040001d0058011a0b1240c85c0e40781365008002c6004141da000d008000b070040c122000c030b003071054030021991a85c01010f104038082103400c0c8410020600001a108030140e100390740d15500420302600c04941694400c2c00107081d074016408001980c48a080300d0030200c81500d00c4181583c2da204c464500040d095440303141d00520081e0b108011403407a041e4050307d050070150019050803d001607210000270040719412840c150503c810342141341a00c40030f0455080240c0581744945404404200d868042045a0645400800ca00095030007075803011b0122140000c050219502d6540c0050010300d1805400040c10003080c20300d4540c1628000d040c03a100c4c000b1702100131030b03050144c1004551548003514441d0b40e5150304640e561130f143c101410f00320400d0a1640e04c1100705600304040d941c500d034043e40703000c1c9500040d61030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 366343300 1250 366342050 366342071
    0x20405090609070e090c0702041a040b0409031e0302130308030708071115181605100914040e03070803010803030a14040309170c03060a09020f100c02040b18040309050103 75
    0x11802c00b19080c50100782d51032500035061600c04402a4030100440385a8a840441c0e4081002e0303c028464400303d140c014a074107045803605000b0650f244009540800c50369800b5100102501c0c2c407411201400441c1034540c0c2021031094044031070035034940c0c10702000f0994901d803900455004803164000500d844000c20b4004d8400d10800c00e00300c0485000306003400c04000c1c0c00e0f050160281c400b030070070035060040c00816681848220754400b1000716000c1c420780303804180000c800841030820200848100240b001668207000c40b6224203082c0d40000d00145508a42443c601c02c004000c0c013a5a4048000102002d000006600c150f071500001c0c818070504030201d406074042514010042270400f88240401d44c5241845064200c81000325440a44003801007400c1c04000d0f5034090045803591321002c10750801822514a094040d41c440c403407800b489a004054044140c0024402c0742c8580c04910140d031120020140e0b00d400324043e20050278107203030151005101d482142d0119081c05400300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 366344550 1250 366343300 366343309
    0x30813091a04060506120106051809040c06020d03020f0d020d020403020d0803010f0b030103440304051209221e090204110f071112030a0801031103060420030a0b09010204050906 78
    0x10341d40c41400b4000d81c041d23420b02e8400d8810f6000202c88841004d05026104150350750813490900940c001e03030354850807a0038100001e0600b14042521010f040c010410200a100050f00301c9007030392409840140c070b91005040d00c0c0e02030b00c19540080d5000c0d035280350600601030fa4600031412900d9949100d4801d95503100301a4141c0400d00c005401d016442c03001c2ca01d00954280000c1c0c1d81600e40c0c004604c000d105940403156289622150600c08a01000300410004100f258540b00e4420748403550401c0303c4800020660100d00e40420045401c3d0702201d50b4a0200381c003e80c0004034180c50901703500081c1141800240030700c007420ba204a0425024001b44541c4c442140c801204d4080c0e4a803034410940c50300100d0b61061601250130201c0340c214601024024006005012015910ad9511394510700f000040280d034a400f40c4e119410007410b1000240c1d03044e059002d540b461204d500110460030300002d0521014020142004500340c040050907841980100145c500c00ca0314a20623441751814030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 366345800 1250 366344550 366344557
    0x7150f0c03140304030e03030d1d011b110a05120c0c09010e1314031206010809010c05040306091b06020f070b031509090a080706020702100c0b01030813091a04060506 73
    0x9008590982c05070b165044100005580c0b05019052485056500c440400d00c2c0d1741c040c03110f07031810994556981c41e05640c0d1003006401087c40da0001d003c0c01600c00d1004401c481085554401c0c40102c001030049580f052003845a6260088152446103404c04810446c541c0000c0b0108100c3c0a034089007c801d203071010341d05040c0c8012030501c40b16a503480c150b520b25011600e40642d82014528000c40920760104010400b03a510303c0304442c4a81825030014003a480c01400a90483e410002c50100b007540c00760030b4504807038100c04086840c062a041c0703020088801d90341d81c0e0711091002008528541c0000d50860090f542804a642c125135509039403842d400b0944541d40398032004141201d482c60304000716a00542110182c40d25001e1650380c041c0140c1c041c010849a035a000b142d0f42c001d500e488140c2d01c1d245001410315290800d040d5407500240394050000038040c403404a100e080304101800c1c050041c02c1c41716410014401c0008840d98070900c121461446035083c11004140d0b804c02d42c096 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 366347050 1250 366345800 366345803
    0x102070605011d04150c0905090408041e0803120618070e03070906060210020c0102160b06090601030905030318070f060201060801061a04060305061507060506090903030c16020f0307150f0c 83
    0x1034111015910018601808901b0300b94410829441000328081d55583c2030f5038011071156022030b80d1b4503e0300003410400142903a00c5586900c00743c001300000350011085038089004000d07188282e64a202c0016070450115038881c3e03e0090070300400110039000400c6540fa203c00b1401c855525946041140542e80c6074065400180c008580036540402c00c1e401800b011010180094207240c80d00800083d0440780c50340949066100c60103100c0181000e011a07a0408401e01c1d0510409450303407130300c0b9aa803201800488850b0b898004c0b0054031042445a2000b900c80b410a50082503501c00c2d00070301a04640c020201c60354a01030b400556003880c3c15544900111030b543d16410a8a044000e6008100060140d9002205180400f00300d00c201c1008203400343c86404000b07001e06116060025444c4e00411580480d4020030505c980304040b04203544c08056070340c605240070000c51000c543d107160100d240e19010b115841d40030440c019a210a6100d142c420740c0e0300070303c840a030702040300d860510140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 366348300 1250 366347050 366347063
    0x90909050c011709070b0f040314031b010c0c030c3e0d020f0126040f0b060a06120c0203090907030203060913021818100b190e0f180102070605011d04 66
    0x8011076082c21b0041c014480b400c0d192241881d5680d03d50804a59014031075001726000021402d92090340c102d00000c903613080100030003c84004180c05444000010b102030140482e5200403c04c200c0c200448080508070120810544408850511074004070761403001c01a400e802420a024100101e080d6041e079001803016400700172860040d40c40c0c8141f40b00d079881c20300965030407400d501460b182d4540210311a10fa510418221410704200c02d86000d40014807404040200b00002e0358070991750f002e100c1c12294000b0350162201c005a280d0320664401c580c00041c41c00401803180d0701603010314410001598040f5460744d90780c1c0b9040101d4200d14009600c8005610203422001021483c1940300c400111000d0f0401c1014806500d010643ea55440d10642c42d10b1180940d4204a040c10030f00d500082c001c640c085013006540d101745040105000800300d84840010556940107010004556481d0021941d8000900308000a85400d00508640d11820440341241c0101442e4040c0328581101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 366349550 1250 366348300 366348313
    0xe030403110307150503040b0f0928060504080915071a10170609070603060317030402042307030b01050313062d0e0c030115090903090909050c011709 66
    0x107039107101d84040c1c8003905030103110361030001c21403074a82e1000302c0021505448040d00c1c2d1030039140c640d8603c5401001800460f944c0b0040c03102d01c1d200060340355441d480d4000750b0810410903180e82e001c015403810020b0500390502d0306000a002c54100240410306080e00c0c10f890828104240803a18030a0b140300810540c102c0c2ea2070300c0c55090a03200d45810248003238695281e103580b044451210340298024900f1034010381c0a11903020700400490740146141c0c1420300440d071842d15036001c0d405810b0041d896400002000404540d1168480d00105403801d58900c2d201801c0c0207090507140c811190800840d240c101e214184e580100c069a11034031300703803813061010001e0380d640700003030700703124a010f0100d41600390008c90940070f68680032501030342404000342c410003000c0041e03d8a01c001c40050b000740d15080c081e00140001640060944540031004260071070240390448001c401075001c56005450403028008100b00820190350101c0e00b41e80c0d08490440c45c00520070022400c3d98034190f241d01c0030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 366350800 1250 366349550 366349553
    0x20406050604030b0106080c07080a0201050f16020c061309090c03110103060e0105060c0a1502090301052214030706060311030c01110706030e1c020a0b160e0103020304140a0c050a090e030403 84
    0xb070006942c40848c1c1d910701c9003460320030b03074840c1c001c3c0d0017100d022001344c0d442c2c03410088a26110342e02c0c0d680c080e0030f42d2020030889140f02c10294032545c11005403401402d000802c3d140e9000b44040c10801085520401c000c404864202488a410366000c103ca8a1001180b013448661090040d0b0003900c1c003420003000680d20701400c0010641c002981d21096018031500c50700419240d01c0c400c82e050301107000150340d40240c04201802c40d14000c00d40710301e055a400120b000c0c0e41400441c4610240e2000d60140017440b902c81103451401140c10041c2861700313100c4c003c006c0050540064a07110001d50489120101060064032038100c0100400c13075560103001c08101c403a120f80c101c0e182100200c02614488e454012000c21444028030f1000050fa1155140c0000c02c003200106540c00a043c03225407c1c24000304000420a003880304150f8100f44d004008601803144000503901c0c043c00d054200c030300004103844e0540d80303c0490f200c1c19210b030344a0480080c0d610f5913070040414400105000d10700d03080c01d6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 366352050 1250 366350800 366350807
    0x1c09150309030c02130b0a1a03060d020d0b0703020703030501210b0c040f080706091706071d06070320010624030b090702150c0a0f0c06021c020403020406050604030b0106 75
    0x4100c1c0603002c0207401082c01d405602c035500b01c508007103103162002c01d00042c2d00003400b44102040c4c0c44441098000300301404122100c0040d250020000c6602401d013034030314000191410112a4042d04001c24501405038680e00355008005891180d2810303c166aa55014203046140b03500d006910502d20300801c0c40002c401d9103260b5404420a444582401c0d211405100c840d07205030001240c179803000d03000384950350b00802d003500108540041c0403e04010441c0003615100c000c0c10748018890724030b40e51600d006080306044060100038000b140c580000d401c000304008401201443c0d000000c141c107c482180600a44007552039a20101c2c4802c040d030401d00d144103504107510030405542c0d040c4a11543e441d46d01e42400349800740d0041110344d000505103016114003929517885003004202c003c000642214187c03980c0130242c10b2214000b20385040450291241d21500341c0ca10301520b030000ca44000590260059234001d990800003d5250018000c140c03017980805440400b82d080100401c0c1c0c403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 366353300 1250 366352050 366352061
    0xa0204050a0608010c02070e09030703050f0307021002120708070905220609020a05220e0a0e0a230c040504032021180d08190504030c06021c091503 65
    0x40303100040c00710383e210005821a480c1e15071202c0140c0000504100301c65210b1441a04a08120051442c0c850140d401401c1481a0303051400508404000a002d241c028480700e000c19059080c20340d80c0343c0f1030403000d1a01020441381a00410080c40214400600c12081300090f9100509283c41c1c050303900251400c04c1003210000c5100d00d4a0700e50105022405001800c1045015218241c9806226441c040c0ea0b407201040501d810b546aa8104140007240042c1c6412203421040040c0c5000c180c50702c58104542c500001d030000c0b005440b848814450109803041d0714030750109580c1181c0da15800c01054800070344020780000c184001e44601c4004000c03c2464010140c2d0842e0b45950b000c1d2024a9156101c45107003a00c500d01184901007103074480c0001d85052011900144442201d5407804014003c528148009000000504c0701ca24040c00845001d15000848103585035075034000203554100001207a000450720341d044034980e0340141c3c40740701070740d20702c2c034860380b000300350600840003080e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 366354550 1250 366353300 366353311
    0x301090c08190e012301030c090c05042d08280f0605100807030b15040c14030604090602030907091d07140105040314011a180a0b0301090b070c020901050901030201020a020405 77
    0x1540c0700008280d040c1c003a85c920704030515034490101258510b00340b0914180b0103602c124035440c2401c001c0040d844c2e02c042144d003507500081c2013041500d030541900c4c8c0c2d01c41071981700c19030684010402040d000c1002541c12090b00b00c0c1514800004540a4001180b403a40d050003041407a040c81400000fa00581009a0001e14900302c808000c1c0d40c1c03804d4034509030043e0f2068a404001e10700b0300840580314035215102050607601032007220300a40000300209621400325500c00000300110b00c041d0346641100e1101c940090b07013591603060407901c00780c40303641a20510321554504456017017414032100c06d00300309040000c00350100e00e20346031143c1c50f041c5448820504002d020003002c00010b041d40400000c46080e0f40001482070f59080c01000e0070854074090038402c810409200311804940000950310021900303000c5203050405011901401042000070a41154041041141c6038015000f540e528021244101c43c1d03640c40040c070a5108080c04041d006070404001c51002d030901d500203a4000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 366355800 1250 366354550 366354553
    0xe040209060702031e070e01060c0605070908030c0708060f0f24040203070e0f0a0b160f0c080d0e0f090a020304050f0d05040302281205010605150301090c08190e 71
    0xb0150307002a081c0340700e4195001048440c0c00115810030402c1240d040500121a12110154100000a40484d030003207001840b0035216400607280c035204954010052900c0ca044a8840380100c558580f02c032441d01410350350307106030030000c0c1216845107001030050380203040260395908c6141c94101c00e070440c035459651010081c1201c80d0035444510007184140c0042d520100d0852070300e02045500700580300494400e0407070582c14032581c0015030843e0800344a80080389030044007458500080100ea1401a100191203500045c99000c04604900003010a64400343d41d180f0840030001c0a0350b00c480c0c03807500aa41c1c80b00103071413602c0650007035400074092411160000140014940f0306080f990705000042ca0108040045060100700d1054101c1e0040700000c40404004004a184581d482040320300e01c140c124513024000b0a5010720050f08024154141240c0502c1004200381e10a100b02e20405140034003214225100d0b6520902600ac4052480d0001c80032040c46006407030740e0001800c1d01d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 366357050 1250 366355800 366355807
    0x1d0a2601090f0b060f090402101812110109090e0d0509010e0a0611010b030109050a02062107030515180f0a02090d0b040501051e040204110405040f0b040e010b010e04020906 76
    0x102d00e40260700c12140c2e03c12142020302d0310f030180620118030000b0700a98040c20071801404016a1190403440a0354400c0c80c0c001e05501521b0046881800070754444102441780007582030278800390b02c4141040103000e807600d000c41951241001c04481c3c92802c46c100c079410104c0310003c898803c5004241101c8149000d0003800d000070009008041c2c11303449800803403128400402a00320a020b91040b100f011002000440d4090f1a0315845003030302c06000348035040003d41c0c40d2081c40204400160030044290840d69840c01c5c00025000b003009036804582003089a85120381494600183c0c0900c0000040741121a00c8803003113034050380740280001d48966020710523030031642c4941d4500740302103003e1000707a0aa0700741400c24030b084030000b6002074080b2100d02c20300c2900d0140b0ba40340c41d400682c1640d001802c01c040c0c50800c2040d0240743c014a60250403c05c0013003041c5500d41014042c0306044500b0071003001d900d14128203d4801d44e04140c04924403012056180c502a8003a10725404082d02513881c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 366358300 1250 366357050 366357053
    0x315040c02010608190c05060c0a0c06030e19030e0909010e0a030c061508070311031507050304031413030f1a0403080f010504110706020c1203071d0a260109 69
    0xc0d10400d600440050303541e490100040101004008400b4440900d024421503103034a4a265641660080601841c030000ea07991884804021114420780c124214030207880d102e0100a014021074401c00e00180704030032b05404074002c407401c0070104907810384074050042e1403e41400400300c001030034900c29550341c07200e0311482c0805111000b4014829a2090000d4400b07142c800111101500160036482c0c412605016107a40000c10f1415030741c1050b020441c5880c4180001d00c0e0141107170241c820042d07500306100c05650058044c0d13024521a4850190720505000c080b00c003400b0f1074091440c4501c1c405010404982d250589450280c06042000c51a1340c030000d0940e10000281ca044000078182c0b0b00300280b080c0c0c450f80e4140500b00456091021807981c0c402841c160040c1003001c0c11051b030008480081007010801040000400c003180b60301d0b45050440a0326030040850b81076104141400c1004240c90042c0d10282034418030103280c4914010180c48036400c2140800d500b1031590303035822540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 366359550 1250 366358300 366358309
    0x31c05060f0a151b020603130f021302040305060f160e0105070b090d0f021b09151e04060504060b0d021e040f230108150d0b0a06030203250b0315 64
    0xb4094003401c103c40c0d1600c145072400070041250903642c08044071041525900680c2d40b18203c03504400c8508000001e0711075803e2400c1e40742400280298805a42c0358415130f158169005401207030700500c02d90300d5595400d60211000c2e04e041340d081c8906104800c0c242003407406034400340c0ca900c8047c94090308004040e50786004000080e103040300c90781d22020482500f50340c0710300c100c0100e14103840030305148512400190403144c03d44200b0ba1161680c1800180340f90f0180441d060207910062103040c125004030050400818501c0c41d850045040c60800701c1c19080501409040b0717024000d02c0d910700020400b200c4000e40000200001d6140429080c0702d41c550320002520150007180c0c403081429240c045626a108003503104c042880580c1a02c0d1010ba83c0c0240105600250300c003030488400100c54000f980042103204010070451180090000c0307c1038542c00f10094074420780440b5841c003425040c0d0080c00300340907106100030034000024485000c290340a11f0b00080c000000210003d032010005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 366360800 1250 366359550 366359569
    0x124051b0712020a050a030b01090203060609061c05060d0206032e141e0f210d08041209050904060b0103061206020d1a0310022a0609060702031c05060f 67
    0x51a042d03155062000c294a06090000b00030801296240c03260f514681d00e800b03500394148259007a13035901000003400c0352150000c543d0070190003003616a0300d181101104070f210085007440c40352685440f00190b00b03030406106160f001600104400d003103644082144c0d00b16401001807442200c82101da00d02c041c64441d0590b00a02140488a0000300c1080148907540d0382861070b040c4d4080208452002d940c5440c150400d04ae50305896030070b0390095814101300011034101e0054250300c01c03075100210066001000f203001d1031040070342240440780e00004554034050f03802216030002840004c200018010b61002807448018180420f034a0b68036079400c084e940e10064142c581a400080c00d0700e024009104490b0518081824085c038810341c50003107503881c900c2c10905166950300285180902c001c0790500219512004403404510782d1403c4c695403141d00235604c2d1020b502c20b80b400b00d20707000d00100540e2200c00c04840c01a42992840542202030301001d0807146c0c0111210000190940317072201c11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 366362050 1250 366360800 366360809
    0x50103120807020102270a0803030703020a180509060616080412060b0312040605180d0c1809170703110d080717040c17030f0c01140124051b07 63
    0x250501044030190252110400078034000031644100010007104460703000903203901d4403810001011080220108110710b8860300b1242042c031003c400c120700a903064008099071000c40d5108024455603145e8400b01e24030500a441c0c0c030012000c0050101d040c0007024140304408040100840550744e11402090350041e0404400c1c1e0034a400c0b9242804032078001c182d07801500750020250100d401410501c0c90003039000d03282c00c0000002d0f050000194041071070b800341c00010076010084045d0301d081c1160744041d2060441003502408400000a05ca10503c0c120b2600000400c4003002c0700403401c056139120315021410b21004406a43c407003402001f1800d9900c505880d600d00301c1c20510405030265904103e0742d000d000d010f50812000460b0100001d08076441c00c00895020031008580904601402c02031515480e40410040c12034001500424a8010000405034160340c032103480ea14002e0600c294402244550180340c24014452401486002111000b41e142040010851414020039074030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 366363300 1250 366362050 366362063
    0x90302070905090606030a06050a02070b0f0106110609030301030303090303060b0d06030c0801020412020f0f060a0c060b0a2601020f0d0204030210030c0c141c030509060601020c0303071113050103 86
    0x1003030040210901c1542e0b001040e100080c0712030f05e0941e002a94582c92441c005000a44802c0441ca840b032282e0140c4910780d52217a82c800d524900b12140c0d603008a42449443e00095a10801c00c5d4038075404140c0340d02407020303107000e98916800c585007a0040e04a001089041540d00d001c0000c0d5000d80c80c1c0078154a640c0c0020108103145181000150550680c01004499104000801c00f85003640c1100400b158142c0340b25144481c1d80001594941904002039001800020080340c0da030b6008107043c076401c0c800c042c02c00101c0c03c0001408450b0301617024080480c12a040020b41249601c000b1260090041d0005880d0103040e90010703007550003c4041d1341d2115000310b4240114034101001002402c0d00e46000c01c034290100030010000c00042c84d02a00e80c4442d00100000c40005120126151400201c001d02050780c100d0010000c0c0803c43e40300b9054096040405d541d5840829000c0303202000078021802d100d01034a44c9a40300c2d407502481d81d8006040803d03c03244952901405009501441 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 366364550 1250 366363300 366363313
    0x60a2c13050708030f2d031e0a0c0503010b13090218180c03010b03070e041104060315062001150b03100b090d120309020901030b090c030a0c06180306090302 69
    0x14150740742c0211504051542c2d0420320246101c44c0345031341070350042c0310048907840c02690120342c0320052403aa40101402c2c40d800000300a00f11400c02d81032904900d04500c1030380a076035410078403422603081080420010320100010000407203214098104c2c0750080e009517415554800c24a000c9a100d00691000f40d0502c886114540c641900101610410341495030380e1464010719106041c84140101ea008101c00301c0460103c902c50340c40c0d1002000b014008000050f0b21051000c0c10345c0280c410080000d00f4006025030140420305280d049580350f44a50640d9108070140d070389803416403d400425590b8500d000111280c00c10000c200520303108050554a0a0280f404244143c1030340000b0138140c000c03c5404400c1d1561160864502d81191200380c00b410007610490150016045c041e5110f091080084203022080e1034050144241401f140c420341c1e6030314181500ca92000c038000d03041c07e0300060100704c2180100720300c0b9001d003040c0f140d10b500b1944a603280000c0b903c00031819401a446803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 366365800 1250 366364550 366364553
    0x815061207080901110c030d020a1103032a1603030c111204080601050901150c03030908070b010f122001090b0c060f060604080a02010c03050d06030f050114060a2c13 73
    0xf8883e24141e20884030000c6d151002c8a030501e5039900c00c200280840540c001140d5032910b11408020300145040802c1e81d80c1c074100700504403441c40c5a0041c1041040d140c0e030340c800304452504200d501b5907007c0c1c903003e0000b4001ea20140c0040c03c42d1403101090100007180b40d580c0c0d0000340092071a100d44100b8040e00c032030a2180840c03420350305801250103a0030360030051141107016040450164003500e07240074000000d10b022009400c520200802c403003c041042e0041002010509041e80c89000311400e0070303582c90601038111081c84501525550003035042442c10383c80c006480c0d1110f28181008a1250fa031800c0b074008c039500100d070940881d00840c1c2030102e0782c3d02d0ba21449801c84400c440c214281801d080b101610f0350f0351128003c1c144040f80d6800e80406000e482981e4080004030750802065640382000420303014a50022210365203400080411030604400882c024100a00000390321418404541c14011041c02d01d1007280d006200e0607140700c0001015940305010120800c02c40514a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 366366906 1106 366365800 366365803
    0x20d0e281109090f0d0305061513170607030c1e05130f061206170a03120212070914120d030b0a080f0109200108150612070809 56
    0x30204050780e00d000c034031811404c00010684666001c0860100d00303c03001222000d512590b162015400014032001500b0344c500058a003108e1940c1381d1200301100c0008000c4501d456100401b045201541070250000c401c80720f017065060384455061507001340004442c003904001001c02c07600c0505c82d0501e0080c0040c0442000010003d4031090020001c00d407807400004482d0401d1170000d40e40e840c0ca4102c0b0240f207188406018404c85030f9030211411840d110b2554186902440100160b08800c41268001e540c030751142c12080d4541410403c03400d0810001c10700c144205030505071255004603c880050342e480c50002443c0c1005000501d080706207802002040c0b18001c5580d000810540c8a04a1240200c84100d0511074004485e0842900c04c0c00082c002160800882c0c40c0190080d11098096401000681421001400120000801c450880000d80b07040148040d540c070 = true := by decide +kernel

theorem cover : BRFrame.Cov 366187050 366366906 := by
  have h0 := BRFrame.cov_init 366187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 366187050 ≤ n) (h2 : n < 366366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
