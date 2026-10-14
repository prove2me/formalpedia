-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2620
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:15:04.90115+00:00
-- url     : https://prove2.me/submissions/2bcf8f15-642f-46bc-9641-09d39517c5f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 471043165 ≤ n < 471223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 471044415 1250 471043165 471043187
    0xb06210604110a0e0d062909040b0a0504020f06031504291c1e0209090c0f150706060608011e0308040501141b030309011514011817010902010f02030a 66
    0x30811380031940e0420040f4986404050340506014140804905074444001d80c035030f41182c40712004002d020b205d03000d000c0018400e40340144010b552200003000011158009604507200400000c5004030800005c0d9450300150f680031032a000c07a48088046290a12030b11707180f145403134001c030007001c0c281c090344882c400030707140300e6008403441ca0300c24608006001103000039a602101c3e900656941e02202800741c2d540314030490144031603801049603204002001c4c0c8440800034414031050403e401402003c402058605502030000d11070480003495a0007110302074442680e500d00b666151070103212604803619501c104005480d0b4050011030541411981910000c0c04c0041840e4001c0d503081078140b29004212404a250002c1c00605d0500400258080e940d00d1000384403a08140000c8003d0019a11448442807140c94941c042035004d0410002007502c1d905d0810701d00c940d1080055203950b940001d80380d00b6559403c03404210340e001031181f0490700e040c0c40254101110110003034450101c075 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 471045665 1250 471044415 471044417
    0x2071d011e03051b0901050f2413090e0d0807080f1008010f150504020c031b0114040c09060e06090411030102093307170d0b06210604110a 61
    0x400405080180340c281d40800843e0b000044541190321032850078030700c0d0180c80d1a00d10510300a000050f082c90300c00d00a480c5490020942c030310030301c41c1e40c0b40c020050304808203440c0c91050622031510700540076511040149069400031444200b00d103955810001d8403084074051100440a01c0b9445502101095110456068413110b40e00d030311000c4500d42c0c440e030780000640e6003018501c40401c01c542e00403503400d01d0344854280155450b6000c00c01603004141e803049103a4410303c6528a13410b2012102d4181c0d03041880002a01c4040000010f90b03648200c605403603882003800b081181011510902004004a070052070342410078000090703e01d01e020784050400c10b9100c141c0c1659540c00e604903001b0031170050444110300d68074003403081490304140c840e01e8420003c8500820034515002110880e0f07910004140525020b00308250344c9401c60801d00300025590000e600345500c0715401410071140d0720408032580480401603400f04140242089e00680c20441d509481b40c1c40031301650031807842 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 471046915 1250 471045665 471045689
    0x80c03010e0702100204081b04020405010c0b060607080a0503070e040212160201151412030702010c030804050c030102030a09021c12030906020f041203020d020105041e14120a02071d01 81
    0x891600700d04d006100d11243c82031074030000d000100c1c10000680b4485403014236108005150b14442004102d002d01e00c0745034013040c0020160400150116034155000c02d00810460410200303885800b050303040218035601280c40003091040180e002003880c42c42c5003048505518144408007400100320002c1d1448603c2c8100c2c154194109000390001d00c40c64040e6201d503540b5594602c9400c1c01c1400c62000d041c010302c40502d405440c5440402210806601a150204070b05040e503001c45140e600204203491a001f40080000c503a07800b80011400790200b4000071888100c0f500410940d01084a800100b90005032580b6000420850030340040d412035040000d81a680c600309040030b03204038880c044015600241c00b1812030111110380040a019a00301d0341c2410451a059080f5042580e02504074140b08201c0540514032950a4000611603900c2400c0081c120361490701d40450750110388031070500414075802441e030410815008001c010f02c4110654a0403182050382d4006016058500c3d070707 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 471048165 1250 471046915 471046921
    0x306130902100f1b0506071704051213080105010e0103061109010e06091305090f010c170105041d010f050f06010e091f03050303070c1704060e040c0e120f0706080c03010e 75
    0x1024104c044403501c0800b200844103219407811a8880304122134000c0402c409225481319080c60102c401e00c1240d1000c010a01c001d4205081881600a40201d0b80d10b51140b89020400041c04e0158500810006090300300950452801d82d00351007100e0080070101e1400e2101403444d030390081408034640c20607100165116451341c0855103d8000c894030b203040e0ba0400043c002c1d01c080015088030030760003004c002c100041001204030b078111010000c1e603110b08003c1005022038601a8040898580c58078250141004200b12007820b45e51080c5148030013583c3c51041119141ca50b00a0650103c024642840c1c041e1601c00010a4088050180c4540b00821500c070000404020705000140d90040202c84c4c613464008002032103135100c0300045409402103a084054406401c0176501a41c0c600e460b82c540c3c8034002424000200182d0750403000708804500a04003944410703504107442ca1b904000750585c0142c880200346040000d511001c1008280c50030000c50704100b5068034191000c102c00540c00391 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 471049415 1250 471048165 471048167
    0xe0a1107320a21030209150d02041a09010e09100b070f1e0519110904060f020a0e090603032b0605090f07021b030d120915020306130902100f 62
    0x2000d4032032503160754031428880e0750034000c400d881c01500c01e05101c54800303a01c40f845011410b034020380d41400e4010758000080108414000042c1c052000e884500500f010b65441d00c18003462000e0300f00302c40c00900025510780659020350440e0520000f0303502c055203405c11b00b541440401c41407050400141c030115070300741086030889180c2c0e00c10350402d0408200d003c4080526400b038018960440343d41c400c106034204c480828034581d80c210703a0010760094400d94108c0903c00d9000d0010320403103c8940e5076044500140b4940302902c4040307580d90303403825484c50100901003040f0010304058403990060040c0c02e1007910090000c903400a0340d80d40019401881c2c00d051002d80703595000a90301c902e4100420000000300b03120300744540c6144c2c0c201c4582880c80b1210044107001e5140e002d0f0140c00c20bda25950642c003903001140015240030b0001280c20b80381d10b0307110301c8a07005400c0e9445141c0001c14403501c0d15100b480e1056815082c0c00400500c40d50394005250f2109407030a440c14416205c404280203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 471050665 1250 471049415 471049493
    0x907080f270f070e0a090209010e040f0b1f09020405091f030501020a081905040b061e06040e1005011b030c03030902060c0105070f02010b0a090e0c0a0e0a1107 70
    0x24508a400c50341040c4007821203544031100f600404840c04180380c001160710955001e0170140030b8014022440a0f402c0c03400da105e2054000700207803400c40b000466940082d541c0341c00d462080b0280080c00b4402040d204201c150b60f10284d000b50916030061105104698681d50005e400c000026070410100d402c001150824642c00d40c00230701554404650302c490035401801140c400c0050607000d90400d01c0e8400c0e86812540103507806420420388100003200350401c120640c50300d07000b25294400704c0b003e540c0018440e62040c0c100101400d400d000b40f141d910100140840a0442404d00e0100809006c2e0700c080c01000c0c2000c05001c01905404590515010384e10030381109030003a00c226074070074150400d94046d15090b909a80003414200b240c0614078411300c00d0fa00c09003401000c21b600d151038050201c0c0984580e800c90300f0f2500525031003003520340ea05081000149001c242075032007840c0200018003110030703c49103000680410822100040c2c030550790fa10344085490081804031a020b125034500d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 471051915 1250 471050665 471050731
    0x90e070309120203040503120a050d050a0b0604031a0601020d081303120c020a2109030204110f03071d031603060216150b0a120b0c0a0522050907080f 66
    0x142c1e1840341a810450754040010820b81c0e109800b1107180c00d94240038441c4502c180c00c028000500b00340700100e14010340d07401660b001500c1920101d00501c500340003d400341d00c2907200300c0341324051120030782090384443c42d41644044240041d104409100718041d0034620014103112000c0000d00170f03d001c040c002d10031820111402c043c10849903002c5000650b417603010702c2041d5006080d103079540b0a440211071040c07084052039955000c40030310b15803d00015001d43c01f4448580a011b0010100e5001d010f0090f510680b520380d0303a246041c044100803c1000c07100c20100d8001c1d000483d030b502c56201180b400604890380300c10010b075513804080441d00b000520080c0182080b40d20a4690b242000c2070f08849090281224000050b5a03900408070899030030741001030401418000250207042804050441154207041c102d18000082d10603480d91500303081c81c00b02d00b01d2100310500890515440c4180d0107501030405c0c00c61030404071501040000c0003070090070b40303400316040d22004c422a5440048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 471053165 1250 471051915 471051923
    0x5010303091a07210206091204260a060212010f030f021c120906030c1e0f3b040227030a0204020d021902190b1b07030f030516090e070309 61
    0x104c1c201c80c801c00400c400369001c2540f0042c0304103030204500d00008205098591801001c02d450240380503c001d1500350004018103800c1c1021040645d003110500c50105001d124400c016903c000f00414900805810303085002c4211402e07a0034000151854528407030580c04a441f90450103e99007110750325401e80000810b500c41040701c040401da0802140d030156112910140082481c2c00003c0702e01545845552800703503821070011041e14014110940030341c40500d0310311185643c8100741a0b80c01d4100358002c0a1141c0092102c00c3ca0300c0191082a00a000320390551400381c60948002e00419400251189041c0600b50342a095804112102800341e024000b552036452101c01c8000035009000c41e070f00c0030811880803100f4140301186428010104003c680b00b00704c920f40305e040e01031030010203101260410740c1400750407441010140c100c19100303032303103011000c0074003500101078800243c0081800c01240005181d01a0002c41010968088141002c0300d82c2d60a0380840c094900344030b01070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 471054415 1250 471053165 471053183
    0xc070206070b16030b011205090f06010602030a0305150f191505030a06061112090109050a0e0406110f040501050d090f2010080708040c080619060905010303091a07 72
    0x400700403410b510103105081c40030b01c0e00c1c90105001c10a0b400e840c0c20000e4140000d118810502e180c0c00e060380510340022004085030440211026003d180490a811000160f0f0021403102d521540c18094598400105142028101504008501c0c410428106248a410340340100342101240c1940b0780000c0440824200020060b02005801035100740d44140d104c60808001082c0c583c000c29900e40c04800318802003004182102440c1da4a80110900c0340c100710360b502000840d9035850000902070039070650303103141030700b440c0ca0300c3c82c200c45000c00100756443c000d02401d00220301700e005803030450b007003800d00665071280030b801a4010300e01c0540080403909040c81c0582802203070311803041e00480b02040380341e181c640401000400068001c010700010f10788000110038904c10054543c01174850089640903540300c1c40c8050401c581109d030318080e4600d071410702d911010b0724000e040003007103801801c020700d506585000700a88114004c1212013081c80d1803c140400018040740c4041350400a20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 471055665 1250 471054415 471054427
    0xb0f0121061d03180f1804020603071b12021b01050901030209010306050604080a022701090b220f0b01030e300f1803151549030212030c070206 63
    0x40d1003600c04c511818080d00780800700c1c0c4100d08100044c1d800049401c0c00380109940d581c0c0c200203590384000d2080c1e0070451034049640d449120301d10029555031064614030301100b620b1030000e29100000784400641100b030f96086c0da00da6046012185a402c1c00c1c43d015035628480340040e400f500b03032580001e401c050005000107200c040403610071b145034070840d4040f8012101c1141d41e5034105000c0039034040c1d42c1400004102c022829400550001400703400d40c901409807124a901c3d0f8208200002035841d124004404a03548038420b01c0c900300000d0908100c040e560032419a43c59545465200718408001e0400304040007506002c2d08011000300a15500e08180e10f5a04041d0090f1803422900c1083c0b80f01690145400300741e01c85c5070070f03100c84000078075680c0038094042030003a072100640040301c07091440740004452509003164809080301c410003039481000014005903a05045620501e05150b50700020390100b0003a800c002048055030322a1244000010385209071f8400a40c040d2000407a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 471056915 1250 471055665 471055687
    0x8010204060e2d040906020c210f0d0c0309050d0f020c06070b15040b120c0a0501111002091f0c0c0b0c0a150b0d0b0f0121061d03 57
    0x42041d50080e944481488072280140070003200d180d00100e8028801c54429202d6880f4407070000c4814000801c0802c0102c80784d02e5031012a071100c0c1d00206580c02c107040072802c041120210418680803110110301c1c1060118815a10780070f9130100b400c1c4282c076480008080c0303204c4d811040f19160480143c2d43c9040e40036074003500e46000c0c403c440002d40110700f6400003034030303115044ea200c1c1a08600300702d0140d580c15942e1494400415625a03000d80e031441c66a10907101c0c400440c90b18a1044010490b110000301003100b03840c1c590740611b041003001514a1440680402c802c13024000c01c40c405a203441c0d80c2000200009441600c651150070340001900420742c1c42002250214001c0d442d8004c251b4507400e841c0001d01c0b8940d48408113a00c820116400500c6414810f0300e106403250380003402005800000e451400f4100003910044009024401660700052007980181800160f4101040128a41c002244010680035020303d0791640200424a400d400d00c08400550500352030f51a444405 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 471058165 1250 471056915 471056917
    0xb0d051b03011508010f030228090e0703050c0418030c170708030610020a0803130c0b0c0a3e12010507031d0105041115120705270f01081f080102 64
    0x3583c01d000031013400000901c14a0300d1218803e40c0e80141504c2c6804114410083d58045a510b4034071850a6141001030b40418511810130103c0c2032300060082c0600c0c0d4104286031030100c2e02400e105a107080c44004111b550034400740950365040c141b40e0b034044038a043c010401c10000b8040f10510f60001440020055000025441800c00301c0d2114910f0103241412a900d030500c902c010800f44080000c00c002280c8880f40303181c503d10034402441d0031a2205911140d50300070744000074251340070a080c0401c12000180d01c42105807460460b803000303d1400d1980c611a0300b4110307880e0550040d11031a03001900d50814007009000250001d10003410580e000030300a0a65070301004910805a0014800d014107001d43c0340219000340d5007084543d2482d04110140480c0406005030030341c00c0111440180031004010712800d030301e403603c584400c0d01d90b001d11800c089102c00b10031492944d03402890a9070b23a0102150540c0004e29006810340e0310601e81d040e03401c03211520340c404a55099400a06400150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 471059415 1250 471058165 471058199
    0x607050115060f0e01140906090a0806010303021e0a030521070804052e0b0402131d0c030f130206041a0405031b0901030f020303040506030c19090b0d051b0301 70
    0x41e850381d10810fa290030403208401080c0f4064002502d500c40b030701807034800300702501342c4100c01040030386410102c9000408440c0d6540c013201070f640003e03004005240e01400240b243d42c410400c1001c085203d04480ca490710f110034001402d0001c0820036600016021409542c1d10f91441d81416403070800c00e01c00f4000050443c1d080341e8a05c2450812058441c486e030f0510701082d2903590100c01d0000d1206414003400511382c420750060b90a00030035040410820140c00180900110800758001080200000704001088002c6c2400c0030030034080c07451950190154400e4038803030010402c0c0140d1000a40c01c0c0319a5021402c0001c08154a4010041d400024401c4070360880441d905101c00400038860110080520b41d84140c006004101040603c0c480700300c000e1008050760303d0161a2000502c2c250400c0d940000d064202190402e545010840524242c65850070401582d0381f40c030341c4182c0b2034880c2c204070400c01529040440c0305440c0000760b01400300014190261070750b031680e42c00400c0107958 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 471060665 1250 471059415 471059417
    0x60426030918251b0503070b040c150e060313020a030b0c0406080906040209180a0b0c0c010e0109120c02031e0109051e070303110f100c2615060705011506 68
    0x71030707031036900f15a0300b001e20507110b04684506260400c100401070000220140a4581d07002c104443e60000d2a000c2100b0701c1345105600c1f2018881c180b503803001001f00c80d40c1a000502910380142401592404180d0758001d007280c01c06108100588003103045a04140c1c4010b20944031101407000da441c1c03450181c400c0d140641e0301c00703030705a44920700c141e9a6401a5006034101c0e55402c00b0800c5440501c007842921b5807040200c03000d100031507a503048855000c540090590401255071040e2038800c0c041c0c86002340031b0b400284120b0b0304036100c0045080301c004075102440468181c01c0c0840d1014010b081005100009510650707004100d428040e03d0303207110840d014018501a4004160315140303e11502c400381000f046170310709540c1c040d1402c0c00d07000c12845c198414100b90381042c0004101d0720100103188080031900c0c00c071a2201426000c3c43c4080e5440b207120b500803007051401ca07101e0069104c13107203400712024246014041602c52107280c00180c00c41d401c00c00417046100d101d8084038125161 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 471061915 1250 471060665 471060691
    0x121515061e0302070c0302010f1e08060907020114010612090204020304260705030406030203071106041104061406070206070f0203070b03040c06050306180414070f080c060426030918 80
    0x9120202c049100d44900140341050021003440954400c840c0e01ca032070100b5042025100b403001c4260340c412500384030542c00080c1060b04120311410000c10858224506e80020f03c00c540d080307104541c0c0c994050007440e04110158030740100a01141d0007078040150045e000315034a050034204070703002154044442ca00c55411819010789901114201d81003107400102640c00c09060000890182d80302401000411200c101c050301104418809503005a104000300f803c1c110280c1c040c001501c030a58010b04113100709044241641d02c0d0041240d240990440c2e80c65940c00c03451030030b05800e0f61685400f94040c8500d1034003140f0750b100c400c021740c041e40c0103c200d244416034071103044420b0300c0100c2e07109030043c03102d2401100143c0e542d801c094025201d134841842d00e00350030000b03a24001081d80040611b4224000402001a091104045144003070710f09034506030405050745040800402c1601d40b02d4440303105500030240600c250307400c86800600503180c40c00d4411144100e0841034400420804c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 471063165 1250 471061915 471061967
    0x339030c03040612061a03090c0f180a0e060906010305070b0717090d02130f05060307140114090d0309180c0915110f010c140412151506 60
    0x2600d03401010403004500d410b0410000700c1c1d12850840c81c101001d602c650011450712408005400380070f40d82d01000382c0b64a04101680c1c03402403400c5086014011003c140c04207074540300818030106982118454031a1203203003d803030080c1343c5002202180d000c0c5600b4880c6031400810894100c0e4059401c480c1c016132101100d100610504074018140c460321b001d4640c0c02900b010141280d80e600521485501141d500413500d0452a42608101e00d90703900800002d81d402485a2900141c09900420740d1600381280703050300c80480980541030020710034541c0300741d4070900100c48500a024041e1f42c0a06070a01d0060034a041c6401008250104906089178059180c4039084580d14603130303186d00c0b08600e80f0545485104685070900f0802031955040080b1009c00c1004200101030740c4c00000e00c0310b001420081051a03003c080c000701b05401c01042100d40400100c195400390800201d902802c29103c4200c010709510318140d40e011a070031000100d190f04000c4050b0341c82c18506400d80084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 471064415 1250 471063165 471063277
    0xf08150f3f150f07030509210d15030f1e1e0213020a020601210c1206050105060403030c111c0614060102030c100203100b030a0204090615020312070203 67
    0xc281150f002c0c9851401c0c50015121612035084a41c00c80c04040983d111500c05140501030078003903c4400c51203400000381e406880c0f84910813554070449102d82d0b0003e46007543c0d20421a2010100c002e0144200320400050b0004903180d0445040c0d0320030845450000d103600e801466012a541c20b9215080031a29030081c0003081c001c0301c1c0e001585a010b0115030f070070080c1c0f02444135003281c0141300700030b44250480000b40e003c00001f000b43c15941403003d4003a41c5494044140d0b1b0050b042140075250a0100300000380e00042d68500f0700d07610181c6e80c00390710203100114400403c02960418038403000c108001c240111644020300d140d6030b04100030680c2c0c1d981001079949200c2c04500280036404201e80d443c0040c40d60380a541c11122104400d1001c0359a03040481c800c0c3c00a44608200d1940003c0030800362001c0d00c10400107188020b4624501001200e010351640a562114690700310b04900040826100f88101c031002c030a4010110003155140f13801308000075044000602d5030f41d0320328000c4074207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 471065665 1250 471064415 471064453
    0xd020a02180403200115080f16180e031e030708010501080105060d022503090f090b090a0e0c0909030a080f0105090103150b100f08150f3f 61
    0x2035505525540c2c280394030705004c603056200045510002d9540c8540365141d04283c40201001013555000510965400384072840c101240c6045040440860110410203111603a071403000500c0d00c05c0000542c549041203041c00d501c60707071003101c0d00b0445540c400f070b118100c0c2c0401346010f00281c3e40c440c06c0b80e031f803103e0040d103598001703004042e0b0086042c000700c080900035400401d0b45c002c44c01640c40c40d00030700040307030035001c04001e0089012541e0740105000019141055000410340302000340001e06c0360780c011454003000a0704601800d1b40712010050402c004101d020300c2514080c05104541c50304010b50350b1641c001042c220005000c40c0003107101e0300003100506061b01c500808601580c1d05c1e596484a1401c1c1d41091804002d8442c86402d003281e0b6480000603142459484400c951101070034010030356480180480303850585610b0300e144a884040005108100c280ca01415500d1010113690421702284500c4d08602e101c1d02426040c051207520f00600351b40305408a5101550807526002a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 471066915 1250 471065665 471065671
    0x60308070804030614060a0b09180f040201110c1507060b1905040605010c12051b03040e1503030a0207170c06130501020f0d1b0c08030a080609010623070c080d020a0218 74
    0x110501120003423040c85080e0004169240b0001c20140f44080074a008e00000341003115029424034400042000390758108c01400b41017002d983c0a001c50b44448400104d106000c0c1070088186240071883c68208006507203c64600040100640c4034401c2c0034202070003081311030181300c3c001c6003000c4d4001602d50242d141c0104041e808202c00044189190040b42d46800c909028442d0072604450300c42018000c0c0010005005038101d10140c52400c80604201c00000d0500140aa030003003082401240e400310300741c016100c0e40300011103031001b41212540307021491440182d2000d0001500644803000100d02d20480b07000303800350b500c2120444102500c0c3c0e02450011070201e200c0306058150704107100c01504040b403080c00c1500c8050303240c10090386560048990840840e001a051003d0f91034500d04850062802d0706c1c003074912420b00602c0100202c4203214003280303030b8800320b40c881c100a8001d551101030000c1e001215100030303000000035a180c150400076802403201c501445002c030300003d000c501c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 471068165 1250 471066915 471066919
    0x103060321020f0a0305070f06021201180c0c05031207050d0e03070605010807180c09030b04060f11091e04060b1c0b060403110907020c0405100602070506030906160306030807080403061406 83
    0x20818215494140340303000048411510948d080142c892f01075041100c050190201203154400b203504003800c40c0c21940c8840c500d100780000c5071051400100004211103582c007500b840c0742c00700d0f102c60380141c599001d02c00309042000d0605000740c2d88140004040d0074164020b090500032030f40d80e54201d507100c3c90240280b80540030200c88401000b0140d400c000041c0c062803a142001c0c030780d41d80312285100341c01d0350308a80d042d884000c4010303041d00034020051080c21001c1172031310304089003000460150b420050280b214010007042c0c3c0700c581d07035503001c0740003081820145582d40c8071030403944030074500301910a04407500c0d001400c44030342086c1c81550240c0b580b10111000c0e5281e0182001800000100740e034046100e110891007140d200c50041500880b0494444624181030030b60284c240300740713a004140102c0d414000c00c804a8800250396800036002c521803410340d005210120060070842e0000b07040701c00002034210070411319400800840340501002c10421442c02c644038801203007030310156 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 471069415 1250 471068165 471068167
    0xa1a090307091a010c05150408070605091b040b0d0b070c150c0507060f02070c0f050a0819140f1b0405060d05060103060c030915061d0915060103060321020f0a0305 72
    0x1007541d50240f0306491210780140100d6280880c0051007c521480480d07042316000701c0800c100c0200007042c0030f401d0300300751214050099480d040c00240d603a05001808240300300d440d010300350003a4590b4080c01c203000c2d40040301045503280c03505014024a1070301e04120340b16500343e51140004400c0c2c0c403840a41003500c1d660b0500d81491921094080c050080c4c0c00b012441d4208200710000d0800b105900080c04034046071544c0d146000200480705c0d101e03030320018260f040320003601d03190145829072080482d8045038984103a040c02c81c10030b20f40440c08030218220310070f000d200c070024440d45401b0049441d0841d4240200d9441e034040c0040d805800030001c200d070b4840c000500008140750006010070318145000070b02c0c0310340394542c0080010380380d542da0602c0fa5100c4040c80441d11a10041e00900400d44c12601c0341c6c00c1c4401647e07603a014855001d9424160800032600c01e0784641c101000a5070403001070b205115901118052038001888050094491034503241482100070500c23190031609500d82d6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 471070665 1250 471069415 471069461
    0xb0904051b0d0b0306010b0421080c0a0b011406070317070e04060906030506010b031311150703020606030c010f1223130b011a0901030b0a1a09030709 66
    0x10101901000d4680008100e8441104a0782444a0041c080400001001041c0c1e030410030189814010306800001062604200a01c05815040b0711a00d41700030302c4070010305140761401e004680c0d0042e400d8015060144203800401c0c4100744040034140d55158800e04010030b001030821015100f48800180455421003050700811040c04c010340d4090b205080100c00350350140c0000d421500780d0341015081c0352307840c242441030207400c000a41c050320041c591146035003010900744030034082504000300502e01d14100603d040d144d55100c034294104124860362940f000b490080e445450458895000e4130800002041c258423880d06030032000b1443d107070709440070b41c2041c8002c058900c40c41d12419801d030340750180403882055902d4510940041000a600d0030322440c1100301c00c9410781c8224840308002c0042034880041d00d00711028010242800182040f032080400c000200c10740c4084060390f002c142c1041c1c419013240c0104504e120840a0b60b80050300c2c4c0501d40d08070340440c08a0300c964200d00d004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 471071915 1250 471070665 471070669
    0x8040807050a02061611060a1e09030605130201170705042306030f160203040303020318010e12010204052704110d0501050a020403031b030e0118090e0f06010608010b09 74
    0x410280e8010020b80d0440103840e004603419920000030140d40300d12420298041c400ea010031600b202800316000f07481c160301c40a005150080c094018015a81c01d0651295207034010b41a8070010f40e4002410700a0b80341414845120110306201a801b10741d58600e911000c0c06000e020b91b100324416151241414107100d008001a04580c07008d800d041c10f00c019041860b641c18010354450421808480420710f4064040821041c0d607a00c180f0540d40f0a100c1400041d80100c26a442040c1c0c1003c84500c804c4114012121032819084950704807401c0e02d14542d86c414190001c00580d001030714002198000c03e000d00c5240031095040c0416401003c010600188a800382e01c202100300420b5411204d9507500c910342154030584a44580941c000742c2081010f230000a1032580602c010509584c008070b649000e010b00b000c82d401c6504022034201441d4100041403a2000980b4450f01d0411074000b952400301e64031000a00c40900e28440c05000040c805c5c03050701614140c81e00c0400e0241410b55101c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 471073165 1250 471071915 471071917
    0x2010815010801031e1b1e06080f15132403050c040e1e06060108060d051005070201060b071a280b060403060c210608121305060a0918020307080408 65
    0x8003114488004009000206003484d8901b5a60488240e0001c0840e00d03140800c03005d015802d40d0102004410380003005100d4100722020707401290000c00c05915a241610501c5c1c00752400701c045d510035044044941c1d81c45079984003000a03655010303200444000c42c4242c001c00c04651100510b9070707120342d03109156030910303810001e076540c1d0a1080b0b8500680c94440c46040d2042241110bc0d1a4409005c0042669218007020b41085050392034071581003840d142d598503200c0044921007441d446502080c4058800d602010003041c1c54170700b0b02d07240c1a181ca00441c0400350342d680c468800d1301c01c40204002802281e540c00c40040717a442882100100c02c2c480c10040d1000314541e95000c1820b00000000c150180607001100308140d0381e104001c0006101c142e210070007246400190791502409210440c40004c084008019180105440e010165000d0742210a260000c2c0d8010382c1c04100014059001040403003074525208103807415125440390101280002c0721a500022001000310340421601b00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 471074415 1250 471073165 471073193
    0x2010c0515180c18010e090c12010f0f06051c060e060a05040311010b01020613020a150c140111040902030604020c0f03130609050a0504230c070201081501080103 71
    0x5035840c0c025155104203400900315400c0000c02c2d2107031824003a422041c4860400e10400310784074a100e81d0114501c0c5000041400784c400d20b135826401203030814008000b01403003914020b01a005032204144403501030520700721101135103810b01a41440d80c220030300510302521009070451760400b4803100501151041c8a80641c0c1c02503468407840d082c03403010b010140c8201401c400100c6c05080901c0d0041c2440c440985040013070f4945502c2c0203160781e010031916000f4078840055a4000d800d40001103070300b03132258041d0381c000e18040b40e409041600700c0b001101e5603010780d019101202000d4056400e8036480003c04050207420041070011816030340c060350b000791001c1d00060505148103041840c0c000c54034a10901c581c00850016628a101010766001d0842e52038019401b92816003c0b41d00d208513400b03214403650310b81858200000e10508400010014228015504e0038412020344943d406020141d00007585a000951809020f01209400200c1a981e071300c110380c40c54445400100042e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 471075665 1250 471074415 471074423
    0x20906070c08071809051b030f010203010801090515070503011203030603140703020a0b04051302030a090f030906180509041401020d02210a05011208090109052d190302010c 76
    0x50056001040203000001c0251501d00d005003802400c0c080c00c1c0000e005030030a11000a420250304000143c0003107111011010b0002041c0d50150340c4000003400d11040350541c510941c408800010701ca101500529200340c007540c15100c3c11401c8200c9030326030100848480340031400820040242c164000849030042e0302034500014400e03201c5c8e65881c01003600c062207031810b6010001c24019854190301b0580184940e00e85030745003901c0e100c04100300ba101c5003000c400896020000892b0740321141c000b403a07256800400f002c80d41031a0310300549004424050720b400607001c031142c803002148040a890035030314000d140620550780e5603148107030b00480581c8603c01c0e5400b4055100002800d0010f002d140810541c0c0801207211135801900b0182c00030507800c00c1c40d080c50010000304000b080c08034400c2d60405941030381c0d451400700686640740242c0c4050f400c078042d0345588080c45000c15a1303400c000380b0024038030103480c074103c00c008100d0000c1c01884040d81d440a010001980034029241c002c1e446 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 471076915 1250 471075665 471075667
    0xf04030c15050106030b01020c030c0a051c0c03081207020102070c1509320f09070c0501090c0e060906010906022509090503070209011509050928150522020906 70
    0x80100d1840542d88281c0c48403010948806001105603010f0009610340340041e0020004035110f900003d40000701c80c40b8041c01882c0740071041103030110703c3c0c20784002c490b044040e000c40c15942e0300d01400700e40c2c046180041882114004140c50300c0c03040c02112a665081a03000049a040c094007100010203080c4070401e214041d00300103203a01158980b0401d140c910b1a1104014070494060a40f444000414900c1451045491070059440c040e9036030b04042d441c68103011840840c40c015005160035080a001c0c1c0d4451600010307805070b680300b83c5c1c1c41003806440700c803101d840c0c41c0019254004940628009030f0000110480081c0c01106031060240042d680b18100360340d50b41c1408210703401c0ca80281d5183e00006400c5007075050a0036294010a4040d4042404161046004001c038065008840c820302440b400b051444000c06120034106201c0001701c11428042c8150304020407200d80e00c0d00c44601d0413000000d00b481e0500034030707900c0a03140150107400111040f800c4020760001b4201c03070740044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 471078165 1250 471076915 471076943
    0x3040b0a050d060f060e03060f13080f0304050304180b151602090103050c03070605250c0b030a050f01050d0206090f0307080601120512070f03030504020301061208040f0e0f04030c 79
    0x2c680110750003002c48031446580c0384e08001004102c40148080c03d40280d0069060000000b81200034640c0403d040c18910700407003d84c0703040f02c104e10802e0b500041e055008818042030100c084005d10803903021003440700c90300c1c1302c2d1002e00e802da6003e1841560700455035141c190402210500801c2c160b80101c2980c1941465035001a81403c82a08159081c0e4804a5211203d04040000707078050f0202e810442c1c181031010400303000301c2c03260f6140c691190002640060402074698012000303881c210f4012506c07450312000f980c0040038101c27003506803074800a0000801d81081e801c4115250b8010303002519180d4814207101c44141030303600b0301d6018868000b0001d0030b80d02c00e00c5803a0184c42d00400038030946001d030400b1854401100000102300c05c1c1040490006100c01c2d040410103907060402141e199240d000082c01000ca50b0701500007070313411000040c208614000100103072070301d821041006580350070110a030a0401c440740341c03c0c3c81b040700c00700340464041c40541d5251885001c41401c500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 471079415 1250 471078165 471078187
    0x3030506060904021605060f04050717012003060a0f0b0a0804140d0203071101030612020918060108030a0207080a022823010f020d081801240303140c03040b0a05 71
    0x107441165802001500d9159840070444103001f501d0300000480c05e15601c9043c5500e5981e220b104903c5500202603510000000350f41081d044948018000407202c26160310749030022400354002c8139454442c4405c20800704103005440e0004007503075101039096040004255040c0c5e42000081c10580e540f0315100e4500d00e0804040101e03c00341c12460780591340304c5002d4030b88100d80c2d903514154241418100030080c40b00d882040c01c102600e80e0100c509910f580c90b881560020110b1304488030b501d60003404004150707110008020b04080010390308540d1056503502345982c4a29100c04000c4d4000d140d0203c0300d09102100707150000f407807484150b080e60159a101001904042a55030000c170501828030b0045170f6811040310403130340411340058600042c0301301c0f0052041200502d21402040c05040101400000354005e0115009441305191030a652148038105903210f03100031000103036424250358a58500c1c0d800d9400c450040c00003035040c90308280d49440c00307821405420080240c140a22403140c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 471080665 1250 471079415 471079417
    0x90305070510110a0602040512060105030a02010f030213030c290306060724090b091f0c022112060a08030901050702060f07060509010513020303090f0a030c082b0206040303050606090402 82
    0x203601c42c410041c2d41f18545400e1084c1004040102d44150b0401c0f001040f1070745001c5400e200603a030919002555400b401400e80090065103007240c0301025418021040205030049242a07500c10f040b0220a5400d41c08804441e0640c2540c0d0300503290148041b84150070020701420055204602c40c8900015240418a201a035149100f4541d0b0b201c41c1341c4801c0c03203141c0c2802608910020013030000000e80d01844500010f0308030701d0b40340d200d0b6503003200d40c0700c0e85c824449818210700024003002c42150282c140070940c6c10004541442c5800711000c105540380980a89046840b40005181010b460070015a078580060f10140d821003000c004803560340c0100c1c8010044a4841d042c0081c140c18220326039402c480c00140803551104020b07074400007590300007055030700054040395468003440070500440c202e2078055100815280c0c01d0a4003003030410b000329880200074403a80c007945121140c540340d407090610000c45040560040004500400e200b0703048030303a001c0800b070034952030000360380003050413 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 471081915 1250 471080665 471080683
    0x3070e09010b0406091811190e0406060602190b0702011d0114060f15071110020a1709090a020a03111305130b0303040b1b0703060c080709030507051011 67
    0xc59640e0400d081031440e040c4240c10192100900c10002560a1800c0c552071640c0e41801424110503c841c80117103070744082e52000b112051407000710f0ba241d44c1d450150400c0304151011203441d42001e0010494601c0001c1c03c840724800c404522451040d15103c41d02c03203100c058402401c5549851290b540140080300070a0030b1580d0400000b0358241218000c13044c034002404c2c00340704030035148844440382d50340c0e143d050508120315186a61030306149480d102130707580f01c81b40e13980010b51160191402600440c141c4c81c5540681aa01000000c0808901c414410102c5680c0d1100006002c614600301c164050700500c03401d81800100b003d07441c0d45100c100e4000c00c1d41907031a040c0c10345050085040080c5141010383d900102070058140803000030392203000d41d0180c4c0346101d0780440c4c85880c9442841c22080301040210a03165280d4603410701c1c8000d0040300c0440d001140220340812071592050120038200d07600600940b007121300b00001c1107d105400340e80d560070440c041c1c1800304403840a02080107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 471083165 1250 471081915 471081931
    0x80c04030b160221040611100c11070902070b07050904090c0b1b01060518040c090207120306050612011a040f090204060906140406051606020a0f020c030a050a020f03070e 75
    0x1d14204044000346003d0a110300456115900d00c0d002c6141144403080d101030386c0c1c450401104443c80c0ea4900b038501802c0c0b41821043c0c0d820013505090898004610401d130702461021740b50300340d80721100d0030203921400c80700500007d010b800044d1228444c0010f804100401000802c034511692199420440c03a0340200403100c8001840814442c0990708442c42010044001d0200503e00310004855500d40e603101c400801c1311000003010400c004040788040c3c1040326045481754250b042400d40501100c0303034080071078038202001c9200c0c94420161094042161010500383e030074105555a1080460b0244401c3c400500c400b00724090f10281303509c040c0c603440c03400507200d0b4a13000e0b0040c400d041e03d6002c50148060444004005031a003400c48040d100340d0305041c1e54603551980c41410b504a4003901800e020301c041100b48003968441000405a051542250780d17003502c0004040d16080c0c0326000500c41d078805942c2000504183c03070901100403006040c0c41c100d030343d9941591501c44040324130b06 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 471084415 1250 471083165 471083191
    0x30312092a1710150e0108030a03290d150f02090306010506031003110f040e0a0b071b02010e030309030105130b07031a010e1516030e03120307080c04030b 68
    0x600280e10050300720300914036031002c001000c080c00b1285495402d41042c0307044858641c0d1409201070718800304100200805407140311650303514455240c890300014042400681428a03408424004540940040c4a01c04419414851440400a4607212003c04403403c0e42c1c004003810007582c0511034100f50070800f11025a40c0c80c440310826080c464143c01952040c84144140f1400982c004c65290a807603001300c5c080008800c850008928002009074a0f502604184c81e21070180c4011907181c0b29244611f0340d050181e02c0704001910704c4121506100ca0035003684503241c0242d8400d91208812a0f4040d054134074000b800f1011070309681c800c60316034684180f580700d201d08002c0d4901905034400514502003150048691450386c5210340513070154104280208001350300d0b41d030010a000c50b03001c5c100c440e55072507036810450b019041039410f060f80415441d091020a60134003090a085184145801030302e103a844402c10b841c810805060780c402c01000b03000c04400940c01d0000e00c2c4c00740c030f000e20b00d403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 471085665 1250 471084415 471084473
    0x61309020415050301050c030106140309070e01090204031101020d050f0724020c060f06060304060b12010c23040b070b040f060c021b040c02060126060a051803070c03031209 76
    0x7243c25108040e00106100340d0408c010440c8550003603e41071000b40041d4841c2d60b81e03c54401e541d01c1c3c841c40303801c0313582c179030260314000150000143d0051040700d00c204079a0001a0b150001aa1200c030390540e80b1000c184204407070042020084014100c2510503000030341c4203541d1142013564030b2010752030405035070b500196550100d401001600e901450039654100e403441c007030000c02c01c01e002c0900300418503074589600400a51343c01c0d42c4e10150080d0007000700561035403440014030300702c0d160782c1c0c0c8441010038140c81400641c0d5442261b0a880c1c0e00c1e1a56031606034690f0398040032010041c020b43c0d01858085210001075407a004400c0800b00301d034000c25280072103042840c0d07a40d2004090740c0c403807850a040002d80d40d03000b01d50b690441e10031480380c0b020f180d0321007290007010b000b080d50407006004400410000501c0d0b07a12803401040c00da5140980003c0064507150b0324400c502c1c028191000d034000400c006442040008601034480e00c000c1082d0b602965080501c410700a105001d6090300682d03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 471086915 1250 471085665 471085669
    0x120f0607052a01020d291c0f030903020a14010503150d02030d120606030b0d1202033906010b12070c06050114040b06160609080c0d08180c010806130902041505 70
    0xa502e5004c14003070082282900d0003020700018011141001e0040410420700000c0b0088081e41f90344058110064115813040c030f10740181682143c0c00101c0c0301c2c091000000c10044050701c4602d14072a4185c45961541d205c800c1c01d19801d81c0080c51495024180c1d00e40c02006840601101400c01f0300e1341c4844040700c24566070741040c0d440310b4101c031081520302401c68669503a41b00014161942012042401000080703007242184180130705030800d2402e681100144010030105040c00c180304011481050318400180c986400c001e03c42c0340b1001000380440881070411103141c50300302806042418212519981c1e04007a0351090780111241585a8a801802e04160050300c0c400482220900d103018005220701a5840040f08060146555403958008000c0b030002117401d4007040d0011250b10103c5628020320090044400c2d03012880d05040440148000060100c1d5480058568401c0e65039824180040c0082091341810a151141c02d41030140e11a8401e01c605d03280c9814014038010709003c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 471088165 1250 471086915 471086921
    0x30c06081509150f0406030206041814070915021609050f0603071a09040b0603010f17030a0804030507060f060e011a04080607050f071a0402120f0607052a01020d 71
    0x10081e40241080810440140744480303041e03002070302c2200d038408080e4000000c04c004214030f400082d00716000050120358a8001c2d90350612000014400340903490f4044031282c1150800c4d541d90003c10300080c030911000510341c42c020482c91191048070205a040505084420742e9130b88010001607541c01401002800e01e515290b02500980091290a01d40302841d074481515100d43c25105201190101d01c1d0343c1c40350408032000703134001c00941d140c0d44c54000c202c452411741d100700c0030030b401c000d482c080d00c842010058520b0320b81e040c2c4a0f01c50541c0c46840558255106410455859503a000745010f4190725101e80c2010b44810f1200c01199810300421203070b11141140050312103407040c402088106400940158481e2141c80d1480c0c80e60f0790354003814994007610400501411407445c00e0501c010f111211a40300d0380c000c481c032462010340c0180d00380d111688203048482c3c0c0c0d00300d000054012130080000780740c01d07a403000c2d094a219014000a803104107640c00645040d07500000d80d0355007407840380 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 471089415 1250 471088165 471088201
    0x601120f1b0507050d11070807080606032103070e010c0203010e0a02010e0103090827130c0810050303071716050c040c171f050a2402190b060406030c0608 68
    0x104120f860210701d610b0701c559480300383e40041c0400c121480034002c50f51081c0540341c020171100c4101c0c5e0741c00ba20b5501030380d00c0709000c4441901901c1507456103600c000340144000c6011002c15200361640d00c0d050400c0700c0300e03220042c219040c0000c403608400141c1382480b0f0a2144c01e0b02d00f001e0580c2c4920b41c40014084043e05216030304150404524002241059045071101200f0a24840e0801e281008886038114103611940c0d2203030403481a451a05925000540c1d403541513550039413665602c1c005038404034414011281c0642c0188540f00006031148209201701011084141c200b0840101540310740d11511800c507201d0700300000c0b080e590304003800350004416550422000c4090f01400f5400ea5060040034a2100c5942e0f08900d10044505a0300d80d02030100a020006099160300a910f00034a64a4652203601000640400203e101090002200d001581040001c810a84540c0304070b0101801880e8461759420002002605105d690002407202d03840d502150310b41442e113036a242c0801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 471090665 1250 471089415 471089417
    0xb04020117060310090510020f0a02060c04060e09071106070309212a0b0a051f05030607140903010504050d08070305041101121805031903140408030601120f1b 70
    0x801c0600446607400300e52502a00f10b8101c00007242071342404d00303528080f410004024038520019946400303889060007040410700c40e4007141c6042d254111058a513101c2c5203d41c1c8005003400004a816142110145412507210300c0c0c20300404076003440690030b00200391400c001296a40000398108804641046c4d4500c540301100808101a1130b0b000d80906074001740c2004444420308030f80315465020000300e0029422414074441c5141141c8103e004020665030341d03401c648144c49140c010303202c0d4074007041a00c0d000340203844661983c010039541070344800c42032911103801707202e45030719500c09100b2640b04a0185004048284041002074290400500700350205810076042201040608011103403202c0c003842e00f1504808490340034002400040a0140c4102011100384140000000541150829501c1c80d1984084514081d0b044030010070300800310f01506000603000c2520200075540c064410b04010b01070185046000c0100c4400f20040310007d60740e844207030000e140c0c400003414490f10f5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 471091915 1250 471090665 471090707
    0x30b0a0f0b03040305031f090515040c020d050322060b040b09010303051e0d0c0c0b09030a080103060b030118031211160b04020126090606010315090c02190b040201 72
    0xc0038a145402e120041c0080c0a204e0004040b0b4080301d5014001d0385111400f00fa0480d40c10b460b00c1c042405402c00f95100f5072a502c8409117000145018840d10012808903001810868103a400544043d00000c1c8100121a10182680302d000341c3c000f24620745600c288400940b5022200c00c1004840d289104a8000c05101e0014070010f9000700445544669a00e0300b45944d20841c070590000344980000014800d040030b410718003468000c098492502d10400f0b10900540d50840036a689014169080c8001151031004002003109036020066089000d400451002003500b4984030300d10b03035000304500007081c001d000a80b45002d84141e15031000c210120a20303200d400f10881182240e0b00345c0c060865012000440e04582c0656403032600b00040c40418102c81090b848240712480701180c005c5003c4c000c110000311558070030321410001d64010200c0d030481c2420301c03410000521007015540190310501680151151241e1780c2802c0e02842aa41403501d4034041c40010101e03881c124009496100c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 471093165 1250 471091915 471091919
    0x9080d02030d050a020a122004030b15040b03071710110a090b120a0e1005090a1505010506041208130b0703020c01020105040b060d1a0a02120f04080a050a1e030b0a0f 73
    0x1502604200c80b600c030500c0003158620f0b0710012548c814040325241c1030a15000a400000c00c00c9071106940304d03c510340d0010f00c0d40e08104080c0400e07660300002c0558543c021400034404d9049024201c100c2e90016400c0f102080d1401103600d0441b00d20310700400c3c00c09404a5918002580b001d4048060002170740d081741403104603144640e000d50060003d4122036283ca1003007041c61400c01c01880704c030b40c00034003e008908008000907103c601c40d01050361012941003404040d080300e07019880c101c0780d002c0c0006203013510b001900036110b01da44c0703011203104408100700c402140031280b010300038005941e54aa0364104602c1e029182007807600640e03040d641020100400318502d5056103a00c03020555403250f60f001e0501e48104078420740c1801461180c4680140800c4d40c0b41da0380608190000c07080b03020299112003000004009044034010301c500c10400a14034030a114802411003808035003410f09071820210303480307110600d02ca0203600c0000d0340c0f42030b09111860701a9685000703101e0240428404c034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 471094415 1250 471093165 471093167
    0x501051f0e0a05070216062003030f070c08070609030806041b2f070e01030209090a0809040b0d15091b180b030307020901090c030507050a0203090904020109080d02030d050a020a 78
    0xc80002c220307a4446a40f580007450142c024060080342900c91200f01084a0302c540024040107400c502641001c0d04046000b0440c41000049074040c821080d100b03100395844100403507079808640c0088078955418050200001c0e814040c0d000d15500c03a86484044c0d280c444244400c4078040710040710310112259000c040a504000b0701c4140c040c1d42402d500148074901d280c00318800150504c400d4074415403500140355045161054103980c400c4072400d0541d140e8a07801962000f690704041c1580000b046210040e1030107902500303441001400e1684411015103401424915007100ca41541d91906d100500308025200c140d4a1000a0f03400d20304000d06001a40e1407240c481113940448035034941c0e89203003a030350070000d4405855000b40000030a6854205606c060407406654501090030a000305000901a200341c40315036040d540110706000241c410040d4000014100b68180401410041402c000034070032500f0320080c40c1c00030350340c800c400d04022045440c004c0c0f115213403502c10b001c1001c481e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 471095665 1250 471094415 471094439
    0x903150e0c010813110103060b0c0708100b1813020619080106020d021005090f0102040f081005130204020a140f040812030f04150e1609050604200a050f070501051f 72
    0x51074110008004c9170100ca00160014410ba42007042e4489003c100400303074181c0014643d054808003000d903400c44841c40b060b502501c08032034920742c1c000445201440d54004111003d03900105c00300030758280e04815000710300c1603407003685468110303151030842c081015080364290740105101e10040c00d09462020000352210f200c008912542c07610303035001c207240c00c10411014880004c1d5900031991680c1e0350001d281d041007144070783d003554000c40050a694000511915114001c5001d0f5910201d10341c3e400c00000358065581c410510a600400801c202c078107030301800c0c02d1407850b070905540e18101055140b91496256003500120b0041003046a4400802c50301c0d0340007580558150510240aaa101c0182a100948014034491418664180c02c140e103c60002c0b00c036418800c21080c3c840c2e500b0f200079240c0c2c00b0074800c400801c01c0000d0141c00e82602c002c0110030503c4c90518280010185055000da120706000c0e103081c2c0d1102e040c40b404a455011441c00c0002c002a00351030030340751210425034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 471096915 1250 471095665 471095701
    0x7030b011b0b070e030c03190c0801020c1b0d1506091508030906280f030b06030610110106090203090309010305010501020f06070e0604030b0f0108100603030203190903150e0c0108 79
    0x10000d802c1044c040585042060014042d00201520100c1115000c0220003441201058859460581000928400601c00c4400d80c60103800600100c0b140c0c143da0b01e07070038130141815070341091b641c400c0c0101280400d50b02080980d8040d4001c500d00b4078042241080d11000006501c81a50804d42004000400000c42c1c4c5d40800582d800398813003140b00c400c24513a0000110b141401030340c000c3d1600d0001d50208080b08600d985403410410851000c0902a00d408100c0e41c0c10781010302920b285058500580c4e491008010400010840540310b1207038600340d80059520004c190b001041d52550b03581c26000789800741000b0310042c24080ba8a020300c0343d0340c01c006840c0b41c3c00d0145c5006040490b40f0380000303d401a41d0000c07060030342d07400c081041000340e150034403c00722207003d04206011000d4290140000b2250103034011030401c05c1d0b0742c98480e0301075607614a210038000150000000174580c10304115000c0211180019a00c0040b00d80ba4240001079002504108000d01004036041c000d003003540c0d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 471098165 1250 471096915 471096917
    0x2710050102012007140705100201050405010f0621110a1202040b10080103060b0f0913060e030a0c0602030c04030c0b0406020615090a051e012c0103110d110907030b011b0b07 76
    0x17194441d044122400c00d916030f00540d8100c41c1c0c2c0420f25510b5901500b1460080740b0400c02080610103030000720341103c05c18003031b01d80014640c503001d034a0100300030b2205290381d0140c071840b954059030100144501c2c00a43c4041d814600035100074056107040d11501500d4042a1004840d03810708041c0104000030500004201c0c0b5a2020040815118052618082c0c6400707400e030704481c20f2409000001c0d42d900e40048410b13a08200100c0744003103011003503c1080b0040d072107018001d0030642d11540a03410040401c0005402070000101080d15280d01c1c00042403841106036869042c03260090401c1c0004000401500340d01c03000c100c0c4e41d200c10446e55400750b45105c00040c540c8928001c000420000e201031907488604c0c000103e02c655005115583e19922541c9890a140400c464410b801c0d201b4030015010350076200294403d802e110f900e100c14144102000020300d03550b900003400b440c000340d07407180c0045d82da15101e50f440c1d40c10415002c1c0300944207000a044290b10364a4010407000201004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 471099415 1250 471098165 471098183
    0x50a0b101b060f02071b0819050a0210030c020d143004150c180603090201050408030307080a0b060c122203060b01020d0810052710050102012007 64
    0x6404200140740801d0100d42c4404184100e6070866100c101035089900c0540c0c1c5030014403540d015041e04004841c0c02c96000c00c019000512074100c2d8050034a04102c419185030141641c00760044e030316003a1855078865192400503200c0c2c4800720083c42c21051000001c10f02040902c0002c94401100a80d41c0c500f6103161201c03040c2c2c1e400a441010700c00740d41c040c0d803a00d09080c01803208103c1108040b0302000f0409404000d125540c100807604031202d8040920441184c05080c000c040c400d801820995006040480c42d081e60b4080252550380100d8140001840c030000f881f96480b213030300410a49010449a05003841c03045040035403241501e0009940f4000700040381011002c00c800e03800d070300d150311a109046a5580f42002806482400385490040c003c1c3e01030f031585280581e072104d029040b17401d10105075134101070501c01800c10706c80701030103030140c45008000b11000030307000c40340310b18441103044840703a241c2000a820740f40034001d4040c12030104aa14203615001905450300315401c45054 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 471100665 1250 471099415 471099437
    0x23030304020915031c030c030b090606130503030f03070206070503040819031b030f1401150c030512130506010515311d060906010f050c010b031f050a0b10 68
    0x50011100305220a82c260144140350740c00350038550010043e107060746d1010b200c154014803085080b1601c000015038802c5110001c190305081c040040c0ca4080741d40b003150100030380c44078006407441e004480400448000082000f456130341c144012034200e4014180f141c01c508081c1d80306034050241c00c02005000400c151501e5041c0d1180d000b90003581440045000200121000100070341002443c5159590410051102c90b2484d15241c50480303034100c07488020002ca04000701e4681c1c3c042d80098080100c00d01102e1414000231a00794010681100c103200065210b01d4850b0030800140c0c009441405c00000e000d0314900040c1c02c076030101104400c0140c6000184001813184c507501c04000c0f140301c00c0d0300c0004c40c0f101c030822a101c5420700d4411003800d0a6881104101c003400003151024005552891506002c03406800070f0030070f0740b203854004180c210703500011a2800d44801c0a6910340c194500c070b4000c05041e1031040f00d800c116140d1003401602030000209a2000b107010100c42085810907079 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 471101915 1250 471100665 471100681
    0x2010f0e041401080f0705030a020a030201050307050702040204090203010501120e030d1d06040c17010603020612331302210910140402120c030a1103010b120a230303040209 76
    0x1002e4901010610b002d007940c4a0250581e85c5100101c2c4901520030501c0110380b80c038001501c801019401002010201c2c00d45c0d00450b815003001d0258000e10005020040043e5940d0000c0c0c000390008900041c0c6035072615000500105020150705000c1d0b10380340d01c0d41d1003a0030100c00c5513070302c0310b0042011410f04042c0501d0146000c98600c111498002e11050208220b400740e0940c4c22540e0500715003c00c100c41440150885000e0310009500080c01c00c40f065904e502510442c0d804036580d60229000c1401800c041c0c0c80b40c801084c0402c0d10200c880c8100007074941406c400104207c03401085007810f11401c00540558640013003642c1c41200f040029095042c104100f0a00503400b6205002480034103600c40c5070f00100b0b0350206d101c1d440030f0307071580c003002000158112001c000a00504600800362100b2a008209000041e059501c65410f080a42c441c000b20700440340f00040241440c00150420542040c24110070308082d80c092810302c0b240c9034000060b20741241c1c0458010026482c1c00d46 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 471103165 1250 471101915 471101921
    0x15111309150305100c020d0f020303160c14060a05010b040e040b04080c16060f030c050d0b06090a0602160b030f16020313030803040c0605090d110616080409060b0702010f0e04 77
    0x48020304a204e042202c076003641c1140c020446005150302181d0385002c0103c425181a100440118016803080c800a00703e40c0302c071031100000090030b00303014402d100300782c0350455071a198094030903099001d0b0301801580b141ca44541e070300401c01c1c2c3c0c103031500309401c0100302448010003801c050442c0315410045820b020010003111009070308541268400c0101da454555000050710413080420341844854000038046e0140e0343c40c2260560f10b00e442c280740790302c050b0001d090f00180180c02050a0220520a40301d00d1050405403801d034008058044031100321040d4010950003040c80f001c014428040c49034100000c10750448064504000d424052000483ca18042c29100d262030302e003421000418030000e800110300490261220005064650100392a10321441c043c458000d086840c0c0680481c80b40d02031120103c400070030685c134141d11124000240350303c501040e18800000601000342156034810b880081152210340d0382001c8103500040d0881001c10b22030020f1000f000c15100c03450b40d03030358 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 471104415 1250 471103165 471103169
    0x90411040e010f080705060f220e0c0c010f0902030c01050d09020a031a0a051b090a08101e06050f060c191101030f05010503030f071b031511130915 65
    0x1602400300c5603520781103e001c00241d4828007415000b24500480c05040100403141088031072203455181030100c3d22403c3c07110100720344e156501490500c010910b44800f609040c0500050103000d070f210300d402c0401508564080f100f8034002843e1500103001070301c0100702900392030800d0912546550305805140054002184029406443c141010033005183d034400881c0704400c074007141c82503803284900b0301290782c25070309122800300c0098481c140350f619400901c1300e0100035184a81c140d0780d40c1c804a05d0210150034a40c1d109456020011440c0501061021908010700092009a00e0440464903845994011078042c0740c0025064401000030000814449506a1000380510315410588002c0302140c0302d0300d001a007005078040e444803890041310f060707900080203185014a038080b681002c0c1d12143d03040b00c54001e031480981032540760046d002d0055014502c080d40403440004000215030b4a00c00060700c02c481407100302e00e420098882c102c1030b0b0310880d4000075901d0424907040c114105076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 471105665 1250 471104415 471104429
    0x2090a08010c020303011a1e0d151401111501060302030c091002010c0306090c080a02070201111603031e0c26130302120d0c122102031005041109041104 67
    0x10000c01c0e0710642c000005c504841c550050b41c1d44104a16801003210301c15034505c2040c200829424000c4052000c004150301400e000300040e02e25201a020b82d40003144d0380c4142d2140c1405404100301d541c10860080d40728071030001404001100306061170344900c06000b020304165000c0001403031820142c0840d00707250300092500d03600100b006802800f030204544070314006402c10314002601007880c050065601d00f5900d0348048d541d1406044002508085401c3c0e041103003001254001900902115000e5040f800300d0710070040c15802c0140811401d101c07580d1082d606981007906031a845050800c00e154042d008201003040e0f1f218161000041c8003081101140002d07211401c00c504040c52002c032442942c00140900840011a0325032116401c0c1901281015007100001548401d01050790102400c11201c405807003a460081100340c0500407104560000a000c15880c10301090001031108403410301c203006010480501074003601101e41c0c01142c942c06c1003031101c91410269800781100c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 471106915 1250 471105665 471105671
    0x313080c010230120a0c030b01050d0b04020403080c070e06030a0209040f020a090c02010c0306230d170d02070203060901050702071e05190627140105120c0a02010605060c1002090a0801 81
    0x403407229580f220301a100c0317010007440c0068084205020307004601c041003058407038506000e243e01808001d800c10040141d4071030f80c200404070018107032102030305c501c119640081180300d0902d4a0047c0f5440090f0007a4030a5025031060300043e5240c6456a90050303000c43d40c1c0910322101c1c40400e094210075081000964105410310841a03815800f00344200103a50b001d22103542e580348030301142c031030880c0c004214022521304454141010b88140400030f1080d040181b50400482c40380f072042e004040060b030041e40003e40402585000c12507250088403d1000f00180d082c006800395483c0382130302c038600490066000d180c0200016902d110010080030303042c2180070541071220032502055005a80105400c2040c3d0b8505508691100b414503410185203440d00c1d042015690a2400360b04015040107010060b00243d070102d10100f5015110b10000c0c13030780311210603101130300f035510b59080640610800c0c4030341556103200050b00400d401c1440c00040e540c0354220702195184516800028040d03003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 471108165 1250 471106915 471106927
    0xc0506011710050108100506060d0603080d0516080f07030207020a1404110a050702010e13091a15010827070b07050d0e010f0305070207050406080313080c010230 71
    0x440c0041c81c00c0c826861001d6a410003800950502211803e0003100810b1707100860034010380c0319035446203804c80340040606040030201c0e0740300026140f113a001124500000b2a1804c05214240034940e0400e40d00300c90361591041943d0001d081b02e01c02071898600300c5480020509040c002d60459a001d90040e0000c00c5164550042032020f019640f00e4074002d031b1814403801c1956070b150303054941d0300c1d409035181440c111040d001103c1c1500003500103a4050039008a05007800442d00c210312045124050401080b00d100c55040c2404500034440c2241000410082d03405d0780c1d02c0862244c0c030103540d04100c115005803060700c40d60740d00c0e060205402e51040282c08079080300d04801501c20b003881802100c0c03001c46601c2007114541c1071001c1c0c0601280c00b08443d42c0c4070f507019170000d560003146c510465042643c0c132030000d001d0307500f280d01c0241e0580001460002880124142401a1440900a000c034480340c0000270b42e0b86244032862149045001c03842e0f001c2482c50402d2890781c0c3c06400070151110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 471109415 1250 471108165 471108179
    0xc0b0604020c070f030210020a0c17100e0a03090e160c0807050303091f1a060c100c050405040e0607051e07061415010807091e0b0a1106010609030f020f010c050601 72
    0x40240c00140d1280c000c1f08040100d05200044100c139040c2d10504000e2010300e44007035065103182c4200400d0710350159215010b003400c8079115889281003c100106000c2c092030402030034980541e002046400750180030490000451a0a00820151841e050324101c0090600700051f00803070300700074124003000040c0447c140d17000070700d000b0100d2082c2d912040080c3d001c82810807581c840c00c041400b941511940212480d010000e003c0c002540c405803148070b145100042c08440381ca07032011022420108041c0410304140c480c240744640010010001d508040502400318002c17480b41105d0721801541d04d1300710035203000035501c8407540503609122104544403050400c50007150841d220142d20420040950310a0070800d0042030191504420035003404281d0b10004501110300300c0810300003c0c00200004130320300034091402540c0c0d0340c1c240764244540003801c2c6101a4804d2040190003002480400c400c0351600d90410381c1147e10701d0300d5808403401a078105841d9400a0183d008d40b00c0002050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 471110665 1250 471109415 471109439
    0x1202130f030b010b0405090606030c070f0821010f030f02030708012a020c130b031e0a0c08060c0f13091802090106020d05030f04080f070c08011b0c0b0604020c07 71
    0x924440c550580b01d07aa02c4d14070003840d9001c0d920555510450003400b10780b90381003000003150050501502a0300e005000c0d03c0d8442d0314100c46c40105c4e10424002001e556448a98070304c104a1404810b9110f51949080103100da03441c400e00018103003015040590046540c10405040101091802401101311119001d40384074410181c1c400b40e5940c145921300c0b010f2010400000140c0028440c45a80c403a500c600c800a26400d500c1503010b1181c030600c0101e080c1629410320002c02004010300d100d4440b0314204601b501940c2c04103105610100070300840c52030301c50a81e141200304c04155a00c0b50500030303401c0d42070b21003680441843d9103810300d0040f01d440e20082140055001f5111507442e640c0c0c13000c040340d44401140003980059418401b00e078241252003031058000f8090402182815011410f15505500440084440510151042107010420300666042d0507050200b4410341035810005025640542c40c01020a588400001c000d5902c542c15a080540700310111039185031104001010f27 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 471111915 1250 471110665 471110669
    0x9120507020109050a0b03041401150801050610110706030c120204060e03120906160503040e1e07020a020607140f010f0207030909020436021611090f071202130f 71
    0x10f500e0210109803810705142400440e09500900d91542c3c0c3c80c0e4807081e02141d41a001001d96548400f100c8200411081c0928090401c01c800014a41051400c100c0c5290000304e041050202d411501c8011503004076009003180c0c4141404100b01c422400102d07412120782041641082c404100415407580c000140780054505034116074001c44203440038000d034080e036460141d003c038081105002000e840451020020300c50030884c2c0c00c1503100c1c9101150b40508440b051004500c40343d2031981300c10141d4441c0d800100b640064000fa00142e00403803d070303100b0020090507006d1034841d5000c0391101040780c0d0382c010340104000c004c8402c40a06020181d4049041a000540301300c10201e842c80191080354121910030800d001000740c1846161480100810300c00301e508017182c00704200d80300303d0000b00000300c41c9034903c010701ea80303d280c11006c0802035600300d4061403000007080703441559803901ca50400c0b0782e03003812401038040204840291007415502c59907060407180c0003500d50390800d20503003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 471113165 1250 471111915 471111917
    0x70e0403020607031b05090f030102040308030603060106030c0f082206020d150f120201180305030706060806062404080a060506150c03030703021305120601030201020f07031106030a091205070201 86
    0x10340c030349030b0030011820341740526482071111341446001260316002c0c00081c0080100a0700c6035101603c040002822600241d2081c0c039000000010408070340b80030b0103001c1c007508a40c103041120010340c01c802081c011a5051040074020568049078003030340694013400398804005e40c41c0132002102d141c003602940040c00d5400b8102d041400c0c664014007602410700a43c1e440098090080e8603149ca41c4040c0c04010009a0510045851104400c0421600d60340030b503000c0d00042d940d40e4000d141001c01c80d9099444080160420380c00d0107103584d610310364070001d42080514a0034080442411064074070590740940031138070a81b0340440070010190022407091208850016403c09144d00c988287d2094508170305807a00200000b641c40740c0294094140d0a081d28002c6480302e0311240401d0300f203c92030000c074245a2188004000315a030410411401d03402d21000ba181c0c0d24a903942c0c20402c45400d58000b80700e2440400024482e030803035030007840856040030003000111009840a0065441010b06074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 471114415 1250 471113165 471113173
    0x180207061a041a030c0402030a060803070309061805060d0c05040503010e06010e0f090706140f0c0a0b1b070b06040902030d17132a030501020415120606050f07050708070e040302 78
    0x41c5900c0d40d03d01c1c8040c14282d000c0e001d0b003d17101c240000c00c002540020083c10300382c1d958441c00305110004002801c0c0980c840e8035004812030412102030030b500103100ca100ca83ca0020303142030141c2d031149400e80716516840240401c10702c820900c1500c0b60f010700c0e00300740d42541c40d00c24110240c000001d000d90403604040325200c026182d0350032140007000100c440304102d41c403030341c0c0401c00d19120b0740038480e8008861100908000d000d41541c00294401001145076500103001102400340e0200c1c4150801e05014005e001c0c500d5808500085000b0140080c0260380f00701c0001d00b8540b034982102040aa00070156840a04080d001400544000000c04111070140c00010b0300028043d109100c003640000b00e0340390050580c461901500c01a400b03a02c0007002c0d1700000400941c090001e00043c0c200c2c0d520440c000f604600004050261a0b44084011410944200641e6400c0707000c035101c4419102e001d90380c48074603040092421340d143d44410500d218944001842040d0341000c6801980301f5400e032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 471115665 1250 471114415 471114431
    0x6050717090d0e01081026010516020d0e0301061205012309150c120921180904022101052401140c0a0b010e040507050d0b01180207061a04 61
    0x1940d96148501c0b0101c0801e0110064045543c011081603900c000140402d00e245611254802808984a9984030310036130240441c50030b1039000e020f0a507200322107400d451034201c0140c030029079801d0030101c91030170322240854609a0b0345003034011802810101441c0000030055150050081c265461039500c1c411801881d0814503d0304014103000f14a44e40c006c000300743c2580b5094010190141c40344007014810040401d039501e83c420880d20640c0c6d510054420811000c0022008048800030700081900810030000d9451040ca210100d0b14801c0e15210750340d076600d01c0400d40c41d07a41000110342c1310a2203250062403100540090b441083c4c0b12502100d00c0c418021b405800141c110544c0f80030414605da541d01d000754450203400d281100c00111030130900691200000e90300281c1040422042c1c5904120034070804200240003440165262a55180a40c903407100300007043c05800441000318048214284682c1c040e5800b10360001801c0080fa41c150320303e611075004410919010310709005007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 471116915 1250 471115665 471115681
    0x12021011101803090509130b060d150605030c0f06072006070b040215030405150903091201090c0b121b070204020409050a05100b0f0f1303030c0303050903030c040302060a0c06050717 80
    0x1c86000704d89241ca91f04d0581010341d1843c8402c030f001000740e03401c84c0329420a0000320303401a8403d80415660b20001a880d800c00080c0342c100304a0002c49401f13001d0311850000c8039140d0303c007101e07645500f040c0f8000c051003140780c00710700b002814441140c3c807a8000c503060081c0990b08800c580510320807500d14540640e49481c2c7d03038040c002150041c0c15074009032204d103803445c03a0100301c84c0c2c0104208243d03850541814001000b03070101d856000b070142c0d95038030280100085001c21102508440030f0142c100301e10040200100c100003410703211041c000780080000d04c090642624170b8194010701c2551601d4441d07640e007004020807200040214100b40208409680302c20030305055400c2c0703641c51880c10303c081d0340c030f80c0982d0311a511003480d55004010708403140c0d180740400c00142d440303590766550404441c10300904ad40c802403e02d01c0950810070600070281a414122802c0b00e9054070345a07104c0d80d0344d00b4181c1c0c00e40342412016000030308200410040130383c400610101b121010101c00d441c0d841f680d017 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 471118165 1250 471116915 471116929
    0x906030c030f02010c0c080102071109040b060d03020c10080603010b010c030e061309020403060203011805061011010f050903030907141e0604080109030305060406120210111018030905 81
    0x84040c0038190101000d101080216100c0e003035041c0181030680400b0069a44d41c40c44070b9859100804a03540170030310108000c600920010354460840d8102601d0074252030350b85d00f8000152416214541540d28001018000d1200c201413850040c0100741c0003c00f03a40c042c00d8042d040b61210f01c6540791a500302c10325802029081c083c0364142c0d8841c850780e01c84100303100d060ba001c3d48141201c02256140041e80ca81d040c0024005144505009030b200d514010300c504140c0b100700880c3c025036047c5802c2204503124aa0100f01c01c49051034100d80c06000711070a540103060482a0030a02030401d4204034101100100540c0515240d00c03c5851240e620842410f018100c81100c1d41d22282d19420142c0325040801008024140208280c0c54265648441800c442024074124040798441c0c0400256241521410004004003035002c04400f40c00c0d40000d248481d103c04803000d002541d48407a40d504e404000ca60103090043c0c40402c003501900d100101904140c1c00100d000407a242c0002c00e02c2e08110f1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 471119415 1250 471118165 471118169
    0x30306151e030b0303040306090f1e11010309060f0905011a061305060a020f0d080403091d0402010c03120603050309041d060133200304060f0e0301150e0708010906 72
    0xe0704040308880d01c40030071400f4201c054001603052105004c0480482c02c0b900c5515140351190040d0405030390b0302d140c200200e000c2444001540220615204045009441120303041c49007442d00150000c4c3c80e1821310000c124011817440c20910b000f14100411074154402e581f1711100b12000a0181100f10030409180320708078000d6030510105034100102d00701b0304050400034203280150783c9042a9030b82d111b4980f059480010001030020390501083c9034004000310040c0007822034003944481406c9000090180140c0000c0c1084020864103080c10711400e02015034405405060214503074a0902d0b5a0341d40050665500c181d143c07200254101210080e0b8000009000005d080681c2c6006d9400203071420303580b01402c03541000088a0106086403a4a402c06805900d0701d0021500007502070030059040e541100040d8030420060200507002a46002d11401c646045056400042d0110f03024002d102244035035003850035000300e0f0400c4810002440713109241c0c0d601e00a0780c0d079a17a4260545500d8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 471120665 1250 471119415 471119447
    0x26031c090209010806090705150c010e1501080d091e050a0f06080c090306010e07050409020a030c030b01020606150c03090d080702030f06040b130302030909040c08070b031519080a03030615 83
    0x20385008c10960824802c04580d82201c29502030030402916104c60a680da10150342e82260041313881c1e0a001850096118050540c01e0014081c90229407400b6048451601a182d4a9101030294040030307442d40214502514020b0128000c442d900c1d0045c000c4158540207810205400900003050b46c10301c00c00b9100e29a00042c0103085036441c011101050302d00181c803d0040000c1000b02140c05180303400284002d4910355000507112000c41e1000742103403030350300080d8115040704090140a1f9910344003507c12000c0c01c0c090580e640800c2e09a18618410083d130f0b250005103030503a20050000010181100c50300903001d0b9102c9084014840c2d03105c007021a0014100e00c0440040385a1043e9200c0c0321111601c00d004483c0303070401e80000139140d2801201c0c101d8002140d0382083c440c041081c80240020070720040c5460450a241c1c2000075a0945180282e01481407070076960441841111890000c01041c41a240f0509060130010040c01890141e16000c0390303601c601456044c0700344500010b5001c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 471121915 1250 471120665 471120673
    0x909050303060d0213020a022d06010506030c070b09030912030703051c0b1807120c0519020109020a0b030a05060a06050a031a0a080102070b0c0426031c09020901080609 74
    0xa0200f0400400307032904042e81c002c408084c902103c04180d00c000e04991015400600c031070409001c40278000e080503d40b0741c01c490150510003141003400102a4190b80d0104e900c03a8490b40e40340700702c035110f014101c40646615060300600040800110040c1108241a13a004074019030000c0f403180c2c1c910034244000c000a208000c80c100c28440380d00f443c829100a00d5000c110300b4991000a00354100214880c0c540d10300450034802c1d0150040f004c00e402070b035051001e1113044242c03c8060800e010794451038840715240e000b1444842c0c0300394088444681d004001c04142502d4078408441030b0401c845440e00645401d02054451400c10700840869002d40d03038051924070080740490260142805601100200c411295003544d03850241001030685030700016103a1449080191150a0152858108000c2000280b0030708070951401c05038070801d01110b00206501079801c43c80c5200e2010310500801c548062501c28443c031ba01f02d8202c0318001c94520035030343d8032200c2264880c0420b68100f580d41e48 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 471123165 1250 471121915 471121921
    0x203100f2007150b0406180506040b0a060c020d1a07020601080d08011a0c01151e0f030503040314030c010c0e03060a1a150c0111070506010e040209071b0f0b0108070909050303 77
    0x401130f0002c10400101400101c0d5059850b10042207403c030901e4130340c0c062904d880810003942000c0c1700d280303d908030032612461030a03c1c12001030a0400f49100280c0110080980d850500c01da00100040030b07510500e9a00652504400080d183d84003805180c140740100185082200d1243c0e0040341030760f507083e80490f0380540030f10010600d40e00a07034800030b07035540b25440e42c2110f189101105008001e04100c40040250780302840080b0142c5030881c90240109000a1001c9040002580c0c26694041340208007550340d411014514050b0500b000303002c0d03003888010f0120075480114810500340c00d40c12aa06902c61820580aa40c1c40030000d220340e400e14854580640703421101c1c8166200003a071501c4c0f500a410b010300e401c0d190002d20164150400088c4d020030041c080044a006201c58000c1009500301179000403900c6c4c001030090020007a8810661441481621b01c0b030344195440030b2a0412a46180780c189002034091150013420301903000c00003282403942c00341e404151741c084083c502e140c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 471124415 1250 471123165 471123203
    0x4030509010f1e0e01032a0e031509030406030e010e0a150b09010e10230d1a071d0f0102030403060f0b090103060506030606100c020405040203100f2007 67
    0xb2115500c01d0040201000c00c40c3d1840d004002000d2030000c20f9592000c0340c11448001405903181ea1008034001b000030031094400d0006502d010304010083d2800701107070205070f00000c0c500f01803c0d8944014009820074002103110000081c4120fa100d5107060004c031010081e00c908030b0300d19800b0860031350081804240058000c0d0380781e41046080003000601c00c142c07980072400010b000d0b04462200d80b141020300080c0404542070a0003004081d4801d03404403000f508031440c1d0038141400340c1c054071003801d0075010041c1c04010303050100b40c0d4201220213490220001002c620403c12004612442619105034608005054000c0764a040e002980384c10703d5035071450010016032003a02403069a89115104d65503441e03044a00860141c00c2c00f00d42400d250040505041000d0700592180c04201d2045a8040d00035a280c14001c1e0100c0d03000880c0e540c1d50011034144400501c000007454944004504811007a0780032428503007004000a444ca8042b0600320104d10941c1c0c070150900a0f1820115584 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 471125665 1250 471124415 471124427
    0x105180906040e030a03060f0905010b040b07170d020d05011703042d2301020a0c09020315210610031722090207120c081603050f040821030403050901 66
    0x700340042c0c400203543c1c142e4080281103400818440e40026110a410803125607a60703c0c2d00c000c0d1201c2d007030030012949021410503440c8102c0c45001528540030407030300144814000c4140030101c42c80780555032030b101c1050000c002e40c020f40d072407900300349400700116400300d103400a40c54480404004600e05803c1500c0c149000704940050401d15040d2050f030400c48007003a90b100300408003411a1600c5800410240454405012800341154040c0341480302050042c3c0e5650212100014010307a01d48588003031041440d6a15491a0017490402d4031200c0a0040d19800580c00e4241050301c02a407110503803400f400d03117140300141164129403501c0c4070402001c00202442421045034071103606407280c0e414000f00a41d40025400c642c0401c1a0050015900b44082681c91a00e0107010802440d511a4001e001c2c07008070400110542c00b00000700341c0914121141c42103030201c13007911241c1d03580b031082d40c3e1f0b14456021441c4c0108402c40c001412900800d590149a1603250a803c3c04280e100444507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 471126915 1250 471125665 471125671
    0x31706210a060c0207030302061b0a0e0103091b09110301030515220803070f0c0c090203060d020a0f080f0f101808070b01080606030d0509041508030d0605040b01051809 74
    0x494010407560000140282c41042c2121603650050303c0c2881ca1414082d0805000078203840040c210a01a02003c0a1003021a03103a440f044c109501e850190000480041038001401002085880d01c04100d0540816003402254548881403200b0b40c1407410402c400c1c0006e00c0014015407020f0314050000c140103502c0d6500110160b9401801c42440c80b0501140046c0c40060301c50b90750000501200a900038402d0002103103604244c1740c01c2409695a8810308254401d0384440381e400b00103d949941c400d20000b4080c3d1f0018420445c3c01d0b01d80010151180140c803800110348103402603100b02c0c8402007100218900300c9009003000c424040a601d020301100c0c100382480006110003000050a9400079000d1103003d25910b07011581401c070454a401005443c5a01c2a030001441a40307142c3d0150884001c0e000603500030483c4500602c0f01c03250210309800000c3c013070001049030020061943d100b4411680f007114180100703c44031340103441911a154221201c15503541d109031080c2050703200035030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 471128165 1250 471126915 471126979
    0x4060902120406180203030a0c1109090616051b07290f0d091e05010c0e130e030c070608160813141221101d0406060909060504031706 59
    0xb04e0f14260340001d040d94440401d100104441e42c2d8154144034004103031807480300b400e4407500103605040d1a01039950341e00514481e10807481015020310b5070b200718241c03100070010200034142d40c00050f41032034135100b55026100c400520a044c43c00c0407020140440d50b800460750000d40352541c0300e9142504e95000e404411410f075110364800000070b455807883d0070f0413901c030176040e01e00d0078140c030b4118290b44000c40701c181041004500022240ea0388041e08000c5100d1241c0020311690040c0b62500b1802210380c024014040c47e40001004e581040c8c072907211301d0344100c3c140642c410035107060790b1003401038a6260b0402609100d0070700140d1046001e068a074281800c58501b010300d981c0b030f04141c0c0d0040b44114182e1075401010340400b418070075060380011800050b1a0103a080c0070012400c00e00e25900f1007425202c00cc0444d0501034158414006003c0351002071003020094208030004e001c05031000c400090b803408000900030208002b141c01298010555404100ea400640c0d04051032000300b05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 471129415 1250 471128165 471128201
    0xa120503040803030c03190603170904091203051f06050702060a0216080c01021b090604180606080d0905060c101a0402041d06010207030302150c040b0c0a0204060902120406 76
    0x100d04404200f0103103102d2a070a111265491410040c1d049403076078a00d070102c488500317000c070600c0007a0300d407071003560a09150f58007261910f0718440000d001e04074041014000c034100f1021607100561540080740705400c039603031b000c840040d01d586569000b5914461280018410710182c001480c0043c0241280070381d030301c1210b404080800400d030414495a116651b907610060107003440f5601407168141c0c507070003803aa904801000d04003045001c01c4c0204203e116640d110b81d544179410030451540d10564024404200264665140a940740c24041d001000b0424003140016180340044c01c441c1681b010b0006031140c8a030310107954020300ba505d10150440360b400c81f00021982c41d0b0b44080d05c02010000310380e90700c006081010340001d1a01500c0d950464000700003d10200b5000a071190031a000c03020109103640c1da802c040016401241c1242240380c40001d01d99003000c10025601c040d45000700c60804c1915038a0302800704074822081071101c52618200003d010075242d500091062608207415 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 471130665 1250 471129415 471129419
    0x130b040807051501030c180e1902030c01170c0a0c05030d05100f05010f03050601031b030b13050f13020d0f061e061406092e090909020607060b041d070608090601050a12050304 77
    0x10b81000503c003240200e83c9c0c5e201e90361406500e400c00110082940c00c0c00c10200040c4000d582d0f641e1840000c16070b051301ca40015040c07a032144100d00a07a20381e80c0020a0380c0d01e804041007500c1c007416050741c0c00003080c03040490205489089500d940120b0310141c46016075400c03900c00c00e80181c00020324180c14540e40b1203450b04820800d1801e414030700520b40d00001e101e03e521003003080c0c1000282c2001802c5240c8001c0010405a040c4a1608424824140d800d240540d1000980c40c3c0f184134001411032a450082c0790812001d50040705240d402101c0f6005414003010031030044803500d1040006c41122071002d42c80c5130030000300505a14002a0081d0b079039805031802e850b24038415214aa01c400003c00c0c2c40e481003030380298140c001d4038000700300744018485500000c105006503140500740c41d075130b0700c1000981e60344ca5101c071f4a0241d07041785141e150b000e5100c2240c1c4074001803041801186401000400001002c2651030580b81c00070800500607041415910715800b09490480d400c0c4810800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 471131915 1250 471130665 471130691
    0x130509070e010f0e0c2b02090a1706250e010e0402033309070503060103020c1c020d0504050d140a05030c0109140c1305130b040807051501030c18 64
    0x207028000c8484644003a91a1003c52900248005c10380c0d11350381700c21b01507600903407004d0b102d601400c045056a4811400941140c1c0028032134900495402029448009880c2041a4562414408503802d0322165596403071140800c4000381031149090f03981c040d12251007030040451030740508041c980089883c2041000c0b504030f9209071408807100041c4800203c00c035041103101e0024000404120012691000124444040c0038040d00c0078403d0220001da4a82d2003030741922442058002101c080e10a540c1e40c03a44240a41b4000340014022005003005650003581290200c0300c0143c188400c0d40b1944d00c682141d503003403440044480c080d580e0310802284082002d4840191100b0000a00b5141c610304024008034010010705250014150811143e07100031540003444444d890110311a0703240d030038140b5080d0143c44001c01200000b000d0205001108001d0302c80503116a08803a5907025405401708001c2092000030b010815100003881040520000d0030324a14210b100402c40a041141d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 471133165 1250 471131915 471131939
    0x3091809060f0203100812030109021c14010302130b1e03150702010e074b0e2202060409022208030c0d080105130e07050307120c0f0513050907 63
    0x40e1902c0d074190080705218411808698000090034100d008200603800c003081c80025000c14451440540d5001c2903081c1d2400654010480c195107101040000c0c1e203800e4912040031000313020507401040d102d065031381644024451400410070041200b00d180142c5001400010382d088003a035014080c02500300d01100c0912502c4c1d0180007107800108403461000402131070544a41d1003904e9000307020901c210201c0804d40007180105d520384005d03030071550301598440c0c2654010b00000000300700000004d5855840d407803080c051000c000021002c1c11820b01282c045121082e00650b020008010403c2841603540c0100090706092100c0074400070190140c420001581d40301c0610b035000041c1d2819800c405200d440d042481e14200481154140000700e000c182c14090501c1036140d03640c200002c40c0100700034070801810002d085558a9440e200c0e00d000b214141c201c1100e5035400341301d000c82e03135450045010041d1030001e45141c0c54000e4130b01100002c3c0a02410181c400d0098000c003290204442c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 471134415 1250 471133165 471133181
    0x203010f110a021209010c11031c05090a050607052e050403030f23010510140a0e120316021509030f011d121b1905010b040c0c0309180906 61
    0x4180140c5450b14890060b080079025102504a284200b24045550782c0140c034060340f903604188030303034583c2410b1401f091915103284502ca002d400004202101942c0c083d00808030350f48240c1c2c0880945580f14103200c028010000024900d800000070060401003a1a21600a074544608a01c518544096403012520706460680c000f0342c80b420240c040702a18051240b005002c46180c9844182440311003102000c1030042e00d02c2103001c0c036400c0c00748a1042110f100300c01040e041840d03480c0200031028089102c032191f00313030143c4403a2900d06c110310008000c4d1103131890289111340c079006450b42001414080c3d1440000c902d141071100102030348007041f4030807407a00c0d04d40002810f08854240702aa25602402da60801e41c02131a030500c0802c050400c2e034180340c1e030ba202c1000070085802c51080c180b00304610144011020503a0010502c81d0541048e180403509680401400741a480103d1307451174a03510180c082050f043c1c08024014140c500d40140c00d000c46000540540660350381d1095510746 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 471135665 1250 471134415 471134441
    0xd110703060c0203120105060720010201020f0d0504032c060703030906020c0a06060503030a0c0b07170405100c14030403121803051207050a14030406180f0311010b0a030605040203010f 81
    0x81990803501d901c120581b8050030b01103e1450902c03800c1d94518002140840c000b80c0c15a1910380e072420315034000d4065800c203081901145840b05403000408000f004119010b0f030000e0a0040c0b16801d034010808060300090030800d072843d10101c040705002456020781821410142ea946401c400b10351030b480a043d1001000c4041c0081c0d07041400e1000541d849600500c0c881e400801030303415101d0300b001196150a0b0302888007406517641c04020b48209046190740143d2510a00404c000c2120219085a0107040c020301001340f2068001c044880c600280c9440d40008000c0021401081c043c0803428500541c3c903001080e11609891303c2c2038a407088040c214081007002c100803c540e9040c11450354451080c0c64128100304a1400c002e01121b01110700d02c000034000030201d800d010168020009100365070781c1c0d2491030f00300c52918002c0c0d21030125081c0d000510400e15104240300c10301503c01040f2000381030180450440c0c841f0b6000700b801610499040d03684403031a0013440d00178000c5415105036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 471136915 1250 471135665 471135667
    0xf12030a0206060109060905150d0e030c10090f0b091c020109210804080717070809040c0207030c0611011d0a0201170f1501170a020301050103060b07050d110703060c0203 75
    0xc0d000603141034809003d0314144540d00c101070001c1603010140c54100c80c003c80b4807039050890704003100e800d885140561003440d424105042001e440000003411204c035100101d03203400c0034541014088801c2d114005100940780f03001803021070700c139141050b04500090107544041402408040c0754580000e001c40c0075075102e008000c240f240490808070b0151420110040f000001c1c0c400400c626002440180b90400c0800c480f02031092590820070304803d03900034917580316140c0c200054030381c06c44d8600510840c14030811a074410710215844084a90021b000c001860425000381e81280403441402040d40d40d0b211903881d24180b0324150302d081e44110002e0000c0030614000100301d0655842802604d00c00c7c48184000141000c030015440300ca042d9410140210110040780c1c05525141070109418020040c490a85c8071030b4020340c104d0303509807403c10009030f6074400c4003042c0c041c09070090200e803c804849542d680c0074416510b000400c600c19608419143d0382c3e82006c50351307142800340040e48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 471138165 1250 471136915 471136927
    0x2d0f0c1e15120e1b12030c06130309030803011d0a1b031d0105010b0a020607170406181b08010e1203040f0507120c030c0f080316030e040608030c100b1e0f1203 70
    0x1c10317504002103044d494000c0c5281c802e080000c42d0340d41502510302c12082516103040740a05208455081c00b465100c1401590b03075030b42e46071482c000c134494001e40f443d40000e1000f2070007000d402e109445182c0c040241c2c01c0505400d441082d4014403a1132139804030030440d942c030300d140c0200c20b20441c0e000e0a140001150ad070811030f24024600080105500d00340008510140b4a07101d00c0c20607682d1040d40042c020a5008800884200801c006c9000078800107007486403403501580c08a0f82c4040da10b00c0700c020001080500860b5646810100203490380020400110300401e40c60761b081c00180b4007500032901c0e0340d40c1d0341c04c881c02c00610000040e541c814030681c042c000c0140d440c161500610100da90340c00160f041c207c4040e207a100c0c010200307450800891000d010180500003c10446200410411070340d5920040c050312940301c0c00c41c4100314001c02c016101460142d11605844070b07000351107200d0703009107665460008907a01d800550b01842100040c0025921041c507988603044007405035840d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 471139415 1250 471138165 471138169
    0x7050417011e02030603060f09070312050c0f062a04081f0b01020d140a020120070605010504021206130e030a0f0f09032d0f0c1e15120e1b 61
    0x82c5002034042e0303000c0c0c010400d01a032a500000d00641100740d0001c0c003e100d442d141e8150f4a042c0c000d0f400105140712a01c4a80304042c1c103c80600402040002602d480904008000b500c032402240c00031000006911850745980306007080d203406007200001c603441d058452a5603454241c51080c0c04d1200760409550340c410f0141d0b40a0708001c0c000030b000400513905062005000c01d0851174102d0400c220210f44400100d200750001d0041d1074a150003c2c0a52040000020040e80003900960303509080c0000081c503406c0038400c40c7c0cbc1100800900d5902c9840c0c5c41e042241a41d008405c1e00400b07521180d011100001c28130080007501d605403148902e8004e203242c09010f4240c904040c8080c800e24070000c001041d100300542c40d9444030f01c865664070a00100492100302c10300d002c0a4861001410728804001c0450389480a566141c0d4601603100d4502c007041c820424203010b01d01662000a0383c4c0303081c682c010701c120100103200c1200490322908502d2403030319049508102c14114040b00c90000f03094 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 471140665 1250 471139415 471139451
    0x110d060927020904060b0402090901030503040f06020f032d120f060906130f110d091b0b070b0406061d180a0c031101090e01080f0601060914090705041701 68
    0x100c8528507005a0000c0d55000544280790060002d4802c540781e6240035100c1d580c1e9412201c8141c0002d01c0000e16503160300302559240c0060103241e030310103003000003c1150740c00000d8203000c1c658080c00561a0018242c1804000c003a90803440d140c0c13524140140d001450034501400d007001c8180700800e6280382c801035040c0e0343e0720301510f00c9000302509800d02c0b54030386070800c000c409985494408035806515010050081a4400300300409100200309000654503e801c00a0b403d400340a0364444000420100195480c040c441d0860958040115100042c0143c1c000d9910500507030b0006030095484100041c08021000b02400c1c9000010811003c40c1d07101000b00604008140244207107a050750795603401030194000644100f1a02040000684c4104a05070240000b2000080513594a02d407003545c0b207a00c0d51000107a40528000030032540d02c26521300341100c0005d0a401c00452494080c04204107001d012041003120802c0b0118105e01122040b00c9030755a48000002c400800b08445040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 471141915 1250 471140665 471140711
    0x109090507050406060516140a053003010614040e04080703090e061311040b071b0b0a080c090429030c040b0a360605030d020f030a03110d0609 63
    0x100d9031030400e0500c8072940c4001a1031004c1012411607034100c150323040030242044072100d819480d104045400c4200400400d43e6503641041100d13600c010000180e440c0d110f00180303891180407a10500040011904c0b40c0d03030010310304001203449481d06e911949840c2d0f000f00c040364151170001d40041d01e44200b50b8400702480051440c04443d401c3c508240c80060810000c00d17922020980c4c880000110303420b40001180c00030205183c01503030f642020719041c803c510312130003204514804080d000980705820011035005056943d51030019903070340102c2c24005c2d003203602c00640141e80d030b02501c01000f882a141244c60305140d2724100c2451000e9082600e4840c150860b54040c0e0305051000c042c546508100005a5024070f5840d020301400d041000080c615443d810803040c49000011b0b01c0c48122540a0010307206d080e0203458055100b007000b0f0366a0044410b01810a601c20803402c01028800e50150001840b0310428a241881321018042074a001d500840c0c01c01390782e0501c06007805200c00c81114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 471143165 1250 471141915 471141919
    0xd1b020a0308071a071202210a150b0f0d020304031b3509060901020a0602030f1005040c120e1f0c2d18081009020102010b060408190206040b03010909050705 69
    0xa4505c3c11000007070811224a0710324005580218001d2070318540b03506a98030300300c844c0e0300c00600c51801c4c512120190101d0044207045183d40c05012400303510200488150710b107102100b61805a080094900135803004006404100c3d2449100b00704600d241e02401490303010310007110000600700140407601c00e803031880d5268031810030141c030f619042200607038080f20710458060791034a00c442c005074104503000d400203006510000401401d00f21541c401c42c01100c3d401041e0f0103031070302d58003444101d403403104040d4040b03420b03074020103541c102c44c1d00902d07054001403064034401d103a5000005080050341c00300760714003516110f001e00711a0303102e01d81d101c408605101c0030000d07a0b1f02e07441d17070607850030140050740c10030009405856580000b10803103001028080308990090540c2c0c01810014084000100d005500b051081c2d0950b00d0243c0070f0303c4c16660208060004090800d40f00100c10f4500002280c100d031080c0303c0029000c0c11000a580281826040450b000d0114034060782000d486810840c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 471144415 1250 471143165 471143213
    0x10060504090b010302060318060106030c17010b0304170d021308010513031d0a0f030302031c060f05060306030f031210090501060e010806010905191d06030d1b020a030807 75
    0x100200781c1442c03900741140c0e01510366035600c4e201c0f00400f08000ca04072003503c01910640000280312645a0322103a80f02c0500d41d42d1070003a9040034034982d0640700178410030345485010b2001c980803c0000c141c001c4041a444031651400c0300b00c80081090760000b00034544101e40015042142d88020f000306640408051002102c00c00240d80190a0940c0d0b1905c0c5103540510b02e8408042e0344540d070320301c005450300300c980c82d0a0941d01c1c54002d5403940007055842d42c80494411182000500b4000c0000b03840c20075035142c00c002e00704410302c092500000e061640c548507d00c0903a4004c04140010311000c950401e91301d5032072414184200d0010045d50268103440e180400400182d6130041c1e83d81c0d5082c070300340380111103a120314004076000302658200c2540842131402070515004c082103220111a640c1100c4000c00414030004181408102c8502c0d4060308401c1d07003201035901c291808070a42003604000780a111a60b000704948402c1038004a0b100c00000901d2010f00400001007c03698600003681 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 471145665 1250 471144415 471144431
    0x7140606280302030a0c03140c0a0b070c03021f0206071412070c021302030709061d0103020a110703030c031e0f051c050c130e10060c080904090510060504 68
    0x4220598481c03105525a0400900415800d11035180000011600101161014071550511102c84200f52004480000c609515000304010100706500310712801003468000c60325100980030307150f001c0c0b04119001d0900b40008801603850141c01e4002601c3c204420030762845044002c0d2400002921031401c0c498544842400400c1920807508a140c812a690400703071103003403007903900815441c4002c3d405a440d642c004452800341d07001c0d500c601c1a95591010f4982e542c003003a50300107603060345080f5200c1c1d000040c18055029400a2003554554a4801001f04c0700100d05070a0005c6500220001841e5000c01800d1651154403088503400100d001c1e5002c620a00026000380c6075801c11500f03000001c0740c201a03580601a24880e100350340c1c50207110724030742688003076016071080c04806110300340b079040403d1400c0001c04541c4107980c40811841d01d1828283c05446510b50b1910441c0d06d0b4030304104100b17441c0c036680100d01a8502c1000181627824102071900e09541594000501503468031f958 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 471146915 1250 471145665 471145669
    0x1b1b06050f0301140409061b0e10120203180d0809071715090f160e0a02030f0a0902030a0609061e050621030c0f0f0f070b0d0c03061a07140606 63
    0x490f81100c40c03c0c2c80e01050040c8620116025010080003c0c200d5441e0001403c0744680e6070307000000c00041c658038964400f106504000c0b82045c50200d40000580f91403400303c041e800c80c0d000b0760300614481e52644a61140c481410300e00130070074400000040312002440180a01007100401410300d4188800c00352040c00e0030595074481d00c1d04243e00d42600e0802041491308280152000c03031030040f054174000c004503100174004000f00e120789459400080c0000e000e560441c07095a0180c00746010034601c80c0c0300c2010b003001403c0c10031f0041e030f0316020301d48007000064040d2241017601807045801180c803c0351040d000c0303140c80b10001d01e0794600d418002040303c00d1795900e0f0107010b0b002000254094041c04d1640c0e192031350080702d0307812903a40b00f011001c900001e40056a0808001b0364130440b58a42003210050303803070b02c03400c2c440c10301e01020074088902c1015007a040500481070b0362070002a00380e03035020115140382301c218803140c05203000106007081c400314821940004201c14010310b194285500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 471148165 1250 471146915 471146917
    0x705032406010c14071415031626010504050a060305120f070b040804031407050a031203090501050f090c2706130c05120f0f0a0203071b1b06050f 64
    0x505169120300040e403580c010016184000e40004041d2124903510f10016540c030003600464000d180b200c3c620745400c0c90840048244241c8842c9030034196103418030b11041c22810b49a80800b4803803100803060000e100205a403140c041c0200c147c4226501d08002e000440d00c02510321061a8140042800414030021319020442c80f1402806ea42700034544216800c0d025803540205105003480610092040290103401582d0040f000ca0f10741c0b00c03010b03241d80c0d5101c0d070300d02c111078002d0403011007000481d034000d5290190100b01c0c00d000c00c0821a0b69200c80c21500102c80d04550b0090180500c10382b150200300c08000d4041c159604c8040c9409240140740301c9109244107030701c0450200c002081c1d40c580b000340003c1403000d020248648030034040003420f03641010112002e8900c9403000103003102d41c00503095000320101c94107205180c0311200614080e600041489051040d410340700d1743e84540004512500500400d140c42030340c4d40c400c16011580b50154041c0c0d0800509100e90380411707050320 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 471149415 1250 471148165 471148213
    0x7170709150903020301090c03030e0109030c050103180f03031b020d080a0e01060e07031a09070c0609020415120b010b03070f112a040c0f021e01091202030705070503 73
    0xd40d5032540710441503001c64210065400080d015400c01d1490410069140006415a03102c0c0c1c80d4080c201c07400200440f20080e031440040c00400c9110300c2040554001d0788241e1042e11440f189003402c8200c2e88603000300c403c244204a0009036242104420300340340140c19608181c0d42c0c0701410046104200080003001c0c0a481c0e0034400d03a480700103021180c02584000010f064001c103100c0c0c82c4c035010304082c008120580513800405101c00c0c10220034680150000c1c400c440c1600e80050106071b6450381c4004080040049811583e14084400424004840d800c01031105680f0f0450301c045601e09460aa034043c0d000d80f207100c2061041c07041c40c0d03410240000320b1280c98034040002d41320a540180c50070503110a0050200c0320364805090090071781c3c0e58011030a9081d40c1c10310961074800401c0700c0d840011403409006070400e090083c00405401c0001181c02d2040b4000b00b10901c0e241c0710084500d880d00c117202c0260740001960b03000c20009001020040030110040c0003d4141c110504141c20410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 471150665 1250 471149415 471149429
    0x130b060403111c0b0916060801032307080d180302030c090703150603091b0323100e0a0506090712141f0b0406080a1106070206040e0f07170709 63
    0x30218075800781d190180d10070032076000c000429a150005080403052031130140d900300518051000d0800f10b02040c00c2001003100c010b07a58182d003aa00c3d6481303661540c02c0078644411122441821450030300310030800407001d0005003019280b07280f50300300c015107070285403060643c40320f00d040c80800159a0100743d1600c07092059504105640d0342540441c01001c0054041401250100011402c1d42d032542c02100410f10640c40c40d030245080358040d40c0c011440d484001c1c1122211407494010b0740141d0b22144198a40000301c40c1551003e00c510300584100f070300c5ca19001d0b0700c90400003044c00070800c0b0b0250840032180140240b1810b112001c02c1d802c00e40c2001808483c00410414403803601005100390a001c42c1c800414004410b402103006066034500c241d00c80c074100440840c6002010a880100580c0a03203a040e40110800c01d100b11130f0400c0c0f500381d900407000d110014039158507501044c0310360040b007480d819905d8150400350503581c2c4150f28003154030448080046042d001251001501c0803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 471151915 1250 471150665 471150683
    0xb011b02010c0f060c080f01080109110111070f030b0f1b1e04030f030e09072c030304051003050108120705030304230a061b030b0a090f06090e0309130b060403 70
    0x302c1c1c02c00f22408043d8020007080c140c85c182c140090030740c0c000380d61406082c6511031404035982e614861401d9a207d000d024042c54130042e40d4102940c058444004001d02245c1680c0c1060340c1c0b00400b00081d006544140d4800703c03a2000c010b9442c0c140c00c042c9500c003040c0d01c2c4865080a034100100700c40c4c05112f81d1003a0700d101401001e910144c40f001610000d5900040340a5001b941d440c00501d440c0d500c1040302e000d0008040031651860244a804c0101c004658100c0c1001d01014130000000641445450305800700f04008116511000280030345801c40da10003098552414100350f140c100c1504007441001c000380041000200013204980d080b81e00031a8161302c001000e960400b2520805141600700e1107075200d0300c800c0000c1c41e003001c84461040301e41d14540741c580410580680303204500440e88100c00290038400c5071996130201504804031100020b6140c0c070369034480110359002c440d90940b0703440402ca02010f0700c0d041c1004458002c51321800d210044451004c0781701802036000040c29018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 471153165 1250 471151915 471151937
    0x180f05011205210706050108010f0e010b18040c090e0325021c020a05060d0e07050405070504030b072c0405070e090105120102070f0b040b010816091e060807090b011b0201 75
    0x4510058134502a001101040b00b540d54200e41c500a0404110700c0d2881c608100380350101c00341c10705c509040500003918001c1544040080e0b400b07040d0307008000712440d90180b580810f020650384601185242c00000965a03130700c208448104000c2e14074042505682005079010043c0c541104042c580a0700c111a80c1c9030f100148001200c501c1340f038001e541c114001007a9204401300365044082d0290880341600d001644a00c18081036490403641d8201050307007044200002124441000d0f48100310f0f140003880780850400d03071800c01e403c00054001d02504400b40c0d03403041c9424400c4642000180c148040701e19203002c04945036403414030540c0e21900000a622070800030a4048490b0150b00000d046003800b00d0389440614403c3c240c1c2c2c1905c41c0540200082641c0c4400242c40c0d54604040342c00101c0369180054407405000c40d80480e51400f1903051441c40e00241c240a0b480c0034101a0028006440c00c1141c5a001c41e62500030160411100403130451003000c1822240e80c000d502031030b064605c80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 471154415 1250 471153165 471153223
    0xd050406020c010f05150604051c02010909140703050901050609042307030b090606030a0f0210032301091a0105310e040303060b07021e0109180f05011205 68
    0x80500000746400d0750030240c510038010313074039404036200702c81400743d8040340360a502c14812075001d140038454001402040301c2801001940d035a0144e40e10501d07003d2401500d0303420040c203071482401280500d29081051240c82900360042a5101c00c010700200040d1803d0342c0000c542c14400380006d080f6078400003080036207a0b052603082d2044090201107030341c6203550b0b280130001000304640c40c040314000c41021a807949800300c6c5540360f03036801011440d241c440d160200520003600031070400030325076146500c0da03c4440d1944411002029034040381641c7d0306d001c41d19003da0f00802e480d061840c401503902e080c180c0e0030105030740c1004102000d140d10210000e0841c5044848a580000580c1ea8000001480050014210310451095034207004a60750349138074040d03034014984000e500100da40c07d50f0b80d450807040c026900048051401912450b0b9a0803450b00010446241d41035075912042a089104c24501650380102048008100c250f02d0b03549a281c0c07035403d0090010140c00d0484031000e164 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 471155665 1250 471154415 471154417
    0xf05071b022404050a050f010f0806030118060b040e0d090315200a0207060513051009090f0f0b03030a050301061809110703120e0303060f041812170c0d05040602 71
    0x820b4002200d401400030700311481120741180c402d40b441017032100e102017800d08182c0e01c41000104180c60f000724010314070300207071203041004028640642d40d8a500c1802e84009081880240703000710000500c049899052000303940100c1c21490081d400014002c20781940300c1c0705241145d8000c03403131040301d80c00c210124010f000c01441c01d03010700446c00380121420b625803004164041454003100c26250383c80d42c0903202401003120704054005001d03000c02190170042410306603003420b841d007504103e40b281000c80171215400c0544014595410345042c02d4882886001c4000303008600940c01c060b8080f40051141c0f00500400080101203282c481041401031021301c068101000144002004802d05c801e0b9074002110540020390183d54100c175560441c0b082d04405000300c07014604e19994201400200e6480c0400700340c2141c0d91b1582000e480398aa42a11800c078071440301120800f03100d040080400c0e0144244480c04140c02041c0922000000e040325174444400d14042003aa459090080003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 471156915 1250 471155665 471155689
    0x13150806010308121b0715020c061008070801020903060624030405030706050a020c120f070b0a0f0501332c0108011203050f0306150706020408010f05071b02 69
    0x240315210001c820011800060101d1950210503004150b50f401e04481c40d10300e8448100190a4082098502242d1300c980c04018213581b161016280030a094035031032a00404481d40d2840442c4044140042c400620141c07005201800c000d508004402c4000b0752106001380106100d01c0c0211641c80d403c440d0459800311220402042503201d14090800c1a02c0ba84046c4040714041d103010005508003035a4030a40c1c0030200248028001c0650154529586034807131144034154150500c000c60018a004803400c0c03003078101c50000314854003d0889407042e986c0c107800001d4441607602031030308a5600e441d07515009c4000c0041e50203d1040c80c00f400c4d11b502c0c2c0340641003054a04200c51849801c3d0100c07083c2402c0640c00c0ea02c0e1401d60380c2c1c0342e600c0c02114200d0f00c1c0c0140010420801c005040140d040610340080008103840b55850250610712020380c03000e0422104150080380070490740f0801e10907100000320507841070103207240000009081c0c85801e0f11003030710300b90440021401d5407203110345511 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 471158165 1250 471156915 471156929
    0x29040b030f101d030d0905100509031902161409130b0a0902010516030e0109080c01170a060f080f010c0c020a09051504021303020f03010212130f1e020913021315 71
    0x59600009150f00d000f5148006c0e064400e403043d11143c1c07001100b13500c50b180c45006c580c005982050203443c0020400344a0030400d400311304c100a01680d2511300c200c0500001d04034442c2800701410f2820a01a10b00b0000344140703030480e41404142c000c01c20581c6155400030040f840081e189865100507104c0340115081e03080c030042054003050426030499101145032200341c8480c0000c95aa003d50b40d40c3e0303032245410303900113501c50007807020720f4004140750b0350020795540001c502161100345500f40620103601801c5154840700803042c44d00c5003032040d91402d0b03400c2c3c540b0885030300b00c6030040b408403125442540343d1a60751b42e000805510000b404240c140000402c103541d0b8410800050b10300000a0006903c103003031040070500940b905100b20b0703400f51480d44001826941d03a103406002c6c00c195060507503855600d40440b90000750b907441c054a506075815a6824813140340d005010070544021300c003204034080c4198850250340c8000e42c100f03d29020a801081d00020020404140c20301c540c0302103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 471159415 1250 471158165 471158167
    0x528020d060603091506080c04020d0b030328020d0e1c0209090c011d0d03030e0a05030c070e0129030c1201030c080d05040f120629040b030f101d03 65
    0x2c40c1007685500200c5120f8056200030300700030000c0c80e10700105c9441d88214445075201708848001424140c01820165444c1c0342c0004110401501103421984500c1d019038a458015003019142e10399455515101c0311544010407140b29210b0f0060290b003442c01e19103120b8030000001c4006044c1540f201c84500f070740a80380b120541040e011030b50b80c550908101c06d01240c40d003039071100c400b4800c80c2c0c0f0403003041009100c5042d84061b624168020403982900000c54000c0e6460000030860401c01445060312403002400c400d13140003035500c102392040e08641d030550b6170142d0746082c03d1540d0002c0ca000b075203460b101c15607035103801d040da41143c0704506900380c10540c400000000e00400030300d00c0381160b00480a540f05070f1040d000c01c031510b01c1280202284480c03c00c42c20f101c40942e03a80e1100901d8070a2400003603040c0007048107a205011100e048060f08120140d11815082034002d488004800342c0c02030010192a00116480b4141500c29202c03656503120001340500e41c0310660031680100324103503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 471160665 1250 471159415 471159419
    0x10c020d030506040b011205070c140304030201090f080d2706050304061d06040b07050f1b0706021209040b03071a0406140f030106050a0309020a060905030f010528020d06 75
    0x180d1244210040200440d140000264250030035020704203060405030b4034040803400c6008018010303c40503009400300702e08441c509000407051b44e400c840e0107400c0c0300119222859840010984000d41d080241030340c84a0504111580001034428040d0b6900e050802202200311140a195081004030300c16180003680c0001d15150000001c600450140701c0c18032002100d101150b180b201d90002c001c0c1d8552140001601164071444107a80240091130607611300030404c0d00d694040d402c040c0a4040507002c4001c0300c0703940081001a8001400580081d00e0020820050785200d802105c0c0040e01564039601100b100395414001c840241003680340001d01440d8441500c0c0c680e40150141c0004100000c8522426010900070350704050b198420040c507580c200642102c29800044e040428192a000040016904c100301d040140c0781c40c0e9509446249848201803900d52100f4580005e6403401c1c06102d20b2040070f440701c0000700800302c0c804456540164002c0002d104031000760144601d04080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 471161915 1250 471160665 471160667
    0x140a024204031b030c060525060e060604050f070e0a05030f010b0a0f0b040513092004290108071e020a0c050303120114120f1e0601030302030301090504060e010c 71
    0x1820540c2c1c0907480c0070355444005422401080030900011702801c440c60340030009148290003c0940c000921624807000c110512840d6844070421411108503481c1c0907a061108020017080394014001c480501031402d108500202100b4081c000f001040712400a02c040c0b03482d0185c030742e8014040074003168000300c03c3c1c5030b009008020220b1081c0c81000d1000000a60600c54201c0500740c1d2601407013149082c0c07a040400240b10345410078810840c0d100c034215008151805105100100f0900046442d0025001004101e80c4c0490940000402e16550001c8005e40031800b510044000c1c28503900545620b10180d41100032628a541449000c2d140d4961680e400304000403503a1182030144980c5484004050b10f90080b0002a40c210281c04010000c0641c50209a4048280a40402c0022903041800c4e4182002c03802062841c0e0703c0040c841d07104990340e548200049000c440500015415590000e459100c188222800b09454402003401d10210b58071403200d2030b640100806c1145040d0740 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 471163165 1250 471161915 471161917
    0x609030f100b09160f0905031b0406060504140f04270308060a080c0103200c06180127031e11011b09051207120b04140a0242 55
    0x3842050b802c00c00d40d200141082c59080303001d00307111010b050340144620340441d1803d09001c40340080109030000001d8544050207510510031407603080044218481003030000f9a01142d01c107108000003007004000e24000320400408206040314540042e00240700024041c1000d15641501500c01507030f00707004042203d051050680c46600d0b0300c5800d07640c2c0b20400a00701d5191048041c1074014100803403040d8401e6002c0c01034800800307400701c4280304c8004100003035045105500441d0b400070092041c0301011021044081111000a00c0300c0c0e51000301c0c00c0440140080000c40702020741595804250040c0c11440346011802490010240c03210360061107060b64084403140382d444c0c143c1040100200304810301c030342002a258100403519140520020442c4035900309114041c50a0204d4a52402d01e21021120302450310780c5034074141030910071003c0004d00305194896102e1020070005895641c403002c031b460b00d44507046040103807100030810201e04480c1c0b00c03151107840c91469146242820 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 471164415 1250 471163165 471163183
    0x6110301060f0e060d05070c0507080d02100b18040f0203030d1a03060114130207080c0102130b030405070311061b011505010305060a0509071101060303020c0f0f0109090b0609030f 79
    0x250300c0d03642548000b0000d840b0406041005078012104100500310828640c2200c0d80007040f9280402005000351109410084190860305054204110289403644d0411194031150002c0c0e90820a140a800014440c9600c1070651000c40510f100080e00780088a080c514456070040e0640e90f0710302800742c41d00d00811000400195400141074982014100000c1803816075241d20095102961060700700b04210031440681c1d03407a1902000510002a042e90140042105031000987c441500c4c09903038034400140d400440d51554107004020114a00240080849401900e41d58107409038a0100d08548283c3c2810501d0402540303403080c028a05601c405072644200850307031501521180110280c03082075400f2a0700510941060240345010030416421107a1400c0690001c00310109040c00c0d20000da0003980941c10a80c0312242d01d09080d1152500804112400c040c408500c10000e070140c1e4103409060403041d42d030b030380c1c40c1e4440c0c0340c0e2001c40d821074078020215040b10703480c0024a59501c04103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 471165665 1250 471164415 471164417
    0xf0b0103050c0711011b080403050705030727020307030204080327030d09050909010603120e13062607080106090203090715020d180b0721020f15040f0611030106 71
    0x8031000481d0700d0341e460140d0320038561101c948131800d0700950046a1900e04c60030342810004d07a100554001034220300007440110301c544040d0101e01e240500b05820010300394070244444002803a540440c025102d13840b4610700780d1550060f22600c13a01d0382103000740295003005d409448000313240c1220716003140503203681030351844640f507118201f102415244c0b0703510801c12001c01d4091500784010300d8018525079019115800004030260340383c40c0d21f030503500c125195402050210100020a09081c51070401841c48864240710013840e00881555a4450040e049a030300040000070354966014050100101324803402800419150030700c1c0f000a41c01940d911125201d1000b00207012140c0d05034040075501250040c0c01004c074045020390705d01050901007058056115404a0024820006080d8042c001c485a062030201043d0b0481008840e15000055502000b04401220700000700b2900100300b004440020f52900d00d44803005031240d0f80010416402c0c01d05e00801c801e031000283d4101c6480b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 471166915 1250 471165665 471165671
    0x903050f0a0e0316050a03060203060f1906020d17010312020f120a03180c05130b030d08271207060b0901091e0203010605030a09021c0b0711030408060703110d0f0b0103 74
    0x104e03480b1944880d9040c45003d0700409480310800c003040140e030140d0340c0210041c04c100d00da403480c040010f224001080c80188001c2c42044184071155040000d0010640c00381040c0d00c9003101a4140214024148001803d0300c0e5400300301c950f641d10912880801c1c40c203a41c100c0b00d401d040320401845130781207440340c40e0000f0700c1c0490701c41070302c0d02080100e8240c03500501c41d00c4015003403100b40702201c0d80340d2064149031070301c2c0c100b0031142c0d44042040f080c20a00940c0c4400c0c0c1424203c01c6014140307125404079248002200b032491034084042041b00201c2d1000111540d14400c0c4c1c0b5011015100c41000d40d40e2000c0640000100071400e50040000218400124039461000e40d030740307000700d00084c019000040c1c800e02c000391080340c6a0f4000c07041c00d070009050401502c8002501c0304031414400b41101d042020505100c2503a130004988100e0500120285041a040c0310781c1e182c0d541c000414140805071240c0e858001c20281104403280103145020502c90f0100624640f00900071300303c141800686 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 471168165 1250 471166915 471166933
    0x702010c020d0801030809060906040f08010c0306090c080a0e0c2707050c0c0d020d291602030702060a1e09030b0c09030a0b0402060f070c030b06030a050a060903050f0a0e03 76
    0x449183c1e05816654030011103030030601d92805000194100301344664015800308404154100c07002e088200802008002045101c8000300080681d0440da0001d401981000b5070300c1c00d00d075080802941d0042002c100000c20800c900c50062420341405102038001c05001d03840f50401d03003800d145449090807035242c03800f0f680390800e04949900c101d490f030040582110035125170503e0303c6100d106c02240010400c0020300c0803519000d48001165083e00b030700d221030041c052041e40c4801c008607880060b80c0700e1194041c100074806074607442041d4000384580e00000e12480d11034001d03c011079102d9800300f030a492100790500042e0860303c4500080da06500c00100040300003c03490120b80802201401400040d400c41d56203000742d1001800c201e0f071104007032141821600c54072002d05002170140103a0121070303241d428814070301100542414060342000703081b1004a03a0028010291950082c80040c0070030701130130100c40c0703070080d1070707020001040014134120100da101f62001d0800700e0440c245c0350900c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 471169415 1250 471168165 471168167
    0x1519050405040903050d240303050f0d060e091c0905010e030102040e0403050c06130f02190e0903120108070b1b010603060203040c083c0309060a03020a09060503011d0a090b0702010c020d 82
    0xd2692a07c03900c0d088404041c40020700c500080c080e684d9458000390304045014410f00f00b078606640000b1040743e961010400703000404c00c403114541440710b00280c0c0a0300d00d0580140307405141d02a0074107003d41891180c01603107003581194001c0c1012051550320341418030300109558081e000c3c102c228481da40201e00307801c0d6420800703280f03581e00c030046d440c0c01000342e802d00481c19060f001c0711400b584081c100064115101c92030911401d81c80014650703c100c064846403800034103811142845c7c0c46070344d05108040702c81c803c07280070b194072404e00811508400201c40c05040f81d604014000750011052004200401c10091300366680c00b0180c5901c0341000540701c0f00c980c096440140c60103240710b0505001c481e0000d400303048001c0070040d646050fa0000c007042c1664020081500002d0340002c42110441d4400940790140c5043e160452455152801f010083e80121005209481100d80441d98450785a4460560380354440d60a04d5a840d01c8100a4024078014000c503002d8060030382d82d6940c036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 471170665 1250 471169415 471169451
    0xd0b0406200c190503070b0910060801050108060109020f04030c0e0a05221e0503031602060f0c040317090d061401050d020a090e0f0601091a1519050405040903050d 72
    0x201c00380307005003890740f0780c0c50740b031804400c0c24202520580010403809000c00c100c800304034400da05110007000c0d10740303500c0500f100316402c07580410035603490710005000f64900410054116000400301503141c07041800c43d001144956400101000c000d000d00140100e400352016101d411038080802050750f8072542c19001c1c1910345480390100854480050004100c41c1150880c1c145070041c044030114103590f850301c0c0d5401601c4140c1c0a10f0212050a00560704200c4c850380a210300300c22448a040504030140103005c1ca010041c004801d510065075000c00240a5a4420a0040c01200000720f6420643c1c0285a0003000e001e0035a8a00c00105031400d010340020740e4079070b0241865610f249070507240c0d4018072031081500c005001d0512000201201000168007800e000c0200060099000341030a20704848520500e0003000c000310003010846044c003d6808a4510b4414513824008520044a080c07090360005176010b8500171101051650002c041c00d185842181e041111581070141a000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 471171915 1250 471170665 471170677
    0x2b06061e020c010810050a0314060a06240302090a0303050c01060506041a0313020d0308070e0a030803240402040b251113090b071d0a0b03070e0d0b040620 68
    0x964001e400e04016075101301681980f0400d100b5042c0101a00c4900003a90f0803810b074415145a24451085100d10b00240030054101040c8001080060301e00302c01c240d1403115055500000680c13113071000c27407424007a8045401d1800d0040c403070b843c0d0a4a9140103080e5410420786500d1540c070380103000c00d8908024044a01b0b46c0c680750b00904880b03442002c2c1040d65440100b00c0ca60300070301c05a03500010785910140c000314901c6620b400b0005e00d0407250003800c980590803581d1141e84201803c02c0491624411613421280d04122415500c4a500203c06070381e075403800c01c44e0000e2000030300040b4010204080c08240038010194014003044a04c480d4202160200250505226081d00365031440c0c0344244045e02503403000b000c111808281c0310051324400480d80080802c0d00c1c000d2003100000d8100303a5140400c01160b400030500c0c02c2400741c200600006200d00305119203203e44070801d6884850703201c1c250394008003490341440c0070720748103014101e4080e00d40c00005500440da00002001025111 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 471173165 1250 471171915 471171917
    0x3010321080105041508010c03020306180c030a0903180906060e030609070608090a0c0f06081f030b06060c0708030421030203070f060b0631050a0302062b06061e 71
    0x78590824081000408280000b42e0034001d600b840060592828004c1c88026603840c3c50058a034075158050000c01124164400c000c483e0440c1041042e0414606070381d000242000001001080c500d070603114800030b40c1110302e402680d82c1d80041e48640c00e0300710100380d03002390b40c0b400020401441031540d01c407015101b2843c0d03070b00001e20901140c0d1080c0d80c00c990256030300b812100400c6042d2580540f400a940101c20803400c9910240035141d0492140390304805049250050034000040c92041c14425000c001c00b41c01d914004100720b03544034000c0d05c00314403080094407401d0b5a50303210a5505d51040c1708400d2a030907103004c611a010604010103803603a4050b0040d603d011201c0c1e0340c5000c44601041e00303c1b03140b070f968152400961520405070000e501404402c184486840082800c0b1303401c060800c002c4420b0909062003aa12900c006108685d81943d000c0d4403030b4124080d44101d85d85102845000300e2808820365154491a000002246c506454000842080700e568800c219841a4008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 471174415 1250 471173165 471173177
    0x313060b030109051f200a02150411190801020f0904050c0301060804030807091502010e0606120c04020f0d02160b060102010c0e0f0a15050706180c030b191103010321 73
    0x24400b001c0c51011600a04030308800210300c40d020068443c132494040d01b02500040108110f0741840d0100201c0c850b071703400d078014110b0a1400da960f03120004c04040045015180b20309a642030b4191032031452000d4990342009540329a40520320703050381d40081c4500c5104038103010100741c540900d0800c9a058545542c0c84c1c0341c4c950f846403000d0b01d000302d02500c98020004402e40c000340340211080d42001c41d107503a5002040312150001010700d00350014005611402512003100c112440c0010021040082502d01603150040c40c0b000d250580a00f00300c41c1c0303000380006185003604e498200024800c500c5181c11a07195101c03000124221800320910001203480e0044404240c40e1035042003c80e00c10052580c81556200c5041b0003d4404910007039010400c01f088a0341041720381d01900f10403850100421201c0d1005032503486950201c1c2c8006080344c1c4010011460800c56141c91400e2600390b05402e2060380e205003413210036940248425179944081c07038411441f0a4003030700f000c01d2054580da560 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 471175665 1250 471174415 471174433
    0x2030115030b060d05070302060d050108060a0e1f0f020705210307020703110f030f0d14070b0115050c0102041517090607050d2003040303060501091512060306020313060b03010905 79
    0x200a03045130340c1c4001e860074441d40000100680c0d41000400b0784038481b40c80410390394907001d0400c1ca04100502940301c0d0b03d0520f114a10440c0d4000340141801c0015030644128945581081d0010840d51100c8d400301400000d03450180040060702d0591402c0340c065560307003070241600070083c90009440100040c1c03c001c07020400720b40c485400c10030f0a07100070f00060280c80b4080000b854001c0d0781c05000304a41018400190300c58002820452001503544028503001c41a55558907018050007000a80484031350b01103c1c00b4841e4041d03404080068008550301c070b40303035001c0c11400c070316441949001550070350f40351603054400c4140c41d0107507044800070b0003562540d1105803815003100d4900d4a24a0341c0c2c6003d640f00750079078000b030b06020424102e8107a680c2802e040c0102901d0803074010a043c484041d001b00603110007241980310480c08e61401b080100a043c8010014020035071024103014000b105101c080005030302c020709201d02c01c410400494280c501458242d8000303032000340060700500f0f22 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 471176915 1250 471175665 471175669
    0x6020703020708031c2310050913080409020d0905030d020c060709120b04050316060515010201050103080f070503130608070306050f061c090b090618210c011e0902030115030b06 78
    0x30241c01b0405002d00c4004058103800175044020003112100ca81080c05102040a402c101d400207030000444540c02d4113407441d030346408600d40b1440c881c541016034009038441c91602c5130740c071907040c0d580e102044e2952220507042c0d520207900f2554201606004a002140c07149014041c08003c81c3d10b09020300769901165250401100340c028000e89980c04204100750034400e400111031505403141d040050542054202140701318081103080781560315200050021135484400d403903500003110307112540e507034203850b0150540c003486900b8a500103011801017003040d00030246500c101500e0b902005426034880c100300e81c260011241c0c6401100130002011015900c0c6191104101c021901050b848001d40c2c6540c1009401c962039030140e046a0184294000005800402030501600908040c10690a41081803000c0104440f40c00c0d4001a1191941001c1d0442140750070b0211001000d00410b2581102400042100700d12951905464501034000c900c4c40e001500d400400c03400c030540d15801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 471178165 1250 471176915 471176921
    0x11040b03191e09030210020f0703020c030a02091b0f1803060603070f05060904060f03080c10020306100c2a0f0e090c0402070203150c07120c0201021507051606020703020708031c 78
    0x13a000c602440801c007401d0309950000b8101c407211407402583d29181741c10021b09010000f81c5851007170304550a0380c405a07803000819900140384006050400b400c80c132581186100300042c2c096a00c60104010707914510320040c061071000103070166074540d545c40d020951603100900890003000000c80091045082183c0900189400680000b5610791200d000c078001c2e0850f540304441d030034000100344d0084403042c03202e240c3d14441c840003941581400c07000240040b41205003d02000720381c0015809010a02c161030010740400700e05d030b0f4480380d61070031890406002d81c0248218240c1040700001c1c00c0c0c529000b401e01c601080c0001c0c2c0f621500c0082040085e500545051b64544034210401c4048550342c1c14050184548207607840e50b402c280d140c5030620740c01e0000c02c2c50500c421040e451016036000704100401612350060340d8090350b00e0001c2903c89000d0031030445405d03e1a5031101040103017030760092140c2c0307009030210342d11240e0302e01d403003a03a03480b17003101100c007130040b44800c4900e0340d030150 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 471179415 1250 471178165 471178181
    0x100b03030702030a05010b042409111c06060906050a1d0f03070909150506030c04050402040f0e030c012a05070312020304150e0f031b0111040b03191e 66
    0x1000c0d603290040c2500000d261513042c031020344070340c1d5440703500841d2481c10384a0403400103a00d144460110f4905101503890309560710402207401d80364000610001003104c2218a282c50840060f092400003101031f0008100901640c008560900d00100d81d6a01500c1039a0010340c165481c048000d24204c330398501101d182811580005e03114800c00b0f4296400d1001d44054800c1c03071400120134805c0d06000385d030300f2140c00c0c0351070b0391a24000500c4021385011441d03005081054801103a81d480c0d51000c00c0041005c0c1881c0c0021525180d0810400c1c0000b01c003c00b005480302e002400f138000d80100401e0300c2d2a8002103203803140d41030b501c015400c60160026100e0076010b800d0000c80600480740c1c50090b0ba00441d81243c402c0341d02c6020750341c035070701e00d101d40783c10116454020b14046c4c810b0701942e541c034820b06d0401c0c1a4a6001543c030380e42c41d0002d410804100b045070400c90b44569442c41040442c5e00700341d80810f52915082031040162015105414403201c4114616191242c040c02303100c0240401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 471180665 1250 471179415 471179419
    0x2808060f0d05070e04120201050709120b04020d0503131802030601090e1f0b0304060e060c16081903092001020a0b0903090406062003070b0c0a17070215150102100b 72
    0x400080040c14420344134815801254000030703601c0003020003401c5409c02803904003400965041840001072b00800183e170315a00c0400c0c02c00c141c40b10700004507c0c03020300c40c008200303200005600080050100425044920400c07040c910041040712420903400110741080c0044c1c058a010004007900c0701c0d207690404200c404010003484058011004044150403400b210100003090008004240c450300e88413416100c00b8106c5828901c41e956a80c0c461300c84c10151102a2044250a00c100441101c000c403030501c2c2c40081d605481079024000c0e0406250540b8450050710008031900040480040d02410503800340a08242a03640c504100340060110641c921042c821880707191680d10444000d02040d4590007031000e0306e180b8411904040301c01c0700d411743e0030038041c0e08006400098540d1300106902c02140c1c03074049107401210406420310036148080d6000052101030741d004590a100340e801420400000d9441d81d451a8110f04c1e4003202c41c0c016480f40300f03043c0c0704e41c2003940030001074040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 471181915 1250 471180665 471180673
    0xd03090f05060f010302151306050c0f060f100b07030504050d060609140612150406020d02090604170c0402190c0201091502010f06210b06010201060b2808060f0d05 72
    0x1034840360b1070250219440584145500c0061055160080c0d500440090720021701e032915010f1079a541140e02c4034403d1a041c05000326039519015030600074803080305858412036415151020382440d03500c200b91034420010a08401c0460744401ca0170440d1805505a101c440c0390524003001c0c0203803865640026140180d171b40b840494100002e00806007070180e16845503495040c00806c00200448444000c0c4166000301c0038150b4030f001c0181a1584950020001600c4000d10b1480340040d2043c401443e1b8003050011b000b0507405158800c801210041d902190450304a0100f800f089118891008650300c814030f002d803d00e2446040c403040500e1042c9414141155907528240c01100403207d00c2016135103898800c92007021511505c5c00415038008620208092003880103503452180303201515175034024000404990007500b1100007070174200b05a070b5560040000c0414410700550070f185d500d442d10102000c070f880c03007085418081d05001740901070fa40080b00030820481e0140f0421210380c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 471183165 1250 471181915 471181943
    0x1e030a02061f090203011203020d0f0e01050c0a0b0c0705010f05060a090f06150203090126040308090708030307051c060501050409020d0902031c090e010602070605220320060306030d0309 82
    0x1104d0000d10300a00d003181c86204603178403e01e0041c1c20450102120030411142c5442c0341a0107600c0040740740d5026003820240d80d990b40c1c68581608258084a000e000c45400b842800281104c2d5002400d446015100030070035541c4600c440345c01e480d02928900e61214000000340080d0141c0d51000e44006100d1100080b120b64505610300890900c0c141e100158001150940d81ca58004125103010080311890200c48022030003880c2c0c840b2006070015082061607000640c0703010041140344054090034042300d40742d2030035000003011580015400c0101d1040510b610010820500500c402d840c0142c49080c14141440f420000a4018000703501c2d0341d503100c030325080258030305002c811a05c1d010140c1c4501c1c3e481c407580c0003424052481d4002d1a01410b000010042070707902103000015288580307480360b03441030104106035034048078904010f22462a84000010481404074102d01c0407061070910800070100c004000c1ea50104a075010340541045c07110440440c032a501603010b0f05d214110541c5140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 471184415 1250 471183165 471183179
    0x90b010e040f060513060b300f04171314030111030f040203010e06010b09011b021206070e190e0c040f03080c060c0702060a11070b0c1e030a02061f 65
    0xc2c1c0d074081d054405a65860284103074100980b80c0711650640c90428840149071500c07202c414440c40f0b203107044002c0f242c00044680030380812400000500030441e4850b5042118044003000e40c00d03602103512000500601c25060014001d58111400242d02e507518285442c03440b81c6001d5107001c3c5a03606558075004031100c1c07014580038500808040d1149811860302d8030600d42122907117145e605207644428010041d051424040b01d039201000c1c40c01d003894038005200388c00703030014440b8000d6000d40004070729820100001030003845001c0c00d5460302c0010030b400d0288180e1030005100380a0070b0340105c0c814803c40c40050300c5640c0140c0490140762520380e840c540402210348642040320900300010741c21070207aa00b0000d0f070f03800280e5207100c146400e144d503001458910840a602c400d000c0880c046100904044c0011030003481200101695000101e200680b615800c819448624140030b6082030000d1002058800001c40c0e60000e200f56243c01c01110f07000011025070781058080b51802103500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 471185665 1250 471184415 471184421
    0x50105030d0c0309080102180a06110a031202160b190e0c0114041e0603060504110409181403070c12020a060813050d1e08090601230604060f02190302030301090b010e04 74
    0x114900700ca88e05000f20310040080340300596000720100404076000b40c002140c0800c48404c1240e2500b004a501c2c40e50b140041c01034010b2542c107040000d41c2d0701d5000c0910000300c0d42136125a4403801d20310208070000c1d150f0320485440300d8001d8101c4e03201202495407540036070184140203641c5110070307081560341c8042c0c484500d43c00840d602c81c02c2c03100400f041055054020803002c0c090480e400d0000440d8041d1100750b601541c4130782400c6d00e89a5000b00d00d0808072001c00ca10042e00540222004411860306603907a602448045401c010114000501031400511f0340301442c2c0d004018400d0709190800071070b10b1000103008244c0800314000041c002480c108500303e03100c691512280c040d0a0710424241603500405692800c1c0701c2520100503540c0808517440341900c104c06084c40d0700c1c9108030a04c0380014001540107810003800034001c02c850340c00c980d04041f00d550550840c0c880b2000b0a06035142d080410307100501513842840180a20711103a0031400f403003501850880c845800d010006815 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 471186915 1250 471185665 471185677
    0x30e030403062c1b0427031d0411071202070b071a0604020a12020c1608010e0f0d020d0f140a110709020c060114062205040f050105030d0c0309080102 66
    0x8003021400c1030895482094071240d440c0071860140c10b401513043d620b11010544c10003003601c515540c1820022680ea200504001c013105100034500000d403d1501410031040000440c41901d40108101500d203454002c030909440d840e2500d41c1041d00f19034504035200c0d0440b66107410f6002c1c00d400032502c1d03c00c98000d02811802542c40c500d81d09440c400e10529180003070003450103140108007c074031141e000050542081c0030a800140d8030303201034503100e041030b000604041d0401296103000500200541022407110140010f60b41d00c00302071a0881d036208100820800075810041a01c266a405290100b4081409062140e4861600c40d410065540510107020218042c007034103200703258040000308050602201c04600d04480510301c19907078001403141d400300540c10014542d5945401c3c1c00d85816010040b0034494081c2c0398030f11400212914000d09010380d1800fa0060441c15030f40c0100c904076030024010308803601c00c220044500d031320301010039418401e0402c40040c031003070244001c0030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 471188165 1250 471186915 471186941
    0xb0f16050c0405070c051917040b070605060904150b030309060a020615010f200f070308040e0c070c030b0a09021e1c05060c03090c040c030501090b0a0303020d030e03040306 76
    0x401c400000e0030002120350243c404420031820b81c44100c0050350001d1300346002c01c2da0030003100b1000040e160007914006406603400409901090004041b80c40e103015080300d40c85850305110b140d0b070300424002401c20403100940f900e0300e00510400074007460341c0000714102c0c01a095070316142480d80031840c2c90348032a41c8040164000002c000044a071252041c0c1c04541c240790403000c0398281d1070010301e50b020041c0303c4030501041c220280c445010400c201c5000f00b40e40400d443c0415604d040401c0c10b500a0701c900e100c07818000740020034004261080b103400543c4004a90380c001e041d074888020664008080e5481290355090090150351100016145407200700c05405000c2030398030910035281c69400f01c06422a44d15410703180069000f051055225000703a034400d880341e44c1c20028514110094410a4116140600b07a920980c0e160300014180d0701810001d0240c1703407100b020b000394500180b10203001600305940168065109800800c0800d5803402101d040548a4940c60211074002110715 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 471189415 1250 471188165 471188173
    0xc061409010f1a010f02071e03122d0e09040b24060405040e0307060e010c110f07031122020c120c0d0e1203031003060f0b0a0b0f1605 59
    0x800d000c02401040d080c2c103520030050101c40400c1031201103040841e220300d4140904210a600214401c00408000b003911018055603000c01601510b608207440c0030a8494200c1c22100b002800e0080078072007041c050180c1500b00b800025900e0444151050409004011103d081400c4c903585901401d801035004121100050501038040044600c0001820b14004c810030228290b6503109001c0e58102d8005540104041005c8210642984200e00e4002c11452030a06c2c05550f4038015071060820b80352503110007003100c0c403a2650541c4d900c181c540c45840e0303a1180c5018400900080e00170850030b0000303040d11220701030002080200c42004101d884030541d0120b609810344204100d1130610700a0320130514601410400780c0c0362601c1c0d40c3d03040744c400c1c02051001540242c59960012110300c01c0003040e00e0312030900c0b07401003044100d1440161403090519110441c008683c3c4214110325800800c041c089901e007030459039184d040610b00d43c6101b64140890403018074403e14550045100700050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 471190665 1250 471189415 471189421
    0xf0c0312051810060509040602030603070b1b070506070b0a0c031b08090d03200304020619030e0618030412110a08060703050109021306050d0605030706020c0931030c0614 75
    0x2c5403a01201d040b820300100e0420004110755124108001e40080e00220056500e030f40d06400300c4d142c00a180d212003000340000511140d4510038440303404581c034158040e2140181c4e00c90410800c4c0c080c691000d49042c0c0303c0f80105594040e980d2007400079200c2800e0220380585a1550411b0100c0070300c080d540401c02d800300700107807840184104020100f860030704010a20003491703c0010400d400300c602030012000004901556214401d07a02c02206064100c100c00d00c03041c0c80100500841d1030011461710a09011a01d02560007003141c018201307400083d41400d14009819001d480c5102054480c031030100e005045980b280e10140c40a000f903100184018102031400608070341c016400141c038940306014024044401304421001c5030124900700d03484201d080c80c000010301241e805242d00d4131a4150003d400c41d008a4141c184031021920100b0954801c440e1004032101d40000340b01e0302a80c05500c1d41700c000c0320b94050902e64002d10305480941503940e140741c00c03034600260315882040c0c66020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 471191915 1250 471190665 471190711
    0x30a050a0201140c0f0d18060b090906250e18010510050406050a050d0e07150e0904050a0f0f06020a0306090e1f02030a0b0a0b070201020c100f0c031205 67
    0x10240c0e1070714402c010030302900d00780031300316468001c580441000c22030006d62160b0088003a006510162a0166402403000c544d00e0b01d078005000c141320302400b50180e400081c00800010604a04c143e21046105800c05a41201a001200c01d903104c142848080b03c020062500c80d4032a08440c8131903c401180554140020046108100c1c071a4008120f8100024001d16502c141070381c82507010742c288541c45030882208440a002c10410504081c401c03014001140d005400110201400b617860715240020144240140104215000340999101d079000f000000d000300245620540102500e4001c9449a581e000581c0d102601c5500003035240c09062200c4005449840480c41408004140001d00d41111112a0b41c5114002d81016804000130b1444082134100103215600284440b400c43d44a086421483c0c201c0b0b40e0990040c40f07180107a011504026031140f42d0070390141c60702d118a07201400c04407180b03c003030b8404804010381c407408003905400500600e8095040318071100fa010b412181 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 471193165 1250 471191915 471191921
    0x1512160306080a050618070807090b01201c030614060a030207020901030b0405070b2a070807031b08070501080411240304120305060a03060f0e160f050603010312050307020a05030a050a0201 83
    0x84650860700447d00c01c00074104002680021510030420100340e102c000380041c1c0d20240b8003030454100c85182002c00e081000c0204000e1402030990380d85041d1002d40307a004408a0346035005145010000c0c611403c200d180031000341a00001c02d2802524000c0703564041106990203a20031103030714017100240420050284200383c00351240594040c141708204110803915031143d52526240c44901c091803103d00d40900800c40507008007422264607558034906411480e442c06401c0310b410703051403000304042078080f48141c00c84905950301d0402c0d494079100c0136082c4104cd0011640080b068070760541603804407000541001d2001a0940c80e07162a0514202d0342d024001c0401c10180390030100461503071fa10242909a0360429000190401206072880041c100381000c102e8600c103005080703221081c01c184480c1519070503004505100e556109014441c0028080100004440701c0c20411961040005d1a13119401d84101e405814150301d880d801d41d40500c8045001880000305072001c250240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 471194415 1250 471193165 471193201
    0x60305010501021207020415050a0f230a0e0c091504030308150109060e0136080c060a0c0812070203090a050909060412050408010e0c1512160306080a0506 68
    0x200150207000840a040322441c40f8420009104a5131241400023040d40c10b5059005070401400450035181c541201d0090300e0300c2031058a81300e0620301c10b109020900482001465800030708545402c1d414119010840003000f41821007125040c854040c0d1580e41010f58088000e5003400c042d591400d50030003e2480700300612901800981c0c2e01240d90a0740c0c0258101c00b00c1d001403800d65568890380f40100c9014803052030004003401e040450000720580c5609407003d050100d03012210195440a07095103a80c5601c01a903803101c0d060100c0d00c281800f51b90481e403084d120f44a86841c0010800155203114401d0300ca4a0040e8008280510755092001c03018001d00012560115035150600d0519950b8000500051542061b200c1000d84940918251009014030000030301c40c1480c82d69445035240446103005d485842c09480914030302480300100c0300e10286d0000540041d6462112215541c2c4810074203108059480000258404060141d035500612440240c0f1080c00c140c11241d00b481040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 471195665 1250 471194415 471194417
    0x30d14160b04030e0913030e01030f1a0a0501020f030f0307030603120e01110f060406020f04031208100e19150b0a0302071b05030a030e24030910020313080d020d0603080301060305010501 82
    0x7880031b02030100d071604081850b041c1d1528001c0226000740c40101d000d05500c880e9a06002e0400403011040b085400c42101020419690714010350b55a00c012603891b0004150206a030b08200800c000311140d900046034032680360b007404a00343d031b40c95540341d418805075449000014011043c00b141c0d981d20400018025000f10000d04001c480c1e12002074882388041c1c0f008100b20f5000a801c800c0d983d4507400d807802190854a5011101361680300900320480c201e50342c196030340300032401042d11041c00c0c3c2c035107016005400fa02e110403621041004c0003412808150310000c1c88400c00094007040440050480102a03a030160312016207140c10b0640010364a200c28901c1205c120030b004544001441080e0a5050301e80709000d1f040200c04aa110002b60180c4158031440e10400e100711403a107001503008e04c02d4101124008285612841c04a000a45450b01ca006000c01c11001043c070b524050084425131410040c03801c4056001002180c4043e07000f100d00300c00c04001000516091300c1454010082 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 471196915 1250 471195665 471195679
    0x1902030f22090903020f12070b190e010c0324060e13090b07050a0f02010c02030d1113031a0106080105210a02131d0c030d14160b04030e 60
    0x9144004140c1c040c40624041c410200e4030000400c28245108000401030071800b00710352212418000e4032a42a10801d1805206981003141d45201d000d00b02d03204150022004e410710346840850341244908a000c08200303944688600032041c10038820600c44070500c1c2c400081c01400e810218410040122074005402c21009041104940010301c401d01100c0440c2d49800e46a16a40000010304864202a00e40000700b4108428640c01000910190980741c40f02c0f200744601c01c030f040b400e0b0350f144891040103810030300c401e1004514a41001c0c40a0821140303960428403210800014800c061780242d0b1120319800b20000056011440c45014003064900302d80c031036040034041600040f0045d0759081c0164030400c1c044281409111500b0701c9503001b050501000040c0a00d2030240c041801d00000e4140562106807a020300029039060040c3e0103405802c600c8203d06e001e8411034001c28070700380300304800c0241141e50808550f05000b818480c42035040c09082608004000349003810401d806041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 471198165 1250 471196915 471196927
    0x1022b0909020403170310030510050402042a050a2021040806070c021302030a060302090702010c1403100807080d0216081b01021f0e010b04140f0408130902190203 72
    0x11410740c8160154005c182d403540d99884855450028000961024103c0c0c003804135481840396854115a00581c022203060042410050084100342030a40701442c17139841701078a0300c11107400303080900980724290a1181d0724400e5004540c007038848406000b034482d000b00c0f0b0001e0036504691420900580c1c170000b00d41c20103040580c59076513003501400c0c4806000c080b114441c11559a070141c0d0ba2006c0704003c06644070b0420b15032000150010340402ca124030800381c00105d0f81441449500002c845603a100d5600880d40d48003031000d80d001130447d0305000100280400c0c804801c100a03c001d0131100010b04000c140d40000031f091802c01c60603062810411311041000d01000600d1750b81145100c42143c1414008000503841c1c00d40c400018a0301801c0f10886141c412072035806612420451002030041780c2c0500c0421003190007040b40d2018012541d8089040c00500d150b00c5507100d80300d01c00c402e1070b24071108034903060743d48180d00051502e500002d02c0001210003000403003840b00140003c5003491 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 471199415 1250 471198165 471198173
    0xf06230a0c0f020d12020f0c010911010509060a05030901092a0e0c07080a020f0d120e030906030f13081204022404090e070f030807050d050306030a1101022b0909020403 74
    0x413050303694a00c20000011500440c3c810546e0481d403003030b000100a26940c12805040e14081c00d84050b082d00e402e0714101c503003111035000300100d40c50004001c001c6442d007035000100740c800350000f4110300c22a6694a10303c600041203c0d95441005050034070305a6860440f01700c0441484446d0840d0300b24a2007803040c40380451425095481c090782c0403082e140c941001c078008a1804c945281102d600c0e200d034409410190303030070200c110040c09054206100b020307440f00707180d6542d00c1052a0240c100c0400c00008602103d11485940c00c0f0758641380c25141f01c01d0030b8031840b00c4c540000d00108621103407030f01840114036014402c81c4031440c0c4940210309401121790035000d540158031841041c2c9481d0304140d44590310038801040500140250105003644905116110340c22010007112507101e001501c1a1540c01001074900c40e180090044c40403400c00c0d0b9440c81654086e4514906610442c459207402c0c482c0015003102d01c5520701036055841381121801000c10005031b03c06440d13507104010900110b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 471200665 1250 471199415 471199423
    0x1d0417190503040f02030109030f0207060216060e18071d010806090a0f0b130f0b060309071a25120e0904020d030507080418061d040f06230a0c0f02 65
    0x403080c0c100503440340d80302c0c1031081651007030000c002d505511341000801055002084180e0340001c0b50700700c4440075100d41d01641c0e200880c0581c074a0740c13840b40204000052003154a550516009091403001200900c3c00c807942d00c400b0384200c00800c0101305000d00c410441d010304031a9a81c246042c222a003032882c0495070402028141e00c42a40c0c6134142a442d50040740c110327000c0079001401e5071480c0e0350068500c2008203070256a007015142021803999051420400b032741d024075402e5001d41442d5250604401c90320085aa0381a03c06009101c42c0d50540300e054041c401c10700007015041d140304003e10342031060700c68003038201c0b042c00803602c1210916280c004d901640503078180c8015260745403900707007a80c50b030190850040100000090101d18110030088120104440940c1880229195201d41d0145041c1440c20b6600a800c1400180420170703150480321118011240010501288128403202d01c902d64a040010078814050203030604552090b1408100140703000030640782030304002922 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 471201915 1250 471200665 471200707
    0x51e040320131a0a0605030a0b03010c0504090c0228020f1c06150305190302160e040305180411071104020f0306060307050c070321090b0306120102041d0417 69
    0x42c40e550707555601600500c2c1d48018407040e90050554184903a1144011b0066104442c4e44000ca03080121a800d181014040e902400c12981c49080c1060b081240b1200103003181d014600441c031030030b5401081120000034a0f001d80c950800044001c0ca02030040c440d03106411020a400b0741c11101c40700c46101040000c03104551780c085400714041d0007955055214144c03a0300060414050490a0f01c2803142000400e880c0a10070b07000d0f503040c0340e81020100340ea229248100c0612030261800240082c0c8981e0003441e1022103d812481040c0c440b1000c01c0c100c0d000c800304401c0d2100c0c001045418089890303d42c01900c4021141075250403951066044103000c09441d0601850002c03020840c07490140b02950964001c89080700c802c10340e281040009407d030600c0c0300d02d00b43c2d10200264500340c414000381c2c00b0740d0500003125240d40c840308107100704070704c07035981c4055595403c0c0004540c86405080c40554026400b801040c0b504041c01c0c62102d1512100d00c100030003c040000c00e038680d00e050742c1d1040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 471203165 1250 471201915 471201949
    0x13140414010b0906130914180a0b0a05041a0f090c0306010f03291f05090709061125080106060f08060f040216060501090f020702180403051e040320 65
    0x248502c45842c0c5c0032100341c00e80c0c110031112801d02d541303078004002507010640b02d481c6101c0c034410f4a040321071990b03844200304640a0018192640002c03640005500070303540051181e828018441440c60350b4100300001501c00c8407400c07012006000103800d04104400c6614411806000203514280c0c4580155140d4403000f4000410f5984ea6019900d6078111a0b0801c21041d540407810b2505150f1000402034502d00c41a074010100d902040c0e900f01100b2180c03048142e0344030f1195080c240319003540c460509201d918590710440605c0c00c41980489102c864149180c4a03009180e03003021002401c0d11f40b1600700104114403905411003c90303016011540185041d80c1080f24080840003007400b84c481c0c01038680451040303600d0407003089400c0d40310314100e9454a2007042211048141c69080c2e12510300060340c81164082c1040e4040003a41040c0d800904c40e00740a49014001c07408000e50350102035001000b044041000c00511181c03c0070079550340801102030b100c0e0401d4100080310a1100da8404d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 471204415 1250 471203165 471203167
    0xc04173003060d111002070906140906040509120d0203060406080f03040e1003080a120524090606070614100f0308120403120501121109060609060c0313140414010b0906 74
    0x300c1401400100000301507400790046008800c5544044c0d42c0707c00390322810108a15103800003803031070845000785d00301140c001d154140e203440c1c1d4020840500b1003d46081c00b6805502542140041200d004041030f60400c90f016031203140c440c080000300e910a601c0480c59410055801d45000004800c0758299114644036274441d80720040c02c4a580700036500000c01c4103170005002072404c2c1c0c10001c1e290900007806002d1145540321440f84500e00005007540c1e03000782c1e114540301d00628245421640c44a4041d04c07890034685a62640401c0e540018540c2000703541141c2032254500038020480090300103800c4105981d461982c81034010720855840340e0f03075522001c01080405104140c400405031a00105211035610f03085a06c511904080d81140e440e000e8565890071400c107210354507c12200209050704000c2c015003808804e03800151550f1041c002003101c2900c450140c5d5001003e014814281d46500300e054080c8422030f007450348140b96000400004004441d0003104503000700e07509841c05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 471205665 1250 471204415 471204439
    0x9050c100e0603072a24180c0f0e070905042d0b030f0703110105070c090f0f0c020312060f06070c08012f040306050c0417300306 57
    0x890368444000c0720355a00032000002e01c0032056024486900d01c640417030640200241e80c0091a60241d4080001495882c0c0c1695060900380c484036052403000e0025804501da02c0003800107603142041440883d44100042401d100305407203211040b024080303146014402c1d08007120b02614250341441001c1c8140e455086064580913602004124815041000d0408040110802010f0b05101b003c4078000c1c07141000c1a02d001c840001c15504890f0040c0701c0514504045c2d0044403a43e000e100150b52992003c0c0e0006840c500c944141c031080c1104000004141d28982603580a580f207d40ca41c00841d030080c440c014155800383d00d103640125040310709540344880c0e900890b0301030190110287c0700a8199a0014030700c3c2041d0020700701088260030300450018000740c1d0403010140811400b034292010f10090001070702c81d80c06680c00010101000c0e06190740c618881d4402d140c020340700801504540c910240c1c2c03030405021030741840c41e90780e02d44103429415414820b144c0001070029115288000c03030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 471206915 1250 471205665 471205667
    0x304020f010504051905010f0f050708090409050f03070b1546030209060301061d0402060d02040b0a0e041b030506060909130b010e061521070309060e0109050c10 71
    0x842d0020136021300301c0e00d0149140740221920821600c24180801c0c1e248003101985446003107512009201500c44a0403d6001c1e00c031407d0507000400d803950000e603034140b0311010505c10031103001b0601c2840000d5a41c0d5005160002d01d400c00a450302c410350701c0654450002d541ca14031141030f1825003110814100c3c054100c8414500c04030840c00000000d40d8800240700e809840383d1800f60f900a4445003d80d848000078942250b219100e4600d141410080079600e40c5200c0440b550440d000070000c40c01d1034012403803541240d0181e481040320043c001489400701d6081310821001090848040000201031032000303044150b8007644804043d95031001450707552b1140d06462503007001030045560303440c0103c010f1200b90003842c0c0668040c0c080400000e404020032541c02e10946029200b14100b98881141d031403507801c0348a42c0f248040039600900714449091000780d1203441580c0c0c1c00b04c3c0001840c2000000c40320400424040c9904001740c81001c24000100c14805d1502941d020a003210312440c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 471208165 1250 471206915 471206917
    0xb0709030b01080705090615030105010c030e04020d0e060711030307030b06040b030717130507051002011b031b0503010305071a040308161101030b0a0b031008120403060e120304020f0105 82
    0x40180044050000443c80b4040001c0302d80c2622001e0f100f10f40a9241c1904200700b00e4201c070164800c0c4041040184a194416908040034a1203401c1c10729503101c5000028041e82c11030f02002c04040d9664104060043e01088095007003c030504110f0a40d5001028542c0c032440018003590905840d43c82010742a01c0c1c20045400800282c10707c240c403070401c0c0310001c001c8003070361001c5041d405084021590384200c0c1c0700700d61b41a13076004c0002c0c100c8500e0f01050020750401100c40070155540ca620042c08800c100c20148070310f000507900020306c001c032541046680107201001c001000418001480000d0000404e2810758600010070003244028401c0c0880c684a0354100800f10040811100c41000e40d00d200302c5c0969120755102c10078100c0460044044400b0118440e503c40d0003e50f04201c4500401c004640207646100300f0740815844005086c90101501c004c641240c0e40041c04000340b02c03003449074094000c410030142c8210400158007070f42d070f8000035002034403c07070083c01a02800c2e800f42c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 471209415 1250 471208165 471208169
    0x121902270708130213060317030c0a0305071116030203070b0414040b0d0f050109030e04140a0c0504080703140706051e09060d05150f030c0d030c020315040b041403160b0709 76
    0x3020001c005c0d00403005030014041c1c5100c220750030800b0100d000c080895400c00d49110302ea050040340d0421040c40d108801401d40a00b004c07007800403441540d1108a403d0040e170025201184050000a03e948141442e010460f40320b00030f0140144803e01210450071074161840a0480b008501001c40000203164007408a800500c2c20f00700500c40070401034103400040005000c0d0303c03841170604440080c442540c044095500741400f445000a00c3e40141e540221101080d5152040c1415140c0301101c0c9040780a40040d601070816944032100e1000c10050000541458600703141050913041d078807149078400c1d02040c0f080307041c04035502285491300e9040d120b000d00b440d44140b000d81007815108010446102c0020f016424010041c4020b08000411141c60040038140881031070503500c0481e06c03c14605800ca0707060240c00701c031030300703440d86404602d010b540503805286044c241464000030300c000b180041161608144031404140300507e28110300d00d07802014110096403514001c8400780290703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 471210665 1250 471209415 471209419
    0x100305090c090907080105160c12090e0903040302150403030801050d030210020409021b0715030905010e011a01080f06031005090c03010501140a09021213021219022707081302 77
    0x900811038443e9002402004881007078000f00060340341c21400740000c541180391180803400c0003a071000018041c801c1e6030800c0140e45005c8456030344481c0309010104003030300c0c544c41d00e60003c43d0a000750b00e81010211641c08014402a2611b032031a0340190142005110700d501c21031a581c6103005250080c00035051032200a03000310341d01c1d034a900746c00000350002c142c81d00054039101040b0081350340005400054445801c0c607203085d540c000a04501400ca60f4134119403d540f0341d075100f2903240b024001c070112400381d02c89540b00d4240c8000010034544008008045200d0301d4020300010341c8004c80c0702419040d191901142603aa0345601a280590120311503404d986800c0000800e41e840c000200d08850040b00c0b0045400e54500300c01c0140e0080005141e00011044c000c10000c40030700308056400e62029080994150401c4809400c0c5020903148804100e011079103002141b5120b010040442c85140034034000c04213500390825100c00013048141401150808940a43d510f0000a0500c03940 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 471211915 1250 471210665 471210679
    0x61802070f11030a140703151a040f09080705060f06090c030c1605150405060703060b190c0c090f0507030c0c0b101a1312030c0605060105130803030402030714100305090c 75
    0x1000792480e46d1041144810b40b0401a03002d003d0443c02540d000355194903810f81d4000e600e4015040400c40240148071100c92100e80e1020000000303150030300680040d0380a03e001e0300440c03a082c00d0f919500b1070b0085c21030748254902810080030340e1408040d02d8000758500607058407080420038503190480c000c9070280403440350040c0042e001403c0f800a80c8214494000d580d4181c5400b80700340c0c107035501e84c007400302c0d08541030201c9002c4064602d034540c8203840c2031510301000c1c11261203032010140250410442c650311440390700300340d4903940070303464102051389010000c3c0003084a0040142c45d401e4402000e03e500d50011a034040c3c00301c1c456001400d004013860b03580d51b18010a10601d41e00480b1005212001c61100041c409000b07484c59107580d0700740e1200c0354085070907610358000381401000141803000511201d1500030b41041080040c0c88540020b650301c2c00c050041515184130780e88400d04288100620032069210600d08070b2034031000f4203004c142070700c444903210306001e43c00003030306c1d04420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 471213165 1250 471211915 471211943
    0x417070b1303020c030102093601060c050c030a0c0605130509011518050135040f02010809060606090d24050f0c3910061802070f11030a 60
    0x21050300019070700744650202e641e4907241100f81401d070301411940070351005c2c1d400c4100e07040b21940c0403e580414040701c0d6840054840d46490b02c0505800c1c2c1000d80000c040300454010050100300c1128020707000c0f030091040803032030780c0c80310010519401900d041140100704009032a08440e140d4001d89001010209550385130000e15001134643d1740080002038015002c0c00c01403400d0800c403801c1d1132040c0d489506c840000c000f06507002a0720b044400303ca000350709940c071001e4240b103112401240318455072503904007140001840f104000c0c0c244059900150240081355030342c1c1040354040c4000343d510780c2d494591414a001451500c40003a8100c040c4081040d43c80714040d80164800d0480e49010341507511403680300301d140d0141100c40032592000d0b010380e2b441200c0301304080f49008140c3c203070704c02e900341c8003054541000307161104894200e446040c1408405440151071480710024403085040c03241e1516507944003a01000007410200c90704100c090551001d22a001340e00c0d40146001040740 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 471214415 1250 471213165 471213181
    0xc1b010606020c190f1a0d141803030925050306040623040b0c070215120f0a020c0715090b030903040e0a02090d061d10060e09150417070b 61
    0x40d4140c0c5681300e90403040d84d240c4a243c60031456404e54100c005034070310380350410044030828003240010440c4244188140e880c1511540212070000d0300426124400d0705000003149081d10f24140c0c0344019801c01e100700035142100107100482d03120000c00e1040000f04108001c000890f4940115400d4055101000140607190f0062b41840300d40c0c280309103082d00d00f0300000080c2e081c152001000d030701c604000704100c902c50382c001d410054001000c82c104158010040701c002e601030b044805a55508100300134540181180e10303944007008034410342c5480c10200e0f440e621044c841c000c0c2c40b080781801c0d00b1001d5035842145038001070074500075040d03664201421061b0b500d030018480c1c520088142c00025050466030700a039424520041c04c040d803480b003180d588201501d03001102c4542141c1038484000141e000704107006441d01785030300018003141856000001501c004002540c0c03940041d2910040c0100c10000990240d004035182c055009101402c0d00f4601c03d81d0300c0680506071a500380a0f0032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 471215665 1250 471214415 471214423
    0x819030203091c0906052b0b09010623031801090c1503060b030a0506130f020c1c08071b020607060606200d0c050c040218030709060803030c1b01060602 67
    0xb800b01d44040b120301d1000520305a081451a004250005141c4001042220f0054015010524084001b20080c540750303d141f0780f800b050404000c29803500c4e180100c5850911200c9180508480c0c0350042c1c1e0403071030491110719107450000c188851000040002c0712041001e03c0340d07144110b010002d000c00c900604045400a03054083c02c810310080040280c4128001c0c4901e00407203a04c0c5a4060455891341c000e440102002004030750494102034600c00650940d00c10b00718010b440300001030716104508003182c40c01c00d007200070b40a00c90068800ca03841540114017140d000d03450b450441e6681c0e03c24a00705155501d4401d000350451008500c250400c5119003001068170300a980301f6040c0c5088a200000705850801301c0303012a0040700419036441d1050101c1500c16015104917802a14800e0104080307902070140da40d0302031a010000c00c482d10301482001c0040429210510075503042031406900d901c005052418810f6000440e1610440b640803040c031000035074070003040004d039075900184d10307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 471216915 1250 471215665 471215671
    0x15080a050f060106081605090a030b092a270c0d0b0105070309030611160c09050601020d0207090c0c02030a050606010206060a030b0a05040201140a090e060904030c0b040819030203 79
    0x24a02a0000c1c0300c508640c001912812691555210086502d03030012800101480000384420014104803900c0141c440711480b80041d407041840340482d1400c0720b9428141401003140010104040c00709c00c0601c0f28005490083d503d080307904c82c1c010302808600c000c2090021442c0f000001c60a401c0000f0407140f4800740051101a0344180981d41e09100111054490300100070041110740905101052542d131207242c800900540c00c42c1381101403101041c14102140c2e040b40c03504803e0710b040c08804014020580c0004080c002803411136403540020751685032500a6003101a51072440d412458450024259800d4010b81074920320001801c1540c1c1341d0340121a854054410400401c1481c20000704040403a03400840c0208a40c481a69102c083d12028109904001858070b400c1c250707000b020010071102d402a00e680c0810b40c9040c1c0072591007400108220b2199a41c03200f0040865000b14000f0004c0307900032604641991a407500e03e55034055141c2a0f0f0b414544084100c8841c0c1d00360b401180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 471218165 1250 471216915 471216923
    0x6210e0f100606081306090c05040911100804021804051002030c0d0b1c03030f0b03030f0a0909090b04060b0d0506010909031107060e120106091104030b060a030809120115080a 77
    0x31450343c5440050707400c00d0058584c030070002c01d28046100810041c0d4441c44c1310342c0c4550b4014146c02c0d0380d00c0004082c1d60701020151241000148484d0107464442b007032100c07c3c41c40382481d40b06868a43c00007903403003415454843c5441d11020029003040f00c140090f0740303c08040c1c40d0854807801d0260000015402c0300340050700c41d0349001901d00c11072420301c02804141803000b180041070401658100d02902040c01e100c42e011303481b100d01d2a469507003030010301001b007001c5050303544881c80c1d000000c04588440d07200780d0000e4900f0b82400003198010381c04640c49508024003180b02034150010417004110040044c0881c040c903000464849603c1c0c008010b84d038047d5454040c8403407071608582c1c540c4c0c05440341c540440c002c641e00300c00c0c60405101e0f02180002010002a6803540c2c3c11404041d1943c1c0804e1010410000130248100020800b10307a81046094a00d4040f550540e50342460300d200e1200c40c14810242245524004502500003940300e10403421041111540c516401da6100090a000c131 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 471219415 1250 471218165 471218171
    0x25060506040608030d0b12071205061005240909010e01090b0f03030702090c0d0903030c09090e07050f120f010f1803021203040c171e0706210e0f10 65
    0xd1400d28003802160140e41006000d10719154130307001d01000800079068600d81020312a21100690071042c0aa2801004a02101030055000b880c0050402c40300522032030300689580420301140d210000070a00d1400090781d100110301444482c12060b01840001c50b034041001000802c8900c0341d04400ca040b550115024040071039003c041294001d2008289078059000b0310041000d1300d0a09600c0750449460500c0078038284d103031000c81c41501c4c030300c8609401090b1503600e00d903038103a4070440c1ea20042a80300400c225980501d1a465124511881090710411107260003c40c155180807001681d9003801040b06c20174004d8520050284c40003080b02d4481ca480e1401c0e00400c000055060101c0300d03072540c00f624510080008840117900050300655612085000200d44075500854110308409102c000380030a44004201c1107290b10196200002a00319041c204440d541040705140c9946004210704c10213810580403900411240c0710407006841458105080114049641d1310907100c0301c1014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 471220665 1250 471219415 471219421
    0xf05270a020d0204020304020f100f020d0801060203120604020f0406032007020a03080711060a030e101b320d051302090402090403020109060501081e120a14250605 72
    0x4591140e949000103504181e41210b09030051a00390300940d4000d10081c10300798803030005400708140d5800e031a00d0001090803808981c2d001901004042c862404070700d05071104d9810154020344078001c3d40c11035150744801001140066072180c0645d2001041d040c481d81d00c0725a81da00080141c07248245086a01c152545a42d5a84009100300c1d00455006000301102034516615401541d102c500c05492040c05010f1f030000503526000117051030300c40d996001c00c42ca5800e114440c28010140c0c0f0a2000c103241a00228907640c5550401000000509040408010792211841c05240c20010034861038024a2100345802802d0007510800011640c2045140e542c5844c05c4088041d01801079846144000010018039000c1000c641c01842480045208035941d079903e0103460081e00724840640003404030340001d07000702012142207040715000740443d4001c03c410a50030700c502c071551820024418101032001c1d841804031141a050880c4a013101c1e50541c0d00132001d000c9002c0103d4107a0b040c2004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 471221915 1250 471220665 471220741
    0xc1c030507050c06211807060f171503010e060919021201050703062306090607081605060117030315240f03061c0b150406050a0e090705031209130f05 66
    0xb1b607a00295000003c01d6614204001940c0c014280702600b001c21a40e8001092900c0c22540d00c40d0141c80084505070b060582d0800b05030944006000f00c540c180d0000741041244100081c080c14034400c0d40e50700c147d82d450640042a000e441c00010b25403151700380014002c0665060b48041d0441d0138001c8000d9800840420b1030312840c0200c4481588114280005002c40c501000180300b424400c032403041c58603070110b440d020007409441c4117807201d40188004000141c0160f80307210049450300c1c003961079894901c0341e120210075050303400d502a00d050308060308000d64082c2c45440e5802c55030322030790312140281c0180c4030b5544100c2f0110b010303080303d0300b60f4030000c60389004145080d944000c4014a40d5507039404050010f00c00300e241d5078002d865103c0040c903070300d0750b030b5502c005000303858145581032410841e0b051034005079600c078134041d07409a420a21580801403d550030741d84121303980300e000044014000082c09130380580079a4140b400040c030180c0c4400c40c111046c1e041d01400340c2c0220b42c030000c0c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 471223021 1106 471221915 471221941
    0x190902040f0603030e0612010312021905070303120606020c010e2b06050c070b04080a03150e04021008090714030a0501110c0c1c030507050c0621 64
    0x1005100307145d4480b21841c20358200741d80703907442d01c503405580c40c0031103405100243c001c0400014000480e80309000000480074071101050041c0328500341240c0769256840104c0104146002c580c190030828081d1408032101038002d8074207800c0348030042d100a007107030001c5a40002c40c41da80000045110071040072407004407600381500305551800b0310440788080c0491003002003e00c548400602c642d419680c1c0254082540b03500ea111890b4298058800c100c0400e079190700c50b80e8041401e50940402620460080368400951040c1070400e444000059500030616006413105000b410815450601020320203012500c1d8096a61121800c41c1c3d03666402c018603402c0080c4002e50b100c0104030309155120704803820843c0112000d450456140d030300c003000b020701c40045480e40038408117004514681e040a8090380c0c1d5403410210126043c01240b100f05801000300011400d8002405 = true := by decide +kernel

theorem cover : BRFrame.Cov 471043165 471223021 := by
  have h0 := BRFrame.cov_init 471043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 471043165 ≤ n) (h2 : n < 471223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
