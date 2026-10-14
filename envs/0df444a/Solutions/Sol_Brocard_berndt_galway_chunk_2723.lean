-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2723
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:33:00.574536+00:00
-- url     : https://prove2.me/submissions/90445057-c1ec-4839-b2e5-888557eb3d04

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 489568345 ≤ n < 489748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 489569595 1250 489568345 489568351
    0x1d0606010e01050322021f02160506090a1e08010e0a1209030b0a020322060c18030b01050409060920040b010906051207091505070c0e04080d0c02030f04060810050603 73
    0xe110312119022460f001ca05540c5036025100a01203050078091280c1c0c00850700100007040010b2740081d505070078800c40c079103500001e0141034035141e01d450b00b40400f0450f06c2c00c0621411040300c00c05a6045400800700c440603001d418100000d03c0400d15003a00aa070341c2642800c00d0701c8180882c0300e130382411070044421604680c3e00803c505d419580300d645c0c40000350030003441c4c40c000c410100620781100c02c10241d0110014031175100050103113900400140f80100c2c14032410b8041002c0742041c0042002d195585045481c1101d001c41d03003400d5031400c20041d2428000c02044000e07071035210040d4039490f0500c10368280382510100400801c48004503182d03070852003080301149081003141401c242e840e00d142d51184250501c2c000307250360364001ca000702d00e200c0c120b00005030300800e20100300604404504010203420b07070680b10504181e11500383c140303c0c480c408810242e5a0049240b41030007442a41e042d44185c6095a48441e514200a0080079040318070b840e0f5004107010105a80c03401c4800d90380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 489570845 1250 489569595 489569611
    0x120c03213b0a020a03031425051513020f030109061e050a021c05061f02030d06080f071203020106030c0e0109051f05010e031c09050118150309061d0606010e010503 72
    0x42d10b5185441c1a141030070200311f000740500080041040e001d200349011010b4030940703040c0c1c3c5954449070404a0524140484441c0214000414841020b01215107000c0c1ea43e012142000c100d0444c0001900515000c0c100038107040c107103c039060740e0038004105d911207d851140103001e640d4400004c0c0080344100950350005078045c045005110686500550b4000c0020300440c510b100240c0c81c0c5040b25244450702d50043e4400500c0441c0c40703c4030b014060090030000c0080030009101090b594885085000b114000d8503001204410b140c800d411072001140c00c243c40c4080c50b61504c008800b000402d019140406003031001007521891183c1020601c6920b441446000034203010044840c2d15040061944c144140c0300d44210140c2c0030301d82000140c120f40c480d10041c134a0172001600b890001001d05884045059080040020345042e100000b80d0750300e000204001a4034091009100d9940728400c5d441b622800c4548601000607400d001e80b0091b211000c445d840800110b5613880100c4080c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 489572095 1250 489570845 489570859
    0x2010507110715110316140114090303010e0910020d021b0a031d010e060f0d0b010c0305032a12010602330903120f04120c03213b0a02 59
    0x5124240724615458855131488107680ca4200310700c41c0c03003051101820301a2801c59035010402d40d02c00c4248614161014010384480711842d02c0450b20f80c0342d020502c111120b01c101e600000c1e0072840207011400301078508150454071003001d280204029000200040640769880415100c0c18034000b403100d00c055496900d100008503940034990303008120605544c140b00b04c078450a0b000d50f5540014008401c070103004d480d00c640d41041c40c20103031042e80e19918140100c0390010300200c1d50107400c881d884a456546510046000400d0a10319074141d0340c0003200301c1d80401c141192800081e05c0c0c0c1d04880745542140d04048054819080041ea49000101e04032020301c034483e42c0d041034540041e4440c641c00305032800c1c0f60b581003801c682c205049404100880d600401c000812a00e5850728414200501c1d0540f0b03448002e0790003900b5640419040420081d83c420120901b11040d00080c036221440c0382c8044100c104c0e003450a03480c07070015141007494040100808641ca500040030044540c00074036030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 489573345 1250 489572095 489572129
    0x1a0703030b0a0803071415070c0b1e010314070e010f170c040e0a050f01020a080103021207151d0409050d12181505090a030914130606020105071107 65
    0x80d00188248040705420200b501d200082110060002d80210b602502c1060000200b20601c0c604003039041102e6001c01c2402400d001100342d1181d14550329580c0803804c40460303102d900424007a04880c09003218021012400071041100781d00d1113840000c42001280c4280d501c40306405488a42400b42912004907100200403a000c0d485405148124800c256025a1446008207050350140d0081086542c081603140c0c0402c0020080c5a501041400086040c60180c2900400e2450103202c007038420300c10082e403d50780141c20b0140d2802004260212007030b80d9142d00000d04252014100755038201640c00520303500b42058084c0050095004014040300c0c0d071070b15801d03a2042c02c0c0d40c1c6840b0a2030754400c0226684880b2031000c02c48140030342d14035410300c120700c0c1000055400050600b00903421804142000035000050841500c0191700901440103900010403882900900d4040c045400c02031f00281e92078042d0f0001e40185402c1d80c0d0484007550f000225640d4161078400d6921007100c110348 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 489574595 1250 489573345 489573347
    0xb0721020c060706020418060f0905061e010e03012a110d2d020a02130b03061602010e1c09050907050a18030b090c041b0203040e1003120503010503071a0703 69
    0x40c0a60343c1301c1e020050510f0303150001e41c01d003a070480c02e00d00300466981009011071401c080c01c03000209008003041c45145409404120725444020400c19140307410000308149a008801c0181710800140081240c00c0c41c1aa1082e20140290141181c00c0c1c82c414045000c94458081420b00c5800e1000030a403580440b2001c4818215040c0c158103500030001007018100103a91510311001000d0340200400802c500400c00d081440316520b01046146c1202d1803216100860f050b0fa008040342c0e20140e0202c1c0480090b401740c04400e1248116000e1340a141c1480e032040b1841c0302000411340e5484160507107600502280b1031007501c1e4400810000d10601564601c038045048a61010f91800c2c851540d4036654665080400e84100445030440307480c0000d241030912540e0450748481c0541d400c0b0807503040340603499206900803c0d41c12401200028800c0052a540c100116031000c003038003400c0d4410200415030303002801624401c0c0204000010300000c0c0c0c42c00d00c5034001e024841c86d8035001655030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 489575845 1250 489574595 489574597
    0x101509051809150405010903170412270b0403050106050409020310090c0f0617330a0e0103050a050c180112061d010207031404030b0705070812010b0721020c06 70
    0x2c8840c05610442c00c0440300201d000410a00441c426000441c21440a1402401d0b480c48625040e00d134811140070080403952000d40582c0309034050400205443c00d52a210801e4080c11f802c800308441c2c03141c0c0025139014144000c000f164000c400800003692a20208420303141c403850043d62660107404c2c400d040032050b901c41c2c00803500c15204525903954807940d440c10619140d101c6000705008170886610340c22020500b0340d004013410181e1f401e030324481c0c000c0998001683c030010380f102c01c4504007600d1615000d00d150701608a00b98104015a5285040344d03840c03800351822203240c0100c403007421482c01d14050300b0b5080c00c40041c45481d503a080050400c8070462042040d101e25880e1074001c0070002e03a0000c1510340900e01400581e5501d0035080c040c0c00f47d05421148840c41c00100701c10400320b04203d58540d0066110701c0c0c42c3d0b51343e641c90b060903070032406080c140034406001c0350000a8030f40030b4800200017040c0300c1d034440b4a07080c4000d81c000f004d284000103c07101680100728490480d00d000c3d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 489577095 1250 489575845 489575851
    0x1d090720010905011805010507090503030a0e0616050703030f1106040f0303180606050a0506040b121b040f03030e1c0b060a0305120a030516020c04020f0409051015090518 75
    0x8000042d207601e00c0e896503070035110a5100090200300c00c3d0015418040e0a0107034030343c40403c5060111500d842c0078042070b41c1c0d1050100d000104602459425007554a0004540b030241d4082d02c039180c810014103045888500c0c0d840700b200800c0c914511200654044e0340307205604c811807800b500b03066035075454200c81079134a03902c124209551030941482d0035110f01600d1b84000d0080d48005a214280740030301510700c0a68112600c1400f040c84104146c104020848444903041300d002c80498441d0070b4030600e80d0204840100c604a004140850350100d0b403076403541101d000380c1d651150f0b0110724040c0036a241408400c004138a10b10040d04c40810440403400350082009000391101c142d82e03490341070408110413404a230b002e600050303c50300240d060113055007000c4166205611000c102c0806907640311480740450003a6004a0309000c1c0441050546004002540b1b05002350300d8a510f0090b10b23599a405000006100505074000c51442014000e080d81d8002d8403990300b24076050358010300f0701002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 489578345 1250 489577095 489577157
    0x60c02010b19120602220e0106050f071403070b01090b040501060309020904060908091804060b01020723010c1218061b1515081c08060a181104061d0907 67
    0x80081c1c3c1411b020141ca4290360401031030100c00c00c0d5051294040e00148107900c040c041100500101019242c85003c4540c1c40760303c03220407400095002541030850040103005048800c40d20b000003003a0181e608440300c2c0c540112401c015603038988005800312001081d000e904060000c00180000d01c003a80901c0742e06014040060030300020740000350280c140025680003441603003040c00304110707450207800346a00090006d41500c6003041d8903030b188800e6101c3c4000701600501c81d02d07401d07039000da0000c208654000c401d0301c4502a0402d80075000307000300540c00c03139050081400000e125101e0440c0340200303841921102c881003229107030210413107013038240c601c151680e0300d201d144208840880b0500400c0c2c010702070301e07038010200e07407030860035007045d0510702845050340401100c1d81c1d44003103100c2550441c282441055000c00e070000005c0c0600c581c0058070960005001c00c926030420003100d44070304412800c2410800a20030700054901c151403120100d501c0064844408181c91b062903404216 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 489579595 1250 489578345 489578347
    0x301030308280f2007060f0209100f17010e07020d0305070207090b0f0301020403051f0218130b0d03080a240506220b03100503030304030c020f1507060c02010b19120602 74
    0x103004c0465240101c45036200703404880041c00008001c0303d4020314540d841420f1045040003041c102080004080e40c0c490401c100c040c3c0032032100280580c0031030a410b9a5a0080d543d80e6031251304400004000f41c0f80b08002d8856042c244015134404c1c011180314400c0f42c1d001d840101d00e4840385038098003803c00741e1688040c41d541c6082081d24244050b000441c001c40c020803d03508007441e4114418009013072410120300402803001c1c1d8102091102030900b10545144807481201000d082c010302019100ca0307840395100d8031030310501d540701c04e03110301460070800c041000301c084c007161000c1c83c1001c0c042d940710540c42110820081c50080080d02004501811030140284100e18246040d52640c1020f03603044008400e018007100c410f01c40c00041e0400754011451401e060720090000b592400009101e41a00103176031500d51200c3d20f6544115418201c41605e0300110700d414405044000d00781ca0056180002c234404920300304590310700800f80141c01712403040c106041400c00311069102910805c0d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 489580845 1250 489579595 489579611
    0x1103100e0c0708180f10090e06150a0306030201080a0c0c0b09030c07080622020f09040809040905011410060906030509070f14040605033403020909030301030308280f 73
    0x10981c028005108441800100c40c40c2d04020450709010385002070f1b0266400d4404030f401a5080500b030000c2c6ca6200781c4203012035407440d0000c0e03000c19001e03085140f00080441c0285040d50980c01030030a0380d200762146c9045a458020900850b00f9210b54640007410700c02180000c20900c0050541080e03442d42500c1c640541c40144910f0000d0580c07150099500039010030074071010080d2064003005084031945401100740c1c0004a41c1c00d864464144941807420104003000300c1c03501120a00e0001400500500c4941c0c10154002c0405100f9408a0704803040010500307040061a4422303207075161601e0880c1802c10030104c0c002c06c001007003078040f031184810100348000680348050050403420340c2101032100e08000c8c0410780d101980224001d60149142c0d03900180083e0a40c61205d0b44000d11413512488007860104645565101a410800740414021b202c04040000c6050b02e0194a40c4c0c011a11107101d00e40344000b0b00e0840b00700360401d00350710115004c0d044d000070b0041c2c1550200414250 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 489582095 1250 489580845 489580853
    0xe011d1311070b10060302030f06060a030902100c0b0109090302151e0f0a0e15070c03020a08030f1e09030a081e0711120403020a171e101103100e0c07 66
    0x2c2c0c04440103441a0081404200c1d4810400e04084064001c03454107504509140070350a090450142106101c2d260104000000c20303c82d600c1403100c29001070030000e0b0038580b100c0107003091195490a648210324400041040101400348121896041d0b0040105406040790046c0340e00002d403102d060304050130181409030b01183c0f204e074010041d02c40e80c5c464074104003080c1c5080b00d50741c3c41290314640041000400032a0503209865204440b07003410768601c2814542282007201c055002482e403c004000e10011480e00fa0155202d03900341e2050854000d07003000b6508800c00c0c11150762500d41e0041041a0b0014442e441d0b43d070b0814500d2a2502100b83c2092500c100ba5008842440001d0b001110381e03900c105040219200d0000c28000940c82c0c075083d0f4020815a1840d070041c0050f510000f6032421032080d003009500d584024418010505200c1e54a0150f1145061140307001035506000c0ca10070308015400840780940c8514034842d003c07038036111b2607400d0941c0c001c28444040c1418001030b4085 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 489583345 1250 489582095 489582097
    0x7050c01050f210604050702150121080f071b080d0e0418030201091b03030503010b0f0c0d050405090a020a0507060f1b0302130803040803270604090b010e011d1311 72
    0x30844525810541c4d00d8a20207100413141c00400040442d8829804c4181070094503204c6419529808040c5e007425000410100703c000c52018014501c8200003445500301c4050303005401c1013846038400604c4101c00030b0481981048500034044903400c5111a400c441c1e006100407140f550b00038002244c681d1901a6404a29056103003c2d405070b516081d108003080820f800d521420b8140703411907602c20307086807001003a5000501441d40c010000240700c1300c0503460720b001d480c45a44401e0481c1c040e0601e0840041088d00180302d84e60041c030596010074075043c0f80340244e440c0c5601694a003070800505403600006481c0300d082c51110280d0340c3c800303034454003040c43c4043d015a06644016a90304400f424500e00f02c802c0354800e05980e0000d0005225414010003142d4441c0d2101011142d8032803d50041d802c246502ca0303d250340070200150004250501d0f4014039260b103000d07210108402c03900c000669404010203908091040d0201c450b005070300e01a08040c0303880085001c0001c4a80c094804003a007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 489584595 1250 489583345 489583387
    0x3020f042016080720041503110303040806070c030908060c03130c0f0b0903060c0405011704060605101e02060709090c180f0302030708011104142e020c010507050c01050f 75
    0x1005c0421290701c5005c1400070407030000031005803410003911b403001c04800b20181023400010502e0303e00111180c100d6a003003041e00c02421066083ea880c42c2071a98000e0706900a0071700823404281003c1d40010581c0000c86c1140c481c281e03100d9000c0c50360352080c40014011580c004211842d20700c62002241d141002c1c60703070f00e01800010080668a013a008209482d10200503d0101710140070042444683d0b03203d010140380c4840c1e102002c4ca00c0e201d0b842d00c00080c0c4450f41119400000160a80000b241d000120032040404120800c0030303801c440700100c1c0c40700c0d400c5a000d004213450003400c0044030313100e0f40121510281460610b0900d01c2c8000e6440c0d840038241c0c04003003000a0f500d014805c1d4034050004034028500080200001d910090403c40180140e11444168100c441c91a815603200ea1740d6031911480c007600c001c001c03115100501410000078200c801c0040c803405008014550040d01240c1c0039503004401001c883e42560011100d603400450044803440c0240031004d1114103423410402c2c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 489585845 1250 489584595 489584603
    0x6050901020901171b1c0c050304060c020109050d180801110909010807062c1c03030b01050a020718020708040e1e040218070509030d030603020f0420160807 69
    0x29840c440c0800040862040c030781351280c510481028010701c0040c00c0803d05150111050f80d540340c0c010001900081019001c000b4601d07810454001400395000e002103220328881ea50230800e6080b8607104a00700e6180d07007402402c039403140724103540307049c041c0007502c400c0358034072840c401c0007078941440c03134251903c1c0f1138583d00900f00415101800e1500030780282c00b41000c0b0303000b00540e9160400040040d00b03486110100f090081d210401200d401c40c5244509910260881e001900068910454044901400e40c0002e18146103a0403961052040750f026007002c0c2d0040040500342010211950070098401400316820000d000000708030b840078000520180b0449146841c09084239004100400006030100c0b8110781003000503903441130440040b0410280441e80b07a60b502c3e03420b441620803000075551501c98403010146640c1e1680005c0c040d0380c030941d0101658450b9506000903180c6413001031048040d0404246a62041c62014140c8052100d40c1038110700e03816101d02c8110350128038140c0f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 489587095 1250 489585845 489585847
    0x25061d0309030d051309020f25050f06010b121e010b030103031107060c0303050a0f1517011a0d030507020907055d0106050405180603150901090605090102 68
    0x3509602d4180440001c1c25400d043c5140b0300000d003082c01881c46000d01500705642e0380811440004e11010b41602d0b0301101504404212400742c14071490b90a8812808a6062042040485103520b000c01d051303048031072030304085080c00c120102110703c65400500981c540d20300c28001c0081d151a0004240c000e102221a0a5a075411400c000300010340c0106d2101495020b02400c00c00940e00804d0071032180d8240c90001015292600e401c8080d2035145852000113013445182c20392007100108500c1264490030342c032541c010050f040c203800d80d0703c00c400300c41c4c030542d40107207801c0c2c83d04005100040d001d2203485c06920f00410b90340055031100c802d0317600300c0000d030340803401403c400c111003c2c807902d80c0c0d00c000d047c500c8401a0b502c40121200d844030001c0f0800116001000d0031200340d084843c202115070361841866860b90001801500a071041d40d1040c0c40d0311040da00741e9000c2e411501d01030070000c1c0203840910007040c8441014180500002410345d038840f0410040340c6c0511035180074800c40b0f8005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 489588345 1250 489587095 489587107
    0x2307110102190b04020402030403050d0906020901030f060f09020a05041203090e090309030601060f090f1404110c07090903110d0e0a06023903120310090225061d03 72
    0x24070307000407821190345000703141020700302144081c4030541d805941285c6c0960f41c0c4e5500c3c9400c486e58042c100640000e035040218020030003c180c0c000d08484102070780c040014009010703184007a80c04030310a100c400610102e05000500d03507a001071040002c2410300c0d03441d0580c7c0f40305c1d06039003020700001a03000075111a0180710002943c0302039908001c00d2001581040a100c0005c0c0d1a10018881c0d41c05004009918406441c020803070140105880755408404942d83e00c14103c04c405030204c1036106d20700e4284020388104050003640ca080000c0030090010364103101c0b0b50401807911410607024404a000003c11391501085420342d100300070740e01c1c26485030705081846500248c0b40c12507010754012042c88000294010308006680a000c140c04001c1b49008800d18903031450401c0280d050700481824502900c088030055003e260101c0d44100410350b9110035408a005910b088a440d124220200c4c07061020390003e00180c46c000c48001903802a0f030405034208102100c0d0080140c0c0002c2a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 489589595 1250 489588345 489588347
    0x308060a060801140f1507050a0b070804050319140c010c140c19150e1612080a0f0908060108011a0909060105010f170f0103051e070623071101 63
    0x3400024125814500b8465041c020001002601405001c1c000c4902c001c03800703041d90707802040e003056030648050302e566244a8245140c40b00003584007a6000d203e840042104148070300170070b034402d5400c41d01641c10010a11582001c80c24041030000c03c01c07070700c2c0798001c10b1407502c20000c019804504000040a01c0e41c11310141c400a010f126080c6403175010300001c1610100464031020f00307030040d03610355107140551400c456400800c018a0094a18100701e19000d0040050306c41640300c0205007502141d1750301e510803413031407084c1c0c2d8006201e510280a900080c42c05182c1034601103280d810003080103900c8001081c0341840c243c2c09003580f80c0d11405d600e0a400704c01e208900821509030f500c0504c6103000e180c0a40c1c0c4007018400d01f41001024803201d2580d52140c10842940d5200075665420307400e18500307495403c030082c04162158041c660b01c506030740b03a400c450300d928400c0c64009495001e2601030b090700e6225001c00c070152202e6078a04420000c022aa000f07040d128454803003101d0550384440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 489590845 1250 489589595 489589609
    0x71d010e090f1c030515012001110a0903020a0b0301080a111315051003140402121006030605040b010b1801260405010606090503060405060a0b010e041503024b0d030806 74
    0x2104002050070500d001c801c0c0d1740020384c03040c0d03042e5423103810011102c07030011070b1b0050241031001100098081101c0e66401d5000b5014030403a4021907151821548440590b8a140f05c20300c908405a440385016000003010085000341000009008100b4041c01d201040c05132220004880e0b166560100c05001905d0140e610103268145807404110000890303000950804003c0c1020b4850301c041100d01000d032000b00140294080c3e0320300e05010860b5a4036100d0050074066800b141c46119010002c24295144004d681002c0c00b0b0500c0c2d440d00001902c01561f105e10010014400d10148019401d41e445504c0e8000b40030300d105100009110385004002004000c0e9608124070070b400900034400403a0000405e1b0307401040d0320300b00107582004900180d074282c4c00c0e24212500141001c030f4480d007100030050314008880c02540c62440200c0340400109100c00092881c8002c82c50142140740d00440068940c42c90b40740107134011212601150010307640145003803084000840d40c000b007024908040b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 489592095 1250 489590845 489590851
    0x4061d1b04051e0307030f06060905070e2d0402040623270a0f080f0607030219050306060409060f031719030f0b21071d010e090f1c0305 60
    0x80c54289818800001d218948a10ba030404000c4100703030383c200c00c0d50180b0440d001581d102c0d0340c0c0445400d01c5d1601801805075803040000c01803501000030300c494000e42c0c18480e40d541c018400c1c003240403402e1a5003081d010380c5882002c23542c3c26181c41002c1fa202d6200810142c0b8190312040750850f885090400580160f507046821030400788220024101c01254440b0281002c8600d0f61341c10581700007091940000d80e01846440405000000d074030000071504001900040342910410342d00c015090741603108007110401c01d00c0d040001e104040c0d205d440555040301e030041c10741d85410340d5003050800703940c11078020248109115408008100c100d01031412010b45c191801c5060410031100740020441c1c0b641810241511031105050042c11a0705c01042c03258000c00b4056074080d108503155608200c04240c00041c03103444004220b00c0681e04c0c81c428150201424030225038213040e260300400601400c850b01500c00c1000341d00c8490414400100203a1140c000d030700e4040c0f401e04005051314005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 489593345 1250 489592095 489592141
    0xa0209010f03080403031d03152202060a05180406031b150806060f0d0507030f0608011e0213030b0903071709030c04020c0a0614040b100e1504061d 65
    0x1240701080050321200c203850440c3d0301410721050342c1c601d5002c0d05080002c1680e80c5549401200304260039248000c0025000d48080140c0d140b8030481a9040c0310111480701e4041d40c040c4040c0061402203101d000201a00380c03213602502e5080c6c440c000441d00769002604111650040d91000483c20b402d0740c48450020408200200c0c0b14400002015240c0000a40307401e0142c200020415072214a10f03086880742064094100420700e0010320050040540190f10a43c45080950018000b40e05000f004401c030a40f00b10320080e840c105205030f0095010240b410480140108000003048c403210741c5900c12061240903555550f864900a0f02a102c0d04d11803c409502c2484004c0c40c0362400120342c840148256001669041580482880c140224800403e0745080011407a407140004901038007542c80381a81b41017a4a0301401e005104501e400340c42c2c00c0c90190300c001a54801c1041381c10b845060007030000543c81d612280b12500d90254005454000c500c850f003801000c280d011480c100e50115 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 489594595 1250 489593345 489593369
    0x9090510080f0a031704021c0318080c06192706030b09090a1704180f0b03070b030f040f06140f0901061a0d1b09080706020601030f12030e030a020a020901 68
    0x4907640c003801100751001176068103c1c0c410b000030f085480d003c406244240f07490701041060111860f0007440c8010b25124000d07141c81d1020005219000040c0b094040400109994244848000c0310714000c0c4411062004202d04041010b170411a00c040e0241d409080c1c45008484606040c0060265400e40390300701e008034032010030081c0c01c541c0070400001283d4040c0c8812450152900b54040602954028465a45070200075480306a402e80c8480d45100c0e11010a00c82440c4100405861b904144111054071204200003080042c03840440350740075124040341641a80c040d1036038001c0714850312104020011400510039894038040d03240303a00c072110384000d103c00c0d8200b00107021b2403800791403040c11010000c55164001c034466041400001c3e81d4460f103112244808030010300355200d502ca00d20850003245004039040d0b1000c01c209050740d4000948040080303c5507141c1807149040e20b075803420555039002c0c4500810040c0003c0141c1120340c1d0081c450701c9420b00400c8564103042e800403243c044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 489595845 1250 489594595 489594613
    0xe1e01050a03060c12061205060c0301080d120e06070e12060903090607030302070b1005090714031b070209042103140a0504021f0507060f0c14090109090510080f 71
    0x203a100700c03540a40354091408075050301d000f2400c0d52605603c029080d4850704040d00481d101a980b100001114080d20450300b030341d10b81c10784501d0640300c20700400a46030030030147d400090f80145414401c0042095002515501c4410031500300003061303c41c1d10019084040070021850300c4085000b40340090000340015051815850790389101c1d143c8000c0c003560020402c80113040c00795041d1286180c011003c074545280c14a40801c1e01078240c05600d110b081481c000c5400288144502200c00032148081480c51701d400c140d8031007a2015400c5588648020881040182c40380001280540d01c5007072203000403400d41e5141d900420039481031f0303020036103055544202ca4425001080d00b2103210400018203031242e002040601c908610386c0e001c0303812519a001002a4810000c20409018080403c610608040b040098890040520000078400301840d2041c0c4904002130000e5241410021a4560b903034004409a510450341c000c860013030814104004503050140d134140d03001c47c00217020102d07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 489597095 1250 489595845 489595849
    0x1020c090103060c0c020a080a050115030323190201050a0e010b0d020915210d0c080702210f032206051902010612150b0303190302090402130e1e0105 66
    0x250510015225549a50015000c1809000010174942c0c02500800707069803141901075072081845021980c943c40c102440c1d5484041c0d003186000e495142d95814122540b00700120080c40ca0503c41410001003084505031f000b2003c0031541c0342054903000030039646032555044045070380390000000c2503414542d400b4455510b0155080d00990b0407207100d400354542e01505000c030240d140e05d4a4002d1030700c000740c010b91404c80c207030490340d19002411201c00406580741100c6e4410010401010900c043c00340b800107241045800165800804600c54034180050070b041c5040009045840c4541000408014800315803000703050f101c0b064080c5c00c500c0303854007800414034820940d848140803820007008000034402e400407030040040450015800303101d400c040c4440001d01d2058100d207032a122048041341004029200040d04c075400c1c400c0c118104400c01da010350b104003411548103608001103a002c00b00ca04007800a0410001c3d22080c5160080d51014001c840c81c600e0f001040002004200030303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 489598345 1250 489597095 489597109
    0x60a0803040501140c0a0308010f0510080703020304110a0b0903060a110301180e1608100507020d03091a01061707050717160f0831030b07170f0f0601020c 68
    0xd810070700c0c15016400c80381444c08114021410034501d0750060103000401e040c0c2c0840c5a50580301d40e00304800b161a502ca040000d540c4c82400088041141c440001d0740d001d00a5000c1c607407042c000d010074002c0060038800942100c02a0708103194180d008950003002c0d0404011190b4858400c00040281200b400761100860205114807140d0711004005a40c202280b60854010040765008480c60b8980710014811344980500443c102d03480b6003801401d03a03201500038640104034540141030700310300d000021000f602e000b882c2038074070100b13088071503020b281c00300e070b00b2030007862903643e80e41001c80071506661448001808030810000c051240401284e00070100340010640700040170f581e16000036803030104150000c0d000e8070102c9501c11744c0007031001c1d5900528249298003070f40105c19a00361040c0d0000e0722444601c94190700160030500014401e100544d401c650181081c41680705030002c04041d070b8404594040080405400740000048681d2016800c500d090001e003408003c0500800c0207 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 489599595 1250 489598345 489598349
    0x2011505031e070b0313150c2f03030108010c020f0f03090d030909090c030506010902040b04090207230a11060f030708100b0a08270a11042a0206060a080304 69
    0x28804408200140030400b00f24040081403220110390300e81c0340079075100c214400f0820055650207140c8000d070100311500c0c411040c56032a15100d0040b40185c10111424124081d46c20b0014031464410426038964208061402840014001b0440c081e071040028200f14195017108542e901c441580000490080161800440140c4100b800040c0d541400c56000313030075a0011031103501d003503030020030300c40421400c81c240d90041081b00d0490360780c0c00c8603000f24401d40c898250110b5080c0028010081c0c41d40051403914025581068644c2040000180f1501c0c0100200316070340c00040880c1c2000340101c0300a0305031004403071003401c10150014952081c840100030000b004910b400191020100501284c09001c1502074651121940c0002070300301c040c2a201007240011a070462112441103031060000c0c0c81000025000c04001507503000e04c840e808171070305039100351640c461203000c0040007000904080c0e00c0007034217150390701c038038020342443c0c8041c4c45540240441c200c1030100740400011602 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 489600845 1250 489599595 489599623
    0x916181d060c0901090905071107140607241e050705090f040c0306030b071808010506060f070629041b092705040b0709080312070311120f01060201150503 68
    0x2035500641c80049810017815009580154600014001a168007400d4501d0f5280d07004100e0389103a85a08988800c080358105d103a6110320200140c000140c28040558211010b04035480c0c00100c101c600c1c3e1098461804ca413680b0301c0c1031040d000e15504268015640c2294090800702e1410f00d80360b01145915240740d00090240303071111800c886d0703148240c0c8400011908482100e0a07030a00550041460146000c42d8805200e82035010442c0340d0184506406420003c2c1000c2c41c1420a421181c0c544c0c1180b03070150383c4190741d420f0b001d00c403421060074003400401d9001d41084c01310200f4100030840c0e44500c101c1151001c668180321034950815212816100c1300c0720040f2582001503021310352800640c1c1c00c1d528081c20201480b003007056044102c1c0c054411520b5a050190700d501641c0d6803805041400300d5100018000311742902d009600206210110104081c50301d80011844240c1c904155851000b202448004028295080c4607021000c0c412010f90316605113407900180d40d450b41e288140c1e0b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 489602095 1250 489600845 489600847
    0x106030515100f110c0f040e070b0c0a140a0b0f060d0f060b03010e06041205030c090316030507051507060b0f091003021906050d050916181d060c 64
    0x1400c03804001c5903103000300c1c00c02010101c80180b0768100070b01940c0b801c00414045040341c030700094008008035201c29200700142c52500c580c1660010000a803a0030600c5207450700a003e00441c6400140d8010100010800e000f4000900c7c2880c09207115485007515a08603080010800700040001340c601e900f01a5003c552902ca4481c000000c8869844550040c80743d01050380e1641002065041882d82a00c00c03002001841400e100558907a0004c6030b00030705e4814684070195005009401554014200c0404a410b1200100100b0b00c5c080413010800d0f40990014401c0080150801421002e0242980e0003000858942550b202c14040d950005180584407110044503403102408890f10100040002000e41000c103000b50900c2460b00040e0302400001c240000c1e80640620000100c0e2034603a41c0d585000c07120720101005010151013030309140201c942820800d041d0300002000f6000b000d0301000c2c10380196803200c0468101038170041e61f17030700c10b004000c8062034042603a03940851150001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 489603345 1250 489602095 489602101
    0x715051e090303120a0e010624031d03030a0f06050f040209040b0418060f0b0105090f01120c0f09050d0f020d0804030602030a09020918071223300301060305 69
    0x10310400c1c0070360504190540700100d54a1258a40f80302c2c5580a610034204c00c200754250104018240c402a00035107075103940c140c0310039951020890800307101c8950784ca0001402104c2c1155001c80c0c001032040b1240c41c0e44040107000407041e0504c2a000d0b89400c280e0104101460000410f103585054038400784516404103c080d616116a04000c421400081c01001891106032152923031100704407050364242c0c504109045014024814004500c105840c0d19040440c40010804048010b400d0141003001c409588140a10790f070181c0d208041c003684035820b203064401030007403c249a0354015845001520024408101c0001d0100001a0180c036400b000f00000c2c100307221148241c0e8002080144000104143c99065600208005100b103880b0456501d0301924043c0d401d0440714816802d4104c501c0400050102c1800340d50b14504c101c11900c0401c00182c0c10250300128020b80782d003c0d41121003c2d1142140000b5040802000e070059200c0040b256142494540014003440c42031507902c1000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 489604595 1250 489603345 489603397
    0x48030402180106020c0103020d180302030a1b0b06132004060e09010e04080c07030507060306050901050111061801090803010e0108120a050322080c010b040605040b0114070c0e070c05071505 83
    0x31618ad0914110322281d5030703d000b860001c0d903d40c0039092000000b5803213200a070220303090803c90300180382c010315038801c1c6894170fa00f00510800302062404415a49241d215118044020a08007121824401e01e40756850b208024242410101c0114031444401005010315114035a04641040d00b08c021180c452181601d100e2425040d07410207049031050000008110f0743c1500518152501a901030308203903030311001035a04440455501000b03401c8100081c58118242c4140c8981d826040000f15035840c284e16400c025030300030707040040a000003400502060004000c04046d17809000030751807603e450050001d08600002d0442ca001135544038543e417104200191181d8a1500171040b01e68807100780c61198001d00310003080303502a500b44540003c2c00e10b024824200302102c1070b12580d0302120b01120032143c13688502000c85024103403103c003082e41240a110244180c10944030b440300d4a42c203080c480e1131308615034002c500900e418461400132035400000c1c0c0d9070301107102607805421000000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 489605845 1250 489604595 489604601
    0x18010902030f0106080d030507051b010f0207080d05130c031103071a090901050a050d110d0506010e04060b090123010201090501240e48030402180106020c0103020d 72
    0x8040d6140c4074803500024145410f60100b01100c0e4008112254032180441c144d09445086070964046003007440800007601c001b0050309200e41c118000005e805502c281090202d8208101c246c80210001c100010300011600c80c0706d030881e90120500a6011980e0795036254000c150000800080c251400300c0c406890070405400984410941804600122000c1d1003054101700310841c0328001150001400c0e092036a40001510005801b088200c0c501d0740760800c11111a9141940100c0107a03481c2d0042142401451302030242810419883d0078a418402d040c0e07003042c0415841141c2d00d0f030041014508107910880c0f02c0b51500142e1003000500c00040c0d004010041c6c0190855003813408102e0125140b0200c188030032010701e81180c88941b50883c00044980844105036000641c01a01c1d050001091080e01140c814103042c8641c0300031030b589903c04112002c0c2400002202205200451500281b0a0003010142c0c90340109985000002555200141d48090505500090032010000160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 489607095 1250 489605845 489605861
    0xc03130c0302040f0902040b180126010606111227191e080f10151806030309150f0e180f040c211e23010f0e061801 51
    0x100f04124000149031201c020740121032089100c2c61515411500c41d29151205d40c1070039a00301255410380e03003400000b1082a282d0003084030682c180070ac403030322254424003800b030151403142e507041c0302d50f42465407041c5010300440010068940178011801d21000d01000348490003a02c500c0e04001d8440980442c440d0f9406d403d000104140d14807010603076206082080c04030b5a8641115862543c0c1c80380d180351280310102c4d052034290084510303d10505240d400102102c0c00a0028000b8640c1c3e40b88000d00e01441b02901014203074603682c041080c5508510711307200070441c1444a42c0d104c1d402000081803c1503590041080c002d929048045c1510f4580882503002c90040454405003400041d00d04030440c116400c94140b075680c0c001044205106141c90210b0310407030f002d210b01080030f0792202c1040703c0c2e24980c800e00401c001c0e20305022a20b0041350300551031032282d01303500d007040118486017500d20310b0008090f01820100c007807000600006440e46e10640040032104084090504d0350b01410b404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 489608345 1250 489607095 489607099
    0x30a03051012050d0206090a0804091104120c0504060603060302010c12030609060303052817060310110702031c12090501020405040c080708011d0402010f0e0915010201050f0c03130c0302 82
    0x4030b80101c040050000d0450f41d400780d05d4007101d101d0750311501c0c203941c1c0e50a19603009241d924180300400c07a4903500d41001028903686900a41459142c08100015410b619010741d10048886010001c5081c24420708004d041c0701d01e400d11400e811a00060003004880000400740c2c03281d10700f284100340c82540084058145c01c40300340512584c908000340150031000d21943c3c03080c61134240e44091141c52a1607102c52a96403242e00d0308800f4000805841a4020b00440e05030040e400e01e010040860301c150000d00d0b5950444540303441a500500d071418900d45110510b003000c0304040005203412001800d4284620704000c80c0d01900361400c43d01a020355070084e03800504140254180035000400349205801b036646030343c203980e40c945445001d503400c400c40c0388071005103002041c095480b543c8407009400c6507003030002140c00180040742e66580b00301c8055490026100c10300c10341d9a8213000e510f4001c2208801c05000b4101800308452502c80078041900f40d2000b01040001c0240d80c2c1040c100540e00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 489609595 1250 489608345 489608369
    0xc1806031006120627120e09040320060c0409020d1103010323010506010f0302180a061e080609011512181104181112030c03040602010c0908030a030510 67
    0x184030180110b0f8403c010003143c1380c4e803c001106182c00c101000b203d8042140c000c101049100907182c01c000001000040f5042140850780302d1095102c0c028001d001d980301e0381e50134081e0b00401268172912200d540b400811508070300c0912002081030750940d02a150b04420040c2c3d2001c074014400300030244403d03003956420b1301000000510561031620403214107040844001008144502e50888508461150120304004075602965200c1d901910120801700c040440b40c100c402c0010780a4000c6601c07030000200c11560b106003814030728115020b2425a42448901c908100740000d074030040500070603101c0c803403201c00340002500c613940c04600354049841c2040b0081c07103d0040034400348555410780d85104d15801740b410904007881040c043c0c00d000081940c52040e10b40c3e42d0800d11895004180e0f100034140d600c40c0e04804140300070702244440e14021503946181c1030340a420354050708409003d201e440102040003860105c11220341114604c0c001489984500210700001c83d140c000420f4058 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 489610845 1250 489609595 489609599
    0xf01020a0b0c03090c0607031e03020f030901060311010c0317091501080319080118050423010f0c0f050d020a0306150215011e090e070504020f1b0c1806031006 70
    0x45020083d800f800c600801c1d03c45a020103018401070344542d020080005000c403142c001c00110140814141801c83d1801501c2c0c61819604041250411b45030200d141e5034408040040100c9400b15120442c0b0a00744000101d50545014068090030444242150302900000d102440c092100b00f1400310700030000140e6503150b207042c81e5680c0081442c0180500c050200346852170040b4043d504882010f0b02c1d500365800000c00e040050701c405881100c00c02e001000d80c0900814903901c082025052000000e46542c82c013141200361010015604d0034400d801c01c1c01d12809601204840d16803061140140e950ba441c1700045009244a50105042006000b980001c1c65800b1580d0040c420b220002c011072662030708406803c1d605817084019910783c0f40350301000070840341e8200500d4020340805454030700f80c3da40c01003001d07a8011500c045182030001101511141078521860411750424000c3c010003d0540109035880401c10040c1c558040c650f0020ba4155401c01c0082d080b0040c014090042503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 489612095 1250 489610845 489610861
    0xa0f051324080c04060311040c0e0405070e011707090b210103030e03010e0705010203030105011206230306010e07020c09062815050708040306090507090212011a0c0c0f01020a0b 78
    0x2030403409000494003403040b0b441d03c649018050780c1c0c16039401010f8070800c00304c0c00e81007000401e4015104818001d0340c1c1044046541c80f48941c1d403182509458000184400100040c204100701c01201001400b14050140d140e0740a94240159107011800f95521a0810420303080c1c4180710807080c144042820010080582c413030380501e6070b1a070540007032203a407401d80301c001d80350040c6002d05401030380240010003680d0320603c503074165008694130000c0c5250300c99070b10400c443e1807a51400c1040050141c0d10901341400c01c030f11801008000454911b5040240000b03448090404956200304070341d2000c40c104c0e030f50342ca141a540200c1003148601001d101044202c03072010601c0b401400c04410032800c2600c1c1d001c0d504940f403a60b07101241350316042c00c6564000086c2030401064603140b2954201055030040303480200720503450000280c0c21b661405400152140201d08036292460080c8003050740c8090020300d000c0d140c1e034126000d00c100e44685004074074180b0190170250001425405000c144 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 489613345 1250 489612095 489612161
    0x81801020c1b0102010e0d050918010f030210080108030a050d060503061603180c0b03070e100302090307090b06070f060e03130f0e0402130f090602071505060a0f0513 73
    0xb00e5003000284108200c440016801c0ba441080c824481f601326078502018144208000c0141000040025209018062440e007812078240c0101101200d07011080c82903183ca0709034000181d03d1890140400c0d0f062849503520303409404006000d000c0003160000d84410ba5400c160098040035080310000e00c3c04600a030000b280c40c14011000c04d00e0180b800e03813000004d41c1d2010501c0e170000052120103160001a00c1c083d40000e10860400224140a00c01c0d681e1700c01001000c9001d03503502584624514041608150041c1e010141103440c210401601c0c3c3c41d0310054404650700300d0524110700143e41007240241180b2010411240000514002c2039903605542b403040da500d00180794502a03d681e0070a090a109890295010956401c6001c21001a03040803c03000c17a10900450742181581c2c079081a60481003040703c400f480c1060f00220b40f5420305c150390b44144203c88401d03034039240190007042c100c4d21f4003855000320b043c004001d4403030685400000f51180c05d4051000404d000382106080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 489614595 1250 489613345 489613363
    0x3020d050322050109030f0203071502030d0e07062c0a0906090f06030b0f0a090b040b0406050f060f1e060f03341b0c0603020307020d090f0501081801020c 68
    0x40d0001e0442c26010445084100301c0c10385a040e11541401401d5440360314405a040204070ba141c0f01d207400200300b004000901c54011003450300115201e0f070900e12200d0a50309110800350081d400000c0c2000031590100b501c002804844107504280c4038015045c00d0003583e903803d40d681106003100001044ea601d070b84210100c0d8001c403c1001950702042c6141c0944035544070262004406602042415070303e0360415402010054000410100319942c10032a602c1c1141d0039500441c2800400041c03040c45c2c0503a99000080040e802100c2ca0160f00283c2c03031b2807030080402d02071404c1c030050040d5000301c003111417281da8005110940b2481c400d50094100c2e0b202304c2e55103c10192080f01c000010110192187c02c03140044405403c0b5019104100c4a507060000c02e6800d00340300b00070303a03404502400c0383c800207030800d42d4000d61b0342e14014801910b4030407544081d4040000c020750422800c448100074105407402468494220b454864030808000340c030300524880c0e54400161101810070000b84804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 489615845 1250 489614595 489614617
    0x6050405120102090d060203060a0306140a140421090503070306061d0c090616020409110108070c03080414070305122a0d121d0f06010506070c12030903020d0503 71
    0x504007490032101d500740c0c0558440541c0040010812000042c026005103500c840c0103400c541250b542c1e602c0c3c080079030359042100720f1803060800901010b0540c0c2e00408030725840041014034581002e07500c0c0e180400180c00c00c17091900c3d809101c000d04500c1040d80800500780102203401e103d44900b003550003001144101004a05407054072a550f4426582c0b0380c1c0300301492180d583c02c242903074080c020107500101209210345803c107200c00050365503120b504000c500a12084030380c0158580003521015001c1e0000302804858802000044e0348161080c0c0c3c440d0740685120075019103405520325209041d04000e10a0142640041d142c8140e40054003030501154089040119082914a03c000703801d50821250342158041845160180700700035020308032120000741d64204904299905c18002402180c03d4000503c00c0d0102310f010070425024100071100383e8504006540c1c0c9034680074542c8512030710b00d060201814145402100b0050085070040c10200040e44685030040d103d60008010403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 489617095 1250 489615845 489615859
    0x5071502132408091b01170403120e0303190b12060103030203220b0d0b0a031e0b06090903040509090f0a030503070216030c1208092709030307020c0f010c0c06050405 73
    0xb1009881180180d0090034000c0c05402d404021303c001d85142010744e00502d0500c04820102c0c0e59140310641042c1c4281c0c0642e4920080308655210242502c1e02034441120581c0144181300c040d1400c174640c80c400481c61040003d62454903800318556210701400b40c1002c0c02030000000900da00031004000c0381c04459842e203022506140b00507951401801039a405110500a0381c80134071079548a61540c0b030303000f0142c040080c2d4070354461030903200741911644c0072100e00400300d0400003c12001a00b00004a5400b485850008182d558034084c51040b18403a41c00000031941804003400130781c02c950400c0c1c0c00d0781c1c24a481401c0141c02c0743e000365102001842140c40d5a0000003500b080d0500392070b400080103200510340301d4103c40b1880c81d41e60603103041404100107070305541d544c3c0803400b1040003050f021003480c2252044054610004100031000e403c00c104101c461540810182c10040c4200c0d0103e8503510f1000040f1050390341d21500074802c00c4c420320046409a0041c001d0001c541e0121050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 489618345 1250 489617095 489617159
    0x6210703091208071b060b1804020904080a14160201090602060f04080901092607050111060f0c0d150302030601171207050f06041109010906060507150213 68
    0x8808680e004440507040b40d855050301d1806610034541c5070b4010080b4505009555120003a00304105103042c0102d443c6961070b20141c086060114802d02d5040b199043c2000d9441c003500419400341d0024002480311074005110503800b80940114a2a104403800003516401c9181007040c1d00513040c1d0b0141d0114028800026025100042542c4241580b01c02d4404946540d520f1540ca07400000c0401e041c44440480402c0100150820781c00d44807aa010791381030701c042600d107035082003c00d8000504100e4070100c0c1c0110720b070001842036001050800e21200b00d80d60b130b41c0690309074010702d030710f190859040c52103074150400400d04100c03d880c001c5003911800d0740e0b501b02850000042c102121815007045240100c000e41100c0500210b81c000d00c1034034420744070489400e042c504204d404076081d450394000c0600d5400c0c0848000d0142170200c000700619828100050854020140000c08050507003504055415040c1c040e150300521344031001803500e03215403061a10b0801043c441442c1040c2c00305c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 489619595 1250 489618345 489618347
    0x1b0601140f060910390b09010b0d0b04030c02041a03061f03030e060c06090718021e07020a15030b031605090106050a09030b0f04020f030703030207170a02062107 71
    0x4886041100034890f4181c901c084000f5100c4128042101060404503c50300350fa04100f4694075107540900381d001c0203005d45510b0100100b101c05001c07407809030715113048440561684245101410b800041c40d01c5a030343d882c90708450000710310320300030740060030100d41d540c160aa4100030381407410b0440658003107583c0c00304880c0005408407141925101191010070210340038030000700010a02030708141c605a0200491450301070151a429020761184c01c00b0080c003039012628205c10012840c003549060064100e032441c0041c40c0c0407000708003100140c0c0104541d40c00c01c0060080c444030054420001c070710f20000e801840812240d9009028040f4030485a83e0600711703c00942c2c41c002c2446403664203102c42290207400909030181440301c0f41c10040f01040d8810020f83c0b0a03c51801d01004c10b1900c0e10600240c49a0141064040c2e44518400d0000070b40100e00d02041d40e41d074841000b140b40c1c1400c2c55038034280d900c079000703034000500080090608941e400d802c9200c02c8466000c403003070344440030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 489620845 1250 489619595 489619597
    0x9030e01230d06230a090207020103020f0f03041a0708191b020d0306050405040c0303050705030706090f1403120a02132c010b03040308060402090a030501050f0604050108030a020709021b0601140f06 87
    0x1060ba446041000184001b2802d68003805059006140c01400d11298500712041a0f01c00c00b01a00f200324080304000400c00314142100395403101003404a400e0820740806820504040c0980109150164001d03248040aa0003003c40c210001024004040c410a010752101c02804042c00040c1c03d1603404621410030340075890090b64071000384c48216145440454413600726103011215404200600d4010691502031685414018507aa503001c03000c0d880c20520405a101c03c26109070010303c41c0390b0340c8181d5035040da980048501000360303940c00701c1004020141e9160f000654100303040d00080201403989105012a994190400c502c0351741c89085941c0c0d00e0104642c018005003144000030780d5030a1940141241c010003602c54101d154413035446a094480c00c07914080c2541245c001c11801d442c00e80240c41c014088040a14504801498005c0d00d40000307003e00030141d6000a200508541c070300390f50f5040c000008040ea9120350315442803000440072507041034420a100042507015180103c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 489622095 1250 489620845 489620909
    0x30e040b03030f180909060a050a0e06150303041a042102100507020d15020315011b0803101706150102010501060e13090b1303030f09030e01230d06 65
    0x740290b041c10700300e101588003135100005079000d00300c40311500c0c10240c4503c92004d001e045100041d2280d4644680b000d401c40b00020490410541003140b440c007100e01c0410096003081c602c5103048500e8040c000400e1452141c0c2d803140619401010340300810700c0300c50000d0425540742d84003184200d000c07145a10000c110380d0b40065403054018410008003409000180880c84c8054001c17040c00d07910792079024881d02c01485c1c190905400100700002c4c08580030081001e1403090820703205000145107004101400300388000d003c6400000410b000060608004000303100040d52100b4a080c480800354442c82e0550b40a800d001040004295035801030141d90706a8456580329296140c000c3c0030080c064034822145580281d071154401c002c00c0504011520402d040284010013026502c0c2c0101101d801840c5001070501c0d051044000a40c0081e80881483c0c0c00d2a100d8030b0b036102a884c01019030703c040c20850760541c0006040d1000130b200d0300914102c484142884202e080d1655008046040a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 489623345 1250 489622095 489622099
    0x110d2006100b1b0a060504061d06011206110301031103061006120f2009010e04050c07020603040206160f14011509180f080c010c0c0b0a05061203070f030e040b 70
    0x25034814403881c8002c0010b001402c02d45000c20003112071240029080c180d52070310a81c2c0254803041080240109801501c22800e5003556010b000c0e15013541e40b03601c0386010301950301030341c20f168a10014010140c21482c0d0b00e90300b4a101c01d9481d41e407442d248900028010920f4080d001c0c200021341010040d5810300100c2c2c1c195156060b284851403141401020414101d0120a60703460104001c91075600f8092030354190218500d580760841c00000d4000c031000d10b60b1b07500c164200410000c0501380e000a80d103d075235054414985980715440060b03598060f803884620305500c8009a4401e0000f40905050880d000e00c410800f02400701c6101820ba814649010110910050007000400c1d031540c440b96900742c104042e90003012040d9510000d2440da0792098608400128a0b060700c0d41003846040e842c441207061014101d941580e442c0c056200042405c0203555640c0005145511143d0010340003c1a0360107a0780d480c55140381c828404a41c10400b500028103000c0312600b103003003900c40c1000c00000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 489624595 1250 489623345 489623371
    0x424050117220f050c090a0c0e10031409030a030507260405071e08011401120803040807020604060518150f1b07030c030519020108060d03110d2006 65
    0x910312541004040301c00d01c100690703140112007408901d50840c9190854810000741120b01c100c1c05c100100f100d0041d00480304d2925000f8800d40c22a044140c0e049100001e6456202100062109400418425005041c030703c0c039160410100700c801200600c4103000302e40381005140c8849070204c1da501e02c50440d41085c1c0f01e6462911103100c0c0e007d400d03143c2c0148944e048400c043c0c4c0303078650b00c0c0403054110a0000b502818000500c5861000c2c013901d603100002400031112580f41100400c01c9901c0e404002d4984c07280000880c080c004058211000d40b90090300c1c09544550300c0d207000b41594014001400e9400d003042d0180380381d15100d06e44403114055441b40c141031105a603495501341e4000b43c200740ca0042110000c000c900014070080b0002c41c043d469942d0302030300d107040090915806e40c4842c075800380f4103021507005030380102049030403070415510b40d01b00c640c40d4a01990a141d0080d142c0800303100d00c1c80307070441103503000400801d001c40310708018140118400119076204420b803102c0d00701d00740b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 489625845 1250 489624595 489624601
    0x29040b0421052515020607051c091104140705090f030a050607020304051e031c0c0c090506031009021f1403070203031008030705120c010b0424050117 66
    0x40c49101804050a10700c0c045101424540d15140b600c0c056900350742c030000c1d54400c5489100810040701d0010314502480c4c0030030f00d00c040d40094660342c004103044140000840c48614001140d026210850090002004144c0c12401c000412005c3c4c0c408141c821030038210f0700c1007528070743c03070426001c0e0605448103811305c100380e0104151214201302007501441061011000710b102080081d000701810307000740d540c503401d0406004c40c034007089004240b0406000080c02d05500c000074509101c8114107284074030011210b40880d0500400e003405400d1a8407800007243c81d0042d44d21060040b1002c40c06c071501200d1009072541566841003019512206602c46108110380c40820003203a55080d240c000120131850450904a80040e1800001039002008100001d0f08082d00c0303c02a003000f9000b03605000d107130b540d045d82c0c1d0105c0ee030310b0f8080d541011440401460094002c6051a00b00600601002551a010ba2584e206c44421221040e0313986000044179400b5074803528240520201c1880385130303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 489627095 1250 489625845 489625859
    0x61003140a0c030b0d0b0103140a1a0606370207030b01180e0a030c021305010e06220207050f0601060f050304061a040e06241011120429040b04 63
    0x124000101c00b081c107840306072003640e6544001070107104501c00e8001ea401941103041031604200005081c03182c07907102115507070100310322070321580c1920600e00d20020550340d001c000c01c50728010306112003101d200382c503481d09800310340e10004140c2d0720b81218180b01c409140c15049a82c0e03a4107200141070801c0000061004d014015420101c4070030100c07011500c4080316641f03c2c680b049020b003d40016428100c4442140307058140140c2d641c003035603010301031b03075040401a0004200c05000140320311000c0c000c410150101c9985209040b80d10002191181c1d4641451500d41e411b000c50840c440c0113100c000b0511034000c4560900715001d90b40d03100c1c110b40d242d9545000610500d000c83d0b0742c4510341d01d20101159503070b0048905203c840800303403000b8180113603944004c00c90585410021000ca6880c01c00d01d4a809264618000703503071a103942510b89080c0b605040032001250400e0b044c0d000035000c260710102c802401340070b0807c1c10402002c94032100d06d0010302e00480c0143d44610b88200000c000350 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 489628345 1250 489627095 489627101
    0x40f0603090f051203010905060904020f06070201030b1f08010801020406020a02010c0c08011d0d09050108070e0a050d06151707031103030d060312020705010e060a03091a040b061003140a 82
    0x40c521440c0c801074034205a0700ca184c03425481c9800c012030040004014405c62413940a92900840103441c040e40500702540012904080202554007584011030700c04107581c03280d048041c0c4000003610030440200c0c1e10602c1036003918600e8000b00824020030002611480c1482105d0444460ba40a070041206035401195914403034141990444400300c0041190307082841240716110250400c00b4101080140300340c03c1080d590218414410b01c80380400160b40c00440441e4843c640345000882c49a03400001000d01d2900c1d006035800803140c045003402c01c059075220800d5041114001d80086540b071b0700303034110b81d408800d51125581001c1da042000400400e030204407a2001002d99007004850051074044074005d41c820f9030340403100c0015008540e0180004806054280380400322954004e010502c21310518160000301076a0b2191001072100c2d00c0d03000e440f10306000301601c08509150500b0484070b5000c0e00c2c041d104405220750a4400740c0648950344850000c1007026808dd03032025505c03802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 489629595 1250 489628345 489628361
    0x1302010c02060f03070f0e10021e0f06040605060f1c021302300a021314060705060403080a05010f03031e020c120a1502030903031914040b060114040f0603 68
    0x20080501c1038500e80d950f51005503105240c26562144183c1084000601041c030768101c06015241480c0c8440015501094140c111403c4d410004020146014048d1070100000c41041103405003034140010421240c0029005900403926144100504001c0000b00d4402210702940071600f03076a00001400c00740c0d40003591a502400040c1041000c02c6080d000e00c00003040b4001e0180391088041585c02216101e50b005001f24004500307001041e00f611074841d1450154040e003004020703083e90243d5030740085801d0103a00c4001d80c1e45c20b081038980500420300c00c2c3c1300c4074001c41c1404008036440c01c00740101401c482e0183c1d51650b01c14400c1d960b100d0482c203010406003c6020304041305000352942d85000380721a031100024440304800303041c001c200d09d2040e0b452015260042040c450404800004d40340c00c550034001c07400700001340b4200c02c2c1c01030402d00d19601c840300b1710404000c24411000070103403007244c003071700c424000901603000c1400512650041652040d8100303030071b20040c0c2c429402084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 489630845 1250 489629595 489629599
    0xa080109050a1b0804020406060815010c0203070801020406080906130221011103100905180703121818230a092405060111120f090112321302010c02 65
    0x1904100401c061940028100f4803440031955200a01045017828842d51005095610340150300e400c05920001221140d03060301e50401038107800c41c0d400c3d547c0c1406800001d0224900031951541e890101070445c01045070f0240711402008009a80c25445644e05000d195000346444601d116100c0e009100c3d800000c41445203658907402e0005580b180c000071070280680da0350003852249030400b600d0940f40b0003010345070b560b00441c030040e140c2c0c10005400d2091301d621210040400e038030020211412071070003088107607000f07546400041c00950910a103e420304074901c14412300c42c0815604600d0792048480900b240c01410008840303030940e500003001c40c1d100d2004840d421805181c3c6043e02d03080c5c281c0c0382003407a42c0c80081c0f18666800c034000e202c0031519600600060300c07440381e00c0700c0f940c00f880c0c4801888800014428226030301c04d5440c43d24403085003404008003103c601d402030000c1a5400b2107200e81c7d80e8144810303800a0300307030001842070044002c0c202103642c03e640111248045050100d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 489632095 1250 489630845 489630851
    0x12060919060902030706021c091401030c020f01110403020f0303030f16050f0705150105100c110a090e150a09020306010302040b01031e0e1027050309280504020a080109050a 76
    0x2c005950512181006001a07402045101c5905503210585010b8602600038018034480030048044007280e40b2600f1ba6090a0005690822010a03420b004150b0340d140c202d546050303001c0c046104180040c009480c0291001d07407003000d1140c241a40c0744020b03902c58044c4d9018000296455035646000c1a48143c0e40c544541440c0884021614a03000941c0071140c1d60450f02c0c4141004a400f0201c9005042c2100c110240350309010014000a503d0309010340711a0070000c1c2c0ca03003d603c6843c120f40c000e03d424841005808903104a0946031800e5501c80311080304901c02240c0024000e001c0e801c4c9141d001000740000b03919540c2000018200500400e060540310101c0c15034a1094444030030301c03000740d141c01082c2c58000f00500360410010780300101044e490581031101e484400f8102c035080d010014034a40e5000742d0380c2400c0d440c41c002c01c040c00e0751000c0000100d002601c0d85110042c13480c40d6014001c001c0715111000c21081e401145154000948920300421408000d900010780000c0440000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 489633345 1250 489632095 489632111
    0xf030905031b0f010e10030f0b09090a1202010c0f0809070e0f090f06040309050907110318130606050a1206030218010e101a071407080c1206091906 65
    0x30a0801c0c144001e0840109094080c2402c14104800c03003c49440c401d01c1c150354000c100340c001503007407450041c24604050381c488141504400503402010203c20003002d02c3c0091a04000356561244200744c1141c6410401820000c903a005024200100300c0c0c075210248a11400502110300c0c4000a1060f032080c464210005032010b52003e060f030040d29070090b074404503e0400740c1d083c80c0c000000d0300301c203042e0311000070040440d501421420554004859510090f02c0c3c80604840b009419104600396010008000001c0c52244240403204030081e15207440d03c14000f0380f07132422103049218003004607504200a1344920710079030030441c0d000c0c0c40700c0c030004105132a900400c0800d851403074140c415a12500062206104640076030354810001c00642ca0100c0c1840c81c2140c0191000c90070000c0303d0404100e52041081600c640000a881003040343d41c0159945880b84d9075818030551240908480f502c251015400801e01c43c0c45162043d00400018015460b1490200c61004042d01c280d9039510b20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 489634595 1250 489633345 489633349
    0x20d0837030908090607140d081e1e10051002060c18010522090f0e070603270c0501090605041d0601030f05070306060315030b0a0c0c0c0305250806040f030905 70
    0xf4001d014000c101560501e10a40d500030302e480c00c004075000920462700200a114a0020044120510505201000c0b9100c2e400314658151107044658070080c0180c0c100401150071a15100440d502119080700c0820054000c1c0d03151103050702d403501c02010803c41980348645c0d1000303451000c4410714000713290011101c10460310414200b00d01d020a0301d9144104094501801078011112403da4200030205203e00c550341e03591098428541419101e8007080402440b0b416000e2201c0240130b540150310072a0325204200105c940904d5021803691900030444d188103005030307001e0318070030301c030070441810317041c01800b011100144250304040e01c40d4540076881d811801003a029001a44021804500b450006000d80d4030320116150f1170400a1420008198000c2c0c909411180000b0002484041d6080807aa01e6110f10005406161100c0001081000000b8455040481c0c021401903402e40f440350000f200b0414030480e150b82d030006020401141e8000e0b00e120780d05e40f00c2e050220001d561600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 489635845 1250 489634595 489634597
    0x60c111009050a0308030403020d0503130f1506030602030109110304080d0e1e060604050a0b010e13020c010608070317091e0a03060f0903020f0f0d0c050a020d08370309080906 77
    0x4c1126016004800e01c010981c04004100f4500601d003000390943c90120700055107241c04810103024203400c1d036008010f0120452564466200050701480425203d051810180d8428426002000d1400f000140c0034411441540c1c09164004011441e280414541c500507141c62021080755018040340216100242001c41c00080700b0b1001814062800400b001304072080101801e00007428601e80120680c0e000c41c0d9144984c40445190145842c05040c40009000e00c0c005c0d24107640c6807101c0841c004000155502c1103d00c110820605400d10108207021801410200740c1c000c10010b0701d07070f1001e80416640b04884c1d40003424400b43c130b595903260301042d2540b0a1403003040755911190001450343c14442c050b4015010f1000b401e0300c0c04110a50b556903880207005208000e4004042004c0002c2806041e186179001032105036100c00743e0400d1481c2c1d6000030441d20046511464030300080305240001c138001990032302031002c600350940d401e03400b41003820800c0390703041010017003010b803aa0348078 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 489637095 1250 489635845 489635849
    0x1d04260c0a03080105010e0a1a2803021e0f03040809040b04150503070527070210020309011e09020a0501050a03020705160f06090803040b0a090510080a0501060c111009050a 76
    0x3d40c1e100381551400300094400c945440005e4000c0c45101420b201081803031054102d40204c1c0014142c0d51900c01c000c1c0e540c81c9042001c01d004161110340c4004401d541500607009205400c920724468038001c0503500380d1032240d60308080b2500024000100841e900c040509071000d4040e0000c5000456800090700725150008034400d80c0310154414002030a00300001c1000e0142503448110541d0400248503c0c440c2810030313225104000d000085620344240060341811400c80401e546900308400d41d103000e05000340008080040f00c0c0c503802e06040850180301d040395005881d1915142c00c0c4001126142d10070710060b01455001c10411000803410000740c0303921082c48010418190503e210441c1d20a4181e000c035081246410b420f01c4880f0000c801c55089130784111075180c0c1e45844000c160764480e07059011981c4580603981a030080368114600c2da100e0510000b003088240e8980405440c9011070007000340c14040e0240c011840c40c20086280549c00ca4107051502c2031a039610b0010356403c44503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 489638345 1250 489637095 489637097
    0xc060403091715221a15060d1a030d03240b0d050408040512010911040e06010605071a1609050307230301021e1b1c050307031508071d04260c0a03 64
    0x7440c0781a416040c07010f845a0007201c001010300c00d0b55a0100000c01a01403208c04000c5180c2c4d4441149268410b000d000c2162140601980c0300f1800c00c1d0f50240c01044c40350380b0401203403094007400484c0f4061042c00340c29610280c48072410510b03203290600040000600c200d4030114100804640c580d111801091480b40050000c9000c03a0381c0d113000283d4400c0011818022800c0013400c3c01418000700d01c840c19103080b4940103843d0892070626481c40c81e50800150b5102906200303004011141001a03226800d1030f44031035113120f544806260340c55003d0702c0f5480400740852135a20200300e16a4a1001070303000140094144804042440e0350008030141e110078043c3c0019808100e01e520540400c5000c0b801000380500b10903100030450003444801700c1c602008400000209032600903840301c04059420310000e180c1d15141c25806589480c54025003120040b01c2c20381e80810301001e149584034036401280b40302113241c403004010110a0400255105210a010100b1441d60802c000051140a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 489639595 1250 489638345 489638363
    0x106060804020d0605090a2307140d0206071a0a0506010e01181a040806090102071703011a0c01140906070201110930010f02090f010c020f0f0111030c06040309171522 73
    0x400c2d141e035140c00511b0740840a403c982142c429907d135038504142130002e8050700c37443d98444d02d918005c0b0781c6401c40003d1085031101441800345140203503207c1c45c8103c000381c03252102c8030400c5005454001032104080311425400c001845039444080300703600301c01104483d090401c0c0d1901c203103a0070900c0c03c4036540000e82d801718400040c0b1852005807120000d49441d901c0c510b50500c08142c20304007906031045111000000c0c07000d88400700f54000c0096040f11300d2380d05020309003000d0841d15a00140c0d4018015800e11080400e907140030002ca49d00c540004210249141102c4070000c10401014605c0c00700180111920803281c900b03000d0416110b4540c980141d13500c0d054420400708078190042603041000c40340e000303001612600143c1c1e4410000702c4013825200c020038012101c011488609065500010440c4000c1c0e520004100307009a00c2512202d10894640100c0e00000188405061035039008101804880c11192112500007814404400c5410920040c404000743e41400031151514 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 489640845 1250 489639595 489639653
    0x1e0c060403080325051204020d0f061a04021213142b050a051b07150809071710051b07050f0c011805090c0405030613050106060804020d0605090a 64
    0x406401c02d15158503200304144001a1342c001c15a000310798210507030807071038000f08080d5a00c0d1345003422002e03400700b0210300141da41d2920768040c001d40300184078042c42070b90040c100c0d89007600940d19040881205203005503100344200c0d030b260b10100c40036180102100785144407150284072030401c5035440345d41e0200b0341c1a100300c82c001c140c000007042e60400405104c4d0010096225040780d00182100c402c0c40103180000e070700300741000c04944c025050b000800d094082d5030740d00001014070407031000040d601c1865440b0341106111990b402c001c0050b0b0012105c800700301030380754052500585401c07040c0500024201d202c0b035050340101010780d480d40c40f046050788844820000c85030a100207190021958021f00030f1084024840d002d00ea01c20b43c2804005801031590005a40041c600201180e00d14180317a680549a0007960005582c15420448041070083c050f00ca260f0003142e010f05801d01c480da2645a207802048041e005c407009008000260000c00d10001c1642007041c032a504042e8105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 489642095 1250 489640845 489640861
    0x316090603020a0e130e030a020d1205090304050d0c03020a0b0d05090d12090219090b0a0b0322020103240815040f02040e0313030b0f06010e031e0c0604030803 70
    0x4829405402050300410450003201e50041880c0d10590080d41e80d0507003403140e82d91410141c2525160342c070300b030300c4007082c045d014550004501d0f200c09142d4880a480300e840f0300704e0ba415102c0441e60141c49a0080100300800d0505250b0220030f03900400d600b81d291034580d400580d992031254041e40c03007410007041c22441d000312340c428581c0101049008000d0080c80a40140000002c6185241c809a442e01503100b55164428030a2004801a400309001622842128010200400c0c841d018085814020403c034080d007080300c4c019003000504031004035001d20328032418014503208a04040d00d80b08040700411903c4000d030300720380c800800390040d2b50405007114500300810100001d020010b200744004203078040e40e0f620341c0b07640540d801704254000001662440c0314608840c00f0101d070b4001c0020074800c0800c0743c03600503441e802a20305251142d000440340c000d119294660b042c2c0004910300a403021414400c0d0400007070400759008d1082140000348183c1140d48283c6000400004000d140e07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 489643345 1250 489642095 489642107
    0x80c0706032a090311043e070b04081806070605090c0d0803190216140111030103023102130806090a0b0f0a02040906080c090105090105101407080316 66
    0x24008050858040d0580c084000700f50380e0b0544005060340300381442d54071058403190841d51500d50803c05800250200030900a1102c000310b01540d10500c4000280d41005818002c0300c4c03a00b40c00901004a80e150360700d420003581d00c5070340c0e00700e035600020b072202500e038882d4805403080b035000300c10003c0d081c541003240e1414081408140361048854020700c100056440f8160380e04500e11102415602e60b01c01e1000d002803040c404014601541007000d5001c100f50700c0704103812800800000e05c030210405656103c1c902007800001d6010381c1082e40388925001c06c5c0840403048201400c0001c0c003003181c0c000b280499102c0b02d0240c82c2c840d018407042c42a80e500300480d6821a50110007000c519a45496000c2c00c1c40d4003502445406810802060f194291601500d014000b0780350100f0060356a5420143d4802c500c0c040e00d8000e074292030001a071031a00b42c075003a041b10340190400400340c0b81860110391708150490454041e620034881140071403452030145101e090160b0800080b580c03454005004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 489644595 1250 489643345 489643391
    0x12070612060504180c0b040f060302030411150403031d1e1f0905030105060306040b13030e130f0f09030e0402070501110304060207030210020c0307290a021305040b030307020d080c070603 82
    0xe0f80c0104410005a200c4523500021104213180050b101e0301d035440c0802c0c2444420400940c44400d01580081c60f0381c07400000c0c400c03284a5212140303a4081d168610200c002c140c3c236084c0c0c0c00491032602050b030101d95118100165001801c0c082555070341c2c0c52040300402502034210019000c00010301140c00c0912929130441011402001585031039034880d01501c400405458518201c50740b100c040501984400080300002001d0290a032002c44014004207020351707074107281500348242030703a02d10301510400c202641c0559130a03001640c40c40c1808060340c0002d2040b16075669910000c1c4065150324082d50050344190405a0340b2412070034020f10300700840080e0a0610320421000812880000841756aa5880700c49800046036440010600201660044000312407100030080100b40079402011101d020074103c2c0011512481400210f96600300300c41d8241c1d100300105000740c44e14078921095144a1a07440b450410120402ca040610380c2e80000701017520b13241c10b85203c0c11102c1000d19 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 489645845 1250 489644595 489644609
    0x603021206010509060706020307020102031509160f050d02030c04030b011d060f010e040504050a02030d020706170604020c070e0106021e0a02040506040e0312090c12070612060504180c 81
    0xc10801990000d08034440064803960600400090840d92503c1c0c2005903441507801080854507442d01281c0680070f54003c544082d080800700c0c0218203a0b00c0c22080d414001d0200c0030044960a28400c0e0681d51409642c0141b018070800b4000040200c416000642c401c110b4a101c180d01e07249140f40403680c0c0241a049024030001380b034002004007038403920140c0c1c846d00488035034148a060400503164102512405600581406d0420060240024804110f40d1090702100c00d030a4003040200d0306c52403d4003030b600010300001c050420b0059440c409070741020f0001e00c0140b6040081c0e44040c036000442e030103807401c001120300400c00141c050000c0c0303113004450845000d034142c0c000744291b1250b2188c1c0f0028482d03039540022514546441e848800ca40746400200d0346d665003070484181c040c0004039004200c5c0c0c400c8441481081c20140842608804100001c100d00c0d41000c01c00d031244145080340300000c55803078100042c05d580302d010311010a518200b006444038410304051903d1201904212 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 489647095 1250 489645845 489645847
    0xa200d050c060a0b1014090d0f0c0603020901050a08090f0604050d080f01051c0c05150c0f010e1908070c06030209041a011b0602190806012a0b0702010e060901020a09060302 76
    0x5070b071520f4042690040082c13920304490004400c86c0881524001d690503107400080e442d540d4000c014800911000681c0241150401e903503840034100c043c0d225603503540380094014001038002900078115681c116000c0c1c0f042d98500c0f841d0f00035052801d20100c50071b58042d8802d20740b0401e01074011192a0300400508000703c120341c1008042250401c00503002003201820048480034422152040d40c05040000c241d4602040c00c03018450254100030400307201030003000d440150031201481180c20300c04003a4060001112000307030700c1012608407501615400401c020443c0028071000d680e0014101c01d072001a0ae800184042c00101c0e441c003c40d882c4003001c4402885816a0010003e2044000b40d011100c0082114502100039000e030341d43d080c101c545210841a452900052214802c15081c0c0e5031024807064010002e00903030002d000c00c1d0080195030001804640c11040555002c9810300000c00c211101100341403920104984944941c0d60100b01e0040050b03118424800404180c0303425 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 489648345 1250 489647095 489647111
    0xc0a08010608150d140a030f0e011b0215071b0e0f06090109020313060207060c020c090f0a09030c14060910140c0d060e0928080a200d050c060a 63
    0x703e00803941401d801d489084e07810203480800c401510700704d4014907044c080e120103017070600d005050980c01c18496000310350469100c50303031548203c0e140303804140760801080c2e00b4011502841508084c8801c800b501c0f480070001e42d0046581c6400080c003c1c44001c1c0080402460300c080e401c003000c0050610045641c0c2c1905005180d0344544c02141550007101c401680d94640ca084102134800b02d1400030105800400d0f180140440d5034041007030040349400b91070458000e0000c214600d10111101c01c401081507001c00e00e02251980140f042c0d921a040494580c071803506c9228030400705244845c4c203035201d9010030880c2d01c01800850295109c0a600f804040320324007081514100090105000c0340c4003245186842c0034580000c1c00504d561030740350020f4104400d807113840350340c0b00100146e400142c1c4000042026034801400300030750042100c03810329440000c101c0f40303210b141024803002240c44070742c140019000e11404080e524240c135555514060111502c0c21300c1c2c4001c01e98100b2030320744004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 489649595 1250 489648345 489648361
    0x506010c0506150103060513150801020307050703051c060e19021606050606040306020a2c10030c0306031203090317011508090a080409060512061027050c0a08010608 73
    0x100c1c0c00898001c011100807200d030004031300400c0154016a402626080748c07001160156100c540c03003540c0a2030301803103146c48401081c01d034401943d1541c00200204520b10202e0b1007a0b01500c01c480904840307440745079034190303ca0140c860503000240a110810203112118000304005072480822407000c0d41064040b01d168403501c4501d41c07014082a1310b0b80000b50ba141c1d43e0504980145901c40400c54a809040400514807801074006c4e402c19002c2c92001108144c00300c03036810405500a100c0c02100162001c218041c28085103408203240c1c80e03d9002c0300044110101c81ca55114a50b80012680703114100240707802200c56440314030100300300040c0002c141c0711710f81c8207002000781020021503c1e03104100f0318094001030054542803000c580411170f89096040360088420454071042113202d0b0741d0703c0b55207542040d140350301003244841c410090001412000104000e03003038520644081c02c80a08410b071942101e8400c000d10001030301151a903048207480c1e02500f110b1070090707498540141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 489650845 1250 489649595 489649603
    0x3110409020d230f0112080328090803150a0f050d0212070303091802120f13141014010803160609050a2102010209090109020c01060e01180506010c05 66
    0x54035126900055410715a84481c2c00000c00c0e04040e140c079640c00f0424040c00c41102c0c50607140d4014182041000084a410300701601d6040e6401400c00361442d1a0100758180c00d06001640303000c444610154040d01c8886807003001c3c6071301d010b504401d50700c2c60001d403042d00c5842c28035049131240c1481c0c601403003038012480c4030300c068807410f446d0702c0900c0585000240300d90b050880d40180500c034880c00401016805801e0408481c200469031600711081e2002600307900820302041002c80c00100000e002100011030203400007030310182d41030324464030b49820740143c95029600403e07920811101107214414403a00e40b0341d943d6051b114045506040b58248c4030b1064030804c07181910701c00c82180900c58903a0003801015800011141c0c051624504500401c0712504020141e800048000020324010b001b200d842c3d00005007003d1260303007000c1c80c080c001d42100c04100c10940d0303143c1c40810078001100049020313204c2a8102180d1a000c28117070f009469000700324a0410101800d54000248001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 489652095 1250 489650845 489650849
    0x912051002030a151d0114010c060b010513090605030f07051005090f09190f1a0111030c0f07151b06180c0902070203060906040209010b07050c0a170d031104 69
    0x140096960f88075103e2500141401000215504502400c006180c40c03002090003400440466034407060303a42d42d100c0051040060030403901288806144c503002401c6a03001504084050400c6810b00e03881d0320080740d10b0f007415088105079680c1e40b0014485407604100700c41c18129141c0041c01014100130115003c0b60803021030205025022039400d81070f030b0b2440d244014628003e440e0101d00d26101a107644a040300100d4510700501d8401c00340300318000d50103007001048068100d00036131100f0030011600000d85214628840c00203008010600e0000c0c0b00b00c1c00ea2091040040000500380310304400424a0680b500e01446109400c404002084200070144035400c1040022644c5400a52a81e001100b1070000c007003c08480c8081101c1001d0703405020075078000d0341260b0300c0d5595000c03442c0c0d48010a0718003961000441c00100000d0b02264004c0c09418800d1050381c141f4090030001c148200d21070382141c00c5401d20381d851407056000c00c01004103191900d1030705110038004000380440c944514 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 489653345 1250 489652095 489652123
    0x30f1506051b01020706110304020f1f1209020603090604170717163507112b050703060c031e200708070c0e070219030c080316091205 59
    0x40c908407400c00b0a6041e0355045401c010140041405000c03005050740c02210700300d106129459032240c9500b070588000740151a66280c400c04403d0f410b0055551561140c00b108040e600c480700b84005072a2800614041c4403020300802c841c4c00c0070724000400420302c4540184c4070a00344954408210388043c002554040ca81e55240d440110500d041c0d01b0719a42d03640a0f00c030390488a0801102403d01030350181c040c400f80160038640c0c4207507080c0c0410b4820503001030004802a007040c2040e2416007015000c4070311200c00507400400e105403200d0701000030001a00c0c50f820150042091242d5401511038910843c641040351034442c0c020b8000c403068100003001000c0d42d441080c13040b503e60003000349103a03007022221511a5a2480c001e11140e10800c401c80d01c08400b50030004500c03803800c00f0a406501650003800134409880505100c8040b0b046054003044828507a02000c2110400110b0040320802004595600304a601500d103000c9a880800d08044090a04001c2a004504000040d02ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 489654595 1250 489653345 489653377
    0x4050f130201031503080a020c01090803040b0306130e0a0525030506040b0403231908070207061407080f0918100509040501060f08030d0e071a030601120c030f150605 73
    0xa1840080e0311340c0c80c140c00084c20484c001906806460700000c03200409542642d4400140783c40e029800e480c2d01a5100c1e1600d180400c1c0041440c0c0c1c035064a1084590840c08000900404110a11480c3c0020060181c0d01c9800510201a00029000c18020b20928a030f0041511524641e9141d542d62030082003c1e0a6618500105040500c2112880558102c0d1140c2000d40304c038010020b1134071382c40400b046040601d0140d405c45858010b01e4071a00c165619005080114580042600c0c0c0c603a02440300580f203d020801c1e0000608282c02502c030b1a0450266035481d19450707414071510018440070185480d900b8000c103c1104007c2d10300c2d4094900640d00100f9544680c0740083c0946502d07005000c01803501a0040b4000c48000040c0c400c09140500034800c540c3c108071220307103504107030080e020015610301100024441d107200442d0401e9040c035144580400c0c050200c000c1b5500d9820150010352180c2c2d95018071000740c0034042a4000c0c07152800e030380a19110016282c2d100c3c5400012240030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 489655845 1250 489654595 489654611
    0x50d03030905011401270c020303010b07030521040b090c0604091e050114100503150607080c0a0309050a090501050d02091f09140a290a03060e060604050f13020103 72
    0x10b080d0065460105040c00d03002c15540c5445040340086011008468218106012420240c040d4000ca9010040d41d8002d1855030742426400503c5a01090060f020301004202600401c2807010515940500c1001d689019044c1850001c0354400064070300c50079948000024a22503454400f1903003160062a40010b0424400010301a800c000d40e19444410745042c000061016040d0b60411002e50111010180450310305000e0358180400c3e1100306e1064884065003d00b82003030700042c0071441c0a41c001c2400d203c005201c0518280c6a20001c030001a00d651040085050050600c000381910740000c1c09030750304100104000700101a006845840048040b0303859845a0b42c088800040308100440f92549940010010300041c0031303400c0640900a001030102a0148070302c4141080f07816621069004a107404400d901c10450308650205125000100103509440340151420749071000d0006c9151100810044800041002d04030942c0c0708c00f0800031495008490341e070281e0908000072044d03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 489657095 1250 489655845 489655853
    0x108060307170606100e301005041b141908010e0d0f090b090904060e07080303040210110309010f11010c020109060b011b1202070312020f0d0513090f020c01090311060a06050d030309 80
    0x7e10340ca2440941d03000f02c085d41d00b4a0f13400d94001c1d40c411070242a0011540512507002e19075040b041c0304945201c50042c244061a19080c0c455140b802c0c0102c624000c0141c0b9801410b00710b950342c14008001e40d0080d0861095150003030000c002a0290703081029600d80f508a000ca018820b050348107200c0c510800004040006075806170826007081d4084881d20707501d80c280b49659a00030380c0c0603407042c840c041c4180c2c1d0743d80c40349a03490701081000c4040c5003000c1640006490800b0351400c00c0f824410039801819100c4024861040c54482c01d42c000304801d9034a08060f400c07601024203050400c0725071201e20010003150384518030b5040e0700410300991a441e140d412424890b050f00010060360135003259442c0e55600280d0540882800025504250200c1c2c030280c1e0380e441880340c15005000700540400040b84103602112450384a581c2c09440c0100c040050760840d481c0b4601100462400c10314404102d034100801c80c0d1020070050104007450411002030000688024010100354460410000304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 489658345 1250 489657095 489657169
    0x40b03070f030302070303121b1d1c06110906190c080a050702100201060e060d02010e18010e0a0e1b03010b0a0e01061101020313020108060307170606100e 68
    0x3007080e0a52403118076103d2030300a4a40160b8402030300021031100c0f00c48860300062245c40c40c1c081165000d900f0001d012407094030030030458100024a04803040506000391607202102d0700400070504c003141071402c075180610454000390b150408a030410300c0b0840440e103404d4101d0300c03c0344e950a0350316054001e0200890b9454682a001090030101013410010950010080c080444c4200c0e01031440c805426412401c8601074802d2a520302d0300f650220b5503034103284010281d1940107160120a101c4400040b075614400881e1a01c80040b103040104800d059040c40c00d41c11400d003500070320000c0c11600c1e5560780c60300f9440001101000c08074461f0000d41e425803209108090141c200d0408903031710410404040302c240b0035440851300903c0c41e0010100e042c805c80303209601c20030900798181900d40046a1601000703000c80c0d094030510801089108060a072400420b4140f001440749141140c00d0103100485c101504080c000c040d002c020340c0d0707030b100400b03001c10601d0841c5001d600510400c402c208 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 489659595 1250 489658345 489658349
    0x60c1605030a05070311030313060209041107140706110a20091003030305100b121b030f070306050d150509010f0c030b031b150a03020d0e1c020106060e040b0307 71
    0xe900c00003034245845500300c0050310322079001c0e03210001100d20085003c0d4882c4401c650003141001000c49a00004201d5400341132070f0080071b40002034184031151070001a80c090074058030350660030300d80292210010440c800142c40c55103455401c041c2030803021991010480f000605400d002000c1d581c521800100104014a00600d000031606001c0300c40d680c0400039000640002c4c0c144070004201e4502c00320000c04072000641901e16080300045800540d90019050808864030f00c512000710000b04805580034204c907141b80038290412200240440d40789901031405902c0d07050405000c5400e6a10380d1101090490011031a507031800300031401000e0f00030004104503c1c00140e0303244598168042c0150013001c0d4203c84001100c00100f0240c04100c5201c0da070301000c000340c2c804985c0741c2c800c040c2ca00c500300c5007405130400c032100e040d0303006591140760139881680c010003000e00b0245010502e15485041e5000030440f1504041000744551040c00c0d20303501441d102c1107a18130b20b442c10010080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 489660845 1250 489659595 489659603
    0x31302011209080a1106010506090d1a010b0c10140a0207060b1c0308060a032402040f1202100804320115170c0901050f04020d0c2c03060c16 62
    0x110010a01d0950f0207070f0412900f100000700d070300000c80c01000d00000c03124161000108424204074952040240480703603001e04030b40e81502c86070031003808458840d000340613140711402d072600da6200c03001c1c1c0c9183c80342c09200c4110381e6040008103c403800d4100c40c140c2d042001100c015a441000e0308045c0b0151070304468040d00581e048001c0a005d841c1412403801c80751083e45c42141d0303506c40508201100b603040c0006862110680703103036001c294003000c140012040702d55000d400c00b6541d42d03800d0bc0b640d04940c0841c04500da072400d600118508041d900480d05441e040c042c2107405d05032508101511520400d0418102a40f188143c0d00022081d8070000042a0001d0182c8012440000c407069402c0c440e0901d031007040311400a00310f8000c940501c1c0790030041c141124580c85c00041000c0902680c400c10381069080043d0440114a8000d218408a540e1502e4100c8001102d43c28450034082e9104055040d14180200c0c440d500812441d8104280c40d03507054580c02910746010148000c900010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 489662095 1250 489660845 489660851
    0x11070f03020c040e010608070501032a17070206041104020d09022d10020d050a0c0813050306010603150e0901110a0207140d03050d0c090801020a03052202060313020112 74
    0x58205540040d00250050082c0e030148079450141c11610700b0380e95540507004082c1c101e5601440303175511070b92061071441d42400f005007820705000007801245281623094070000791a041fa20b900e444180c04015040503491000f4602440e091321903203c05959458090322454000030503500c92101e9400c404034140d001841d0701150004124a0001150481c1d10358030700c2e8140804182040c80d2040074000b69850300c0c0c01a090700310500c201220350fa03006400300f406101c1d220320301c0300114002c8800741c0201d030081d006280c0703070604060400d840c02c24164402000c050600380140702c00c500c40c020704400c9682c440f03880303c0c4c43c1d10354905443c00360500c0084210640c0d004500a11629400500741c021143c44c00c1611408245000902400088004020f0042041085001007110440d13020301d0f514001454000c6005032504900c901360b0388120301c1440081c3c0c48200303109440110480100050010302c0c079103030720210580c0c04079141d80001090610000400031101d815640a04c13034031611031607045020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 489663345 1250 489662095 489662123
    0xc060c0e041401030b0a02070b1317190206010b0a09060c06091a010e01050612071805040615020601052b1106070b01081528090501020c0a14010b090402041107 70
    0x16600c2c0600910066030005030303100109424144074821914000d8000315040200d80d500c3e4101d000401d041031040716a4055060100e81c035210b11805403801c04191411345040c0b4180c200024034141e4187c04c0155910b0080020500003604542c5070800c9400d10b0070844d41c200030078248400108100040a0312075241d140f4100d0368040c0003841d850696041c800740803042e989900900980d0f00030b0500ea405028403203404101369038040c248000805810800b141c100c5031b11500030030155012680f00620401311815610325081d014400035001d00820f0312815403900011441070038000b80300c2a0500500311000c9584107004015482020070640a04007035a00d90b81c5243c400d4089d042480b5006450050510f40c08812800680060252901e40c04000d50300402000f8000d5004e2166100f0520a0380c407011345000440a0018200501d000c0c00035020020b030a080c02c0c1c6031035104004008060345880c1e40170b031a507524800001c0e000f6070180c1c2c000451141d00d03a035011071407143c442c000d05005081400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 489664595 1250 489663345 489663371
    0x60b0c030c0f03030114062808070314060a1e030f0c0f0b342001171b0a0c050610090f092d0b07020607021c0c060c0e04 53
    0x410030807156400320742081049409040d182c0c00280030380010707100030400d080070300c0c0b43c2600a000f054004540800c054403220345e198100c9a00103c0700c3e0003052080e01040340d01c0380c042c071584802411704407004040e49804030000d883e02605018142130710521319500700c1070000c2410703013070007643c3d00c002104519401410007034140c124600c43ca83e001d0000440110b00c100d012004e9440c0d100d842207610b00704160280d8103001500110023500c40380d641000d000c0c004180e24481c1c4540c144541d10494071941c642c40d000510028000702040c44000805040c8100c90030055014000501980019510741000d244d044510300140c40028005100e08018005124011000d00d81220381c44041003204031592400e41e070584003410406012900280d007464681110500c42c0001c0450402d8541440380c9030b0b80d10407041080584a890050740420100459150100217160051642045000c46800c0303800005000070480e140081049490702003007540f850080c00c3c0c0800340580100180f05650480030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 489665845 1250 489664595 489664597
    0xd051c03050901060f1202090403051e03090f010507020316030e0901080d11070f03030c06023c0403021e041b0c110a151808010204060507050c01080601021c03060b0c03 74
    0x40b101034a5280c07001c0020b80909070100041143d290f201200da1444241d001c020450800030815824400c00704280200b07401c4c014038404003250615021522410080e980500e030412060a01846030f00d4203042c40001c54000081d210922000b41016000c140389141c2201c001d0740c0360075081c2d040189030002180703240000c00c42e1402c0001c0ca81c1c0c1c5004002220303403125960a154400c180000c0560300080c00842c1c4a064260385490044001620307003841a010a000703c00000c0e101c0b0a1741800681111800c0d5002030070003000038100307130340509050075600019a291100070001d107924a0940068407a6100c580103400e0708115003008a00d40da103403100140040207007900071215083d4400030503010386050320b444019038900c0c2002d04e502051041045d150310007507045015884403100400034400300240000c201510083c0d0320f00f51a00c803d80340c070a140c010501c2040c0c0c18001c1c0142040450b1f64006940c2c10b03001e013120a03030011404008400d0300146520f410513000200c00007032801c84884000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 489667095 1250 489665845 489665851
    0xc030d050702150720031c0b090705040f0501050304060902030a030e010207080102030f0c030714030406150821031005091312090b04060c02010e1008011a180d051c0305 74
    0x3400b900d00c4803d030100708040d4020211821000300d00d03061428498007113003100f000e80031148003048a2070200c0f07c5000712104d1042d140001005619020828550300b42915159000703129070070102d06050410300407a08800e85030087c42e041240110005081c0216900481001a00541034450402c86410020211850b00110301d0243c0f0401c0130018a4800c140b088034410012030003a920180c54050020301250b00c00340200c000c12440e0800b050040c0c40700401180240c0c0b1a15000401c021410039a14000d00310740d004950503000207009a91002066802c1c4040c507900a511a5a0b680d45c039079050f0300210346800c15a0803040040400600308005041d03240040c0c0180d00c40c040441c121141113508543c50f009401d80c00c28180810002c0c24001e60038180300f144141804810100400080b8420800c100c450a0001d0b54080c010800c288420b0f1003007110408041100e4604603412458510a02d09004450b000c1e001215403101444010f20910344150440c41da2100c1040e800800200030701016 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 489668345 1250 489667095 489667097
    0x3150b03010b0d0503090405060111030307020d030f02211f060e03061303021504020a0306020a030218030c0a0b0c070504091505010819150605060f0d110306010e060f0c030d0507 78
    0x2029603400b03580b41010b8401891a445001945080b00e007009000242c00c0c00b0302010f0610000740b0824814130170900c0514031551240d80100300094080740001c068500002100c1041407040000f40004000300b9186569080d801500c0c000075299008561030407407981c0124400c0c0e0400500110700e8a6000d00f41d00c00c40c240850843e040d07502c9000f00d601050003c040c2c0100540d004000e90351418070341e100016440b40c002000e1440c1d1960300d403030f0b52040c0c2e8440d0342c07102e0020394002001e8008000150842d198030109a004251014110300410b603166010300410001c4c85c1d0102d050302411000304903040151501500620601041d450401511a00b1a80c1594210f090500120f030005000490b0b040e01407120800d200d450ba065212220381e0f400c00ba86442800c0c0d218640820701f9224130f402131238400150001030f592031340151050011541005288035002e0000c10038016685c0e032004841c800003808503400390360f0700c0007265860310b280319240c07000141d4000403c8110060620f0380c4844e20401c01c0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 489669595 1250 489668345 489668351
    0x3081506040b370c1704090e061324020405030703030c150e03040e150d03210b0306040602090a090908030a0c0f120b041d06041a070c110a03150b0301 66
    0x180d4440c016528003614040d0202c6052281c500861040180101c1903000c1c40501d00c100c2545e50384045c083e401034003d6184142c5a441000d1110020060700343d1101440000b003441a0391b607034036030118800300b00780b850317141144060b4042004869030482c0c1c02000c1c01001c0362902e959030f00c1c000c7d244044038002960180314503070070302e9502d985038001c1a5116800c42c0c05075240c2410907400240107800030340032002c906c01c10440940c1584802ca21648928026250080c2280c1c01080c1c0d1103808586a21039020141004103104a075180094200c0d00964040c40250302c55004d640803452050103940325401c41424000c0340b00901013004000c0d80108040e01091080324403880040e1640c040d030700070503000500040c89115440700b140c1d019001c2d05000410119041d4100c080c42c1c801140c5d100340e1000c0c5900720f901404108050290610304000310981c91910b0351900220242c4020000303c0081d000184808522603195210726820380616070000052501e403400005900082859087c5507019601e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 489670845 1250 489669595 489669637
    0x501030501060f0203031f03060e0f010509011404261602150301050907120e010c1107090507051c1d011d01110904020c1c080403030b06040f0303081506040b 69
    0x3215400609003070042d078008614644038040180c1e03490080040c210124180814080002744c0d04c0d008171080032010300014000c0010080c100b03801c40d880600f080f10039030b2516110a60500444004c9680f094100c081c0706200c18009100f1816003101a224050012001a04c17481207016401800f039280e000f99811420071a5030100c0c0203881c4001e008650340020040c0001c0d00b04c52182e40401115800e1290106d0b443c40c40001c0c03c0d09582c040c405810100b030001000ca00500000c101c1d050050501c04d10078051400c00c640013600c5031044407120001c3d500380b500003401940a64020746880c03c03c0280d5204e15a0a9100080c003d14881c1c031502c4144002650140b00744e00305004d598651083c200c1d10718a4040860200320003035021503129401c5000d01603226259201c2c455540c0460380c030796140c400c12031600e490f008007110310416645100e01c13400c0c04140042d083c04c114040c01e4a605052692141e1100c0d50140f910b8004200e90710350003100000c2c041100220000517292031407410140c5401c6032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 489672095 1250 489670845 489670847
    0x2e0b060d05160e2707090801020d021c060608010e040311150f1f120314030c07020a12110d021f030c110109080d02070f1a10080d1205100f0906050103050106 69
    0x42c103810b14604005891604d00940090080a0b01e500801e15080502006590341442800d90700081d08510000358089056455912040028401440e000400300301940c180b0300054150803060080d5120f00703111100080c10580603c0f54100d8805120044400d05281400b540701c1180007143c0c00c1200301420408208000c034040e4840d140700b80301498410216007850716500a10105402c1542000483c0b510309071a043d4280c019801032140005480d81ca0129005000c0600c2c11540030031110350400075004041040210b8410302201c08807805151311440b40002036405e100340700c1c0c4808014820014075800798041c0d10280008101d40c551505007a501815a422a4841040a00f081ea02001140c0c5840400c2e8010142c091140ea401d4128070103e071180358440c4a800100144444900c003480040d040405c040740061105100501c2e003288158401800c010036030035a81d000d02e80781c40c08260710759402c0300204007400e140c110401400d50f0312805000904418031419010074a40070001c5009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 489673345 1250 489672095 489672109
    0x417030c03042d3309060b01051e030a1b08040209090106030807120915090e0609040305090d051e100b0609030703081602041a032e0b060d05160e 64
    0x520300003601d40b4200034107884040281050520501d900e2980070503030480c0101001311110490b80c015000105a0031618020301216103a000403814007070144400c803015481e00c44107042d1070740da21480343d49030740f500120540509900c0442196250840c0814803502d03a02c803041c0340c880d038001c0b1540c4103540c47d2a40c1003401c07035800c2d00000d072030f40b81c04002c64408150b5001c141c0840c01341924040449a581e1080303d46140b8101a440c0001031410720104600c8091b0882d664204004603110001030400c0d40d4081e05d40d201d82d44815008200403410f000a00c002400f40714150150070020f00311070503034814415101e046d103180d0000c5091034105504001e003441000d880800001500902d0183e045490f4020180c00c0120f201c1001d07000c040c1c60354016115030041c3d950b5a40b4402c0b684441c00111010113007012030b108004290b81201412104800c0d82ca5200502281d0300072900058240e143c0000c07548902c904104400000e0805041c400004401c5045a42da144a81d0314480c5210b2000108045 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 489674595 1250 489673345 489673403
    0xa050f0c07030516020312040611030301060503040224041d010e0f07110f0a030822020a06030c0c0c0f0e0f06030604030e010203090307090e010b04230417030c0304 72
    0x2141400c0c0641e4002a000d40c0c01000d4a046424081c10801900d0b40002c1c81c00705424210130844c800450100310060b0840714000d60b244030310340611300315030403e0780092035408000c0011f441494590034102e2002e0260701c01d400b684101c859400e079502c0c0c48170350f44030521075640c0e05c83c013050241900014004851055244c003a0048016410290b00c40b0b8400721240b0f80500f002106a000c0c031080c6013810041004800c40052081e164900945401d09020380c2080c1124490750300000301041c1c0200581da06130700b51051b605d0710f080c000345035441544111080101140010290400700ca400700d40900da1650030b404590010800107155a5040a03803c4503020984045030594082400b00380060300828145050703500610480782070100f2580000c0c9400e6041c0c0c852810705036505810601a903003030050141c3c8003410383d01400100b80c41d145020045a900e50410003a0b10070b076021400b004080352580b925080c802080d640c403030508118102680c0d00684089409091244200040c44218070908003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 489675845 1250 489674595 489674611
    0x10507021003050603070b0a0e0a080d080106081e0108150c04061d0622150c0302070320030a0305090301180809130f020d050402030c01050c1f020909010803030a050f 73
    0x30402680c071070035006090301500080d4103004202e404916495440064644c1d44110f0395680e4606865034244220015030b0381029003203802108071103001c40d804c035810b0390444007549400d039090b581e0000656101d81020402c200c0c61040d03507000142048001520442e03182451503109400d803507007048941c40e40706921854001c0380d1105024a8104030040352080c4030f59016003101c0c5003c01620040851000040302d80146002d520020f2003021070a010340d002402c45400e20010314a41034402a5545529210060060340c48220401c0002000c034030820314410050221020f8440900e00038000c2d40001c080c4901a40ca0212113403500c81201004010460300441e4003840c20110f18244a842d032402c06190656540300c0080c3c80c0c0b203c4d901c1c8010044138000702c1c0d001880d418203104050401b03507840c0d0f81c1410481e0905c1280301440e0007080503080b60580c06294504d1100e041300303100190050765401640032a40f1800001d82c0c4c02c0120066102da00b20071002c000d02e6440d004481f6081c1c01c15a4101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 489677095 1250 489675845 489675859
    0x141c09060e0409350c1207062c0114010303090b0703030b1e01091e060c0302190305120a0c0801060513080109030e150304030806060313060e0105090c01050702 70
    0x810140144010000540064000302e02c090150f16800c500078611404800c20040180740c01c1c00051403502044e1404021440c0c1c0d900e0060f0100f280b42d03503030710500a0b02c401241c00007441e4040100680c440c3d00e505c0c0c081103034110040c107090310718080120196041c04040d400c0560340025000b03031038400d49c143c1e90b2544865014605202120f03001c0c2c1c1080e14200c0a0507500c0e000c0c0421642c90300c4c041d031014512032003980c04d511601c41c001003252009034014403a00c41d81c102001c00a558100041041e50a03e00d4084800e2006080481c03900540c000240d000200300c0e9480814554000e0050010a8103040f403885903855046c01d5000f112901321038600060040401800380500c580001d000d1004c194a40301103040d10b450302242113540c5820101c0104601c040f40700c03501d0800d65602401507100307410880c158a402d86001e044c501c1c0042040788103034800000103441e107519440c40c042c140c0d00a48200100350307420013245e00818007681d400c4110320072103807642c002d50310500440740d03550307030240c680 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 489678345 1250 489677095 489677099
    0x180103050a2a26120a02010c090b1219020c10060506090a0314070308040801020307081f030b07030207060c030504020a050a03170708070f08040609051008040b0c090d141c09 76
    0x1d125041d5621101d240700c0f0300d074411100580c190800c00100d01910b461060b039610072845002030b0031143d00c0e007161814466844020071203181c1c0201519480800c00989002076a0b840e9403059019481010110000d840483c4040f4501c8002514a0b05914001c20800645441d80104031590003202d4500f0ba12101c1032105000085000fa41402001900c0049400554607960341c80115000350f000014581e502104000748182e01c4118640c00c03400c003861107081416016001030500e2001e01010302040e2180d0b0201300b0b0b171131190781160f086640140041090a560340e400901912003038030281e118988021010503a85012107811044039402422107840c500b0b00300c003034040742d0003401003910100c00c20b202c0a00481e00c0b06003454041c7d88280009545d541c24081c1c0031f0b0880340703903400a0340105102d00e148004039401140c443e03081a0070010b035501c40e5545514680703042c801c102803d908205140300131030400c10101c0c4550080701580040ea1302c5030240e26481518081118010710000f6200380003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 489679595 1250 489678345 489678359
    0x10e0a0e0705061c0605040204060f051e0c010902030d0f0e09060d0b0403050c0106120213051503030d020a0318050c0d0317070c03030c020a031d180103050a2a 70
    0x40048a50410140c070a155500c6000031a1a000901071040d41000810b01180000042c132408002e0201200c04506150130070728002c0c800512800c0903014030000080b070130440d03044c80b5078280c43d041891186603503803004480035074083c2c900e02204900903c10000d9003450b540c094200044c0e0780da0b290761201c00c450442c904008007104058016a040f402c9201d203040070130f44091041d803080f4041d071034480d07452203101d04050840700da0b9446540c1012206460000590352100032948249611201141545440c60000c0588504490950b03042c88009516034210380290060443e651030b640701003040e980441d812082004c48141c0c000c0080c0c00211805400f441d100c6400c140c600d009203045458900c0d6080c82c0b151542040e40c403038011641c442d0200c41010b80c140600950f184880c40070703060080845d50054140340d0002036003811031000301001000d0b600c842c11121161400514290115652824607949815180506a401a10b06102446e80120134280300350a0a544603030344100d5454029 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 489680845 1250 489679595 489679601
    0x9070309050607090b2a03030901051806131205090a0905070306051c0201030e0f0109061b0f1e02010906050c09040608031c05040c050d0c06030516020a110609090406140609010e0a 79
    0x303542019901c9510b181b4117203c2e4100041c2d8842e01c00303080006440d050001120714250ba0160980706250b1000c8100010f0721034080c0d07207803101580615000300d41c0600705010f44950090110458105c0882d45000548451981215000e500e42d0b480070008036032908188804070303294407c1580a00c484c0c1d01104010351199020b000804c503014160303140c09061060540c291000003c0548190f85c682d00040314651320341a1200b00d500301c909000300d0b0494a00c10181040510b560740800741c04850607288800b6000f0b4000c000c446500c0fa804118511300121810765036080300000c036010304c5c0f030010b0105014078004215001201e480d4040906042d0302c60a0501400c8010403c03039804400340c00010b0140c1f00d4000b041d403610b100300c881045090500100904a460082026541100310640440a20340100741c00d90391b2500a000d241203004044040340c0640b1400c04502d4110300a40704000501c5015071041414034a01c81c140311031922540100322a144080c000c4604022529020500400030b542c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 489682095 1250 489680845 489680887
    0x1b030304120e010e030a110409080309030405130203060108060114040803070b01080f07030f0602070303020706020c0604021921080f1c0f060320040e0d03090c080f0d050a090509070309050607090b 86
    0x4102249c0c00302c0540c2c0300c0640760400d44103445d8a0307202044c2071009141c0300c404000c21400303000086081d0710b88200020f001c02800b0303242ea414000c409290304a80701d4000215809481401e00302c84da25800c0c0d280054056000f44107900f00c1c0d00504d0440c086510010a500048907002080d6000c4803c854a4440081d44010380803000e050b4200260300006400b070000d0181110080042c02091901c4d0040c0302144044a04c1d4010700c1884210a0095020000909040c20000c3c0703010051030b0f600d4900341d0700510821070b84000c0184040b6410740d291620039044001c070281503000388425074412890070140c991902004020041c0f9000100b20f00d036403d8030582039103100500100303000640e880e903075003420725404013980080c1d210003402003480343e92101c0300014071488000b400b4400c1c00c40380050b2940d0070000c0b0035040200000317410013014070840c0045d001d00030003043d00f001d0b410041000340047c40419011a081d0240d80001800740303020380b0703031031044503100c00d149413a0910715459044001500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 489683345 1250 489682095 489682099
    0xa14070503031f080706050403060f29040f1d0f030705060c0a05120109022a060a1508011e050106030b0906060d02070c0b040e0c031302061b030304120e010e030a11 72
    0x1031000202c4c0d2004100080081c0003030b403a82507541e4210300344a403d868000140e4218a420882c00031050380d244809044181100381481709010200b80c0050b01819207019440030351030800c051002e06c40c980c0030200c0d41002000342182c514650080882d0b8483c050840b0260103904640009072201d1300d40d20040234881340b03601d0624a01100c00d0200070800600b80c204c1500035502281607690104100e4140160483d07103000b85004180311004a41d83da40010100c1c0d9480c5e4681c2c06481d44846250095009005654000e21100c3c55107800c0881d0403503844100e0b91644d040a00010b1128001d01c5800002c1001902e0340403641e40781c0c000d0100c0c40d030004540c902403980c204012800320307946000201c00b800d090100103640303d151040c43c040e00d040141c0a514049010018818091030b0071003000030656040c1e42c1d01e52502c49049111001d2800e03400d20b010701e40030000410040081c0d044021040051507180e103030301da1941000444040000e0900e141d091740c002e0340c5850219156119441c004100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 489684595 1250 489683345 489683401
    0x2d0301140109031506090605060f1801090b0a1e0314060f030f1207061505061b030417010506011707020a080f090a0b0c0601090c09170a170a1407050303 67
    0xa290307103551349104400501e0301c80940d0384505000c456010301825008045c2155810308140000111004074400c20085024911400a10703900c40c0c0d004100380401000f98084c1c00c2d0f00e44507100340107403c082e016a0300051021085600c480964001d104210401e00c003040c2035080d50341c82000b80304011441b0384503282c4c5440f450001800643d0200310f00c1040d4154100b03407507154020341c502001600e1120b030200070a141030a000b03000c20b4803501c0c01d07034100c0060b00e2040300f16162041c40050551190f608403803410041c0c6980c81045d502c0542007103005100a076034152680005103410200240152049001600300304e22400101d407041c0c2c05822489452030801b864589080001241c00c042584601007101c80414065407845040c8001c0e40180b6108400307100101d9030307100061008042d4042c07666050000840941040010049003050780c0c0c0c007000203001a48120480d81142c0c00c0f4601800005604070700314803a4014200175218803507400401141903485121504040309440c06040d649081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 489685845 1250 489684595 489684599
    0xc0109050706030b03070503010207110910030501110414031b1509040c170c03070503060d1505040b01050f030a111021091103010506030a02010305060114030c2d0301140109 76
    0x18003072018000030001c98900242000d00c10040c581480043d6010302d01c240d1062140308080768803c400003a000200f00d50010055884200b82c2c0d48480e035030382020b0b2031586807410702c0c1059440c2ea80108244d8001840624000c207104080507030b102c0c0f098008402c0c80107500e034001d92a007403504031203290341c0903081c0b8141003005000100d4202d940801c0da01d0006141094102120440c400c46981c1044030320300054558641490090920720016207082d00030141d50100c04107106100c1000e90183e599808103000505150400314030314042030003500d114010340f10079041149400500840d196600c490015060441d0008000981c5802441e20042c003004418044601c2c3c08918280004100c00c480040c2190b0ba605100d44078a000882041c001e070700d40703814130030961341c0080c00d00303041582460041019610340700100c0721012980e0240c0203c500220a02c10552000005030510451400d1000408002d0403540300e41018851342804000100304018025100614403010350404181041d0f41015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 489687095 1250 489685845 489685853
    0x102180913140c01140c0d0c0305211609030b010b0310050a090c03060603090b0a3308060601030c0503010e0408070f08090f01090602100b1302042d0b0f0c0109 70
    0x5400401044641c100414400484d81c000500080501180b182c0d182020f100181442d507420003000d555040c49114815102058468001c640d8440403400685203011a40d4002444400c000c1d140e9010014a0f204156002e81c8116040b80449401004a26036a46042041c100c164005018070800b4507110a0105094842c0704c180001048030100015070362045510003011501c0c1604200e042508140002012420b0b100105420955050002a061100b540d05a803100c0c0c92052030340180d00294010341000340584c6030319003103c48102c240c461540c4d42800440c00c60310b586100001040b401c1c0014000c000801d001664054400c40e100e5141150702d4030303118104010083c0032203044d040000e6500391070422062040c03c0c0502800e28881275400e00502a44071850401c42209980d17540070341c03c1d4150b644019200030704100c0b010440d80d1355140ca2808500c2050355009200401781d03030018510b100c0e48100c038901240e02119456041c00d400320394081540d40403903402c615564a80003004082 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 489688345 1250 489687095 489687113
    0x1509050301111c0e030a08040c090b060a03150306060602030c1006060504031e0203030d0b03101b0e01020114180f060903041a09041103100b2503050f0a020606120102180913 76
    0x40866154031f660780c60507143c83c0380003000b550031805030a401c00c940f10500fa200d11003551156082810089500b0180b8007140d07803101103507403010702014104100084c0b1103130003000420700b000782e10b003d03a048004105000c0c81036401601c101000150104410400700741314004140c0159428116428418600d80000b861500841c00c00c0d10890b5a80140da149403808000900c080c142080007400805010000c0c083d2903030000c0c0120040c000c640a40d4041c40e0301c00c1d1312145540030281d01b42940d5041c02000c41c40c0341c91403803d06801600c2640502444000001885880f03244150011b500d800d003030040040102a013002a480c01030814803001c4100c1da1103003c0c12040c140f025944944a1030034403070018003001d02c1d500102c2c10003420001c00f0803000850034503001000c40e0b03c1002c0741010540c501250b0720b00ca20036081c400090003040400840d9400308200303004060032500e2080498503d40094200c1c89200342017120b030b034034490210320a803c15000203603000c1c00c0c1c0000388821902c1a1a603200c0d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 489689595 1250 489688345 489688357
    0xa110f060709060309020102120d0f0207050303070324050d060209060a020109111009170f0303040515150d0b0a18150c0e090a02221509050301111c0e03 67
    0x5aa0090400c0200ca00c0e40018540010002840d06218524150700042e48074480d04007241046600013a40700350b69041078125400d4120905011540c8440d1800c005480750408d40d19200001c0c20000086000d401000414104074035411154050350301d0401001102d202030301080300d00617000e00040d9101ea0310b0360060081c40c1d8050300042100513680c0703421105044280c0038280b18850711b14070100d6183d4029001d40a8481c00d0340e8425070b121007e0031803854212907000c10f904620000041004016001c00c05204042407402c001d07071340c0d881d00b0341d24405200000c0071407a0400c00154464001c1405640201c3c0c1102c450800019001101032052032864500038082d28015540c0b01c00c1e074902c000520500c500c541c8640740c4508202c2d2504006140361102400388100c0035004509005102d03064400e00b80000d00031240010074541d0307420903607680e0810303c03104404107004c0c0d1000545810180182040d041076015403502c1d0081054100303024060100f8420405651000d884222000070002010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 489690845 1250 489689595 489689623
    0x603080703030e0721050705030706051305010f05030c0912160e180a08071e0c0509090d0f2102070602040e1302100c11150405040b0108041101050a11 66
    0x164403050341c100507040e1820050494076541c040082049441501c01152042c0d0201c40f000068180490411600d0580c054200380e50600030b603d07000030001e400070020000800a200f800302c103e0390f81c030019140540d201c10303060080f600070400140483e503e0001080c041000401703044101c80700e41d41491030610a24000c01e00308803e4a8240441a4640786082c0d02c41d059465448588428000050701d416501d1b60050005101003020300800180c0bc4624000702a008043c00200240b810310740c403071640b903100c0d2500801c0e81601041c0354003008259030644000e0b40d00e52120040500008682000c1258008031000302400c2c401c5000014500060100b5801082d01580301d03410301c0362607400700502078032050b54002c8640e200c00042e102c120701040a1700160410302070096043c00c040d01411203512034507502c4000340381c0411561000c00094400e40300d0036030341004213070709020054410781e4003500c01800900c007156030103c1940c424002800440245c0c40d09101a1900c1c0d00214580801514054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 489692095 1250 489690845 489690847
    0x607020d030f06050315220c09050106020c0906090c0c0604080405030c060a020a060b0a0b0d050702100209030316170406090303020c1f0309080906040603050402270703020c0c04060308 81
    0x540c28903498001c1607140604514200301040c58413000954600008403c8055144000c00044816164101c0c00821300c4132003c1c5985410900c1c64904030503211130088960091407e4000b0802c0d1f0310005100f45030f0b80001e04805041d031211410458400c1b03009241e07001c240000c1044198100052025038012403140c14440c0c3c80d5400c10041608000b41c035041e10b0302505052040c2e110241e400513120300780c0340d0481c0300020071840c181c0200d007a0000d04c5d04008002e003000900041c40951907404a0f216203420b03426117400c41000495982684911f540e01d640c182e0050100306041d440d00c4c9805010684125000e48255090b125800f40d075801507440070003c0b5003198002c0051540500090452040448805403080003030b400320112040402d50281c10107583c0d000503420440190200e034109600104142d4840782c0e00c070402000307810112012406410401003031080342e820503001440b0780062490f0440c45585000c004c0300250050401230102d03100354a6402c8294503a88607180285000301002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 489693345 1250 489692095 489692113
    0x30102130609031a040528020a030302031909050f12010f090b0a050705120a1508060109020c1b030c0d0f12050408010c09082503060f050103030f14030c0d0e060702 72
    0x40c41121541122503403400f04c1004000010b00081410b04511140303d05040c41c01600c0110040c071140d03030100c0250042030b455804414140c0000141142003034a50000c0440c1003580021510006e20b132050070f81011000050107030910303224076511b83c0300704a040000791140c103001d481029900b50450540b0031002c000c0034411040320500174a544032145051992a14016000003160000002d140240c43d96449290703140c013083d0550090f00134402030044603141d50710f88080000a50200c54140864410b00400030311040d4000380140c807004004014003500354030781084c0051444107000440c0d0040143c1d02c1c1100003200000b032148100c0440e920903480e1400d002c40c80b404c41e03812503010313010301c0328100c0b0070001c03c02e0000720380d503011032075036221040200607503441e0300030b9050354100426140c102800349160203001e41c0118100c1e4001d0b911040c0e003100d444800d503040290035180e000031280410003e000030309008014620140f149600146887c0d0054181d41000001e60300c41d801604802d50f6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 489694595 1250 489693345 489693353
    0x90307150206010f0501080a050903070203010509060105190308121306181e0f030f0c0209130209071403010b072306060910080c0f030f0f060f070f020c0f03010213060903 75
    0x1100340035061003441c0c0e04c1e82d54100300c0007820400004119004154446000420b651002c5c42a07070070a56002c0c000340b0903400d04c0ae86031910350000340203117801213041c0f040b080555418035009808498009030010321b010090f503141c50184100903c00494804a0504100010b4040c801c0d0344004041c081906005040c5281001080c02000d40502d03040660b0104a400304074041078030540254142008055840407000945036070320b0a40e00650720500c040200300c0303c05c04440100100c54030031645004156903040b0147c030010032100030744044001c18801171040d4000c440080c0201c5000790044502c1c3c445107414081013450080d0244181e400070003d20825040c20200c0f030303030000a03002030322000300e080180080d503a05c20300c81003c0c422144c0388990070700340d1400c0c01300204140300a815961101d591500450392440c00340c8071f490b00800310340001005144181c1c24207171524215030141c81940040401c00508280308089903030b065608002c4420744c4c07007041d808103005003095102e40002c1071071420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 489695845 1250 489694595 489694603
    0x403061a0108010305100f11120115080f041b0b0a021f0b061c0209060408031905090d1101140c0703290f04050a0b0112110a0602030904110903071502 66
    0x503601d0601041e030006000051000c034900d200e0000251001905044075074640024200220048146a03000a001910320140341c8440703043c0c1c2d58403031080c40c0c00660540c003114440700803120300031042c8404c00850002622540200d088000b00980d02406a84800e0451803aa00103c40300d000341c0c0c00040b010001d90384a5113981d00030001623030104000400b010200362517108214114410300c004280103505404568159201c820001d04015202c0d52500c4042c1c0d50303079004020740c2d4001300d02c0c0d0982d200810300ca00200e0f02c0d580300250001c4280d8501d0380e6500c07140900c2c0380c802414050f10a0f44082610400406400904051402824003a107107041c40d2803144c03141d170100b042404800750b412810030880f644440d0007140440c0e01204a669900346141841c0040c1ca000385050a000c00004901b641491042107450042c440b1540aa4120742001502c0d000d511800700581c006103d400e00600e07203a0300031881c441100c40301f1032900034007000080c18850360340c0040300c010f580300b504202c119038108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 489697095 1250 489695845 489695891
    0x3020f0f1801090b0f0a0201090818130209030307020405040302031c060609080a0b2802070b15060306030703120306030f120f050f2b020a0909270204051b040306 71
    0x3c200a900103040c90945030a92148a1000520800000d8028800c9100b54414200307a0340101d41d06454003030941000c0c04040301c00d02c03164403aa42c0449205104c844510842d4104070300100110314060f001c0d801d100103010020b20039803d50009000c000344c108010300034483c40790145280000e0290038120003034911046508030803029440320417054000348484001c190022642c0386001c10028010981481c0858045003803030f036881c0086a401e003004000340085010300000418106051850f0040c4a078a000c02c0b2007c83d8550b12130308040012030000c1144100001c81c500c1c0228043e922a15104140c0900c000e040b0382c80110380d0213450006038400c2e9014901c0031240ba03c0341c0342540c181c038000707060f0040090003c0e064041040d189a002d60382e00c10b40c902c61a10384800d6456241101001d000710243d4840e13078a0362410030010498507403002d580e0704100300280a07840190501a000d010040c00010f243c0441102c0d2086150040e0305840060130082d441450082440032144840c12200e12042d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 489698345 1250 489697095 489697097
    0x1b1a07090803091c0c18060609050f0108040f02060d020705030d0b03030910050f041a070507051207060309111809150105090711120a02010c1b0c0e0703020f0f1801 72
    0x52281080c02c2e5208142044e14150003440d554001c0340d1410525031070740d1258003080a2180882e03590803404001c0d080a021103040e1346504844944d41c0c01440205c9044c5405140062641c0000130001814074a035010b995002512140c10400c1080f8000d00302e0340103070750617511907001161914a42d802c60140c2035001000b50086d50414010034003040002544403881010302c807010440409209040c400d9030000c0c00c2c00c20210600b1003c02c2201e004941c031411064a05000b102c0000c160b6081c01c00890803d208014010181245802421402801144003c0f10018414100c030801603a03580820094104040c0303030b1105608201070b0207890402107000c1e80d25020550001000036a0798042d049074010054280000105141c00c05a4200303980300360070320210b4001203889042164158884155141641c44202d02c0340c4411240c1240d50914a000420241a031a02401000c0350684807a030825540d040140c01c2400d1401d102003183c01c080e16545c50004040b810541a80003044506001c1c007007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 489699595 1250 489698345 489698347
    0x506040302060a050a0e040212040b0a0e0d0f180b031014090a0902040207170301080d02150402010c0503070501060b070215122403071805011e0302011b1a07090803 72
    0x80c541c041440ea004400e200c40c1440008644180c441b40140d204030111724000704119683c025004849003140002c1e9000e8a5580480d400a41c0c05104c40c468107956100e40001044020741d008400c84181c0c8007403424504001003e800855050a0111900d02a00b030400ca02912882c14855003214610280d0200d039807d4494559a1000d480f03a41d0303080e8214030b005101080b40c2c000c0c0d0003c900a4801d110703005050018050f1f2035007609050f0006113058840a034107403580814042000c80e81c6104540b0710301c09400043c1c010900540c06001d150b61a107215209480c1450001d0b101d49003100e181d40d00190705400c1c000b0f040011031800504da400700c0e42030012000d040c81e051240710760a07000c000f0144800c41782609a8510181008010421002001030498000b80e840768501010101003000c0300030128204400403505d030004804040081a03d0700141030120b20719001103924500b070750b0a851410082040034404544540c19440d8044060100c21a4074249848000c001c202c06901c800c2090304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 489700845 1250 489699595 489699599
    0x1903030f03020f1c05010e060d0203151003080d050402030d03021c0b130f24120f060f020c0a141605060906040915080d0504030c0b0a14180901050604 66
    0x24100d40315002080c01440c00584611107000d258105100704018000e2140c40c940c1e050040d81d481d500040d05031008030403403a4950300d5581c103214042402610095250b0081d841e0f941c01211409a203da102c8200122052040d0342c0b030b280d1900607400b5440c072449940e1580c0401055090402890003180b16030710781140b602c000800303421311004030080d5030304141e5143c1541e000e0a0b0b40b2140318404100e55141c040281c2c104034102d4000506442413a00d1500d0b520b0f98420740442000e100d00300480ba0960950881d18141d5504e20541d2803a00c1c50850f1b01554400c0c0d0030003c51024400b410030040e21000411846056041c040c0c000a400100000c9682c00007481001c110807040c1c920040b160191903080d110308048000031046c0c01a600a51415403401508050301c001c0718030180126000d8400391400800c010720200c9452145000c050113100d5920010072940582000030007580c2d40034075000d070a140000b2628001a803001c5c0d48c013540d115103415000000c0c9400b240890041000320780e410325042c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 489702095 1250 489700845 489700847
    0x31e030504050909160f060314040503070308040303061a0a17061c060209130504020a0e060105030c090d171b0a051908120108031c0b0307030b060a05040614190303 72
    0x1c455402403e00816000b804190109001c100581d00d880030002940941510707001d110201c1001d601c070303132000a0f0610600c00c841a10200103180903542241c0a585410080c2d102030b00d00820140040341050359480300040c10328880c2c13420841c0740d421480f050390756941d84103008050403161058130303800c04050002d20405684000700a4040503c10488140004071410041c00034001c1d1a0303a50781042d482c1d01e150307400300c000394400d03885144200c0c2e901c2c2c0d42c0c40d120211141c0080d0200c3e08203020400401c08500c4580fa58005892000b80c02060112000c1c540e603503041039070502110785564001e000c108405120185441240c09207486001401c501880e0307103429580720012107810350103401c500e40c00d200f40141607003110000c403d00b90000309256501c101240c2d580d0310012042c20312080160040d043c500250040115051004000384081820358664200e080f901410b1150320410080000a0b680c9950051500030455400924041c8a8510a1006074103208035450114203c0f21000c1c000a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 489703345 1250 489702095 489702097
    0xa11220501050103142e08060f07171513020912010c11010b0901030204150515040305070609030308161110020912030906040308030a270c0501030608030d0f02070f0c031e0305 77
    0x3010203207141c02504000304248400c2c000c2d03180c10109140c0034810801c0502c6484030300c0c2ca030080c4154bd4440426606680c0300c40303000202034030210a414121100c081c09450004a400f120b4074482000520b8403881000182c240c0002c4070008000e0394440614400490304690000d44e1100e85c80000c0c444001540c2c0021a12401400000e2103647d030390000d03080f00702d2019040400b404000e000200303207001500140200307411501c0216644c0c030890401044851040c3c6106003200d03810b03110300a048e12003009800c0c000381100c4448080000f0212001c0300c0c0f02040108210384620b112005a440021200f0f104c05842c03011590380c090350080000c0102034a95070211002c480d0007244864403500d5410060025010216103226400c00300e0b01c140b04c00407500110b0745a02845028040000d55440005600392103130b038070506109800c14446904207162580bc00d03020b9a15a440040c81c007070301075a400149100000060f507050340200410701c10000c0d140319060310307a06e0041540304021340c291340003849 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 489704595 1250 489703345 489703381
    0x3200309090907090e061b180609041b0e0a15050a1211030403110d140f0703021e070f0e04110d03020a0c03200109080a1122050105010314 61
    0xc0c2074031030001a08010280403034406490861418030949560046980e0740d00e0040d1848a42507440401c60000002603400301c0364402c26400d01d031a111880350080003a5034200d500e0b240d403c161071701c1c06400c5d003000e1070f04607000e40d461684807183c071070315044113000b10030149400005400d80f0b29460030503040c0c3c002007aa81c3c03014840ca031041030240d07890305180240a82c54141124080c011062104168105807009e42c2d040c101400c03206081c0340301c3c108035000b8819100558020f542041302419a101c11001031140038000c0c0100e40042c48500300c41c00c82d04500701203030078007500a50414007031000c20302c000e000104505000c0380d0b058181501c45004400c45200c807148200107440c004010540288100c54005400685501d20251b59081c0321003001307220344006507103440b507214420556006801c218252000c0400901c5501001d43d01c00c42c0120f50000c80f00d0307101c1c520b481e040b40d00051410b01c203211040164004030f0194074003400501074403144611410700000140411110078900040400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 489705845 1250 489704595 489704599
    0x3030103060207051203040b06040c0201090b01050108150303132412020306150c160605281b0c08120301030f150b060d060302030613030504060c031b0f03200309 71
    0x82e072002c0303500c0c203240342c086946100c0c01c20300030100807c020301810013403440c403807642903405020100303860f4012400c0300d03507442006001049480051065521074a80c540e0b104401e0100311003505142000a840d5412617103141150800407941804903a280b04211509940c1242c810ac0c591890500003401843d4034151b03c01400703078040b0015915650380e00740481c1884650681568070709a1492140d00d0700010038100d0b480d542c150200081c0144160110352100106003138000c920382c1e503402d41c01c5084500ca84000c0c2000800c210308174004030180361001d080d902c200c43c030890320380c84e001d410350401c1c0d0440c41884081c00103000400105206030040340400746e0101c0c0c189114110000f00400403c01c2d0390880d40c10840104d19062291060750009003907034021411288960f0381d20079000c4150302c0101c0010000395060104000700d60254000c0700800d44a801c2211140c4e00194002e514084020003d43e0002c00b00b909120515030041c800c0d90790140c0002403a280016010303001c40d92071183d010038078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 489707095 1250 489705845 489705847
    0x60307140a0e1302041508030f0318030310090b030a080f13030b09010f060e04030f0c050f010c050a0806030106210f140304060f0203070b04030f020a060f0c090605030108030301030602 81
    0x5481e584180304500505407881c0d040c2080c0c24103800603460681d205204900541c90038008200c25280d020315a0104c0d1680002075141081c0080309941d150009003990b10301030820564440800320a01c080e500c10300311102204074451500d00d07a0310907600700f803d030307076001e034008401c0e241c0415030340780032a82101641024143d4403141d008146402003055031010300f004448005120465606402c0041198100142846200d40b6401c1c580305400c81510010041503807511803888107405900d04902590180040c0ca98a8a50102c3d103425a100d00403280000390001074000d0210741c1012010307401800c250000c0100c1030070101604410245514621400c80002c0d49102c104a0045602aa2690302001010040c2c850440ca02d80d03d4000307000c0c03034010404800081c40c1041c03001054480300c0e03400c961080210b46031600c0550710108110300020440c002d594880d404501070b0700542003c0c10f900c81000482c40c00c0c80500034007440d05034220108009082004001540c1e002081d00e0541c0c2e0040001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 489708345 1250 489707095 489707129
    0x1f06050a0c1a10080d030b0d0605060303040905090c09012c0a1104030605010f170c041d011401030c09110d0b0303160303050709092a030b041a04060905060307 70
    0x80e041540502041d02e10358103480411070000620b00340d51089441c01401c560b03920301003d4003681501d848909007034010754140c07500e1020907020b0300708a0b04524080c0c241d03454552900c031b0103001e8840850344041240d002c1200c50400b401c0c540010360060281d22103004140300308840c0c082c1005490b9100c91080e14034807001c1044ca802545c064011003c2e0002c001d0742e160795a281c040e01420b024410740f120581410400120182c2404290030b02d015041c0103015000101800c12000300a6440320b01d08141c154525420306c1e0340e007403061503001100031540c0a415891880d14450314001034004581c41418421a01e1202c020b43d402d44484107401c02d0042040301680c004203103140200224a100d00c0301990400050607010f03030105000308003a50310350348801e856200070b109468040d551640300307060305012980400000b141008011500d071034007203080203080300014156211802c18598481e2401801c10461800d8811000100041176050182d80b8003080001d4846403e8480d0700039101c901525 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 489709595 1250 489708345 489708353
    0x103020d02010c030e061308061015030507030b06030f04050606040e0d0c0206070b0403081602071503050601090b0301060905120a0f0212030c011404031d1e060409090303051f06050a0c 81
    0x807000c43c0317080141035991914695044070707804654034400c00d07045020700008034103003e43c9242500240c1ea40e806882655908aa004400500700100581d081507516803038440e0f1035444c0c00c02075002d030320318005c0d818690502d400d080341402c00c003400c1c66210302d10313080c25621500300118142c1d450f40f0301410700b04404c04003070010803010702c02c401005200a280c0c40401040541215000340580146810141c45252900341030b070769400c0d140219040f06604d10301e03040106100b6004981c0c0031781e040c5041d080040ea110009002500f0a81001c0c010440204041c043d41c10079074182c4c0c08a803005c40050015903003544480314020500704010703008a10b5601c00034104d100c20402c840e141da494800800c4007503d20311540040e61006c2d41c1c2200000d01005601d185210f203d00340d00d135001360040c040071260b8185080080340440c41864a41c001c00140400103288805100744061b03d03000303840104d410f103031100c400c2c400441d0070300243d0446084d162041c44055804400d46000c12203e00382018000101d00b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 489710845 1250 489709595 489709607
    0x50a030509070f0b0d1d010e070b0a021b0f040f0209030d0e0603010501052802060f0108013b070305100b0d03022d1606030608030906091011030d050105031002030103020d02010c03 79
    0x441008451206c4405643c0d804150b1045003249481025180141e44851001f103240c072481e41c105c401a4890064214800c0003998800c286c1417000703121600d007603070300804941511503420403002520303070200d0540e00030700701403000010489903458020325405919000411601060082c98100403000c02c0080b130352078070038081c0d05034880644c2404800348000307540295194012550300c00340202802c0000f40390310050154803004a01c8400020f400d80c401c003001c8060416505c0303210071850820a0101d10200c0a0000c040954040c101500c00007522400305806e40f000140910b001d02503298420001c02e03404110780341c0340360054900007054081c030b40c6605100300d2080035580d00c50051103010300300c1124582e28041101c0d02500d06101c201d6440210325183c0c0286e41c02250400c4041240b90300a20308808034407203032906401c0c414403180c00040420715540040341610011951540180040e01c0c0070404891000101c000561a540c11a8041101c0e400150f000a050107906800d120405001c1c032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 489712095 1250 489710845 489710861
    0x4031a0a0626010c1d0f0f0d0309080d0c0b15130c0815031c05030603101d0c1c0807060b1e091608010302060f19050a030509070f0b0d 59
    0x440318502c81c4080320b4101080c00b51618807034240b98a01619640f0b201d0040d1800c2e917000c41e10303040002c26074918205000051040400b8241e000e01c031711f00080c12540c1e842d00c1c002441c901039680d0040c40303801c0c608c0c0300d40703041d0070491030b5000d1200040034100041c401030a169840041d2410400000e4000750204d2030448003424003200d01c2c0d00f008081d1007516841014075200b03e8119000c0300752480b417881410b4444801000c810010000010300b405410301450045410000280c220344842a420500e80219120721104c080241c100310102d81c420002001000d10610003107480c00c00d0080c0340400c00740783c0d00403000000c0a00d8808200d6809200c460740c044408110080e12001005101c2c61096011442030802d45226529030740100e145107001084041c2410a00c1e10340b420355900b59001c12003030b608460070890030300004104400d00100d003414200c01a822a4456a40354980f007100503083e500010710640d001d51040c0000c0006440c848079500403640243c048a98640180e103072440502114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 489713345 1250 489712095 489712109
    0x7082b0e13020703080a1a0d03020a080304260a120c02030c0d02061803070506040206030910090c0603111602011206050307290c102a08190204031a0a06 67
    0xd000c42040380d0040d40c00030000c3d80e2003540c5442003a81d0b40342c0c40004885107441c00c581c200303100024407050f904080b00c0d0811000d02a00440f001e90445a840000d554012141114400f40d1407400b08441c4505524000d603114502032400d041085c0031000402c0c80d01013681380c0d042c1035118203060040d140248119245084c0d007000799019025042d501075030361001590071095400e81c1d46c0c4c140c4100701c0c010068501c2a98000003504064481d602080307040e070800b4210f21500e0085100d0401508003078400ca10500c0d104a0001c80100e2070f04201804a03054800483e0240c8000c100c1b94500c0034140810503021075090a042110f1001d040302500107040d15040203130188221310340440e040071407003104032400c000801c0a44455038141d0500c02e050203040c8170a040c0b603108080e070001041558002440399031030360315400859103034100351011511100c0c0b0540089190b14051041e800045c010510034a08045004d5242c10320b1a56403034004011044031400c80c5041c980862540300d51034000ca4000e10750 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 489714595 1250 489713345 489713359
    0x12100305010f05100914040213140103060902030d080103020d0f150204061101061a03010e0c07080a08070e03210f090d1b12080d0b0103110f070507082b0e 68
    0x440c01c2c4540003080c0964681c04214488000081c4200c1c6a01a080e82030204464180581c0c840d41d090001d270491003c201a481d03501d07519081140c19000500074001d500072113002c03031030801500600d4244400840c00400300004480188056100e888940710050790110503800c0d00682c0341060185004505000101e0900024000800a41c803242d10f0303802640c000c000300b101554850b00004070018107007a10142e12000d000400010001000301f940c800c40030f4280600d000c16564a215850703100400c200c3c00304607032505002046503c105c08075165001a80200000d008040a084640802c40305000c0054000180100780c400c806058076003001002d01540c01d5911546005c00c02404105000451098101c4000420180940756240700c660004600c03842e00c02c0305000c0328090840010814181600e494080d401000040000c0240c42d40c003008540c0c44440c245440c42c104000c0d50320801c05076001d001460b0720a807104520300151401022813601d80108100107842481140c107042d980000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 489715845 1250 489714595 489714611
    0x7030c02060c07050127050d11040c03021c060308030a020c0309120717060c030a0e011806020c100209100e120304030308010e0109150504110702130204150c081210030501 75
    0x1500083c4030b01030310002d03250440a0405000360344020f040b5400311400344950362008000d1414903000c40e01002c1d01620507402884808000324040c0e42c0d046400c80006136002408904d031308030074010600c0c44c034024102840301c285941c440f4920350001030440c810140e0700145260081c1001c0048844851000c0c200f41c4002044543d00e5464005503c904503070002904078040000f400898403d1048440030502030960320b821003804010b0141e402030807915941d07a0524090020041c03046c048241c4034150141c2d03220440ca907080e0402c1a0903688901e018010700c4005416560f072036401c04204060b00d41800070001c1d4400059a1000c103039003060040c040020040b06041d48805000c0c161a0510882030b41e0b80d0b601d4441804441501e4240008005c01500903c030b81e14054020000d4000d000300800e0808050790000b03503800c020211b0588106070f000038208080b042004020003642c0341410810400d00c0727151902081d0344544440b09502c0300780200080c111080b102c030010b014507007140080040350 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 489717095 1250 489715845 489715867
    0x51207061d131b0206101550030105040e010212071107050109180f0209121b0405060114090d06020d0b0301060f050604030305090a120f1208150607030c0206 69
    0x8111a03800c450085990140101c6500000d585801a070315815006c0401e46480540d608200004071104200140180440c4d100140072070256105442010141d000e43d4030706400c001800c0d8009001004403039540c0480c5a521203607002d0324110307101541c3c0491800300c0d600080d8024850200b201001320300200501c010b280c1d03c41e044a00310080503003124401500e40c001900c0c404014451400b00d81c00680045807841e4464020b03a0340690210405801c0900810000e0000c629040c24403401d0b50051b5400e00c8200081001e08450480a460030030140c142480001d0104540505040301240001064569070700c07000700c1550300302e8100d1811903e8550302101003011700301c117940c000d11941c200304000c540181600c090404a8400501e901d15082c80c40e0fa055031990801c8818541c0010b03c540002000c41604441440340f5115001c0402d04407503502c0c28051854003152403500700400c0008100c4034220b02040c00c2c070240011120f1548500840c541211084042c2c4002500b1060100c2c00030b00711 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 489718345 1250 489717095 489717101
    0x312040302150a0207020a05010e03012a02012406201906050601020c011b0c0f17160b0a0309111806040c020a0b04140304091103060a051207061d13 65
    0x351400c40c0904001e449400103c0706038060040080d40c05003000390200070660064503009803000c0064008109101e481080e020b2a03034545109082e010765407088064481e50a11801003d42e840d54500242018044006010002a4003886050007818402c1d624901c2100300328115542d103480031030b000300d2018600e0040102a26204883c003d0811010600540c004507a4000211040e5107000d44122008a440074200c5986401d950390b80c020307a004680c070f1440e804110b01500f4a08000c450380c41e03141c44241e10b400050244a000034080440038051800d004d411030300c61810a2901043e03002c06410180d01408020f0401a07202440c0c107003d40080e001141410300c244811102002055462002070b81c4595000c031009009010b01c1d80082d0004002c4a01c0d5a41c1d485080300300c0f0b00301030f2544420390849003101d40080c241500401000321701c1c0380c1103204001909040e41c1c80e4003600001e902c000d90320f403a6801400e0074411b004248440c0d040801d1281070300100c0080c807810802070119042001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 489719595 1250 489718345 489718363
    0x9060c1912050703080a1107081204140d21022206030b04020a121d06190c0c0308070311090a0e04060605011718010906061d2401030e0312040302 64
    0x514601d50310144599000d80c040c3c0b082a41c254031020040d6445001c0d0320000c000c82ca5000d00d60400a001c41c2c00171541200c083d003a03a00303280c00303103249600b484c0c1840c024600d00c2e00e00c40360b13080c0d200d82003200c02c1962148103032146e8404c40150301c000e0301c0d02c0030b443d02c040c3c000c00100091120b00d8084280a40c0000d6200e54102c80d110f0300e0400002c441e072001d00041c2e1150000d820081b82140030120800040b40d405804200c0c02a603190340c80300342d20f0000c00e061090658101c20540000105507103a0899442002030440d520300b0441100c40c501d54000c0d005090062070501450f03526401502405c5044088030501070008010b104410b490300d010856150302030310309680a80c5400400306e01940600e5814802c407010344e000e000944e464440c500e03982c2c0c2c1940c40380b81c810354840032140000380141c0124006070040012040c2032510340013018221410007001d021442c1440840d5084170036485c6002d0071354140070700c0c0100300c40304000c0c00c05140d4442c40c00b18902654010b0100814141d000c548040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 489720845 1250 489719595 489719603
    0x5032d072c22080f0706051f0602060708060f041e020a0215060303091c0f110102011407080718171606030b0f0409020f04060e060f01050301140609060c19 68
    0x21042e1146038241e104040c1e407664031564a036118403910042407484001c0d00c5413072011034040e803912120b6582e500c01d035081900c0c005400841d00c51264613180c04000920090315452000300307461302d4200070003005098080c00e0207000f501116200e40103a00c03142c120800041c44815114810b140c107003221030080d800f400285006001b0a501210408040c05481d8010080240214240325845040005210300650140c0c4241284102240080d901da000040c6081c050078001c000f45400400190075154420b00211040d1044000c00c031941d50000407a5810074003901d0807101c03404148500c040c91940981000820701c002008691303000d00e0015400d04c80e041c04060311111035960350710039015a034000d161268425401049181c03a402e03d40c0c0074842d02030005000b41030401d072180105080360ac80384c03c0129503a1140301045001e05290101811461081c03070028610340c54840c000340030185000c100d83c4211000100802c4683c3c80d2000d48920000030302c141c840400f030814a02000d6190600216 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 489722095 1250 489720845 489720929
    0x92b120f020601030507090e150103030e040f090f1518060c0306061404030308280905061e0406020702060f160203190302030307080c04120b040b0105032d07 69
    0x35508510105001d0304a039840002403174003e08014582001d422090781d4412584030305100c01d00e44078024107010380214000e88403040684901000d1009070b4120101c41c021080c20114031100007050109006c000c242c000f526111198541f072102c0003e480e6150381446486021020582030200c81c2d4400b590100694404010117a550036003524070400d0174400401840b401e01040011900681c00c10358000c58040c4005072140640c90306441d0300300c00c02c003000d401943d40e1801404200c401c20846410044540e1aa042ca40303541803481000e06005100500c41500420003c046450322800c0c4c482c8c504c0f0820201b520360480428400780c281910350281c0c881c1c031440703c54519080700c83c50741001140d090b9019501d5540c50761001d88003600042d041000300ca2003080009200d06e10303000780d0115a0b225a045002070308090400107030340241070b04040d11030307003203041c001858454525a500380c51000300211800a1144a5206e05001855002d01c1c4100640d048030800170f20380d01c11600c1181c400e10070302 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 489723345 1250 489722095 489722117
    0x30303020d0e0f031b011506110d3b041b1e05090127080c04050115090e070e090f0402010206100f120213020406020715020109030203092b12 62
    0x1141d8444080b0080b110f41c2d003040020241c2c14101c3c0c5007682412490100100b4524494000c0d20b00e05007861f030103440029212299062114810b02c55900040c203e0314244040b0184110314000e0b16a010a0301c401591003540c0070b0300d040849101503220100000c0c810846400540000030307440f50004c03c1c03403002950140e0055200041200c1c1c14411140903503a25041210314801910102807030b8501044411264210b02071281c805180200038240800103485a2032000c0240010f484068201c0c2c07808907014215041c00c0c0354480103941c07c8600301c8000c0ca005446501003501c0070302c0a03004041d0015400c0d0204055984403c012600840c407c1c0d0864000c0d036a00ea002d912004118001d4a48405054804101444810802000c144d0008044980f4600d026910303c0883e44103902680c0560040002041a075030040348030b0b82105c4850000307200e610038a84e0000d49912680009510499a00c41940c070b01d1201e81c100c080c0b0248465540710222592402c02d0507455030300d00001d400049000c41e81c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 489724595 1250 489723345 489723371
    0x40e01060503040818030f160512030301150e0d170406090e040c15030e061807050a03050c04020304031124010504020c19050f07031202241501020c0a030303020d 71
    0x2c40b80b05a0b00202030340c0c02c1c510ba80040f1002400c0d0420032903407600c9425442500303801c0900402403a951a07040074075105190505111103a000303009022401e07041400104a06000e5524802103030350f01e03143c51540b616401000801c55541b240b8094952420f128204401c200f0310300080c010b448168031406102507540c0e01d114041841160020700c5044c29542c108401131001c03100c0390764001641400301b1340e0404680b88510b01202201c0020b0003c3d00d2440a42e070441080c040c1c0e02c05070100351a50481c2e1403c6031201640c42d4081e40107103000d01d600100150626110750340c407400525044c0140c0e9a0b100c90b040c460890904002134120245d81c0302800040d5030f01d41842101c0f41e01c01098042c00c141361904107144614070746004d0075030301809921240c2c50112414860800076501c40d24540d05100b40800c0002e1410100440514090060301044101c0ca4000d10003103520500c00285080b0007045980102d042101d900074003a04085c40700804002c064064001d0080c040030705004010300182410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 489725845 1250 489724595 489724597
    0x50612030901032d1a01020613030f0e0411030a050601030e0d031503170307030f050f011203020a081c0f020405010e1318030c02180c0a0302071104050c040e010605 72
    0x44011003039104101c51510355009402c240420050040340c00d98210490121002000c041c0300c50300d081d10b80e5000b620040303000c42c1075010340d0f0b110207100422061900f04d21920340300d034400201600340095420900c00061051040250626014100b4810940b4415141c0556001a1444901182000c1c0017850652103442412840001c03080246541d48000c901980100060304000c944450054400700101c1d94285d8030203448a500700405035646071801d8000c003154030508101c2c02c81400d01701400701c92900c291b041c070305480d00f0b041c0885541c0c1951030107a1414143e45401030807041e0210b5003007a80400000c01081c400015201030002154a01d100001c900c03940c040e16002c6071003906441694108851031000c8403101100008000481400d0a4100d400d1100c04800165000e41c4910440c248602c0915100702070150314003060a00b0480e1101e54002c0740004805c050303011401e01d0611168092015200740043d00401003420700e100708440716406401400010450f810000580c144164 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 489727095 1250 489725845 489725869
    0xc053a0305190e030a030804020a0603060803040e07020118060506031212010608071b05102403020909071a090a06080702190f052a0a060c0b04051c080106030506 71
    0x20381c0381d078078118074180300c0701015035058150401c1020484000340152020007486458600a4859640340e183c00d01c1002090700044d0454800c00d42480410054410300005a905036004081c10304441da407407600803401800b103500c0c9040a42040203025081c17207110b0380005d003e805c040d01030310810341c483c40040b03007207110b1000c4c2e58242d010030400420049215428a64100120b803400c4c046080240841804c58000010140c41e5034001c0c00001310543c4d002e110304c1144440c0c00e10489071982070b02500840c42000c3d0b1202a0207103001c6d400180190038103001030f6000d4980c100410300c4511070110b00030f585800003107589008120720341001c180507015006c100c1c40390312203a001b402480400c00c100d9003056030311501102c0300030303036508000002102400203401c4404480b848500742400860603220180802250b14011052503a080c09803c0e4446280c10301580c11440f018030980f602e103445850641c0c0100c00d02ea56000143e50402404e50010f8202d048888540d024419900c80d01c00300540c0d00254 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 489728345 1250 489727095 489727097
    0x1009020a09210218061c0b040222092306090703110409080c0d020114060a05010c05120703120b03070506120403200f070b0405060f070c053a03 63
    0xd808200525641c901c0c100300400350100300845105000e03808524103814001c111021a03007104100b01030707170400314a01c4881111041c11007032101b086481d0340ba005100944041e0182401400020508110140340102d00e6030514041080003001c3c10142040e0f4120525550104480c4210400740007001a041d4014054000600005491642d0384120380000e4900c09030810380702c9059070301081c10180904499180c40000e810303028040f910080c212001c8400105811021006001c030301d8880c48a2401070720028200072050240504180f403504210b196141200040020400c003007590108034a00000980c15051000701c0b103010400d030f11142c0780c0c01555045001807007692104042c0c0305400360840d01904000300c011140000c1030980a604202900c034650081005405040e020000b4034001e1000e03034011030525080c100000c00354480c0303040301c040c680300118403e8103000e5030340b90b84002004020002c0105410a2903028400400d2088482d03c1c44e900040c030480400d0b980c01c23051602541 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 489729595 1250 489728345 489728357
    0x608120922110313050f01110a11010f02030709060809071211040207171309020c030f0a110a210804031e0c0203121e0a0c12031e051009020a 62
    0x141040d40c08616026607201454540300c404a480d010129001140550035448206034079058a0a005190550301e182284040c0c1c54151404444071f2064161820300c0c28070b1a00c6400c1030000303250382e40900140111144001d10020a010065800c101d07184111840c0d603c4690b01c80e650310326010f450b0302841c480c1c60550320a41c00c182d000100c1c4407007a4100000300900050500350315440c0c803a412440d0b0012040c0d00d40d8006681e803440280811031000800340170005618020014029585a0180d0a156907901c18040350b680d46032800342c00340e541554034500848120788102e0074144120840032403101c46c83d111480d1000c410300e200d941400c0c4510381685030301d99013611244440f80150b030340b50380d20820051249003850040e50240003182100c64898161a2a030120200c0740801c2c803135150081650882c200150b510f0550403c000c0c00c1c3c1c1c00e030000300c01e14a0420350038056010b000c2c0942c501728004c0300f0464400040400c0d0380103e0188a60040b00c501082d1120b000341c00320300c43c1039506000326007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 489730845 1250 489729595 489729619
    0x6150203030708040204062111030318120307052a010507030e01112103160c02010c060f0b130e010f06060e0f0f180412020601121202071806081209 65
    0x100074100d854001d031014000040b800d503101c0b54030800c2d08d00700c01311000398004403004005000d04c041c100622000d00300d000d941350030384424100a044941044042c01420141c51101c180d0400b1310983c0e00c002d402c4030940300404c2d132855207058455030006485c2c90741d200c61500d0041c154458400d54908984c50340701d200c044c210740401918070051001800109108084c000181d00d901d11070250300b070203605034245890381800504003a202d180314058508115002c8403030005030781d02c807400d00e00d030701d4000d500012100b040040600103070070080710850300028103540d40b41c2c2040440d030102c1d00c480c81150081103048100f04804040d140e041c403680f070000f05105100c40c0c4901d400c0000541c1440010b00c280c1d00ca0300e40401082400a100742e14414034a0300200b00800d2040e0040b8034075002501c1d2014002542c10070403a0507040c0304100d405401c1c0100c03080e10b00f1405000308245400351842103441d6100101800d40340c005400c0f1030041100602036a00764040001c41541680c149080080003140d0640d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 489732095 1250 489730845 489730847
    0x91609061a030406060f1203170702030405060c0f12030703051e061504050d0b10091b0309050a0506090d030630150e0a03090b12070e010c080409020d061502030307 72
    0x10b0030207401a528160340381c03800946144e203002c20034001c001a181548014203503040151081940702c060b0203045240c071040006141c0d001c0211000e407001110180d03101e0804c0015149801940f84010807030380324040f4504041c20140c1e000e50310910041e078084c08180c1c0e80407189040c010845104840400c40390020980b2032819500784080c075144283c66a0806641e4000229059202c1c4029100300000c40c0611001c0b0500c040740b00041e01d6007210030300503070b22a05400c200760a1101c44860800d590360b42141c0070410203100d00140ca50b0030008a84e030a040015150341c42d0501800e602c0d000c00d19162002550301c8009281e89000d8401c1050800c3c0005255551440803804c4101240e00c0c00003480c0c42e40d00d20009201d007000c0b241001005100211861030040c00241040c1c01107006080c3c00d10404000015403040d59900821a18050314260f0548005071518800038000800750b220100300800c0300101a4040e04051603c95002d02060f0340d8ae10074003010b002c030700542c9001a0010800a613020b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 489733345 1250 489732095 489732097
    0xe180f1b0d060f02070201020c030d0203030609250e03010501060905031f020c0610030b0a060b19050903010e10050708060a0b0f04050a06050903151003020d050a0b091609061a 77
    0xc4600504904206541e0707584090442d20442c260303a4000f94046144410355a0412159802240580042000b040700c010301950328040189401d120b80e00d84000110680045e000206038001542308600103e140000b028000304850b8426074081d40c030b00000001e2052080e60b108040b140082d01500d2031003980005410118110010b840d001c070340801c107962a2010070825184200d442e00c0482c0b00d41415481c201d440020060700709880d242c1020f0013402401241c0b012a001d4680c2007090b0620b60440718019205070051859240c0d0551a00e416000c1346a0b0100702d032500c2d840c40481c100b03c1551220000d603894502503844903040b188010701885803120840013032003c40f0200140c3e608280e512000203401c0f0308190004c00000301e0118150403103040410035920f5441d00d0032005284c03803070b0a20300ca4182c10414031002c0d1140569000c1e0703405104060140c801c01c0d0382c200c030000313080e0f26000c0382155581c0b43c202d1501030f0f0a80c9090000401089920448042d01d000d040746400070b0710030381c4440c585 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 489734595 1250 489733345 489733393
    0x6040b07050a0203070305030a08010b0f03070c021f03060314011107020909010e060703090308060405220201050f0414180402101416051605030c0607030c0f06060e180f 74
    0x541c4114040c0e24050398040122030006c501c00c0380110f81d202d0b81180010000d05040c1d00c1842e500f02c1c00e0010344240d4100d0300076250700c01500d162810510a160002904000805070714452000141007042c1825606070800015680203840b180700100e03401840500321a101085103419030001c1c0030301c40c0145020085603802091205c00822503035241c100542c20030340199080d40100740e41300e40c00e404068001c2003055010008490400c020718286024507005007481c040880c942e4007440400045a0161081d00e02e1144115110398407a0f40303a07502032103101c01000c015803203140070050b4400d40c5400303040c480d482641d01811080700005640c10a880d1011548841000d0007401cac8203041e202410004401c03001405a002044480c510002c0300288500940141d4029000403d17415229145d1800300c0e04007580c1450702c061a490541001304d00e40c2840c1d500280040e007031000004645000b05082800790800b905502021422805c0319a507441500310709100c03c0c0c220610800300d0010610500304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 489735845 1250 489734595 489734603
    0x20d050c03250501060902210f0105040203071704060617030f0d0c09030b100e01080c01050304260f04230d030f0e0a0905040b0109060819021302030a02031b0906040b07 74
    0x1410002070b0343e410b0940300160002080260b0110b40d060724031051034410520880f03121130403541030502103490000b284050146038022030700040440c0c0c035240304204111140400080c01c0c6400d0030a07251141c081c00c07143c401c541d03000007a05175002085102204035454013600d15281d91421a031601c00340060400000150300340900140c0010102d81030f400018810141c0c8010054810b040512000c410035040e04410380e1a80080c12880560b40c014003100c2e0480c0e00009418000f0714042c0032686003410100e50703803174009408600000506120000740c400d54001d8920103815051480302c2ca085807043c062082d50003903071482c0010200c0d0145a80c05040d0040c3c3c5020820306c5003e8004c030302e00c03800c0c5034000155140c0c1c4000300000c2c03021080c080b9000d0000c6000c148182440c152400d81e070b030100307202540b40a0345021030b25021543d0300c50010362948007060701075469141090480e4000d403c102c032056114003094100804103a10310701220f074412001021a400e041c20164451040d8101040c221 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 489737095 1250 489735845 489735907
    0x4030f020c1008062409060c2d0c030a080403033603110d020a030201081f150f140409090213050c03011a0304030f08061f050901020d050c03 62
    0x101c0d94640740b1074a0b031800466100d10806003072480a101c003800f0210b00000c2d03115501070030b400300c0d080fa0302c04680c02c01c4000c0705e0081d100d8028105044c100201c9040c140a60109000268103200d0380c0080040f400714003401751840c04003030406240c1c03104800d1a00400c2c0001c1004144002800b4541007410480d01483d604440d00d0203418030348400352034081c41040b118500e0010003c0120301258498000780c1500c04020a0485a02149291900e0302009050110890008a00d801b00b40705041c070131480d40807003070500c5a48040c40d03038a081610711610300003841084107000f09406002c0000c00710200c1400c0c50b1825290403003920003485c065104981c0000b80031221102c1160500641e0300407008010101d0352545454150300e8500d0f500d00b42500c0f401802d0040001203904a5a204032003901420252160b40d42c4400180054881c40c4142100e42031003286528070650207400707040d20a00c2a021212100c0603224240c03081d0140350390000039580108166409220802002211081d0382a007003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 489738345 1250 489737095 489737113
    0x31030c080c0f01061a07020904080319020d09140d021e0c06041e12050d0507031110050411012c010201060e0c070b01050d030e040b031e030c1c0804030f02 68
    0x107142031810781500144540e450f40030902c85484804210101c90002d007a05520307011165001c600107210007000507008400200000e03200140e41c105910444110860441d80c5d0150009004010040d070f54041c2c0c1c803090b00d44024460214000b8101b0300308070083c3c0040c00c00c0c0c0e00000c000311400006100d044814010403400e101ca64883d18041c1c005489a011090141d40500e9141d00400c20941e0240c500c000c100506800412008070303014050602c20b140080da10002ca040035580098050310451092003045d03082e01140e4581c0d406240103c0c403600305d0342840500d0000454849080c06903d0580c0d030120307280c603024051040b07048039401a060001084256440f4080c000041003169003105d96600001c124082183c40340b0010f000d04421500d8242501558070000c25000c007030014103000c1d070354a41c06015156010080d20080300e4500031038580841e003228401d071b201c0d00414040e03002407250506440c6018403440e8a102c804140d82c1e5400340661303554070b0442d150a031404a070801d5026482c08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 489739595 1250 489738345 489738367
    0x50616020705152805220506040323060603370311070501051804180602040605070302151308131d01180e0705040e011401080631030c08 60
    0xa084249503c0701c10b980c45410b01d02c89003e000c60124141100000300806808815800c0000d9034500203086a200e00c41d4600c1c1c40b040a11000d40c1d42200d540b001001c14004100041510400507100040c00c9203580d03c4040707840240d9840043d141568140c00828009086441e951020b810318559110300340e03800308180440c038114030f07015401540014400800090403607000c214000007803a080ca003441c030709410030b1401040d900741c225920384103a44038a00c54560302010303d60000c01d40c1c1c20010071543d0316a108000307400c03a4400b00b81200503001d519951404041e0b0601d00c00d01c0780d5128540740e040122542da074401c640d4801d00d01003421240f030f2400841c0b010245d06001081c0400304d807802080e03506060410b212961100c0d0b0324816941403148120325008042a480c04031401174074082100100e0300c00e0640900a07011022031006d580d2000022500ca0004000340200503c1c2c80c8501d0070081d44600005407650780042c4a00380c4000c3c1d00c0940001d21034082c140d541d42c0107a0480f4140740041030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 489740845 1250 489739595 489739609
    0x2130f1b020a0201230d05060105070203070f3b0717090105180609101509050f0a06050a060203030f1909030207030311011a12030702101701060507050616020705 71
    0x19034440181e0090411104558104034a0761100414462005da80782c51190503090034031608100068031500c520208405034000c2003520344c40356004064641140c3c440030300300103080f514400c001c89424482d040c441007608822660b03061807c0b110303c190691450101d48158000c024081b1420010115010800f00c0c403c00d0b030301402848640c00204540c101040d000003080303801c80204100c4d81045003882668140000d0000091403080c10109541c0c101e030078400818440b940c08002c0036400d01c03007086804142226120720a240da08400c00c00e07143c031981480341c401074500903180564001c1001c41c2c01d04003690002580203150303100004c05843e001c0b4a1100b5030320743c19411800360340121803d10816801008178140740310340200030403201302609080c9a0245401010b10702480b070060b2046c540d0001071003103e8a19070058001c6c07800081e142c0b8001c01c440c4a061601c40e500f51400c0000c80c1c3c1c40d104504907000781c0d4020005100315103444010494640c4030241c8441035110340314000030580c5401c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 489742095 1250 489740845 489740891
    0x3070206040b0c1e1507120906050f010807291e070b070203031006050306040219020d09091b08091519050609010803070305031f030821010302130f 65
    0xb20301d0549412605185034900301c003440743c0310703140c1030000803d14045070009024509a5040e101d400e9840d1902c03907042d80d400e0741d9007246c20406400d0014282c04d00c85603422403801140010944009030baa030750300076a02d07995980100544180e41c0744502c0c1c298884468550300c007240800b58a4034000440141c002488110501902c005001060410901036200d512562000e4280051071441c9001540f401e815807070b5000302410b10402001103040ca40300c1e40c0c140d50075621454181d104018040202954420320740551400081c0000703004203460045004803050280f403a50325080c8400410390596222100901e1207060348500a00b8008170140e01c45254040c041e80142e2888440a220f5403809841008046601403000b43c1b004000c0d4080c000300b200c101a1705071405a440e500c6100a66600c031282c4802d60035000329a140c08410320000400a0050b00b15200d491000702c0e4200d800d8000c000c4091201950005070040c412890414940208070140f54408000840d68013650103440c500c2004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 489743345 1250 489742095 489742109
    0x303050a050f1b0105060a0b030c1c02040303031b1d100c02100807030e070b040905040c080a050309310c02010e15060a0608010e13020103060810051906050a170307020604 75
    0x3c40c980361001c06082c4180d80c0c000c0f006076480c120f210f0420360203804520016000c08640c51000403403840f40c006c003038070000365490280001d6569a0703517030030020007a00c0d04088113455160048000400240110404105405002001084040050308002941c041000c80e2001d00240c000100b0050341c0e102035501d1919142d449202003810584c00040407102000c0034a81d183e440748006010004010082d80e049850407003021445a0301d51030034003040d6610368061241c074410803405800f0850f0100c003402d2904020389814184000d920801003140e40c1602c04040403540320310b074600d4150706541110700413400a00010901464010b230f164039040184000584c0e100810b0140001071604c4204100103092a01d00812a941040c0386078056400140c4052802e00c00c100191046900030b400043c0100074a00655140c140c2d07025108025240c12a164009803a50322a40f10f20000c1900c185000d9503405452914524101b580840f06801c10701c90300c0c0c44610042c00b40400613560b5000400281640e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 489744595 1250 489743345 489743377
    0x30705010e0d020c0306010b030a1803020102040317190804022103030a06060c1a090a060504080a1e09030602130909080a080c070201080a0b0409170a090f0b040303050a050f 76
    0x2091266030b082c03912080ca003500f1504090301e81002558005081410f55001800c20350307480c0c548100d0307034004180740807031401d000707030404070750b0082c0764041d4040d00859008201540d00b810138412915101d1040e070704409040360f880c0c1e030b10b50748140c81403610a0b4030038406450750b1f0501280401780c86c5150303003045082846a1000040014504450103800000d269904255103903410319907905a444d10841350785c1441e07440100019441003010000c4400c00c50f040b2000300424140f07402e00441a03401001c0c3d100100b01d181c1c40e400c00f07018070726000420710200c554841c800c160850f074079500658800a0414001981e0207400b14410740301d0300c58040c52030703c1203c038581c0e03800380600b014160120090229490740403d1004a000d81d8202540b00d90110007581e00160344442e1070009002452100006400701540b2000d480d071041ca10801000ca004040d1a020300603a40d650380482185028007a1070f4106506000030400070707018030080c00403040141040c508050317220425802c0e0b5000382640c0540414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 489745845 1250 489744595 489744611
    0xc06020301140114070308010611150a0f0506030714150d0e06091e06060f010512010f090e1912200105010e010e0709030209060102190f020411130618050303070501 72
    0xe0130a80c1960040a01d103641400c0500c1341c0c40c05482c8a605200b28018802c0c10107030445117040a2040007494038020070349000a00f050000440240800710060344184d00e0720300458490301c0c001030110b04583c901c80d00001494480300a05c115042007040d40542c212050000d0317a1a0000c6009860100207250020300c0149171001031349207000000d03d102e122210000f94540b80c020b102060841c1d00c0340041d10700220320829200121400d02c19401d4070110400102c00100b14400808030070811204500810300942260701015a140d40da506d01008603c0a0941c00c9030000d01d0b00d01c1c5c1c0480c11152070501009101c42c2d58424280c48031103401e5124035964030b100500441e0300300d010390750160000b0140c00ca8507182192001d09001c0ca507003c00313442040030b880099003a030302c00c000c0d14103496500e01c2c03441d52201080c6001c1100c5018440101d103e14101603030390320f40c1e54a5030280c42ca1041103015840505203003283c2507946401c014011000d100601c403000c00d03a41c900300010b0411604c00c9000040c104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 489747095 1250 489745845 489745847
    0x20a1b0b0402102604020112020c010f1a0612130209181b18040c26010e03090a23040509061b0a0f0825020304080706030203010b12070c060203011401 66
    0x3d08629032001c1030000c0c0c14240245060308415003081280c9100b61446103407940d00050307640c4030101d24540005400000e40244814064001d07440c49500c042080c40f4600e00811014864144006c84030340100041c8001b1041801d60b00016411000741c0c0c50b0b4010110141e0003280041408485030501c00c4036410380d5600c03182d4100102d1155040280000ea015049080043e01e400320a44000c50400f00302e00c0403130188410045950700130300c0d101c0080350b0040071100b62031510341c501c5001c0071403a529219000d50940300c04070071503c1c0d0710001085a0b44030740c01d083c1015045080a411f05c0b40140c4c078210103804035100e40c400c060050101400801103031138004501a91034409000c038035441c000c10300c03801807800d80010044001e5600e9040c100c00301d555101615005401d18101362107610390803100303c03541c150080000c1c816296070000341e503401d6480f90000d4040c1c0c402072051a00f005005c0007407441c0801e549000780c1d0861600d1070404254007403502c6420aa800c00c0e002400350300c0310120200555 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 489748201 1106 489747095 489747109
    0x904021b250e01050a0611010f0524030706050d270b011a0309070b0901050d050a020405180f1302060d0203010f06260406020a1b0b0402 60
    0xc0c603505540260300c0078010400562035101c00074085040003070060003a069420151204000b145400070484c1c2c0d1140e00300c039020155507542101c0750500018040c0600401400820041040e056800e003880c0342c583c084e2161007584004020844250040c1c10350740b1940c1106c400256031042c01000c40300380c00008982034940f030000f02d10b030410400c0e0318800703605a810361084007907009001303071480f8414802920790b20b4040d80410000c000403006603000b0b292a03001071401c50304040d40300c10340600783c1c1c005071120054183c0200d818411410540c0340742d500c3e521152502145030911703201ca4007c1c074030044c0c48440d0f0000313112652020344d104d1000f01c401c0b0b510140d5045507651f95a004400c902c2d0128011840040d003080c4041e4a505c805082058800030031901c1aa0310f92660780c0d4490007503005800d00003d2203120803000341c4554500f620a009103002c0c80540500d0301e050300c10031401c = true := by decide +kernel

theorem cover : BRFrame.Cov 489568345 489748201 := by
  have h0 := BRFrame.cov_init 489568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 489568345 ≤ n) (h2 : n < 489748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
