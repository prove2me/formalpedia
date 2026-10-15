-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4091
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:32:42.193847+00:00
-- url     : https://prove2.me/submissions/60de685a-f54b-4dfb-9ec8-71b7d83260d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 735611510 ≤ n < 735791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 735612760 1250 735611510 735611531
    0xf030306030519080a0f0207090903020f06180715030906050921210408040306050109020d0b060910030513060509160b040e06010c1712040b0601020706050304141609020409 76
    0x4070b407050450303076101413030324036001c05904140c522210342d1242204500c41c0798004a034440c407520136000040e010350000c0120059031002c0628200c0c00604c4401022680c0400c0740c031580c0f00207901c4082d503c10384054440060800800c070018500a500a00700f40d0500060090040d40807490310405e0312281c48041000b400c01f100014144184e41c1190314680408440880407001099000d0f0424810041c2c07a02c0c00742ea90b1102c80079124280c03c1141d9482c0d00180c890240c103624422000007810a40b0300c40d080c800a540046c28400810200f04d0602d52180001162000c80b0514048003940c002410419170900020a640c0c074421081100c02050b1180300100780302d4108002d6800f01c07802019440c0a130b940c2e990046450300e41e0f4100c00c850b144400701081c0441c5603100090500030340c40c00c1c000300780ca10705030030200c55030507025024034159080745c0000d0001940c4002100c0c0c2c8180c002d1242c50b001061b1381d40c00c5140c08081c0c804090105154480800c40114640080084944202d41407000c040350 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 735614010 1250 735612760 735612793
    0xb07020309010e0f1f1710050607030f050c0a03030203040611040806071b0b09010b100912140a0204060b0d05071b12090902181206040b010e040503070f0303060305 72
    0x400c810715001c240509840c02c1c032842d000f6803440c42d07a04060640301c07200d407090b11518026115003000344045581d601c15034078042d000c1c5903400c0e8001a40e44243c000180b800020540b01c1c8a544406401c0105115400810500800440d03881002d43c200303d84401b1a00d0070700034029002914222074050034950f28046000e0000160b40076a0790701c8000d03020350f40701c02c40240c3d490784c41c03940103407050300180c0d00d6a8041483c24200610030810b400000c50031030074000c03c0012509000800e03400b801410501448242c1b4103520703159480c0e1b400038400246030030100c403c07460103030003003002503011741446804241c1c0c07a10310380a80004070510006104039110010283c41e18288035880c460012840300c11880072650411454003880c003d4140701d8502c64503000307509d0503a400320104004644032501861414180a41101d0440251202610759410665a582c400b075406202e141d4003940048086418402d0900032142c51940c001080f07030b05590356213000b034060b221620058800e4014074044450440b032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 735615260 1250 735614010 735614017
    0x402040503072603130303020c0a06080109110405030d170114030606150702120304060f0201020f071106120f0103140f0c0405281d0a031d0609090a090b070203 70
    0x2402406031820508040c00951840541a80c0c00505901030b01d000c00c40c0d00c3e05000a10000040e5209032550034154200603184c0003203400310301d0081e01c456100f00b0103540d02085c3c42d815985400e0001c43d40b8540c00200030060300490704002d51501404c3c411162003500003c244e2507050010285040c05d0780d0305d101c1c204180915990407a0150004400600b5900d000103807004440101d156031404c20700c080d00401e102c0c54802e0b28040080d03000003001d00c84940c100d0003000d1080502d200940ca0401000c1d851f9945003d9924010020042188054100d64988060300c203e80500401d140c118507140c0ca601d0041c140c20710064a1401100c6040e09071482c0c007041d89660051010001c00c024081e5405000081c8401407100b144d03a060705c0c0000c0011080154243c80000c00800007140090700c40040402c02603404000200a81c098201e00c1c000941010001c80c00e03900080031522403801c10300c0440c0c4a4840c0003055a0702610b40b804105001600340d12140d0800d020b00904c07161542e032050705999030720 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 735616510 1250 735615260 735615269
    0x50109140612060703020d06080d0207031e0c050d05030c03030c0904061410120e1002030f070306120620030c0a020706031112090309150d050c1606200d0614040204 72
    0x800c032a001030304c0b05003e60014245601d11500000310702e690341c800c0d1820300d04520100d60060f00324210070000d00003d942c00300503036030722050030ad8603c040c01d0386d5803403500300c0034800e030790098408009101c1400300c1401910703603001d01c46082da0355030b103480106241240d02100034244564900500400c041c41511764112095201818801110038810f00c20380d0500c002c0e100404c0260740b41c50103d140450240038505014505080250320703414000c483c41d6207280020226010140740520820a0740f481d6114850300a0300204c000602c0c200d0b19130543e426408881d584003202e0b00c0041401802c0d44030a00034006103c0c59070907200690f884031002c0b810345041405514000c5030a203c00034004c0001c0314030f0390f004501c110480f4940089000406c100446424006c1c0d030090b80420003207150302c2d490142c03582c00103091507114a800d01041d0b25050749100c002c00036240550310606501150300818503403650003070505401d40c8440c89d10103d14081c03c685d0013000d100030401c1e56400d0180c103090081d00c0564 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 735617760 1250 735616510 735616513
    0x1b05030304210519081504020409020a031805060f04060b030a03080105041406091504090c0e040b07020106510e01020111071b0902030a021201080d0915050706050109140612 76
    0x544440c07a0880310201e0242401e1b2101031080f16500f03080d41c51788010402051444005a101c0c01d034100c0140495060788401800c804030900c7c203000084011406581c0f01c4038000c40701c7d40e1504c440c00d080004024907081c1d10342602c107842480b01403540002d002c034107e640c00c850501c518420000c07100c0741c0a0094402c2a088070310400403d80ca240900060fa212442c050000100401036880306840080160702146d420403003101848248542501e516500070303001e000900030342c0c0c81c02e50702c10b00000520310007021030100110364a150b000792855031141c003210340c8221818139581100c503020340c1610150181c049208442d0410040d4018000c0710f00b00c8001e19050303801d101c1140c8920782000131080117541d80b4210030b04081800405840614043c0c039084078016211030780380720052415075040c0c000d01000e44c440b480d03010105600c404100d054500241d20f007406140d600750242d40d01d00800000820302030400c1e0000c21510002c0d4040c28a80705480c581c0c14080d06c844007070044214000640c001903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 735619010 1250 735617760 735617797
    0x1c0203071e170a0e1c021f020a03111e0f04030b070f090609050f100e030a1b050d020619120c02030c060f060d0b100302120c030706030b101b050303042105 68
    0x50715141407117008a800b490040d20000c080200101d4000510801c0e58001e49074041a2200b81d250300d486a82c1c0d42d044c44282484c80d00c96202d070385002c81c41c40074803003081031107001982c9a07040d0489019a001181e102c00d2540b0941080c10380a0030000011020000141c1e200c0350000300c90748611005011904090944601009650140107100e0409818181400701d68440192541c404000504010b40601c0e040e40c90306105503a42e080344001680170070f01c2552140740c99400759a07090111170300d015144010301840d40d001d070415a07c02000607012105c9605d00081e407c40160088000c002064001064901a5817a15480700c58a031080c1d42264100d803451401c040080c8201c2e10464120f0102064403049940d40d80c00503507000781d440442c000c0f036080415040d03141c2c1030800c0014041e10260400744800b01042c40881e20002151511400304011100300c4100c508041c03aa1040c100d811000b41e942c0c80c0341a0600222440700429070b0502c88030304040c1a0040340c4a40c0654100508034506580c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 735620260 1250 735619010 735619033
    0x6040b0603071a090303070b04141b0108011806051302040905010e090616022b020d030b2206030c09021905030403080a050408090306010f080c04021c0203071e170a0e 73
    0x10f80b604541c105640620080000302c0214041d0b48085104621801a03109407140d40c80c00c0d0b50805a85048901c0d0300c1404d08002000d684c0c010a905c0d044d43c0c0903803080c5034501c05a00d1840c001e400c132540719542200443d07503880b89440040c0c00a1090b00c00030a000c0c49541d0b0784032507000d4260b1007110f0070100c40e040b84d0082604401c44a0011f0301d84c14181c0304071015408800c1001d1052030700c0d40030030507074003449a00150a03540c06001c02e007807851060804010310701442c2d01065507070440300101c11f44207a000070901b40c0c00c8038640c0683e01031600b000c1c0f1074081039160075500e0000d40c41103584045030050b00036200c40d00c2c2d102e101140e100d10b074140e440c4c20040c4c03140c008050190401a000301d8a0410a0205180c1030314104001402001094030101659250040450405514080f041e000c0d80c0100070550b44482a144000341e00c840c00c80c00143e0741c1d40c1342001111800082440c18400f0a001c272480c00c413031580120044155800e42c5e0009945440b2800204100c13044121184500e4103c20700035074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 735621510 1250 735620260 735620309
    0x909010605210115090e060d0308090709050c0a02011401140405040602210106030b0621090f0d020106140d0f060e0c0d0f0b061002061909080c06040b060307 69
    0x7040c049910310112680748010b04003001032009801c10103802c00702494440c03119a018a07544010100c0c180c0f01d03145403c00350b02280c03803075040ba0700280c14800360340c002c150030f00c02c104041e4000700020b000802440c00d0540043ca01603110500d00001582888040d4109401a0400d0750407a0100702d4019084101002400050304009200341c600507401d0104504400e1070228101900003072004140481d81499005400c41c1d03c44d0303803410b0046005110103101c01e02c0d8440000603000841003d94403d035107813a01c141c03408422108100c07071070140c0c61004115540542002082c1c0b0460f0310850a2034140ca004e00080c0c80c03034500040c002d500032581d1900424490f910181c014003444080d2a06602c0001c04600368114199007200e40e0701428650b04140455035100ca5000042101c0c0902c0c1c0b9a16484001e43c1c0b00320180008148003840410141d01c2c801a52081000781c0c0d000e00702c03540392000600f280e42c4130f4034212400e070f0b14650701400050051401090141c00e5079000310f04030652401500007507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 735622760 1250 735621510 735621517
    0x10203061f0504090203130501050903040b0a120905070e040b0c070201091401030609180507080a031e0504030b070e011d091f050406240503090d08060301152402030909010605 77
    0x41c410300408100100d0344000e540000c5204070800003460100810a140a600f1a20010603000041d0010702060118480fa0b2088505030000c078601000000001d90807030004041d45035009000c0c0c8500007001611100c080c84c002d2245004108070820f5907101c0390501807522031010700070700013200b2136814413440c0a01c400820312000180b60000710b0640303820007242100c0581c051554100448070112040020030030025024185240140c50480025a00070700791090000300c00b5501d60302c90120b0403d240c824000c0da8021904039a16140300d0801c02c0025041c1c520340211140012004003000001c000b0103500d480d0722031030241203071038181d4a0800c40c154040a076a648401120500c40010b1155213501030300000e80a8100341c00302403060003449040c0088440045828030031b0070300c1001908a0045a40701000a043c24110015920b07800040d0040c4240c80442c0c841ca40d90540100d507550b5624103001a110400802d41d0061600300703401e03070f078a00512000387c0c1d1000090300107006080c400c6029 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 735624010 1250 735622760 735622819
    0xc05030f09100903030f06090603080702150f030f100509040b040605090c0307080114180d140f0a11070f24140705010b0a0905070e220c0e03070801020306 68
    0x2501c0d2007480410b200801d0700d40c5007805800103500c0c2d0081c044401c1c19071044800419080f0300411445240d542c6c0c400c01802001d5019120703002c0d0a1a00c1d106a00510844400800f184c1e0340075501d184c244802c0000d81010b8845200c0e0f841046400b160074200100024011900460f102409690702e0355408040c000c0200402e4075405194a03502c03550b1400c10192018089110011a450040c40480d05006400030800b1414040103040f07214003145c007107080200e9600703078a00b680102d56032150b0481d039889488004e100b00000000c0306101d1035030162006030301c01e800100b600c084540d56481d00d8101402402802044002004605a0018500510300d040d80940c00d0820780c0e049101e049110313940041c88156043d0751a01e41c203800034a08911100c1c09014071000800090510080003040055000c00c09030140400c003450708080b0700700c0300713690701c2102d001c2c0414040280014001010b401c10000034502900c20400041800507060090ba8810301001d400c91281d218003a1950b030304440030400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 735625260 1250 735624010 735624013
    0xb041e210c180509010b04180605071812050c040203150d0c090606110601080706120b0f030118061107021c1412180a08061302031c020607120c05030f09 67
    0x100040695a2441142e40900060400039903440c00b0340c80c440c2901e2101251500c01d0346048800740c3c1d220b084d0030788244c2c1640c00180008256941003030948040d444409450302640c0b0605002855006c0d0020841d24148140260340c0c0d1000740c082030006901040d80c12f02c410031190058440b56080213405c80041501800300300011035500c40183c021510550859030002c1e4602c1c1720030404950420110b4010300032b036802006038628000700141190a500143e2200c10b031251a0880c0640e0b0b010403501c10440000c000304400c07600402c0140d00c40c1c4562408481541c2072420000404521005441c140c9030040c000107481141d801012880c95500c10080341d02041003044044c0d903010030050301050b41703452029283d0b15031000d040d10040400380d00e4064030a1340500d00a0040c038101060803034102c3c840c0d41032110b024040d440024280b120740c0c182c0d0051280110300045c501c41d800114076028a1050b00c2d003442000d041507890080c0c50180c0f2103500428020000300c5d4820318640d14a41d8042110700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 735626510 1250 735625260 735625283
    0x4140d0b090a020a0f15110307170c10020415050f0c0102030901090b090a031d030a0501020c07140901060827060f0106080709120f0c050603010b041e21 67
    0x240d480641400c00d98542069a020ba01140d0840c144400e9000c082d2003d42010203030589010406d1001907103120205d42084000c4040c1480c1da8401c00c00d9030b100b80c1c1d00c009004400543c515640007030b900300b00000d8450b4880d1019409481a8501c01c50b0240c596110b1081c204e81d108000070f40b21a07000e034003242084641009040f80c5046c0a2001c0c60040c108140017103005003041c10070048010016107044c1070b5400c9a170240c80041e4003c0c0c80d00a2100c410101260b4890a4071b0000c0e00700b80d403181001d0206e500004401c0781140000c43e02809a603544084040c6024215042c040740d42c0c000d0141201042c207002c0401c3d00c0c004a4603c000058400000410106201c50841414203005450030706c0d032200d040005001e16a0090030007544200c1601c1c0000441b480c1040044202421040c081c003206200c02502090010f40d8000c800076000241c18183d40c0d5a49a01e040d00305e42c030900c107214044024a181d910003c80c24060002281d0070b07600200fa0711071544001100d59501c40d40c04607500403420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 735627760 1250 735626510 735626513
    0x60a02031b0703110405190e121201091d0706210c0c030225060c021f26070e3d090801140f040309050a1202030d0206010b04140d 57
    0x1030a0072034031811000003a100282c61894802c4400c0000d008451103142404200114810b07000500c5944848030a40803442034200680203052040d1000220302c00000050884840c9131000714481c103d0703070300210812100701c2c0482d0000c0702c2d0b1000a4051640c0d000034100b0400240f00b0041120340724030303444651801075842c00d194006c4504000c981c0000c5007070920601c0505070140a03a50120703111106050b5843c031401152034000186000d05010710820301e103c0741c15500e842c00c07414400c3c04a000c443c10403480011001e44a0030b400b402d4002046e140c181520f8050302d000c02040c1c0190a031751940b45080c44100708008003c44800140550804c2101c50500b10030042d49202e500c22102c000340e201c2c0b000d01107000410b20007080d00041d020341e0400014030414a420240950300c8000010985c02c0f13502d40d49030880300e90080e42e1185520500803440820075150110103122010320807030454510144200042e40c864209116021030014280010413002c500b003441130003207120083c404100a01f49 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 735629010 1250 735627760 735627787
    0xb01050a1d0c13060c020f090c040b0c0109050303040b06090a2928181506030203070504171c0f08010504020a030902060d0605040b150a032706050703150f05060a0203 73
    0x513407042c4000744140c462101036082285002c0c511480903500304565240006992180e44904c0c8940d449411002a01100c2840207500207400e036603000c01078030380d2070905041500d0f410b0015078809100e050a9001b16445800a10030040e0b200380c1407030000854041080700f048207640143c4155009598800810103181000d00c0c2d4860302070041060600340340c145206d640054a00d0b009018110303107480342e46540b11001c210100d049601900d0050382d203650b2040d0480f224000c641c40100c0310085c82c4000000c4003008601080303249940001d01d6104298400102ca406008418600114002e0380051000d030815800808244130b4600780402d00450355404100260b01070045909070680d983c0c014401843e00f130040e04100a4100c0c0c00000b4410340b140712074001d02c5546032990a0507514002280c404804c42102c220881c040c0d83c00514070400d605118024000880d45040001d2415501c14400a040744220702520b002c1003c01ca0950300300424060558840491482540310501401021405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 735630260 1250 735629010 735629047
    0x15090e071e021f020412080f0c06180c0904020906090a150b0702030106171009170706050402040c020d05070f0c08030f070b22020904060b100201090b01050a1d0c 71
    0x1801d074001d201c2c0548448100f40301d00b41440c0e5040d15140100010010700720400c1412000a420800c642d81c1c0301281e041462440c45500c1e484071780c9001d03d10800c0340c80300f041d090140c0d813030031307854180c3d01c0c07a18100c1d00f00400c0c010101c1c0c009500205181c0828420b0400038911640100b4090000030307140f42100528005d5000399101c690340401c00141c910850500b030158000400c14503000c080c0281841c0102d03500c501c000180300082036a580c1c3c02174148020344440d040003107038010400d5034400c07207824154060102142c09134000d50902d03003149e241038800039546402c3c1110744e40d000d08000035030b0746180840c90850f9065500700d94002d404148440244002c1400b02140702d0400e503074811918059170241c0c40102078000d064003801800340d40725815000121001c1d4100c5d0440200c0c0c3c1da500c2c00358020928410225040601c0d4044912025015440034800d00d0290a02c0d208a03070340d038801c02c0a00d080c1d60080e9041284044441a00200d0b010901138012022000540c01d00e18100e004402107074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 735631510 1250 735630260 735630317
    0x40e160e0415170d02120a0207050a23100801061b0b0702030c12040b03070f11011406121b06130b03040f061404051b030c0d0605010603050115090e07 66
    0x8412080200f00c0c0e403402186030421603040980100900c0703442c041d40b5201c4905410707440b900300080003400790303109210f204050322004141510640c0c44405600f80d605503114038078071840240a164055180c21010462541c0d195610021a60300f000c03030448040c000c1005101c082801042c0550026400300c20091142406500942e1034814580001c0c0ca05400b508942c551068100401d008a1030b0186c01c40e507026206040402c2c1c80c84107400102c07006420525110071039460030043c041903204020100e40141e000300c403030b01c06140025401507214004000c041d20300300c00c4000c01e0042400c1400c0540f8118014a030400b1007142c0d110729150701680200d5080714030403424445132040120038410640300851345440c60300700c0c1c40c05941c0d031607581c0b88402002c01e44604000442074141d83c100081782c00e59001821041030070101e481c180d4042c01c400c5c0103e4001c03c1c1031000108000c02a04014114404950f035400056441e10243c116450b070090400020003205143c48402441c50f20348400303884 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 735632760 1250 735631510 735631541
    0x1020309060a0b06040f1e0305030313050d0f1b06060e04050114010e0606032403070b0d0e0d0c0803060307090c0c0c0f051516050d0801060311040e160e04 68
    0x502e0040e004038211a854400d09115410030f20041c0009500c880e03041c0103548400050008210102c011130100c04d0007a8001001031000004110740700c030b006145510711910030000c4032000e0b9260b040c2a00c0e0762201c0c071000307400a0302884022200c045000c0c001c0e080d45018200010f985078403100610001d0004613001c0e07404e0ba4440080c81031200e080300886d40103118000b11101c490900000246d118840500000001a90f54241000b00c4035500c80000752000001e08075a0b1003569041085003a81100800c44109481c000968014501c00701d07104011008942c1c81030403140349903451b20307030f40d81001d001c080e01886100d070046912142071085070340c00c1e080c544070102020b83d01c0c030304080d00340040e420400b44107080f02010030090311105040c00507401c0310020261a043d25004001041071148809061845000c0d8501402074009a00f18140e46807583c0c14882c0b82c0085002203054030a501c00c0110306004a00064141c050b02c821641c001c0c070b070525008050401c050000780a4481024560056 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 735634010 1250 735632760 735632773
    0xa031a0604030b0f0a0614010c051e0f010516020304032003010510140d0b18210a020d030603110103050c090a0f06030b010c080304062a03060e090a0b04031b020301020309 75
    0x21000059400c0d0348175144517024040c1e9402c000e102d991081c5c001d0a00740c14030100b210414200402400100c801c1c101002c4a207500050400d1107a0f914a440f01c0901115464640840e0001d0188020298a071906400a524003861540c542140c1001c0150360885040f035155442e4495401b805000e019040c0507107040032140c1006c0b00913482e4591080100c0c8900b858410301c01c001a501d52610760300c0034621050110440c410041c20f41814100c1e460b10180070b039821400c1409002c8030000c4e241e002c42903400c407106c0d143d9500040c1d003100c0721404050700620144203800003562098001d030750300c00c851144040c14039448401050380802c05800520040e20164000c0c0322040e85071003072440c00403003460301a2a18006448160251101810103010b464442917001c460241020240d60b411280794101c41c40d0055003031006000340614003c8901080741c01c40803c001d010b0020b148580550007103c590b415840b42d940c20f40e07050190b6120130140000d41c4920703201580d400c1c4095071280d0304000c0a40300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 735635260 1250 735634010 735634021
    0x17070e03100c0e04110a0c1b090908131a03010302060a09170d0e011812020406150201090303200a080603011107111c170c010209091e070f050a031a0604030b 69
    0x64804017560306548400070310040401d260700000040301c1c00c6d00000c24070820f03107a0a600140540c0759400088244e13042c14060f03004c00007200001c01103410201d5420b0702941d16001001885010412500078941d01440140003503c2c0c1040107001b0b0382c0ca01d0502c0b0401d03c0e40c602181040c0c0c068400030010366080180991071446c4c00c007940b521101c0c024645013075850840e0090745070401d00f40c010b0b80121b06640a1130703021500d842d4000301c0501a0302c0c103603412002c04034100074041d004920085002900b0111910f030f1844182140035003010714101e81c10f0401d95038590407540d500c40140500d40c150340743c42410500802001c000c1101038001c801c0c02c4034442240d020b1101762101700c0103025000312a503020314003150185255444509a8041c0c050b034a085802c2c60501a0054041d22980400e1800900c00b01503c0d101c4400c0501208100c1c13000d5581c2c5008080e50354010103048103001c6141000040000d40c8a58880480d525011401428100d0710303030302140043c2c05c503800807a0602c21010a115 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 735636510 1250 735635260 735635269
    0xf0405011710020306030a0303180605130c0b090603181c0908010b030606060f0307091e080d0309051e03040305010203010f0602060a06080a12030f09080306010f17070e03100c0e 78
    0x2084030300c000c2c19031460915001083e07660107070b11805000c02d0303910300c1c0c80c0702c41d03800005421482c43d0700a03105004504007034400641c04c400365002124104401c0c01e00192007200882507a64680004001038195501c0e0540410701c0000c000803240c80c1d0181880c0302600b541c450031007543d01c0080e548c60b00090341c1071800550845001801070761003581708904104060740e440e821a201e82c544403044079240c2e25452025030306907942d81c000d402103504083c1030000300700b100c000745011500d03400c0c21207603000d940c1c02050f402c495498801402c1c1d40c01c60b180310b05542002c00d40b40e01b0054406000c4902d01030741c0f031f200c0d142260000c0e00b00d08050780c003c4004000195041040f55000800c00303030200240c80ca44861f003aa030f02940e080090900e0b60200a0251050107a880540800c8151f0000d00884000340b4041d1a240d200319500350200d44041018001184149d8a205071280c40c8501414651965107058410b81480141954580708c0e03540c1c40c03e00480c0340e0003020988415030701d98004110200c070400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 735637760 1250 735636510 735636523
    0x21008060414090321010e01060f12020d0b13020307080624030f0a05010501020f0a065411041109100206040203060c1206101209050309041a130b0f04050117 69
    0x5500140c00800180f043c804101c43d20741c1103a07454200090b211043c00d40585d80044842c2f070320342f103062011810480d00c03d250340240c08407a01c226580c2144161503040300d0120300054a92400045070100041d60b1402d21543c00e048001c0403820f1040c031603c8a0102c0103003a40b0450741c40f04581c0e0300d02c090003680c0a25026890240000340050182c2c500c10000c081d56817110040040c1a0300d440e0f105644040d4850010400c980060014400010441981c4960030400c0f031041170502d4030420403080c401c0410340070b00d01e400c240e203c004088000340c1e007810800a0705115109070800726040102554994500d9031070b0884801d1074011301785500c1d10340105410312038000d00c07018283d071041200d8404920017000781070344080c04864244e02c4170009a4116032004164452542103883d025002d002c5c80b00001c05024052000c80702480020344000762040801f02a42c2c000e80c00030b100035403541c03902606800400c203201000d01842503030011071001809861080e030010300c0d00c06003100d4150313071810140000e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 735639010 1250 735637760 735637807
    0x1d1603060b0a15052209021305041a220207050601081c0c0303050910110405030f0102040b0313081e0904050709062007030510020306030f0105040210080604140903 72
    0x441c0d00c0e641c43c04603d2018201d14100c15400c008000034030701d44d14100c0e80403420f52a0300c0d0aa91201490300c4030b00c2000203500c940030b81c1e0715592018200140c949068042c1000900010300da0030203480030001488120029100324003100e40d1000700c8600d074440548040c2003101d0082c0d00410055140030310060034001c208102036009603102c004000131a40107480a50307280d80c1864005140c2e83c1b5020803c3c18410660035284190b400e00441d40c118a403800301030020703a9000c03010340d071459810310111030803032142d44102154008140000f400381c0c000e42044000c0103018050161528400c0004011080603020030503100510102d608501414184640347e401080c60802003006410110090840446180d03501000c00c1010461202040b044c0444401164454215800300c46401030f03110181d04200c46640c0241304519055441c4001402003a010325005002a400d94109071000c8580d601c005042c0c541184d100d1410098154014285612071616038019503150b8440d5180f025100030488803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 735640260 1250 735639010 735639019
    0x60603031d0d02060d1b030204060f08010815060109120c0306050601170c2212030e09071b021f08010603051602061f050a030f0b01090516031d1603060b 67
    0x100340140b03031a80250422038680456045881c0e00c42ca103101e80181c041101d80c03c18043c2505c0804031300c01d03056009001504c0103034031140200d0085c0f040071a4082001d110b51585a03001100d051207060030034000c0d0360001c006141035808075403998102c0601c070201080444002140410030030a1002d503200c0c040d0084001d180820a0300603030101d002c80400d000d840c0e51401c0d8000100742ca0801584990506403026800580850702c0c3d41d10700500404407510310039404038003420380f204180c1c50183c60040c0703d145151a500319614800403901081501c4070710480e000040b0001e641f50481201c180403ea4441540e6400420360601d0001015590702174010010b80a400c85140b00d40f82d004034880d640030480c170340546d483c0b5586228004800940354082e40d08840482c0002c41400000c40c4103000f10303802408003204907641c1d85240c1048038001c8030081820100440c8401991f8426040551034600741c00620030038110f40807140f4140640d0014444000703c0c0c40d80700308108181d5001c0c02104210488 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 735641510 1250 735640260 735640307
    0x25050303011d1b0a030c18080c040501050d05030307030504020d020a090b10090b22030602040303080708101d1003080d0e01110f120a02130314060a050402030c040e01020c0a06060303 80
    0x140f807030005000f04411301080c1511144100c0400e4468110210b40707004584003004c030155108136040c0c55815410041e0300807400c081c00401c0354141501c4002e000c0d5440f01c02517281d03580c0c00320b08500904000c0c1c0100d0b0b110b412503030701d41c01695070b840115001d49145c145c0050350b0240082082025503000050700f041c020700c3e69041040e002c50340300b51820404410006270b010f901c1c0460f11040460b140d04020803017440403401005042e80980e58a200f402541c40b108400c1d1181c0c510790014110501c140103030300344040a141c0107840510507954011034081c03150040e981d12551000030540040e050a0b10b1300390760318a0300b42d222009001d028107411060ba845480e00051405492040c401c5000c160000071101010402000e020345c122001600d80307031550b40e161a00c1c1e1030700e100380552010002c4500e1080034041650081c1038840d1754003032030b07000b0020300d00c801c200c400340800340c40c0385020916595428000600c001c502842221010f0384540c60004200c0d0642c600070303241d154400740c61448254480d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 735642760 1250 735641510 735641551
    0x60f0d0302030f0f04080a060608070608010f0605092e0212120f0907031a04172713110304140303090a15020d0f06170309030325050303011d 62
    0x407044849000c40070040aa440401d84d001c00550320495006007014481c001c51901442120750140054072400b0f01643c41140c1d0b24101242d0300b007030a00440707055400d900010011940207600402450704003030a48020803030148464100c0740341071001c6004041035155805000c55050102280d4500c09014490070003c0f14000b16008040092201c46140076101c08183d0f158000c20288005562280c22200d00c8a0f18441e000956001607508450311a41d0b14620204100c0d02c80075103103240400300703004c1c8080c0187c0407100c4855120310402c035000b0031072012192204440d40180c15005c100441380a0b80c07414240b9154298800c10b424008850304207005100e00120b011030104801604200400310410b40c650548000f4450400c19001c3c940c604240b402061040e9003100c41100c0c0c48a16802010409a00c016140d2095a0446034103410812480b98009441200009200320780240032003c0001980c07850b03c3c6900a070404440100c0300a64401d4095402d900241d00459801c0802141e200c7d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 735644010 1250 735642760 735642763
    0x2010e1c020d033c050f0a030c03110a050301081006260319030c0f050c07030206160b0c07050105060a051c1a13020406080a0201050f0d02040506030f060f0d0302 71
    0x11031038000d1040c1440c0310104141445183d00c94110720a081e4004118040910b02c840c240607665121414540042c07500e21929018405950100c0c3c0320006c40c03483c1407100c0c03038214001c1000400b01c80600d55124040c0d030010ba41140074105500c45a2a00c69480d414142c502d4609200c02010008060600009202402004859890341402c06031540022061000000d01314001c2c0e40d01040070994080d489180b450749a002002c06140a4803805001d0025020442e05881101d8603c1c1895020348001c00041c14585d00400c0a904140480085c0203000ea48210304c0d00e4056500f01120b0300c0104510040c04800e12840c2d03086401115210031140c50031000c038400500a0910281c4404d2503500b00c030507c00c00c011041003042010840014620f0100055141040400340581c007840c41c00b4804145000009000450b56405031540c40c2440085481c1d5034003507028504030646031341c0074800000c3d0b64a9600241d03010780f2481c920300c40540340c00e13024000403010345000d20b40316400244a88010940 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 735645260 1250 735644010 735644059
    0x20c0402090d1e0605070e09060406080606060c0102040f0305010519020301030f0b040303020c160f080309060414030f030d230f0c1e040902040f050607080a05030a1107050a02010e 79
    0x40c880301c00700a1000c0003e4000d0100700c12100a0a001d040c041080b43c0c0036448200340702102400c440055140e120003061004441c850300660043e81e2040005c036485140400c06091840382c2280050314164840e00940300034080c1e607004903803ea45603030a201400a54580d2544e0303e44964000710300f990301d161660303120550100e03405010f40101c24003040601d07110340c0440f210700285208845820791b58001c0d8022210072441202c15031900014080756000000c0101c9030b4100000f03003903174101400d1890000b0706240c3c0410b05503040c0302e007013912843d12030144042d00308081c0308180021131100e41d150f101902c200c4a40c440c16031003115410000e00000745031440e81c01040a10341c0c80d0721165070700d21141110100340c885d004914030220740011100307100d8000b0000e45400f120b41c030102e40d9450302401854000ea80000b0300000d000d1040c0d1010f584210065a8000c2d05400b0208030160801900d9000d94004c82094407117808c549100c20039540c208032a503d03610030a40c0c00c2042e0300b0040111144246 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 735646510 1250 735645260 735645263
    0x617070e010c02061204151538130e04030f2a060504050f0c090a0e01020f040801090308070521090a021519090302010504030b250f020c0402090d 64
    0x88128035035180d10440400e041c16a02901c2c2d60342e208034044029441c075004a0701211a5101a0f0030361107140014000c010340442c0c42d00700506681c0c101490307484446d94480c00011000b02103440c0f8015044402d080320009d2603e041d4541d620818100401342d070104903040f660165060405000000c0e520085030940c000151500003000c3d890b502c250329a9075050342d058406031000150400900041e1b91043d40158420380803074403c041c2c3e11260f070b43c41e03111844840764005400c00000e11103171107a412400018a00400040c6001440c0018000d2500a50450740c0c09a5442141c5410590000ea607140c0200c101e04020741003290f0180d030085680d80d40751800c051349001c1c41c0411051a0204a8402c0c001d5004064000c50026542040c8880c0c0084100f01d800c10350103401c0c080c3c610700540c418030a40780c041c0c3d9214680b41c15521703044001e070310103800c140c81c02003100801003172a44c600014500c040015607500040c410001e0f8024609459120198480e03441044945031942d1215509800b05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 735647760 1250 735646510 735646517
    0x1d010503090715170603010c0c1b0305070b091215010504090311370213091a0c0406030b03010e0d0f0216030c06120c020a0b220b01080601061707 64
    0x9560312814503040460030392014901c1031490260f8a40e031038000300d5004031550f810204440d503541e0181003500341c5015010203000308404c1c4400310b02041139865000b410400c06052170034a81e64a54406140c2138456201422442c03010a00c01142d2800c07070445905802200002c104a205c5058544040041845582e21465960425604060140a0700040180020b00380d0303d00803c000c855000c00e0000080d080704140c807a00c85941092161040c1d41000c0d40c01900c0e030b001c04441c1000b02c45c0104088101551120400c5000121461031b400205106044045120361580e07d08200941a03683c1c14422a00c40d9051104040d0407101c00070780c0c2c600070700d0985407840c190b21816100740d0420480c00c0e090303203d4101541c1c001c410701401015030000c0351060b6480d50041d5001050b00021106601030440043c0c0210712044080b65080c000c080d0030601c02c0c0200448100c03403d00d002c60420300400102c805c00c1c1034034010050340030107200c0076004140e18209201c814808030080000517500400000c1032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 735649010 1250 735647760 735647767
    0xf031b13090b090a02010e030a03020304033002010e160b0717271306060c11010504090903090e0c030108030417010912081605180603130803100807061d0105 69
    0x2500e660007444a15801222a00c1142001a0190f0300c0d9100b1010590206904140403905401c0c00118521401d8251740550704007429130f82c0d200343c4048001920f6118803100e24107014030a1762070440f0340405600da00006001031071604214100b261301c0f100c2c1102104400d03420050071610f80105c4000a900040034a00003210701da010b0a1409000d0214060001c6d003840510403500c22000d14482e03440448070028004516104041a03507664090350380050036248950001592031210041c0655050400078102511881e500044400002060b000036864200c10091790010310795041d0800e000112031342c550341c14810305c5c998a10807803041040180705641140a200320039840071240c20350280c4001c0c140c088000780200b0001059502e070484c042060440c4840c00d0164044442e44805140e9140b4055030b43c80030462540c200800a01890034031a10600006c1c210b603004501c00c010351094003030010b082c6001c05103411201e4000c1e03428040d081c0d0f48400940d1a03aa4013480346442480c3c415134 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 735650260 1250 735649010 735649039
    0x80706050d0e070806040b0a1109010315051507110a05033f0d0e06220206090a0b07140307020609040504050a020a09061404110409020304020d0b0907050f031b 70
    0x610b894607056400b80105000412810b1000c60394a002d01d020b4081b100399601c5040d003034004c444d01c03c91900a418010440041c5650007a00420315120002c89107051032503842c40403e0101c0d0182c1c25003181c84030005101c004004002e038482480038020340b01e21380481d040801103995203160140c0d0015041102940b030000780d1955100203404503283e15180e60000004121030042c1d006600480411420040c031590742c007000007103e910540303200e1840b8401d00a1001e01e8042030f03200150698201a040200c41506e8440c481058002c00c100900aa40d03034003c1d04000706072185890b8100c1407a00304214041c05a580d200c2076443c00c040c2202c001a00ba05da502c0d000f03280c1400000025080001c0050001c0c05918580c0404126601201c494400d40030300c4082200b20f9030250600c22049000b40700510a0500c1c82d0b02130b549c40303480541002018591a11180b0580c0b2044a6a4015a0008105214904124580d00702075882540200381621603d13684025031644408820b02507a41100d0194 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 735651510 1250 735650260 735650287
    0x602030c042706081506040c030204121505221101110109060506010e0a03080403060c0203091201020c190b13150f14070203040e0106033603030509010608070605 71
    0x400400710603240002e00c015030040b0340c004005140007030304810302d480c90005140301c0c0401c007028281004042c030203140e80e60808100051050722041c4041550030300002c1101d152840300c0915030390085d122500129000c0c150001521001012109000040d80e0090103c0424a1503d0102584986602c940103e1840122010142d00303150100660a143c0e218081c044c0d25402039003d18400ea84440030035903810107011060b9400d2100a1405038200805c1001c103182d0360001500240398416a842c1950a800040070a81d504003424120b035800913241c5030300c040c20003a81605281d0f80896080b01900c50b1203000b000c0400074903412042c85030000b90810040d000c4002d00a0221040c0200032400000f0410002011541003250010313414034003003590b283c000010b950407504000d003000b0050303081ca0002c0307000d030070200c0315144180b900c00100304c0701892a440d58003080840b90b00e83d611505950034001d06035140a0203007460340c0d00d006401d100c10f031804207449007078903210309100d0f41d14540300030580c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 735652760 1250 735651510 735651517
    0x126030f07030507060603060209040510080a080c0c220b010309030c032f0a111509150903010606030b031c050f070f08030901021e1303020120070602100c1404030602030c 75
    0x174042868540044104202540584a03e134000c0d41e080100d552500d0054081d00d085024280681e4480d21031600001c00640040c10160440816654a1190f00e000305241c2c40c000b0401d0000d40c802484d281c86000c280d0b11411480d08004d00c1d00340820f401c291409000301c108040060304200da0300d92a02142000200900301d0660070301020544200084803050300d54040090496032005014502d480d80d10788080040c1c803000c0e001150510385050300007042910f003d0703945214100b40080c8030b83d00d44c2c0c0d0340a218507030080015850107d9907510040825007084640e035010b640f00d510046111003503903440002d4520301c1607090410381d80c0d4034050034151030344a03500c18001c20705d02002003049019441034001c0c1ca901c000d41e0041e40c50402c41103034218401c3c01004060320030309a43c0542080558800c0d0429481400071240300404040e80001c242d0038181103401090269201403404089210f0500ca0dc1c035805c4100c0c500003402e851815100310709442a4480540200d4001c40810811050305044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 735654010 1250 735652760 735652763
    0x504051c030c270938091807060e01210204050406050901031a0c090d1a0c07110402030402184303090c050a030b0126030f07030507 58
    0x4988502182030040181981082600020700a009001400c140300f841020b940705110158400150404942e41d004288010b01c8002451001c00c1407105441240f0003824a1098032040c11600310303c1d8024050b0620010f00846642e1200c154034010814000c1400d03810f5aa19213451200c034550840120b503040e1801007443c2406a1140412020111070380c002d000300c076001e03142444016669801c100d030345c1809100280c403a40d150601038000700307803909070260300521030a0441d041c0b1030400b012034401c46400f00200d4400b299050b100e00312403500c8003030941c800b1895841d94174044541c0e40351031041e8820601e8900403500803010404555805803234200008009145074030520f00100e1000361300110001d118029180f480700000490f5248945040d00400e126040b801d5203c802c2c4110010207010509a80da01480d070380c046460b542d07044400c0d000f140221044240707075040118030031076005c1d68034280480204090802000303e034088207071840300c1a2049401e4940c4441e09041e1781d070b1320400030b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 735655260 1250 735654010 735654043
    0xf1a07090e0f040303061d090d080601120203070c0c0e071205060130020c1606031103060906040605060309010207150506090412180905010314010908091302070f0b1e1504050405 78
    0x30347c144003008240e01600c1194480110f820402c0c0049040d01c0030310050740c00d1030000350403500c500d410b0034580d0010364000c40c40e85002c014945d00c03919841130f110700540001d00244074840a115440d5844410640388a108240412007802e010001a1101200a502e00c0c4a107d40e003400022481002c5d69810895114400035941c0d0340c190051261181c070540c5100d014500948004a822803092080c80c1c80d85400514443c80c64854104204294200a204c5980107481e04804500d54075030300040d50081c0100000507845003254580800d114090182444280d45001d040040c90780d41c81c20701581050b002502e610400d001603000300d41104692104804410074900c000480e00c91680c0164126805440d011406591440d5030343c4c2695011030025112400078000c07100d0614001e13445280120404500502d4400c141e91006420088480155189400041000b03480d11004504000398408058065454076250b040013200620364a0340c40d01a650341c50001d000c120007046459112405880f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 735656510 1250 735655260 735655289
    0xa0618111c0f0f0c080f01030f3005210c0a030b280f050117061009090e0105060f090f0703020715051924030f08070f1a07090e0f04030306 61
    0x2102075010f466084c2d09240003510120018414060485586040c0e0340d004c1c0d11004076054907120258140307050030381c60f9072030800f00c0034200e5404490191000d001d107031621802c0d19002d12401c001060140205068844c5000100b00300c4800308180884004001900380051031441c0100483c1c0300c0d100803490503a172216603d00075030455020408010442c4c1403100c201071459245c400440d94285a04101004880d04a0204940c0e15200e41100b000710071510306455203903a60f1080c0c03001e491000d442240780365914000d20601c0d061001d021000400240c2d841c1c1c0301c60500603541030070060003d203903504040d0301141c1201000007411002c200801c02d1081404241001a1040c0402d1049542804024544030f900f100d03e00c00490248032942000303d025034071924644a0010040140c60103c40d6140c0800403000020180d92005110354069000d080e000ae074044d100d40a10200944000b06001e1624020803a15003442c2683d58003502001040c0c03030a450f1480c0aa0180106800c561068090300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 735657760 1250 735656510 735656531
    0x120e0c0904140606012a051002071a010801020c0307120e0630161b2109060309081c060512030c0610060801060c15050a0618111c0f 58
    0x961412030b00712403000598003540c03950801540c0c042111200c08842c40d0312010103012105842498860560040054a49039405003105808036405142c0c1245c0080d07280710078151203515088118090070b1000d0007146059071560070180d9038000c1c140c00910381784541076100e034081e100d503040d4403c0714000791005464602c000d010681c03e607100420f146c1040056413280c10a044503035120b40c060b640078009044100e40c99202102c15092940440780140c150100000004a082d4028280010050094a00b8541030800200441015880316040505101140000c503209600310340d162070803a80c105d5401b8003065001005400c0701d9000c650f006ca055281c0d103403c804040011311410189505aa4460391482d4400e0358040a6004043c00500e5500c014000640501407101502d40104400581d4070203951450381502d0044807000402602c0c2c540420005c103c281d0103441c2075050442c10301c01032081d81c0b0000032500500c51800407480c110700340d203152641954001070088072030710343c203000e842080f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 735659010 1250 735657760 735657773
    0x911030621030d1a010314060f10030b060a02010506090721090f05060a0f060801020c33010b070204050c270f04060e0411010804030816030b03030c010c020f0d120e0c0904 75
    0x20504d100d07010a003000d8a030503001d8440c83c861131182000805004412028005000b00301e11071007040300c14159254040318080d40d5440140012401c0e40d400410245895810700101880203080d040a210007100c05240308282d803990300001346441d01000070380c0b0425040003107801d85240710182081c001c00d0280100c404154220380b11014200e181070080c15521748502d4200c0c4205000c844458000102d02c481c02c480c00b000400101d44584072115910891200a5031087c0081c0c2c400070311540b00042980450078030b40201d5921a1840d0000d038180b040c210203410081380586040310361410404031044081d0354130300d410958600c02400820030f603629001c840c44516404d072015100043c911088041540c410b80d0350b18031076585552031165a455040d82d141c8916072000d5507809060705e40000102585082000e03290251403100040b480c01d1450002a0902d08012a102e0359900884d0000e040301d0740010002101d022028000142e01d00285003a50901c030a12000170b5000d0800300c28442070004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 735660260 1250 735659010 735659051
    0xa0c060c080d050907060e1c020402070303020c0d090602150124020f011d010b06070c09110403140c040b040608120c030c1c0807080f040f05120d060911030621030d 72
    0xb81b9441c1c0d005ca0740581010809050410843d105d030303888081980e6401402c0a402801940b8400d05025042080610029003007442c801c120742d000442a82c410800c160b4100000030106001c0d05c4613004170350400d0751002902a0071000c0d44020f0494294000346c403442002100562480d06c0000c101d410308060080c03044074000000b0382074542c2446100034035440c052084a04941d40074100441c2245001e00d604083c00355402c0620f0702c031000340400404a2015a454105a017520b0042e03c1201c10040070001181d03c0101c00c0743c05030f4a080030500c030001c000500c1d900c000668080c0c0c1034482c2c014a8070f56183d446041480c2701c441c0211400f0013039401c5c0a808034100350b403894440e1100c560b02c9070303000c481e0240308036105201d001c036002c0480d0200300380056004c0b00f14014810307101841104540b04000382d000c601c410040a648800802003081c040c416484032078509071070325245050030000108007580d03110311364081c44881c44012400c58000c0080310f1900201c50303414050000f03a00e8000242c0403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 735661510 1250 735660260 735660269
    0x108061e0117100f0e0705040e090f10020a1205010e0a0b0a080115030201080108060609040638030708060c0702060306030a0516031713030308190204030606080d020a0c060c080d050907 81
    0x2100d41c010900d00b03001c0740360702d106481d9542c40310f0509103081000c0e910200e01425400f5580140c03490044024001d001c03240c0c400b0cc144001607500ca82c80c0b07000400c03000f07150131110b10440c641001440403200320910386800c04d11050020448940c0c5038005080c2c0041a448000c0c00c1d072078816203489942c07902c0c0032002140e000342c81d401c0d866a0780301c11075611000215941503210320480002070001d60030758400c80c1c403039100d0030150114155040c40040700d84061182d04100324514000c60003a0b280030040d01010704241d030060440d90400384101c0b0003900903101c000f841354101000141c000d4804000070f0b2003103908207044807070500c6112039a10b803661003404140e5000015864814081456204507031a5560610071000e800e4519207040303d1000001d001814032000c80044414480e4080c009072001e50701800001400c2464230050038a885031802c0880155005103c001c4017044030350009a08407252800c1001e50403401c2e02e0312a10a1140c0d602c0341c01601c0c600340600880c41130000d841000da5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 735662760 1250 735661510 735661529
    0x40609020c280317041505070e040f0902090103140a050a0b09010f06080c091015051b160b16020405070203090a2106150b1908060108061e011710 64
    0x19880840030801c908003041c1e000d4045600d403016446580e40102c4e006030b0081c000c650030710001c07440070030f071000361f81c000e91329007000a00c600074680d4a072806110381f00381880500c50421040c03d469001c54082030052001908203501c48804030030010060100c02000c9a1001c150303000b403d103c1c076190200000540d00722040e90700c0c1140d400500055441004295001100106100e009560420840090040092804200c50ba030300040340c100403603424901c55016140d06480d0220103043d074541044019207405a58010f581341c0d8003d000742c6032000103442c0d0f032008030360351902100030302140b404010b003009420910300b008010b00705901101500c40c90710219402a091655141c056030f014107070b80b0b050383d010b1b8040c0c1d01401c00076603242d12103002c11210340c1d51405969030714035962001e034011285080414000515222801d81d01610456008200b42080d652034240b110108182c0d00f0400c114981c0c0700c2a901c42c1103280c2c0e00414004d600f810500060003c0d03441d02c420100b080c0300880c81682c03280d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 735664010 1250 735662760 735662803
    0x10200f01110403140d080f0a090209092a06091306030503070b18070b09120f0d0203030106020d03051302090c09090c0a1b0510150b04080304061b02010c020f040609020c 74
    0x1003000200f8000000d0740103075110006907c07140b01c07464003c00068a0300c1802c42e0744a6110300103803104c1000c0f511800c9481e0203042d58204c101680c4a011500640000711000c2c92160413000b6640d0106540030041c06850303070f00034001d50100160041030107401c090002e100c0420b00324200709040c09914400e901d090000c2c06c0c1d20b80c89071605581c0c0c1e1464080e0030b40303800c130520264420b82080305141480b401681c0c00c4805038824520751074100210000c20f0070040c0c1000006205086d01003040d420180d8280c036080001386060030100d1000c54070540028862018a00401d000d8450300c0280c40710440000c142200e681031401c100c082c2940070040110104945c40d280301c021030031808442544540050281c5500b402498041e07008102c40c41d4128100703261100b000c105820902c0291014110900c002c0d41c5d501e04120000d8521003101541d01030551542c0c80190050740e0101c0c0d200d50f19941601d000c0c0e844122100000c015203230b9504130920313142c8080f40b4001e003214001b43d6100102800d121383c00a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 735665260 1250 735664010 735664043
    0x91202010b10030b040b040f02030703050603070803070b07030204090513020a060201060b03222405010e190f06080a060516080615070f060203070f080610200f01110403 74
    0x3a640071461041d0300094610419800601a402078800254028000195072000c4400071b02200c82c45c51494403c146c0c04410000c00c60381610034142c2194081f402400103520b48001d10340c2e28801d0410013030903074081d103020030300080c004c0d016500a85407440d81800a890809180c10001c45030b500c00760301c9881e090b440029040d0062141c10203654020410754034658170100036000030254540100d09100c4400f00040101d8445110840c10031081010302245401101c0e204080d18010f030080b15603d6030b0f0364140418100c1110401c04540d03160307140890283c680301c109034000c0080703a000e02000d006142c03400042024070341c00180304144104205c244070008080c2100c1030081200d900b5003140e01e4166070780d0420f1801000e490101d215182112170030340159140300507600306462240c0810071180400d801e0f190002c850781e030310800903101ea940c0c08a0001c2e005081c106404504801380d013231400800280c00c818000d03040b443c001c11000b40500c10001c62a00541e0788544025514815a50103201c0f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 735666510 1250 735665260 735665263
    0xe041101080a0c0e0d021306031a01050f060904090f12120524061806040e1603140a1104050d23030702060d0515030d2001020c0613140f01091202 64
    0x221003d0b038039940c440300c00c10141d00344031058001c4030051340d03c1401c0c90385c1c1040e610500d0107044042c44c800c0080c400c201c21400e040d00300d07401c0181c0001c0c0c416007041d040011192544000e4034050036084402191203101418400207041180c1c6014100c001a00c0f2402d01150300441034111170861355104220700d1340e0310341903100c107203c0c0640e100445401d044861003651510b070018003006821a0740010511401c00f00240165100b540194020030a000c104040001840c4000021035000c1c2014071120f4140308a8405c0e81d1002040885615628401000d48000b00000c0e140500400b40240c2d101e00d265042140445024102d541402d49252050080260010041e524201e078058202030400e4201040704000e000028015141c0e40000b00e0010b40c1c0743c3e4100710b003070582e1750184c0f14541c21207291200c50b424500d24660710010740e801004880b0b480d001c005000d81c1d101b1059600c540040784649018034180512400e4034101d0700c5014407521502c035042d4841d40c03401c0d116020501500385402d100b039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 735667760 1250 735666510 735666521
    0x8060109060903020d060207080d0203100f050105070c091815060801180b0a020d0b030313180e061b07140105060906120d11070519090e03090303071502040e041101080a 74
    0x1e400004017625007001801903009080f12034401d400c07040c14500401c480720308a0b0002c071003100b00d9a0030010b04000340c400001246016200038a07241d85480d034152509040e40b016440703640741c21a070f2444400c00c64030790f203502a0130060f44483d03050f404035002c160440142403d40074210180d4a05110780104514a500350f8031481d41c092400c41d015541c10900700b0080d04008100a007440d282c075600c0302a0f540620081401e514080c00c450481d9040020f404034450320007a0340320049140001c40c2a000400050341030340b00142d00d0700b42961074000302800500d4000d09100800c0c050020442103c443c0c41904010b1250000703a4403010780c0d603030702801c00c948000c403203040342d180307412189944966500c258001c050018104d01111256079075900400c0d21f003040e05001e44298001c0d07038018482d88800b8010b0020400c9070700015402c1550b4030b40040d4580c410650028079181c1c03180030490085255806840041c50031301c0d0788040c03503d402d0a00310704590700301c015540014484c0001840f40b00040c4241c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 735669010 1250 735667760 735667763
    0x7050307120209160c031112040810050109020a141c1404060b030604020a05040507090312020c0910081f0609020a030c200d0f1e0c050706021c12090b0708060109060903 74
    0x10b250f50785045d0344007600c00041d03000040c1d065010303818604502804d0100144002d1040e9002032402c40c204240c0350048401c103030022100c00d40108007001076568005241d80b0b200201340d0240c2c2d501e0100d683c44001c00131001c1c0018044a09100302c242051054503491480703240120000d0058003519000c1507200c0104071b800a40c802d0161000780400d08290b4005070380b0903090f06104070782da5182c0c0c41e588001100f8585c06401030f440300d03101c01c0c80c60030072640c0300b500203e0300d80c6a0400385003088149600d54003180803070080b0846060361420b60a40d2600204001e0131322660855403444c0828000300940010182c101c0810344501c141080c0c0d24a81a440c0d40b17041c3e80c0000f411002c0240501250074540e81b522480c10003d00035035548001c4039031a48203401481c4c94682503071410091404908010440e0310040a64014094494410b442c144aa020141c02d52625140500d021f00e0840010401010040e00e00c405000c03c2000180d0403840c010701a20003600c400041940d500307411900260305010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 735670260 1250 735669010 735669017
    0x6080f01111812060c0a0215011a0a120c05070b0112021e04020c0601090e070f061d150c100501050621040f020d03080115050c0c10020705030712020916 67
    0x1091860602c2c10079044004001d1988120350041c58075645806030586104040960000300302a501ea01086040c2e05041c03a11300a80082d03140504090307031104210f441e44550500040c102042c1da2051007141616280480b00300800303010080000c1c140e4100303500854405030440c0c00850034a00c151880d861140e0b000340103140c12800b207007580703800c0c0302850724150704140c00780b20405840e401400418040d003c2c030200010000d107070304001440c120b000d501648115500b0316050040070b40c0300350b400c40c0301464040703113014071050000441c810014200d4080440180400d000c02c2d581d10120b10041020000e000030701069803103404020443c894594555074202000084252030403900725070951140c0034000b07548421b4415001300315082014201103000440d428010701683c110100c04a036000b900e03141c41c0d030030040041c60250340c0c0c082c902c6190741309076224400d03040700c54400c1041c9000f0300030107000c0d643c07034940e9003801c2039441e9040c6004030b202e071124030000780c0d88440801500d0700c660a0340e039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 735671510 1250 735670260 735670267
    0x305060f1306090804091a03010c08060109031103150f06212a030a122607050903070b0408010f0b030d080f0408040807140414010803030a02180a0906080f0111 70
    0x60700d02005150800f0300301e825041c18071000400c1d142501c00e081e01803000e0741e60074026240344400c0500f1101c020280d01d051000d920280809030340d0051150013500d501490000303844010000203490700040c08500000f0000050400080e0080c091119009400030780d0241c070900f0174130951141203a02c1c0c01e2440300b99800400281418543c11051041040b80308940c043c81e4683d40f8040303400c0c400c12460545100c1c1d880940381d41c13401e030b000012118050000d0000c000e0802043c416602001d00580b0174801c20402050f0411a5038050146030000c12411410994440d44c60150602801e16400070700d07045480d150f4510010700b008640c49901d51680da0f81c24030b40e40d684070740b00d41c1c14000150050300c042c0420f0001050140c8204407140141041c0f0701c0e0282c00f4440c0c581000300307076128045c6111120315440010044100f0000c02d0f0390304500340c11000343c2c40c1c0b00440c45210240c02d48039a100d5002400d1540010314100750380c08602a0341304a001e549040c6101c414441c280c607a03042d651040e602041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 735672760 1250 735671510 735671513
    0x603150b03160c020307030f0b07111c0e0d0507060f1d0d15180b0105030d020d1220190203040e071206030f03030b0a1d040609020a08160305060f13 65
    0x42c101d580c04031490404074408000d54002c00c0c54003085410445022100c41050b00600620f103a070264803440500d4800340490b822080740f83c641e0000341c0c44111a480c44c0c00e540a016008007030180300c2000143c8038403c18109800d000750b40700d180c0c3c0325040c0850300d448021085603100f034240908004070151303401c03295031a070424819003000150050b9441800c11340700900d0000e80b0b0007415400e030303904c001420115040303040401089170306910a92095010580c00b0710865008142e082c8900e6a0f42030003118039010003411406032075203001010350355600e10045400081120041d18030044240b4070a40341861502c4280d980381b1603801102c22a004850000e0b41e01442000c512200c90506000440c11940c0d03651242c2c42106050800c6003c20784400010310f4604042203800c0050a81011400100c0b0241980e800741c84005803020b440303d40c03070f2260399040d501c2c0c061440c0010703d43c80044030403003180081c40d4041d031800c03804220ba0500401c00032031150840300640500506405d0f0b50004031060a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 735674010 1250 735672760 735672781
    0x52208040e091c020d0905010318020103050a1b020a1109072312240105090604030204050c120405030d05010f03350d020a02010f090f02060d090209100603150b03 71
    0x1000304000d880f840d10955200d03d01010030b080701e07258a400819401c00b01000141111840d03821860416240210074841440101c004607903182e0207090002e480d4940290035406003a000303441100d0915407200055080b83d00141103c0554058041410520b80174800c20140c07503c1550b0280008040d50303241e45ca4115a02c19080495202401940c9440040c01219101040c211145035803034482c2c071020b9502e00f112400640500f1024a00213240942d00d1000880702e00503808080c0c00f559413940003450700002d80003191175041c8403101d100708030300e01490444e5981e0702040a4144007404e00b000050000b001c0840758040c3c4c0d034825440041905507818003001c00c07001016050321010200300822210310500d00409043c0845003003d40c1c0d8034403c0d20003174251500e000391400c6c038610b05a07045001c01da03481e0085a06030360440d08241e0b14017254242c03501034a14070101039070205900f8244554043c02020101c1260115201807008a400342e95086071300c200e51280005222040001032841d126 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 735675260 1250 735674010 735674039
    0x1d0403080a18060905060f041214040302060f1b0a1e1a070810080c030d0f050c01020f04091b080601050903010603150203010f0f1a090105041805220804 67
    0xc1000066401c41c80a4490360b032441950180e460f640d640101c034040c044140400b80c2e0145000031780807082d0070036646080742c8860742e200324010008088041e1125984080c1210004d6400070302c41d645418410f400c41e44103601165141c0c95604100c41c248034440d80c0070444070303402ca40017000403000c05e24600f4140c01c0100c9120080f034818410102080c0b4001e1001512030288580b95281e040c81d01e86410201202c0c043d5402c4920154000004108982d50019200c401d4080a1038683c07100c034000c01d4107a40b41d00034150484529400400d0642c010348a90000d40b048030740314841071010703d50b24103051124000201c8000f0000300020001070265000d00c00822104801800000d0115070f00c6d1180f440d008051200145010380010040215081c02001400602001c000002c8818a03041c40860751100e0748034200060400898280c007540e00500c00d450040008001e24802070312440d080c440144003c440307042940c8806490300303810020034819441002c0e48a15a68130340350624414401241c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 735676510 1250 735675260 735675271
    0x60f050d020f0705060405010c0f0302070507050607052121070f080c0c031c0c1b0f300320041701020c0a0c150503040213020d060b1c05011d040308 65
    0x364204003c0c40002e07410004184958041c0000141004102c07000803d0308800e002e000c410140103210000c0403070001715403502101e00450b4600ea0740c80c15880c0032801c1012100081d001d00856105e0807140000f03200090841701c94840d0003000c01301d251105070f180d0a100756880c1e000103145801e0700c000301e800b9104003508042070f030040328140000c1150300b500e598044140b103c142c007001041440d1540540c0a040442e8919003001004031090440740c1007003a0320b60b1000360007910f46650000c203001e0410f0000c4c01410b02d5000a8903d5940c800309003102c3c8621840c07400000340f030100450103201c1d00000007140103140c40c1c8031901c1c05240c860300748016103010740e9903885554200100c486030b001c01c000100e0700b10b1089203d01c11342850710710b810340710140b1b8000301000c0c80000c100b0000181c2e41e9400f6041c0650075141d0058840c00440c40b140000d0029400c00c0c2c19801c0c00203940d01000d84140710b080000d20460fa0b050145130b8883c0071240440b03e840d810141410003000202c1d0000740103200442c1d100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 735677760 1250 735676510 735676537
    0x6010503070e1807080601150e0a0605340b1602011b030c17040b0402310e0f060709080106050a0b090f24040e09010905061f0801060308030907060f050d02 68
    0x1942c852171800d08080c0b081e4007030201d111a401c2e45031201504410703e800d48030000c4a0082e0450714100002d441442102100c0c81d010000003001004104070202c03c40e00700ca03010003802140152413514850750b02c4240d850110485005400c00100d501c14003a40b54200c140303205005030340e400c0740c600358040c200d1080504240f142c078202011f26080d40910b02c9115602a00711034202d401c0074018440300b030000c2c408440e541041044401442c82e0112001e802000d219000002c0103039601d92101c1c2003150860015459008440c2401620356001780e0400c19943c1d29802008201e940d00200302114200d40306030003180c0800c2c40407980d1b03031800701c442044029000c0c00006806e000b0029154010094400c0d028402101003414002295410b01155100351000300030003012829454203a074a00f8003d043c24150204000d15629040880b41901c0003091014000e2201b0350301c0c4d107094a40c40d0421a44415184103451001940364491020224030654540320140360880354072260010354440340600018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 735679010 1250 735677760 735677773
    0x6030b0906240d0e0a110303041211060c060a0b1e0306131115190806180403020102090301020c0102030901151a0a051e0306040f15091802030f070806010503070e18 72
    0x395590013000740302c010400c00707030035000d07107070b02d005d82c500b80005c19068065801408207014400c0780d10641d00002d9000302c0407401c06030360900052000d108010180140e0b0091205000004c07441d6040050072050444450802e00440d004001609940c24580e076411340c08000840c0d009100ba40010b0890340c01652031004d0034101501069100d401e204081142e031a000440320809003541406030b1304114a4030b09005503042030320004004852400c200d070885444200801c08040c000d50445107520320180003951580c145001d000d0003500220360419582d402d082c41d0700e9900f88101c0c800801e0703c2d040740491743c0c403000440001d503c0d84c028118a00c140030041000c15038004a2030141c1d034001a4402105541e4030b00300040c4000e80c4d00e00049502a07608002107029101c1e9100030744030a58147c0320000616460809034860003002c01800690103000b20b0030180110400420a501918440802caa60f5a40c0c2d880c01c0c0760b0744660610440f09047c6564010503c0c0c503d00704050500001c40104a614 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 735680260 1250 735679010 735679027
    0x1e0c060a2a150e07060504050f0111060a02040f09020405010503070c0303090f0807031d0112151a1b0607020709110705011b0905180406050c190906030b090624 70
    0x6284001c4a07080e0303581d00e603080303888070105000d020302e00302024044054564a4a06640a00503000394061a44959412401e50019900c504003910303036400d5201c1103500384c1c1003001f07030701d80254414003c40312107007032240b40401c0031150b43c0219001c591040c0d41c1c0c81e15582c4c52441c1100c070011404801c42c10180c680f580a40410400d4024401c02c034040c507030b47ca42e00c040360319010305547d5012403a222460100d1101e20b61a81e00044407001c003401c2c080c1d012a199041c500d0120180d507003500245502110700c40c076108070f110340e0b902a14034035120f80083d419180408045c15590030342105c030400141d002030030a01844805801006884290407a003a00b0062140d81d02829984c9001d0b0040950724051803400d0081e0744166210b004003804e440800f00751072800c078980c0c0c0d5070000800c05031001d910f400200d061980c42030101e8403201000a5060803034400c3c6500201812203511030000000e0a1011000365458520491030090324010f10010310078031800c0e03002650750340030700076191400803e01c104030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 735681510 1250 735680260 735680327
    0x1504050415060b120a0504050c120c090c070308090a0f020607060207140a050d1110020306011b0f02030d2d110313030b100810020c01060b040303021e0c060a 69
    0x10301403c40e400c600c0e900c030010f080801004460007080d495106003002c0902001c03c1c000300325444000c0041d50704000300f60b001000b01b03217801403401e12540c00c04980410856502c4540300a846900d200741d4a08289456440b503456451900c541c1c040d19074502c900d03c920051412400900116118032009402c120a945030900c45804240304a4401e8008050700c0040050a1140c48445801da04014010b4100448911769070b10341c0140400b1025800404110142e0080484200c1040c6141601c0c0406000749406449000d540ba0100d0080c450007164050035800741e1240c040300c100c14606030745581d0021000c032071440c00c140340000030701c101c2c6049034580c56020f000400d02c0c40f500009041900f03285151020340050300500d004851040e0b4482400510008031b04c0650350640d580c000358480c00c48c2c425480c0148010b6016142407103000400004058000c03601e00850107840000c2c4004090070345a240d00d4042101c02d1540c4480100000081940151000c105150380c03a070380780c00070100b9681d07102c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 735682760 1250 735681510 735681521
    0x306032e0207140c03012706111c0606082514030a0b0f12060f180d410d02040503060a0923120306060d062c1504050415 53
    0x954801801642c14503400704100580c40b040f00b01500200100c561f10b40a10760114552284141203420483c1100d0a000240e049181c10300910040c3c41c1e42c400501c040d4940283c5420703c4500c00d41d0802c400010401e002d075048900ca00104924503407840351800a548080840c9501c078420320002e004008005140880650305c20084a500000e004620401700601f4806402049201e1007880c1c20900b500340c40440d42d1030300301d95904c50a0030142c0f14420039042c65007649030310611510560084100a50340080c4c3c0c42040c50000110031112600b0181781c840b0100e5850700b0070301082c15814141142800440240b10050000e030005087c00e4076800003d0030817500b518092807a903101c2461b00240007031742070311303072031001c5103500d01d81c0a1214148003d48451641044052160010000074520740f07404045514000440e40d00300b005030b031101301d02041c803203119001820301c900c00b000e0010a0020414058002e034015440c001203090154208006488000c00444800b8042424100703610014081e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 735684010 1250 735682760 735682763
    0xe1f120f020c0708060c19111b010e0613030b07050714060405070e0f160507020429031f0207030207081603150908180127090608030306032e0207 64
    0x9a0b030360001c10710542c501000c0342c1100813190083c02c00d0214002c03200d070440b008080000d5038882891440706040d41c1418282d501402c02e40548446914031682d040344010b0303c00b100343c942d551041c0070102800814020301c10340c3d00310400c904406102240381c0c55071055111585240007841c1407083e903120308401c44483d20008071713907100c242403008108080c0644809130400741d1950400f441c2031400d40c401c071540035252041c040034120480500c1307445001101c060940140c0140072140c408692114a00c00340c0344260300c110700c2e20000001030719001c41d0b820040e9082c00e5900c0050342c0c044059200075401607500300c0651240200000e100882801003140304950346850414440c9036042241d000079400314440c080910303007056100050071600540b06e1a0402c1c0c50800c120216110042e51a0f1801c45d00311a458001c0182e9450710712032030b841000540399102c01c144109903407003186950303c2c003040d01d0f42685904a030703000740c04039078510340000c4a1047c230f006491181c141c1009644100c1c1d108400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 735685260 1250 735684010 735684041
    0x1e1e061112090601140607080705010f0e030a0e011b061e051e060409030503041e150f18021f09032f0f06030601030207021906021c0e1f12 61
    0x8202150b041400424010122410b602500390360718800505184140e9400603c100d0f000306058051010961140844000c00441005010a842031a130b0740c1c0d07001700c1000030008146d04591182c551051201c0c80c408a466511072460500355a03d16000e4641000d04001c66003540c00800c035903800030b01406c0c0c09000b46a031003c220621644061103411001051103001e5030500c900365000071b0b4800122584107411a10030003031031098101031002e49a80002c064848001c0c0e00c100d400461840d40080d1803840d4500040050b61186403603000100d210300b0000c3e612803185490b03000700340004ca0340101d05601510345042115102d075181d1081741c2442030703030300c44c040403c04030b0b407010310458600c01100010883d01032601340102d800140c040e100c014595410981c0210b0154115184c42031034000c9100340b1108402c1060701d44200955039136040d1007443e82414004844401e9030701545c4585c40c2e4032800b91030500201c08504100740170006402c03c42c1e04011410340e500d0000d0a180c81407a40309002c400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 735686510 1250 735685260 735685297
    0x9020301020d140c0a020604031103160809101d1c0b0a0b0a081c030c030902090a15050d030c06050612060414070b09030c0d030e0a030305071e1e0611 66
    0xd50003c2c88801c003d200c4682c00c0360412202e80415000030b0a2903110303525180c032100a0034070001c02e80c01c501822a500c1c0e03482880449040c1000603840c0606030503c070a5507505116040c0800441c0e801030321008041250440c0d0140307101c41d0801d0307001c0328148036901c80c494690062070313070702e40c81c8118080300d8000106564560a50715444d29101040052445900074890074805000d07221481d03041c1d070303044018990780e01d5546094034001d801c00380c00c42d42c000b4810b42591801001e2440a00340c0d2180c0f0400e00c1c02c0d0000d0104840c540000d9003205a81c0582c0e42c00100c0c2c5066645400030400030303200f81e520421280207111640410032180d446241304503100058070900c0c0419038644140d5410154150509000707001d201e803000541c1142e0040100c52a206100403420b055030101c8a5041107a00000446804414180c1020041038880e1040c501401607000d250b803401890403003180020b082611061541121049101d0740402090041100007000c68202d505098640e015800280810301000b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 735687760 1250 735686510 735686531
    0x10302091501021e3a11031207090302040906140c090f1306030605010b030421090611101803030e010608120a0212130905060121020d09020301020d 65
    0x40400398001460703a80340c04602400c0d8001035296125401c44040420510b854468444010440300e140e0440416101884d508101100c070b80400b4040b2000c0754078818900e0143c04c15101d0280c078030b40f01aa02020318140242010300c180c01c80c1010f0281d008025100e18080090b0352148030741c401203840f4003400100011022548180742c0d5004101c0f0004003810710440c102502d4040100c20b00100c116051b156038080b03880034100411030754001501940c5030400100b12201c0350802140030350300442901d242c8529541451072083c01c9981207000003007800d1070800642d80203289d02c04d450802d2500343c03804d079600140f11004840c4100c0c1e0307440c100300c44140d00c841890b0705442066488500b20000f802054241040ca0703a50305421440410840f00009010441c135100b80502c0b41c0040c010080940d444060b0074100d80d01e00c009001d060541441c1c140880d9156001d000070784200c80022401c28882421010100002d4000c00041c144454807802c080005a4080c402003189000007440040e40e081c88 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 735689010 1250 735687760 735687769
    0x12090a0f350403031704120c02030322030b0c0406140304020607061517120405011103160b06010f050307390b0108120f0d0b0d0b070f1812120e0909010203010302 71
    0x60041121704000d015080c000440c0034141e802203a04442e09114260070340740d10100e40b45104d0a270899002c60803140c90345200d8506480c1107001c60740210200c040c1c40d219184203107104d110f28460340d00416100c0d420508140991009160700a000521160500d1569162031007500d08503202e1300300300412076105114a01c1c2c50101c40c0001402d0703500801c05031740e40c070300b0100342031045008080c1440031845650100c44002c000b194503c0f0461106620784412a24050385156020340e4698085410740c601000000e2141e401d8034412030182d0741c0c5401011000d2101c1180e03000740d10203030f00c081110801c62552255068004245075100341050021589001481400c00c1c1e1038065000d85084100690107410220000755042001200b500103142c603064000281e80440c0c208008040038000760401c0001c079000280d00c2c4848180b52a18002d41c101e14054030b001583c0c500411301a4000c548e59480418400607003c07a0100007810012070f00d00d2044c0026071200c004440243c2240c5d00000144110b00b030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 735690260 1250 735689010 735689027
    0xd050606040f0c02120726030a180320030d020a091e080a0b090114010b0702040506011b03120e0303090703060c030915090302011b0512090a0f35040303 67
    0x1032070030040201c40c2040c43c000b9100c007952802c0c2d402101000c50040280400981406090441d40b0b588400c0005200d003a4905504100c2d004d2403080d14001d401d0410710042e4941880d1140e041e0382c1c1d2900301d131301070800c00c1004143c0994409140300502501144000c0c902c003c2000003074036140c20412510300012030640f8a244000d03010751642030f4004002c1d07040006101d03008640c0c0090b6202060740c0d175031060307401007603108a00f88180050100000d0802d03144401040303414001d5900340f155a4603440152402c80134200082001400f446030304010a01c200151007204217900c0380410069082070629203990411344142d101e680203240c040040040300d1281d2000f800150400340184102900c0c0c0c41045207104920589050301c5480742c504040c402e5002c2c03031200d0841c0f03400742c89046082000501507000203940124031451803011410901000407590038090740041ca14220f04040d9072092a40c400c01c903014004100c48681d103030301c0c182044d01c1d12a1103180d20480e0581b0340b032a50030000c02a01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 735691510 1250 735690260 735690281
    0xf060a0903090e040807120e0f0d05061302011e0905030d02060105010804030c14060a0f060e0417070201090e010602030a171608070c080c2407020a020405040c03020d05060604 77
    0x345411911000242c01250010840740781c2405100203985070b080807000c5214020004104040c805c0030640741341e404c0304045000b000c2c213891b804802c10741902840890340c50440042c140d58130400004000710101416000341610602d020012071200643c800f604036041d81000c0003145891805000314103042001e47c4000d001c40c070080640c0c0d450310002800040d0044c00103420171958005110a020b001e699a0508002a104071030251070a002d006005119003644c82c61050304201d00080d4076040202080d00554014282c1d101c0c02000c9010790500f40d1108000301d050101a80d030020340c8003c0710850170700070400c40e00619a81d02400c1d070003d01c0300c90003000845810116100340700100da17208560403000701c81c41c18200c955403989003044c0c8011004c0d01c0d00a01c410000544035500d0740e008250000c02401c600c012031200790f4003404206451100300c2d454001603121100d094090300e00354002d80c1d0018061a0742808003034a80d004101e400005010680742d681c0040c045c04540d080a10400b10b404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 735692760 1250 735691510 735691531
    0x5070206040f0f02041b090f060c03120e1e0a11150a14090a06050706150308181318050d090b0d02093001060506190f030e07080f06 58
    0x1d01d841d42d41c9800707078030560300c01070115461a00030804544840e4842d030003400d02d0340300252021007410710003842e040c6180901c0481010329000050940d000d286240c124070340c107444d043c0c401c004141854000b0442c0c0d0550800a01c00d03d490704c14820806c40d9030aa9410400c1c016010306540c0f400c3c46400e0761080f0700d03128082c6003010501c2100c40100010745502c0c984902c3e0a01201c50a207400c141c080c002d00f91110341c1f01c50320140004000e41c11400a00d40c0c03510a4031309010b17044140000014001c21480040c1448a00708540f2054048901e80b003d00c4020007440084203a2003613040d80100c40003c007680c13521081551f0940d080c400700f0801551640c0d41032034070300b030903034204030415003580183c071549680b084d0081050300c05030361503070610088844064880c2e484000300ca000c8031960031122004960301c0d440c0410119441c14680c0460360b03c071a0507560115400c0424404445070311f4044030000406590303c9098412483c02d21100005005920040c082d803d1031504807810008040d0151864 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 735694010 1250 735692760 735692773
    0x12160e0103080f0901020705030f0c130608030906070606350726011103040b010e150a03020603040305090a08031b0309100c03020322061b050a02062b06030204050702 73
    0xb6500e07108945884040304035040d1502c0040b00142d241582a41215070f0502402403040c0d9150000107107002000b804482410403491010032100444065000725039a5410810503200e07141895802007000380c2c0320381d0000406e1540c406c0c070001c8481d05e041425803504c80500c09403001591040680520903c280081c2041344d02e000e62440e10340341403802c0244c80740054150480e02d0b40c42903103c4603141b00c0c07401c2c0c0241c0d646000d24018015403424024030451505500100310410307056861004160710103400150214219000c00c815604000c1c0214100007040144003100d032102c6503094010102980190b07184c008170340301148000c40300b1103010615441408540f44668501e140075400c1c08181c1401203036000c07141000c070305610911664104124840200700908010000200102c1c0d110f641e07003040c41401102558503080d40c5c030380c001c1c1041d448058041c000d0315049004113940a243f0700700480000030300c054104009050f0500b5180780b40d543d0000c00035810903004260740305440c1e1015180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 735695260 1250 735694010 735694013
    0x81c0f020a110f1e070b071101080f07020304060507080417010b0f0607021f110307150501060816200d02030c010c170a2007120936020912160e0103 65
    0x5039544001550304c003e01807104202102e034024000c0001620366020103a6460f503003130510189008e441c02d1801e0014803200006510b1482c0302c8001c0c0d0056146da4061494a49040412902c3d90480103040c0c4204004100c0000c02041803080b07842c62014502c00450038103848001c1100b919417221300f41c0d0040c03000301300c2040165109094080d102400208040e941141100100d802d0610469480c1040c8800103901045c411140780401c1101400881888941e807a501d04988041040d036038800394260007807000300818000c441041040949040312191328201344000341c5004411700c8900c01503000001d100661600c28060008480c078503040c000f0041800d2040d480318680010b0080251965801c042400d10015002140415421441154a941c0c0ca814803030382c0d2200e03204004c0301007880c03101d0004100e0300e40c030340140403c0315002e50240d0748000d0715040301d507190207803044034512a4208100c0c0919516000059100c812005c0101001d100032002c041900045130045540c10903180b00400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 735696510 1250 735695260 735695263
    0x200c0109090e01021204030c0b07020c15310f140d030507052505132c1c03020309160e0402041e05010e070f0504080a081c0f020a110f 59
    0x10101c0e01c20000008450341c181440390700a0003451a806a0810404284400c0c141d011480d0a1454040e2404031000d0301c840702c00703070307555103544803030980059040102c4070240705520050810b9075841486d014280e81c81c03000c00d000200034250201d40d0440300c01014000910864403e1000e4115805d50940300c0961100262100c0c0302040001c04214002400741c0400c00148010155a641c50002984c060318441c1c00d101303401618080c04c3d0060790b0000180041a41d14000c21414090205d0582043c40060700c414076136070728003051000f1901c18071044035100c1e01300400c0400803508a0343e0044e26418002e01c0142000501c0c07443c465010b0b03000005202d0350080318000c5070003d82c110b400160780702d4400d6080c80e00c0400c2400d0751805a140500000d540e409801191344900c01c03030341c1c1d00700d01041e4040054505006a0141207480e03401400c8900c0014034540080100385014402c41800d04c01d0b400d081e209480704901d000e0030103070300490020071b01d0741c204030400504c080c0d02d005051a040c000340180d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 735697760 1250 735696510 735696527
    0x100503070b040b2101080a021302070f060c021504060f111201260d03090501060f030803060405060d12020109030210050f060f130608160f080312070302040e0106200c01 74
    0x6101d41c100010b0380301380c090000e107400094208500306410290b17590b80045482e5407402200364000e072401e031011450f5001502c21110440d601610070304042c1c40302c0e200c00c0010a0400b5485055202c1c5501c0d03d00c18408100e4054441d40c86500c0c04076800046444120641c4e546000c840041c40b802d125486150400c0350b03602d4159448200003a5024880c480408034403001e8611403040c1d4041d800405190700d0303040c0c01010302c41e409007000380b050580c0c503035800054403505d10014240c03a400b032010607a03a142540049410482c01001600d4003582e075115903128402c17190241026070b545071030810801d5018060b0000300080c0003004c03c01c501d0725544401c60120300a154a219141201c48810603a85014001e810300c92550802c22209440d03000c02c0ea0b0301c16040c1c20490201c1050f800000c0d58803452401502500d4510000d54100580070034000703c1e03150301034810420b05030284070120700002a1072900b4000c06e841d680e1045840c10925040c0d41000c0c9000a040064100740188502643c000104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 735699010 1250 735697760 735697769
    0x70b040602030916080d08060f01020304050f030709140717040803071b080409240b04031509170406110c1507150c1e0302040e010506030402060c07030b100503070b04 73
    0x5690b035a90194240e05004100e0303030760654584640800701e492800007844002d545142c1c3c03102889a202c0108003c0780c0e003481d45585005900410051100f0b0408802c214100d800107000c41d83d545855200a00540e20038408a2103c2c24104003000206548a50345d80c0b80d4034604d0018007610309041c4c4800e42c4074400100b0400c1404207264000c1100c0030740301802ca00c001e40041d0590344540c0c55203040e501410240e00204400f144241d4040703041c20341e18070600110341107076901c13903d480c2c5181d94683d0b40c042142482c60140395100641c1e80414100824000c4004d900680c40d0717910b5003810320103840064414074103c1241c2c0481000d00e003a44400421554500010856540781c40d481d143c20008a120321800303892030742c01d02c90f140f807805422010290703010b400e407c1c2c0400000008a0220100d000d6403141454080251004000da03007025401190030900107404c2c03516007640e407446185801c0c1c03194011900604484200003480e9200050a405001c0440262a80c42e190131041c04e1180564081c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 735700260 1250 735699010 735699023
    0x307082a1e012105010f0605030f04030807020a050304030f0c0b0306150913020d09030f08040b0a0f0219080609090106030213050709030f050d030606170a0b030f07170f0102070b04 79
    0x103100d080ba801043c0318540740e48414203400306091002e00b0700f4042c100a200d4504003140e200000300d80f16002d0b20036030f84203481c51009215140e5480e1030803038000e0000703030111040d409400c40301004502c080c001480514040e49194202129906d8840800041079202c12039a040c1407007408a144c0c0c40046554602400f024041c0d00c80382420300060a08000c91502c1c42018400a8030501ca0900c58011000c150f0203a00c0380680507a011206440350030003283c1c000e02c0c0c40c48100020b0b403251160382c803542c9243c40d0700000500349000441254080c2e91051260408208800200081d03441c1c598105648080004001c3c800180340d640030800e4a9114105401c4454907035001681840c07040380c14500440c0c002040e05500c07185030402d541c440c0449042c0c0c2001070306010b00840d18901900881b6802682001c204403076588610130f4000070a8901803540e450b000300e129121180b0405c004180207464094140000ca041c090030141c502480002c041c59641d005000c50303400325940e1400a07601a82150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 735701510 1250 735700260 735700309
    0x2090402060d0f051005030a080a08100329070207140103090f0c0b0a0e0904020907110a08030c0a0e04090321110714010e060405101a0307082a 63
    0x40041c105004600007140318915265083c070001886070000e50043d4004543e600c2d240f80c41e203080c55142e0251b000b01030401c65082000a00c01842015a150f02000c3c0307404050200d5140da990b402600307048101c11103c07581d001c5210800781201f03804250000c480780000c014051400303003240c0c50b00f50031821143c14196541c4e124014448000d05c0f001c250b0f0380c003240311581151121b942494a410144003000020b40480ca91740716404e22410303040c05190004c04410056582d4042100c24083e80c031b813040d0281c041d00f001100010500c01c040c500a050301d01e0455111521110010821013000d50410301c120706000e02400800c1d00301c49003801d00d06a002c0c24048406024003920054a42c0c00c02e2540c0c11b1600060380400c0c014845080c2c0403a0312940d0091180e14001802c135a03850700d069502a203a9004814200030002a40d8000628101c2e58059003031200c1c00ca000103400e04001d0340c440102a009000010411082000600c00940380311040590140d0702c01e02207400001140da1503ea41b240340c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 735702760 1250 735701510 735701513
    0xf0301051801081e070f0603020a14030405060112080d0504050606151305010e0102030c07120c09090b0a1a0a0b071208070804230307030e1002010606050f070c050907020d020d0318020904 82
    0x60184002034106c07040490f64203603580c44010000e5103d40001c50014a010543c6079001c0032200031a40225003050040007281d0171b04e403a80078250080383c0c00321103510081000101d001030a000d6103201d20300510142c0400c1c40d0104c00e010021143c07031080c08460404002c0c0c6a02000d503914100240c07842031810881440f14800140e00e1481504140c0050b48100c01000a410340b070042c10f030514a104030801071800d41c0c0c0306101350035150308103001002201c2c4500000c2c000240d0342c5c0030850081444080c0c4941071648804105d00b04440d03000000030300000074118062111924410441201da490615028585058000d00c080d0018000604c2c408800050400220b8115440c80d030005106003601e655030507074a00a40150b41c3e207004540510b100e91a1003d01500612a20301201e9a070784600d4030348141800b10034141c0c1e200c00b40441e2031081003000400c00303072140116144105440d4004203c1e813100c4a0380a480c00060040a208140c2821031858055140b1048400e0580c0d069031243e0071500c89 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 735704010 1250 735702760 735702763
    0xc09090c1a0a030b0a0506221203090e060f03061302010c0b0f10050402180409021507080a170112021002100f0618060b041505040b0f0301051801081e 66
    0x694000300c1000030801c0100602072903074000b051841c16030340303081010030154400d00229001500c541948820203111940c0d00c2803040c400000c40c0c2c0c0c06003111074207861315501c2980d0940c40c00c030070980004504104c1401070f280b160a683d5000541220301780a100c40c028006582c445004004400c4004004246411a4050401038560700da00030480c1100340384c0010707100070120080340c1c0c0300c0e0b41d03540c40400007445090900c00c94034142c0380d50444030345100d240400d01010b0300d203a43d400c0341c004958065402a07505c0000191106038801c1c0d08007079031140c0406008025178040c0c141c3c5940c2e840b03040010448209481d10709044940c0c1a03c0c1801422542c040983c205508022050049400c014500b107200381958801c905070385000150f1161180d01c03945100884096000781d41b4000d01c00c000078460b080600c003120001c1c84041c03511314a001d4903260304ca24260000b0f030040c0816800400180821324262407544414042e48460000b04e45c54400032a69882e41018145050f10038203207900c008920 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 735705260 1250 735704010 735704033
    0x618010b030a0f02030607090f0b0f0409060801020703090801051608040f020405183c03130e040c150e0f0301141825060305060d02191a070c0909 64
    0x3010b4501440d80d505049041000200c0100e00c240100800100c400c1d0149201c0020303501900100d0143c2070801941c1c904980c84050180d00401c0144030020707889500e800f4a902806072040056141c072800e15014185c0442030300140c0442c0d06000030007881008860316500030000c1440c00c0202d5451740c0c107280b688510003c2c000b0750013030b0504042200b0100c1598030030100030218800c40e0b100c00724035911003500030301c84034020380c2003503101460f5000700c0c40c19002200c10b144404281c13482d201e074484403143e4900040c0c0c0900d805e4480c24041200344403112500f50000c00c40103205020200319084010210f000003040790388030380b11043c54036100b510254451031510085042440841c00c28441d1880031f0100e28201c0b030014803656010341682c510003139062100c509080349001d5540d06010054010b03217002003c1c10741185040040754096070780c82c1c0000705101040c0303040350440da0814801074040d0025400040c3c40b0882000110006485032805000702c1c1e025132000190b5001070300d0012010103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 735706510 1250 735705260 735705281
    0xf060a080f0a0b0d300c0809280312091805150a060201020c0601060309020904080c010f050c090f0a050f0f0303092d0a06320f0d050c0c061801 63
    0xc503180c0040104017107040c1141e402c09a800e4021191030b000398504507802d500b140c00c0000260440080800030344420f01420344107400030a64845124580b2a030b2000711090150b0760740100340d014040060080d00c685003d5200c00c90314009000604140107545840c110301c0c12001c1040c1d4560005000c0f03903500300145100795006080c0c50585a130740c0c0009000c1e41051340c0c800828081c13170000040282c046e128145c061507000c0c240b8280c80c0d03103980750b003c404c1d044915180003554039040003406245a078800c047c82034040c0707501207880700d225506204d104500d4070000c5001d1200a84148140d40c1c800c0131008003400100d400b20b0740ca5801401013400d60041c00000c071b80000341d80c201c0c00c04000c800b40303410510b0302502400c00880c6000e032007003244000180c49010302081e028603508160300e40310300503113288480800505492401e03249000741c0507402661300345450040462903402d0f40105d0302601d0b4004601540c41030500d86500043c68403400c001c2e0950040fa401007446203481c1030290821186003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 735707760 1250 735706510 735706519
    0x406080f070c0519170403110105031003050109080a1e1d030f0a231b0405091f02040810020c030a030509160305060106080906070903020f0f03030f090f060a080f0a0b 73
    0x2a507130510007100c5001070004603140740800003da14180781005c16241200e822045840000400c030006503110750024044d4020f451180e5404808038609000b42440140702e00c1103283c0c0d9079441440245603068081c01301000c41c000a4600d46030070703070040e0204d400f10044101d00240345601d03400286040ca64030b030481601d01950148100b88016500c602014505540c102d00303183c030320194800d880720300322041d40c045191118ae450046080c9684007a5000440c60222684101c180c1c44803940d41585038601c2654030b40001301405210700c24040b041004211132825414965000b0040d61030340290300c503500c10960307600001182e0b81010881c02c0c402c0310700968a440741680780d0500c2511542e09004000110300301c41c0c045203101500066062041034a40c1d55070141c0340c190707401c2040034882c0e1808264022140f07044c40d0010b82d8248018907042400f242150b03940c100c07003010300a01d9030785500c0c41d6120300303030500c05228481c0e0403900003903111080c2403d41105564840880006210007504913800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 735709010 1250 735707760 735707773
    0x11030d050906180a0b0f040c09020c1c03090f1709090a0207020307152705060a170f07021c050f042916020409050124060f03020406080f070c05 63
    0x544000b10b000e81c012000792443ca001041c3d4415626602d80d45450b00400c018010400070722000031100840c1e801510912204560340c2d81d68501800340d0b04104a000710035041460500c854000304510220203540364181402864105d45801c3c90742d07405041d001d400d0081c6000030320004001402210740295005202000c142080c400d0380b0001d40107004128024455144c000c82c401952503c622100c7d400e0790303101d0090509071000c0700c640340450490050f1540c80071101180301d03a1040094540a1541c1da0f43d810b541c0c0750007069094035540a000842c5072403181c0f040c00320003680030070112102012015400c16151110000f02e4061103800c800d80f41000c00490007195110110f51026441044d500c540c00380c00754420b80d1000daa1140c5160a20140940c403009401414030344c0240510074052000042ca000226107140c640d40d101c0c8007085100514000d040c4032041c1c0280504498038090301d030131401e040c24080d000c0c0c96140c024006404444d4880005110f444c8240e10b000c28a40d40201034500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 735710260 1250 735709010 735709021
    0xf1515031302040518100605060307030e160603020d1b0e0603040f0b1303180612090614040c17010c090509190f0519140105010f091d01180b1011030d05 67
    0x1100b85550106540c021070140c24151b174014024041600c6000384a00d185840b4560141c0c024207401501102c02d0107100300c441201007842e400f10004200036140540e846c0c0b50b0030040421035100000142e41c581e00c03249045109a804440945a00015141107030fa907162400e1120240860400c000c2c0140703099020040900c80c801007011040348030b40c859107100182c2c40c0300c2e0700d201d0580303010740000544942d811079000891600440015030041d5000681c0906000c03e500c4a40c0c2c1c100c030296048540000c04004c128910552050040043c030000c2040c034400300001080c801c4148203ea1050b0860000705004000a50484c5001e140080040204000000d070003400340c581203a01110141000300b00c6090069175014201c040012028a00c500d42c0c00d200043d00c03441c0d082d440403801c11a0745a40818070503182c442d5412414481002800603600d07000b07410300f40060140c030910116003000150130250715455040000d8402c5800c08a2160a4100c4014903500901841c403040d24103007001c1c400c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 735711510 1250 735710260 735710281
    0x601031509020f1201090506030a02101407110f0a2108040503010c03060f0503070503030301090c140703032016030c03020f100902090105030105071409010302190203030f15150313020405 82
    0x48001c14144c81c0390b94030b81e40c40403814122036040328440d4054000d4096000149800b48050302602414102541c0108801d1650b219940004400300c1d101021119903101030324000c2c0003007080001c103c030200051410a8001e40a01c0c030b201700840710074020080703030504018941e41550050322015000308100c1901c0c10307004026124622030b0a000e00b081c4c042c01708680c10080381d01401e40d18043c000b181b40d80d281024605c0240b00c07120485007000303040c81651241d1502c2000030306045000e5600803030380d5100c02003001c5402c080b076010380800352420400010000701c1a14143d15294160814002c401060b00b41a801c2c0002c0442010390307801155030801e0105030903404941520f0096030302d1510f0760b032145c05242c221402510b0200205d44a0500c01c00040d83d11001802000018580541030022420404079a01e1000d29641c016802c04010864202c0b429001658402030241d5143c01c040a500c000c00e110b44903031044d40e540800c000002800c0c9040d540d0086a075254090020001403a1105c03032017 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 735712760 1250 735711510 735711517
    0x304020907051611040b060f120a0504020f090702010609020412030e040e06041719080114011706010c060b1503011a0a020607210e0d090515030601031509020f 70
    0x1244141500000316400601c110191008104101240204002d003915095440c440c0480c2e291750207500c82d2241d03945030b100c0d0000703401c2d644194850643c4403440c00c0346001e00180001c0c8030140c1c0928000821003da038070203450400c034040950b5449083d85808100324050603d40c0c0084201d03500004000a0f107850100e4072290f10750003035807021003541c0d00b04104030a0f140804109802c5601c00400b050100c3d4180280d10917041c4000d040516041f4044590407501c0b000e0701c00c61000c914510010020586d12410003039105009190001c03504841403c08602c021001e04824100107148440e4020080194040040c12030700034a466641d00d6404000c0070581c1c4240180154400c82010707030120000a42c0a03120480c049402503c11940d0700001200c0e02800c1480c0850340c3d0503504820b0342c52504510403002ca005413680030302824414228043c045004076070025008040b14505403134070400240c15660084d00c00d01e404140e42c10303603030340c28130807488940c020940c060310000d00d5030f000e0b03503112006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 735714010 1250 735712760 735712763
    0x1206020d052406041211011205040303050f0c0304170903030f07050703031b152a081b040608010b0c0a0b07080601031d100c0923031b0d080702060d0207080304 70
    0x4420021040c001400f285000b24403c020f40503400785460000210300400c0c036000510706142c60000e291002c20184240c4001f601c058004c0b0b0798039000d1002d0b81900d583c1855106c9640c915443c0f8508165650030b01440d000d144800709084081182800c6c0d07034042c01214010407080004903210301c498180f10346c0b41d80e2540310481c042751460075005a221041100e440d0702d55002000041540170032030b515000b8016120380d84403032031420161b804501c0700c0076244400d055583c0e5a6810b0b90308d0560711580c0c0986041c0c1c1c1c1690029014030041100c076901071002815103281c4960180c440b501d15590b1451b00c0b03241180200302d810004200003120354440b60091041e102641c4c00e004100d0300858440c00c020114403042142c1d08620320581070806035400555551220385800b5403603a84e81c4c01050843e64604601c1d104070459001c0101442c5002c0003124209100341c0803a98032003682c2c20000d10051620b200083c01e900003c1502d03400d42d0707a0350007034402404120100355038400d114a81a910342e40b08680 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 735715260 1250 735714010 735714061
    0x60f08060f010603090c180b13020d1a030304030f0c090e0f061003021c3002120a020706080a110406030501081b010e01110a1e05060a0905071206020d05 67
    0x10b840d03100f0f000e400005c1d031308001d2150301d503030034400301c3d94200a00d20007142d05e0035100e81d0504a180c413078402c0354940300116074005884840f502044000d680360f0302d50744440c5140282180b104c0d03a901000720b500b00c1b54030100d01527108801c0d10304011214516807011a186180c01c00c080c0380314101185040414071180d080d00c2e12582c3e80381c68440d90109a0101a40000101100341c1c0154241c0031140c00c01400781d240c0420140048252542810fa0600e50390a6991401103c00444d81c04100000415281882c0c0d58140000d501300250307107003000c2c420351081005040108074010f501d9030065100c40c240d2440d455541c1d41311030000c0c019002c00c0c4245100c03803182c00c0d80031060180c09103111151900503941d42c501c141e80c0c0001140d07404060100d0440c18064110620000f404680d119004420003540740741d88403400d410309608085000741102030f118200019000042e20118079031040c0c46c01c4040d107405d0040c0301c0c24140000c0c0980e80828025070325003000d120803000703804c041221440350602d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 735716510 1250 735715260 735715291
    0x5010302030d140a0f0c05010c030608010b0909100b12070e1e100e1504052a040b1204030e040c0206010906060f020316080712090504060501140d0c03060f0806 70
    0x4070845801102d43c10364200180103010a20010303102e680780401e5a0400d02c1d122a82c0709040e21001e003160144c00e40311001c2540c95000304008007080c0542050184100d03040106403508040b0780c1e40742c4407502115041c03580c0e11032240d11a55280300c072004008a00c0b00440c1c1c1c10030f444801c02140102c0540320040c0c146008404c90101e103d464145520400001c05082c0701c1178a041900d0110460140c52030840300f00f00181d105d01500c0b1841420b202c1e0355074a1620b078090b4071901c0c611011100070340c8101a056020172042c04200a03400403103061400c408401c2076a41d0341d074201200c0404aa2200d680d0050514008590351a400500c407030680d0302a150400a0b1545c5030300549101e01d403021020003580040c4190b502840800d0800d102c1c090054040d14030300081c0f9600d8182c0c29210000c5000450f10200301070104c0d0900348511400303002c0c28200707280940f9445100495600429035100921516a0803000c0c2c0240b080c0c100500a241c1c41c60b6900029440368800c1d600c030700003107031100c0d000360588 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 735717760 1250 735716510 735716533
    0x14010206150f04110d0905010b1c02090723070b07031a0a0b130b040e040516030804090203040f02030105011401030e0c0d08130f0906031e1713080f010501030203 71
    0x12507041d140c610040912241082031001d21020341030605040c00c46420502101a030300c0b540340111000548100300001e881081d600c00c200840f1442d070107150301103c0c1140c491005803940c2044940104981c100116420010b20001c802280c218100e0102d080020034441d04200da1103240d103010f1009138405114480a080c1089030116801d008998404080b00040200240c0708000740100116030f01e200c05025201c0c001046668411342c0440e0038086044100000c0c42000d10000502c140c1500d00505020700d540c88030b0a0602036406800c18490f800404542040056203443d003440780e002d0300900503581d40b0800011001d900040305804603042c280311100209010a0810b0b40490003007400d4540403c030f440d411410740048141c043e6000008c0c00210741c1e0400880c00350001e0030780c2140411541e085142140480c00c03408210b4544042603942e01c03000583c080b04c0d41d8981c1d0451400c0303988404454108140c81c2c0c41e9644100d0403401844a8284140c00640015050360f00980c00c50380c0d003c43c5c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 735719010 1250 735717760 735717781
    0xe0106030506091b0f09090f07080903070b150f090f01090b09040b01030609260d06140f01050c01020403021e0907050c0d180e130303060605090a090c0207030b0114010206 75
    0x212211100384c6410545608903034800800340200404000c08542480300807804a244140155008802a1000b60030403d41d90b601004517680105241c01440c1020455500c1e00141c1002804004c0c0f040140b00801000c0e440d13280940f5142c1d0f1009086030680c7c10414005007801200b8051420001d0030040d0b8007499080008041e0f00403940024400101c2e803960320b9180013001100030840700d83c00f002c0e2805114100340c007881d01c180c109034100d0b01c0c1d40d800c0e08a80c8104460a0b980004001c10050340821101c0c1d40e00f0803843c40046007030810f0340d5200041d110031030085c4603e4000950140e02c0040d011907101411341d400720191002d46180d0080d450310312080e02c0e035004803500810154071514448600d24070a0300171180100703403c0e030880c06050b01c0f14512454040115500e8004200c03007182c92080c5907040c002d0307000510b40740c18014a4008004049070395001540100c400716901d03100510b03841e40c42000b09000660300030702898170b1035840b00001d905141207203034030798010b100310702c04a10540030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 735720260 1250 735719010 735719029
    0x30506030d020c0906012007080c0a0501020a141f0f1103010f0b09040b090903090117010b0f1b0703050a0605010b030606030a1a031b1203040f18150e0106030506 71
    0x1c05400030203a0a025004001c03080c04020800c0e41040900a03038203140b001407007014440908054003406100d420700b040d0a24150490601520446402c0c008010380d90300802c180300d21942144600e01e0114000359140d1808140398185c4408910703800c40394810342c105501c41c0f0401c0010b60750500c20003c0031050440640030078000c66040034a01ca10805c6030840403130060200e928080d1001c10480c201c880000c440c20403c4070341003200e400001c1c0c000d50544c0c1c0300c07509100100c240030081c0565410101010802d0141400b41e1485c3c800008828105200d811481041e640002040380d40c0d51341c80e40381c55510760100e148221f51040c24040085800c42408042c1c2c7c0c491034000c4c100382e05640c0c034181247e0142030754000d0f10303200a18075107000703036240c038184069500402a010501d240103111000c1c460002c00791901a0307550b400500c010f016a201e0f064041c0301321142e6000740c41c12140c000040302d0003888940c0d03125403c2039100c1000207440006010b0203040b580b05440402003980c030318044c444140b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 735721510 1250 735720260 735720283
    0x1603090b03090c0d030309060903080a050f09031905090a0b070201090806280b03010c030608070905010b0901180b0c0a0b0c19050f070212060f28051509150103050603 73
    0x1c00c03d4142c540c03103040510344e030000640246804034280040762079000c112500a0303415030005039440104003c0302d5203801000d410070f011001e0000240b900c040c0007500c0b409030840d010b0700400d054a04491480c4134009940400d40000c00d4502103503628080362406074003280c0100d000c103035043d40004a440c0e000c580544516202080f180b1078901d04542002080304503a521a0b20725621484104143c500f4402d0080c031a0315900c0c00540c89080c01d501d035141080a501888115042400500070400303024141c1d041018203080402950045141c2c601d00e040c0183c01c460040c0c02c02058400000e14000f80403420b030741c02907035076501070f4440510003589480784000d007003003058800024145080c8500300510103194010b22a0f4205000d590028070800400d011002030b40e8001c0c028410500c501d461000d4010000c4426980030350544c183c121039030b1603c0384c900d803031240d581ca0004811001001c00341d00c00480c000d020007280d2030b20307201e07806405030300700c00d940c1c000303442c00c00007480d5405c00003141020807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 735722760 1250 735721510 735721513
    0x2180103051c0806130609020a09080705040b13020706091514070e0f10031e092a14130c05070c1a0d0510320103060b040611010b03031603090b0309 65
    0x6558000500a03010321701d4040a8400b540c540c00007550411500c040c04150400d507481c1e1000d04c0c41c03c4103440c54014650804c1e40302d2454400c0f010b680d55150303403e03901d0901d412640541c5496050a04a00802d0a040068121144d000503080480c1d4207138044031384480000d52000a507140c0c014220740d080b18403101075401002c1d42c44024440e151429604090401610b000b1400f001148005440140103e5001442e01d44071b100e1101041070180c40d100200d40720f40400308013106082c0305103645001038400c0807c0c04420050b045481e0312240020001c2030100c900c1403190898064006245900007842910b2101310394001007a00051400b28940040110000d107050000c1c00301c0c45002400040c040740d070407071880c203000a401210351140518290b05c1228205074000ca400d142044c40000e45601410546031034824003024040e08151015181e544c40c11700002909200320500420f0301116442c2c0c9488081052881c13005d40c980d04c4030b2501c1c03003a44c0e415079666542002000500060740c07820501d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 735724010 1250 735722760 735722777
    0x21e0a020a06030b24093f0a0503160b0f0105030d0e030708060f01080d0c0c0b09010507170c010612021008041e060f0b0d030c081602180103051c 64
    0x40380300f034102c1004c0c00307002083e101d2440b020140d0241045428000c01d841c6000215803080c09291802181e1500c80346001141052900003a0140050a000343d449100308085140006030240801100318181d910008482d5540312a0807151580c1c003580408849151304000025600c07203400150364100c61010303008024060403880155000001071480a03018405e072007001681000822540d0b0090003010604174495040c510003d052031245000502800072180302c00000034403038070400040760b104404107504c80e1006c0004a55610400c0409010303020000c40c40c0e0209d82c1c07010000c010004405000700141a61007008841908010a0103503000b110001406415401403401300e40c80780c82500d07220520300c1d042240048410b40d103441031b030389241e13034281c00e115506262003040356a1400f12a4501440d0503503400402d034201c0c102000740502004101e0b03896040c06100c2188800743d00030403140002c0203440312079406900900c001e45803403040103240480c1c4141d041150b00c2d10801e40d070b0762112 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 735725260 1250 735724010 735724019
    0x1401030b03100e2406030c01181509080313090e0106061b0302070e04050606100c0506151203070503031504050c180d080d0902180705092101050403021e0a020a 70
    0x4202c9214099001d014101e2154640b140002c0c2644d0345034401c2010325403904110003458544690310080a045c844082442c01a5150f42174030f9400b01c4007041d00c00303510708a0082044502068036440100b0600c004121030210403c4500940305540700703e0410440311440030841030a0b6101c42c400da40202d413000c0b502c0806051000d0b011040213000b4011504040da4417007500c5050001203d00380d442e604107006000b200c0c64202c401d615035072814684484c62150ba0b031200c40d00d0300d90151094926421000e80c901d25901c48420703c201020514007a241c81d4142c80c2081d030344070b510894100382201c280c18040001454203115284c000d19200c03a416041c403002c01200841e680140c03003c070354030101085d80200000e2840c00107010201010402017080e1403103105002803894070100003608042000e003044042e650020a980c042c2c601103c8890340400904900b1081900750406008194200000c000c20300d80c0010b50202842c5024411901c40c45403075120513100c0c00481c0c0001e601c0389840c1001c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 735726510 1250 735725260 735725293
    0x2120f180a0509070c12170f0406200a03060b040819050106091803030b1e0f01050c100615030b010912020609100f0f020604020f24030a02041401030b03 67
    0x624440d001d80a801001d0321500040d010a00444180c0000340c5018503060030800181d581410100003030801c040c0e8030002055254021a00800803c51407078008001001d00000d6004964280d05c031030450b40d110314010700b802c4000ea00001c1071030003007400e1800c0082c8008146088400301c1c0c003048003402c8180007125252911035040182130301e02d5900e80d403000c01c000e0302c20f105004840700b0b808005000e540e070385d15015058072440c2c81054030a5401140030b11881c68900041c0410b090112400501000000010783e000d001d0900520080c1c0305400784030380b0075005c80d400842540d10401559240c095001e008405950001c0c4d0f42070300050b401c100401000030301e542154070362803000301040d08140c2144041030706d0340401039a910001d104500c1c5c00c100280c00c80b403006141744035403000d00820b181680106850951004580e80035580541c2902c603014488821100700c0c210440701ca6542c1d0420314002c5001e03420074020b00c00c80c250314907103004032503010741304d0320148250180281282040e05200c0a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 735727760 1250 735726510 735726547
    0x7080d0507051c0201060515180603100e160206090a050703080f07060e070e0106090f03150207020303070b0f0105060a1710090221092b120504030c0302120f 69
    0xc0300c070b40c85510342804103e10341c84100080707032029900006074036103040c04000030f80e070000e259200390b40410010320030000c8032a654403d00e079805540f42c1d50b1740e440d48842e00d46190080d80c04100c40d40c0d05003080c800c2c0c42035a460210740d2a00b44e41d084601c65154100d0868860421410040c42c59021210420020310100080c104100c8524800c0d410180c454503803000740c8515030203415640d00402c1c0c060080c400b42500e52070140c6a18500aa00740341810700c507580c81c04c2c2c1400060202e00c1d0b03052402070408842d40440d1000c65001d000d498407171090741340108040d98113550b410014403140c400420103040000980b840c4003481d0781e80d03140024144480d0304070070b9409401802810313541503010850003030900081901c031022a180c3c4011111884c4000002c48016201081030f40100404103000ba2001e4880700049003503410021350940c074100160740000c88070100d1041282800100000e15130040c03640350409020341c0940d8000c6055800b038860038030410114150189080c4854501e02d0340a0713103a03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 735729010 1250 735727760 735727763
    0x708131d0a0c020705060c030c0609010c02030a050705070f0f0602010b0d0f020f0d0b1005090603030903030405012a0f0203010b0109030b070c1401050108062d01061215030303020a09060207080d0507 87
    0x51300c1801d902c5601140032940000c40303010459200060710800301400300021075214203c18020080303040d00c0c03000203441e0312a210004040010100e41c89091000901c60400203101e40b0441407031559640d0300d145c01310f45017403041c003004d135203002520801818419620030718250b001c41801c14041d00d0b5400c2140060414480e1604044141003180002c4c8038408900d014503405084200311a01e40000c01180d0b9500a1045009400c203000d01012920b00109490564400342010318050502c034512090300c0805005003106500103510100c03e100001e4413440710180207170024006801c4950066030070003000e10005103440070340000510101d219002418030b151242232044d220420710156603007515800c0c0c000d101c0715000701d010700c1811550640c8040c0c0703030b04682500c001160780111050794003000501c01c0d5402d2200a000c0b00846801c0f41e0700500341d510702c650f04410f1071512420024003c2d00041c0c18040480d0140c42d0209104c0d000050405c119040c0c00d000f45940702400904603070a4009071b20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 735730260 1250 735729010 735729013
    0x30706080c190c17030907172e06090911010815060a02030d020415080702150f04230a1103011418010b0a0602030706050114030604060c140708131d0a0c02 68
    0x20003000200c01c3c3e0381030384d0140022490f468a90408050050038202141e001d0685c018101ca0b1000c410748010620720308290900020b5400f140c4d160200400c000d0681064001c03044c50201c021801007540ea01c000d03103803802400b01c0c20f0b8100d041001074610400660f8002c03864900f8600170a07903490420020030311101188150f9042c100b0340e1413100180d030042e030424008a0031300030b40b115406900c200340c140d0040047c8010f0001024406138a100a4800351200f40300d0441e000005041c40040d14400c000e07010b882c540c00643c505d4a01000340c94600580040303400c1140302055003c2c0349014050001c0c4502024004806911944404404420000c09240c22552902d0802d031195440d0000b403c02411550061036441c210b600d46002101c0058002200c8204200b8400c4025200051041d81c0230358401400955600001c03001d464510051028070300f82500040d203401000050405844551f4110030020310301038541c00602c0c1c503081a60f0a60342d5405600700029090016600000840d40d807600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 735731510 1250 735730260 735730277
    0x10302010c0b0c041d1801020f031b19021b0105090f060706090605011205010e03041a03070903050d0513230114041802180d021003020f04090501080c030706080c19 72
    0x40025405a07604031172119804c44000c104829486100159204501400b00071464141c1d143c00000031808007420035240d90945100b50902c0355802030480360301841d1b411227070b0304140001d440207507140c0c1c0c000900225144880000641540107a00769001c01c04020001150042c04c0002c0c00040c1e00003144c00c3d107555448003021f1011440500c11103028101039408500300c01c20600b003c5007555a0f14412515aa1081104100c0010b5244071184d8150304242080d82d01c0c0c4405008a501040a80019019000e8941045e20f0f032031f0004014074004492618510701d49650f00301d403040c1c901800408000a80c2d024801120a61084455051000e20300100310b04160311b6408400c107041c0340605840a0726400691080ca08004c0c8809440c603080444202000c40b0256010450a40d8114442c4007031540120300c403002d01d03111600b5a0041c0c00807060800266a4030310225540d24501c140309800380c09448800315129102c2c80c50184502c4602026610300414202c1c60114441000c2807001000100c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 735732760 1250 735731510 735731519
    0x915010504090f02030f07140301050d02030a020306010906050f040e10020c070b07060b040b040b030c06031e040b07030c090b07150e031305210c1c12090306050609010302010c0b0c04 80
    0x14403d056100400e40310050b01c0749001000c0c0030780040064000c0d0300f440001e8031400284800501281c1c150380096400001981d110b1021038582180c0b1500258580a04000450700784c3c5150700c0b4004854040b00e9107441440000240b004071a014011001150415504000178a40d2500100340c41400c0c981160301442c3e03a5500b50a07940c00001c000c40300c540c1c603100051014501400764041109089900308450300e521400290740d07101d0f0200e0700303008003000f20000d15484491401c0c0d024422041c0d04443d83ca181519090a031400200c585001185c07800e00740240f990f1041c074009041c0d13080c408006140070201e448400030064245444400b0b039441c0c030660040c001c3c042c0b01602544284100280402d400c000030803244081084400700350480b00525143c01c800009400c904400040e80c844400350b4100d4002c0660b428190030141a040360002c00a840aa004c403100c000c490003040200600d486480802c49181402c0c4000381c000b4203401d844d207004c01c0c1040b6285420210740c804487c03505684 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 735734010 1250 735732760 735732779
    0x1b030e030703030f0206151804210201020304050d030e07180603060c0c110102030a09181401030308160804021f0314090a02180c0720090f04060e0703020915010504 72
    0xe03007040f00084d44206034142c5440d01081040d40003140038421003900c404580100e03146210400c8480014000b18002c14180105100c0f00d00e4a100b0700a24000952102c0c10003038081d60054901712880c4c4900c404089080d0b02c2031140c01001c0982401800c1d0b41440c2440c020300102c41505030341d1070706960b800b000000aa02e44220b4001d0394a644412014882a051507000c0040c40b1482e1030564000300420010307107911036411000e685040519111041100c50754070020080c0f8a0b025410400c000d001105140c0c104204a10035060044c800d04000c85180c001c03607419109890003504482d46441e504400120403001e03010b640071504d40011101c2da00d5480080e82230f016074103c00070381c024400075025401c0c02421508003107003030360001c1e009040030380f0301012900c1284000b40001c0c41d0341c44040740103103021a0b0089200e070000c104000070704050585280c0d440d01501c0484515103002c040d0a0b5103c00468501c0840381c000741450901c2d5a000c0c550113040100840d40d9041001c10040400d00c1141c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 735735260 1250 735734010 735734023
    0x901290711030c0a060e1c06090f022403010e1510050d150b04050f1309300c080901032307080f0124171305100b011b030e03 55
    0x8500c84004150301e201458240812803031018064500c83c541809661b4000640c605441c0e0141d035420240204042c4819055a82140003065542404144414403609420121801e4021101103803034060b565a1144105a0070f005120451814801004600600030700359500242c0f0900709401c3d10001c2001851030803485a44c540419030108945440381d2031072051000b495001421a5141402d001301c81c01240143c0c80750a2103803080345030394240350311a4120408100803541c0c062002c03190303034900030202e400404103000c20b03003600f0314516969016552104d01400702640321003010300f0309078880c030344542d010301d210302e0525485406100d02c104003072103c1c24048035950903041d840d08140c44020143c40f8060b00120120b528040140002e4542000e13400d00a11130051002d03840c8041201642c9400100099412004041e002c020300300001e0101c51482600c9803068070b515040c01c41401089034a2101c005000507001507502610550301c001c5400894020b05100301d0b5000d003000024901070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 735736510 1250 735735260 735735263
    0xf0a0312090b070809010c091d09030f1c0b010905060a14040503030c0313060f12020a180315060b130e040203010b090c07030e090601173c01120209012907 68
    0xa00310405c1221a6000f803041c103a588030301e46000d01748a0301e4400c2082c5421443c400c002040001c1070301050b0b1070f020130400c6034140c03c020030391648c4490309000f056182421160390042c05c02d00b050900d010543c4616114000d44800404150030514007810441d482001d0750092103038154100000300d1156820000740640700300c03100083d66176407e80c0002c40305403000c030b0788500180f0003e01e0746030098a8000103220084131109c04010b13220703072000ca01101c811420350b050b0061400d90764404001c0c401c4031380042d2000c0f140301d4418810680d80d144c11071002d04c14042c1c0304100719100801803201c103607c80580e0340c10070300007000403607100130103000202d82141c207941410701d066000410008054110300861441d843c00c4440c2012071801e0740002c0c205111220452403003c0303402c4001480300b00f0400700280e0742c0600280100b10034a020031001c001c07401e000003c5403454491400041c682140c400030351a21940070707018413101d0746040390b025100c078402c060769080c48550305002c042c48a4008042e00245 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 735737760 1250 735736510 735736517
    0x3020304031110061a03010b0a080907090c0f02060f1005010e04090c0902090a080a02030c2107090609151a0c070e090a020103060909051c090b0c100605030f0a0312090b07 75
    0x15440d00b407a80071144110551030380c5c100d40600040008950590641c2d02c0d812290030052819070765904041d0070204141c100040c153320703240704c04080c0c55121040e104682c01e1602100c0080d100c1c456041400802101d803000358941160b018000c43d4071501006c013080c1400361002c24071749100c1d035848200189a40156000d10390110305882c840c82e002507814001d05202c000f0f007203001090f4010035105c02d0361001d6140a10002101c00201c042c02102a1084105690681d011180c445010001503c094070410074960700380000301d905556403030201000c0344d048480482640b8841184013202d80c000b040019194020b400001440300401e5884500c91203170700c4c026141c00701880c07002600321069a040023034042c0c50074100070005140020824030618410095a160141000045403a007405030044840c54002088158512100140319800c46850040a06c5070540741c00038555903844064807800c032a0302c1400820701007030194949542c01c000c800400f00e444034541d112800701400c183d5220000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 735739010 1250 735737760 735737771
    0x2d01050a09020406120f061107050109030c0311150112210f080c03040b040f0c1206050406141303050f070f05031903150e09030c0601080a0c051f03020304031110 71
    0xc61425100c0c100107003044d00c1c2d017143e0700340b0700d0307110104141070a24004100079035814503100d0707201e00541640c1103140e00c60300a000e90202c5250050550f03404180840200e49a100c02d03184030b034030200d140c071004080a640000703268a8071908030040500d041040d958107111410814800710414180c0054200741d403034035200400c800800410012b001032414815200510a0100180e09694800d800a8202c0c401d00c0790030826090661b0751040c135600200310004a00503070820007500d5007105200d2405180e0410600302103440d0800c11890456910301712510301d40f03070030001174041e40240010320282c2c1e1001e8207120701640e4101365059003c0007501c0d00d50021601c40782c0108036844c0d14201505600d414442300d20102c0c078031a00e59044e8007604a12440c004001446207908000f40c0e0b040c1c0055808807801542c0d03070281140c0b03806e00241d0940d00840b1010000c01c6604100c1500c07581c011904445080e00349074600b04400070b4002070000c078100540d514101c190b0349020055402090b4014900195 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 735740260 1250 735739010 735739013
    0xb060c060906040b090105130602090406050303040f090b0f0d02010c030903050a200114090f0d2109090b180705070c030c09060821070c030c0320040203092d01050a09 73
    0x40313000020300c10f805580c1040d0401510000d00030319501d842c0d0b8005000750b00c5100220014003c1c00b03040e0001a0180b10204002400d85d0f01c11039884101e8090700303020044404142c040c0041c1c06e210300310151300071801c04461001948541b8200002c4da01074907240c800c1c10740b80d9403224240511458241c1d005480c04882440c0c2100d105c410741315040d0309003060306841000d43c03a403071841d024900c2040e00c220110b20301e40c141030303c0300224400010b070f22000c1c0b04203201c400c5054010540c03c4a9030170740040c90240f40415802c03150f100d2410800001041188a10010320710100c440000911302c504201e014810600000c00b40d00400c005148100e4244560074200008201280c5840e444451294001c0200341032000c0078002ca00505110302c00500c0d036030880303820510b560384000c2d84020310450321500004280649500c4c0003d13003030401c7d0307441710190480380104000c1c0d0200780c1e103407a0660484180f845000e0000150701202d20b040070081d03c01180048542400c40b5402c032003d020b119283c001140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 735741510 1250 735740260 735740273
    0x301061803140a11180103022403090106030b2d220c080d05070b0115030902150304022d0904060b0a03030e0310050405120a020312010303020c0915130b060c06090604 73
    0x1321009020350f6502020035030181d850b09840340c10721010b40188078440c501c000d056941c44c0401090107181140c550b40303003084c0b134003a4001c0c810b92000391406005507012400020000c0043c0e000800c200b031038603058203000c1d0320802198801400c00c040300ea0b0044007007003044102288a8a51601031b1341c8200c0e00600c0c01e02103504040c03000d21007400700101080364034001207000d0042c40c15100351b0b40354881004c4040200b03800920301100080c1d4040482c040c00c01d401005040198800d901c01c1c1c420500c401c180351000c404084e512441105101a000c0625086007407440c0025840350050384042050380c42400801c0d87c40030745401c1030f000190740403482201c60400f040340643ca0500050200803600c0c1907102c45403100315601900300c00c1c020000714014403503c20000d8075542000d903180101c16594074038000c0c0d03583c03000b094000e005080d5500010205601016441c0c02c6003c05800b008034103100301170740300c02003100792107090340706100f80281c1c08c20b0700081244078032502d68807004110504207420042e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 735742760 1250 735741510 735741533
    0x605090f01050105012f06130501360f0c17010e0309062502130b130915020901051309020a2a0f02040f1418010207080301061803140a 59
    0x103451903070402c40100107690344814584074030765403008040740b00820700015021400c07410b03e218015200d41e000380001c07016011814468188a03038020441c0c03030480c1885038040002a92804401007409608200c174070161680100c41e14841c00d007220203080207a03202c081d004480c0e0008546610011000c001803a001d02c00d00355400345c0708008509114a80000584510640360b0610f203603e40704c0052201840182440c4030111750040c084001e07031421700f08000003001064141c620a104c1c0b9169074110050912691004c0c580041c4488681194100c0b50000b0754402c2c1d000b030341000380400c619844083c240203604050b290b010401b5a9a807000c0d2401442c03070840008020b810300e03894590240100e05c825207c1601c80d030141e841c1405514900001e001405d000445841d02d9007803951100041124500161003003200d4103100e0304202d6401c3c642c600300d000701e02004001e188100018890302c0c3c056107400004907550076668107100d0322640c460905210340d10407944641c1c803d0b40250f082116142a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 735744010 1250 735742760 735742783
    0x305030a110c0f060f07080304060516050c0601090213090e0d03050705030f06010f050c030703020c2d04150b040f050f090618070306080d080405100c09060311070b04060509 76
    0x18000d072a106000103103000500d40e0f4252103443d000503550b1401007040305507102260003480c0c2c41c0d200d00e00b1741040005040c08855084108a003402d030501e400b8041d00680b14800d071080b0003000141c0c01c1004e814000d5004050b1000c001c6100f007000903503010341d80182c819100600700038201e50365540d240941a19000b902c40c205003d0300f40b080100ca10200e212060f4424002d190100384000721140c1501d9a204041d503a410754000001d1800c1410f40000d07001c006950142d401e100301030308411400c40780750003030000c52030107103e0511642ca041c6010b40041c5c6a01001c2480000c00941e5007001c0c41150b4400d9014800d003e00c00002001030b841c2601d0080c03801c690031b030795a03103207490607100144819481140c18000801031101082001d8840d52101000e0704c2e540c0100d45400b41080d6018040b04002c840c112498403a00c81d000744001082d0003400b129840c552907400101c0e0038894198080c200500c40420396207028084030300445c000068083c09580682c90004403030900c021040e003810040ca21 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 735745260 1250 735744010 735744013
    0xb03030a020a1205130306140601020f070905041104060f08071d0c0a1e05041701060305070e040311060f1807080c061b070828020a0501030c0e0a0305030a11 69
    0x10241980120b08040425440354103d0110b400b0b03424161110301403040400240d404004000c001c1203541da000c9001010344000101140e1703a41001241c0e114000806074415400881d070801c89901c080d048141c00900c50426a983d0703910000108046038529800184843c1e1040820001c6503010300044015011007404010840c090490000040c100604540107000d00015824002031051109021000346444115070310700001c0d41c01000340d0000d0240c018000480200a100e480051041d441202c0d808400342070a40c0c40d010010140e20303c020000c0d414803100301b9008500321001e10485114084002c41c0c01d420f4205007405140d0003c14945070811a4004841071000c450005421010309200b1580c1c156a03141c000e00e01c2205507a00d0208074035130301c102d0502092003000440c202c030406510b682d0764500009042e8519808440000010b50860b8204400740190b5100380c008041501003401c04081c0ba40004002c500d411105034000d4449070000b084490403d58040350800c5c18a400302d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 735746510 1250 735745260 735745267
    0xa020a08160311040f0f0b18090d0c03050c060f10050d0302120d0e06041115041a13120b0106090b0c0c124201030f06091b06120b0303 59
    0x101440c40e01e005804083c00d0f014810840e200305948940000105e5049528107024031000c0c0d10308980030b008101d0315144101c0c0602e0782002030035040d44400d072181d44044010020807902200a1300c0300310244009908010b8100240c198a0508020040c010401c040041c495854008402c01078070b09250000c43c420300000c000d4002080e400036410501119103080c807a0744800c018802002040c03620b10000700c034044d0104010a2103440e8600d11041c0400b0b503100041c00b0408803000703506110320f0140b4070340340451070b8002c15481c001d50b026146a08103404030004880d01c603004014201f110905c100d8110307207944014803200ba4801d070300c0001041400c8146050541c90a08562100901a9020f0107a64005074255884804205464181704441001d66000f0011800100004942c0300f030410900045a40c0d00001400408818101d81e040201c001218070036a0310a0007a00c3d507000d09855279400c00346240303501000284020014801038031a0951031000c0d8405406440c1e90700786480c8250001d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 735747760 1250 735746510 735746533
    0xa0e0c030403140a020c1e15030108011802151e030f06041103070c170d06170f06040b010626070e030708120712050c030f07050606042f19020a020a08 66
    0x1907240407404c4211031400600b680c0902150100300214510323507010804580c0118009480f000540c10f0382d1a800003071040348032568180e1805829100000d41000b03140c40500700324100080a030800040d49010001240138880c0b01e84c0d0305801c2030b40d00c0646624410184602883c2c2446490548402100110b045113844c034800340800c820a1809840c030b01c0c4038005104503070001e03012942c044003165010801d083e151040840c0040283c40038500d01d00c00c2c1d1201189000c40015014400ca6104000c011180c1c244201100c1c052460640c206448248825510000340558007481c4141c006590303e0b40c030040e1000c2010300d440b10580c880c0c40039400100c0e0b5141c00d58501070450300072a03000080107089154098007210b40d4880c0e66110700c00c500020816481e0b035900740000b480c0b400d000e0811a43d042e200c2900308001c071341c009048a6880c400740c1c0680d6404002130700c5001d40c001840703020340781860003050205402c0070700c0c22203210060300080c6640d42185002201c12019028801c001d1412603c80c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 735749010 1250 735747760 735747763
    0xa11041d0d050d020f03010f29190512010605031905040b06010c0f17090a060305071d0409020604032117240d050607021c0203180a0e0c030403140a02 66
    0x10580104940020f4030020440250101e40a81c030010412955941c3e581908401e1160140204144d0702071035003502c40181091040b00f200381c2116141549000c245ca05501982c1040301313030390400d00c4002e2119141003110006043d00134004c980701c0e141c0e24980404502902c10950f885c1c2d49805140000b80404140d4100d41e465200c0f40a003056540c2c5552400c143e03c210b680440300a000841c41981c0481e8150414040c142c03a010658a04c83c404e80c942400341c0507501c044410340c0010b036072545c4c1c440003031059201d1000030302c40c0500b00055007409500441e40f268005d802c10f49809418035900710501086d50140c0082e035045284c00700700034103580c1030031040441c040c107085238000e655041d01c01155111020034100c500000c08412007900f403440c105486060807160a8003500414a104540c80003101585d604d81555901039850b00000d44200200620b00070a8103802640380358001c14103d6201c171034130b4050242c100d2656181e2a29180040c80c55101d210316521a80043c8040c4800640 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 735750260 1250 735749010 735749023
    0xe09030406090b03180717060a0c080f07030e101b080c0406050705010f020406030c0e010e03070b0304060b060f04090509030a0c1e0203011503020901080616050c03040302030a11041d 80
    0x541c83c0100e43e25201c0008944a181d464492402e05015076400045e07003448a100c9241030092607802d0710301d0351b9243e0082504036048528040c0200300c0a500081e80d8003400c280d49035205415050000358503180c1c400d80b86c030300b001405030795819a070754002d104200c480390708080044841380e04c1e04035014a002d14035181d03107001d84e00c64901400000300e0860100002034108424a4001c50340454a882d6501c20060103040094020008607003144040c5070f80b03510884640e00b4191000d0010285103142c9100d03400d142d800200301340c1d401552005508156507820008043e00e040516255490300e0030300c0f20b10403c40380701a10602a55104100c950308164020420b4040184c000780000068040410801119040600b0003585035180c55120801e5038100582c40302524000e40e00e400301c1e6a21040015030b146419a441e03034000b24090301c1440078510500050a004800ba415a81480da0700c1d4003003840c00079540d404903520001c08080080600b002d204080032101c40381c9800301e054140403002c0b82c6400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 735751510 1250 735750260 735750269
    0x402130e040602040806100311030106030201020c06070318060e09151003020a170a02031602120304080c3f132c040f03020f16060309030c1b0e0903040609 68
    0x951440014203214459044d0b80c02025400c00792240c500d00f141221440f840c05000c12180c5510010f910040340c1414410b02d401e60f0f6040e0001d289803140c010401449030000082241000f26120b03c03d200c0320110802103000382016283e0380404c144803410844885002400654411405c09404449668042c5507044a28071401c00507602c0d500c20f030007120849900c09405a00d12050000d000d58442c50354021882101104c20b500001e01c5c08140803600e03140004208003211030148042804190414000c080c0c0704004d2048400700e03200003403060459a2003004615062a514060340c1c00f00e10f1a0b891380e80ca40c2c14030f0940070b1400c51047d1490341060214001c0281080d6120046c010b1036840c2c4c084008420f036401900f0496140c58900318442c00e1070b1500490050040310300500b2410400244040d450b081c40340e140150500303101c0d0490040c0000d8800748c040002c625501c201159401d481683c90103031403c5094859420145a4038280c0c1e006028404558020001045080e5000c001d040644 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 735752760 1250 735751510 735751529
    0x51b0405060909122109070810090b0415140c07020405100501021e0709060f05120a0812060406120308090d0f050d0506060f0c0d021b06040b092d0f040213 68
    0x108805103c0c0310170000c2000000c103400b1350348418817005050021b22481110200303400c8903000840203070028160f40c1c0c4214000e01c02d0907040302290000f017020103120010081071100142151006000385041d001c16a03080f200e540c0b0001d01c0e0000d501789030040540c02070780d41a010b940b140ca020b00003982c038040f40c0700c060000a811000203d0380c0805006541c0100500c0c0028020161242040c03100c0c030f80b1500c1401d1141c031070601c0e1b08856030004521541c4268000c2c1c00c103824102140140e910000000f091503901c103a4030720b00424014442a1403401d00c42c000c0e85d5402041c40d0480ca00341c42c0c0298156120140014013504c07500d9142d02104a401e0382c581c22030049440d40714107000c02c08c5030150041c030085500c008035201a0f0904000780d00c2e1941246a8210b482c00c4003e805040900400c82d01071907049001008103100040c00350004100307040014040c1451105020303100c81003d003020319040c20590b00c081080c6070a281400d061110f92908442c00c5143c01001b198581481c0c4a520468005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 735754010 1250 735752760 735752767
    0x18170708090f1f050903070807050105161e0609020f03010e030306040f0b100c0b0c030c091018080c2d0d0f0c0b120a090b060913051b040506090912 65
    0x1280c81d0f03540c040c0c001e80390b44000354440c03450700040501650044444180240701d0500300082e80340d03002414904560303041e1510b9103450380d95554645a45440401559086400d5420000f60685410500300c001e0154500007090a502d2041010b041c244040a034800e80c1060510300301184041304a80e007164044070001140d400903440e840113403101205856010041c400c41e070925075040301907000e5451181200050b962b50f8103200d020303103000c10340700c0807002141846510400d0408040d00c0469022500f4114000202450703c851182c12940000c4165000f131411014581007900e0341030314500b10840320501114003502c0d0102028801641c0c07a02c1920304455103001c0c08000b01280203415040550701400302e0f10b814134681c069003d0030b000b445502080d0b00180b4180d42c0d6108808100380d01ca0041e070102e0702c4010030406152409889040d48011000846001507000c000f1440000c0c0484010030482011500b08030407180020655405500e241041001283c80456880310035550007400c07948 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 735755260 1250 735754010 735754039
    0x10060e0f0f030f0a200a081507090509101a0a120c0c080c0303010501081305060403111e070e010905040807030c060f1d07080106060909050402060c011817070809 71
    0x19048000c1e030310303d0301405801884810310914400c641c2c0e1083c0150108140b1580700c00501424003440e105010321500190304503200610001c0c1d0503600240c180c03401113003460703c13a40000c0b60343d1825607600f034000c41070140800034441d245200f20300c60b0400c02515402c3c1103a014010f03100c602c003410381a081d13958407104c85e24018003c03000003201c02d4200b080700b904c44400040b000c0e5203074828007465001c94004000200e111050121030100a644580900150341341c0d80d406503403601d10340e05000c106014517241040940010880c0000b000070b682c00800c0743d180f03801c0f498422032006030401001b0600705400c2201140080d03048a2645501d850700c0d512000041c200b920007030803411009240c06040044508080040400e40541100d110f8162524560748800142c200d507440e100d0700740450a031100030040302078107910456029001030406441c1281006400d421100c00f01c40701a20f002401e6001d2051058544005042d41b01080d0410701d0302c0440e807a0f152484c00703a0705946100700c0b20700580c000b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 735756510 1250 735755260 735755263
    0x7090501110304120b1b041212020703140d0e0a060c0803090309090109091e020907030b060403120503070909060e01090b010309050109060506040f0216020d03022410060e0f0f03 78
    0x140140701412946070031821170302d40600003401c03d03200108036030030010b0362101000721030b0110307011208011101c0303800c502c583e9182e0340713000d080d0440351044d03000310302000000c9140150301c4245da44808016050136200c03420081d2002c1d2828201d1800b69203200c009100d0b868003c0c901003001d641100b2416101d54558050ba403851041c0b280707554101c2e4444000207542d10540d040100007511460080c44110504103200c2117005000c24080d521002d5000030882d014017980c00396105240c042c001c207160945a0b261070252001001c4880c0000b20000104140f059000484001400c0389020a0002501d000e0100d0903400d018002c102c94a6512410108207070b002c4d5100400035603220000b07011040860a2060003170100700c03030940c00f650070111003d544000c1032003200c0ca907112080c0380c2020f801060302480807070300104404400b035114040341804981510101c0d8084100308541492141c60486030111714612a603100509000f0241960a403550b03a1014850380010709950343c0034100b10200010f03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 735757760 1250 735756510 735756517
    0x10b040e10151e1b060510120c0501032a0e01030207021309020103110f0d0e0312160e040e030a111c080a060e01050d111917070806070905011103 64
    0x40756481041507240b00e00719001800c6048924036540f404841c00340301c00c0240e40051000c0f10101d0300c20b410183c4480041c41c40d52010740c01110b45c500d869803003601d8620010006090902c103840c0d5440000c0300300300035a454000c10811082012440d0400c0ca8601c80e41041680c3c074407041d0046c400d2050958039164400c0e8141c81905800800420415013101c0c11070b002002d00c08400e90000341007921455150714894204c1e020007500c1d400c05c030301d007011282003a801402c15025a8ac1d09010401a00c07010b040c0c0b00c03402c1e41c05003549083c1380182e0794806c1c0c0042c18104182a0003401503040c400300c407501140102c142c5841c40d2842c280800d0090344104054103040140015000202c0641004600c480d4070003007580c4204003005003044400d0326084214015402403107030b2070b401a220390400001a42e140c1107141c0c0428003405c412a1010001c00f91887c80d69103400200410350031039295011072208200990050025502078900c0b4200302100808059250245a041c45095400952010800c001b00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 735759010 1250 735757760 735757769
    0x5010f151d0603010303050c010e0129030c090415050a05070903060b010905030105190f0b062b110904050a0e0d1404081005010512153606090f06010b040e10 69
    0x3190f03642c1da1280f4003d8000c0d00611402203040d86002c640c10b40b00201441509602e90b60360100e041108480c0912220a810004425401d805158031203030490301c6680c2d206009500c0307591850002d82c9100040e004950f00200f40021550070041480f0321590004804030035030b50800b0021641540358001a600072a541c2d01040e010762a000401038800d82c6214112400c8038010014407520311040ca581040d6114418190340c011020851404e00201d201150b0406440f1480485c1d0301d50400c000c2401180c0c0f209203100011800001e080c508d0341b52a1103100d074004a406001c005500000032015030714601000e0003002e00984a80401c41c40c0c01101c242c5004120705808c50f000f1042010400c80a00002e01c00c11340605004060032190b0700001c0385915480705002003500300b84d40c0398120b01c0032008201071050320030f001c0c4c5800c4010117803000d2401800d000c4c042d0010480d50401107103962402c0e90320310f03907102180c02080041c02a000001c0c03c4500b261014480b070041b0741c4444c40c0d85844c03007105610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 735760260 1250 735759010 735759019
    0x60c010b0d050c030f060402060a050309071509090507051314010513090e0c180c03040c150806150a05030103150608071403070603050112060e16090e0105010f151d 72
    0x150380d080010006603c80000c500703505450702004550402a50b407807064074020b601c164244024126544100c001e1035100d070141080300e4800340c0d1182400007000d82c1850400005503440704c107200201c00e501800e50805880c1c83c141c0d1404c200e0010020345501c8901070040b90111324039031241103078410404d03950041c5105050901003551150400010315000c0c10141d054001c2150041841c5090034080504101c6410b04180c141d80b0000400200d03800100100d034850031505000c00c6a0400c10100c2030030302d2041e10340b1005401c081c01040385007a041c1c1c11040b8006020000c0903146580041071b40e0445c2e030311207c2400080d00c0100c0090140c0b10326000b40000f44541480010041031054807181d501c0400d4080c0d800c06034030303014210207841e0240229100700b00041d1241000a55660185603021020015910000d0240b450681612111b600144090f40c4403500b00310a08001c0c42194010f001250a03c500f5500c0d00f09030100c91022210b50708140120240e14280d00918450081e844040042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 735761510 1250 735760260 735760279
    0x5030f0d0608060c13090903021504050303070801090b060f0f04030222050903030f16140a0c0201260601110c0402040303121410051e040203040c0e0705090a0302060c010b 75
    0x14203030320080046105a960910070b140104815041d4a41282d0b00b07001401703951000780303007400c011202400c000c01d0114114400c00451481c103000508086000301e2007140a0342c5c0c0c2e03061001c00100710f11010303084010818034003070519407a03643e080304403010100701034113161319580300380102c10319800765502c0a908402d04a5040000c91000d82031081c0a00751072100b00b1031034a4214546540780811030309020010398610100d10030301c2c5441d44000f04800f2a140c10309911010811083c6141c0002c0d4035000864001e80c0c180701150780000d11100c0318026500700702102c0400ca8104940c0b034130084c10890500240c12800722a00c40d0501092041c2c1c140504250743d5203540f03240080c4a020354903054081c0350321341715020100c0c2c040200d5807400758140060380c502507424070b400c00602d041007da003000b50080840c0341441d1504c0324006141f045004e04480d0f0142c614000050034160710040907281002001c000030201030b5201c0300d841c0192a01695026150f03941034060b540140030f42c200056010341400e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 735762760 1250 735761510 735761527
    0x612030d0b13110921030301091d070f0510081510110102040b030f0915010504050c0c0604050a030f170c0f1215040609060e19060b0301080604110607110d05030f 71
    0x22001420f81c044e007907511440ba00e20f0840e05103010704240620748080d0b04100300401c0250b0054004588801d10719083c00c003000d03d14604146001130a600c25003107010000d0041029103403511011151800d1804c10051901d44160060420ba420103891481840c0503a004521944640081c0c000007003075600071560340782c8460200700550011943c20f07600740341c00d500041005002150b4a04460500c0d0340e88842a420501084027500c4010700c0d402c5000e90070720504086410404c6281c0c0194050f00c0a0b20301200241030082c0310200480502d400e02885100e400012500390740c1a6901c00c104e0403103c1d40b1030300000340310b20f140d115400c41d061030082c0c1a0280700c5652070b41240b000000001710707820884130382c1c0e851030350040c1c60043c07140030265480400001c00c1c1c01740f000d100d500840407500000a059855014a0341030350400c0c2c02c03009403580325000308401c11100000050f14040100c03205030030031986507264012406e0040c051409840b041140800700502001961101c000301024541c8800c0813 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 735764010 1250 735762760 735762791
    0x118230c0c070e011a0c0c15090a1202180105150a12020c06150901080304090b06070f03110c0d2a1503020a120c090b0c030f030403050703080612030d0b13 68
    0x280140d804401c3e00d142c2815a105c0c030301084a41c120300c0303030018081341e00c9030404021100c03003400b074071440c004400c07c1018030595440e1500340c0600746000c1651118452401404112140d0048086148070218010301c06640c2e1090103000881110580554807186107030700719504d501126840740700c01d00104100c0c2001c000442c84600c030b00f05c602c1d050a41d03000c051082240c10303c001e00c242180f43e00200401d01030b01520750002840a034010b41410700d404000e540d41c1000005411081d40003ca034928aa1944071042c0040d4400d2a012211604081445c2e124a4003144481101c4204801d07080071320412501550554402082c804e040d2101003005100017401a501540410000400210741e03280501c46a01c00c070380c026401aa10728a00e20309141d004100f03548100c0b00e02101d480300b8400b082038103c07140001e51080c1d06c13a680760b40e2245d55514000d8010040a49424890010401801c0c002c0c50004140c41d00c081c0104030101e241e85941011810212800b0709a1500c242040340c0c03460000d11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 735765260 1250 735764010 735764039
    0x8070e130f080730140904090807020604090617010e07090b01120c1115010e130201050d05150901050306130305030a090507090608060105010507080406051806120118230c0c07 77
    0x1e081c20480c01c94004800e003118a8a440c00105c0914a001c6c084512541066404600f00510401080d450080240c001a0352900507a119400990b00c4900620501440d03000b4082c0b0383c1918030091002141c40c604d81500d40c1902d008041e0010b58440d0245903a81c2721b07901c901340d54207524000b08102103940c2d400070540301c402030920840d8883c920b49094007004041100c0d04076006408035240d240c403104200303980b1110041c41030f410410140410307250358542c2d208250150003500039aa1a041c0c41c4020700032458030503880280310ba0041d404200b0803030000d10012510561501d04a5681e542d8100480c00409000202070310358403409101107000166940044290f0b195401120416a40c500046400d48500170000700004000c0c0000c010081c000c4014107003101c144240c440c0303075503910401310714142c00c155a5401c03c3c1d03090a0040291700c0d060b0032844030030021403405000c00c0083c200103a104860903040700000d4810b17440002c802c40409000e0714100a681c01c1540e02c0d00b9501ca41003404690b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 735766510 1250 735765260 735765323
    0x31812031e0f080f0615030903040f0f1215020d02040e09010e0c01050a0c0c150e1005040b0403021c0204020307080106020f07050a0e0a0e010c020708070e130f0807 72
    0x41c510015085076000c0c0b4040c620309074481da21405603541d51410044400d40c00b811054110000000e003088589030040590b21407001d2030015130701c0e1450702104100c0081c03031760301803008014280c90030301140c01d000b0308000080360800404428150b12000c040024130400d64261f00652000c20040754070316000d03201c9406502410300912a414a20428076100c4403641c01c1540495020006049401c0c014010700c201e00f80103000380307940b090380c807800164031403520b000210000e154a1050342e51417400d807202d020fa08900385030082c10181032804102840c812404040d1103450a1000c044010a001a0748a0ba0507400703401503440b810001d002900141080c010324015004030044c041003508000303803841c03c440c0020207119005141070352011040d031014261139122510340100615902090084a001350400c1c0e00920800d4940704030581404c005400c449202c42580091181400081046803566500140f00d1310700c00c60760b07107444841880381c408001d0a00000d40c5c94000d840308079010300d107800d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 735767760 1250 735766510 735766547
    0x708100b0a05040515130e0a0305030106030c110706120e0109081c0216080c1e06311b031506090f05040506070806030304050604140406080d020a03181203 68
    0x1075842e1010082910303003c458030a4a01c14070448000b80e031900407044680501285000522a0510b8400c1414018105c1c0c0c00d40200744000b0040001030b90612a8089150036482c140991211410320583c49001c07a00c00c12003000100c480460040180e94032400d191408c45008000d012090f2078110155041100c05100c8100c2c0c54141940309805030085a00140c42005042015200d681c2c0c0e4200d25005400134062621a11080910b0284980c5c2030364482e0a0000040042d81303414180080d00661001480103541c140d01e0314001d18001c400c007142c1529512901415092905040f002d001d180705902c080d00709114440e0240c80795940e07520035401d03a4003003d410312408001658134410f9600643d80240107a010a0000e14554840c7d030701032b41c2040005041d04c2ca043d540d0f0001403602c4c0c0180d000105880c0700410a03000600c0c11780b1a800007454280080c2019440046010f5240c400e40d040140902c40c460085000b1040e001001e64060010100303140e52001560800500c0d000c02d0403e9500d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 735769010 1250 735767760 735767779
    0x100f090e1f0e0f0c03040f050613140c06030a09030513060f030b0d0305090f010908031c06050901080a0605071b2613061407020a060215070503070806040209030708100b 74
    0x580d80d0080424810000443d0707108003501d44101451450744010819904e5100506c809000210240801c1740544e040103c0c5003000b03401820108840d18015030068070300d5101c441c2c03200254440c0310a80c0c2d8404840300001501040300e04040d91203100d405500b40c0e40e003051580101d0582e03004882443d809180d075504018561902c028007060109814008d40815002d2003160080d00d0080b90540311a40185030286519540d200c1e42869a0402144110070040407042b00c1e030f800300301d40305680c000d0500301c5080b4001e506d003103181c1784c8404c00b200d0040c01d80340e110340004144601a40e803000b0388404090700c0584030191420000c6010045203d003544c031003160b2b615036018804540039a2810102c40320401c1a0f41d141103030588686428021659a000c800c0c005c0001603554012007a004142c00d4018041c95842c0b1000e4000c0d0450060100091202c18414007001079413000140c1d50003d01a1001139032032410400180c544401e56206440c5840399181007040781c45150451500002c055606180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 735770260 1250 735769010 735769019
    0xd1406180102090109090c030e030313050f0c1c0c0509180c0d08041503090b040803181504020108040f0506040312060506070203150c12010905150102010b100f090e1f 73
    0x907880f90361220340c001403804100b03010700400ca510101c2440403070305002500e030b240e009600f41541c0088411002c4c403608140103109000050028420241d1060040e0480c0a20680024100c030038499200d1120301c0c0c4400720100300314150140b4000340100800069051401d05482d211010a9030003420103400f800342c04843c98100009240b0105601c40e4145040600b00300f0314081c09010000b9050405440340c8440700030401d00c403441c07805a4015040f0341c0d641e2601e5a00800c52201162280f000c0d0f6104e03404c2c0161798080d110090b80c0003542403074214000c2c1c98a00b48000c9000e03500e080900a8080e8005020030182c1100c10f00b00c0081000300c1c14054203580e042041214020550080c0d015001000d1a082a00c01102079503845840e80741c4075030070301d1158502c1c800c0030b0800340c1101408030742e82c10900c04d1287c124158820404401d200a00c214000c542c0824411003a0a1041c414450403002560b04980130f02d040c4030282040c070380c0c0c0780ad651418003c151040f0900700400454040260740101713 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 735771510 1250 735770260 735770263
    0x130b150c1f090c0504020c03040f14010206070c11060a050c03181002030c06010e07050c16050109090501120f0215120f0c040320060405101205060f030a080304020d140618 75
    0x2100c15004101c0c08400313850311044c813010350300020303c0d422a8001000003007141c50b0b05040c160050080c01c00d44080034074404001a103440c0c000f0f0b1485c0d05001d9003c900100003001190340040c502ca0170b5030116100c4982e0b4209440780c0c00340410070b580d540004519101004150440b8609803c030848071911410101034050b030b164070841803070f00c070380703810400c014001c06600d00d4980d0707046105440d00510b85401341c42035908002c2140c0400d040d11400090820180d03074455041170203481c00c02800c000d694036007280c10310341c0c81c076001c4020700c0c1503148141c0744150341d20a01e40086025007501c00c142e8408039440295220041104e0780284581407002143d0032461540580701a02d5000d09002c0c1e265061520121140c85552400d41d4000d008200c04500c64668616501c0d2a140a407203101c0c490300c007801c0c400103880004000c1405815800c803120f110f60703000100c0251007500102025070382e072200c0c00450099105180003408144124207603019450b0b001a00750311032003003414600b039110940ca0800c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 735772760 1250 735771510 735771521
    0x4110a0b0a11150c0a0c1109070f08010b0301061e03061e05040501170c120c0604060801060809340504020f03071107080a02310204060e060405130b150c1f 68
    0x946400d0020301c0305e60f0110340104c0e000340c0b055019903c2c2d40303000f41021000804450045071440c0020713440e0354103c0b0360940c0003440a8090046078481c80d0079581407500c014181070440c6015008814982d03081c40405001c0d0b808980500040302180e03560402082a9905030741841c803840e07014a1502000280c0c045825180c0c900e00404d190182c41229101800c00c02075484c003d42c00e00c1180294003800403a96100300080006158540301c65006615021011303202d8000100303401081d0b00528a003a8041c00740303003000c4031050701e030209806045480b11151002c00300b46400464106100240c900c50211440e400b641c0310303d4080c4c3d24808003a100240e805c0d10b403042846425155880b40c8200001441c0820944068030404965000140045648440c1070840200602180c07607000409103e05540319801c0e9400c05400c0c0e03140c92138107180001182c4520034000700100c4240d9210b244501c7d90b03441040d01c0703611000e8480c0341512000c56490780f07900d6007603009048103900000380380d03803980100c14000d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 735774010 1250 735772760 735772771
    0x338120c01180b0f07051e0d08061008180708121210141c12180603020f030112031106010306230601020604200a080303090f0c0904110a0b0a1115 64
    0x40d040001130034809030207410651040b501c902034602e10b810210251382103410b0100039040240550b07110144041c1844078013410490040125640d51119507411007140d9401201c43c40e82011011002030129050240b590002d090303600612a00d51840060b40c0c001c0c101c0c524010042d611241c03030b40c140d00900300106100e40a404074400c440140c0d41d02d4110490082c09481070b078004040b01056450350902002141d800000c40d2154040101001b5034820701000b40905007011071400904801800302c5020502c10740104000755020300003018030a442d02c2c400c0301030000484403d56120300e064400781201d442c00000c0849902426007504040b8803100d8040c000603005400c0d00e403165203d50900142c43d40507003503a407021542e4899107403a14108030f802000ca0101941e124140040d80d00d09110010f000541598400c5020710030036a6070f80700c8981c100c0d501c16a03059013074403500d02046e411090761b0300a02503080080703800f070346583d0030100a2a42c0c00b008802e0710721058950180c039140c580143d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 735775260 1250 735774010 735774029
    0xa050108071205031c05070e0301020a0c110312040b0408010e03040605070326010f090b100f1211040e180d0e04090c030c06030c09060338120c0118 65
    0x78200a0750011001c48508a80540b054928002040c0681c20313400402074490702c041da54503400c02540b180d01a48008910008070b00942ca41002c03210000d100c0c445628000c3c0c40860441ca40c4801c130740d400c1003c01030314521280d209071a41e960715003040e42a085441070f040c0070350a10010170204da40110840d4141c40003622500c6c03d00640b9207084408131900e08010005850603503400d5043c4843d0200706000b06440040030404070309100c00c1c801030710010080030703001d810302044008490703400c50501c4415086525111444103d051512130151403083d100c8104c00c0c1c0e00181c00714100c900d999070544180d112211106c250004200040d079204443d441d808002850000761f6003151810303800180c0d80702d000c0c40b003144800362a9201d20840e951554404808a550f40d500c50324540d8000d2000d000030220b0741803c0003000c0796034840b0680d40d50703030f0f5004541d982282c1c52130042160580002428904001e040406039010030700003140d4070390a0000c0c03a400b0413009502092081c8a102c1008143c407404003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 735776510 1250 735775260 735775273
    0x412020d2d03020d0f0506030d0e03070b0a120608070302090603061605180a120b06030714010f03061502060910290a05030d18120b070e0307080307050f060a050108 72
    0x81c0c104185600c24400308042d0208140c002500e01c0c1c0c042c40c42d02d8007014000140a04002007050302c3c5c410103070908418485042d000001f1540c01040da5002c4510540c0c0c0c950b511603012004440d50148084040c551a15200000c5400c074000121a416a4401c0d6801c2250740c0b500c500305550b0300002c42d82c03d03241301c605048031080f05100c0c00c06031042001407550304c0a501102c000242c8403100035005103001001d43c055100521645900494014000340c2c05008200d0400810100d0360500c1ea81c0f070703418050b14046e00c10945100b540048018916546010009804440004d40740c08054411404a104a003483c007100503540c07103140b0100c00b04141f024102403281080325006801c100d00b03540e00010008000405403030500600342c940e1902e0303403041826940d00e640c046601c24284c20446101905105905c0000d15a1014a4019405003024000b030307640d8000081c40d0a080c0d4100c1e4155010200700c0100300040050031265448110080d40c1d084d80d039502c0d01c030b030850f4400d100c1d50385540c0c80b84 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 735777760 1250 735776510 735776567
    0xc0e1f170c2a010e150c12010303081513091205041211030f0f0a0c08010b0a0608040f142a0d030c0c090c0e0405100303140c0a06050412020d 62
    0xa11820070b08502d5186031841805809441c0340c00c41d103110703400ca1aa40c100311001c0b01c1142800d0203166125883c07010032420f0808000107201c06010500000b01030000e260003061a0780c00e00d2030795042c0690000d00450003400100300020107480e9441c03007210300c240302080500f21a40504180c0c1e00b46c1c0c0c222645461041c5003500d0302250242c100e002c480d0035000b0131040040d81482407150031f03071043c0d2250040149000f20320b0943c13003091007a403201c200c1c1d0b407420039903e005a403101703c1d160854901c0d140c1040180c441c0d08100c1c044003410900100100000c0d0700310284d0190104001120142c44600281c00c1041400d0301064074600c2010280e1144400d02642c0001740a00e0010106500a0a24040050f12680b03440c0498800944031000310b0a0840200341d5071602e8051070341c1c01510f190046c0d00291031503402503c078100603a17100e440c8207400701d503255046004215034160982c02c8601408a41807900b000081c4002c250034941c010300524404c0016540a0144040a1034480b18a54000501c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 735779010 1250 735777760 735777787
    0x31b01122a030b0405040c150504180506061210170604080304170d060f0306050c0a090b0f13091d0d0c030e121501060923040c0e1f170c 60
    0x50124001815550900e015058071203120b014070480c400c00c250021681230458803e005040502d038002000f404200c1071040400e468600e8003500b1003070001040c6529008001140d42c0070320310994000110a008001d00840e00c0c0482d0022035056424105070301050611035a00c5402c01c941c041d00841e001c00115000800000f80a403d07003510081c42030a021102d43c052043e603010394401a0b40550300071040c002c2c448544140d0350810f010344020303460400003400c054490f07400b52040800809011903010604141c2030100d0b141103002c200c1d1307180681d4480c0082c800401483c00c070703038042c01540c5000800400001504e00310030503650701c2e640303650710035680e04407420003c03003900360340184101c1b81c1ca104000040002d075220a048411075592513040140041030030484da40041e81c0e00400e03200300500c518008a501c0d40d104802e6070045007807015140c05455040e010b400d00c9070008178090303190b1004d070b2000c0303000740c907110a03550717224080e610120590790f00d01d10034ad4000305441e100300540141c0301e49 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 735780260 1250 735779010 735779081
    0x80a05101a09040605101211030106021506010311161101050c070902070c09050702030703030e011b030e0f030f1809070e0d061410030c080609150c040302031b0112 72
    0xb001031000c41e5494803040414403880188140c100400c0416010100f111104c1c014082c05490400b089070643d85402e0001756030b242d6400c2150724846010000c6001a481780d000544840d0804542954a9901c0850813000e141c9540054803034a0385401c0102d03003903101d03004540900b5a060001c1004900301030009000303500440c0300320341c02140d607000050440c0150152a1080d00e407134000d50745400c01420064182ca90303d0f0400b05159240c00c8140700c1c1d000321202e07444040c80039460002007010310014810300d42854001038810920010844000c626010001441126035101c00400303c05a01c1082c4144c0751400c1e500c050105100c100d0090f69400c0078016140c41d01e01501010030004807501e0a40d20b811006d503501085000ba1000500601804172418402406220010315885c07604c02e0100340c80700f5030349419450b10141c42b001301e030040841005032406035400600782d0700410800b07001c801e0803101103200d441c040b861150740d036801d40300503100300306c100c0400c4955410940840c01240c80741c0312 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 735781510 1250 735780260 735780277
    0x80307050c07030203120d0b031f0b180c0a110304060c020d06180305090f0a051503070c12170601020a0302100b0102071208070209061207052b03080a05101a 69
    0xb15000d0300002603070303003000b4400b41c0c101e060b000380d40d8424121040030f098a01050341c02d4041e90040c403ca5050f8400c88121601001881034002100421040011909140c0000010200040105200c01c000703039000100840200c80c3c0340e10880d044002c1002da102d019070321a140104000c4440c500150400f520340051641c03161000082c803034401509410420441c500aa00086010449805504240510342000300c0c00b00d400c2c0c07190a283c400042e080d40086403c2c142c0c1da5030003201203002180100280c180c0243d2000d0641140303046010010203c00700d43d00c50b40c401e00903a00114040e940041031400260b60540d0241c59401c1516000c14060004400c00d0b604606c2255000220b840c80b26600d0000240305800031540c3d00c00034010403c001c240a05600c3c4a1032617681d071014140c00c006254000c4a8082e5030b480d038a03d81105170074806207406a24201c3c605e0003804010300301036000408501c5241c1c405001c2000c1d45901da01480d000c0e20600a6403c11280942c0710015003030035501500208 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 735782760 1250 735781510 735781513
    0x30f08120907090b03071a07060e0307030f0201270f1b090608010f0c08010e0714030c0a0201151d1005031207030207140901090e0a0606140a12080307050c 68
    0x4065102001206100725081c0d00c0c40d42001400780240022401400030040341100140031140c06c0c00701100740001040c0715484c03030302c40c00160581084202d410070000180030106480d207a0086040141801402c0701c1c1e02c10055180c050340f9510940000440d49841c0b40c0a028810240c0303195440b1218100720080c1a119000b40f096a1440c001450440c50064a5100703008103207145000b00d03c40c02c1d203065640c0341c61120b0400c0c44110352140c1c0300c81d21504503008500b0301d1402e911900402e491440c5041003500e0144c9000040152850b107031002040c00020a5000300302e51120030740140d07165070240c041c0e800d801008800d042c400c414040e0460750000641e01e00704e19070300d69660009190545031402000d03503c0010841c0b05c145a014044c0c0030080146914440d900140d40000411360041400340e00d00040e0b9824840e681c4010400c000c0341265807000c01003100a880d8030a1940300260303240480c1c40360682c5140896440746014600c44001e0740083c9c0142940c40300314041e0f581e03030031100007112203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 735784010 1250 735782760 735782767
    0xf25050705011d0d03050c0f03070c0c0e01170c0a0819020a1707031b0302060906030406091403043b090307050a0804061202070203061902040902040b0a02010e07060801030f08 77
    0x55044000d0280b40c3c3e00d1840103041000020002400b5034100070b00022007082d0607c00e10600f0000e8004480e40308074103107015040403455140001c3c00f041103400c00340c001e079180320010981c0307112580c000606520010840320210305001c1002080101805150032640080b00e940c0d04008544050702c2080740300030440c600c4e46481e0303240c5200d400b082040310445588064020070078400309100c8940b00c143c40701e104a0000d402c43d000308580c0d201d452040b07402103e001000605004196014000c600d50089205031003402552043c1c0d6244c00c5801115440f250880b0ba07402080189880080b414182022004005e0702508502c8158040240550520b000810840c0c00151007030041084092154056a803150b0522000600303241356241004401481049a80056a03001078540e80c8440002c9080c40a01646007440d0041e000e681c3c0891041c0340049400b01c0c0718032042019180c0c101c0703142c1c020800710b88100442c03603880700e05208610216850a0060020a140c000f108500034051a041c902c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 735785260 1250 735784010 735784031
    0x30414030604050a03230d020d15030305191b0302010e0d03090b01030209131208160c081806090406090f05070309080a2307140d110d0503060a090c080f2505070501 72
    0x240e82d44134010702c1d0350307c0d640000c034003c10710102c1c420071043d02403406640080c0d50031550060141e00c680383c40500c400c20304c00204c41c1903074899407002ca4160303410601403505040500e0064042c2c01c070107c00e407895002d03425502014921921401e400c1d00c1e0051400440c0d03900c3c51b001c2c845440e40240041d4031017040315450030f010582481c86001c481c1c0c0c599840c10001e141c160400e02045600001400c10848242d8405010800c0780099828405c080c4850f14525050b1400290f43c52052184c500d410504190000803480c40c40e41c000c00443d105800c0c00e100302d81c2d9a0b0b504908443e800c45006000450a01400f40014466828100c100904140b210703540200c0c48a555041e8021602c2128200c0103408001301080b007d10403010819611304003140300c0c0c3c0b840010f103070716036041074601c000304440840020090b54070203011303000420b444c80301080328080100d4000c00102c812210f0b250a0281e4034081541c0d05142001000d403524800e001740191a00e0080403a82c0758031500d02524259260303a0f4020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 735786510 1250 735785260 735785327
    0x90b0604060e120d2a2f0909010e0105010902070503040b0703030f020706020c0d1806030c0c2003071521200306010212040312080603100c02030414030604050a03 71
    0x80e42032069219a18440041e4102c1c0e80702c007519000b18040b60745c42c0210b10700080d500d5030251b00300700e44910710900e1300881c0e42038541050040c2500b49074800f03d4041400b01d005010b5200b6582102c0d40d5000384085e070380b20450b100580c41181c5000304654400c03c000c00403550054041d01d03580f4030914021030b4080361154803a0998005150640d4142c0d40080d0103054440200090070301d0705990f003003024180511019020179164680310341824151229003204d8101d20400d0702c1c0f581c540d40050119212030f8240201a100c80182441e20300a03c10203c000c19900c840322403801c403141141d92024040306261075403004043c0040400b00707002c0d07158243c1403034140092600b0141d010307002c11032035203915050000900e011148142640c114508000c24400308900c1f1f40300c20020162030030003488035220032003c0b03481c1c00010070451005a14158459a070281e002c0020001c55103003c42420b445115a82056110142a500104107602900e004000a0300480c0e540905d00000024003110504440001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 735787760 1250 735786510 735786523
    0x3020103021308060718140108010902090f0d08190912230307030c230303040f140d0f021203150d060615050403060e06070f030b0d0c12020a090b0604060e12 69
    0x6003c0b0f038512001505200a102c1b9a030001c10340081c0b09045442140f0000e40742a106002c0c0228560b000542c4844030b840d4044040151040509102d182e00c8542c203084c520f1360010310090012601c014400c507003161084c3c500c502130781c0118401000001c0380c2e43e03508d04040004250315005200f280081d546a40091000d09900b9000f40c032440d01441316841d00c40410490030b03c005403055151181640c4240c00081a01d078865405070344003c00e6803581c10010b141e041c401d0069851071152900d10540e040e4448007503014460a03800300c85029403032071a0688035000c200c0340410b40307002c01c1000000038030b00281ca180b4140e0191800113600d607141c0c03a10b4031400c0240c00c0000e02198000500300100403240c400c502034042508007070030361401d008000600c60314401d05441c04250f00c4961002c420ba88508204103150b5100252154041c1d4030b440304240984030f01d806910407003a113000000d44225a0161108505004000c68506801e214081e240380c182d903042103401c40c451300c80e400d408080400c80c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 735789010 1250 735787760 735787771
    0x30406200d05061f030902210304080c03010b0108130c090e0106050102160b040302061b01090f05060a0606020d050f04031b03050d14070303020c100615020d08010f0302010302130806 80
    0x199944181c003441d100c0641d440500300760f00841448100c000054020034449034504c03028680800c401c2c5803400020005400b05000220310700c41141003281801000008004480c000b10940d1412005d0408042c201e55049501d1800320b0a5100025030000c2607104421f101840b41588610554440344030604440340c06186410681d56000140050b607010003051000b10317540000c2002c0e8038200394001072140110311000f4000d07040803c541c6e032a20003403515034044164580003000b002459090201c0c03c440111016500d9000340e0003c1560343c14a0b02070f050990703005800415501341102002c5030282d0202c05820303541c0c0d8040c44080000385d50220804200303003c42c2000e008403030544c1041da04043c00041d10100303002030148860b001107140790542c0d0b16107805040058994545e520058101038000300b0107003c4514248010610f4403610b440103500d429103501700c0380441c140b11740984001c2380a005081800600850420040d072007900100348802c00b50000900c8c2c103a8507545545004030941c0e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 735790260 1250 735789010 735789071
    0x303010603110301030c290c070609060c020307150c020310090b240f040209041815060b0f0f121e2206092a0513060b0d02030406 57
    0x4100031581401207400d1080c850710300d40e2442d4915601c6040c000322512440c29148034a01485c54805a151311a491030700d050a03050740d07100745180c042d0341c440406005040100f0030002000c00c46520840d46035a17150307405001018a64101181043c4201000302000c04025503001d910300180c41c18801c650070741402d4030f4007040c590140d207050100090001c2c0002440b000c88503140c44140c160040c900b90600054031105107091446002c240030f841340e0920950000c0c06c010521030345501003840341d11500c0c0114a14032180c0e051107182d0040e2400b030303c601d02c00400240065100003110070020540d41d980117040500e4a2100385201090070740454221100038144406005c0204819202540c8141d10b0000c2c51a0786030320161601510b03544040c058034481d43c1d03255080c1000440c5065000300d105180c05600c102d407074541d803941c1903005030040302e001b04081c4c0b102c54050f4500e40190410341e031404801504040b18041004000e4000800036500c464590313800321181d080c600070f81c210f200000c18 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 735791366 1106 735790260 735790267
    0x60a15091104090635100b0d061b020d0806090f1003080d1a0405060d0b0c040306090b07021603020102030a031a030f0d020607020303040b060f010302160503 69
    0x422402081c0e2901382d000c5005002d03055607000028040c600e159441c5c0304403004281400460007180b03031310b91003581d40c00e1003413565400201480f000608404802001501e82e01c1c280d40b500720541c880814500e07105641154140200c000030100c0c3d041110b6641400004035034041402801c080d0002c0c1e00101180c001507044440d04002c6030003600f1552a261a00b40407001003502070007038491048441d81c040c0481c140f600507284101001000e007000c055207601c5e0748500c1d0030700621403010400304000100002c0d00d14464442d4481c010044103440d4038000c000030740b41110303540310510b1042e124002000141e038008202d0302c50300c0d4035107000314600d130803155600040350501f1280c0350302d8040c4445034003000320001013070b81540d0b0940c1d00715011600c03545d500f607840340b1003030700c01038a1040c1c1c0c9400500d2605221091035800a07062400520b00030080564020b902080c0004a41940000 = true := by decide +kernel

theorem cover : BRFrame.Cov 735611510 735791366 := by
  have h0 := BRFrame.cov_init 735611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 735611510 ≤ n) (h2 : n < 735791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
