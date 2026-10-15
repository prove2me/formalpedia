-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4882
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:02:39.304979+00:00
-- url     : https://prove2.me/submissions/65ee2516-9894-4f8a-bc20-9b8616f97409

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 877877697 ≤ n < 878057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 877878947 1250 877877697 877877711
    0x11b180504050907030311100f0c0809060403141305060a2c21030c0a030918110d1d1b10050a0f0503070c0506040c05042a050d2904 58
    0x34071003119021102d41499502030401030010034002d080365201003414004a5001d5100071302d440081e5203699203402d141079210710040d0001504602c000351705c4810341006196928064500900003803010040303a85440002800420f04044103034100003031b16000c2c2c05243d440e42c0c1481c000300b0309020036001901d105600d2181907682e002903900e4058001c0003c2031100c41013803031309002d0f0b403001c1840c885080302d01c801c011900b000e035810b0000b0095a80a030f01d950880501d003280348041201c11058050311a843c20603148415251001611280d40003808006404440301e0301c488503810503c4c0d013442051203078100c101c00103155000b018804180603a502180c0015011040c0c0382e42c00b468804101103040d0103400803580740b20300059548810540b800d044040d0040d01d0300c60420105881c1a150b41000510620640c2840e002d10365101700140a100c0300810541080c443d60800c52600d00d08214002804040c040324a030014004004031000d03440c0044012040007803c00340060f15540100c1c10410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 877880197 1250 877878947 877878949
    0xa14100801080c13180f0b06121002031003021201050709050d0f030e1302221502030703122a2705150d020a090906141809011b1805 58
    0x8041070403140080c004010301c105000810500038882c29601c0002e581d601c4d0070340a000050720040078401d0041c0b0400d1103030211401d0444541500a050900811417100404280e00000a40c3d00c0d16443e128801a101d4545400181e1076040951000e948012201070701401110190f0146004030580d8030f0307620809940d4018080420f0074000050040704004840101190240094880110000b0100e1845d140703005500c43c120b0700104000b030718141103260712103002c04807827808001510206e02c1144002c81300701002580c2e4440c107030f00101041400724091110003407681044134205190882010410680c00390a8055207011200034001891200e00500302da00030b4401002a000d04500000c1581c208014031140e04003040d0049600181000345098042c403610140c25000d007141d5603102914500140303070040e01c046802000b0300b0000a016504951384d00b030480382d680c0115116180c403039501c021203d0b004040074620140c004080105106900340d0103440d50300c44010103000800240d0304c0340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 877881447 1250 877880197 877880207
    0x706080a060605120426130b04080601061b0618200303090d23010b0315160f020f060a0203190608060402092203020616080f04021302090a1410 63
    0x120501c400300300308002c00c0c070072131181148083e8007500841c44a03054031a40707155a50b240c800d45568404200010884c0c10210001220803030062088100d4107041c83c0c1020314844e11850b041c41168244080c1c3c03c2c1100f070403880e03080103200840c4c20100410040c81002d04110b0361609500e41158030031488100c00a990440d50090910094060b00550030a4402c4040c0540858a200140c601d000308582e9003140018103198120840317800700010440f500603405040c50002d40216640c0305d00444010400e01c03020340d922904c1002c5591a00c1890200d205000f6814030040d00b2100c9500d001d140c040001e0113819030001d50185405042040d02500d1842c11071040307401c14014000260448404107026180c031750322aa401035009800c06050005020b03090241d603e03040002c50241e0040c0d070411003406030f14000315600124034100034200e85000ca20036038416000410007485100b40d010b0100311800c00c3e505a8510303000c0035040d0003a0540390b45450f540156038440303503442859850b00100c0100d100d9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 877882697 1250 877881447 877881449
    0xd05190b22030807021e0708150c030720060a05060102070b090607061505030f0c100c030c0b370630050a1e0b0f010f0303030509100606020706080a06 66
    0x103030070005000140750740884905030003030b000800b14031515818082880040c41c4403044500c640c0028685149080c044238184191842c4040200150f5420010060b001d00103ca034007043c20b1030300304c2001c0b0403024940103103940d051049080c2d12450b0208100614542d100038043c09091b002c03903d4040d50740121f0141445048502900a1810f024070000030f8044e07000075040060300c24001c0b441d2500c80010a141819007000c405080d84a112601e44900b0114030b4008032800b45d190016038200c00d602c2c042d14510f151100206065650000034401c2c03d403503000901d80c3c0c507110700186000d0744900340724000304403200026182c641c80c215000a01e04c3e20002c01c0160000b0540d204448cc001d031411a02c0b01c000050760547c2d09000346414180001c1812242c02ca138a000122190145d2100d414078081c01c0c40002c00385002d90b4850b200500080d0b400750107181c1244d50500e0013040687e50400e519007810f0f6103100010019042080104401d03401240a00a42c3d080b951441d03919510416280300b900c0d82 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 877883947 1250 877882697 877882741
    0x60603070b09060d0c180623070f0b010609030c0518061908100c08100302150d020d050708010305370609020d080318010603020f040b0d05190b 63
    0x224108071005024000c0c0002c0c510041c80a4200113030101c0207000d0314210a80340001030012178641c14103012a1500c1c5028081a04d82190702920f0842c140c5c06001041c0744a8004090104e00c140810400c10f1031010103a91000061609594510010700300102038041120070740d91040e03000c1058200594051102d60046180082c030b41c0341c130002d00218800007801c180e40b40121035004181c0c2e51003085152200a40c24400207114282400c00030120b503805000d030800084031074010409640d90f00c400c03500d00805808a10f660742590305990f0024401e41d00340c0400d16003043e042014070f0385c1001110781280c2c081c9042d0b403440d41145076902c44921707566954030b111032000305c1908285090110314460044c440d410000704507001d50005004015803040c200e442142c00002c11100d210380d400d445203500c0802000780499425031380000d03650783c02c0d8500e80c1d00441c1d541c03050300c201e55220201103281c0d6400c031040c0ca0038541202d0610015040d10b035026600d110040d03010581c81c400c900808a18904 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 877885197 1250 877883947 877883953
    0x160c060f02011a041127040c0e0d0204111b060109180f080d0914010902010219030c08090d0b0403020c0f01110a1b091a10140f030a1107060b0111060603 67
    0x503400301008001c0c8140410307031885480502180780c880411900d044190300c00890491040c3c6ea600d0704010550712400c604c1e104200c03000040c4841500c0d03111035014040d41c1260301042c5040400a00c407468001d50703041038500507620007150000c020129240b41a03403440c0740c040c070602a0f1145140040c281c50300c00103018007501102e40e40450fa959014101c610b400d080081040034080d21012110300348101401100d965a00002d41103680402406030500e03819603400f11101c06a45015206a1000c140540300081c00a85d0761107613501c04444600050307012404000c1800d060134001c1d90303401a020035a000d80000400d5101a6018542000000b44944010205510140d4465622081c07881e001103681c950040d0203d00e41906000b0542c0a9031000344900c180e01006040080c06040d02000405002a545c41d032014090420300b1109854002c201c40c80c1e0ba03840f904c02960040c03c1400300141d281c40085003107401c11083e60868801813500343d071103448203400380500c1521004103464190f030540c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 877886447 1250 877885197 877885241
    0x703031512241401081f0c0215131406180a12030911031c23041a040e01031109061e040b03010921020f030306010c06050c160c060f0201 60
    0x141075103032046101107080800f15065003100038522006100ba0031800b0356030004054080c1c040010204d91181941d10380040c810f110402c80040c2d00c81005400c1014032903861400980103440400d1a00c17081e9500c07080081c0c8104003e882240c40b20010340d200c4030840070045070740d545464005140a00f00340c1150102c040303408100030940040000c80350813503c191840325400c1c00d030380c2c0c00e02c041c00c05020212250b6000c030000e20300c010a48000514042e4001da400456106a5940b040c181c8080da4020312000d0000d030030402d42d460160107154020400329400c10004000c2080341c034150b0f0190402629079103034541319007080180301c801101c1d45100c481c0000440343c440317190640241c915505c0140000594240f0340d00c0300e00d00d5020110111030080301030104100c201ba8104410501001d090b0050750a50800b90002040040c0c0440040e2020341c80380045055035481070308403008000540d490142c01a801d00c0c0c880d4682c9604d1003a040455410342243e0078440c0103000b0130201e482071124259480c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 877887697 1250 877886447 877886483
    0xc130509070c02090a020c010c0203030f13141207030f081b0f120f07110a0f02130204080f0709110406080103081e130905060a0501021518030703031512 67
    0x15210081000301004100b48900c00982c8468081c0c50080241c20809a640c01c0804421030a45003204200300855200b0001c1140c0d80480d122040d40244203503840c0340d400041c0c0c2c10100b040c10800342810741640540701c0e01440c017441c1c0380d008088080c0f003612161340d5050984010b44450710304846032034030151b560740c0c10141195440010945042c200384954100704c1c1e050030002c14604121030005294000a06025101e40c2182c4080d140e03e5860000b800190344590b2507107040910080024011341c010051407100e200a601510054100e080840f01c2040d40d80809950b60f104521410a09500d0005009003200042044405441c8540c8503c0c40d00d903e0b50341c902106501000f41076041100e07004500500e07002e103000825200c081203501601d418180f8809104403000604030390302c42c408500341040700e070b40c001c43c1e2403452565680d2111580c3c1e542c40c038880100c0342030b94901d00daa400005495010150147d000300e508010001c01c044c034581e201c0c1d0308502042c0380e1610240990030019545070036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 877888947 1250 877887697 877887709
    0xa080a050709151805030102040f0e100e0c0924181c03080901060906062a0c08070e0a0c05120714030a0603020306062e1701060203120c1305 62
    0x1203040703450494400340d07940400d0500300d48160a024001002d03a5400203c040c2529001c4c405004110000c516151502541350350b0200184980000003403c00c001502d05004000c3e5140106403041c003504213450601190032082d8850b51541d48030f90800752034100013902c5803101c0440c1d8086540701d40c0c0b42032030900702d40038103c04680c843c41e4030103400d100406003494500d82039680b0740d03c40e40716001c00303040c800040f03429640560021080140703071560400c4065401803a42c200e82100003e2001e1890180500359100001c0030b0340600b03503a0354110300169050b4000f0716002141d00c59000b845140e02c07502c050034142c1d280082900006803062014040000000c00040d41208503424408844000d0f825000c11680003103c016119540c3c40e0010403c2d401c040c0302c003c2d840303030040f80c0011001518240740c2420700442c20708414580c4059407600911030155106100340023031820300003420741c0d403403c0081d0749900015403140b0060b101030100350101d0542c802d8402911a04022229031403c0c40f00340a4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 877890197 1250 877888947 877888951
    0x80d020409060602010513030f180816030c0603021c0209040906060b180315160207080a030c1709010903080c0705130e0d080907030818041d0601050d1e08090909070303080105060a080a05 82
    0x100f840b002b02000071819404c00030950310072032042110381324603c2c2d0b007401983c0ba4550303030000040c940100403940041524a170102e8200015000042e01d962040f80403500401c94444024075580c41c200012441014450141c00300c02c0314144003603400802c080038035403034400b02d60100052001c03203c04900c51416000085200b0520381c81100d01c04d035907940460f4903100014000f503001c2014541150103028480b00f860380c407501101d08041c0303000025400202802050311004d00303d920085030120001c0070034010800108001011400c114074800c11450051410700d00410840c46950780f1101500e0007402150711a400034405070019a00e1078640310314990040d0303004060541034010394110780d80c44d481244221400c8500312741c41e1f043c219074114900001a0071540c07003009032446220004002150003c0b10482c0c00b502000304006507c0c1c40c00f2240196425290300030000302c05c21501035800034584003285d00aa070b6880250742c0e2001402514411119032000003120480000d003040360130b402c025 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 877891447 1250 877890197 877890227
    0xf0d0203070e1806030106060302040e060d052406030607030e250b040303111005100501050d09021c0b01060309080304060506010c050f010209040506040621080d020409060602010513030f 82
    0x142c0104400c0060b220700007003110744a00310010003d101e850b08091164202805032070504525140c180300b080c43d1155001040da40c4550f01c0c40d8a100f00700541400390000614408401d58204000301c3c10810544d03074200c030210701074401d45002685c500e22a001d00754007001401e014119a044941030240703000301800085000c207050400014000085400420040d40213030741f01541201801d07151401c107810142c0e90f5441509010502c050400c100c0320700e40445409003405a5100c180700078003000b0b08000b100113580a000030f4541460401c080c40c20f9a0120700c01c014070703e0b19a803600320a4048442011000c1e00500c1b0a200150008070a64080c5402000504011842a0095503014642007084000c8101d9035004500990182003034007685410000032a03040c841c0904041849007055800903d101c0b5060382c0080c04400d21074940112414501d0720b190643d600c0c0d0302c1e012450b02800c4248500d070015032901001134010061401d02942003540340c0c3d129456884c442808448202003401c1c80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 877892697 1250 877891447 877891457
    0xa030b06062b05091005010b090402070c09021605191a06130c030e1902060f2a0106180902090a0e030f070506040c3305190207030204110f0d020307 65
    0x18081a00e0240d502c464034640074202058600d8904242c50070031043d1030000042a04210042c00032000c000c0a4501d048020b407001600c5900c2c42c14141d4040c0d00030707070200f000b55100042c1e011002c541c2a01143c1424040c004640c0910340180b041032121404100c041c06000c083e000d1141c0c1803200c02e0b080b40d00614002c12900e009a1003845070001c9492075504c0340042a5501d8203002c180e10140500741502035101b50b102246107441e00492400e1180398810030700800b00051070200e006080c59892008448040701c0c3d20b181c80c540c50000d009103480d000f211409028151000b0085d07113580510b40c6546c0d40580b21078400c0e180c0e00c8240015154060005c00c01307000600149440b15020005081481d0140c0d00030002402c01e802c10b400303c1880c5030032400804201280f02d032400c03518500100840c0c000d4241d55040b140c1e04542c22038882c0110a95180310b5080c0f0501e0314403680d800510081540e008490400100f91104d0780c00304640710b0b002d0100307801030f800e00c0000d114481c15800b0f0340e4850154101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 877893947 1250 877892697 877892737
    0x160c061d0312040c1d060d1406070f0207120f060515120a232116030f020f0f071404180c14030606011707180b090f0a030b0606 56
    0x781103820071038440e0125070303a220801c01072001204c11080106080b211908a04440c0365061440010090403180039101c0d00c041c0c80c00300600300450340d151a0030203043d640f0500307049200410141d03202e22150018468005c0205550380e40310015007840f588141c041d100c034682695460301621008040c07581640c0b40e044041c82a40b51980035044003031128003d01848140391822940010108481a50082d525003c403e070103880003540d110300e003204213034036020121100a0030849111b480104c07411070031281c404a04054125800302822040c9070240c994500c541c514413641c80040e8007081d443c0d98041c8501b004034503420700da0950300c110043c0000c03401e617101080503591002c10f00700490703100302921409c02c54405c51418800410004801803d1607042c8440020480d60080300c101c4215000003001c5002c40b0700a209143c403030950300091002856807040142202e410800040c0c0c02440618102d0340b5901d0b04a00c0c0e01e080da40d006240003065107503003003800075540060890700c08403640b030382d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 877895197 1250 877893947 877894001
    0x9010b16170f0d0609060e22080d230601200f03180a0b040b04030605180a03030b0f0303030115140f070804030c12150b040603020d0506010e160c06 65
    0x2d01c06a02844201c40d0b075a4201403a0f04119010740d444092203e00d800341c00c0c000c4041e1061201d801c000113000f11158554181c40c42c2c0d00d00c00d9450030062006100023466504028a50040c0032240308540307441c0035001007000e01d14500901143c05c14001004402e00c071001c0400e6003812248031038681c0c00c5914082070b066540349142d01180c1c0d03c20540b4070b03645038980b1707a2801c0e15003a0060568404070038103183c40e044003803000d800340e800014102d58440000810620b0300c2102001088400e20403502c0300056400c01500400c82c4020050180707400840d9007585041c000100da04840b00e05143c25103101e04140c00300c400c0c0724050005070b401c050420082144c1011580900882401940d407030b950349165107801202007100c3e42c040300180040700000f00c0441c40d07031000e04526626208002c28518a128006002400b854000070740c00222441e0610902030000340c0c0c14142c941076801720f00b9036101d49000c81841c0200084000008100044a0b000518290000150422100300d10504000703020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 877896447 1250 877895197 877895243
    0xc1201180501050405160f0b030c0d05040b06040b0d0c03060e0c13060504180f06090c0503010c054305030409060b031b0a02030a1107082a09010b16 65
    0x100090721141c0d1035009000c02d0207414817103100d100301046150558585850b100907146203141c03050103203280d0b0200c00030f098802c40d5804c580985000300e6041205280c240b0f80050000b20130744205004902e40080070105003071000303829101603000382a602043d407543da01c03c000b1b40b030007409056050059850481040e00c071401511042065180045032041c00d00f01400110345040340c180e203003c9040320100c030119a900172040320300303908004041480c841904024070b1001e440d0348926015841e010200c0d56899003c0e01130544003010784184905001c034880201c03504000a407291030b0301d01207044040d1302c075961910b0300d0b45010f100385c040d03d06007030f5200d4424003140c0311075000706280b1100101700414130102d61000c071140c9400d400b03c02c0c1031440c17584009507a40501e1a820b41030009040d56000440020041140180058030444200004801c004400809030103000d2800d10721342415030751246484000709050302c0c12213401504000c1110356a07841208001000e40300704107440d11140700c0c48210303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 877897697 1250 877896447 877896491
    0xd020709020f090f0406091103040b0f01050907030b1906180e060306011712070f0203060f240d0203060901200313120314040309050a1a030106030e0f16050906030109050c1201 77
    0x20082319920303803402c0c0c105468806001407603244a20003000044c40a0342d03c2103410340d0000011314000031001118802705103008034007511141c0e1100800b40010b0466402900107420b40c20403032001c82c0003640c5640070441580c0031b503039680d0700d500f010f0014803151240030780c0c08900c0c4070003500701c865030b071402400781180341e0201d4416280c42003082c811000350b090400c04107801ca00800280c4c031746172030540d61a0701c640701414488505100045034240582d07440d001c21100c2d0741e40040945000e03040001e2200e000b0620442031911041e19262860768591002c025688200e2441ca07600e02c881c41d550356091041c0c42c2e00000301c018155503a80b001a68142d0309052403080d03110f511a20f801c80e09090400810070526031103001c0c2d10104101007002c4103810401d80381140d032141000314190580151403410200b2380d642544581c402c89000f200800b00c0040c0b0705048950070340d0084200d4441c442032600365040346070060059440070142c02541d00b07140c442808100c41a01c00000d0b201051389182c14030700c0031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 877898947 1250 877897697 877897721
    0xa15090b0c07060e010806010804120e03060c0c010c0c080708030c1902010b010206180a291f090b0d0f080d02070305090a12050706030c0302040905090d020709020f090f040609 77
    0x102a0900c0380c0c0340c1100f050044113100b403d04078450311f88500003d240000052005200c0b20524610b08850340c043c550016002400405691013441c2c0b411040b100707900b000240c500ca943c24035451250046c0907401043e80c0c91342044d00d1515002c02a00d54140d0b56001a0507420303011402c0121500c0058942106003e6101d654004244041da201c002031600394050038070102c0841c00c4501d0a00c42d5800a400031600342e01545a00ca250b00352014202100b5418041400314002a0101300d04c00c3c2030004003d00a04200d00301c0b9403510340303a8219008495030b404080e40c10034000720b82400400d01030000b49061030300c100449450b00c20998104816604440400c501081010030070324514a08401d50700e015151500741e00d440310b1840e407604c42d9500340e50321881081c180d82d07000088000e44a07070116000b41100303c030184103e0420259803582c42d07403c068043c005004001d400325142c140d0303000719110070490001a60510140008220321200e0401000f503115a8840300000c100c01540201e000803030b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 877900197 1250 877898947 877898953
    0xb1506040b070b07110d08061201090b0115080f0112050a0204061d0f060105030f070c06110a02012a0e01021005180d0503011208160b091e0109020a15090b0c 69
    0x41070380f41c2045440300c050219414820300d445083c00d60400020090052442443c1401d00c58903510f001c07624070300c02040b40081650805104070b0502504040751412034149175000c1f000c0031000542124540c0c01503400645030b400c40ca00401620410044990720309024809603000b003d62503000a0445101c0d03803004415a494151030342c040181d000744181c1c001700300c009003c458a42030000030200d200081c0010b02015403e40810740c4d9a108011154a0590000d010880d5260072101521513030002c5101d0001036003445000078040000307041001101007002124910421008010b880d82503440c0340349411481541111a0103681e107006c1d1a00802555540e884160f603101085414552000003420070302004000400c00081c00481001150b5084204192110041a00800c0f0305800751070241c120880c040c1031116100d404995170354011010304612580d0740760744610074282ca4810300080c1d84840707031090400001c200c103a0094402e207680d2601d070076029240c80850321640c0100541c840b40d54 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 877901447 1250 877900197 877900207
    0xf0c240c01060621060b090114070501050103050709051602060402130908030a0c14180103270501051f05060d0c11030f040501030b04180f0507120f02030105160c0b1506040b 76
    0x1401a200d04c01000c039103003134240301203410501010121712846001d1030401409038922140050b200741030310322199006000b8816541c0d04d0807c1036491090b402540748440c90000403030002c42801d001c8840050054014140700d0380c0d60f0b020002125481e002818402d61201e41010010b1207050040d8404c000143e8001101c1e459494000c0486544030300181c02d01e402048214a40503800c0343c4251030400918000c940700c2144034001030307101140c4801e200d074404081d207a4401c004064107d02e102d4001070040c404d0f0700800111002c0c0343e502074890a03030003000030418103203080c1580d040307550785034035500300001e801704d014600341d196511014111080ca6030226040c040340da45030140010341c1004035800e10810203502d0702c0c48500f0082c11001004905281010030411074148402001440303480440150340805050210070380840040403446940b07004000343d2400140004110280d22a40d210b5411240a5680e010000d0005d424144003060a094062495882c540100050983c2c04684e039151 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 877902697 1250 877901447 877901477
    0x30320070605012603030f100f060c1103060c09040b120a0302210f0904091b090e070b040e0403080901060f0320010e130b0a05040e060403020f0c240c010606 69
    0x16104c2d020b101c0c0d2140400e444115100105490b00801d961002ea00c040d00d03420364640f050481540501c01850f200303e400503003160400360305540603000d000c2c0844950700c41c2c010152614412135092070400814003020308141099480b00c2c105090190040b401c914030580b0542c40c00c00d0a00d42140140e00030300c0030003000e1009001421981e20400c28460804040f482c2000c4103020300090740d802203a07155407002c18424140c0784034007070031204240c5441d03041d01c80c5002c0c130161040390500d010b548550381c0c00050000fa140c040341c04403154500550000d4565075003c5030102400340c10800c07250748030700020902c070040c02000c1c00114403898408214159440c152a81c00c15008403c9045c480080d9020300241c95004000c003419908460000e8540c040c50300280146d00180c0082c0e802501d0520891385500c1d0001d40c02d401503003c0c4d02110075070ba501d40b60b01aa20420751040300c1c0c01c0362044d0020030444060055046694a40c050901c0c180b00d0031203007481c211107890b440480002c800d0b035445a0744c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 877903947 1250 877902697 877902719
    0x3110d05160509010f08091005010b030a0b01020a050a020411040f0603050a0606020c010c240e010e06010519090506010912030801031b0f21050a122a03032007060501 73
    0x1181e09410301900307101c00100040c010170141050130041c809802c00103003d540d8288642643c00b00b01c40d00400c0301c1d50710390114150541007100d40400c400d03c0c2807209080d560000034041c20440e0310100401c041d2865a080c00050850b07005420b81d4050140000708503140356000e4900030704040d9800007598504120fa49055800d00da0028040d5080914400d1150f6800324014441a4203c0b0324001480d44020148513940d004006081e4464645150500307900030640052980d0164817040f58241c1e43c8074001c0142031800700c030455080d6425a4401c020040b01d981029a114a05041482d42d240c2d0710303c02c030f0b400101c481008800040c0544018410460384030012103d84103000000501c0c1401c104400b1454203060203190324448000d425814505548021034250701c0d0700101392528040701c0d251680700e2802c1c2c41400c0c000b24845002520741d801401420040c244500d0380c2c0b801403510306841c154010b01c1d44104c0002401b190707100242c0050b6007503004051241c40b824002680f90300d001c19070f0305 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 877905197 1250 877903947 877903981
    0x60503061311060304120822050319020105010e07030c0201021c051e06031b0d05030a0f08011202060901211a0405180322050307031104050a2a03110d05 67
    0x303c00e00f000c0c41800080762204100000000c3c0314140500c9039100c9104140d103558400c80e13964024400c1031004002c00c0000700140c40440c2848844906040b11400182d098990134043d500560f5100f00010741d617030344641c100040e984802d000041c5070020308030308615050300401000442c2500d034400d0102280a009171415450500380c42258281440000252240c01803d460f107446641201e1201546e81c0700c0c525144115803140031207039181c01b45407018242c2d80139194802c0c04546440e000048401307442c1c0c00c1c0035020f50300404503071815103441d0054401c00c1c40c1000041a02507800c161740e002901500c10509540600040c5e0b0f24411080e408000a81c2c200400000ba5110800e141204155001082e6542c1c40d45030480f640601039094005006111030790300c5a17a0510807400e0000500030001303d040071500c1c0a40e0b085c4016035a10305000c00303548213050342000d1860303072504080080910a107600036030070881c034010503806103001c030b1440c407608505510701400e42e6502c113000c00c58200001c41c00d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 877906447 1250 877905197 877905199
    0x30108100501320405070f020607020f07030303050c0c0f03131d0a020702030a0b0a02030105041a01120b01020a0c0b0c0105010608010b07020607020409140604020109080304031113060503061311 85
    0x80500e604011289001c07100c0d8811a041814101d03842400c6200003102101c0c000070f028000704410300c2c11036401441c0314800443d10015000b50740c0810005440414801c1001c680e18005004492460760220004c0000810004030888184004003034820184542c0003402c0ca03003002103031200803076520700600800c190310000306100301540d51151103001c0820b0a9001384c0e031540c01601d0743d2940c0042410f02c907080b68010720000c0480100050f1604035400345058030700580e01003082d1202c403040c130307010001c07aa207030f0502042081900003c4004981c11034006030307906206541c1c43c0505c0c0d507100c14003896280c004141170303180442c003460706c8002441540d004003e14607180e02c1d25403421070003084600c1f03040c0000e406003400082d560195196904001c840c164401070b4021140101480941c450f0410350381240020b443c0320b0300281701e500c0041503409598204050b450610102e4003004410744040c04400f8406854910004a660f0180f02c403c2c8030300747c400a200f409000e2441c04a40c030000d0022030f2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 877907697 1250 877906447 877906451
    0x70303090803120c090607021003060305071d0a050a240e06010e0604060f02190803040b01060503190e0a02150301090e2802040b041503020411030103051908130b03010810 75
    0x203416100c010003989608128813142c12562280c1036008034046108031603029400c50004a8020b643d240d060303100c5800c41e4040c0007612069911000311101c901144880c106603509024041078008910380c1c0502d4000008490025006588231150705d01c80020a091018080989008201880303070b40c0305080e4890b40c02d1900b03220309040400080c43e00d0042c0d00818041020a148401459000f04098604141600c50588004c542c5203020141984100c0b4110b80c2c501e6010000500306000380241c9006145400302c200400c00ca00c0f18040c01801c0d00541030b42184102c9000d400543c9400d40114810700030301007060f50303075810618007000352a03440c003550140b40e201c14002c0d5402d10448801e5034000740c10a415802640b09030000501400c210f1840c0c5502c5482c00d03080d1801c0d03e4400103100200ca03c01c2c0d605000718a8401c0d030050b209c0c00309100241c62900465884000000c418486005452040001900380100d0107210328110a064102003910500080180032200d401c00c00c04c0030b81000d00f807003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 877908947 1250 877907697 877907707
    0x120b060301030f170319180b0109020c03090907200a1205030a0f1419021201050d080f130e09061006081005190302041d0303061903060c02070303090803 67
    0x4142603100500c00685254180c0103030740200006a00003e69500c0c0720f02040d5281e04000c131901032280940b00d0101240c5142202840c031540b420300d5071300183c51b00008508c43c140e282941c004080e5008480450340e03400204400070b0b40d60750301840325002e0380c40c40d5140d1014800440490404080d200da00340722581c0003656034000100c0c07a00c03060491186c07614006440c1d0300c07201c0c2208050641e4816602c060380c1042001c4d2002212010f070b8522481c0e0300001070000400d0000400100d11801e105252601305a50061106081807c118500e4901c100340c500d14210ba0146000c109420605407401803a405e50410440803410100070743c0c00c1007890000e071010341003c18103680c8040e400d21443c4140311000b0005a0b441c0c8428425100a080240081c130042d0b201c1490000104d4060000300d104514003d049110004054000e28070a500c48006500e90b40307038101048403170416490076094001c0a080c001c000201d0718000d0514a1107207400403e110340c15071401400360020b039000000d0039032040c06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 877910197 1250 877908947 877908949
    0x1033809131205070f02030d080f0c0403170f16050304030308010b0c150702160605250305040b0904090f06021e0c0706050702040219091706060f09180607020c01120b 73
    0x418410804250070402c0e65140035103030685d1040c001c541c020398140179204201c2030554100c0f000b40d02c64041e140c0105026541c10000503524002c0d400701815802400c0358000e00c442200005005810480d540c150400c55000c0c0030300b490025880307003181d89400c003003810004c258200416a000d02441c00f6001d08061448500c25910b501c2681d80e224006507040120310440d009001010100b280c00050701d0405031155005003440d480364181154894151104080d1a011030504490300c540c5541c1e138070316203440e00030505400c1e042805030a5010b90350b95600c500081e440341c049607600b8881c0e1300c00768482d030008a070308440d0810024035204074031003040550890301020400c0401d0b0340c803505009498100b98004a0b0003405060000041200c861200c0d01c030340307034101651074101d034000d0342c00000501e16205819151002600d00c40d8000c42c45040541551030f200e2281d0382e0180810318200311074034503505d41c07918080b8280d4000300036800200203008135580c0802d01c0c856080784814140000c0d140e0394 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 877911447 1250 877910197 877910213
    0x50139030e0105180910090513020306013501110711010e040504050705040f02091009080d210906020918011d0405060c0a0203070f110901091a0103380913 68
    0x4c0701c600c11848a0001100f50014602d0709016041d920340401040c5010f4010046041e60b6410a1384213204110001030704200c00302449040c00c3d00f0038607455154006800c601411a08460000301e15500eaa641441e012503c2c0c0107000400d000b00407800e0480070000c009003e070300e500280d1902031410802000003040c40014010203d0782c05071000154441c1d08040d4100074000c00c0c507810f902802c8403100c11181640681c80006940392003040d1840e2440d130040070f40d940310441032850840310900958030901d600740da01040585014100140c58401031000181e10003080c4541c1c280b8100109005002c62000d00300c0901d01503141c100131100d1400d05882d103590b140350040000010b240c0019651a4030f61003071059070f0f4401d5210903924400d601e94501041c4081d004c01302030b40500c034094000540d00e070780c0b402001750902090200c0503841c043c2030011009840001d104041c4d0901800902c00074055802c0604a00c02c01171480c0c3d107529913000d0070030501c40310140c640741302c0b00d800c4103402c3c01040c604 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 877912697 1250 877911447 877911487
    0x8010216030503060a21061404050a0209130b0703061a04030308220818090703020313030e060c070f0302041b050307030f0f0c110d1107050139030e0105 67
    0x142c10440c0e141d6540b0400601038524940140c4044a14508149041d0074017880d070444191040c1d9051103401c58081280031150011600940203a212000100260034000b0140e500151005040ca090809640b150406110107507004000260750700c0040110304002c200316120200103450341450145140c034020000c06010703254141000816485003070b4118007201c081401a072040e5115203c07442e40c0c0040c0704079044090389600030a40100010000c1d072181c400c40384180b5203610b0501002056460407034080c121005c2003500700c582001035040e442401c1251400800f180d80c0c625800d603095205100a480c100c00440030911403074405061007035040380036a540110355140000c1e1240707003640c0b035802030490740d003003559824944a80b103201c0c0340c0d0020628020820803012900a2049200c0480e501c84485040b40d02c0c40d00100c00a111941c4101070b404034001000b18a1200803a03482c1c2840d010352800303040e014180140d005088201138004080400b00c01003400c0450400942c054916001110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 877913947 1250 877912697 877912703
    0x1614040b0d0515120609061e220507120311010501060509151c06050f030a05030d0b0612010b0403021215060d020402070615090f0b06070b0403021203040302100608010216 75
    0x70b54001a500c8030030a4510300c906040181450b0140d21007038071140d124981694032000c0c0d4015075001032640028000303180c0f52000107991400d03181d601c0084083c0704c01115020302c40303201d1a9982440c04643d04018940c05804a5001d0b18080c03461880c0140582003021842800c990409004100d03080d0400240c034842e00040e646803161400b624800c207482c0c03040d499600c1c500da41d81c040052100420350b00c00025507400380ca02c80c0c010340c810810942d98962921f03009201d80c0c8104030380f031850200d9800060303041c40058005800c007240c041c80e061090000b40c12460460b00049010015803a2012620702150004405007200d01c08100c2c0d00390744910010f010f0b80c044c641642502c0d0031500e440e07048444050f0002c900700000d25481c032840c40300800c03622030900a41c1c11b25210050b00d4655103d405d103071900040c5428904902a80c9501c8100002070042c0c1c15406410480b14641203c1401507100c3c0b84668044c3c09405402c1147c0c82c11135001e504180c0352070303206018090748900c7d00355015840a030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 877915197 1250 877913947 877913951
    0x904080a030b0d080a020c0a06230a0c0f060209040b09220812070914030c2b080a05030402040f0e030a0309061104170c010810031205121614040b0d 65
    0x11860010039901d0200f090010480e80d400218504016404607a0350f02106040b01d003000e40d40d42d1554100e401c10401780c1e1301c1184101480d0340e40340e001840301c014240b428540c141000d6005040e201d119640b41500760503501c41d500011006040c0c81c00340721b000c0120b0004c9a5504140c01c003840a104001c003200341900340314006100c1d00b4140303c1c0e07040540c0c8440788291a98416407600200041001c00544524812600c2d00c16440c2070602d00400d50100180010b0040d00c1c10013082581c14204040c11244210051001d0008001092800780200034a00f1141c0307134599203060070720600c000c50307001146000d541031420750120714070500401200c04000d05442d0119540d041030500070014954501803c4c40c081001500003400340b411b84003080d0415403034040d6070355500140c00640e002101200e451244000030b48090000919140c40740340300702001d19040b428200301c2d0a1202c540703070060342e484000040c400310740c400e000c4c5c6c0881c080b4180070301c00004070306003454825944658094400d88407040780d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 877916447 1250 877915197 877915211
    0x50915070201020f19090f060203090118030804030503130807030c0e0703630f0209130506280b280611060610050918240904080a03 58
    0x907200750151040c40a81c24820750740e0300c018561100740d403584003030000045a0000b90001b4213a028075240b0b01204c1c2d03990061807900d20380d000111401c1c414050401881c658208011000c1103c42000d88050b500c62002035654020b803001800c20702c0701d83e5200d504c1d10b902504042c000900c0404100c8122100c0c0c00c800021a2603102c4147d01501d0915281c003603040c41c040315a18002401401070305d44240b03028652201c0729410400c01d50501c60b038825510a0101e003c1c200c05604100034400241c140201030070301c0301829a07400614040d400743c415850720b41600242c081400404d2000b1038000340c1031425004002405070b405281e40300f000c00d4207041e4580c0c0c1c91089034a5143c42d0030190364200d02180742c003118007000820100c00d080314000c00300040e440003240b0b9000e880c001000c60050300d0051600c036800101c2c8408540c650310030407805800000c104104080b00401f0402240070b1010109003c00588502c03011180110006920174402c08101d0305200100344907004a60800100d8540840c0301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 877917697 1250 877916447 877916461
    0x26070504020d02120a1d19260a03091712070e0a0302030a200d03080127020d0b040f0924060b030a150e011d0912040b031603050915 58
    0x28000c0c6042c0461210300c580c204241c103d040d034810306c022819546042411010668501d540f00d4140d14501c02ea17000f87c01586001c2100c000c1c50040001050706803402c681900c03008002e60780c00071141080440d4035041503108100f0700c1c1402c0024500b990b03007814289181d00b90040f16200c0080d02c540c091100140c07501115031180400e41d0080c1d600903080703590341c55851a040044142040908400394102140d0b59460701d007440301c0341442a05a41c4003c990b90810084c2004266138540444840440070342ca0304003003450b8000b03080000d00403400010100c0141c014401a510074600300304401d841d14140c41c0020b00c003040208602070004005441004c00850408000e1000d03030000345a8030300c080200700314411a5000300c180e4042c85500b46042965610386202ea004080c091105c0000c60315011202c5050349004199000b442d817000c403400740f5089440b040312a030098002006e64500082003000003e0848a005003100b0146010485c40c40c280207019121001c07001c0c20243d200100c80801c001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 877918947 1250 877917697 877917701
    0x90503040b04230609030703110102010603120c0203120f041e05150705011b081305070e0907170a170a0e1807021b3a080426070504020d 60
    0x242014501c01c80c2c0c1c0d562164400701c3d500d000800c0343e040481e8503c000c01860b00b01031066070110140600100303816415507551072410014000385034111343d13886200002042d054840c218803440503850741500c00b60540189424000010b01d4903d6000303041000300c1040031540101d4088a034011043e841502100a02101ca4800c81d481f05500c13048c51400c00b0284144540104403031445140200710000c04403101c149004803400071300000c41e82d03102c0000c0501d0038501c4401201d42c070034416a04e42540f10940c0a030ba041003550100d11f540d10032001801282e030a00b450030b01d0b80c41c45800a00d00075036030340d03204500b0a003c19200303480c0d1751021501c0705e404c6014594018006100411040c001900341e4421804148200d0b0260b00520a0603c9031300c1e0001c41007800d481c81300d00940340064541c64240c211810400d24480020203020840990305411600c000d5820170512071210b00d076440e46003d20000a607422048185410040c0c440c0c580c500400004928080715170580f0007507203d600c04055440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 877920197 1250 877918947 877918949
    0x4140d21060b03092401030201020c12010b040e1c020604080703260103080a0e060a0c0206090a0504050a0203061009060228050a0b010e070912060f15080706080f04110409050304 78
    0xe824200442404110940841c0d105c0c00700901402c03004542068024200b401d00c0284000b03030258000000c0030700a81003c4030444001c980660010030307411b1010000c10202ea16040070500d603504040d03d9000c480e45111802e40c001300181c030080040d401c0c41d4694891502c05d02c0402024401050880703404a4451310000680003022400768006603501c0c14422290380c010300e0141e0005201d010040047d01e054002c1e42c00560050352280e419071429424012503900c505e080310b43c400703250140000c4c06d80d0f030b80c028107202d4600d030000580c4a0074004c0611060200b008001014401107110611410f58009549500811a260009600c400130b140c10041004264000b41560141414003001e12042154050490310885241655a541c440040741d001846001c0c41002124501c0700c9004100700f40c0041041a17102940000e01d5006001c510202048a60040074203070000041004074680090126511160100185411303140940c3c446410b20401d0f2501442160340309000b0080c0031080055034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 877921447 1250 877920197 877920209
    0x12070201060e130506070912201909200304060f15031b1712210f040624210606091e111903020d06030b04140d2106 51
    0x4041801c14031200701c450303d5803190580752071040402040009101e08511011604e40344445030510605548003484002a42200840c41001596440c06603807650800b120703028181141c055180c0c83e01500c072041d1540f441300b181101f1030050b024010140c190703044a500942c0420300088c80741c0d00c10000002444400092076080008120110400020714181080520341c80603050103071755104100302c410140d01c480d14289401402600115410180c01750801c905c4100d0040c40c07421204c50501102081114407c2c0004d1140b0103200a00102d88902c2c0d0014044120000b41000324140500e407640705031051001c05c2c0051541c03800c40d148284071407c200c543c003031010711810765211088005042101c1c1ea40400030001030310102c8010503842900b2252121401d060300300001d91100012600703008c12003109041d000c102c05030140e00c19205002c0910300c00c82c81c102082c1040e050440c210b000c001035020707003a0b1110039210401a0005c4403101684602c011038041c11103221200d40241c01c4c168014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 877922697 1250 877921447 877921469
    0x5031b040b030613060b0d020f09030f031c0b06070f02041e020a030b0f09010324090305070605010b03060a090b01050c0a12021c080115051c050f0c0a051207020106 72
    0x21811108040065003e1501110b4102d50b0004100401c07003183c4e6144200c1c41e05403020041e00c00c000303615070040c205034100700014030b040000c490040b1f82090707400e0005610a40000580f520070034000110850420406042004800d0a00f00411003038452040040c00c000c44003c50982150f940d40c0090120303c1d40484060200f240340107170310020b900020304000219007451034880b0142010701030154072180080c4071742056440c680f01c64401492408480503e2880500340001501e040d0060400081c0309584050f541c0300c09081180495030180c2140d0808103040043c0007865803103004402c240c03036058400050003940e6100603901e51240c55860350f40750140c0c22070002840400e40040c15040582c0e0240d6441034a454541c8a07600c80d1780e403a18006c2400e0b80c00601130410070303a50007003150206040c660700e0880000740f004880302c000ca0114000f01d4951081084111050207000d402a003c0380c41035007026892a005000c3d80201020700401102240008030a10b1003504104004e007503413266 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 877923947 1250 877922697 877922699
    0x2103051b031303051014040f020406120311010c0801081b0103060f0b0309010f11030f070c061a0f0105040513090c1a070302010c090e1305101506090b09030a020105031b04 75
    0x82d2500e910700d14402900d01d4003070100140c8501c4007901a40d0320344140c010125501d640c403981d5004041e2195031017a600b06540d200003003111014200c560291038003c2c3ca60303201500d4888010303400c1d14080a180410458004010400e0070000120b03e46207000303046d2408502c02000780100c0003403185030b000f110840d400440000715a040d034001036000340740800c000e000c9040120403410a94198420300c0c01141d004100060844036904402c540180d0300d441c000c0b5408840d40c940d003054582c190040709902804000e604158940101e100c90700701c6080c01c0c19400c0c03600c0c100000380c0442410207110a0a81c031610503000708075200d0200805805030304000199001d440a85144907000124200c000d5803070708c2110503c4501510b41003045030400100800165038607040f410820303000300400c40c0d25100303051400411130002d004003203200850b115801c19031458100c0c003c1c00e200b900d0b8480c240480041200328119200401c40000e540d4080c205075a503900c8002d521500c18200e900c103040790700401b0030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 877925197 1250 877923947 877923967
    0x1030609170d0f050a09020a0e15061306110f1c0e0d050a0308010b0f0a0c140106060f09270203100e01080a06050c03090a15150b0909012103051b03 65
    0xf221001a9515010030441940c0d103c5000d01140d00003070300a5444441131a0800c10600116940f40c1e00001040380d01e400800300e2800b1401d103810040055007580740030801803019507440342d00410341c1001c800c020a02e100d03004441d40e84841900310041c0310a0503040700c141c41c0c20f004a8001101240213807101d940030105041c15500d030484044210002500080005014003846084c0c4d244110b180020b107281c0007451805440c002c03070f001c00c122106081c0e0801300030b48150030b1041500404076611900e0100358000340042c44200e542d041b070382c118900003500c50480380651005280d4415085030060352a203c43d00d0480070142a6880f05504400210020410800104045520314400c1c0c4003800b43c5d4a402251040d1401304403001c08942e404100b281c0302250f40c00c0280300520201400010b501c41c688a940920030310075800c50b0b03900501c0010400061b04001d6034041c010969110340ca01e00c1d040740c2000b48808500000043c041000101ea2900c440041c00c40b2841e5254107082140d035650713170041c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 877926447 1250 877925197 877925201
    0x70507060806031f090618050c0901051203040519030b2a0a02060f0723030108121e0a1206080d030f0507050a03050408130602060405060702010c0801030609170d 71
    0x2005100010306000c010031164207001030361200104c220b42c503422440390390301d001ca00200505c680554805484105a891078001c2c44001d981c441d000310301400c62100030000380000e480c0c043e0300070790081404502a4601c11000301c01d840c140c1c0d40456044a01c480ca500600074090240d403c06030003080d5000034010195002811088020211280400e00030701002e03440341540254402070000d40c01050010718070755101182503a21500a0030940b8640c00b41c8601034000307090000000b58034080000c0140101d0100304a800000761403031907500d1030a001c140d02070310708411805080c08280004902001203034041c81c2101244400760000300082c50303894803200d0765003403021001c00c086490f10000407288070361401028850300064032500d151541600f1300b00c0061500520070f494020701480540f40d62010320200d07100401c09580101150b040c80e090050900c20007030311f10410f5a2500000300b4000d604240c0302411241c0105002441c4105c2c2e081806041d040401907010381100003074010032a004c29 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 877927697 1250 877926447 877926449
    0x9040216060e15090c09040809041d01231b0a03180c0524040b2203030e130204030f1103010f0603140714031b121006140102010b2112070507 62
    0x43c0c40788107115141c0745440c685800381c82d0420342c4c04c14041c0f000038021420081c0107280e0b283d4080e00000c2c0c2d92030034080c0108044260440c103070b0580d4582e13500303582c0f446070540328031503116a100d9400824149400e000c0d500302b09401200044000c04101221224046d5105441480d1050900c408101e118035000064401c1c1c4e024035072242c80c0300c0c80c01100300d08450044c5403c5c0c0d000042e07854541418802181840c0d082a000d000d059160510a02024000000d54600842c442e032154815010721a041084da117031041c200c40107052040c0002c0001c43c919422580c00c0c103030040120700c070000180e400700e405042c0456070b845019050140000070404107802c00088100b1013000d4801d460b444240c1d01082e524600d10481d4540d1004107a5520440141200009094014681c20365910319005440c1000ca0014a040c01c290b59140200300418440000101c0c44c0400d02c02000a40f01c9a40000e000c1c0458039620705030504030220381d8081503010007902c1c5a02c100000c1094440503d440c12035600d43d02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 877928947 1250 877927697 877927723
    0xd032712140306090402090c04030c03080904051312080c0433020a3f050901020c2704020a080111071112030f180406090b03010b011409040216060e 65
    0x140032401e0005800705040ea40180c1c0010060880e6889907002c225600f03602400717582d01c2080401c00040000c4081c00c0b600c0040d441682c00c1c80c0c50703006080800c4100c400007029081c85010071200c0100042c0e80b540c08400c6111785040c0545030762a10110700950780565044804032070034500a2000d11400c000c800010400b145a80410000640b0800c0781c036602d006000a2406850b42c030400390410130250069400c50221032550000d000c00c40c3e0081e0440010610840840c0b00043e0030011035034180100311480f00143e40503820700c03034104038188151501d1074003849510314010100c4c04540d1510041801040b00d1002404101452900041c0700d6010140c210b030301c0c40343c805010300b060400e0402030055051003c0514101801c6419080300e980c068400d40b100d14220221a114550360b910500d0084e14410000103150742852084c03608484003100b945041c014101c100c2c26104184900f01e41c3d030400180c03000b40c0c0b21000c0c14448488145850001418142410503101c110080000d40022801d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 877930197 1250 877928947 877928957
    0x360307061a2b0516080f06010303050904020a1710060e03070f060f0e181f051e01050f21010605092b0b040606060906050c0d032712 58
    0x8030148100206640201078990000624210318460710b15000700004280080340c04040d00401540d281400c000b410b24285004256071403051110020400a5050004c86440205040d504548029202d401901716441c030403070700000d43c01000340c800e13240c00307000a511395802030700c1e41441d503506007034034085001b62800586640e803d00c0d0603140024440080310020000c0d00e660b50b007040f004031030341c00300c140c0c04071b007484030075403c403007154a41580880800c143e4100300c41a42c1400c81c0101002d40c180b001582c0c0221304040140300350b84e50951104412500220242e005201c01d0005841c0c41c000c0c100400c18600000c00c00d08020fa1040e642516650007040c00d180190380c0f601019a024050011201e0300074501c00301e03108003444403c01c0002c1042400c1c0c5c40785150252540c07603072086002110116851920f6035020040d45da000103010003c0c0580d03052882c2400600344090381d0303805481040d401003548444141d0040e0030703805040d0310380528a1016034101242e60400383e04018000188a0000e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 877931447 1250 877930197 877930211
    0xa0b041802130905100b0c010c0813031d040e0105160906020601060203040e132405070c110904141204051f051902120a020f190b36030706 61
    0x105920864501600c2200303032180c1907061030b90f400020f1100818100e00314200003000300ea24051000900f00345814400003146850342c400000b4541880546140900212000c0c00d0000980080307013840040201d400002102d00079100081c0a011140c941300c00652924083c801420260440280c1710b180380e86840098590b1041c080713985032000d102c0c00c40140c00c207100c00c0c044c03503500942c0c0c03503000110316000d0994101e140c4c4a8001c00300400d015210505140b203200e012040440c02020780c001828202071800c2041e41d15480038021514460500c9a84084000390400c603c40144860700101d82003242c0c404000500301c000598003c0c0615482103001e000b440d821910b00d69180c08a5004940d83d15013882071400d60f921050030480345034401d50049000145585e440c09000d01401079550f401400c0e501d40014a6500b0304800d0754408550700e9081d071100d808901032004c1180c0164495036410b056101d0001100100e003a11000b01c551004030305842a4070700c01c000b01400403540103c4080041e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 877932697 1250 877931447 877931489
    0x190f050c30030702060408060a060509061011070e0106170a020a090b070321020403060b060304020d0201050c010902132a120b011b060203220807120e0a0b04 69
    0x40440048800400442200c0115603041d0340e41020001034000320482c0d041120a50020381c0c6904582c003c41100d130f1022040010403a810302844006103030a58611050341040004110114240004402400184104910403190400441006060090719039480e561590002403a100c0326140e03410030182903c0110b038a405283c400c485040713007151119501c0d00c6ca03001101c0559049401c0c00c2d001d100c1500b181c1d00b403a107212200d18401016a00c001031340c0ba0304624100003190f8144041c58000d00050003000f006132101800e030200c00360242049901e426034290307100c0c050088160001d40001c01020024040a4103404c00e400360022256441d104984076030100030000c00c454181c0000a494038040b130303c1080741e60301440e0302600602d0a00c07103240f082240b2200c00c071407054044032415800010010141d05c0f100b0134018000c040c003801440708041e80c07076a0107103014114020b4000a941c2c40704d884103130b0081094000703c41d40903003072020aa598170b00c0303602c0b26085407051212041c40c515140000b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 877933947 1250 877932697 877932709
    0x203070f110f0c0d020103090611090a08010608030904020f0403120507030806030109110121060f06090501081b211e010b04060c1709060d0b010f0302030402130e190f050c 75
    0x501d1812002030143c44001c004208400d04486026414542d0358411080032880a0044255010580d01069036030500e80040c03100080c003d40c03242c40264540704050000d2800441241e84000c4111000360b140c4407041c0a00f0154426a44000c000102c0c1031180c2c54200c0d0010094521207000303071100d0b1900ea542005260aa0700c244000030424a0030b050030910540c01000386e0141d01c00903e0070302199064080910048450903004110089010035040040590080e106000f408007860315210500708210010b0500c0d900b12100803608402080c041c0102d00c40080d40c0708202280000110903080060700b00c55141d0707800d41c2055502c402d0030000703d694240c2d40c0480781210140d039650320005403291154070b00580c0301c4102c5050080700700b000300c50a651b9803000d4019048202c00018040c0c1085002400301d113441150041418014003c200150350341040c100100b41d500140030404441d030111203030138134000590f4051489000311042061041420360604180e10840c202d03031480e1102010000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 877935197 1250 877933947 877933963
    0xd23070506060405091903091a120c0c0309060409020309121821071710151514030a0f060504140402010f180e060913020901150e040203070f11 63
    0x4555800400410002d00302541301d181d10280c42c000f62149010030600e00d00720780e080c400b070680010380400707000e2000c3d8101001900820700000200351800804154139070328030303200801d042070b80c0102040c0d20300e50b14424011120b961070300405841e610364803801e03414000e400c1034800001c984905030000d5035180c4408200c50205480c1a045030440e4003050400c02034402d8500e1740880e4102d8043d240b4100ba00c2081484040c20303c0e1511848014044166103280c00320018a03000f41c642021040e2004800d42101502034482ea101044200314100e070064582000c00000e05d12100d40000c10050025415884624400c407800024010345549038200010303550703015100118982400c02040066024410786062103500d03051502c81c482407060036840c11358065101e481c03400c07404000c0007001c0c07516003003195109020341010042e0100035000f1580ca19414007462203146805036401c51138500981941410000c010015996894140300040c58411030911301b6004ca0307103801814002110224085c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 877936447 1250 877935197 877935203
    0x102041a03151e1203040e0a0905060f072f0d0e041103150603060a1221020a0302070603051b04120302011812031e0c02011d21030402120d2307 63
    0xc00d0f0101c4000b00a03212800c074402c401d051008004c00a600b07445601c3c078034880c04020000080c0d589031824040d050010007001c04840c140030034108030500350401c40c2c882480c0301d1560601008408a0041804440000300d004024800c148510300d41036800110b581841c0300980d003c0c00051002c200c0e240250100791904034118808a201101a080400c003565220b0b200400044007150344915040d40c15101c02026181c40c0410400c01111808001c90b400040c00c40f80300a1506140030b4a00944911090252008040d200c1c804038004041e800c182c55a4035040d0820242d070b0b546e1310f1050540202c1c16071022405542007400c100b10b000f01e50468110b1564104244240c04030b200307842240185450b07d600c0300c0f62041e520619402034054825007008045c00c0e0000101ca180000c1403018480d00c501404c409584251050014601110704000b0b400700c0313406045449450b14400125000741c540d0044c4d89510480640b5030314154001c204c07249008408114110300e8040c014142c941d4031400c0405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 877937697 1250 877936447 877936489
    0x409051501110313050d02011b1b051509100306050a240206040302070e0c130b070b010e061008090f1c03060603110703050d06080f01060614090913050102041a0315 72
    0x5c0106040150014002ea48149428582640d000003501e030b000d82c003c00141d40031900182901c180c600704501c3c1d18040c0078212050b8070104100510300c0340070f200301c0000d24005d0701e126072a00817840c002e4200380e018000c010001460141c940b80302e402d6545108418901241d9512071102c4024008505203002e40d800d503028100789420304140400e61403001e04a450724200c10031808003c80c80c0c0001800c05000d003d0a0699079035200d0074480030451040e0086407000804000b40020f580d100510a03229442c5401d00400a5a4030422541041e05a0b403c503a035500420740e035806890510100c40c0d00c4611151010090b0603100c00b001c8080700e0300c05850000401c1c0070080e000c00709000b5030160500c1006a8030103c1c07030136102c10840d8200b40300e044441c080c9a4445609001c01500f000b0500b601c08892600182003422410002c8c0200708050100244841e00244140500030b0a40440b0007429034070030f4024000801061300071142d0700480d82c14400b0010403205001e45d00d040c3d0485440d05040d0010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 877938947 1250 877937697 877937699
    0x305030f090c060d06170d09050d03090801090c030b13120503060607020d030206010501271502030d180c060f02150a09140303010e010e2401050409051501110313 71
    0x100340454200545214624803501003102110780c1c81e0300003000b1000200102140862400340d43c0b41182d2100f00001c40d040d0080b000744031102d544804904c0c200c500c2260558181e4086040680d202003507a049020107500b014035410a003c03189100c0c03400c0760301c0380c1340120680d51781c0030465510307440240b0004d0104000c0c400350281c0300d104101550b0055402007000380b800e000d650025281c9010014107e0240e00301c40300420040da080301481c0b03150212005850800d02585051002c09080d038010820365103820760840824920030410740b0481b61400c9170802c501400600550120448484200d501c0001c075580840e46d60310032803030031004d07030841c0e0002d003c5460a99442032000304003d0403621855610028800030500c120b8508918002e20005144d82e0b5040c03014404800405030050020320b11640c003402484004061041d00c0410000800084000c00f4801201d0030701c220b9004003c000d040030180044c0708840060341310903030707002d8a42c07002c0d203401017459a8407401000d80388405600480e02c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 877940197 1250 877938947 877938961
    0xe090f04052b08041a10082104090e0106170705130c0203030703050414030409050a1805030703300c0210060501090b0306030708150717040b0423011b0e0409030503 72
    0xc119000740c0310b9040c010307800d0316180790450505c404440d15580c0c400d40c46000c0124030ba05100743d5a800c2c00c2c0c00368800c514031020500320402c1c032403449010510740e52240d1070b58000000b03512500c040d000c001b21100d119100d401203155100418041c1c2486600c00d03c10b052160800d80c86558010011034014505582e11f04009800a00f401041556a010390101d100203418003800100040c01403d00001100d0405441d00b808540225030101400781039118006c011403000400e481c09103038146480c1d00e03030324070740104e08001007161903100380d00c13028030702c1030858103d859040b04107a0601d541c00c0310ba0306107052281100351a0b00344900c50103d0706890040c8202940c0704001c6600542c0901158041641e41e070b8110f00c5e04090400c42c2030100554000c0c016159440503206200c40300c001039001c103c1c20580c41301d9100707450107400148074004200c0710400e00d4a0060700d030407204555100030003207881a0030070710000f4100c14511600140c0c100000e60030f87e00c0d003882141d0805030103545490555603201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 877941447 1250 877940197 877940207
    0x6010b090112090c03050f212a07081b010e0a052d060723010527190c140a03050604080903070f1221020604120e090f04052b 55
    0xa01380c540c000310b101c011001c90020003141000504200c01410002c415400380c0000b4580c0440e40c580b0054108910701d01c2032044402c0e034407004039a04000741e501c3c4124203d030745031554542c481203040c001e2a1890210035085041c500e01a042a201d4200f43c0240d1810002081600d005440d8001010f0202d040e40014054845040070003098072a807070032000071f0009038144c201c0007080380c0b10042002d104500c0020041c88443d98444400240054200184400460040d0040242902c040c1d91440d6204840801071045403000c10071040320041c00b1424183e042580c1800740a0100825501c800c0aa0401d094054116a00a0050b1001c0d44507680c0307002055010b02d202d46e51501c292000400c601c1010300032000149074003240c140440000c5e01d400360741e403624001d1148080180ca1400505150003042c425801640464100c464082601d01600d4011700101d01d19080506401001320004006040b20301507405803080715408480441026401000c803c54611080c0c0000e0b01070003400d0281d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 877942697 1250 877941447 877941461
    0x72d08090c0d030e1c11270a051302060c10050108030705060a090201170106091401050315152a0f070b07030302030c040b3606040b0c07050901031406010b090112 71
    0x240783e21404241040170f1000c0c0000240103440c6c191a1000e802454a05035502d9800d44c031803050075003018070b008540c00744100401000d10307180c9501e80c0000b800d551101c52800141c02d0b80103007210784945180c04820303a0741c09040d0382030005500d800d0001c901c0c154000243c0700050707881401461290396288512004c0c25207518100d042c001c24540c1c81540c3d20120007a14040c00040d07650301e001c2071800800030003180250001d5418800300b0820310440e260400b910001c060720984844900803048105420380e8883c1b04c1801c1d0a40c038a056a2005102199040b4090354207280c0443e040c040710101e11a4580459100301078241d50104038280c00207000b90080c0d9405614008000d00301a40c420102000d6807005542c801a40c805906000240c18840482c1341052100407500207000d00340408920130348500d00403215940e00205108452510403c803407800740c000540306041c80d5a60f8035100122514040c41701000d030148400200781418031005071500c1e0b06059642c3c045509010582500074414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 877943947 1250 877942697 877942699
    0x6060618030f0f250b160f02030118030e15120406060506040f0914070203030a020c0c0d0f030210020903030a0e0301420b0d05072d08090c0d030e 64
    0x4001c1540e48040c1c1c03c0c0a0303ea124a0080080c04441e010807802108070210041e40099140e810501800031031a6002030741e060310407000c607041130341c40306080441145000d545d0082d455800d021445d044008520b04d010300303461003600da4040742c060702e0080049a00b0b91103100c4948145c1803242c0b00010040c45541e9030803030300072a400264a629040850b00d81d5100c1c2d08040c108000d0110200441e80c41c07482000f882e1071a20400032054200500025201c0c8005000310034519008a41544820341c203200850003148020315142040c0300a25140d64081c405102c2580540118004020320072414002c484110100030095850090302c2c00c4281ea04504c00d6404035015980ca010000c030052400d40e0b02211020426000801d4210000c82c00819504a41c64800394003900c00741008003110083c180c400c4094880c6010510380e9070314404542a20603546c4100c0454406107541d05d4007000c0080104001845541d041102c0d51441241a51b0300300c4015015048440d115207180440c0c441d0030b4085038000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 877945197 1250 877943947 877943953
    0x5090613080d090614070c02010807080c0f0304060605150307021f0603051905070602010e0c04050a2c010b09010b160320030c0f0601061e020c0d0b06090106020606061803 75
    0x401d42d10030b00201c03072010304210384c0d4954a0101d411084c0c2c0340320034240d100c900e038904030074121100e500003040814013400e0041808020070111b4017400442d8161040d01c014400100d4891901d418280e000d0950b40c41260700034003000c5202c8a040c4503140403203100d0310040d00203009600342c1d040e4041316605c0d0240105122a0750350b0300400041d034140012515450700803142102d100d19820454203225203680f106096a24000100160020104010b07401d4031080360300207444d41d100e43d0020050a00f04030801000c040c030712144580c06851903250154202140000c00c80c103401c030f07000d0004804081c021035080d03440600c02454140440c41001014510918000c0c2502617441c05642501c40901100011a00003195a40020400b00941a407404071603004101c08d51500d540a00f491042c0700980700e10764210f48091011900810565407109000b40406002c546d981c10001d81c2d511040c2c0d64107105520f01030000070094030001d141030047d80b000f08201d1414903a41041c01100079041c141d0b42e0540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 877946447 1250 877945197 877945207
    0xb070213061203090f061407150219110604031e0309140c01080a060b07171c064415010b03160306064505010f030509061308 55
    0xa4540107103401024508007004003024646409802c02c402d54200070348800302d40c8010042c0992001c01c1c0c103030f8a901020403a9464009040c02c02201d020141c008000d940001400502c03515959024081181c07103554040c0180a46502541c407600c050307801800061071010380c030b502c00c0c9460311540001c0205040c00a0103409035038844080ba50361b040702950641114000041c81c0d40c20410040c3d0154407407000b00a00c1d4249003c0d400c59008851000c0c1c00781800c582005409420481156410100c5ca1611074840e58071015000103011180140c1042e10394100f4a140542030540b100300c81c100301e00e83d11284503c035210032401481c144210301c1d5103d2007040450050b510f20b60b010180a88000000d550307480ca01080320410104105a0701d030101841c2c42c03020480c1d2580045240d084803a500b2090a0300b88284c114840200c00d8210b032074005e0b550113010742d1141c00e0b84d034120a00b10b130f03420380301c41410a105250907011128100d50034461a0007c0001640c0324641c05e0425144070300c100d80d81400d00d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 877947697 1250 877946447 877946479
    0xa0b0102060f2d01060f05040305070b0a0504170307030905100807030e0a02060c3316090905090f01111606020309011127100c0b0603010b04090602070213020403020a0b0702 76
    0x3422003c01d903440420781c210040c0040369002d0212580c640070f90400300c0ca42895a13071150780e100001c1c800d40058035004624504c40178803a004030340090084a80c2900b003419020388454070b0368440b00046021811140e80041c15090442a020100c0081c1d01d03078220f240c1d14564140c2c054011900c0b03210990003202d0704580141d40d1100506200120300300108900e05094014030000303240030500002c41105c1d0a0140f2583e00c02041856003d070024444103030b0500040800e607506141038000512650820007000320880e0700007010180585801c00a00c602040d0307891714152403188d145290043c510304c0342110049485a00150f4018480d000001660074000074101c88940040c4007e01c40700c2401c8000b1480804a6403401480c81d10032240192404421400540070a03c206401003803130085400003410340e9001e5120704d418902c007a10920210b400c07407610400a500a030400c80c030814002c0020101e91400d4400c1d241902d901034007102d2070504124410035690488070b0120380c00650038501080f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 877948947 1250 877947697 877947751
    0x130e0109051501050a0b0406032301060224150402180406271803080403020a080a11070e0106020a0f0c03060906020705011811150c011b080a0b0102060f 67
    0x9880c0541c0c00303407488400d0806a109001010303400240318815054040c0040e11003002202c04460050800084a440138403004032000307070485401c07840660603000029296004545d0951602080b41e41c0c5941c19076600f0304501ea824180c5020001001222040c4170a041907030007800d5842880b06010b22001c04100000c1c1038400c0d507040040302c00310040c0c1e01144144450301644103102034080074480c6900c448203406600f1000c1c0c0c005002c102d0000d021505040c020301840c0135064201840b10355680f80f0320006480d15000e2003241041d4495442e0000745a1048075020381628441c0d406082c01019075195000426601c850549051814010020006072070744168400580f04e243e0168695000303041860031a030007040d0074000d8400b2401000001841c40310060f0800710103c55141c065201042003c20038020014031a8040d86848140060201c1003a0304850010150380c1c1c10f4070b241e41c2e048914041c1d0f40c600e0100d41c0942e000b1004200030300d044500050b402542c10b11003014282200c261280 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 877950197 1250 877948947 877948961
    0x103060b03010605071401090210260703050601020f0c100f021603050a33020c10090b1617041211010f0501060e01050405090103021201020f0a090f0f0311130e01 71
    0x101368002507101c00c001c02003500c040d0b0103da0200800c445441034002ca1484850485282c080042c50356112120417042701c0344a11840503c1050007052030030700300c060000c1c40d081e075205025218002046aa512000134040700710113025000000c00065800151512180d5a1042041d406110071440803000000030660045000e98010000c860181c240034901d6060b413500c540ea1225020305115400d450000c8060401d100c0304401607a07411403038115800d048000c4540b8881c141090440c40c00e002034540034074040c040390301304075a202c102c46070f0a07601000c005082d0121a50710070001030219040b407001038120034460410040c40a2510810713421200f001404d6950f56a842005000303865001000300d43c2c81c4005c0c00c09901d0f003420100014990041440002d03c511203981c41c03000205800e4041c0c401c514804105261107071030414002e020550140a818070440c00c524000500c11800f124103411250421110000c1a500c04248600c09568258150615440c8c0001e402c0009007445098 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 877951447 1250 877950197 877950209
    0x3070207120308070f030b060711030106080322060302040503060a0c140307020a030201050c09010c0f06020412120e04091518210207090204050a06081302060712020105181b0103060b0301 82
    0x40d0180c9072000e4050100c408400e114010946480100502c9403104022603200c275402201d0380a00c110808000381c09044a50400311075404045110310308032002c083c1428400070003440003172040d44c640c00d04804078065031182903415849140451001812a80038088440e03a45c41d08100038480e030001c405150b4003d89003600103a20404040050560a100701030700304840c03040d61403400c040000002c1000d07681c0d040142c00b4a400e0180c1404011040c0d045800424001986952102850804035100c0040d1302e0904041030900384544240d00c3d00388150070400c0e50180c26184109030001c0c0800043c044d04814024181150040d0130208040701c1e03072032445c01d0411400340c0880c490150000d0800800d9440105440d0051100303002550b5006a240203441c031520701500180d0307404004c40c3c1e10a0b810000a500a40e00141c140b00340086020300380c9030390210707070001d104e50f454402c041080c0100b0003c007070115410410740c2c0d2618420111425030b140805140200c0c1d0103499280c018840e90081c5d03c84 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 877952697 1250 877951447 877951457
    0x60902091e060d0803070302130e070302090117010b03181f0b0a1a03040b190e10050c0c070512011418060702031c0207060908160c050321030702071203 67
    0x840400380c10001c00d56800001a101d12506890070f0751551114000a009002815004140380030303403144170000e6100a140c14800e0481d503081c8514082c000398400b100700c9001400c0b00d0043d019840c51114542e048500e480c070700514590761794054001d1252000301d0100c9500a42054407013003000c91303640030769007484010000741c0440da21042210704d6410343e00041008001c0307000c0c440c04c10025000d5030381c4150800c105600540c0c4421b10310301c3c40c40c06095017a1b04289000001820360701d0010b946810085464810402a262440c910090b4090307603103044115800f109052101e42841104c04c045c2e200c0490000c2a1560395401d501040c1c101151801035658612111087c040403c00016400c9441d40c00074603e4514800300448208101400041070960005202020410703a584080a03a036089134031942c942030412210960629452010342c1d40c582110004902490301160004010411080b20050550504290788682d0001400f5000b54002c40c91300043c54030b40207981c3d038051b520960790 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 877953947 1250 877952697 877952731
    0x90209120d0e1c08190c0203070e160c0210031a150d180b04031b08030a05090c06090105160204060302061911060f0402010c0f1529010c0f06090209 65
    0xa1140078149a8443c00d41d519440081001085540b003c80c3d60503d281c0f002c10b15410b06001c0300750340c400384140009406204080f80025001c044081d00c074002e0020341c6102446c2441d80e40d0441c6e2004030301102a6006540301d2090307103083d000c1c1c0d0140c40420042000044030024600014202c50805a200c01020000103402810540c2c80d11856004040815403010742c594030b921110f40c2c0b4800200001e05010030400781da6401703101c150b0403e60f426070003d040d6913240f81141c49500540000d032040e491a22502072460818680f090946d00c5e03a030010f075103490030032035111101d42001413580c90503600190364800c04400b503180c480007003d1484070002028003000d49124000c0c0720100700c00c4444a1a008481400007428800c4001034200380c0901c1e06801c0700009050040c0913148400000f055038610000540d940b40151f00900308003044140c40c07590030000c45088031b220080c0e0a01c42e600050300c00e40e8400000d030b86c03c100700317a94501a66000a401504e5404580d48143c1607d10440595001391 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 877955197 1250 877953947 877953949
    0xd060b130207060b0d080f07030c1e120903051b0a050301091b0e010305100b130f05090f0106081c050c010203040f0b090c0a06200105011401090e0c04090209120d0e 72
    0x19a08205000d55414410b941170b92031b002c2840c060880710042c1c0381c50024000c001e01d886100e03100c1240303800c071104030345003000f810b6071020280011100701e1b40b030000c06140413440e49c05500d202045079045405800245888611806094242541313203520480513440030850340c0b800d00c01c10200d0761048025a01d000d0801b60000340050039940301103035262106006200007a804a81ca4600015200b130100d60300c80c12400088082170301c1c10039140c40d03d1500f5000324070040f031900840d02031201c11040d100c9906451025a0a8510710b020349503866004040100291004040481c08008949411030610700700103021800e83c3c0c025101a0b40e040c800c41618030a0145098106070801c085a0003442d91910f2080400c4403c0300a00c2a00240940c0a000708a141440008145424110310007009603684809044c82120900f0280c030f400a8030382840440e04000400c151805044c10f0341d426818189041c00b0a000b035800f680301da6070130555111440c168200200860030102255840b40d407070042e5448 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 877956447 1250 877955197 877955201
    0xa0b01091d0706050702130b040f05070e011407140a140102030108070f1202130f020c0106140a0302010816172703090a05010810080d02060a150f050d060b13020706 72
    0x100602810350444038003005944c3d000811100c81982c1a1011904810b800342400001e105400405400034145940aa01545c0543c80188507100710f880c1d48070003006520044a51400c01ca00b038000b152010042c6001007482c03e40080e151a0300d40044544091403640c8036860703880051605c400b160f40200040c80140b000341b0180014002c0844410612864800c001c030807034071581000303805400704544e198100c1d09150405110414030090655481a85000c1e55000f07080500c905d19102803002e060b1845440e00740800c2c000c4a405964050346d507202c0412080c103c003907490300c400603c40000c0c04500f11403101d00b440d5100d4003d210148a11908043e100e04200e404d408680b20603820400100b40c140da241d42d1850141c0b0001c1c40c02045aa403102d03680c2c05011a180c00411040c400c1e0044d072542c643e4002f0f040b6101c0c60154205206c001841201c107059070711140101c6e405002c85d15030501842c1016800c8540040c014240414086070701d40114445100500c2d10700e000c00d40018070501841064 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 877957697 1250 877956447 877956491
    0x80c0f070906051f030c03270204051506030402120c04090614060904030f050c1203010f170d020a02010f0203090d0803010519050a090903090f0b090906040207050604030e030a0b0109 80
    0xa5860710700740c0042001340d154241412800b0300c24036070707100107298100d032003a80b0100e19000c44030a039103603030a845443c4803049680300f0405c91042e4144000207460207a6840c0030140140050700c0b142c00e5071155400c000420701d101c40300348070a100d0601030700207559450240d1010315028160024880007200060080d0480040101b4020641c100500000035880b00a0042c40d540610701281c46202d00c07100e090070418a2200010099004800443d6000000d0010021181250a04230342c800792a0130382c685450f22103000002507040200d0450142d4020516002030280c2c0d40b05407803500484200003024043c04184c25501120302000501907410416442c0c80d05c80300d00c000c0d8903070080c80c1c0400550420000d02650301d06a031500c4078103040600071603c010142806e042962401e945480e111401a0020501076100d0000035000c18050b0816200b01c40082c0d4202014040a60b50b41e1825104003840d100c005030103110700c50115020411101c00382c1e0280c00544004600c50401e00e40c038071850540 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 877958947 1250 877957697 877957699
    0x221e06050d150c05040902040b030601260118061508060f0d0203120703110303010b130b041202150c071206050603010c020303010e15042c01021303060207080c0f07090605 75
    0x4010410020030b003000b40105078108140004144850910000c8036180125400401e28a0001c0350202e5212010400745110700000c0e0385005c0b5400b212020a6014440f281c903044547e0150001840316062520813246403420344040868013641e02c020b04121210f0840c4180000b96840050120b1842c040e42d40c210700070811202e40c626101282c0000703884030143e0b40d00d200c080f48001662403c141c0034100c600440541d601c203403a200d42c0e40307c46100c1c080d0311100b03140542c10036031540131424ac0000ba00f954155122a0700000d41d5425550030f21a41c0280268426900c070018018401104400c120410203001c40888926098103540b40260a590300a42624481e034144540545901d85c0041a64110344032050498100d803903a1100414129003800d5180d045424140c00810109142103490079610410945c03500320400c4040317032401c078041c00d2500740794111841810000b203003860700503200030f130300546a092070007101008040c5085594101c0328200c2d00050f0080284841c503200da0402004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 877960197 1250 877958947 877958959
    0x71a030a0b0a1505071406040528080a0e15031005042f0310030b07050423090610090906060c020316050d03050304051f05101a0405221e0605 62
    0xc209000351800d04480001d0303900300800450036800b0b001c60b00c061500599010820344070f0905050505907202c00000e08041060101200d8400790a240607443c09902034108bd09141000406203013100d07440f071403201c0b4680c41140c1064144440c030100c00214080c1030741003086075821340707040c0510058800710b603c10300030711100f080c142148180001041c0131003014440c42da650b984d82d00b5051031070000c00e504041c1034040c3d0b40040184075900032004105171041c11043c88001c035045016940f5015040d100e030b80d001050784021440ca800c041e9001d4140074043c0c01d0800f0b803d92104000c808649256000c60000780000204500703606091203e44003801c10031420043c1e260500c0d021500c9159104002803c0104c008000360078440c05000c45007045041d140c8103d40511881282e001401c4265100d08520054240000c0d9030008031406d180340381241820700e4241480e04041050b6140350780001c4500582100322107000c509580b02e541d411256281c0090210044040400100c41c2c0540202d4041e072 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 877961447 1250 877960197 877960199
    0x141c020708190305090a09020a030b15090a0311030127020a0b0307050313080c2a0301061406030c0f0c0318091909020f030d0504030b130201080f0702071a030a0b0a 72
    0xb84a442072500550181000ca607510074190224006d05602c1e13114031640340c03010071100340e4150305801400641c401100c0300c0b0341c1307925201c0900d5681e228902c80c0a600210b00e041c1080000c41200c05c60800312030050001420032841480003240e0452351146800035a480d6807081c04518044066001800201c0329640c110314001501401c18070010300901e0b0707403a517004803240401c50000102e9000c1000c040c01d55222061210501c0e4800105903400011064102d0003264a03050505c90f0030221120700e13410740b60409280c01030200e20742c0050700e1000d65220030006d076134200c28941c0041c02582201030045030b0b11000441e40000c0c07584101c41304c0380b01d040560103100c8081080c0703224040450b103842001400d03060910021329104000000b45401d07000d11001d0081e800c2d040006001181d01402c41032056940d40840070309140350b0380400a0200c1e01d4000426207080751403038025400305490046503462501d8030b607032104126000320b0791148150000100506040303c0e01a001d14a001603c0c04c001d1030f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 877962697 1250 877961447 877961473
    0xf09050705101838120c03130602031012080408010f0b0f01320c060c03041208041e06061701090c0b180603090d0807020f07050409141c020708 63
    0x295a041c419655220010510400441c0c44c40003000c0d80e07410016140d0b4129444840a06040c1d0000d1381c090404280d00c1000842c404081001c4a1141c042c005800310781c0c00265542e01c00a4001505950380405554804105440d41c0a0041c800a0255800c26100ca1426045034251800614402c0901c1e042103001c41d00c60702c9000c1000405042406e00c1c07005040c040d0000d20246c1401990454101402d29070101900c200c0f60042101004c050b0036105030360344207101c0c0a100c0c07106a90041104105401e4455624411000140c02c00d00c00c8800e10240005175450945c000b002080944a0701d82e036013400c00c10501d034268000d0310190414020701030740146032120f5800c0d5046200d0401e1341c54001494414081c0d0406807070360b10050042800703899040c04c407040d6075105400e8100380085885240440c1e03405000143d2600340092060080907058240380500000d012100f208681c190300012408420079020f00c030750b02a1b000341d528642c4a140805400030f1414480354044140d80e04626404404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 877963947 1250 877962697 877962737
    0x512070f060e030a1a01060215010b04061b050a05010507080f06010801052404030609291609030b090d0e0123220f1d0105030618010f0905070510 64
    0x840714541000c244038000e190100342040e5114400802c0701800c0301003517400402100b41541601d00c40e03400c0301c500010002c0c0b40741c410f0070f081c0500e40c05a030301484100a01441041c6044180c000c1c01007104d00380c0f803540c3e40c0034582418030508036401e075114003c10403081c0d404040c807a4060a81c5002c50b400e03080a400203003601c2d0060082902440c05180150f864900703080340e004c010400c40010943e2075070b0724103060300204801e04007241c224070801c031014200054041c2062409620281e83c4596848003c0c3c030103424081904800c0c01d00c07034100c0d40040031035080305420f44150362500282444400d04e640c01486000112061070501442241c1c140411354130a10000748019901641076990000d00c5800b000d080320040400b03080b0b010071801045550790b460809040f100e80c0e0030940c111141c10b524800d500300c400d000b9503800d68031010005800042c2030b0b00410340c84210100001c0d49062111030310003550483c5105031b0701680014400c0100d030400c81925840c469107031400340601d12050440d010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 877965197 1250 877963947 877963949
    0x12060e0a050907210c090209091303030b061c0e0f0a03080406090c1d07021b090712110c0c031b0d030210020301060915090f0501050a03020708030403090512070f 71
    0x25900d960360002100e010081000300068038490310b041651307007a00345146210710000c0004880101005100050000d00b078020790304c0e2104000c10740b002c1e55403a2140a80c13010784403201901096220458810703246c5810340100031000d0105659002c242c07000506005a4503200e110690702d501c010304182e20b01101280c10b4425540c945010062501d03141004000b610407800c0c0540020311410f00000d5030014011881c500d1000c1808095840d03441d131a040e40c881e42d0341041c031036101c00303680000c1000d403511268413035021107a41049184121056107102c200c0d1324500c84251040c00c0000c001002d20b04c01c201c25420320340c0850050006250142c11404c0130b4029000503070245103c411031200709402844100e400045405045440e5a50340b4401059000144140c50044200b001d1038010035104249507410344060f00400805a45800300441c0c29900442d440d004160b030074031041d030019913590021030046000b07036540c4100c141440c4c1006020001d90702c4034112903000e18010400324001c245440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 877966447 1250 877965197 877965211
    0x21e01051b0a0c080102090901090614210f0d030b0427020a0902070803010510082809170a1b210e03010e0a0c050307062007150f12060e 60
    0x5144184020303140032002e90008040f03400b84040414003003015800782410b4541203d001a0590703031000030304202d80040c045e800c00d81c0070f403e02641d8281401c911008070310205050a018000c60000c006003000c0e160f080201d140c0d0848261405416498000c0104402c81120100a1455414050412485d50340c1d01070302082c03008003988066580f02070348113005000001055580c4c1102c2e16140b09141d00902803540b08800e00c03c04c9206142c4600307080e9104441190015071445884403921082000c56100c0c8400d69480b40e501c040010ad100d0b00b44460760410b00c801c00e07110316410f20080c0052848001e013080c1107030030500c1c0c0d50200c0d0480015a111400240c010a62448512402c031030b20100030180036015802c01090410007100051a44d14443c000e140090249444a0415440c3c030030134410301c0c000601030007898018202d0b02c0d85503411030714513004842c1d80c0c0c1d541391122201186660020004129001d0440c50f80540068842080701d161110030040b0608004030400c80850242080c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 877967697 1250 877966447 877966477
    0x6090314010e0d0c06050f01030b06040b0a0f0605030a0c020610060305060112050c090108070509100e0d1a010807050604230d0503040b0a0e03070e0c030703110313021e0105 76
    0x18280c006080d030100030700e41c0d503080035140d0729010850003030200d24840a080352220f01d4034000a0f0442031001001e41a41d034001480581e54a8a100700009403d01100d034541c0450b2100c00042c0031201140c851000f4400ca03101c030764881c9801e01c082401c484150100d00b00707540004041084065800d1407080076a201801e0025250b110381004030f030034843c16210404d690340351106002c0c00107038850260040000c01d80c1c1d4241e181d61912400c036224060712207400d800c05110040044114060407000103804000f0f08180f507048030781c0d110320b80e4803400c0380004d1140c2c5e030321440144143c900c2440340002a00041c0d81940c901442c00750702c0c54111040b030310640b000c1a141c42002e000e541e60795059a03000741c1c001c003c8a48480c4c0350700704900e19030f00407101c0360085465007271564003e007000300d861005c442071000c440700070b50b440400c07000007984010449420980e4904d0b10604000495000c0c0d4028a4074940c48502c0d46118414084001d00100b600d07850542520070802184e03a00c0781c21201040840104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 877968947 1250 877967697 877967723
    0x1807050d03180f030b0703060302060301170c030d050a11030705060a0c0e030d11010b010912080708070f061b1805120304030530040b18010905031e1204060903 70
    0x84501c03403500345400250151444000070400803203039000f004e82c3e0103442414601d8903000001c0c0d0480d0303000d2000a400040500040094048002c0103c1d1244a45800d039000b460310f07200060300305003846890001086e4049030350840c09038007080039040002024019850b0003400e454883d80c400000b010300c0b40c501c4d140c032550146a441404c0528003418064100d60394030110040c0030380310182c6108444455803034001d61818035842440820100c9160b5503002c06540e08a031540f00c0203038031801c41611420002c00c0f4003000500041c83c1a2a0f185c018040014802e10b40d0b51003a04800807984024104170705501d50504c51140551038608031f0307c04075806060007444260306421130140364400b84c2140142500c405c0d42c05003c900f0300c2c4a26903002e441410b62013190381c4101c054002c9014540701000e0600c200f020241e10808c0740ea003010414100900407a5540d00000d00d03162040080380407503440c000b000046401c1c10850b03002c04003542c40295042508101d0001c02c03130911440080d1904540c400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 877970197 1250 877968947 877968953
    0x60b031f12060c030b090403170a0c1d0a0506041719030815030f030705060a060f03081608190f0e0901061416060c02071703030f0403050d11041d1807050d 68
    0x442a0305c0000042d00d000014030301400c1c064000484042c20321400c86014000548801c00ca1040c0c07005400c1546880d0060701d01922032154041e950048160800e103d1500400c891f580c0340c0151000f0641000c0c4546100c810302211420b0824000c0101091658000c1c1c0f040002e4014401c1071b40300035900210782c49500704100003842c0c84410700d0780c2051070100049403030611001203012407080f40c035a0014850a980c076052040c00300c02c6484064802c20050003107500c2500c80342c401100c0b6034040e42103181030088850b449190000c1d1243d4031004910155040f0b01010307080a0504054601254099031540c50200c0240000c8110407005441c0600000d1006805078106914058183c03c010b0802864184002c0651380e04010b0160791850452901144100c0c0300020450788100c280c00e110483c9611255021303070740780e001010050501c98981441980d80d00202000d00020b144d29000249804090b03d0443c2e070041000d40400036a441d810b42070084d0340d0740068544c081710740507102c0100541d2a42 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 877971447 1250 877970197 877970201
    0x4050117060f040f0b04060b03010f06120e011505032406040e16120b0a090809100507050a05010b120304081b0a09050c0310060516060b0307030501060b031f12060c03 73
    0x180c0c0440c0e20620b00144e44881c0142c95116002c20350f0141d40410500e03403503080e0124030f80002d20a5400c0038004200c2031244a00c28034100c0958880c000c5c002c00e4644c031031a0482e080d6554050407051a00c0410001c015501c0c0400c000101d2003043c034110680350380711110780d05900f0001000f03a400349441d101c84840ca04420007443d0408082c0f00807505010b0745482108000c030080003400e940d1109000c5c0800e000c0d4440d4460350864561010303505140000c0d0300c044c01600075190000405101c8240305001c0450710500c680507845100340c0000440d184c48604000c80c0d0120304d14200d030780754400e00c010700107407000040101040c00d0300d403983c1d8100300401001030396140d41c64100e0301e126410700e01444420401d08015500034400d403854175030480d8454004681602602008503404005240c590021a80b180d200410015010382520501174603034590798250b424030b50107540005000070412003001050010480203407a0001c0b0550325034601050030507071030081e03400035191694031064200c810b4065 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 877972697 1250 877971447 877971469
    0x2d020a02060a2102120108060c03040f151b12090b19061205060a050c12271204051503010602100203060f131a100f0c080c161a0405011706 61
    0x1500603a034400f42008060080e41105040d07220b030800020000c103501e00003082691041050001846c1141e882d42c50b80240842111000d0b0380d900c0454401c0e0718000c1150080036881000c00fa1110b1840c41255401026560001c1102004a06d4810360000040c001c5009940001c03011404c40a8004840f0350400201400c0c0e005040c002210700a039000c002c404505d1a11800c4040010091030341c59281c8108644102e450b955404e19003c800a611801030380284000c11100c81704660180407a181c0d0a45841465030410310301000200b004c00031031910041c4c041c0303030103000b246180c2554507000e00039540c2c45601d800303100350607000320000f425910f0306004e10301003420003000024101c0811211000800d07a400501c02500c0b03074006038010900b0b0150407240304812a903201c1c00c1c4000b1045048038609042d4070b0440d4865810030011440440410566044248e0562400340e5a442d140649650100040e40000c0303a400c14081007140782e810031503904501000901d140b41c1940d41a00040c030030700e40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 877973947 1250 877972697 877972727
    0x109140112270f1b050901092003130c0b0f1e0c150a150e010b0a021516080709050310021821010e150601030903110d2d020a02060a 58
    0x1903002c0c42c000d02c2180c100c40803c06004035055820f18012284510303106040740246034004144000410002150b0741c4003a802c4900d04a40000042c02c0c02040303c1c20381d1042c5c0c0e2030a0500103102d003410520007209502801041c1480b001403500882c1c0d10f040580d07004550801403189080662100740c1740174081100c10014100059a442c0002d0b0070345120714140646241066900c1e041d01c6407889030202c3c03821001da40115a007842241c1c684940c0d028594050901141140212009030302180810a82240a541d0550314908043c1c06821300502c008401440d4604002200b0030130006510041401c844c8080d1076100036070384444000a0904412400341d005030025000d104010003402403440207410451104020711100c80003034040ca642c3c1211800c0000032824060102e44550700940c04a89024441e05240410b201d40294650518003c21600c80c046409040e0824120140c0c600401d403051808903441800c000d00d0500950f1503161003c000d029001c002159035110740581c20028490340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 877975197 1250 877973947 877974011
    0x1803080a05030a0605061815040b0304080414011d090a23220209010915080d050a0801240804110406030c0305010e0606062b0c020303060109140112 65
    0x5400c0c40e00400c40e600c1212592280c6190290200e21407900000321001c040c51405001d82c8107100313604001c1500b1903c0860031066104000c0084c41c1c0c0b401c0fa020358170440c054240203494900d040000415011a0483e0340d04000b0000c003580c100e10110003206240c40025150300c0403ea450001075001800354010f220500810088000e40b1500099200ca204010303048443c00548090202c01441d070b1002c90000b548014900e006200001c02980100d0041036648003280d00f16a841400340d040458090034000014000540620055041004640180342100c548611361412200466441c1c00030a0400304200414000c00c0038041c041c50503142d4000001e00404c800e0303980b4600600e01e10a144011601c0e0f50801c0c41100b07410030f0106e03400b07202c1c140290401e45004c00040d4150000b44510303180d400c0204488456001c40580e620540c0c4860140d03400642d9031b420613200245c09102994000d030b1641700b00008402540e41c0c041d41c10302c4019488407011030801141030410303080c080742200e507140080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 877976447 1250 877975197 877975207
    0x312050913240806100f061407060f02070b0a111303020f04060f081e0106050d03180b0735090409020a03050d2003030903040e0a0213080d030c081006180308 69
    0x80020030f900e402081c3c040858020b5030342c6d580407250420b10910038400172900034503442c04524064001024018858080050b240d4103030703502c1c00c0490300140c85c156032030707805d040412a242c80d60740305402d01ca00071010003a00b8140b000d8284a6084c0003800300900030240600c1521840e20740c1d41144001e0085012541031968950f520350380d0380c8181c03200d40022800300c0c1d1800c0030610818891101640c0e006050b50301800801c1d281904c49407c0322800803400144c0310b1001030f00c0003000d005880c0080c850148222500340898160094103012224002e203080600862014003010400316040040309076000701d881d030001c0c0006a0310b4401c03988050030502170b4125003800c25601a10140c54054030941030040304580306200b0ba500d0001700c841e00c055610810082c403032402e0400e4402c0d030141d0032510161410ba0b18070075120700c070072003940301c402c15901c01d82411034955014042c3d004220443d00d0b001704145490048910004030511901d0180040014082c0070034861a00b0480070f50f42103110300742e4030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 877977697 1250 877976447 877976459
    0x6090612090d020d0c0210050a12050a02070201090504050f19020f121e070507150b030d0215011406041202030c120c090f190c1116031205091324 64
    0x782c50182ca800c0018022003aa51076040d00401401d0103003500601102c4451108060aa41d0361740000c0c04902400602e200310050a2103601849100341441d060150f01c0d42804c2c40003500e122550703040386100e581003004129680c000b480b80c0c15401189034160f400c0b801c81e034082c403074024404c075418840c10f1940000c0f040111078048081501400d00d5202c4011038800c040e2100c1d100c3c100c140d0f05600051010803000000c114413014130032650440c0c80001881c2203010740080d103892001804400076810455400c40346040c441c1d0024010311003460004940407080300003c0503481030f0302480c010943c10f6400c08041d51410004101d8488000c1d04680c191101400810b9980d000d03104e1391482500002c0015201d104031450341e034052600100b481c01941c171586203d00c0074210250003001000759456800c200701e40c0410815000181080c41000700c0da06508012814800501c42d8030240041000410416210b0b5417002c04c600260010016080c41c0398541001e58440c001103504a0071202c0e0404208 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 877978947 1250 877977697 877977703
    0x3090b0a1d0907020604060515040c0e0109080705010c02040911040903050304060621060c11160305071e0b0d0f060e0a0f0e0d0e0a03150e0d0e030703020609061209 72
    0x20965424400c1e018614001042100d02e560403a01e00f0010f8008074003190025015411903504642c1101621001241c00c50208040f10803120540700080c44c02c982540d100d503013046000c0040c160703c038052705132142403200181c84ca01e41d44000900640e5256400760038400c6c0380d41100195140200103002480181c14028515002030710103980861034140e0000d1b02d141080d442140300d041c40100204071703040c251150802400c03046a07c009211108031407981d4941c0c140324601c188a800c015030126036040d420321131320f014103640200c4504034400009901000d5801882022148448003840d0381d0081000c0d00d03005801400d908001c440d08001000c104031248a000c1482103000d94401c008140886d82c108084d2160800c49401c1c0340c0000a85203c1d9502c14494606140c001902d00a41c1c80e94982d514003151a02800f00491540d490b450307550051000c0c8201501e1200074502000141c0d01c850000340ca6404a00c0020f2040d280017074440c1c0341c4c2d1141003d40d51300021080007884949030003084180c1b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 877980197 1250 877978947 877978967
    0x1050906100c060c080415051e0a0e010603080c150c0712050f0c0c090901050f162f0d080c031501090513090302010605120601030b0402030109080c0a05100c0206070c03090b0a 77
    0x340007014080e1045100d501f905c5030900c81d001c1c26130310104290000004003003c0e100581f800d10a00c0d21141b805040410074022140158410304101e59100085100340b800d024030789020080a031064824440409548025141d06681001100881014034803003a0b529200e104038103040100042003c951000000c240c4c401402001e80e5500810794840681d01d00f220310845000002c0c900c0500410743c250018642c01c2103a030200e040c0b52001c1074241008015108001100c0c02001d42901801148800240b007200000384403800c01c3c50050420300c080082c0742c08000e003408240c25509007000c180b030b0b20411054000b808013400012300d01e1059000f41014014050701907000d5030a0807000600707401d0110340300b0303032068052001e00000c1e403e540d10003940740005030090384e25640310618100407400280041c0301101c000c0340106154003040c6416820b211034442075201e4149042d5880440903000302e41f150307120485203081d070182c2e55146002e0f01c0308006070300303e20000702010550158950300505444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 877981447 1250 877980197 877980203
    0x103050303090105160807030908160b0415020a3e030703200a0213020f03130c0b070f03030c1707020d020106080c03030f1b060a0504110901050906100c060c0804 71
    0x840551717210418103d00b10300b2054080c0014038a4400a0400d6211394050103599210340c2c2d140f1f1030304100c5201048180d01b2582c050358041c0d042e000f4401003040580800c406560210000d5040c50700c0f10401400b050325199200d00c8006060346403001d80258103454110820200083c0306810420b660100d941f900039401c00c80210b03002c0500150241da503a08186600d10700c00000300048013150303091107141600201c2154125409000f01d414062504003d144260072500504405002904118803810682d91001101d103200704000008111800c1c42080016003504020502d19080f010403200b1007014610b0010702e04195082c050340e194042003a0802000b158000d02140e80c580d05010b0b240c001884456506601c20402070020070407443c060000b00c000c8181c2c2c9260142d450300640e0a080042342c540e041195610200300c20003c03c0740400c220610150b83c0d03440c0c290b0414010400044000d00f01c148200600c03401c05604a102d48422245545d101d103050004c03507012034021b002a041680c0403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 877982697 1250 877981447 877981451
    0x50a060f1b030509060118021216020d05120c09011e0917070b0a0e061b0106061b170d0209060d0603020a1d070c17070f15021c05061801030503030901 66
    0x8481c0d240e100e405000d01404851000d0021030346803410441c0c019204c00b5080742c10907000d00c40754204e25400d1320b88910410180038800c0b1151010040203007064443c000354010700c442032040320400d24131914410f41c0031070000c145039907452042d80142e0707581d42d4200320a06807441004c51006459448202c1408980c1103510441040c41014290b03a00d4000324002ca90350041c080c000303403054034855494030b0000719001d4030592620311444e100d091410b10b61001d1030516910381400f0420194002c0340c0c3c030860b0100300041c464505182d0348099000c540341c503039142c40200203c0e0703c2000c41915412940e07440c4005048560340c5074220207500150017188000c0c0d2203200c1302c0100060907100e074640c030100241c2644a00e45555604071003034407040c18a01096901031840c800c292003441c100f100810701107010310404401c10300d0b10b281c14078140d50072030161b200d900e0040c040031000c50f048602c40c00d400c1c40c81480c041040da8442000c640310038036180210800541d40c500010910002100540c06001c0c50402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 877983947 1250 877982697 877982741
    0xd0902040b030706051909030b0405011e0207110d1e1a01060e0d120e0d21020d0203070809040e1e0613021807090e070905010306080a080301050d050a060f 68
    0x30562180602c1c86180b02052041100c220304800070850550386c08810300f004100641c50391602000300c901140c0031145c5a64880f84140310010816400c50150341c480c2040d8070b400560b54400b03010707003441c00f0b656000d00240f503104002c1160540c01403188124940d0b20701f149100301e090001200340c070502d0345104000700500204000d4820a044c3c0e103101c0c4060314001d991007041d500c1c541580d071440309100c204611000c0618803580c4849441054034040c480280c60810b10145803895032998129220030b41d40b0078500f8112440d000b1065030b4040e03812500c00703510340d1300030004180a840c0e4080d55420500890041c1c6001e01ca034180c401c1a22504c410403142c05a4a04015280d04044042c0c042d60101d500c02c009454445890602c0368004c50a01d000360203283e07600103604800780d00740c5080000c900200f509000b01d5a043c8503400003081c60380002c040781e0100c1c0e1504d840d10302c018000c0714000d00c00c02550300c0500c0300401a03020281e41c8400200003120f40e02c072014000f000c00e04000e008182c0030001d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 877985197 1250 877983947 877983949
    0x1204031403040e01031e050d11160303020d121104060203040f0614040e0c1603020c030c0d0b060d080c1902090a0902031b04060e01031a070216030f020a08030d0902040b 74
    0x20658040e01c800c0240700e00031341d00355120101d8065100e8000255401c107407460500180041c440071405117800d0300c8481c2900c04040006040003100366490125515041080002c2640010010b91944e09400d000080007000c0070300740050080b9841d04036030281c00013400200c0a50000043c021158019001c5071201d0302d400089412038145c921f5003180c0c00040c40305119002c910070699401107090142d45260032040181c20940c107014030002e0300503030018041035400d400d0900c0b104c00310150880f420b149958007666074101c0304002500c1c850154908501c82e2080003034040803903210203880c1c0d00f291000104202074280448440e88120b01500c0a0340104080c1d26150040c600f00302d40c010302401e00d591102c680e10811041e4100d6003039015464160010b603070700101c007069010714000c18007042c1c151480844483c022501520000455005910500942400300c200d102a01e5110100c03041c4040d6500010300445c000b90040015400000f50748e85c0c41201e01d901608542d4401c3d2810b103d6400228 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 877986447 1250 877985197 877985203
    0x61e090b030601030c03060b0d02090406060f15050d2c010e1002090108150103060b040b0d050c0310030b09031b010902011d01090b0c01151e0e04032f12040314 70
    0x2c48005d100176034480050002407000c0d0007400d500b03000681819080402c1e41c00140b210304082c0c8040d61074554880e0180400d1103041c0601000e440702c0449da07600303e42e900714003c01c988545524804100d54840c410140c000c80003004c444d04401d880800300c0456880c9060074000c0070100321020700e510400c499002888100e000b0b80c0e211400503112061166914016074800c644400030090401d60758110101e01446100c0c0a0005080d00d0a80c054481e035103da83e40040307440c064042000c1440c203200304003c620059020000b5264042c0414017036072074090806145000b0b0017a80c009160020189a401c03110561140e10700c54001d0761809001458400c01c141d42044100c507a500060b00d41c00305118408641e130003001c001c0020381c0000740320b03030704418041d140c1c08094116101644103d002c01c000d000c40c0da00040080c0c8001166076440b402e003542c0140c000141d102c40b02100060001460f81c03141030f04802c80c04d031024642e00b03071000b881402e503a5103072075170290000b00c9001405107844017101d1800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 877987697 1250 877986447 877986449
    0x20d08061005090a1502030c19050303161e0c020102151b180301111e0a050a0c0204090c180c050c0c190803040609090f0c170604061e090b030601 64
    0x1d842411000100503044400c0da220003285074110000c10000107410309070501d40680d810340c56025640780c00e41c48004a08202039140024101058080b06401090f008000c8031342000b01c0401c84c92042c0e6000f84145c400c6100600142103949115400d103035056001b070500350015100741e0070768400c01c48040302d400d00114161100158520100581061103034068014111910713030956990010890200003420f46503000c50711701c0950404164920707040d24480343c1043c0c0c0d03507600d00f801d030030a145840010043d00828002c0da0030410046081c10654440340d2104100343e401030719000c451612444007404c5921b4032002140030501d4400e020b141e0522071015030b0140b11650014000419034201080070218100c048000000c2524000064040003080104000c0c4030540740d5006051415003248219007035404010b00d01410001511191648081080108a41c01c01d82e2a05511110003103002040c56800010f00c061103600300f540d101282c1d04280c4111454400c051000d0510a4103050b1a035100f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 877988947 1250 877987697 877987699
    0x20d06061b0c03030e0316230303040308031f080604061e06140d24050619030809040f021303080705240c031510050909010906060c080d0608010e0d020d0806 69
    0xb682800003e21900182c0700200c802000c403001c140085465980c0c0d00c2ea00e0b40080241600c403007a40130044205500c11452103811809103042515685031b0031014800180800320300400030801194400803100ca101c060010401141d40e54a003902c0c2c10401130140034012002000140f4021048240c103015910586a0340322055200220100a000408013095000c403800c82140506405014840602c423504400000012a482c24120b0501005540d0440000f01c1c4900202c0d0500108200e00215650b0f41400d54000451001c600070120081c043e094820140e030140c00000002d101049000c2c0c240f9501031010340d001044a980046ca60070910003600421721a800005001c10074000003865002940480803c080c1d114140041d40d603380700048500801c0300412400198100f080322a40584aa41e404100e1181000740280045840110040001000040e100a0300c09542c001400030700d51500280001810003030010740b28040741e446000144a6144440040c602c5141c8443c02104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 877990197 1250 877988947 877988963
    0x50a06051507030309020609030f1c0c11100903240f0506030d1101150e091015150509030a060e1207150e010e0f01020316020f0c010305060d06020d06061b 68
    0x5980c3ea094000e402d1501007a41d01010500600f003080d1402c2c80380701000300c48600a00ba03107076887c01143c022403400c0d0f4034030400c0102810300e107030018010110000d5039a41c1283d450454050495007110442d040380c0004004c41c0680d200c11034030307000c481e08621a404042000b4001c1e03000b0a607400b01251400c480c407a61540c40814050b80050098010340303040624000082a510111480034251081d181c0c0444425070400d000c00240344000c1c0701003060764608050a1000c111821f10940403d8190300500301c0b0104845c941e0440f050154040300d05054002c1c00b501d0405002d418000001c0c50520031001050003026400c090031100d6200300c444003030380401c00c0c0181e03003140821100200220b40040d01d40d9076951209142d20320381001450300070040500051303a80d2070b12800240880c4440540941990f00c442d0407a112107401103070f421404502881c1c0018140c1d158000585040341c2110007901d00e9100140c219400c0351660454005d4802a8603102844040d1500c285c001c00940540504100c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 877991447 1250 877990197 877990207
    0xa11100e01060f1d010306110f0c100c0512400c0b07170f250c061701090203040305090d08040806010b120406050a0209030102131406070803041103120a03050a060515 73
    0xb1f2016030001040f404040a8141806040c4808a1199106041c00d001c5079000864107110540700d03001d080f41e0000507150140c1055500e010b101c1d034007100035006010116060b11060314640d19260605046801c140b00b031030f0b0308005013800f03040d24a0080800e035140703086a0301c045521000e078400c803003900d0b910000d001c4010003a419103c22a0b0070101211a00310410003d00c101ca5403110313000602d0340040000312202500e1403400e80d000e1415644a401845100e03032201c0c20140f05d409400781120b0349801d0150340c907940c9140880381c62084c0358006901c9044c4020301824010701d0307006841038a500904039100d6903229148c00c541c502806000b11381c000781e92400280014215080242c10890a0780090304000d20800003901366004400c1103024080b03940000c001159002448a401e10800d9554501d00202901c405040d840010009407200710421645511507d0801c40e440b0003003954640191a4801104020050002500d0301142030741400008035441c82c0070207041130072200d0203440910b41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 877992697 1250 877991447 877991453
    0x801150c1e0302011a151206030c03010c0f090603050f071b060513150606200c090705040806100510030f0906060305010507020f0c060a11100e01060f1d0103 69
    0x500e4000c6011190307810700c1d1800814007841001c0c1941c44501c25000895100da02c0b044c0c1680b420314003030703106101c0d0080e51400c03090700b039076034007281c2c0c80c001c205200d200303190b84060100745000050000c031a05580382c400680740c016030225042e01d26030650b076a4a921641c1d5202c00f2400d40e034080c0c030004803100603407003c00d8481e401004407015400d201d50b40d249900e0007540320300f002c46008595440d1401129040030040003026141404e03c40c001082c10842c07941412030081142c1e0540000c10100200301d04000c054480070041042e1041005003450030f90310780030b00300a0071600580308583c003a2160304082103c469010701002c041e100302070910780c0e03801c2c0081c00443c090400c419009005503521045000401d00710702520020b1400780c00082a14280640c0003460042c0c071400020441e001440f007a621740e80c83c0341c100d81c20001c01d480c11101c0503541031714850400d0022103407002c8091034019840100381c9d06404c18811030f2281c034200313002e25959094801420000c90946010908003034014000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 877993947 1250 877992697 877992707
    0x6010f0e070525150507080702070b0c03091203040819060501080c090601030c090e0a02090a05090106081f05030607020a121107090e0a050a0807120507120e031f09020a06080115 78
    0x1c85000d520844640b2141c0d0b500d0204031170007900c8020025541c8001c00c0665901008001c0c024203154010344e290213206021207880b4000d510b040c1c2e100e841105140c0c00f032100300300184e901038071000040d14001c156547e9041c43e2034400c20001ca800905280001607000d1000c12140d030584000f40414000b566020011001086949042c03003c0c80600c100100390740c0292100d807072160891050043e5210007020400c00d44d034009038091407040d41803d0061112070381c048505600402001e44048681844d659507001407000c6400c495014400c0508103c8190340c00a01b50404a0013405004000480c07600211142c040425080450f030784200300c04c1020078007981c81543e240d81d00780c09035845c018081d9521070800426a109550030305000c00c0030020b0045c0150210307020700c20b40c100145000242e680e650400d510748400182404512030f1416082d440910004e0001d1503002404e082c0140004c03030b65401458406001d0380666401d130310100f9203900070f6118605942c0d05020070fa03c042c0c482901114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 877995197 1250 877993947 877994017
    0xa1e020a02040509250e0f010b070f0305070807081e0405010e0603061c15050601180308071502031006030e0f0312090a0c060e040f060501270806010f0e0705 69
    0x154801d50b117502051201072420f0b00c000c9510701030342c016541d02e0311301c5075101c2c804043c2000c1400042c3d039004002070240001150203041d4088541036110002c0d040656050044080290100300c0024234a010800c0c5100200b040c1041c3d42075000c003d0240e0400f55000d4007941c0071303443c00b090043d0300200040c5440400741d503201c00000e1038500f5440103e4030100c105080c00b803080390306504040400b102040540505a848402031030082010080c22060320b68000c00340c800508088400203640c1c00340f08843e414094860040d1209640d02c1c00d04091a070034030031080c85a000040d00e481c04078201400d0100d9141e0a0805020055080c24074000e4030030452140640300c1c90f05803103a0041000003034200c104000c024a02500c80250080040040c0300a880d01b400d0b004503001d14000081c042680c02168441149400c08041004108158046240c1c3e034400d400007a0917202c1d000000905071a400300d20340c1510460510116542c07200a07041d1001c0c080c01c0030080304ca4803800741c40c1e0041e50412050072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 877996447 1250 877995197 877995211
    0x610091527020c100522021008190e100605030303040c1502030c010f0504020909061e13020d0c0504180b010603020706090204090605010e060d03080a02030a0e0706050a1e020a020405 80
    0x10701c2c3c0940140501d11305002c1079014a00d8503120820000100c0b160000c01d01c1c01c8000c181c044510500c00d6001945d800817000e021300c10302c980d030004509400c1100010418600309045d04201e003000c10403507555585081000b8441940c24040d000c1224240481a20b0250f41d000e1401c003400c3e030810700780d80c084480c41401d00046110902c41c1000004003401400c820b255548000249810140140507800600400c000c007a50b01000c01d100c80000e10903502c416607001501e007120035889100b0552001c900b0140301030b41c0219401b46d00b0040c045002588800c5420481d030403ca1141d07090441e0051001d0080040c0008400600410a00307000b41c0040c91450303c604000030b0345003216070001d001c8500242c0b0503a0081c1d640c2c8018820701d80c1058482d60401e604680200920b48076070780c02408440010100a4800e40120128541c0e28083d006110298800f50640740b900d5201c0a00910030b800c14160715001500d209198884081c640c0c04546180849602500c26a800e640a000c090500076240c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 877997697 1250 877996447 877996451
    0x120f2a090109050406050c09010203090d020f1215100b160302030906160b0105150412110303040308130609060c030c1406090705120d080115110610091527 68
    0xa02129565401064040e1441e0140018a4100344c204203080b940c001302408400c0800f04810507650381c002040d10500441101d845070400001d102142d03402c4103500032079400c40703500c5000084040000c00d5102c00000c0c901c04000303160b6500e0819507404640d5101e075180e0b2000802000003030344603400d541c0d080b160080c011689040014004124240d000084101c15000b1007041c5808110300c840c03c4500600c0c1c111b4218141040c03103900c4034a281310b503100f405003242094201008029071140c081c40308140c001d0a03a0b494983c1e0341000e500f540c0c890300340b80c0038001240e1000f041c6580599400d50946003113070f640c003030301c44c0d602d81d03058500240245041c0c0307851800f8074800084400070400d03140300d03608000107010342034904000e1040e900c900031800802500700d440004038a6620170030090448650241440003a03019000a441c40900411821410b01500c01004140743c01c034544d41048032120f04080101d4002151a290240c178140918044901406041c400c01214a001250a038441202c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 877998947 1250 877997697 877997773
    0x615060509090a14010605041d070e040207050708010c02030309060c04030c030b130c060e18040b04030e0112020301120308092109040e010e100605030307050606010c08160c05120f 79
    0x213081080c5209038040d1001950000d003e2141c1c0e010301c410121074030004100c40c0c1c1030b41000d440c0540403035015000c060040c0c1c0e0226001d420310100304074080c01005220000c200b00d81800d0320007501d03544110780ac03501130b100f40c0b0301003001c0042c0d200c112070480341c1200e4031200301800c44d80c1d4206400702c054494000907440d440458041041070b06210020061034640c15844460750090004000c04030749504880030110080001003a6001e1b82c0f02da0150b41460905c00e03628a02c0c005030b4170904440c541e022020b20200012072202500501c4490780d070b00a0300c88510070358030004440da030b50b035800300c030003202c4081d6610b80d40c0527024080161400c1c1c140240049032285107001220b003100c1071155035104071751100400c4801829a0b02c01e00d0060305080c0d0182d454542c0783d88030307165a6000038100320304020503608441c4c24880000d0036502107040c11a111b007003c80c040e0401c1d80d4003034950b00074a441001740c1c074901a02c040002840c040d4022601c8040c208044400c80c0750901120706000010569408c168 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 878000197 1250 877998947 877998971
    0xa0e1905031234110d021f020423040b0f0f0906060f0c1b030a0b010b1303020d030804050d0206100501051606060e010305010b19090e1f090615060509090a 68
    0x602403d507910030500404560050500030004a20f07081d032003200750020b100b10a011580400c00058010304074000111200f000140c610003885903070701005901e1446082c056410204043d4903603140c81c00c03101031240040e18400c2002c040d12110806600c115030b1040ca0286080c402c400661005009201500f44074001603003000c0b0354024001942c0c40e401848442e03000010300144140900703002d0300188031180041d80c46c8446220107028000c400c5d0000f150240e0103462806001001c0d55015240d0032a4000600d4060203e400540f0200c0780f5001c0e034a81b061040d480000c1040c4034007805800c10800501c0c01c0d00640d0303290b2080c0e2062103030303040c40501c00020900d81d01918008104003420340b169585107007016408c50f903085801c14812100007200f04060b00c1c2d18620342c03040d607191040004201144601e04c0d4a13051450b40201c0c5840c070400f04009103969583d01c9071451b1400780505014404c2c041ca0050707400603840c013400c401b040c4117012640c140e003002c05590b540a4000b810009041c04112 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 878001447 1250 878000197 878000251
    0x40b061c141906080304120b150a090504021c02240708160308010603020f0909091009030305061206060a1a1204050304032003100f060e0a0e19050312 66
    0x36000000107040060907200c180b024410900100b2541c0080d40c00c0500b081d210560300702c00701c54041e009910281c00700d184c01e2100c03220111524001440040300329590304980010b06005c45050f0305c500240440311201d585c2c001c41050b0364540c0107240e852280b40e074540c5000d40046c076500d10742201c1070601a400001d6440001840c2c407880c90100c1c003c907414240ba004040800581004c410103005001030f04039401240140d070a1030004480761031042ea12015054940b400c00301d104501a82001d00d50028140c16920180c02000151080080b29402c0c03002250382e403805580c01504802c91580400840c25040400350114240d14a41c5207000ca55508200c02c44009482c2903a0030740001078100200700c244840c102200100c030301d004110a01c030200282d01d60402d01c100320042ca4940c4100461040b050388041c0203030005421900050030116030300c2005041c1c140c0200900e21600e5403104c29481920a00020720b07034840e004629001030051910499007020784030000d1242c42c510240402c400391 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 878002697 1250 878001447 878001451
    0x90a02090a09020d05091f0b010507120806010216060801120c03020907210e0d21020d06090c05030f040807060b0d060203190605240d021b0c040b061c14 67
    0x400544c56940035124001207800281c0000c01e10384c4a4a8409005c21002d10b024006440040000500f4120280183c480b40700780303040100b00c1800603200001c0300d60090703d8103015203000e074201d8040031521300e540da0303068160740a41c0c1c020801d2140100035190451401c0c103c210b201d074411140e21542da03404152402410340e0b403000481c03000c400d4000c141270301c00300e0718100c00d003100e409101e8243c1b644141915140d40c18501001c10020320030004c6401c0700c42803a80700880703181301c04540c1c0d84400c4411000901482c0640080f1500300a20f62000500c20810b483c01002d0b000c01d202403607242c4d0f955941c20303036000420071100e4603183d414090a5070f9030300040580c1c0030700580700980d47c0e203886ca00300b5803100c05654500d054103140c0307101400b854450102c04c5916a40e00d84d104411400c504401820728050740c0c041c40b20060000a21166164501001501221390360302126072492103e0108807d031003165134401d40180303007402806022110500200031165038100c00194050b04041b910400d1441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 878003947 1250 878002697 878002709
    0x31812030c0a0605070e060409180803010909030e060c0c060d0608100609051312030b0310051807080606010c111c030e0f0d051005040528170315090a02090a 69
    0x45000b51000f404500d0155552040d950300e00071001c8440840014a24080c07801940002661803190f840040314106048540680007191240c59603910700640016004040c82240040c101d00d04d0050383d401d258058031030400c5a000944903500f00c82c000e01c1880d40250b8403100b0516200c1600092100c41401940100244003102144003030a01c0e00d4801500c5002d0405004102030f00c0420000c6443d500038030381e40100f586000f0414800000c0003c0c61301802540c422542c0f40703003505000d8640304080b0001101e0042c10709503903200d07540308009510340004a13a041d001c40d0030703201c0c10400a044ca01c0d104010101c010440b0001c104460324400d0740560390041240400c4501c03010241918000f080d800c0300f20f000300d03585020500b0740e6951584404414072071000440c0c4860104003004030078481581401864041d440280101555408149084100644402c030510000f09500b1030b9040442c0c2c400c0c8550340f0000d140168010a03c59000401810f5507a8560300b880b903014507a45110059004200c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 878005197 1250 878003947 878003953
    0x9010204140d0309180906020f1801110a020f120115060e0307030320070302090708040b1321090512070e0f1905090c06030c1218031812030c 62
    0x10404000c0e010006140e81442c1c4a0303003803801c5040000c2d5101d1041c0b0706981690305011000441420303000f01402890340028070b902c0c000700d10000f0450f40540980310240f184a8088e20b081302c0500191000e0320030503e2458181c00c800452005400d20100000140c940a0959004802409000c0d42103038603a92a000502c0b0302e000c020410980c1c40f6200f409510002c5010b068454a141c1d006400f08402c0c1e000340c10500c814920583c54001e060010100854025000c0c100503d8030460091640d2001c60701121b07400b0195012070344007010a500d106400d903105c040b041e900034ae120b8072443c0140c410b40d8111b08104552002203840c3e01e41300f80c042e42c2d010b40c10000340703003860600f040c3d80c003200d00017070030441d81d80f00f610308008100d0105142081d07444a050000240740e201d018001781800b00303d205954003c00b00005000940320b101d0000c01c241e481d03804840342113880c1c4a20b006007000c2901700d4203140758030038802481d00d490909030b6080b11030790082901c481c0484240449080d500145003032600c3e50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 878006447 1250 878005197 878005199
    0x7053307031a09011503091b0e01030c0b0a0804060f1d1e06220309080a0308090d0e0303030c0a1803140d050703170402010e09010e06010e0628051209010204 69
    0x15801401c1102c00c00c0212000c040075030600303201410308803c0400c081d04040d00e0740681d1040c41101042d8100f1a0300b8500071220840e2194581100c00100b0711045a00421803200050105c0010007581c0e650f041036503034591241c680e40c070741358007a00342400d2106005a6034000454407400c0c00703910800c030f1031024002e88120200303039070722140480d10012a02620b40111040011100f0a5003045200d156210007001040d01141022198000c0d0b80c0c0103152184110748001c82070503081414548a092848100c9407180310b00942103501440446500780c1592007030010410b0110543d018143c0c43c845481d140414040c91400c039803c182041e4000c1c4c80048c505000790400250034810b07000241e00e40d003441854620030307a500510501c0d45442a10040c1c00c00c10100301160712402800c400020b0091178580c8a503110707e4050076045065990383e0214004080342051130500f082501c060701203181d181e00103050880507054151751060740403001c02c1010000414070742200d4180720b0140c4c0e840000140c542d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 878007697 1250 878006447 878006471
    0x1603022e11100209030604030503130b25170606030c1e071101110c01081504050406060f050f0a121e0305070501150e0a0b0103020412260705330703 65
    0x800c0705090b94030140100b065400545002800030f80059162400356070300d9039201c0e61044108014107000b04100214020f022a040342c0e0380301c841041c0009250701c803009003160700c259152500d00000d00f00e03582c00b10300004c8040c6022409140d0020704d012000d8a443c0c0c61101d120080d05120780300d030150100c04904074041c00071a001c00c1881d10300a00b4003180031003407955804d680e81001e600031410885542d0001d40c40c0c0000721030740615044050420301145c01c192400d40040c0907180107004411003484c01c00246880c01c40c0e40303040c2004014160b001c149003006040400a0074414081c0d52080720b401c207880d0020820140303917600038000e5941c60f4941895207801400e48080101070f800c0c3c5042508180301c00071035010b20760b411907401074000a441c8000c10042e000ba02aa5001d580d20800c1c40c0018800d0000e203200d542540c00d5000080c42d42c0cbc48040304094080e00130600050310b01d5110f807002d04040d42e0b903429118200307181c850506144a04200e0514100002100e1a10000e61a11501a12 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 878008947 1250 878007697 878007703
    0x1d07200a0312050f0903070b0606070209012909010522030b01030308090d020109020f0609040e1f0b0a150f030906050115030c2d0c0b0906090607021603022e11 70
    0x305080f01c3c03984c19a03040c4100d91039524021804042c003080c0c1c0034004a1a0f955514040314445039000d05003501c3c2c2d40e507070100e41400074a0324140c61025521010f0220910002030110703801e0180507158241005a1741401825040e10b103010407032407003001e400100200350001240341c000c40c481d1303450220f0351601401039800c01034108040703829a07061007400700041c0e46a14071410f03040c070107076170040e100c0c2107410005014245419a1418038000c1c1c805a03080711824104820080d560300b4400e101d50b4280720240305039140350384900c841d441c0150301c46410480c840c2209d03121000b411301e00401e012032107403129000c458083e8801c16150f00c2d00c1c2d000040854150091120804050a04124903486d050324010900310380d8400c0c0000d0703650703008007030002c50052011980700c54002d000030b441454400c5020b5035441c0140ca0202c1507104c1c4000140f0841e1000a100c00c8400250301d80c11191072456003032000d21800842021841040030700c48001d402c4841c8203400c41000c13181d071892400340078505802c1c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 878010197 1250 878008947 878008951
    0x21100e0c0310050c09040b0f0a0305100c0e090f041a0705090913030903120516052b02030a0e0a051201050a0f0b06040b09060705251d07200a031205 65
    0x2440700c0c02c04082168904c40b40082d50b00c455820b44000c10800b4000d00016407480c0c500c14080e9100c0407259001c010320000107107038004652440c0b002c10031403050a01c20390745450764552055204001030002240301800720281500281b103010300f4035042400100c0004801800c89018000071004280b02c41c07180740c030042c1c858002c00760b4007005600070a40e0b1001400768205000c0500160300d0060480d05492044040741e0008040380402001285940340c03036a222498024081010106008402c0041d4049020024051801d800441c5801c55171a010f0356040c03102c3c0c0c0100d901041000380001d05844a00341c0b4040e1300e80d1800009410710b00200388808507030420704211403040c42d00400c0840c0e030b220042110103a842410600c6d403600585800101386100356140180140200540080c0b070034813294183c1e6480001c2140d0030b81450304d07144a81500c1e80c0b0704910014403198040400c2c0701c1170140307009030075004105500c4481780170094015460307d60303240c60480018000980341050030f201449502e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 878011447 1250 878010197 878010223
    0xa0222091a0f070e060703110c040204230603010b1804060e041a15010e04150915140324060f100f1409090105011d0a0e06190521100e0c03 61
    0x14014903284c3d0208200f030040d0340008051006070700300e03600340d09000c00802d405c500c00104103540c0d9588612401c104a2200c0b4880380d0103110181c40c0c00660718202042d64107a0b0307008104207040841600e0300c0c441030030b20301d00f5071070304250340d07074000702c2d031900400e00d450300c11801003010070341c880c500c00200e000300000207006451041c01c0201d0002d07640e07440781c000c8840410841d4041424008404401c008200a600c00200c06103440034010b54840d9082c5103c04031480665841d0140c2c10076404d15440d18120030350450710901100c5451110030404071695082040901003004110704400030450407030101c0c41d0304000c1400d494081c80340c107500203040046180341510250925821101103100c0c004103016845c18046920240c8091190b01c003c008c04000c00101000c03040c607640d4910650b1802c0644215010b5184c145003017405805040c0f603801215000b40803202080140d03080300304010300b681d18100c0c40c0e0084c1d1140d10b0f0300c4086400703240c03074180259000e4025900144201450076440130120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 878012697 1250 878011447 878011457
    0x15090a0f1a120a081605160306140717010b03041a0c040906050a15080c130b030703110705120309010e0a11120d0e0112020702030613060b030a0222091a0f07 69
    0x60000150068103032a058040c00300c1d14517403c007142c03415605001d0500010001010140c20000030b104043e08400890880f6144406071912000400c9400d01700d1282c050720800c000314010000324450700d000b144d010340590158800140e4000d204081114291411080d015001c038080c0b00d0300d00b4910445000708421100c8a805a150102d8140c1780320496862100340881100040c0503070003580120b807028105003101061203902d0364580b03207158200b5264400000c2c54010070480c0f03105410221b80c611038205000380102203c811003807020764402003000102e035407111450602040704106210181c0c0c46201c0703141d1004198001e20500c16a507150170b24941d031011001140f01a000102d03190440c4084ca0100070150503504070902a00c1099002505849000100710038180c0300d004220f2050303c00d01091211040c0e2004041d962081b0701070195111246408400c15402851440700c840e4014030700116031404e203600c5a01c200130806441200c0081058100121980c5800c00d480e880b8000c2d04103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 878013947 1250 878012697 878012713
    0x3060515130c030912050c1e03180307050a03050307290a05040c0f060e0301050c130501032a08010e090109030c0b040212030d020c010b040515090a0f1a12 68
    0x3007112400c0c03802001c0c000c0d5105040000c00344030343c2103000c803160044c814600181411500038005d174090588545a0b004131080d008064190b48003400418111390300441c01c5ca0817010851490081d00700c0ca41d81d00d840b460f140000e0a403181040300340114080c80103076880340e4040c20304d045c0300f0450511202940e21030341500c111203240e04c0f80c92900b1803800580041d0507a41e52074943c016000c20b0f0071090507824045c0000604982c0109a00040c0000707400901803616140c0c4481114010110b000200e07452100e41400254480d9002200d1020412141c10405d0340c10300d500350080c411105214000380e9078400501000b00012145034000d60284020080d01c00943c030700809103420500014031a010940c041003c0d503503810341d14088403014005407950b5444015240e80294041d0082e90307499400d0515080540ca094401c8501c10910f043c0f012450240c00d504000300304000805243c2040c1c3e0340c0d02020325441c3c043c821407001c4800314a412405200b401d042000014250410008079405040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 878015197 1250 878013947 878013949
    0x90503060601051207121406040c0903080d0209130908070b2a070f05070e1905101a220f09020307020703030e0f030609160b03012304140f0103060515 66
    0x42144d0b03011075007a0414580d40c440e010103c400c42c80c0c0000d82e02e031590510403401039582200400d1401103600300c0f800c1142d81403080b02911240000e05c4051f0402105018040c1c00403860b80003828280801042c103002005c00c1084c02d42104d260320801e41d1007c50200d05402017000301001150000030b00c0c94081c41403110310701842c406118500451040d001c01048242c10801540c1150440550200a440d503494a0f025001200c40301291402944180c0a030100414a110f00c51140540c140c6004130709101c1c18a080600a1166074042070300c2d00c0001c010301140c203010490410980303041182c14050382807906008034030824064004141c503501c10014004003540024494040f82c1e030505101c0b8400711000b00090f501008020483d07050b020b10410011000b1000c60300b4000e2080040c504078025465881c1c01071280000d0050070200504010180c42d0b82d505100b8003448560001c0011884249130310000544d00f50030364226420024000040c800c100f805c5c01040d9101c0303002415000b410b041e100c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 878016447 1250 878015197 878015207
    0x801060b1c0c0504180b030106060f2c0d11090601050c0a24020708040312020703050d080c13080606040b0618011101021e0703030e16090e012406090503060601 70
    0x46070200103507a1101080780640c0a502520014100c0035001c0505c41d100304e80c400c0c0a071110703080c150700c00c0d440d040c0b012418901402c10001d40001e241d4400008640340d100e00c081d034404020101602c0c1c42480f950000540d00e0075041c40302d29106500c0300c41500c5000080c4a03003454080c01460601c102402510501180041c82514250f00880075006500c40d810003042a24210042d690415000080c100d05003c0260018030403207104400c00340c101254401c0c00ca8440050303000040080e00f14140850309c0520800a46410a42d9641624a481d070741d8884510303800040c1c0e00481c80c42d04000b0130007a451506114030322000100b17483c0140b600902010900f03038400c00f611603605110710154000c4990300e09506644410140513504000710380420b030a4100c3d80c210503000c60000c1e06015070031030382490200b01402e004d80396443e00140b06003001102400307414804076641c00b82d0368444400341541410340c845016951210140d0740400e0400368010490400754100798020751110043c00b5690b6848 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 878017697 1250 878016447 878016487
    0x15020718020a03090212070e0a091a04030519031a091519050301111e0a0203070b0916140312040807030314130f171506011209080705070801060b 64
    0x1030000580d50140d0303042c1a40144070300500030707400052101260782100c0c00012450309690309003104291070f94940341c040040d0307010b01d88000c0070801440614010040c107038030043d40042c481e04119060005015803154460007424042c00000d8039907601e20180c0261740e5441210a209665615403031a0030740324001d504050560803030007502d880c0354900c03011034443c4203600034046c020300030f020512207103c1040c06038005414004101c10b00384a250701900340901150070b00e0001d60003071402c01e451030329074449410008100a80b1030040c40c41c1940300c1704140500c140078221030b1146194004902c405c0c10300e440803500d441031000600b00400e000700c074400506201141d625191205001a800700003c0c1d06005452115003160041d58022034042003a00d0311100361014968020042c0d2540080b0665420481e000c04502200c0c1c5804500c89501c80c52105841c04001c0501113005c494940d5909200c1d13100f4401940e45800c200d05c148802c50082c040d60b0018002010034030300b829004d0101400140300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 878018947 1250 878017697 878017739
    0x20711090a140114120609030307080610090302041e0f0501060e01020703050615030a150f0c0801050117040809030a03080906090114010b1c020a0c0c051507020415120c150207 77
    0x1300002400c0b9600c1c41c0c82200703105401c4c1d00342d403154100b10002a0f03482c2c04c02e07076408011441180000348941400c09564141340c42c2ca0790f40070191407458003800020016910141c0d051081c0b607485d0085042640194404500104000a10307985800001403440c444d00307001504542004400700003203180081e2540d0850004c128030244070300c010001910f41550788900400c1072814138046109840c0d150310500c100d0340c0301302051190300e1079440e00301c40b0300209000d0180412003010050103d4003e40d201c03590302900c40c03100a4541528400003074500040d0150480000e01030408204c08803409015550308a40610020b00c15440c00613101121304d40140101d600c820400320300582041d50100c0018101132104508540d03446142c00700a1001c4002c64054841100070980091f150030301750b640c070315115500c2040504001041d03081001804950600b8213403690026804207805001c441c400203124070902c00e001c01e40746800315007a1103109100b258000e54001c400304010940383c7c029450307079441d9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 878020197 1250 878018947 878018969
    0x703050c0912250e07080f1801113408071b05090117011506020c040c090504050a0203040c0b0703020303071b0b1006090e0c1204030c06020711090a1401 67
    0xb4203616551500c14030900000324280c00488440c2c900030ba10003071005640c05100300b0135081d40d03440400d0b2602c4000392080c1c07983c29a144001440100c516003000d440030038040012400c40c40556a484507500140e142c00c1907403404101c00e018242220514802001420030441121011610380c142d09008220014020000481c4180341c07002210f000c1001901d401054443e00756121050220b80994607000c0c040f01358645480c01c01c0c882c0e400b050071000c84030607130300030001c01200f48140800380154189007801c0c040c00610201e019500d5000d06803140c000180c00503200c0c03400f8204079a50b4075071503000031804401013001201196020003120340c840110300303100155260310300718810f0303400940700040c2c003580f005424004841071014070003086845966415000e00d4407010704030040802507500c84d40e8494100021104091074174882c60740107010381050100046961141c2f410380c5e001c20703021600c030108402d070100b01d85000300c00b0641101c6040020803014000c038149084441060007a8035402c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 878021447 1250 878020197 878020219
    0x13140a090b1e01201b011814010c05070b090f09040c06050304080c010207050a11040c20210a030f02040302010c0209040620071e080307080a020f1b060703050c09 71
    0x80d016040928907101c21303c020134407114401280b0754444400013403c83c107102140710140c0c010b40c4245a42d03408881250582550685041104403900d0a03041445050020303482c480030106501340681801032402d0171000e961840550200000500c3d02108513203c0c0004e04144004942c0d0032000006070b07881410480c0d40c23522141080b42b124000c0f05940d003941c0d030000a21070300301b0a000c5071000e00d8034486da201c41d501e036002c1010007095a840c02c10083c001030200501100e4000c0710f048032910320220f0020303250400f8410206046412204045030360003180050a030f00c0d680c0c0d1512980503865a076082c11420281140d00082c8050031900303029105080c4400801d081c030019520030001e07200d10b440002a109240c40c0401001e4005a01c00e0707030190968030382066003000504030400000d07400100f45d4910764a80710141c9880c01d000d0b2541c40003941c00d0083d018000302c0384004020042c0f620900c00d01d104001c100451030000020403c00415051a080c081c100900205590f0b0149040710220100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 878022697 1250 878021447 878021449
    0xc0715020d0213140a0e060d1515061e031503061e150f050306040503030711010b1504240504140f09040f020a060309080d1113140a090b1e 61
    0x70f401600c20718018550203030310000e40c1200c01c81c05410001c01c02d41c0c04241486c0e1301c444c40081030408440840c0c0104546040c3c80000e441c6207003c1001d401030200010b4a00a6403241054145507604400c1c04201049006681d0448112101c2062049032405004201e040201d031140854903100081c0710300e407146480d2074840c5207543c4108040c03081d04e03400c010312161241c1c1070305107103010302c5607400e04d840c14500441c041c10045100c901c9903130060b00075841c544412401301c840000d0400002681d558548420701c0959a541450422a09018000e9190790801d145180900c01410340704100c1174101c50002074251304030080e034040b110000c1c0341e1704940c1c00b18404100c401e0000740801c1da00000300400c000c20001c0d48000405100e009460000c072035501c0301000e80c121a80480080c24010050142145011960308601d042084113000d907400c2029591400700c0c6d00c03460707030842601c2c059601c1c150250350510000306d1004155241c1c05105000501c8003103201d610b491041040000c140e080813802c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 878023947 1250 878022697 878022701
    0x203120a0c17270f041503020f130507020c0f010e0d0b1503010e15091501051009080d0c03110c0108160905031902031b03030306040c1101020705060f0c0715020d 71
    0x11290300b0031016052070200301c2e103180301c0b0f02200d2194490040240710041ca402c15120f010030514803d459001164216003c002d510b503071542c0290b41c0084810381251046a06029081c01000c0301d40042c141600c03060200110610b480f407440d4100000241c0d05010740d079070410722022590700b040e0103200c01c1e16004407112050030742d000c2890b033560070000544c01d00100043c90880b0720b0081083c004140e290f043c002c6481d605581c0e0300c0605c000080005200501d0040350700c800c84800d5007440f21015035262507403030405405040c024013040e107101c00d60080c160000134600e40c40411901a01550381000000707051744d840035003080080d03111421900d40e414003c4a215004d400300508513040d0841100021041d0b140c403803400c0703001e809142440100074407103d401407240d00c0020061400c5a540c902840003e10302c110104c0c4c100a004008946179038020b1004001242c0580c024142ca8504203441590382c510241ca100c01c03d01080105d040070408118680600004e05080966509180040040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 878025197 1250 878023947 878023957
    0x1214130204150605070c08030406140f0904050a0b1021050618010e1009090c060f030605150403141b09151806130c0219081c05040203120a0c17 63
    0x80064500000030810a402070050240c2031b01c2421014109521216550b4490141d0700c15100400c01200c00e04019841c2c800150006082041d41c4c03a00340191400000c096500c1039900b060b80301d40e2030707400e4807040c241800c82c0aa45492070070148600c100003041061000585020020420368840c003003402d40d0346010086010000e5030b02402869612812905170390a025146482c011201c15000921800b00f0300440c0c5d121034014003e001c07540c0c54031009583e030340c8449000d1020150380d0b21002c00c030b540d06e51040301e0880c10400030741d6840340d00714540310f00c6035401454a8650b9502041680004034404007a03018008002e55078100b840d00c4c2c01003a08a64140c0c0440f80303a000020202c81900070481c07071041c5e4407403942191051192880c40190404540b103c5003043c006070462090440d21001000070040d5580c0f0900890749401915129014a100003a071404540d07522070080c00b0940c642041200c5c03a480202c42c400e490400c0c10304003d4001c0c4a80c02c2d0007048079203070340681804480035009541d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 878026447 1250 878025197 878025221
    0x20c010605030616200a080a20010b150f09040e0708100f06050d0201120c140c010506040606110a0b04030314040507030c0b0a0512040807150c1214130204 68
    0x2600f541080e9041541c2c0f04260103940d000a212518410090704000c003000b42c3e0b0f064103001420070801030b9104d4201d25071160280070300b4000c0e2a945044808060954880c064030020000076000341340c00200142d0742c2c1c030076240c0d144404080c00b10100130300010040301c015401c102c0340003c01c5400e1803000c40c101a19070740005620300a0f0981c07051050b072650409d20f044c14003020308005003621a802c00c4081151a90040e00082102c1481c00039003580da800f51602d41100e0504259a0395402a07000003540501d074107100702d0b51544240001402d09010343c0c0042c1045044c05a0b011600e005806c2d62407000010140000d044000450305250195004001d000076020031320320300c4e14040c01c00581d40c1c0d00c0ca200c100c42d1304520710000075080040c40c0643e0003100340da5458515042c2200138400c4902030160080d90409800c0042800056201ca00710303040b020f0700c03600429500801040545501c240c1c8900c2401141012071082e10003007a030340e11640c44080b01000e10f03000d034000e001040041a19031588 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 878027697 1250 878026447 878026453
    0xd0f120e07151101050c040311100311070804150f1b0f020d240209030712021201150905100e01030b07030e0f100e07060e090403110327030705030601050103020c01060503 75
    0x40d0b81816402582241d469800c40020b101c291241540c981ca584600d1201406101d03c8803440005490301c9841440304110300e18000c1152a00b1920305c4041d80d00003c02251010000201003109200c240d10b01590704509040040d0040748171700010f89001d010b201d850715a16102c4a11b042009803043c001d6001236006042180c03501301c1071078002600041120b0018a19105c2c41c3d840f41c00c0009402280d0b10544041d024040c0c481c9082500b50342c1d210318030310490b4040890710054503460802d10408122000850b10790350058640021441281c8000c0c0040d0400740400005200400744029554116580841060f03d03075628440c0031001000c0121a4003140d0040c1c66041c0c1d032001e00040c0080c0c0c01e0013080e00c2000030241c9406010f0307035070210384520400314a5880f90781d8254a0a299a03076400342c02810207981e200910f0b02c21a080d54400442184240005144001070402d0040086ea80b1803042c0e000300480f9041100081e69070344140305050400d5000600c000710840203400160040c0710180407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 878028947 1250 878027697 878027729
    0x11090f01121703041a090111180103021c09020a0f0f0b0a0e030a030503070f0e1807020a0c06020601030b0105040c080c1309020d0507031107030507020f010c230d0f120e07 75
    0x2003c034a18070340d003450f1103126010385d0201d0201c000c18413548030030400c92000c2d240f501b420400c0c0880700f100a007041c0c0d414160f09110945120300c07051200e00c200009000b000072807102d184104149541d090f001216507580c40d2405216090084443c802503507403a04180e0749580710060120340059600c50000d03094085c3c1c4d01c03a1020150410040e50040d82e003030329020b145401c4a14201c409107404c4040d1035100019603d0040140005100c5641044032481034130743c0c1900c1034403115480c0500c5d038020801a0710443c010130034081100007a50240108840504c8600c0c07100c0c0005000d090b02500741d207210301002804076109064400303810005e000c0d09006640721014100c084005210840b003850110b410096021540e40701e05044800703160741919558104003254081c03001000d00c1c0d400c11418020400707034640100380301c100010040b0160030b411190080c201c003a50b906107003104522005103c9141c0c0c000320001d400202c1104400703100c2d440000c0c40310140309450b2504415510540070b004518103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 878030197 1250 878028947 878028953
    0x510030803130c1e081c09050d230705090a0c2309041109150a1209111302030a0b060a0e12071511010c0504030b0403030209210a11090f0112170304 65
    0x8013a20454940740280c644c030145142c052807248009050300d8000840002050100345011a5681079160003040d8440881046401c640c042c6042c060300c054441c0d0082d5002c020a103400100180c0c05820b1460a10601d00501000380c0b80720b074903a448000c105416240030105a00343c0065460900340240140620f201740928480c0d42d40c846920a8002c98031840c0b1196900703010400c0f02d080d03041c140d8600700e89440c083c52000051415000844e12290f02a072100030b40d80d01c8000030012240341c0000140e0f81d0502c03400f40f1044405c8090102d000d03160902020f050b02e5046a00315207001010b4600340308041d12007071a1070411603190440300300485603169401034182d002c1941807414880030000c02040c8030900050307415002c3d40c840140200d41c800000740001c0d101c1c1d0041c1076a030380041c0803459209550340e044821020900300c500e200d81e0003100a60144502004280c1c00340380c00383d4501d0001d0814000894608005004401d0001401080f680812103003500c603000300c040e110781e01c54a90a1500e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 878031447 1250 878030197 878030249
    0x3160f210f02240f09010f0c030204050f0a0b0301050f040908131509080d051b06040813090603080306060703090314030a09090c0e1e0405010b07060510030803130c 72
    0x75100d20041c400c040c448094903852607601150384003d00b04100181e96101c04039204004000c044100315501c039026111800098028421a9101502e0168480d803c00f418400d0843300313107040c05c1c8140783c4a0700420041c0026000c40707064820540f1064602c01c443c4020a000e043c20380380060403c10000b4900503001c4c8414801e20030ba6154006c107030945d540449044401b2a81806500400d03088040c41c0708c400b901a40061a4401e01004c14008585403902440d0800ea000c031025114640000384241600030110714a20241032018820030001e400c6440c3c0e038050b800000e100328091400050780e102410700800c0c00000450380050441c050103081a0081d80b250006801617020402c41c45000c00d004c0d03003a0091040881281e1340e0301d00610320400412420000100016103481603a01c10419681c032036020762130180440c02d403401c1d513401c8549007400413103400900211591040d40018000030b071909080b40e03000142d080030513250b1340007401c0590740305c4181e9100346003810f041840c0380751482c0b4003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 878032697 1250 878031447 878031467
    0x20c0d0503180312030f04030e061209060a020c0309150f030109020711040b030d080a0225050d020604120503090c0d03030e0c310e0313140303160f21 66
    0x4010b000501807042e0107060fa03480703d000880300c030060140001011056150800ca90281c002d18041c0b01c804c0806000c21002e80c040081000404071000820150308010802c841e044640d070301c801c61905962500b01a101e01420107414812000390012060240e00b100903921603e42282c031407a5030f0b5135074125200c025440b150048815280c109200007891030710b84907143c0c0700d66020b4080d003010908540c040300c007610020010840d0300c0c2d0078050b00106980142c4e1070310300c1c188540103903e82c20003141012854082410090011903000d80b04101c0098025400c042d00441036041440e203e44800140608010a0b40586078110251442c0c0b40306255042e0440c0288a0150080d905401c81940c140451802d801e081c040704900001107000385280d190500502c14251000300090141c01070381c0381c0703046038000952500e140c480400103005071600d0032841190700b4011002149404040500d2803180250300c20090000b4042100204c00d20207651700703400220955021030000101003407005001000c2c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 878033947 1250 878032697 878032717
    0x1c0501050c03130b061504080109031701061b030c06050c07020108060a030210050a051201031a09060f010605070807060507091403070315090c0b13090b010c120f020c0d0503 76
    0x30400864120404001128055616200001e40b518425101d01a516038060b04d078607040048654000078107a009000380c0b02038200c04001185006081c100149502c015000802c1509140c034010445190403800304a41c003801d803c2d03d8241032045080a9032074070500030303015000034140700801c43c07001d29200c02040703035038400d03202e084150302ca103410310115010314040290001c44160941d64098010806428105541e01e4013074580140441200e1030b0105c2030740201c80f4900c541d440000c2d20010662400d501210007401820380346804620701090030010311545051180005a12091040040c202c3c0c1d40c8039000354040c006070070301200007480503115100b140604088403d01b4041c9180200700d14044070b0300091240b1b80201517007a444020400c0c082c04807005241c14000041c0d000360a8041d0810340c1010300d851494514000d420020754411004103810400d5144c1d0032800900180f1041411785000e14180c80303d03441ca0030b400d034039120202080d60390041c0321588150030880004010921045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 878035197 1250 878033947 878033951
    0x7050f010209040e01021603081003020316030317040f0807060603082d0903070504050c130924030f03080a0f091401141e100e15030f0303090307140c1c0501 69
    0x1803110702aa081f03020305400c5981c1a00048500c01c0400c1c03140402e242c00c00c8020080425142d6070fa8002460944d409160001000030f840003001070542006000e40b100102d0310140800d850310343d0310502100000c01000342061400b262306001e00661341d0100019543c041c445070751b51014031141d10356400d40c1d03109400645114000d914030226441c403e0724050100600201900e034105010000640b100500000d0404000d02041c2e44150405c003c2e440246840f620010b40ca503150540644031000203500e0742c203e941f110104000044024502c02c1980c0d0309403405540c0ca0329102c20007000f6020401041e4043d504080c0d408081c01076201c88808145100b1008100328026440308040200e42184e04407440e03500c52601842c0c90f00c0880b001da80c85418000d14000c0c01da191040c98140803802d40307291010f0340e00061010030038202000a4450000003000a50461902001c91542d034032810340010304580c1c02d080861541ca80800c0310001100300102414400140c148005000c0d001c2920309464a40c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 878036447 1250 878035197 878035211
    0x151202160b041b1512020d020f0a03051509150109051f120e120705010204081203010801151a0a03140106020a0b0c0403050a020f130e01050901060e13060c0507050f01020904 76
    0x2188040f4002d04680010244000312014900c0a545050800c0c3d031141c03a01c0e0302003041c140c080803280f0040c0640076100a4807a11103000703a000400700c1d0b100034008044081d00104a0410703588a540c0c1d0355000c011a105200c0300c04450004844800765540140d403c00240e000114210460450000880c14240d4562092a1141c160340c0c05650300d141c0b14501c90f800c14449001840312007070023424020301071000540307440d64030003000d4a4030340c3d801c1c00300c2982c00c030201c01400303149003e00030382c81c00105003d074a0300c03454104046200d004e10510004441c03e00c0002c0c03800c01e082d010740c1240725480b50790400010300d907950f98406511501d06130000c45540d4000c80000340b0a00f00038055400343c030780013402415200119400d0281c00000c03031005542c03103800c90321a018a00e00c240a03107540089100004129810903001a0303094500c190400c4810043c65410815481c1e100703000c60a0803504200e0201d03255140f80e405a030b40f0b10480304064014014480341c400707130700740c150024080d00e070302550700300281 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 878037697 1250 878036447 878036483
    0x405040f060f0b0313080315120a030206010519080604060f0e0607080601050708090402070c05090a180b101205011a090403020604031430010f151202160b04 69
    0x1034101c1e0081004403500e941080c49420120005942d0000c482c02d010a88541c81da2a820800c0d002103446180307100c0201d0005049040c1510140d1561102d03c0007810f4080c55070f44d001c0d45134501405440d000340c10b260341b440d240c00b003284003007002001c0c020b090300d481d4102801c2502c00f500b80c2c01c5002ca20f06003099000c258814000900d00c0c4070381f0080e5144122602c4203001101c2d03035800840140e0721080240103001d0243d83c1e40c401030691510807014040b0f0f141c64030f03041c4005410000e10390f0344200c1c64001c009030700d05000b100701442c540d40003201c3d22186c0d6424000c1d8000e00143d03041041c003115050524010046d05511203101c04004410722009800da407820031022400403100140181c0250707001c240000e0041c0140c004203002000349608141e0041c0300328901d40700039065075011101016000d144944003540c1203000d00400b00c41d03421581c0c00c0012600549c40c00c1c501d0881040407043d003641922016605540c1e100b511415500c4d0311540b2803d04055a460607101038840c038141240000f1a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 878038947 1250 878037697 878037701
    0x1c0e04150501090611010207060e10061a070809030f3403120c02220f05060a03051203190f1d0d021c0908033906010311120a05030405040f 61
    0x21140140d4600c60440d0410303074102c68090170716070804001d64080c016080012070301c0c003c00444104900c010300c00c4120415510b01a13501907842442001403480c11805540f215508943c0c2c805e8201c00015905c060901c007280c60f0406840c80585c66006961809281810180620361044280741e502c0010030154031441c600c03010a440001c0c108001d0350082070a2030b014800b00e1040c54002820322003a8800c004014002c002d0324104544450f030f8032081c13480200c220b4828141c1040c0141e5095803000d056a450650710403841480c8105600003100090801d226810740b140a6010714000b40030094100c883c841c00f030035440386118400d40c50041d0307159414100044030f441c500d9095008000c1500071446880b9036491254020040014204c0d01003402c0004100a0004c0c01c68644401c0d0741200020003500d20715004152804002031920079180c4048001403070905403500704881d00b042180c66400076010a00076500900300d401107201d036006012020000d4011102d041c0d8043c84450108212201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 878040197 1250 878038947 878038949
    0xb19110705010e0d0809040c11160e041b080d030603060e010b011e05160c030303050c1603050f070f030c050d05040b161e1101170f07111c0e0415 64
    0x10000f542c0c220300c4540c5180c14240e0130302890042d103a06142c10f010401207000e907852030107031780085801130902344c0555030200041c401c5608a00c080342c0f8001c1c07c005807100780000146c00507140006401d403140350803240300d0390400100f454504580c1100401c01003d406041c482c40292a50b83c03a040c103580c07440f1410302842000c81e405a5840c03103000004000c880740d01810300d80070320800405002c1001000d02c4100a20000750040b082e40c2040c0e03103103240040c29510002c00010f5a0002882120250501e00c00c1080c0d609038582022a121260307154040300501030031501428488030307800d1480506400c01c012001017401001501c4500c101704030207170345901c42d42c41900c0c6080420000f41880c03540b40304416441d588607010342d255a20490000c0d06010358101c0d02a00d20840501e201001580c11500903200c40d01c001801c941340b854141c20300c1c5003d03000141a1424050103250342c09003c0c5007400304100124a0140c10400040180002417482c65104c140174092803500c0045100c0d2103446c3c13440c0c1c1c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 878041447 1250 878040197 878040199
    0x2041104050603160203090a031a0106020307030c0f0f0b0f04050606010216090b0f0406032117070809120f090112020c190309051804030e0108100b070c0b19110705 72
    0x10f18684070000b0f68a29608401e000c0e0045000034420703000b044e9a2203584000840c0600140314001000c4d03210700e429042c06900c2002035600030442600020342042801c260700f40c01c100214180d0420f41400c05082c01246001030121080c01c0c100b040001d0410300080c0214010022104c4c6961003800599a841c64188142260b4907000070822178a001d68004587e10784018001403003010514000c1002e40d0001c0d001107401001134415a049461800f04c100390080705490001c0403149010556a00b40401070a100d0811030b246000030102e00b0108802411040880820b5540d918261207021b440e800003007840740094080e40e090042c1007004c1c001c1e5041c0b04842400b5045104480440c10b525030801d480480074001c10140000c1c41d40e0303541041c0d000744240c0c20005038151800e031400030300d03402030711391528148074100c0f003409650b0250312040015614001c0082d59600c50030306284215451030341c8100516031000800000b24003696035042ca4070501501c030f801c040c9a114030155103c1c0c41c60b004403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 878042697 1250 878041447 878041459
    0x102070521010204140909010204030b011502341a031f090e0304062a03030e0c09040c03050c1e01050a0c060c03050f1303020303010e09010b03070f030204110405 71
    0x140810724000c140012141076400941c039070140340a20541c26a08150700100c010b0000c01d83c849403909101460f954410481d4000714901819951409103154060041501148002e0030480c11140200328034006600ca802450b010f038400c803150f03e1080c004201d4401800040d00c000061443da0410510304100c1170f05501c641580c2e68254503070224a60001e00300f10740e0620a2001a100c8110302ca26400201e100c0040d55450703041a20140440001c0c003054020480301408040d000d20302e5400b207162041d41494089002244225920310f080816240c0c154019551402c3c04108414a202032003103900c80d00640e00046045010804001020b43c4551007500000c14900304961044006220780b01860400100287d1180ca4401c1120b50714014000440c1c0d0314814813007421000b540031035114412b50300292102a9507600291240018403d54900508104c040740304100c080d0044c4d5400755014044511099942440c207400c4190762100f64080c0f450940107080b20b401040482c4c00f580e07406410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 878043947 1250 878042697 878042699
    0xa1205030714070b040b180a0302032e020d0504021011070e0403021204030813240507061d100f020a140703030e0d0306080c190b0304081e0a110606010207 68
    0x807000b00c036500050702e8900380a40c1c40c000c9100c096000c00391002d0b00000d66113584550100710a0600c1c03804c3d0300a014130030405100e0400040e070780096110800c0c20b10840c1018080500b0640550b41c0c40d103955181d90707043c0080384a64814400ba03110500c141d00844943e00012107022090320300035858880d0417259044020240821504000b0b4542c10510a1046445001102c0a44d441e1030704150000c50318608006072211032001d0b80803d80c0080c003440556180307030003e4001d50705140c140034800b03070090000110340c9100303200d0117500c001c0075000035081c0d072881418143c103401d84500d190044025418a0050903444501440c400c0e03074800066a10b0700024400f13031b504649015044044103d040646030014807110348001d200c000200001d5032008102942403039846818410310060b03107409558604040c468514048500d002211464119182c0d6903d070760501c000d81d80f1600c034035120103281d040040405d0743c11610090890b110641c0d100c81405040c000e06949914007510510300603440044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 878045197 1250 878043947 878043953
    0x10080f04030207030609060e060615040918080d0b100c0b040b06030a020301320405060c0f12130303060e15011101021b03030901051e0c090105040b12060a12050307 72
    0x1081a4016029004880185542e40d03250350988186e56000c5a0141c1c90715a441c0404804102054100c50216140403a48100e074003006110300591254443d5291600101c1602a000c0d1400c000c2654010321116a10704145164074050115505881c0c096485080b5020000e8032031000c1d4481280d10481e407074660380712911420444c1101604955041c020312420b540181d500344210580d5403190a101356003080044000400c1d070000003007180e401c03202001008001040801c03200d40c89105500c08980310380045166450501414107803140b6501e1400078802250008000c10184a00c80c0e98140300043d10380c600510076010503034850b8203524075805900b030030b58001d6210300c50003685400014101400b070041301010141c00b0700c0d0f1007003a4000201780000c40b802800399a0303100d10300c0c011448000c007031106690700300c6100402c13007402d0030070104105045a2080080350300600004a8881d116080c05c0450241e070320043e9210b41c802e9401c02c02c001101e44a454801a4068100001e141402c5451f1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 878046447 1250 878045197 878045221
    0x40905070f080f0a0f06050a230402010201060602160e1305030406120b0414060f12010216050c060a02070b070f06061401020d0206060d0807050a0b011203020c04060308042d060215061008 82
    0x1030004440162207611070612a0527103002100d2040c202255580765042c1b900029084a62682012003103400034000c02410781c254112500403103840e940700c100c00b965245110000d444125000828600000034000307080d82d84800340c030014500e20300d02002258000317410030084842d440f81d00c40040c030040340000c0e902c4c5442c2044018005c4040c0011100c0d24000b031031242203900c05403001080070400c00d2070703800703010003008500c196640a07035050b468a9181440a0743c0ea190324400c080382508006584000c001c5003120305454154800020701c072098032400100d1500c031000f03090500610400008100303951001543c5805450302829400e5107486a4483d8296a0302c1044c05a4440c455400804005a1540109402420150860300101d103480c0b50090a000000000703a10030741c00c101003440410700c14012202141e0700304828210703a03007204400501020f685c00c075170f40e016240700394001a400e4001c90800c00070780c2a41820011907540508121821803404038840c00241c0010000b51071001e20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 878047697 1250 878046447 878046451
    0xb13170a020109150c2303060d05030c0114070e010807050d0c03180309050a090b1c03030b0d1217090304031b1e05091806040b06040905070f080f0a0f0605 68
    0x141c400800c401640b6140c80000607829550303040f0071070f61040c461082039070001000848403d000302c900404a2000340d5407105000c054021441520b050103900c2c02c000c0e003001200c0820760824000d102e94802c0202d1300160010440d84000030030709004003c01158403450589114564989400e400c02d0911000c43c401800001400300c28141d80c0c191a0398000e8804040c404410b1081d41c80c00c040324141014031510200c580d008001076420a594a1129a07a0001011113256020007142c41044030341000c50140c00c10005d02c3e40c1050042e1445014003000f4460070342c40341c1480d00d0b8880d6041c50200441c1d44240210b5900341d59400a1000707000051000c107290760a00c800c1100c0c801a81e0311561074501000c1c2e48010406000c2a21008001c00c0c28803240480e40b01001c184200b0032035203118041621420001c1009100761084000150b4030b82c0c5a5000450240c1c01030100d4482a440e41d00440e8420750138044d500641c852040c1445e000f141c00074800034101c2c2d00c4649032045140b2075444002800c40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 878048947 1250 878047697 878047717
    0x10c02060403272409061713060c0801050910060e0d061e05010f09090210120e01110d0e07182f09040c03020307050f03041109130b1317 60
    0x245502c900302c030f0403803006048083c0101c682c120510501c15440c02c0780045408034618240f03c0c4240c2c0030491a50001da80c2101c801004090503156965203820412920710007000030074a5152544014406512045031810f98038180c941d04116107d0302442d090890007071095400003010b29070301d00303a94100b04d6031090b601441810b0201d00707003d001e003a40802d4244102000091a42d8074010481d0b2013160f21804014a01c44400b000303180b1080d0041114040c4900319031080c07003541d080c240341010082d0f100d1140501c00380020441221710310484401030f8802072490305c1003070a10544151799440481c15004807200e1130000c40b00480c210560708090031403805140f8164450041d490303203880014501e4000c800381200c80c40e0781e50107004104411103200c07140c20810548113004220345550060101c0301080c4a00a20f2a03c950b01d40c0707000c1d20901d001315141908501c4000610514494164035400524070510150715559140301400c808504041c0014000c0c0e892007040a04140b0300030020300c1501c2d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 878050197 1250 878048947 878048987
    0x703030c1104140910020f09010f0e0603070207051809071221090303080a06051c02150d0501030203121207050c0c12030a0e0f0d080f07060908090a0602010c02060403 73
    0x907408001000c9a6001400c60040c00e502c03010400c540b40d090011a0202003660400c600306038011b8000d01d180e0207404006d83c1448400f20300808607900521184485120040030203a5034502054001e481d14060b1085600401c42c023145a100c15121241c014400c40e00c0c00000d002441c68211400b85041d0144c0040d100962049140c492503109804041c01c101e02c3d0b9140c02014038034600c0e000b00014801003040c1c0010b0f10b000700c01d103c02e566400021065061101c041c99a0303d0782400001d414207800207200101050000341030002c3c480c1508a14100c0340200c0c241c550414404031107a203039105207030180712100c00342c50019564900920103040c20b40e5407281190702401d41c0a0100d903200e0b4050740d22030125400450868000783d0322101341c0b42c2883c2d0559030b4000140d024004141d408114010040c002d400104003590381030728601c2522002500103c00b448500d482d410010075943c803c5000901500078544041006801405104081000c40d0300401d841da4035500c040b40c0411030400d070f807000d5070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 878051447 1250 878050197 878050223
    0xb0303092809060e011d0403080c0912070e1503030a0c0305180301020a081501030b0d0b092a030105330102070b0d0b0307060e0d060c0216090b09060108090703030c 72
    0xa40302d03c0b030500076104007020a80e0380c4d410300c0b80c0c184c0300280309a0051070804441c0d04000c0000e61103419203420040000740c07651921502c0d0000b86050b031201d05d0403215449150000903903151141043d90090708a07076040039024202c101416140d10840524a02280001200d40002440f41e0300925a140002c0b4008003802400f0002909a034444040803000941c00428000200321080d158800e05400342402c000000c0c50a01148401174849006404e001000300001c41120060080543ca07100002540c007a8900006400e01d80c1440c2e1100580298a01400510740317140320f65030039a03c0d4490100c2e1002e28600c0c0c09424201da2502405281107004800300060f5415100026000c01c4810f5080810455850401d0500d00f90280d800f1004220b56070f804044a03071a41c44c445c4010380c0e04000302081c044030b0329a05a1602c409190000c039800c00d00080021110010307404452550030403505007510391640401103031200f0b0b0a41e14040160004e9604200013030241880e12212442000181c00d04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 878052697 1250 878051447 878051459
    0x506150d0f050a06050603031603050c0f06160f080c0d0b03070302040f02070b0a060b030c0a091503020d0c09080319030b04050109020c1207210512041202010b03030928 74
    0x3156140d80700700c80660010792454200401030060f141d00500580065007010001d0b12009110b03000100003505201c000918a401100d090141000f1409500d08a80203030034005105407003901002d18900c0021000c0b02011401c0d8460982a4000d034040400c1174101225400850000c144400005900d1301c04c1400010040e2160300910300c40700c640c064016103888032818907510303500c4002c007030390074107031625809000c820b0407d4280ca800460000c64142c440c5591642500c48043d00d80040a07580c41e220061658182c0c150020103142c02205024004516072400c103407001c01c4140a5401070341c00500020951410300501d000003181e0070b103400320740108a080480c2c1140d5081e000f9160341500004c0c1c042e80b03180c081080c410007003010300540e4540402034843e0054400d0000c0300c1c1a010315503003581400d240c4030750300380c0307680e0f05c4418107014050406140c4810092506403e000c055403c01200a03d1860088280e0303000410140001c001d84040c641c0002c00244400c403000c0380600e01700004141 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 878053947 1250 878052697 878052713
    0x60d030e120718140402030a0314120a230402030a06051e130303110403031707030902030f150907050a03060e030705100b09010b0c0a14030c0d0903021c0506150d 71
    0x9000540f01d070303440d0b158402c001c43c060301e50f0315100050000001003400300603100010601704d420340614004003a1103110109025501c100501d52025403400030a104005d11103a000c0c8801000d07503034158180c1401e4012104441600b107078082e5064020340803420106429030400340e40000c0c046414000a0190300c1c40441081056800e44c24411b9078024160030140c0500c102000400004ca07294182461a500242800e403080c5071030005651440c08030300c4043c044d8010162590b8010260b4041c0801000ca4603a07038004900015a01c4042c00f003c01d003e440301140c010156000076100688050441d140c0d00064020840d48401c6d6200c10414500491824480545500d4401001040045400382007001c40308041e00b0103443e4240401000b404c1c8400042d8210f941da42c86901c440310310b00c00b007403550304502500c404c0403260301507100100c0000c0d0307200c1000c0301071741d1080340d028100c0c80c01e11815001402100348000c02960201e00031412110b028406035540d0b6100410f5204414150358821031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 878055197 1250 878053947 878053949
    0x20a0503070807080d0201060f090903030b09040f12050f07030c0219081b0102030306060d0b04090204020d06240905190801020a0807030b0d170a1808070302011205060d030e1207 78
    0x8a075411591040c0401309003481040104a480e1000707001c420300302140400b100c0d1051060007505961108060b080501035080455441c0d03009020f04024075181c103090443c0d00032040200c54139140c01d0361a0003040c0c012402d80f80c511a0f03494031035003030003995a41038980b82d5154800b82d82c0498061781000b9144000704500c80038260001c09880000e260101c291a85801030303c4090554205100300701d00c40c0c071400e05840f61503101c1100840c2c0c07000507902190045c64407440194002e030001034402c001440f990441d2003141c04008482c0112030580c10428035450221001e0000650030a05c1000685450009010020104d4802c0c403400750f0766080e44d0f400c99118903c1c52000c0b0f0001030401c0815170f0184100004001d0680e20300c00015243e030b41e0040d51401c580d00404d609074011410b00205480780c0410000c4202c011581c10300991078103c1030341e43d006140300490014401013410369411500e17001d25070050300c0140c4840140c010070340d0252140c1e030b08040700a0b04188440a402e03e07441c820031510b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 878056447 1250 878055197 878055209
    0x604240305030c060f090c0904061d010213060903080f0c070b0324030a05120c1002040b1207050c03090f0607081b1c08061216060302030a3204020a050307 68
    0x341c0d40303c1070243c519080c03000041c55035074002038860400491391000308a8040b401741c02c40d20226542d072280b80c0040201904042094040031154402111560541c01070070050308034024a0021503407500221244909404010040c3c80c00307228090380189010041c01d0410000410344958549401d9000501d8004803000140141c002090b14903543c000c500407001c404080d405440304041c5500c400d40e0314100601040d0103040f00081c94602020180640342c044640302074199903980d03a5807a01d141540004c226298a484500c000c500c2d414040c2084460b1003038280e01650070201c0301c13020410b51611580f860f40d040402005104001003071803006103c0036031085100f90403d6240b10b07919141c051480280d40d002544060316102d2260400e0515601080072035400f10100c42440100c0e00300707820341501d207803195005e00d00851295055000345105d4a80b941007005074015091955243c1c50302c41882181e07070350134400000040352422441590040c0040c01c0407030700341c1da01d2011a1a008666110f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 878057553 1106 878056447 878056453
    0xc03070e0103110705010e060a0213091806090b1e0624041208041a1305060d09150c021203010e070c03210504030f03140604240305 58
    0xf1480d42c0c240c00b0809485095a1030000c1c00f03419598040c90441c0280030000d00944080e209848003c3c0300903074109030451511260400800400c401c0004c80c061182e99600464103900940445a02c1413410624502c0c082c014008855010300c050b0042492540c00e0000341c2d45d400c0c8010703804102082e0000110144080c072072401b48102c5d031100c160100b54070074980a02c000c205c00f1b801222950b580c044203140c01c0b5594100984606c40840400000180c020f0009040500241800714400180003641c0c198030703101d4074500004901858a50b5032903000d02425540d0511040e00d0341c0c040000d5a030704650404402e8401480010084010041c0190301002407501c109144440c40a0301c0842d040c001190b0200c01004d8401140c060b808a0911514161524428858420100c400741e001807020b480d194100800b500c141c0280c0f0201e1040301820640d0080d0444441d4025445103001f = true := by decide +kernel

theorem cover : BRFrame.Cov 877877697 878057553 := by
  have h0 := BRFrame.cov_init 877877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 877877697 ≤ n) (h2 : n < 878057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
