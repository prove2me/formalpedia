-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4152
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:43:40.840994+00:00
-- url     : https://prove2.me/submissions/1dd02166-13ad-44bb-a81b-5793b4a478f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 746582733 ≤ n < 746762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 746583983 1250 746582733 746582743
    0x30b0a1503030c02131b0908011a03060703021c2316020307030507060b061204110105180d0c0e012715062717062a0d1d06090f 56
    0x70341c0507601c074642400b4a508001041110365041c03082d00351203078210582003882c541c81e44200c4290741c9840214a160420107429034580742c64140c0442c45903005041d4548020070427130360090341c40c500140c0d11034195030942c10040c11410b00e82031280c81c2c800c10003100c1d03042400d04044021180841c5015030354041020340d50340c4a003080480140c00c10b01181c00080e0040c0050000a40b1132000071814102c1e15002c610950414482a9891104030b0140000d001d0300059190715680c00f0311340589440340341800c40c8002001c03003421a020781001c5262030f0a0001040e80c4130050010020300e080c2c596910081030303000d609801c01281501d82120700000c60742e0458400c010390070121070b41c2001d20514008090300e10b40d20901c202d507038080e00402c1e40300021448020060141c0190314080055010000031b1604c2c1500091110324548005051441402e030818081020f0600d58202c665039400201724120160038030322000341c103024407007a0503071406a022500a22541c4c11000310342440c1e4142c034a19940c3d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 746585233 1250 746583983 746583989
    0x10603020c0c15040b1b060a1407020109020105040b18040f0218060715050c0d020c07091a0d0809030f0115030501140c070b040f050d0f20071e0f030b0a15 68
    0x100703d00700020060f9030060340c0941a40c0d1000d1440c1d1009140034020141030070412201c180c40302d070fa100791300451000160768142d007020f4584000c10401045500184c0b00c0e2143d8000d04401100c081203190205051803000410550060018002515a4000d01029400c0341031001c0e07152a40c848020a641007035000e41d203034150005a87c951805606190400800c00902101c110700b50420409040340a54002400340c0c0080300300903c0c44500d0000400c1c11030310b0310301c0d0b400310f03210016030030790b029541e9110341d005415085400a40d0b142170240c00286807410111071130b0804d50901510003001440e450110342100d010340024001c01145400e4440c001104603004400c80c01c05012282c0840c1440654542c454171920700342c040c0208036152180b030b2201c00740b1020300080d140034034400d0003a44440c101b0b070300c0842141180c0d03104801136511906c07100e8074099440030f908a8085030002a50040c07070503000301005062544c405440b0305094403084001c5980c003c0e4141001c09040b010082492a0012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 746586483 1250 746585233 746585269
    0x130b121e01150b1e1c0f0c02030d050a0b030f0313050409050a03110304030b25050306030a03140708130608010f050904030c031e231603050c15010603020c0c 69
    0x440790500b0443c0c440b0f41c2050394280b00103880d1105440b0f000d003401009040361240c1c15000f4141100744810502550305031100c09944905103032615140710b40000a95020b0700c500640411a540c03041c2403140140b20305a20240d051046480d800a82ca5000c40282003500b10fa204141959459000b44403d0b00c0b03500d24002c2c820b030f00088264006c20711643c4004801e251290549240550b01d0b2140c985020068990b080150030600c118450100034031020403000d000c508009055182c8100000c0d11141d6000024092060400140d460001040200c8041c0ca501500c0b154941c0c00c4008070440b40039080c0164008998a6000031526242464612080340d9000b445000503a8450342e0840e10710640b600101c043c0103555040603140c0500200c5c0010164041c0d03540c00840703c4520482c516039014090f032245840e0100000c14600030103113049158680c050422655500c030100c0c41c64506400d083c030b2001c01484030000030540540c10703002061800b108800f15081081110700700504903100c2800022 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 746587733 1250 746586483 746586521
    0x6050307080d0f0905090403030605010e0f0108060f21030306310c110d020d02071e05060a171005090105181512100f060b070c05130b121e01 62
    0x101280c450140440750343c400d450b0113101c1c0d955402c081a1051021b680440c0030a072141810710107540e1040300a40c002c1d000316840c8400e400541c0010f44038100c00b914043c01958010682030103900c50000c42203c0c070a18901000303d0b07601c030001080c1c6075042500c00e80d03c590000340e10203944100114410306076503105540c5501c0e9100080100c002061078585041c28004030b10980f071280031003480a9440c038143c0b41c000d4079186054580090400240350030040248604008451460145400c501f05650b826202d6954401085105860031040d1107145d100562301d0780c0c2000340c803000c01003140e0110b94065a0a240030b0762120100005c5025452100c6103030180d510000e02c54040703074803510361500c0b00644a03100c030003e2007210302e0400340e40305500380b0700d56181c110500345130700725100e0030000b0000d201c911414050310342d4400d880e030800c0744185841020500788205c0110324a038881c02c240b0900030046c1070b60483c440e02040c1c8440c996038100000c2803010070302c08443d0b041130140b001078100d22400d042c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 746588983 1250 746587733 746587753
    0x7080307050a0e190303030c09060c1b210201030b0405070f0c0212030a0e0a0f06050d021c0207140f0705010e0607060e1509010e0c100c14010c050703030605030708 72
    0x850301d41149110108000c0340310f21100c43c40e180d041000c100c000303540c1d0300c08415500f14100a810b075200200c1440420410860400034240e1118100c800550b0042840c0d032400c0d44489441840750140e00110180c08410301042c440c0c99640d81d000031290b03c00e032001d1024540c10002c02044480486000020541508820001701d00c190b880b61865440103004c1c403240c3c0468040030b45590440401d80000c1101c4108521041c501b62142d071004200b880024000103041c450020a140503c0c50401d00064000c9901c8081002c111403030300d1a040718200071515011603040102046903494070700ca50074004c01c4c84040d41d609000c20300e003094881c103031282c409141411084c0401603001200541e034941c1e4500c0241101c107401d002800d100344002d2840151801c1400c2c3c51421150900c44100507a844135070058800d803241680340790203401d94241002c451019003807100303c0c8104a4409040c65103090410702003250010050100309020b60f8040050544403030a042e80d4484c80d000b40b99096212081c0c0c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 746590233 1250 746588983 746588987
    0x60109060e0f070c1202030a080c0f0418111201150e0a0b0d09020307080601061101050411010c0602130b22030f1407090507120c1b020f030a020306042607080307 71
    0x1103a0030000901e00301e00f4030520b580300c9005000100791042e00603000000c0c1423481039404240990009480041036141501c03641c0c08c41d86904c038601c542c0a140c1600080341c01301618a6021898a007600610180c2c0da010741d00900011403001d000e011002440940000710181c8114140d494401018010007078080c14800820800d0300b00d01103016116448035554001610203200041c01440c80800070702c00d9505008001c0c0100e14002c914800d907038904820003001c05e940d80452258041c0c2800c1604500c80b5500b006c0001c0e00c40c0e40c5460081600c408800514442c50800801c140000c00c0d00303001c11420640c05250000106110103001c181c0b0160601001c00e20030b101044610703104604413086256200341c0407090780c404950003c049400103124a0549400c2c2c021009038204c1880d00305005810b0b006400449152080060300800c402ca0f074210306501d0800034041001d400170221102450f0a01c0c040f054804e43d103031440e00030b110b2090240c240e8020101074a012580c441709031811965080c00c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 746591483 1250 746590233 746590261
    0x94401050f01080c1e0a0918031412060f06070f05070806070306030f02040213050a030b1b092413090b03070509070c2603012c01060c03031104081608060109060e 71
    0x1c00da000078882e00000d8078084502c03660381c01c00c02d81d900b01c0205903010305016100e10289110603407440790410495000c001d28540c02f40d07000c8030071600c00391030718010303004960540140400100602c126041d150207202c40000c1110458030a001242c1e170543d00d403a8200c0c1030300d5080c0300050200c400c8001d100c00505d856000f03030074041e64084404150b1540d0f0000100720345113541c030648400c2ca00300b0030b120100d1103001c4138004680003401c8403858030b25803801240703524800140b07082c0024056501c1030034030721902c0d040700c80d2040c401e6003c04925440d180480c008043c0002e506102e8070506d04006014105050881c1c4078200c20380752001000c03601d40b1461040010105403203200440815a076102e454040c01942c084c00250031010080450700e0348410003419108600c4c480118502c0040246c0e55108516003a10366052401180c030307003649400b403441409103800c444010f00850b4000704502c0c0010110034200c1e02480c0807034905990b50284603044502d01d0052900c6411b01c0340c0003a00888000c05 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 746592733 1250 746591483 746591539
    0x9140c0102280f0c0306150b04090c031b030b0f090c22030b07210e030412050708010c11070b0301080a082d031006094401050f01080c 59
    0x2d2050280364140d96030b80b80c82991504119840750309510180180159407003000d401c0e4824818202d2550305000600c129405103102d80c20341a625204031410b99440f80e040300c0141c00301c4280d8650300c1c90004501802500030b15902034040e8244000710081884d224440318003903401c0c019114030b0030800a000981821202f00c0141c600c0416810020004182c900524401e1013155a060072a55090510340814010180300081d8a41081c0381c3d01030b000404000c64003100e0011030200d51207045443c09034100b04c6581d05c200e10039464520301050381504051812802152902564503041d120200c11400d40428008d40040c0d03407181c011000041d0704040203054420200c0014040320f6805d16843c81c0c004010540098030311000300910000705540400362011b000c003800c3c0707030b0442c07030520004091007280302c9004003a402910120740c58100703045503040000612410510190040090414040c11083e540d02009a5050000051801d00400c1c89800034000400303e1015104104031002c00e008450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 746593983 1250 746592733 746592793
    0x8031902191b05030a0e100201020c06070e04060b0d0516110c15120916050d050c06032703031009061212030f02041811070b01090c020307060c0309140c0102 69
    0x20b4070200400c02c108041c00f0014090390700c40000c1241401406001603001d104c5a0039a07006000c2c0300c201110200d462a802601c51401a8007014400c00140240400d035000c464500b43c0014864400101900010720505801e01c600710544400c0d18202e942a42664580d15240c02c101d1100d859460b140d4140c91070400c0302d508440c144040502c84070f820003002e48a1403061340c025030390382c1d030394089000141000348021605c00c030307007151642c441a4583c00081c0b0b0b05441800c00100040300303e59041c450400c007070103903030b881007202d00300081c029507070303030047e03031240c120042c6250002110303120340c010882a0f940032080e4a030546507a07624030301c8900d01445d01d44189600d840c0002a010781c20720241004007541c1640310100d43d49030000d502101c806450401d0417103410080301c00807802001c55981111820400020788a0010200f24118040c13100000c001d582095982400541d01d80c020040690090000030318039603a030002030b944c41d245030b045580560070102040000d1004a01c820840400d04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 746595233 1250 746593983 746594027
    0x3170909091509060106050a03150801020c030301031e230c033301050123040308030c0324130e0a05060c0a09080c01021b06160803190219 61
    0x900280301058100d030300808551190040060403203072010300640001814002e0300300d550400400409600c00c80d00d1400034161500600c0c030703050000380c00000003040b01d440211b403070300f007100400e503280d074401c1c071064680303c800704000d070080154038070101000c0d5070052601c40120070030700c07030109050b4030a030030300031280146c281d1002552002c0c84004525142c4c4603482c817210032244071901c0303815400101244010300368401071000da40c01c03564100b450703005000351102c24084061480554412604001c01401020061003011000c04c0c003d180224154221000c034459051500200e20303c400c3c0320658054021480c0d41760b40e0030180c2c0201c84420082c8141c680250991320348918020065800d9401e241c070000e8514043c0b039000b8040f8010305003190250106506000c0000d644c2c004c2425012850822100b0f50a501d070b941c1d2080b1590340d90480400d91502003c1c1c14111240c0d04101d41c4032003030240390302d854500d440d4148221003c0c0c091105010242030000401180d058a545080c0b140800e15 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 746596483 1250 746595233 746595247
    0xc020310020301091410050f0a080f060a0b0603040c0e09161401020c0102160603020a0302040e1303030b010302090a0902090609090411042711010315080a02030705010e0306010317 79
    0x28000900ca100c22124056500c3d450035244c1c2049030241000783d01c1c3c0c40d5071001408041d1268030844400c45808850002981030004e0010f40074658651240c40b03d8414401c10410258010810b644903070020076082002540450612146100c1100e00a1a030b00272603201340246040c0005086c0c1020b00c49045907010701c4112000c440c40c1d180d40d00111000c0c11040310010156a0410100000032020b10242c654242e03800d528640b0b0744058000c1200703054020401203011882981a50000c1000c20700100190400c80108029021100340542c0001e0900c0c1081900354080e0085900d4400b025144151151810115000a411000e0719541c031640401c071144042d030310401114002d0b400f880c0404809013510307040204991450301e0083d0846041b03c031602150b51995440000c1d140c1101001c600c41c80c0b1500120010311412800c5180a101004040b070518000910322142c03a02c01d0b4100d030040c9481d40d00544002c0e00b5182c40c954980e010000620020341c01100c07100c0e048903d48551414100703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 746597733 1250 746596483 746596489
    0x80f04151a10020a1b0b0f0903030706110a080937050706051c18060513081c0b030c0a0506072607050c0108150f01050f0c0303190c09150c02 62
    0x2082c20b00c4400183d004400140510081e07481c030401c1c407040343c03003909031403454040e1104050003140c01111403502c0c0890100b4843d2400d10444092035481202080690720524100301c8580000b1000000151043c0025514100000f8480802c600c141496110392801d4185110116486208020700c00179920801000030707020054000584101e840c1d540c0c440380d00103404122103064004002d802070400c103807200100300007441c1d008115040070000c138a960700c1c500450505114440001d02c01d00c0001240113606800316035002080807590030a10503088860308060343c82034840e0055510040c950340c1000503162600080c44c1d414405d80003100030003030380d0040002403400f504102050f40d000244020030003d040c840e03c0304200e002d0901e06504d00300403002d0821440c2d814081c60144805c2841e400482c3e0054080e1040d00384002d03a0350703681e0f081001000d0f4591704103541600b0140001c000003448010f190190088040c62030340e07100d003030a2808222111406452940509004601c444a00940c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 746598983 1250 746597733 746597749
    0x6080106140312130501081503060103050c0a141003200a1d010305041a1905090c030d05070317060f10020a1e0f2907030903080f04151a 60
    0x2240c0066401214041a01818103111002440f40c042e464100404028a00d6a210a400740c0e0b07420303c0c001e40a9039401135001010b110900f0300503490b2092000000c00c200c000203441c40c003040140c81d50000c10360b59500144054500300300150f400068204901c004c248254040303411604148032503160039001c80c0c1000100e500540350764000880c2c0c0318000780000c61000180c4507800003860204024502500c401c44614100d15500b4200b04510011840300301e080c90035030000781c00d81c0e1000c211604100d1403440d901c040880c07505000c2c1c001c0f151409803040c00381064034140d079050b46900c200128665144941c80c0e80050089a000444590140b110788400301c0810415241d50020a41211607007464088580e12500c00b80c0d8101140c0c0a0307000091011002d4521103901c070100d95060361180b032040c202404820300d03140e41c04031789500f00104a0390503004001d41a000e07032140b454a869400114541c1c5c0c604030380182030703102054000280d41c0c10550041c2c503641180320b003500c0e610810100181d540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 746600233 1250 746598983 746598989
    0x60e040b0708180618010204090c11010c050304201c080703021612031d041e0b04020f0a0f09051e030f010c0207050d11060301060521060a170106080106 67
    0x11030821040107100d603045514a81c1100703050300c1d254042001e0364041c03030382c0c0d240090034003401d4402c0a40c0c45a00b43c0d003d4041d100030788040300f805e0124841c900001041d1003000588012550b0810599072130140c050350440e0b025540007071080d42c110707140440000e0560001281c070798214103052f8011f4003018601d1100715585124044807503a9031300381e0030020f150060b442d00484494030307134420402c2004001d803480855180d00d030400040c4a05503034003603040c180c002e443c8240c0007030a040d249004801110806d40c0d4200080310200010207210342071204a0007a5011a141040704003c00c00c1d03014003071f40520700400980d14010954544a00200308074203581c002c10405003180d141044450b20741131252460001900b0000c11041c000300c80002d507509058408d4600071a0400046c0c414400c404400050340c1401606c511380d41c0d65108001402a8000c50805100309440d0b03120b18108031034400c80781d0003584014645c2c82030500349594104131040481400c000c0d590b840343d0010760340300c082c003641c0c0013 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 746601483 1250 746600233 746600243
    0x90636110702100801080316030905060a0c12090302060915160506160212030f100b0c06040c0e060a05040507120501090902010e09010b03010b0a0c06141009020405031b010201060e04 80
    0x25000709205000241c00712120020a006a82005000e60b08000083d030343e0303180c1c000100d02c600c02c0660900b95928150394002581240000071801c2400340c1014810041030304c112031398030860f40d400c4030440300f520003800002d60041c07040114801c9031400d4401a2180708404007068640408181c86003412201c922040740c041c1c205008001c409183d41d400003800081328005030010040180c0b44091501c00180084892003440700800d002e00c014002d1040905040e1800550b9030541804651313590038201c1d42141e64041910004c01c0c55201e454085018402c0902000b01084c00c220422000c2e210080c018008c0000e1980d0703240340807415010f200e00900c074218001a20041c240001401800e00c040400c1c0981031510040060f07110310800c1340d046600d4400d001d61668040c00c0211030308501c2c9600500a181400480710010104a1003e03018401c0700e003100300030b03a81c0e0307100788416802503114881c6d16801164418405000e48104c6d80c001020500c0009001c50722420803071000001540c003a24 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 746602733 1250 746601483 746601487
    0x40b030d11010b0409080d020c011b0305011e1d0c1c09020a12030807031109060a02010506040510060e010c08040312050c0c061e0d0609020f1309063611 67
    0x101c00d00203119409285000703031014000a6010303101e8404a11801c1400c0c240ea03980043d0003200800203511074618680744000603504400d4072000140900b500380195802d01e0742c8403d0802c40f05c40810001c50850b00302080e06111030440c2e10b070341503800c580100610304070030041105909840c1e00000941040e52613580008230700d08980188908568640c0040410f41c9002020380e0200341c00090b0540d01044900c0c0104005000180d42c200e2402810489a001400410407025858042d00003e10604050303030200001e55800c01d01000032812481084081b03445580d00401d194410020320120700d0080341c0d0740349000d41e0b07660b400c8001180e591580c00010300100c0d000000301d00910242d440c0c541c00700c9103e07041c142114404280b0307284000765600911000a41e0b21000742c040d030441c1005003020a411500d5454221103000144c0c0541c51198031090106408614540c0520039041038030b05040e1060320500c0d900303000002107100700250154821984040d0101a00c06024018401d4a0704071165 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 746603983 1250 746602733 746602757
    0x207080606030a0f0210020c03100b120c01050318031b0a0308010f030506060f1809010516110d03050709030f060623010c23150f0117100209040b030d 66
    0x2034185a40980140e00c283c000700c2c440c1c00440c90b414001c80c11150100c0e40006d0b40045060140d161604812074150980520100c402d8810314582c030100341d001080d26520f0b0341c4034014440320780310440681c20a0109005102040d0b2102c9000e40c55400c0082c038400b00d91a00c68015840c3c0c10b580890009140300340d0007000140201a800640d1500500c08184480c032001c0c1181e86080d240c1c50000c014500a03120302c00c01c0c1c089030f41d4030317180218220500154980f4904003c0e000f140640001c455041d03465a0300141c07123443e54402e02c001c424400c02032014cc031400b04100012000b82101800d200c0c10029052400f0020491080c0e0450b1924450764000503c980f17002c000306841e1942003140100404442c0c484115641c00075100c0941552001c00448041c0d006400c0d5a07410501d038a00701d140b441256508407544100c00b230b6135401001d00380d48100780c50ba640d50340f807500c209054400c42440c1d04581c484807815003140e0045c0480c0c08000f480820030140700c00220340b40c8100c0f0a03e0100140ea040700030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 746605233 1250 746603983 746603999
    0xd150b0c0c060c0a0605070c0b0a050f0714040306051506040e010e0115050a0e041b0509120706020a0f0c030b09031c060803092101090f11040504022116060207 70
    0x4014000710940748541881c0c1c003400d81070340300c074400d8802910a035107500000b86024440c80401002c3c0303601040c0c10503d41409440200202000c8690040850031600454400b03401008100c890920800c000d502e49400c5a0340e000240c440038150650710341441124800c16600e00d80600040c1c05060040d13001d541c07601003145610041030341304095058081030900a07161f48a0120f4038020741a05007091203998000101f4001c04c1ea180308050400c1440c41c08240003a0711038020102c0c010111407507103a59058900e9079840d40070522070080580c1c80082042c000032600c1605504584c0204604081e003a92512003040c901c1c02181d0001480c1c000044031700085800d4111103042c20302c00d180c108032441c1480f03285079480c070500801c43e12555000e50842601c02449031100c0c038032340c40340d0300900000302c1c94503042c3d05040340080212412040000c00100c2e0b4103162044a00ca560024030b290444031070740945001c07003c40d00305d60035118028004401006580340481d60000d011541c020300b0302c0d6142000e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 746606483 1250 746605233 746605243
    0x210110d0b030f0a1b1a04030305030916090b15040f05010c05030c070e070f020d0906110c0d032a0b0403321c05010b0f1c15031104020705060c0d150b0c 67
    0x4464520014a0140640d0706c00600640701a00c0c1e00d41001c40d81c81e211a00e0540c41d003540986030343d050081c00380001c225808160000b000c200c800343c079038a06514000c0300c1c41415004a020304c40012142030010002c0c0d61040c00304c040400e00540580b0310341202c0e045e0650403d1140d130071a1a400c00b0760b8052012090f80406100e2507038104e807000e010b007200c641d000205041c0c0030b48507800c208100e0b080d82200e8050140403441000c0d9004118503207055107444c000d02010b011200701c801801d4031103440100c034660290f00c066101e5000d0f601c0c0e090f0b03035030f01c1d0780507900050b02c2200d02d2007411160103102002103006592440c41c400d500c4840740c44c1e100880d031940003030303003503110440d103075400c2c0001004501c6400054407881c02c02c0c00c08094030b0380d999410324500340c00000c0411030080d003041100710300c03001c0a507841029a07000e4841c03159088041e03801d000580c4926100140380d5805000000c5106441e0b0000e49000309442a000c1840a0b82031420903503545960408a4919400603c00101c0841080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 746607733 1250 746606483 746606489
    0x7060504082502010f0f110609160b1207053406110a2a080a2a050d0c050f01020c060f011403030a1815030207030210110d0b030f0a1b 59
    0x1419040400580e0000700000101c001c111700f801300c0d614030490440c1c01401c49101183d09030007280c00514016000707039942c1803520300000700c080345d41e00081a5900080100c80c0c2c0080510800055512011012606075000c00a880202da0701c8a40e081151041c8100e50425586c04030080c1c1460304080c18001c04030380e40001c001108038010441c004038990010a202e2621030308400c49600580030103920b40c010108403d00800f2101c00050741c0301655045110103910002d108240e416001010f00202c05901c4070703080c040c0440c1e10101d24091600e2207513901a0b810b5100308161040e06045180103800e80c3c000d501459900d404c40420418021001074020340140ba80070103010b02141e000e4040390b02c03131152522075020001c00390700c5948040011042100182040619506d8590450400400940042c00101c0040c010002511100074170781c054001440340c02280035103491040c5e00541300800d0b60301545a0580107604820403410420704c05c402400e0f0040c074079406800c008104000301800a50 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 746608983 1250 746607733 746607787
    0x30812060105211f080a060b0f12060714040b1c0e060a0209130b0913031112030a0c0e030d0e0a090515120102030f24031219020606030a060207080706050408 69
    0x14101700124000011001901c0741c100c1e8000410948942c0031514030f84040c3c42494201a06c2d5070b054180c904000f4040307101e011160f65289440d07030343c000300344030750700c504d2003640c040b071100b1b1010340c034024100840c615410520600000300350f4442c1c80010b041c0401110706a800d140c0c045070701d03d0942401e8002c400c1c1104100c0d0b04119920990740000c080c10000b9005480841c5500b0820007010301814030b16160561010407944905000120040350380c0c400c4883e4081c0740c2c24500400a0741f402148646407041004019001e541113910046031600c12002c034035030380260500c0c0005044050352007014041c0e00d803150036200c4c050240c401d00c0409154071203441e245070300c10000c0108c20071070048259000031040c151500e51050344408078a0141c0c4c000d0400340d050003485800300700141c0010041056800310060124a050600303000d80c0c5074003044440b1a00342e0414455000010b64960041202030300c540740140c01c1041607220102141c0045404507a02440003c035850401040700242000300249 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 746610233 1250 746608983 746609041
    0x131805010608071e0e1605070b1003060e06060a0e0a09150b03010c0206041a0c0f0307030c09060c0314031b031602060c030c090d14030a05040f0503030403081206010521 74
    0x202c80c4040c05e880000740100c899056101a84071546d100c4c00454800e203412078802d8290703007406080d0303101c0100ea0348800c4900e00d2900f080341910200210746d2034860400140341484440c5031514640c3c888800038221148150b031a03421400040405040a020395aa520000380a203031140906085911070407117442917500c00410080058000d01d502180c45040580000e456100c580c1909803e0040708100c4543c640b01100700468164964404100901107076984a103542d07441c0f0042d41c1141c1800c0001d070001e0307015042108000302c810b00441c1c100403c8001d103065080032200b1182160800c1d1880f000800443c0d0343c0d000260390411003a90440f424102540c80c1d414088410110b502c28803505601801012803400c0c14001403030440c801c0d00d84804e0075242e036000a641c0c010401e51190040c6d0f6450310045502042d43d080000645d02034a0344203500034074000d4803610000903004001c12240c10004108901d000da000310b008180c5400c0403c40d001242404c2c4200040e05208051901c01403007212 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 746611483 1250 746610233 746610239
    0x30601050a08120f1207030207062a051c0c0206040b07020606061603140d0609180201021905010b1f17160e06071b03150b131805010608071e 62
    0x8100007000c052042030307a80c2c1c0c410720340c0b120360554020050185d1111594000700300055806800074642940300d0b54003000030381d42d86002c0c07088803ca4200440041103003142c11244070380c09240103220f251030030307a190402030710020030031415211010000001a003040d804d00c010820704800a41e0480001d0000e490701c4e140820200c3d00a01400c8000e1010102c04242141454010700c00424046e0380d01560684d40c054082010b0007070302152250610a902d019401e082010702c000d80d581e01d00e50f0590180c01000d2010709070003518074180c4000c1d501550307101c004541907641d5403a10f030070f034258000910040519101e405040c2103101594407000d42510010010039a0889026072200030050402042c0308002c407011a1143c00340e20401450b5043d910152100450324021501c00c8038030a50380c020b00d00306500e00780b00540f400d0110702500024800100c6056502c6a0003440c1540700f43c40604401d1030054030f0305800c3d1a1039a22001d4142c118100500c00b048450b401c0301d1011070491030404106103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 746612733 1250 746611483 746611499
    0x31a06130e13170a0c15021902070b030103080913180213090c0b030a020d0e0307140d051204031b060b0301061403060a15030219090606030504050318030f030408060402030601050a 79
    0x10b0216010703803c0d8001003005038503015110035002c6613085103524041c9a00455101c0083d44000c42c1941c601d0700814111071160320000d50756041c0c65180882d1411030740f9642e160440ea070000d684e001d50201418011042c480b0304d40c41018007000051752031070f040d00014014060b0b00e001074685100c40728103100110b004209401e101508481c2a000c15a9895441d03000500080c0110100001110f080c010401245000000a0701070b0030b0046800b01c07010140d03c1c3c40c03165141c003c1c856000205900384a0444a094181034241e8854000d007007104100d0311000b44a16141c030741940403190180c0e20181c01c0c0b02420240306203c00303861100c1c0800b808961680000b903803048014120044241c640c804460203590510201d001954041c0102e4224154180c00210800c3c0714060f19020307600d403600c0081c143d4824000d9600554001001c0d524003e21809816001140340240b04d41511403800c100ea4a00c60030402031000b040b0781e002400340c50030540f040500f00f4006030703c424412100cfc080d041c01941c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 746613983 1250 746612733 746612753
    0x70f09051c0219150203070b0a0b130903090e07080f1b0d0506030a0f030503011e14060c0c06030c090915030c1012060e06120d050307031a06130e13 65
    0x141c044442180c1c00321180401100b980c0e06800c6522900c01013103148640e90740000140c9282840342c0311240980d0780c0d4480d284111002c043c1c00c1940040d40240c1009409050303032014039102e001e850725514554a41d168010041130585800000928038400c0201204004558541042505898107540500240b4940e914001c14644084e800c2c1d5440200b521503508010400c401c1d9400b09181300d0823145802c0c0070b021071300709100750300d4003400310702441081684180001c4182c804400d5044140c1854409000c075541020360a01030328401c942c02100141d446e01e000d5849018842100c2e81c0da001505c003400020309000d0040814240000d183d000c0541c1c0100342c41080c0300c025685800d0200074090102d60922a0300515443d05190040105040d40368110380c602c00c501c15102a2000c5441810481d07543c5900e0100713000062040c0045510103110360005405d08101d00000d00031542c1d441700060840c3d10080404801072010742e0100200b0408214183c1d0090b101c80314460025060380b24a800e05c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 746615233 1250 746613983 746614039
    0x3070b1c061410080402280906030303090b150a1206021209071514040e090312150109080a0f1103070b0f0403020f0a14010c14030a02010e070906060210090614070f0905 74
    0x7d9005030041049a5100e0300d001402011020410300c0126501e0030094020a081002031b6654122a000514150740400c801c5001c101c000c0c0ca4043c01078a000980151080840e03411900e841d000c1040283c800300c0700103207034084c6642d080500841880e203141c94032852618251941405400408905d04c000c6a4050740c08507484601c1c04402559220701d1300b030951003101d03000c502380344948007807000480860b401c03510201002e0b216505110380351200c1d03640d6800300080c007e10111401c1000030006c0ea60071100001204064102d0304500c3e150079824600390444070f6045440c2c01c01040400a600d0400385002c0c02c61804c1c0e4002035854200080c1d103801c00205a03129040c4000720b51a0020810246101c41c42c0107521010f6a03199045000001d000e00300c0c010260900d07201d11346002c030f00348030144240300840c1c034150005c0c0441c80a80c1500e102170440300b28240e5101d0f96405d0031000c5840c42102c2c1c1440b8040ca55142540c000f0120300141406000c0c0d0800d42c0100141304001041e54a08001c0800c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 746616483 1250 746615233 746615269
    0x31605090c07050f100e0111120402010c0c0f24090f0b07050a140619020a090e13050312100815152404140f03070b1c061410080402 58
    0x907921681c00d24a1901c101c030a00004c4901c2010131160501185030b0107040ca494026000b400f01e024061002c000901640444610075804d442c04180150b0203a00c41c2500c00e44984001d0045681e24075140c0e03810070041d801401c01d40b6030208041c2c0e01c08003551043e10084d901d800d040100da07040000c41002196280075050b200f080005483c1c0034444100400c03151990f015900700300102c40380d40e01c0703601c1d084140c2d49010001d203042c1180f00c1d01096030080d100c41852a60f901301d451440e10b40b90450000c00500401e40300007042045d4030100703030213200a1010011f00710342c004060400c6400005590a81d9100b8040394004520082d03030101c6408042c1e401c41c14110101700000d0000e0000f0f900e0280c203050003c020b004082c40010a104604c0192044944510302e07a001c41200e9801e01000710303601e81c08158035400816041c001d0814201c007a00c208100d458140c401040e11a921104036140ba80040c0c0a0700c0b055101019940360100c41001040c1892400300410b00303207507001c185545052204515 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 746617733 1250 746616483 746616487
    0x303080a02091f1b11150f07030c0201081807060e0f0a0306151703040522060603090209181002090111060f01090b09040f0308181b031605090c 63
    0x1400301035406481070040024945803010011030b251900300c1c5151981080820007072041d0105240d00c900100c50a80d400c0304188030080d030305108116140110b040840319550040c01b044140c0c00c00f41016110a912a40307030141c5010090001503d10300300285080c0f85010300d01000f618800012454000b226090300704441765000da040000c00344040c40c2c100c1500009008000828450150401a07444c02200c00764500d16850301ca40b0840d491140c1e000607869030040000704020306000700001c154000c8104150b001010780b0f60303940e06840c41988018006512030000405602c0c02c401c02c507800ca1040300c030076015440c0c084201c0e40c4a050120140c050b80c0c0e4085201400c41e4000d8103500303044010501506c00c50b14107490301ca0604c1001780225800145003801031003013400c042c800a0301031b0307402c40c02800d4203080319601101c40907001001603105030143c410400c015402001050f11660442800d42c407074140040a24bc0752840341c100c00703900d03005900da040140d034840b55511500304111103201a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 746618983 1250 746617733 746617741
    0x50307060c0903151b03020a1b020102070302150307020d0e0f090403050d06030804180e06010909080702060a021c09120b13050312011505090f01031a030d0302072a030308 75
    0x2e41c10060b15400036001ca100e00d82482401c903420b0780101c0744445c0344240d52281d60b000c08022000c0307026116600003c1400042c04183e030711402e540c1403203007510500c100d54926480368007180c0c4101c1030103050a03c1d2000401803201483e018454002908114030b8041807640c01c201c00034a003940d20300c108a001d515484003080034588a0800c9502e81c229401c424070a059592912140d5581320b846004900d11129205095410f05030062400002d108401041c3c40e0342400400d02c010200080101d4403514100001e10051300c0395005407521b0705013900508840608101090045007000340110100960000d0030f11a00b090308510351880da40243c8400607030381c1d0310140f244a000061202414602c00401c8200c000061045124140c1c1c41c0124204403001e101e007400e40e880d02408400130f90103002e00265803e154403d41c41420683c02144000c4820f03407901f400701e81041c508042000000c1e400003140b00c2881861000e05002c409842100b100d500040541d18810043c00e002c02020007940e5000b103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 746620233 1250 746618983 746618987
    0x7050f01051f0e07120e0a020909060403140a0918020a1b0c06050a02101503031b0308070305091c05030718030b07030b06120f0609070813030f050d051801060f03050307060c 76
    0x281d403c0c03c450042048010501b05d172003a581c901c07519089224400c50000240070010100c3c04c503003c2c99141d144c2460f81c54130039000c55102c0d000721548104108104c000050007115441c00e00194000441005035240c25403000103012010304040c091400112140c0b14000840b80121042250788928202c2d4a803010300341d0490414000b4800c0350502e50400e000283c003c2d410648080441c3c0c42900d500c80c2280e0344c0680511841c005041c00380102e158200000c0c50240030350086c907486400703c03040e261504e40c003540303115003031841d000e480000401c04410001c000f500302140e10541180041c42442c22859941c0301780d0185401021007007019100c038150b002c80d440f8002603d00c40c0140e0344040c242d51811b070844040c1c0310021110540301ba03000101142d0f5450040c10200d004100080f42c0e10450742c40f90b241079072891442111a0200074041204418035200d0307124141c080c89803401031031100170522a2041c00c0d15929000480c581820300000c0001920010488041550009010401481305401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 746621483 1250 746620233 746620247
    0x210050c2407020f06041a0c12040501050105090702030f09060f0903030307022401120f05030c0f0109060e0c010507060f0207081804061725050607050f01051f0e07 72
    0x6580e14101041d0008000701e584000c41c602c550b8403942201d010000a120090340c0d240b041d40c0250100844010107580003000c110200d51000020081901d86004000210f4000c441118242c550f13965600c0180b00a240c55450507400001030310040d41400900d00c5010010711900282c58412140055803050082d625000d60700b400c1002810340f03072a440c203e03030003039203c0740324008142d0350000008a06140d404000300b00e44c1601c4440152480140d410355500b0502e0840d0b07041541e180c401403004640a16040190074041401c1c00c00110b20082da80c0f074803105803006c24201e0f9103981c10513001810b10782d07400b60645801640002004c80d61691005100000744505030024016030400500f4041030312030a6800300c6240c0c800d83d42002903964840c424a10004660b444400c580c0046007001c2488115a07128100d10045074110070b200c6680f5000100315038004081184c207a0004200d440d0310000a00c20307981d014060302d00e8070441c0102c41025441c004414000c08200d6101c100c08200c0302c0b03203d601 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 746622733 1250 746621483 746621503
    0x20d050d0e0d020f0c2704050f0d0905190e0c031f0914060a080c040f0b0306010e011a0f160f0c030312060b0c0d050901020f10020a03180210050c 64
    0x3064410780106080e009444103004868641e2a2180c540001c100d0309000c80d0b540d01000e5044203058916217911401403d2006c050420f949912421181322894902481080c0b41803486031940750b041d5191070148000e159030240841078040140004021142c003000e10664807034800c5010320390304d5480848140c2c429888100c0c201c001c8004c400c0205c6c4849483d40482e180c030344080003180c0c4599407501085038500f03041c01000300e0b0360003540c0e500e01c4a003000d400c9643d540303495200c04510030b074640c008240743c01401d83c0500c1c04a0494001000314a400d02c82551342c0b540e541c07203400e28201c001e5402c0d42076031164003607d13500391403030b42004002d11030000000c14015622100f8240e01c941c0c0c03400c0082103490381da03404030201441c0920018200340d50030102d40c40116140054046401c035213006544079000341100c00c0c1940141900c07103600d940180991050080c0304000144c98800e0507200030200c1d090740c400f19002c80681c01e10100907a83d00344140e45805107071303c0c00554070601400c601d420515115 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 746623983 1250 746622733 746622761
    0x904031103070510111602092d0a11031323030a0e12030a09090b06090312030910090206031f050a0305011d0c0603011503060315020c0f070501020d050d 67
    0x11a0b140104900407030316046008210a043c030041c2855084840702c0c1c4030703010100121022000f10303040142400d803805a40701401c40e0051404803140f450480c40024104c183c00044044a0100304440d2068425440c3c04002225518214544149018000b0300407560151071240b08101ca0005010101941c180030cc06000035240c0314180500040c1442240001c07540c4603c84c20500c80500344000800d459058500b5500d400c0c40c50b250000343c01c014150425500e8101c001080352005645080042900030021140119520320f4911185030501c11207040350b4011904100030380300036940343d0341586c3d040313200d6a904213045048001441c0c0340c400603030310942d00009880400418401c041d0b000030701e140e1400d0b510703080c0c5010321850309071604074031050107038403800c2400140300540201c0340c0384d0035601d0181000075070140c81c1d403291281100e00c1e86041d0360a50300011500c0e60040203001e10300c01102e0123001014242c1c1071400107503d9445006141d41040f601103491580313907c540d0007400d40c000c088 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 746625233 1250 746623983 746623987
    0x3110102070602270301020c10150b03012c07050a030f0605150c0f06090d0c050c0928050124030b1809060708070c0602160b250216050904031103 64
    0x1400e0448039140600818035450f2444c0c012200c42801c06000301d130410710154018115605503000c00d50300800e610158045400c448030307408166050044001c501070034600603c112160340001c00c1992000c0300700940320340009203074288000aa000420780e05446010705020511020780d146420051005500c003a90041003880c40000516a40e0001c1120300385030300a4076160010000010343d200d005407541c5070603a02030200744c1282442031800407803c92007441074a40e4140070f5000100d010030140c401d101495140e0108003e01080355207000c81042d103400c420322240d07250507501d01595217400c450160302034010035080c031928401d610188020400070310300d841d19903003083c45000080048a11a0b498420711002c40c502074001d0303509520074001943c44080c01186651104060740040c0100340b42c2c00c0c80500b41c1c00c0054850342601d0320512128440042070042c0030001d0260010103102c600554101801510b40c075603444401d502500d01c00d030b4210220307843d43c0c681114641e80f04541440d083c000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 746626483 1250 746625233 746625247
    0x10509130f0209031005060a12020604030b0a0605041a010e040e01020c06010e0f0106021c051e0a020c0901050f0a030f02060f16030201150501080f07021617010507110a03110102070602 81
    0xc01d9010b40303c5000c0940c220790b200e603c41e03040001203c00c151100e03075102205040030040c000c02004003400c100c0c0f0103488079007003558983d6101483d20003a5203100405440e0740e414002c038103041c480c068070b22110840303081c00090003500291600303610031003180c0a9512402c4040403a02d0075011558610f26101c2201d541d981d641c400d14031101d0040e181480000034010001030303040d01c009602c44a0f82145520380395a05c1003244280c2e000e81c0b1111a02c4000f8002d07034901f030314041819019151235001500500080846e410410141c07400581103540301c0c052182c4444501d41341c509000095135440f41c0d134080840060300005003a8020700f00004c0c8201e80000d100000d09884c640e680350000e200f60024800d0b803030115400141000e00340a0140043d0b0768400094140e070740e81e0002e0350001036500585991850815540b058890250468060b100f0b5813458040182e80c24482c691344070b9618900040c1410b09140da85032242d0141d50040c0c100a00041e50306100c10b401c0d41120a050b070302203011940d03041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 746627733 1250 746626483 746626511
    0x90c10090302090603010902060406030b0f0d0308040b1810022d040305010b030c1f03091b030b0a0507091505121003140a0302030901110705100305060a0f05090601050913 75
    0x80c5400100e000b945000c0c00301e03189040500520b511540d008150600303260030240100c0c0200346681d100d40c3d00081600c0684610344418050b03c0049009640300122850941486400c40c2c402600ca040da0094158051005560115400483c1004440d02503900e8510031031481d841c420010490018140e24100040c4682807080104102d0344a54001d0040d01e00c3c0c5401c16448442c80903095410035112107105140f0f2042d0141411980d6050030001010b05441c0c81c0c00200341640161048510317103090b414020321010480050384551507002c240061726101000810304505813060144c1228072072a1160101d000d00140d0f01402d1051150b040baa03d81542050041840d80c4000c2c1d592403039004040c2e1034250003042d03c1601f150550021480c00180c880119510120744403881c2c0710b0702560402242d2580da01c41c5507000001156000b05143c10074070200400140c0786d500c050704814421740c04010640303407030460503400380e42400d0254882c075000001c0307211000300c1c1c0031050b551890a00c803104010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 746628983 1250 746627733 746627747
    0x80304060206091606170921030a0605030c030a020105071a10090b0319150609050f07091d040803130f120212040f1203050712020d1202120f090c10 65
    0x80f1203a00301d807403e12850264000c110400d00038900040c0951584030b00038281c2010080c1c0105200045410302a0100032100c07180c1c0690500d40d201050000a00540c10702c40d00820000d454100c3c00342c070400e0005000a991150800b000a06110f0f0203e2940d00b0b00ca445113a40301002c103407008107215807400d000003580c00c0b141402990501407400c0009a10b03810002255039030202600c001181550707042c1c96034030b14640484070003d11143c0b216000f0514031400c0c0981406140232207015401810800c0c005010740301c3c0340d007140c1d40020b29010b000c1c1c03101070000c142d55005500401c655a03640c592500760350391032045070030140100c50f4a250030320820841c000603062800196080e00da000c41c0512441c00c1900c21032164070460600090180070040b1803140f00b103101e0f40310381452864005160345901d0102144880240960000311841080035001501210003907841d403421840d111120503408000e04002c0e003041c1000200c600020000c40d007c009010381e0410050890440c0381100038020116 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 746630233 1250 746628983 746628991
    0x2151e04050d03151203210f06030b06090f130c030210081603021e0f092e021c08102d080d0206010b0d06120609021c240204080304060206 61
    0x703440c0819000c0000c1c0c0080039901580c00c00380e4103215000301c541b401c98800c41490944d00c0c1552059010300300c01240791050400801c00458040307a09459400e01040c1100c1c0108070701c2c0900c1e10701c8108031011206000c0d0a912800d03045105c071143c1c001e41010010001260002900403450440001a168024000c984a000e031010000000450020220140c0c010310110b1050205002044042c0e507251034080e0003010b405180c000d080840da0000140c200842c5105640101c080c142440481500304183e00d540c1c05c20341c00100b4407440150002c410b1490a04801401c00000c0000300d2180a00f00c02c0501c000c110104c07241c0280080102004910000c0c2240009a1072500b03400045003a80031a00c14180341c01500a0102686401c1105c15241e228218400e0503d0796201e02151010222203500407541c0515400501c1440d64410b000c01590740346030b03000c6100b00f490086000110340d001400f952039811034a0342d815480054296020f0701543e003080107203000101d00410b809500044d20f500c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 746631483 1250 746630233 746630237
    0xc030106050a1707080601032f010503312d080403020f04020d0c0801060f020a0c0b0309120c010c080a0902100e01030209030114100b1206040510120b040b06030304050102151e04050d 80
    0x654841950a895081c2780040140d001c0b078411700c0020f03003814041c0a032070302d2404c284000c000c030203184500500035840070290446400340501603d1001c0d42015545254100e0b19a01d1503d5948a036100c1c3c401901851200910400095200b0182501c950f0140d8502c01c0c1c221100f407100b050019405014002c00b40101340006c0c43d421014400c2500c0050b0001c600c1e40c001c4081c8283c070b8200000300040b640020a0b01c0700030301c03850201011b00703100d42c3c005266503c040340c0009440c42201d03c000b415814090490700c0441e05110720040075980740300e480c040200e694101080070030b203400010383c0a07001e040c0f040d540c90352801d00000d04109010304154071a40c10201c102042903280c116000480c000c3d01d2499900310000c1c0000b50031400c2c84d41c00345070044500381710007038415580c014118800d43d80b104110303612442c10080c8420001040c0c0e860307420000450145043ca424000001d655442840c4401092460040441c4500d100f100000050312002c1c0c0c10601186402e04029545c0c000313051490700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 746632733 1250 746631483 746631533
    0x16030c021914030c06120a0b06040b0a02100606020d1d0616060f020f0301120c0f080f07080c01020a020d11120f06130c0b070627050c030106050a170708060103 70
    0x80c26140c0402c4c1c00c12240001020281044464203004283c5200142480c00302655602c1518641d079665002d00024040c0d10000703030350713002d0351a0000d0414089000d0700e000c1908040c000d000442c0c010452000410072032504c01d1072001208103000540346940c12140d040400090f001300f03240801d20b005562280030389010702c400d20319003e03154101e200d03950340352115400030310043c000302ca0f079a0001c0c14110301a140c181d81083e00c507428904a2107082e0300c50403069109560b007000c0150248056401012500050300050050b0720001c2d45564034a00f0091050000b0f4001c0000c0068000200e24841d9000e0940d907400710003131541c166a61031100c0800b005106840000d02c0c405669194050300913401041e20003038602c2d1080107821608410310440d407040c1c82d07100302c124030070015101000c0a9900d90340300032415400c0c10600e0414001d4502c86020ba410010140030584403940c04104454413103291101c001000703c031a5050004a40140d091406035900000c180501001d1408402440a210780c1c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 746633983 1250 746632733 746632769
    0xa0902010315050a030b0901060308030a090201030b01022b0c15020301051e060904020304023c09010b03071b17091216061206090e0a060e06070516030c0219 69
    0x2884140c043c0c0f142c25440b58242d131052001594440e405c50f080b0342c0280011900d161a90303191603580c2c01c101c0d402c40c0d8541d5140360f8001551fa150080003102a0280054085200140005070104203107074404400850180005000107110f10029000c25810040d400031031440b4443d42c40281d802032042034807403587d0310f08604003e01000718540c0b00c0c0100034081442c1c4078480080c031010b9040140305a03071041e2070085d1004a01c00c3c1030740c5405031b003400b0718a00c58550036042440381108440b9500c00c2c010007400f0010f001d0f68400c601181d8101d0110300b42a09480c41c4100c01e040d003142a0540100030034a030045140031654900c000c1d080407141281c20782c1c04c5240b0580e80039503421044211000b101c0c02054100905402920180014514900d0105a4076140d4169000b40e45042c00030b004a0307480104014284085481102c800c440c2c004003402250805c48001016802085402075074001c032075440f282014000c4010743c26680c0c2c05003554440b400c0711000400040003d04c2411101421002c0c1d030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 746635233 1250 746633983 746634011
    0x9010905031c0305010806250e0d0c080d050c0601030b040f051006090b0f3d020c0316060903140a0624050405060d03030f020408010e0313120330050a09020103 70
    0xd079201d070420700000340c02c03084558010340d8442c50108c880014040250162145510380520f08122540030f40e8100608500d03040c1c046250a14002c50b0004200b01801855441c080c0400e095046035009800c10b1200d40b560300b4034016800b96a44000c003203200321b48180c454000c69401c01c2045071031a540811009850785d06210000e03c440384c3d0366038400f035581d200420001410b51030050351041d5015460281c0a00340c01c140c040e0301c00758840d0025034050301e21240145010040c1d407082250a24084095a1600b50042c0c804901400000c0ca41d12050550100d008000c01000e01e519403c408144070095803040d01c0c0e40d8480c0c02c404880030300c102c1c140f4081001e05250050902581010b022800032460030b846c00c40080c1004041e03444e10640030400014a4802401401c18a040c070001559403401613031144503116000c0d40c0f0100400031903440741004030750440f6902041801d01f4804140840c1c1c80307441c50803000703070fa81c2003c12010300e0103040c0304440c01158007161249200781c07030030440c8411440c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 746636483 1250 746635233 746635243
    0xe012303012c0c09013525120b010605160503030411131e090303110c0309011b0b040201031107050607050c1e0307060b0a0312031e0b03100209010905031c03050108 72
    0xc09002117071210750100d490109425240c1d42d81c03514038030a85800490450b0600707007610011040311810070316120740950484507141b0f1008100c5500450340c01c0c0d1080c0d860049d49501441000144403003c40e01c40801e402e849100b000c066402801e5030394a00e058a031414400c6000c400311409003643c910602070760b504920900449410650800710f040c04114074040c0a0090110100c041640301c2200e00381c85042c060240030b0002c40400959207071801107000420161512a40e03103120450700d1458404990104001a0820740a2070003180d00346603050f40010702c0c1b0650310300510f940318000410243c00c0d48003000d442c0e44e01000c415201c0f03181c05c170040b8401130760507411032007001d4004015030400510507905c22152150054480e030b003855038946400022074502503d40e0040780c0c80b892404594448840c440c040804030000400181d40c455000c603644040c0500244501e5600150403041680260104401003100500b260b080c10f21520000d81100509401007000c20308040000ca481d09006c21 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 746637733 1250 746636483 746636489
    0x10e090606040b061b060108012a05180d2307030c1e08070602030403020a121a06060c0712021003060b03040803070905090a150e012303012c0c0901 65
    0x9180340d8640d5401c01005151400d000c0da0300c400300300320407188443c5120110074001e01c0080a426598540062076007512155000d40c408041c240b5044a0064002c0083e207100c3d55913840d01035254550729041a9400c0724003c2503560100c094550340c410040d4214a48822546444140e104098030b40c00080c1c0c4ca00281c00014080b50640700e0500410704c081c1004144488480c03094490369a880708100c0c00c064440c0c00030740044c0c03c001820b000350b00f001a11400140302e4441241c22490442e01c503100c086280b01620391074022a00082210780c0d03200703015034490311840415150340682d60a5a070711000c00d20f0200724002c840c0c1c0880310aa041c080d100320700c2210314503842245140d545a9544c1000c0d0303c001c01400500119020200d101d880700244d15108040c03100001840c507040050307141c00c407a601d17481b0100000e80f48006000704107081c07038104000c1c0201566000600d03800b00c00203000d070909100b2041c0380c0704030175080c143c0b80301a201541000d00040007643c0304510707624140800300c0c00c240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 746638983 1250 746637733 746637751
    0x70210111005060609090412141e090414070c0b0603010b0609010c03020a120f200c0d0203010b030102030411100903050613061d1f180206070c0b0c06040b010e 70
    0x140c041c00c41c89a034000c030740e10a4006125901d40040c8000140c0e0515064505481c001c41c441081658950010800300c690400c09007542d007441902c0405034082406400f5007440e07104d020602c0141034445410240342c014104882c024189441030000f041a1075140060380c08842010118815003410302c130702c0b0900c0c40301078602443c0421040041da891018084114218451005030343d0100d0704044078400442c1060340d070025203c80c09c0000402480c0c40c0c4075a020380d40d14502c0d0a01c2c01c2e40c00051507132506001550116600d4003a4000030340102039801906402d540000208020415642d403a5664603400300c500340308501c014901161f400d0341e1400024074650100300440c90b46c440f0790030000d00e52032040001042039002881d820304d900c80c1020401e200c0f0b50081300f0042c0798980440065100000c100743c10481e4940c0d082c0d0480e907072a08440040d01918000941d001400150b0b14104003401c025003601d690303241e610603410340d944012035080e5128425100085850100d055030760303019401c15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 746640233 1250 746638983 746638993
    0xa030f06030b060f010c0803010b0306010806040b240403150b1504212111060114010203121008030f071a010b0d0e011b030204080c010c051c0306090f0207021011 71
    0xca0140204138034110400d90511100d00c80b8400000c040740700641c00391001c5486140c403400e102c03002509542028284a106900302000d282307064842c01007a421291100c4810100c4040780380d6111101e110341e0300080c0198600c406501100103240e0000e220092040e40c4034480c80140003005090b5005070f000700d4401c00e03217030590a411070b405085540c0f200c0340294031541c843d10710340c0340c110010080c80580328040780030840b61060041091003441d00501c0210500c61030400342400003902c0340701e1504195000c0c0c0780f040109803201c1849040001070840075048a60750700200c000d00079540c000e48801c0b19001900548141c401003900300c1c25040b91a15510b1a040200c4c00a0000c090301c042204030443d0365907803298232031287c1440044020540507450046c2e541e41004403040c1007485514240341403005440200001510016084c013580380164800030005c4000380040700903000c10b601c5101c8050070010341e483e6001d0107074014440f25100b00c2d1105100c2c41c0b4813105482d10f44103001900c840e5004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 746641483 1250 746640233 746640241
    0x50a030b01030605040c21020a050f0315030a2118030303020c0c060a210209031e12040905070807020706050a2313030507061706010f11010e030a030f06030b 69
    0x3a042501480c105050100c0d14580720800b003012642c0074010300740041c05c10016148032198804290690300f007d280700f98548090750b48090082e20841017114042980080040d100406c0e4100c0e01c40f000c10020280c034010f04c224200043d02c40d400000318100d0841c0c030310342c0001030ba02074100b011202c4400c54100c681545161403e4009401801c8100070502a03002d90200e95030303c1c84000c0500080f0b0340c55521540380c64206020f2a581000070103d03100d8030400c00e541c0e5541e8005040b0700c0741d142d14280d00b07290141440300ca07410002c1e2016940115040454007242d54a4160440e074807d403142e9948134400c0e52140c2d002c0365134034a1807080602080d0208040100d0f1881f8104001c4060341142490000113003890b440e40880e03018501d10703500b003201c100084c400c003c3d052003584010002d40c544012661029078034a4941c0d600509000e042c40001c580c0e00680340c0c042c072519500981141c0c001c00001a6100071a500c940c416140c0c0c00019140c440b61036103012141c800c04c0181c079081100d00302c0581da = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 746642733 1250 746641483 746641487
    0x20d17060909010f0e010f060914061207031203020a08090c0a0b0c010213030521120f06010c020301180c0b07081e1e0408060f01030f0204050402010e0a0909021f050a 73
    0x880a4070350010383d501c643d00064641824081e0702c06104e00c0c10000190011400c1400081394000d8001c010f2860900c0c3d01d4014800140d52956000b102c21074546420001c60901d40d498120306900040259101040d0480e040390160f02400c84d00e601c80c1c40d50300b501e42e280c1c00d00307545a010f04004558400f61203001800380480d480041c12044d0400000145480003141240e541c40d1040d034400c0f9642d41c860440603401121124000d610035a20316403280c100501602c1080c15140001d211690b04450000000c00581c411801070101c0f507000f4000300441c000344c45422100e420511002e986014810000041186201c001c031139405070026150341c20100038030300465060042010715101000c0c184a001c0c030000031a0f070501c401d204007842040d0740b05d192140d0542030090042072284540c920400420200d169060011103180e0f040380c000400359101d10041e10b65400e185032042e00200322150124507007506034040803d05000301c410b00e0402c601c0780400074110540c50f11883c0000c5081c001a08641c5c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 746643983 1250 746642733 746642749
    0x90201021507020c0406030c1e05010906110712080903011103071205270601140901140d151a1507080a0804030507060906020d050a090b0c0d0605090109020406020d1706 74
    0x21071a1050300e13410403005000030280c0d100e40c3c000b9100c40c4001c5d4000c0028519031441592109000c91800e02c070b40c0c0c42d00c1c00107070030b17824544501c0341403046034000311003280b00c02e01c00a005019a00340c9501b480305141003040454100b0104203010358607182580c03080304040380680f8072881c030a90710401801c40a03590400030b0200375060508102c84506103c00e002440790410440040c8000200003643c50b051131000740390307000c001c071074080d6140c02d0043c0024011401c161961240a9039070100c101714516000240034120440e0a4095103000440f4404240902200e070307403030b0002c480b440407100005290501d68419010000d004c000304014203480140180005548a4028140745090080a0f16814180c2d04001030403100c441d17000588040c120114450650800202d1000308641402503035840088080584411101c07040461800d10809041e001078014000c060041000303565581c1d0140003030b4000c2e0203140c0150160030f000841e018402d0406007410b120030503070740310517890390800d00c90300d0317 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 746645233 1250 746643983 746643991
    0xc010e040b0604080a0b16090905180f0c010f0203120103170408150f09060405060c0f040f080a020a1a040303050d091a060f0409051b010203070c08030304020406090902010215 77
    0x810380700c41961001d507603001c020f00010030900f0040d0443d40403a20780100142c000400740800300079000c1d850442a80c2c400c1d0200c054850310080050300d52a0342da0311205150b2800312650b0544110b80c1c10407072040000c02c440c2c0c99560280ca0700510718101c10b0050341c07030740580c0740c0944000145100400220704031442940d100081203143c1813800d030320b03040660304000030070301740003d2204403105020f0a100c2c04090541e2240120000d04020700b059510103446441c00b922111005401181c1441c6c0010000100d5004040d40d80d240c0d600c01d40d0302c0c94482e40310014000140e2180d403e0302d00014400750b444410225464402c20410300d01401d582c0c0940d5560000e10030490025034800b140000124100f440821031440745510085500d802020081090342c4417100303c0c02a4207080c07a680003c0d200096100e480180400d048410000700030040b07185008000000e0402050f170f24000031195030100046010740e000799400e1120540321310195055540d404070003030040e401203154201000c98880b001e504 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 746646483 1250 746645233 746645239
    0x1e0c0221160b0c070c14030a020d020f0d06150f08070909060b04020c030702040b03010b210a210305010902070f080a0311030703020a1827020d15051903050c010e 71
    0x414025031501071400d581221070383c1600d1400240032013800000c50003e4018080385299a414003060700100e134a81e80c00b548020b005002e045c00c035004550b5264000201c0e032502901051003152681428005046151700b094080301c011000843d0604007004d880c41a2003585000300703c82032912580c00010010030744280c0b0110354030056076400f9075440c002882051000700040d07481c2d5400e801000102c079256900c01348a07a141452400302501c1c3c8140003491740c0051000255142d0958440a0416240440c020300ba49010701c203820060390002c80115002c04d02d40e8041000d680c8540303803c0101e204642c2c014000440c0c424880380090900c038001d1003d1401c3d480c0210301600180e00180003a041078400b4400300c1d070040784502c012a8084414040d615a05520103605440c0c2121000203140b11030414400e030001d07902d4040001e000e501250400c0154040c1001ba01c1c61079107050103c0101802a030748903e41c291b90480400f04400031001c07c0d00d41003800380c83c01c4c0c030b401c000544885a400e188290 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 746647733 1250 746646483 746646517
    0xe0108060d031704240b041401051c020a0306020a02061008070f0b09040e0a0302010e010f050f0a1112040606030c08060907050907020c060313060b060a020606010c0c091e0c0221 78
    0x411444c070440b60041005d03080c940403078141c80c1130042005039103c13030708844803050001004000710341c0c8410703030641614111034948007402001d001207482c0507055040541000e000061000ca01940002c05a2191040011402c40305480b00c0c40c0039180c501e10310564080d40c0c241202808202050f0005060b0400001c200003100b0880d40d45150918078140d1082c2e000d40d40d10300d402404c104007801343c030700f5070a09080c0820181c0b03010320508808038009007142058690311890000380d8207c040880c0c1c40860034003d41c4c8100c3c6840d181c6200a002d070341c0812111410720b0600020703020070010f40c007401240d85a02074401d60381460306000314400000c14800451103101c00c514000d868220040d0301501071900c020108090606100060b251400e428a01540c41040b0b081501a0301040c041d4010401b480c280c0000c480b01e003002d06030708107160030101e1120720b822881e600c2e1001c280c0c2d07105603060140340d052241140300b81060341c450002e0741c0e403507c017880a15690302441c48104000c100082060b03080074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 746648983 1250 746647733 746647763
    0xf071e0e090a050103050c0102070f030605060d0c09050123280b07060501080d0f0203041202300606041b0c02060f0406122007300e0108060d031704 65
    0x560040341580d80958403540c0303c0041c0300340030781400705c10400c103001c0c00141085840c025241c4000c407410720028000c0340c2e07107001088031640c032529100c1c0c8054001100c1c880b2a81c40721802c400a06013841002000001c241080806900c1000c6000031190014803501c00340c00042180c01880a10b6010f8035610315019101140c500706600180c4030301406a000000e50390b04050920f4505816085401c0c184540c0c0c020749450300d40e000045405036450a540c11110111a1020451014468201e6000314840038095a103074100500502d01c4001140100c61944c1c0321902480120342c10381e0080f40b81e0350207092000c2c0346079000e104445141d5101801d800c0c07801f8031102d00344040340c2107a00304200158490701c1582d5200e940e8050aa2a144440e4042c8503258a0071031a11061040c00b40c0245410042d5816802425076069060040c02c0403142e82c209411040200500002c114001240072401e0100821a07904085507407090030395164035592600100e002c1141c4204038010011684d40441040203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 746650233 1250 746648983 746648989
    0x110a0306051f1d180f0706050a1701030803070f020307020d050a0507060302040b1c1506210b0319020324010501080a0c0e1302121008060f071e0e 64
    0x14811650400401c2890103900d0390301000c0c01c5254402d084000075083d415014140c0307800a0760704460f060424048032044c1440c0c8504044504100310308500402000044150300400184800c200c80e60b1000c0443c020142d000381c0c3c40d03000703010190050fa4140000b0314000d00426210008402320f0048a0602e000c0781e00041034201d41c00710484241d001018241e042203000c2214802a180508041d4102801c0c10071300012406540481c540c050034502d00c0d0701820195a1210404036000984680440d40720140a0a01e403100c283c1d00382a40394005d180806207065100382c6c0d540cc000100030705204041e06020145413400000280c0e814010080c0e0310641b0b40c1441d1002c0c0f220b8007038429080b80b941c034102c005020140020402403c0e18100140010701980c04124408083c2041340d013825100c42108170300000b40158088405100985814401040c03500d02c9400d08913a00701e0100d64150f5201450f0f071498007015a500d102045142044c0460480f40818100d0382a8141c079101134032020807000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 746651483 1250 746650233 746650241
    0xc1b0d0602030c04050f09040305070210110109050c090714040e1033030b030c01080406060f0b072a0e0402040f0501141003050c0d1137030b0d110a0306 67
    0x40261401c200050402c064180f9a011079000c3c9001c80b1008608d1419403000341040c41000c030000c0c4038400d1030304e02c201450f000c1c42ea02606130410700001c002c9000546801c0c0e03900e03500e4944042c46404048001000c603480f9240302c5c4000c0302d081c10a82d08041c90220041c100d0400604260b070100c14050b004500d100c1c0006031514004c211600004d2404002c0288021952420f45603004150902035004401d4400041902c2c203d40c080c80c048286a40c1e600f4010002c00c86074002c483c29111160300041d5412482001c1d001d030390b001d10031450000c1c0c4e2100001c1d804101c14181c1c441c0d00982c0000400840f14919a070950007030001e00041002d10070510b6110440d94260002070445402d41380048581c00d20f212105103081e01030034100700505040c0c014040381d000343c411030709485455004054500d0a02d0702500c800307102161400b04486d00000300200c018040c0000d40c401c0c4065004014103245c0709008031642610084c0c0843c41000090310769007800060a013006401040102d4008002100341c86 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 746652733 1250 746651483 746651491
    0x21603050301060e010804020a05010807140c01061a0a020601180b030307150f0c05030a0209011209081c05010e0c16151b050304170c1207081804020c1b0d060203 71
    0x80e8031035480d0705040740580b541680761031342c904100f0390704100310040c0c440c1c1d001201502e9003420000e82e0380e940c619045403010803500b102500400301198600c15010705400c480181d1312000706a0040c004020100f10144c0640b00035807005a0203640104400000c01960000c2c6a810001c00f05426007440c010030b01c0c42e84005011610070448500c0d40c00e401c4464460f4481030404000240b006020260300145240005405070400a034000fa2604070b070303030003840400c907200d40039030781486140010b061641064100b144126411500c401d106050001c06118850503070fa44240480c0054844000900042d0041400349800c604680030b180301042105030001d4141100c1140807a003488100340098881d2034800340d1005018051080c00300103500f00c0e00903030500000041300b45e258403200c10382502c0d00c0d02c80c10b24410114000928041809502802085020000b00c820840245600d082c00100d10408030046841d8102c84180480e10701c00080440040f50014446402c0001c2522004102d9000303403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 746653983 1250 746652733 746652737
    0xc060f0405030f0a090f05030f1002180a08010605270c0901120e0f010b040608031210031205031e0108031c0204090c0203070c0b0406050d111911010e0f1b04021603 72
    0x140d410001601186c0c2c1c5900903160540150081521401441da0fa44650003401078400e500800e4650a51020710a90301040030b004085044490b80e4108083c0200014081d136802140c1810b51a00543c60f5411051843c0c00240c2000742541c1d54100901840c0e040030300118102700308015400d10115190044e9050905080094114501081451400c46010400c0b6600a0382004810042101e021054450707000d40d6046032900c81c0d8030700e0340c0320f94071070002c1c1c0000b0002c0082e5103064007486d0307214000d1845422900d590030b10b10001d540c0200c0c0451824881d0502c580d00c10007100040b050703150341c40e0301c0c011aa654090b0800e41c035180020141c1d84c0c4980c0100040c0d002040341020312285500702001002e07a00520352819040510080662041404036000d035519944807087c0f21600e0001c8502c042c800b660a01d40404221200030402c241b1240c50f41c0f03456017400d840a44020000c2104010524000001c02c181d0440d50080354178000c1071015598055400e0000550800b0211450591107110b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 746655233 1250 746653983 746653997
    0xc050c040515091b0d020d020c060c041809020603130606050301060b13090b0325050301050106080a050f160c020315181e07181d100608030c060f0405030f0a 69
    0x42e0148200440003c2c030280401c2800700ca140720684a01c005c40b41000501400540c0d20700581b00b5501c040d1050b140c0d4041e0500c40c1d40f040040707403041c0f580a0420384004038500701c5a441c00700d800a05641441d00c0c06540060300304042210340d41c2820110350f0f00c0d4850203000c41c100d40d075800020708407202075010b003c803401c00040e9905101d00c0c611142e405002d48800411280e200c544c0400c0d80c0d4400070b12200c5450700c0c40c40b00c0380207030720166010100a00e4010000c0c000d03517031100c000802410302500c8481203107007010f003c68104038010340134610495046a0080c1e2700322411404841108034224141e826000340c540380c10580d040907500034070810107156164491302e1486261807810b0207942d0b40030450f006806110075014000f01c0c1d007030100c034000301850000c01511040380d401485000350300020869210116542401e011680e0001d003250304104201c860b0751204066200e1040d802c1500d80e45c0c11240004d200783d202c4100741508540640704627030510300c0c41142c0c80107540c05880d402e400304e100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 746656483 1250 746655233 746655271
    0xb070f020315060f04020c0a021002101b0e06071205130918110904050601090f02090613050906030102070f02060708071a0603061308120c0c240f160c050c0405 70
    0xa5100b41000b50304c1620114649007151080584509151000074400c08940200180b030a20811640342e0036540100300704059040414140100304244025401241d0b0304005440c0d14580344080d03600389074008040301b5090f400c1a404444540c095030725580540c4200b607001c9121b078000d20400c41c00032803007031010394881e280e400c0a0b242d00300000c3d12140325030100820400021808100c16046401d01d00001c81c5201c0403c810802a0045440c1217400c8040401c45058900721140f400080780d5040e1400320390742e145c40c07084c14240d21403140041d0a41c400ca03030800006007004c08c000e112040c02442214140300c4159a213540084002c0c0d0740c1c64601c41200144900c0c0e24040c400c0ca034000d41c0b00710000c501d02502e03948101d500d010781c0c3d83e000d413410801302c00282c1c030440c40d40c11242c00d0800002a00c049119840c158996004140324203001c49507031100050b07811a07152102e40c00341e41c04500c0d00b806603a00420868170706002903070803210f80c000e00350031821940781c84c05a9401078140001c610540c401c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 746657733 1250 746656483 746656489
    0x8040305090d081c090c0801050610050a0309062c1911040b0414040605010f120213060e0705071a0402061215060d060314060c0a030e0c0303070302030a0908030a090b070f02031506 79
    0x3195400c450481d9240c270050200c43d0707455a0078040c143d0003e040c59074841145a006600600510344044c3c055420700e80d1034450203d000340c800e030700f071110f030007010005000280000d0b544120b05c0320510043c00180c00280701164030f000c0c600d5603200700180040303100350103440424180c0304000e104410202c213003001e00003004100c0c000c80d8050007000f00744409682c90a0080e141c018644440030f80180060040340e0049081c60704400d01070710504580216505040c0402411a40040e00548420b50070100c0400700c101c1c0309401c64062a0001c02590400704940a241e6240304003410022a8184281c40080980c60b51b0300500f2954074480f8000510f10315608014600000c0c4d00241d90aa400c1103007045840d058420540c0c0c058606890005200f0f4038040c82c2c18680b1495080246e0f2610012075031700c0c10940c0c00002018a601c190351081045555503100550b00c3c0502089803010030b10f000f005101840c1908058800c5601400c2c1d0703030058041640100e4244407845080e0601860f100e420810241 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 746658983 1250 746657733 746657753
    0x12020703030f0e060a12180506060f010c020a050103021b0d0203071e0c0e1515190f14180619021605031e0a05030a03090b0708040305090d081c09 64
    0x802503052011201d4200400901e4a03caa020414280306d80560b082c4c1d40340003258400791116556603204122548a0f05200c0c7d40d402080b614a4461504184d0451040d403050740b03483c0045901911001e0581e08010042d0041e401c661704802c0c00c10b035000c401c2e49a0060070400203844040700d4007d1545c504d00c50620280d6600d44000c168000c8802920b241e001840341c09000c82220162458040d0940360801c0800e14000441e10840e0b008051110806018180b1350007000c50f10340c51180791074a901d800c0701c10f840749a44128280c0202e0b030000000204100c0d0390004202d003c4c0c610f00402e0350000503500003401e90f004000800c044130f01c8500402140f0307404100380e51202103100150300003d8680b030000380ea25000360580f2401c3d900481004510b5200411010310850b038484152a190400048014018014944180c0350a040d04000c904220b0040c450785016503059520b45141181420500c100b55264880860304100c2c200b04200300d100c2e00710196807032020025804962420207083ca61448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 746660233 1250 746658983 746659007
    0x2a1c03080c0f07030e120304031b050103050f0a0207031b0305180f0f190527010b09010f0f180b090103050105040204051f1b0305030121030e010c0f1202070303 70
    0x500720030010711045002c51001d5035801a4035190004064043d040819494211000c100d002ca100220340801000182c0b520100c8600d10071420f00304141d550001102030791400d480c2c03030b8600c3d02c8183c08181041c2058008042080c06410001d54489000e0750a27420081100310036400108082401000030780c880291f0066280120b86001101a041c0005a42800303a03083d828400c58180708810105181c076440070005001c02001c1c21001105000600d00c02c495940b040090200d8103400460b888074514259012003506a444621000c096001a51820704148520061009800280380c0307078030503018002c000d000c08150007034a54150000150a682040c2c001d207201d60b0060009000981300c80325050040c20f40058055039007450345500759200142c2d605913902c230f1440c100f015401d06030440700843c100d4072030303e0003401c0c0041090004030f079036580c002004001610303113441101650320407008000303424000d00d804030f2070344c0031661007090f4000003402038400341c0c00028081040c1078210001d4260 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 746661483 1250 746660233 746660251
    0xf0d0e0117010e060607060b06030406021312080301170f0105180c010c02030a08031815070f0302070506010611011e090b010803030103030e010305070c06020d060f0906082a1c0308 79
    0x140d41040ca0100c00040d000302132501688000c03440d02c06000d0301e60002140c112000d41100da4a0800303040c61400f0358485090303030f1002480081d000911f503903021f14000d5500d400000850444c0d0030540010425031401c1400e4140b4850b844814018600a05c600c42c05238000c9040d4018040c0d100701c48909040300e811000781070112034001e1801607240400d00003140c0e544a00303801e80d00c1c0c1e200d04000c0540140301540c0d045c5440303408644500d000619040502410349034440c40c400c40c015030003c0b01030340708480f001003183d04517000400c0070701d009415514a50000100108001c0c41c0e0182c2c0c10030034035144240c80c4019848841020034866560f2915000d400c800b03000d10314641c1940c9016110302c5205004504250390b0308000707105e60780f01c0c1e80d0b244200d0380d2001c0159520a117806580000d0585401000c44110000c4000280c4030000d01c201d1049440d601c0150003a4051812807903030054824190449800350501c11303290383d507110090107200c09145282040080024100104170030002011080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 746662733 1250 746661483 746661527
    0xc080124230f030a0f030c050105240405090c1e0a050f0109030b09072607091b0311090d08041a03060d0f0609230f120306010c050f0d0e01 61
    0x1030481d81444001826800580e8096101c00042d804245407002c0700001030944803e4140d05401c040d84942040d8650780941c000b40410b848103210010b88119810750391490081c468100c80103400c10340c00140e40500c19809480052000d0030104652804503070301c1c2c4e403859450204281040ca01b80680d2806090181c0b038030407207190064000303041d050351400058118065040044c142c0e01041200202826a450000075280ca0103010b1107100c1003039008400075405000000304003c11148168011020f42c8000a920000456815001040340303240c0146c482c14100010306403601c03800000702d00b16106000440e5120b140c0380c141a841110644000f02086080050015075680d1095096219030054010740c0308910074506407006000080000348a01403410116154044191035140f2000c00517003545c000d2a001c44800e5124030148409064241050000c5242d0703502c0398003809030030f9200307000312840c0708459101245040c180c00e40c0f400001721041158003407540d002c5a450104041c1e00000c0b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 746663983 1250 746662733 746662769
    0x509130b090f0a060801020f0d0e0606010906030f02041d04030f03050c0703030216050106230312040902090a0e040f061b021b06090a03050309040e06011a070c080124 73
    0x1c0c441c600c01904030840c05081070301207928078105900240060051800031582e45c60710309520340b480d4012041c1044141e00c0c2c03149005040340d01003400d506c07460301603482c8111181020429401481d40b682c501058650901c80810048021440e01e004a00e003001110f203289032500d0020440040050540f04040c188000d119a900e00a0142ca0a817649400c015840e4110b4040c9c40700502082d0001400c00c0d0701345503000840040728400c4201501c610341c04003101058460501d980e550107070302d000d040040304202c1088450020f501900704200300500c4548056034860003000c40fa1400d0340d042d40c0f510910003000c2d0030442d1503c00d84c01c00c6020700e02000814805654003944a040a8494018103400307082c001c030315903950304215a4444030040800d04540c1e141c0c10403036580c3d006610309a000d50720300340300c1159500d400184681218115250b03582003480303815500c4155000f02800b200e00e0340340c0400215030384400703000c0e4822402d10010780034080b92000341c030700c0c12217260355000d01d02034001a1914 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 746665233 1250 746663983 746663989
    0x402212a1303120e06030406050a050a020c0a110a1502011a0d0210080c04080106060221030f0411030a15090c05010e0604031e080c060403020c01090518091c0509130b 73
    0x100301101c0d00315400c00004449603c0c00e42d1030301400d40e41940d002800000300010400d660340118002c0e41d50450401859035400081ca0480c03148100314a031f9580400c0f032510008011358012100440d0140449550560ba01c50050304400801d00c00400f50351501c24007032840d01e1305405c4542c003180c1103440c80c01e001c2e0907070046180c04000d0b0780180204408600000c0720b501a40c0226030042101030700822140707a5514000351250144c0c2d048035010b000003500b507851101000c2c10b030f0b40594450403440001d82c40710344c0d6115900f00400c2d03c2d181c040c000c010300a00800c1951000c08040280c503600403981c80c2c05841d01c0c60040e20660041814468070401621a6032180d0060f076055030390000c288401c0f440407640c00e00d203120140030020010540050403064a440203c0c5060080c0d01c240c00f210101340005c0c00568240b07006004490b0400c408103215500410000041c6030414041001c0c1d41100010b045640241948080d4400118100094511150403ca80000d04000b0441010043c4e25440d0b000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 746666483 1250 746665233 746665267
    0x50a050f0a080703030c090b0c010606090504060b03220b0112050d0216061209060c09061e05030703020a03021303050c0126012601150905240402212a 66
    0x3c0901090742c0c4403080d130305543c0105003030005410221016901d0340940341c91140600300500601000989682c0005610b0405006000a564008a12600b503980f1650032409030104200510045001000f01502040c240c05110b8080d020301c040201203000c480c04e0803444c3c030841589440455102e062148076003004c082807030041d200c913881c1884075070640c290307070038041e02c801c140144c00c1c1407401000500c071940251024088510540350000644031082e030341d2040031102c070b0811010079001c00c00106481e02c26401040a6240e900f00107050951a01c080c12805a49030801c0781c0c01d61100411241c550707003261840c411a58919091814695400c80c640d40c0359106210b201d61000d64245001c2040f44040300c0718048044200c020801c0c560300c0c0521400ca000d50f0b2140c2c0d500d0324a0140420940c00d40c9a00400800c940140f803190100100703000d0200035808079040c480d10031401824841d50303510000d00c103809507404d40d002590780d80207819481c4c03c8003a20345454240e40c0080000110303540410074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 746667733 1250 746666483 746666497
    0x310050102190615030206030a0b030c06071709060c010f0e01050a0c091701110c010b10080609070819060e06040501080109020d08071b090903020601061d04050c090904050a050f0a08 80
    0x8501504c45040325403140d4081d400003503100501108101da1903e8030340c03003160030500c2101255030011001c4203001c81c03441030100181c24460034502c10700ca01003980008283e84140a01000d15008c10036a110382110b801042c654421a1221207032842050309001e184d4214601c46020400a10340c10f0300542285020311840e0300c20f01034a1045100c8200a41c0805050001d0b0240c4903918070800c0c07a480d00800c1058140e622925444140c6101c803482084918814140030f807080e42c481d1540c0c00142c8546d5030051052403105030340d04201d44041b42d02e025000c000c01c8840040b00090034841e0402c0107036401600400d8a5070700d490241e1016a8410358126a881c0c2c000300200d941d4021410071801004031142e0002c03148030b50700d4000604404541c030440300f0074040e500740c801e0340e602d841080f181c400200d2510110f0321400101042540790951007940c0040c1000101c030318158100002c125690421241612030340c02021040041c030105200c000224602c500c05420001e9140d61604000d0060300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 746668983 1250 746667733 746667743
    0x506030d080c1b1c080f010618051c030311160b100f030803060301230c0a09081912210203180f030a0923042c03031005010219 56
    0x20800d45502c50080340c1d41c0703106442e1007a01042540010341d50700c16413030410650071200100c4a110fa603220744040c60003407003010000d2a199282a100b00c41c161400161441210940b07030380018203a480e0f0b100391400100e450700f100b40002a03814050100d13520b83d084002404010003008c40504100d44104c105241d118084862a4076643c1a003003409801341c0008a40009801001c418405190050362151604400a00c200c060040305042c2d00c1405c00c2d0a0181d03600301030082003182e43c105014001c1055980b40064181d944c421246260600542002c0f4814414200c02800c1c031620309840780b40711b105401c050001300440319010120054201501d05001e41c0070002c908a80d0103041000400c0009000316a0804120064030346c99034441184400450741800000607040e941a504544e4030740c800003104c50100d41031040c0400380100459a0f000016140c4076a1ba0f042d0150081298442751500210380341d181c1804640d0700c180c40741c3c01450641d4000c00d080c151808010700556100e503801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 746670233 1250 746668983 746668997
    0x80601060c0f0605010b12150f0f040f0213030201030b010212040603020f16110306070c050a08181903110d080910051c051e2a0403150218040506030d 66
    0x9400d242c2005064004000c00c40e5042a0000640d1140080603200100741040038150a40365041c0c44402c40c80d00d40482034029086441e60201441c140c41d0003062640050300200f41d0080194803841241d001c4102502e03040030f20f410500640d41c0c503104124441c107080c0010300c600c0324510041480c034002d51050300101034000645200c0320288500f9140b481040840c108030020a500c1e201c0034030070758200c559020f485203e00066800742300781e1012890b650008041c1c65401050785503902280d1010a806c4540c0d85e000040d4000d40d104d1075040b13941100782c80308000f602411490420b14007042c0d50311641c0f280d01014046000302e44014102c440e9180119a81040002c001d0815107081c002d444948055403102059002030000c0c51300514447c004c00d2480d40009081120401800e41d002c0c0d41c2c003100358010021403410900000203000710031900d4054181415503a17540c108200b10190300f01000140c001c41d08980b09107080842403d03401040f10184074914041020075507558418100f00304104407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 746671483 1250 746670233 746670257
    0x30c0e07080910230a1a04150311040e190c0801050f01120f060f0b2b1e052d21070201050d06031a01080d0c0b0c0c1b0f0a08060106 58
    0x8004440c4003402e000003010702d40c13845d04482d0030004100d0a0328148040006401c1c9102911305803141104250300c05900030b400508545070780b2040344140582c03503003041e40e075608030884800c01c0081d1040e61301301000410144c810b510b800410340c102c65218030090b0b0b06010501190519000790300c4c2c19141d0540308a0094020ba06060b900d4403070750100900032034070f81a07007068242119000030300e41440964200007020741c224041c0700c198440342d03041182e0384406070200001134040021641d81584920401203425042e44440341415282990300c5440040011810402140d440d0f090035070000c100090540103900744400c007100d800b02005c4000c05e90000910101310b81c0074609a0b0366084180004115160700c0c0c0c036000307101d00d41402c0030f481c07420b800c032000080420b400241070340c0002680c4c2c1c902c0898402c0f80c0d620220b980002d003c0307081241d0203001b04400e012040040c80c942e211011481c5103c1160107007401a103001caa81458014806020f051001d041c00060160454540346025804100f03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 746672733 1250 746671483 746671511
    0x5030406021c0f0c08010e01030b0c120109020912060603120c1207050c01090509100504051806041b080a020a0b1b0a0525030f0b0403020313030c0e07080910 69
    0x2c030380c40036881088044402c0403142580d6a0003581040000401006042000c100a4030701020920489443e001c1010040c400204074100c150703040310444030b1041c10b10f5011100284444401d03045622801d901054421642c54601c1d1a042c21041ca0409064503080c1600860780300c031388034502c00d9003900000403041c00c607000402031601c20a004420050301c894092400580300c1c042c03890340c01d0009000c42c401165510303104101601412102e800c40400c245000b0500001d0800100356049000c001c0103801340c051420b00039248154406e056074040181c40e1800c401c00c480c016004078115078070500001c0010707250000580195041c7d80142500c41c08410a448400c0c00480a500d2090107120f40e020200701c000115209a030001c0510040c1c940d0031501034503400161403001400000707a6050f0b13200407523040740046800034000d2044e2447e00d0400c00d1200505902d5a0045850800d02d0f1410015103140700d041c0307034221000d07240c050400d0804007a80c543c0c5800740c07484049659503031815800100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 746673983 1250 746672733 746672737
    0x1602060d0c170c1204030f05070f03030e16051005030901111b0d0201180807150e030d050a021204140309040c050405100c0206180409080315030d0e100503040602 71
    0x500400c000c0c41056000840100a070340c1c2e070011500c14400700408503c585007580c003559111500200491910f903541d07201152903c42d0442140c090081c1086100003081606145103011b41c0281c501040103141511201e290005102d90040c04c407005400501c01ca564102d4110705020b110b1030800c2d03e80d140c000383d02d4010031106a21601c0c0200000e031402c0d050b40b0b010f115407080d228060541e01e007001c40480c180d00740c136407188816140c0820f0321907180c00110f20300050045507000b00e00c081340d20402042c0f540308807005840700303116a40c0003203120008146207000341c0341c0c8406090030135410b10710440746000c2c007901f002d000280054000191051401030800958240010090007409000521000908a0313401400741034007920a580304100d8450251001e0300300c0d142d002d0441032500c4012541d44071700d41c000141c40350b070040d180c1d411100800d11716000b0711300030300e021482c0e6948031149804041c5008840004c1e4001e101d840c81c040304840d6154050320b01c800000c0d0821780d5803541c861400000038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 746675233 1250 746673983 746673997
    0x4030807050717070b181204060c261b01021204060b01020a08070b22020a0e0601030b0301110c06060a0f120204020910030606110312180f072d0308160206 68
    0x85000c02c4090601c0090005e040c018010312142d0a024001d8a071183d0312011210000c10380f80204110030006544a8803a4444c0315000381e203070f44640300850f44251400c8a0f824044d805594000c150261102404c0111003290300014008626044a14454030410b001c02000940031f6035482c0c119504076402400400e104540c0810711036034130b4a452a044148050544810081e510140e58600d100160340c84c16282d45500100326405e100d1608000c01007c041c0180307282d041540b20091340441c0e803006d008143e0a03800300c1e0840394a81c60f10001513460020000d1003d8401c420401c403c0004000c2280e028007900d46414442c0f03180c042900106002e8821a00600c0d041000d181942240300d0341503001c0015550b40c0d41e1a40006140480d40d1a0380f07020394284c42043c0000c030404101001d58061803101168840001c1d10100c400c24024182406a581c0c4800f402c2c810081941d950041040f103100700d504401c201c000705007800c50300c0b240254080d2140c010340075003174448907205540d40c0c0c500b03851807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 746676483 1250 746675233 746675273
    0x120a1d01020a1e0c1d27100501031205040b1213140c040509030a1710050a1805090706120507030b030d0c06150503150408041d011706040308070507 65
    0x101c3e00014460030381c0d140c0c1c806001d8030001070148001c40c000200d030503100e9005001d9007110200c1e071038240259020100710a0014103c6401a103030515210007840401d00001c008100007409614500341b0002c51680c00d4805070411408010920040e2003200c183d80c102c11403156100259039800c4140d0350041c003005400f03000c86040783c0d4569500000080c04545206003070f076060040da05d500a000750707203000c0d180c105c001046039000c040c0300c140c1ca084642a40066114158450a035560b40858050134107600210078500602c00d00714095000b5004060708503075100c2c01003081919103500204840e01c1d80c0760418032291690046444140700b900300002c10003008094880d4102c00c44c0700905900741c880b001721500c0707080010001d5240d8611b040b82c0700700e0758003501810240020b402d0300e0203803000090080380c0c01c4070103010101e88984068403000340001c0c041000000365041844025010a14580d61101c1e42d00620421001980c8654502d4105040d2700b031068440300070340740655035601d215407681c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 746677733 1250 746676483 746676503
    0x30612200301090c1211090a0b0a06020604020306070503150a09050106090b03040b07050f160b0f06030a11190905040f0303230613020d05130302120a1d01020a 70
    0x180804100305800104604542105200254041c1030903109580c60290064800960402111243c0c2040c162000c1c85142100040203100300041e000c007900340c3c1c1726000d9903902e9420f6034141c1060001c04000d424640001c0c019480c05500103a500ca100810300c20030003101001281402084000242804000502800e461a00d607002c03900106000d11401c40000c2d8408400a403074000b901c220782c01640c101c0040005131740d501c07000795056131080d06070051100b8200405c240403007103180300414480c0305086100d0181050401504031813400f5208521940061240c1c000080a01c0254000c1400540300c1005004024003011010500395004074107103801c110810041205d0700400101061003074808002006044502421084244080c0d0780511480310104060340350540044080002d02900036182c4600849948180d80d01600d4280301c10404203050310405406000c0300f0f001c0030034070341d00d81e0a202170746000920403500b0414111409516003025aa0b5901c244249409107400c004c00035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 746678983 1250 746677733 746677769
    0x13060e07080a11071a15060c01021206010f020d030b190603200405060412170a0c0203060601050306030a0b04060204080d111507090e06040b120a02010e0d020d03050304030306 77
    0x58401e1000b00d440b45182440e000d80040440001e1003500c010300e4100e001d03201c1e02406108401c812990142401c0c11401c50000144480d42c4c2c1c40340248600720300c00001580f01c0025015003440440040c000b68180480c1c4c42d41007424641c0082c6810b03407050746141c0810008481d43c045411030b090702c010250040c003101008034103d0341607004088582d1b40440c09150301850950350701e0072030046000f09644a8001c1101700002c0c9081414500d88a0150200f5403104041e080764816070341c000380b0036402040c030b00614042545028850247d01030700a0030080d2a51400f000042c0e111540410000c2c85a2100004203061001581c1136401030085d841c22074440c14038010000c0e0110b21058440142c034820b18080c1c3c4074409160081307900515054a038900441c5c2030000c803980c45000140500c1d08035a40e0b0304003c446540e19200a628114008040c0152374585c2c000103010700c113130300036003400350404030009001a100c203c00380a1041d0580b406607103c0d106c0e8036003100a00307d40d0f48413107007140031403181d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 746680233 1250 746678983 746678987
    0x1305060309031806070203150c0f0a0801030209072d020f0d090806250309020303070b040602040914040b0103080c07090501081621150f020d06031205031513060e07 72
    0x30006590100c8407009484030780410004d903440b5103030009415802a4082c040580030b044c4201d600800c403254010309280004040c00c1141e040b025400300040c100200400540c18144809a0026014500680c81040121070900b41e40e500f009107807000c0079208282c11901e40300f440f1a515915280c01590862109001c0007400c013150303401100500c1c0103910209070500100002c0d107504101c540d68804441c03400d002e09130b00401d0380c3c0f1021307601408104840d600003400a50204d1003540302d0741006071150304044030300c0c048440854003130603c084070b4410b001c0403407403003180d40d41183e52100070030ba1340d041070002c12401c1c001c49500030301c3e0050070306c1d0001c5581c01e004a400000318a0601c00c5070800760752004001c180340031207805800038031800411100880c00b00000c41202e083c0140010031816501c2c04688203d9202c80c0c290480155100d10074010003244040c2280004030b5031138640d0440c2000351011620070300c4040403a20a080300d1035800c80b4102e540d002030000b41001110328000340750002c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 746681483 1250 746680233 746680237
    0x80a2d0e031e0a2f091506030f090105070309030e13110c010204050405071e0f200f010b0a050901210609030503070807180302060c031303030c1401110f130506030903 73
    0x403c80d000b40021440c0c8904c10320000790104c9884540c885440c681c0884428000c541c03401818420b400000c007111407840352900070095019640d030141207a207919001040b02c1c2141d2000c2d002c0002c25040504920100781d0200a601c4181c60841e050a41104644a01c80091502145038042a000403800160b00c1c84103601410071514183d6080c09960f41e4100c003126040c80306141141c841c812840000001031164800302c0085415080000f0101c03081c03052013014400c4107000600c150301c82c01035410031440c02c0c042c2030303002c82d410f0354495141810040040c0712401d050081c00c80c5034044030003500b164070000c0c0b09580c042c0c0d00400304120b20b101c3c50500900e50b5100f1a0f840f804a46007001086101c1d1042103517060035400f00400358101401d40d420048070340c0c80b484000c207481c030083c0070008044440c0c944502c001c6120f0303164100f03040f07041e00d4403412490a2a42542d856458200102d14030494402126004030955000756500e04808210302d01c2558103030802a00010003004000380a040040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 746682733 1250 746681483 746681503
    0xc23070b0d0c05070236090d170c09100c08030411010810080601120f142a030d0e010309050115140a1a0a020a050307080a2d0e031e 58
    0x4002d001141c8030150a5559200d000f40c02908450070651503110b01c1540a01071901d0501010713500044000680c10480c01e000030350b0003001e180c01071252022040e07000a05210001042d0400b0101c80c40c20310b80030801c0e07010b240409070246000510310702d080c078401e40b40c004010350301488140d181d0405060010605009140320350104502e5000b01b5800402c9444450480d40600c000b410a607081941400904020382012203d00868414950005001540c440d0440301e80301c00418003420055084e68800754181001800209845d5034111641c502140d0065403a6103400c001c00b000f101240120028149118003801c25442c00580100c0810090515021251000082000003503104c040183e680600d04c00c03503843c0c0c6500118499001c0c0024050f0100b0941c0b0b00580b8100310071912110b0a69100712001c482c1c4502c001032181c0840e8100e104c00115414008021488a031041035590150821640f88401d102c04405070100d660f804202501c82c5044840200c0c0021100c1300785144e942060344 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 746683983 1250 746682733 746682757
    0xd05041802131404021b010506100f0e010e220506030c0301060612051b030906270307150204180204051503220f020904140114070c23070b 61
    0x10154100c2055034000e07110700b5401d40714481181d5161079600720102c441c1c2e403110340d0015001c1c8a07440c54180036040348032480c1c00c0c060011415103404c0040101000d02504140c1c20f0010b00c000ca402003d900c8965201081020700700580e40d5441240040c1c0303501030743d0b40c0c4603840008040318100d000d8101c0e000303030b4000c80c800e50441e07250140140806080c0c0b0f196000340400030303428043c080d040f285141c200d1504481500c0004018088000d072984040c0d20449000e04640d0111003403100c81040b034081140c50205031280500e0000042d041c42d0344a2280d0b180203086840700340a1041d405000e0f0303040750000c004010340700740b441818000080180d04940304007846000d6001c9520480b02a007011688541c6860030004504051800c44007040c0c108020140d80c6c142c0340b540c0312801601c502c059030f40514042c0c1c041c4032820101000d02c5080d9554030705040c41c6c144201c0700b400302341740e08692008400307070340103410362211000c1d060584150341b008401c6840511841c040022440c640d08024052041c8034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 746685233 1250 746683983 746684009
    0x150a1104030f020907031b120608030703091d0705090f030f061e090303100501120f060b03150d11060d0905121323010f0e040905030d0b0103110403020d140d0504 71
    0xc0c00d0240c04541c403030840e103120440e81102c540c1f21241b02d8034912140d80d6103a9400255181c8a1402500d5034022050840120340c000138184180c07408003220542154410401400d1441d124500804601030007082c00d0003442111482c1400f59020720403071024007031700421100319103010248004490f504e81001200f0b6140b040104085000220807030348100704031a00001000e217428011107481141c8c12800d54250b6503040754412441c0d03903000c2c01005040803582c042c1c407410801031044041d81c504045a200d02000840400096a5819401610641120529140e5069100c440040e03c0901402413840c081c40030031707195001010020300851040300306c031803500035161408186203c919065102002d42010303450b1015600c1640c800e840101b080c602094040700100c0814142c1c0d11070384049840c0d0b00082045810030140744204182c0c000c007440c0a0007141e00c104031516091066010290180c00440030030014803074011282050365405008a402c541c502c100018007a4026005041c0341140d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 746686483 1250 746685233 746685241
    0xc1207020a05060d0e100c3c0504080f03040f0608040221100203011d070903081c0b042a0203041a0a030902031f050f270c03100605040605040905150a1104030f0209 72
    0x40b050750451440f0310820594060448202032a00e07100d08c040d04001002000c2001007034180013884200b1006030828010b548036818001000c00d00e81c102d0300000200b207034032010480580c0d80c3ca5003074100c800315150368210142c05203550340d040105807907150154074000800000d0502c0800488000900c44450200654441d043c00702d800000903c0050441035050003101403016120707041d5010020070005c005480c501800c00302c0c040d100e50303003078803e40e03c1c20b9007a00c104110425144080c02c1d840500c0510b00c0c003800c12009c0081c1c80c01c0241680c001d8400400c20f4100c03e40a40c4c48000700343d0300141180c48160301d1b00c40b80c20407114001c1001c1c0d41d044c01c05021422946280910901400b0f080d00400002c0307c4450504000111800b40c07a03400b4031800040c0c40080c4c0782480b200845036102c5402140c0b5a04000501c800c1da02d26912481c081d03031411032890049100406d5000390340c451903103444099100d4032100d80c0a000d10b0001c0110003080001d0001c201f01030f4600020701d280c42554240400c0da1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 746687733 1250 746686483 746686517
    0x1021201180c0909020c150408071403030903040b0f040b040b0403060e011103180124061707050a180306180618030905010f02030c01110c1207020a05060d0e100c 71
    0x1482c40000425001003041c040081c41e90003605820601c44200c07a1b8000244d45911403507081584c00ba910708400080b00800d025198400b0148c80000320021407850400740c510907501e205a10865001ca40d01045194080342c194084900038102100302e151039980b10001e1403c2a40036100c11030329186401d031380800c60401030081c1d4031151903110196055130340c1c0903074500407070001e442080103655030388400101113a182e212034401c58500d15070315105242491805025410342400340c0080e02c040100f0084680e5200049542d014181c0c603100c0c859403090f80d00358181c0d500c0d580008160380e05200c1191000a0085024030240f801250184042d105201c0b4030b00c0304041000e00580090714140c82030140b03500440342e00e10039181c148100c0b0300c0e007120500c400342150008011042184d10003d11104807801c2002400c2c1400481c01c407003441c002607580010307000c10507480740034060103010425215811031a800b283c1c90140540c10344060f038403102941d800a0621040c10004502c02e0a41500810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 746688983 1250 746687733 746687741
    0xa05030f0301050a0f0f05040f0b03010504051b0102010e120703050c0703031d3a05060c0a171e07032c010528240e04021c320102120118 60
    0x18400305441212506040901c00600295552809a4ae40b0741e83c0038030003a10244070300d510440c000d5028000b80c48903c0d64015080d801005001d045a0501040ca0400b8202003000d007468070030250ba0aa58641030301d41604c542c0200d03202112a030080000c00402e250f084030b1502c0202c6c503488000142c0a03209400c219104a200804800381e2454890b907101048000266610b01d60700418445640c900c1596420320b01070041715240d101b560081548903101d90010104041e45d0b144444002d210301d0311140350503140718030340d030750360642542c42e004100300724000d07440a5810007402000000c42d136420701c1030f40d42850f4440800130296180c80005807580d1300284201c21000070101c00110410100440c01d40680441e2000c0406440385804a4880c1c0c588074035030318010700b09014400c506107814010490301c0c031110b0840e54900040f603102d2000050002d401c0382c1d1285401e1043c91941c018508000d81c02c0105458078200d15840000d0549882014001c0d0780d040300d46040d01d100000c081c2100341400c2da = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 746690233 1250 746688983 746688989
    0x80609060f2404060b161401020304020117040303090206030f15040b0102030912120c060103110301020f0904051b0c0709060909030c120c060516021006080705120a05030f0301050a0f 80
    0x398a90052186641c0c41c2c1c500b004000d55000380049a5a41c4881d0000f0450303000a640405080303000a03060104112280d004d40940c00000085085180980001e03051800405002d40104007450000f01007602a9000700c01e401c0d00540300a4903854800f041c0107015005880000d0480780e03510303001a043ca007a01072022054010381c0a9410410804c00b8001179081d0009462000d0140320303440000701b040d4402030705100340c002005201e1035145061408500400c1e0319118040d034010069403005020120440da2400c02c16500020140d407003200c000044c10f501c040c2480301da200043c80744580345002075214155090a0410000c03d9510000101141d0b41e03100300801240b020070003000858246c00520612012a0504040d500308617682c0703404440e012a05061540b5403003452008407541001409001c04002d40200001070030700c00101e40d1603000c0d1040c1c0344030348100f81e540c1c68172542c2480525901d6501c6402c0b00c0e02e401c0c00b10041d000c160024011107028813610720340040c405070005060022 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 746691483 1250 746690233 746690251
    0x201080a09020a090911031213083912060702010c0203031003081318051b0c0c13270201111506101e020a0b1e13020406050307080609060f 61
    0x20980c44e1103001c4003d05050481580c540342401c810340b003d1789080c01060303c2030b448042c100da50383d409110030900c1c00c4503c1d04520080d0b803007000c10140b4040040d6812582441032440f046166035101c040781005104043c640790888040700741c1c4081104001005800303008590020f00c240200c110b02282d6130b000848280356003004098081000c1603c500c014154000307231010038004d40b034940c14a141700c0055103182203081a5143c1c10010420300040c0700ca1076140805001c14684442071f0091307a50b440140d6021413140c10500360603c030059156210320a41c06a40031804000044501001c024008151099001c03034580c100194503a2800300d4640b14840c241c0c103072031140c2d4840c0d138203200d0000e040c614030000340700108003c1c10f10b481d03804c00c6404c1d1303801d800c0e80200304803040c83c90300800252024201c2d035590f0b140c2074803140d010303114207030b0742070b444901082d0038403c100e440e000150240c01b9651140e0307007500403d800414010800718013a0300c2984a0011034600d03445501c040f00f5140c00407036503821 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 746692733 1250 746691483 746691499
    0x3120f1e0411030f0d11060f01031109090c150d06060806060304030c05190b0601030b100e010c020a030b0403050c12070c0314011d0705010908030309060723160201080a0902 76
    0xb40440303400c03028100701608688070341e0900c2e0321061030f16403d01440e10201d450b4030351899010108014043e440700c1d055403000309551455030381808030007890303881078420b08200b00092504d8074100910314104400030030259415201151442056220035444e02e0749070f003454800710701d450003009050702408010700924556617943e10211140c4003460030489041c0039200001261000c10b100c2c01043e0b600030300c190309150414000140440f10000811805201c0b210212500250480e504035000d40d400e08040408108510008050004540004000d20010000d00c002e05910002509600f20a0700458169400031141c01109000e00d039401000c00f42d102c242070002a00c030b2503003111580c84000c00891061030390384000347d914032040400021030340001401c00c0355603806a0034000602d030b080051440c40c01e20043c0252a41c4000701a0b4050101310104a540780e4406a0030806051054540e5a12004017403601c45d4520008d55040c3d0015540b403003c202d0039800361041d20725596008111318 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 746693983 1250 746692733 746692741
    0xf0f0b03060f1005090702030d0207030503070314060303030c0c0c0a0b0703090f0305030d0f0b030706031a0a031e03050d02030106080406051e042411090907020313140d020303120f1e 80
    0x418005c002c081a0031404244400103402c1c038170340094025103200ea1103030b640b249000b00d8000d003204c519502141c000d0000d40144242c03a1004801c03282c2006ca190069030b501d130350f265a034500d070100d210055074105a035800000381c033303810040280070910301c290348800030140d6907628450841c0c5070740400b4107190070411103186011940d070302040d0020b8600c04086041c0610034002800d00d01941d000402003a203031141100701241e40c906900d1401d4080300c000480ba4150341314100340104100c02d1208131610350f5802410325001d20160b41c0c8400541c04250350b41c1da103402006001490550382116600d04100c0499482080744911303030780d200b04103a80302c5139a60319034407220383e507851114645030b40300343e04a00300c000c40810303004000c90710542c6400240c0d00c0c0ca1180900c00e802200810b541c00b103400034820742c040c246020403520202d0340b10300100282e0241c0100090501c00103150025854070000a81018425286007414070810702c0348040070b0142c0d10400c0c94420103e1040a14004403181c0b0001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 746695233 1250 746693983 746693989
    0x12270504020d0f1b140a080a0b0109051002032203051005040309050310061401050a081f0e011205070609060c0213060f0605030411030d090302130f0f0b03060f1005 72
    0x60b141019404501040c00311000f007400c0101da4039510207880c141070080340e0380c0d1402d81051000c030242c2c908a40b041d1400e02c801d00c009002090140082031003d85403102c603e0182e2242c041480035201c018209540b4801c02103000e503136944400450380444003c0300250203802d050340d52110440c0e8022000d061308018504031140184801071003241440182c44d0040b071251001c200394107840d000c400000403103d0400c040c510684c1103032002c0c2d0381044000c119549502d54009042e0342c01000c010780c0010220705031341c078020003030601d50006926182c9100001508030f50145c0c4400d903a030702440c10350702d4458880343d040342d200e00c481c041c034404075042c090800010300780b40c2468840c0e0080500c0000340d10307442c1c04084842118560000d0000f070b00200910043c4050003200c28509003040f802401242c00e030b044040d1040c0340a22000e03200c1c0c0007003110791541d10030540101d4881000d0440421002104044010085c4580110a40a48140d01c00036200711260000c1c6405203500249541c9018686420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 746696483 1250 746695233 746695237
    0x1050304080a0327061505030c210604030e011b230f06070203040e09010612080307051614070803090d0206071407121a06010c080c15041227050402 65
    0x142000c250303640d0140f25138483ca228441400011151a80688141c282070820039600018841640c80d03507046401c20140d5000034510614010a5840b001d0030200c910303102d40104a903006050060240c18100400c043c1d00134095441d000c8240c0b6501410000c0300d01c01c8080060f1401d0040c4640442c0c501480c032082c10000c0340b00c4505018085a00d819505024541060350940c0d504025a001240c140709089030744500781da126921100030843c2500c7c0410207401c60310402e5002d070500d140000031411142c4600200c0300840403a10928030000c0540ca421440c02c403801d801030016004140d4003040d40c42c0c000c030440e29082030051800524504540800030640e0040c0360803501460021144c100540342401700c2d2005182104413041c1803225410508810910a0003076003100300280100a1107a07044450b03201c0480d04032210b1030f00c42d0680180d19203020340b02005003600481407801c010070840410b071800c0c807840141e903480448122205502207a03135070001041054031400501405582010340c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 746697733 1250 746696483 746696497
    0x5240f0f0913230919050102090f060708071106070602130806160804021002011506030b03070506040e24030712050f010c050a08070215090f0d05180609040e010509030403110604050105030408 84
    0xa0b00c01582114141505d1650740381c03421116039401044d404001e10b0301c0214040824020740d00d291070700105a0364400030f031090810040c040300c07258512280e6501d909040c1d683c0540d1020f001c41d40d5100c070034160001c0040620403550719215513800662204102c2d0801c805402c1d171a2104456a111503081014450705101c580003190342c0c1e0f54100c15418000b08408000709080d481c0020305401c0314091605210103600304074020034081200f0003850220203402039101c09a85034003410800780210104888403a21009503051190f03000c080340c41480d542001038903900c200e045515003907038555120300381d608c5401c0000119005101400b80980140701c803960240d03107032040d01c5c04030342100c440204250094a441a0a0f40024109000050100184001c2c4905814040c1c140a0403514519040800028150003500301240741c42503901c0d580c016040e003002c24402400b40d841d10040c1305a60b500113202c2640c000c3e1100c40817800504003001180d040e00d0b01a0364140c519074954441042c40e0b0f020007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 746698983 1250 746697733 746697751
    0x140a02071a182b140616020d08012301021f020409050a06061e0309020a0e0a0509070e060607030504090903031407090501080406272003010605240f0f091323 69
    0x840601c00714a090182c10304c06c01d01c02101d4240078038551002868403180c0c82c511000e00440c80c0060012602c9101401e480200d4220364216028847c1e0040381420030400e01c4c454600021030f01001c0c01081a0094020703684421410480c50340c40c040c1007010340d550351003424082104c55512414042c140c0241c1805282c880c01c01142c41d0159502103102c020682d40200d41403992a800d1203a80c100d5400340d9600114114020140e25051000c5002384507030107003000d40304000000d82c0c001010700480c1a20000d1680d10802c011440b06800d0190140510340308460001c0d030840000750313a403405111521f003079400694551146a032980e031160700030f00120003240702d090200c14411010580103c0318804192045000e102c0c42d2291080c10340e842d048980542d84280d041c0082441540c4491642070b81c5400414012004c40c020040900700c548034201c0420454240020942000c240440c014010404142ca1440d2100408801d400c00c8985850301d8182442201c045495400184520550060b52072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 746700233 1250 746698983 746699003
    0x41401060f14010311030a1d060a0b0411090307170a170c0d091206050c19030c030c0e0d060f0204051009080d0f080a050402030f150603010605060703140a02071a182b 73
    0x201151454880100d030b07001d00840e1a403040b442c4be0b00b0240900781402240c50b20f440c6c2440e0000c2c001039201c0a00e40144c0ca15600448a0404280340800014200c2604058914140446441101e610b41d01c1140a44524450a5484051588a09205001c507007440e0461000d44106907a84005040082e0100d00c0101c07090005400102e020004c0b60141c8074143c4000480d9001e00001800751403038000c019060149101c016985074980d940079080700c503070020001619074030b0004040000d0180d0380140703800155280d90205d03440d400104d488140e030540412200c08814040c8200d030103100c0c40c40c01800007058030b408207031403200c1c40d0441c68001d8030090542c0d51a807403c0380d106160003400540b00d098402ca0000303118407400c2c00c1c03140790013030003050f02d88503c1d0218940f0082c0181c00c00c255410683d410004060000b40c1c0700b4844280681401e0b004001c401c014905500d24541148103411540303130117203e040c038091a00c46010410400c2c1da1400c02000c0025111400144228920588074074080d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 746701483 1250 746700233 746700281
    0x30c0a02070923090609030d020d020d05090a0515010b1602010201090210050d060b073825020106030213090213050a02040321090509041401060f14010311030a 70
    0x8140110324420100300c0c18a80191001250a66106001340400a0580003c020320075404000710446007114183c00e00540e40f00d0781d0355a80f100902c200304080c42c03528540010703c4544c5ea404280001814040e50480314000240030035200e80c80c5080c0710b00f10b00018108402f0181c13004401c160030840380140000070303084803186c0110b040300000820301e00005900003500080d285803841030401810040450900b41201503842c440840e0304030301d4414030001120680300e285101250380404d04d00388448072221a04100034000e0120000101c0580c2c809212038011600070301c144a14411a50010f204100d10b10310010128014489040182e81103401ca4008039074075421400b80a00885003c00010790f501c1c80c6040c1429044003000c86059030340308102d2101e80607a41b00c4003150580c3c0003124242020f840317a141080003001c0700005403015500b070081c00140407400e41806011500021540382e0b940c08503c0044040751100e240c81018403000b0710114a58646551168088100011020300c01c0c142e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 746702733 1250 746701483 746701499
    0x411060d05100612060f1226120108060402010f031109040e0a0b0f010f0308090d0609150b10051206010509120c040b12030304030c17070501050609060312030c0a0207 73
    0x60700b240c40403a01d00590504000b01948002c04982403086801c0400000781051994a0b1040c2c881c4101e40025132544000b00502619064906640c89002d440c4c0c0701c04440d903c2c01c0d8289400c25000402400304a2000040f07100c00424401d00c1641d050396000c03500e68266100f68001d103408a00c800c000f0401b40403000d225162842180c9801407503200916807130359103151003a00410014246d01b2410381c07490040000300702800e641401e49600054282d240c001c140c0c0850040040d1100250400d4107020080d030901a1380c41103008a2150b5480178480a142d9000703100c10410165400c0c400500100010b6201d1213103810341c075810580501d0501e142c15904030010b9010a040c0140042540200e03154040a260902c80c00e88030030005c0d102d030320f80080c58641c003e81b0b9000060002e024041c9415001c0e0411400111440d0511144082c0d00d84500b802e05116000b0f02c0d080f5405401a40503c001c5099482e000486a03134441d045c0b041c03503145544c0c108000c50f80d034000b445c2031410751080c00b0010074201c2d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 746703983 1250 746702733 746702741
    0xb0f0a020d11070c0b0f031303050d060b0d06050a12030e0406050a0f060e0301090804060305100317180306151012050414060612033112050d02060f0411060d 69
    0x48503160300b0b2901c40f801818840c0b5400102e5203e42c00b2a01c0820109015011080036645d219140403030012421943c0e05007a00c0a1051203203d406c4186000b0011a6003610440540006065800c0821016458005006502e0118010084403010b24881100000d220707110b40c040039040038101040b0959118007050302c010294120903d440c98910007840070a0348031100998080040f8020722000305251243d4459116501400c41016216000a0a0080100c465500456014100304060302801c0a1403856802c03440c400c2c1000c0382c020398486118a0001100b50141a01d41e50700d8040703140e214100070303100c0c0c0380c51240000c4c443d9002c02412502c610f48a03082c0306a000315030851000408100c02420880000c24180c4150050004500b00c0040001034810003c02c0c8480321421821280701c800f43c09242480b6001003840142c0013040c0c04410080b0105018030038403c5411a41c001d01042c1d0329500c003103d650000759048400100407800d141d410030b5036100040c001d180b9115a004040c8265 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 746705233 1250 746703983 746704001
    0x20406020d02160614400e040215030601020a0803041a0c0a02060a0f09050106031b060c0807021e040c1806050f0313021503130c0f030b0f0a020d 64
    0x540c0114501400035601801541180c02400d0403050041c0c2c02c28001420310074202c03007030701c079490f0010522a42c1181c070180c9401c00c0a0f2020240740c0c04d2203100440c0c1c6c0c1443c0400d05404d0b45007002a600183c10301d440358225000340d50080c10b219285101c40c01c03e250640005000e107046101d41424040071507001c000a40c010380c041e038241200070384004d0307400111000c044c0040600c00020003c4600340d40c3d020621a40210500c840030602c12000c200da4000740a030f0f040094850b519000d400020010701500b0aa509400600e44081c0e2a5035400240e603040c601c42c0000c1c2c01c906003006030704010b141c28500c2600d02140d80c0d82d0243d1444007107001c074040b1998008481d02180c21040095038246042899000a055510b0140d2410091210041c01800302503c0e0440b01c00c403c0c90030404554404402c1d6030303400d80110b42c0a480e490301400b407040050350304600f959031640400000c10130019125481d07056a4000700b0702c0340b154441c00d103144c0c0d0780c0e4802400d000e0390360350074010b116685032240141810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 746706483 1250 746705233 746705237
    0x2030f0a301a060703030b1210020c10020316030f06090e03090306090c0d0f0212060c0a0e030106030305070201081302150c060f0412051c0f020a030b03010e121309020406 75
    0x354045000030101150100350340b903000225034201a44495881c0070032150180c2e071502d4045907030f1084c20f011802c00e01803800c0510b40f034001d07460388020150055014001c0544e0100071036015034040e035001ca04921080c4d0381015181e0380303a003245007418000e8000143c044544070f4001059a0340c0c0d55504102c4d10b9903513104119810028914049180c00c001c2150030048072350140c003400d80e0700d0300001e07405001c1000003081c040c400c280e110259584e000c40021082000401d4030842d10300894121655804400d0010206040c2881d102107401c0501c00d400c20b03030f581904e409180c01050f800658203ca0000c040b81c03c2c0074070840f0000d00607211031000c812a00c00845406841c2c4040c20442030800c03100030401340406104004210224070300080441c06c09a02c3d003002070b81c0d2949020079800c101a0550b00e910141d042015412410340c0d103034010511443e0b1a80d0821080c1100000c00d8203888094660400603805200001c485640c503e00070082201580c0100c1e4109546007140f005980040c3c0c080c0c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 746707733 1250 746706483 746706557
    0x50307090e0c04062117030f011a04081e030904090507061b080702100203300a0e070e0c2206090e040510050717040c0312020c0102030f0a 61
    0x181c00408100c01d500c000c000300c805101d040d08041101d00c0c1e1411400099403d5040060380c9070030700c160107508500500800118941e68a4040b200c4c903240c190a100c1c0c40402c0c0504446140c1040226094034251294600039180d8101001175510309400c42c0e40e002a000c0c00100300b44621551140328000c1d125203d4000741558510b4243c003e41610b00f2030f0800259203410400d0300d800140808201c0d21056411207102d2015111814200c1c0303580190608814410b8000d0031000112042c15131816862000c5d84410b0b04540d41d0240e44416100c0c000c103e098a80d1103107005002d51040b54041c154056500310742c2038141010840e42c101c10142074481060004500b04040c020a648490a8005001d05110641c031604043c1d03152680c4040d514800d500c2140d485c008960024030409020608007c070441e0740400e4285401c00c0a86e00601740300c12030b8440d66020321131612a001250500110740140c01550404c0c4040f4080725440d030005015000300f01140c151848440da00c51b02c14044001c94007a040707 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 746708983 1250 746707733 746707751
    0x120106091a01021f2d110f0d0c0203130915121505070c021008090c040b030703030e0a03210f0507081b0f0d050c0c0d0c03020d080405030709 62
    0x25088841c510750152007007407082410406a41c000402c0300d0785194101100030b420005484140090408401004081c0030104041c0311a40c000344c0340321181c2e210044200030080d0f4100f4840079510410004280c1904144541400c0248070b6100041800d014015030746040c1c2410410501c40e440b03504040e11240c1d84001380c040803803144e40c90201401820221029080345900e51000c82c211100107450030640750301c0001e010701d00c00c5854624650b4080d14154007500400b00140080c80c0071a035805c0c0500c11007990030000c0c6854001e490b0b0312100900681071007810750314100c650a10047e4456042507801c4000000910003211803840c2d5000000301f888800c0c05190001c0081004521220030090b084c4051800310300e43c00210361004c030745115107035950803104041c030f41040c100742e00c143c040b0300a0000c080507150304030f4020000d0626001c00c0e1036134111003d042240f401070700703603015041e1600d40c803043c8018240501d2207a06c40c1d008070307601400c0551714400a49000129000341201d640c850f0409 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 746710233 1250 746708983 746708999
    0xc0438061314030c061c1517010f0504120309141b01080106020d1704050f0f0105061801120f230d03140f04030f030207021309050c01050304080a0c02010e120106 71
    0x42e1034142d40480241900304040d2001900a0103065544007030a0650100c4011110855128100d28080b900d007200c1c0055030b84100710344440c1540302003075942d400c2040010603000984107840c41203a01122003440c0d00b008074002c6000707100384a001c594018900c000e07002900c0080190401010b0021801110540c0070400100001c0c0706134041e0040d58061800e02030781d542c10030040300201e2440c1485030525039940c1480e6203849070112420310302c1c1c0030361088411808410b401c090720401d030036151901e030000c0c043e500d072523141001d11486a4080300c0c41c820400103441d03a0200e00350f40d80a0029a40d01440d080c0c031040d440c46040c1c241c0041340d842600e503008642d8150080d040507086c8a0800761a9103001c41d005080c81c1c4000740300508121044d80d0302501940640c3c181c441045d00904064283c0420154880040540d20410b85140c843c95014451641c41001141c0c807036548070100398245899808151100040040e0803814809402d28070703032060700d80ba81e83d0211481c1c01c000104141e03280484ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 746711483 1250 746710233 746710259
    0x6061806050d080d0c1202072a06080a090c08060108060f13030c020f12030f041a03010312050f0904020f031503071d0c040512030703020c04380613 65
    0x2541c012504490b404011940910650349410350030000401c1c0c14108a8040f1102d0402529000882c0e01c0415507005000c0c0c4038251326811281d54401c2d104001040810500c80e185c00d11031003002642800010b1b800044642004c0112482010f0602c0b0f1036403140a01c60808000b604081d0312544050204104440c2e80800240c100010a54a0f0745040c025100240781910f1810040c2c012101c044031510207803103a42142981070b02c5030b410380751143c0d2891f1003820554090720590254404d9020344903510b461080489040300c0d4008000068002141c0081e1900c1d001400600e500764002c1c094908076484130300040555090440c00d070359581c609814100404101c07038a4030750013035004ea9418400410071032240901000460a081503580e10794040182030f204580250390021300594100d03400000000140100c140300e5001c1d502d03600c4180040c401110a28400703102001d81e41c0d03c040082451100840b00d10354422150543c111400c0004941a0380c00000042003d14107001d0401c2807401d0010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 746712733 1250 746711483 746711489
    0x52d0d0507060f0e18060d03181517010605040e04060207150b1306060f1107080a030824060f0f210610030504050c06090d0507180c020d0f050a020a06061806 69
    0x5a845e10b501544c0000b020f00c000003c203114042c0c0000c844c3c0c001818001c040c0340c008000b40b20b00240c00551203040070500040d4150400f000b0502210b264012040b40c01c1e02176040c0c4081e079840038281303807802c004a100400003900640c0d6203542040b140f00850402800c050400c0c2c29000c003c26990360f03040a1048061904980980462414000b44101c1d540160120000501880d00d240c43e80c404414480c20b160040e4040c808500c50880d6010030550040403a40c42403800c2c5800300d00300c005180d98621003540d906403050b0301c02010052000314045200240001803002c50201d801c0c8a9144a0200c82da4100c0c800f191503802420100300d41d62818600002c1c20f40c1031444c0c148507074203060b83c03050740d01c00060901500c60355010401d80c00c0b50700d440070000c41c0c0355001000c1b260450340e1410100702d05200c913007080a209080100e000d8009000041c3e6241e082455914003501e91018141165942c1060300f6120850260a02d030001180041c0120b0002d0042c0110101c5141c100700120402ca6280e0740c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 746713983 1250 746712733 746712739
    0x40f060e0a180b060c010b010e01050c06010b0310030b070201151a0306120109050d0c030e0114070f05030913020d0513170a0201091403030402040501052d0d0507060f0e 74
    0x80c00151403621070122180444440540b038074003034482030326030034050016011100c1d000080031803003049021054002d54006034003a2100e01003880010011902c0340302e601070300c0e40c065010030010840c0021480c0110382c03000c02c0040030340e061512a95903814000c015210240140c0d1a0049101d40c00140e000a400074141900044254170042d00f40c02d84c3c81c00018025480790034003413846c0340c840b6001c0d000680c201c1d6008040e210740070740403840034001c0e40082d5815000102d414a14140d6540104d1002c0d000c1d04501084a0034004542e4494000050b0f560303045425000a000d0b0070074603154120024003241c030542002d61281454000041142c00c000c040015a0b101e6018100210700c89031554240701096070701090361403404100580c090140c10300c00811038042c103500c41c2401503000c40a140600e100711000d0201e0390f6034804000100740100e090014035102d95510702442c4082c401c04030340080b00680303020301e07000c01a101d585c24902207610410202d04018080510380743d21100d110303113001c412 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 746715233 1250 746713983 746713997
    0x50405013312060e0609031315090e0402040b040e0c120606010e010f020c03070b07020f01030b030606012703050d1e05040603020a0201020d15170309060306010c080717040f06 77
    0x4032401150035000d4401c424501440302c180005100b50703504444403400e044011a603450600070601503a035480f00341c000c00c4a2480e680040303250300346580021600c2003181d490320a51424810380f4032000030060000ca0f4030035034468140866031160b0050200004030381000d410001000c0c024031044055070a070003221a0001420003026030780016419005900a00c1c1001907280701800691614114192942d41840340d41030000b01108014010840644242e6007910720385402c07801501a180c106443d00d070b054200c003002a5040d44100055401c01e0200385004402741061a865640c2140c25042a12940c00040d1100c400c182c00c81c52001c0c15440b43c0702c0d0540122a508002000c0d402640909030130980c000480c0003040d03200350180d4074040c042100c10880845496000540702c1468810900c1303401c4402600f907603100c808400d0750340910014150030700d5a5200001101c2e9070010620880308520300748841d40100c1c140d210b00501e4121030403621655542440c0c00010340114960012081241d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 746716483 1250 746715233 746715311
    0x170a020c0d031a0924220614061201030201210e03190804050705010c151509050603070605030619032f0d0320010e03070807020a1406030106050a1205040501 69
    0x203100ca04911200d9542d034900b10250307100c1c1c00100d28082010b005e01c410050006d800560401c00d902203811202840d001c2d07584401c045060154a0149070131041d0500e02080041001d54010410f80c41c810440444000341e00100400310b000b190346140d10758180e40c0c40403400d2150000900100751030f01c80c880c2400461841c050387c41c1c66890882d03004c2d041c1002405c003600400c01603014100280341028a00c1800f60344858074548011034158400c05140760b0400000c00c200341800300d0f01c8420381d400c5d607503514955942c440900072440c242d08141c09100c0fa0829000001c00c04008500885c1d005003694040d0310035100035a482c22807801c0a0451107115100b1100c00002d401c9030120001d5400103201404003040c5009644c01031511044142c00c50000003410070402403010002c02c0310358402c843d100f10303040c0c44a8030160006811500a5085102000103010300e600984c0a083c4605641ca0480710315140c00c1011016a5000d580403a12a0744030300c01d10082003900202c0440174140c98412082c2104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 746717733 1250 746716483 746716501
    0x11b170606040f151707050306310e0f0105180d0905010c110a1707030510020304050307020108041e08042111100203040518061c0201170a020c0d031a09 67
    0x8443c4036408a000b29940c91640c0d03540180c0c000c41d1080c45c40c0160400c50710b404070f4007a0066004a642c0c81c07080461245c0341c1580d041c40314040304058501e042c1144c18011a89401d8010200d41560790b0701440f03108051841d45100b40161403041d401e0190f48070340761000c044003e1a2414002d808002d201640d070b004e110690b444150640d480390020f00a0340c19052000200308400602d42100d11500b1039010b134041103040000e01c1c030048070721400441c0c10382c07454803217808203d000940b0018420b40040202101540c4110706a5405c2405090104491080c03190140001000030000701c8640001207010000d0010b025201101b04480750b801034110105551442c250040c0010070920510b003040c20010124401c20581e800b034040640341c0b0b00d0f40010888948061103080b1181807003016006d043c5d5800440d181c206184980c1d06031101140440350030b03414100030130001d00564445500740651403075244100038121400c03009440025a0303039800000d0050038103805100d980108103400034410081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 746718983 1250 746717733 746717759
    0xb030708071d030d030213061409060723010b010e03011505190509040609051c17250c0323031b090306240a0e070c05011b17060604 58
    0x1419880c0c508015452030a15006401042c0340240e010701c2225030f5102280c1c0c055004050044103007107003a0140b0756070b40c070845001d000401e064880010a201070002424004040c000c0700e8815240d0345a0142e60841ca0415616460980480c0d0380d1605011101560090b1100380340110540003440030310900e00c2c488542141a121311070044d440d640c0819030040010b039841340501030042c100d800d507007171900f4004050010380300d00b50341a014908181c1070480d9901c1d10016002031640721022046204d018482031040c00404c01030046462074113520402c60304440410000c001500e5080d07010741c40d42001481c0c00c0094801102a6070780810090032141c5e04000c0d40d5200820100560701c0d4444000000c125018210ba069003501c900070902118440ca06a140f88254000300450540f2100304100002008a4815201441a00004503070340d0b0748100440b01c0c8007070207a000420300e03102914889003a10716912401002554480c03c0c240c100380300780318103030704004226080b505013420903001007011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 746720233 1250 746718983 746718991
    0x417060a0c0f1b050c040c0302031902210703060b1c0e07080c060705160b03070e190e1f0f17030406050f0a1107031a090d0915120c180b030708 63
    0x40f01ca0311151400c12108110207001d4160242c02407140340c0c6a0040076029402c1a41d0700c200001c030019001701150514801d83d102c90028500000d1705180c1001c0301401064090f03c28400c060301c82c1000708600034000020120480000001602c04252050107400c5405c002d80c0c0f80c070190810b802c2004803000c000303200180003108541c4d0300d139580110700d05186010968010940e0203042c10400103003501c03d210141d481805162200c0c1d035501c10070f80c104000383d1245420201c004491355801e000d1808101702196218805030303200c10300c94080c09a181042e4081d9400000b925541c02400c0c442960400315881d8280002401141002c0c14180003421a00518420701d0404c0e90118240b9000c91052200e20341140364402903440300c43d2030781803090090075034008440d141760694000c6070b003901000401c51240c0002e42e0340c0750b40003400c02104000304440200b95108103c1880030411650368913206000000c082070b01c072042c1e80440243c503005040320035404140d502805008020f2078540010b4490340c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 746721483 1250 746720233 746720267
    0x3080a0302130e0702150906190c2d0f050301030f0b090a0c1d0f1006050c032107020f0a1509080403051f051501140d020417060a0c0f 59
    0x4809120101442d10185030b40098a2484944180288140c010603a10115003841000c04041d0b921100070550782c480550300c580e4805100300200d40d504070030703078071a080c0104c061900c00600112148a002683e00345403500c002860741c94007948200e030704113128800c01805424140e003158515160f40b60740070108180030708031903084000590031504c14000c45002a91085a0702481d6480b00c21030b58002c140e0300b070300782601015100410700c80c0c440748906510030300103001001903240c240f910498030780e0000c24414400c2c6c0300921005822146815101d014810410a040030740d240c601c0000340b0700203a04d0f98507800ca400c00040000414001a040c99050b5110900810042e08134075081905114a5101920901a03030b10700c942c000756075070703103216450300e94100900c825140c800b00600c0b04c80040714136034003041d5002c00c60981428030344013426905501c0e001c0103060983e03801c40141d1140c003d0b00d0560041d002b1000b081403449143c814601d03102d0083c03920b2440075841c440c01400307194248000c81c0d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 746722733 1250 746721483 746721487
    0x201060e060409142a012109030e040608030309070b0901050a0804021804080c0d110318130203040f030f0207152313050103060b030402030c090406110f0304021903080a0302 76
    0xd0005460014000002c000d00b111700484003206031040c03070240a901240303050760f9100100d05540c0300d100104080c1c0300c0c1a0724040d200a4140543c40244480e580880c02c0c8120b04e01f809119590340e00c100c00040004001955880c83c00717240c0c507410100f040e00460803103501404002020b9a0000c00e039242c1c0d013410308241509480750b000040d070790a10340c0c040080d41240e14003000100600e40014110300c40402c01141c00868000d007050300c0f040e03072481e9000e07425402808290700c0041c4c0030800400c0210040d1161070f8165044940c8001c1e603004a6051740c804100e10111070805500c20515404c00700340b840038180b064100031000c04ca5800302c110303507400c1145004038002a000341c0c030142c240112400e01010303560501c11050105440703d600c03a140c046450a00d0000340031203d442240d100d158000c0c0603000e414560320070031a01310350141040d115a030395011f00c0c400c100b1800d001010740c2e4401d04819610380c9014410040007000783c0c00c0c1c001801011000800c002101d01007520201c2444d810050303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 746723983 1250 746722733 746722751
    0xc070c03022101020a050a02010e070e0c090f0301020403140624040207060f09060501050307291c18020f10020604021512041401051b0406050f0d051e01060201060e0604 74
    0x1040c10009903081c00043c1d44006245002550414000c0c031040303100d9002844550800c80310142c45003014810840d0740803c001c00100b240c441ca000502d02c03c2e8000300400507248603280441d00f2600190021078480c00c1400c2000021030b03003003112070b91010351036400180c520100b000c41ca021110901b5214000d40d004210340082150035000510207010380d12082011035018200000074040a1041c203000340950320002c1900c100401d440c0110001c40f2800a078440b1650610001d1980050b144120340b881806144020861034000c40c0c0516071602d958428200d403a00400410326452510b8034810141c1c1c8080440d10380e000302d8001e40c0190100c17a103150121204058140602c0f0703180001040c1d00b02d607800c00c0200054280d104070182c20070381c0200300c40d80e80c40e0170280c0141800342c0c0c41d05507060103201c100240c5210398014040344a41d0f1100b18140382102d100b81c800d0b0341d021303503525644038984d805003543c11300d001d82040c1c0106a94070080c8244c51a11065400203000a08441c1c041c9440d0b401d2a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 746725233 1250 746723983 746724019
    0x3050a0c0f08070f02090108011a0d03050415050315040b1e06160b041202010231030816140303010b040b030c07021c030e271b0a0f03050c070c0302 65
    0x40c040150444070143d559111480e02c84e03030600360702c4c000701d00c40d0800e0000802c402c181445005100040058450100c2c0391180c2000410035140d5021070400100f0040400c01c103034412090040c0c0f41e415103031281c0300e060440d500c0d00840c3ea080c00c00c4d40280e01d4080d4034140766640846900080c141e45120785010030110340441c0a91080b141c000d40c0c200340c0034007188104910821000d10070340c00740c8032a24265107403280c201d0a0b8480d0f00e82c181c044024104059512100105032560301100300014800c1c4c0f50350b25915003e80d600702d102c250700c02e402c2419440051100303613840004c800e0503010255141d5810407008050178080ca00039070360345600210014407050308640864100540085c00c0511401010755401107241d03510301c0c200c00140301d903101e4038070031304040b80128040350b20010064241a005803149403002001015031010143e0640600445c03081c90001300421031503039480c0380741e04644440140c01d55001501c106507009003005080045050100c01c001943c2c3e040300c01c0d80340400f1003008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 746726483 1250 746725233 746725253
    0x6030c0306010c060c1d0d020a05091806071115070f03110c0106080d12090c120609020a240e0603010510180b13050d15051305070e041e03050a0c 64
    0x2009008916040785e1608858003c0b02d0080354012000b904031110a01000b8031901c5100c030b65009401202104040c01180341460300c1c0b0340d22000602c1012741c1c51003030341c4407145407141c140c1d16034000c924400f40c420b010107424429154584244058a00fa03401d0040004010110f4540890201984d0300210480c007001c840c00c95004e4820300000703100c029107a059040d207404070304030884040b0300006044001201c0350700035000e81680050f00f0890a81c40c01c01242d81100305998101c80c02d40d0f032455440b0040c8e50b40c200403006000e169001060f03401d023048006211040000700314081c03050811460001360b41e50030440e070661b203059840412000032950292038141c038040421800040428001c20f550603000c01904000d01201030340508141c1c1c5006002d9220000003014101d4030845440d0b001129440c0c2046800040948103070250003002c0d11041e040c5000c9030400009117071a0700500003402440c0000d03032480d00e210301d46913105841994014050380300e0880030605001641c0461424021401c2d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 746727733 1250 746726483 746726507
    0x1205060d02030a06360602030403120f050603012415020a1e05190210030b03120403060f0b10021c1824030b06040b030c16050f120906030c030601 64
    0x1c00c86800a8642c0f504c0801784c103103103a03400d0340d501c254502c00c0c1600703420302e04111280000031005450303000307151a8840030b90f000034015002d2040c03000180c41c0400c0184901c904054400c2d90020b018104002058295010702400c0b05121000340c050126070160807450600f180c40c6110f1801c401100c035681030f42864868180030344998941603c00d106005c03c40c19252941e842a01035031000703543c502c44040c0901041c480690400c075198058108240a58458105a1001800c891101d80f603100d0010403a4025001110b00300d44035a14468051801c0c013906c500000111070301041602e800e44025039510340d00002c4441000400400785009000c0d259044120740402d024154894680044803016080e40001d001082c403040c00e05680385104e4407940d032807003d0003803c06182504d0200d01000307541010305130500500f010000c6020620000e51802c151a00c600041e02c003c00800c40801d04107120710b168141007220800407600c1550350701040765400b10600440300c0c1c403a1a003500403210741402d09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 746728983 1250 746727733 746727739
    0x6090e0309092e031106180907181211031b011d041104170d0504140112140103150e1c030b0d0c0f1a0f0307270303030c0f1205060d02 59
    0x446015002c4216034161800e4901401d07107440c844102d03200f40441441880025001e1078410100b80e82d09142238450550007016030719243c08a0030001703110300d00c2ca5115074042400c0c104000244001c00202c52005640b03164210003034901f0600346181030024035441d0401c00c0c104400a1004400706459414043c1440009801004000751100c241c00155005d40605012501509101c02010b4400628001e5003c1265100c0341018036010780744090040a60869060201d48554041c0c0700c041403145115807000e03600c1041c05945142080c080391013807490603921540c02c20010348034003c40050070540f028140c80000750b81c040d040004800130894142d40301d5010910004e45014050269800c81c15242a000190f554a580c1c440b007140360500170503c030041101c1804400b19880c00b0a001d10340c41491810800c02d00030075042207031000e031120202407030421181d000904c1415818421404880c1141c00c2c40314280549850250082201d20b0031010700a8035480004c4040d02e484e000c075030310f0a6000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 746730233 1250 746728983 746729041
    0x30c0f07030206181b0f040608030d0b010f110c0f040e100f061202030705120f0f010e060703020315130b0315040b0601090302060304080a091d0a06090e030909 70
    0x1501d0001e4032004160b40d4414104c00386058418a0400840d0840c000002e00c506803949003140c0040c001c405250040c1a41c0c041d695000000d0743d884d0510080001c58031402000034513a0340b02d000500750680c480340700d8042114401004d01c940900140e40d0b85960000c85141412050400014010f007a040108045034000c14a20701e00c11507041d0400010100141c4040c003816803680300222590482d918060742c5035000200c10003040c00e00011a01101e9100015a00b0f4100380000c02490204442034416040e0b40d00e50403507003041c906218036a040807113403030207520754240808901034001c5685500c03441003640110740c0480c072a0903030000c0308415018081c4e8240c10142b501c20300b000c00c0220f40540780c4684810004806621914099082d2a4002c0c482800d6480b60b454540c0d09403c1043c502060124100001c6540900c0070007240880d1182c0507008081c2c80c15003402d02c05c1d510641d203c0030b2190f087c4a10a2010030b00401030ba4034410007078604d5585a65002842134100b040c1c03000c0b01010041c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 746731483 1250 746730233 746730247
    0x1170109120f140c0312040f0609080408070b0306100f23040905060f030a0b040f0b0c04181e090213090605040201080c07120f0e0907050c100b0f0402030c0f 69
    0x2d0745641941e0140c40d2a91107420b1681c03a10760700d21075039410341e130b031030304100200c004200c0c2000c0c071541c01a010359003029a00005903500411114005425210380c500460100415403003000b055000c0d254610f00e41d4150305041c0c0c0854640381e406581c500038460001248030240d4032400046400c01100c410b000c403e82010041c000155115004003906541070a0004000d414150110b03007a201300034008155511494840c0010740b10003a0040783e82620400d50080400c0c001c41c1418080d04882030b206960350f24140d042861080c03050300102c02caa0519102c816418100210f144410400d00320208464800b4800949012841c0828078503040c5010081014041c030350b0f1007148900d200f80c80304495900e807511403980034024100d004101034040808200311a02c680e2a01509480508202c03910b1b07200a00010541d00c02114000e00003a80440c0703d04003508200402806401d5a0707100b0440b10a1510101e003442400341e4030035008a8002000c00c027241c502c0703030440f11160056a080364071480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 746732733 1250 746731483 746731487
    0x3071806090512070b0a1809090b1501080609180304170c040b01080c07021c02101814010512070219080c010f050c0304410609010608060117010912 65
    0x907441c09010302645804410b510105800141d0605a506640c0030905001030000c00b02c0e442210140c44030b13840805540c00043c031407160f01456801c14401d400440d010700c8c001c021092104211083d00d410448003405100c919210003003080d030400071000320983c81c0b208030101ca51852003241c0c08601502e00313258995804010204090350501e00440d4103000c100d00300401180ca4038010f43d05492909001c10050006280c01800012084600c00050001c85401e0300011444030001c22090b0100e4034500003c20000c030300351048800340005000e00c0b41002c81800008116000381d00316120452400c1c0045030b10b00d0b008000381143c1c1c8801c0700304202a5002071030200f80681040554003090341c00c4c402020f401205e2401050b1003405d6103550f5030f05654840d10f0f143d0400c0c08070a4820052103c507403400c1920003c92540d03030424041e180240000c000d410001900c1c0440080040e412a450000c1c00d1000a001003060340c11181c1e010f060342c1d000e0348041621401001c01c810000e06028180b07803243c000039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 746733983 1250 746732733 746732747
    0x304090c170a240b0d0b0102031c0f0608030c1c020118020d1704120224070f15020418050703060303020309060d09170c0607020106080a020603071806 66
    0x9400150248009035911105440d4800a180c03121801480d01001800402c080e511003590441000482011a01c215040501103d4982c00c1903803d408002000402c411180c01101030102081c8011490040107006111086040404c8401025100e08081900e0480d80c0c2140c00035220640a83e42c2c0d8000c5d0300341a07640d81d01c45849070300041041d00808103126006124004903468504a15440b80c061542001a0300342c04420441c0c0864604d0407562030050120701520150648640c07030400303400f40703004201c801c2c102d920780e100c02031040c03106070240880d40c502520019680201441e625105a19007105440390320070140c91040e1010a0008400080640c1f6100c40305800c0400c00c61600c81d1307501281078440501001d0090303403041095000d03a081c8280102400d070b0032a40c0000d8101d04c03503905e51600f0313840c0303208010b00b8503c041407a02c5181001d105082e0007a1560000304030f201e01e0f0440c115115449040080c5c0b0070f40f0702000068805004822500062901a24078103400d030b12440082c100d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 746735233 1250 746733983 746733989
    0x80115180503030409020a0921081b100e0f010902130b01050d09030c03030e0d021506040e0a050c0a06170c03130605091609020a050412050f03070305030106140f090906031e0304 78
    0x45036a2400a12708490000c0c800702200740d10700aa201c02c0441d00c4000c1158403e40d030240040c61054050003030040e0910000024020309000840c0c910b0348040c1d100d280c440d01444030700b9144d250422031401a50f402c503550154442e0842c01042040e15040180c5080c01114003034202c8034103100c0d00900b0198041c1041600b548603480401051380922030302c0c0c0c0e4030022001c0d09009a032007925050010b4040740d032882e600560007032021071201d0100c4001800d044981c0780440b03099019a010392068503004603000090007551804500e1541031540302080303120007502181050300000302240909150010070b40d84c09802500c180840d0034000e01c8959103180107841481c40152400c00400d0f100300a00844844001d1551107504050030407902044203203002c0c0085485110340e425040c0900018400f800c0e40a003e626215200e46c0760420103401c000c12180f90041c098410841e000f0032185d2441030300e00c00b00003a101c0b15600ea480c400820f1400346034500741107400c194a07050103241e910010040084e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 746736483 1250 746735233 746735237
    0x303031b09030b040f020a08030d06090b06090a0b13090905030d060e0702033412230f1e0f0c010b040204050102061603140f010312080115180503030409020a 69
    0x8001502000c64000c052400b004041d800500080750103d048030980600c80c90005003402d44503a65900e41610b143e03c64850049800d8841c02c0c10000706035280325544800000390303441272600e4108070000310031070361390301802002c201d0208070041c002c1002d07200e24025003410700007080160032a05000740c0c0da401840090054070f0400714042250b4015119072030140d5043d400450820b50180ca049011440b0301002c454081142011002000400c91015250302d004485200d080071400c0c500422420b21125500480035680a56008120120007119842881c1a84650312848000c4424074060700b40c1d813074054401e00100b0300800e08040c40004010145100303000b0049003a005003400168000c3e03104582c0584c0212001511304102901141c0d1a604286000035607402641e49180d800d0304190f581030f180c0d105500041c0704004292210044610050918101942c50709201254801d218865041000303031281408120020050100c00901402410b80391903e8460508800a4224a2003400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 746737733 1250 746736483 746736521
    0xa0f090b040c1b110d0f0b0c04030f06020c0a020a0902040602070906050f011110180308181c0201090b0a0f05010e130215160c050111010c02190516030303 68
    0x9503250030720a50707180b60700c191a4500b143c080b902500820010480742a5980700e16400d0307089180e079034a2120f44403a0b115403401c50000e049800e0440341040001c0a201c161082000140302003142d1144002c12154400d81c056906d0442c064078905100c5211300c020342010b0fa07003c000ca003c14481c1c0250040d50469801c6800190780d0b001d1500507142a0b00c11203801880104503100654403074070b803980040d0042811140360380800e101800c221100802c0002010400c42030920405900030074044c0c0140c1d9820710789081c01d80038005035131a81100c1c400102280540008000d840b8000c1d00407248071504203003032481515184203441e015180344000074220700c0c6000004200c684076a125140101e151622004081d813180d82442400c201100002a05113020301c50300c501840383d42144101c062045c02400071141c940000074000f40c0d480d49000b142039050041c1c440e03180d540055104190414080e0f0b584400c0d04500f4103a0402202c1132038000340704c41008000c8141601900701c8010b02ca07021404030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 746738983 1250 746737733 746737751
    0x5030f01050702011a06070b1e090a060f020309100c020c12060609091c0c020a05090c190207210213021902070e041a04061401061d0307050d0b0c090a0f09 68
    0x420280480c00c68a40d21100521003072000c81d0700780d054149d0001231248d044240d0508108000c2c00d0200032030341d42c0301d9544020003000030081d10b03001d07401501030002c8040d07046040421807640c8842c940c800b44888940d940701d0746440d0034400c03c40400e000d0340241c10b400c207c00e464240e103034131000102c5400b8002e0a2540110f80d00c4400024903405481019246101000c920342085801d0004180145e030300c001e10300c0f00460039175948001240101040c0c00600d58400940c6080360200400b03107910300c10354000070b0003082030055180d0703480c0d121100503031208083c90302840010021003202c441038000302c0c404100301010000d0f00c065540c1030f6946408540107269150812400c0f140201c40c007d05407040346117071050000303050502d5034006215206c0454034100414803204481400d82c4520001002c0130300c0200d0380581300401303010400c003c0d0b028207940750509004c28480282500001c11901c040703030011f0b40c042d100f81e080e604074102c024a04080190b4494082d20f240f43d80d0302502540b00d07c0c0101c29 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 746740233 1250 746738983 746739011
    0x110c0d05090f22050a1d0f25151e090819030311040608011a21090309040e210c0c1203040305060f1819030f0c151d0601031e030905030f0105070201 65
    0x4403200f4007c0c001807041c070b045840c0380c84080c40c02010003040422141e501042400107040641c10601140d0b51b522060181041403c05460070818004117005440750b09000b1550003003071221004a85c4a500c03000c0542a1404500404418190560608021038081803c2d6886040359049031a0310300c000038040b104041413002071007080964400f983c038084002d408500b0325510a94090f00110544c4c0c10401914081810b40d03144025080e1560062000e44030004480c1d00c006050701d0315002250709000d0200a0b196848058007611803143d454411104c0d010358040046070060740d0f0103002d032186810320030030705203103a5070641d00a103008100c0302c0040c50807100010a641c0016103a01018581d1030107440617150345815480740000c02c0708c1c18840c2408104000c460002c42a10001c0000d20440145100000249002800704454200500401c00714113400f282d044e4604065884211a02d0545002c1d81c0c100c11035400710f9018003440103241680107040d482030384505d07855002031042501c00070318 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 746741483 1250 746740233 746740243
    0x307050705090f0103030e0607080c1c09030308150d12050301060f030c0c0b0c0d061e0f05010207090509010204180905061006091710110c0d05090f22050a1d 69
    0xf0344080f4150b801c1c01040031030f201d6030f5140020240a042a03140211544a003103e5a001c00c03405c0da1694030080031789280172040d04c04118031400ca841c003455030a01b543d0300240a10740c042c244244408900a0a071705039590b200355185500c0c0c0c03040f0050403d049040024200c1e8200b4421080461902220f42503035030300900070340320100102e950301d900c241c900c0e6603a02c45103580603180b500007030818854005421858414400a4007414620000c01c5004140b000080883c0303130010010080c070341c1c1003004682d80008030030054855040e00881d0540d650f0700c0450080c007070b0358440c841c0f211705030068001c0c20713600740e1090046a01130001c2c3e0b065544c4480d207420307042210348540b034009070007200200b1002580112520380030341404141d4200401c404034400a5031150a100044a0030003e0040e40d48031003003041d4aa41c80039070070710b141404d0040b00000e00100703031a0b401501401481c0d0000c1c16068003521a4454800006400c01103406c0001c110b90050040401c0e540d504107004070320342102c03000050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 746742733 1250 746741483 746741491
    0xc0d03180c0504050712020c0a110414180307050604060b04150e01170312010f1502060610120b040920030307110d0302120d05040b0705070f260705030705070509 71
    0xc1d4100c5410301e04401e0100401000b420a0308000c480e501d12128000f6900041c90600c001400510040410341045280c8918104402e803203a841d28400e030446000301000141d201161110114664015612080c05d51054200c01030240c0512000c1100b00692075001c00036007101a601013055032208a9222f110500f14081c15130701c548007100400480d4000704012030792810341d0065900f45440506402f24a440c20b0300a40c00c11444601e0a0203680c407910b0134265080c405100508250074540003013405075000724484820001086804141c858940e04440b42c42c1002a0007040344e00f0321400c0c10740405242c481c42d14400c41e0420403500a514001064891041c0c101c6082c1207209a29001c0004c44410310030300303c1c00d60140b040981500201c1d08050491741c8d00e103030700119107032401d8601040310040c0101000d090007020b01225003c50f80c040411510030703a00c41c500c06035941584895801d051405020344070700700c60005140c0104000400507050181c480c408541005841d1400c11009410484d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 746743983 1250 746742733 746742743
    0x150501091d0703080310090212090d170121082802030a120b0d02030a030c03091a0a0f1202071a01082e1404201002210409020c0d0318 59
    0x1000e1011070b010300010754010b280925079842080d907c4408106a03084001c1e1429010510800c00004134428007100c8542030244c545040c40c2900c0012114442c0010302894102a481101e000f0303c203d00c0605030040307070382c00a1000c0c0c0c8900d410b1f85480d00040412540c1d00044640d084031406607030000090f1900c043c0346880308248500360101041c000c00b102e03c2000c0c0d011424041c1403000d0380b42481070340e180720b00039076411a10030308a0a0203030413603150ba031164200182e64103100082443d07000c29034031000d440780340a15040e1100c20040724008050500d030700d44988001380e1f0400300b200f41001190070a0301030034004d00c0c1c2d0f070303030351070180d845001001d00901c4130700348083c00c01c1904035801d00100050321035a6002641c900c0c80040c110180c04110340880d040091580401155040303a01102c002e61003c407146003901031003160003034440c25204020144030790316240d8500d240c080e0b0030680d006003000c1721003151502006603106036036a103000f1000c8042032a00183c048000d83e15410310030705517040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 746745233 1250 746743983 746743993
    0x203060103270302070e090c040b0d02040608160506070309120c03060c05070c33090801050403030e0f0d02030d091e0b22110111011425020606030607110a150501091d 73
    0x1a005209c041c02da5820903903402804082c010b00165610303c80e0780080c0c4a030b0170040000c0e0345400e0135819040300b00d03040030740b144400f8480d60b8002640806440240c0d842c83c04e0b1030003668654580b41d202510103800007400541070141001c40ca651180107089040d004441050510b0743e10541355155505e42000d000405045c01108001c090704c5100b180e001c00810300e000e1113401d40d45e845040c212901030f01c044000039142c8030a000d400604101c642d61607024600a050b9400c42c03020040d58074441c1e540305e04407c03038640350300304280060105125000812000701c1c0d0781c0d00c42145418030a0380002c642e4243c01d9004818100e0159600f1040341c184140d110614800c0f00d40342e8030066900503202200c2407065901c40200403012004804054040d0300e50320103041c0b01071080000700031105001d81c1e0380000c40d400942080001e50340082c031190403005500304032510380141031070281030060549003c0e00e100901c0305400302482d8950300c814100e8803600010461000e040811007009103007600921100c2d444 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 746746483 1250 746745233 746745253
    0xb03220209011401210507030b0303120402040b0406090f0902030f060f060d060b040c1106060303090d1101140a0905091b0a110309100504030c0e040c090203060103270302070e09 78
    0x9241d100003483c4505040c0415800b080c9035003182038150030816040080d4440c003d0010940d014050410310381c4085011758246040140140040c10000b000a4803079612924001050703290f50748100b0241444260a000c1d0614a03200600600064138003280240704003c4003030024480400c1240c01442d68865102007600d69001704107056580410546a441d51140c29001d6540d0310305c11003500605a840f0368050030410400a81030240051000c1d000b40c004204020942e80c030b0031240c3c1500d662041e402c40128900300300407070f071500c2040321540402d0400910505000c0c0c0200c000f508494041322502816519000782c2140400c408404400c04071090200700707511805181c20381c0c180000c5008890905450600150382c3e01c0d81400400b011890014040c0280030222060350007524070205d910b03699040595031400c40145034420720300280d50200200340e40c2ea2003500400c02444010f0180004c00103107400c0041c1143d17004100720090b200360b150028104200310b600740d1085058101400311212 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 746747733 1250 746746483 746746499
    0x6100909050c10210b010e060715051009050a0b1f02161502060a0c21020f030103080d0c030b0f1c050a0c0851010b0322020901 56
    0x40910201d507540200d8000c0d00c50354443e00080c203d090302940d14680c1c0320b40d65140c1c281080d0101156880c0c0c1908110503400a84d03000140e480c9012000e8901e15518641800e00c0c2c00d03004081e400461145003403a0600401d0080401400250380300180200040e4961a980c04200d445060b00c0030782003041001421380d1402005da2809098100380140c0b01c811116103003d1744c01681a030406446808036240e1000ca04c4c0c2d041000da580700b00451410080c01c0d500c0700300508010000c400041031421682c0402c410188503805440c15128103030040340d05e130750310384c5040080e50708115400502e02d031402e00400c100510034040c020390790b400030b00f400740f00e000300b00d00f03000f0301b000e0081e61890502d0302e40c00d081c00000c404205e01c82c2d10a001d8400071561500f401c1886051036079400000c0705042e00300c401403480d141541d112030021a0301c04a1101003404059800307441040c441040d2881c452032a000103000d9240c4030095116565400d04401015003c820100b003030045410042d40090300d4100500007a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 746748983 1250 746747733 746747741
    0x41701180f1401050106021b01080103020a1505130311040b1009140103020903030c030304060c0c050607031e0e0601180e03040b09030a15061505071104110f070302031209061009 78
    0x160085500b0302c4108508502d280c2903ea00380e100700c00680c084200c81003444984c0400c48401142481c0208079945107800048400a0900484040c2002500c0030380a1501442c11248280c007450903c43e0a60303507a080c18122018400291801103050a868051509c0c040c28880000301490b01c58000940c105203c0c4407103200304148840c1490b0f82041150303481d45d400c10180031740c0340030b6000860350f902e0140b80c88810f4910003081681400011560304002030780218590740d001e14281f0300018241103241048000400b41c043e070590480c07610889a1004c8400b05007a41030b110a00b44802402841410300f000725a8114814001500305002c18055407507407034014001060300030201d850352031a5484a010044a000440a520780e552404025240103150f00c0002d01e9081e0a085080020315180d003407451954804082c825170b1741e01c0b05203507041084000d80d481141c132240e496444010700d2802951300c3d80040b09461400383c0b9400000e5406400280c1c841c403440d00f030050010f0140c40c12060102034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 746750233 1250 746748983 746749013
    0x6081636050406030c0f080601050d06021e030c070c08120409050a0b120607030b010c0807030804050f070801020c06010b0f0f070c053d0e120102040902030c04170118 73
    0x3a00418001a6540c0c5900540740507501031780101d0246072828200c02002005544002e40030382101004016943c0c64012495aa1b5001480985e5a030f4086403074005016008000c020320f03500200c28010b8081d03d07a009440914428800d40000c2c94607080090341c1e40072100040042200204424040300d6659041325070021105503000c140d880b0501e00046c0520802c2407001001e070b2000c020050130540c140105240200300f0b0a185413045000e403102d1000388030b60900501032124040120b0200301c002c110f06c00c0740045080507071311010b84503c03155001c0e60165060540501c140d02c0003046850f0390400700c800e00101520054680802c2c031020824540002406030b40d410b59030b400c002103d4a40141c0d200d80010002d0f180742900000038411503003148060411b11410b5200014408040d4005002e40c5200a0441c0c0360f110500d0300b000c90901901c2290410107032180044103010341c1984600140054030f1404031102204950032000c1d5003201d06520903c190aa60010100041514207a0000758 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 746751483 1250 746750233 746750327
    0xf0d140f071a1506040b09240301050a05150a1404090e0102091e0d08031305010603060b030d0203030c0306060d061e03032006010b0a030213060816 65
    0x90a102881480040c0c0000505a41a4100c0076505650920141610754004007400e0315034030141042000c201c1354041d60003072501c0390f40e001500814039500c19407035203660f65148045c401c00c202001c982882c150402c0c80745c280208081da00203e000d1418002400050000c1c01c58a410004860422070720450202c004000d164070410020694403002d0160030403403130b4410300141e42c651039202440009210b414030801d41800c100c1510045a503045048a00e0981124135903440e521100f5a2500d21184c080c0020490361a140380001008020782144030150003c505884060403450000e90b120700c411603030b440600b00d00f08000b501500d0410064041002600c1e4000fa903680c40d03205040440b030070303d44d05501200c600c403030030402c041d40076442214104010b01c1801d07001e101d0940c050303a10001030040c007002d8540031a8660311544a641503a0181400520030308105640c1c2c1c202410b0484107803a07918000f46400340580401c2d000e41108485280c60428140f18030701d03000c5195203200961500c03040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 746752733 1250 746751483 746751487
    0xf1318020918070e1c2315040201180305011406012a080708040603020915040605040603180f0c1a03070e01081f080c1903080405060706110a051b0f0d14 67
    0x1004ea00d4540e41c400755144100d601844243c01401e0008131250400784440c8410607180c03620b4018000800d0ba0491048111880f600c10340300c030710040e51001e42500d280c071110200d0b50400400d0040c15000700902817494800c0940c82d880f0303c0011130b01c180a20181054014003503403800310718000d0056050085004034031460400e0b07800c1d906c0124941c450f83c04100000d8003c60f44204501d020044c10382c2481d908244145820b1500c0c101501e540594030171041030560b1114508680300c407030340946102c2540140540c100e03000d2481c06042003150f80c091402500841d40c0112441041401103d0084070940c450300b1316070050302d004440b0203e0061440000c501400c3d40040603650140040000c0c100c090007810700e00001c8014882c0d28104114070a1000800d00310420124030103404032400e548054403400d594803214140400034254013030075600c1000740020b802e0b0b411503009015014011100301c02000718000b0200242c1e4400c401940c580d160b4021083d20702003180180070303a0740c035041c00d641014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 746753983 1250 746752733 746752757
    0x903031407230a0b1503061e0a0b010201020d062c091c02010212012615270f060105040f09120807092c10150e04020f131802091807 58
    0x10341d010704c0550318082c041c2181d0f000c5490901d800c1c04901c0d84181403007408988006019004c1880c04405000c00a156aa076000d10715664401e4040301d04c261482241844074035940e003000e441d00028010050480c0f83d107000012000300410041b40e02500a810081001080c00c1000d403150216485122083d99030811014104940d0103401a00078226451015030080703448030b001100c09040d44020038250408c039949587c910200e820075400004a1044a100000580c03003440741c200b1a40b07401080d4418042044150440007031101d05031242900c05021440000c000b940c01e03a485402c0042c4074030032481c02c103d502d91145290962000c817a14015542582d070b529041080303804000d0b100c0b41342c820054286240f401514060303030044113404101096030719141d8244003e40d014480c40c41003050f1101c40181d5030f9a29010b941400800c8103000303546141c84050000d548007a440741c02d40c407001081008501c81c3c035a209840604c5400b612600d1a54803401200381510f900820400a01c250180c0d03107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 746755233 1250 746753983 746753993
    0x3020312060a0e1e0c0f0403110a1d0106021b060d0b0a050402040b0306090f010305150c0714010507030e01020f12060d06360213020a0e040203070903031407230a 71
    0x201d028101e601c51310640000100080415114010900c02c00d0b00010818145008045821201120b80220f02c441e0806a20400110140c0d5141e02c50032441d0030300010307440c1076940d0b414058125080d076000c0b1030241c03000480740903c2a2800c000303581e001c9400d0151441401c21a004651282402020211140c1c0c8a10000f0200c2c0c2040c0c01010040c20701104100c410300340100c0c0e258100440100c01a10303503145564056455088140b00030080300c1e6080070901144d00300c025201c030a41c7c40400703507140708046d2078240d000700003c40721140044e007000d0b1480f490610610803030392862586034010f450040c10480c241d40385107010b0110f940040c4000b80d404042a11841a0071100c541005542c0400311048130400c980101c104d9154180e0040205000c01680c580516020740c0001100142e00d03096140c800380d5101c10540c80550300a40000108005188c0c800e20305010b581c4a40c4500e103000300c6443c1c502080d40100d020003007020102802c5281580c4a1aa010f03540c000c51404480701c0303410036070754 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 746756483 1250 746755233 746755259
    0x513031203090501060b0c060601260a05040221100207051e01090326063d02010608070b0702151606150e04030c061805160602060c0703020312060a 65
    0x185a00207070362036641c4000c003e028001c4100400c0e81080f02420120000035503619000302500b100d050142c0b13020301e40e1624008036250350401032400820403c500d0710840d481c0240604a0b4105c3c0300d18060424424540242e8101c01c1e10141c804000345054841000c03503200950003404d041c2d0f41840b640141003803400940049102100c2e90200129a1b401c9601e03018004244c1460425001000c4000d101600030201e6040c65100c0d42c00c8560801110191000d410b000450400c200460b040c0348008100b06a0400503803400d020165000304a5a82c0d1900803946800286c000c140c0c2200080204e84058501151440302c40d1a924190300e00e41210100300ca034080c400c00380c0840b101a2201d2005043d901d640c144003005144540706000070b85880d80d401004a401103000608a9035140100000c00d004158030180030340e480f40c105e030106200c08410360305649041c801c140040c400d05002a10000c5050180e520703007075054005600f425070f0042d82640b215002050683c000710300740d000148075800e02c64 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 746757733 1250 746756483 746756513
    0x2413020310020a092301031d0f0a030f0302250311061003060606080609191e020c011805151b0d0b0a0602010b0607020918061008010e060601080403051303 68
    0x40c1d076500f44800103003444490342e000c1d0301000c8420126030000880e842a8418640003442c00107106103c07035a55503540842c03051590600c3c0304148082054900c001410305286009468280c40202c0751031046081e40300e61041800b03070b01400c079101c5c400e800350340010007a1203209040000d0340001050985103814411200000c01271101c040030420300683c1d1003110050704140c82e020070305280a20102d1003480014040d0107102071410301c0390001c444250303c103042c58451818008000049100711b00065040629440119443d0040700d107004000c2d032501e010940c0d4484090140096146840d410048005100401c55040040c0161000030034a0086c03045010b01080080c025010744240401080c00b500b020003968905610114a40d4602c0c09840308a54100c0d401041691228a1901d0202e03e028008149108000c10701640310f840a50700c60948846a00800240080303841e4556290019903401e80404e5030007000c0340210b84200000c001c960503481030004a2036880c1d5441d074590000c0d035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 746758983 1250 746757733 746757763
    0xc050f0d0f08070c0809010c020420131401080708101a03160e0108010504020a091206051e070e0d060b09010801020c1b060a0509190b071424130203 65
    0x407001200d207a0000040343d008002c1c0d02d01680185130035603c09009104030500f15040c006043d24a4045581d81d070003040181202c040d45054041080c0700400b4603810000381d01c06032114860000c0f41c20b00300f01070580b00c10a8143e507880a03d1f15042e4090743e1000025108020000d40700794082402d26000340b8021012044217201540c902d44503413901006801c1417500700800090fa0402e0400e680e01c248414103540d8203c4005a65112b140021f48114507540e00408044440c4a5030724244001540142e204400c400c1d0307010070114081540c0690404111600400720703144c070300f5120803800c0c0074a0744003440303104420000d491a070100c0000c14100099210519680d00003840500e0140705010741c40074583c40a11404100400740700007061401601c07050ba04011001c122250b40740d41d00c030921000d9214103500c8180c400d4450b10002e0513548041d0080e0741541030128150030102001459030f100607005010310710004044030700780094140203400c1d0784031880501070840150380c0611408603052500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 746760233 1250 746758983 746758997
    0x6130608031b060f180a051510051f03270b04030f18030602030403020705060a050c3309010b060a030f060f12110a0b040905040c05040204150c050f0d 66
    0x501d1405205180c0516800d40c103411450510000181041100d07400105215403084010000017405280c1020140d0142107886080510681c900455803418001d0039500034881e01d81e83c841d0103101460a140c031440d0401111190310703020f40d6120360300c94410011041840c0d40100301840a0310135020100c00191426202136082c0401c150f00161a40180501030801c0703410107203591001401445d5512010b001940c00100140805100b1712441c405410000c10080d120303071018100030125008542d00300c0c110720500d52924580c10107174039840e880e41180944a80403440c030480399080550040c02402c0346640341c1d01110b1496440d10094540c001c141d0760300058204000301110182c80312540b000d1314000701c00c04203004c0414901e004031801504203070000c0c0b114281c00c1c0032405050896001064400000c5400302d1900980c0d04210300490140c8403043c0c01c04c2e00ca804001c101c0c1300d54031803180340d004106191420341d8020024545036902440503100207014984c1c40e50301382000d00545100150360 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 746761483 1250 746760233 746760247
    0x9030a0824280512191b15020106081c030f0908030c091c1101050c120d05180705011d01030b090901290d0b090a0f030807090b120604050613060803 65
    0x440800c0328001c1c5011188401c03400d514011300c54445c0740401e24108202100d00b00328090180400f07401050405100e04420141e82d100c6c0e0460004070040b403608019401c0480000ea803c41c000b0b000c1003203d0182410600c030402090040d00104001400c8036000c68860340803001083d1450041e510035918107010903620036264080140d41c0101d0090444607413014030002c0003140e00100c1103035a58000307003802c82d556101c000c0190301d016200b0b9a149040c3e84009045d00c06140e440d00180c0c010300366034021030740d00c1102003030b174a84070920340c02080d0003d07000959150604042c940302c24403042d0103040020310f40300e184002c01d044640464000ca0141c0d1250b0110380a601861542016203410000c0c40441c1050000001d500700036001001e042521200041451103605214038164a0782c0220060366490003440d000d800d0354402c803520001b0481040700010645140c80c1120051b0000c00031040296a0f404200401040064203558000da0710200d1100314503500d10a00000e0007100000b10740f1240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 746762589 1106 746761483 746761549
    0x70f03080c04170a110409121202090d11030d05040e01051009080d0207050a050d050a060e280510090809040b03030c0106030303050f09030a0824 64
    0x441d007030307800703410f8000511100d05501c90801d03540c14844560405c0200d40800320007500340042c18000c1c84c2c44910400c00b080e038581007104018144419540450b4507182c2000048403020002e00c0c40078410b207010030002d11001428036000307252505042207100303a40f1040c170603e8010300802c666000c0441c01040424050a400021100303144002e540c001d40c1c6481ca44200b078003c0b20000d0000c40c51b814002465a00e01d40c00c14000c04410507640d4078a0010298540e00101c2c9010b1190b05000c1006203450101d400c1c100406981c01c0a90300d410200c0c01c10085503450841245000d14541c0090f05203800d50f600288210750002e18450005d0102c0e0441c41001d85c0c0e0700ca15468610302208160309580301a020390300070b100c924016583c2156169a9104007980791022904800010b00d041070010708016911203054144425003103201c003c0b401d03242001480b00d01c1503941100c0010707824 = true := by decide +kernel

theorem cover : BRFrame.Cov 746582733 746762589 := by
  have h0 := BRFrame.cov_init 746582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 746582733 ≤ n) (h2 : n < 746762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
