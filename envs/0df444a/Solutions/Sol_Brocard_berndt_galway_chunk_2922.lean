-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2922
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:08:41.266913+00:00
-- url     : https://prove2.me/submissions/ff152080-3716-4afe-be7f-ab0668f2501b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 525359712 ≤ n < 525539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 525360962 1250 525359712 525359729
    0xf0f0605090306010506090d0605241e0f01140301030606060f05090109051c0c0b070303110f03040204150302030610090c0c020102030d0213031403070302120c060708060a081005040606 81
    0x248020350000a683d040b060003490f109600000d4140515607494004181a81d4004800e2140f841c20404440e42040141d441541e030b5880c11851800515100000040345810b0300c200300d110110740300500c00783c140c15008690500c03580d03800c5100b601f9608806140214421040811001e0400310300404800110300c005080c444144040d500c1a0b03048034544c025940d047d82c00b80c440e01c4810388901c00c0c10300b95401c05003034603402020204059005070000c26456000c1e49084c000d42c0012040c0b00b40c42d00c42c2d0800d81c0680901480460b0040c035003904032003d440700c08040d20680c95202c0d00003904008090782d0352141315881450801195210340a02d203030000030ba0406003040c40e01600040c0d180c0c880c0b524030b540010343c00542c9002c130344035060f401d40103983c201c103509811b049841e0030940d4039402020203038090b215007d40e5131581c0300144100d80510154201600081d02c1c3c0160540380c11a010f44140d5000821b544003060200d010001c5034940641d0b41004030b1181454142241128070a4110303030320 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 525362212 1250 525360962 525360967
    0x1701030b13032102070614012129060f033007060c0f081b04050423160806190b03070c020319060b040c0f050d02130f0f0605 55
    0x4615200c60896100000e00e41c18031900455103421500c412108a6181d0a00d0090103074100c9010b00c0c2e030182649500c1001d041000d032101c02003e49408009206600700070060384c4a54014805402502085522645040c900806200711110721007003080354518003a1036000c104a130314070f0907644800180c18203138040d004649000e007181150342040c48081032659100d000076081d07881b0803012140c03081e4000408102840302e2801c001e15131010038585000007800071004c1040500043c452401c243c140c0300340e89140c00d10700f03001d02c0042c0c07060314080c4002c1e5a130441c0d41051424911b2000388501d8403604d481d141046591000b40c030944c4003400d03250150480c003007034482120030810340381d081d1901810400e4a99681074421102030b00007000080d05401540c0e0500e0003024000c02103280c803481800b0a1007020914802d2208642c0c1d80220200020203d820884d40a40641c0c02006c0440e1f6056015260041c41020994000c003a940400c51601c0701100820405d401005048042d18a1385813651 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 525363462 1250 525362212 525362219
    0x1f050601030c0e040e0f101b02060112060c12090804050a0b16060504170c0606130209030c19080304030b0106030c0503040317070522090b060403050703140c0904121701 74
    0x3c11a21905070700720b0185641c1c04e4403401d00c00c0104250000c0140202c100d450100c40440c451002d03008200c1c1c081402409420180e111a00121309a030580e41400005843c203240380d240c1742c002c0c05c5003039540020b21580468401c0c0400c03d030302131010514000c81e42a5a01e074500028040665074a9000e065000ea040c001b03d540700500702402c0328072603000b000200f1145c0f5641480a401640303d1983c41e800440080d22840700640414424031411044881034180035250540106900c6940091035050f0170044c256a128a4a0850440440d40381ca081520241e12003901914644c06508290f9034520a8801003001c6541809a02445521441d01a046003400e84e00a451240302d24503503078a665001000882ca1846030050f1404140060b1031180100c1040040c076208800d14010207915a041a03c0741b001402e01e90200e80450703603c280100302103455a154400c1840a940c40750600e409a42c10044455071240c0ea0140201d016600d12045614501c4c03000c1c000c03003001c003500c0701000b100c0b00042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 525364712 1250 525363462 525363467
    0xd270b0c0a0504030b0a0b030d0323040b18010e0a030206040b150603010b0a3f06081002130b041509090903050702010e0f0a080a060f05090a021509031f050601030c 72
    0x86045962100180484e52601c6014501070b0030302c2c48187e0b405101d0000d0800c0056415007260f0a20070101e8070210381d5a080c0c5000d40100001206c02230030810449000ca00d10b4107010400c1440740d281c0400000780c40100350344a40c00c013804188180d005a1242092005000c2005082608180d0f1412917100c00024080070940310701051180c24001c0b240810ba803414140a01400040703540c0722020742c0b03084c062105140c10961901c0002118600101440080a418501c034000075541c0d03180040041441c192000000381d40100c08a600b1802440b000240c00c04408000c0e101904904c4c41244542c0b0b0070b181c00404030803903540002406400e002040307011a82000071208600d40a1074420340c1c011481c0042019a405c1d4090680c00650860340054140f44c045501140c4600c1030005100000b0300806031002d85206442018041e040380041f0380040c80d20700c481641c031018080d1141e060446000c0000c2c1001500a606410540d03058041e01d9501703194801c2030781c040d809007001c001c2c8440d1020b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 525365962 1250 525364712 525364717
    0x703030507030e04020d020c0114040b150a05030d11100908070602091c080405040c050408060705070c0e01080105190218120106030803011d0906040f080d270b0c0a05 73
    0x1409000380010300c0401e240c412030041901d080c1c007903c155995104138800b00c000750310200c0441119483d1085013a040c5c15011241c500554101092104a0701e8904081d06203070b003040c1c0e00c40d0307220710f00b6100003405460a0100086a09041d00e078800300050007030304036060422000d00060006d14000318070780000c1002044d1040c0e9600007900584a00064004c68580080071103c1840c8140e02c100500c200415000181300b03884064500b0b0020307a00150058405015178003511099801040c00100802d00c1400075080450285103e15425503030f0300780e02c422541c030070b803c40b002507510b9104105d00401807040c0e12035120b032407038411413405100d44042c07601e55400000310391045203840111050f070b40007500402e01039500f244050b550795075200a1904c00c00a5400c01120900003000007035841074000c1882e80c400c0b500a0b242d00d00c51551603880110542c0120720704000e06030342d07001510315108810052004e41050400c0c05401d24003c0c00c00c0d6900070030050140c5d207055810403c042000741d00405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 525367212 1250 525365962 525365969
    0xa0c0503120f0a050405130c03060501090e13060b060c0f0c0a0b0a0c0c090c0e040e0d02030316032307080c03130213090503030c12090601060c0f02010905100507050c0609010207 78
    0x60035032a24044401104c40d07104a80c085544405100e080d0f03c490003140d409060040b0180c3ca041207440d0f5203000640300506140b05880f08a517030f143c00640c075803000c14031503180244242000130354080f15070000754a5800040d407001840d0f0180040044c1c11700c0800c40c020405504441310f02d050361400a41e1607039440340080720740404c884088940104040140040040c0203016018891580c07004401000c0c2c100500030350b03110364200a550140100003007014201c0005c681d020b5451a40e03404020002c5045d208a4030b4101a500c0d48007081c00410b490061649040148242c1014205004000c010b848081e020204000041062240202194280340d60650341039072901c1200803021548001002e40010181286c000002044100c105200040107615851100d100c401c0c2c4681030f68a40e80d040900855010030041e10307162000c00d40014421b4801c0e403051412031001c64842010813810034126a4000c04103002280b200b003000001c1c4000c141c60102079800d24105004e01000039581c403c2c912 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 525368462 1250 525367212 525367237
    0x1701050c070201110a020a060e0306010b09030705090705210604050702010515010f09030b0a0506120307050303010e13050109060b10020105060f060c0f1606030e2121090a0c050312 79
    0x82e240c2c03004c0c4d40134081d00008540082c201141c5655840020341303001d005150780c80c868041c00002080500300c25090f1108004090000c101c40c5080500b4840d41200151004c414404e042c0103415815060402c0c4144170314041c881c1410a042c00c40a0009803400600400c6c19a418001000b1810b601a80700b161132200929100c01102302e03281003602c048000e5003019180b520460100322005090f608803900621094032000c44801043c1c42254807030254000c000c040e0340040004000e82040801126008049810103140c50b00b40f0341d460030700711040d03440304371055504c500c2d0a441c640340c5404270f034000469a00092100d8030b044070010340200b4114801d80d20494000c03c542119010802005024884100c21120b541c16808900a004c000c94460803002034103185041340d00d1000400c1086c03000c00d600300510780301c0d54074581013603032030300040c9000410000407192241740290071840d00303004420b02c5001e04002207041c2004181002a074001d00e00a40c000c001c044540810b803030441d0051035400d07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 525369712 1250 525368462 525368477
    0xf150e01051e0a1107030c0e0106020304031104020f0d15030c0f0501170903270310111902030d09060605130608030a12060e04060c0f0315090b031905071701050c070201 74
    0x2007609136005824500d821505124410002c010441d40d14500c5003603610f1003058040f10f87e6200001c13642c138880c138040180b6011a0705030400890074150080c00082c254031181d141400c020300c20180480360111880b202200780032108000b1b00000c00508005071a07031007507e0302c6050802c0700292001c81c29142c40d040c030082c92400600ca1032030078000d5604080b003000c151032142091071012a2402c00020207240700e400303001c1a005007541c8a11503c000c034003c0c440045d0410202049503000c00a10340c0000c0c003940010490b01c054120301344102d0401c14840e2000080d2030741001d0500c51601c0c0c00004d030703445403450300d0014000035000005455800350180b80802404032603a8510014010f95400310500d901800300748070801869070050307180c1030825a514200c2d00d00d44003080742510a0402120100440d400d02030042d141c0036004010a9076010301103407807406102c1046084103e940d0000d540a400180d414040425010b0740540b50b040d40c01c00a10003410000b8819000c0e110300c40c0000e043c0800c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 525370962 1250 525369712 525369727
    0x60219020d0f0c03030f0503040b130507080304060203071505070e120c0d03030c020c010804120c03050906220b03060a21050a0507060e0927070f150e01051e 69
    0x4600d000d010035940070340d400601141c2c03440c00e003020300501d0100b200402d0181401800e21407040742034038441e58002050007441e0325400200340480105a20aa659001c1c90602082185d0100000c1008007110740c010340c0d940d1030300d0030030440440701c40282030325044c02c1c20280064250311401d0170a00703150440f02c080154050130001d903e00b02c0b07408031840e04141c81503680c0081c036130980c0c011640780c4141d07000c1c0c541e040c5109004582c80802203a00802c0d0707041c501e0710f00070f1082c4030b103104600184c42401c1c00c030b1508105200290380340e000700d040409403148420340f0007039000305424900000c1981440a43c00c6050400001e90003142901540d001d414040401d400b6581c0d40000b12001d132500901a83c030b482100d8284140c0b1000f544c0120404120b945120540504208100e6449410a0742500003061070700a411602c40358008020110361007001d1012a000404405c888010106a01c11052801c0d400304080c0c20303441c08466050600c0300038000c0814008020500700312407911820015601c245 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 525372212 1250 525370962 525370969
    0x3020708030726093f0a0203040e09030405032a011b020d1b0b09030309090703060b19020114090a0204051b07050304080c030d020d0815090c0a0e010906021902 70
    0x50622105510a81da03506000703c1403008103480c103585d034040c4200040c240e02c0c00c00745c40e0070002051004140400403020300c00c04d1408039000c1c0411080c240b054074a401d5440c6860044c40005a03002c01c0303a0380000a0821442c5010804c606030101180010b44452403006181e481442101000c41d0510000800800d6008403003801c510340690b0040c14aa0400010304000040341c03150b02e024084d00d02401001300d64400c2e45c805640c000039006000754a81184a03052060600703000d0050810305407240002b250b01c01509019080704800d96980c01b040030b907410390007804e40f100000146200c0b001641800841d03003001c40d001500070740581c0c0110305034480c24640340d011201a45200341010000c10b50340d0410101200400450350810200c0f5541c80c501d0082607103802aa450090169001600e025109400307440e04580c0135054094280f8140035200c04550692812640b602050300d00080c081d5206402582404c02e001c02880c1031600703035080c624065901d5000004500440c10042d44c1101150b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 525373462 1250 525372212 525372257
    0x70b030c0409020d05090f01020421080d0504080a0305060f1507030e03010c05090a140108180307120c051903020706110313060504052b0b09031201080705030706030207080307 77
    0x80b1a40d00315541c603442040c01c0024007040d00c2c4540240280d0085803800c00c414000c4c5d80980d0b039821528440700000100300c85882c10b0881045543d400103110030032020b50503108052003035010715031103591014918001001c5810040605100f03450750061100c86855031342e28052203914105100355501d04505084c0d4891030310120036503240d820640c40600c04d030390110241a01d008107560038142603448000301640c101c403518601d4001103200001031040c0031440500e1480500c4903043e0707450081d184c0c4a07107003025801114540401c100d11f2180080001c100710505444d403c011000d00c0c40c0781c440c0e60080d01d401c40c9110300010065034203205641c4040034411107000205020443c0039140d03807200090300d81d4100d48140c41c03044182e000301114488100400b10440c4180300d420000400c0d050342ea211f01d461015003503a11f584402d10418026500400d505c40c042c0a03100002e0094503d400101840c2c82c01e0703a00010101030060040200140e0082d0540390425100d0030f22800c1010703080310100810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 525374712 1250 525373462 525373469
    0x80a020a120903020d030f0209030a110a031505060901061b06240e09010e03070804090c090b030915010503031314032104080106151704060615120509010c02070b030c04 74
    0x3529210120003059000517102050707030741540f410b1003885003510100b0124040c004a181e016040300c00300c0c2d0300040100c030210342d5580303000301042e042c0ca4482c0c030355107141003486a10041080d5218203005507450910a40c0380100311030301e031282100625501105044075180d0004080755102d140d42c0101c0c42214585070314581c445500d00c040c503030b40c55070409413920040e2a4141c0c0c0f946031400000100d6408000c40e504242c005c85003601d8145042c02c0310000342007900034241002141280810790a00c0500114004c1c14901c0040c0702d1000d29140c3d617402e00e00c06070b0105200e64410054200764034092400c84040721203403d4450802990080841c0c205810f80f00d000c4107401442079074122060700200503209030761001002f0031409440300303404070400300885602c0b00414401880c0c01d0820082000b0103500038851034020412540d128a00b9081516108007080450085806800004514820a544110008001d1005545072100652640414000ca01c654400000012101000c11003104c005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 525375962 1250 525374712 525374747
    0x62c031011090d2010051b0111030a02090a0509061302030a09050d02060f1302062d3c0405061803060f0412030e030d0c110f010b011707080a020a 64
    0x541d2524a0560020a03070700d003040440c490f04c00d204001c9814030780184038000d00c0e991203842c503103402c0d40c1c16070340e0070340260802406564071070700e1000895940030003071401844020703000b581380c0301c291007003294203040b94100500914112080205980d40e4405a001c620411240186da9459071a0307040e01500c0d450030090594418012610708140d400204544126140708102c00b498075540c0103d0011001260083d61042060100002c800f8030468098800c00750340f20407001e54500d42080e050a80c20402925200c1c41340e441400715440e0064040001502c200404858103c5808107007803154052030050038019040420740d0b4a441c00c4000e03403000b400341c004080307616600e0109816058000708503011100b8440da03c816080180c040d000705000c0c2c0180d4030103541001207428013140203004034000103003040304c84a0400c0710b1aa00744440c0411000f00000480c2d014400e00c00501606144d400c0c801d0041c60b90b5041001c0c1550260216400c404400400340e0382d800644002c582042111454141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 525377212 1250 525375962 525375979
    0x905150a3308040506011d04060b04150308030115030209030d080402130227061c0b0d060f02040512030a0f181d01091508070b0703050c07062c03101109 67
    0x410340d82041442c0d109034403a0b4201d642d180c0c0ca84018252514409035000301d0485a00045000603841e42c00c07181103108094000106d0f2000d4a0a2031440e100d9540140d8481c2c01c0000140000707000d03a12002100d244a08055142c8600355000c030f965a58612002810400e03c680071804640d41d41c0c407407041c284070022096440d90708010400344808a048500c0e0001e0040c500e00803482c0c10480d0540350021000da00c4101021007458142002c2c1400079001e6500c001209034180000b100d81c8104116415507070401a10f4509000a2003c05401d101c00703103140f94402e116020049910484803a40b14505140000e18a20b00d03107100c2c03a00c003006802003140410792041a03401e40c001c921025048071030300da005004030050f218203046070919502a19260350448841406030700034420082000c244280352061034021000c0b056401d00d003194002c800020b003240c8100c013070b500450289400403c4074041d10508800d0000000342c3c2c4400414007902e031941c6921880d00803411301c4051b14003400c3c002d0101403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 525378462 1250 525377212 525377309
    0x30703060513020415210507030216080d0509030c0307080c030d090605070815150c250612050c0909040606030b0a090b0a02040e041e0204150905150a 66
    0x4043e40181c040c8401025071110017000262107040c030710b1906980a19850040c220210360f88000c3c0c00001d0001c418940c08021441414a54003400c501003401240402d403034035080c0341c400054900140c200c50b45a03100b031061060040012040f104030350341c030155082d901d440780080d0509602812126001761882c08403403009202e81504030601ca0a03140e91009141d82c0c82c10400300f0310096029a440e040f56198070040c440e642400002c2c066004c072101124180c110000340103c54040a0355140103501c0c00e01c0c000c01c0b140e500001d5490850500c01300070b21880c030381a4500f0b18503015124001e4401e08801000c42c00344491703540418047c54228440d40d8a40c9030003a6101e003c0e00075600115144001600051240400e034802e4a043d1000d581c1040710544513a1201f4034a8200b503003109080240c0941c040005a0740c600c5030500000040402e00c1600d071800c28201c00b00d900040c90340346641203030440d1200655a901104098442003204500800d02903010b0050032808454140c0034001c0400288 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 525379712 1250 525378462 525378499
    0x32a0807030b01090e0601060e01051303060f2a0203070b070c061410050a05090106030c09080d23130b0c07090519150e0f04020d06140f0901150b0307030605 69
    0x5041c4c90840b801071000c903508440c195500c0340300f40f0900000417103043c101e21496100d0002408040c05c80c01d0100b40c11a200d8403054210b0b9016040c54200740e0760f0388101200e8007840048000e800080d50b4035004041c4210310b010b034072845503e40052840f005080000c900d107024184951600740c000c1010016940422141b00c0a420190341003074440a00c2c640c006214030f049003c0c102a51000341030705a40364a042001e034081c0400203415003e0215480010400d413404001c1c0ca090008945d4a0034130b402600300040c0c44184044425020b14102001400d030a914055115030845040d21070061342e0f05044d228207824030056420400816007018140419648460140d44550420388010000e1070b00e0781c808018070022520440290001c0000044c02c4101d426600030303400303070028148401941483c7d41d1982211014403a030381410382d04c8000e021804d40c075405010703405a840002003103240390890202c1c807c030901e88611003011400100240e1107600c01d03004507004000c00f400c1690000d494001a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 525380962 1250 525379712 525379733
    0xd020c03220f06020312090a210e06121501020c1903020907020a050d030504060b0901260f0a02040504060f4106040b01020a1502040f080106032a080703 67
    0x4000700089124404952520481e01039030484140d40c00031072500e04000140da054450040100c0d00c680181c0394003c02040101040502c0c482441d5501d401c1c0b1219440701034907404940445c00c1c05102c0030b10450050b0301c4003949203a0008500050380002c0c55101c00100e18048880c0340302c07034100703c590518030f905000c100e2051003664400c480c024220303990440300b26035952410001800c0c42d030048041c0184e01d07001e45e000c0c98203d800790301d01040400c11070f40441c00c204407e034000080f5800c080c1190154240c0c5210184840303401c207001e004d800101030612503859000c424080c0c0b0039030b640d001150411640e94000c2c6034401005d4000d014403559049240c5220725009901c2a101c6181e80803548803201d8a240d22460a186030b61204d013030f85640003800002d20404900906500c01e040c41140460b80689801072914034004015941d141042c07001c500c1c0c0c1201d64400000d581c1003000510020301800700d41c05009e1089184550b294518000300f2001084541c018145805440e40110602071407412 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 525382212 1250 525380962 525381007
    0xc02330a0305010e101512090c1809030915030f0e07080d0c0b130303090507081011040b0409110f0d0903081312120209041107021008040f02060d020c03 67
    0x808010580e80e401c00041044c10448505c1d0140c0407102017400425280c003400c170342d144154504905003100141c0100d084031100036003a1501342403034004000e4007041401405d00c2c050a0002232050401698003c2c045074a18092103130032100184400c00c00511981c0b24000c0640885402c1c010b410f5101000c0d0b0301c84180303015070115805501450000c8502400c20041982e80c00001888240c0d50070602440020711502e007102016160036800d0081181084000054072904000d44851800a20b9500455070081019014a40c0620041000701c1c056010703a02160440c400128689041c0304c0141d00c14420302040f4108014041084007004006512908015220b41c40b00c41d1b083d12001904100401d0210004241d11455841c2c0a841c84c8504220108614501800350401e13280e10700150a9400020031484012008501c02c019883c04030444003008140d13060218140c145070b10342c0d4258000900b00a409401c0001d100d400348551941101c148401d02c03c1540e4503a201d00040c0800220b9408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 525383462 1250 525382212 525382217
    0x109150603030e0126180a1a070207030c1e05100504030c140d022b08090a060e030601060311070f031101050109020906090409061b0206090105010e0402010c02330a 72
    0x40a016154080e40031803c59594041c05c610150206840d0310000301d100410100c1a4901510a10b85c540c40411180040c1c0d8030610950f00d0840c9028100440d902c4010181821503001c01000c202040404600c1415100c1d242c4050141100030f04c0045a51501759101e560003a0500c3c00c008074540d4040058016640303c1d1121107020b5949a5140140c1d811014002d54402c0002110304c00504d09200d20441c9a03030205001800d00034039030b400d006188102001a0b542c10000144079110780380504000000c1c0c40326050003002101c0d1400400c0e82c03004140507a0742450b82d1803c003003c1ea4292102030f110b804d588086900214421440c0080c524440c50503001c0c1d00c1d6003800c0012520102500a83c0c9403444040c010728200404881000050318514500361800c60b520800d024448020700d10380140e090503600200783d6400c1001c0c0550844505a214190984440d800e100042c2c0c4e00084046580360100c4000c0b980c001c0301f40518a1428502d103411001c180050482d225522601c07001e00b010340741e640c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 525384712 1250 525383462 525383477
    0x7020d02010e0c0603070c060b03070b090f040204060f050705011512050c010c050303150d0606120507080601060203071205190905011b1112030c0307050102090f1c060e010915060303 80
    0x207000b0703540d0352181c2c4011680c8503030103000191059210380c8a41180d82d00668010441d2001e520120b800d042e1700340c00c0100760540c0019030340b00905001003480040340c41a0303411441c09152150044c02840340d0621041040b600090010a200094004810b0090f40c865640440caa072600350901d042411302c02101caa000d4510945c5d855030055605981c0548c0003000346203955914450407000c40d04400480c0d41c810031000c6180d012070a1403040001500c41d81ca8105030800560820a15040c03c50380716001c640d22100c014814254080203503005c0039801001503185241c0382c5000c0e246409900c03540001d650341c4402c1c1e284080c1e4031074052012a403007070b202c842c3d5040e600c0d0a60351400000d5040a00700800d12a02144641402c0010556240c8142d0035641030880080c0d4003802e5510607181612541c0d00429500030a1605008030407552004440850710110300c0c050800d500c041800018000d01d64900103503410307a84c02c1d0400c0c40902d07031204141d60b50440107510000103081d076000070390000790314 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 525385962 1250 525384712 525384731
    0x7050d020c12011a06090a08100f110c030405040b0d020301050f040201030f0c091206230108010c1d10020f120d060609061407150e014106030703080307020d0201 71
    0x61040e401300060351590341c4203c84882d01808001d9001c403186070b0b0404010300703000800d241e05200c0140301c4402d0007008194000c1e80b8070a17038241c03004844d502050700300070442000840310001c00ca4040b0307101075602040701c801c220002840100040001ba405508290420281c03000c0600308612451003600c003006015082040c0808030b4541300c4207880890781c4400284000807000410300d1100e8270441e0301140c4da22410b80c034004900c40c1070251881820000c40181303c94a000e008481184480b882d240b800b0f410200c010521030390318504d4582c0683c14401c203001d03001d40b09003e43c2c0d101c241c69034200d40103c1c03d12007801605500000407940402d16101021405501ca09011421a803143c0d40340904510000c4107111243d00510040710a00f59040e4001c1c10202140103c0300010040000000e940b00744c800c107805041c610b0406c40405040074100405c1408110010a0b54032000ca03503a16a2640d411340861700d01110b503040501041e0001c800c1051155001400520140c201c1e4000d0244081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 525387212 1250 525385962 525385999
    0x801321b12092a0a0509060a0b0c0307030e180711070321030b0d0c0b0c01061e0618030308011a04030609060213080f07030803090309180a060b04050604150507050d020c 74
    0x43c1244400e42c410a080302c00c00c03081c9484007105030030000060518100d5a559900c2c0450b40c0e10404040056800108090003403540100880c00004400c1d03c4412001302e036003407d81d9419100405034010320241c030b11020385407074042158401459022070b15400c1419590351080001298525910002c0d080c03400220b594145124151046584060030b003103107a04003040d1042503085047e80032199036a031580002c5040500100020702d03c822040c80301c03c0b50130004000c01d088100c1c0d038224000d2414000402c0002c5d0310150050440300400d00c5d80f10008800e80681c8524840c990020344032a0501e0480070a0142a5000700700021000c2c8810a402c1d944c1c403401030b116900f103416001641c022a2042010882d034400442d8800c0d900d000396407504001e0310018140d54070030088501032000903c100414018179100c3e11f0054490b5440e8682024a070000080d01c034880c5000340c0c100d1f80f4400340c203004010b008005803580e241e07110095503000210030344001c0d40c0e03c1f07264020921030300492848150340d08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 525388462 1250 525387212 525387283
    0xa05011104171902040c17130614061f02030d0f020414090f07050a1b0320030c0c0d020105040b07060f0c0c080a1103090a0801321b1209 60
    0x2000c6031a0041107043d9408200080501040e91402e115800c8246840c68401a64403071240d42e0b000d2102c8901001802c111080720040300407401500300c5103003441a1642c880c481c202525001d08200c100100c03004004a046010b200068094039061455002c16112140c01810603140310030110300c403141d440c4041009a45003a074080b00000c801b840800d00d030f10b1040000700906541402d0a10f2061001058081c50001d580d0303040d4005054840c0d80220007403406d0300c0703482c084da0100003542800e8468001a03101c0c10350080305840394031941d400c1c40c116400358007690000c241e51040d082d2101800d09081d8080c0c52626000e03c8503500e0305c1ea948003450b003d28003816460b0782003003041d424280044001e8600c220020011038451005200c07210081d6242101b1300c003d800d80b01c00219541c1c0800010051403264890b1040c8180890150000f901070100141a071040c801003c0b4820088002c0c401c600b03a01c135080b00d090390161030f07004009d40c0503400103000c0c060001ea801644503081c0b0880b0f460181d01c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 525389712 1250 525388462 525388483
    0x605031e06060d110f0d0c230912070b07080703120603030e09071e1d0603010e1b090402040e0103120e0333270109080412050a0501110417 61
    0x20000e0011840103000e6034007060040b9540000503241ca00120365205941e00810080c14040c7d40b240301c0c482925900407070050060003d105841c0305841e1442c3c0754200b134014165554000d07902400080d174030100c1040642c0003850040a010f5607550541410a450340c0805c40071390100c0c9403904030568040c10f5115540032a82c1550707610440d603c03402d081140d0386101502620421204407000060310000440c3c81c4215403542d1200b20030000289140c00c840b030a41800c4600c01e035000c3c0300400540c60400b02560303000c0e000a0110702e103030b407c210400315140121404950000e10124010480018550314035041e24022641140d810741942e400700c0308510420a000d0701504100c01042e4040d45c01d8400f0f407c103075544103c90200c1641c240da43c0c214600c080310b071140c00144082e0a072070b803200030b10400486086880000d00c0b0038050307501c41c0a603c1c8031320f11030701407071514284405017402400d0010610040d8010001d1000c082080545c46040e04603011f003d141902c20003e08030400c10010303821214 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 525390962 1250 525389712 525389719
    0x7031b120305090103090605100503070e04080a0807090308040605030406060b03190e1911040b030307030c2402130503010501050105071713080304030b01060806090103020d1401020d02040605031e06 87
    0x410344507070301160700d5040030301d20605040d00d840751040092500d010f010301c180f0107800c949035164074010425180040c0f42d48080c0c1d0079000300e01480b0105540300304035400307171205080481903a101c008045503260002c0d0b0010b00500e40114001c10050f80c400d0085004a00455003403120545408003a0400c1c4000d0310b684014001210710220014404e4001b1100c000b5910195018091b60f00b4400c2c00403040844100c0f42c02c1002004c82040e850036205443c00d46030240c1c002e5041a0195901400c00748415401501c480d0700da80d41003880c03600c0c00841705000c15000900b5901c40c280c00c9009100c00c10140583d82c400d5080030004501c03940304400340c07418981c0040d260046a0020080c3c80720310360240c801c010117680c560b640404d00c40d90410080009500c80d08840b0768540c502000240140c0c40503128030310401025004101507a100300d11328801c140c008084201c460b10780d039100ca00a1049440d021003050010070000344480e00440558414507062981c42003c401506200403c40c4007110b02c141e1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 525392212 1250 525390962 525390989
    0x60117010e040f06020d060801090c060206040b040b0a0b100201050a0c02030f07031b0210050d0501050406180c0c0c06020c1f1e09081c030b0306060102100902060909040507031b 78
    0x2107103003100c1d1030f02d4181c0a00703001460a4690f0071110305961381c0c0e410410f50b682d100c0701e40100300b0510900400c0141181c0c8043c021031b0415603200c508030b120140c000350090300d0703034408110b40d45201d40c4288228107004003000e40c6131844d900064041c0908680c0054168a041c07684043e047c004011203403010a40b48000c0c1c501901942c0654100d0448a441001e105480100d2001a00e4050596821800540302c0b2030325440c0541100b416140d05800c0203005038241f5008224040191140c010840c0400c10041003050300803a0880b024244004098154042d80c02c0009559130040b41851a451040c0d440c40326a20500c41e410005110b44241900001c031480b1003084248160603101d0000186c81c40c04114065507060075501c2e140042101c14042c0f09080800900140c05210303400550405a0152100349003060000c0e40360301c0300840c0c00986a13145d804c22011581e8204c1110a10a00204226002c0c189410007596135030b018002102c03400320f52203008000b8030360720326040101c1c1c404104540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 525393462 1250 525392212 525392221
    0x120f06090a05070e010507030e0a0b041509080d0503070203090915041a1f0207030602210a140f0a0b040f0605010e1206060d150c0e0f0406081905031b06060117010e 72
    0x180c0c1b65010417001c6e0100110703a4001030b056940c9164030402402603d41c90740e100e50428043e441c842d448803482c041401f80440040007d0034000c104020700c02c68034249140c481d900d08030281e0441c8152055643d00046e0300c8100b00c140010216012030350308090742c00300007024030b148168080e01c0c1381900c001d90148840c021020100010707c2d52110742d011a20649040303955030398482d4240d810015146072015007101044864540d0000c156a1000c90355100f840024880910b003164070b04040d007013034007181c0410000307414800907030090040d586000d401000383c0d40a1401031300c000d000e01d015840c0003c030b076600759403914504101749403100f0610202904c040c3d01c541c420000d4281d405001151060180c0c0801865503100380714410200c103890300c40c44050080d90341040100300c0c1c00745141380319a16081040c0a501c3d80003c10107401c90760351203840406226400d18a16501484270802a41c82c203012014610607400b09221340100000c0c1c83e0407030300c030001802e1000051402d008150308240700c4800036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 525394712 1250 525393462 525393467
    0x70909020a030f03021e0601030b10030308151207031b09061a0a02010f0204060c120906020706051c0615120506010c03030f140c1209010c0801051302120f06090a05070e01 75
    0x1503c0e43d100740120b84000712042607002e4606569140d40e0503540100004000b4420b1014035217500c00c404005d90b02d002d601390f690203081c508020303024459103010340c41110004e841d20041c40303c0783c00c44102210300c2a41e0304e15000c0189061100b0803845040441000610059207010b04e10580b09044100e01c215604100c10b80f1542c0c220541000c1159210721120368040703980d10060010745882e0b81e07558024101e604100e00e540754080c040c04100030143d00200300b03050b0302042071000c0d100e862504070b076100c11704400c40030f04103010110f4000386850708000003141140e2428500c8001c500d43c60b4088000d13640400c1170304403241100c1d06400b2900783d90410300000d102e40c3c08007090003540315001a5000700001480508031088908030100640000e480b0301c610800840e50b6841071041c4028411801c140300f00815490b01846002d000e01c920511901041c0780980607511120740310403501815280c144200c442c0c2d81d0003550160b0259925402089004c1c2050084922403503841c2c403680803511058004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 525395962 1250 525394712 525394733
    0x10e06090a120c0602030a050612120405010c020a03050708011b11070e06010c05370203150402030a051c030e1c081806090c10020d0e0603100503010518070909020a03 73
    0x604202d0103803460f20015980b84055405000e0824000860b0302c1c00d01d0900c425058040c18030182a07000302e003412181802081210290384080c03901644074100c920201d0030b01880380d0801007440c02103142c0454400e0055000030740380c40074510a15044c54000d041518064240030907581980c010880c107100300c1c01d00e0301c10150059010703d840d9221942a0312140d00745001511107400702038a400002c1604103042c2c44600302d88030189109221901e255000039501d1044890030304540c1d20300300c001415941c041c8407404c3c03015040001d9446401c9030507819001e001141c115100030911304095005103c200242210741c42c442a8000085c08016107c1a0760a00780100b40d0941d021403401c8050544400b40641e40c040e48601c0c00070524020000c2c10064030b002441c03403a000b10741c40f0352204055954010790070b90891100341c3c2e0584d40c90322200b891100c00c01070364001e1b9030150300b001c0a0011207080c0241c803804c94800d410545003040d8440d45030406968103a200a54801045c8009002142a8404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 525397212 1250 525395962 525395993
    0x303020304090c0903123207121b140d1e0809190602341401090c061707050406140d060819110f090a023702010e06090a 53
    0x1420004c4950380c1c2c1c1c4807050041460b03a0a00021003500d81c1b030300821040c0796244000c8520802403110a81d515203681d070b1300d0040d4580980310900c8011a082082d00618240003101154009011003440a0070b050080511a2505407034620a0340c0d02031000c1c600c280038040d0300320344400710045c0003809910112842100540403000c14044c00501c4040c801415280380c0c9458482d960160312400c0640441030703805c000b42c0180c034841a0a081c5a4214040ca5a98003011644601e00514000c0d141803980e006208014004082031050b8801103286c503002401d07040c41d41b450720300850603503440c00700484950007148203140229809141c0f2505445103070001d410041c18030800007c40f507643d00686464079240202031030210780005e1402003449184d00401c06540c03419030312407151342110030100e0001c00004140303040c0b01e070740401d03000d00c110800c142540781c1082210403841c60425001e5250380c400c5080f00d64001541c6007000080400c8808a00a40716011450160840100d607464a40c9800c1c1c0005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 525398462 1250 525397212 525397217
    0x70605060f061908010801020a1707050c071202030607020c3d08010609080601050609040f0e100f0e01052a1204121205060906130204090e03030702070506040303020304090c 76
    0x40103a603242c485001600c0302a40c0440307100d2901840750000341913820107070000d100381c1e40100040f502240d04800d0b401411100c003d030001c90b41d0b41d0716900320350034081c40300d9891550192031000101c0e10b50444035a80301c1c1c1d00172010349451380c40d00c44040c3e13641c0b200d020040c0d4004c00881a0500e44100c0e1a150184140028644042382c242ca00c409103501082c984015012032200c8005105c060750080d058000380c000344004183d1075050500103400e50003600c406074480d540321640600c50040d00c0c0c012031b06000d018401c60b031140d00d8003141e11002c0d000d880b411a0a0510b004000a025541402241d0280c1400883e00d072588990703c2d0304102c01c10b4144d0110114880410188000086401c13140b4031503401070908150a54000c00005d002c0c8404409120104e410081401015500d41541980224040f00c07111051500300c129040a402254460301c5414030f003100d40f40001700080300951040c5501c0c1d00780e40126403600c0401459004500002d401644188000d0040b0320140e4032074505280c40c2d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 525399712 1250 525398462 525398479
    0x16060c0b071b0f050f060106020d30050f0106030e031e0c011506180b04061d042403110103050f0a0e01180503070303110307140706021b1609090807060506 68
    0x20f4481480580c04140119581d0307001018a02400c10240402405008244040e1504000801c0010300e03401c4542c0d03c100e0040c6007036102142005401c180d000014510b00c2051259280005905c0c100800c2407007400c002c00c0c1070039041a00ca100c0401260818000301c2041c1c1c07404000c0084102ca00c0d00f01c0e42034040e4966a03050103540c3c401c0c82029500080005503aa40e030b0155005082200984c5103900c0070289407801e00c018030106401c2400300740004180c2000f0081001c0020004028100082e00541320501109c80d0b82e00340d104c5d54590030262030143c01003148403c0d031180110b00f121000c4410302c043d1796880d804207109250303980241482c51111000403a08002e404024540410400011640e40e440098806c0805405019201031001c12042490a62900d003002800803000710120201d14240041d848003040410f40c16540c0e03100e8101401c00350074441803082e50752165010280d40c000b004c80d030000a500100b60141c0c0d0400d035031080c0c4e41c0d07040c20025519074004d40300240801d940040748 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 525400962 1250 525399712 525399767
    0xc0114031e040c1a070b01061809110a0e0a031a04050313062705090118060f0902120901020f09060901030b1302130e24060d0e16060c0b07 61
    0xa085100380914042c450803d0b0b45458036514a404240100c14660a02c2080c810303140803030f104c1c88a42d4111502400c000c0c450182c2030b00d00c030700f1110240c0c06c00c1c0300103440d100041c2030740003052015048082d09a1224150010380c002000b40c1e4003118480140503580250302503042810703585c0b040360410710a0702168180300c8410b200304003425440d009400041d4041c1600c00f016800c0d00c42d00030f031502e4540d10756210320781841c0104d5041001406007444200d011460b0281602042c1d002c4002084000c51680c212521181d101e0080d41c40100305440c03a4002502048075402c041c4200c80d40300c0c14002e0702ca844c1090710700c02d0041d541c000c29000b5051503500d8462440c0351320b507a2940090190440001030351800d0403a81d40c1b01d0004650010b0300c481c4620b008220401403080150901200c40b08102c400c103d2080000661511482c078051010a007080000f412510000071318480c00b8148c408400686525880700b05d8000300f0300314003d080541c00c5800304100c5ca01524482c950103c1858040d59240103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 525402212 1250 525400962 525401011
    0x50a0503070605191e020a050409050112033c14070f0528080322080d20190504050607050a06050c0705330406050601030e0c011403 58
    0x4018401c0d100d440e194800c101c00203031136102c00d00380c0303c000c40310422003820010012920880d2040107500c40721781c0098a006818000c40544000706070070380003403016607140c00c0c0d104150b0b081444101e0202c6c0924020181c03119601d002c004141d096503140c0301684e0039007110f0401503141054a40309008110640600b6161200c0050440303a00a401a41081c8004e181191800300640c818000a4031090205140c41081d40f02c600211900036000544076181c241d58442e801c0c1c101c046480b64400c08200410401002c100600b07595060301c0010803524a02c3d15074081603040020081c9510b80c002c110110345110004283d60825040f450b0032410551180c000c51103990028000791401d5010070074030300410886005082d840010306207914109942641c44641d1284003006c0f01c002c1107903102e40c4a0078030400c40c1c440ea1042401c01354490840c2002d0814800800099607180d00181c01c243c6051800e20002031201e402e400c06945030b021a80e04241e80084581000e0101c522900404900340f0f091031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 525403462 1250 525402212 525402217
    0x7021b012c0f0405010f05060d060806070210060e0411121510090b06091c060b1c2306011403210a020601090b03030706050402030a02030106080c1908070b07050a0503 73
    0x440d501c184012030004401081014459010320310701c10342c181001400410394819808044070002c0c1ca80541b40c21100e400705000d4a42900080164841c12041085035175002401c2e0714001c078081000c0144644542d080b0b41800d008480103401016440c00704511400d240702c540340b0410000d010740d42c51000c0185441550003040d901112035444225060040204d03d210314002c004c8200c5619241800e031801040071650b0a000e81030741803445501402c24825550099800c07140b004101034460319070203d2400311100c0b0303a03c05960041781d9005d8a004203d100030b06021100c07000e0b0003007046070f1170700c29181060300e85c1501c165098014900248140d18031140390001a0020030309840d19808402c0d0024a0004c05a0003800c419081150320541902c020048401007500f0810218403030381c880c000f082c130f440c19460009406612b4070070005a0504003182c840102202141c180040902e001d440c0340502000f4012004150001c04e4108000c2c94041c1c0101050b522034010380e81304480646800d070954 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 525404712 1250 525403462 525403517
    0x9010b0c2406010e0d0b070804060f020c1c031515080702070b070602030402010e13060302040b1e04090218090d2613020109080304090e0c01030507021b01 68
    0x190022400103040d8105001403200300703124224148401c0c00010000c0c4800402a051605101c0e8182075001c20380c031617400a1008036040300300210b103070400e1003005125003400c803401c2c1c400c0c9141c40c880072880c080a00842d40031050040003003403094001d11010700104008104082030642d6426060f59445482100030020041003400c12400088201c016000d400028800384c21500811414004034841e40103949410b508034100584076034941c401030b26040d404c00c0352a503112990040c0583c981455406c41d83c1130b02e10a850910004240e80f0503c001c200c13020000b5490100b8480c11036083c3e0400c6e41c00540c120340000c0201100c1e2000d2059444405400e550714a881d8001528010100f9006019583c04580c00c5000c1c0a00650320f9809202a94000e044880a0940c4080540c03d6a1054280c1e10203491040152550b0300e80c2c0318046402448aa47c00903094000d10629507003640c000d1140700c1c4100015009020f00303c0316042040c518039001c00b03d1030b0503c4103100081c000c00d098044a200390 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 525405962 1250 525404712 525404729
    0x703060207050705090c0d1a0a1e0b131e09090b090607080103080a030209040e1002070201020105010f050906090910060608040203060f10091a1f1e0504030305070f020901 75
    0xa81c0424200241810000d410080c003810035001401300031a01e0b101220b81012904100041c100d43d8600800c500c04044001d041c0e0024401c40c001c121020a60010702284201c0e02ca80240c440e91800403d40c240140006480401c4e0400010004203103001c20050500340510b402c2100079031a901c081d422181c81e5030044d646920190108104800100f1005800c0340c45030800c2d2a8961442d80c2d408a80d00c100d111450030150089802d04d03554641d500325480c1c08003140142c800c40120301000304020b4000c1e05003a4019803c0000000707000c0e404012400543e0009041200d2660381d43e024403c03a0716004c0c1c034018a81c4244800300301c2c507100c24850032018000c140d90b0065241400e00405140c82d0000e01b8003840d811004c0148550344120301380e1041107030304d20b03c00030a2001c10104150354442506801581003110003141e00050354024916034504500e03610350b042040300340314440b90085407034275050010031b0b0108001e10209000c0c1c405040214440d1003d9001400c0546c04240009130a9204410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 525407212 1250 525405962 525405967
    0x3020303070b160e0603060f0d1203050a060e06030c01050a020a140304030623061002030f070c0504060b040f050f0a03060c022d0618070e070e01020c0906030d031a0307030602 77
    0x1912001000780c011100c3c500c0c5045000302e0113034000603043d40b1000e400030780304042a0407009510b0f00c802750012083c3c2c0d000610039650340c28002005d40901350440b503404a4500c2c201010030303070f0803e1015442c0290800380003401c4141c00d1f80019129075100d89011002d43c42081c0c007685c0040c0e1181c2e2900c620000e0b0074003a54550b40365243c0002138a146070032003c244961070040600c5021801c6485911510888480341035040d19003041e801d6200700c4809403c041000035000092010f40c60709601100c00503030341040729030b03615480d103030060055000c0e41ca0030203103004007002545025a08200588001881c03c0300e125500e85d110b100301c55400c466000036030441254500c1510514105c0c200b1414281c640c10602d220303030408591910001803285502e038508140018034044104074850140002c0100718609040c06039002e0801540010b0560041c8144401d403009420568512070150001400600c090302905134240d025020404076042400b0000340f900c4520303030b400c216500055005a10042c1d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 525408462 1250 525407212 525407221
    0x5180f0c1003020a08041b05030d0c1e08120a1d0604061518050c0d020c3f0307030e011104031e050a02210a030e0111010c080114030703020303070b 65
    0x11a11a06032421402c0c14414000c40c02c0d4030750010503c0703501c9980100c4a641d802500e130792103480c240e459042681c0500c2041b00c0400c0980e0000040f00410b405082c0402c2d09100d0f5080e0303480344480c4124010300c1d201c4140b10f00b00c0c00c58401d0b840c0c0d41d004540703107801144a101300d1005014046070302c0008d1940780e0100c1c080c4020b01050744200c80c2900031902581094604004106110b0703840c2006280d407440d550340000794290381071000c3d11001e44000f075056542d9038550510355074411480c1030b01c80c2e0020743c00514500411036030b000b4980102d87c08940c222800c8205c200320090760801030443c0c041c10307201c94803960a55020721032030003041000403100e926142103003044108092a0008611a06002c60800c4081000000c4140b0308690440c0d0452000442205c4011085240c00c000c891a22175681c440381010741002c03241c41c207100280d03140001800d45200707150a03655401d99080210700b00718010301c00b40c0d04450144000300340140440300c2680e62940801d1466101610690340001d601043c407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 525409712 1250 525408462 525408469
    0xc213f02210d0b0316050607020609190503100b0109060804020f090115090501030b1e0a1a180102012a03020c0303010b0712020703030206281805010605040c08040605180f0c 76
    0x2900c3d450001c0c1d00400780071800281800e007000d010b0049070701c2480080b442c0d81c00c5640300d0045030b40400002e40000e8420003014800c802040441c06558442d00038001040035115845c82000280d01c41655190351580ca048d80503070b1a21000790069800011040146036a911054003080c02003510848000d0010800d850041000a40e600315504041c2000c0200308603548107241803140054148914408070681c07800101d005404d54003201404411100411b9a890044040c00d052045020628844150ba00049007204d8050303140890005110843c2a2680031030021000e458086040c0180f8250407440c08526640091340010800d02000072541c003000320a90300d0280c008410300080c0003444c15980c001c7c1d1122401060307880c0881c03220440311110041c41c00300c056a070100b40801c000120a190054266410741081914a503003001c0d00000c1c0c50074203108010011a1315960b04203285c589545a030007034480500942511900c0301c2042c040c8100600100c42020340341c1000b021040d11441c00d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 525410962 1250 525409712 525409721
    0x30325020705010206040803060a03020d060e0106050a0e15131415060705150702120f0a14091309060603020a0e1602070f030f0c213f02210d 62
    0x1600219003058404102036600012515003082c4e01440b00c1d030b03c0340d071074201203070100c0c2c200da001070350026030a1108014051542d00c000d4810301d01400070300240d500c0d0f905202101348d1620505c4075040307115002800b41c900c0006d071028209401807041281c0311200020006581100c100d00c0341003000e190034000714410251030000380c8442a07424906055442c1c5030b1503111418103510f031641c003110500082d035462090000100524112420a444490701591000580c1000551602165094070340d601d5941e4402e0176280e20050007480124603815004090703014000c07a42049818035159100800141d82d40380c4160003804405038104014641120301d007654800c204071a60035500582000d001c03000900e000c1100f44e03500a2440640c00125213010802011700760f00c1842403060f000031038603145184d80042d0f21a1401040d404540105400200d000062544810704c201d50a000000302d0811050f501c00340603140d2801564022009000c003c04403540d2030308071b0350104000091021b8610524400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 525412212 1250 525410962 525411031
    0x100e06030c061e0d0f0e010b0a180c12090b191a09060d0c0842060604080303070c20010903031d040213030507210809010905030303 58
    0x7001804544008039840d480b800d080e0344500e02103625001c10300c003c10070840e020004115801c01c02d903280c00501d04010805404000300740e501b04a011a03070741c0380a04440c41510b080b84900c1c080c81b43e519218800400201e00c102c418030001813010034080c403031407040b46504c6001700f59a610a16040085900d007480e01c140515901c1d180040f4070307114002203640c0c0340c0980c030141c401c802503403101070000c2c115101c40b81c001058081c0038000424581c50100d55900c5a880d4a48040c0c0c85690300b030f040714150100c417280f81059000e04000b60641d074851400080e0024400340c0468a41602c9900d200e065600071a1000007042d0307000c4151040241c801e5100781600110420b0340e0602c00702d100001c10500113440090100b01000c95025048400ca04a4107480e0f50004d000b1903071544459000c0c0d02061b050311040da00380c081c203140001d000508095802580c05100300005034403400d41d40d10341e42d64100b05403840c100018600003103401d4a01f0001540101c1c10030714002403611035130314540d60919000e030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 525413462 1250 525412212 525412219
    0x1703070818070909080f070f0b060607050316020d0203060a0b1318030c0212072403020a080703021815090906100219170a0f0807093803100e06 63
    0xc66212180e0301044440545010143c0410401a00c0c10010800d002e909413035411401c2c00116001005039007002d0072455442000d145c4c10b29502c00c0704000041c0148140600103400c2041041103d0030040c05a0003000d10040601500c0c500580200b8507100089548002d03a66a03880700e2072862608070051500e44075001400e008a00203c0704160072084d030994000c0600c00300c407811a04565512080214083d0500c046611a40e0340b0924040060140e545020003080c00c0c013400c2c0079042c480d000311f4286070050307242c5070582e855108044000354003210398134412a0200c4800c000316502c44214160b08280c03a803501e5203403140f01007084481c010240100d84504080700810510f150041800b45000c8104036000b242c03d030b000e003090702e807411040b000107441007070006034a0f500a07084041c0c4182c009031941c0701c40300c6507070b4450151a041c440e070140d08443d0281070b50900a80c0c60301101c20140c8100080f5542c81400900c440d031001d130b0410f9951a0840e5200f0780144442d490000c12650b009400301c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 525414712 1250 525413462 525413491
    0xa05100501121d0105070e12030301050108281a01021c120908040308030a020319060f092406121404110402070302120d050612060601090b1617030708 66
    0x180500c0030391000142d1031519840c0c002881d4010104088441c441500207101501c1c00a2004040300c4d07214100724413404000381c40582ca0280041a00c0c1aa84180c4403003426886040080c100991400e440010202e0b0341ca508100340c2d0924050f0825003402c4025440151f19484006070904103941c2c0032031206180c610542000e50742c80040c0801207200400005580320050521281600c01d58002808100c400020b05c4828041d590040d48183c4580d401035648546800c1c4880c01d0b11618840d80007c0c0c654414140318100c07aa600000000821090400c018081c50315a00d018004581c80707800469030301140081d800b0030381d0042c10007002e1141d035040304a291560300c0210b5111004e08140c00340f035002c50302d80304050080103240e841045100c0d40c2c80e00c1d10086000c010103814121040c5004414a42134066001d0000031118000d1505031200100c007407c100803040c641d04a0302d01d07040c0c40c41500d002000400c107060f40080103440c1f81c4060b60307900c0c948810054200d2030007400c241c0031016a07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 525415962 1250 525414712 525414719
    0x509010609150e4f1a0c070c030b0f090703030512330a1502120f0408060109090203010f06031e021c0302012f0f0d0603060e0303070e030f0c0d140a03080a0510 70
    0x40083e0000640c50207080c241254686c9011600706018500c0700074500c0e0804100031091200700f4080364841c0c0e64003903080c07400342d684851080c0c0b40c4034640300c0140416002d102c100d0b00c000740c041000d603118004003c038825030200489007440070340791945a42044170a501d209182420450000740151400f1203166008111a00d4001d681d41c400030000e114012000c10248586122070f1b041350001c107402000c48445503110b1018500030a40404201c2c400e610b0116134200d414090300800044a40008140000085014620b0035000e00f00d102280d000c1c0084900080c1c815003c441909800d00030350000455160403e031150780c0600801440c2c00360341e204040e0a015510840460703402e1040811040d403100810056400645055000100014105400c12900040002c00740d44141429a54200094401400c4c5a00c0b1200285007041c950000000c0d4a01d41c10003155603540148602940000e0984503d4041c0c1800c8001408900041180051144003201c41c010301d60018910120304103a6480d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 525417212 1250 525415962 525415973
    0x6060a0207170f0f0f190201080a0b031507110f06010e060d1a150f0405013008070c032006030115110703060509010609150e4f 56
    0x80342d11881c0011041c50000101408003840904003000c0b4400868202c0001c9501a0b40c4034608140095214801d00000300c99110414109201c025010713112013400d0745951008d240541000700c0701507094441c0c100246440810807425a12400710b50341c85440100919049508115101442e0b01495109000500100000340d1056801a108407170044485030a46030040a015540c0d484100407016801084801d42c043c42c40e075100d40d1000c940d020300700f110100400c03040f0384081c050148100703e801da94550070034110441910a00c1c41a88203591600309980d50104c41e84a0321044a000070b2603542041005075000000100078032000f6040d50150086001c03907024081445a0f00e94014828020401a0b008815506c0c2000c0c4803000c0d65252922421704402900007a0b40c640d14640c40c1c07240008141940d4881c180c94100e0107841218000d01d1b1441c0030649800161014032100380c403200c4e5250703d01c07400540c4620100b00b83e440303c50003081c8800642040d003554440000e8000544c0300c4400064 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 525418462 1250 525417212 525417223
    0x525090515040b0a090c02060a0f020307140c01060503010f0209091e071b0203060702010c080a11270603010e060a060f080601030507110a030e041a0102060c0a05090d06090b06060a02 80
    0x1201614001840c083c4000025051101503219001142c64030030a040040c0d0b02089403441000254024080b9041c0310a081d0201d2204458980002ea08000c420544e41182e4005000600340200003080341d0b501c403000642124000c202e211195940010440d500c1c0c20a042c0b0564400b04002540d1462180c4045081c11008010702c0b54082200242d04140840541c10340d1081407a009400c5410070700d40075502034001d000502c402c001007100e110004141d00141d025290000e40d1862203242003511010251352500e402003120b0740d0301420010148000d07142c1c5030280d8024203c07400d0061342c605144090040c0090b0343c2e0041400c0180c401d0f110b064640e04041e44640083e820b290006070f590320740c0340c200e418903400710703c0c1c64943c05580020001d060740040740b103107a83c2040b60704004c2000300e9055250000c1030f26111341d016070003038000103150845d0507002d8018001c00d4240540303030000c01e80008800c88100c44040f1242070343e8016a006200410850302c2d03000e407041c0c900502d0103507800b80103595036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 525419712 1250 525418462 525418501
    0x403050a0e0a350c0f27240303070b0c0912030a030606020c032122030623010503072108070308160507030905040f0905250905 56
    0x28403080c45076207440c0c288000400314641a141c3c3c1d141910741d82c400e4918002c2d82010748021200640c025003030041214105140020702c2e4002d44d980b018140101681c4841c41c442c10700140659181d0f8504a540c1e6061150740380381001e400c00720301120301402d108a1808603601030b5006200010002d0b828010954100c444941b03a5a00c03103d80c0f00c006a03003900d049a92103000d0101181004600d034250700b008050341c4c415000d403181d401448090590350751105c180800c0300790b15034401c3c0790400c40e014002c1002041d0017000005c049006030882900441e80e900c101e4007a6640c45542c0c3d510282c2c81188100d034019417105182552614002980e2906603004031240e1844030003601e035031140300d043c01c190025807104445844c5c0c485030402401481d41100d440c41440c0c00d42c1e0500c0303488c0d84581d0844541641c10744900709484c3c00d050512006121040310182138503642c01e0701202083c010451314200f0b5408104056425030030ba005141e0040381c40e84110541d500700028001080c16500144405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 525420962 1250 525419712 525419717
    0x30c110a030e1e0108070e0f13290609040b19060f14090102100c0203071a0703060503190605070c080c010c0f0504050307030b071403010609090506010e0d0b040303021e0417060403050a 81
    0x10045208000703540c1b0089123107881d0384030448604048221402d9000081c01c000140140e00d01501ca01c6d01c0c80040e842500021070380000c0070000c0b4055483c1ca40d2207403100c0700016242024928911146021070380c00ca0300500042541b04211200c0d81d64021818150943d9440d03410381000c900d000080d59440c503502070642c940b51541c0b6001a140e1007042504e8015422880d080c00318001c2c910210018641900d02c5000a4203000c000300712810300050040c1401050303440b40384840305d10385968000700342c05003a110802c268001c100c4040360b1301ca40901120328000000049098400130064050400320b0031407000d010f01400100000c1d43c012801d042100d82101a00e0701c01d64990004540c81600304c94102c807284004070000c00c030780c0d40c40440319003502e810700b80401c02a203032840191507a1420b182c10070360005491410b400010000040b00c1d03003191113810050f0800500030740b1100202d4500c0440f0001401c0070804210140320300218a54504d0000041c10082c03c160300c00804512845410009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 525422212 1250 525420962 525420977
    0x6120f020907050c010606052503050304080c1011030a0518031c020d240b09060a20030a1106010b070305040510050913062603040501030c110a030e1e010807 69
    0x40c800e0290f811280981d20a600812070180c8408014001c0e800030f0000311011142407242c15007416014032049009a0940c51701421a512a62010255485468500138600070309e144404011701902030143d85001000340c00344c41c0d10303195800c10210740008040e850001c540020b01c814075039022080702d400740a800c1c140070310103034000010030291264101042186144c44007000c5454000e1090059882c5201c000b00c0a03107980b1406090b480c098a000154000d02c10002e0154550086000b166485044c00c10400c101000d00c844e6419074000c0c00c44000464041c20028038129801c5c420079001d040d0082d641410100541c80c000d1003400790b401914040d6141c0300c400c01d40d09014001b0b5031007007040101b0400240440f049114007610745c1c0d203c0c069001c0400681325001c00420300c0341441e12002c640c010340c02c0c0b915040c0118040d046191061082c0880c1c0c0f00700036501c4c80140000030405000740c48031540011504c0501c445a504181502c8442d07400d90300c19180c1c0ea92004123640c1110710342c54101c0c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 525423462 1250 525422212 525422221
    0x507051b120d06030302060f10050f0f0a0806090f150117030c250503011802040510170a03020610030f170c010e0c1306030317040807020a061206120f0209 68
    0x24a02020786440d2042050702044555800c44180c1010302a04c0c4694259016920351b1f00d080441844191003154001640c4502403004c0d0034404441205034500030001c4240d40c03802808200d070300300c154200b00c03031315084042007208410042259003540b0040d880104446400c04281c00811841801000d03584102504151401320040041d01c0c01e000300d80050303034204064030a103c1c01c52220241e540300108500d0000062610341885a5145080c03e950f600c02e142e01da683c00c000c01014000d154160312031230002d000c1001e05944040e409800840c41c010410b480b8281000382c130b04a00184100741c0000011000c0c0002800c20034040c40c034950106414084030072580ca01100da0251100c3c0c03080b15842d04d200d40701c9540d0001000c84140d803050b0742840200c941640c20b00144e41c0180006004a8100070743ca04010294100556105009145240c1000241d40c00107008083c02e6110303a001901201d880342c00412a807003000014000e558a0310601c10883d23032420b098041d40c45010740b14080100c00034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 525424712 1250 525423462 525423517
    0xa14090c030a060b0f0706050f07050307030c050c030f0702090f04020d060e031213030905030f03120603010e03031f0807030209060f0301061e06140406050301031403040b030f01051201050705 84
    0x700580380c1e000342c1585819951500e0b07a8286c201c41c0e4199540c906141c0803c41d1a482c1c80030381c5006040590360307140b442c0e03245e4070700f9000361510f240600c04000040040009100c0e00b40044c043d600003109505030b40d0740c141d0042001101d006002003180d40c99802c04e200c0160381d03082140c08442d40c004000b25680219600050550182d40103c000a12261007045803c0c0c1300b40c1d000780102842500c4a00629880d0414155207070070003042000664410070101c0d000c5003070080043d0b80801c000380003040d25028076085c0b900703640007940c154603004c8036516001c0030701411001d040d0103002504007c0610034036680009154040180c82c441c0101a0102c1010325030303d081d00010003404100d00c41582d4480c0f900700b0002160014410139000444541402d0b52101c8208110b4084030700381d40d101821039003551190034a404600c40c034000349220801c000110503042d000510301c2040003000c812282c0d071601c028441030042c0d40307a45080c264500710402c06100c0d002816628421800d583d903441c0c000503014034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 525425962 1250 525424712 525424721
    0x1d060d0311210a0201050a0b0102060105010e120a03020c10020a08031519062f060106080619350607050d0e0106080606040b19180b100e0a14090c030a 66
    0x200b061481d01444540d11040c2e00d4004010407691a4001c001c1e80c0e485451250403901c80940103801600308100401256110f0840d0042180c0021b11951000c015100300c14580703080b00c48103c0143e0801d0212800500c0c00641e40b80c3d21480c54000b404902c0046c1d51003592601c0010a004100d900d240580c0415441d0700f6103000d105175081c46030980307070760f106d41014124a0800e034211080380b121043c1e00c7c00e00c0f61818607489590b00c0310802824681d00302481615100401030600d13404c01c09040038a0a076600c030800303890061001ca080d241540007c1d800c44010000c5607804a64079007452800300052220000d01164400040c0c80d0403a00c40c0400304002d000341a01d01c4080b965982880004151028003140240c000c0000301d81c1008030303130b49040901040001c540404c01040d4401e841c20011a41030f0407015407441288140040c403d0200c400240d581d5801004140000d00040103000a50a211651001528419040c1c1e101d0b01030600c0000e203c3d24008069013a0f115010011500341d0050703820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 525427212 1250 525425962 525425983
    0x109110403080a12051f14060903030d0506030709020f0901080403030609090503041e050904060207030215010303050c100209060f07051009080c010c0306060e0402070c030b010f1d060d0311 83
    0x100c40c1da441030712510060800081c440c5500700c40b403a00006c284d610b6a4103800c0010b1040010a509035503203040d0a4180704843d0340041074101c00100700ca18480e81d0240003c001e9030210010005841c00d04400345407a0072010740010031076501c10804245c3c240050020f0390b90322003003403070003040541c0c0700d15046010341101c1c0d000f844014285980b420400c2800720142c415a030141c0d80e1010b4070410300140b42d1040c074003445040e42002d145400b140c04241150001e11920b0701a0040726100e050241d601006913400764410f070000345020a00401201044c0000c217801b071002d420035030911491390300050b075a01c5120a40280100c0010f091001c2000034004115500902d035070400ca0427034103081018466210800000701546840500310445010740700341c60030b540c020359550502c041113209000080d4032400095039a20002d8000000103411651124041d120803d0841d140c98a050780098500003110515415080040200301081e1180824075008942500c0d000d681010740d5103485040c03040c0c500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 525428462 1250 525427212 525427223
    0x904020a030b18070b091e06161a0112020f030c1516140c2403040201030905030706110c010b0306090a121b0c030209010602011a1002010f0e100c050c03030109110403 73
    0xc000407120840320141c00c02a0b0195115030f2030301007070400180b000000740c03102603000409100c4203289d040c06001030724030b540c81030070040345942851a400b0000b1030240c2c801e400c1070058030700d544110b08000401d0301c407401080d4018004404600c0008001205003036460340b950030040340c9000d60003011212004086c0d00007a40001c4140c0c01102c042c0c1320300741c1e074080c0f80c050040c81d610242200d00005c071b00440500300108050643e02d4a071f0044015002d61201034500d0301c014885240442c40b24400c005820b250f89403001d5480044400d00c0303082d00e62005400d44640c11420030019540004549510b90b0756000440c400e50502e0804d0580720030030324141e8140c04401407d15441040307030041088040e81c0c000c40f51012a0b0f84e07100012401d031000b40d0840b0705000c03c440c100c1c0d0320707604101c0050721106100d4000801c480c41c100400c00103e071903603580310032554055081503d4018461003140032100c2d60b072410f50300d01070300103640030741c0c2e840180703c1c9080c0d540d030b5008a00d060b940d030031003a20081d641c0803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 525429712 1250 525428462 525428473
    0x20c0c150313060b010228050c010f020606010e0409060f0b0406080106030f082101030807211d130c05090a06080106050f1e03010602011509050601140d0f1b0206060904020a030b18 79
    0x1d02000c004050141c0007108c052280000d800401d600403505105089040d0f40280f0740c0d40d0300c0c01d0044500c1640f00019a0700503403215800030008009000740c04071028250800540c9000060411054500c03e40c00f60703031640d242001c24008100c0d04403070403400035003041095949126201034541c003440703000384040c030003090040040304004508006007510b078082d103148148550030186007145040c400302444086803900c12010040008200c0c80745c5010001070031008101c1040e14158240c43c1d00743c00a0001600c0010000402d140141d8400080e0001745009440f81d810100064103d2240600603c2260b4010924143d00030020101660300b0511400c203035187d59441d0f4020740030b04104001c6202e0860702d120003040c20302e001d100301031041105960b80103104100b601d040f1615400a0018803ca03900c0b80c80d1509080340b54007884085844207411035880341c240220003410640e0107400c0611910300c0b5003c4c4030140e640c0a0016003582d4000c052400303940c035655200c2566100d400711140c05c60060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 525430962 1250 525429712 525429763
    0x605070c080a080a021002160b040f24060e0c040314160605090f1e0d081b0d08010e2401020307020301050a0203010812040302090a051009020c0c150313060b0102 71
    0x20f40e030181285034895000c46110280c21207840c000e81c081e102c030035420f80740206003003000b141701c903540588c00c240031710f049591001603501d80d0007000c20b407140044203503441c0d80900b240c440c4072407140c40002c002d03840d1002c803181840301400d507052117a4803000d005c00316180c1d800c5000000074000c1030400501d0f1212004643d5942e0b00c050650742000c1c104500c1041c0000f04a041410000c10003072140154102442d0703100752400400202540100b825a200b0809010305009104803410f100c0c440000750008212000c0d24480090050405070041c0443c1d50402d07052080001d03000340d030b8500c4204496611440b543c80380c1d00403440c502071003002030350540c200024460000c0940d8002c5059407003640543c0c4c40002c0311740c03801205104a02c00250882d54040009030b1038491076021030b8011600355650300c81c8030350312002041a40c01a104415181d0000f0700130180f28a441d1441384000200e0380c96007819071404c81007280e1a81c80156000c0c2201d41c6604101117140e109001141c101c5004645804e0740d00d84 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 525432212 1250 525430962 525430973
    0xe180f100903031a0f1309020901080709150b0a0f0c0803041b0f030812130b010914010f0b0922060905041203110301060e0112020a03050a1508070605070c080a 70
    0x107050070a0340881c0c500004a00d00f118061110481160060024001c1c4481ca405028607801000c42c0041640d50354140140140d880d4090b07240213102d500018440c5070b0500d00c02600b01c500310325040440d010041c00400000e13880c10181c80c0f40d1016800d212801c03050181d41905c0d442c0c04548000c180c0503001003000304001322804025004142c40c0c9a500855890740c0b130310940b40d500c9000141090750103202e581160160456003d078420a00344c043c076819a1165035807681c1100c223030460110b4075110070400c408030f144c80e0101801814600c200c056058542103125103103214102c901400707000c80782d12079010b078008074504004149941e2020403e00b45c0d0780c580f8500504060760110b9480c1c900c0f4600c8400c0c80e105e4040c0403060034000100ba4a141d00e809000c5c0d0302492200032460600c0036514494101503260300c050180c440058030302080303600c0c2540212086502c00309030142050079191060001010000c0c468041d076600e17003842a036440301d80c2840039242a0b13551000003e03200d0344180e10100300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 525433462 1250 525432212 525432221
    0xf0433090e0a110d05070f0201110708070507080a050a0303051e0a020d0b0a08010c03050108010626070b0d1407020f1e030405030a0602040810020301081b01110a0606050a0803040e180f10 82
    0x4555625040c5181447e00100c0c00d0b50b4558041c500d45c0c9106026401c040380ca01e6005125440c860b10858828684c4d0702400d9052181c03842c401c0c0c8081d000400c0e072000389500350050a501c21441012840d10391444140d400c0440c0021b1b0507108540e5001c101020540100e40c40020b81010082219500a90f80d0406038042d040e00c015040000b82040000144090140514002c3c1c1e0160340340036030607805502c40e0310720040e0101e0121140d84510700001404911503001456072100d641c8001c0307603aa0074000f4042200d00040d2400302103500050b44603d0701c0b5000b0601000000d001c00820491088001e0118614003850300040d5150090084240400c0240c1e40100200c0311040c1c21742d8450039005080307504031f0109214829460300200c03540c00c02ea02c0940064280d07460141420413089446144480c605034810100320303681969180d0500c5240390540e41c40c0c0041032003800540c60581802074052403003101610080c0040540d407859590702d1400c0c400040812009012034401c02030045082d80900b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 525434712 1250 525433462 525433471
    0x601110a1b0b0f03071812030c140c0d060c090b0c150105100c030f030906020706050a0605040b03100b0105090904152306150f0433090e0a110d05 64
    0x14901c4000c00985140b09005035101e103400d15103c582541c0c1d4200060b2202c01c42010740c8080301030074100100e81384001c00c0a407107031749010341d88205003080d461800320b60714003075030b00180c005078015454040315685030003d44003140e80c413a2021a00407406207080d00c400700355030880864001e02140a4141d158000741031a840300c00300381c0f854030310b0740e07190248481c522a100d80c00c00001c8242c10070601080c002e800c0f80b16801c00514001031204a90f03202e80040346c0014008980c1e007a214402c0c40348902d954010100a420304031010170482d200780c40081d81e204803500440700942e488018480541c3e0040c01611042100501898294603041c40c24100c84010044104240f518048000044085000d015070f000384001c5200603040d1500d80400c42c1e80c0710091142d2403e01c4e0200400210411003002030030082c9484403040805c0c039682e40c1126030308010f0b1a00c00a590540283c5006601c1d84422640d01f21050011014007a07222150248080c00c020501003008440c0025100e052502641c40a44030703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 525435962 1250 525434712 525434753
    0x204230906010e0105090f0411120f0606040515092a0409060f030c0605031305030417010b09090d11010b0405130b071103040b0d0f180c0806010503150601110a 70
    0x7540e807552884601e200080c010180c1041014001030300d0302d0602042603402a002c3c4083c0201503001600045441c000c1c1141c4040c40e8110b05c5e840240d00408015464010104440c1880740c0e1a190445500350302d15020450303c50303c1d44502040c2c0e1240380d01c1002072125030b0707850200c0c415403481c1d40020300355009100e140040740c6820000103a10030801d402e0801d42e640100c481e02054135090045420340c001401c1c1140b07a111124140000440c100000c02c0200104031020704104503185040d400c458000f0b4440e8001e060340801c101054501264040e607003005824003804098000d1506801850009070040c0c00a1070304082c000009010301d41251b81d1403141034515401c0e9110701e000c03100c104040c55050311580c428401842510130340c801400410703a135580c00003403103d2102209000e562a45011a0300301e4070a01e600002d010314401d461000e04405402400c0651401021956130b11000700758081040c0352601158403070703100e45c440700d00e0401524115440c03401d007030414010302c640c100320040d203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 525437212 1250 525435962 525435973
    0x15040905040203160e07031d0d08090705061e0307051209150901021309741c030815100c0209070201091407080c01030b09040f02042309 60
    0xf4104641c0a41c0820394040c0601200551211b4005030041c00707c11031401080c120000810402c10401c0102c607489201c0d540e41c0e08194102607070a14180801c1e03401c080d0041c4010031615007025050041480c1c2c00310f401c4802562070381c8504040b10030f0f0007828019014821800188a1010400111084072044920849030385489100404c2d00300e1198100c804550243c0c408100903000f09e55101d985c0241e0030020304841d106040c888584400b4181000140300391805001215900c071110a10310716400c6482c5003810401d00b11003000642d1079901e8080d4401d1800040025940c4499840010301c101c070002c8070100d00c0541c80c000d020404203c138114074035011110851164500152179030820707191501c54906104451302400b0300c46d0002800581990740b1001c600000400c4010124140402480a0440282409407544c10082c035181010304160412072449400da803241e1442d5042581300304c6c481c800181c2840807030064462035400d0f14442e003030b815500000c0d5403a003000c80c1c841c2d4480b1060703d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 525438462 1250 525437212 525437233
    0x2001020f0a120b2704150c050c01050f06130b010207181e05060607080702030312040f140102120a020c0c15090a0909080a08041a04030f1106190b15040905040203 71
    0x10013a010442140004039100c4520b05480203802c140358110707000c4c5040040309445040f4500a6442452110b0300103440018200018042881a02e0b001a0104100c40441c201403000800f10b00f03103d08030007401a5180718101c2c841c2c0c003c029010042485104211008810003020750060103071743e4011100d0703130781c0d041c43c08180541c51181134420a402040d89040001c0f54869492940102d2400c0380c041c40200044d95211680001c002d100f50f01c143d004400b900709034a44a0a039004030710780002c0603030040c0040d410312542010907560286c031503000141c8a04071450114035040c1c0490b038031034002c00c902c601c070b1a02c10048002441620029074a61110301e076140c091004403455004042e0070100d00f8411803241d144181201a00940901401440c1c0c010b071507c00c410000080c1c500b10302081d034020100d8901d58201c07070102c51120402e0007130401803400304080040a07240541d0204c2407592000e0602c101d54511a000910440601050780c40b240c076012414010041039606900c030303102d4640f050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 525439712 1250 525438462 525438469
    0x90507081015030b060c0319030504050a021e18070f0207030b06040207081c0203070e010509100f050d180501110c0c06091201020d1b0e012001020f0a120b 68
    0x1140204828945501100d241c003011121002050b42c41c4010151204036800c00c1c1c0d03071910041c01448100f140616521000012003660b552011054201403504240c100000b0607400b1410302d02441d0155192006802c48000d0700c0303041118090b905900c0301031010201081d0848410381881103246450b031003030000107000c0a0b030f0b4801d501c0c440145240c142d8000101a824583c01500d40301e4402c00085040140704d0214600541000090362442c40e4040308101265500669522030004203007816031030021040041030400d80e00c03413210320500c50204101c0145a1003001141c990f459002d4040002d0550151f00341c1605004c00c205451a42c20401038018480400c4211030040d40f0150041200d05400d50510109400c070b900e00f554041011212003c4140082c00100b2042c1c403000ca000416040030720b5040991981a801c5204100510303058503903d0741c2080101440d0b410320096065540e504801c00ca000e44281000109403100c0418080d0410b904841708504501600009000c5a100380742030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 525440962 1250 525439712 525439727
    0x80d0e0c1002070f090b0102120a03020a02060c07260c0a05160b0309030d0b0f09040602070312050606040306050406061509090501091104050103500c120702070519090507 75
    0x702c000310305001c4d204114031210713944240d14000040c01618160020108140812b4100001c01030100e42c0008800603515818008036a0084104001e50306020311512100d40da101407000207000e10700107000054208448100340d40014003400c00300c07100c0ca000e41c54601d17100d03500611441d220f41141c49010800000c51015244240005802141800c480180c820b01074030315490080c2c0c01040003c020070580d01c5145410b44958041d07400540c0d83d1030311345002003034907940f01c040701d884600e404180b082c40d40e80c2c40c04460032250044000305140d2143e0501400412450340500940070700f07101601c40098216400004407021030f0340030022a079a0b8070100094444688040740443d0040000b07001d1907009621150703403000c1c01076039121502a807020042d0843e00200740080c1081d030364000b600c0300380703a400d0414079064401c3c8100c141905002c500c402cad180c00740d10b2010f8180c03445400091030003813080058000030080180b41c4184090007500c0740b1041203490240d821001c0c1840e001030034481c0596803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 525442212 1250 525440962 525440969
    0x209010e09041e0f0b010e07021b1e18090718020c070501050d0e07080c040e0114070503041a01030b06010f0e0f12030c0a0c05190605090904080d0e0c100207 69
    0x5150b2003004940404030540c0418034003c54001c0c4c04505030002282c00b1019060181c940d0440003070075400c1445019142429103658281e20030303c0c550790b500780d60b11503191000c040c21445510700c03498448180001c003002605500e00701c88415400c2007000e00e034400240c4100311995550f007400001d204220001c1a845120b0426899502c480410002544500003d00000e4810540020b6184030030b4007441c280003050784085559072103049000401d1415220318070350040c0c0e0700000c001d0500003081e00307041040d004124400b0b10201000040600c81c01800480c180c41c049102d0305141e41e141c1c90102901c0d00140c55082c00a0518410000c045015982c644e40d00d07000140490f498400f034408002e9948501c6c1d1100d9080e00050002c11554030042102024181c482e07007425040e10705000521940000d01c3c541d80d082c000302351004002e07068102046400f682d80684517000c1c66030300c600b09140240708103840c50300d4640c030b0078110104800c03001c01c0c0d1015007107046428208044074404200d075180d04074007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 525443462 1250 525442212 525442223
    0x9050f0c2103090f0105070f0501050118020a0206150105040e040803010609122406053706090308090a0506030a020d0b0f0102030a050c010603050a030f0e030a1a07031d010209010e0904 81
    0x1d0000b442c6400d40c2d200150781c1c4c0503d08103290003070320750b1005001c1100020440ea1a91540d0040c00100d21810081d40036071a94282141403100e0038400a6440401801d202c100c11012110b0b4012640305070205c0c0d01801c10807416a40d176060526018105034070034030604000401c44c2c02e010400c1082604050502604a1002c02521004031200324000c410208103070300c1e50b9951100050151140110020a00003401c0a403000d0344000c102e41c0443c82c8200000c00012101400034012280c00204510a880d040030519840b00b6aa502180c0c800d4210b4018030f901801c04020040d240c201034000342032042d800002800f4174030500050014a1401c1503c0c2405a002401800b62891160001d0240c20f0048800451555941d85455040001c440e40a03000680c01c21241c0e060660820070308201ca075016001803c00c17281c1034541d43d03031400944c0c04001c0f4807241c24000c1294288203410048081074000410480204d0010f0164000e500c0700c001a40800e80030b00040c0010714001d2661445540c102c1c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 525444712 1250 525443462 525443467
    0xc1018120c091e0e010c03050c040501021f140a0b330c0106050a0602030306010906081933090e0a1104022104030503010f1203140d09050f0c2103 64
    0x80051405003030f9488803440300c41d41c0c03810540140040ea01445141c240e08500006910704242402000c0e07800007003841481d9076040000300810390380050781664208540010f000e50f880e4078800a0701401040034120b8511111809010705012541e0041c843c41d0400c0f113030950305d0001c800b2009158201c00301814840007034603d0f01e4043d0070402c3c00420b040041b82000081c2c00d92034234002014141c941e041800145d10100030028256080340401c4050400e40c10040d019103001040018401140c424100801e902c400c0404001d1a0003021600074100d89004241c2c0551190f040e01c1c203a0046200b5207207082c0c10100880584000401c0030440d280e000704003001c21410138000c0c071001e58130150070307011860183c038201120b0030010400b082c001c500c13954070103943c0e5141c11102c1c0c5074800c40b42c1026900551a07180300000940021020711440a01881d45071541000d031141c60090401c4003019002e400380b818581407140c008602008c06d001d0403210104107030404448010702d42440080043d003a40f08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 525445962 1250 525444712 525444719
    0xb10030c27212f0901090b04060839100807021209032104051509190b0d0509190503070c08011e02090f131a0906060a110c1018120c 58
    0xc1100b001c812614183d8001d60581c0d1200030907501c03d030980c00503d80681d075141c0c9188501d0a4001d52004000304401001099940041c00d17004103181000a07070b420f0714100030314403200043e1400c0d5042c80c03030040010000d2850460040c00f0700000b21540801401074a240003411580c000c151a0340030005001048200300400c1c2000d425020700c1d80d060449002400000340c1f6550340d103000a0080300c01489561101c2e060340500080d0610b6001640380d918190105104181924059800003a1202c4c008903054981c034101c6410300643c1301c10000704041501940007171010000040030060700c2156044542641d400b001d071300320760b11440c00d8115444c030304104c0c40300716080d90041d0108840041048500200490016601407210388050340200e0f140c0c120a0600658402070505500d020345061226141c84030014080e44075100c000c4046c4917a803615079500b0201008010290a0f001d040448890404034007d0081034880c6c3c1000c81d004208400411756401505040d4002580a501468420705 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 525447212 1250 525445962 525446003
    0xb0909030a0f0e18010b070c0501090303171b03130516050f060a2d030f051b07030c08070506040212030c03070809040f0c0915030b10030c2721 63
    0x10b1025007568008860080c40410701e132941800340c000c010f54180785641e10303d58a8150b00e0740b85039620250510440c00b100b040400e13000b0454031038150001005201d142c0d41d4940040111203c0c0300b141c0d02000000c400c0141d502030102e403c0c001c0c580108200e820758407008149045001e114064607411001700e00010401c0e00b0071101a09600c500c0b8180382911000d00f40c00c40c00090f2104102d00070341c1454040034012680c252050324465840048180410f143c40e401c107824041c0d20074003c1a07c0c40c000500d210501d0b01c030340c2581a205070b2126041750b88907102c0c1031540e900c1c5000e03501644103090300c00d505d5a549000004880845207014081e40c1800d25685034121280c1200744216007042e225aa5103040e0b10891041929290302c0e034803070b6911a410500e10008000801c40000245031410050300714030341e51102c146030f824607545400b040e241c545d1081100c10340751a07044640303803220042c2c000b1100038980444609645a2403e034078696407800c0b00c2c840d50482c00202c0036181e0700d10f00e0f07030000b01a02c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 525448462 1250 525447212 525447227
    0x10c09092903100c08041218150e0d080c12031909030e060c01060e012108070501020f04030b0114010c121d030f03040905070e0a0e060f0a0602010b0909030a0f 70
    0x2500609403a40710880303c1c01c08040e03c10366035103036000907803400421003081400300e000c070071029281c90048180303080420036400ca10481c1c01034881c40f0a50890b0580302c00d02c22100403d5029000e8520240c3c0e42452811010581140c400c0030700502500500d008031020718002d40c2d03c01c4440106040c1d640c0e86441010008002e00b48060f8104400050320f5002071310b42c0300003026401040d0000180d024607124400c000040c040c2c02000442885089800340701e1400c6641039203403038110000a0380c0e0405132900c3e0740280b141c07950340744000001013000001c0c003440500050407520b0b20004060700c456a080110346071703903e5030b00007409101c20140c102c2c0e000340700d10070480303c040e40c0c104810034500d0a04000f0345400385440b00c120450740002424001da00b11401002d0b042019820a041c641e188140003844002d090700610300d04241d0b08001550655076650541201c040160040014a0311804024060440c81ca2401d00800c000350205044206c00001c80c0e102d420556a20800b2610101d02200c440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 525449712 1250 525448462 525448541
    0x708031c02130e07020a030201050603060601050901140d111c090b1609080f0709061d011a19052d0d0e010b030f07050111010507020d2f010c0909 64
    0x50310340d600104145801503103040c00b56404c1c1d0001d103031080c041e15000f8250f0700001c2c0024041d270844814014a42d801405a40b090348090074112850244111150240e00480481090050800c3c10000e4030b02000d60003000c440c84d0b500040c0c004800c00c89030b00001d41d2115107004200301141d40000d841c1040d0000720044601c02ca1511025941c1d8070714840d480d1040c505031700100ca0f0031800f010441141284951001040c0d410510803805154240c0051110014443e0a106440c0c1c0754160311135016110465001c607018110b0081d41400d00c0800a0a40c0c0003c0700180c0b43c1d034803827526222005c0d2140311038500039090a030b03c98600070399041c0003400341041c0790403203240e592a00c04503845981e0078403502b411440d0703410080103014504800100350a95200114401e64900002e00600f50307404280510001c2c02428441000d04d24070f142029458030146481e050001058001c0b440f048043d0400300c02803445a441000f8117850708140c000310341c5040344545103864840e240302040541c1e00c1164009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 525450962 1250 525449712 525449737
    0xc1305040e031224030f0a08090d0515040308010e060a1e0e01170105061522030203030a030b01120b0a031b08030406120f0501080a0b040c081203090708031c02 70
    0x18600c8410345041d04550984d01040300c0c20341d000c08600c07103504c2c00340040c1c607400c81140201040e580464005864592104014100d40c0740043d00312055200c80386422006540801203c105900300d449450111400356011070009030480e000180a02007104014060300000f4815103c0614024102001c40900480e04c290001100c00c00940c02e50080300c801d0007080c0301911800480b0b101c0700aca40c00c4603c01400e40d481520b544900104098203d803e40c0c0c2440c1711540388200e170704401c031020401e14100d41c3c4001e616100011325184407561541006210a1083c0c071140700c00a00100042c058900319441e080e00950600710810110758212020003014401a140944042e00ca007191411a030080e00801d0200c0c0a0480c030502503403c520505003249055081042954188151941c07104e07001e94001e0050400d4070040f80a1060841c15040102518001c03160020031045003aa941d070001c5896025501541c0000150802d0110444045e95144810741941c854181c081400a41040855410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 525452212 1250 525450962 525450967
    0x1051807021914010b010c0b041212050703090201030c0905010f0e06040f0b0304030206070519050d0b030f0a0b0901050c041a071e0b090d05040b070213061205060c1305040e03 77
    0x58032010200e448219034050182d007403a090419403c903007911460800d041c10401080b8003940410300411811781c009074405607440501c51030b080100c035903821000510025901d05014886800e415900c8140528400e032170502444203015030a07130380300d0000d1040b1030104000d07860541d04107100710300310801107070000c0030f0600f05500c07400103480c00b041d40e0b0408154000c0000070300c070038160100b0400d580192075203086031600403200042c0314080144007410b4280100403072224400a410340014540c1c0502400719940c0d000c0000590766194a00c050a403210324101c40451810541030250600c6040407840c964900707460b195410500307096002d007201c10742c0018480e5800242c0b00d0300720b441c50b0405410500b4241c90850401002c5408060190001d07075000345104000f07150030006680840c1d1002018a1703c500d80c50020480f20b4507605200c420342c600d0300001044012860200900c2c181c0503904580c000d60700c1100c5040c481c41003036550b1200d41084601040341b4505034214056100011064a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 525453462 1250 525452212 525452233
    0x30d051c060b0403030302071b1404050703091b05102a15060816050f1e011112040611030a02190f051605120c0d0f050a020306090309180105180702 65
    0x403a030f0026001240082d030001009410705c4a06807019810f400e099008202080ca022465840701d880f8031402d60089485d6400603503014000c2e0b0065070700680000c8010310000706458501e8044131a409114410600c801100122078895058007070b08104080104c00320071b8101d0142a64003103100c504880382940001079405006035800381100801401d40142a08001f054240d10301802a80003a800f0b085100c2002e00c00d41d4441140002d070104801c040301c4140d401c2c20040f2890384600240d10354074401d00210b40d05200d00788000b4411151141d50b9204292074880b01e50343c8078442c504160340107074000400e154200401743c1d0300041e42e5115441c544a051013950300c8070308242c0c800b04030000240f25250200098101400540d4803a10800e0141c42c40f400d2a00006284805030074000c1e1500d190012000200502000702d211555001000c99080b80f40210360145d0301d03840241d5542c0500d00c66804a03040001802d445030503100c0c01440a6103018682e9000103401100428004c214400d031000b99 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 525454712 1250 525453462 525453479
    0xe2b2a1403070605060607080a030e01020f160209060429010513090b121c030209060d02040f0f050402091e0102100c0504050411090d021201150603050411030d051c06 73
    0xc00c15014010055034555406003000022210300409150150400f0481c0c1000a004001211114003180c200010720003407048003980240503030002c0a85000d0f000403800907140c0e034001e5100001d4400c4410010503903550080c00243c89005500c09803004800d60845070255032218014200c4506251060070b0040d08007c1454070702003644055a96a600d601907091810008189000e0080380001070201d05000c0300e9500c9400c100b01d808000f0503602041d4600c0c2e990304c60044a803164820642951580c2e2584d004424404203417003440b620038004640001c075801e1a000352009070000400c1845030b941149207213405c1d00126066541107010700654000102028401d43e1202051a44c80684503400e040610044540e5065038800c0840113220301403095031800c1c0c4ca522100ea0646445c4484000d43e003407a4058510314500d0500705442c500080b030001c3d41a0701641c0304a01440c5050700c508030b031805140e00c41c1c3c030b40f521940004804001c010300f001880c102d0005600c0c0000c10009482d686c0300c901 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 525455962 1250 525454712 525454733
    0x2070c090b030c01020606060a0e010c0206030f071101091e15050406020405040c2f101a010e010804050a03030e0a0803160315060801060f030b03010e2b2a 68
    0x4444241d61208028402e0404005484000901703000400e179a04000000074180e0280100003820810341d42c440c91400c1c2d00c940403500ca103070750260059807039040a040315084445c08440307500004034a40d03402c203100714050207007070781542e080003910320b5444a112003816480b111000a8030403990460141030a618544920bd115a000c3c0c0300060301e403410882003100f526000440b04c410000c40740381c24a01500b582c10b1041c16400c450b2590454038401142841c10f040c0c890040e00b1846107446440c2142c80e003851041d90b4502000d03a10890b40048420065540350740594016200703a000c00c0070390000030300940c06440c401c24030074102d43c103440b8560ba40ca04164000c51300c2c8290841d070400780f488426054011401c80000710050f1901c2c00341403110042c550501441508100001c1c181e865480344c0c00780d030045541101c0600203009880807111550b6454a502e45601c004103429142d0890350042600b004003d000f0301c1d504d0841c1c414174003d8400d2007400445804580140c3d5900480004001f03800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 525457212 1250 525455962 525455969
    0x190818010905120a03091e0b0721110c040911042004060e0a080c09040303050408090a032108010602030723070609030c050406260715051206120a020105030a02070c 72
    0x2d01d801314513843c0003040702001d984068041071000385004030403601c070302c00041640c001451040d1180d41c00d003481d141d1030300f100142c82c03080210459207920305076001c007c1c1032650001200720f0b68480300d04820300c03041302c0c1e80000180090184103882859032605400c02c01c852120314003610701d60901070a400041d54065844500410010705031b00a131400d044450740014411840600a1840c0c01c0703011070b1044000900080401d0b41c2c03100040d04000380c4005450b0b25180c083c100a00c029203910f0700c400721441d511107650b0200700c11046210709610034610141602c4031507015504080c3d540d42c401e4110903001b200350340141020403040d02c1c0034900b08021001010643d444481841c03850134606845040ca07000140114101001441404410746807034520b172144200c006024040300d400c1904101a6400c14021540403d03003003240a5480409480d503902030207410462a1102d10812000e0702209080d0070840e04174052440266000c0d601441e486003500c0000751800c007041e030322490b508840b40c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 525458462 1250 525457212 525457249
    0x608060d14100f0c0903170c0a0311150402010f050705010f150303140c06010324050114031501050d03180f090204030b060d0f060b0a050301020d0509190818010905 72
    0x41d2508029102d40212100d0300c942e0b00c000c2000024a900041c084600c0c1c0c003010300f22030f800c00544a0302c07000103001c031208140d8450039290100140d140c018203ca006580c045da5034030602170452190307003100c03072458000c1d036058482460b074448045d001d0361660440c0205503555585e440048503c05850700400c901510030940500344a401c0d40340240c01145d40d6001800030f82d405021a00520b44009101410b40e40c220140907120000e10002a949040c8101c000c10110300b00307400003420f4800d440000d809400f08900791400c0181d07403200075003540300074411980d0220b94086d000003c00e0044110301c0d00c094424804246141c0c0311000000e43d03000d683d21100805070b00040c00c0041c4407041074031a800003400c07181292880b00d5901c0b0203c800c8031185000c2d101507580c1080324000d5454507290300041201400075510390319128005401000d041381e0303025441c0529613800e10140c551040e032a001c00d074000000303810003a01c07840c404c988102880d141c606000450f03502040d196201000488003c2012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 525459712 1250 525458462 525458473
    0x10b061306140301030b0601082707090e0f120d0207021f0201050c030c030610032c15040305220f0b03040c0608090d0e042004030c1e0608060d14 64
    0x1140080054402c01030440b00d0103030910040c80051038038032905030414001d1809001c5915052400001c1c0300c02d5441c50000400b110000440fa03800210f401c3d0220383c24803900b001440840000d4030340f1010045036800c141e8100c3c5440d44950343c111009400d00c000302c41c3d070040c14202c080c0d0115507010751392a40c5000c103c1d20740c500c1d106030340e034240981c0e80e101e8900f02c0003a00f181002c00010f000c501014050a02c2480d884840b101071503c00d611071000440c0103020305070f0b03c0406980a421400b8003036000d0f0344c80d020b41c4844008840c05600003d010380e501d5500d003441c0048403c0e810440021425118004000300328000806802c00801000980300243e076043d03030703424203280040403a4070960000e810700c000c0d6402c0110001000c01c212990b81041c1c1032080c1c03100450b000083c02048a00310301e20071010390081c803207444011034000c0c200b52445050040c0b011a2034502c80c40010602c0301615815a41000702400100c3c4107250761504500c000d00724003044070b080d0384d0354420509500205409640803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 525460962 1250 525459712 525459719
    0x20403050a050f0607020c010f083303070806040302151306050127060302060a030908090a0b0a0f020714060f0912030a090e01231f020102030f012705060102010b0613 73
    0x84c03107074a8001600b03000030102083c240d8000f800d10324011000800f400428000511030900091003000161103415510b40446a00109500510f14032842c1d640a4070801d000403030200030005003031f4000c540507001840141901c02c140050b064005000c10802007100c80d9120002d0024040c041c0a8001400000c41405d08200c80380703003580306d41c0b0051909a040c03000400240c2c44584c21903010040c50304d8089100380313136818180d89078416040b4a40d008040d65030002002c2d92203101810070f418007650b036040405031101c0301f280d68641e103009500441503021480b03400d9141440013412000d0f42d52050b14141040200042c81a450f07035600d180b0750f0340002034601842c9610004210150200c100300d205294100702c29000c0e4030b2041c01030745a01c0710151014000700c0d920700042d00054040c00180c40481c017178400000780070b03420036101d07603001c000707800000300d0340070300c0c0300744660080c4074600700700c565031603081c020f0005441e001c1d00640c1955038138014844603803500c40080a000310400b03003e4904903d07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 525462212 1250 525460962 525460993
    0x1020306010e06120109150503120403030206010e0108030d2d0b0909030c060a090c0b0d060f120201020c09101a04030218061f120e01151415030a020403050a05 70
    0x94030b41d18030340700d0b4000f04501080c280b011a030b4541941d042c0305001600050300040b032102d02181c2c0d00525031500c1400401602d040002c0c0040043c3c0b807081e404e42d215a646ea0003071180001081c081c0d42000c0d0001c1c4201603083d03080e980400c00301c000000c034500490065501c201c0d990100802d180105945400b401034003400cdc215441600000058011403601d002c4020403910744001504c034403625600c0d803050005011541041001a1a0100c582030f510150b00402d07200070400c81c8104100b49241170030004405202800844010340c0680207004440070000407c02d0b2048010048104d04485400100f2802541981c00d210181c1c0b04410039641c0d4207500401200703248000300d4200450b10103042048507250ba4602580c92403c4030303101c0d035a00d000700b40c066a050507000c0c2040155031078211011000c00c01504140720101d40c4048a40310a074940c1070038130200410f0320101d90410703600100701000640f400c1c01158031018064006051540702e50f109414208503500a4a4982c03024560030002e11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 525463462 1250 525462212 525462227
    0x11030304030b0f0a06151d13021603021b0a030201030207170a090303031a0105190c0803070e010f02060903041e08030d060302011413030201050f16030207150c0b060909160303020102030601 83
    0x401001b011000d00079080000b85944009003241d4040030508010301816116240000d852144040d001c4d5100e070000020034070784984c12241580184103900c00510213000001d5020f01400002d03107403000e81811900113601039070144004850950b030903052010300d640110f01a04141c0115503604050600d5400c0080981d13064610301d0142d001019441c0c0d50070380e0014100c9100988070b0300d46a20710020120242d420150101000c0c151503400410003000c240d0104c80039401c1c050036200d1303c1c583d007403401c07089940d41c00440c3e070a8900c2e0310820040c08401640c0c400768500000507404085403039122482c031400c50700078244c1d0311a12600d41c8000d00445d88c229640d84a80050440f00342d0500c2c5e204103103125002d15601c03000e814400005030500d07100c88150121001250100c6502c030341d034641407070300965441c0d42707106550b05000c5818940124030310540c2e8415005812200c00300700354550b042000f034081c80c0940184214400d405010a0880041c0c0c4140001c5000c1d4000588901c0d003680058040e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 525464712 1250 525463462 525463469
    0xf060609190f0b090a0618080303010b041701020c060414010e030f0a030b0105030907030209100e090d11010b090f1e010b0a020c04060b0a14040513091106041211030304030b0f0a06 79
    0x202c3c107002d620442e4031a504c45000b19800b0380b51494030540e02608480c04030324242c004100d00d0100000101700020004003d0048800480105042e200024130042c204d0142c00000c5045821100103d000b203013900e01036001000c00381000040c014144180145544d22240250480c2100452400c2009416202e580b000c03107800e003003161840c9003400e04244c480121b400000d00c9480660007061041300400b000d04040c0c040c12140d00c6440c10000c09980d41d6007000317400400081c0305010302070524241800b0350249914040d001e08540c0c1ca540418400648004281c002150520b0303000b540b00c07023417154100b8001c210000840d42e4031114800c00a0509032b000d001a40541d080482c00c1080c154068102c6070141c00070b103016503d81c0303040d4036030180e42e201d83e5000f550311184c400450ba1407680e00e544485941ca00c01d04040507920114014015107000307902c101c1a001c0c50f2103500d040031600303842070021029002415a803900e522951090440801a076070410110f0105082218801e811310880029 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 525465962 1250 525464712 525464729
    0x90b09060601080f07021612050f1b060c010e0d120501051503011e0305010e1005130506010308161b170a0b01050103020a050c0109051f11030f060609190f 68
    0x240741000002e041c0d11806440313001c0c0c465501c000210114401e01499490b4401e52411a41255403403151a59008100f03405440500030100c44480c0c600b4001820500c6100c01c08081c40030a181501308040e6411a05152010755200e8002c40080007040c42114411035282e164488000302d400b4549086440580280e0b0040c075000254010745440901034a045441c2020410752122008468404c1000300703a1000346a907090043c2c012084c007002c10014112082c5a008000da03555100003400708582400014129802001c0140040740c8200300406981a034240e003c1c00d2000c1741d50300d40180142289500d000c084107440705002e030701900b1841031607030003000700205100061600c484010315418030a0606042e40040c840261501400a0f641c5d4056407000800c0418001d0604c540c55074001c0c20919903141c00411101351101480c400c444600744110780c070030b05545d100741c0c1c2804540800b9005941c003c00c188140b40d00c680d076082c00351040000620380000b245251891800c18021141c00c40c840 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 525467212 1250 525465962 525465973
    0x10203010b07060b1206010b0c010e030f070201030506150304080304030905300c090901060510091d100b07050d02060702010212060d0204021909060e010309051b040204090609090b09 80
    0x2040d2100800d454016401c6580000c107040344c0b40014100054840a4002c0c40c005c0e80000682e4810300b00150918082c1c603c024050712100c40e4200d9185d21502c5181e41d40036405111840155109912466000d00301400e0943d038048611004009170b003003103c04030b40d41c503000000c10040641c000e6000c1d0042c4402d0300c3c904804200d5000d2a500c0a080e000c6400c501642021085940682003206031300c0010f000c0c2903e4441d007442050307030340680384c1d80c000c582c015a4170340100e480c0d0a1040650340200c6080d002814681c1015034075000070030300082c06ca5200700e8040c0d4030108803811280000d000d824441e4005040540101c0d170040d0a11000804a10070741e48140b00180320058410815a40090101c03a404088403451000038006e001c1d01000b41305040340311141c101040d41080c0320505849661307c5416081003143d0044050f940640c10082c401e81180e2a0014080607104500340310401c020409414152100e00b9102141c00316401000c400352581000d009018828010030781201d0500050304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 525468462 1250 525467212 525467219
    0x30705100804110102031b060103210207090513080a08160801051008250206040b01091a1e0909010603020109080a030917010207060603031707030507020c190801020d140901020301 79
    0x1070258100420180484640550404180e07100b44101c030300080926000d404d0b000c3c1d07140005070765408240822204259092104071785c1c0e001c1e0442404050b40a0390003014440d080642001c041e11000c0c10020560211440354000034805602030424034842d942c031000d20345040001a10154494041c82c803e00141c0c40052295468180c5407401031300582c1844010b5481e5116040c50300d84528904822804034083c101c084543d011818034000d80c001c4044040603622070203240e04650038034064840041e000300754107265007491038042035031448459111002e600404d012a000b41c0040326a00300a0b5502c6105008668004188030b0142c1468001451003500c1d1359005010701c41c072406410406900c100050712022002d40454840943c881e10038001640d892401504440c68074202a900a0412000a900790b20a208503845151a41d0007042046c0040c002c0c080c074a4020300d4480540165400d02240a0000340010000440b0348080010013810800542000000241105a15900420041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 525469712 1250 525468462 525468467
    0x904030504050103020c12030117072c15040e06090f0c0603040809060705100501090b0315061009170a050d1b0204050a0f09050a0506100501231c060503070510 70
    0x1034042d6202030900598030f8582550302c62800d0384280c0c00c03541d00240040041f800c28005600024030701c00c40802c440c403003038036100100c503801840002224003134820044002000c00300186150410b03c01d420700c80c1d441c810725020400ba01d02c2e01282d2105540700b40b09220645004001001c4071070703240e5024103401c3e0f0b4444000b500620000c1c05c0a08440d0001c1480002607490208032214160b2001c2241c00c3c0d003203041202c10140809119400d14285040e1804403d82008902608400c401280c03028540c1e8a41c01001203824002c680001080090303000403a042c0700c84c20241d0840e9000070014600c200480c5003036460302100f004607004105800c20b0000f610110401513002c0c103039048802088a0b683c182da003200500c0404250900c503030400e401030b01805070201d2101d5011b80030303d0545240c0d07a00e02400d0107400007584600750010700865102454581103604d100c00c0f461410042601d04440c0342121010130131001254400165240303400c0065103030401c003c1000b00710680d07082d15205400e0101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 525470962 1250 525469712 525469717
    0x714090408030c16110a051c061a18090705060708030112020607081603120501050307030605061f1e030525021f0906060918080a0905061c0b09040305 66
    0x200000004000b00e03100a80040036500040003590001c403c444450502081081105d401d0f5400741d1548a0042680d0a02c586c0b0078203103940e00e034021090004240c1e03508004240d1400b00e40150201e480c1d8a55a0303030790b0f03040d020814050311080d0b40d0260408052003030070025980e1100f0700c00c0c2c00802c00309000902c1c1100b40c134111641c880004404040c10300104d4042d22950400514024000a42a0503802140402841c00d40070381c0e208100102100c254004a072820701a07181e01d41d1001c101040058110782280f6803208001d060302201d0082010042083e51380c25100d100440d0300000c00c40b040d00c52910303180c1403020b010300e014065428080c04101c0d110709003440404103081000c41a0442038001c1011030140c0482c101039120000703941e50910028900703100d04031019810b06400081c580703054040d000403400030300b0b51620503043c4d550307880407694400040c850a100c41c4c42c034000b441d40d41c3c0030090414210f105490b1081040c0640035242180c4040320814030944c0040c040c0030100303921406 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 525472212 1250 525470962 525470971
    0x90d02072603040e07020607020111030a1e14060913030e0f190b0c1e0d0509241308010e0709050a020c0f01060503120a140f0403020301140405071409 66
    0x10504864415542400303852906071036031404510000600041e0310741c8081e0326501c80d00e816800d8844507206c8100032420789100d401c00100000007840070410110065001010074800b0000a00203110f0f182c0180d030544030030703a6490403102c613040100f007523508080c4010781c6d100300e0550b01c148044029a4019041c445c2ca40302c1503000d9880001021000e440d1810044007005604c50821040c0307695a010b400c1d168003611851116020300b400b12030300d10780e061140c6c500d40c014450240a00100036a01101d4035040041076945c4072140002d100510800380d00b030302c1c960030262010b03c0c1e40d4565800300308089000e90f034003280031680351141d00203001c0404243c4c1003da50f4916004030342901e81605000284c002c00c21103103507034050f00d49a1104040154000c0003140c8040d02500c1c200c44011442c183d99010380343c40b20010940d122200080c0c1c0c18000e00503c1c4001420400c1c80c2026100e0300032a0031100c148040482c0021040188000e02c00d0170400440142032428003040106031000c0882c200840251 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 525473462 1250 525472212 525472229
    0x6030405030d050604021c1e020723160b0a0801050a0501080a0f0f32010f0909080f070803040c0503010c0e010810030b091014040c0545090d0207 64
    0x601007800e45c0d9480c0c04484401c00e18420990049082d000781c2c90052144507034110390003101e030840d0700c1140c01900075036601a4210387c800c9071101c1c3c481c40350050782d0801c1501c0c000340d005d440b0001c426130f404048884050081800056102c4548280c082d11380c950680140d485000f40e1001000715aa106880e241d010810f4035010038002c00c0d807994a4058048101c10300080c60030701101a5002c0e6010141500b01a4260401ca240c0001c0c40203001201900780500310122a141d039041c40b241a20f50001409103206081d81850406810b41e2032245801c080801c540d1994000b080c0414040c044000320301602c801c4008011a41c140070000c0e1100e407105202905110034007000038503031400c0c044c1a100858100c8401e60951034459107107034a03688d151000c41c000500e008003c1c1c914480d244d90300c0b4425680140c82c0103045081c03404015000b00c40c4c4808024141c0560001401040000e50141c101e91a0f080c1c040c088180c2d00050080d500e0b001050302d941035120b48803000c0c0305540025400c080302c041d003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 525474712 1250 525473462 525473471
    0x506060c0d0518011430070c15090b0601050f0f040b03011502070e01170708030a260601082809140106060c150207051908040f080606090103030e01030e16050f06030405030d 76
    0xc6c0c2080c0e4007940c1e61244288000d100410010202e800000d460001e40c42401c0200091a011009104403803074920050400090760b80091550750103440103002e10072442c03400c1c6003041d03040603c0c601d803984150416034550030040010440c02003800809070b03640b4001d0003c0c020305410300c0320468a0810503c00c0d41102180c2825001515000b480240007a00207002520b50b24541141c02800f038201e100f0509501c208800f58001f24a440d00308094020f0780e050392040740d1900c804038181d21440e42c00340701d219912000a05c50031212024443d44a00a21a08803203010071309504626085403103035840403003880311038804000003642190a00100440c0b1080050b103450072410702c640703400388440b030001141540d02e8400c02403000038406403007180d010b1041000c000c0d80303e4207800e44403801900d071507030031401c00030051000038018100c1150805040c5000905a14184800742c64454942071054104d4161041400b00c0d040000b00e820a00380c05461452071420b0940d41e6035624411021140c24007581d6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 525475962 1250 525474712 525474757
    0x201020c060a110906040803090a1505090f041b0f021e030403020607050c060711132c0c1801171204030f020307031a0a05150d02040506060c0d05180114 67
    0x14030003941c0c1c151344c02800301a142d41d1107500d0301d5900c2c0e00041c880740c0708403001d6038001034440030102e00c010a50b80711741e54181000740103420f110081855180a5071700907255045032240304100d003501607030000281da905660010a07c4043d0401c4002ca03040784200c0740042c024003030340100000319812030f135050b200c4e65981d80180c10a10b003455804404a0350000d000101c080c00d01c260040621301c1504111a05080003040c8082c0c0801c48410020204000c5540020500c102c00001e003480b80030f92001d4240e81e21300c40358038005001c4120040fa100c2c0c41d5540311005000d40c424002c50146881941801803a400700081c40704207550089110041c280314000c0811003c549081c4980802150300140c0f205080c042881c2c20031102d103044420703804051910000500d4001d40500c450304d030900c0600100841c6d4019024400074280041405402040030000142c00c00740c20000442829015550540c980c01120508600c0e4598994114100880a42c90881d0b00104504481c41c2c112900c6040072591507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 525477212 1250 525475962 525475991
    0x405031b040905070806180102070c0b090a030501050106180e011a0c030d02030711150103031d03030c0604050a1a060a060815121b0103060f0509091e010603030f0201020c060a 77
    0x500c140000c3c5a8098502c0c0004c6500d0300050b001d0007400140e0180444036a0328200600309d000b06c1002401c003491080301007021040c060014103200300c0140107503111940300d858050a40d0401c0e400280010950440294480345030241c4101420040200b182554982646590000c504440c242d220302d0000400c0c611200d0304208079443e00c03079000411341d10327490940c0d0054107815035a0382c2007003c2d005000c40680500d040c100003d05032070303150700c13181c100c0c0511402c08482008209070f15a0144410095600350708c4d41005024400c61044c0c00808a80b00c00f868403140c1c100307819090628442e02a0705020095a07840c8102003030351140d2802d2049582c43d43d00171a00d009040e46040d400240c4d8000380e0f5400714001c50880600d200d420f13031800046001300011030440d44039104100b40391816038028801440c10120302034000ea03024044604040b4020891880c0d11402a5401e650369980c4508108250f000800507040407090300003141001000110a41c680d60000c100c084901e91350f482801c00100e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 525478462 1250 525477212 525477221
    0x61f0503061f0807080309012616050f2802030a020d03050a0b0916031107020307031b0302120724120c051c061701020702030a15090b070c03030e030405031b04 70
    0x2651108544034039517a948910f0703c0c5d6204250b903034000b03094000c03000e20b81020103005120040d00d020302c50f2490703511100410506005a134641040220030001d04078a800785a010340b480340d2000b540c00e40e850f4100000404442c011400e0701096401c2440b01803003464020860788000103042c01e0101d840d40e50b03c1410302c0149085990340c0c1d800b100d030409000c031000c00f00b0006c01144503280c80400140c200c65143c84440c5c0140c400007581984011030604c00203814280d524071620190070005205900c1e940040d205128400707488009600c841030800400352100d0781101d9505200401760480303500c06c040200555804c21001e000b01e500c42401084261085080358030b4507809210081128407501e100038007520315446400c1c2022141103000d074100b20103108440c0225030050051402d424260303119903501a0001601d44517941e54240c55020802040c04948108519a01c00c2c0380044d45180180848800c90380100c200d0348140000e00c1241c80c005500031400c02c4450007141141181e000040141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 525479712 1250 525478462 525478469
    0x1061802210f0412081006120213081005150612071403150f0a06020d1841090a0b0f06070c1502032503120905061f0503061f 55
    0x1000701c0d40410250710a40c211030780c0124412071804524014404080707a04030003d07141e0313000d500844103040200b940107101d01c04a08207400c00160410001c803011102044c540e80c0f1800654000c5004009003040e98484c00d64404180100d001011001072301090031170050340922a844014030001c035119501481005520784060301007960b50b1302d4240b40003003050b8070a00b16a8081d00c1030400803141c03807a005071008150b810b0b40d40109005800580c04803a0040780c0e105640c2c214a0410000c9001081d1800749100c1503584410f8580365400d07c031155102c0c01d07230240b0300c40c03000716000d059144a64450031800d070031009921001c0344009504000912050045200e1503014100007500707010841a2040c0f002103075107907111250000d0304c18500f40d0b124803901d0103110314400102c8841540c40318105e00c4600090013454440480880c04072400200c480d051024ac0309580306004005800b112601e071080f03c3c0c150003010004880c0b5102c04241e4551001c0c0004207080e0701c445601ca00c80d4035068900c8010b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 525480962 1250 525479712 525479767
    0x4081e01020c0a0320030316051b03030106021c02010b0109050405090304121a01051017041e060b0406050a03030806040908090616150207120e04020c030a0306080c0301061802 77
    0x1243d04d0007401d0102d14120724426103092000d0300c08000d401109a034803410902c82184025100c41c0d01c100c07101e91000d00048911500b484110418100c2080a18042c07d01a001040c0d5103040000e01c0c82600c1c2200c01070811a0f0400510160300e9910003000012180255170105142c4c0300c49620034114042c940002445440e60148401480420500c4030407404030400c10b4119641c8030030900000309030030306400020800401c0e0350500010401c0320164032034002ea030f184000181e000a1500c111031301c40c4045c2c07007454580070f448150749031910800f00100411101c0c0f03000c803443e680d000303802302d00c004001a22565603040349100340070308101103440640c4000c00a0383d6500b45000700580c0c1486010040d290040504c6030300c4420085e510031114890f42007991400300f15401942110300400d0000100d404c2178003401800c65400c42003029240c0b0321103c0d20040307101c50415101c00e20b462048014180701e61705150040218004000c080f0b031481022080250383c030800038021007054000075031017800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 525482212 1250 525480962 525480973
    0xe190512010b0f0901031e03090b0a0e011106011a0c0703020d03020a03090b040b0708090114130e09280305040e0a0203040605090a0309121e0804060906030204081e01020c 75
    0x44600661200302d109004440c21643d0a240206114644d2004d02000f00600c0e80300da008a001504040d8081000d442454400c01903a15029460035540164824002080c00e03078000f110203607003201c050460b131062a0003c200030341c03400098404054031075005070400000020454240002070010501440e000742c013101c0c5524080c40c0080d550b00907a0000e9001440450001c505000c0c01c1d002c480840307010341d810604080440e1900e40d03050303011100c61030520190454643d84a103a2001800750b864030000c09902a80c5440c00f603c032000801421038000b900280813003424400a01e10b40c120188031200ea010a2405a207029610340c032940d00f000040e8000001004134080840c0c00940c07103144207043c1130015072115500c0540c1c034900140001c000c0b0f16010024403074415102c81d4070703040360300605170070541100031030241c2e051851141d0b00b0f036801d04c4002030500086401c5035440000781000d1408601e013501c0c203011161200046101010070701016099034000700025016140c10740c1d0a1015a103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 525483462 1250 525482212 525482239
    0x21140f1b0a1b171903091a0720010b0f0102010b030604030309170301030804090b0d0c060305060d0c230111070302060a0c0503180a0b0405090f0a0603050307031710060e1905 76
    0x14070b1307005854039071000218001d10886041c464010802115070051048003000e0880078240381481004100004000c50f01d044143c5841c1140c0c03c00032420340c00c7d4000501107000c1405d00880c5c800c1c1e00b4007141960b041c00b4001e00394ac0c5000070125803040d054600002c4072800d41c03403c0b102c100a103d1084141020100000c41401540e000900031a80030304000c12a03004040c0030f100d519850070304054565040c0c5071080103507038083d402c40d0340d0040380208003003d161056503400c000c1c00b01c150842c0703a0800d0001d01510103110440c3c29162039600908056803859560503582d585c0d8100b900000307001d1140410f600c00c1d007038000c059441f6110b620800380c90300d4000c8603c44035000c044407141c43d4460503400c000007500d68600c3c01203071b0a4a00c041c2c00f6914580c0d4800c0d04a60796200600b205080c039a690100001240e41400a44140c1c0e00c603644201d480b54000c0303070310518103601504043c01030009640400c400f80d0083c2520541050503a282007103d2111104081c10001e580c0c0540d401141e03220521 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 525484712 1250 525483462 525483503
    0xe07031d030322120305060f040e01021305040e06130302120c161a0405060c07030c06080708010f050a090e01060e010f031b060c0321140f1b0a1b 64
    0x540c802c0e01e00761024183e18900140560500c00341d840003515040c0440001c030000c51181c1c02407035001401600102c207004002010404a48e82480404450396011440c0f81800035007148200045c14121003c0c4110300030321203101e4903850094508405c10b084031200b401054000c1c00301c0d58054213100092911801b03150621a20b40054084c0c2c4180004002d001280c159070f805250041600c081810600707090600b01848246e0f80070303842d05103007131181c80000000100c070345074103101500c03540e583d00c3c243e42000000030b0400705041e00680c012000d8031005200707a49500c6080002c0720b48030740c400b041c0041501c038040e00508454202c1022400c00d000041107858035003002c0e50880c1e2081c1505e2030580c071440c500510303a034120300400000485116241011038428100452105c056001c0c0241d0140c1c03681a00c0c040b100781c0c92000820711401c1c0c041207007580e44c00000d681c1c000c1850b003481d081050102c044405910510100c002404a00c00c1f004c1103192032034002c0301e440344d88281d400221401d100f410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 525485962 1250 525484712 525484717
    0x6180504110c0d02060907150e0603010303021513080d090201110106030b0114121c1101020a210b01020a1b030206040e0f011508074409030a05040e07031d03 69
    0x50016500c2109243c1c0c010350310009001e4424013180b0040d01c2140d04200360460f802c8030a4141c14100445000c00008035900d1702c00450095100b50001c1089440805809004880060915880f901141015408522984100c1d4401c41d10388500091460103440141e51a004184c6000d80d030f5881d00c84048108020a00300c1c5050b242c2c03001e1124800d10f421006c21808425910340110075401200d900ca100104410b05041e2009850404810078500c034120b10b822600f0010300d040024000d4820084030308003848078101a40c41c2d0b0401070001180712030010f940d51890810081c46d14003896280044447c2c402c01072409550300814199070b035a554004440b4001096030382c01c2d0a5450071000040313401030701c03c4188180c4055218400b1031b82d81c0300c0003a2418644400510307140502201c1e4100b12504241d00070b11407034015280c4412200718074092403056000180000e10130390042010004040d0001e00740d41c12911030310110141a6038648041740a86003c2684074104400c05500d090b460703c01102 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 525487212 1250 525485962 525485977
    0x11100b1216090f0b0a0e09030c150411010f171008010c03050103020f041407320304030f051c15030f08070516060516050a020307230402070201090618050411 69
    0x10240400308200b10480300726912011030307031750266144d1070801c0040c0f000c0706100e5011012401340c90624a8503c851410160348420028012050341c04010401084800e02c0c40139000a01e0180b60000702c00101500403c44076594886003990400014804641c401451016204000003070040c80d070100b9001c3c000c2c10080c00101c1c8030300c000c03502150540c2850300c6240850b07071a09050845036100e294058803803180341011008603211040ea100305289501c94060000c4500d000b4580c0d403454141402003940c02101204c40c00c000c0104841004241406100e41181d0040000061014005110030080b0240d603800103040c500b0403240c0b40103101c000000f8006850140003a07039640b02800740304040e9820140100404a00700f4070468502d090310042035403e007403194044581500c1540c000070300d400c8003607202c120220303c0d00404010f491078510598030380660540b001d6041a8030350303001905644c0d09010b0641000000f50751900181070383c000000c010f00c1c018200b000101250340751707440958800300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 525488462 1250 525487212 525487229
    0x40606090611010e03040e0415020f0711030a051c031b02240105100c0812010e090c041e05090313090b1005031b0307020f06100305070611100b1216 65
    0xb2074885115106000f81020f071380c07207038020358034003070400705810300451028009407400100c41c000400c1c485100d10042410102908a494954089141900180f5030b41991540260461000301c0001040001c0083d03104034034082203040c40d260058218010f040d0044030003050035029825560300c0750041142c08502400c1e541200070081d211190312002c48080c400c01d0b802450107404420082d00c100c82481c00c00c0d1040d07500914061030f8240c001e840c1042a004950400259001c0c440944010404000ca2800a5505125106c01240507803603843c01c6160502c0350382d44441c00600c1c1030005000b1100d404903100480084180c84044040040c01050581801100046001e44036140114240e17480781c4800703c000300bc22034040480107402e801c040d12060562140407040d801c001402c0c40090f21904504481003902465420100d1074144280e21100c00d206c4a0085548012000b1940d452000100c8002241562007a0042004401d0440130802517000e22822244402c07945140907040300e00c0070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 525489712 1250 525488462 525488477
    0x8250b0c0c150a150e10090b040e010515041b08060f010c02032b360902040905101406030f091c110f060112020405060411030f1b030c0702040b0307050406060906 71
    0xb4000c1c5040100d003031750410300b0072280d10010000742000c0e23008190004070281005c940d000e82d42d003100c0e00350b80098548400b06119400e100c0f81d142024810000030030180902c0c124015100f2401030031144024040901522003c0641105039000e8100412081d6002e0100e418400413205481c1c000d210a009900b1320126889100041d18412001d1222078000008000e0039407408001e5042220641c80c0500c00c217500030300c0700060400e03180c0f002c5c10003840c9551002c2064a8800f4428082c4506904011200040100161005c0d1256006d49511508038a03c44a042c3c032282210b51900c040c5102a2955204e504031030995503910001c2ca0f0f030030588000403501044010041c079501c418090007106c2c014a419100760025107019045180c00070f402038000902c4030000381c030000c0c1c154001c48118000300349007818410281100d00c407020f05044c02c00d181500714205001255494400c400c0007038812900d8241056080c2d40a021140081c80028400c010499507150040d00c8118144540404100d50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 525490962 1250 525489712 525489719
    0xd0c060e01090e07050a020f01240b03100611100221060109030b1f080d0f020609030a050904020721021e0a05100c050403080708250b0c0c150a15 64
    0x46400b2010343e20740705000059940c9150048440360081000702003107218540112944000038424075145000015500c011220804c0c2d0440620b02d0b150f0010305901c60030410030442103c520200c0050314401d140480c004218003c103117241c2100b411490710351302d05c00070b06a01d00c0c11185400d0244100507450b00d50803a40e4401c01960a85d030350740301c09070030640c12400141d00e9050369040038003d50b030a0040700c60b0150701d81c0945460a40d094041102180000036107212190301041526800354a01c030003145455440017005020b4090041d9040c016900032425004110380e0035048a031040300c00c2030603045003243c0c0c600256518111500000000d9128800714110b000109941100c140c00c00010440c0300514040d100092052864650400500b81b00100001c2d25040051000500032041a5140d000800107071421620b01380103d85420000b880313143c00501c03a5a1000c0d0f0280300a02c8180e2140030040d046401c2c003411040b00c103114840141040b600744425032003001d1400c6590b1130351004686 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 525492212 1250 525490962 525490967
    0x180102030c070923070e10030e0f070801060806220305040302031b0f01030e0606060309120d060e180a0b0c16060501030b070305062407020d0b090c0415051302090d0c060e01 76
    0x40c00e50344240080d01b0310004803024180b034550340c2840001494001078225030a981e0f581440c0c3c05152441954200c0042000480c0003401010f0142103000090446401c01c03801205541050b0090322854a02140080040c0343c021820741e801141c000e4140d60303560803031940003110442d0a419142c03140300880c0304010786510a00c40d40e1140c5034550000c5c2290b48440b01000720a400003055101e4903c40e20950115506140024100441c040800401e401d0305228200c001d207640145a4540c074048900b0300050174100081d52240c2c40d401070b5182c4401e4564465034a00c91041c1280e40c5c1c1c660100d0840310302081920351003103041700c2c01290121016260035000310140c80c1c003910700c4c540c860307110111181c02c4c4c00340c14109404881180c0d4003914101d6240e020a602440d685000d03a201508031b800c2043c0c141c014040491400405c540800c21083e8003000d600c0300461310700525009403040340c004020010941c4c12107000a2000b0088001c1c46418580741d1708190741d50207000b00003030000020380020f50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 525493462 1250 525492212 525492281
    0x301060f02100c02102a020a050106090c0e040207060b19080f0304030819090302090403080402011706060d02091504090504020112050132040e0d170c180102030c0709 73
    0x3c0903406000c81580000e10340c806400034483c040810f100c040452010584180c104031071895164001d41404081070900f107084646e1980285403035420544400e403e10341c000300b030707070714010088400603102c002ca401e2441c010204c01c100540c1101000c000191070f01d1203460440102d5550070304680002c03c80903035607501c074010f520005246010034403501c03c0302c080d24400c1c09002501440c109464660303c2c0c00207444141c09840640105091409000541d41d0280c107160030021310361a0015281840743c0840d001d44148c0040811b840d9020421002d680e4444640313482200304080f14644541c0c44100e045c00410003601d00301e011414440d42d188400790a4001c1038100c41c0d5955103040a50b03560401144001150400722407000d07040c640c0c007041562140700d005001c00c40407004000d80040408013411103201c100202c401006d4420402c0140e040c140126011030308881e415440400d2030a00503807840c003910b0034956081c003c1e0180030503010305560008503041315090515000382042c1c1c0c85c02041030f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 525494712 1250 525493462 525493481
    0x6030605030a06020a020f06190501050904050d2307051b030a08040504021305060c0d02070603090506040f021c060b15070f0308040219030c30260301060f0210 70
    0x1604000c8055000c0341599001e0800760200c0e00580360814807e44a0900303000b01250440040001e0041e0b20390000002e10501d07003d4003094420f00b2a500301a19440e0756003c941c00204108a40300b0401d80300140e1541903129041e04003850991916040c4c580320f51100d1400c03c20b68422095403c84021528000401e600040e0b041801e040c0781c64100070a21000e90301c00590000a224603005c0040d80e502e070040209900c1401030003801c00700e032890600904040303c0f94850000c0600342410000800c0c8081161030f081640915425844001032002c01c0d06503031040ca648050101e020342c0c0c40280062904007841d1590121031600031040403800c0c1c000780c0c0c09a4200501000900021000000e009801c2e841e0031900081c0320940321650300c85000224986500219100c2e01c0c15502002260300ea040010214808902c50200ca800e46034078905d00341c4943c3c0b0010b80b603450202042c0c030f201c25190381100b14044c401034000b40e80b07684990740035000074a0141a0801481402c1e5074a110b11200d100c4e07004c21 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 525495962 1250 525494712 525494719
    0x50a120b13122303130c0603050c09120c190f06050703050a1b02040c020a020f1c03051b1c0225060302090612010e07090e04020904031b05160f06030605 67
    0x1200b94080221000312a14141c10222100c0c074201014848070400650701c503400c03458020a600000303180c04807103001107a1256040c50b040105002c086581711b0141c0b00c0354131003078513a04108404045410720308010042c00310f4014100545641c2c2d501c00f0b0f00080e00c19140e41c0751000b2840c0e40da0300c40c111034506c507189000d00001c0060066499483c8108200c1500096003010380c101845250001011691428103810140c0c3c016544003086041001e00d24a40c0101140c0c0c1260302c200c0d00380c201000100300c060040c1000070018031002500d09007440c02d8183c42104040743c5400c0d001551019400c0c2d20100340d1005031040d03038183d41040e904440c12104080c401c0444014603468501c059002c0c0d04018001548800d0034410340c91075100301d0031030748d000b0849650b4400040c102440042c0000c982c40e001024810446030070480961605a4603640040d410715008040f8404444948404820004004d00e0b074094240c1d130040d40940060300000b503502d8800005c2c40b160340e034081901122624851543c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 525497212 1250 525495962 525495983
    0x1a04110c1c0210051e0906070905030a0809040504020d06141b0702010903060506060c010509010c110708030304080304060905010905011406060c0a0b070c15060603180b0f0907050a120b13 82
    0xc003600f10b0700503c2e0481403120070241102d404c1d4607110410082114403100da070340001d04000805d640100e007070008080c01e40140c02d4007541c584480c0420310400c40d04900407500d920115045440c1c424140310b80a400007400c110715010003032840fa03100020388004001414524000500005020407200005c0c4e050b1501c105852959680001821340104400d0744500705100103c050300c802c1c0070300c0d4403401d20b500002511080081c005440c01c13101c050460310540c00710b4004e0000e1000041100d800c02d400c060683c0d202c1d0744d0307894410041c04801100600550911071402d01f0000150803462446880d400000d085541d6201445058004c1c500c0e0751090f90301621482010600e07174034074a504103a007464003a02c88032054849140c1c10b4283e100703c4681c1a555a81004019814030074007001c81c0c2c1d000040040000030317446d44040300001601c00c4845024102c04112031090030060701c0002c00d13019060250351079445000c403080c50449003064907220031301d000140c1110048014141d001c0d41c80190f401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 525498462 1250 525497212 525497233
    0x1080601170405010f0c08061005090109031103011d0f07270f0b0916170f0c0a0c0c061805090412180918140c131a04110c1c02 56
    0x422040020b00155159540c075608107454030307000d000b0703c21712130031503150501c490418900b031052003080000400d0130020240f1980241d03a034880d40342002c40b07030881d0100101da00c0c0100006e004007840c0d030203801c50044000c14003814410108440c0c0540c421181a40e41556803041880d618541c49820f4400403014880700300d4560806a11902c0c40d4000d0b010002500b0b43e03004045180c180c029907407080360703001c4031040d0751000c1c0d4409050100110000e1290f011f82c2021204c400f65000d000e800c04030030b80f101150344021b06118450903028250440f0b59007089954405029022000506542413107040104001c240b500f402400c00d03003d01d0f4022100502d407042c007102100d0b4900e10410114203107414a00001d281001c5004007403480302100031643c1c00507060700d4100304201d00b61207424825040541c41d007000380d40d0b06401507085411800301041c42e100c9900600d40c00e008500e0715944c054030380284000404507076805070214071120702c121295015110030040324211444076107030060b40301483c00c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 525499712 1250 525498462 525498497
    0xa030e1902031015090203012709050c100c0b010e0a0c140a0509060f0c1b0906010917121201080d080910090c0b0c0a02011206060903060207050f03030405010c0e01080601 75
    0x1132040d40403486508415215100d140590b4420b900000c200c030281020851031900c26000345160444c18a01080030002658907035490b190001403040c0b207021040103c007140c601644011802591008800a5079031715010754001c0c680040d614006c445151924084002e40603203443c0d0409000a61128100013001c0c0c5c04035401da100c0300d482c0350800c41c2800300c141f500c90110302810320981e41002510b40760140c3c150543c8407810307162002e4440c54200341407040a0340c2140c81c41d0141c480240e0f08209904218115924010300010050845c420000740050202e0b01d180095050380c44220603100c0002d1130345000c0340c00c4401620719584039002902c0360806e242ca654084001c071031241c84500441c0d0303500c2070102d000d0340041d01012001e4220411440c21580e1018503014580c424060400000e400d02800415a44040c0401400079a0000e0520b040c402d04021f05040d00700808116540c9242c00c0c40c095029101050000020030200140341d820b0b580500703402032040d00c060752240314107422112607 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 525500962 1250 525499712 525499721
    0x1092010231e1801050414040518100b090a050c030c0d1b0309020f120706033c0f1b050703140f0c1011030408030406110a030e19020310 60
    0x40340d06041c010402e0424122010248008020440300301c0e41e10381400510a100f150260040181006000c000c28008000003060b1000601025100010346a89200241041c160303080219103440c030412440110403002078100e04d054903801c3c2c902080903154000c087d03040c4c0e803042c0c868224012003440090f01d442c0083c4007a01c00d07190803503408036056118000e01101046500c141e40c000a444440541c19400c1c00401d40026480668091466070b508140d1070352100c00c2c5026100415888546402d00e4075001c040b081c1e9010f08103c46c44110002d05107203121700c15650540040f045041c2000104408224402c82048003801081c0b5503038500155021102ca9000880450502103c4c40140000300502e0000d41048400b929400750b558402840b241d18085081e80180c5046007001c42403840c90a090b0152074000d0b0707000705841e450352110301c0d00c4000780210074507482e015440400c2d4003070074030762507001200110341c25070070f41d602e404048039808040820502c02940540c4200305240c01088a0f511 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 525502212 1250 525500962 525501017
    0x30405010314071e1b0c1410020d1818020903060a0e0d0c051011090f0307120602280e090a0b090118060504060f1706040c120807020301092010 63
    0x400344245c9410500f1403041440034801035039200d00070001440005214800242e99030002c846100c800051440002d6035028111141c200700101d0b4075843c15051194200b10000e0003224242c0d000031007181410400035048032540c40c1c4244121008100000c1e224403c00e904103403544085d0040629106041d01d0300b902c03480b811540c1c0d100c4c4613400c114001c1d1b640b05500d880000c0d1034805948807984000c20200b0450394940d54400d0300541c1c42000100f0701200f03503030103903079010402685071000034943c12445a901501d034280658140480b41040358484c0940c04524000c03200070074140c4400b809402224000204590403c1c1504c0050140f07070b035a82c450300d0110b010414003244054680c1c0204059444ca903010141c10043c0722000c3c42102201f0341c3c2044603004040040c4160305c0c2c03a459010b14a00f451181003d052070405040d010f00005508944400d41c028000388140c1d02c4600c0e24280054a05045801c0111495a54200741c03030703c112001d81a0045a441e1032200041401e890107c061400303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 525503462 1250 525502212 525502217
    0x7020904080d05040c1502030f1e0405030d090e0a020f0a0e03010617031306020303070801030f151d010b010318060e0708120304110906060a031517030405010314071e 73
    0x30807840729000e03a010b000d00c0381e4410800b8821503446c1c1122803041c0103980d035244007550003e220617103030411044195101050240c035505101003610301031840b603101e0fa800c207541502500000204246c4c005004104892000c0ea003271019a560010190403405035100e41010300b00200001e90056214100710410800c00070000200701d030707075980300e1681c804009003c080c403500003040756401840c0c0c16601000400d0280040e51071481c0140005005240501000740440700b0303080c5002c107100d007035082d6113a000302c81c0908002589200500014500d00003a40ca000c135820046140e4495219010b0044a10b40c00b0222030210032103540c03510041c000903055040c5611030b1081c0000c43c000300300513005040f1500721090745d60b4245424140466840106028026452032080c4080c5441e01c00c21501c4d244428540001c00052036542c0c2c020449442c1c1c01040e1040404c20704040580340803009104a500980b0100309151040340c0b00460b82408441040103d604110b42042188000c550b03031301c00c00c1c880d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 525504712 1250 525503462 525503467
    0x120c020a08070f05090606120c0d0f06090b040f110306011b0f0b0f070305071707020f06041110090b0d0506120f010203070801060c200f04020d091707080702090408 72
    0x848a05281841c941d103d10502c2c18000c1e0100110b00349006003680240003500c1441c0303056a05100d007401000007800760060780c0c00010340768900e02c509500c083c112002c0c0c203409000c100c3c0d4580004000e0807050712114401c034505403581101081900c0f8042d50403000500705030640e6644001942c501c240340400c005000c0781c842080c4001042e50b81d400061a2107501340110905080c501d900c03203000b000744840181440e010034006540c0e0484906030803010302a1350008181d460113422030a02d00200310300721070340c82044140300030485a50002d068078602a280c1c0d5581e01082401250340b00301920844821200401a40d000010180c1003168000300142c00e001c410001116540d01d00b500070000c42c90140d40c00b0091064440d4080e50203401070441e4170f00101920140e464040380c072164140a4440003101509040d940d882d600b0300c10b0040c140040c42107403a00c810501206c09411201030844000041d140c615118115100540f104075800c01986401c0004642c24466081c10107002900c0f1404c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 525505962 1250 525504712 525504719
    0x60e0f07050f21011220060d06120b060a0819141b01121107111f08040605070509010e040f061706390f1201080c0301051b0a0804020d1208070807020307120c020a 71
    0x2801527030002c00340c505214402d0721035801c04090314040a01042e00c11840c1000c00c000c406400204401d4604401c0d006240e200c0480ca40740c2c580d5203032802100d1540c007a0b1000303103040300440a0200e80020b02a291f043c02070510841000031600031010000b94103100340700203130100d14495000991030740c01420007060b0010303a0b00c11030081140701c90348900081e074400400c010425a8040d1350b81204407030406d80d04003080d0a00103045051407040c20350095580700c50f80b41d030140c450741003400246442020041491601c0c04256101d4800725440010341860300d100d19488003c612601c50743c121180510001c203800015204401c0c1e0001540c506156014031011500841481d40d2034002e18880c0700070103454a1030000c0c5070070748a000b0600a0f101030001e4504807810603102c02c41300711914034500348260f81d50318070011340c0b06908880040c14200d03200c0c0c10710b00c803147c101030f01e24058452a240d21060f984c07111012641c07445009802007116900d01d2039100d5843c0030f0612004500d20007000c07814500d44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 525507212 1250 525505962 525505987
    0xb1003060e0607170708060d11040509010c0314070e090403030f05180c040b15090109090f0c17090a1502360103060e0f07050f2101122006 61
    0xc0018000c80a8108105100300329401203800d02c444c0700d06061a02c1d003483e2402d80905019402451180203200426100c010400c0b000641c0c61502d8006004005c0b5041c610051030003490110f84072030100386031010308070310b8060050365240b0074805c5541d1011061201020b20040c0003002d44201c05041d1655129000c0452034090640301d004440c0903c00c2c011620081185031128111000f03014610b800e00070925600c2e200d101e004000e04402107941c3e41e00082c00100d03500c0758540e1102100d2490302c80b180080d20556000410000441d6440b0f481a0b250040078044400050760307030091640c880c0f41e8040025900201004a00105800050030440002c0c8103896a0301038001d0002400b002807140b4507401500f103140401d001e428a81089402d0902d2540c003101c1e00040d00c2d42900b96410000a014a4410021030f0701c1001c0c143d004603100ca60800052044280c4205070304440e070f0940c4004078840f07803072004240c4603e0b004116400c040c4644207241240c800c40c5c050042d0001000c01c10018100b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 525508462 1250 525507212 525507221
    0xb12010615080f070c030e0d06060e040204050603030a02101a090907030c081209040b03011e060f060327030e120c03010501090e120306040605100203120a15030b100306 74
    0x1604100180054000c0300000c1a110000f81181d59111461090100140c2d01094090015525083c901e01c00c3c52050002107010140407070040141d800c066000c14081030180c0c40c640554401d540a200c0c64540c1070805880f40940c080400069002200c064400403507074012041644c923100c200745c003480302240030072030f4100222000000e50380660001c2040190340d8100ca0300600502010b806425003079440e0300543d22440b8a118400d5850b0034100c01c0560b02980f1020030001e410089000303910703849160802800c00b5114034480240e01a00004015000c3d003c0c90001030903251000c1121300d29540c46c4054540c0740c500070f0701005105000d00c041034840014540314800c0c000018240d00c54200105070a5500581100050b542004d00c401c21803200040c0c3c940200d08007400b001e45030b96510002c54024070741d50341701c55401804085840d581e903401000030050381d0412007001400c0e58586c0101810703145e043c10914084130b9414002c2010400d40c0442d19017010010042940f4640e0380d0b1078034025038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 525509712 1250 525508462 525508469
    0x4031e020d1b0e0702010c022a0d0501060503030a0f020d021912030905030c0109051207080715200a02191e1b260d09120501150608060f0904020609040b120106 70
    0x5039507d85030300600035010018a150031f020b4100c01a124490b003403082002d1400200702502500c81e03809140300b000020341183d400b80a02404617903c1e044400001082640a46130090241c0030302d442c0481c44920215414507042180c50910790300d0182e6980d84a5002072001c0d800c01019a100701ca1030018a050004064000f0b40400206002c111030034040e007421024108104405d00401c003a10016a143e01520300894012000b2820002c6006801c4003406000305810107020060740007494a10b407090140110454a600b00ca04111041107080800080030b14058410600c0042000c9074a26001c0c245540610851003180c00d010740c00960344c801000d64004503418030210803040c100400101c42401d001007404010b014450401c58040d02240c4d841c010218504085608103090220941280c007144004000000d00607598000050500f0030503510f151043d0b0120283c2500c904e4a900c006018130b4004211918150311002000020a014221543c100e182c0b0b14143d0035180b02840b401008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 525510962 1250 525509712 525509717
    0x10c05010b090c0d182a082b110c04020a1b0501052a03071b0803070207050906040c021b010306032112020c0c0d0503130b04031e020d1b0e07 62
    0x2a1500d0080340310541e110000d130781c3c103070820017031400022a0740d80200c1c81e20305100072140301071505101021001c0c940c00740c1004581d4032034158403d8041c444450380405c071401140e003c2d0844050428100e6a00101c03031401c4c0d080e40d102a050351040d00e4164020201c1c2c0020382070548100407022103070f024a0110b107a00381d40301e95541082054442140b60f0b2003682c0203d0b9003d9401c0c47d2103003602c2043d2400081c003110200310004840114504034112142680d54120181980760301c1d1454000f0741c1c0c0c010754000c080c090140913001c43c943c2d041c01e00640809a8050f00900380c0f40c03200c2c107940303001c0c00c6008036840d04240d01c07000004041140803018008820540c1c01c403800b5481c0017a006000e4000d86440d0003107040c81000804006040070031138595a40040390340d0503050038541020703861800342c0424103088040341c40c400240505140010400c4920070304c1c900442400d80e40c82d5049103032000c0300c00b0b0b4022000086d064001510030a5404004c406a4400464181c5a25601d194440200c4081c000b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 525512212 1250 525510962 525510967
    0xc040f020904060b130504090b0a020a0e1c0501060e09120310031b031e110904021807020d020c06040803030c0a1103040308091809030f0a1e091e050a05010c05010b090c 74
    0x28251760141c5001620301a10103020742641e5954030a040000102402e60203580440d0700c1082e01e00c51402140100f100500384408038132001490b180c1d101c2c1c6000d048459601c0c000d000119841040c502600c60000940a00040c580010020720154001001100c00040300a0044000b400c140050301d0004550307050003c1e09421413500004c0b61000030020350180b52481160b50001d04645402c0008000075140104070351a45d1000c5030002d00504001e035820f0243c101046400340e0700003034030440045581e084458404410040c000c1620072409400266041000020308003451308000b442400030302d04e8504003003c2d400900c6420340d04640c1003200c2e03007400050301c441030340f5100100d113951541d01e442074038440c200307000d2955491083c005842c031945004288141d482d80601843c60140510250300b00341207001d0440142228064068040816008901142c960304550482c0d0150b44001d4000b1010301d003020015102c10030745d40c00807201c039900c1c0e01214600c0d4480d1204036004000d010607064 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 525513462 1250 525512212 525512227
    0x70816140d0e0f30090909012c100b0102030f0d0f0f14150a080a050a060507020d0c0215210907050d05100f020f03011d01050108090c040f020904060b 66
    0x60400700044490340d140da10121074a0310300219482c01c098400b00c13184030910040044c107042000d0380079010300113a101e403040e010400500c8041d0080009600d01b90300180c042440786d4622100c02c00018051005035105040d01001c40007107501c001200b40e81401180d0130440b802082c1d401907800300020300c00d00ca842d203101c48050040d90040020741c3c03000d040d050029840000c000074000000030008204054801c940b10302c103484a0f0100b01c090940501918041600c0b41043c50740c901305074504844452400002503101c910100f201201100c065540c07203890300058003009262010a42d102e02119070407c402035000c00040104c00c0c0300c86184c1c001024618004881c2070404000e80d012901540e60113024900088000c60006610881d04000044e8641082d101c00003e016070401c801002d81c0000c00410342c546070100804402d8207035180000c20360780310401140c440c48181d880001d1544131482d107003098038283e00030400342c00c0f03500c900500300140880010180ca40070f030312010841100140b0780 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 525514712 1250 525513462 525513491
    0x100507060615050703030b011b030302030105100e0303040e04061401080610090e210714060a0e0c01080106110f0111040501021e2d0114011d070816140d 67
    0x8a00804203408050360496003080c0282c01e41c81a134400404050342c0d296100c1c0070381e005202004000180036500d2140074421b282c042c0c001c0d03100f0301070944100041e0100c2d1401511a4611005a00002c3d01a6080a150140203040380d0700241003214650b0b100c9507120344c0d110010807001d00034129100280894109224504203803121504017168007414142581d95160000444880c0407030780601800e11a800c0c7c41c1c0a401b00c0c000d818004082d4036407102d802c100b0400003e80306005d088094400c020040c0007180d0543e43d01210110f09021403010740040200500960209035000074580988001c841040b14403802c440320b040c014602d15501043c288040d50781041110110807160007501c0504140b01c403001c2d0b0312070441c0f413446503546501890004041c02401c0446206810a00a02141c10041c144c0c01c207102d801d00581402c5044140611403101007481e0190042d1101d403106003041d1178a9198415040910003620140441008a885032842c513000800d250500c244002501d5196041270 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 525515962 1250 525514712 525514721
    0x903030b01020604021f021c05130815070f030b040905030d0e0303010f0509040309091a13051b090609060c0a03030e120306091008030a020f06010f0e04060203060f10050706 76
    0x4007811548200b0412006031202d110550075040e0010501d0910a65001c1c224034162404440610441c0f400e0024041250820040c00c2c0c2c50700f503003541c030000a8592420b0341c0d587d007410080d01c02c4105002c0200c1d18650291003440c9801000d850301040500c640c5011034140d9038940021141a07000040300d0b089841548a170b43c0d0440c1015014518552403da0300603044d202d0ba020302c1740300d42e075900040b80801d0701410381d640c0141508501400360207003240e8602404044150030034000c10208030359407440d225a01c0b803544560358220096028401003141c40c240c0ba04801c60560b0042c104014940e482d54401020344204403098000f03101203200e03450000c00f51807030f1031040100e0b5840380000b00b007450000419660300031425101843c07942d580144030762011080382e002052034000026116000c2e580450216034220b048800ca9040e030743c1e90759a0b0a160310851080103815440a0b006c600054241e40085402c1540103101c0702c890340d01c240c005030b90148601402404540c0000700b92042180f18000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 525517212 1250 525515962 525515981
    0x307032301050a061106013b07090f080d18090908220e1521030703081b04030f0204020405030304061d100f261e0a050114091018090303 60
    0x7004030f06004203845c2e01e60740d0300c81030003040841e1003c03141281d8100c054840f10710201d4403051900c50f010b541d01c080e0740a8848142c0d83d00002400510001c035400040c40554401c44505400030004100d50480890b1f04040851088416600d1003900007201280d902070056901d018410442c0e40381d0284c00c1c0c900343c00c00314010b206d07118881183d0070410090380f1840c042d0b00402c0080f00c240c40740d21078000261000404042960000010309a00303a0b83c5800001030058244652100851500ca441c0c14144104829100383c0342540c017040b0510010f1044035031705103014805000503081944400009045801c90f401550000f188a182d0260000000e1440051090141d07079081c80240c440c44014062a031814812040c820800443c5810790010400800860801407011246007019540d103411208072071400c4c8610440100414603048440c13140740c0c1221400709916000d11003100600c081c8043c000d0a106a0300c03030702e82c030000701d0401c0c0801c00010360074403403000900c0500f20324010781100c0740c041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 525518462 1250 525517212 525517217
    0x5010e010204050a0914042303180f0f09060d03020a0c0e06010f050301080a3e01030f0612060c09090f1d03030601270504090803090105070c050d03020307032301050a06 74
    0x1404000106c03022821290816040340c0c00d50402c6c070003507105203409603092941280303500c80000c44001c0c41d07548030040c1c0404503044410118a84040c020442c0024003c072109600200110108115150200082e40d9680c46401a103464a10544840c1d02100c030705d610111141c3e8a001c200201503a010000e001c190b56141070550441d41858809603443e0030041c002005080080810082080d29811402054540f08420f1211015040300d41e1030100c0d81481c1540400c1c02c1804145260072a401103105a801c004000d104034484c03510f81c01c6c050b2002f8041c00c418408080c50115110095004444125078041d002103455180e65040402074601c5020841850b0814010302c1610780c2d1000398400b04d00b62190411180c0d28490044140007403041c0c0c08103611914043d5141c041191031000f4502c9406180020007181d078882c0d80a445450034040c004205400044807440414020741c013031070f0032860314540054001c1c01c5001525008840e1b401c1802c4880384000100310078940403400b07074050946403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 525519712 1250 525518462 525518471
    0x100609080d020c1012020d0c35061f091a04050618131d150f040b1e010e041403041d0604180c0630051305010e010204050a09 55
    0x1007900a444043c038110003441403001d83c510a000a200e039100e0042400544404c56a404020322050010b0100012400c0818480d41d1b103000c0311341c801c09801e40d50103001e04840000c400d44c0481d6041085005103065030082d08080b40c0c65890241681001450103a5210004250709050484032031301c0302503091071034108003040203004540303031041078603500314001540e1520540500001007801c012401e20b100c5442ca009052203a0340c10700394a041d15100180160789451008036200c0e24641002c42d09007182000c1600801c0005800111180e8403500e208454100140380c4d200000f80e910f400e07400b400105c0050070902c82881154000c0070f0200000400651405149c910401c407031005d004079443c621080b40001921a07111504500741808030300c140f0128070311851601c0a60b030002e0740902c10010760f803689202c0700d003a15a040d040162941103c9040c590b50081c1c0000003600000f44501c411001c48846880028400d0090400c42d030041000903031038508080a02113404050350103560b0840c2003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 525520962 1250 525519712 525519733
    0xd2c070302010e061605010f020a0e03120318070504050f090606010f0818010605030303040503130e0c030105120a060c260606071205070503210105180601030b0d0203010510060908 79
    0x180080c080a401a10030f1368030b5089a0110100f00d20403200c01030055401e2440c40c0c01054a40e50046c01e04c00140e48070a54400d1407201030540d299500085901070700000c2020860100303c0d007019403103140182c1c08a80d81203455002040070b503802074918410300c0c10b0800502403401402c2c402181e1000081c03a00b02c2412400c5000200000750140003201608200d241020700b0450a40080020301070103811a0760301d060910300141e695000d600740041d4281010343c00b040e17850076541c0c014000d20600c0d0f140c41c00d503420101007004000c001c0071070b005103100d000403010000380c4078003d01c005002c503070322502c904d0520081702c81e4140b5903001a044c1c140c075210080014071740d2160240d0b030060b500003070075403d080072000d4141d80510404401820500c40401c03501f0b0b0024030b44c840395040c1c9441511941c60399036110140031480c61460800343c804032102e4001941944607034441010b400c80203015103c100ca26801080c01c4840c280c4141103100422003050121580007108280200484c0c8000d02a4a08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 525522212 1250 525520962 525520967
    0x50a02070f2a080d02060124180503060f040c09060b120403020f070801020a030632010306090617060601050f07260f03060a080c060412080d2c07030201 67
    0x1c4040c4020300d900c90724601030810a036490004515100c007100300c10b101d030381c0b500301c80c50b600d2401d6528a0f0040c071032000045089203122040c2402480c90305000c88040d1041e56060b5030445424007400030320310600700d00041550742004034a01525480444880364105420b14082c0091190883d210013420f000d03040112904a404076105841c0303036400300350302d900c41d490120b0820b0700284610b40c46119810001c601204194010002c402c0103440800c8100d40c1c801c04005080685600d41e16200307400004402400040c070001001c0d02c03070515000803480d4841c000030085900c15003005032400360401d003c081c1440c081008503049102420002d0802d250703c0318000b0984079044000784101c1c07030b401d88106031182c080f61f121040803002d03407181d45642a645008040d40c0046950798454012110000b6411102080500c510741d0041c1500e468a4104940c10042024046040364034400800c4902c00e00741c1c80d803043c14240780400c83c01e602241c2d220303180e080d6144030326545250150083d50b82080180e8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 525523462 1250 525522212 525522233
    0x10020f0d0804060e012c0601031502030702010b091317091c05010912050d0b100827010f0e0d17011202011e02241005060304050a080c0d03050a0207 65
    0x9200d1820300301c039684900d06240500030030b4006503655820b00001e00141c07003803c00e0303000d124030350400d2241600381d080b0700303503540d8000a200c050840010f028500303019598039001983d0000e00790001140c0b2403402004100003242c00c40d41ea401c1b280d400380501003004a01840304000030041050b09040090740000501d41c600010424407130440704090640801c0b000307402c6480c2c05600400c0885009045c8400500341d503115080d0140030900d040207060340c500d8050000002e4072115900d0354a50b59aaa4040d03445400301640b0b030000c910000c084003083d40007402050300000c601c1d50080b510106040d5490710701444011401d0034403002a01c6603027010a50b500403811604200303543c500318451400145d0b8403a00d500420040e40720030b004e0301030f250f035000901601a031074bc400e40951201400c00010710004020741c0c0f0315100300d4440d00d0402c05481c004015641241c0600180c604c040d081f0f0ba0307060075952003007020580c07680141c507545076000c1c0c05128040e417006001606500d0002c00390b8419518a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 525524712 1250 525523462 525523483
    0x160902031009021e070b060f010320090409020d060f150b070f0602120a0606090501022803090506180a050604050603040609240912090503060f07022a10020f 69
    0xb0380c0c00300b440f4a2611803e00b400380c038201240e03020b5548102e6410082c51010080710900c5c010b18074080d010000b0f501c0b920444503485400d9070310341c1110340182c03130926480c1e10100d080e660040c0c0319540c1d540035a032000c1c1100c1006100710000100e1780030f88203c640c20b6800955401c20b1040550300b0030040200e0040c200c0b128070b6031012941e00042000d1800d8402401181c4400c1c400c0b000c88810030407980080e0f48501c4c02d96a07183c41d21030a96548500482c1c0c1c8102555405484060b42010840070300340702d6210710b00e61403007410948170458407200400c080d43c21905128084150302c24031034181d4108039410001910b01969200d2810b810003021490703620028000074180382e0380700740030b800f407101130712440c08000304d1800172410401d40501c048000e481110340960f0506000508015040d01500c404000c445014000c1c04660f13455000301520400c0040400b010b40c011001d66540c0001c01507001d546004019009982c3d6503401020700c450910040200741c2998404059241c0c56100040c440284 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 525525962 1250 525524712 525524729
    0x2060408280507020307090b131503080a05070b13120f030f0204080c0a0905132004050f070f03050912130b2a0703020108060d0201201609020310 64
    0x1c8000d19805501404039100500e412951100d034500303182540403004003512402141214035154481081c042180e10402c50a80d10100c0001c004123800440d400514109140d003480700d03c0e03a9940d89411030079520200403000018000108030082101d149400c0e9004011140e03003044601155646e140a0500314020308240042c4002181c030310780c440d411988031455002010754445a542005680d6801c9000890b4843d420a020101e40c0590301d11030345100b5010303100604191134450b2a00a5943e80303802450b05540f121201d400e10989446c000d2501650214a00b05a10b140c0f100c03000300f059080d131007603004240c10041030041220000420003400040640c403144d503440f1420010205142980c0301000744500403411054040d050102a15603c40e03503812600200000c0111070b4888440d4000203000c03030040c0c030101d555400c14284c149117075481810b150024203103644131a034445014445468170355000749400040c0f0008601840028505802c055045040890401c10031450324010080e2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 525527212 1250 525525962 525525967
    0x1308060601120e0f0a03110c03030910080603030f04030c06030b090907172401050a0512060c1e0310300f0501200403030201110324031e0f0f01050702060408 69
    0x4203010284100002140e00c141205d81e010898913000c1d140c0c01c4000c400c40f64600540300c41c6401030501004032645058000d20300e00e40000c095505039120300c00a0301d020313090b100a22607101d261029000038405103020300d031340b905201d00c0c10200805039900381c1c401c40e004a580101740543c64400050800aa881582c0d1000724050381a0500345400024810702d80000c40031514440c4242541d051607060300c005444410442e40c44009101392424a480c1160150380210005980700a100300a0506140d1071501d6a06030003222007000310381d40081c0c036a4100030f00340f250100181c8080c0c2c0340c4510420744000300400c1c210b4081030340f6602c11140090103844841950800c508110080d4411100d80884064840d0550450645003040d5007043c042280550f20708030b0800c0c0d0800080c0c00b6684940d100e074114030000d2035503010328056412102d0619030507100e0840d0f840380e5007030299020249440e01030b0007840d2071210400d40702e2410803100790041b80341e4503180510099030780c0801c40d95405078000100f240e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 525528462 1250 525527212 525527231
    0x15050c10021c09151a030114010503032506060806240f010809240103031214060f0112020f12150d1403070b0708010e0a050f06100215010308130806060112 68
    0x58642c004141841340e4500300795140e1070081c1000b140c16907102030340200194001c0320100e082050081c054190b0507070007888039147c0320f219021040c0b002441000c0460440141c1d0791a80300350341c580d402c02d03401c54114000b08074035462015200c29500441e0a250340c0d08901d1400840c920920040405040111110000b15805420004108807050140e024400e1540e42808010800d0b403e020480c00100c0c260a10707640094a40a41205050111064a1203488040c02c000708540400a40c3d4148000c034001c1c000800c0d040d20142008013041e101d041e5032210101404001600e0040901c079410928040c03100d135540303c118202d9200d030b602402e450b041142c0c01d6040361a500400301c00038007400c0f07207504214541c2e605c00b89540c1202d60b8002440c005846903603000b002d841040701c00400350710311200083c0340d92624000222003d405401581e040400003a0300c044036440981023500d07852000030b2030000381b41000509600801c881d0b0003510003800c1040000305a89810720040405544400c07014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 525529712 1250 525528462 525528473
    0x4060c0317040c081002031006030b19150201180b060411070c121a0f0f06060705030c0a020f010f08070309020406090f0f0501061404150915050c10021c09 68
    0x10070340800c2440520760900e0149000704200348640514442c40c0116501c04000e070225009880c00344440800184003541006011030003014001d040c1035014000301e000046529903003220b600038280320102c0d160042000440a030a5800c003001c0d030250010100b80c0e40b8007040c032046200c3e4015400b210003048241c136113040700c41c81e03015440010b04500849100080d00100d90181c0048117481544111607160b6220064008040304846100d0700480103030004224400a030081a8041d600610140c205104d50710b60918503000114241c00030b62205042c1c10661a00710303200e01891000746009412400f00b82001407184c0c07800707405482132640358903000c4215521904090701408440800304070680520b41303501c0291003500c24403d0003518203400812910312900b80e070b0007142c803179510040c506841d150004921407404400a0100301d6400c4000c50700d00c2003d001400c00b4140382c1d072581c0d00d40d50ac48203c3da040100c103007980c65800303104100020720784039480d90100c2044d81c01c8070300255050396401c08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 525530962 1250 525529712 525529727
    0xf0a090c0b040305010c0e060a0f021e0c0f1906080a110d050f060604140d081b0d02010606020c010c120e030709061403030a0e06030a0618051807060504060c03 70
    0x10820029032401161140014000d00110b078000d000a000e003ca00705401d44540e0400080240c000104001d00c10700130740129856280e8a550b80f0448a01c0d0707299014489036145e089101c11404c3c0c1100001e42d400e0b10304021040203070728007110941e40380c0743c3d2840a4200b40c200703440f8500034000c9000c002100360a80e580140c020a8a2040380c6940303500042c2408010201140d4110800009001041090400e0030607138060700e8095441e0315100644604003c114811003c00300d800000070070002040b51000c042442c040c440e2000103100c11010060007038251011a000502150300260104060b40e0703001e8048004a071300403c0d8180580b442c40000c503a507551110b00c207905403151880002c0c4040d44c2e68440f400f01d038140c0260307407c2c03507900e1000c064980c45032020410001e00115465103844c83e100000316080004070800145c07480d51554410040451b130180d19000d140e45030200401c82007020001c6690f40e01080107000d44505103034016226000b940185810040072100c6030041500400b003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 525532212 1250 525530962 525530981
    0x150c0906040620010c0f1d060405040f18030c02010210020309190305070b090601090b04050118050903070b0108010507081f170f1006030614070c12031404050705040c02150f0a 77
    0xd014a0b164124041c0026540e031140c1c2001840a101400c02d140c07107c41500c1c8a500000d1450380b41515000401000e1300c100b42d404142c0c103659503002c150781942880c040b03c00c0c41c0309481e039004814140c000641018621070f40100800d0041080001c0300a01182c0701c00e5880384a58006480301080c103044035107018555005054941d000b0a014042e0741c005480b50485030212000d114401034032060009880b8284542c040c40100d5924078580400e40340c01103a4060744000482e42048002d8490304040f0100fa4040c10351170359070b481407140e0f003a40550807a0707020404ca58020302110000c04010070381c002600c1440d21074044028062241b0005211880c440100d81c800c503804660446488001810203200866071289428560016801500c2c2024450002a2101e0803c0100c0e0703212803c0d80503c85804004140d580e0f008014450464224140180d000c2c0f4010101d0a041c003042c4412144070344410390a40d40010001c0d40c179101c80190203540405d9500d10000a44c95011041000c0c141c00c25 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 525533462 1250 525532212 525532277
    0x60715020706060312051c0209060c060a0b01080c0304030c0b0903041d1008070f140109030f03030e06071407030309020d020d0807050c1f030b0a0f08150c09060406 72
    0x50950305000b40c98004405481c01090030a0180e480c22100b503c1600c03a400005203030000403078009894a000780e0140c000850007070301c4039140614000055041030411101000b4507941c2c1d501d10310865911080c1c0950102d42254401d166083c1501d000d040c0f41d1030400d004050315032450010304001800d000340c1d0300500f1505004a1041103140c640c0000e01011251485001221903000407072610000e0060210f400e64240000c400e400c2014800f035400c10089542e040c00300100c0700200152540d00710710620b41c003035500054412800340c4600e00300580507254004001c2039100c0403040c00b44000c02c45150a40c9410000758803c403a2020540402ca20720010b91711002c4014118184094580180f00c0e551144c4240c48180c41d1031403c101c1c20900c3d1065880c441882d07800c01030b8a0a010340d0041d201d810004202c0040950707202e1880340081090b42003040d05401c200600f030028104141c1d22500b005220303c2c0c003070a091141007c04d0550080d4850705d8100658641e4035400742da180014203c41d884080d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 525534712 1250 525533462 525533467
    0x20a09020d061805010e0f04030201061511010b0103060f06050c0114041b1e030803190c030209010e030c0d12110102030703050f010501081003060b01020c1201050402091b040506071502 81
    0x101084010001c501c580c0b1000c104402000903d07600d031348152811ba8682d840d1401140c0c0303500600c0c190408005204806640d0f0f00d580100311030604a0703520708814081c0d41d5160f07800000001c0d45003035038040240d043c1414200b060500070800c00e0f040a070141c40d501e02d026030300c890401001078050450410301000c20407a520a1200384922094902c510440c14002d05000e0b540e40c0341c0e010f10b0711196054450100180d80414030029800038000c54000340103500d1018900c0d602510700d01240d008200d80004607a0000700c0c3c0700c05580104000740c00c0300b0b00304c015041070303005000425145030940f6002401190009580006940074a0740c8600e2030303604d0740003103480e85407186024000340382c10344001003180303030182c0001100e41c41042c0d642e100e51901e004052029113141c1d01c4401500640c030050341940540b260440384d0361030300400e46022003404000405c9a00b8540180004508068079011025846d41e402e09140055030045400b10380042c0d982c03590351403d5091546003507500880100442d07000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 525535962 1250 525534712 525534727
    0xe090c0402030c270405010b1e090a0801050f04030807032a03090807030c0203010f0603050309090901112a06010b0a11030417060610050a0e0f060d020a050408010b010c110d020a0902 80
    0x4070300300c1c003103413090701c040200e80d1302c1b514800c1d00342c0240500c10340000b403010348010b4143d8014000c0d080e02ca5003d040c280e00c0b182c0700c805903829180102c51851038aa1404208000e1583c4602ca807a0030523694102044040072f40c1c070454000d1120035041c20024103200003820b2945101340e201c43c90b0b072030300100040c2d02c540300c61600034504a05c0d84401d030b20070340c2811409010101c05110302001c03250b0020045161000d29000c6c800e406c40003c0140c19a0f541e500c104510b000c010344020b02c000c50a480f401c03000c0741141e420903003100341860b01c08503955200f54018032010340c81604450582510f802d004500c482210001459840b55402454001d08900b49007004c0440010f002c44c001c2404071810182040c2c07148088405002e2044070000081482503007814505064042a03426117001d0302451805640050312400d80c4e00001c24000006d00005040200c4002031282d440204000d203080b40003942d56450300c00e10b00060080692048041e4a500404c640e94200410001c00031004155200c142 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 525537212 1250 525535962 525536017
    0xb1f210e0607110102040608010509040609240509210711100c060e0d12090501060e090307020a14030709020c010e0d030c020706180e0910150f0e090c0402030c 70
    0x20242c0d00000451029000c2035a407a02c180207540603180c2e01d540f00c030303400c1c2e103842c0070814104809003041e10103030790f1500c40c100411028014600b480742d24800d0000304048001c080b800702e420043c0f0141d600c0c3c21415048504044c00c0100c0b2000010070075110b6254481400c08012600b00003001503801000030322040e1106401c82100702106014450030460702100201c2c1d503841b44456403a00340007541307070700c0861460340180e480801468080c1d000080c0158454510715141c000580700144140e0012510404500d0f0003101500681140b190560b6685410000300f9600d92983c012045415001b240c2056005425400070600f50f50684c12501440032aa50140041c0210580d11006002e440400300d407440c02203c80c02c00c041d402d2205072000c0392a0823a500c004c0344010b0031918507070195801350002415075000380b4403003507081d42030b80c04d085250031401805045294000d040d0320b445201000361400c00480d042d600e03040240d601503070b41d50b01d40010752a40d101c0c030350700c20141c01c00c05400d04188a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 525538462 1250 525537212 525537223
    0xe1809060708070806010c03030f091712100803070b06013006084201030605060f0f012709021c06050301150b1305060a02030703030b1f210e 62
    0x76503100d800c4036031900f007800c843c0f4520481d0640e0118102d0300c09000000d100c1d41c00050342c4c44410304000342100665403820510107000340000010f82000c148054040e40304441ca6400107546030740c07200d6251420012540b40d00507114090000d460001c0001e400e41d000300c804080c41e920f00700d11004d4014012113a8440c820301e000507502c2c201e2070118045a25040090451a180c5942c0d1070650140340c90f2246080c030071540038010400d84100c480000740364003c0510140a584504408650b0385171010030301001c103c1864003a84201042440440541d030881031411004208894103213400c4140340c003408081100e40d00c0303c4140744c40040c051001d0502420a002505020f01f014080c5c81c0e0344004041c282c81c01c0081c02c1061242c180301c20030060307000d00020700b183c1c42d0f69000b5080c2990b50b08001480c64001c9000a00981c200150480070145d1600ca080c000b02c02c21110800c6078101008000380718480860072800b0b21080401e00340c1060350003101c118500501034800e10501c10140311258456 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 525539568 1106 525538462 525538471
    0x30a0b04051018151e0b0c15010b2b06030507060c15060312110f06131403040e0a0b01030f06030c050a0b03090a030e180906 55
    0x5440d540280d91099008024070484189003040c1d401c01e0649040c9182d510900d80740941c0b092051101c002d80541d4114141d034541040d40202c1504448034035000a01e002c2404100300041c03103030000d4803070700301c0160020910540c3d03600c411160b418024007100302c5080305031880c40c20842c0419003600403031001042c004180d00d6502c6d16240e05000054010710b00040000c1c1903c014460894141c0620381105d0604101c010b1542c1c440015185415071880700304001000c0810142c00108004c4a88001290a450182c01c0408000c07140d01d202e007504842183c541805290100004004d0302c04440d6039203d00d440b580e450110050050442c15021818159100503540500296200b140095072064107084c000c1c90400303003006011080d0794026030b4440c0c0d0802c04c001d89500c0226180c803445a05041c50a00311941000094800032141d80c00041c0c040040100001c950000400c00d009 = true := by decide +kernel

theorem cover : BRFrame.Cov 525359712 525539568 := by
  have h0 := BRFrame.cov_init 525359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 525359712 ≤ n) (h2 : n < 525539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
