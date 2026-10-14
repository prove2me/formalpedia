-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2231
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:04:06.205141+00:00
-- url     : https://prove2.me/submissions/f5a384e5-56c8-4a7c-acc1-855c55ff6f8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 401079136 ≤ n < 401258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 401080386 1250 401079136 401079169
    0x20706110f0a020d050a2907022e0e030d020a17011404230906010303020105090a1e03090302031b011214060114040909150506040608120d020409020a0c11040b 70
    0x3110b0402c09100c010700185201d507800c00d15070340b503a00407c00c0c0341c001d084401c0d0b4000001000f072404030310100d10215071441c02414003000340311500364040700c0b081e40c0c495400303a1405681c2d64840f00400220b080c000781c00440707507000c03005858140c503ca014090f921900801c06519241d080140058000000340103154503003910b0024941d400000c40801c1c03043e0b140201600303500203400f0007002ca600042c407a0b068074460f40c000d00281e200d5845543d0f07288440c3c1c00040040f603540805c03010050542051012480c001c0c038012080c2a600d4010a081c100c030784089451500c01008001241e51708850842e5900703007142e82c1002921803c28104088e41406066203040014400380e203241c001c2c590701603030060400c0000402c4034100901d0045034003290602d00b100218107000024031145003a21500c81154840030281c41c010b4803038841c90740b443c1e00c104680c1c120994240710100300e0009a01c06007030201a41d8448120b14003445c00c0080580c2d610985d514401e50405200d01c4203030f00d802c559903204c07014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 401081636 1250 401080386 401080399
    0x110c1603150504081303050a020f0f1e030102040b0309030a0306080c010c110f0a08030d050c18010c050f0a1a0a090503040b070c080f031324050901050c0d020706110f0a02 75
    0x207542c589401c0511172000d903250421417510f00031003444004100066034610071140d50022980c4074090140044d0311000d9184c1c403040300b0030b2071070032010303010a81c0b20450b6008000502e003c1d1107801030240d940042d2040344841e400412540900c9805209d40e00c0034000c0e41c801172144000040000b4060181c0e03120051014000241c0000300e910748000304400120028110f801e5141c03920881940c940280303100a842d18200004101301c11000411101d4a000d0780b030305006a1900385006490405c640c1404540c244202e40040c0e00c4014240004807003d03102d5180404841e4041c1c00741c1200341405400101950300c0c1003c03080001360000704072003c031010900c0198448812b802e00860080003a40b00301c2c541e0190491661082c1e00200c0140740e481d000b85160001103441e0307030704440c80e0040400c61400c05803100340100040390281d0040c000011051600c10715040302440040d09000d0108021070150f80a400e0074000079030091004508582540b00501040c0610704c141680c2d0040082d02078003801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 401082886 1250 401081636 401081641
    0x30606010c1109040506150a05180c071707030e040b180603101508460f0507240e13090503190909021206090c040504110c16031505 58
    0x1400c2802c2803248000502018452505040080d1544c0d8101d548202c01d005845241005203040000e441c02c5d550040c250035003000c074074190201c10900140550343c07216018405040002c49100c03109020f4503814404a440704014038001e00b091001e2074103203201e01e040030074600d07094440c0d0507801c0310301030110074600c0d0a483d100082070804a148414030030701070400c07942e4607030aa03a08082d0b100322128441181d40d1888010300c1031206815884034411011200c01e504004240c1d0540c2d6131403130700c40c18248091044401c2daa01e441c0003000b407400321039170b07081000b0401089100070180c040034010450b80d00e03122107002c48000e2803450a65141e0b44518030130b0589422000140c0d019040e915032000803170350740d809041c6204c42c5071070011003074600040d100311000c10810494020358900d040001c0c46120b4a0f03d0715401c0200d200001003040068401c2800000341c079030f0300c0380201a2104202581d0b60f40d24114107200500f410041a102d652812014204000284211103100741660303044400080e542c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 401084136 1250 401082886 401082893
    0x50c03012322050105120d0519030219030c020115050a180f0221090d0f030b01020a06060902040f080303010e0403200d090806090111042601090f02100e030606010c 72
    0x940408000c0854401641580107209003e900182c180c8108a03402d00c03403202200c2d2074a5490a1103214513001447c141b00010460150000801c0c21078900c3c180075041c07000030003d034001d910324440c4010000f0344541c540c041080d020710402400e5a40c00c0382010a803420400402c07204000341c422240c841c4000b82c00c00018081d581e021807000e002202d81555150407040702e07007440d070400c525410080d0380500301155070b005000035055038421907070300e07201406105044140e0080403420082819801408000b01c00140d0b284520b00c0682003c0300010303219070401012840c030026940212401c0d50007000180101c40e40d412025501c5039141c03503c0c0c8403003401c0c0b17089202401181946000940b0814400300c480c15000103d501c143c0d00040100c410070f0740e820b80240d09940d0040c1061508840412052144240f02c00c20070b0a1080c4400f03900062584e00b5180508603184050203a030300c061415404002c52500500110064045282102030050f0000c002903c644000d804181441085405003042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 401085386 1250 401084136 401084149
    0x812370f020309030307022b2d0906140702031b0604030c030f03080c070210050a030e07170f0a081c0e03071407050a0b07020603101a0d050c030123 65
    0x300c0c000c00942d01c90a004600665942040d608000540a486000740c04210302200e00000e10000d4145c18800705001c80054030012203410060484e004281102101c12992030075080d603124065403034002840c54904001c00c1d610710544200243c44040040102582d000070b511007028582d1002503101d28a00000038519104591005000c42c3c0000c0001060000e501c1c1c952844034003913142c165140d65068849010f038418110020341c086d20b80b03911a10402d114001500380400c0d103060004e0301c5141280458074100881c1c0c0820580310102550217003c2e2000c3c003007004812003100c0148000c6400380d4038100f66011340c0c010460001000c482048100040b5000380111080d16819690350351001c5c1803400030316141980820051007441c43c002190f0400c040304408485c80b40c0d00007802e2805650820015500203428030600d40100c01005c81c4201d80c4600103842004030810060741d900e014000710040d80c000802230110158240010090035140d80800059450244c04110074425210000f801 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 401086636 1250 401085386 401085401
    0x190b0c0309120a151e051b13050a06032307090e0c09011106060612100f06091505040510030e1f0623010c080c0c0904081237 55
    0x612800107082a446400c012a812040f81e00410300d28000002e079240d0070342940c4507082c080e40140d0307501c040400c007131200c0c2d171209820240c07140c00e00b03168107070b0480154440d801c8540303d84400342c03c490041005c0e00c0d100c50884014055030809005c094003096803007d25841a000c0042c450120b5000071b601d440c0316403229405003200011031740650812071400e0b081504001c4c0d58034046009048040c503115070005905200c0c100003003d82c1e20b80441e22441c9110200d000d02403020128400a0110300c6c54010342400d4007411a40d5100321074a45000c1d6480c120481e84522074003403150800041c066030300d500e10703888600c140300c2c02d011070b04110681015281860059494442003905a2842c1200f00142c0001e01254009c484c41c901100d07807810b00100c10094950010b020a030094103850010f03503c0d01c085d145505a5070143ca002200d510301040004c6c8084404482c01100054250510b04044820903001100041100c00a03e080c161540f46000000556100001e54919801c40356480380c02140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 401087886 1250 401086636 401086639
    0xf0e07060c051908092404180e07090b18090d0e0607062d020c1e030408070306020304060e0c0a06031d0a0c0501110a080306090408070f051b190b0c0309 67
    0x10f005114500307003491240c10400006200740004500e54a14540b40012461040c01850005182518142c2c400440c030858448030010b460711407006480b04101842188000c010525000c90403a407802c04000300340c0b150380c0c1103071038800906d02400f059880000780c0c0d105003551400c10490401d07051001400c02e0140410082401d070500400703020314106080721443d0365000002e00204055072485040c280d0150f14a03004090f071001d80c0705010454481603000c110145d00e41502e1409032664845420082207410580d15030750000144400c010f054841e044c1c840c1a00405890f0880004001030701000320b0b44030305d00415485030800d460804441580d205144500c2044031001042d0b031901c50b01100b128807942d0b01088a00c00503c214100114509050326803111245165030b8800c0100300f088040608103942c00c80c42801300100107041002581081c6000300300500c0180c1250003640d56210b205c2c0d801500540240702e0039078900c0c200c50810401c4c1d8020460301d13500c4600d008980381c9075004440c03086 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 401089136 1250 401087886 401087923
    0x204050403021509030a0203160305040e04200a0303080f0a06260f0303010e070315030b040620040602030703120b300115030b04021503090705040f0e07060c05 70
    0x3108040d00041d8185850040011802c2140d8604030441c0c1c40340903800e940070141e08100600d00325040d004040b019002e100e4181181081e031125128510f4170021138049402d115040e82000141e0303000402e00454140407100c010100d42156001000c00070007806480c00700604501003050044243c1007040903158018980c0d6007a9072203d504082401c0c1e1241d0b80d00140510781c4041c880280200c1180d040e00e891668180e80798a0b451800c038024080107044050880d0301d40703404400100c80d100b599000b03074089e002c0402e80e542c2d12080303166500b070050104022890100b004000300d07600442a0f034800c540606109007a9121f40748400094a40440c0840d405103400305442c1560400f07180200d0803c0340f1410a01d44400c10200d601d00300c5042c85040c02080030315090400024000551b00c9901510180c01c2e02c0030310002c190100c6c125001602e6150140d04111070500c060b041c14850740ca0030a00303c80080c002c204030000110303200c1499024545c01c1001d00000c000a108081080c64103400120066 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 401090386 1250 401089136 401089141
    0x1407030c0212010b0112020703200f19050c0109030308010b0c01060b0403030807090602070315020a110703080c0d021f050405120d15051f03150f080c0103050f0c090108070309020405 80
    0xd90007001d0038840c9502044500340c0d40400d00d01d483c42a00c8e130071681034841800c0c001c01d16645000620480e00c0030141c51003501f0412154403030600c411000364121415548615445140444c00c16410740070181c10004030110800200741c0c00307041c02d8112024445500d0307a4603500c02409000d0b203507940001410302000a4008201035000710564441da0381d603550300302a2030311800203d8868940e48000f412010050b10140c0103050603a0080481200c0743c2003001003200000c4000b81820f00a510590b1107075030100d0502c00d44642800b01400724819072024090700c0444030019680b044039940c1540302e16985400180c01c0200c00c1081e002403100c242400754a40300c4100c00400601007054031080d60a10a042c001503c3c2416400031401200c40b20240c8801824100214001c04080c00e8004085159a0001030301c0609a03405c000681301d00300203004000394100001d0261400500168040c410b00010071842c5594181034406108092800305401d40741d01d84128054404010041d60141ca030005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 401091636 1250 401090386 401090419
    0x70f02210301031a04050c101e0f020709020a020307110402040803030a0f0b04020c0d030b03120412050c01050304020616020f04020d02122d0c07050a031d040c1407030c02 75
    0x78504891050300c00c45070300600c03000b4420084400f03a0300148198001488000c0d030b450000900042c183c3c5501d480814074240c031200c111008040048980401d25401d4801180c0e64180072840c0a00584041907141c608144c8009540b8402d6100180c0b040d80c10070740d100c001c0d560b0b6404440003001030408030b039128144613400200900007569258500c41c5072003a0319a103070406000303580042d8150f41c060030880600d00c0c810303006410303882802949402032030640c0d00301c0046032014102826a4803009820328a9620b4040e15203440411700c581881028810007005a81d00c0c01100e00d0002041030742d0703100580300c1c404180101d810002d1554828004240710741d00c8610350740500032856000308144056180c2d28020b4100004103a0142e03d04078120351a110503003000d203034071038010350b509114030b103000721a44949080400d140300c21800203c607019554540044142c0c008940c8034100e0307041214441c2104041c0800c1142903907c01100c070040381890a05004010000801d500a0070140f0314101041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 401092886 1250 401091636 401091703
    0x905090613060807090f140f04020a08011b032f070606090c030b10090605040b0c030405030f0304030212060c0304030e04180b270706110a1b030b011d070f02 69
    0x2400115502c1e021a001034404940109440b04500315000901c5803140d81c104232032420010800c0c0d82014185600098003d82440f0b44081d00d0324148003c49000c0d0940b01c0101a80e025244452a460540304d0314052030710024485642c400c10680c044d41e4a008074078140c00079201d25800828964030b000060048180c05810100c9240400c95072000005051031090350340942c0d40c007032680080c2d001c4c0824494440b40c0001000c211702030758102c0e03042c070b13648000003032510001740c601c846950000321f010811400e280204102040219000e1705580ca4510380c0c01840d03002c0140040c08100304200380c82d6a40d1256840214084507008a03c021117000f070421820a03d426104003840302100090549071440714101042c00720304480c0907200103450110120380350408855030820350f020b540c403c4030000d10303524541e2040303c003070103100700481d403840c1410000c00a050b0f101c2280100c0511104008004c00148254824480d045c9440045106442203181843c0c042e800c1d041d0080021000e2242100e40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 401094136 1250 401092886 401092889
    0x90b0403110d020333220809030304030c03080c0f07030f06180b1e06040204060c080708090d050609010501090b061b03130f05120d020a0f030c08030a0b1801060905090613060807 78
    0xa10914406c2c0c4401c0c40016040d240c031104201d1400d00001010b000800040041c42c0d590303c0101264182030b280d8440344052055540100c0f00300a0004901189040130300400700c0d0020b08801a0002600c5c583f0341c1201c06600b00c1c0020b101aa44070300b508016003903c0d00b881241c179000503549101c3c0c60070301580441d0b01c48030004034022012417400601545000c0c001c580c2622078954510120a00702d035903461107600000001c4410354000e10001c90141c0302d003040103841d1070103a0000d20b840d0522585c464215101a0407900419080441d401d4181d2a0745084070040c0c9548200702c2560342d084050705045000d10440808501c041142c002141e01d24080081e0503110201c4800c03e50001a000742542c4610319070006015030044103104000c104424002c0c00c1d01c50080c2003145c0106a00c0e0344a61090780f0890b160096960b41d17155001650610089060f15004000d643c404207505102015010380ea1a10070944038851240000301a038940b880241072448510a00340f04058640341e0068139150035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 401095386 1250 401094136 401094223
    0x30606060f08011a04260303190f0203271507020106030201020c12060403180f1203081b1c0f0501060806030d1404050904030e030607020d090b0403110d0203 69
    0x2040b002240e91040d8181034140d94004501152403d803420076a0905404145081b001d154541030101044c504280300562081105800d810201000b000e094011030f9400c1020300445807041c0100075110201c2954210021020366204143d0150182824904404003170346204100c461000d00014036015000041907910036001e8542e03182d03440051080d6114108481122980f10300045400b09026991600c2c20441e580b1201c1946a03e41d10924100c261650010300191150258441850392003041c00e078111281c2c0c000c40200211005001c68240244407010b4040500c1540e4174003030308450340c03000c00707501d41540007401550ba54080c041d00740c00089030f00c00d000c0e0003000c80900009110b85004041d80105032415400c1905000c1400032405c4000e1085080c03240307207548500655410032409200740c0c282d41c01885d145040c0000101032485550200840480500050002541880079413180440503070f508001d2900314000285000c0707425a4244590440140f020f0403000400320740070134000d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 401096636 1250 401095386 401095397
    0x411190302031b1308060108030a09060c030c0b0603160311030d0206090601091d0f070f0b0a0203090d11100503040318120201200304090603210507030e0a030606060f 73
    0x126000650a9100403500d940d0384481804041103000c09000140442c030005100103080b00c0d450b135904604d030a00a0300b02c098641c1c004074440041c61392280c443c03006070016141c10800b000c0c0d584d074043e1180601d4070f00140740c003800340001046a1003c2002102c8204002c21856203550350b130030100c504004088103d402800b0796408024000d000050301800795241d0401000035030b00e0b1944210040002c2c40020100340f80360080c20819980400210380c40001c00317009064040c0c5040c83d1f10071142d1315613000c03a807040802d0141c07101c100e4000c03007590b130525004c0c6c6000407041464070b044203803c0078030003d40303a10074a0409070b24aa0b65110300510b2041d44240c640500c0d0140c0070a40ea860740e1007500c644920790704045603075001544115901200154003208045806c1c0c4c43c00040c50558111f131f00300446440d03540004000340122200f0010055541041d100e034941241d200040c414030405030040c040c0450614045803646815681500030350300444204001030320384900500a24403021903400152 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 401097886 1250 401096636 401096677
    0x90801050610080a09080f070602030901060f18051f031410060f03110f0406060f0219080f031e010e0402041a010f030b06070f0803040b1e06040e0c0411 67
    0x2401d64542001c40b03295110400740d560344111100141000aa0441d100c40092041582c00007a01020f00400c41c800c1d1405a12407800301401d03421130f0700c10f41c0400c041c4180c110040092461040c5230030625010102d0200315540c4030100304459810f020750101403200080d8002050014291842e0107900492096400ba800003010000075540e85008000e4200300c0e4030f8003040040c884114010004101610401003048284000b40807640c465000c203011610310324402c20002d5051007440c00d081001c030b60f20800160f135525564240d0084002c1703203503614400004508503c09074001c500340019201d01d000002d40c4c4585c1c0a420000041d2001c9016908200009000c0c1030707061a40303007030101c040c0c4da20024075000c490200c0280800c1242c00d0380041041000c0c00220340003102c06510a40035090256980c2024a000101050000d245c42080a03010183c0c00b518280c5210407a001f000880300414034488000c500d500b003080c141c0c60503a0240c580b00c00003000188410141003a541014121b0b00c140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 401099136 1250 401097886 401097889
    0xb01170604050319020a14010606030f0509071502030715060e0c0c0c0402030a1e02042606070c1403130f090b0d15020403080708220513050a0f0c0908010506 69
    0xa20302550000c000d40c10a21407090100352005182c0000001841140c1104e00c49803610110645000944102a51a800140480781d0140105243d0400c2c0290811103450316028140c0c851340340d8028a10714071034802501c03803414801c105498260350041040e502040b1100a160700510844c0b103006207105981c40042c9440070b605040e2110982684040c0c03c04055070230801000b584020845c2084075501c0058040d41c041c03499850b20248151000140d540d820704461501d00c0c0050718662007400290031564140c03c00104006030020028107041d4030300841c92500500e11349503100c904110b48004034048440e01100d00c1c0440c202d62100414510080e20340428401391050f0324541508100303503455490025100f00444004400d00d50340040c201a12035440740c409a0140743e00303989021010030b02c0c0c440ea40d0820303022028807200700050900d141ca080c0c049420120b40c0201c3d800416551000150801d1481d0410300f08030003010b9040011208036500900700c14a18002c03030069610b0480051030a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 401100386 1250 401099136 401099143
    0xc0a1205030304060b0411041d0606031014010507080a080618100e040f0803070807080123040506010e121e07050102120a02030f0a0c05150c03060d03090807030b0117 73
    0x460303030840d01651540c0e449407207400107043c05003090b60704107a130b400707040701054958009000544203c880350400380e0f0350100821043c9070050401e9120b25020014405551200c050400480b0342402c403203212040c00d000140ca590003085405440240002001c03804941c1c4403031128807a10084815440c1980ca01004074120441250a00380c1210324180c103004152440081c0f03a405031107142050f44615039a913400c001c1d034100340c4000f4040b841e000e007408441030b04440c180e4003402c6446506003070403000d010138a5400c110521028040c590f95000b180303082e40700e140f481905420107400340e174200c030000c005107903181d0b0b0f20001420b801c0c0d01d4200c44079003144003003a0a400c41c1c3c4168010a148085030614444daa48040c01e040154030040052007614a400d001034914241c80d5200d6040d001c030b40d41002824802e0720326014020440d80c2003000741f07014220060340e8010006441c071030081c40f4940340a0f030340c1202d20340051219100301c0000008028024550a0594900d903031548180782d03003410556034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 401101636 1250 401100386 401100419
    0xc0c0b0409050a0c0f0c140102190914010f0509060d090507181a0f060408010c02031e131a04050301050903070212070e01330e04051501050409020307020a050f0c0a 72
    0x41c41c0458180c217018411901444118060001d0000070348107401542d003240c0c031400f071412000c101d41d910340100030b030403007649001041d8107640e55078208002c00009040705940307020b250600c82d02081078006074517060300365050030341c046408101e0485281400ca40d05e561504ca6160403c0122040b5840c882c002e010f2119110184009801d41102040800a001941d5a2100c0d04408107100008250109000c1d101c404800c5401440d41c5078110f5503004c441100c0791206004043c01085072140200f48a8208411182c8038120f400480304a03050380c800c6480f0341d0740055415820a0144003410714040003c000881c4216090291401d140f02416201c807282e02c111300aa00b801001081206d010f00696926035503840000103211414041a1901c0304030080c000c00011244508141c20b41494891950013035002d620340c203584806040020305034819030003040318168020010410395402000143e50055018040ea0001c0305c02070b455a90b0303a400186020300c60b82851a0000780c541c81d0551f19030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 401102886 1250 401101636 401101661
    0x60b0402120402040504030e181e0103080a0e010e0a260c0108150a1208130608100522110c070f180207110a061107150905100c0c0b0409050a 62
    0x8a0750350b41c08100c01803c00038070643c180000c3c40c002c8c0c052550b0b1426880700c42000420310912609207c0100b40b00b4000c0800810041c1c10b140d40180003061104058854070039180c9421051180031000403200c003541490510b400694001c00411605141200440c10140d040c008a040203009843c3c3c966070703440135500c00e01048070310000c00d85c560328000b0300003003c00001d0410603000395074400310042018514400c3d20a00404541d55440b68000554000242140d26040c000d5081c100e96000ea80b024034402c00d4401d84520342241166002601c81c010400e92031310003000380c60300410341035070550301610f000b0f2142d00411001040400030b07800c01109603215001e460071030910b80e1014400a40c40ba801c1900d180003071160075503c1d030b41c8603070b010b10140c903ca903545500c0c804800c078030a182488981003000078002601c0c0301c0c0314007a07204c0c8485085600480d4405100c881d608800c1d0b56805614102420b90708e0305010101d44840e001d00100700b00c840c2071000300516602c4189242c1203440320520741 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 401104136 1250 401102886 401102917
    0x40e1f0603020c0f4201091406040b10050a0201060308040b03011d01030b06090a420e040b101203020102070c0819150e0115030c0602030c0d0f0c0203150103060b0402 73
    0x1407800e0304400703c215483c0244461254501748284040b200403034090340005a015103403c810902c240100c8841a003011082c3c4051010742400000a203504002c070170500c08000c004184040c046100350400c1d4015504002c0140c0c1d41c03038580403c0710700390307000f406800c054020300b80c4440f18600582507142d040341d401800d4030507542c03602001c00075621405460007a02c5911061421059001099064a0040051a0fa035058200819103402a114070840200701948a603410010b5103410041c43d9030040e841364008155944820b81001710844d02c5c0c000a02c40b589121076081003540540c01404010302551480301f046680b0160305594001210210b4005000004443d000440004600c0070070810304001054100404840c142160302c0d49c00031000500310b803003040040c44064810399000d05503500c059450a42c1c069040ca43c2d41064100c48810414603612007100d041c8110051102c490780101175641412000800c115003045c04e002c00d9841510740310500406190034821070318a5084503046 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 401105386 1250 401104136 401104183
    0x70b040b060120030a0e120118030305090a0201090308070201180605031e06331c0b0a0515091f08040308010509130807020a1a0a0f0311040e1f0603020c0f 68
    0x6c0703a40c40021445103030030948901c0708141131002070080070745404158892400e03141080c200107050703070000b5128042d00e0b0041c08a07180523136806007070a0180c03900704104c02c0c0d9685483c0300403241015130400f42152060003410116007030b6400002903003d511410101d11404042e901c24084407030003680c0d81607002e044900f441c1c0081c85086107808507091440303208804080030740b0304410903902443c070300310661410340034103900d014403840303402c40d210801e40e0014542810100841d030800b08507100502e2501004c503014120b5500d00d01c41c41c1c404000307405c0e901d00710980b41802070316814042e00d0407030210307540310300204160403c500d00d2032003103221020328124100c4640303581c001940002400e0f604a542d020010440300d2455860b4a08100712410fa40d540b0a4080d0001703020312081c030b51032005c05003040440d2107181400700c01d54003502d0b41082d1800040c2c40d5141191078510b0150341c0305401b0500244000b9030545c03d0b50181454403041401d0b604016491070145850310041c0075692030030404071701c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 401106636 1250 401105386 401105407
    0x1b0f240708100e100602010e060112021306030f0b0f16020c010c03050d050702030c0601060201140103170d1a0109060e0a0e060a0306020f090a0b0903061b070b040b06012003 76
    0x5800e5045441503503060101d0b03440f031004244500040707400c085200140c01040107215070921600ca54004c2d080040c142d80d5052141541d41582003030f5010380310b8940d12503040701810496114000039a44803891207503090a51030721a0420a080b40e8039002c51201500080050029010a0721400c4d503980c080e10100000d06c0056035541222802079007000018004200e2140c0d440c841c460140049400642c3c0351160700c1c0c107071031800c2416040b540440e410b044415088016840565055950103104070070110707901c41c12001c6900403008101d10035030900401402c500c1025105002910080c4d841000c001c1c1c4407035054801c1d081144480e40c011300b1f0400c0421002c588448401d400003001001d030051b0315520745076141603801041300030140d03040000b81c1450500c1c2c14001f581c02072941030246070801036054002611180d00170000c50801440c0008031110f90340c820200c50100f5801104662541481d0420921640301240d52078080f032480c14080040072000b03445a5080c0080b9402549422031050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 401107886 1250 401106636 401106647
    0x308061002060f0a0617061b040806040201030b0d0b0a06051c0206090d06090c0810140c07031103090a0801020d0e0c0d11010905040f05060f0613030b04081b0f2407 72
    0x200300c04ca402c0c2d5100004250803030f00c2c078510343c852406007000300013900700208a4032400284108060480004000c10451540c01113a0a5803168090800203400400030012440849810400400102c803404c200300e81440c40b540120161201a0707800d405460030030700504070281040300c0203540808280300c0c20034103150000c1c0c4a058035200b58400320301044541d80c2ca000d071140ca50400000c3d60412001045d6400c0e040c03081701c000800366a05848107007069000614035101d084805810000968005442c0e800c041040322113081e405440b1402c45651040d0b00d60007504030003001e0b900607080881c07804224400141542d5007620042400600d42840c0d43c40100252000d400b450500510383c4000a03699124401c0c0742503600440d00c0441c0c0c40c58080e08100d855000e41280078801c070b80502095001703944440281040e07070380c82410004d40d40ca131810710380c001d4014228410018000084640e28041000c5816410550010101c5205110400e81c00369403040203420b8007011070603000094602403181 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 401109136 1250 401107886 401107891
    0x5030d12020706020721030c0c030f080a0b030601090b0108010503070b04180e0a060b041b080a0b0613090902011404030803060603130609030917070e01141210090308061002060f 78
    0xc003001031070004a1b5480f07401030802072203201c860910401070030b41080e42600801e03d000c1c0c120315002e111522655400b60061040303038540410001010300140d11401107a00c0843c08410041c00c0f2400c9681d80c0d000c0101a00c10514810300140e4448000100b6040c0041e844040c0e425401d106820281845841400d010700724968006240e122107607000d00702c0050091041450007880b001c01c015000c04240020ba0302820302c0c4172103140e2828034007056241e110f00348540042c019580400c22480c4100024118001c1440021041c02204400188100c086d44607901a6200781c940c80480300c0050030b05400e500591101800003201000020044d103408001190f018280b40401c2e0aa070340a9190541140d109030401c50107e031350444280700001d000345c8284240301d00e01740100545802c00014080c9407a061055809000c3d41c0c164420071651510800ca9202c018403084411130404540c1500140c95850004d50204042c07401003010f9080010f4045541d02d070940080800d030b11210020040350100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 401110386 1250 401109136 401109143
    0x60504050f2b060902040b0f03060610020f1f180f080d020d1a0108150a031403040b030c0a080a06050117070e040e030c1917090a15020a050705030d120207 68
    0x1d20b980307000d405030b00a11280d00700740030300d01c00145002d480c414002143c5070a07401600c02d0303040c5480e44105660004000ea80294203030351070340100308801c80a0b4a021802e6046581900607085c80c2c003450800042003182003c403c0700103100f06542510b0142c0191b000f05005403052101d003c4050208010030000c02c038580c030700a80140703000401da2140003106d118a036401c2010740711120212056a0104403150003080c158030b440c0b02901c103000040c0c012401848010300040c000d5011800143c01881641d0040c2400044140d072032920380000425030f03000c9240140411132040128030321000511524040d01d01c103840e68441003071007500055803054000d080004201c40d00031801c0e180e807a40e00a042004080400443c2c80340005000c0a090224035210390350000410003140c030103c1c3e403c07031040110728110210141c0c0da450080118903981e046820640301c3c9056104806002075000a03680c1c10a40036505455040b510342080541320b0380214140400642680c05e0000c1c10850380d402040d03a94031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 401111636 1250 401110386 401110429
    0x905040309050a24030506011b0f0206030c040306150f0308030a110f21060a06050313050a0c05030d140d0b011209030206072006010608041425060504050f 68
    0xb65480002d0000c2c800b0b422480c007201012001c84003543c2440851a10401c060034140034614001c1c00007090400d08001140b9a100428a000144002145160065500908a61380d64a00000c415615a00c0307440119599450685042d00140c1005000011b9600d0b000c1c02c1180b15146072100300d902e4101501da0384009561368105000440041c000f030003012005c000c81902e80c1451040306400ca00c08c40500e641c00144030040210716030710340b250b100540c2d015040942e182c1c0c98000c0040085025030100410a200c2d1080380014400445514400c8480403000c540b00b4070b06007841110206ca90011103901c042c0240703c08280c100854000300c00a200c18900010071340450100c890544480b0101a005604000203211100d68070205421020010302c03a45221035401480041d41c96405220340f400308650540442d0800c421880c0a020041c84c43d42200c600310382c0d01d5810518240840c4000c002000c2108000415500600580d07003281c00003008628500e00710b02c01d00c00302600900003012102c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 401112886 1250 401111636 401111639
    0x30a11040e1606030e0304050a0603020c0a0b0406051b12010603110d0f050711070308090f040609090c0509090f060117120c07050103060b03040206031906050303040801020903061f0905040309 84
    0x3082900a5002c0c20442c00c0491481d0000c094225122507544042c5c0d90001c00c4103118584038050740c041160b44d04d00d030040c1d8486c01c40c00312030300340002e20394018940c2001005000034800d091300143d00500c00c01a058407441400c6150322800e204585100040c105c40500400c02640203034090f4045003200b401c43d03851f0140f054502d8080f9181841c07040201c80d0760b80c0902c041141d0000c0b118081e090000d0081840508540f42c1c070070a0f014440e54148905100d20651200b034491350440c00003230085139000d01440c102441c00481c2d02120b40903031402240d0240000d01248000120004544002d4020305400e03400c1c070ba81c112500f0110a00f00700603200d04018408100081d500070140c04070248040d20b042400c0c40001420b4036429804804d40c3c0b5402d10911000d03a480104a0b9007014991104031500400021f03541c025020341c3d480746a06000104000851441c190000c00400801b20207850060f500d640341419081d040e40c624001d81981c040c8107000040d502d6000d950814040e0500040c1107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 401114136 1250 401112886 401112911
    0x1062007080f3f0307030204180e010f020331080a0903050c15030a0209131506080105040e0706050f130611010c08161b0605070503040213020306030a1104 68
    0x21484544640701c1d0301c004000d41c0c3c26080206603403045401c1c241800e070582d410070b440341c1c41d659696414142000e00000880e803054002d50481e0000c0000c0000080886584d202c0ca200900d00e04090013415404c0c46019991034095108480c85200b003400c04403603040c0711790718041c128a15400840010600c0e81c040c100492044030103403001207502d0f030742c6d11401c0d41107250040c00c1c100c51700600c81c0030310310815850710b02c040c845040d41e5006a105e030005031030f43d010000056000000380c06181d1a640350904280c0301c01500c200d60b40a9a03510b844100059076501c05202c22583d616140321101e0f002040c00f401004e10440c0140843c2c200383e04803030f04125030300f200e460095003a035000c000401d403100f407603180f0484280962118460b03141000011072030614100c3c113148015005c010b00b040704400170b00805819080250700402e4118100300719514008a000d0680ea05c181d900781d00c284400d0132418000b20480c003c0b07078400d0002402603e40c5045690b5462030200c140a42fa5500907203480350072402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 401115386 1250 401114136 401114143
    0x7030c0306051b0f070b04030c1406090c030319080c0f04090605010e100806060901020f101515050f130e071d040e0c120705030307060c030606080106200708 69
    0x40c5010380400245418800f82006150142652a250200c410b0100c08038140601c825030719556000b203110800e6603521b01d011920082c000500810000094000d014101310015005205001d024200c1c1c2c07103088070504241d902d0003640e07a07090783d4104c00504451040d10550909400a41d810217443c1400480e494484140c0c100d074022a294540da80303010440c640c0d003d507140040000c01d0f2001448181d981100501704d00005000d54082c0400081400740759100304542c1c4d80e01010305080e200b02046c11003480b0050188059595021035440300c3c040b40701d002c02c1d007000d06142e100c1c1d202d00b4a0990300c0060130030542c21036034102c60700d2000710800141c00d248148000f480f0301c20640d540c48010110b08024940c60301014503480c061480c11024040301800000c1b41411a041101d4500d105000644020f1400c00b041c0c201c030350580804a000c034204082a04800e4841c200742d1010f015698030788100301c6142a0921413580041e0700314507401105038140c441d5000314440314003510366441e21200c070f0341d02d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 401116636 1250 401115386 401115389
    0x108010b010e2812150c140714030d0207050c030601050301110a111204060f11010b06041a09190303121806090c050913051506031e01090b10081b130b0307030c 70
    0x20221018421745443c4185071103224002051801d000f0f10803600000405668015090300a210382c5c20040c100000841c1001030f81c0504803041415507540009261032074440704c190405502030320510001141030310f018000c1103000c04038501124208001c2c040c0454254542c000e015205000d1041161000c01c070800081003c2c0240d900d40c1c024000c0712610040501d4280c00c00310000b40d14cc12028581917468604071421030f0545451141e40b40c05d41c1c2110310a522546480310761113041460310f0b0b41203603048140f41080303e01075100c150602141c4486202610a107150b50b41d0041d000090340d0001072459030000c035103075008821001c507540d15a40820002c10b07090703c100d0340e901c8051000000300b0204001002d0035200c003805c1021035084c15008a80d42e00c00701c0300500e003210700312004040752610941c0f20301c24181d045120008107081c8038928142c983c03441d004507000f80c0038070544650b407083d480c40b251400e41405004544031880e8000105d00400440300110b61500440c400000400e030000c85000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 401117886 1250 401116636 401116643
    0xc17071809050312180109060e16051c03090803032d0106090b0f0706050109050a0b120601172103060901050306060f011809050a0204060813110f060706050a050108010b010e2812 78
    0x5084101c0b900e100c2c038240c0f20101c08404415200300c1440302e0785a000e809683c01c091100d04031610040dd10381612500400c1d0003c04841c800442041201002620701e405c804480303009141000c40307141410540300ea4240540e40100d0f10b00701042011a491400500590344400310b540d04100b403c0d682c45041d40d800380d1241c88115151401d005101000d032142811080c0111010016018842c8420381c540700f0501c50013928400308407a00c001c20005020344085c18840c541120309680d080c40c100d0066410603103600d8001d90061002048900300052250702803040100360241c0b280049004540d08040c0030290a03014081d8440058517208501807a8050a40c41c2c0000d80c8907400c0020045ca030400041c07003c80c0e51708054142c80c0114080344c0025107420819201c5d002c42c0410352002c200d030751240c1c4070002d0000d4a000c1c2041824412540164169480740009010b1071003c8401107500810000086900240c08003c00c55005035454600c40f03410030240718081c21690320340d01c00c4040e803e80802078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 401119136 1250 401117886 401117891
    0x30308060d06051305160303142b0507080a0e06150f0d051c020d050a0c0f020d35090105030603240f0615090603040c1707180905031218010906 63
    0x80041141c2401b5010342104240a100240c903d50b46004018030500c10003207885183c00124800d0302152520110184400d00402c940400c2c40c02c026240100f070f049880c1800160740b6004642031000e00e000382040d580201c00100540e46664038072160049130418140d90004400141c0812500c400390880091409070b0040c000800c04411a1141d1a03c0018480304542180c0c05080c2074540000030b07600d00d1800c40c6003c031414859032070300c0b001040c900040613601c1500601c0d0041003042d840e81030548880d80c0d084146d42180103a844d011514112402d60601760000d0003c10b4143d44208041c503400400203044a0f103243c0c8448458414404001c03105e884601010200260b00b440c80d402141c101100742c07452601c41c00004008415406401e4005101c2e1034004082000e0110301140c400281486800801c1d044052014888d90b4000c0e5105200280901095002120300c09108040d00907400001a602d440041017104070300c0800107007640c44c2502c0c0c000d02ca003a421001d1081b00306081c40341e00300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 401120386 1250 401119136 401119171
    0x5100c080903031012050a080f041403060c030a0e0c09042a06020307031247090112022e08090a051f18050c0108060105070507030308060d0605 63
    0x3000c2410050038280c40703034410024000020000410001200d0081007032148540342d0b403501034208881004081d110040200b00d5840914606008004a4030250030303045041200344203041e11400f08a82c405010a8203000040e603542c951340080c10a82c6140d81603522103450080010248201500c00b52240522690415586140c055080745c2042404003600d02e890301c1c080c0001e607a4031820394010100468000c0801e0206019044070600b1036107000c980582240780d00b001413000c01d1061880b501610354413000010030322003000c0e42c100c0b50009007091200b0b07800c000f5000300d1584490000c1740c000f0001c070044814054035140b41c1502d103a074940c050600300c103508801070910070041c203450305a41069109100140c0c1c0041c042398821412440310302510f482c00b15117001040c44070740740c0618084c90440401000310100c2d02c401401c101341c0b540c004680f030300801110123020b03244000b0440d40c4041700610120b0301404a903030b84004014000d0b51340680ca595180260741d41a580501c1e90107032201c6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 401121636 1250 401120386 401120411
    0x504050f01140d080301060f091508100b04050303030c0912030304060209130209220605030a03030603120f050a0c060b0402210901020a020c0424030503031504020702010e06090a030510 81
    0x1c000e220b0142100e500d00b001450740c07124140c1d8030041c070401d000c2c40404081c9181043c01821488000d00b10440910200210758602414801081703038032104219000c0d0000c00c0c032070520b00070758081d1200a0300840c119514075001da80c082e4030204150b64081d07140c072140b180e0888100000c1d80700354070410b800350311600c2180078051040903821041041d0f90051201015a1725841c1d1280403050b00c5c100084030054482480d14001d0850342c01c8541c040c020320b241d0740305054168111104883c440c05440b0982c1c2d41d403a0080359500c100c10b000301d00150040090b45400c91103020000035050140400191620300700b0005822a80540003490711055164003c44141c3c8145018030342c4040094000d5260454a40b0000d4441d044901c400d44145e603030f00706000b280200704151800035452101954107103900c0781400f90707880d00111244042c0800e441c03d680d010381864000d944d50700394182c542003003804408040158903003162030300c10341084002c403002001c80c1040102c00b540f8054800700040f03c488420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 401122886 1250 401121636 401121659
    0x306060415020a110901030b060f0f0603070507260714011e060302040b01140906070f0b0403020c100c050d050913141506120a0506130606170f070807110102040504050f01 75
    0x14606100d17080403801000400d1142c07001e5603000c0d904580360310410040c0c034001000c0144000140d41c12550100400203016000b90003001014042e465485800300c90750894485800c2c882c02504200c1f80500007600009d80740301d1488031329880000045625807501010b0036070903103420b0080c0c5903d5125081003065040c24032418041c0c040a280c00b00d40019600290051803081c1e0020038010000003034081d081c08800703500c40c140319501031142007aa05080c00c0003966805011070541c40317192419440303038049014801140342d4a034031401501c000c1c1000c101c00e442d203801c415049504a642d08419150088440c802c81840c222504025100307030074140200c1603a0b2941e4511240184010407065100451108006910880800d4041001c0e40c1d00404214510041d010081e84142840408150039820a041c0c1c45c021a015002520035070f104038046007402010380b40b82001c10341d11408903900300d100e00f10340d94044003140005440c00f03550780003060803100120788540391400c40d02e006005440250 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 401124136 1250 401122886 401122913
    0x2030d050f0435010510050f060c070e0f1312180b07030c05100608030f031e0a0915050c0712020321010e0718150315140312031005060306060415020a 66
    0x643c000c211600d0556002c8039540114010b0030301c107190044813503020340d81d0f200854034071940d0142a151802d40e200002c0303400000580d550585c50a140c00013030106003105021300111303074202e0303194014041e480105440d0914407148070446050120030220f402c2440c840105000c500c00d98420b45403080b141040c608201c0b103140545421400e01c0c0b000c000c0f0303840c004151440d202620702c80540e039031a0441109400705568210351200941c0004000032940c05500c550050790190a4442d05000c1c2c2100f03800885204480202c00c0c101c9c1400210b01041c0c0044a100c030005035801240d20b0224410400c80c031643c15065407264040708440148419004005520340010f020f007031a075400840e450350202d40c0007080c080e00c0315030f8404180c0003850a00c01e8000b04241d01d001c528051043da100c100901d80310410320880b03402072003801d103aa083c400303042c022241318140e50000358824901b86800c004096002a250940c817846c140008506041501011003603919107030014a00c0c0341c00c030300e00f610242c03d0b01c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 401125386 1250 401124136 401124239
    0x1704090e1614060913020c010501121a060d060f09050609010605031203040302070e0712020d02030402100905060414210105060a06020604210216030c0f0902030402030d050f04 77
    0xc068110315143c030000e03221294400c0365200c0e83c0103580000000207002d550170358103456003424000141c00c611030014025041c0030310041c04084a20700d641d001c0760036050700d0081e08190000042c00104d030140e071101500000c4602c0101301400f00c1e4451610300003042c0c2e54031a0b680d556140c10442e900d000c0100311a642040384186085248c5601c0194840000e8407a01c28141d1000c40000c01300c83c820070344600c00c000240d00440d1134002d62040e01d4008e405c2240d0485c011042d000914000c17a004038400011a5001050030b0325142c04e00320218103408012401d1a00504401d5603201c1d810000d100102a400590000083d1441d202042042d00340c22030740048195045902800003040d50500200038901110001109071f041d560310891409c1303090360166006410201e40881001401172101048a10b40c00940300c00d991512480d0049200030344000b580360380f061080d41507050040020300b04108200d903c0c9410f0668980ea50070307030304405c90340700020094003d08280c00d0143c40308940400404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 401126636 1250 401125386 401125409
    0x1060902181c0308040201110703060203181b0609040906090b06030105011e03110112020703110d0504060207090506061902070504050c0723011b090305070605090d1704090e16 77
    0x48151140321071440d8003d82040140000141503901848803d076410181400712403280c1c0d0303281004802504140d0300380c0450890303400c8403c09558001005240d1000c6101100401064201002001d80c8200e8205402648070380303001c1c01088580c86141c1c40c1c135016854100c1303d0324080e0101070844005802041c850140001d100710340301c044004800c00c0c0ea503c483da413020035128034010382e1440d107980700c00318109000180c29001c142e404920f1500c01c410030011507462070709881c801c5d94580030b035004140050b0b10040d800c120100301a0849078100401a10580c03424802c5109418040c1c0050000c202584c020b51307081100381804e102300c5900500c000c01032418020b00b0381d126442c11444001750780398103013465a100344c12042035000c0c81041450030043d400d00204d00d40044d00c40da00320310041e9190300518200182460240c01151200480200710b6040d00c031099440f100444a80148000b90010601002c100c03040c50384155440c03040c140c8010f12031341d0212030b10312010300e010741c0040c0c11015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 401127886 1250 401126636 401126659
    0x100c02300c070e0a091e050703080f07140f0d120b060c0d08011211010305041110021b0a2607050d030903110a0501091a220e0a0b010c020f0102010209030106090218 72
    0x400a46c1c1e405112085810031107401c3c03001e03040070b900e02100d54201030030150000403c40c43d4050141c00900d1103130701c10f0300c602c612850310300d0f4403c0d21807004011025058225034003c0d82c0151041d080360082c400d86080000e0b08150881c04109a034108007821034042c0d11010f08030300380940241c14107004001c00c0c42700c40d40468030b503a240141442415407003818591035401003010089100904042d503100030300180a4414034410003540c0348514903140e010b0304500c0305d841d402c90902117001401e980704d40440030001d00c4c1110407a40c148612181c45032a5000d424008651641e5901d5012041070095030b4203480740342903003850351700349402c96980e5101d5134a40004000507600400540708403440c00d0340d508110014552000241d1042260300c2030140700c2010644500c504010b01c0c1c0e429140140b4a0342c00702e685001346402201c2e10044031601007510645510010f01d060300c1410b81800c030610006d030400012601290941d00300750850b0300b002c0d4010840210142c0044011082148200c4c0c11060340b1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 401129136 1250 401127886 401127893
    0xb1c090201021513170901120b0609150f0c03030a0b1039050d02190b0f0403031415030c010e01090323030301030303020c100c02300c070e0a09 63
    0x20014906404883c01421000600000c0090b00795042580c2010070740015002d1160520742c5075120700c0096000c0350703401202e6950060b13203100b80c450002008d0401c1349001d0b007601c00c00240c0c1d00c0450185103486010010444500459009045c082d201000115140c4c10281061400d44072562829406101da0035003402c2c40540c03101541b8941d0051407116620065120484841011f01e4145880200082c2d10802c0030030000080400c00c00700561300341c43c10040880400c0802c0c05010f0340140c2411303a50f102140e6040174681d00c0d550030511030b080002d0320100c400250140300780c080b117400000c403c02061004642c20288031000904500340390804a02c5d68070340021380b4180c01800084c14040040d400f000640303406001c002c0916203141c0c01c032512581d4a02e0002c4c041d50044c03101e00300c107008030783c217003208418a03004282d06c0540c243c01230484201581030072030901000c00c0c0f1002504460310154180084d403c0004c203400035284001e002407900f0400c260400c40030251003044054136040010f40403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 401130386 1250 401129136 401129143
    0xc120509030d11070504090b040204060605091302030a0212074404060e01020403120e030601030308010302010c020a1a041a04060503011523090f0306060303031f0f0b1c09020102 78
    0xd02d9803d003014403044649040d85454000d0940210380c01c00d141180400501c403009403d1840350744201d60a01285480c0c0c03004803098010041030355085112a00c810204403010340155500c01e201c5580141030510580003042c4609060398980003050118080d980451010115120848401a00384804080c110b070340c00c1008844240d003541a21020001c0790400c1115040002c1240c20324000b591503a440741810048031034900d000030301103a11103210303808605000c50564102c0707030151500500c9070f10b103400540d030b200c8a910f0126030003020f4020124074204070180307180c58102c0c5c2c140c50944990900005803550b080110f02d0524143d014882085050f9111085a045d5004403140d42c5d54810381107025694803a86035061400b0348400100c0e000c0414551014150100e81141e202040c00082c00030325032910001d030f40c020f4040c1c01c1040010f01442501c90510507021701e000580b0300b0742d0740d10164074201c00c040f90800340c01070130300166819040703141c00742280c0446102c01e010411b69040b0b500103541d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 401131636 1250 401130386 401130403
    0xe060310151e0f110106150f0309020108041707060e0c0f03030301030f030f02340504021c0509030d0911010e01080906040f140a0303060e070905090c13050d030c12050903 75
    0xc12400007142a43c16104010031042c2080c0c684c001d2108640714840c01c000c9844944c0743c100050340481f40140c055103c2e0181034003c3d501a1900400e60700d031502d40030002d0000c441a50015041004410f000481038400c40455900321800780a55810344010408030886505041c0c1c031a40c000e10051010031a4144601e441d56414103165a403070031035000590034075500315032140340008485030780701c1294020309040040101d925207100480d62203000b003104a019913501d042e4903400ca03024500103082507520454121800c0c8007264149018041080d0954559000c00c5940c1d06207050381c10280d503001490402c1094090038a41685e2030070f020542c1e82c1d017500510140144030360019040c280030f019030b1030b0624407907140c064481880300d41c01c014018099920800058081010001e1a024403581c1c440090352030041c4007000310f4136001e0144100780c200c0d58810ba45850542e07030015060f614984105500d502c651141c4030356440b181068500c004207445418203211040010781001d9902080d50b54 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 401132886 1250 401131636 401131697
    0x9020306041404060501031b080c0108271621060903030b0406030f02030601170d0c1403030103260f1c0b1201141506070209070e06031015 61
    0x585a559000004001d8250040300d000315002000502007440b002d5002141038038051303001e05c50b0400e4003010790120425503216407101904000d1043c2803641c824030b00d807504840d00d42001241659410b600d51a07890144012008940c040600310440c0061a07040500030915095601c1200b8031031101c40144040d40000281541d41d00d041e0581014001d50200700d890074080c100308001601c0c0c0c80d000c001000010416486031044034000520581000c031030540c9821070358090109100d8090b81980e0302030901c030088581030164004a01250380400107540254000d04a964040b211480110314180e04003000b80c0c0d4111040100040035401d5400300e4100440841e142c01284000d0780c48000100f00074459240c3c01025400e12006565054000802c100da00034110412501c03109202d1282002455840c0c1e0030030070900004001d4988030340c0c150f0703010340a41001202c0c100504001a01940700300d42001036125941c00030b10500d00c20702d40c45009104507091524000d06449009003200c0b00c03044420 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 401134136 1250 401132886 401132891
    0x3081b120a0804081b031606380112020a030c140403050d0530150d05150903360301020a0e15090303070c05031903090e070516050607021e060109 64
    0x144c402c00b02e004420303041120600546e510b415441020150000c00c0c1c450903074848c0d00308000d0720364007000b103101c00c2011811246003000c04400006960044142003500b90f050090a40904880700c0550008101c40c00305a40c0000f4031342212800900070450305040500c40081c240018000204001815040145503040450700d502480460140a003101d07010b203000140d4000c01c078040201e5003003242e07015a0110030b640700c9517000e510501c040101a80405451a4007013145403600c28410800c0d0350b000700842d02624600740390340c1000f0f111121000150b031032050020403803c2c542c903824003041213510821002580b602c416094001c101001c130390f144030f10807800e1020741d41c404610b5100710b0b8443d50380034064a031103130783c2410150600d680c1d07403045034040d005042520b00c0d840450359040000304c1d0f2503260342c1c05c03150a141c0d50000d80c040061405c014854208104070200075800c581c1e10342540304900401c000c0c58408002410b000c8940e000141080110025450806002c51004d06544100200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 401135386 1250 401134136 401134147
    0x509040515040f0606110f15040f0b0702031309060501020c01030c1b0606051e031213030c09050a141005010e0301022514030306100f0903081b120a080408 68
    0x503084030702207414249500034585001500c450a050b00880d08840094690300246000a5401030b141c40c0e540090551a400003e10340c03c5045280c1303c03040d0058080c20580c080d007a0719540b901c860700340c103551000260f071000c24004d040c2807003612000040c0540301d1003030100524010011395501c04a00071141410303100c508400c50340b40b0540300100c0984180046292010107410035400400703080c014680120000c110b035500c1c1d50803c2d020350440c4180a00140380c940c9541502c981160001e4182c813400d00c03118200000482d015004400142c22a0b10f40000d0904161612100300c9103025070004d214090384080224103a058410501282c900f82020b6154039035110010380248603010714210b000c0080d4500d400220186900007100a110380382102c018070424001da65070b400221f0f11103501c06600c2c01b0f00340c896403162481c07844101c0a400c051007195125a144400368100030b16240203070040d82003101c50300c9401c1014500e6031100d20b0b03600c0d290414100d070041403014014400b50851500144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 401136636 1250 401135386 401135401
    0x50102280c0b150d06050c07170711090a0b04060b18030c01080106050c03040f03050a050d09050a260f010218010503040c0b030c0403051209040501090e2d0303090606091605090405 79
    0x3040c1c50301c0c6a200e0010020b40c64080f41d140c0c00c40d000901c0988a030b0041c489c090b04240c20900442c0e50180d0404003210190300f41801708030034414000d10003000c0300c2e280c00b0a048651140d002c4d0074041c10b102455982c40d0450710b1011008030403442070341480703640603524002d030b140d82103114681903c801e440c0080e500e030101d07000c2510310700c91680604d080c402d00040001c14020f0100d0a003401d24810410b48011001c001d4048408042c4e90040980c0a510740008200280128061001400203032802e00b07a041035050115040010210346106280d4000a0440c04003e0b4803043e4542d401d42404c0003819418140c4418206c2d60860080710304001c0b00001041617881d003038068400865104088400d10600b1103000c052640080090354012410000041401d203158003414100c800c046c0000c101540341284072079042e071000704805001c41c503040c0401502d0201400158030591840002300714908080c030500010800091103a1094110480da408400340c1c060220382034144110360208d4952200103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 401137886 1250 401136636 401136649
    0x4021c020d080a020d1107120f300201090803160908030409020a03140412120204050a080105010e070503040b01030b040215030f06130b0112050a09050102280c0b15 72
    0x28040d512295030440481088541c0004140918266003030f03660185080c103050310303541080c864a0111b42c205490521268017020500158207002e424045e46561403604d80e174407031201040d41e4240c40b10301c940d1890014031010000348030701d0101c3d03c020000607950f503c80502501000d0a2030740000304005120010510824584001d0a21601900e94880d601d161641c0258481601000400c2c00d0030840d903403402214201c58401c0340c005c00e16003052040d109044800c040780048032803500390300384000315250302d03103404075006080003000005455040c448142c01c0d0001c002c040d4020013100f082001f0004a006c00801d04403035010b0031840241e129403001a014858220444252141c04010840740d420a49010b9009a10030741d40084d50140c0c07a054101a59046004640461b003034100008601000341d1000d540071502c0840000c0801481e543c0b9030030381c0e100a030b46c0601010821000d05c40c07220500448800040c0c1401c20600c4240543d5a07650f80c12801001d020f00308501d1031a0000395251013 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 401139136 1250 401137886 401137939
    0xb0a090b03041b0803131202010c150609051008010b030705150309190305030103030f1e11282a09090303090b07030501140105070803060405040201120c090303031109090402 76
    0x560b0b401120684681130182e40c0c0d04400c503803080700280b495000951104030040a2006078040e9200f100740c0c1d0f05a15070102d2450042c40280d2103999807100020042c2151065034000c000030400d0840191420568900303454001030740324400c0c2c0004078200640e90b038280c114038440f0f0940d24400e071a44d8460a08905203007500d40c44c1c1e6040c14405d4442010540e00c040114140c0340b0039210040070b0740c0348810482c1c41003034800c0c80003503648607020126841c074040c59058a000b02c0d20300c1151140711164617242441c141c1c0d0703041c901481c99550309807010001d100380b81c1d64081d40007203000031441a0121814141120714450f80d081503690b44002002e040c804d411602000342c2045111929003040c4030000c00a0209100d8895012245807041c44130758030500855080310341004034681142c450300104070041001401c200d042c001401d4901c081075065000e6091140281c0d112000210b28504015059030102c1c0ba4101061004100e104e0055864610194100c0c4d015a807040c84802c0c000341500c65800304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 401140386 1250 401139136 401139173
    0xf030f0703030905090106210506210d02010c0f050412060b0622150206040b1305100218010e060a0c02010e04020d02041d070215040c09050711070b0a090b0304 70
    0xa03004080705160f00800c007001240c100f0358403071200ea81c0c1c1c0d0600302c0f013200c21440c4040c0858806603144a907802d0903080b0507000580140711040f0ba02c100040401210b051650b241e2040d040b85000140d1290280709541501c440c60404624520540100a10742d20440c005c0007a2010a41001c0c0140081603204040c0c903a00903100a650f654a580508941201981000041001c02d4404142c0c020f00006e43c00d142009a001080185c072141c0d565260720740300800c90120303c03400c8020800070800402034014903604080006030380d0700c14402d903a40015400a1700034144147d811a01c4080d4441da000c0303490302c0320310b0700c0d180104140ca440102d40036241c01221940c02070000c511441803654582c0100110303030045074660450b441c0e0042d408071b9403004481c648090b8100e586480103442e60320780b146034403901c00c420040c0d403291101e071810201d4005a500c2c00010354800c6e881032840d17504220001c05400d0700c0c551182004403506e4000d0114145000d811240b510200116042000c242c01c100c0e2032503039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 401141636 1250 401140386 401140393
    0x1509090504060e0d02030412231c0e09010b07060e0c1e13140f130209040b010e090106140607020a0b04080c01081008101107020d0503030702010f1a0f030f 68
    0x142802c000028208503400c0d118a402100484455035000208441c216605080044614a01074a0746003a1010702c641104640b94040c000d002203c50510000d1035000040810103020804d11500820ba50382000085028030098401400890105810313120856403041e804141c0f04072181109041c00b410030001900a1030303000b808403d40c81140fa441901910544001c0d50819403c92140280c1c0c140d50244054580410007207031130904191b10640e8041d00d00c0d0200c00d10903800340d001c520b14540c111000c0c0d0b88280044011b02c8402e03100341640d608484c00d10001d1050324144440070410a09103044503201d114002003640864484100450041100e05012034866a88440d05034580301c245103a240040c0040b00000c110104541c64182951840c000521400000448003001001c002040c00c64428040c8901300c0141e54110101c440b5901c05c030080d60b20703820805170123429a040f5400e10141d290901c0c0d000e031003140c40e052802038004402c891411031100610003190500c3c02d400c0c02c50b5050300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 401142886 1250 401141636 401141641
    0x8061e040b030d08090d0504120201081e01030506040b15031018020a0308031b040e0106030f09060c020c03100209010c11040204030b0f040213050c1b0c041416020105010501020715090905 82
    0x3074000030741c14800d0300505c1c1580c407550035468080341c1c64440d5014079101002058003450255103e00c02942c0e009501d800a9030000c030b000752001c0c100c8802603200300c1e05640030004200400c40c039041e69a4120301c95850346500500503e000a8580c002ca010800c9101d036a02d0000300042000c1700c14000b5a40c019240100c0c035600c0b41041404c83d0320840b2a00c01d003580000c42c45002e24400c0c01200c040b1500b018081095908141d02103001d4810305140300030042d103403a0f040011a015108102c480d80e12034009141c2d003001c207003d140c1002104401000800d00c10701c80300b1050390b00002130101580c0d020301d00c0e02c41070703258174001030003405550005010961007804101101d00001c41d454002c0d40200c58110b4100b0100f200b06003940e604844038140c1c4801032108034260ba03810306209035150003010507201001c8400c03000c181196182c110252541201209101000401c0603d42045510070700c024001981004d0000c0d43d02e030514440c0f00032800c113014030609800c0c0710f158610041d2000c65420709c80f60 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 401144136 1250 401142886 401142913
    0x20a05040905160f030c02100f0911060c030a1b0f05390d02040924060f0303021213091a12070e07050c010221100608061e040b03 57
    0x5410900441d000d091820b004118402d907010f50206050041d65110600301c4070601044003d40b030039083c80300c1544191084603403000c40c01e020b5240c0400c0c01c00e10010b02d284131800d00e5214085820110ba000b46020006c4283c442c038040100c0d1142c032064100a0200f8082c01c5098039a1a03c0000143c20750406401400401c44003180d503840c20010304a4507556105520304c0c0408410a2100c0003401014000e50300265081c0440c070902000d00003400001e0fa900143c6960300444c9007418183e01d140c840c2c07107540c1c0c1d050645100b01d001905c2c441c03440b1214282160303006551001c5082c1000e1410b400808c54481d034002d003c4070718010300304210043c0041081e031044000c10000124040b031184600190140480200041c141c04948040298800079200d550301540c8641c00b18840b008195020800004202034100c10560030100b1410010480d03c0c0c1000013090100c2e00e904010204091182800b0700d50750740c030042002811400f3b1304c0746142c0c0c0c0720b81c000900034000d2040701d03034050058140d80c0884 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 401145386 1250 401144136 401144147
    0xa1d1003090318090c09141e010e1f1b020603060609060d0f02070b1e1602031b0c01091a040612140f07090501090f03080c01021c0b031606120905030d020a 68
    0x1170342e449803607140410741c0300c100d0a50a11030340a0340c1600880d06011192084203c15410100d401060400c524105030b2680480c0b000390704402c40403500394942e00f074190500e40c003c803a480c03200700c0d20641c40040310701350340020480d100203401584a0303c00032950410750307501d0b20300300d9071802544034080044510070102c1c0406904404015210000041c0c0040c011600309000c07005a842c0c02801248595600ca981016407251581c41c1d40171840300b03000c0212604640346080c6996071256004042149495000401d04001e0340c200c414201c0c9150040c40120040009660580d0154100140025002d05610303008200444140b800ca141d404180044000700e0030000d40521a03941d601c0c6032440d110320041d504500644549010060805000c00c0481c92100207000c0c2000401c001500c3c4c00b50700000c41c85245030455603052180c0d514804415145001c00c450041e090034014080c1006142200240c0800d20501d643d44481d907e4051082c1000820b0045620441405004646605615a0081a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 401146636 1250 401145386 401145401
    0xd020a1a0c040b040608040c0b090303161403040906050a1e0e09011b0f03050105060306030c090606070c062d05040504020a0c080a2105090c130608060c0a1d100309031809 75
    0x8c02e07240c200030200c1d401400204070b807101000a401545040580e4001d004003030000d41040e50204c9461200304402041480144000c01210b0400b02d00213003004100220418217038401d00d155080c003070851044150141020003100c00042d250072f421355540382d0081c05040e02030056400024003002c0c080c50250010190300c0a00301650741004113030313201d10a0000038402620016815072180300e80c02000d2500c5074429070302c038070089c0609042c64030580d1266030007070702e680008021444c1c2d034482130990098200c28000110080017080850058540301521038031540c02543e005607000900c1c102158001c131540c0344c403282c1c8401420f564281a0340020220340c820f50201d00c1d0416401004c0b00c0707541440c00b843e4091144400503240511086013000440d440c4000700b01e20058894000140c07146061204070b10a40e8522800380e510a1005401001003034500d40d041010710852071000d01a4443c110620560600390070001392281150030141c4550845005494219141c068003203408107c6800418 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 401147886 1250 401146636 401146643
    0x91603030f031a0a05040216050307060c0215130b04050102190504140406180e150c0304030305090f0a141e0a020a0b04030f24051302030d020a1a0c040b04060804 71
    0x240810800c40e44010343c402c0301c2075581c420724200d03003840640b0381540101a1031b40d20a242166980c100d98840d41140c12420013a60b0695a0340d4002200e81d4060211800051803421454218a0101c0b21200e035200c480201400501e008000501001070950458804403106508441428064403000b80543e103e40110701842c60b411203040b10710b0900d80100f00c25151b40749589040140e9514451006003150300030341c549031288080c0300090b561010402405003ca2118040d646c1c606030a025040c0d50b0b015002d81480d41c00944400101003011608552065100c501402c080d45146a011700d4442520f180d260500c0c1d800140e8511248001020388c9400c0c400c0e00c8448e0b12690340d413142d054030b0240b48030180c108820b4aa906d000100c0078008407006885800000000104040000e0100c4008550401c00440c0d059200029481c08100284642c98203200900480440360344908041c460320308403118130000c0c100841d03000c0025500b510702909402d41344c1d680703899448000602e814400c0d282503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 401149136 1250 401147886 401147891
    0x501031211060604020a09050a06030c1b052109041d01060617070c1b17060f01151107170d3203060a03080d0902010908010b0f09091603030f03 63
    0x40112a01550903070101540d400042d181c50340d12081400080d43c010750000302004108000400c550f91510b003480c0103403140c1d6800041500751500c0180020700707104043d8066448503400940003440c00191441c00d4001c41c410800035a40e002c480c48117602641500c180d02500386514001408507500c28000f078001c2c0d0400030300c21940e030f0303c2c000d0311031190004003100b00c0d2101400143c211802a000d0008082c480c1d03400c10400f050b0003c0d800600c45841d005002581c03e07008181c00b1000f41007003183c0d04805500010719a40d407610a6423000122900510010b0018000d0048034107001070140d01d000301044000e0384810070024502a40714446508518003050840d8a4244440410703906100f605100006501882c4001911428103400c014000c039401005030202000041c0701d03030040e103044a010800820712130814800540021300c40d403c406032036032500e11b0f00340c000d986031031021420034030907a14000181c0311040094203001c0a038162803da00c0c82680c00000b01940030401020811141d41c04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 401150386 1250 401149136 401149163
    0x2031521060403050703091d010510090f060c06020d0912020f010603020616060e0d02034605041508240a060822120206010512030304060c120f050103 66
    0x821030a8904100c06aa400310000400181c02100207051440c02800c2401140390380d41405030607644c0e20861008120240310041016050184960349440b641d13081000e201c50818000a0f43c50a03d8030a0700304024401150505021540c0e04030307900c034001e5003024440e030700742410603161051540240d0f070014414800c01c1d082850341032245c6c10580351300a081600d010205689661008000d40c0141c0d200e583c0ea040e10000385d101001810078a41c15500030310f4035035000d0050701c1c08041300c28104082500e400c0110502060a5200d907002109180251501d4041008412119402144c002080c040d100306d052004064000c054a0f100310742d400b0007403002100402900e0b46400c0001101074000442c01820301c10203000703180d010380c030082e41c03061328001c800d5580c4184244403003500240d501500a80060680315414010740d40948801d0350203502c82401660344554a01c401030025090316507031818910100d1180c51001012001100103101780c15a507410603008000a120484602201540 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 401151636 1250 401150386 401150419
    0xf04030c050d0807061104050306161d010c06090303020708070c030b10060806010c060e03070c09050906160f051605060603010b040b010f0e0a0e040302030c06060d0b0606130801020315 81
    0x3542d031940c1c0e0b1110446080002964403a0094007100d41c40030585201172001044649040100e144240011181c8a4460360048000b80203075052203c0025110307141c00c0340240d070f6600864186005544110300080c00300305414110001e001c0c10b04014041000001c94078240702d11180c0320400e49001c1c035040e00c601c0e15807141380101c8280c14400d100114a00000050803980a2051040d81e140035040c0800e51900034440c140c00c46e84100c104031400f0010100c02d0004101350300c5680d6000c1c12803001011282840082c2e8800c9002c400d038120100200c500b60307050007a10403826222000c0c82d134400c103a0010060700c1c1c0651503440032074600b070182d0301c0c0c014641030f5882d19000f404002e4006031542140c8420520f005c903143c07901040815003212941000123454014285a6031103203009030b003c1c6d52600121a0150b040c2100502222304c140e1035440c034000443d17005d002c00390300320741d04540c1660390340c00c10b10054403610540d92101c178295101008020b5100660a00ca02c8029400c0f00c000e860240030380c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 401152886 1250 401151636 401151649
    0xf060302010f03090f02060c010c0806040b1f02031317010f09030914041b0816050c100209041d0f010b040615081305061512060405150c09060f04030c05 67
    0x2101900055154070b003400e42c107000798403000d1800d000d11100d5107162070340d4011034129485032450900c941c0d51102001e080a40c4610003d0f081941214207000f501412030000c1c0311101041c5800e03007040040c1e00000240d038001c10445040480d04410b80181c2d03555050b80408041c0d80c221585910b500b08040700c03810244910a042d18564552a920304403810104102040108a05001c0d000b540d15907904088105810112201c40d20540c1e600b0458a1700d40385100e2420303040000401441814003140070701620210b10380452400d0380c0c40c016110501400020050900da80c6d942c10441320946001217550b001144201100c2c00c074034000e00c90101020240011982c852264460661507550290092881170b40c0721034014100341d00791040414292203160030320a05484007540c0c1c07101004040c109007012100148a20100c1c40038102f1071415840300d40e1104020721004410214410014400100c10802e0f11404a0081e200e5a2102c0c103170b0104012075401400169885511104c00040518100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 401154136 1250 401152886 401152889
    0x70e09031c0e070303050a2307020a0e01030312020a2f010605012d022d01050a11070308070912060e06130503070f020a0b030f041101180501081b0309030a02010f06 72
    0xd1000b80f0380307589551411686030b004101ca42040001c2c000c0d154260030740c440f202086103c8251341c080d940c0d91251042000700300c082c1d030005100c884031000400103c2e801c40138052100940342000b50f035034901c150b412a100c6919500982d0420a108510000c0c0345241d03420185242c1b01200801c0b5564403640151107641038000c40b81d203103950000c40c45880c01078194261841081034011a00000030350100c80c02c0110102e00346003c8680b060b85a0180101c0901440d50020039008081201140c1e0412045580c414500d02034244800c800c0415002c40c4600803400043c07248006c1c00b000b8020750702e802c1010b400d040e54068064410070b00402d51302d01d00654004000d6502c0401145080d4803907581245945c0c40c420280c3c1d00c550a41d00009045030120015841070980c000e800e4001e24007844c08880001e01c2c50a03281c10000003030107014a0310028684c007402c1e24824204030720315030b42e41c403c02044142020740c08a0b13810008018401d50707000000203401140021b0700288040c03030840d0f00038421600316 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 401155386 1250 401154136 401154161
    0x6050a090b07120b031f09050c0402030c0d0606360b0d0e1203062b0219031b0f06031806020406080403170408090607031704050303150604080a1103070e09031c 70
    0x400f0704d1031400b00598841e0900308d00c42d00075078400c200c811000034101c0c0c0084030804007015001441003c1ca281620640e00600041c2c14054114982a500107443da03030403691092100040d0901d900902c1203814500e070040104e4080d1079641c0c000404200054908140505201d22802c0246d40d00058400c007501e1150030041c2001d0000c014a5520060401c001c280481c40c2d4003954000e1030260301c0d240048c103004901060303c9911181703145407089000603c80105440300f90554030601c11043d60341c403000c0465113245000f041c81c0d482c11904075440100708000a00707840c400a40000c10b1030b00000c0c21f901c07886c001d8a0748008508803894512101d1400c8500401c41c07a0208400c1d05a0f2901c1400b42c481503000e40b6010301a2401041c0712555140281c0f400d85545c0e10100c01c010148003880c2d5540c013000700c02e65819050a281c0603416588690115005000410300d00710305a003500c00b00041070003012080ca41e035515003000020240c0700e90040c045440c194800b2040c0d88207807002405410082c501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 401156636 1250 401155386 401155423
    0xf081b03120307110f03030f09010c12020c1f0b18070504091e1d060a060e0105040c0e090f010515030f04030f050c0708070f051c06050a090b07120b03 66
    0x910384203003030307550004000200b0300812000d00e80941008024541c0c4605103030004540d44e0424080c180c0c08450004c0968007180c3c1444070b188000c503400801d0700343c070900d02c00004d40c8440441d01282c2c10044442800e48d000c0001c1d08500700b98005580000050007000e4a1102030707111004030000d541e48040362864007060701003104222260030b9901c170300e982502d04e0b411020760101c0a41c4241c01c1d10b010b1354a41c201c120921161f8400304006005443d00401c00d0b41c02049103d00d418064010680e05100ea81d100741c2ea01c0e0962803c09000c1c807140c0b04100c000a100e4805460051859402e451082c00b41c10701403410b02c114440b00c8010348085038000c001c841424080d950b1a5903045503030700032000044003040b0b01441281c000709402c001000150134188080c018035810720444002e03200321644424411489170030f44100c030310304803056480c280390003120101c0c40c0c0c3e86d10168400901586a8002c00050285082050300c503444030080c0c0e80030381e110700c050081c540303c0000c0540d201604121101c0343d11 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 401157886 1250 401156636 401156653
    0x13060605070b06040204050d080909010f051e06041509030c050405040b010b1c18021503010e0105010f02010b1806040f0504030807180f08060601081b09040b010c0c0f081b03 76
    0x2e80c9841c59582c0701038001c2001d80b41641b5003020030040c0080034400c0318400b0340801c40c415180b82114080313001d020b1142c0703600d00039840e05000446a9180c40005040b4800da03d05050700340e20f5500450f0048c105002300c8000c58018250010144c000c40e22080e2084405103e0104007454980103143c0515003180d01c0010503401d0101100c2958014100e03080407100045032008030080c0c3d8018203540c0c6000d110880c4481401d40140700c1000c07464203100e03c042e5010401401000d100444450641c1d4080c03030250104d80c400402a4014440088175650100780c040380f150702819035502d103d108907801c1c0d034240800c80740c0700ca4100a4500c2a58001c0204000c0d00004401510410102851464100011901c141d8810503522000786036004814030350002c500300003055810414403600900c140030005189014401e00c20700c00d01030300c0342e19480740f82c0319003504000d684900e49241825410810212159a4511003803488600c14451900d441c0120700440000840c04040f07013180e114050041c0c808103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 401159136 1250 401157886 401157893
    0x5030403030908390d0b19020306030318012106050f010f230904020f070311070305060708070c0b09061b040605120406230415060303020a0303050709170307021306060507 75
    0x2004c480d080c11894007501004801c683d51902070390101c86020b04880212030614001c20b416070003125070b816840c28010001c1c890252000412603d4031030201c0e80e1070781e54140e00c5004846200a40e1480100200c40000c9103012804991103c801c842044a4819040c580d242c011b41e03480c1849030806000c82c411100180300740740115203a074645070f200c1c0c0c013492601400f440010220b070850070840e680220040b5002c1d04042d0000c0312080540c5512004149661840c0c0c0c44690b2501e000300b0040410156001261116000701510340700c66601103410525480d1500034181d8800048851212120355013000f01210203040d8111801e03500c8583e116072a00c000103144055103040500300321070442d42c0344022001900030181d204040e00c41c4070a82d18990030705c0d00b09105030812000810380b000f40b0300030041001a400041e002c00c0700e43d240c100403a05a03160902070314803e101e03520004a904032407940c0040540044010f0005078802c6076070b08071004003502454200c5a05004d010040340c020000c80011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 401160386 1250 401159136 401159203
    0x14100b0304110415030305130509060a060c080d181104020a20030f070b0a060f06051b0f160602060f090c3a060b150f0702030a0f05030403030908 64
    0x1182c2c2c00380001c0f5a000001c041419000f0b141e91082d8005100850341c042c0b00300f071100004008002c2251030f0001414810b001504501c1c05201d02e2040c0801c851000b01042002d00c02e440841c3c180c03d4003040f9402580603074183c0001290380460b106c0310f03041105003141c80c10b8402c1d591105502da6454600402d602e90356100e9403840c1e042891680300074002101303c0302125000305000f911540d68101035050007a903200680340300340c00c0384046031141c450038045c4903070007426030b0600440b45103610700651a00c010181086c4040c8040b03a05405401c03413003604007003140190812911035508403000d0b660350b1054405411000c1d1850440c43e0004000c0909501d00403001462100c2d81042d146403103a178081b40210840f00d40031034504c2c0b0b01000f078004414850588070b00861a0b50030307034441030b03156a0514540503620030039580e1010280042101029500c00b00920820140d210601e081714041c0c5041007036980d0058032044000406ca0000440c90840224620303d21840c2e100003d00510f0102114400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 401161636 1250 401160386 401160413
    0x610060309260a08150108040b2e0503100b0f12120a020106030c0504090f0b0c04090207060203040501200d1e0203100801060b0906090d0609021314100b0304 69
    0x2030348a8841005280b0310800c1007034034500e0410001d09a6210000320380600181002080202d0b504802900001166000354079644d0041d40845610b030316a4541e015104002d00f034508081500088074011641413040c0c100304400d5880403401c076031150440b42611000d4403081e100c1c550700b2035a58a460900c0303050001c400d94102d407848043e1000f140ca16940307095650003080f4144c005179103035802001408a02810305002e0403060747d05014050030b2b92101904030412000040c200c81d45000040c3c0d00e440c0c15410313178000d040003440c1555143d40c90300f4050007a400c1502c00782d525520f0040c42c03c003400f00040d84d130040c02d44084074150518140d0040b071070042040c008103528400c00355102007003205151005501c102481401e540d502414107200c542169016040780708892002c0207103580d5980e608094800100c0b08071045803090701e9a240034000391a071080025000b20404804c041d8460a580124114038415800e40e40300f81d0360001d10048411b1035218440c2c0f00401000824007194104c0800c1c0b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 401162886 1250 401161636 401161643
    0x30e07120f1101021f140f01060f0c06021603080a2d02070303090b0c0a0f05031308090f03010903050c0c18060616050706020f060903090f090a2004060e030610060309 73
    0xa02c403880c040060700400e140d00440180c0f6686e601480b050f1030003203000c080c2d0003404c02044083c0940c14140d003e0201c5110060310410311401d60018000c1003440d4048544c203401d0401e40314480a11454050041c8000b034503070760500742c24110000d40410a0b240c240505081008003650003180c1001c01070300035400250241d0403d9102c20300d54001c9401000b03030a01403d10300d1000b0399261410350000386078032801a0310b241003000c00c00622082030302c03120113520b0740740d0820300c610780c1c40d0302600000307410118003100643c155081c044040140b42d0040050101102c54000351000e941c907247c00c1100c3d8440081d1340380c20220190020504500b044405403c4500c4200080d01c50741361641c680340d20b0032250b544400c005a0003400303c000c007440c041c0301031a0440d0f501401542407a82020004100c04030000406001d4698100085c03040c05007070b01b1003030190001c10000340468410348109402d0350b20078010180800c62a401e5101e42e4200002c07940c0c4500d4070030080421090425100310701030201c103c0d064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 401164136 1250 401162886 401162893
    0x206130803041203020c0a081c2006041b0503030301090e150c1305040504350c0a0b07020613290c04031a07090303080a06030501020703030e07120f110102 68
    0x45a8000c08000400c040d109400592846510518000b8501008241e805010307000901c010090b00318002007498101d0551141c205034024444030403031707014405410408180c0038419001181c2040800c0c194000c900a400c0036000c0c000d00240c0084144080c800c00340c040c1c0c810801000000e11591002019215103004e5800e00e0181600f1441c1d4040207413114003c260740000c1642c099903100c1c650034010314095800780401d00e45501d035000d1a050003800001840005403050031448261441007607650b806000081d01c84840403100c50341c0d80c240c45004c49500e903075907000c00c214500004003103200300c2c2e696021080328546030b6510164400e018180c43c0c1180211b0609000700b00510465034443c03041c801c840d6448502e11304000c07001d6001000c031449801c0da06800e01c64095400300002c1b081d03c1c0c05060515090300c1d0003004800a01241e031001d080f551010410404160389508180000d1000008482005840e44400007110f103020300000c00040003404900d00140d022510f51003c410140143d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 401165386 1250 401164136 401164139
    0x20d080c07051309030206131b0303090501080c0910031a0a0314070b093708031c1e0f14180d0507020f091003020301020a210c080103020613 62
    0x21482190405003444849800c452001d00090070034900c0c5000d85a15140144150000b50324081d4035a140503100380140c0e00186581c1c414031843c400d1000428680c840e000c2504e03580c03420014008146406043d0014203903802244030b8503641c8050300c00074040104840c201240a10081e80100810202c607000ba030074103801011a0380d03c04142c23800441c0521403501a08540c0e41915003002501e8204400b20306007808020710680b105505040040504100303c80c0d0300741c0444030901d00000c00e070340740885101c2d52100441c1d201c1c0044050000030340c01185440c100340c0610105c005541c02d100c100122031024041400407100150405140c212070751400044c03901060400100c0a4011504040c140410b81c1502c03210620801c0030310b0a05074a898200d05104407030b0300007280d2004050000c3d108040001c045190108140746c403400840d4000c1c021036580e291602d01401e400d07a0840e00f102c85407840400080040e103a0f015100d4444199a26106130342e09550800c03102350807018000c9c089900d1140b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 401166636 1250 401165386 401165393
    0x7020f0f010c06021c15030b06090a1506050910030519150503060a0e0d0302090901030b0c0c011a030706080105030a0611040b0c07090507111005060621040b060901030c0b07020d 78
    0x41a01d846816900000b05c29107290082c00e54821412030900b1400091080004c6800320268a0300454101d94841c92511121400c201a15405e078030540040494800082e010747c01100904100300141d07400c401c009003409043d001c440c404c13100b50422100042107040b01034115400700311403503600482d040c0c44603122030100b4904402164400540b5654202e0000c2284042050701038954162400f03514021070709011925841c410b04c030040890b0032200c041141d00c002101a5402c2d0321114000b0489210102507140e03a03100b00105040c0070340140100458014454000581607540250041603844015a500d02c010008603580b405050001d1002045114040300185503403082100207140c15401c005192080715005000fa00a21883c41c07841d0b0384c2550301084584800c130402400084980d521801324245115142941c2c5503102c00040310201080342a140c280601d000b8841c1c0306040d6200410f01003404400e0001400f0000c041504011200c0002c0c018400d140c8040c0c00141144071a58 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 401167886 1250 401166636 401166641
    0xc3f250c0f050c0916020d050d0908030a1509090506151809070906050901061e140c0a050123160203040317031803040f031506030b16020105070507020f0f010c06 71
    0x10102ca81e6040781d0700050f1180f0b032584119401200c865001500111140b001941d5032042195000030302c400480c0400070094950300545440d50050b00440d600e140042c032034401004071900c45440e1900d01c400110721000e462285640969000c001400e8984a842c812184161500c4290354051160058158010220112a40100f1034000180440c500f803003414030a541c80354210600075644280100111903002c624010140b0702011002d140142a0004803801000c01a801803619000511525015000104a42418081c0008120100d04140b0071040003044c0080c4070128002d410120360180022031210342c020b070082c011285059070b02e40c0e4441c1c1e06d22544d03001219800c000300402c68845910242049440d44003005940b41a080c110b10700550717162400701800503d840300603900c03050055803042e40a50740080384080c151501c8444c90603210550442c0da00154207000200d03445c0fa000344140c1d1000d03039000382001c1d56107000100b0b020010031441561810000111701c040003203159071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 401169136 1250 401167886 401167913
    0x110c04110304030e090606070f031103040623040b07021021020705010b0a0608180106051c120c08030703020c01091416060206040b010e0c3f250c 64
    0x548030039202d2601e820041c0c40c0154588000f405401d52a042080a540300003c03100322590001c580f5030760110328181142c41034020020a01140300010700420a80d4126015400c201c80481a4155142030014840c1031802184034180007000c0611030000189010080d8507100c913081d1505030005000d4080d2115190000c055002170241d0024240c4140503080c0100c5a10803c03d88140000d103140080c000e103d104028407012201003040307c3c09a4000082d0811002010b00805c06120402203002010a8002c4030b0804c4607800740c0c1c00d400c54400c82c042e8101074071560700b00088506598540d0310a5001e075200c0c84006481e0356031180c4030000101e5402c502d60603001e44000a1105030001d100d81c000300c65194101e0030556001c24104000280c111203142c0c1911520803141c1c1e043d0301e0700404400306002c1c141e103d126841241e5080c24440302c02e2141040d1100409540c901c40480504406070018010758559502d0903c4c6e0f44507139803002808440e14284016458013106211058a9842000c80003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 401170386 1250 401169136 401169161
    0x1804090213020a08041a06180a0617010e07050109030f022b050c0a060e031b011e0305060f0f1008060f0315010323070303140d050a0509011401060f110c04 68
    0x203003060100f40a0800c81500190b2403401b1500d0303160030702070006608646c501c103009500d405c1d10f20000b51807074440e810910080221a2401001806c0300e8201406060b4100c54100c0318451420300298940c0324042c0b080031660088002c0ca0610043e03000d0011444407504981040140101d14820302d00c116408199424060406843c0740b2100004018130314030b0390381c004003c100642d0301c1c440e01907a01044080079402070240d07608100e9219001680d003940c0c1182c440c4452050790511900280c0c16030402e034842e001c2241c0041100300e4500400c41985462800c15401c45510a95050018080c504140c1c100768003c1c81900c0c90b08000000a00d007100c4e800b400740d11001401d004000704401c00141600786082e10913224485d151000c1450350f203940c2840044e0400c00c00c510384120300c50945045414150030944284134070710344403091001515094900c01c01d15880c0c1041592a000755182540c107903285030b628110080d81c92130044407141c03c030002d848211301501003102c0f1b49560301c0c812092090917 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 401171636 1250 401170386 401170397
    0x31a0d0305130609140415051503071121030a0b0406060210061a091302070501090605090d030905071505040902070302060106080a06080606090c0d2f1804090213020a 73
    0x106226039204000443d0301c000f043c00007045003802001d24441840060348402c0c1d074001500c524129142d030321101142d00c500d822140d40c0c02d80c030840d031202d03000440c0305176040c0e2111550b03000740c41c0714681d540031010301241e001d507903c02d0140204a4050021604042003040c081500441107001804451040e0320810260780600201c805000e4240540001025011a44408004602400c880c1442025801481418500307a07913001c40c00c0d158103a80382550050001c01c03040b0300e2498003c0c01003c0c01d640507522480f0708140b02c0c603118030a00805040d02e5011000d417815924100c05901082d407002148811b00c0014040856400755500c0600b41d42c600030b6005007680e500d00b0340f01804451700540140c1502c3d080c21000e000a0900003580e54111109581586407541d501b200842c2c2c0d8000d18038010b4041e402d150301c40b425003020704880c0b404119003050742403080780e1414894002d4031071481450500e005001c11400c2d90300e850f51081407264005416000b50b98060350004040340c2c48004400040381 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 401172886 1250 401171636 401171647
    0x1b0206010816150c1703090606011b420506010305060102030a05030c03070507020405040c06020d030903021504020303070b3405030402150d0c21060b040303031a0d0305 74
    0x103400c00c52181c140404042c42c030a035a050064150500071068800401d03c011842d01004000d4103009000901084106880c3c9130306202460329203484013640e0090004004a516036a064a011100010a5408140f80040181e040507401c03140c50300c0c1c01c0a10402c1c500025020980ad20400752450000e04214005810300c0c05e00005000c442c0b0280c102070440d40144405030b003540e00304080743d8101454483d429142e40e1070110448a40c410840000c0d001070070304061004009604c0320240946a030354090b1440959034420803011190203000282c0180c0c0843e0007071500c45a40110a40c1003070000e03054a16041d42511101c0e01040140c03107101c0c0c80e40b0201802c03590070144481c60240b0004200a107003202002140040c454000500042d224011603c050f5601c1160107007140d041085c8100f00b07214940380410080d0071403014009000d158104070155242c280c242d07205a00079103100c500b9041c10903045842c104d000f08140140c0c0e402100e0803034141f540ca940c5110849907a140310ba90f40c5175407035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 401174136 1250 401172886 401172899
    0x605270d0b0115050c0a060b040f0c11060c030928060c080f060301090b0f060102010f0f0218060a090b070c03020307030c05011d030309060708120406020705070e1302040504061b020601 81
    0x11480f84150030801c0300c02c3c4448115280c01203000d600e01d0b50409804503401d0b00f554000750050030b40c02c0c40400301d5450444c0c450f07100c5801c50400001c000605090b0f880701c0d541c111001800c0d00c411264200b182e00241e594040c044140003070119120040c1c01250040156965014100d42084400c0c2d808256090208802200c00c881902e0388160140d0003401000e8030750b40c610440c0c110140203d84120702800000351142d100f50310000d91808010414080503440182e684000d6200324001038011225030207a03070041c148242242c00300381440d52034084ea2171030b03d5134140706900554422600810350300780001c09a0b40401149000d1405618903c072a40e05d0728001410103c0007810200e4840403e00c81000c95a90110a0340c002a00c00d1740c0003950f90246e85010985485010000000b8030400c0081c8014450f840e030281800b64130a00850305000e40b2441c5041903001e049400010440c100181500107040c03d8200b107800c0f40c802c40c8041220340c0d0901d8011050341800100074010780c0806c0c01009030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 401175386 1250 401174136 401174159
    0x90203010b0c1e0a0f1b030305030115090305151e0403050d05071107050108090a0507091d0303090712060e030309010c09050d02130c0e031c09050103060605270d0b01 73
    0x640d0303c480c90090611010400300e64466494a5003e06102000c3c0f49580501c210302003080d640012030008444515124034001d4015082809070000714442c08440301c1205010719400001c0e2500309008141c0030100c8144a445900f004212038102c0c0800341c4002030707420819075140d029900c01c2e00c480e500c034503955001c0c01c21103030000c220004000315002e243d03040c8540454448240c40080c81c0c00e071004c2d1b503581540346c50b040310342a00800610511100189000c000da00640c00c0021100003243c1131140c00004940da030005035510080d5400207101000082d412009132403106208107170120b495001031080310300b560400c45596846035140c1008958040d030007040900607120848250340d2400071a0082a4000d00f01c00c8041c682d41d5880103000c8895026481c0740420200060440b0080341340440d956400080519041c40032901c11907005c03a456000740a00b1040d074440e541c903a42003800094031000700c2420405440b02106c4000505101900d48a8031602450702602c1541001c5d45001c1100d517030b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 401176636 1250 401175386 401175403
    0x90203070f051c081b0c0a030605040506092406010e060409050403080901021c020c030d15060906020114070c020f042d05011406070519120f030e030409020c0106090203010b0c 77
    0x848600f41490001c0c58040039101790010030994142c0c10340c165040c240c80d01c0d04241407180c1c0030910480020400036240c0100d03219920400075900d89441d10402555101054110349a0304e030750245412418000011789030f03a02c440140360481c41005d41c04081009035010341c000b141c0550b00c41c4200b00506400224403504181001d000318a464036000c010220301265180051181e9000a00464400020800d4850802d00000204801d240c0140b51441d078144501c03440f000b0618004000030958018450461050b00d0641d0304a000d507100942120148201d203c03ca80c040510340f20712030707030741c850348684c92072025590030400030300b0f40340481a025442120858a100c0d0705100c01800520300a0545091400007030340c074035840fa201c61506504000110b00c060404918902116080c0a40040c000800c08000c1d02e888035440c42e08001101601e050b80200d03070950340104002c101c11803256004005840881b0300001c2d41302e46400800c01030780d0003a44040c0c036141000ca03c0d100802c106102d80300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 401177886 1250 401176636 401176669
    0x40317010303111903020c0d0204020702062a0f0c0f1915090b0337050a020d061d0c0d0b0a0807031703240402090315070807171603090203070f05 64
    0x2d480d44c400d0354000d5590310084a16030140151030b10180854441c0e030103885256600821881d100c0e00100010801200c2070940103040748210406401740c0d2401094200c00310301d103200075100403c031240602c041c0004030512150049035103a200310082015189000c0900900f50009441c0c00c0300c250014031141103500030244290f010000e01038100b40b06006c1071a02e801040700020b400d004014580c3d00544000d0204018909060400c03220601640c0100b00c1240c500c90f0820107151110140d60307103034a990030040242d1265001003685081c00d48040c02181d0340380c0b0404242c9048201c04107c1c0a02181d2003c03030154030081052003080050010340e040c442000141078110310388000301035000e40e0b060300b131900c40c804415a900d10b2903c4940417115084c20180484050601300cad2004003400f20111940e8000a111501180c40e0603c584110300071004420141440e40e1074008101d04084143c2c0716010516640d05c002c00016241404038000030950f0540302691a85801d040c04180d1143c000900c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 401179136 1250 401177886 401177923
    0x40501091b0e010e090102160501020301030c0e01080318030304150c021e030a080c03040905040305220b12100e0106050d0f05011a0d06090e030d0f0b010503060904031701030311 78
    0x10302a42d0301c0c0452883c11907282e11481e074800d84400010384d00903c1101c1203005800340b03641a903401d004054000714101c900c100000c3c0a810b5807101d85c0c0304124000c6c01060703001d0300100300c003020300440c0003000b100418004050301c0c03809070b4400d1a005081804c0c8540c80102d11038054030000d5141c6101176400340c1c50300e480d07000b20013401440004d80300d40e41c890004020040100f002001c440c002c2080c0c03005002261020000c904040c20080c090f0341100100b1804401c03145000306001e800205c0c040201c1e801c0601c103d040c01030008007000706110081c84101c0707a01c1d4800740090080191002c1d14020300040c1c8440744d0724030404102c0030580702c4614603064440e06250040000e01d401a184103d518101c401d40d54440342001000400707055aa07018410310790814961aa500c00c0c08801407034880c8080408000450790704225006035408a4a0b20b80454000e000161150424540065201e0310a1a05c80c519805050303511661000a8205400003900003035910300b400030070003030300c1070310221110303070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 401180386 1250 401179136 401179139
    0x30903110f0d02011b091701090c121104060b0a030902040f0533031911031606090807050a0915032f01020f06010303050c03040f17060f040b0c160803040501091b 71
    0xf504180643c8241403071a44800340040c0d20400a520074049d041c1d04c0b0030b0301036940307a9a200001c00e212032a0402e4600c1081400903001c1341c42d0070300c81c2e5801c440030058620304210040109400403c1181010783e0032075120810f03940c2083c4503110305c42c41a00c04101401845644500c0046021b5445c44403a544100304503106559917000541c1c00440140500442d000000e01c4c64141e4a41d2200c00b013443c1c040c81800c0780550208501344000e07055031915035034003d14543e0303082156503690061145940011101000703000300c03862500300f41c0c5511141c180070006203513030390b48810343c0d4a0b1841c9a00304400310300180b00d001000241034801100b009100420207200ca1301c040544400301072000600340200056841c400305002d10030f40e0002c02c0701010486003650303144040f98a40c40302810080c0c0364000e003400600040100300450780500d030482100713141c940e240c0481501581c01014021210084441101c00084645000310b00c1b9600c100f00210784800c0b1464440035201c00e120741000003040c001d90 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 401181636 1250 401180386 401180441
    0x3060617030418020d0221061207051302090a051e040b182403030a020709110a05070b0408070212030702030d020105090a0f0c09052410050a030903110f0d0201 70
    0x201030190f200510341c01a51032031452203520003841180035501030070400c0040030040c0d001c980c60700d601c10b01c001c0c1c03504501800c03500001900c9221038060240e00401404d85201995100e42c046c040c250b40c09448944034070344030400079503519144000a86800e45842003032440d400c1c1402800d9481c102654540c160101c5140c452400900003004000f03581760507038081c3c0b02c2c209180d51120f001e00c405801daa075600501e200007526a261802614a15418500c0c0c6d12412043c480c22500130828a6441c0f0f0300349691943e95004445e0040c01c00c4d280d0030002d100d8034001d0703903030918107802c4040315200070340e590305071841414207044000029905691401d001c2083c910030106c0c44410241e4007600d8001c1c1c1603502d10b003500c00825541c011281c0e480c504010046c8003410365001c190380031000702840a0704003010080040508200d030814000a0007406500d210130702a4025443d1140b280c1040c41c02480c1d0b18601a02d045095071411946a203d031a00d180e107140c0a00c26500519003010700b032142c0080100e07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 401182886 1250 401181636 401181659
    0x40312030209042703201e0319170601020d09090c1110020408070b0427090203101b05030103050604032105040b060a05060328060f030606170304 64
    0x540000a0507000910306040d0b54659000850f490300f221034615a9080c0d607481d1a05000224200320046200e1040c5802e145c65101420408100030100a1581c45414000424940c4043d00c02804612040c8401c00200d0801c182203c1c0350380c0340380c0d2b58900050711002c26890340b81010780303c40d056400c0894403101c0280d0041460342030310102140070070f810700a283d04403507145a40400090500465190b5414503003680c004000b00c0d01c3c001c0c21107190a071140000b840611692060700114014048006074090f05c20120314001840700400080e1090103801190500c5803005040035001d0740c035480129000c40040c014418444246885411513045650342a541c030005040641400800c2400c0c40003139100c4940c0c88a9040b520105001508cc2464032201c850300949821f8403604040801040906200e01030306e00c140c50740b02e0a8a508012480c006240000300c0c21809865907c4850100390020002c148074010340c8202400681c5900e07001c1103001d0214a014082d0380d642042204210228414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 401184136 1250 401182886 401182913
    0xc030807052a07050d1a070807050d0b12030d0501061b050c06070c1206090c051806040e0f032109010c0f030506130c051b0102030919050a14030304050d02030403 71
    0x81900011003102c2d010031501e8a01c9030340c41540e000805545510801518240d000411210041d1034400307511421401c0e41c0041c000c45d5803400040b024000d181c10717191141c001100b0404064145185141000507041c110b62103500d242c07170381e65100c2c03004104003588900c2ca8242c000162412000e81d0324581c2e102e9031a8400c0c0c520191040c600072500c4401c0c4480310720a00c0c0245144036200407504c5481ca070440241c130600300291014050750303034002128140403540303003460040b504540313950b6a01c200c1040010320b9543c40184580c030441688040140041000f410410702554244c085c01c83c0300b410310f545002004103084034603410140c041c40750750342118415008851a0030f000c41c6a603100004110311040501d002ca40e1107050039800e0307010a4210008180e886212800701500c100e8241000d400d0788800d07503010215500084c501352a01c107041030351610f594401c02c2075030840d02c120380340c0d214189158482c004075074000109000822004003c4c4030baa248140c0065070416146403180980300600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 401185386 1250 401184136 401184187
    0x803040308031b04080706090911031305100518070b09011707030e01090f290106030207030302090301060f180c02060f0c16151503020d0f02031c0c03080705 69
    0x201c00324a0107540f20700603012540300c48183c0c540351940d408220742d494070548140c0c004900b24007804101c06540b4002c24000b14440c40b0410b246460b0110201d0026001200c00d403407034040c100075041c600e202c5001e82c5000f241d1542034504641c1d017000308103041860944c84024101e5007080800300c02c0c7d8102c5070303500c20701c959008000500c1d660602c0036406041c10b41e803464290b5107046c00e8442009145851544800e00407806407000d80154520762601c0c10100081c110524039034001006214800c0e001001854400d140c09814001404017080c2943c0d02908149468005140180028a11144804005050301e102070112030914900030703468180181010700315820100c00110124001070071a01015095110080043c15504101400e6503498065400c61340c10070580810f22011884808207a98008200840b2030f41300340c0e80c8070052110640d04030f8050050030701b4503c1420100c80810038440640e12040c00d00b900b249002004140300821960a1003c1403011507403043e400c042c000c0c24400c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 401186636 1250 401185386 401185403
    0x90a02040228020307120507051e0718050402030c010f050702040b01140307090807050d0312090218011403010f231801020f090a0e01060c110f060412020f03060108030403 75
    0x700003041414200411800d42c040032000c0070048039554000000c040d402d0182d2068650000798410866582c8140316028040703500c1601c070102d0204000d0002d070002c41940e800c40c0d100d80e640700450540e01080c01c140c501801d40c0c80301000194103041c08a80c0120782c0910784030107442d1342c0d401c018015000300840a03019aa88407080c9200d03902401041840d0501c80284940302d2802c01c000811098083c06031f4807590061385030001d900d082044900c0d00042d859190300ba032449085400f4070003800b080b24180e0703101d0440306a480110204644041c042e0200c0708900c0414991b52060500351145242c00440d2189800b40740c0c22a451840c41d40b020420448001a80301c0c0c50300080c1c0301a420f000650107805510004007002880034080040c02c000794240c50402c60180d40b981d000b00d007280c00340f25610100721075a08120004900f6820841c85039002060355501c0d403d0131000c20710348c0c0c000d0f40000d00f00396141031419055181c411141c680020301180240b20340e6062001d400d0f2240194070000f00f44d4003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 401187886 1250 401186636 401186647
    0x7330302090618062502040e060603030715060b0703090f1202100e0112020d140f010321090b04030803151f140903010504050703021201110a0f02010b030114011805090a020402 77
    0x20f4030714040300d41e110301c490b840031135024001540702100036510001b03e21851520024681400f80801d055200e00d0b0014091030a104040c4c440c01c1d2000b685500c0c440340d460390b5010104080c00840040e00c01076010b656100c980e9400d2040c400c0e0141200c3e00f1599080d080981c031000181c1d1080c07110b0402d41c4052410031203000c5440c0050f558070114000001d1900e0004c910285160b142c3d51068440410100b4842c41030744070941c1c1c007040401e0a001c050318084004014800c0e004140d268000302c600303d0715001050540d251b180103540c0e041a0000c41d0091000021310020b4034209611007501c00d030440d00034034400c036521820304a60349111888014828003001c65501e050940095070311500000d00240304a140c0b038a030542d11100d0710b00040707104007612111005103140c144074003d03440d0b64081d9030a24081c580c243c1565044054100802190f4a40c0103e181781d8900b8001c160b4403200b2041260002e5041180c02111414400320fa006900c1c074080800020960014040c80c00300d806640040c2e507036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 401189136 1250 401187886 401187889
    0x4081c05150d0201020c0909010507030b010e0f0405190c08071e09230402070822150e0d063801051605030403120206090c01080606071407330302090618 67
    0xd40c8080706500401d10b404001c81d02348103400442c411b5609a41c01c200b2441168015190400300320b81c00c0e60071901031f445111303840c1401d51009810804101210090880b0300d088502a904101c1c402d84c0040c1c444820304c00840d2f00205c0b61900c03009032010b46441c80311a81c4005141c401c25204010a40d42d0428031044483c0c0c0c3d00c164980d00d00009081903540d0f01003410006402d40c4040078269a412080e0380030300f4000e45299403070099a585000c3c80c41210040c4c5000ca03440859014000d13808243e81240c00c00241051080d000084004011440845800040f0300c84080c2c1b1200f84d040a088900203c224680e80300d400c40b1b00c020503481800400c0300f200d080c00c52850280d80c000400c584211b004195507203400050562203626120102d5403969400001154100000d50b9810f401c4030080c081171001405002400c3c02011361a4101c803601540d861030b000c40d0415498201c520101c0c400307181e03000500004c502c03919520150078294505801800400c49074030544000d1050300845420021b500d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 401190386 1250 401189136 401189143
    0x40c06090b03013c060801030c0b040e04030f02100507262217070503121003030804140a170a080f090c01050c070e0f15090403050f07020a050904081c05150d020102 72
    0x1051324642190b80320f50f00c2d50005012140203000964255003050000190080d108013102c0640740801c100c01450b80703650340d00742e540701044000c000c25402001b1064102120911540348200410b0b0303102c808c0b1440d100b00c203031285400410400d0650154000b00000e031100802c080d4885c1040004130301c0520543e0402100401c5000650140341000081041c1800780c000050421420701d002c00d220313281c80d10710440396084000c2c440200424011000100814244c1e40d4001c444020a070917a511840f455950700700301c00c00c09100618040010a4603048503500880341540098450040f03100c909003e030105541d01d0300c0310f03100c0707041002c00908415500d0060102c003009184501c1058000c0c1040c99041c01500b47c200c4441c0c410b0131811094026519180d90780a0059406072a02ca2070607030b070103500e0101c540c40220280e811229a22000416032110710030305100fa40607132412622200396440c412400020104003241c481c2c24030701031094103144980c081d030502408441c00f035010091840180d08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 401191636 1250 401190386 401190479
    0xc02030615030d05130b0703033c0e190c0f0e061203071a0603010b1e090702070305070603021804090317220204051e040c06090b0301 59
    0x4140c000c200510249407440000e510003101c04406584400700200000c94060217401030342d0ba52080c959100f00b11036184840145541400b82c0b8002c120350480d40c000c4240b00421035040801c180d103200910100525034082c91500ca07100407001e0005503651721246580301240d034641d1504540c0c1d031001e182040070b00c11885000703207513403d4440d02c1c1540c1c0d0409401c40d24001c40b10030740504420101e541a0240110440d00c105500800480146512000043c0c4070380703000302903640541da1130040125541c0c40501c850380c83e03180c2d541000304140c0e800061080e0004050045d030199445140c082c000200003003210401d41d0300c42d2030010385031899100a8059055242501d582045c604075006041c140e0262034800390700140060903050b03072034403c03424203c00274100a0040318010389980500620301504400e40110000c8010200c104800710400c1c0c03402403c1d10b007119100010841017056581051400e0010301e4901c81c618110740c5003a400c4542d01c04410900c8543d00c00360840034680d440420403005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 401192886 1250 401191636 401191639
    0x905030306100e120d12060320030c150714030a21180b0601020f030a121d010c091404020f0304140f16060801080307020a050d0302210a110109030509100c02 69
    0x8000303ca480e001a40c0307400c40740f0018000030711b030000c0325102d00c101da002e0035040320383c07000802c6c040a0002c0d44001e1a02d00c460b00440c1c0c54020450020516940c0e0300b00c44c07c00d480100e821a903245c0d41494007511101004042c840141c1051115a03801e542011040846e050b001d11000541000110070400038501d61000d002003804248203002407010040c245807180301d0a8086402e07440ca110302c1a6600d0044000600000c1d0081c00001c65030f144540103804005a102030b5078440d000003a650909441c22902d01c00c00242c4958010844558040e20210308030304240c80861800d04199560741045c0300060015180d0b920811800c0c400716403c00c183c5241c405d003d0b044c2d80707540108444c10303ca00b80340d41c0310340400101c0c80c000108000001108548c0000c0d0f0040a1007240c1c0d252a09026841450039005d506502541074880c4164007100f0500c44042840a5059540d024400d0027414050082da0101c14582c94100b0a8000a41200c2251920041200c0141881e0017040c070850b02d40d50341c0030700203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 401194136 1250 401192886 401192899
    0x403120c030204050906092511120c0d090b030103020402090316030302061801140601270303030b04110a08040b06150d02071406090d030f0f09110a090905030306100e 73
    0x4000d015890350140003655801c8488410584440302040074011003652485440182d41114410820f13036089080d04040650400018901d210954242007000e011f40e1400c2494001460701543e940502202004a1035414981d404034180101c0c060107020501009004030303400908410380f96810411410451265585854034945904d0b0094a614041d070f00454501c014085044001034180120440c6001e0301e20a10350503500c1400445062002602c8400004020f500100804a000012501960007902c011803a100c150060008890a21000c980b0120b0140400302036254841038007504241c011514803490b842d41400602200d0401900c55810346000405141c00103082d000307060030034040c5011001c03070070481a140e81c807041c084a07c18031b180c002e42d6280d404680a43c1c01030491000024002850091910b00c0b402103604420301078402c005e0303000400ba86450101010809080246c2081c41a504c0c580e540e079a1306e0001a040310301c901c0061100c194841c0c85003141400d01d0b500103098 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 401195386 1250 401194136 401194151
    0x1e03120203070c20010806040b0a12030206092a0f0301020c2505010e01020a0303051e04061e1503110607060203010b030a05090307030f0c02180702010f0b27040312 72
    0xa411603204040480710180c82c070b25404440001c3c01c11040c500c3c0010b0319074586c80e9031030008003c014810f41104030343c4039920141c04a1400c01c40f100c1250242c1c80b0b50010805070601d50042480e201d2001c1010700081090089408801c0c40c50139945c07102c44054403503002014000c03000074060302a52211003120720800300000400700c1301100a01d1401581081005299141d2004444002c03017102a28090303401180d454002034441c2d0b10160340014100c800d03c080c140d140f400c142e24910203a40a40da000d45401d011502c0140200441d8072070414030030700300a17071a44d451880809480707505c4003400280d4111140d00c4c00f034136268112501c1e00e6004104554035a1180640300854100703a844002c074034508000101e80050000c125940140c141c0c4440d1744080c9201022981d060414004a0b01b200e9282c50309146c41038040800c900030101e40d0004151002ca2480340411940b49402441c0320f528056002165800407150b0030405241c0e0f400c0204060b500d900b400c7da1501001c00c00d010f036061030440c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 401196636 1250 401195386 401195401
    0x15120f06030204150605030613020c010c080f07020601060806100306080708150a0c0e060d0906110c010e12030f1308070809010e06071203050a0b12010501050a121e03120203 76
    0x1034410789100b00c0d02005040d1102c0c4000d9041c0b02c5a0140303501040742000031034110300d400d0b50404c034401140c0b02c01520300346501da00182503d00e03a001d00350200303014406005120842920b4164403c10300d01c010202c0d9803422400801d4400b010b0000303400b0750000d14203030000901c070341c01110141c02d5120403260001d0f036a10440340d480c0640c0c3c214103c40c507c0600891212119401000e0b50070581d80d65461520b0346007010811158490b0319090f941d10340e65501400041c40c14050080c40c146100348064440318102e4440b400e552026070315a0f51754200c4110345500c0501e4105580d001201003411b040b281d1384130042c120000c1702c61880a0012180480e11504101503840103050440d000c1c0d86500201d40340c8014060030b0300851000401a603030000b071846000d403007a80841ea12000c0c0d0100400d01894a001241040c1008580c540142c0d440f9801800035062080a517002405a9540802e0761090758a4408144e91481d210b49009084980102c0c2814498100c1000a18181004650700d041044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 401197886 1250 401196636 401196641
    0xa2703020411030108120906160c140a0608180a21030f02030408270d14150601080103060b0f0a06110d0e1e04060f12141615120f 57
    0x441244518102816000a04103030000c2d00e0481700700c0030051020f144171403d905900e402810105410a50030f00c0515403101d000c240c0015042c3c0120200c06002d0305180c080780320185c0c40c040140c000c0e500500200502c41e807001060fa4040403011540c03c0d540555412a030500302c20074006001c18118924001c2c0030003041841c0501a05a92010041d03a688954a001680012100a0185201885661400e402940489441e29a110020307003150208200050747e4104a10080d01c0a0000501040207000b0400010781540d1803e04040002d1074484002040407005000092035075456110f4803410340c5500d8041d60a000700140651040398454000074605000502d0300a403a224003a100c0c110700d03025001680c99070340081c01c29000b821101e11a040701c0c5900f60311054210750343c0d10000911106d00d541840240040391302154800b1054100545800910716410840c0e41002501c90700c00007001d00200104e44149040c0200b01502c0a01500e40030b1450404079611824013440c060710f020b40d903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 401199136 1250 401197886 401197889
    0x8090609181909080901050a0915020a261b03070204090f0209060a030b0c0f04030f0c06021219080601050c0706020f0f0f0303010902032208090a0506070c09020a27 72
    0x2800c2d0300216240301c600740320640d580700c00e02074240d02e0108145261944a00c3c0148500c6216081c100329490356000d905c074001260f1400c4600603005030702c41e10104881d4a1084240d104400d00003d803c0003a004800140d204031604481108841102581c1607034040c029200d02d6900200200542c0556080041503c200c1000892152440c0d0780060070078904986228280c1b0740180002929942d440c1207155030750310646040c0400001840000002912040201c80c00c0b807081c1c02403c0ca140c039095010740703410142c0b0303900240044240700314401c13040306e0030150316668413a18007400c0944800e00143c8091181d44100711003806100c0010440701d40011715001b1000d1401c0032600b10101d00c3d803a10b600d80700c0c50348458006030010401044002c034203070003654100741015000070319074180380010075001c240c1a008641809000c101c2c4800d0340b41c1401c0050007048191842868046a6580c40107100501d000d41081181e0200380140010b01c66006209240104011105182c0c5004000603a02c20035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 401200386 1250 401199136 401199151
    0xb1b150403030b0a0608041208090106080a0c08070b0708070f061d010e21092b05160506090913031b05030403050c0402120106050705120a08090c090705070809060918 73
    0x4030001424520500d1450307c52a00301d19040c0b000701e410302c4d017162541e00c003400c03c3c440d5640b1074002007124841845213802281c0b0500f110385500d45400e51850404589600c4401c100401340410000708110303a0884260700e501c0694204001510b2038030000400401040181600c1121181d0605100542c0002180c49000d02203d0304c0003007400354140d00d450704110119404100340321003081d504141c18030140d255035210b000b40c81e00d40d03000051004441418429106a8446031028154032000200b081c00340c801961401d24103039580e00407a09442010f0940b1210951241c40c0205040c4202801d07000342004040d2282c4203001c41c1816507480c2c000d0300003900c050240380c240500600c1c0c00c0c400c5620340d00c070948c410315080c0c0c41e10505607819001070005071414012003029103d00800d5a00808010f6400d0311503100714104149131a24048850305c02134016078aa10503c0061038120003591140ca600800d029510400140032840742d0085105c283d800030004500c0d403140d4414000c209104100c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 401201636 1250 401200386 401200399
    0xa1e0c0e0901050f0f270f07050304030903120c060c0309030909091e030e03030703170703050c030604020f1909031712040809061204110114040b1b150403030b 70
    0x4808041120320a0300f072003542d503c40031400d082c030b1960074072801020014100904040190f5000084180090625514003407001c42030001c208640a034008659009506842d0050640ca030030b5802401c2070385a40005045048003000c550b03407607841903080d03460084d4003840c2400b80e5a24544040c000c0c003684041103000c10301c4030070046040bc01074130494908640000e04c074018210f032900b100c254000c00350403c0c1d0800040e80451042070300c041004262040c4070303513595000401c10244843c10303a0009400d4000301820328050041e51400d01c07003541c0d00201c1c2200c0c01aa20341a00d000a86103100d0111001000e1000d0322203081001e40000994003100c2c081c00312207540c44408180840c151140d0b08008406d1280ca40105000c40c0c2042c0141404880180080b480c1c51020b1041d0f0080440850b8204e41041e5008010980380d43d00c41c010181003100603c91600345424410f621070503014403101000240ea007004c102001240400c80c500190215044600f42800c19080040240c45240d175075a001d0b91 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 401202886 1250 401201636 401201657
    0xd0b15030604110f01050d02040e0a0506010c0201080412020a05100608070807061704060b0603090c0102010b03010e0a0b0a0603120306092a030b040e0f060a0b010e180a1e0c 76
    0x100811014460b56100d001030b164400b0303060800400c003229281c4103040180074016200c00315068401030001d46400d441120681c0750072070005040d10300c014445410400e591600500503600901d4181c0c02507406201c0700c4500920760422881e2141c11880500948600c078103800d032824503640b141054446440130361780401d45030b56210340c2d2030000340709a0f0001000a0109075280c4441c0c20b96a401604c215000f150704403406000a44c01d400c2a00d2912040d0440c5003105229030302403140050004064009108000e40d5030300c1592100c0500030064000000c5070000348949469a004002941d8045c1c0320010040d041d45005000300441e0040c200040d280c155050301550014016809014400a8441503042e8804c81100070f400c0d0f198129802a403501c14080621000340300410100071440018040c915098a11805944c0c090100d203052190042042c2d115844801824502a02908407a551501d40c220910001c12043d428001445a8410a203090340c005811044810b10b0540d40c84900f003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 401204136 1250 401202886 401202889
    0xd09170f22030209072a03030b030d080c090909010f050702150601030638040b12180312070c06050114130605011d010c0602030a050402030d26150d0b15 67
    0x101c1034000030b0b500480c04400190b05a100310740e9040403056440d5083c091400c24252050b80014100c8201d001c640c641000450b2030a08203c2140c0d80c45561408034041c0c1003000d404100b40c8034507000540100414400107658110941210b00020000d5408004615001c48001d407145520304051100c1000350001c10403544c46406800c040d00c55640204010455600d290108140c00345a1004404a840b50013141c010602e00903100915100402e03950300c062034548820301d500010400344012032a0340101d00124000402e45546044404103440281c039403440c240d941c01000080100200e04142c00071491440b43c1404040c00c031030588140c0c0b808101c0d80210803c0d22000d004080c001180c4000340e542040034140380d50642501810100040710700c40d16003001f640d100700c07081e06516440b641403100718101000600d9000407245012230a916841c0d5000d814038134011000818081d0a00101d040300c40741c4612601d0800001300401d420126500e0000c2c0c0109049a0f0814900d0b00c01c060542d65 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 401205386 1250 401204136 401204197
    0x212030309030d09150518070504110f09150a02010c030b030303040f020f122d061005040b0604120f03110f251a0c0c150d09170f 57
    0x2a88044065070510034050440307002480c402a0690301c4001da00605d08000c04603200d080e02450710f00d0b804400041380c03000e90b68901030b159032269004514080301c040074030801405446d150583c40301d0866403044180001901142441c01011140100155000c405501580138030041225900e084c051003410000b05526408100d40c060325600c0400c00000040c070301590318070300d408401032040b00154400901e1301d103000c0b841c0454000b580c54a01d051810315400a01c501410360050000307210526203c6000b01903d00399208a40c000c4e6101c000d14203442d0703202c40c10786000d03003006040e0707030302c49032003414800da180d500040281c01245514401d80a07030400882c1c0c140380710040e00001e00640800454086400041790b030800940c40c2600c0010170b8141040c400c80114010060310203413503d41400e0041e0900c2d0b0024220b9100c0d20b58061400080140481502c0b110700070580b001070b0005d4541000034003080c507486003044c840c8001a0315624101d100300138002d048400e20703030340382420040c2207007043c0e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 401206636 1250 401205386 401205391
    0xc16060e060414121204060206040b06060a120b0105091815031605010507020307051504033f030e061f0b07170d1e0218030106051c060b130902120303 66
    0x422060881e0080f6103003413811400c551001070303e080722640c0c0c091000f802d00d960801e80105005801c4241840240f1429102981d0801402c44245240045200010307050b000c0c12603203140c440d0389405485545170b0041c0180d82a40300081c06010480c013140c80344590b08141121408030040010015800038200042d0310130007000c4200d021105182060300569590704501c3c812649807081c903101107201e446130b1400e00101e8002d410040c1d110740c00c61510790041c001c0315940700403d10340d000000f0518a806d08404807900c5010401c41c0c07440c151440304801401740b801d50340c1c095215080600030b8000003818803415910900c00f0902c2c0b16901c0340800010b03407050319006820042c20b8004030b00c079100114020482e08298540000d5450500310061161114202c0180d07003466012a00500c940d40240a042d03140c18110020000c2c1d0f0304090009031103c1c1c1020110303000c0495041060204215980440144a8000d02684054000014040250203d91800c070b01460101c407000695486c000113490 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 401207886 1250 401206636 401206649
    0x9090d020606010c11040903020c09090307050c1216061806020c0f04152c1302090a0c020c04020304080c1c09050913060e0a0b160c08030a020c16060e0604 68
    0x7540c2c2d21a1001103e4442142d5030070307541c05003002c801843e159210300c6583c0c1c82911a0700030309804104030703040140a001c000d0070400c45030410042c080018001207480d000301d5030125002c0d91508480300c1c843e03150111902910207501e00c52a0f010401e5034002c41d04030104903513200d03081c0704541c407000f01702d231150727552507030540c10604211007003c10345032a4010102150142e0b00b940c01c140e5803104141851154035030171548a001401400780c1e290094001a42e1008030b011072403d48108550202d4031000c3c00500001d1260369402102c4076052003800401c14a0707100a101359200d040c5030804002c25408a4140c050078401d2107003810780381011612115842c80300d5100d04d02c03103920300003d000f0703109001000c0d19003038200e0440c5000081c1c018400c12142c810340348001d2405000c81e181c00c13480360002408a000a6042031046402607a01201c0d201220764042100364403912a0600340d4040d02680e00b010b40c050207400c10421a9132064486582210780303541c2d07a03006103410f20060140e80e10841c001c55 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 401209136 1250 401207886 401207893
    0x1092735030c07060b130b012003070303090c152d09090207030306120b06040c0207140f19290a050a21020d0c1115010608130203120909090d02 63
    0x1500d04090801410f400c9005090105070400340c0c000080944150080c002c01507962210203180382c1d64015400750f660075045d2654410880601045590780c0620f01005042580ba0100d035410000c0c07504200d4000c00d9002c80d8151184d80101000c1c10802190600260404103c102c0c612000c0d2101c1140305420440e0310350340d00c983d00300200c00000e5400a0000d80505480704c0001403800018408a226140100750320310076414000200300544100f50420001c65104900a100c079045440840f1900b00d01112407030107008102010410483d81c4800c081f5440541c0200094500f1340030041e009a0600c040103d124212502c50900b001d005209844000401c03e02c80d0116444c0904440c0410004119250290320600082c2c0c205990000c0da906841d2515075010740c10442d0030000c041c40da1140328016240d41c2c1100000501105014400c4000700070202001c0b501519001c80307220041c94010342030701e460392140c40501c21039600074034000e8042d420200c000b0f0101c0c880825008102855075000c0e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 401210386 1250 401209136 401209141
    0x71106030402010c171c0203071205151c0203030711010f210903110a05070f05060306090c07020a0902130f0e0412030f0e010f050402030115030b0109273503 69
    0x80300000900417803085040c0b1401c014108480880b06642510003004110150b581d2074401c200800c101510b150340017800e8240020f2090b09940c0344e61048a4143c103486031921810000440e02038001288806901801300040740d00a120340c200e5050300303000342070321680501298104125044d40b0781ca820051100200701010b82101e550f074100200c914000d241800c00c200400f06003e04150109100300c03502d40c0700c070380104140c1c80220510002000201e17902800e518110000c240b407500c000f00903d003d8074000804008558403c1c03d020043c00c2006000c54031403501001c40c05018601d4000d101054152080000d03807110007031006481180d0103600040f8107051100d05030040d141200c0d0800300203803101d55941104500f407096010322180301e507000c10541001d00505084842007000310368070050741001400424020201581104d1005000203440c9a40811800c1c0c0d1a50100151240404442d4800f0600002040701400da40c0064902c0704000040501502c41800030096240380316005e100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 401211636 1250 401210386 401210393
    0xa061703091c0b090c0909070f030213020717040905011a0a0f0201061d100e0907030b1b07060902040c0e0307031704090603051c1404260105070203071106030402010c 73
    0x900401010003500b407800c0104190f5601400407401c072001140d650021106035241c2c42c0c94510940c10801d002c0142c156a41410005414664540000b83c00b64520300c1d1000c03141e00195040304e41c03040e0840680e01c0780725082030400440e0f83c4a40f080c003002600741130000c0303424000720740301245910345d120415242240001080c1ca03c070785050821010342d541c0c0c1c00b0010703003142e4615484210800c0391002c01c0c60f40c07816007610710383c9030303025040301130f02c44086820450306400014442c1e059940015200081d41d5885d840c5101c412824001001c100034081401000c000054200b003101c681300310b9050203100b406036403c4840728040145075034107034440c203800c0003c229011801003c1d980400e40c460720300b40d2079104150954015a00840f0076510101404403182110440d284542c4018a0420500c00f0080c04120341c07401103020b00c03aa19a8001406001d552561105010040b0000c00174002443c009070042d4894001c0c80054442d2207895419082e01e182c803c0403a403003103905842e0079900c00720710784 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 401212886 1250 401211636 401211649
    0x10219031503140c090114060f0705190c06020607020d0516021813050d020304030f030e01051c061d0103050a080912191406160e0409020a08060a06170309 68
    0x2241001c1030440d07820040040360200d003a0000d001c0140e0300404942611000b0f00c10107071416804804420303200045070b8150ba4801040b00c5520f40c20103403030307500c50295082c11810000c40881e1003001144080703a20040020f80d050b030204403519134007502c48d582d44103038050381c458a00e58a000c3c001401007058880a0042d1025003025600107801481e51070300d070105d000c0901c24207a55400e090341c4456540d07003c10130100800f08070380840740701660905145944d04813005c292003e00a0900a140459100c5a40702d8025600c62035101e44980d103081501c198888000c1a8601950b6006c10001484100d03000100045d203041b00c0c0e01c00001c041100c2c0c207848080d00303508540b0f48558451015171319a041c007a030802075100740040910020100e40e81a103401c402040050307200e0b000d42e0300100c042214105898001c03900051042c1480315403c3c2070300002400410f0001c5000354008010b68000c2042d140010782c1a00c644140401004925201c0801c1d40300d03204124241c600a500421004884d0305002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 401214136 1250 401212886 401212901
    0x5011e0806011206050306040f06060f120f02042c0c01020f190809061b07051e0f030f030d050a05010807050d06020703091d040302010b0906030d110304090507020f0c0301021903 78
    0x100018100e17261340001c1d0401c207003601d098030000400445d0f041400642c2c4100c0c001440c4501c005d001c142e03d4011500032a04104201402e00340d09894000150f48964000c02c40e0101c0608216004050481d0310a509011154500c0c180b2321421201252a50000442d00c01c100c1004005244580f1607034204800b00e41100c0c0101c4102e84140f040d43c829456200c007500521080302080004004600790162030410507030300c0180714900e01105c020315010720000344400d1035800c2d24482207882d5401c011a1402a0f003030b4003061140b100041d002409141940513900a420054081c0f141e81d907644107455480117240101584100445107113000161260f0003401e036644a402c1040340565602040901c101404150a1a00140c90b08000070140c0c20300ca0858096011a0386d500030f41002030220750746001c0a130030001401074840200f002d4600400c1a9402040c0319501885103250000780203448014001d550074440c420011040c0071403406001382d80400c88900482d03203180c0583e8508a010780401c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 401215386 1250 401214136 401214167
    0x10f110d0e121902061e150f12010905120f040b160611030a05063001020c0a050706020d1e05160b010902180613050402030402130608060105011e080601 67
    0x150b90740400300284980c050911040d2201600e00c40c40960703c00a400c1c0000180982c1040c020800c107031034108404019a50005100094001d08284490104040d04e10403800c69902030907803a00342c41034060540000300314034402c009480141600042446c5a80960200040b016100313000034452480c001d000340c846240f011b102c910100c8800c1c2c03036490448030000c156030710100000081003144000c1d402466004942aa40d20b51a03072040940c00210701d801c03160b0b2941000480d108030030012001d40550704040c0da00310580d03101c4101442c049a40e07001c9441420054003ca0088003400c900a08100910304440f0811440100c08010700301d40aa01070283c235070800d00030061180200b260000764901030070b8840c60040e610f100e07040515400c106070f01d00a607c01c10f000c000034154010f4110707071407040780c81c16180541c507901c451001a55007210347c0021241d072480e020002400703000000c1c030395040325004c2e02e4046020b03620391100100c412540380510f02140e02c80020a84a5100387c0b064480182c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 401216636 1250 401215386 401215393
    0x70b0f121003141501080f1e07030b0109020a0311030705030708060a0312020105071e0c020405250e04110a0c030e13110d0e1518120304050a05010f110d0e 68
    0x11255103900f200031641c1d01d014055449084c0ca140200d000d02442409800d01d0310003845d02c150b040380320640d1805900c02c0b00b00c17040a40b070100051030308104252006075038004181440b40d0386807004d24000b03420400305840024181a65110040d0300d540c101c0c0d0007290a035591501d1503581c00b600b610100805009a5004001000000045040338241d02c4020210384d0011902d0300341060000d02c07441c0081c05c00d00145000007030080c08030f50040d0040340700603410f907804113190b600c0d902c840310403500300d0002c0405501c1c02c2980c09003055005051400400c0704a03402c014861a072002c50314075008051442001c145c00d1803c0d04003081c0911032190500c0001400501c01c2071440f5406000d581c89110030200b0f00d076003c01c0c0c1e44032018281c040c0c0c01040c8015001000840801091411000d4019001d1040021001c5040708030100074007a00c1d5514032501c8c5c619a070303400c151078020341d11000184180d80c81d500e8514801d45000e018020903102c42104400c05003010503204004c0c0c010400c500510f00d1610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 401217886 1250 401216636 401216639
    0x406020313210f0e031e070801060305030a14030f010308280c021305221103030a0f080a060303050a030f021e1c0c020d0c0f0b01090509070b0f1210 65
    0x10b401401c6201c801240101c400c01e2095956006421510300c06014003d00c010281c485007913880010b003100000c03082c5000110500342140c400c0e814682c1d00e03045a070070b9509103580070050000000040c01d064203282e40f603104c140c1c91480c6102ea40e003c2901c0000c00710800f600104041106840034020510300c0300f407588803245450424800c681003065070320000c2120805648250316140940d40b04140c00d81105110b00c1c50010051504c851382e100d00020300c00006e805100920044041d00e108424001c2c00f1680d076850b05031030190084a100c0d86400000706010300040c00600c880c0902c4040b40c0d815181c0c142401c64541095002d03040035201d048909a0074040050454010403484000c1814411401e95030180c0c0b0308051281c0e101c00c0c1002803403034182007447c81044d40c006101e03540300c1d031180b8082e803014003249801ea8420b4000c150181145881d1000894074501c950701140c0212001800c644000340c0e01c5190041a0150000d0aa08200140440780390a11401480c69210001400c00390045 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 401219136 1250 401217886 401217893
    0x80f22060f0501031b080102030c0910020703051f0605040e0a17070510060806070c0c03030e0a0902030f2505030a050618040807030f1b020d03120c0e03060c04030b0406020313 77
    0x90ba401d82c42030390021420615030210b94034400c22500500b02c240002e514525002610310300a104041c1c100e80034003142c0311890a024828040700c009507038868140d911101d000802060a80000c44da50082540f0301000007425190502c109001a6940380c0541242da005880b440c003c4061441c03100120b181c10400000010820700c9114031084a0900000d1090b00707020103146405c100600c102c0034000c11100e80340201e0480240101241da041c5002d1045003d240045008020036a0143e41c1481c008000e01001ea545540c1c030034412505500e0700d410461002003001c4265410000102c04920300b0000300700c0c52040d6800c0103a10041c042c10303645003082d0101e280340010404031010340c0e4a0744041240380070181c1c007407a008114800744c0b501c601c0f41d6807281107a00c4a80050140248034840b0b03031109404041c00360014001d0b0020640040180c01540000503007012a2006000c1c807902600c00081c410025220990742501d80120114410350348503503d91000754030103000203401ca000000e005000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 401220386 1250 401219136 401219141
    0x7030c050a020d0f050405030d110d03090b040f080702121b0301060b0901080408040305030a090f08160905072a150e060c070305040302060310030b06030c0f010507021f020d080f22060f 81
    0x220300c27141e039a2428010340c10410341d04002041500c10100b6080020741070200d01803031440c036001074100c61501c5881d00076140c010b5092081040094002c00c0c2c014024117240400305444552087e803d120540300d60440080600303e401c24028100340200901089070740d94861080b8a0b03000d0304c81d0007668581074403a12098a544c0086021100140701d00c0c10174403180d12a1030ba280014521080100003445030385141c0080440715000b0900b90341d99450000d20202d206402c20355243d0001d40c03441901c41c1494902c07103802208808252240c0b0791071210f407940c1c022039104544229040c000030302a03588507405141881da00501080d02040307000d1101002503910000190700420b1041a01545180345203052840400010b000c544641c0244e00c0c00380c000e4817003101002e10310200f441e24503543e4060340700049100380850070905001e01c101c0c4c050301c016500021031034041c100c40d803a088400d5988501d01d2400c44000c54030308400038490040359664210031406002072900ca4280030a00b01d4203106017104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 401221636 1250 401220386 401220403
    0x80a05030301080709020406020d0c0f02090a0b120a050d080403020f03030c180402090a030222020f07021c08090d080409150303030c02011404020603071709030307030c050a020d0f05040503 83
    0x400390400070040001c03003410007400c4000c1046a100f58100b51500c94081d441e030341c0f4a02000d0902009401003000c000c030301d1031200c8001d6401440e040507130034040c1d00c1c100207201f200c0e42a070140c40e4009160b0440c0c2800140480c03407980c002e0007889234402110007140d41590160048007944564000c6014000c803d1003e1446188440c008648a04240041400e000382d000c4110740201d10412070b03030140c1d440e0318040006a0340c0544001c2c1c4005400e00e00c407122942e840c03506080c02880840e81242d00d80c0c27000c0c01461040c1c0200d40f00300c008403c2c100c008007200c45c81c0703500400000040144070703070900340750012441c4140500062410aa500c414450179120041c00e58161030381ea0300310901c00c2580501c00c40802491a10080002902400102c881d0f804060700c00f070701c035107000700010b560b8612840ea0b003403a6003d69903116126007080141c1365520f400c00e443c0c810110f41000e00c02841d4600c00c2003039942d0440341c1e500030049400301d803409455a07101e0340368003010444108000b00303064600300310380035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 401222886 1250 401221636 401221643
    0x70510170403020a120503070f0311090a0e04060b06040b07120201200309011b0903030507020d1211100c0806040e070b310b0a05030901091703090c0d0b0109090c080a 73
    0x203809200c44c0b61030b001e1605c04500c080e0521609009000d121548240d0340f201620340d60a0001e004100c0b620189030600a0a59080e8000004100030405013040d140e40c9000c0d51141005100004019040080c140901d0003120520141440450301041903d0031032140ca0002c0d00002a08400015501102c040c06000c2d02100b14800000c1c060030748400d22030300c24201560440365000c001e281000030034054440c80040c040000c0401c2200c199500c008415403890f5004a00140f00300c6001e07806401c0300e0841d90b5000e01c1c0e014521a05080c007900740120404030000d59204811990380c4c00c100030007881c0c001020174484c030030360401056980ca000d00030508250008050f44902413640703982007880d1030b10b0510b001c041071484820059143d80e0000d950601c202814031541b60780c1c0300d2322480e006000d8048040c101568188180c16100071b01c1c80150f001307107480810303240840198401e000808404c400001d241c00760080040201600583c00a40214881c0c602da4040581c0c0d072200c103113450150311054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 401224136 1250 401222886 401222893
    0x301030803070f090e0c092101230408090409330c020a020a030201200d09090b010305540105130803160e04020714011d07051017040302 60
    0xb030b400107022008158640380ca0700c000c905142c1640b042a801030960704440c07501140624095840c0c0440030500504200f608062420044d402c07400b070100320b00280100d4040c00418412904014030301445035411811103442d18035000c00f0b00c00100b1449400303845601407100c8011141d200e921080380380803000e040450b11128038440c1030080b00c00424000d029540002c1c0703c00016110b0310a0842181d80900303003071000140100700300b4001040c108200d43d482c000e032580f180e24190400c410070107407510810200240d074001c00040d021a030082e20654075165409100c0510f00c910950401c0c030060b003100a90316400408074401c101088100010508072031203e08440801d42c003481000e502501c002c032141c20f01c1240d900c0ba07071513501c0007400300802c426402c0b00c1510000d0040301c4e4050240c0b00034004561301d800314244442d0b104458001380009500340074100884454a40b0034210035002c1c0005014203628100400460a01a01c5590f00740300312518140f01c0849051401071055000c0e4018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 401225386 1250 401224136 401224141
    0x603051507120b011d1f050706110f09041d01111209060c1c06050604030b240604050d060f0203010b0304030e010203070b070804050a0b1509090d0f1808030301030803 73
    0x6440c2c4407050907820242407030000180781d01e0313030302074800e41c00140641c840c41004003007039001c07a03182c0d104240700307040322221110842c40040c0c1c08001003039414040e4008020320311a034014062244521040d4034050102800660707030915003640012140d022003542c01403c01c502000e202d081d40d80d10901030344d0303c10001c2102c004018a10802c0c0d03901a030508003030300c158034001054502c680a82561a415a03884030391551000013694010409480d0041c15903843d00d540c0c1c90031214602e02100c0c0d0951f04c0107410300135000c00c2c01c1e51241c6001c0540060455003000d0400040c00500190b0a1042d9459603c0d0900783c01c6503409440294040d20446440b00e40e00e2810781800f41082c4410400e942c1194010080e090219800c050f074103801052501c0c00c2017040d2164105035142070040d05014004101701000c0c050072100c81c3d44007e800410544041c84190354580309951552010f000600200e440320646c3c10b00288111300710400010548000c1a400d502d506449142d034100741c004171920740c0300105 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 401226636 1250 401225386 401225401
    0x80a0903150b241b120d0207050114010302090c0a0203190207050a08210309010b041d0114010b0a05130306060b07110405060d020609060706140f0c0c070608070306030515 75
    0x1c43d250304215507003901c40d5070101c03060340540d140328568804d003410080103490403d140c018006040720075052a07400780c440e030640107404003c0d4408481224698030b401980e503140400e4811890407650000c0014940d55510320700514140c0c0010303000021400108800c03030510792000d107403400b040481d90003000d40e81c0c105002c0c001840c0d000d0300705840d9a403080920b071a0560041410550102c02d031141c1e40c0e180e0f00c0301144a0b0140c4130355440640e11506006643e0f000041100d041050041884002c1c41740103c80d1001d5091604203001d40c50390950200880f0b614140500000e0040c40207030180c0120b40c9650340c5682c000c4554541001c405c3c10070014004d814446441504010200e04840410041c20146c00042194041d2040240070b0400400e1440302030f56401d055601c1c99800410900541c900e0004032400d15030229005141e16000074003240a5441442c26240340e40003070b80082204505008081e03a6805000380744c0c0e01055243c83e000300010b0410320580030904140c1a004981d410640d2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 401227886 1250 401226636 401226649
    0x120d09060e150709181e290d0809100207050a12050106050618090402031e010b030708060c0a081b0d020a0909020f040b0912060f19020a0c080a0903150b 67
    0x3025402013140c00320061141c0e04030506101d15042e40b003000001da54454050041025289107460400ca03071800081e0901214102c401d01110000d01d03d034005100b64580070030000c040c6903480504940003d0042548500348a102d00720154a14011070341c0075a07585002411005841e0411a0129035152161007041024000e01d405000201c13a21804c01c9090350440041607540700d4107510601104011405544040c01404007c00421056584600c22064002c1c040c02e01d80b82060b01a2003901c0340056404400703d507041c091283c0c00031320b80c68001814400c49480101402018446540240140f01815148000d2000400e10100980c492850f01005054442c055000801460042116800a82251040f507040e40d20340d43c100c2e51640d2002000c01d4240e0740000e503400007440342c0000c0c400c045000c8181c0034480d20042119044013020000c001003a0b000d030400e00c0700030a0110100c00c002480710405055880000c0c0390a5524a41d240c5500d426428142d00c1d03004100d9407145441d0450074500d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 401229136 1250 401227886 401227891
    0x20c030f040314010b0d030f122007141b060a030608061e1e010b0c01021303060509190209060d051507110d2109020105040f03120e040e120d09060e15 66
    0x403646c280d100d2000d81c90192032041140161b10410443e0038892645040390f5010306c0000b4205495100000301c0480c2c401541e0340052000d680103c04141c9500510b60000303108248450781c808020a0000568107010003604a0103500d801c0c1610380782e01003401c88003044403030700c9080351800c03040b011030000050401d20b4101800c4450b199080021003a46a0b00340002181100c1408030785580c1c41c00c141501074028000e00344c0805294074640000401d01c04242c02076400380038ac0c4016507290f40040740600300700d603106440003500b2518070000a201441d20a811245041c010702c181c428040c0f00050807a03002004543c588003080500300c04803100c4004000700100f03407003141020f44004410701204100207107807680260f002a141c9003031a0840e40b01c0c1003584c0c0142991107400c0c5d801a181c0c50705442240301c032000c0700005004260401c038146020b004800041c034191001c0c154014001c030040341d4a620801303031034075884e8450000c50009540c1d1701c10030340b820581102030142403002c1202c0d8261020301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 401230386 1250 401229136 401229139
    0xf060e04020f0f0a050d20090106020a021306050d0b0403020712020d020904050f0a080306011e0518060f04030b0a1b020601121a070309120203040810020c030f040314010b 75
    0x20401000016200d00c1411041918111a80c03455810904001a107031111604519007200b1b00b08107240410180e80410b0380c0b86498416904e00f40d5400d8001e2160001c03003449502c005a0140c6485009030030030307024415845c0390001000c1026034561002c90500817187d0011503c04a8030010002495418400603024040b12110030f1007580c0300d44c0025280e4440414040d2162100c08081010880200300c00340c4003400120a488511841c2d0502c40340c0ca410445065021a1041d00d1804640c0080d034145400c907030361501c89500745117404003090f040c01003440c403058101f041008440180102600900300452040440460511740708006800f680c000c0c1222203010104200d107802100c2e00420100d056a2060810306084051390401c44807500c4d9100310351102c01c41c44800c0c012044c3e415000340032014060b0303002e1940030f400c000040382d5034401c40c45400350390341105099405900c243c0d0024140c01601c00d00300c0b420945044c40741541c40e882503000705d0340c3d2084548240d102500070302503099149030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 401231636 1250 401230386 401230409
    0xc030f020601050a09110c190303061a070618060f09030e0f03030f0c15070309050c030f1c02010e0f011d0a020f040b060d0e1e03190c020303040b030a0f06 68
    0x24002c00328021118a0180703a150b241c80703550080446d04050151441d0b041880211026808210781394207986400680c00d500113070528001185010440700082e4489015241091411a03e521182e000f0040d10b0000e16a0000040e0000c02052107409a068285c446440000702c1c17200300d15010b440302c0901d01c02c280c040c608404140d03082d0ba4000c0b080d01c0520f41400c083c00d03501c12103070405a042041d40c0007400c903c8003400f014007000fa541035200300520f5100b8030407201062010070405958540c648a41440ea83c4a10345192000002c02101c50000038540008603021003141d541c24101480000c2c10306650f07540b800314580000000803000720200910303000e4138101c1c0d10394000c545070440007410b031781c0520b4554aa07982c113030f100c08044070b240c0c05a40100b0000c0042094066481d8801d54012841e85110301001c200f01220100c1150500700402030482c0d24440460000d41e03504180700e40680e4580001c0c04006843e544150044d44235102d00403001903040c087c4a800d2003215115000380c4400c0c1c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 401232886 1250 401231636 401231639
    0x10b0f06040e0c07060501090f0e0c031b0d080408250b0909060d0b07020105040b0a140114030a080c03040816360204031a0109050f04121e0c030f020601 67
    0x211550308a5003038451841814031a075942014101c0075100c3d601d402800d551600c0c000081e8420079901070021111401024456007145480007503860140d0400035a040d040103d01034001281044d100413290000390214440460356107442260780c0003030740407580c1034102d050210f003401a072429401000d4041c0c120105e00c50b040001c04404d5005a018030341c000c43d61500400d003a640e032500c00c800680c1d0310540c030181615110000a02030101690100d40f04690781002c6014142c440c0589180042807030340e49140313a8680300d21f1003102c0d4654040c1607014081c40541c0b40124030944020000514a00010b5943d189003927146407510481400350040342c03082036410b001e0f221042034480b10207421881d244100312003800e4400c8002c101d000e8001ca1070380c4000307170010030006601a03d0351880300c54071540360140c0e40c403807a44090350021140007507515000000240002c441070f410309071403c49071826040d0004810701c02c0c0b580f080c80c00902000301d21f54203c84e4080552010301c002c07850030a840a01050f5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 401234136 1250 401232886 401232889
    0x1150602030c070b03070311160c060e0609150706140403080604111b07090614010e0a1203080403030e150901053103110703030305061302070f080a1106010f08010b0f 73
    0x1500f990041c0e03401e92000001145685129070041202d0b03090030307406180d917050a07138013001480711640411035201600c0f40b800100c23207001d140d0ba9040b511029040910708a80c0070704114201c0fa210b101c1d149804410b0185c4004240e0601c02c0c455400003000102c8420704180c1405480b000d0f000304214444c9051140c2182c00070000780a0701e0b050300000c0e607001182182c8900b014241a440c0d040074800926240300012501d800d030880034611803081c0c9070351121003120024000020040d00a0050454041407a500020f1045846507401800380c500055240c4584854a05214070051800b24091049052103100a001e1241c10340004025109640d28251115014040c8185a00c80000360509070044003d050007529076944034039003541524003498aa01e0701030300800e01503070242d006440c0d00b02d445201d0181d91080700d443e40e4102c01c0140f0710203081c1e030310907625030300000d10a02000303601c0b000043c1900c01004a107010b81030a100355030106040900036403c40e1221001c1c60700c1441061503a061a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 401235386 1250 401234136 401234143
    0x90303070204050624040501182d03060e100b0103020c0c0f0d08040e04060b030f0a110d02030d0f0807090303080f15090412021203041104090201030b0301090501150602030c 76
    0x32180d0503203021901d0fa0b14030340020385070100c1d10403c1110803d100100d41070102018010815900700b40c80b01c801c4e584850104909120300360190301d40081038201e41c80d84280140348844005c0f240742c070b500c541c0d440e207c0d5200c0341640c0010000300c080303600c18443c241030701c01030b4058295070640038602107040c204200e244990b00c40c106640306004003105507520b0107607104d401c141c401c0150800700284c0e40b00c2e561a0801d0300c0400c2102c0c155212807929603500300d030385404602400c2d8804064010010707244151074046140660300e00040e0b00141107035080005131424043d0070300e04810382e103d035a490f02e10400c028100c03940007051a403c0003882042400080d400150103078000e1190f40010065581d1418440015400382c02c0b1341d9070100410080004000c5820403c00391401c442d420348495600c449020841d502058400500303800c1c940c1c4441e0000c1c10164800241540149400b00d91404145c1c003180c03c40d00c0104094456945450102c0c01010905105200806951000354540112160055203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 401236636 1250 401235386 401235397
    0x150302060c0c18040f0f2a0510030603033005010801021803010b060406081008011103011502061306020d0b0613050f061912090209010e011503060605190c170a14090303 74
    0xe041848494061041c07441d01c241040e0421411031090b0f00c116400c7e6042d10200c0e2090502c22002d030f80e82030060910030b0044204595054031144181c0c109080550301c03210f240e181082c44401140c0c1a46410116070042d5402080780e40001a500c03000b00c01190581112581d0440c001d07070500305940565221403048a04458052a0003040d03611220440403040c45c050340414159030a20001d84107a2420300b0085041300d52440c40001031210811090b80c68020455580d08020725110000c40413407682d40007405c644808c0c81d40040d0a01f40307000042c8054006402111162466110a11041c1485070a014024900719045030900d80d0701c0c01075440c1141c005143d0b1080015024002000007980d4020300c3c003880e4014a011059078640c810911a03850074410502d204054024943c2032501903c40d12041d68000d507210307450401c1d4240c91a005048908409041066405444001c0703200c2d110980d00064002c1500c41c1e94004e2807500070101c18000b1000500c41c0006c002071152540c00008440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 401237886 1250 401236636 401236643
    0x90c01031e0906182a060207031502130e090129040207080c0304091b0f02070e09030d020c0a050f030301060e0d08160c050301050112020105030109150302060c0c18040f 74
    0x1030038041610309074003c0e00785134115400700e52542040000304018840240350503034009100400480c82c022000000c04158032991005d41c010007000d001280c0c2030280180303040141c45002d40741c0289114203401c0c0360b0071a4031000b03040c64148148102d20200b270058164800e611740c03040b501c15a0300030402c81ca0300392002c4510b20851380003540c41e040000003410b4406d4281d604d4207032601c41e60784544e140068100d01c0313448410f103140c180d004891a03000c1c8044100382c0040b0b40c000c0043c44e0070402000d407001d001130001e051600c014010941e25500ca4001002e10240402c054a00b00080b807504600e40a00200e0b12041504240014080070381e00900b44520100200c940700710105d5a0704240c406840741c40303001140c0c0c03640884110240552011402c00300c0d441034000704016a44d544c4040481d12010000034006001000100310b4028142c00000000c5090a04002d240343e5a60001c0c125034841d1000e007590b500161070100d01854510100b00140ea02c000c03504100345426590074020380300454004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 401239136 1250 401237886 401237891
    0xf0b160201031b080601081e06190512071a030c0a0f180303210c02150405010b0a0e0f0708070e0103020c01110f0c070510080105090919030503090c01031e 68
    0x44156842034100800038920a425905481c0c43e40b03600801814044078501e0100d80c00c000070809600401005034089402501d414400d52211000c124400c0b021104108940c0c00f9000040341e036586102c40c0e0140600030000914020346400c0c0b40e80148100c0c0c1c00450308a02e810f2003044040c1842500700e81c82e0300c40901d8480c0074141039483c250ac0c40b51010460950034403001201104140e0443d01178221124804441c040280b2107001510681d0b440780114401a04429491490309000001c0c19400510a1001003a400206008100842956403006081040003c00d0241c0c0502e5450b071990025100e24004101c0c3c40d05005c040d0441c108583d0080c10164001007541c0104c2c02984825005e0309601a81c41e40c030a00311105100c190400740202d82036008a06c00090645040a40f10041c00f0590f100c224007a86008100980708500910742e940a0195080c000c100041c5803404084640c82515501d0701c9080180003a8609012040d9413414185040300d40070b100d0ba0f1006c0d54030105690108003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 401240386 1250 401239136 401239177
    0x80123070507210c1a04170f0904090f030f020c2d040c0e030f01090209180f150708160c0b0705091e0f0108010f0506070201050c060f060a0f0b 63
    0x303c0c1c1144500400f0f0304038807242c4081e04080d0b01411102d07036140600c0070709014100d2920070210303a02041e20020208a140c68400d290480041c02400500350007546903400d00c449400840c06403a143c1c04100e0300c02d45003501c44030400d8ac0140c0318009068203807006010303c1d0102c5010a0300110b0104e00200d055248140b83c80c201160303c1142d0441c0e0394054810301824081a0703001d0050580e03041043c0c400d018517064070300518014071404440c1e980040ca041140d8a80f04a8580884d4034114032609074096400ca9060311340c070801074240501622010f2501c0d52501030b40045c110348020305800c002c10540481c1c02d2250340c0c000aa40c43ca25042400c0c07540c9030701c0791001500e4901c110406140c108102d0380c2c02008050444034032401142d800e0360071403407a042c070000441d8800c50901552900d46240c00c000e11081c2406000707443c0091041c10000d280a88090340c4078a86042112040180302024003041000c0c14900b9521000f0300641135003805030390515280004602540000001041c01d8010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 401241636 1250 401240386 401240393
    0x5091e060c0301031b1e05040c030b09040f0f0b0411090a020307081501110f0a110d0503070f0c0b1210090c0210050408210f0108150402040b0d0516080123070507 71
    0x860b070009291b0480c603403840000e10b14440d4643c408a114440c81a85040d100c0085240240200102410003c09800d900c2d13031281d65108454010348015569600020000000101069111802580201505030f4003548c80810009011030003450b41c44000c1c0180306016400d904074946a0b0400c8443c40200c0c80c500403180101c2e00c11986c8405050503105140e0440055030300800c080c00014090381c1c08505110655081c41143e8101c2c80c40140140d10400c08280030a00364000034021a109080a5585a5582c2c094009580003504414055241c4800340190060b61b41750300e400a105403c814042c03007540c40c902075150b485103200201c055845a000a0420008500300c0e658061864600d4550008689502901c0c8004440072540c41540c0000400c1d110701c0096903e001c0b03400203001c00b405517215420b10015040500100780c100842c10f020b44c1c0090b0041c045101141600d04070b8100c1c07540341074509425151030341142078410790141c1c00075001c1c07014003004650000b0301d820559592809441d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 401242886 1250 401241636 401241683
    0x70308060312030a0e1506010c0219090603060e0105092b090b0a020610060809030d270302100f020405030a020f030f0a0b0103033b0a0905091e060c030103 68
    0x4581d00149400002000042c484641c482c000e0f0100c0d403411100558481c5038041b001200549690b402307d90b10020020040c58892a011020383c04004c036800340340c4d51014150141d410300c0c0c004541c4262100020a21001d0901c141d07070384949550300030040d20f40c0c0340904414052107107464113009580c001d03100c0805030041510b0401003801c141c0b05030366890a1034000303440381c4050702c0109840700e105070300289141c4a031440707038019207040780550f145c041c810702c9110082c00f42d01740c461166464501001e0328852020000d908940c06034001e00595500c003400c03402222580018000028410f000611080c0c400142d131100096060f11450300c0d04400100003454125103200040461040c002d06504004404044074100c1c0c2c42a01c4103c1d13444254800301100c140d50a184018401c2082020036200c200b0320211624281c0260400b500240c0b207c202400780c45080b50300140300ea02500152110140c940711080c00013903800d02906071810800c400980030f01c8180320141001e402c1c0710044241d242c121 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 401244136 1250 401242886 401242903
    0x1005040506041a161b021302250803070302090a180e060105100c02120307210e060a050307180f09140a09051c091d04030206060a1413090b0f0a150b0703080603 70
    0x41090705500e01702d6947c1d4001e544099100d03d91a0103030442001010580c6400000c01340d4808110340c02c0d9501d4220440080d0442d050355a07001c220807200141d803002700c05005004013207a11020440e0000398551502e0020182d2145000b05510301c3c0480e1078540c406070365540710b50304540800b00500c10030409483c50040c0900070341042000005014520b0060004082c0205030792540380b8402803000402c6001d00440c0c005d0700c0481c804100080c0f0440c8101c624a0100341c00d08002025a900e4512a030910007207a04801912580c410110004001d69079902e40e02024080b404e003c980a40c0c4c2d601501ea148441c825240c82a56144036080607000340e404070040c2c0082c0c51090440c0d0700d55400c140e060241035030300394098021000030445a062030fa00074001d94040c0c0e00846034000b45101403040034114441c0c0d800c161a80c4441101c006172002130002d010b9012205000e000b4140100f1100c2111a04041122068255141041660800d00554200c250141000300003640c400b000b0a040881a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 401245386 1250 401244136 401244139
    0x219051002030c041409010b030f0702070306021603090b2a010605060d020711010e0a06050703030207022106091c0e0303120a1a030102071509051005040506041a161b02 74
    0x10042010f40c101e000003410480c1c10694021988005000c00d211a068003800f40e0000c4140c2000041d022920301c00725148c0008861045500a1743c4c0c03510f41900301d80100e0218907444c040e141101c01807650010340203000c1c0003042c0c075003445c0c980c0407003030020491255001d05680c40900e18492007580000e505c44001000090141660f8001d65070348a002941b011000721414072001c41c0301b85041d4800d103203607444400d0190003824110b003000419541c81d0442c2c0002c50815800b0429580180c80d02c1101c00110b0040c10201e100880e40b03000c0c9141082001042080b46130f0008140003641c262010400c0d4150b1420700701040c02d54400e20120741544100059400000310304014850a04800e9101207040e100c1603108240480203030741098281e00c10158060245c0381d4101e150344110446600070703025103220303000320780c2c00320041840c503000c0c0c400441e07087d05d054200004000501c4400111540800d840000d069002d1402036042000d245030045071404200202000b03900480e000500c00c10003540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 401246636 1250 401245386 401245391
    0xf040b130c110a0f150213060e210d020601060c030903030f0905120d0f02030909010504020310080d03091112061603020d0608030705010c0507020d0807110d05011401060f02190510 79
    0x3d5044c03559800d0321000003203526000d0342a001c000c8003001e00c2540d41440c205294034500500d4283c0c125041240c043d07800768000c0c0b1408a1000350150500c3d00d4407041da006018140000c9103441c040d0400b20141d000505012541d8000d10029a10102400a69600d800e0010040b00b490504807509030998114035044401080c0ba58101500026070001c108c000d5946c1c0365541c2c40305001203849018034080f043e00090300710018000d524054025691085106000c0740c1580ea0302d400c0217241035280400d0b00d011a6640c8131110902c032020880c542c070500c041c3c480001c40c01520310040d03524400100203820f0180240d91002d042442901100e40c1d0b04510341e410302c8681d46075403003203851f81c2c001c03442101d142d0310b44507080c810380b4050810b4600268005141c0f1001d0740070303a01d803d0003540c0a858121015400c500223400142d445060f03c041c0c16015500014144101c00c100a20420341a0848c07030900440055100100e680042c010803001e805007002c0001d50340720b28042c1e01d4144080a5012400d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 401247886 1250 401246636 401246653
    0x6110304030302070b0105060a0c1e020301110409050a0b0d02101e0201060501090504050405070b030405150a020406080a050103110613050d14061b1813110301050f040b130c11 77
    0x40d0702d500a04815030103000c181d51580d9071384040255501c1881c040d0804204510455004640d24002903945818009008945070714680c0c00030742100d161216030f4141000110701030007c8205407081580c020713a02d901c10440c1d03550040c0011000c200c13101000344580050031140049074424090030b041c6004d01010000403000000029020b08840e00410380002e8211100080301e1621b40035043c00341342c00801500090742090b40c4102c8e240e000a000b0360b1a441407110307111394001044004ca1251380c6186005072200d050102c0100005400341002d0010f6082600501c0492031904c60f5031410042215050f513500c50804e540c2081400c00d5010030360204010400006206c003030358044450122800c1511000e03038a0440505051032604022407080205000c00100310351140c500029100004010b140c404400060a5040d40c6213458240a25140840100224106040710070701010040fa401d1000716143c001007034038084032850500d25140c9581d4a0f40c0140d008900c0c00c4220901c0c20152120031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 401249136 1250 401247886 401247893
    0xb011b1212023c0415090501020d091e0308030405070e22080a031116060b04110d18121d010f0512150303042607050d0b0406110304 58
    0x200c80344052101066030780d40001e00c198503600c2151108440d0584105032880031080481200d14000316000d1040d0401202c05101034456010700700901c0310340040c040c4a00d0f8500c0041524086500090540d40319120a02055410854040c251120403845451854240c01c800300400340e10b90016110307150006c10311062180205a10050316802c0c00d14040d07a848031480410320707415660324507550031150000c290003e6881c2004045800481c82c0204003591354010401c010760112402141601c286003d01041105c035000d01608240204c5040041081e190202419407049100700d900c403030342d00d02c000180e809000b0504001c4940000402c105440c4c8400050101782d00c402d00002c9034900345002d2200c80d07104446110340004280d58032810f110303042080d18810700e00034024080078504d210141c002c1e51804c20140c00148000c0b490301001008401c2c104554049c8650004800e81090b58140516201d1490b000003d82d480314902201b65070710705068008108004400003d40c50020910060 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 401250386 1250 401249136 401249153
    0x406021f1b0207030b060f18060f043e09010c050708030c03041d10030b0a14131502030601050715060305100219020601060f03020a020c061308070b0408100b011b 71
    0x1d41e07115a081720900d840781802c010b83c010010000c103922420440002c4150003c0345030554001ea4081d020b0600b0400302800070701660000c0c0700c100000c1c03800c4003a01c04882c02400520281c03400c4c202d4a440d03412074019242e1260310070003181605100c2d07204c1c03804082107410040c1a000700020810750b03440f0700304c440205440e07910a1180c0300341800c2e00203040e5841802e41c07a20a0081182c00141070501c1e140d55030746141e410008043c0c50320541c0d00c0198010070340310034a03603070302c55109803580091850f00c62503d440103010761280709166038814810040c083e600201150720840c0c1000d0200c5010702c0f0319800d403000e80340c0c0ea04014958003840300c0d0300d140c1e42d259401401040f840401100b59145003841d0407603558009115080002d400c03440060074860007680105042c040501c1074520101d0b00c4408110b02d81c0c040301c0d491400c0a4058000c0003005800d00c03025000c0c0080e5402c4a141516055102da070300c40ca140c0300480042d03034941c09070b60140c4c0507a81e01071a1841c88034000e442c6903102d0414428 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 401251636 1250 401250386 401250389
    0x1060306060f05040602030d091103060a36082803050a1b0e04050a1503140609060103080702060f0c061003150c0903080d061205070504110406021f1b0207 68
    0x1082c90076064181c494021000e81d020380e03403103a0045003800c039002800f00103040030501c00c0d912030050701c82078069030f1024003060f031107082400d04c0451143e0400c0083e01000c1d140512214003100c41c1039801683cac12080d000c40d641d00350440d0626403a080da10048040c4003107110a041242c0c5030288001d010580c040e00940d1044400c128200710403c11078008520b80c0560400c4400041d03402065030407a403400b80d01040c1c200803010400900c06a544401400c2226250000e68803100554a01c0403850020400e1030b07031128064018064035455a500d00c1e500340140d640080c0700348030102e141d2584500034400d079080b040322801150f10a00703000707103c0540c0c144c0900099071945c410440d1200d901c07070390780034a00705000c41d90b9406541c1441c50722910b1007500301c000e1016501e512a14002404510165900d00c250b02880191034154036040810040320b85030024845101d90901c8200669034021500381c0d0f003188040d200d000b11400b1501e5840040c41e041c9108401c201c0d1074980c0040c043e500099860 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 401252886 1250 401251636 401251649
    0xa1103040e091c02060a050705040801090605060411040b161b1214010b03031803010f09150b040605090402060c010b0603010b1e03010b0f0f07081605190c060c0203120301060306 78
    0x890700305110f918000c02154003141000540d1001c40881e100d1070a5a005030780c04138061400b6403d154948000600b03561300c000007600d04be501e5900340405803030140310b88000c00340d04441d0145443d1400c0e080c29414003800450b01d41251138121100c0900003001c454905a010b800c0d100c0724800c3d2103601501001d075040ca01620136510700c0b980e0303600b1304105225401101d58000d00440c01c002c00040c01e0300b4498a103021003501552100020060000c080c01040141441008054050800c500ca000200e44a145405e403203241091030411003034072004031068010350195a441d030748203d403180d07290140400e004443c0d0814800400000c0600d0004090b200e00f50313900c60402d048003904002c21405000070300a161841004028a4060f10b41c084028003031004020001420481c080c1c48031610754212001c2804029402041401002020312008410002c035050b0110703010101d8440711180100b9009250603c062101300c00255a0f04204141000058151190ba0ae6071507100060240c00c1d14411030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 401254136 1250 401252886 401252893
    0x111209010b0102150610020709020307050c19030909050c070b0106021c14030c1b0709060501090605070309051905040f0b030106081207081608070308390a1103040e09 73
    0x4040c0703503202003022248400060711448603500c42400b000002140403940da4250b200e4042e001500e4207a0f40055807107040305444003511001000402400e00e0300b03402c403080408203c29200310000740c00045902c207885100400094640d1056000c00e05031080d400068188945071740000341955000842026268128401c00c54070034600c0002d481c4034600e40d10002c0f6440307043c40002c844e042e0500242403504003402002103001500180d40e0f0070207585401c0001c450f61944c00038056035030000c143c400204800d1404510302045510b0050a41060b4007070301e8400c0c00400c42250840308000031000140100610411402c000c40050030020844030794030078004c0d400e105000030030705404615110743c0c1c80055134143c6004101d40e50014641e00900ca542d0704e038840201ca88010940c030101824015100351540d080e14140030003c0103440c61429694545280d102100d036642c8038041c00440031041070018410303200c0d01020419102941c0c0b442e0540c41e9403102240004050300803000d1540140000d0095 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 401255386 1250 401254136 401254151
    0x3090503120a180f020405040305040e01061707090513090201210e19120c0215040b130f0510080a0b06070b0109050a020313020f0d020a08010606110a05060106080a11120901 76
    0x10703007030034490f00c0000d0108000940c0b00d40243c2015000103078003034800d10f003c9191035159140b01c501c80d1000c0c0c0000c80000c0c894080c0140b000c40c8010b502d0781001d171038285801003e182100141040c1c01c0b01c000c2d0340c0e10399206c1245c2011a4058140107090b001c090741d40502050f44260482c0c008c01c14801c0007200c1c0d104004003100b0241d601042c2484158000f0341c41210800301b150240d5544c0d00d03008003242c000000440d40c2a06000c2c400240010304a480030140c0d80d40b442012025076806203800041e80e01401540401550f59642407158980c82181020070341d035510000300f04018010484e010360800000a40e007400c0050068400d0305845807000c00b000991941602001203000071500c0b407115031080c450f498054541490f00d1018540018a40321090f0150341c08103005a21603400040b25030b45804003440400e40240d8091010201d00c030017020004030603280c850b5528010300c5039a05100c0c442001c11a590307400c0c4c1011840e050110030507551010500c402c4c54490300cac2100d07080c0c03480d403178200d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 401256636 1250 401255386 401255411
    0x1e0a030f060b0301380403080711040605060d0c090e0c0a120903050315041d0304080c09040203070e190c02070303080105041503020913020d060c14121603090503120a 73
    0x80e681a100c5e1003412207203524451052841c006080d000d41160122a01858106404042d000300702440c4500c0707046454410f60b01d08214041d65541145100301d04005040c401a00d401d8192030145a281c9808a503101d101d0509a030300d580260041080140260100611000406c2c002c2c0b980e092156141031881e000031a10030300303d8618000c01000680200007103078007062050303029003034032030010800100b0501201c42e0703108403c8000d40182c15031b00007040801c0341907c10b100c4400c1810040d603d81c000761400c0d0340060b481c0c03c0140100f0039a00711800c04910031011060210b008400ca50500300540a031484010b5901c40340ca03c4201d00003000c030000402c82c5c2c2014022000b026403051a5550001c0c195802c221688100800e055902e031051154240984d460013a10b01c030043c050701d0000303124603000704010043d001800e10340b0480003040103a00c80583c0032213007140c0e22040500360844400140181100075004400c0064554440450030b6900404800038041c021041044208021400c2a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 401257886 1250 401256636 401256659
    0x11061329042a08061315020714010b0a3c0b0c06180a0f050111040902030402090f06030d11030702040903080f090c0a051e0901080d080601020c0d081e0a030f06 70
    0x24605030758100c240443c4618140170081c4010605c200081050384922803e15012a0400031040d47c1e03e030140c420441d0592401e200342c000c204410b407403c02d801808d040c41e440c03150f2040381c0381e1860f035108030000002a46c1c0403012411020f1012126040300c5d940c6280c1c0c5480c81c0c0140c0402d160a00980010071500b0380d51036500945200d90074003802c900c01d0103444260003d000140700760361654841501c0340124620f80d00500103010030240040c3c480c1028014010040002030045000a50303010a00c60b55550005107504620b440307140100040301b0a54943d4218082d04c03070001d400500b02481c0d0002c0540000c256031280400c00280049907a40043e1b2503518022440003641051041c0014016400c201200340c0503034002265010240c803d00d804900c0c050000d80c06500300d5081203c1001d00786601c50710b401c4e0010002d200410f00b0025000c0054110040075400400105000540700200000d49480d1480201c6059240c0d450700215000540038100e82000791121914003400070520003d00c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 401258992 1106 401257886 401257889
    0x50a1808100b040c0e060d0609020a050304140703030f110319030e06070503060f01050a0e130e0c181f090e070611061329042a 56
    0x81c601e07400c5a00c0810041d02c990700b0414000c4100d503210f0a2224900d000b12061035880c2250315130350340284219031101603082d00110712201500d4200340503601c80c50058226009030824104110344600d910300000300844e1501960a4100788035840143c400303190b003011a464000a807403030000641c0b114481d0340c0000c1d1540248a0b195505103e6107030440c500d81051030840c105007001410f81145c890086041140c00308600109501c101060703000c0e010080d02c0340c0c81142041582c100034101c0f051802001d48691020301040d0708008026070207940e00310300300c0701158884104003a14101c10807100c804881500d4008141c1040307a02c15561850101c400070040b2a242c01c1029040003e00507004540350065410010042005511600d40c20b51108444e11026041e0146a8400744040f901c20f030000480302c104410003100c02c962100d1104002012145056007011221440050307 = true := by decide +kernel

theorem cover : BRFrame.Cov 401079136 401258992 := by
  have h0 := BRFrame.cov_init 401079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 401079136 ≤ n) (h2 : n < 401258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
