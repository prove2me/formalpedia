-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2865
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:58:40.212992+00:00
-- url     : https://prove2.me/submissions/11feee8c-9225-43dd-874e-d79cb235c58a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 515107913 ≤ n < 515287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 515109163 1250 515107913 515107987
    0xc0c0d1a0f0c0d0506030f070801020406030c090b09150c0a060f0b030607080103030e03010f050f0105010e060c060a020f160b06010806040e370602180901030b040209070909020d02 79
    0x1800301950f0441c0500300c0c0100d030340d031150f00210b81040207829800c003c50082400100b21180f0540080044071280e550070010070b46030300e81c121910742c0b09000d1404041010450794103503203003810b644080209401c800b03a03e400c007600091858240f500c042210b0709501e40228101d6003406110352260104143c010388124070b4030f0301c4018401c8805010007410702140441061198800350b0205010007150700040020742440000c80301c46034000d21a160000d800061102014141a41a24400c0408400078030080e2034070321201d4040c2d0040646180c0079002400300310301a400d90b01010541c103000302180c480c00e0030150001800c00c40300404081c004c0c1d08000c1210f21200b0000ba4054000d221002d00d011102050613807608448182001070308108881080f6405102c004c2e801086000c010750401280304410a0030b1240c859070034030024200914880c0010054200b00c03005036800f01c00d40c640b0000a03038542040ca0100d030400404010b00715400709081c82d140c2d200d00d400700102980c07110040c070103001c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 515110413 1250 515109163 515109181
    0x1606030e03090103111903090b010801021315050f0a0f08060609132c06190b060d09020a0f06090302040513050a1b0e0a090614060102070501050c0c0d1a0f 68
    0x110382c461181c1010384d0380d00e5161680c490300e0140c42d84407203040d040c03501d01c02e00c60710010701030301c03103104240d0b4a041a03000029601c0310500c00c84166290403030850341e9291414540340404c1c4c6108101d44141f107c20040041c01210541c0207007240e18081d11031003140da1500c0ba00410f102d80080c03100c4c0c01600200700d6005540c0c1e070140c0b910050012400c000c81c190b4480802c40d6040101ca4541200c0114101415002007502050f074520030b007408a412500359980041c84419101e08010007034000200300049402000310750440f9500718000b0344001100380c4c3e1040201d0001100350301010016142060034021481e06005894009000f01c01c80c004502c00307500c6840c0c41e1461880010440111000752080320100a291031000b44441c05004040b841c0c4003180320060300c15403400b10341c0030349490b903001000c0703003000c00440c001d400680c000c11420b81480015a83d83d404000c00744454070903070311041d48135039a14100c81002d92040f0300344038010300550341da03450f002009407144000034462410070602c84 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 515111663 1250 515110413 515110417
    0xa02032403250e070305090f01091109070c050f030903010c08010302090c13031406060a081c1107050901080a0b0c040e040204050408091305010e0610080c0d1104081606030e03 77
    0xb0015026401e1034490214821041295920070f400710607010f800c02403541e415603c6940b1410307160007502c000840d060550350803544d103004020460180510f0303507200c13410150384007a4044024244480c00c080540c55241c03030318401e1580f14880340c0c8000f480c07080f10b040a0080d0340d0781a005062410752035040d5400510308000003400202c001030b02254640c040d800b8401980000c40d0001c000e0400b28000c0c1c0f20a41c2c540078201c80c07140c0604161900041d5210740041c44407200c7ca100100e241c0b000210300000c40e640b12400f200b010391485141c00108556541c0e1007500d000302618001880800120329000d009102c009002403000c40e4144004c0006032140c0c0011548176504407000180340e42c1c2c501e0041d66501440f8019900a403001c80900b018907802c0c0d2105042c1e407400b11a001c1103607184000c12031301101180110000075011b1010400a98034800030785440b90000001044a00d24035040121a400076404440d4030307841070020f144002c200981700c80c05802c0514052008040c0076100030b40d01c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 515112913 1250 515111663 515111683
    0x2070e0a05070e1e040b060a0f0e0f12070f0e0f130302030706060e0613061a03090c2206141f0309150b030601172109090a02032403 58
    0x2254552001404081c4100d0480040200061503003603083d850211502c07581e04113844084c0218544624a00949045410b994840855907507401451107076842c201c1e40300d50710052450304408441e281604580c1c4140043c5000580b600003001c1ca54600004d2600e50545944248510ba441e201407000724084810040ea0003411041542c2c085035251904030703c0d40c070800b00042c00d124036220012440b40c1c00d10b501d042c0901801c68a042500c0404608502254040e01c1846140c1c80007030312049942d0240c4015552084514003074942125641002c140405160542618511016800d2034483d203507610072800a00080341d004980c1d00307010404503048401c224500340c3c0340c004255007030001034841c0d0400d0b0f103002ea000d07500881c1601ca54540c000a8880046c415200b8007030f0304000301d81401c405401c030a65405000060000c0001480b054501083d00f0170003004c05e400030000140750342c031a0700d06070740214148800143c0d689030194851441c01e90101b2a802d030f12901c0c139445111039500040f04119 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 515114163 1250 515112913 515112931
    0xc0201200d0e0f1020030412120e06030601030f020403150507080703050105030607141c0204060f02031e070305120f06120f070b0c190606080d080c1215121b0102070e 73
    0x2c00c505c0d00d2411000444030500078141300000b000b0844c01034010000322510702c9030507405400d800844040c0c0300000e0700d00c0b1403230b04584e003840011710b00d41c8a83c22900c80902091801450961251244c1e401012030a4500c0803a545a6050001c91a40480c1c1268800c0e03081c58208002d50504c400251039003030203801d54040002d0741018501c008203044c2118181000702e0140c5100c1d038035203021403020390810720425011501f6040a0b042050002c42100d0b8030070030840c0307604800704851003d16100c1d00000019010400c05012420b001c00312500b18901401d0f01552100d841d00c1c1031700130410500022582030803da00310401e61103900d90001894415181c2d900c80842e101d8100d161520710b0605021313102801000103604000600030190f0115043d550040b0aa0b40441d41000301500c9007441074800c00c0070300c0c00400c0181c200e800702d40fa1454110708490000000910300f80005042e00c0d0030b000064034160410384446101c13002c3e186243c40e40c0341e000c1c000781001a1030303c00304222a41008040c3c1d46 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 515115413 1250 515114163 515114177
    0x100e0408090d06020c0a0507030b070912080c01140118050106030c081501030e1f051609180207020402030a0c110d12050405030d02030108030a0801050618010c0201200d0e0f10 77
    0x2c00c1100c55010b0f02e10145c90403085031280031641c01c04680d5600144070075124a0428004107aa10784161284001e03200b005500d01000e0426076184003c0da40203040060b4255612800e1a01e00500310b2540c4e070090a8071900d09555161000001003201e0061b1b10800a04d0726154015075480c2e000016541c1c44440388103801c0072a1404c10050303000d880641030007001d50107504010b14506851111996400c580d84604000c155034008103a0030480612070402c000c6030822100300801544401d014180b407100c1e40c00541012982e5010030141d0700305a508500f002c1d01c072503266803015400f408020810358440003c140389174605030301802401c4540208440c80c4d07210800101482400c0003201d181d800e440104540c0c80d139451320042c0e00c0750070a00c052000110140300026040c54171405450411500c1002c0e5000503011900641d94022100012418000d10500c6040c2005500314003060301c00e4bd0102034072441040b17802c024214403403140b8151040e0700b014040042c94039011403041d10110907040a41c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 515116663 1250 515115413 515115439
    0xc050f0d1704240f0b0f090c0a11160305060609011a0708040803120603060106050c2805120c0c12122203050706111c030c110a050105100e040809 64
    0x30b821418907800d030f580000809480714020207116444200501204a010040c40c546041000348513500c00c014030f82d0006d50000803501c0c00c4c2d00d540003400c1440c25410001c0750540c404c680d05051040380041c4000154003000c0800510005101d40ca0740001d003100c2640c010360400514001d020b107000000020350401013450340801c0131140845016048042c1100c0d11203081c03c029000000003200c0e01402401450000103d06021300c0c240c3e40c0031b584200150a41c40207080c07001c1200002c040585032150b5413a204400403c10a101d6900c80003440140ca40d070b51500c0d10350061030041c840c02164010007020b1380e26062204c01080d0040300d005800c450303559030001070f01000785041030040500d1000041080000402c81c000030328100f2920240c07a6503502034a100099511801aa1741502d400346419078080c00a5120380d00080e1140d0150400324802610014000c2c5408490001203440f80e544100340b003100801c103101003005003c801514001450596904d100310b00800c0f40a500030b200c0030b50703d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 515117913 1250 515116663 515116673
    0x6150d0905060109150f061e140a030f06050607080405090405010b1206041505040503070b18030403141b0a0b0304020d0210122403080d060e01060c050f0d1704 70
    0x5140c1898014089070029610390f0002c03801030106000c0583c3c0003401c1c81d00007890100380d011020413640b6a4442817a00c64540c501c603601040310a100000708040c6214415008141c0405032000c0c1406550005030410f80c01e07051000c0307074100c1e080b85210b541c051040000280140c0f080380c00b964020354900324a034960f071802c50701420908c041e155100c4000c00c1a07625a0b0342c00540c40e0310960041c0108a500480c0d04507035022108141d9014000f500200003050120b0448001c9035004a1310402240101381222401429500305420444004000351079061100c5000c00442c503418941c842689400314903000080d100d1003aa12903c400941c010001400359943c42c0d901d440307056006000c007450000b1340000101032400a2140142d40b52030259807550504030120a000f400c060180205049810b5440740800e81d08a9107210003010385443c4045030380b0312003894060013459591204002c00040d890100d06060b40a0312600d1190301c02901280302681c8808000302489254981c041c4540b10350030a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 515119163 1250 515117913 515117921
    0xa2114030d18051606050306040b0a0e0c09190b0a27060e10170606070f080414030f06070905090402061b0706031d150c040e28020306150d 61
    0x7162881403074001920101490202e116611501c650155143c8251038101610201054000d040c000741040c0300045007410315502000c540c010041c02903103d140d4030301d40e20081e14003c4030000705081010500058509104e44140360a04009070180096800d18500100d02d0140c8801c0c0000c00c404000481c1d03820700349a440559070f00380070422240054039a007002c1d2250601c0104203001c0c1154441c140301c0684a46065642c031402e039642140c164441c13008003c0382e07400080d820782e42e203140c0607040700000c0e40150060000700004608000f003250204101410700000000c1c0c5c240d00d0300300c0810000c0d07145e40201074205a4108903800075007600c95001048903800b8560100044000442c4c1805880c40005070718401c403999641c060000d01d0b992910010003045c0900c203240b041d07224921522080e44001211544041140c0c2c40e42c2c145aaa0f0702c441c4c5403401c06982c00000703410300807041c0d0203c0c2e404024000c000c4010080c10f40c07450614801050411040310704284900350041030340c6094982d0f90308 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 515120413 1250 515119163 515119177
    0xc1e2b06020901090f030305030714570c010206090606370905160c0b04030c0c060e090c030112030f0210060b0d0c030506010c11040b040203090a020a211403 69
    0x1c81030300c9590b00c1f4507020340b003039205903140c00101d48080803200d41c03402c0010444a08a4518002c00e2411802240b241c00c403100b92003607580c8031520311009440008a00802111402040220400740e480160b07040d801c1080c80f420281c1107401810800103031f518001002d50304000b050700d002e01c0945103100d441107520905060203c02c44040784140c1080b00000000200744c61345010700300419290450f01070784522241010201040719001c020001c60031a41c5801da1103806070a01400b14289541d42c0c000004060b007002d008144000324000d414100b44c42c40070390210b01188254515410302260b50001140148000e00308010800003143d403910070300c6100b00c407103044c0c0c0040c454140c40f58000f04998100c0411005583d00e4103504080701c42c40790060500408040e1101c8a07500d0003a01d81700b04040015000a0b00325890b8411042281c540344003c5101d080048090071000d406481000f80f00302c0c0e00d40c444a803000f100b99118981c40038030744c0e0541c00c0c290b0000e80543c0642c2e400b101076040d805a11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 515121663 1250 515120413 515120429
    0x504021801030506032d07030c0b03010312090f052e030c0e030a030503071d030604060f05090c0a05010509010306050d0813090e0715020c1e2b0602090109 68
    0x85000d081044040301660821102628203105583c0d8840c141a590503010580130840581d56021400c3d80d01202a16a0720b1404801503900d001e480351907000f010183c1c0d511840360b0190010042046c009442e100d60100c400307614001c402186040a01d40702d42c66a40078030340c03041e0200e90f080c000f0340c58a4460080401e072003000700d41d180f0880410160003006c03107603c001c000c1604100403a40f20b140c0840e00c6200075074591202800d5450715001280c21100042800d51040d018071a2450303070b40e404000d65407180b881000041101d00d210510348003500e4001d8000009a031000182100039501c00742c081040e40c40031b00e442d540310409000100d0180c42103910158100301442c101c1e07030a0003100b4000700316a060284200a010741d40e4400c844c00c03100018244846500704400c2800f180c40fa00d40350745a142074a03c1106c107204180d07800101c880745012014812790120421241d03003818111507a46881d0b111075001020340c1b10144103032605607260030000301801e60028051210ba0701528003100506014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 515122913 1250 515121663 515121667
    0x1315150b160c1707050d020603040b190501030b060f030c0f011d09101a03040f1e0b0a06050a1509030209090f06130201120e03070f060605192102150c0304050402 71
    0x35401c800308460b80281440d529028106000c82c5d103040c01001511919409002e5078655901c9881d1154807c0c0094481e11202d0019408000041264000c10f40a9800f40050440c207040002c10000d0b641d0300198800d0007034001400e103032100d035180141c0c046141c5007801c22800c241421048421000f205c030032000c4e40140e111041c0400c0c80c410304100820b4481c0111649108654004550f12030301048030020320700c3c81d41d008040009800c91411100f050001000c4008040c141d9807000301544007251190440e070707a201801c0200b8584512040d004080e05680311076150f0680360018902022800003900800707102c001f02d14504000c201c0e0088041c64201910305a05101c01c1041c42c03e03140b80e8050f07001500c185500743c2894142d1107100c100101c5200118a030038807039918002c2050702500140d501c50350720b910014003900d600244d12111090515040009800c2c9500a2001050010495581c016821121006844620b1591644040c81c404c060316061001c58441c076600c1580c100310303001400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 515124163 1250 515122913 515122919
    0x150a080d080f0705070b011202040f0204030b07080604020f04090e030c0106060203270f0f01030e01110408072103051b072402010509031801171315150b160c 69
    0x10040595008070b003866004601a26060302c01c131100d000e0107002130301c1c0c0d6203048010010a00c00d80c8400720858406000400d4030542e200030f0350101e822642c4250303030200000d0100004070ba0300004155000ca030403901181410031030f01001803103010394003034940e01590340d201100c05440d007041a20303601d03501c0c003000780036007500c0d0072009450341c0004074162038554510101340303403512107940c01d80d81c4010054001c01c1001d1900003000249803940301078a050555030f520302440220280948940031004012480e0385038602134a8604d00b20142c0d102080e006410a81884541c040c802c001805c2c0b90036240058451184810155402829000007031142c801d40c0c1000442d800c0b1596030581011340000451484441c90760700f46c2c280d40e01100e0003c07080d0410000341c86000e0486c5070200c209141850b086690f1204110b06107054281556468070300c05529680c002000801b12103032009561110040c807080041d0740d08188502c1545c000c4140d10100403c031807040c45082c501c0308100b1900051003443c1559 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 515125413 1250 515124163 515124167
    0x4060302090a061412071815020c030a020904030f110712030905060a08040314040503120c010b1807121e060e1b04031509051e071d150a080d 62
    0x8000c5071064000c14050b9000a40c90f4003c03803031039600307040e050901d41c80c0c101025041d54440100405a4040c031259001000546001341d280d8009440c008420681c2d801b950036010345000c0c0c0d0402c0d00d42c480d0b0300c0101010300607154440c04a030000e506051500c42100ca400d4140c0324a8450146010f00c1d2241680c0042d4030501341d44480e5002c1d000c0e0300d8102c6aa07482e074046c003215208940c8600b000c1040390340843c00180c418a16804611448865a4206510f500010742401900500854910404904102010300a110340a0640c40480303a50300c081414508203100c20000070304107020300601d60381c107000f03001d01074105020418406031404180b0001c40241c8004003814014850718903d03000000d009002c00350300401e07134054400340103801c113442e40c0d0b110303008088450070b292400c503150981d000000e0070070401c545007680389980c40c0c00c210320201c6505103080070039032004002806600d0703101c1c141c441030a0069080102088485924001d490214040b5105907000c05100d2141e0320314464125 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 515126663 1250 515125413 515125417
    0x9040c060806040e1b060910050d060b0a1706060d110a080109180215090a170d1b0609020409080d0606080f0610050705070e010308030604140c16020f030304060302 72
    0x100c450700d982500b40c0340c0b2010722048a01480214100354040320540001509040320707060040d500801143c5444542000719101c8441041014003190000c03d81020340c82c007a00844c4090300364031020f40c6c1804650040100004400b17800e100001d0b40c583c0c0030410380d03141e200856a45085541c0c0c00d110f411240f01702c0b03e01c81d9001114160008490320004100c000c0a8000c41a440d4445801c02c222000d40b82c0807c680c1341200409e41c01640306c00c000d40c0d00c0d6500d400000e10002e10a02e00c44900807000e05807040d00b4841c1e0b03032101200700000c4000345c400b084801c0380c041001070340001c40081d2040301032002c18004c00002e0030103405030030f010441c3e004407030b410f4102c0001e440c096035a4500d140c44011440c0015102a103a031a8017404031000070418600c41d001806445020f10200c8034034955424603045891002c0e042507401c05c00000c10041e040c02e0a01980d8000310307011800304201d1510240842c0b40d40241882d04040c08a003401c02010755940c140c200107095002070607251750380d40c0c4c0d0b24041c00079 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 515127913 1250 515126663 515126669
    0x1504020a0c020f031c110a0b0907050102070819080d0b0915010320070803041a01030501020712020d1e030f14040507080d05031504020c0d0c1b030c05040e0c09040c 72
    0x15103c80001803040341400300e0024404103040c206205c52000310340c030550307944460300702c0741c26144140084000881c2d25090380b9805400000c1c050100c1604100c00242040203030740114880c3d5204901e140c4034034904d58400403000c2d8000c41e0158813082551074490150440c0140d040c1d0281d209001d00160b4901c11002045906003620101711204540740d207030161913140b100d04072959070103100040205e60380100441d80039105842c0c100d07040c0b0100b4801ca0046001380c1090f1603c7e940415048104007141c49404800a00c6000070019114102c200030405104044190700d500a048505140c45010360005444445400800d00190403070030070141d14158222010703a8030b84204040042e9689010489840c4079145546040c51a44c410340300803001c13540801d205070020350810112802c2c000c2401440b8103a05255a01d96807040d0314200b949160810b000c9000c03800d500f203e010400926440526011240140e03000700e5041d080a81840c1840b0030600c41c950801904c10801040003c041c61403029 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 515129163 1250 515127913 515127919
    0x4140f0901060302030a06110c0a031e08190c020c1806040606030b010503071b14031909080a060e030706061d090c010504050f0a090c020714040b030601030b1504020a0c02 75
    0x255484442036420b850320382c80003a400d034001080325008110380b0b4100034020001a60b103140b40c00645040c5915090503e07606900082101450790342590480601c15410029413030070301070500f48003c1c3d825100910120380c441307a075640d82904038068028040c00340103000040c80d10400781c80c940c1013001c500c9000c95403248154074240380491414001d00c55044841c01c1030b9110381c195580c1080a480c030004107901000741e80d0750341d0318070b00c00604007480c1010100d10314805980c69140f01400c940c015078807174072040c0a0000d070030410301c080d41001400d40c440039005840414a420715404603811441070003006002c0c1404c29902151601401c402c51907036030040303c0d40d10001d0b941c5010320f544540700c02c8402400110100401c109518020704440808134009004440030365641d6403c2003280e030307402030801c05a00710250811500e180c00101c0050103000b138030103000d2403c081c0c00080c1c84000c1408000c20045d2a5008103503000042102128001c10291046544a225182c00f604180300354401b00c0c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 515130413 1250 515129163 515129191
    0x10902031212010302120c040903030b01030c0f05160816030e01020f161401030f0c031d150a0c090b0a03050a06050414040201050901050c03070605091203010609061d0414 75
    0x401d55901801ca95248000700201c810741e074219401c200c00e540707003a00103034901e114406280e0626a1140f0805100074030a440c0083e030800c03410000350907a100a401e02c0f00b800155004080d20390f4016040b00c0c0101c5000e1b0a860f002107072490045803a000304510b20200000009104081540090044031003232426001ca40314940145442c0740d4035118481410a4800c00700c1e42000412034a217a04c20452005040c08960740d100751400c4011228102080d10000b40c85080c1c216940c89010320070401c440080004d0700d050b6800b20003005007403002800100c83c117a0340300004540c2c24400c25904002e49201d1480300d507241c0c0b650700004c0181c40306559080320545803220004c3c00c4c0c607052140c10040140d100d102042580c5540040d1650341102c10402e050141c200044002c0d60018402402000e00ca1040080d0b01c2c180011198604110f41d0070710341c0c143d82c0c00c0005000c00b075007000404003190741030310300100c4150712800c0041880c1c2d00c9035031480d049070405070f500015150200b0381d544140704202c5188 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 515131663 1250 515130413 515130433
    0x30f110304081c032f091201090c0509010801020c0a0809010306030f03081009020703020a03080613090f0b0718090e0c0406030501021905040f0b0702041d0303071404060813140f01090203 82
    0x841401402090f2200c5600d03111980b402c2007483c480a0881951b00810000396030300e4951a490940780079460071034400c1c210340c40c1404186003815101d405416a00b001710b00b445010006680d840712554070103001e900700403400130340c1b41e803203504440e014590003c0d01c10a08410f502c6c0140c0b803040140e99580c4002140f00b00880c6450862080e82c070f0243e050381c014a00740020380c806a403d980701420040d00016200c2501c541c1c003040c0d0007811091441401c00f55486c9a039414031075480078001c1c05801c10410503c0c2100700115468210009841000b0800a80e5022006030303249400300b00c0303c566802c036040c2031000007881700c10340c040c12007400c001d0350002c9400a410070895440c401c50061054804041c1c03414441200c42c1406010214400b5000080035400e82c07405a0b03840c8041803280c06254400401c002000c0d40c04072103444907200c1350f2130140c1882d0910502420b10b042c010450285802e01c59a1071050041003443c030120a0803400980c0c110884014009020b4400d0620070703402842108120 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 515132913 1250 515131663 515131691
    0x204030b1806100302010c030e09090d020705061303020907030e01050403050d0b01080108060a0c0c0c08060103120507020d0b090c120c010923040b130c0822030f110304081c03 77
    0x100d00c540043e91050191a046a00540319482c01140030f80c03c00ca0b4103401a051510342d2042c060040550700024482030440b807d0092600007560004c502400c8144085c0081c800c50640c0e5106880d41140c10394150340d5004800c400411440e85410840c1d07003080240000d154019005105001454071306100c040001300055880160030b1140000350740c0180d0009004840f55448019201207500e803111161585488003070084100350060388540e001600100b041100d0340140c42c07954551070070007502b004040d0700080c0d1521170b1084054115601d0000041030030700c0500c4038041d80c1000803c801c0f0030b500c0b640e00e9251b9455007038000c00d0208035800004510201420703a0311001060003e0b101404503448014040501680c002c6541c02400e03d03d400050300043e4003c1a815182c0c6d07075550403a0703140010141c500c4e69060306141000b41c000b0940c1d50f010a922400c1c1045040307460421844030740c1541c90491451207945c1c0709081c0c4d4040c65946181202d00060106881380743c5580c1030002400d10030720 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 515134163 1250 515132913 515132923
    0x11a0f0a08010504050f062107030c08010606030e160504021818010305060a0b030c04090f021003200705061b0c0304090e0607020f15060112020c0a0611030c040b1c0204030b18 77
    0x15a50710844591040840070003603801e406142c48c034803003a00c81807540c0382d803a1140d40019412010169440308018130019a040c0f0441401800d120000c1c203a08000c0e203001214041140a2680125000070f070707c807041038000c01307010744108002d44038480d10800f105480c500704100780030440d190b00840010840c0568140102560780c1c200401504c21101c5a42c00c001c010101e4000845642800030955005651144034000c0c2405131501c01059010701040e031f00c80d10600140e95070ba00c0050602c1080045000000c419600100120350040e89503400300c2940518002c0c585507030901d210024020544c034215400600c00010803004507003803500d038003030300341e03101c2070342850f1346c81154800131043c07180e603898208407a044070047c10301b03220a2128141840590340402405501ca030701417048c200800985210b0406030005040704203045003042c4042c4e100e03620451107a401c200c1030116458a1840d911224485020104001156155920329211500c204c0440e42e114034800c1a8000d20f03071a40c00814 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 515135413 1250 515134163 515134171
    0xa030e041a0d1a040309090c02070b0304031b080c070504050c042111030738030a0b060c0d0801051804080901200703030908011d06011a0f0a08010504050f 68
    0x560003418035840070302030003207010441030f200c2d200807841c00441094095070301070165000781e9070303902c030503060800c4a02a40c007040c0c4040210340c0326070000c04c8205002000d407030300150f00d89000c2201c0c0710071407a0f01d000354800c010b010304240300025419144000000e403400440358150740901181c4c0d01c3c4c02c2000d1450041c1d10800581040c1e0880c4518203103000341000340c01c03a1260b00b003180c2070160440440e01d4801142c11010b2011a0081584c0120140c034644180030781c0001d40e40c1c11540040d000c504818000902800102500d85512071616551720082c5c8044209800403103004454140005040a6080c420300c2d0040c91805500202c071020744285512581e00300e100503107440f006000441c0c080d0fa00c2008550211104003042400107420300960307000b94026590000078600300501213003161011484844194500b60290b6060781001c100541110344045664645004559807059940301d1880810709030880010b404590301d1704008510305070741055804102569405c01c3e602d1484134151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 515136663 1250 515135413 515135441
    0x110111010b1002100621020108060d06050405010209011209050c1011010e161d04151b0e040b03030705060c07141e070e040302190c1208091903350406020a030e04 71
    0x80035006c0594001d0000c1500190003401402200a450b11000101d500964040b10240d40000790200190381c020409061806c5090042000795001d688403641c50164082403801642c58826840100740111a980100d00500c8000d1000c0c6158134960383d00c0310070b0310a000c1036212515001080344160910f58681110b15966040c0403030704d99464100140038400109008a61142c80f1442c660802120fa848401e0a503200d1400070043c0d00108004e036400c151a00d03000342c2c4140903500101e03800080c3d041c0c02c2850440030307950f50140303402d00842100c0004000c508900c6601110300340c181409282020030240f58054816190301c905e01c9003200c080944025005900030184254680300034980e42d40100e11034003c4185480c0d840803500d8441e00302c000d06844640d804030b800c00d054100704080c0000100c444803050805c078116a00c0b90070030362140c0c520300c034452119160325026601010181c0203100e07c0384411794840f0b41d2904000e58462001703004600040351880142c1d070300c0c1001d00407215085030711 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 515137913 1250 515136663 515136719
    0x3060315011802091306091401140d060e0c04090f03020706020109120e030f0708010207060e0309010203070305180d0c0801231612050a15060804110111010b10021006 73
    0x490510b001940100c45030603802100240d94950040b92440b4138401013082c014041070403682a810b004d60000140d01402d410342c55140000d40960341c41d0700414440d9481180021506a002d0000b450070324404031894100d441c2000000030b00c00c0c00034002c82203d119908860b0b1003500c5a00c202e082e1040d210000300a03006040007090b0080c043c4000801c0441c0240840e8904003076900b41519045030f1798808a00c695002451400b88191400762829401d1040300135450400b40c0c0000035035070300c1501406000c01c140441d00c220300848015801d0b611810050020141c008207042140f064145840ad0081039840e10051490300c280201d00c0c8244812444103d49040d0348541d401d8440c15001c00e141020001018119004d0f4034051180e03501558030100001900006524203e04c1e15480d0f800c40001e0090306c004107c0003401c00e0795490500002840c1c0b090f0140362509440340580203c205060f484410f488402d884030b680044d681402640094051140c29610030740341003810415100c1004078112 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 515139163 1250 515137913 515137949
    0xc09030d1d1305150a0807090b0607170d050f0402090f0a1104080703030e15042102090411010206060f010203030a0504080f04090603030f2f010b060c01020306031501 73
    0x16409400140900300308039008618850300003030400c0c1104018107402950781d0240b005003001e135940700391004415540c4000b202d0800700d04d0780d40d50312544600400c0075140c0000d50203d0711188103030760404da80544000c40c00d014a110321140c0c3d400952031144180e24040005c0c50040722201e105014075009012006161120705020200e00e50060070300340b01c00d86600e031100813041404000d000602c02c0b680903100707084c113624000306518003402d020352292070150000070440e450001120304a40c03032110074035508a041d0200c0d01c3e4082080c0c20203940443c0200800c07040c008503561041d24402d0990a44200d80d49410030428407000c00602c44c0e0040e801480050240381e241e41c043c07500306005040305810030b50004040240e0b680700340c1204003141d4a82500b041090340019881d1038520150403d03081c03840c1c0c2e140303009043c0200030200414610a21245920792982035102014480000e0500c80c5d864100c108218040e50041e61818064420001c20000c00340f02501014107a4103d4048078140d01c83c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 515140413 1250 515139163 515139167
    0x1603020d0b1803040305070f09020c120a091205010f0e190312060806010b0703090602070e0a0b0f030313031406010509131106070309090e0a0503160f0c14090c09030d 73
    0x44018a211500c00d4142e9000035100800c10183c801580f05600800b00c440c00c000c0141c1c001e810aa0000701c45500600001c9114440429131000766291000055154000c4040071120f000c6103601203201c40d010003603d1010302506400c100359042e41800203111011401a901c0e90f603251001c0b041811400711072818000a114890b00010003080440115000740c840c034505082220030381c42820301500005003442015004941403005040500241100e107151103058000c40318000e0105c402c0d181d80b82c90302c4080359180090703c500d102000e001c9a0320303a03d00c03030311004558455000903141142010001c40100000050071416103c0242040245480d05100b9070090241c0444c200c590b501d00303101e4500241c807280c019240c01030090b524503200781c0c42c0c180c05904450541c80ca241003a0007801421022600000440340c440c607040c4c09031b689040703550602d80642d40410b103004044440542000440b500042003020820104503849101a00d40d240240024810400d0854043c0c228195407a0001c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 515141663 1250 515140413 515140433
    0xa15030b01120203090705030f21072603010f0503190b0c0408100b01030506010f2c2713030c020405060f06070311071502100c0c05030712021603020d 66
    0x440181400d110103502c2110040c140d800071140b050980c1e0007000104414078040140c3d2071401c01032406030840301f00000d0208080b12541c0d081e42c50f1140c0010b0400200001110442149501d001030f443e208a0507901d40c0c110741d40207105607030850b0340a1001080a1074045a06540406141180440e02051759182c010380807000302141e43c20303501848001012001805030349007007144500000360104006001401721000a030902c1d0400641c1403016180ea81c014144034076a442c401166000c44890908001012103880040c5030002c0040300761122804020300300c2d08410820b45500f0307125503281c1c0b07075011144805000150019180d0800003003d400c060303005c1c81c2c010724054102b030031003528200410110341c0724010840002d0303a031096420000e4001d000b0070000d07240f480481d01d840299540e0003175031000c01e07040c42040c1c1c80d99100c40f03405450040e8440039000342e1200c1505e480c3c0c9100d040181c1c4c810400707413801000d402441001c040c3d5081c00d005c0b104c16a0b500800155840e5191703151454a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 515142913 1250 515141663 515141681
    0x603012a0908100c030609050403200c030f030c0d0f0203030112050a170d050a1b03051e0408040e1b0706050709030209090f0705190509092401090b0a1503 68
    0x3116041d1804100c880040c84100380d040381d99003001c900160a000001c0840b441da03880300c0452803078a410f010000394420186040006d20004480c58a1506190641800c01c0c0480701c50b418410010039128240707020010344005244081a13459070100c001041d01d21030140c107008001600b04100502850700c40040200b21503028200319000e6410f02e98403e441901440c0c036803006000c0c00f00300b0103440c011a0084070790005611009020001d0500c660324404a01c2007040024983c42d4030006108d64031440181c0d034042040001640d450a060a107000c0b16807240c09a00c03582da00765000120010314881006885103d0312011901d0030500e81c4a4000400c401b1380801b080101c6a8400070140c0d0301d0050340ba01694241c80230f008006a545401881c12010340c0c03201e40100403100248500c0c1c90ba01e5283c0c0c00721501654048044d0342c030102011700f40003a103440d00e800440b00301540e4103070306821040c4a05941151408000c0d0700c60351403c00443c140b0507c80d0050821381d01b000308103030600c290042201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 515144163 1250 515142913 515142917
    0x180203070e19060e090d020a0c180b0411071e0506070c080c0d02030405030f06100311030f0d0c0201030e031201031b050406030f02040c11033f0108060603012a 70
    0x55142e4010b50a50702c16512540820320610144980356100f40074031020048180010926800da40d99001404c85503482851a0480001140b202a41e11a002034442480c000e1041000060980c4550415002010280e402001040101e960592060321444c44070750030800600117a0344d400000c4400c900c4002d4102c032640c2e018448501e5108080191895001c03a580245444900308001d06103480e104120038005a40b0400c1442040c404c1c0764a45400d0701d0f00a00c2805c225031030140842d04d86045250000d0a900c00c03801c1c90301801d03078010500c0c182c80380300340d900380013828502807423541c1c0340248044414000389100042000078040c03415040c1c01412108191084d590303907000203046420551060b96642190f2201008525151281d81c001101509141c2d181c60a0920003da4078044e91305581c1c116111140d40f042030103440c1640e14040d44084580b41d1140c2da0900c040c113082002803180c1e045a10684001ca08546811300840c0000d10100c0018101a80a8140c40c031525075480c44000c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 515145413 1250 515144163 515144191
    0x17040309051324240903200306040b0603120301060e0f1c1b0e01151101090204110a09090507020d0305100509090714100c1113050702070603180203070e 67
    0xc0e050b035051800c1c082000c0e00349405032105103132880500901d189145451401040e402001ca10b11340c02c81a0300c0d064175040b00c80d080c50704e1145258682c0b900f0352807021503498841d80c0e04102c00c010307441440600c13980003902980e408288003090494140070a001d40000b1a544001c1c0503a9824000381e80b00490074000d01e0056203c00c41081e5540780318141d202915160110700c49200001c201d40541c0e001030038140c0303205419600d4038080e02ca201c105900c01d0000c016003101d035904014000d4000300740d1381c0d80083c03042040c24002c8400c2400b550001a03e80041404842e0010b1240f040c1d01c1064807950403500501000ac040c201c0c12401094003d20b413250300800b80f0000b00e051f4591820a92090040030020b008541c200300b0b2104032000301e400360610588060f284240042da1142040600a074801c40b48480d4640440024002500c88038032400b8143ca8542001040c41e400030300c0b18116800764808100168020b055510b074000540e5003c1e400d503120303610400c0b004842440f626404600c08030003030b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 515146663 1250 515145413 515145431
    0x907050405070c020118030b18010618060519061e050c01020d02030714030103020627030d03020405040b010c1e1a1323060705030a1d010507170403090513 68
    0x504840741a52840c0016450380b80740401c40d60456110701e00c50640d0340b0704e0001c1c02c3c41c5517180c002c4114014824900c01020240081c55000300b500240050f020042c1040440c542200e102c40041c803003407090501c1400020a260310300c000d80e0443d2001d540da00e64a660400d202445505403e404001101003041340800840c1003d04081c40980f64541c0030038405641c03414403901c01420644400d503086100c603001c100410069942c0701c1104c000240c1c0407480129034802e888150014440501c1341c68040c060360030302c008007030b40c594007c005548040f182081564001c0c1c0046803d220000b400030400b48031100411a0b11480038050480036100d4007c5602030281840b0f540c1c140381c0c0565440104040d108907007030070000f21210790b41590140020040030a0354074010f050792004c0181a0605118000010071807107031191308032000c80c002699030440d00d04209006d07a80288012900d0700b0009041c942400c400c203a48001d2640681c3c1c1565031401d4141c00c000030004900d21103006403082e0380d80c46402d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 515147913 1250 515146663 515146669
    0x2913032411030115020d120b010c050a06090516080309120c060d060302040b220519060e01051003021e130302040603080901020105100f210b0115020706020d0e0603090705 75
    0x680003010008441ca40c0303d5160103580c2d942a824440d08030700f03540000d4649104954402c1900322450414800891040401c2c40140c1e1a02075200000d0014029010007600f8441e081c0c00003900248a44219082000e00c2d04480c034141c000360145245a4000300300e8032020386041811201901700020581e01c4009503c0700188003030b4450804101c0b1192510410020751502e03106510005c5401ea400b124628000d89104031aa17913a82c060a028030f0340e820125040b0710345c0008444200c04500c0c0e00b0460340e03448d80801c45203082d003442490711171201c004148106a00c07a000380c80c0c04140500d60344440d841140c441d2782d400d400101403501960b16035103001000d690f40d40a03800c01140070f00d111603035492680e800203007950f40c010040c01000c44100c3c0c0c100210104144d0005c201c618000d19007082c080c07000c4510243c0d904409000c2c05000381e41c00003292070500c9184000b640d02c0c441d000c961280c1d5840d1026a110300724210842c1c0885c2c4804074800d01c40c10600021540701404c0420f60704130507103e80c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 515149163 1250 515147913 515147921
    0x1b0c03070303110c010f140705070305010510090615090324060b0a0e09150d03170f0f010e070e0d14070308031008012009030a060629130324 62
    0x10940009002c40041d201000b0113101e0a468140280781a80d6083d94064000d800c001004101e41800300c000107070f904c240700c0280996000755500a000f1721042c14140c0d4000208191402000e01c1320b8a84200001c003051103541000c51b003912a1a0f05002070b00e561160b03410301182020503440005c420301010a0f403c2180700d030703101a10049202c81e80b902c6071510002c181c48201c90909018a600606101d41d0744190f018181d01c07500200c0e80508072040314034086030140700401d10b0121203001078040c811180100026107119a100c150444c01983e030303c28003d03070388960980b1540c0100f41803407014447c03414020380741015076000386041d0200c2c82d080d0b82e002d8074041250380251415a404414002203044c01040c01c001450781400078030565031604074081d100d20080d03141400600340010700d614141c400744194201c030342d0404401c1010030b81d01c0c09281904802c0c0c0444d28a45034464481c20002d020001c19074600000d0382c40800480f07070869031134103110300f07440402100040034410054926080760003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 515150413 1250 515149163 515149169
    0x503161d1c08191710090f0902270f0c03070f05040e09100609090506061311040602030c1009050a020d170a0c0c0b16080706090807050a020a080c0102031b0c0307 71
    0xc0b9421100600b200f0040ca00312419a4002070300480409021659060b0301511050702c004100c0002c1d408004841d000042c45280802500501c103000b80071101550210018105a12403040d241c1aa45a408400110f541140c21519510050020921440c4540d914000050050a1440c545a210610080014030807600d191141c2e120003641d810483c4180550001010100b10511007080b0954038182c9800c0020001c600a4405400c03000080b1a180c111500800c00808034a684980f517102c0252240d1054110481c1b91082e1141c0f981244010b10545102e15045000307040420003a900300f044240310b801c2c00f5140800318840d400346030300b194001455244a10307101c1c0102c401c114502002e00001c2d50380085242c50060102e0401c803011003c0c03208446a00c101400d60b01c000070710780103004182d044006494010701044c00c00400500242c002201c6000701d6480b84480d0b945c03410f199580d8048401580180c03c20b03c200c0b41100440341e11400302848030300a445003503182c1c1020030b251042c40d034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 515151663 1250 515150413 515150437
    0xa020d050f0f07050a090b03070b1b0615130c1709070609090504031403130c0e01030b0a0b0307090b040b0405090312010b030f070f02010b09070503161d1c08 69
    0x1400c1e80c010200708660001011a500508003081c585000a00702102c0c9100740754055880302c81800300c0e940c3c01e00240c0017618181d144181c54070041e400b25642d41d1803440300c12000d0320820001c500a0b500150034041c00e8040186402c0148042019880c058049829810140608445a603d01500104645229090603030040c00000d240510042800060703a2092101601d01800d00002c40e910000e82e02400c4180900e190303481e00c03140031036031140d004007070050b140703161003400401c28105120016041b280503110310762070f0b03880d41403c15084482000d00d10798158807a11007084041d000742c10000030480c005000096107102c400118085d100112010034558200044008032098441d4140307000d080b4400d07601d825842e104068610080e07020303003944188049215086803882c802d4001c40c0a50384c02600314407083c1402e0340060034a40041d68860049004505069003c40c417801400c51b9400c41d812110f403607500c2c51000e01500b101c02060803810303046142c4642c00880d0044000f403c0d50344841d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 515152913 1250 515151663 515151673
    0x8010c0224010e0709080a06051503011503350702032506051323040e0a0f020603040609080418050a140615040f06030204030b07020a0b040609050a020d05 68
    0x141400038201000a24070321860801c1a18404040110754906415252800c00e00501074860312400d5030b0760180ca52202c0c3c1940300e41c09455040041d150805400307000000c440c90001210b800800d426200d110390700081280103d00c0c1080030420078000901600504580104d6401452039442c0200e45c2e0315501c500c0460000a034481181005c025840441c440c010511800a48045c91010070b1401d40c0f01e0300c4c00300880481e00f0b8451026038400c5070000c0528045800c42d03840c0403031120201c81440c0002c248107500c3d10041e217101510204602120703c0d40302c1c640003060402d55080048035000600181c2e1150b5458582070001000040100098016444d00e01c1f0507481c4203c1c130710203580c001402030340780d241009c0840401c1008141c03640d030801c80c100c0306c0744c1d91503008210302c00070b81c05194440d450303801c080c0b600018055007507030003001075034007a0100044c9641c0702002039940d43e0444000500d4404c4032070024002c1002544900c105134405c0090b5110980c1e6074001400030900306a00703540075044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 515154163 1250 515152913 515152931
    0x31d0f27010e01050d150b0607030e03100203100e0a0204030b100e1506030f2a07020a0902030906041401060e0c0301140a080c01110f101e09020a060c030c0c0801 71
    0x214140c031a0041503001d0700d240007581054085803800807000b00041a013125182400d4100c0640d401070780d00210041c00c1141c6030b1b0b4403410b00800c9000042e490b14024060309020260340300070740c000c5902c03032001c944a1070020743c540340d46070a41c0d0390000d04030034100f6401d000200c0000d1300c4004060183c00c01d04000c5103681c0c10218194612480503003a29903180072201c10300711544074241a260300c80b070a1508142d0558904400c2c903580161110803940410405031b40d0790703064602001500400e8002c0d1901d5074415194001d00c0c3c00c0344019988129968082e02c0080d00143d96600d01d03803440c90b110b10001c111255030314000f845481065810614001d03010005008015047c089180558811500000c07590326003602141c5440540034854100855807240d8401405c0802c01000c01300f8110007151240c0790b81c00309520080551041034052011041d04007501c0840c58003070041d016400903c080e423160701c1c21400340d40e01022080100d052040c4031050401140e0907071401001441c2450000c100d80003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 515155413 1250 515154163 515154229
    0x1107120605010e090d0207030807110a0806180a05190215041412030702010e04020904090f051c02160b031806040f21091811030412090b0304031d0f 65
    0x100149500700c81e60190110360350a036030000d00c0c0c1f002c403074002ca080e82d41d91070503040a50349400c5488000b600b01307454050019010000090072489891010903291103551007200058030b445144502419550119440d881108510010001114070040802100175507c52081e8090b03009648000840c00701e04210200c182821152001e4081c0010040e5240200c2d6a0010344030700900120382c0c1c00b840d80481c003803c02d0340b2290b12011101e600200240800310301c600d810f076500c159400d10b0207c0044590034240200d0300001d50f00003980300c030f040308040b0581002c00324025604000d15140710700b0340700410006916070078400240a1401010f41e8042400c55043c04640b0344140000c0c0d001003051694820319259110000c0000c0d1800000075041c072a1807504581c0240100ea8804140700074008140810010020040e030722803071440c0c48440c0403994a160201c4603003c111f4000e00032941c0ca4020700d150301e80104030b0513405080142040040c82c100710104007000c41c0c9080802c082200c00c07000c40e101d50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 515156663 1250 515155413 515155439
    0x190e120708070506040e0708100801020f091306080706030e16031407140105040b0904020d021b01140103020d06020c0f032712070e1b0d06030303051b0901110712060501 74
    0x8002d540040c070700380c86c0c07550004000f8002800c4404220442000c241c0090070000064002c111a100a64a03458001c0705010f0543c0112401d07803055804a10081c0c45100310b000b07a1084460f420050103059180c40800d4001d041c210241001c2070181c15641c2c0c0078099030305000c0000d14000e6881d4422807a01d004100e1500c84940c00003195410703403403910140c80c0e0780801203a05440c200300320301e0780354540c0d000031030081d00407150044061070010070807842da90301c1d500c0640d2001081c2c400a20100403501c4002035000303400c0c0030180d0070410610414010541c00c0d00208840c020b80c1080303400c9400005401400d40e00300c1101501c101d41040741d0000480f901111030b0301c4544040394070b041d10b84010462190383d501103108185d100342080c00041c00c5103500521010170384450049080e543c10514240384003c1c11a0b001c118046803400700890300c15002081c505541c0c1104648061070100b04000558488003410f070807484500c60450041850700c6050300071300384144181f030702190781d50420b850b100802e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 515157913 1250 515156663 515156669
    0x303040b01181a010c06060308030108010b0118051518090403080601020f060c0301060f09121505090a11040e0a06290607030c060f0b060a080109050c040b190e12070807 74
    0x242060141100d080c80c0307040d4043d5164003401e00d860000c002e171500c5009000e1a40c0b014040140120000900c1780d010f411910180e41e00745c0c0c41101c03513111684580000c18542c000e013500428171071042d40307a2540b800003d001d54401d00d40313001100c032074200c0083c8007404120740840028941400344081c80d40c0402910810300c1d6580d01408180c589007600042c0350005102c3c0c10300304159004501d1741c1174082c04009020303082240b01c410b10944503007042390300302c081d640b091032a81c1d00d48800101990030205048082940c0720810307040c0c40d100c0400708000b40c94020003800d802d01400c050100000d01b02c1c400e4444071102c0103150020070440e508400c00c1021003404140c0190740030020040020b038031030795401c102507001d800055041300301c0d40c40310b004001207070f802070704104000345007190543c100304c5941c101c841200d8280242d5032001014041802039204007841d010091016035256565100c00c90b00008940c0b9140910650b5140012a101c0c0da019142040b50041c2c902030080d40d000f44090005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 515159163 1250 515157913 515157959
    0x70311010219091d0604050a0207020312030f1602030a03110903010c031a1804260a031e0204050f06030a0f060b07140109020607120e060a03020d0b040b090c1b0303040b01 75
    0x10316483c21584e04500c0038020592442699a080003038102c880035410380342070380e0f00038003214105031340d0100701c0c00d040c2e10036500040642080400640500c1c001000342541c58159806942051050b62047d00980208041316803c00342c244064140c81c0c40c01d1240030230622055402240529041b24441643e6204c00c0e04113010710001110b100b07160300c0300b44d42d4503001b691201c03042c5455400e140503218404841c550f1100350f4100050400707007071503164000800f21010074441240581d04040340004030f1045228550300081c85100303520344c62030604051030f030000213400f01164040301441c0c545c040b0b415503000748807044008102e003024081512021040c0c83d0100b0000c021100c582d0300050720034016041c009022404a1b0b0301c1841c0c071445408001951000503008075110880907902402a4220f4952441c3e258034186d00c026140c60107000d0042150000781104c00030340c58150505026600042010004403200c0c880d00400d01c800b000114401d0b4003c2c6001401c9504019104210522480705661 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 515160413 1250 515159163 515159189
    0xf01091a01030203030a0c060905121803010e0c041d0f010c090906210618120f05090915030a120503040b0c0c0727050a0b090601050703020c0607031101021909 70
    0x1030b10b00104540320b86c0710070f0070400c80300c551a142140107023141070300051140c0a501c022250041c403032005080c0000e0200c00d00458075a42d00145422141400d8500d010b41d4000d011907170740340c200b0380e02c4114241d5416030100034009540c0c1c03050b031404500700510651a0354480510301310503404a05a0091b080701170b41880034130719021100b8032a29080075805400500e2070400c0c5d00300082c640c0f010a400103101c1a059080140703061020306241c17060050f1010a400140d2910407600c10f03400c41c1c110441c01840440789884040e40c0100004204050507090301c52036103010041244100c07500c0c9040000e0b40d447e5030f41e150500d0918001c64002d403038400e80000c14840c50040745008070703950003a503480e178280c640701151040003a030841c00c243c094085001c0c60300050100c030351402d40002012420641d00d041041d1100001111107100703000c40035006801901606000346050402402214040d01e082c600d500c850300c80c0b05003282e1100088c04454411003048a40d41604400440014411182100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 515161663 1250 515160413 515160419
    0xd0e0601030c0608280b1009080708071a03130503040801050a0f0603030c060f02041805160e03060a0504030e1002030a080903044a0a0b030d0e010c030c050f01091a01 73
    0x1001901c9840002a4007100e4020007000c1c0f4070103503005044d032400040085020507d20400034040d03a0440c05012800d0107800004204640005888400c9805009112803510034002020780c460300042c1c03940c04180b5849500c000810750400c080c01c0036004001c0005024145140c01c0d004803071000d80442203482c00e00e44c042000c680c0001c860140e51381c011002084900c0c0140d500c2009210f1030300000426048106800f14900c808d40c042352180803145565000180440829915508170fa583c49506512000001d0517030452904113540191090910903c05820310b40052110490245004016400032421800584d44507881c290840c210001661416013400f591414a40c016001c6032074288561050203201000703140509071406020b114070320000c0710001009200c0324140d40900350355052031410005440e01080d1b039400b40b040340d03e41200f071018420054460900d5100160107010800300745101261041c80b1b44408802e0403000020966807030729040012141015003203940c121404014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 515162913 1250 515161663 515161681
    0xf06171029011d041802010e06160816150207110d05030d111303050304032603070305040f0204051521070911130816080a050a02060a050d0e0601030c0608 68
    0x520180314082c6040c07072030308014411070b4840c9400c8803c1c0c0b6400600d01048040d0386a0079051494101d40300b41ea489486440c0c1c42d040045c02c2c002c0c240a100810b00f1829000002401c0000034401c02000000c2e0411041d0151540f6099500501220291540000c2d00d8810403094808075591854110740740080b40c0c80d1a202c2540d60700650440a0350a55a03100c24107000c4e10303e009866500d11151000a402da880e0b1800300e4681d00540700444040c105c4806040c0e5501c0103072014110b0140e4051000c1c1942d440c0d8100f200071700006002035800f8032494404c1800758a80d802140c1c440c1313220307101200c00e820341d2000307200180080b05500240c00e09000c500144010f00440c01404903800310902064400a80313a0f21304041c491207404500120041c0d42c0094011030200d101010032440c804c40020040c1e85041d5280c551440806c02070260304080c18100041c581080a800721449600c1e01c107081c07031100c542e6202103c10340e2a00304120361040c0010401c018025541002615213480c004003241403030029 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 515164163 1250 515162913 515162981
    0xc0904060602011a060a0905220b0102071503050a020f120907090225030e210601090b010203031911040e01170a0506070e04022116080709090f061710 66
    0x14500c500c1000550300c4165101e04141400742c40c0c020302611400c00f03061524040f2800200c2c03140c141c141003000c2b0071641c1d80081000c10850380c8a0352a61300805101c1003c0b401480024094030f0000d0b070a002200c0b5103810032001d04150020240c0c02c55660814028003031600f20345900c6507107298010002d810302d007213414400c2c1140501d0030741801d211040f603280c1500c046201d845426044070300320000d805400c44c0c42c1e541540c50b030741040030f4a10f242d8980c1d402c00f0680d80d000c2d00e01405a88200003048900d0f00b412010845000e04680020760128590b56000050703010340c1c0300703884420b156001031045800c140301340c14424a0103002041007022075071360592034000040c29070091002111541800e9110341d0101c078050642141e004141702101c40c801000010290b80c0c8648031076410138505c050034012401503004094903191184402e140550007005800d05100024006440701300001c0c0c640e228a00a82c07c402070000600700c5180440d504104035541030f800034407800a00080c4030515510300d80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 515165413 1250 515164163 515164211
    0x9081902060c0a1403030a0c0c03050406110a1202010c08130f02060717030123030601061e03020d0e0303042a150c020d03050307200d0c0203070308030c090406060201 73
    0x888030340326100082c895040043d0381c600508003143c40342a9407008000800214802d40c85180100b0a903503590780c01f01c4071091000002408541d0070801805803500400b08002c200d9003900403035018100366698680d207008182c02400c00b41c0c0d150100d035a609508444c3c40c031342c131520194503141d8400e0507454400440e5248100a07008040000c1ea2070705000e03070080034213484000c5007003a681ea541e48004800250280314203003500c0a00001903c6410b107400302e0218100d44030781c0e6034071211070301881c6260081c40d40307102d4000600d40e003000300f481c0e05c0c2c10030300415030b001d2040360141d500d9140504294841c4000400d8040c592440940c80340c000d40c090041030340640c0c0c1c0a21860078045000e140c1619204480c0d04082d5000c240300388541c040603400001035209a2055581a40807a516100103401c030144024141ca00d4000804000c9840c0c440c4e599004005c1c0000c045807542039880d241d1342aa68010740b0301b260800d000140c2500f41c1e013030500030000240b000740b008100702400d10704854a000c175481 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 515166663 1250 515165413 515165419
    0xa0803100803030c0910050409090f0b0f0f01060e061204080c0c0d12030906090212061b04080a02190e0a050a0b01090503150c0d0e010e06070309020312030c042409081902 75
    0x200c3c04c10000e907c1003050f2030203130950340401c2200c01da95080101c400d000385d08049410041c03060000380540c00c030004480c01640410600060369003041010b949074242c20006c1c1e500101c0600200b00003807464980c6900032400342040720b40e140d580400090500030691a5035000322848020a000035a0090405108400d0b510300040c04a40a01c0c001001d01100302001c0c2d031180411103da084000045041d50107441000c803200e0018516250100c490301480c40740523034940007030121401600f450b00320400d84c00303201142c0741b02070394540a4441c020301050380c3d6020b48c15034940c1000500c05e010710846426880074200014145d24240009564440c01d080c00a0380b40c00c00c09c042991402c07000152600e60f80810402d100d06401040100d009102d502c09001803441100d000c1012940030f071180d07141c410b4001e00540451000e0790124806548080c01c0801108808c020020300703604010114203040b820801290079444420a008010804940100c06e080c0c00182c00c10318800c0002402900c031a5040d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 515167913 1250 515166663 515166679
    0x80a03030f0b0a3c0308090d0203010e060f090303101203030605040f0b090615070807030c021e010f14041206090c091e090305030a020304050c030a0803100803030c09 73
    0x1200300c01e005800c00c800100d401810320200814428214100100d030220700400d05940144401c0d10034894402c943c5000f00c0d124484e61091000c82c038010000c000b4a034014010041c08240c41c0d010a085840c2c0e002840801d400c01005c1c030902c410341800d829008846da500960960401c8802445c2d07030074007403294403a4080d04d03059403402c16010b50000b00060070010020410403011070070003000b515040e003c251264241200091182c0b0b07183c52400700148020000c24244940ba03654a10658440c0c02c0903014005002d003044010303900c6c86007600025881c1d0360b8a20565210800140180300955604c40a0016006a5244115030301e000d503001c83d0b02ca1411940d01d59030074100400240360b1444050070501a8620109100120350030240c140300d4204000c5084490b200c28140c1256070016005000441c00c02c007140c2010030380d80207181c1283c015020354481c21580000a031500702e000904075100000031041204030100e0f0308841c4014030320b50f0065407a40c07420079401d00d81403048541c0c980c0300d0402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 515169163 1250 515167913 515167931
    0x7030e09180706080106180803030103110d0b0903041401050a020c010806010302130b030105010f140304230a03020c09060d0b01090203071704050f16060e0409110607080301050a0e01080a0303 84
    0xe5001d510780c0e0014614251040c05448080041038228240120008958260400700d504808082400100d23014500510b0460342540c1d9140003592034161426444074010341e545004c100180030050056800303c00459590340780c8a4541d000515100c81d4906206040c811002c0942c0c011600010a400901c0c28424650b01c0c0e0700182c2c020302900c481c01d040b01243c2d0202081e131849890085043e2a000d03200c50381102442402110903d2990700c182e00441410304c045800149408400142c5111a001760709400700a40010b500c1c10000709010f80041e407100049078400d0400c0c524a07038005100751a400d400704140c0d01e5480600d00c040c031610b5403055000000030761141c0b081da0900d4183c051400c0308903440c04c20303062041c1d0310f01c3ca5105041241c0519504866280401c00040040b9041905c4000101c0344180400004180000e810350f07400303054008240440e501c00c401040303024455004151294100000d0040500054201d880c84e1460b150061040490001d980740c40164146401b00708a24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 515170413 1250 515169163 515169181
    0xf02030f03071109010509090d08150603070206040c0503060702070b031807060206010f0b040509010902130911120906040b043009030b1f1e030804080a0c090207030e09 74
    0x812032181102600022035204104044840a0b510529040380c00c0050390340c0303c008200c696503003078444221035030000b04004104d6005203040340c0e0041022090f11546100b01002c01c2540e03008851101c01600000c00300001c0001c54415140a0042900109030031324200340007079900c0b0707014003581d02162004400039100040303650400d019102c40209440600769a820083d68540c828000c640d00300c2030710b11012540c6034003207054030102c0d43d00510b0110380c0d91800a410b0001d500040000728407852a00c07000c64038030300c50700440d4000d084582505c0e5840c00d245a01c1000044c010b4400200394110005003c081910003110980064000c1840c405031940c600d645081c100c44481c1c503070720401c18410005d0302c2c01e40066045080b0b0f4001c07562100c041e52000c22011046540c280f916410ba0701c0031000f40556040c41d251034041595020202c6100d5480361500d00d1203411070b5000a003198040610402040556082c207402001e1000041d8100b800e25600505030b00c080241090040b001c100000d91454 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 515171663 1250 515170413 515170423
    0xa0605180402040e0405060c0304030f11160e10050102120f0918091501080610170f01051501030b030a150504020d061b1e050d0b0301231e090a0f0203 66
    0x204010002c560b03d41e0740d98030000b800c2c0e40450341511507002c1c0100040c182c82800341201d210fa036040e501c211800ca0030070801c0c1d070014220800da0f0b020780b0440c079065040e042c01c04001c4001d44081c01240060f4502886002483c074216000b890464200002c0a184481c4400a855002e00d04a982d280c480722040c0101700243c2070200383c04004940d4100b0f11908100109040400401c00d1041c501c0c0741e0707251030459035940c100f900da81010707840d001010403091030f4540d000c6078031121000c15241c0ca19071100b041429941d0a03140d001c11006d0842d0303850040d6815200703c440035501900500740c000c10710340760340f4001079062035007880c4141c440000402315614440d0b05000190f02540c100041d184c03100c503500305c0204552419002c43e034505c603911901543d45020000800c0c503992400d01d0491805005400313008400071140e015900e942100303000300a2182824080c000920104d10145490054802000c1664841c100180020b20a01507107040202e0030744159600425510b2905c165440824640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 515172913 1250 515171663 515171707
    0x90603042a0608011220060d06030308010f08070803040b0a021009030509040f020c030a05070c0e0906091504080711031218090903090a0312090f0303050a02010e0106050a0605 77
    0x11403200c4841507026040440060180c90580d40c54440c580c1e250042040e0710008603070041e0085007201248022400324803412520b81001500c402d04214207498102c055403150b410403804103d40800502000d043c02c2c0d040002800420001c1c07100520f440e1403251a40302c0d6002c3d41c5565900014451080c03402004482503e40d43e28200300a2401c0500b802440c5070410704410b0310071030034400d40e08440c110900036542c50480e0000510714200c04c0c805e09488030790040104a500c03107440722001a1a480c010800e602c60a1340a000e00726600d40420540d00b0000408030405403109510140004103410380c2c02c2e10702a562010030356143c240300c0c00020349054040c1d51072485851f00010012014010642c1c2840c9590003034919092640703031105083d44074064a003400740c200910302402c10115600c5101035064003000c1c10020034090f2a0240c582c02440560010340c041580082d052590a034244074120003002844000c001150402000880d201040d11175142007140216818038458045101d07440f00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 515174163 1250 515172913 515172953
    0xc1202030f0a030603031b020307050418020d1b0603060b070303020705160f0501091220011b030201021213120503060103020d02040906090c090305101a12150702030c0309060304 78
    0x211001e0702d50041c00703090140000c40001d00703040c00c40141000d2080b81d4603c829402030103459200e0030501800000d2010b00074062059280e02441405a10707202907207441c85000d1483c0c00e12011511104008090795684244101482c04104000306040c3d8020760f12071941c54540541e5034a003a0800030b15101c13800380b190b844040c6240001401c800038250f0f800440310b0a0700d0343c0706920707501c0b40842c0042554180142170851a19240e0350409501000d00c0c5110005041c69131105002425100e1400c0c20f4200860140c3c2d40010342c0356214240c00b0708180d0000c08504010301c00c20701c55854401e2120442d005c90b0500c40e001c03000c2900c48c0e020780c050398001c0b9200d002c00c5403030f41e98419860020340074034400e23001068a400e9002c8c081d2071250010781c0569400000800180142e4400000140a4a082146040000106003072982c0d140420407101860200040c0b0f01c202401075100780884010f4855400c0d94010400740300b82040110507194856012512142c03a076460f03091400300303045c0080e07101790 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 515175413 1250 515174163 515174167
    0x9120a09150f030c1106010909030306081e150402030307060506041d03180105040302061905040f0b030a0e010c090e090a0b0414060c211f0f0302090907060c1202030f 73
    0x1c0c1e00d0b0340c40010303a120220941d4081c0103007403c02c401660000350400100c0d03110f400013401400410000e811208a452103480c001824580d9004000c1c2059607611aa01398803284070500c003c5042e0800200c83c588036108442901c5091541c0080e6481c414980020001d07900e420000340d00343d5869101c928848024a8000e0350350780b9420419840b6840950041410703ca0208070f200294498000d64040d80e42c054085483c248040c1c115142d540542036034001041410000443c1d2070358040c2c15007009100c0c502410b51642003001f0b81000707071a48500c070f0250300c0e8586010b00d80c000382d00040741000c030b034215051340c3c0007038860401603418805403031005084145590240700030020706a03c0e80c00c850f07031741000b0348005071502226000b040c491010001240c00c07000711240c50018807030120355080604a5102e94240d40001130b00030042100da8466041105801e07010025410108036455020f00040090205941807074000f0308000752221002c2c02a0420f220700c03100141c02042100c0c150304040340041c1e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 515176663 1250 515175413 515175449
    0x306040509070e070521060109030b1b16030e0d0201080a0209060f031509100b07150e10150b0301081902120a24020a270b0403110103050603030309120a09 68
    0x517025900c015101c0950826805241c1103401c1a21881e600402050b51003511003032464440d480345070000790240e01e203441c01e4003640c95091195402040c404108240c0c4000124a41c01c0c0500320349003004015004072a100f00103030050780e000c228a5446070000d540182c0341c013044401710380301c0d014240c10418009000002d0001e501801d494014081504840016a69440014100c8c00703000d0781c801d0a9608006001c010009145100000000c24800c0c40010319041640c20f2189046d120300c280c03100c1d2a0740d0b50328005489208132a400040c0550607000c3c4c0c41d55142007c0d0316074402c00f1000c4180100c1e039166a0204650350207024201c441400303011285281c41e10300707105180780312480140c800824003010310702c06c050060003543c1501d00d4030348400b0f44084005032803900d01940640c001c20940c00302c41000c5440c201c00030140000d0742c0200c1c071466070648500300250842c1c07805049203100350300070310801040100008011542c0310020500e2912200d200b9010385a0801540044030b000c03102030703210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 515177913 1250 515176663 515176667
    0x30c110a080a020c1309110a0e0f04030c0218040303050a1e0534020601060f1d0604050307230105093a0b0a050a02040f050d08070c1e0803040b0306040509070e07 71
    0x76091040c018070504541f444e0980030484040d0040c0f0410000041c1d0740d0008800d04081107000e03034014080c3c00c1c0181b41090360340c0040c481c02d20100c03208008041110070310040c954580b1a80382d03c4480c01004000c0d50805001402c03458040307404d07600103035480c0c41c0007641e480f03c550102e1101e0181c2c212605055840d1100c444284c0310018103c900620498000003010b80c4240d20800c50080729440350b03840204da2441c070078450f06040f1800d41d0400340822001aaa450403c198401403406880f00000011b140c40340041c8810b0b4103c0860402c002405081650b50394094040d900c403031500802c44207134101010380d91030b02e159040005980c03540081c41c6420300900710700145c40341c1c01c8880100840c0e82c0b41003100c000c9000d0b5000e000300b0000000e00a100e03134100b0304000b4034442c0c0509661400c00d001c40e0b42e0710440310a140c12002282d4800c1c403c6200740a000f00300d42000d080d030800a5030410f17042c50081c0102d03020090906104070344500204041c00014403600001d0250030f11502840d1801802c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 515179163 1250 515177913 515177921
    0x501060c050105070201090f060504020121020a020c030c06030f070306030c0612140103080d0903020309190e010807080606040f0e061f0b03040213050402030f1b01030c110a080a020c13 81
    0x1d4400307500b80301c0000d24091041c480c00580561084039450240d00d01c0e1500d600803c4010070482c1132103601444541d42c000215044202c40e555004096074401061000030b0400c46e1698440c1d009903c2003160100d00d6542005aa911104202031061907070390703d104c22009403140303a201800c507240604002c11466440142a52012100c00040c441e84e03040d002c10100070b070803d02c4094920f00d014000703444101001d41002c000301e40640b04403030038030b421040004e0780b20b0270303030ba1030100001c5490701c0400c207000344040751500410880c1c0203021128035002003140c68110080ca60ba100d00c4d42c0c0c611000000e00c00758402e0260040300000c5600703c0c68400011b8500c2111480307002d00a000d9500e00181e808090030480b803003543c0c0038008032401000e02407540050030010b04120780c94050044800c81d400002c11007002d01c80d03102d41c11400ca245212001608440c0c10320303004001c211019501c010a44c00000d001000075178041d150300c4ea210000d500c202c3c05c5c0301060103102d92010094200360414489600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 515180413 1250 515179163 515179187
    0x20915130918030e102c03010506010521131202010b031b01021c030603051c080f01080604120908011806060e0f0c130b040602060711010c09050919050106 68
    0x2000304404402540200c030480b00740c020b0009030803c0300d03078426082640b003c0c01c0301840760070080c0000b0342800ba4403807000c00d0301104209110024140803d140380034020315400c003100703007010b80c541185200101c50700c1d080e85109072001060340340407230300c0c9407411030118030010b170407180890070082028402406040e242041c64420302c1802c0040c41c000410500034a003103a8140c0060404000c00c0000242ca400c074100080103141d43c1d00e000002040d030074800c01b600912949803c68407103c0d4200040c00002024210308280304400005201c004000905a600b1a40043c8484007003904071000311100080da421070348240d402d041012030080c04181c0d030103046500c20b400902900d921241032001808045403020b4007014a4000314005184080080c03020900201d040711406444028412503680700d90f104c3c40042e40400108441650f2014224030360b003a559000b40111400018002e200d48200d0084902ca100c0c01d00120b2881802102c107410050340c034000501c0250f9440b070b4060b1403051041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 515181663 1250 515180413 515180429
    0x306040e060105030d1b0602040803040f09060b0301180b030304125106060806011101090203030a050d0f05010e0f0f0105030706030b030a020409060b0a0803091302091513 75
    0xa011124003140225000b8142c40028000382003a00030503208a654511000401480c86034101d42100410150700003000a0140140110703944c1340380854807007202c000d41e806a42e0503403806205209090240003143e045640684403a6003240159605900910142d81e070a545840b000900040349071204000504207409500c00c0048202c0071140040c408800c20300b801c2131440b8480015010607900024030706e07030851000f0040036130908030840600300c5001d0f400c0600403e0b18101044010360f80043c10340c18a80301ca0009104003000d41d80401c0e81d074082c0e24000010b100011583c517924010541c01001420003000c030500082d6940c90544031150819640b000680c02c61500144e080e41e124031030319048607005801400300ca0310b08142100204402d03204035500d401480610005a6a54002c5000490041c42c0014500d0743c001d00304080340e4800e074080c4140b84c109000c250540d07510f4142a030003c04800750050790751080d020000d03001030301e0710343d5582051401040c8585c3d4000e120481d4002e42e0804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 515182913 1250 515181663 515181671
    0x8090603093a0512010510090306090305091005090d080a0e0406030f1406100506070c03080319061505090f0d050703050c040515030c1e060a1106060d0b0112150c020102030604 77
    0x41502120b19100d40700420390a000101300410450400300c10030381042e0514070f03040d46400e44130396460040d0349419205030005540400c0c074428030310b480790796041c440c0c521b0300b4000e00d0851410b020441d0300000c040090041c280102c0c48044a0740680d5441d02c00d81d000a1080121585900c2d103d00c410450f08e0050311071f28140031070f0741c180e814001340315802250354140a05c0542d2401e403c0000c507034401032086501403d5201c00000103808030b0f018501500070040c040401161200d000b10898205900524040450418100c005900001107540f0a001604c0050038644c2c8000070880d80006510010190300c110800001880710102e000710059408840512142e228030703070001401c0b20701d82000b90f8542c00000d80507040c6d2400100410000514441c0507002d50034900004100d5040038041001150a0781031106032008180481544006d00300c0f54105214025151280d4101c01400b4120032111000404414007090f0790b5103004036000001c0c18046a606d190001b07011390000e44a041c061820 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 515184163 1250 515182913 515183023
    0x2c010513080f0c0a0804090518071401030e0c0910030303180312021303140d020106080f070b0d021228110d09020a030f24090809060309 60
    0x3424403014580d6401000c0c00d8101101e440400742282d0150074898203602c142c0c02c811002600d081c0282000348519080010189090b81e03004400d000c4c2414200110340005405100d0081203481c1d0050400c020b290000343c4200740c031620303850a5402140c003a4848007010800c04013614400740c10b01624840e507001e1004010316a8559030b0310228440040c0444c4c0c80b11002d0044482d00c2d40900b014035040108510000d90320380f120780081c0768000c4611400d4201c0f4908000098090103200010800c00004000d48444040c09546508807400340e00e181090000c0c0425840b201a01070381c0309030851821565807418004c220b0360185250003516100000c034900794810000440c8108110001d448807214136001146030800018403243c64100d070b00028800d0044042408848100c65461152908036410350807000c826105100d040c0c44045868203101d6400001203541041d07801619065820644a41343c0c200c1490400e03040a800310040070080407036403108220780c1440c1c600541194107885d42122 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 515185413 1250 515184163 515184181
    0x31902070f060c0303020712030608010b09090d14131415130605090d0c03051e120d090602040e04031e0201111603170c07020a1d0403122c0105 63
    0x24284035400310807070046401c0000714010a01c0c102240e00ca803500526082d0181d80307200702241341241c07100020755510418046840d0910443d000e085048540046510300101d046940d0842d0420180800425001d028040d1a0001c155000507602c4442249100d031202c00180b0003600803d03010348a0403c681c451202d92281408403585114a21000241507082c00410f692950000000c0c03504410792114050102d140402058059480b810240c440c0100c040300d0030802419038100c0302001c0c2c2200781345060803900c880448803010b40340c45001c600c5c2c010508081000b0301030b9034804004546c400c03003003008042d844021144900000640c1400b0f18034185000c80c22140c00e40742c40d0b182c45c4410800100081c2038100c2d859071b460320915042c6070b10f07090340180c090f00300801e845d45402010003094040c11403504001d440d01800d24a43e80380d0b04c0d1002001e079459580805840a001d0004411101040004940080da12050a01131402c0754500501540080d8111076030062615440d01000c82c035840e03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 515186663 1250 515185413 515185423
    0x40c0605041401030e210417030415211a0301050705090303090d1401020f0316030209060a030e0115060c050601050303030603120d09021903060b040c0503070309050c040e031902 78
    0x10003100d242c100c07081407400107400a040b4800c612241e845071484001990000440500108035003e4113940c8907403034076a02440c614801e20b45200d85800c148414803448860540710400304c4200d2074200c0d51030b00050544d0724250310000040020b03a0404401c1c0c0b920282c07210703100c0c00c0400706500070846541c5800c407c4500d03006100f00a54141c00800a1549034580314041803071681c000c40728140d0072000303284000c1c01c90b804212a69103100005c000c200111925464502510406013410341c900400503002076080c0c03107061541402e0540e580c44032545c0d58800d6002c2c00785c0c0050350341500142034171504094025800b000084070584180d10000c00c1c942404400e032801003d001d0020581d4400304112040180c10004100307185503900d4441c2c0c0b001d0b0380c0b800300018041c2d0780c41000d480e402d81142800c0341a01c48040000e4041d50801c82c059003140c6c0d0040c00c50783d0101c442c1c50001400961444c0c29400d096820700b4040d4414200380350200060800320043c4a00e42c039500c501007004010b480e060b6110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 515187913 1250 515186663 515186669
    0x30718060509120d1b06110a08070908280809041409010b0411040306020c16061709030a0e060f04090f1401153e01091e080405101b0b040c060504 64
    0x1c5c0a40403900b80400789420760941161040b14042075203562082215029005081550300103203510052000458100580c13a0103491a50082c00c6c0145090742c902c41003e8904e00341340e40d06004044c2c3c840500c11014296102c0420080003805040a08a03a031507400350181d030f1120842d460400d02900c90700d850b115000c58002d9207e005800d0510b19190900203400c0220001c1a50003044011458400080400310190060b5201c0710172046e0401c20320940002c0c000c11a9800358070800c8955005900310161180704070044880301e640e41d03508035041c01a406154001c2c9030790b80c1410391080a001c0d407504050051100111048590303a070b5070580c2070800b0301c2c0c1d03407000011540c2e06189600d00704100d43c20140034441d445002004000845400107a4515103064590360b035034031808142041540f50580da85444e20644003000c0310b84645036140a4840d610400d072044901c00210f610050003649a1203030301c44404550a024006030800072410b1604580403207000c1014a804244d85005405890039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 515189163 1250 515187913 515187917
    0x30115140f010903060b0324040506070504060203030402130b03030a0503041208040f03080a0b0924040b030706030b0f060c07030b06010c120e03150c0a181a030718060509120d 77
    0x70302e4956211317000101440340340300d901401100a00b14070b01640a401c1d0740b00700600d0b00340448500c1c16003800340c00c004020b03200d041000800c00003046055800415a0742094044400b030b00030015181c580c40c0103100b0300000b40e806000208074440850b0b0841c1c040c0d8800d40c01550a90b000303e145003030031680c462080f9001420032081d01e4420021030711605200b0340c4840030400c00107280e00480000ba00002c0704650140320b1400600580a0f1a103a59075070f0312040748261414000c000307285c03000a1b22950320740130700002c1594030000021240e64070105680c4c2018058155070780e94680e00351040d00c41c54240015540031414001240340b551090924070f102035003246082e13401e001200d0b412600b200c1115181d03941889410100c410600c90f40000741e000c0c09224040e20b42c0e848804401a0100d4048080c13080118040c20f002c11a000c038219881440210b9074442c240d0302d1b60381c20029901d07081402640c1c6402c18081c0c80110741c142d0440300504240104541034850003011180e1240d89080f50702407800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 515190413 1250 515189163 515189177
    0x71a21040b13050c130e0c040b0303090d060b04090303140903090d0b15130e01110405091f15020102070201090504091a1b0c1e06040b061e030115140f01 67
    0x40d180301141c81c0c222030340d44502c090b24402000840024200000030240070880e80c0c6d00c1c40c0c80900c80c60300300328403c80d4501c00d4806014050800001a45901075402c800b402110380c2c034440e4040140301d85c410b00c250740b0010000c01450906080003070040680100e0755140240d07800100746001000000d031820a40014480030941c03c0700d0ba1001d0f0055400740000404c079240600e41e9019903121420414281c80805000558100181c2884c0c2505d41e20486107070f4142e800c1002340415100c943d41268400e03100207100d2091010010150118882540410700480440102010175541900204040c078001d0381c45124281d10b400422007210303c82007004020f1071420f1465026500c14241d070503400881038001100301801120072401d5070340203030900483c0c1c0d08841c041c15402011700301e8003014072030b507a0000c24a5182030354a52405d24405410b407480740d1040c000d19040e10110f0880c04405900207002880a00d100c0c40c0642d00081c064003c003201e60100c15a108040d08000c00541da911070141d450308 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 515191663 1250 515190413 515190421
    0x8090304060f121404110a080a020d050c0901030c030501060509071205041e0b160807020706081018020307032a03020d020415082401090308030603071a21040b 70
    0xa91030302440c1c01644103000360100350506041240c4685050b0359004000d403800740c6806c0c6003403821100700ca04164410010703a1800e1010140000751100e40c3c95041c0c0b0380018420590a1982c030300500d4504a0707074001d03070b0075001104102141000b0341c2201c2c4950020301c1419250010040e14010441d0002c000820040ca104d610340b44603002aa045030244000015030124521001d045030303c00081600c02407001d000b40210b101030b0309a5540b031115035280c914198141401c00a403035001900c0392a081000b0704020551483d00055020000d04400c2e070040028040245010b000c0d400c216440d8021910307003520b105540725030702c5418001018021540044184100c016402501700c04c0e81d044c04e1039402e000c081402c8070030303100c22203e10f031054803091754500c0e0407502e4110751113000032120310441030003451400c2031341c004a1081c1613952044c80c403600c0e59a0300021900c0e041e43c1d50b00408039030781340307040d0701098241c0c1100501020b041d100d4841d40da0030b02d6541e400400e05040d107008005016200c002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 515192913 1250 515191663 515191667
    0x2010b10170414010203330a120507082b0e061c060b18190e040204050402030307061a1207180b1c0614010e07080a05070504080601030813060809030406 67
    0x21580144500d0094021024098483c0d003243c1045420703242c1c3c6892807080c1055a0034013458080c008015001000d8500806004507407603c00c14030410300a0f00441c0d90380c41c10010180000c4018041d5101280d00c59610350340d000d4103801203443c10740840c0d2000c0982e100707100d106808050300414050460317490907182c080700c4e20600420300f0242d020169100c00c0490303000301100042803c1d2a907407451130005c6842c24200040000e080420000d007801c800c508102851041c4030071544160100c400089035665400441d040d480b400c60b00600071498004022111b400080f0103c104c2001a030750304a420980020003aa1034886000d00a42c05404d5001d00f8101d4400c0e0300300080098024104044d40d41e00415a01d041d41d411003411143e540d114500e54800b90f080b0f80516004004031070307010600d810445030190002c3c42c0134140080c61a1944d0001d24070600540484009107540c200b191070325a03503030030404899000101610362400070000c0c0003440350300c6002c2e070501811551010754a060300c1c1c030a003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 515194163 1250 515192913 515192957
    0x608010b010e0f030f0a050a03200d0507110603040b040512210702030f03090d1d09041b0f030302031206030601061d010909060e06040605090c090105030c04050a031202010b10 77
    0x18550510449005c00d005c0030003408003e0070544900000d0200d0581880c018103010524030707032142c0684601c4008401e5820010b0b109200030100c0c200b8554924807411f2011003038444a41d90b40c0c11110010038070007008810ba5000744954003d41c2034640400d02111600b02c144640d902d03010049520134a681c207504a6200243c0d040b603603900407246419000412107280e80c20840c1d466071a504025561050b09410101c0854440070850140301050074400010701e5002004d0009058090160203070070f074001480345400042c24403a15400046552894000e42e07941c406035030403020820392004100a0308000500c0d6050310441e45824121001e44601c0c0102d502004401d2070402017451400100c42010780310f800064054011481d00e075140403c04d10055900e240d0009000c0c1024108000300005048103036039040c0801d1a10a9036502c4031050681e150050b600029030140c0128400000c001c003103550090482d030550020300510a1707441c00c1040380aa00da600071b0105885d0444494002400d42c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 515195413 1250 515194163 515194189
    0x31207021203090913030f050304200415080d031103011d1e01120308060316060e030106030203010c0305040b09061608040f050a03020606181308090d240608010b010e 73
    0x849081800311000903400000955a5032607803103c40c0134101c14075138807000b1091070141f00e00b070040c41e50920307075111504080117240110504044400304001591940c101306180200c1c01c02003030020380c691401c95240c902860002c000b0a1501c9400c1c0c14142d441d00590703042340c80c1d003080c2d410000d0410444000d1484014a903864220040c910b00840006132810940a0510750f40046400b02141c0340243c00c0800c05801d2a1290b4440a00107051140380401941590501d00d01980b85c400e004022902501d95500025495400c21004848040d4964040f5204900403142c443c1983c450040315900c41000341c5075003007002c00f03840903981118020f42e20707250028071480c6264448600c42c0c0b502802d003800300c68101c0050f00042c09102041c68424075140c1210103c01c07004070241881914864250000c0784020100900410381001e00d5481302d0b05076070700680009024070582c001030407903080e4442c01000b204080c4e14100d40410054414450200d000300c06841d07540318201240108100702070402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 515196663 1250 515195413 515195449
    0x30a1803060e030a090602060f0703150302040f140612030702150d02030f09060c1201122303130e01140111210702040506040b01120510120f0302070503120702 70
    0x160020028500303100b0034400c450480302031611030203401c200601401d2203a00a104541c4401d01784001c2d000812101034110425040018003a2025107940f5032800e03540d07002a5215140a010065002c070039042a4404600031903145000c1ea54201000038a0690208070790441c5d00c02d20182d001802e00e174000d01d607095100071a00c0e0500200d80d42d441c050303a008507505140c801d94201440003814040050b00e801800d8914410b01b04407041400c0025194144503008400d0ba41e154880244041c070108a060690080c1001c401c440603010300582d80d83c082c40400200d448000d20004824846891540c140d44150400202c8813050078011502d01ca0700403080e46c15801611086848007540911015010440c0440303292134518a00420046902c018113507402075060426034611680d024210155640404500007900c1d01c40204040045150b600300312400031070038040e0400e000400044262452083d421152020b49a5041c0340c2c55401b02241d880c2d48502c203100c484014a080d00031880030341080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 515197913 1250 515196663 515196707
    0x3051209070302131b0306080d03050612060f071101060e15150406020a060f0c0c030f0203040302040911040c0e0f06090d02030304030f2105070b070c1703071b0203030a 74
    0x40d40000b403040101c82c020501c1c1a580340da405d20b21032090203410810111509080069514001c10551942d0724006103c04043c0e40d10006420b50347c500014481d90075080d801c4800518101c003041009400594240000c40c401040b07541003034005000704c4043c0e448200c1c101d4520707200c0711062521186440d29103540103162214400040709510041e100070a583e50040941a0b50340c1060300071070740e19020306071025082050003100240c01c0380c44d200b4444d40c90300c1e14400852403480c0c100c0c00e41c0120380009500c68204044201440107206581701d8110741281d04001000d40000f055500086d10113085401411405070f03600d451078007801420790000003410b400c00301c44071940028103551041d0021184904080b0014051100a01c80c48651a00680c80d5284095100801602c0c1d8001c24030000c00050244000843e083c0c8100040c040d80d541c0324400b90701004058400c2c1c01c0b940c00403a040070000d02e460300540c07038140e82441218012500070703010307524003130b9044c108031549003031003540031032900d1a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 515199163 1250 515197913 515197919
    0x140a0e070b0a0c0648050c0705090c070b1003032d0e010201061d0a060803070b0c092e1b0b0c131a0d0b01080c16141f180305120907 58
    0x4022171741c0880350711135209841c6090103450506035551000c0d140308214040c8040c560803500040c0c62010740c0d50880300e4804944c0c0d05102c40405100c0c0b03800080c8104400c0d0240b00000d4071040810041d24401e0b12a040040c821800010700d07540740b1040c510750048152401128075004040c1d0348005a018400425001e448410308150402808201500e40403003400b0024026414402c11004c0c0246601039450041c10f900e4609a51074007174030954107040700044901056440c01c00c003100641214400609242d200c1e03107145295030b45480c020000c00c2c03c10a80700b400c1c0b04000902140c081c3d1010411a0540b81d001c804c5109410444415003041c21808022540342c100001d803030554015103070700c207540304441d4452406a9003440c1c40d250500281c4810321120344422020b8450400e034034142480d5004150034003401103100856102c2e1301d0f0154800d2070101070042106075181d02c02480c41400030b100c08217905191220310900140010300140040f8080c1c00c04013250751741052a9008840500c1c1c0c07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 515200413 1250 515199163 515199221
    0x70b0a0302130b250204180309210c180219120608030f07080c010204120828090603021c0c0c0b13020306040311070302060f0711031204050f04140a0e070b0a0c06 71
    0x2d8258042d804274841032820006042a9000708110380c0741c0500022142c1700558460784a014107010380e0550f1012070b400b0700c0040f885a4181c0e40c05c07403408840c01e0604060080e000d40001040c004d0100074506108001c83e1202c4e0000c2207030305c400c5124271518940400d985581802d5080b814056031155020840041c0d0a02c0307203004046010b00805545580c0d10340100c14040b9500c3c035100c0341c80303142381c20984680c0864122074468112003140c1030159940112044035600307a8000c01000310100d1a010b088120647e1184001507401d01ca01d6040728643c0b10908000e020141201c4001d502d98407403000600028420750074043c406006804803009240c0320f600007080c64100745080164140041000e400380403196500982c5040180c001d0f08050a203206a031109204a00500703005001c41c1e0340c9070407691540ea0003032a01c1003001500d00302a0a100d0200e10240c001d55820080c50700c5040d00202d0800286400c445030b240700d640301e0705142e80c155550b0401a01d40e441c849600024591800880c0030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 515201663 1250 515200413 515200451
    0x150f07021816080a0e0c06030c12010b04090b04090c270c0804200f040c0207080f0f0114100e070509090405060a05010f0803071103070b0a0302130b250204 68
    0xc200d14806469202080000a00a042c02040c040200c0d0a2620350113020b4000300d00c0c0040c00c6c805442442e40c0380c2c1e0308092036010784100c480a0b1451020440005124200080a00182d80591030244544113003041040180c034580d402c00341a40071000e001b004020800803031145080baa01c4000c8500c43d2007041c1d450200c0d10310300c111201103246042080200002910241d414032040364151845075908000300e901203200780f42203400340d955103480882c03080c000c2002c1c0f070042c80014226602c5404140700b55031075190307009000c40b6640c01c02e030954004840f000442441680310400c00c2e4201442c0495003045c00501812070802d01604018000c1541c80b5000020700c01d030b0007000103000d1070408114060071102c05030310004c40000c0c09201480b04107004400c8a01140e0050b0034982e00c0050300c80064108140341e440703280c0038070300012007501c03130390b0160042c050002d40c28604411440c0d49009044e0584030f10100c41650481400c0d50403101740325110030304c05042c0090800949540d2200800400c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 515202913 1250 515201663 515201671
    0x20a08031305150a0804020a2d0603020306060a030c0c08040e04020a060305150d1a0412020d0207120210021509031b030a0e010c17040303050315150f070218 69
    0xd40002465051414582240400910055444041241c0352022074261070082d12800d40030407000c3c0d0301141c155694401c0410142000f6801d15041200ea002420034814001c0d1000300750340b9000c040015074501038800d480c400c03200030300080c2c50306d0600b141c03c074010950043d200e4244291000c1c1d00780881c480d071002e007010340000040540e0b9418a8010094149407030350000d810142008200040004502c9003010840c1d8107907002007000402d0f1407c0104102c441c0000700c103610941080100303003c2e03a18070051060140b9000e4031031200841d6402c03a1100018018aa001210218032400509101039800301481c000d1040d15035040d00c1e0103401d006110240c6403500315a101050310004e01e03a00c0104003525017542001149401c03016940034060105485682d81070010064450003804440e809000301020480007443e6582d0301d0f444d0160054006490030000648035403030070803007410140041031345800c0b580f003502c0c107164182c2c95070102907014000c100c1c0c028100680c0c40f50007840c074500d81f03030007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 515204163 1250 515202913 515202929
    0xc1b0e1303031a06090f06070203100b1003060f1a0903011a040c0201020301030f08160b0c0711030a020307150509030f0d02150f0f06011715210304090e0703020a 71
    0xd10341641001001d03a09030f8161012010500c401226081c1c0e501c404540c9450001e03140c405600400d0000221030340100381d4041d416002d1101101090340b07160740501e852020884240301043c081d00000c40860300760740030340083e040541000b4400d194041d000c0710700c21b0703d80811941c501002100840e0948560b06445041c00081ca144c0800350710b040c0c090500203440920085040d585142c58200800c0120075001e00300e1400022014008482c40381214000f80d0000078104190404506603c4140d01c40d07042901c10100142001c0c40d00e142c0810120741e100d8005006110440c103028101c00420a0304481d0380078801c04004078403907502d0901016600010342c03409040c4070004401c0107401c0542103018145111120820820031251001c90b05030044400501d40d034140e0383c0c100040e1042c40000309103c151065540c2040320114180e21100003c1e4400d4130f80020b1204404201c0f1051035040750301c096035410600052126888030f612260710034094508a0356920707501d4010410251594022500c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 515205413 1250 515204163 515204191
    0x90d0509060d02090d030c29130507050a03080d0f020406020a02040b1f0305040b07032306030a0f080c0d02061504090203150c0c010c050f03070c060b040c0201020d0f05070c1b0e 78
    0x1402941e0b8812807031002c0400c030142182e60151071680701c40c58012702034940c500c0000c0c40c00c02030101c1048814090400a0f007044130380364490401c0c1e0b503550004c0705000180b0717041003403510805903e4001c6d41c0c1264290f4004015011103a805c0101a005815501ea00000c043c0318001d211000c414012040d03035695103002440d8285420310030000381004046005150410034107150341d40550340f10300c5a4441030760414003d61100c000003810480d04103c042d02c4000c0901c110001d03c0a000024170700c1d0001c130070488103040006002a41c5a120440b0700c200b1142c04c1d10b51210060500382c001c0b03001c03144014165500300c0348181b00280e102900f600c2c4c4140b000c4001c546404c140b50240314500104455041150401040741c2c02143c86100080448041183d1080101c081211a8000c000110b038001d00500c030347c02035040024000e40000c080e0310701036410640180983c3c0740e80d1040c6030055020b035030703239014184068917090013192802c10300d10a00070100304001041c0d07104d0b034850390045898541001e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 515206663 1250 515205413 515205437
    0xe0d0807110a20040e0a08030606030907090c26010e011206020408031801090b27010302130303120b01030b0d0f032c0108060612071b06060803070605090d0509060d02090d03 76
    0x3104a41785c00b102c5982075444108401e0200e0407020075294892800c0385c0d0704d650383d56090040c83c280307078155021a501d981000004c1c1609a08501c000284096000440030405840005480300c01420b1181c40e1030003810000501c1101c00340c0c2d10182605000e808090301c1d10355910708143c40d5038800103030440c04071603280030004650303448443c2c00002c140d4580c84601701000405981d0402c05140840703002c0c550014207605035640a50151600e0b0000c0c003011010050340d90070f014082488240c2000c91091600c0500c00696000f0300c45e40c001400090108030f2100d10a90300c18542c48104001541484002080008245545c4140c2c040b0301c00c040b8204600b4241c00c40025107049006080944038110a202c618501c220706000d16900070014a090070440c81d502000c4980c0b4091000e001d485c4a09000020400e07500000c000c141e100d1054404121550303da0384040e0312800c3d40c0b00300000140040000c1546441c12002030030380000659401442c04995100041001c021414118045070310502c400c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 515207913 1250 515206663 515206669
    0x80615090d062705150a091a04050f030406021504031710030c0911161707050309130b06070f02041d0c0117013501060b030405010e0d0807110a20 64
    0x56010888414900d84000c140d504c0c0c9440c0d10440c2d40c5100030031402c2e4002821020280c028031103c0380c0242d0a03040c0d42c4160b451582604c9000c45050780c070352041c07400c8402c0c1000004200c3d401c6601c607501030224200a2008003000c400301030010b5041010361a0120880007070710f0141c4c0e00580954403040070f020310b1454000c000d520a07605c003800003440c01240000120356031003100c0c003007504000803030409491352a0040b08102101104401040041240c0d010404000024070b9504d2040b0360108110003040f984505841130440010341000061000500050000903d80c030100d100510104180340d0405010240708800c80030300c019070340004650285560404129106a007140702e01510b0766041c1a800143d402032030500340c3c118480803c002c40380350441110788400c010f00f10024452a640c0f41d0090382950001d0b07405a03965403074014250f00a140c0052440700d041e101d51203c04440e03031500c034160741c000c102050380340f0390340110003070000018041c03a00c5c0c0c1c8040c02c6c620603100b841201c003400c7c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 515209163 1250 515207913 515207951
    0x1011060a060302060403080306010c06020c1b030d0c030f090315020414010c12050f130905090724051c0516180308030103080705100507080109050a0b01080615090d06 73
    0x1401680a28101c0d0620250700e400e41202c043c0e075000031907941d0340d0f218540125490160510080c001502c0428034000d001c0d8003240a90801d10015202d40c001a820000c0544030065541ca150200308102132400c0024040c440001f2114642c1c10040c00c1943d032034841500e0070817803210041c411540020107202c87c5c10900f4920800603020301e0700d50320a0717001d03075622039081803500b04140c2403010100300e11a010341140100e0b40e00101d44540c5075003a82c1d4500383d1070003800e0309a9109169024141d404101245209501d82604003900007070252003002e1603081c4e40700ea00285503806410802a11313600b10400602400b0b01403070010f00c1d0906040303444030300104012080d03109126100140c04042012a000c041603a0650380c104a220340d5440407490000e1500c0f901a41090403d406c0404100e540c03500020002c3c1201c3c1c80c42800c1c8200d9440d40803000480703000da02201d0100c3c1005011500d10304112114050842c5442806403a04070b243c40041c914044c5002c04560b407a886203000c02094440c446 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 515210413 1250 515209163 515209171
    0x4080114070806400209030613080a080408070f0c1701140f0a0213090b131407111f020405030706080702100902030c10030e010e0d0e0d11101106 64
    0x2d04410641448800100c1840d215180311941d51401240c10400b01e0030b022440d0300606000d0034612410310031a0510000c1c0d084001128401d018203070006003024130256000301c50540c00b090b1140390810014040d50415000752081d1603506050102d0000100c02c0d620300900903025031710340f4008501c0c2c64564503100d00c541d00d1140301a410710603054050a00b00e5030b090340248414108001c540d6403244200002d01071880c40c0514a080e07410002445105544041c1c8610015aa03881d2220840e14400c01921401e450310401400e600b80040c903110b02c81c1044102c00c401185c2130314100c1d0207111580c040c04180810722a465580050f040103145402c11052004041d00d041181c0645402040692526100950316108549858440045507000c1c80070459143d8001c08502406244204c020f0045c082d40030b80201d00d40c42d04000106200f0009003028407200b0a5880e03011003104241480501d80880348126850400c003618a0100e40d50700c9220841c400c419500c024460349102030300740c500480a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 515211663 1250 515210413 515210417
    0xf07050901050d020f210a060e0c0f0711101106060d05070e070c020a0308071b0302060307031113171b031902060d09150e060f1303090b0408011407 65
    0x5956941c0d07001429039440ca842c8241c01a1907038003401c0c8070f020030321070b400c1e00b04000d00e550740101252090403407105000d0141c00c04104165900c56480307510740401a5424224410207106070341c007040001000300580c0303100b500c0d10039445005601040100d1103a050b003901003190800c0f8007008400400905500103c1112200030051107501c52a8840348203004941c0e404805900250342c01d4011000e03c1c40550340500040c0d00a0340da0306050760541c02c800e5044841c0c002004c00f0894420752840d07040f06990b00106120b18507220301c0019001440c2041c980c55407020b0600203440b40c0001d07950001d004100011401c0507800c2d800d0b62144c10003540030400c1801d840710b26505030160b01c00041d44070ba5502c1070801e8041e40a03140c00059154003903980c5501d00c5a080c0101982003001c8000040c40080e19440180141d40072032021540b2018200d4410240b14150030000b60b000b0003000f005000c4c02c1c0207003040c80020303840d59090340035540315030050401c580d11070b0008050001d40540c1d50b58041154 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 515212913 1250 515211663 515211667
    0xa0b040e0d0e011b030305090a0f03090f150e040b041d0303060117010e010b0307210b03010f0b1c0c1a030402030d0e030a060f06080a03020c0306060f01090b03101208030f0705 77
    0x22113040100090940c0a400c155a640004101d40c1d02003100300070290f009560407002444514000300811781e14050403400c110341080028200010700491081c011403500c64028030300c0355a0511004145444040381e10603196002c120295103028405080d00000c0b002841d80d0b45414800542034234180f42440351900a10001000125100b1814070706441d60740600545e01d03180e02d10100c0c0c2d18a003101101c0c50031945121100d841d030407a64000e01588400350000c1c8461202d05d0042c1e4112507032494080c1e04034848170260600f940d503d50507070501920940000742c40648504480d0700584103850354a9822100000348015890100b081041d2810380d40f80c012041000180400d46450110b07034014100c5464604607a1842e00d250080c03405000240100c658034035460400a40d0303004000c00041c080d0064901091170b07801d1503110031884a9040c1c40c0d4041251130890a484c0d6030380010b160340c248621103003000c81c0b000032070700c0c0310348405002d041e2107a203130305002d4205003c2200c007800711003e000e02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 515214163 1250 515212913 515212937
    0x60503010506032a04081b030318041104270f0203010312030c022104090e0613151e06080f0d021c03060b0a080f07090503070902030a0b040e0d0e01 65
    0x240c2e60860742d0100500e007510b18600e1444d5211486450700701c1225040c01c40105012400c414002000d090b030041502c00c101c0c07121016000e05403240704046540d5200031900030a4001d50420350400c0b8501d2401400461400744e4030461044242c2c90100300940502c000c0d915041c1e03402070f82c0201c002c031742240001186154034503920a800211b08a0008052548481195a1107802404040311520a1308070f4504cd1805031020208168094094005220301e020f01801c202800065014031401728060200caa030b060700d446d50050107140c1c0e14a401400e4840c54003c03520004c0c5a268003441001c40404189a0304002c4042e04181c0d0f56038403204594009254900d00f40d0307000031041c07020081820420701c240340103001140946900d40060f10b00380c0b80050700e440c2c2242d110307424620944d4442084c0c0c003207803030b20b80089840450034450140e0550018200344551481903004642258201800203042022030300442c00b42c0f9008004800160850a011821140c001030001c290a60910b42504030303143c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 515215413 1250 515214163 515214169
    0x2100b010f141b03210405121b10060f0b0307021e0f030c03190f05040b0d0b030118060606020a1a04031b050313061403040b0901061701150605030105 66
    0x907402207908100300052500300358008081d07007243c034160002c0b64101902856a1441656580400130341170400c90850000c80898906a0031140030b158000302800e071824041c085c1c890941c2200107100914400c428040007400030400400c2c00708501c540d408654035181c0004000c55003c144d1096000d054100104120302d58007192598044000d00b100e82c0c0d242080002051419400c10f0a12006100004885508050020103402d100da20300649401c20035000c001200c5880c40c40512202081c2c02340010700c03603500310601170a01c3d45500c81c0001440f11113800040c1c01d440788030b000d601c41030b2454100402402100d00a680c09440f4030700041941d1a001d40c2e40310444650518585454010741010804140c80f54590240101c46d0011029629149042841e280d6003c4010510340d01c003000d00c00035201d0702860b214090281c5204032a411580e454588030310800004103100059581c640000c5171080c444029511503e080d0b00c00092070210102c002c07130480d05140c1102c41030200500042160795 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 515216663 1250 515215413 515215427
    0x10507030e1e030307050304050f0307050109120f0b1602281e0804180501050405010e04080c1609062322110d0c0f03140a151206050702100b01 63
    0x40301c2500c0701c00014054181c1e00650954070003899515020000e60b8405003c0000b01134000d9941c01c81e43c0030310319620ba00402d070740c80500d80700b0103002c180008410000c00072102e8184001a00070340350400c441c4000e5485080030f40c011104c101880c0c95140c0f2203101550b04101d10b026040c1d10b0882103a00c500103000c186100076103000014121036242d07413446031400400100c116800e03441010035413a00c2c0ca64080b00300d4074046985014440780b030040002194034145c004c180c1210401011841300f519161a6040d8a40c0400744103d258400c0d45160b000810340c0341ea80c04000e0217a440000b075210300300000586058280d115110002440024082c42d90359400507408552614290292450822a440402030050485601c032003e80c007040003450300f42da41c0c200001140c0103658400d80340000c0d22058003118081511100c13050315010006442c0200c2c0d5111074031040c550b600d000c0b071003540c1d0300c0494141d075041d5030b01b2111a52144180111160100000f82c101030310a0000e01609140c40002082c075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 515217913 1250 515216663 515216687
    0x506010e030c0d1403130314121803010b220606140a082a04030b011e150c02131a0907050a0e010507081603080a0b0904060b01031b1d01050703 63
    0x542c44505000c1d04004004040c2e00c00c4403025805d403919206101400a044001c0d031100ba641c2480d040681650b580c4007141c00c805021070101c043d4144000c1c50900d1118014458403a0341542d40d40541c5c110302d60380d0307601011812551908a080185012280c141562003d902c04014404940000c0851020180a9528000c81031070000e0aa40e0b800e90036010005c80340040000d41c0200c200380c00398620304500240700740c90040c0c24040070b41c5d0740c41c0008114000c9007034928910118040b010705c06e02041c0944501007220a1a0400c807084007a00012040d80c04100340891243d0342e51100356010a09045c01c90302e420007100c0070903a82c40d241e480644a841403400c0e90b02042502c001c4100c5981c02101034403841c5811655035501c07500d0691840c076081d050448294040740354440000c1110f9060700074100c081401030b01ca41c0b4192943d07510400907000b00014181855200e0785079900b080721003803451142c041541c1c0e4051940c401c2051400b400d030450703003100d81003240411440c00032a800c10318040b65 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 515219163 1250 515217913 515217919
    0x50a03032702040c180608090d080105091602030f12060a060c02010807181a0c070806070e0d0c0e160f030b0904021905120c1c03210207080703120506010e030c 70
    0x66042200012120501c120040a505e001450380100344140e02c005214802c480c14000c81d0140d5641c0c802c29100b802c0700b441000e5100b12854000341d580c4010400c504184410303070044034142040c6952040c200c0c5c10143c0c18013004020704080001e10f24003803054200a003aa810a500124042c1c1c000038003001004065000703000d516000010234a400310f020300020301e1080ca205401d10007070442d14115a201c4040d080ca6442480000300d4154404145035004000a84400c40c402c2c00c500d0a10408580c0c42c80182c0c1c40d9841188005070b050346d081c1100344603841e41c14000d2241710711100041c0c10a2444090030040605d46090818541c64043c94140c10540444080d8000c1c00440809050400380750403003500100048280740e0341100006903c5451007040b10b48101c11200309040c4603041c442e034500074000484801b00c0c1e081d81c030b61f120304900c0007151568003d4540074094880a0450344005c00031400983e048401e81c518407940c0c40344640145003441d0480048145100080d5502c0301040300c0d82c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 515220413 1250 515219163 515219171
    0x120c071419050c010815120106090905030c190c050609030f0109080a11210c0304030804140a0603090b01090c12090b0f062407061107050a0303270204 66
    0x4240091624104000c041010486107054078802407605801c204041c12101441032080005203907000390401446400300703180c01e141a070803940400441c0328211802240715503031204045200d0501d03000b44c0c01810301500080d50341318041c0b03250710f280c02c810707003030000ca12058200c40600240e40100c80d0750840e54203c848588600c4404c000a082ca4071b940c110700500c1d0700c1e185c542c500300107d01000e460804200d4032aa854040cc41201c2c5880d21101107090780c07985804103901d00945640300c00f030304a610941c41100d01b415100e9691140d10790282d00320280350070006000301c3e132a280c00070b818800380c056840c0911000b9200d65601da41c07a141230142c45c4000e912008410005842a103c800380b02002c00c81c01d0020515a0814607000401039440001c0c103085540002e503c2e0510382c6142145c05003101c4c082d6840d1100312110078081d001000110b0f00c054490302900e280040b5140901030107401100581450091440d014003202c41c0380092450101c1e0f03412a000c00456410710b450304c0b07940c040e5400b02d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 515221663 1250 515220413 515220427
    0x50c011716050a26040b060a030f0f060b0a030b0406050c0c1903180f0f08010227010e060c010c0e030c0f040b0607050d0c110901210201031103070e0f0402120c 70
    0x103216400e0f40c202d03610422040c04c80a603400e40d00001100c0c080c0d8000c4000c04a01e072907400520542d400c1500028000c502824150350005102c40d80140245014090024081003190001400e40f21241d10a07180882c0403001c0c4001d200710b92060940008900b07074541d1400619211507520340d103080b144a103840040c0882241490f025902e00582d032401014560b500716141c6a002d1110a41f5000c1da400c0c8000c0785401203184801482146d00000e211043c1081207841401c0c49030651030f03080e21b2785041140c01d00200300e4a4075680b018000d4142e500c2d00114100100c250020301040700d401c1000d100742d1241c00c1450310790f15807401c4152150029180482c982451502060b100e00c60010020060b200d103100c10302d01a0760110120700b10b10304c1034110340c3c2c400d9412130400034048401c2c01421406003100050742c6048002c680690203452040c103000c1040828118800e240380c1084a00c000800e0010900444601d000c840910015508a5046051145405014000742c41c010040342d0890000503030a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 515222913 1250 515221663 515221667
    0x40b061207050a121707031713050a0303050609060109060522123e0d11040603032a0507050f190801140f130204020d0e0a050c011716050a 61
    0x3a401601e0b0242a000c200d66581442040380010040d05468100000c0b20082045410004441c02141c1680e07031880120011011070784881c5001d000811610300d41c00724000041c1e02480b0f2001c0c0b5500070b403800925403a00000340064181c0040c401410440c4559044c0211074006065403201c0c05e0044507003080ea48600b0030300f148902240c10001e20300e02c3c0303d004081040071805050681444540a00b080e010f20780d8404900c241ea4000c1910084500c000702c44040c0c10b00b100500c2000780200c5d48560320b50702041c0800c0407944e40741c0003540010480744a8403101080c1000b01e160400000380d2440030020b81c0c1c0c40d81d03501c8408030701a1f0380c40b402200c55510740a42d9243ea003031761280801804070074200c0d5140c005a000b001c031b101c00b1402550310302300041c0c5808241c040062150f010f240c40201101c001e41d0030040203511640102e04800d941d90302100c80c04400f040141d40042c441d2008280c4e90b00c03814009420120382c0440e8540841c0100104000300e54a010040302c40c00050502940326140e200d81 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 515224163 1250 515222913 515222923
    0xf1917031e0a060f0f0303090b0309210409090b0f0c07150c02030405060f120606071e1b06050414060412170d020a0216090513020105071a0f0906090105040b0612 71
    0x1284d00b0070b41c5031901c0415508944584081200c0c4240c9402c4005540c032840200c6502044500040c60380014403980b49060045e940110700c4400d4000d854501038860a082049038908202a41c05c49124800c2044c0621585051a080a900300c20582051616594550b500081030501d100c80da03190507000b8030190082040c0c13005040b008001c80c2e12a000e041086882d900002800100c072912840450901d00341081141e1850b0b4010b012001000c400e201d11010310019104211170b03c8003580300400d440941b0483c0103001e0f040701d030346440d541d074601b107400400180020030040c46240204001c00810701074490050f080d03644490300d0240d45252003100c0109000700c9040c49125800042c84610055000c11114400d07034500c4003101c1007948911b4204d080300c80468154550480c80840040903600850244c1b400521031000401f184020403a4802004802c4d280303480c1d60b01041060040a050600c04603502101d428002c10140c546611105030300d000c003500860003001034800c240ea00100c10301c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 515225413 1250 515224163 515224169
    0x6140d0c0302100f03150b04060f090b0417060f0105030a12050f03010f030b0f07020d050705010f061d0c0c031803031603020304090c050f09040209030f1917031e0a06 73
    0x400320000280c4a04040c0160700c4d110b00d003000192611010f458454844481241a00c2c1c0c0050f8031401c0c01c2c2054401da1f4840d0300c00503100b090200d2880d000403d50160f200500103005500000b08456244a00d00751800d130015194042588020740107025507100007503250409a04030a02c10840c928504003907a00348a50300700100c001c0d100200208a2a00c90400c0c00d040360320951500c16a50707212220141660f01c280d8a050060704592000e0400e1031241c009000741e94040d4000040c0010100b925030100e40c2e095001d0b028280540c8041c2052024a105036640a0f200d42a00d40c030780741805103455143d10400c5944d011145002e01c2c2030606071000c00a94130316240c49040040f841000f4180a035480c0c1040c03180803149801d00380318041c40c83c41a030a4400590782c4000c16800c002803c3c2c03c000c00381d00800d42554151240300c9040c3c0c02d50b0b004000c1401941e00c4010000c4400b8510f040c000203400c8078000d03400039000100140030070b000c1c05203446401ca689219148a107501d4640020303005d00305983c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 515226663 1250 515225413 515225419
    0x120708070609230d0c0e0f07051309201306020f0a03020304050613080307050c030d020c0a050d170d020702040605040506010503180f0a032712240e0109020907020106140d0c0302 78
    0xa0000c5072039007581d40002c2c02555040394207e46130b65503000c21185440364000490030704074520f40030000d46001d038210040c3c100240419491202c1180303400b00c4160422007210f5071446d40200c04020483d010f2210020b5501040d020701803d1004d0388000e035980c0b01e140700700782c09014002816402440e0707503200c85000d0308200007900d98460840c101f055071442c04a5045101e40211010a803c060000441810303a0030068003d40c1c40910740020401c10240c100019a0700002c000c16010310300381080c00612161040c0d800c01a180d80d29030040c0012180950056030041c3d28080c1170109684e00101a280d01410546110380000082c3c0c1c58181440c400c92854040380c0b00341da2001d4105038110b01c03c20181c8103400000700340c4030796048850701411564815103e4000c0c40180540c08030303040803002c2114050400e241800d03040e0030390615044440c1c2041002c50380c0d5452042000318034145020f10340017402440288074880c02c10791400c12944c900c4040b284181d03070307113511101007164807081d80008540007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 515227913 1250 515226663 515226683
    0x80f0f040311030106171e030c0601030c030302210d0203130506010909020922031409090709080d080708070f0c1221180818120708070609230d 63
    0x707180400501801c0c007421803181d404d081c00842d60303080d001c0305186ca0707500c81c00081c0485071203226100301d6080e041c80d040056010810000038056810442c840c0214802d480c072040317041c5542002410003601c25402007003200f94581483c444500042590001e4a4158005a890715900307620810104a0180180785001e07000c000282c8011f280c3c002401507000b5611400c00f607440c4c0c814036510204588503010b803c400402c015000c64070a001d511718403212907122610b4165031000098201034200d03030003000070707184000620040106001c076260540060900341090b0130140e1019000d14001400e860030811001000100548110354640340c46401ca131400c6840e0401050040c00344040000720000341c2d4610f1130b4180340303280c2c51003918039540011a4010764070307589a0310000711b580300404655201c40c12051440260741d030030301d1050703054030700c0b0008010013458107234040d00302034099100c0d5050000d216020052544482288841c040299490b819002d061600003084800c02c0d010251080540c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 515229163 1250 515227913 515227919
    0x2030324010c0f05060a0e010204180b1318140d080f0a092f03030406020c041505040513030306140906041d0303090a060510030f150f020a0e0f090f0103080f0f04 71
    0x5c0354060050001410900c0021079030300d0000d0a034810781c0b1410364103813601c0c0382c02c102c50301070740e480080c080000416102e440a0109040e100360b42c0c0c80e8100310090240e0f82000410081c05402c04282041c042003e070120900c2268041c20002c401800002e01d6104000004d09a0407294000654507500c50400490719070326002c2050111140002c04404c2100503086201c0c07460000b0507501100c0856000b007406c1c840714030500003c4d1031090710031000465503110100d10b0740c1c2c070350190394851040c80d0000c211002080c10300409880c11980700309400b64440300407074425201c001c2100c0e4407000c00e441c089641d8818000318524108500d402c2d60701d6004c08401e000c006400881c000d504a070180c038003400170b5124001300302c0b07501c0024880108440f08101300800000d00980e00d07a1411008020b0000d0390303907003041408080e03030700008009001402c00c030030284462410502c042d401000136624803040e407410038041d65041d54180800f038514000454082160807071001151f501204c00b1301e2071612699 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 515230413 1250 515229163 515229173
    0x206031302011b110f0402031009090503070f05030711040b0a0509040f0c0b0307030c0509090a0e0f03040b0405030f070b0304030809070315020c0606040506010e0d0302010b1509030d02030324010c0f 87
    0x342e10000c0c24070a8010707000340a179600e854029a800b82d82150240d00f5010b2500c2070f800014070426004460714001030001d00082040b40e402c4080c4640160042c42d911038483c03902e403596540780200103200c3c40c40c0c81c50412850f140e80e1121010f50f0403d85060700b440e1943d00f800410a100d5880007092058104030100c0c0003001c01015600885584e281404010b2040c40d05482a00910b8025504101c025001030030401c0305d50001c00b420301780c0e4000c3c3d07076040400d60f440500759030084d00035446800d00000c0c00c10641c01e0800031141443e4031403001d824141e0a2140b0340655200262015080029090220305155020b0028400656010910300d880ca508004801c010790040013044069008150006103a03040c02d000e8948034000581d070302d032403040c1040208040800c6440c03045c0e0441d075940d413800d9082d072951229032155583d031054076034441c0c2621042602c0c1010048141e01190018401d105000608000340c822a01084200541c0141c0d00c01c01207500c401e482101603d101c4040141d002400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 515231663 1250 515230413 515230433
    0x130603170403030f090e070503130c08013e090316060c060b0d05070e0a112d1c020304080f0d060e06030c13050a0e10020310050d0206031302011b 64
    0x83d1190f00c2d200b410211071a8280c1d5151900e20a0100e40e042c18000199a5489100250344c0808802002c0c40d00c5001901c4180102d00f454100c500b0b140c1d90b07264100c3c0201403881c03600c3c540c11825001b103040c1d80c04181e014121440b0402620307100040102c1c001e40169410701200d04c2009200030009160b40c0e50b168020f14440846200b1340b1317110300e010b484500a0415905805803290004c0007000c0092601484035188000200316a440c40e07601c9902d403070184030000003812259846440d0003001e050a800910300781494901c5449002c00c200f14950409080c41c54941c1d800601c1d01c0010307183c0e42c3d0350401c10300600c96202801020703000045c440c00c8c8800310f54040303801d449808408032465a603580c1459942c100b90080f00d41d0100801c4801044d588140d08500c1d8402c4116001040c400f00e0307400c0322890300c1e41301800300c405a5008800c004280110801c114000e010458030000b4440058011440038071025040d04c078014031b550344203402c1d6400340903150300760100700c151001030141c182465602d007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 515232913 1250 515231663 515231669
    0x503070b0106140405010206040b07030f0606080907080c030601091a0603040609060f061a130509090d0e04110a0804030212040b12060301020309071509081e010e01060e061306031704 80
    0xf150842003020344040c9600309603002d841c4103800914580e140c0d9110f0410300f0000034844001c0503103402000340880418021940181844d46400c03102d0b00300764078803a040502c280c0041c0310541c0012744100403913600052150459071b0800300000c1100e4245d600780c0c4046104003c0640000b000000d01040125603401104454010002000881d45104048003a1420752040906400c1c90300201487c15070510000c145600062404006003270b03440d0302080c0b040d0000c40b41022287c100b24100e89070300b40c200300c044000c0b403c100c404200b90352010029900d240140102c003002c011001c00000d003054000c002d00007a9000d105c20943d09c83d9650f400f0540d055201d82c03500360340d418601000c94180c1c1414000e0700d00072070031034018010880c01d01c6c2ca01c00c06c00c882c0d000240d041000c02000092210414800000c03410303019200c0c4450034044001c440e0139550f0564001a03203a141500030051410350740c540325040102103a4a0016000421100018180f240c1001d81041c201a4041c0c0710420700100900032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 515234163 1250 515232913 515232917
    0x405100c090518070801090b03010e011112010816030b0c1215040f05040206040504110708030c0d0501051f0503070917031306090f0608070318030216050a061707020a0503070b0106 79
    0x2c50f400d2a14007071907624054030814007042409005010241540d004400385010160001480c071210000e030380e003903420726142500b80c59000510010f01c00040f01c2d10300e014201e06002031006030000380c60604a42a1448064901007907240850014094072040303a070280300c0135064440c9400d1644400450721000b500c4940f10f00d20b840820b030a039100038010741c0c0c81113030000d09640c2401e10b8001808082d0008000c9203600712802c2100314002510b50f07020314006e0f440c2244494a0315052481482103034010f0f001325115000e90201100400560344404c45000181c6c0703000c07a102d40300c2c8101500d444145411501ca800d1f0409a28400f000001020f44496048850b47e19032660340d510342551445114028004000078110302400840e002e0b1015a800c9545842e0010721001d42d01c100344505591202d0440050308061030340c0c2500c140103400358000e03201c00c0307800e94025440c10034082e00320b10444c04016151560710300003d802c94000d000c6024101d40200a03aa507584280c542441301032000d000d5200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 515235413 1250 515234163 515234179
    0x170405030d080108100b0603010302150405280b0f1602010915210209010516051207051606020d021b03100c0f0305070912030305040c05030106090e19030206040b0405100c0905 77
    0x2c1e142054041c2c046d02c07010161206d45544d085800344100c00041c00748641c84010f080000080360348441e01d02d00d0304841e4a400200740803000c20300c0b10b4103070a040e43c040024400b05102c0c03060f07102c040c44101d540b540d84294110218050910040e103001107554025181c05204100c3d0300365040e04500481c4ca802101e000f060060903d0107100c000b02c0c0180c1c007145001680601800b1004080c64040804460203201281d64001c45c40c50001e10030340c4200c4040f036460304210035154481070b0000003c000f51000d400603005421140c0002581d603c0800d040340111010086564020307241480b01807242c0c80d410f4030034403641d803800f14090101c00541c4541000a49444001a6154407890700b041c240c0d21070036405c1c4448034080e01e007200034040241042e5050917040e90000784a58007482071200800105e0300110701841103411180c2041c6841013420852005082c3c01d80c0065808a00c95900c25801601c0e0112501c4a0030040d14100d00075810380e200c14a030002030050b10760072103948412a5001c4840310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 515236663 1250 515235413 515235433
    0x306031e03130e070905060a050409020301061e020c150a140a02030310060507080d0506061605160608090309220603051606020a0b0c0f070507030b040314030c07170405030d080108 79
    0x55000c0f040f039284000541d5640107010920f0304400074800e890302c0380751690034152a0074504080b82d00070b074000c1021410342c1e8074071801c15600f0341d420311050303d00340050021404e5000202e034a8040b9101d80a98413000020340d9038100340a400b0a0440c80f00c41c0807000d890f81c50000c0045d40c1c0340d05c2a0b400d9000c64142c4070000444511410484540d603512600e42420101c0710820540541006010540d01050070b100304181c00040f12589d09200d80100020700c08911580115a85140a5000301080001e403404008590000000b04d03a5115030554031480104c60000641005002c06002c40311100e0510b500002403100005803a03003400c00200360a400960f5404003030781d480c01c0c1e01c00004e00718003900d000160504401d002a10b104400e80d83c2c0c03580340103815070790f450030a9100e410842d450000ba005100a0603804905004e150b58014005403131030400c240140a98001da0500520004c070239800030007401d6082c426203008100150403280c0f185000c0c100074007400802d0181704c14038452501d01c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 515237913 1250 515236663 515236679
    0xf060a141006021c0c1505010f0902130b070302071d09010b010804030e100e0a03050708060718120c0b070f0b151012061730030604020306031e0313 65
    0x11908441c807640081542900048201c001d07404500694414000002c805c00f010894030f0220340314900381d29100086640c1401c0c4400c0c01c06080b5005040014418811801c505582c6030b410000c1d40c130300d042103a89500192074220310f081d040e50410355151003070351380518140b8843c00e2640d01400d0100000e1140f200100c00448962804480240001c2e4038048900500d040001c5000380310f294030319020030346000c51408104020915841140c036503005050030000c4040501030b154002c4d0641c507150320252031040448a0301c84082c0588913400d440c00c0360380810007800f0100300000f0310301030f0f03100c9403100914109650b002100d1f00058464507030200005d0865180d403ca00001500e005210003045160382c0720495403c03451442000340d99a5808012542c0048890364000407141100148a0020160341c1800c0e0940900b03107a50034400130380c41851405e0800c40070750b544080207440040c1c480c1d4903400000d141c41d04001829141d198004a00c41c0080130220003881c401854803c0c0d0f050684e038894003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 515239163 1250 515237913 515237941
    0x30c0709110702060d0b0a0308160b090a0305031801180c0e0a0b0306010b18040608011b050406170903310b070209071b05160e090309130e0f060a14 65
    0xb90b01c1300040000490942c03065119414600d0081c004000090312561044469030000d00c61491038a4085002810007030342c001d1003541f080d0b0380c1c80038001c400007590380a0a98040641080c00c1c000b14001240c4000030b09500c0b4207100583c2000c40c080410890a0441e400744980c015980745410000c002566a050ba00603880049005401004180e18041c0f0790059034220000041c8440c20007840e01c81560381c1e50080901800020000150171590603816828051000101ea1b06014060001700101c1e50080c2040f04064a0b000c02c800417603882032411810751089904c20035018450a0301c84a1525000f1007070101c002d0080400c0d58003984403245288103004100009512a118100103105144190b1101c90940c7e0001242c002e01d1170700759240d41c02d1000080b8940980c00000d141000ba15441094058105500f800514038042c00b0a0104243d0050b20211190241d220421202088010402004c42d100b42c1415a04c130750900411200c00b81406454080e08000a8030107e1414116485 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 515240413 1250 515239163 515239177
    0x1b0320190c061b060e0c1207141c0633080f0708061f050d05031c0203090616180f030c0b031608041704080606090114030c01140c030c070911 62
    0x142c211030a400d070f959144c0141030031541c01500d5002d01411000c046d111280720f070100e14181000380c40d10508141c02c16002c08968240785104030305144403141d4100c41c08603512140c0d40c0184010a003c0d511395810300c041d6042d0201101d10180c105444050000c048010348140c0780da54007510810041c1c075009c3e560b502050301030307603c041d0000fa010800e103c0d0b03030714034008000301c86404200c211561303a000500c02510041d419a201c1e0800150081c0e0b03000302e026074030085203000a003103080d410300c1d528607a0340b501c0c0144014400720314072400b414994042c00c41c8a40741500e002c107651400d601d0b000304e4901e00c9120310003250950340d0660041050820740c020b50344240c010149800000180d0203040301c9119019000b516514480a01e1141c402c0d80e010040018040d03400081c402400c080c3e00f403040c1820140d0164001c0b21032030112104a503408101d0322650942481d2450004c10148458035462007101720340d80e07140c48001a45619001c01140a83c00c0b501510000c0284000c00381d045801403040311 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 515241663 1250 515240413 515240447
    0x7020a0509190f0f020a1e081b0a201f110f0318101a1009170705040c08090d080903040308071b0b0301080d1b0320190c06 54
    0x19142c160800c0e9544102078403101040c012600c9144400500100d0384000c50320000100800240038103807148141c01050b40701a480c1c2000c0500c2c1481091710703804103c006a283c41580000c00c03940701c5104040c01d945202d0b980c0d400d00200d49190740f01c2e559502c0c00049140b1140c2c8c000d10800f5141381c66105540102d815000007500c2c102c1c00d0030212160fa0700080140841500f84400000342c614100190710660310200c4002980d5881c900c0e00c0d0f2009074800f21600c1c400e20740001540e0f140c96009030400c080750030500303030844041078424001d400c044994000a401518100c0c0d000d280769402022070f405001c1e00810780e03040300038284085031541d000300c60f0364107154001c000c104006842c0d10004c11103280903070800b83c4540d450030312802d01e40b030310742d840b15840340e00101c014030982c0c1c000d00c4070f0841c0402604200c40328a8403083d002c00d03001004100a014444005800c00118040a0420800030344450584075961880c00303030010410380c408030607a0140d2031240d01003140781c066058000490000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 515242913 1250 515241663 515241691
    0x1020705061305030705060f18011a010f050c190b0601020a0c0509040609051501030512070506190b09010305010c0305010f050d060c020102090a090b120c010c0803091c0507020a0509 80
    0xa0010360324401002e400c580a100810281c00800d60511101d030080204140000d180c1c1800c108060003403421804000d1140d1511643c1c0c0e602c84504000c08040742c0d070030b08004042c508010015185800b0305510304046000e5a800282e440c1124502c08403941d1003810010840c0e04c074100120790351103a400005001d8802c4640500c024071f400e020540c7e00512072003010404819603a10f45007003009081e40c6441640400c0c00520411200f4018019015865240c042c02c07e061502d5495541d83c0240241c00c036100c0078003010042b070000d40c1088802c008050130907400d0396580c0c40e025009115500314400041d242600210310040321858490444070b0082c48000d01e00340a4984400401500c0b50840c195075003044070f6032040d11208003050040c8004180011850468424407902204070b0400751380b1600610880303100d40e03810240d176030480b40e000f040b6141c407951600002850100d401850341040202c040e652003410740d000e00104261032080c1c600384099aa10b40600074490f2040d50703d1181d803410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 515244163 1250 515242913 515242921
    0x1150f0e0c031b1602090105120304050906060c010204060203040e060901050d0201050a0e03121b120403080c0a051009140609191a01090207031e090513090b0c19020102070506 77
    0x345201950704041401e401030821803c840d200c00c05036200003500480100b00c1c0c9078403015441d10200e440e00603d42955540c4e22108280c0301d0310344034803d41c01928420b100d4000030038000d46960080c2c0c0c0c0081c2c184002107560710346481c000780d1f680d002449401f883d00420000592141800200c2e40c5c1240c801500424000455500540315030f0001da200004100310b881160b1015501044003d842584000c2d2891769071421840c01140407400140c4664550b218004038541e0005440c11102241c1d0410142921100301c240d11038204180d94201a20324403840c00750096003d12035010394503045c4100100b2040c00301800c1e0707050700e62600b00c03403022050708006209c11043c0d030304540605078140b0503080201058030140c440c1040000c00c0e000803102650215a031020560440c2000e0000d11001c0800000c0c0205904000c1000d401801614010500402d40a10307020f815040029845e03403040c40308200d0301e480020340e0480d03001a4694915510401c15500703099006208865509400801401c0c440e56 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 515245413 1250 515244163 515244181
    0x5120402040b04050721052203020f030a0207051206060d03050d0207080414040510030b010b0f04050d12031503030c02090402180f0610050c0d12110c01150f0e 70
    0x401081030740c000c1e03181c0c000812580c1d036a1050354418400358031600f114003154481c001e800300792a8000c82c10149841c0500c69202e00018071740385444503051414101080313031f107422410002d54011003a083c1c80040360744a81d071600400d85d0700075650150368911452003803580540d503d80c01651001d4101c201d80030380401284c480d0008050b0042c00c010007500c1c109003a61592001d5119078400b080760121034910400c0b514103801482d80040c1d0b41081c0c00d41d50341c00d50b00d4992202d041071180360340c22540040c0307500b07001c0f03181026100140401440c010a240c020304048020000c00703001d100003c2d24042c0c003187c40c1c1c49901d110105883c0c0690390310304c00c01035580c00e1201590018200b6a4015200e0a0b4401704801e4891401c0c40342a00701ca54a0460034510280b0101d8054604c0c400184082030120143c02c110010340b64090074800c1c54071100c1070a641406400810101c1420400000d0000d21204c10b0901500700107680880b10301c28240c91640c5400c1044894541c1c080d0700d220a09401c04115110 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 515246663 1250 515245413 515245447
    0x806040906230414030304150507032702010807080702030406031d1603050606040603030e04050622060609091503021e0d060e010f05270c090702060609070e0105 71
    0xe2048000181e030398550a10100d2820058007000d2481d820350b4200420803071030800c0307144102e15850046003141803540d59220312002d002e0700c0d0b0880036075500c00142418404d8101414038100315608641848051000140c0c00c0050a011b0340455100700210b10f41600c02c0d000d20780300b8520340e4051400c0601740b0034100c01401446d40c82110901c074030f21150711840000d100d030040c544841e1030150900780c55441e01900700240148194801c5151445c00c0001c241c001881c200c0c507590480c0c00007269070b1150300003844209000c0c0d000000005650b4a88040e404541c0584c3c01c0d10750f00c0c1c60b8100919038590a4006540216210740c3d072156071003100b08010300700f500e07691059113040003808002c0c0c1c40400101d1840d4500c010181c842680741c80c0b103d9a14075080c8103442c0e040524000600040ca00310f071070801c00c40300c07200342a810031045e0115000202c80620a40c4021940108110480c2c1082c5c0e000a50700c140a4910340e210b882448003145540e4007030f40c000844420182c40d594140f04d04400450300ba6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 515247913 1250 515246663 515246681
    0xb0c1303061508071202090103060506031006060809101517190602090901140906060903010b06030c0d0501060c05060123060a03091e05062703070b0402150a080604 72
    0x240400180480010114024088103040c0c901c46410701d24505030f281843d01401d0b43c40b4844c07182c600503920000d42c03140c140d10b0341581c1c1c01c050b02081686500c00400e1511100f4114050454034150001c1041036200c014a80145000c1c0201d4000005680018044803912400b141c40b0410810003089004410848010310411080950b002880c0b5441a949101040d001c211101c0c0c3e8002800c660a140042a46000d0600c2460704942c1b0480c0d000802c04080010302510320405021812a00580d025046000300302d201500054680c10069101d2506421103115060854103040021070041c0c8030305840c00049400070300501c86039203421000c040c0721402540c45003901d00f64100341c14640d03d0b901c00030b2002c4c081d50380d000100e660850a1406a00111200c0300498002d25805600800d01c0019010707000048580c0899a580420710210300300c0404040060640c0000700c0c80741d051242c01c10015124900a81c1d007060801c010880105092168041c00c3c004540c035140410f216080c10741c03140f021 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 515249163 1250 515247913 515247937
    0x905060d0b0a150504140d0b0f01090c03050601020c120304090c090512060702100b03070f03030519050301050a03080d15030b0405070b0f0a0e012304080c040c02030702091906060504031a01030b0c 86
    0x40b0844d23900c1d0502103110480382d050801841600400c44800c05118504030341c07000c6e190404c10341c200000001e49401d078900d0114803074a103a00315684840014011a001094014002c115840308020b01501d0b11750280310346071241400e4040102d4140f0046003240c41a0001e0340a4010342c1401c0a11000408841c01c80c2500740c414140003054082c8203205450180d4060f855107078442141140302a042c01028114100f005401d000402242d02c070740410700e054961260600d6184c041d02085500106541d00314030b000803912481c00401c2c0090b1244e214055070240042e18500c50319a40480100e2040000c2c031036500b5003c2000400940c840c0840f00aa14414036050748244e8261003604c0740e2030102049108500780000701044000c0301041002d91081c0d0648040c011a4050540652640200340d0081c3c00f4107407110024030803507440006036000c0c05000a04006094903030f4070042c00c5030043d000868807194107218410115402d0000b00303040360391180380794105958809040b003403600300d01c4500b01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 515250413 1250 515249163 515249179
    0xf0304080708030705180307050a060c15060f1a0301050105030a050c1605030406170c03071103131d060915041107051c080601141204030905060d0b0a15050414 70
    0x40020200b80046014070b60303583e5540d854036119480045404c00d5054854866441544100f000d9119090800e04565203424a80620f00321410140400002000150100c601c0c1074000329a0321010449072080d110000c040300c45a10802002c4031840c802805480d021075400e000180388508542c10283e403000d488185582802c80c0c00c00c072030b200101c000c8000c42e46500f02280600c60350f603100050000c80c060041a04e0340ea4100340042c11814071025040d0740400c45c039000e1a42003010100100d4038040414000e8524042c3e58500c440602001180412000050a00442d4161400340946401050325410300801002184200002444001107032401043d040c451b9001041d01405052902404191440031041240ea0010201c00b401800c00381401084070001c5101219503050355629880d500700e5088a840742d04041e50545841d41c09642c0c08940001c10406080440d040050a601c003654a860481c0c0c07a00030304642c102d02504407c00158082c4001c21841451291004540138080c00402e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 515251663 1250 515250413 515250427
    0x19030509030a06061e06120b2206090f0b1f02070f0915060201090b070c030e090103080c0d1b02090a020403020301110a0f051e0a09170a061503080f030408 68
    0x10b410600590b40540382166240c00030001e814030101c100e10441a030200c44440a428400086c10300d00018078074064260303481d5a80c0c00e290b2180c41500504003030b0448000c010241200054026050901448031000d00707081441c40304440070300a40380d0038100200b090300303c0b40c1400c4814002145458034241144540000043d030001e00200e140040c00c000030012880c0c0044210001c083c1d50240d0200c021a032400c242540820164200c26801c40c0c480c1c580803206d05040d0908403a10300080754100e80c0460000700000800064000030280ca5184100b940c5400122202c1a680a085050f6502d0380300d03141c1102e440103160044009034003074a8100010705040d1071f030f0042030840b003810320345440d02c0c000003420454148d009001d03086c1c7c80d03d013458441d14140a501001d0403811083c810b000c41000003140b076213421030188034a8006408842400c110440c05c091000b41c2e5210641d005a65039450410b0000b82c1913281207100301540d8120010714608820318280500d076074402841618220005e000d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 515252913 1250 515251663 515251669
    0xa0609290a031208071e0917030f071b1e03120c05100c18060801051509060d0b04241e08070b0906070f030903030306080d09050910081507080903030919030509 70
    0x20350400341d0700c0e07601d1f200e42600740711041c52002a8110482000c0d4014040c00004003290380440d00c469902040340d100f04c481d402e1001118030802d4000b0342c4075142c12182010b9440c402042c40089901401080181035040c1d501a102e0840c0c1d0705000d0310b25007190501030004601c6405c8140c0d81d011030700e094003851400b1081c4032520101c90f0012400141148010011440d040e448180007401d030714606480c0450307101c00aa0184591201c181c40c90340c03511a4100740755959407083c00d5099030310150900000306084041c085c2162800340c8611007200308540202c08500d1825181950782c2400204441d5080002c1c8010076000b01507120b5021004004400009400071b81c0220180d2284d2201b0120500750f180103400e54069812068241e805980015880c941c40301199040b9281601e00e0aa55118a40d01e82c90b5155150080c030560312400b120744011540c04941188129207135036840d45c2c1c0e91904100b041d01d911055803020a16404604084107481030307100d06103821482414540d20b002c1141c008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 515254163 1250 515252913 515252957
    0x41103070f080a06060501050307020a0f0f14010c121a09040807021203040806130b060409080d02040f172e0204090618141e0a0609290a03120807 64
    0x48180b641d00800f24500070002240a001c0250909080241c00c41c030300203400944d11103807040040c1c1007401c07030650341043c480790206404035076802003030175040c464101110034040d00f004c0c90f080002603030800b0309428415261185a40f40d250840c080d0078005415010442c003010040e00950350302404200303620041e5218070072403501400040141d5102d901c0d210140e030800074014412010000c40c042c15600141a803007000e40d0240301200d000400301810300f4002458040d40b42291034191000602160880c1441d100600f03c9680408202003200c06c0c9102d10744581d02206480d07201d141c42001c4034481802071081072102c850902d0010708085e940c030710245c10b48c1c050380e01c1600c181d01d040820000260300c0e03001e11081103110060b000d4441c149007514400d5280e0100100c00c0840340e540100c0c1e914542900400c004002100c01440002000100d10014020b40080d4074040c488041010010782040c50310841180d810a85a85510410060a07a407089000309500e081041403002c200142c2e400080c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 515255413 1250 515254163 515254169
    0x80c0a03080c0316030206011d0103030f0315051009090b270a0207080a0c230d030f090c08010501060810030203070e060d0609030e0a1a040501050717031f090207030206041103070f 79
    0x4010215940340144000c2700c01c2d02442402a0128840014008260071a9600d8100c94441c40c0000d05c61007000300545101040b40c0141e54400c403643c40505c1d03540c1e8000052000e0f1100c00d4003c10000c40d174070b010403a40340780c54245094050750b4407078041c3c04012080304856114402410161600301e481e0fa5030f84082d031002501d200450060b4003c4028010275441240100c0010a0009a84003003116815079030047c5c1092a000c0503105c42840076001c189401c585800307a4030401100340507454920080c0600401d002c5d0300e00295052000501c21080300d140b080480b60050060b210311401c10005101480c0002d04254100324288045c40001d0810300c68906014007070365030071520010310810458040041c1c0d201e403403d042a0990746001081201c01c960440d442400c0031703640c0365510300d000d41201e00d481c020100790100110130020381451007030450441081012500d12565222680c01e0101d006440340907005038401d40000d000030b00940c1c404840f0710002012611900d58032000d881403554150 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 515256663 1250 515255413 515255417
    0x1503090c180c140711090c0403140c0103110a0801030f03090b12040b181203040203010e030a0c0501060611031e040906140f031c050703050f160c080c0a03080c031603 73
    0x140b100091540c0040501a0290080c411a142407160b4036200014401a655148642420300100e400742d2500003c650045074411480c02c0230b6031a0011094450300320480b9540801d08241510f009942030000300d44c1c00c0015a00c4150469085442d00d86034445c40c50782c00c0707007441684000821484a8540034009110089403d01c01c14601454081202000580000c009842200c400410581c0110780a0440c0e064245400d84075a124000a805098603000d1a102c0b80000501c1885140d40700e1544140ca902800c000d00c40a0390b40c1e0000c03607035018070166480040c1c10a2007080c4000c0c2d001294800d2030605980c4260400381c50b490b1000c11200d103544624a0594548010310f000d040c41822460031803c11805000904580030b19215403c400380380300703010094001f800104150203402038607071900c003240782a9201c3d210a20f00842c030110400050b00c01041401d400944030303800203018084040050007002416156a840d50b540d40c204440c407080782c4c0801e0101100040d030010340c080402d0301076 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 515257913 1250 515256663 515256671
    0x5190212070311040812030a11032a030408030a0c11060a090c231215040f1506150e130f020702090c0403020609060d09050609061801061503090c18 65
    0x712101808403034007140080d81c0600203000403c4600070100b0030b600c0d410000f400301c075681c0d0380d9203502d640101110368200201d0b44000c401c1c07010344078100c44c013107030380c10342022002100e0084442c0203d007602007228010300e070784010000a032000916800c1518010403030300307203100f441c40e9034800e4500782042100e001881030b03610080841032200380c0e00303910000d065441440d56500c0b410803c4600340b91085070340b680074201484039001409410010120005080c003941c40342d609242c900002c07107403c0848140c4002003101a05036040203140306480441c3c84c540200e2807204041c52003603491140c0d03400016401042010712800e021403501820385400b5000e000160f80c0c11091040020110001d0500449940180014001070b1918011141d81c07804c2110115100c80440f03604102170518850010300600500e03040c030941043c0024403600400c1d0714807260000d00c0d49880703180d08071580c5102c0c0134003030692806551034880c002d50040c0c2c4564000d44042c0c00054442e80f5030268007081a0103c00e0305651 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 515259163 1250 515257913 515257921
    0x20d061d100b1c080409050714070302060103030809160e09030d0608060402100c151119020a061802060d0221090c030c09010b0714030d09060615050705030d05190212 73
    0x400c11400184200c0450014a004044d4986503120b01840c05040e0005640e0350100e003c01e40100d041143c10110040903968958151400940f1140207210407400700f40407802084600340c0110380d0200324111102807040c078a1600010300b141201c087c00d4289540801c00a80215035258011440a000703044018a001d08161040c003d020180781806030800560030810000a443c81505090056440704003007502900281c5004440c800c44c003610350050380e104482040a6004500440054080c110030404600000c045440c1c010b0540e80c000c0d4411801c20080c00300c40d42c1a805004240e58105104801051007403051180d07442c16648043e140d40101c18175841807900b04a00300400070b05032401c4150303500d0523000308140d0240d110000d080b4403d40d01c610003803440c00c1007a904100032400c4240103105160030038100514107401001c0c251721200788604003d030700031012664295840300045140100d01204d4400501015018000d0030300940c03031402024100340090300075030303416114900507414 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 515260413 1250 515259163 515259169
    0x60f13031203020301060f08060103060b1804110f0702210d09080706020d050304060f1b110601080312070507050f24090a0302100902130501080607080c07020d061d100b 74
    0x40d00c6001e04081500410040c40415441807007088940b4641c100301c240b0341c4881005a01909041d0440020004042480c5091840c011655001002c054400304124241003c1c425841d208038000412110003c011800041c103121811120083d0303070b2124880f00308111f0801c541890132422a5034001401c902040c402039809024483c01003840740000c1c00801c03000d03080a01a8000144003400075541c0f242481458407003070f0480c2c403004d00c8000200048055925002d0701a0601352805076031481804004200101c0000488a0300000d001050400742d0701e510f8115541c6e4840f40302125103009450410811000030068100e41100917241e9410512034100b02d01d80c0141d00800c8100c280d4844024040400d0300401d220002d000550808201d940f806e00106003000c05422110600529000c000551660042611409070500d45d440581d2600d8010b02d0302128020070f84042e5025059104c41c0d40020300301d40c017541408101c801500340c45000030510a0600e61400851109580c0300c000f0300400385 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 515261663 1250 515260413 515260433
    0xc06180607030506030715020a120201020d060806130f0203071a12060102211806180312070c0b28080615120f060a0b0c0a1e050a11060f1303 62
    0x740540b0301000b0610b000c40000380e5508080c8a403403562124208105e11071882440312a117001e4101a401e5404580604000d000390321100000c0c03c01d03440c04501044145000c02c10074010913000b2181030080b182c949442081030411601240e0511950f0000175091241081903212900790030a07490720ba080d9014450440c0c18001c181ca0b04540020b00000c240324501c50741e402c443c00c0074940c2207031208030100c080d442e445000c0c100d030785e404131001c01c4180c020240c8882000407104154152100b441d201c1e0340301030050080d0180102034014480f030600c00315598038040c10f1400103d041759802503007451205106404da04c1d24400000340036604201e028200048444c103101c0107081c54915020525602c07003500701c0301414285144a41c01c02081030799480040e01ca025090f600f99a030303540c0c0c25524000d5960f0703d840c801140c8040c2000c441c002800d0030001341039030858120010f056814051345d41d003600c41c500c418a242e4004014020303050300ad5080805080b49012172a1104821420b50810003d06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 515262913 1250 515261663 515261671
    0x605010b0301030f110301020c070308070c090c09060e030304090c0e030d020304060f0516020a060503090d0813080702031006140a21140f01020d1a0102010606230c061806 75
    0x403681080100005200001d030703001403503002584100102c5060740082d01900c60031903548524403590001206100301c4200800340d952250001502c401daa410100382903c0ca810380c1780780807a400241c10441d29004900c1024140390050980380b0342500c130314540040742c0c0e10f60000c40005401e401920000e00b401c20843c0210300c50b0340021810300b031030308000500a01da609006020024042201c0039804d4078418404030710b540c020701e00b040c0b894552500400301d40046030700c400c4502c01e80b00541c407a00e0082c0346d260b0140b000e22202c034003803d05580340d20380380394029a0200e8051103221441c48228000e842140060038503031114284410b0540100040300c03109030081300c40b0850201d1741040c255210400740445c0f40e8450b0305812040071000d041800c100c0d10fa00c180105500008202160007600d500c070710015440407803911948110071004a00f00c1d05a8081c1c04085139805000c5c0880800394036030706510303540000845d0310700141041c240c0c3c1040002c0e2400380d4030541e40c0f0480842640103000190344 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 515264163 1250 515262913 515262929
    0x30f08010305120714061e0f13121b030f030e0c0d021002030408060408040338060609331201031101030b040c18080f0705060322050a060501 62
    0x550541e00d500b91a090742c02412100f5010001c0c14904000860555084214000c2c040c1d0b00341d40743c49145d48280f0f01070361025a2103601103000144181421090070b40c00750000b82e840440c00381d2959110b41403000010015000d206200c41850390f030480c00c107526200203110b80d6030400d00e00c0b41c9401c043c081e10001410b03100c0c1a004000340c03004545038414100411a011030340d54209510204050303055108681000d809030041d4030402c400e1000003c020003c591041c000c0c586690340040526403525008080f0050004a52400c004a03025030113155400040c010074140c41d00e030740f00000402c40e41d0003417000d85039014100c1000c407000c491400100560155442068a8202c2c8004840c8511205020091020500e91182400b59100e0b60240c80b0052002c0c0c42001164007a074006460041000300d41030099141082c04034000f0303000b14a072240d400d2084001d10700e01c1d040c2410084240c100a00e10744107c4d02025505c00d8942c45144590741060144015195007a12800c1c0700c0309460b4140c0250007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 515265413 1250 515264163 515264177
    0x2090702070803030636010f06050c0c0f032401171c050d09060509010902032a04090807062c070308090d060f0203070504170705093d03030f 62
    0x20480c0401100d45c000030803100b41101d02c945031059203640c08110080e20a80031001c156403007062610410505aa006240c42520640e40381c108503854403c4204040300e6800c075241044a60070b1000a00c1c0c06028010165600303440071404902d181960384510003650740e140e04c0100101501302004803a414a080d02a008144d10648030f14220218040c040c420000001403003210110750790710001c0392a030f21080900440c249246614040c0a40c0c044c1a48a0300494480450442c0400c40500341c280d80c1d507811840203021802008010b040d500801e4a10540421900c0000307070003840f80000030184108600d00145150001c00e4403207040d481c0103101c990006070b051002c111131805031684500121002c00c8003640da40f610601800d0054111b030112030010041c0048e1303940102c06041a241140120407504050f005566503c1015129441d044201c80011409040c14148000c0049001040100c502c400c0155119440507284000032403141c900034041c010581e0080000550309120b1034114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 515266663 1250 515265413 515265419
    0x7020901090902150706060e0c0703020c09070e040f020c0d0201150803031314031303080c0c0114030403032a0c0209060d030917070b030c070c08120403061e05070207030209070207 79
    0x482a80407990130720348441011580c0800c0101d43e4000a004e000d5030707142050300b4149440402c80503007090608601500400403460203900300b44241c14442c5400741d403240143d00d459424840246440105148455000c00c030008002d0010000c10310b02800c658000212680d48591034640c04078036802403079440d0020018001c41d80d0000d00d1a9401d26081441c503c424400c0d560114554171403017000d45082c5452035000014080500e0107800010032280503544080c00b001c0044901801c2c1c400c1c14502c00c0d0040c008200401d1003944400c014810200c80c201e04002c00b030746a41307a1402603440c0d03c000681c04007210030071410035a032030310340014007a200034002ca03a075503a001e02000402e000c0e003c403041c080c03260241c6e080700400030b440040c10100c21440d600e080214080741ca80d4807014090b2001c2d40c200b0070000711850000713000c0d1204600d18000702e00341400c555402001c1d040c0500030944001d44640340802c4100c0794441c542c05402c40c0d070000d00b01c3d14914414402e0080005024000f9500010010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 515267913 1250 515266663 515266669
    0x301030b090d1202160f0b25091e21060b0913201206060405010512070909020627040c111f02040b1603031103060f0603060a0e0c07020901090902 64
    0xa0722200910b1401684030400c141c220240b41c1c45864014003c030410f54150400c1c003440601841c000d00c8e41c1d150b0b040742024030108400c0c0351311662400500080c4035020030030160040050868041039030a0a18aa20b070340d403120000d414000d41105140304c1c4401c003131030b8204030091151442d203143c00d50ba899110b10300700f49010306a01c01d12801a2030b0718040c0b101e00c04c2c12070100070140c40e00c403401801d40d0820a03c8951095442e2000c6503814000d80c034007000864145402c0700004400070343e000c02025000d00f00426a006821a240126002402407040040c4100441c02420450340030f41e020310f904104402c1080103907002d02c060740090120020390810340f4800800c0a0300c0e1840c0c06018003030114506a426002442070f81c0c001216202e02043e5035407c22000d448a040440c0203070740034840c44000300329003501c038401603030b80a50144e520401c1c07020608061018613800380d0018200100c169480410305001c0504032a000307100302d80004d81e40c0031454813000301800360400910800101c8019808 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 515269163 1250 515267913 515267927
    0x1060b04031e081308070e04020a03080d0204030614150406030809010e010c21110d02030412020118150914130203042a03021003050906071101060305070b0301030b090d 74
    0xd000340a88418504010303400c1c000b0000090b6020107050f03680d2a510891910451480c022030146000c2e05c07a0000e0300f07200c1c00b00c2c100c1c0220b8005140d01501032641c0d550010340e034030120140c02031503002d2100101142c038502c2220b000004501c618199442e120415010140354840b2041c801d500c1c105090002c07824002c00c0c4c0312046020b081032800007410b02c0c01604c01ca400780310700508001482e814050101b89a0340403000c2440940c5071007082003481c91a854442c4504105180140d1060208010341102450300e200307114010b05181c2566506606010980c0d2080d40150090002d1040d546d405c00e03500c241d1010040c0302c400242e2804403100c80c00204051902e60360210940d40100100d41841190b0a44a0b100307001138401005450356401381c11444c10a0f0b12080e03104101c04811800841e0186c059184514504000b811140d07660781d5050b1284200c0e10740c41e801315136a58001100007913042080d02c0103414615a000e8130b079031440c641405160402050380d602508a40c100010351900511 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 515270413 1250 515269163 515269169
    0x10504020316050c150a15080a08070209061206090705120d0912020418030f031a0907080a061a1b070305100b2709060f070e010503150607150c0201060b04 68
    0x54050b50302c01140400628080e850b0712820084440d260a018143c1415405811f400c2840400c003807009030b0311070f0242d864401404002c0e00c04c6204201c90001031406480442c0e002038000d1207901040034004510785003500c22a90310095034442801405546440c0382c80d602c42c811a10014002c1c480c03421802050308020b4416003142004200f0003408568944d042000e01c1c2c1e400008600c40942c1038200100300c10702c15080e03000460324180b400c21502c607121460488409010b40b18521035124240704480c60640208016134040d51608081202241d54030300300021041a10455110310300c01d9a8950b1181e00c400500c1050b034813490042000a20106900c111010503042c00188443c118000c02d101c50310401010109800c021800000e1044444203c0d0249090104480d203540e5040c070030070403190007543c0c5000852200000c0c40c03605d40c45079005641c4510049220300907100e402000c50305c0b41c1c0040008a540b81c081185200c2400700c41d12542428089500c000d0044902d043c028441d90711981c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 515271663 1250 515270413 515270417
    0x30a1b09170c150301090606030b060f07030c0203100c261612020a081503060f13081e03010e07080f0a090602070b010b0d0c03113009010c08010504020316 68
    0x700300803000c4205121000101d1000352448100ca60004100c070780b654000d00500804038544000401c0c3c0741d21a00c141c05941c800a000b5500c0e046000302d0031074443d00000c00840c1008440484240142c50a001900c0d84080644000c22040c2c059000900014040c140c40d100c00d8480c0005000b00b80f00f55003407550042e0014450070b20781152400200d5a030301084d000b40310303814000113100c0d00c20f0380e003e000c05109101c0c12080303c454034032035170805841d140280e03400d00020314000081003070040003840005e0b00c20f200d102950b1421058101c4170540b10402130594244003400b000400c1801e24801e4141e50020303080c5841c401070300e88600480c0719010064054100c03170360b1700c0b03103005c0400a242d41100c0080d5001a0500600e40e134543c0ca1741402d903c021183c1d03006a04140c51014100d01038085c042410119010f030300e0500018100b101e01c10380c1c21000c840f8040003001e400d45c4840b01c5030380740079018118100001c5110409084090403200040e071000f40140d104104201d458482040d00383e807942514 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 515272913 1250 515271663 515271689
    0x50111030708040e1603020c0706030209040f050408070506060108040c0b0a0507080c0a0203121c0504020a03150c020601140609010804060f061214070b041a070f050102030a1b09 78
    0x200002031860254503402041001c00007070100d225070040f59820f12070050781c100c060340c10000003801c40590088518582c2d480e8030450f401e1198038000d80203001142005000000c01c0e00a00950b54141d0300d0940e4240c6101c1c000185440a1000c2070014590000c2c00b800e1035200c9003000e940346100b1061038410880c03d110003061520038107110307070100d03800141c010081540358111003900c1603e40c0c403400c1080b0300c603104843c0e080454055000545027843c0c0014503101c28400b00c0d40119001d454010030403a4090403002011002598001d040c2450300041c800000d866802190042c1c9000d406130403d406201c0303035a1400d45650f40c1c0c1c03421290440310a180805003901d4614192001c0c0100c000f00841c01c0d400c012011800e1104a90041c0c4900c0c05085844010903c5126003070301c40c491401001130507241000107004440001120007000840543c40c9807400145456a07805240e00c400c0450f01650000b041c00f070b03401124040d441e291100c44080883c10801318402800748101803107084007003044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 515274163 1250 515272913 515272937
    0x31a160e040912211b110307050105040b04110d020d02120c0a0b070218130f050f07060e09060907050a120b0a0e0f01060228020f31050603070501 64
    0xa66005035100c20307400b120203001c001540070f015100c4000e01e1100011005840308441040c80c0034001d03500403898080c10001c480841c07080840d900380f00d161140a151100700007440010300700f4800c0b54441c03802503a181540d42818609840d032078071b0101c035440c816000000e04c4005a691080030b0400b103581241c0c111504481480107509100101180c1d0b0752083c2e40d0f00f4001083c3c1440360061200b14803c40c3e11054000700107109444405094404c1d800d90000c041440001070303810894402c02d68069412100a400243c003050301e0183c154001c0e000103042703110f81c407100e401c081c00c4249c0c014100303c50301c918510740410020503a02503085400c04121000754000f00c1c0c0c502c1da5005550341d00c0040d0003824a140c0300c81002590082c280d0b608612010054000a6120303c0071948040009604148006480450800c00304030034010781d003070741c3c0410002040b207956900e40800300070348213031000000a91441c1442200410400c0d162020070241090f0030005195808541d03402910300900700b12030984a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 515275413 1250 515274163 515274169
    0x902040b160f1a06030f031e0f0d020315040606020c10030203060406030218060109080d05070305070825055b0209041a0d24090c031a160e 61
    0x2191541c06007002000141481143e0071646090b8030806041c0e085036900c2200311400da0792031192400c40c00c10701004e03194210078024081300500004191646281c2000c0350a04070004a038000c0d14000d04610403003d150f46c20341010b00a21700108445e0002d0805d801f400c001190000351003501c01000c141d80000000c0c0c1d06d80d5641d00c46005150043d21a04001d4462000b0f50380c2c2200590b105408901ea10030002a01c14000480022119060341c40302d081003850307542601c05800c010000c5070400c4044c441d5603400c910703a03005c44109448403480144072480d9814601e040031a4004581c0f0309468901080781a2100c0c2c070114600550b0100301000b580c1c048400c000c1100b0005088844540c284030034040b40d030310f05900642801003044900304404048420b00c10313020302d10045425007140f00010824041100c8c1040c800c0c09880200445602c80982c4c90b812084076020076042324141c010740c9080c0b09101111651060040d10041c8a245038103103081c03448490b41d03501605000b044a0040e001c0e180d61 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 515276663 1250 515275413 515275433
    0x6031502121324140f04030f03051510050a0f0302040f050613120308010e010e1b0702011e0908060609060a0b0703021212060127060f0e061801090902040b16 69
    0x4001c00c1c000b0190381521800000c05042d07144159400c41c840100401d01a20b1170042150089515894180c0c045031031034000d03400303480010034802111908000300d90f00d6449a00100301003408039640c1540e03070210828003038030650800d00c0d01c00070940705000900059299206132401c2d1641103030020303120a5051060a40300e5842d07007240300c1c00c00005200004050304040e915042c2d483c02d8082102030b03130726210400b245440c12a0901941440840d42c040c0003034404004001460062505507180661306285900382d400c01c2010000003880e0704003c002c050707010300119805c40011035000c03485040c10000a61001d0190164100d10040040e684d01018000c011301e00f502108480c031036485000041210905020845980e800b00710100c000002a04020801d6100300c08130700800480181082011614042078101207000e100410304802c0c06541d8003000f420b504541d85002d41c2015000a000404005103640000b140340c1c0144014019890700c0300568002000008112202e10801d04040c1b09070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 515277913 1250 515276663 515276693
    0x1115061201021b0109121704082505100e0a0b160203040f09060617190f14090303010302030106050306160f0c1b0e01050a18020a020a15060315021213 66
    0xa80c0310007001501c0440b042d04080001030140c58049202820428181c1e0741100000f440d61f040402107000800290300040540a4018005110010540c410000c0022608001c4066505520540b2200068030060041003c1a1100d1001c2e241a0140f5503e1144e010b5016080309011015080000e90040c0b080041d24005c00e180c9004880d040d64401030346004208500480d00003581c03608588803004000c01d07629000700c401404448031030020100c480c0041110b040544000c644484103450490207000c19030380240c0361174018650769451031040508442c11944018040d4024070200403c1440040c49035400180b00c2c2012142c25811070b5040354200c0c8445001401c00815000000650401e50f00704416078510605809503a41c82d003003004461800707440780301c0d00c42190782080c05603a8a590058035220206004540301804580c0d00c1042c11f03913560300c540f03501e984c2e15001003040c400502007480d6401c03803c03d001c40c80e01c11081c50b005005403008200701a4000b511248204011420f03d4048035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 515279163 1250 515277913 515277937
    0xc1c05010e0a080c070e091b04060902040e09011a060a1b1703040b1005030309130b1804030305060409020d140c060c010c18062703020d03030c111506120102 69
    0x14040d01803405190f607800c811095a5244101d60000c0f8003194841c10b2540150010001030104485480c2144800d451528416803c1034444100191815840c00640081c240f1b84048880034070301a9402400c580c0034424082d040e0310600c22600c100e4980d14229111010949046100790304030890240051540c25002001808c0d043c264001d03003010302000d14081c600c50b00d60903500e0f84030040c1c940c040400b0b80c002e041d491b400410401c561482c004080c0365140b2411440801da8070792070000910242d180029486440c042c0e40c00b00801c040e4503100390b9034040780442d4200034144581e0081984200e030200020000540c00d101c01c1940401000a00440c2e800108200da94902201c80c141c00f92450014890115140ba441820300e0300180d00d0350829191503581d501c0043e560401c1c1100c0300d40361180741050b5040d02460120158403940c20000045001707445c0800c041303521030002002e00c444100c013464582c1080344401c0b44040150038182d04a1700866403088086441081c2d640280706002003000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 515280413 1250 515279163 515279173
    0x30a030e1c050d0f030b0102070e060103020c0c1002010204031505011d090307060c020706020c010905031c050403050d020624211002030a09020a060804080d1e050a050105040501080c1c05010e 84
    0x1482d40e0f4000700540e58000b585d5418482c50440c1c00059075214203501604036600382040014050703500c6540580203003001796080707441e130075070400104a42d010001555001030f50006004e100340485482005c4000380c0c4450104410761621441d03002c8185030301000d441c90440c94000c03031007034042003060719074443d0840c6081200b00c1c2024030180d0303076007524424000907020f090958070141d8081c0c00c3c100c085880c080c02420070000410740102c081c1d02401e50310f03000e0060070701010020440c1001314900702c000070b400411543c20449138441d00c1d0213001920480610748445441d102e034894030741441442d44026070365000440d1507020b060902c5044501c00e55510300c00700400115440b503030440c00c9400e00980701c00d986951117280071a001c0c0300845001d840310000308025211290107601c07084814442907120030084510f81030607010b0350000d40f44400c03403d403950014040c1c0d283c5031141500512010b0028092182c6020119980e807024142c00030425410742081c4080c0002900804501c2802005440c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 515281663 1250 515280413 515280433
    0x1203071208101e0315060510020a0b0f0a1d03040306140c1209011113050f03030a09030f02010c0606090f15050f0114040504050f0114011b020f15040b18030a030e1c05 73
    0xa4006d081e981308181c07150101181e06914140089070080b02d85400c15544e5a041d640d0380311030341e401c09010f0b100502d0709a40d944a22400c0702c010400c500e00c20f420300080c60350740c1e00d0760902000b0765080e2500100c0c021150028042c070b91405030211313106c0c65080da43e460f440b40e030382800c0580107101e07a07600041200d10000306500d403507004071100c40a44808803481c01c5203803c564181550f82c0204030281c40807840400c0144085800980d540200c18070503d003003002544980e03030f204150358a44c0d00490000391184210706501c0d03020f00030740102010565560206d035242c00005000082e1480442d414402c805d142a04030303a47d42d508072005010007170020b1260307050002c40c40348220b109202e020104485000514038030f41c0b140d411110401090840003095041d07580030800303440c504400c2581d104034120300246421101d136010b4401404d03a555070584070102550390301410341c3e03490b00f01403013a080180c40c40c0009030809800f0603d000c1c2030b101000d6041c60101e00514039510017030f0107449441545c100c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 515282913 1250 515281663 515281703
    0x40b0a080a02030f0606030a090503070807020f010c030203032202030f030c1b061905090d050f0f0105240a0305160906080c0916030b1203071208101e03 67
    0x80094021599918129603603090034801280001d42c2c4440603c10940d0100d04c4600d0600040c581226080030005100c41c4145d880c0351844d444044121345089000c00d0910651500e640300000c0807001f03003000f900712202660000d45a20005200b03001c0c19010100d429100309101001c80b081e15805800c541e180e01d4a0a0019a00d0300a03d212049a04c04c80710306030400c00622008201c580c001504150808010810402c0c1c0f00800081030400c010050010681c25a1244034130740000c0e01a10150203241c4060725058144004580d05d5001d5a04100600520079200c0412005c42000600109148140c3e200080c8842d25150700113001441030038281480302c84120600e004942151208200403a56003480544403281202a00d60042c1d400002841c13911a000a201c1400014a00003d1000740b050000b51131800c104410003481c0c0c0046110002c000e1a2508041c001009081400c11850890b519566594090043c09407200030b599640d184829041c030070340080e6500440b02d9003e02c9038518a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 515284163 1250 515282913 515282917
    0x70c140f0c060703051207141201060206010605070302100c02070f030b0718051c020a050d03030b03060c04083406030c021b030d14040506032811030105011d06040b 72
    0x440180d80200c101c9400306107010301c02ca81e4050380c107860302400d1070700210045103c00c000500318824001808132890a00c00c05000500101c0344040c282401941400c1c80203240c1103051f0050000e00c0001c1000c2d01c0402d030005560101021894004648445841c604034240400d50b8414000030b10070040200801041c01e16aa11851103070307030761000380001281e102c0700d04096031280c250170a10f5450003d9400d03240c0c42020201c0f900182c610000d0903610004903489001417030301900041c0d038401400d011498180074040d08003801490050500741000038050f01d82c0e400c481b003041e1154035280b940c1402004015105001d441000301c524880c0e980d02409006027108503140710041c080c181c3ca92412480d82200002507030000b4005203400140c1803c10307030705155600707580b0411413014403000480f9513441c0c005611a084001c070f1860741c2000341480407260040c0a0303044900a040412041c0b104200c0810349045503024a05240241251104010209802600c941d0040303c00a80443d26002c0480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 515285413 1250 515284163 515284183
    0x270e031611010c0b041b15030603020a0e010f0510030b030303041a060103061505090103090209070c031e0206060402090f0a26190201050f0c0a030909060b0306030604030305070c14 79
    0x400044101080c8011200f0380a0154001c0407880060003050200d501110950202070384200c0d40081320fa00d450000386003036424014000003e85a070303824001c40c10980414001001c090304007450300c0d41096001407425902c0d016443c000c042404805204510070742150603d21000380130349660303041ca03081c81c2d04526031400c0c43c00408a119400300b003803944607106040c101c5100507041c00c440310001c54200c9071030b4054007010f81011380b61b215107409661102c1c8428003454090302c03070035001e018528010f00341c2070b15511151107400e00004148203254010030041da100800300d60069858144100141c90500304040c3c85070031060b184008541d040050b41e11252030f0150314001801c10720980d9260756151039900503a4441b569140c5200010f50203000900040c0d0b8101c0d413900d081c8946803111034a00080008107a00080d04460100084815403041501030940039003441d1551501d64003080d602c0d2409440202017580d5500000c0c0041d02c201d0300c0c007070401c0c1d12410901c3e40e10410750783c03580c0d560360881c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 515286663 1250 515285413 515285423
    0xb0a1202030118110c070e090a0c14091e060105031b07060515030c0a2c0c13060f210e03040308030f070201060302010212070602120c0d0b01020106270e0316 69
    0x401d000740c0303065006050b5064030f541240140721b43c43c10a203030005c0c0b000001e0484002441460609000100c0050b60340000d07020000b00048070300500c804100188001404414401881500d0394004480100c1c0055101c5428281151f80c0c1e15680c3311702d011090848500202160040b45000c200301c2e45400150046036000400380c0b10380740300000c142c0c851b2001001e40d40d02c20512442040b401545040c00302022030b00e03044084940c05840c0380c4105504044803441a44240000c020740004074041c5500c002d003c2c140742c8148444080100540300056840d00545444402011b452000c0b14603040f07154190b400e43c05403500c8503600c1ca40f5654681054a00800807d0050005404144144114422690140d00904c80c80744584400006640012411744015400304100c51402000084032400389160300509551070751010308500843c0e0508400d5411641080000c120f04603030751000d11401205005000c0c162800c029240c0000d1604c01071001041c040801e19101c41b13108051042800c5010f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 515287769 1106 515286663 515286671
    0xd06090f060c090609080d0f05070224040501141e130302100e011709031c2003090607020a0807030f21021b010e070b0a1202030118 58
    0x9103480b4011507510f290811003240d022603010018480d890107091404051000203041d030710b80202c420308100700400c00ea030139903a8401045034012a110351107011460340994402060b00302d4460180403421004d03000715528814002c80f40d01c8a40421400e0f0fa04c0c042d005a81003980040d10107800a100c800800300041e1240024051f007072500f40c0301d41c81c00c6a010b000040483c40c04070b25640324901050700b4807480716030004c1079500d142c0302d5200310f042c0520180e041800920300507044d682c0d0f0303480f5460b14142000322400114010081c8006a03101d554500d4000e0f81d0310040b1100c003c01d4800f0400c40351022030f100d00002c20a4008034035280c0509003010100ea8100540c000c0c1c503521895000a4810055529500c0c0f4844049290b00a1008200d581e0210340c5812085c842c4aa4106001650f000c60034400c500560003691451411074807540c483d24440d0001070000b030407440d810b1070 = true := by decide +kernel

theorem cover : BRFrame.Cov 515107913 515287769 := by
  have h0 := BRFrame.cov_init 515107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 515107913 ≤ n) (h2 : n < 515287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
