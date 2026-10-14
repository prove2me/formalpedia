-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2783
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:44:06.272064+00:00
-- url     : https://prove2.me/submissions/f1d7b21e-f867-4b3b-90ac-f4a545296a11

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 500359712 ≤ n < 500539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 500360962 1250 500359712 500359721
    0x607121107150c0e090117031e0a0e041104181b081510080a02032802090405010b03090712110303040914060301061a0706140403030504021302031005012001 69
    0x44402041d40c81690309400e40d14814a0041c010031300e001800440c110780000e044910601034a000c070302084441c0007401ca0108201c0d0b55244040508601d1030002c83c8558003560000360f007080c042061241040070b5840c0600c5941410034046e041903003050f042100c031840100031450105903440e986d400c042c401500d0748a954481800982e1740201c9464201031091801d064004114098208550050315007600410340940c0142c1d5288010303100c0c5c0d40c0d02021840000d913618104006001c81c503020810084a030024090584161024482c990741c03400340e0079003840101c500240c141c0180c50b00303000705003c2003000c0b41c03424050b011410280009000181c21540654400046690340e0b080f00800c030106004282d070b00040840013004a680b4180c051084800e8039240c40301149400600d003001c2209550002000c2e4444007601403040c0b41c03901d805401020142e600f03912807150f00b942c820b40147c86008883c41640c070a035080c0d9a15141c60010b40300380f5030404c3c1e0b0300e80c7d1580c1e0780340039407581509204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 500362212 1250 500360962 500360977
    0x2100c0203091c02130b090c03060f0a06030c0207080c030d050a180909020a050306070801150c050a050f010b060403110616050a1101030b01030e0601050d0206130608150603040506071211 82
    0x541c20180191032040100c43e5204005041403139003070076202e844550305c401c000c541c043c1e225400b580c4c9d669507403400580c045118401030356015041010129250758550b202d0400042c9640844684540b14144295076480004100d40c3c154031030345a011a0906c00c6010b807940d4401818026811034511850750718038809c0760801b407001345c4d80d01c2c601000d518110390018000d18080d8040d081609003400000c0c05000140994101024154a500c080b58031810b0529202da030004251000881d55203401d40d124030000785811803940c200a94041186002c100300c40440c4c0e403222104030b400141000740091074014000c00100c0200740b407181030205400388030403841540305950720758280040400140031521241c064504162400300107a0161a00254481c1541c004031400103011441c0e10001d4060302c220b91400706007004080e80010110380001c0605d0140e0686069560050070000a014203400304440c0900765612820200c0d04040c001e0a100300032846112010821030400501e002407a0300064 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 500363462 1250 500362212 500362249
    0x204020d110301080c01030c09061b15020c0304090e03040b07030320070b0a0c0e030717100e0a141f0c03061e0f050301091109070507061109040e0c0102100c020309 72
    0xc17904181340d0791501c20040c400d0005d06280700050304080b002000c1c0d030410045140d02205020048083c00700c0c0c0c002c1c40f10340b035060340000c6d581c5030205100c4540765000b9114030340ca03d5050007003003800b5201c04010b450a0300c100014043c1001c0c1c43e900c0c220003030b008a51200e580e0950305191504e10b0034124008202c00790003000d480082e070604004202c1224100310341c8030704020b07120303105809555002c68508115502135410701a45c014400005090041e0080034074413003454070f0b081030481c050205054058900540720203825007004001c0503160b06050100b501084031030004951002d007070f41d101c0443e180c014a000201c0f00d071030342030715050204041040c04050b40c0380a420007810b10b00349514409024103030000e00512401c0d03683c131500d9041c40c0e0ba8440c4030b680c1402c0005d405a00c54425110115000503040c410340d10f1600204a030b652000101c54095030070000a00710440000402c07002100c0182c2c0200070031031250790000300900d809200601140010000303008036039942210840781a40c241e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 500364712 1250 500363462 500363473
    0x4060501030b090d0912020402040e011205190f020103111c020310091107080901050705030d052706160903140f070f03030813061407080709050f060301030204020d11030108 76
    0x1030402841c1000001d02120582d804118134021050f8800d020004880903100907500424003071000601902490b00000b810701c0d58100002a40040d018034211128058000d68080c4a02e00d08a000100500b14000c0e01c240c080c01a5003005511a9201d00a41020800c10a0030054500c450403d203030350100b5161401600030091119450b06480c24400030501210204070746015200210342078020745001800c13201001ca43d0030403590050003160103151780201070f2542ca003c0b90030201c004290566529180c1c5002019981e415850307051001c8114802d07500510b440e84e5402d02c10a1103001c80d44e0700008111450b200040095443d0418500103500800a003050f03180702d00050385401c129500c4142d003091128020404203812610640d000b2030032a601d02c0341510f190801c040541600e00d50403205d000d81404020b003e59103c200c16011304400c3c1c1da002041c554031410440c1c42c000c548100c0f0b41c841800c100410040c5003a500403e8403098800c1c01003409007035000810304642090303102c1c0510b82c011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 500365962 1250 500364712 500364719
    0xc1c020d090f12020c0109180b030f01050702120309101a100804020306060a1d0601021e03030402040e0303060307270e03210f130606030501021b120a14071a04060501 73
    0x2002c0340f0064540d840242624203400000815841d07a0f44a142403c4154801c000d6000e0b000b9089102d4030322002e0101c890060319810424024602100c00c480180600101030a0030610282101c0c041c1d0f6080c4010a4041c4076001954000c085120030884c0503c15421541c003152500480200c1101254880d0038461400e0b00507d81410b400402c03a070700c07030743d226102030004500c00240c0506103400291801501e549580050346009161501b940443c0740c4c802c003006000200200442c1f00314429901404058060510140c0d40d001c20346400f540b58101c0b4806001d18032004c01c1002d40c0401451100402c409500c005030200c4281d02d405422607000059099419144020441802e100c01d50400a540c90302c0011004281c0c0b0240080304200000d4614005104841d01710801558020b0001c540e200282c99034885004040508200580102c500041404405d041910004003060700e81c121a403030030000208056100031801c9a003105c034100b440700700c4110b4400140c4140d00c0703000700261a505 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 500367212 1250 500365962 500365973
    0x406090b0a1d011a040b07060b01020d0908120a050f040f171902060d021c2f0a050c030706020a0804110405070e01030c0e030307060c080f0c1c020d090f 67
    0x345500b0218030041060071611096401d0b2074024111140c0d40d0418841c00007a5a0200b1a441141d101120b000c00110305c00060028951100b414030b28260200d50300d03500701110075a481079280c86482a01d4012804503060148154001c00e6224100e1600700e140589400c20022507400036008244064034004050103007844000e41c480f03605940800408407503281d000041800c11458400a0140d04046200000104a078042e90302e4404c000c44042d20780e007402d030f104030010119100c12122503250400c0700350001001c0e1081148044050b049945044415031055806500c0400c01107500d1108004407400307d0014405018040b91560380d100e0a424a8207100f1806031284c80300d28440c0b4900130a200750550400e0f41d15228103420300780481c0f4000c00300400e40d401c0d100440c40e2900740c0000140340c410018035600580d0007100644803021191901411114070340381c11104111401c02c10040340043e61030400307281c010008100d801528001c0e10920003c1a600c94450032a078240010000008105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 500368462 1250 500367212 500367229
    0xf0c0a060b0108100302040b010507060f200a1704020315040515011401050306040c1209050a0516050105040303180302060a051317030706020d0e0307030207090f1503030e0f0406090b 80
    0x2443d183d001401c20454021200f101440f000f4800c5a0720701c105c000c580d005405507528940c00107810000500c0030102c0c540074242074114007003036480788213000e4449500c020941d09020400c3d40da1000e00c01c14480c501c0da201c103010f002a83e0505c60b60000c0380020003a42c04c010b115600c03960181684017118000b41c2030a900680140f40700e006450500852030368040300344d0758072400072113022414000d80481540e81c908960030074002c441c28240128207100c0300050030b82c4401d1284007140c51108441c411360b04840c205014860000e9401c200400100e4402e45a07090080703030300343d50100c055070f880d40001c1e9158000944400442c10120b0f08184a10090318114010444103080c0e071040d1000c2c101941c2ca07442801d10062107194086000c0f8034401c4503a0242c1449201841200c0e940c104500f0041d54a21041c45028199401c0002d0780260050700e00801c1c1d2500c020241e08107c850840d036050303070983c0c0c18280468010440030100340c8103990300d0041d800140b50100c030004034602c4240522051a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 500369712 1250 500368462 500368481
    0x1e0b0c1c05090d030318060203090129180a11040f05030c01020a0503090d0503040317090a1502070b222912010905180a1505010e10060e060f0c0a06 65
    0x1c061003030564603168099401107907981031500013890143e540d804140c80d00d1648002d00401c0c808020071481805c1540111000d051800c4141200304004200c18640c00100c00403607003000340801002e1000070412582d030780001c83c2200202d9020301b404038141035500103030304c4002d122018503400c00071810203204030a07081000b0f1025115510080d02da4503620320500400a02031411a40f00c401401424420344024503445001c001e5086141c2411420507000310307488174030900c101c1d20b002821aa01001940210030b043c1c01401e681348c43d00c0300404040d042014644600300085a000000310703c8111810041d100e1042d120030b1042c28084405000101e4046c1081c1c003030420016140302c010300d0a542070462302c0070300b000300300d95841c040111160380e0300740d0010b0083d00c1410382ca4000c02940014003094003c201200b0080c81e07036201701200b40c070308040c0c0b10810b00241089087c80381d64412944540d0280019200f00c0c074007004014403110562011926910701e03080200c040041088a00581840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 500370962 1250 500369712 500369717
    0x506041a071a071704210309020301060b070308060306071205060117040c03031211190e030303460b0a0b161106070302030d09030210061503060501050a02071e0b0c1c 73
    0x40c40d0981d03425040c10300000021110301b4000c1c0002c1c680c2446904400380c5503601400910855a44070a20410303900700c548124041103030b180004501c4d040005105104108503900c41442c140380c1300c2c0d20001060080e100e075041090707800d001d101094004004a002d54454580741c981d00c2d2a608000f411422441c503020882814000d04e8120b20000300140c0c0c0c5418500685e10000007100707442980d101400c0085183c060102008001100c1000c3c5003010400f444002003101d00b485116103280d0f9200c0300010040d5100c2e102882c0000042203500c5040c038258007038500b036204c0d51a012103900c15044038005812482401101a007006503000407662070072802d03204c15090504507a030107901c0e40640c4c2902c50044d5542c00700c98090500c00c010410290015010400c01e45031140070743c00e11a6140c15100000c40e040c5000010075500c1001124102c00c0f8660250140c02d050981032550a00c00d0000c0904172400100c0210b105140c200040101d14440001480c4c0d000c0140e000003201c45110301500306 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 500372212 1250 500370962 500371007
    0x30509060106200f0114010f06140a050c070f080a0312050402060f070507050405010308040305210306060d1b020d080f0f071101180302010f060905010506041a071a07 73
    0x100356000748810301400f640301503050300c803d092003540d454a1514220030040c0e42c2401000140502d140f80200d0503145e03041c00503400b064890406591034400c00e1841c5c21003000030024040b21600c45c50141000f8094101038504441c0d4401c841207661800e500030200d641c0041404c542095007000009074020303000ca00901807440e0980004903a80515a8031640f1010009090302c1084000d20042005d0304c00100104450350712400c041c1c000303402a000480e8144200303141d8801c0ca6511074407070409c4400195540b40b0756036448081c81401e400452070603508035260188a850780040130004004041164014032251a812000502c2e904014082c520030419210030b102c8200d5400710303110351041140c200321601d104810312450040c4020310a41802070704100b0180100b50f81034100c18100200c00f0030920219889a01c2541101c000784074070341c2e12501c200400c00c1400d240441182040000405950510305a6101d021550018840301d081c907c901c04c0800c025950060000680000c9003140c214 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 500373462 1250 500372212 500372219
    0xb1315050f0d02190609240f0c1218080c030c120c04021b062a0a09210b06040b03070e04020d0c03080706050c07050c0111100911030106140a0b03190603030f0305090601 74
    0x941401c060345400d002c0000e40c4060010342350061040c2d12011341e1110f641708010300d0b18000100098101c00b09a80000025070000480d20380029500703001010080c05020b180c400441000260106a41c08010354000c2c801d5819565440b88090070700088901200c005c01c601400c4a40e0406800800040d40fa000800f6000c07070094201c4001070145110044c11641d130020000140d540d041c240e4843e242804045c2012a811480fa6002000b2203200314840c031540c0d00ca000c1080181c40b8000d440e50303056441503108004000b0004082c0d80c225002411814002c01161181d00250350b460b00207035600b8900050384003c000403481501d500c0a40310380da690900c0c0e850394540e52641c0035918014104240c200000c030341c140c0148081d007031a82c241503042003490520714100c9010b0428a0380c0c5c038465468981d00081e81210030415002d8000000c0030540454200400e010b55900081e105100403065103402040c542c90f14400c080c040c500030b81b1030100c14104120024142e030002800010190000070042 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 500374712 1250 500373462 500373509
    0x904051e01060b0f03010906061707120b09090c0102010f0c020a02011d030609160603051905060120070518070f0f0e03030f03041b0e07030207080c0304090b1315050f0d02190609 78
    0x2a400c0100ca15240540b2600e0348cc1c200003401d10850b0081d408030980007440130390384001691010781503003a0028019068a1041c0004444049401c0030150f009100c1503c01580300c0c10072000c0404034600a03c0314180740a02291411700110b0b200d240c41d034005680c00c5c0c176880c8015142002000186800d207c00c0c940499540c0c450301045d600d01d0051525070001c02c1c9103138081e004500030b02401c0c2c0c82c41c161102100c03504a60300c88281c884c480c001d00e0b90110582c410040d00c1e50715441003e4607203c1b280e520614070000c503403481c001d4244404001d06116051203981d030601c014080040c640c0b24554480c2054200f0621182c0054800c00d08003403980010070844003190074040d8441c00e6420016107413903042c109580742c0e104650310080140030001e4045040d08140d0322400882d4400d950003089011401e00500858651710314240103142a201c040040d8071b0210320080c0d462001030060500030034113a0108004c202900040d1105100301c28050081a5105081034010301008100100042902424 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 500375962 1250 500374712 500374757
    0x11070e0718050310231f0f031205090a030f0b0403080f04111e0405040609030e12061302060d0903080a1b050f160c03060c0e0904051e01060b0f0301090606 68
    0x110425102c03c3c030118500105082825801410554017010380b905454898103a04000445004610311007408520039500101d9034042e0f070352000100c01c58010044042d00e02c2c2c0c2188481a91240f043c2c030011000600b014041c00d8064440d9a40030a907081a14000d055050010f080c1e4024941400411020400e01c41001095000903505059100404044602420740b56048503820904040500041050030781c81040210301960301c2000c131060040802c480b08018844091131640880c01003103076610681d100000032480100190718004e086a200070580749402810390100d1051020881604500e0203907405174503001d06000c61247c1e2520001d8954000d0704603500009402050f0fa40780c03209034000016a01e50000000c1600c40e98074075091009d002105890f90000d4281d920091640c1405050035009035482006800282a200407240f80340b8044d8848505542d01c484001495070401402020b099220109043e569810b00c02440242e4503164003a20811407408000d1503001d028146 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 500377212 1250 500375962 500375983
    0x414040c0e010e120f1204090c03020702130c09030b160201110306030a061503020307120303060506030c16030225060905030d02030301050613030c06052104020312090111070e07180503 81
    0x1001e0709007001d141240380c6881c50040e500d005d81c0c440c1d5a2101a8031595402a004448075031101b4070610103c900102e040c0c0c040d214000750401c0c003410341684400301e241c2103c60302d41418a0300c0c15005907203859030245a941503030b59552401c486550844003a6081c020300d031380c07104000f00c1c0e039145040c140086680d80480707070000740c0500d80c0c402070202048034602c0d001c0015034000f0b04807047c168540c0d0364003042d07920700d100c2140481c0c6080d1000542c1d00707000b01504e115411042d0418144586024074030000240c01b4000c40441c024800e00f55076002c01103491444103005c001410340722500706a4007078100445038121a103c2c1c0d1100d5184d21180307500108503819035400b030780d08039281e01422806024842151300011324079400c1034008203c541d070040181036500c03854a0300f502200c501002500d405030040c0c070040d405800003145c1c0404603a4030401808070003810f1400c80544a041241d050400300d10f5008694110504001d02c010998004001d02c1941d00980c24900c40c141742c040040c2d40d5159044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 500378462 1250 500377212 500377219
    0x21090c010801240c0c0618150903080a12050103051e060f150307030501020c0102030a05182107060509030702041506021906090b0f0403090f0e0612030c030414040c0e010e 75
    0x22600fa100c1c0c401d003000852580e02000790f4000e00d44a1102034881001d00c07800043c2294402d030f0001d811041807aa07600d0418807074a400b81c1f00303811a1155101540400c0c000e030180034404455001568617886010700850050018017060803141d07240c1c0d400b81c1d075241c2201e03200b684400d0a1148800d500c20025400100010400a0740300c2d111700441e0a05003280e1011f0055440490743c140191010b4001358400c06c2d030707800e080207203585007801c542c080d0422003da0b03e01548103050b01e22a0103201140c0086ca402508000d90805c10555030b00ba094460840f284103542e00045440c000b14182402030100000030aa0403007052814050700235529003ea004001c2554440c8445e24240039596200b2299607400182c690550300e400c0070024a48081580c0c00c8000408116000980303c010004100a85901c50030300311464803401c0c200400860440d0900825000070866111544810801480248032118a0491002d04035040100725030300207003003406000c8c44542003c4a6030340180740450420044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 500379712 1250 500378462 500378519
    0x3070506091e030303040b010303020705060307080f06032d070902071a07030f0e01152301110c120601060e03010b0d020402130e190f0606210221090c010801 69
    0x2002e1052036000c2c030100c03581e01404000b082c0401c0c498619844c6050705c1c000c0c0c08031086142e0700c0044c0b214610084414200040400020451410440c1e08840d04154018210b81c1c48020101c0d4071034803110640606071090354501d54510304c2d1034041c48100000d2038507000c114140aa943c03201031080f03902500b040b81c261a81800194407034000d03440101d03010a142002c0080a0400c07040c54001c2c850894010001140c801001840001489200d01001d40c25154100100d50810040d1911040803410820034000d0a070005236944440d07a08011588181000300095490200081c014510a91810307000303904141041455407a000210546254180c80040e9140101d0f003603071007084561303006039140c00004814400c01502103217038100400402501040900b004482000c200c402d0740c0314075000304140e900341c80d0100391120071103800f006000c0c00142ca020320103400c11180380007108203500c208844105004c00303036104001c151120038081c00e005103294100a60840d885d00d420039086903102c0503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 500380962 1250 500379712 500379739
    0x80303012711070b15040c0f0e010905040c08071b0201020d0c150e010204150201090f020907200d0906081003080906070c0305010b0f10050a200d030f06050307050609 73
    0x840e800b006159115800d1a83c403001c10b03160000000b00c0580b4400c0800d11100b40c00803170751500c2c1c89200e10381e14554071018442c3d240d0950950f031464400c0240d44c144030881728005001e40340c601410340a18902d0341e40071558684000301038002e030040440b8200c81c0b1a02204e940050b41c0006110045402d84c0c03c1c030b40845451860400d020400d4800d0030f5282508000910500100540180045e102000c040108044100038103d00b2682013030000340402c140602c021000d410000e1201c0d4002c0018a0000341402d030704142886241341ea01d030351803003551001010641290340030500d0b0300034281c2440e000010303080c114525111b01469001c042c1403000009803201c01079461508a0790040e030f1041640c0c0c00d080e40d0341041402040d0854401d8002e000001c1c44540700d1900203480c1270100880e40b1200d0070040f1842c03045880880c01e0100040300c80c4003500491642c41c00f0070a00150441d541e40204d0b080c55402d030f6a9050710311990156000307910080d418800359031540143e0700d801ea000d80300142ca0058 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 500382212 1250 500380962 500381039
    0x12020a0807150908070f12170103060b04020702030f07152c010504050406080313090c02060f04050c041d01060b03010b04031e23010606020604030e090a0615090e0108030301 76
    0x72083c000600b6614001031100410511820f600340c014010034100ca181310000c1c005483e1148140d101544401c07002006000140031a4011600420040c0c00142801c0f03099000c24074185581180b0300fa6940000c0e000c00480e01405506d403202d4046252041950034903041d0f0307600c5a0340000c603480284121800c06040c43c0d109105603401400003c00500241380d848140a44a0380300c401031102d03003500418013081402c0360340181e00d003000d060707402001c1c940e03070f0125031840110f40a08202d4090040c51681550303070340c850041c04480710400200d682040e5413804400e00712000756004014000042c00104282500102518112900150308201c0240001c199107403034516a0402042e1120366003c4190b02c500402401007000b80c0240200b10301ca450305003d03643c1e40c1084500400003810101030700c800d4208030076443d40148000c480419400d45032414a10a0302c103600b00d0700001000f8100420500901c0c4202e140103240740350196282d541421004003850100744400e41c1340a486501d100b96898 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 500383462 1250 500382212 500382221
    0x30906101d0106110f030f043f030509130203010e070806210307140606011101060311040902040e0d0206070e04050f0a0c0207152001151710050a0203010312020a080715 74
    0x1a1900240d1f9902c141d0001d2086480e0003e02030020100ca12440b410610000c0c800c3d119030403030801c40c1320441c034224560700f19400124424200c0401000380f1003444203032503c0c401d541410703290784405a12507040401c1d02000803001030081d001c001d0789c3d0051007c25294000581b220038051f81c0d8500c04941c450031250314520a0a00c0107201504224190700c00c03020200341240034450999a4140d03c4441601150903a890742c007003e8541d40d5220382f0900980f070158480b510b02072000e0004544050404442030619542600c102c3c003581100040200d075550007008010700300d02c2100c04014a00b000c000319140080014422402e0070345c0c640100000324000c018031001031004903000d020000f14174030010304206405000d1090184010011030503000c041c0101c2080164810318001d8540c0f4001d100880640c0284403000c840c01039143d0049100d21a025091041e480d0315805a900e501d145414030550b070845200e1401c640000303a0b4100003485c4841140d100540200f1042c055071040c462010050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 500384712 1250 500383462 500383483
    0x30c0509090705310302150a05030c0717120f1608040f020402041a070507090c08040f02040b04111803070302061204030905090a090b0702071a0309030906030906101d010611 76
    0x1600c00c55142541c11441c944c42e4800d0341e10070358070b40b03940c011586103152090082c40081800301e00d082c00042d03441650300c8068244c1d11300079048000c500c0c402c414100d41d1903000b011240e01104400302041154400c42008941011700304400f0030b200e070440c14000f800030401900040c40c84a004d454801036688a405840c0030b800c000f0340c800c04134030142c0034440345a805803c0c2260310380500c0e0b400150707280c1144035042601d05581c0720a082c50380c13140e9a4480e211031f1054101d921527030316690320003076031203d00c00c2c40d031040c1651031029560000740c80c41e0780081406611551088e40180000e00060f00c615050365055425021014482e4a5a107015103d224054000035084005e010401c07101c500e07170b5003100703941502890740030080341c80c4c480c401c90321402d403030040051210341c40100b03070414501d8000031944104681c0a4a041250010016204d9402034442c102c1710361040b8144101030310300c041104000c002d15a09400045403d01c21280c0510051150714140542d585d0106c649010a00030300111 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 500385962 1250 500384712 500384767
    0x9060507021f0207150c020d030e03010f05070e01020f010501060f18030210120506010905010503011203120518070b030f0414190521090d08280807030c0509090705 72
    0xe0300c2d00c01e200299540d134281324005201c0104031040403558000c4084041054014082c1d613030f510072030380b4180d440d04404000245c042d9a10250858601d42e80e100d004e0007004e103596404054648070000919142c0f2802600314680d140c440104002500f008521054080d142040c00010010ba10001c8407641c0903030010f0341200c00e1514160701c490380079100080c40c00342410200001c0c0c03118001141c0107802401441d02003201003005001c032400366050780392030394442c0c1b41540100c1809960341c001c1d45c40030340d000114500102200700e94a0402d000e02c0001c0c0a00940640c114a00312030084d44220f400b030005444600009010f500c000014405840340141c0c2c0c0035000c444909070325040b17690319110154602044a13554401004c03001500494002e924018201002c120300c60315040010340c00003600014419040b030200c040c607288400080034500082d19401d500703140450003d400c4d599050401402c004c02046112942e07561010800d03000010b0345409915904070200031804a08040c403003d48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 500387212 1250 500385962 500386009
    0x15030a050303090706031b0207031e050a0803060301060608102619020405010f0e181903050406090929030313080304050f090c0a03050c0412050c01021b010906050702 73
    0x15043d8000841c1d00850300169000c20540300e6004540c104450704962800c01a00071801c01c01c04107141d4440b031480741902401c06000e4484d00ea03070f00c1e07151004035a412541d440021080007210f18080c802c1800428842c01c00600c1c40c9030482c1c0f0801402c1c000d000e91003003450300154401110041600b031007420b0b000902142c090740000d10209031002e2030123100700e1041d4184400480d020000301010000c0b20400503982c0708503210341c11401030041055030421490310450000391445e03401700002d50f2030640207807691a915410040001c0040001d50021000c1a042140c44040c80324056150310316140c0840000003200140400203003180304d14204510b0030708158030301051121020004100700c840440ea40c2491051400070700c11846000c0b0f460381c1c00b43e1414030500f00b0761030282d0070241d8041880c3c88010318290301d416140d089030746110700540d43c0d9405540250075550701000102e4081c10810000e20100c1c3c44140000d24400007409200708001c07000c2842411502d03078200070741403000124620700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 500388462 1250 500387212 500387221
    0x5091222061809020c120304060905033006060a120e0105090d12150515040305060a09030f0206060a1511010c030b010909051302210f0c03120f0315030a050303 70
    0x400b845242d2592414a42e240c1d50b00290040303041c800c40d5883c8290001401030301c0c40007030b400502a00700070010380d040e54440080400060060008021140c1c054200c402103508500ca00840410f1142c01380340c1c50040c600c04d001c00c580e142c1d8161650066149000b0b40c0e40b050035103810014082c00012411070b90300306818059070003004108c003000c3c07400a13a1484144401d280742c10b415658482414901c21645400a103d00e080040000c89058241051145042d85d01d82d074682c505601101d00608003651140d84404060f4000403101c080d1815100a004904000001580e07080041c41105802400005502c021070b00905080165201c1c2da8020028001c0c200c101501030300d141d100341400a0282180400c21b50941c0c82414041e2458586407018600c161707090020f508000c12640c2c5a0210702c0f01201082c8204100c600c52009a0708007500d0742c12000c000f403515019825090304a803510030300c1040329080c1750b00d0039a688145219004102110482c02080c00d0006005002d88680030000410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 500389712 1250 500388462 500388467
    0x6190905210d0e0c06040306020922050f0c0901020c0427050601082a0409030e0d14070b090102060f0c0f040b0901180e0708150607061e0509122206 65
    0x341039000550b0b80a009550581c442192070310350701d40f595580080140414400305030194058010000701800280100b003052003404003a1020380640040d860302c1c2c400b013015444071147d25a070080c0c03d0341502070504a1180011b501c40042e40c2c0380710b00079a80c9011114030304c0b603d01103a00412a032049080d03403000b0780d8103001c1d84802090103010b8141c03040840c540c440c089030520a000070107002c243c400040f40c4100801c40640312200703041e0200f1040c0d8054000c00c0d9600c0c584510614854183c10a44a000c1010507091103410f0780b0051848a01b40507440d0244d030045151940850503500f400c3c510782e603650300c001c600c2c0111031103132104c6080070a010400e110110000c05a15038242c90b20f40c1141500513014083c048a40a07025042c0340d12004034041900440303d20b90031030700d890319506102176104081103ea0b00724001c10394880c1d4a502143c40005000c0d10085102a0907500501407440c1440d04c0981d10403016240210b40c44000a1941d02c4400d400050700d2840c142c0b008052500c1c1c0d03902da00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 500390962 1250 500389712 500389717
    0x806030a0f0c21120e060a05071a0a090b01141c02130203041203060b04060c0b0702011b05180a0f0b0d020c030307031d010504150c0c050a0812090619090521 69
    0x4070b0b030700100e200907821000d01420704101000c00c000d0105240041521048902e42c0227800212052b0380000c0300143c0c11414865514803405c29001e00150914050030403100c2124181e102d00c025600d6076880441a072a05101c0d0344064038038a0001040c4001c1d48085050000c0b544010788500d803020007403104000e0358841101800005035410f00900351248c80e24100e51007580300307180106296044290004e403618541035800711041c000060701c511042d03022900c09024402e0480020400139805228000150b080c80c030450b403c1e513540010a041026021401060740501a200f000220b030440c02058035030115000000100c06403034403400d10701009005800c04c0c07e407002c13209441035003240e041a814414240b040390018440414421510440c1c0010041001c4540c01c1281c0b0061810115a04000d20321015100c0d400b40c5503103401c09112030325009000303004001c95070030110030b10441504482c511152407900800c00143d1491500e0500d05c2d14001b007a0310078600308401c91412418034201c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 500392212 1250 500390962 500391029
    0x305010207110a0803120a0b0d1b180e19081b16050d0b0a11040302030303011508100803040332010606020105090304030c15020102120a0c030c0806030a0f0c 69
    0x8011112544030130025849000c0da1000c484a41904400a004180160010714003c032000d0900d19400c5401d840f81031800941c14804408031100e498200103a9031950424503083d100301c2002c00a24480145894503000400d0555412240300402030040c04240300846008180041101080840004080340c8a161315801d0780e8400114840c00900c0b8240b1b80403013551181d02c82860726142c0d85100d1110001d020b035580030305d0601c5007808040016242000158003800b15064021075844090f2001002900c0051002134102d2840b4010000400700005030f8003940d610054203550b0b03c00b00668907440e04110420807101d044c1071081084480d1040d400311098503940d90007440581d80d02040965284114440103000f941c114404008a8250008104c0c100a80348000752030711412084002c1c031312905540002080703a41e02c600441060305071050440e504003030700300350f422403a040340041c0d25000790640140000e0b5429200c182040a03030414a8051b0920380b034180f068480c4001c0c0b0380a84100e83c007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 500393462 1250 500392212 500392219
    0xf030c010c020613030804060509070812030f070c02090411040b0d0803100b19030209030f011410050103110315030a0b07120b0d020f01050a051204032c06040b0a09030501020711 78
    0x1000310304c1941c41d01e242605990340540700c070302c0d8984913a034407000103040c02080c2d071115009216020030603142c2423005880030200c02003030a03201e04058858102c4020003404c0d5405201007503030000c0058075402d2000d980140c104450300071600490020401174691600783d540c0c01a400d0b0504820010540095806a076181c1420b07641c3c40d88641444240d4800d141d021603241da0186500103c40744260001c2c8400310026059503850307004a20060b0945080a1310068040346100c20003940308180320392040281400d103020b02040d480443e210100384005800741d00110305000d540d0203680c07020041c0208859209800d607455250a40000f00100750405050110300d0500400300001e2508520308401503400030700e07904c0d240c88048010b503429440b83c0044800c0c4071060041c00d81154407806014401c9000340c88606440030300c0103004071807542d0b04080395a020401c00032481c40e91502000da40c1a1410002215520a00c481d0107641c0c1044070750004001e90b0002446804214100f05680e0400e182907 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 500394712 1250 500393462 500393473
    0xa0f06091e03020d11100b010207120f1401180b041406070806100c021e190321030218220203400b04080903060f07110706120e0f030c010c02 62
    0x300071a89071700f801801c481c585c0d10040420442c40001c0d48403803410481401140e0100341e44003400038101d0540e40c420b5514040910031075060041005043c1c21809125008101181c101c45076a99a00c1c0c031008060411041a00014204000500e08110358044103003140e04624210f800101a07000c1101d50030f000342a01307400c0b004d01c180103810014240f40d00410302e400c80b0805164402c01490025030256004480034003018070003807900644000703180150f141c80100728100d80c0024020641003901d808141c81000002c1d0401e401203046102c11800311500b044900b4184103540210085c0c00391603005a1002050040300c140c2101c80000d4a51110000b00d200300a0b0b04140305216241c0b01c200451841a500b200000b0300c030601201d40c024071400f5203d080610b06804685042011100182080c1610302403050f0507820036601d004211001000381070701303804e01c035008002e80302e401c03148615a901e031000c200c030101080c802d1421448000d001c490316990707410b031a5800782c0000b075417400c00340c001d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 500395962 1250 500394712 500394733
    0x50616030c020a08040e07020a0c080d0e01170f0604020910080115021c0302130e04050318040c1209020f030f0d1103030601200c030d11070b0c0a0f06091e0302 70
    0x45400f18000f50003c99041c201440d2071000312601c11b008085000314028848540002200101c00001404890004160312650396002514110f100444036040c001c1150251601d6208000029444280b020140340540c40d4200400d01034082c0003444c6a01c482850300d0703442a554410040c1d03040300c415050481c0c02d80d00c1243c044e41c0710901c2821410708822800c061300403d600036001429040c42a190b60001c0517039980403007000706001d64003181c00d9040040d03842246080b00982c5075456008030350402045000030005040c01100c941d0103030f100342d110080c400030f5503038103640290080006420340d85824081ca000c942ca0f410500c00c4500442d514010300110604000141c0b03104a2041c0c440585020008140450308bc42e11409620f85201300f80d0ba4940d1610705202c2c004a0b91981d403038000280d08032200c10b600384142c580210540207014044c520001100280107101660080034a1342001c020303080041c081e000c07451703000c1c0802d0b1207000c02c0e4807401c0c1e00d59580d81a95002e58290b0301741e01c26 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 500397212 1250 500395962 500395967
    0xc030702032103040f170a08060102010c020d0e042d052202030a080f07061b020f01091112070b3015040c030609060b2d07080d0207050616030c 63
    0x3202c903120031205001d000041c0065240c00c170b0200440d0203004c07943d01645000d48150b4442e03200001190028441c4024008596024094401080b0150000d8803a6410800c03001740341d480c27102070103842170303844ec0c0c01c0f028110740700c0c0d480c0007043e060040104048282e10380810007a000a5035203240c0c801203078410204a00e0f46162103040d43c1c2d4020302034000c6800716100c203503160300010100b00301c0c07600c00c101c1d03180000c072075120718039541e480440303800524480200040e041c810b0314485070201e641410112800030741500550703004071404440110a68881a44091070410140c000b800b0440c2c0c00295004101d44404226081c4030b019803041ca601c1522042c204141e200a40b185003c0381d43c00d55000c040c2d03290542008031800107500c1c000a02c3d03581ca14400c0140e0788907911030103aa02000400d452030702000c56184150301010480a07440702300b40a80c143c0c45202d143c034043c0400c180441c1c51030050344160103c40c0d00b5508441280c2690420b903d10b030740b004801540700310110b8030b0992884002c1e0f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 500398462 1250 500397212 500397253
    0x310060504033302070f0c0504200c0304030206030403030605090a0e0618011b0c050f1606030b03030f04061805100c020f0f06031801151206020a02120c03070203 71
    0x7a0300a166a081c0048406142c1070750004040c000440c5685800f40358807462a4406000d0700c5001d480b000e211600d060070300381790007202900818000c034102007840f80310841035030447c00d60082d10b080482d0360701010f068940c00c5005a40009501c030740004144004d241d0f05400c4030042d14021110203540d51111802d0300103c1d0101500b10906810003000504090340139001e1522280c001d000124814508080b508101008281050f020030000c42c00941800b004200d0514410320328401802c0d0003048101083c10209540300c4d2004050700d58048080640307061040d02d40308000c683c211a212520b484000d4598840714020210703d40300380200240900e0303d04030044065196440d030400d038a4482e003d100c000340c40602030301c0d0040c1c100e0030364144948444000310b21818220310a0707601040d0110002c0c0c25604080040c2c0e607a0194101c09100c0c400d40b59201c00744641d40000010707a00c984ca082c0c20b0341040c088043c1c2c460f1021f40420000c00945c408801401c06074400c40a6581003440080001c5084 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 500399712 1250 500398462 500398469
    0x5010c020a06050307030f0608030a1404030b1314010227031614060c030304080306180c030135030c07060215160c0602030c04031a07080a0c03090212030310060504 72
    0xc05a003010003005004100540e000380207446c0101d10312107181031420a4410541c00902964000141400300d15031202c200c96102c2da0052801d45007a241d0344600c244844080d00d0388858005040403901004080e0700751703401d401d2680d0001d54440d442c40700401001c9484903100e403041c11624012190524000c9240010160b915040d114190b04007180f010705001d454414a1f041001041703981d02d502d5040024501ca02d200d1501559645840306c1804040070a09502144107960780b014000c04581280070780f8150b5041c03040081c0f580c8904084d0580840e011202e1044904401c08640301169000c402040800590710880b140180d4851040f80d88070001944000c504140b00c000c5042d070301501d004110140040e1034070040031001034030707010101d03842560182000c600014081040011114400000d01c90204c4101c02038541940e0242074054003c2030610620340c5c9070758880e4818060390042c00d01c0d0350040c0c05c59505014844031160360398416101034201c0c1c811340d4000a40f0303510800446041c3c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 500400962 1250 500399712 500399719
    0x1140603101505390d0504090507050702041806060b0408060402060a05120c0909150607020405042103061e0b0a030b0105071a06280e04050708070303110705010c02 72
    0x80900d0428070441d548404800201086010881c0c403815601516100c0e410075813081c00500340400203d10310404107202094886280c0041410951441d001000d483c2210800d041c00b1401da964800215014841c010000750f029250071101000010206503203608244907550800816445401d00c0004d80aa4840d80036141d00800001f001424044085c020b40d05d480d042181c14803540000c4024091000c90380c64101c4080070581d02e450b4034100e40c52035000340d61003040c2e4480f0041e100c007090709481105070282c0515151404603080102c51107042542c8e03031001141c4855210300d80780080c090061841001842924400c40b54031481d400711208041f186141c1c1481d00c0d00000c010160003070702143c20070754140b1405000442c042403004a0211002500000b000b8541c030f807071007c00c1690040041088045d2104c1202c004c4564000c2d0503250540f04032115000342c41c2d46038684540790000c03581000190f802824000810150410b502034a00c0c03064000756661a80c50b5401100c24010542c17020b9807 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 500402212 1250 500400962 500400991
    0x90207150c050306210f07060228030801031e02060d150f050325080d11010e15011403010e1b03060705090307152601140108010302030c090601110d0801140603 70
    0x4101a1741804100c1004045e4269141955400719050a00c1069413144015800c10307001315211460400c0c04245a94a001d5103020545841c5c60042180e00b05000c0104054048021880f511383c8100070142c04130341c010b0405540d540303200750140180060f903034003800360111414041143d080001c1d00000b558009002407960a90200014001400c154000c41d070300b1202d00d030007054103003085c408100e4075960b980b03600404200c4a42c0c4035084541e990703032041d0b16800c41040030003003840017550a0b044601c1e029079500c0480031500001e0040c041d0156003070a0740300355091a11007074080c9290301c441c032008500f601c4071651419000e41e61840758420f982c1e8581c001101c244200d0380f07040200072801a641c6807030491503607861030200104a61850f100070144500e401041542450320b6408a807207020710300427200d07500d50360200707980d00220f0403148d20442aa400151246c4d200d00c0c000142c460404046600744803889102500e20082801400b4211004031104006410840112805002121031081 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 500403462 1250 500402212 500402239
    0x3070605180607020a02130c0f030f0b03060109050609010f320904060e0d02010b0307152109150515040c02030f0a0e130e030f0d0204090207150c050306 67
    0x50050800030040c0000051070551400031000401409100707848513002002107929900401c10141c403000601c4800500309003000c428150f01039a00c1000341d0160801203450100c3d03840f294064425095043c0d01480380c000001040811a08080c0c000c02066540a032181d80303682200e1100c85080c0201c060104450106600c44104c00d00ea06404410b0044c918604040c000c000858510b800d45054940315101d98820340c04aa040c010380070302800038002001400a80808242c40d0000ca2054203080d0410903c511502030248280c0030500e10648611115103040004110092000040503540303101d0361004a00305851601c110750048181c42407039041e0794170f0041000013a100c10681d40c011400280000c0030042643c4000d400403400c0760b03c450390401c4044080c0048610104d01c5a24124140f00b9003410f1002c2c0842201c1c8218004200d00b60f0b030b0310044a803000a4421a4044040b9510008400c0107024900035502c0b0081e190350418011446401000c407003030300090f01c030710750300c07110320b0b084c50 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 500404712 1250 500403462 500403473
    0x120903030207140a090e030c070f291b070611030703050403060c09180c170c0703050c0f150114150d091b030b0412020120031905040309051206090307 66
    0xd04960350020a40c113040c61326030b0b42040a1b44c4c2ca00b100e40c03e043d071000c80c00c044080c40600c006130103408029110101145070255206921030040d10300005d09461841c0603a1001c200c4013110168100c03d5003030380c0003252015020341c0d947d016201d0040011701c03085000c2e03201c000c0402122560703501035a0b494101400c68944000520181755054103210303840800003010f241d01c00511284024030000000d44008111004c0c203141003c031040400c0300101350410140c3c65042c010b80300c18a405260107502c810b145160300b0320340592207525002a06c40d92440c000c1580051041d2810b80c0d519804282264074006d00388590f000201e0b0040400100621101c0c84008266110104e40b50041ca00350324820402050b254034241c3c190001d4500c000c41c8410007080c090524041e1060308101c0c0700800c15107460390000740c1c2a0a5000001810810010100c0c00e540f1019000701107100705800d0070440d6091a14028013100c042d0b100d0036003d1420b200848840d40c40c04030380c844c400e40841d03002c0d5251891642e2403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 500405962 1250 500404712 500404739
    0xc0c0f01030b0d080414030c0d06020c0f1002040906210b0601140c0a030906080f0a05040c03200a1e03060b01050f0d0b13020702030a231207120903030207 68
    0x1994101580d4000c1c1c19030070354a0344607507106140100b18190f640c0d07003040314040a401d0454112030181d4810014031002d0f445400c540001d481e004000142c0b9140c104070342d2828512011031816040c8942040740081032240d9000f8011900d103450b00304000da9880b100c010740174201a410020182790854010040f40420302e440c5c1e0700450500d0f2014130954800ca103001c20360000c2c203800c200c5a0010030b140b000c040e00101102c3c0504241d0400024502c2c10700d00d41c00c8070040c000c14142403151204085810050030300100f001950b40419104d880e9a01c414040751707640100186c1610810042c02c0014114200c3c200d0601001c40d80380450001c2400c0d9201d0741c6c0a826060040350400c8404c00c142c1a5030a2060090014030910103c0030801145841c10040000f80c0e503401c810b5010305c1048840010713640015540070700381d03010003500c807010710000c5c900494000f00481e1020b64003502c1c605c2c441c00802ca800030600e881c031800341d0040a4102c0301c0d00f00d03808100c0707001c002c016038010b100078031690444503107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 500407212 1250 500405962 500405989
    0xa0807140c01112d010c09031a0c040b0c0321160e0a0b0f0712120c08010b03070e010c0c06233109140430030f0207021206160201020c0c 60
    0xa681d250b6403c0c40400b0f401c541601b003000c80003da501e40b0038070802811030000e030101c03803401c09aa441801c080052880ba0311443c40f84100400001840441e640c0c428415250382c540b903c4521085540d24948950305081c0c11105000d00014030044a603407075001340c20400e4406009884802e005081c5803040354907038404045054500c000340210f40004a100300c02c0507030002c19640d4170301c0806203c10244165900007d0700c00500150300d0050150700669419a5032020080c1307000c0c0c4001d0003260050f40c101144a40241040d854020003041c2950000e4803070b20b968002d613042d010030140038104d0410600500b007440d180821400d51002890100610f4100c06c8c001c054170444410382d88032505400c84418084003180916218100000d10000c2c0c0918911900a0402c001303d4030790050114101d42d45180281c400d16130b45544404a4101c140e05070f034880e50340545054201d892440b030350380c0d079000e0841d00681c645884030b0301c200c001d62060098458001d5002d00620480f1200400c018112101c00d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 500408462 1250 500407212 500407273
    0x3140a120537060e100e2512021b030301060f0206040203060105040e030c06011d06040b13050c302521050f04150905100e0a0807140c0111 61
    0x3034010a4082442c0b007a54001d038441481c0b0485c01d441c105913030320384100082044601c80014410043c0071900300301a000400c40c01c0ca8a08054215211444000d00074200c08060000c0380c0d00d904c101065002004605a45242e2582804e2691500d07040341d8681088078025050380104004118078200b0360441c840f000e01000c02d40b81002d00240005192400076480604480402c038011040340f00d01030441500480290340900100b000c00010039060100c1207400400395075554001841589170724140c40205803803003042c4030b900000d20000700011801e0407101400f070103c940422000c12201c08844140030400f0800b540110409406842083c1c0214404021031402d8403104414500b82c400ca5100341507100102c811424282010b900711045401c008131154034018402010600000d04011541d081880120744d512030b4203a541d04005000100800504001c6080002c115041a000106024800491703d8191007031004403807010306000d4008180d004082100c0c11601d00c42c103412100707140c04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 500409712 1250 500408462 500408471
    0x11100201020f03040b01030c0609050d0b09070b0d0504020901092a050708041e09020c0c090612030c150a06180902030a020a18050f06150703140a120537 67
    0xc8041c4402c56108075801c96080d00144014020494a080340a0203452245410540740707060030f010a1401e001c01c0f101508413912040081d802c0142086510040c001d00b0008549501900c000310010307103015901248614600d80020403c52814858420403c5013410b100d001107000303040c1060f0344c00c404480710040080400c510008141c0c080c00500080880e103509405044201c48820600c40c400c0c1c0000c0c046e14010040d90070b54000c0010304020403807046540031803540b10701c400604208101400f04442e03020221305091103400c04111070a0103082c4201c4481c0700c1e5030b01ca01207011650385000322009071010a003139041a45880d0710010841e440507086a030100310355000155092407941c00103849075184182210107985074010b023900101a148444440c1c201000041c5001d0348941105000b0800443c0140900d8802c41100740307100440d4203415513681101b080100402c40c00044002d506052901040100c03511980ba038100c00c42032124480c17841c60b0b00c0b102003a1420025040038885844 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 500410962 1250 500409712 500409727
    0x50a0209040f030e04090203030910020f0610060f0f080c03040f020901080609100504050d080c0d050a02030a0c0e030d122c0f061302042c0115121110020102 69
    0x101419280502e000e99441502100d0502d40100010040c9040c14021400d0040300c90050310000f0a4401844048601d41d0b90f04102207000ca00c4e05c035108130051000e215060500092a68401c07200080d90501d551b44a1f45825105d0241c55030451200e00c900000c11200000344405c0c0e07004003030b54019100e4107402500d100781ba000910580c00a80045105401a205200c112803081004802e541301c414410f00451400e903d6941d203510a030031f819018041c2c0480094030600201017125500a020a020441c034201000410000c0d0402c55203040020724011081c80000d014800c841c500c02c0300107005000c1e114402d101151a1421a55600c41040d200d05104020f01001c2c0001d40b648000030740742c50060000b880440c0e00c0c3c422010640c00c82a00224203119104100d0b04400d41d106405640208804400c01020702101c40c0c0c0f00c1c90840c00a00c1102a0020200107411903481c40c402c0454101619464030b0011060f00700c00080146002c1da090f1180381e180c1444400b095006071640001403c0c01c29 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 500412212 1250 500410962 500410969
    0xb0d1b1508370e1b03100905160e010302030d050c03090d0204060810020304020f090105010f0e13050c030f0903130501030b040e010207030c060c0201060e0f1503120a0e15040e04050a02 81
    0x160711041e1402c940ca5092000c4882e8080003c2e41848011422413a0000c500c4008a0b85840c1810b100c034050a0711401407e061000401a5035034440300700e520114055502c139084190540e0070f0204030f100340900b000700c0300b406224409031a400c11110000d14a0840c00700100004942c4100049800540700c007400109000706101d80003160014040160b40c030b1400d8030401007021032505c0b105100c1e1980f900103106507603020702040910101400d061148228860000709000038603903d09102600f8481000038a0030200003460181c00c10080c0c4410740c0d00c4801c416500c078040d03006107040514844104000f00d6201e600040012080500000740c1c00e07960341c19103401c3ea48004000e80c04030b602c06038000304108140c459451100346610007042081d0904c281d04079562070160001021802c0701d404a030141d91000c40c5400030040040860380050312200c2600e00c1508034151010109601410710805030604809044048003a68620b81c6402d007000c0c80b043e51600b01420564a40c403880e160000141c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 500413462 1250 500412212 500412301
    0x902090f10090b0d0f110403030915110d0518180c07080d0e06070f030c0c020402090f09010e0a0612020306131403030c07020f031506130b0d1b1508 65
    0x3495154042902100901281c055800030b1b00401e02c441000c000c1040442c0e800f019200944002c2002c1c84000554440e003200c1203030480c9030700c140303a000708503445c9a80394100c001805c0403c0180c40c032105895031751040042601451450300d000c03101c1e503400100007210000041c501c4900c11000c0320304107503d0302c0c00001141d00300e111120090b440481844100d50700003100d098804140d00e018030a070000300000034104c0500500080c00b070790300840d0001c4d082d80c645005061030030020b041c2070780540c0d450b280811240c2c0262100ba002518021020070180c880e0720702003000913000740040c0300715103401185c0b4041141011040d0350900c02c01c02c0c041c08201c420700c001d50044070107030251034548003640108400307800c0324a01d080c401c0e48841c0407443c800d0419111a98004070803144122090b50240c140405010038525180d030045200b11101c00304a200b02c11404042400d0404264264654000c03040ca40741c0c11240c07102007040301c8001982c0135078040140ca00212300c0c0b07141c01000514220368803880c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 500414712 1250 500413462 500413477
    0x10902030702160f051801080d180510210e070b090301020c07030b01050a0f140f010e0a120b0a020c0a0b061804210503010f210f1b0902090f10090b 65
    0x1844c2000c0c10459440c0c4050140c03468054400c4482c4294540310f041c66480d80d45103441c40501c80141d4484181c088486070b680e0042101404200301441e00c0f100090440c10045c03200681c15401d094a00000d0082e8490640000760b00e00c0181425030820005180c142c0064040702c1d4550740801c000014181e09200c00c40065101b5031003140d50f54146010064806102d401c40000e42100384810401140c01006c201c03140729094a0a2a041c8441070040310603440c2018025001400500005029610118508c41031801156030000a031a8070840c90140e20854841b10385c0765005004c16000308244008140d044000101a00030f221052180869004403c071000e60706028a4000e100040120300c0e80e030205030199141c030920395810b0213084440c0f04240d015955403000c116a6070003000075481341c01d40140d90809000c4039216450b1501112150314409003840340c0025880018011119000f620b5184000030588088250510140700c3c9030b00181c004201000242280050400180c20050950 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 500415962 1250 500414712 500414729
    0x112020a270b1e1b07080d0e01080115090f06020a0309050f1005030916060305070f080613020d29010f0203090d0f050102091003060501090509010e040b070212042405030f01090203070216 82
    0x190340707080100c1e4100000390740b07c40d06120441881c1d40603a0703071040003941512000e00301300040d42031142085590070800d03044000000c0600c200847d04a8001610403a814400d44e81c15007110b851304203000525000c0c060254201c502c0d07600360b01d02103000744069a0b0040c225000c0700c04004020003441d00c0d0314440c3c0d0080b40401d5640d020710081039844030154081c9009401c00c1840c5081050100b41c42c1001a00c0240301c5940c0412490707000000c07504030141039030160b000e042581075503215001c500f82e401100540402c0b08241143c0c070303490011007a1008104c0043c041c000d21152030f07c030401003588440013110155400c0001610341c0e910181c107a64100f1581d900080e8184c2400c3c0058030a000715000b0a128030350100c0100501d1400d0641c241d0700561040c00305800b03444e1030001743e240202000070b908000f100480c0129154013412608004c91401d86d1920700e2840d4500b01c01c0d07138180b02c240c5e10403124141000042c05a01480e030003c5030480c545d481102c1c1801e207103810000400340c0c3c640140c1c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 500417212 1250 500415962 500415973
    0x120415050c0a090b0304240905010614030d02070f050112020d1505030111041818050303041b05060304150c12020c0615120307030305060112020a270b1e1b 68
    0x1242603104003c0e0000d4400342c884503186043ca5101d4124198007070700514000ca00106e0b01c0c0345a040241c000c082d00070f81c418024014285c6030818083c00c00901b040c001d000744100c0e90300d180340610006160044621a003d8508881d0134030004450801e8200010510242c003000804901e00283c49212044004004020342080c10002018252111305030810000b20081c04103000b03880f00320a062105c0940c0c420f000507052600c10189025504e0903401170183d010100401081c008428580e2032038030142e401e418015901ca004005a501007a60082d0040c00e014840b8551290682d00c001540d031114100040c0c110701e0109070005903404503c0078030450300500306110820664036055824a1000c0302c0c60200b4807007101245640307000700000641010b0701c0b840400c02c9039011700140340402220b24019555100d049202520340c4201091105072a8028006640080c5c00c900c504421342e0b00c0410a640307009000c050b200800141c02da404507007244200043d00401121070480d2180c401c400c4098034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 500418462 1250 500417212 500417227
    0x120c0109050f032a0a0f05030706050901051501121d0c030f0c240c0d0503010e06090c030c0c0c0402070609020a06090b042310090f09060803120415050c 67
    0x40c20055000e00044283c1d000307024126044000302c1010103440340c051984a803507054604010300e050500103015200700d44421084080c04400b20041030040d001c1d19090082c1c1d1250b90713041c1d00302c5004580349503000041c0780d4002115882a50903120b001c042036400f1030f01010f0040307500d40da41c48880b42000c00d40d10191014119041c02d204401c140c50108000c0c20f9440c001001003840004e089485035036107010018050450519a0241e580b0720061500700c424085107400d02500c941d00c01c2c041c00c0c14080300080000da00740340c12854a032280201f405d240703085840c4c000d80a101c3d1307006426142c20768080c00c0c0c1140d01c681c50740d01c00380107040c0c0120740c04114501140180302c84007980342c100301d04100e8224070502a00c40d0781d4044804540f011961198a00050040700c4805202d544040340d200d081c80c0b01c01010303a688052403170143c890031403400d40c0044d6502e1440c41200c5040c820700359243c00500417024034079090404203600a00411010b0101c01c02c101004040351012203090009007808100079 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 500419712 1250 500418462 500418473
    0x5090309010327060e10020d0209090c16061503021c060b010c0309031101050904090b04060b0f0d0210020c090a050703050c12040204050a150b040504050a0c08070f02120c0109 77
    0x107900f10401c44040c1c2401c1e815001c80403609101451002d4411a11000c2065102c1e0b802c0260004001440302c0854070303500c010189401075441803c000340310b6850390300030902e2042d030039007164410022502c05c40c203021030a656840142c004442c0305800d0700c0500a00002588510001c11650800c40d1960545031500c2d00d030031011907a10f142c215040045500ca81000643c02c001058103807074224a42c60f2040d201c0500480345403040c3e92609400505011403041004540c2241500581c0b00724024058494001c00b4081c04440842e400c036808603030802d0b40005030074643c030000700036503103032040c0c072184194200401d24442c001c0c0d410201c50340e41d650410601d2603061150719007101100c40d0385c070b20702800502c1c2a8800507002d4006031180da074800208101120680c0500003040300c2c042c0140c4038641d40d481585254206100d024080c03414100058031082040c810000c1c0700006032035601351512185405c0b03864000d0f5452403015441a030303102155510005001d40f54905800c3e00100b4240c2c2c0c00d107085c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 500420962 1250 500419712 500419721
    0x417070803091603030801120c150309030f0203030601092c040804092f0a0201060503012313080712111c1806020303180a150c0908030906030109090204020904050903090103 76
    0x52544805103e2010720000c4d911040c030340d0440e50024150300300d103c01030400030b2100c1c0c40c0d544401098101039004400b00c640503000104094013907110000064481c5000340d07141e1000f1104640002c4880b0014001e0b900c4c82049042c50b0010410450382d851076200c0b08540c00b4400351030548100742d021608001e0048070380603e5806440c184407010182d0b05499800110085022a82005038804900c9a40141c0300b54402030003408010003d005d41100107030300c09100101445d40c0100b046980b0001025100d80b80300c42a519948401071904d046126210f0400c080c2512145004201c140d031800002000304204903013036602800496807400060140160010151f6200d440f40744642ca0810003d194005c4180c07a841803200014030f003249411400242001141000248940d48041481541c82d4040d070007030840301515140c240c6555140e800d020ba07a40240c40d20b580d44214200b0040c49030007865007040304664400760000d410b00150070b0004e4240c0700125070f16482584007140030030707056905020b0f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 500422212 1250 500420962 500420983
    0x10e160c0f03050418060b0a120e07180b0d110904081e0301060807020f06220605150a0b0c060703270609050d030e061f0e0106020604020f09011409041707080309 71
    0x30400c1147d15041d40503100b0700034203c4100c188568903c451110391600c0d004160162202019146007640302e50f00e0702403568006040030007a501d8130500910500341a114203603080d0b00b0180980012100d04100498500000d0049896602c01e1181075020b48041c0f00400c1140812a545500e0390305081000704605c00090110085500c0490100080c2070041500c0f900000c41121a41a049010300b4101c0301c0e075203a40c4010442031812080002030701000b80e114225a80c01c0b03400c614171303640d84d4503007020074010070701d1000c2d4503007100700400c0318140607603c00302070703c502408074901c0c40c6102c4440010302001e202e81511926241c004074002c0000034070400005501600f02040490440c4480964880300144040d40102019080f081040044044800140300c0300030005030035a15600020b44901044d00d040b4000c014000807036019143c01000750741640d50b554100c814601d103000400420210180056510001c81c1340783e10505a0720000506480d80034607100c41d500d003803020f40c5515081d03a000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 500423462 1250 500422212 500422259
    0x20011a0a0308030604050604060b0c03130501020a0506191b05070b010b03090d0c050a0c0f0e060924010c0816030e091b1c05010303080703050906010e160c0f030504 72
    0x280501c000350844003500e0f0084800c3c0c0e0001070565490021400521980d00110b0f081040411550b01c030000010040100c00300f501000c031400d40da80c80c0166907d00d5042001440d5801c4071000270200100d4a20140c003603080074002041241d04446002c480481e000505d0000030400140d01044c00a441c0c0158018410031014914518280b202940c545402200c602c0c200003101c2500c4090010822042c102c5640042c5602c501603a07507460842c9800e031a00c1400348109020000031030a2400520f41c5201d17502c14048080120361641c0002181c90000e0349850601082440040100d080080a015240ca04c0f113021260210681006400c1c0121951018842d43c41401041204031725030170140c44800700d2854198540b40c504002e860110000c240e600c00851801d40004107041e07020700d4031405030b003090318104501d407240841d80d61078003024003400620042507008142e05022008125070107560b01e1501c961291510380e42d21a8401862070240c00040000c10207000b40d6082e412080c9000d01c140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 500424712 1250 500423462 500423479
    0x3020c0d140a030c0e04050a0e070803030408031501020f0604110307120807080322031e0507030212030903130b09040606020706021005040c122019031220011a 70
    0x18000c18030075108107800002095144d800c0415942d000b11426045860014005d211928060030860000d08000151107202e00c03507014000307400c1d880401203c4c0070ba50045002c5146658101d0b400c80700e2008009118114030419010940c2048184401402684241440048a90800c040510348074140d008021a042c2d0340412000091105003200c0c00d46600c14541600c0b030b070f035074201d01b25402031207220f283c4c2c10344110b0006010550b2100c0d0700c00b440d0f01031040303203000082950011a014094404000e0142e440401030540450f801e02c0070f168000c9251080300e01d030030003980c050121040d0550121542201c040343c0d41c80750f454640500406000740b407000b80380692600710300039912900d989200e003806030b5410210f000d00c03600c40c0c03840024003403a164000b4484414030704030421246030741803c5040f031b0380320050038840d180400d0955002c01154442d13040b0b89066440d401e841840c407a42c0780c400d211380701e174140c2c40e980352991007011403808803000001d10880760340408160360131074004203101e034942 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 500425962 1250 500424712 500424737
    0x90705090a090e0c0a0305030301030c0e04020d1103010f2d020307020613051507020c090f010b0d02091c0c03030810060c110102010f150f090603050a0b0403030b090703020c0d 77
    0x825400300c044400c18030012450304040340c0c3c01400d01080e0080b05400040025001c418000c0010041d4100d81c410141820a5661a5880c11050800381c80c000e600107030a8450034081800410f01d80f45000000b000000e10f8490000322104031400b48400c03015494800009040d02d04281c8010043d582c2c40540545c91403030412402510b44070010030195242d061403511070b051040401c68609003a04070008040541030a00e00a0b41e104e08214115125484840019041c541859002d904a0b2010b0160034100703120411100080d40100d1501c03078010f410481c6440c0018281d0020a40132030250405c5d844503400c5090041c56003034010400322108940030000c0040a5004095100301034220305804e00c0300c481c000040b80502100c941141c00c4a007064010500740700c60100d90811603c0100100d007031140c1e02d400740015608144800f4059821038122800400e002d10003c0341d10501c80e00e80092041181400142c5a003c03e954280000f81e01040501218000300403d0424828030704101e4401020f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 500427212 1250 500425962 500425969
    0xb0702010806011b0501020f0d05070306140d1406040b0708090f12030901090c0602030a0e010e0d1b0315090b01090912110309060f1801092d050301050f0609070509 72
    0x1070b110504020010550b480907005025103211115408002503680341c1c031032500111290400300705542400d1030540440d101170300070b20400c000c4541081c0c903001d41136040420404940c44005090352000500b01d2004180001400458030480c847c0500e15141d090401004040384001421101194006409181c004400140039403c8a00142c003040d80d03541d60040399409009040401480d00c1e01807c0e0214440b500480505003144040d6141030340b03078001c08011190021207684450304441d42d0710516001c10201810400642c090550095540d9500e658505681131010020842c0035036403110b41040000604519004001c2590309208440b4291113806030790640e80e4014042c06049510242090800d2007910b00d80310005181035160280200c14440a500050058450386c0d000c41d15800b4a40c0030314092002d6810500000680001c200c0307030450f003402c003485900201c44c0032103000605c9560901469100b074100a5144481d07007000c00a0010b0048040c10781e10a01c00c2c28464480b181d10b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 500428462 1250 500427212 500427227
    0x11a070f050730080f160f050c010c0803010e0a02040b0301030302010606080a0902030c0111100e1501090e060112030e0d060213060e151e0301081f0c0c03030203060f12010b09010b070201 82
    0x3c0c4c128503201d603109000401c0703030707554410310303649048030b40d210a003040602014003141c4030280d0181c426555400c00150044600c4203401100030802c107020710040c0103105e00d81650701d5204c070400c0301c018070302078868203c0121604241d00440050b91540300610a1541c000d0400e80c10481c0c5606c04c0c0100c0d80346600098540b8070480400c0c0c10850407a203071400004c1e00300018154a00209020030011042c00d00c10358680b20981400f4181140c52800041c3ca240c2502c142e24800300c2c0c1c41e02030300321a42001d0301d540513028a203000354208680742c0d01410a9035545503107480e90718451240180c1e02c1e9103080291a516000b6800001032281780c4911800765180c240c441055010084c030783c1640c1e28030b038107001100c58607030410030600180d01000103e03807a440000e90a40300308540912004005212140324266000e000c15000001d00100140001a0180d0051a006040140304006410790000440c3c50022051030b8141c1c681c0d11070201050741e06112800502408040c11007514010841d00040c1c10103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 500429712 1250 500428462 500428559
    0xc010c08040b03061504080a05010b060a02060105090910050703050402012304060302280225080703300203041802032208070b0a060603050606090108011a070f0507 72
    0x40b4000002412698511504c0648140c84c1030540303072119250015287c3d512841c1004491035840c10121a07400d10300301d01950b0071158954004c00d181da00302414000c255001034007140c0f113481750b4800f0a00c0704034640100c0f840760703041e50340000b81381c0780a0000501c04210743c00300303810242c0c100c28400d0074401c080c4115810f481d0b480c10b0240e40ca0620701141401c24410501e84841c0260813010742b0f0040e0b5010685201201000100c2c05000045070004007000c07840d480303281d6056010041c00c1000505603402013909140801d26510440e00b0441d058142e501d80e6200140180c02c000740034071800c600800c0d0010218403110f000c50951400f040007841303a035040040b0507000c1020021090810405208a46515500519440791070420750b003004050141c50140e080424200b0f0b0024140d4140001910321001051307549848503480e02c0010030390a01d600d80103060044e410040000071420a45529003224401c1c001010707003914100d031841710206c03402d0600360181040740220321142100021061030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 500430962 1250 500429712 500429729
    0xd03050c0906070f02041103150f04141608072a02151b0d0305040b16020106050604030c030b0108010507140901030605130b01030b060c0307030c150204170c010c0804 73
    0x458a030401400a140a0480c2190780404001400d104000360807100c43c030407a01c02c2d5020320084e041c410309100d10703006c11900341200e4561030003600200d01c0d0144c1b250401140140c07000402c0c6070f00c01000c4042c16400c641140c0d460301c2e46504100c003241e00041c12036001c0428a40401070100000e0000841c8041e030039002c4c01030700482c4442042d582d40341901c401000071022050342c0d8952091401e583c1558090700c11080c0e0080852a00c0710038024000c480c45141e1014040e0900ea541045483d04c138040342030100e045650b641c4010525444500c020400755000b110402c0e540740c039514121541e0a0143c21a1030a641402c0c00d02a42c02c1e04040c0000088983d040c00d20341f82c20b0f103c1d00407001040c080d40040d03445003041f840c1030780030042d030f51001e50410000c0e13905000d00e40075501405524800c0300c004840ba03610400c040000300703110f0079010040e144a2150b15420071800714483c4240d0300a60007501005400c40700320780c1c40c42010000540c03070590a00b0001041403058480310300c140601d1180615 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 500432212 1250 500430962 500430971
    0x30807110a32070f141819050a0e01051b1632060a202d0a0f0e01020615040f0f150506040803031b120906041e050d03 52
    0x1c80e01d202d1040005814240070081d00220341e915956a56048180700b800c0015000030030100d0301c0032622048281030500a01010030010070034072018104800244112038200c02c0409109043c00c0034042c007401840004008590311850003482801c4440203411031003140da984903c0c00c402140c00e07082c0d640e07118100c0000103600545060881e505c0305400344a480e45030380140041c4184c8072401b404d500c078100c0c900866500d503030303120b070f00300b088580701141a050f00380d801c0c01210551403444010301c1d004078101c00f011200c0c40c00c1b001c10070f9610552181031a14540214004e810103500030449000081240390103000e00c818000040d4480001030f1040c141c045600e0742000c215210b13038014400d4041110003c2050403c030440c0980180244030802c940078485d03140000e0949841c030190b4042e595040c026500e1a01c0f903c10303010714840c2812140718056000e12150800c20500d01d0303618414082e26001e0041494180b60001403280c910000c84003908262060002140c3c00080380d01c1851124100001e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 500433462 1250 500432212 500432243
    0x904060513050d1205011527081b1203040303080a0207030c120f02060105100909020d0605150c0c040905210415020c030c030c0603130c0b030106030504030807110a 72
    0x5228409034800641144038800000c4100c5512200300c10303001c413624008001590300c54404000e0900c1d055580c000258040151808122094550b41d94804140b0490044c443c0c0d58903106081808203074818070003a03003400c0218401d0070f000310072900004d00280554075007800c50340d018140302c001900c4015220b6020450004140c010080010995004500003409543c98640200803105041180006000310000010f003170418810066210016440d56102141840d480d0f0000750403201c02c04403869100d9900040307e460307030302e503c0044510343c40d06541d86179100300c1c80904d0401403801042c0250b2400070f11202003200410302120005d81d00046c50562003003800c180b003031070050b60800f0140d1501c62034400c48454000990304003041c1d05400351224070000030105501c40d0000300200342c01c07020070400213500c04110f400081503184900e1922100d01d0321160341d540c0c40d80090f00050007085d035540a01c0249900702601d564491618541000200f44140d415a00e50302c003454014443c00ca02d4010301c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 500434712 1250 500433462 500433481
    0x20705031201080f07050102010b010f050d0b0402070503071b0b16020312030702150906070f0f0302041e140a05060d090302030c0607030c1112040b070201021606030c0e0f09040605 79
    0x442021540300a801e185584aa105588403004400c100c40584183d400001e02c5500601a0082781d0505841d4106080c1038070b84191384a521200200443e2640d07815500c1d0682d8892001d00380c0d4031301803801580c40704041d142501c5103000c00900c01030752911f03058013045107400c10000c5800f910f41400a00c0840507051001c81e18080c0441c40d5007402031070100400c02c210381c1c005200c610b06800e2403143d40c1c55464105e0000d07180ca00544201e400180c1103001694400e000d03001214242e11f26240052625503202103200b40c0c54284010202040110503003000700140c03a1030304401c0400c0031a104140c0d2881d010009105200341020300038256283e250f01000e05000340107550042242038280c4525240104d0010300800320485420081446c3d80424100c0710381c000740840e248107243c14a0381c038041c100741d0120103940042c0b07002c13070461041030901c03036601246e00c40d00f1000f0079043d100481c0814600c500545031403d0021840e001d052010211a40d0365918402282c01c540c104000056075101d26200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 500435962 1250 500434712 500434717
    0x3060a09050a0b04110f010e060901260901150801180213060b1305030d0f020303280e15220f030e030703051b040b010804120504150804060f051902070503 68
    0x240500303c81104110621466422452580c00d00b00d496034011840400150746407001001c3c41d6130802400c1c4000d41c9154001c4402c0c1464021210001c01460a040360650b4010412254504542d442d18810604840798000880103010b0010090101c01d880050000e6580e580c154064450400102044e5030307614680e02240c06880700d0620b0f240c4e00c4402ca910508200080d2041c1030180c4a000d0901c60312522916600c499100242c0c0a50315544554081c0f14400c520000c2c103002034410000c038401c0007a018030031101e405880c140a403007410b04004200264a1005005000140c0c4034140c14075540d89440c0200c2c480d590090300350000100701c1c20708541d0010106607007601489000404407d02c1070002d0b10b8619140680c50908800c2006c0040c4016a180010002d0100d0b01c0c40d00440c0001d121200b000542041d546859402c01da9500008a85c040403501c400001c541104140000d210540c040c082c000c040e120014005d0342400c0c1042c0c102100a4004101d03119070124000042000a008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 500437212 1250 500435962 500435983
    0xf060b1c02160c0e07140f03070504120b06010806010509012001060816150e09071b080d090b0109021e0705030f0f09090f04080301061803020301230702010b03060a0905 74
    0x4600c80d40b0030991a0034081c80c2c00a0103110780c41d08110000900c03c511038116520a030044040c19810304510302d100c040550409404074091200c1400b01190940000340b44441941c0216500203580c10107000250407000050201d50411504004100756640c01c00b000c3e5044225201c03400c0c8140d010400c02600410f500e41224040c0d01440c100c180b01e80058842c0c510940c1c08088500400350703c89002951384100346244181c10115034000200f0281c0211724015500b80501071080450310dd50744c40340440d900a800c10300130325560f180800c041c008002e580314050401c00200318500722500384050b07103041d125800003003590000100a820030a0520607162210f0944d29065281d00001c0b1740d021454208804150040880c0c0001a618140310742060740119040540305140d6420940100d60441c000754404820310042400000180c400344100301e02200305546900c40b80c82c0d506490325078880050520781c00c5a04140941e800303660042150347d04191103180c001404803071440c280e8200215000f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 500438462 1250 500437212 500437237
    0xa0e0a0816030c02120115080f0c1e04060b0c010e060603280803090114060d0209010510030e0609060106020f03070309050118030605100303030b150909040204270302010f060b1c02 79
    0x1840b40898a030542203400c07081034142e031f03000c440750315646041e903a9070031003514800319444040c0346085400d10340503041525011140c2c0c1c0c2038ac1e1541002040c29540e890b4800341004500240082c101142849030740056010380000c0c04044c20300c04d00181c1e561800020490742543c1503405c81d07070030350b8a82c509040c50641c0440c0ca6900c918000140038004c0c006491180c070510224000034409240a283c1652065030007030452140b64240b10a00c401e03100c9540c440c00070b043c2d851203254010030301088601d1240d0541e200900b240d606040c4020705000410701c00007441d170b00c14094500000c4d001158001a50001c0c078110601c050745803940030080740698006012a40342c181030002c0d9800400f00c040940b8000e07281448805c6150060145881241c4524002d580381440000c220b81340c81e884480c0c006000030000f03d0400303030090686040c0100300220000256500800d00200f640a00400c4400000341e1400c004061070403000444622400f5200ba602d1400302c40100c05510740c2d81d040d04d50110038103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 500439712 1250 500438462 500438479
    0x15011b0602090103110406170a060504020408030705070f030503030106111218030c12100b03010905070b0d1103070801030f052a010215060f060a090503150a0e0a0816030c02 76
    0xe0910a000354440c2d04200d00083c103180f59036059005410880d01100c0341039071800810603603081601c6801c48080c041090003601c40400195598990018101401c0e502c0041d554030700903450120300d4680568070482c0040c50010040000c95000f00640741141c0003818082c15015445514034140b02c62420103c103030007400300e0506070542d00403d4111080c0000d400720303402c080b512002c202c0e07845c0e092003062603130307921a103c0c2181e030405075040744200d008040c0002c01d404101c1d984160903ca80c030b80100824540c04100d56035170103014010224815441c9501503e942003c220042102005000181c00031480900600800c402040b501d520400780c40d18140c6580442440745140500b403c2200d4014416400000540d42e46160703001d008070402440f110b441c054a0007402003541040482005205070340b00700141685050003001c481801c0ba0740c6001940c68200c288804035000201e882c03c49510100800001800d1b2200b03c481c84bc1480903a284400c41c00d19044907034010901000390480700300c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 500440962 1250 500439712 500439767
    0x2040f0503010509011e0903020f06040308090d0c0f080a171008011a030a11130e07051806090708060f0a090c03050f100302010302310509010803121501 67
    0x151186842036890450003031146843c0c181500742a0740301d000c0083d10108034500c240b18403240795400424198421300541c0c0001c0d203c10159401c00708200c8040d03000c0384500c5c0400040386000c2c400c41c040b601c000c1c101041c04800c113454403074080303020350b4004081c890300207400c281c030341c2c05a0300c0d0a182204440c000310f0030740b43c084401e0312400b034944180c0b00d040d030924040c6600c5141184142080c3c400c0039000b0311140c002901d504403040d0303030441d003541c01a82c0d20b174440c90302c0d0040d4081c240c058951000104400da2406051041204079899107c42c200103800c00d00c1007a80d05c010116170010854682680c0c60f0301c90900007a8091829003c4030f502c102408400203038152030350090f101c0240680c804008541d61310103420340b04c5070308130742e2528054081c120074401503000e50b003d460909810421103809103801d1611203021070821452940103079440c0d03010021340c500083d85074090807180c0c1c003450a2180b00c0d40c804400e41e0000c1c1c10014050115034805c0c0f4541d12880303000c0000d0404079040c4207607604 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 500442212 1250 500440962 500440979
    0x60906450a0606060c050a080306010e0901060e1c0b060d051006030302071e0803030c0a020304051810080705060403080c1c09090b01080103030507060c0215070f02010515061213060204 81
    0x1140c401c1100d0080c10000e0024809024000084034503070803401528004039503981d500e000341c3c00204124144101000d01c040c260b00d409035103034064400c54481c8032120004004120034502042402c0c41015400702007080081c2d001c04525401c644203840000500400d0318140742041d0500020004031803a12000101f403503030018070301c0101c900e0340544007000c2d00142c4007820b11120034040c1d981c0c81c1e0b00820206000390204c400a00380e481d05881501d0a20380c80e0350025005010480081c04408401418411011801c000d250000d20341c040042010514000c0403034000d00980c4000341c605d04003c41d900b5020b88062080f032590784450b40e034040d101034000102400318401405030383c111078689070b501c04040d40101c1d43d460603240c042d10313400c1c1400490703590b21025040c00c1c101c01c0e0450041d1103080042c0503240070032030f01414460301c07481c0b9500e10810b0000c0c2103071070040c20b001003040859a400303a1912400c044039100b0b42049004080740e039a810701e52a1071158241e004011510000d0000340a51 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 500443462 1250 500442212 500442223
    0xd2301020a080942150108070c120e0d060c0302040612060303020604060e01090c0308090321030103060c180f05090106030515120111030a0605010206090645 69
    0x1207841c0c58601d03050f150410b0321a95540c2c070013010010b401c88020214603c00107654183c45401c444c48403420700040110081d90b03821001d40d807108601210300c4040e0880d44c0c0047c0419840703895450300740e8442005480b4203400514000da0b190910402c2110005151502c205180b519034021030280800000c1c540020b0081d8010301c110703000103041040e140c51102d01401103000300d0b40c2603401000607844903110325000709002a4178007039940d031310080d100003c2d0140354000f0055002c5c405481c2c840c0e862078180750402c00882c5902d99001c0c91380c0c000f0844199040103413410749400c03041c0020702a60b41e1400795154540c04446030b00415800d0400a24040c2c1034000006482e0305941254050342d860074180c0640b03000f511410a014034855a031001c2d8207000680821540b0400c001150103403900c1c2c055401d41d070080da00707841481d454010a0166580411540390042c18400080c0700d5490200511a40c240d20b10840d4071280c0b901040c0d41d031244d91503041541e0f4542d4840c0b100c0908406640f41c2a9560 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 500444712 1250 500443462 500443477
    0x90c0d0b04050f210f1207020c0a05040606090b13050a0e06040f111e0409090615080a05030f090a1a0714070810020d15080d23090d230102 61
    0x42c811070b50302c4459441c010400340d0100340c94042d460b103008450f00c0c12851981281004e1301c0c20100503c51209004c0c0d41b9090107025280c40c3d00a04104005007051150340945034002601840c105501046200e5210110f0411109080078040d01ca071410202851514580e9000c241e000c41100408a0715100d4007a615020303900c00c480822501386200c1c00c2d002601c5900200c4410349000340501a01040341c811101c15419031310400a01c7d140e100c030750210450303051040686840384e969802903081150142c3c1c55000c0c100ca880104400070455817013075944d20682c0c40030043c1d14004140b0380002c1e100c000c1d400004e040541e0000000c4031100140072060380102070203032058804409902c003030840c0400c00c1c5090307034284409059855001314178038020b54060b540c0228070554446548901710b00303505006c00503000b0a00904104030400e000100685801011074440c031001e04100c56521107040201e5070071000603225143e80c4a41410403041c502588411a00c1400c01252400c1c100c080c190f0080228 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 500445962 1250 500444712 500444723
    0x506120702240609100803031303021b03122203060509010b0901050109170709021303020315060112090206310602150a1e02040905010e06120a020108090c0d0b04 71
    0x40e405540c50032001c0603075209a9551209800101d030450400d078581c140d00c24105d100301d802299503400454139640c8211095a00c1150702d50301d210406a06001100118501c44507800144010700c00007a11014484410782c202100000c15000c402e24041890501541128099044070382e01e051890182400f2114241c040d4600110309240d403506d40000d5041c0c48041c0d40f031029290038500c18494125aa0400034800c0c0704d0701200145440180c0000c080910b08a8001d449003860362051618248441400071099a5200104109a6400091150b182c8203540010507800c0080c00480c501d1720403101074107401c0300c8044074050001c019421558000010b803100c201d0407079666800700c1c0c6405482185503819500d078408139000c2e1800e5000382c0741c8000450003a071401925207007034408a81c0540e22400c00c5584840041000f18030880c1403c0e0b00401c06d4801005581103440c0041e164001c0c1d41009040c45440d030042110b280c400c00640c2e454990190030300307401400d50300b8104041c0e00c0446d401c440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 500447212 1250 500445962 500445973
    0x9021201050612010e2e0314030c0303071407020d0b090c0402041802030402031e010507201e120711030d0c050303040b0613060306020904270303150506120702 70
    0x4541c1064030403200442c540f031925210a07401c240391000102c902508400958076030320207a640d6010b0389460049a689100116030034146149000782c0120048964442107400c24026602c5620020080300da0007034203032400145804a804519606014051010b500100ca992005041010342a103081c0a01403070130458007403034031180400c0264811405026041010764500028055941c2c000c1c580281c4003d017550461012502c80140c0700c000d41e942c0e501a03a458405101c4066000140348641042c0e1400450041c41c1c0140425601c00d4190505c800201c04030305a1030700a1014016001107502d0001c185685906a0803d1500d00c0125000a1b01ca4010041101401c0e8007810b061084c440d840b4000e0750840c0d545403200d4020940080116410000180301411400034903c200c02c0034603c03a100c0180c94144020a01080320320001c4902d0032038030455641d5039191841e8400580700c03070307042c17038041003c41c3d240303c8111381281c86030b00060304000702288205000c0786100c1c40303c1c0f2511403a401c841 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 500448462 1250 500447212 500447219
    0x309090203130212030c01110307080f0609040b25110f2d011e062d090b0307360501030c0303030c171f06020a0c060e031609021201 58
    0x804a12040d1030810b016410001a030300141080710071640b1142e803c3c0d0589003418007100350740d42516101403d201b0300030030004c100a0400d07080741c172050308840001c0151b8400e190060109803e406c01810107080d10403240009000202e004951840c1c90025070a50b000d00c41005002801d440381c0d00c103034205a406650100b901c440e0700001d4115507142503141c0624480c242d41400380001604081c902d100c2d5407200402d490050001022445240d40180c001904600d0700c0d10003180c0000c5030150494241040000003840300c0030b940d4100c19500801c1001411043c2080000c0c50310010743d2101d5000c100301c5880c6603903001e48580000d900c0b003440e0f8003d019002078001c0e0a04079042400000c102401000c0b061020134403d80c000b401800305030800000082c90190f011140340000c54001440306065920350b180c144141c0b8150004000314001040c0c00c009035030b6000505066400707440c2c00c1040003015051b05540c1081380c00742c482800c40c0340703614080d00d40740b465010b9404510307a01841d082510000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 500449712 1250 500448462 500448479
    0x9050a150807092306040207050304030f21030b0904120917030705070f2403060e1003381510020303061005190815150304060e1c210f090309 62
    0x10304c803004045404e48007a0b40c40400b044000e401c5610184c03134610081c00b010000400d031180f0341103500e001d00700300f01071840201c0b44400811200e00b81c4400f0903050a4403959207454100155810540c404440381886904a0040303c000c1e1f13555120f10342c00e4000004024100307e01000801880d4024400d444001d038940041d1945800301c0e1140894803103882c01d6008558080c610007a40d1103016140110f01c1b1695a075031800c421800752541d20520300341e803074204100310303148120060b02409006190020082144940c40204201c41d0204c5e2b0044500300092800c00308001458217040c00622103114100710324130081d604e03002280d1480c01403058030074a01d0701c2400740d42683e1545c4080f41026a408411620032203d4920161401c2e0b0a10030040c4407e44c41c3e507640080901c0b61410b80300881d140d140505003101918004c10003500150000408541d20880ca08022106000c140c281074020703d0f005602d40c50a803444055034140c03036140408a01d01d1582c00e030400301c070007402566060581510303078095 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 500450962 1250 500449712 500449751
    0x602030f1812030a0b0a06120b03060105150c030405060c0d030509070e04080903100e0a020f06030f0105060304050c10030e0d140a0f1103070c03020909070f09050a15080709 76
    0x1041a07500468070302d4110954600256480010b54030042403070405000410080c4816030008004100d4980c0d64050341846442603080070304080340244000e5142501090081442401601c244480003801c110b10b80030801c02c0724001c180281241e503861003541121034641070a0480040003070b003483c011030702086000503920103455102080300030302e469a40c0e40c0722866000303520498243c09407032601068070700e2900c143c00034900c4140c0038004260140c41008001800081000d120f01820300901c000c0e61030340c010550541304242c503041e50360f407900c3c1002841c0c404442107981c1d108440d00130164409602d508424074580684080300d10603c1110380c25034003602501c000d074224490501050001901c0780c02c01e24240c4019080c0750900c480740441c000d0441d442a00191450b0340211002c2046040107050554030000780000b0f05020390070419070740e09124081c403840707081d181c41d003022406145550f40f01d940d4025404c040001034030703074990102c7d0b1a185188035003152280b8000030100015a0202c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 500452212 1250 500450962 500451001
    0x106020303040b070c230607020106080715080408070f05010b0406051e04180203011b0e1c2907030606020c06250f0b0114040b060a0c0204050a11070602030f 69
    0x3d050455a541083c01c40305c00e0500202030351b0026140a81480440d0031465101c045600782c00500f803145410b10000c3c4c02d69542e41d00c064240e500c909000c00130920380c0c400803941da003114580101c4c03d03200d90070841e0150161900c05003200e004a90740d50708214056015040100d020745d8280102c554507030070071050f03040d00680d540003031103401224401340c5400d80c001807540d03032500d1280a001c00380350042400c6a0000540e491888084865801029040002210024022500400c902509540c2085140121000213246c4030000f440c2480d14109990308d0b0400e007090300070b001d20340c0ca010040140500003030310504c1c0140c02a6050141c2c1814144100c950b8407221141201d4900503c42821007610003e81040e9039810341a8a5a000a140000c90038000c0c2100d071002082d04c0c40c41c004000840c1d980d0500d01d40300345000c0080c07150150700040702c50f02c040c0c0c04560003d01e0b40d0b503000001010303200300c04d1820340140c000600c6e80d0400015901460040031440c40d0b00440790f0700c25204400c10f40b1340702e6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 500453462 1250 500452212 500452223
    0x12060b0d05220503090a05100228060c05030a050c091e031c1106010b040e01050409060e0d0302070c0b030c16110904150e010c0e0105130e010b12010602030304 70
    0x200444203602904069085801031110810542d103103a158612689820000c85854100203991215850144101000b500b004c80e501840742590300e00280d40c070b00b4070304520fa404248140c650010700c3d00010f201178400d600014140504034086900804650085640c0d0038120f20308000f0404d8020780d07409442219401030f00013007c41c1c40300c000c0840240006000c01c2d91512a508a620103145101c07040b0006116079101c00c1105451208c2c410300700481600104843d1400748420400341805019582c1100da007030310000f94400d80c500f8540302a10001034031662905c51805480320460b4035900400090307000c0d100c50906103131583d01491907444261440b40e448070081c403491036001500d008138640244101030100c9007a01200201760343d0003044405680c4000c0c08a110b16500c08180102e10301d00407040f00801c48050072600c05000010100c98050411101042c014101c18000d034a00010f01100440c8115a6070b41c1e074030000b1560300601200380030004901c00060041d0000007501d002c0c07640726 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 500454712 1250 500453462 500453467
    0xb09040b06210603150601020d030b030c0a0602032d250f0b06040506030303270703061503060c0c0507050105070206041d0a180512030a0e070609030312060b 69
    0x100100000380440e148601c0d030001d8200600a210808480c0000700100d901800a40610b8504100350030929103c0b81c0b090200410781c02c100c00baaa02180c9401401c0d01d905000034162200c0307001c01d24000c81c2244050300516051008500f1f2138000019000307020710b40c004d60307840241501102d070000c8500b540c0c001440d84103000440040802c0c18501070034540f01501c5246425036034807a4a6805580882590040d9031803051040ba42054000d4646c0010709a00551640c1400d650128080f61040d00d503485450388090200320f80e110030f000041c011500001c0610140000050000705518240310840e5001d10b0015104202409140c140640035004009801228501360041d105a40850002ca0b800042084040740a8280e6103003804c800c2c1d24a0303d54402803800441800c111482c04241074031541a1000c4000000c50004000c0a113151828120307450303466035000400904030084440a19024100300402c420781d00040c07203821070340a50f1f164410310900c40320307000c100c40e4a13010b005100d2104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 500455962 1250 500454712 500454727
    0x1060903021f180b03040b0112021f3b030601150305060609040e0a1103010501080a0f110409050f0111090904032007260606010c0b09120d14100b 64
    0x722007408a088602e828044244000101c94180100c0d180d0400c090589001c014402404820b60f5440e01400300c40d45950748003a000d400040100c1c02002c01c015051005224000c02e040c45030100000303141c072201342291b000c80d5101040c041c01000d4030512810701ca0a400011485c80c0001c0c1d040d0480e403814032084500b49103000100d003c0d0400a02e0715070032810412401090b03844910a0b12035020254001d40320842e002c2c54802800b1580c1c0d12001c0c8280c0c1420018401080e0100707038020995408552104c8451107440c3c0743c4003441d081e00032030b0f07801450155103606010011803220112107822008020b52409054406030900541c1006a0047d19400001c1c00080c05417020141102c0d01c4500c00100381d4650b0030851030034001d9000b5042c0d13400204c01d0080c0c0c252044041c4402c010b0001c02800542c500000003e041d0544918058003200300b0502040c54030f030f01845403041c8006e12140c210758400705050003802404e02e07580f8088117a25a0701c0080c0094014550400544038120240c0345803019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 500457212 1250 500455962 500455999
    0x1020c061305101b031e030603080d02090f03161e060903020105030a020c070b0405150309030703210501062c0a260601150908060c0904090305071407030b0106090302 73
    0x200310500c03040903402c403840c4c0c440d130451500300d5100390740300100c894148810b203440c0070b18144420141401d0107028400a21001c00b5900310000741500180c40d13a4866001551010101c04a20340502036070495144c40c1566800d02c2c0d05a406145507441d801040102411108000c4e03c1010001800320030180010b6210b0070043d900310501302030250030b00f00e580e03c0c2941000d10580c40003142e200c00040800c9141030509150b58111202201c003400c6180040e43c1903100c0c0700e0258014100003c030703001c2e480134550342070024600d02d003d9032007027000390303103824001d01010108034100c110105416000c0c0d40b0b9500315a50f001140e0f8010b090108410320f8040d11b440708013154540c150810f04180d0700404245010000c030f90003441c620308a40108840250060300d00c6005804c01203c0f50450340810148160580845504407403d031000101c443c0d85007003c407440d00a1090041248000015201d84494009402d40c00e40e4041d100b020116603803004140c2e4801100e210003900841c403038102080d80d09 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 500458462 1250 500457212 500457229
    0x50f040f080715022b0603080f031e04030207051c050a02092508240108011404020405060d09050601050604080c0d0507050904120f09120602090d0b1501020c061305 72
    0x18400c0fa400b00003081c603c890340040e6008a030001610410ba481ca1641410400c41c0171042c0c16007014042000d1402c644648615108284161f100c8043c000049403988404160603243e42c41c1038403040440d070800340b400075190b841c60b03c28a807050011030040700c2070805071201e1044542d8400010602d00031507900b40100e2060052043d06802c0896010030740000d1030301000d0b0910000d03565962703560300c2e200803080f0034403921740c0c8100a503040801d41003003640d8020740700c0e074152421410090000e451010001c0c01a2080c0d420841d0000804103001902c4510f03500041d00c41c500c01d9040c1e81443c0c0c1c91307205018003800f4030b00c1a060700e984000c030080080d0402507142d1100d103001c2c000769031090380c482c0700ac64003040065500302d5000021003424003032194880c2c9010f0b0301c20360602e88180c03c50324100c945101c4095500014040c0c07680000e419940c0c0c3d45148c441e82c03010380d202240294500d0007030104014412030000b1580540aa10300520342490424200c802244061902e81c0303080782070505100d07100c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 500459712 1250 500458462 500458477
    0x3010605011b1401180302010f0513080c0a05070f05121501090906060302040c0c05100603030503010e15040f0f0c02160e040309031b05010f050c0a03050c03040308160501050f040f08 80
    0x40740140c0c2103d00444080c0a03070642c400c416644e01101125a00e030003400c40d02140c00f0740b6001c602d042c00344881800d00007075011606800c01e4bc425207074100500300608040200030018841d02c10840005028910034441204403031049408000401440c054a0b840f0401e501c01001164900b20050203110759540c0304924107405031000080c02c0e503c9900ac2012594480c102002059000d00005c041250400540c800031015480610050f841e680c0e002e00540010b000d421b1464200c034000800e4000e281c2203444400f00010000e102c41410b0030182001001024500a50282850340040401e4000130b085603001060789005149107207407440c1e00584110140003201080034103c000030201d000310b518104c0c0d501d0603c2494441034680000034010040c03464941c000c1c01818045082642c60100d0a41041c54243c204181d40e181074403c0681944145d070401040c114010504c0d800342c00c05a6001c84490344284001c000c5901d030080e5061a652080340c00418401c80440c2800c0000e60450262184 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 500460962 1250 500459712 500459723
    0x21010e131a1306020706140c0a02061603180b06100207050a03061107080d02030a14041211011508100501080c0d033005040c06030c020304031e050303010e0109060503010605011b 78
    0x1460700b1580d038030007664031100c4180ca4403a200c4003245ca051050002150700b20414072801031404031520406500c560000303110940c1c40d008014044041e40c065000041c020f138010f04503610421403440d140d000c00d1800d6955600034401c042c0009140d600009140054a40060200c0142d501c1e664601e00941240c9200f10103665060201c50002002a0042c05401c0380020340940c89143c101d02c161704442e08000c0702c8508003081014040480c03a40172000d150707001e40c1d1400e40968800200c0c298050303c510100070180b4100301e0300020b65120085902c02c84d1001740c41d01842185d90310f40d40c013565466440302e080e500038010300c81500064041c0900c0d01103590f82049031610200903da071408060801103801c1d149940719000c110030000980c4611000c1c01107401c0c100041002054020360f24000c03400010f0081101401103041d1041c01020002007541c4182100e0782c035a111043c00192800038480d500d00c140c10688041502c1c5410b00171078069410694501c0b0340b8403000a0108240c1c0300d40d0905884 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 500462212 1250 500460962 500460991
    0x807140f07050d09031a060f120106150c1a070f0804050f071502010b0306040b0604020901050705030a0203041706011802160213020a09090608070e040821010e131a 72
    0xb61040c414003582054075100c0300140c0345141405006503d1114001c200f40b50764600f0080241d8a00840c600307007090907641c0f220381000541e401401402560060741d0740d0707900002c14000711540660071042c8207110340480c1050750154400b604c0e0380c400980c0d407100402c0c014800c9c1400c1504c02c1c10101d41c05400352045030040a440e0045501b020034035000f42048180840c0824506502409248150001074004003814a40341d10750341504000501120302c51500000d6440580c1e1041098541050700300c010b4a81d1400c071420040d503680c0c00341c429100c810301e8a00890b03494020100b8524100d510b681041b04034003a90f2141100254003d081c2d500f4000300d004400000343c0c036000101024826001c20050340c400006001070a00740b82070f84580c2c01282402004d0200c1c3c400400c1100840d015840c80d41000e84a40c540b144141c09200c2503c1001403807a801401da447c03840c02d0301d5048035070200c08000b40e52525221804070461182d00640084600158046000e108040c00c903440001d402c0850f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 500463462 1250 500462212 500462227
    0x6080a0c092a050304170a0e01050d110f0403020f060421030309080706050403030e0f0a1415100f05010c050316020a1d09011d12030402011e020a060c0807140f 70
    0x10881000e0740b100e0b50000c0c00c040200401c0080c2011b42503441815404210705180800000034500c8140d100c0b040e040040c040b503141c00c452101d400c901280c0c000740d0b10003038449480d0700101d00346030001d200a030702c02c00c0c0746076612941e400d01404450a0360b003644200042000544660021344003107072000c50402d603031181841c0204040b80060030a143c070030310010415043ca800c0040664a029886200750f4101500005040341c0c00200d65220f9a40a0450302651800c100c0031814003001d040c04076840d44981c4100000c9000d0520004151a40100ba84003000d40303d10046907000c0c19980000c08a42c802c12481210807188ca105442180c401440b81d00c00075143c5a500b198240202d42c50008142c540040c010400020702071008142c0903070b40c0518010003c80021507480c460707540f400014501c0003001c6800d41e441901c11101140054507500320800b0b00c580300139610450710303006039945d0786058590a0007620420721140603515603543da104120303002810404c41d5022482d8060250760421004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 500464712 1250 500463462 500463521
    0x31c0903112b02030c120d0810090501120c1e0512120a0306140f180c090d0f0210210e010b03060405010509060901110301260a060209010306080a0c09 66
    0x1400314054200720030941c2d850307031051603c4c0004101840d4070079060342c4482d1801305000a07282c2213010070340c5442c240a0700c5500700206044001c3d00010351301c42c10f00c40046072030302061504811142c410b402d8200000d585104041c400b41e160a074201c00603411400070801844c0c510140300c8031f1101c00083e60b080042c0d0280c07083c00c0c0e078410044003007c00e07120601040b4490030300d01d0b0704201c580e0680d20340120105440008520310b09542d038a080702d202d01008980c40065034025580a811701070240502200c3e80e080c000ca01e00e540c030b40c00702c0c442d94902c1903492105204501103002c6092800440000701c1000b205030010306030640900c2507541d80c44401d000141e030100305460090307004000001d400d0906103101d90400000500040c40340e03061010201c4403c4406040303904407140c00031030300040b031440340e403401300f50342a00108200c510560740c0d42414045c03658001e040d00242600c0412081396101c0c03100d902c4656884001e0300e03c0610311030412445603550040005030415407100703e070070079030b14040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 500465962 1250 500464712 500464759
    0x30c07062d0b030f0304120303180c03061505030c030a030305060d0b1504060506030c09010810090c0909150e0415090b010305061504060e1b1b030306031c090311 71
    0x80c200c10744414100c04141418044c010006003524051031501e0708015905007031608403c0300804050b070703641400d080f29004048a002c02039100d00f140e180c4580c4e07810b01c000540304d940100fa5018000d0100040c031880c0000e102800c0f00c1003d000ba0000c0d49064409400400000703101c5034101c3c02401c00764000911401c492480391445901010000841405100464680740c02c07490060700104103000c10380e01d5070b10503124052800d2820410607540d05404081d1241c1503402022210305000c941c00304e05401030030030b01c02c0e0307030b0b01d00c004124030381c031f409d04000082d0f55034414402c0b8801020041008590112a04410700a05035804500a400703999980795104090340241d0b80f540000c1c040c0f02c10500030380c0c0d60024808046900707210b0700341080303141d100481020300035503184d06101000d40d030382c056100c099807240080d0b848003411500c0b00720b800a03100d81c0111005031107401161441c80b5119400080000d1011039580e56508003811581c84002e40030240138000c0e4400304403000036520300e240c0071a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 500467212 1250 500465962 500466041
    0x50d121707081f080a082706340f02010f080105011205090705100801090b0103050615030403020c03070807061209120507060618090605160203090114040306140912030c0706 76
    0x113030342e4594512144101c04a403003100d03c8040c0b02090f000800780d550301403e841c1004220301d0303c1b00321030403014109c2000c0d5054030881c0090b441c81401a10a0102089034054040c3c001e807940694070171808000c0390511030900070540403c1852803001003142d0b039030740461380c0200a14103c420440e00c5000084000840e60300800016141c20010301c00d641c43d9001745041d1142c21b00f0305000d1820300c030300003445e415151020b03541004d401000140506108204942000002038141ca0300a80c5848449460385240e001c0e1001140c94901c0c02d861480c468866000519000354142129002c412344c01c1b1030310b90103204c1c02e80300c031a101e00c004a03000ba00c90302c4485038059020300c0040c4103070b0607281010a03224014210151840240b00d80b640841e00031080b511260340c2480c01084015004000c0d120394000d41d040548843d14280d4184240c0da2069449070107074000d0800caa80c1140e0220540c070041c4401c07100d00003168814004a030004005402c014004005420344003a000183e80424045084000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 500468462 1250 500467212 500467223
    0xb07021e100309020d211b050714060d09080316210527030324090604110408030c0303150d050d0e04060806070309061a010503060904020604050d121707081f080a 71
    0x480c070303e400c6c0e50400104601d00b00c0b0440060708405160301e030300744c89044d14030484807066452100d041e4a0354640c41192207004621008011246441c00c1c2aa4283c1044404400385e00b105c4000da2019400381c10490301230450a4201503540d50100c4616000c1c20b4058070f030303c1c801120b400b9001e00b01c800d400b466130320b03044003030009607124680042081e802c3c58803e03800c004800a0b5038202e1195888510449512250648020462180110705181d082c4516440345109000216a0f0304289202000442c05010508041d20b003445c40c81c03040040220400c00c0040036070740014640081c0e17a01546100380e202c0001480081c00302d6503200340d1403c0000480e10580040c1d9203030700302d0003000158880e0800061402c42c16442c2060038000103020b41c40040c0010b8802e0344500d0002e0111354401c01260081c003005440c00072203030710514015441008000007800400e091107030741d800480e03840040c03038070507402595601200e40740c03181c08041c01c00954403400184680c200d00441d48002c10452a900c1300d1180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 500469712 1250 500468462 500468513
    0x1003020c0105010b0c03071101110708160f0503030304060b010c080c0d0206072a17040e070905040c090e0403030e0d020c120d0e01050d0906060b07021e100309020d 72
    0xd511500b100c0050f00f003030380905000e1140d10703190b101c00010740c0d0104d684840012140000000169903a0010342d408030103904c15100041034881d00480c42d80b1a40b445100c1c1d003e4101d07100d0a05030160000c41c0210740d003551052002401051107038101c01d02160060402d918000e14070703221013001c0d5000781d100d040c181e80030184200d0881d42c10001a644001c0501c1e002a6070035403c46201c5070007002103017200c22513000c1244002031069105000d6000009020306a5a403642c443d80d0001d04c0d5811600000030803d81500010306007001e0060000d521500e95030036440f1400d00d041da0a03d90009401034040564803240d04080400030000c0f050031051580040540c44440800c000506002094181454220700080c00ca12600070040c1002003a0074284151519a5216404e005000160000c0d03c0c00b41803a20005801c9078800c01414010b000391841c40f400b0b94608400480075040e200c107a50010800900795003080e00c65881040201d10050a26a02807003589954016a00000c5040030300d810702d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 500470962 1250 500469712 500469727
    0x6020f041d06030309011805060c01140109092d1227080606060a140a0c06060501020a12050c01020c0105091e0703150f0b030609070806060627030705100302 69
    0x2444403a0008014a40501c1c1103840d01102181d140d00503c881981484641960154040c4210100401410001e00000d1720340030513041d860302030264070920b007000034000400820788407268003d01d003455400039503d0324520701205084407c0009211115610324400244400203558481181c0e1481243c0d918110325074013403070031202804004c0c816610070316010a020441e00d440420541e41c001390032101765444200b00b442c1a5524032011000040e48603000603050b01d1150408545600715004107002c014482c0c03680b00690780c416500300043c250940a40c3c03480301d003920810041c00c4201c1c10100250502e100b00c0070715420f490042d141e00701389800a54842c0c580d01d0911844030380410740240107104a618540f0340e085840790041c640f9140540702c400c00440d0340c006030001c0d0340714000039040f24018503024056039141c000c64021410036010300408a0854548181500c0c0c4442100402c100703a0030314224000c0c0800545d40800d9098002c0080000300e40c0d035016548801246143c5025980b04407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 500472212 1250 500470962 500470979
    0x10603050105011e05042a030c121116080d1503060f0204031a0a0212130203010608011e0b12030304030507050f0105010b03041e0510020d0b040c052506020f04 70
    0xc16080b4090030b01c01d80b0b1a400b0544c0c41960305000f2118103071000075029034003038922400d241c11100c65889610b00c200d56041d4556040c0d00c02401c0501c20359800d0006030070304001d0000d0715904100d81d9500c0c282400000c0d616540700c03006020070747c03045000d2487d01c03011113940019144008400306920b0341260b003c1061102c03e000786190800c403040214505421940d800100d1240b8103a8031107106244000200030140030b504a403400b00260492a43c03500e89401200144490514120700070b500300407000800180501952403403c180c44503201d0411100400d1138001c0004219965000340c8240c18214814400c0c40214011402680c0c0d5580c0c0e001035090092515071032405622103030307141c10010020050f0a0085d84e4000e98001818201d40211241c03520480c1000e503c0a0050b00a00d11058010841a40245041c000d542c106211003100042000201c0d50501d0003000410790411a1905135000b213105c01c10b030101140050166810a81c49071000c98100c070111103000000003805004008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 500473462 1250 500472212 500472221
    0xf070603060b0a02030304030807030608100203090d03050f01062615150f12061f0f03061211120f070308041d061305090c191e030b0115050c0f0106030501 68
    0x80c82c055180c010036040c020360382c1c800240040c04114441c0b0200e074a0f14401d80115006212440071100c1318070030b000c8984003d6005591804061145480441c0968024001c580c415513040380030b0040341c1c2c81d0010a544503820340c812001066010000e0081c022061005103021703810f4100304038a013145078000c0c8074503240300c2d18212513000340600c41105170000703d404441d400040582c0c4401d1980718100801c0d00105074045002c0d001c1c0000341e00381c2d4295400891810800001d80d07040c000d80342e4400d41000340740340010000e1304420804a1034000d81c1440c0080b244400b060302d0848400201c00d50101341006501c2e0000c458144000a080101c41104590288094201c8100c084103041c10300c0092003660070301c108031642c9512540000c1e081c1c0d07401e200c031075900003010300403518030f498004002010005d107008070b0f1954010b07154644840c20620740e098041e664402100c211a90819031034507401d80d004800c03402001020002c610308080d0a0001100d0100d0042c00400c0c2141549001400e58 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 500474712 1250 500473462 500473469
    0x5010e071a0d02090d02060316031808090d0f0b070206040308010f0e060d02190314012d05090a0f0f0605060f0d060f150e0703050f06010f1803050f07060306 69
    0x1450041114203941c5031004070350081c03820b500016075812907940400c1d0810800c06011394402804030800000e00c01060303d814010b00d090b42d041041c0d140c3d4000d0307040c840c1200440508121024404403000f820082d010300c0c05980500c2c1d811140442503a00da0707201c04811603d840050f08260306000070150081c0115014285281d005135100b420448019411880100b40c1413107004820158801d640300e0186485000f01e1440d1100b010725220305080c40c0581d4081c80807403480d881c1500345510000140141116020320196509c01070040003c080044c01c0090540c04040c01a03a603a64001041d640c103000501c0d221b22a0302c42510442d08101049600007019940600d088500806c02507442c10000303c1016030000000a82000790142c5c1c0008141c140c5000c1e070f90400842000c01c165219402e414421615a94180001c0d070741c10540041412003034a040740401c200e09035601c103050080f21440305103001204010141903503034903028507248078849030b150103030400c80042c1b005135414028003015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 500475962 1250 500474712 500474729
    0x3050408060c1602091b030a09110d02090606030916030320010c090501030914060901380f042406020c010c080a0f20011a09040c03140c0a0305010e07 66
    0x8040c8074000c0f8080c42565079400a204107136650000341244580d11110101ea440700300381c281c8920301400b48a004000c4220150764025003100c0c0300445282c6004180b00302a03010b404062561030300d2080c0030301d540024101a03200d00445c1050000d1001124509000394000d40d946140c0303e10710380d80c0c01c5600050852070030721a41440340d12034060340c0000c241d01c112a420318001a0028036810b043e03403500c40039000142540103c00511006140540024900c2003003031880390440a41e6030307451250b441d1032803004400e00807060b102100701c1c0340ca00c22001c400710020308040707009459005c6805481014002406291424140a020300c503810000703000148401e00740708460070115102d50100e4001d00c3d4680302004054a0364540d081e10548000010350211804e41841080842411303020f440302c01c1d815044481c603019a0906843c083d01918010342d0130000e40e4590750308584502815420790b0f80029224423640000b034146440301a080d40085000e2400000d6214110b00454244001039008269 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 500477212 1250 500475962 500475967
    0x16022e030f02120601050d0f050f07020d08130609020409050d18060507050c0d020d0f1a07030b1f05040b04120203060c190309020a0b030c0d050610020a08030a02040e0403050408060c 80
    0x101d034030f081c0c960420800d00303140b174456452000c003e003d0818001c00300b8009040a0600541040c982036090240910b5000e44404500ea600300310b030300c0081258401c44003002c7c070740d40384081001c640c00102414000780010a91001c10b403a142e140c01c000a1469000982103585a88800300340d007503250213080185440340c80d0464503151240d907030880c0003020b4032489a0701c0c0c1c41c40071035681c200f42c0300070b503940b2129490607840c1c0360404400041e42c14100008103160f00d0b0006503030380d1181c0700b8803201200050421020702201310301c41c0b0070380d00e4034486401800020803000c01c015803004084d20040405500c1a10000420700c103050130105c003d000e5600364102408001048c240c0e450803030031070b49198540003550302803070300005e00501c1c9180c0c440c0d441c02900205012004443d0f000510804071210400d0120b500c0c0c0c1c605011003240c525050350016080b0078000d600103030b030001c010f58000b80c0710940541040c4d1210158003114000352400c4000c44c0380054104182c400600440b58400d0303802a603c0d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 500478462 1250 500477212 500477227
    0x604060f08031908010b0f03090703021c05060f040b0f040611040b040515090a0e07020a02091503010b010e01050d0b06040503010c020d0f05030105031507050d050123031216022e030f02 81
    0x6d13218040c2442c4828801404000540f0000d8100954401940c004004585025580c05071318900b0f141003200351128060500010b0007800d112400c1390150740e121070f914036a50f0710100c11112509003d481200c00d25180d541203035210302d21a000d0400f07444c1c11001e483c0c1d213603c0e103410040d000f017000101d14105082408406265aa000c050600300c0e4500c400075046962103000880c280000740c20025403104041042c030502c0825580b1030b040b08030007540200038900c281c100544942e0301403d6014001142000301400b21611500000d09980010304114140b645640c0040e09668440003901d0044e0f01103c81c00035850340c0300c607c4148401c800d041840c9554101400309448091030058101e4201d00c06000c65031b80c911400031182d1145100e001008070b561609a003603400c4000c545100c00140c9007105001c0203140c00704000d280300c44d580c500e062816260812444250390180d4051341c0c4400030074050782020209190f240e496100702d22a005c80410303040e001904403104c20141040c854410321020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 500479712 1250 500478462 500478479
    0x190c0510020714040c050c0d05030a05130f021c080c0607270e0402060702060d2c0c0904051c050415090305060402010309060b10050408240403080604060f0803190801 73
    0x280040015200441c84610075042510644200780c2c7e50101c900c00d5000548000d90b10001031400b444061380f0500241e00c82d81007039404110212405489521110703202d60051501d0512450224481001804200615110200b41c0c0d00100920252030300103004114280b50700c42880a00c442031502c44172400e580b4040c5213180c83c06140100d00c61012030b80040340c1035507581800d0740c0070154002d06055441c4c82c615040800780140d2039000d4086802c0301e0708a500c000710818031522a82010000f031003d01c080e030040058420015205403400d0090140c0d515590b0200e9030405010f82e00307a114070b69a10700d00b0701070001501403200c1903020080780700400e200049000c101030307800030f809203400b14480c802c6040100040c01e0106403d980105080e240c82c450390b8000001c0c10031585684140e945010600724504411440c1340380c3c404070415074500050009028071001c503003201015200081250b2a40e400d4448000b0b42d8001c1e403086d44c40492440036803021500d28075010456031610501c2e5514003440d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 500480962 1250 500479712 500479739
    0x1104050f130f060b06070602130608011a0f04030602122a04140f04020c010609050a0204030b042003060103030e0f180c0a05090d0b040c080a030207030b09190c05100207 74
    0xb403403050380400c488103200080c0c2000200640080981e6915441c40c0741540080d400204c510700844000307000019001e01600c040c9048440c84144861080c1c40380410554507031190124840c050030501c0040046640d0344040c0c11000102d80c42184d1034209001512450700d05164401c0001d0903403505090802d003801c056404407644100404010122500040d03d1950b2102200f030300244081a000c04030700f415005a0202c40603640104610348400000c0010f0744150300002e40741081450110340062a1121508400344282d07040f03640503600d00f4000b03404d200081e48107800040001d07010581610b08142060003c200496060b00f260040c03d030001d00d03904d4020003001c0114070100d40304522078064012682034020082100c1000c00c1c00349404000090161015a442c0b68007003408a8401c10000d07082c03a4694145d0010300143e0320399991403143c1c00740140461803601a0802c4200300c002d0040c0a0300449105222018034603040c0000d020b42400290103090866000340360812101c01e03049039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 500482212 1250 500480962 500481001
    0x93f0409140a1109010509041d1605030109051222031110030209031510091b112e06050612060103240b0a0c0503160203010b04060602030a080912071104050f 69
    0x1b0107684845204000500800c071000701101c4006002500841e498004106010080509600e0401c1c0680750028503089612069000302a948810404230715003061201901d0a00c02c8009078035000d00b24031035841c4c0044100d600850310a500d9800601462410842070301454141c1d03d811402c02c2d000d8000603640708141c81444215081080104c4c0301e008503640b4220140ad4140d400b8085480512560112055420103001c0042ca145400e008001c40105a07480c1c00418441e140440c02040c542c180c008030201d01a007a03095a0303e00c00003680380c076004007a0440440d42c0e06a0317060362400718009803c2d02c3e046c1a202e1415008164802411060030490a0560344034100490300e03181d4586c03040d07074400c9101c5006441d03480045100d0b5103030302020001e682d12a1090317001340010b0340d4440900c03042d0360080c0210809a002800000b4400340b185021030380c0013240c0d40c100ca080c0f0485202c00c1d41c007a8001c0c030007034441659103d81030600742031038017506802c2a02c4003500c000520f8220301d41030354100840d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 500483462 1250 500482212 500482217
    0x130c17010e073c080d0905031203070504141f020f01060b2106041410060e040923071707030b0606070b0402060f040509130209093f0409140a110901 65
    0x10050124000741000714020304013000480703602e62800080600380b0713200d41c032440e4403d01c0740c2d80c1d01d00d000160442c140c0c1e025090580304d060806040030b40c1148140347c2d0b04469900542400154441e60b0122103081412508640280c510590ba044e40700e801c0d80c0d2a600540c1d6043c10403c0010141480c0501201c075149030a80c1c2d00c02d66403511000140a131000c00c083c18442c5210350107001800d01c1000c0c0640440303181d919080100509030050100b90b4421803c00707010581c0948104065000b140161142d1110003001d40d040d1541f1580e4215102c0b060480e6404907501800c0280204166980d80980141c4220f0764203091800c0c90b030718120f1000d03000300000d008410105100202c0e114a02c1641e003c0d11300180340303181c945004984020041305110007644283e0406010030300e003100100d003080f04030820b400e01400301001d002006a64006031082c0c0810744c940d4002904502d1906009080500a0000e0201e0381208000d0141c2050201401c040c0d0380318034040c003c40c14110382c1003c543d03581500b030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 500484712 1250 500483462 500483549
    0x1c050115110a0209010b0405010915080f0408070b0f061306080d0509130509011e0207050606091305060a1b0203040e0a0f06120f02031e0303130c17010e07 68
    0x641c80c55007010200e08000350001c1d00c000010842031422806002034500aa030b0b030041141e80c0b0004c88140d140101000c1e400301e50b0241c0454a00186d0b0403605600c20f014868131482d1036074995642c11629001c0b42d18420040641c0300388006444d02650310030448054001c01d2011605216496442c2c04007504240e040c000006000081a11000300407082112b96540c1048039103084038141c1e000e04540404061880420030b42c0180c0460280b00f91004160080001c1c14280d940e9000d01c10359040c0076011f4034201001202050010360104116032040c13100754408100000e40e00c1d100804604c100c12804255042440203112a00300010040d41c001028980805e085010341402001000960014000c0e45118401c400c18481c020145000b0b00340700354111003031001c1c14007004001c88061503400d6160f8004102140318550f44c0a003506041d40103801e1018515515112003103100000c6d13180d200142d440315a00d0ba290007040c803034240200b0600804504603e0f03200c01e5281d01c02d0852200c1c02c3e0340b031400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 500485962 1250 500484712 500484737
    0x12408030d051f0807050306070c120807020f07030606031a1e1b03013201090e1509190f15120512040b0c071a0306240d021c050115 58
    0xc0c0015a03503803040c5a03041c019444c1c540511580b1036134240200f0703009105178400314080758494946040d8042d040400151803103036040040b034880d04080e040c441148035041650101420070302080d070046100d0741c000260146907240410300c21f98403800100c4568031890030400c004203008242210903d40c040854019614010038400c1b0356040406100002c8011001003400c0054800d001100031396071417074450042c0c050040400103a0000c0402c0e0000d18084010444415542d110540003650000803408100d12840415140c60045410600340303540304602c3c0001d580c03948a403040400f00300401f03010446607401701c1c0441c0c01c814442d0003420851034121030103001081c4115004500920001e503500c581e40d00040c826908402c461080c41e0040000016545d40e40d40402c030144e4803a1607ca50440d66104100480316002c00049031458128240c01c800c001e40c03000007003d82548081e40140c652082154170890701c61602c5081078035a207800014444d003444609020006e0b04107180c0114003011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 500487212 1250 500485962 500485981
    0xf1e0408040807030c0612090c06140702030a0c061e090501080c1903050a2a050c03071707061404170f13031401180f080327012408030d05 61
    0xc940c0540080d0045620104c00c0100d50035120341150f07420380c1c1d6080442e050245280407039000034802060316520340e0040100900410100c40740424801c8002d0500c425038010a007054204441220417003060301c0140300c3d035a0030030030443d030f51180001c0b0b80e00d44010291014002c20094092141881100b100090090020600303c441c0e9505003846003250812410018000c1c100603507170203059a040c62900c5160f00c100100501e10708002d6054681a104581026507159000310030900351400100a01000b0030701c4d8841840c1110581c1500d0380c0c0c0c40042d814200b04403203040c0c9c0f441d011028103505100100c1c452100c24101e0419a00c0d0040d03540f020b1003412162842901600c0c0f220008590002042c080c40004022907184641c000307002c540603c881e00c800d100e45044008090305681500710010032000710207190301c072703410710400d00c0240110444a54880b069050303994a036034440518861b994007580d03100504000041e020049107060800b0203440e4000c0c0c0505541155552001960021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 500488462 1250 500487212 500487217
    0xa02010c142b1514041512081b0318030c03012703050906030f04060f09020306060108070908070315060906050120032505010b040614010809072106050702030304080f0a1403010b040e0f1e0408 84
    0x4040ac80c0c0d030b116410b003a01d009444a002d031641c0711f030180c3d211490507424113014020705030302c0d44011483e04032014442103031813141c0780c8400c4d0208801802074070007a44a0100560013055100350401070342c50f140c90b12900f910f440011010441c0d0828000c8001a10001000ea40051003428481c0d00d580e94082d08440a41241c1e02c40116441103080000612441403001c03000d0321014003040c40025207031221801625898070400e400079024840700741181d21000240051101450280c900c0c241081c42d0241c1500341c004034204c003040e001300c0010200042480340c1c8961070300a42e8180f00427890031629500c10b003030040b10181070100800014881d54401e000030005005413580304000c49101a0b0080006a2018011241c1e01d00d00000700702c86600000a40f40b00c1c96001c4034a0f0b103003100040c102101a0002e125490910140a5101c80100144000785000c0e00d0310800c0300351281e00c1c0180e60340c646c5101030180ea5542c0c400100b840703540040e085420845034000074002c04070f170300c50b40b03030243c0b4a2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 500489712 1250 500488462 500488507
    0xb061e040c0c0308060303040e2e060305060102160e01090b13020703030e160b03011503020d050118110301121e06020a02010c142b151404151208 64
    0xe4075081800c1070494000da01e51108501075940c003403090752100140b550301d110f035002e9001d00c07284100008030408070184001d0b0480c0008078103121b00700e95214850507280d44907088100800e071242d04100755942e04100022501070341420784c9000a16101e04917000980600407181190340f03482541382c05849030074104100d80592042150303907007020300f4000c004141396921201c0318040c0c1c83d40303062006e40c0340b4421815103070001c0070249580d00e824200140344005d0400c000500d40c0034440109140c0d61071003070031b008003c2d4600c41d91040040348212001c40e01c4e04803480c540080c8c01c0c40144048a24020309018a80e4010360f41034400000e8540d0300d0001402400003010703030380001000400c8075419009142d00c0303802500c03216103540000310810100d000d64000c1038024585c01c0e03c0d00c0a10600c0c01d100d8600c4082200000450000e0407050311404440d070b40041e080090015a48405418241302c0d090040c10440d403081c00841c2423000c0002094240740d00500441000f080e8070002c1c800b1100c001081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 500490962 1250 500489712 500489719
    0x10020105040b06210a0501020405014821020706052715160615081005042303070b0105060703020a030507060f0501031b050609010522090c02060f0703090b061e 70
    0x145c81e01071030f00740e010b1340c00703405514002204c1107800c81d030108098003000c0c206090550070124500c00c003083c4503900c1d00051940030030b0a480107840e0010540c1c4c21030402c181045e04942da40c0c82c502090f80640707858203d9221004000003000344d2032102d05000c3c10840e07800701e85100e00c406403071010f0024030111811b42018a8040000a40f40701002502800e45006841220b090100c03520780180064804200d00c180c040ca50404c00510042d00360326440349500610802c03d42c0395820741600080c400100300c1c0c242c2d0140d5031000031030310107005a102c4c1050044c08121441450031407180d60003500e409441c400101804004030b498410043c00e41c11401110b01390810130002c03580d50303090202c2503c0038034400d52241400520082401d040c4441290509035043e11001d16043c40202c642c0c484070140c031103c4070b000d0514000407400d0103460045829160099008014a0500c03524901c905007014002d03100b817610f80040000002c1615450070341c000c03000c071860004d00ca00b00b0800320000742d80c0c51542c2c1c2d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 500492212 1250 500490962 500490973
    0x9061203020d05030c032802030c13151b06140c19031109150c0a0f1205040e15060723150105130b031002071110020105040b0621 57
    0x4640100208680150340298212000801e0740c140507a00743c48190364140c011603003040050a407002c1080e0791641c00c01c0c241000040202207625401c00c80c0c2050f50300701c1c125040040c0300300460314444e4041c4068089d02d07040c207101c540ca010001e80321000c038405446460460b514284188040d07035006010b001d80145d180380302450240d015030002e90183e0f402242441107038408104030752007480381420505c0c0c0502400d140202140410070070192904107002c0f10742c030030040c141e40c0000c1800103c2a440c42120b201d40c08d50540e1070030081c5040e400005104000e4188010882c0411850140f03070064140d0300d1640300f011090001c03400e68403540320007400c000741c91185480308044198405851000c43c0c802c1d60220002c1d02c0e44450160004c0c0318803580840c10340308510940d00aa4443c000322500103085a004400141e104000d980220100355200c8000b0342041d103560404c2c01d80500f00e65150710003000316140c00d50300c114040380040d00290146030f680da130800c401c56000b010f110a011007001103a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 500493462 1250 500492212 500492219
    0x907030c030b040210081006030b0a050d06061406030403020c0d0c0b1603080a0b150306031f14070e0907030b0102030405220b06070302060406050403090905040b07031d1e01060906 79
    0x1010b410b0540f4100d00901e039901040341403e10990103c0c3c02006074031031400341149400c2c0110b0151a48209055000f034241100182c256211a124840d1601c01c0784041900f62501e0303034031080031540c00032003401017404204000c002039001c00c80410b024400c54030800070340c1960911144d402001c1d045110380c8500000d001103050724141d8661807aa1080c2d03544001c40d0341d40c540f04829600c0515440e034200c6851044ca654040c2d4034009907038803240181c203c8828100c010b0040f10b100b000044100001c81e911000e0410008502d10001da00614504101c002034040c3c50200d00f100100078282800c040d40c4080f106a940e200348122030050030020564000b8005500c51020a040b40504031028a40f070300b801039080b41045400e8508068054025106655540d2100c00151800410440402c04514008a4a10712a20070180240c0c0640c01024080c5032000000c0c044a0f4201056421100c1002c262424481c001810307110004540c0c40c41d04804207204442c60151201c1e40101e103c40f4144000070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 500494712 1250 500493462 500493473
    0x607061503121808010614040905030d0507051201141509041d0c0f100203070b0c040315090210030e0c0f0102031903051b0a02060604020c0f010501080717031602090907030c03 77
    0xc483c0c8850032441c043c070555201145804c0710f82c42e22444105188a035582e1b0f001345440c0d4000d00030140603809480c6481c003071070040c000b00c03031741241c2800c04620080340c1840c81400702c3e007120307015003e918241845580d40c4c10010b5800c07600001c40c14440540010030740314070307100c68201000008070246001600a20051802d0325050a4200c1d076020b1070504911443d03515000f06900d615903444c1d0059803034603490392240c12070100020140719200c001000000300082600c1e010b400381d40000c48000078010b06501c1044040e00c0d00004000c1018100b0688400c00075012850032170045080b1040400e280c0ca610040c1d096024410050980e000e001d0708038442d250709074003e68400c40e04418868907074280450703141e03031500580003103d0050340180e000500d1824998000c00760810054110307094881607540071401d40300700740c0090740207030403011041000c05803090000a04000d080081d42c2800c00c2000c1d1101071815510020740300300041c001252010209104403c0616000a00344400540700d0604 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 500495962 1250 500494712 500494727
    0x1512080904060b0c0d020114070804020a03050a0f3509190e0a0b100503270a05161202012312090a0b1012150213081608060105060706150312 62
    0x42000c45d0160940c40001584107100e801c02400c00807000e04810b407584030341198509001401207802c1682d546021001c90010840b1941181c4103090340b000c001018981085e6203000c2d4640c61f02111201c1401d10310101104041e05101007038440d01540310b084144c0084c502c51203480c00b070741c500442880f022400424001c1494070481240205012801c03445041c0400c040642000038001401400407402441d03103009012440301c01111000c001c0240c60a0b000d040505544007107441d6441520004100507001070700b040141014050940c2850182d00041c000915040c480070300c4024000480408082c0740c3c003078600340400c1c049100314502e01559400d50382d4400160586640d02c031f20000403520a0b081501d9000d0324101c002c51981517695645e00d02030550420410503c642d0203111000713051200e800b00e00000c1040100600300441c0d1080b1501c003001e0550030941690700494014000b40c0c44500489094542c403110024812045201c0001c800050750002002c6520215901e004254011074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 500497212 1250 500495962 500495977
    0x15060d0603050c180f2a0304120807020a06151e06020105060f0a0902210a06051309050d08090a170919050108190b0306040318091512080904060b 64
    0x450300b203d81d120f01008407030076124954850201c04800007403658081620070136042407881d1518854400340700d60442c0946005104142c1052001c01000b0502c4070301c0c0e82c500d071111000d06001610341009070b002516160f00d607030302800c65616000100311b6030042c86114402405554292180c81603a900812509409071050740010760a18011400a00e88142d550b82580301c000c2442107501e1820ba01d00380030b50006610072010a46108182807810300c00d004451003204041800039201e400d003800c00184200011b90002c40a107010007980004100080b28540c0b1200c5040c10b00082d6030740506589015121080282580344403d40302103204c204030003602e41c0450480e00d40042400351510343d8107214a82c07040c117001400d40000b154440100310a0168626018200400d082e4150000f00f441d064040c1c601720000303205400803503803260480702418060b1040320000d10039126400c07441c1804401d28041e500300300792000071030420402a0000c40b01e48010190090000665500008225820400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 500498462 1250 500497212 500497223
    0x50a11190c06080105060901030902181018020f0301061416030201021201170d08070c08120106030c0c0b07120e01140702190816050309090c07050d0e1815060d0603 72
    0x2040442c01d607014211880c1641c0020300000e05050340b1000440190491a001381d800156000807002c07601400c18174036200d20424102100268070708011645800c11181030a40000c0c4140845c511003048501100d0445020b440c140d2107454412101229070700c207109055003100969004041015019000740150603050001705005a0740e030032650a882c12700c0b0441403443d401c840c0224588a004810b00c580107084c03868018955034442c0d648080c942c0c411154500e841c1a00c00040000a81c18016070750302a02c00c3c81c0c00c81614400f0758076002c41c80b00280a010034403c0c5200381a0070484a50700000704c0e000c05038020701c0b00304000d02c800500c032a0141d402c000180160300c1c0050302d00d1030300c280d80105664420707045440c02504100c0400301c0103450310101c1e0540010400a4440d03540c4c0d0303003047c3c080c00303140d01034507528285464128504104a81c03110300740002c0401c04591603585006603100c6921000404505a650b0120240720001e24515a54465804580001580900d5112405591155 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 500499712 1250 500498462 500498483
    0x603100510050703051b0c0d11190b0304030c1b12020f04021e030414030301081605030a0b0106031a120a020a1a0307050706060f0e190615050a1119 65
    0x4400311614031071104084c000c00c80402001241c00e114007480c0c106086608280c981d102003910004405020070002a00c14110403194100289002d540811613080780b031404107207080c43d00c0c0040030b0318000104082c0501c064103007040c1c140003412003c1c01c00451030305842205280c4500c101100102204c0c402da00070300c0750182500b25420584212403017a0300d007107440c80d05511400310071140c0764002041142c0703c0204a200400d00f060400180d80680150b00107408034281034000c19807450215400644650311000c801d0000c281ca00398464107544032407402140c1e0307003515a658005901c0c2e24082d0780d0000f20420029010400100d010b1410743e10843d00511056620501a00c101c0d1b506031100504400400101da600c43c0030740700808031b0901c80c0b0300210350b0f1aa111032031a5a05200e03417100e80010303110004c00008048006458160b05040442081a40d081c00030b1112502c0840c0070781c0c0180100010304bc4059801044001d980710002c030220783c50240060a841440000b08808440c81d00c2c19 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 500500962 1250 500499712 500499739
    0xf09010c021b0418020a090501051507030801051309050a06020903300c0a0606080703060e01021801030b130203040f020102010e150606030a0204080d090303110c090105060a03060506031005 83
    0x110340181c030040c4803000d142140400100f0000108454031210921440d640c155400603101c0303400d00001041004000640b0358902400d00604800c000544101050100002030000e9000107044d4103454081d640a114084642d1808000b17020498001d0024441d140b84441003204070340040c01c0c1c03448140c0c1a41c0d0080c2e031500c2021280751036407080883c1740b88000341c209003982802020701160401c1504968032034036180c5840080312006d420203180341e0442d0a0a20a2090303174042c1c0701d06140160002c51500e0003084542d43c68108800c856030406072030319031490484c0e85e001d5001c0c0d04030301075401c1103580341000d1505c060440300b003180c01ca01550900a070040c00460200303000d0329012803c4003106481c0d90304010001382d64001412000555800e0002242c240c02c01c00114005100e181c482d11138690441c28040e01000d481c80f000707022031703021251210140e110802ea40d8115407040e19901d44400051320154064800d40c0c00281d0030003c040200001000c810114000f00c60301074800c038484251 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 500502212 1250 500500962 500500967
    0x28090c05040e0303010b070624030b070503011401030c030605040e1e1f091a04052109011d0402070f21050a1706120d170f010609120302150f09010c 65
    0x104400651503940044c801080800355a070028018544900030001d17030711130316440320500b1943c260a010000c40c0110828402c000700a54800d1700941c01c1d0902508561605140c00041c0306c581c80d221b810151604480d10601c0e00030380210b4040d100040c03052005000c06500307250780c0c0c11580360030040501d040c440e6511401021030f05000c20341e5566220500c1a440829600c00380034000d4003119284c003e403042d20010b170032120b54907024910440142481c0c5640d00205075080115400c59402d003441009140d81680c3c110001d40011501415002c0604a030680007070001d0107410350242401261032041c904006034100c2c2007150403a0211101d10124402034100c0d030b14010544581d0219103001c07111206d4202c0248010b40c041c400810b40016409920b543c103081000010031000803a0000c1a00303910b008a58444036485900340007150340d1507140003c018961035182c840c407000c1d106110190002d040c8203221880520b4250340d00351020781400410f01303041c1c0304102c41c01c01c0f65510309030f10b2858162 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 500503462 1250 500502212 500502221
    0xf220213090c0905060f0904021206190807060c020a09020406030b10050a0f080402041d010506011b080904020a091e050a0504051017030c15090c03070e0f28090c0504 73
    0xc00b0b681c41d2640c2505103014400e007584007203503981d4050030038003041801d42d80d5400103080080c544207681700a820503106024840c1214082030950214826041c041000c1c0010500c00b103c0031481e0000002c6100e0010510396101600100703c264000100812099096041045090b40030f44540d1081c22040751308a030705005070701718500000c0a81140744542d038801c54405401900007800000d06c0180348030300d243e114170f440300f084081d41d4490040054a40c0c0051980310000c0301b42c401500c09038000d594003880d83c89140400c501c25a8046400311103d032040b00c0c41c0c3c0141c07a0b8400400e904e1019805201e05000e29031003228450b8600803808160340c2000d0141d2401042c1404444c1a01404e04000a41e07210303240400c82ca547c0f0040c041d04030050300401000d62803014020b503090380c50405080b0300381000d5040144601035800540c0400400c00b5500219600007541c00500040391148544050000c0d0300602040c1a8a4980d820180031130959005010b09482803d408404503078034018407040c1c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 500504712 1250 500503462 500503481
    0x40c2115120c0b090112090b0a060f050904060c0507051501090f0204060c121110020304020405090a030f0c110a03030f0f09050d0b04050a0803040506071d09060f22021309 75
    0x1c0c2c680510401c258407492000d044c43d0101414444c100d0040544604100c0d45600340507a1240c040d0300500004007010b10480002d8400380c1040541c0a040c84040703010440054030080a1641d00d0719a8040240f00300300760344007039030701000741c4000c41c00c160501c03c0c1d104003c0c043c865660f46842c100d03132034820781b510843e4125055a02c0750f0544002c0746e224a006a40e10a0341d08082c0059240301004404083c010740b5110800032100503201e042a00500045480041c0b40c0780050788240302400119401031840107040f099440c150107481c80ca072400c50000300f020741045411805460001c410590049034000c45610700d55100400e031590f20108503201c00031031182a802810901002000c9140c052402d5441806a0105c40c0e00710041c1c0c2d65507031145d01c00c4134103a031690401380510800ca98072000c6a84082c01c000c0d148080c4000c0c400004007000005042e0740d1041c1110b0402c54541d44540301281807000d2240c5070424982078400c8010003a40c001e00181c0e4068900c400045a001250300c5000c105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 500505962 1250 500504712 500504723
    0x6030615060310030804090c140c070308070c150f0f0e0a050d05070503030c07180203010f14031507031a061207080702070b0a0e0a05060c0c040c211512 67
    0x2880840000c0c03240d036a101501043c004040e09a020004c100b120b40200024017010200081142c0d80e0600189000400d001303018111070200722402071500002000e105803030b0841c495036941c0b5094a809100180c05500040d103002c29185507212054100c1d000f01c00c61002c0380c03181400c450803030004898442e82c480c0c1d0346a000d01c10031424402410404405a4064854001c582415031210000307459a00030b4400c0c0c413001d0340809024408101d0810000c1d690301840032080d41554102181c244502501d8020324680d60152018400c090781c0c2044800390304420524074100d07604013544020050055003207082d054002200480c1283c1c10007004a844828040e9100d61180d1141803040302d40c00c4010b441e41d021480b68001c0400d181c01084014500203002c0d80b142101c1e00400d05c2840345c400280e40c8002d11412007402062071242c1d02080f0201c040e1303002c07034000805410025013035a00100729020100340c40b0700d101e12a400019103521040c0c00509100403505455550410101da1689400d0010324 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 500507212 1250 500505962 500505991
    0x908010c1403130606031202070f0e0103020420031003060510030f0609030216060f0305011a07020d030224040501050f070c060b0a090203270d023c0a0506060306 71
    0x324820907405140c002d0b42211112080091a0311502c054450541003034407203080c410791922040c1e07010017501f0014100700c1711100e481403401e20010024401444040d001d651540403c02103008078030b0304c440050b640c0c5000a516818010180d84d180c215600044420f14508008182551080002c1100702d031360042030b9107003400065071444054807403c0412400e521030040e5240c00c04605551200c040d000359910413503040c0e0280e1004080d00e03010307408011601000c200d49040c1202d07400c12105d0464068403101000f00341460120302e03045080001e50444910481d480100d18940f2400901803030040d4001c1c4502d4492000c10862691f0564905001c41e50100008001031220307001901c4c0264000c040042c195a5a854581070b41d0044501d401c280780c182e41c01c0c02c020340743c0d10013942d0700ca50764400500c0021850000650347e011124001003507981414401001c0500000c171614031070000319040100f070f41410035001c2d914800b245080302c65000d09400203034181000034910348200d640c000c0c2c815 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 500508462 1250 500507212 500507237
    0xc040303030b0607050106031505060d23160f0602150f2701020a080108061003170915040305151b192c030d0c080d180b07030605010908010c 62
    0x400501c100d1100783e41080041c004031010840038810130008501440140e0181b0082c0e801d0201103d200415043c814440e03441c0810100c3c0f160008010382c008010707002500006140c2440e0b10f4405020140c82814070f030faa60201b482c21f2011748000458007143c080b100081900d5801441d00c0a0441d001c0610002c0d0100080c404180cbc50030301401c1c099050990b0451094200001d801da030300564003c0e012440d010010003000504000036a40801c400103010500390a55591002e05e0030511030160728144042100c000d256510740c41c80260461001c4a6aa40e03607680c0b0307040352504070108802a21907103c20004240319040c1c10500200515481c9003442d08a01035240d9041c034a420322568104040700048503c1d0b004115140e005c40c410030204000b4104140042514164516412100f04104030192000054100050b640c1d0744094280105a00300f42c0700c680b48406d0880300004d81400003140030b01040d19003581c004016034000783ea17000e508540303a40a141c00c0e03507418480d08001840200060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 500509712 1250 500508462 500508467
    0x6032f060f130f031b060c0201080601050307091206051b0a14070327030510020a0203070f2909010606050c210d020705010204080d111905070e0a0c14030c040303 71
    0x2c15260041c1124500d82980300e11009a480d400c42e0012245840c00a4908401803800c440c490018100c40c030f041000306c006a400204280400351449040c0040400814006030084007124040d0209203201c445503002030a060300a0202070350196003102c00d02a007110440081c0341120110800ca86600c45200240e44400d40968040c60301942008140003d20700c44001b4141a0b4500500426511880f281035081003410680c108030b00c507a44620401c020101c042e0044203070341c581500311040d0f15041455060100300b5203100040d0340e9100042810030b490740f84c400c4842c1070043c801039000300b24403900c170301e0151f503544034582500d502540301507028203d40740d500c0c001d4009000e010201905148500316007006036082244111901c0c2d401290a10000108101858200c8800c0c0303400d51100344500d90643d240c21130b89004c5440000814142c50500c007041010800902d081d054800780c510b000300401e0010403030f00c0050400211100342109010700d11505580c0940030b406c03042854585565001d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 500510962 1250 500509712 500509717
    0x50c160809040608010c03050a0b01120203091203130c0f030206040311030f10020d151a0f090612190e06070c0302070509070509120304061e030b030106032f060f 71
    0x200c031018010046000c031500c55008a20040415500100d2152440d51020341a40e20040c2050040f40c9861440d410b00da80c04030022030030100c0305500503034a03280d0074150341c200310140c0e1036000d18003000828028000d000803003c0d000d0f98010408034400303903203514001c0580103207480081c0d8070400900040c40030416000b1a645941002001c44601000e40c584060401c008a00003140440d4049846059038042e402519880114481981075139414483d0b0724403140100800d0410703107070300400c10581c000005000c44818076401450740c0d881c0c1c0b8041c0e400388010030049885450b0700780c158007115403103001406038840561824003d82075903a9115401c64a910380c07190154110f00c54882d00180507200c041d4400e014031050741d01d6582e5010079400344010140041c0205406034000c00040164540c40348443c0c0910711009091480003c0365001200078004d500e03109945546001000001c1180003500040301e20400c2d441c400c00b511400208081c0a806e800d5460341001c01080a481c510261400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 500512212 1250 500510962 500511007
    0xc0f05011d120f01050a0b0103150b0319050c0405150a17060f0d050d0e180109092f150a08010b090a32090403050a0833040b010201050c 60
    0x42d00d2800144510710526183c10903140303844995440d410300030507100a003c2c552845000b0308003030040e5201c103640e003544200300307218080002c040803010806040d00d19000e8105010010014002c40c18003407845411030b481445a144a1400c01800d20003104070a015a420080342d03840d00171310101d1280b00030990b01002098145d016084100c0c0801036511100c030000b402c0d001c0e400401d01c0c00501c0030082d12040e07107854400e110303015407c00041103800201525040d5100c0350702c00310b980d00b09841d1001d0f46000c1c01440281040e4110784801c0580440c41c0807030505003007201d200095140040d00c002480c86044081000aa6980018064031740c5401c01441d07000c5020382810f610542c2c90580c00313001c4e16000d800032815145200000c80205031515080200003040702ca0070418181660080c125114010041d000e10035680000744d1481065200c014007922020000907881c0f20f03011484114941c2c4030403945c0705924045401e000fa520511880d0701c25142d1050380c81c030b0f00c0d26940001c0f8080c400c2d1074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 500513462 1250 500512212 500512219
    0x80103033e0c041109060406050d091a090601050915010c053918190e010204060201150f060206040201180515040314010506030613030c050a030c0c0f05011d 69
    0x4003003152a200c00e80e81903500c4080c00203001c1c2000400c04020550304e081c40d140038903400a10031055960740b80000c43e0308440321414269520310704c060121015000d440700142c0340a803c00d11000101043d0b6403228820007040302903400a0781c880040004e001c0c415690301000c4021040c2d5030300d065000d01144a2842e004004a81a00d4000c100701d03044070358020b17812501c4652000c41c8141041008101c401001011960201c0c2619291842004050001c10b40c0600c10604c0b842500d804850354007501920041c1c1c0002e550f943d0b1241800ba010304032234000301d1360309001c0d0400010243d107402890002d8404946c00340025407920b8004443d540841c14080600e0760003e203000585a4600c0e05804080f00034142035600c1d60704e182082c409103100c003182c00c48a641010108802d641d404191a64403090102c06d43c050a45241412124207084010080c5540b05903100b00c0306258001001600c1584500c040140503070315601002041010781c401c2e64049201034004101c8a04505006660a04d014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 500514712 1250 500513462 500513537
    0x1e0103090813170607110c010e130c110c01030b090a022115010e03060709062114010f050d080d020d09021e0102011a0a0b03070215042108010303 64
    0x184800452001c0c1c1c0d400114a000404100000c0f11402d100c101c1e8068040e00703180c1c1790b401e074500031192601c440460850401c0321045a82c8501d07510030490340c1810904c2401080100b49928015240c9500405900312910580395010410340c420301482c0302d44000908105180e13203908401300c0107504007407101c181d08014a10002141e10315040d02511074240c003122401800300440024145080b0002c3c03281c004c0d0400001c00210980011f607a00c205c0e002482e201d40003540d0f41c11104076010014a1001010341009003810f4175141040ca02816140b103001240143d554074020005846007680b002052050144501c080c0700f88698003406183d0305100000c20a42c0c179680c00100d6a6140d494034681400a100160f80c0c65682441011400b203a05070040c2008c09403540000c2114000e44912402031710700000085003684280011450803840445c81c2c0c6d0a81050f2034582c0e501c640c84188504101c00c0c010381454201d101e40302c0c582c100c940545500401120411000c1598803142d0b1140c001c21699 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 500515962 1250 500514712 500514727
    0x270d050307060212101530060e18060703020705031c090b1006050403080c0f0f0d021c080c210109141302180a1b1d1e01030908 56
    0x910090440030b101d540c005a44602c00d41e01c02c4103411024000d580d118280d00c0041c041101101c480051403511400c107261008400c21841d842e9501c071803010181114801004080c08205400140588002d845140c449540320407c1044028010880c100340707038010b10200300070034065401440e00a002da400e0f01d180540c0038a400d00d8030011900c03803203040350f99482800207008a040206820040c0d020944100c0e41c80c12030010802d0040d80409800b50b01d001800f5240c0c80d500301311803108003052009449035045406400c503210001d0244010260243c2c1d0305c40d1203091500703101020508000d854141c415200d030215880c154010410f049600943d6101c40c0700c0d6101301521083c02480c0d0000046a00d10f5196403828103a400900758016102c4554907090040e964880c0302108540d6882020503035070741e0011260003030240e1400d501d07015401100380800032036115500781103811014160a1800a150090010f000d1500e10001d0b90240c42c20070f0750f202d640c801d4101c0c0d81c1050141080c1070400c0315 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 500517212 1250 500515962 500515973
    0x150d060e0906131118090105130c050f0d050106080304080f01060602070b031306110a0e0d110111150103120314090a140f030d0c0201060b0a050d090c0b0c160803270d 73
    0x12601a1701420520a040050103c801d00603558000e6003841d030441004010b684850821350140a9148900190417084000e41c59400004800e190044000e000507980c61a00a4136035016000310700240c003540c0c80f000724215050081c901111901e60003808050314011650800b44c101070001d16290b070041051001082c02e46c0500c1c10742e11044040180c0c1c3e81d40400000c1c00780a152100b4602603800d002188021900c4201ca8100c103001c28200302111034208520203081181100c0050005018800080140010102240f05c4e00c4101d403030402500712075404119a07080102d8a110b400c0e030050603510b0019160303110142d0340120f104c003180c160420050115066811500c2d447c1d070400e81d603105000307080341d090246c58011307c42024050f1402c51400c1004015209041d00243c444e03071940f4088080102c5407242400400c600d641d86d980707070040000b04584cd182071205c480a51007c1402c0442c1c00c044c0402205c9064030380280081c011094440c0b02c5d50f030341c40020011540400343ea0400000b142 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 500518462 1250 500517212 500517229
    0x60702060d06060e030d0203090411160302010501030615150c05012007120509030706030c35090c0d060b030c030601030503070c0b0702060a0e040902150d060e09061311 74
    0x52041d900890141e00300035004154240741e1040510a07880b000c018000e0ba0340210880f14004008e460101e40c0102454035120a07100b07039081640c1c001c44005445080c154190b124505a80c130803102072010007820710030100d25480300d0003944e05c0c00e041700f034030224094026801707181c0d12840343c0000314000c55a520841207041d0032028035244214002003000c00c00240d410769814456043c1080e0b4100001440801c0c1d80d00058001e0009040d0344a4408011f580100822095131407a01c01100f2a003800b00c100c1010754007003100c000d4122035200c1c0442c016031000314480c00200c5000d40041c0b80d0724419101d1801801c03058071000d030140103180401c5015102400388a020b10700800003565580070b6031078000e200b20720550011112000900107100160340d0300d8200d4440c002146090024550018002002020f6440c0000d500c2100300314800a220040009040d208280c50350400030315955001c41c01050710100c036100c400390000070005022980236501e00f180e15010381c14820010302c50f000400c1646 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 500519712 1250 500518462 500518477
    0x206032406040317030703020c010606030e010b030d050f180d05011401060305060303030118020d05100f080c061e0c030f0310080c0307030b070c1506050a1d0604090206070206 77
    0x11103152000c85002800d0202140c201481a240c0500c2e0902c3c640311881c490160750340d00d0b00c035004000049a0841c0c42a01a82c4013012840020400c02d59500d10180040900443c80c626550030719400c03048500d808926074041c0c807400d43340c50b46414450030501619500c450f004843c2c150102421600b113841303190b41e200c4800d10800001a01074804060200c81a8050340010200741c20031080001c1a10007206403411507801e90012200800c2c002c1e50300c0040d01440940354402e40c908801c0081141c2c0788008101112a1801c5814005454140d040d444500c0c07180e4454001c4010041d0b5101c201100c0040e601c0d100d110b6001034104030060125034115800018000c00301c400c08420310208881034900000240707d030f000100040d60380900466200c43c16848042c00310546040010400c50040c100822199440100c000c0501407021a4500034002c600170580100f04500c400300c3d981044041c0b10704c0e210b40b409502411940e0310030410001e013090341403c82c0c200f001401581d00685800000e000c80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 500520962 1250 500519712 500519731
    0x705031b060411131b021c09080a0f0303091203060306060e191d15040c0f05010c120306090608151b042c0f010f060e0108060d030c020603 61
    0x2100660315100603800400351680c08550001c805100005103160100031840c40d05a5002e1014800c400c6139100030000c4c00035040d11054400700801882d40c0c003007040034503d03103190703900786080040c83d408607078201d51400742c00d40e10b520000c1c88070040340320b8404400c0e4140c4a8070b8040f850040c180d0b65100400800780d04c0d080401d071520400d104008140c06040054078204500440f03070310344074070406480007403504003146481d035408918001c03240140c01848042e11714811141807880405c02402d07140780c00c54007507500d02410900420a22030302d82c5160100d440580d201c441c034140589405500d855043c000c0c0c1e040c541c0d5000c0015580700140100c00040c00030402424010340d034140b4880c91104020010254034412a013041c99081003c01a80e00392035003c00201480b9419058074103404904a40045402044504001001d9082c1d014241a1480814280c0c603d994a41d4169442406c548466001c245c4544c0024a1424540740300d41303500e40a0310305581c91210b1030b0040341c01c5510540b0400c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 500522212 1250 500520962 500520967
    0x13030e0310020c0f0c0d11130605060c0a11040c0504030212031c09050114010b0412060209090c04031e02010807142a0c091504091406150a050909060109050c0f070503 73
    0x71994080c0501502c079070b41595010b185010b0303595507e0300c0403a9503c0c3c4911480c181401d03c11419060303030082010700006802144e0380c520425070355a17202c40d502001c8660303201d5480010454207260280c00117040300c0342c9801e1300b001d00310750801c241e007100e00003420b51b40d00c81484a030580a11080168250010041c800108201070b4100b5509446050340d104076068041c100420440b5800d20403201111920704840c1985a010305d480710180c4140c0343d44a6100204005000f4000c1d03141e0300034004c8a1280100100780794181410799010540708401074042401e07000001c54a6001d280b40c04055114030600038a400c0070010200071032051141141160081d40f8520710743c1c14010401c1c204040001c403003d48491030b010003c04a654200ca0300c4038006c9844280a0003003180104010010022034402d8034001c0c9011440131f000d801d500c048041c4554100074000641e07080c40c440325401307020480080c081a80c01c00e5480303809000301038030340822040c0801c0524038550b5803a018000e1140315401455 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 500523462 1250 500522212 500522233
    0x1060507060c080f0114010302041d01151106060d060615030c1805030a0f020d0c140a05040e0307030804081e03011502070807030b06040f05070e100813030e0310020c 73
    0x704032208068501c1c14815100d0034041c0307668084c000117045501400c950300b204079141004134013034080e079403200d031031171134081c83c050448030726212868161144a0400c0c081c0004070841281c10500e00310100d44035800c00004a00d150506c04400340b0301e103010390b0021a920384d50700781c401c480454064040d40045da90b240800ca00e03981c04144c0400b601c10011a81044904250020361a2030b140000100442d01101c910011034403000c0304440f03100d404c04200e6519959401100d4900403035002903910076038000c8404500c1d03241512410210b81d100900071030400c0c1c907581e010b03558038001038429100c1000900050441203500700300f944510b10348454041d180d516200c10000c551190304103120540d001480c09221005001070680201c942000b03920314251070760700110340204090580da6088074182403c02001d1a0004500e2191b017105541840002c084d40b00112104030003a1400c0000494581080b800309201e004150603100b0020142c1e060881002010000c907402804009015080415600b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 500524712 1250 500523462 500523473
    0x30313030b090105010e090d050c0c04050c0a02150c030115020f01110d060b0408060c0d0f02040b03150f03030d1a1905100206010b030a020a0201090203070f14040b090703090503070b01060507 84
    0x44c0e0042c1b013024511002c0f402d00c0b2040985404614005004000d0040342d240d021070ba0400c003101880320013a1040040307092201540c607c981c080c81c140c0340544501192500407a4100340c1151140d42451585400e59003050710b400c4c50007900e10114000c42c42203800080001350f00380703d034183c514090204c040c0c0d2010000501011b68141e60301c0f0010322030b402d101c1042030440c08030b15580e000280c1040203a4030202422104001e11074441120030f290310100c0e0228400f0100170081d409404c4c2d080c03a8070414071080c030030400001e148105080c0c0541082c01804080b14940d04400c41c1542000ba6402444021a001c608e6401440c400114107a041c0d0108212504100380180e4903101c252014160b190704014011880788406464000300c00d600240d8514514400c0d03004600141c0c0c000c0030b540c15250b0707681706079a81103120300440c4590440b540c0a5515860b2620502c03a0088002d09007801940c1d555200307400800184000740c81c680010421280021640340e40039010300901c0c0c030b615403200305500f0300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 500525962 1250 500524712 500524721
    0x50d0b040c08221a07020f060702061506031e090c130f050603061003022e090602010f140133050a12020412110103020f0a0203220308030a0506030313030b0901 70
    0xe080c1544200790328501080300501004034124800140d8140d98407805001c80ca806102c0000008900236002400b51150340800c203d0300403140c006c1c1c0002c1d0548804104903981c03200359070802e2811080c58407550240b000d0310b081a444000d90003074541d610006404990f852042e50b00303110440d0b55403406000c1c820031511500e5088031068009006514011120144011041c00043e2007a610760300108014001c0d803074103408403400044a002c0758090000702610b01d48044c01404c0155080c146d590319038241d50b00c10620482e00028044481da440d180c012402032003640da40c0081040710703200c0071030f4103400050003400700c88480c1c1c1c0366640c2c1d0780c0c0998000c00200a400d05030000d140100300820018405091520340785410606001c0700d4070402d00142c0c000e101e00020f2000125010450080c0303140c02002512002141c0e40404040121703c07030b20340031100650300004010800034000b09003802c541e948403030f40c4000007a0407a441d115001520340020811580102d60031025038003040740c1504280034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 500527212 1250 500525962 500526001
    0x70824040e070f060921020409060e0f0f160303230c060709210602160c081f0608070e07050903070e04021f120207030302090406030c17030a02030406050d0b040c08 72
    0x200802e9041c104255011206c403080141c410382641c0c0d0707820001350750307a541c0109602a4000c078200090b0a4100c1c41684410710444800700078010b030024078440100114200d41c0010b000800001d059081d55800d070348038241081e000315030440300255114003407100c41c001c0103507681a84c01094135140c40030005046c01c401c0d4001c100c1a90802c0c031695118012140b01c0d1351040c1d4000f80158071080189201d29042001800190000400000000f98910041500f09107054050000d06014100340103240036241c1c0c078803e900455000d007004001c1602c1400c050740d00a5000c1c03504501d407c0e0a103000a10300200c903044a001c07880c501c0c0c148000c5103441264074404860040c444000c1081000c009440c1407400b0302d8821546400240c1107040511a0381280e0503620014002c200d0717035403641007001c8085818051840405007800001c1800c4c1800403d0f1042100309900861a140c2029421070340c1e41c100d5881c15103459242c05c01d04210350703110301070b806103180c0d26a48c40070035250031080e400441d1040384 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 500528462 1250 500527212 500527217
    0x60e040807120221030402060d14150d080a0f110102040602010204060801080a03080f0a090506040f0506090312040210050f1206100e01080117070815061305070824040e070f06 77
    0xc0c1914030b1350b14149280c001034803038144803612030362640041000c9200f1a8044809985052105501c18000e01100c90054101e9008502c243d00200306101c02c0400e100c8014002d0341e000d004854085200700c1c80080841c41c40c0c030f4541041084444120309a801c1038000c0da02503500801d06104455000c05260300410703240340200007107007a0b0345000c0c0ca90350f805422092020054000200c203000c0d40d80281748003a5020088644501c2c25080565802803e1102100d10740545401300d40801400010764600e030380481c2203501c90741c441d80d00704041022540941000d2103000d200004c0360104e0440600002820081860034500d482020016111038061145003446007541f03981c0c049907401500c0d1410b4510180e0f400c0811440004011700e803a0095010f04901e00c12044c44c4269000d850100d10701440d0706480c1000704030749100c000380540d80116000c400041d100030004481841440d001840f074590000c414814515082c081000c0c0e6079100703c000c0d25542b0818042055030343d100c030150b00900d03e52 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 500529712 1250 500528462 500528473
    0x6131106070206120a0b0d08030406060509090d051c020c06090f030f0d1503080a0207030b010b0304030e040b0a03170418020405030a300339030c03060e0408071202 72
    0x10342c000b405a0058012940c000d1010400062801400ea400544d0741c43d40103100c00041c000d20720b4081c405503c100c0c5e00701c0b0014100100028141030161030303203014011240203071100c205200021102500b000482d20b80725100764111440b1a42c04d0b200a0407000002e001070301e02c5141103a100e0b0318200c16000301100a0b4000c00c4000d41d0151110700781c1d11074071001d04010943c1c100c1180700d03245408080e0006003580c400000c01201d295000a5a00d086a2149100c02000d03a0380703040480c0203002c12103020300410260f80d400b010718541a800340e0014103000302002e007001d0f100c1c1c503486448181000c0340d4507080c800045c00d208400486402c2c0501c0882d4030002e40c82c0a082102003034840c641c0b00320091030801ba400d080b401c062861080000200404105035a0000ba0f1420040142c1248c480041020033780b1800c2000300030040203980c81303400041241c3c0703007122900c0204600600308509120105aa11038010844014542c03009005a01410784141c850b845410300000500e0302c100144c0655101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 500530962 1250 500529712 500529727
    0xb1c020102061e16020a05060a0203220b010b1615020a1d0307170715020705012a29240102060112030503040311060403091502012003070c0506131106 66
    0xe0f480182c1d20032100100d02010440b040800e074903140310440000c07c00d0080031708000c03600ea11036000e0761242e50f038541c03c0300c1c0d0081c0130f06c00c1100a01d070f07a8a02600082c03080c0c0052010164400040040e6843c03003e075400d46140c140c07105000322180c0380d02915503680008811303922513480313091404034129480c0800c0c07003088540000b036610030719440b50100003c9614a1120158024081c203001021171106ca07120107440301000a480741030b0350040502140704c1c0c2203031902450710507020403080700711a04141289980f584030040d44100c4aa620700c585003c100000c2610041c8030200703800742941d840703d485001d8010200140b82030300c00c40c84604542c810740c0108450141d00009144240c2c040c1800d583d03c1d121414201d4240c40c1080540e043c070b100d5a414001019070000300c0c801142d07036400d0441200440703a0b20490a9480707400710000c0c0d05410308002040d50303c24000075604002907090003400400c4590302e940c14a030044859011200070003030050240008078461181b800e50494a0628005e030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 500532212 1250 500530962 500531011
    0x8060a0b0301090f020f0304060b100f0518040605030a0b1905070f18030204051911090618030703020a0b07051209151b0319020f01020903030406120b1c02010206 71
    0x51040b0086903840e0000d0115140c07141c1c0c100d1b0314031050801111b03640d14090822300081c0a110003558051074299280440c0c46104401110301e8070f05503034a051400401012500440e6143c040a5510035a0781c0000070f2a550100501402c642c414410742949150044208001200100380060403504040400009540c45500c2d040c0304902e508040f0b5900b01c0d4a8804501041030740c000a400034509000e0001c0062100038806000203084400d000d108403440d8251002c4c015801c0c0346400201c01e00000c80c0301c5801e21040440c1e4203015046a101560307940002d03055803800e6020380c200b54030018112052020500c81d141c844415a00c219141101c00000304280426045c01011034000c080f9100001101180c404000603003042e00712525000245003820074106074082d03440140c442c6910140f20702a06000703541541300010082c40c01d0524101d401e0358100250381181004030341c4c0c1c42c1018155511400c200d9040014130039010910340702480013914104020341000280318400c02e01c4420b11741c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 500533462 1250 500532212 500532217
    0x70801150816121103060703050411030c010e01120f0c05090a06050a080f0406020d11131202151b0a06060e07020102031510210c03050f0702150c070f050d08060a0b 72
    0x2c41c4540c000500c4825410054084c10f084421550305008080074410f005a064005a005500800310315a400749843c04160395141400d916602085e80b804154541d58040d208001c1c2e81a4410408200c020302c130440c0c14102c030300380081c400100307001140c180751071700b0301c41d4840c009440c2d941841e91500104402c041e24940e0700410703480c4c100000c0d0b00040c0400095805807020702d1600c810074030840e5103a01e00c0c2c43e0580c201c0c103000780d01082580000682440103203801e200c040d401800c2d0590b009440780800d9801d50141e001d20205911380f940402d0b400c00100100b0540501503840000d2032810440801000800034045504580c014030a0000c0c3c030403080c900d00300b55403080700d14034010803500c070301607800d02c0440102c0319501116072605142414160040c00030000c840e0383c10030490390358805204160b102036800400580c004403245100765420f4202c0c64004030b04062003414a600c565800c3c000c18802c5100f01e0703842c1c00c50142e03120002d403c0303140796810040890305a89803504104c102c41c00ca0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 500534712 1250 500533462 500533469
    0x1506050325030209030a05100e0a02060306060a0221040302040c0f0503070f0915090f05030102040b07110d0b0c1b031905030604060e040c141005030403110708070801150816 76
    0x1c0c1c04a29403803621070b00036411510381c07880140940b07030741d0f08440c21300d2030701c030611005084901410b0045400620601081c00c917411a8000d20340c6080da1900e4090154070303000903004600b584601c0440020f030036203e00600c5000104079031041d580e1800c600c10310060350724050b002d00074000c603000004001e581010540740d105070545000c0b00d01c041d680c2d5040380e402e096588403850248545401005440c0d129240000350344405180c01545540e8005040c200d00c181e00c0b43e2aa4001c0900c41c803400035000716540071000300000c26554521650348c85902c404001070318014800840000e840f9581e10540c41c0c400794070380c1c0308405503003042810f600000290140b54120b004100b000000a8486c1d03035180c1c091400f42c0b1b400c184220491070145485424007985019115240c04e10400c1c4145e140307030580c0e084400040641d680c81c1152240d03030f400e45d500d81009800c034126001d10240411880410404100100b01c40f40003c10700ba0400d0203203038807504240c0c1061102d030f0003441c00702c110801c9142d00d0070106d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 500535962 1250 500534712 500534761
    0x302010e04061505091509030a0206030c04090501090e060a060503030427050108161a160f05010921050306030d08060a0f030f2d0b18010f15060503 65
    0x52144803000600103040c15080309004005207100c42c4200b03a400805000301170b000384c0d003d103034485a1101003001d0b80250000c00c0e6060303000403c0103006050034006182c2184100d003d8608064456030280165082601f101070025600c102c0b01034110020000f503900052100c004010345c070305110201c3d0b2207128a02a0002414101080340002c803144010120440c8500343d0412403540c54060030b545821088011089000310408013154011204a4640ac882c2400992600c0c00b6030000c0c000130560301100064039040300000703001010802c280034000c0c4c510f00c01c8286514950388001d40c20303c00241c002040c81040000c2c4204000368034000f440002c611242d0030400116519040019940c1030a6003280302d040740704c00070000401c000c56640140e010300c20070710811515000b414007003c0250303403101c003e0405800079224001c540c025081341e4018080c000d140b0107000a1180c40d50a5484a23440d800d0456030301c018100311600081c0c00e04026004516001e45142848007840000c440c0704140b2800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 500537212 1250 500535962 500535977
    0x30b090f01090b0a03051504030f050a090303120f0507090f06020304230a0506041508071b060b0102190b0105031c08040605060f0d0302060a110f0d15080111040320010801030201 78
    0x82c3ea41d0702c3c21100000c644c070801b111000281908078145821058804602003070301056008000b500a106982c4040d4082d0740700340105107140c40440d8084078200290000d25a2004602174110403030198612032140c0b0b84406000901e0410919402d690384d510103000c6401c10301007488007242e0010103210484040c480304000c0406a40064089030b03980c0e01c8558400c60000e00042d01d03040590075515646801e4540031110f958052084d00e0840010404000b18800340c03c04c41d0001e03031254801c3c1311860b0184101c0d80b88016032101c158000110000c2501c640c07200318010403052500300800b0591004008444611400c1c81e40e02501441004e44000c1038141c44100159640c4c481c4000f1303c4e541200105003411440700e40c20040d480388002c1d030790194414204a820503115448d00126501c041c141400b2514212103503070840010201c0500314901c102c003100c0005600c00090184458002400c1c90040c0e90720b2443c035142e0080c4120081d00a40410070078444500b980c1c2100001d4112030302030920b0308 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 500538462 1250 500537212 500537231
    0x90a030b0c04050a1511010902090705030a0609020a05040f1a0f0309030706020706020417070303021b030c03010615021b030319032333010f02030409050c0a030b090f0109 75
    0x190b4080d0390030668000c2ca1508000881203142c03014440948000e03101e042840c209810218269401d00c0406900314181c0400f0400541c0710301c004542c0310003403000003d111a01c80b050b05040e41d2180340c10f0ba0000d940441d003070003a000c1140d032940c020b003983e0200d1000c500f40244040124040c0c40f000002d506404030008074021414811100035135030100c011959081d142c90150b0081d001400b91403c030307520044440c0d500c50400a401c6013500c3e01500284481400388844c5100c451925a210f41c25001d0b4890b80d100d01d403001d004002c007501d080d184158625940e00030003860990810081036140303003080307144080ea45021003101c40d051080740c14003440140000056014148462820b140c801d005250003065100a80b0440e004031010007220103001c624048044505840c00d480304620f040e00c080d0b144080d80201d074992a41038007401542e0420741e541031050100e54040301c1c900f04c0038100140e1008140c0c2d26104003503002d60201c41d141210b00700fa00010b940d0712014041c400843d91307101c40c0e1030f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 500539568 1106 500538462 500538481
    0x6050a020705060f0a1d0a0308071e080a09080c07030c06020a05030904090f050f01060929040519151802030103020117040303090c0e150402090a030b 66
    0x50519480d241d003013103421000070b00300d511300e5070740d901080008929042c0701d5481c01c08600c0c06069010081d00340908100f0005102000b040200361040d4541000c403140844091181d00e840103980d039403c0d40d0080140451480582010b40201d0016507110002039598107aa01c4ac0300d40001841d81d0f0341060381e8070254503800400640091101a035181001d9114034205030246102c10451043c9842c0c07503041002208508440380d4540790244a020002e005890b0f207485a02d00300003610464807407400c02c012400c000346104d1a00c0f2404508550981458649403da913a00b0070032a042d45d0b07080394003403881d86200d890240484100d025070b65024a1003640d04903034040c2c49201c4c0c0c00b4109100c1000c0c0804c010400c81c00c2c55a01c165090104020362810405000380c8204420203040c0300030601203194082c4521803140780104104081619402090f40840ba840615000d9503140c80221 = true := by decide +kernel

theorem cover : BRFrame.Cov 500359712 500539568 := by
  have h0 := BRFrame.cov_init 500359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 500359712 ≤ n) (h2 : n < 500539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
