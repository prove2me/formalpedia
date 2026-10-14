-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0774
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:42:14.833286+00:00
-- url     : https://prove2.me/submissions/b2a37b49-b531-434c-86e8-f45040f559c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 139028776 ≤ n < 139208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 139030026 1250 139028776 139028783
    0x13030507080307090504090c170c1c020f0a152c0409030309050d031a2704050a141e0c010f0e030106030807060b0103060e04050705100302090613060f030603 69
    0xc00c000c40c0414800d60146400c1209440c1c03c1e4000340d0703a00000780a95060380c0d01a555140c0400d0100240000d00351881070a0001e20080c010b40d020000c00104c05a0b0303c0241c0e5003460301503e0710310045540d43c0903800f1705040010716810440d515510fa03105010000c0344030b8800300742308911030b2400740007a10810301b01142111001a004146105000140010000403030a05413141e982c2d0340010302c00d01130000030310020390f0001400541c1401c0c2412941c07103403690600400e81301c05101120100b40c00c0c0c26007070607502c03074001c0c9642d11145066890701071450301c06005c900c2044005992100049114071001d80010302c25030840e110340c01c00c2925800002c101d60f006c11622200c10301c4442c05a801074450070002400002c1e2159240c454829a500c00c1400715030266540502c4410b80d07802d8440c800107044441a503001070300c4c003561400e0741c03106179015282c03088025229404409100c1d404942c0440d8020b008142c85140302e000000c08210180104000705043c0c9059280503440780c8240310807240c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 139031276 1250 139030026 139030037
    0x110f0111060c09150a020d0305010b400609030308010e01141005042c0f09070608040804150507030906020c010203070809031203070c0b06040c0806010f032c01051303 73
    0x11103003040103043c0d001080c4560041511a5007465103400c1c540130f000070340e101d80c028180321045004000d00f120016003150341d074140c081c426800d051654a1182c00c410542130702c00d50b081641e001c1b61200c8010460341010303540055440102d982c5600030501c0342200e00c0380d01c5200151741c9580320840512000d000e444c0381804c20510300309451402e101064680c104034103105107800e85410101c04401c0d001c1049903050a80c00f413002005109407407849134030104814002034241020030501c0d44804651042604100c1114041070911030701c0001c03103006001c000115920001e419001402c50b41194400f80c01044030400009902400400c861b102201c05034065843d200d403681e101e0036203400130b0004a406118544415555100b22001180524881d44440030701e0132903854055503ca0004105600031420504100d40c01030308517083c550410000d00702801d502000000c11001802c01c000741350313004041c00d12041c050307940a0309111804844480284815591400e0923142c40224990007000900d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 139032526 1250 139031276 139031281
    0xb01030b06250203010203090d080a0b0f092d0103060c11120f0408010c09080f010606050a1d0a030605070f080609010302060a180b040608150a03080c01060b07110f011106 75
    0x30b05044074240c400380c1d18451507a020005401003400c82c0c200703c0b10001079a012011413090f090304110307010b034001c20300082400004031800c042850b0381d1220307010300d000b03540b00c3c408210320a0440320341207001c110b001110312581500d40c103c2200c545d028803054440b02d00d4001c4c40540c7c10310603442c441101030500c00411202e000d010444a17240c1c45070344003030b50607002800f011880c600c084c01880c0710004c1d02d84c0d0b040941e80c24080c0581c1411584607800010341c4c5412020231101d60043d081c2c40308140241040c4000740e408198503d42c0c55900701c006135206040d61004000c03c041e42d0b01c039134041d640c41c0e030320b000d01180d05507001c0e503070300f0b10955445900c50311440040006142103030050180c0c01043c6001100d0b40c00d40d03034403070010780419004070703203544030100b001e01c40940c0c06800380ba0b0082400c94034000030180e41c0041040c900ca10b00000d0311008000500100280b000d401074001081d110003000d030f8540260802000662030088100e01c103c09084215020f903102c1c1c90b40c41c040002c6100a0001d94 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 139033776 1250 139032526 139032547
    0x601150305060a05101101020309151303090e070c020d032001060302061209010e0703030e01180b160602160c030606120201050d0c170702100e0303072c060f07060b01030b06 76
    0x101c17090050031080000003050354505120038000b03940180c010b64010314801d220600004c2da43c0d040189020185450030603840c004c01d80c4880f0b03a40480714041e6082d1111303194a80704584c0c42d420381c0c1010b500440941461400c2507880303241d034180303103480781454407a6601c0c0010041c05d07a901844040c0d807284050180d84122900d40c40615000240c402c000981100328040d054180161588141e0215142e94500e08083d43c10103003002482d40c280000e212500d0400700000c0540c001e208200c510f08015102250030000c19504442200010790004483c44400c0d152088202e921030000b1601582041800101031000d802490754060b4140c403160704091300110034030700a15506400000304480d414504031940c0700b00421500031109036026014686140c01c1d00d5040c0c4112228a0031264020002c0203401c40d402444100c4028000c06010000300e00850810700055120b081ea035407042c4002a02c41c13035451504000c00602d8892030702401000c65110054003147e082010050700001c0c10400350162 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 139035026 1250 139033776 139033789
    0x30904020f0d05040308090c010801051e010210021b0705030706090302010507050703080f03041a0103050706050c030405030712020111010501030c09112703010b030c060703180b0c0601150305060a05 87
    0xc01000160031801c00d42c042c064401529001d94003600810010002e10081801c14405820382d036400703090500c40c0794904800318004420358ac00c65030103008040c82c3c41160342c2c428044540190030600b810364882d4462881c1a13401c10141c4850080c92091980002d402e0401003124011102161101e02009241da001503c035540504400c50b0349000b00d81002c000108400080c2c846032801c0020b040d00d928091070031031440c60480443d10840040e5000410016100082c0b4401791205071818548881c01e880b601490341c043c507046254180262000414080002c40312000303c68002d07030310043d51116904400b822034000380401b03081c0c02c1001c407091201a41d030b508608140042c010200c1d190403000340c0c812030800300f445030740703401c04415120500d0302e4502405141d04080007200945080106080043e000c0d2203030380c1e0700806000c840500594072103070b1000031b20001e210382c528980e910151001d84580f248030901034940342805003510a00928031074400d642c407805000c1c00206100c2d042000300f220 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 139036276 1250 139035026 139035037
    0x50102071a030f040c1205100605030a0b040305090a0905090a172805090904060501080f0f1b010e060304050703051b030a0b040203160f1518150e04090809030705060c03090402 77
    0x155400c100000242c6c80d0a02e65460381030a000d03002134400702c481c6081020030b840f15a44024402c0d0700c0138298502095111440b2500f040c0d0608016039900704540101d150117460b940048a11031400040180040300801d01182103442982c103400c030084407004c11135650003840c0160341c0304110741012500d042840306020044032064180341d4105240b040000c1c2900300100c904840141d00c4000400071070004201e0344081410820180a5016104200c1691402e0303203a10b00300c54110750000080c0f1030340103852006241a02070881d569911302420041c0c0d4440c3d09100c200c6061052003080303000c41c00100700041140000401034180e00749a80c0f0703848000d150103801030382e050203144600e0f40300000403c1804020082100c0c06c8084901c0e10060a080c104e0783c444031070a0080c00345104601c0340722021020162000c5070b28404000a000c00104c0d44911000c80e4070390094501052072051002c07102c00b40ca10305008030304503035a00b0f486106010250103540341c07900c2c0d0340c0d000340000e1009240c503401074036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 139037526 1250 139036276 139036283
    0xc080c09040f060603020c0c0a050f04051003020301061d011d060d15060611061005180a09080708030411030d020601151416020a0b0304230322050102071a030f04 71
    0x1000d0300b08110880480300d1541c132007804668001490131081100307001c1452030b5002110001056868880454800d000001d85903100702d5490b00000c070110220104035000e150050300800038152641001c05410148005e440d40340f00e82d0000026017058120003a4015000c0360a0701d185035100d01c42801303020050100d00f02e070407803e007400010101e0390328400c4030000c0c00355644a880c0f02514529035401c12074003030302c034541d1040b0900c0c040c01151240100d90301100892003088903282e9803c813101e4020014000000c1060400140784414030403440301942c000c0340107081242448612204045e914003600f03a4110168008a0042041000b40700090810b4191410034040f558209002c1c07030b10550048260b0000c00030340e4200d400544c00c100546002424246110b1491070402d034541d009a6480c03c0d0f20094040c1200000e203404035418802c1c0c1d112100001410003600c1d2148694410301030b0030f4001c550051194510000300b00d09980400010162808841c1e8a1a2a52400d00415500060095 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 139038776 1250 139037526 139037531
    0x2060a030f090809100905150c03120a0f05150d030815090901050405010627110f07050601061e0c021c0b01030b01081027060b0d06050a0e010c080c0904 67
    0x200300d61003960040d12002c51007280119030390701c2c4000c208a01400c442c0201000c2003801c00041c00b0a440d02c44512141d0b020303902000d0344034083c0149640ca50f20903040c14200100c55031050004900d2250082510440070800a001503581c441d680c4000e56481103a250f0f10006841c11240404c0c028419240c00c80e40e083d0241142d11104d101003585150240d0700c070407a0360754410402051180078400c690241c40c0320300c440b101038440c040c105107074080c2c1d0103e22068907503220004400c0f0280340045031481c603030b100300c22516280107040050315a1070034440c0201042070b054030400b4107501d0444d04081c0c0c01260301c801c24040c40980038050402011030400182ca100c0a4070a0046040790270414000d510a01d5020302c2581000140ca0814002c0b40501d07410a05044400d000802d604102d0403a640014841c40e26011103801d00e03001074030b07681e281590012411056441482986d40005110355400e05040c8056800c102900d800ca42c038910410000920105c00304011a40700b0740107112201008201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 139040026 1250 139038776 139038791
    0x70c060b150c0d0e030d0f02031b0d030b0f150c0f16090c0512070e0d021306030512090303030115030b04020d0b010f030c0221270108010905040f02060a03 68
    0x1046142824026000c0da126021840100100040081e40300110042c079000141200081c0806d585108003601070f41441180b50f24000b10f07520800646140d1401c101c6800c203c480b000350b4594840c02500441400242001410822801c04041c94070b110140a801104410600c0c4d0700c058660300150f41840a03800342104503c100c08040040e4441d481f140c0042d00c0903c1e1400741c03614116034044002ca424068184004190301d403020402640c80121410072018100c0b074000000d6502d05031200095000c40454101121495564046415680b144080b0380d46071100c4400c004040c011007005a1340750740100014415140560845190352203d81000f1070344080590000301039800c070005845071a0340d6600c20701103540e402180fa284810305810100000c45907060025141d59140f109005686051b201003034401c2c0020080b501c004214002075080380200014040401044c0d02c0840e0004a03400004114241d40b80305290265034400c0320b85203011881d41c28000a50001c0041d4010f0658a008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 139041276 1250 139040026 139040029
    0x60e060702060405091e0703061401030e0a05550318030b040c050d0c0509090a150606020601060531030503030711010c02012003060604031202010b030705090f070c060b 74
    0x5d64010b2040341b8104044400c104000e102d0880d00510003400c2508250080040ca0721446010180520038640070988940200106d40741400c030507001400e0703200d0050030702c071528006002d504a04c4038294001c90f001307044030380150a002c0b80303c07000d40e070384112070701c1100d074400b82a07403d2903c8901c00d05004411400075501030a00e0140d0380d0040c0c59800300706080000704035a10324a040a050120741d01020459903850383c0d4068980d90003810300030481d20002ca2200f100401030350000561110140501c03090200020010388114440c0c81e0152041030000310341c9600500076600d204a03940c0d40d4a14404800804140c010319110300246000c400045c080b01180c800d000852088001c1d490f101056682c6003821800c480f484800b00c0c0459241c018031030f03071048550250074400230130480e030b40d0b88a841e840c00140342d500c202c0e031000300000605120300e850240c06400c254900d01e005c0301600c444c1595241881911881102c82403200403013440007620803800340c1400b50496001d0000003410100860 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 139042526 1250 139041276 139041289
    0x50c0303071b06030203192a0306080606030303160f0504050a0b070c051f081b0a11060906010608010b07060605030f0a020a0902070305030c0721111006060e060702060405 75
    0x140242c41484080000e007150b0b405540c400c0e00202201d00e0114554940040782280c01076004030304142107a2111482d100744c5400400e542c103106200320310208240038100000d001402107110b000494040c080006806140100c150781c0300b8100c1ca00d45a01c0b29a940008907010104108148140441440301080544a120f00c3d03030050301800591a40c1c600303090400e0b00c11141a82c0c4101d120740c80450781c0340d00d018040034800c00558406e040c455829110519a62040100081c030b44055039030129034075403090f9011500b0f42c16200400107440e8143c40d00d0a07000c0d02c507482409002c012a0076800100036894040e030007801800d000352000030320552104002828000f603010f0740d07080755000149c3e1406614118461800400c0186030451a04807156030150203804014103015030f0b103101040510a2111040e03002c1007a8401001a240811030307102c0280400c004079034146400d102d5044060503c00c1c030f41c81030a00f55002c81e1505e00c0c500051004020056120380800c0fa04403006001c0001e0645030301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 139043776 1250 139042526 139042537
    0x315090a0e0a0c1d0702100207030e15130b0901020a0b06030307050a1b0803041229090303150f01020a150f110405040b010912020d020a171b0102010b0a0b07050c0303 73
    0x107101070040c462034003c011441d803440b41c4200404d480010188845a074002a0301c812601a2202c0541c0701c44031401d0603580740241002c0c0304d8200c81031210561500245100130410941c00d100360044454036944030000b42c0c001c00320f050f030240e8001c0d850280451905510550310030001011286403c029683d22030420044c03d1040b240ca800116000082040c500d540703101824142c402542807a24000b2000d030484484034001c1d2a558069030440000c0100d1280d11090028003151a050340c14a10045541c130703032040315080404201517401d0042ca1400e0b10348031b401c5000581c02041921700d141c0340d5180d40c40d541e01d11070404550b034840c0740d0310b140d0007030066600d00001c1071000b5480314a42001c0c0800d8440384400e90741000042102406001c1d00c0100418043da0107a590402c502d12610115080309019003040d2045039130709448118040c000241110711442000c040314840c90008016800d0700d90407082e655100b012004240004107091001d4582c080c0035600f110010316061010a056a009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 139045026 1250 139043776 139043783
    0x618020d030f0e10170a15030c06120b030607140c0703030206190e0601090b03100204080105240303070b060406030c0303080f0108070b19030905010c03020c0c060315090a0e0a 77
    0x500c54240882900315200381c020b800159811941d0811280005181085c038542d40380b400306607800842d60019040e4000e202c000210118000b2290322400c2c450a40b031018428900022501c46080182da41c1e80d018002c050342c0c010340103015645a50b10284c4003050303a585503050a90701401b544100d80710030041c0000843c0241c0103410b003404c2911155400e1411040300c941d080b0f040c00c40303140c0705000003e00d2504440303860b03000040c0e0340e4001000030f0901415107030b651003080c00401c006c00d4201301984540c0c01008041c403202104440c015844003012001f00d80c40707605800a0140d40046200c0c8409181d100e0401000055126182d58540b040c143c0590000c5e00010304101c1007152030046d15000e1405400001c0c004c1c5403d03482d0400c5250f0341d01c6154000e4074810b14a0380b9002d0500c0c080e8200602c41030b84240280082c00001d080100203402281060400d840b411640115a0070200110303402000411441e640054404040c403d1140028013050340c02c030344d1505000301c42c0a0502210131480e10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 139046276 1250 139045026 139045037
    0x603020301050a05060d0f050f060106080901050604090c0506090604030b0c0301031203090c0b09010201142a09030c1224060103061e05010807090f08070812030408070618020d03 78
    0x56005060850740c0c0100620b00161030041440b5080d600d1003020a2410351041c070411000c0300b80c3c43c00c6400c0000c6111600841d00c52300001150701c940000305c0b030b84520f8041c002081681d450004000070b80e800306034054011032000209001908064005007040040034026600e081e40c0c81d17a450303005076002c94a5101c1098040014420081400410302103241c2c6860309004214198032003001e550120710842c1400400014041e04a034002c2d0070002c40d0742e00894000300e007450300c50b00071030304011000702d40d009100f890807120807201c0d0300d1002d40d00c00000140042440c0450101488910a03201c000212030707100f104800350004a840c629800d4007080038010f0211400c00030005800c0e990070342c1100c0d0704032945900001b022a10481d80d401180c40034a014440e584451005607800d80440c2c1040c1410700f50741070041010000020650b044442c2c500c00c90780c07485016400071038140029200105488020450280071401c0c85d080344801240b4407541060701c2c00c56600203605e240070828100c02140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 139047526 1250 139046276 139046279
    0x11040608030d051501081005091306020c06010521060606070c03080f120c03070e010e04180506040c08030a020703080705030d1e0605030d0c03180308160b01050301060302130c1202030a06 82
    0x110741e2404d4210224080c01c0120361810000700d101d603620382d180a200c0c0100c03020800104003410203444050000c2d004002196079200c4800104d8950a003402400c3c0034031110040d030003050382c00c4402446a207140d03c0c003400c071036112401001004d90200c2c4003564198507060020001c105124014400826140742441d034404c00f2014007000030320020070801100b4414010401265008070304a4000107003407804100174030000b400940207102102c81405142010104001001800039007180030750700455544403101e41cbd030421700b0342d240308050400d401a00f00100070000140c02e440030f03054003803050041e6410190152149400c60300c034103508242d20f504614000c610074074580b0620002d400181d014204420f5414005014511b410000600b0019514126113030181e100e072224000d50ba0101849542c0c0d0c00b013804c2200310000c069020744100c0d883e20000580c524051080c88200e9501411090180881d4038400000b011804003540c144603220740106c05802061005510a0080301000030350359 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 139048776 1250 139047526 139047541
    0xe1b04050612010212070e011b0602030403110f03071103030301031205032a030411031b060d06030609030c14010905060106140c0d050408010c0507020a03170c0303040b220f11040608030d05 83
    0x43d9061082030f4140f10200b910722708103103804495a045103400040150341d9480340c1c5411140314100380c8d09a040c40c01504022225660007000800300c3ca0301070101d18200c09401400c2584a21081c07200170030923008203540d070700e01c24000d9024503071040407020400c0c001034183c09006d000880d0101c481c074040704000208010011448200c581409003a001480ca2642c000c0140a1024040d00d10310b01c11400814200d2603401c032a00b04d00d0280d64044400d120b07400c4a890081d200e400c40e0300d81100d400c00c1002030a40c01d00300c14421400d0841d002001420350364648581a00d0b103d18280725a02c4c05081048000314121040260b403082d8440340d42c46564603890002d1840c21689145080010060100003050241c2e490244450513249c100000f10b9042d04001900e005501c5201d520030001c0c00302104010030301001803c2c080c481c00310400c855120740000c0440194051707024100030303c0d400c00d82741480081481028500a407040240002902a40704c64400345160021404003614646035410000030307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 139050026 1250 139048776 139048787
    0x15040303060f0b03040b01060513180c080915040b15120709050a02091e06090312030603010c0309031e26100e13031b150905010e1b0405061201021207 66
    0x4100f0780e0f55803421420701e0365800d803455206200b04070400101095040b02d482d040314014004043d0401401403482000d08207034003a0a0302800308020665500000300504404665154409017035a0300420598076661071500142e000703881c072401e005c901c9448422a032a21480c10408030301240050004a18101c1c12900f070754001422001040d0044c802c02e01c5035190140010301d40c0001800c52103c210401c0082411380c00303040c1326503030b051003002c807400b003440003410040d40203140940c02480b0005400600350180c84590b407005001801101415030054a4000b1700f03010040e00340780c182d1041580d0024400130b540c00c00b00d04203420942109204100c104150003900810502180045034074201c0200801e894131a0b0010f02885002050764204400d200c030b118001541c040c0ca24004500b13910b881000409040400715619842d040384904403032000100c0300084050031039800800c200940600c8013400010380b950340c0150b000c410945a504082c0080c0002e6440705084107081d10b41407900414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 139051276 1250 139050026 139050029
    0x7020402030c09120c1c0f1707050106061706061b0102180f0a0b03010512070503030a05040914042303040801091a010f030807171909080115080d030b010215040303060f 74
    0x1c0c65480103403000d42036261007800c20340d03101071506500810b0a440c107041240c0c5d03e06a030001c103e01303000300f800c82d4201c0d23141b8050070706103002d00002c104070764451805a0b00c0041012040e10245800300000d01d20345400f000620790281d05481641903804610483c500b6600070010940d01600c15200c092440e04129030440030190080f01c0c0c080c0d1b614580080034040d48018010342d80514501540200d070018100422401004050112940c4d01440003000700150041c0c0590a083d40c04d010310303c111203c07074100e0180030341e030008804100c051000c4810041a000980c121600303010901c00001c40010a108900015014480c035070341d06a12800c002e10003000503040f4440140c1054014404541d224050b1510b150340201410718500c00d403d1210350a0182c40754645200040203200070516511020b44421034000a0092280501c6180d200b2107010b51409202c15a42c031010f11261494803940180d02c0a2030180141c50142070303660411040908101c1d01500840d440302020456008202080310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 139052526 1250 139051276 139051309
    0x1061101020702090a0209190b0a080f0712021303020406140907020708030a120b060d0f050702072409121a0708040302030d0b12010608060a050106090305100207030507020402030c09 80
    0x42c6403103800d60005480000282400c40c00f150b001ca00081141c1303410502490601c20002d4040509030b840f9090441540a42c1301080020362800215081e0402042d82d1401010301d41c4a5480821503515020000d41241c1030710540c1052041300003000d41c860b0b100b0b01019000d44141140030700001c07020301440b4100545035000310b50010408001c00394020080c0c0d0800d50071480c0890410704001c0e0340c84090070380405020392001d40007030420a52401507000f05800502140280702a544195003a07031112924812140400c030001c0000303c0d040d400107181c805140040c2003035166242c8036054030301d080340c03108021078020365146044c00425400c810b10641c410318030302e800549403034140c0c3c000f912401201070607080346441e503844402a5a40200040300d4501900080201e1591107200d581c1c0c5800c1621141600c03880c00c400890302e94803451a00080c0e0b40c000c40102021030445440f40300a41c01140181c0401205100400044e41d850001350b01a118501000351120224800c00503032406806d11039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 139053776 1250 139052526 139052531
    0x801030503030f090c0909011d010b10052101080f0601080304050a030605040c1502070f12020303030420030a080c0d030902030d03090203030d0c180e04051c0c020a0e01061101 77
    0x4000250000089030b6101482c000340c0200781d00c07035010a52510305469017855020b403007181042451001580404490301000c03400c159685d80000b4428201c45400a005401514070040110b86900070310041c640a111942d0700701c01d0089400c984c4010303d50a8001700e0b01500328107000060b8500c204559800360180c080912318043c0b0b40000034a00c0301c0c96110040a142d1113800007014400c01513103440041c0010180440c001003030603030003919405c1a004000c60300006010124101d4040158000e485070301070025481c5803a280c41e540c020102003880e14000900000340507441d034400344030f0b403c2418842c1d00e800b03449131001c0ca82c0078284004e40d64170004040c03034403d240015a50001c0c0001255200381000100003090b400401d042d032140405500c60a81400d0301c0460007984105c40c91003041500d04030f0840395464500c0788039a140c040c0c4002d403080d030202014007110112228271007001142c1d820644044010f56002c0360a070451b551010484440ca28010808190805182d00c00030386640001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 139055026 1250 139053776 139053779
    0xa11060c130e0709060c06092307061106040206031f030501020a08011202030a20210d0c12030c0e0415090501120b04060f02040509010e0105101e1206180501150801 72
    0x90840c501071040d181001000d0031400207002c1c090703100c02106904500c4134080c0014683e011040013032794042222040c426071400081c0c5510402641c813000c85050043c1c06a5102c0f0b4081103616000030b403c0699500342c880800d548444040e02c007a00441c8034100158035245085006080ca440583c4900b00c4c0b4003d070200900141c1e800724051042c035078440307840c07507030101e1400b44100140415950181c01c810001c4c00340401e519405104144400c1c41c10450b00c0c4419880d130101d9a59005400c014240c001100e008503069002c2c0d04800424061854071013800c540e441c002600b980c43c0a005500302a00c8220103008009003030145901508815428441c00c510954414200f04001080509010b6485580c05194640382d01124010040148040c8181d61a040340d40d003014002c1c80b6451141d8802e01c4e0907000c96001e94044025080101410181011905400e0b194620b070500d00481d49680c50b07401007042c2560340d0300801c500c80c14170400070741e83d0f06100c0c100c4940b102501c285014491600c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 139056276 1250 139055026 139055041
    0xc01020d0801060c06050903090a0b130807030b01140301020904020f0c0d020607050a110f0d0f02010c03090f0602090d06020409150b0c120a0908070608071d0609060a11060c130e 78
    0x120360080c4c0c0705c0c00001c0e10b0359503d092541980941d610940d44140b80c20340c000344848c94840a8140b4802c20440b20fa01d8964a170b11081e0303540c403d0302c001032840d41007500400185203152030768011428050009842c10200320300080c1280d01c01e000c0038a1081e00420306c009192010400c0c0202c200050006001e00e003886403000c1c0c401c2c00b0f0100c3e030100b000301c00b0303850840a40c03081c89605409003018040301d100141041010b460151080002c60066203000c00008582b40300b8058003040c17130f4002502e03000030700d1103882e80400ba50024550940052080720005d00203511440203100404916a0024495003043c0034010414030550101044050a1040340d040000100d0381020214550420658614148105803020112030303200308054050f1044c00141250409407152154045a882c4081c1c141358200d0700d410012213460381604642c080c40100c0b500e00b80030006191407907103810913400900c07400300110302d4641d08460a0058841c00300d6240c82081c50500044090082c0d02c6c800c05c203d152000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 139057526 1250 139056276 139056287
    0xa1d060a0321090e0f0708070e0f0d0828090801090506060d020a09230601181505070b04060911010c11010831020f04020f07020d0602040f06020c01020d080106 70
    0x5451400c0390040c20900740e028020b518610082a44c5000321209180402c0207640318041103454802094030180051880e6115024210030382c5801440740e400c0da40b04805000342d0f01e0029104a0388070f00c003004048940c100000e135a840300380840100c0e10f19900d03944002000041140d00c1022168144a590000036001244042d03010905036201c504880709400060b00e83c3d821a80541c0801d8a0144105c00d18034410007002200c00c440c1d9840c101c1501c9000044034409062140001071544c2040144001407000702ca0206205840c600305003800d490b40c40d49680220181c0b8200ca9039690340c80d01108004010102070103005003402d040010070503540700c1c00718000c1604c80180c1082a03240000319400c0d090315580700c0741c840110f00c00c00c3d040701c482c229261415030840309a2080070005c0e12210585814021541003403405480c041c2051a190b080c01003116203d10308036206902444085031401c0c1d021000001881c503980103101c40c048103c00a828055054400410000030070018029140c101c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 139058776 1250 139057526 139057553
    0x80706030606090b07330515010c06050702030f040e01180b1806030a08040806090c09191109041103010906090b0622050306011206110306150c0c0a1d060a03 69
    0x1000199100f14610300758000c2801c1d000886e80b4099a11441410903551056074440d9022104042110ba00c1317204000000700741400903907002845518005c00010510f410450f007010590044a09001e10942c9a0200c2d8025410a56008003044010880122010a0100c0c6d049644c0000c00401e40d0300b00104000b010418030703510005c2c4000000c2942c03a10200f003910b800a810124031600c5540b2060300588510054034500c89034461515000700704c0c94440400e1340500003411407000d410311200c440e44040c040043c0341040c0203400740302095494550340902480c0390b004a403529525810302c2111000c80350b081c3c000010300b070314050300003280340c4a483c212074840c0b044104805800c840003c0b5045042003c1d04071075014028000006540c0081c0e0760115541407040c001449055508140301c07105001c00c8810701d0340840b2500503070507000121002010040007983c1900c0c58150b0120100324846c0103a4000c2440c021070400079208640c0a440341074120404403002410917203180c680421a1909 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 139060026 1250 139058776 139058789
    0x1d060a051603020718020403110f010906030b011803050705030f03180904061d0f0c060c07060c08130608070e031906022b09020a1203050301090510080a0c08070603060609 75
    0x540c2114240343c02080588000c007041403103a072017896480066400b94100e4403040303504460001c00603501746404131542da9500d6041e502c030103034146009011006010b2580d040d505128031810000c06850240160b900a54000c070010914249070800381468aa0080711720b00050300280468500798512000719403083c2c0e4202c2d8004165101c500b0304100800d40c0c0f0682d0600152030b0040d1003070300b10000c5030070070340e07181a441a50b0b8030700f0b1b10006200c9a4400c103d5120410f400c144c01c140308d414000c070011400107008800300c1707080c110003c5022400f041150801804100311608011f01264407100212103110b06901070446503c1d0303880c0d140100400008010724190300460690220b04a18420321090388013659000d00c1a1a20900d440c011302800609a029040807900030440d04411000032000c03581c10354805296038a4a942c200003000040d1640b4011000b1070750004400d803003003024201243c080c082921040b40350000381d6291800030390002003411b06041080081e660001c0c59441111607 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 139061276 1250 139060026 139060057
    0x240206090724030618050114010306031113020f220b0408030d050405010b040c030f0b0301090f0b09031b0c0310050603070605070204150e1e040f030c0203010603121d060a05 76
    0x1e114143d020701501d40210706410354140541601402c0c5410440c126003000c0c18102410846800440695046c2c6c080984400020414442c0b103050650b540c82c6500106c0c103006040a040b00103c40681c0d2200f0884649800c0d03110024090080e8500303440c0080201c400d180785050720704a445522401341e8082c8082d001e581c1c0740000c0500000b900700c0201c22100900810014000307640141c002c003100110400d045250140b440c60324141441402c03496504140805070310006940c504145600c003e048040b0303400103014080c00c0034003160300c442c06818810083c0c150000c00c0000d0500e0b0420102043d104141481e06110203601d010030b070a020b41e41f040c9000f550310825800400d0180401c1c04400d00c0648044500092500801d841c85014101e4070003038030b606054688800c1d0030038000b0f03070380507204031113854020b0002030082241002e89440030b000400c40994079101d2900180858841e200480c0c00c65401456107130244c0c0100c10240300856515080c0a404500107110f070203042e031041c030140d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 139062526 1250 139061276 139061339
    0x17030405041d06010b12040b090a06020a09060801120206030103171c050108060f040b1614040f062613060b1005030619080303010e040c12060209011d130f062402060907 74
    0x60340ad03c418001c07036402920641d50f071030902c6002040c050b018030408001880410002c40c815003507090040c240358009004a0540e429501d0340340c2c10070040100c040f04c1840801c0001384100c00912036020762003d08000050962510044a0034000c00518003598a0160010400050201761401e80c002c88004403002200388507401c242d900440400214900400114002880b0b01d000044402610f80701d075205a803081c501c00c08400c80140c1c03109592903041c1c1141c0003601c0a00e0940002c41e900c0c1c0910008900c9051850100b64a80340103589940040c2e800420402107040801ca560802100c545581111a00d800245a1640010700800c10101084008030301400425000180070304109a40a0203c440030f01e0044002d50203c145d940c003040c0c2c04844101859a0808111803103413018101c6041e003030309040903200030080c030443e0f12410b40e42c0b8440480c031401000c0000d4003078444002e001d841c100c8c030040c2c00391502c10001c16840a6610001003407014050110056204186042e440d40885 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 139063776 1250 139062526 139062541
    0x60b060c1e010e01020d051608040519030e04020a121107050703141c05040303140301050108060f0102071e030501060f031203090c1203120b0103051017030405041d06010b12040b 78
    0x42824180120f100d40c004203050441400f00c3d40680d018115210500c5907042c3c84100c00c0c3c0b80100100c3d0081d040350002000d000c00e10381c0541441842c14400d1074100001e407138280c0090103d03009281640c1c0005c0700c03410031412800c1c25200e240590a940e4070558104801070b40e403141c0c0e9502901000f0b001c01c0094008030b05c5140208000450860941c1c184c10b204800f0550003085604188800d800083c2d0405004070380e40d9101040700c0c140d91041e905c81160345e40b01c206000180104078a0281140301c2e031407000812604154002c2c0070103020380c0442000e140356050403800c3d120182c101c10305120784a03070204002007081407030b01d0800101e81004514283c650400040c691103d901c074100712007142e180e4004050b441400d00400c04115074082204082090044040b6081110b40001d601c096210901000e42440480c550220450301101e11302030b01c034030116040d6121a400f850601c246440300c50b004c1002402010b0140ca209010749050940240c1c581c1414440508081d00002820700858000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 139065026 1250 139063776 139063781
    0xb0901050d060b07030f0e090717190f0b0f090106080613061814180c240c010204060f021216050a0f1b0815010b1303050a050a060b060c1e01 62
    0x242485442d4944500e4181405400001d4111b004800502241e006140505d4040f400074000c0d000c950b81e405000d254803041c00404180500f981203084035844a1030980c1c580760281010040000c0f02c007050694420082c483d0702c0004880440c8038020010045c4180d40e0710504190780a1411698000400c2c420844000101300c90b410040c1c1541c902e43d81000c1014843d0005071700d15499481340e68881d6281409443c000740c1c0c3c40000320050f00010700daa11300d07281480c00c0b036251a2006401032800302168500400651107007824070081c0c1d402142c10082c42c2d0700070010008080d05800546100e441e00f1136582214800e03148186807011812022a062010822002034000d0380300c1e1880061070090708103629403200011000281300107210f00072480740e2000c12070000260000c101071030140d007400481d144540210015500034030000c0000008144100b11451100d4000c501031b0080c84041e04001d410740e005003101600a5804006820011000040d080c5160b1000881640d4040050501034003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 139066276 1250 139065026 139065029
    0xa180902070803010e09010902010c02041e0509070609060f081603090204020d0f060603020412020904030318060204091a031c020123180105130f150501060206060a09060b0901050d06 80
    0x609101207228020081c4003002036069445e01340044e8256501c007080d00d4240c600700040203002803212034130b8500506103900182c2030a00400407003004007101d2421001203231021141d125055018040401400b5080704251000d480145007540710b201002c10003900b03001c006042c09001603030036441190498400d44c404007416500900541d603d8524503005005000701c1840068100c3c9014030014606010744200c60443d448020f2070185480b6680030450103250040c4241d091680350b50076401c034003810603040c00b0314a01c1100016141c604100c1e840f400c41c0d480307240c142c3d00d0701109990307001c0c0365a00041c080c0d8121525400803e08106041c4105d000d0400ca10481040c0d58008a82c409010410582c4034410400780900d4100340c044a0907032426600c003590170b2034014110400d42c002050701943c1560036540194148103403040680000e02c100e8000368400c6005130031550510003245002e10345803000700320509044c0125410018002c0c00b5100c0c440314a81404800035202a001c001500300c0d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 139067526 1250 139066276 139066289
    0x10303050c01141906140a0605030907090203070503100905070507080711030607020a0209060603060d020909010207080f0a031b08012102030a03020304052803080a0e19080f01050c0a18 81
    0x3c009003010551100100205403400d40041d00300344d004a440340803039561031368008004002c603220603d048001d80f480e0b80007811810181c050301402103540c0c802400254001e1350140d5880c1e45d41d00e020b4400c403020841903000402d01a00344004e0040c5698810107441035190401e20095440b0010319000300c086010b03201c0590103000700703000c000c0e415401141c419070340ba00070386070120f043d80c0751010880300e4441280d20703d61220803070f10701d0740150030455005c0750b010007000001481d000050311000c2460700401800d084001000640b09102c07980750140301c1010298560382d010311184450040c0040e01c0500460607102002240009082d100c90912005541c01a0a0303585190f110309009440f588030340145070003281304917020541d03003d5400c0704041002d14040070000d051300b196524036a03640070701d1400d410005085000d050035910070800c1c140d020351841103c3c030139a1030b194800e0f042800030650005164507000411040010410444207880100c1c42c1c00200c459146030702444008990704040b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 139068776 1250 139067526 139067561
    0x16110109120306060809121b060c030613180212010603021503010303111b0f0a050405130501110c03090906011b05030903070f0302060d05150d0303061503050708010303050c01 77
    0x1105000741800c035241d03144a255030a00c032941e16220182c9020800b0b42d0701c24a20f500102042003a480480c000c1c0c003a08101118440703260350601185850528140c40903c1c010400009200c0303140740841c440741e007880042a0038860107440a100b0b043d18441e0740000381c0a60094685002119406e5114002960b4020050441d10002088000c2d007a0400d00049010802036140307816041c400007841910741d01400c200401741c401c50424005502c00200301c00f5003000901c240811140e907a0b000351441402e000200b01c170316510038148517080d181000c1450800400400c02c0c007440190102c11562000340559601c1c84580f180d0700101c6198865001c5031040841c61141941002030200080121540890485203016150420000703000d81610000350700c600700300000c48100758a904440d9010080044420420012002088500409036400c5000035903ca00602c0401c103110003401000c426032500300325514061001070000c0c4c4041c0009801e1000c00700c1c0c1044070f20402d4005010025015029 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 139070026 1250 139068776 139068791
    0x313080910021e060c040303051c020313030305010b091503060a0905040b070206090c010f0e0d050d030b0a0e28240501080a09050316020d0c03050a0b0906010509161101 74
    0x94a6403540009602100c044190208402c40001001340c000c03a901c1180368509071540d078080c2d03050340c07003042038202d0340c03048050100c2000c0c417a1000c0d5100d100000c005501402e020315004003100c6c8141c2111601590510103c0242d46561010741c0070500070516259803a00c40c40c00041e0850f02c180e014a03542400c120030003040080c060140350141c0e481d6000c5429946440d45540d484119a458250002e102907001c60343c91486410412100d01d0040c0c45007102e4640ca488890921501c1000040842d484400c2c40800c2c0c14508070b440020400391340d400c040d90801900d10849520600c010042c80e500e02200d42c40103001951001024140341540c9071802d94000411201c00d1001d4840c00c0e0204402e880015151035041c02201d00c3c566001014600d48051100d603110a00c030405020303078000d0300c00a0314800281c0e110340b10303002079405a4000c0c000344040b4640500c1d41d007030060204e400740c0c011000400c1580c40b02d42d22103401204940d5000410220100300319012084000000007a42c00d0051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 139071276 1250 139070026 139070059
    0x606080a03030902190803070602070f02030d08270309060705150115030501050607051c05040b0705010b0307060518010c111003050712091e030c0507090605040f0e0303130809 77
    0x4040f041c503100b901d840684094142221050080922480f83c081e00104002c90005140b507004110b5140b2807800c1403010420382d00800d00d40240d00c4947c502140300d031414803002c8440b20801038000780c4180001984590300f03440a0340c0364081c0408107401610085083c1007000b8040c054500844103405d00c0303190660752816041c0102d503ca20300c16002ca49001d002050314280501110010360300480207100c82c68220361030340c41c2d03207041018070310820509100109801c49c180e001040c0280c0544008a40f01c10701d0303030801d4104901644441d0034071400f00306081c0032a00a426208a0700000d0a00f07601254190501c0b100c156070000800b07500207484141c0d2041a40c150303000a0060606660700c0c080010580e070701104031044448003500440001400700c0406c826810450002d621900d030502c190340031aa9030504c7c2010507000340c86900d031904403d0240d4201441040380003802401e00380203413180302400640340c1c03101416682e03c2500284071007080c4620441114030440c03011f090842202c25601 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 139072526 1250 139071276 139071281
    0x30e0307030507031d060316120e06060301140105150d020f190905012309040f150e0709240903020603010602070e060f03071707031a0a230606070606080a0303 70
    0x100210080740c1ca5004001306081842c40c1c50360782e490081e00f100e01c1c549403408003c40044921940c030040020300b007202d0031009c100f03000703040148400314014071030f41c10b0442c1090f081d14203848200e64406141d00040140e0fa4454500f00455511010303815540c000704c59001000e88200c8080320002030000409804065840c1203a620820569460020158688004540c54907045000c608100380225031082d041e256074001f40440c0c680144000740c0840c44074000d00a4070924400c05d25a00147d00041000c1c84000c0c400710341c00f041e240b4100d00c00904000350903841c0142d4500750701300101c100c001010582d0144e500d10014580080c411a1039603554280256500000e00801020100c440c000c1842c50500d81c0224050810040180c0103c9007441c6980302414000060002c051040b46000404034002e03c1c1d002502c0ba640415020461400036620415540444500f07a041d400e00d06141086250028100303402c290100c90b080d90305c01d01070810740040c0400c2d801c60800ca01032550340400301500359 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 139073776 1250 139072526 139072537
    0x120b010602010e010504111c0606030609170c0d0c02060d050c0319020f0409020306060d020a0306140d050a020f060705030310080c01110c01080612011e050901150312030e03070305 79
    0xd81c028808070112000c05402d030b4006490080504043c043c1d41d484518208114a180c20740006c540c1c103039490603448010642708140d2050341c085030ba503000003003030000c1540c07540d40c1407251110152412411034840f0303583d100b80c101c0c54010003036403402ca1821940d61804590313502c3e202c0c00013400203090a448641c416402940d0f45c240e00c0490703094103815040c250081e40e480c1c51075810f016040500e0b0040a2300a035100809c0103034018400c10070080c40d18041d10240a81070155540000e820703007894203858400f000700c00568031409405c1c034001c00003100000c050304a240d050301c800360f0000b440c00100d01207001c0d03080001e05a00002c420405450b60320301c015000c6640510858000b850580e0043d900c0740368000303c065070303900141c801000a5000300700c242e4004d00013818041034210341e0030901d406c64403010710100301618ac1e241c083c0c10068040c01900d0f0404c2d6258001c0044080709074036106200c00c58440104520f540e054540d410501961185070207031104800d50707544402034500201907500a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 139075026 1250 139073776 139073789
    0x409050a030807030b010e061801020a080c10050606090306040609030e2d04141302030c040c08060a0b040501120515030a05030406020123010b2b020903070e04020d0219120b01 77
    0x188441004251f02c2590000300c440740240c003440c17804400510420b04601c0c284462815441004006030000c0c1c4840b00030291201030030040c04440300c1c1d58507110282c5001500300c511800050014442c40daa001c5522030304a41d001500254031031240c901074031903842601302280d010020302501c41044c00254828506d5200d01c030faa00020f200d240c81040103c880840d502c15620240d4000151000d13900160b4840d001e0008084545c900341c5140000c003541c6030010014000b903410400e000321402c0025616000c0c00031000c2040c14542400002030440c0302d003000a64046440b5404616002c01c440034107a2410740107819240005987c1c1030aa5607503200348640c41c019031034021429250a40c0e20010320100d600c000a180013130740f0780404040a500203003c0c446141d200c0c11202c1400041c12510302c04840300010b030140e101c0380c20301c0405003001d0391035101500f4640c0d01000c000040e074440040c850001d43c1100c03883d0070b641a1a181d90070440e06500b01d0603114001203200400d04c0001c42025048414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 139076276 1250 139075026 139075031
    0x1207020a091a040203101712030708040c0e010b09121203130213020a050c16050a0506030916080d021207020907030905070e040f12021f020a020309041b090614040509060409050a03080703 82
    0xb03801340c0496582c6009230030685004000d0010070301c81440f980386941c0042c042d540002e10603071186414254580300303a116075500b04000070345880034100355000b900c04805010141c07803101160001103c0034400201010112004044071004550348c600043d5007060034860215220b0014040103001a40b2140104e06c4034030031171004840b00c2d41042d0511050b50000344c1600d03800b510f02402d10000fa000500100c11171300034201007030b0b150742044080d0402000c03400f00420760307000d8440000e0304013843d00145092a01c001c02880300940c45081002e41c0280c06841c0009824403d424864102129600300c034203049201410310080c0103041e002508150f002d41569070303c280302e25906990f1002c07442920301c0c1caa03441c0b981d19443c43d0190760203002060040d00540c2c1c03405580e1000a8211120203c244a03420500d421600065921040700000341050341410340300407101c4900d8112174080c9114244c403d00303002000800e5516550403072400d06600008482c42d0050b50b00d170281241c91304540c40c900092 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 139077526 1250 139076276 139076309
    0x204090e0c0607173016020102040608060d0807020d0302010b011403040201020604020f0a050d08070c0902090603042a0b0909060a0b0a030222060c051207020a091a04020310 76
    0x80d00404941a0f1035001c01c04032503920001814012036040700f5a19950a0f001824200b032001e10070802c102120100c11501515284c1550303d413a0f0321261034108401c581c8144002c1c4841e64008501c150041e004486802d030483e0f4034545505a8454800002d401450041c40b6000b0035805400100c1d4550090f06c07101c1d03074216080258a1180021a07010b40180e215031b0204000d0705017800c0401e03903402c0c00f80144a061792a400450b40110407070b04102e942540000c0c080c4c040c800002101006481d804c54154a00010341b400207009020140002d03080a1401c3c10040c00d011103111911413800e003c0c110329905650f504042080764010301300403030013182c02c000055014604444400c0c15900385d29180b504060140200310300a40004c00c440710325208610030085c00c070484601000090807996100000d9110701d28020b4184200a4000b07807401c0800c0c0894030050b969070354400150303400a00002010010100d100007450b00034500560046e10010601400c00a0300341c1003410303115642403511108 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 139078776 1250 139077526 139077529
    0x30c15071b020a050405060d020411041d010305070b0307050706060b0c010c0206062805031b0a1512020705030d0507030c0306140f150409020a02011413170a11010204090e0c 76
    0x801c8501d0009501290103c001d0205140a500081e002800a007001c0c0c0341202a41c041000c0b036002c0144117840d114003150030809644811141902e1a003008009105949180d48013035695289005900c4103030008400070b141288590207450b42c4903001803043c00903e0b91040c9641c039a900144090b0483c0d420940346406842c00058903500038400a0541c0004503411005030000c2052540310381c14030300b10050300003259501004004c0302808504042c03008141280c00b01b2588103010b621034150342074000c2ca0a54520b0f000b1880c48000c0300104800760340ca061502d002e5080d0b02c901c4e4146489140352005100781d0740d1b0705500203000c40249490402034070b61200300c1d608000a1203201c0319400a03801e20007180320f05101c1c013241840720002c04005d04145d150f14001c02a41c00040030301005170f54801510380f010854580c0b06802c4112508070201458158483e00170321004c2140c40c40c4440c00000e56103c009115044d8683c40128507002151102d46442400300601820780e00d40d104c5204018009415 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 139080026 1250 139078776 139078817
    0x10503040b01050111010f020c0312011203091503090203010e0a0302010e031213020109050603040f06060e0103080a0c0311032d03060d030f03111c0f020310060c05030c1507 76
    0x366070015000002a03280400441da0f01041d001c20784e86a5489030780301125800180046e05140e00b146000c0c6850b91103480162030f540300141e224048804003401d00001094209030171005941561001008001c1100025005000541c40094042d0701c2c0c6485183c603a0f00114002480f580701c0c0d4000c2c004500f44d03110070792f540d01808850b113076100000740200e14442e546440d400c02c0d0754410b0404c5884140d071040003d00c10b0300119021340c0c840d0040b81140c420070180744112805005605c40302d44080d41583c1f43d01801e4020001c9a205004004c044801031501812400c410345d942d00c1d080780e47d54a90902c50040b202d00b000b4038454011401b42e500c4030112800b03000d40707204100240c640c2120b10340355202100d2030f0704000422414559181d480c00080030305d03100100203c21103404043c0802c0790070454101118030858500d40c1c40c51060060144500b118084034003213036080d2820340540c0c0c0032381c10000e0541c0301c3d1102c801c20500c02c60514000703292040e44410f1007404541c440c111141e80d0b00000c2c01c0c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 139081276 1250 139080026 139080031
    0x90115060e010c0f06020f0a09050301140c160c2718021e0301050c040e060a03020a12080919060f02031903050a0f060902090a12050c060c121204020f010503 69
    0x7050511440359015442055605070081c05250760b43c02d00c144c19284c400407a40300c50300d680d1400c20001018200282c11080300c8000b0310701a8020031000704a042c8203003030f1000c06003260314007040000e04803640d0401c0b03801902c03006130403491103040295910b80701c401a542000640c9050340614040140000321846003008a1050b0052008a455207500f0003003032070049030703070501020550101c5180303030b440922955101d69146903001e65076078213200300c00c82041c40050030381d4030841b2052814001600c030210b403a800c603408100d4525001a8a00d0b00308070500815581d1078010894005c1c40c0c41d0615068402c3c411518181c89064206840c950120384902c600031803072004810742650041918440ea001581c0301c40042c80001d0380c2001034415106039181a4060000203401041d01003003840c102806070000d01002e00010400510f90381c0303c58071a5420b40e4094400d074000b19110002010500400d80211403500405036988800350441c040c00c0c00c00e03101a40981c5101500d0201540250308036030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 139082526 1250 139081276 139081289
    0x1201020304050c0d03020a0b0106080403030f05060109031101111902040e03041a0706060e040309060f02010c090b0906250302071706060f0f0604030803011806180b040b0a030506090115 81
    0x41c01c0d01c1e404c3c80780180c2e100004504500c5013000c1140410302d003000c042e029007619a03501d01e06d030030103007402410b80715084841090649490180020388c7e8104a800044941c0180c0f83c018040348080162044051051905154010810f94030b00100e26031110981d5180f00711804c0040529004410341d0301d015a000345108080420040c0703080242600c05090807620595021500300c2d121911501c0103d0240d038201c0c0421300400c010312a183e04140c51b420907460610080140d0000d038080200284000d100e03071880d04c00300199140340c0f515070000302c03802044d1210130400d221040c56031002c00180440c605900501407004080307040402c108601007003030003100c0100748680b1070800b000800701512400030740c404100242442c2c1f580307030a0080d100450050780c0342c0c1c0d140e41c54240c10218400184103040703540d80c582403003800542d04292503080d01840c004400183c580d00440850700802d80f03108510360280c1d00c0e01c0000704101001034482e03c180e44040090040019490001c00c541800d1300590 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 139083776 1250 139082526 139082533
    0x1d0603160b0f0c03040b040e09010b0f030a021908030a0f03060807031709040608060703020a140a080126100e10151208070606060f0206160206060d0827120102030405 73
    0x49a40d4094000d04540c40003107003130300e25003a9910f500c50100e80c8960700544800d41e103c8100000220280301e0300400d40020b0322459900290039000130340720303030744404002c0c442c075504248000803150f220220310107802041c08682d6102a0b10b41c0143c12403901200070320001c1d00f450408105d41d0b1020521504580d4001a88000c0c0710102d0040c241c281c012100254005540c0c1400203440203003089014000c03000c940740169140a960350003414542c1c90000341200200421506420030f920425140c111000244044a5500440030140d042c43d48075110408a1080c08400540151186d100364030084041c01120703440c50f101ca2254050710b40c0c0c0c01c1000407120441d03604020243e08000382e0f1011b18800c6200c64a000c483d40d80710021144183c20410005181c00d05499446404104841c0c01200e448051140d2016104000350b0711907008000038003e0302444c6440c81000104030684000702c40741c0d41c4070300c03c00e000742d03c150184600c0d11610724413603018076100001c0c040b410310859011743c0d0080c021b03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 139085026 1250 139083776 139083787
    0xc121306030b060c0d0e041104030218220303020d050112021318020604030507141906031109130507020c010903021c021804060506040510061e0203041d0603160b 71
    0x5800810035900c0d0b55412810820010000e1001402007036000c00041d29600c01009a00041c8011a55041c9012081c00001c00007400503a80ba0060014002000c10026907640c4ea01454960002e00004a00b604080503c956504141d0075402034510442440da08201c0d0380e036144940800700101050107500940d442103c42000252604901c00088039004c100c0d0120300301d540030441036486640b060351140c02483e000d00a189101da80c800600100316001d0721000004c0e070069035085214800c05052641c0c0307094284a80340a40e0036034641840040502441c1d51110481d00060300049803070700c0040c0540c00c0609155800b92420b042541d070003401c51a94041e000540103c40941c50b41c0030b0f0f03401440003000c120401c4030704403114415031243d88003007150b091003024002520303805441d040b1059400003007445031550148071100c42c110708041c040680088442c040e030035031090350001880610301c1507100e0340150111045038042e49042d01280c55825040021a00420315401003580300d010130401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 139086276 1250 139085026 139085039
    0x5010312080c0c0a0f020a052b260703080609070903031809020c1c170708180304080c150c03030f09072c06040b0a0b07050c0a0b0c1213 60
    0x16282e80100503942161805282c402d40304e00d0a44000000c5841c0340c9a20a140d0841c01d010607104001c10b0107484c590601c900c0303d4032481c1d00e0500407030b101e1805440459401e091043c2d404250040c01d409001403410828007410b00c601541c4054400d4011603141e2008c25214180300a00030321a5886541e070304842400c40d036040703500301051020300c007022245d92004101c10a680c8001c180c10076032036000b010301c004c00c182066240201048a80300340000107150000d079060f4603842d10343c800c0790361400178a2599440e03c81d05500c00c607520200441c0c40702190101307894000040c149402c90046810b6410b100b5002c10103010343c8610424003c50b5002400401c1511010421158020f40300d142070b034000d40e0319440c080780a2041c0c4424001d03034141480300c90380d40c0c0c014101801e411100980b030610212510101040881006200e0b075007101c4400120b41c0280101484115200c03d0010304c0e42004c2079450240311200c0c1c01000843c600707802584540c0c00d2602035102210081070040c044005201c0c2f170401e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 139087526 1250 139086276 139086287
    0x3010b0a030b06042f0301031211030a0e030a1b1d1006180305030a050307080114010807050901230d0513110904020607140d0905040204050a2c0c0703080a05010312 72
    0x80f08400805060040051002c3d10f01032040c5c0c103170300c6100d002d5200d40c914141105568003801a400911040704402042000d01000310f403010f5081c3d0403c0000b0311503030400310f881e02c100081e01070015145c0380c0702201e5a101a400c21011600c0386054001e401d010141030345541030f402d448205142040304010400ea90080410381003102c403e08041003420341e01e84845095900c810410717000034000208004006c2e8200d060790340500368038056427540e4512140040c2000202901b1801802801b0989440c51382c0301e03900d510b0000410750705003541d107040c111124800340c0001039581c11083c01c0500040e0820034600c04410f03160342105c0f18041c0803007a08244005000c011300203a130000ea040040e100890301696420030f0100700007008110403156420014a80324198215a2003280104030410260769900c081c441075826004140000c28540020640b181e4a03229000c00d1002d120000c21038656804405446018060b441c2d28407559500d016038803c41c0e0302408010700b00144c0b03000d90b803007c03403064 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 139088776 1250 139087526 139087541
    0x806030d0c1202030f0d05010518010302010c03110c0303040b040e0f0f0a090516060216090c1202030c090a03051605030a12080403021005090703150b030307170d05040606030203010b0a030b0604 85
    0x40c0140e9151aa02d17500c400c1c482d6200c2048040540d440c4c43c0104943d09050075150b80528400b00507071107a50555000a2144000d80406410400500351450001500f80a0441c0c580002803c407942c0347d5803041c1c01500c94000e0300c81c07070540141c3c2c8000100c404c1c00090340284500042e40000d052030395070b00641401000c0007031058031640703d2024581724082d900500d01c000780960340c0007070080020400340600c1000d02a0050341d000341c00d18045445c00c03074000c0032840354103464050241e101d039101d1200c0b0445001d1411800e034415010800007051003004106a50b46800900000000c00d85a4090607601c21440000802030701d00200241d209622490506030003e00c00d2068904804007002c040059a500742c5001d4070070382000340300f0000c01c06c11382e00100c501c84040f60140840b01c06100029100d0007a000d0141815054090010494055400300d500c41c11203c041085242464203021004000d680008c90196103000010605403404201e00740840c4e500802241a9039140024080a48200e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 139090026 1250 139088776 139088813
    0x302030906030f010306051b03060409080705100204050a06020d050a0e04020d0f02032d0609100e131218061409040603080901020606011b0b0c1c0902010806030d0c 72
    0x38410303000955201030046006062800d050900c550440c104001124005084921310780d800c44c40203030030b610b4900150703907020408441c00240c80301181010507807445a003400800781e0081420f140d1000322554060700984d80c0945156609a4907444241d135240400c09056010600900c01c0c0403c46115420340404817102410150404520500c01800e8854003151809010b03004410040707000100c80440c024000302600c1c01082010307181140c076500d500a0100b5014402c0b050001d0326025900d0710510080c00c0d44100d42d00545805000402003410124046894240550098200c5c52141710b1501da69072180c140910308a107481c40c151003004501000052203801407009103400c4d03480d449000001e601801010360754007481c0000904080d00145500d05104511030904065100c1420030311882d9440385c06070a140e00c4820100c021341c050b1150007104220b00710040400c06100f500102007503031007a01c581406440c2c1904064440c0003060445000446500b80c00010541e0200300c200301003076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 139091276 1250 139090026 139090033
    0x308090a15110712350408030627010302030d03050103031d12070303080114040203130809010507060c050d0f020c0a0f150207081b070b030406020a1709010606020f070302030c0d0302 80
    0x1c45030b442210301c0012009820118421180e84240409481e0216040b42a145c0081200f802c204030010000d00e8003410107403240c20701000088050721001d0501c103d081c045482510122952a0103131003d5400f400202e01074001c6401d41520301d802809801d05803681903d03079032003c003940086801784201111145900c02c008014100b40454148221800303507010340e41d01e016032344c1046008142e81c0007115040e030040d8030400030460b00c0000d1b00541d001040c1c1c01211940ea40380307141c004179044d00071107901a240e2840c0840c1428140e4004009205480e00001c0174002514100300401c200d000e0300b10083d2554110103081c0000903801284590480c0c0709480c052581d04240c1c044100b00e0f004414221402c0d900020245c07080003440c10211444141c03a40180b02c681e04004154810740409031005040d141c010900c010f03400c1c0502050719070f00342e542d50204d0027840d0240000c1c4c041c0c0b010b84a010054082c8690f201d902e41c0001c111007044c1c0390090300520b1704901280c01c1c00381e1541e820100b03030114007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 139092526 1250 139091276 139091287
    0x3070305090a081c061202060f07030311120105100309020f01180902042d080a110319030e0f0a030206191103180907020105100b0c070515070308090a1511 68
    0x600d0390b00500800c41a8204c803054107a1609166801c642c1d590b08141c210800c8041c60000603504c04049841140848071016261840ca00d1f054001c2c003091507980041d940d01003000c520784640c40c01154126501280c4800c2c031030f00c10b0031094044914004029401000d6010408125401003205c254140210262805500e0b0358140c00400c80e04203070011150b00140400c03584d40a02000917154044403a90500101c02c0e29010200707940f15104c440c0101900c420242e40d90a950702800416042c0c2c4100702c240412803c280b400400d0407070802107052185004400201e011b052070041501aa54054032040c50b01c84c2c11540000411b1480300080200240a00498401003045c00980607030301e01c0c0c021041010704a042080466a0700501100443e85480c0400c8503c40386135254900710703107802603641d40e1600c190300301909040b066004240c00824054a86071940e16180042003058000c0c4d8a41506884081388103880700e480c2c900c040c00078100c2880c60740f0410700e55445810315200000d855440d10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 139093776 1250 139092526 139092533
    0x10b090d020d060504050d08090c15040b070c0306050c0c030f07020303090d05100f140601110102210108071401080711011806020703020f0f0312130803010807031104050c03070305090a 81
    0x1400b000b001201c80e240c40301c0621042040c100082c1301800d00d107081c120003501e00b080596907250041056203110b005011484100d9585000c110303405881a0b44400c0d81d00c903441c2c10329201d100c40030f1100700ca40d94a03040000c0c4e003450000c0d0039079480400c4480518544600481007800541106505a074540010040000b02e0340c0d07600c900c54030843c0300344041d20703030001ca03010f000c012211300c02a003145440c142607400c00c1412001d8280e90744100c003401e007400e1820f16403a02e5802400b8040003076110074244210a00d45040201c0c0041c101c0700483c0c21611803d131219520a180f080c00c81c0c040740464583c401040c4980d025170480c06141c60854000540542030341540d07100110600ba0a5030690b80c006800f074141076050142041018840e4001e0030503210012450340d5034440c03175009a02020010011542d0340480e9100041d4803a0810b140c99180d5848410541d00c501041c801100d4140300403c0340c203010308180c041d6a00c1007007071810392800c580d503004080d0083c280c0100303809801d00804c2c8541c03001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 139095026 1250 139093776 139093789
    0xa08031e04050d0e0612040f0c0b0f1803010c020a080c030705030f19030e06130501150f0f06030606050301090b06090301110301050102010e0c09070f14040801050615070b010b090d02 80
    0x118010b00c0100001c851914010b00084015461980640000c05c54426000c0d40800c0c41a085a48502c0103154541c032420048030f10407042d004042000e2000609160445400004d0030000c9501046175514030010002c25080350305034080c000268212a030341c600401c641d000640f5030043c22000740d0380381241d541d45441c1190301004620a1002c40812506001d01504000741043d01240c2000c02c041840c08a8448e41c900c80281101c05c0c021241580d10200b1000703402c004e0741c0650740c140601742c0545a13907070300c5100d4116010740441124102c40000c0c4c0d0134480d0003a84101c42c69500d41a1459003800900809400c00006164215104016503d0346450034864bc54160515440e100d03200d50400f0002802d440d150710340740500307038441c07210090b0300c0c0e8580311110782100c2c0078102001d030075481500c00e803000d484848040c1c00c1c070100450f0011b04200107410152007150308960b044075000c11000e0142740c80c050458054100c00b06c000041c000f54250307200030445444014940d54207942680d0003e4527 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 139096276 1250 139095026 139095031
    0x90201120c0c1109061807020a0b01080607030c050f0406050d020712030b090c0705030d0c1724100e01030b04020f07080c01061508070e0604091415060c0a08031e 71
    0x41c2c060720300e100c00c1c490001c4083c90700300703011680309a00e0b040c144c0005200f0020030018560710815000490b0303206000b00310003140a60301c07000d04000c1c1c0d0782d00c414054a0b40000c848410201342042c100000c054816001c6940001c0004089400d0a050002c11601c98012211049001b9801c1101e603000c00c03001c0610f0041c4003001d0780c01150344401c5030240551175002503e46840910300380050700000d000441521018598a100000d011140300c904a039252803405c409151f0031a0002071041c921a03100c0405190b0f020a550224080001010b1015000000c08050001b82182058440760f40c402d80081c15090310051025040540b4414000b4040c0d2082d28104c403401400155818051b9081c0100c2000342a403d15a9040d40441c2c0d4010300b81c07185c01840e20080101020b605021030b03456805440161070b180c4810810b00301440007030400140d00b940c3c00700081e089194003c2c4140340c044200c602d4000c0070b0020f0b21900070740795290001030b040a051480c1c11085d0601004861b0b012005492 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 139097526 1250 139096276 139096301
    0x31707021e010b040f0e0705040515150d0b090105060306010507050c0a14121908030c0d15050f030a0c090b0f130c1205090607110102070506090c010909150909020112 73
    0x20b041d0210b1402c00c03049030340d41c045c1e190005007003c280151003200483c0e203504890066901042075138806406214010303040c020a070340031051075020701340d889a032000780580380601c08003000400c22000805c56021f00074800d50b5803103041040040da4651140010780103d600c034000719805202c1100000e10b0070405500700c40e12507510281c0300e0a0031b01d007064260880d04004000b07029055069017000d1044d5a4440307002d0060380c030010104161481da074085800b4180c52050400c10000300c45101c0418080a2188510500d00200303036440a150201d80480c141c0e6121500074805442d1548500203000d90302c220f640d000083c02044031a030b890308282084a011048400240980c2110010308802151240300d040c003450704080104900000582c10b4010b00c4a0a00582c160405485540a40710340c200040a90054405018002c00c0010b801e03030350b02074241c031480001a101d2413036104880e8541d40b40c2140150340c0342c04101c150200e0b84014074050040c50003048009400042c002520b4800e131001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 139098776 1250 139097526 139097531
    0x90d0f20030706031806020a05070501060e01051206150f0301060e040c0303020706020d0c06110d090b0f01080a2f0a0b0d0c0f1205060402090a0b09040c02010504031707021e01 77
    0x441c642400b00307002030320160608128503c0051041c801c20030040ea00240710550010340780815074000c4040c0d401980d4004000e21403a0380310108544040020b1007003d00030034030700e5403400e162800440c03080e2040c02403802000d58050420100315101004801780354155695400c0880c20300e1410300400e01c15800382e980603605904c0d501d002407802507554001011500600c4241584643c13100c000c200c00f0380c00440101d0b140309040000402407107101000840c403131400182008003d1081d01840c421a04604a542c541c0e0340c400760107803034036030703594009080028652100c0307480d02c24010001d4019840c0c900c002c80015501c408035100c0a80c2e03070065000082c020810f918961058090304416045a1a04c01d48c07a003907124014010300d000c004041382031522040003400707039201da030b06039141c11100421100c03200380e590702404001d131301c90a88a409581400c600e000c005005004845c015585075554030002201c008424030300040280023041140600d8940844c02c2c3e0b040c010460702211200d000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 139100026 1250 139098776 139098833
    0xc2202070602070b0105010305160c051009110306061918140405060108061b0307110a150e120c0304030b0c0d09210f02060c0903010b030f010605090a11090d0f 70
    0x11341030b030f101c144c0c403250405051100308208804407000c0e503c61070746941007100d05c400303d41c90000d00340a0700c01030101b0700c0ca00e0b08031078109020440c10401280c0005038295042e5485040502240032641c0f4621001e14249400400001c40c0c13142d8002c0c185a507064001070003030700544952820103070946050382d80703030300036001070000c00f4080c0034944c2c01102d5007041c2480d40ea20500d01044a02005240209001110800c2c554404061050110903580030601307503110441411120300a200034286404540b20380c44180c0011064601181c1003112490300071401d00e072070f507a191010418000c00e81182c51006002280e44050340d8080c804000d485402005210400d42490408510303c1d1215142045152230221403900e801140d11030300650480340aa540751503010110f80074200b680c480342e80512070200c0a415a440c1035024a042e02c10446003c0d000717484183c0400103641901451002d005010482c120142c0381400040c142c0d14824a2000f403d00420744601c1c001121002c1c000200002034240d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 139101276 1250 139100026 139100033
    0x902030f09070614030a0905070e07020f010509121e0c070302041103060a091a030703150510060e04090c12050a120302070506130203070314030c0d0f020c220207060207 74
    0x5841d51080600d0001c080c1c0d5403902c100100504c2582002d1000d0810000202d80e0a10b4207070003980f11247c00001b00c41440703542e04038080180c6801c075900001401030a1081445a0041c01a1030055140310010030b0310309004140f40d251a4044800545030041d1840c0984940c40030401902c600100c0d9405080c0c0c4510b18014030099640036003413000211410800c00440e60703141d40240b010b4400c65800010382d00300f000a8004861051080700f90b041c46280000020072142000b0b103103c4104409003030015844e002040501510745004030740c04100c0c3c2101311126414071380d1148582c3e41c05409400d840580c1c840314000c0b448a140300035a215001a21b18038240700340f8940d0501d405030070b45011440c0007101e07101c003a01c0c0c0b14080e107000d24100811241109640c0e08014410165404c0804689104020a4074540e60340c00f40700780110741e00491003a8002c0ca40070707100384194400b40d80c004c0d02d60301724a0000c21550107072030202c01c3c1a0a401342c0c40b54902c0da000c0c0c03014101c4540f25450040c2d90b00764905 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 139102526 1250 139101276 139101301
    0xe181002130b03041a04050304050d060603020a0f0e0103140a0606030602070b150a050103020705120c0a0302240703020901120c03090b09070605040b0304030207030204140115032c07050a090203 85
    0x10003289420b4020400d1000103008003079400290b01021180040380e885a10b090740c118810359018540c89284404814184442ca5002c8001c691003142e82c10f10080c1d580c00c0300104917025100b0b4008138011880100b0118280c01d1400b540281d000c4103070f4031400742c59968502101da0540054070310f00e40c007140c6401044000309800c2e4100324510f0100c448203440b03100241c40c0400074011541010707004203031201004000c20801150b50700d811701540d101ca40314500341c1d1f074503a0001c0e8258010300c20b8032844402165043c0c24040000d030312101070f0760f040d9910b8406401a50001e030b1018108815104000840d000d14415800030030000c1d5030102d0088994101810800300207440c4000b607402500742004415084012281180c402910481d100e9486060aa0910026a1000c0d40242c10506d0f05260b1014040c5450b041c0d1382d0b400b03201140380b4100f801c101c085496045c000c1e960340a403402e001700514811031000070081d20003811030b21141d8442e0086030300320199502034005d254002c000e00c070400700d452 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 139103776 1250 139102526 139102529
    0x10e15090c0a140f01030b060c011b031401090903050903010f020c01061d010e10030c060206041a0f0402060310090f0b0a0b0c030f0702060d1a010f020f06010e18100213 74
    0x496800c4281030914001d80c0541d0f0003050410310a026000c11041940d000c0d0b08130001c5030000400d00c0e61500e20302c9410364040c00007889214031199a10345031600d018060b00c261070b40c03d66115894420360b070810168800a080c2d6110540a120040c000100c0d9950309002d00c00d010f0200c48800360b143c04c0700640e1242034440d83c0d00b11480e202c18002e2540c824a09425803141120b103503901c002115100d02070f0340d40c2d003c411500041c2800b8004100462000e03000150300d40101c1c401c10001c1c035100d55002c0000c01d1207900796480554505410082009440c1040181d0380054401c03140070303510769039045610b0850780c0b010101003c540c3c550401402d64913208140c1402000c410898a14088114003015142c0c42583c811038a4640081280015511080c09444800b601d0b4a010400210a45400354580500070402030014100810f0411702500c08201c01190802d004010f11083c0d00304007031107203c0c04000f401800254091407440003072100c104140c401d461240a0700580d01c2494100c00c0c46074000740d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 139105026 1250 139103776 139103779
    0x503060c0f031b1c060602120702100e01110307060912090315050a06150e150903030d0504050307120507120305010e06190302092706090606010c05010e15090c 70
    0x14000034801d480400102ea60000040d0b4001c2210a90003502c41101d00071074102c0d08500000b4004490210070380c0d804001514101e800f05c40b02c6451a05e1a000a480741010007074000c441010704080300d90042c20001c5280605042090003204016041451900004800c0c1c0e0b540da2039403501c205110b1000350004101000d413070844002c1e803e503124002d142030400700141000b5a030b0400220f599000da4441c9001c2c1c141d03074040b500341400003000240300b4001c1c5500d40f48960140b0350a20800c05050084034000d00703010f00614184088105110010315000300160380764042007220b240007072070700c1311042c0180203261519500d0b0741450915401214456480d0000d1620b807a00504c020000503008aa1009045a01546030680040d03a103020a0484e80025004101c150034060101002450009200c4503090303002c5010b02440305880c3e03504015603088076142c0110002c182c2c2d80d48603d0f00f5a11080c0908004902201c0d1100700524101307402080c500001a40400e01010480601c08a450441c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 139106276 1250 139105026 139105051
    0x806060c070e0415021206010e0415050609010909060303020109150c080f040201110105070e031902090c030c12040609060e01141f091805160e0c090103091407050306 73
    0x41411225945940e0741c040c004519201d0700004042080b16031101d0190030120005546605103880103e0761440305842542c0030a0403c8006001810944501c040150500452480141c500020701145030701c1300a0b07403410002c0001d0046105452409424020752295000145010190501c0c0790101e000c8104800810f04015800590a900030040d44d0000c0000107043d205888910068522101601c556007695007864100070070642c02c03120060b034941080e001e0741d2003000c07003901c020114241c90f030f0025840200d07000418004007200e409550721481e140b081e2468408034200342107043c0f004a804850407031711118800204034003070098500211183c4001e00031443c0c40e40308011880001000174580250810b8110000c000d11118040102401403007000b501703c2e54100c05032031055108080e1024404c00702c1d00340c0e03910b040020324000c0301c50011511034581c4400f810a20346078840c03d030050406495140c044041084c000304800c0004e4428010400b203443c1406050030041e000700300e09610741 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 139107526 1250 139106276 139106287
    0x70501180b07020609120105160206100f0e1305160f0b040b030609060102010f0c0225050102100209030a1220010513020f03120703120f0204060c0818040f060501080606 74
    0x1880d01075841850f811111640c6901c002e1000c6100307034205048295056090206200b80903489480c481c480c121182e003541c85950390540b00700301c2e5900600c0351298015080d1010820380804000154201d0070f91003414848240300e45850740b808200e4015a50143c0045a041051015402c182030050002c0006a801d00d8901040c000d8140001040180981da04d00001a42d80c0e00c01e620102c455138181030700300485011010003d58800ac98400c2080305102c0e1002154034181c92a920022548141d00800490501d1081d0764041d40042c4041505031045d1115200061680d580c3d21404001c0c90f84c0d1462500381140c1194049400d2440046030341e4901802c0c80394040c10b285540b03052640503500040d001220002103440c0441c1c041d12400e034120041814402c25a02103e02d038043c0e1000b1034180106004920554201d2140b1b00c82c1d00040341c0f01120a4001618131006031411850203a00c210000c02c002d80440c083d0340c1f1400c490740c1c1199840724144401c0d80c100c00c5042d0081d0080e240300d41001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 139108776 1250 139107526 139107539
    0x8030a0f0806100e01121d010204030204181e0c26012004050d11150901020f0f211b0309040c08041106161713150f0807050405060c07050118 62
    0x911395041042c10007000700c0c1c2072041c8030030f079800c140042001045100c0c0184641802d4074000d400c03c0c0400ca210324240320302840d110000d01d405005072a00700d40d81c445c03509503003481c81051a425a0b4111001480341d500082c984081c416440c4840d46a04c200c00c101c0a50582420f003110b00151005250300c0300840e25005807550b020650702075480550300c0108101e003d0400c402c40d03400c0020341c5540036200e003182c0c48025040c000540280d0000307030210f4400840b204c0d840c035140c043c24441005d0303d07884084198580c103810035460406800742c00080b0319059850005800f5200c52100703c40c0b07540e000041c418540d0034640314004010403140b9042c00c40d41400d0303481c0d109401103580c406100b61310108400001c10901e0034881c80c2c3c3c950007a8040340c89081c107100c0240a0708200c400652230b5041410010724a2030700d410024007100d0315078580c200d0107006101540c503140042c00701420000103100c0131400d61038001c010701c00140f4032801041d049241100041c4003a202c200c419034880c51409080080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 139110026 1250 139108776 139108787
    0x10c060f200c0d03150806010305030d0b03031e070609120207170d080115020f03070614070c0b1f050d08070605060d031409040209040203010b0307022104031b08030a0f080610 77
    0x200f41520300426003041e000c00c140b00760303501c542050503030b0301407800000308104000000b0034041c4601c030014030060310070f44105901ca0003400108151003441035507a050b0380c500c0800034008c01c1d104580024145c2060341340e907100b10040c0c80020002d42e00c01b0b0b40038004845280c104c401c02012010040c442001d0900004042510610850300103d107070145040d4207900030f008001201d4460300840341c5036541414044050301002d0f07064800c882c184c0001c540403034442c2c1e0022001c00d4010000300d02548903003640f0070120b1100148245411001200032510744c0c0c440280c2c541513806141419110407450421404407a0701410803403180804032080c10000e0740240129841c0c0b140c00e02c07490b1300c3d000b000011a01034071410164962181c030000005c03640f240710364003541c021f40f004d50071540c0c2100b45c02e407074250609690030134000e5840300740401c000040d40b40003662120300003d0b0b08609410750b640701251645c1c000e0750052021481c0985c09040c055030120360f40354880011100842d0304d800d108806001e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 139111276 1250 139110026 139110043
    0x507140316080318030f0706060f0501050a0e04090501020d090302060a0c090e10080109081b06190b060405030a06060503150f010303080c070515091009150209010c060f200c 76
    0x300180200c0001c441e5a1200502c09011800c0c805403613651035410040841d40c7d01c054000c644d0907190040c0070a80c0590741e20b4490960b181030b11500d01d4480480e03000d4a504500520300c0d50f2141e10380e050500010000c2c00501041140b085020440100302d00e40a401c8c480c00070000400c20303207441c030034104003580071480e50b00f281d05540204102d82c4980c942e2108030301c0725800559666080c81c0848080010340c1c3c0040074200c0d142116554080c074180315107a150101529001c4154261050b40311011a00c3e0344040c802071401844c19103040da5550101b4242078075040c051303800c0c80d074644040206085c28408001c80364003200d904003040c071b804101c24036143d4042c08042d00300700540000032858960071048031002e9070070000f1a00c28544042c0201c0080f40b00319000e01107801248140100c0002c40e00a05203032646c4544003420445490308114003d4111040c181e04006088410001040c82c0c0d00c02c0b14502d0039100000b068043e0038038603100900c00c00019100303128004101102054002140444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 139112526 1250 139111276 139111283
    0x712080601230927011202090721020d0204080115030204050612030708070303060302090901050712020406091202030a0c0b031e040f060b060c0d0908100c020706030513060204060507140316 83
    0xc14a03d0000020130700345400c0c41c5070381c0d08050750341c00100300750030040e141d007244034801c1340c50800966522400b12002d00300140540071052600480c1c0c04901250b4001d46100d141310880181884e6603040706d41d003502c119040f54041d1402c641000d00c15403c10380660399101e20f00340c8400005200030b2041950700c0c0700d81000a485800301041c0c90b010035100c0d80085005540040c481c120f2400c1c070002e00d0b402408180c6140b804103e80c80d2801d40f0449140c02a40d0895a1a442c0c00034000d00d0016406c1482c50503600c200c0e454014080044002614003044101605554111300d407603140ca0000045030a6000c52040c40d5041180100000181c15084010143e075109201090180c0b07410b01043e80f600074030380007030072a0041056040394998409008021101554201c1e941b0400c5103030f0b54011a00301900400050b00508000d00965000f904000d80041180c208460101d02070b440301412030b0001e400c0f0500181000514105101243e0356049a0701040000b441c40c181d14041c0550720590040e5004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 139113776 1250 139112526 139112539
    0x3011d0d05180a03110103061715090309040213030c080307020a05040c02210a080c0a050f1606020d020705160b0a2105040c1805090316020607120806012309 69
    0x140c1c000309406030000c0b00e01001816070340b9819180c1c03404600e81c0c2007400e07003107001038500640050b030b242d40880b4441d1020b0080c0c015040e200d110b45402c44c0742900082111034144410401420280c482d84020580380468401980d000c508524001b0101c1c10f0355031019003c0d034814032069002da070326010540100ca40484001410801c850002d17420300401084515504803403480c84030480090030700901e44030741d0300e54802e07115a0b15a1014051402287d80d8080040e0301440700324291002c1c0001805048898403990201014a5440406036444808540307142500030885000300041001f00c0d00d18010b0351201d400100c1d040040c2003096015681040e0100005000c0780d200c850017440c000151207480310000e000301c2c0751a05220000306064850303845046280041200a0015449903038082c99202006e1490980d41509060121014103c00e90b817108041010340001540704100c04030954280d2a40f000b01c0c81c2c5400058480491503010761701c030240148000c04c28640b00c10448007400f8089500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 139115026 1250 139113776 139113787
    0x30309060a020d09020d03180b07080906070c031b0312030b01140a0302071407080f0312010303180905100806010807030507030b1f0303030e010f0204050108070e191403011d0d05 78
    0x1180030780700422000e034001042440304801e0540c042305146c128000348034010400b650b2507010041d03502c150340020b000e0039410301c142c400902d0201c0c010000079002c0c0b0303541c0c542940c07251613022041c003520301003103010a4420002c200304040c0c130a160360106610308081040c0003401c000079209190131003030500d07075201c0040d0203681d083c02507041e04ca5441e00980c5c030310342c03075000001025500d032414040c418440c41500c0722001080c1c0008200c039075003200004980b403603911710307501942c3d00f68041100700c0340c0c112403100200d5481c00901c50140305644441d40b001c2814a082e0600f030034840b06811441c1540c00c422410710101e1400914038088a502041c0541160b039428403204075010030604d40f030784590181000006166058000c0500c0c040d1403c001c21240128148002c200d00c2075100e800d01244100d000100158001c0e01d054a41000c00b070b20080d004113001000d20000740c1290000c030340b600c0011008010301c0c00d0900c907a54030044104980d200c800a000d00303641c0d41784d55480c50041003082c0000ea = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 139116276 1250 139115026 139115047
    0x5090a0e011b0c020406050d150509011d16350705030f0303010315150504020c120408010606180b0f21040602030a0b0307030b0a020a0e03070303051b030309060a02 72
    0x4240012400c02c0c60180e804941d1400003031203500c2110042e03100318140305010410f4030b4900c01c885000342e4803036454030940740c02ca44440040c040003449810555070f81c0c038071041008905001e00010411150241140d11a0058007205074036203600040e030600d11501801010000403241ca000701a07402548080180c0320240e903525296003500080c0d0140140d9400002e42e480000141d03040c2d80c0b00f406000601174100703085004030344100000e002e242003650410801030420b03a008001020800c0150344542400e00400d92440c1d1181e03100c3c0d11169991007080205507408110141c05d4051039841468051500080740801d00504100300d01c4078000041c2d02c0000c400800c04402004240a51640c103407034203080400c009d41080719182030b00340c18030101004a26000c1a004280c039801442403280c1d449902d12000250022103002d010b008010104000c2a40c0402124004600c41d44d14980d0f01d04010000700005018004045a01d41c0248103100c040503001c0b82d02e55000144c00d00046c1c4071800d854 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 139117526 1250 139116276 139116281
    0x5061006050f0d0605062d1c091109040b0a0c1b020f0102031902061006170406180f050a02010216061b080d020a020d090602030a02030702040e1e03030f06010905090a0e01 75
    0x180441c6d40072070009602c0f49a03014400b1104100c1040d8100040d402e2081c9405000c1c82c46244240c01d02d0903600c890000300300c00c07035078440007441e4018036001e0030407203406001c82c0c1c0020342583d040da5019400380412607400070380e009031020b8200f40e07e0844030304901040807201c403503c42d0070020f205003208585040240d100300203560b051681528002c1d01c1c2518040040e44411042d2801041700c500c011010900501034030000e0307020315000c004c52255903159181c05c80241f0655400c9400045010611000726611043cad0205a41c015806031070015100c1c400649404c03040010000390000c641c2082080c80d8104095080c10380a81403a80c0c203410b11890450f54034420360020b142e065102041c40640a940003400500e1144591100c41c0c05580f03400080e69640541100280181c2c41084240c0060410744c110160045845088814074107120b03100c0314511081c080d120790780b81e1003c000c02000100b00c070411900043c0a08001c4140c034148030100d0703410719000703000e0244180c40b0184158440403d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 139118776 1250 139117526 139117529
    0xd06020304021c08090f060a020618071502030c010606030e0d03020f0d02070b0f010608090318120114040c05090432060709090501090506030a0201140d060f0305061006050f0d06 78
    0x90740d000c02c0b001c400c4c0740400454210340441e43c010300d12000c82c00124182141241c005c00c2d2690020a0346542c3e88082884100c01c042010500d80100304c0000b4050304030300c022442c803007000d4000d582c07281c004180050840310240d00c040f04040c04e000d65005920ba0104564400700080c2c43d0240c0d90f02c0c00b4848c2ca000c2440395501401000e0f1000031480c05004400b24618040c1030441c1a40445990390300048440f0841038405409030b80080010480d00b2440701460800164050319400d5100c0a541003182110700030880b08900130300c0e5108000400c507030541d00300c024140880324085070781800d4903840044a00781030180040840310141c06429400106040c440300ea020b81100c526181c1404000e220410620460745418188000807480c900c540c000d55104103400b40080c01c42103095001143c4d200c0307100101070282d80c0f0402500a14090074001e0380c0140082020a580742461490028900038008246040900c1d03869800d10940e030f1300c50100c40030b0b0050000c4c0c01d078440d495030b4044001001c15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 139120026 1250 139118776 139118809
    0x151401050a051c0b030c010f1b0c0e01030308090f07030804261c0e0307050306060609150307080417031605030a1103010312020115080304030b040312090311060105010e0d0602030402 80
    0x70030003004403c000d20f80145116003010303419036201c84404401542e103d50254518008a41c0d810034000a990a2000091a0b80d00907030a04a10300d40e242c090310304522081e0419000641003204000810328104041d005000b2000002d02c1498070b542c0b21000386000c0c6010341120301c0240c4210000e21b1800354030101d03d604443c400d64501018070000400e4144d0101200340115071980c840c5c0840e450041148411240040c024120315a00c0d001004141c1c0d000080c2181c2c0b0a001d89100d03440f190f42040914414406605c3d818403c0c1011b0518041540c48400303400759150307003001002003030007050b54201500390050801644940b0350b904e4010180c40b0080c60580140800300c0000140b0213a5000c1c048490400e40080040c20080c459803046c5600318052142c0d150b00801040001949440546905c98040e2903d40301060585070540700303542494000ba030000380104403000c01c0783c80503c00b46004100c01d00780340740003945100c041000420080e10103455194040300007802d548803545801c5200b0300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 139121276 1250 139120026 139120057
    0x615240504270b0a051c0201020114070f02072408060307090f0f0b0312040608250206070906020606011407110603130b0a020f1207020c0a060c0303151401050a05 71
    0x404561114441d0148607480c04890f0505500d030485040c15040d450070781d43c001c1e0200110054220070710b602c10500603000c80c1199030710340c506045800c6036034016004110355502c00741841c08a0034002e242001581051900500c0070540e00340885681a010760503000c0340c20070203031650b14400020b0030b01d000f0f80e019403201800c3c4112000500d4540e480980390100c00352080044019070404d050b035821418000e100002d01c00c0006221150040019580c4031421000c3c800c8110002d000b00c0c010302101074242c00141e80010103100c0304035040128036000e0300903440103182d28038081000034000e50544d00150848800010410180200d103120000501005400309550b070902d007045443e60407a01d041641c21020746008150b0700c048034000c642c0da104500e04450300346280911038031070640015000c1410751007040140f14407134443c0410a0001e0a9070b45900000c0c1000b814081c00f61080000462000012640c00b840030746000d040600001d2420b186c800e4681001030020380301441058882100d044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 139122526 1250 139121276 139121309
    0x709030f17191101060503060f040f120f020114091c021203010806090f030f030a020c1501091b0806030304030609150e030a0906020610090e0a06050a090615240504 72
    0x501c035010081c501e036541d6262030f50b401c1d010340018200ca241340941503064201001050700e580384006603070f4101d03000700060b41001c48669100200103a4a141036004a582a41a501348580a10030480c1000c40505002034920701000e10586808100c05039103100002442070b400004e100f0401598a03107071440210f0303900d503114119240e4400088402200e03078407030703010024901e940110981e90412220302070103096031103030300c241070180d0804091240c80d807088040600e0540e03501603084e4020010811300280c0c6501d514400460001403200301001d00031103206103e000c0d100007045408407600100e0000c1c0390010307881d0001c0f080b44001c40d4154003a080080042c05208084001c03c488030752910342d42d00655aa800503a16210111900000c03020034000800030603469170000880c0d15007000030780c2e12490042ea030b04805c031002038903400d00b51582ca00104003040f031184141c201108203800089003080c901007481511542200e4607882504800ca020301200d401141560094a41d02c42d514a105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 139123776 1250 139122526 139122547
    0x105100203130e0f090304060e0105030606070b10030209091b0f04020403022e0e03030703030c020106080703080910020105060d030318020d0812010b0c0309060723070f0603050709030f17 82
    0x41091310000740c18100480072820045000040700e0071103100d504d60364100c8025070010b4603550401048103400110030800080000e8018440c1071069690381d15076001c0d10f09500500802c80c030001d0100c4042d910a4030100b04803840790303c47c10031040003101c03004620b98440000c20044d00070342c1c0c03000b900303c00034038082d410740f9175125490000010001190a000381d034010048803141e151845558041d00f0420610380820701c25080402411018000894599501d80c01940f40038915030007a1804a8080742105452900030000800c0c8131040c40280603a0400f500014a412024031004080c0b55442451600400c0c2c0074102d41621078004120800b44989810103484690103001d0961260072500004510704071070006a810401407000203600301880701042c880d007503000090681d090100e42c0800d0100088080c0358041501c03015000e010020700e40680c0b4211801250060000e05050208004105a01c00562030444e50441100103002030b650500704a001180058554807200029400010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 139125026 1250 139123776 139123799
    0x506030c060d091a071709010504020a0e0405120a0203040306060504060e0f1302060406081504090c06030e030c100605011b08090d02040e010f05090c0109150e15160308010905040b010510020313 85
    0x50111b802c0c111819031b1030348002e5007210802c543c007c0d480040003800340245550302003282d42c418403440440e28640c50300c1c038a062180d002000c80c9401a400060240308100c81401001c00801003582d050000e141020709000c0c20440042c0500c040c56141c0000074003010f034038040c40070b07034607006800300c1d6403203440703444c0209814011560210a0020a00c24540a00381841402a00c0b42c11000c1e101c0c8690038400c003100602844040e05040348014885010703e60801d10403403054142010f000a41e80303103084005041d60750384010b40070f42c00090360540d0b40480c3c0316034126840010103c1300c900100c091032000400601624440c82d03000e40c6072030400408013000d0740c81300c2d00030b1104900b00c41c11075020400440708c102c0355000b5035040003a48030702440b545004107150748410400030030006044160019515040d04002c0020030f0345461000364900785a007091015000d4001000280b225241a4840300740102041c0304103400340500d2103a40103014801d0040e50351054550004800311940c6020440c3c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 139126276 1250 139125026 139125047
    0x9050a05010914091b0f03010e0d08010f0f0504020a050f0a0905121f02130b0a050a030c0516020d060f230601050c061b09090c0c010506030c060d091a07 67
    0x38201d1402d40034240c44000e0800103841130002d0402002d0107402a07050421100301d4902c00c0e900411480380381c02c05a075080c0100044003054600418260b100000c0003006040181d01403520341110a5040c42030020f208924425901c0580d0f0260340d440c404041103903144114240140136075030114080700c0c01d50b404003108044510032148691003804640c2525190007422a282440458010f51040d03420210f4001d40920901d18003c0c0f024940c1d995502110b07944504c646c080050741c009042d444050b05881103620503403480c80c02504159038000c80c030341c044880807400380c03145a000050f0010404190003016144142c480248800700d00311030b94000c155070414003203280e903047c000000e50740e510640c160b030a201402e80c01002c280d2151030303c01c1020b0f40307684800e84981600b0030001440780c5915548a009003076221600fa95000048030440c21100090081c0e842604958004440740e60703018103990004424401c0042c1d610528680210f007000c000e4203440781d5501b20780c1000200758006143d482d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 139127526 1250 139126276 139126289
    0x611160e0a0e010209010f0c020609032416091e090623060a0c02090a11030408030a0b190902091c030207050a171b011b050f070504020c070b03040c09050a0501 70
    0x2d9080c60210b80e40c242d0151a02040c00500c59111000c2e2aa10504170700601e2030010300500d140460f1400130a0070859507404103540c007071482c0d40091341c0440c40c0b038015a2000414808124900d810b410043c0310301e51034807403000350700640034100384c0030b03040304550000400d100f03001040030300d503501500c06005241000150a203059000001c2d041e007007407000c8841e6501990343d111745500b4103500308140c1030360107440003203075650f10745817120402c0e103400045000754003401e1026268500608110181d030303080d044250098134031030844c40300d0f511201c42840984000c0100540c4914113a00840c4200c1e9080b005040d103010b4403e910014550042251000c0e43c8041d9002d8a01c16160001c4901c040502c2841e240194400c51456000c003054a490000da0201490700006518000700c0803801c03481c190006461039000741c40f050140c0c0302c00b04a03c1e4002c08003500c082d82404010f40700a40c550580d44114011000000005001c004c2d4500780300d0080c01106c8010072a0741415410302c402805c01740220b5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 139128776 1250 139127526 139127531
    0xf0219061e0302030907090c020a0501022a1b01080702010905060c0a11030319020a2f06011a07020409050a0b16020712081606110a0201020c1608070611160e0a 70
    0x1036001c510078000c80340300c0c030190030080c100140340a03800c5004000120b42c4608500400c003156001800c203000070301004240c03800e86030719811103150120320418007050807a80b50b403200d604500303120440300b00c203d2a2003007401c2c0007100f540d0300340080e80900300072003004181e809070100300018212610003a150740e181999501d00b0046002100b941c1c1da00c41643e5420300d52100300e5040900901a800800c2d0500e041d103402000c024503041d400d1b0804c0300c0c481c5241d40b030715040805940104003c1150074010318440798001400403034211029824031820380c01030f0141e600d552281061000c00c10044a001cbd030302800e14009071030f01b000440c038002034030041800180100040002da000da1b105c050340c421034000c2400f41c076001c2480402038024100c80c00c21a12a40c0351404114443c070303854050941940160005a9600811000d06041070300950b0030081d4440702d14011b02816100145080503900941840350808584e00120380c9014205e0300003c048074469600411400c0ca00c00180c0c0c021810004103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 139130026 1250 139128776 139128827
    0x8040c0906030203030403080703050d0c05120f1b031005030d110f060105181009180215040803190c020d030c1103060103030806011b0204021318090804030f021906 72
    0x21102a14007600c406945907005020034030200d92010010255944a805c10a141400b180340350829a00070003981c4000c03c2c400701d08440a007800d80c10444d0f0102d0381160b00c2c2c00754a0100c00015807640001702120ba0710b04d0100005003103c0341c14405201518004003104d03401d004000c40104503001256070b50350386008103680144d0420001a902c4e0607143c004000c000c082c8494050814540b000400c1444034440180e400508801c40e0721512518051004400d0603048030b90050010040b851000340c00c1202c0c04000c10054900b000c001e4844130b42800600810716041c03a00104c0d04240010707000b960001e442d103010340c00c05070406d0048111314440e4090016078041c1508054a60009101c06400700f2483c200194082d0f01c1035281c100c0010341105903004141494000c87c0490b0040b044108810b600100d090240c0c0f03000c0d28903241d60007448503080c4022031040d80c60001c2401944001010800007203004001c5503901c20170880201104074170701c2c0503203648000c010001000c1281d40d038401c03402c100b034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 139131276 1250 139130026 139130039
    0x40b0d02031f05010e0f0d020a03050607092102010810031e03030b010305070f21090506010812040b09090a0204120506010509130b0c09060f030c0702190e04030e0613030308040c 78
    0x40c1400316a016100c402e0b46515590038070081c200c1802c000c40c0c7c4400100d10040041e9128031560000c0c5004600601a0f4602120003501c00340c0b01b500100c1074200b0034140c801800900c14585e540640c2e083c0303004501c5459880d80000010344641009101c070700705140030007100e580390500000c60b074000e41d0240311710010b00b03005400722002070f24280c002600304501100e226008415420511401482e02c2400241d0401c08104690f0311040031140c0d0340004c0010048181b042000c83c0070b0400d8160003914042c5415510203252040420381030088264030009150320070356a041d0380c0141241011801010510310b08140c444d2802d00409208107154004a1104c41000c1843c04e10b1039400209912582c8894003900c0003a00301181c100d901c400c0801c00603440321074040245008000c550221380e1a0341040c0704100d0018104184101ea24110a800700500c81403141c1803900a81c0505048100b50140c01c0803030b4191090071444420b02002031400003c1641c00803101d80701c0c5004114000080da00c0c0e28 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 139132526 1250 139131276 139131331
    0x6060503060f04110408030a05180102030c0a11130f0507030507091a07020409060e070303080601020d08010b0a020c03060709031104051b0309070e10090525050a0302040b0d0203 78
    0xc07407460704400075800c1d40c0d52604180d40004101d100c0c1050050902d6920341d405451039111101e150001200803511907410101818a40c010b5503090001c0c42c00d21410508999440306065405428451010250398903074464415240750090f52a606000300144110128041d0000703680c5000020320300000248154800c11414003556618440c5518640200f041d1012039044004140d13805070361503140c20002805840f80b001200044800740c40f03114a9802c02801c12500140040d065402c501e440703840030b42d071001e02981540d4400800c0354407a0b0700240e0483c5800809403417107404d84211001d2054054100040c00103e901c6407100000c80c04017a024001950000d41c1c00408685581c0b030400300d0407a01c080034550000c6140100c800f041c0c1e9032855a450303000256821035098030302102c1802031030310500603264002508140010106441d0343d503942e030807501140710804c00c0b4022039400c503c18400e40445004005c1c8292032500c4423240681e5800940c070681b4821001001c03031824050041c2d0340c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 139133776 1250 139132526 139132531
    0x4140d020604110f01031e05060a0e0405100911090907090608010b03060c0313060c03050a140709030206130e0a05060109170c0405191a0102010501080a080304020d0611030c0a0306060503 82
    0x4050840d03025032500c03c0c03056003c1c1005000c0e050644440f460800710904140d1900c6400c51f071240031503d41081030038001e03400003903008203910182d45801c20012480c00039240f0101c1122510005110410307051140c0303521503a030009a44140a1010320051000014503c420344020260410034079988801442c2211429240f40360540c00210016111603502e40196a225085e40707020300c0c01d1a60395480104a0b85e0700310300b0f20080b075511000c0c0301801c1c1c00c0d0300c105402e0081e81c8200c40741501706114080c280540c5840000d1040000046030030704188426504801840c103c800020141488501d02000d444e01300c40e1140029020840002c4020480d840c810210108070040c107180880d400c140809098000d0075102d1241007841229a480718510601c1c0c020305031210b2800d1050300d600002804c0d6801a84955481d9022034000c0d004281e4041c100c81c5c03c194102c41c0c0c413407584600d00d802000341580041503880c0300f40c01300c1000b08417004040141340c60001f03550100702c400d45a010035540307800705 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 139135026 1250 139133776 139133783
    0x30f020f0703060e07051c0317041a0703021b0a33020a0207050d0302010f110301060e0103020732010e010501121b03122703020904082104140d020604 66
    0x203403000c0000c00c0b0700d03504c101042c1e00c10506607007203181c0ba0008540401000408011102d01481d61001410350189055800755a500d444001505242d1503060250a2040007541220b47c0540460103540c000e84c11111001c40c01c000300521640070305c0d41c15032a641c0c1030300213640c3e05c1026003081c04200902c541000d041300d88c00300c0ca142144004400c007002500291100400d51050700c41c0411650707610881024030078802c0e400407039110003e421410541c2d000d180740c20f14508041c030060100940202e043c5210311030030b02c2d0058440500e801d01c801100d580b20507102d0321000c8800341c203100c1541c2200c840341c2009030307100030b001e050982d0040c20f003242d80c00d100b0800741130b0312031040d00c0020304600300c5076907000007003103805640e50340341e4554030611068071407045c000c5070401c420954210720401c0845420903468007020300300c514580209903a12002000180701c1c1c40e00180301310798445203000000160000030140421807a051403d2001c0c4840900304000c1440303843c6829103254400907829101c1c5a1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 139136276 1250 139135026 139135033
    0x91704091d0d0809030c0102040e070f09030b0c07110402030901020316020601060c021002151807170d050c07030c030614060f030a12090b0d090b01080307080909060105040b1204030f020f 82
    0x1070700b00b400c5414500160840c503850100300043d4603404003d001400113080b00c0614900142058040a815001404003103400c0c0030180a0400104d00c10840302e40c1e000ca0f01915080c0c2d54a050314200c0711120001c3d401315032091000c41404241901507010350300c18500d01642c034001c942d0316001680e6a440074850310000400c1d00c0700c20801400c1c620081c5070740100600485400c040207400507000054211860002c401c1c0308440400c10b15020060380b002070a0b00304007103403445d06440c640d50f1607001c07901c105810b09c90000f688456008080101d60015074202d14002c224589034907207040a420001000c10321480f048012a0503071a0540e0383e581d441000400404070a80541d03240d0000f42c040d050301d0b10500ca800f000020f4400840c50050034000240200025254a03514200b1402441a000038480e6402400220001105201140c40e94101121001a180e032000300484e1180308a4004100c00300c00810001240060260054019442910b0b400444058924100d0703454240c0c4003800503550 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 139137526 1250 139136276 139136293
    0x90b040302040f0905010203090f1c0909020a1e020102090406050f06070201030b03010e070303090509090609031c0b060f180103020901050d0b040b0a030b18010219030c03091704091d 80
    0x19082d84100070146400c07002051041690305d415007240c00c2104d0082080d0040825680000b10070700c19400e481d40c401c0d5140000c08030044000b40b21524a00590307071055400118019114041c0b0008580551132081ca440a600c0d0404024040d4003c694424001d43c20124041142e10300300250a44c08840034089a0901d005500114080d00070907801c15055542e80c500300704903200900000300034501a80714400524a01000d00403007020040024145420a60601c289184040101ca185c050411480c540782c05505250800a04c003944005030300810000d0940e090001140c01380c0700012907403018502c6100b54500642c1680300e001c5041d40001d0742002081d2a440e00d41d8001e0121004c05040007a0004040c4c004c03403e03c1c26290015a0000311440c108282030380040700b809a03803102000250b080207070040f61440048a007410820030b040d101d089042000c0d00c80da000c1e054440d0800390000c08133035105180341aa91081c084c2176003140c101940002100003c04500202161280040c03d040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 139138776 1250 139137526 139137529
    0xb121e1e28081606060906121e170703031e0b0102010b01020a0b180a0605010617130308071d0a0b04060e03060c0f070c1203050d05090c0d0803060a030606080a050607090b040302 78
    0x8401d81c0390b049030b180ba074840c0d000c02c00d04058030444024014000d101c007540010380c00d041068040400c60000000d10019a8000040d0700c072040c0070207081902b011684603c2103203000e0340a0101620320039404104034a1404100300d65800401c030314502a002008144d0741c2c0340049880304070a03100a010304c4101008a1400e4000c548040308004414080d0f510b01406075032144181c070401ea01140000303805811f000c02c000e903100c05450f000040765441c1180d1421594019003c1c0c8002010981880200e603414103504005401d546d240704c8009180d44e001a488511410b5103410502402001492105056440e4103000444901451000b5000d90400c055207441c04410b9000c0c0c2c10032100c2098904001641c0246c200c201c0501c01e201e501d403a903c0e42d4880d190002100c10042001c0896442840081e14546595000103010b90b00000b0303c96490703803510f010500030801030340001c0507c0c2c6031403c002070b02c1402044180034184580181d82094403460000c680c912894010710031061020003041005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 139140026 1250 139138776 139138807
    0xd0f09080a05060c030a0b0a080703020109050a08060f0402060909040c09110a0207031b051c1b061704021c050f070e040c060c0302010603020402030a09060b121e1e2808 74
    0x8109640001f280b902c0340034021030040030080c0d01046550b07220750030600c03c540c1c00100d00405018180c4102c4141490810340c2980c42201900038055062020003280640d154441290f40703001c400790008000c0e041134502044480744510901c2800d62074080c0f110f0460345c800003140c0704200158010a40941075440b9120f5100310b03580003088184000000046a445102a0a54034550341419188880d03003402d101000180d802c03200220380a0041c4140b02c4183c108600d0741e0b80c140700380103202e241c0c1d580780f000c99240070b4032558a0750702d000d408a07000200040003484076420085003043c1c0e10000d07651481028126006c0d07078024110000c1d80001c2c01031034490303030b0060410390082c400400c80740d6036500424100ea200381d03501140c4603160b010440900060307005982c03e90f1410307100750b0188000c401303219458103000c03070421001d00c0c01420032a0381c0d2802041010541c00e4001d14075104031802280036544c0c0c1100f091407401200001e40681c0b10754001d480c080719004e410a180500c0e214140850480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 139141276 1250 139140026 139140031
    0xc070b1f170a0b090d0908012912010f020c0f06010302010509010809010b0a06030b04050601080408030a0f091719020a030507082a010f0b0d17070201110d0f09080a05060c03 76
    0xe144580700c2e074400030480311031940d4020107042c07018100c0101e050900804c50a0740c0d0f00308044980c1403070141c0d540d044010102600a0783c0c00407114240d50304074400600e075100c2c04009160558205001c0e880e482d0020380c01003059040710021103600c01c0090100c1c80d2901424071019010400512100140394040c4411035445085840009140b810b10000907041400300c0c1c12020000c1e544030603c6180c0c0c01c10b84515600400c090804585c1071501e81d6039801d45210003031441c0022520344030001d184011942000c2181e80d40020b52907030f01d10700444020710703a802521b03481007003800e020300c0b0b000400d00102e00e640c2001d4040c0d481e0f91510685031107048141d400082c80004184000051426403250740c1500010341c4540000030a448508070000c106a480740798800c0d101d183c0320221180040d07015141400e1303103100c4460194884825000589001e0b041c405d01140a00407142301c83d5141e03521810801d5140c42d143c0740e021072103490741d00d107990720b18108000400383c1d4010030100361180c04480240d035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 139142526 1250 139141276 139141319
    0x120f03040308132408090c090106030e0a02030a0f0209220b100e040308070306082e0213080d021c0e010c08090a030311011d03030f1504050c070b1f 65
    0x240580d580c0d01310400000001c3c042044001848085003035419030100500ea00050701d00014072141014000052040a0620a00d82415a5021200d020030414403096048a4004081d922040c50300e040c50070a065100d0000c92050380b1030000501c2000b0b41d040e40d02d0b00100f40c08403c04420304c8994841c202d01001a280c0d0030503424001c0d00094041c110340030b05104611a40d0340390f203141000107015095401903004034034142c101541e0f0500c6c417402e1011446488032910003180720304d40f42404100c028030a856400e000c02c1d21252006c10103580000d0b00124a542076400c403400c00040307022400180118000d804d0001c0c270b0110091049600c525174555589019045841c6022140310014005021941c0708401180400c410400c401400303218403008403880001052012050101c0300e0740700d120082162448482c194082190031000c55114050543e001c0e1081002d07041c24400c80c45d0b40d4101d580f04480c0440b00f08006004100b407104883e29404920311b49462a600f80300140c0484620f584018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 139143776 1250 139142526 139142557
    0x1030503121e07030911030106060e010305180601060c0b070804020105090d050c03060a09030912021f09030804061d040b090a09151401150801030b0c030901020c07080705120f03040308 81
    0x6456140c2441d0b04901441040e100062002410f1801282802a40440e14800d07407400100300403a5411103481404403000340380000d10b564842c1c59004485a50843c1069684982000842d2039030304800340d80280d074020542c0c5d003501d41c4d61303c0040f1440102150020b00040c02031020a01030705201000d0500c45208105031103010703c0e0440443e14000307003200e070311005980318401d4009068201c40110068641107207600065a010340120750103015603194642c1e90071324111003e0078503224805501c09558050a4a81c0c0ea59945800604c0c2c0b800d2004e4040e0340303038071001150740203240c41d1294040d881409414001d183e42c800d41158010108048262050918074110541d5804a84210300c10602482480c0001b5410400c0e00c0b00c40011014180d014890010014000b1030040410b495000c10349990140d6296526420180640a01d003041011403107581d40110f00c282d40400c442082d44c605036911981c40214080480e9501e004640507a0036810130001800890038420043c5505141e4031600c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 139145026 1250 139143776 139143811
    0x6090b07030e032b090305060c070c0b030901020a08090307111003020706060e1806041110090e090c0301050a0b0904020607030302090907020327031506031c03020d140103050312 78
    0x4a0f040c12200051104080c021400713080f80c0c601c814101114801162074014061811035030341c255500c1c806025030819441c046100c40400003400711000290000d18801c680340e082c84003401d4042d400000d40303c004038607604001004a2000800d4980a6401001029030003060703d041c0007000800002c48000c064080260034089441405150010052410355296074074180f40e4000031b264450902000c01d030400800e21020030b500c83c04508414800326281d071648040c0303003400e84035120b40354032203101c01e10040104500f2480208442c42a80d40a80091041d03540d07415041c81111184a21a548460342e400424050304010001d01703000b901c2801c005180c00b061382d0019501c60b03021140032005038000070f07080341034900c560342c401e1030741035a58614160840c480e0002600c400002480003021040705000138190f039802c0181da80d05481101c801d14205c1c0212000601070f40c0100801584242040304918551fa14071303078050f0403a50440095400d080c1c10b04100e8008550142c40008a40811182d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 139146276 1250 139145026 139145029
    0x180604030f030f020a12050a0c0c0b060d02091518090d050d0b1c1709060f0717130303082a03071815030509011415060403050a03020a020102070f06090b07030e 70
    0x20a1154020785810088002d4038141d1b8054a9004040c03140c2c850505a011070156000000e1540c0742c0c5c0c0c0610304500c151754845c0480c4c2511005480658041c0151081c031000b6407401070740c0c042850301a600d170301d00c80c142c000301e0740501041070703c0c262442d60241d002040d906118401400b02c9400020010410826140001e000000010240b04c24420241c0ba844204218040c0d0340c04510845d8000c1030900043c0c400160290080c900c03000c025007800201c3e50f04002c0f0111b0418aa041c44424540e1a0349030748455160b400902e010071000700751000e000c00c081e800c582030035060039550043c2c500f1b035401a4002404e00c40d08081e0074502400b50710b03e50320800d54061203007031020b0004010300046201040c08020190340028190b0481a40350056230100ca00509501b9030740001030f4030500700d1150821012900030710a6500150103402450801e208165022913080300b9a4001d83c2180d4556481e10600c5040d00403d10500020615011040000205c600007924a140c040e0604e0084803040c10b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 139147526 1250 139146276 139146281
    0x6030c0312020607020d140306061209070812070c120323030712021207030c090503010e0109061506020606010f0903060203160201060602030a0c0f050705060c060906180604030f030f 80
    0x4000711109800e4440c0780404907410000198000345510045c50070312000348010300300039200c1c01c10034090707040040040d0b144d450f20f408072a4003e41402440302245000c4400319120b009600461150340900481c400803131685600f0745400d02e4002180084d554506a03a010294442150407800c1c01203c0d1a80c0940d40d0100300820054003454021a5a80c50107078030003030983c43c6482c0c02c510b40d01d10500042c5d141890483d251075102d40a03050000f81420350560603035400070954000c0340d240d07007040411800c21006411030540d1a104003c284410040c3c24880182d41c0450301468006900c00400034013590b01c07903c00c40ca040805409c00c00d240700c6e12070b12034000740d0340100c601200d48940505003140307195091240400402d22480614100728a40b10010542aa110ba0191144908060b08824020144500c8000b890010895640c8004c0d248006489100840d6040000c1c014140002e4440004540343d880701c1c81014054a00d0350350b00d0f80c2c141d41c6500b220010804242e03540c080380041540d82e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 139148776 1250 139147526 139147529
    0x30a0905070314031e0a0c1716080d0f021c02031308030106020a030216080706050318010219090905280b040c230a08060d060b030601031406070c0503090f0406030c 72
    0xc0d004d0342d0342c2c4243e100500d0201100018592100c0b000300701300c9075a81d900c00d0750f4450f499808401c241040030074809142482c01a44810504107a01880d8002007009600051a00c4690710205010001154041508900a6100f402250360050140304102c101a5004540c041440c040198100c0020344620000ba04240c00400160b03010700102004e05170100310b49555180c0c40d00600c3d400604111a058881c03046100b0340050000200103c1c8203c90240e4921030040140002192111548000c0f5074100310000d01c7c80011079100000070900c0c420364025181309500c0071188000004a409010705000010003604901603911000c411300c1e52b5a07405104820800c0e5511711102707940071300c40107200b001d41070780c1914502400c001d070804098200c3c4a40d80e0100080300c103a0a486280e09001c00034100c600b111981c507010300c00002c0f007005800180c8a500a90764400c98050343d4908005881c01c5007806400b42050348240150100744c501103150071243c0310040d0000ca5410303901c1d50348150300c500c0b6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 139150026 1250 139148776 139148813
    0x30409090c05090a0504020307050d030203040909081309020a0219020d020a060906030f09020d080703020322090b010c020a0b09030708060a0c0e18060103091a040c0f1a030a09050703 80
    0x20390804200ca85031104243e41c2141c2145020411414560300290b5511410b00c10680115802d03412001450300a109036801442074046c213002903000c0c0d2070400003580c01426044004034003120040386000c154420b803031202000c1c0c1c004201142a07643d0f080103682c8010b004a910184025030000141c4900c004c40d001441c0c6a20751111240c1054800303025100d20110300c011442c85d00900c00c0159980c800b0001c007150300011480c1e622540c07420304a00714070405007000b2107075410601a004881400000100715002d8840400c11030020000450780e241d05641c000c3d612911040341441012941401000c40d6007001782110300d400d0791400304d14203000084984030f4065603549000281541c2142000c06004011116640040504088103081040c0038003042c0c1015640d581d810208829098100c40c03855100b01070072420f280920740504500581c0c0554000680b50010004000c10030380f49102c40e11032280c1d140d0b41542e4404841034028030440c40b06552030312460400001003410341e810980103162 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 139151276 1250 139150026 139150043
    0x6330d0b040905010f200414030a0206040806041106032404180803040c0b030408030106030f230402030d081909060609090b150d020f0d0201230c06060a06051b03040909 74
    0x10403001410858107150003030364001421485c401000c4d2411011a170035230b01442000315445401c0c0c40440d10f04000390400039049840020f0101e030400c8000b5107944150f100e409000303180341c1c0450038401c440c003050720000e900111021111000144031001c4403400d000140c0009005244880d07405c00003a1101003d84021200201340301c2441081e080d580081c04880740c0075031650030160b40722046840305204180400d40d9a203442c41c2c1e40302d801d07008692505201e168400c2d60041c00ca00400400fa42950b0481c82403084070040410280210b0030303c0d1081464016590928808a1401c03020b0414400101d84844d0341e0350021400841038820340585601a40c11591203161440e00031401400c006200b5201c4e00c55110500010ba4406109450809081d2070740606010030384016038101d07d200000720610310314018040166082000a09440140c4804903101a00ca100c01c1c40102010b42c0100000a081000811042e100b01060055503004031000c403480c050381c1d808540d0444924000840e610031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 139152526 1250 139151276 139151291
    0x6060603021c020703080403051b070b0a030e010501030b0c070302150703020a020d030506060702040b040f0f1a040905060402190807030606230a03120c06020304060506330d0b04090501 81
    0xc02c1031010348100302c400c00314585101a213010b803000700020b20050800c9400203109220140f50a13030000301e00c401e48100c4400f952a00c0560545801800422000078030308001c4401d11141401814101da4012a400300c250b00d0748403100c0e1060b844020241c0640c443c0d800744140b070030303600d0041600c20545543c0042c1c403440e07000c00090800410300f078a2400c0500b080140074065a8920880344c2680d8104c400203850044003000c5405068a4000165000e140c151a01e04a11640d080781c400692a010001541030410007000201e4002c0b02018000d9800f110000e0014280b15402e0240080c00b0500340c004107564988007031502071560400c9603540e840c0c040400c00620012000704100002e040c0c5424100e05001c081480e02d1003610001d001110f9103402154850300940900040130f40004c405d5560345054104000940300659110f4051003000c0300d40380040c02034003420704c22542c04980348466852881d1003284650410561130f034030300355103031a003a1099895101e100c506e548204008588032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 139153776 1250 139152526 139152547
    0x304170606010f020601060f1b060c11030f0405041a03070f030302010609060608071d0307060c050c040b0105070b090712140f010c020a0b190e0a0b0c07020901030609030c0606060302 80
    0x2006003809041c44031030f0619502c401d0300072400c2c0d410340380703e480d201801100300f16088681c1413401c0d5100150011002100051096541001c05058915150146607501009416507248200d06145208880074001131003649081d4202d9072600d02d908201001c4102044006400e101c0154008507414110410030810182c0a0040340010203032603800b040300500e000c00c0905061713030080c518803c00540300003040e001200040d481802c000c0103002c6030111138031600064088481e44e1410741d140e2003012416240d5242c203010364003010206a6501b0304000440da03030313004811005070804038240900d00000c591b44000c0b10030250020700038000100084403013901e150400c980444245401c2e414110680c0845070000340c2445010760040d0112002c1c0c0d0b0b0304000043c21040e80c40d15500e0242410305e200c015110018000b10035900a011903403081c1c80b0341c41030360198440e01100035001011240100b002c624150712a019060003401d204000d01040da450b031003110b00d01e17045000807985c040b50389100c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 139155026 1250 139153776 139153783
    0xb0411041212032a0c080f0c2512050708010504030519020610051908330f06060304050c04050f070e030303010308030f09070803040306021c0207020d0206090f03030417 74
    0x719090070802e401140f0b400081ca03030032040d24005013802848a859100b4400c0d1450131840350030144403500c52030041d804025642c401340c040c2003180f144062968041e0300c0b40e41401c0d00c118080790090b0016103441c14204442c0040c1c0400c1d138960250203070016102001f0f0240c540300750b100c2c1d9185a40c0301c8402d000c6032000143e08620301c04540c0014204000b031724895000000b55401240c04080346202e038030250169045a40094030140201d04100c1c034800c6181c00c060365420003c91907040400c015607480311141d181100d90302d1341d130044e03140802c04506142c3c00541c0c016001e082a0390111480c070006c0340a441c0155254490600302004001446074080100301e42400220702442c46c65240d07485114140c000038060840c1d50400c880487d0004108210540c02000040241d80d02d950f52404c04800135009400c0652140ea1400904c2003000304034403c45002c541d004021000051450f0240f00300740e0080c04046410054104903070b0003e60742040a00014900d85944000c82008007041d1800c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 139156276 1250 139155026 139155053
    0x10305091506061b011508060115210f1d0c010f0e0f0a08060712050601030204031239021c030f03050c1902150114030703060b04110412 60
    0x801d401201050842005584030160040c004480349030700c80d841c214000c142c1ca00d4031311540895610b0b10020020390502c0720b10340403c60703404405a601981e610900411003000700d4038104002091009408402c0901c01801d000c1c5001503400040c1400310802c0840460710104150b0900503014118120440703000c001c02045208280b90800e0020201c410140c102c200c4800007511944010f240740000d030b12002410030044c0041c07003c4442c030b8182820054400c594140224002c2810040050220350081c001c480c00c0301d42c482864101080c8048044510000b06150200090308880102c0d41140101d240d1080c3c4e6042003601e501e040fa01d5204116003000e492608408000d40c0c10344420129422001da401c06442604000c00d02e175442009082c00e42c0320700c801c41e212000d1052040991079500043e20717180f6041d13074080d022060740c07504010421144507240d0283d140d8006031041c400a540d5811440e82443c0252010461106210801060303422a42042c000100c1c0e6082140900100b90403005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 139157526 1250 139156276 139156291
    0x1103061504050d02060706020c01110712020703020108011511010e0c030f070b0301150306030609060605010e03160611030f07030c03120b0a060305070e0a06082a1204050f0601080309010305 83
    0x14078142c03518010521603000820040d00c105004982c0300c00303008054040300c20708040840208182440d181c0c1800d6560801a01628010381c00c0380d054201e28000504807003030301e4050b144d0600e42d07883c00746900b0504c400c00100c0002c1180c5a01110301d1440c0034000d01110441600281c40c20906040c149403400308880c2c548840740d03002070313000c0020403951021241500c1000d40c511a8415a6400503006409250320003806249018070501c20f12000b43e00c4042502c409076503101c42880d0000c2056500c02100303100e1030681a401e8410888280a0305004c41c404e03503a501070b6410010780109090554200045c10384c0805d103849419002c05910580280c0340960305142003040c00410400b003155001070303009603010316039124003260301c043c018140c115410740c1c0200b400300c1054442600400c06807040c0e800d20000074608910220380303503041010300c40c81400e040ca0b240c2400007464645001490240094900c5e010741161140540030a1000901901c0f510700115030b500048800101114801043e11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 139158776 1250 139157526 139157569
    0xc120806330f07050604080306040f05071e2007060801080f0d0503041a041101090b07200d120513090e0613081b0f0c0f15130306110306 60
    0x981d1109800760700a0078119000034035621414181e140101e1031092078000b0f07020307116940410040152110003148604000e6600307102050003040f060054450039285070700031603072803035112942d1400700d00500544a0f652422401115200201c00c03040c0541103440300d8647c1118505010b415004040980140710302802800c41d41054600350342c440a03036000600400400002050500caa110f070296800e00404290940f9424180342c0b02c00c0030b1b5010380e000c5010820301d601c00a44480a041034601481d080b00c12a2111010281070600a540403244d9941c0186990000004078070000380100c0354000c1c1d82c442c02d558026104d1071818140c1564040c12005040c1020156003840204d030702034200300b40081c1c9460104241c076021340640075500484e071101900c101d21030195040000e9000401c80c031103080c0c0e05592400801e2106240b0f2903072117076401031100c03020107556218482c02051480199a0800610394481d910f010070f46148007107200140201000703002c42032812168140080e00080401c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 139160026 1250 139158776 139158829
    0x21c0b120c0612073c0926010f02070309030c080d0f0305070c0206160b0c0c12070302100c0305041b14130b060c1e0705060d0b010c120806 61
    0x38050388204803449880c1d41c00200401c0c0c1040c010101d07200304421308160041c0c0180407a4420070003c01c1600d601d091200b440c1710420b00240a030500c441510040140c00780c0d41200940c0c5a020030fa00c200f18052559030700e516426880e001c0c1d00c041c0c80400e2003507030b904081034074600341740703a8130755864101700c0785d035008201c9007801c07030b5001170001c02038590a00f008a0984d840007420b44620b11085006900004005642040743c90107010211030103200302c88028960b19820070080c0280103a0a680d5000e03844051301d000a02d4003080a886020311920403031710003244201b83d58050700c03002542140404d03211400e00c000c01c400d1030040080180400000c106040c9814411130110702c0302c00a59002d0060107618403601d404540003501002c0010700800d82e41c2c9408050290385d000c04500728041c05181002d02040c00d0000310f48102202c1e00100f00314280183e4001c2c0000410f448419541400300c031200daa4006248081c0c80e01c2540c00948070084030389040d1090000441c1c41c00300388013900101080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 139161276 1250 139160026 139160029
    0x5070c120b0115110303060d060e0a060203101a04050f1302121006020a030806010311280201050105181603090b071706010e01082a040f03110d02060d0b04021c0b120c 73
    0x41e42d501001c210f41e03e0500c88c00c1750031701c50002d0459011564540c000d18104c08103200c641d400442c042c00003100c07181c1095648813100400c002108200180040003004104031500c5d05505089140a004000c0110074911108440490b48152216045111001301308000e600036464100000c00702800a0540d94200303035001084088020a000c0c1403540e681842d140c0400320406850000610034441c8400d0007203009103408510b480030701200190b00304400420a42050390421102d454044880303082c607240e0300005111480718486c050100356466004070003059240c4012800b0b09106d4803600c00345100e081d021402044000e04c000d0501c100e401520190740d03070004030181d02c0842e007000d00301c1182001c0c084121400c0e8480030518181c5012070080b5220303c0b41e43d400b10441e4490104080802d000800340030004000070303006540f2030740921411501c8502034102502130b00c5c8c0100010714001510f034107403804002511b00105465a9924001d0340ca00b0700400c01d4583c00200402071060844010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 139162526 1250 139161276 139161283
    0x31101140906090909100c02011a010e01080a0c02160902090306010608010f0b030c070b01030524010b04060c03111b010311091c060f09030509031006060f05070c120b011511 76
    0x2000680a02c03184000101081c0301405598005000406c05000910101500a018001403e0014040107501080c686158000d03069183c488006840d03129841d80e81007980c038001c08041c2c41c42030550223a0002880d0711740c00b000842e40a031006c1c82c80141c40322111001c0c14503003c2c0580080040c030450000501c400d505100ca103e08507500e48081950326560744942d542035008041005001800ca900080108003000c200d0000d00c3c001c6007c8640300e070003140340b42a0340280c20b10804250410800041c02514854807420000d940281012141e500540c10203e01e0441750280056030000c08a11700c074219039141c040e5420381030340190214204442c140020301103e00b40e00720740c00e82d9a0100204e0381003109a03001081420b4008404201c60a01d0b800c010300158008440180b0900400c41c0c450090802413080381d0030744080d44d6442c00f00c00101c8805070382c103512096068403407556580002408195096000c1c1c4414402d0040142551600202002a05a0206401c10701902034170507000c001000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 139163776 1250 139162526 139162537
    0x230306091209011202040e1b090109090e0f06101707031a06120106030302100b030604030e06030a0f0204090912020f0c041d0a03030504150905070e100f031101140906 73
    0x3981c0c1296201d80c0d02e00180d403000701d60b81050034080d002040014196803408402ca102e0f07020800760543d07145002000411074800e103d4182e002c200e401a0901c07100000b94805801e01036920111420181080f0705c081c07902c2411034a54407051040c40c02030040400028039607101c0300a01c0020110142903039150054520300c070b0f048021801e0f001c0c0c0020103682d41c038106d40c1c882c64402c1c4004c00203030b134607810000c1d00c23840102015465581000e0b00742c1c21505000800e94482c0ba05035844551842a80080045603840900042078041e155410ba440c490070900c020002040403582c005001582487c15034a01e5145403c00340954001c0090128a004042201c80c0840c0c8201c07070004002c3e004042000000d5819002080c0358868468a141010341503071020303000e980500352082c1d5a02000da1000f00390340240701c000700242c1211900b000040c00c05c1400640001840c5040429a40c9030b00c80805c0541080d4025158116180400091541c00010010700c8441c42e1001501e8100507a01040c203074400c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 139165026 1250 139163776 139163803
    0x405130509121c0c0201180b010302010f050301180b030f070f050f010302070804060f03090b0c070c0f050d0213020c1c08070e060a120b040507030b03010e010507171f23030609 77
    0x155075515551302c1c130030750003415110040d024540110044c0e00340b0500c2d20800340001c034041400d2650a100700c1e4080c0c82524100c8600c40c80e043d15400c06413100101503c0c00000054052013400b04000080340140b1420010b0000d5003106d05020b45000308000074080300116043c1414410840d4201150400c011207080e1801d0f07007080911110403a804070000c101110300030303019556080502c5041c1d0141d200507ca014014107200c45d401e500c1d070030700f00c1310080184501e030351103400c50b00c40b2801418144000721042c03040c000c0040c10041175aa03501e06180c250002642002e00004150030f440d03400030311080d0031a43d5483d180e11404404004100d29100d560203000502241c14608040302100360401c0f00e1040c0003070b100b400705003050503018014102001040b4400c4d402c10701e41440300c460500c2440e114248503035400c201c20008048800c802d4070043c04a02c2c070300242c41c070602461001c2592100062816240700500c459207042c0c03400301141d01c24009032180d0001d00901ca1821400910142d00484 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 139166276 1250 139165026 139165031
    0x80d120b03250905070e12010c08070e0105040e01030503070302060906090601180f110309101103010b13030c0b0316030903090b0d0e0601120c08210f0405130509121c 73
    0xe282000404031202e0b90000000504040c200000240d01c0168400c60f00c5d000d64500c0344c101e040c1d40946003030f940000307400c2000450190000c0c407002c0c0302d80702242d0f2194040c1000b5161589900c3c149900c90b509800913100fa5200040c5482050350412480703600045540c05130586080411360b4035140d10701842050014465820440c1d454210350b840f41040b94000c070010882d0940d50b101c118190303001150814414021100102101c00d05030041d15440c02c03c0400c1185541c0c02d00026182d982c01007000030301002ca000d000800050710440440f0b0290030342c4901c0640b82d140401c0c0f81c250950102ca1503400701410038400400003034010442d0000d03109842d94040e01e52040006c81e100401e1400b0303141400d031150400024140021070b500c071124a004034041c0c80a20385501515564060810a00450b180060b0302140740f40360f400c01400000505140f82ca1034681d40380d00059145d901c062249078210780c2c0e4400d003c6000d100300202d0814111130ba451500742428041c0b091131440b04c102500018ac1e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 139167526 1250 139166276 139166323
    0xf080a0803060411270d0b0f15030d030212060d05100b0616081e0307120e0a1a06040f05070c0f050f0f240118180c080d120b03 56
    0x9480350040b0800801d40314082d51a42405954100e041c148203000752408041074041800a003000c0c0b90046c06e081d000304051007161207003583c00d0542000104051011580400109220b550500003060050745c60f81c3e0141c2c46040c44840840740304400b0306454822210300b4080c0c000540041007410484200010004143d440100821594410400d60710150118100e0000c100030072003010308414040c0b8038950742220340000320720728144030554820b004940c6034041c0e02c51549a075001071070040d01c42015500c900d452a81c0d81145c0c0d00c8603889683c0800c0300c40040080b50301782071203000b0307210500050501844c00c10a2000e8a05400c0807000750008810500500600000f00040c983c2d00500e441141d8130050840300c040e859000c0c0da12403040d160203541c94200a03400031f0040b181641d0007030386240300248488162070000c141080e404411040d95510680c049030300d000201005280d0324000c1c0c80402030310300e00105000042c80c0105d0206141c0f100504482d100000c3c81101c0082c03829201805d070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 139168776 1250 139167526 139167529
    0x90102160809040e010c021e0304030b0610030e011802010e0307050609011404082e06050307050d03020f0616030606021506040b030a080c0703120833040204080114010f080a080306 79
    0x109084c2c40151400e40c200790310320708000d90001d051840c10416071111000b4900042d6480d46901c294031025040903241000b003001842c1040800900001038100040c0315400b030111503007540c021181c0740c0f032200703003209100c0c00350f58001d1800c0c0381114044001d4100700d030512001030400d000e40c03c06903040008121161746c41240820488020780f003400700b20b4400088010410b44c4140d5000116180050310740028103102c0d640c4c0c044d19040d68002800750000314144014000200003480c0b05030210b2103075880d40c0c0e0b0380301030600c11140540c005042003441c1c80c07113400024050f41c01c654407000456100e03000070741c00c881c030f60001715400c01800c40340810041c203d0800246060714500002d00f0b03840b00000c802a51100016003501106d2040b4010a040c1070319510075101b40700c045601000b034018030741011204202c5078840111040c903a1181034240c40311070b40490100d80023a00b1919071a99139100e008400b00000340b1b120b00402104441481d55420040080d45800d8142d41c0107085000202c04a004d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 139170026 1250 139168776 139168781
    0x201050708011a0c070b0702012a060f0b18090d02030901080406020a1412160e010c0f0204060f1d06060408070b0d060e040b061305270a06022109010216080904 70
    0x41c0c1101011101c002e901d030050443c0c6c030340c4412030803808101d01000e240036545501c1208080012100c010100c49030041c0c40c0d8101404032060442502903490f00119066560104030034007003072586021882500d400d06a66181c4020b82d03070050191361003405090944da03800144564026400a000741e20384081503030944400c9410201648241c0000c61600d1085840d1105503200702c1904c0c24600f4416002541030340e120305650350040c00a44039103840b4011910b07442d100d00000cbd10140000038550755444074984030810319088600c400341a620403480751104128000e8001c207048039042d21f441d152103100d0369111054800c88040340e03004220620001d801e58894001022104c2001d00745203410324064420b00001c45149200d100f1410000c07210017198071810348280082104941011892055822445000c45102c403043c8207903074074000000c080f8001782020b40c900050340651019980c003124a9084000d180c80c100342c1c07048c0402036050882828040c88242c0144515540d0b400ca000807a02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 139171276 1250 139170026 139170037
    0xc01020706180c05240304021207080c010306051005030115020106080d03060e0708041112010f1112010b0702150912070308092704030e01051908010e06010201050708011a 75
    0x60107140c105035410251074400e90340718843c0300d03a10403a509603c0b1010403a1301c0e054020003002040310300180c4117410728044011908107000400c20414030018914080c5000310a0700540d510360490702d2051354a5815014000241c44100c035079940140716150300911500052089006128901d95884081c40c000e52240300905068401d40c1d503880d10040000e4060001840f501180c10540f200280c101341c820441d0600540c1e00c040c2c0d00346800a403030b042041100344076030144800d560300c2d01c55a005014910824621000c85c0000c643c40d080c070098080c010580c160711000310b00e182001580e00507a16041188180c803444110192940884c0340800c160354640011051144104c0c4404000d010341503010b400505001c07200004065408104058400e0100041c810204020700c04180024018444881030403011724140c1d0409500c44170b44070094091500b00b10101c6c0c2110018030101c0105503105d540301d0003e00087c01942480140200b2904051090301d00c6400b0b00d50007140d00000d079004848 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 139172526 1250 139171276 139171283
    0xe2a1818060103031707020c030606100302040b0d150515030718050907020703050d0311090f030a02090408071118070c030e06120a0e010b180a060b0313030f03061401050c010207 78
    0xe01d1581c40b480e01400c0c00d100e0003641c22040c0040030024448510024500f40802d9002d00a84007a860324810302c2040b10040601105041e000d0101181402040000e0111603c5e408004a81c1c2030175441d8050110346660401c6002d02d00c10160398028101d110100c03a0828800c1c50f103071841030b0785045092070380c2040e0381000b40e01c840081c050022540d40000c00b84203481c000d505850a038500440160226098609618541c02c002c2c040c0054901e092038a841c030460b80a4150740b4060595400034044050841c0c0840b0303114400310303846050003180008511142010342d5647c2c039085644020081402c0f000340340004100c0440003405c00c1510078555090820b501034003560b1500046070f000d10151004444d4081510700c0d06a00203410101401032a4082c031014100421030400560790310721801004207010489501c441c0c0000d0325155810095119020444036240c11388003a10b802040130304414181c1007094240076083c8225192035030401c0040c08242081569000d404075a10b003e4040c801018 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 139173776 1250 139172526 139172533
    0x501060909030807022a0103110c0601180f0506090103150906020309010e1c050f0a0207080a060b01080f060a062105010e22170903030c010e2a1818 65
    0x30070950000303e07290150490790280c5003000580105401405030032030110082800400111800354041d51040c003012003010145868000e00d864503d103802000c1e480f0f142098140082c0180401903442080c2a21048040c14092400c250001600c1c6000602002e07100d035180201103944852035a10032920254440300945d124a4000d8081c0d0080156088004060040704445162003000d2080000d40c0455520381500382040403260000c00d410004104095115400011448900030014503500c184500f00c045140403101000400c503c0c000350158941401d07440a0000c560303101c0600340e0075201c2500d0a030101400c106e5040c21500349944c039002445280800114507005460f4501c1d2140210304040f8006a2941a1801d40500444c6014000520642c92018001d02d48001058407000007002c480c1003900e0322000e542180d0305090700b540c440e8841a0400150400703101400c4080e541c02100d141345100000215507a4200070403211b10040c3c080d0000360404042058000d070b40c80204085 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 139175026 1250 139173776 139173791
    0x20c010f0b030f030c100203071103030916050103230903160b04060b220c0e040f0b030607030903140702011403010306020c060c04050d0b0402060f160218010303050a0c05010609 78
    0x40001440001086402802941844141003100104681403003841c00006c20312011010b40c010000d40000e07148104100c4c5054040410301c004002a50194040d503002d0810b44500c3c0c4842c40030300d40a584003038107050404601e0b004480700d58040d00d80d0010340604042c0595900703003126085102d6000100d078900c20789000f403402c0c4140342c90001c3c4250b104140070003400c00d0796810081303405c44a0165041c1c02420040b41a044069030300070781c1c1c882ca22418811488195070000a054a04904003207540700c3d41c55000888500c0e080080300e80112290500300942485524010281006c5124004a010b0002610021079219040706114400004000c5460b56101c0c44d203400603510240c640a040c1c03140401103440d43c0e0707240088a00702c2d140204038a696441642d6080043c04000344166403200c01800710741010303103520780180301600320b8a1510000d2403881c81000600190070058100c00d4072254010300020750442c084482c044203034202020b40d0311243c40e0041c0941019009042d0140c10311f0b42 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 139176276 1250 139175026 139175051
    0x319030e070f15020303061e040b06030c0904060f0501170c0403020d08031005090f1602011409070830030a0e0a0c0501030e010506012c040617070806090c010f0201020c01 75
    0x20520640b0302c03d244810101c41401012a5030740030a8482079440840f04020380101700c0072040d00054100c01030808150031444800044c480c2d041165490045c0c0400a01c00407a031800e40f003504081e18540410703051260610340000c15598014034101c02c4883d804012505041006081d28000d41e40205a42903a071610b20f014140d9400a035a018602d000412000c00c4520700fa860341032142c0c0786203001000300e90b00c03814020030b030100078446501955664407041003a0401b45403030030b01c180f03141401000b1107481d1850051420042013003e8001203c8502e0300840c85091551010b42074141c5202c1545948441c04084002c05891010980760310038051800f0802103814403440c00c603002601c00f0803203044c090402509a441c100e4010b400500c1c0780c2c0c85d100e8504600520784c02102078416540840c0104280407400b1602a07803c80c00242c0c446603e190700070b40040061502030803040024100b58149003021684d280d601c030459606000300443d00c2c0c03d030980700b5410395002c41d286e500203004a002490 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 139177526 1250 139176276 139176299
    0x6110703020f0f070302010c0201030f1503060b030d0201110306040c021f14061009030206210a050103050606010914061605010213030309120b0f06060708070302010b0a06030603050319030e07 84
    0xc2031102c2501480c0e00c06100240049140c900b200e8041c1c450303820080c5154011002011003910900815584814402c61451048840c00185100704030006101204030101898103003004800011603041200d1800c1020002c000e40c1e80000d02520045102071010b001642001202078514412001c0d8030720a1440d20080c3c1c00050701640d00981552060f120101400741d2860300c1d00c410300114036241010001420000020080590082190380a0b50003200d450303000890141e502c0c45000f6112401441400020301985811850908042c0710492420304510600e5522403c910300c0354001160301d00c1c0101d0003810b000c0e02d480d4044000c5689441c03d503140c1e540010b583c08150001170844001007103403c80d9024040c00190402c0a1842c2599200b040d0314607604001d041980000060142c00001102900a0048139105e6000462403000c00401c1c0410907080e0340c491801c06040481c00c102040000c001c030354080c013032807001c2800b2031118001039001d00301030070b816522845a40c10010b02e100801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 139178776 1250 139177526 139177543
    0x1060302180103030e06030115080702010f090503041a03010e01090b0102160914010b04061202090d050a0b04060509031c05040c2115110406050d1e090203060f0708130611070302 78
    0x5d80340c00284100650a1100078042409101140044c5000c6014028001c0042580c080710920004c80d80d18258901d401c1524221901200d0550001c2028001d03000750160b881001c4080000c520700b90340c94030190b64501c143c10320900800594880e03039810203900c24818604094500003610004c5590396180200510340c204180c1040e001c00d1001154455440d02100c0440340d180c0d481c85080900080b441c0001d501442c032169200c180e0b0110303480021014011041d0680c05074500390554505030401c8029a00002d00c01c6074203030410030030600c90700c0034502e00040440007000009019901d61405080c03604158004016a1210034445a10311414031000c488031442550b1000c0005042c408040544520f10195850b48800340401d001d11440740340501514030b90502c005c600455004420904c01c0032184d45607030010b03282c6c0c0d82081982130420a803500108010301080ca240340200d8028145c900203402d40c55200c4c45490f650050080582080810b13440c0080800d954035801e1801940d00e1900c0e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 139180026 1250 139178776 139178783
    0x602041212030504051c0c02040608010e16080a110415091a09040c0b0f0f030708041e0b06130603050f0a1a1b0d0e1006051e1e0301060302180103 64
    0x2800604018a80b00740910760103240c0c40030007801d010400d101c6200803480107059000401070032a4036a40542e40e240601401400480000160840300c41e5519051072102c200400301d55005400410035240001681d208640d003014001e140502103400140107010340c00c070340100d803c00302c07100030408444590203d20504d89034204221013116500a0203e003801c105d5026043c1e0101d40010400d02e0441c10041c800c0d07544000f4038615000003220741440c0e40e041a214000001e60b10010401040021907000d1400b00949180d040803082c41e98415500d1140286102d009042c2c03001520340e51222a04524091179010091b0f83d0065038020000351b80c0c8a1000080d503801c603548120440e0b0441e09680140680c0c640034940441009103581d00e40700354402c281044910b0798500b0904d010b10810301c40002d80c49a8400c0c0425038901d0103041080c000c0803002c144154080f2281b00e42c1007513441403080d2420703801100c000325019042400003801086650b2003e50810f0780c2000419001d6003000750b15040c1d912 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 139181276 1250 139180026 139180043
    0x60a0521010501050a030b0a0f0b120a02270a0c0201061d040209010504020406050a0e030c0a0821031512030706060e0f0106050405010509190f06090807090509030412050a06020412 79
    0xc4e14002c103c405243d41c4400b41200c0030700c03800b083d10005141c001c1d4120701038020000c00c2d08100c410214040494502c6442c0c895048001c00f981140342c0246011500308500302c1407040790f025040c0a48071840701800441540360388030503000c55035000307402440080100e400422a01841848070141c141d0040754101d00c01c84c0500004202032410380b0a8800f80c89466803514140b4800743e130181d505101c0403540039070512410042400603614861003a02070080d1201038440d280c0c4001c05000b07010012610706079505010300802c003800d2066030704500311000c1207882ca42584085c104440c1944180c0d400a41a5810b06401040f015a28101d80c1d001d40398240706140e240c0e0b078407642280d03070340520700070710340041d00401c440201440c040942c031030300ca90300841c5071000540d2041009040c1c510380e84100c0100d40741300c0301040340744c005001e007500403d0810001e1100d490070501d00c2d030b100c0c81345001308045a9000000350090040c200800c0007440d0707120200319920703912048885201006010102c89510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 139182526 1250 139181276 139181279
    0x303010f05120a0b190b031606031415010c0f050114060114030405030f0f0c0d11210a0f020715031a0402160b0a0f020715050c0f070b060a0521010501 66
    0xb00001440c00569402c6102038116880c0c4208109020380c5c0c0f44080c40348603031961ba1b0701e00b40740c4d41440501c3e400412100340c51801480c01c040079003921034040c80348441a1101040000b160030000104440a03030900c1d120560341c4507490005603c10111001408640c83e00c5c9884010880441a15006032001d884101e40d6010752120b1407128401181d004005400500628000b80c002c50017802d400c1d1031417082c0c0d9041c0804460042d2038000d22510200c0041d00f5003070030146403001403083d52444494002a0003120070100031545480c031803c12014204402000b0b04460349209008600181070b0459100c50891030181c0000c020b080410881e10500f03000011844c018a0a44202d50501d481801c808101d1034160f11400180c400041c01049550744481790747d424003003a44000c1680504c12002d09411030740c011400405c4032801030107000030000411148820704070304030549040c0e92b8450680c16103a80d03a800861a0440194130540c1c03c00c01c800c2e00a40d0380c040d2010800c00c0c6c01003030b1000300800d0303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 139183776 1250 139182526 139182559
    0x180a0903020f0a0c05010807030608030a030b040b0409030e10030e0d0806040c030203061c060e01140a0e03070302060a153b1501030203090a080c070e0708040206030708070c050303010f05 82
    0x402c1d031180004c00e4010880c82c10070165000ba03c100350701c50154140028450b5490029505540c41076480c00002a60f6400e48551032416202c0da1556050075501004040b502d50b402800384040c140c940e501c030700a0031010108841c480e802c03070b80d0340e5081c00040d6840d0103205036000d8014281030740d20034419400c10000840d0300b8800c3c400d492099000601605000c0c90b0392003078138940c641d110400d40b502138640c20003c0403501d00340140a0040904007a990b558a006010380b000c4030420700c040701035600300b0030061300440d07400944640c014821010014290310b0102100814180660102c070351000740b00038050440265050006941304180d0654140401003217004102082c11516203e0105500180e801654441c2e40516808081002150145841a1a42203140d00300180e4580258041c140a2000740c120426441d00403120381004580760409a00048640c04000c2c91082007080742400111000c1c0329081e4010702a40240a0300e0b5a035850b0510740700c0d9000c060007250300030781c0e030400c140840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 139185026 1250 139183776 139183783
    0x1b0f0e0109030305071a09030a090e090a142803020f0604080406030c0e0607061e0204060e06210702030d0c05040f0303080c07060c030516170402040b180a0903020f 72
    0x810016580c100c04a030031550b06640b01e03040030704282e4246105400c64800407405e104114007078402c0f10002d645614521100612610341d540003912342ca0300044c2400350784000080d14a100c56400301c0303410101500c00e1808c3d407502d900301d030343c4140b41e0147c0c50440d07000b0204045808140e41c0680c1c00e49510052040131aa0b44100a5400031300d801380c204010840c46100c0d0744003001c082003d05d0106480c480000000d16550400700098900503a10007044550107601d02244031404004001942013a1808001034880729985080c1802424001181005d01e03081806149240361170149103041c0381440b084c001d50340d07040071402c90012450100400c241a0245041d1011910900c0340b8001c100d007950350807181d80401410014402ca801c1c4415400031b400350140031a480c0c240ea4000400e441c0c003107141626081c01080340b0040c0600f00c1c1081d0702c9481212051540160140e401007049240705001c00c0d244500f249285511000350070030310150140c242c1040d1500d43c040d03030032100184d40040020f0345 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 139186276 1250 139185026 139185047
    0x10908010e0607030209011803210f0903030c021f1706040605030a060e0c06120a0b01050c0307020f06040504090606090e01020f160c03080d050f090c03030d0f0902041b0f 75
    0x10b900142c00039030300c0f038842e800800d07040c081850034625000a1001503c1c0714038040d0000c84500c01d42d0b0b800c02400046800d03019580d02081c2c80d002d0740a0743c00007005442c0c1081d41c00007904110150200303031709540b01c0044240001481c111030740940348003114018150780b8407400046410261030040740c0c10786054010501940c400402509421072140d803070304028035038240700c40381601801020400315075840c0c010703000020702024540c040d454141d403036200301d078030010107581031260a101c4183c98034000410b94818650503641c40c4181c59003100010381c5409580c0c031040d841030130012503008004050b04104102c55080308103101092220440900386c0c06a50390141102d9130500a84159801e0807140d0240c880c01070103654a00c0b070b02c94030313100d905034424030410003459103407010f2040c0192925400c0b43e200c0325201c007402020001e0740000c0e444e8450447c3c100081611841382001100665110001130350b0300400400840030350b081d042a4070703040d15041401041d0b10a008000184c01070b110400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 139187526 1250 139186276 139186301
    0x80408060a0b030d0504061101060f230a0f06030906061703070c0506030f0f07090302030307030503070216060207060e030c13090302060718121a0711070501090f170f01060b0901090801 81
    0x90616080c010211401e581900c01c0303003234641d291580003981100d10106000070b0400040e950720710003c806070a03101820801d0350113001c0d03140c14800300000d011046001d800d84d002da280201d403142c003e04048010700183c0d00108440c2034104441e8040c03060000082c1030851003051251036003543c810030401240011030380c002c01400c003040004c104004030001a5802080382c24440c1c800d5450303401092071034008110480c0461070002c10f01080c3c0b90100070011400e400380030841c15050904100940340d811500c04e01c2e041c0407100c441542c607554240f2600403280b41c0502600c1241c911515000c01074002d4101c15405401208007050141e44265001c50504240d9400218090f250241c8030203c540502c1381900e0700130554990031001c0c0e030005802800f80d1059511900d40c1c4180c10181d909043e01d55000c00e06100d8065410409103081070045e800311510201c14000011540c2500c03802c019401181d41d00079443c1407808580c1051980141074503400c2030341c070305030080d03281c1240d182254400f00c44031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 139188776 1250 139187526 139187537
    0x3060103020d050a0803040c050f060307020c010f0318060c0e09010317031506070605010906140a090c05070c090e1c021c0e0d0f060c0201021e07060207080408060a0b030d 75
    0x188098180541074600c0705100f042154030450580d101d003242900142c0d000c44083c42c000000300424030340301810a190741c60132901d0910303504200d02e01a40c1da060020086052046500c1400b081c49e000340d12070403110200c00781031910380c0d42902c0e20000808240241c4800b0510010b41e131401424411801410303294801c9020913201c0034455000d0454000074805012103070b081340e00748065203e04020b05280c0b44911070201da1941010100c8080d03c0c3c2c1034000451058a140701d03c100781d96214041c100311451001c00156100340560100c030313284190000649200307002e140c00100c0030341990120012203c42426594101c1188120b1580000603400401c01a80404405100c030840040800c007a034125050002c900d200c10030104013446540f88064400d68810404201442040d0207081d005023007a20003145002d010600090700341c00031140300c0d140c4c030802003140d10070010541c0c11243c40c0d0f030b044580c498a42e85c2d2a10500c0d40d4100071900c5070556414040350003541d043c00100c00400d4401d503244c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 139190026 1250 139188776 139188779
    0x8241f0e130917070c0f08100e0d0c060b060f03090304030c1202061801030f0609090302070902070206250f0b090c0109030503090f0a090504081308070b030f0405030c15060a0b0306030601 82
    0x3d2a08980110702c06840d8070555800026690242a0101c0002d0000303002a2001c803d182500c0300803210f064024801c190401103641107030070351002d25181c009900080c0010289140f401091050040036a10101e40030000140050400c00001400c21203200c1c842c2c0f034440c292a1030941032042d0031800002e401a400b8010b07400c00048202d8403030707503030070041c58002081c02c0f150000c0b609a0708180d020b0b4100b00c5d0b41c1c808202c14980d041c02460054034082c4804d40c9010065404200c140c400c04c40074640c0341c6010341003c4081105850340c80700d6290030440d0b050b401c842c0c1d0708103114903000981d99820644901071030500154010b1300620201c940000c091420040704030240202c20300c510120703607840141c0d030744040b03010603c41c03051a0046010b1108107407201140342c100111000181c01146c506e1348040d0040101c00c113030404036644a00303201044c1007903861b6403a0035403550113a0172801040d40500340981c400b821803521400d00c43c08044400814441e40c0d4664151107210a60345a030701500b01400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 139191276 1250 139190026 139190063
    0x120109021302090f090a0c02070501020c0312090117090321090c01030506030708030d0f0b0117010b0a120207030e09070509091609170c030c0108241f0e1309 69
    0x30749480d420181440030150303e40400105d1340c0d002121801d00355581c40b010a641d0581c10449003014140a00041080081000c0041d603190b218411441020381c1c000780e101c0d10341e403045003600918581d84110281c02e007009507107107440750044001d65801446010340e07c3d500c160901d549030300841d1100c02038803103c1c100714011000f0740402080340b501403244050000c7c0c4c0c1c1c4070810043c410344080754000250840c4122620040d0342d13601c018603040052800c15002c0880800388003604440c0c0c10203540e655803154000a44020b990280b141e05250310101d040d0081c0764000460341d415030710403105580d4a9a584405651a00800346141c4e01700c031b4510b0005910148030303501054000c06905089240940d00c1000340914480018654280d802070107a900243c2002c00101c1e40b002c1c000d0802c048207280000c1d440072500e5034a98408101d0380c4041200708541c94a94001512001d4444a90b000c54100c0802500c990114105207001c2c2d01184030140e0141c241d4031030603801c0c60380429444114100c452 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 139192526 1250 139191276 139191281
    0x512040f021507050606040c020d05040603020c0c180a0b040204120b0a0b04061d07260402010e091e0c041401050c01020d0c0c12020607050901030e0c0405151201090213 74
    0x9408980260070241103425400b26100a01020f52007600140f10030b02d0300c0000c2c442a2150501030300255400f0442040d4025000b2058500380d805919006071100b8150350700901e44a000c1e5601d07a000072901d03507034121241c0c803440040d10038040320390203100d0001c0160a05c001c030320880c0300d00c2c110030384d001201400180440c010386070080b1041a0200340e5041c0c110014013100c0256101b4412143e01d01216009441c2c461070542e4002c866041510b18100d1090341d115502c20098610350200e4504030004046a00034000d0f41d40784000135255403254680303819001c00072070a0849600090458400040310342c15850112001e899000f18030048805284006441d01c0c0c103e03e00c0450f80395000d10032564070341d4141c0304030411307081c055a03030b4002304003641840c0381803501c4120094219000303601041080c64103d001c95854070405e1078002100388200f522141805000400c41d6807060511080c440369558030050002001411103200020f02200988142202c80040c3c0c002e401c030035091a9040381d00d066a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 139193776 1250 139192526 139192553
    0x70b03240a0311060a03060b030901150e060609090c071b06141905070305070506090c0f12280b0a0f0b010504030f061503230601050301061a07170409020405030607051204 75
    0x50902244903621100108e10580003100d800c2126990340120640c0244440e01c068010b010071034a00603e0709214010171807910401c607100d4010740b1001c01180c0c0c04e40ca124102d80703400b90020400303003450603082e4444c2c03141d200500c54038002561255804c0040d01c20801101c1500f2052140310500e110301c00815903190700888016010700ca03090092801050080c45414480c2d1078a01c0640000c0181d10f040001070a24010058051140c4c0c014100c4c00000016012030001d4035084500790419003881c154081a02c1400f000302100b2268080c03000c040300c943c1146803050b088550074002050f20f900115114040e034403020300400105c1720355801003103440c8d000d0215007140183c21000303142c681c0c5900d4525240071000002d520b42411100c40f00e203000384241e501620003103000303000300c902d05258124204502401c1c56400640011036000b0030020307100c24024040d0b94004030740c5544d17460046500a4016101e5203000e400388400003500e6500c6a002c0710040609880f00b03545a403207076102c01d100d00a21 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 139195026 1250 139193776 139193797
    0x7020304050a0e0405010f1a0906030c100918020a0f030c0207120807030e03010b0a0b03100f0305030c06010906060804080a11071701060b09030604030f02070b03240a031106 76
    0x810010070709403248480b850180200e02c40c100d405013400c3c0342282c01c48a141d4400c02015180c142c41d00b8040b0020092003640a0044404c0c1c0c00e60749900c40007a06213202408296444a8107500340079009400c9140d60301114411074003541c2c103038140c1d0703181400c2c0d00c0385030750110018450300c480140e5607010741d1040e020f0303d4040c412600680e4540e002c4145a08108030145c46100c800f02d028001c05a00c44951000e00c10160020b0102c6501d150200305405411701030010448004000200140d21040c1042d0040501100d655515070342c078240075450340c1c801c164981150050708004a90f40b2101d000d07400840c0c8056a40d9802c0d40d545403110140c90708150002010004d00c0342c100e080f03801080000002521203040410401d880d8451490f086541c01c0d0321100481005220f140c64580d00890010b50081c0c060816541c00580424100c0c00c203a9a0b80160a00201c0441030126140c81060f9407107501120b65a200d140c891401c080094402c924840100760502401469400b400c0550150032075030702 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 139196276 1250 139195026 139195033
    0x90c0403050601141311030a0c170a36030c060f150501030605012f0f0d0c021c0c0302101103031303030b06040b07020f15070515010518010e0702 64
    0x2101e548090520a080c1d2145400c030a1004031002240b074404d440300d000b1710105104201403803e43c0c4c804039950000505c00c10304d00c2e03074407244200c8850003200321041c0ca40305040500366a282c80e0804000401c10303113101d1000380c5190304124007848501c1000103c032a1402c83e906d6800000e90780c0403105a8886d0034121201e03500d541c400c0318504101d01071814440e101c54400f002c0c030340c244000141140c0290b071205042100c0ca42c00103d122850500d6440c01c02c031000c200354103030309038103950781d2410568815280181c03203001d0180802c50f901c089408803080c4200c3e00000b00c40340d0090303428103a82102001420109400500b040107180807005038444004508106025802c010303a460b05541045a949a140b5110014601095403500c02c040c00750790120340740c90600b410440d00b01014040e042d002400744250f1318a5600555829901d0000142035105880d82c5031620f1901c3c54541c1c0b5004103000084680100205042c82e0406c2d99400c46894a540d080541e8609a90700700c4c81007010344150203502 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 139197526 1250 139196276 139196279
    0x300207150c230706140f0405120f16060603080d0203270c011d10020f010501060504060807030b060405090103081e0306010f03022a1501080105010b07060e013c110702090c04 76
    0xc17550301d9074501c00c99441c05401ca052416041c603a082c03c2c0f00d10765940d0780460401c550403048030410144c0344100c1007092003d01c101140d20b0001c0007030600d50809401c0d4140030840d04070075030050b00114030401809501030110300070101c0c1b411032041c4150305512281c224012a0f4070035441401c100c0c010354444100e2120301080100441c0c14844010f03903003801a0040f5180850180090081c507004008a141c1035203400e180a0f002442e4400c050416400c254891040114944d503040680c5d020b800014003205441d40d592402516541c40010002c003c200001c0741c0a00b045010303400d0702d100b008180c55416800c040b5007000ca000391700c12214500900e829000c154480c1004030002c0f284a00b1032001410114a000380c06a0b0442050b1b20510709030381040e00600082c18001c0035988403540c42000425903c052a54950241035510031413041040400c61101c0310041e00d4045107050200c2c40d000c00100d41012445a0a84911408807000b6900804c001001410889582d951200500d5070090400c1d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 139198776 1250 139197526 139197551
    0x90f02041104060311030403170910051005030f0606130b0301060b0708090913020102070b0c100f02042c041112030f0301090b0907300207150c230706 66
    0x1c40066840c1103144002003002d0101e81d4041c03284803000020b40f81220304615141d034000b082401c01c3d500700700c00da4510300c010400350b40b820422618003601c4528107105901e04105128000c3c0403a1080d94481d20800740c40d54481c560115082c0d000c0c54000e040a030034046041c4201010340711082c0b429030550369030b0b50000360f22001d400c00303001d20b14031444046075558062400c00103030503009014410007001190410740181c0e0005940300403130300d411650f103840d101441c3d4000e00706101901036000442c28000c1c4542e804415a00030320569800190400007103001c60030010311007022030551608400e0100106001c00d01e00c6688a041010040101d01202c443c02c01480c1182c003c0c060781150000040b00520910195014581d2160000d0381c40087c24940104c1c000c1480030f090300300c0d944010048000050010880701084483d60621406542d02c1d02545050708044104c40440b811039454480b66108017485210081c540c0d8804d40340410a070380c625000307054954804041211119560100503a20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 139200026 1250 139198776 139198781
    0x1b03020324150f040302040b09090d031802100906020120031305010b0d0b04050d0e180a11041205060a09080403120e04051e0114100c02030f060405030c210d090f0204 73
    0x56041c901030140c0744e519600c18841620740250950380304241e0b0f0303020405440e900050001c00102241380114815815480d04140c90301e040002a40284501715094213803070b000b5682c10111040c4d5402000501c09039001c40000b07150000c502070907588104081a010800441d001c0c2c2c00da40201c00019900450346c000550383c4664004c00c9481a03290300c100030500005100003542c134003190130100d41c0e209880001420052005c1120119450110081200c6504030344c00001c565078045902030743e03643c440c4100c54081820010480e001d1054800241031602140102a4540e9004014900f0b160445d50b0322001d46030480c008000f002152020000c40c0d95a41c01900e004090b5540002031018408102e4441c1000503040812040403490303c01c10340b92190015042803a2003840c0c1901900d0061000a042a00d081745420040c0303d444144030a00901000620342c200c03c1d04100e85000030341620320700c0d94640a1042c0c40000f282404020300b00040b0344c00c1000402d105002c403000c1e0343c5056002404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 139201276 1250 139200026 139200037
    0xa0501080405030c1509010c0201060b0306060d09020a08010b030105090a0c030b0a0b10090303020d09030b010b2115030d0e03030a0e1201090b061509030706032408011b0302032415 79
    0x1130007170700c0018009004020720410409400702c4c40280f000c1800c10b0a01d0859100241c1051702810300059101d54120590f400098043d03801480d8000459441d61402d020384003004007544254a80000f190f44594002080070080d40e0080456030b00b5465500d46007802d10000300402c81c00c980314400003000e80c0d64070080124418454442c20f55050650034028606450310044c6c105004510109001054064100b681181c201c0300d03015641314044006048010103c011107040c0c22074079014444003550f007034200c0f0315420302601121942040f55a08942101420352050340541040080c400d181e44201200344c11a500503000312100c4400302c1620303003100c40d0440180c1d141c0a88000f03201541c80c209000b0741d00c0c02c0c5000240fa0910f620040001d03102e0002e4442c203000e2503611000040c2000000d8282040340485445520000d0303134680c0640d01804005060540b40c180d070309043c1810324000d00c240d0340030719121200b001c01d0400c14801c4088440b010041640e001d1140c00c40c058011803950010318 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 139202526 1250 139201276 139201303
    0xb090f0d030c051c030f020306010e040e0a02030102070803090c010c0314031003021906020f0f0312100f0308070308011211011404080a030e13090203100203060a0b070602030609070504050a0501080405030c 90
    0x4c408040d4590028100c1d4520101d048840e40100305001c6260385c881818400b0030011a400200940740c0c0750740e2841c10f003c101009406500104140080c04010005584034416031026100340e20420001100c1d05103500340c0081c0410304044124402000c010050356001d64084000d039011a181d4000030070010040480a00141441c0401c0c003009038140902000711010900402c84080c40c9045240c69002d9008545a140b401c1c0000480d0884000100c00044c1103510011340d90076120b042902e0309501c150b1060b001300e0381c043c0000910751140e1040081c517a0304032001c000c0c01c071a560011250b411069520001300c00003404046440f140910801c803046110340c40d0014107081310700c20300404144403014174004030f19248d040d0000d83c034041442c42281c1041c0d00016525611000083c013180003a0304250024980401c1200401540703600a6000f10b030101c80004056440e0841117416200e14000d00d5040030007110200100c1d4068440d07540c01610510075681018503018001d45804000b11840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 139203776 1250 139202526 139202563
    0x315050604170106050901080d0c0501020f0a05070618020d061802060307090303021510032a030b0a24060c06090b1f090614010e120a03020303010501090b090f0d030c05 74
    0x542c0794070091044400030041940c0c013000d01d40c03500c51101c0d107a445402105080c05800400401040001c0d0b0469150307448500400d034603503111200041103900503650803030f643e51400b10240350b040401c0080c01d004907030050a044080310f1554992015000074080ea400080030440e80e040107030b85103800b43d80f02d030055a43c0c1502d00c0780b950600070701d00394201d104600e54150b09410300c00c00e0b03c00e10020f0000d503074105004940c602c8528107030301c032200c2d4208000498032014003c04002c2115240d0106c1c024540c4281c14404a484080d4400240704000c0300740700c060750b695100b0442907001d215a485154060407001498008944980c01d2000b030445502c07403800c0d4004010f05286540d01d20400c00390041070310800500b410b1006c4001c1c150700c8240e090341481040400118683e480d82c892050f03007000398054612818003450040d690b60805e01890340401c031402d82c0882d940040800340e03003400300d0041640342038001c5d41048c4034403181c17601003c0e000c2000e14050080030034410041000214500d1242 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 139205026 1250 139203776 139203809
    0x1e0905031306051306090b0904050601021603080417010b010e09060d0b1303170705070204180609060f0b24070804080303100e10080a0b0c04180f1503120315050604 72
    0x42c8440303481c0c5174000c1014000e82000a01412020a059440c5240240c1c5c000840d61a43e0b030050b032924001c14030414002010000110810101c04c014004440c1c203582c44500c0d00d00d013440c3c000e0a03140c41000030b034001510308603000400e2a002c00785130f4101c070000d051410010442c0d114500152421200000d100c22900050b20805510200581ea0000007404c0903082d03007054000200140f158040c00f034402c0c0c7d183c1c802401880903810501005503071000e010400040e140c0f4100c0c028000e001e845c103494510f84819140a4140301c0d11440c00004540000300c2d10340b000010301d10503500180d805890881c014000410f00303203410030056001d000004540b03a4002d00d4560054100c200c014441c209201c0c600394101b2051100041c2e2b6800540c2c091101915542d4003441d140300c90090794081c444407103040c524070f5600d600550100158010294091024a0300b82006a51105113884000d10360200d0f10b030502c154501c6540300e0300ca0b282214100c0410704d0b0343c4600092042c0c006070040e040c0d0488040c3c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 139206276 1250 139205026 139205047
    0xc16050a06020718020a1209031206050f010906030e0a0503040e0a050a060308371709010516080c130e06040e1219020106080a050a151e090503130605 66
    0xc0c0030010191440180000782c20b040350100038030320600506685540108051070380e103029502044541041e80e008004c2507945050090480d4040f04000a0040c40c10b20040380900300707120700303146000381038445002c0f0031700e8540c0c128024600c4901c03e003110b0042c0115803000440130702c010b10080180f01807042a40c2006811003023100c4002d0441c5004611f001c008100207a09001560288030380c2c81710050064850300c254240c030240e00c0a5a00f0b918101c040c0c14182180c00212108440000075510305440d521402401c0c01c036401616815000b2020168120015100d0501e2542c07103450a01f1490803c000031450440c41040c5400c0300500711a030408104542c00d007442015440c016400041c41c00ea91f8402040c9298812018503102840640c070b04cec00d00c214001d4201c0b000030510201201d840201c00d0601540340c2c1c0281300210346901c14000c4c1c484004e105801503014440c961502e000a004d01c0c0e92103c1c000384105402140c45000500c900f80c040c000302244c02000301081d88441c0d030380b03000740023 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 139207526 1250 139206276 139206289
    0x3c0a050d0e0a26070f060c0e09100927060b0102070e070f030e160b0a0c0506010807090b0108070f120e06090109051009050a0b04020a0f0311030105010e0c120c0c1605 73
    0x2d29030183c040060204a0100f80c1c00c0045001c0150030803800600088041402c0300d11208401030184c120840e0424000c0c100041c18a01049071900d090821200032414161640c0175a02040c040000d000003c3c4840810803c0e40880d911540500407140c41030b580d400384080d01c00c4225100c030049132241594021540d014050601c3e4840020040c000d200c0c0c088610b4210440580a03503007603c58042209840c0c2c80c0142d071054881d5800034111030556030740b1503c86039549014040d0f41c10140c18005101481d5002d000158024405074440b020010a03080381250800d0004001c01c0b0700d00d8803043c18204035401440100c2c041d40400b0000b00f545000b07411300910f0412070000c04210f00d46040d01201c0464004610f81c24900c0c0c2c0101040620340300c031b00000d05168042d4101503100c44140718008100040d61030000241e100c213900a011a0b031346d40034039a400000c11a000280410204000401120714641d903a501c500707204060360910010b58002407402610603040383c40c040c0440800c0c0711510f0100f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 139208633 1107 139207526 139207583
    0xa0519090602040510050702030601150201090f060b183c130c080a110609012705040f0501050105090d030c06023c0a050d0e0a 56
    0x41c00c2110082d0f000e0701c2004e03c0380c1482003881101728028416189195001405440d080e0b180c081941e500c0c4841001240465580700012000540c1402c214020140503500000f1404000b0052206195802007800c4400a110381001101e000c0f000c14042e0040d6558110400c05240c0e014041e448640c1c00c0705000d10070100001c01010855848500401500626106041a58a080607a1201c00084003c1c00c2e440b542ea000a5450403c0001881250810314004e00492160008d1407141586016103907030007001501c04004500d8103000c0d480851045034020409541340c03e0002e401c6e841103a0a41d030103802140700754024036000d007a6004100350001c01c15540d40010006220340c0b18032068a1151580c00c9013400c1e4051003a0011245400d403440c4c4080d4904044130405172000c0c0c00c4a00728048054907a0100d400004060040310700040c0300c0d90b1402104000d6404000c0c0500b8031707 = true := by decide +kernel

theorem cover : BRFrame.Cov 139028776 139208633 := by
  have h0 := BRFrame.cov_init 139028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 139028776 ≤ n) (h2 : n < 139208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
